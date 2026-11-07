"""Bounded reader for the small subset of Firefox JSON used by native accounting.

Sample columns are decoded in bounded batches into anonymous packed files. Only
one thread's columns are mapped at a time; unused fields are parsed and discarded.
This is deliberately a JSON reader, not substring/regular-expression extraction.
"""
from __future__ import annotations

from array import array
from contextlib import ExitStack
import json
import math
import mmap
from pathlib import Path
import struct
import tempfile
import time
from typing import Any, Iterator

CHUNK_CHARS = 64 * 1024
MAX_SCALAR_CHARS = 256 * 1024
MAX_DEPTH = 64
MAX_OBJECT_KEYS = 1024
MAX_KEY_CHARS = 1024
MAX_TABLE_VALUES = 1_000_000
MAX_TABLE_STRING_CHARS = 8 * 1024 * 1024
MAX_SCRATCH_BYTES = 256 * 1024 * 1024
MAX_PARSE_SECONDS = 60.0
MAX_EXACT_INTEGER_OVERRIDES = 4096


class ProfileBudgetExceeded(ValueError):
    """A declared parsing resource bound was reached; no summary is complete."""


def _constant(value: str) -> Any:
    raise ValueError("invalid native profile JSON constant: " + value)


class PackedColumn:
    def __init__(self, file: Any, count: int, kind: str, negative_count: int,
                 exact_integers: dict[int, int]):
        self.count, self.kind, self.negative_count = count, kind, negative_count
        self.exact_integers = exact_integers
        self.mapping = mmap.mmap(file.fileno(), 0, access=mmap.ACCESS_READ) if count else None
        self.unpack = struct.Struct('=Q' if kind == 'stack' else '=d')

    def __len__(self) -> int:
        return self.count

    def __getitem__(self, index: int | slice) -> Any:
        if isinstance(index, slice):
            return [self[i] for i in range(*index.indices(self.count))]
        if not 0 <= index < self.count:
            raise IndexError(index)
        return self.exact_integers.get(index, self.unpack.unpack_from(self.mapping, index * 8)[0])

    def __iter__(self) -> Iterator[int | float]:
        if self.mapping is not None:
            # A bounded bytes copy avoids exporting the mmap buffer to an
            # unfinished iterator, so error cleanup can always close the map.
            chunk_bytes = max(8, CHUNK_CHARS // 8 * 8)
            for offset in range(0, self.count * 8, chunk_bytes):
                values = self.unpack.iter_unpack(self.mapping[offset:offset + chunk_bytes])
                if self.exact_integers:
                    for index, (value,) in enumerate(values, offset // 8):
                        yield self.exact_integers.get(index, value)
                else:
                    for (value,) in values:
                        yield value

    def close(self) -> None:
        if self.mapping is not None:
            self.mapping.close()


class ProfileReader:
    def __init__(self, path: Path, *, max_bytes: int, max_samples: int):
        self.path, self.max_bytes, self.max_samples = path, max_bytes, max_samples
        self.meta: Any = None
        self.buffer, self.pos, self.eof = '', 0, False
        self.bytes_read = self.table_values = self.table_chars = 0
        self.scratch_bytes = 0
        self.deadline = time.monotonic() + MAX_PARSE_SECONDS
        self.decoder = json.JSONDecoder(parse_constant=_constant)

    def check(self) -> None:
        if time.monotonic() > self.deadline:
            raise ProfileBudgetExceeded("native profile exceeds the parsing time bound")

    def _fill(self) -> bool:
        self.check()
        self.buffer = self.buffer[self.pos:]
        self.pos = 0
        if not self.eof:
            chunk = self.source.read(CHUNK_CHARS)
            self.bytes_read += len(chunk.encode('utf-8'))
            if self.bytes_read > self.max_bytes:
                raise ProfileBudgetExceeded(f"native profile exceeds the {self.max_bytes} byte parsing bound")
            self.buffer += chunk
            self.eof = not chunk
        return not self.eof

    def _peek(self) -> str:
        while True:
            while self.pos < len(self.buffer) and self.buffer[self.pos] in ' \r\n\t':
                self.pos += 1
            if self.pos < len(self.buffer):
                return self.buffer[self.pos]
            if not self._fill():
                return ''

    def _expect(self, value: str) -> None:
        if self._peek() != value:
            raise ValueError("malformed or truncated native profile JSON; expected " + value)
        self.pos += 1

    def _scalar(self) -> Any:
        first = self._peek()
        if not first or first not in '"-0123456789ntf':
            raise ValueError("malformed or truncated native profile JSON scalar")
        while True:
            try:
                result, end = self.decoder.raw_decode(self.buffer, self.pos)
                if end < len(self.buffer) and self.buffer[end] not in ' \r\n\t,]}:':
                    # A number can straddle a read boundary (e.g. `1e` + `-3`).
                    if not self.eof:
                        raise json.JSONDecodeError('incomplete token', self.buffer, end)
                    raise ValueError("malformed native profile JSON scalar")
                if end == len(self.buffer) and not self.eof:
                    self._fill()
                    continue
                if end - self.pos > MAX_SCALAR_CHARS:
                    raise ProfileBudgetExceeded("native profile exceeds the scalar parsing bound")
                self.pos = end
                return result
            except json.JSONDecodeError as error:
                if len(self.buffer) - self.pos > MAX_SCALAR_CHARS:
                    raise ProfileBudgetExceeded("native profile exceeds the scalar parsing bound") from error
                if self.eof:
                    raise ValueError("malformed or truncated native profile JSON") from error
                self._fill()

    def _keys(self) -> Iterator[str]:
        self._expect('{')
        seen: set[str] = set()
        if self._peek() == '}':
            self.pos += 1
            return
        while True:
            key = self._scalar()
            if type(key) is not str or key in seen:
                raise ValueError("invalid or duplicate native profile JSON object key")
            if len(key) > MAX_KEY_CHARS:
                raise ProfileBudgetExceeded("native profile exceeds the object-key string parsing bound")
            seen.add(key)
            if len(seen) > MAX_OBJECT_KEYS:
                raise ProfileBudgetExceeded("native profile exceeds the object-key parsing bound")
            self._expect(':')
            yield key
            if self._peek() == '}':
                self.pos += 1
                return
            self._expect(',')

    def _items(self) -> Iterator[None]:
        self._expect('[')
        if self._peek() == ']':
            self.pos += 1
            return
        while True:
            yield None
            if self._peek() == ']':
                self.pos += 1
                return
            self._expect(',')

    def _value(self, *, retain: bool, depth: int = 0) -> Any:
        if depth > MAX_DEPTH:
            raise ProfileBudgetExceeded("native profile exceeds the nesting parsing bound")
        if retain:
            self.table_values += 1
            if self.table_values > MAX_TABLE_VALUES:
                raise ProfileBudgetExceeded("native profile exceeds the table parsing bound")
        first = self._peek()
        if first == '{':
            result = {} if retain else None
            for key in self._keys():
                value = self._value(retain=retain, depth=depth + 1)
                if retain:
                    result[key] = value
            return result
        if first == '[':
            result = [] if retain else None
            for _ in self._items():
                value = self._value(retain=retain, depth=depth + 1)
                if retain:
                    result.append(value)
            return result
        value = self._scalar()
        if retain and type(value) is str:
            self.table_chars += len(value)
            if self.table_chars > MAX_TABLE_STRING_CHARS:
                raise ProfileBudgetExceeded("native profile exceeds the string-table parsing bound")
        return value if retain else None

    def _numeric_batches(self) -> Iterator[list]:
        """C-decode bounded primitive-array batches, including unknown CPU deltas."""
        self._expect('[')
        started = False
        while True:
            # Numeric arrays cannot contain `]` or quoted commas. Invalid nested
            # values fail JSON/type validation rather than being silently skipped.
            close = self.buffer.find(']', self.pos)
            comma = self.buffer.rfind(',', self.pos) if close < 0 else -1
            if close >= 0 or comma >= 0:
                end = close if close >= 0 else comma
                fragment = self.buffer[self.pos:end]
                if not fragment.strip() and (started or close < 0):
                    raise ValueError("malformed native numeric array")
                batch = json.loads('[' + fragment + ']', parse_constant=_constant)
                self.pos = end + 1
                yield batch
                if close >= 0:
                    return
                started = True
            elif self.eof:
                raise ValueError("truncated native numeric array")
            elif len(self.buffer) - self.pos > MAX_SCALAR_CHARS:
                raise ProfileBudgetExceeded("native profile exceeds the scalar parsing bound")
            else:
                self._fill()

    def _column(self, key: str, files: ExitStack) -> PackedColumn:
        file = files.enter_context(tempfile.TemporaryFile())
        count = negative = 0
        exact_integers: dict[int, int] = {}
        for values in self._numeric_batches():
            first_index = count
            count += len(values)
            if count > self.max_samples:
                raise ProfileBudgetExceeded(f"native profile exceeds the {self.max_samples} sample parsing bound")
            for index, value in enumerate(values, first_index):
                if key == 'stack':
                    if type(value) is not int or not 0 <= value < MAX_TABLE_VALUES:
                        raise ValueError("invalid native sample stack")
                else:
                    try:
                        finite = type(value) in (int, float) and math.isfinite(value)
                    except OverflowError:
                        finite = False
                    if not finite:
                        raise ValueError("native profile has invalid/non-finite sample values")
                    negative += value < 0
                    # JSON integers can carry more precision than a native
                    # double. Preserve rare exact timestamps/counters without
                    # turning normal sample columns into Python object lists.
                    if type(value) is int and (key == 'time' or float(value) != value):
                        exact_integers[index] = value
                        if len(exact_integers) > MAX_EXACT_INTEGER_OVERRIDES:
                            raise ProfileBudgetExceeded("native profile exceeds the exact-integer parsing bound")
            packed = array('Q' if key == 'stack' else 'd', values)
            self.scratch_bytes += len(packed) * packed.itemsize
            if self.scratch_bytes > MAX_SCRATCH_BYTES:
                raise ProfileBudgetExceeded("native profile exceeds the scratch parsing bound")
            packed.tofile(file)
        file.flush()
        column = PackedColumn(file, count, key, negative, exact_integers)
        files.callback(column.close)
        return column

    def _thread(self, files: ExitStack) -> dict[str, Any]:
        thread: dict[str, Any] = {}
        needed = {'stackTable': {'frame', 'prefix'}, 'frameTable': {'func'}, 'funcTable': {'name'}}
        for key in self._keys():
            if key in needed:
                table = {}
                for field in self._keys():
                    if field in needed[key]:
                        table[field] = self._value(retain=True)
                    else:
                        self._value(retain=False)
                thread[key] = table
            elif key == 'stringArray':
                thread[key] = self._value(retain=True)
            elif key == 'samples':
                sample = {}
                for field in self._keys():
                    if field in ('stack', 'time', 'weight'):
                        sample[field] = self._column(field, files)
                    elif field in ('length', 'weightType'):
                        sample[field] = self._value(retain=True)
                    elif field == 'threadCPUDelta':
                        for batch in self._numeric_batches():
                            if any(type(value) not in (int, float) for value in batch):
                                raise ValueError("invalid native numeric array")
                    else:
                        self._value(retain=False)
                thread[key] = sample
            else:
                self._value(retain=False)
        return thread

    def threads(self) -> Iterator[dict[str, Any]]:
        with self.path.open(encoding='utf-8') as self.source:
            found_threads = False
            for key in self._keys():
                if key == 'meta':
                    self.meta = self._value(retain=True)
                elif key == 'threads':
                    found_threads = True
                    for _ in self._items():
                        self.scratch_bytes = 0
                        with ExitStack() as files:
                            yield self._thread(files)
                else:
                    self._value(retain=False)
            if self._peek():
                raise ValueError("trailing data in native profile JSON")
            if not found_threads:
                raise ValueError("unsupported native profile table: threads")
