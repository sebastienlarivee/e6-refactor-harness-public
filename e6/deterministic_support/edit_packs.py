"""Small, immutable-source edit compositions with strict hash/span guards.

These are syntactic proposals, not proof-preserving certificates. Conflicting
or nested edits are alternatives; all emitted complete sources need validation.
"""
from __future__ import annotations

from collections import defaultdict, deque
from hashlib import sha256
import json

OFFSET_UNIT = "unicode_codepoints_zero_based_end_exclusive"
MAX_EDITS = 64
MAX_PACK_WIDTH = 8
MAX_CANDIDATES = 24
FAMILIES = ("same_edit_batch", "compatible_edit_pack")


def digest(text: str) -> str:
    return sha256(text.encode("utf-8")).hexdigest()


def conflict(left: dict, right: dict) -> bool:
    a, b, c, d = left["start"], left["end"], right["start"], right["end"]
    # Insertions on another edit's boundary are deliberately alternatives:
    # applying both can depend on order even when half-open intervals touch.
    if a == b:
        return c <= a <= d
    if c == d:
        return a <= c <= b
    return a < d and c < b


class EditSpace:
    """Validate a hash-bound inventory before constructing any child source."""

    def __init__(self, source: str, document: dict, *, minimum: int, maximum: int):
        if (document.get("input_sha256") != digest(source)
                or document.get("offset_unit") != OFFSET_UNIT):
            raise ValueError("Edit inventory source hash or offset unit mismatch")
        edits = document.get("edits")
        if not isinstance(edits, list) or len(edits) > MAX_EDITS:
            raise ValueError("Edit inventory exceeds its bounded list contract")
        if type(minimum) is not int or type(maximum) is not int or not 0 <= minimum <= maximum <= len(source):
            raise ValueError("Invalid target edit boundaries")
        for edit in edits:
            if (not isinstance(edit, dict) or type(edit.get("start")) is not int
                    or type(edit.get("end")) is not int or not isinstance(edit.get("old"), str)
                    or not isinstance(edit.get("new"), str)
                    or not minimum <= edit["start"] <= edit["end"] <= maximum
                    or source[edit["start"]:edit["end"]] != edit["old"]
                    or edit.get("old_sha256") != digest(edit["old"])
                    or edit.get("new_sha256") != digest(edit["new"])):
                raise ValueError("Edit inventory content hash or source span mismatch")
        self.source = source
        self.edits = edits

    def compatible(self, indices: list[int]) -> bool:
        return (len(indices) == len(set(indices))
                and all(type(i) is int and 0 <= i < len(self.edits) for i in indices)
                and all(not conflict(self.edits[i], self.edits[j])
                        for offset, i in enumerate(indices) for j in indices[offset + 1:]))

    def apply(self, indices: list[int]) -> str:
        if not self.compatible(indices):
            raise ValueError("Conflicting or invalid edit pack")
        output = self.source
        for edit in sorted((self.edits[i] for i in indices), key=lambda item: item["start"], reverse=True):
            output = output[:edit["start"]] + edit["new"] + output[edit["end"]:]
        return output


def _bound(source: str, proposals: list[dict], minimum: int, maximum: int) -> dict:
    """Bind trusted single-edit generator output; reject inconsistent evidence."""
    parent = digest(source)
    groups = defaultdict(deque)
    seen = set()
    for item in proposals:
        if not isinstance(item, dict) or len(item.get("edits", [])) != 1:
            continue
        if item.get("parent_sha256", parent) != parent:
            continue
        edit = item["edits"][0]
        if (not isinstance(edit, dict) or type(edit.get("start")) is not int
                or type(edit.get("end")) is not int or not isinstance(edit.get("new"), str)
                or edit.get("offset_unit", OFFSET_UNIT) != OFFSET_UNIT
                or not minimum <= edit["start"] <= edit["end"] <= maximum):
            continue
        old = source[edit["start"]:edit["end"]]
        if (edit.get("old", old) != old or old == edit["new"]
                or edit.get("old_sha256", digest(old)) != digest(old)
                or edit.get("new_sha256", digest(edit["new"])) != digest(edit["new"])):
            continue
        key = (edit["start"], edit["end"], edit["new"])
        if key in seen:
            continue
        seen.add(key)
        family = str(item.get("family", ""))
        groups[family].append({"start": edit["start"], "end": edit["end"], "old": old,
                               "new": edit["new"], "family": family,
                               "old_sha256": digest(old), "new_sha256": digest(edit["new"])})
    edits = []
    # Bound each immutable inventory before any quadratic conflict inspection;
    # a long family cannot hide every other family's composition opportunity.
    while len(edits) < MAX_EDITS and any(groups.values()):
        for values in groups.values():
            if values:
                edits.append(values.popleft())
                if len(edits) == MAX_EDITS:
                    break
    return {"input_sha256": parent, "offset_unit": OFFSET_UNIT, "edits": edits}


def compose(source: str, proposals: list[dict], *, minimum: int, maximum: int,
            max_candidates: int = MAX_CANDIDATES, allow_same_family_packs: bool = False) -> list[dict]:
    """Offer same-text batches, greedy packs, halves and bounded repair packs.

    Singles stay with their original families. No arbitrary powerset search or
    source rebase is attempted here; every pack refers to one immutable parent.
    """
    if type(max_candidates) is not int or not 0 <= max_candidates <= MAX_CANDIDATES:
        raise ValueError(f"max_candidates must be an integer in 0..{MAX_CANDIDATES}")
    if type(allow_same_family_packs) is not bool:
        raise ValueError("allow_same_family_packs must be a boolean")
    if not max_candidates:
        return []
    document = _bound(source, proposals, minimum, maximum)
    space = EditSpace(source, document, minimum=minimum, maximum=maximum)
    edits = space.edits
    groups = defaultdict(list)
    for index, edit in enumerate(edits):
        if len(edit["old"]) <= 30 and len(edit["new"]) <= 40:
            groups[(edit["family"], edit["old"], edit["new"])].append(index)
    plans = []
    for indices in groups.values():
        if len(indices) < 2:
            continue
        indices.sort(key=lambda i: edits[i]["start"])
        chunks = [indices[:MAX_PACK_WIDTH]]
        for count in (2, 4):
            width = (len(indices) + count - 1) // count
            chunks.extend(indices[i:i + min(width, MAX_PACK_WIDTH)] for i in range(0, len(indices), width))
        for chunk in chunks:
            if len(chunk) > 1 and space.compatible(chunk):
                plans.append(("same_edit_batch", chunk))

    def greedy(order):
        chosen = []
        for index in order:
            if space.compatible(chosen + [index]):
                chosen.append(index)
            if len(chosen) == MAX_PACK_WIDTH:
                break
        return chosen

    indices = list(range(len(edits)))
    packs = [greedy(sorted(indices, key=lambda i: (edits[i]["end"] - edits[i]["start"], i), reverse=reverse))
             for reverse in (False, True)]
    packs += [greedy(indices[:len(indices) // 2]), greedy(indices[len(indices) // 2:])]
    for pack in packs:
        if len(pack) > 1 and (allow_same_family_packs or len({edits[i]["family"] for i in pack}) > 1):
            plans.append(("compatible_edit_pack", pack))
            # A failed constituent should not force discarding the whole pack.
            for index in pack[:4]:
                plans.append(("compatible_edit_pack", [i for i in pack if i != index]))
    # A few simple disjoint pairs are useful even when a large pack regresses.
    pair_count = 0
    for offset, left in enumerate(indices):
        for right in indices[offset + 1:]:
            if (allow_same_family_packs or edits[left]["family"] != edits[right]["family"]) and space.compatible([left, right]):
                plans.append(("compatible_edit_pack", [left, right]))
                pair_count += 1
                break
        if pair_count >= 8:
            break
    result, seen = [], {digest(source)}
    # Reserve half the output for each composition mechanism when both apply.
    queues = {family: deque(plan for kind, plan in plans if kind == family) for family in FAMILIES}
    while len(result) < max_candidates and any(queues.values()):
        for family, queue in queues.items():
            while queue:
                chosen = queue.popleft()
                if len(chosen) < 2:
                    continue
                child = space.apply(chosen)
                hashed = digest(child)
                if hashed in seen:
                    continue
                seen.add(hashed)
                selected = [edits[i] for i in chosen]
                content_hash = digest(json.dumps(selected, sort_keys=True, ensure_ascii=False))
                result.append({"family": family, "site": min(edit["start"] for edit in selected),
                               "description": f"Compose {len(chosen)} disjoint source-bound edits",
                               "component_families": [edit["family"] for edit in selected],
                               "component_edits_sha256": content_hash,
                               "composition_input_sha256": document["input_sha256"],
                               "edits": selected})
                break
            if len(result) == max_candidates:
                break
    return result
