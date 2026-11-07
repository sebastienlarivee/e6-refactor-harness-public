"""Expose one proof capsule and native tools in an empty Linux filesystem.

Keep the outer host PID namespace for owned-process supervision. Native Codex
tools may introduce their own PID namespace; shared Lean admission uses kernel
file leases rather than namespace-local PIDs. The separate user namespace and
dropped capabilities prevent /proc root/fd links from exposing other files.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import shutil
import sys
from typing import Mapping, Sequence

from .config import REPO_ROOT, environments_root, runtime_root, runs_root
from .experiment import experiment_spec
from lean_tools import arena_workflow as arena


def _narrow(path: Path) -> Path:
    path = path.expanduser().resolve()
    broad = {Path('/'), Path('/home'), Path('/mnt'), Path('/mnt/c'), Path('/mnt/d'),
             Path.home().resolve(), REPO_ROOT, environments_root(), runs_root(), runtime_root()}
    if path in broad or any(root.is_relative_to(path) for root in broad if root != Path('/')):
        raise ValueError(f'Isolation refuses a broad filesystem mount: {path}')
    if not path.exists():
        raise FileNotFoundError(path)
    return path


def _fresh_pi_home(home: Path) -> Path:
    """Accept only the empty private home provisioned for this Pi pass."""
    directories = (home, home / '.pi', home / '.pi' / 'agent')
    for index, path in enumerate(directories):
        if path.is_symlink() or (path.exists() and not path.is_dir()):
            raise RuntimeError('Proof capsule has a non-fresh native Pi home')
        path.mkdir(exist_ok=True, mode=0o700)
        expected = {directories[index + 1].name} if index + 1 < len(directories) else set()
        # The SDK uses in-memory settings, auth and sessions. Even empty auth,
        # session or extension files must not survive into a fresh pass.
        if any(entry.name not in expected for entry in path.iterdir()):
            raise RuntimeError('Proof capsule has a non-fresh native Pi home')
    return directories[-1]


def _pi_runtime(config: dict) -> tuple[Path, Path, Path]:
    """Expose one installed release and tool executables, never their parents."""
    paths = {}
    for key in ('pi_node', 'pi_package', 'pi_release', 'pi_rg'):
        value = config.get(key)
        if not isinstance(value, str) or not Path(value).is_absolute():
            raise ValueError(f'Pi isolation requires an absolute {key}')
        paths[key] = _narrow(Path(value))
    node, package, release, rg = (paths[key] for key in ('pi_node', 'pi_package', 'pi_release', 'pi_rg'))
    version = config.get('pi_version')
    if (not isinstance(version, str)
            or not re.fullmatch(r'[0-9]+\.[0-9]+\.[0-9]+(?:[-+][0-9A-Za-z.-]+)?', version)
            or release.name != version or release.parent.name != 'releases'
            or release.parent.parent.name != 'install'
            or not release.is_dir()
            or package != release / 'node_modules/@earendil-works/pi-coding-agent'
            or not package.is_dir()):
        raise ValueError('Pi isolation requires a fixed installed release tree')
    if not node.is_file() or not os.access(node, os.X_OK) or node.suffix == '.exe':
        raise ValueError('Pi isolation requires a native Node executable')
    if not rg.is_file() or not os.access(rg, os.X_OK) or rg.suffix == '.exe':
        raise ValueError('Pi isolation requires a native ripgrep executable')
    manifest = json.loads((package / 'package.json').read_text(encoding='utf-8'))
    if manifest.get('name') != '@earendil-works/pi-coding-agent' or manifest.get('version') != version:
        raise ValueError('Pi isolated package does not match the pinned release')
    return node, release, rg



_SYSTEM_LIBRARY_PATHS = ('bin', 'sbin', 'lib', 'lib64')
_SYSTEM_CONFIG_PATHS = ('/etc/ssl', '/etc/ld.so.cache', '/etc/nsswitch.conf', '/etc/passwd',
                        '/etc/group', '/etc/hosts', '/etc/resolv.conf', '/etc/localtime')


def system_readable_paths() -> tuple[Path, ...]:
    """Host paths exposed by the fixed system mounts, resolved through symlinks."""
    paths = [Path('/usr'), *(Path('/') / name for name in _SYSTEM_LIBRARY_PATHS),
             *(Path(value) for value in _SYSTEM_CONFIG_PATHS)]
    return tuple(dict.fromkeys(path.resolve() for path in paths if path.exists()))


def readonly_mount_paths(config: Mapping, *, elan_home: Path) -> tuple[Path, ...]:
    """Shared mount exposure policy for sandbox construction and credential guards.

    Dynamic broker helpers and writable capsules live beneath the proof/run
    tree, which the host credential guard independently excludes in full.
    """
    paths = [REPO_ROOT / name for name in ('e6', 'lean_tools', 'transport', '.venv', 'scripts')
             if (REPO_ROOT / name).is_dir()]
    if (runtime_root() / 'bin').is_dir():
        paths.append(runtime_root() / 'bin')
    if config.get('agent_backend', 'codex') == 'pi':
        node, release, rg = _pi_runtime(dict(config))
        paths.extend((node, release, rg))
    else:
        codex = Path(config['codex']).expanduser().resolve()
        package = codex.parent.parent
        if codex.parent.name == 'bin' and (package / 'codex-package.json').is_file():
            paths.append(package)
        else:
            paths.append(codex)
            sidecar = codex.with_name('codex-code-mode-host')
            if sidecar.is_file():
                paths.append(sidecar)
    if config.get('model_catalog'):
        paths.append(Path(config['model_catalog']))
    paths.extend(Path(value) for value in [config.get('primary'), *config.get('compatibility', [])] if value)
    elan = Path(elan_home).expanduser().resolve()
    if elan.is_dir():
        paths.append(elan)
        paths.extend(link.resolve() for link in (elan / 'toolchains').glob('*'))
    for name in ('retrieval_index', 'examples_index'):
        if name == 'examples_index' and not config.get('experiment_spec', {}).get(
                'search_extensions', config.get('search_extensions', False)):
            continue
        index = config.get(name)
        if isinstance(index, dict) and isinstance(index.get('path'), str):
            paths.append(Path(index['path']))
    return tuple(dict.fromkeys(path.expanduser().resolve() for path in paths))

def wrap_command(config: dict, capsule: Path, argv: Sequence[str],
                 writable_roots: Sequence[Path], child_env: Mapping[str, str]) -> tuple[list[str], dict[str, str]]:
    """Return a fail-closed native CLI invocation and its clean environment."""
    if os.name != 'posix' or not Path('/proc').is_dir():
        raise RuntimeError('E6 proof passes require native Linux filesystem isolation')
    binary = shutil.which('bwrap')
    if binary is None:
        raise RuntimeError('Install bubblewrap before launching E6 proof passes')
    capsule = _narrow(capsule)
    if not capsule.is_dir():
        raise ValueError('Proof capsule must be a directory')
    home = capsule / '.native-home'
    backend = config.get('agent_backend', 'codex')
    if backend == 'pi':
        pi_node, pi_release, pi_rg = _pi_runtime(config)
        agent_environment = {'PI_CODING_AGENT_DIR': str(_fresh_pi_home(home))}
    elif backend == 'codex':
        codex_home = home / '.codex'
        codex_home.mkdir(parents=True, exist_ok=True, mode=0o700)
        # One fresh capsule owns one pass. Reusing a logged-in or archived CLI home
        # would violate the fresh-context experiment, even with --ephemeral.
        if (codex_home / 'auth.json').exists() or any((codex_home / name).exists()
                and any((codex_home / name).iterdir()) for name in ('sessions', 'archived_sessions')):
            raise RuntimeError('Proof capsule has a non-fresh native Codex home')
        agent_environment = {'CODEX_HOME': str(codex_home)}
    else:
        raise ValueError(f'Unknown E6 agent backend: {backend}')

    environment = {key: value for key, value in child_env.items()
                   if key in {'PATH', 'LANG', 'LC_ALL', 'LC_CTYPE', 'TERM', 'SHELL',
                              'LEAN_NUM_THREADS', 'OMP_NUM_THREADS', 'RAYON_NUM_THREADS',
                              'ELAN_HOME', 'ELAN_TOOLCHAIN', 'LEAN_PATH', 'LEAN_SRC_PATH',
                              'LEAN_SYSROOT', 'LEAN', 'LAKE', 'LAKE_HOME', 'LD_LIBRARY_PATH',
                              'LRH_SERIAL_MODEL_TOKEN'}
                   or key.startswith('LEAN_REFACTOR_')}
    for key in list(environment):
        if any(word in key for word in ('SEED', 'ARCHIVE', 'BASELINE')):
            environment.pop(key)
    spec = experiment_spec(config)
    reprove = spec.first_pass_reprove and capsule.name == 'pass-001'
    if reprove:
        from .broker_lifecycle import BROKER_ENV
        for key in BROKER_ENV:
            environment.pop(key, None)
    elan = Path(environment.get('ELAN_HOME', str(environments_root() / 'elan'))).resolve()
    environment.update(HOME=str(home), **agent_environment,
                       USER=child_env.get('USER', 'lariv'), LOGNAME=child_env.get('LOGNAME', 'lariv'), PYTHONPATH=str(REPO_ROOT),
                       E6_RUNTIME_ROOT=str(runtime_root()), E6_ENVIRONMENTS_ROOT=str(environments_root()),
                       PATH=f'{elan / "bin"}:{runtime_root() / "bin"}:/usr/local/bin:/usr/bin:/bin')
    if backend == 'pi':
        environment['PATH'] = f'{pi_node.parent}:/run/e6-pi-tools:{environment["PATH"]}'

    command = [binary, '--die-with-parent', '--unshare-user',
               '--cap-drop', 'ALL', '--ro-bind', '/usr', '/usr']
    for name in _SYSTEM_LIBRARY_PATHS:
        path = Path('/') / name
        if path.is_symlink():
            command += ['--symlink', os.readlink(path), str(path)]
        elif path.exists():
            command += ['--ro-bind', str(path), str(path)]
    command += ['--proc', '/proc', '--dev', '/dev', '--tmpfs', '/tmp', '--tmpfs', '/run']
    for path in _SYSTEM_CONFIG_PATHS:
        if Path(path).exists():
            command += ['--ro-bind', path, path]

    read_only = [_narrow(path) for path in readonly_mount_paths(config, elan_home=elan)]
    projects = [config.get('primary'), *config.get('compatibility', [])]
    # Custom/path dependencies use a task-scoped measurement helper in the
    # host broker's private cache. Expose only its generated helper directory;
    # candidate verdicts, broker state and managed documents stay private.
    support = json.loads(environment.get('LEAN_REFACTOR_FEEDBACK_SUPPORT', '[]'))
    if not isinstance(support, list) or any(not isinstance(path, str) for path in support):
        raise ValueError('Invalid provisioned Lean helper paths')
    project_roots = [Path(path).resolve() for path in projects if path]
    for value in support:
        path = Path(value).resolve()
        if any(path.is_relative_to(project) for project in project_roots):
            continue
        key = path.name
        root = Path(config['root']).resolve()
        expected = root / 'warm-broker/private-evaluation-cache/helpers' / key[:2] / key
        if (not re.fullmatch(r'[0-9a-f]{64}', key) or path != expected
                or not all((path / name).is_file() for name in
                           ('LrhMeasurement.lean', 'LrhMeasurement.olean', 'ready.json'))):
            raise ValueError('Lean helper is outside the provisioned broker cache')
        read_only.append(_narrow(path))
    if elan.is_dir():
        environment['ELAN_HOME'] = str(elan.resolve())
    writable = list(dict.fromkeys([capsule, *(_narrow(Path(path)) for path in writable_roots)]))
    if backend == 'pi' and any(path.is_relative_to(root) or root.is_relative_to(path)
            for path in (pi_node, pi_release, pi_rg) for root in writable):
        raise ValueError('Pi runtime must remain outside writable proof roots')
    index = config.get('retrieval_index')
    if index is not None:
        if (not isinstance(index, dict) or not isinstance(index.get('path'), str)
                or not isinstance(index.get('sha256'), str)):
            raise ValueError('Invalid prepared retrieval index')
        index_path = _narrow(Path(index['path']))
        if (not index_path.is_file() or arena.sha256_file(index_path) != index['sha256']
                or any(index_path.is_relative_to(root) for root in writable)):
            raise ValueError('Prepared retrieval index changed or is writable by the agent')
        # One immutable original-prefix index, never its siblings, build logs,
        # or a shared writable directory that could carry earlier pass state.
        read_only.append(index_path)
    if spec.search_extensions:
        from lean_tools import proof_example_search
        index = config.get('examples_index')
        if (not isinstance(index, dict) or not isinstance(index.get('path'), str)
                or not isinstance(index.get('sha256'), str) or not isinstance(index.get('identity'), dict)):
            raise ValueError('Search extensions require a prepared source example index')
        index_path = _narrow(Path(index['path']))
        if (not index_path.is_file() or arena.sha256_file(index_path) != index['sha256']
                or any(index_path.is_relative_to(root) for root in writable)):
            raise ValueError('Prepared source example index changed or is writable by the agent')
        actual_identity = proof_example_search.inspect_index(index_path).get('identity')
        if (not isinstance(actual_identity, dict)
                or proof_example_search.binding(actual_identity) != index['identity']):
            raise ValueError('Prepared source example index identity changed')
        # Source examples cross the boundary through one immutable file. Never
        # mount its cache directory, sibling corpora, build logs or run history.
        read_only.append(index_path)
    # Explicit HOME paths from no-model tests are deliberately replaced by the
    # capsule home; do not expose any controller CLI history to the agent.
    if backend == 'pi':
        command += ['--dir', '/run/e6-pi-tools']
    for path in dict.fromkeys(read_only):
        if not any(path.is_relative_to(root) for root in writable):
            target = '/run/e6-pi-tools/rg' if backend == 'pi' and path == pi_rg else str(path)
            command += ['--ro-bind', str(path), target]
    for path in sorted(writable, key=lambda item: (len(item.parts), str(item))):
        command += ['--bind', str(path), str(path)]
    statement_view = None
    if reprove:
        from .statement_first import load_view
        statement_view = load_view(config)
        # Overlay after all broad mounts: cached environments on the host are
        # never edited, and original source/proof data are unreadable here.
        for overlay in statement_view['overlays']:
            command += ['--ro-bind', overlay['source'], overlay['target']]
        for overlay in statement_view['git_overlays']:
            command += ['--ro-bind', overlay['source'], overlay['target']]
        for path in statement_view['hidden_files']:
            command += ['--ro-bind', statement_view['empty'], path]
        for path in statement_view['hidden_directories']:
            command += ['--tmpfs', path, '--remount-ro', path]
    command += ['--chdir', str(capsule), '--', *map(str, argv)]
    (capsule / 'isolation.json').write_text(json.dumps({
        'schema_version': 1, 'method': 'bubblewrap_user_mount_namespace',
        'shared_pid_namespace': True, 'capabilities': [], 'home': str(home),
        'readonly': [str(path) for path in dict.fromkeys(read_only)],
        'writable': [str(path) for path in writable],
        'host_mounts_exposed': False,
        'statement_first': statement_view is not None,
        'masked_source_files': [item['target'] for item in statement_view['overlays']] if statement_view else [],
        'masked_compiled_or_history_files': statement_view['hidden_files'] if statement_view else [],
        'masked_history_directories': statement_view['hidden_directories'] if statement_view else [],
    }, indent=2) + '\n', encoding='utf-8')
    return [sys.executable, '-I', str(REPO_ROOT / 'e6/supervisor.py'), '--', *command], environment
