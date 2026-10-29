"""Regenerate the generated Lean modules from `data/k42/` and compare them byte for byte.

The four generator lanes write every module under `Erdos188/UpperBound/Data/` and
`Erdos188/UpperBound/Checks/`. This script runs, each as its own Python process:

1. `export_certificate.py`, a fresh export of the route and safety certificate
   `certificate.ndjson` (with its `manifest.json`) from the six gold inputs;
2. the four lanes in order, cover, routes, membership, safety, into one fresh
   output root (safety reads the routes lane's site modules from that root);
3. a comparison of the fresh `Data/` and `Checks/` trees with the committed ones,
   by file name and raw bytes, in both directions.

Run from the repository root with Python 3 (standard library only):

    python3 scripts/regenerate.py

The exit code is 0 exactly when every lane exited 0 and the two trees are equal.
Equality covers only the generated modules; the hand-written modules beside them
are neither generated nor compared.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
ROOT = SCRIPTS.parent
GENERATORS = SCRIPTS / 'lean_generators'
TARGET = ROOT / 'Erdos188' / 'UpperBound'
SUBTREES = ('Data', 'Checks')


def run(name: str, command: list[str]) -> None:
    """Run one stage as a child process; stop on a nonzero exit."""
    print(f'== {name}', flush=True)
    started = time.monotonic()
    result = subprocess.run(command)
    if result.returncode != 0:
        raise SystemExit(f'{name} exited {result.returncode}')
    print(f'== {name} exited 0 in {time.monotonic() - started:.1f}s', flush=True)


def inventory(root: Path) -> dict[str, Path]:
    """Every file of the generated subtrees of ``root``, by relative path."""
    files = {}
    for subtree in SUBTREES:
        for path in sorted((root / subtree).rglob('*')):
            if path.is_symlink() or not (path.is_file() or path.is_dir()):
                raise SystemExit(f'unexpected entry {path}')
            if path.is_file():
                files[path.relative_to(root).as_posix()] = path
    return files


def compare(fresh: Path, target: Path) -> bool:
    """Compare the generated subtrees by name and raw bytes; print the counts."""
    fresh_files = inventory(fresh)
    target_files = inventory(target)
    missing = sorted(set(target_files) - set(fresh_files))
    extra = sorted(set(fresh_files) - set(target_files))
    common = sorted(set(fresh_files) & set(target_files))
    different = [
        name for name in common
        if fresh_files[name].read_bytes() != target_files[name].read_bytes()
    ]
    print(
        f'committed {len(target_files)}, regenerated {len(fresh_files)}, '
        f'identical {len(common) - len(different)}, different {len(different)}, '
        f'missing {len(missing)}, extra {len(extra)}'
    )
    for label, names in (('different', different), ('missing', missing), ('extra', extra)):
        for name in names:
            print(f'  {label}: {name}')
    return not (different or missing or extra)


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.split('\n\n')[0],
    )
    parser.add_argument('--work-dir', type=Path,
                        help='fresh directory for the export and the generated tree '
                             '(default: a new temporary directory)')
    parser.add_argument('--target', type=Path, default=TARGET,
                        help='the tree holding the committed Data/ and Checks/')
    parser.add_argument('--keep', action='store_true',
                        help='keep the work directory after a successful comparison')
    args = parser.parse_args()
    if args.work_dir is None:
        work = Path(tempfile.mkdtemp(prefix='erdos188-regen-'))
    else:
        work = args.work_dir.absolute()
        work.mkdir(parents=True, exist_ok=False)
    export = work / 'export'
    out = work / 'generated'
    python = [sys.executable, '-B']
    print(f'work directory {work}')

    run('export', [*python, str(SCRIPTS / 'export_certificate.py'), '--output', str(export)])
    manifest = json.loads((export / 'manifest.json').read_text())
    print(f'certificate sha256 {manifest["stream"]["sha256"]} '
          f'({manifest["stream"]["records"]} records, {manifest["stream"]["bytes"]} bytes)')
    run('cover', [*python, str(GENERATORS / 'gen_cover_chunks.py'), '--out-dir', str(out)])
    run('routes', [*python, str(GENERATORS / 'gen_routes_chunks.py'),
                   '--certificate', str(export / 'certificate.ndjson'), '--out-dir', str(out)])
    run('membership', [*python, str(GENERATORS / 'gen_membership_chunks.py'), '--out-dir', str(out)])
    run('safety', [*python, str(GENERATORS / 'gen_safety_chunks.py'),
                   '--cert-dir', str(export), '--out-dir', str(out)])

    print('== compare')
    equal = compare(out, args.target)
    if equal and not args.keep:
        shutil.rmtree(work)
    elif not equal:
        print(f'kept {work} for inspection')
    print('generated tree MATCHES the committed tree' if equal
          else 'generated tree DIFFERS from the committed tree')
    return 0 if equal else 1


if __name__ == '__main__':
    raise SystemExit(main())
