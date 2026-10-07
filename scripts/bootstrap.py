#!/usr/bin/env python3
"""Reproduce the pinned project environment; preserve unrelated checkout edits."""
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent
ELAN = Path(os.environ.get('QUADRATIC_MOAT_ELAN', str(Path.home() / '.elan/bin/elan')))
ENV = dict(os.environ, ELAN_HOME=str(ROOT / '.toolchains/elan'))
DEPS = [
    ('ClassFieldTheory', 'https://github.com/n-yamaguchi-0729/ClassFieldTheory.git',
     '2eb22d6485af45f29c5219de6c49f196a61c4f49'),
    ('AINTLIB', 'https://github.com/CBirkbeck/AINTLIB.git',
     '160e446617a2168c34c95bbe7a76c4105b392434'),
]

def run(args, **kwargs):
    return subprocess.run(args, cwd=ROOT, env=ENV, check=True, **kwargs)

run([str(ELAN), 'toolchain', 'install', (ROOT / 'lean-toolchain').read_text().strip()])
(ROOT / '.lake/packages').mkdir(parents=True, exist_ok=True)
for name, url, rev in DEPS:
    folder = ROOT / '.lake/packages' / name
    if not folder.exists():
        run(['git', 'clone', '--filter=blob:none', '--no-checkout', url, str(folder)])
        run(['git', '-C', str(folder), 'checkout', rev])
    actual = run(['git', '-C', str(folder), 'rev-parse', 'HEAD'], capture_output=True,
                 text=True).stdout.strip()
    if actual != rev:
        raise SystemExit(f'{name}: found {actual}, expected {rev}; preserving existing checkout.')
    patch = ROOT / 'patches' / f'{name}-lean4341.patch'
    reverse = subprocess.run(['git', '-C', str(folder), 'apply', '--reverse', '--check',
                              str(patch)], capture_output=True)
    if reverse.returncode:
        run(['git', '-C', str(folder), 'apply', '--check', str(patch)])
        run(['git', '-C', str(folder), 'apply', str(patch)])
run([str(ROOT / 'lakew'), 'update'])
print('Pinned environment ready. Run ./lakew build QuadraticMoat and the axiom audits.')
