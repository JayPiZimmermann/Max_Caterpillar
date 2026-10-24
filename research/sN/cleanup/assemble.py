#!/usr/bin/env python3
"""Extract declaration chunks (with docstrings/attributes) from Lean files by name.

Used once by the cleanup pass to assemble the `MaxCaterpillar/Count/` files from the
superseded sources (git a503f01).  `get(path, short_name)` returns the text of the unique
top-level declaration with that last name component in `path`, with `private` removed.
"""
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).parent))
from prune import split_commands, resolve  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[3]
_cache = {}


def decls(path):
    if path not in _cache:
        text = (ROOT / path).read_text()
        _cache[path] = [(full, '\n'.join(cmd).rstrip())
                        for cmd, kind, info, full in resolve(split_commands(text))
                        if kind == 'decl' and full]
    return _cache[path]


def get(path, name, keep_private=False):
    hits = [t for full, t in decls(path) if full == name or full.endswith('.' + name)]
    if len(hits) != 1:
        raise SystemExit(f'{path}: {len(hits)} hits for {name}')
    t = hits[0]
    if not keep_private:
        t = re.sub(r'^private ', '', t, flags=re.M)
    return t


def many(path, names, **kw):
    return '\n\n'.join(get(path, n, **kw) for n in names.split())
