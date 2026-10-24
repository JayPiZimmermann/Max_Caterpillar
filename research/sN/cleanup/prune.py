#!/usr/bin/env python3
"""Split Lean files into top-level commands and prune unused declarations.

Usage: prune.py USED_LIST FILE...   (prints pruned files to stdout, separated by markers)
USED_LIST: text file with one fully qualified declaration name per line.
A declaration is kept iff its fully qualified name is in USED_LIST (instances always kept).
"""
import re
import sys

DECL_KW = ('theorem', 'lemma', 'def', 'abbrev', 'structure', 'inductive', 'instance', 'class')
MODIFIERS = ('noncomputable', 'protected', 'private', 'partial', 'unsafe', 'nonrec')
CONT_PREFIX = ('|', 'termination_by', 'decreasing_by', ')', ']', '}', 'where', 'deriving')


def comment_delta(line):
    """Net change of block-comment depth on a line (ignores strings, `--` comments)."""
    depth, i = 0, 0
    while i < len(line):
        if line.startswith('--', i) and depth == 0:
            break
        if line.startswith('/-', i):
            depth += 1
            i += 2
        elif line.startswith('-/', i):
            depth -= 1
            i += 2
        else:
            i += 1
    return depth


def split_commands(text):
    lines = text.split('\n')
    raw, cur, depth = [], [], 0
    for line in lines:
        starts = (depth == 0 and line and not line[0].isspace()
                  and not line.startswith(CONT_PREFIX))
        if starts and cur:
            raw.append(cur)
            cur = []
        cur.append(line)
        depth += comment_delta(line)
    if cur:
        raw.append(cur)
    # merge prefixes (docstrings, attributes, `... in`) into the following command
    cmds, carry = [], []
    for cmd in raw:
        joined = '\n'.join(cmd).strip()
        is_doc = joined.startswith('/--') and joined.endswith('-/')
        is_attr = re.fullmatch(r'@\[[^\]]*\]', joined) is not None
        is_in = re.fullmatch(r'(open|set_option)\b[^\n]*\bin', joined) is not None
        if is_doc or is_attr or is_in:
            carry.extend(cmd)
            continue
        cmds.append(carry + cmd)
        carry = []
    if carry:
        cmds.append(carry)
    return cmds


def classify(cmd):
    """Return (kind, info)."""
    text = '\n'.join(cmd)
    body = text
    # strip leading docstring
    while True:
        m = (re.match(r'\s*/--.*?-/\s*', body, re.S) or
             re.match(r'\s*(@\[[^\]]*\]|open\b[^\n]*\bin|set_option\b[^\n]*\bin)\s*', body))
        if not m:
            break
        body = body[m.end():]
    toks = body.split()
    i = 0
    while i < len(toks) and toks[i] in MODIFIERS:
        i += 1
    if i < len(toks) and toks[i] in DECL_KW:
        kw = toks[i]
        name = toks[i + 1] if i + 1 < len(toks) else ''
        if kw == 'instance' and (name.startswith(('(', '[', '{', ':')) or name == ':'):
            name = None
        if name:
            name = re.split(r'[\s(\[{:]', name)[0]
        return 'decl', (kw, name)
    first = toks[0] if toks else ''
    if first in ('namespace', 'section', 'end', 'variable', 'open', 'universe', 'attribute',
                 'import', 'noncomputable', 'set_option', 'local', 'scoped'):
        return 'ctx', first
    if text.lstrip().startswith('/-!'):
        return 'moddoc', None
    return 'other', None


def resolve(cmds, prefix_ns=()):
    stack = []  # entries: ('ns', [parts]) or ('sec', name)
    out = []
    for cmd in cmds:
        kind, info = classify(cmd)
        full = None
        if kind == 'ctx':
            toks = ' '.join(cmd).split()
            if toks[0] == 'namespace':
                stack.append(('ns', toks[1].split('.')))
            elif toks[0] == 'section':
                stack.append(('sec', toks[1] if len(toks) > 1 else None))
            elif toks[0] == 'noncomputable' and len(toks) > 1 and toks[1] == 'section':
                stack.append(('sec', toks[2] if len(toks) > 2 else None))
            elif toks[0] == 'end':
                if stack:
                    stack.pop()
        if kind == 'decl' and info[1]:
            ns = [p for t, v in stack if t == 'ns' for p in v]
            name = info[1]
            if name.startswith('_root_.'):
                full = name[len('_root_.'):]
            else:
                full = '.'.join(ns + [name])
        out.append((cmd, kind, info, full))
    return out


def prune(path, used):
    text = open(path).read()
    res = resolve(split_commands(text))
    kept, dropped = [], []
    lines = []
    for cmd, kind, info, full in res:
        if kind == 'decl' and info[0] != 'instance':
            if full in used:
                kept.append(full)
            else:
                dropped.append(full)
                continue
        lines.extend(cmd)
    return '\n'.join(lines), kept, dropped


if __name__ == '__main__':
    used = set(l.strip() for l in open(sys.argv[1]) if l.strip())
    for p in sys.argv[2:]:
        txt, kept, dropped = prune(p, used)
        print('=== FILE', p, 'kept', len(kept), 'dropped', len(dropped))
        print('--- dropped:', ' '.join(d.split('.')[-1] for d in dropped))
        import os
        if os.environ.get('OUT'):
            out = os.path.join(os.environ['OUT'], p.replace('/', '__'))
            open(out, 'w').write(txt)
