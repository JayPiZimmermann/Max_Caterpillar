#!/usr/bin/env python3
"""Resolve the paper's Lean references by declaration name, never stale line numbers."""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
from urllib.parse import quote

ROOT = pathlib.Path(__file__).resolve().parents[1]
LINK_BLOCK_START = '% BEGIN GENERATED EQUATION LINKS'
LINK_BLOCK_END = '% END GENERATED EQUATION LINKS'


def embed_equation_links(manuscript, declarations):
    """Keep copied main.tex files self-contained, and reject unlinked tags."""
    guard = r'''\makeatletter
\AtBeginDocument{%
\let\paper@linked@tagform\tagform@
\def\tagform@#1{%
\ifpaper@displaytag
\ifmeasuring@\else
\ifcsname paper@lean@\paper@equationlabel\endcsname\else
\PackageError{caterpillar}{Missing source link for equation `\paper@equationlabel'}{Run scripts/paper_links.py and copy the updated main.tex.}%
\fi
\fi
\fi
\paper@linked@tagform{#1}%
}%
}
\makeatother'''
    block = '\n'.join([LINK_BLOCK_START, declarations.rstrip(), guard, LINK_BLOCK_END])
    if LINK_BLOCK_START in manuscript:
        pattern = re.escape(LINK_BLOCK_START) + r'.*?' + re.escape(LINK_BLOCK_END)
        manuscript, count = re.subn(pattern, lambda _: block, manuscript, flags=re.S)
        if count != 1:
            raise SystemExit('Expected exactly one generated equation-link block.')
        return manuscript
    if manuscript.count(r'\input{lean-links.tex}') != 1:
        raise SystemExit('Expected the equation-link input or generated block.')
    return manuscript.replace(r'\input{lean-links.tex}', block)


def equation_rows(content):
    """Split align rows, ignoring line breaks inside groups and nested arrays."""
    rows, start, pos, braces, environments = [], 0, 0, 0, 0
    while pos < len(content):
        environment = re.match(r'\\(begin|end)\{[^}]+\}', content[pos:])
        if environment:
            environments += 1 if environment.group(1) == 'begin' else -1
            pos += environment.end()
            continue
        if content.startswith(r'\\', pos):
            if braces == 0 and environments == 0:
                rows.append(content[start:pos])
                start = pos + 2
            pos += 2
            continue
        if content[pos:pos + 2] in (r'\{', r'\}'):
            pos += 2
            continue
        if content[pos] == '{':
            braces += 1
        elif content[pos] == '}':
            braces -= 1
        pos += 1
    rows.append(content[start:])
    return rows


def validate_manuscript(manuscript):
    """Require linked, numbered displays and confine text links to headings."""
    body = manuscript.split(r'\begin{document}', 1)[1]
    if re.search(r'\\\[|\$\$|\\begin\{(?:align\*|alignat\*?|flalign\*?|equation\*?|gather\*?|multline\*?|eqnarray\*?|displaymath)\}', body):
        raise SystemExit('Every display must use numbered align with a Lean mapping.')
    displays = list(re.finditer(r'\\begin\{align\}(.*?)\\end\{align\}', body, re.S))
    labels = []
    for display in displays:
        content = display.group(1)
        found = re.findall(r'\\label\{([^}]+)\}', content)
        if not found or re.search(r'\\(?:notag|nonumber|tag)\b', content):
            raise SystemExit('Every display needs a numbered, labelled Lean link.')
        if ';' in content:
            raise SystemExit('Do not use semicolons inside displayed formulas.')
        for row in equation_rows(content):
            if len(re.findall(r'\\label\{([^}]+)\}', row)) != 1:
                raise SystemExit('Every numbered align row needs exactly one Lean-linked label.')
        labels.extend(found)
    if len(set(labels)) != len(labels):
        raise SystemExit('Duplicate equation labels.')

    def balanced_end(start, opening, closing):
        depth = 0
        for pos in range(start, len(body)):
            if body[pos] == opening:
                depth += 1
            elif body[pos] == closing:
                depth -= 1
                if depth == 0:
                    return pos + 1
        raise SystemExit('Unclosed manuscript heading.')

    headings = []
    for match in re.finditer(
            r'\\begin\{(?:theorem|representationtheorem|lemma|corollary|definition|proof)\}\[', body):
        headings.append((match.start(), balanced_end(match.end() - 1, '[', ']')))
    for match in re.finditer(r'\\paragraph(?:\[[^\]]*\])?\{', body):
        headings.append((match.start(), balanced_end(match.end() - 1, '{', '}')))
    for match in re.finditer(r'\\pfclaim\{[^}]+\}\{', body):
        headings.append((match.start(), balanced_end(match.end() - 1, '{', '}')))
    for match in re.finditer(r'\\(?:leanref|leanid|leanlink|lean|leandecl|leanlinkdecl)\b', body):
        if not any(start <= match.start() < end for start, end in headings):
            raise SystemExit('Lean text links belong in statement or paragraph headings, not prose.')
    return labels


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-url',
                        help='GitHub blob/COMMIT or blob/main URL, or .. for local source links; saves the setting.')
    args = parser.parse_args()
    config_path = ROOT / 'paper/link-config.json'
    config = json.loads(config_path.read_text()) if config_path.exists() else {'base_url': '..'}
    base_url = (args.base_url or config['base_url']).rstrip('/')
    commit = None
    if base_url != '..':
        match = re.fullmatch(r'https://github\.com/[^/]+/[^/]+/blob/([0-9a-f]{40}|main)', base_url)
        if not match:
            raise SystemExit('Use a GitHub blob URL with a full commit or main, or ..')
        commit = match.group(1) if match.group(1) != 'main' else None
    mapping = json.loads((ROOT / 'paper/lean-map.json').read_text())
    tex_base = base_url.replace('%', r'\%').replace('_', r'\_')
    records, lines = [], ['% Generated by scripts/paper_links.py; do not edit.',
                          r'\makeatletter',
                          r'\newcommand{\DeclareSourceEquation}[2]{\expandafter\def\csname paper@lean@#1\endcsname{#2}}',
                          r'\makeatother',
                          r'\newcommand{\leanbase}{' + tex_base + '}']
    for key, entry in mapping.items():
        if 'source_url' in entry:
            if not entry['source_url'].startswith('https://') or entry.get('steps'):
                raise SystemExit('Source equations need an HTTPS source and cannot label proof steps.')
            kind = entry.get('kind', 'literature')
            if kind not in ('literature', 'certificate'):
                raise SystemExit('Unknown non-Lean equation source kind: ' + kind)
            tex_source = entry['source_url'].replace('%', r'\%').replace('_', r'\_').replace('#', r'\#')
            for label in entry.get('equations', []):
                lines.append(r'\DeclareSourceEquation{' + label + '}{' + tex_source + '}')
            records.append(dict(entry, key=key, url=entry['source_url'], kind=kind))
            continue
        path = ROOT / entry['file']
        if commit:
            result = subprocess.run(['git', 'show', commit + ':' + entry['file']],
                                    cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            if result.returncode or result.stdout != path.read_bytes():
                raise SystemExit('Pinned commit does not match current source: ' + entry['file'])
        source = path.read_text()
        pattern = r'^\s*(?:@\[[^\n]*\]\s*)?(?:(?:noncomputable|private|protected)\s+)*(?:theorem|lemma|def|abbrev|structure)\s+' + re.escape(entry['name']) + r'(?=[\s({:\[])'
        matches = list(re.finditer(pattern, source, re.M))
        if len(matches) != 1:
            raise SystemExit('Expected one declaration for ' + key + ': ' + entry['name'])
        line = source.count('\n', 0, matches[0].start()) + 1
        while not source.splitlines()[line - 1].strip():
            line += 1
        url = base_url + '/' + quote(entry['file'], safe='/') + '#L' + str(line)
        for label in entry.get('equations', []) + entry.get('steps', []):
            lines.append(r'\DeclareLeanEquation{' + label + '}{' + entry['file'] +
                         '}{' + str(line) + '}')
        records.append(dict(entry, key=key, line=line, url=url,
                            sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
    by_declaration = {(entry['file'], entry['name']): entry for entry in records if 'file' in entry}
    main_path = ROOT / 'paper/main.tex'
    manuscript = main_path.read_text()
    def refresh_declaration(match):
        command, path, _, name = match.groups()
        entry = by_declaration.get((path, name))
        if entry is None:
            raise SystemExit('Unmapped Lean declaration: ' + path + ': ' + name)
        return '\\' + command + '{' + path + '}{' + str(entry['line']) + '}{' + name + '}'
    manuscript = re.sub(r'\\(leandecl|leanlinkdecl)\{([^}]+)\}\{(\d+)\}\{([^}]+)\}',
                        refresh_declaration, manuscript)
    declared_labels = [label for entry in records for label in entry.get('equations', [])]
    equation_labels = validate_manuscript(manuscript)
    if set(declared_labels) != set(equation_labels) or len(set(declared_labels)) != len(declared_labels):
        raise SystemExit('Equation labels and Lean equation mappings differ.')
    declared_steps = [label for entry in records for label in entry.get('steps', [])]
    proof_steps = re.findall(r'\\pfstep\{([^}]+)\}', manuscript)
    if (set(declared_steps) != set(proof_steps)
            or len(set(declared_steps)) != len(declared_steps)
            or len(set(proof_steps)) != len(proof_steps)):
        raise SystemExit('Proof steps and Lean step mappings differ.')
    declarations = '\n'.join(lines) + '\n'
    main_path.write_text(embed_equation_links(manuscript, declarations))
    (ROOT / 'paper/lean-links.tex').write_text(declarations)
    (ROOT / 'paper/lean-links.json').write_text(json.dumps(records, indent=2) + '\n')
    config_path.write_text(json.dumps({'base_url': base_url}, indent=2) + '\n')
    lean_count = sum('file' in entry for entry in records)
    print('Resolved {} Lean references and {} other source references (base {}).'.format(
        lean_count, len(records) - lean_count, base_url))


if __name__ == '__main__':
    main()
