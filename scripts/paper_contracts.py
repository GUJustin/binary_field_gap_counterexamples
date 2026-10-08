#!/usr/bin/env python3
"""Textual paper/Lean drift checks. Uses Python's standard library, not Lean."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
BASELINE = Path('formalization/paper-index.json')
INDEX = Path('formalization/PAPER_INDEX.md')
KINDS = 'theorem|lemma|corollary|proposition|definition|remark'


def digest(value: str | bytes) -> str:
    return hashlib.sha256(value.encode() if isinstance(value, str) else value).hexdigest()


def normalize(text: str) -> str:
    return ' '.join(text.split())


def tex_without_comments(text: str) -> str:
    return re.sub(r'(?<!\\)%[^\n]*', '', text)


def tex_sources(root: Path) -> dict[str, str]:
    """Follow literal input/include commands from the canonical entry point."""
    result = {}

    def visit(name: str):
        path = Path(name)
        if not path.suffix:
            path = path.with_suffix('.tex')
        name = path.as_posix()
        if name in result:
            return
        text = (root / path).read_text()
        result[name] = text
        for child in re.findall(r'\\(?:input|include)\s*\{([^{}]+)\}', tex_without_comments(text)):
            visit(child)

    visit('binary-field-counterexamples.tex')
    return result


def brace_group(text: str, start: int) -> tuple[str, int]:
    if text[start] != '{':
        raise ValueError('Expected a braced aux field')
    depth = 1
    i = start + 1
    while i < len(text):
        if text[i] == '\\':
            i += 2
            continue
        depth += (text[i] == '{') - (text[i] == '}')
        if not depth:
            return text[start + 1:i], i + 1
        i += 1
    raise ValueError('Unclosed aux field')


def aux_labels(text: str) -> dict[str, dict]:
    labels = {}
    for match in re.finditer(r'\\newlabel\{([^{}]+)\}', text):
        name = match[1]
        if name.endswith('@cref'):
            continue
        payload, _ = brace_group(text, match.end())
        fields, pos = [], 0
        while pos < len(payload) and payload[pos] == '{':
            field, pos = brace_group(payload, pos)
            fields.append(field)
        if len(fields) >= 4:
            labels[name] = dict(number=fields[0], page=fields[1], title=fields[2], anchor=fields[3])
    return labels


def lean_without_comments(text: str) -> str:
    """Preserve line boundaries; handle nested Lean block comments and strings."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
                out.append(' ')
            else:
                if text[i] == '\n':
                    out.append('\n')
                i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == '\\' and i + 1 < len(text):
                i += 1
                out.append(text[i])
            elif text[i] == '"':
                quoted = False
            i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
            out.append(' ')
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            quoted = text[i] == '"'
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('Unclosed Lean comment')
    if quoted:
        raise ValueError('Unclosed Lean string')
    return ''.join(out)


# This is intentionally a restricted source inventory, not a Lean parser. New
# command forms must get extraction tests before they enter audited modules.
COMMAND = re.compile(
    r'(?:(?:public|private|protected|noncomputable|unsafe|partial) +)*'
    r'(theorem|lemma|def|abbrev|axiom|namespace|section|end|variable|universe|'
    r'open|include|omit|import|set_option|attribute|module)\b')
IDENTIFIER = r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*"
# Attributes such as to_additive can generate declarations. Do not silently
# treat arbitrary user-defined attributes as harmless metadata.
SAFE_ATTRIBUTES = {'simp', 'expose'}


def lean_commands(text: str, path: str):
    """Yield (start, end-of-command-keyword, kind) in the supported house style.

    Commands and attribute blocks start at column zero; continuations and
    proofs are indented. Only named theorem/lemma/def/abbrev/axiom declarations
    are inventoried. Unsupported commands, declaration modifiers and generators
    fail closed. This does not enumerate compiler-generated auxiliary constants.
    """
    commands, pending_attribute = [], None
    offset = 0
    for line_number, line in enumerate(text.splitlines(keepends=True), 1):
        stripped = line.strip()
        if not stripped:
            offset += len(line)
            continue
        if line[0].isspace():
            # Indented top-level commands would otherwise be swallowed by a
            # preceding proof. These keywords are not needed as tactic steps.
            if re.match(r'(?:@\[|(?:(?:public|private|protected|noncomputable|unsafe|partial) +)*'
                        r'(?:theorem|lemma|def|abbrev|axiom|namespace|section|end|'
                        r'instance|structure|class|inductive|mutual|macro|syntax|elab|opaque|example|'
                        r'set_option|open|attribute|export|notation|local|scoped|import|module)\b)', stripped):
                raise ValueError(f'{path}:{line_number}: commands must start in column zero')
            if re.match(r'(?:where|deriving)\b', stripped):
                raise ValueError(f'{path}:{line_number}: generated declarations are unsupported')
            offset += len(line)
            continue
        rest, consumed = line, 0
        while rest.startswith('@['):
            close = rest.find(']')
            if close < 0:
                raise ValueError(f'{path}:{line_number}: multiline/complex attributes unsupported')
            attrs = {a.strip() for a in rest[2:close].split(',')}
            if not attrs or not attrs <= SAFE_ATTRIBUTES:
                raise ValueError(f'{path}:{line_number}: unsupported or generating attribute {attrs}')
            if pending_attribute is None:
                pending_attribute = offset
            consumed += close + 1
            rest = line[consumed:]
            spaces = len(rest) - len(rest.lstrip(' \t'))
            consumed += spaces
            rest = line[consumed:]
        if not rest.strip():
            offset += len(line)
            continue
        match = COMMAND.match(rest)
        if not match:
            raise ValueError(f'{path}:{line_number}: unsupported column-zero Lean command: {rest.strip()}')
        modifiers = rest[:match.start(1)].split()
        if any(m in {'private', 'unsafe', 'partial'} for m in modifiers):
            raise ValueError(f'{path}:{line_number}: unsupported declaration modifier {modifiers}')
        if pending_attribute is not None and match[1] not in {'theorem', 'lemma', 'def', 'abbrev', 'section'}:
            raise ValueError(f'{path}:{line_number}: unsupported attribute target')
        start = pending_attribute if pending_attribute is not None else offset
        commands.append((start, offset + consumed + match.end(), match[1]))
        pending_attribute = None
        offset += len(line)
    if pending_attribute is not None:
        raise ValueError(f'{path}: attribute without declaration')
    return commands


def theorem_header(text: str) -> str:
    """Find the declaration assignment, skipping binders and type-level lets.

    The type itself can contain arbitrarily many outer ``let x := ...``
    bindings. Their assignments are not the theorem's proof delimiter.
    """
    depth, pending_lets, i = 0, 0, 0
    while i < len(text):
        c = text[i]
        if c == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                    continue
                if text[i] == '"':
                    break
                i += 1
        if c in '({[':
            depth += 1
        elif c in ')}]':
            depth -= 1
        elif depth == 0 and (binding := re.match(r'(?:letI|let|haveI|have)\b', text[i:])) and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == '_')):
            pending_lets += 1
            i += len(binding[0]) - 1
        elif depth == 0 and text.startswith(':=', i):
            if pending_lets:
                pending_lets -= 1
                i += 1
            else:
                if not re.match(r'\s*by\b', text[i + 2:]):
                    raise ValueError('Expected theorem proof := by; unsupported or ambiguous declaration syntax')
                return text[:i]
        i += 1
    raise ValueError('Theorem has no := delimiter; unsupported declaration syntax')


def lean_declarations(text: str, path: str) -> dict[str, dict]:
    """Extract supported source declarations and resolve their namespace stack.

    Definitions are hashed in full; theorem proofs are excluded from contracts.
    Namespace and section scopes are distinct: ending a section cannot pop a
    namespace. Unsupported syntax fails rather than disappearing from coverage.
    """
    text = lean_without_comments(text)
    commands = lean_commands(text, path)
    declarations, context, scopes = {}, [], []
    for n, (start, head_end, kind) in enumerate(commands):
        chunk = text[start:commands[n + 1][0] if n + 1 < len(commands) else len(text)]
        tail = text[head_end:start + len(chunk)].strip()
        if kind in {'theorem', 'lemma', 'def', 'abbrev', 'axiom'}:
            # Lean can accept a second command on the same physical line.
            # Reject embedded declaration/generator keywords instead of treating
            # that command as an untracked part of the preceding proof.
            unquoted_tail = re.sub(r'"(?:\\.|[^"\\])*"', '""', tail)
            if re.search(r'(?<![\w.])(?:theorem|lemma|def|abbrev|axiom|opaque|instance|'
                         r'structure|class|inductive|mutual|macro|syntax|elab|namespace|'
                         r'section|module|import|attribute|export|notation|deriving|where)\b',
                         unquoted_tail):
                raise ValueError(f'Embedded command/generator unsupported in {path}; use one command per line')
            name_match = re.match(r'(' + IDENTIFIER + r')(?=\s|[:({\[])', tail)
            if not name_match or name_match[1] == '_':
                raise ValueError(f'Unnamed/unsupported declaration in {path}')
            name = name_match[1]
            namespace = '.'.join(label for scope, label in scopes if scope == 'namespace')
            qualified = (namespace + '.' + name) if namespace else name
            if name.startswith('_root_.'):
                qualified = name[len('_root_.'):]
            contract = theorem_header(chunk) if kind in {'theorem', 'lemma'} else chunk
            key = f'{path}::{qualified}'
            if key in declarations:
                raise ValueError(f'Duplicate declaration key {key}')
            declarations[key] = dict(name=name, qualified_name=qualified, kind=kind, source=path,
                                     statement_sha256=digest(normalize(contract)),
                                     context_sha256=digest(normalize('\n'.join(context))),
                                     admission='axiom' if kind == 'axiom' else
                                     'sorry' if re.search(r'\bsorry\b', re.sub(
                                         r'"(?:\\.|[^"\\])*"', '""', chunk)) else 'no_textual_admission')
        else:
            if kind in {'namespace', 'section', 'end'}:
                if tail and not re.fullmatch(IDENTIFIER, tail):
                    raise ValueError(f'Unsupported {kind} syntax in {path}: {tail}')
                if kind == 'namespace' and (not tail or tail.startswith('_root_.')):
                    raise ValueError(f'Unsupported namespace in {path}: {tail}')
                if kind == 'end':
                    if not scopes or (tail and tail != scopes[-1][1]):
                        raise ValueError(f'Mismatched end in {path}: {tail}')
                    scopes.pop()
                else:
                    scopes.append((kind, tail))
            elif kind in {'set_option', 'open'} and re.search(r'\bin\b', tail):
                raise ValueError(f'Wrapped commands (... in) unsupported in {path}')
            elif kind == 'attribute' and not re.fullmatch(
                    r'\[local instance\](?:\s+' + IDENTIFIER + r')+', tail):
                raise ValueError(f'Standalone attribute unsupported in {path}: {tail}')
            context.append(chunk)
    if any(scope == 'namespace' for scope, _ in scopes):
        raise ValueError(f'Unclosed namespace in {path}')
    return declarations


def lean_module_contract(text: str) -> str:
    """Include imports/context even in declaration-free umbrella modules."""
    lean_declarations(text, '<module contract>')  # Apply the same fail-closed validation.
    text = lean_without_comments(text)
    commands = lean_commands(text, '<module contract>')
    parts = [text[:commands[0][0]]] if commands else [text]
    for n, (start, _, kind) in enumerate(commands):
        chunk = text[start:commands[n + 1][0] if n + 1 < len(commands) else len(text)]
        parts.append(theorem_header(chunk) if kind in {'theorem', 'lemma'} else chunk)
    return digest(normalize('\n'.join(parts)))


def snapshot(root: Path) -> tuple[dict, list[str]]:
    errors = []
    sources = tex_sources(root)
    labels = aux_labels((root / 'binary-field-counterexamples.aux').read_text())
    statements = {}
    for path, raw in sources.items():
        text = tex_without_comments(raw)
        for match in re.finditer(r'\\begin\{(' + KINDS + r')\}(.*?)\\end\{\1\}', text, re.S):
            kind, body = match[1], match[2]
            # The first label belongs to the statement; later equation labels do not.
            names = re.findall(r'\\label\{([^{}]+)\}', body)
            if not names:
                errors.append(f'unlabelled_statement: {path}: {kind}')
                continue
            name = names[0]
            if name not in labels:
                errors.append(f'missing_label: {path}: {name}; rebuild binary-field-counterexamples.pdf')
                continue
            data = labels[name]
            if name in statements:
                errors.append(f'duplicate_label: {name}')
            body = re.sub(r'\\label\{[^{}]+\}', '', body)
            statements[name] = dict(kind=kind, source=path, **data,
                                    citation=f'{kind.title()} {data["number"]}',
                                    pdf=f'../binary-field-counterexamples.pdf#page={data["page"]}',
                                    statement_sha256=digest(normalize(body)))
    # latexmk's recorded source digests survive copying/checkouts, unlike mtimes.
    fdb = root / 'binary-field-counterexamples.fdb_latexmk'
    if not fdb.exists():
        errors.append('freshness_unknown: binary-field-counterexamples.fdb_latexmk missing; run latexmk')
    else:
        records = dict(re.findall(r'^  "([^"]+)" [\d.]+ \d+ ([0-9a-f]{32}) ', fdb.read_text(), re.M))
        for path in sources:
            expected = records.get(path) or records.get(str(root / path))
            actual = hashlib.md5((root / path).read_bytes()).hexdigest()
            if expected != actual:
                errors.append(f'stale_pdf_source: {path}; run latexmk')
        # A PDF predating this build's aux is inconclusive; content fingerprints
        # below detect replacements against the reviewed baseline.
        pdf = root / 'binary-field-counterexamples.pdf'
        if not pdf.exists() or not pdf.read_bytes().startswith(b'%PDF-'):
            errors.append('missing_or_invalid_pdf: binary-field-counterexamples.pdf')
        elif pdf.stat().st_mtime + 2 < (root / 'binary-field-counterexamples.aux').stat().st_mtime:
            errors.append('stale_pdf_aux: binary-field-counterexamples.pdf predates binary-field-counterexamples.aux')
    lean, modules = {}, {}
    folder = root / 'formalization/BinaryFieldCounterexamples'
    paths = sorted(folder.rglob('*.lean'))
    umbrella = folder.with_suffix('.lean')
    if umbrella.exists():
        paths.append(umbrella)
    for path in paths:
        name = path.relative_to(root).as_posix()
        lean.update(lean_declarations(path.read_text(), name))
        modules[name] = lean_module_contract(path.read_text())
    for key, declaration in lean.items():
        if declaration['admission'] in {'sorry', 'axiom'} and declaration['kind'] not in {'theorem', 'lemma'}:
            errors.append(f'admitted_definition_or_axiom: {key}')
    pins = ['formalization/lean-toolchain', 'formalization/lakefile.toml', 'formalization/lake-manifest.json']
    result = dict(schema=1, paper_statements=statements, lean_declarations=lean,
                  lean_module_sha256=modules,
                  dependency_sha256={p: digest((root / p).read_bytes()) for p in pins if (root / p).exists()},
                  source_sha256={p: digest(s) for p, s in sorted(sources.items())},
                  artifacts={p: digest((root / p).read_bytes()) for p in ['binary-field-counterexamples.pdf', 'binary-field-counterexamples.aux'] if (root / p).exists()})
    return result, errors


def compare(before: dict, after: dict) -> dict[str, list[str]]:
    changes = {}

    def add(category, item):
        changes.setdefault(category, []).append(item)

    for collection, prefix in [('paper_statements', 'paper'), ('lean_declarations', 'lean')]:
        old, new = before[collection], after[collection]
        for key in sorted(old.keys() - new.keys()):
            add(prefix + '_removed', old[key].get('citation', key))
        for key in sorted(new.keys() - old.keys()):
            add(prefix + '_added', new[key].get('citation', key))
        for key in sorted(old.keys() & new.keys()):
            label = new[key].get('citation', key)
            if old[key]['statement_sha256'] != new[key]['statement_sha256']:
                add(prefix + '_statement_changed', label)
            if prefix == 'paper':
                if old[key]['number'] != new[key]['number'] or old[key]['kind'] != new[key]['kind']:
                    add('paper_numbering_changed', f'{old[key]["citation"]} -> {label}')
                if old[key]['page'] != new[key]['page']:
                    add('paper_page_changed', f'{label}: {old[key]["page"]} -> {new[key]["page"]}')
            elif old[key]['context_sha256'] != new[key]['context_sha256']:
                add('lean_context_changed', label)
            if prefix == 'lean' and old[key].get('admission') != new[key].get('admission'):
                add('lean_admission_changed', f'{label}: {old[key].get("admission")} -> {new[key].get("admission")}')
                if new[key].get('admission') in {'sorry', 'axiom'}:
                    add('lean_admission_introduced', label)
    for path in sorted(before.get('dependency_sha256', {}).keys() | after.get('dependency_sha256', {}).keys()):
        if before.get('dependency_sha256', {}).get(path) != after.get('dependency_sha256', {}).get(path):
            add('dependency_changed', path)
    for path in sorted(before.get('lean_module_sha256', {}).keys() | after.get('lean_module_sha256', {}).keys()):
        if before.get('lean_module_sha256', {}).get(path) != after.get('lean_module_sha256', {}).get(path):
            add('lean_module_contract_changed', path)
    for path in sorted(before['source_sha256'].keys() | after['source_sha256'].keys()):
        if before['source_sha256'].get(path) != after['source_sha256'].get(path):
            add('paper_source_changed', path)
    for path in sorted(before['artifacts'].keys() | after['artifacts'].keys()):
        if before['artifacts'].get(path) != after['artifacts'].get(path):
            add('build_artifact_changed', path)
    return changes


def render_index(data: dict) -> str:
    lines = ['# Paper statement index', '',
             'Generated by the explicit refresh command below. Public references come',
             'from the compiled `binary-field-counterexamples.aux`; links open the corresponding page of `binary-field-counterexamples.pdf`.',
             'The JSON baseline retains internal labels only as machine matching keys.', '',
             '## Check changes', '', 'Run from the repository root:', '', '```sh',
             'python3 scripts/paper_contracts.py check',
             'python3 scripts/test_paper_contracts.py', '```', '',
             '`check` never writes the baseline. Exit 0 means no detected drift; exit 1',
             'means drift or stale build evidence; exit 2 means missing/invalid input.',
             'The report counts additions, removals, statement changes, numbering changes,',
             'page changes, Lean context changes, source changes, and build changes separately.', '',
             'Raw PDF/aux byte changes are informational: fresh builds can change PDF metadata.',
             'Source, contract, public numbering, page, context, and dependency drift fail the check.', '',
             'After reviewing each change, rebuild the paper and explicitly accept a new baseline:', '',
             '```sh', 'latexmk -pdf -interaction=nonstopmode -halt-on-error binary-field-counterexamples.tex',
             'python3 scripts/paper_contracts.py refresh --reason "Reviewed updated paper and Lean contracts"', 'python3 scripts/paper_contracts.py check', '```', '',
             'The required reason is recorded in the JSON baseline. CI runs only `check`.',
             '`--check` is an alias for `check`. Use `mapping` for a JSON label-to-public-reference map.', '',
             'Refresh refuses missing labels and stale source fingerprints. Freshness compares',
             'literal TeX inputs with the MD5 records from latexmk, plus PDF validity and',
             'PDF/aux timestamps; this is build evidence, not a proof of PDF/source identity.',
             'Source and artifact SHA-256 hashes then pin the reviewed baseline.', '',
             '## Scope and limits', '',
             'Paper hashes cover labelled theorem, lemma, corollary, proposition, definition,',
             'and remark environments reachable through literal `input`/`include` commands',
             'from `binary-field-counterexamples.tex`. Comments, labels, and whitespace are normalized; statement',
             'wording and formulas remain significant. Changes elsewhere in the paper',
             '(including macros and proofs) are separately reported as source changes.', '',
             'Lean hashes cover supported named source declarations throughout',
             '`formalization/BinaryFieldCounterexamples/**/*.lean` and its root module.',
             'They include full definition bodies (these determine',
             'the proposition), and theorem/lemma headers before the outer `:=`, excluding',
             'their proof bodies. Surrounding imports, variables, namespaces, and other',
             'recognized commands are conservatively hashed as context. Nested comments',
             'and whitespace are normalized. Commands must start in column zero and theorem',
             'proofs must use `:= by`; type-level let bindings are retained. This is',
             'a house-style lexical checker, not a general Lean parser or an enumeration of',
             'the elaborated environment. Same-line and separate-line `@[simp]` / `@[expose]`',
             'attributes are supported; namespace and section scopes determine fully qualified names.',
             'Private declarations, declaration-generating attributes, structures, instances,',
             'inductives, macros, and command wrappers currently fail closed. Extend the checker',
             'and regression suite deliberately before using these forms in audited modules;',
             'this is a tooling limitation, not a mathematical API policy. Compiler-generated',
             'auxiliary constants are not individually inventoried. Lean compilation',
             'remains a separate check. Toolchain, lakefile, and dependency manifest fingerprints',
             'detect pin changes. Imports are part of the context hashes; changes to imported',
             'external APIs outside this package require separate review. Textual `sorry`/`axiom`',
             'status is reported separately; replacing a theorem proof with a complete proof',
             'does not fail the contract check. Absence of these tokens is not a kernel audit.',
             'Admitted definitions and axioms are rejected even during explicit refresh.',
             'No hashes establish semantic equivalence or theorem coverage;',
             'a changed signature may strengthen, weaken, or merely restate a claim and needs review.', '',
             '## Public references', '', '| Statement | PDF page |', '| --- | ---: |']
    for value in data['paper_statements'].values():
        lines.append(f'| [{value["citation"]}]({value["pdf"]}) | {value["page"]} |')
    lines.extend(['', f'Indexed: {len(data["paper_statements"])} paper statements and {len(data["lean_declarations"])} Lean declarations.', ''])
    return '\n'.join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', nargs='?', choices=['check', 'refresh', 'mapping'])
    parser.add_argument('--check', action='store_true', help='alias for check')
    parser.add_argument('--reason', help='required review explanation for explicit refresh')
    parser.add_argument('--root', type=Path, default=ROOT, help='repository root (defaults to script parent)')
    args = parser.parse_args()
    if args.check:
        if args.mode and args.mode != 'check':
            parser.error('--check cannot be combined with another mode')
        args.mode = 'check'
    if not args.mode:
        parser.error('choose check, refresh, or mapping')
    if args.mode == 'refresh' and not (args.reason and args.reason.strip()):
        parser.error('refresh requires --reason explaining the reviewed change')
    root = args.root.resolve()
    try:
        current, errors = snapshot(root)
        if args.mode == 'mapping':
            print(json.dumps({key: {field: value[field] for field in ['kind', 'number', 'page', 'citation', 'pdf', 'source']}
                              for key, value in current['paper_statements'].items()}, indent=2))
            return int(bool(errors))
        if errors:
            print(json.dumps({'status': 'invalid_build', 'errors': errors}, indent=2))
            return 1
        if args.mode == 'refresh':
            current['refresh_reason'] = args.reason.strip()
            (root / BASELINE).write_text(json.dumps(current, indent=2, sort_keys=True) + '\n')
            (root / INDEX).write_text(render_index(current))
            print('Refreshed reviewed baseline and public paper index.')
            return 0
        previous = json.loads((root / BASELINE).read_text())
        changes = compare(previous, current)
        expected_index = render_index(current)
        if not (root / INDEX).exists() or (root / INDEX).read_text() != expected_index:
            changes['public_index_changed'] = [str(INDEX)]
        contract_drift = {key: value for key, value in changes.items()
                          if key not in {'lean_admission_changed', 'build_artifact_changed'}}
        print(json.dumps(dict(status='drift' if contract_drift else 'clean',
                              paper_statements=len(current['paper_statements']),
                              lean_declarations=len(current['lean_declarations']),
                              metrics={key: len(values) for key, values in changes.items()},
                              changes=changes), indent=2))
        return int(bool(contract_drift))
    except (OSError, ValueError, KeyError) as error:
        print(f'paper contract check: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
