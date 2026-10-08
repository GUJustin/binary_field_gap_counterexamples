#!/usr/bin/env python3
"""Check the explicit admission boundary using Lean's transitive axiom reports.

Run after `lake build`. The public inventory must cover every current project
mathematical declaration. A theorem may depend on sorryAx only while its own
MainTheorems proof explicitly contains sorry. Definitions never may.
"""
from pathlib import Path
import re
import subprocess
import sys

from paper_contracts import lean_declarations

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def parse_reports(output):
    reports = {}
    for match in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S):
        reports[match[1]] = {x.strip() for x in match[2].split(',') if x.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        reports[name] = set()
    return reports


def unexpected_axioms(declaration, axioms):
    admitted_target = (declaration['kind'] in {'theorem', 'lemma'} and
                       '/MainTheorems/' in declaration['source'] and
                       declaration['admission'] == 'sorry')
    allowed = STANDARD | ({'sorryAx'} if admitted_target else set())
    return axioms - allowed


def main():
    declarations = {}
    paths = sorted((ROOT / 'formalization/BinaryFieldCounterexamples').rglob('*.lean'))
    paths.append(ROOT / 'formalization/BinaryFieldCounterexamples.lean')
    for path in paths:
        for value in lean_declarations(path.read_text(), path.relative_to(ROOT).as_posix()).values():
            name = value['qualified_name']
            if name in declarations:
                raise ValueError(f'Duplicate public inventory name: {name}')
            declarations[name] = value
    reports = {}
    for path in ['Checks/Axioms.lean', 'Checks/StatementTypes.lean']:
        result = subprocess.run(['lake', 'env', 'lean', path], cwd=ROOT / 'formalization',
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if result.returncode:
            print(result.stdout)
            return result.returncode
        reports.update(parse_reports(result.stdout))
    if reports.keys() != declarations.keys():
        print('Axiom inventory mismatch. Update the explicit public-import checks:')
        print('Missing:', sorted(declarations.keys() - reports.keys()))
        print('Unexpected:', sorted(reports.keys() - declarations.keys()))
        return 1
    errors = []
    for name, declaration in declarations.items():
        unexpected = unexpected_axioms(declaration, reports[name])
        if unexpected:
            errors.append(f'{name}: unexpected axioms {sorted(unexpected)}')
    if errors:
        print('\n'.join(errors))
        return 1
    admitted = sum('sorryAx' in value for value in reports.values())
    print(f'Checked {len(reports)} declarations: {admitted} explicitly admitted targets; '
          f'{len(reports) - admitted} admission-free declarations. No unexpected axioms.')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError) as error:
        print(f'Lean contract axiom check: {error}', file=sys.stderr)
        sys.exit(2)
