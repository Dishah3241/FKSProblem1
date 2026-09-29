# Comparator run, 2026-09-29

Comparator accepted `FKSProblem1.Palomar.target` under both NanoDa and Lean's default kernel.
The target is `Problem1Bounded`: for every `d ≥ 4`, every finite simple graph on at most
`2d` vertices, of maximum degree at most `d`, with no complete component of order `d + 1`,
has an injective placement on the radius-`1/√2` sphere in Euclidean ℝᵈ with every edge at
unit distance. The unrestricted question and its unrestricted `d = 4` instance remain open.

- **Tree:** worktree based on `f758d31ce6514ec7799776a6449a0f06ed52768a`.
  README and metadata edits were uncommitted during Comparator; all Lean sources,
  `comparator.json`, toolchain and dependency pins matched that commit. This record
  was added afterwards. No commit was made; the caller commits and lands the release.
- **Library:** GraphDimension at `db8062bb838b4ac31ea4d5648ea2a8b51685cfa0`, matching
  both `lake-manifest.json` and the local dependency's `HEAD`.
- **Toolchain:** Lean `v4.35.0-rc2`; Mathlib at
  `065356127b1dc0016f66b7283ce0ce2c4055aa55` (`v4.35.0-rc2`).
- **Configuration:** `comparator.json`, target `FKSProblem1.Palomar.target`, permitted
  axioms `propext`, `Quot.sound`, `Classical.choice`, and `enable_nanoda: true`.
- **Sandbox:** disabled. Comparator uses Linux `bwrap`, unavailable on this macOS host.
  As in rung 3 and P9, this checks the mathematics, not isolation. Sandboxed Palomar
  preflight on the final release commit remains the manager's responsibility.

## Command and result

From the project directory, after `scripts/worktree-setup.sh`:

```sh
PATH="$HOME/src/nanoda_lib/target/release:$HOME/.elan/bin:$PATH" \
  ~/.elan/bin/lake comparator --config comparator.json --inadvisably-no-sandbox
```

Exit status: `0`. Build and final kernel messages:

```text
WARNING: Sandbox disabled, this run is not trustworthy.
Resolving dependencies
Building Challenge
⚠ [2440/2441] Replayed Challenge
warning: Challenge.lean:266:8: declaration uses `sorry`
Build completed successfully (2441 jobs).
Building Solution
Build completed successfully (3400 jobs).
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

The export lines omitted above both name `FKSProblem1.Palomar.target`.
The challenge warning is its deliberate advertised proof hole; the solution has none.

## Target axiom check

A temporary file importing `Solution` printed both target declarations' axioms:

```sh
~/.elan/bin/lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false tmp/ReleaseAxioms.lean
```

Exit status: `0`.

```text
'FKSProblem1.Palomar.target' depends on axioms: [propext, Classical.choice, Quot.sound]
'FKSProblem1.StatementA.Problem1Bounded.proof' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Local gates

The build and audit suite were started from the clean committed baseline above, before
release edits. The probes archive committed `HEAD`; they therefore verify the baseline,
not the uncommitted documentation. The manager must rerun the release checks on the final
clean committed tree. All commands below exited `0`; their last output lines are recorded.

```text
~/.elan/bin/lake build
Build completed successfully (3436 jobs).

~/.elan/bin/lake exe axioms
axioms: audited 307 FKSProblem1 declarations; every declaration reduces to [propext, Classical.choice, Quot.sound].

~/.elan/bin/lake exe fidelity
fidelity: 32 obligation(s) discharged; every claim has a satisfiability witness, every non-dependent hypothesis a drop companion, and every definition a separating example.

~/.elan/bin/lake exe module-system
module-system: all 18 project modules use the module system.

~/.elan/bin/lake exe layering
layering: 10 project import(s) across 8 modules respect mathematical ownership; examples, standalone modules, and tests are leaves.

~/.elan/bin/lake exe proof-links
proof-links: verified 46 automatically discovered isolated claims (40 linked, 6 open).

~/.elan/bin/lake exe standalone-mathlib
standalone-mathlib: 3 module(s) rest on Mathlib alone (12019 modules in their import closures).

~/.elan/bin/lake exe style
style: 18 source file(s) within 100 characters, no trailing whitespace, final newline present.

~/.elan/bin/lake exe documentation
documentation: 7 mathematical source file(s) contain no unstable labels or development-status phrases; 7 project source file(s) use the required terminology.

~/.elan/bin/lake exe palomar-compatibility
palomar-compatibility: checked 5 declarations; the statement closure is portable between the Challenge and Solution modules.

scripts/check-palomar-challenge.sh
Challenge.lean matches the statement source (without its proof-link note) and footer.

scripts/lint-env.sh
LINT-ENV: PASS — no new violations (0 grandfathered, 0 ratchetable).

scripts/audit-probes.sh
audit-probes: 16 passed, 0 failed
```

The build replayed the same deliberate `Challenge.lean` warning as Comparator.

## Local blueprint check

The initial `leanblueprint checkdecls` call failed because `blueprint/lean_decls` was absent.
As in P9's local record, the generated declaration list was extracted from current LaTeX
without comments. There are 43 references to 42 distinct names, all checked:

```sh
python3 - <<'PYTHON'
from pathlib import Path
import re
source = Path('blueprint/src/content.tex').read_text()
source = '\n'.join(line.split('%', 1)[0] for line in source.splitlines())
names = [name.strip()
         for group in re.findall(r'\\lean\{([^}]*)\}', source, re.S)
         for name in group.split(',')]
assert len(names) == 43
assert all(re.fullmatch(r'[A-Za-z0-9_.]+', name) for name in names)
names = list(dict.fromkeys(names))
assert len(names) == 42
Path('blueprint/lean_decls').write_text('\n'.join(names) + '\n')
PYTHON
PATH="$HOME/.elan/bin:$PATH" leanblueprint checkdecls
```

The check exited `0` with no missing declarations and no output. The generated list and
scratch Lean file were removed afterwards. This is a declaration-reference check, not a
PDF or web-rendering check; CI runs `leanblueprint all` before `checkdecls`.

## Metadata validation and provenance

```sh
uvx check-jsonschema --schemafile https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/v0.4.schema.json formalization.yaml
```

Exit status: `0`; last line: `ok -- validation done`.
The initial sandboxed attempt could not access uv's cache; the successful invocation used
approved cache and network access. All 18 template placeholders were removed.

Worker model strings in `formalization.yaml` were read using `harness/run-model <run-id>`
from the Math workspace, including the GraphDimension leaves and the bridge run missing
from the wave-log ID column. The release run `20260929-130556-008a0f06` reports
`gpt-6.1-sol`. The managing session's first assistant event reports `claude-opus-5-5`.
The parallel novelty and read-only grok release review dispositions remain pending for
the manager; this release makes no priority or independent-lineage review claim.
