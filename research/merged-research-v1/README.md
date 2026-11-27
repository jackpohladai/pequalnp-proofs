# Consolidated P vs NP research — 27 November 2026

This package preserves the existing research, solver, proof components, tests,
and failed attempts. **It is not a proof of P = NP, and it has no proved
polynomial worst-case running-time bound for general SAT.**

The merged implementation includes the existing compression and refutation
components, a per-call counting cache, and an optional explicit order for
compressed variables. Research workers are paused. Nothing here launches them.

## What was checked locally

- 52 Lean modules from 23 component families compiled and imported together
  with Lean 4.36.0. The precise statements and assumptions are in `lean/src/`.
- 410 solver regression cases and 326 compression controls passed.
- 14 larger controls were exercised; the original independent oracle was
  inconclusive on two, so these are not all independently confirmed answers.
- Integration checks preserved the tested answers, reduced one fixture's
  counting calls from 12 to 8, and reduced another fixture's peak retained
  states from 8 to 2 using a supplied order. These are specific examples,
  not universal performance bounds.

See `merge-manifest.json`, `lean/build-receipt.json`, and `tests/*receipt.json`.
The Python implementation itself is **not formally verified**. A compiled
component theorem does not imply a complete checked fast general SAT solver.

## Run the merged solver

From this directory, with Python 3.9 or later:

```sh
python3 -m venv .venv
.venv/bin/pip install -r requirements.txt
.venv/bin/python research.py status
.venv/bin/python research.py solve input.json
.venv/bin/python tests/test_merge.py
```

`input.json` is a list of CNF clauses, such as `[[1,2],[-1],[2]]`, or an object
with `formula` and `order`. Positive integers denote variables and negative
integers their negations. `--quotient-order 1,2,...` supplies the complete order
for compressed variables; `--no-counting-cache` disables the per-call cache.

## Rebuild the Lean components

Use the repository's pinned Lean 4.36.0 environment and Mathlib revision
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, with the repository's
`PEqualNP.Defs.Search` dependency built. The original checker project commit
was `440d4d6`; the historical receipt records its environment. From this folder:

```sh
PNP_LEAN_PROJECT=/absolute/path/to/pequalnp-proofs/lean python3 build_lean.py
```

The project defaults to this repository's `lean/` folder. Compiled binaries
are excluded; rebuild the sources. `lean/source-manifest.json` records exact
source hashes and the limited namespace/evaluation-example adjustments used
to import the existing modules together. `lean/originals/` preserves originals.

## Evidence and research archive

- `runtime/`: merged implementation and its dependencies.
- `lean/src/`: checked component sources, plus their joint import.
- `evidence/`: 385 folders of proposals, test results and review records.
- `experimental/`: existing drafts; not promoted to checked algorithms.
- `research-snapshot.zip`: the broader existing research snapshot. Many files
  are failed approaches or unverified model outputs. Read their verdicts.
- `archive-index.json`: hashes of the published archive entries.
- `publication-manifest.json`: publication inventory and privacy changes.

Private account-wide usage exports remain local. Contact details are redacted
in the public copy. Historical logs contain original machine paths and earlier
statuses; they do not describe a currently running service. Historical source
hashes refer to their original bytes; the publication manifest separately
records any changed public bytes. No new experiments or model calls were run
to prepare this archive.

## GitHub publication and project points

This branch archives research in `jackpohladai/pequalnp-proofs`. It is not a
bulk submission to the upstream project's proof checker. Publishing it earns
**zero automatic pequalnp points**. Only accepted proofs of the project's
assigned statements qualify; accepted reductions wait for their child proofs.
See the [project submission rules](https://pequalnp.com/join.txt).
