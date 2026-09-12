# Matrix Spencer: matrix count at most dimension

This directory is one complete standalone Lean repository. Upload its **contents** as one Git repository; `lakefile.toml` belongs at that repository's root.

## Statement and conventions

For Matrix Spencer, **n is the number of matrices and m is their matrix dimension**. For Kadison-Singer, **n is the number of atoms and d is their matrix dimension**. This repository's regime: **1 <= n <= m**. The original Lean statements generally call these sizes `n,d` or `N,D`; the quantifiers, not variable letters, determine their roles.

For every 1 <= n <= m and every n complex Hermitian m-by-m contractions, there are signs s_i in {-1,+1} such that ||sum_i s_i A_i||_(2->2) <= C sqrt(n log(2m/n)), where C is one universal constant chosen before both sizes and the matrices. The logarithm is natural.

The explicit constant is **6,796,548**. Every norm in the target is the Euclidean operator norm, explicitly connected to `Matrix.toEuclideanCLM`.

- Final theorem: `MatrixSpencer.matrix_spencer_rectangular`.
- Main proof: [MatrixSpencer/RectangularMain.lean](MatrixSpencer/RectangularMain.lean).
- Target definition: [MatrixSpencer/RectangularStatement.lean](MatrixSpencer/RectangularStatement.lean).
- `MatrixSpencer.lean` imports this repository's selected main theorem.

## Compile and verify

Install Lean's [elan toolchain manager](https://github.com/leanprover/elan) and have `lake` on PATH. Python 3 is needed for the full verifier. The checked-in `lean-toolchain` selects **Lean 4.24.0**. The checked-in `lake-manifest.json` pins mathlib to **f897ebcf72cd16f89ab4577d0c826cd14afaafc7**, plus its exact dependency revisions.

From this repository root, on a fresh machine with network access:

```sh
# Fetch the pinned library dependencies and their precompiled cache.
./run_lake.sh exe cache get

# Compile this repository's selected proof and all local dependencies.
./run_lake.sh build

# Check the final mathematical statement, allowed axioms, and kernel replay.
./verify.sh
```

If executable permissions were lost during upload, use `chmod +x run_lake.sh verify.sh` once. A normal Git clone preserves these permissions.

`verify.sh` must finish with **VERIFIED** and exit code **0**. It invokes the original checker with an explicit route/module selection. It checks the actual final declaration against a separately written primitive statement, screens local admissions, audits transitive axioms, and replays the project import closure through Lean's kernel. Expected transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

For a direct kernel-replay command:

```sh
./run_lake.sh env lean --run tools/Replay.lean MatrixSpencer.RectangularMain
```

Replay uses the same installed Lean kernel against imported environments. It does not use an independent kernel implementation or recheck all of mathlib from primitive declarations. Full logs and the most recent local receipt are written under `.verification/`; do not substitute compilation of a proposition definition for this verification.

## What is formalized

The dyadic Tsallis finite walk/epoch existence proof is formalized. Neither this Lean development nor the current rectangular manuscript claims a polynomial runtime bound.

## What must be included in this repository

Keep **every file in this directory's source distribution**, including all of `MatrixSpencer/`, `MatrixSpencer.lean`, `tools/`, the Python checker(s), both shell scripts, the toolchain/configuration/lock files, and this README. There are **194 original Lean proof modules**, constituting the complete transitive local import closure of `MatrixSpencer.RectangularMain`. No sibling proof repository or original workspace is required.

Some foundational Lean modules are shared between the four proof routes. They are intentionally duplicated here. A filename referring to another route can occur through a shared import; it must not be deleted on that basis. This repository does not import another route's final main theorem. The module namespace remains `MatrixSpencer` in the Kadison-Singer repositories because the foundations were developed under that namespace.

The KS checker imports Python helper functions from `check_rectangular_proof.py`; when that helper is present it is verification support, not a requirement to include the rectangular MS theorem.

Do not commit `.lake/`, `.cache/`, `.verification/`, `__pycache__/`, the parent research workspace, or installed toolchains. Those are ignored caches or local verification output. mathlib is restored from the pinned dependency manifest; it is not vendored.

## Provenance

`SOURCE_MANIFEST.json` lists every original proof dependency and copied-file SHA-256. All original proof files were checked byte-for-byte against the successful original verification receipt dated 2026-09-09T11:33:25.756423+00:00. The original research files were not changed. Only the repository entry wrapper, portable launcher, verification convenience script, documentation, and packaging metadata are new.

The standalone packaging check, once completed, is recorded in `VERIFICATION.json`. Original receipts and standalone packaging verification have separate scopes.
