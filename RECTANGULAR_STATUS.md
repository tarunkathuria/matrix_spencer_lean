# Rectangular Matrix Spencer autoformalization

Latest addition, September 11: the actual dyadic owner potential now has an
exact, attained, polynomial-size real SDP representation. The explicit
affine LMI data, their objective, complete physical-to-coordinate
reconstruction, and the size bounds for the manuscript's tuned exponent
are formalized in [DyadicOwnerSDP.lean](MatrixSpencer/DyadicOwnerSDP.lean).
See [the SDP scope and formulas](RECTANGULAR_DYADIC_SDP_20260911.md).

The existing [finite analytic sampler](MS_RECTANGULAR_ANALYTIC_SAMPLER_PROOF.md)
proves returned-signing correctness and success probability. Polynomial
numerical tolerance, step-size, iteration-count, and total-runtime bounds
for the rectangular walk remain deferred. The new SDP theorem settles its
convex-program representation and size, without asserting those remaining
walk bounds.

The following verification details describe the preserved September 9
existence checkpoint. Its status is **VERIFIED**, exit code 0
(2026-09-09T11:33:25.756423+00:00).

The preceding square goal is complete. Its immutable verification record is
`.verification/square_complete_20260909/last_result.json` (`VERIFIED`,
2026-09-09 10:07:11 UTC). The preserved archive is
`../output/matrix_spencer_p2_lean_verified_20260909.zip`, SHA256
`1eceb21a97be5296fbb8de7c8d450c86f17af7d03294a1ab4d5ae0763601bbf0`.
It proves the original square theorem with universal constant 4,345,437.
The square source files and original verification program are preserved.

## Exact separate target

`MatrixSpencer/RectangularStatement.lean` specifies one universal constant
`C > 0`, chosen before `n`, `d`, and the matrices. For every `1 ≤ n ≤ d`,
every family of `n` complex Hermitian `d × d` Euclidean contractions has
a full real signing with

```
‖sum_i epsilon_i A_i‖_(2→2) ≤ C sqrt(n log(2d/n)).
```

`check_rectangular_proof.py` independently freezes this statement using
`Matrix.toEuclideanCLM`, checks the actual final theorem's type and axiom
closure, and requires the same kernel replay as the square verification.
It writes only under `.verification/rectangular/`. The final theorem
`MatrixSpencer.matrix_spencer_rectangular` now compiles with the explicit
universal constant **6,796,548**, defined before both sizes. All analytic,
preparation, finite-epoch and phase premises have been discharged. The independent
verification passed with mandatory `--kernel-replay imports`: 195 project
modules and 4948 local declarations were replayed. The exact statement,
standard-axiom closure and unchanged-source fingerprint also passed.

## Mathematical implementation

Choose a dyadic natural order `p = 2^m`, `m ≥ 1`, within a constant factor of
`max(2, log(2d/n))`, and set `q = 1/p`. Instead of postulating general matrix
power derivatives, iterate the already verified positive square root.
The actual regularizer is

```
R(S) = θ p/(p−1) Tr((root_m S)^(p−1)).
```

The root satisfies `(root_m S)^p = S`. Its actual derivative is the
composition of the proved Sylvester inverses. The inverse derivative is
the noncommutative derivative of the natural power. This proves the
actual gradient `θ(root_m S)^−1` and the full Hessian formula.

The exact polynomial inverse Hessian is bounded by the explicit model

```
U_S(B) = p/(2θ) (S B root_m S + root_m S B S).
```

Only this model is compressed. Its inverse is an artificial lower
curvature bound, not the actual compressed regularizer Hessian. Repeated
square-root compression proves the model compression inequality. The
faithful high/low estimate uses correlated weighted trace interpolation
between `S^0` and `sqrt(S)`, proved by repeated weighted Cauchy–Schwarz.

The exponent and strength remain fixed throughout all restrictions and
phases. A global response coefficient and epoch duration avoid changing
the regularizer when the live label count decreases.

## Completed local foundations

- Actual dyadic root, continuity, compression, smoothness, invertible
  derivative, and the exact natural-power inverse derivative.
- Actual regularizer gradient, Hessian, inverse Hessian bound, strict
  positive curvature, positive-cone strict concavity, and concavity at
  singular endpoints. The `m=1` function agrees with the original p=2
  regularizer.
- Actual density budget `θ D^q/(1−q)`, attained at the normalized identity;
  continuity and the exact pure-state value.
- Boundary gain proving every maximizing density positive definite,
  including arbitrary singular or zero Kraus sources.
- Actual unique maximizing density, compact attainment, the supremum
  potential, supporting planes, and the invertible stationary chart.
- Actual optimizer smoothness and derivative from the local inverse of
  the gradient chart.
- Actual optimized potential Hessian, supported inverse response transfer,
  and the complete original-coordinate coefficient estimate at every source
  rank: `Tr(CJ) ≤ 2√k + 6 L^q k^(1−q)/(θq)`.
- Actual joint covariance/center smoothness and covariance derivatives;
  supported shaving, compact paid preparation, and finite rank-decreasing
  spectral-dust preparation, including empty source support.
- Actual fixed-face uniform Taylor expansion, finite sampler drift, and
  a proved epoch drift mesh indexed only by the coefficient support.
- Positive model compression, exact balanced-coordinate representation,
  correlated trace interpolation, and all three physical transport
  budgets.
- General continuous-regularizer preparation and family deletion; actual
  dyadic initial potential bound and pointwise signing/norm extraction.
- Dyadic scalar parameter choice and globally fixed epoch-duration
  bookkeeping.

An ordinary axiom audit of 73 root/calculus declarations passed with only
`propext`, `Classical.choice`, and `Quot.sound`; its log is
`.verification/rectangular/dyadic_calculus_axioms.log`. Another 62 actual
optimizer/response declarations passed in `dyadic_response_axioms.log`.
New agent-owned
modules also have individual ordinary axiom reports under `build/`.
These reports are local milestones, not the final exact-statement and
full-closure kernel replay.

## September 9 existence verification

All required checks for the stated existence theorem passed at
2026-09-09T11:33:25.756423+00:00. No proof work remained for that checkpoint's
existence target; this record does not claim polynomial numerical runtime.
The immutable record is `.verification/rectangular_complete_20260909/`;
the archive is `../output/matrix_spencer_rectangular_lean_verified_20260909.zip`.
Its companion `.zip.sha256` file records the archive hash.
Replay uses the same Lean kernel against imported environments, not a fresh
replay of all mathlib or an independent kernel implementation.
