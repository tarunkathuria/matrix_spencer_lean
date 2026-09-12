# Rectangular Matrix Spencer: exact dyadic SDP representation

The dyadic owner potential used by the rectangular Matrix Spencer proof has an exact, attained, polynomial-size real SDP representation. The construction is connected to the existing `dyadicOwnerPotential` definition; it does not replace the potential by a relaxation or assume an optimizer identity.

This addition formalizes the convex-program representation and its size. Polynomial bounds for the rectangular walk's numerical tolerances, step sizes, iteration counts, and total numerical runtime remain deferred.

For a physical matrix dimension \(d>0\), let \(H,A_i\in\mathbb C^{d\times d}\), with each \(A_i\) Hermitian, and let \(C\succeq0\) be a real covariance matrix. Set

\[
\Omega_{A,C}(S)=\sum_{i,j}C_{ij}A_iSA_j,
\qquad p=2^m,\quad m\ge1,\quad \theta>0.
\]

The formalized owner potential is

\[
\max_{S\succeq0,\ \operatorname{Tr}S=1}
\left\{
\operatorname{Re}\operatorname{Tr}(HS)
+2F(S,\Omega_{A,C}(S))
+\frac{\theta p}{p-1}\operatorname{Tr}S^{1-1/p}
\right\},
\]

where \(F(S,M)=\operatorname{Tr}\sqrt{\sqrt S M\sqrt S}\). Lean expresses the power as `dyadicRoot m S ^ (2^m - 1)`, using its previously verified iterated positive square-root definition. The final representation theorem is in [DyadicOwnerSDP.lean](MatrixSpencer/DyadicOwnerSDP.lean).

The SDP uses a trace-one Hermitian variable \(S\), Hermitian variables \(X_1,\ldots,X_m\), and an unrestricted complex matrix \(Z\). With \(X_0=I\), its constraints are

\[
X_j\succeq0,\qquad
\begin{pmatrix}S&X_j\\X_j&X_{j-1}\end{pmatrix}\succeq0
\quad(1\le j\le m),
\qquad
\begin{pmatrix}S&Z\\Z^*&\Omega_{A,C}(S)\end{pmatrix}\succeq0.
\]

It maximizes the affine objective

\[
\operatorname{Re}\operatorname{Tr}(HS)
+2\operatorname{Re}\operatorname{Tr}Z
+\frac{\theta p}{p-1}\operatorname{Tr}X_m.
\]

The fidelity block already implies \(S\succeq0\), so an additional density-positivity LMI is unnecessary. The explicit coordinates impose the trace equation identically, using the maximally mixed matrix \(I/d\) as the density chart's center.

The trace-power proof bounds every feasible `Chain` by

\[
\operatorname{Tr}X_m\le\operatorname{Tr}S^{1-2^{-m}}.
\]

Its proof compresses the positive blocks to scalar inequalities in an eigenbasis of \(S\). Equality is feasible with \(X_j=S^{1-2^{-j}}\), including singular \(S\). The existing fidelity-block theorem gives the corresponding upper bound on \(\operatorname{Re}\operatorname{Tr}Z\). The already proved faithful dyadic density optimizer supplies an attaining fidelity witness and hence an actual maximizer of the complete SDP. No positive definiteness or nonzero-rank hypothesis is imposed on the covariance or source; zero covariance and an empty source family are included.

The finite real SDP data are explicit. Each \(X_j\) has \(d^2\) real Hermitian coordinates; \(Z\) has \(2d^2\) real coordinates, and the trace-one density has \(d^2-1\). The positivity constraints are padded to the same block size before realification. Every resulting matrix inequality is a real symmetric affine pencil, with its constant matrix and every coefficient matrix defined in Lean. The objective is proved equal to its constant plus the inner product of its explicit coefficient vector with the coordinate vector. The coordinate map covers every feasible physical triple, so the coordinate SDP and physical SDP have exactly the same feasible objective values.

| Quantity | Exact size |
|---|---:|
| Real variables | \((m+3)d^2-1\) |
| Real affine matrix inequalities | \(2m+1\) |
| Order of each real LMI | \(4d\) |
| Dense LMI coefficient entries, including constant matrices | \(16(2m+1)(m+3)d^4\) |

The objective contributes one coefficient per variable and one constant. The affine matrices use the original covariance formula \(\sum_{i,j}C_{ij}A_iSA_j\) directly. Matrix roots, eigenvectors, and the covariance Kraus factorization occur in the representation proof, rather than in the definitions of the affine SDP coefficients.

For the actual rectangular parameters with \(N\ge1\) input matrices of dimension \(D\ge1\), the signed lift has physical dimension \(d=2D\). The formalized depth is `RectangularTunedParameters.depth N D`. A deliberately coarse proved bound \(m\le2+2D\) gives fixed-degree polynomial size bounds:

\[
\begin{aligned}
\text{variables}&\le4(2D+5)D^2,\\
\text{LMIs}&\le4D+5,\\
\text{real LMI order}&=8D,\\
\text{dense LMI coefficients}&\le256(4D+5)(2D+5)D^4.
\end{aligned}
\]

These estimates concern the size of the actual encoded SDP, including the rectangular proof's chosen depth. They do not depend on a polynomial degree that grows with \(p\).

| Source | Formalized connection |
|---|---|
| [DyadicSDPTracePower.lean](MatrixSpencer/DyadicSDPTracePower.lean) | `chain_trace_le` and `canonical_chain`: upper bound and attaining dyadic chain, including singular densities. |
| [DyadicOwnerSDPIdentity.lean](MatrixSpencer/DyadicOwnerSDPIdentity.lean) | `owner_SDP_exact` and `owner_sSup_eq`: exact attained physical SDP maximum equals the existing owner potential. |
| [DyadicSDPCoordinates.lean](MatrixSpencer/DyadicSDPCoordinates.lean) | Explicit real coordinates, reconstruction identities, and exact coordinate dimension. |
| [DyadicSDPAffineObjective.lean](MatrixSpencer/DyadicSDPAffineObjective.lean) | `value_eq_affine`, `feasible_onto`, and `values_eq`: actual affine objective and complete coordinate coverage. |
| [DyadicSDPAffineData.lean](MatrixSpencer/DyadicSDPAffineData.lean) | Actual real symmetric affine LMI data, convexity, and `target_iff` identifying their feasible set with the physical constraints. |
| [DyadicSDPProgramSize.lean](MatrixSpencer/DyadicSDPProgramSize.lean) | Exact size formulas and fixed-degree polynomial bounds for the tuned rectangular depth. |
| [DyadicOwnerSDP.lean](MatrixSpencer/DyadicOwnerSDP.lean) | `exists_maximizer` on the actual affine LMI data, with the maximally mixed center; `actual_size_bounds`, `rectangular_size_bounds`, and `rectangular_exists_maximizer` for the manuscript's tuned depth and weight. |

The existing rectangular discrepancy and analytic-walk proofs remain in place. This addition establishes the polynomial-size convex formulation needed for a future numerical implementation under the permitted real-RAM convex-solver model. It does not yet prove polynomial total runtime for that rectangular numerical walk.
