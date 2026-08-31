# Lower-track submission note

## Claim and scope

This submission is a kernel-checked lower-track protocol claim.  The exported
object is `ProximityPrize.Benchmark.candidate`, with theorem type
`ProtocolClaim 6762 10288470 33554432`.  The accompanying score and radius
files use the same numerals: the score is 6762 centibits and the radius is the
exact rational `10288470/33554432`.  No floating-point approximation is used
by the claim.  The proof remains inside `ProximityPrize.SubmissionLower` and
imports the lower benchmark target plus the flat submission modules only.

The improvement is not a change to the statement, a verifier bypass, or an
extra axiom.  It is a refactoring of the certified counting ledger followed by
an exact re-evaluation of the resulting rational inequalities.  Every bridge
from the combinatorial certificates to the protocol claim is an ordinary Lean
term.  In particular, the final theorem is obtained through the same closure
interface used by the preceding lower submission, rather than by introducing a
parallel claim with weaker obligations.

## Structural proof organization

The proof has four logically separate layers.  The arithmetic layer gives
closed values for the finite coefficient counts, local ranks, nullities,
quotient thresholds, and the capacity ledger.  The cap layer turns those
values into statements about every admissible polynomial or residual support.
The selection layer transports the caps through the chosen pair and its
ambient lift.  The closure layer consumes the selected-pair statement and
produces the protocol-alignment and error guarantees required by
`ProtocolClaim`.

This separation is important for trust and resource use.  Large finite objects
are not reconstructed in the final theorem.  Instead, each closed numeral is
proved at the smallest module that owns its definition, and later modules use
the resulting named theorem.  The proof therefore exposes the intended
invariants—degree restrictions, weighted support bounds, nullity bounds, and
ledger inequalities—rather than relying on one monolithic evaluation.

The count/rank certificates use the characteristic-safe arithmetic already
provided by the benchmark.  The changed B-side certificate uses the reduced
quotient profile and its exact local rank; the A-side certificate uses the
strict quotient obtained from the first excluded Y level.  Both statements are
proved over naturals with explicit inequalities, so subtraction and cutoff
conventions are visible to the kernel.  The ambient and auxiliary certificates
are kept distinct from the selected pair: this prevents a bound proved for one
support shape from being silently reused at another shape.

## New certified margin

The submitted construction has 262144 total positions and 131071 agreement
positions.  Consequently the certified error count is 80378 and the positive
agreement gap used by the closure proof is 50695.  These values occur in the
profile definitions, the flag identities, the replacement-grid bounds, the
residual ledger, and the protocol theorem; they are not merely metadata in the
score file.

The A-side cap is tightened by proving that a hypothetical support at the first
excluded Y level has zero coefficient count in the corresponding quotient.
This yields a common Y cap of 74.  The same cap is propagated through the fixed
stage, its characteristic and identity gates, the consumer interface, and the
selected-support bridge.  The B-side total cap is certified by a separate
quotient calculation at its own reduced support.  Keeping these two quotient
arguments separate avoids conflating a Y cutoff with a total-degree cutoff.

The auxiliary replacement calculations use their own residual support
certificates.  Their thresholds and gap factor are recomputed from the new
agreement count.  The replacement grid then proves coverage and cost with the
same common Y cap used by the fixed stage.  Thus the grid obligation is not
silently weakened when the A-side cap changes: the validity predicate, cell
bounds, remaining-capacity estimate, and cell-cost theorem all share the new
bound.

At the scalar end of the ledger, the seedless contribution is certified by an
exact coefficient count, exact local rank, and exact nullity.  The list budget
is the closed value 2700000000.  The field-capacity budget is set below the
field capacity by exactly that list allocation, and the arithmetic layer proves
this split directly.  This makes the list contribution and the multiplicative
coefficient contribution disjoint accounting obligations instead of two uses
of an informal global slack variable.

## Identity and residual accounting

The fixed-stage identity calculation is an equality in `Nat`, not an
inequality asserted by automation.  Its three flag components are expanded
through the benchmark's `flagMixed` definition and the two tail supports.  The
updated slack polynomials are nonnegative sums of monomials.  The theorem
`identity_budget_exact` first establishes the exact decomposition; the
following budget theorem obtains the required inequality by the canonical
right-addition fact.  This keeps the direction of the natural-number
inequality explicit and avoids any dependence on integer subtraction.

The fixed regular contribution, fixed singular contribution, residual-stage
contribution, and residual singular contribution are separately closed.  Their
sum, with the protocol's unit overhead, is proved below the multiplicative
coefficient budget.  The residual proof carries its own slope bound into the
B-side profile and uses the ambient profile only where the selection theorem
requires it.  In particular, the residual argument does not replace a mixed
flag by a different flag or absorb an identity case into a proper case; the
case distinction and the associated ledger entries remain explicit.

All changed interfaces are propagated through the closure chain.  The
selected-pair record carries the updated A, auxiliary, C, and B profiles; the
universal bridge consumes the same records; and the final no-large-pencil
bound is stated at B=6762.  This alignment is checked by Lean at each module
boundary.  There is no stale lower-score theorem in the candidate path, and
neither the upper track nor an umbrella import is used.

## Exact analytic checks

The radius is represented by the unreduced-looking but exact fraction
`10288470/33554432`; Lean checks the required positivity and the strict upper
bound against `IRSProfile.minRelativeDistance`.  The error estimate uses the
same certified gap as the combinatorial ledger and proves
`certifiedGammaError ≤ 2^(-128)` by the benchmark's exact integer comparison.
No decimal rounding is used in either obligation.

For the score inequality, the proof uses the integer root associated with the
complement of the radius and splits the exponent for B=6762 into an integral
part and a two-decimal fractional part.  The two closed inequalities are:

* the hundredth-power comparison for the root and the factor of one billion;
* the 128th-power comparison for the complementary numerator, the power of
two, and the radius denominator.

They are discharged as numeral inequalities in Lean.  The resulting statement
is exactly `(1 - δ)^128 ≤ 2^(-6762/100)`, not a nearby decimal surrogate.  The
candidate theorem and the text files consequently cannot drift apart without
causing either elaboration or verifier failure.

## Kernel and build discipline

The only computational proofs are over closed numerals already introduced by
the arithmetic modules.  The large finite calculations are split into local
lemmas, which keeps reduction depth and memory use bounded compared with a
single aggregate decision procedure.  The submission contains no `sorry` or
`admit` in the candidate closure or in any lemma it uses.  Library warnings
about declarations outside this submission are not used as proof assumptions;
the changed modules themselves elaborate against the prebuilt library.

The final verification is performed with Lake on the lower submission entry
point, after the individual arithmetic modules have been compiled.  The
verification target is `Solution.lean`, so it checks the exact exported name,
its namespace, the lower-track imports, and the complete closure term.  The
numeric files are read independently as part of the submission check and
match the theorem numerals stated above.

## Research record

The mandated literature query was run with the paper-search CLI using the exact
challenge query `FRI IRS proximity kernel-check BCHKS resultant` and targeted
arXiv, Semantic Scholar, IACR, and Crossref sources.  The returned records did
not provide a source applicable to this benchmark's private Lean definitions
or its BCHKS-style resultant ledger.  No external statement was imported,
and no paper result is presented as evidence for the formal claim.  The proof
is supported by the benchmark target, the checked arithmetic lemmas, and the
kernel's type checking only.

## Reproducibility boundary

The meaningful reproducibility artifact is the chain of named Lean theorems
from the arithmetic certificates to `candidate`.  Each exact numeral has one
owner, each profile is consumed through its declared interface, and the final
claim is exported from a single flat `Solution.lean`.  The score and radius
files are intentionally minimal machine-readable mirrors of that theorem.
This note describes the mathematical invariants and the verification boundary
without reproducing the source diff or presenting a recipe for altering the
benchmark's certified construction.
