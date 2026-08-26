import ProximityPrize.SubmissionLower.BCHKSStableParameters6400

namespace ProximityPrize.SubmissionLower

open scoped BigOperators

set_option maxRecDepth 100000

/-!
Conditional combinatorial finish for the specialization-stable factor-cover
experiment.

`B q` must be read as the coordinates at which factor `q` has a *pure*
received-value slice: after specializing the coordinate, the received affine
value is its only `Y` root.  The weaker condition

`q(omega_i, U_i(Z), Z) = 0`

is not sufficient, since that slice may have additional roots.  The theorem
below proves that a pure/nonroot cover would finish the 64.00 lane, but it does
not assert that an interpolant's factors possess such a cover.
-/

/-- Removing fewer than `K=131072` pure coordinates from an agreement row of
size at least `185364` leaves at least `54293` chargeable incidences. -/
theorem bchksStable_sdiff_card_ge_gap6400
    {ι : Type*} [DecidableEq ι] (A B : Finset ι)
    (hA : 185364 ≤ A.card) (hB : B.card < 131072) :
    bchksStableChargeGap6400 ≤ (A \ B).card := by
  have hinter : (A ∩ B).card ≤ B.card := by
    apply Finset.card_le_card
    intro i hi
    exact (Finset.mem_inter.mp hi).2
  have hsplit := Finset.card_sdiff_add_card_inter A B
  norm_num [bchksStableChargeGap6400] at ⊢
  omega

/-- Summing a uniform upper bound over the owner fibres.  In the intended
application, a pure coordinate set of size at least `K` determines a single
affine polynomial line, so absence of alignment bounds each owner fibre by
`errors+1=76781`. -/
theorem bchksStable_pure_card_le6400
    {ζ γ : Type*} [DecidableEq ζ] [Fintype γ] [DecidableEq γ]
    (Pure : Finset ζ) (owner : ζ → γ)
    (hfactor : Fintype.card γ ≤ bchksStableFactorCount6400)
    (hfibre : ∀ q : γ,
      (Pure.filter fun z => owner z = q).card ≤
        bchksStableFiberCap6400) :
    Pure.card ≤
      bchksStableFactorCount6400 * bchksStableFiberCap6400 := by
  have hpartition :=
    Finset.sum_card_fiberwise_eq_card_filter Pure Finset.univ owner
  have hsum :
      (∑ q : γ, (Pure.filter fun z => owner z = q).card) = Pure.card := by
    simpa using hpartition
  calc
    Pure.card = ∑ q : γ, (Pure.filter fun z => owner z = q).card := hsum.symm
    _ ≤ ∑ _q : γ, bchksStableFiberCap6400 :=
      Finset.sum_le_sum fun q _ => hfibre q
    _ = Fintype.card γ * bchksStableFiberCap6400 := by simp
    _ ≤ bchksStableFactorCount6400 * bchksStableFiberCap6400 :=
      Nat.mul_le_mul_right bchksStableFiberCap6400 hfactor

/-- Exact conditional stable-cover theorem.

The hypotheses separate the missing algebraic statement from the proved
counting finish:

* `Pure` contains challenges assigned to a factor with at least `K` pure
  coordinate slices; nonalignment supplies the owner-fibre cap;
* every remaining owner has fewer than `K` pure slices;
* all agreements outside those slices are roots of nonzero coordinate
  polynomials, and `hrootMass` aggregates their `Z`-degrees.

Under precisely those assumptions, more than `13893745256` challenges force
an affine alignment. -/
theorem bchksStable_card_le_of_pure_nonroot_cover6400
    {ζ ι γ : Type*}
    [DecidableEq ζ] [DecidableEq ι] [Fintype γ] [DecidableEq γ]
    (S Pure : Finset ζ) (A : ζ → Finset ι) (B : γ → Finset ι)
    (owner : ζ → γ)
    (hPure : Pure ⊆ S)
    (hfactor : Fintype.card γ ≤ bchksStableFactorCount6400)
    (hfibre : ∀ q : γ,
      (Pure.filter fun z => owner z = q).card ≤
        bchksStableFiberCap6400)
    (hA : ∀ z ∈ S, 185364 ≤ (A z).card)
    (hsmall : ∀ z ∈ S \ Pure, (B (owner z)).card < 131072)
    (hrootMass :
      (∑ z ∈ S \ Pure, (A z \ B (owner z)).card) ≤
        262144 * bchksStableRootMass6400) :
    S.card ≤ bchksStableCoverCap6400 := by
  have hpureCap :
      Pure.card ≤
        bchksStableFactorCount6400 * bchksStableFiberCap6400 :=
    bchksStable_pure_card_le6400 Pure owner hfactor hfibre
  have hrow : ∀ z ∈ S \ Pure,
      bchksStableChargeGap6400 ≤ (A z \ B (owner z)).card := by
    intro z hz
    exact bchksStable_sdiff_card_ge_gap6400 (A z) (B (owner z))
      (hA z (Finset.mem_sdiff.mp hz).1) (hsmall z hz)
  have hchargeLower :
      (S \ Pure).card * bchksStableChargeGap6400 ≤
        ∑ z ∈ S \ Pure, (A z \ B (owner z)).card := by
    calc
      (S \ Pure).card * bchksStableChargeGap6400 =
          ∑ _z ∈ S \ Pure, bchksStableChargeGap6400 := by simp
      _ ≤ ∑ z ∈ S \ Pure, (A z \ B (owner z)).card :=
        Finset.sum_le_sum hrow
  have hcharged :
      (S \ Pure).card ≤ bchksStableChargedChallengeCap6400 := by
    norm_num [bchksStableChargeGap6400, bchksStableRootMass6400,
      bchksStableChargedChallengeCap6400] at hchargeLower hrootMass ⊢
    omega
  have hsplit := Finset.card_sdiff_add_card_eq_card hPure
  rw [bchksStableCoverCap_eq6400]
  omega

end ProximityPrize.SubmissionLower
