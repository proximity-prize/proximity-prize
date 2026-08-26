import ProximityPrize.SubmissionLower.BCHKSStableParameters6400
namespace ProximityPrize.SubmissionLower
open scoped BigOperators
set_option maxRecDepth 100000
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
