import ProximityPrize.SubmissionLower.KoalaPointCount
import ProximityPrize.SubmissionLower.HighCore82229Regular

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace SplitCut.Incidence
noncomputable section
open P1 (K I node)
open P1_7_3 (persistentNodes)
open HighCore82229Upper (Input)
open HighCore82229 (FixedWord agreement blockLength degreeAt scale muNum)
open HighCore82229_5 (nodeVelocity)
open scoped BigOperators

/-- The old occupancy lemma with a single ordinary affine degree on the curve.
    The two coefficients are exactly the old constant and shortening incidence weights. -/
theorem curve (J : Input) {T : Finset K}
    (hword : FixedWord J.model.word T J.family.scalar (degreeAt J.hi))
    (hd : degreeAt J.hi < agreement) {k δ : ℕ} (hk : 0<k) (hδ : 0<δ)
    (hc : ∀ x : I, (∃ γ ∈ T, (J.family.scalar γ).eval (node x) ≠ J.model.word x) →
      (T.filter (fun γ => (J.family.scalar γ).eval (node x) = J.model.word x)).card ≤
        (2*(J.ell-(persistentNodes J.model.word T J.family.scalar).card)+k)*δ) :
    scale J.hi*T.card ≤ (2*nodeVelocity J+muNum J.hi*k)*δ := by
  let s := (persistentNodes J.model.word T J.family.scalar).card
  by_cases hT : T.card ≤ 1
  · have hAn : agreement ≤ blockLength := by decide
    have hscale : scale J.hi ≤ muNum J.hi :=
      Nat.mul_le_mul_left agreement (Nat.sub_le_sub_right hAn _)
    calc
      scale J.hi*T.card ≤ scale J.hi := by simpa using Nat.mul_le_mul_left (scale J.hi) hT
      _ ≤ muNum J.hi := hscale
      _ ≤ muNum J.hi*k := Nat.le_mul_of_pos_right _ hk
      _ ≤ (2*nodeVelocity J+muNum J.hi*k)*δ :=
        (Nat.le_add_left _ _).trans (Nat.le_mul_of_pos_right _ hδ)
  have hs : s ≤ degreeAt J.hi := HighCore82229.persistent_card_le hword (by omega)
  have hp : 0 < agreement-s := Nat.sub_pos_of_lt (hs.trans_lt hd)
  obtain ⟨hm,hl⟩ := HighCore82229_5.incidence_weights J hd s hs
  have H := HighCore82229.section_incidence hword ((2*(J.ell-s)+k)*δ) hc
  change (agreement-s)*T.card ≤ (blockLength-s)*((2*(J.ell-s)+k)*δ) at H
  refine Nat.le_of_mul_le_mul_left ?_ hp
  calc
    (agreement-s)*(scale J.hi*T.card) = scale J.hi*((agreement-s)*T.card) := by ring
    _ ≤ scale J.hi*((blockLength-s)*((2*(J.ell-s)+k)*δ)) := Nat.mul_le_mul_left _ H
    _ = (2*(scale J.hi*(blockLength-s)*(J.ell-s)) + (scale J.hi*(blockLength-s))*k)*δ := by ring
    _ ≤ (2*((agreement-s)*nodeVelocity J) + ((agreement-s)*muNum J.hi)*k)*δ :=
      Nat.mul_le_mul_right _ (Nat.add_le_add (Nat.mul_le_mul_left _ hl) (Nat.mul_le_mul_right _ hm))
    _ = (agreement-s)*((2*nodeVelocity J+muNum J.hi*k)*δ) := by ring

open MvPolynomial
variable {F σ α : Type*} [Field F] [Finite σ]
theorem weighted_cover (I : Ideal (MvPolynomial σ F)) (T : Finset α) (x : α → σ → F)
    (hT : ∀ i ∈ T, x i ∈ zeroLocus F I) (u v : ℚ) (hu : 0≤u)
    [DecidableRel (fun (i : α) (Q : Ideal (MvPolynomial σ F)) => x i ∈ zeroLocus F Q)]
    (hcomp : ∀ Q ∈ I.minimalPrimesFinset,
      u*((T.filter (fun i => x i ∈ zeroLocus F Q)).card:ℚ) ≤ v*affineDegree Q) :
    u*(T.card:ℚ) ≤ v*∑ Q ∈ I.minimalPrimesFinset, affineDegree Q := by
  classical
  have H := PointCount.cover I T hT
  have HQ : (T.card:ℚ) ≤ ∑ Q ∈ I.minimalPrimesFinset,
      ((T.filter (fun i => x i ∈ zeroLocus F Q)).card:ℚ) := by exact_mod_cast H
  calc
    _ ≤ u*(∑ Q ∈ I.minimalPrimesFinset, ((T.filter (fun i => x i ∈ zeroLocus F Q)).card:ℚ)) :=
      mul_le_mul_of_nonneg_left HQ hu
    _ ≤ _ := by simpa only [Finset.mul_sum] using Finset.sum_le_sum hcomp

end
end SplitCut.Incidence
#print axioms SplitCut.Incidence.curve
#print axioms SplitCut.Incidence.weighted_cover
