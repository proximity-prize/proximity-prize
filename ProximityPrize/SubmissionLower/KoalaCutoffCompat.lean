import ProximityPrize.SubmissionLower.KoalaStableFlow

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace SplitCut.StableFlow
noncomputable section

open Polynomial HighCore82219Upper HighCore82219Upper_3 HighCore82219Upper_3_1
open K1_14 (L FX)
open P1 (K p)
open private HighCore82219Upper_3_3_1.mark_biform HighCore82219Upper_5_1.marked_coefficient
  HighCore82219Upper_2.jet HighCore82219Upper_2.jet_poly HighCore82219Upper_3.oldDenominator_eq
  from ProximityPrize.SubmissionLower.HighCore82219UpperGeometry

theorem open_nonmem {J : Input} {B : ResidueLift J} (P : Ideal JetRing) [P.IsPrime]
    (ho : openFactor J B ∉ P) (r : ℕ) :
    jetSeparant J.f ∉ P ∧ oldDenominator J B r ∉ P ∧ jetDenominator J B r ∉ P := by
  have hD : residueInJet B ∉ P := fun h => ho (P.mul_mem_right _ h)
  have hs : jetSeparant J.f ∉ P := fun h => ho (P.mul_mem_left _ h)
  have hp (n : ℕ) : residueInJet B * jetSeparant J.f ^ n ∉ P := fun h =>
    hs (‹P.IsPrime›.mem_of_pow_mem _ ((‹P.IsPrime›.mem_or_mem h).resolve_left hD))
  refine ⟨hs, ?_, ?_⟩
  · rw [HighCore82219Upper_3.oldDenominator_eq]; exact hp _
  · exact hp _

theorem relative_cutoff_mem {J : Input} {B : ResidueLift J} {D : Factors J B}
    {P : Ideal JetRing} [P.IsPrime] (hG : graphIdeal J B D ≤ P) (ho : openFactor J B ∉ P)
    {r : ℕ} {c : JetRing}
    (hrel : oldDenominator J B r * c - oldNumerator J B r * jetDenominator J B r ∈ graphIdeal J B D) :
    c ∈ P ↔ oldNumerator J B r ∈ P := by
  obtain ⟨_, hd, hu⟩ := open_nonmem P ho r
  let q := Ideal.Quotient.mk P
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr (hG hrel)
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
  constructor
  · intro hc
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hc, mul_zero] at h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (mul_eq_zero.mp h.symm).resolve_right (mt Ideal.Quotient.eq_zero_iff_mem.mp hu)
  · intro hn
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hn, zero_mul] at h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (mul_eq_zero.mp h).resolve_left (mt Ideal.Quotient.eq_zero_iff_mem.mp hd)

theorem relative_cutoff_stable {J : Input} {B : ResidueLift J} {D : Factors J B}
    {P : Ideal JetRing} [P.IsPrime] (hG : graphIdeal J B D ≤ P) (ho : openFactor J B ∉ P)
    {r : ℕ} (hr : 0 < r) (hp : r+1 < p) {c₁ c₂ : JetRing}
    (hrel₁ : oldDenominator J B r * c₁ - oldNumerator J B r * jetDenominator J B r ∈ graphIdeal J B D)
    (hrel₂ : oldDenominator J B (r+1) * c₂ - oldNumerator J B (r+1) * jetDenominator J B (r+1) ∈
      graphIdeal J B D)
    (hc₁ : c₁ ∈ P) (hc₂ : c₂ ∈ P)
    (hsimple : ∀ x ∈ P, ∃ t ∉ P, t*x ∈ graphIdeal J B D ⊔ Ideal.span {c₁}) :
    ∀ x ∈ P, action J.f x ∈ P := by
  obtain ⟨hs, hd, _⟩ := open_nonmem P ho r
  have h₁ := (relative_cutoff_mem hG ho hrel₁).mp hc₁
  have h₂ := (relative_cutoff_mem hG ho hrel₂).mp hc₂
  exact stable_of_step P hG hs r h₁ h₂ (simple_transfer P hd hrel₁ hsimple)
    (graph_derivative_step J B D hr hp)

end
end SplitCut.StableFlow

