import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import ProximityPrize.SubmissionLower.Koala6844NormalizationData



namespace ProximityPrize.SubmissionLower.Koala6844ActiveGerm

open Polynomial
open Koala6844Normalization

noncomputable section

set_option autoImplicit false

theorem normalized_injOn {K I : Type} [Field K] [DecidableEq K] [DecidableEq I]
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
    {w agreement errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ w agreement errors excess) :
    Set.InjOn data.normalized (↑data.seeds : Set K) := by
  classical
  intro g hg h hh hQ
  by_contra hne
  let B₀ := (data.A0 0).map σ.toRingHom
  let B₁ := (data.A0 1).map σ.toRingHom
  let T := B₁ * data.normalized g - data.D1
  let difference := σ g - σ h
  have hdiff : difference ≠ 0 :=
    sub_ne_zero.mpr (fun hs => hne (σ.injective hs))
  have heq (t : K) (ht : t ∈ data.seeds) (htQ : data.normalized t = data.normalized g) :
      B₀ * data.normalized g + C (σ t) * T =
        data.d1 * (data.selected t).map σ.toRingHom := by
    have h := data.equation1 t ht
    simp only [specializeAffine, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, htQ] at h
    simp only [B₀, B₁, T, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    linear_combination h
  have hgeq := heq g hg rfl
  have hheq := heq h hh hQ.symm
  let deltaP := (data.selected g).map σ.toRingHom - (data.selected h).map σ.toRingHom
  have hsub : C difference * T = data.d1 * deltaP := by
    dsimp only [difference, deltaP]
    rw [map_sub]
    linear_combination hgeq - hheq
  have hT : T = data.d1 * (C difference⁻¹ * deltaP) := by
    calc
      T = C difference⁻¹ * (C difference * T) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hdiff, map_one, one_mul]
      _ = data.d1 * (C difference⁻¹ * deltaP) := by rw [hsub]; ring
  have hbQ : data.d1 ∣ B₀ * data.normalized g := by
    refine ⟨(data.selected g).map σ.toRingHom - C (σ g) * (C difference⁻¹ * deltaP), ?_⟩
    rw [hT] at hgeq
    linear_combination hgeq
  have hbase : IsCoprime B₀ data.d1 := by
    simpa only [B₀, specializeAffine, map_zero, zero_mul, add_zero]
      using data.coprime_denominator1 0 data.zero_mem
  have hQdiv := hbase.symm.dvd_of_dvd_mul_left hbQ
  apply data.active
  convert dvd_sub (dvd_mul_of_dvd_right hQdiv B₁) (show data.d1 ∣ T from ⟨_, hT⟩) using 1
  ring

end

end ProximityPrize.SubmissionLower.Koala6844ActiveGerm

