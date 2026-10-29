import ProximityPrize.SubmissionBinaryLower.P64C6Theta
import ProximityPrize.SubmissionBinaryLower.P64Cofactor
import ArkLib.Data.Polynomial.ResultantDegree

/-!
# Resultant orders from finite flow evaluation

The resultant is counted in the parameter variable over the fraction field of
the coefficient ring. This avoids specializing the spatial variable at a field
element, which would impose an unnecessary field-size bound.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Res

open Polynomial

section Scaling

variable {B : Type*} [CommRing B]

lemma coeff_eval_scaled (p : B[X]) (a : B) (k : ℕ) :
    PowerSeries.coeff k (p.eval₂ PowerSeries.C (PowerSeries.C a * PowerSeries.X)) =
      p.coeff k * a ^ k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial n c =>
      simp only [eval₂_monomial, mul_pow, ← map_pow,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, coeff_monomial]
      by_cases h : n = k
      · subst k; simp
      · simp [h, Ne.symm h]

lemma eval_shift_scaled (p : B[X]) (z a : B) :
    (taylor z p).eval₂ PowerSeries.C (PowerSeries.C a * PowerSeries.X) =
      p.eval₂ PowerSeries.C (PowerSeries.C z + PowerSeries.C a * PowerSeries.X) := by
  rw [taylor_apply, eval₂_comp]
  congr 1
  simp [add_comm]

variable [IsDomain B]

/-- A nonzero scaling preserves the order of vanishing at the centre. -/
theorem pow_sub_dvd_of_scaled (p : B[X]) (z a : B) (ha : a ≠ 0) (r : ℕ)
    (hv : (PowerSeries.X : PowerSeries B) ^ r ∣
      p.eval₂ PowerSeries.C (PowerSeries.C z + PowerSeries.C a * PowerSeries.X)) :
    (Polynomial.X - C z) ^ r ∣ p := by
  have ht : Polynomial.X ^ r ∣ taylor z p := by
    rw [Polynomial.X_pow_dvd_iff]
    intro k hk
    have hc := PowerSeries.X_pow_dvd_iff.mp hv k hk
    rw [← eval_shift_scaled, coeff_eval_scaled] at hc
    exact (mul_eq_zero.mp hc).resolve_right (pow_ne_zero _ ha)
  obtain ⟨q, hq⟩ := ht
  refine ⟨taylor (-z) q, ?_⟩
  have heq := congrArg (taylor (-z)) hq
  simpa [taylor_taylor, taylor_X, sub_eq_add_neg] using heq

end Scaling

section Resultant

variable {B : Type*} [CommRing B] [IsDomain B]

/-- Evaluating `Y` along a curve and `Z` at `z + a t`. -/
noncomputable def curveEval (y : PowerSeries B) (z a : B) :
    Polynomial (Polynomial B) →+* PowerSeries B :=
  P64C6Flow.Ev y (PowerSeries.C z + PowerSeries.C a * PowerSeries.X)

omit [IsDomain B] in
lemma curveEval_C (p : B[X]) (y : PowerSeries B) (z a : B) :
    curveEval y z a (C p) =
      p.eval₂ PowerSeries.C (PowerSeries.C z + PowerSeries.C a * PowerSeries.X) := by
  simp [curveEval, P64C6Flow.Ev, coe_eval₂RingHom]

/-- Bezout's identity transfers the common finite flow order to the resultant. -/
theorem pow_sub_dvd_resultant (R H : Polynomial (Polynomial B))
    (m n : ℕ) (hR : R.natDegree ≤ m) (hH : H.natDegree ≤ n) (hmn : m ≠ 0 ∨ n ≠ 0)
    (y : PowerSeries B) (z a : B) (ha : a ≠ 0) (r : ℕ)
    (hRv : (PowerSeries.X : PowerSeries B) ^ r ∣ curveEval y z a R)
    (hHv : (PowerSeries.X : PowerSeries B) ^ r ∣ curveEval y z a H) :
    (Polynomial.X - C z) ^ r ∣ Polynomial.resultant R H m n := by
  obtain ⟨p, q, _, _, hpq⟩ := exists_mul_add_mul_eq_C_resultant R H hR hH hmn
  apply pow_sub_dvd_of_scaled _ z a ha r
  rw [← curveEval_C _ y z a, ← hpq, map_add, map_mul, map_mul]
  exact dvd_add (dvd_mul_of_dvd_left hRv _) (dvd_mul_of_dvd_left hHv _)

variable [UniqueFactorizationMonoid B]

lemma resultant_ne_zero_of_irreducible (R H : Polynomial (Polynomial B))
    (hirr : Irreducible R) (hpos : 0 < R.natDegree) (hndvd : ¬ R ∣ H) :
    Polynomial.resultant R H R.natDegree H.natDegree ≠ 0 := by
  let A := Polynomial B
  let K := FractionRing A
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hprim : R.IsPrimitive := hirr.isPrimitive (by omega)
  have hirrK : Irreducible (R.map (algebraMap A K)) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
  have hnotK : ¬ R.map (algebraMap A K) ∣ H.map (algebraMap A K) :=
    fun h => hndvd (hprim.dvd_of_fraction_map_dvd_fraction_map h)
  have hcop : IsCoprime (R.map (algebraMap A K)) (H.map (algebraMap A K)) := by
    by_contra hn
    exact hnotK (hirrK.dvd_iff_not_isCoprime.mpr hn)
  have hne := Polynomial.resultant_ne_zero _ _ hcop
  intro hz
  have hm := Polynomial.resultant_map_map R H R.natDegree H.natDegree (algebraMap A K)
  rw [hz, map_zero] at hm
  apply hne
  rwa [Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.natDegree_map_eq_of_injective hinj]

/-- Sum all forced parameter orders without choosing a spatial base point. -/
theorem sum_orders_le {ι : Type*} (R H : Polynomial (Polynomial B))
    (hirr : Irreducible R) (hpos : 0 < R.natDegree) (hndvd : ¬ R ∣ H)
    (dR dH : ℕ) (hRdeg : ∀ j, (R.coeff j).natDegree ≤ dR)
    (hHdeg : ∀ j, (H.coeff j).natDegree ≤ dH)
    (zs : ι ↪ B) (S : Finset ι) (r : ι → ℕ) (y : ι → PowerSeries B) (a : ι → B)
    (ha : ∀ i ∈ S, a i ≠ 0)
    (hRv : ∀ i ∈ S, (PowerSeries.X : PowerSeries B) ^ r i ∣ curveEval (y i) (zs i) (a i) R)
    (hHv : ∀ i ∈ S, (PowerSeries.X : PowerSeries B) ^ r i ∣ curveEval (y i) (zs i) (a i) H) :
    ∑ i ∈ S, r i ≤ H.natDegree * dR + R.natDegree * dH := by
  classical
  let res := Polynomial.resultant R H R.natDegree H.natDegree
  have hres : res ≠ 0 := resultant_ne_zero_of_irreducible R H hirr hpos hndvd
  let K := FractionRing B
  let f : B →+* K := algebraMap B K
  have hf : Function.Injective f := IsFractionRing.injective B K
  let pts : ι ↪ K := zs.trans ⟨f, hf⟩
  have hne : res.map f ≠ 0 := (Polynomial.map_ne_zero_iff hf).mpr hres
  have horders : ∀ i ∈ S, r i ≤ (res.map f).rootMultiplicity (pts i) := by
    intro i hi
    rw [Polynomial.le_rootMultiplicity_iff hne]
    have hd := pow_sub_dvd_resultant R H R.natDegree H.natDegree le_rfl le_rfl
      (Or.inl (by omega)) (y i) (zs i) (a i) (ha i hi) (r i) (hRv i hi) (hHv i hi)
    simpa [res, pts] using Polynomial.map_dvd f hd
  calc ∑ i ∈ S, r i ≤ ∑ i ∈ S, (res.map f).rootMultiplicity (pts i) :=
        Finset.sum_le_sum horders
    _ ≤ (res.map f).natDegree := P64Cofactor.sum_rootMultiplicity_le_natDegree _ pts S
    _ = res.natDegree := Polynomial.natDegree_map_eq_of_injective hf res
    _ ≤ H.natDegree * dR + R.natDegree * dH :=
      Polynomial.natDegree_resultant_le_of_coeff_natDegree_le R H _ _ dR dH hRdeg hHdeg

end Resultant

end P64C6Res
end ProximityPrize.SubmissionBinaryLower
