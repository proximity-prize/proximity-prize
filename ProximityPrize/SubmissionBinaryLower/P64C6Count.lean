import ProximityPrize.SubmissionBinaryLower.P64C6Degree

/-!
# From coefficient orders to the resultant count

This is the counting part of the finite flow argument. The local flatness
lemmas supply the orders used here. The bounds concern the original
trivariate representation and do not require a spatial specialization.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Count

open Polynomial P64C6Coordinates P64C6Degree BCHKSSubstitutionVanish

variable {F : Type*} [Field F]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree

lemma reorder_natDegree (R : Tri) : (reorder R).natDegree = R.natDegree :=
  Polynomial.natDegree_map_eq_of_injective Polynomial.Bivariate.swap.injective R

lemma reorder_ne_zero {R : Tri} (hR : R ≠ 0) : reorder R ≠ 0 :=
  (Polynomial.map_ne_zero_iff Polynomial.Bivariate.swap.injective).mpr hR

lemma reorder_irreducible {R : Tri} (hR : Irreducible R) : Irreducible (reorder R) :=
  (MulEquiv.irreducible_iff
    (f := (Polynomial.mapEquiv Polynomial.Bivariate.swap.toRingEquiv).toMulEquiv)).mpr hR

lemma reorder_coeff_degree (R : Tri) (d : ℕ)
    (hR : ∀ j a, ((R.coeff j).coeff a).natDegree ≤ d) (j : ℕ) :
    ((reorder R).coeff j).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro b hb
  ext a
  simp only [reorder, Polynomial.coe_mapRingHom, coeff_map, coeff_zero]
  change ((Polynomial.Bivariate.swap (R.coeff j)).coeff b).coeff a = 0
  rw [coeff_swap]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt ((hR j a).trans_lt hb)

/-- Local multiplicities whose sum exceeds the spatial degree force a coefficient to vanish. -/
theorem coeff_theta_eq_zero_of_orders {ι : Type*} (R H : Tri) (P : F[X]) (z : F)
    (D w W m ρ : ℕ) (hR : wd R D ≤ w) (hH : wd H D ≤ W) (hP : P.natDegree ≤ D)
    (ω : ι ↪ F) (A : Finset ι) (orders : ι → ℕ)
    (ho : ∀ i ∈ A, (Polynomial.X - Polynomial.C (ω i)) ^ orders i ∣
      PowerSeries.coeff ρ (theta R P z m H))
    (hgt : (W : ℤ) + 2 * ((w : ℤ) - D) * ρ < ∑ i ∈ A, (orders i : ℤ)) :
    PowerSeries.coeff ρ (theta R P z m H) = 0 := by
  classical
  by_contra hne
  have hdeg := coeff_theta_degree R H P z D w W m ρ hR hH hP hne
  have hc : ∑ i ∈ A, orders i ≤ (PowerSeries.coeff ρ (theta R P z m H)).natDegree := by
    calc ∑ i ∈ A, orders i ≤
          ∑ i ∈ A, (PowerSeries.coeff ρ (theta R P z m H)).rootMultiplicity (ω i) :=
        Finset.sum_le_sum fun i hi => (Polynomial.le_rootMultiplicity_iff hne).mpr (ho i hi)
      _ ≤ _ := P64Cofactor.sum_rootMultiplicity_le_natDegree _ ω A
  have hc' : ∑ i ∈ A, (orders i : ℤ) ≤
      ((PowerSeries.coeff ρ (theta R P z m H)).natDegree : ℤ) := by exact_mod_cast hc
  omega

/-- Resultant orders for the original challenge coordinates. -/
theorem sum_theta_orders_le (R H : Tri) (hirr : Irreducible R)
    (hH : H ≠ 0) (hsmall : H.natDegree < R.natDegree)
    (dR dH : ℕ) (hRdeg : ∀ j a, ((R.coeff j).coeff a).natDegree ≤ dR)
    (hHdeg : ∀ j a, ((H.coeff j).coeff a).natDegree ≤ dH)
    (S : Finset F) (P : F → F[X]) (r : F → ℕ) (m : ℕ)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hderiv : ∀ z ∈ S, derivativeAlong R (P z) z ≠ 0)
    (hr : ∀ z ∈ S, r z ≤ m + 1)
    (hvan : ∀ z ∈ S, ∀ ρ < r z, PowerSeries.coeff ρ (theta R (P z) z m H) = 0) :
    ∑ z ∈ S, r z ≤ H.natDegree * dR + R.natDegree * dH := by
  have hn : ¬ reorder R ∣ reorder H := by
    intro hd
    have hh := Polynomial.natDegree_le_of_dvd hd (reorder_ne_zero hH)
    rw [reorder_natDegree, reorder_natDegree] at hh
    omega
  have hpos : 0 < (reorder R).natDegree := by rw [reorder_natDegree]; omega
  let zs : F ↪ F[X] := ⟨Polynomial.C, Polynomial.C_injective⟩
  let y : F → PowerSeries (F[X]) := fun z => PowerSeries.C (P z) +
    P64C6Theta.flow (center (P z) z R) (derivativeAlong R (P z) z) m
  have hc := P64C6Res.sum_orders_le (reorder R) (reorder H)
    (reorder_irreducible hirr) hpos hn dR dH
    (reorder_coeff_degree R dR hRdeg) (reorder_coeff_degree H dH hHdeg)
    zs S r y (fun z => (derivativeAlong R (P z) z) ^ 2)
    (fun z hz => pow_ne_zero _ (hderiv z hz))
    (fun z hz => ?_) (fun z hz => ?_)
  · simpa only [reorder_natDegree] using hc
  · dsimp only [y, zs, Function.Embedding.coeFn_mk]
    rw [← theta_eq_curveEval]
    exact dvd_trans (pow_dvd_pow _ (hr z hz)) (theta_self R (P z) z m (hcurve z hz))
  · dsimp only [y, zs, Function.Embedding.coeFn_mk]
    rw [← theta_eq_curveEval]
    exact PowerSeries.X_pow_dvd_iff.mpr (hvan z hz)

end P64C6Count
end ProximityPrize.SubmissionBinaryLower
