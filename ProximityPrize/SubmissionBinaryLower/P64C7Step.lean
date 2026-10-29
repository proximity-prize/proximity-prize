import ProximityPrize.SubmissionBinaryLower.P64C7Residual
import ProximityPrize.SubmissionBinaryLower.P64C6Finite

/-!
# The finite count for a residual auxiliary

Matched points contribute their usual flow orders. The missing point adds
the residual order, and the resultant pays for the resulting vanishing.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Step

open Polynomial P64Found P64LineOrder P64C6Coordinates P64C6Count P64C6Line
  P64C6Finite P64C6Boxes P64C7Auxiliary P64C7Residual BCHKSSubstitutionVanish

variable {F ι : Type*} [Field F]

noncomputable local instance : CommRing (Polynomial F) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial F)) := Polynomial.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial (Polynomial F))) := Polynomial.commRing

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree

theorem sum_forced_orders_le (R H : Tri) (hirr : Irreducible R)
    (hH : H ≠ 0) (hsmall : H.natDegree < R.natDegree)
    (D w W d e m s : ℕ) (hRw : wd R D ≤ w) (hHw : wd H D ≤ W)
    (hRdeg : ∀ j a, ((R.coeff j).coeff a).natDegree ≤ d)
    (hHdeg : ∀ j a, ((H.coeff j).coeff a).natDegree ≤ e)
    (ω : ι ↪ F) (y : ι → F[X]) (μ : ι → ℕ) (i : ι)
    (hflat : Residual R H (ω i) (y i) s)
    (S : Finset F) (P : F → F[X]) (A : F → Finset ι) (r : F → ℕ)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ D)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hderiv : ∀ z ∈ S, derivativeAlong R (P z) z ≠ 0)
    (hr : ∀ z ∈ S, r z ≤ m + 1)
    (hμ : ∀ z ∈ S, ∀ j ∈ A z, 1 ≤ μ j)
    (hRord : ∀ z ∈ S, ∀ j ∈ A z, OrdGE R (ω j) (y j) (μ j))
    (hmatch : ∀ z ∈ S, ∀ j ∈ A z, (P z).eval (ω j) = (y j).eval z)
    (hmiss : ∀ z ∈ S, (P z).eval (ω i) ≠ (y i).eval z)
    (hb : ∀ z ∈ S, ∀ ρ < r z,
      2 * (ρ : ℤ) * ((w : ℤ) - D - ∑ j ∈ A z, ((μ j - 1 : ℕ) : ℤ)) < (s : ℤ) - W) :
    ∑ z ∈ S, r z ≤ H.natDegree * d + R.natDegree * e := by
  classical
  apply sum_theta_orders_le R H hirr hH hsmall d e hRdeg hHdeg S P r m hcurve hderiv hr
  intro z hz ρ hρ
  have hρm : ρ ≤ m := by have := hr z hz; omega
  have hi : i ∉ A z := fun hi => hmiss z hz (hmatch z hz i hi)
  let orders : ι → ℕ := fun j => if j = i then s else 2 * ρ * (μ j - 1)
  apply coeff_theta_eq_zero_of_orders R H (P z) z D w W m ρ hRw hHw (hP z hz)
    ω (insert i (A z)) orders
  · intro j hj
    rcases Finset.mem_insert.mp hj with he | hj
    · subst j
      simp only [orders, if_true]
      exact theta_residual_order R H (ω i) z (P z) (y i) s m ρ hflat (hmiss z hz)
        (hcurve z hz) hρm
    · have hji : j ≠ i := fun he => hi (he ▸ hj)
      simp only [orders, if_neg hji]
      simpa only [zero_add] using theta_order R H (ω j) z (P z) (y j) (μ j) 0 m ρ
        (hμ z hz j hj) hρm (hRord z hz j hj) (fun a b hab => by omega)
        (hmatch z hz j hj) (hcurve z hz) (hderiv z hz)
  · rw [Finset.sum_insert hi]
    have he : ∑ j ∈ A z, (orders j : ℤ) =
        ∑ j ∈ A z, (2 * (ρ : ℤ) * ((μ j - 1 : ℕ) : ℤ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := fun he => hi (he ▸ hj)
      simp [orders, hji]
    rw [he, ← Finset.mul_sum]
    simp only [orders, if_true]
    have hh := hb z hz ρ hρ
    nlinarith

theorem forced_orders_of_dimension (R : Tri) (hirr : Irreducible R)
    (D w W q e d m s ν : ℕ) (hRw : wd R D ≤ w) (hRyz : WtLE 0 q 1 d R)
    (ω : ι ↪ F) (y : ι → F[X]) (i : ι) (hy : (y i).natDegree ≤ q)
    (R'' : Polynomial (Polynomial F))
    (hR0 : (lineShift R (ω i) (y i)).map (Polynomial.constantCoeff (R := Polynomial F)) =
      Polynomial.X ^ ν * R'')
    (hu : R''.coeff 0 ≠ 0) (hμh : lineOrd R (ω i) (y i) ≤ R.natDegree)
    (hμs : lineOrd R (ω i) (y i) ≤ s) (hνs : ν ≤ s)
    (hqd : q * lineOrd R (ω i) (y i) ≤ d)
    (hdim : P64C7Counts.upper s R.natDegree q d (lineOrd R (ω i) (y i)) ν e <
      (auxiliary D W q e R.natDegree).card)
    (S : Finset F) (P : F → F[X]) (A : F → Finset ι) (r : F → ℕ)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ D)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hderiv : ∀ z ∈ S, derivativeAlong R (P z) z ≠ 0)
    (hr : ∀ z ∈ S, r z ≤ m + 1)
    (hμ : ∀ z ∈ S, ∀ j ∈ A z, 1 ≤ lineOrd R (ω j) (y j))
    (hmatch : ∀ z ∈ S, ∀ j ∈ A z, (P z).eval (ω j) = (y j).eval z)
    (hmiss : ∀ z ∈ S, (P z).eval (ω i) ≠ (y i).eval z)
    (hb : ∀ z ∈ S, ∀ ρ < r z,
      2 * (ρ : ℤ) * ((w : ℤ) - D - ∑ j ∈ A z, ((lineOrd R (ω j) (y j) - 1 : ℕ) : ℤ)) <
        (s : ℤ) - W) :
    ∑ z ∈ S, r z ≤ (R.natDegree - 1) * d + R.natDegree * e := by
  obtain ⟨H, hH, hHw, hHdeg, hHyz, hflat⟩ := P64C7Auxiliary.exists_auxiliary
    R (ω i) (y i) D W q e R.natDegree d s (lineOrd R (ω i) (y i)) ν R'' hy
    (ordGE_lineOrd R (ω i) (y i)) hR0 hu le_rfl hRyz hμh hμs hνs hqd hdim
  have hc := sum_forced_orders_le R H hirr hH hHdeg D w W d e m s hRw hHw
    (coefficient_parameter_degree R q d hRyz) (coefficient_parameter_degree H q e hHyz)
    ω y (fun j => lineOrd R (ω j) (y j)) i hflat S P A r hP hcurve hderiv hr hμ
    (fun _ _ j _ => ordGE_lineOrd R (ω j) (y j)) hmatch hmiss hb
  exact hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_right d (by omega)) _)

end P64C7Step
end ProximityPrize.SubmissionBinaryLower
