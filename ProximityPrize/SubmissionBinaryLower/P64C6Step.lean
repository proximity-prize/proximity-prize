import ProximityPrize.SubmissionBinaryLower.P64C6Line

/-!
# The finite Stepanov implication for a flat auxiliary polynomial

Once a nonzero auxiliary polynomial of outer degree below that of `R` is
available, line flatness forces parameter orders in its resultant with `R`.
The dimension count that constructs the auxiliary is separate.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Step

open Polynomial P64C6Coordinates P64C6Count P64C6Line BCHKSSubstitutionVanish

variable {F ι : Type*} [Field F]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree

lemma forcing_inequality (A : Finset ι) (ν μ : ι → ℕ) (W w D ρ : ℕ)
    (hb : 2 * (ρ : ℤ) * ((w : ℤ) - D - ∑ i ∈ A, ((μ i - 1 : ℕ) : ℤ)) <
      (∑ i ∈ A, (ν i : ℤ)) - W) :
    (W : ℤ) + 2 * ((w : ℤ) - D) * ρ <
      ∑ i ∈ A, ((ν i + 2 * ρ * (μ i - 1) : ℕ) : ℤ) := by
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  nlinarith

/-- A flat auxiliary polynomial bounds the total order of all selected bad parameters. -/
theorem sum_forced_orders_le (R H : Tri) (hirr : Irreducible R)
    (hH : H ≠ 0) (hsmall : H.natDegree < R.natDegree)
    (D w W dR e m : ℕ) (hRw : wd R D ≤ w) (hHw : wd H D ≤ W)
    (hRdeg : ∀ j a, ((R.coeff j).coeff a).natDegree ≤ dR)
    (hHdeg : ∀ j a, ((H.coeff j).coeff a).natDegree ≤ e)
    (ω : ι ↪ F) (y : ι → F[X]) (μ ν : ι → ℕ) (G : ι → Tri)
    (S : Finset F) (P : F → F[X]) (A : F → Finset ι) (r : F → ℕ)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ D)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hderiv : ∀ z ∈ S, derivativeAlong R (P z) z ≠ 0)
    (hr : ∀ z ∈ S, r z ≤ m + 1)
    (hμ : ∀ z ∈ S, ∀ i ∈ A z, 1 ≤ μ i)
    (hRord : ∀ z ∈ S, ∀ i ∈ A z, P64LineOrder.OrdGE R (ω i) (y i) (μ i))
    (hflat : ∀ z ∈ S, ∀ i ∈ A z, P64LineOrder.OrdGE (H + R * G i) (ω i) (y i) (ν i))
    (hmatch : ∀ z ∈ S, ∀ i ∈ A z, (P z).eval (ω i) = (y i).eval z)
    (hb : ∀ z ∈ S, ∀ ρ < r z,
      2 * (ρ : ℤ) * ((w : ℤ) - D - ∑ i ∈ A z, ((μ i - 1 : ℕ) : ℤ)) <
        (∑ i ∈ A z, (ν i : ℤ)) - W) :
    ∑ z ∈ S, r z ≤ H.natDegree * dR + R.natDegree * e := by
  apply sum_theta_orders_le R H hirr hH hsmall dR e hRdeg hHdeg S P r m hcurve hderiv hr
  intro z hz ρ hρ
  have hρm : ρ ≤ m := by have := hr z hz; omega
  apply coeff_theta_eq_zero_of_orders R H (P z) z D w W m ρ hRw hHw (hP z hz)
    ω (A z) (fun i => ν i + 2 * ρ * (μ i - 1))
  · intro i hi
    exact theta_flat_order R H (G i) (ω i) z (P z) (y i) (μ i) (ν i) m ρ
      (hμ z hz i hi) hρm (hRord z hz i hi) (hflat z hz i hi)
      (hmatch z hz i hi) (hcurve z hz) (hderiv z hz)
  · exact forcing_inequality (A z) ν μ W w D ρ (hb z hz ρ hρ)

end P64C6Step
end ProximityPrize.SubmissionBinaryLower
