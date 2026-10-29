import ProximityPrize.SubmissionBinaryLower.P64C6Auxiliary

/-!
# Finite Stepanov bound from the coefficient-count inequality

This theorem constructs the auxiliary internally. Its remaining numerical
hypotheses are the strict dimension inequality and the forced-order inequalities.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Finite

open Polynomial P64Found P64LineOrder P64C6Coordinates P64C6Degree P64C6Boxes
  P64C6Weights P64C6Auxiliary BCHKSSubstitutionVanish

variable {F ι : Type*} [Field F]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree

lemma coefficient_parameter_degree (R : Tri) (q e : ℕ) (hR : WtLE 0 q 1 e R) (j a : ℕ) :
    ((R.coeff j).coeff a).natDegree ≤ e := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro l hl
  by_contra hn
  have h := hR a j l hn
  omega

/-- The nonzero derivative along a bad curve pays for all its line-order defects. -/
theorem normal_defect_nonneg (R : Tri) (P : F[X]) (z : F) (D w : ℕ)
    (hR : wd R D ≤ w) (hP : P.natDegree ≤ D) (hs : derivativeAlong R P z ≠ 0)
    (ω : ι ↪ F) (y : ι → F[X]) (A : Finset ι) (μ : ι → ℕ)
    (hord : ∀ i ∈ A, OrdGE R (ω i) (y i) (μ i))
    (hmatch : ∀ i ∈ A, P.eval (ω i) = (y i).eval z) :
    0 ≤ (w : ℤ) - D - ∑ i ∈ A, ((μ i - 1 : ℕ) : ℤ) := by
  classical
  have hdeg := (derivativeAlong_degree R P z D w hR hP).resolve_left hs
  have hloc : ∀ i ∈ A, μ i - 1 ≤ (derivativeAlong R P z).rootMultiplicity (ω i) := by
    intro i hi
    apply le_rootMultiplicity_triEval (Polynomial.derivative R) (ω i) z (y i) P (μ i - 1)
    · exact ordGE_derivative R (ω i) (y i) (μ i) (hord i hi)
    · exact hmatch i hi
    · exact hs
  have hn : ∑ i ∈ A, (μ i - 1) ≤ (derivativeAlong R P z).natDegree := by
    calc _ ≤ ∑ i ∈ A, (derivativeAlong R P z).rootMultiplicity (ω i) := Finset.sum_le_sum hloc
      _ ≤ _ := P64Cofactor.sum_rootMultiplicity_le_natDegree _ ω A
  have hn' : ∑ i ∈ A, ((μ i - 1 : ℕ) : ℤ) ≤ (derivativeAlong R P z).natDegree := by
    exact_mod_cast hn
  omega

variable [Fintype ι]

theorem forced_orders_of_dimension (R : Tri) (hirr : Irreducible R)
    (D w W q e d m : ℕ) (hRw : wd R D ≤ w) (hRyz : WtLE 0 q 1 d R) (hde : d ≤ e)
    (ω : ι ↪ F) (y : ι → F[X]) (hy : ∀ i, (y i).natDegree ≤ q) (s : ι → ℕ)
    (hdim : (∑ i, (conditions (s i) q e).card) < (auxiliary D W q e R.natDegree).card +
      ∑ i, (conditions (s i - lineOrd R (ω i) (y i)) q (e - d)).card)
    (S : Finset F) (P : F → F[X]) (A : F → Finset ι) (r : F → ℕ)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ D)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hderiv : ∀ z ∈ S, derivativeAlong R (P z) z ≠ 0)
    (hr : ∀ z ∈ S, r z ≤ m + 1)
    (hμ : ∀ z ∈ S, ∀ i ∈ A z, 1 ≤ lineOrd R (ω i) (y i))
    (hmatch : ∀ z ∈ S, ∀ i ∈ A z, (P z).eval (ω i) = (y i).eval z)
    (hb : ∀ z ∈ S, ∀ ρ < r z,
      2 * (ρ : ℤ) * ((w : ℤ) - D - ∑ i ∈ A z, ((lineOrd R (ω i) (y i) - 1 : ℕ) : ℤ)) <
        (∑ i ∈ A z, (s i : ℤ)) - W) :
    ∑ z ∈ S, r z ≤ (R.natDegree - 1) * d + R.natDegree * e := by
  obtain ⟨H, G, hH, hHw, hHdeg, hHyz, hflat⟩ :=
    exists_auxiliary R hirr.ne_zero D W q e R.natDegree d hRyz hde ω y hy s hdim
  have hc := P64C6Step.sum_forced_orders_le R H hirr hH hHdeg D w W d e m hRw hHw
    (coefficient_parameter_degree R q d hRyz) (coefficient_parameter_degree H q e hHyz)
    ω y (fun i => lineOrd R (ω i) (y i)) s G S P A r hP hcurve hderiv hr hμ
    (fun _ _ i _ => ordGE_lineOrd R (ω i) (y i))
    (fun _ _ i _ => hflat i) hmatch hb
  exact hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_right d (by omega)) _)

end P64C6Finite
end ProximityPrize.SubmissionBinaryLower
