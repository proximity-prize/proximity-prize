import ProximityPrize.SubmissionBinaryLower.P64C7Mass

/-!
# Counting retained curves from their profile

Every retained curve has positive normal defect. Clearing all `2*N`
denominators by a finite product combines the mass bounds over the field.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7Retained

open Polynomial P64Found P64LineOrder P64C6Coordinates P64C6Bessel
  P64C7Aggregate BCHKSSubstitutionVanish

variable {F ι : Type*} [Field F] [Fintype ι]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))
local notation "wd" => P64Caps.Weighted.weightedSupportDegree

theorem card_le (R : Tri) (hirr : Irreducible R) (hh : 3 ≤ R.natDegree)
    (w q d : ℕ) (hd : 1 ≤ d) (hqh : q * R.natDegree ≤ d)
    (hRw : wd R 1048575 ≤ w) (hRyz : WtLE 0 q 1 d R)
    (ω : ι ↪ F) (y : ι → F[X]) (hy : ∀ j, (y j).natDegree ≤ q)
    (hprofile : 2 * (R.natDegree : ℤ) * w - R.natDegree ^ 2 * 1048575 -
      (∑ i, (lineOrd R (ω i) (y i) : ℤ) ^ 2) ≤ 65536 * R.natDegree ^ 2)
    (S : Finset F) (P : F → F[X]) (A : F → Finset ι)
    (hP : ∀ z ∈ S, (P z).natDegree ≤ 1048575)
    (hcurve : ∀ z ∈ S, triEval R z (P z) = 0)
    (hderiv : ∀ z ∈ S, derivativeAlong R (P z) z ≠ 0)
    (hμ : ∀ z ∈ S, ∀ j ∈ A z, 1 ≤ lineOrd R (ω j) (y j))
    (hmatch : ∀ z ∈ S, ∀ j, j ∈ A z ↔ (P z).eval (ω j) = (y j).eval z)
    (hproper : ∀ z ∈ S, ∃ i ∈ A z, lineOrd R (ω i) (y i) < R.natDegree)
    (hcard : ∀ z ∈ S, 1482911 ≤ (A z).card)
    (hsupport : ∀ z ∈ S, w < ∑ i ∈ A z, lineOrd R (ω i) (y i)) :
    S.card ≤ 40 * Fintype.card ι * d := by
  classical
  let h := R.natDegree
  let μ : ι → ℕ := fun i => lineOrd R (ω i) (y i)
  let N : F → ℕ := fun z => (normalDefect R ω y (A z) w 1048575).toNat
  have hN : ∀ z ∈ S, 0 < normalDefect R ω y (A z) w 1048575 := by
    intro z hz
    obtain ⟨i, hi, hin⟩ := hproper z hz
    exact positive_defect R hirr (by omega) 1048575 w q d hd hqh hRw hRyz ω y hy z (P z) (A z)
      (hP z hz) (hcurve z hz) (hderiv z hz) (hμ z hz)
      (fun j hj => (hmatch z hz j).mp hj) i hi hin
  have hNeq : ∀ z ∈ S, (N z : ℤ) = normalDefect R ω y (A z) w 1048575 :=
    fun z hz => Int.toNat_of_nonneg (hN z hz).le
  have hNp : ∀ z ∈ S, 0 < N z := by
    intro z hz
    have he := hNeq z hz
    have hp := hN z hz
    omega
  let C := ∏ z ∈ S, (2 * N z)
  let τ : F → ℕ := fun z => C / (2 * N z)
  have hC : 0 < C := Finset.prod_pos (fun z hz => Nat.mul_pos (by norm_num) (hNp z hz))
  have hτeq : ∀ z ∈ S, 2 * τ z * N z = C := by
    intro z hz
    have hdvd : 2 * N z ∣ C := Finset.dvd_prod_of_mem (fun z => 2 * N z) hz
    have he := Nat.mul_div_cancel' hdvd
    change 2 * (C / (2 * N z)) * N z = C
    nlinarith only [he]
  have hτ : ∀ z ∈ S, 2 * (τ z : ℤ) * normalDefect R ω y (A z) w 1048575 ≤ C := by
    intro z hz
    rw [← hNeq z hz]
    exact_mod_cast (hτeq z hz).le
  have hc := weighted_mass_le R hirr (by omega) 1048575 w q d C hd hqh hC hRw hRyz
    ω y hy S P A τ hP hcurve hderiv hμ hmatch hτ
  have hμh : ∀ i, μ i ≤ h := fun i => lineOrd_le_natDegree_of_irreducible hirr (by omega) (ω i) (y i)
  have hpoint : ∀ z ∈ S, C * h ^ 2 ≤ 4 * (τ z * mass h μ (A z)) := by
    intro z hz
    have hl := P64C7Mass.mass_lower h w (N z) μ (A z) hh hμh (hμ z hz) (hcard z hz)
      (hsupport z hz) (hNeq z hz) hprofile
    have hm := Nat.mul_le_mul_left (τ z) hl
    have he := congrArg (fun k : ℕ => k * h ^ 2) (hτeq z hz)
    nlinarith only [hm, he]
  have hs := Finset.sum_le_sum hpoint
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hs
  have hf : (C * h ^ 2) * S.card ≤ (C * h ^ 2) * (40 * Fintype.card ι * d) := by
    change _ ≤ 10 * C * h ^ 2 * Fintype.card ι * d at hc
    nlinarith only [hc, hs]
  exact Nat.le_of_mul_le_mul_left hf (Nat.mul_pos hC (pow_pos (by dsimp [h]; omega) 2))

end P64C7Retained
end ProximityPrize.SubmissionBinaryLower
