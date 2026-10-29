import ProximityPrize.SubmissionBinaryLower.P64C6All
import ProximityPrize.SubmissionBinaryLower.P64Light
import ProximityPrize.Benchmark.BinaryTargetLower

/-!
# Class 6 at the protected binary parameters
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6High

open Polynomial P64Found P64LineOrder P64Cofactor P64Light

section Generic

variable {F ι : Type*} [Field F]

lemma parameter_weight (R : Polynomial (Polynomial (Polynomial F))) :
    WtLE 0 1 1 (P64Caps.YZ.yzSupportDegree R 1) R := by
  intro a b l hn
  have ha : (R.coeff b).coeff a ≠ 0 := by
    intro hz
    simp [c3, hz] at hn
  have hb : R.coeff b ≠ 0 := by
    intro hz
    simp [hz] at ha
  have h1 := P64Caps.YZ.coeffWeight_le_of_ne R 1 b hb
  have h2 := Polynomial.Bivariate.coeff_natDegree_le_degreeX (R.coeff b) a
  have h3 : l ≤ ((R.coeff b).coeff a).natDegree := Polynomial.le_natDegree_of_ne_zero hn
  omega

lemma support_of_dangerous (R : Polynomial (Polynomial (Polynomial F)))
    (ω : ι ↪ F) (y : ι → F[X]) (D A : ℕ) (Az : Finset ι)
    (hcard : A ≤ Az.card) (hdang : Dangerous ω y D A R Az) :
    P64Caps.Weighted.weightedSupportDegree R D < ∑ i ∈ Az, lineOrd R (ω i) (y i) := by
  unfold Dangerous at hdang
  rw [Finset.sum_sub_distrib] at hdang
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hdang
  have hc : (A : ℤ) ≤ Az.card := by exact_mod_cast hcard
  have hh : (P64Caps.Weighted.weightedSupportDegree R D : ℤ) <
      ∑ i ∈ Az, (lineOrd R (ω i) (y i) : ℤ) := by omega
  exact_mod_cast hh

end Generic

open ProximityPrize.Benchmark

local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
local notation "Tri" => Polynomial (Polynomial (Polynomial Fld))
local notation "dom" => BinaryIRSProfile.domain
local notation "wd" => P64Caps.Weighted.weightedSupportDegree
local notation "yz" => P64Caps.YZ.yzSupportDegree

theorem card_le_of_positive_bias (u₀ u₁ : Idx → Fld) (R : Tri) (S : Finset Fld)
    (P : Fld → Fld[X]) (Az : Fld → Finset Idx)
    (hirr : Irreducible R) (hh : 1 ≤ R.natDegree)
    (hw : wd R 1048575 ≤ 249292 * 1482911 - 1)
    (hd : BadData dom u₀ u₁ R S P Az)
    (hbad : ∀ z ∈ S, Dangerous dom (lineOf u₀ u₁) 1048575 1482911 R (Az z))
    (hβ : 1000 * R.natDegree ≤ R.natDegree * 1482911 -
      ∑ i, lineOrd R (dom i) (lineOf u₀ u₁ i)) :
    S.card ≤ 17 * 2097152 * yz R 1 + 4 * R.natDegree * yz R 1 := by
  classical
  have hlow := natDegree_mul_le_weightedSupportDegree R hirr.ne_zero 1048575
  have hhcap : R.natDegree ≤ 352552 := by omega
  have hwcap : wd R 1048575 ≤ 369677849011 := by omega
  have hF : 2 * R.natDegree * wd R 1048575 < Fintype.card Fld := by
    rw [BF64.card_ext3]
    calc _ ≤ 2 * 352552 * 369677849011 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hhcap) hwcap
      _ < 2 ^ 192 := by norm_num
  apply P64C6All.card_le R hirr hh 1048575 1 (yz R 1) 2097152 434336
    (by norm_num) (parameter_weight R) (by simpa using BinaryIRSProfile.card_index.le)
    (by norm_num) (by norm_num) (by norm_num) hF dom (lineOf u₀ u₁)
    (lineOf_natDegree_le u₀ u₁)
    (by simpa [P64C6All.gap] using hβ) S P Az hd.deg hd.on_curve hd.card
  · intro z hz i hi
    rw [eval_lineOf]
    exact (hd.agree z hz i).mp hi
  · intro z hz
    exact support_of_dangerous R dom (lineOf u₀ u₁) 1048575 1482911 (Az z)
      (hd.card z hz) (hbad z hz)

end P64C6High
end ProximityPrize.SubmissionBinaryLower
