import ProximityPrize.SubmissionBinaryLower.P64Classes
import ProximityPrize.SubmissionBinaryLower.P64C6High

/-!
# Assembly after completion of the positive-bias class

Only the low-bias class 7 remains as an explicit hypothesis. This is an
intermediate theorem and is not the submitted candidate.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64HighAssembly

open Polynomial P64LineOrder P64Cofactor P64Light P64S3
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary

local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
local notation "Tri" => Polynomial (Polynomial (Polynomial Fld))
local notation "dom" => BinaryIRSProfile.domain
local notation "wd" => P64Caps.Weighted.weightedSupportDegree
local notation "yz" => P64Caps.YZ.yzSupportDegree

lemma widen_positive_bound (c h d : ℕ) (hc : c ≤ 17 * 2097152 * d + 4 * h * d) :
    (c : ℚ) ≤ 128 * 2097152 * d + 4 * h * d + 1 * 2097152 * (d + h) := by
  have hc' : (c : ℚ) ≤ 17 * 2097152 * d + 4 * h * d := by exact_mod_cast hc
  have hd : (0 : ℚ) ≤ d := Nat.cast_nonneg _
  have hh : (0 : ℚ) ≤ h := Nat.cast_nonneg _
  nlinarith

def Class7Interface : Prop :=
  ∀ (u₀ u₁ : Idx → Fld) (R : Tri) (Vs : Finset Fld) (P : Fld → Fld[X])
    (Az : Fld → Finset Idx),
    Irreducible R → 4 ≤ R.natDegree →
    ¬ (derivative R = 0 ∧ P64Incidence.dXPoly R ≠ 0) →
    wd R 1048575 ≤ 249292 * 1482911 - 1 → yz R 1 ≤ 58589180685 →
    (∀ t q, ¬ StGood dom u₀ u₁ R t q) →
    (full dom u₀ u₁ R).card < 208984 →
    208984 ≤ (P64Incidence.lam dom (lineOf u₀ u₁) R).card →
    BadData dom u₀ u₁ R Vs P Az →
    (∀ z ∈ Vs, Dangerous dom (lineOf u₀ u₁) 1048575 1482911 R (Az z)) →
    R.natDegree * 1482911 - (∑ i, lineOrd R (dom i) (lineOf u₀ u₁ i)) < 1000 * R.natDegree →
    (Vs.card : ℚ) ≤ 128 * 2097152 * yz R 1 + 4 * R.natDegree * yz R 1 +
      2097152 * (yz R 1 + R.natDegree)

theorem high_of_class7 (h7 : Class7Interface) : P64Classes.HighInterface 128 4 1 := by
  intro u₀ u₁ R Vs P Az hirr hh hXY hw hyz hgood hfull hlam hd hbad
  by_cases hb : 1000 * R.natDegree ≤ R.natDegree * 1482911 -
      ∑ i, lineOrd R (dom i) (lineOf u₀ u₁ i)
  · have hc := P64C6High.card_le_of_positive_bias u₀ u₁ R Vs P Az hirr (by omega) hw hd hbad hb
    exact widen_positive_bound Vs.card R.natDegree (yz R 1) hc
  · simpa using h7 u₀ u₁ R Vs P Az hirr hh hXY hw hyz hgood hfull hlam hd hbad (by omega)

theorem protocolClaim6400_of_class7 (h7 : Class7Interface) :
    ProtocolClaim 6400 78622925 268435456 :=
  protocolClaim6400_of_high (K1 := 128) (K2 := 4) (K3 := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (high_of_class7 h7)

end P64HighAssembly
end ProximityPrize.SubmissionBinaryLower
