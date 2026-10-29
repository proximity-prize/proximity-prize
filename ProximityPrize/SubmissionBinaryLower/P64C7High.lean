import ProximityPrize.SubmissionBinaryLower.P64HighAssembly
import ProximityPrize.SubmissionBinaryLower.P64C7All
import ProximityPrize.SubmissionBinaryLower.P64C7Profile

/-!
# Completing the binary 64.00 certificate

The low-bias profile follows from the existing bounded interpolation test.
The residual count and Frobenius descent discharge the remaining class.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7High

open Polynomial P64LineOrder P64Cofactor P64Light ProximityPrize.Benchmark
  ProximityPrize.Benchmark.Binary

local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
local notation "dom" => BinaryIRSProfile.domain
local notation "wd" => P64Caps.Weighted.weightedSupportDegree
local notation "yz" => P64Caps.YZ.yzSupportDegree

theorem class7 : P64HighAssembly.Class7Interface := by
  intro u₀ u₁ R S P Az hirr hh _hXY hw _hyz hgood hfull _hlam hd hbad hβ
  have hlow := natDegree_mul_le_weightedSupportDegree R hirr.ne_zero 1048575
  have hhcap : R.natDegree ≤ 352552 := by omega
  have hwcap : wd R 1048575 ≤ 369677849011 := by omega
  have hF : 2 * R.natDegree * wd R 1048575 < Fintype.card Fld := by
    rw [BF64.card_ext3]
    calc _ ≤ 2 * 352552 * 369677849011 := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hhcap) hwcap
      _ < 2 ^ 192 := by norm_num
  have hb : R.natDegree * 1481911 < ∑ i, lineOrd R (dom i) (lineOf u₀ u₁ i) := by omega
  have hp := P64C7Profile.profile_le dom u₀ u₁ R hirr hh hw hgood hβ
  have hc := P64C7All.card_le R hirr (by omega) 1 (yz R 1) (by norm_num)
    (P64C6High.parameter_weight R) (by simpa using BinaryIRSProfile.card_index.le) hF
    dom (lineOf u₀ u₁) (lineOf_natDegree_le u₀ u₁) hb hfull hp S P Az hd.deg hd.on_curve hd.card
    (fun z hz i => by simpa [eval_lineOf] using hd.agree z hz i)
    (fun z hz => P64C6High.support_of_dangerous R dom (lineOf u₀ u₁) 1048575 1482911 (Az z)
      (hd.card z hz) (hbad z hz))
  have hc' : (S.card : ℚ) ≤ 41 * 2097152 * yz R 1 + 4 * R.natDegree * yz R 1 := by
    exact_mod_cast hc
  have hd' : (0 : ℚ) ≤ yz R 1 := Nat.cast_nonneg _
  have hh' : (0 : ℚ) ≤ R.natDegree := Nat.cast_nonneg _
  nlinarith only [hc', hd', hh']

theorem protocolClaim6400 : ProtocolClaim 6400 78622925 268435456 :=
  P64HighAssembly.protocolClaim6400_of_class7 class7

end P64C7High
end ProximityPrize.SubmissionBinaryLower
