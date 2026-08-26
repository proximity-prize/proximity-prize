import ProximityPrize.SubmissionLower.BCHKSCodimTupleCount6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSHybridCoreSwitchAudit6400
open BCHKSHybridHighDegreeAudit6400
open BCHKSBoundaryCoreArrangement6400
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def bchksHybridCoreSwitchCodim6400 : ℕ := 13
def bchksHybridCoreSwitchTupleSize6400 : ℕ := 14
def bchksHybridCoreSwitchAmbient6400 : ℕ := 131086
def bchksHybridCoreSwitchIncidences6400 : ℕ := 54306
def bchksHybridCoreSwitchPerFactorCap6400 : ℕ := 17522390696
def bchksHybridCoreSwitchExcess6400 : ℕ := 2895540839095
def bchksHybridCoreSwitchTotal6400 : ℕ := 274975480759976375
def bchksHybridCoreSwitchCodim14PerFactorCap6400 : ℕ := 42295792977
def bchksHybridCoreSwitchCodim14Excess6400 : ℕ := 6989297180479
def bchksHybridCoreSwitchCodim14Total6400 : ℕ := 274979574516317759
theorem fiveTwelve_mul_sub128_le_square (d : ℕ) (hd : 128 ≤ d) :
    512 * (d - 128) ≤ d * d := by
  have hsq : (0 : ℤ) ≤ ((d : ℤ) - 256) ^ 2 := sq_nonneg _
  have hz : ((d - 128 : ℕ) : ℤ) = (d : ℤ) - 128 := by
    omega
  exact_mod_cast (show (512 : ℤ) * ((d : ℤ) - 128) ≤ (d : ℤ) * d by
    nlinarith)
theorem mul_fiveTwelve_sub_le (d : ℕ) (hd : d ≤ 512) :
    d * (512 - d) ≤ 512 * 128 := by
  have hsq : (0 : ℤ) ≤ ((d : ℤ) - 256) ^ 2 := sq_nonneg _
  have hz : ((512 - d : ℕ) : ℤ) = 512 - (d : ℤ) := by
    omega
  exact_mod_cast (show (d : ℤ) * (512 - (d : ℤ)) ≤ 512 * 128 by
    nlinarith)
theorem factorCharge_scaled_le_universal_or_core_of_base
    (u L d z C charge : ℕ) (hLu : 128 * u ≤ L) (hd : 128 ≤ d)
    (huniversal : charge ≤ u * d * z)
    (hcore : charge ≤ C) :
    512 * charge ≤ 512 * L * z + d * C := by
  have hLu' : u * 128 ≤ L := by
    simpa only [Nat.mul_comm] using hLu
  by_cases huzC : u * d * z ≤ C
  · have hscale := Nat.mul_le_mul_left (512 * (d - 128)) huzC
    have hsquare := fiveTwelve_mul_sub128_le_square d hd
    have hsquareC := Nat.mul_le_mul_right C hsquare
    have hbig :
        512 * (d - 128) * (u * d * z) ≤ d * d * C :=
      hscale.trans hsquareC
    have hdpos : 0 < d := by omega
    have hdelta : 512 * u * (d - 128) * z ≤ d * C := by
      apply le_of_mul_le_mul_left _ hdpos
      calc
        d * (512 * u * (d - 128) * z) =
            512 * (d - 128) * (u * d * z) := by ring
        _ ≤ d * d * C := hbig
        _ = d * (d * C) := by ring
    have hdSplit : d = 128 + (d - 128) := by omega
    have hdecomp : u * d * z =
        u * 128 * z + u * (d - 128) * z := by
      calc
        u * d * z = u * (128 + (d - 128)) * z := by
          conv_lhs => rw [hdSplit]
        _ = u * 128 * z + u * (d - 128) * z := by ring
    calc
      512 * charge ≤ 512 * (u * d * z) :=
        Nat.mul_le_mul_left 512 huniversal
      _ = 512 * (u * 128 * z) + 512 * u * (d - 128) * z := by
        rw [hdecomp, Nat.mul_add]
        ring
      _ ≤ 512 * (L * z) + d * C := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_left 512
            (Nat.mul_le_mul_right z hLu')) hdelta
      _ = 512 * L * z + d * C := by ring
  · have hCuniv : C ≤ u * d * z := by omega
    by_cases hd512 : d ≤ 512
    · have hsquare := mul_fiveTwelve_sub_le d hd512
      have hleft : (512 - d) * C ≤ 512 * L * z := by
        calc
          (512 - d) * C ≤ (512 - d) * (u * d * z) :=
            Nat.mul_le_mul_left _ hCuniv
          _ = u * (d * (512 - d)) * z := by ring
          _ ≤ u * (512 * 128) * z := by
            exact Nat.mul_le_mul_right z (Nat.mul_le_mul_left u hsquare)
          _ ≤ 512 * L * z := by
            have := Nat.mul_le_mul_left 512
              (Nat.mul_le_mul_right z hLu)
            simpa [mul_assoc, mul_left_comm, mul_comm] using this
      have hsplit : 512 = d + (512 - d) := by omega
      calc
        512 * charge ≤ 512 * C := Nat.mul_le_mul_left 512 hcore
        _ = (d + (512 - d)) * C := by rw [← hsplit]
        _ = d * C + (512 - d) * C := by rw [Nat.add_mul]
        _ ≤ d * C + 512 * L * z := Nat.add_le_add_left hleft _
        _ = 512 * L * z + d * C := by omega
    · have hdlarge : 512 ≤ d := by omega
      calc
        512 * charge ≤ 512 * C := Nat.mul_le_mul_left 512 hcore
        _ ≤ d * C := Nat.mul_le_mul_right C hdlarge
        _ ≤ 512 * L * z + d * C := Nat.le_add_left _ _
theorem factorCharge_scaled_le_universal_or_core
    (d z C charge : ℕ) (hd : 128 ≤ d)
    (huniversal : charge ≤
      bchksHybridUniversalUnitCoefficient6400 * d * z)
    (hcore : charge ≤ C) :
    512 * charge ≤
      512 * bchksHybridLowZCoefficient6400 * z + d * C := by
  apply factorCharge_scaled_le_universal_or_core_of_base
    bchksHybridUniversalUnitCoefficient6400
      bchksHybridLowZCoefficient6400 d z C charge
  · have hcoeff := bchksHybrid_coefficients_exact6400
    calc
      128 * bchksHybridUniversalUnitCoefficient6400 =
          bchksHybridUniversalZCoefficient128_6400 := by
        rw [hcoeff.2.1, Nat.mul_comm]
      _ ≤ bchksHybridLowZCoefficient6400 := Nat.le_of_lt hcoeff.2.2.1
  · exact hd
  · exact huniversal
  · exact hcore
theorem sum_factorCharge_scaled_le
    {R : Type*} [DecidableEq R]
    (Rs : Finset R) (degree zDegree charge : R → ℕ) (C : ℕ)
    (hscaled : ∀ r ∈ Rs,
      512 * charge r ≤
        512 * bchksHybridLowZCoefficient6400 * zDegree r +
          degree r * C)
    (hzMass : (∑ r ∈ Rs, zDegree r) ≤ bchksHybridZMass6400)
    (hyMass : (∑ r ∈ Rs, degree r) ≤ bchksHybridYMass6400) :
    512 * (∑ r ∈ Rs, charge r) ≤
      512 * bchksHybridLowZCoefficient6400 * bchksHybridZMass6400 +
        bchksHybridYMass6400 * C := by
  calc
    512 * (∑ r ∈ Rs, charge r) =
        ∑ r ∈ Rs, 512 * charge r := by rw [Finset.mul_sum]
    _ ≤ ∑ r ∈ Rs,
        (512 * bchksHybridLowZCoefficient6400 * zDegree r +
          degree r * C) := Finset.sum_le_sum hscaled
    _ = 512 * bchksHybridLowZCoefficient6400 *
          (∑ r ∈ Rs, zDegree r) +
        (∑ r ∈ Rs, degree r) * C := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    _ ≤ 512 * bchksHybridLowZCoefficient6400 * bchksHybridZMass6400 +
        bchksHybridYMass6400 * C := by gcongr
lemma bchksHybridCoreSwitch_codim13_exact6400 :
    bchksHybridCoreSwitchTupleSize6400 =
        bchksHybridCoreSwitchCodim6400 + 1 ∧
      bchksHybridCoreSwitchAmbient6400 =
        bchksBoundaryOffCore6400 + bchksHybridCoreSwitchCodim6400 ∧
      bchksHybridCoreSwitchIncidences6400 =
        bchksBoundaryDeficiency6400 + bchksHybridCoreSwitchCodim6400 ∧
      (bchksBoundaryErrors6400 *
          fallingFactorial6400 bchksHybridCoreSwitchAmbient6400
            bchksHybridCoreSwitchTupleSize6400) /
          fallingFactorial6400 bchksHybridCoreSwitchIncidences6400
            bchksHybridCoreSwitchTupleSize6400 =
        bchksHybridCoreSwitchPerFactorCap6400 := by
  constructor
  · norm_num [bchksHybridCoreSwitchTupleSize6400,
      bchksHybridCoreSwitchCodim6400]
  constructor
  · norm_num [bchksHybridCoreSwitchAmbient6400,
      bchksBoundaryOffCore6400, bchksHybridCoreSwitchCodim6400]
  constructor
  · norm_num [bchksHybridCoreSwitchIncidences6400,
      bchksBoundaryDeficiency6400, bchksHybridCoreSwitchCodim6400]
  · native_decide
lemma bchksHybridCoreSwitch_budget6400 :
    bchksHybridCoreSwitchExcess6400 =
        (bchksHybridCoreSwitchPerFactorCap6400 *
            bchksHybridYMass6400 + 511) / 512 ∧
      bchksHybridCoreSwitchPerFactorCap6400 * bchksHybridYMass6400 ≤
        512 * bchksHybridCoreSwitchExcess6400 ∧
      bchksHybridCoreSwitchTotal6400 =
        bchksHybridTotal128_6400 + bchksHybridCoreSwitchExcess6400 ∧
      bchksHybridCoreSwitchTotal6400 < bchksWeightedNumerator6400 ∧
      bchksWeightedNumerator6400 - bchksHybridCoreSwitchTotal6400 =
        3519240023625 := by
  norm_num [bchksHybridCoreSwitchExcess6400,
    bchksHybridCoreSwitchPerFactorCap6400, bchksHybridYMass6400,
    bchksHybridCoreSwitchTotal6400, bchksHybridTotal128_6400,
    bchksWeightedNumerator6400]
theorem sum_factorCharge_le_codim13ExpensiveCap
    {R : Type*} [DecidableEq R]
    (Rs : Finset R) (degree zDegree charge : R → ℕ)
    (hscaled : ∀ r ∈ Rs,
      512 * charge r ≤
        512 * bchksHybridLowZCoefficient6400 * zDegree r +
          degree r * bchksHybridCoreSwitchPerFactorCap6400)
    (hzMass : (∑ r ∈ Rs, zDegree r) ≤ bchksHybridZMass6400)
    (hyMass : (∑ r ∈ Rs, degree r) ≤ bchksHybridYMass6400) :
    (∑ r ∈ Rs, charge r) ≤
      bchksHybridZCover128_6400 + bchksHybridCoreSwitchExcess6400 := by
  have hsum := sum_factorCharge_scaled_le Rs degree zDegree charge
    bchksHybridCoreSwitchPerFactorCap6400 hscaled hzMass hyMass
  have hexcess := bchksHybridCoreSwitch_budget6400.2.1
  have hscaledFinal :
      512 * (∑ r ∈ Rs, charge r) ≤
        512 * (bchksHybridZCover128_6400 +
          bchksHybridCoreSwitchExcess6400) := by
    calc
      512 * (∑ r ∈ Rs, charge r) ≤
          512 * bchksHybridLowZCoefficient6400 * bchksHybridZMass6400 +
            bchksHybridYMass6400 *
              bchksHybridCoreSwitchPerFactorCap6400 := hsum
      _ ≤ 512 * bchksHybridZCover128_6400 +
          512 * bchksHybridCoreSwitchExcess6400 := by
        have hzCover := bchksHybrid_componentLedger_exact6400.1
        have hexcess' :
            bchksHybridYMass6400 *
                bchksHybridCoreSwitchPerFactorCap6400 ≤
              512 * bchksHybridCoreSwitchExcess6400 := by
          rw [Nat.mul_comm]
          exact hexcess
        rw [hzCover]
        exact Nat.add_le_add_left
          hexcess'
          (512 * bchksHybridLowZCoefficient6400 *
            bchksHybridZMass6400)
      _ = 512 * (bchksHybridZCover128_6400 +
          bchksHybridCoreSwitchExcess6400) := by ring
  exact le_of_mul_le_mul_left hscaledFinal (by norm_num)
lemma bchksHybridCoreSwitch_codim14_noGo6400 :
    bchksHybridCoreSwitchCodim14Excess6400 =
        (bchksHybridCoreSwitchCodim14PerFactorCap6400 *
            bchksHybridYMass6400 + 511) / 512 ∧
      bchksHybridCoreSwitchCodim14Total6400 =
        bchksHybridTotal128_6400 +
          bchksHybridCoreSwitchCodim14Excess6400 ∧
      bchksWeightedNumerator6400 < bchksHybridCoreSwitchCodim14Total6400 ∧
      bchksHybridCoreSwitchCodim14Total6400 -
          bchksWeightedNumerator6400 = 574516317759 := by
  norm_num [bchksHybridCoreSwitchCodim14Excess6400,
    bchksHybridCoreSwitchCodim14PerFactorCap6400,
    bchksHybridYMass6400, bchksHybridCoreSwitchCodim14Total6400,
    bchksHybridTotal128_6400, bchksWeightedNumerator6400]
end BCHKSHybridCoreSwitchAudit6400
end ProximityPrize.SubmissionLower
