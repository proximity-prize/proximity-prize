/-
Copyright (c) 2026 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_Valuation_RankOne

/-!
Permitted flat proof port of Mathlib.RingTheory.Valuation.Discrete.RankOne.
Model label: gpt-5.
Original Mathlib revision: 905b95818eb32af7874a58b427f50c1711a5e96c.
Original source SHA256: e1243632544534b53bec77c2db8f75adbba456269cd06f7d961c7447f81cb0c7.
Original copyright and author notices are retained above.
Modifications: module/public visibility packaging is removed; imports
are replaced by the trusted target and the necessary flat proof ports.
All mathematical declarations and proof bodies are retained, except
any explicitly documented ordinary-term expansion below.
The full Apache 2.0 license is in LocalMathlibPortLicense.lean.
-/

/-!
# Discrete valuations have rank one

## Main Definitions and Results
* `Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt` : the order-preserving isomorphism
  between the `ValueGroup₀` of a discrete valuation and `ℤᵐ⁰`.
* `Valuation.IsRankOneDiscrete.rankOne` : a discrete valuation has rank one.

## Tags
valuation, discrete, rank one
-/

section ProximityFlatProofPort

namespace Valuation.IsRankOneDiscrete

open WithZero MonoidWithZeroHom NNReal WithZeroMulInt

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

section Ring

variable {R : Type*} [Ring R]

section LinearOrderedCommGroupWithZero

variable (v : Valuation R Γ) [hv : v.IsRankOneDiscrete]

/-- An order-preserving isomorphism between the `ValueGroup₀` of a discrete valuation and `ℤᵐ⁰`.
TODO: rename this into lowerCamelCase. -/
@[simps!]
noncomputable def valueGroup₀_equiv_withZeroMulInt : ValueGroup₀ (.ofClass v) ≃*o ℤᵐ⁰ where
  __ := MulEquiv.withZero (intEquivOfZPowersEqTop _
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)).symm
  map_le_map_iff' {x y} := by
    rw [(WithZero.map'_strictMono (MulEquiv.strictMono_symm (mulintEquivOfZPowersEqTop_strictMono
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)
    (Left.one_lt_inv_iff.mpr hv.generator'_lt_one)))).le_iff_le]

lemma valueGroup₀_equiv_withZeroMulInt_apply_zero :
    valueGroup₀_equiv_withZeroMulInt v 0 = 0 := by simp

lemma valueGroup₀_equiv_withZeroMulInt_apply_zpow (k : ℤ) :
    valueGroup₀_equiv_withZeroMulInt v (hv.generator' ^ k) = WithZero.exp (- k) := by
  simp only [map_zpow₀, valueGroup₀_equiv_withZeroMulInt_apply, WithZero.map'_coe,
    MonoidHom.coe_coe]
  rw [← WithZero.coe_zpow, WithZero.exp, WithZero.coe_inj, ← map_zpow]
  simp [← mulintEquivOfZPowersEqTop_symm_apply_zpow
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)]

lemma valueGroup₀_equiv_withZeroMulInt_strictMono :
    StrictMono (valueGroup₀_equiv_withZeroMulInt v) := by
  intro x y hxy
  rwa [(WithZero.map'_strictMono (MulEquiv.strictMono_symm (mulintEquivOfZPowersEqTop_strictMono
    (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top)
    (Left.one_lt_inv_iff.mpr hv.generator'_lt_one)))).lt_iff_lt]

/-- A discrete valuation has rank one. -/
@[implicit_reducible]
noncomputable def rankOne {e : ℝ≥0} (he : 1 < e) : v.RankOne where
  hom' := (toNNReal (ne_of_gt (lt_trans zero_lt_one he))).comp
      (.ofClass (valueGroup₀_equiv_withZeroMulInt v))
  strictMono' := (toNNReal_strictMono he).comp (valueGroup₀_equiv_withZeroMulInt_strictMono v)
  exists_val_nontrivial := IsNontrivial.exists_val_nontrivial

end LinearOrderedCommGroupWithZero

section WithZeroMulInt

variable {v : Valuation R ℤᵐ⁰} [hv : v.IsRankOneDiscrete]

lemma valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (hsurj : Function.Surjective v)
    (x : R) : (valueGroup₀_equiv_withZeroMulInt v) (v.restrict x) = v x := by
  simp only [Valuation.restrict_def, ValueGroup₀.restrict₀_apply,
    valueGroup₀_equiv_withZeroMulInt_apply]
  split_ifs with h0 <;>
  simp only [MonoidWithZeroHom.coe_ofClass] at h0
  · simp [h0]
  · simp only [WithZero.map'_coe, MonoidHom.coe_coe]
    conv_rhs => rw [← coe_unzero h0]
    rw [WithZero.coe_inj, ← (MulEquiv.injective (intEquivOfZPowersEqTop _
      (Subgroup.zpowers_inv (g := hv.generator') ▸ hv.generator'_zpowers_eq_top))).eq_iff,
      MulEquiv.apply_symm_apply]
    ext
    simp only [Units.val_mk0, intEquivOfZPowersEqTop_apply, inv_zpow', generator',
      SubgroupClass.coe_zpow]
    have hg : hv.generator = Units.mk0 (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) (by simp) :=
      generator_eq_exp_neg_one_of_surjective hsurj
    rw [hg]
    conv_lhs => rw [MonoidWithZeroHom.coe_ofClass, ← coe_unzero h0]
    simp only [coe_unzero, Int.reduceNeg, exp_neg, zpow_neg, Units.val_inv_eq_inv_val,
      Units.val_zpow_eq_zpow_val, Units.val_mk0, inv_zpow', ← exp_zsmul, Int.zsmul_eq_mul, mul_one,
      inv_inv]
    simp [WithZero.exp]

end WithZeroMulInt

end Ring

end Valuation.IsRankOneDiscrete
