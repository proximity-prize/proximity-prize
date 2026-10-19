/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ArkLib.ProofSystem.ToyProblem.Codegen
import ArkLib.ProofSystem.ToyProblem.Leaderboard
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.UniqueDecoding
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import CompPoly.Univariate.NTT.KoalaBear
import ProximityPrize.Benchmark.CodeBridge

/-!
# The interleaved-RS challenge profile

This file owns the concrete downstream choices which intentionally do not live
in ArkLib: the field, smooth evaluation domain, code dimensions, repetition
count, and the public argument-size estimate.
-/

namespace ProximityPrize.Benchmark.IRSProfile

open Code ToyProblem ToyProblem.Impl.IRS
open scoped NNReal

abbrev Field := _root_.KoalaBear.Ext6
abbrev Index := Fin (2 ^ 18)

def totalDimension : Nat := 2 ^ 20
def interleaving : Nat := 8
def baseDimension : Nat := 2 ^ 17
def domainSize : Nat := 2 ^ 18
def repetitions : Nat := 128

theorem interleaving_dvd_totalDimension : interleaving ∣ totalDimension := by
  norm_num [interleaving, totalDimension]

theorem totalDimension_div_interleaving :
    totalDimension / interleaving = baseDimension := by
  norm_num [totalDimension, interleaving, baseDimension]

local instance : NeZero interleaving := ⟨by norm_num [interleaving]⟩
local instance : NeZero baseDimension := ⟨by norm_num [baseDimension]⟩

/-- The size-`2^18` KoalaBear multiplicative NTT domain. -/
def baseNttDomain : CompPoly.CPolynomial.NTT.Domain _root_.KoalaBear.Field :=
  CompPoly.CPolynomial.NTT.KoalaBear.domainOfLogN 18 (by
    norm_num [_root_.KoalaBear.twoAdicity])

/-- The smooth base-field domain, embedded coefficient-wise in the sextic field. -/
def domain : Index ↪ Field where
  toFun i := CompPoly.Extension.Ext.ofBase (baseNttDomain.node i)
  inj' := by
    intro i j hij
    apply Fin.ext
    have hcoeff := congrArg
      (fun x : Field => CompPoly.Extension.Ext.coeff x (0 : Fin 6)) hij
    change baseNttDomain.node i = baseNttDomain.node j at hcoeff
    exact baseNttDomain.primitive.pow_inj i.isLt j.isLt hcoeff

def encoder :
    (Fin totalDimension → Field) →ₗ[Field]
      (Index → Fin interleaving → Field) :=
  ToyProblem.Impl.IRS.encoder totalDimension interleaving
    interleaving_dvd_totalDimension domain

noncomputable def code : ModuleCode Index Field (Fin interleaving → Field) :=
  ReedSolomon.Interleaved.irsCode domain totalDimension interleaving

noncomputable def baseCode : ModuleCode Index Field Field :=
  ReedSolomon.code domain baseDimension

theorem encoder_injective : Function.Injective encoder := by
  exact ToyProblem.Impl.IRS.encoder_injective totalDimension interleaving
    interleaving_dvd_totalDimension domain (by
      norm_num [totalDimension, interleaving, domainSize])

theorem encoder_range : Set.range encoder = (code : Set _) := by
  exact ToyProblem.Impl.IRS.encoder_range totalDimension interleaving
    interleaving_dvd_totalDimension domain

theorem dimension : Module.finrank Field code = totalDimension := by
  exact ReedSolomon.Interleaved.dim_irsCode_of_dvd domain totalDimension
    interleaving interleaving_dvd_totalDimension (by
      norm_num [totalDimension, interleaving, domainSize])

theorem alphabetRate : (LinearCode.alphabetRate code : ℝ) = 1 / 2 := by
  unfold code
  rw [ReedSolomon.Interleaved.alphabetRate_irsCode domain totalDimension
    interleaving (by norm_num [totalDimension, interleaving, domainSize]),
    totalDimension_div_interleaving]
  norm_num [baseDimension]

set_option maxRecDepth 20000 in
theorem minDistance :
    Code.minDist (code : Set (Index → Fin interleaving → Field)) = 131073 := by
  unfold code
  rw [ReedSolomon.Interleaved.minDist_irsCode domain totalDimension interleaving
    (by norm_num [totalDimension, interleaving, domainSize])]
  norm_num [totalDimension, interleaving]

set_option maxRecDepth 20000 in
theorem baseMinDistance :
    Code.minDist (baseCode : Set (Index → Field)) = 131073 := by
  unfold baseCode
  rw [ReedSolomon.minDist_eq_card_sub_min_add_1]
  norm_num [baseDimension]

/-- The exact relative-distance value shared by the base and interleaved codes. -/
noncomputable def minRelativeDistance : ℝ≥0 := (131073 : ℝ≥0) / 262144

theorem card_index : Fintype.card Index = 262144 := by
  norm_num [Index]

theorem base_minRelativeDistance :
    (Code.minRelHammingDistCode (baseCode : Set (Index → Field)) : ℝ≥0) =
      minRelativeDistance := by
  rw [CodeBridge.minRelHammingDistCode_eq_div _ baseMinDistance card_index]
  norm_num [minRelativeDistance]

theorem minRelativeDistance_eq :
    (Code.minRelHammingDistCode
      (code : Set (Index → Fin interleaving → Field)) : ℝ≥0) =
      minRelativeDistance := by
  rw [CodeBridge.minRelHammingDistCode_eq_div _ minDistance card_index]
  norm_num [minRelativeDistance]

/-- ArkLib's stable fixed-radius façade for this exact protocol profile. -/
noncomputable def parameters :
    ToyProblem.FixedRadiusParameters (ι := Index) (F := Field)
      (A := Fin interleaving → Field) where
  k := totalDimension
  t := repetitions
  code := code
  encoder := encoder
  encoder_injective := encoder_injective
  encoder_range := encoder_range

def merkleOpeningEstimateBits : Nat :=
  repetitions * (256 * 18 + 62 * interleaving)

theorem merkleOpeningEstimateBits_eq : merkleOpeningEstimateBits = 653312 := by
  norm_num [merkleOpeningEstimateBits, repetitions, interleaving]

def merkleOpeningEstimateBytes : Nat := merkleOpeningEstimateBits / 8

theorem merkleOpeningEstimateBytes_eq : merkleOpeningEstimateBytes = 81664 := by
  norm_num [merkleOpeningEstimateBytes, merkleOpeningEstimateBits,
    repetitions, interleaving]

end ProximityPrize.Benchmark.IRSProfile
