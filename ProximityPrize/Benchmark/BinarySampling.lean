/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import CompPoly.Fields.Binary.BF64.Ext3
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Executable uniform sampling for the binary challenge field

CompPoly supplies the executable base-field bit representation and extension
coefficient maps. VCVio transports a uniform sample through these equivalences.
Sampling uses three independent 64-bit limbs and never enumerates the field.
This adapter follows `ArkLib.Data.Probability.KoalaBear` and can move to ArkLib's
probability layer when upstreamed.
-/

namespace ProximityPrize.Benchmark.BinarySampling

open OracleComp

/-- Uniform base-field sampling through CompPoly's polynomial-basis word map. -/
@[reducible] def baseSampleableType : SampleableType BF64 :=
  SampleableType.ofEquiv BF64.equivFin.symm

instance instSampleableTypeBF64 : SampleableType BF64 := baseSampleableType

/-- The executable coefficient representation, in `c0`, `c1`, `c2` order. -/
def coeffsEquiv : Vector BF64 3 ≃ BF64.Ext3 where
  toFun v := CompPoly.Extension.Ext.ofVector (P := BF64.ext3Params) v
  invFun x := CompPoly.Extension.Ext.coeffs (P := BF64.ext3Params) x
  left_inv _ := rfl
  right_inv _ := rfl

/-- Draw three independent uniform base-field coefficients. -/
def sample : ProbComp BF64.Ext3 :=
  coeffsEquiv <$> ($ᵗ (Vector BF64 3))

/-- The pinned executable sampler for the 192-bit challenge field. -/
@[reducible] def sampleableType : SampleableType BF64.Ext3 :=
  SampleableType.ofEquiv coeffsEquiv

instance instSampleableTypeExt3 : SampleableType BF64.Ext3 := sampleableType

/-- Canonical challenge sampling uses exactly the three-limb program. -/
theorem uniformSample_eq_sample : ($ᵗ BF64.Ext3) = sample := rfl

/-- The executable sampler has the uniform measure on the entire field. -/
theorem evalDist_sample [MeasurableSpace BF64.Ext3]
    [MeasurableSingletonClass BF64.Ext3] :
    𝒟[sample] = ProbabilityTheory.uniformOn Set.univ := by
  rw [← uniformSample_eq_sample]
  exact SampleableType.evalDist_uniformSample

end ProximityPrize.Benchmark.BinarySampling
