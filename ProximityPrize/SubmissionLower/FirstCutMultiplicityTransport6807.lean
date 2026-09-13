import ProximityPrize.SubmissionLower.GenericSlicePoints6807
/-
UNCOMPILED. Reuses the frozen original-DVR multiplier argument.
It proves an order LOWER BOUND. It does not claim that arbitrary field
extension preserves the original DVR order exactly.
-/
import ProximityPrize.SubmissionLower.LowerFoundation

namespace ProximityPrize.SubmissionLower.FirstCutMultiplicityTransport6807
open RCN244 RCN135 RCN095 RCN074 RCN218 RCN186 RCN310 RCN313 RCN086 RCN217 RCN248
noncomputable section
set_option autoImplicit false
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

theorem normalized_first_mem_power {B : Type*} [CommRing B]
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (C : FirstTailComponent S) (f : MvPolynomial (Fin 4) K →+* B)
    (J : Ideal B) [J.IsMaximal]
    (hfactor : f (originalData S C).factor = 0)
    (hcontract : Ideal.comap f J = componentPrime S C)
    (tail scalar normalized multiplier : B)
    (htail : tail = f (numerator K S.F (RCN326.w+1))*scalar)
    (hnormalized : tail = multiplier*normalized)
    (hunit : IsUnit multiplier) :
    normalized ∈ J^localMultiplicity S (canonicalLocalDVRFamily S hproper) C := by
  have htailmem := proper_global_tail_mem_projected_primary S hproper C f
    (0 : B) tail scalar J (by simp [hfactor]) (J.zero_mem) hcontract htail
  have ht : tail ∈ J^localMultiplicity S (canonicalLocalDVRFamily S hproper) C := by
    simpa using htailmem
  rw [hnormalized] at ht
  obtain ⟨u,hu⟩ := hunit
  rw [← hu] at ht
  have hh := (J^localMultiplicity S (canonicalLocalDVRFamily S hproper) C).mul_mem_left
    (↑(u⁻¹) : B) ht
  simpa only [← mul_assoc,Units.inv_mul,mul_one,one_mul] using hh

end
end ProximityPrize.SubmissionLower.FirstCutMultiplicityTransport6807
