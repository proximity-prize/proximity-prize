import ProximityPrize.SubmissionLower.LocatorBatchProductRoute
import ProximityPrize.SubmissionLower.LocatorGenericHelperFactorSwitch6803

/-!
# Initial A-source bridge for the 68.03 row

The selected gcd has the wide support `(slope,middle,total) =
(34,153,6676)`.  The independent A kernel splits its regular factors into a
direct-helper part and a universal part.  Universal factors inherit the
narrow support `(29,135,6676)`, precisely the ambient on which the retuned
phase receipt operates.
-/

namespace ProximityPrize.SubmissionLower.LocatorFixedBridge6803

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN095 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238
  RCN266 RCN275
open LocatorFactorAggregate LocatorBatchProductRoute

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : GCDMonoid P4 :=
  UniqueFactorizationMonoid.toGCDMonoid P4

/-- Narrow A support used by the retuned ordinary/hybrid provider. -/
def narrowSupport : ResidualSupportParameters :=
  ⟨29, 135, 6676, by decide, by decide, by decide, by decide⟩

/-- Wide support of the selected TCap/B gcd. -/
def wideSupport : ResidualSupportParameters :=
  ⟨34, 153, 6676, by decide, by decide, by decide, by decide⟩

/-- The retuned independent A constraint kernel. -/
abbrev AKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 17773574 131071 130000 29 98
    IRSProfile.domain u0 u1

/-- Exact direct-helper charge for a factor exiting at the A source. -/
def initialAHelperCap (p : FlagDegree) : ℕ :=
  (LocatorGenericHelperFactorSwitch6803.helperPair
    130000 135 29 (middle p) p.all (total p)).regularCountCap

/-- Linear reconstruction of the retuned independent A source. -/
def initialAMap (u0 u1 : I → K) : AKernel u0 u1 →ₗ[K] P4 :=
  kernelReconstructLinear (K := K) 17773574 131071 130000 29 98
    IRSProfile.domain u0 u1

/-- Factors universal on the retuned A source. -/
def initialAUniversalFactors (u0 u1 : I → K) (H : P4) :
    Finset (RegularIndex H) :=
  universalFactors H (Finset.univ : Finset (RegularIndex H))
    (initialAMap u0 u1)

@[simp] theorem mem_initialAUniversalFactors
    (u0 u1 : I → K) (H : P4) (F : RegularIndex H) :
    F ∈ initialAUniversalFactors u0 u1 H ↔
      ∀ v : AKernel u0 u1,
        F.1 ∣ reconstruct K 17773574 131071 130000 29 v.1 := by
  simp only [initialAUniversalFactors, mem_universalFactors,
    Finset.mem_univ, true_and, initialAMap,
    kernelReconstructLinear_apply]

/-- The universal A factors divide every A row jointly. -/
theorem initialAUniversalProduct_dvd
    (u0 u1 : I → K) (H : P4) :
    ∀ v : AKernel u0 u1,
      regularProduct H (initialAUniversalFactors u0 u1 H) ∣
        reconstruct K 17773574 131071 130000 29 v.1 := by
  intro v
  have h := universalProduct_dvd H
    (Finset.univ : Finset (RegularIndex H)) (initialAMap u0 u1) v
  simpa only [initialAUniversalFactors, initialAMap,
    kernelReconstructLinear_apply] using h

/-- The universal A product divides the selected carrier. -/
theorem initialAUniversalProduct_dvd_carrier
    (u0 u1 : I → K) (H : P4) :
    regularProduct H (initialAUniversalFactors u0 u1 H) ∣ H :=
  regularProduct_dvd_carrier H (initialAUniversalFactors u0 u1 H)

end

end ProximityPrize.SubmissionLower.LocatorFixedBridge6803
