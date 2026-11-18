import ProximityPrize.SubmissionLower.LowerGeometry
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.Lower80850.Initial
open scoped BigOperators
open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (Potential rawFlag rawFlag_all rawFlag_middle rawFlag_total
  sumFlag sumFlag_all sumFlag_middle sumFlag_total)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end ProximityPrize.SubmissionLower.Lower80850.Initial
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.SecondJetTotalAvoidance
open MvPolynomial SecondJetSupport SecondJetCoefficients RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {K : Type*} [Field K]

theorem coefficient_total_weight (P : Poly (K := K)) (L j : ℕ)
    (hP : ∀ e ∈ P.support, e 1+e 2+e 3+e 4 ≤ L) :
    wt residualTotalWeights ((asS P).coeff j) ≤ L-j := by
  apply (RCN081.weightedTotalDegree_le_iff _ _ _).mpr
  intro e he
  have hh := hP _ (coefficient_support P j e he)
  obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates j e
  rw [h1,h2,h3,h4] at hh
  simp [residualTotalWeights, RCN081.weight_fin4]
  omega

theorem coefficient_not_dvd (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (L j : ℕ) (hP : ∀ e ∈ P.support, e 1+e 2+e 3+e 4 ≤ L)
    (hF : L < wt residualTotalWeights F) (hC : (asS P).coeff j ≠ 0) :
    ¬ F ∣ (asS P).coeff j := by
  intro hdiv
  have hh := RCN081.weightedTotalDegree_le_of_dvd residualTotalWeights F
    ((asS P).coeff j) hdiv hC
  have hc := coefficient_total_weight P L j hP
  change wt residualTotalWeights F ≤ wt residualTotalWeights ((asS P).coeff j) at hh
  omega

theorem leading_not_dvd (P : Poly (K := K)) (hP : P ≠ 0)
    (F : MvPolynomial (Fin 4) K) (L : ℕ)
    (hPL : ∀ e ∈ P.support, e 1+e 2+e 3+e 4 ≤ L)
    (hF : L < wt residualTotalWeights F) :
    (asS P).leadingCoeff ≠ 0 ∧ ¬ F ∣ (asS P).leadingCoeff := by
  have hn : asS P ≠ 0 := by
    intro hz
    apply hP
    apply (asS (K := K)).injective
    simpa only [map_zero] using hz
  have hc := Polynomial.leadingCoeff_ne_zero.mpr hn
  exact ⟨hc,coefficient_not_dvd P F L (asS P).natDegree hPL hF hc⟩

open SecondJetCoefficientSpecialization SecondJetClearedHelper SecondJetHelperWeights
open SecondJetRelaxedInterpolation SecondJetRelaxedCoefficientsReceipt SecondJetProperAlternatives
variable {N : Type*} [Fintype N]

end
end ProximityPrize.SubmissionLower.SecondJetTotalAvoidance

namespace ProximityPrize.SubmissionLower.SecondJetPairBounds
open RCN260 RCN052 RCN294

end ProximityPrize.SubmissionLower.SecondJetPairBounds

namespace ProximityPrize.SubmissionLower.SecondJetRegularData.Data
open MvPolynomial RCN319 RCN260 RCN327
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]

variable {nodes : I ↪ K} {u0 u1 : I → K}

end
end ProximityPrize.SubmissionLower.SecondJetRegularData.Data

namespace ProximityPrize.SubmissionLower.SecondJetAsymmetric
open scoped Classical
open MvPolynomial RCN135 RCN136 RCN319 RCN327 RCN238 RCN222 RCN234 RCN156
open SecondJetCoefficients
open SecondJetRelaxedInterpolation SecondJetProperAlternatives SecondJetExceptionalComponents
open AsymmetricHelper
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]

variable {nodes : I ↪ K} {u0 u1 : I → K}

end
end ProximityPrize.SubmissionLower.SecondJetAsymmetric

namespace ProximityPrize.SubmissionLower.SecondJetOwnShape
open MvPolynomial RCN130 RCN234 RCN156 RCN095 RCN347 RCN135
noncomputable section
set_option autoImplicit false
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

end
end ProximityPrize.SubmissionLower.SecondJetOwnShape

namespace ProximityPrize.SubmissionLower.SecondJetProfile114
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts SecondJetRelaxedCounts
open SecondJetRelaxedCoefficientsReceipt SecondJetRelaxedInterpolation
open SecondJetNumericGeometry RCN260 RCN294 RCN135
open SecondJetOwnShape
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

end
end ProximityPrize.SubmissionLower.SecondJetProfile114

namespace ProximityPrize.SubmissionLower.SecondJetRefinedCap
open RCN095 RCN260 RCN294 AsymmetricHelper SecondJetNumericGeometry
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end ProximityPrize.SubmissionLower.SecondJetRefinedCap

namespace ProximityPrize.SubmissionLower.SecondJetRefinedCap
open RCN130 RCN234 RCN156 RCN347 SecondJetOwnShape
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

end
end ProximityPrize.SubmissionLower.SecondJetRefinedCap
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.MovingFiberInterpolation6811
open SecondJetDifferentiation
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetSpecialize
open SecondJetRelaxedCoefficientsReceipt SecondJetRelaxedDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
variable {K N : Type*} [Field K] [Fintype N]

end
end ProximityPrize.SubmissionLower.MovingFiberInterpolation6811
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.MovingFiberSingleCore6815
set_option autoImplicit false

end ProximityPrize.SubmissionLower.MovingFiberSingleCore6815

namespace ProximityPrize.SubmissionLower.Lower80899.PhaseRows
set_option autoImplicit false

end ProximityPrize.SubmissionLower.Lower80899.PhaseRows

namespace ProximityPrize.SubmissionLower.Lower80899.LedgerAudit
set_option autoImplicit false

end ProximityPrize.SubmissionLower.Lower80899.LedgerAudit

namespace ProximityPrize.SubmissionLower.Lower80899.CompressedBand
set_option autoImplicit false

end ProximityPrize.SubmissionLower.Lower80899.CompressedBand

namespace ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6814
open LocatorPhase6800Oracle Lower80899.PhaseRows
set_option autoImplicit false

end ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6814
end MergedPart3
section MergedPart4
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.MovingFiberKernels6815
open ProximityPrize.Benchmark RCN100 RCN119 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
namespace A

end A
namespace B

end B
namespace TCap

end TCap
namespace Source00

end Source00
namespace Source01

end Source01
namespace Source02

end Source02
namespace Source03

end Source03
namespace Source04

end Source04
namespace Source05

end Source05
namespace Source06

end Source06
end ProximityPrize.SubmissionLower.MovingFiberKernels6815
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.Lower80899.FactorSwitch

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient

open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end

end ProximityPrize.SubmissionLower.Lower80899.FactorSwitch

namespace ProximityPrize.SubmissionLower.Lower80899.PowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient
open LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact
open Lower80899.FactorSwitch

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end

end ProximityPrize.SubmissionLower.Lower80899.PowerRoute

namespace ProximityPrize.SubmissionLower.Lower80899.BatchPowerRoute

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open LocatorLowQuotient LocatorCoprimeQuotient LocatorArbitraryPowerAvoidance LocatorArbitraryPowerContact Lower80899.FactorSwitch Lower80899.PowerRoute LocatorBatchProductRoute

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end

end ProximityPrize.SubmissionLower.Lower80899.BatchPowerRoute

namespace ProximityPrize.SubmissionLower.Lower80899.Oracle
open RCN095 LocatorFactorAggregate LocatorLowQuotient LocatorArbitraryPowerAvoidance
open Lower80899.PowerRoute Lower80899.FactorSwitch
open LocatorPhase6800Oracle (Potential rawFlag sumFlag RawBelow RawStrictSlopeBelow)
set_option autoImplicit false
set_option maxRecDepth 100000

end ProximityPrize.SubmissionLower.Lower80899.Oracle

namespace ProximityPrize.SubmissionLower.Lower80899.BatchPhase

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266
open LocatorFactorAggregate LocatorArbitraryPowerAvoidance LocatorBatchProductRoute Lower80899.BatchPowerRoute Lower80899.FactorSwitch Lower80899.Oracle

open LocatorPhase6800Oracle (Potential sumFlag sumFlag_all sumFlag_middle sumFlag_total RawBelow RawStrictSlopeBelow)
open LocatorBatchPhase6800 (regularAggregateFlag regularAggregateFlag_all
  regularAggregateFlag_middle regularAggregateFlag_total regularAggregateFlag_mono
  regularAggregateFlag_all_lt_of_ssubset regularAggregateFlag_raw_mono sum_phasePotential_eval)

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end

end ProximityPrize.SubmissionLower.Lower80899.BatchPhase
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.MovingFiberPaddedIdentity6815

open RCN095
open Lower80788.FixedStage

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

end ProximityPrize.SubmissionLower.MovingFiberPaddedIdentity6815
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.MovingFiberOrdinaryLow6815
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN174 RCN159 RCN086 RCN095 RCN275 RCN198 RCN263 RCN087 RCN203 RCN084 RCN313 RCN074 RCN335
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end

end ProximityPrize.SubmissionLower.MovingFiberOrdinaryLow6815
end MergedPart7
