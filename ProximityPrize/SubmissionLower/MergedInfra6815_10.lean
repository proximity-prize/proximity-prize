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

theorem count_le_left_cap {K : Type} [Field K]
    (P : UnequalParameters) (F : MvPolynomial (Fin 4) K)
    (hY : F.degreeOf 1 ≤ P.leftY) (hR : F.degreeOf 2 ≤ P.leftR)
    (hZ : F.degreeOf 3 ≤ P.leftZ) (count : ℕ) (hgap : 0 < P.gap)
    (hc : count*P.gap ≤ (P.n-P.w)*dot P.leftAgreement (regularVector P F)+
      (P.errors+1)*P.gap*(regularVector P F).z) :
    count ≤ AsymmetricHelper.leftRegularCountCap P := by
  have hv := LocatorCoprimeQuotient.regularVector_le_mixedCost P F hY hR hZ
  have hdot : dot P.leftAgreement (regularVector P F) ≤ dot P.leftAgreement P.mixedCost :=
    Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left P.leftAgreement.y hv.1)
        (Nat.mul_le_mul_left P.leftAgreement.r hv.2.1))
      (Nat.mul_le_mul_left P.leftAgreement.z hv.2.2)
  apply (Nat.le_div_iff_mul_le hgap).mpr
  exact hc.trans (Nat.add_le_add (Nat.mul_le_mul_left (P.n-P.w) hdot)
    (Nat.mul_le_mul_left ((P.errors+1)*P.gap) hv.2.2))

end ProximityPrize.SubmissionLower.SecondJetPairBounds

namespace ProximityPrize.SubmissionLower.SecondJetRegularData.Data
open MvPolynomial RCN319 RCN260 RCN327
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
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
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
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
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433

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

def cutoff (m k n0 h : ℕ) : ℕ := m*181265-SecondJetRelaxedDifferentiation.reserve k n0 h*50196

def Interpolant (m B s U L k n0 : ℕ) (nodes : N ↪ K) (u0 u1 : N → K)
    (P : Poly (K := K)) : Prop :=
  P ≠ 0 ∧
  (∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1 ≤ s ∧ e 1+e 2+e 3 ≤ U ∧
    e 1+e 2+e 3+e 4 ≤ L ∧
    e 0+131071*e 2+131070*e 3+131069*e 1 < cutoff m k n0 (e 1)) ∧
  (∀ i, MvPolynomial.X 0^m ∣ substitute (K := K)
    (localize (nodes i) (u0 i) (u1 i) P)) ∧
  ∀ d ≤ k, ∀ f : Polynomial K, f.natDegree ≤ 131071 → ∀ z : K, ∀ S : Finset N,
    181265 ≤ S.card → (∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z) →
      specialize f z ((pderiv 1)^[d] P) = 0

theorem exists_of_dimension (m B s U L k n0 : ℕ) (hsB : 2*s ≤ B) (hkm : k < m)
    (hN : Fintype.card N = 262144) (nodes : N ↪ K) (u0 u1 : N → K)
    (hcard : 262144*SecondJetRelaxedGlobalMap.rankBound m L B s U
        (fun h => (cutoff m k n0 h+B-1)/131071) <
      Fintype.card (SecondJetRelaxedGlobalIndex.Index (cutoff m k n0) 131071 L B s U)) :
    ∃ P, Interpolant m B s U L k n0 nodes u0 u1 P := by
  obtain ⟨P,hP,hbounds,hcontact⟩ := SecondJetRelaxedGlobalIndex.exists_weighted_global_contact
    (cutoff m k n0) 131071 L B s U m hsB (by decide) nodes u0 u1 (by simpa only [hN] using hcard)
  have hc : ∀ i, MvPolynomial.X 0^m ∣ substitute (K := K)
      (localize (nodes i) (u0 i) (u1 i) P) := fun i =>
    SecondJetGlobalDifferentiation.nested_to_flat_contact _ m (hcontact i)
  refine ⟨P,hP,hbounds,hc,?_⟩
  intro d hd f hf z S hS hvalues
  apply derivative_vanish P m 181265 131071 k n0 d (by decide) (by decide)
    (by omega) hd ?_ nodes u0 u1 hc f hf z S hS hvalues
  intro e he
  have hb := (hbounds e he).2.2.2.2
  dsimp [cutoff] at hb
  norm_num
  omega

end
end ProximityPrize.SubmissionLower.MovingFiberInterpolation6811
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.MovingFiberSingleCore6815
set_option autoImplicit false

structure Carrier where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  deriving DecidableEq, Repr

structure Run where
  stop : ℕ
  who : ℕ
  deriving DecidableEq, Repr

end ProximityPrize.SubmissionLower.MovingFiberSingleCore6815

namespace ProximityPrize.SubmissionLower.Lower80899.PhaseRows
set_option autoImplicit false

structure PhaseRun where
  stop : ℕ
  witness : ℕ
  deriving DecidableEq, Repr

end ProximityPrize.SubmissionLower.Lower80899.PhaseRows

namespace ProximityPrize.SubmissionLower.Lower80899.LedgerAudit
set_option autoImplicit false

structure LedgerRun where
  stop : ℕ
  witness : ℕ
  mode : ℕ
  deriving DecidableEq, Repr

end ProximityPrize.SubmissionLower.Lower80899.LedgerAudit

namespace ProximityPrize.SubmissionLower.Lower80899.CompressedBand
set_option autoImplicit false

structure Run where
  stop : ℕ
  code : ℕ
  deriving DecidableEq, Repr

end ProximityPrize.SubmissionLower.Lower80899.CompressedBand

namespace ProximityPrize.SubmissionLower.MovingFiberReceiptTypes6814
open LocatorPhase6800Oracle Lower80899.PhaseRows
set_option autoImplicit false

structure BaseRun where
  stop : Nat
  sheet : Nat
  deriving DecidableEq, Repr

structure Numbers where
  carrier : MovingFiberSingleCore6815.Carrier
  base : BaseRow
  threshold : Array Nat
  prefixValues : Array Nat
  singletons : List MovingFiberSingleCore6815.Run
  baseChoices : List BaseRun
  phaseRuns : Array (List PhaseRun)
  ledgerRuns : List Lower80899.LedgerAudit.LedgerRun
  thresholdRuns : Array (List Lower80899.CompressedBand.Run)

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
theorem coefficient_exact : coefficientCount 23924340 131071 76330 39=5372513324094290 := by
  rw [show 23924340=182*131071+69418 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 182 69418 131071 76330 39
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 132 76330 39=20494511840 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
end A
namespace B
theorem coefficient_exact : coefficientCount 30086670 131071 15421 50=2165386041082735 := by
  rw [show 30086670=229*131071+71411 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 229 71411 131071 15421 50
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 166 15421 50=8260292112 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
end B
namespace TCap
theorem coefficient_exact : coefficientCount 45673740 131071 11193 78=5528547372439440 := by
  rw [show 45673740=348*131071+61032 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 348 61032 131071 11193 78
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 252 11193 78=21089734219 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 45673740 131071 11193 78-262144*localRankBound 252 11193 78=85333904 := by
  norm_num only [coefficient_exact,rank_exact]
theorem quotient_count_exact : coefficientCount 45673740 131071 0 78=45673740 := by decide +kernel
theorem quotient_count_lt : coefficientCount 45673740 131071 0 78<85333904 := by rw [quotient_count_exact]; decide +kernel
end TCap
namespace Source00
theorem coefficient_exact : coefficientCount 11599498755 131071 3840000 19840=30707103195602755936705787 := by
  rw [show 11599498755=88497*131071+108468 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 88497 108468 131071 3840000 19840
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 63999 3840000 19840=116780376202356671680 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 11599498755 131071 3840000 19840-262144*localRankBound 63999 3840000 19840=93828256412168595823867 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 93828256412168595823867≤coefficientCount 11599498755 131071 3840000 19840-262144*localRankBound 63999 3840000 19840 := by rw [nullity_exact]
theorem shape : 11599498755+19840≤131071*(88497+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    93828256412168595823867≤Module.finrank IRSProfile.Field (ConstraintKernel (K:=IRSProfile.Field) 11599498755 131071 3840000 19840 63999 IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric 11599498755 3840000 19840 63999 93828256412168595823867 u0 u1 nullity_lower
end Source00
namespace Source01
theorem coefficient_exact : coefficientCount 5799840000 131071 3200000 9888=3203068458886446493984520 := by
  rw [show 5799840000=44249*131071+79321 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44249 79321 131071 3200000 9888
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 32000 3200000 9888=12172764924613929328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 5799840000 131071 3200000 9888-262144*localRankBound 32000 3200000 9888=12051170488452604225288 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 12051170488452604225288≤coefficientCount 5799840000 131071 3200000 9888-262144*localRankBound 32000 3200000 9888 := by rw [nullity_exact]
theorem shape : 5799840000+9888≤131071*(44249+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    12051170488452604225288≤Module.finrank IRSProfile.Field (ConstraintKernel (K:=IRSProfile.Field) 5799840000 131071 3200000 9888 32000 IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric 5799840000 3200000 9888 32000 12051170488452604225288 u0 u1 nullity_lower
end Source01
namespace Source02
theorem coefficient_exact : coefficientCount 5799840000 131071 2880000 9888=2880973021201531445984520 := by
  rw [show 5799840000=44249*131071+79321 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44249 79321 131071 2880000 9888
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 32000 2880000 9888=10950008283031849328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 5799840000 131071 2880000 9888-262144*localRankBound 32000 2880000 9888=10494049854430335745288 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 10494049854430335745288≤coefficientCount 5799840000 131071 2880000 9888-262144*localRankBound 32000 2880000 9888 := by rw [nullity_exact]
theorem shape : 5799840000+9888≤131071*(44249+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    10494049854430335745288≤Module.finrank IRSProfile.Field (ConstraintKernel (K:=IRSProfile.Field) 5799840000 131071 2880000 9888 32000 IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric 5799840000 2880000 9888 32000 10494049854430335745288 u0 u1 nullity_lower
end Source02
namespace Source03
theorem coefficient_exact : coefficientCount 2899920000 131071 1062000 4940=132437019288815010683775 := by
  rw [show 2899920000=22124*131071+105196 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 22124 105196 131071 1062000 4940
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 16000 1062000 4940=503593395806461590 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 2899920000 131071 1062000 4940-262144*localRankBound 16000 1062000 4940=423032138525943634815 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 423032138525943634815≤coefficientCount 2899920000 131071 1062000 4940-262144*localRankBound 16000 1062000 4940 := by rw [nullity_exact]
theorem shape : 2899920000+4940≤131071*(22124+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    423032138525943634815≤Module.finrank IRSProfile.Field (ConstraintKernel (K:=IRSProfile.Field) 2899920000 131071 1062000 4940 16000 IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric 2899920000 1062000 4940 16000 423032138525943634815 u0 u1 nullity_lower
end Source03
namespace Source04
theorem coefficient_exact : coefficientCount 1449960000 131071 531000 2470=8279436385594675048202 := by
  rw [show 1449960000=11062*131071+52598 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 11062 52598 131071 531000 2470
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 8000 531000 2470=31483869872329770 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 1449960000 131071 531000 2470-262144*localRankBound 8000 531000 2470=26128801782659821322 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 26128801782659821322≤coefficientCount 1449960000 131071 531000 2470-262144*localRankBound 8000 531000 2470 := by rw [nullity_exact]
theorem shape : 1449960000+2470≤131071*(11062+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    26128801782659821322≤Module.finrank IRSProfile.Field (ConstraintKernel (K:=IRSProfile.Field) 1449960000 131071 531000 2470 8000 IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric 1449960000 531000 2470 8000 26128801782659821322 u0 u1 nullity_lower
end Source04
namespace Source05
theorem coefficient_exact : coefficientCount 181245000 131071 88902 308=2717882477285942235 := by
  rw [show 181245000=1382*131071+104878 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 1382 104878 131071 88902 308
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 1000 88902 308=10336494078526 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 181245000 131071 88902 308-262144*localRankBound 1000 88902 308=8232573564822491 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 8232573564822491≤coefficientCount 181245000 131071 88902 308-262144*localRankBound 1000 88902 308 := by rw [nullity_exact]
theorem shape : 181245000+308≤131071*(1382+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    8232573564822491≤Module.finrank IRSProfile.Field (ConstraintKernel (K:=IRSProfile.Field) 181245000 131071 88902 308 1000 IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric 181245000 88902 308 1000 8232573564822491 u0 u1 nullity_lower
end Source05
namespace Source06
theorem coefficient_exact : coefficientCount 2537430000 131071 3640000 4267=303020312516603787210897 := by
  rw [show 2537430000=19359*131071+26511 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 19359 26511 131071 3640000 4267
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 14000 3640000 4267=1150877542707512224 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 2537430000 131071 3640000 4267-262144*localRankBound 14000 3640000 4267=1324669961085702762641 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 1324669961085702762641≤coefficientCount 2537430000 131071 3640000 4267-262144*localRankBound 14000 3640000 4267 := by rw [nullity_exact]
theorem shape : 2537430000+4267≤131071*(19359+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1324669961085702762641≤Module.finrank IRSProfile.Field (ConstraintKernel (K:=IRSProfile.Field) 2537430000 131071 3640000 4267 14000 IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric 2537430000 3640000 4267 14000 1324669961085702762641 u0 u1 nullity_lower
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

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

def helperPair (L YS S leftY leftR leftZ : ℕ) : UnequalParameters :=
  ⟨262144, 131071, 181245, leftY, leftR, leftZ, YS, S, L⟩

def HelperPairGates (L YS S leftY leftR leftZ : ℕ) : Prop :=
  let P := helperPair L YS S leftY leftR leftZ
  1 ≤ P.leftR ∧ P.leftY < 2130706433 ∧ P.leftR < 2130706433 ∧
    P.leftZ < 2130706433 ∧ P.mixedCost.y < 2130706433 ∧
    P.mixedCost.r < 2130706433 ∧ P.mixedCost.z < 2130706433

private theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  omega

private theorem degreeR_le_sWeight (Q : P4) :
    Q.degreeOf (2 : Fin 4) ≤ wt residualSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
    wt residualSWeights Q at h
  omega

private theorem degreeZ_le_totalWeight (Q : P4) :
    Q.degreeOf (3 : Fin 4) ≤ wt residualTotalWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  omega

theorem divisor_or_helper_count
    (D L S m YS : ℕ) (hD : 0 < D) (hDa : D ≤ m * 181245)
    (hshape : D + S ≤ 131071 * (YS + 1))
    {u0 u1 : I → K} {H : P4}
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181245 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899)
    (F : RegularIndex H) (leftY leftR leftZ : ℕ)
    (hFY : F.1.degreeOf 1 ≤ leftY)
    (hFR : F.1.degreeOf 2 ≤ leftR)
    (hFZ : F.1.degreeOf 3 ≤ leftZ)
    (hgates : HelperPairGates L YS S leftY leftR leftZ) :
    (∀ v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K D 131071 L S v.1) ∨
      (regularSeeds H selected Gamma F).card ≤
        AsymmetricHelper.leftRegularCountCap (helperPair L YS S leftY leftR leftZ) := by
  classical
  by_cases hdiv : ∀ v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K D 131071 L S v.1
  · exact Or.inl hdiv
  · right
    push Not at hdiv
    obtain ⟨v, hv⟩ := hdiv
    let Q := reconstruct K D 131071 L S v.1
    have hF := RCN167.positiveRFactors_spec H F.1 F.2
    have hrel : IsRelPrime F.1 Q :=
      hF.1.isRelPrime_iff_not_dvd.mpr hv
    have hQbox : Q ∈ globalCoefficientBox K D 131071 L S :=
      reconstruct_mem_globalCoefficientBox K D 131071 L S v.1
    have hQYS : wt residualYSWeights Q ≤ YS := by
      apply flag_box_ys_bound D 131071 L S YS (by decide) hshape Q hQbox
    have hweights := (mem_flagGlobalCoefficientBox_iff Q
      D 131071 L S hD).mp hQbox
    have hQY : Q.degreeOf 1 ≤ YS :=
      (degreeY_le_ysWeight Q).trans hQYS
    have hQR : Q.degreeOf 2 ≤ S :=
      (degreeR_le_sWeight Q).trans hweights.2.1
    have hQZ : Q.degreeOf 3 ≤ L :=
      (degreeZ_le_totalWeight Q).trans hweights.1
    obtain ⟨hleftR, hleftYSmall, hleftRSmall, hleftZSmall,
      hmixedYSmall, hmixedRSmall, hmixedZSmall⟩ := hgates
    apply AsymmetricHelper.regularSeeds_count_le_left_intersection
      (helperPair L YS S leftY leftR leftZ) H Q F hrel 2130706433
      hFY hFR hFZ hQY hQR hQZ
      hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall
      selected Gamma (Finset.univ : Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by
        change (Finset.univ : Finset I).card = 262144
        rw [Finset.card_univ]
        exact Fintype.card_fin _)
      (by norm_num [helperPair]) (by norm_num [helperPair])
      (by norm_num [helperPair]) (by norm_num [helperPair])
      (by simpa only [helperPair] using hdegree)
      (by simpa only [helperPair] using hagreement)
      (by simpa only [helperPair, UnequalParameters.errors, (show (262144 - 181245 : ℕ) = 80899 by decide +kernel)] using hno)
    intro gamma hgamma
    dsimp only [Q]
    apply specialization_eq_zero_of_mem_ker K
      D 131071 L S m IRSProfile.domain u0 u1
      v.1 v.2 (selected gamma) gamma
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i))
    · exact hD
    · exact hdegree gamma (Finset.mem_filter.mp hgamma).1
    · exact hDa.trans (Nat.mul_le_mul_left m
        (hagreement gamma (Finset.mem_filter.mp hgamma).1))
    · intro i hi
      exact (Finset.mem_filter.mp hi).2

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

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

structure PowerRouteBox where
  tLo : ℕ
  tHi : ℕ
  yLo : ℕ
  yHi : ℕ
  rLo : ℕ
  rHi : ℕ
  deriving DecidableEq

def stagePair (L YS S : ℕ) (b : PowerRouteBox) (j : ℕ) :
    UnequalParameters :=
  helperPair (L - j * b.tLo) (YS - j * b.yLo) (S - j * b.rLo)
    b.yHi b.rHi b.tHi

def stageCost (L YS S : ℕ) (b : PowerRouteBox) (j : ℕ) : ℕ :=
  AsymmetricHelper.leftRegularCountCap (stagePair L YS S b j)

private theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  omega

private theorem degreeR_le_sWeight (Q : P4) :
    Q.degreeOf (2 : Fin 4) ≤ wt residualSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
    wt residualSWeights Q at h
  omega

private theorem degreeZ_le_totalWeight (Q : P4) :
    Q.degreeOf (3 : Fin 4) ≤ wt residualTotalWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  omega

theorem regularSeeds_count_le_stageCost
    (L YS S : ℕ) (b : PowerRouteBox) (j : ℕ)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181245 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899)
    (F : RegularIndex H)
    (hFY : F.1.degreeOf 1 ≤ b.yHi)
    (hFR : F.1.degreeOf 2 ≤ b.rHi)
    (hFZ : F.1.degreeOf 3 ≤ b.tHi)
    (Q : P4)
    (hQT : wt residualTotalWeights Q ≤ L - j * b.tLo)
    (hQY : wt residualYSWeights Q ≤ YS - j * b.yLo)
    (hQR : wt residualSWeights Q ≤ S - j * b.rLo)
    (hrel : IsRelPrime F.1 Q)
    (hgates : HelperPairGates (L - j * b.tLo) (YS - j * b.yLo)
      (S - j * b.rLo) b.yHi b.rHi b.tHi)
    (hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma Q = 0) :
    (regularSeeds H selected Gamma F).card ≤ stageCost L YS S b j := by
  have hQY' : Q.degreeOf 1 ≤ (stagePair L YS S b j).rightY := by
    simpa only [stagePair, helperPair] using (degreeY_le_ysWeight Q).trans hQY
  have hQR' : Q.degreeOf 2 ≤ (stagePair L YS S b j).rightR := by
    simpa only [stagePair, helperPair] using (degreeR_le_sWeight Q).trans hQR
  have hQZ : Q.degreeOf 3 ≤ (stagePair L YS S b j).rightZ := by
    simpa only [stagePair, helperPair] using (degreeZ_le_totalWeight Q).trans hQT
  obtain ⟨hleftR, hleftYSmall, hleftRSmall, hleftZSmall,
    hmixedYSmall, hmixedRSmall, hmixedZSmall⟩ := hgates
  have hcount := AsymmetricHelper.regularSeeds_count_le_left_intersection
    (stagePair L YS S b j) H Q F hrel 2130706433
    (by simpa only [stagePair, helperPair] using hFY)
    (by simpa only [stagePair, helperPair] using hFR)
    (by simpa only [stagePair, helperPair] using hFZ)
    hQY' hQR' hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma
    (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn
    (by
      change (Finset.univ : Finset I).card = 262144
      rw [Finset.card_univ]
      exact Fintype.card_fin _)
    (by norm_num [stagePair, helperPair])
    (by norm_num [stagePair, helperPair])
    (by norm_num [stagePair, helperPair])
    (by norm_num [stagePair, helperPair])
    hdegree hagreement
    (by simpa only [stagePair, helperPair, UnequalParameters.errors,
      (show (262144 - 181245 : ℕ) = 80899 by decide +kernel)] using hno)
    hQzero
  simpa only [stageCost] using hcount

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

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

def exactRouteBox {H : P4} (F : RegularIndex H) : PowerRouteBox where
  tLo := wt residualTotalWeights F.1
  tHi := wt residualTotalWeights F.1
  yLo := wt residualYSWeights F.1
  yHi := wt residualYSWeights F.1
  rLo := wt residualSWeights F.1
  rHi := wt residualSWeights F.1

private theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  omega

private theorem degreeR_le_sWeight (Q : P4) :
    Q.degreeOf (2 : Fin 4) ≤ wt residualSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
    wt residualSWeights Q at h
  omega

private theorem degreeZ_le_totalWeight (Q : P4) :
    Q.degreeOf (3 : Fin 4) ≤ wt residualTotalWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  omega

theorem reconstruct_mem_low_of_batch_power
    {D Dlow L S m j : ℕ} (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D 131071 L S m
      IRSProfile.domain u0 u1)
    (P J : P4)
    (heq : P ^ j * J = reconstruct K D 131071 L S v.1)
    (hD : 0 < D) (hDlow : 0 < Dlow)
    (hcontact : wt (contactWeights 131071) J <
      Dlow - j * wt (contactWeights 131071) P) :
    reconstruct K D 131071 L S v.1 ∈
      globalCoefficientBox K Dlow 131071 L S := by
  have hsource := (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D 131071 L S v.1) D 131071 L S hD).mp
      (reconstruct_mem_globalCoefficientBox K D 131071 L S v.1)
  apply (mem_flagGlobalCoefficientBox_iff
    (reconstruct K D 131071 L S v.1) Dlow 131071 L S hDlow).mpr
  refine ⟨hsource.1, hsource.2.1, ?_⟩
  rw [← heq]
  have hmul := wt_mul_le (contactWeights 131071) (P ^ j) J
  have hp := wt_pow_le (contactWeights 131071) P j
  omega

theorem counts_of_batchExitStage
    (D L S m YS delta fuel : ℕ)
    (hD : 0 < D) (hfuelChar : fuel < 2130706433)
    (hlowpos : ∀ j, 1 ≤ j → j ≤ fuel → 0 < D - j * delta)
    (hcapacity : ∀ j, 1 ≤ j → j ≤ fuel →
      D - j * delta ≤ (m - j) * 181245 + j * (131071 - 1))
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181245 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899)
    (A : Finset (RegularIndex H))
    (q : ConstraintKernel (K := K) D 131071 L S m
        IRSProfile.domain u0 u1 →ₗ[K] P4)
    (hproduct : ∀ v,
      reconstruct K D 131071 L S v.1 = regularProduct H A * q v)
    (hexit : HasBatchExitStage fuel
      (D - delta - wt (contactWeights 131071) (regularProduct H A))
      131071 delta
      (L - wt residualTotalWeights (regularProduct H A))
      (YS - wt residualYSWeights (regularProduct H A))
      (S - wt residualSWeights (regularProduct H A)) H A q)
    (hfeasible :
      fuel * wt residualTotalWeights (regularProduct H A) ≤ L ∧
      fuel * wt residualYSWeights (regularProduct H A) ≤ YS ∧
      fuel * wt residualSWeights (regularProduct H A) ≤ S)
    (hgates : ∀ F ∈ A, ∀ j, 1 ≤ j → j ≤ fuel →
      HelperPairGates
        (L - j * wt residualTotalWeights F.1)
        (YS - j * wt residualYSWeights F.1)
        (S - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1))
    (charge : RegularIndex H → ℕ)
    (hcharge : ∀ F ∈ A, ∀ j, 1 ≤ j → j ≤ fuel →
      stageCost L YS S (exactRouteBox F) j ≤ charge F) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤ charge F := by
  classical
  let P := regularProduct H A
  change HasBatchExitStage fuel
      (D - delta - wt (contactWeights 131071) P) 131071 delta
      (L - wt residualTotalWeights P) (YS - wt residualYSWeights P)
      (S - wt residualSWeights P) H A q at hexit
  obtain ⟨e, U, v, J, hUA, hv, hJ, heq, hbox, havoid⟩ := hexit
  let j := e.val + 1
  have hj : 1 ≤ j := by simp only [j]; omega
  have hjle : j ≤ fuel := by simp only [j]; omega
  have hjchar : j < 2130706433 := hjle.trans_lt hfuelChar
  have heqOriginal : P ^ j * J =
      reconstruct K D 131071 L S v.1 := by
    calc
      P ^ j * J = P * (P ^ e.val * J) := by
        simp only [j, pow_succ']
        ring
      _ = P * q v := by rw [heq]
      _ = reconstruct K D 131071 L S v.1 := (hproduct v).symm
  change J ∈ nestedCoefficientBox K
      (D - delta - wt (contactWeights 131071) P - e.val * delta -
        e.val * wt (contactWeights 131071) P) 131071
      (L - wt residualTotalWeights P - e.val * wt residualTotalWeights P)
      (YS - wt residualYSWeights P - e.val * wt residualYSWeights P)
      (S - wt residualSWeights P - e.val * wt residualSWeights P) at hbox
  have hweights := nested_mem_weights hbox hJ
  have hJT : wt residualTotalWeights J ≤
      L - j * wt residualTotalWeights P := by
    simpa only [j, Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm] using
      hweights.1
  have hJY : wt residualYSWeights J ≤
      YS - j * wt residualYSWeights P := by
    simpa only [j, Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm] using
      hweights.2.1
  have hJS : wt residualSWeights J ≤
      S - j * wt residualSWeights P := by
    simpa only [j, Nat.sub_sub, Nat.add_mul, one_mul, Nat.add_comm] using
      hweights.2.2.1
  have hJcontact : wt (contactWeights 131071) J <
      D - j * delta - j * wt (contactWeights 131071) P := by
    have hc := hweights.2.2.2
    simp only [j, Nat.sub_sub, Nat.add_mul, one_mul] at hc ⊢
    omega
  have hlow : reconstruct K D 131071 L S v.1 ∈
      globalCoefficientBox K (D - j * delta) 131071 L S :=
    reconstruct_mem_low_of_batch_power u0 u1 v P J heqOriginal hD
      (hlowpos j hj hjle) hJcontact
  have hPT : j * wt residualTotalWeights P ≤ L :=
    (Nat.mul_le_mul_right (wt residualTotalWeights P) hjle).trans hfeasible.1
  have hPY : j * wt residualYSWeights P ≤ YS :=
    (Nat.mul_le_mul_right (wt residualYSWeights P) hjle).trans hfeasible.2.1
  have hPS : j * wt residualSWeights P ≤ S :=
    (Nat.mul_le_mul_right (wt residualSWeights P) hjle).trans hfeasible.2.2
  refine ⟨U, hUA, ?_⟩
  intro F hFU
  have hFA : F ∈ A := (Finset.mem_sdiff.mp hFU).1
  let QF := regularCofactor H A F ^ j * J
  have hQF : QF ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero j (regularCofactor_ne_zero H A F)) hJ
  have hrel : IsRelPrime F.1 QF := by
    exact regularFactor_isRelPrime_liftedHelper H A F hFA j J
      (havoid F hFU)
  have hQbounds := liftedHelper_residual_bounds H A F hFA L YS S j J hJ
    hJT hJY hJS hPT hPY hPS
  have hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
      specialization K (selected gamma) gamma QF = 0 := by
    exact batch_helper_zero_on_regularSeeds j D (D - j * delta) 131071
      L S m 181245 2130706433
      (CharP.char_prime_of_ne_zero (R := K) (by norm_num))
      IRSProfile.domain u0 u1 H A F hFA selected Gamma v J hj hjchar
      (by decide) hdegree hagreement (hcapacity j hj hjle) hlow
      heqOriginal
  have hstage := regularSeeds_count_le_stageCost L YS S
    (exactRouteBox F) j u0 u1 H selected Gamma hdegree hagreement hno F
    (degreeY_le_ysWeight F.1) (degreeR_le_sWeight F.1)
    (degreeZ_le_totalWeight F.1) QF
    (by simpa only [exactRouteBox] using hQbounds.1)
    (by simpa only [exactRouteBox] using hQbounds.2.1)
    (by simpa only [exactRouteBox] using hQbounds.2.2)
    hrel (by simpa only [exactRouteBox] using hgates F hFA j hj hjle)
    hQzero
  exact hstage.trans (hcharge F hFA j hj hjle)

theorem exists_strict_helper_split_of_batch_source_thin
    (D L S m YS gap delta fuel : ℕ)
    (hD : 0 < D) (hDa : D ≤ m * 181245)
    (hshape : D + S ≤ 131071 * (YS + 1))
    (hfuel : 1 ≤ fuel) (hfuelChar : fuel < 2130706433)
    (hlowpos : ∀ j, 1 ≤ j → j ≤ fuel → 0 < D - j * delta)
    (hcapacity : ∀ j, 1 ≤ j → j ≤ fuel →
      D - j * delta ≤ (m - j) * 181245 + j * (131071 - 1))
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181245 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899)
    (A : Finset (RegularIndex H)) (hA : A.Nonempty)
    (hbandThin : LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
      (D - wt (contactWeights 131071) (regularProduct H A)) delta
      (wt (contactWeights 131071) (regularProduct H A))
      (wt residualTotalWeights (regularProduct H A))
      (wt residualYSWeights (regularProduct H A))
      (wt residualSWeights (regularProduct H A))
      (L - wt residualTotalWeights (regularProduct H A))
      (YS - wt residualYSWeights (regularProduct H A))
      (S - wt residualSWeights (regularProduct H A)) fuel < gap)
    (hterminal :
      L - fuel * wt residualTotalWeights (regularProduct H A) <
          wt residualTotalWeights (regularProduct H A) ∨
      YS - fuel * wt residualYSWeights (regularProduct H A) <
          wt residualYSWeights (regularProduct H A) ∨
      S - fuel * wt residualSWeights (regularProduct H A) <
          wt residualSWeights (regularProduct H A))
    (hfeasible :
      fuel * wt residualTotalWeights (regularProduct H A) ≤ L ∧
      fuel * wt residualYSWeights (regularProduct H A) ≤ YS ∧
      fuel * wt residualSWeights (regularProduct H A) ≤ S)
    (hgapLe : gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 L S m
        IRSProfile.domain u0 u1))
    (hfield : A.card < ENat.card K)
    (hgates : ∀ F ∈ A, ∀ j, j ≤ fuel →
      HelperPairGates
        (L - j * wt residualTotalWeights F.1)
        (YS - j * wt residualYSWeights F.1)
        (S - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1))
    (charge : RegularIndex H → ℕ)
    (hcharge : ∀ F ∈ A, ∀ j, j ≤ fuel →
      stageCost L YS S (exactRouteBox F) j ≤ charge F) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤ charge F := by
  classical
  let source := ConstraintKernel (K := K) D 131071 L S m
    IRSProfile.domain u0 u1
  let recon : source →ₗ[K] P4 :=
    kernelReconstructLinear (K := K) D 131071 L S m
      IRSProfile.domain u0 u1
  let U₀ := universalFactors H A recon
  have hU₀sub : U₀ ⊆ A := universalFactors_subset H A recon
  by_cases hall : U₀ = A
  · have hdiv : ∀ v : source, regularProduct H A ∣
        reconstruct K D 131071 L S v.1 := by
      intro v
      have hv := universalProduct_dvd H A recon v
      change regularProduct H U₀ ∣ recon v at hv
      rw [hall] at hv
      change regularProduct H A ∣
        kernelReconstructLinear (K := K) D 131071 L S m
          IRSProfile.domain u0 u1 v at hv
      rw [kernelReconstructLinear_apply] at hv
      exact hv
    obtain ⟨q, hq, hproduct, hqbox⟩ :=
      kernelQuotient_regularProduct_nested D 131071 L S m YS
        IRSProfile.domain u0 u1 (by decide) hshape H A hdiv
    cases fuel with
    | zero => omega
    | succ steps =>
      have hDlow :
          D - delta - wt (contactWeights 131071) (regularProduct H A) =
            (D - wt (contactWeights 131071) (regularProduct H A)) - delta := by
        omega
      have hsource : LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
          (D - wt (contactWeights 131071) (regularProduct H A)) delta
          (wt (contactWeights 131071) (regularProduct H A))
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          (L - wt residualTotalWeights (regularProduct H A))
          (YS - wt residualYSWeights (regularProduct H A))
          (S - wt residualSWeights (regularProduct H A)) (steps + 1) <
        Module.finrank K source := hbandThin.trans_le hgapLe
      have hterminal' :
          (L - wt residualTotalWeights (regularProduct H A)) -
              steps * wt residualTotalWeights (regularProduct H A) <
                wt residualTotalWeights (regularProduct H A) ∨
          (YS - wt residualYSWeights (regularProduct H A)) -
              steps * wt residualYSWeights (regularProduct H A) <
                wt residualYSWeights (regularProduct H A) ∨
          (S - wt residualSWeights (regularProduct H A)) -
              steps * wt residualSWeights (regularProduct H A) <
                wt residualSWeights (regularProduct H A) := by
        rcases hterminal with ht | hy | hs
        · left
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using ht
        · right; left
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using hy
        · right; right
          simpa only [Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_mul,
            one_mul, Nat.add_comm] using hs
      have hexit := exists_batchExitStage_of_bandBudgetThin_succ steps
        (D - wt (contactWeights 131071) (regularProduct H A))
        (D - delta - wt (contactWeights 131071) (regularProduct H A))
        131071 delta
        (L - wt residualTotalWeights (regularProduct H A))
        (YS - wt residualYSWeights (regularProduct H A))
        (S - wt residualSWeights (regularProduct H A)) (by decide) hDlow q hq hqbox
        H A hA hsource hterminal' hfield
      exact counts_of_batchExitStage D L S m YS delta (steps + 1)
        hD hfuelChar hlowpos hcapacity u0 u1 H selected Gamma hdegree
        hagreement hno A q hproduct hexit hfeasible
        (fun F hFA j _hj hjle => hgates F hFA j hjle) charge
        (fun F hFA j _hj hjle => hcharge F hFA j hjle)
  · have hproper : U₀ ⊂ A :=
        (_root_.ssubset_iff_subset_ne).mpr ⟨hU₀sub, hall⟩
    refine ⟨U₀, hproper, ?_⟩
    intro F hFU
    have hFA : F ∈ A := (Finset.mem_sdiff.mp hFU).1
    have hnot : ¬ ∀ v : source,
        F.1 ∣ reconstruct K D 131071 L S v.1 := by
      intro hdiv
      apply (Finset.mem_sdiff.mp hFU).2
      apply (mem_universalFactors H A recon F).mpr
      refine ⟨hFA, ?_⟩
      intro v
      change F.1 ∣ kernelReconstructLinear (K := K) D 131071 L S m
        IRSProfile.domain u0 u1 v
      rw [kernelReconstructLinear_apply]
      exact hdiv v
    rcases divisor_or_helper_count D L S m YS hD hDa hshape selected
      Gamma hdegree hagreement hno F
      (wt residualYSWeights F.1) (wt residualSWeights F.1)
      (wt residualTotalWeights F.1)
      (degreeY_le_ysWeight F.1) (degreeR_le_sWeight F.1)
      (degreeZ_le_totalWeight F.1)
      (by simpa using hgates F hFA 0 (Nat.zero_le fuel)) with
      hdiv | hhelper
    · exact (hnot hdiv).elim
    · have hstage : (regularSeeds H selected Gamma F).card ≤
          stageCost L YS S (exactRouteBox F) 0 := by
        simpa only [stageCost, stagePair, exactRouteBox, Nat.zero_mul,
          Nat.sub_zero] using hhelper
      exact hstage.trans (hcharge F hFA 0 (Nat.zero_le _))

end

end ProximityPrize.SubmissionLower.Lower80899.BatchPowerRoute

namespace ProximityPrize.SubmissionLower.Lower80899.Oracle
open RCN095 LocatorFactorAggregate LocatorLowQuotient LocatorArbitraryPowerAvoidance
open Lower80899.PowerRoute Lower80899.FactorSwitch
open LocatorPhase6800Oracle (Potential rawFlag sumFlag RawBelow RawStrictSlopeBelow)
set_option autoImplicit false
set_option maxRecDepth 100000

structure SourceNumbers where
  totalCap : ℕ
  middleCap : ℕ
  slopeCap : ℕ
  gap : ℕ
  deriving DecidableEq, Repr

def SourceNumbers.fuel (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  min (s.totalCap / total p)
    (min (s.middleCap / middle p) (s.slopeCap / p.all))

def SourceNumbers.band (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudget 50175 (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

def contactDec (p : FlagDegree) : ℕ := 131071 * middle p - p.all

def SourceNumbers.contactCap (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  (131071 * (s.middleCap + 1) - s.slopeCap) - contactDec p

def SourceNumbers.bandThin (s : SourceNumbers) (p : FlagDegree) : ℕ :=
  powerBandBudgetThin 131071 (s.contactCap p) 50175 (contactDec p)
    (total p) (middle p) p.all
    (s.totalCap - total p) (s.middleCap - middle p)
    (s.slopeCap - p.all) (s.fuel p)

def SourceNumbers.Routeable (s : SourceNumbers) (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ total p ≤ s.totalCap ∧ middle p ≤ s.middleCap ∧
    p.all ≤ s.slopeCap ∧ (s.band p < s.gap ∨ s.bandThin p < s.gap)

instance (s : SourceNumbers) (p : FlagDegree) : Decidable (s.Routeable p) :=
  by unfold SourceNumbers.Routeable; infer_instance

def exactRouteBox (p : FlagDegree) : PowerRouteBox :=
  ⟨total p, total p, middle p, middle p, p.all, p.all⟩

structure PhaseSourceSound where
  source : SourceNumbers
  potential : Potential
  stageCost_le : ∀ (p : FlagDegree) (j : ℕ),
    1 ≤ p.all → p.all ≤ 39 → middle p ≤ 182 → total p ≤ 11192 →
    j ≤ source.fuel p →
    stageCost source.totalCap source.middleCap source.slopeCap
      (exactRouteBox p) j ≤ potential.eval p
  stageGates : ∀ (p : FlagDegree) (j : ℕ),
    1 ≤ p.all → p.all ≤ 39 → middle p ≤ 182 → total p ≤ 11192 →
    j ≤ source.fuel p →
    HelperPairGates
      (source.totalCap - j * total p)
      (source.middleCap - j * middle p)
      (source.slopeCap - j * p.all)
      (middle p) p.all (total p)

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

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

private theorem sourceFuel_pos (s : SourceNumbers) (p : FlagDegree)
    (hr : 1 ≤ p.all) (ht : total p ≤ s.totalCap)
    (hy : middle p ≤ s.middleCap) (hs : p.all ≤ s.slopeCap) :
    1 ≤ s.fuel p := by
  have hmiddle : 1 ≤ middle p := hr.trans (all_le_middle p)
  have htotal : 1 ≤ total p := hmiddle.trans (middle_le_total p)
  unfold SourceNumbers.fuel
  apply le_min
  · exact (Nat.le_div_iff_mul_le htotal).mpr (by simpa using ht)
  · apply le_min
    · exact (Nat.le_div_iff_mul_le hmiddle).mpr (by simpa using hy)
    · exact (Nat.le_div_iff_mul_le hr).mpr (by simpa using hs)

private theorem sourceFuel_feasible (s : SourceNumbers) (p : FlagDegree)
    (hr : 1 ≤ p.all) :
    s.fuel p * total p ≤ s.totalCap ∧
      s.fuel p * middle p ≤ s.middleCap ∧
      s.fuel p * p.all ≤ s.slopeCap := by
  have hmiddle : 1 ≤ middle p := hr.trans (all_le_middle p)
  have htotal : 1 ≤ total p := hmiddle.trans (middle_le_total p)
  unfold SourceNumbers.fuel
  refine ⟨?_, ?_, ?_⟩
  · apply (Nat.le_div_iff_mul_le htotal).mp
    exact min_le_left _ _
  · apply (Nat.le_div_iff_mul_le hmiddle).mp
    exact (min_le_right _ _).trans (min_le_left _ _)
  · apply (Nat.le_div_iff_mul_le hr).mp
    exact (min_le_right _ _).trans (min_le_right _ _)

private theorem div_remainder_lt (a b : ℕ) (hb : 0 < b) :
    a - (a / b) * b < b := by
  have hm := Nat.mod_lt a hb
  have heq := Nat.mod_add_div' a b
  omega

private theorem sourceFuel_terminal (s : SourceNumbers) (p : FlagDegree)
    (hr : 1 ≤ p.all) :
    s.totalCap - s.fuel p * total p < total p ∨
      s.middleCap - s.fuel p * middle p < middle p ∨
      s.slopeCap - s.fuel p * p.all < p.all := by
  have hall : 0 < p.all := by omega
  have hmiddle : 0 < middle p := hall.trans_le (all_le_middle p)
  have htotal : 0 < total p := hmiddle.trans_le (middle_le_total p)
  unfold SourceNumbers.fuel
  by_cases hT : s.totalCap / total p ≤
      min (s.middleCap / middle p) (s.slopeCap / p.all)
  · left
    rw [min_eq_left hT]
    exact div_remainder_lt s.totalCap (total p) htotal
  · rw [min_eq_right (Nat.le_of_not_ge hT)]
    by_cases hY : s.middleCap / middle p ≤ s.slopeCap / p.all
    · right; left
      rw [min_eq_left hY]
      exact div_remainder_lt s.middleCap (middle p) hmiddle
    · right; right
      rw [min_eq_right (Nat.le_of_not_ge hY)]
      exact div_remainder_lt s.slopeCap p.all hr

theorem routeable_exists_strict_helper_split
    (sound : PhaseSourceSound) (D m : ℕ)
    (hweighted : D = m * 181245)
    (hshape : D + sound.source.slopeCap ≤
      131071 * (sound.source.middleCap + 1))
    (hslopeM : sound.source.slopeCap ≤ m)
    (hmChar : m < 2130706433)
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181245 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80899)
    (hgap : sound.source.gap ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 sound.source.totalCap
        sound.source.slopeCap m IRSProfile.domain u0 u1))
    (A : Finset (RegularIndex H))
    (hroute : sound.source.Routeable (regularAggregateFlag H A))
    (hnarrowS : (regularAggregateFlag H A).all ≤ 39)
    (hnarrowY : middle (regularAggregateFlag H A) ≤ 182)
    (hnarrowT : total (regularAggregateFlag H A) ≤ 11192) :
    ∃ U, U ⊂ A ∧ ∀ F ∈ A \ U,
      (regularSeeds H selected Gamma F).card ≤
        sound.potential.eval (regularCumulativeFlag H F) := by
  classical
  let p := regularAggregateFlag H A
  have hr : 1 ≤ p.all := hroute.1
  have hA : A.Nonempty := by
    by_contra hzero
    have hAe : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hzero
    subst A
    simp [p, regularAggregateFlag, sumFlag] at hr
  have hfuel : 1 ≤ sound.source.fuel p :=
    sourceFuel_pos sound.source p hr hroute.2.1 hroute.2.2.1
      hroute.2.2.2.1
  have hfeasibleP := sourceFuel_feasible sound.source p hr
  have hterminalP := sourceFuel_terminal sound.source p hr
  have hfuelSlope : sound.source.fuel p ≤ sound.source.slopeCap := by
    calc
      sound.source.fuel p ≤ sound.source.slopeCap / p.all :=
        (min_le_right _ _).trans (min_le_right _ _)
      _ ≤ sound.source.slopeCap := Nat.div_le_self _ _
  have hfuelM : sound.source.fuel p ≤ m := hfuelSlope.trans hslopeM
  have hfuelChar : sound.source.fuel p < 2130706433 :=
    hfuelM.trans_lt hmChar
  have hlowpos : ∀ j, 1 ≤ j → j ≤ sound.source.fuel p →
      0 < D - j * 50175 := by
    intro j hj hjfuel
    have hjm : j ≤ m := hjfuel.trans hfuelM
    rw [hweighted]
    omega
  have hcapacity : ∀ j, 1 ≤ j → j ≤ sound.source.fuel p →
      D - j * 50175 ≤
        (m - j) * 181245 + j * (131071 - 1) := by
    intro j _hj hjfuel
    have hjm : j ≤ m := hjfuel.trans hfuelM
    rw [hweighted]
    omega
  have hfield : A.card < ENat.card K := by
    have hcard : A.card ≤ p.all := by
      calc
        A.card = ∑ F ∈ A, 1 := by simp
        _ ≤ ∑ F ∈ A, (regularCumulativeFlag H F).all :=
          Finset.sum_le_sum (fun F _ => Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (regularCumulativeFlag_positive H F)))
        _ = p.all := by simp only [p, regularAggregateFlag, sumFlag_all]
    calc
      (A.card : ENat) ≤ (39 : ℕ) := by
        exact_mod_cast hcard.trans hnarrowS
      _ < ENat.card K := by
        rw [ENat.card_eq_coe_fintype_card, RCN183.field_cardinality]
        norm_num
  have factor_le_aggregate (F : RegularIndex H) (hFA : F ∈ A) :
      (regularCumulativeFlag H F).all ≤ p.all ∧
      middle (regularCumulativeFlag H F) ≤ middle p ∧
      total (regularCumulativeFlag H F) ≤ total p := by
    have hsub : ({F} : Finset (RegularIndex H)) ⊆ A :=
      Finset.singleton_subset_iff.mpr hFA
    simpa [p, regularAggregateFlag, sumFlag, middle, total] using
      regularAggregateFlag_mono H hsub
  have factorFuel (F : RegularIndex H) (hFA : F ∈ A) (j : ℕ)
      (hj : j ≤ sound.source.fuel p) :
      j ≤ sound.source.fuel (regularCumulativeFlag H F) := by
    have hle := factor_le_aggregate F hFA
    have hFr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    have hFm : 1 ≤ middle (regularCumulativeFlag H F) :=
      hFr.trans (all_le_middle _)
    have hFt : 1 ≤ total (regularCumulativeFlag H F) :=
      hFm.trans (middle_le_total _)
    have hjT : j * total (regularCumulativeFlag H F) ≤
        sound.source.totalCap := by
      calc
        j * total (regularCumulativeFlag H F) ≤ j * total p :=
          Nat.mul_le_mul_left j hle.2.2
        _ ≤ sound.source.fuel p * total p :=
          Nat.mul_le_mul_right (total p) hj
        _ ≤ sound.source.totalCap := hfeasibleP.1
    have hjY : j * middle (regularCumulativeFlag H F) ≤
        sound.source.middleCap := by
      calc
        j * middle (regularCumulativeFlag H F) ≤ j * middle p :=
          Nat.mul_le_mul_left j hle.2.1
        _ ≤ sound.source.fuel p * middle p :=
          Nat.mul_le_mul_right (middle p) hj
        _ ≤ sound.source.middleCap := hfeasibleP.2.1
    have hjS : j * (regularCumulativeFlag H F).all ≤
        sound.source.slopeCap := by
      calc
        j * (regularCumulativeFlag H F).all ≤ j * p.all :=
          Nat.mul_le_mul_left j hle.1
        _ ≤ sound.source.fuel p * p.all :=
          Nat.mul_le_mul_right p.all hj
        _ ≤ sound.source.slopeCap := hfeasibleP.2.2
    unfold SourceNumbers.fuel
    apply le_min
    · exact (Nat.le_div_iff_mul_le hFt).mpr hjT
    · apply le_min
      · exact (Nat.le_div_iff_mul_le hFm).mpr hjY
      · exact (Nat.le_div_iff_mul_le hFr).mpr hjS
  have hgates : ∀ F ∈ A, ∀ j, j ≤ sound.source.fuel p →
      HelperPairGates
        (sound.source.totalCap - j * wt residualTotalWeights F.1)
        (sound.source.middleCap - j * wt residualYSWeights F.1)
        (sound.source.slopeCap - j * wt residualSWeights F.1)
        (wt residualYSWeights F.1) (wt residualSWeights F.1)
        (wt residualTotalWeights F.1) := by
    intro F hFA j hj
    have hc := originalCumulativeFlag_cumulative F.1
    have hle := factor_le_aggregate F hFA
    have hFr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    have hs := sound.stageGates (regularCumulativeFlag H F) j hFr
      (hle.1.trans hnarrowS) (hle.2.1.trans hnarrowY)
      (hle.2.2.trans hnarrowT) (factorFuel F hFA j hj)
    have hR : (regularCumulativeFlag H F).all =
        wt residualSWeights F.1 := hc.1
    have hY : middle (regularCumulativeFlag H F) =
        wt residualYSWeights F.1 := hc.2.1
    have hT : total (regularCumulativeFlag H F) =
        wt residualTotalWeights F.1 := hc.2.2
    simpa only [hR, hY, hT] using hs
  have hcharge : ∀ F ∈ A, ∀ j, j ≤ sound.source.fuel p →
      Lower80899.PowerRoute.stageCost sound.source.totalCap
        sound.source.middleCap sound.source.slopeCap
        (Lower80899.BatchPowerRoute.exactRouteBox F) j ≤
          sound.potential.eval (regularCumulativeFlag H F) := by
    intro F hFA j hj
    have hc := originalCumulativeFlag_cumulative F.1
    have hle := factor_le_aggregate F hFA
    have hFr : 1 ≤ (regularCumulativeFlag H F).all :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
    have hs := sound.stageCost_le (regularCumulativeFlag H F) j hFr
      (hle.1.trans hnarrowS) (hle.2.1.trans hnarrowY)
      (hle.2.2.trans hnarrowT) (factorFuel F hFA j hj)
    have hR : (regularCumulativeFlag H F).all =
        wt residualSWeights F.1 := hc.1
    have hY : middle (regularCumulativeFlag H F) =
        wt residualYSWeights F.1 := hc.2.1
    have hT : total (regularCumulativeFlag H F) =
        wt residualTotalWeights F.1 := hc.2.2
    simpa only [Lower80899.BatchPowerRoute.exactRouteBox,
      Lower80899.Oracle.exactRouteBox, hR, hY, hT] using hs
  have hmpos : 0 < m := by omega
  have hDpos : 0 < D := by
    rw [hweighted]
    exact Nat.mul_pos hmpos (by decide)
  have hDa : D ≤ m * 181245 := hweighted.le
  have hP : regularProduct H A ≠ 0 := regularProduct_ne_zero H A
  have hcP : contactDec p ≤ wt (contactWeights 131071) (regularProduct H A) := by
    have h := LocatorArbitraryPowerAvoidance.contact_ge_ys 131071 (by decide)
      (regularProduct H A) hP
    simpa only [contactDec, p, regularAggregateFlag_middle,
      regularAggregateFlag_all] using h
  have hDcap : D - wt (contactWeights 131071) (regularProduct H A) ≤
      sound.source.contactCap p := by
    unfold SourceNumbers.contactCap
    omega
  have hbandThin : LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
      (D - wt (contactWeights 131071) (regularProduct H A)) 50175
      (wt (contactWeights 131071) (regularProduct H A))
      (wt residualTotalWeights (regularProduct H A))
      (wt residualYSWeights (regularProduct H A))
      (wt residualSWeights (regularProduct H A))
      (sound.source.totalCap - wt residualTotalWeights (regularProduct H A))
      (sound.source.middleCap - wt residualYSWeights (regularProduct H A))
      (sound.source.slopeCap - wt residualSWeights (regularProduct H A))
      (sound.source.fuel p) < sound.source.gap := by
    rcases hroute.2.2.2.2 with hold | hthin
    · have hold' : powerBandBudget 50175
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          (sound.source.totalCap - wt residualTotalWeights (regularProduct H A))
          (sound.source.middleCap - wt residualYSWeights (regularProduct H A))
          (sound.source.slopeCap - wt residualSWeights (regularProduct H A))
          (sound.source.fuel p) < sound.source.gap := by
        simpa only [SourceNumbers.band, p, regularAggregateFlag_total,
          regularAggregateFlag_middle, regularAggregateFlag_all] using hold
      exact (LocatorArbitraryPowerAvoidance.powerBandBudgetThin_le
        _ _ _ _ _ _ _ _ _ _ _).trans_lt hold'
    · have hthin' : LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
          (sound.source.contactCap p) 50175 (contactDec p)
          (wt residualTotalWeights (regularProduct H A))
          (wt residualYSWeights (regularProduct H A))
          (wt residualSWeights (regularProduct H A))
          (sound.source.totalCap - wt residualTotalWeights (regularProduct H A))
          (sound.source.middleCap - wt residualYSWeights (regularProduct H A))
          (sound.source.slopeCap - wt residualSWeights (regularProduct H A))
          (sound.source.fuel p) < sound.source.gap := by
        simpa only [SourceNumbers.bandThin, p, regularAggregateFlag_total,
          regularAggregateFlag_middle, regularAggregateFlag_all] using hthin
      exact (LocatorArbitraryPowerAvoidance.powerBandBudgetThin_mono 131071 50175
        (sound.source.fuel p) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hDcap hcP le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl).trans_lt hthin'
  apply exists_strict_helper_split_of_batch_source_thin D
    sound.source.totalCap sound.source.slopeCap m sound.source.middleCap
    sound.source.gap 50175 (sound.source.fuel p)
  · exact hDpos
  · exact hDa
  · exact hshape
  · exact hfuel
  · exact hfuelChar
  · exact hlowpos
  · exact hcapacity
  · exact hdegree
  · exact hagreement
  · exact hno
  · exact hA
  · exact hbandThin
  · simpa only [p, regularAggregateFlag_total,
      regularAggregateFlag_middle, regularAggregateFlag_all] using hterminalP
  · simpa only [p, regularAggregateFlag_total,
      regularAggregateFlag_middle, regularAggregateFlag_all] using hfeasibleP
  · exact hgap
  · exact hfield
  · exact hgates
  · exact hcharge

structure PhaseKernelRealization (sound : PhaseSourceSound)
    (u0 u1 : I → K) where
  D : ℕ
  m : ℕ
  weighted : D = m * 181245
  shape : D + sound.source.slopeCap ≤
    131071 * (sound.source.middleCap + 1)
  slope_le_m : sound.source.slopeCap ≤ m
  m_lt_char : m < 2130706433
  gap_le_finrank : sound.source.gap ≤ Module.finrank K
    (ConstraintKernel (K := K) D 131071 sound.source.totalCap
      sound.source.slopeCap m IRSProfile.domain u0 u1)

end

end ProximityPrize.SubmissionLower.Lower80899.BatchPhase
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.MovingFiberPaddedIdentity6815

open RCN095
open Lower80788.FixedStage

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem identity_absorption (f : FlagDegree) (a b s : ℕ) :
    131073 * 80900 * ProximityPrize.SubmissionLower.RCN146.identityCurveDegree f a b s 131071 ≤
      50174 * flagMixed f (firstTail a b s) (secondTail a b s) := by
  change 131073 * 80900 * ProximityPrize.SubmissionLower.RCN146.identityCurveDegree f a b s Lower80788.FixedStage.w ≤ _
  rw [Lower80788.FixedStage.identityDegree_linear]
  norm_num [firstTail, secondTail, Lower80788.FixedStage.tail_support_formula,
    Lower80788.FixedStage.w, flagMixed]
  ring_nf
  omega

theorem low_pad_parameters (p : FlagDegree)
    (h : ¬ LocatorHybridCostC2.HybridAppliesC2 p) :
    Lower80788.Fixed.padSlope p = 0 ∨ Lower80788.Fixed.padB p = 0 := by
  dsimp [LocatorHybridCostC2.HybridAppliesC2, LocatorFactorAggregate.middle] at h
  dsimp [Lower80788.Fixed.padSlope, Lower80788.Fixed.padB,
    LocatorFactorAggregate.padS, LocatorFactorAggregate.padY,
    LocatorFactorAggregate.middle]
  omega

theorem low_provider_mixed_gate (b s : ℕ) (f : FlagDegree)
    (hS : s+2 ≤ 32) (hY : b+s+3 ≤ 149)
    (hlow : s=0 ∨ b=0)
    (hfs : f.all ≤ s+2) (hfy : f.yz+f.all ≤ b+s+3) :
    (1+131072*(2*(b+s+3)-2))*f.all +
      (f.yz+f.all)*((2*(s+2)-2)*131072) < 2130706433 := by
  rcases hlow with hs0 | hb0
  · have hy : 2*(b+s+3)-2 ≤ 296 := by omega
    have hs : 2*(s+2)-2 ≤ 2 := by omega
    have hfS : f.all ≤ 2 := by omega
    have hfY : f.yz+f.all ≤ 149 := by omega
    calc
      _ ≤ (1+131072*296)*2 + 149*(2*131072) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131072 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131072 hs))
      _ < 2130706433 := by decide
  · have hy : 2*(b+s+3)-2 ≤ 64 := by omega
    have hs : 2*(s+2)-2 ≤ 62 := by omega
    have hfS : f.all ≤ 32 := by omega
    have hfY : f.yz+f.all ≤ 33 := by omega
    calc
      _ ≤ (1+131072*64)*32 + 33*(62*131072) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131072 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131072 hs))
      _ < 2130706433 := by decide

theorem low_identity_mixed_gate (b s : ℕ) (f : FlagDegree)
    (hS : s+2 ≤ 32) (hY : b+s+3 ≤ 149)
    (hlow : s=0 ∨ b=0)
    (hfs : f.all ≤ s+2) (hfy : f.yz+f.all ≤ b+s+3) :
    (1+131071*(2*(b+s+3)-2))*f.all +
      (f.yz+f.all)*((2*(s+2)-1)*131071) < 2130706433 := by
  rcases hlow with hs0 | hb0
  · have hy : 2*(b+s+3)-2 ≤ 296 := by omega
    have hs : 2*(s+2)-1 ≤ 3 := by omega
    have hfS : f.all ≤ 2 := by omega
    have hfY : f.yz+f.all ≤ 149 := by omega
    calc
      _ ≤ (1+131071*296)*2 + 149*(3*131071) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131071 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131071 hs))
      _ < 2130706433 := by decide
  · have hy : 2*(b+s+3)-2 ≤ 64 := by omega
    have hs : 2*(s+2)-1 ≤ 63 := by omega
    have hfS : f.all ≤ 32 := by omega
    have hfY : f.yz+f.all ≤ 33 := by omega
    calc
      _ ≤ (1+131071*64)*32 + 33*(63*131071) :=
        Nat.add_le_add
          (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left 131071 hy) 1) hfS)
          (Nat.mul_le_mul hfY (Nat.mul_le_mul_right 131071 hs))
      _ < 2130706433 := by decide

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
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80899
def agreements:ℕ:=181245
def gap:ℕ:=50174
def prime:ℕ:=2130706433
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K prime:=by
  simpa [prime,RCN223.prime] using
    RCN128.challenge_field_characteristic6600
def firstTail (a b s:ℕ):FlagDegree:=
  reducedResidualAgreementFlag (RCN198.support a b s) (w + 1)
def secondTail (a b s:ℕ):FlagDegree:=
  reducedResidualAgreementFlag (RCN198.support a b s) (w + 2)
theorem tail_support_formula (a b s d:ℕ) :
    reducedResidualAgreementFlag (RCN198.support a b s) d=
      ⟨2 * a * d,1 + 2 * (b + 1) * d,2 * (s + 1) * d⟩:=by
  have ht:a + b + s + 3 - (b + s + 3) =a:=by omega
  have hy:b + s + 3 - (s + 2) =b + 1:=by omega
  have hs:2 * (s + 2) - 2=2 * (s + 1):=by omega
  simp only [reducedResidualAgreementFlag,reducedAgreementDirection,RCN198.support]
  rw [ht,hy,hs]
theorem tangent_gate (a b s:ℕ) :
    errors + 1 ≤ (secondTail a b s).yz:=by
  rw [secondTail,tail_support_formula]
  change errors + 1 ≤ 1 + 2 * (b + 1) * (w + 2)
  have hb:2 * (w + 2) ≤ 2 * (b + 1) * (w + 2):=by
    have h:=Nat.mul_le_mul_right (w + 2)
      (Nat.mul_le_mul_left 2 (show 1 ≤ b + 1 by omega))
    simpa only [Nat.mul_one] using h
  exact (by norm_num [errors,w]:errors + 1 ≤ 1 + 2 * (w + 2)).trans
    (Nat.add_le_add_left hb 1)
theorem flag_characteristic (a b s:ℕ) (flag:FlagDegree)
    (hS:s + 2 ≤ 32) (hY:b + s + 3 ≤ 149) (hT:a + b + s + 3 ≤ 8121)
    (hflag:flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    flag.yz + flag.all < prime ∧ flag.all < prime ∧
      flag.zOnly + flag.yz + flag.all < prime:=by
  dsimp [prime]
  omega
def FixedStageBound (D a b s:ℕ):Prop:=
  ∀ {Gamma:Finset K} {flag:FlagDegree},
    (S:ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
      prime errors flag w (RCN198.support a b s)) →
    S.nodes.card=agreements + errors →
    (∀ gamma ∈ Gamma,agreements ≤ (S.agreementFiber gamma).card) →
    S.F ∈ RCN174.globalCoefficientBox K D w (a + b + s + 3) (s + 2) →
    (flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) →
    Gamma.card ≤ flagMixed flag (firstTail a b s) (secondTail a b s)
theorem fixedStageBound (D a b s:ℕ)
    (hDlow:w + 1 ≤ D) (hDhigh:D < prime)
    (hS:s + 2 ≤ 32) (hY:b + s + 3 ≤ 149) (hT:a + b + s + 3 ≤ 8121)
    (hlow : s = 0 ∨ b = 0) :
    FixedStageBound D a b s:=by
  intro Gamma flag S hnodes hagreement hbox hflag
  have hDchar:D < prime:=hDhigh
  have hflagChar:=flag_characteristic a b s flag hS hY hT hflag
  by_cases hTail:S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)
  · have hTailNumerator:S.G ∣ surfaceMap (polynomialEmbedding K)
        (numerator K S.F (w + 1)) :=
      (globalTailCut_dvd_iff (polynomialEmbedding K)
        (polynomialEmbedding_injective K) S.F (w + 1) S.G).mp hTail
    have hprovider:=RCN146.actual_identityCurveCountProvider S agreements hnodes
      hagreement (by norm_num [agreements,w]) hTailNumerator
      D (a + b + s + 3) (s + 2)
      (by norm_num [w]) hDlow hDchar hbox hflagChar
      (MovingFiberPaddedIdentity6815.low_identity_mixed_gate b s flag hS hY hlow hflag.1 hflag.2.1)
    have hpositive:1 ≤ ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag a b s w:=by
      apply Lower80788.FixedStage.identity_positive
      have hy:0 < S.G.degreeOf 1:=S.y_dependent
      have hdeg:=degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc:=identity_surface_seed_bound S agreements
      (ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag a b s w) hprovider hagreement
      (by norm_num [agreements,w])
      (by rw [hnodes] <;> norm_num [agreements,errors]) hpositive
    have hscaled:Gamma.card * gap ≤
        gap * flagMixed flag (firstTail a b s) (secondTail a b s):=by
      calc
        Gamma.card * gap=Gamma.card * (agreements - w):=rfl
        _ ≤ (S.nodes.card - w) * (errors + 1) *
            ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag a b s w:=hinc
        _= (n - w) * (errors + 1) * ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag a b s w:=by
          rw [hnodes] <;> norm_num [n,agreements,errors]
        _ ≤ gap * flagMixed flag (firstTail a b s) (secondTail a b s) :=
          MovingFiberPaddedIdentity6815.identity_absorption flag a b s
    apply Nat.le_of_mul_le_mul_right ?_ (by norm_num [gap]:0 < gap)
    simpa only [Nat.mul_comm] using hscaled
  · have hprovider:=exists_delayedTailMultiplicityProvider_of_reducedGeneral
      (stageErrorCap:=errors) agreements S hTail hflagChar
      (MovingFiberPaddedIdentity6815.low_provider_mixed_gate b s flag hS hY hlow hflag.1 hflag.2.1)
      D (a + b + s + 3) (s + 2) hnodes hagreement
      (by norm_num [RCN327.w,agreements])
      (by simpa only [RCN327.w,w] using hDlow)
      hDchar hbox (tangent_gate a b s)
    exact stage_card_le_flagMixed S hprovider.some
end

end ProximityPrize.SubmissionLower.MovingFiberOrdinaryLow6815
end MergedPart7
