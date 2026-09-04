import ProximityPrize.SubmissionLower.PackedLocatorTail2
import ProximityPrize.SubmissionLower.PackedLocatorRunsA
import ProximityPrize.SubmissionLower.PackedLocatorRunsB
import ProximityPrize.SubmissionLower.PackedLocatorRunsC
import ProximityPrize.SubmissionLower.PackedLocatorRunsD
import ProximityPrize.SubmissionLower.PackedLocatorChecksA
import ProximityPrize.SubmissionLower.PackedLocatorChecksB

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunChecked. -/
section PackedLocator_LocatorPhase6800PhaseRunChecked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunChecked

open LocatorPhase6800Concrete LocatorPhase6800PhaseRunsBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem states : PhaseStateChecks := by
  intro R hR hpos
  have hlt : R < 30 := List.mem_range.mp hR
  interval_cases R <;>
  first
    | exact sparseLayer_to_public 1 (by decide) (by decide)
        LocatorPhase6800PhaseRunData01.sparseStates
    | exact sparseLayer_to_public 2 (by decide) (by decide)
        LocatorPhase6800PhaseRunData02.sparseStates
    | exact sparseLayer_to_public 3 (by decide) (by decide)
        LocatorPhase6800PhaseRunData03.sparseStates
    | exact sparseLayer_to_public 4 (by decide) (by decide)
        LocatorPhase6800PhaseRunData04.sparseStates
    | exact sparseLayer_to_public 5 (by decide) (by decide)
        LocatorPhase6800PhaseRunData05.sparseStates
    | exact sparseLayer_to_public 6 (by decide) (by decide)
        LocatorPhase6800PhaseRunData06.sparseStates
    | exact sparseLayer_to_public 7 (by decide) (by decide)
        LocatorPhase6800PhaseRunData07.sparseStates
    | exact sparseLayer_to_public 8 (by decide) (by decide)
        LocatorPhase6800PhaseRunData08.sparseStates
    | exact sparseLayer_to_public 9 (by decide) (by decide)
        LocatorPhase6800PhaseRunData09.sparseStates
    | exact sparseLayer_to_public 10 (by decide) (by decide)
        LocatorPhase6800PhaseRunData10.sparseStates
    | exact sparseLayer_to_public 11 (by decide) (by decide)
        LocatorPhase6800PhaseRunData11.sparseStates
    | exact sparseLayer_to_public 12 (by decide) (by decide)
        LocatorPhase6800PhaseRunData12.sparseStates
    | exact sparseLayer_to_public 13 (by decide) (by decide)
        LocatorPhase6800PhaseRunData13.sparseStates
    | exact sparseLayer_to_public 14 (by decide) (by decide)
        LocatorPhase6800PhaseRunData14.sparseStates
    | exact sparseLayer_to_public 15 (by decide) (by decide)
        LocatorPhase6800PhaseRunData15.sparseStates
    | exact sparseLayer_to_public 16 (by decide) (by decide)
        LocatorPhase6800PhaseRunData16.sparseStates
    | exact sparseLayer_to_public 17 (by decide) (by decide)
        LocatorPhase6800PhaseRunData17.sparseStates
    | exact sparseLayer_to_public 18 (by decide) (by decide)
        LocatorPhase6800PhaseRunData18.sparseStates
    | exact sparseLayer_to_public 19 (by decide) (by decide)
        LocatorPhase6800PhaseRunData19.sparseStates
    | exact sparseLayer_to_public 20 (by decide) (by decide)
        LocatorPhase6800PhaseRunData20.sparseStates
    | exact sparseLayer_to_public 21 (by decide) (by decide)
        LocatorPhase6800PhaseRunData21.sparseStates
    | exact sparseLayer_to_public 22 (by decide) (by decide)
        LocatorPhase6800PhaseRunData22.sparseStates
    | exact sparseLayer_to_public 23 (by decide) (by decide)
        LocatorPhase6800PhaseRunData23.sparseStates
    | exact sparseLayer_to_public 24 (by decide) (by decide)
        LocatorPhase6800PhaseRunData24.sparseStates
    | exact sparseLayer_to_public 25 (by decide) (by decide)
        LocatorPhase6800PhaseRunData25.sparseStates
    | exact sparseLayer_to_public 26 (by decide) (by decide)
        LocatorPhase6800PhaseRunData26.sparseStates
    | exact sparseLayer_to_public 27 (by decide) (by decide)
        LocatorPhase6800PhaseRunData27.sparseStates
    | exact sparseLayer_to_public 28 (by decide) (by decide)
        LocatorPhase6800PhaseRunData28.sparseStates
    | exact sparseLayer_to_public 29 (by decide) (by decide)
        LocatorPhase6800PhaseRunData29.sparseStates

end ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRunChecked

end PackedLocator_LocatorPhase6800PhaseRunChecked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier192 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdCoreChecked. -/
section PackedLocator_LocatorPhase6800ThresholdCoreChecked

namespace ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdCoreChecked

open LocatorPhase6800Concrete LocatorPhase6800ReceiptCellCore ThresholdFastProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem thresholdR01 : ThresholdRIndexed 1 := by
  exact LocatorPhase6800ThresholdR01Checked.checked

theorem thresholdR02 : ThresholdRIndexed 2 := by
  exact LocatorPhase6800ThresholdR02Checked.checked

theorem thresholdR03 : ThresholdRIndexed 3 := by
  exact LocatorPhase6800ThresholdR03Checked.checked

theorem thresholdR04 : ThresholdRIndexed 4 := by
  exact LocatorPhase6800ThresholdR04Checked.checked

theorem thresholdR05 : ThresholdRIndexed 5 := by
  exact LocatorPhase6800ThresholdR05Checked.checked

theorem thresholdR06 : ThresholdRIndexed 6 := by
  exact LocatorPhase6800ThresholdR06Checked.checked

theorem thresholdR07 : ThresholdRIndexed 7 := by
  exact LocatorPhase6800ThresholdR07Checked.checked

theorem thresholdR08 : ThresholdRIndexed 8 := by
  exact LocatorPhase6800ThresholdR08Checked.checked

theorem thresholdR09 : ThresholdRIndexed 9 := by
  exact LocatorPhase6800ThresholdR09Checked.checked

theorem thresholdR10 : ThresholdRIndexed 10 := by
  exact LocatorPhase6800ThresholdR10Checked.checked

theorem thresholdR11 : ThresholdRIndexed 11 := by
  exact LocatorPhase6800ThresholdR11Checked.checked

theorem thresholdR12 : ThresholdRIndexed 12 := by
  exact LocatorPhase6800ThresholdR12Checked.checked

theorem thresholdR13 : ThresholdRIndexed 13 := by
  exact LocatorPhase6800ThresholdR13Checked.checked

theorem thresholdR14 : ThresholdRIndexed 14 := by
  exact LocatorPhase6800ThresholdR14Checked.checked

theorem thresholdR15 : ThresholdRIndexed 15 := by
  exact LocatorPhase6800ThresholdR15Checked.checked

theorem thresholdR16 : ThresholdRIndexed 16 := by
  exact LocatorPhase6800ThresholdR16Checked.checked

theorem thresholdR17 : ThresholdRIndexed 17 := by
  exact LocatorPhase6800ThresholdR17Checked.checked

theorem thresholdR18 : ThresholdRIndexed 18 := by
  exact LocatorPhase6800ThresholdR18Checked.checked

theorem thresholdR19 : ThresholdRIndexed 19 := by
  exact LocatorPhase6800ThresholdR19Checked.checked

theorem thresholdR20 : ThresholdRIndexed 20 := by
  exact LocatorPhase6800ThresholdR20Checked.checked

theorem thresholdR21 : ThresholdRIndexed 21 := by
  exact LocatorPhase6800ThresholdR21Checked.checked

theorem thresholdR22 : ThresholdRIndexed 22 := by
  exact LocatorPhase6800ThresholdR22Checked.checked

theorem thresholdR23 : ThresholdRIndexed 23 := by
  exact LocatorPhase6800ThresholdR23Checked.checked

theorem thresholdR24 : ThresholdRIndexed 24 := by
  exact LocatorPhase6800ThresholdR24Checked.checked

theorem thresholdR25 : ThresholdRIndexed 25 := by
  exact LocatorPhase6800ThresholdR25Checked.checked

theorem thresholdR26 : ThresholdRIndexed 26 := by
  exact LocatorPhase6800ThresholdR26Checked.checked

theorem thresholdR27 : ThresholdRIndexed 27 := by
  exact LocatorPhase6800ThresholdR27Checked.checked

theorem thresholdR28 : ThresholdRIndexed 28 := by
  exact LocatorPhase6800ThresholdR28Checked.checked

theorem thresholdR29 : ThresholdRIndexed 29 := by
  exact LocatorPhase6800ThresholdR29Checked.checked

theorem coreR01 : PrefixCoreRCheck 1 := by
  exact LocatorPhase6800PrefixCoreR01Checked.checked

theorem coreR02 : PrefixCoreRCheck 2 := by
  exact LocatorPhase6800PrefixCoreR02Checked.checked

theorem coreR03 : PrefixCoreRCheck 3 := by
  exact LocatorPhase6800PrefixCoreR03Checked.checked

theorem coreR04 : PrefixCoreRCheck 4 := by
  exact LocatorPhase6800PrefixCoreR04Checked.checked

theorem coreR05 : PrefixCoreRCheck 5 := by
  exact LocatorPhase6800PrefixCoreR05Checked.checked

theorem coreR06 : PrefixCoreRCheck 6 := by
  exact LocatorPhase6800PrefixCoreR06Checked.checked

theorem coreR07 : PrefixCoreRCheck 7 := by
  exact LocatorPhase6800PrefixCoreR07Checked.checked

theorem coreR08 : PrefixCoreRCheck 8 := by
  exact LocatorPhase6800PrefixCoreR08Checked.checked

theorem coreR09 : PrefixCoreRCheck 9 := by
  exact LocatorPhase6800PrefixCoreR09Checked.checked

theorem coreR10 : PrefixCoreRCheck 10 := by
  exact LocatorPhase6800PrefixCoreR10Checked.checked

theorem coreR11 : PrefixCoreRCheck 11 := by
  exact LocatorPhase6800PrefixCoreR11Checked.checked

theorem coreR12 : PrefixCoreRCheck 12 := by
  exact LocatorPhase6800PrefixCoreR12Checked.checked

theorem coreR13 : PrefixCoreRCheck 13 := by
  exact LocatorPhase6800PrefixCoreR13Checked.checked

theorem coreR14 : PrefixCoreRCheck 14 := by
  exact LocatorPhase6800PrefixCoreR14Checked.checked

theorem coreR15 : PrefixCoreRCheck 15 := by
  exact LocatorPhase6800PrefixCoreR15Checked.checked

theorem coreR16 : PrefixCoreRCheck 16 := by
  exact LocatorPhase6800PrefixCoreR16Checked.checked

theorem coreR17 : PrefixCoreRCheck 17 := by
  exact LocatorPhase6800PrefixCoreR17Checked.checked

theorem coreR18 : PrefixCoreRCheck 18 := by
  exact LocatorPhase6800PrefixCoreR18Checked.checked

theorem coreR19 : PrefixCoreRCheck 19 := by
  exact LocatorPhase6800PrefixCoreR19Checked.checked

theorem coreR20 : PrefixCoreRCheck 20 := by
  exact LocatorPhase6800PrefixCoreR20Checked.checked

theorem coreR21 : PrefixCoreRCheck 21 := by
  exact LocatorPhase6800PrefixCoreR21Checked.checked

theorem coreR22 : PrefixCoreRCheck 22 := by
  exact LocatorPhase6800PrefixCoreR22Checked.checked

theorem coreR23 : PrefixCoreRCheck 23 := by
  exact LocatorPhase6800PrefixCoreR23Checked.checked

theorem coreR24 : PrefixCoreRCheck 24 := by
  exact LocatorPhase6800PrefixCoreR24Checked.checked

theorem coreR25 : PrefixCoreRCheck 25 := by
  exact LocatorPhase6800PrefixCoreR25Checked.checked

theorem coreR26 : PrefixCoreRCheck 26 := by
  exact LocatorPhase6800PrefixCoreR26Checked.checked

theorem coreR27 : PrefixCoreRCheck 27 := by
  exact LocatorPhase6800PrefixCoreR27Checked.checked

theorem coreR28 : PrefixCoreRCheck 28 := by
  exact LocatorPhase6800PrefixCoreR28Checked.checked

theorem thresholds : ThresholdsIndexed := by
  intro R hR hpos
  have hlt := List.mem_range.mp hR
  interval_cases R
  · exact thresholdR01
  · exact thresholdR02
  · exact thresholdR03
  · exact thresholdR04
  · exact thresholdR05
  · exact thresholdR06
  · exact thresholdR07
  · exact thresholdR08
  · exact thresholdR09
  · exact thresholdR10
  · exact thresholdR11
  · exact thresholdR12
  · exact thresholdR13
  · exact thresholdR14
  · exact thresholdR15
  · exact thresholdR16
  · exact thresholdR17
  · exact thresholdR18
  · exact thresholdR19
  · exact thresholdR20
  · exact thresholdR21
  · exact thresholdR22
  · exact thresholdR23
  · exact thresholdR24
  · exact thresholdR25
  · exact thresholdR26
  · exact thresholdR27
  · exact thresholdR28
  · exact thresholdR29

theorem core : PrefixCoreChecks := by
  intro R hR hpos
  have hlt := List.mem_range.mp hR
  interval_cases R
  · exact coreR01
  · exact coreR02
  · exact coreR03
  · exact coreR04
  · exact coreR05
  · exact coreR06
  · exact coreR07
  · exact coreR08
  · exact coreR09
  · exact coreR10
  · exact coreR11
  · exact coreR12
  · exact coreR13
  · exact coreR14
  · exact coreR15
  · exact coreR16
  · exact coreR17
  · exact coreR18
  · exact coreR19
  · exact coreR20
  · exact coreR21
  · exact coreR22
  · exact coreR23
  · exact coreR24
  · exact coreR25
  · exact coreR26
  · exact coreR27
  · exact coreR28

#print axioms thresholds
#print axioms core

end ProximityPrize.SubmissionLower.LocatorPhase6800ThresholdCoreChecked
end PackedLocator_LocatorPhase6800ThresholdCoreChecked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier249 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Checked. -/
section PackedLocator_LocatorPhase6800Checked

/-! Assembly of the kernel-checked sparse 6800 receipt. -/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Checked

open LocatorPhase6800Concrete LocatorPhase6800Oracle LocatorPhase6800Audit

set_option maxRecDepth 100000

theorem thresholds : ThresholdsIndexed :=
  LocatorPhase6800ThresholdCoreChecked.thresholds

theorem core : PrefixCoreChecks :=
  LocatorPhase6800ThresholdCoreChecked.core

theorem states : PhaseStateChecks :=
  LocatorPhase6800PhaseRunChecked.states

theorem rRows :
    PrefixTableSound checkedBaseCap r1200Potential
      sourceR1200.Routeable rPrefix :=
  LocatorPhase6800Concrete.rRows thresholds states core

theorem cRows :
    PrefixTableSound afterR sourceCPotential sourceC.Routeable cPrefix :=
  LocatorPhase6800Concrete.cRows thresholds states core

theorem f500Rows :
    PrefixTableSound afterC split500Potential
      sourceSplit500.Routeable f500Prefix :=
  LocatorPhase6800Concrete.f500Rows thresholds states core

theorem s1200Rows :
    PrefixTableSound afterF500 split1200Potential
      sourceSplit1200.Routeable s1200Prefix :=
  LocatorPhase6800Concrete.s1200Rows thresholds states core

theorem s390Rows :
    PrefixTableSound afterS1200 split390Potential
      sourceSplit390.Routeable s390Prefix :=
  LocatorPhase6800Concrete.s390Rows thresholds states core

end ProximityPrize.SubmissionLower.LocatorPhase6800Checked
end PackedLocator_LocatorPhase6800Checked

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier250 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800Certificate. -/
section PackedLocator_LocatorPhase6800Certificate

/-! Fully checked compact certificate consumed by the algebraic 6800 route. -/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Certificate

open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def certificate : LocatorPhase6800Composition.PhasePrefixCertificate where
  baseCap := LocatorPhase6800Concrete.checkedBaseCap
  rPrefix := LocatorPhase6800Concrete.rPrefix
  cPrefix := LocatorPhase6800Concrete.cPrefix
  f500Prefix := LocatorPhase6800Concrete.f500Prefix
  s1200Prefix := LocatorPhase6800Concrete.s1200Prefix
  s390Prefix := LocatorPhase6800Concrete.s390Prefix
  baseSound := LocatorPhase6800Concrete.checkedBaseCap_sound
  rRows := LocatorPhase6800Checked.rRows
  cRows := by
    simpa [LocatorPhase6800Composition.afterR1200,
      LocatorPhase6800Concrete.afterR] using LocatorPhase6800Checked.cRows
  f500Rows := by
    simpa [LocatorPhase6800Composition.afterSourceC,
      LocatorPhase6800Composition.afterR1200,
      LocatorPhase6800Concrete.afterC,
      LocatorPhase6800Concrete.afterR] using LocatorPhase6800Checked.f500Rows
  s1200Rows := by
    simpa [LocatorPhase6800Composition.afterSplit500,
      LocatorPhase6800Composition.afterSourceC,
      LocatorPhase6800Composition.afterR1200,
      LocatorPhase6800Concrete.afterF500,
      LocatorPhase6800Concrete.afterC,
      LocatorPhase6800Concrete.afterR] using LocatorPhase6800Checked.s1200Rows
  s390Rows := by
    simpa [LocatorPhase6800Composition.afterSplit1200,
      LocatorPhase6800Composition.afterSplit500,
      LocatorPhase6800Composition.afterSourceC,
      LocatorPhase6800Composition.afterR1200,
      LocatorPhase6800Concrete.afterS1200,
      LocatorPhase6800Concrete.afterF500,
      LocatorPhase6800Concrete.afterC,
      LocatorPhase6800Concrete.afterR] using LocatorPhase6800Checked.s390Rows
  joint := by
    intro p hslope hmiddle htotal
    simpa [LocatorPhase6800Composition.afterSplit390,
      LocatorPhase6800Composition.afterSplit1200,
      LocatorPhase6800Composition.afterSplit500,
      LocatorPhase6800Composition.afterSourceC,
      LocatorPhase6800Composition.afterR1200,
      LocatorPhase6800Concrete.afterS390,
      LocatorPhase6800Concrete.afterS1200,
      LocatorPhase6800Concrete.afterF500,
      LocatorPhase6800Concrete.afterC,
      LocatorPhase6800Concrete.afterR,
      LocatorFixedConsumer.initialRegularCap,
      LocatorArithmetic.fixedRegularCap, certifiedJointMaximum] using
        LocatorPhase6800Concrete.joint_le LocatorPhase6800Checked.thresholds
          LocatorPhase6800Checked.states p hslope hmiddle htotal

end ProximityPrize.SubmissionLower.LocatorPhase6800Certificate
end PackedLocator_LocatorPhase6800Certificate

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier251 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.LocatorClosure6800. -/
section PackedLocator_LocatorClosure6800

/-!
# Final reduction closure for the 6800 certificate

This module keeps the protocol and residual argument independent of the
generated receipt representation.  The only input is the sound
`PhasePrefixCertificate` exported by the phase composition layer.
-/

namespace ProximityPrize.SubmissionLower.LocatorClosure6800

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN050 RCN319 RCN238 RCN259 RCN156 RCN234 LocatorSelection

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

abbrev K := LocatorPhase6800Composition.K
abbrev I := LocatorPhase6800Composition.I
abbrev P4 := LocatorPhase6800Composition.P4

local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

theorem selected_pair_count_of_certificate
    (cert : LocatorPhase6800Composition.PhasePrefixCertificate)
    (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ gamma ∈ seeds,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ seeds, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected seeds 131071 80781) :
    seeds.card < LocatorArithmetic.budget := by
  have hnoResidual : NoLargeSelectedPencil selected seeds LocatorArithmetic.w
      (LocatorArithmetic.n - LocatorArithmetic.agreements) := by
    simpa only [LocatorArithmetic.w, LocatorArithmetic.n,
      LocatorArithmetic.agreements, Nat.reduceSub] using hno
  let phi : K → P4 →+* Polynomial K := fun gamma ↦
    (specialization K (selected gamma) gamma).toRingHom
  have hparents (gamma : K) (hg : gamma ∈ seeds) :
      specialization K (selected gamma) gamma S.QA = 0 ∧
      specialization K (selected gamma) gamma S.QB = 0 := by
    exact S.universal_vanishing gamma (selected gamma)
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i))
      (hdegree gamma hg) (hagreement gamma hg)
      (fun _ hi ↦ (Finset.mem_filter.mp hi).2)
  have hnodes : (Finset.univ : Finset I).card = LocatorArithmetic.n := by
    norm_num [I, IRSProfile.Index, LocatorArithmetic.n]
  obtain ⟨d, hd, hfixedRaw⟩ :=
    LocatorPhase6800Composition.gcd_fixed_count_le_of_certificate cert
      u0 u1 S selected seeds hdegree hagreement hno
  have hfixed : (LocatorCover.fixed phi seeds S.QA S.QB).card +
      ChainGroupMaj.residMaj6802 d ≤
      273301903386687639 + LocatorArithmetic.fixedTailCap := by
    simpa only [phi, K, P4, LocatorPhase6800Composition.K,
      LocatorPhase6800Composition.P4, LocatorSelection.K, LocatorSelection.P4,
      LocatorFixedConsumer.initialRegularCap, LocatorArithmetic.fixedRegularCap]
      using hfixedRaw
  have hd' : d ≤ wt residualSWeights (gcd12 S.QA S.QB) := by
    simpa only [K, P4, LocatorPhase6800Composition.K,
      LocatorPhase6800Composition.P4, LocatorSelection.K, LocatorSelection.P4] using hd
  have hresidualRaw := LocatorResidual.gcd_residual_count_lt_slope (K := K) (I := I) d
    S.QA S.QB S.QA_ne S.QB_ne S.QA_flag S.QB_flag
    selected seeds (Finset.univ : Finset I) IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn hnodes hdegree
    (fun gamma hg ↦ (hparents gamma hg).1)
    (fun gamma hg ↦ (hparents gamma hg).2) hagreement hnoResidual hd' S.common_slope_le
  have hresidual : (LocatorCover.residual phi seeds S.QA S.QB).card <
      ChainGroupMaj.residMaj6802 d + 1 := by
    simpa only [phi, K, P4, LocatorPhase6800Composition.K,
      LocatorPhase6800Composition.P4, LocatorSelection.K, LocatorSelection.P4]
      using hresidualRaw
  have hpartition := LocatorCover.partition_card phi seeds S.QA S.QB
  have hledger := LocatorArithmetic.ledger_lt
  unfold LocatorArithmetic.ledger LocatorArithmetic.fixedRegularCap at hledger
  unfold LocatorArithmetic.fixedTailCap at hledger hfixed
  simp only [LocatorArithmetic.sB, Nat.reduceSub, Nat.reduceAdd] at hledger hfixed
  omega

theorem selectedNoLargePencilBound6800_of_certificate
    (cert : LocatorPhase6800Composition.PhasePrefixCertificate) :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80781
      LocatorArithmetic.budget := by
  intro U seeds A selected hdegree hcard hvalues hno
  obtain ⟨S⟩ := exists_selected_pair (U 0) (U 1)
  have hA : ∀ gamma ∈ seeds, 181363 ≤ (A gamma).card := by
    intro gamma hg
    have hc := hcard gamma hg
    simpa [I, IRSProfile.Index] using hc
  have hagreement : ∀ gamma ∈ seeds, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          U 0 i + gamma * U 1 i)).card := by
    intro gamma hg
    apply (hA gamma hg).trans
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvalues gamma hg i hi⟩
  have hno' : NoLargeSelectedPencil selected seeds 131071 80781 := by
    intro P0 P1 h0 h1
    simpa only [pencilSeeds] using hno P0 P1 h0 h1
  exact Nat.le_of_lt
    (selected_pair_count_of_certificate cert (U 0) (U 1) S selected seeds
      hdegree hagreement hno')

theorem alignmentBound6800_of_certificate
    (cert : LocatorPhase6800Composition.PhasePrefixCertificate) :
    AffineLineAlignmentBound IRSProfile.baseCode
      LocatorProtocol.errors LocatorProtocol.mcaBudget := by
  have h := alignmentBound_of_selected_count IRSProfile.domain 131071 80781
    LocatorArithmetic.budget
    (selectedNoLargePencilBound6800_of_certificate cert)
  simpa [IRSProfile.baseCode, IRSProfile.baseDimension,
    LocatorArithmetic.budget, LocatorProtocol.errors,
    LocatorProtocol.mcaBudget] using h

theorem protocolClaim6800_of_certificate
    (cert : LocatorPhase6800Composition.PhasePrefixCertificate) :
    ProtocolClaim 6803 10340095 33554432 :=
  LocatorProtocol.protocolClaim6803_of_alignment
    (alignmentBound6800_of_certificate cert)

/-- The non-parameterized benchmark claim obtained from the checked receipt. -/
theorem protocolClaim6803 : ProtocolClaim 6803 10340095 33554432 :=
  protocolClaim6800_of_certificate LocatorPhase6800Certificate.certificate

end

end ProximityPrize.SubmissionLower.LocatorClosure6800
end PackedLocator_LocatorClosure6800
