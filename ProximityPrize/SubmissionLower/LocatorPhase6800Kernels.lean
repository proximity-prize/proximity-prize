import ProximityPrize.SubmissionLower.LocatorBatchPhase6800
import ProximityPrize.SubmissionLower.LocatorPhase6800SourceSound

/-!
# Concrete kernel realizations and four-phase chain

The analytic source records are paired here with their actual constraint
kernels and isolated finrank receipts.  The final theorem composes the four
state-local transitions while leaving only the compact receipt's cap
equations and defect inequalities as hypotheses.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Kernels

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN095 RCN100 RCN119 RCN130 RCN140 RCN180 RCN238 RCN266
open LocatorBatchPhase6800 LocatorPhase6800Oracle
  LocatorPhase6800SourceSound

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

def r1200Kernel (u0 u1 : I → K) :
    PhaseKernelRealization r1200Sound u0 u1 where
  D := 217670400
  m := 1200
  weighted := LocatorR1200Source.weighted_exact.symm
  shape := by
    simpa only [r1200Sound, sourceR1200] using LocatorR1200Source.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := by
    exact LocatorFastKernelArithmetic.challengeConstraintKernel_finrank_lower_bound_of_numeric
      217670400 82100 370 1200 19825077939631510 u0 u1 (by
        rw [LocatorR1200Source.nullity_exact])

def sourceCKernel (u0 u1 : I → K) :
    PhaseKernelRealization sourceCSound u0 u1 where
  D := 48975840
  m := 270
  weighted := by decide
  shape := by decide
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := by
    exact LocatorFastKernelArithmetic.challengeConstraintKernel_finrank_lower_bound_of_numeric
      48975840 130000 81 270 321495185604514 u0 u1 (by
        rw [LocatorArithmetic.kernelC_nullity])

def split500Kernel (u0 u1 : I → K) :
    PhaseKernelRealization split500Sound u0 u1 where
  D := 90696000
  m := 500
  weighted := LocatorSplit500Source.weighted_exact.symm
  shape := by
    simpa only [split500Sound, sourceSplit500] using
      LocatorSplit500Source.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := by
    exact LocatorFastKernelArithmetic.challengeConstraintKernel_finrank_lower_bound_of_numeric
      90696000 21000 155 500 230574129441305 u0 u1 (by
        rw [LocatorSplit500Source.nullity_exact])

def split390Kernel (u0 u1 : I → K) :
    PhaseKernelRealization split390Sound u0 u1 where
  D := 70742880
  m := 390
  weighted := LocatorSplit390Source.weighted_exact.symm
  shape := by
    simpa only [split390Sound, sourceSplit390] using
      LocatorSplit390Source.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := by
    exact LocatorFastKernelArithmetic.challengeConstraintKernel_finrank_lower_bound_of_numeric
      70742880 19500 120 390 103687669979190 u0 u1 (by
        rw [LocatorSplit390Source.nullity_exact])

/-- Concrete composition of the four fresh-source phases. -/
theorem stateLocalRegularBoundOn_fourPhases
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (ambient : Finset (RegularIndex H))
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80752)
    (baseCap rCap cCap f500Cap s390Cap : FlagDegree → ℕ)
    (rDefect cDefect f500Defect s390Defect : FlagDegree → ℕ)
    (hown : ∀ F ∈ ambient, LocatorHybridCost.OwnBound
      (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F))
    (hbase : StateLocalBaseOracleSound baseCap)
    (hrDefect : PhaseDefectSound baseCap sourceR1200
      r1200Potential rDefect)
    (hrCap : PhaseCapEquation baseCap rCap sourceR1200
      r1200Potential rDefect)
    (hcDefect : PhaseDefectSound rCap sourceC
      sourceCPotential cDefect)
    (hcCap : PhaseCapEquation rCap cCap sourceC
      sourceCPotential cDefect)
    (hfDefect : PhaseDefectSound cCap sourceSplit500
      split500Potential f500Defect)
    (hfCap : PhaseCapEquation cCap f500Cap sourceSplit500
      split500Potential f500Defect)
    (hsDefect : PhaseDefectSound f500Cap sourceSplit390
      split390Potential s390Defect)
    (hsCap : PhaseCapEquation f500Cap s390Cap sourceSplit390
      split390Potential s390Defect) :
    StateLocalRegularBoundOn H selected Gamma ambient s390Cap := by
  have h0 : StateLocalRegularBoundOn H selected Gamma ambient baseCap :=
    stateLocalRegularBoundOn_of_base H selected Gamma ambient
      baseCap hown hbase
  have hR : StateLocalRegularBoundOn H selected Gamma ambient rCap :=
    stateLocalRegularBoundOn_onePhase
      (sound := r1200Sound) (u0 := u0) (u1 := u1)
      (kernel := r1200Kernel u0 u1) (H := H) (selected := selected)
      (Gamma := Gamma) (ambient := ambient) (hdegree := hdegree)
      (hagreement := hagreement) (hno := hno) (previousCap := baseCap)
      (nextCap := rCap) (defect := rDefect) (hprevious := h0)
      (hdefect := by simpa only [r1200Sound] using hrDefect)
      (hcap := by simpa only [r1200Sound] using hrCap)
  have hC : StateLocalRegularBoundOn H selected Gamma ambient cCap :=
    stateLocalRegularBoundOn_onePhase
      (sound := sourceCSound) (u0 := u0) (u1 := u1)
      (kernel := sourceCKernel u0 u1) (H := H) (selected := selected)
      (Gamma := Gamma) (ambient := ambient) (hdegree := hdegree)
      (hagreement := hagreement) (hno := hno) (previousCap := rCap)
      (nextCap := cCap) (defect := cDefect) (hprevious := hR)
      (hdefect := by simpa only [sourceCSound] using hcDefect)
      (hcap := by simpa only [sourceCSound] using hcCap)
  have hF : StateLocalRegularBoundOn H selected Gamma ambient f500Cap :=
    stateLocalRegularBoundOn_onePhase
      (sound := split500Sound) (u0 := u0) (u1 := u1)
      (kernel := split500Kernel u0 u1) (H := H) (selected := selected)
      (Gamma := Gamma) (ambient := ambient) (hdegree := hdegree)
      (hagreement := hagreement) (hno := hno) (previousCap := cCap)
      (nextCap := f500Cap) (defect := f500Defect) (hprevious := hC)
      (hdefect := by simpa only [split500Sound] using hfDefect)
      (hcap := by simpa only [split500Sound] using hfCap)
  exact stateLocalRegularBoundOn_onePhase
    (sound := split390Sound) (u0 := u0) (u1 := u1)
    (kernel := split390Kernel u0 u1) (H := H) (selected := selected)
    (Gamma := Gamma) (ambient := ambient) (hdegree := hdegree)
    (hagreement := hagreement) (hno := hno) (previousCap := f500Cap)
    (nextCap := s390Cap) (defect := s390Defect) (hprevious := hF)
    (hdefect := by simpa only [split390Sound] using hsDefect)
    (hcap := by simpa only [split390Sound] using hsCap)

end

end ProximityPrize.SubmissionLower.LocatorPhase6800Kernels
