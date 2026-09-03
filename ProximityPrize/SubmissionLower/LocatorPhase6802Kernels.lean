import ProximityPrize.SubmissionLower.LocatorKernels6802Arithmetic

/-! Concrete 6802 kernel realizations and the four-phase C2 chain. -/

namespace ProximityPrize.SubmissionLower.LocatorPhase6802Kernels

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN095 RCN100 RCN119 RCN130 RCN140 RCN180 RCN238 RCN266
open LocatorBatchPhase6802 LocatorPhase6802Oracle
  LocatorPhase6802SourceSound

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
  D := 870590400
  m := 4800
  weighted := by decide
  shape := by decide
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := by
    exact LocatorFastKernelArithmetic.challengeConstraintKernel_finrank_lower_bound_of_numeric
      870590400 300000 1477 4800 4607803177954025032 u0 u1 (by
        rw [LocatorKernels6802Arithmetic.nullity_R4800L300k])

def sourceCKernel (u0 u1 : I → K) :
    PhaseKernelRealization sourceCSound u0 u1 where
  D := 435295200
  m := 2400
  weighted := by decide
  shape := by decide
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := by
    exact LocatorFastKernelArithmetic.challengeConstraintKernel_finrank_lower_bound_of_numeric
      435295200 200000 738 2400 410735023077819764 u0 u1 (by
        rw [LocatorKernels6802Arithmetic.nullity_R2400L200k])

def split500Kernel (u0 u1 : I → K) :
    PhaseKernelRealization split500Sound u0 u1 where
  D := 217647600
  m := 1200
  weighted := by decide
  shape := by decide
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := by
    exact LocatorFastKernelArithmetic.challengeConstraintKernel_finrank_lower_bound_of_numeric
      217647600 82100 370 1200 18811500529412710 u0 u1 (by
        rw [LocatorKernels6802Arithmetic.nullity_R1200])

def split390Kernel (u0 u1 : I → K) :
    PhaseKernelRealization split390Sound u0 u1 where
  D := 70735470
  m := 390
  weighted := by decide
  shape := by decide
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := by
    exact LocatorFastKernelArithmetic.challengeConstraintKernel_finrank_lower_bound_of_numeric
      70735470 19500 120 390 95423319727890 u0 u1 (by
        rw [LocatorKernels6802Arithmetic.nullity_Split390])

theorem stateLocalRegularBoundOn_fourPhases
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (ambient : Finset (RegularIndex H))
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181373 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80771)
    (baseCap rCap cCap f500Cap s390Cap : FlagDegree → ℕ)
    (rDefect cDefect f500Defect s390Defect : FlagDegree → ℕ)
    (hown : ∀ F ∈ ambient, LocatorHybridCostC2.OwnBoundC2
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

end ProximityPrize.SubmissionLower.LocatorPhase6802Kernels
