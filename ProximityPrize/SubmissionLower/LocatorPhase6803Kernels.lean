import ProximityPrize.SubmissionLower.LocatorBatchPhase6803
import ProximityPrize.SubmissionLower.LocatorR1200Source6803
import ProximityPrize.SubmissionLower.LocatorMiddleSources6803
import ProximityPrize.SubmissionLower.LocatorPhase4Source6803

/-!
# Concrete 68.03 phase kernels and four-phase composition

Each numerical source is paired with its retuned constraint kernel.  The
composition theorem deliberately leaves only the receipt's base, defect, and
cap equations as hypotheses.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6803Kernels

open ProximityPrize.Benchmark
open RCN095 RCN100 RCN119 RCN130 RCN140 RCN180 RCN238 RCN266
open LocatorPhase6803Oracle LocatorPhase6803SemanticOracle
open LocatorBatchPhase6803

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
  D := 870542400
  m := 4800
  weighted := LocatorR1200Source6803.weighted_exact.symm
  shape := by
    change 870542400 + 1480 ≤ 131071 * (6641 + 1)
    exact LocatorR1200Source6803.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := by
    change 5090867013182078230 ≤ Module.finrank K
      (LocatorR1200Source6803.Kernel u0 u1)
    exact LocatorR1200Source6803.finrank_gap u0 u1

def sourceCKernel (u0 u1 : I → K) :
    PhaseKernelRealization sourceCSound u0 u1 where
  D := 217635600
  m := 1200
  weighted := LocatorMiddleSources6803.weightedC_exact.symm
  shape := by
    change 217635600 + 370 ≤ 131071 * (1660 + 1)
    exact LocatorMiddleSources6803.shapeC
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := by
    change 18278038734560710 ≤ Module.finrank K
      (LocatorMiddleSources6803.KernelC u0 u1)
    exact LocatorMiddleSources6803.finrankC_gap u0 u1

def split500Kernel (u0 u1 : I → K) :
    PhaseKernelRealization split500Sound u0 u1 where
  D := 181363000
  m := 1000
  weighted := LocatorMiddleSources6803.weightedSplit500_exact.symm
  shape := by
    change 181363000 + 310 ≤ 131071 * (1383 + 1)
    exact LocatorMiddleSources6803.shapeSplit500
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := by
    change 4003459072456058 ≤ Module.finrank K
      (LocatorMiddleSources6803.KernelSplit500 u0 u1)
    exact LocatorMiddleSources6803.finrankSplit500_gap u0 u1

def phase4Kernel (u0 u1 : I → K) :
    PhaseKernelRealization phase4Sound u0 u1 where
  D := 63477050
  m := 350
  weighted := LocatorPhase4Source6803.weighted_exact.symm
  shape := by
    change 63477050 + 106 ≤ 131071 * (484 + 1)
    exact LocatorPhase4Source6803.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := by
    change 92137303795050 ≤ Module.finrank K
      (LocatorPhase4Source6803.Kernel u0 u1)
    exact LocatorPhase4Source6803.finrank_gap u0 u1

/-- Concrete composition of the four retuned sources. -/
theorem stateLocalRegularBoundOn_fourPhases
    (u0 u1 : I → K) (H : P4)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (ambient : Finset (RegularIndex H))
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781)
    (baseCap rCap cCap f500Cap phase4Cap : FlagDegree → ℕ)
    (rDefect cDefect f500Defect phase4Defect : FlagDegree → ℕ)
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
    (h4Defect : PhaseDefectSound f500Cap sourcePhase4
      phase4Potential phase4Defect)
    (h4Cap : PhaseCapEquation f500Cap phase4Cap sourcePhase4
      phase4Potential phase4Defect) :
    StateLocalRegularBoundOn H selected Gamma ambient phase4Cap := by
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
      (hdefect := hrDefect) (hcap := hrCap)
  have hC : StateLocalRegularBoundOn H selected Gamma ambient cCap :=
    stateLocalRegularBoundOn_onePhase
      (sound := sourceCSound) (u0 := u0) (u1 := u1)
      (kernel := sourceCKernel u0 u1) (H := H) (selected := selected)
      (Gamma := Gamma) (ambient := ambient) (hdegree := hdegree)
      (hagreement := hagreement) (hno := hno) (previousCap := rCap)
      (nextCap := cCap) (defect := cDefect) (hprevious := hR)
      (hdefect := hcDefect) (hcap := hcCap)
  have hF : StateLocalRegularBoundOn H selected Gamma ambient f500Cap :=
    stateLocalRegularBoundOn_onePhase
      (sound := split500Sound) (u0 := u0) (u1 := u1)
      (kernel := split500Kernel u0 u1) (H := H) (selected := selected)
      (Gamma := Gamma) (ambient := ambient) (hdegree := hdegree)
      (hagreement := hagreement) (hno := hno) (previousCap := cCap)
      (nextCap := f500Cap) (defect := f500Defect) (hprevious := hC)
      (hdefect := hfDefect) (hcap := hfCap)
  exact stateLocalRegularBoundOn_onePhase
    (sound := phase4Sound) (u0 := u0) (u1 := u1)
    (kernel := phase4Kernel u0 u1) (H := H) (selected := selected)
    (Gamma := Gamma) (ambient := ambient) (hdegree := hdegree)
    (hagreement := hagreement) (hno := hno) (previousCap := f500Cap)
    (nextCap := phase4Cap) (defect := phase4Defect) (hprevious := hF)
    (hdefect := h4Defect) (hcap := h4Cap)

end

end ProximityPrize.SubmissionLower.LocatorPhase6803Kernels
