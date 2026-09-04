import ProximityPrize.SubmissionLower.LocatorPhase6803Kernels

/-!
# Receipt-facing composition for the 68.03 phase chain

This is the smallest semantic interface the generated receipt must satisfy.
It converts four cumulative prefix tables into the defect and cap contracts
consumed by the four concrete retuned kernels.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6803Composition

open ProximityPrize.Benchmark
open RCN095 RCN100 RCN119 RCN130 RCN140 RCN180 RCN238 RCN266
open LocatorPhase6803Oracle LocatorPhase6803SemanticOracle
open LocatorBatchPhase6803 LocatorPhase6803Kernels
open LocatorPhase6800Audit

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

def afterR1200 (base pref : FlagDegree → ℕ) : FlagDegree → ℕ :=
  applyPhase base r1200Potential sourceR1200.Routeable pref

def afterSourceC (base rPref cPref : FlagDegree → ℕ) : FlagDegree → ℕ :=
  applyPhase (afterR1200 base rPref) sourceCPotential
    sourceC.Routeable cPref

def afterSplit500 (base rPref cPref fPref : FlagDegree → ℕ) :
    FlagDegree → ℕ :=
  applyPhase (afterSourceC base rPref cPref) split500Potential
    sourceSplit500.Routeable fPref

def afterPhase4 (base rPref cPref fPref phase4Pref : FlagDegree → ℕ) :
    FlagDegree → ℕ :=
  applyPhase (afterSplit500 base rPref cPref fPref) phase4Potential
    sourcePhase4.Routeable phase4Pref

/-- Semantic payload to be extracted from the checked 68.03 receipt. -/
structure PhasePrefixCertificate where
  baseCap : FlagDegree → ℕ
  rPrefix : FlagDegree → ℕ
  cPrefix : FlagDegree → ℕ
  f500Prefix : FlagDegree → ℕ
  phase4Prefix : FlagDegree → ℕ
  baseSound : StateLocalBaseOracleSound baseCap
  rRows : PrefixTableSound baseCap r1200Potential
    sourceR1200.Routeable rPrefix
  cRows : PrefixTableSound (afterR1200 baseCap rPrefix) sourceCPotential
    sourceC.Routeable cPrefix
  f500Rows : PrefixTableSound (afterSourceC baseCap rPrefix cPrefix)
    split500Potential sourceSplit500.Routeable f500Prefix
  phase4Rows : PrefixTableSound
    (afterSplit500 baseCap rPrefix cPrefix f500Prefix)
    phase4Potential sourcePhase4.Routeable phase4Prefix

private theorem defectSound_of_prefix
    (previous pref : FlagDegree → ℕ)
    (q : LocatorPhase6800Oracle.Potential)
    (s : LocatorPhase6803Oracle.SourceNumbers)
    (hrows : PrefixTableSound previous q s.Routeable pref) :
    PhaseDefectSound previous s q (parentDefect pref) := by
  intro parent child _hs _hy _ht hstrict hterminal
  apply terminal_le_parent_charge hrows
  · simpa only [LocatorPhase6803SemanticOracle.RawBelow,
      LocatorPhase6800Oracle.RawBelow] using hstrict.1
  · exact hstrict.2
  · exact hterminal

private theorem capEquation_applyPhase
    (previous pref : FlagDegree → ℕ)
    (q : LocatorPhase6800Oracle.Potential)
    (s : LocatorPhase6803Oracle.SourceNumbers) :
    PhaseCapEquation previous
      (applyPhase previous q s.Routeable pref) s q (parentDefect pref) := by
  intro p _hs _hy _ht
  rfl

/-- Four sound prefix tables give the state-local bound on the exact ambient
factor set supplied by the caller. -/
theorem PhasePrefixCertificate.stateLocalBoundOn
    (cert : PhasePrefixCertificate)
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
    (hown : ∀ F ∈ ambient, LocatorHybridCost.OwnBound
      (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F)) :
    StateLocalRegularBoundOn H selected Gamma ambient
      (afterPhase4 cert.baseCap cert.rPrefix cert.cPrefix
        cert.f500Prefix cert.phase4Prefix) := by
  apply stateLocalRegularBoundOn_fourPhases u0 u1 H selected Gamma ambient
    hdegree hagreement hno cert.baseCap
    (afterR1200 cert.baseCap cert.rPrefix)
    (afterSourceC cert.baseCap cert.rPrefix cert.cPrefix)
    (afterSplit500 cert.baseCap cert.rPrefix cert.cPrefix cert.f500Prefix)
    (afterPhase4 cert.baseCap cert.rPrefix cert.cPrefix cert.f500Prefix
      cert.phase4Prefix)
    (parentDefect cert.rPrefix) (parentDefect cert.cPrefix)
    (parentDefect cert.f500Prefix) (parentDefect cert.phase4Prefix)
    hown cert.baseSound
  · exact defectSound_of_prefix cert.baseCap cert.rPrefix r1200Potential
      sourceR1200 cert.rRows
  · exact capEquation_applyPhase cert.baseCap cert.rPrefix r1200Potential
      sourceR1200
  · exact defectSound_of_prefix
      (afterR1200 cert.baseCap cert.rPrefix) cert.cPrefix sourceCPotential
      sourceC cert.cRows
  · exact capEquation_applyPhase
      (afterR1200 cert.baseCap cert.rPrefix) cert.cPrefix sourceCPotential
      sourceC
  · exact defectSound_of_prefix
      (afterSourceC cert.baseCap cert.rPrefix cert.cPrefix) cert.f500Prefix
      split500Potential sourceSplit500 cert.f500Rows
  · exact capEquation_applyPhase
      (afterSourceC cert.baseCap cert.rPrefix cert.cPrefix) cert.f500Prefix
      split500Potential sourceSplit500
  · exact defectSound_of_prefix
      (afterSplit500 cert.baseCap cert.rPrefix cert.cPrefix cert.f500Prefix)
      cert.phase4Prefix phase4Potential sourcePhase4 cert.phase4Rows
  · exact capEquation_applyPhase
      (afterSplit500 cert.baseCap cert.rPrefix cert.cPrefix cert.f500Prefix)
      cert.phase4Prefix phase4Potential sourcePhase4

end

end ProximityPrize.SubmissionLower.LocatorPhase6803Composition
