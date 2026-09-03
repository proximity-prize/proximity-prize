import ProximityPrize.SubmissionLower.LocatorPhase6802Kernels

namespace ProximityPrize.SubmissionLower.LocatorPhase6802Composition

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180
  RCN234 RCN238 RCN243 RCN259 RCN260 RCN266 RCN319
open LocatorSelection LocatorFactorAggregate LocatorBatchPhase6802
  LocatorPhase6802Oracle LocatorPhase6802Audit LocatorPhase6802Kernels
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
local instance : GCDMonoid P4 :=
  UniqueFactorizationMonoid.toGCDMonoid P4

def afterR1200 (base pref : FlagDegree → ℕ) : FlagDegree → ℕ :=
  applyPhase base r1200Potential sourceR1200.Routeable pref

def afterSourceC (base rPref cPref : FlagDegree → ℕ) : FlagDegree → ℕ :=
  applyPhase (afterR1200 base rPref) sourceCPotential
    sourceC.Routeable cPref

def afterSplit500 (base rPref cPref fPref : FlagDegree → ℕ) :
    FlagDegree → ℕ :=
  applyPhase (afterSourceC base rPref cPref) split500Potential
    sourceSplit500.Routeable fPref

def afterSplit390 (base rPref cPref fPref sPref : FlagDegree → ℕ) :
    FlagDegree → ℕ :=
  applyPhase (afterSplit500 base rPref cPref fPref) split390Potential
    sourceSplit390.Routeable sPref

/-- Semantic payload produced by the compact generated receipt. -/
structure PhasePrefixCertificate where
  baseCap : FlagDegree → ℕ
  rPrefix : FlagDegree → ℕ
  cPrefix : FlagDegree → ℕ
  f500Prefix : FlagDegree → ℕ
  s390Prefix : FlagDegree → ℕ
  baseSound : StateLocalBaseOracleSound baseCap
  rRows : PrefixTableSound baseCap r1200Potential
    sourceR1200.Routeable rPrefix
  cRows : PrefixTableSound (afterR1200 baseCap rPrefix) sourceCPotential
    sourceC.Routeable cPrefix
  f500Rows : PrefixTableSound (afterSourceC baseCap rPrefix cPrefix)
    split500Potential sourceSplit500.Routeable f500Prefix
  s390Rows : PrefixTableSound
    (afterSplit500 baseCap rPrefix cPrefix f500Prefix)
    split390Potential sourceSplit390.Routeable s390Prefix
  joint : ∀ p : FlagDegree,
    p.all ≤ 29 → middle p ≤ 132 → total p ≤ 6403 →
    afterSplit390 baseCap rPrefix cPrefix f500Prefix s390Prefix p +
      initialAComplement p ≤ tightenedRegularAllowance

private theorem defectSound_of_prefix
    (previous pref : FlagDegree → ℕ) (q : Potential) (s : SourceNumbers)
    (hrows : PrefixTableSound previous q s.Routeable pref) :
    PhaseDefectSound previous s q (parentDefect pref) := by
  intro parent child _hs _hy _ht hstrict hterminal
  exact terminal_le_parent_charge hrows hstrict.1 hstrict.2 hterminal

private theorem capEquation_applyPhase
    (previous pref : FlagDegree → ℕ) (q : Potential) (s : SourceNumbers) :
    PhaseCapEquation previous
      (applyPhase previous q s.Routeable pref) s q (parentDefect pref) := by
  intro p _hs _hy _ht
  rfl

/-- Four checked prefix tables give the state-local phase bound on exactly
the ambient factors supplied by the initial A split. -/
theorem PhasePrefixCertificate.stateLocalBoundOn
    (cert : PhasePrefixCertificate)
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
    (hown : ∀ F ∈ ambient, LocatorHybridCostC2.OwnBoundC2
      (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F)) :
    StateLocalRegularBoundOn H selected Gamma ambient
      (afterSplit390 cert.baseCap cert.rPrefix cert.cPrefix
        cert.f500Prefix cert.s390Prefix) := by
  apply stateLocalRegularBoundOn_fourPhases u0 u1 H selected Gamma ambient
    hdegree hagreement hno cert.baseCap
    (afterR1200 cert.baseCap cert.rPrefix)
    (afterSourceC cert.baseCap cert.rPrefix cert.cPrefix)
    (afterSplit500 cert.baseCap cert.rPrefix cert.cPrefix cert.f500Prefix)
    (afterSplit390 cert.baseCap cert.rPrefix cert.cPrefix cert.f500Prefix
      cert.s390Prefix)
    (parentDefect cert.rPrefix) (parentDefect cert.cPrefix)
    (parentDefect cert.f500Prefix) (parentDefect cert.s390Prefix)
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
      cert.s390Prefix split390Potential sourceSplit390 cert.s390Rows
  · exact capEquation_applyPhase
      (afterSplit500 cert.baseCap cert.rPrefix cert.cPrefix cert.f500Prefix)
      cert.s390Prefix split390Potential sourceSplit390

end

end ProximityPrize.SubmissionLower.LocatorPhase6802Composition
