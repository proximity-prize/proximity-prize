import ProximityPrize.SubmissionLower.LocatorPhase6800Audit
import ProximityPrize.SubmissionLower.LocatorPhase6800Kernels
import ProximityPrize.SubmissionLower.LocatorPhase6800Bridge
import ProximityPrize.SubmissionLower.LocatorPhase6800SourceSound

/-!
# Final composition interface for the 6800 regular-factor certificate

The generated files only need to instantiate `PhasePrefixCertificate`.
Everything from those state-local tables through the four fresh-source
algebraic phases and the correlated initial-A split is composed here.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800Composition

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180
  RCN234 RCN238 RCN243 RCN259 RCN260 RCN266 RCN319
open LocatorSelection LocatorFactorAggregate LocatorBatchPhase6800
  LocatorPhase6800Oracle LocatorPhase6800Audit LocatorPhase6800Kernels
  LocatorPhase6800SourceSound LocatorPhase6800Bridge LocatorFixedBridge

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
    p.all ≤ 28 → middle p ≤ 127 → total p ≤ 5964 →
    afterSplit390 baseCap rPrefix cPrefix f500Prefix s390Prefix p +
      initialAComplement p ≤ LocatorFixedConsumer.initialRegularCap

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
    (hagreement : ∀ gamma ∈ Gamma, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80752)
    (hown : ∀ F ∈ ambient, LocatorHybridCost.OwnBound
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

/-- End-to-end fixed-part theorem.  Once the generated receipt constructs a
`PhasePrefixCertificate`, no algebraic or combinatorial premises remain. -/
theorem gcd_fixed_count_le_of_certificate
    (cert : PhasePrefixCertificate)
    (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma,
      (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80752) :
    (LocatorCover.fixed
      (fun gamma ↦ (specialization K (selected gamma) gamma).toRingHom)
      Gamma S.QA S.QB).card ≤
      LocatorFixedConsumer.initialRegularCap +
        LocatorArithmetic.fixedSingularCap := by
  classical
  let H : P4 := gcd12 S.QA S.QB
  let phi : K → P4 →+* Polynomial K :=
    fun gamma ↦ (specialization K (selected gamma) gamma).toRingHom
  let Delta : Finset K := LocatorCover.fixed phi Gamma S.QA S.QB
  let U := initialAUniversalFactors u0 u1 H
  have hH : H ≠ 0 := by
    simpa only [H, gcd12] using gcd_ne_zero_of_left S.QA_ne
  have hsub : Delta ⊆ Gamma := by
    intro gamma hgamma
    have hm : gamma ∈ Gamma ∧
        phi gamma (gcd12 S.QA S.QB) = 0 := by
      simpa only [Delta, LocatorCover.fixed, Finset.mem_filter] using hgamma
    exact hm.1
  have hdegreeD : ∀ gamma ∈ Delta,
      (selected gamma).natDegree ≤ 131071 :=
    fun gamma hgamma ↦ hdegree gamma (hsub hgamma)
  have hagreementD : ∀ gamma ∈ Delta, 181392 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card :=
    fun gamma hgamma ↦ hagreement gamma (hsub hgamma)
  have hnoD : NoLargeSelectedPencil selected Delta 131071 80752 :=
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80752 hsub hno
  have hown : ∀ F ∈ U, LocatorHybridCost.OwnBound
      (regularSeeds H selected Delta F).card
      (regularCumulativeFlag H F) := by
    intro F hFU
    exact initialA_universal_ownBound u0 u1 H hH S.common_total_le
      selected Delta hdegreeD hagreementD hnoD F hFU
  have hphase := cert.stateLocalBoundOn u0 u1 H selected Delta U
    hdegreeD hagreementD hnoD hown
  apply gcd_fixed_count_le_of_stateLocalPhase u0 u1 S selected Gamma
    hdegree hagreement hno
    (afterSplit390 cert.baseCap cert.rPrefix cert.cPrefix cert.f500Prefix
      cert.s390Prefix)
  · simpa only [H, phi, Delta, U] using hphase
  · intro p hr hs hy ht
    simpa only [initialAHelperCap] using
      initialAHelperCap_le_potential p hr hs hy ht
  · exact cert.joint

end

end ProximityPrize.SubmissionLower.LocatorPhase6800Composition
