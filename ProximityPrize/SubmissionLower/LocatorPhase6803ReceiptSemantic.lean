import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData01
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData02
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData03
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData04
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData05
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData06
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData07
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData08
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData09
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData10
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData11
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData12
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData13
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData14
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData15
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData16
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData17
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData18
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData19
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData20
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData21
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData22
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData23
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData24
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData25
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData26
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData27
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData28
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptRowData29
import ProximityPrize.SubmissionLower.LocatorPhase6803Composition

/-!
# Semantic interpretation of the checked 68.03 receipt

This module gives the generated row certificate a flat, zero-safe lookup and
extracts the four prefix-table contracts used by `PhasePrefixCertificate`.
Base-envelope soundness is an explicit input: it is supplied by the separate
ordinary-cost audit rather than inferred from the generated row shape.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptSemantic

open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (Potential BaseRow ThresholdReceipt PrefixReceipt
  rawFlag rawFlag_all rawFlag_middle rawFlag_total)
open LocatorPhase6800Audit (PrefixTableSound parentDefect applyPhase)
open LocatorPhase6803Oracle
open LocatorPhase6803ReceiptCore
open LocatorPhase6803SemanticOracle
open LocatorPhase6803Composition

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def lookupBase : ℕ → ℕ → BaseRow
  | 1 => LocatorPhase6803ReceiptRowData01.base
  | 2 => LocatorPhase6803ReceiptRowData02.base
  | 3 => LocatorPhase6803ReceiptRowData03.base
  | 4 => LocatorPhase6803ReceiptRowData04.base
  | 5 => LocatorPhase6803ReceiptRowData05.base
  | 6 => LocatorPhase6803ReceiptRowData06.base
  | 7 => LocatorPhase6803ReceiptRowData07.base
  | 8 => LocatorPhase6803ReceiptRowData08.base
  | 9 => LocatorPhase6803ReceiptRowData09.base
  | 10 => LocatorPhase6803ReceiptRowData10.base
  | 11 => LocatorPhase6803ReceiptRowData11.base
  | 12 => LocatorPhase6803ReceiptRowData12.base
  | 13 => LocatorPhase6803ReceiptRowData13.base
  | 14 => LocatorPhase6803ReceiptRowData14.base
  | 15 => LocatorPhase6803ReceiptRowData15.base
  | 16 => LocatorPhase6803ReceiptRowData16.base
  | 17 => LocatorPhase6803ReceiptRowData17.base
  | 18 => LocatorPhase6803ReceiptRowData18.base
  | 19 => LocatorPhase6803ReceiptRowData19.base
  | 20 => LocatorPhase6803ReceiptRowData20.base
  | 21 => LocatorPhase6803ReceiptRowData21.base
  | 22 => LocatorPhase6803ReceiptRowData22.base
  | 23 => LocatorPhase6803ReceiptRowData23.base
  | 24 => LocatorPhase6803ReceiptRowData24.base
  | 25 => LocatorPhase6803ReceiptRowData25.base
  | 26 => LocatorPhase6803ReceiptRowData26.base
  | 27 => LocatorPhase6803ReceiptRowData27.base
  | 28 => LocatorPhase6803ReceiptRowData28.base
  | 29 => LocatorPhase6803ReceiptRowData29.base
  | _ => fun _ => LocatorPhase6800Oracle.defaultBaseRow

def lookupThreshold : ℕ → ℕ → ThresholdReceipt
  | 1 => LocatorPhase6803ReceiptRowData01.threshold
  | 2 => LocatorPhase6803ReceiptRowData02.threshold
  | 3 => LocatorPhase6803ReceiptRowData03.threshold
  | 4 => LocatorPhase6803ReceiptRowData04.threshold
  | 5 => LocatorPhase6803ReceiptRowData05.threshold
  | 6 => LocatorPhase6803ReceiptRowData06.threshold
  | 7 => LocatorPhase6803ReceiptRowData07.threshold
  | 8 => LocatorPhase6803ReceiptRowData08.threshold
  | 9 => LocatorPhase6803ReceiptRowData09.threshold
  | 10 => LocatorPhase6803ReceiptRowData10.threshold
  | 11 => LocatorPhase6803ReceiptRowData11.threshold
  | 12 => LocatorPhase6803ReceiptRowData12.threshold
  | 13 => LocatorPhase6803ReceiptRowData13.threshold
  | 14 => LocatorPhase6803ReceiptRowData14.threshold
  | 15 => LocatorPhase6803ReceiptRowData15.threshold
  | 16 => LocatorPhase6803ReceiptRowData16.threshold
  | 17 => LocatorPhase6803ReceiptRowData17.threshold
  | 18 => LocatorPhase6803ReceiptRowData18.threshold
  | 19 => LocatorPhase6803ReceiptRowData19.threshold
  | 20 => LocatorPhase6803ReceiptRowData20.threshold
  | 21 => LocatorPhase6803ReceiptRowData21.threshold
  | 22 => LocatorPhase6803ReceiptRowData22.threshold
  | 23 => LocatorPhase6803ReceiptRowData23.threshold
  | 24 => LocatorPhase6803ReceiptRowData24.threshold
  | 25 => LocatorPhase6803ReceiptRowData25.threshold
  | 26 => LocatorPhase6803ReceiptRowData26.threshold
  | 27 => LocatorPhase6803ReceiptRowData27.threshold
  | 28 => LocatorPhase6803ReceiptRowData28.threshold
  | 29 => LocatorPhase6803ReceiptRowData29.threshold
  | _ => fun _ => defaultThreshold

def lookupPrefix : ℕ → ℕ → PrefixReceipt
  | 1 => LocatorPhase6803ReceiptRowData01.prefixData
  | 2 => LocatorPhase6803ReceiptRowData02.prefixData
  | 3 => LocatorPhase6803ReceiptRowData03.prefixData
  | 4 => LocatorPhase6803ReceiptRowData04.prefixData
  | 5 => LocatorPhase6803ReceiptRowData05.prefixData
  | 6 => LocatorPhase6803ReceiptRowData06.prefixData
  | 7 => LocatorPhase6803ReceiptRowData07.prefixData
  | 8 => LocatorPhase6803ReceiptRowData08.prefixData
  | 9 => LocatorPhase6803ReceiptRowData09.prefixData
  | 10 => LocatorPhase6803ReceiptRowData10.prefixData
  | 11 => LocatorPhase6803ReceiptRowData11.prefixData
  | 12 => LocatorPhase6803ReceiptRowData12.prefixData
  | 13 => LocatorPhase6803ReceiptRowData13.prefixData
  | 14 => LocatorPhase6803ReceiptRowData14.prefixData
  | 15 => LocatorPhase6803ReceiptRowData15.prefixData
  | 16 => LocatorPhase6803ReceiptRowData16.prefixData
  | 17 => LocatorPhase6803ReceiptRowData17.prefixData
  | 18 => LocatorPhase6803ReceiptRowData18.prefixData
  | 19 => LocatorPhase6803ReceiptRowData19.prefixData
  | 20 => LocatorPhase6803ReceiptRowData20.prefixData
  | 21 => LocatorPhase6803ReceiptRowData21.prefixData
  | 22 => LocatorPhase6803ReceiptRowData22.prefixData
  | 23 => LocatorPhase6803ReceiptRowData23.prefixData
  | 24 => LocatorPhase6803ReceiptRowData24.prefixData
  | 25 => LocatorPhase6803ReceiptRowData25.prefixData
  | 26 => LocatorPhase6803ReceiptRowData26.prefixData
  | 27 => LocatorPhase6803ReceiptRowData27.prefixData
  | 28 => LocatorPhase6803ReceiptRowData28.prefixData
  | 29 => LocatorPhase6803ReceiptRowData29.prefixData
  | _ => fun _ => defaultPrefix

def previousPrefix : ℕ → ℕ → PrefixReceipt
  | 1 => fun _ => zeroPrefix
  | R + 1 => lookupPrefix R
  | _ => fun _ => zeroPrefix

def NarrowState (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ p.all ≤ slopeCap ∧ middle p ≤ middleCap ∧
    total p ≤ totalCap

instance (p : FlagDegree) : Decidable (NarrowState p) := by
  unfold NarrowState
  infer_instance

def checkedBaseCap (p : FlagDegree) : ℕ :=
  if NarrowState p then (lookupBase p.all p.yz).evalAt p.zOnly else 0

@[simp] theorem checkedBaseCap_of_narrow {p : FlagDegree} (hp : NarrowState p) :
    checkedBaseCap p = (lookupBase p.all p.yz).evalAt p.zOnly := by
  simp [checkedBaseCap, hp]

@[simp] theorem checkedBaseCap_of_not_narrow {p : FlagDegree}
    (hp : ¬ NarrowState p) : checkedBaseCap p = 0 := by
  simp [checkedBaseCap, hp]

def PrefixValid (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ p.all ≤ 28 ∧ p.all + 1 + p.yz ≤ middleCap ∧
    p.all + 1 + p.yz + p.zOnly ≤ totalCap

instance (p : FlagDegree) : Decidable (PrefixValid p) := by
  unfold PrefixValid
  infer_instance

def prefixCore (phase : ℕ) (p : FlagDegree) : ℕ :=
  prefixAt (lookupPrefix p.all p.yz) phase

def satPrefix (phase : ℕ) (p : FlagDegree) : ℕ :=
  if p.all = 0 then 0
  else if PrefixValid p then prefixCore phase p else prefixSentinel

def rPrefix : FlagDegree → ℕ := satPrefix 0
def cPrefix : FlagDegree → ℕ := satPrefix 1
def f500Prefix : FlagDegree → ℕ := satPrefix 2
def phase4Prefix : FlagDegree → ℕ := satPrefix 3

def rThreshold (r v : ℕ) : ℕ := thresholdAt (lookupThreshold r v) 0
def cThreshold (r v : ℕ) : ℕ := thresholdAt (lookupThreshold r v) 1
def f500Threshold (r v : ℕ) : ℕ := thresholdAt (lookupThreshold r v) 2
def phase4Threshold (r v : ℕ) : ℕ := thresholdAt (lookupThreshold r v) 3

/-- Pointwise interface exported by the sharded executable certificate. -/
structure CheckedRows : Prop where
  stateAt : ∀ R V, 1 ≤ R → R ≤ 29 → R + V ≤ middleCap →
    StateValid R V (lookupBase R V) (lookupThreshold R V)
      (lookupPrefix R V) (previousPrefix R V)
  prefixRowsAt : ∀ R V, 1 ≤ R → R ≤ 28 → R + 1 + V ≤ middleCap →
    let q := lookupPrefix R V
    q.afterR = R ∧ q.v = V ∧
      (∀ phase ∈ List.range 4, prefixAt q phase ≤ prefixSentinel) ∧
      (R + 1 ≤ 28 → ∀ phase ∈ List.range 4,
        prefixAt q phase ≤ prefixAt (lookupPrefix (R + 1) V) phase) ∧
      (R + 1 + (V + 1) ≤ middleCap → ∀ phase ∈ List.range 4,
        prefixAt q phase ≤ prefixAt (lookupPrefix R (V + 1)) phase)

theorem stateValid_at (cert : CheckedRows) (R V : ℕ)
    (hR : 1 ≤ R) (hR29 : R ≤ 29) (hRV : R + V ≤ middleCap) :
    StateValid R V (lookupBase R V) (lookupThreshold R V)
      (lookupPrefix R V) (previousPrefix R V) :=
  cert.stateAt R V hR hR29 hRV

theorem prefixValid_at (cert : CheckedRows) (R V : ℕ)
    (hR : 1 ≤ R) (hR28 : R ≤ 28) (hRV : R + 1 + V ≤ middleCap) :
    let q := lookupPrefix R V
    q.afterR = R ∧ q.v = V ∧
      (∀ phase ∈ List.range 4, prefixAt q phase ≤ prefixSentinel) ∧
      (R + 1 ≤ 28 → ∀ phase ∈ List.range 4,
        prefixAt q phase ≤ prefixAt (lookupPrefix (R + 1) V) phase) ∧
      (R + 1 + (V + 1) ≤ middleCap → ∀ phase ∈ List.range 4,
        prefixAt q phase ≤ prefixAt (lookupPrefix R (V + 1)) phase) :=
  cert.prefixRowsAt R V hR hR28 hRV

/-! ## Threshold cutoffs -/

private theorem powerBandBudget_mono_fuel_6803
    (delta dT dY dS T YS S : ℕ) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    LocatorArbitraryPowerAvoidance.powerBandBudget delta dT dY dS T YS S k₁ ≤
      LocatorArbitraryPowerAvoidance.powerBandBudget delta dT dY dS T YS S k₂ :=
  LocatorPhase6800Audit.powerBandBudget_mono_fuel delta dT dY dS T YS S hk

/-- At fixed slope and middle coordinates, raising the raw `z` coordinate can
only make a retuned source easier to route. -/
theorem routeable_raw_mono_z
    (s : SourceNumbers) {r v z₁ z₂ : ℕ}
    (hz : z₁ ≤ z₂) (hcap : r + v + z₂ ≤ s.totalCap)
    (hroute : s.Routeable (rawFlag r v z₁)) :
    s.Routeable (rawFlag r v z₂) := by
  rcases hroute with ⟨hr, ht, hy, hs, hband⟩
  have htotal : r + v + z₁ ≤ r + v + z₂ := by omega
  have hpos : 0 < r + v + z₁ := by
    have : 1 ≤ r := by simpa only [rawFlag_all] using hr
    omega
  have hdiv : s.totalCap / (r + v + z₂) ≤
      s.totalCap / (r + v + z₁) :=
    Nat.div_le_div_left htotal hpos
  have hfuel : s.fuel (rawFlag r v z₂) ≤
      s.fuel (rawFlag r v z₁) := by
    unfold SourceNumbers.fuel
    simp only [rawFlag_total, rawFlag_middle, rawFlag_all]
    exact min_le_min hdiv le_rfl
  have hbox : s.totalCap - (r + v + z₂) ≤
      s.totalCap - (r + v + z₁) := Nat.sub_le_sub_left htotal _
  have hsameFuel :
      LocatorArbitraryPowerAvoidance.powerBandBudget 50293
          (r + v + z₂) (r + v) r (s.totalCap - (r + v + z₂))
          (s.middleCap - (r + v)) (s.slopeCap - r)
          (s.fuel (rawFlag r v z₂)) ≤
        LocatorArbitraryPowerAvoidance.powerBandBudget 50293
          (r + v + z₁) (r + v) r (s.totalCap - (r + v + z₁))
          (s.middleCap - (r + v)) (s.slopeCap - r)
          (s.fuel (rawFlag r v z₂)) := by
    exact LocatorArbitraryPowerAvoidance.powerBandBudget_mono 50293
      (r + v + z₂) (r + v) r
      (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
      (s.slopeCap - r)
      (r + v + z₁) (r + v) r
      (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
      (s.slopeCap - r) (s.fuel (rawFlag r v z₂))
      hbox le_rfl le_rfl htotal le_rfl le_rfl
  have hmoreFuel :
      LocatorArbitraryPowerAvoidance.powerBandBudget 50293
          (r + v + z₁) (r + v) r (s.totalCap - (r + v + z₁))
          (s.middleCap - (r + v)) (s.slopeCap - r)
          (s.fuel (rawFlag r v z₂)) ≤
        LocatorArbitraryPowerAvoidance.powerBandBudget 50293
          (r + v + z₁) (r + v) r (s.totalCap - (r + v + z₁))
          (s.middleCap - (r + v)) (s.slopeCap - r)
          (s.fuel (rawFlag r v z₁)) :=
    powerBandBudget_mono_fuel_6803 50293 (r + v + z₁) (r + v) r
      (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
      (s.slopeCap - r) hfuel
  refine ⟨hr, ?_, ?_, ?_, ?_⟩
  · simpa only [rawFlag_total] using hcap
  · simpa only [rawFlag_middle] using hy
  · simpa only [rawFlag_all] using hs
  · rcases hband with hband | hthin
    · left
      unfold SourceNumbers.band at hband ⊢
      simp only [rawFlag_total, rawFlag_middle, rawFlag_all] at hband ⊢
      exact (hsameFuel.trans hmoreFuel).trans_lt hband
    · right
      have hsameFuelT :
          LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
              (s.contactCap (rawFlag r v z₂)) 50293
              (contactDec (rawFlag r v z₂)) (r + v + z₂) (r + v) r
              (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
            LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
              (s.contactCap (rawFlag r v z₁)) 50293
              (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
              (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) := by
        have hc : s.contactCap (rawFlag r v z₂) =
            s.contactCap (rawFlag r v z₁) := by
          simp [SourceNumbers.contactCap, contactDec]
        have hd : contactDec (rawFlag r v z₂) =
            contactDec (rawFlag r v z₁) := by
          simp [contactDec]
        rw [hc, hd]
        exact LocatorArbitraryPowerAvoidance.powerBandBudgetThin_mono
          131071 50293 (s.fuel (rawFlag r v z₂))
          (s.contactCap (rawFlag r v z₁)) (contactDec (rawFlag r v z₁))
          (r + v + z₂) (r + v) r
          (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
          (s.slopeCap - r)
          (s.contactCap (rawFlag r v z₁)) (contactDec (rawFlag r v z₁))
          (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) le_rfl le_rfl hbox le_rfl le_rfl htotal le_rfl le_rfl
      have hmoreFuelT :
          LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
              (s.contactCap (rawFlag r v z₁)) 50293
              (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
              (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
            LocatorArbitraryPowerAvoidance.powerBandBudgetThin 131071
              (s.contactCap (rawFlag r v z₁)) 50293
              (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
              (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₁)) :=
        LocatorArbitraryPowerAvoidance.powerBandBudgetThin_mono_fuel 131071
          (s.contactCap (rawFlag r v z₁)) 50293
          (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) hfuel
      unfold SourceNumbers.bandThin at hthin ⊢
      simp only [rawFlag_total, rawFlag_middle, rawFlag_all] at hthin ⊢
      exact (hsameFuelT.trans hmoreFuelT).trans_lt hthin

theorem thresholdSufficient_at (cert : CheckedRows) (phase R V : ℕ)
    (hphase : phase < 4) (hR : 1 ≤ R) (hR29 : R ≤ 29)
    (hRV : R + V ≤ middleCap) :
    SourceThresholdSufficient (phaseSource phase) R V
      (thresholdAt (lookupThreshold R V) phase) := by
  have h := (stateValid_at cert R V hR hR29 hRV).2.1
  rcases h with ⟨_, _, _, _, _, h₀, h₁, h₂, h₃⟩
  interval_cases phase <;>
    simp_all only [phaseSource, thresholdAt]

theorem routeable_of_cutoff (cert : CheckedRows) (phase : ℕ)
    (hphase : phase < 4) (p : FlagDegree) (hp : NarrowState p) :
    thresholdAt (lookupThreshold p.all p.yz) phase ≤ p.zOnly →
      (phaseSource phase).Routeable p := by
  rcases hp with ⟨hr, hs, hm, ht⟩
  have hRV : p.all + p.yz ≤ middleCap := by
    simpa only [middle, Nat.add_comm] using hm
  have hsuff := thresholdSufficient_at cert phase p.all p.yz hphase hr hs hRV
  intro hthreshold
  rcases hsuff with hout | hroute
  · have hz : p.zOnly ≤ totalCap - (p.all + p.yz) := by
      simp only [total] at ht
      omega
    omega
  · have hsourceCap : totalCap ≤ (phaseSource phase).totalCap := by
      interval_cases phase <;>
        norm_num [totalCap, phaseSource, LocatorPhase6803Oracle.sourceR1200,
          LocatorPhase6803Oracle.sourceC,
          LocatorPhase6803Oracle.sourceSplit500,
          LocatorPhase6803Oracle.sourcePhase4]
    have hcap : p.all + p.yz + p.zOnly ≤ (phaseSource phase).totalCap := by
      simp only [total] at ht
      omega
    have hmz := routeable_raw_mono_z (phaseSource phase) hthreshold hcap hroute
    simpa only [rawFlag] using hmz

/-! ## Saturated-prefix monotonicity -/

structure CoreGridSound (cert : CheckedRows) (phase : ℕ) : Prop where
  top : ∀ p, PrefixValid p → prefixCore phase p ≤ prefixSentinel
  stepR : ∀ r v z, 1 ≤ r → PrefixValid (rawFlag (r + 1) v z) →
    prefixCore phase (rawFlag r v z) ≤
      prefixCore phase (rawFlag (r + 1) v z)
  stepV : ∀ r v z, PrefixValid (rawFlag r (v + 1) z) →
    prefixCore phase (rawFlag r v z) ≤
      prefixCore phase (rawFlag r (v + 1) z)
  stepZ : ∀ r v z, PrefixValid (rawFlag r v (z + 1)) →
    prefixCore phase (rawFlag r v z) ≤
      prefixCore phase (rawFlag r v (z + 1))

theorem coreGridSound (cert : CheckedRows) (phase : ℕ) (hphase : phase < 4) :
    CoreGridSound cert phase := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases hp with ⟨hr, hr28, hmiddle, _⟩
    exact (prefixValid_at cert p.all p.yz hr hr28 hmiddle).2.2.1 phase
      (List.mem_range.mpr hphase)
  · intro r v z hr hvalid
    have hr28 : r ≤ 28 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrv : r + 1 + v ≤ middleCap := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrow := prefixValid_at cert r v hr hr28 hrv
    have hstep := hrow.2.2.2.1 (by
      simp only [PrefixValid, rawFlag] at hvalid
      omega) phase (List.mem_range.mpr hphase)
    simpa only [prefixCore, rawFlag] using hstep
  · intro r v z hvalid
    have hr : 1 ≤ r := by
      simpa only [PrefixValid, rawFlag] using hvalid.1
    have hr28 : r ≤ 28 := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrv : r + 1 + v ≤ middleCap := by
      simp only [PrefixValid, rawFlag] at hvalid
      omega
    have hrow := prefixValid_at cert r v hr hr28 hrv
    have hstep := hrow.2.2.2.2 (by
      simp only [PrefixValid, rawFlag] at hvalid
      omega) phase (List.mem_range.mpr hphase)
    simpa only [prefixCore, rawFlag] using hstep
  · intro r v z _
    rfl

private theorem core_mono_add_r
    {cert : CheckedRows} {phase : ℕ} (h : CoreGridSound cert phase)
    (r v z d : ℕ) (hr : 1 ≤ r)
    (hvalid : PrefixValid (rawFlag (r + d) v z)) :
    prefixCore phase (rawFlag r v z) ≤
      prefixCore phase (rawFlag (r + d) v z) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hprev : PrefixValid (rawFlag (r + d) v z) := by
        simp only [PrefixValid, rawFlag] at hvalid ⊢
        omega
      exact (ih hprev).trans (by
        simpa only [Nat.add_assoc] using h.stepR (r + d) v z (by omega)
          (by simpa only [Nat.add_assoc] using hvalid))

private theorem core_mono_add_v
    {cert : CheckedRows} {phase : ℕ} (h : CoreGridSound cert phase)
    (r v z d : ℕ) (hvalid : PrefixValid (rawFlag r (v + d) z)) :
    prefixCore phase (rawFlag r v z) ≤
      prefixCore phase (rawFlag r (v + d) z) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hprev : PrefixValid (rawFlag r (v + d) z) := by
        simp only [PrefixValid, rawFlag] at hvalid ⊢
        omega
      exact (ih hprev).trans (by
        simpa only [Nat.add_assoc] using h.stepV r (v + d) z
          (by simpa only [Nat.add_assoc] using hvalid))

private theorem core_mono_add_z
    {cert : CheckedRows} {phase : ℕ} (h : CoreGridSound cert phase)
    (r v z d : ℕ) (hvalid : PrefixValid (rawFlag r v (z + d))) :
    prefixCore phase (rawFlag r v z) ≤
      prefixCore phase (rawFlag r v (z + d)) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hprev : PrefixValid (rawFlag r v (z + d)) := by
        simp only [PrefixValid, rawFlag] at hvalid ⊢
        omega
      exact (ih hprev).trans (by
        simpa only [Nat.add_assoc] using h.stepZ r v (z + d)
          (by simpa only [Nat.add_assoc] using hvalid))

private theorem core_mono_of_grid
    {cert : CheckedRows} {phase : ℕ} (h : CoreGridSound cert phase)
    {p₁ p₂ : FlagDegree} (hp₁ : PrefixValid p₁) (hp₂ : PrefixValid p₂)
    (hbelow : LocatorPhase6800Oracle.RawBelow p₁ p₂) :
    prefixCore phase p₁ ≤ prefixCore phase p₂ := by
  rcases p₁ with ⟨z₁, v₁, r₁⟩
  rcases p₂ with ⟨z₂, v₂, r₂⟩
  change r₁ ≤ r₂ ∧ v₁ ≤ v₂ ∧ z₁ ≤ z₂ at hbelow
  rcases hbelow with ⟨hr, hv, hz⟩
  have hr₁ : 1 ≤ r₁ := by simpa [PrefixValid] using hp₁.1
  obtain ⟨dr, rfl⟩ := Nat.exists_eq_add_of_le hr
  obtain ⟨dv, rfl⟩ := Nat.exists_eq_add_of_le hv
  obtain ⟨dz, rfl⟩ := Nat.exists_eq_add_of_le hz
  have hR := core_mono_add_r h r₁ v₁ z₁ dr hr₁ (by
    simp only [PrefixValid, rawFlag] at hp₂ ⊢
    omega)
  have hV := core_mono_add_v h (r₁ + dr) v₁ z₁ dv (by
    simp only [PrefixValid, rawFlag] at hp₂ ⊢
    omega)
  have hZ := core_mono_add_z h (r₁ + dr) (v₁ + dv) z₁ dz (by
    simpa only [PrefixValid, rawFlag] using hp₂)
  exact hR.trans (hV.trans hZ)

theorem satPrefix_mono (cert : CheckedRows) (phase : ℕ) (hphase : phase < 4) :
    ∀ {p₁ p₂}, LocatorPhase6800Oracle.RawBelow p₁ p₂ →
      satPrefix phase p₁ ≤ satPrefix phase p₂ := by
  intro p₁ p₂ hbelow
  by_cases hp₁zero : p₁.all = 0
  · simp [satPrefix, hp₁zero]
  have hp₂zero : p₂.all ≠ 0 := by
    intro hp₂zero
    exact hp₁zero (Nat.eq_zero_of_le_zero (hp₂zero ▸ hbelow.1))
  by_cases hp₂valid : PrefixValid p₂
  · have hp₁valid : PrefixValid p₁ := by
      unfold PrefixValid at hp₂valid ⊢
      unfold LocatorPhase6800Oracle.RawBelow at hbelow
      omega
    simp only [satPrefix, if_neg hp₁zero, if_neg hp₂zero,
      if_pos hp₁valid, if_pos hp₂valid]
    exact core_mono_of_grid (coreGridSound cert phase hphase)
      hp₁valid hp₂valid hbelow
  · by_cases hp₁valid : PrefixValid p₁
    · simp only [satPrefix, if_neg hp₁zero, if_neg hp₂zero,
        if_pos hp₁valid, if_neg hp₂valid]
      exact (coreGridSound cert phase hphase).top p₁ hp₁valid
    · simp [satPrefix, hp₁zero, hp₂zero, hp₁valid, hp₂valid]

def PrefixTopChecks : Prop :=
  ∀ R ∈ List.range 30, 1 ≤ R →
    ∀ V ∈ List.range (middleCap + 1 - R),
      ∀ phase ∈ List.range 4,
        prefixAt (lookupPrefix R V) phase ≤ prefixSentinel

instance : Decidable PrefixTopChecks := by
  unfold PrefixTopChecks
  infer_instance

theorem prefixTopChecked : PrefixTopChecks := by native_decide

theorem prefixCore_le_satPrefix (phase : ℕ) (hphase : phase < 4)
    (p : FlagDegree) (hp : NarrowState p) :
    prefixCore phase p ≤ satPrefix phase p := by
  rcases hp with ⟨hr, hs, hm, _⟩
  have hs29 : p.all ≤ 29 := by simpa [slopeCap] using hs
  have hRV : p.all + p.yz ≤ middleCap := by
    simpa only [middle, Nat.add_comm] using hm
  have htop : prefixCore phase p ≤ prefixSentinel := by
    exact prefixTopChecked p.all (List.mem_range.mpr (by omega)) hr p.yz
      (List.mem_range.mpr (by omega)) phase (List.mem_range.mpr hphase)
  have hne : p.all ≠ 0 := Nat.one_le_iff_ne_zero.mp hr
  by_cases hvalid : PrefixValid p
  · simp [satPrefix, hne, hvalid]
  · simpa [satPrefix, hne, hvalid] using htop

/-! ## Checked recurrence and semantic terminal rows -/

theorem parentDefect_eq_previousPrefix (phase R V z : ℕ)
    (hphase : phase < 4) (hR : 1 ≤ R) (hR29 : R ≤ 29)
    (hRV : R + V ≤ middleCap) (hRVz : R + V + z ≤ totalCap) :
    parentDefect (satPrefix phase) (rawFlag R V z) =
      prefixAt (previousPrefix R V) phase := by
  change satPrefix phase (rawFlag (R - 1) V z) =
    prefixAt (previousPrefix R V) phase
  cases R with
  | zero => omega
  | succ R =>
      cases R with
      | zero =>
          interval_cases phase <;>
            simp [satPrefix, previousPrefix, prefixAt, zeroPrefix]
      | succ R =>
          have hvalid : PrefixValid (rawFlag (R + 1) V z) := by
            simp only [PrefixValid, rawFlag]
            omega
          change satPrefix phase (rawFlag (R + 1) V z) =
            prefixAt (lookupPrefix (R + 1) V) phase
          change PrefixValid { zOnly := z, yz := V, all := R + 1 } at hvalid
          simp [satPrefix, hvalid, prefixCore, rawFlag]

def fastBefore (p : FlagDegree) : ℕ → ℕ
  | 0 => checkedBaseCap p
  | phase + 1 =>
      if thresholdAt (lookupThreshold p.all p.yz) phase ≤ p.zOnly then
        min (fastBefore p phase)
          ((phasePotential phase).eval p + parentDefect (satPrefix phase) p)
      else fastBefore p phase

def semanticBefore (p : FlagDegree) : ℕ → ℕ
  | 0 => checkedBaseCap p
  | phase + 1 =>
      applyPhase (fun q ↦ semanticBefore q phase) (phasePotential phase)
        (phaseSource phase).Routeable (satPrefix phase) p

theorem semanticBefore_eq_zero_of_base (p : FlagDegree)
    (hzero : checkedBaseCap p = 0) (phase : ℕ) :
    semanticBefore p phase = 0 := by
  induction phase with
  | zero => simpa [semanticBefore] using hzero
  | succ phase ih =>
      simp only [semanticBefore]
      unfold applyPhase
      split <;> simp [ih]

theorem capBefore_eq_fastBefore (R V z phase : ℕ)
    (hphase : phase ≤ 4) (hR : 1 ≤ R) (hR29 : R ≤ 29)
    (hRV : R + V ≤ middleCap) (hRVz : R + V + z ≤ totalCap) :
    capBefore R V z (lookupBase R V) (lookupThreshold R V)
      (previousPrefix R V) phase = fastBefore (rawFlag R V z) phase := by
  induction phase with
  | zero =>
      have hnarrow : NarrowState (rawFlag R V z) := by
        simp only [NarrowState, rawFlag_all, rawFlag_middle, rawFlag_total,
          slopeCap, middleCap, totalCap]
        exact ⟨hR, by simpa [slopeCap] using hR29,
          by simpa [middleCap] using hRV,
          by simpa [totalCap] using hRVz⟩
      simp only [capBefore, fastBefore]
      rw [checkedBaseCap_of_narrow hnarrow]
      rfl
  | succ phase ih =>
      have hp3 : phase < 4 := by omega
      simp only [capBefore, fastBefore, rawFlag_all, rawFlag]
      rw [ih (by omega)]
      rw [← parentDefect_eq_previousPrefix phase R V z hp3 hR hR29 hRV hRVz]
      rfl

theorem semanticBefore_le_fastBefore (cert : CheckedRows) (p : FlagDegree)
    (hp : NarrowState p) (phase : ℕ) (hphase : phase ≤ 4) :
    semanticBefore p phase ≤ fastBefore p phase := by
  induction phase with
  | zero => rfl
  | succ phase ih =>
      have hp3 : phase < 4 := by omega
      simp only [semanticBefore, fastBefore]
      by_cases hcut :
          thresholdAt (lookupThreshold p.all p.yz) phase ≤ p.zOnly
      · rw [if_pos hcut]
        unfold applyPhase
        rw [if_pos (routeable_of_cutoff cert phase hp3 p hp hcut)]
        exact min_le_min (ih (by omega)) le_rfl
      · rw [if_neg hcut]
        unfold applyPhase
        split
        · exact (min_le_left _ _).trans (ih (by omega))
        · exact ih (by omega)

theorem phase_terminal (cert : CheckedRows) (phase : ℕ) (hphase : phase < 4) :
    ∀ p, ¬ (phaseSource phase).Routeable p →
      semanticBefore p phase ≤
        (phasePotential phase).eval p + satPrefix phase p := by
  intro p hn
  by_cases hp : NarrowState p
  · have hpNarrow := hp
    rcases hp with ⟨hr, hs, hm, ht⟩
    have hRV : p.all + p.yz ≤ middleCap := by
      simpa only [middle, Nat.add_comm] using hm
    have hRVz : p.all + p.yz + p.zOnly ≤ totalCap := by
      simpa only [total, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht
    have hstate := stateValid_at cert p.all p.yz hr hs hRV
    have hz : p.zOnly ∈ List.range (totalCap + 1 - (p.all + p.yz)) :=
      List.mem_range.mpr (by omega)
    have hrow := hstate.2.2.1 phase (List.mem_range.mpr hphase) p.zOnly hz
    have hterminal :
        capBefore p.all p.yz p.zOnly (lookupBase p.all p.yz)
            (lookupThreshold p.all p.yz) (previousPrefix p.all p.yz) phase ≤
          hereCharge p.all p.yz p.zOnly phase (lookupPrefix p.all p.yz) :=
      hrow.resolve_left (fun hcut ↦
        hn (routeable_of_cutoff cert phase hphase p hpNarrow hcut))
    calc
      semanticBefore p phase ≤ fastBefore p phase :=
        semanticBefore_le_fastBefore cert p hpNarrow phase hphase.le
      _ = capBefore p.all p.yz p.zOnly (lookupBase p.all p.yz)
          (lookupThreshold p.all p.yz) (previousPrefix p.all p.yz) phase :=
        (capBefore_eq_fastBefore p.all p.yz p.zOnly phase hphase.le
          hr hs hRV hRVz).symm
      _ ≤ hereCharge p.all p.yz p.zOnly phase
          (lookupPrefix p.all p.yz) := hterminal
      _ = (phasePotential phase).eval p + prefixCore phase p := by
        simp [hereCharge, prefixCore, rawFlag]
      _ ≤ (phasePotential phase).eval p + satPrefix phase p :=
        Nat.add_le_add_left (prefixCore_le_satPrefix phase hphase p hpNarrow) _
  · have hzero : checkedBaseCap p = 0 := checkedBaseCap_of_not_narrow hp
    have hsemantic : semanticBefore p phase = 0 :=
      semanticBefore_eq_zero_of_base p hzero phase
    rw [hsemantic]
    exact Nat.zero_le _

theorem semanticBefore_one (p : FlagDegree) :
    semanticBefore p 1 = afterR1200 checkedBaseCap rPrefix p := by
  rfl

theorem semanticBefore_two (p : FlagDegree) :
    semanticBefore p 2 = afterSourceC checkedBaseCap rPrefix cPrefix p := by
  rfl

theorem semanticBefore_three (p : FlagDegree) :
    semanticBefore p 3 =
      afterSplit500 checkedBaseCap rPrefix cPrefix f500Prefix p := by
  rfl

theorem semanticBefore_four (p : FlagDegree) :
    semanticBefore p 4 =
      afterPhase4 checkedBaseCap rPrefix cPrefix f500Prefix phase4Prefix p := by
  rfl

theorem rRows (cert : CheckedRows) :
    PrefixTableSound checkedBaseCap LocatorPhase6803Oracle.r1200Potential
      LocatorPhase6803Oracle.sourceR1200.Routeable rPrefix :=
  ⟨phase_terminal cert 0 (by decide), satPrefix_mono cert 0 (by decide)⟩

theorem cRows (cert : CheckedRows) :
    PrefixTableSound (afterR1200 checkedBaseCap rPrefix)
      LocatorPhase6803Oracle.sourceCPotential
      LocatorPhase6803Oracle.sourceC.Routeable cPrefix := by
  refine ⟨?_, satPrefix_mono cert 1 (by decide)⟩
  intro p hn
  simpa [semanticBefore_one, phasePotential, cPrefix] using
    phase_terminal cert 1 (by decide) p hn

theorem f500Rows (cert : CheckedRows) :
    PrefixTableSound (afterSourceC checkedBaseCap rPrefix cPrefix)
      LocatorPhase6803Oracle.split500Potential
      LocatorPhase6803Oracle.sourceSplit500.Routeable f500Prefix := by
  refine ⟨?_, satPrefix_mono cert 2 (by decide)⟩
  intro p hn
  simpa [semanticBefore_two, phasePotential, f500Prefix] using
    phase_terminal cert 2 (by decide) p hn

theorem phase4Rows (cert : CheckedRows) :
    PrefixTableSound (afterSplit500 checkedBaseCap rPrefix cPrefix f500Prefix)
      phase4Potential sourcePhase4.Routeable phase4Prefix := by
  refine ⟨?_, satPrefix_mono cert 3 (by decide)⟩
  intro p hn
  simpa [semanticBefore_three, phasePotential, phase4Prefix] using
    phase_terminal cert 3 (by decide) p hn

/-- The complete semantic phase certificate, conditional only on the separate
ordinary-base envelope audit. -/
def phaseCertificate (cert : CheckedRows)
    (hbase : LocatorPhase6803SemanticOracle.StateLocalBaseOracleSound checkedBaseCap) :
    PhasePrefixCertificate where
  baseCap := checkedBaseCap
  rPrefix := rPrefix
  cPrefix := cPrefix
  f500Prefix := f500Prefix
  phase4Prefix := phase4Prefix
  baseSound := hbase
  rRows := rRows cert
  cRows := cRows cert
  f500Rows := f500Rows cert
  phase4Rows := phase4Rows cert

/-! ## Correlated numeric exports -/

@[simp] theorem initialAComplement_raw (R V z : ℕ) :
    initialAComplement (rawFlag R V z) =
      initialAComplement { zOnly := z, yz := V, all := R } := rfl

@[simp] theorem residualCharge_raw (R V z : ℕ) :
    residualCharge (rawFlag R V z).all (rawFlag R V z).yz
      (rawFlag R V z).zOnly = residualCharge R V z := rfl

/-- Exact correlated receipt bound at every nonempty narrow state. -/
theorem coupled_le (cert : CheckedRows) (p : FlagDegree) (hp : NarrowState p) :
    afterPhase4 checkedBaseCap rPrefix cPrefix f500Prefix phase4Prefix p +
          initialAComplement p + residualCharge p.all p.yz p.zOnly +
        viableProperExceptionalCap ≤ certifiedCoupledMaximum := by
  have hpNarrow := hp
  rcases hp with ⟨hr, hs, hm, ht⟩
  have hRV : p.all + p.yz ≤ middleCap := by
    simpa only [middle, Nat.add_comm] using hm
  have hRVz : p.all + p.yz + p.zOnly ≤ totalCap := by
    simpa only [total, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht
  have hz : p.zOnly ∈ List.range (totalCap + 1 - (p.all + p.yz)) :=
    List.mem_range.mpr (by omega)
  have hchecked :=
    ((stateValid_at cert p.all p.yz hr hs hRV).2.2.2 p.zOnly hz).2.2
  have hfast := semanticBefore_le_fastBefore cert p hpNarrow 4 (by decide)
  calc
    afterPhase4 checkedBaseCap rPrefix cPrefix f500Prefix phase4Prefix p +
            initialAComplement p + residualCharge p.all p.yz p.zOnly +
          viableProperExceptionalCap =
        semanticBefore p 4 + initialAComplement p +
            residualCharge p.all p.yz p.zOnly + viableProperExceptionalCap := by
          rw [semanticBefore_four]
    _ ≤ fastBefore p 4 + initialAComplement p +
          residualCharge p.all p.yz p.zOnly + viableProperExceptionalCap := by
        omega
    _ = capBefore p.all p.yz p.zOnly (lookupBase p.all p.yz)
            (lookupThreshold p.all p.yz) (previousPrefix p.all p.yz) 4 +
          initialAComplement p + residualCharge p.all p.yz p.zOnly +
            viableProperExceptionalCap := by
        rw [capBefore_eq_fastBefore p.all p.yz p.zOnly 4 (by decide)
          hr hs hRV hRVz]
        cases p
        rfl
    _ ≤ certifiedCoupledMaximum := hchecked

theorem zero_afterPhase4 :
    afterPhase4 checkedBaseCap rPrefix cPrefix f500Prefix phase4Prefix
      (rawFlag 0 0 0) = 0 := by
  rw [← semanticBefore_four]
  apply semanticBefore_eq_zero_of_base
  simp [checkedBaseCap, NarrowState]

/-- The receipt-side part of the empty-retained-state ledger.  The separate
fixed all-H package raises this to `zeroStateTotal`. -/
theorem zeroCoupled_exact :
    afterPhase4 checkedBaseCap rPrefix cPrefix f500Prefix phase4Prefix
          (rawFlag 0 0 0) + initialAComplement (rawFlag 0 0 0) +
        residualCharge 0 0 0 + viableProperExceptionalCap =
      2578750567056087 := by
  rw [zero_afterPhase4]
  native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptSemantic
