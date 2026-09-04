import ProximityPrize.SubmissionLower.LocatorPhase6803SourceSound

/-!
# Compact executable checker for the four-phase 68.03 receipt

The generated rows contain one affine base envelope and four threshold/prefix
entries per raw `(R,V)` state.  This checker deliberately proves the finite
phase recurrence directly; semantic extraction into the algebraic phase
interface is kept separate.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptCore

open RCN095 RCN260 RCN318 LocatorFactorAggregate
open LocatorPhase6800Oracle (Potential BaseRow BaseSegment ThresholdReceipt
  PrefixReceipt defaultBaseRow rawFlag)
open LocatorPhase6803Oracle

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def totalCap : ℕ := 6676
def middleCap : ℕ := 135
def slopeCap : ℕ := 29
def prefixSentinel : ℕ := 1000000000000000000000

def certifiedNarrowMaximum : ℕ := 274069859239065828
def certifiedJointMaximum : ℕ := 274566473159888063
def certifiedCoupledMaximum : ℕ := 274730998566515451
def viableProperExceptionalCap : ℕ := 18437737600
def residualBMaxEscapeDot : ℕ := 429140070

def phasePotential : ℕ → Potential
  | 0 => r1200Potential
  | 1 => sourceCPotential
  | 2 => split500Potential
  | _ => phase4Potential

def phaseSource : ℕ → SourceNumbers
  | 0 => sourceR1200
  | 1 => sourceC
  | 2 => sourceSplit500
  | _ => sourcePhase4

def thresholdAt (q : ThresholdReceipt) : ℕ → ℕ
  | 0 => q.r1200
  | 1 => q.sourceC
  | 2 => q.split500
  | _ => q.split390

def prefixAt (q : PrefixReceipt) : ℕ → ℕ
  | 0 => q.r1200
  | 1 => q.sourceC.head?.getD prefixSentinel
  | 2 => q.split500
  | _ => q.split390

def defaultThreshold : ThresholdReceipt := ⟨0, 0, 0, 0, 0, 0⟩

def defaultPrefix : PrefixReceipt :=
  ⟨0, 0, prefixSentinel, [prefixSentinel], prefixSentinel, prefixSentinel⟩

def zeroPrefix : PrefixReceipt := ⟨0, 0, 0, [0], 0, 0⟩

def SourceThresholdSufficient
    (s : SourceNumbers) (R V threshold : ℕ) : Prop :=
  totalCap - (R + V) < threshold ∨ s.Routeable (rawFlag R V threshold)

instance (s : SourceNumbers) (R V threshold : ℕ) :
    Decidable (SourceThresholdSufficient s R V threshold) := by
  unfold SourceThresholdSufficient
  infer_instance

def ThresholdValid (R V : ℕ) (q : ThresholdReceipt) : Prop :=
  q.r = R ∧ q.v = V ∧ 1 ≤ R ∧ R ≤ slopeCap ∧ R + V ≤ middleCap ∧
    SourceThresholdSufficient sourceR1200 R V q.r1200 ∧
    SourceThresholdSufficient sourceC R V q.sourceC ∧
    SourceThresholdSufficient sourceSplit500 R V q.split500 ∧
    SourceThresholdSufficient sourcePhase4 R V q.split390

instance (R V : ℕ) (q : ThresholdReceipt) : Decidable (ThresholdValid R V q) := by
  unfold ThresholdValid
  infer_instance

def BaseValid (R V : ℕ) (q : BaseRow) : Prop :=
  q.r = R ∧ q.v = V ∧ q.segments ≠ [] ∧
    q.segments.head?.map BaseSegment.start = some 3 ∧
    q.segments.Pairwise (fun a b => a.start < b.start)

instance (R V : ℕ) (q : BaseRow) : Decidable (BaseValid R V q) := by
  unfold BaseValid
  infer_instance

def capBefore (R V z : ℕ) (base : BaseRow) (threshold : ThresholdReceipt)
    (parent : PrefixReceipt) : ℕ → ℕ
  | 0 => base.evalAt z
  | j + 1 =>
      if thresholdAt threshold j ≤ z then
        min (capBefore R V z base threshold parent j)
          ((phasePotential j).eval (rawFlag R V z) + prefixAt parent j)
      else capBefore R V z base threshold parent j

def hereCharge (R V z phase : ℕ) (here : PrefixReceipt) : ℕ :=
  (phasePotential phase).eval (rawFlag R V z) + prefixAt here phase

def initialAComplement (p : FlagDegree) : ℕ :=
  let t := 6676 - total p
  let y := 153 - middle p
  let r := 34 - p.all
  let nr := min t (min y r)
  let t' := t - nr
  let y' := y - nr
  let nv := min t' y'
  initialAWidePotential.eval (rawFlag nr nv (t' - nv))

/-- Residual viable `B(m=111,L=14261,s=34)` versus the viable terminal
`T(L=6679,Y=250,s=56)`, after subtracting the retained raw flag. -/
def residualPairStage (R V z : ℕ) : UnequalParameters :=
  ⟨262144, 131071, 181363,
    153 - (R + V), 34 - R, 14261 - (R + V + z),
    250 - (R + V), 56 - R, 6679 - (R + V + z)⟩

/-- One proper-predecessor charge for the residual B-factor. -/
def residualGroupedStage (R V z : ℕ) : UnequalParameters :=
  ⟨262144, 131071, 181363,
    153 - (R + V) - 1, 34 - R - 1, 14261 - (R + V + z) - 1,
    153 - (R + V), 34 - R, 14261 - (R + V + z)⟩

/-- Aggregate slope-free residual B-tail. -/
def residualTailStage (R V z : ℕ) : TightParameters :=
  ⟨262144, 131071, 181363,
    20131293 - (131071 * (R + V) - R), 14261 - (R + V + z), 1⟩

def residualCharge (R V z : ℕ) : ℕ :=
  (residualPairStage R V z).regularCountCap +
    (residualGroupedStage R V z).regularCountCap + residualBMaxEscapeDot +
      (residualTailStage R V z).countCap

def StateValid (R V : ℕ) (base : BaseRow) (threshold : ThresholdReceipt)
    (here parent : PrefixReceipt) : Prop :=
  BaseValid R V base ∧ ThresholdValid R V threshold ∧
    (∀ phase ∈ List.range 4,
      ∀ z ∈ List.range (totalCap + 1 - (R + V)),
        thresholdAt threshold phase ≤ z ∨
          capBefore R V z base threshold parent phase ≤
            hereCharge R V z phase here) ∧
    (∀ z ∈ List.range (totalCap + 1 - (R + V)),
      capBefore R V z base threshold parent 4 ≤ certifiedNarrowMaximum ∧
      capBefore R V z base threshold parent 4 +
        initialAComplement (rawFlag R V z) ≤ certifiedJointMaximum ∧
      capBefore R V z base threshold parent 4 +
          initialAComplement (rawFlag R V z) + residualCharge R V z +
            viableProperExceptionalCap ≤ certifiedCoupledMaximum)

instance (R V : ℕ) (base : BaseRow) (threshold : ThresholdReceipt)
    (here parent : PrefixReceipt) :
    Decidable (StateValid R V base threshold here parent) := by
  unfold StateValid
  infer_instance

def RowValid (R : ℕ) (bases : ℕ → BaseRow)
    (thresholds : ℕ → ThresholdReceipt)
    (prefixes parentPrefixes : ℕ → PrefixReceipt) : Prop :=
  ∀ V ∈ List.range (middleCap + 1 - R),
    StateValid R V (bases V) (thresholds V) (prefixes V) (parentPrefixes V)

instance (R : ℕ) (bases : ℕ → BaseRow)
    (thresholds : ℕ → ThresholdReceipt)
    (prefixes parentPrefixes : ℕ → PrefixReceipt) :
    Decidable (RowValid R bases thresholds prefixes parentPrefixes) := by
  unfold RowValid
  infer_instance

def PrefixRowValid (R : ℕ) (prefixes nextPrefixes : ℕ → PrefixReceipt) : Prop :=
  R ≤ 28 → ∀ V ∈ List.range (middleCap - R),
    let q := prefixes V
    q.afterR = R ∧ q.v = V ∧
      (∀ phase ∈ List.range 4, prefixAt q phase ≤ prefixSentinel) ∧
      (R + 1 ≤ 28 →
        ∀ phase ∈ List.range 4,
          prefixAt q phase ≤ prefixAt (nextPrefixes V) phase) ∧
      (R + 1 + (V + 1) ≤ middleCap →
        ∀ phase ∈ List.range 4,
          prefixAt q phase ≤ prefixAt (prefixes (V + 1)) phase)

instance (R : ℕ) (prefixes nextPrefixes : ℕ → PrefixReceipt) :
    Decidable (PrefixRowValid R prefixes nextPrefixes) := by
  unfold PrefixRowValid
  infer_instance

end ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptCore
