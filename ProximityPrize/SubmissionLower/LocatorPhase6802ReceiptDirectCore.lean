import ProximityPrize.SubmissionLower.LocatorPhase6802ReceiptDirectData

namespace ProximityPrize.SubmissionLower.LocatorPhase6802Concrete

open RCN095 LocatorFactorAggregate LocatorPhase6802Oracle
open LocatorPhase6802ReceiptCellCore

set_option autoImplicit false
set_option maxRecDepth 100000

def defaultThreshold : ThresholdReceipt :=
  LocatorPhase6802ReceiptDirectData.defaultThreshold

def lookupThreshold (r v : ℕ) : ThresholdReceipt :=
  LocatorPhase6802ReceiptDirectData.lookupThreshold r v

def defaultPrefix : PrefixReceipt :=
  LocatorPhase6802ReceiptDirectData.defaultPrefix

def lookupPrefix (r v : ℕ) : PrefixReceipt :=
  LocatorPhase6802ReceiptDirectData.lookupPrefix r v

def rThreshold (r v : ℕ) : ℕ := (lookupThreshold r v).r1200
def cThreshold (r v : ℕ) : ℕ := (lookupThreshold r v).sourceC
def f500Threshold (r v : ℕ) : ℕ := (lookupThreshold r v).split500
def s390Threshold (r v : ℕ) : ℕ := (lookupThreshold r v).split390

def prefixSentinel : ℕ := 1000000000000000000000

def PrefixValid (p : FlagDegree) : Prop :=
  1 ≤ p.all ∧ p.all ≤ 28 ∧
    p.all + 1 + p.yz ≤ 132 ∧
    p.all + 1 + p.yz + p.zOnly ≤ 6403

instance (p : FlagDegree) : Decidable (PrefixValid p) := by
  unfold PrefixValid
  infer_instance

def rPrefixCore (p : FlagDegree) : ℕ :=
  (lookupPrefix p.all p.yz).r1200

def cPrefixAt (r v bucket : ℕ) : ℕ :=
  let q := lookupPrefix r v
  if q.sourceC.length = 1 then q.sourceC.head?.getD prefixSentinel
  else (q.sourceC[bucket]?).getD prefixSentinel

def cPrefixCore (p : FlagDegree) : ℕ :=
  cPrefixAt p.all p.yz (cBucket p.zOnly)

def f500PrefixCore (p : FlagDegree) : ℕ :=
  (lookupPrefix p.all p.yz).split500

def s390PrefixCore (p : FlagDegree) : ℕ := (lookupPrefix p.all p.yz).split390

/-- Saturating outside the parent-embeddable prefix box makes the table
globally monotone, as required by `PrefixTableSound`, without ever consulting
an absent row.  Slope zero remains exactly zero. -/
def satPrefix (core : FlagDegree → ℕ) (p : FlagDegree) : ℕ :=
  if p.all = 0 then 0 else if PrefixValid p then core p else prefixSentinel

def rPrefix : FlagDegree → ℕ := satPrefix rPrefixCore
def cPrefix : FlagDegree → ℕ := satPrefix cPrefixCore
def f500Prefix : FlagDegree → ℕ := satPrefix f500PrefixCore
def s390Prefix : FlagDegree → ℕ := satPrefix s390PrefixCore

@[simp] theorem satPrefix_zero (core : FlagDegree → ℕ) (v z : ℕ) :
    satPrefix core (rawFlag 0 v z) = 0 := by
  simp [satPrefix]

/-! ## Finite lookup predicates independent of the base certificate -/

def ThresholdAt (R V : ℕ) : Prop :=
  let q := lookupThreshold R V
  q.r = R ∧ q.v = V ∧ ThresholdSufficient q

instance (R V : ℕ) : Decidable (ThresholdAt R V) := by
  unfold ThresholdAt
  infer_instance

def ThresholdRIndexed (R : ℕ) : Prop :=
  ∀ V ∈ List.range (133 - R), ThresholdAt R V

instance (R : ℕ) : Decidable (ThresholdRIndexed R) := by
  unfold ThresholdRIndexed
  infer_instance

def PrefixRIndexed (R : ℕ) : Prop :=
  ∀ V ∈ List.range (132 - R),
    let q := lookupPrefix R V
    q.afterR = R ∧ q.v = V ∧ q.ExpectedShape

instance (R : ℕ) : Decidable (PrefixRIndexed R) := by
  unfold PrefixRIndexed
  infer_instance

def ThresholdsIndexed : Prop :=
  ∀ R ∈ List.range 30, 1 ≤ R → ThresholdRIndexed R

instance : Decidable ThresholdsIndexed := by
  unfold ThresholdsIndexed
  infer_instance

def PrefixesIndexed : Prop :=
  ∀ R ∈ List.range 29, 1 ≤ R → PrefixRIndexed R

instance : Decidable PrefixesIndexed := by
  unfold PrefixesIndexed
  infer_instance

def PrefixCoreAt (R V : ℕ) : Prop :=
  rPrefixCore (rawFlag R V 0) ≤ prefixSentinel ∧
  f500PrefixCore (rawFlag R V 0) ≤ prefixSentinel ∧
  s390PrefixCore (rawFlag R V 0) ≤ prefixSentinel ∧
  (∀ b ∈ List.range 22, cPrefixAt R V b ≤ prefixSentinel) ∧
  (R + 1 ≤ 28 ∧ R + 1 + 1 + V ≤ 132 →
    rPrefixCore (rawFlag R V 0) ≤ rPrefixCore (rawFlag (R + 1) V 0) ∧
    f500PrefixCore (rawFlag R V 0) ≤
      f500PrefixCore (rawFlag (R + 1) V 0) ∧
    s390PrefixCore (rawFlag R V 0) ≤
      s390PrefixCore (rawFlag (R + 1) V 0) ∧
    ∀ b ∈ List.range 22, cPrefixAt R V b ≤ cPrefixAt (R + 1) V b) ∧
  (R + 1 + (V + 1) ≤ 132 →
    rPrefixCore (rawFlag R V 0) ≤ rPrefixCore (rawFlag R (V + 1) 0) ∧
    f500PrefixCore (rawFlag R V 0) ≤
      f500PrefixCore (rawFlag R (V + 1) 0) ∧
    s390PrefixCore (rawFlag R V 0) ≤
      s390PrefixCore (rawFlag R (V + 1) 0) ∧
    ∀ b ∈ List.range 22, cPrefixAt R V b ≤ cPrefixAt R (V + 1) b) ∧
  (∀ b ∈ List.range 21, cPrefixAt R V b ≤ cPrefixAt R V (b + 1))

instance (R V : ℕ) : Decidable (PrefixCoreAt R V) := by
  unfold PrefixCoreAt
  infer_instance

def PrefixCoreRCheck (R : ℕ) : Prop :=
  ∀ V ∈ List.range (132 - R), PrefixCoreAt R V

instance (R : ℕ) : Decidable (PrefixCoreRCheck R) := by
  unfold PrefixCoreRCheck
  infer_instance

def PrefixCoreChecks : Prop :=
  ∀ R ∈ List.range 29, 1 ≤ R → PrefixCoreRCheck R

instance : Decidable PrefixCoreChecks := by
  unfold PrefixCoreChecks
  infer_instance

end ProximityPrize.SubmissionLower.LocatorPhase6802Concrete
