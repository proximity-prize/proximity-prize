import ProximityPrize.SubmissionLower.LocatorPhase6802BaseSparseChecked

namespace ProximityPrize.SubmissionLower.LocatorPhase6802ReceiptCellCore

open LocatorPhase6802Oracle

set_option autoImplicit false
set_option maxRecDepth 100000

def defaultThreshold : ThresholdReceipt := ⟨0, 0, 0, 0, 0, 0⟩
def defaultPrefix : PrefixReceipt := ⟨0, 0, 0, [], 0, 0⟩

/-- It is enough for the stored cutoff to be outside the benchmark row, or
for the source to be routeable at the cutoff.  Routeability is monotone in
the raw `z` coordinate, so no false-boundary computation is needed. -/
def SourceThresholdSufficient
    (s : SourceNumbers) (r v threshold : ℕ) : Prop :=
  6403 - (r + v) < threshold ∨ s.Routeable (rawFlag r v threshold)

instance (s : SourceNumbers) (r v threshold : ℕ) :
    Decidable (SourceThresholdSufficient s r v threshold) := by
  unfold SourceThresholdSufficient
  infer_instance

def ThresholdSufficient (q : ThresholdReceipt) : Prop :=
  1 ≤ q.r ∧ q.r ≤ 29 ∧ q.r + q.v ≤ 132 ∧
    SourceThresholdSufficient sourceR1200 q.r q.v q.r1200 ∧
    SourceThresholdSufficient LocatorPhase6802Oracle.sourceC q.r q.v q.sourceC ∧
    SourceThresholdSufficient sourceSplit500 q.r q.v q.split500 ∧
    SourceThresholdSufficient sourceSplit390 q.r q.v q.split390

instance (q : ThresholdReceipt) : Decidable (ThresholdSufficient q) := by
  unfold ThresholdSufficient
  infer_instance

def ThresholdAtOf (row : ℕ → ThresholdReceipt) (R V : ℕ) : Prop :=
  let q := row V
  q.r = R ∧ q.v = V ∧ ThresholdSufficient q

instance (row : ℕ → ThresholdReceipt) (R V : ℕ) :
    Decidable (ThresholdAtOf row R V) := by
  unfold ThresholdAtOf
  infer_instance

def prefixSentinel : ℕ := 1000000000000000000000

def rCoreOf (row : ℕ → PrefixReceipt) (v : ℕ) : ℕ := (row v).r1200
def f500CoreOf (row : ℕ → PrefixReceipt) (v : ℕ) : ℕ := (row v).split500
def s390CoreOf (row : ℕ → PrefixReceipt) (v : ℕ) : ℕ := (row v).split390

def cAtOf (row : ℕ → PrefixReceipt) (v bucket : ℕ) : ℕ :=
  let q := row v
  if q.sourceC.length = 1 then q.sourceC.head?.getD prefixSentinel
  else (q.sourceC[bucket]?).getD prefixSentinel

def PrefixCoreAtOf (row nextRow : ℕ → PrefixReceipt) (R V : ℕ) : Prop :=
  rCoreOf row V ≤ prefixSentinel ∧
  f500CoreOf row V ≤ prefixSentinel ∧
  s390CoreOf row V ≤ prefixSentinel ∧
  (∀ b ∈ List.range 22, cAtOf row V b ≤ prefixSentinel) ∧
  (R + 1 ≤ 28 ∧ R + 1 + 1 + V ≤ 132 →
    rCoreOf row V ≤ rCoreOf nextRow V ∧
    f500CoreOf row V ≤ f500CoreOf nextRow V ∧
    s390CoreOf row V ≤ s390CoreOf nextRow V ∧
    ∀ b ∈ List.range 22, cAtOf row V b ≤ cAtOf nextRow V b) ∧
  (R + 1 + (V + 1) ≤ 132 →
    rCoreOf row V ≤ rCoreOf row (V + 1) ∧
    f500CoreOf row V ≤ f500CoreOf row (V + 1) ∧
    s390CoreOf row V ≤ s390CoreOf row (V + 1) ∧
    ∀ b ∈ List.range 22, cAtOf row V b ≤ cAtOf row (V + 1) b) ∧
  (∀ b ∈ List.range 21, cAtOf row V b ≤ cAtOf row V (b + 1))

instance (row nextRow : ℕ → PrefixReceipt) (R V : ℕ) :
    Decidable (PrefixCoreAtOf row nextRow R V) := by
  unfold PrefixCoreAtOf
  infer_instance

end ProximityPrize.SubmissionLower.LocatorPhase6802ReceiptCellCore
