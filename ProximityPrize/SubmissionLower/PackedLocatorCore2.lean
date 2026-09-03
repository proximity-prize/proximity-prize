import ProximityPrize.SubmissionLower.PackedLocatorCore1

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRuns. -/
section PackedLocator_LocatorPhase6800PhaseRuns

/-!
Sparse checker for the phase-state grid.  One `PhaseRun` covers
a half-open interval on which one already-active source line and the current
target charge are affine.  Two endpoint comparisons replace a point-by-point
check of that interval.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRuns

open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle LocatorPhase6800Audit
open LocatorPhase6800BaseDirectData
open LocatorPhase6800Concrete

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def phasePotential : ℕ → Potential
  | 0 => r1200Potential
  | 1 => sourceCPotential
  | 2 => split500Potential
  | _ => split390Potential

def thresholdAt (q : ThresholdReceipt) : ℕ → ℕ
  | 0 => q.r1200
  | 1 => q.sourceC
  | 2 => q.split500
  | _ => q.split390

/-- Prefix evaluation with its receipt row supplied by the enclosing row
checker. -/
def cachedPrefixAt (q : PrefixReceipt) (phase : ℕ) (p : FlagDegree) : ℕ :=
  match phase with
  | 0 => satPrefix (fun _ => q.r1200) p
  | 1 => satPrefix (fun x =>
      if q.sourceC.length = 1 then q.sourceC.head?.getD prefixSentinel
      else (q.sourceC[cBucket x.zOnly]?).getD prefixSentinel) p
  | 2 => satPrefix (fun _ => q.split500) p
  | _ => satPrefix (fun _ => q.split390) p

theorem cachedPrefixAt_lookup (phase : ℕ) (p : FlagDegree) (hphase : phase < 4) :
    cachedPrefixAt (lookupPrefix p.all p.yz) phase p =
      match phase with
      | 0 => rPrefix p
      | 1 => cPrefix p
      | 2 => f500Prefix p
      | _ => s390Prefix p := by
  interval_cases phase <;> rfl

structure PhaseRowContext where
  R : ℕ
  V : ℕ
  base : BaseRow
  threshold : ThresholdReceipt
  here : PrefixReceipt
  parent : PrefixReceipt

def rowContext (R V : ℕ) : PhaseRowContext :=
  ⟨R, V, lookup R V, lookupThreshold R V,
    lookupPrefix R V, lookupPrefix (R - 1) V⟩

def baseAt (c : PhaseRowContext) (z : ℕ) : ℕ := c.base.evalAt z

def parentCharge (c : PhaseRowContext) (phase z : ℕ) : ℕ :=
  let p := rawFlag c.R c.V z
  let pp := rawFlag (c.R - 1) c.V z
  (phasePotential phase).eval p + cachedPrefixAt c.parent phase pp

def hereCharge (c : PhaseRowContext) (phase z : ℕ) : ℕ :=
  let p := rawFlag c.R c.V z
  (phasePotential phase).eval p + cachedPrefixAt c.here phase p

/-- Source `0` is the base line; source `j+1` is the parent charge of phase
`j`. -/
def sourceLine (c : PhaseRowContext) : ℕ → ℕ → ℕ
  | 0, z => baseAt c z
  | j + 1, z => parentCharge c j z

/-- The cap just before `phase`. -/
def capBefore (c : PhaseRowContext) : ℕ → ℕ → ℕ
  | 0, z => baseAt c z
  | j + 1, z =>
      if thresholdAt c.threshold j ≤ z then
        min (capBefore c j z) (parentCharge c j z)
      else capBefore c j z

def SourceActive (c : PhaseRowContext) : ℕ → ℕ → Prop
  | 0, _ => True
  | j + 1, z => thresholdAt c.threshold j ≤ z

instance (c : PhaseRowContext) (w z : ℕ) : Decidable (SourceActive c w z) := by
  cases w <;> simp only [SourceActive] <;> infer_instance

theorem sourceActive_mono (c : PhaseRowContext) (w lo z : ℕ)
    (h : SourceActive c w lo) (hz : lo ≤ z) : SourceActive c w z := by
  cases w with
  | zero => trivial
  | succ j =>
      change thresholdAt c.threshold j ≤ lo at h
      change thresholdAt c.threshold j ≤ z
      exact h.trans hz

theorem capBefore_step_le (c : PhaseRowContext) (phase z : ℕ) :
    capBefore c (phase + 1) z ≤ capBefore c phase z := by
  simp only [capBefore]
  split
  · exact min_le_left _ _
  · exact le_rfl

theorem capBefore_le_sourceLine (c : PhaseRowContext) (phase witness z : ℕ)
    (hw : witness ≤ phase) (ha : SourceActive c witness z) :
    capBefore c phase z ≤ sourceLine c witness z := by
  induction phase with
  | zero =>
      have : witness = 0 := by omega
      subst witness
      exact le_rfl
  | succ phase ih =>
      by_cases hprev : witness ≤ phase
      · exact (capBefore_step_le c phase z).trans (ih hprev)
      · have heq : witness = phase + 1 := by omega
        subst witness
        simp only [SourceActive] at ha
        simp only [capBefore, sourceLine, if_pos ha]
        exact min_le_right _ _

/-! ## Affine cells -/

def baseSlopeAt (q : BaseRow) (lo : ℕ) : ℕ :=
  match q.segments with
  | [s] => s.slope
  | [s₁, s₂] => if s₂.start ≤ lo then s₂.slope else s₁.slope
  | _ => 0

/-- Either a singleton (which is trivially affine), or one of the one/two
segment shapes used by the generated table without a segment boundary in the
interior. -/
def BaseCell (q : BaseRow) (lo hi : ℕ) : Prop :=
  lo = hi ∨
    (3 ≤ lo ∧
      match q.segments with
      | [s] => s.start ≤ lo
      | [s₁, s₂] =>
          s₁.start ≤ lo ∧ (hi < s₂.start ∨ s₂.start ≤ lo)
      | _ => False)

instance (q : BaseRow) (lo hi : ℕ) : Decidable (BaseCell q lo hi) := by
  unfold BaseCell
  generalize hs : q.segments = segments
  cases segments with
  | nil => simp only; infer_instance
  | cons s tail =>
      cases tail with
      | nil => simp only; infer_instance
      | cons s₂ rest =>
          cases rest with
          | nil => simp only; infer_instance
          | cons s₃ more => simp only; infer_instance

theorem segment_evalAt_shift (s : BaseSegment) (lo z : ℕ)
    (hs : s.start ≤ lo) (hz : lo ≤ z) :
    s.evalAt z = s.evalAt lo + s.slope * (z - lo) := by
  have hsplit : z - s.start = (lo - s.start) + (z - lo) := by omega
  simp only [BaseSegment.evalAt, hsplit, Nat.mul_add]
  omega

theorem baseAt_affine (q : BaseRow) (lo hi z : ℕ)
    (hcell : BaseCell q lo hi) (hlo : lo ≤ z) (hhi : z ≤ hi) :
    q.evalAt z = q.evalAt lo + baseSlopeAt q lo * (z - lo) := by
  rcases hcell with heq | hcell
  · have hz : z = lo := by omega
    subst z
    simp
  · rcases hcell with ⟨hlo3, hshape⟩
    rcases hs : q.segments with _ | ⟨s₁, tail⟩
    · simp only [hs] at hshape
    · rcases ht : tail with _ | ⟨s₂, rest⟩
      · simp only [hs, ht] at hshape
        simp only [BaseRow.evalAt, if_neg (show z ≠ 0 by omega),
          if_neg (show z ≠ 1 by omega), if_neg (show z ≠ 2 by omega),
          if_neg (show lo ≠ 0 by omega), if_neg (show lo ≠ 1 by omega),
          if_neg (show lo ≠ 2 by omega), hs, ht, evalBaseSegments,
          List.foldl_nil, baseSlopeAt]
        exact segment_evalAt_shift s₁ lo z hshape hlo
      · rcases hu : rest with _ | ⟨s₃, more⟩
        · simp only [hs, ht, hu] at hshape
          rcases hshape with ⟨hs₁, hfirst | hsecond⟩
          · have hz₂ : ¬s₂.start ≤ z := by omega
            have hlo₂ : ¬s₂.start ≤ lo := by omega
            simp only [BaseRow.evalAt, if_neg (show z ≠ 0 by omega),
              if_neg (show z ≠ 1 by omega), if_neg (show z ≠ 2 by omega),
              if_neg (show lo ≠ 0 by omega), if_neg (show lo ≠ 1 by omega),
              if_neg (show lo ≠ 2 by omega), hs, ht, hu, evalBaseSegments, List.foldl_cons,
              List.foldl_nil, if_neg hz₂, baseSlopeAt, if_neg hlo₂]
            exact segment_evalAt_shift s₁ lo z hs₁ hlo
          · have hz₂ : s₂.start ≤ z := hsecond.trans hlo
            simp only [BaseRow.evalAt, if_neg (show z ≠ 0 by omega),
              if_neg (show z ≠ 1 by omega), if_neg (show z ≠ 2 by omega),
              if_neg (show lo ≠ 0 by omega), if_neg (show lo ≠ 1 by omega),
              if_neg (show lo ≠ 2 by omega), hs, ht, hu, evalBaseSegments, List.foldl_cons,
              List.foldl_nil, if_pos hz₂, baseSlopeAt, if_pos hsecond]
            exact segment_evalAt_shift s₂ lo z hsecond hlo
        · simp only [hs, ht, hu] at hshape

theorem potential_raw_affine (q : Potential) (R V lo z : ℕ) (hlo : lo ≤ z) :
    q.eval (rawFlag R V z) =
      q.eval (rawFlag R V lo) + q.totalCoeff * (z - lo) := by
  have hz : z = lo + (z - lo) := by omega
  rw [hz]
  simp only [Potential.eval, rawFlag_total, rawFlag_middle, rawFlag_all]
  have hsub : lo + (z - lo) - lo = z - lo := by omega
  rw [hsub]
  ring

/-- Endpoint equality of prefix-validity regions, expressed in the direction
that is useful for every intermediate point. -/
def PrefixCell (r v phase lo hi : ℕ) (q : PrefixReceipt) : Prop :=
  r = 0 ∨
    ((PrefixValid (rawFlag r v hi) ∨ ¬PrefixValid (rawFlag r v lo)) ∧
      (phase ≠ 1 ∨ q.sourceC.length = 1 ∨ cBucket lo = cBucket hi))

instance (r v phase lo hi : ℕ) (q : PrefixReceipt) :
    Decidable (PrefixCell r v phase lo hi q) := by
  unfold PrefixCell
  infer_instance

private theorem prefixValid_down (r v z hi : ℕ) (hz : z ≤ hi)
    (h : PrefixValid (rawFlag r v hi)) : PrefixValid (rawFlag r v z) := by
  simp only [PrefixValid, rawFlag_all, rawFlag] at h ⊢
  omega

private theorem prefixInvalid_up (r v lo z : ℕ) (hz : lo ≤ z)
    (h : ¬PrefixValid (rawFlag r v lo)) :
    ¬PrefixValid (rawFlag r v z) := by
  intro hv
  exact h (prefixValid_down r v lo z hz hv)

theorem cBucket_mono_local {z₁ z₂ : ℕ} (hz : z₁ ≤ z₂) :
    cBucket z₁ ≤ cBucket z₂ := by
  unfold cBucket
  by_cases h₁ : z₁ ≤ 64
  · rw [if_pos h₁]
    exact Nat.zero_le _
  · have h₂ : ¬z₂ ≤ 64 := by omega
    rw [if_neg h₁, if_neg h₂]
    exact Nat.div_le_div_right
      (Nat.add_le_add_right (Nat.sub_le_sub_right hz 64) 303)

theorem cachedPrefixAt_constant (q : PrefixReceipt) (r v phase lo hi z : ℕ)
    (hp : phase < 4) (hcell : PrefixCell r v phase lo hi q)
    (hlo : lo ≤ z) (hhi : z ≤ hi) :
    cachedPrefixAt q phase (rawFlag r v z) =
      cachedPrefixAt q phase (rawFlag r v lo) := by
  rcases hcell with hr | ⟨hvalid, hbucket⟩
  · subst r
    simp [cachedPrefixAt, satPrefix]
  · rcases hvalid with hvalidHi | hinvalidLo
    · have hvalidZ := prefixValid_down r v z hi hhi hvalidHi
      have hvalidLo := prefixValid_down r v lo hi (hlo.trans hhi) hvalidHi
      have hrne : r ≠ 0 := Nat.ne_of_gt hvalidHi.1
      interval_cases phase
      · simp only [cachedPrefixAt, satPrefix, rawFlag_all, if_neg hrne,
          if_pos hvalidZ, if_pos hvalidLo]
      · rcases hbucket with hbad | hlen | hb
        · omega
        · simp only [cachedPrefixAt, satPrefix, rawFlag_all, if_neg hrne,
            if_pos hvalidZ, if_pos hvalidLo, hlen, if_pos]
        · have hbLo : cBucket lo ≤ cBucket z := cBucket_mono_local hlo
          have hbHi : cBucket z ≤ cBucket hi := cBucket_mono_local hhi
          have hbz : cBucket z = cBucket lo := by omega
          simp only [cachedPrefixAt, satPrefix, rawFlag_all, if_neg hrne,
            if_pos hvalidZ, if_pos hvalidLo]
          simp only [rawFlag, hbz]
      · simp only [cachedPrefixAt, satPrefix, rawFlag_all, if_neg hrne,
          if_pos hvalidZ, if_pos hvalidLo]
      · simp only [cachedPrefixAt, satPrefix, rawFlag_all, if_neg hrne,
          if_pos hvalidZ, if_pos hvalidLo]
    · by_cases hr : r = 0
      · subst r
        simp [cachedPrefixAt, satPrefix]
      · have hinvalidZ := prefixInvalid_up r v lo z hlo hinvalidLo
        interval_cases phase <;> simp only [cachedPrefixAt, satPrefix,
          rawFlag_all, if_neg hr, if_neg hinvalidZ, if_neg hinvalidLo]

def sourceSlope (c : PhaseRowContext) (witness lo : ℕ) : ℕ :=
  match witness with
  | 0 => baseSlopeAt c.base lo
  | j + 1 => (phasePotential j).totalCoeff

def SourceCell (c : PhaseRowContext) (witness lo hi : ℕ) : Prop :=
  match witness with
  | 0 => BaseCell c.base lo hi
  | j + 1 => PrefixCell (c.R - 1) c.V j lo hi c.parent

instance (c : PhaseRowContext) (witness lo hi : ℕ) :
    Decidable (SourceCell c witness lo hi) := by
  cases witness <;> simp only [SourceCell] <;> infer_instance

theorem sourceLine_affine (c : PhaseRowContext) (witness lo hi z : ℕ)
    (hw : witness ≤ 4) (hcell : SourceCell c witness lo hi)
    (hlo : lo ≤ z) (hhi : z ≤ hi) :
    sourceLine c witness z = sourceLine c witness lo +
      sourceSlope c witness lo * (z - lo) := by
  cases witness with
  | zero =>
      exact baseAt_affine c.base lo hi z hcell hlo hhi
  | succ phase =>
      have hp : phase < 4 := by omega
      simp only [sourceLine, sourceSlope, parentCharge]
      rw [potential_raw_affine (phasePotential phase) c.R c.V lo z hlo,
        cachedPrefixAt_constant c.parent (c.R - 1) c.V phase lo hi z
          hp hcell hlo hhi]
      omega

theorem hereCharge_affine (c : PhaseRowContext) (phase lo hi z : ℕ)
    (hp : phase < 4) (hcell : PrefixCell c.R c.V phase lo hi c.here)
    (hlo : lo ≤ z) (hhi : z ≤ hi) :
    hereCharge c phase z = hereCharge c phase lo +
      (phasePotential phase).totalCoeff * (z - lo) := by
  simp only [hereCharge]
  rw [potential_raw_affine (phasePotential phase) c.R c.V lo z hlo,
    cachedPrefixAt_constant c.here c.R c.V phase lo hi z hp hcell hlo hhi]
  omega

structure PhaseRun where
  stop : ℕ
  witness : ℕ
  deriving DecidableEq, Repr

def RunValid (c : PhaseRowContext) (phase start : ℕ) (run : PhaseRun) : Prop :=
  let hi := run.stop - 1
  start < run.stop ∧ run.witness ≤ phase ∧
    SourceActive c run.witness start ∧
    SourceCell c run.witness start hi ∧
    PrefixCell c.R c.V phase start hi c.here ∧
    sourceLine c run.witness start ≤ hereCharge c phase start ∧
    sourceLine c run.witness hi ≤ hereCharge c phase hi

instance (c : PhaseRowContext) (phase start : ℕ) (run : PhaseRun) :
    Decidable (RunValid c phase start run) := by
  unfold RunValid
  infer_instance

theorem RunValid.sound (c : PhaseRowContext) (phase start : ℕ) (run : PhaseRun)
    (hp : phase < 4) (h : RunValid c phase start run)
    (z : ℕ) (hlo : start ≤ z) (hhi : z < run.stop) :
    capBefore c phase z ≤ hereCharge c phase z := by
  change start < run.stop ∧ run.witness ≤ phase ∧
    SourceActive c run.witness start ∧
    SourceCell c run.witness start (run.stop - 1) ∧
    PrefixCell c.R c.V phase start (run.stop - 1) c.here ∧
    sourceLine c run.witness start ≤ hereCharge c phase start ∧
    sourceLine c run.witness (run.stop - 1) ≤
      hereCharge c phase (run.stop - 1) at h
  rcases h with ⟨hstart, hw, hactive, hsource, htarget, hleft, hright⟩
  let hi := run.stop - 1
  have hzhi : z ≤ hi := by dsimp only [hi]; omega
  have hsthi : start ≤ hi := by dsimp only [hi]; omega
  have hs := sourceLine_affine c run.witness start hi z (by omega)
    hsource hlo hzhi
  have ht := hereCharge_affine c phase start hi z hp htarget hlo hzhi
  have hsEnd := sourceLine_affine c run.witness start hi hi (by omega)
    hsource hsthi le_rfl
  have htEnd := hereCharge_affine c phase start hi hi hp htarget
    hsthi le_rfl
  have hline : sourceLine c run.witness z ≤ hereCharge c phase z := by
    rw [hs, ht]
    apply affine_le_between
      (sourceLine c run.witness start) (hereCharge c phase start)
      (sourceSlope c run.witness start) ((phasePotential phase).totalCoeff)
      (z - start) (hi - start)
    · exact Nat.sub_le_sub_right hzhi start
    · exact hleft
    · rw [← hsEnd, ← htEnd]
      exact hright
  apply (capBefore_le_sourceLine c phase run.witness z hw ?_).trans hline
  exact sourceActive_mono c run.witness start z hactive hlo

def RunsValid (c : PhaseRowContext) (phase finish : ℕ) :
    ℕ → List PhaseRun → Prop
  | start, [] => start = finish
  | start, run :: runs =>
      run.stop ≤ finish ∧ RunValid c phase start run ∧
        RunsValid c phase finish run.stop runs

instance (c : PhaseRowContext) (phase finish start : ℕ)
    (runs : List PhaseRun) : Decidable (RunsValid c phase finish start runs) := by
  induction runs generalizing start with
  | nil => simp only [RunsValid]; infer_instance
  | cons run runs ih => simp only [RunsValid]; infer_instance

theorem RunsValid.sound (c : PhaseRowContext) (phase finish start : ℕ)
    (runs : List PhaseRun) (hp : phase < 4)
    (h : RunsValid c phase finish start runs)
    (z : ℕ) (hlo : start ≤ z) (hhi : z < finish) :
    capBefore c phase z ≤ hereCharge c phase z := by
  induction runs generalizing start with
  | nil =>
      simp only [RunsValid] at h
      omega
  | cons run runs ih =>
      simp only [RunsValid] at h
      by_cases hz : z < run.stop
      · exact RunValid.sound c phase start run hp h.2.1 z hlo hz
      · exact ih run.stop h.2.2 (by omega)

def phaseFinish (c : PhaseRowContext) (phase : ℕ) : ℕ :=
  min (thresholdAt c.threshold phase) (5965 - (c.R + c.V))

def RowRunsValid (c : PhaseRowContext) (runs : Array (List PhaseRun)) : Prop :=
  RunsValid c 0 (phaseFinish c 0) 0 ((runs[0]?).getD []) ∧
  RunsValid c 1 (phaseFinish c 1) 0 ((runs[1]?).getD []) ∧
  RunsValid c 2 (phaseFinish c 2) 0 ((runs[2]?).getD []) ∧
  RunsValid c 3 (phaseFinish c 3) 0 ((runs[3]?).getD [])

instance (c : PhaseRowContext) (runs : Array (List PhaseRun)) :
    Decidable (RowRunsValid c runs) := by
  unfold RowRunsValid
  infer_instance

theorem phaseTerminal_of_runs (c : PhaseRowContext) (phase : ℕ)
    (runs : List PhaseRun) (hp : phase < 4)
    (h : RunsValid c phase (phaseFinish c phase) 0 runs)
    (z : ℕ) (hz : z < 5965 - (c.R + c.V)) :
    thresholdAt c.threshold phase ≤ z ∨
      capBefore c phase z ≤ hereCharge c phase z := by
  by_cases ht : thresholdAt c.threshold phase ≤ z
  · exact Or.inl ht
  · apply Or.inr
    apply RunsValid.sound c phase (phaseFinish c phase) 0 runs hp h z
    · omega
    · unfold phaseFinish
      exact lt_min (Nat.lt_of_not_ge ht) hz

/-! ## Final Split390 bounds -/

theorem complement_raw_formula (R V z : ℕ) :
    initialAComplement (rawFlag R V z) =
      5743475809 * (5964 - (R + V + z)) +
      6005121364168 *
        min (5964 - (R + V + z)) (153 - (R + V)) +
      21911127063412 *
        min (5964 - (R + V + z))
          (min (153 - (R + V)) (33 - R)) := by
  simp [initialAComplement, initialAPotential, Potential.eval, rawFlag,
    total, middle, Nat.min_def]
  split_ifs <;> omega

def sLine (R V pref z : ℕ) : ℕ :=
  split390Potential.eval (rawFlag R V z) + pref

theorem sLine_joint_le_of_keypoints
    (R V pref lo hi bound : ℕ) (hlohi : lo ≤ hi)
    (hlo : sLine R V pref lo + initialAComplement (rawFlag R V lo) ≤ bound)
    (hhi : sLine R V pref hi + initialAComplement (rawFlag R V hi) ≤ bound)
    (h5811 :
      sLine R V pref (max lo (min hi 5811)) +
        initialAComplement (rawFlag R V (max lo (min hi 5811))) ≤ bound)
    (h5931 :
      sLine R V pref (max lo (min hi (5931 - V))) +
        initialAComplement (rawFlag R V (max lo (min hi (5931 - V)))) ≤ bound) :
    ∀ z, lo ≤ z → z ≤ hi →
      sLine R V pref z + initialAComplement (rawFlag R V z) ≤ bound := by
  intro z hlz hzh
  simp only [sLine, split390Potential, Potential.eval, rawFlag_total,
    rawFlag_middle, rawFlag_all, complement_raw_formula] at hlo hhi h5811 h5931 ⊢
  simp only [Nat.min_def, Nat.max_def] at h5811 h5931 ⊢
  split_ifs at h5811 h5931 ⊢ <;> omega

def sChargeWith (c : PhaseRowContext) (q : PrefixReceipt) (prefixR z : ℕ) : ℕ :=
  split390Potential.eval (rawFlag c.R c.V z) +
    cachedPrefixAt q 3 (rawFlag prefixR c.V z)

theorem sChargeWith_affine (c : PhaseRowContext) (q : PrefixReceipt)
    (prefixR lo hi z : ℕ)
    (hcell : PrefixCell prefixR c.V 3 lo hi q)
    (hlo : lo ≤ z) (hhi : z ≤ hi) :
    sChargeWith c q prefixR z = sChargeWith c q prefixR lo +
      split390Potential.totalCoeff * (z - lo) := by
  unfold sChargeWith
  rw [potential_raw_affine split390Potential c.R c.V lo z hlo,
    cachedPrefixAt_constant q prefixR c.V 3 lo hi z (by decide)
      hcell hlo hhi]
  omega

def SIntervalValid (c : PhaseRowContext) (q : PrefixReceipt)
    (prefixR lo hi : ℕ) : Prop :=
  lo ≤ hi ∧ PrefixCell prefixR c.V 3 lo hi q ∧
    sChargeWith c q prefixR hi ≤ certifiedNarrowMaximum ∧
    sChargeWith c q prefixR lo +
        initialAComplement (rawFlag c.R c.V lo) ≤ certifiedJointMaximum ∧
    sChargeWith c q prefixR hi +
        initialAComplement (rawFlag c.R c.V hi) ≤ certifiedJointMaximum ∧
    let k₁ := max lo (min hi 5811)
    let k₂ := max lo (min hi (5931 - c.V))
    sChargeWith c q prefixR k₁ +
        initialAComplement (rawFlag c.R c.V k₁) ≤ certifiedJointMaximum ∧
    sChargeWith c q prefixR k₂ +
        initialAComplement (rawFlag c.R c.V k₂) ≤ certifiedJointMaximum

instance (c : PhaseRowContext) (q : PrefixReceipt) (prefixR lo hi : ℕ) :
    Decidable (SIntervalValid c q prefixR lo hi) := by
  unfold SIntervalValid
  infer_instance

theorem SIntervalValid.sound (c : PhaseRowContext) (q : PrefixReceipt)
    (prefixR lo hi : ℕ) (h : SIntervalValid c q prefixR lo hi)
    (z : ℕ) (hlo : lo ≤ z) (hhi : z ≤ hi) :
    sChargeWith c q prefixR z ≤ certifiedNarrowMaximum ∧
    sChargeWith c q prefixR z + initialAComplement (rawFlag c.R c.V z) ≤
      certifiedJointMaximum := by
  have hAff := sChargeWith_affine c q prefixR lo hi z h.2.1 hlo hhi
  have hAffHi := sChargeWith_affine c q prefixR lo hi hi h.2.1 h.1 le_rfl
  constructor
  · apply (show sChargeWith c q prefixR z ≤ sChargeWith c q prefixR hi by
      rw [hAff, hAffHi]
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hhi lo)) _).trans
    exact h.2.2.1
  · let pref := cachedPrefixAt q 3 (rawFlag prefixR c.V lo)
    have hsLine (x : ℕ) (hlx : lo ≤ x) (hxh : x ≤ hi) :
        sChargeWith c q prefixR x = sLine c.R c.V pref x := by
      unfold sChargeWith sLine pref
      rw [cachedPrefixAt_constant q prefixR c.V 3 lo hi x (by decide)
        h.2.1 hlx hxh]
    have hlo' : sLine c.R c.V pref lo +
        initialAComplement (rawFlag c.R c.V lo) ≤ certifiedJointMaximum := by
      rw [← hsLine lo le_rfl h.1]
      exact h.2.2.2.1
    have hhi' : sLine c.R c.V pref hi +
        initialAComplement (rawFlag c.R c.V hi) ≤ certifiedJointMaximum := by
      rw [← hsLine hi h.1 le_rfl]
      exact h.2.2.2.2.1
    have hk₁lo : lo ≤ max lo (min hi 5811) := le_max_left _ _
    have hk₁hi : max lo (min hi 5811) ≤ hi := by omega
    have hk₁ : sLine c.R c.V pref (max lo (min hi 5811)) +
        initialAComplement (rawFlag c.R c.V (max lo (min hi 5811))) ≤
          certifiedJointMaximum := by
      rw [← hsLine _ hk₁lo hk₁hi]
      exact h.2.2.2.2.2.1
    have hk₂lo : lo ≤ max lo (min hi (5931 - c.V)) := le_max_left _ _
    have hk₂hi : max lo (min hi (5931 - c.V)) ≤ hi := by omega
    have hk₂ : sLine c.R c.V pref (max lo (min hi (5931 - c.V))) +
        initialAComplement (rawFlag c.R c.V
          (max lo (min hi (5931 - c.V)))) ≤ certifiedJointMaximum := by
      rw [← hsLine _ hk₂lo hk₂hi]
      exact h.2.2.2.2.2.2
    have hbound := (sLine_joint_le_of_keypoints c.R c.V pref lo hi
      certifiedJointMaximum h.1 hlo' hhi' hk₁ hk₂) z hlo hhi
    rw [hsLine z hlo hhi]
    exact hbound

def FinalBoundsValid (c : PhaseRowContext) : Prop :=
  let maxZ := 5964 - (c.R + c.V)
  let threshold := thresholdAt c.threshold 3
  threshold ≤ maxZ ∧
    (threshold = 0 ∨ SIntervalValid c c.here c.R 0 (threshold - 1)) ∧
    SIntervalValid c c.parent (c.R - 1) threshold maxZ

instance (c : PhaseRowContext) : Decidable (FinalBoundsValid c) := by
  unfold FinalBoundsValid
  infer_instance

theorem finalBounds_of_runs (c : PhaseRowContext) (runs : List PhaseRun)
    (hruns : RunsValid c 3 (phaseFinish c 3) 0 runs)
    (hfinal : FinalBoundsValid c) (z : ℕ)
    (hz : z < 5965 - (c.R + c.V)) :
    capBefore c 4 z ≤ certifiedNarrowMaximum ∧
      capBefore c 4 z + initialAComplement (rawFlag c.R c.V z) ≤
        certifiedJointMaximum := by
  let threshold := thresholdAt c.threshold 3
  let maxZ := 5964 - (c.R + c.V)
  have hzmax : z ≤ maxZ := by dsimp only [maxZ]; omega
  change threshold ≤ maxZ ∧
    (threshold = 0 ∨ SIntervalValid c c.here c.R 0 (threshold - 1)) ∧
    SIntervalValid c c.parent (c.R - 1) threshold maxZ at hfinal
  by_cases ht : threshold ≤ z
  · have hc : capBefore c 4 z ≤ sChargeWith c c.parent (c.R - 1) z := by
      have hsource := capBefore_le_sourceLine c 4 4 z (by omega) (by
        change thresholdAt c.threshold 3 ≤ z
        exact ht)
      exact hsource
    have hb := SIntervalValid.sound c c.parent (c.R - 1) threshold maxZ
      hfinal.2.2 z ht hzmax
    exact ⟨hc.trans hb.1, Nat.add_le_add_right hc _ |>.trans hb.2⟩
  · have htz : z < threshold := Nat.lt_of_not_ge ht
    have hterminal := phaseTerminal_of_runs c 3 runs (by decide) hruns z hz
    have hc₃ : capBefore c 3 z ≤ hereCharge c 3 z :=
      hterminal.resolve_left (by omega)
    have hc₄ : capBefore c 4 z = capBefore c 3 z := by
      change (if thresholdAt c.threshold 3 ≤ z then
        min (capBefore c 3 z) (parentCharge c 3 z)
        else capBefore c 3 z) = capBefore c 3 z
      rw [if_neg]
      exact ht
    have htpos : threshold ≠ 0 := by omega
    have hhere : SIntervalValid c c.here c.R 0 (threshold - 1) :=
      hfinal.2.1.resolve_left htpos
    have hb := SIntervalValid.sound c c.here c.R 0 (threshold - 1)
      hhere z (Nat.zero_le _) (by omega)
    have hc : capBefore c 4 z ≤ sChargeWith c c.here c.R z := by
      rw [hc₄]
      exact hc₃
    exact ⟨hc.trans hb.1, Nat.add_le_add_right hc _ |>.trans hb.2⟩

def SparseRowValid (c : PhaseRowContext) (runs : Array (List PhaseRun)) : Prop :=
  RowRunsValid c runs ∧ FinalBoundsValid c

instance (c : PhaseRowContext) (runs : Array (List PhaseRun)) :
    Decidable (SparseRowValid c runs) := by
  unfold SparseRowValid
  infer_instance

def SparsePhaseStateRVCheck (c : PhaseRowContext) : Prop :=
  ∀ z, z < 5965 - (c.R + c.V) →
    (thresholdAt c.threshold 0 ≤ z ∨ capBefore c 0 z ≤ hereCharge c 0 z) ∧
    (thresholdAt c.threshold 1 ≤ z ∨ capBefore c 1 z ≤ hereCharge c 1 z) ∧
    (thresholdAt c.threshold 2 ≤ z ∨ capBefore c 2 z ≤ hereCharge c 2 z) ∧
    (thresholdAt c.threshold 3 ≤ z ∨ capBefore c 3 z ≤ hereCharge c 3 z) ∧
    capBefore c 4 z ≤ certifiedNarrowMaximum ∧
    capBefore c 4 z + initialAComplement (rawFlag c.R c.V z) ≤
      certifiedJointMaximum

theorem SparseRowValid.sound (c : PhaseRowContext) (runs : Array (List PhaseRun))
    (h : SparseRowValid c runs) : SparsePhaseStateRVCheck c := by
  intro z hz
  change RowRunsValid c runs ∧ FinalBoundsValid c at h
  rcases h with ⟨hruns, hfinal⟩
  change RunsValid c 0 (phaseFinish c 0) 0 ((runs[0]?).getD []) ∧
    RunsValid c 1 (phaseFinish c 1) 0 ((runs[1]?).getD []) ∧
    RunsValid c 2 (phaseFinish c 2) 0 ((runs[2]?).getD []) ∧
    RunsValid c 3 (phaseFinish c 3) 0 ((runs[3]?).getD []) at hruns
  refine ⟨phaseTerminal_of_runs c 0 _ (by decide) hruns.1 z hz,
    phaseTerminal_of_runs c 1 _ (by decide) hruns.2.1 z hz,
    phaseTerminal_of_runs c 2 _ (by decide) hruns.2.2.1 z hz,
    phaseTerminal_of_runs c 3 _ (by decide) hruns.2.2.2 z hz, ?_⟩
  exact finalBounds_of_runs c _ hruns.2.2.2 hfinal z hz

/-! Maximal-length representative row.  These are ordinary data and theorem
declarations; the external generator emits the same shape for every row. -/

def probeR1V0Runs : Array (List PhaseRun) := #[
  [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨4254, 0⟩],
  [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨65, 0⟩, ⟨369, 0⟩, ⟨673, 0⟩,
    ⟨977, 0⟩, ⟨1281, 0⟩, ⟨1585, 0⟩, ⟨1889, 0⟩, ⟨2193, 0⟩,
    ⟨2497, 0⟩, ⟨2801, 0⟩, ⟨3105, 0⟩, ⟨3409, 0⟩, ⟨3713, 0⟩,
    ⟨4017, 0⟩, ⟨4321, 0⟩, ⟨4625, 0⟩, ⟨4929, 0⟩, ⟨5233, 0⟩,
    ⟨5537, 0⟩, ⟨5841, 0⟩, ⟨5963, 0⟩, ⟨5964, 0⟩],
  [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨3634, 0⟩],
  [⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨3634, 0⟩, ⟨4069, 3⟩]]

theorem probeR1V0Runs_valid :
    RowRunsValid (rowContext 1 0) probeR1V0Runs := by
  decide +kernel

theorem probeR1V0Sparse_valid :
    SparseRowValid (rowContext 1 0) probeR1V0Runs := by
  decide +kernel

theorem probeR1V0_full :
    SparsePhaseStateRVCheck (rowContext 1 0) :=
  (probeR1V0Sparse_valid.sound)

end ProximityPrize.SubmissionLower.LocatorPhase6800PhaseRuns
end PackedLocator_LocatorPhase6800PhaseRuns

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800BaseDirectAudit. -/
section PackedLocator_LocatorPhase6800BaseDirectAudit

/-!
# Base-table soundness over direct `(R,V)` lookup

The dummy array parameter lets this module reuse the already-audited proof
text exactly.  Its local lookup ignores the array; all closed computations
therefore reduce only the selected `rowRR V` branch.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800BaseDirectAudit

open scoped BigOperators
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle

set_option autoImplicit false
set_option maxRecDepth 100000

def lookupBaseRow (_rows : Array BaseRow) (r v : ℕ) : BaseRow :=
  LocatorPhase6800BaseDirectData.lookup r v

def baseTableCap (rows : Array BaseRow) (p : FlagDegree) : ℕ :=
  (lookupBaseRow rows p.all p.yz).evalAt p.zOnly

def baseZeroCap (rows : Array BaseRow) (r v : ℕ) : ℕ :=
  if r = 0 then 0 else baseTableCap rows (rawFlag r v 0)

/-- The sole semantic arithmetic condition required of the compact base
table.  It is finite on the benchmark box.  For every possible carrier
`(r,v)`, the row for the aggregate `(R,V)` dominates that carrier with all
remaining factors charged to the zero-`z` table. -/
def BaseCandidatesSound (rows : Array BaseRow) : Prop :=
  ∀ R V r v z,
    1 ≤ r → r ≤ R → v ≤ V → R ≤ 28 → R + V ≤ 127 →
    (r < R ∨ v = V) → R + V + z ≤ 5964 →
    LocatorOrdinaryZConvex.rawCost r v z +
        baseZeroCap rows (R - r) (V - v) ≤
      baseTableCap rows (rawFlag R V z)

/-- Slope of the carrier's affine ordinary-cost tail, valid from `z = 3`. -/
def candidateSlope (r v : ℕ) : ℕ :=
  LocatorOrdinaryZConvex.rawCost r v 4 -
    LocatorOrdinaryZConvex.rawCost r v 3

/-- Carrier line after adding the exact zero-`z` residual-table value. -/
def candidateLine (rows : Array BaseRow) (R V r v z : ℕ) : ℕ :=
  LocatorOrdinaryZConvex.rawCost r v 3 +
    baseZeroCap rows (R - r) (V - v) + candidateSlope r v * (z - 3)

theorem carrierCost_eq_candidateLine
    (rows : Array BaseRow) (R V r v z : ℕ)
    (hr : 1 ≤ r) (hz : 3 ≤ z) :
    LocatorOrdinaryZConvex.rawCost r v z +
        baseZeroCap rows (R - r) (V - v) =
      candidateLine rows R V r v z := by
  rw [LocatorOrdinaryZConvex.rawCost_affine_from_three r v z hr hz]
  unfold candidateLine candidateSlope
  omega

theorem candidateLine_shift
    (rows : Array BaseRow) (R V r v start z : ℕ)
    (hstart : 3 ≤ start) (hz : start ≤ z) :
    candidateLine rows R V r v z =
      candidateLine rows R V r v start + candidateSlope r v * (z - start) := by
  unfold candidateLine
  have hsplit : z - 3 = (start - 3) + (z - start) := by omega
  rw [hsplit, Nat.mul_add]
  omega

/-- Two affine natural-number functions ordered at the left endpoint remain
ordered when the lower function has no larger slope. -/
theorem affine_le_of_start_and_slope
    (a A m M d : ℕ) (ha : a ≤ A) (hm : m ≤ M) :
    a + m * d ≤ A + M * d := by
  exact Nat.add_le_add ha (Nat.mul_le_mul_right d hm)

/-- Endpoint domination suffices on a finite interval even when the candidate
line has the larger slope. -/
theorem affine_le_between
    (a A m M d finish : ℕ) (hd : d ≤ finish)
    (hstart : a ≤ A)
    (hend : a + m * finish ≤ A + M * finish) :
    a + m * d ≤ A + M * d := by
  by_cases hm : m ≤ M
  · exact affine_le_of_start_and_slope a A m M d hstart hm
  · have hMm : M ≤ m := (Nat.lt_of_not_ge hm).le
    have hdecomp : M + (m - M) = m := Nat.add_sub_of_le hMm
    have hdeltaFinish : a + (m - M) * finish ≤ A := by
      rw [← hdecomp, Nat.add_mul] at hend
      omega
    have hdelta : (m - M) * d ≤ (m - M) * finish :=
      Nat.mul_le_mul_left (m - M) hd
    rw [← hdecomp, Nat.add_mul]
    omega

theorem candidateLine_le_segment_of_start_and_slope
    (rows : Array BaseRow) (R V r v z : ℕ) (s : BaseSegment)
    (hs3 : 3 ≤ s.start) (hsz : s.start ≤ z)
    (hstart : candidateLine rows R V r v s.start ≤ s.valueAtStart)
    (hslope : candidateSlope r v ≤ s.slope) :
    candidateLine rows R V r v z ≤ s.evalAt z := by
  rw [candidateLine_shift rows R V r v s.start z hs3 hsz]
  unfold BaseSegment.evalAt
  exact affine_le_of_start_and_slope _ _ _ _ _ hstart hslope

theorem candidateLine_le_segment_between
    (rows : Array BaseRow) (R V r v z finish : ℕ) (s : BaseSegment)
    (hs3 : 3 ≤ s.start) (hsz : s.start ≤ z) (hzf : z ≤ finish)
    (hstart : candidateLine rows R V r v s.start ≤ s.valueAtStart)
    (hfinish : candidateLine rows R V r v finish ≤ s.evalAt finish) :
    candidateLine rows R V r v z ≤ s.evalAt z := by
  have hsf : s.start ≤ finish := hsz.trans hzf
  rw [candidateLine_shift rows R V r v s.start z hs3 hsz]
  rw [candidateLine_shift rows R V r v s.start finish hs3 hsf] at hfinish
  unfold BaseSegment.evalAt at hfinish ⊢
  apply affine_le_between _ _ _ _ _ _
  · exact Nat.sub_le_sub_right hzf s.start
  · exact hstart
  · exact hfinish

/-- Finite arithmetic checked for one aggregate row and one candidate
carrier.  Every generated row has one or two useful affine segments. -/
def CandidateRowCheck (rows : Array BaseRow) (R V r v : ℕ) : Prop :=
  let q := lookupBaseRow rows R V
  let zero := baseZeroCap rows (R - r) (V - v)
  LocatorOrdinaryZConvex.rawCost r v 0 + zero ≤ q.z0 ∧
  LocatorOrdinaryZConvex.rawCost r v 1 + zero ≤ q.z1 ∧
  LocatorOrdinaryZConvex.rawCost r v 2 + zero ≤ q.z2 ∧
  match q.segments with
  | [s] =>
      s.start = 3 ∧ candidateLine rows R V r v s.start ≤ s.valueAtStart ∧
        candidateSlope r v ≤ s.slope
  | [s₁, s₂] =>
      s₁.start = 3 ∧ s₁.start < s₂.start ∧
        candidateLine rows R V r v s₁.start ≤ s₁.valueAtStart ∧
        candidateLine rows R V r v (s₂.start - 1) ≤
          s₁.evalAt (s₂.start - 1) ∧
        candidateLine rows R V r v s₂.start ≤ s₂.valueAtStart ∧
        candidateSlope r v ≤ s₂.slope
  | _ => False

instance (rows : Array BaseRow) (R V r v : ℕ) :
    Decidable (CandidateRowCheck rows R V r v) := by
  unfold CandidateRowCheck
  dsimp only
  generalize hq : lookupBaseRow rows R V = q
  cases hs : q.segments with
  | nil =>
      simp only [hs]
      infer_instance
  | cons s tail =>
      cases ht : tail with
      | nil =>
          simp only [hs, ht]
          infer_instance
      | cons s₂ rest =>
          cases hu : rest with
          | nil =>
              simp only [hs, ht, hu]
              infer_instance
          | cons s₃ rest₃ =>
              simp only [hs, ht, hu]
              infer_instance

/-- One finite `R` layer of the carrier-row checker. -/
def CandidateRCheck (rows : Array BaseRow) (R : ℕ) : Prop :=
  ∀ V ∈ List.range (128 - R),
    ∀ r ∈ List.range (R + 1), 1 ≤ r →
      ∀ v ∈ List.range (V + 1), (r < R ∨ v = V) →
        CandidateRowCheck rows R V r v

instance (rows : Array BaseRow) (R : ℕ) : Decidable (CandidateRCheck rows R) := by
  unfold CandidateRCheck
  infer_instance

/-- Complete finite base-table checker.  Its executable domain has only the
2.443-million aggregate/carrier splits, not a `z` grid. -/
def BaseCandidateChecks (rows : Array BaseRow) : Prop :=
  ∀ R ∈ List.range 29, 1 ≤ R → CandidateRCheck rows R

instance (rows : Array BaseRow) : Decidable (BaseCandidateChecks rows) := by
  unfold BaseCandidateChecks
  infer_instance

theorem candidateRowCheck_sound
    (rows : Array BaseRow) (R V r v z : ℕ) (hr : 1 ≤ r)
    (hcheck : CandidateRowCheck rows R V r v) :
    LocatorOrdinaryZConvex.rawCost r v z +
        baseZeroCap rows (R - r) (V - v) ≤
      baseTableCap rows (rawFlag R V z) := by
  let q := lookupBaseRow rows R V
  change LocatorOrdinaryZConvex.rawCost r v z +
      baseZeroCap rows (R - r) (V - v) ≤ q.evalAt z
  change
    LocatorOrdinaryZConvex.rawCost r v 0 +
          baseZeroCap rows (R - r) (V - v) ≤ q.z0 ∧
      LocatorOrdinaryZConvex.rawCost r v 1 +
          baseZeroCap rows (R - r) (V - v) ≤ q.z1 ∧
      LocatorOrdinaryZConvex.rawCost r v 2 +
          baseZeroCap rows (R - r) (V - v) ≤ q.z2 ∧
      (match q.segments with
      | [s] =>
          s.start = 3 ∧
            candidateLine rows R V r v s.start ≤ s.valueAtStart ∧
            candidateSlope r v ≤ s.slope
      | [s₁, s₂] =>
          s₁.start = 3 ∧ s₁.start < s₂.start ∧
            candidateLine rows R V r v s₁.start ≤ s₁.valueAtStart ∧
            candidateLine rows R V r v (s₂.start - 1) ≤
              s₁.evalAt (s₂.start - 1) ∧
            candidateLine rows R V r v s₂.start ≤ s₂.valueAtStart ∧
            candidateSlope r v ≤ s₂.slope
      | _ => False) at hcheck
  rcases hcheck with ⟨hzero, hone, htwo, hsegmentsSound⟩
  by_cases hz0 : z = 0
  · subst z
    simpa [BaseRow.evalAt] using hzero
  by_cases hz1 : z = 1
  · subst z
    simpa [BaseRow.evalAt] using hone
  by_cases hz2 : z = 2
  · subst z
    simpa [BaseRow.evalAt] using htwo
  have hz3 : 3 ≤ z := by omega
  rw [carrierCost_eq_candidateLine rows R V r v z hr hz3]
  cases hsegments : q.segments with
  | nil =>
      simp only [hsegments] at hsegmentsSound
  | cons s₁ tail =>
      cases htail : tail with
      | nil =>
          have hsound :
              s₁.start = 3 ∧
                candidateLine rows R V r v s₁.start ≤ s₁.valueAtStart ∧
                candidateSlope r v ≤ s₁.slope := by
            simpa only [hsegments, htail] using hsegmentsSound
          rcases hsound with ⟨hs₁Start, hlineStart, hslope⟩
          have hline := candidateLine_le_segment_of_start_and_slope
            rows R V r v z s₁ (by omega) (by omega) hlineStart hslope
          have heval : q.evalAt z = s₁.evalAt z := by
            simp [BaseRow.evalAt, evalBaseSegments, hsegments, htail,
              hz0, hz1, hz2]
          rw [heval]
          exact hline
      | cons s₂ rest =>
          cases hrest : rest with
          | nil =>
              have hsound :
                  s₁.start = 3 ∧ s₁.start < s₂.start ∧
                    candidateLine rows R V r v s₁.start ≤ s₁.valueAtStart ∧
                    candidateLine rows R V r v (s₂.start - 1) ≤
                      s₁.evalAt (s₂.start - 1) ∧
                    candidateLine rows R V r v s₂.start ≤ s₂.valueAtStart ∧
                    candidateSlope r v ≤ s₂.slope := by
                simpa only [hsegments, htail, hrest] using hsegmentsSound
              rcases hsound with
                ⟨hs₁Start, hs₁₂, hlineStart, hlineFinish,
                  hlineSecond, hslopeSecond⟩
              by_cases hs₂z : s₂.start ≤ z
              · have hline := candidateLine_le_segment_of_start_and_slope
                  rows R V r v z s₂ (by omega) hs₂z hlineSecond
                    hslopeSecond
                have heval : q.evalAt z = s₂.evalAt z := by
                  simp [BaseRow.evalAt, evalBaseSegments, hsegments, htail, hrest,
                    hz0, hz1, hz2, hs₂z]
                rw [heval]
                exact hline
              · have hzf : z ≤ s₂.start - 1 := by omega
                have hline := candidateLine_le_segment_between
                  rows R V r v z (s₂.start - 1) s₁
                    (by omega) (by omega) hzf hlineStart hlineFinish
                have heval : q.evalAt z = s₁.evalAt z := by
                  simp [BaseRow.evalAt, evalBaseSegments, hsegments, htail, hrest,
                    hz0, hz1, hz2, hs₂z]
                rw [heval]
                exact hline
          | cons s₃ rest₃ =>
              simp only [hsegments, htail, hrest] at hsegmentsSound

theorem baseCandidatesSound_of_checks
    (rows : Array BaseRow) (hchecks : BaseCandidateChecks rows) :
    BaseCandidatesSound rows := by
  intro R V r v z hr hrR hvV hR hRV hfits htotal
  have hRpos : 1 ≤ R := hr.trans hrR
  have hRcheck := hchecks R (List.mem_range.mpr (by omega)) hRpos
  have hVcheck := hRcheck V (List.mem_range.mpr (by omega))
  have hrcheck := hVcheck r (List.mem_range.mpr (by omega)) hr
  have hcheck := hrcheck v (List.mem_range.mpr (by omega)) hfits
  exact candidateRowCheck_sound rows R V r v z hr hcheck

theorem ordinaryCostOf_eq_rawCost (p : FlagDegree) :
    LocatorHybridCost.ordinaryCostOf p =
      LocatorOrdinaryZConvex.rawCost p.all p.yz p.zOnly := by
  cases p
  rfl

/-- The `z = 0` part of `BaseCandidatesSound` is exactly the Bellman
inequality needed to aggregate an arbitrary finite zero-`z` family. -/
theorem sum_rawCost_zero_le_baseZeroCap
    (rows : Array BaseRow) (hrows : BaseCandidatesSound rows)
    {ι : Type} [DecidableEq ι] (s : Finset ι) (r v : ι → ℕ)
    (hpositive : ∀ i ∈ s, 1 ≤ r i)
    (hrCap : (∑ i ∈ s, r i) ≤ 28)
    (hrvCap : (∑ i ∈ s, r i) + (∑ i ∈ s, v i) ≤ 127) :
    (∑ i ∈ s, LocatorOrdinaryZConvex.rawCost (r i) (v i) 0) ≤
      baseZeroCap rows (∑ i ∈ s, r i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [baseZeroCap]
  | @insert a s ha ih =>
      have hra : 1 ≤ r a := hpositive a (by simp)
      have hRInsert : r a + (∑ i ∈ s, r i) ≤ 28 := by
        simpa only [Finset.sum_insert ha] using hrCap
      have hRVInsert :
          (r a + ∑ i ∈ s, r i) + (v a + ∑ i ∈ s, v i) ≤ 127 := by
        rw [Finset.sum_insert ha, Finset.sum_insert ha] at hrvCap
        omega
      have hsR : (∑ i ∈ s, r i) ≤ 28 := by
        omega
      have hsRV : (∑ i ∈ s, r i) + (∑ i ∈ s, v i) ≤ 127 := by
        omega
      have ihBound := ih
        (fun i hi ↦ hpositive i (Finset.mem_insert_of_mem hi)) hsR hsRV
      have hfits : r a < r a + (∑ i ∈ s, r i) ∨
          v a = v a + (∑ i ∈ s, v i) := by
        by_cases hs : s.Nonempty
        · obtain ⟨i, hi⟩ := hs
          have hri : 1 ≤ r i :=
            hpositive i (Finset.mem_insert_of_mem hi)
          have hriSum : r i ≤ ∑ j ∈ s, r j :=
            Finset.single_le_sum (f := fun j ↦ r j)
              (fun _ _ ↦ Nat.zero_le _) hi
          left
          omega
        · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
          subst s
          simp
      have hcandidate := hrows
        (r a + ∑ i ∈ s, r i) (v a + ∑ i ∈ s, v i)
        (r a) (v a) 0 hra (by omega) (by omega)
        hRInsert hRVInsert hfits
        (by omega)
      have hposSum : 1 ≤ r a + ∑ i ∈ s, r i := by omega
      calc
        (∑ i ∈ insert a s,
            LocatorOrdinaryZConvex.rawCost (r i) (v i) 0) =
            LocatorOrdinaryZConvex.rawCost (r a) (v a) 0 +
              ∑ i ∈ s, LocatorOrdinaryZConvex.rawCost (r i) (v i) 0 := by
              rw [Finset.sum_insert ha]
        _ ≤ LocatorOrdinaryZConvex.rawCost (r a) (v a) 0 +
              baseZeroCap rows (∑ i ∈ s, r i) (∑ i ∈ s, v i) :=
            Nat.add_le_add_left ihBound _
        _ ≤ baseTableCap rows
              (rawFlag (r a + ∑ i ∈ s, r i)
                (v a + ∑ i ∈ s, v i) 0) := by
            simpa only [Nat.add_sub_cancel_left] using hcandidate
        _ = baseZeroCap rows (∑ i ∈ insert a s, r i)
              (∑ i ∈ insert a s, v i) := by
            simp only [Finset.sum_insert ha, baseZeroCap,
              if_neg (Nat.ne_of_gt hposSum)]

/-- A checked carrier table gives the genuinely state-local base oracle.  The
proof first concentrates all `z` on one factor, bounds the remaining zero-`z`
family by the same Bellman table, and finally applies that carrier's row. -/
theorem stateLocalBaseOracleSound_of_candidates
    (rows : Array BaseRow) (hrows : BaseCandidatesSound rows) :
    StateLocalBaseOracleSound (baseTableCap rows) := by
  intro ι inst s p hpositive hrCap hyCap htCap
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨c, hc, hconcentrate⟩ :=
      LocatorOrdinaryConcentration.exists_z_carrier s
        (fun i ↦ (p i).all) (fun i ↦ (p i).yz) (fun i ↦ (p i).zOnly)
        hpositive hs
    have hzero := sum_rawCost_zero_le_baseZeroCap rows hrows (s.erase c)
      (fun i ↦ (p i).all) (fun i ↦ (p i).yz)
      (fun i hi ↦ hpositive i (Finset.mem_of_mem_erase hi))
      (by
        have hsub : s.erase c ⊆ s := Finset.erase_subset c s
        have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ ↦ Nat.zero_le _) (f := fun i ↦ (p i).all)
        exact hle.trans hrCap)
      (by
        have hsub : s.erase c ⊆ s := Finset.erase_subset c s
        have hrle := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ ↦ Nat.zero_le _) (f := fun i ↦ (p i).all)
        have hvle := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ ↦ Nat.zero_le _) (f := fun i ↦ (p i).yz)
        have hmiddle : (∑ i ∈ s, (p i).all) + (∑ i ∈ s, (p i).yz) ≤ 127 := by
          rw [sumFlag_middle] at hyCap
          simp only [middle, Finset.sum_add_distrib] at hyCap
          omega
        omega)
    have hcR : (p c).all ≤ ∑ i ∈ s, (p i).all := by
      exact Finset.single_le_sum (f := fun i ↦ (p i).all)
        (fun _ _ ↦ Nat.zero_le _) hc
    have hcV : (p c).yz ≤ ∑ i ∈ s, (p i).yz := by
      exact Finset.single_le_sum (f := fun i ↦ (p i).yz)
        (fun _ _ ↦ Nat.zero_le _) hc
    have hmiddle : (∑ i ∈ s, (p i).all) + (∑ i ∈ s, (p i).yz) ≤ 127 := by
      rw [sumFlag_middle] at hyCap
      simp only [middle, Finset.sum_add_distrib] at hyCap
      omega
    have htotal : (∑ i ∈ s, (p i).all) + (∑ i ∈ s, (p i).yz) +
        (∑ i ∈ s, (p i).zOnly) ≤ 5964 := by
      rw [sumFlag_total] at htCap
      simp only [total, middle, Finset.sum_add_distrib] at htCap
      omega
    have hrErase := Finset.sum_erase_add s (fun i ↦ (p i).all) hc
    have hvErase := Finset.sum_erase_add s (fun i ↦ (p i).yz) hc
    have hfits :
        (p c).all < ∑ i ∈ s, (p i).all ∨
          (p c).yz = ∑ i ∈ s, (p i).yz := by
      by_cases hrest : (s.erase c).Nonempty
      · obtain ⟨i, hi⟩ := hrest
        have hiS : i ∈ s := Finset.mem_of_mem_erase hi
        have hri : 1 ≤ (p i).all := hpositive i hiS
        have hriSum : (p i).all ≤ ∑ j ∈ s.erase c, (p j).all :=
          Finset.single_le_sum (f := fun j ↦ (p j).all)
            (fun _ _ ↦ Nat.zero_le _) hi
        left
        omega
      · have hrest0 : s.erase c = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hrest
        right
        rw [hrest0] at hvErase
        simp only [Finset.sum_empty] at hvErase
        omega
    have hcandidate := hrows
      (∑ i ∈ s, (p i).all) (∑ i ∈ s, (p i).yz)
      (p c).all (p c).yz (∑ i ∈ s, (p i).zOnly)
      (hpositive c hc) hcR hcV hrCap hmiddle hfits htotal
    have hzero' :
        (∑ i ∈ s.erase c,
            LocatorOrdinaryZConvex.rawCost (p i).all (p i).yz 0) ≤
          baseZeroCap rows
            ((∑ i ∈ s, (p i).all) - (p c).all)
            ((∑ i ∈ s, (p i).yz) - (p c).yz) := by
      simpa only [show (∑ i ∈ s, (p i).all) - (p c).all =
          ∑ i ∈ s.erase c, (p i).all by omega,
        show (∑ i ∈ s, (p i).yz) - (p c).yz =
          ∑ i ∈ s.erase c, (p i).yz by omega] using hzero
    have hcostEq :
        (∑ i ∈ s, LocatorHybridCost.ordinaryCostOf (p i)) =
          ∑ i ∈ s, LocatorOrdinaryZConvex.rawCost
            (p i).all (p i).yz (p i).zOnly := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ordinaryCostOf_eq_rawCost (p i)
    have hflagEq : sumFlag s p =
        rawFlag (∑ i ∈ s, (p i).all) (∑ i ∈ s, (p i).yz)
          (∑ i ∈ s, (p i).zOnly) := rfl
    rw [hcostEq, hflagEq]
    exact hconcentrate.trans ((Nat.add_le_add_left hzero' _).trans hcandidate)
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp

end ProximityPrize.SubmissionLower.LocatorPhase6800BaseDirectAudit
end PackedLocator_LocatorPhase6800BaseDirectAudit

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseBridge. -/
section PackedLocator_LocatorPhase6800BaseSparseBridge

/-!
# Sparse base-candidate bridge

The carrier objective is coordinatewise discretely convex.  Consequently a
split of the total `R` coordinate is bounded by one of the two positive
endpoints, and (away from the two hybrid-boundary layers) the same is true of
the `V` coordinate.  This reduces the finite receipt from every carrier to

* the aggregate carrier itself; and
* `r = 1` or `r = R - 1`, with
  `v ∈ {0, 1, 2, V - 2, V - 1, V}`.

The definitions below deliberately separate the generic convexity argument
from the concrete arithmetic proof of the four shape fields.  There are only
38,239 sparse carrier rows in the benchmark box (at most 13 for one `(R,V)`).
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseBridge

open LocatorPhase6800Oracle LocatorPhase6800BaseDirectAudit
open LocatorOrdinaryZConvex

set_option autoImplicit false
set_option maxRecDepth 100000

/-- The two positive endpoints of an `R` split, together with the unsplit
aggregate carrier. -/
def RBoundary (R r : ℕ) : Prop := r = R ∨ r = 1 ∨ r + 1 = R

/-- The only `V` values left after applying convexity on the shifted interior
`v ≥ 2`, `V-v ≥ 2`. -/
def VBoundary (V v : ℕ) : Prop := v ≤ 2 ∨ V ≤ v + 2

/-- Monotonicity restricted to the finite prefix `0, ..., N`. -/
def StepMonotone (f : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ n, n < N → f n ≤ f (n + 1)

/-- Midpoint convexity restricted to the finite prefix `0, ..., N`. -/
def StepConvex (f : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ n, n + 2 ≤ N → 2 * f (n + 1) ≤ f n + f (n + 2)

theorem forwardDiff_mono_bounded (f : ℕ → ℕ) (N n : ℕ)
    (hm : StepMonotone f N) (hc : StepConvex f N)
    (hn : n + 2 ≤ N) :
    forwardDiff f n ≤ forwardDiff f (n + 1) := by
  have h₀ := hm n (by omega)
  have h₁ := hm (n + 1) (by omega)
  have h₂ := hc n hn
  unfold forwardDiff
  rw [show n + 1 + 1 = n + 2 by omega]
  omega

theorem move_one_right_bounded (f g : ℕ → ℕ) (N : ℕ)
    (hf : StepMonotone f N) (hg : StepMonotone g N)
    (a b : ℕ) (ha : a < N) (hb : b < N)
    (hcross : forwardDiff f a ≤ forwardDiff g b) :
    f (a + 1) + g b ≤ f a + g (b + 1) := by
  have hfa := hf a ha
  have hgb := hg b hb
  unfold forwardDiff at hcross
  omega

theorem transfer_all_right_bounded
    (f g : ℕ → ℕ) (N : ℕ)
    (hf : StepMonotone f N) (hg : StepMonotone g N)
    (hcf : StepConvex f N) (hcg : StepConvex g N) :
    ∀ a b, a + 1 + b ≤ N → forwardDiff f a ≤ forwardDiff g b →
      f (a + 1) + g b ≤ f 0 + g (a + 1 + b) := by
  intro a
  induction a with
  | zero =>
      intro b hbound hcross
      simpa only [Nat.zero_add, Nat.add_comm] using
        move_one_right_bounded f g N hf hg 0 b (by omega) (by omega) hcross
  | succ a ih =>
      intro b hbound hcross
      have hdf : forwardDiff f a ≤ forwardDiff f (a + 1) :=
        forwardDiff_mono_bounded f N a hf hcf (by omega)
      have hdg : forwardDiff g b ≤ forwardDiff g (b + 1) :=
        forwardDiff_mono_bounded g N b hg hcg (by omega)
      have hcross' : forwardDiff f a ≤ forwardDiff g (b + 1) :=
        hdf.trans (hcross.trans hdg)
      calc
        f (a + 1 + 1) + g b ≤ f (a + 1) + g (b + 1) :=
          move_one_right_bounded f g N hf hg (a + 1) b
            (by omega) (by omega) hcross
        _ ≤ f 0 + g (a + 1 + (b + 1)) := ih (b + 1) (by omega) hcross'
        _ = f 0 + g (a + 1 + 1 + b) := by
          rw [show a + 1 + (b + 1) = a + 1 + 1 + b by omega]

/-- Finite-prefix version of `two_discreteConvex_endpoint`. -/
theorem two_discreteConvex_endpoint_bounded
    (f g : ℕ → ℕ) (N : ℕ)
    (hf : StepMonotone f N) (hg : StepMonotone g N)
    (hcf : StepConvex f N) (hcg : StepConvex g N)
    (a b : ℕ) (hbound : a + b ≤ N) :
    f a + g b ≤ max (f (a + b) + g 0) (f 0 + g (a + b)) := by
  rcases a with _ | a
  · simpa only [Nat.zero_add] using
      (le_max_right (f b + g 0) (f 0 + g b))
  rcases b with _ | b
  · simpa only [Nat.add_zero] using
      (le_max_left (f (a + 1) + g 0) (f 0 + g (a + 1)))
  have hdf (n : ℕ) (hn : n + 2 ≤ N) :
      forwardDiff f n ≤ forwardDiff f (n + 1) :=
    forwardDiff_mono_bounded f N n hf hcf hn
  have hdg (n : ℕ) (hn : n + 2 ≤ N) :
      forwardDiff g n ≤ forwardDiff g (n + 1) :=
    forwardDiff_mono_bounded g N n hg hcg hn
  by_cases hcross : forwardDiff f a ≤ forwardDiff g (b + 1)
  · have h := transfer_all_right_bounded f g N hf hg hcf hcg
      a (b + 1) (by omega) hcross
    exact h.trans (le_max_right _ _)
  · have hcross' : forwardDiff g b ≤ forwardDiff f (a + 1) :=
      (hdg b (by omega)).trans
        ((Nat.lt_of_not_ge hcross).le.trans (hdf a (by omega)))
    have h := transfer_all_right_bounded g f N hg hf hcg hcf
      b (a + 1) (by omega) hcross'
    have h' : f (a + 1) + g (b + 1) ≤
        f ((a + 1) + (b + 1)) + g 0 := by
      simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    exact h'.trans (le_max_left _ _)

/-- Coordinate-shape facts used by the sparse bridge.  The shifts avoid the
padding/hybrid branch boundaries at `r = 1` and `v = 0,1`.  The zero-cost
function is abstract on purpose: the concrete proof uses a total closed-form
model, avoiding the out-of-range default of a finite receipt array. -/
structure CoordinateShape (zero : ℕ → ℕ → ℕ) : Prop where
  rawMonoR : ∀ v z n, n + 2 ≤ 28 → n + 2 + v ≤ 127 →
    rawCost (n + 1) v z ≤ rawCost (n + 2) v z
  rawConvexR : ∀ v z n, n + 3 ≤ 28 → n + 3 + v ≤ 127 →
    2 * rawCost (n + 2) v z ≤ rawCost (n + 1) v z + rawCost (n + 3) v z
  zeroMonoR : ∀ v n, n + 2 ≤ 28 → n + 2 + v ≤ 127 →
    zero (n + 1) v ≤ zero (n + 2) v
  zeroConvexR : ∀ v n, n + 3 ≤ 28 → n + 3 + v ≤ 127 →
    2 * zero (n + 2) v ≤ zero (n + 1) v + zero (n + 3) v
  rawMonoV2 : ∀ r z n, 1 ≤ r → r ≤ 28 → r + (n + 3) ≤ 127 →
    rawCost r (n + 2) z ≤ rawCost r (n + 3) z
  rawConvexV2 : ∀ r z n, 1 ≤ r → r ≤ 28 → r + (n + 4) ≤ 127 →
    2 * rawCost r (n + 3) z ≤ rawCost r (n + 2) z + rawCost r (n + 4) z
  zeroMonoV2 : ∀ r n, 1 ≤ r → r ≤ 28 → r + (n + 3) ≤ 127 →
    zero r (n + 2) ≤ zero r (n + 3)
  zeroConvexV2 : ∀ r n, 1 ≤ r → r ≤ 28 → r + (n + 4) ≤ 127 →
    2 * zero r (n + 3) ≤ zero r (n + 2) + zero r (n + 4)

/-- Only boundary carriers need a numerical `CandidateRowCheck`. -/
def SparseCandidateChecks (rows : Array BaseRow) : Prop :=
  ∀ R V r v,
    1 ≤ r → r ≤ R → v ≤ V → R ≤ 28 → R + V ≤ 127 →
    (r < R ∨ v = V) → RBoundary R r → VBoundary V v →
      CandidateRowCheck rows R V r v

/-- Convexity in the positive `R` split. -/
theorem splitR_le_endpoints (zero : ℕ → ℕ → ℕ)
    (shape : CoordinateShape zero) (a b v w z : ℕ)
    (hR : a + b + 2 ≤ 28)
    (hraw : a + b + 2 + v ≤ 127)
    (hzero : a + b + 2 + w ≤ 127) :
    rawCost (a + 1) v z + zero (b + 1) w ≤
      max
        (rawCost (a + b + 1) v z + zero 1 w)
        (rawCost 1 v z + zero (a + b + 1) w) := by
  apply two_discreteConvex_endpoint_bounded
    (fun n => rawCost (n + 1) v z)
    (fun n => zero (n + 1) w)
    (a + b)
  · intro n hn
    exact shape.rawMonoR v z n (by omega) (by omega)
  · intro n hn
    exact shape.zeroMonoR w n (by omega) (by omega)
  · intro n hn
    exact shape.rawConvexR v z n (by omega) (by omega)
  · intro n hn
    exact shape.zeroConvexR w n (by omega) (by omega)
  · omega

/-- Convexity on the interior `V` split, shifted past `v = 0,1`. -/
theorem splitV_le_endpoints (zero : ℕ → ℕ → ℕ)
    (shape : CoordinateShape zero) (r s a b z : ℕ)
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hr28 : r ≤ 28) (hs28 : s ≤ 28)
    (hraw : r + (a + b + 4) ≤ 127)
    (hzero : s + (a + b + 4) ≤ 127) :
    rawCost r (a + 2) z + zero s (b + 2) ≤
      max
        (rawCost r (a + b + 2) z + zero s 2)
        (rawCost r 2 z + zero s (a + b + 2)) := by
  apply two_discreteConvex_endpoint_bounded
    (fun n => rawCost r (n + 2) z)
    (fun n => zero s (n + 2))
    (a + b)
  · intro n hn
    exact shape.rawMonoV2 r z n hr hr28 (by omega)
  · intro n hn
    exact shape.zeroMonoV2 s n hs hs28 (by omega)
  · intro n hn
    exact shape.rawConvexV2 r z n hr hr28 (by omega)
  · intro n hn
    exact shape.zeroConvexV2 s n hs hs28 (by omega)
  · omega

/-- Pointwise Bellman inequality reconstructed from the sparse carrier set. -/
theorem candidate_le_of_sparse (rows : Array BaseRow)
    (zero : ℕ → ℕ → ℕ) (shape : CoordinateShape zero)
    (zero_eq : ∀ r v, r ≤ 28 → r + v ≤ 127 →
      zero r v = baseZeroCap rows r v)
    (checks : SparseCandidateChecks rows)
    (R V r v z : ℕ)
    (hr : 1 ≤ r) (hrR : r ≤ R) (hvV : v ≤ V)
    (hR28 : R ≤ 28) (hRV : R + V ≤ 127)
    (hcandidate : r < R ∨ v = V) :
    rawCost r v z + baseZeroCap rows (R - r) (V - v) ≤
      LocatorPhase6800BaseDirectAudit.baseTableCap rows (rawFlag R V z) := by
  have sparseSound (r₀ v₀ : ℕ)
      (hr₀ : 1 ≤ r₀) (hr₀R : r₀ ≤ R) (hv₀V : v₀ ≤ V)
      (hc₀ : r₀ < R ∨ v₀ = V)
      (hRb : RBoundary R r₀) (hVb : VBoundary V v₀) :
      rawCost r₀ v₀ z + zero (R - r₀) (V - v₀) ≤
        LocatorPhase6800BaseDirectAudit.baseTableCap rows (rawFlag R V z) := by
    rw [zero_eq (R - r₀) (V - v₀) (by omega) (by omega)]
    exact candidateRowCheck_sound rows R V r₀ v₀ z hr₀
      (checks R V r₀ v₀ hr₀ hr₀R hv₀V hR28 hRV hc₀ hRb hVb)

  rw [← zero_eq (R - r) (V - v) (by omega) (by omega)]
  by_cases hself : r = R
  · have hvself : v = V := by rcases hcandidate with hlt | heq <;> omega
    subst r
    subst v
    simpa using sparseSound R V hr (le_rfl) (le_rfl) (Or.inr rfl)
      (Or.inl rfl) (Or.inr (by omega))
  · have hrlt : r < R := lt_of_le_of_ne hrR hself
    obtain ⟨a, haSucc⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    have ha : r = a + 1 := by omega
    obtain ⟨b, hbSucc⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.sub_pos_of_lt hrlt))
    have hb : R - r = b + 1 := by omega
    have hRsum : R = a + b + 2 := by omega

    have endpointV (r₀ s₀ : ℕ)
        (hr₀ : 1 ≤ r₀) (hs₀ : 1 ≤ s₀)
        (hsum : r₀ + s₀ = R)
        (hRb : RBoundary R r₀) :
        rawCost r₀ v z + zero s₀ (V - v) ≤
          LocatorPhase6800BaseDirectAudit.baseTableCap rows (rawFlag R V z) := by
      have hr₀R : r₀ ≤ R := by omega
      have hr₀lt : r₀ < R := by omega
      by_cases hvLow : v ≤ 2
      · simpa [show R - r₀ = s₀ by omega] using
          sparseSound r₀ v hr₀ hr₀R hvV (Or.inl hr₀lt) hRb (Or.inl hvLow)
      by_cases hwLow : V - v ≤ 2
      · have hnear : V ≤ v + 2 := by omega
        simpa [show R - r₀ = s₀ by omega] using
          sparseSound r₀ v hr₀ hr₀R hvV (Or.inl hr₀lt) hRb (Or.inr hnear)
      · obtain ⟨c, hcAdd⟩ := Nat.exists_eq_add_of_le (show 2 ≤ v by omega)
        have hc : v = c + 2 := by omega
        obtain ⟨d, hdAdd⟩ :=
          Nat.exists_eq_add_of_le (show 2 ≤ V - v by omega)
        have hd : V - v = d + 2 := by omega
        have hVsum : V = c + d + 4 := by omega
        have hleft :
            rawCost r₀ (c + d + 2) z + zero s₀ 2 ≤
              LocatorPhase6800BaseDirectAudit.baseTableCap rows (rawFlag R V z) := by
          have hv' : c + d + 2 ≤ V := by omega
          have hnear : V ≤ (c + d + 2) + 2 := by omega
          simpa [show R - r₀ = s₀ by omega, show V - (c + d + 2) = 2 by omega]
            using sparseSound r₀ (c + d + 2) hr₀ hr₀R hv'
              (Or.inl hr₀lt) hRb (Or.inr hnear)
        have hright :
            rawCost r₀ 2 z + zero s₀ (c + d + 2) ≤
              LocatorPhase6800BaseDirectAudit.baseTableCap rows (rawFlag R V z) := by
          have hv' : 2 ≤ V := by omega
          simpa [show R - r₀ = s₀ by omega, show V - 2 = c + d + 2 by omega]
            using sparseSound r₀ 2 hr₀ hr₀R hv'
              (Or.inl hr₀lt) hRb (Or.inl (by omega))
        have hsplit := splitV_le_endpoints zero shape r₀ s₀ c d z
          hr₀ hs₀ (by omega) (by omega) (by omega) (by omega)
        rw [← hc, ← hd] at hsplit
        exact hsplit.trans (max_le hleft hright)

    have hleft :
        rawCost (a + b + 1) v z + zero 1 (V - v) ≤
          LocatorPhase6800BaseDirectAudit.baseTableCap rows (rawFlag R V z) := by
      apply endpointV (a + b + 1) 1 (by omega) (by omega) (by omega)
      exact Or.inr (Or.inr (by omega))
    have hright :
        rawCost 1 v z + zero (a + b + 1) (V - v) ≤
          LocatorPhase6800BaseDirectAudit.baseTableCap rows (rawFlag R V z) := by
      apply endpointV 1 (a + b + 1) (by omega) (by omega) (by omega)
      exact Or.inr (Or.inl rfl)
    have hsplit := splitR_le_endpoints zero shape a b v (V - v) z
      (by omega) (by omega) (by omega)
    rw [← ha, ← hb] at hsplit
    exact hsplit.trans (max_le hleft hright)

/-- Sparse coordinate checks imply the complete Bellman table condition. -/
theorem baseCandidatesSound_of_sparse (rows : Array BaseRow)
    (zero : ℕ → ℕ → ℕ) (shape : CoordinateShape zero)
    (zero_eq : ∀ r v, r ≤ 28 → r + v ≤ 127 →
      zero r v = baseZeroCap rows r v)
    (checks : SparseCandidateChecks rows) :
    BaseCandidatesSound rows := by
  intro R V r v z hr hrR hvV hR28 hRV hcandidate _hz
  exact candidate_le_of_sparse rows zero shape zero_eq checks R V r v z
    hr hrR hvV hR28 hRV hcandidate

end ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseBridge
end PackedLocator_LocatorPhase6800BaseSparseBridge

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostDirectCore. -/
section PackedLocator_LocatorPhase6800CarrierCostDirectCore

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostDirectData

set_option autoImplicit false
set_option maxRecDepth 100000

structure Costs where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  deriving DecidableEq, Repr

def defaultCosts : Costs := ⟨0, 0, 0, 0, 0⟩

def row1 : ℕ → Costs
  | 0 => ⟨274881052677, 481041580039, 687202107401, 1168243163149, 1649284218897⟩
  | 1 => ⟨481041580039, 687202107401, 1305683165197, 1924164222993, 2542645280789⟩
  | 2 => ⟨687202107401, 1443123167245, 2199044227089, 2954965286933, 3710886346777⟩
  | 3 => ⟨1649283170317, 2817524236305, 3985765302293, 5154006368281, 6322247434269⟩
  | 4 => ⟨3023684239377, 4604245311509, 6184806383641, 7765367455773, 9345928527905⟩
  | 5 => ⟨4810405314581, 6803286392857, 8796167471133, 10789048549409, 12781929627685⟩
  | 6 => ⟨7009446395929, 9414647480349, 11819848564769, 14225049649189, 16630250733609⟩
  | 7 => ⟨9620807483421, 12438328573985, 15255849664549, 18073370755113, 20890891845677⟩
  | 8 => ⟨12644488577057, 15874329673765, 19104170770473, 22334011867181, 25563852963889⟩
  | 9 => ⟨16080489676837, 19722650779689, 23364811882541, 27006972985393, 30649134088245⟩
  | 10 => ⟨19928810782761, 23983291891757, 28037773000753, 32092254109749, 36146735218745⟩
  | 11 => ⟨24189451894829, 28656253009969, 33123054125109, 37589855240249, 42056656355389⟩
  | 12 => ⟨28862413013041, 33741534134325, 38620655255609, 43499776376893, 48378897498177⟩
  | 13 => ⟨33947694137397, 39239135264825, 44530576392253, 49822017519681, 55113458647109⟩
  | 14 => ⟨39445295267897, 45149056401469, 50852817535041, 56556578668613, 62260339802185⟩
  | 15 => ⟨45355216404541, 51471297544257, 57587378683973, 63703459823689, 69819540963405⟩
  | 16 => ⟨51677457547329, 58205858693189, 64734259839049, 71262660984909, 77791062130769⟩
  | 17 => ⟨58412018696261, 65352739848265, 72293461000269, 79234182152273, 86174903304277⟩
  | 18 => ⟨65558899851337, 72911941009485, 80264982167633, 87618023325781, 94971064483929⟩
  | 19 => ⟨73118101012557, 80883462176849, 88648823341141, 96414184505433, 104179545669725⟩
  | 20 => ⟨81089622179921, 89267303350357, 97444984520793, 105622665691229, 113800346861665⟩
  | 21 => ⟨89473463353429, 98063464530009, 106653465706589, 115243466883169, 123833468059749⟩
  | 22 => ⟨98269624533081, 107271945715805, 116274266898529, 125276588081253, 134278909263977⟩
  | 23 => ⟨107478105718877, 116892746907745, 126307388096613, 135722029285481, 145136670474349⟩
  | 24 => ⟨117098906910817, 126925868105829, 136752829300841, 146579790495853, 156406751690865⟩
  | 25 => ⟨127132028108901, 137371309310057, 147610590511213, 157849871712369, 168089152913525⟩
  | 26 => ⟨137577469313129, 148229070520429, 158880671727729, 169532272935029, 180183874142329⟩
  | 27 => ⟨148435230523501, 159499151736945, 170563072950389, 181626994163833, 192690915377277⟩
  | 28 => ⟨159705311740017, 171181552959605, 182657794179193, 194134035398781, 205610276618369⟩
  | 29 => ⟨171387712962677, 183276274188409, 195164835414141, 207053396639873, 218941957865605⟩
  | 30 => ⟨183482434191481, 195783315423357, 208084196655233, 220385077887109, 232685959118985⟩
  | 31 => ⟨195989475426429, 208702676664449, 221415877902469, 234129079140489, 246842280378509⟩
  | 32 => ⟨208908836667521, 222034357911685, 235159879155849, 248285400400013, 261410921644177⟩
  | 33 => ⟨222240517914757, 235778359165065, 249316200415373, 262854041665681, 276391882915989⟩
  | 34 => ⟨235984519168137, 249934680424589, 263884841681041, 277835002937493, 291785164193945⟩
  | 35 => ⟨250140840427661, 264503321690257, 278865802952853, 293228284215449, 307590765478045⟩
  | 36 => ⟨264709481693329, 279484282962069, 294259084230809, 309033885499549, 323808686768289⟩
  | 37 => ⟨279690442965141, 294877564240025, 310064685514909, 325251806789793, 340438928064677⟩
  | 38 => ⟨295083724243097, 310683165524125, 326282606805153, 341882048086181, 357481489367209⟩
  | 39 => ⟨310889325527197, 326901086814369, 342912848101541, 358924609388713, 374936370675885⟩
  | 40 => ⟨327107246817441, 343531328110757, 359955409404073, 376379490697389, 392803571990705⟩
  | 41 => ⟨343737488113829, 360573889413289, 377410290712749, 394246692012209, 411083093311669⟩
  | 42 => ⟨360780049416361, 378028770721965, 395277492027569, 412526213333173, 429774934638777⟩
  | 43 => ⟨378234930725037, 395895972036785, 413557013348533, 431218054660281, 448879095972029⟩
  | 44 => ⟨396102132039857, 414175493357749, 432248854675641, 450322215993533, 468395577311425⟩
  | 45 => ⟨414381653360821, 432867334684857, 451353016008893, 469838697332929, 488324378656965⟩
  | 46 => ⟨433073494687929, 451971496018109, 470869497348289, 489767498678469, 508665500008649⟩
  | 47 => ⟨452177656021181, 471487977357505, 490798298693829, 510108620030153, 529418941366477⟩
  | 48 => ⟨471694137360577, 491416778703045, 511139420045513, 530862061387981, 550584702730449⟩
  | 49 => ⟨491622938706117, 511757900054729, 531892861403341, 552027822751953, 572162784100565⟩
  | 50 => ⟨511964060057801, 532511341412557, 553058622767313, 573605904122069, 594153185476825⟩
  | 51 => ⟨532717501415629, 553677102776529, 574636704137429, 595596305498329, 616555906859229⟩
  | 52 => ⟨553883262779601, 575255184146645, 596627105513689, 617999026880733, 639370948247777⟩
  | 53 => ⟨575461344149717, 597245585522905, 619029826896093, 640814068269281, 662598309642469⟩
  | 54 => ⟨597451745525977, 619648306905309, 641844868284641, 664041429663973, 686237991043305⟩
  | 55 => ⟨619854466908381, 642463348293857, 665072229679333, 687681111064809, 710289992450285⟩
  | 56 => ⟨642669508296929, 665690709688549, 688711911080169, 711733112471789, 734754313863409⟩
  | 57 => ⟨665896869691621, 689330391089385, 712763912487149, 736197433884913, 759630955282677⟩
  | 58 => ⟨689536551092457, 713382392496365, 737228233900273, 761074075304181, 784919916708089⟩
  | 59 => ⟨713588552499437, 737846713909489, 762104875319541, 786363036729593, 810621198139645⟩
  | 60 => ⟨738052873912561, 762723355328757, 787393836744953, 812064318161149, 836734799577345⟩
  | 61 => ⟨762929515331829, 788012316754169, 813095118176509, 838177919598849, 863260721021189⟩
  | 62 => ⟨788218476757241, 813713598185725, 839208719614209, 864703841042693, 890198962471177⟩
  | 63 => ⟨813919758188797, 839827199623425, 865734641058053, 891642082492681, 917549523927309⟩
  | 64 => ⟨840033359626497, 866353121067269, 892672882508041, 918992643948813, 945312405389585⟩
  | 65 => ⟨866559281070341, 893291362517257, 920023443964173, 946755525411089, 973487606858005⟩
  | 66 => ⟨893497522520329, 920641923973389, 947786325426449, 974930726879509, 1002075128332569⟩
  | 67 => ⟨920848083976461, 948404805435665, 975961526894869, 1003518248354073, 1031074969813277⟩
  | 68 => ⟨948610965438737, 976580006904085, 1004549048369433, 1032518089834781, 1060487131300129⟩
  | 69 => ⟨976786166907157, 1005167528378649, 1033548889850141, 1061930251321633, 1090311612793125⟩
  | 70 => ⟨1005373688381721, 1034167369859357, 1062961051336993, 1091754732814629, 1120548414292265⟩
  | 71 => ⟨1034373529862429, 1063579531346209, 1092785532829989, 1121991534313769, 1151197535797549⟩
  | 72 => ⟨1063785691349281, 1093404012839205, 1123022334329129, 1152640655819053, 1182258977308977⟩
  | 73 => ⟨1093610172842277, 1123640814338345, 1153671455834413, 1183702097330481, 1213732738826549⟩
  | 74 => ⟨1123846974341417, 1154289935843629, 1184732897345841, 1215175858848053, 1245618820350265⟩
  | 75 => ⟨1154496095846701, 1185351377355057, 1216206658863413, 1247061940371769, 1277917221880125⟩
  | 76 => ⟨1185557537358129, 1216825138872629, 1248092740387129, 1279360341901629, 1310627943416129⟩
  | 77 => ⟨1217031298875701, 1248711220396345, 1280391141916989, 1312071063437633, 1343750984958277⟩
  | 78 => ⟨1248917380399417, 1281009621926205, 1313101863452993, 1345194104979781, 1377286346506569⟩
  | 79 => ⟨1281215781929277, 1313720343462209, 1346224904995141, 1378729466528073, 1411234028061005⟩
  | 80 => ⟨1313926503465281, 1346843385004357, 1379760266543433, 1412677148082509, 1445594029621585⟩
  | 81 => ⟨1347049545007429, 1380378746552649, 1413707948097869, 1447037149643089, 1480366351188309⟩
  | 82 => ⟨1380584906555721, 1414326428107085, 1448067949658449, 1481809471209813, 1515550992761177⟩
  | 83 => ⟨1414532588110157, 1448686429667665, 1482840271225173, 1516994112782681, 1551147954340189⟩
  | 84 => ⟨1448892589670737, 1483458751234389, 1518024912798041, 1552591074361693, 1587157235925345⟩
  | 85 => ⟨1483664911237461, 1518643392807257, 1553621874377053, 1588600355946849, 1623578837516645⟩
  | 86 => ⟨1518849552810329, 1554240354386269, 1589631155962209, 1625021957538149, 1660412759114089⟩
  | 87 => ⟨1554446514389341, 1590249635971425, 1626052757553509, 1661855879135593, 1697659000717677⟩
  | 88 => ⟨1590455795974497, 1626671237562725, 1662886679150953, 1699102120739181, 1735317562327409⟩
  | 89 => ⟨1626877397565797, 1663505159160169, 1700132920754541, 1736760682348913, 1773388443943285⟩
  | 90 => ⟨1663711319163241, 1700751400763757, 1737791482364273, 1774831563964789, 1811871645565305⟩
  | 91 => ⟨1700957560766829, 1738409962373489, 1775862363980149, 1813314765586809, 1850767167193469⟩
  | 92 => ⟨1738616122376561, 1776480843989365, 1814345565602169, 1852210287214973, 1890075008827777⟩
  | 93 => ⟨1776687003992437, 1814964045611385, 1853241087230333, 1891518128849281, 1929795170468229⟩
  | 94 => ⟨1815170205614457, 1853859567239549, 1892548928864641, 1931238290489733, 1969927652114825⟩
  | 95 => ⟨1854065727242621, 1893167408873857, 1932269090505093, 1971370772136329, 2010472453767565⟩
  | 96 => ⟨1893373568876929, 1932887570514309, 1972401572151689, 2011915573789069, 2051429575426449⟩
  | 97 => ⟨1933093730517381, 1973020052160905, 2012946373804429, 2052872695447953, 2092799017091477⟩
  | 98 => ⟨1973226212163977, 2013564853813645, 2053903495463313, 2094242137112981, 2134580778762649⟩
  | 99 => ⟨2013771013816717, 2054521975472529, 2095272937128341, 2136023898784153, 2176774860439965⟩
  | 100 => ⟨2054728135475601, 2095891417137557, 2137054698799513, 2178217980461469, 2219381262123425⟩
  | 101 => ⟨2096097577140629, 2137673178808729, 2179248780476829, 2220824382144929, 2262399983813029⟩
  | 102 => ⟨2137879338811801, 2179867260486045, 2221855182160289, 2263843103834533, 2305831025508777⟩
  | 103 => ⟨2180073420489117, 2222473662169505, 2264873903849893, 2307274145530281, 2349674387210669⟩
  | 104 => ⟨2222679822172577, 2265492383859109, 2308304945545641, 2351117507232173, 2393930068918705⟩
  | 105 => ⟨2265698543862181, 2308923425554857, 2352148307247533, 2395373188940209, 2438598070632885⟩
  | 106 => ⟨2309129585557929, 2352766787256749, 2396403988955569, 2440041190654389, 2483678392353209⟩
  | 107 => ⟨2352972947259821, 2397022468964785, 2441071990669749, 2485121512374713, 2529171034079677⟩
  | 108 => ⟨2397228628967857, 2441690470678965, 2486152312390073, 2530614154101181, 2575075995812289⟩
  | 109 => ⟨2441896630682037, 2486770792399289, 2531644954116541, 2576519115833793, 2621393277551045⟩
  | 110 => ⟨2486976952402361, 2532263434125757, 2577549915849153, 2622836397572549, 2668122879295945⟩
  | 111 => ⟨2532469594128829, 2578168395858369, 2623867197587909, 2669565999317449, 2715264801046989⟩
  | 112 => ⟨2578374555861441, 2624485677597125, 2670596799332809, 2716707921068493, 2762819042804177⟩
  | 113 => ⟨2624691837600197, 2671215279342025, 2717738721083853, 2764262162825681, 2810785604567509⟩
  | 114 => ⟨2671421439345097, 2718357201093069, 2765292962841041, 2812228724589013, 2859164486336985⟩
  | 115 => ⟨2718563361096141, 2765911442850257, 2813259524604373, 2860607606358489, 2907955688112605⟩
  | 116 => ⟨2766117602853329, 2813878004613589, 2861638406373849, 2909398808134109, 2957159209894369⟩
  | 117 => ⟨2814084164616661, 2862256886383065, 2910429608149469, 2958602329915873, 3006775051682277⟩
  | 118 => ⟨2862463046386137, 2911048088158685, 2959633129931233, 3008218171703781, 3056803213476329⟩
  | 119 => ⟨2911254248161757, 2960251609940449, 3009248971719141, 3058246333497833, 3107243695276525⟩
  | 120 => ⟨2960457769943521, 3009867451728357, 3059277133513193, 3108686815298029, 3158096497082865⟩
  | 121 => ⟨3010073611731429, 3059895613522409, 3109717615313389, 3159539617104369, 3209361618895349⟩
  | 122 => ⟨3060101773525481, 3110336095322605, 3160570417119729, 3210804738916853, 3261039060713977⟩
  | 123 => ⟨3110542255325677, 3161188897128945, 3211835538932213, 3262482180735481, 3313128822538749⟩
  | 124 => ⟨3161395057132017, 3212454018941429, 3263512980750841, 3314571942560253, 3365630904369665⟩
  | 125 => ⟨3212660178944501, 3264131460760057, 3315602742575613, 3367074024391169, 3418545306206725⟩
  | 126 => ⟨3264337620763129, 3316221222584829, 3368104824406529, 3419988426228229, 3471872028049929⟩
  | _ => defaultCosts

def row2 : ℕ → Costs
  | 0 => ⟨549762105354, 755922632716, 1511844216850, 2267765800984, 3023687385118⟩
  | 1 => ⟨755922632716, 1649284218898, 2542645805080, 3436007391262, 4329368977444⟩
  | 2 => ⟨2319318646804, 3925661122587, 5532003598370, 7138346074153, 8744688549936⟩
  | 3 => ⟨4217723224091, 6408189902882, 8598656581673, 10789123260464, 12979589939255⟩
  | 4 => ⟨6700252004386, 9474842886185, 12249433767984, 15024024649783, 17798615531582⟩
  | 5 => ⟨9766904987689, 13125620072496, 16484335157303, 19843050242110, 23201765326917⟩
  | 6 => ⟨13417682174000, 17360521461815, 21303360749630, 25246200037445, 29189039325260⟩
  | 7 => ⟨17652583563319, 22179547054142, 26706510544965, 31233474035788, 35760437526611⟩
  | 8 => ⟨22471609155646, 27582696849477, 32693784543308, 37804872237139, 42915959930970⟩
  | 9 => ⟨27874758950981, 33569970847820, 39265182744659, 44960394641498, 50655606538337⟩
  | 10 => ⟨33862032949324, 40141369049171, 46420705149018, 52700041248865, 58979377348712⟩
  | 11 => ⟨40433431150675, 47296891453530, 54160351756385, 61023812059240, 67887272362095⟩
  | 12 => ⟨47588953555034, 55036538060897, 62484122566760, 69931707072623, 77379291578486⟩
  | 13 => ⟨55328600162401, 63360308871272, 71392017580143, 79423726289014, 87455434997885⟩
  | 14 => ⟨63652370972776, 72268203884655, 80884036796534, 89499869708413, 98115702620292⟩
  | 15 => ⟨72560265986159, 81760223101046, 90960180215933, 100160137330820, 109360094445707⟩
  | 16 => ⟨82052285202550, 91836366520445, 101620447838340, 111404529156235, 121188610474130⟩
  | 17 => ⟨92128428621949, 102496634142852, 112864839663755, 123233045184658, 133601250705561⟩
  | 18 => ⟨102788696244356, 113741025968267, 124693355692178, 135645685416089, 146598015140000⟩
  | 19 => ⟨114033088069771, 125569541996690, 137105995923609, 148642449850528, 160178903777447⟩
  | 20 => ⟨125861604098194, 137982182228121, 150102760358048, 162223338487975, 174343916617902⟩
  | 21 => ⟨138274244329625, 150978946662560, 163683648995495, 176388351328430, 189093053661365⟩
  | 22 => ⟨151271008764064, 164559835300007, 177848661835950, 191137488371893, 204426314907836⟩
  | 23 => ⟨164851897401511, 178724848140462, 192597798879413, 206470749618364, 220343700357315⟩
  | 24 => ⟨179016910241966, 193473985183925, 207931060125884, 222388135067843, 236845210009802⟩
  | 25 => ⟨193766047285429, 208807246430396, 223848445575363, 238889644720330, 253930843865297⟩
  | 26 => ⟨209099308531900, 224724631879875, 240349955227850, 255975278575825, 271600601923800⟩
  | 27 => ⟨225016693981379, 241226141532362, 257435589083345, 273645036634328, 289854484185311⟩
  | 28 => ⟨241518203633866, 258311775387857, 275105347141848, 291898918895839, 308692490649830⟩
  | 29 => ⟨258603837489361, 275981533446360, 293359229403359, 310736925360358, 328114621317357⟩
  | 30 => ⟨276273595547864, 294235415707871, 312197235867878, 330159056027885, 348120876187892⟩
  | 31 => ⟨294527477809375, 313073422172390, 331619366535405, 350165310898420, 368711255261435⟩
  | 32 => ⟨313365484273894, 332495552839917, 351625621405940, 370755689971963, 389885758537986⟩
  | 33 => ⟨332787614941421, 352501807710452, 372216000479483, 391930193248514, 411644386017545⟩
  | 34 => ⟨352793869811956, 373092186783995, 393390503756034, 413688820728073, 433987137700112⟩
  | 35 => ⟨373384248885499, 394266690060546, 415149131235593, 436031572410640, 456914013585687⟩
  | 36 => ⟨394558752162050, 416025317540105, 437491882918160, 458958448296215, 480425013674270⟩
  | 37 => ⟨416317379641609, 438368069222672, 460418758803735, 482469448384798, 504520137965861⟩
  | 38 => ⟨438660131324176, 461294945108247, 483929758892318, 506564572676389, 529199386460460⟩
  | 39 => ⟨461587007209751, 484805945196830, 508024883183909, 531243821170988, 554462759158067⟩
  | 40 => ⟨485098007298334, 508901069488421, 532704131678508, 556507193868595, 580310256058682⟩
  | 41 => ⟨509193131589925, 533580317983020, 557967504376115, 582354690769210, 606741877162305⟩
  | 42 => ⟨533872380084524, 558843690680627, 583815001276730, 608786311872833, 633757622468936⟩
  | 43 => ⟨559135752782131, 584691187581242, 610246622380353, 635802057179464, 661357491978575⟩
  | 44 => ⟨584983249682746, 611122808684865, 637262367686984, 663401926689103, 689541485691222⟩
  | 45 => ⟨611414870786369, 638138553991496, 664862237196623, 691585920401750, 718309603606877⟩
  | 46 => ⟨638430616093000, 665738423501135, 693046230909270, 720354038317405, 747661845725540⟩
  | 47 => ⟨666030485602639, 693922417213782, 721814348824925, 749706280436068, 777598212047211⟩
  | 48 => ⟨694214479315286, 722690535129437, 751166590943588, 779642646757739, 808118702571890⟩
  | 49 => ⟨722982597230941, 752042777248100, 781102957265259, 810163137282418, 839223317299577⟩
  | 50 => ⟨752334839349604, 781979143569771, 811623447789938, 841267752010105, 870912056230272⟩
  | 51 => ⟨782271205671275, 812499634094450, 842728062517625, 872956490940800, 903184919363975⟩
  | 52 => ⟨812791696195954, 843604248822137, 874416801448320, 905229354074503, 936041906700686⟩
  | 53 => ⟨843896310923641, 875292987752832, 906689664582023, 938086341411214, 969483018240405⟩
  | 54 => ⟨875585049854336, 907565850886535, 939546651918734, 971527452950933, 1003508253983132⟩
  | 55 => ⟨907857912988039, 940422838223246, 972987763458453, 1005552688693660, 1038117613928867⟩
  | 56 => ⟨940714900324750, 973863949762965, 1007012999201180, 1040162048639395, 1073311098077610⟩
  | 57 => ⟨974156011864469, 1007889185505692, 1041622359146915, 1075355532788138, 1109088706429361⟩
  | 58 => ⟨1008181247607196, 1042498545451427, 1076815843295658, 1111133141139889, 1145450438984120⟩
  | 59 => ⟨1042790607552931, 1077692029600170, 1112593451647409, 1147494873694648, 1182396295741887⟩
  | 60 => ⟨1077984091701674, 1113469637951921, 1148955184202168, 1184440730452415, 1219926276702662⟩
  | 61 => ⟨1113761700053425, 1149831370506680, 1185901040959935, 1221970711413190, 1258040381866445⟩
  | 62 => ⟨1150123432608184, 1186777227264447, 1223431021920710, 1260084816576973, 1296738611233236⟩
  | 63 => ⟨1187069289365951, 1224307208225222, 1261545127084493, 1298783045943764, 1336020964803035⟩
  | 64 => ⟨1224599270326726, 1262421313389005, 1300243356451284, 1338065399513563, 1375887442575842⟩
  | 65 => ⟨1262713375490509, 1301119542755796, 1339525710021083, 1377931877286370, 1416338044551657⟩
  | 66 => ⟨1301411604857300, 1340401896325595, 1379392187793890, 1418382479262185, 1457372770730480⟩
  | 67 => ⟨1340693958427099, 1380268374098402, 1419842789769705, 1459417205441008, 1498991621112311⟩
  | 68 => ⟨1380560436199906, 1420718976074217, 1460877515948528, 1501036055822839, 1541194595697150⟩
  | 69 => ⟨1421011038175721, 1461753702253040, 1502496366330359, 1543239030407678, 1583981694484997⟩
  | 70 => ⟨1462045764354544, 1503372552634871, 1544699340915198, 1586026129195525, 1627352917475852⟩
  | 71 => ⟨1503664614736375, 1545575527219710, 1587486439703045, 1629397352186380, 1671308264669715⟩
  | 72 => ⟨1545867589321214, 1588362626007557, 1630857662693900, 1673352699380243, 1715847736066586⟩
  | 73 => ⟨1588654688109061, 1631733848998412, 1674813009887763, 1717892170777114, 1760971331666465⟩
  | 74 => ⟨1632025911099916, 1675689196192275, 1719352481284634, 1763015766376993, 1806679051469352⟩
  | 75 => ⟨1675981258293779, 1720228667589146, 1764476076884513, 1808723486179880, 1852970895475247⟩
  | 76 => ⟨1720520729690650, 1765352263189025, 1810183796687400, 1855015330185775, 1899846863684150⟩
  | 77 => ⟨1765644325290529, 1811059982991912, 1856475640693295, 1901891298394678, 1947306956096061⟩
  | 78 => ⟨1811352045093416, 1857351826997807, 1903351608902198, 1949351390806589, 1995351172710980⟩
  | 79 => ⟨1857643889099311, 1904227795206710, 1950811701314109, 1997395607421508, 2043979513528907⟩
  | 80 => ⟨1904519857308214, 1951687887618621, 1998855917929028, 2046023948239435, 2093191978549842⟩
  | 81 => ⟨1951979949720125, 1999732104233540, 2047484258746955, 2095236413260370, 2142988567773785⟩
  | 82 => ⟨2000024166335044, 2048360445051467, 2096696723767890, 2145033002484313, 2193369281200736⟩
  | 83 => ⟨2048652507152971, 2097572910072402, 2146493312991833, 2195413715911264, 2244334118830695⟩
  | 84 => ⟨2097864972173906, 2147369499296345, 2196874026418784, 2246378553541223, 2295883080663662⟩
  | 85 => ⟨2147661561397849, 2197750212723296, 2247838864048743, 2297927515374190, 2348016166699637⟩
  | 86 => ⟨2198042274824800, 2248715050353255, 2299387825881710, 2350060601410165, 2400733376938620⟩
  | 87 => ⟨2249007112454759, 2300264012186222, 2351520911917685, 2402777811649148, 2454034711380611⟩
  | 88 => ⟨2300556074287726, 2352397098222197, 2404238122156668, 2456079146091139, 2507920170025610⟩
  | 89 => ⟨2352689160323701, 2405114308461180, 2457539456598659, 2509964604736138, 2562389752873617⟩
  | 90 => ⟨2405406370562684, 2458415642903171, 2511424915243658, 2564434187584145, 2617443459924632⟩
  | 91 => ⟨2458707705004675, 2512301101548170, 2565894498091665, 2619487894635160, 2673081291178655⟩
  | 92 => ⟨2512593163649674, 2566770684396177, 2620948205142680, 2675125725889183, 2729303246635686⟩
  | 93 => ⟨2567062746497681, 2621824391447192, 2676586036396703, 2731347681346214, 2786109326295725⟩
  | 94 => ⟨2622116453548696, 2677462222701215, 2732807991853734, 2788153761006253, 2843499530158772⟩
  | 95 => ⟨2677754284802719, 2733684178158246, 2789614071513773, 2845543964869300, 2901473858224827⟩
  | 96 => ⟨2733976240259750, 2790490257818285, 2847004275376820, 2903518292935355, 2960032310493890⟩
  | 97 => ⟨2790782319919789, 2847880461681332, 2904978603442875, 2962076745204418, 3019174886965961⟩
  | 98 => ⟨2848172523782836, 2905854789747387, 2963537055711938, 3021219321676489, 3078901587641040⟩
  | 99 => ⟨2906146851848891, 2964413242016450, 3022679632184009, 3080946022351568, 3139212412519127⟩
  | 100 => ⟨2964705304117954, 3023555818488521, 3082406332859088, 3141256847229655, 3200107361600222⟩
  | 101 => ⟨3023847880590025, 3083282519163600, 3142717157737175, 3202151796310750, 3261586434884325⟩
  | 102 => ⟨3083574581265104, 3143593344041687, 3203612106818270, 3263630869594853, 3323649632371436⟩
  | 103 => ⟨3143885406143191, 3204488293122782, 3265091180102373, 3325694067081964, 3386296954061555⟩
  | 104 => ⟨3204780355224286, 3265967366406885, 3327154377589484, 3388341388772083, 3449528399954682⟩
  | 105 => ⟨3266259428508389, 3328030563893996, 3389801699279603, 3451572834665210, 3513343970050817⟩
  | 106 => ⟨3328322625995500, 3390677885584115, 3453033145172730, 3515388404761345, 3577743664349960⟩
  | 107 => ⟨3390969947685619, 3453909331477242, 3516848715268865, 3579788099060488, 3642727482852111⟩
  | 108 => ⟨3454201393578746, 3517724901573377, 3581248409568008, 3644771917562639, 3708295425557270⟩
  | 109 => ⟨3518016963674881, 3582124595872520, 3646232228070159, 3710339860267798, 3774447492465437⟩
  | 110 => ⟨3582416657974024, 3647108414374671, 3711800170775318, 3776491927175965, 3841183683576612⟩
  | 111 => ⟨3647400476476175, 3712676357079830, 3777952237683485, 3843228118287140, 3908503998890795⟩
  | 112 => ⟨3712968419181334, 3778828423987997, 3844688428794660, 3910548433601323, 3976408438407986⟩
  | 113 => ⟨3779120486089501, 3845564615099172, 3912008744108843, 3978452873118514, 4044897002128185⟩
  | 114 => ⟨3845856677200676, 3912884930413355, 3979913183626034, 4046941436838713, 4113969690051392⟩
  | 115 => ⟨3913176992514859, 3980789369930546, 4048401747346233, 4116014124761920, 4183626502177607⟩
  | 116 => ⟨3981081432032050, 4049277933650745, 4117474435269440, 4185670936888135, 4253867438506830⟩
  | 117 => ⟨4049569995752249, 4118350621573952, 4187131247395655, 4255911873217358, 4324692499039061⟩
  | 118 => ⟨4118642683675456, 4188007433700167, 4257372183724878, 4326736933749589, 4396101683774300⟩
  | 119 => ⟨4188299495801671, 4258248370029390, 4328197244257109, 4398146118484828, 4468094992712547⟩
  | 120 => ⟨4258540432130894, 4329073430561621, 4399606428992348, 4470139427423075, 4540672425853802⟩
  | 121 => ⟨4329365492663125, 4400482615296860, 4471599737930595, 4542716860564330, 4613833983198065⟩
  | 122 => ⟨4400774677398364, 4472475924235107, 4544177171071850, 4615878417908593, 4687579664745336⟩
  | 123 => ⟨4472767986336611, 4545053357376362, 4617338728416113, 4689624099455864, 4761909470495615⟩
  | 124 => ⟨4545345419477866, 4618214914720625, 4691084409963384, 4763953905206143, 4836823400448902⟩
  | 125 => ⟨4618506976822129, 4691960596267896, 4765414215713663, 4838867835159430, 4912321454605197⟩
  | _ => defaultCosts

def row3 : ℕ → Costs
  | 0 => ⟨1855444746261, 2405205803033, 4191928451107, 5978651099181, 7765373747255⟩
  | 1 => ⟨2405205803033, 4466808455203, 6528411107373, 8590013759543, 10651616411713⟩
  | 2 => ⟨5033781231653, 7928634081328, 10823486931003, 13718339780678, 16613192630353⟩
  | 3 => ⟨8375317364784, 12163536781371, 15951756197958, 19739975614545, 23528195031132⟩
  | 4 => ⟨12610220064827, 17291806048326, 21973392031825, 26654978015324, 31336563998823⟩
  | 5 => ⟨17738489331782, 23313441882193, 28888394432604, 34463346983015, 40038299533426⟩
  | 6 => ⟨23760125165649, 30228444282972, 36696763400295, 43165082517618, 49633401634941⟩
  | 7 => ⟨30675127566428, 38036813250663, 45398498934898, 52760184619133, 60121870303368⟩
  | 8 => ⟨38483496534119, 46738548785266, 54993601036413, 63248653287560, 71503705538707⟩
  | 9 => ⟨47185232068722, 56333650886781, 65482069704840, 74630488522899, 83778907340958⟩
  | 10 => ⟨56780334170237, 66822119555208, 76863904940179, 86905690325150, 96947475710121⟩
  | 11 => ⟨67268802838664, 78203954790547, 89139106742430, 100074258694313, 111009410646196⟩
  | 12 => ⟨78650638074003, 90479156592798, 102307675111593, 114136193630388, 125964712149183⟩
  | 13 => ⟨90925839876254, 103647724961961, 116369610047668, 129091495133375, 141813380219082⟩
  | 14 => ⟨104094408245417, 117709659898036, 131324911550655, 144940163203274, 158555414855893⟩
  | 15 => ⟨118156343181492, 132664961401023, 147173579620554, 161682197840085, 176190816059616⟩
  | 16 => ⟨133111644684479, 148513629470922, 163915614257365, 179317599043808, 194719583830251⟩
  | 17 => ⟨148960312754378, 165255664107733, 181551015461088, 197846366814443, 214141718167798⟩
  | 18 => ⟨165702347391189, 182891065311456, 200079783231723, 217268501151990, 234457219072257⟩
  | 19 => ⟨183337748594912, 201419833082091, 219501917569270, 237584002056449, 255666086543628⟩
  | 20 => ⟨201866516365547, 220841967419638, 239817418473729, 258792869527820, 277768320581911⟩
  | 21 => ⟨221288650703094, 241157468324097, 261026285945100, 280895103566103, 300763921187106⟩
  | 22 => ⟨241604151607553, 262366335795468, 283128519983383, 303890704171298, 324652888359213⟩
  | 23 => ⟨262813019078924, 284468569833751, 306124120588578, 327779671343405, 349435222098232⟩
  | 24 => ⟨284915253117207, 307464170438946, 330013087760685, 352562005082424, 375110922404163⟩
  | 25 => ⟨307910853722402, 331353137611053, 354795421499704, 378237705388355, 401679989277006⟩
  | 26 => ⟨331799820894509, 356135471350072, 380471121805635, 404806772261198, 429142422716761⟩
  | 27 => ⟨356582154633528, 381811171656003, 407040188678478, 432269205700953, 457498222723428⟩
  | 28 => ⟨382257854939459, 408380238528846, 434502622118233, 460625005707620, 486747389297007⟩
  | 29 => ⟨408826921812302, 435842671968601, 462858422124900, 489874172281199, 516889922437498⟩
  | 30 => ⟨436289355252057, 464198471975268, 492107588698479, 520016705421690, 547925822144901⟩
  | 31 => ⟨464645155258724, 493447638548847, 522250121838970, 551052605129093, 579855088419216⟩
  | 32 => ⟨493894321832303, 523590171689338, 553286021546373, 582981871403408, 612677721260443⟩
  | 33 => ⟨524036854972794, 554626071396741, 585215287820688, 615804504244635, 646393720668582⟩
  | 34 => ⟨555072754680197, 586555337671056, 618037920661915, 649520503652774, 681003086643633⟩
  | 35 => ⟨587002020954512, 619377970512283, 651753920070054, 684129869627825, 716505819185596⟩
  | 36 => ⟨619824653795739, 653093969920422, 686363286045105, 719632602169788, 752901918294471⟩
  | 37 => ⟨653540653203878, 687703335895473, 721866018587068, 756028701278663, 790191383970258⟩
  | 38 => ⟨688150019178929, 723206068437436, 758262117695943, 793318166954450, 828374216212957⟩
  | 39 => ⟨723652751720892, 759602167546311, 795551583371730, 831500999197149, 867450415022568⟩
  | 40 => ⟨760048850829767, 796891633222098, 833734415614429, 870577198006760, 907419980399091⟩
  | 41 => ⟨797338316505554, 835074465464797, 872810614424040, 910546763383283, 948282912342526⟩
  | 42 => ⟨835521148748253, 874150664274408, 912780179800563, 951409695326718, 990039210852873⟩
  | 43 => ⟨874597347557864, 914120229650931, 953643111743998, 993165993837065, 1032688875930132⟩
  | 44 => ⟨914566912934387, 954983161594366, 995399410254345, 1035815658914324, 1076231907574303⟩
  | 45 => ⟨955429844877822, 996739460104713, 1038049075331604, 1079358690558495, 1120668305785386⟩
  | 46 => ⟨997186143388169, 1039389125181972, 1081592106975775, 1123795088769578, 1165998070563381⟩
  | 47 => ⟨1039835808465428, 1082932156826143, 1126028505186858, 1169124853547573, 1212221201908288⟩
  | 48 => ⟨1083378840109599, 1127368555037226, 1171358269964853, 1215347984892480, 1259337699820107⟩
  | 49 => ⟨1127815238320682, 1172698319815221, 1217581401309760, 1262464482804299, 1307347564298838⟩
  | 50 => ⟨1173145003098677, 1218921451160128, 1264697899221579, 1310474347283030, 1356250795344481⟩
  | 51 => ⟨1219368134443584, 1266037949071947, 1312707763700310, 1359377578328673, 1406047392957036⟩
  | 52 => ⟨1266484632355403, 1314047813550678, 1361610994745953, 1409174175941228, 1456737357136503⟩
  | 53 => ⟨1314494496834134, 1362951044596321, 1411407592358508, 1459864140120695, 1508320687882882⟩
  | 54 => ⟨1363397727879777, 1412747642208876, 1462097556537975, 1511447470867074, 1560797385196173⟩
  | 55 => ⟨1413194325492332, 1463437606388343, 1513680887284354, 1563924168180365, 1614167449076376⟩
  | 56 => ⟨1463884289671799, 1515020937134722, 1566157584597645, 1617294232060568, 1668430879523491⟩
  | 57 => ⟨1515467620418178, 1567497634448013, 1619527648477848, 1671557662507683, 1723587676537518⟩
  | 58 => ⟨1567944317731469, 1620867698328216, 1673791078924963, 1726714459521710, 1779637840118457⟩
  | 59 => ⟨1621314381611672, 1675131128775331, 1728947875938990, 1782764623102649, 1836581370266308⟩
  | 60 => ⟨1675577812058787, 1730287925789358, 1784998039519929, 1839708153250500, 1894418266981071⟩
  | 61 => ⟨1730734609072814, 1786338089370297, 1841941569667780, 1897545049965263, 1953148530262746⟩
  | 62 => ⟨1786784772653753, 1843281619518148, 1899778466382543, 1956275313246938, 2012772160111333⟩
  | 63 => ⟨1843728302801604, 1901118516232911, 1958508729664218, 2015898943095525, 2073289156526832⟩
  | 64 => ⟨1901565199516367, 1959848779514586, 2018132359512805, 2076415939511024, 2134699519509243⟩
  | 65 => ⟨1960295462798042, 2019472409363173, 2078649355928304, 2137826302493435, 2197003249058566⟩
  | 66 => ⟨2019919092646629, 2079989405778672, 2140059718910715, 2200130032042758, 2260200345174801⟩
  | 67 => ⟨2080436089062128, 2141399768761083, 2202363448460038, 2263327128158993, 2324290807857948⟩
  | 68 => ⟨2141846452044539, 2203703498310406, 2265560544576273, 2327417590842140, 2389274637108007⟩
  | 69 => ⟨2204150181593862, 2266900594426641, 2329651007259420, 2392401420092199, 2455151832924978⟩
  | 70 => ⟨2267347277710097, 2330991057109788, 2394634836509479, 2458278615909170, 2521922395308861⟩
  | 71 => ⟨2331437740393244, 2395974886359847, 2460512032326450, 2525049178293053, 2589586324259656⟩
  | 72 => ⟨2396421569643303, 2461852082176818, 2527282594710333, 2592713107243848, 2658143619777363⟩
  | 73 => ⟨2462298765460274, 2528622644560701, 2594946523661128, 2661270402761555, 2727594281861982⟩
  | 74 => ⟨2529069327844157, 2596286573511496, 2663503819178835, 2730721064846174, 2797938310513513⟩
  | 75 => ⟨2596733256794952, 2664843869029203, 2732954481263454, 2801065093497705, 2869175705731956⟩
  | 76 => ⟨2665290552312659, 2734294531113822, 2803298509914985, 2872302488716148, 2941306467517311⟩
  | 77 => ⟨2734741214397278, 2804638559765353, 2874535905133428, 2944433250501503, 3014330595869578⟩
  | 78 => ⟨2805085243048809, 2875875954983796, 2946666666918783, 3017457378853770, 3088248090788757⟩
  | 79 => ⟨2876322638267252, 2948006716769151, 3019690795271050, 3091374873772949, 3163058952274848⟩
  | 80 => ⟨2948453400052607, 3021030845121418, 3093608290190229, 3166185735259040, 3238763180327851⟩
  | 81 => ⟨3021477528404874, 3094948340040597, 3168419151676320, 3241889963312043, 3315360774947766⟩
  | 82 => ⟨3095395023324053, 3169759201526688, 3244123379729323, 3318487557931958, 3392851736134593⟩
  | 83 => ⟨3170205884810144, 3245463429579691, 3320720974349238, 3395978519118785, 3471236063888332⟩
  | 84 => ⟨3245910112863147, 3322061024199606, 3398211935536065, 3474362846872524, 3550513758208983⟩
  | 85 => ⟨3322507707483062, 3399551985386433, 3476596263289804, 3553640541193175, 3630684819096546⟩
  | 86 => ⟨3399998668669889, 3477936313140172, 3555873957610455, 3633811602080738, 3711749246551021⟩
  | 87 => ⟨3478382996423628, 3557214007460823, 3636045018498018, 3714876029535213, 3793707040572408⟩
  | 88 => ⟨3557660690744279, 3637385068348386, 3717109445952493, 3796833823556600, 3876558201160707⟩
  | 89 => ⟨3637831751631842, 3718449495802861, 3799067239973880, 3879684984144899, 3960302728315918⟩
  | 90 => ⟨3718896179086317, 3800407289824248, 3881918400562179, 3963429511300110, 4044940622038041⟩
  | 91 => ⟨3800853973107704, 3883258450412547, 3965662927717390, 4048067405022233, 4130471882327076⟩
  | 92 => ⟨3883705133696003, 3967002977567758, 4050300821439513, 4133598665311268, 4216896509183023⟩
  | 93 => ⟨3967449660851214, 4051640871289881, 4135832081728548, 4220023292167215, 4304214502605882⟩
  | 94 => ⟨4052087554573337, 4137172131578916, 4222256708584495, 4307341285590074, 4392425862595653⟩
  | 95 => ⟨4137618814862372, 4223596758434863, 4309574702007354, 4395552645579845, 4481530589152336⟩
  | 96 => ⟨4224043441718319, 4310914751857722, 4397786061997125, 4484657372136528, 4571528682275931⟩
  | 97 => ⟨4311361435141178, 4399126111847493, 4486890788553808, 4574655465260123, 4662420141966438⟩
  | 98 => ⟨4399572795130949, 4488230838404176, 4576888881677403, 4665546924950630, 4754204968223857⟩
  | 99 => ⟨4488677521687632, 4578228931527771, 4667780341367910, 4757331751208049, 4846883161048188⟩
  | 100 => ⟨4578675614811227, 4669120391218278, 4759565167625329, 4850009944032380, 4940454720439431⟩
  | 101 => ⟨4669567074501734, 4760905217475697, 4852243360449660, 4943581503423623, 5034919646397586⟩
  | 102 => ⟨4761351900759153, 4853583410300028, 4945814919840903, 5038046429381778, 5130277938922653⟩
  | 103 => ⟨4854030093583484, 4947154969691271, 5040279845799058, 5133404721906845, 5226529598014632⟩
  | 104 => ⟨4947601652974727, 5041619895649426, 5135638138324125, 5229656380998824, 5323674623673523⟩
  | 105 => ⟨5042066578932882, 5136978188174493, 5231889797416104, 5326801406657715, 5421713015899326⟩
  | 106 => ⟨5137424871457949, 5233229847266472, 5329034823074995, 5424839798883518, 5520644774692041⟩
  | 107 => ⟨5233676530549928, 5330374872925363, 5427073215300798, 5523771557676233, 5620469900051668⟩
  | 108 => ⟨5330821556208819, 5428413265151166, 5526004974093513, 5623596683035860, 5721188391978207⟩
  | 109 => ⟨5428859948434622, 5527345023943881, 5625830099453140, 5724315174962399, 5822800250471658⟩
  | 110 => ⟨5527791707227337, 5627170149303508, 5726548591379679, 5825927033455850, 5925305475532021⟩
  | 111 => ⟨5627616832586964, 5727888641230047, 5828160449873130, 5928432258516213, 6028704067159296⟩
  | 112 => ⟨5728335324513503, 5829500499723498, 5930665674933493, 6031830850143488, 6132996025353483⟩
  | 113 => ⟨5829947183006954, 5932005724783861, 6034064266560768, 6136122808337675, 6238181350114582⟩
  | 114 => ⟨5932452408067317, 6035404316411136, 6138356224754955, 6241308133098774, 6344260041442593⟩
  | 115 => ⟨6035850999694592, 6139696274605323, 6243541549516054, 6347386824426785, 6451232099337516⟩
  | 116 => ⟨6140142957888779, 6244881599366422, 6349620240844065, 6454358882321708, 6559097523799351⟩
  | 117 => ⟨6245328282649878, 6350960290694433, 6456592298738988, 6562224306783543, 6667856314828098⟩
  | 118 => ⟨6351406973977889, 6457932348589356, 6564457723200823, 6670983097812290, 6777508472423757⟩
  | 119 => ⟨6458379031872812, 6565797773051191, 6673216514229570, 6780635255407949, 6888053996586328⟩
  | 120 => ⟨6566244456334647, 6674556564079938, 6782868671825229, 6891180779570520, 6999492887315811⟩
  | 121 => ⟨6675003247363394, 6784208721675597, 6893414195987800, 7002619670300003, 7111825144612206⟩
  | 122 => ⟨6784655404959053, 6894754245838168, 7004853086717283, 7114951927596398, 7225050768475513⟩
  | 123 => ⟨6895200929121624, 7006193136567651, 7117185344013678, 7228177551459705, 7339169758905732⟩
  | 124 => ⟨7006639819851107, 7118525393864046, 7230410967876985, 7342296541889924, 7454182115902863⟩
  | _ => defaultCosts

def row4 : ℕ → Costs
  | 0 => ⟨4398088454180, 5428890042410, 8658733760568, 11888577478726, 15118421196884⟩
  | 1 => ⟨5428890042410, 9071053766712, 12713217491014, 16355381215316, 19997544939618⟩
  | 2 => ⟨9191375372346, 13683980959817, 18176586547288, 22669192134759, 27161797722230⟩
  | 3 => ⟨14285285425225, 19980499943512, 25675714461799, 31370928980086, 37066143498373⟩
  | 4 => ⟨20581804408920, 27479627858023, 34377451307126, 41275274756229, 48173098205332⟩
  | 5 => ⟨28080932323431, 36181364703350, 44281797083269, 52382229463188, 60482661843107⟩
  | 6 => ⟨36782669168758, 46085710479493, 55388751790228, 64691793100963, 73994834411698⟩
  | 7 => ⟨46687014944901, 57192665186452, 67698315428003, 78203965669554, 88709615911105⟩
  | 8 => ⟨57793969651860, 69502228824227, 81210487996594, 92918747168961, 104627006341328⟩
  | 9 => ⟨70103533289635, 83014401392818, 95925269496001, 108836137599184, 121747005702367⟩
  | 10 => ⟨83615705858226, 97729182892225, 111842659926224, 125956136960223, 140069613994222⟩
  | 11 => ⟨98330487357633, 113646573322448, 128962659287263, 144278745252078, 159594831216893⟩
  | 12 => ⟨114247877787856, 130766572683487, 147285267579118, 163803962474749, 180322657370380⟩
  | 13 => ⟨131367877148895, 149089180975342, 166810484801789, 184531788628236, 202253092454683⟩
  | 14 => ⟨149690485440750, 168614398198013, 187538310955276, 206462223712539, 225386136469802⟩
  | 15 => ⟨169215702663421, 189342224351500, 209468746039579, 229595267727658, 249721789415737⟩
  | 16 => ⟨189943528816908, 211272659435803, 232601790054698, 253930920673593, 275260051292488⟩
  | 17 => ⟨211873963901211, 234405703450922, 256937443000633, 279469182550344, 302000922100055⟩
  | 18 => ⟨235007007916330, 258741356396857, 282475704877384, 306210053357911, 329944401838438⟩
  | 19 => ⟨259342660862265, 284279618273608, 309216575684951, 334153533096294, 359090490507637⟩
  | 20 => ⟨284880922739016, 311020489081175, 337160055423334, 363299621765493, 389439188107652⟩
  | 21 => ⟨311621793546583, 338963968819558, 366306144092533, 393648319365508, 420990494638483⟩
  | 22 => ⟨339565273284966, 368110057488757, 396654841692548, 425199625896339, 453744410100130⟩
  | 23 => ⟨368711361954165, 398458755088772, 428206148223379, 457953541357986, 487700934492593⟩
  | 24 => ⟨399060059554180, 430010061619603, 460960063685026, 491910065750449, 522860067815872⟩
  | 25 => ⟨430611366085011, 462763977081250, 494916588077489, 527069199073728, 559221810069967⟩
  | 26 => ⟨463365281546658, 496720501473713, 530075721400768, 563430941327823, 596786161254878⟩
  | 27 => ⟨497321805939121, 531879634796992, 566437463654863, 600995292512734, 635553121370605⟩
  | 28 => ⟨532480939262400, 568241377051087, 604001814839774, 639762252628461, 675522690417148⟩
  | 29 => ⟨568842681516495, 605805728235998, 642768774955501, 679731821675004, 716694868394507⟩
  | 30 => ⟨606407032701406, 644572688351725, 682738344002044, 720903999652363, 759069655302682⟩
  | 31 => ⟨645173992817133, 684542257398268, 723910521979403, 763278786560538, 802647051141673⟩
  | 32 => ⟨685143561863676, 725714435375627, 766285308887578, 806856182399529, 847427055911480⟩
  | 33 => ⟨726315739841035, 768089222283802, 809862704726569, 851636187169336, 893409669612103⟩
  | 34 => ⟨768690526749210, 811666618122793, 854642709496376, 897618800869959, 940594892243542⟩
  | 35 => ⟨812267922588201, 856446622892600, 900625323196999, 944804023501398, 988982723805797⟩
  | 36 => ⟨857047927358008, 902429236593223, 947810545828438, 993191855063653, 1038573164298868⟩
  | 37 => ⟨903030541058631, 949614459224662, 996198377390693, 1042782295556724, 1089366213722755⟩
  | 38 => ⟨950215763690070, 998002290786917, 1045788817883764, 1093575344980611, 1141361872077458⟩
  | 39 => ⟨998603595252325, 1047592731279988, 1096581867307651, 1145571003335314, 1194560139362977⟩
  | 40 => ⟨1048194035745396, 1098385780703875, 1148577525662354, 1198769270620833, 1248961015579312⟩
  | 41 => ⟨1098987085169283, 1150381439058578, 1201775792947873, 1253170146837168, 1304564500726463⟩
  | 42 => ⟨1150982743523986, 1203579706344097, 1256176669164208, 1308773631984319, 1361370594804430⟩
  | 43 => ⟨1204181010809505, 1257980582560432, 1311780154311359, 1365579726062286, 1419379297813213⟩
  | 44 => ⟨1258581887025840, 1313584067707583, 1368586248389326, 1423588429071069, 1478590609752812⟩
  | 45 => ⟨1314185372172991, 1370390161785550, 1426594951398109, 1482799741010668, 1539004530623227⟩
  | 46 => ⟨1370991466250958, 1428398864794333, 1485806263337708, 1543213661881083, 1600621060424458⟩
  | 47 => ⟨1429000169259741, 1487610176733932, 1546220184208123, 1604830191682314, 1663440199156505⟩
  | 48 => ⟨1488211481199340, 1548024097604347, 1607836714009354, 1667649330414361, 1727461946819368⟩
  | 49 => ⟨1548625402069755, 1609640627405578, 1670655852741401, 1731671078077224, 1792686303413047⟩
  | 50 => ⟨1610241931870986, 1672459766137625, 1734677600404264, 1796895434670903, 1859113268937542⟩
  | 51 => ⟨1673061070603033, 1736481513800488, 1799901956997943, 1863322400195398, 1926742843392853⟩
  | 52 => ⟨1737082818265896, 1801705870394167, 1866328922522438, 1930951974650709, 1995575026778980⟩
  | 53 => ⟨1802307174859575, 1868132835918662, 1933958496977749, 1999784158036836, 2065609819095923⟩
  | 54 => ⟨1868734140384070, 1935762410373973, 2002790680363876, 2069818950353779, 2136847220343682⟩
  | 55 => ⟨1936363714839381, 2004594593760100, 2072825472680819, 2141056351601538, 2209287230522257⟩
  | 56 => ⟨2005195898225508, 2074629386077043, 2144062873928578, 2213496361780113, 2282929849631648⟩
  | 57 => ⟨2075230690542451, 2145866787324802, 2216502884107153, 2287138980889504, 2357775077671855⟩
  | 58 => ⟨2146468091790210, 2218306797503377, 2290145503216544, 2361984208929711, 2433822914642878⟩
  | 59 => ⟨2218908101968785, 2291949416612768, 2364990731256751, 2438032045900734, 2511073360544717⟩
  | 60 => ⟨2292550721078176, 2366794644652975, 2441038568227774, 2515282491802573, 2589526415377372⟩
  | 61 => ⟨2367395949118383, 2442842481623998, 2518289014129613, 2593735546635228, 2669182079140843⟩
  | 62 => ⟨2443443786089406, 2520092927525837, 2596742068962268, 2673391210398699, 2750040351835130⟩
  | 63 => ⟨2520694231991245, 2598545982358492, 2676397732725739, 2754249483092986, 2832101233460233⟩
  | 64 => ⟨2599147286823900, 2678201646121963, 2757256005420026, 2836310364718089, 2915364724016152⟩
  | 65 => ⟨2678802950587371, 2759059918816250, 2839316887045129, 2919573855274008, 2999830823502887⟩
  | 66 => ⟨2759661223281658, 2841120800441353, 2922580377601048, 3004039954760743, 3085499531920438⟩
  | 67 => ⟨2841722104906761, 2924384290997272, 3007046477087783, 3089708663178294, 3172370849268805⟩
  | 68 => ⟨2924985595462680, 3008850390484007, 3092715185505334, 3176579980526661, 3260444775547988⟩
  | 69 => ⟨3009451694949415, 3094519098901558, 3179586502853701, 3264653906805844, 3349721310757987⟩
  | 70 => ⟨3095120403366966, 3181390416249925, 3267660429132884, 3353930442015843, 3440200454898802⟩
  | 71 => ⟨3181991720715333, 3269464342529108, 3356936964342883, 3444409586156658, 3531882207970433⟩
  | 72 => ⟨3270065646994516, 3358740877739107, 3447416108483698, 3536091339228289, 3624766569972880⟩
  | 73 => ⟨3359342182204515, 3449220021879922, 3539097861555329, 3628975701230736, 3718853540906143⟩
  | 74 => ⟨3449821326345330, 3540901774951553, 3631982223557776, 3723062672163999, 3814143120770222⟩
  | 75 => ⟨3541503079416961, 3633786136954000, 3726069194491039, 3818352252028078, 3910635309565117⟩
  | 76 => ⟨3634387441419408, 3727873107887263, 3821358774355118, 3914844440822973, 4008330107290828⟩
  | 77 => ⟨3728474412352671, 3823162687751342, 3917850963150013, 4012539238548684, 4107227513947355⟩
  | 78 => ⟨3823763992216750, 3919654876546237, 4015545760875724, 4111436645205211, 4207327529534698⟩
  | 79 => ⟨3920256181011645, 4017349674271948, 4114443167532251, 4211536660792554, 4308630154052857⟩
  | 80 => ⟨4017950978737356, 4116247080928475, 4214543183119594, 4312839285310713, 4411135387501832⟩
  | 81 => ⟨4116848385393883, 4216347096515818, 4315845807637753, 4415344518759688, 4514843229881623⟩
  | 82 => ⟨4216948400981226, 4317649721033977, 4418351041086728, 4519052361139479, 4619753681192230⟩
  | 83 => ⟨4318251025499385, 4420154954482952, 4522058883466519, 4623962812450086, 4725866741433653⟩
  | 84 => ⟨4420756258948360, 4523862796862743, 4626969334777126, 4730075872691509, 4833182410605892⟩
  | 85 => ⟨4524464101328151, 4628773248173350, 4733082395018549, 4837391541863748, 4941700688708947⟩
  | 86 => ⟨4629374552638758, 4734886308414773, 4840398064190788, 4945909819966803, 5051421575742818⟩
  | 87 => ⟨4735487612880181, 4842201977587012, 4948916342293843, 5055630707000674, 5162345071707505⟩
  | 88 => ⟨4842803282052420, 4950720255690067, 5058637229327714, 5166554202965361, 5274471176603008⟩
  | 89 => ⟨4951321560155475, 5060441142723938, 5169560725292401, 5278680307860864, 5387799890429327⟩
  | 90 => ⟨5061042447189346, 5171364638688625, 5281686830187904, 5392009021687183, 5502331213186462⟩
  | 91 => ⟨5171965943154033, 5283490743584128, 5395015544014223, 5506540344444318, 5618065144874413⟩
  | 92 => ⟨5284092048049536, 5396819457410447, 5509546866771358, 5622274276132269, 5735001685493180⟩
  | 93 => ⟨5397420761875855, 5511350780167582, 5625280798459309, 5739210816751036, 5853140835042763⟩
  | 94 => ⟨5511952084632990, 5627084711855533, 5742217339078076, 5857349966300619, 5972482593523162⟩
  | 95 => ⟨5627686016320941, 5744021252474300, 5860356488627659, 5976691724781018, 6093026960934377⟩
  | 96 => ⟨5744622556939708, 5862160402023883, 5979698247108058, 6097236092192233, 6214773937276408⟩
  | 97 => ⟨5862761706489291, 5981502160504282, 6100242614519273, 6218983068534264, 6337723522549255⟩
  | 98 => ⟨5982103464969690, 6102046527915497, 6221989590861304, 6341932653807111, 6461875716752918⟩
  | 99 => ⟨6102647832380905, 6223793504257528, 6344939176134151, 6466084848010774, 6587230519887397⟩
  | 100 => ⟨6224394808722936, 6346743089530375, 6469091370337814, 6591439651145253, 6713787931952692⟩
  | 101 => ⟨6347344393995783, 6470895283734038, 6594446173472293, 6717997063210548, 6841547952948803⟩
  | 102 => ⟨6471496588199446, 6596250086868517, 6721003585537588, 6845757084206659, 6970510582875730⟩
  | 103 => ⟨6596851391333925, 6722807498933812, 6848763606533699, 6974719714133586, 7100675821733473⟩
  | 104 => ⟨6723408803399220, 6850567519929923, 6977726236460626, 7104884952991329, 7232043669522032⟩
  | 105 => ⟨6851168824395331, 6979530149856850, 7107891475318369, 7236252800779888, 7364614126241407⟩
  | 106 => ⟨6980131454322258, 7109695388714593, 7239259323106928, 7368823257499263, 7498387191891598⟩
  | 107 => ⟨7110296693180001, 7241063236503152, 7371829779826303, 7502596323149454, 7633362866472605⟩
  | 108 => ⟨7241664540968560, 7373633693222527, 7505602845476494, 7637571997730461, 7769541149984428⟩
  | 109 => ⟨7374234997687935, 7507406758872718, 7640578520057501, 7773750281242284, 7906922042427067⟩
  | 110 => ⟨7508008063338126, 7642382433453725, 7776756803569324, 7911131173684923, 8045505543800522⟩
  | 111 => ⟨7642983737919133, 7778560716965548, 7914137696011963, 8049714675058378, 8185291654104793⟩
  | 112 => ⟨7779162021430956, 7915941609408187, 8052721197385418, 8189500785362649, 8326280373339880⟩
  | 113 => ⟨7916542913873595, 8054525110781642, 8192507307689689, 8330489504597736, 8468471701505783⟩
  | 114 => ⟨8055126415247050, 8194311221085913, 8333496026924776, 8472680832763639, 8611865638602502⟩
  | 115 => ⟨8194912525551321, 8335299940321000, 8475687355090679, 8616074769860358, 8756462184630037⟩
  | 116 => ⟨8335901244786408, 8477491268486903, 8619081292187398, 8760671315887893, 8902261339588388⟩
  | 117 => ⟨8478092572952311, 8620885205583622, 8763677838214933, 8906470470846244, 9049263103477555⟩
  | 118 => ⟨8621486510049030, 8765481751611157, 8909476993173284, 9053472234735411, 9197467476297538⟩
  | 119 => ⟨8766083056076565, 8911280906569508, 9056478757062451, 9201676607555394, 9346874458048337⟩
  | 120 => ⟨8911882211034916, 9058282670458675, 9204683129882434, 9351083589306193, 9497484048729952⟩
  | 121 => ⟨9058883974924083, 9206487043278658, 9354090111633233, 9501693179987808, 9649296248342383⟩
  | 122 => ⟨9207088347744066, 9355894025029457, 9504699702314848, 9653505379600239, 9802311056885630⟩
  | 123 => ⟨9356495329494865, 9506503615711072, 9656511901927279, 9806520188143486, 9956528474359693⟩
  | _ => defaultCosts

def row5 : ℕ → Costs
  | 0 => ⟨8590013235255, 10239295356991, 15324580151377, 20409864945763, 25495149740149⟩
  | 1 => ⟨10239295356991, 15874340159569, 21509384962147, 27144429764725, 32779474567303⟩
  | 2 => ⟨15101343432787, 21500944121958, 27900544811129, 34300145500300, 40699746189471⟩
  | 3 => ⟨22256869769318, 30168321753209, 38079773737100, 45991225720991, 53902677704882⟩
  | 4 => ⟨30924247400569, 40347550679180, 49770853957791, 59194157236402, 68617460515013⟩
  | 5 => ⟨41103476326540, 52038630899871, 62973785473202, 73908940046533, 84844094619864⟩
  | 6 => ⟨52794556547231, 65241562415282, 77688568283333, 90135574151384, 102582580019435⟩
  | 7 => ⟨65997488062642, 79956345225413, 93915202388184, 107874059550955, 121832916713726⟩
  | 8 => ⟨80712270872773, 96182979330264, 111653687787755, 127124396245246, 142595104702737⟩
  | 9 => ⟨96938904977624, 113921464729835, 130904024482046, 147886584234257, 164869143986468⟩
  | 10 => ⟨114677390377195, 133171801424126, 151666212471057, 170160623517988, 188655034564919⟩
  | 11 => ⟨133927727071486, 153933989413137, 173940251754788, 193946514096439, 213952776438090⟩
  | 12 => ⟨154689915060497, 176208028696868, 197726142333239, 219244255969610, 240762369605981⟩
  | 13 => ⟨176963954344228, 199993919275319, 223023884206410, 246053849137501, 269083814068592⟩
  | 14 => ⟨200749844922679, 225291661148490, 249833477374301, 274375293600112, 298917109825923⟩
  | 15 => ⟨226047586795850, 252101254316381, 278154921836912, 304208589357443, 330262256877974⟩
  | 16 => ⟨252857179963741, 280422698778992, 307988217594243, 335553736409494, 363119255224745⟩
  | 17 => ⟨281178624426352, 310255994536323, 339333364646294, 368410734756265, 397488104866236⟩
  | 18 => ⟨311011920183683, 341601141588374, 372190362993065, 402779584397756, 433368805802447⟩
  | 19 => ⟨342357067235734, 374458139935145, 406559212634556, 438660285333967, 470761358033378⟩
  | 20 => ⟨375214065582505, 408826989576636, 442439913570767, 476052837564898, 509665761559029⟩
  | 21 => ⟨409582915223996, 444707690512847, 479832465801698, 514957241090549, 550082016379400⟩
  | 22 => ⟨445463616160207, 482100242743778, 518736869327349, 555373495910920, 592010122494491⟩
  | 23 => ⟨482856168391138, 521004646269429, 559153124147720, 597301602026011, 635450079904302⟩
  | 24 => ⟨521760571916789, 561420901089800, 601081230262811, 640741559435822, 680401888608833⟩
  | 25 => ⟨562176826737160, 603349007204891, 644521187672622, 685693368140353, 726865548608084⟩
  | 26 => ⟨604104932852251, 646788964614702, 689472996377153, 732157028139604, 774841059902055⟩
  | 27 => ⟨647544890262062, 691740773319233, 735936656376404, 780132539433575, 824328422490746⟩
  | 28 => ⟨692496698966593, 738204433318484, 783912167670375, 829619902022266, 875327636374157⟩
  | 29 => ⟨738960358965844, 786179944612455, 833399530259066, 880619115905677, 927838701552288⟩
  | 30 => ⟨786935870259815, 835667307201146, 884398744142477, 933130181083808, 981861618025139⟩
  | 31 => ⟨836423232848506, 886666521084557, 936909809320608, 987153097556659, 1037396385792710⟩
  | 32 => ⟨887422446731917, 939177586262688, 990932725793459, 1042687865324230, 1094443004855001⟩
  | 33 => ⟨939933511910048, 993200502735539, 1046467493561030, 1099734484386521, 1153001475212012⟩
  | 34 => ⟨993956428382899, 1048735270503110, 1103514112623321, 1158292954743532, 1213071796863743⟩
  | 35 => ⟨1049491196150470, 1105781889565401, 1162072582980332, 1218363276395263, 1274653969810194⟩
  | 36 => ⟨1106537815212761, 1164340359922412, 1222142904632063, 1279945449341714, 1337747994051365⟩
  | 37 => ⟨1165096285569772, 1224410681574143, 1283725077578514, 1343039473582885, 1402353869587256⟩
  | 38 => ⟨1225166607221503, 1285992854520594, 1346819101819685, 1407645349118776, 1468471596417867⟩
  | 39 => ⟨1286748780167954, 1349086878761765, 1411424977355576, 1473763075949387, 1536101174543198⟩
  | 40 => ⟨1349842804409125, 1413692754297656, 1477542704186187, 1541392654074718, 1605242603963249⟩
  | 41 => ⟨1414448679945016, 1479810481128267, 1545172282311518, 1610534083494769, 1675895884678020⟩
  | 42 => ⟨1480566406775627, 1547440059253598, 1614313711731569, 1681187364209540, 1748061016687511⟩
  | 43 => ⟨1548195984900958, 1616581488673649, 1684966992446340, 1753352496219031, 1821737999991722⟩
  | 44 => ⟨1617337414321009, 1687234769388420, 1757132124455831, 1827029479523242, 1896926834590653⟩
  | 45 => ⟨1687990695035780, 1759399901397911, 1830809107760042, 1902218314122173, 1973627520484304⟩
  | 46 => ⟨1760155827045271, 1833076884702122, 1905997942358973, 1978919000015824, 2051840057672675⟩
  | 47 => ⟨1833832810349482, 1908265719301053, 1982698628252624, 2057131537204195, 2131564446155766⟩
  | 48 => ⟨1909021644948413, 1984966405194704, 2060911165440995, 2136855925687286, 2212800685933577⟩
  | 49 => ⟨1985722330842064, 2063178942383075, 2140635553924086, 2218092165465097, 2295548777006108⟩
  | 50 => ⟨2063934868030435, 2142903330866166, 2221871793701897, 2300840256537628, 2379808719373359⟩
  | 51 => ⟨2143659256513526, 2224139570643977, 2304619884774428, 2385100198904879, 2465580513035330⟩
  | 52 => ⟨2224895496291337, 2306887661716508, 2388879827141679, 2470871992566850, 2552864157992021⟩
  | 53 => ⟨2307643587363868, 2391147604083759, 2474651620803650, 2558155637523541, 2641659654243432⟩
  | 54 => ⟨2391903529731119, 2476919397745730, 2561935265760341, 2646951133774952, 2731967001789563⟩
  | 55 => ⟨2477675323393090, 2564203042702421, 2650730762011752, 2737258481321083, 2823786200630414⟩
  | 56 => ⟨2564958968349781, 2652998538953832, 2741038109557883, 2829077680161934, 2917117250765985⟩
  | 57 => ⟨2653754464601192, 2743305886499963, 2832857308398734, 2922408730297505, 3011960152196276⟩
  | 58 => ⟨2744061812147323, 2835125085340814, 2926188358534305, 3017251631727796, 3108314904921287⟩
  | 59 => ⟨2835881010988174, 2928456135476385, 3021031259964596, 3113606384452807, 3206181508941018⟩
  | 60 => ⟨2929212061123745, 3023299036906676, 3117386012689607, 3211472988472538, 3305559964255469⟩
  | 61 => ⟨3024054962554036, 3119653789631687, 3215252616709338, 3310851443786989, 3406450270864640⟩
  | 62 => ⟨3120409715279047, 3217520393651418, 3314631072023789, 3411741750396160, 3508852428768531⟩
  | 63 => ⟨3218276319298778, 3316898848965869, 3415521378632960, 3514143908300051, 3612766437967142⟩
  | 64 => ⟨3317654774613229, 3417789155575040, 3517923536536851, 3618057917498662, 3718192298460473⟩
  | 65 => ⟨3418545081222400, 3520191313478931, 3621837545735462, 3723483777991993, 3825130010248524⟩
  | 66 => ⟨3520947239126291, 3624105322677542, 3727263406228793, 3830421489780044, 3933579573331295⟩
  | 67 => ⟨3624861248324902, 3729531183170873, 3834201118016844, 3938871052862815, 4043540987708786⟩
  | 68 => ⟨3730287108818233, 3836468894958924, 3942650681099615, 4048832467240306, 4155014253380997⟩
  | 69 => ⟨3837224820606284, 3944918458041695, 4052612095477106, 4160305732912517, 4267999370347928⟩
  | 70 => ⟨3945674383689055, 4054879872419186, 4164085361149317, 4273290849879448, 4382496338609579⟩
  | 71 => ⟨4055635798066546, 4166353138091397, 4277070478116248, 4387787818141099, 4498505158165950⟩
  | 72 => ⟨4167109063738757, 4279338255058328, 4391567446377899, 4503796637697470, 4616025829017041⟩
  | 73 => ⟨4280094180705688, 4393835223319979, 4507576265934270, 4621317308548561, 4735058351162852⟩
  | 74 => ⟨4394591148967339, 4509844042876350, 4625096936785361, 4740349830694372, 4855602724603383⟩
  | 75 => ⟨4510599968523710, 4627364713727441, 4744129458931172, 4860894204134903, 4977658949338634⟩
  | 76 => ⟨4628120639374801, 4746397235873252, 4864673832371703, 4982950428870154, 5101227025368605⟩
  | 77 => ⟨4747153161520612, 4866941609313783, 4986730057106954, 5106518504900125, 5226306952693296⟩
  | 78 => ⟨4867697534961143, 4988997834049034, 5110298133136925, 5231598432224816, 5352898731312707⟩
  | 79 => ⟨4989753759696394, 5112565910079005, 5235378060461616, 5358190210844227, 5481002361226838⟩
  | 80 => ⟨5113321835726365, 5237645837403696, 5361969839081027, 5486293840758358, 5610617842435689⟩
  | 81 => ⟨5238401763051056, 5364237616023107, 5490073468995158, 5615909321967209, 5741745174939260⟩
  | 82 => ⟨5364993541670467, 5492341245937238, 5619688950204009, 5747036654470780, 5874384358737551⟩
  | 83 => ⟨5493097171584598, 5621956727146089, 5750816282707580, 5879675838269071, 6008535393830562⟩
  | 84 => ⟨5622712652793449, 5753084059649660, 5883455466505871, 6013826873362082, 6144198280218293⟩
  | 85 => ⟨5753839985297020, 5885723243447951, 6017606501598882, 6149489759749813, 6281373017900744⟩
  | 86 => ⟨5886479169095311, 6019874278540962, 6153269387986613, 6286664497432264, 6420059606877915⟩
  | 87 => ⟨6020630204188322, 6155537164928693, 6290444125669064, 6425351086409435, 6560258047149806⟩
  | 88 => ⟨6156293090576053, 6292711902611144, 6429130714646235, 6565549526681326, 6701968338716417⟩
  | 89 => ⟨6293467828258504, 6431398491588315, 6569329154918126, 6707259818247937, 6845190481577748⟩
  | 90 => ⟨6432154417235675, 6571596931860206, 6711039446484737, 6850481961109268, 6989924475733799⟩
  | 91 => ⟨6572352857507566, 6713307223426817, 6854261589346068, 6995215955265319, 7136170321184570⟩
  | 92 => ⟨6714063149074177, 6856529366288148, 6998995583502119, 7141461800716090, 7283928017930061⟩
  | 93 => ⟨6857285291935508, 7001263360444199, 7145241428952890, 7289219497461581, 7433197565970272⟩
  | 94 => ⟨7002019286091559, 7147509205894970, 7292999125698381, 7438489045501792, 7583978965305203⟩
  | 95 => ⟨7148265131542330, 7295266902640461, 7442268673738592, 7589270444836723, 7736272215934854⟩
  | 96 => ⟨7296022828287821, 7444536450680672, 7593050073073523, 7741563695466374, 7890077317859225⟩
  | 97 => ⟨7445292376328032, 7595317850015603, 7745343323703174, 7895368797390745, 8045394271078316⟩
  | 98 => ⟨7596073775662963, 7747611100645254, 7899148425627545, 8050685750609836, 8202223075592127⟩
  | 99 => ⟨7748367026292614, 7901416202569625, 8054465378846636, 8207514555123647, 8360563731400658⟩
  | 100 => ⟨7902172128216985, 8056733155788716, 8211294183360447, 8365855210932178, 8520416238503909⟩
  | 101 => ⟨8057489081436076, 8213561960302527, 8369634839168978, 8525707718035429, 8681780596901880⟩
  | 102 => ⟨8214317885949887, 8371902616111058, 8529487346272229, 8687072076433400, 8844656806594571⟩
  | 103 => ⟨8372658541758418, 8531755123214309, 8690851704670200, 8849948286126091, 9009044867581982⟩
  | 104 => ⟨8532511048861669, 8693119481612280, 8853727914362891, 9014336347113502, 9174944779864113⟩
  | 105 => ⟨8693875407259640, 8855995691304971, 9018115975350302, 9180236259395633, 9342356543440964⟩
  | 106 => ⟨8856751616952331, 9020383752292382, 9184015887632433, 9347648022972484, 9511280158312535⟩
  | 107 => ⟨9021139677939742, 9186283664574513, 9351427651209284, 9516571637844055, 9681715624478826⟩
  | 108 => ⟨9187039590221873, 9353695428151364, 9520351266080855, 9687007104010346, 9853662941939837⟩
  | 109 => ⟨9354451353798724, 9522619043022935, 9690786732247146, 9858954421471357, 10027122110695568⟩
  | 110 => ⟨9523374968670295, 9693054509189226, 9862734049708157, 10032413590227088, 10202093130746019⟩
  | 111 => ⟨9693810434836586, 9865001826650237, 10036193218463888, 10207384610277539, 10378576002091190⟩
  | 112 => ⟨9865757752297597, 10038460995405968, 10211164238514339, 10383867481622710, 10556570724731081⟩
  | 113 => ⟨10039216921053328, 10213432015456419, 10387647109859510, 10561862204262601, 10736077298665692⟩
  | 114 => ⟨10214187941103779, 10389914886801590, 10565641832499401, 10741368778197212, 10917095723895023⟩
  | 115 => ⟨10390670812448950, 10567909609441481, 10745148406434012, 10922387203426543, 11099626000419074⟩
  | 116 => ⟨10568665535088841, 10747416183376092, 10926166831663343, 11104917479950594, 11283668128237845⟩
  | 117 => ⟨10748172109023452, 10928434608605423, 11108697108187394, 11288959607769365, 11469222107351336⟩
  | 118 => ⟨10929190534252783, 11110964885129474, 11292739236006165, 11474513586882856, 11656287937759547⟩
  | 119 => ⟨11111720810776834, 11295007012948245, 11478293215119656, 11661579417291067, 11844865619462478⟩
  | 120 => ⟨11295762938595605, 11480560992061736, 11665359045527867, 11850157098993998, 12034955152460129⟩
  | 121 => ⟨11481316917709096, 11667626822469947, 11853936727230798, 12040246631991649, 12226556536752500⟩
  | 122 => ⟨11668382748117307, 11856204504172878, 12044026260228449, 12231848016284020, 12419669772339591⟩
  | _ => defaultCosts

def row6 : ℕ → Costs
  | 0 => ⟨14843539095630, 17248741752920, 24601787629678, 31954833506436, 39307879383194⟩
  | 1 => ⟨17248741752920, 25288987639918, 33329233526916, 41369479413914, 49409725300912⟩
  | 2 => ⟨23072927776880, 31688765931655, 40304604086430, 48920442241205, 57536280395980⟩
  | 3 => ⟨32599312760967, 43036244574366, 53473176387765, 63910108201164, 74347040014563⟩
  | 4 => ⟨43946791403678, 56204816875701, 68462842347724, 80720867819747, 92978893291770⟩
  | 5 => ⟨57115363705013, 71194482835660, 85273601966307, 99352721096954, 113431840227601⟩
  | 6 => ⟨72105029664972, 88005242454243, 103905455243514, 119805668032785, 135705880822056⟩
  | 7 => ⟨88915789283555, 106637095731450, 124358402179345, 142079708627240, 159801015075135⟩
  | 8 => ⟨107547642560762, 127090042667281, 146632442773800, 166174842880319, 185717242986838⟩
  | 9 => ⟨128000589496593, 149364083261736, 170727577026879, 192091070792022, 213454564557165⟩
  | 10 => ⟨150274630091048, 173459217514815, 196643804938582, 219828392362349, 243012979786116⟩
  | 11 => ⟨174369764344127, 199375445426518, 224381126508909, 249386807591300, 274392488673691⟩
  | 12 => ⟨200285992255830, 227112766996845, 253939541737860, 280766316478875, 307593091219890⟩
  | 13 => ⟨228023313826157, 256671182225796, 285319050625435, 313966919025074, 342614787424713⟩
  | 14 => ⟨257581729055108, 288050691113371, 318519653171634, 348988615229897, 379457577288160⟩
  | 15 => ⟨288961237942683, 321251293659570, 353541349376457, 385831405093344, 418121460810231⟩
  | 16 => ⟨322161840488882, 356272989864393, 390384139239904, 424495288615415, 458606437990926⟩
  | 17 => ⟨357183536693705, 393115779727840, 429048022761975, 464980265796110, 500912508830245⟩
  | 18 => ⟨394026326557152, 431779663249911, 469532999942670, 507286336635429, 545039673328188⟩
  | 19 => ⟨432690210079223, 472264640430606, 511839070781989, 551413501133372, 590987931484755⟩
  | 20 => ⟨473175187259918, 514570711269925, 555966235279932, 597361759289939, 638757283299946⟩
  | 21 => ⟨515481258099237, 558697875767868, 601914493436499, 645131111105130, 688347728773761⟩
  | 22 => ⟨559608422597180, 604646133924435, 649683845251690, 694721556578945, 739759267906200⟩
  | 23 => ⟨605556680753747, 652415485739626, 699274290725505, 746133095711384, 792991900697263⟩
  | 24 => ⟨653326032568938, 702005931213441, 750685829857944, 799365728502447, 848045627146950⟩
  | 25 => ⟨702916478042753, 753417470345880, 803918462649007, 854419454952134, 904920447255261⟩
  | 26 => ⟨754328017175192, 806650103136943, 858972189098694, 911294275060445, 963616361022196⟩
  | 27 => ⟨807560649966255, 861703829586630, 915847009207005, 969990188827380, 1024133368447755⟩
  | 28 => ⟨862614376415942, 918578649694941, 974542922973940, 1030507196252939, 1086471469531938⟩
  | 29 => ⟨919489196524253, 977274563461876, 1035059930399499, 1092845297337122, 1150630664274745⟩
  | 30 => ⟨978185110291188, 1037791570887435, 1097398031483682, 1157004492079929, 1216610952676176⟩
  | 31 => ⟨1038702117716747, 1100129671971618, 1161557226226489, 1222984780481360, 1284412334736231⟩
  | 32 => ⟨1101040218800930, 1164288866714425, 1227537514627920, 1290786162541415, 1354034810454910⟩
  | 33 => ⟨1165199413543737, 1230269155115856, 1295338896687975, 1360408638260094, 1425478379832213⟩
  | 34 => ⟨1231179701945168, 1298070537175911, 1364961372406654, 1431852207637397, 1498743042868140⟩
  | 35 => ⟨1298981084005223, 1367693012894590, 1436404941783957, 1505116870673324, 1573828799562691⟩
  | 36 => ⟨1368603559723902, 1439136582271893, 1509669604819884, 1580202627367875, 1650735649915866⟩
  | 37 => ⟨1440047129101205, 1512401245307820, 1584755361514435, 1657109477721050, 1729463593927665⟩
  | 38 => ⟨1513311792137132, 1587487002002371, 1661662211867610, 1735837421732849, 1810012631598088⟩
  | 39 => ⟨1588397548831683, 1664393852355546, 1740390155879409, 1816386459403272, 1892382762927135⟩
  | 40 => ⟨1665304399184858, 1743121796367345, 1820939193549832, 1898756590732319, 1976573987914806⟩
  | 41 => ⟨1744032343196657, 1823670834037768, 1903309324878879, 1982947815719990, 2062586306561101⟩
  | 42 => ⟨1824581380867080, 1906040965366815, 1987500549866550, 2068960134366285, 2150419718866020⟩
  | 43 => ⟨1906951512196127, 1990232190354486, 2073512868512845, 2156793546671204, 2240074224829563⟩
  | 44 => ⟨1991142737183798, 2076244509000781, 2161346280817764, 2246448052634747, 2331549824451730⟩
  | 45 => ⟨2077155055830093, 2164077921305700, 2251000786781307, 2337923652256914, 2424846517732521⟩
  | 46 => ⟨2164988468135012, 2253732427269243, 2342476386403474, 2431220345537705, 2519964304671936⟩
  | 47 => ⟨2254642974098555, 2345208026891410, 2435773079684265, 2526338132477120, 2616903185269975⟩
  | 48 => ⟨2346118573720722, 2438504720172201, 2530890866623680, 2623277013075159, 2715663159526638⟩
  | 49 => ⟨2439415267001513, 2533622507111616, 2627829747221719, 2722036987331822, 2816244227441925⟩
  | 50 => ⟨2534533053940928, 2630561387709655, 2726589721478382, 2822618055247109, 2918646389015836⟩
  | 51 => ⟨2631471934538967, 2729321361966318, 2827170789393669, 2925020216821020, 3022869644248371⟩
  | 52 => ⟨2730231908795630, 2829902429881605, 2929572950967580, 3029243472053555, 3128913993139530⟩
  | 53 => ⟨2830812976710917, 2932304591455516, 3033796206200115, 3135287820944714, 3236779435689313⟩
  | 54 => ⟨2933215138284828, 3036527846688051, 3139840555091274, 3243153263494497, 3346465971897720⟩
  | 55 => ⟨3037438393517363, 3142572195579210, 3247705997641057, 3352839799702904, 3457973601764751⟩
  | 56 => ⟨3143482742408522, 3250437638128993, 3357392533849464, 3464347429569935, 3571302325290406⟩
  | 57 => ⟨3251348184958305, 3360124174337400, 3468900163716495, 3577676153095590, 3686452142474685⟩
  | 58 => ⟨3361034721166712, 3471631804204431, 3582228887242150, 3692825970279869, 3803423053317588⟩
  | 59 => ⟨3472542351033743, 3584960527730086, 3697378704426429, 3809796881122772, 3922215057819115⟩
  | 60 => ⟨3585871074559398, 3700110344914365, 3814349615269332, 3928588885624299, 4042828155979266⟩
  | 61 => ⟨3701020891743677, 3817081255757268, 3933141619770859, 4049201983784450, 4165262347798041⟩
  | 62 => ⟨3817991802586580, 3935873260258795, 4053754717931010, 4171636175603225, 4289517633275440⟩
  | 63 => ⟨3936783807088107, 4056486358418946, 4176188909749785, 4295891461080624, 4415594012411463⟩
  | 64 => ⟨4057396905248258, 4178920550237721, 4300444195227184, 4421967840216647, 4543491485206110⟩
  | 65 => ⟨4179831097067033, 4303175835715120, 4426520574363207, 4549865313011294, 4673210051659381⟩
  | 66 => ⟨4304086382544432, 4429252214851143, 4554418047157854, 4679583879464565, 4804749711771276⟩
  | 67 => ⟨4430162761680455, 4557149687645790, 4684136613611125, 4811123539576460, 4938110465541795⟩
  | 68 => ⟨4558060234475102, 4686868254099061, 4815676273723020, 4944484293346979, 5073292312970938⟩
  | 69 => ⟨4687778800928373, 4818407914210956, 4949037027493539, 5079666140776122, 5210295254058705⟩
  | 70 => ⟨4819318461040268, 4951768667981475, 5084218874922682, 5216669081863889, 5349119288805096⟩
  | 71 => ⟨4952679214810787, 5086950515410618, 5221221816010449, 5355493116610280, 5489764417210111⟩
  | 72 => ⟨5087861062239930, 5223953456498385, 5360045850756840, 5496138245015295, 5632230639273750⟩
  | 73 => ⟨5224864003327697, 5362777491244776, 5500690979161855, 5638604467078934, 5776517954996013⟩
  | 74 => ⟨5363688038074088, 5503422619649791, 5643157201225494, 5782891782801197, 5922626364376900⟩
  | 75 => ⟨5504333166479103, 5645888841713430, 5787444516947757, 5929000192182084, 6070555867416411⟩
  | 76 => ⟨5646799388542742, 5790176157435693, 5933552926328644, 6076929695221595, 6220306464114546⟩
  | 77 => ⟨5791086704265005, 5936284566816580, 6081482429368155, 6226680291919730, 6371878154471305⟩
  | 78 => ⟨5937195113645892, 6084214069856091, 6231233026066290, 6378251982276489, 6525270938486688⟩
  | 79 => ⟨6085124616685403, 6233964666554226, 6382804716423049, 6531644766291872, 6680484816160695⟩
  | 80 => ⟨6234875213383538, 6385536356910985, 6536197500438432, 6686858643965879, 6837519787493326⟩
  | 81 => ⟨6386446903740297, 6538929140926368, 6691411378112439, 6843893615298510, 6996375852484581⟩
  | 82 => ⟨6539839687755680, 6694143018600375, 6848446349445070, 7002749680289765, 7157053011134460⟩
  | 83 => ⟨6695053565429687, 6851177989933006, 7007302414436325, 7163426838939644, 7319551263442963⟩
  | 84 => ⟨6852088536762318, 7010034054924261, 7167979573086204, 7325925091248147, 7483870609410090⟩
  | 85 => ⟨7010944601753573, 7170711213574140, 7330477825394707, 7490244437215274, 7650011049035841⟩
  | 86 => ⟨7171621760403452, 7333209465882643, 7494797171361834, 7656384876841025, 7817972582320216⟩
  | 87 => ⟨7334120012711955, 7497528811849770, 7660937610987585, 7824346410125400, 7987755209263215⟩
  | 88 => ⟨7498439358679082, 7663669251475521, 7828899144271960, 7994129037068399, 8159358929864838⟩
  | 89 => ⟨7664579798304833, 7831630784759896, 7998681771214959, 8165732757670022, 8332783744125085⟩
  | 90 => ⟨7832541331589208, 8001413411702895, 8170285491816582, 8339157571930269, 8508029652043956⟩
  | 91 => ⟨8002323958532207, 8173017132304518, 8343710306076829, 8514403479849140, 8685096653621451⟩
  | 92 => ⟨8173927679133830, 8346441946564765, 8518956213995700, 8691470481426635, 8863984748857570⟩
  | 93 => ⟨8347352493394077, 8521687854483636, 8696023215573195, 8870358576662754, 9044693937752313⟩
  | 94 => ⟨8522598401312948, 8698754856061131, 8874911310809314, 9051067765557497, 9227224220305680⟩
  | 95 => ⟨8699665402890443, 8877642951297250, 9055620499704057, 9233598048110864, 9411575596517671⟩
  | 96 => ⟨8878553498126562, 9058352140191993, 9238150782257424, 9417949424322855, 9597748066388286⟩
  | 97 => ⟨9059262687021305, 9240882422745360, 9422502158469415, 9604121894193470, 9785741629917525⟩
  | 98 => ⟨9241792969574672, 9425233798957351, 9608674628340030, 9792115457722709, 9975556287105388⟩
  | 99 => ⟨9426144345786663, 9611406268827966, 9796668191869269, 9981930114910572, 10167192037951875⟩
  | 100 => ⟨9612316815657278, 9799399832357205, 9986482849057132, 10173565865757059, 10360648882456986⟩
  | 101 => ⟨9800310379186517, 9989214489545068, 10178118599903619, 10367022710262170, 10555926820620721⟩
  | 102 => ⟨9990125036374380, 10180850240391555, 10371575444408730, 10562300648425905, 10753025852443080⟩
  | 103 => ⟨10181760787220867, 10374307084896666, 10566853382572465, 10759399680248264, 10951945977924063⟩
  | 104 => ⟨10375217631725978, 10569585023060401, 10763952414394824, 10958319805729247, 11152687197063670⟩
  | 105 => ⟨10570495569889713, 10766684054882760, 10962872539875807, 11159061024868854, 11355249509861901⟩
  | 106 => ⟨10767594601712072, 10965604180363743, 11163613759015414, 11361623337667085, 11559632916318756⟩
  | 107 => ⟨10966514727193055, 11166345399503350, 11366176071813645, 11566006744123940, 11765837416434235⟩
  | 108 => ⟨11167255946332662, 11368907712301581, 11570559478270500, 11772211244239419, 11973863010208338⟩
  | 109 => ⟨11369818259130893, 11573291118758436, 11776763978385979, 11980236838013522, 12183709697641065⟩
  | 110 => ⟨11574201665587748, 11779495618873915, 11984789572160082, 12190083525446249, 12395377478732416⟩
  | 111 => ⟨11780406165703227, 11987521212648018, 12194636259592809, 12401751306537600, 12608866353482391⟩
  | 112 => ⟨11988431759477330, 12197367900080745, 12406304040684160, 12615240181287575, 12824176321890990⟩
  | 113 => ⟨12198278446910057, 12409035681172096, 12619792915434135, 12830550149696174, 13041307383958213⟩
  | 114 => ⟨12409946228001408, 12622524555922071, 12835102883842734, 13047681211763397, 13260259539684060⟩
  | 115 => ⟨12623435102751383, 12837834524330670, 13052233945909957, 13266633367489244, 13481032789068531⟩
  | 116 => ⟨12838745071159982, 13054965586397893, 13271186101635804, 13487406616873715, 13703627132111626⟩
  | 117 => ⟨13055876133227205, 13273917742123740, 13491959351020275, 13710000959916810, 13928042568813345⟩
  | 118 => ⟨13274828288953052, 13494690991508211, 13714553694063370, 13934416396618529, 14154279099173688⟩
  | 119 => ⟨13495601538337523, 13717285334551306, 13938969130765089, 14160652926978872, 14382336723192655⟩
  | 120 => ⟨13718195881380618, 13941700771253025, 14165205661125432, 14388710550997839, 14612215440870246⟩
  | 121 => ⟨13942611318082337, 14167937301613368, 14393263285144399, 14618589268675430, 14843915252206461⟩
  | _ => defaultCosts

def row7 : ℕ → Costs
  | 0 => ⟨23570986041449, 26869549236341, 36902676201615, 46935803166889, 56968930132163⟩
  | 1 => ⟨26869549236341, 37727316213903, 48585083191465, 59442850169027, 70300617146589⟩
  | 2 => ⟨33415370768529, 44556688752812, 55698006737095, 66839324721378, 77980642705661⟩
  | 3 => ⟨45621856764076, 58893510770887, 72165164777698, 85436818784509, 98708472791320⟩
  | 4 => ⟨59958678782151, 75360668811490, 90762658840829, 106164648870168, 121566638899507⟩
  | 5 => ⟨76425836822754, 93958162874621, 111490488926488, 129022814978355, 146555141030222⟩
  | 6 => ⟨95023330885885, 114685992960280, 134348655034675, 154011317109070, 173673979183465⟩
  | 7 => ⟨115751160971544, 137544159068467, 159337157165390, 181130155262313, 202923153359236⟩
  | 8 => ⟨138609327079731, 162532661199182, 186455995318633, 210379329438084, 234302663557535⟩
  | 9 => ⟨163597829210446, 189651499352425, 215705169494404, 241758839636383, 267812509778362⟩
  | 10 => ⟨190716667363689, 218900673528196, 247084679692703, 275268685857210, 303452692021717⟩
  | 11 => ⟨219965841539460, 250280183726495, 280594525913530, 310908868100565, 341223210287600⟩
  | 12 => ⟨251345351737759, 283790029947322, 316234708156885, 348679386366448, 381124064576011⟩
  | 13 => ⟨284855197958586, 319430212190677, 354005226422768, 388580240654859, 423155254886950⟩
  | 14 => ⟨320495380201941, 357200730456560, 393906080711179, 430611430965798, 467316781220417⟩
  | 15 => ⟨358265898467824, 397101584744971, 435937271022118, 474772957299265, 513608643576412⟩
  | 16 => ⟨398166752756235, 439132775055910, 480098797355585, 521064819655260, 562030841954935⟩
  | 17 => ⟨440197943067174, 483294301389377, 526390659711580, 569487018033783, 612583376355986⟩
  | 18 => ⟨484359469400641, 529586163745372, 574812858090103, 620039552434834, 665266246779565⟩
  | 19 => ⟨530651331756636, 578008362123895, 625365392491154, 672722422858413, 720079453225672⟩
  | 20 => ⟨579073530135159, 628560896524946, 678048262914733, 727535629304520, 777022995694307⟩
  | 21 => ⟨629626064536210, 681243766948525, 732861469360840, 784479171773155, 836096874185470⟩
  | 22 => ⟨682308934959789, 736056973394632, 789805011829475, 843553050264318, 897301088699161⟩
  | 23 => ⟨737122141405896, 793000515863267, 848878890320638, 904757264778009, 960635639235380⟩
  | 24 => ⟨794065683874531, 852074394354430, 910083104834329, 968091815314228, 1026100525794127⟩
  | 25 => ⟨853139562365694, 913278608868121, 973417655370548, 1033556701872975, 1093695748375402⟩
  | 26 => ⟨914343776879385, 976613159404340, 1038882541929295, 1101151924454250, 1163421306979205⟩
  | 27 => ⟨977678327415604, 1042078045963087, 1106477764510570, 1170877483058053, 1235277201605536⟩
  | 28 => ⟨1043143213974351, 1109673268544362, 1176203323114373, 1242733377684384, 1309263432254395⟩
  | 29 => ⟨1110738436555626, 1179398827148165, 1248059217740704, 1316719608333243, 1385379998925782⟩
  | 30 => ⟨1180463995159429, 1251254721774496, 1322045448389563, 1392836175004630, 1463626901619697⟩
  | 31 => ⟨1252319889785760, 1325240952423355, 1398162015060950, 1471083077698545, 1544004140336140⟩
  | 32 => ⟨1326306120434619, 1401357519094742, 1476408917754865, 1551460316414988, 1626511715075111⟩
  | 33 => ⟨1402422687106006, 1479604421788657, 1556786156471308, 1633967891153959, 1711149625836610⟩
  | 34 => ⟨1480669589799921, 1559981660505100, 1639293731210279, 1718605801915458, 1797917872620637⟩
  | 35 => ⟨1561046828516364, 1642489235244071, 1723931641971778, 1805374048699485, 1886816455427192⟩
  | 36 => ⟨1643554403255335, 1727127146005570, 1810699888755805, 1894272631506040, 1977845374256275⟩
  | 37 => ⟨1728192314016834, 1813895392789597, 1899598471562360, 1985301550335123, 2071004629107886⟩
  | 38 => ⟨1814960560800861, 1902793975596152, 1990627390391443, 2078460805186734, 2166294219982025⟩
  | 39 => ⟨1903859143607416, 1993822894425235, 2083786645243054, 2173750396060873, 2263714146878692⟩
  | 40 => ⟨1994888062436499, 2086982149276846, 2179076236117193, 2271170322957540, 2363264409797887⟩
  | 41 => ⟨2088047317288110, 2182271740150985, 2276496163013860, 2370720585876735, 2464945008739610⟩
  | 42 => ⟨2183336908162249, 2279691667047652, 2376046425933055, 2472401184818458, 2568755943703861⟩
  | 43 => ⟨2280756835058916, 2379241929966847, 2477727024874778, 2576212119782709, 2674697214690640⟩
  | 44 => ⟨2380307097978111, 2480922528908570, 2581537959839029, 2682153390769488, 2782768821699947⟩
  | 45 => ⟨2481987696919834, 2584733463872821, 2687479230825808, 2790224997778795, 2892970764731782⟩
  | 46 => ⟨2585798631884085, 2690674734859600, 2795550837835115, 2900426940810630, 3005303043786145⟩
  | 47 => ⟨2691739902870864, 2798746341868907, 2905752780866950, 3012759219864993, 3119765658863036⟩
  | 48 => ⟨2799811509880171, 2908948284900742, 3018085059921313, 3127221834941884, 3236358609962455⟩
  | 49 => ⟨2910013452912006, 3021280563955105, 3132547674998204, 3243814786041303, 3355081897084402⟩
  | 50 => ⟨3022345731966369, 3135743179031996, 3249140626097623, 3362538073163250, 3475935520228877⟩
  | 51 => ⟨3136808347043260, 3252336130131415, 3367863913219570, 3483391696307725, 3598919479395880⟩
  | 52 => ⟨3253401298142679, 3371059417253362, 3488717536364045, 3606375655474728, 3724033774585411⟩
  | 53 => ⟨3372124585264626, 3491913040397837, 3611701495531048, 3731489950664259, 3851278405797470⟩
  | 54 => ⟨3492978208409101, 3614896999564840, 3736815790720579, 3858734581876318, 3980653373032057⟩
  | 55 => ⟨3615962167576104, 3740011294754371, 3864060421932638, 3988109549110905, 4112158676289172⟩
  | 56 => ⟨3741076462765635, 3867255925966430, 3993435389167225, 4119614852368020, 4245794315568815⟩
  | 57 => ⟨3868321093977694, 3996630893201017, 4124940692424340, 4253250491647663, 4381560290870986⟩
  | 58 => ⟨3997696061212281, 4128136196458132, 4258576331703983, 4389016466949834, 4519456602195685⟩
  | 59 => ⟨4129201364469396, 4261771835737775, 4394342307006154, 4526912778274533, 4659483249542912⟩
  | 60 => ⟨4262837003749039, 4397537811039946, 4532238618330853, 4666939425621760, 4801640232912667⟩
  | 61 => ⟨4398602979051210, 4535434122364645, 4672265265678080, 4809096408991515, 4945927552304950⟩
  | 62 => ⟨4536499290375909, 4675460769711872, 4814422249047835, 4953383728383798, 5092345207719761⟩
  | 63 => ⟨4676525937723136, 4817617753081627, 4958709568440118, 5099801383798609, 5240893199157100⟩
  | 64 => ⟨4818682921092891, 4961905072473910, 5105127223854929, 5248349375235948, 5391571526616967⟩
  | 65 => ⟨4962970240485174, 5108322727888721, 5253675215292268, 5399027702695815, 5544380190099362⟩
  | 66 => ⟨5109387895899985, 5256870719326060, 5404353542752135, 5551836366178210, 5699319189604285⟩
  | 67 => ⟨5257935887337324, 5407549046785927, 5557162206234530, 5706775365683133, 5856388525131736⟩
  | 68 => ⟨5408614214797191, 5560357710268322, 5712101205739453, 5863844701210584, 6015588196681715⟩
  | 69 => ⟨5561422878279586, 5715296709773245, 5869170541266904, 6023044372760563, 6176918204254222⟩
  | 70 => ⟨5716361877784509, 5872366045300696, 6028370212816883, 6184374380333070, 6340378547849257⟩
  | 71 => ⟨5873431213311960, 6031565716850675, 6189700220389390, 6347834723928105, 6505969227466820⟩
  | 72 => ⟨6032630884861939, 6192895724423182, 6353160563984425, 6513425403545668, 6673690243106911⟩
  | 73 => ⟨6193960892434446, 6356356068018217, 6518751243601988, 6681146419185759, 6843541594769530⟩
  | 74 => ⟨6357421236029481, 6521946747635780, 6686472259242079, 6850997770848378, 7015523282454677⟩
  | 75 => ⟨6523011915647044, 6689667763275871, 6856323610904698, 7022979458533525, 7189635306162352⟩
  | 76 => ⟨6690732931287135, 6859519114938490, 7028305298589845, 7197091482241200, 7365877665892555⟩
  | 77 => ⟨6860584282949754, 7031500802623637, 7202417322297520, 7373333841971403, 7544250361645286⟩
  | 78 => ⟨7032565970634901, 7205612826331312, 7378659682027723, 7551706537724134, 7724753393420545⟩
  | 79 => ⟨7206677994342576, 7381855186061515, 7557032377780454, 7732209569499393, 7907386761218332⟩
  | 80 => ⟨7382920354072779, 7560227881814246, 7737535409555713, 7914842937297180, 8092150465038647⟩
  | 81 => ⟨7561293049825510, 7740730913589505, 7920168777353500, 8099606641117495, 8279044504881490⟩
  | 82 => ⟨7741796081600769, 7923364281387292, 8104932481173815, 8286500680960338, 8468068880746861⟩
  | 83 => ⟨7924429449398556, 8108127985207607, 8291826521016658, 8475525056825709, 8659223592634760⟩
  | 84 => ⟨8109193153218871, 8295022025050450, 8480850896882029, 8666679768713608, 8852508640545187⟩
  | 85 => ⟨8296087193061714, 8484046400915821, 8672005608769928, 8859964816624035, 9047924024478142⟩
  | 86 => ⟨8485111568927085, 8675201112803720, 8865290656680355, 9055380200556990, 9245469744433625⟩
  | 87 => ⟨8676266280814984, 8868486160714147, 9060706040613310, 9252925920512473, 9445145800411636⟩
  | 88 => ⟨8869551328725411, 9063901544647102, 9258251760568793, 9452601976490484, 9646952192412175⟩
  | 89 => ⟨9064966712658366, 9261447264602585, 9457927816546804, 9654408368491023, 9850888920435242⟩
  | 90 => ⟨9262512432613849, 9461123320580596, 9659734208547343, 9858345096514090, 10056955984480837⟩
  | 91 => ⟨9462188488591860, 9662929712581135, 9863670936570410, 10064412160559685, 10265153384548960⟩
  | 92 => ⟨9663994880592399, 9866866440604202, 10069738000616005, 10272609560627808, 10475481120639611⟩
  | 93 => ⟨9867931608615466, 10072933504649797, 10277935400684128, 10482937296718459, 10687939192752790⟩
  | 94 => ⟨10073998672661061, 10281130904717920, 10488263136774779, 10695395368831638, 10902527600888497⟩
  | 95 => ⟨10282196072729184, 10491458640808571, 10700721208887958, 10909983776967345, 11119246345046732⟩
  | 96 => ⟨10492523808819835, 10703916712921750, 10915309617023665, 11126702521125580, 11338095425227495⟩
  | 97 => ⟨10704981880933014, 10918505121057457, 11132028361181900, 11345551601306343, 11559074841430786⟩
  | 98 => ⟨10919570289068721, 11135223865215692, 11350877441362663, 11566531017509634, 11782184593656605⟩
  | 99 => ⟨11136289033226956, 11354072945396455, 11571856857565954, 11789640769735453, 12007424681904952⟩
  | 100 => ⟨11355138113407719, 11575052361599746, 11794966609791773, 12014880857983800, 12234795106175827⟩
  | 101 => ⟨11576117529611010, 11798162113825565, 12020206698040120, 12242251282254675, 12464295866469230⟩
  | 102 => ⟨11799227281836829, 12023402202073912, 12247577122310995, 12471752042548078, 12695926962785161⟩
  | 103 => ⟨12024467370085176, 12250772626344787, 12477077882604398, 12703383138864009, 12929688395123620⟩
  | 104 => ⟨12251837794356051, 12480273386638190, 12708708978920329, 12937144571202468, 13165580163484607⟩
  | 105 => ⟨12481338554649454, 12711904482954121, 12942470411258788, 13173036339563455, 13403602267868122⟩
  | 106 => ⟨12712969650965385, 12945665915292580, 13178362179619775, 13411058443946970, 13643754708274165⟩
  | 107 => ⟨12946731083303844, 13181557683653567, 13416384284003290, 13651210884353013, 13886037484702736⟩
  | 108 => ⟨13182622851664831, 13419579788037082, 13656536724409333, 13893493660781584, 14130450597153835⟩
  | 109 => ⟨13420644956048346, 13659732228443125, 13898819500837904, 14137906773232683, 14376994045627462⟩
  | 110 => ⟨13660797396454389, 13902015004871696, 14143232613289003, 14384450221706310, 14625667830123617⟩
  | 111 => ⟨13903080172882960, 14146428117322795, 14389776061762630, 14633124006202465, 14876471950642300⟩
  | 112 => ⟨14147493285334059, 14392971565796422, 14638449846258785, 14883928126721148, 15129406407183511⟩
  | 113 => ⟨14394036733807686, 14641645350292577, 14889253966777468, 15136862583262359, 15384471199747250⟩
  | 114 => ⟨14642710518303841, 14892449470811260, 15142188423318679, 15391927375826098, 15641666328333517⟩
  | 115 => ⟨14893514638822524, 15145383927352471, 15397253215882418, 15649122504412365, 15900991792942312⟩
  | 116 => ⟨15146449095363735, 15400448719916210, 15654448344468685, 15908447969021160, 16162447593573635⟩
  | 117 => ⟨15401513887927474, 15657643848502477, 15913773809077480, 16169903769652483, 16426033730227486⟩
  | 118 => ⟨15658709016513741, 15916969313111272, 16175229609708803, 16433489906306334, 16691750202903865⟩
  | 119 => ⟨15918034481122536, 16178425113742595, 16438815746362654, 16699206378982713, 16959597011602772⟩
  | 120 => ⟨16179490281753859, 16442011250396446, 16704532219039033, 16967053187681620, 17229574156324207⟩
  | _ => defaultCosts

def row8 : ℕ → Costs
  | 0 => ⟨35184674078856, 39514037813398, 52639565873332, 65765093933266, 78890621993200⟩
  | 1 => ⟨39514037813398, 53601645887668, 67689253961938, 81776862036208, 95864470110478⟩
  | 2 => ⟨46437914771638, 60413954949333, 74389995127028, 88366035304723, 102342075482418⟩
  | 3 => ⟨61633744142549, 78049362706676, 94464981270803, 110880599834930, 127296218399057⟩
  | 4 => ⟨79269151899892, 98124348850451, 116979545801010, 135834742751569, 154689939702128⟩
  | 5 => ⟨99344138043667, 120638913380658, 141933688717649, 163228464054640, 184523239391631⟩
  | 6 => ⟨121858702573874, 145593056297297, 169327410020720, 193061763744143, 216796117467566⟩
  | 7 => ⟨146812845490513, 172986777600368, 199160709710223, 225334641820078, 251508573929933⟩
  | 8 => ⟨174206566793584, 202820077289871, 231433587786158, 260047098282445, 288660608778732⟩
  | 9 => ⟨204039866483087, 235092955365806, 266146044248525, 297199133131244, 328252222013963⟩
  | 10 => ⟨236312744559022, 269805411828173, 303298079097324, 336790746366475, 370283413635626⟩
  | 11 => ⟨271025201021389, 306957446676972, 342889692332555, 378821937988138, 414754183643721⟩
  | 12 => ⟨308177235870188, 346549059912203, 384920883954218, 423292707996233, 461664532038248⟩
  | 13 => ⟨347768849105419, 388580251533866, 429391653962313, 470203056390760, 511014458819207⟩
  | 14 => ⟨389800040727082, 433051021541961, 476302002356840, 519552983171719, 562803963986598⟩
  | 15 => ⟨434270810735177, 479961369936488, 525651929137799, 571342488339110, 617033047540421⟩
  | 16 => ⟨481181159129704, 529311296717447, 577441434305190, 625571571892933, 673701709480676⟩
  | 17 => ⟨530531085910663, 581100801884838, 631670517859013, 682240233833188, 732809949807363⟩
  | 18 => ⟨582320591078054, 635329885438661, 688339179799268, 741348474159875, 794357768520482⟩
  | 19 => ⟨636549674631877, 691998547378916, 747447420125955, 802896292872994, 858345165620033⟩
  | 20 => ⟨693218336572132, 751106787705603, 808995238839074, 866883689972545, 924772141106016⟩
  | 21 => ⟨752326576898819, 812654606418722, 872982635938625, 933310665458528, 993638694978431⟩
  | 22 => ⟨813874395611938, 876642003518273, 939409611424608, 1002177219330943, 1064944827237278⟩
  | 23 => ⟨877861792711489, 943068979004256, 1008276165297023, 1073483351589790, 1138690537882557⟩
  | 24 => ⟨944288768197472, 1011935532876671, 1079582297555870, 1147229062235069, 1214875826914268⟩
  | 25 => ⟨1013155322069887, 1083241665135518, 1153328008201149, 1223414351266780, 1293500694332411⟩
  | 26 => ⟨1084461454328734, 1156987375780797, 1229513297232860, 1302039218684923, 1374565140136986⟩
  | 27 => ⟨1158207164974013, 1233172664812508, 1308138164651003, 1383103664489498, 1458069164327993⟩
  | 28 => ⟨1234392454005724, 1311797532230651, 1389202610455578, 1466607688680505, 1544012766905432⟩
  | 29 => ⟨1313017321423867, 1392861978035226, 1472706634646585, 1552551291257944, 1632395947869303⟩
  | 30 => ⟨1394081767228442, 1476366002226233, 1558650237224024, 1640934472221815, 1723218707219606⟩
  | 31 => ⟨1477585791419449, 1562309604803672, 1647033418187895, 1731757231572118, 1816481044956341⟩
  | 32 => ⟨1563529393996888, 1650692785767543, 1737856177538198, 1825019569308853, 1912182961079508⟩
  | 33 => ⟨1651912574960759, 1741515545117846, 1831118515274933, 1920721485432020, 2010324455589107⟩
  | 34 => ⟨1742735334311062, 1834777882854581, 1926820431398100, 2018862979941619, 2110905528485138⟩
  | 35 => ⟨1835997672047797, 1930479798977748, 2024961925907699, 2119444052837650, 2213926179767601⟩
  | 36 => ⟨1931699588170964, 2028621293487347, 2125542998803730, 2222464704120113, 2319386409436496⟩
  | 37 => ⟨2029841082680563, 2129202366383378, 2228563650086193, 2327924933789008, 2427286217491823⟩
  | 38 => ⟨2130422155576594, 2232223017665841, 2334023879755088, 2435824741844335, 2537625603933582⟩
  | 39 => ⟨2233442806859057, 2337683247334736, 2441923687810415, 2546164128286094, 2650404568761773⟩
  | 40 => ⟨2338903036527952, 2445583055390063, 2552263074252174, 2658943093114285, 2765623111976396⟩
  | 41 => ⟨2446802844583279, 2555922441831822, 2665042039080365, 2774161636328908, 2883281233577451⟩
  | 42 => ⟨2557142231025038, 2668701406660013, 2780260582294988, 2891819757929963, 3003378933564938⟩
  | 43 => ⟨2669921195853229, 2783919949874636, 2897918703896043, 3011917457917450, 3125916211938857⟩
  | 44 => ⟨2785139739067852, 2901578071475691, 3018016403883530, 3134454736291369, 3250893068699208⟩
  | 45 => ⟨2902797860668907, 3021675771463178, 3140553682257449, 3259431593051720, 3378309503845991⟩
  | 46 => ⟨3022895560656394, 3144213049837097, 3265530539017800, 3386848028198503, 3508165517379206⟩
  | 47 => ⟨3145432839030313, 3269189906597448, 3392946974164583, 3516704041731718, 3640461109298853⟩
  | 48 => ⟨3270409695790664, 3396606341744231, 3522802987697798, 3648999633651365, 3775196279604932⟩
  | 49 => ⟨3397826130937447, 3526462355277446, 3655098579617445, 3783734803957444, 3912371028297443⟩
  | 50 => ⟨3527682144470662, 3658757947197093, 3789833749923524, 3920909552649955, 4051985355376386⟩
  | 51 => ⟨3659977736390309, 3793493117503172, 3927008498616035, 4060523879728898, 4194039260841761⟩
  | 52 => ⟨3794712906696388, 3930667866195683, 4066622825694978, 4202577785194273, 4338532744693568⟩
  | 53 => ⟨3931887655388899, 4070282193274626, 4208676731160353, 4347071269046080, 4485465806931807⟩
  | 54 => ⟨4071501982467842, 4212336098740001, 4353170215012160, 4494004331284319, 4634838447556478⟩
  | 55 => ⟨4213555887933217, 4356829582591808, 4500103277250399, 4643376971908990, 4786650666567581⟩
  | 56 => ⟨4358049371785024, 4503762644830047, 4649475917875070, 4795189190920093, 4940902463965116⟩
  | 57 => ⟨4504982434023263, 4653135285454718, 4801288136886173, 4949440988317628, 5097593839749083⟩
  | 58 => ⟨4654355074647934, 4804947504465821, 4955539934283708, 5106132364101595, 5256724793919482⟩
  | 59 => ⟨4806167293659037, 4959199301863356, 5112231310067675, 5265263318271994, 5418295326476313⟩
  | 60 => ⟨4960419091056572, 5115890677647323, 5271362264238074, 5426833850828825, 5582305437419576⟩
  | 61 => ⟨5117110466840539, 5275021631817722, 5432932796794905, 5590843961772088, 5748755126749271⟩
  | 62 => ⟨5276241421010938, 5436592164374553, 5596942907738168, 5757293651101783, 5917644394465398⟩
  | 63 => ⟨5437811953567769, 5600602275317816, 5763392597067863, 5926182918817910, 6088973240567957⟩
  | 64 => ⟨5601822064511032, 5767051964647511, 5932281864783990, 6097511764920469, 6262741665056948⟩
  | 65 => ⟨5768271753840727, 5935941232363638, 6103610710886549, 6271280189409460, 6438949667932371⟩
  | 66 => ⟨5937161021556854, 6107270078466197, 6277379135375540, 6447488192284883, 6617597249194226⟩
  | 67 => ⟨6108489867659413, 6281038502955188, 6453587138250963, 6626135773546738, 6798684408842513⟩
  | 68 => ⟨6282258292148404, 6457246505830611, 6632234719512818, 6807222933195025, 6982211146877232⟩
  | 69 => ⟨6458466295023827, 6635894087092466, 6813321879161105, 6990749671229744, 7168177463298383⟩
  | 70 => ⟨6637113876285682, 6816981246740753, 6996848617195824, 7176715987650895, 7356583358105966⟩
  | 71 => ⟨6818201035933969, 7000507984775472, 7182814933616975, 7365121882458478, 7547428831299981⟩
  | 72 => ⟨7001727773968688, 7186474301196623, 7371220828424558, 7555967355652493, 7740713882880428⟩
  | 73 => ⟨7187694090389839, 7374880196004206, 7562066301618573, 7749252407232940, 7936438512847307⟩
  | 74 => ⟨7376099985197422, 7565725669198221, 7755351353199020, 7944977037199819, 8134602721200618⟩
  | 75 => ⟨7566945458391437, 7759010720778668, 7951075983165899, 8143141245553130, 8335206507940361⟩
  | 76 => ⟨7760230509971884, 7954735350745547, 8149240191519210, 8343745032292873, 8538249873066536⟩
  | 77 => ⟨7955955139938763, 8152899559098858, 8349843978258953, 8546788397419048, 8743732816579143⟩
  | 78 => ⟨8154119348292074, 8353503345838601, 8552887343385128, 8752271340931655, 8951655338478182⟩
  | 79 => ⟨8354723135031817, 8556546710964776, 8758370286897735, 8960193862830694, 9162017438763653⟩
  | 80 => ⟨8557766500157992, 8762029654477383, 8966292808796774, 9170555963116165, 9374819117435556⟩
  | 81 => ⟨8763249443670599, 8969952176376422, 9176654909082245, 9383357641788068, 9590060374493891⟩
  | 82 => ⟨8971171965569638, 9180314276661893, 9389456587754148, 9598598898846403, 9807741209938658⟩
  | 83 => ⟨9181534065855109, 9393115955333796, 9604697844812483, 9816279734291170, 10027861623769857⟩
  | 84 => ⟨9394335744527012, 9608357212392131, 9822378680257250, 10036400148122369, 10250421615987488⟩
  | 85 => ⟨9609577001585347, 9826038047836898, 10042499094088449, 10258960140340000, 10475421186591551⟩
  | 86 => ⟨9827257837030114, 10046158461668097, 10265059086306080, 10483959710944063, 10702860335582046⟩
  | 87 => ⟨10047378250861313, 10268718453885728, 10490058656910143, 10711398859934558, 10932739062958973⟩
  | 88 => ⟨10269938243078944, 10493718024489791, 10717497805900638, 10941277587311485, 11165057368722332⟩
  | 89 => ⟨10494937813683007, 10721157173480286, 10947376533277565, 11173595893074844, 11399815252872123⟩
  | 90 => ⟨10722376962673502, 10951035900857213, 11179694839040924, 11408353777224635, 11637012715408346⟩
  | 91 => ⟨10952255690050429, 11183354206620572, 11414452723190715, 11645551239760858, 11876649756331001⟩
  | 92 => ⟨11184573995813788, 11418112090770363, 11651650185726938, 11885188280683513, 12118726375640088⟩
  | 93 => ⟨11419331879963579, 11655309553306586, 11891287226649593, 12127264899992600, 12363242573335607⟩
  | 94 => ⟨11656529342499802, 11894946594229241, 12133363845958680, 12371781097688119, 12610198349417558⟩
  | 95 => ⟨11896166383422457, 12137023213538328, 12377880043654199, 12618736873770070, 12859593703885941⟩
  | 96 => ⟨12138243002731544, 12381539411233847, 12624835819736150, 12868132228238453, 13111428636740756⟩
  | 97 => ⟨12382759200427063, 12628495187315798, 12874231174204533, 13119967161093268, 13365703147982003⟩
  | 98 => ⟨12629714976509014, 12877890541784181, 13126066107059348, 13374241672334515, 13622417237609682⟩
  | 99 => ⟨12879110330977397, 13129725474638996, 13380340618300595, 13630955761962194, 13881570905623793⟩
  | 100 => ⟨13130945263832212, 13383999985880243, 13637054707928274, 13890109429976305, 14143164152024336⟩
  | 101 => ⟨13385219775073459, 13640714075507922, 13896208375942385, 14151702676376848, 14407196976811311⟩
  | 102 => ⟨13641933864701138, 13899867743522033, 14157801622342928, 14415735501163823, 14673669379984718⟩
  | 103 => ⟨13901087532715249, 14161460989922576, 14421834447129903, 14682207904337230, 14942581361544557⟩
  | 104 => ⟨14162680779115792, 14425493814709551, 14688306850303310, 14951119885897069, 15213932921490828⟩
  | 105 => ⟨14426713603902767, 14691966217882958, 14957218831863149, 15222471445843340, 15487724059823531⟩
  | 106 => ⟨14693186007076174, 14960878199442797, 15228570391809420, 15496262584176043, 15763954776542666⟩
  | 107 => ⟨14962097988636013, 15232229759389068, 15502361530142123, 15772493300895178, 16042625071648233⟩
  | 108 => ⟨15233449548582284, 15506020897721771, 15778592246861258, 16051163596000745, 16323734945140232⟩
  | 109 => ⟨15507240686914987, 15782251614440906, 16057262541966825, 16332273469492744, 16607284397018663⟩
  | 110 => ⟨15783471403634122, 16060921909546473, 16338372415458824, 16615822921371175, 16893273427283526⟩
  | 111 => ⟨16062141698739689, 16342031783038472, 16621921867337255, 16901811951636038, 17181702035934821⟩
  | 112 => ⟨16343251572231688, 16625581234916903, 16907910897602118, 17190240560287333, 17472570222972548⟩
  | 113 => ⟨16626801024110119, 16911570265181766, 17196339506253413, 17481108747325060, 17765877988396707⟩
  | 114 => ⟨16912790054374982, 17199998873833061, 17487207693291140, 17774416512749219, 18061625332207298⟩
  | 115 => ⟨17201218663026277, 17490867060870788, 17780515458715299, 18070163856559810, 18359812254404321⟩
  | 116 => ⟨17492086850064004, 17784174826294947, 18076262802525890, 18368350778756833, 18660438754987776⟩
  | 117 => ⟨17785394615488163, 18079922170105538, 18374449724722913, 18668977279340288, 18963504833957663⟩
  | 118 => ⟨18081141959298754, 18378109092302561, 18675076225306368, 18972043358310175, 19269010491313982⟩
  | 119 => ⟨18379328881495777, 18678735592886016, 18978142304276255, 19277549015666494, 19576955727056733⟩
  | _ => defaultCosts

def row9 : ℕ → Costs
  | 0 => ⟨50096923213995, 55594527490235, 72224776650973, 88855025811711, 105485274972449⟩
  | 1 => ⟨55594527490235, 73324296667357, 91054065844479, 108783835021601, 126513604198723⟩
  | 2 => ⟨62449802150111, 79569806885122, 96689811620133, 113809816355144, 130929821090155⟩
  | 3 => ⟨80944217260290, 100813042745637, 120681868230984, 140550693716331, 160419519201678⟩
  | 4 => ⟨102187453120805, 124805099356488, 147422745592171, 170040391827854, 192658038063537⟩
  | 5 => ⟨126179509731656, 151545976717675, 176912443703694, 202278910689713, 227645377675732⟩
  | 6 => ⟨152920387092843, 181035674829198, 209150962565553, 237266250301908, 265381538038263⟩
  | 7 => ⟨182410085204366, 213274193691057, 244138302177748, 275002410664439, 305866519151130⟩
  | 8 => ⟨214648604066225, 248261533303252, 281874462540279, 315487391777306, 349100321014333⟩
  | 9 => ⟨249635943678420, 285997693665783, 322359443653146, 358721193640509, 395082943627872⟩
  | 10 => ⟨287372104040951, 326482674778650, 365593245516349, 404703816254048, 443814386991747⟩
  | 11 => ⟨327857085153818, 369716476641853, 411575868129888, 453435259617923, 495294651105958⟩
  | 12 => ⟨371090887017021, 415699099255392, 460307311493763, 504915523732134, 549523735970505⟩
  | 13 => ⟨417073509630560, 464430542619267, 511787575607974, 559144608596681, 606501641585388⟩
  | 14 => ⟨465804952994435, 515910806733478, 566016660472521, 616122514211564, 666228367950607⟩
  | 15 => ⟨517285217108646, 570139891598025, 622994566087404, 675849240576783, 728703915066162⟩
  | 16 => ⟨571514301973193, 627117797212908, 682721292452623, 738324787692338, 793928282932053⟩
  | 17 => ⟨628492207588076, 686844523578127, 745196839568178, 803549155558229, 861901471548280⟩
  | 18 => ⟨688218933953295, 749320070693682, 810421207434069, 871522344174456, 932623480914843⟩
  | 19 => ⟨750694481068850, 814544438559573, 878394396050296, 942244353541019, 1006094311031742⟩
  | 20 => ⟨815918848934741, 882517627175800, 949116405416859, 1015715183657918, 1082313961898977⟩
  | 21 => ⟨883892037550968, 953239636542363, 1022587235533758, 1091934834525153, 1161282433516548⟩
  | 22 => ⟨954614046917531, 1026710466659262, 1098806886400993, 1170903306142724, 1242999725884455⟩
  | 23 => ⟨1028084877034430, 1102930117526497, 1177775358018564, 1252620598510631, 1327465839002698⟩
  | 24 => ⟨1104304527901665, 1181898589144068, 1259492650386471, 1337086711628874, 1414680772871277⟩
  | 25 => ⟨1183272999519236, 1263615881511975, 1343958763504714, 1424301645497453, 1504644527490192⟩
  | 26 => ⟨1264990291887143, 1348081994630218, 1431173697373293, 1514265400116368, 1597357102859443⟩
  | 27 => ⟨1349456405005386, 1435296928498797, 1521137451992208, 1606977975485619, 1692818498979030⟩
  | 28 => ⟨1436671338873965, 1525260683117712, 1613850027361459, 1702439371605206, 1791028715848953⟩
  | 29 => ⟨1526635093492880, 1617973258486963, 1709311423481046, 1800649588475129, 1891987753469212⟩
  | 30 => ⟨1619347668862131, 1713434654606550, 1807521640350969, 1901608626095388, 1995695611839807⟩
  | 31 => ⟨1714809064981718, 1811644871476473, 1908480677971228, 2005316484465983, 2102152290960738⟩
  | 32 => ⟨1813019281851641, 1912603909096732, 2012188536341823, 2111773163586914, 2211357790832005⟩
  | 33 => ⟨1913978319471900, 2016311767467327, 2118645215462754, 2220978663458181, 2323312111453608⟩
  | 34 => ⟨2017686177842495, 2122768446588258, 2227850715334021, 2332932984079784, 2438015252825547⟩
  | 35 => ⟨2124142856963426, 2231973946459525, 2339805035955624, 2447636125451723, 2555467214947822⟩
  | 36 => ⟨2233348356834693, 2343928267081128, 2454508177327563, 2565088087573998, 2675667997820433⟩
  | 37 => ⟨2345302677456296, 2458631408453067, 2571960139449838, 2685288870446609, 2798617601443380⟩
  | 38 => ⟨2460005818828235, 2576083370575342, 2692160922322449, 2808238474069556, 2924316025816663⟩
  | 39 => ⟨2577457780950510, 2696284153447953, 2815110525945396, 2933936898442839, 3052763270940282⟩
  | 40 => ⟨2697658563823121, 2819233757070900, 2940808950318679, 3062384143566458, 3183959336814237⟩
  | 41 => ⟨2820608167446068, 2944932181444183, 3069256195442298, 3193580209440413, 3317904223438528⟩
  | 42 => ⟨2946306591819351, 3073379426567802, 3200452261316253, 3327525096064704, 3454597930813155⟩
  | 43 => ⟨3074753836942970, 3204575492441757, 3334397147940544, 3464218803439331, 3594040458938118⟩
  | 44 => ⟨3205949902816925, 3338520379066048, 3471090855315171, 3603661331564294, 3736231807813417⟩
  | 45 => ⟨3339894789441216, 3475214086440675, 3610533383440134, 3745852680439593, 3881171977439052⟩
  | 46 => ⟨3476588496815843, 3614656614565638, 3752724732315433, 3890792850065228, 4028860967815023⟩
  | 47 => ⟨3616031024940806, 3756847963440937, 3897664901941068, 4038481840441199, 4179298778941330⟩
  | 48 => ⟨3758222373816105, 3901788133066572, 4045353892317039, 4188919651567506, 4332485410817973⟩
  | 49 => ⟨3903162543441740, 4049477123442543, 4195791703443346, 4342106283444149, 4488420863444952⟩
  | 50 => ⟨4050851533817711, 4199914934568850, 4348978335319989, 4498041736071128, 4647105136822267⟩
  | 51 => ⟨4201289344944018, 4353101566445493, 4504913787946968, 4656726009448443, 4808538230949918⟩
  | 52 => ⟨4354475976820661, 4509037019072472, 4663598061324283, 4818159103576094, 4972720145827905⟩
  | 53 => ⟨4510411429447640, 4667721292449787, 4825031155451934, 4982341018454081, 5139650881456228⟩
  | 54 => ⟨4669095702824955, 4829154386577438, 4989213070329921, 5149271754082404, 5309330437834887⟩
  | 55 => ⟨4830528796952606, 4993336301455425, 5156143805958244, 5318951310461063, 5481758814963882⟩
  | 56 => ⟨4994710711830593, 5160267037083748, 5325823362336903, 5491379687590058, 5656936012843213⟩
  | 57 => ⟨5161641447458916, 5329946593462407, 5498251739465898, 5666556885469389, 5834862031472880⟩
  | 58 => ⟨5331321003837575, 5502374970591402, 5673428937345229, 5844482904099056, 6015536870852883⟩
  | 59 => ⟨5503749380966570, 5677552168470733, 5851354955974896, 6025157743479059, 6198960530983222⟩
  | 60 => ⟨5678926578845901, 5855478187100400, 6032029795354899, 6208581403609398, 6385133011863897⟩
  | 61 => ⟨5856852597475568, 6036153026480403, 6215453455485238, 6394753884490073, 6574054313494908⟩
  | 62 => ⟨6037527436855571, 6219576686610742, 6401625936365913, 6583675186121084, 6765724435876255⟩
  | 63 => ⟨6220951096985910, 6405749167491417, 6590547237996924, 6775345308502431, 6960143379007938⟩
  | 64 => ⟨6407123577866585, 6594670469122428, 6782217360378271, 6969764251634114, 7157311142889957⟩
  | 65 => ⟨6596044879497596, 6786340591503775, 6976636303509954, 7166932015516133, 7357227727522312⟩
  | 66 => ⟨6787715001878943, 6980759534635458, 7173804067391973, 7366848600148488, 7559893132905003⟩
  | 67 => ⟨6982133945010626, 7177927298517477, 7373720652024328, 7569514005531179, 7765307359038030⟩
  | 68 => ⟨7179301708892645, 7377843883149832, 7576386057407019, 7774928231664206, 7973470405921393⟩
  | 69 => ⟨7379218293525000, 7580509288532523, 7781800283540046, 7983091278547569, 8184382273555092⟩
  | 70 => ⟨7581883698907691, 7785923514665550, 7989963330423409, 8194003146181268, 8398042961939127⟩
  | 71 => ⟨7787297925040718, 7994086561548913, 8200875198057108, 8407663834565303, 8614452471073498⟩
  | 72 => ⟨7995460971924081, 8204998429182612, 8414535886441143, 8624073343699674, 8833610800958205⟩
  | 73 => ⟨8206372839557780, 8418659117566647, 8630945395575514, 8843231673584381, 9055517951593248⟩
  | 74 => ⟨8420033527941815, 8635068626701018, 8850103725460221, 9065138824219424, 9280173922978627⟩
  | 75 => ⟨8636443037076186, 8854226956585725, 9072010876095264, 9289794795604803, 9507578715114342⟩
  | 76 => ⟨8855601366960893, 9076134107220768, 9296666847480643, 9517199587740518, 9737732328000393⟩
  | 77 => ⟨9077508517595936, 9300790078606147, 9524071639616358, 9747353200626569, 9970634761636780⟩
  | 78 => ⟨9302164488981315, 9528194870741862, 9754225252502409, 9980255634262956, 10206286016023503⟩
  | 79 => ⟨9529569281117030, 9758348483627913, 9987127686138796, 10215906888649679, 10444686091160562⟩
  | 80 => ⟨9759722894003081, 9991250917264300, 10222778940525519, 10454306963786738, 10685834987047957⟩
  | 81 => ⟨9992625327639468, 10226902171651023, 10461179015662578, 10695455859674133, 10929732703685688⟩
  | 82 => ⟨10228276582026191, 10465302246788082, 10702327911549973, 10939353576311864, 11176379241073755⟩
  | 83 => ⟨10466676657163250, 10706451142675477, 10946225628187704, 11186000113699931, 11425774599212158⟩
  | 84 => ⟨10707825553050645, 10950348859313208, 11192872165575771, 11435395471838334, 11677918778100897⟩
  | 85 => ⟨10951723269688376, 11196995396701275, 11442267523714174, 11687539650727073, 11932811777739972⟩
  | 86 => ⟨11198369807076443, 11446390754839678, 11694411702602913, 11942432650366148, 12190453598129383⟩
  | 87 => ⟨11447765165214846, 11698534933728417, 11949304702241988, 12200074470755559, 12450844239269130⟩
  | 88 => ⟨11699909344103585, 11953427933367492, 12206946522631399, 12460465111895306, 12713983701159213⟩
  | 89 => ⟨11954802343742660, 12211069753756903, 12467337163771146, 12723604573785389, 12979871983799632⟩
  | 90 => ⟨12212444164132071, 12471460394896650, 12730476625661229, 12989492856425808, 13248509087190387⟩
  | 91 => ⟨12472834805271818, 12734599856786733, 12996364908301648, 13258129959816563, 13519895011331478⟩
  | 92 => ⟨12735974267161901, 13000488139427152, 13265002011692403, 13529515883957654, 13794029756222905⟩
  | 93 => ⟨13001862549802320, 13269125242817907, 13536387935833494, 13803650628849081, 14070913321864668⟩
  | 94 => ⟨13270499653193075, 13540511166958998, 13810522680724921, 14080534194490844, 14350545708256767⟩
  | 95 => ⟨13541885577334166, 13814645911850425, 14087406246366684, 14360166580882943, 14632926915399202⟩
  | 96 => ⟨13816020322225593, 14091529477492188, 14367038632758783, 14642547788025378, 14918056943291973⟩
  | 97 => ⟨14092903887867356, 14371161863884287, 14649419839901218, 14927677815918149, 15205935791935080⟩
  | 98 => ⟨14372536274259455, 14653543071026722, 14934549867793989, 15215556664561256, 15496563461328523⟩
  | 99 => ⟨14654917481401890, 14938673098919493, 15222428716437096, 15506184333954699, 15789939951472302⟩
  | 100 => ⟨14940047509294661, 15226551947562600, 15513056385830539, 15799560824098478, 16086065262366417⟩
  | 101 => ⟨15227926357937768, 15517179616956043, 15806432875974318, 16095686134992593, 16384939394010868⟩
  | 102 => ⟨15518554027331211, 15810556107099822, 16102558186868433, 16394560266637044, 16686562346405655⟩
  | 103 => ⟨15811930517474990, 16106681417993937, 16401432318512884, 16696183219031831, 16990934119550778⟩
  | 104 => ⟨16108055828369105, 16405555549638388, 16703055270907671, 17000554992176954, 17298054713446237⟩
  | 105 => ⟨16406929960013556, 16707178502033175, 17007427044052794, 17307675586072413, 17607924128092032⟩
  | 106 => ⟨16708552912408343, 17011550275178298, 17314547637948253, 17617545000718208, 17920542363488163⟩
  | 107 => ⟨17012924685553466, 17318670869073757, 17624417052594048, 17930163236114339, 18235909419634630⟩
  | 108 => ⟨17320045279448925, 17628540283719552, 17937035287990179, 18245530292260806, 18554025296531433⟩
  | 109 => ⟨17629914694094720, 17941158519115683, 18252402344136646, 18563646169157609, 18874889994178572⟩
  | 110 => ⟨17942532929490851, 18256525575262150, 18570518221033449, 18884510866804748, 19198503512576047⟩
  | 111 => ⟨18257899985637318, 18574641452158953, 18891382918680588, 19208124385202223, 19524865851723858⟩
  | 112 => ⟨18576015862534121, 18895506149806092, 19214996437078063, 19534486724350034, 19853977011622005⟩
  | 113 => ⟨18896880560181260, 19219119668203567, 19541358776225874, 19863597884248181, 20185836992270488⟩
  | 114 => ⟨19220494078578735, 19545482007351378, 19870469936124021, 20195457864896664, 20520445793669307⟩
  | 115 => ⟨19546856417726546, 19874593167249525, 20202329916772504, 20530066666295483, 20857803415818462⟩
  | 116 => ⟨19875967577624693, 20206453147898008, 20536938718171323, 20867424288444638, 21197909858717953⟩
  | 117 => ⟨20207827558273176, 20541061949296827, 20874296340320478, 21207530731344129, 21540765122367780⟩
  | 118 => ⟨20542436359671995, 20878419571445982, 21214402783219969, 21550385994993956, 21886369206767943⟩
  | _ => defaultCosts

def row10 : ℕ → Costs
  | 0 => ⟨68720053453010, 75523338272996, 96070628540682, 116617918808368, 137165209076054⟩
  | 1 => ⟨75523338272996, 97307588559114, 119091838845232, 140876089131350, 162660339417468⟩
  | 2 => ⟨81760275267852, 102333486924083, 122906698580314, 143479910236545, 164053121892776⟩
  | 3 => ⟨103862518481203, 127493793251674, 151125068022145, 174756342792616, 198387617563087⟩
  | 4 => ⟨129022824808794, 155712162693505, 182401500578216, 209090838462927, 235780176347638⟩
  | 5 => ⟨157241194250625, 186988595249576, 216735996248527, 246483397247478, 276230798246429⟩
  | 6 => ⟨188517626806696, 221323090919887, 254128555033078, 286934019146269, 319739483259460⟩
  | 7 => ⟨222852122477007, 258715649704438, 294579176931869, 330442704159300, 366306231386731⟩
  | 8 => ⟨260244681261558, 299166271603229, 338087861944900, 377009452286571, 415931042628242⟩
  | 9 => ⟨300695303160349, 342674956616260, 384654610072171, 426634263528082, 468613916983993⟩
  | 10 => ⟨344203988173380, 389241704743531, 434279421313682, 479317137883833, 524354854453984⟩
  | 11 => ⟨390770736300651, 438866515985042, 486962295669433, 535058075353824, 583153855038215⟩
  | 12 => ⟨440395547542162, 491549390340793, 542703233139424, 593857075938055, 645010918736686⟩
  | 13 => ⟨493078421897913, 547290327810784, 601502233723655, 655714139636526, 709926045549397⟩
  | 14 => ⟨548819359367904, 606089328395015, 663359297422126, 720629266449237, 777899235476348⟩
  | 15 => ⟨607618359952135, 667946392093486, 728274424234837, 788602456376188, 848930488517539⟩
  | 16 => ⟨669475423650606, 732861518906197, 796247614161788, 859633709417379, 923019804672970⟩
  | 17 => ⟨734390550463317, 800834708833148, 867278867202979, 933723025572810, 1000167183942641⟩
  | 18 => ⟨802363740390268, 871865961874339, 941368183358410, 1010870404842481, 1080372626326552⟩
  | 19 => ⟨873394993431459, 945955278029770, 1018515562628081, 1091075847226392, 1163636131824703⟩
  | 20 => ⟨947484309586890, 1023102657299441, 1098721005011992, 1174339352724543, 1249957700437094⟩
  | 21 => ⟨1024631688856561, 1103308099683352, 1181984510510143, 1260660921336934, 1339337332163725⟩
  | 22 => ⟨1104837131240472, 1186571605181503, 1268306079122534, 1350040553063565, 1431775027004596⟩
  | 23 => ⟨1188100636738623, 1272893173793894, 1357685710849165, 1442478247904436, 1527270784959707⟩
  | 24 => ⟨1274422205351014, 1362272805520525, 1450123405690036, 1537974005859547, 1625824606029058⟩
  | 25 => ⟨1363801837077645, 1454710500361396, 1545619163645147, 1636527826928898, 1727436490212649⟩
  | 26 => ⟨1456239531918516, 1550206258316507, 1644172984714498, 1738139711112489, 1832106437510480⟩
  | 27 => ⟨1551735289873627, 1648760079385858, 1745784868898089, 1842809658410320, 1939834447922551⟩
  | 28 => ⟨1650289110942978, 1750371963569449, 1850454816195920, 1950537668822391, 2050620521448862⟩
  | 29 => ⟨1751900995126569, 1855041910867280, 1958182826607991, 2061323742348702, 2164464658089413⟩
  | 30 => ⟨1856570942424400, 1962769921279351, 2068968900134302, 2175167878989253, 2281366857844204⟩
  | 31 => ⟨1964298952836471, 2073555994805662, 2182813036774853, 2292070078744044, 2401327120713235⟩
  | 32 => ⟨2075085026362782, 2187400131446213, 2299715236529644, 2412030341613075, 2524345446696506⟩
  | 33 => ⟨2188929163003333, 2304302331201004, 2419675499398675, 2535048667596346, 2650421835794017⟩
  | 34 => ⟨2305831362758124, 2424262594070035, 2542693825381946, 2661125056693857, 2779556288005768⟩
  | 35 => ⟨2425791625627155, 2547280920053306, 2668770214479457, 2790259508905608, 2911748803331759⟩
  | 36 => ⟨2548809951610426, 2673357309150817, 2797904666691208, 2922452024231599, 3046999381771990⟩
  | 37 => ⟨2674886340707937, 2802491761362568, 2930097182017199, 3057702602671830, 3185308023326461⟩
  | 38 => ⟨2804020792919688, 2934684276688559, 3065347760457430, 3196011244226301, 3326674727995172⟩
  | 39 => ⟨2936213308245679, 3069934855128790, 3203656402011901, 3337377948895012, 3471099495778123⟩
  | 40 => ⟨3071463886685910, 3208243496683261, 3345023106680612, 3481802716677963, 3618582326675314⟩
  | 41 => ⟨3209772528240381, 3349610201351972, 3489447874463563, 3629285547575154, 3769123220686745⟩
  | 42 => ⟨3351139232909092, 3494034969134923, 3636930705360754, 3779826441586585, 3922722177812416⟩
  | 43 => ⟨3495564000692043, 3641517800032114, 3787471599372185, 3933425398712256, 4079379198052327⟩
  | 44 => ⟨3643046831589234, 3792058694043545, 3941070556497856, 4090082418952167, 4239094281406478⟩
  | 45 => ⟨3793587725600665, 3945657651169216, 4097727576737767, 4249797502306318, 4401867427874869⟩
  | 46 => ⟨3947186682726336, 4102314671409127, 4257442660091918, 4412570648774709, 4567698637457500⟩
  | 47 => ⟨4103843702966247, 4262029754763278, 4420215806560309, 4578401858357340, 4736587910154371⟩
  | 48 => ⟨4263558786320398, 4424802901231669, 4586047016142940, 4747291131054211, 4908535245965482⟩
  | 49 => ⟨4426331932788789, 4590634110814300, 4754936288839811, 4919238466865322, 5083540644890833⟩
  | 50 => ⟨4592163142371420, 4759523383511171, 4926883624650922, 5094243865790673, 5261604106930424⟩
  | 51 => ⟨4761052415068291, 4931470719322282, 5101889023576273, 5272307327830264, 5442725632084255⟩
  | 52 => ⟨4932999750879402, 5106476118247633, 5279952485615864, 5453428852984095, 5626905220352326⟩
  | 53 => ⟨5108005149804753, 5284539580287224, 5461074010769695, 5637608441252166, 5814142871734637⟩
  | 54 => ⟨5286068611844344, 5465661105441055, 5645253599037766, 5824846092634477, 6004438586231188⟩
  | 55 => ⟨5467190136998175, 5649840693709126, 5832491250420077, 6015141807131028, 6197792363841979⟩
  | 56 => ⟨5651369725266246, 5837078345091437, 6022786964916628, 6208495584741819, 6394204204567010⟩
  | 57 => ⟨5838607376648557, 6027374059587988, 6216140742527419, 6404907425466850, 6593674108406281⟩
  | 58 => ⟨6028903091145108, 6220727837198779, 6412552583252450, 6604377329306121, 6796202075359792⟩
  | 59 => ⟨6222256868755899, 6417139677923810, 6612022487091721, 6806905296259632, 7001788105427543⟩
  | 60 => ⟨6418668709480930, 6616609581763081, 6814550454045232, 7012491326327383, 7210432198609534⟩
  | 61 => ⟨6618138613320201, 6819137548716592, 7020136484112983, 7221135419509374, 7422134354905765⟩
  | 62 => ⟨6820666580273712, 7024723578784343, 7228780577294974, 7432837575805605, 7636894574316236⟩
  | 63 => ⟨7026252610341463, 7233367671966334, 7440482733591205, 7647597795216076, 7854712856840947⟩
  | 64 => ⟨7234896703523454, 7445069828262565, 7655242953001676, 7865416077740787, 8075589202479898⟩
  | 65 => ⟨7446598859819685, 7659830047673036, 7873061235526387, 8086292423379738, 8299523611233089⟩
  | 66 => ⟨7661359079230156, 7877648330197747, 8093937581165338, 8310226832132929, 8526516083100520⟩
  | 67 => ⟨7879177361754867, 8098524675836698, 8317871989918529, 8537219304000360, 8756566618082191⟩
  | 68 => ⟨8100053707393818, 8322459084589889, 8544864461785960, 8767269838982031, 8989675216178102⟩
  | 69 => ⟨8323988116147009, 8549451556457320, 8774914996767631, 9000378437077942, 9225841877388253⟩
  | 70 => ⟨8550980588014440, 8779502091438991, 9008023594863542, 9236545098288093, 9465066601712644⟩
  | 71 => ⟨8781031122996111, 9012610689534902, 9244190256073693, 9475769822612484, 9707349389151275⟩
  | 72 => ⟨9014139721092022, 9248777350745053, 9483414980398084, 9718052610051115, 9952690239704146⟩
  | 73 => ⟨9250306382302173, 9488002075069444, 9725697767836715, 9963393460603986, 10201089153371257⟩
  | 74 => ⟨9489531106626564, 9730284862508075, 9971038618389586, 10211792374271097, 10452546130152608⟩
  | 75 => ⟨9731813894065195, 9975625713060946, 10219437532056697, 10463249351052448, 10707061170048199⟩
  | 76 => ⟨9977154744618066, 10224024626728057, 10470894508838048, 10717764390948039, 10964634273058030⟩
  | 77 => ⟨10225553658285177, 10475481603509408, 10725409548733639, 10975337493957870, 11225265439182101⟩
  | 78 => ⟨10477010635066528, 10729996643404999, 10982982651743470, 11235968660081941, 11488954668420412⟩
  | 79 => ⟨10731525674962119, 10987569746414830, 11243613817867541, 11499657889320252, 11755701960772963⟩
  | 80 => ⟨10989098777971950, 11248200912538901, 11507303047105852, 11766405181672803, 12025507316239754⟩
  | 81 => ⟨11249729944096021, 11511890141777212, 11774050339458403, 12036210537139594, 12298370734820785⟩
  | 82 => ⟨11513419173334332, 11778637434129763, 12043855694925194, 12309073955720625, 12574292216516056⟩
  | 83 => ⟨11780166465686883, 12048442789596554, 12316719113506225, 12584995437415896, 12853271761325567⟩
  | 84 => ⟨12049971821153674, 12321306208177585, 12592640595201496, 12863974982225407, 13135309369249318⟩
  | 85 => ⟨12322835239734705, 12597227689872856, 12871620140011007, 13146012590149158, 13420405040287309⟩
  | 86 => ⟨12598756721429976, 12876207234682367, 13153657747934758, 13431108261187149, 13708558774439540⟩
  | 87 => ⟨12877736266239487, 13158244842606118, 13438753418972749, 13719261995339380, 13999770571706011⟩
  | 88 => ⟨13159773874163238, 13443340513644109, 13726907153124980, 14010473792605851, 14294040432086722⟩
  | 89 => ⟨13444869545201229, 13731494247796340, 14018118950391451, 14304743652986562, 14591368355581673⟩
  | 90 => ⟨13733023279353460, 14022706045062811, 14312388810772162, 14602071576481513, 14891754342190864⟩
  | 91 => ⟨14024235076619931, 14316975905443522, 14609716734267113, 14902457563090704, 15195198391914295⟩
  | 92 => ⟨14318504937000642, 14614303828938473, 14910102720876304, 15205901612814135, 15501700504751966⟩
  | 93 => ⟨14615832860495593, 14914689815547664, 15213546770599735, 15512403725651806, 15811260680703877⟩
  | 94 => ⟨14916218847104784, 15218133865271095, 15520048883437406, 15821963901603717, 16123878919770028⟩
  | 95 => ⟨15219662896828215, 15524635978108766, 15829609059389317, 16134582140669868, 16439555221950419⟩
  | 96 => ⟨15526165009665886, 15834196154060677, 16142227298455468, 16450258442850259, 16758289587245050⟩
  | 97 => ⟨15835725185617797, 16146814393126828, 16457903600635859, 16768992808144890, 17080082015653921⟩
  | 98 => ⟨16148343424683948, 16462490695307219, 16776637965930490, 17090785236553761, 17404932507177032⟩
  | 99 => ⟨16464019726864339, 16781225060601850, 17098430394339361, 17415635728076872, 17732841061814383⟩
  | 100 => ⟨16782754092158970, 17103017489010721, 17423280885862472, 17743544282714223, 18063807679565974⟩
  | 101 => ⟨17104546520567841, 17427867980533832, 17751189440499823, 18074510900465814, 18397832360431805⟩
  | 102 => ⟨17429397012090952, 17755776535171183, 18082156058251414, 18408535581331645, 18734915104411876⟩
  | 103 => ⟨17757305566728303, 18086743152922774, 18416180739117245, 18745618325311716, 19075055911506187⟩
  | 104 => ⟨18088272184479894, 18420767833788605, 18753263483097316, 19085759132406027, 19418254781714738⟩
  | 105 => ⟨18422296865345725, 18757850577768676, 19093404290191627, 19428958002614578, 19764511715037529⟩
  | 106 => ⟨18759379609325796, 19097991384862987, 19436603160400178, 19775214935937369, 20113826711474560⟩
  | 107 => ⟨19099520416420107, 19441190255071538, 19782860093722969, 20124529932374400, 20466199771025831⟩
  | 108 => ⟨19442719286628658, 19787447188394329, 20132175090160000, 20476902991925671, 20821630893691342⟩
  | 109 => ⟨19788976219951449, 20136762184831360, 20484548149711271, 20832334114591182, 21180120079471093⟩
  | 110 => ⟨20138291216388480, 20489135244382631, 20839979272376782, 21190823300370933, 21541667328365084⟩
  | 111 => ⟨20490664275939751, 20844566367048142, 21198468458156533, 21552370549264924, 21906272640373315⟩
  | 112 => ⟨20846095398605262, 21203055552827893, 21560015707050524, 21916975861273155, 22273936015495786⟩
  | 113 => ⟨21204584584385013, 21564602801721884, 21924621019058755, 22284639236395626, 22644657453732497⟩
  | 114 => ⟨21566131833279004, 21929208113730115, 22292284394181226, 22655360674632337, 23018436955083448⟩
  | 115 => ⟨21930737145287235, 22296871488852586, 22663005832417937, 23029140175983288, 23395274519548639⟩
  | 116 => ⟨22298400520409706, 22667592927089297, 23036785333768888, 23405977740448479, 23775170147128070⟩
  | 117 => ⟨22669121958646417, 23041372428440248, 23413622898234079, 23785873368027910, 24158123837821741⟩
  | _ => defaultCosts

def row11 : ℕ → Costs
  | 0 => ⟨91466384802045, 99712790167825, 124589441548603, 149466092929381, 174342744310159⟩
  | 1 => ⟨99712790167825, 125963841569083, 152214892970341, 178465944371599, 204716995772857⟩
  | 2 => ⟨104678576488765, 129014237430120, 153349898371475, 177685559312830, 202021220254185⟩
  | 3 => ⟨130697890169192, 158400856588691, 186103823008190, 213806789427689, 241509755847188⟩
  | 4 => ⟨160084509327763, 191154781225406, 222225053123049, 253295325020692, 284365596918335⟩
  | 5 => ⟨192838433964478, 227276011340265, 261713588716052, 296151166091839, 330588743467626⟩
  | 6 => ⟨228959664079337, 266764546933268, 304569429787199, 342374312641130, 380179195495061⟩
  | 7 => ⟨268448199672340, 309620388004415, 350792576336490, 391964764668565, 433136953000640⟩
  | 8 => ⟨311304040743487, 355843534553706, 400383028363925, 444922522174144, 489462015984363⟩
  | 9 => ⟨357527187292778, 405433986581141, 453340785869504, 501247585157867, 549154384446230⟩
  | 10 => ⟨407117639320213, 458391744086720, 509665848853227, 560939953619734, 612214058386241⟩
  | 11 => ⟨460075396825792, 514716807070443, 569358217315094, 623999627559745, 678641037804396⟩
  | 12 => ⟨516400459809515, 574409175532310, 632417891255105, 690426606977900, 748435322700695⟩
  | 13 => ⟨576092828271382, 637468849472321, 698844870673260, 760220891874199, 821596913075138⟩
  | 14 => ⟨639152502211393, 703895828890476, 768639155569559, 833382482248642, 898125808927725⟩
  | 15 => ⟨705579481629548, 773690113786775, 841800745944002, 909911378101229, 978022010258456⟩
  | 16 => ⟨775373766525847, 846851704161218, 918329641796589, 989807579431960, 1061285517067331⟩
  | 17 => ⟨848535356900290, 923380600013805, 998225843127320, 1073071086240835, 1147916329354350⟩
  | 18 => ⟨925064252752877, 1003276801344536, 1081489349936195, 1159701898527854, 1237914447119513⟩
  | 19 => ⟨1004960454083608, 1086540308153411, 1168120162223214, 1249700016293017, 1331279870362820⟩
  | 20 => ⟨1088223960892483, 1173171120440430, 1258118279988377, 1343065439536324, 1428012599084271⟩
  | 21 => ⟨1174854773179502, 1263169238205593, 1351483703231684, 1439798168257775, 1528112633283866⟩
  | 22 => ⟨1264852890944665, 1356534661448900, 1448216431953135, 1539898202457370, 1631579972961605⟩
  | 23 => ⟨1358218314187972, 1453267390170351, 1548316466152730, 1643365542135109, 1738414618117488⟩
  | 24 => ⟨1454951042909423, 1553367424369946, 1651783805830469, 1750200187290992, 1848616568751515⟩
  | 25 => ⟨1555051077109018, 1656834764047685, 1758618450986352, 1860402137925019, 1962185824863686⟩
  | 26 => ⟨1658518416786757, 1763669409203568, 1868820401620379, 1973971394037190, 2079122386454001⟩
  | 27 => ⟨1765353061942640, 1873871359837595, 1982389657732550, 2090907955627505, 2199426253522460⟩
  | 28 => ⟨1875555012576667, 1987440615949766, 2099326219322865, 2211211822695964, 2323097426069063⟩
  | 29 => ⟨1989124268688838, 2104377177540081, 2219630086391324, 2334882995242567, 2450135904093810⟩
  | 30 => ⟨2106060830279153, 2224681044608540, 2343301258937927, 2461921473267314, 2580541687596701⟩
  | 31 => ⟨2226364697347612, 2348352217155143, 2470339736962674, 2592327256770205, 2714314776577736⟩
  | 32 => ⟨2350035869894215, 2475390695179890, 2600745520465565, 2726100345751240, 2851455171036915⟩
  | 33 => ⟨2477074347918962, 2605796478682781, 2734518609446600, 2863240740210419, 2991962870974238⟩
  | 34 => ⟨2607480131421853, 2739569567663816, 2871659003905779, 3003748440147742, 3135837876389705⟩
  | 35 => ⟨2741253220402888, 2876709962122995, 3012166703843102, 3147623445563209, 3283080187283316⟩
  | 36 => ⟨2878393614862067, 3017217662060318, 3156041709258569, 3294865756456820, 3433689803655071⟩
  | 37 => ⟨3018901314799390, 3161092667475785, 3303284020152180, 3445475372828575, 3587666725504970⟩
  | 38 => ⟨3162776320214857, 3308334978369396, 3453893636523935, 3599452294678474, 3745010952833013⟩
  | 39 => ⟨3310018631108468, 3458944594741151, 3607870558373834, 3756796522006517, 3905722485639200⟩
  | 40 => ⟨3460628247480223, 3612921516591050, 3765214785701877, 3917508054812704, 4069801323923531⟩
  | 41 => ⟨3614605169330122, 3770265743919093, 3925926318508064, 4081586893097035, 4237247467686006⟩
  | 42 => ⟨3771949396658165, 3930977276725280, 4090005156792395, 4249033036859510, 4408060916926625⟩
  | 43 => ⟨3932660929464352, 4095056115009611, 4257451300554870, 4419846486100129, 4582241671645388⟩
  | 44 => ⟨4096739767748683, 4262502258772086, 4428264749795489, 4594027240818892, 4759789731842295⟩
  | 45 => ⟨4264185911511158, 4433315708012705, 4602445504514252, 4771575301015799, 4940705097517346⟩
  | 46 => ⟨4434999360751777, 4607496462731468, 4779993564711159, 4952490666690850, 5124987768670541⟩
  | 47 => ⟨4609180115470540, 4785044522928375, 4960908930386210, 5136773337844045, 5312637745301880⟩
  | 48 => ⟨4786728175667447, 4965959888603426, 5145191601539405, 5324423314475384, 5503655027411363⟩
  | 49 => ⟨4967643541342498, 5150242559756621, 5332841578170744, 5515440596584867, 5698039614998990⟩
  | 50 => ⟨5151926212495693, 5337892536387960, 5523858860280227, 5709825184172494, 5895791508064761⟩
  | 51 => ⟨5339576189127032, 5528909818497443, 5718243447867854, 5907577077238265, 6096910706608676⟩
  | 52 => ⟨5530593471236515, 5723294406085070, 5915995340933625, 6108696275782180, 6301397210630735⟩
  | 53 => ⟨5724978058824142, 5921046299150841, 6117114539477540, 6313182779804239, 6509251020130938⟩
  | 54 => ⟨5922729951889913, 6122165497694756, 6321601043499599, 6521036589304442, 6720472135109285⟩
  | 55 => ⟨6123849150433828, 6326652001716815, 6529454852999802, 6732257704282789, 6935060555565776⟩
  | 56 => ⟨6328335654455887, 6534505811217018, 6740675967978149, 6946846124739280, 7153016281500411⟩
  | 57 => ⟨6536189463956090, 6745726926195365, 6955264388434640, 7164801850673915, 7374339312913190⟩
  | 58 => ⟨6747410578934437, 6960315346651856, 7173220114369275, 7386124882086694, 7599029649804113⟩
  | 59 => ⟨6961998999390928, 7178271072586491, 7394543145782054, 7610815218977617, 7827087292173180⟩
  | 60 => ⟨7179954725325563, 7399594103999270, 7619233482672977, 7838872861346684, 8058512240020391⟩
  | 61 => ⟨7401277756738342, 7624284440890193, 7847291125042044, 8070297809193895, 8293304493345746⟩
  | 62 => ⟨7625968093629265, 7852342083259260, 8078716072889255, 8305090062519250, 8531464052149245⟩
  | 63 => ⟨7854025735998332, 8083767031106471, 8313508326214610, 8543249621322749, 8772990916430888⟩
  | 64 => ⟨8085450683845543, 8318559284431826, 8551667885018109, 8784776485604392, 9017885086190675⟩
  | 65 => ⟨8320242937170898, 8556718843235325, 8793194749299752, 9029670655364179, 9266146561428606⟩
  | 66 => ⟨8558402495974397, 8798245707516968, 9038088919059539, 9277932130602110, 9517775342144681⟩
  | 67 => ⟨8799929360256040, 9043139877276755, 9286350394297470, 9529560911318185, 9772771428338900⟩
  | 68 => ⟨9044823530015827, 9291401352514686, 9537979175013545, 9784556997512404, 10031134820011263⟩
  | 69 => ⟨9293085005253758, 9543030133230761, 9792975261207764, 10042920389184767, 10292865517161770⟩
  | 70 => ⟨9544713785969833, 9798026219424980, 10051338652880127, 10304651086335274, 10557963519790421⟩
  | 71 => ⟨9799709872164052, 10056389611097343, 10313069350030634, 10569749088963925, 10826428827897216⟩
  | 72 => ⟨10058073263836415, 10318120308247850, 10578167352659285, 10838214397070720, 11098261441482155⟩
  | 73 => ⟨10319803960986922, 10583218310876501, 10846632660766080, 11110047010655659, 11373461360545238⟩
  | 74 => ⟨10584901963615573, 10851683618983296, 11118465274351019, 11385246929718742, 11652028585086465⟩
  | 75 => ⟨10853367271722368, 11123516232568235, 11393665193414102, 11663814154259969, 11933963115105836⟩
  | 76 => ⟨11125199885307307, 11398716151631318, 11672232417955329, 11945748684279340, 12219264950603351⟩
  | 77 => ⟨11400399804370390, 11677283376172545, 11954166947974700, 12231050519776855, 12507934091579010⟩
  | 78 => ⟨11678967028911617, 11959217906191916, 12239468783472215, 12519719660752514, 12799970538032813⟩
  | 79 => ⟨11960901558930988, 12244519741689431, 12528137924447874, 12811756107206317, 13095374289964760⟩
  | 80 => ⟨12246203394428503, 12533188882665090, 12820174370901677, 13107159859138264, 13394145347374851⟩
  | 81 => ⟨12534872535404162, 12825225329118893, 13115578122833624, 13405930916548355, 13696283710263086⟩
  | 82 => ⟨12826908981857965, 13120629081050840, 13414349180243715, 13708069279436590, 14001789378629465⟩
  | 83 => ⟨13122312733789912, 13419400138460931, 13716487543131950, 14013574947802969, 14310662352473988⟩
  | 84 => ⟨13421083791200003, 13721538501349166, 14021993211498329, 14322447921647492, 14622902631796655⟩
  | 85 => ⟨13723222154088238, 14027044169715545, 14330866185342852, 14634688200970159, 14938510216597466⟩
  | 86 => ⟨14028727822454617, 14335917143560068, 14643106464665519, 14950295785770970, 15257485106876421⟩
  | 87 => ⟨14337600796299140, 14648157422882735, 14958714049466330, 15269270676049925, 15579827302633520⟩
  | 88 => ⟨14649841075621807, 14963765007683546, 15277688939745285, 15591612871807024, 15905536803868763⟩
  | 89 => ⟨14965448660422618, 15282739897962501, 15600031135502384, 15917322373042267, 16234613610582150⟩
  | 90 => ⟨15284423550701573, 15605082093719600, 15925740636737627, 16246399179755654, 16567057722773681⟩
  | 91 => ⟨15606765746458672, 15930791594954843, 16254817443451014, 16578843291947185, 16902869140443356⟩
  | 92 => ⟨15932475247693915, 16259868401668230, 16587261555642545, 16914654709616860, 17242047863591175⟩
  | 93 => ⟨16261552054407302, 16592312513859761, 16923072973312220, 17253833432764679, 17584593892217138⟩
  | 94 => ⟨16593996166598833, 16928123931529436, 17262251696460039, 17596379461390642, 17930507226321245⟩
  | 95 => ⟨16929807584268508, 17267302654677255, 17604797725086002, 17942292795494749, 18279787865903496⟩
  | 96 => ⟨17268986307416327, 17609848683303218, 17950711059190109, 18291573435077000, 18632435810963891⟩
  | 97 => ⟨17611532336042290, 17955762017407325, 18299991698772360, 18644221380137395, 18988451061502430⟩
  | 98 => ⟨17957445670146397, 18305042656989576, 18652639643832755, 19000236630675934, 19347833617519113⟩
  | 99 => ⟨18306726309728648, 18657690602049971, 19008654894371294, 19359619186692617, 19710583479013940⟩
  | 100 => ⟨18659374254789043, 19013705852588510, 19368037450387977, 19722369048187444, 20076700645986911⟩
  | 101 => ⟨19015389505327582, 19373088408605193, 19730787311882804, 20088486215160415, 20446185118438026⟩
  | 102 => ⟨19374772061344265, 19735838270100020, 20096904478855775, 20457970687611530, 20819036896367285⟩
  | 103 => ⟨19737521922839092, 20101955437072991, 20466388951306890, 20830822465540789, 21195255979774688⟩
  | 104 => ⟨20103639089812063, 20471439909524106, 20839240729236149, 21207041548948192, 21574842368660235⟩
  | 105 => ⟨20473123562263178, 20844291687453365, 21215459812643552, 21586627937833739, 21957796063023926⟩
  | 106 => ⟨20845975340192437, 21220510770860768, 21595046201529099, 21969581632197430, 22344117062865761⟩
  | 107 => ⟨21222194423599840, 21600097159746315, 21977999895892790, 22355902632039265, 22733805368185740⟩
  | 108 => ⟨21601780812485387, 21983050854110006, 22364320895734625, 22745590937359244, 23126860978983863⟩
  | 109 => ⟨21984734506849078, 22369371853951841, 22754009201054604, 23138646548157367, 23523283895260130⟩
  | 110 => ⟨22371055506690913, 22759060159271820, 23147064811852727, 23535069464433634, 23923074117014541⟩
  | 111 => ⟨22760743812010892, 23152115770069943, 23543487728128994, 23934859686188045, 24326231644247096⟩
  | 112 => ⟨23153799422809015, 23548538686346210, 23943277949883405, 24338017213420600, 24732756476957795⟩
  | 113 => ⟨23550222339085282, 23948328908100621, 24346435477115960, 24744542046131299, 25142648615146638⟩
  | 114 => ⟨23950012560839693, 24351486435333176, 24752960309826659, 25154434184320142, 25555908058813625⟩
  | 115 => ⟨24353170088072248, 24758011268043875, 25162852448015502, 25567693627987129, 25972534807958756⟩
  | 116 => ⟨24759694920782947, 25167903406232718, 25576111891682489, 25984320377132260, 26392528862582031⟩
  | _ => defaultCosts

def row12 : ℕ → Costs
  | 0 => ⟨118748237267244, 128575203180866, 158193535680880, 187811868180894, 217430200680908⟩
  | 1 => ⟨128575203180866, 159705375703408, 190835548225950, 221965720748492, 253095893271034⟩
  | 2 => ⟨131513948176754, 159921300767137, 188328653357520, 216736005947903, 245143358538286⟩
  | 3 => ⟨161759574688161, 193843475120592, 225927375553023, 258011275985454, 290095176417885⟩
  | 4 => ⟨195681749041616, 231442197316095, 267202645590574, 302963093865053, 338723542139532⟩
  | 5 => ⟨233280471237119, 272717467353646, 312154463470173, 351591459586700, 391028455703227⟩
  | 6 => ⟨274555741274670, 317669285233245, 360782829191820, 403896373150395, 447009917108970⟩
  | 7 => ⟨319507559154269, 366297650954892, 413087742755515, 459877834556138, 506667926356761⟩
  | 8 => ⟨368135924875916, 418602564518587, 469069204161258, 519535843803929, 570002483446600⟩
  | 9 => ⟨420440838439611, 474584025924330, 528727213409049, 582870400893768, 637013588378487⟩
  | 10 => ⟨476422299845354, 534242035172121, 592061770498888, 649881505825655, 707701241152422⟩
  | 11 => ⟨536080309093145, 597576592261960, 659072875430775, 720569158599590, 782065441768405⟩
  | 12 => ⟨599414866182984, 664587697193847, 729760528204710, 794933359215573, 860106190226436⟩
  | 13 => ⟨666425971114871, 735275349967782, 804124728820693, 872974107673604, 941823486526515⟩
  | 14 => ⟨737113623888806, 809639550583765, 882165477278724, 954691403973683, 1027217330668642⟩
  | 15 => ⟨811477824504789, 887680299041796, 963882773578803, 1040085248115810, 1116287722652817⟩
  | 16 => ⟨889518572962820, 969397595341875, 1049276617720930, 1129155640099985, 1209034662479040⟩
  | 17 => ⟨971235869262899, 1054791439484002, 1138347009705105, 1221902579926208, 1305458150147311⟩
  | 18 => ⟨1056629713405026, 1143861831468177, 1231093949531328, 1318326067594479, 1405558185657630⟩
  | 19 => ⟨1145700105389201, 1236608771294400, 1327517437199599, 1418426103104798, 1509334769009997⟩
  | 20 => ⟨1238447045215424, 1333032258962671, 1427617472709918, 1522202686457165, 1616787900204412⟩
  | 21 => ⟨1334870532883695, 1433132294472990, 1531394056062285, 1629655817651580, 1727917579240875⟩
  | 22 => ⟨1434970568394014, 1536908877825357, 1638847187256700, 1740785496688043, 1842723806119386⟩
  | 23 => ⟨1538747151746381, 1644362009019772, 1749976866293163, 1855591723566554, 1961206580839945⟩
  | 24 => ⟨1646200282940796, 1755491688056235, 1864783093171674, 1974074498287113, 2083365903402552⟩
  | 25 => ⟨1757329961977259, 1870297914934746, 1983265867892233, 2096233820849720, 2209201773807207⟩
  | 26 => ⟨1872136188855770, 1988780689655305, 2105425190454840, 2222069691254375, 2338714192053910⟩
  | 27 => ⟨1990618963576329, 2110940012217912, 2231261060859495, 2351582109501078, 2471903158142661⟩
  | 28 => ⟨2112778286138936, 2236775882622567, 2360773479106198, 2484771075589829, 2608768672073460⟩
  | 29 => ⟨2238614156543591, 2366288300869270, 2493962445194949, 2621636589520628, 2749310733846307⟩
  | 30 => ⟨2368126574790294, 2499477266958021, 2630827959125748, 2762178651293475, 2893529343461202⟩
  | 31 => ⟨2501315540879045, 2636342780888820, 2771370020898595, 2906397260908370, 3041424500918145⟩
  | 32 => ⟨2638181054809844, 2776884842661667, 2915588630513490, 3054292418365313, 3192996206217136⟩
  | 33 => ⟨2778723116582691, 2921103452276562, 3063483787970433, 3205864123664304, 3348244459358175⟩
  | 34 => ⟨2922941726197586, 3068998609733505, 3215055493269424, 3361112376805343, 3507169260341262⟩
  | 35 => ⟨3070836883654529, 3220570315032496, 3370303746410463, 3520037177788430, 3669770609166397⟩
  | 36 => ⟨3222408588953520, 3375818568173535, 3529228547393550, 3682638526613565, 3836048505833580⟩
  | 37 => ⟨3377656842094559, 3534743369156622, 3691829896218685, 3848916423280748, 4006002950342811⟩
  | 38 => ⟨3536581643077646, 3697344717981757, 3858107792885868, 4018870867789979, 4179633942694090⟩
  | 39 => ⟨3699182991902781, 3863622614648940, 4028062237395099, 4192501860141258, 4356941482887417⟩
  | 40 => ⟨3865460888569964, 4033577059158171, 4201693229746378, 4369809400334585, 4537925570922792⟩
  | 41 => ⟨4035415333079195, 4207208051509450, 4379000769939705, 4550793488369960, 4722586206800215⟩
  | 42 => ⟨4209046325430474, 4384515591702777, 4559984857975080, 4735454124247383, 4910923390519686⟩
  | 43 => ⟨4386353865623801, 4565499679738152, 4744645493852503, 4923791307966854, 5102937122081205⟩
  | 44 => ⟨4567337953659176, 4750160315615575, 4932982677571974, 5115805039528373, 5298627401484772⟩
  | 45 => ⟨4751998589536599, 4938497499335046, 5124996409133493, 5311495318931940, 5497994228730387⟩
  | 46 => ⟨4940335773256070, 5130511230896565, 5320686688537060, 5510862146177555, 5701037603818050⟩
  | 47 => ⟨5132349504817589, 5326201510300132, 5520053515782675, 5713905521265218, 5907757526747761⟩
  | 48 => ⟨5328039784221156, 5525568337545747, 5723096890870338, 5920625444194929, 6118153997519520⟩
  | 49 => ⟨5527406611466771, 5728611712633410, 5929816813800049, 6131021914966688, 6332227016133327⟩
  | 50 => ⟨5730449986554434, 5935331635563121, 6140213284571808, 6345094933580495, 6549976582589182⟩
  | 51 => ⟨5937169909484145, 6145728106334880, 6354286303185615, 6562844500036350, 6771402696887085⟩
  | 52 => ⟨6147566380255904, 6359801124948687, 6572035869641470, 6784270614334253, 6996505359027036⟩
  | 53 => ⟨6361639398869711, 6577550691404542, 6793461983939373, 7009373276474204, 7225284569009035⟩
  | 54 => ⟨6579388965325566, 6798976805702445, 7018564646079324, 7238152486456203, 7457740326833082⟩
  | 55 => ⟨6800815079623469, 7024079467842396, 7247343856061323, 7470608244280250, 7693872632499177⟩
  | 56 => ⟨7025917741763420, 7252858677824395, 7479799613885370, 7706740549946345, 7933681486007320⟩
  | 57 => ⟨7254696951745419, 7485314435648442, 7715931919551465, 7946549403454488, 8177166887357511⟩
  | 58 => ⟨7487152709569466, 7721446741314537, 7955740773059608, 8190034804804679, 8424328836549750⟩
  | 59 => ⟨7723285015235561, 7961255594822680, 8199226174409799, 8437196753996918, 8675167333584037⟩
  | 60 => ⟨7963093868743704, 8204740996172871, 8446388123602038, 8688035251031205, 8929682378460372⟩
  | 61 => ⟨8206579270093895, 8451902945365110, 8697226620636325, 8942550295907540, 9187873971178755⟩
  | 62 => ⟨8453741219286134, 8702741442399397, 8951741665512660, 9200741888625923, 9449742111739186⟩
  | 63 => ⟨8704579716320421, 8957256487275732, 9209933258231043, 9462610029186354, 9715286800141665⟩
  | 64 => ⟨8959094761196756, 9215448079994115, 9471801398791474, 9728154717588833, 9984508036386192⟩
  | 65 => ⟨9217286353915139, 9477316220554546, 9737346087193953, 9997375953833360, 10257405820472767⟩
  | 66 => ⟨9479154494475570, 9742860908957025, 10006567323438480, 10270273737919935, 10533980152401390⟩
  | 67 => ⟨9744699182878049, 10012082145201552, 10279465107525055, 10546848069848558, 10814231032172061⟩
  | 68 => ⟨10013920419122576, 10284979929288127, 10556039439453678, 10827098949619229, 11098158459784780⟩
  | 69 => ⟨10286818203209151, 10561554261216750, 10836290319224349, 11111026377231948, 11385762435239547⟩
  | 70 => ⟨10563392535137774, 10841805140987421, 11120217746837068, 11398630352686715, 11677042958536362⟩
  | 71 => ⟨10843643414908445, 11125732568600140, 11407821722291835, 11689910875983530, 11972000029675225⟩
  | 72 => ⟨11127570842521164, 11413336544054907, 11699102245588650, 11984867947122393, 12270633648656136⟩
  | 73 => ⟨11415174817975931, 11704617067351722, 11994059316727513, 12283501566103304, 12572943815479095⟩
  | 74 => ⟨11706455341272746, 11999574138490585, 12292692935708424, 12585811732926263, 12878930530144102⟩
  | 75 => ⟨12001412412411609, 12298207757471496, 12595003102531383, 12891798447591270, 13188593792651157⟩
  | 76 => ⟨12300046031392520, 12600517924294455, 12900989817196390, 13201461710098325, 13501933603000260⟩
  | 77 => ⟨12602356198215479, 12906504638959462, 13210653079703445, 13514801520447428, 13818949961191411⟩
  | 78 => ⟨12908342912880486, 13216167901466517, 13523992890052548, 13831817878638579, 14139642867224610⟩
  | 79 => ⟨13218006175387541, 13529507711815620, 13841009248243699, 14152510784671778, 14464012321099857⟩
  | 80 => ⟨13531345985736644, 13846524070006771, 14161702154276898, 14476880238547025, 14792058322817152⟩
  | 81 => ⟨13848362343927795, 14167216976039970, 14486071608152145, 14804926240264320, 15123780872376495⟩
  | 82 => ⟨14169055249960994, 14491586429915217, 14814117609869440, 15136648789823663, 15459179969777886⟩
  | 83 => ⟨14493424703836241, 14819632431632512, 15145840159428783, 15472047887225054, 15798255615021325⟩
  | 84 => ⟨14821470705553536, 15151354981191855, 15481239256830174, 15811123532468493, 16141007808106812⟩
  | 85 => ⟨15153193255112879, 15486754078593246, 15820314902073613, 16153875725553980, 16487436549034347⟩
  | 86 => ⟨15488592352514270, 15825829723836685, 16163067095159100, 16500304466481515, 16837541837803930⟩
  | 87 => ⟨15827667997757709, 16168581916922172, 16509495836086635, 16850409755251098, 17191323674415561⟩
  | 88 => ⟨16170420190843196, 16515010657849707, 16859601124856218, 17204191591862729, 17548782058869240⟩
  | 89 => ⟨16516848931770731, 16865115946619290, 17213382961467849, 17561649976316408, 17909916991164967⟩
  | 90 => ⟨16866954220540314, 17218897783230921, 17570841345921528, 17922784908612135, 18274728471302742⟩
  | 91 => ⟨17220736057151945, 17576356167684600, 17931976278217255, 18287596388749910, 18643216499282565⟩
  | 92 => ⟨17578194441605624, 17937491099980327, 18296787758355030, 18656084416729733, 19015381075104436⟩
  | 93 => ⟨17939329373901351, 18302302580118102, 18665275786334853, 19028248992551604, 19391222198768355⟩
  | 94 => ⟨18304140854039126, 18670790608097925, 19037440362156724, 19404090116215523, 19770739870274322⟩
  | 95 => ⟨18672628882018949, 19042955183919796, 19413281485820643, 19783607787721490, 20153934089622337⟩
  | 96 => ⟨19044793457840820, 19418796307583715, 19792799157326610, 20166802007069505, 20540804856812400⟩
  | 97 => ⟨19420634581504739, 19798313979089682, 20175993376674625, 20553672774259568, 20931352171844511⟩
  | 98 => ⟨19800152253010706, 20181508198437697, 20562864143864688, 20944220089291679, 21325576034718670⟩
  | 99 => ⟨20183346472358721, 20568378965627760, 20953411458896799, 21338443952165838, 21723476445434877⟩
  | 100 => ⟨20570217239548784, 20958926280659871, 21347635321770958, 21736344362882045, 22125053403993132⟩
  | 101 => ⟨20960764554580895, 21353150143534030, 21745535732487165, 22137921321440300, 22530306910393435⟩
  | 102 => ⟨21354988417455054, 21751050554250237, 22147112691045420, 22543174827840603, 22939236964635786⟩
  | 103 => ⟨21752888828171261, 22152627512808492, 22552366197445723, 22952104882082954, 23351843566720185⟩
  | 104 => ⟨22154465786729516, 22557881019208795, 22961296251688074, 23364711484167353, 23768126716646632⟩
  | 105 => ⟨22559719293129819, 22966811073451146, 23373902853772473, 23780994634093800, 24188086414415127⟩
  | 106 => ⟨22968649347372170, 23379417675535545, 23790186003698920, 24200954331862295, 24611722660025670⟩
  | 107 => ⟨23381255949456569, 23795700825461992, 24210145701467415, 24624590577472838, 25039035453478261⟩
  | 108 => ⟨23797539099383016, 24215660523230487, 24633781947077958, 25051903370925429, 25470024794772900⟩
  | 109 => ⟨24217498797151511, 24639296768841030, 25061094740530549, 25482892712220068, 25904690683909587⟩
  | 110 => ⟨24641135042762054, 25066609562293621, 25492084081825188, 25917558601356755, 26343033120888322⟩
  | 111 => ⟨25068447836214645, 25497598903588260, 25926749970961875, 26355901038335490, 26785052105709105⟩
  | 112 => ⟨25499437177509284, 25932264792724947, 26365092407940610, 26797920023156273, 27230747638371936⟩
  | 113 => ⟨25934103066645971, 26370607229703682, 26807111392761393, 27243615555819104, 27680119718876815⟩
  | 114 => ⟨26372445503624706, 26812626214524465, 27252806925424224, 27692987636323983, 28133168347223742⟩
  | 115 => ⟨26814464488445489, 27258321747187296, 27702179005929103, 28146036264670910, 28589893523412717⟩
  | _ => defaultCosts

def row13 : ℕ → Costs
  | 0 => ⟨150977930854751, 162522897318263, 197295230943657, 232067564569051, 266839898194445⟩
  | 1 => ⟨162522897318263, 198944510968233, 235366124618203, 271787738268173, 308209351918143⟩
  | 2 => ⟨162575632695723, 195363919299038, 228152205902353, 260940492505668, 293728779108983⟩
  | 3 => ⟨197356814402014, 234130891211281, 270904968020548, 307679044829815, 344453121639082⟩
  | 4 => ⟨236123786314257, 276883653329476, 317643520344695, 358403387359914, 399163254375133⟩
  | 5 => ⟨278876548432452, 323622205653623, 368367862874794, 413113520095965, 457859177317136⟩
  | 6 => ⟨325615100756599, 374346548183722, 423077995610845, 471809443037968, 520540890465091⟩
  | 7 => ⟨376339443286698, 429056680919773, 481773918552848, 534491156185923, 587208393818998⟩
  | 8 => ⟨431049576022749, 487752603861776, 544455631700803, 601158659539830, 657861687378857⟩
  | 9 => ⟨489745498964752, 550434317009731, 611123135054710, 671811953099689, 732500771144668⟩
  | 10 => ⟨552427212112707, 617101820363638, 681776428614569, 746451036865500, 811125645116431⟩
  | 11 => ⟨619094715466614, 687755113923497, 756415512380380, 825075910837263, 893736309294146⟩
  | 12 => ⟨689748009026473, 762394197689308, 835040386352143, 907686575014978, 980332763677813⟩
  | 13 => ⟨764387092792284, 841019071661071, 917651050529858, 994283029398645, 1070915008267432⟩
  | 14 => ⟨843011966764047, 923629735838786, 1004247504913525, 1084865273988264, 1165483043063003⟩
  | 15 => ⟨925622630941762, 1010226190222453, 1094829749503144, 1179433308783835, 1264036868064526⟩
  | 16 => ⟨1012219085325429, 1100808434812072, 1189397784298715, 1277987133785358, 1366576483272001⟩
  | 17 => ⟨1102801329915048, 1195376469607643, 1287951609300238, 1380526748992833, 1473101888685428⟩
  | 18 => ⟨1197369364710619, 1293930294609166, 1390491224507713, 1487052154406260, 1583613084304807⟩
  | 19 => ⟨1295923189712142, 1396469909816641, 1497016629921140, 1597563350025639, 1698110070130138⟩
  | 20 => ⟨1398462804919617, 1502995315230068, 1607527825540519, 1712060335850970, 1816592846161421⟩
  | 21 => ⟨1504988210333044, 1613506510849447, 1722024811365850, 1830543111882253, 1939061412398656⟩
  | 22 => ⟨1615499405952423, 1728003496674778, 1840507587397133, 1953011678119488, 2065515768841843⟩
  | 23 => ⟨1729996391777754, 1846486272706061, 1962976153634368, 2079466034562675, 2195955915490982⟩
  | 24 => ⟨1848479167809037, 1968954838943296, 2089430510077555, 2209906181211814, 2330381852346073⟩
  | 25 => ⟨1970947734046272, 2095409195386483, 2219870656726694, 2344332118066905, 2468793579407116⟩
  | 26 => ⟨2097402090489459, 2225849342035622, 2354296593581785, 2482743845127948, 2611191096674111⟩
  | 27 => ⟨2227842237138598, 2360275278890713, 2492708320642828, 2625141362394943, 2757574404147058⟩
  | 28 => ⟨2362268173993689, 2498687005951756, 2635105837909823, 2771524669867890, 2907943501825957⟩
  | 29 => ⟨2500679901054732, 2641084523218751, 2781489145382770, 2921893767546789, 3062298389710808⟩
  | 30 => ⟨2643077418321727, 2787467830691698, 2931858243061669, 3076248655431640, 3220639067801611⟩
  | 31 => ⟨2789460725794674, 2937836928370597, 3086213130946520, 3234589333522443, 3382965536098366⟩
  | 32 => ⟨2939829823473573, 3092191816255448, 3244553809037323, 3396915801819198, 3549277794601073⟩
  | 33 => ⟨3094184711358424, 3250532494346251, 3406880277334078, 3563228060321905, 3719575843309732⟩
  | 34 => ⟨3252525389449227, 3412858962643006, 3573192535836785, 3733526109030564, 3893859682224343⟩
  | 35 => ⟨3414851857745982, 3579171221145713, 3743490584545444, 3907809947945175, 4072129311344906⟩
  | 36 => ⟨3581164116248689, 3749469269854372, 3917774423460055, 4086079577065738, 4254384730671421⟩
  | 37 => ⟨3751462164957348, 3923753108768983, 4096044052580618, 4268334996392253, 4440625940203888⟩
  | 38 => ⟨3925746003871959, 4102022737889546, 4278299471907133, 4454576205924720, 4630852939942307⟩
  | 39 => ⟨4104015632992522, 4284278157216061, 4464540681439600, 4644803205663139, 4825065729886678⟩
  | 40 => ⟨4286271052319037, 4470519366748528, 4654767681178019, 4839015995607510, 5023264310037001⟩
  | 41 => ⟨4472512261851504, 4660746366486947, 4848980471122390, 5037214575757833, 5225448680393276⟩
  | 42 => ⟨4662739261589923, 4854959156431318, 5047179051272713, 5239398946114108, 5431618840955503⟩
  | 43 => ⟨4856952051534294, 5053157736581641, 5249363421628988, 5445569106676335, 5641774791723682⟩
  | 44 => ⟨5055150631684617, 5255342106937916, 5455533582191215, 5655725057444514, 5855916532697813⟩
  | 45 => ⟨5257335002040892, 5461512267500143, 5665689532959394, 5869866798418645, 6074044063877896⟩
  | 46 => ⟨5463505162603119, 5671668218268322, 5879831273933525, 6087994329598728, 6296157385263931⟩
  | 47 => ⟨5673661113371298, 5885809959242453, 6097958805113608, 6310107650984763, 6522256496855918⟩
  | 48 => ⟨5887802854345429, 6103937490422536, 6320072126499643, 6536206762576750, 6752341398653857⟩
  | 49 => ⟨6105930385525512, 6326050811808571, 6546171238091630, 6766291664374689, 6986412090657748⟩
  | 50 => ⟨6328043706911547, 6552149923400558, 6776256139889569, 7000362356378580, 7224468572867591⟩
  | 51 => ⟨6554142818503534, 6782234825198497, 7010326831893460, 7238418838588423, 7466510845283386⟩
  | 52 => ⟨6784227720301473, 7016305517202388, 7248383314103303, 7480461111004218, 7712538907905133⟩
  | 53 => ⟨7018298412305364, 7254361999412231, 7490425586519098, 7726489173625965, 7962552760732832⟩
  | 54 => ⟨7256354894515207, 7496404271828026, 7736453649140845, 7976503026453664, 8216552403766483⟩
  | 55 => ⟨7498397166931002, 7742432334449773, 7986467501968544, 8230502669487315, 8474537837006086⟩
  | 56 => ⟨7744425229552749, 7992446187277472, 8240467145002195, 8488488102726918, 8736509060451641⟩
  | 57 => ⟨7994439082380448, 8246445830311123, 8498452578241798, 8750459326172473, 9002466074103148⟩
  | 58 => ⟨8248438725414099, 8504431263550726, 8760423801687353, 9016416339823980, 9272408877960607⟩
  | 59 => ⟨8506424158653702, 8766402486996281, 9026380815338860, 9286359143681439, 9546337472024018⟩
  | 60 => ⟨8768395382099257, 9032359500647788, 9296323619196319, 9560287737744850, 9824251856293381⟩
  | 61 => ⟨9034352395750764, 9302302304505247, 9570252213259730, 9838202122014213, 10106152030768696⟩
  | 62 => ⟨9304295199608223, 9576230898568658, 9848166597529093, 10120102296489528, 10392037995449963⟩
  | 63 => ⟨9578223793671634, 9854145282838021, 10130066772004408, 10405988261170795, 10681909750337182⟩
  | 64 => ⟨9856138177940997, 10136045457313336, 10415952736685675, 10695860016058014, 10975767295430353⟩
  | 65 => ⟨10138038352416312, 10421931421994603, 10705824491572894, 10989717561151185, 11273610630729476⟩
  | 66 => ⟨10423924317097579, 10711803176881822, 10999682036666065, 11287560896450308, 11575439756234551⟩
  | 67 => ⟨10713796071984798, 11005660721974993, 11297525371965188, 11589390021955383, 11881254671945578⟩
  | 68 => ⟨11007653617077969, 11303504057274116, 11599354497470263, 11895204937666410, 12191055377862557⟩
  | 69 => ⟨11305496952377092, 11605333182779191, 11905169413181290, 12205005643583389, 12504841873985488⟩
  | 70 => ⟨11607326077882167, 11911148098490218, 12214970119098269, 12518792139706320, 12822614160314371⟩
  | 71 => ⟨11913140993593194, 12220948804407197, 12528756615221200, 12836564426035203, 13144372236849206⟩
  | 72 => ⟨12222941699510173, 12534735300530128, 12846528901550083, 13158322502570038, 13470116103589993⟩
  | 73 => ⟨12536728195633104, 12852507586859011, 13168286978084918, 13484066369310825, 13799845760536732⟩
  | 74 => ⟨12854500481961987, 13174265663393846, 13494030844825705, 13813796026257564, 14133561207689423⟩
  | 75 => ⟨13176258558496822, 13500009530134633, 13823760501772444, 14147511473410255, 14471262445048066⟩
  | 76 => ⟨13502002425237609, 13829739187081372, 14157475948925135, 14485212710768898, 14812949472612661⟩
  | 77 => ⟨13831732082184348, 14163454634234063, 14495177186283778, 14826899738333493, 15158622290383208⟩
  | 78 => ⟨14165447529337039, 14501155871592706, 14836864213848373, 15172572556104040, 15508280898359707⟩
  | 79 => ⟨14503148766695682, 14842842899157301, 15182537031618920, 15522231164080539, 15861925296542158⟩
  | 80 => ⟨14844835794260277, 15188515716927848, 15532195639595419, 15875875562262990, 16219555484930561⟩
  | 81 => ⟨15190508612030824, 15538174324904347, 15885840037777870, 16233505750651393, 16581171463524916⟩
  | 82 => ⟨15540167220007323, 15891818723086798, 16243470226166273, 16595121729245748, 16946773232325223⟩
  | 83 => ⟨15893811618189774, 16249448911475201, 16605086204760628, 16960723498046055, 17316360791331482⟩
  | 84 => ⟨16251441806578177, 16611064890069556, 16970687973560935, 17330311057052314, 17689934140543693⟩
  | 85 => ⟨16613057785172532, 16976666658869863, 17340275532567194, 17703884406264525, 18067493279961856⟩
  | 86 => ⟨16978659553972839, 17346254217876122, 17713848881779405, 18081443545682688, 18449038209585971⟩
  | 87 => ⟨17348247112979098, 17719827567088333, 18091408021197568, 18462988475306803, 18834568929416038⟩
  | 88 => ⟨17721820462191309, 18097386706506496, 18472952950821683, 18848519195136870, 19224085439452057⟩
  | 89 => ⟨18099379601609472, 18478931636130611, 18858483670651750, 19238035705172889, 19617587739694028⟩
  | 90 => ⟨18480924531233587, 18864462355960678, 19248000180687769, 19631538005414860, 20015075830141951⟩
  | 91 => ⟨18866455251063654, 19253978865996697, 19641502480929740, 20029026095862783, 20416549710795826⟩
  | 92 => ⟨19255971761099673, 19647481166238668, 20038990571377663, 20430499976516658, 20822009381655653⟩
  | 93 => ⟨19649474061341644, 20044969256686591, 20440464452031538, 20835959647376485, 21231454842721432⟩
  | 94 => ⟨20046962151789567, 20446443137340466, 20845924122891365, 21245405108442264, 21644886093993163⟩
  | 95 => ⟨20448436032443442, 20851902808200293, 21255369583957144, 21658836359713995, 22062303135470846⟩
  | 96 => ⟨20853895703303269, 21261348269266072, 21668800835228875, 22076253401191678, 22483705967154481⟩
  | 97 => ⟨21263341164369048, 21674779520537803, 22086217876706558, 22497656232875313, 22909094589044068⟩
  | 98 => ⟨21676772415640779, 22092196562015486, 22507620708390193, 22923044854764900, 23338469001139607⟩
  | 99 => ⟨22094189457118462, 22513599393699121, 22933009330279780, 23352419266860439, 23771829203441098⟩
  | 100 => ⟨22515592288802097, 22938988015588708, 23362383742375319, 23785779469161930, 24209175195948541⟩
  | 101 => ⟨22940980910691684, 23368362427684247, 23795743944676810, 24223125461669373, 24650506978661936⟩
  | 102 => ⟨23370355322787223, 23801722629985738, 24233089937184253, 24664457244382768, 25095824551581283⟩
  | 103 => ⟨23803715525088714, 24239068622493181, 24674421719897648, 25109774817302115, 25545127914706582⟩
  | 104 => ⟨24241061517596157, 24680400405206576, 25119739292816995, 25559078180427414, 25998417068037833⟩
  | 105 => ⟨24682393300309552, 25125717978125923, 25569042655942294, 26012367333758665, 26455692011575036⟩
  | 106 => ⟨25127710873228899, 25575021341251222, 26022331809273545, 26469642277295868, 26916952745318191⟩
  | 107 => ⟨25577014236354198, 26028310494582473, 26479606752810748, 26930903011039023, 27382199269267298⟩
  | 108 => ⟨26030303389685449, 26485585438119676, 26940867486553903, 27396149534988130, 27851431583422357⟩
  | 109 => ⟨26487578333222652, 26946846171862831, 27406114010503010, 27865381849143189, 28324649687783368⟩
  | 110 => ⟨26948839066965807, 27412092695811938, 27875346324658069, 28338599953504200, 28801853582350331⟩
  | 111 => ⟨27414085590914914, 27881325009966997, 28348564429019080, 28815803848071163, 29283043267123246⟩
  | 112 => ⟨27883317905069973, 28354543114328008, 28825768323586043, 29296993532844078, 29768218742102113⟩
  | 113 => ⟨28356536009430984, 28831747008894971, 29306958008358958, 29782169007822945, 30257380007286932⟩
  | 114 => ⟨28833739903997947, 29312936693667886, 29792133483337825, 30271330273007764, 30750527062677703⟩
  | _ => defaultCosts

def row14 : ℕ → Costs
  | 0 => ⟨188567785570710, 201968192586160, 242306847343078, 282645502099996, 322984156856914⟩
  | 1 => ⟨201968192586160, 244093567369702, 286218942153244, 328344316936786, 370469691720328⟩
  | 2 => ⟨198172872409576, 235651335389727, 273129798369878, 310608261350029, 348086724330180⟩
  | 3 => ⟨237798851674655, 279572347224662, 321345842774669, 363119338324676, 404892833874683⟩
  | 4 => ⟨281719863509590, 327788391629453, 373856919749316, 419925447869179, 465993975989042⟩
  | 5 => ⟨329935907914381, 380299468604100, 430663029293819, 481026589983538, 531390150673257⟩
  | 6 => ⟨382446984889028, 437105578148603, 491764171408178, 546422764667753, 601081357927328⟩
  | 7 => ⟨439253094433531, 498206720262962, 557160346092393, 616113971921824, 675067597751255⟩
  | 8 => ⟨500354236547890, 563602894947177, 626851553346464, 690100211745751, 753348870145038⟩
  | 9 => ⟨565750411232105, 633294102201248, 700837793170391, 768381484139534, 835925175108677⟩
  | 10 => ⟨635441618486176, 707280342025175, 779119065564174, 850957789103173, 922796512642172⟩
  | 11 => ⟨709427858310103, 785561614418958, 861695370527813, 937829126636668, 1013962882745523⟩
  | 12 => ⟨787709130703886, 868137919382597, 948566708061308, 1028995496740019, 1109424285418730⟩
  | 13 => ⟨870285435667525, 955009256916092, 1039733078164659, 1124456899413226, 1209180720661793⟩
  | 14 => ⟨957156773201020, 1046175627019443, 1135194480837866, 1224213334656289, 1313232188474712⟩
  | 15 => ⟨1048323143304371, 1141637029692650, 1234950916080929, 1328264802469208, 1421578688857487⟩
  | 16 => ⟨1143784545977578, 1241393464935713, 1339002383893848, 1436611302851983, 1534220221810118⟩
  | 17 => ⟨1243540981220641, 1345444932748632, 1447348884276623, 1549252835804614, 1651156787332605⟩
  | 18 => ⟨1347592449033560, 1453791433131407, 1559990417229254, 1666189401327101, 1772388385424948⟩
  | 19 => ⟨1455938949416335, 1566432966084038, 1676926982751741, 1787420999419444, 1897915016087147⟩
  | 20 => ⟨1568580482368966, 1683369531606525, 1798158580844084, 1912947630081643, 2027736679319202⟩
  | 21 => ⟨1685517047891453, 1804601129698868, 1923685211506283, 2042769293313698, 2161853375121113⟩
  | 22 => ⟨1806748645983796, 1930127760361067, 2053506874738338, 2176885989115609, 2300265103492880⟩
  | 23 => ⟨1932275276645995, 2059949423593122, 2187623570540249, 2315297717487376, 2442971864434503⟩
  | 24 => ⟨2062096939878050, 2194066119395033, 2326035298912016, 2458004478428999, 2589973657945982⟩
  | 25 => ⟨2196213635679961, 2332477847766800, 2468742059853639, 2605006271940478, 2741270484027317⟩
  | 26 => ⟨2334625364051728, 2475184608708423, 2615743853365118, 2756303098021813, 2896862342678508⟩
  | 27 => ⟨2477332124993351, 2622186402219902, 2767040679446453, 2911894956673004, 3056749233899555⟩
  | 28 => ⟨2624333918504830, 2773483228301237, 2922632538097644, 3071781847894051, 3220931157690458⟩
  | 29 => ⟨2775630744586165, 2929075086952428, 3082519429318691, 3235963771684954, 3389408114051217⟩
  | 30 => ⟨2931222603237356, 3088961978173475, 3246701353109594, 3404440728045713, 3562180102981832⟩
  | 31 => ⟨3091109494458403, 3253143901964378, 3415178309470353, 3577212716976328, 3739247124482303⟩
  | 32 => ⟨3255291418249306, 3421620858325137, 3587950298400968, 3754279738476799, 3920609178552630⟩
  | 33 => ⟨3423768374610065, 3594392847255752, 3765017319901439, 3935641792547126, 4106266265192813⟩
  | 34 => ⟨3596540363540680, 3771459868756223, 3946379373971766, 4121298879187309, 4296218384402852⟩
  | 35 => ⟨3773607385041151, 3952821922826550, 4132036460611949, 4311250998397348, 4490465536182747⟩
  | 36 => ⟨3954969439111478, 4138479009466733, 4321988579821988, 4505498150177243, 4689007720532498⟩
  | 37 => ⟨4140626525751661, 4328431128676772, 4516235731601883, 4704040334526994, 4891844937452105⟩
  | 38 => ⟨4330578644961700, 4522678280456667, 4714777915951634, 4906877551446601, 5098977186941568⟩
  | 39 => ⟨4524825796741595, 4721220464806418, 4917615132871241, 5114009800936064, 5310404469000887⟩
  | 40 => ⟨4723367981091346, 4924057681726025, 5124747382360704, 5325437082995383, 5526126783630062⟩
  | 41 => ⟨4926205198010953, 5131189931215488, 5336174664420023, 5541159397624558, 5746144130829093⟩
  | 42 => ⟨5133337447500416, 5342617213274807, 5551896979049198, 5761176744823589, 5970456510597980⟩
  | 43 => ⟨5344764729559735, 5558339527903982, 5771914326248229, 5985489124592476, 6199063922936723⟩
  | 44 => ⟨5560487044188910, 5778356875103013, 5996226706017116, 6214096536931219, 6431966367845322⟩
  | 45 => ⟨5780504391387941, 6002669254871900, 6224834118355859, 6446998981839818, 6669163845323777⟩
  | 46 => ⟨6004816771156828, 6231276667210643, 6457736563264458, 6684196459318273, 6910656355372088⟩
  | 47 => ⟨6233424183495571, 6464179112119242, 6694934040742913, 6925688969366584, 7156443897990255⟩
  | 48 => ⟨6466326628404170, 6701376589597697, 6936426550791224, 7171476511984751, 7406526473178278⟩
  | 49 => ⟨6703524105882625, 6942869099646008, 7182214093409391, 7421559087172774, 7660904080936157⟩
  | 50 => ⟨6945016615930936, 7188656642264175, 7432296668597414, 7675936694930653, 7919576721263892⟩
  | 51 => ⟨7190804158549103, 7438739217452198, 7686674276355293, 7934609335258388, 8182544394161483⟩
  | 52 => ⟨7440886733737126, 7693116825210077, 7945346916683028, 8197577008155979, 8449807099628930⟩
  | 53 => ⟨7695264341495005, 7951789465537812, 8208314589580619, 8464839713623426, 8721364837666233⟩
  | 54 => ⟨7953936981822740, 8214757138435403, 8475577295048066, 8736397451660729, 8997217608273392⟩
  | 55 => ⟨8216904654720331, 8482019843902850, 8747135033085369, 9012250222267888, 9277365411450407⟩
  | 56 => ⟨8484167360187778, 8753577581940153, 9022987803692528, 9292398025444903, 9561808247197278⟩
  | 57 => ⟨8755725098225081, 9029430352547312, 9303135606869543, 9576840861191774, 9850546115514005⟩
  | 58 => ⟨9031577868832240, 9309578155724327, 9587578442616414, 9865578729508501, 10143579016400588⟩
  | 59 => ⟨9311725672009255, 9594020991471198, 9876316310933141, 10158611630395084, 10440906949857027⟩
  | 60 => ⟨9596168507756126, 9882758859787925, 10169349211819724, 10455939563851523, 10742529915883322⟩
  | 61 => ⟨9884906376072853, 10175791760674508, 10466677145276163, 10757562529877818, 11048447914479473⟩
  | 62 => ⟨10177939276959436, 10473119694130947, 10768300111302458, 11063480528473969, 11358660945645480⟩
  | 63 => ⟨10475267210415875, 10774742660157242, 11074218109898609, 11373693559639976, 11673169009381343⟩
  | 64 => ⟨10776890176442170, 11080660658753393, 11384431141064616, 11688201623375839, 11991972105687062⟩
  | 65 => ⟨11082808175038321, 11390873689919400, 11698939204800479, 12007004719681558, 12315070234562637⟩
  | 66 => ⟨11393021206204328, 11705381753655263, 12017742301106198, 12330102848557133, 12642463396008068⟩
  | 67 => ⟨11707529269940191, 12024184849960982, 12340840429981773, 12657496010002564, 12974151590023355⟩
  | 68 => ⟨12026332366245910, 12347282978836557, 12668233591427204, 12989184204017851, 13310134816608498⟩
  | 69 => ⟨12349430495121485, 12674676140281988, 12999921785442491, 13325167430602994, 13650413075763497⟩
  | 70 => ⟨12676823656566916, 13006364334297275, 13335905012027634, 13665445689757993, 13994986367488352⟩
  | 71 => ⟨13008511850582203, 13342347560882418, 13676183271182633, 14010018981482848, 14343854691783063⟩
  | 72 => ⟨13344495077167346, 13682625820037417, 14020756562907488, 14358887305777559, 14697018048647630⟩
  | 73 => ⟨13684773336322345, 14027199111762272, 14369624887202199, 14712050662642126, 15054476438082053⟩
  | 74 => ⟨14029346628047200, 14376067436056983, 14722788244066766, 15069509052076549, 15416229860086332⟩
  | 75 => ⟨14378214952341911, 14729230792921550, 15080246633501189, 15431262474080828, 15782278314660467⟩
  | 76 => ⟨14731378309206478, 15086689182355973, 15442000055505468, 15797310928654963, 16152621801804458⟩
  | 77 => ⟨15088836698640901, 15448442604360252, 15808048510079603, 16167654415798954, 16527260321518305⟩
  | 78 => ⟨15450590120645180, 15814491058934387, 16178391997223594, 16542292935512801, 16906193873802008⟩
  | 79 => ⟨15816638575219315, 16184834546078378, 16553030516937441, 16921226487796504, 17289422458655567⟩
  | 80 => ⟨16186982062363306, 16559473065792225, 16931964069221144, 17304455072650063, 17676946076078982⟩
  | 81 => ⟨16561620582077153, 16938406618075928, 17315192654074703, 17691978690073478, 18068764726072253⟩
  | 82 => ⟨16940554134360856, 17321635202929487, 17702716271498118, 18083797340066749, 18464878408635380⟩
  | 83 => ⟨17323782719214415, 17709158820352902, 18094534921491389, 18479911022629876, 18865287123768363⟩
  | 84 => ⟨17711306336637830, 18100977470346173, 18490648604054516, 18880319737762859, 19269990871471202⟩
  | 85 => ⟨18103124986631101, 18497091152909300, 18891057319187499, 19285023485465698, 19678989651743897⟩
  | 86 => ⟨18499238669194228, 18897499868042283, 19295761066890338, 19694022265738393, 20092283464586448⟩
  | 87 => ⟨18899647384327211, 19302203615745122, 19704759847163033, 20107316078580944, 20509872309998855⟩
  | 88 => ⟨19304351132030050, 19711202396017817, 20118053660005584, 20524904923993351, 20931756187981118⟩
  | 89 => ⟨19713349912302745, 20124496208860368, 20535642505417991, 20946788801975614, 21357935098533237⟩
  | 90 => ⟨20126643725145296, 20542085054272775, 20957526383400254, 21372967712527733, 21788409041655212⟩
  | 91 => ⟨20544232570557703, 20963968932255038, 21383705293952373, 21803441655649708, 22223178017347043⟩
  | 92 => ⟨20966116448539966, 21390147842807157, 21814179237074348, 22238210631341539, 22662242025608730⟩
  | 93 => ⟨21392295359092085, 21820621785929132, 22248948212766179, 22677274639603226, 23105601066440273⟩
  | 94 => ⟨21822769302214060, 22255390761620963, 22688012221027866, 23120633680434769, 23553255139841672⟩
  | 95 => ⟨22257538277905891, 22694454769882650, 23131371261859409, 23568287753836168, 24005204245812927⟩
  | 96 => ⟨22696602286167578, 23137813810714193, 23579025335260808, 24020236859807423, 24461448384354038⟩
  | 97 => ⟨23139961326999121, 23585467884115592, 24030974441232063, 24476480998348534, 24921987555465005⟩
  | 98 => ⟨23587615400400520, 24037416990086847, 24487218579773174, 24937020169459501, 25386821759145828⟩
  | 99 => ⟨24039564506371775, 24493661128627958, 24947757750884141, 25401854373140324, 25855950995396507⟩
  | 100 => ⟨24495808644912886, 24954200299738925, 25412591954564964, 25870983609391003, 26329375264217042⟩
  | 101 => ⟨24956347816023853, 25419034503419748, 25881721190815643, 26344407878211538, 26807094565607433⟩
  | 102 => ⟨25421182019704676, 25888163739670427, 26355145459636178, 26822127179601929, 27289108899567680⟩
  | 103 => ⟨25890311255955355, 26361588008490962, 26832864761026569, 27304141513562176, 27775418266097783⟩
  | 104 => ⟨26363735524775890, 26839307309881353, 27314879094986816, 27790450880092279, 28266022665197742⟩
  | 105 => ⟨26841454826166281, 27321321643841600, 27801188461516919, 28281055279192238, 28760922096867557⟩
  | 106 => ⟨27323469160126528, 27807631010371703, 28291792860616878, 28775954710862053, 29260116561107228⟩
  | 107 => ⟨27809778526656631, 28298235409471662, 28786692292286693, 29275149175101724, 29763606057916755⟩
  | 108 => ⟨28300382925756590, 28793134841141477, 29285886756526364, 29778638671911251, 30271390587296138⟩
  | 109 => ⟨28795282357426405, 29292329305381148, 29789376253335891, 30286423201290634, 30783470149245377⟩
  | 110 => ⟨29294476821666076, 29795818802190675, 30297160782715274, 30798502763239873, 31299844743764472⟩
  | 111 => ⟨29797966318475603, 30303603331570058, 30809240344664513, 31314877357758968, 31820514370853423⟩
  | 112 => ⟨30305750847854986, 30815682893519297, 31325614939183608, 31835546984847919, 32345479030512230⟩
  | 113 => ⟨30817830409804225, 31332057488038392, 31846284566272559, 32360511644506726, 32874738722740893⟩
  | _ => defaultCosts

def row15 : ℕ → Costs
  | 0 => ⟨231930121421265, 247323408990701, 293640704885287, 339958000779873, 386275296674459⟩
  | 1 => ⟨247323408990701, 295564864913959, 343806320837217, 392047776760475, 440289232683733⟩
  | 2 => ⟨238614909682217, 281092791403108, 323570673123999, 366048554844890, 408526436565781⟩
  | 3 => ⟨283394928869988, 330477085524639, 377559242179290, 424641398833941, 471723555488592⟩
  | 4 => ⟨332779222991519, 384465654579930, 436152086168341, 487838517756752, 539524949345163⟩
  | 5 => ⟨386767792046810, 443058498568981, 499349205091152, 555639911613323, 611930618135494⟩
  | 6 => ⟨445360636035861, 506255617491792, 567150598947723, 628045580403654, 688940561859585⟩
  | 7 => ⟨508557754958672, 574057011348363, 639556267738054, 705055524127745, 770554780517436⟩
  | 8 => ⟨576359148815243, 646462680138694, 716566211462145, 786669742785596, 856773274109047⟩
  | 9 => ⟨648764817605574, 723472623862785, 798180430119996, 872888236377207, 947596042634418⟩
  | 10 => ⟨725774761329665, 805086842520636, 884398923711607, 963711004902578, 1043023086093549⟩
  | 11 => ⟨807388979987516, 891305336112247, 975221692236978, 1059138048361709, 1143054404486440⟩
  | 12 => ⟨893607473579127, 982128104637618, 1070648735696109, 1159169366754600, 1247689997813091⟩
  | 13 => ⟨984430242104498, 1077555148096749, 1170680054089000, 1263804960081251, 1356929866073502⟩
  | 14 => ⟨1079857285563629, 1177586466489640, 1275315647415651, 1373044828341662, 1470774009267673⟩
  | 15 => ⟨1179888603956520, 1282222059816291, 1384555515676062, 1486888971535833, 1589222427395604⟩
  | 16 => ⟨1284524197283171, 1391461928076702, 1498399658870233, 1605337389663764, 1712275120457295⟩
  | 17 => ⟨1393764065543582, 1505306071270873, 1616848076998164, 1728390082725455, 1839932088452746⟩
  | 18 => ⟨1507608208737753, 1623754489398804, 1739900770059855, 1856047050720906, 1972193331381957⟩
  | 19 => ⟨1626056626865684, 1746807182460495, 1867557738055306, 1988308293650117, 2109058849244928⟩
  | 20 => ⟨1749109319927375, 1874464150455946, 1999818980984517, 2125173811513088, 2250528642041659⟩
  | 21 => ⟨1876766287922826, 2006725393385157, 2136684498847488, 2266643604309819, 2396602709772150⟩
  | 22 => ⟨2009027530852037, 2143590911248128, 2278154291644219, 2412717672040310, 2547281052436401⟩
  | 23 => ⟨2145893048715008, 2285060704044859, 2424228359374710, 2563396014704561, 2702563670034412⟩
  | 24 => ⟨2287362841511739, 2431134771775350, 2574906702038961, 2718678632302572, 2862450562566183⟩
  | 25 => ⟨2433436909242230, 2581813114439601, 2730189319636972, 2878565524834343, 3026941730031714⟩
  | 26 => ⟨2584115251906481, 2737095732037612, 2890076212168743, 3043056692299874, 3196037172431005⟩
  | 27 => ⟨2739397869504492, 2896982624569383, 3054567379634274, 3212152134699165, 3369736889764056⟩
  | 28 => ⟨2899284762036263, 3061473792034914, 3223662822033565, 3385851852032216, 3548040882030867⟩
  | 29 => ⟨3063775929501794, 3230569234434205, 3397362539366616, 3564155844299027, 3730949149231438⟩
  | 30 => ⟨3232871371901085, 3404268951767256, 3575666531633427, 3747064111499598, 3918461691365769⟩
  | 31 => ⟨3406571089234136, 3582572944034067, 3758574798833998, 3934576653633929, 4110578508433860⟩
  | 32 => ⟨3584875081500947, 3765481211234638, 3946087340968329, 4126693470702020, 4307299600435711⟩
  | 33 => ⟨3767783348701518, 3952993753368969, 4138204158036420, 4323414562703871, 4508624967371322⟩
  | 34 => ⟨3955295890835849, 4145110570437060, 4334925250038271, 4524739929639482, 4714554609240693⟩
  | 35 => ⟨4147412707903940, 4341831662438911, 4536250616973882, 4730669571508853, 4925088526043824⟩
  | 36 => ⟨4344133799905791, 4543157029374522, 4742180258843253, 4941203488311984, 5140226717780715⟩
  | 37 => ⟨4545459166841402, 4749086671243893, 4952714175646384, 5156341680048875, 5359969184451366⟩
  | 38 => ⟨4751388808710773, 4959620588047024, 5167852367383275, 5376084146719526, 5584315926055777⟩
  | 39 => ⟨4961922725513904, 5174758779783915, 5387594834053926, 5600430888323937, 5813266942593948⟩
  | 40 => ⟨5177060917250795, 5394501246454566, 5611941575658337, 5829381904862108, 6046822234065879⟩
  | 41 => ⟨5396803383921446, 5618847988058977, 5840892592196508, 6062937196334039, 6284981800471570⟩
  | 42 => ⟨5621150125525857, 5847799004597148, 6074447883668439, 6301096762739730, 6527745641811021⟩
  | 43 => ⟨5850101142064028, 6081354296069079, 6312607450074130, 6543860604079181, 6775113758084232⟩
  | 44 => ⟨6083656433535959, 6319513862474770, 6555371291413581, 6791228720352392, 7027086149291203⟩
  | 45 => ⟨6321815999941650, 6562277703814221, 6802739407686792, 7043201111559363, 7283662815431934⟩
  | 46 => ⟨6564579841281101, 6809645820087432, 7054711798893763, 7299777777700094, 7544843756506425⟩
  | 47 => ⟨6811947957554312, 7061618211294403, 7311288465034494, 7560958718774585, 7810628972514676⟩
  | 48 => ⟨7063920348761283, 7318194877435134, 7572469406108985, 7826743934782836, 8081018463456687⟩
  | 49 => ⟨7320497014902014, 7579375818509625, 7838254622117236, 8097133425724847, 8356012229332458⟩
  | 50 => ⟨7581677955976505, 7845161034517876, 8108644113059247, 8372127191600618, 8635610270141989⟩
  | 51 => ⟨7847463171984756, 8115550525459887, 8383637878935018, 8651725232410149, 8919812585885280⟩
  | 52 => ⟨8117852662926767, 8390544291335658, 8663235919744549, 8935927548153440, 9208619176562331⟩
  | 53 => ⟨8392846428802538, 8670142332145189, 8947438235487840, 9224734138830491, 9502030042173142⟩
  | 54 => ⟨8672444469612069, 8954344647888480, 9236244826164891, 9518145004441302, 9800045182717713⟩
  | 55 => ⟨8956646785355360, 9243151238565531, 9529655691775702, 9816160144985873, 10102664598196044⟩
  | 56 => ⟨9245453376032411, 9536562104176342, 9827670832320273, 10118779560464204, 10409888288608135⟩
  | 57 => ⟨9538864241643222, 9834577244720913, 10130290247798604, 10426003250876295, 10721716253953986⟩
  | 58 => ⟨9836879382187793, 10137196660199244, 10437513938210695, 10737831216222146, 11038148494233597⟩
  | 59 => ⟨10139498797666124, 10444420350611335, 10749341903556546, 11054263456501757, 11359185009446968⟩
  | 60 => ⟨10446722488078215, 10756248315957186, 11065774143836157, 11375299971715128, 11684825799594099⟩
  | 61 => ⟨10758550453424066, 11072680556236797, 11386810659049528, 11700940761862259, 12015070864674990⟩
  | 62 => ⟨11074982693703677, 11393717071450168, 11712451449196659, 12031185826943150, 12349920204689641⟩
  | 63 => ⟨11396019208917048, 11719357861597299, 12042696514277550, 12366035166957801, 12689373819638052⟩
  | 64 => ⟨11721659999064179, 12049602926678190, 12377545854292201, 12705488781906212, 13033431709520223⟩
  | 65 => ⟨12051905064145070, 12384452266692841, 12716999469240612, 13049546671788383, 13382093874336154⟩
  | 66 => ⟨12386754404159721, 12723905881641252, 13061057359122783, 13398208836604314, 13735360314085845⟩
  | 67 => ⟨12726208019108132, 13067963771523423, 13409719523938714, 13751475276354005, 14093231028769296⟩
  | 68 => ⟨13070265908990303, 13416625936339354, 13762985963688405, 14109345991037456, 14455706018386507⟩
  | 69 => ⟨13418928073806234, 13769892376089045, 14120856678371856, 14471820980654667, 14822785282937478⟩
  | 70 => ⟨13772194513555925, 14127763090772496, 14483331667989067, 14838900245205638, 15194468822422209⟩
  | 71 => ⟨14130065228239376, 14490238080389707, 14850410932540038, 15210583784690369, 15570756636840700⟩
  | 72 => ⟨14492540217856587, 14857317344940678, 15222094472024769, 15586871599108860, 15951648726192951⟩
  | 73 => ⟨14859619482407558, 15229000884425409, 15598382286443260, 15967763688461111, 16337145090478962⟩
  | 74 => ⟨15231303021892289, 15605288698843900, 15979274375795511, 16353260052747122, 16727245729698733⟩
  | 75 => ⟨15607590836310780, 15986180788196151, 16364770740081522, 16743360691966893, 17121950643852264⟩
  | 76 => ⟨15988482925663031, 16371677152482162, 16754871379301293, 17138065606120424, 17521259832939555⟩
  | 77 => ⟨16373979289949042, 16761777791701933, 17149576293454824, 17537374795207715, 17925173296960606⟩
  | 78 => ⟨16764079929168813, 17156482705855464, 17548885482542115, 17941288259228766, 18333691035915417⟩
  | 79 => ⟨17158784843322344, 17555791894942755, 17952798946563166, 18349805998183577, 18746813049803988⟩
  | 80 => ⟨17558094032409635, 17959705358963806, 18361316685517977, 18762928012072148, 19164539338626319⟩
  | 81 => ⟨17962007496430686, 18368223097918617, 18774438699406548, 19180654300894479, 19586869902382410⟩
  | 82 => ⟨18370525235385497, 18781345111807188, 19192164988228879, 19602984864650570, 20013804741072261⟩
  | 83 => ⟨18783647249274068, 19199071400629519, 19614495551984970, 20029919703340421, 20445343854695872⟩
  | 84 => ⟨19201373538096399, 19621401964385610, 20041430390674821, 20461458816964032, 20881487243253243⟩
  | 85 => ⟨19623704101852490, 20048336803075461, 20472969504298432, 20897602205521403, 21322234906744374⟩
  | 86 => ⟨20050638940542341, 20479875916699072, 20909112892855803, 21338349869012534, 21767586845169265⟩
  | 87 => ⟨20482178054165952, 20916019305256443, 21349860556346934, 21783701807437425, 22217543058527916⟩
  | 88 => ⟨20918321442723323, 21356766968747574, 21795212494771825, 22233658020796076, 22672103546820327⟩
  | 89 => ⟨21359069106214454, 21802118907172465, 22245168708130476, 22688218509088487, 23131268310046498⟩
  | 90 => ⟨21804421044639345, 22252075120531116, 22699729196422887, 23147383272314658, 23595037348206429⟩
  | 91 => ⟨22254377257997996, 22706635608823527, 23158893959649058, 23611152310474589, 24063410661300120⟩
  | 92 => ⟨22708937746290407, 23165800372049698, 23622662997808989, 24079525623568280, 24536388249327571⟩
  | 93 => ⟨23168102509516578, 23629569410209629, 24091036310902680, 24552503211595731, 25013970112288782⟩
  | 94 => ⟨23631871547676509, 24097942723303320, 24564013898930131, 25030085074556942, 25496156250183753⟩
  | 95 => ⟨24100244860770200, 24570920311330771, 25041595761891342, 25512271212451913, 25982946663012484⟩
  | 96 => ⟨24573222448797651, 25048502174291982, 25523781899786313, 25999061625280644, 26474341350774975⟩
  | 97 => ⟨25050804311758862, 25530688312186953, 26010572312615044, 26490456313043135, 26970340313471226⟩
  | 98 => ⟨25532990449653833, 26017478725015684, 26501967000377535, 26986455275739386, 27470943551101237⟩
  | 99 => ⟨26019780862482564, 26508873412778175, 26997965963073786, 27487058513369397, 27976151063665008⟩
  | 100 => ⟨26511175550245055, 27004872375474426, 27498569200703797, 27992266025933168, 28485962851162539⟩
  | 101 => ⟨27007174512941306, 27505475613104437, 28003776713267568, 28502077813430699, 29000378913593830⟩
  | 102 => ⟨27507777750571317, 28010683125668208, 28513588500765099, 29016493875861990, 29519399250958881⟩
  | 103 => ⟨28012985263135088, 28520494913165739, 29028004563196390, 29535514213227041, 30043023863257692⟩
  | 104 => ⟨28522797050632619, 29034910975597030, 29547024900561441, 30059138825525852, 30571252750490263⟩
  | 105 => ⟨29037213113063910, 29553931312962081, 30070649512860252, 30587367712758423, 31104085912656594⟩
  | 106 => ⟨29556233450428961, 30077555925260892, 30598878400092823, 31120200874924754, 31641523349756685⟩
  | 107 => ⟨30079858062727772, 30605784812493463, 31131711562259154, 31657638312024845, 32183565061790536⟩
  | 108 => ⟨30608086949960343, 31138617974659794, 31669148999359245, 32199680024058696, 32730211048758147⟩
  | 109 => ⟨31140920112126674, 31676055411759885, 32211190711393096, 32746326011026307, 33281461310659518⟩
  | 110 => ⟨31678357549226765, 32218097123793736, 32757836698360707, 33297576272927678, 33837315847494649⟩
  | 111 => ⟨32220399261260616, 32764743110761347, 33309086960262078, 33853430809762809, 34397774659263540⟩
  | 112 => ⟨32767045248228227, 33315993372662718, 33864941497097209, 34413889621531700, 34962837745966191⟩
  | _ => defaultCosts

def row16 : ℕ → Costs
  | 0 => ⟨281477258412560, 299000866538030, 351709123576428, 404417380614826, 457125637653224⟩
  | 1 => ⟨299000866538030, 353770723607148, 408540580676266, 463310437745384, 518080294814502⟩
  | 2 => ⟨284210986877550, 331997529703085, 379784072528620, 427570615354155, 475357158179690⟩
  | 3 => ⟨334454288351917, 387154348475116, 439854408598315, 492554468721514, 545254528844713⟩
  | 4 => ⟨389611107123948, 447224684544811, 504838261965674, 562451839386537, 620065416807400⟩
  | 5 => ⟨449681443193643, 512208537912170, 574735632630697, 637262727349224, 699789822067751⟩
  | 6 => ⟨514665296561002, 582105908577193, 649546520593384, 716987132609575, 784427744625766⟩
  | 7 => ⟨584562667226025, 656916796539880, 729270925853735, 801625055167590, 873979184481445⟩
  | 8 => ⟨659373555188712, 736641201800231, 813908848411750, 891176495023269, 968444141634788⟩
  | 9 => ⟨739097960449063, 821279124358246, 903460288267429, 985641452176612, 1067822616085795⟩
  | 10 => ⟨823735883007078, 910830564213925, 997925245420772, 1085019926627619, 1172114607834466⟩
  | 11 => ⟨913287322862757, 1005295521367268, 1097303719871779, 1189311918376290, 1281320116880801⟩
  | 12 => ⟨1007752280016100, 1104673995818275, 1201595711620450, 1298517427422625, 1395439143224800⟩
  | 13 => ⟨1107130754467107, 1208965987566946, 1310801220666785, 1412636453766624, 1514471686866463⟩
  | 14 => ⟨1211422746215778, 1318171496613281, 1424920247010784, 1531668997408287, 1638417747805790⟩
  | 15 => ⟨1320628255262113, 1432290522957280, 1543952790652447, 1655615058347614, 1767277326042781⟩
  | 16 => ⟨1434747281606112, 1551323066598943, 1667898851591774, 1784474636584605, 1901050421577436⟩
  | 17 => ⟨1553779825247775, 1675269127538270, 1796758429828765, 1918247732119260, 2039737034409755⟩
  | 18 => ⟨1677725886187102, 1804128705775261, 1930531525363420, 2056934344951579, 2183337164539738⟩
  | 19 => ⟨1806585464424093, 1937901801309916, 2069218138195739, 2200534475081562, 2331850811967385⟩
  | 20 => ⟨1940358559958748, 2076588414142235, 2212818268325722, 2349048122509209, 2485277976692696⟩
  | 21 => ⟨2079045172791067, 2220188544272218, 2361331915753369, 2502475287234520, 2643618658715671⟩
  | 22 => ⟨2222645302921050, 2368702191699865, 2514759080478680, 2660815969257495, 2806872858036310⟩
  | 23 => ⟨2371158950348697, 2522129356425176, 2673099762501655, 2824070168578134, 2975040574654613⟩
  | 24 => ⟨2524586115074008, 2680470038448151, 2836353961822294, 2992237885196437, 3148121808570580⟩
  | 25 => ⟨2682926797096983, 2843724237768790, 3004521678440597, 3165319119112404, 3326116559784211⟩
  | 26 => ⟨2846180996417622, 3011891954387093, 3177602912356564, 3343313870326035, 3509024828295506⟩
  | 27 => ⟨3014348713035925, 3184973188303060, 3355597663570195, 3526222138837330, 3696846614104465⟩
  | 28 => ⟨3187429946951892, 3362967939516691, 3538505932081490, 3714043924646289, 3889581917211088⟩
  | 29 => ⟨3365424698165523, 3545876208027986, 3726327717890449, 3906779227752912, 4087230737615375⟩
  | 30 => ⟨3548332966676818, 3733697993836945, 3919063020997072, 4104428048157199, 4289793075317326⟩
  | 31 => ⟨3736154752485777, 3926433296943568, 4116711841401359, 4306990385859150, 4497268930316941⟩
  | 32 => ⟨3928890055592400, 4124082117347855, 4319274179103310, 4514466240858765, 4709658302614220⟩
  | 33 => ⟨4126538875996687, 4326644455049806, 4526750034102925, 4726855613156044, 4926961192209163⟩
  | 34 => ⟨4329101213698638, 4534120310049421, 4739139406400204, 4944158502750987, 5149177599101770⟩
  | 35 => ⟨4536577068698253, 4746509682346700, 4956442295995147, 5166374909643594, 5376307523292041⟩
  | 36 => ⟨4748966440995532, 4963812571941643, 5178658702887754, 5393504833833865, 5608350964779976⟩
  | 37 => ⟨4966269330590475, 5186028978834250, 5405788627078025, 5625548275321800, 5845307923565575⟩
  | 38 => ⟨5188485737483082, 5413158903024521, 5637832068565960, 5862505234107399, 6087178399648838⟩
  | 39 => ⟨5415615661673353, 5645202344512456, 5874789027351559, 6104375710190662, 6333962393029765⟩
  | 40 => ⟨5647659103161288, 5882159303298055, 6116659503434822, 6351159703571589, 6585659903708356⟩
  | 41 => ⟨5884616061946887, 6124029779381318, 6363443496815749, 6602857214250180, 6842270931684611⟩
  | 42 => ⟨6126486538030150, 6370813772762245, 6615141007494340, 6859468242226435, 7103795476958530⟩
  | 43 => ⟨6373270531411077, 6622511283440836, 6871752035470595, 7120992787500354, 7370233539530113⟩
  | 44 => ⟨6624968042089668, 6879122311417091, 7133276580744514, 7387430850071937, 7641585119399360⟩
  | 45 => ⟨6881579070065923, 7140646856691010, 7399714643316097, 7658782429941184, 7917850216566271⟩
  | 46 => ⟨7143103615339842, 7407084919262593, 7671066223185344, 7935047527108095, 8199028831030846⟩
  | 47 => ⟨7409541677911425, 7678436499131840, 7947331320352255, 8216226141572670, 8485120962793085⟩
  | 48 => ⟨7680893257780672, 7954701596298751, 8228509934816830, 8502318273334909, 8776126611852988⟩
  | 49 => ⟨7957158354947583, 8235880210763326, 8514602066579069, 8793323922394812, 9072045778210555⟩
  | 50 => ⟨8238336969412158, 8521972342525565, 8805607715638972, 9089243088752379, 9372878461865786⟩
  | 51 => ⟨8524429101174397, 8812977991585468, 9101526881996539, 9390075772407610, 9678624662818681⟩
  | 52 => ⟨8815434750234300, 9108897157943035, 9402359565651770, 9695821973360505, 9989284381069240⟩
  | 53 => ⟨9111353916591867, 9409729841598266, 9708105766604665, 10006481691611064, 10304857616617463⟩
  | 54 => ⟨9412186600247098, 9715476042551161, 10018765484855224, 10322054927159287, 10625344369463350⟩
  | 55 => ⟨9717932801199993, 10026135760801720, 10334338720403447, 10642541680005174, 10950744639606901⟩
  | 56 => ⟨10028592519450552, 10341708996349943, 10654825473249334, 10967941950148725, 11281058427048116⟩
  | 57 => ⟨10344165754998775, 10662195749195830, 10980225743392885, 11298255737589940, 11616285731786995⟩
  | 58 => ⟨10664652507844662, 10987596019339381, 11310539530834100, 11633483042328819, 11956426553823538⟩
  | 59 => ⟨10990052777988213, 11317909806780596, 11645766835572979, 11973623864365362, 12301480893157745⟩
  | 60 => ⟨11320366565429428, 11653137111519475, 11985907657609522, 12318678203699569, 12651448749789616⟩
  | 61 => ⟨11655593870168307, 11993277933556018, 12330961996943729, 12668646060331440, 13006330123719151⟩
  | 62 => ⟨11995734692204850, 12338332272890225, 12680929853575600, 13023527434260975, 13366125014946350⟩
  | 63 => ⟨12340789031539057, 12688300129522096, 13035811227505135, 13383322325488174, 13730833423471213⟩
  | 64 => ⟨12690756888170928, 13043181503451631, 13395606118732334, 13748030734013037, 14100455349293740⟩
  | 65 => ⟨13045638262100463, 13402976394678830, 13760314527257197, 14117652659835564, 14474990792413931⟩
  | 66 => ⟨13405433153327662, 13767684803203693, 14129936453079724, 14492188102955755, 14854439752831786⟩
  | 67 => ⟨13770141561852525, 14137306729026220, 14504471896199915, 14871637063373610, 15238802230547305⟩
  | 68 => ⟨14139763487675052, 14511842172146411, 14883920856617770, 15255999541089129, 15628078225560488⟩
  | 69 => ⟨14514298930795243, 14891291132564266, 15268283334333289, 15645275536102312, 16022267737871335⟩
  | 70 => ⟨14893747891213098, 15275653610279785, 15657559329346472, 16039465048413159, 16421370767479846⟩
  | 71 => ⟨15278110368928617, 15664929605292968, 16051748841657319, 16438568078021670, 16825387314386021⟩
  | 72 => ⟨15667386363941800, 16059119117603815, 16450851871265830, 16842584624927845, 17234317378589860⟩
  | 73 => ⟨16061575876252647, 16458222147212326, 16854868418172005, 17251514689131684, 17648160960091363⟩
  | 74 => ⟨16460678905861158, 16862238694118501, 17263798482375844, 17665358270633187, 18066918058890530⟩
  | 75 => ⟨16864695452767333, 17271168758322340, 17677642063877347, 18084115369432354, 18490588674987361⟩
  | 76 => ⟨17273625516971172, 17685012339823843, 18096399162676514, 18507785985529185, 18919172808381856⟩
  | 77 => ⟨17687469098472675, 18103769438623010, 18520069778773345, 18936370118923680, 19352670459074015⟩
  | 78 => ⟨18106226197271842, 18527440054719841, 18948653912167840, 19369867769615839, 19791081627063838⟩
  | 79 => ⟨18529896813368673, 18956024188114336, 19382151562859999, 19808278937605662, 20234406312351325⟩
  | 80 => ⟨18958480946763168, 19389521838806495, 19820562730849822, 20251603622893149, 20682644514936476⟩
  | 81 => ⟨19391978597455327, 19827933006796318, 20263887416137309, 20699841825478300, 21135796234819291⟩
  | 82 => ⟨19830389765445150, 20271257692083805, 20712125618722460, 21152993545361115, 21593861471999770⟩
  | 83 => ⟨20273714450732637, 20719495894668956, 21165277338605275, 21611058782541594, 22056840226477913⟩
  | 84 => ⟨20721952653317788, 21172647614551771, 21623342575785754, 22074037537019737, 22524732498253720⟩
  | 85 => ⟨21175104373200603, 21630712851732250, 22086321330263897, 22541929808795544, 22997538287327191⟩
  | 86 => ⟨21633169610381082, 22093691606210393, 22554213602039704, 23014735597869015, 23475257593698326⟩
  | 87 => ⟨22096148364859225, 22561583877986200, 23027019391113175, 23492454904240150, 23957890417367125⟩
  | 88 => ⟨22564040636635032, 23034389667059671, 23504738697484310, 23975087727908949, 24445436758333588⟩
  | 89 => ⟨23036846425708503, 23512108973430806, 23987371521153109, 24462634068875412, 24937896616597715⟩
  | 90 => ⟨23514565732079638, 23994741797099605, 24474917862119572, 24955093927139539, 25435269992159506⟩
  | 91 => ⟨23997198555748437, 24482288138066068, 24967377720383699, 25452467302701330, 25937556885018961⟩
  | 92 => ⟨24484744896714900, 24974747996330195, 25464751095945490, 25954754195560785, 26444757295176080⟩
  | 93 => ⟨24977204754979027, 25472121371891986, 25967037988804945, 26461954605717904, 26956871222630863⟩
  | 94 => ⟨25474578130540818, 25974408264751441, 26474238398962064, 26974068533172687, 27473898667383310⟩
  | 95 => ⟨25976865023400273, 26481608674908560, 26986352326416847, 27491095977925134, 27995839629433421⟩
  | 96 => ⟨26484065433557392, 26993722602363343, 27503379771169294, 28013036939975245, 28522694108781196⟩
  | 97 => ⟨26996179361012175, 27510750047115790, 28025320733219405, 28539891419323020, 29054462105426635⟩
  | 98 => ⟨27513206805764622, 28032691009165901, 28552175212567180, 29071659415968459, 29591143619369738⟩
  | 99 => ⟨28035147767814733, 28559545488513676, 29083943209212619, 29608340929911562, 30132738650610505⟩
  | 100 => ⟨28562002247162508, 29091313485159115, 29620624723155722, 30149935961152329, 30679247199148936⟩
  | 101 => ⟨29093770243807947, 29627994999102218, 30162219754396489, 30696444509690760, 31230669264985031⟩
  | 102 => ⟨29630451757751050, 30169590030342985, 30708728302934920, 31247866575526855, 31787004848118790⟩
  | 103 => ⟨30172046788991817, 30716098578881416, 31260150368771015, 31804202158660614, 32348253948550213⟩
  | 104 => ⟨30718555337530248, 31267520644717511, 31816485951904774, 32365451259092037, 32914416566279300⟩
  | 105 => ⟨31269977403366343, 31823856227851270, 32377735052336197, 32931613876821124, 33485492701306051⟩
  | 106 => ⟨31826312986500102, 32385105328282693, 32943897670065284, 33502690011847875, 34061482353630466⟩
  | 107 => ⟨32387562086931525, 32951267946011780, 33514973805092035, 34078679664172290, 34642385523252545⟩
  | 108 => ⟨32953724704660612, 33522344081038531, 34090963457416450, 34659582833794369, 35228202210172288⟩
  | 109 => ⟨33524800839687363, 34098333733362946, 34671866627038529, 35245399520714112, 35818932414389695⟩
  | 110 => ⟨34100790492011778, 34679236902985025, 35257683313958272, 35836129724931519, 36414576135904766⟩
  | 111 => ⟨34681693661633857, 35265053589904768, 35848413518175679, 36431773446446590, 37015133374717501⟩
  | _ => defaultCosts

def row17 : ℕ → Costs
  | 0 => ⟨337621516550739, 357412885234291, 416924423422645, 476435961610999, 535947499799353⟩
  | 1 => ⟨357412885234291, 419123463455413, 480834041676535, 542544619897657, 604255198118779⟩
  | 2 => ⟨335270346359479, 388674792653562, 442079238947645, 495483685241728, 548888131535811⟩
  | 3 => ⟨391286172484346, 449913378439997, 508540584395648, 567167790351299, 625794996306950⟩
  | 4 => ⟨452524758270781, 516374723888000, 580224689505219, 644074655122438, 707924620739657⟩
  | 5 => ⟨518986103718784, 588058828997571, 657131554276358, 726204279555145, 795277004833932⟩
  | 6 => ⟨590670208828355, 664965693768710, 739261178709065, 813556663649420, 887852148589775⟩
  | 7 => ⟨667577073599494, 747095318201417, 826613562803340, 906131807405263, 985650052007186⟩
  | 8 => ⟨749706698032201, 834447702295692, 919188706559183, 1003929710822674, 1088670715086165⟩
  | 9 => ⟨837059082126476, 927022846051535, 1016986609976594, 1106950373901653, 1196914137826712⟩
  | 10 => ⟨929634225882319, 1024820749468946, 1120007273055573, 1215193796642200, 1310380320228827⟩
  | 11 => ⟨1027432129299730, 1127841412547925, 1228250695796120, 1328659979044315, 1429069262292510⟩
  | 12 => ⟨1130452792378709, 1236084835288472, 1341716878198235, 1447348921107998, 1552980964017761⟩
  | 13 => ⟨1238696215119256, 1349551017690587, 1460405820261918, 1571260622833249, 1682115425404580⟩
  | 14 => ⟨1352162397521371, 1468239959754270, 1584317521987169, 1700395084220068, 1816472646452967⟩
  | 15 => ⟨1470851339585054, 1592151661479521, 1713451983373988, 1834752305268455, 1956052627162922⟩
  | 16 => ⟨1594763041310305, 1721286122866340, 1847809204422375, 1974332285978410, 2100855367534445⟩
  | 17 => ⟨1723897502697124, 1855643343914727, 1987389185132330, 2119135026349933, 2250880867567536⟩
  | 18 => ⟨1858254723745511, 1995223324624682, 2132191925503853, 2269160526383024, 2406129127262195⟩
  | 19 => ⟨1997834704455466, 2140026064996205, 2282217425536944, 2424408786077683, 2566600146618422⟩
  | 20 => ⟨2142637444826989, 2290051565029296, 2437465685231603, 2584879805433910, 2732293925636217⟩
  | 21 => ⟨2292662944860080, 2445299824723955, 2597936704587830, 2750573584451705, 2903210464315580⟩
  | 22 => ⟨2447911204554739, 2605770844080182, 2763630483605625, 2921490123131068, 3079349762656511⟩
  | 23 => ⟨2608382223910966, 2771464623097977, 2934547022284988, 3097629421471999, 3260711820659010⟩
  | 24 => ⟨2774076002928761, 2942381161777340, 3110686320625919, 3278991479474498, 3447296638323077⟩
  | 25 => ⟨2944992541608124, 3118520460118271, 3292048378628418, 3465576297138565, 3639104215648712⟩
  | 26 => ⟨3121131839949055, 3299882518120770, 3478633196292485, 3657383874464200, 3836134552635915⟩
  | 27 => ⟨3302493897951554, 3486467335784837, 3670440773618120, 3854414211451403, 4038387649284686⟩
  | 28 => ⟨3489078715615621, 3678274913110472, 3867471110605323, 4056667308100174, 4245863505595025⟩
  | 29 => ⟨3680886292941256, 3875305250097675, 4069724207254094, 4264143164410513, 4458562121566932⟩
  | 30 => ⟨3877916629928459, 4077558346746446, 4277200063564433, 4476841780382420, 4676483497200407⟩
  | 31 => ⟨4080169726577230, 4285034203056785, 4489898679536340, 4694763156015895, 4899627632495450⟩
  | 32 => ⟨4287645582887569, 4497732819028692, 4707820055169815, 4917907291310938, 5127994527452061⟩
  | 33 => ⟨4500344198859476, 4715654194662167, 4930964190464858, 5146274186267549, 5361584182070240⟩
  | 34 => ⟨4718265574492951, 4938798329957210, 5159331085421469, 5379863840885728, 5600396596349987⟩
  | 35 => ⟨4941409709787994, 5167165224913821, 5392920740039648, 5618676255165475, 5844431770291302⟩
  | 36 => ⟨5169776604744605, 5400754879532000, 5631733154319395, 5862711429106790, 6093689703894185⟩
  | 37 => ⟨5403366259362784, 5639567293811747, 5875768328260710, 6111969362709673, 6348170397158636⟩
  | 38 => ⟨5642178673642531, 5883602467753062, 6125026261863593, 6366450055974124, 6607873850084655⟩
  | 39 => ⟨5886213847583846, 6132860401355945, 6379506955128044, 6626153508900143, 6872800062672242⟩
  | 40 => ⟨6135471781186729, 6387341094620396, 6639210408054063, 6891079721487730, 7142949034921397⟩
  | 41 => ⟨6389952474451180, 6647044547546415, 6904136620641650, 7161228693736885, 7418320766832120⟩
  | 42 => ⟨6649655927377199, 6911970760134002, 7174285592890805, 7436600425647608, 7698915258404411⟩
  | 43 => ⟨6914582139964786, 7182119732383157, 7449657324801528, 7717194917219899, 7984732509638270⟩
  | 44 => ⟨7184731112213941, 7457491464293880, 7730251816373819, 8003012168453758, 8275772520533697⟩
  | 45 => ⟨7460102844124664, 7738085955866171, 8016069067607678, 8294052179349185, 8572035291090692⟩
  | 46 => ⟨7740697335696955, 8023903207100030, 8307109078503105, 8590314949906180, 8873520821309255⟩
  | 47 => ⟨8026514586930814, 8314943217995457, 8603371849060100, 8891800480124743, 9180229111189386⟩
  | 48 => ⟨8317554597826241, 8611205988552452, 8904857379278663, 9198508770004874, 9492160160731085⟩
  | 49 => ⟨8613817368383236, 8912691518771015, 9211565669158794, 9510439819546573, 9809313969934352⟩
  | 50 => ⟨8915302898601799, 9219399808651146, 9523496718700493, 9827593628749840, 10131690538799187⟩
  | 51 => ⟨9222011188481930, 9531330858192845, 9840650527903760, 10149970197614675, 10459289867325590⟩
  | 52 => ⟨9533942238023629, 9848484667396112, 10163027096768595, 10477569526141078, 10792111955513561⟩
  | 53 => ⟨9851096047226896, 10170861236260947, 10490626425294998, 10810391614329049, 11130156803363100⟩
  | 54 => ⟨10173472616091731, 10498460564787350, 10823448513482969, 11148436462178588, 11473424410874207⟩
  | 55 => ⟨10501071944618134, 10831282652975321, 11161493361332508, 11491704069689695, 11821914778046882⟩
  | 56 => ⟨10833894032806105, 11169327500824860, 11504760968843615, 11840194436862370, 12175627904881125⟩
  | 57 => ⟨11171938880655644, 11512595108335967, 11853251336016290, 12193907563696613, 12534563791376936⟩
  | 58 => ⟨11515206488166751, 11861085475508642, 12206964462850533, 12552843450192424, 12898722437534315⟩
  | 59 => ⟨11863696855339426, 12214798602342885, 12565900349346344, 12917002096349803, 13268103843353262⟩
  | 60 => ⟨12217409982173669, 12573734488838696, 12930058995503723, 13286383502168750, 13642708008833777⟩
  | 61 => ⟨12576345868669480, 12937893134996075, 13299440401322670, 13660987667649265, 14022534933975860⟩
  | 62 => ⟨12940504514826859, 13307274540815022, 13674044566803185, 14040814592791348, 14407584618779511⟩
  | 63 => ⟨13309885920645806, 13681878706295537, 14053871491945268, 14425864277594999, 14797857063244730⟩
  | 64 => ⟨13684490086126321, 14061705631437620, 14438921176748919, 14816136722060218, 15193352267371517⟩
  | 65 => ⟨14064317011268404, 14446755316241271, 14829193621214138, 15211631926187005, 15594070231159872⟩
  | 66 => ⟨14449366696072055, 14837027760706490, 15224688825340925, 15612349889975360, 16000010954609795⟩
  | 67 => ⟨14839639140537274, 15232522964833277, 15625406789129280, 16018290613425283, 16411174437721286⟩
  | 68 => ⟨15235134344664061, 15633240928621632, 16031347512579203, 16429454096536774, 16827560680494345⟩
  | 69 => ⟨15635852308452416, 16039181652071555, 16442510995690694, 16845840339309833, 17249169682928972⟩
  | 70 => ⟨16041793031902339, 16450345135183046, 16858897238463753, 17267449341744460, 17676001445025167⟩
  | 71 => ⟨16452956515013830, 16866731377956105, 17280506240898380, 17694281103840655, 18108055966782930⟩
  | 72 => ⟨16869342757786889, 17288340380390732, 17707338002994575, 18126335625598418, 18545333248202261⟩
  | 73 => ⟨17290951760221516, 17715172142486927, 18139392524752338, 18563612907017749, 18987833289283160⟩
  | 74 => ⟨17717783522317711, 18147226664244690, 18576669806171669, 19006112948098648, 19435556090025627⟩
  | 75 => ⟨18149838044075474, 18584503945664021, 19019169847252568, 19453835748841115, 19888501650429662⟩
  | 76 => ⟨18587115325494805, 19027003986744920, 19466892647995035, 19906781309245150, 20346669970495265⟩
  | 77 => ⟨19029615366575704, 19474726787487387, 19919838208399070, 20364949629310753, 20810061050222436⟩
  | 78 => ⟨19477338167318171, 19927672347891422, 20378006528464673, 20828340709037924, 21278674889611175⟩
  | 79 => ⟨19930283727722206, 20385840667957025, 20841397608191844, 21296954548426663, 21752511488661482⟩
  | 80 => ⟨20388452047787809, 20849231747684196, 21310011447580583, 21770791147476970, 22231570847373357⟩
  | 81 => ⟨20851843127514980, 21317845587072935, 21783848046630890, 22249850506188845, 22715852965746800⟩
  | 82 => ⟨21320456966903719, 21791682186123242, 22262907405342765, 22734132624562288, 23205357843781811⟩
  | 83 => ⟨21794293565954026, 22270741544835117, 22747189523716208, 23223637502597299, 23700085481478390⟩
  | 84 => ⟨22273352924665901, 22755023663208560, 23236694401751219, 23718365140293878, 24200035878836537⟩
  | 85 => ⟨22757635043039344, 23244528541243571, 23731422039447798, 24218315537652025, 24705209035856252⟩
  | 86 => ⟨23247139921074355, 23739256178940150, 24231372436805945, 24723488694671740, 25215604952537535⟩
  | 87 => ⟨23741867558770934, 24239206576298297, 24736545593825660, 25233884611353023, 25731223628880386⟩
  | 88 => ⟨24241817956129081, 24744379733318012, 25246941510506943, 25749503287695874, 26252065064884805⟩
  | 89 => ⟨24746991113148796, 25254775649999295, 25762560186849794, 26270344723700293, 26778129260550792⟩
  | 90 => ⟨25257387029830079, 25770394326342146, 26283401622854213, 26796408919366280, 27309416215878347⟩
  | 91 => ⟨25773005706172930, 26291235762346565, 26809465818520200, 27327695874693835, 27845925930867470⟩
  | 92 => ⟨26293847142177349, 26817299958012552, 27340752773847755, 27864205589682958, 28387658405518161⟩
  | 93 => ⟨26819911337843336, 27348586913340107, 27877262488836878, 28405938064333649, 28934613639830420⟩
  | 94 => ⟨27351198293170891, 27885096628329230, 28418994963487569, 28952893298645908, 29486791633804247⟩
  | 95 => ⟨27887708008160014, 28426829102979921, 28965950197799828, 29505071292619735, 30044192387439642⟩
  | 96 => ⟨28429440482810705, 28973784337292180, 29518128191773655, 30062472046255130, 30606815900736605⟩
  | 97 => ⟨28976395717122964, 29525962331266007, 30075528945409050, 30625095559552093, 31174662173695136⟩
  | 98 => ⟨29528573711096791, 30083363084901402, 30638152458706013, 31192941832510624, 31747731206315235⟩
  | 99 => ⟨30085974464732186, 30645986598198365, 31205998731664544, 31766010865130723, 32326022998596902⟩
  | 100 => ⟨30648597978029149, 31213832871156896, 31779067764284643, 32344302657412390, 32909537550540137⟩
  | 101 => ⟨31216444250987680, 31786901903776995, 32357359556566310, 32927817209355625, 33498274862144940⟩
  | 102 => ⟨31789513283607779, 32365193696058662, 32940874108509545, 33516554520960428, 34092234933411311⟩
  | 103 => ⟨32367805075889446, 32948708248001897, 33529611420114348, 34110514592226799, 34691417764339250⟩
  | 104 => ⟨32951319627832681, 33537445559606700, 34123571491380719, 34709697423154738, 35295823354928757⟩
  | 105 => ⟨33540056939437484, 34131405630873071, 34722754322308658, 35314103013744245, 35905451705179832⟩
  | 106 => ⟨34134017010703855, 34730588461801010, 35327159912898165, 35923731363995320, 36520302815092475⟩
  | 107 => ⟨34733199841631794, 35334994052390517, 35936788263149240, 36538582473907963, 37140376684666686⟩
  | 108 => ⟨35337605432221301, 35944622402641592, 36551639373061883, 37158656343482174, 37765673313902465⟩
  | 109 => ⟨35947233782472376, 36559473512554235, 37171713242636094, 37783952972717953, 38396192702799812⟩
  | 110 => ⟨36562084892385019, 37179547382128446, 37797009871871873, 38414472361615300, 39031934851358727⟩
  | _ => defaultCosts

def row18 : ℕ → Costs
  | 0 => ⟨400775215841946, 422971785085628, 489698924430082, 556426063774536, 623153203118990⟩
  | 1 => ⟨422971785085628, 492035404464898, 561099023844168, 630162643223438, 699226262602708⟩
  | 2 => ⟨392102230491908, 451433822618443, 510765414744978, 570097006871513, 629428598998048⟩
  | 3 => ⟨454199823631179, 519063417783186, 583927011935193, 648790606087200, 713654200239207⟩
  | 4 => ⟨521829418795922, 592225014973401, 662620611150880, 733016207328359, 803411803505838⟩
  | 5 => ⟨594991015986137, 670918614189088, 746846212392039, 822773810594990, 898701408797941⟩
  | 6 => ⟨673684615201824, 755144215430247, 836603815658670, 918063415887093, 999523016115516⟩
  | 7 => ⟨757910216442983, 844901818696878, 931893420950773, 1018885023204668, 1105876625458563⟩
  | 8 => ⟨847667819709614, 940191423988981, 1032715028268348, 1125238632547715, 1217762236827082⟩
  | 9 => ⟨942957425001717, 1041013031306556, 1139068637611395, 1237124243916234, 1335179850221073⟩
  | 10 => ⟨1043779032319292, 1147366640649603, 1250954248979914, 1354541857310225, 1458129465640536⟩
  | 11 => ⟨1150132641662339, 1259252252018122, 1368371862373905, 1477491472729688, 1586611083085471⟩
  | 12 => ⟨1262018253030858, 1376669865412113, 1491321477793368, 1605973090174623, 1720624702555878⟩
  | 13 => ⟨1379435866424849, 1499619480831576, 1619803095238303, 1739986709645030, 1860170324051757⟩
  | 14 => ⟨1502385481844312, 1628101098276511, 1753816714708710, 1879532331140909, 2005247947573108⟩
  | 15 => ⟨1630867099289247, 1762114717746918, 1893362336204589, 2024609954662260, 2155857573119931⟩
  | 16 => ⟨1764880718759654, 1901660339242797, 2038439959725940, 2175219580209083, 2311999200692226⟩
  | 17 => ⟨1904426340255533, 2046737962764148, 2189049585272763, 2331361207781378, 2473672830289993⟩
  | 18 => ⟨2049503963776884, 2197347588310971, 2345191212845058, 2493034837379145, 2640878461913232⟩
  | 19 => ⟨2200113589323707, 2353489215883266, 2506864842442825, 2660240469002384, 2813616095561943⟩
  | 20 => ⟨2356255216896002, 2515162845481033, 2674070474066064, 2832978102651095, 2991885731236126⟩
  | 21 => ⟨2517928846493769, 2682368477104272, 2846808107714775, 3011247738325278, 3175687368935781⟩
  | 22 => ⟨2685134478117008, 2855106110752983, 3025077743388958, 3195049376024933, 3365021008660908⟩
  | 23 => ⟨2857872111765719, 3033375746427166, 3208879381088613, 3384383015750060, 3559886650411507⟩
  | 24 => ⟨3036141747439902, 3217177384126821, 3398213020813740, 3579248657500659, 3760284294187578⟩
  | 25 => ⟨3219943385139557, 3406511023851948, 3593078662564339, 3779646301276730, 3966213939989121⟩
  | 26 => ⟨3409277024864684, 3601376665602547, 3793476306340410, 3985575947078273, 4177675587816136⟩
  | 27 => ⟨3604142666615283, 3801774309378618, 3999405952141953, 4197037594905288, 4394669237668623⟩
  | 28 => ⟨3804540310391354, 4007703955180161, 4210867599968968, 4414031244757775, 4617194889546582⟩
  | 29 => ⟨4010469956192897, 4219165603007176, 4427861249821455, 4636556896635734, 4845252543450013⟩
  | 30 => ⟨4221931604019912, 4436159252859663, 4650386901699414, 4864614550539165, 5078842199378916⟩
  | 31 => ⟨4438925253872399, 4658684904737622, 4878444555602845, 5098204206468068, 5317963857333291⟩
  | 32 => ⟨4661450905750358, 4886742558641053, 5112034211531748, 5337325864422443, 5562617517313138⟩
  | 33 => ⟨4889508559653789, 5120332214569956, 5351155869486123, 5581979524402290, 5812803179318457⟩
  | 34 => ⟨5123098215582692, 5359453872524331, 5595809529465970, 5832165186407609, 6068520843349248⟩
  | 35 => ⟨5362219873537067, 5604107532504178, 5845995191471289, 6087882850438400, 6329770509405511⟩
  | 36 => ⟨5606873533516914, 5854293194509497, 6101712855502080, 6349132516494663, 6596552177487246⟩
  | 37 => ⟨5857059195522233, 6110010858540288, 6362962521558343, 6615914184576398, 6868865847594453⟩
  | 38 => ⟨6112776859553024, 6371260524596551, 6629744189640078, 6888227854683605, 7146711519727132⟩
  | 39 => ⟨6374026525609287, 6638042192678286, 6902057859747285, 7166073526816284, 7430089193885283⟩
  | 40 => ⟨6640808193691022, 6910355862785493, 7179903531879964, 7449451200974435, 7718998870068906⟩
  | 41 => ⟨6913121863798229, 7188201534918172, 7463281206038115, 7738360877158058, 8013440548278001⟩
  | 42 => ⟨7190967535930908, 7471579209076323, 7752190882221738, 8032802555367153, 8313414228512568⟩
  | 43 => ⟨7474345210089059, 7760488885259946, 8046632560430833, 8332776235601720, 8618919910772607⟩
  | 44 => ⟨7763254886272682, 8054930563469041, 8346606240665400, 8638281917861759, 8929957595058118⟩
  | 45 => ⟨8057696564481777, 8354904243703608, 8652111922925439, 8949319602147270, 9246527281369101⟩
  | 46 => ⟨8357670244716344, 8660409925963647, 8963149607210950, 9265889288458253, 9568628969705556⟩
  | 47 => ⟨8663175926976383, 8971447610249158, 9279719293521933, 9587990976794708, 9896262660067483⟩
  | 48 => ⟨8974213611261894, 9288017296560141, 9601820981858388, 9915624667156635, 10229428352454882⟩
  | 49 => ⟨9290783297572877, 9610118984896596, 9929454672220315, 10248790359544034, 10568126046867753⟩
  | 50 => ⟨9612884985909332, 9937752675258523, 10262620364607714, 10587488053956905, 10912355743306096⟩
  | 51 => ⟨9940518676271259, 10270918367645922, 10601318059020585, 10931717750395248, 11262117441769911⟩
  | 52 => ⟨10273684368658658, 10609616062058793, 10945547755458928, 11281479448859063, 11617411142259198⟩
  | 53 => ⟨10612382063071529, 10953845758497136, 11295309453922743, 11636773149348350, 11978236844773957⟩
  | 54 => ⟨10956611759509872, 11303607456960951, 11650603154412030, 11997598851863109, 12344594549314188⟩
  | 55 => ⟨11306373457973687, 11658901157450238, 12011428856926789, 12363956556403340, 12716484255879891⟩
  | 56 => ⟨11661667158462974, 12019726859964997, 12377786561467020, 12735846262969043, 13093905964471066⟩
  | 57 => ⟨12022492860977733, 12386084564505228, 12749676268032723, 13113267971560218, 13476859675087713⟩
  | 58 => ⟨12388850565517964, 12757974271070931, 13127097976623898, 13496221682176865, 13865345387729832⟩
  | 59 => ⟨12760740272083667, 13135395979662106, 13510051687240545, 13884707394818984, 14259363102397423⟩
  | 60 => ⟨13138161980674842, 13518349690278753, 13898537399882664, 14278725109486575, 14658912819090486⟩
  | 61 => ⟨13521115691291489, 13906835402920872, 14292555114550255, 14678274826179638, 15063994537809021⟩
  | 62 => ⟨13909601403933608, 14300853117588463, 14692104831243318, 15083356544898173, 15474608258553028⟩
  | 63 => ⟨14303619118601199, 14700402834281526, 15097186549961853, 15493970265642180, 15890753981322507⟩
  | 64 => ⟨14703168835294262, 15105484553000061, 15507800270705860, 15910115988411659, 16312431706117458⟩
  | 65 => ⟨15108250554012797, 15516098273744068, 15923945993475339, 16331793713206610, 16739641432937881⟩
  | 66 => ⟨15518864274756804, 15932243996513547, 16345623718270290, 16759003440027033, 17172383161783776⟩
  | 67 => ⟨15935009997526283, 16353921721308498, 16772833445090713, 17191745168872928, 17610656892655143⟩
  | 68 => ⟨16356687722321234, 16781131448128921, 17205575173936608, 17630018899744295, 18054462625551982⟩
  | 69 => ⟨16783897449141657, 17213873176974816, 17643848904807975, 18073824632641134, 18503800360474293⟩
  | 70 => ⟨17216639177987552, 17652146907846183, 18087654637704814, 18523162367563445, 18958670097422076⟩
  | 71 => ⟨17654912908858919, 18095952640743022, 18536992372627125, 18978032104511228, 19419071836395331⟩
  | 72 => ⟨18098718641755758, 18545290375665333, 18991862109574908, 19438433843484483, 19885005577394058⟩
  | 73 => ⟨18548056376678069, 19000160112613116, 19452263848548163, 19904367584483210, 20356471320418257⟩
  | 74 => ⟨19002926113625852, 19460561851586371, 19918197589546890, 20375833327507409, 20833469065467928⟩
  | 75 => ⟨19463327852599107, 19926495592585098, 20389663332571089, 20852831072557080, 21315998812543071⟩
  | 76 => ⟨19929261593597834, 20397961335609297, 20866661077620760, 21335360819632223, 21804060561643686⟩
  | 77 => ⟨20400727336622033, 20874959080658968, 21349190824695903, 21823422568732838, 22297654312769773⟩
  | 78 => ⟨20877725081671704, 21357488827734111, 21837252573796518, 22317016319858925, 22796780065921332⟩
  | 79 => ⟨21360254828746847, 21845550576834726, 22330846324922605, 22816142073010484, 23301437821098363⟩
  | 80 => ⟨21848316577847462, 22339144327960813, 22829972078074164, 23320799828187515, 23811627578300866⟩
  | 81 => ⟨22341910328973549, 22838270081112372, 23334629833251195, 23830989585390018, 24327349337528841⟩
  | 82 => ⟨22841036082125108, 23342927836289403, 23844819590453698, 24346711344617993, 24848603098782288⟩
  | 83 => ⟨23345693837302139, 23853117593491906, 24360541349681673, 24867965105871440, 25375388862061207⟩
  | 84 => ⟨23855883594504642, 24368839352719881, 24881795110935120, 25394750869150359, 25907706627365598⟩
  | 85 => ⟨24371605353732617, 24890093113973328, 25408580874214039, 25927068634454750, 26445556394695461⟩
  | 86 => ⟨24892859114986064, 25416878877252247, 25940898639518430, 26464918401784613, 26988938164050796⟩
  | 87 => ⟨25419644878264983, 25949196642556638, 26478748406848293, 27008300171139948, 27537851935431603⟩
  | 88 => ⟨25951962643569374, 26487046409886501, 27022130176203628, 27557213942520755, 28092297708837882⟩
  | 89 => ⟨26489812410899237, 27030428179241836, 27571043947584435, 28111659715927034, 28652275484269633⟩
  | 90 => ⟨27033194180254572, 27579341950622643, 28125489720990714, 28671637491358785, 29217785261726856⟩
  | 91 => ⟨27582107951635379, 28133787724028922, 28685467496422465, 29237147268816008, 29788827041209551⟩
  | 92 => ⟨28136553725041658, 28693765499460673, 29250977273879688, 29808189048298703, 30365400822717718⟩
  | 93 => ⟨28696531500473409, 29259275276917896, 29822019053362383, 30384762829806870, 30947506606251357⟩
  | 94 => ⟨29262041277930632, 29830317056400591, 30398592834870550, 30966868613340509, 31535144391810468⟩
  | 95 => ⟨29833083057413327, 30406890837908758, 30980698618404189, 31554506398899620, 32128314179395051⟩
  | 96 => ⟨30409656838921494, 30988996621442397, 31568336403963300, 32147676186484203, 32727015969005106⟩
  | 97 => ⟨30991762622455133, 31576634407001508, 32161506191547883, 32746377976094258, 33331249760640633⟩
  | 98 => ⟨31579400408014244, 32169804194586091, 32760207981157938, 33350611767729785, 33941015554301632⟩
  | 99 => ⟨32172570195598827, 32768505984196146, 33364441772793465, 33960377561390784, 34556313349988103⟩
  | 100 => ⟨32771271985208882, 33372739775831673, 33974207566454464, 34575675357077255, 35177143147700046⟩
  | 101 => ⟨33375505776844409, 33982505569492672, 34589505362140935, 35196505154789198, 35803504947437461⟩
  | 102 => ⟨33985271570505408, 34597803365179143, 35210335159852878, 35822866954526613, 36435398749200348⟩
  | 103 => ⟨34600569366191879, 35218633162891086, 35836696959590293, 36454760756289500, 37072824552988707⟩
  | 104 => ⟨35221399163903822, 35844994962628501, 36468590761353180, 37092186560077859, 37715782358802538⟩
  | 105 => ⟨35847760963641237, 36476888764391388, 37106016565141539, 37735144365891690, 38364272166641841⟩
  | 106 => ⟨36479654765404124, 37114314568179747, 37748974370955370, 38383634173730993, 39018293976506616⟩
  | 107 => ⟨37117080569192483, 37757272373993578, 38397464178794673, 39037655983595768, 39677847788396863⟩
  | 108 => ⟨37760038375006314, 38405762181832881, 39051485988659448, 39697209795486015, 40342933602312582⟩
  | 109 => ⟨38408528182845617, 39059783991697656, 39711039800549695, 40362295609401734, 41013551418253773⟩
  | _ => defaultCosts

def row19 : ℕ → Costs
  | 0 => ⟨471350676292325, 496089886098185, 570444946604883, 644800007111581, 719155067618279⟩
  | 1 => ⟨496089886098185, 572918866641747, 649747847185309, 726576827728871, 803405808272433⟩
  | 2 => ⟨455015881638741, 520583861961632, 586151842284523, 651719822607414, 717287802930305⟩
  | 3 => ⟨523504484156320, 594913708868587, 666322933580854, 737732158293121, 809141383005388⟩
  | 4 => ⟨597834331063275, 675084800164918, 752335269266561, 829585738368204, 906836207469847⟩
  | 5 => ⟨678005422359606, 761097135850625, 844188849341644, 927280562832663, 1010372276323682⟩
  | 6 => ⟨764017758045313, 852950715925708, 941883673806103, 1030816631686498, 1119749589566893⟩
  | 7 => ⟨855871338120396, 950645540390167, 1045419742659938, 1140193944929709, 1234968147199480⟩
  | 8 => ⟨953566162584855, 1054181609244002, 1154797055903149, 1255412502562296, 1356027949221443⟩
  | 9 => ⟨1057102231438690, 1163558922487213, 1270015613535736, 1376472304584259, 1482928995632782⟩
  | 10 => ⟨1166479544681901, 1278777480119800, 1391075415557699, 1503373350995598, 1615671286433497⟩
  | 11 => ⟨1281698102314488, 1399837282141763, 1517976461969038, 1636115641796313, 1754254821623588⟩
  | 12 => ⟨1402757904336451, 1526738328553102, 1650718752769753, 1774699176986404, 1898679601203055⟩
  | 13 => ⟨1529658950747790, 1659480619353817, 1789302287959844, 1919123956565871, 2048945625171898⟩
  | 14 => ⟨1662401241548505, 1798064154543908, 1933727067539311, 2069389980534714, 2205052893530117⟩
  | 15 => ⟨1800984776738596, 1942488934123375, 2083993091508154, 2225497248892933, 2367001406277712⟩
  | 16 => ⟨1945409556318063, 2092754958092218, 2240100359866373, 2387445761640528, 2534791163414683⟩
  | 17 => ⟨2095675580286906, 2248862226450437, 2402048872613968, 2555235518777499, 2708422164941030⟩
  | 18 => ⟨2251782848645125, 2410810739198032, 2569838629750939, 2728866520303846, 2887894410856753⟩
  | 19 => ⟨2413731361392720, 2578600496335003, 2743469631277286, 2908338766219569, 3073207901161852⟩
  | 20 => ⟨2581521118529691, 2752231497861350, 2922941877193009, 3093652256524668, 3264362635856327⟩
  | 21 => ⟨2755152120056038, 2931703743777073, 3108255367498108, 3284806991219143, 3461358614940178⟩
  | 22 => ⟨2934624365971761, 3117017234082172, 3299410102192583, 3481802970302994, 3664195838413405⟩
  | 23 => ⟨3119937856276860, 3308171968776647, 3496406081276434, 3684640193776221, 3872874306276008⟩
  | 24 => ⟨3311092590971335, 3505167947860498, 3699243304749661, 3893318661638824, 4087394018527987⟩
  | 25 => ⟨3508088570055186, 3708005171333725, 3907921772612264, 4107838373890803, 4307754975169342⟩
  | 26 => ⟨3710925793528413, 3916683639196328, 4122441484864243, 4328199330532158, 4533957176200073⟩
  | 27 => ⟨3919604261391016, 4131203351448307, 4342802441505598, 4554401531562889, 4766000621620180⟩
  | 28 => ⟨4134123973642995, 4351564308089662, 4569004642536329, 4786444976982996, 5003885311429663⟩
  | 29 => ⟨4354484930284350, 4577766509120393, 4801048087956436, 5024329666792479, 5247611245628522⟩
  | 30 => ⟨4580687131315081, 4809809954540500, 5038932777765919, 5268055600991338, 5497178424216757⟩
  | 31 => ⟨4812730576735188, 5047694644349983, 5282658711964778, 5517622779579573, 5752586847194368⟩
  | 32 => ⟨5050615266544671, 5291420578548842, 5532225890553013, 5773031202557184, 6013836514561355⟩
  | 33 => ⟨5294341200743530, 5540987757137077, 5787634313530624, 6034280869924171, 6280927426317718⟩
  | 34 => ⟨5543908379331765, 5796396180114688, 6048883980897611, 6301371781680534, 6553859582463457⟩
  | 35 => ⟨5799316802309376, 6057645847481675, 6315974892653974, 6574303937826273, 6832632982998572⟩
  | 36 => ⟨6060566469676363, 6324736759238038, 6588907048799713, 6853077338361388, 7117247627923063⟩
  | 37 => ⟨6327657381432726, 6597668915383777, 6867680449334828, 7137691983285879, 7407703517236930⟩
  | 38 => ⟨6600589537578465, 6876442315918892, 7152295094259319, 7428147872599746, 7704000650940173⟩
  | 39 => ⟨6879362938113580, 7161056960843383, 7442750983573186, 7724445006302989, 8006139029032792⟩
  | 40 => ⟨7163977583038071, 7451512850157250, 7739048117276429, 8026583384395608, 8314118651514787⟩
  | 41 => ⟨7454433472351938, 7747809983860493, 8041186495369048, 8334563006877603, 8627939518386158⟩
  | 42 => ⟨7750730606055181, 8049948361953112, 8349166117851043, 8648383873748974, 8947601629646905⟩
  | 43 => ⟨8052868984147800, 8357927984435107, 8662986984722414, 8968045985009721, 9273104985297028⟩
  | 44 => ⟨8360848606629795, 8671748851306478, 8982649095983161, 9293549340659844, 9604449585336527⟩
  | 45 => ⟨8674669473501166, 8991410962567225, 9308152451633284, 9624893940699343, 9941635429765402⟩
  | 46 => ⟨8994331584761913, 9316914318217348, 9639497051672783, 9962079785128218, 10284662518583653⟩
  | 47 => ⟨9319834940412036, 9648258918256847, 9976682896101658, 10305106873946469, 10633530851791280⟩
  | 48 => ⟨9651179540451535, 9985444762685722, 10319709984919909, 10653975207154096, 10988240429388283⟩
  | 49 => ⟨9988365384880410, 10328471851503973, 10668578318127536, 11008684784751099, 11348791251374662⟩
  | 50 => ⟨10331392473698661, 10677340184711600, 11023287895724539, 11369235606737478, 11715183317750417⟩
  | 51 => ⟨10680260806906288, 11032049762308603, 11383838717710918, 11735627673113233, 12087416628515548⟩
  | 52 => ⟨11034970384503291, 11392600584294982, 11750230784086673, 12107860983878364, 12465491183670055⟩
  | 53 => ⟨11395521206489670, 11758992650670737, 12122464094851804, 12485935539032871, 12849406983213938⟩
  | 54 => ⟨11761913272865425, 12131225961435868, 12500538650006311, 12869851338576754, 13239164027147197⟩
  | 55 => ⟨12134146583630556, 12509300516590375, 12884454449550194, 13259608382510013, 13634762315469832⟩
  | 56 => ⟨12512221138785063, 12893216316134258, 13274211493483453, 13655206670832648, 14036201848181843⟩
  | 57 => ⟨12896136938328946, 13282973360067517, 13669809781806088, 14056646203544659, 14443482625283230⟩
  | 58 => ⟨13285893982262205, 13678571648390152, 14071249314518099, 14463926980646046, 14856604646773993⟩
  | 59 => ⟨13681492270584840, 14080011181102163, 14478530091619486, 14877049002136809, 15275567912654132⟩
  | 60 => ⟨14082931803296851, 14487291958203550, 14891652113110249, 15296012268016948, 15700372422923647⟩
  | 61 => ⟨14490212580398238, 14900413979694313, 15310615378990388, 15720816778286463, 16131018177582538⟩
  | 62 => ⟨14903334601889001, 15319377245574452, 15735419889259903, 16151462532945354, 16567505176630805⟩
  | 63 => ⟨15322297867769140, 15744181755843967, 16166065643918794, 16587949531993621, 17009833420068448⟩
  | 64 => ⟨15747102378038655, 16174827510502858, 16602552642967061, 17030277775431264, 17458002907895467⟩
  | 65 => ⟨16177748132697546, 16611314509551125, 17044880886404704, 17478447263258283, 17912013640111862⟩
  | 66 => ⟨16614235131745813, 17053642752988768, 17493050374231723, 17932457995474678, 18371865616717633⟩
  | 67 => ⟨17056563375183456, 17501812240815787, 17947061106448118, 18392309972080449, 18837558837712780⟩
  | 68 => ⟨17504732863010475, 17955822973032182, 18406913083053889, 18858003193075596, 19309093303097303⟩
  | 69 => ⟨17958743595226870, 18415674949637953, 18872606304049036, 19329537658460119, 19786469012871202⟩
  | 70 => ⟨18418595571832641, 18881368170633100, 19344140769433559, 19806913368234018, 20269685967034477⟩
  | 71 => ⟨18884288792827788, 19352902636017623, 19821516479207458, 20290130322397293, 20758744165587128⟩
  | 72 => ⟨19355823258212311, 19830278345791522, 20304733433370733, 20779188520949944, 21253643608529155⟩
  | 73 => ⟨19833198967986210, 20313495299954797, 20793791631923384, 21274087963891971, 21754384295860558⟩
  | 74 => ⟨20316415922149485, 20802553498507448, 21288691074865411, 21774828651223374, 22260966227581337⟩
  | 75 => ⟨20805474120702136, 21297452941449475, 21789431762196814, 22281410582944153, 22773389403691492⟩
  | 76 => ⟨21300373563644163, 21798193628780878, 22296013693917593, 22793833759054308, 23291653824191023⟩
  | 77 => ⟨21801114250975566, 22304775560501657, 22808436870027748, 23312098179553839, 23815759489079930⟩
  | 78 => ⟨22307696182696345, 22817198736611812, 23326701290527279, 23836203844442746, 24345706398358213⟩
  | 79 => ⟨22820119358806500, 23335463157111343, 23850806955416186, 24366150753721029, 24881494552025872⟩
  | 80 => ⟨23338383779306031, 23859568822000250, 24380753864694469, 24901938907388688, 25423123950082907⟩
  | 81 => ⟨23862489444194938, 24389515731278533, 24916542018362128, 25443568305445723, 25970594592529318⟩
  | 82 => ⟨24392436353473221, 24925303884946192, 25458171416419163, 25991038947892134, 26523906479365105⟩
  | 83 => ⟨24928224507140880, 25466933283003227, 26005642058865574, 26544350834727921, 27083059610590268⟩
  | 84 => ⟨25469853905197915, 26014403925449638, 26558953945701361, 27103503965953084, 27648053986204807⟩
  | 85 => ⟨26017324547644326, 26567715812285425, 27118107076926524, 27668498341567623, 28218889606208722⟩
  | 86 => ⟨26570636434480113, 27126868943510588, 27683101452541063, 28239333961571538, 28795566470602013⟩
  | 87 => ⟨27129789565705276, 27691863319125127, 28253937072544978, 28816010825964829, 29378084579384680⟩
  | 88 => ⟨27694783941319815, 28262698939129042, 28830613936938269, 29398528934747496, 29966443932556723⟩
  | 89 => ⟨28265619561323730, 28839375803522333, 29413132045720936, 29986888287919539, 30560644530118142⟩
  | 90 => ⟨28842296425717021, 29421893912305000, 30001491398892979, 30581088885480958, 31160686372068937⟩
  | 91 => ⟨29424814534499688, 30010253265477043, 30595691996454398, 31181130727431753, 31766569458409108⟩
  | 92 => ⟨30013173887671731, 30604453863038462, 31195733838405193, 31787013813771924, 32378293789138655⟩
  | 93 => ⟨30607374485233150, 31204495704989257, 31801616924745364, 32398738144501471, 32995859364257578⟩
  | 94 => ⟨31207416327183945, 31810378791329428, 32413341255474911, 33016303719620394, 33619266183765877⟩
  | 95 => ⟨31813299413524116, 32422103122058975, 33030906830593834, 33639710539128693, 34248514247663552⟩
  | 96 => ⟨32425023744253663, 33039668697177898, 33654313650102133, 34268958603026368, 34883603555950603⟩
  | 97 => ⟨33042589319372586, 33663075516686197, 34283561713999808, 34904047911313419, 35524534108627030⟩
  | 98 => ⟨33665996138880885, 34292323580583872, 34918651022286859, 35544978463989846, 36171305905692833⟩
  | 99 => ⟨34295244202778560, 34927412888870923, 35559581574963286, 36191750261055649, 36823918947148012⟩
  | 100 => ⟨34930333511065611, 35568343441547350, 36206353372029089, 36844363302510828, 37482373232992567⟩
  | 101 => ⟨35571264063742038, 36215115238613153, 36858966413484268, 37502817588355383, 38146668763226498⟩
  | 102 => ⟨36218035860807841, 36867728280068332, 37517420699328823, 38167113118589314, 38816805537849805⟩
  | 103 => ⟨36870648902263020, 37526182565912887, 38181716229562754, 38837249893212621, 39492783556862488⟩
  | 104 => ⟨37529103188107575, 38190478096146818, 38851853004186061, 39513227912225304, 40174602820264547⟩
  | 105 => ⟨38193398718341506, 38860614870770125, 39527831023198744, 40195047175627363, 40862263328055982⟩
  | 106 => ⟨38863535492964813, 39536592889782808, 40209650286600803, 40882707683418798, 41555765080236793⟩
  | 107 => ⟨39539513511977496, 40218412153184867, 40897310794392238, 41576209435599609, 42255108076806980⟩
  | 108 => ⟨40221332775379555, 40906072660976302, 41590812546573049, 42275552432169796, 42960292317766543⟩
  | _ => defaultCosts

def row20 : ℕ → Costs
  | 0 => ⟨549760217908020, 577179508278106, 659574809953192, 741970111628278, 824365413303364⟩
  | 1 => ⟨577179508278106, 662186169992104, 747192831706102, 832199493420100, 917206155134098⟩
  | 2 => ⟨524320542163882, 596434153047033, 668547763930184, 740661374813335, 812774985696486⟩
  | 3 => ⟨599509396423673, 677773494060104, 756037591696535, 834301689332966, 912565786969397⟩
  | 4 => ⟨680848737436744, 765263321826455, 849677906216166, 934092490605877, 1018507074995588⟩
  | 5 => ⟨768338565203095, 858903636346086, 949468707489077, 1040033778632068, 1130598849775059⟩
  | 6 => ⟨861978879722726, 958694437618997, 1055409995515268, 1152125553411539, 1248841111307810⟩
  | 7 => ⟨961769680995637, 1064635725645188, 1167501770294739, 1270367814944290, 1373233859593841⟩
  | 8 => ⟨1067710969021828, 1176727500424659, 1285744031827490, 1394760563230321, 1503777094633152⟩
  | 9 => ⟨1179802743801299, 1294969761957410, 1410136780113521, 1525303798269632, 1640470816425743⟩
  | 10 => ⟨1298045005334050, 1419362510243441, 1540680015152832, 1661997520062223, 1783315024971614⟩
  | 11 => ⟨1422437753620081, 1549905745282752, 1677373736945423, 1804841728608094, 1932309720270765⟩
  | 12 => ⟨1552980988659392, 1686599467075343, 1820217945491294, 1953836423907245, 2087454902323196⟩
  | 13 => ⟨1689674710451983, 1829443675621214, 1969212640790445, 2108981605959676, 2248750571128907⟩
  | 14 => ⟨1832518918997854, 1978438370920365, 2124357822842876, 2270277274765387, 2416196726687898⟩
  | 15 => ⟨1981513614297005, 2133583552972796, 2285653491648587, 2437723430324378, 2589793369000169⟩
  | 16 => ⟨2136658796349436, 2294879221778507, 2453099647207578, 2611320072636649, 2769540498065720⟩
  | 17 => ⟨2297954465155147, 2462325377337498, 2626696289519849, 2791067201702200, 2955438113884551⟩
  | 18 => ⟨2465400620714138, 2635922019649769, 2806443418585400, 2976964817521031, 3147486216456662⟩
  | 19 => ⟨2638997263026409, 2815669148715320, 2992341034404231, 3169012920093142, 3345684805782053⟩
  | 20 => ⟨2818744392091960, 3001566764534151, 3184389136976342, 3367211509418533, 3550033881860724⟩
  | 21 => ⟨3004642007910791, 3193614867106262, 3382587726301733, 3571560585497204, 3760533444692675⟩
  | 22 => ⟨3196690110482902, 3391813456431653, 3586936802380404, 3782060148329155, 3977183494277906⟩
  | 23 => ⟨3394888699808293, 3596162532510324, 3797436365212355, 3998710197914386, 4199984030616417⟩
  | 24 => ⟨3599237775886964, 3806662095342275, 4014086414797586, 4221510734252897, 4428935053708208⟩
  | 25 => ⟨3809737338718915, 4023312144927506, 4236886951136097, 4450461757344688, 4664036563553279⟩
  | 26 => ⟨4026387388304146, 4246112681266017, 4465837974227888, 4685563267189759, 4905288560151630⟩
  | 27 => ⟨4249187924642657, 4475063704357808, 4700939484072959, 4926815263788110, 5152691043503261⟩
  | 28 => ⟨4478138947734448, 4710165214202879, 4942191480671310, 5174217747139741, 5406244013608172⟩
  | 29 => ⟨4713240457579519, 4951417210801230, 5189593964022941, 5427770717244652, 5665947470466363⟩
  | 30 => ⟨4954492454177870, 5198819694152861, 5443146934127852, 5687474174102843, 5931801414077834⟩
  | 31 => ⟨5201894937529501, 5452372664257772, 5702850390986043, 5953328117714314, 6203805844442585⟩
  | 32 => ⟨5455447907634412, 5712076121115963, 5968704334597514, 6225332548079065, 6481960761560616⟩
  | 33 => ⟨5715151364492603, 5977930064727434, 6240708764962265, 6503487465197096, 6766266165431927⟩
  | 34 => ⟨5981005308104074, 6249934495092185, 6518863682080296, 6787792869068407, 7056722056056518⟩
  | 35 => ⟨6253009738468825, 6528089412210216, 6803169085951607, 7078248759692998, 7353328433434389⟩
  | 36 => ⟨6531164655586856, 6812394816081527, 7093624976576198, 7374855137070869, 7656085297565540⟩
  | 37 => ⟨6815470059458167, 7102850706706118, 7390231353954069, 7677612001202020, 7964992648449971⟩
  | 38 => ⟨7105925950082758, 7399457084083989, 7692988218085220, 7986519352086451, 8280050486087682⟩
  | 39 => ⟨7402532327460629, 7702213948215140, 8001895568969651, 8301577189724162, 8601258810478673⟩
  | 40 => ⟨7705289191591780, 8011121299099571, 8316953406607362, 8622785514115153, 8928617621622944⟩
  | 41 => ⟨8014196542476211, 8326179136737282, 8638161730998353, 8950144325259424, 9262126919520495⟩
  | 42 => ⟨8329254380113922, 8647387461128273, 8965520542142624, 9283653623156975, 9601786704171326⟩
  | 43 => ⟨8650462704504913, 8974746272272544, 9299029840040175, 9623313407807806, 9947596975575437⟩
  | 44 => ⟨8977821515649184, 9308255570170095, 9638689624691006, 9969123679211917, 10299557733732828⟩
  | 45 => ⟨9311330813546735, 9647915354820926, 9984499896095117, 10321084437369308, 10657668978643499⟩
  | 46 => ⟨9650990598197566, 9993725626225037, 10336460654252508, 10679195682279979, 11021930710307450⟩
  | 47 => ⟨9996800869601677, 10345686384382428, 10694571899163179, 11043457413943930, 11392342928724681⟩
  | 48 => ⟨10348761627759068, 10703797629293099, 11058833630827130, 11413869632361161, 11768905633895192⟩
  | 49 => ⟨10706872872669739, 11068059360957050, 11429245849244361, 11790432337531672, 12151618825818983⟩
  | 50 => ⟨11071134604333690, 11438471579374281, 11805808554414872, 12173145529455463, 12540482504496054⟩
  | 51 => ⟨11441546822750921, 11815034284544792, 12188521746338663, 12562009208132534, 12935496669926405⟩
  | 52 => ⟨11818109527921432, 12197747476468583, 12577385425015734, 12957023373562885, 13336661322110036⟩
  | 53 => ⟨12200822719845223, 12586611155145654, 12972399590446085, 13358188025746516, 13743976461046947⟩
  | 54 => ⟨12589686398522294, 12981625320576005, 13373564242629716, 13765503164683427, 14157442086737138⟩
  | 55 => ⟨12984700563952645, 13382789972759636, 13780879381566627, 14178968790373618, 14577058199180609⟩
  | 56 => ⟨13385865216136276, 13790105111696547, 14194345007256818, 14598584902817089, 15002824798377360⟩
  | 57 => ⟨13793180355073187, 14203570737386738, 14613961119700289, 15024351502013840, 15434741884327391⟩
  | 58 => ⟨14206645980763378, 14623186849830209, 15039727718897040, 15456268587963871, 15872809457030702⟩
  | 59 => ⟨14626262093206849, 15048953449026960, 15471644804847071, 15894336160667182, 16317027516487293⟩
  | 60 => ⟨15052028692403600, 15480870534976991, 15909712377550382, 16338554220123773, 16767396062697164⟩
  | 61 => ⟨15483945778353631, 15918938107680302, 16353930437006973, 16788922766333644, 17223915095660315⟩
  | 62 => ⟨15922013351056942, 16363156167136893, 16804298983216844, 17245441799296795, 17686584615376746⟩
  | 63 => ⟨16366231410513533, 16813524713346764, 17260818016179995, 17708111319013226, 18155404621846457⟩
  | 64 => ⟨16816599956723404, 17270043746309915, 17723487535896426, 18176931325482937, 18630375115069448⟩
  | 65 => ⟨17273118989686555, 17732713266026346, 18192307542366137, 18651901818705928, 19111496095045719⟩
  | 66 => ⟨17735788509402986, 18201533272496057, 18667278035589128, 19133022798682199, 19598767561775270⟩
  | 67 => ⟨18204608515872697, 18676503765719048, 19148399015565399, 19620294265411750, 20092189515258101⟩
  | 68 => ⟨18679579009095688, 19157624745695319, 19635670482294950, 20113716218894581, 20591761955494212⟩
  | 69 => ⟨19160699989071959, 19644896212424870, 20129092435777781, 20613288659130692, 21097484882483603⟩
  | 70 => ⟨19647971455801510, 20138318165907701, 20628664876013892, 21119011586120083, 21609358296226274⟩
  | 71 => ⟨20141393409284341, 20637890606143812, 21134387803003283, 21630884999862754, 22127382196722225⟩
  | 72 => ⟨20640965849520452, 21143613533133203, 21646261216745954, 22148908900358705, 22651556583971456⟩
  | 73 => ⟨21146688776509843, 21655486946875874, 22164285117241905, 22673083287607936, 23181881457973967⟩
  | 74 => ⟨21658562190252514, 22173510847371825, 22688459504491136, 23203408161610447, 23718356818729758⟩
  | 75 => ⟨22176586090748465, 22697685234621056, 23218784378493647, 23739883522366238, 24260982666238829⟩
  | 76 => ⟨22700760477997696, 23228010108623567, 23755259739249438, 24282509369875309, 24809759000501180⟩
  | 77 => ⟨23231085352000207, 23764485469379358, 24297885586758509, 24831285704137660, 25364685821516811⟩
  | 78 => ⟨23767560712755998, 24307111316888429, 24846661921020860, 25386212525153291, 25925763129285722⟩
  | 79 => ⟨24310186560265069, 24855887651150780, 25401588742036491, 25947289832922202, 26492990923807913⟩
  | 80 => ⟨24858962894527420, 25410814472166411, 25962666049805402, 26514517627444393, 27066369205083384⟩
  | 81 => ⟨25413889715543051, 25971891779935322, 26529893844327593, 27087895908719864, 27645897973112135⟩
  | 82 => ⟨25974967023311962, 26539119574457513, 27103272125603064, 27667424676748615, 28231577227894166⟩
  | 83 => ⟨26542194817834153, 27112497855732984, 27682800893631815, 28253103931530646, 28823406969429477⟩
  | 84 => ⟨27115573099109624, 27692026623761735, 28268480148413846, 28844933673065957, 29421387197718068⟩
  | 85 => ⟨27695101867138375, 28277705878543766, 28860309889949157, 29442913901354548, 30025517912759939⟩
  | 86 => ⟨28280781121920406, 28869535620079077, 29458290118237748, 30047044616396419, 30635799114555090⟩
  | 87 => ⟨28872610863455717, 29467515848367668, 30062420833279619, 30657325818191570, 31252230803103521⟩
  | 88 => ⟨29470591091744308, 30071646563409539, 30672702035074770, 31273757506740001, 31874812978405232⟩
  | 89 => ⟨30074721806786179, 30681927765204690, 31289133723623201, 31896339682041712, 32503545640460223⟩
  | 90 => ⟨30685003008581330, 31298359453753121, 31911715898924912, 32525072344096703, 33138428789268494⟩
  | 91 => ⟨31301434697129761, 31920941629054832, 32540448560979903, 33159955492904974, 33779462424830045⟩
  | 92 => ⟨31924016872431472, 32549674291109823, 33175331709788174, 33800989128466525, 34426646547144876⟩
  | 93 => ⟨32552749534486463, 33184557439918094, 33816365345349725, 34448173250781356, 35079981156212987⟩
  | 94 => ⟨33187632683294734, 33825591075479645, 34463549467664556, 35101507859849467, 35739466252034378⟩
  | 95 => ⟨33828666318856285, 34472775197794476, 35116884076732667, 35760992955670858, 36405101834609049⟩
  | 96 => ⟨34475850441171116, 35126109806862587, 35776369172554058, 36426628538245529, 37076887903937000⟩
  | 97 => ⟨35129185050239227, 35785594902683978, 36442004755128729, 37098414607573480, 37754824460018231⟩
  | 98 => ⟨35788670146060618, 36451230485258649, 37113790824456680, 37776351163654711, 38438911502852742⟩
  | 99 => ⟨36454305728635289, 37123016554586600, 37791727380537911, 38460438206489222, 39129149032440533⟩
  | 100 => ⟨37126091797963240, 37800953110667831, 38475814423372422, 39150675736077013, 39825537048781604⟩
  | 101 => ⟨37804028354044471, 38485040153502342, 39166051952960213, 39847063752418084, 40528075551875955⟩
  | 102 => ⟨38488115396878982, 39175277683090133, 39862439969301284, 40549602255512435, 41236764541723586⟩
  | 103 => ⟨39178352926466773, 39871665699431204, 40564978472395635, 41258291245360066, 41951604018324497⟩
  | 104 => ⟨39874740942807844, 40574204202525555, 41273667462243266, 41973130721960977, 42672593981678688⟩
  | 105 => ⟨40577279445902195, 41282893192373186, 41988506938844177, 42694120685315168, 43399734431786159⟩
  | 106 => ⟨41285968435749826, 41997732668974097, 42709496902198368, 43421261135422639, 44133025368646910⟩
  | 107 => ⟨42000807912350737, 42718722632328288, 43436637352305839, 44154552072283390, 44872466792260941⟩
  | _ => defaultCosts

def row21 : ℕ → Costs
  | 0 => ⟨636416160695175, 666652971631535, 757500834481153, 848348697330771, 939196560180389⟩
  | 1 => ⟨666652971631535, 760249634522113, 853846297412691, 947442960303269, 1041039623193847⟩
  | 2 => ⟨600325454431235, 679293938238550, 758262422045865, 837230905853180, 916199389660495⟩
  | 3 => ⟨682523802797142, 767952015721641, 853380228646140, 938808441570639, 1024236654495138⟩
  | 4 => ⟨771181880280233, 863069822321916, 954957764363599, 1046845706405282, 1138733648446965⟩
  | 5 => ⟨866299686880508, 964647358039375, 1062995029198242, 1161342700357109, 1259690371515976⟩
  | 6 => ⟨967877222597967, 1072684622874018, 1177492023150069, 1282299423426120, 1387106823702171⟩
  | 7 => ⟨1075914487432610, 1187181616825845, 1298448746219080, 1409715875612315, 1520983005005550⟩
  | 8 => ⟨1190411481384437, 1308138339894856, 1425865198405275, 1543592056915694, 1661318915426113⟩
  | 9 => ⟨1311368204453448, 1435554792081051, 1559741379708654, 1683927967336257, 1808114554963860⟩
  | 10 => ⟨1438784656639643, 1569430973384430, 1700077290129217, 1830723606874004, 1961369923618791⟩
  | 11 => ⟨1572660837943022, 1709766883804993, 1846872929666964, 1983978975528935, 2121085021390906⟩
  | 12 => ⟨1712996748363585, 1856562523342740, 2000128298321895, 2143694073301050, 2287259848280205⟩
  | 13 => ⟨1859792387901332, 2009817891997671, 2159843396094010, 2309868900190349, 2459894404286688⟩
  | 14 => ⟨2013047756556263, 2169532989769786, 2326018222983309, 2482503456196832, 2638988689410355⟩
  | 15 => ⟨2172762854328378, 2335707816659085, 2498652778989792, 2661597741320499, 2824542703651206⟩
  | 16 => ⟨2338937681217677, 2508342372665568, 2677747064113459, 2847151755561350, 3016556447009241⟩
  | 17 => ⟨2511572237224160, 2687436657789235, 2863301078354310, 3039165498919385, 3215029919484460⟩
  | 18 => ⟨2690666522347827, 2872990672030086, 3055314821712345, 3237638971394604, 3419963121076863⟩
  | 19 => ⟨2876220536588678, 3065004415388121, 3253788294187564, 3442572172987007, 3631356051786450⟩
  | 20 => ⟨3068234279946713, 3263477887863340, 3458721495779967, 3653965103696594, 3849208711613221⟩
  | 21 => ⟨3266707752421932, 3468411089455743, 3670114426489554, 3871817763523365, 4073521100557176⟩
  | 22 => ⟨3471640954014335, 3679804020165330, 3887967086316325, 4096130152467320, 4304293218618315⟩
  | 23 => ⟨3683033884723922, 3897656679992101, 4112279475260280, 4326902270528459, 4541525065796638⟩
  | 24 => ⟨3900886544550693, 4121969068936056, 4343051593321419, 4564134117706782, 4785216642092145⟩
  | 25 => ⟨4125198933494648, 4352741186997195, 4580283440499742, 4807825694002289, 5035367947504836⟩
  | 26 => ⟨4355971051555787, 4589973034175518, 4823975016795249, 5057976999414980, 5291978982034711⟩
  | 27 => ⟨4593202898734110, 4833664610471025, 5074126322207940, 5314588033944855, 5555049745681770⟩
  | 28 => ⟨4836894475029617, 5083815915883716, 5330737356737815, 5577658797591914, 5824580238446013⟩
  | 29 => ⟨5087045780442308, 5340426950413591, 5593808120384874, 5847189290356157, 6100570460327440⟩
  | 30 => ⟨5343656814972183, 5603497714060650, 5863338613149117, 6123179512237584, 6383020411326051⟩
  | 31 => ⟨5606727578619242, 5873028206824893, 6139328835030544, 6405629463236195, 6671930091441846⟩
  | 32 => ⟨5876258071383485, 6149018428706320, 6421778786029155, 6694539143351990, 6967299500674825⟩
  | 33 => ⟨6152248293264912, 6431468379704931, 6710688466144950, 6989908552584969, 7269128639024988⟩
  | 34 => ⟨6434698244263523, 6720378059820726, 7006057875377929, 7291737690935132, 7577417506492335⟩
  | 35 => ⟨6723607924379318, 7015747469053705, 7307887013728092, 7600026558402479, 7892166103076866⟩
  | 36 => ⟨7018977333612297, 7317576607403868, 7616175881195439, 7914775154987010, 8213374428778581⟩
  | 37 => ⟨7320806471962460, 7625865474871215, 7930924477779970, 8235983480688725, 8541042483597480⟩
  | 38 => ⟨7629095339429807, 7940614071455746, 8252132803481685, 8563651535507624, 8875170267533563⟩
  | 39 => ⟨7943843936014338, 8261822397157461, 8579800858300584, 8897779319443707, 9215757780586830⟩
  | 40 => ⟨8265052261716053, 8589490451976360, 8913928642236667, 9238366832496974, 9562805022757281⟩
  | 41 => ⟨8592720316534952, 8923618235912443, 9254516155289934, 9585414074667425, 9916311994044916⟩
  | 42 => ⟨8926848100471035, 9264205748965710, 9601563397460385, 9938921045955060, 10276278694449735⟩
  | 43 => ⟨9267435613524302, 9611252991136161, 9955070368748020, 10298887746359879, 10642705123971738⟩
  | 44 => ⟨9614482855694753, 9964759962423796, 10315037069152839, 10665314175881882, 11015591282610925⟩
  | 45 => ⟨9967989826982388, 10324726662828615, 10681463498674842, 11038200334521069, 11394937170367296⟩
  | 46 => ⟨10327956527387207, 10691153092350618, 11054349657314029, 11417546222277440, 11780742787240851⟩
  | 47 => ⟨10694382956909210, 11064039250989805, 11433695545070400, 11803351839150995, 12173008133231590⟩
  | 48 => ⟨11067269115548397, 11443385138746176, 11819501161943955, 12195617185141734, 12571733208339513⟩
  | 49 => ⟨11446615003304768, 11829190755619731, 12211766507934694, 12594342260249657, 12976918012564620⟩
  | 50 => ⟨11832420620178323, 12221456101610470, 12610491583042617, 12999527064474764, 13388562545906911⟩
  | 51 => ⟨12224685966169062, 12620181176718393, 13015676387267724, 13411171597817055, 13806666808366386⟩
  | 52 => ⟨12623411041276985, 13025365980943500, 13427320920610015, 13829275860276530, 14231230799943045⟩
  | 53 => ⟨13028595845502092, 13437010514285791, 13845425183069490, 14253839851853189, 14662254520636888⟩
  | 54 => ⟨13440240378844383, 13855114776745266, 14269989174646149, 14684863572547032, 15099737970447915⟩
  | 55 => ⟨13858344641303858, 14279678768321925, 14701012895339992, 15122347022358059, 15543681149376126⟩
  | 56 => ⟨14282908632880517, 14710702489015768, 15138496345151019, 15566290201286270, 15994084057421521⟩
  | 57 => ⟨14713932353574360, 15148185938826795, 15582439524079230, 16016693109331665, 16450946694584100⟩
  | 58 => ⟨15151415803385387, 15592129117755006, 16032842432124625, 16473555746494244, 16914269060863863⟩
  | 59 => ⟨15595358982313598, 16042532025800401, 16489705069287204, 16936878112774007, 17384051156260810⟩
  | 60 => ⟨16045761890358993, 16499394662962980, 16953027435566967, 17406660208170954, 17860292980774941⟩
  | 61 => ⟨16502624527521572, 16962717029242743, 17422809530963914, 17882902032685085, 18342994534406256⟩
  | 62 => ⟨16965946893801335, 17432499124639690, 17899051355478045, 18365603586316400, 18832155817154755⟩
  | 63 => ⟨17435728989198282, 17908740949153821, 18381752909109360, 18854764869064899, 19327776829020438⟩
  | 64 => ⟨17911970813712413, 18391442502785136, 18870914191857859, 19350385880930582, 19829857570003305⟩
  | 65 => ⟨18394672367343728, 18880603785533635, 19366535203723542, 19852466621913449, 20338398040103356⟩
  | 66 => ⟨18883833650092227, 19376224797399318, 19868615944706409, 20361007092013500, 20853398239320591⟩
  | 67 => ⟨19379454661957910, 19878305538382185, 20377156414806460, 20876007291230735, 21374858167655010⟩
  | 68 => ⟨19881535402940777, 20386846008482236, 20892156614023695, 21397467219565154, 21902777825106613⟩
  | 69 => ⟨20390075873040828, 20901846207699471, 21413616542358114, 21925386877016757, 22437157211675400⟩
  | 70 => ⟨20905076072258063, 21423306136033890, 21941536199809717, 22459766263585544, 22977996327361371⟩
  | 71 => ⟨21426536000592482, 21951225793485493, 22475915586378504, 23000605379271515, 23525295172164526⟩
  | 72 => ⟨21954455658044085, 22485605180054280, 23016754702064475, 23547904224074670, 24079053746084865⟩
  | 73 => ⟨22488835044612872, 23026444295740251, 23564053546867630, 24101662797995009, 24639272049122388⟩
  | 74 => ⟨23029674160298843, 23573743140543406, 24117812120787969, 24661881101032532, 25205950081277095⟩
  | 75 => ⟨23576973005101998, 24127501714463745, 24678030423825492, 25228559133187239, 25779087842548986⟩
  | 76 => ⟨24130731579022337, 24687720017501268, 25244708455980199, 25801696894459130, 26358685332938061⟩
  | 77 => ⟨24690949882059860, 25254398049655975, 25817846217252090, 26381294384848205, 26944742552444320⟩
  | 78 => ⟨25257627914214567, 25827535810927866, 26397443707641165, 26967351604354464, 27537259501067763⟩
  | 79 => ⟨25830765675486458, 26407133301316941, 26983500927147424, 27559868552977907, 28136236178808390⟩
  | 80 => ⟨26410363165875533, 26993190520823200, 27576017875770867, 28158845230718534, 28741672585666201⟩
  | 81 => ⟨26996420385381792, 27585707469446643, 28174994553511494, 28764281637576345, 29353568721641196⟩
  | 82 => ⟨27588937334005235, 28184684147187270, 28780430960369305, 29376177773551340, 29971924586733375⟩
  | 83 => ⟨28187914011745862, 28790120554045081, 29392327096344300, 29994533638643519, 30596740180942738⟩
  | 84 => ⟨28793350418603673, 29402016690020076, 30010682961436479, 30619349232852882, 31228015504269285⟩
  | 85 => ⟨29405246554578668, 30020372555112255, 30635498555645842, 31250624556179429, 31865750556713016⟩
  | 86 => ⟨30023602419670847, 30645188149321618, 31266773878972389, 31888359608623160, 32509945338273931⟩
  | 87 => ⟨30648418013880210, 31276463472648165, 31904508931416120, 32532554390184075, 33160599848952030⟩
  | 88 => ⟨31279693337206757, 31914198525091896, 32548703712977035, 33183208900862174, 33817714088747313⟩
  | 89 => ⟨31917428389650488, 32558393306652811, 33199358223655134, 33840323140657457, 34481288057659780⟩
  | 90 => ⟨32561623171211403, 33209047817330910, 33856472463450417, 34503897109569924, 35151321755689431⟩
  | 91 => ⟨33212277681889502, 33866162057126193, 34520046432362884, 35173930807599575, 35827815182836266⟩
  | 92 => ⟨33869391921684785, 34529736026038660, 35190080130392535, 35850424234746410, 36510768339100285⟩
  | 93 => ⟨34532965890597252, 35199769724068311, 35866573557539370, 36533377391010429, 37200181224481488⟩
  | 94 => ⟨35202999588626903, 35876263151215146, 36549526713803389, 37222790276391632, 37896053838979875⟩
  | 95 => ⟨35879493015773738, 36559216307479165, 37238939599184592, 37918662890890019, 38598386182595446⟩
  | 96 => ⟨36562446172037757, 37248629192860368, 37934812213682979, 38620995234505590, 39307178255328201⟩
  | 97 => ⟨37251859057418960, 37944501807358755, 38637144557298550, 39329787307238345, 40022430057178140⟩
  | 98 => ⟨37947731671917347, 38646834150974326, 39345936630031305, 40045039109088284, 40744141588145263⟩
  | 99 => ⟨38650064015532918, 39355626223707081, 40061188431881244, 40766750640055407, 41472312848229570⟩
  | 100 => ⟨39358856088265673, 40070878025557020, 40782899962848367, 41494921900139714, 42206943837431061⟩
  | 101 => ⟨40074107890115612, 40792589556524143, 41511071222932674, 42229552889341205, 42948034555749736⟩
  | 102 => ⟨40795819421082735, 41520760816608450, 42245702212134165, 42970643607659880, 43695585003185595⟩
  | 103 => ⟨41523990681167042, 42255391805809941, 42986792930452840, 43718194055095739, 44449595179738638⟩
  | 104 => ⟨42258621670368533, 42996482524128616, 43734343377888699, 44472204231648782, 45210065085408865⟩
  | 105 => ⟨42999712388687208, 43744032971564475, 44488353554441742, 45232674137319009, 45976994720196276⟩
  | 106 => ⟨43747262836123067, 44498043148117518, 45248823460111969, 45999603772106420, 46750384084100871⟩
  | _ => defaultCosts

def row22 : ℕ → Costs
  | 0 => ⟨731730824659934, 764922596164616, 864635340194910, 964348084225204, 1064060828255498⟩
  | 1 => ⟨764922596164616, 867521580237918, 970120564311220, 1072719548384522, 1175318532457824⟩
  | 2 => ⟨683339860804704, 769472459900087, 855605058995470, 941737658090853, 1027870257186236⟩
  | 3 => ⟨772856945640631, 865758516217102, 958660086793573, 1051561657370044, 1144463227946515⟩
  | 4 => ⟨869143001957646, 968813544015205, 1068484086072764, 1168154628130323, 1267825170187882⟩
  | 5 => ⟨972198029755749, 1078637543294396, 1185077056833043, 1291516570371690, 1397956083910337⟩
  | 6 => ⟨1082022029034940, 1195230514054675, 1308438999074410, 1421647484094145, 1534855969113880⟩
  | 7 => ⟨1198614999795219, 1318592456296042, 1438569912796865, 1558547369297688, 1678524825798511⟩
  | 8 => ⟨1321976942036586, 1448723370018497, 1575469798000408, 1702216225982319, 1828962653964230⟩
  | 9 => ⟨1452107855759041, 1585623255222040, 1719138654685039, 1852654054148038, 1986169453611037⟩
  | 10 => ⟨1589007740962584, 1729292111906671, 1869576482850758, 2009860853794845, 2150145224738932⟩
  | 11 => ⟨1732676597647215, 1879729940072390, 2026783282497565, 2173836624922740, 2320889967347915⟩
  | 12 => ⟨1883114425812934, 2036936739719197, 2190759053625460, 2344581367531723, 2498403681437986⟩
  | 13 => ⟨2040321225459741, 2200912510847092, 2361503796234443, 2522095081621794, 2682686367009145⟩
  | 14 => ⟨2204296996587636, 2371657253456075, 2539017510324514, 2706377767192953, 2873738024061392⟩
  | 15 => ⟨2375041739196619, 2549170967546146, 2723300195895673, 2897429424245200, 3071558652594727⟩
  | 16 => ⟨2552555453286690, 2733453653117305, 2914351852947920, 3095250052778535, 3276148252609150⟩
  | 17 => ⟨2736838138857849, 2924505310169552, 3112172481481255, 3299839652792958, 3487506824104661⟩
  | 18 => ⟨2927889795910096, 3122325938702887, 3316762081495678, 3511198224288469, 3705634367081260⟩
  | 19 => ⟨3125710424443431, 3326915538717310, 3528120652991189, 3729325767265068, 3930530881538947⟩
  | 20 => ⟨3330300024457854, 3538274110212821, 3746248195967788, 3954222281722755, 4162196367477722⟩
  | 21 => ⟨3541658595953365, 3756401653189420, 3971144710425475, 4185887767661530, 4400630824897585⟩
  | 22 => ⟨3759786138929964, 3981298167647107, 4202810196364250, 4424322225081393, 4645834253798536⟩
  | 23 => ⟨3984682653387651, 4212963653585882, 4441244653784113, 4669525653982344, 4897806654180575⟩
  | 24 => ⟨4216348139326426, 4451398111005745, 4686448082685064, 4921498054364383, 5156548026043702⟩
  | 25 => ⟨4454782596746289, 4696601539906696, 4938420483067103, 5180239426227510, 5422058369387917⟩
  | 26 => ⟨4699986025647240, 4948573940288735, 5197161854930230, 5445749769571725, 5694337684213220⟩
  | 27 => ⟨4951958426029279, 5207315312151862, 5462672198274445, 5718029084397028, 5973385970519611⟩
  | 28 => ⟨5210699797892406, 5472825655496077, 5734951513099748, 5997077370703419, 6259203228307090⟩
  | 29 => ⟨5476210141236621, 5745104970321380, 6013999799406139, 6282894628490898, 6551789457575657⟩
  | 30 => ⟨5748489456061924, 6024153256627771, 6299817057193618, 6575480857759465, 6851144658325312⟩
  | 31 => ⟨6027537742368315, 6309970514415250, 6592403286462185, 6874836058509120, 7157268830556055⟩
  | 32 => ⟨6313355000155794, 6602556743683817, 6891758487211840, 7180960230739863, 7470161974267886⟩
  | 33 => ⟨6605941229424361, 6901911944433472, 7197882659442583, 7493853374451694, 7789824089460805⟩
  | 34 => ⟨6905296430174016, 7208036116664215, 7510775803154414, 7813515489644613, 8116255176134812⟩
  | 35 => ⟨7211420602404759, 7520929260376046, 7830437918347333, 8139946576318620, 8449455234289907⟩
  | 36 => ⟨7524313746116590, 7840591375568965, 8156869005021340, 8473146634473715, 8789424263926090⟩
  | 37 => ⟨7843975861309509, 8167022462242972, 8490069063176435, 8813115664109898, 9136162265043361⟩
  | 38 => ⟨8170406947983516, 8500222520398067, 8830038092812618, 9159853665227169, 9489669237641720⟩
  | 39 => ⟨8503607006138611, 8840191550034250, 9176776093929889, 9513360637825528, 9849945181721167⟩
  | 40 => ⟨8843576035774794, 9186929551151521, 9530283066528248, 9873636581904975, 10216990097281702⟩
  | 41 => ⟨9190314036892065, 9540436523749880, 9890559010607695, 10240681497465510, 10590803984323325⟩
  | 42 => ⟨9543821009490424, 9900712467829327, 10257603926168230, 10614495384507133, 10971386842846036⟩
  | 43 => ⟨9904096953569871, 10267757383389862, 10631417813209853, 10995078243029844, 11358738672849835⟩
  | 44 => ⟨10271141869130406, 10641571270431485, 11012000671732564, 11382430073033643, 11752859474334722⟩
  | 45 => ⟨10644955756172029, 11022154128954196, 11399352501736363, 11776550874518530, 12153749247300697⟩
  | 46 => ⟨11025538614694740, 11409505958957995, 11793473303221250, 12177440647484505, 12561407991747760⟩
  | 47 => ⟨11412890444698539, 11803626760442882, 12194363076187225, 12585099391931568, 12975835707675911⟩
  | 48 => ⟨11807011246183426, 12204516533408857, 12602021820634288, 12999527107859719, 13397032395085150⟩
  | 49 => ⟨12207901019149401, 12612175277855920, 13016449536562439, 13420723795268958, 13824998053975477⟩
  | 50 => ⟨12615559763596464, 13026602993784071, 13437646223971678, 13848689454159285, 14259732684346892⟩
  | 51 => ⟨13029987479524615, 13447799681193310, 13865611882862005, 14283424084530700, 14701236286199395⟩
  | 52 => ⟨13451184166933854, 13875765340083637, 14300346513233420, 14724927686383203, 15149508859532986⟩
  | 53 => ⟨13879149825824181, 14310499970455052, 14741850115085923, 15173200259716794, 15604550404347665⟩
  | 54 => ⟨14313884456195596, 14752003572307555, 15190122688419514, 15628241804531473, 16066360920643432⟩
  | 55 => ⟨14755388058048099, 15200276145641146, 15645164233234193, 16090052320827240, 16534940408420287⟩
  | 56 => ⟨15203660631381690, 15655317690455825, 16106974749529960, 16558631808604095, 17010288867678230⟩
  | 57 => ⟨15658702176196369, 16117128206751592, 16575554237306815, 17033980267862038, 17492406298417261⟩
  | 58 => ⟨16120512692492136, 16585707694528447, 17050902696564758, 17516097698601069, 17981292700637380⟩
  | 59 => ⟨16589092180268991, 17061056153786390, 17533020127303789, 18004984100821188, 18476948074338587⟩
  | 60 => ⟨17064440639526934, 17543173584525421, 18021906529523908, 18500639474522395, 18979372419520882⟩
  | 61 => ⟨17546558070265965, 18032059986745540, 18517561903225115, 19003063819704690, 19488565736184265⟩
  | 62 => ⟨18035444472486084, 18527715360446747, 19019986248407410, 19512257136368073, 20004528024328736⟩
  | 63 => ⟨18531099846187291, 19030139705629042, 19529179565070793, 20028219424512544, 20527259283954295⟩
  | 64 => ⟨19033524191369586, 19539333022292425, 20045141853215264, 20550950684138103, 21056759515060942⟩
  | 65 => ⟨19542717508032969, 20055295310436896, 20567873112840823, 21080450915244750, 21593028717648677⟩
  | 66 => ⟨20058679796177440, 20578026570062455, 21097373343947470, 21616720117832485, 22136066891717500⟩
  | 67 => ⟨20581411055802999, 21107526801169102, 21633642546535205, 22159758291901308, 22685874037267411⟩
  | 68 => ⟨21110911286909646, 21643796003756837, 22176680720604028, 22709565437451219, 23242450154298410⟩
  | 69 => ⟨21647180489497381, 22186834177825660, 22726487866153939, 23266141554482218, 23805795242810497⟩
  | 70 => ⟨22190218663566204, 22736641323375571, 23283063983184938, 23829486642994305, 24375909302803672⟩
  | 71 => ⟨22740025809116115, 23293217440406570, 23846409071697025, 24399600702987480, 24952792334277935⟩
  | 72 => ⟨23296601926147114, 23856562528918657, 24416523131690200, 24976483734461743, 25536444337233286⟩
  | 73 => ⟨23859947014659201, 24426676588911832, 24993406163164463, 25560135737417094, 26126865311669725⟩
  | 74 => ⟨24430061074652376, 25003559620386095, 25577058166119814, 26150556711853533, 26724055257587252⟩
  | 75 => ⟨25006944106126639, 25587211623341446, 26167479140556253, 26747746657771060, 27328014174985867⟩
  | 76 => ⟨25590596109081990, 26177632597777885, 26764669086473780, 27351705575169675, 27938742063865570⟩
  | 77 => ⟨26181017083518429, 26774822543695412, 27368628003872395, 27962433464049378, 28556238924226361⟩
  | 78 => ⟨26778207029435956, 27378781461094027, 27979355892752098, 28579930324410169, 29180504756068240⟩
  | 79 => ⟨27382165946834571, 27989509349973730, 28596852753112889, 29204196156252048, 29811539559391207⟩
  | 80 => ⟨27992893835714274, 28607006210334521, 29221118584954768, 29835230959575015, 30449343334195262⟩
  | 81 => ⟨28610390696075065, 29231272042176400, 29852153388277735, 30473034734379070, 31093916080480405⟩
  | 82 => ⟨29234656527916944, 29862306845499367, 30489957163081790, 31117607480664213, 31745257798246636⟩
  | 83 => ⟨29865691331239911, 30500110620303422, 31134529909366933, 31768949198430444, 32403368487493955⟩
  | 84 => ⟨30503495106043966, 31144683366588565, 31785871627133164, 32427059887677763, 33068248148222362⟩
  | 85 => ⟨31148067852329109, 31796025084354796, 32443982316380483, 33091939548406170, 33739896780431857⟩
  | 86 => ⟨31799409570095340, 32454135773602115, 33108861977108890, 33763588180615665, 34418314384122440⟩
  | 87 => ⟨32457520259342659, 33119015434330522, 33780510609318385, 34442005784306248, 35103500959294111⟩
  | 88 => ⟨33122399920071066, 33790664066540017, 34458928213008968, 35127192359477919, 35795456505946870⟩
  | 89 => ⟨33794048552280561, 34469081670230600, 35144114788180639, 35819147906130678, 36494181024080717⟩
  | 90 => ⟨34472466155971144, 35154268245402271, 35836070334833398, 36517872424264525, 37199674513695652⟩
  | 91 => ⟨35157652731142815, 35846223792055030, 36534794852967245, 37223365913879460, 37911936974791675⟩
  | 92 => ⟨35849608277795574, 36544948310188877, 37240288342582180, 37935628374975483, 38630968407368786⟩
  | 93 => ⟨36548332795929421, 37250441799803812, 37952550803678203, 38654659807552594, 39356768811426985⟩
  | 94 => ⟨37253826285544356, 37962704260899835, 38671582236255314, 39380460211610793, 40089338186966272⟩
  | 95 => ⟨37966088746640379, 38681735693476946, 39397382640313513, 40113029587150080, 40828676533986647⟩
  | 96 => ⟨38685120179217490, 39407536097535145, 40129952015852800, 40852367934170455, 41574783852488110⟩
  | 97 => ⟨39410920583275689, 40140105473074432, 40869290362873175, 41598475252671918, 42327660142470661⟩
  | 98 => ⟨40143489958814976, 40879443820094807, 41615397681374638, 42351351542654469, 43087305403934300⟩
  | 99 => ⟨40882828305835351, 41625551138596270, 42368273971357189, 43110996804118108, 43853719636879027⟩
  | 100 => ⟨41628935624336814, 42378427428578821, 43127919232820828, 43877411037062835, 44626902841304842⟩
  | 101 => ⟨42381811914319365, 43138072690042460, 43894333465765555, 44650594241488650, 45406855017211745⟩
  | 102 => ⟨43141457175783004, 43904486922987187, 44667516670191370, 45430546417395553, 46193576164599736⟩
  | 103 => ⟨43907871408727731, 44677670127413002, 45447468846098273, 46217267564783544, 46987066283468815⟩
  | 104 => ⟨44681054613153546, 45457622303319905, 46234189993486264, 47010757683652623, 47787325373818982⟩
  | 105 => ⟨45461006789060449, 46244343450707896, 47027680112355343, 47811016774002790, 48594353435650237⟩
  | _ => defaultCosts

def row23 : ℕ → Costs
  | 0 => ⟨836116529808441, 872400701883493, 981390647100607, 1090380592317721, 1199370537534835⟩
  | 1 => ⟨872400701883493, 984414327145663, 1096427952407833, 1208441577670003, 1320455202932173⟩
  | 2 => ⟨773673003648193, 867278960395548, 960884917142903, 1054490873890258, 1148096830637613⟩
  | 3 => ⟨870818067318044, 971502237910391, 1072186408502738, 1172870579095085, 1273554749687432⟩
  | 4 => ⟨975041344832887, 1082803729270226, 1190566113707565, 1298328498144904, 1406090882582243⟩
  | 5 => ⟨1086342836192722, 1201183434475053, 1316024032757384, 1430864631039715, 1545705229322046⟩
  | 6 => ⟨1204722541397549, 1326641353524872, 1448560165652195, 1570478977779518, 1692397789906841⟩
  | 7 => ⟨1330180460447368, 1459177486419683, 1588174512391998, 1717171538364313, 1846168564336628⟩
  | 8 => ⟨1462716593342179, 1598791833159486, 1734867072976793, 1870942312794100, 2007017552611407⟩
  | 9 => ⟨1602330940081982, 1745484393744281, 1888637847406580, 2031791301068879, 2174944754731178⟩
  | 10 => ⟨1749023500666777, 1899255168174068, 2049486835681359, 2199718503188650, 2349950170695941⟩
  | 11 => ⟨1902794275096564, 2060104156448847, 2217414037801130, 2374723919153413, 2532033800505696⟩
  | 12 => ⟨2063643263371343, 2228031358568618, 2392419453765893, 2556807548963168, 2721195644160443⟩
  | 13 => ⟨2231570465491114, 2403036774533381, 2574503083575648, 2745969392617915, 2917435701660182⟩
  | 14 => ⟨2406575881455877, 2585120404343136, 2763664927230395, 2942209450117654, 3120753973004913⟩
  | 15 => ⟨2588659511265632, 2774282247997883, 2959904984730134, 3145527721462385, 3331150458194636⟩
  | 16 => ⟨2777821354920379, 2970522305497622, 3163223256074865, 3355924206652108, 3548625157229351⟩
  | 17 => ⟨2974061412420118, 3173840576842353, 3373619741264588, 3573398905686823, 3773178070109058⟩
  | 18 => ⟨3177379683764849, 3384237062032076, 3591094440299303, 3797951818566530, 4004809196833757⟩
  | 19 => ⟨3387776168954572, 3601711761066791, 3815647353179010, 4029582945291229, 4243518537403448⟩
  | 20 => ⟨3605250867989287, 3826264673946498, 4047278479903709, 4268292285860920, 4489306091818131⟩
  | 21 => ⟨3829803780868994, 4057895800671197, 4285987820473400, 4514079840275603, 4742171860077806⟩
  | 22 => ⟨4061434907593693, 4296605141240888, 4531775374888083, 4766945608535278, 5002115842182473⟩
  | 23 => ⟨4300144248163384, 4542392695655571, 4784641143147758, 5026889590639945, 5269138038132132⟩
  | 24 => ⟨4545931802578067, 4795258463915246, 5044585125252425, 5293911786589604, 5543238447926783⟩
  | 25 => ⟨4798797570837742, 5055202446019913, 5311607321202084, 5568012196384255, 5824417071566426⟩
  | 26 => ⟨5058741552942409, 5322224641969572, 5585707730996735, 5849190820023898, 6112673909051061⟩
  | 27 => ⟨5325763748892068, 5596325051764223, 5866886354636378, 6137447657508533, 6408008960380688⟩
  | 28 => ⟨5599864158686719, 5877503675403866, 6155143192121013, 6432782708838160, 6710422225555307⟩
  | 29 => ⟨5881042782326362, 6165760512888501, 6450478243450640, 6735195974012779, 7019913704574918⟩
  | 30 => ⟨6169299619810997, 6461095564218128, 6752891508625259, 7044687453032390, 7336483397439521⟩
  | 31 => ⟨6464634671140624, 6763508829392747, 7062382987644870, 7361257145896993, 7660131304149116⟩
  | 32 => ⟨6767047936315243, 7073000308412358, 7378952680509473, 7684905052606588, 7990857424703703⟩
  | 33 => ⟨7076539415334854, 7389570001276961, 7702600587219068, 8015631173161175, 8328661759103282⟩
  | 34 => ⟨7393109108199457, 7713217907986556, 8033326707773655, 8353435507560754, 8673544307347853⟩
  | 35 => ⟨7716757014909052, 8043944028541143, 8371131042173234, 8698318055805325, 9025505069437416⟩
  | 36 => ⟨8047483135463639, 8381748362940722, 8716013590417805, 9050278817894888, 9384544045371971⟩
  | 37 => ⟨8385287469863218, 8726630911185293, 9067974352507368, 9409317793829443, 9750661235151518⟩
  | 38 => ⟨8730170018107789, 9078591673274856, 9427013328441923, 9775434983608990, 10123856638776057⟩
  | 39 => ⟨9082130780197352, 9437630649209411, 9793130518221470, 10148630387233529, 10504130256245588⟩
  | 40 => ⟨9441169756131907, 9803747838988958, 10166325921846009, 10528904004703060, 10891482087560111⟩
  | 41 => ⟨9807286945911454, 10176943242613497, 10546599539315540, 10916255836017583, 11285912132719626⟩
  | 42 => ⟨10180482349535993, 10557216860083028, 10933951370630063, 11310685881177098, 11687420391724133⟩
  | 43 => ⟨10560755967005524, 10944568691397551, 11328381415789578, 11712194140181605, 12096006864573632⟩
  | 44 => ⟨10948107798320047, 11338998736557066, 11729889674794085, 12120780613031104, 12511671551268123⟩
  | 45 => ⟨11342537843479562, 11740506995561573, 12138476147643584, 12536445299725595, 12934414451807606⟩
  | 46 => ⟨11744046102484069, 12149093468411072, 12554140834338075, 12959188200265078, 13364235566192081⟩
  | 47 => ⟨12152632575333568, 12564758155105563, 12976883734877558, 13389009314649553, 13801134894421548⟩
  | 48 => ⟨12568297262028059, 12987501055645046, 13406704849262033, 13825908642879020, 14245112436496007⟩
  | 49 => ⟨12991040162567542, 13417322170029521, 13843604177491500, 14269886184953479, 14696168192415458⟩
  | 50 => ⟨13420861276952017, 13854221498258988, 14287581719565959, 14720941940872930, 15154302162179901⟩
  | 51 => ⟨13857760605181484, 14298199040333447, 14738637475485410, 15179075910637373, 15619514345789336⟩
  | 52 => ⟨14301738147255943, 14749254796252898, 15196771445249853, 15644288094246808, 16091804743243763⟩
  | 53 => ⟨14752793903175394, 15207388766017341, 15661983628859288, 16116578491701235, 16571173354543182⟩
  | 54 => ⟨15210927872939837, 15672600949626776, 16134274026313715, 16595947103000654, 17057620179687593⟩
  | 55 => ⟨15676140056549272, 16144891347081203, 16613642637613134, 17082393928145065, 17551145218676996⟩
  | 56 => ⟨16148430454003699, 16624259958380622, 17100089462757545, 17575918967134468, 18051748471511391⟩
  | 57 => ⟨16627799065303118, 17110706783525033, 17593614501746948, 18076522219968863, 18559429938190778⟩
  | 58 => ⟨17114245890447529, 17604231822514436, 18094217754581343, 18584203686648250, 19074189618715157⟩
  | 59 => ⟨17607770929436932, 18104835075348831, 18601899221260730, 19098963367172629, 19596027513084528⟩
  | 60 => ⟨18108374182271327, 18612516542028218, 19116658901785109, 19620801261542000, 20124943621298891⟩
  | 61 => ⟨18616055648950714, 19127276222552597, 19638496796154480, 20149717369756363, 20660937943358246⟩
  | 62 => ⟨19130815329475093, 19649114116921968, 20167412904368843, 20685711691815718, 21204010479262593⟩
  | 63 => ⟨19652653223844464, 20178030225136331, 20703407226428198, 21228784227720065, 21754161229011932⟩
  | 64 => ⟨20181569332058827, 20714024547195686, 21246479762332545, 21778934977469404, 22311390192606263⟩
  | 65 => ⟨20717563654118182, 21257097083100033, 21796630512081884, 22336163941063735, 22875697370045586⟩
  | 66 => ⟨21260636190022529, 21807247832849372, 22353859475676215, 22900471118503058, 23447082761329901⟩
  | 67 => ⟨21810786939771868, 22364476796443703, 22918166653115538, 23471856509787373, 24025546366459208⟩
  | 68 => ⟨22368015903366199, 22928783973883026, 23489552044399853, 24050320114916680, 24611088185433507⟩
  | 69 => ⟨22932323080805522, 23500169365167341, 24068015649529160, 24635861933890979, 25203708218252798⟩
  | 70 => ⟨23503708472089837, 24078632970296648, 24653557468503459, 25228481966710270, 25803406464917081⟩
  | 71 => ⟨24082172077219144, 24664174789270947, 25246177501322750, 25828180213374553, 26410182925426356⟩
  | 72 => ⟨24667713896193443, 25256794822090238, 25845875747987033, 26434956673883828, 27024037599780623⟩
  | 73 => ⟨25260333929012734, 25856493068754521, 26452652208496308, 27048811348238095, 27644970487979882⟩
  | 74 => ⟨25860032175677017, 26463269529263796, 27066506882850575, 27669744236437354, 28272981590024133⟩
  | 75 => ⟨26466808636186292, 27077124203618063, 27687439771049834, 28297755338481605, 28908070905913376⟩
  | 76 => ⟨27080663310540559, 27698057091817322, 28315450873094085, 28932844654370848, 29550238435647611⟩
  | 77 => ⟨27701596198739818, 28326068193861573, 28950540188983328, 29575012184105083, 30199484179226838⟩
  | 78 => ⟨28329607300784069, 28961157509750816, 29592707718717563, 30224257927684310, 30855808136651057⟩
  | 79 => ⟨28964696616673312, 29603325039485051, 30241953462296790, 30880581885108529, 31519210307920268⟩
  | 80 => ⟨29606864146407547, 30252570783064278, 30898277419721009, 31543984056377740, 32189690693034471⟩
  | 81 => ⟨30256109889986774, 30908894740488497, 31561679590990220, 32214464441491943, 32867249291993666⟩
  | 82 => ⟨30912433847410993, 31572296911757708, 32232159976104423, 32892023040451138, 33551886104797853⟩
  | 83 => ⟨31575836018680204, 32242777296871911, 32909718575063618, 33576659853255325, 34243601131447032⟩
  | 84 => ⟨32246316403794407, 32920335895831106, 33594355387867805, 34268374879904504, 34942394371941203⟩
  | 85 => ⟨32923875002753602, 33604972708635293, 34286070414516984, 34967168120398675, 35648265826280366⟩
  | 86 => ⟨33608511815557789, 34296687735284472, 34984863655011155, 35673039574737838, 36361215494464521⟩
  | 87 => ⟨34300226842206968, 34995480975778643, 35690735109350318, 36385989242921993, 37081243376493668⟩
  | 88 => ⟨34999020082701139, 35701352430117806, 36403684777534473, 37106017124951140, 37808349472367807⟩
  | 89 => ⟨35704891537040302, 36414302098301961, 37123712659563620, 37833123220825279, 38542533782086938⟩
  | 90 => ⟨36417841205224457, 37134329980331108, 37850818755437759, 38567307530544410, 39283796305651061⟩
  | 91 => ⟨37137869087253604, 37861436076205247, 38585003065156890, 39308570054108533, 40032137043060176⟩
  | 92 => ⟨37864975183127743, 38595620385924378, 39326265588721013, 40056910791517648, 40787555994314283⟩
  | 93 => ⟨38599159492846874, 39336882909488501, 40074606326130128, 40812329742771755, 41550053159413382⟩
  | 94 => ⟨39340422016410997, 40085223646897616, 40830025277384235, 41574826907870854, 42319628538357473⟩
  | 95 => ⟨40088762753820112, 40840642598151723, 41592522442483334, 42344402286814945, 43096282131146556⟩
  | 96 => ⟨40844181705074219, 41603139763250822, 42362097821427425, 43121055879604028, 43880013937780631⟩
  | 97 => ⟨41606678870173318, 42372715142194913, 43138751414216508, 43904787686238103, 44670823958259698⟩
  | 98 => ⟨42376254249117409, 43149368734983996, 43922483220850583, 44695597706717170, 45468712192583757⟩
  | 99 => ⟨43152907841906492, 43933100541618071, 44713293241329650, 45493485941041229, 46273678640752808⟩
  | 100 => ⟨43936639648540567, 44723910562097138, 45511181475653709, 46298452389210280, 47085723302766851⟩
  | 101 => ⟨44727449669019634, 45521798796421197, 46316147923822760, 47110497051224323, 47904846178625886⟩
  | 102 => ⟨45525337903343693, 46326765244590248, 47128192585836803, 47929619927083358, 48731047268329913⟩
  | 103 => ⟨46330304351512744, 47138809906604291, 47947315461695838, 48755821016787385, 49564326571878932⟩
  | 104 => ⟨47142349013526787, 47957932782463326, 48773516551399865, 49589100320336404, 50404684089272943⟩
  | _ => defaultCosts

def row24 : ℕ → Costs
  | 0 => ⟨949985596146840, 989499608794310, 1108179075204388, 1226858541614466, 1345538008024544⟩
  | 1 => ⟨989499608794310, 1111340195251492, 1233180781708674, 1355021368165856, 1476861954623038⟩
  | 2 => ⟨871634125325606, 973022682088837, 1074411238852068, 1175799795615299, 1277188352378530⟩
  | 3 => ⟨976716410193285, 1085492423165412, 1194268436137539, 1303044449109666, 1411820462081793⟩
  | 4 => ⟨1089186151269860, 1205349620450883, 1321513089631906, 1437676558812929, 1553840027993952⟩
  | 5 => ⟨1209043348555331, 1332594273945250, 1456145199335169, 1579696124725088, 1703247050115007⟩
  | 6 => ⟨1336288002049698, 1467226383648513, 1598164765247328, 1729103146846143, 1860041528444958⟩
  | 7 => ⟨1470920111752961, 1609245949560672, 1747571787368383, 1885897625176094, 2024223462983805⟩
  | 8 => ⟨1612939677665120, 1758652971681727, 1904366265698334, 2050079559714941, 2195792853731548⟩
  | 9 => ⟨1762346699786175, 1915447450011678, 2068548200237181, 2221648950462684, 2374749700688187⟩
  | 10 => ⟨1919141178116126, 2079629384550525, 2240117590984924, 2400605797419323, 2561094003853722⟩
  | 11 => ⟨2083323112654973, 2251198775298268, 2419074437941563, 2586950100584858, 2754825763228153⟩
  | 12 => ⟨2254892503402716, 2430155622254907, 2605418741107098, 2780681859959289, 2955944978811480⟩
  | 13 => ⟨2433849350359355, 2616499925420442, 2799150500481529, 2981801075542616, 3164451650603703⟩
  | 14 => ⟨2620193653524890, 2810231684794873, 3000269716064856, 3190307747334839, 3380345778604822⟩
  | 15 => ⟨2813925412899321, 3011350900378200, 3208776387857079, 3406201875335958, 3603627362814837⟩
  | 16 => ⟨3015044628482648, 3219857572170423, 3424670515858198, 3629483459545973, 3834296403233748⟩
  | 17 => ⟨3223551300274871, 3435751700171542, 3647952100068213, 3860152499964884, 4072352899861555⟩
  | 18 => ⟨3439445428275990, 3659033284381557, 3878621140487124, 4098208996592691, 4317796852698258⟩
  | 19 => ⟨3662727012486005, 3889702324800468, 4116677637114931, 4343652949429394, 4570628261743857⟩
  | 20 => ⟨3893396052904916, 4127758821428275, 4362121589951634, 4596484358474993, 4830847126998352⟩
  | 21 => ⟨4131452549532723, 4373202774264978, 4614952998997233, 4856703223729488, 5098453448461743⟩
  | 22 => ⟨4376896502369426, 4626034183310577, 4875171864251728, 5124309545192879, 5373447226134030⟩
  | 23 => ⟨4629727911415025, 4886253048565072, 5142778185715119, 5399303322865166, 5655828460015213⟩
  | 24 => ⟨4889946776669520, 5153859370028463, 5417771963387406, 5681684556746349, 5945597150105292⟩
  | 25 => ⟨5157553098132911, 5428853147700750, 5700153197268589, 5971453246836428, 6242753296404267⟩
  | 26 => ⟨5432546875805198, 5711234381581933, 5989921887358668, 6268609393135403, 6547296898912138⟩
  | 27 => ⟨5714928109686381, 6001003071672012, 6287078033657643, 6573152995643274, 6859227957628905⟩
  | 28 => ⟨6004696799776460, 6298159217970987, 6591621636165514, 6885084054360041, 7178546472554568⟩
  | 29 => ⟨6301852946075435, 6602702820478858, 6903552694882281, 7204402569285704, 7505252443689127⟩
  | 30 => ⟨6606396548583306, 6914633879195625, 7222871209807944, 7531108540420263, 7839345871032582⟩
  | 31 => ⟨6918327607300073, 7233952394121288, 7549577180942503, 7865201967763718, 8180826754584933⟩
  | 32 => ⟨7237646122225736, 7560658365255847, 7883670608285958, 8206682851316069, 8529695094346180⟩
  | 33 => ⟨7564352093360295, 7894751792599302, 8225151491838309, 8555551191077316, 8885950890316323⟩
  | 34 => ⟨7898445520703750, 8236232676151653, 8574019831599556, 8911806987047459, 9249594142495362⟩
  | 35 => ⟨8239926404256101, 8585101015912900, 8930275627569699, 9275450239226498, 9620624850883297⟩
  | 36 => ⟨8588794744017348, 8941356811883043, 9293918879748738, 9646480947614433, 9999043015480128⟩
  | 37 => ⟨8945050539987491, 9305000064062082, 9664949588136673, 10024899112211264, 10384848636285855⟩
  | 38 => ⟨9308693792166530, 9676030772450017, 10043367752733504, 10410704733016991, 10778041713300478⟩
  | 39 => ⟨9679724500554465, 10054448937046848, 10429173373539231, 10803897810031614, 11178622246523997⟩
  | 40 => ⟨10058142665151296, 10440254557852575, 10822366450553854, 11204478343255133, 11586590235956412⟩
  | 41 => ⟨10443948285957023, 10833447634867198, 11222946983777373, 11612446332687548, 12001945681597723⟩
  | 42 => ⟨10837141362971646, 11234028168090717, 11630914973209788, 12027801778328859, 12424688583447930⟩
  | 43 => ⟨11237721896195165, 11641996157523132, 12046270418851099, 12450544680179066, 12854818941507033⟩
  | 44 => ⟨11645689885627580, 12057351603164443, 12469013320701306, 12880675038238169, 13292336755775032⟩
  | 45 => ⟨12061045331268891, 12480094505014650, 12899143678760409, 13318192852506168, 13737242026251927⟩
  | 46 => ⟨12483788233119098, 12910224863073753, 13336661493028408, 13763098122983063, 14189534752937718⟩
  | 47 => ⟨12913918591178201, 13347742677341752, 13781566763505303, 14215390849668854, 14649214935832405⟩
  | 48 => ⟨13351436405446200, 13792647947818647, 14233859490191094, 14675071032563541, 15116282574935988⟩
  | 49 => ⟨13796341675923095, 14244940674504438, 14693539673085781, 15142138671667124, 15590737670248467⟩
  | 50 => ⟨14248634402608886, 14704620857399125, 15160607312189364, 15616593766979603, 16072580221769842⟩
  | 51 => ⟨14708314585503573, 15171688496502708, 15635062407501843, 16098436318500978, 16561810229500113⟩
  | 52 => ⟨15175382224607156, 15646143591815187, 16116904959023218, 16587666326231249, 17058427693439280⟩
  | 53 => ⟨15649837319919635, 16127986143336562, 16606134966753489, 17084283790170416, 17562432613587343⟩
  | 54 => ⟨16131679871441010, 16617216151066833, 17102752430692656, 17588288710318479, 18073824989944302⟩
  | 55 => ⟨16620909879171281, 17113833615006000, 17606757350840719, 18099681086675438, 18592604822510157⟩
  | 56 => ⟨17117527343110448, 17617838535154063, 18118149727197678, 18618460919241293, 19118772111284908⟩
  | 57 => ⟨17621532263258511, 18129230911511022, 18636929559763533, 19144628208016044, 19652326856268555⟩
  | 58 => ⟨18132924639615470, 18648010744076877, 19163096848538284, 19678182952999691, 20193269057461098⟩
  | 59 => ⟨18651704472181325, 19174178032851628, 19696651593521931, 20219125154192234, 20741598714862537⟩
  | 60 => ⟨19177871760956076, 19707732777835275, 20237593794714474, 20767454811593673, 21297315828472872⟩
  | 61 => ⟨19711426505939723, 20248674979027818, 20785923452115913, 21323171925204008, 21860420398292103⟩
  | 62 => ⟨20252368707132266, 20797004636429257, 21341640565726248, 21886276495023239, 22430912424320230⟩
  | 63 => ⟨20800698364533705, 21352721750039592, 21904745135545479, 22456768521051366, 23008791906557253⟩
  | 64 => ⟨21356415478144040, 21915826319858823, 22475237161573606, 23034648003288389, 23594058845003172⟩
  | 65 => ⟨21919520047963271, 22486318345886950, 23053116643810629, 23619914941734308, 24186713239657987⟩
  | 66 => ⟨22490012073991398, 23064197828123973, 23638383582256548, 24212569336389123, 24786755090521698⟩
  | 67 => ⟨23067891556228421, 23649464766569892, 24231037976911363, 24812611187252834, 25394184397594305⟩
  | 68 => ⟨23653158494674340, 24242119161224707, 24831079827775074, 25420040494325441, 26009001160875808⟩
  | 69 => ⟨24245812889329155, 24842161012088418, 25438509134847681, 26034857257606944, 26631205380366207⟩
  | 70 => ⟨24845854740192866, 25449590319161025, 26053325898129184, 26657061477097343, 27260797056065502⟩
  | 71 => ⟨25453284047265473, 26064407082442528, 26675530117619583, 27286653152796638, 27897776187973693⟩
  | 72 => ⟨26068100810546976, 26686611301932927, 27305121793318878, 27923632284704829, 28542142776090780⟩
  | 73 => ⟨26690305030037375, 27316202977632222, 27942100925227069, 28567998872821916, 29193896820416763⟩
  | 74 => ⟨27319896705736670, 27953182109540413, 28586467513344156, 29219752917147899, 29853038320951642⟩
  | 75 => ⟨27956875837644861, 28597548697657500, 29238221557670139, 29878894417682778, 30519567277695417⟩
  | 76 => ⟨28601242425761948, 29249302741983483, 29897363058205018, 30545423374426553, 31193483690648088⟩
  | 77 => ⟨29252996470087931, 29908444242518362, 30563892014948793, 31219339787379224, 31874787559809655⟩
  | 78 => ⟨29912137970622810, 30574973199262137, 31237808427901464, 31900643656540791, 32563478885180118⟩
  | 79 => ⟨30578666927366585, 31248889612214808, 31919112297063031, 32589334981911254, 33259557666759477⟩
  | 80 => ⟨31252583340319256, 31930193481376375, 32607803622433494, 33285413763490613, 33963023904547732⟩
  | 81 => ⟨31933887209480823, 32618884806746838, 33303882404012853, 33988880001278868, 34673877598544883⟩
  | 82 => ⟨32622578534851286, 33314963588326197, 34007348641801108, 34699733695276019, 35392118748750930⟩
  | 83 => ⟨33318657316430645, 34018429826114452, 34718202335798259, 35417974845482066, 36117747355165873⟩
  | 84 => ⟨34022123554218900, 34729283520111603, 35436443486004306, 36143603451897009, 36850763417789712⟩
  | 85 => ⟨34732977248216051, 35447524670317650, 36162072092419249, 36876619514520848, 37591166936622447⟩
  | 86 => ⟨35451218398422098, 36173153276732593, 36895088155043088, 37617023033353583, 38338957911664078⟩
  | 87 => ⟨36176847004837041, 36906169339356432, 37635491673875823, 38364814008395214, 39094136342914605⟩
  | 88 => ⟨36909863067460880, 37646572858189167, 38383282648917454, 39119992439645741, 39856702230374028⟩
  | 89 => ⟨37650266586293615, 38394363833230798, 39138461080167981, 39882558327105164, 40626655574042347⟩
  | 90 => ⟨38398057561335246, 39149542264481325, 39901026967627404, 40652511670773483, 41403996373919562⟩
  | 91 => ⟨39153235992585773, 39912108151940748, 40670980311295723, 41429852470650698, 42188724630005673⟩
  | 92 => ⟨39915801880045196, 40682061495609067, 41448321111172938, 42214580726736809, 42980840342300680⟩
  | 93 => ⟨40685755223713515, 41459402295486282, 42233049367259049, 43006696439031816, 43780343510804583⟩
  | 94 => ⟨41463096023590730, 42244130551572393, 43025165079554056, 43806199607535719, 44587234135517382⟩
  | 95 => ⟨42247824279676841, 43036246263867400, 43824668248057959, 44613090232248518, 45401512216439077⟩
  | 96 => ⟨43039939991971848, 43835749432371303, 44631558872770758, 45427368313170213, 46223177753569668⟩
  | 97 => ⟨43839443160475751, 44642640057084102, 45445836953692453, 46249033850300804, 47052230746909155⟩
  | 98 => ⟨44646333785188550, 45456918138005797, 46267502490823044, 47078086843640291, 47888671196457538⟩
  | 99 => ⟨45460611866110245, 46278583675136388, 47096555484162531, 47914527293188674, 48732499102214817⟩
  | 100 => ⟨46282277403240836, 47107636668475875, 47932995933710914, 48758355198945953, 49583714464180992⟩
  | 101 => ⟨47111330396580323, 47944077118024258, 48776823839468193, 49609570560912128, 50442317282356063⟩
  | 102 => ⟨47947770846128706, 48787905023781537, 49628039201434368, 50468173379087199, 51308307556740030⟩
  | 103 => ⟨48791598751885985, 49639120385747712, 50486642019609439, 51334163653471166, 52181685287332893⟩
  | _ => defaultCosts

def row25 : ℕ → Costs
  | 0 => ⟨1073750343681275, 1116631636903211, 1245412944512397, 1374194252121583, 1502975559730769⟩
  | 1 => ⟨1116631636903211, 1248711504561549, 1380791372219887, 1512871239878225, 1644951107536563⟩
  | 2 => ⟨977532468200847, 1087012867343858, 1196493266486869, 1305973665629880, 1415454064772891⟩
  | 3 => ⟨1090861216630258, 1208038314346069, 1325215412061880, 1442392509777691, 1559569607493502⟩
  | 4 => ⟨1211886663632469, 1336760459921080, 1461634256209691, 1586508052498302, 1711381848786913⟩
  | 5 => ⟨1340608809207480, 1473179304068891, 1605749798930302, 1738320293791713, 1870890788653124⟩
  | 6 => ⟨1477027653355291, 1617294846789502, 1757562040223713, 1897829233657924, 2038096427092135⟩
  | 7 => ⟨1621143196075902, 1769107088082913, 1917070980089924, 2065034872096935, 2212998764103946⟩
  | 8 => ⟨1772955437369313, 1928616027949124, 2084276618528935, 2239937209108746, 2395597799688557⟩
  | 9 => ⟨1932464377235524, 2095821666388135, 2259178955540746, 2422536244693357, 2585893533845968⟩
  | 10 => ⟨2099670015674535, 2270724003399946, 2441777991125357, 2612831978850768, 2783885966576179⟩
  | 11 => ⟨2274572352686346, 2453323038984557, 2632073725282768, 2810824411580979, 2989575097879190⟩
  | 12 => ⟨2457171388270957, 2643618773141968, 2830066158012979, 3016513542883990, 3202960927755001⟩
  | 13 => ⟨2647467122428368, 2841611205872179, 3035755289315990, 3229899372759801, 3424043456203612⟩
  | 14 => ⟨2845459555158579, 3047300337175190, 3249141119191801, 3450981901208412, 3652822683225023⟩
  | 15 => ⟨3051148686461590, 3260686167051001, 3470223647640412, 3679761128229823, 3889298608819234⟩
  | 16 => ⟨3264534516337401, 3481768695499612, 3699002874661823, 3916237053824034, 4133471232986245⟩
  | 17 => ⟨3485617044786012, 3710547922521023, 3935478800256034, 4160409677991045, 4385340555726056⟩
  | 18 => ⟨3714396271807423, 3947023848115234, 4179651424423045, 4412279000730856, 4644906577038667⟩
  | 19 => ⟨3950872197401634, 4191196472282245, 4431520747162856, 4671845022043467, 4912169296924078⟩
  | 20 => ⟨4195044821568645, 4443065795022056, 4691086768475467, 4939107741928878, 5187128715382289⟩
  | 21 => ⟨4446914144308456, 4702631816334667, 4958349488360878, 5214067160387089, 5469784832413300⟩
  | 22 => ⟨4706480165621067, 4969894536220078, 5233308906819089, 5496723277418100, 5760137648017111⟩
  | 23 => ⟨4973742885506478, 5244853954678289, 5515965023850100, 5787076093021911, 6058187162193722⟩
  | 24 => ⟨5248702303964689, 5527510071709300, 5806317839453911, 6085125607198522, 6363933374943133⟩
  | 25 => ⟨5531358420995700, 5817862887313111, 6104367353630522, 6390871819947933, 6677376286265344⟩
  | 26 => ⟨5821711236599511, 6115912401489722, 6410113566379933, 6704314731270144, 6998515896160355⟩
  | 27 => ⟨6119760750776122, 6421658614239133, 6723556477702144, 7025454341165155, 7327352204628166⟩
  | 28 => ⟨6425506963525533, 6735101525561344, 7044696087597155, 7354290649632966, 7663885211668777⟩
  | 29 => ⟨6738949874847744, 7056241135456355, 7373532396064966, 7690823656673577, 8008114917282188⟩
  | 30 => ⟨7060089484742755, 7385077443924166, 7710065403105577, 8035053362286988, 8360041321468399⟩
  | 31 => ⟨7388925793210566, 7721610450964777, 8054295108718988, 8386979766473199, 8719664424227410⟩
  | 32 => ⟨7725458800251177, 8065840156578188, 8406221512905199, 8746602869232210, 9086984225559221⟩
  | 33 => ⟨8069688505864588, 8417766560764399, 8765844615664210, 9113922670564021, 9462000725463832⟩
  | 34 => ⟨8421614910050799, 8777389663523410, 9133164416996021, 9488939170468632, 9844713923941243⟩
  | 35 => ⟨8781238012809810, 9144709464855221, 9508180916900632, 9871652368946043, 10235123820991454⟩
  | 36 => ⟨9148557814141621, 9519725964759832, 9890894115378043, 10262062265996254, 10633230416614465⟩
  | 37 => ⟨9523574314046232, 9902439163237243, 10281304012428254, 10660168861619265, 11039033710810276⟩
  | 38 => ⟨9906287512523643, 10292849060287454, 10679410608051265, 11065972155815076, 11452533703578887⟩
  | 39 => ⟨10296697409573854, 10690955655910465, 11085213902247076, 11479472148583687, 11873730394920298⟩
  | 40 => ⟨10694804005196865, 11096758950106276, 11498713895015687, 11900668839925098, 12302623784834509⟩
  | 41 => ⟨11100607299392676, 11510258942874887, 11919910586357098, 12329562229839309, 12739213873321520⟩
  | 42 => ⟨11514107292161287, 11931455634216298, 12348803976271309, 12766152318326320, 13183500660381331⟩
  | 43 => ⟨11935303983502698, 12360349024130509, 12785394064758320, 13210439105386131, 13635484146013942⟩
  | 44 => ⟨12364197373416909, 12796939112617520, 13229680851818131, 13662422591018742, 14095164330219353⟩
  | 45 => ⟨12800787461903920, 13241225899677331, 13681664337450742, 14122102775224153, 14562541212997564⟩
  | 46 => ⟨13245074248963731, 13693209385309942, 14141344521656153, 14589479658002364, 15037614794348575⟩
  | 47 => ⟨13697057734596342, 14152889569515353, 14608721404434364, 15064553239353375, 15520385074272386⟩
  | 48 => ⟨14156737918801753, 14620266452293564, 15083794985785375, 15547323519277186, 16010852052768997⟩
  | 49 => ⟨14624114801579964, 15095340033644575, 15566565265709186, 16037790497773797, 16509015729838408⟩
  | 50 => ⟨15099188382930975, 15578110313568386, 16057032244205797, 16535954174843208, 17014876105480619⟩
  | 51 => ⟨15581958662854786, 16068577292064997, 16555195921275208, 17041814550485419, 17528433179695630⟩
  | 52 => ⟨16072425641351397, 16566740969134408, 17061056296917419, 17555371624700430, 18049686952483441⟩
  | 53 => ⟨16570589318420808, 17072601344776619, 17574613371132430, 18076625397488241, 18578637423844052⟩
  | 54 => ⟨17076449694063019, 17586158418991630, 18095867143920241, 18605575868848852, 19115284593777463⟩
  | 55 => ⟨17590006768278030, 18107412191779441, 18624817615280852, 19142223038782263, 19659628462283674⟩
  | 56 => ⟨18111260541065841, 18636362663140052, 19161464785214263, 19686566907288474, 20211669029362685⟩
  | 57 => ⟨18640211012426452, 19173009833073463, 19705808653720474, 20238607474367485, 20771406295014496⟩
  | 58 => ⟨19176858182359863, 19717353701579674, 20257849220799485, 20798344740019296, 21338840259239107⟩
  | 59 => ⟨19721202050866074, 20269394268658685, 20817586486451296, 21365778704243907, 21913970922036518⟩
  | 60 => ⟨20273242617945085, 20829131534310496, 21385020450675907, 21940909367041318, 22496798283406729⟩
  | 61 => ⟨20832979883596896, 21396565498535107, 21960151113473318, 22523736728411529, 23087322343349740⟩
  | 62 => ⟨21400413847821507, 21971696161332518, 22542978474843529, 23114260788354540, 23685543101865551⟩
  | 63 => ⟨21975544510618918, 22554523522702729, 23133502534786540, 23712481546870351, 24291460558954162⟩
  | 64 => ⟨22558371871989129, 23145047582645740, 23731723293302351, 24318399003958962, 24905074714615573⟩
  | 65 => ⟨23148895931932140, 23743268341161551, 24337640750390962, 24932013159620373, 25526385568849784⟩
  | 66 => ⟨23747116690447951, 24349185798250162, 24951254906052373, 25553324013854584, 26155393121656795⟩
  | 67 => ⟨24353034147536562, 24962799953911573, 25572565760286584, 26182331566661595, 26792097373036606⟩
  | 68 => ⟨24966648303197973, 25584110808145784, 26201573313093595, 26819035818041406, 27436498322989217⟩
  | 69 => ⟨25587959157432184, 26213118360952795, 26838277564473406, 27463436767994017, 28088595971514628⟩
  | 70 => ⟨26216966710239195, 26849822612332606, 27482678514426017, 28115534416519428, 28748390318612839⟩
  | 71 => ⟨26853670961619006, 27494223562285217, 28134776162951428, 28775328763617639, 29415881364283850⟩
  | 72 => ⟨27498071911571617, 28146321210810628, 28794570510049639, 29442819809288650, 30091069108527661⟩
  | 73 => ⟨28150169560097028, 28806115557908839, 29462061555720650, 30118007553532461, 30773953551344272⟩
  | 74 => ⟨28809963907195239, 29473606603579850, 30137249299964461, 30800891996349072, 31464534692733683⟩
  | 75 => ⟨29477454952866250, 30148794347823661, 30820133742781072, 31491473137738483, 32162812532695894⟩
  | 76 => ⟨30152642697110061, 30831678790640272, 31510714884170483, 32189750977700694, 32868787071230905⟩
  | 77 => ⟨30835527139926672, 31522259932029683, 32208992724132694, 32895725516235705, 33582458308338716⟩
  | 78 => ⟨31526108281316083, 32220537771991894, 32914967262667705, 33609396753343516, 34303826244019327⟩
  | 79 => ⟨32224386121278294, 32926512310526905, 33628638499775516, 34330764689024127, 35032890878272738⟩
  | 80 => ⟨32930360659813305, 33640183547634716, 34350006435456127, 35059829323277538, 35769652211098949⟩
  | 81 => ⟨33644031896921116, 34361551483315327, 35079071069709538, 35796590656103749, 36514110242497960⟩
  | 82 => ⟨34365399832601727, 35090616117568738, 35815832402535749, 36541048687502760, 37266264972469771⟩
  | 83 => ⟨35094464466855138, 35827377450394949, 36560290433934760, 37293203417474571, 38026116401014382⟩
  | 84 => ⟨35831225799681349, 36571835481793960, 37312445163906571, 38053054846019182, 38793664528131793⟩
  | 85 => ⟨36575683831080360, 37323990211765771, 38072296592451182, 38820602973136593, 39568909353822004⟩
  | 86 => ⟨37327838561052171, 38083841640310382, 38839844719568593, 39595847798826804, 40351850878085015⟩
  | 87 => ⟨38087689989596782, 38851389767427793, 39615089545258804, 40378789323089815, 41142489100920826⟩
  | 88 => ⟨38855238116714193, 39626634593118004, 40398031069521815, 41169427545925626, 41940824022329437⟩
  | 89 => ⟨39630482942404404, 40409576117381015, 41188669292357626, 41967762467334237, 42746855642310848⟩
  | 90 => ⟨40413424466667415, 41200214340216826, 41987004213766237, 42773794087315648, 43560583960865059⟩
  | 91 => ⟨41204062689503226, 41998549261625437, 42793035833747648, 43587522405869859, 44382008977992070⟩
  | 92 => ⟨42002397610911837, 42804580881606848, 43606764152301859, 44408947422996870, 45211130693691881⟩
  | 93 => ⟨42808429230893248, 43618309200161059, 44428189169428870, 45238069138696681, 46047949107964492⟩
  | 94 => ⟨43622157549447459, 44439734217288070, 45257310885128681, 46074887552969292, 46892464220809903⟩
  | 95 => ⟨44443582566574470, 45268855932987881, 46094129299401292, 46919402665814703, 47744676032228114⟩
  | 96 => ⟨45272704282274281, 46105674347260492, 46938644412246703, 47771614477232914, 48604584542219125⟩
  | 97 => ⟨46109522696546892, 46950189460105903, 47790856223664914, 48631522987223925, 49472189750782936⟩
  | 98 => ⟨46954037809392303, 47802401271524114, 48650764733655925, 49499128195787736, 50347491657919547⟩
  | 99 => ⟨47806249620810514, 48662309781515125, 49518369942219736, 50374430102924347, 51230490263628958⟩
  | 100 => ⟨48666158130801525, 49529914990078936, 50393671849356347, 51257428708633758, 52121185567911169⟩
  | 101 => ⟨49533763339365336, 50405216897215547, 51276670455065758, 52148124012915969, 53019577570766180⟩
  | 102 => ⟨50409065246501947, 51288215502924958, 52167365759347969, 53046516015770980, 53925666272193991⟩
  | _ => defaultCosts

def row26 : ℕ → Costs
  | 0 => ⟨1207823092417890, 1254209106216340, 1393504575030778, 1532800043845216, 1672095512659654⟩
  | 1 => ⟨1254209106216340, 1396940575081978, 1539672043947616, 1682403512813254, 1825134981678892⟩
  | 2 => ⟨1091677274637820, 1209558758524515, 1327440242411210, 1445321726297905, 1563203210184600⟩
  | 3 => ⟨1213561728992867, 1339449153816266, 1465336578639665, 1591224003463064, 1717111428286463⟩
  | 4 => ⟨1343452124284618, 1477345490044721, 1611238855804824, 1745132221564927, 1879025587325030⟩
  | 5 => ⟨1481348460513073, 1623247767209880, 1765147073906687, 1907046380603494, 2048945687300301⟩
  | 6 => ⟨1627250737678232, 1777155985311743, 1927061232945254, 2076966480578765, 2226871728212276⟩
  | 7 => ⟨1781158955780095, 1939070144350310, 2096981332920525, 2254892521490740, 2412803710060955⟩
  | 8 => ⟨1943073114818662, 2108990244325581, 2274907373832500, 2440824503339419, 2606741632846338⟩
  | 9 => ⟨2112993214793933, 2286916285237556, 2460839355681179, 2634762426124802, 2808685496568425⟩
  | 10 => ⟨2290919255705908, 2472848267086235, 2654777278466562, 2836706289846889, 3018635301227216⟩
  | 11 => ⟨2476851237554587, 2666786189871618, 2856721142188649, 3046656094505680, 3236591046822711⟩
  | 12 => ⟨2670789160339970, 2868730053593705, 3066670946847440, 3264611840101175, 3462552733354910⟩
  | 13 => ⟨2872733024062057, 3078679858252496, 3284626692442935, 3490573526633374, 3696520360823813⟩
  | 14 => ⟨3082682828720848, 3296635603847991, 3510588378975134, 3724541154102277, 3938493929229420⟩
  | 15 => ⟨3300638574316343, 3522597290380190, 3744556006444037, 3966514722507884, 4188473438571731⟩
  | 16 => ⟨3526600260848542, 3756564917849093, 3986529574849644, 4216494231850195, 4446458888850746⟩
  | 17 => ⟨3760567888317445, 3998538486254700, 4236509084191955, 4474479682129210, 4712450280066465⟩
  | 18 => ⟨4002541456723052, 4248517995597011, 4494494534470970, 4740471073344929, 4986447612218888⟩
  | 19 => ⟨4252520966065363, 4506503445876026, 4760485925686689, 5014468405497352, 5268450885308015⟩
  | 20 => ⟨4510506416344378, 4772494837091745, 5034483257839112, 5296471678586479, 5558460099333846⟩
  | 21 => ⟨4776497807560097, 5046492169244168, 5316486530928239, 5586480892612310, 5856475254296381⟩
  | 22 => ⟨5050495139712520, 5328495442333295, 5606495744954070, 5884496047574845, 6162496350195620⟩
  | 23 => ⟨5332498412801647, 5618504656359126, 5904510899916605, 6190517143474084, 6476523387031563⟩
  | 24 => ⟨5622507626827478, 5916519811321661, 6210531995815844, 6504544180310027, 6798556364804210⟩
  | 25 => ⟨5920522781790013, 6222540907220900, 6524559032651787, 6826577158082674, 7128595283513561⟩
  | 26 => ⟨6226543877689252, 6536567944056843, 6846592010424434, 7156616076792025, 7466640143159616⟩
  | 27 => ⟨6540570914525195, 6858600921829490, 7176630929133785, 7494660936438080, 7812690943742375⟩
  | 28 => ⟨6862603892297842, 7188639840538841, 7514675788779840, 7840711737020839, 8166747685261838⟩
  | 29 => ⟨7192642811007193, 7526684700184896, 7860726589362599, 8194768478540302, 8528810367718005⟩
  | 30 => ⟨7530687670653248, 7872735500767655, 8214783330882062, 8556831160996469, 8898878991110876⟩
  | 31 => ⟨7876738471236007, 8226792242287118, 8576846013338229, 8926899784389340, 9276953555440451⟩
  | 32 => ⟨8230795212755470, 8588854924743285, 8946914636731100, 9304974348718915, 9663034060706730⟩
  | 33 => ⟨8592857895211637, 8958923548136156, 9324989201060675, 9691054853985194, 10057120506909713⟩
  | 34 => ⟨8962926518604508, 9336998112465731, 9711069706326954, 10085141300188177, 10459212894049400⟩
  | 35 => ⟨9341001082934083, 9723078617732010, 10105156152529937, 10487233687327864, 10869311222125791⟩
  | 36 => ⟨9727081588200362, 10117165063934993, 10507248539669624, 10897332015404255, 11287415491138886⟩
  | 37 => ⟨10121168034403345, 10519257451074680, 10917346867746015, 11315436284417350, 11713525701088685⟩
  | 38 => ⟨10523260421543032, 10929355779151071, 11335451136759110, 11741546494367149, 12147641851975188⟩
  | 39 => ⟨10933358749619423, 11347460048164166, 11761561346708909, 12175662645253652, 12589763943798395⟩
  | 40 => ⟨11351463018632518, 11773570258113965, 12195677497595412, 12617784737076859, 13039891976558306⟩
  | 41 => ⟨11777573228582317, 12207686409000468, 12637799589418619, 13067912769836770, 13498025950254921⟩
  | 42 => ⟨12211689379468820, 12649808500823675, 13087927622178530, 13526046743533385, 13964165864888240⟩
  | 43 => ⟨12653811471292027, 13099936533583586, 13546061595875145, 13992186658166704, 14438311720458263⟩
  | 44 => ⟨13103939504051938, 13558070507280201, 14012201510508464, 14466332513736727, 14920463516964990⟩
  | 45 => ⟨13562073477748553, 14024210421913520, 14486347366078487, 14948484310243454, 15410621254408421⟩
  | 46 => ⟨14028213392381872, 14498356277483543, 14968499162585214, 15438642047686885, 15908784932788556⟩
  | 47 => ⟨14502359247951895, 14980508073990270, 15458656900028645, 15936805726067020, 16414954552105395⟩
  | 48 => ⟨14984511044458622, 15470665811433701, 15956820578408780, 16442975345383859, 16929130112358938⟩
  | 49 => ⟨15474668781902053, 15968829489813836, 16462990197725619, 16957150905637402, 17451311613549185⟩
  | 50 => ⟨15972832460282188, 16474999109130675, 16977165757979162, 17479332406827649, 17981499055676136⟩
  | 51 => ⟨16479002079599027, 16989174669384218, 17499347259169409, 18009519848954600, 18519692438739791⟩
  | 52 => ⟨16993177639852570, 17511356170574465, 18029534701296360, 18547713232018255, 19065891762740150⟩
  | 53 => ⟨17515359141042817, 18041543612701416, 18567728084360015, 19093912556018614, 19620097027677213⟩
  | 54 => ⟨18045546583169768, 18579736995765071, 19113927408360374, 19648117820955677, 20182308233550980⟩
  | 55 => ⟨18583739966233423, 19125936319765430, 19668132673297437, 20210329026829444, 20752525380361451⟩
  | 56 => ⟨19129939290233782, 19680141584702493, 20230343879171204, 20780546173639915, 21330748468108626⟩
  | 57 => ⟨19684144555170845, 20242352790576260, 20800561025981675, 21358769261387090, 21916977496792505⟩
  | 58 => ⟨20246355761044612, 20812569937386731, 21378784113728850, 21944998290070969, 22511212466413088⟩
  | 59 => ⟨20816572907855083, 21390793025133906, 21965013142412729, 22539233259691552, 23113453376970375⟩
  | 60 => ⟨21394795995602258, 21977022053817785, 22559248112033312, 23141474170248839, 23723700228464366⟩
  | 61 => ⟨21981025024286137, 22571257023438368, 23161489022590599, 23751721021742830, 24341953020895061⟩
  | 62 => ⟨22575259993906720, 23173497933995655, 23771735874084590, 24369973814173525, 24968211754262460⟩
  | 63 => ⟨23177500904464007, 23783744785489646, 24389988666515285, 24996232547540924, 25602476428566563⟩
  | 64 => ⟨23787747755957998, 24401997577920341, 25016247399882684, 25630497221845027, 26244747043807370⟩
  | 65 => ⟨24406000548388693, 25028256311287740, 25650512074186787, 26272767837085834, 26895023599984881⟩
  | 66 => ⟨25032259281756092, 25662520985591843, 26292782689427594, 26923044393263345, 27553306097099096⟩
  | 67 => ⟨25666523956060195, 26304791600832650, 26943059245605105, 27581326890377560, 28219594535150015⟩
  | 68 => ⟨26308794571301002, 26955068157010161, 27601341742719320, 28247615328428479, 28893888914137638⟩
  | 69 => ⟨26959071127478513, 27613350654124376, 28267630180770239, 28921909707416102, 29576189234061965⟩
  | 70 => ⟨27617353624592728, 28279639092175295, 28941924559757862, 29604210027340429, 30266495494922996⟩
  | 71 => ⟨28283642062643647, 28953933471162918, 29624224879682189, 30294516288201460, 30964807696720731⟩
  | 72 => ⟨28957936441631270, 29636233791087245, 30314531140543220, 30992828489999195, 31671125839455170⟩
  | 73 => ⟨29640236761555597, 30326540051948276, 31012843342340955, 31699146632733634, 32385449923126313⟩
  | 74 => ⟨30330543022416628, 31024852253746011, 31719161485075394, 32413470716404777, 33107779947734160⟩
  | 75 => ⟨31028855224214363, 31731170396480450, 32433485568746537, 33135800741012624, 33838115913278711⟩
  | 76 => ⟨31735173366948802, 32445494480151593, 33155815593354384, 33866136706557175, 34576457819759966⟩
  | 77 => ⟨32449497450619945, 33167824504759440, 33886151558898935, 34604478613038430, 35322805667177925⟩
  | 78 => ⟨33171827475227792, 33898160470303991, 34624493465380190, 35350826460456389, 36077159455532588⟩
  | 79 => ⟨33902163440772343, 34636502376785246, 35370841312798149, 36105180248811052, 36839519184823955⟩
  | 80 => ⟨34640505347253598, 35382850224203205, 36125195101152812, 36867539978102419, 37609884855052026⟩
  | 81 => ⟨35386853194671557, 36137204012557868, 36887554830444179, 37637905648330490, 38388256466216801⟩
  | 82 => ⟨36141206983026220, 36899563741849235, 37657920500672250, 38416277259495265, 39174634018318280⟩
  | 83 => ⟨36903566712317587, 37669929412077306, 38436292111837025, 39202654811596744, 39969017511356463⟩
  | 84 => ⟨37673932382545658, 38448301023242081, 39222669663938504, 39997038304634927, 40771406945331350⟩
  | 85 => ⟨38452303993710433, 39234678575343560, 40017053156976687, 40799427738609814, 41581802320242941⟩
  | 86 => ⟨39238681545811912, 40029062068381743, 40819442590951574, 41609823113521405, 42400203636091236⟩
  | 87 => ⟨40033065038850095, 40831451502356630, 41629837965863165, 42428224429369700, 43226610892876235⟩
  | 88 => ⟨40835454472824982, 41641846877268221, 42448239281711460, 43254631686154699, 44061024090597938⟩
  | 89 => ⟨41645849847736573, 42460248193116516, 43274646538496459, 44089044883876402, 44903443229256345⟩
  | 90 => ⟨42464251163584868, 43286655449901515, 44109059736218162, 44931464022534809, 45753868308851456⟩
  | 91 => ⟨43290658420369867, 44121068647623218, 44951478874876569, 45781889102129920, 46612299329383271⟩
  | 92 => ⟨44125071618091570, 44963487786281625, 45801903954471680, 46640320122661735, 47478736290851790⟩
  | 93 => ⟨44967490756749977, 45813912865876736, 46660334975003495, 47506757084130254, 48353179193257013⟩
  | 94 => ⟨45817915836345088, 46672343886408551, 47526771936472014, 48381199986535477, 49235628036598940⟩
  | 95 => ⟨46676346856876903, 47538780847877070, 48401214838877237, 49263648829877404, 50126082820877571⟩
  | 96 => ⟨47542783818345422, 48413223750282293, 49283663682219164, 50154103614156035, 51024543546092906⟩
  | 97 => ⟨48417226720750645, 49295672593624220, 50174118466497795, 51052564339371370, 51931010212244945⟩
  | 98 => ⟨49299675564092572, 50186127377902851, 51072579191713130, 51959031005523409, 52845482819333688⟩
  | 99 => ⟨50190130348371203, 51084588103118186, 51979045857865169, 52873503612612152, 53767961367359135⟩
  | 100 => ⟨51088591073586538, 51991054769270225, 52893518464953912, 53795982160637599, 54698445856321286⟩
  | 101 => ⟨51995057739738577, 52905527376358968, 53815997012979359, 54726466649599750, 55636936286220141⟩
  | _ => defaultCosts

def row27 : ℕ → Costs
  | 0 => ⟨1352616162362829, 1402644336739841, 1552866286765675, 1703088236791509, 1853310186817343⟩
  | 1 => ⟨1402644336739841, 1556439726818923, 1710235116898005, 1864030506977087, 2017825897056169⟩
  | 2 => ⟨1214377787000429, 1340969597994712, 1467561408988995, 1594153219983278, 1720745030977561⟩
  | 3 => ⟨1345127189645016, 1480034183939907, 1614941178234798, 1749848172529689, 1884755166824580⟩
  | 4 => ⟨1484191775590211, 1627413953185710, 1770636130781209, 1913858308376708, 2057080485972207⟩
  | 5 => ⟨1631571544836014, 1783108905732121, 1934646266628228, 2086183627524335, 2237720988420442⟩
  | 6 => ⟨1787266497382425, 1947119041579140, 2106971585775855, 2266824129972570, 2426676674169285⟩
  | 7 => ⟨1951276633229444, 2119444360726767, 2287612088224090, 2455779815721413, 2623947543218736⟩
  | 8 => ⟨2123601952377071, 2300084863175002, 2476567773972933, 2653050684770864, 2829533595568795⟩
  | 9 => ⟨2304242454825306, 2489040548923845, 2673838643022384, 2858636737120923, 3043434831219462⟩
  | 10 => ⟨2493198140574149, 2686311417973296, 2879424695372443, 3072537972771590, 3265651250170737⟩
  | 11 => ⟨2690469009623600, 2891897470323355, 3093325931023110, 3294754391722865, 3496182852422620⟩
  | 12 => ⟨2896055061973659, 3105798705974022, 3315542349974385, 3525285993974748, 3735029637975111⟩
  | 13 => ⟨3109956297624326, 3328015124925297, 3546073952226268, 3764132779527239, 3982191606828210⟩
  | 14 => ⟨3332172716575601, 3558546727177180, 3784920737778759, 4011294748380338, 4237668758981917⟩
  | 15 => ⟨3562704318827484, 3797393512729671, 4032082706631858, 4266771900534045, 4501461094436232⟩
  | 16 => ⟨3801551104379975, 4044555481582770, 4287559858785565, 4530564235988360, 4773568613191155⟩
  | 17 => ⟨4048713073233074, 4300032633736477, 4551352194239880, 4802671754743283, 5053991315246686⟩
  | 18 => ⟨4304190225386781, 4563824969190792, 4823459712994803, 5083094456798814, 5342729200602825⟩
  | 19 => ⟨4567982560841096, 4835932487945715, 5103882415050334, 5371832342154953, 5639782269259572⟩
  | 20 => ⟨4840090079596019, 5116355190001246, 5392620300406473, 5668885410811700, 5945150521216927⟩
  | 21 => ⟨5120512781651550, 5405093075357385, 5689673369063220, 5974253662769055, 6258833956474890⟩
  | 22 => ⟨5409250667007689, 5702146144014132, 5995041621020575, 6287937098027018, 6580832575033461⟩
  | 23 => ⟨5706303735664436, 6007514395971487, 6308725056278538, 6609935716585589, 6911146376892640⟩
  | 24 => ⟨6011671987621791, 6321197831229450, 6630723674837109, 6940249518444768, 7249775362052427⟩
  | 25 => ⟨6325355422879754, 6643196449788021, 6961037476696288, 7278878503604555, 7596719530512822⟩
  | 26 => ⟨6647354041438325, 6973510251647200, 7299666461856075, 7625822672064950, 7951978882273825⟩
  | 27 => ⟨6977667843297504, 7312139236806987, 7646610630316470, 7981082023825953, 8315553417335436⟩
  | 28 => ⟨7316296828457291, 7659083405267382, 8001869982077473, 8344656558887564, 8687443135697655⟩
  | 29 => ⟨7663240996917686, 8014342757028385, 8365444517139084, 8716546277249783, 9067648037360482⟩
  | 30 => ⟨8018500348678689, 8377917292089996, 8737334235501303, 9096751178912610, 9456168122323917⟩
  | 31 => ⟨8382074883740300, 8749807010452215, 9117539137164130, 9485271263876045, 9853003390587960⟩
  | 32 => ⟨8753964602102519, 9130011912115042, 9506059222127565, 9882106532140088, 10258153842152611⟩
  | 33 => ⟨9134169503765346, 9518531997078477, 9902894490391608, 10287256983704739, 10671619477017870⟩
  | 34 => ⟨9522689588728781, 9915367265342520, 10308044941956259, 10700722618569998, 11093400295183737⟩
  | 35 => ⟨9919524856992824, 10320517716907171, 10721510576821518, 11122503436735865, 11523496296650212⟩
  | 36 => ⟨10324675308557475, 10733983351772430, 11143291394987385, 11552599438202340, 11961907481417295⟩
  | 37 => ⟨10738140943422734, 11155764169938297, 11573387396453860, 11991010622969423, 12408633849484986⟩
  | 38 => ⟨11159921761588601, 11585860171404772, 12011798581220943, 12437736991037114, 12863675400853285⟩
  | 39 => ⟨11590017763055076, 12024271356171855, 12458524949288634, 12892778542405413, 13327032135522192⟩
  | 40 => ⟨12028428947822159, 12470997724239546, 12913566500656933, 13356135277074320, 13798704053491707⟩
  | 41 => ⟨12475155315889850, 12926039275607845, 13376923235325840, 13827807195043835, 14278691154761830⟩
  | 42 => ⟨12930196867258149, 13389396010276752, 13848595153295355, 14307794296313958, 14766993439332561⟩
  | 43 => ⟨13393553601927056, 13861067928246267, 14328582254565478, 14796096580884689, 15263610907203900⟩
  | 44 => ⟨13865225519896571, 14341055029516390, 14816884539136209, 15292714048756028, 15768543558375847⟩
  | 45 => ⟨14345212621166694, 14829357314087121, 15313502007007548, 15797646699927975, 16281791392848402⟩
  | 46 => ⟨14833514905737425, 15325974781958460, 15818434658179495, 16310894534400530, 16803354410621565⟩
  | 47 => ⟨15330132373608764, 15830907433130407, 16331682492652050, 16832457552173693, 17333232611695336⟩
  | 48 => ⟨15835065024780711, 16344155267602962, 16853245510425213, 17362335753247464, 17871425996069715⟩
  | 49 => ⟨16348312859253266, 16865718285376125, 17383123711498984, 17900529137621843, 18417934563744702⟩
  | 50 => ⟨16869875877026429, 17395596486449896, 17921317095873363, 18447037705296830, 18972758314720297⟩
  | 51 => ⟨17399754078100200, 17933789870824275, 18467825663548350, 19001861456272425, 19535897248996500⟩
  | 52 => ⟨17937947462474579, 18480298438499262, 19022649414523945, 19565000390548628, 20107351366573311⟩
  | 53 => ⟨18484456030149566, 19035122189474857, 19585788348800148, 20136454508125439, 20687120667450730⟩
  | 54 => ⟨19039279781125161, 19598261123751060, 20157242466376959, 20716223809002858, 21275205151628757⟩
  | 55 => ⟨19602418715401364, 20169715241327871, 20737011767254378, 21304308293180885, 21871604819107392⟩
  | 56 => ⟨20173872832978175, 20749484542205290, 21325096251432405, 21900707960659520, 22476319669886635⟩
  | 57 => ⟨20753642133855594, 21337569026383317, 21921495918911040, 22505422811438763, 23089349703966486⟩
  | 58 => ⟨21341726618033621, 21933968693861952, 22526210769690283, 23118452845518614, 23710694921346945⟩
  | 59 => ⟨21938126285512256, 22538683544641195, 23139240803770134, 23739798062899073, 24340355322028012⟩
  | 60 => ⟨22542841136291499, 23151713578721046, 23760586021150593, 24369458463580140, 24978330906009687⟩
  | 61 => ⟨23155871170371350, 23773058796101505, 24390246421831660, 25007434047561815, 25624621673291970⟩
  | 62 => ⟨23777216387751809, 24402719196782572, 25028222005813335, 25653724814844098, 26279227623874861⟩
  | 63 => ⟨24406876788432876, 25040694780764247, 25674512773095618, 26308330765426989, 26942148757758360⟩
  | 64 => ⟨25044852372414551, 25686985548046530, 26329118723678509, 26971251899310488, 27613385074942467⟩
  | 65 => ⟨25691143139696834, 26341591498629421, 26992039857562008, 27642488216494595, 28292936575427182⟩
  | 66 => ⟨26345749090279725, 27004512632512920, 27663276174746115, 28322039716979310, 28980803259212505⟩
  | 67 => ⟨27008670224163224, 27675748949697027, 28342827675230830, 29009906400764633, 29676985126298436⟩
  | 68 => ⟨27679906541347331, 28355300450181742, 29030694359016153, 29706088267850564, 30381482176684975⟩
  | 69 => ⟨28359458041832046, 29043167133967065, 29726876226102084, 30410585318237103, 31094294410372122⟩
  | 70 => ⟨29047324725617369, 29739349001052996, 30431373276488623, 31123397551924250, 31815421827359877⟩
  | 71 => ⟨29743506592703300, 30443846051439535, 31144185510175770, 31844524968912005, 32544864427648240⟩
  | 72 => ⟨30448003643089839, 31156658285126682, 31865312927163525, 32573967569200368, 33282622211237211⟩
  | 73 => ⟨31160815876776986, 31877785702114437, 32594755527451888, 33311725352789339, 34028695178126790⟩
  | 74 => ⟨31881943293764741, 32607228302402800, 33332513311040859, 34057798319678918, 34783083328316977⟩
  | 75 => ⟨32611385894053104, 33344986085991771, 34078586277930438, 34812186469869105, 35545786661807772⟩
  | 76 => ⟨33349143677642075, 34091059052881350, 34832974428120625, 35574889803359900, 36316805178599175⟩
  | 77 => ⟨34095216644531654, 34845447203071537, 35595677761611420, 36345908320151303, 37096138878691186⟩
  | 78 => ⟨34849604794721841, 35608150536562332, 36366696278402823, 37125242020243314, 37883787762083805⟩
  | 79 => ⟨35612308128212636, 36379169053353735, 37146029978494834, 37912890903635933, 38679751828777032⟩
  | 80 => ⟨36383326645004039, 37158502753445746, 37933678861887453, 38708854970329160, 39484031078770867⟩
  | 81 => ⟨37162660345096050, 37946151636838365, 38729642928580680, 39513134220322995, 40296625512065310⟩
  | 82 => ⟨37950309228488669, 38742115703531592, 39533922178574515, 40325728653617438, 41117535128660361⟩
  | 83 => ⟨38746273295181896, 39546394953525427, 40346516611868958, 41146638270212489, 41946759928556020⟩
  | 84 => ⟨39550552545175731, 40358989386819870, 41167426228464009, 41975863070108148, 42784299911752287⟩
  | 85 => ⟨40363146978470174, 41179899003414921, 41996651028359668, 42813403053304415, 43630155078249162⟩
  | 86 => ⟨41184056595065225, 42009123803310580, 42834191011555935, 43659258219801290, 44484325428046645⟩
  | 87 => ⟨42013281394960884, 42846663786506847, 43680046178052810, 44513428569598773, 45346810961144736⟩
  | 88 => ⟨42850821378157151, 43692518953003722, 44534216527850293, 45375914102696864, 46217611677543435⟩
  | 89 => ⟨43696676544654026, 44546689302801205, 45396702060948384, 46246714819095563, 47096727577242742⟩
  | 90 => ⟨44550846894451509, 45409174835899296, 46267502777347083, 47125830718794870, 47984158660242657⟩
  | 91 => ⟨45413332427549600, 46279975552297995, 47146618677046390, 48013261801794785, 48879904926543180⟩
  | 92 => ⟨46284133143948299, 47159091451997302, 48034049760046305, 48909008068095308, 49783966376144311⟩
  | 93 => ⟨47163249043647606, 48046522534997217, 48929796026346828, 49813069517696439, 50696343009046050⟩
  | 94 => ⟨48050680126647521, 48942268801297740, 49833857475947959, 50725446150598178, 51617034825248397⟩
  | 95 => ⟨48946426392948044, 49846330250898871, 50746234108849698, 51646137966800525, 52546041824751352⟩
  | 96 => ⟨49850487842549175, 50758706883800610, 51666925925052045, 52575144966303480, 53483364007554915⟩
  | 97 => ⟨50762864475450914, 51679398700002957, 52595932924555000, 53512467149107043, 54429001373659086⟩
  | 98 => ⟨51683556291653261, 52608405699505912, 53533255107358563, 54458104515211214, 55382953923063865⟩
  | 99 => ⟨52612563291156216, 53545727882309475, 54478892473462734, 55412057064615993, 56345221655769252⟩
  | 100 => ⟨53549885473959779, 54491365248413646, 55432845022867513, 56374324797321380, 57315804571775247⟩
  | _ => defaultCosts

def row28 : ℕ → Costs
  | 0 => ⟨1508541873522236, 1562349648479858, 1723910399723232, 1885471150966606, 2047031902209980⟩
  | 1 => ⟨1562349648479858, 1727621279778528, 1892892911077198, 2058164542375868, 2223436173674538⟩
  | 2 => ⟨1345943247652578, 1481554628118353, 1617166008584128, 1752777389049903, 1888388769515678⟩
  | 3 => ⟨1485866840950609, 1630102647080896, 1774338453211183, 1918574259341470, 2062810065471757⟩
  | 4 => ⟨1634414859913152, 1787275091707951, 1940135323502750, 2092995555297549, 2245855787092348⟩
  | 5 => ⟨1791587304540207, 1953071961999518, 2114556619458829, 2276041276918140, 2437525934377451⟩
  | 6 => ⟨1957384174831774, 2127493257955597, 2297602341079420, 2467711424203243, 2637820507327066⟩
  | 7 => ⟨2131805470787853, 2310538979576188, 2489272488364523, 2668005997152858, 2846739505941193⟩
  | 8 => ⟨2314851192408444, 2502209126861291, 2689567061314138, 2876924995766985, 3064282930219832⟩
  | 9 => ⟨2506521339693547, 2702503699810906, 2898486059928265, 3094468420045624, 3290450780162983⟩
  | 10 => ⟨2706815912643162, 2911422698425033, 3116029484206904, 3320636269988775, 3525243055770646⟩
  | 11 => ⟨2915734911257289, 3128966122703672, 3342197334150055, 3555428545596438, 3768659757042821⟩
  | 12 => ⟨3133278335535928, 3355133972646823, 3576989609757718, 3798845246868613, 4020700883979508⟩
  | 13 => ⟨3359446185479079, 3589926248254486, 3820406311029893, 4050886373805300, 4281366436580707⟩
  | 14 => ⟨3594238461086742, 3833342949526661, 4072447437966580, 4311551926406499, 4550656414846418⟩
  | 15 => ⟨3837655162358917, 4085384076463348, 4333112990567779, 4580841904672210, 4828570818776641⟩
  | 16 => ⟨4089696289295604, 4346049629064547, 4602402968833490, 4858756308602433, 5115109648371376⟩
  | 17 => ⟨4350361841896803, 4615339607330258, 4880317372763713, 5145295138197168, 5410272903630623⟩
  | 18 => ⟨4619651820162514, 4893254011260481, 5166856202358448, 5440458393456415, 5714060584554382⟩
  | 19 => ⟨4897566224092737, 5179792840855216, 5462019457617695, 5744246074380174, 6026472691142653⟩
  | 20 => ⟨5184105053687472, 5474956096114463, 5765807138541454, 6056658180968445, 6347509223395436⟩
  | 21 => ⟨5479268308946719, 5778743777038222, 6078219245129725, 6377694713221228, 6677170181312731⟩
  | 22 => ⟨5783055989870478, 6091155883626493, 6399255777382508, 6707355671138523, 7015455564894538⟩
  | 23 => ⟨6095468096458749, 6412192415879276, 6728916735299803, 7045641054720330, 7362365374140857⟩
  | 24 => ⟨6416504628711532, 6741853373796571, 7067202118881610, 7392550863966649, 7717899609051688⟩
  | 25 => ⟨6746165586628827, 7080138757378378, 7414111928127929, 7748085098877480, 8082058269627031⟩
  | 26 => ⟨7084450970210634, 7427048566624697, 7769646163038760, 8112243759452823, 8454841355866886⟩
  | 27 => ⟨7431360779456953, 7782582801535528, 8133804823614103, 8485026845692678, 8836248867771253⟩
  | 28 => ⟨7786895014367784, 8146741462110871, 8506587909853958, 8866434357597045, 9226280805340132⟩
  | 29 => ⟨8151053674943127, 8519524548350726, 8887995421758325, 9256466295165924, 9624937168573523⟩
  | 30 => ⟨8523836761182982, 8900932060255093, 9278027359327204, 9655122658399315, 10032217957471426⟩
  | 31 => ⟨8905244273087349, 9290963997823972, 9676683722560595, 10062403447297218, 10448123172033841⟩
  | 32 => ⟨9295276210656228, 9689620361057363, 10083964511458498, 10478308661859633, 10872652812260768⟩
  | 33 => ⟨9693932573889619, 10096901149955266, 10499869726020913, 10902838302086560, 11305806878152207⟩
  | 34 => ⟨10101213362787522, 10512806364517681, 10924399366247840, 11335992367977999, 11747585369708158⟩
  | 35 => ⟨10517118577349937, 10937336004744608, 11357553432139279, 11777770859533950, 12197988286928621⟩
  | 36 => ⟨10941648217576864, 11370490070636047, 11799331923695230, 12228173776754413, 12657015629813596⟩
  | 37 => ⟨11374802283468303, 11812268562191998, 12249734840915693, 12687201119639388, 13124667398363083⟩
  | 38 => ⟨11816580775024254, 12262671479412461, 12708762183800668, 13154852888188875, 13600943592577082⟩
  | 39 => ⟨12266983692244717, 12721698822297436, 13176413952350155, 13631129082402874, 14085844212455593⟩
  | 40 => ⟨12726011035129692, 13189350590846923, 13652690146564154, 14116029702281385, 14579369257998616⟩
  | 41 => ⟨13193662803679179, 13665626785060922, 14137590766442665, 14609554747824408, 15081518729206151⟩
  | 42 => ⟨13669938997893178, 14150527404939433, 14631115811985688, 15111704219031943, 15592292626078198⟩
  | 43 => ⟨14154839617771689, 14644052450482456, 15133265283193223, 15622478115903990, 16111690948614757⟩
  | 44 => ⟨14648364663314712, 15146201921689991, 15644039180065270, 16141876438440549, 16639713696815828⟩
  | 45 => ⟨15150514134522247, 15656975818562038, 16163437502601829, 16669899186641620, 17176360870681411⟩
  | 46 => ⟨15661288031394294, 16176374141098597, 16691460250802900, 17206546360507203, 17721632470211506⟩
  | 47 => ⟨16180686353930853, 16704396889299668, 17228107424668483, 17751817960037298, 18275528495406113⟩
  | 48 => ⟨16708709102131924, 17241044063165251, 17773379024198578, 18305713985231905, 18838048946265232⟩
  | 49 => ⟨17245356275997507, 17786315662695346, 18327275049393185, 18868234436091024, 19409193822788863⟩
  | 50 => ⟨17790627875527602, 18340211687889953, 18889795500252304, 19439379312614655, 19988963124977006⟩
  | 51 => ⟨18344523900722209, 18902732138749072, 19460940376775935, 20019148614802798, 20577356852829661⟩
  | 52 => ⟨18907044351581328, 19473877015272703, 20040709678964078, 20607542342655453, 21174375006346828⟩
  | 53 => ⟨19478189228104959, 20053646317460846, 20629103406816733, 21204560496172620, 21780017585528507⟩
  | 54 => ⟨20057958530293102, 20642040045313501, 21226121560333900, 21810203075354299, 22394284590374698⟩
  | 55 => ⟨20646352258145757, 21239058198830668, 21831764139515579, 22424470080200490, 23017176020885401⟩
  | 56 => ⟨21243370411662924, 21844700778012347, 22446031144361770, 23047361510711193, 23648691877060616⟩
  | 57 => ⟨21849012990844603, 22458967782858538, 23068922574872473, 23678877366886408, 24288832158900343⟩
  | 58 => ⟨22463279995690794, 23081859213369241, 23700438431047688, 24319017648726135, 24937596866404582⟩
  | 59 => ⟨23086171426201497, 23713375069544456, 24340578712887415, 24967782356230374, 25594985999573333⟩
  | 60 => ⟨23717687282376712, 24353515351384183, 24989343420391654, 25625171489399125, 26260999558406596⟩
  | 61 => ⟨24357827564216439, 25002280058888422, 25646732553560405, 26291185048232388, 26935637542904371⟩
  | 62 => ⟨25006592271720678, 25659669192057173, 26312746112393668, 26965823032730163, 27618899953066658⟩
  | 63 => ⟨25663981404889429, 26325682750890436, 26987384096891443, 27649085442892450, 28310786788893457⟩
  | 64 => ⟨26329994963722692, 27000320735388211, 27670646507053730, 28340972278719249, 29011298050384768⟩
  | 65 => ⟨27004632948220467, 27683583145550498, 28362533342880529, 29041483540210560, 29720433737540591⟩
  | 66 => ⟨27687895358382754, 28375469981377297, 29063044604371840, 29750619227366383, 30438193850360926⟩
  | 67 => ⟨28379782194209553, 29075981242868608, 29772180291527663, 30468379340186718, 31164578388845773⟩
  | 68 => ⟨29080293455700864, 29785116930024431, 30489940404347998, 31194763878671565, 31899587352995132⟩
  | 69 => ⟨29789429142856687, 30502877042844766, 31216324942832845, 31929772842820924, 32643220742809003⟩
  | 70 => ⟨30507189255677022, 31229261581329613, 31951333906982204, 32673406232634795, 33395478558287386⟩
  | 71 => ⟨31233573794161869, 31964270545478972, 32694967296796075, 33425664048113178, 34156360799430281⟩
  | 72 => ⟨31968582758311228, 32707903935292843, 33447225112274458, 34186546289256073, 34925867466237688⟩
  | 73 => ⟨32712216148125099, 33460161750771226, 34208107353417353, 34956052956063480, 35703998558709607⟩
  | 74 => ⟨33464473963603482, 34221043991914121, 34977614020224760, 35734184048535399, 36490754076846038⟩
  | 75 => ⟨34225356204746377, 34990550658721528, 35755745112696679, 36520939566671830, 37286134020646981⟩
  | 76 => ⟨34994862871553784, 35768681751193447, 36542500630833110, 37316319510472773, 38090138390112436⟩
  | 77 => ⟨35772993964025703, 36555437269329878, 37337880574634053, 38120323879938228, 38902767185242403⟩
  | 78 => ⟨36559749482162134, 37350817213130821, 38141884944099508, 38932952675068195, 39724020406036882⟩
  | 79 => ⟨37355129425963077, 38154821582596276, 38954513739229475, 39754205895862674, 40553898052495873⟩
  | 80 => ⟨38159133795428532, 38967450377726243, 39775766960023954, 40584083542321665, 41392400124619376⟩
  | 81 => ⟨38971762590558499, 39788703598520722, 40605644606482945, 41422585614445168, 42239526622407391⟩
  | 82 => ⟨39793015811352978, 40618581244979713, 41444146678606448, 42269712112233183, 43095277545859918⟩
  | 83 => ⟨40622893457811969, 41457083317103216, 42291273176394463, 43125463035685710, 43959652894976957⟩
  | 84 => ⟨41461395529935472, 42304209814891231, 43147024099846990, 43989838384802749, 44832652669758508⟩
  | 85 => ⟨42308522027723487, 43159960738343758, 44011399448964029, 44862838159584300, 45714276870204571⟩
  | 86 => ⟨43164272951176014, 44024336087460797, 44884399223745580, 45744462360030363, 46604525496315146⟩
  | 87 => ⟨44028648300293053, 44897335862242348, 45766023424191643, 46634710986140938, 47503398548090233⟩
  | 88 => ⟨44901648075074604, 45778960062688411, 46656272050302218, 47533584037916025, 48410896025529832⟩
  | 89 => ⟨45783272275520667, 46669208688798986, 47555145102077305, 48441081515355624, 49327017928633943⟩
  | 90 => ⟨46673520901631242, 47568081740574073, 48462642579516904, 49357203418459735, 50251764257402566⟩
  | 91 => ⟨47572393953406329, 48475579218013672, 49378764482621015, 50281949747228358, 51185135011835701⟩
  | 92 => ⟨48479891430845928, 49391701121117783, 50303510811389638, 51215320501661493, 52127130191933348⟩
  | 93 => ⟨49396013333950039, 50316447449886406, 51236881565822773, 52157315681759140, 53077749797695507⟩
  | 94 => ⟨50320759662718662, 51249818204319541, 52178876745920420, 53107935287521299, 54036993829122178⟩
  | 95 => ⟨51254130417151797, 52191813384417188, 53129496351682579, 54067179318947970, 55004862286213361⟩
  | 96 => ⟨52196125597249444, 53142432990179347, 54088740383109250, 55035047776039153, 55981355168969056⟩
  | 97 => ⟨53146745203011603, 54101677021606018, 55056608840200433, 56011540658794848, 56966472477389263⟩
  | 98 => ⟨54105989234438274, 55069545478697201, 56033101722956128, 56996657967215055, 57960214211473982⟩
  | 99 => ⟨55073857691529457, 56046038361452896, 57018219031376335, 57990399701299774, 58962580371223213⟩
  | _ => defaultCosts

def lookup : ℕ → ℕ → Costs
  | 1, v => row1 v
  | 2, v => row2 v
  | 3, v => row3 v
  | 4, v => row4 v
  | 5, v => row5 v
  | 6, v => row6 v
  | 7, v => row7 v
  | 8, v => row8 v
  | 9, v => row9 v
  | 10, v => row10 v
  | 11, v => row11 v
  | 12, v => row12 v
  | 13, v => row13 v
  | 14, v => row14 v
  | 15, v => row15 v
  | 16, v => row16 v
  | 17, v => row17 v
  | 18, v => row18 v
  | 19, v => row19 v
  | 20, v => row20 v
  | 21, v => row21 v
  | 22, v => row22 v
  | 23, v => row23 v
  | 24, v => row24 v
  | 25, v => row25 v
  | 26, v => row26 v
  | 27, v => row27 v
  | 28, v => row28 v
  | _, _ => defaultCosts

def Correct (r v : ℕ) : Prop :=
  let c := lookup r v
  c.c0 = LocatorOrdinaryZConvex.rawCost r v 0 ∧
  c.c1 = LocatorOrdinaryZConvex.rawCost r v 1 ∧
  c.c2 = LocatorOrdinaryZConvex.rawCost r v 2 ∧
  c.c3 = LocatorOrdinaryZConvex.rawCost r v 3 ∧
  c.c4 = LocatorOrdinaryZConvex.rawCost r v 4

instance (r v : ℕ) : Decidable (Correct r v) := by
  unfold Correct
  infer_instance

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostDirectData
end PackedLocator_LocatorPhase6800CarrierCostDirectCore

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck01. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck01

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck01

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 1 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 1 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 1 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 1 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 1 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 1 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 1 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 1 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 1 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 1 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 1 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 1 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 1 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 1 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 1 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 1 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 1 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 1 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 1 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 1 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 1 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 1 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 1 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 1 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 1 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 1 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 1 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 1 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 1 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 1 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 1 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 1 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 1 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 1 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 1 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 1 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 1 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 1 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 1 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 1 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 1 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 1 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 1 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 1 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 1 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 1 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 1 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 1 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 1 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 1 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 1 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 1 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 1 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 1 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 1 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 1 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 1 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 1 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 1 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 1 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 1 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 1 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 1 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 1 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 1 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 1 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 1 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 1 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 1 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 1 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 1 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 1 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 1 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 1 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 1 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 1 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 1 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 1 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 1 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 1 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 1 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 1 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 1 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 1 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 1 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 1 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 1 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 1 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 1 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 1 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 1 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 1 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 1 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 1 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 1 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 1 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 1 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 1 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 1 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 1 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 1 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 1 101 := by
  decide +kernel

@[local simp] private theorem correctV102 : Correct 1 102 := by
  decide +kernel

@[local simp] private theorem correctV103 : Correct 1 103 := by
  decide +kernel

@[local simp] private theorem correctV104 : Correct 1 104 := by
  decide +kernel

@[local simp] private theorem correctV105 : Correct 1 105 := by
  decide +kernel

@[local simp] private theorem correctV106 : Correct 1 106 := by
  decide +kernel

@[local simp] private theorem correctV107 : Correct 1 107 := by
  decide +kernel

@[local simp] private theorem correctV108 : Correct 1 108 := by
  decide +kernel

@[local simp] private theorem correctV109 : Correct 1 109 := by
  decide +kernel

@[local simp] private theorem correctV110 : Correct 1 110 := by
  decide +kernel

@[local simp] private theorem correctV111 : Correct 1 111 := by
  decide +kernel

@[local simp] private theorem correctV112 : Correct 1 112 := by
  decide +kernel

@[local simp] private theorem correctV113 : Correct 1 113 := by
  decide +kernel

@[local simp] private theorem correctV114 : Correct 1 114 := by
  decide +kernel

@[local simp] private theorem correctV115 : Correct 1 115 := by
  decide +kernel

@[local simp] private theorem correctV116 : Correct 1 116 := by
  decide +kernel

@[local simp] private theorem correctV117 : Correct 1 117 := by
  decide +kernel

@[local simp] private theorem correctV118 : Correct 1 118 := by
  decide +kernel

@[local simp] private theorem correctV119 : Correct 1 119 := by
  decide +kernel

@[local simp] private theorem correctV120 : Correct 1 120 := by
  decide +kernel

@[local simp] private theorem correctV121 : Correct 1 121 := by
  decide +kernel

@[local simp] private theorem correctV122 : Correct 1 122 := by
  decide +kernel

@[local simp] private theorem correctV123 : Correct 1 123 := by
  decide +kernel

@[local simp] private theorem correctV124 : Correct 1 124 := by
  decide +kernel

@[local simp] private theorem correctV125 : Correct 1 125 := by
  decide +kernel

@[local simp] private theorem correctV126 : Correct 1 126 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 1), Correct 1 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck01
end PackedLocator_LocatorPhase6800CarrierCostCheck01

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck05. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck05

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck05

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 5 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 5 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 5 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 5 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 5 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 5 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 5 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 5 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 5 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 5 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 5 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 5 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 5 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 5 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 5 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 5 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 5 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 5 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 5 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 5 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 5 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 5 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 5 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 5 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 5 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 5 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 5 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 5 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 5 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 5 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 5 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 5 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 5 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 5 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 5 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 5 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 5 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 5 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 5 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 5 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 5 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 5 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 5 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 5 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 5 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 5 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 5 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 5 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 5 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 5 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 5 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 5 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 5 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 5 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 5 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 5 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 5 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 5 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 5 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 5 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 5 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 5 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 5 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 5 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 5 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 5 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 5 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 5 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 5 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 5 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 5 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 5 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 5 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 5 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 5 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 5 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 5 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 5 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 5 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 5 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 5 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 5 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 5 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 5 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 5 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 5 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 5 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 5 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 5 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 5 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 5 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 5 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 5 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 5 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 5 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 5 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 5 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 5 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 5 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 5 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 5 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 5 101 := by
  decide +kernel

@[local simp] private theorem correctV102 : Correct 5 102 := by
  decide +kernel

@[local simp] private theorem correctV103 : Correct 5 103 := by
  decide +kernel

@[local simp] private theorem correctV104 : Correct 5 104 := by
  decide +kernel

@[local simp] private theorem correctV105 : Correct 5 105 := by
  decide +kernel

@[local simp] private theorem correctV106 : Correct 5 106 := by
  decide +kernel

@[local simp] private theorem correctV107 : Correct 5 107 := by
  decide +kernel

@[local simp] private theorem correctV108 : Correct 5 108 := by
  decide +kernel

@[local simp] private theorem correctV109 : Correct 5 109 := by
  decide +kernel

@[local simp] private theorem correctV110 : Correct 5 110 := by
  decide +kernel

@[local simp] private theorem correctV111 : Correct 5 111 := by
  decide +kernel

@[local simp] private theorem correctV112 : Correct 5 112 := by
  decide +kernel

@[local simp] private theorem correctV113 : Correct 5 113 := by
  decide +kernel

@[local simp] private theorem correctV114 : Correct 5 114 := by
  decide +kernel

@[local simp] private theorem correctV115 : Correct 5 115 := by
  decide +kernel

@[local simp] private theorem correctV116 : Correct 5 116 := by
  decide +kernel

@[local simp] private theorem correctV117 : Correct 5 117 := by
  decide +kernel

@[local simp] private theorem correctV118 : Correct 5 118 := by
  decide +kernel

@[local simp] private theorem correctV119 : Correct 5 119 := by
  decide +kernel

@[local simp] private theorem correctV120 : Correct 5 120 := by
  decide +kernel

@[local simp] private theorem correctV121 : Correct 5 121 := by
  decide +kernel

@[local simp] private theorem correctV122 : Correct 5 122 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 5), Correct 5 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck05
end PackedLocator_LocatorPhase6800CarrierCostCheck05

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck09. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck09

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck09

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 9 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 9 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 9 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 9 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 9 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 9 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 9 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 9 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 9 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 9 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 9 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 9 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 9 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 9 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 9 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 9 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 9 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 9 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 9 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 9 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 9 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 9 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 9 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 9 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 9 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 9 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 9 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 9 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 9 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 9 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 9 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 9 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 9 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 9 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 9 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 9 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 9 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 9 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 9 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 9 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 9 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 9 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 9 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 9 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 9 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 9 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 9 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 9 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 9 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 9 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 9 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 9 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 9 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 9 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 9 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 9 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 9 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 9 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 9 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 9 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 9 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 9 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 9 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 9 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 9 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 9 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 9 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 9 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 9 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 9 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 9 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 9 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 9 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 9 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 9 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 9 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 9 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 9 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 9 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 9 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 9 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 9 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 9 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 9 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 9 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 9 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 9 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 9 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 9 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 9 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 9 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 9 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 9 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 9 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 9 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 9 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 9 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 9 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 9 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 9 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 9 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 9 101 := by
  decide +kernel

@[local simp] private theorem correctV102 : Correct 9 102 := by
  decide +kernel

@[local simp] private theorem correctV103 : Correct 9 103 := by
  decide +kernel

@[local simp] private theorem correctV104 : Correct 9 104 := by
  decide +kernel

@[local simp] private theorem correctV105 : Correct 9 105 := by
  decide +kernel

@[local simp] private theorem correctV106 : Correct 9 106 := by
  decide +kernel

@[local simp] private theorem correctV107 : Correct 9 107 := by
  decide +kernel

@[local simp] private theorem correctV108 : Correct 9 108 := by
  decide +kernel

@[local simp] private theorem correctV109 : Correct 9 109 := by
  decide +kernel

@[local simp] private theorem correctV110 : Correct 9 110 := by
  decide +kernel

@[local simp] private theorem correctV111 : Correct 9 111 := by
  decide +kernel

@[local simp] private theorem correctV112 : Correct 9 112 := by
  decide +kernel

@[local simp] private theorem correctV113 : Correct 9 113 := by
  decide +kernel

@[local simp] private theorem correctV114 : Correct 9 114 := by
  decide +kernel

@[local simp] private theorem correctV115 : Correct 9 115 := by
  decide +kernel

@[local simp] private theorem correctV116 : Correct 9 116 := by
  decide +kernel

@[local simp] private theorem correctV117 : Correct 9 117 := by
  decide +kernel

@[local simp] private theorem correctV118 : Correct 9 118 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 9), Correct 9 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck09
end PackedLocator_LocatorPhase6800CarrierCostCheck09

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck13. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck13

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck13

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 13 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 13 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 13 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 13 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 13 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 13 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 13 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 13 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 13 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 13 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 13 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 13 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 13 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 13 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 13 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 13 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 13 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 13 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 13 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 13 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 13 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 13 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 13 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 13 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 13 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 13 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 13 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 13 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 13 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 13 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 13 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 13 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 13 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 13 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 13 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 13 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 13 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 13 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 13 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 13 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 13 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 13 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 13 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 13 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 13 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 13 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 13 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 13 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 13 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 13 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 13 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 13 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 13 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 13 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 13 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 13 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 13 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 13 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 13 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 13 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 13 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 13 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 13 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 13 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 13 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 13 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 13 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 13 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 13 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 13 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 13 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 13 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 13 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 13 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 13 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 13 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 13 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 13 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 13 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 13 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 13 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 13 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 13 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 13 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 13 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 13 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 13 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 13 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 13 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 13 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 13 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 13 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 13 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 13 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 13 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 13 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 13 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 13 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 13 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 13 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 13 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 13 101 := by
  decide +kernel

@[local simp] private theorem correctV102 : Correct 13 102 := by
  decide +kernel

@[local simp] private theorem correctV103 : Correct 13 103 := by
  decide +kernel

@[local simp] private theorem correctV104 : Correct 13 104 := by
  decide +kernel

@[local simp] private theorem correctV105 : Correct 13 105 := by
  decide +kernel

@[local simp] private theorem correctV106 : Correct 13 106 := by
  decide +kernel

@[local simp] private theorem correctV107 : Correct 13 107 := by
  decide +kernel

@[local simp] private theorem correctV108 : Correct 13 108 := by
  decide +kernel

@[local simp] private theorem correctV109 : Correct 13 109 := by
  decide +kernel

@[local simp] private theorem correctV110 : Correct 13 110 := by
  decide +kernel

@[local simp] private theorem correctV111 : Correct 13 111 := by
  decide +kernel

@[local simp] private theorem correctV112 : Correct 13 112 := by
  decide +kernel

@[local simp] private theorem correctV113 : Correct 13 113 := by
  decide +kernel

@[local simp] private theorem correctV114 : Correct 13 114 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 13), Correct 13 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck13
end PackedLocator_LocatorPhase6800CarrierCostCheck13

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck17. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck17

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck17

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 17 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 17 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 17 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 17 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 17 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 17 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 17 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 17 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 17 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 17 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 17 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 17 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 17 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 17 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 17 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 17 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 17 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 17 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 17 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 17 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 17 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 17 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 17 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 17 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 17 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 17 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 17 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 17 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 17 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 17 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 17 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 17 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 17 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 17 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 17 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 17 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 17 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 17 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 17 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 17 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 17 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 17 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 17 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 17 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 17 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 17 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 17 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 17 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 17 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 17 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 17 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 17 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 17 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 17 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 17 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 17 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 17 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 17 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 17 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 17 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 17 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 17 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 17 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 17 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 17 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 17 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 17 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 17 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 17 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 17 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 17 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 17 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 17 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 17 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 17 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 17 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 17 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 17 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 17 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 17 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 17 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 17 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 17 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 17 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 17 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 17 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 17 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 17 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 17 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 17 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 17 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 17 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 17 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 17 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 17 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 17 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 17 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 17 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 17 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 17 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 17 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 17 101 := by
  decide +kernel

@[local simp] private theorem correctV102 : Correct 17 102 := by
  decide +kernel

@[local simp] private theorem correctV103 : Correct 17 103 := by
  decide +kernel

@[local simp] private theorem correctV104 : Correct 17 104 := by
  decide +kernel

@[local simp] private theorem correctV105 : Correct 17 105 := by
  decide +kernel

@[local simp] private theorem correctV106 : Correct 17 106 := by
  decide +kernel

@[local simp] private theorem correctV107 : Correct 17 107 := by
  decide +kernel

@[local simp] private theorem correctV108 : Correct 17 108 := by
  decide +kernel

@[local simp] private theorem correctV109 : Correct 17 109 := by
  decide +kernel

@[local simp] private theorem correctV110 : Correct 17 110 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 17), Correct 17 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck17
end PackedLocator_LocatorPhase6800CarrierCostCheck17

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck21. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck21

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck21

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 21 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 21 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 21 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 21 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 21 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 21 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 21 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 21 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 21 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 21 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 21 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 21 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 21 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 21 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 21 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 21 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 21 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 21 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 21 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 21 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 21 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 21 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 21 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 21 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 21 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 21 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 21 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 21 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 21 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 21 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 21 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 21 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 21 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 21 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 21 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 21 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 21 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 21 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 21 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 21 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 21 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 21 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 21 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 21 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 21 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 21 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 21 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 21 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 21 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 21 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 21 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 21 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 21 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 21 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 21 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 21 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 21 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 21 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 21 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 21 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 21 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 21 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 21 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 21 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 21 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 21 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 21 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 21 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 21 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 21 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 21 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 21 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 21 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 21 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 21 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 21 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 21 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 21 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 21 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 21 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 21 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 21 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 21 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 21 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 21 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 21 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 21 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 21 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 21 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 21 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 21 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 21 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 21 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 21 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 21 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 21 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 21 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 21 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 21 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 21 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 21 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 21 101 := by
  decide +kernel

@[local simp] private theorem correctV102 : Correct 21 102 := by
  decide +kernel

@[local simp] private theorem correctV103 : Correct 21 103 := by
  decide +kernel

@[local simp] private theorem correctV104 : Correct 21 104 := by
  decide +kernel

@[local simp] private theorem correctV105 : Correct 21 105 := by
  decide +kernel

@[local simp] private theorem correctV106 : Correct 21 106 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 21), Correct 21 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck21
end PackedLocator_LocatorPhase6800CarrierCostCheck21

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck25. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck25

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck25

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 25 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 25 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 25 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 25 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 25 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 25 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 25 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 25 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 25 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 25 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 25 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 25 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 25 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 25 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 25 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 25 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 25 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 25 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 25 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 25 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 25 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 25 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 25 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 25 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 25 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 25 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 25 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 25 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 25 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 25 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 25 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 25 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 25 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 25 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 25 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 25 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 25 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 25 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 25 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 25 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 25 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 25 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 25 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 25 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 25 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 25 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 25 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 25 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 25 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 25 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 25 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 25 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 25 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 25 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 25 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 25 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 25 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 25 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 25 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 25 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 25 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 25 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 25 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 25 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 25 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 25 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 25 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 25 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 25 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 25 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 25 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 25 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 25 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 25 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 25 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 25 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 25 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 25 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 25 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 25 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 25 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 25 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 25 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 25 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 25 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 25 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 25 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 25 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 25 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 25 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 25 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 25 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 25 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 25 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 25 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 25 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 25 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 25 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 25 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 25 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 25 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 25 101 := by
  decide +kernel

@[local simp] private theorem correctV102 : Correct 25 102 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 25), Correct 25 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck25
end PackedLocator_LocatorPhase6800CarrierCostCheck25

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck02. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck02

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck02

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 2 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 2 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 2 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 2 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 2 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 2 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 2 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 2 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 2 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 2 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 2 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 2 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 2 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 2 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 2 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 2 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 2 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 2 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 2 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 2 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 2 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 2 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 2 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 2 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 2 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 2 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 2 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 2 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 2 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 2 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 2 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 2 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 2 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 2 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 2 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 2 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 2 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 2 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 2 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 2 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 2 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 2 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 2 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 2 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 2 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 2 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 2 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 2 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 2 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 2 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 2 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 2 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 2 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 2 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 2 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 2 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 2 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 2 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 2 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 2 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 2 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 2 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 2 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 2 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 2 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 2 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 2 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 2 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 2 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 2 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 2 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 2 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 2 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 2 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 2 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 2 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 2 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 2 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 2 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 2 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 2 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 2 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 2 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 2 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 2 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 2 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 2 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 2 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 2 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 2 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 2 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 2 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 2 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 2 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 2 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 2 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 2 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 2 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 2 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 2 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 2 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 2 101 := by
  decide +kernel

@[local simp] private theorem correctV102 : Correct 2 102 := by
  decide +kernel

@[local simp] private theorem correctV103 : Correct 2 103 := by
  decide +kernel

@[local simp] private theorem correctV104 : Correct 2 104 := by
  decide +kernel

@[local simp] private theorem correctV105 : Correct 2 105 := by
  decide +kernel

@[local simp] private theorem correctV106 : Correct 2 106 := by
  decide +kernel

@[local simp] private theorem correctV107 : Correct 2 107 := by
  decide +kernel

@[local simp] private theorem correctV108 : Correct 2 108 := by
  decide +kernel

@[local simp] private theorem correctV109 : Correct 2 109 := by
  decide +kernel

@[local simp] private theorem correctV110 : Correct 2 110 := by
  decide +kernel

@[local simp] private theorem correctV111 : Correct 2 111 := by
  decide +kernel

@[local simp] private theorem correctV112 : Correct 2 112 := by
  decide +kernel

@[local simp] private theorem correctV113 : Correct 2 113 := by
  decide +kernel

@[local simp] private theorem correctV114 : Correct 2 114 := by
  decide +kernel

@[local simp] private theorem correctV115 : Correct 2 115 := by
  decide +kernel

@[local simp] private theorem correctV116 : Correct 2 116 := by
  decide +kernel

@[local simp] private theorem correctV117 : Correct 2 117 := by
  decide +kernel

@[local simp] private theorem correctV118 : Correct 2 118 := by
  decide +kernel

@[local simp] private theorem correctV119 : Correct 2 119 := by
  decide +kernel

@[local simp] private theorem correctV120 : Correct 2 120 := by
  decide +kernel

@[local simp] private theorem correctV121 : Correct 2 121 := by
  decide +kernel

@[local simp] private theorem correctV122 : Correct 2 122 := by
  decide +kernel

@[local simp] private theorem correctV123 : Correct 2 123 := by
  decide +kernel

@[local simp] private theorem correctV124 : Correct 2 124 := by
  decide +kernel

@[local simp] private theorem correctV125 : Correct 2 125 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 2), Correct 2 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck02
end PackedLocator_LocatorPhase6800CarrierCostCheck02

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck06. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck06

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck06

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 6 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 6 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 6 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 6 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 6 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 6 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 6 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 6 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 6 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 6 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 6 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 6 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 6 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 6 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 6 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 6 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 6 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 6 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 6 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 6 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 6 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 6 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 6 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 6 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 6 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 6 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 6 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 6 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 6 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 6 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 6 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 6 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 6 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 6 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 6 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 6 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 6 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 6 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 6 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 6 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 6 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 6 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 6 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 6 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 6 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 6 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 6 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 6 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 6 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 6 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 6 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 6 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 6 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 6 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 6 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 6 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 6 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 6 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 6 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 6 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 6 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 6 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 6 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 6 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 6 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 6 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 6 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 6 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 6 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 6 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 6 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 6 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 6 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 6 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 6 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 6 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 6 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 6 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 6 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 6 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 6 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 6 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 6 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 6 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 6 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 6 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 6 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 6 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 6 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 6 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 6 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 6 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 6 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 6 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 6 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 6 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 6 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 6 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 6 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 6 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 6 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 6 101 := by
  decide +kernel

@[local simp] private theorem correctV102 : Correct 6 102 := by
  decide +kernel

@[local simp] private theorem correctV103 : Correct 6 103 := by
  decide +kernel

@[local simp] private theorem correctV104 : Correct 6 104 := by
  decide +kernel

@[local simp] private theorem correctV105 : Correct 6 105 := by
  decide +kernel

@[local simp] private theorem correctV106 : Correct 6 106 := by
  decide +kernel

@[local simp] private theorem correctV107 : Correct 6 107 := by
  decide +kernel

@[local simp] private theorem correctV108 : Correct 6 108 := by
  decide +kernel

@[local simp] private theorem correctV109 : Correct 6 109 := by
  decide +kernel

@[local simp] private theorem correctV110 : Correct 6 110 := by
  decide +kernel

@[local simp] private theorem correctV111 : Correct 6 111 := by
  decide +kernel

@[local simp] private theorem correctV112 : Correct 6 112 := by
  decide +kernel

@[local simp] private theorem correctV113 : Correct 6 113 := by
  decide +kernel

@[local simp] private theorem correctV114 : Correct 6 114 := by
  decide +kernel

@[local simp] private theorem correctV115 : Correct 6 115 := by
  decide +kernel

@[local simp] private theorem correctV116 : Correct 6 116 := by
  decide +kernel

@[local simp] private theorem correctV117 : Correct 6 117 := by
  decide +kernel

@[local simp] private theorem correctV118 : Correct 6 118 := by
  decide +kernel

@[local simp] private theorem correctV119 : Correct 6 119 := by
  decide +kernel

@[local simp] private theorem correctV120 : Correct 6 120 := by
  decide +kernel

@[local simp] private theorem correctV121 : Correct 6 121 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 6), Correct 6 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck06
end PackedLocator_LocatorPhase6800CarrierCostCheck06

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck10. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck10

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck10

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 10 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 10 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 10 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 10 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 10 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 10 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 10 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 10 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 10 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 10 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 10 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 10 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 10 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 10 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 10 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 10 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 10 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 10 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 10 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 10 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 10 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 10 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 10 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 10 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 10 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 10 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 10 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 10 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 10 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 10 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 10 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 10 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 10 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 10 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 10 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 10 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 10 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 10 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 10 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 10 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 10 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 10 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 10 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 10 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 10 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 10 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 10 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 10 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 10 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 10 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 10 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 10 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 10 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 10 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 10 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 10 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 10 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 10 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 10 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 10 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 10 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 10 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 10 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 10 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 10 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 10 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 10 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 10 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 10 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 10 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 10 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 10 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 10 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 10 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 10 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 10 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 10 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 10 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 10 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 10 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 10 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 10 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 10 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 10 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 10 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 10 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 10 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 10 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 10 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 10 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 10 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 10 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 10 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 10 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 10 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 10 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 10 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 10 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 10 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 10 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 10 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 10 101 := by
  decide +kernel

@[local simp] private theorem correctV102 : Correct 10 102 := by
  decide +kernel

@[local simp] private theorem correctV103 : Correct 10 103 := by
  decide +kernel

@[local simp] private theorem correctV104 : Correct 10 104 := by
  decide +kernel

@[local simp] private theorem correctV105 : Correct 10 105 := by
  decide +kernel

@[local simp] private theorem correctV106 : Correct 10 106 := by
  decide +kernel

@[local simp] private theorem correctV107 : Correct 10 107 := by
  decide +kernel

@[local simp] private theorem correctV108 : Correct 10 108 := by
  decide +kernel

@[local simp] private theorem correctV109 : Correct 10 109 := by
  decide +kernel

@[local simp] private theorem correctV110 : Correct 10 110 := by
  decide +kernel

@[local simp] private theorem correctV111 : Correct 10 111 := by
  decide +kernel

@[local simp] private theorem correctV112 : Correct 10 112 := by
  decide +kernel

@[local simp] private theorem correctV113 : Correct 10 113 := by
  decide +kernel

@[local simp] private theorem correctV114 : Correct 10 114 := by
  decide +kernel

@[local simp] private theorem correctV115 : Correct 10 115 := by
  decide +kernel

@[local simp] private theorem correctV116 : Correct 10 116 := by
  decide +kernel

@[local simp] private theorem correctV117 : Correct 10 117 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 10), Correct 10 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck10
end PackedLocator_LocatorPhase6800CarrierCostCheck10

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck14. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck14

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck14

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 14 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 14 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 14 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 14 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 14 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 14 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 14 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 14 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 14 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 14 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 14 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 14 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 14 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 14 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 14 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 14 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 14 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 14 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 14 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 14 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 14 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 14 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 14 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 14 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 14 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 14 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 14 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 14 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 14 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 14 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 14 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 14 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 14 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 14 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 14 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 14 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 14 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 14 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 14 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 14 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 14 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 14 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 14 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 14 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 14 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 14 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 14 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 14 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 14 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 14 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 14 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 14 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 14 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 14 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 14 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 14 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 14 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 14 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 14 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 14 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 14 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 14 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 14 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 14 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 14 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 14 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 14 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 14 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 14 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 14 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 14 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 14 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 14 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 14 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 14 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 14 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 14 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 14 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 14 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 14 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 14 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 14 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 14 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 14 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 14 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 14 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 14 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 14 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 14 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 14 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 14 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 14 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 14 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 14 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 14 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 14 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 14 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 14 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 14 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 14 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 14 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 14 101 := by
  decide +kernel

@[local simp] private theorem correctV102 : Correct 14 102 := by
  decide +kernel

@[local simp] private theorem correctV103 : Correct 14 103 := by
  decide +kernel

@[local simp] private theorem correctV104 : Correct 14 104 := by
  decide +kernel

@[local simp] private theorem correctV105 : Correct 14 105 := by
  decide +kernel

@[local simp] private theorem correctV106 : Correct 14 106 := by
  decide +kernel

@[local simp] private theorem correctV107 : Correct 14 107 := by
  decide +kernel

@[local simp] private theorem correctV108 : Correct 14 108 := by
  decide +kernel

@[local simp] private theorem correctV109 : Correct 14 109 := by
  decide +kernel

@[local simp] private theorem correctV110 : Correct 14 110 := by
  decide +kernel

@[local simp] private theorem correctV111 : Correct 14 111 := by
  decide +kernel

@[local simp] private theorem correctV112 : Correct 14 112 := by
  decide +kernel

@[local simp] private theorem correctV113 : Correct 14 113 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 14), Correct 14 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck14
end PackedLocator_LocatorPhase6800CarrierCostCheck14

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck18. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck18

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck18

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 18 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 18 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 18 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 18 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 18 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 18 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 18 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 18 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 18 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 18 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 18 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 18 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 18 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 18 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 18 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 18 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 18 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 18 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 18 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 18 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 18 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 18 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 18 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 18 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 18 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 18 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 18 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 18 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 18 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 18 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 18 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 18 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 18 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 18 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 18 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 18 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 18 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 18 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 18 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 18 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 18 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 18 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 18 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 18 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 18 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 18 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 18 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 18 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 18 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 18 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 18 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 18 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 18 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 18 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 18 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 18 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 18 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 18 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 18 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 18 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 18 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 18 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 18 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 18 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 18 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 18 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 18 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 18 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 18 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 18 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 18 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 18 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 18 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 18 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 18 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 18 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 18 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 18 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 18 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 18 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 18 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 18 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 18 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 18 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 18 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 18 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 18 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 18 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 18 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 18 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 18 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 18 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 18 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 18 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 18 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 18 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 18 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 18 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 18 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 18 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 18 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 18 101 := by
  decide +kernel

@[local simp] private theorem correctV102 : Correct 18 102 := by
  decide +kernel

@[local simp] private theorem correctV103 : Correct 18 103 := by
  decide +kernel

@[local simp] private theorem correctV104 : Correct 18 104 := by
  decide +kernel

@[local simp] private theorem correctV105 : Correct 18 105 := by
  decide +kernel

@[local simp] private theorem correctV106 : Correct 18 106 := by
  decide +kernel

@[local simp] private theorem correctV107 : Correct 18 107 := by
  decide +kernel

@[local simp] private theorem correctV108 : Correct 18 108 := by
  decide +kernel

@[local simp] private theorem correctV109 : Correct 18 109 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 18), Correct 18 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck18
end PackedLocator_LocatorPhase6800CarrierCostCheck18

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck22. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck22

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck22

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 22 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 22 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 22 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 22 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 22 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 22 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 22 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 22 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 22 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 22 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 22 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 22 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 22 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 22 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 22 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 22 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 22 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 22 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 22 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 22 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 22 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 22 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 22 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 22 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 22 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 22 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 22 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 22 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 22 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 22 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 22 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 22 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 22 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 22 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 22 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 22 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 22 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 22 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 22 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 22 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 22 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 22 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 22 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 22 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 22 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 22 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 22 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 22 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 22 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 22 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 22 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 22 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 22 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 22 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 22 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 22 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 22 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 22 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 22 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 22 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 22 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 22 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 22 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 22 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 22 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 22 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 22 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 22 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 22 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 22 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 22 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 22 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 22 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 22 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 22 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 22 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 22 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 22 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 22 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 22 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 22 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 22 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 22 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 22 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 22 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 22 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 22 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 22 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 22 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 22 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 22 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 22 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 22 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 22 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 22 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 22 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 22 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 22 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 22 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 22 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 22 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 22 101 := by
  decide +kernel

@[local simp] private theorem correctV102 : Correct 22 102 := by
  decide +kernel

@[local simp] private theorem correctV103 : Correct 22 103 := by
  decide +kernel

@[local simp] private theorem correctV104 : Correct 22 104 := by
  decide +kernel

@[local simp] private theorem correctV105 : Correct 22 105 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 22), Correct 22 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck22
end PackedLocator_LocatorPhase6800CarrierCostCheck22

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck26. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck26

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck26

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 26 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 26 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 26 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 26 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 26 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 26 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 26 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 26 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 26 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 26 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 26 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 26 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 26 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 26 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 26 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 26 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 26 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 26 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 26 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 26 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 26 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 26 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 26 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 26 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 26 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 26 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 26 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 26 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 26 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 26 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 26 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 26 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 26 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 26 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 26 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 26 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 26 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 26 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 26 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 26 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 26 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 26 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 26 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 26 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 26 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 26 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 26 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 26 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 26 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 26 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 26 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 26 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 26 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 26 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 26 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 26 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 26 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 26 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 26 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 26 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 26 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 26 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 26 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 26 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 26 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 26 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 26 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 26 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 26 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 26 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 26 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 26 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 26 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 26 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 26 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 26 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 26 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 26 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 26 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 26 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 26 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 26 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 26 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 26 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 26 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 26 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 26 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 26 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 26 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 26 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 26 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 26 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 26 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 26 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 26 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 26 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 26 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 26 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 26 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 26 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 26 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 26 101 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 26), Correct 26 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck26
end PackedLocator_LocatorPhase6800CarrierCostCheck26

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck03. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck03

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck03

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 3 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 3 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 3 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 3 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 3 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 3 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 3 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 3 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 3 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 3 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 3 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 3 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 3 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 3 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 3 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 3 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 3 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 3 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 3 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 3 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 3 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 3 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 3 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 3 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 3 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 3 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 3 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 3 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 3 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 3 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 3 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 3 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 3 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 3 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 3 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 3 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 3 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 3 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 3 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 3 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 3 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 3 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 3 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 3 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 3 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 3 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 3 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 3 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 3 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 3 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 3 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 3 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 3 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 3 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 3 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 3 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 3 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 3 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 3 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 3 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 3 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 3 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 3 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 3 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 3 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 3 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 3 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 3 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 3 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 3 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 3 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 3 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 3 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 3 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 3 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 3 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 3 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 3 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 3 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 3 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 3 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 3 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 3 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 3 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 3 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 3 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 3 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 3 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 3 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 3 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 3 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 3 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 3 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 3 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 3 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 3 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 3 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 3 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 3 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 3 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 3 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 3 101 := by
  decide +kernel

@[local simp] private theorem correctV102 : Correct 3 102 := by
  decide +kernel

@[local simp] private theorem correctV103 : Correct 3 103 := by
  decide +kernel

@[local simp] private theorem correctV104 : Correct 3 104 := by
  decide +kernel

@[local simp] private theorem correctV105 : Correct 3 105 := by
  decide +kernel

@[local simp] private theorem correctV106 : Correct 3 106 := by
  decide +kernel

@[local simp] private theorem correctV107 : Correct 3 107 := by
  decide +kernel

@[local simp] private theorem correctV108 : Correct 3 108 := by
  decide +kernel

@[local simp] private theorem correctV109 : Correct 3 109 := by
  decide +kernel

@[local simp] private theorem correctV110 : Correct 3 110 := by
  decide +kernel

@[local simp] private theorem correctV111 : Correct 3 111 := by
  decide +kernel

@[local simp] private theorem correctV112 : Correct 3 112 := by
  decide +kernel

@[local simp] private theorem correctV113 : Correct 3 113 := by
  decide +kernel

@[local simp] private theorem correctV114 : Correct 3 114 := by
  decide +kernel

@[local simp] private theorem correctV115 : Correct 3 115 := by
  decide +kernel

@[local simp] private theorem correctV116 : Correct 3 116 := by
  decide +kernel

@[local simp] private theorem correctV117 : Correct 3 117 := by
  decide +kernel

@[local simp] private theorem correctV118 : Correct 3 118 := by
  decide +kernel

@[local simp] private theorem correctV119 : Correct 3 119 := by
  decide +kernel

@[local simp] private theorem correctV120 : Correct 3 120 := by
  decide +kernel

@[local simp] private theorem correctV121 : Correct 3 121 := by
  decide +kernel

@[local simp] private theorem correctV122 : Correct 3 122 := by
  decide +kernel

@[local simp] private theorem correctV123 : Correct 3 123 := by
  decide +kernel

@[local simp] private theorem correctV124 : Correct 3 124 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 3), Correct 3 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck03
end PackedLocator_LocatorPhase6800CarrierCostCheck03

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck07. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck07

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck07

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 7 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 7 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 7 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 7 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 7 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 7 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 7 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 7 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 7 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 7 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 7 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 7 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 7 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 7 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 7 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 7 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 7 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 7 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 7 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 7 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 7 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 7 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 7 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 7 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 7 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 7 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 7 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 7 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 7 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 7 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 7 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 7 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 7 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 7 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 7 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 7 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 7 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 7 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 7 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 7 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 7 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 7 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 7 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 7 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 7 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 7 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 7 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 7 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 7 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 7 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 7 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 7 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 7 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 7 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 7 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 7 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 7 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 7 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 7 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 7 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 7 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 7 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 7 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 7 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 7 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 7 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 7 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 7 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 7 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 7 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 7 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 7 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 7 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 7 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 7 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 7 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 7 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 7 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 7 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 7 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 7 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 7 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 7 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 7 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 7 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 7 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 7 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 7 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 7 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 7 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 7 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 7 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 7 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 7 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 7 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 7 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 7 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 7 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 7 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 7 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 7 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 7 101 := by
  decide +kernel

@[local simp] private theorem correctV102 : Correct 7 102 := by
  decide +kernel

@[local simp] private theorem correctV103 : Correct 7 103 := by
  decide +kernel

@[local simp] private theorem correctV104 : Correct 7 104 := by
  decide +kernel

@[local simp] private theorem correctV105 : Correct 7 105 := by
  decide +kernel

@[local simp] private theorem correctV106 : Correct 7 106 := by
  decide +kernel

@[local simp] private theorem correctV107 : Correct 7 107 := by
  decide +kernel

@[local simp] private theorem correctV108 : Correct 7 108 := by
  decide +kernel

@[local simp] private theorem correctV109 : Correct 7 109 := by
  decide +kernel

@[local simp] private theorem correctV110 : Correct 7 110 := by
  decide +kernel

@[local simp] private theorem correctV111 : Correct 7 111 := by
  decide +kernel

@[local simp] private theorem correctV112 : Correct 7 112 := by
  decide +kernel

@[local simp] private theorem correctV113 : Correct 7 113 := by
  decide +kernel

@[local simp] private theorem correctV114 : Correct 7 114 := by
  decide +kernel

@[local simp] private theorem correctV115 : Correct 7 115 := by
  decide +kernel

@[local simp] private theorem correctV116 : Correct 7 116 := by
  decide +kernel

@[local simp] private theorem correctV117 : Correct 7 117 := by
  decide +kernel

@[local simp] private theorem correctV118 : Correct 7 118 := by
  decide +kernel

@[local simp] private theorem correctV119 : Correct 7 119 := by
  decide +kernel

@[local simp] private theorem correctV120 : Correct 7 120 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 7), Correct 7 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck07
end PackedLocator_LocatorPhase6800CarrierCostCheck07

/-! Packed from ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck11. -/
section PackedLocator_LocatorPhase6800CarrierCostCheck11

namespace ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck11

open LocatorPhase6800CarrierCostDirectData

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem correctV0 : Correct 11 0 := by
  decide +kernel

@[local simp] private theorem correctV1 : Correct 11 1 := by
  decide +kernel

@[local simp] private theorem correctV2 : Correct 11 2 := by
  decide +kernel

@[local simp] private theorem correctV3 : Correct 11 3 := by
  decide +kernel

@[local simp] private theorem correctV4 : Correct 11 4 := by
  decide +kernel

@[local simp] private theorem correctV5 : Correct 11 5 := by
  decide +kernel

@[local simp] private theorem correctV6 : Correct 11 6 := by
  decide +kernel

@[local simp] private theorem correctV7 : Correct 11 7 := by
  decide +kernel

@[local simp] private theorem correctV8 : Correct 11 8 := by
  decide +kernel

@[local simp] private theorem correctV9 : Correct 11 9 := by
  decide +kernel

@[local simp] private theorem correctV10 : Correct 11 10 := by
  decide +kernel

@[local simp] private theorem correctV11 : Correct 11 11 := by
  decide +kernel

@[local simp] private theorem correctV12 : Correct 11 12 := by
  decide +kernel

@[local simp] private theorem correctV13 : Correct 11 13 := by
  decide +kernel

@[local simp] private theorem correctV14 : Correct 11 14 := by
  decide +kernel

@[local simp] private theorem correctV15 : Correct 11 15 := by
  decide +kernel

@[local simp] private theorem correctV16 : Correct 11 16 := by
  decide +kernel

@[local simp] private theorem correctV17 : Correct 11 17 := by
  decide +kernel

@[local simp] private theorem correctV18 : Correct 11 18 := by
  decide +kernel

@[local simp] private theorem correctV19 : Correct 11 19 := by
  decide +kernel

@[local simp] private theorem correctV20 : Correct 11 20 := by
  decide +kernel

@[local simp] private theorem correctV21 : Correct 11 21 := by
  decide +kernel

@[local simp] private theorem correctV22 : Correct 11 22 := by
  decide +kernel

@[local simp] private theorem correctV23 : Correct 11 23 := by
  decide +kernel

@[local simp] private theorem correctV24 : Correct 11 24 := by
  decide +kernel

@[local simp] private theorem correctV25 : Correct 11 25 := by
  decide +kernel

@[local simp] private theorem correctV26 : Correct 11 26 := by
  decide +kernel

@[local simp] private theorem correctV27 : Correct 11 27 := by
  decide +kernel

@[local simp] private theorem correctV28 : Correct 11 28 := by
  decide +kernel

@[local simp] private theorem correctV29 : Correct 11 29 := by
  decide +kernel

@[local simp] private theorem correctV30 : Correct 11 30 := by
  decide +kernel

@[local simp] private theorem correctV31 : Correct 11 31 := by
  decide +kernel

@[local simp] private theorem correctV32 : Correct 11 32 := by
  decide +kernel

@[local simp] private theorem correctV33 : Correct 11 33 := by
  decide +kernel

@[local simp] private theorem correctV34 : Correct 11 34 := by
  decide +kernel

@[local simp] private theorem correctV35 : Correct 11 35 := by
  decide +kernel

@[local simp] private theorem correctV36 : Correct 11 36 := by
  decide +kernel

@[local simp] private theorem correctV37 : Correct 11 37 := by
  decide +kernel

@[local simp] private theorem correctV38 : Correct 11 38 := by
  decide +kernel

@[local simp] private theorem correctV39 : Correct 11 39 := by
  decide +kernel

@[local simp] private theorem correctV40 : Correct 11 40 := by
  decide +kernel

@[local simp] private theorem correctV41 : Correct 11 41 := by
  decide +kernel

@[local simp] private theorem correctV42 : Correct 11 42 := by
  decide +kernel

@[local simp] private theorem correctV43 : Correct 11 43 := by
  decide +kernel

@[local simp] private theorem correctV44 : Correct 11 44 := by
  decide +kernel

@[local simp] private theorem correctV45 : Correct 11 45 := by
  decide +kernel

@[local simp] private theorem correctV46 : Correct 11 46 := by
  decide +kernel

@[local simp] private theorem correctV47 : Correct 11 47 := by
  decide +kernel

@[local simp] private theorem correctV48 : Correct 11 48 := by
  decide +kernel

@[local simp] private theorem correctV49 : Correct 11 49 := by
  decide +kernel

@[local simp] private theorem correctV50 : Correct 11 50 := by
  decide +kernel

@[local simp] private theorem correctV51 : Correct 11 51 := by
  decide +kernel

@[local simp] private theorem correctV52 : Correct 11 52 := by
  decide +kernel

@[local simp] private theorem correctV53 : Correct 11 53 := by
  decide +kernel

@[local simp] private theorem correctV54 : Correct 11 54 := by
  decide +kernel

@[local simp] private theorem correctV55 : Correct 11 55 := by
  decide +kernel

@[local simp] private theorem correctV56 : Correct 11 56 := by
  decide +kernel

@[local simp] private theorem correctV57 : Correct 11 57 := by
  decide +kernel

@[local simp] private theorem correctV58 : Correct 11 58 := by
  decide +kernel

@[local simp] private theorem correctV59 : Correct 11 59 := by
  decide +kernel

@[local simp] private theorem correctV60 : Correct 11 60 := by
  decide +kernel

@[local simp] private theorem correctV61 : Correct 11 61 := by
  decide +kernel

@[local simp] private theorem correctV62 : Correct 11 62 := by
  decide +kernel

@[local simp] private theorem correctV63 : Correct 11 63 := by
  decide +kernel

@[local simp] private theorem correctV64 : Correct 11 64 := by
  decide +kernel

@[local simp] private theorem correctV65 : Correct 11 65 := by
  decide +kernel

@[local simp] private theorem correctV66 : Correct 11 66 := by
  decide +kernel

@[local simp] private theorem correctV67 : Correct 11 67 := by
  decide +kernel

@[local simp] private theorem correctV68 : Correct 11 68 := by
  decide +kernel

@[local simp] private theorem correctV69 : Correct 11 69 := by
  decide +kernel

@[local simp] private theorem correctV70 : Correct 11 70 := by
  decide +kernel

@[local simp] private theorem correctV71 : Correct 11 71 := by
  decide +kernel

@[local simp] private theorem correctV72 : Correct 11 72 := by
  decide +kernel

@[local simp] private theorem correctV73 : Correct 11 73 := by
  decide +kernel

@[local simp] private theorem correctV74 : Correct 11 74 := by
  decide +kernel

@[local simp] private theorem correctV75 : Correct 11 75 := by
  decide +kernel

@[local simp] private theorem correctV76 : Correct 11 76 := by
  decide +kernel

@[local simp] private theorem correctV77 : Correct 11 77 := by
  decide +kernel

@[local simp] private theorem correctV78 : Correct 11 78 := by
  decide +kernel

@[local simp] private theorem correctV79 : Correct 11 79 := by
  decide +kernel

@[local simp] private theorem correctV80 : Correct 11 80 := by
  decide +kernel

@[local simp] private theorem correctV81 : Correct 11 81 := by
  decide +kernel

@[local simp] private theorem correctV82 : Correct 11 82 := by
  decide +kernel

@[local simp] private theorem correctV83 : Correct 11 83 := by
  decide +kernel

@[local simp] private theorem correctV84 : Correct 11 84 := by
  decide +kernel

@[local simp] private theorem correctV85 : Correct 11 85 := by
  decide +kernel

@[local simp] private theorem correctV86 : Correct 11 86 := by
  decide +kernel

@[local simp] private theorem correctV87 : Correct 11 87 := by
  decide +kernel

@[local simp] private theorem correctV88 : Correct 11 88 := by
  decide +kernel

@[local simp] private theorem correctV89 : Correct 11 89 := by
  decide +kernel

@[local simp] private theorem correctV90 : Correct 11 90 := by
  decide +kernel

@[local simp] private theorem correctV91 : Correct 11 91 := by
  decide +kernel

@[local simp] private theorem correctV92 : Correct 11 92 := by
  decide +kernel

@[local simp] private theorem correctV93 : Correct 11 93 := by
  decide +kernel

@[local simp] private theorem correctV94 : Correct 11 94 := by
  decide +kernel

@[local simp] private theorem correctV95 : Correct 11 95 := by
  decide +kernel

@[local simp] private theorem correctV96 : Correct 11 96 := by
  decide +kernel

@[local simp] private theorem correctV97 : Correct 11 97 := by
  decide +kernel

@[local simp] private theorem correctV98 : Correct 11 98 := by
  decide +kernel

@[local simp] private theorem correctV99 : Correct 11 99 := by
  decide +kernel

@[local simp] private theorem correctV100 : Correct 11 100 := by
  decide +kernel

@[local simp] private theorem correctV101 : Correct 11 101 := by
  decide +kernel

@[local simp] private theorem correctV102 : Correct 11 102 := by
  decide +kernel

@[local simp] private theorem correctV103 : Correct 11 103 := by
  decide +kernel

@[local simp] private theorem correctV104 : Correct 11 104 := by
  decide +kernel

@[local simp] private theorem correctV105 : Correct 11 105 := by
  decide +kernel

@[local simp] private theorem correctV106 : Correct 11 106 := by
  decide +kernel

@[local simp] private theorem correctV107 : Correct 11 107 := by
  decide +kernel

@[local simp] private theorem correctV108 : Correct 11 108 := by
  decide +kernel

@[local simp] private theorem correctV109 : Correct 11 109 := by
  decide +kernel

@[local simp] private theorem correctV110 : Correct 11 110 := by
  decide +kernel

@[local simp] private theorem correctV111 : Correct 11 111 := by
  decide +kernel

@[local simp] private theorem correctV112 : Correct 11 112 := by
  decide +kernel

@[local simp] private theorem correctV113 : Correct 11 113 := by
  decide +kernel

@[local simp] private theorem correctV114 : Correct 11 114 := by
  decide +kernel

@[local simp] private theorem correctV115 : Correct 11 115 := by
  decide +kernel

@[local simp] private theorem correctV116 : Correct 11 116 := by
  decide +kernel

theorem correct :
    ∀ v ∈ List.range (128 - 11), Correct 11 v := by
  intro v hv
  simp only [List.mem_range] at hv
  interval_cases v <;> simp

end ProximityPrize.SubmissionLower.LocatorPhase6800CarrierCostCheck11
end PackedLocator_LocatorPhase6800CarrierCostCheck11
