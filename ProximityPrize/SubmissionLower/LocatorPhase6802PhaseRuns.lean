import ProximityPrize.SubmissionLower.LocatorPhase6802ConcreteProof

section PackedLocator_LocatorPhase6802PhaseRuns

/-!
Sparse checker for the phase-state grid.  One `PhaseRun` covers
a half-open interval on which one already-active source line and the current
target charge are affine.  Two endpoint comparisons replace a point-by-point
check of that interval.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase6802PhaseRuns

open RCN095 LocatorFactorAggregate
open LocatorPhase6802Oracle LocatorPhaseBaseC2
open LocatorPhase6802BaseDirectData
open LocatorPhase6802Concrete

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
  min (thresholdAt c.threshold phase) (6404 - (c.R + c.V))

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
    (z : ℕ) (hz : z < 6404 - (c.R + c.V)) :
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
      5791742386 * (6403 - (R + V + z)) +
      5785309650353 *
        min (6403 - (R + V + z)) (149 - (R + V)) +
      23029633986507 *
        min (6403 - (R + V + z))
          (min (149 - (R + V)) (32 - R)) := by
  simp [initialAComplement, initialAPotential, Potential.eval, rawFlag,
    total, middle, Nat.min_def]
  split_ifs <;> omega

def sLine (R V pref z : ℕ) : ℕ :=
  split390Potential.eval (rawFlag R V z) + pref

theorem sLine_joint_le_of_keypoints
    (R V pref lo hi bound : ℕ) (hlohi : lo ≤ hi)
    (hlo : sLine R V pref lo + initialAComplement (rawFlag R V lo) ≤ bound)
    (hhi : sLine R V pref hi + initialAComplement (rawFlag R V hi) ≤ bound)
    (h6254 :
      sLine R V pref (max lo (min hi 6254)) +
        initialAComplement (rawFlag R V (max lo (min hi 6254))) ≤ bound)
    (h6371 :
      sLine R V pref (max lo (min hi (6371 - V))) +
        initialAComplement (rawFlag R V (max lo (min hi (6371 - V)))) ≤ bound) :
    ∀ z, lo ≤ z → z ≤ hi →
      sLine R V pref z + initialAComplement (rawFlag R V z) ≤ bound := by
  intro z hlz hzh
  simp only [sLine, split390Potential, split500Potential, Potential.eval,
    rawFlag_total, rawFlag_middle, rawFlag_all, complement_raw_formula]
    at hhi h6254 ⊢
  simp only [Nat.min_def, Nat.max_def] at hhi h6254 ⊢
  split_ifs at hhi h6254 ⊢ <;> omega

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
    let k₁ := max lo (min hi 6254)
    let k₂ := max lo (min hi (6371 - c.V))
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
    have hk₁lo : lo ≤ max lo (min hi 6254) := le_max_left _ _
    have hk₁hi : max lo (min hi 6254) ≤ hi := by omega
    have hk₁ : sLine c.R c.V pref (max lo (min hi 6254)) +
        initialAComplement (rawFlag c.R c.V (max lo (min hi 6254))) ≤
          certifiedJointMaximum := by
      rw [← hsLine _ hk₁lo hk₁hi]
      exact h.2.2.2.2.2.1
    have hk₂lo : lo ≤ max lo (min hi (6371 - c.V)) := le_max_left _ _
    have hk₂hi : max lo (min hi (6371 - c.V)) ≤ hi := by omega
    have hk₂ : sLine c.R c.V pref (max lo (min hi (6371 - c.V))) +
        initialAComplement (rawFlag c.R c.V
          (max lo (min hi (6371 - c.V)))) ≤ certifiedJointMaximum := by
      rw [← hsLine _ hk₂lo hk₂hi]
      exact h.2.2.2.2.2.2
    have hbound := (sLine_joint_le_of_keypoints c.R c.V pref lo hi
      certifiedJointMaximum h.1 hlo' hhi' hk₁ hk₂) z hlo hhi
    rw [hsLine z hlo hhi]
    exact hbound

def FinalBoundsValid (c : PhaseRowContext) : Prop :=
  let maxZ := 6403 - (c.R + c.V)
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
    (hz : z < 6404 - (c.R + c.V)) :
    capBefore c 4 z ≤ certifiedNarrowMaximum ∧
      capBefore c 4 z + initialAComplement (rawFlag c.R c.V z) ≤
        certifiedJointMaximum := by
  let threshold := thresholdAt c.threshold 3
  let maxZ := 6403 - (c.R + c.V)
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
  ∀ z, z < 6404 - (c.R + c.V) →
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

end ProximityPrize.SubmissionLower.LocatorPhase6802PhaseRuns
end PackedLocator_LocatorPhase6802PhaseRuns
