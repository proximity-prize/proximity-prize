import ProximityPrize.SubmissionLower.Part.G096


section Compact_PhaseRows80791
/-! Scalar-prefix interval verification for the proposed twelve-phase certificate.
The source data is untrusted until the predicates below are proved. -/
set_option Elab.async false
namespace ProximityPrize.SubmissionLower.Lower80791.PhaseRows
open RCN095 LocatorFactorAggregate LocatorArbitraryPowerAvoidance
open LocatorPhase6800Oracle (Potential BaseRow BaseSegment evalBaseSegments rawFlag rawFlag_total rawFlag_middle rawFlag_all)
open Lower80791.Oracle
open LocatorPhase6800Audit (powerBandBudget_mono_fuel)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem routeable_raw_mono_z
    (s : SourceNumbers) {r v z₁ z₂ : ℕ}
    (hz : z₁ ≤ z₂) (hcap : r + v + z₂ ≤ s.totalCap)
    (hroute : s.Routeable (rawFlag r v z₁)) :
    s.Routeable (rawFlag r v z₂) := by
  rcases hroute with ⟨hr, ht, hy, hs, hband⟩
  have hr' : 1 ≤ r := by simpa only [rawFlag_all] using hr
  have htotal : r + v + z₁ ≤ r + v + z₂ := by omega
  have hpos : 0 < r + v + z₁ := by omega
  have hdiv : s.totalCap / (r + v + z₂) ≤
      s.totalCap / (r + v + z₁) :=
    Nat.div_le_div_left htotal hpos
  have hfuel : s.fuel (rawFlag r v z₂) ≤
      s.fuel (rawFlag r v z₁) := by
    unfold SourceNumbers.fuel
    simp only [rawFlag_total, rawFlag_middle, rawFlag_all]
    exact min_le_min hdiv (le_refl _)
  have hbox : s.totalCap - (r + v + z₂) ≤
      s.totalCap - (r + v + z₁) := Nat.sub_le_sub_left htotal _
  have hsameFuel :
      powerBandBudget 50283 (r + v + z₂) (r + v) r
          (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
        powerBandBudget 50283 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) := by
    exact powerBandBudget_mono 50283
      (r + v + z₂) (r + v) r
      (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
      (s.slopeCap - r)
      (r + v + z₁) (r + v) r
      (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
      (s.slopeCap - r) (s.fuel (rawFlag r v z₂))
      hbox (le_refl _) (le_refl _) htotal (le_refl _) (le_refl _)
  have hmoreFuel :
      powerBandBudget 50283 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
        powerBandBudget 50283 (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
          (s.slopeCap - r) (s.fuel (rawFlag r v z₁)) :=
    powerBandBudget_mono_fuel 50283 (r + v + z₁) (r + v) r
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
          powerBandBudgetThin 131071 (s.contactCap (rawFlag r v z₂)) 50283
              (contactDec (rawFlag r v z₂)) (r + v + z₂) (r + v) r
              (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
            powerBandBudgetThin 131071 (s.contactCap (rawFlag r v z₁)) 50283
              (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
              (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) := by
        have hcap : s.contactCap (rawFlag r v z₂) = s.contactCap (rawFlag r v z₁) := by
          simp only [SourceNumbers.contactCap, contactDec, rawFlag_middle, rawFlag_all]
        have hdec : contactDec (rawFlag r v z₂) = contactDec (rawFlag r v z₁) := by
          simp only [contactDec, rawFlag_middle, rawFlag_all]
        rw [hcap, hdec]
        exact powerBandBudgetThin_mono 131071 50283 (s.fuel (rawFlag r v z₂))
          (s.contactCap (rawFlag r v z₁)) (contactDec (rawFlag r v z₁))
          (r + v + z₂) (r + v) r
          (s.totalCap - (r + v + z₂)) (s.middleCap - (r + v)) (s.slopeCap - r)
          (s.contactCap (rawFlag r v z₁)) (contactDec (rawFlag r v z₁))
          (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v)) (s.slopeCap - r)
          le_rfl le_rfl hbox le_rfl le_rfl htotal le_rfl le_rfl
      have hmoreFuelT :
          powerBandBudgetThin 131071 (s.contactCap (rawFlag r v z₁)) 50283
              (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
              (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₂)) ≤
            powerBandBudgetThin 131071 (s.contactCap (rawFlag r v z₁)) 50283
              (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
              (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v))
              (s.slopeCap - r) (s.fuel (rawFlag r v z₁)) :=
        powerBandBudgetThin_mono_fuel 131071 (s.contactCap (rawFlag r v z₁)) 50283
          (contactDec (rawFlag r v z₁)) (r + v + z₁) (r + v) r
          (s.totalCap - (r + v + z₁)) (s.middleCap - (r + v)) (s.slopeCap - r) hfuel
      unfold SourceNumbers.bandThin at hthin ⊢
      simp only [rawFlag_total, rawFlag_middle, rawFlag_all] at hthin ⊢
      exact (hsameFuelT.trans hmoreFuelT).trans_lt hthin


def phasePotential : ℕ → Potential
  | 0 => Lower80791.SourceSound.Phase00.potential
  | 1 => Lower80791.SourceSound.Phase01.potential
  | 2 => Lower80791.SourceSound.Phase02.potential
  | 3 => Lower80791.SourceSound.Phase03.potential
  | 4 => Lower80791.SourceSound.Phase04.potential
  | _ => Lower80791.SourceSound.Phase05.potential

def thresholdAt (q : Array ℕ) (j : ℕ) : ℕ := (q[j]?).getD 6918
def cachedPrefixAt (q : Array ℕ) (j : ℕ) : ℕ := (q[j]?).getD 0
structure PhaseRowContext where
  R : ℕ
  V : ℕ
  base : BaseRow
  threshold : Array ℕ
  here : Array ℕ
  parent : Array ℕ

def baseAt (c : PhaseRowContext) (z : ℕ) : ℕ := c.base.evalAt z

def parentCharge (c : PhaseRowContext) (phase z : ℕ) : ℕ :=
  (phasePotential phase).eval (rawFlag c.R c.V z) + cachedPrefixAt c.parent phase

def hereCharge (c : PhaseRowContext) (phase z : ℕ) : ℕ :=
  (phasePotential phase).eval (rawFlag c.R c.V z) + cachedPrefixAt c.here phase

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

open SecondJetRowIntervals

theorem potential_raw_affine (q : Potential) (R V lo z : ℕ) (hlo : lo ≤ z) :
    q.eval (rawFlag R V z) =
      q.eval (rawFlag R V lo) + q.totalCoeff * (z - lo) := by
  have hz : z = lo + (z - lo) := by omega
  rw [hz]
  simp only [Potential.eval, rawFlag_total, rawFlag_middle, rawFlag_all]
  have hsub : lo + (z - lo) - lo = z - lo := by omega
  rw [hsub]
  ring


def SourceCell (c : PhaseRowContext) : ℕ → ℕ → ℕ → Prop
  | 0, lo, hi => BaseCell c.base lo hi
  | _+1, _, _ => True
instance (c : PhaseRowContext) (w lo hi : ℕ) : Decidable (SourceCell c w lo hi) := by
  cases w <;> simp only [SourceCell] <;> infer_instance

def sourceSlope (c : PhaseRowContext) : ℕ → ℕ → ℕ
  | 0, lo => baseSlopeAt c.base lo
  | j+1, _ => (phasePotential j).totalCoeff

theorem parentCharge_affine (c : PhaseRowContext) (phase lo z : ℕ) (hz : lo ≤ z) :
    parentCharge c phase z = parentCharge c phase lo + (phasePotential phase).totalCoeff*(z-lo) := by
  unfold parentCharge
  rw [potential_raw_affine _ _ _ lo z hz]
  omega

theorem hereCharge_affine (c : PhaseRowContext) (phase lo hi z : ℕ)
    (_hp : phase < 6) (hlo : lo ≤ z) (_hhi : z ≤ hi) :
    hereCharge c phase z = hereCharge c phase lo + (phasePotential phase).totalCoeff*(z-lo) := by
  unfold hereCharge
  rw [potential_raw_affine _ _ _ lo z hlo]
  omega

theorem sourceLine_affine (c : PhaseRowContext) (w lo hi z : ℕ)
    (_hw : w ≤ 6) (hc : SourceCell c w lo hi) (hlo : lo ≤ z) (hhi : z ≤ hi) :
    sourceLine c w z = sourceLine c w lo + sourceSlope c w lo*(z-lo) := by
  cases w with
  | zero => exact baseAt_affine c.base lo hi z hc hlo hhi
  | succ j => exact parentCharge_affine c j lo z hlo

theorem affine_le_between (a A m M d finish : ℕ) (hd : d ≤ finish)
    (hstart : a ≤ A) (hend : a+m*finish ≤ A+M*finish) : a+m*d ≤ A+M*d := by
  by_cases hm : m ≤ M
  · exact Nat.add_le_add hstart (Nat.mul_le_mul_right d hm)
  · have hMm : M ≤ m := (Nat.lt_of_not_ge hm).le
    have hdecomp : M+(m-M)=m := Nat.add_sub_of_le hMm
    have hdeltaFinish : a+(m-M)*finish ≤ A := by
      rw [← hdecomp, Nat.add_mul] at hend
      omega
    have hdelta := Nat.mul_le_mul_left (m-M) hd
    rw [← hdecomp, Nat.add_mul]
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
    sourceLine c run.witness start ≤ hereCharge c phase start ∧
    sourceLine c run.witness hi ≤ hereCharge c phase hi

instance (c : PhaseRowContext) (phase start : ℕ) (run : PhaseRun) :
    Decidable (RunValid c phase start run) := by
  unfold RunValid
  infer_instance

theorem RunValid.sound (c : PhaseRowContext) (phase start : ℕ) (run : PhaseRun)
    (hp : phase < 6) (h : RunValid c phase start run)
    (z : ℕ) (hlo : start ≤ z) (hhi : z < run.stop) :
    capBefore c phase z ≤ hereCharge c phase z := by
  change start < run.stop ∧ run.witness ≤ phase ∧
    SourceActive c run.witness start ∧
    SourceCell c run.witness start (run.stop - 1) ∧
    sourceLine c run.witness start ≤ hereCharge c phase start ∧
    sourceLine c run.witness (run.stop - 1) ≤
      hereCharge c phase (run.stop - 1) at h
  rcases h with ⟨hstart, hw, hactive, hsource, hleft, hright⟩
  let hi := run.stop - 1
  have hzhi : z ≤ hi := by dsimp only [hi]; omega
  have hsthi : start ≤ hi := by dsimp only [hi]; omega
  have hs := sourceLine_affine c run.witness start hi z (by omega)
    hsource hlo hzhi
  have ht := hereCharge_affine c phase start hi z hp hlo hzhi
  have hsEnd := sourceLine_affine c run.witness start hi hi (by omega)
    hsource hsthi le_rfl
  have htEnd := hereCharge_affine c phase start hi hi hp
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
    (runs : List PhaseRun) (hp : phase < 6)
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
  min (thresholdAt c.threshold phase) (6918 - (c.R + c.V))

def RowRunsValid (c : PhaseRowContext) (runs : Array (List PhaseRun)) : Prop :=
  ∀ j ∈ List.range 6, RunsValid c j (phaseFinish c j) 0 ((runs[j]?).getD [])

instance (c : PhaseRowContext) (runs : Array (List PhaseRun)) :
    Decidable (RowRunsValid c runs) := by
  unfold RowRunsValid
  infer_instance

theorem phaseTerminal_of_runs (c : PhaseRowContext) (phase : ℕ)
    (runs : List PhaseRun) (hp : phase < 6)
    (h : RunsValid c phase (phaseFinish c phase) 0 runs)
    (z : ℕ) (hz : z < 6918 - (c.R + c.V)) :
    thresholdAt c.threshold phase ≤ z ∨
      capBefore c phase z ≤ hereCharge c phase z := by
  by_cases ht : thresholdAt c.threshold phase ≤ z
  · exact Or.inl ht
  · apply Or.inr
    apply RunsValid.sound c phase (phaseFinish c phase) 0 runs hp h z
    · omega
    · unfold phaseFinish
      exact lt_min (Nat.lt_of_not_ge ht) hz


end ProximityPrize.SubmissionLower.Lower80791.PhaseRows

end Compact_PhaseRows80791
