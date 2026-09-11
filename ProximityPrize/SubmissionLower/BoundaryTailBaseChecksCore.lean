import ProximityPrize.SubmissionLower.BoundaryTailShape
import ProximityPrize.SubmissionLower.BoundaryTailStrictData
import ProximityPrize.SubmissionLower.BoundaryTailPhaseData

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecksCore
open RCN095 LocatorFactorAggregate LocatorPhase6800Oracle SecondJetRowIntervals
open BoundaryTailBaseOracle BoundaryTailShape
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
noncomputable section

theorem raw_affine (r v z : ℕ) (hr : 1 ≤ r) (hz : 3 ≤ z) :
    cost r v z = cost r v 3+(cost r v 4-cost r v 3)*(z-3) := by
  apply LocatorOrdinaryZConvex.affine_formula_from_three _ (cost_mono r v) _ z hz
  intro n hn
  by_cases h : 3 ≤ r ∧ 2 ≤ v
  · rw [cost_eq_high r v (n+1) h.1 h.2,cost_eq_high r v n h.1 h.2,
      cost_eq_high r v (n+2) h.1 h.2]
    exact high_affine r v n
  · rw [cost_eq_old r v (n+1) h,cost_eq_old r v n h,cost_eq_old r v (n+2) h]
    exact LocatorOrdinaryZConvex.rawCost_affine_step_from_two r v n hr hn

structure Carrier where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  deriving DecidableEq, Repr

def Carrier.Correct (c : Carrier) (r v : ℕ) : Prop :=
  c.c0=cost r v 0 ∧ c.c1=cost r v 1 ∧ c.c2=cost r v 2 ∧
  c.c3=cost r v 3 ∧ c.c4=cost r v 4
instance (c : Carrier) (r v : ℕ) : Decidable (c.Correct r v) := by
  unfold Carrier.Correct; infer_instance

def Carrier.eval (c : Carrier) (z : ℕ) : ℕ :=
  if z=0 then c.c0 else if z=1 then c.c1 else if z=2 then c.c2
  else c.c3+(c.c4-c.c3)*(z-3)

theorem Carrier.eval_correct (c : Carrier) (r v z : ℕ)
    (hr : 1 ≤ r) (hc : c.Correct r v) : c.eval z = cost r v z := by
  rcases hc with ⟨h0,h1,h2,h3,h4⟩
  unfold Carrier.eval
  split_ifs with hz0 hz1 hz2
  · simpa only [hz0] using h0
  · simpa only [hz1] using h1
  · simpa only [hz2] using h2
  · rw [h3,h4,raw_affine r v z hr (by omega)]

theorem Carrier.eval_affine (c : Carrier) (lo z : ℕ) (hl : 3 ≤ lo) (hz : lo ≤ z) :
    c.eval z = c.eval lo+(c.c4-c.c3)*(z-lo) := by
  simp only [Carrier.eval,if_neg (show z≠0 by omega),if_neg (show z≠1 by omega),
    if_neg (show z≠2 by omega),if_neg (show lo≠0 by omega),
    if_neg (show lo≠1 by omega),if_neg (show lo≠2 by omega)]
  rw [show z-3=(lo-3)+(z-lo) by omega,Nat.mul_add]
  omega

theorem affine_between (f g : ℕ → ℕ) (lo hi z m M : ℕ)
    (hf : ∀ zz, lo ≤ zz → zz ≤ hi → f zz=f lo+m*(zz-lo))
    (hg : ∀ zz, lo ≤ zz → zz ≤ hi → g zz=g lo+M*(zz-lo))
    (hz : lo ≤ z) (hzi : z ≤ hi) (h0 : f lo ≤ g lo) (h1 : f hi ≤ g hi) :
    f z ≤ g z := by
  have hlo : lo ≤ hi := hz.trans hzi
  rw [hf hi hlo le_rfl,hg hi hlo le_rfl] at h1
  rw [hf z hz hzi,hg z hz hzi]
  exact Lower80811.PhaseRows.affine_le_between _ _ _ _ _ _
    (Nat.sub_le_sub_right hzi lo) h0 h1

/-- Endpoint certificate for a piecewise affine row against one affine line. -/
def LineRuns (q : BaseRow) (f : ℕ → ℕ) (finish : ℕ) : ℕ → List ℕ → Prop
  | lo,[] => lo=finish
  | lo,stop::stops => lo < stop ∧ stop ≤ finish ∧ 3 ≤ lo ∧
      BaseCell q lo (stop-1) ∧ f lo ≤ q.evalAt lo ∧
      f (stop-1) ≤ q.evalAt (stop-1) ∧ LineRuns q f finish stop stops
instance (q : BaseRow) (f : ℕ → ℕ) (finish lo : ℕ) (stops : List ℕ) :
    Decidable (LineRuns q f finish lo stops) := by
  induction stops generalizing lo with
  | nil => simp only [LineRuns]; infer_instance
  | cons stop stops ih => simp only [LineRuns]; infer_instance

theorem LineRuns.sound (q : BaseRow) (f : ℕ → ℕ) (m finish lo : ℕ)
    (stops : List ℕ)
    (hf : ∀ a z, 3 ≤ a → a ≤ z → f z=f a+m*(z-a))
    (h : LineRuns q f finish lo stops) (z : ℕ) (hz : lo ≤ z) (hzi : z < finish) :
    f z ≤ q.evalAt z := by
  induction stops generalizing lo with
  | nil => simp only [LineRuns] at h; omega
  | cons stop stops ih =>
    rcases h with ⟨hstop,hfinish,hlo,hcell,h0,h1,hrest⟩
    by_cases hzs : z < stop
    · exact affine_between f q.evalAt lo (stop-1) z m (baseSlopeAt q lo)
        (fun zz hzz _ => hf lo zz hlo hzz)
        (fun zz hl hh => baseAt_affine q lo (stop-1) zz hcell hl hh)
        hz (by omega) h0 h1
    · exact ih stop hrest (by omega)

def stopsFor (q : BaseRow) (finish : ℕ) : List ℕ :=
  (q.segments.drop 1).map BaseSegment.start ++ [finish]

def StrictCheck (c : Carrier) (R V r v : ℕ) : Prop :=
  let q := BoundaryTailStrictData.lookup R V
  let zero := BoundaryTailStrictData.zero (R-r) (V-v)
  c.c0+zero ≤ q.z0 ∧ c.c1+zero ≤ q.z1 ∧ c.c2+zero ≤ q.z2 ∧
    LineRuns q (fun z => c.eval z+zero) (7502-R-V) 3 (stopsFor q (7502-R-V))
instance (c : Carrier) (R V r v : ℕ) : Decidable (StrictCheck c R V r v) := by
  unfold StrictCheck; infer_instance

theorem strictCheck_sound (c : Carrier) (R V r v z : ℕ)
    (hr : 1 ≤ r) (hc : c.Correct r v) (ht : R+V+z ≤ 7501)
    (h : StrictCheck c R V r v) :
    cost r v z+BoundaryTailStrictData.zero (R-r) (V-v) ≤
      BoundaryTailStrictData.cap (rawFlag R V z) := by
  rcases h with ⟨h0,h1,h2,hrest⟩
  rw [←c.eval_correct r v z hr hc]
  change _ ≤ (BoundaryTailStrictData.lookup R V).evalAt z
  by_cases hz0 : z=0
  · subst z; simpa [Carrier.eval,BaseRow.evalAt] using h0
  by_cases hz1 : z=1
  · subst z; simpa [Carrier.eval,BaseRow.evalAt] using h1
  by_cases hz2 : z=2
  · subst z; simpa [Carrier.eval,BaseRow.evalAt] using h2
  apply LineRuns.sound _ _ (c.c4-c.c3) _ _ _ _ hrest z (by omega) (by omega)
  intro a zz ha hzz
  rw [c.eval_affine a zz ha hzz]
  omega


open BoundaryTailRefinedCap

theorem proper_affine (r v lo z : ℕ) (hlo : start r v ≤ lo) (hz : lo ≤ z) :
    properLine r v z = properLine r v lo+properSlope r v*(z-lo) := by
  have h : z-start r v=(lo-start r v)+(z-lo) := by omega
  simp only [properLine,h]
  ring

theorem retained_affine (r v lo z : ℕ) (hlo : start r v ≤ lo) (hz : lo ≤ z) :
    retainedLine r v z = retainedLine r v lo+retainedSlope r v*(z-lo) := by
  have h : z-start r v=(lo-start r v)+(z-lo) := by omega
  simp only [retainedLine,h]
  ring

theorem profile_between (r v lo hi z : ℕ) (g : ℕ → ℕ) (slope : ℕ)
    (hstart : start r v ≤ lo) (hz : lo ≤ z) (hzi : z ≤ hi)
    (hg : ∀ zz, lo ≤ zz → zz ≤ hi → g zz=g lo+slope*(zz-lo))
    (h0 : profile r v lo ≤ g lo) (h1 : profile r v hi ≤ g hi) :
    profile r v z ≤ g z := by
  apply max_le
  · exact affine_between (properLine r v) g lo hi z (properSlope r v) slope
      (fun zz hl _ => proper_affine r v lo zz hstart hl) hg hz hzi
      ((le_max_left _ _).trans h0) ((le_max_left _ _).trans h1)
  · exact affine_between (retainedLine r v) g lo hi z (retainedSlope r v) slope
      (fun zz hl _ => retained_affine r v lo zz hstart hl) hg hz hzi
      ((le_max_right _ _).trans h0) ((le_max_right _ _).trans h1)

def choice (c : Carrier) (w r v z : ℕ) : ℕ :=
  if w=0 then c.eval z else profile r v z

def ChoiceActive (w r v z : ℕ) : Prop :=
  if w=0 then True else 3 ≤ r ∧ 2 ≤ v ∧ 2 ≤ z ∧ 2340 < r+v+z
instance (w r v z : ℕ) : Decidable (ChoiceActive w r v z) := by
  unfold ChoiceActive; infer_instance

theorem cap_le_choice (c : Carrier) (w r v lo z : ℕ)
    (hr : 1 ≤ r) (hc : c.Correct r v) (h : ChoiceActive w r v lo) (hz : lo ≤ z) :
    BoundaryTailBase.cap (rawFlag r v z) ≤ choice c w r v z := by
  by_cases hw : w=0
  · simp only [choice,if_pos hw,c.eval_correct r v z hr hc]
    exact BoundaryTailBase.cap_le_raw _
  · have ha : BoundaryTailBase.Active (rawFlag r v z) := by
      simp only [ChoiceActive,if_neg hw] at h
      unfold BoundaryTailBase.Active rawFlag
      dsimp
      omega
    simpa only [choice,if_neg hw,rawFlag] using BoundaryTailBase.cap_le_profile _ ha

theorem choice_between (c : Carrier) (w r v lo hi z : ℕ) (g : ℕ → ℕ) (M : ℕ)
    (hlo : 3 ≤ lo) (hactive : ChoiceActive w r v lo)
    (hz : lo ≤ z) (hzi : z ≤ hi)
    (hg : ∀ zz, lo ≤ zz → zz ≤ hi → g zz=g lo+M*(zz-lo))
    (h0 : choice c w r v lo ≤ g lo) (h1 : choice c w r v hi ≤ g hi) :
    choice c w r v z ≤ g z := by
  by_cases hw : w=0
  · simp only [choice,if_pos hw] at h0 h1 ⊢
    exact affine_between c.eval g lo hi z (c.c4-c.c3) M
      (fun zz hl _ => c.eval_affine lo zz hlo hl) hg hz hzi h0 h1
  · simp only [choice,if_neg hw] at h0 h1 ⊢
    apply profile_between r v lo hi z g M _ hz hzi hg h0 h1
    simp only [ChoiceActive,if_neg hw] at hactive
    unfold start
    omega

structure Run where
  stop : ℕ
  witness : ℕ
  deriving DecidableEq, Repr

def RunValid (c : Carrier) (r v : ℕ) (q : BaseRow) (start : ℕ) (run : Run) : Prop :=
  start < run.stop ∧ 3 ≤ start ∧ ChoiceActive run.witness r v start ∧
    BaseCell q start (run.stop-1) ∧
    BaseCell (BoundaryTailStrictData.lookup r v) start (run.stop-1) ∧
    choice c run.witness r v start ≤ q.evalAt start ∧
    choice c run.witness r v (run.stop-1) ≤ q.evalAt (run.stop-1) ∧
    (BoundaryTailStrictData.lookup r v).evalAt start ≤ q.evalAt start ∧
    (BoundaryTailStrictData.lookup r v).evalAt (run.stop-1) ≤ q.evalAt (run.stop-1)
instance (c : Carrier) (r v : ℕ) (q : BaseRow) (start : ℕ) (run : Run) :
    Decidable (RunValid c r v q start run) := by unfold RunValid; infer_instance

theorem RunValid.sound (c : Carrier) (r v : ℕ) (q : BaseRow) (start : ℕ) (run : Run)
    (hr : 1 ≤ r) (hc : c.Correct r v) (h : RunValid c r v q start run) (z : ℕ) (hz : start ≤ z) (hzi : z < run.stop) :
    max (BoundaryTailBase.cap (rawFlag r v z)) (BoundaryTailStrictData.cap (rawFlag r v z)) ≤ q.evalAt z := by
  rcases h with ⟨hstop,hs3,hactive,hcell,hscell,hc0,hc1,hs0,hs1⟩
  apply max_le
  · apply (cap_le_choice c run.witness r v start z hr hc hactive hz).trans
    exact choice_between c run.witness r v start (run.stop-1) z q.evalAt
      (baseSlopeAt q start) hs3 hactive hz (by omega)
      (fun zz hlo hhi => baseAt_affine q start (run.stop-1) zz hcell hlo hhi) hc0 hc1
  · exact affine_between (BoundaryTailStrictData.lookup r v).evalAt q.evalAt start (run.stop-1) z
      (baseSlopeAt (BoundaryTailStrictData.lookup r v) start) (baseSlopeAt q start)
      (fun zz hlo hhi => baseAt_affine _ start (run.stop-1) zz hscell hlo hhi)
      (fun zz hlo hhi => baseAt_affine q start (run.stop-1) zz hcell hlo hhi)
      hz (by omega) hs0 hs1

def RunsValid (c : Carrier) (r v : ℕ) (q : BaseRow) (finish : ℕ) : ℕ → List Run → Prop
  | start,[] => start=finish
  | start,run::runs => run.stop ≤ finish ∧ RunValid c r v q start run ∧ RunsValid c r v q finish run.stop runs
instance (c : Carrier) (r v : ℕ) (q : BaseRow) (finish start : ℕ) (runs : List Run) :
    Decidable (RunsValid c r v q finish start runs) := by
  induction runs generalizing start with
  | nil => simp only [RunsValid]; infer_instance
  | cons run runs ih => simp only [RunsValid]; infer_instance

theorem RunsValid.sound (c : Carrier) (r v : ℕ) (q : BaseRow) (finish start : ℕ) (runs : List Run)
    (hr : 1 ≤ r) (hc : c.Correct r v) (h : RunsValid c r v q finish start runs) (z : ℕ) (hlo : start ≤ z) (hhi : z < finish) :
    max (BoundaryTailBase.cap (rawFlag r v z)) (BoundaryTailStrictData.cap (rawFlag r v z)) ≤ q.evalAt z := by
  induction runs generalizing start with
  | nil => simp only [RunsValid] at h; omega
  | cons run runs ih =>
    simp only [RunsValid] at h
    by_cases hz : z < run.stop
    · exact RunValid.sound c r v q start run hr hc h.2.1 z hlo hz
    · exact ih run.stop h.2.2 (by omega)

def RowValid (c : Carrier) (r v : ℕ) (q : BaseRow) (runs : List Run) : Prop :=
  max (choice c 0 r v 0) (BoundaryTailStrictData.cap (rawFlag r v 0)) ≤ q.z0 ∧
  max (choice c 0 r v 1) (BoundaryTailStrictData.cap (rawFlag r v 1)) ≤ q.z1 ∧
  max (choice c 0 r v 2) (BoundaryTailStrictData.cap (rawFlag r v 2)) ≤ q.z2 ∧
  RunsValid c r v q (7502-r-v) 3 runs
instance (c : Carrier) (r v : ℕ) (q : BaseRow) (runs : List Run) : Decidable (RowValid c r v q runs) := by
  unfold RowValid
  infer_instance

theorem RowValid.sound (c : Carrier) (r v : ℕ) (q : BaseRow) (runs : List Run)
    (hr : 1 ≤ r) (hc : c.Correct r v) (h : RowValid c r v q runs) (z : ℕ) (hz : r+v+z ≤ 7501) :
    max (BoundaryTailBase.cap (rawFlag r v z)) (BoundaryTailStrictData.cap (rawFlag r v z)) ≤ q.evalAt z := by
  rcases h with ⟨h0,h1,h2,hrest⟩
  have hb := max_le_max_right (BoundaryTailStrictData.cap (rawFlag r v z))
    (cap_le_choice c 0 r v z z hr hc trivial le_rfl)
  by_cases hz0 : z=0
  · subst z
    exact hb.trans (by simpa only [BaseRow.evalAt,if_pos] using h0)
  by_cases hz1 : z=1
  · subst z
    exact hb.trans (by simpa only [BaseRow.evalAt,if_neg Nat.one_ne_zero,if_pos] using h1)
  by_cases hz2 : z=2
  · subst z
    exact hb.trans (by simpa only [BaseRow.evalAt,if_neg (by decide : 2≠0),if_neg (by decide : 2≠1),if_pos] using h2)
  exact RunsValid.sound c r v q (7502-r-v) 3 runs hr hc hrest z (by omega) (by omega)


/-- Finite Bellman checks, using cached raw costs only. -/
def ZeroAt (carriers : ℕ → ℕ → Carrier) (R V : ℕ) : Prop :=
  ∀ r ∈ List.range (R+1), ∀ v ∈ List.range (V+1),
    1 ≤ r → (r < R ∨ v=V) →
      (carriers r v).c0+BoundaryTailStrictData.zero (R-r) (V-v) ≤
        BoundaryTailStrictData.zero R V
instance (carriers : ℕ → ℕ → Carrier) (R V : ℕ) : Decidable (ZeroAt carriers R V) := by
  unfold ZeroAt; infer_instance

def StrictAt (carriers : ℕ → ℕ → Carrier) (R V : ℕ) : Prop :=
  ∀ r ∈ List.range R, ∀ v ∈ List.range (V+1),
    1 ≤ r → StrictCheck (carriers r v) R V r v
instance (carriers : ℕ → ℕ → Carrier) (R V : ℕ) : Decidable (StrictAt carriers R V) := by
  unfold StrictAt; infer_instance

theorem receipt_of_checks (carriers : ℕ → ℕ → Carrier)
    (runs : ℕ → ℕ → List Run)
    (hcorrect : ∀ r v, 1 ≤ r → r ≤ 31 → r+v ≤ 142 → (carriers r v).Correct r v)
    (hzero : ∀ R V, 1 ≤ R → R ≤ 31 → R+V ≤ 142 → ZeroAt carriers R V)
    (hstrict : ∀ R V, 1 ≤ R → R ≤ 31 → R+V ≤ 142 → StrictAt carriers R V)
    (hbase : ∀ R V, 1 ≤ R → R ≤ 31 → R+V ≤ 142 →
      RowValid (carriers R V) R V (BoundaryTailBaseData.lookup R V) (runs R V)) :
    BoundaryTailBaseOracle.Receipt BoundaryTailStrictData.zero BoundaryTailStrictData.cap
      BoundaryTailBaseData.cap := by
  have hsound (p : FlagDegree) (hp : 1 ≤ p.all) (hr : p.all ≤ 31)
      (hy : middle p ≤ 142) (ht : total p ≤ 7501) :
      max (BoundaryTailBase.cap p) (BoundaryTailStrictData.cap p) ≤ BoundaryTailBaseData.cap p := by
    have hrv : p.all+p.yz ≤ 142 := by unfold middle at hy; omega
    have he : rawFlag p.all p.yz p.zOnly = p := by cases p; rfl
    have h := RowValid.sound (carriers p.all p.yz) p.all p.yz
      (BoundaryTailBaseData.lookup p.all p.yz) (runs p.all p.yz)
      hp (hcorrect _ _ hp hr hrv) (hbase _ _ hp hr hrv) p.zOnly
      (by unfold total at ht; omega)
    simpa only [he,BoundaryTailBaseData.cap] using h
  refine ⟨BoundaryTailShape.shape,?_,?_,?_,?_⟩
  · intro R V r v hr hrR hvV hR hRV hfits
    have hc := (hcorrect r v hr (by omega) (by omega)).1
    have h := hzero R V (by omega) hR hRV r (List.mem_range.mpr (by omega))
      v (List.mem_range.mpr (by omega)) hr hfits
    simpa only [hc] using h
  · intro R V r v z hr hrR hvV hR hRV ht
    exact strictCheck_sound (carriers r v) R V r v z hr
      (hcorrect r v hr (by omega) (by omega)) ht
      (hstrict R V (by omega) hR hRV r (List.mem_range.mpr hrR)
        v (List.mem_range.mpr (by omega)) hr)
  · intro p hp hr hy ht
    have hcap := (le_max_left _ _).trans (hsound p hp hr hy ht)
    by_cases hraw : BoundaryTailOrdinary.rawCost p ≤ BoundaryTailBaseData.cap p
    · exact Or.inl hraw
    · right
      by_cases ha : BoundaryTailBase.Active p
      · refine ⟨ha,?_⟩
        simp only [BoundaryTailBase.cap,if_pos ha] at hcap
        omega
      · simp only [BoundaryTailBase.cap,if_neg ha] at hcap
        exact False.elim (hraw hcap)
  · intro p hp hr hy ht
    exact (le_max_right _ _).trans (hsound p hp hr hy ht)

end
end ProximityPrize.SubmissionLower.BoundaryTailBaseChecksCore
