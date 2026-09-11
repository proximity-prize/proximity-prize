import ProximityPrize.SubmissionLower.BoundaryTailAssembly
import ProximityPrize.SubmissionLower.BoundaryTailThresholdChecked

namespace ProximityPrize.SubmissionLower.Lower80801.LedgerAudit
open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (Potential rawFlag)
open Lower80801.Initial Lower80801.PhaseRows Lower80801.PhaseData AsymmetricChainPolynomial80801
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def bound : ℕ := 253080253061200723

def ledger (c : PhaseRowContext) (z : ℕ) : ℕ :=
  capBefore c 6 z + initialAComplement (rawFlag c.R c.V z) +
    c.R * unit (c.R+c.V) (c.R+c.V+z) c.R +
    (33-c.R) * unit (153-(c.R+c.V)) (21378-(c.R+c.V+z)) (33-c.R) +
    14000000000000 + 860903991184427

def complementUpper (R V mode z : ℕ) : ℤ :=
  let t : ℤ := 7199-R-V-z
  let y : ℕ := 153-(R+V)
  let r : ℕ := min y (33-R)
  if mode = 0 then 6224763708*t+7930822886661*y+37324898468619*r
  else if mode = 1 then (6224763708+7930822886661)*t+37324898468619*r
  else (6224763708+7930822886661+37324898468619)*t

def complementSlope (mode : ℕ) : ℤ :=
  if mode = 0 then -6224763708
  else if mode = 1 then -(6224763708+7930822886661)
  else -(6224763708+7930822886661+37324898468619)

theorem complement_formula (R V z : ℕ) :
    initialAComplement (rawFlag R V z) =
      6224763708*(7199-(R+V+z)) +
      7930822886661*min (7199-(R+V+z)) (153-(R+V)) +
      37324898468619*min (7199-(R+V+z)) (min (153-(R+V)) (33-R)) := by
  simp [initialAComplement, initialAPotential, Potential.eval, rawFlag,
    total, middle, Nat.min_def]
  split_ifs <;> omega

theorem complement_le_upper (R V mode z : ℕ) (ht : R+V+z ≤ 7199) :
    (initialAComplement (rawFlag R V z) : ℤ) ≤ complementUpper R V mode z := by
  rw [complement_formula]
  have hmy := Nat.min_le_right (7199-(R+V+z)) (153-(R+V))
  have hmt := Nat.min_le_left (7199-(R+V+z)) (153-(R+V))
  have hmr := Nat.min_le_right (7199-(R+V+z)) (min (153-(R+V)) (33-R))
  have hmrt := Nat.min_le_left (7199-(R+V+z)) (min (153-(R+V)) (33-R))
  have hti : ((7199-(R+V+z) : ℕ) : ℤ) = 7199-R-V-z := by omega
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [hti]
  unfold complementUpper
  split_ifs <;> dsimp only <;> omega

def branch (c : PhaseRowContext) (w mode : ℕ) (u v : Bool) (z : ℕ) : ℤ :=
  (sourceLine c w z : ℤ) + complementUpper c.R c.V mode z +
  (c.R : ℤ)*(if u then
    (unitSlope (c.R+c.V) c.R : ℤ)*(c.R+c.V+z)+(unitConstant (c.R+c.V) c.R : ℤ)
    else 7000000000000) +
  ((33-c.R : ℕ) : ℤ)*(if v then
    (unitSlope (153-(c.R+c.V)) (33-c.R) : ℤ)*(21378-c.R-c.V-z)+
      (unitConstant (153-(c.R+c.V)) (33-c.R) : ℤ)
    else 7000000000000) + 14000000000000+860903991184427

def branchSlope (c : PhaseRowContext) (w mode lo : ℕ) (u v : Bool) : ℤ :=
  (sourceSlope c w lo : ℤ)+complementSlope mode+
  (c.R : ℤ)*(if u then (unitSlope (c.R+c.V) c.R : ℤ) else 0)-
  ((33-c.R : ℕ) : ℤ)*(if v then (unitSlope (153-(c.R+c.V)) (33-c.R) : ℤ) else 0)

theorem branch_affine (c : PhaseRowContext) (w mode lo hi z : ℕ) (u v : Bool)
    (hw : w ≤ 6)
    (hc : SourceCell c w lo hi) (hz : lo ≤ z) (hhi : z ≤ hi) :
    branch c w mode u v z = branch c w mode u v lo +
      branchSlope c w mode lo u v * ((z : ℤ)-lo) := by
  have hs := sourceLine_affine c w lo hi z hw hc hz hhi
  have hsi : (sourceLine c w z : ℤ) = (sourceLine c w lo : ℤ)+
      (sourceSlope c w lo : ℤ)*((z : ℤ)-lo) := by
    rw [hs]
    push_cast [Nat.cast_sub hz]
    rfl
  unfold branch branchSlope complementUpper complementSlope
  rw [hsi]
  cases u <;> cases v <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;> ring

theorem branch_between (c : PhaseRowContext) (w mode lo hi z : ℕ) (u v : Bool)
    (hw : w ≤ 6)
    (hc : SourceCell c w lo hi) (hz : lo ≤ z) (hhi : z ≤ hi)
    (hloB : branch c w mode u v lo ≤ bound)
    (hhiB : branch c w mode u v hi ≤ bound) :
    branch c w mode u v z ≤ bound := by
  have h1 := branch_affine c w mode lo hi z u v hw hc hz hhi
  have h2 := branch_affine c w mode lo hi hi u v hw hc (hz.trans hhi) le_rfl
  rcases le_total 0 (branchSlope c w mode lo u v) with hs | hs
  · have hm := mul_le_mul_of_nonneg_left
      (show (z : ℤ)-lo ≤ (hi : ℤ)-lo by omega) hs
    nlinarith
  · have hm := mul_nonpos_of_nonpos_of_nonneg hs (show 0 ≤ (z : ℤ)-lo by omega)
    nlinarith

theorem ledger_le_of_branches (c : PhaseRowContext) (w mode z : ℕ)
    (hw : w ≤ 6) (ha : SourceActive c w z) (ht : c.R+c.V+z ≤ 7199)
    (hb : ∀ u v : Bool, branch c w mode u v z ≤ bound) : ledger c z ≤ bound := by
  have hs := capBefore_le_sourceLine c 6 w z hw ha
  have hc := complement_le_upper c.R c.V mode z ht
  have hti : ((21378-(c.R+c.V+z) : ℕ) : ℤ) = 21378-c.R-c.V-z := by omega
  unfold ledger unit
  by_cases hu : 7000000000000 ≤ unitSlope (c.R+c.V) c.R*(c.R+c.V+z)+unitConstant (c.R+c.V) c.R
  · rw [max_eq_right hu]
    by_cases hv : 7000000000000 ≤ unitSlope (153-(c.R+c.V)) (33-c.R)*(21378-(c.R+c.V+z))+unitConstant (153-(c.R+c.V)) (33-c.R)
    · rw [max_eq_right hv]
      have hh := hb true true
      simp only [branch, Bool.true_eq, ↓reduceIte] at hh
      norm_cast at hs
      have hh' : (capBefore c 6 z : ℤ)+(initialAComplement (rawFlag c.R c.V z) : ℤ)+
          (c.R : ℤ)*((unitSlope (c.R+c.V) c.R : ℤ)*(c.R+c.V+z)+unitConstant (c.R+c.V) c.R)+
          ((33-c.R : ℕ) : ℤ)*((unitSlope (153-(c.R+c.V)) (33-c.R) : ℤ)*(21378-c.R-c.V-z)+unitConstant (153-(c.R+c.V)) (33-c.R))+
          14000000000000+860903991184427 ≤ bound := by omega
      rw [← hti] at hh'
      exact_mod_cast hh'
    · rw [max_eq_left (Nat.le_of_not_ge hv)]
      have hh := hb true false
      simp only [branch, Bool.true_eq, Bool.false_eq_true, ↓reduceIte] at hh
      have hsi : (capBefore c 6 z : ℤ) ≤ sourceLine c w z := by exact_mod_cast hs
      have hi : (capBefore c 6 z : ℤ)+(initialAComplement (rawFlag c.R c.V z) : ℤ)+
          (c.R : ℤ)*((unitSlope (c.R+c.V) c.R : ℤ)*(c.R+c.V+z)+unitConstant (c.R+c.V) c.R)+
          ((33-c.R : ℕ) : ℤ)*7000000000000+14000000000000+860903991184427 ≤ bound := by omega
      exact_mod_cast hi
  · rw [max_eq_left (Nat.le_of_not_ge hu)]
    by_cases hv : 7000000000000 ≤ unitSlope (153-(c.R+c.V)) (33-c.R)*(21378-(c.R+c.V+z))+unitConstant (153-(c.R+c.V)) (33-c.R)
    · rw [max_eq_right hv]
      have hh := hb false true
      simp only [branch, Bool.true_eq, Bool.false_eq_true, ↓reduceIte] at hh
      have hsi : (capBefore c 6 z : ℤ) ≤ sourceLine c w z := by exact_mod_cast hs
      have hi : (capBefore c 6 z : ℤ)+(initialAComplement (rawFlag c.R c.V z) : ℤ)+
          (c.R : ℤ)*7000000000000+
          ((33-c.R : ℕ) : ℤ)*((unitSlope (153-(c.R+c.V)) (33-c.R) : ℤ)*(21378-c.R-c.V-z)+unitConstant (153-(c.R+c.V)) (33-c.R))+
          14000000000000+860903991184427 ≤ bound := by omega
      rw [← hti] at hi
      exact_mod_cast hi
    · rw [max_eq_left (Nat.le_of_not_ge hv)]
      have hh := hb false false
      simp only [branch, Bool.false_eq_true, ↓reduceIte] at hh
      have hsi : (capBefore c 6 z : ℤ) ≤ sourceLine c w z := by exact_mod_cast hs
      have hi : (capBefore c 6 z : ℤ)+(initialAComplement (rawFlag c.R c.V z) : ℤ)+
          (c.R : ℤ)*7000000000000+((33-c.R : ℕ) : ℤ)*7000000000000+
          14000000000000+860903991184427 ≤ bound := by omega
      exact_mod_cast hi


structure LedgerRun where
  stop : ℕ
  witness : ℕ
  mode : ℕ
  deriving DecidableEq, Repr

theorem bool_pair_bound_iff (a b d t e M : ℤ) (r s : ℕ) :
    (∀ u v : Bool,
      a + (r : ℤ) * (if u then b else t) +
        (s : ℤ) * (if v then d else t) + e ≤ M) ↔
    a + (r : ℤ) * max b t + (s : ℤ) * max d t + e ≤ M := by
  constructor
  · intro h
    rcases le_total t b with hb | hb <;> rcases le_total t d with hd | hd
    · simpa only [Bool.true_eq, Bool.false_eq_true, ↓reduceIte, max_eq_left hb, max_eq_left hd] using h true true
    · simpa only [Bool.true_eq, Bool.false_eq_true, ↓reduceIte, max_eq_left hb, max_eq_right hd] using h true false
    · simpa only [Bool.true_eq, Bool.false_eq_true, ↓reduceIte, max_eq_right hb, max_eq_left hd] using h false true
    · simpa only [Bool.true_eq, Bool.false_eq_true, ↓reduceIte, max_eq_right hb, max_eq_right hd] using h false false
  · intro h u v
    have hu : (if u then b else t) ≤ max b t := by
      cases u
      · exact le_max_right _ _
      · exact le_max_left _ _
    have hv : (if v then d else t) ≤ max d t := by
      cases v
      · exact le_max_right _ _
      · exact le_max_left _ _
    have hr := mul_le_mul_of_nonneg_left hu (Int.natCast_nonneg r)
    have hs := mul_le_mul_of_nonneg_left hv (Int.natCast_nonneg s)
    omega

def branchUpper (c : PhaseRowContext) (w mode z : ℕ) : ℤ :=
  (sourceLine c w z : ℤ) + complementUpper c.R c.V mode z +
  (c.R : ℤ) * max
    ((unitSlope (c.R+c.V) c.R : ℤ)*(c.R+c.V+z) +
      (unitConstant (c.R+c.V) c.R : ℤ)) 7000000000000 +
  ((33-c.R : ℕ) : ℤ) * max
    ((unitSlope (153-(c.R+c.V)) (33-c.R) : ℤ)*(21378-c.R-c.V-z) +
      (unitConstant (153-(c.R+c.V)) (33-c.R) : ℤ)) 7000000000000 +
  14000000000000 + 860903991184427

theorem branches_iff (c : PhaseRowContext) (w mode z : ℕ) :
    (∀ u v : Bool, branch c w mode u v z ≤ bound) ↔
      branchUpper c w mode z ≤ bound := by
  unfold branch branchUpper
  simpa only [add_assoc] using bool_pair_bound_iff
    ((sourceLine c w z : ℤ) + complementUpper c.R c.V mode z)
    ((unitSlope (c.R+c.V) c.R : ℤ)*(c.R+c.V+z) +
      (unitConstant (c.R+c.V) c.R : ℤ))
    ((unitSlope (153-(c.R+c.V)) (33-c.R) : ℤ)*(21378-c.R-c.V-z) +
      (unitConstant (153-(c.R+c.V)) (33-c.R) : ℤ))
    7000000000000 (14000000000000 + 860903991184427) bound c.R (33-c.R)

def RunValid (c : PhaseRowContext) (start : ℕ) (run : LedgerRun) : Prop :=
  start < run.stop ∧ run.stop ≤ 7200-(c.R+c.V) ∧ run.witness ≤ 6 ∧
  SourceActive c run.witness start ∧ SourceCell c run.witness start (run.stop-1) ∧
  ∀ u v : Bool, branch c run.witness run.mode u v start ≤ bound ∧
    branch c run.witness run.mode u v (run.stop-1) ≤ bound
def FastRunValid (c : PhaseRowContext) (start : ℕ) (run : LedgerRun) : Prop :=
  start < run.stop ∧ run.stop ≤ 7200-(c.R+c.V) ∧ run.witness ≤ 6 ∧
  SourceActive c run.witness start ∧ SourceCell c run.witness start (run.stop-1) ∧
  branchUpper c run.witness run.mode start ≤ bound ∧
  branchUpper c run.witness run.mode (run.stop-1) ≤ bound

instance (c : PhaseRowContext) (start : ℕ) (run : LedgerRun) :
    Decidable (FastRunValid c start run) := by
  unfold FastRunValid
  infer_instance

theorem runValid_iff_fast (c : PhaseRowContext) (start : ℕ) (run : LedgerRun) :
    RunValid c start run ↔ FastRunValid c start run := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩
    exact ⟨h0, h1, h2, h3, h4,
      (branches_iff _ _ _ _).mp (fun u v => (h5 u v).1),
      (branches_iff _ _ _ _).mp (fun u v => (h5 u v).2)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩
    exact ⟨h0, h1, h2, h3, h4, fun u v =>
      ⟨(branches_iff _ _ _ _).mpr h5 u v, (branches_iff _ _ _ _).mpr h6 u v⟩⟩

instance (c : PhaseRowContext) (start : ℕ) (run : LedgerRun) : Decidable (RunValid c start run) :=
  decidable_of_iff (FastRunValid c start run) (runValid_iff_fast c start run).symm

theorem RunValid.sound (c : PhaseRowContext) (start z : ℕ) (run : LedgerRun)
    (h : RunValid c start run) (hlo : start ≤ z) (hhi : z < run.stop) : ledger c z ≤ bound := by
  rcases h with ⟨hstart, hstop, hw, ha, hcell, hb⟩
  apply ledger_le_of_branches c run.witness run.mode z hw
    (sourceActive_mono c run.witness start z ha hlo) (by omega)
  intro u v
  exact branch_between c run.witness run.mode start (run.stop-1) z u v hw hcell hlo
    (by omega) (hb u v).1 (hb u v).2

def RunsValid (c : PhaseRowContext) : ℕ → List LedgerRun → Prop
  | start, [] => start = 7200-(c.R+c.V)
  | start, run :: runs => RunValid c start run ∧ RunsValid c run.stop runs
instance (c : PhaseRowContext) (start : ℕ) (runs : List LedgerRun) :
    Decidable (RunsValid c start runs) := by
  induction runs generalizing start with
  | nil => simp only [RunsValid]; infer_instance
  | cons run runs ih => simp only [RunsValid]; infer_instance

theorem RunsValid.sound (c : PhaseRowContext) (runs : List LedgerRun) (start z : ℕ)
    (h : RunsValid c start runs) (hlo : start ≤ z) (hhi : z < 7200-(c.R+c.V)) : ledger c z ≤ bound := by
  induction runs generalizing start with
  | nil => simp only [RunsValid] at h; omega
  | cons run runs ih =>
      by_cases hz : z < run.stop
      · exact RunValid.sound c start z run h.1 hlo hz
      · exact ih run.stop h.2 (by omega)

end ProximityPrize.SubmissionLower.Lower80801.LedgerAudit
