import ProximityPrize.SubmissionLower.MovingFiberInitialArithmetic6811
import ProximityPrize.SubmissionLower.MovingFiberCountingArithmetic6811
import ProximityPrize.SubmissionLower.MovingFiberPhaseCore6811
import ProximityPrize.SubmissionLower.FoldChainArithmetic6813
import ProximityPrize.SubmissionLower.MovingFiberPairArithmetic6813

namespace ProximityPrize.SubmissionLower.Lower80860.LedgerAudit
open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (Potential rawFlag)
open Lower80860.Initial Lower80860.PhaseRows FoldChainPolynomial6813
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def bound : ℕ := 274980719741869740

def ledger (c : PhaseRowContext) (z : ℕ) : ℕ :=
  capBefore c 10 z + initialAComplement (rawFlag c.R c.V z) +
    c.R * foldUnit (c.R+c.V) (c.R+c.V+z) c.R +
    (40-c.R) * foldUnit (185-(c.R+c.V)) (27313-(c.R+c.V+z)) (40-c.R) +
    18000000000000 + (PairCell6813.cap c.R (c.R+c.V) (c.R+c.V+z)+42*1378234957498)

/-- The affine pieces of `foldUnit` as functions of the `Z`-cap `t`. -/
def piece (y r : ℕ) (u : Fin 3) (t : ℤ) : ℤ :=
  if r < 2 ∨ u = 0 then 9000000000000
  else if u = 1 then (foldSlope y 2 : ℤ)*t + (foldConst y 2 : ℤ)
  else (foldSlope y r : ℤ)*t + (foldConst y r : ℤ)

def pieceSlope (y r : ℕ) (u : Fin 3) : ℤ :=
  if r < 2 ∨ u = 0 then 0
  else if u = 1 then (foldSlope y 2 : ℤ)
  else (foldSlope y r : ℤ)

theorem piece_affine (y r : ℕ) (u : Fin 3) (t t0 : ℤ) :
    piece y r u t = piece y r u t0 + pieceSlope y r u * (t-t0) := by
  unfold piece pieceSlope
  split_ifs <;> ring

def unitUpper (y r : ℕ) (t : ℤ) : ℤ :=
  max (piece y r 0 t) (max (piece y r 1 t) (piece y r 2 t))

theorem foldUnit_cast (y z r : ℕ) : (foldUnit y z r : ℤ) = unitUpper y r z := by
  unfold foldUnit unitUpper piece foldPiece
  by_cases hr : r < 2
  · simp [hr]
  · simp only [hr, false_or, if_false, if_true, Fin.isValue]
    simp only [show ¬ ((1 : Fin 3) = 0) by decide, show ¬ ((2 : Fin 3) = 0) by decide,
      show ¬ ((2 : Fin 3) = 1) by decide, if_false]
    push_cast
    rfl

theorem exists_piece (y r : ℕ) (t : ℤ) : ∃ u, unitUpper y r t = piece y r u t := by
  unfold unitUpper
  rcases max_choice (piece y r 0 t) (max (piece y r 1 t) (piece y r 2 t)) with h | h
  · exact ⟨0, h⟩
  · rw [h]
    rcases max_choice (piece y r 1 t) (piece y r 2 t) with h' | h'
    · exact ⟨1, h'⟩
    · exact ⟨2, h'⟩

theorem piece_le_upper (y r : ℕ) (u : Fin 3) (t : ℤ) : piece y r u t ≤ unitUpper y r t := by
  unfold unitUpper
  fin_cases u
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

def complementUpper (R V mode z : ℕ) : ℤ :=
  let t : ℤ := 10169-R-V-z
  let y : ℕ := 185-(R+V)
  let r : ℕ := min y (40-R)
  if mode = 0 then 9182745250*t+5716429996169*y+26789807578148*r
  else if mode = 1 then (9182745250+5716429996169)*t+26789807578148*r
  else (9182745250+5716429996169+26789807578148)*t

def complementSlope (mode : ℕ) : ℤ :=
  if mode = 0 then -9182745250
  else if mode = 1 then -(9182745250+5716429996169)
  else -(9182745250+5716429996169+26789807578148)

theorem complement_formula (R V z : ℕ) :
    initialAComplement (rawFlag R V z) =
      9182745250*(10169-(R+V+z)) +
      5716429996169*min (10169-(R+V+z)) (185-(R+V)) +
      26789807578148*min (10169-(R+V+z)) (min (185-(R+V)) (40-R)) := by
  simp [initialAComplement, initialAPotential, Potential.eval, rawFlag,
    total, middle, Nat.min_def]
  split_ifs <;> omega

theorem complement_le_upper (R V mode z : ℕ) (ht : R+V+z ≤ 10169) :
    (initialAComplement (rawFlag R V z) : ℤ) ≤ complementUpper R V mode z := by
  rw [complement_formula]
  have hmy := Nat.min_le_right (10169-(R+V+z)) (185-(R+V))
  have hmt := Nat.min_le_left (10169-(R+V+z)) (185-(R+V))
  have hmr := Nat.min_le_right (10169-(R+V+z)) (min (185-(R+V)) (40-R))
  have hmrt := Nat.min_le_left (10169-(R+V+z)) (min (185-(R+V)) (40-R))
  have hti : ((10169-(R+V+z) : ℕ) : ℤ) = 10169-R-V-z := by omega
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [hti]
  unfold complementUpper
  split_ifs <;> dsimp only <;> omega

def branch (c : PhaseRowContext) (w mode : ℕ) (u v : Fin 3) (z : ℕ) : ℤ :=
  (sourceLine c w z : ℤ) + complementUpper c.R c.V mode z +
  (c.R : ℤ)*piece (c.R+c.V) c.R u ((c.R : ℤ)+c.V+z) +
  ((40-c.R : ℕ) : ℤ)*piece (185-(c.R+c.V)) (40-c.R) v (27313-c.R-c.V-z) +
  18000000000000+(PairCell6813.line c.R (c.R+c.V) (c.R+c.V+z)+42*1378234957498)

def branchSlope (c : PhaseRowContext) (w mode lo : ℕ) (u v : Fin 3) : ℤ :=
  (sourceSlope c w lo : ℤ)+complementSlope mode+
  (c.R : ℤ)*pieceSlope (c.R+c.V) c.R u-
  ((40-c.R : ℕ) : ℤ)*pieceSlope (185-(c.R+c.V)) (40-c.R) v-
  ((PairCell6813.slope c.R (c.R+c.V) / 50194 : ℕ) : ℤ)

theorem branch_affine (c : PhaseRowContext) (w mode lo hi z : ℕ) (u v : Fin 3)
    (hw : w ≤ 10)
    (hc : SourceCell c w lo hi) (hz : lo ≤ z) (hhi : z ≤ hi) :
    branch c w mode u v z = branch c w mode u v lo +
      branchSlope c w mode lo u v * ((z : ℤ)-lo) := by
  have hs := sourceLine_affine c w lo hi z hw hc hz hhi
  have hsi : (sourceLine c w z : ℤ) = (sourceLine c w lo : ℤ)+
      (sourceSlope c w lo : ℤ)*((z : ℤ)-lo) := by
    rw [hs]
    push_cast [Nat.cast_sub hz]
    rfl
  unfold branch branchSlope complementUpper complementSlope PairCell6813.line
  rw [hsi, piece_affine (c.R+c.V) c.R u ((c.R : ℤ)+c.V+z) ((c.R : ℤ)+c.V+lo),
    piece_affine (185-(c.R+c.V)) (40-c.R) v (27313-c.R-c.V-z) (27313-c.R-c.V-lo)]
  simp only [Nat.cast_add]
  split_ifs <;> ring

theorem branch_between (c : PhaseRowContext) (w mode lo hi z : ℕ) (u v : Fin 3)
    (hw : w ≤ 10)
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
    (hw : w ≤ 10) (ha : SourceActive c w z) (ht : c.R+c.V+z ≤ 10169)
    (hb : ∀ u v : Fin 3, branch c w mode u v z ≤ bound) : ledger c z ≤ bound := by
  have hs : (capBefore c 10 z : ℤ) ≤ sourceLine c w z := by
    exact_mod_cast capBefore_le_sourceLine c 10 w z hw ha
  have hc := complement_le_upper c.R c.V mode z ht
  have hti : ((27313-(c.R+c.V+z) : ℕ) : ℤ) = 27313-c.R-c.V-z := by omega
  have hp := PairCell6813.cap_le_line c.R (c.R+c.V) (c.R+c.V+z) (by omega)
  obtain ⟨u, hu⟩ := exists_piece (c.R+c.V) c.R ((c.R : ℤ)+c.V+z)
  obtain ⟨v, hv⟩ := exists_piece (185-(c.R+c.V)) (40-c.R) (27313-c.R-c.V-z)
  have h1 : (foldUnit (c.R+c.V) (c.R+c.V+z) c.R : ℤ) =
      piece (c.R+c.V) c.R u ((c.R : ℤ)+c.V+z) := by
    rw [foldUnit_cast, ← hu]
    push_cast
    rfl
  have h2 : (foldUnit (185-(c.R+c.V)) (27313-(c.R+c.V+z)) (40-c.R) : ℤ) =
      piece (185-(c.R+c.V)) (40-c.R) v (27313-c.R-c.V-z) := by
    rw [foldUnit_cast, hti, ← hv]
  have hh := hb u v
  unfold branch at hh
  have hl : (ledger c z : ℤ) ≤ bound := by
    unfold ledger
    push_cast [h1, h2]
    linarith
  exact_mod_cast hl


structure LedgerRun where
  stop : ℕ
  witness : ℕ
  mode : ℕ
  deriving DecidableEq, Repr

theorem fin3_pair_bound_iff (a e M : ℤ) (f g : Fin 3 → ℤ) (r s : ℕ) :
    (∀ u v : Fin 3, a + (r : ℤ) * f u + (s : ℤ) * g v + e ≤ M) ↔
    a + (r : ℤ) * max (f 0) (max (f 1) (f 2)) +
      (s : ℤ) * max (g 0) (max (g 1) (g 2)) + e ≤ M := by
  have hmax (h : Fin 3 → ℤ) : ∃ u, max (h 0) (max (h 1) (h 2)) = h u := by
    rcases max_choice (h 0) (max (h 1) (h 2)) with k | k
    · exact ⟨0, k⟩
    · rw [k]
      rcases max_choice (h 1) (h 2) with k' | k'
      · exact ⟨1, k'⟩
      · exact ⟨2, k'⟩
  have hle (h : Fin 3 → ℤ) (u : Fin 3) : h u ≤ max (h 0) (max (h 1) (h 2)) := by
    fin_cases u
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  constructor
  · intro h
    obtain ⟨u, hu⟩ := hmax f
    obtain ⟨v, hv⟩ := hmax g
    rw [hu, hv]
    exact h u v
  · intro h u v
    have hr := mul_le_mul_of_nonneg_left (hle f u) (Int.natCast_nonneg r)
    have hs := mul_le_mul_of_nonneg_left (hle g v) (Int.natCast_nonneg s)
    linarith

def branchUpper (c : PhaseRowContext) (w mode z : ℕ) : ℤ :=
  (sourceLine c w z : ℤ) + complementUpper c.R c.V mode z +
  (c.R : ℤ) * unitUpper (c.R+c.V) c.R ((c.R : ℤ)+c.V+z) +
  ((40-c.R : ℕ) : ℤ) * unitUpper (185-(c.R+c.V)) (40-c.R) (27313-c.R-c.V-z) +
  18000000000000 + (PairCell6813.line c.R (c.R+c.V) (c.R+c.V+z)+42*1378234957498)

theorem branches_iff (c : PhaseRowContext) (w mode z : ℕ) :
    (∀ u v : Fin 3, branch c w mode u v z ≤ bound) ↔
      branchUpper c w mode z ≤ bound := by
  unfold branch branchUpper unitUpper
  simpa only [add_assoc] using fin3_pair_bound_iff
    ((sourceLine c w z : ℤ) + complementUpper c.R c.V mode z)
    (18000000000000 + (PairCell6813.line c.R (c.R+c.V) (c.R+c.V+z)+42*1378234957498)) bound
    (fun u => piece (c.R+c.V) c.R u ((c.R : ℤ)+c.V+z))
    (fun v => piece (185-(c.R+c.V)) (40-c.R) v (27313-c.R-c.V-z)) c.R (40-c.R)

def RunValid (c : PhaseRowContext) (start : ℕ) (run : LedgerRun) : Prop :=
  start < run.stop ∧ run.stop ≤ 10170-(c.R+c.V) ∧ run.witness ≤ 10 ∧
  SourceActive c run.witness start ∧ SourceCell c run.witness start (run.stop-1) ∧
  ∀ u v : Fin 3, branch c run.witness run.mode u v start ≤ bound ∧
    branch c run.witness run.mode u v (run.stop-1) ≤ bound
def FastRunValid (c : PhaseRowContext) (start : ℕ) (run : LedgerRun) : Prop :=
  start < run.stop ∧ run.stop ≤ 10170-(c.R+c.V) ∧ run.witness ≤ 10 ∧
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
  | start, [] => start = 10170-(c.R+c.V)
  | start, run :: runs => RunValid c start run ∧ RunsValid c run.stop runs
instance (c : PhaseRowContext) (start : ℕ) (runs : List LedgerRun) :
    Decidable (RunsValid c start runs) := by
  induction runs generalizing start with
  | nil => simp only [RunsValid]; infer_instance
  | cons run runs ih => simp only [RunsValid]; infer_instance

theorem RunsValid.sound (c : PhaseRowContext) (runs : List LedgerRun) (start z : ℕ)
    (h : RunsValid c start runs) (hlo : start ≤ z) (hhi : z < 10170-(c.R+c.V)) : ledger c z ≤ bound := by
  induction runs generalizing start with
  | nil => simp only [RunsValid] at h; omega
  | cons run runs ih =>
      by_cases hz : z < run.stop
      · exact RunValid.sound c start z run h.1 hlo hz
      · exact ih run.stop h.2 (by omega)

end ProximityPrize.SubmissionLower.Lower80860.LedgerAudit

#print axioms ProximityPrize.SubmissionLower.Lower80860.LedgerAudit.RunsValid.sound
