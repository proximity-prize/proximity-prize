import ProximityPrize.SubmissionLower.BoundaryTailBaseFast

/-! A separately convex sequence is bounded by its endpoints. The tables below
certify convexity in v from 1 and in r from 2. Retaining the exceptional boundary
points and reflecting the zero-table indices reduces each strict split check to
at most sixteen corners, while implying the original quantified proposition. -/
namespace ProximityPrize.SubmissionLower.BoundaryTailConvexity

set_option autoImplicit false
set_option maxHeartbeats 1000000

def ConvexOn (f : ℕ → ℕ) (lo hi : ℕ) : Prop :=
  ∀ i, lo ≤ i → i + 2 ≤ hi → 2 * f (i + 1) ≤ f i + f (i + 2)

theorem bound_length (f : ℕ → ℕ) (n lo cap : ℕ)
    (hc : ConvexOn f lo (lo + n)) (hlo : f lo ≤ cap)
    (hhi : f (lo + n) ≤ cap) (v : ℕ) (hv0 : lo ≤ v) (hv1 : v ≤ lo + n) :
    f v ≤ cap := by
  induction n generalizing lo cap v with
  | zero =>
      have heq : v = lo := by omega
      simpa only [heq] using hlo
  | succ n ih =>
      have hend : lo + 1 + n = lo + (n + 1) := by omega
      have hlast : f (lo + 1 + n) ≤ cap := by simpa only [hend] using hhi
      have htail : ConvexOn f (lo + 1) (lo + 1 + n) := by
        intro i hi hi2
        exact hc i (by omega) (by omega)
      have hfirst : f (lo + 1) ≤ cap := by
        by_cases hn : n = 0
        · simpa only [hn, Nat.add_zero] using hlast
        · have hmid := ih (lo + 1) (max (f (lo + 1)) cap) htail
            (le_max_left _ _) (hlast.trans (le_max_right _ _)) (lo + 2)
            (by omega) (by omega)
          have hstep := hc lo (by omega) (by omega)
          by_cases hle : f (lo + 1) ≤ cap
          · exact hle
          · rw [max_eq_left (by omega : cap ≤ f (lo + 1))] at hmid
            omega
      by_cases heq : v = lo
      · simpa only [heq] using hlo
      · exact ih (lo + 1) cap htail hfirst hlast v (by omega) (by omega)

theorem bound (f : ℕ → ℕ) (lo hi cap v : ℕ)
    (hc : ConvexOn f lo hi) (hlo : f lo ≤ cap) (hhi : f hi ≤ cap)
    (hv0 : lo ≤ v) (hv1 : v ≤ hi) : f v ≤ cap := by
  have heq : lo + (hi - lo) = hi := by omega
  exact bound_length f (hi - lo) lo cap (by simpa only [heq] using hc) hlo
    (by simpa only [heq] using hhi) v hv0 (by omega)

theorem add {f g : ℕ → ℕ} {lo hi : ℕ}
    (hf : ConvexOn f lo hi) (hg : ConvexOn g lo hi) :
    ConvexOn (fun v => f v + g v) lo hi := by
  intro i hi0 hi1
  have h1 := hf i hi0 hi1
  have h2 := hg i hi0 hi1
  dsimp
  omega

theorem mul {f : ℕ → ℕ} {lo hi : ℕ} (k : ℕ) (hf : ConvexOn f lo hi) :
    ConvexOn (fun v => f v * k) lo hi := by
  intro i hi0 hi1
  have h := Nat.mul_le_mul_right k (hf i hi0 hi1)
  dsimp
  nlinarith

theorem reverse {f : ℕ → ℕ} (N lo hi : ℕ) (hhi : hi ≤ N)
    (hf : ConvexOn f (N - hi) (N - lo)) :
    ConvexOn (fun v => f (N - v)) lo hi := by
  intro i hi0 hi1
  have h := hf (N - (i + 2)) (by omega) (by omega)
  have heq1 : N - (i + 2) + 1 = N - (i + 1) := by omega
  have heq2 : N - (i + 2) + 2 = N - i := by omega
  dsimp
  simpa only [heq1, heq2, Nat.add_comm] using h

open BoundaryTailBaseChecksCore BoundaryTailBaseFast

structure ConvexCarrier (c : ℕ → Carrier) (lo hi : ℕ) : Prop where
  c0 : ConvexOn (fun v => (c v).c0) lo hi
  c1 : ConvexOn (fun v => (c v).c1) lo hi
  c2 : ConvexOn (fun v => (c v).c2) lo hi
  c3 : ConvexOn (fun v => (c v).c3) lo hi
  slope : ConvexOn (fun v => (c v).c4 - (c v).c3) lo hi

theorem bounds_between (c : ℕ → Carrier) (g : ℕ → ℕ) (a b v start : ℕ)
    (cuts : List Cut) (hc : ConvexCarrier c a b) (hg : ConvexOn g a b)
    (ha : Bounds (c a) (g a) start cuts) (hb : Bounds (c b) (g b) start cuts)
    (hv0 : a ≤ v) (hv1 : v ≤ b) : Bounds (c v) (g v) start cuts := by
  induction cuts generalizing start with
  | nil => trivial
  | cons cut cuts ih =>
      rcases ha with ⟨ha0, ha1, harest⟩
      rcases hb with ⟨hb0, hb1, hbrest⟩
      refine ⟨?_, ?_, ih cut.stop harest hbrest⟩
      · exact bound _ a b cut.loValue v
          (add (add hc.c3 (mul (start - 3) hc.slope)) hg) ha0 hb0 hv0 hv1
      · exact bound _ a b cut.hiValue v
          (add (add hc.c3 (mul (cut.stop - 1 - 3) hc.slope)) hg) ha1 hb1 hv0 hv1

theorem check_between (row : Row) (c : ℕ → Carrier) (g : ℕ → ℕ) (a b v : ℕ)
    (hc : ConvexCarrier c a b) (hg : ConvexOn g a b)
    (ha : Check row (c a) (g a)) (hb : Check row (c b) (g b))
    (hv0 : a ≤ v) (hv1 : v ≤ b) : Check row (c v) (g v) := by
  rcases ha with ⟨ha0, ha1, ha2, harest⟩
  rcases hb with ⟨hb0, hb1, hb2, hbrest⟩
  exact ⟨bound _ a b row.z0 v (add hc.c0 hg) ha0 hb0 hv0 hv1,
    bound _ a b row.z1 v (add hc.c1 hg) ha1 hb1 hv0 hv1,
    bound _ a b row.z2 v (add hc.c2 hg) ha2 hb2 hv0 hv1,
    bounds_between c g a b v 3 row.cuts hc hg harest hbrest hv0 hv1⟩

open BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

def Step (a b c : Carrier) (x y z : ℕ) : Prop :=
  2*b.c0 ≤ a.c0+c.c0 ∧ 2*b.c1 ≤ a.c1+c.c1 ∧
  2*b.c2 ≤ a.c2+c.c2 ∧ 2*b.c3 ≤ a.c3+c.c3 ∧
  2*(b.c4-b.c3) ≤ (a.c4-a.c3)+(c.c4-c.c3) ∧ 2*y ≤ x+z

instance (a b c : Carrier) (x y z : ℕ) : Decidable (Step a b c x y z) := by
  unfold Step
  infer_instance

def CellV (r v : ℕ) : Prop :=
  Step (fastCarriers r v) (fastCarriers r (v+1)) (fastCarriers r (v+2))
    (fastZero r v) (fastZero r (v+1)) (fastZero r (v+2))

instance (r v : ℕ) : Decidable (CellV r v) := by unfold CellV; infer_instance

def CellR (r v : ℕ) : Prop :=
  Step (fastCarriers r v) (fastCarriers (r+1) v) (fastCarriers (r+2) v)
    (fastZero r v) (fastZero (r+1) v) (fastZero (r+2) v)

instance (r v : ℕ) : Decidable (CellR r v) := by unfold CellR; infer_instance

theorem vRow1 : ∀ i ∈ List.range 139, CellV 1 (i+1) := by decide +kernel

theorem vRow2 : ∀ i ∈ List.range 138, CellV 2 (i+1) := by decide +kernel

theorem vRow3 : ∀ i ∈ List.range 137, CellV 3 (i+1) := by decide +kernel

theorem vRow4 : ∀ i ∈ List.range 136, CellV 4 (i+1) := by decide +kernel

theorem vRow5 : ∀ i ∈ List.range 135, CellV 5 (i+1) := by decide +kernel

theorem vRow6 : ∀ i ∈ List.range 134, CellV 6 (i+1) := by decide +kernel

theorem vRow7 : ∀ i ∈ List.range 133, CellV 7 (i+1) := by decide +kernel

theorem vRow8 : ∀ i ∈ List.range 132, CellV 8 (i+1) := by decide +kernel

theorem vRow9 : ∀ i ∈ List.range 131, CellV 9 (i+1) := by decide +kernel

theorem vRow10 : ∀ i ∈ List.range 130, CellV 10 (i+1) := by decide +kernel

theorem vRow11 : ∀ i ∈ List.range 129, CellV 11 (i+1) := by decide +kernel

theorem vRow12 : ∀ i ∈ List.range 128, CellV 12 (i+1) := by decide +kernel

theorem vRow13 : ∀ i ∈ List.range 127, CellV 13 (i+1) := by decide +kernel

theorem vRow14 : ∀ i ∈ List.range 126, CellV 14 (i+1) := by decide +kernel

theorem vRow15 : ∀ i ∈ List.range 125, CellV 15 (i+1) := by decide +kernel

theorem vRow16 : ∀ i ∈ List.range 124, CellV 16 (i+1) := by decide +kernel

theorem vRow17 : ∀ i ∈ List.range 123, CellV 17 (i+1) := by decide +kernel

theorem vRow18 : ∀ i ∈ List.range 122, CellV 18 (i+1) := by decide +kernel

theorem vRow19 : ∀ i ∈ List.range 121, CellV 19 (i+1) := by decide +kernel

theorem vRow20 : ∀ i ∈ List.range 120, CellV 20 (i+1) := by decide +kernel

theorem vRow21 : ∀ i ∈ List.range 119, CellV 21 (i+1) := by decide +kernel

theorem vRow22 : ∀ i ∈ List.range 118, CellV 22 (i+1) := by decide +kernel

theorem vRow23 : ∀ i ∈ List.range 117, CellV 23 (i+1) := by decide +kernel

theorem vRow24 : ∀ i ∈ List.range 116, CellV 24 (i+1) := by decide +kernel

theorem vRow25 : ∀ i ∈ List.range 115, CellV 25 (i+1) := by decide +kernel

theorem vRow26 : ∀ i ∈ List.range 114, CellV 26 (i+1) := by decide +kernel

theorem vRow27 : ∀ i ∈ List.range 113, CellV 27 (i+1) := by decide +kernel

theorem vRow28 : ∀ i ∈ List.range 112, CellV 28 (i+1) := by decide +kernel

theorem vRow29 : ∀ i ∈ List.range 111, CellV 29 (i+1) := by decide +kernel

theorem vRow30 : ∀ i ∈ List.range 110, CellV 30 (i+1) := by decide +kernel

theorem vRow31 : ∀ i ∈ List.range 109, CellV 31 (i+1) := by decide +kernel

theorem rRow2 : ∀ v ∈ List.range 139, CellR 2 v := by decide +kernel

theorem rRow3 : ∀ v ∈ List.range 138, CellR 3 v := by decide +kernel

theorem rRow4 : ∀ v ∈ List.range 137, CellR 4 v := by decide +kernel

theorem rRow5 : ∀ v ∈ List.range 136, CellR 5 v := by decide +kernel

theorem rRow6 : ∀ v ∈ List.range 135, CellR 6 v := by decide +kernel

theorem rRow7 : ∀ v ∈ List.range 134, CellR 7 v := by decide +kernel

theorem rRow8 : ∀ v ∈ List.range 133, CellR 8 v := by decide +kernel

theorem rRow9 : ∀ v ∈ List.range 132, CellR 9 v := by decide +kernel

theorem rRow10 : ∀ v ∈ List.range 131, CellR 10 v := by decide +kernel

theorem rRow11 : ∀ v ∈ List.range 130, CellR 11 v := by decide +kernel

theorem rRow12 : ∀ v ∈ List.range 129, CellR 12 v := by decide +kernel

theorem rRow13 : ∀ v ∈ List.range 128, CellR 13 v := by decide +kernel

theorem rRow14 : ∀ v ∈ List.range 127, CellR 14 v := by decide +kernel

theorem rRow15 : ∀ v ∈ List.range 126, CellR 15 v := by decide +kernel

theorem rRow16 : ∀ v ∈ List.range 125, CellR 16 v := by decide +kernel

theorem rRow17 : ∀ v ∈ List.range 124, CellR 17 v := by decide +kernel

theorem rRow18 : ∀ v ∈ List.range 123, CellR 18 v := by decide +kernel

theorem rRow19 : ∀ v ∈ List.range 122, CellR 19 v := by decide +kernel

theorem rRow20 : ∀ v ∈ List.range 121, CellR 20 v := by decide +kernel

theorem rRow21 : ∀ v ∈ List.range 120, CellR 21 v := by decide +kernel

theorem rRow22 : ∀ v ∈ List.range 119, CellR 22 v := by decide +kernel

theorem rRow23 : ∀ v ∈ List.range 118, CellR 23 v := by decide +kernel

theorem rRow24 : ∀ v ∈ List.range 117, CellR 24 v := by decide +kernel

theorem rRow25 : ∀ v ∈ List.range 116, CellR 25 v := by decide +kernel

theorem rRow26 : ∀ v ∈ List.range 115, CellR 26 v := by decide +kernel

theorem rRow27 : ∀ v ∈ List.range 114, CellR 27 v := by decide +kernel

theorem rRow28 : ∀ v ∈ List.range 113, CellR 28 v := by decide +kernel

theorem rRow29 : ∀ v ∈ List.range 112, CellR 29 v := by decide +kernel

theorem cellV {r v : ℕ} (hr0 : 1 ≤ r) (hr1 : r ≤ 31)
    (hv : 1 ≤ v) (hfit : r+v+2 ≤ 142) : CellV r v := by
  interval_cases r
  · simpa only [Nat.sub_add_cancel hv] using vRow1 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow2 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow3 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow4 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow5 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow6 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow7 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow8 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow9 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow10 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow11 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow12 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow13 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow14 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow15 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow16 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow17 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow18 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow19 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow20 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow21 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow22 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow23 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow24 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow25 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow26 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow27 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow28 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow29 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow30 (v-1) (List.mem_range.mpr (by omega))
  · simpa only [Nat.sub_add_cancel hv] using vRow31 (v-1) (List.mem_range.mpr (by omega))

theorem cellR {r v : ℕ} (hr0 : 2 ≤ r) (hr1 : r+2 ≤ 31)
    (hfit : r+v+2 ≤ 142) : CellR r v := by
  have hr : r ≤ 29 := by omega
  interval_cases r
  · exact rRow2 v (List.mem_range.mpr (by omega))
  · exact rRow3 v (List.mem_range.mpr (by omega))
  · exact rRow4 v (List.mem_range.mpr (by omega))
  · exact rRow5 v (List.mem_range.mpr (by omega))
  · exact rRow6 v (List.mem_range.mpr (by omega))
  · exact rRow7 v (List.mem_range.mpr (by omega))
  · exact rRow8 v (List.mem_range.mpr (by omega))
  · exact rRow9 v (List.mem_range.mpr (by omega))
  · exact rRow10 v (List.mem_range.mpr (by omega))
  · exact rRow11 v (List.mem_range.mpr (by omega))
  · exact rRow12 v (List.mem_range.mpr (by omega))
  · exact rRow13 v (List.mem_range.mpr (by omega))
  · exact rRow14 v (List.mem_range.mpr (by omega))
  · exact rRow15 v (List.mem_range.mpr (by omega))
  · exact rRow16 v (List.mem_range.mpr (by omega))
  · exact rRow17 v (List.mem_range.mpr (by omega))
  · exact rRow18 v (List.mem_range.mpr (by omega))
  · exact rRow19 v (List.mem_range.mpr (by omega))
  · exact rRow20 v (List.mem_range.mpr (by omega))
  · exact rRow21 v (List.mem_range.mpr (by omega))
  · exact rRow22 v (List.mem_range.mpr (by omega))
  · exact rRow23 v (List.mem_range.mpr (by omega))
  · exact rRow24 v (List.mem_range.mpr (by omega))
  · exact rRow25 v (List.mem_range.mpr (by omega))
  · exact rRow26 v (List.mem_range.mpr (by omega))
  · exact rRow27 v (List.mem_range.mpr (by omega))
  · exact rRow28 v (List.mem_range.mpr (by omega))
  · exact rRow29 v (List.mem_range.mpr (by omega))

theorem carrierV (r lo hi : ℕ) (hr0 : 1 ≤ r) (hr1 : r ≤ 31)
    (hlo : 1 ≤ lo) (hfit : r+hi ≤ 142) :
    ConvexCarrier (fun v => fastCarriers r v) lo hi := by
  constructor <;> intro i hi0 hi1
  all_goals have h := cellV hr0 hr1 (by omega : 1 ≤ i) (by omega : r+i+2 ≤ 142)
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1

theorem zeroV (r lo hi : ℕ) (hr0 : 1 ≤ r) (hr1 : r ≤ 31)
    (hlo : 1 ≤ lo) (hfit : r+hi ≤ 142) :
    ConvexOn (fun v => fastZero r v) lo hi := by
  intro i hi0 hi1
  exact (cellV hr0 hr1 (by omega : 1 ≤ i) (by omega : r+i+2 ≤ 142)).2.2.2.2.2

theorem carrierR (v lo hi : ℕ) (hlo : 2 ≤ lo) (hhi : hi ≤ 31)
    (hfit : hi+v ≤ 142) :
    ConvexCarrier (fun r => fastCarriers r v) lo hi := by
  constructor <;> intro i hi0 hi1
  all_goals have h := cellR (r := i) (v := v) (by omega : 2 ≤ i) (by omega : i+2 ≤ 31) (by omega : i+v+2 ≤ 142)
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1

theorem zeroR (v lo hi : ℕ) (hlo : 2 ≤ lo) (hhi : hi ≤ 31)
    (hfit : hi+v ≤ 142) :
    ConvexOn (fun r => fastZero r v) lo hi := by
  intro i hi0 hi1
  exact (cellR (by omega : 2 ≤ i) (by omega : i+2 ≤ 31)
    (by omega : i+v+2 ≤ 142)).2.2.2.2.2

open BoundaryTailBaseChecksCore BoundaryTailBaseFast
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The guard records the exact domain of the convexity receipts. -/
def strictCornersBool (row : Row) (R V : ℕ) : Bool :=
  decide (R ≤ 31 ∧ R+V ≤ 142) &&
    [1, 2, R-2, R-1].all fun r =>
      decide (r = 0 ∨ R ≤ r) || [0, 1, V-1, V].all fun v =>
        decide (V < v) || decide (Check row (fastCarriers r v) (fastZero (R-r) (V-v)))

theorem strictCornersBool_sound (row : Row) (R V : ℕ)
    (h : strictCornersBool row R V = true) : StrictAtFast row R V := by
  simp only [strictCornersBool, Bool.and_eq_true, Bool.or_eq_true,
    List.all_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨hR, hRV⟩, hall⟩
  have get (r v : ℕ) (hr : r ∈ [1, 2, R-2, R-1])
      (hv : v ∈ [0, 1, V-1, V]) (hr0 : 1 ≤ r) (hr1 : r < R) (hv1 : v ≤ V) :
      Check row (fastCarriers r v) (fastZero (R-r) (V-v)) := by
    rcases hall r hr with hbad | hh
    · omega
    · rcases hh v hv with hbad | hgood
      · omega
      · exact hgood
  have alongR (v : ℕ) (hv : v ∈ [0, 1, V-1, V]) (hv1 : v ≤ V)
      (r : ℕ) (hr0 : 1 ≤ r) (hr1 : r < R) :
      Check row (fastCarriers r v) (fastZero (R-r) (V-v)) := by
    by_cases hfirst : r = 1
    · subst r
      exact get 1 v (by simp) hv hr0 hr1 hv1
    by_cases hlast : r = R-1
    · subst r
      exact get (R-1) v (by simp) hv hr0 hr1 hv1
    have hrlo : 2 ≤ r := by omega
    have hrhi : r ≤ R-2 := by omega
    have hlarge : 4 ≤ R := by omega
    have hc : ConvexCarrier (fun r => fastCarriers r v) 2 (R-2) :=
      carrierR v 2 (R-2) (by omega) (by omega) (by omega)
    have hz : ConvexOn (fun r => fastZero (R-r) (V-v)) 2 (R-2) := by
      apply reverse (f := fun r => fastZero r (V-v)) R 2 (R-2) (by omega)
      have heq : R-(R-2) = 2 := by omega
      rw [heq]
      exact zeroR (V-v) 2 (R-2) (by omega) (by omega) (by omega)
    exact check_between row (fun r => fastCarriers r v)
      (fun r => fastZero (R-r) (V-v)) 2 (R-2) r hc hz
      (get 2 v (by simp) hv (by omega) (by omega) hv1)
      (get (R-2) v (by simp) hv (by omega) (by omega) hv1) hrlo hrhi
  intro r hr v hv hr0
  have hr1 : r < R := List.mem_range.mp hr
  have hv1 : v ≤ V := by have hh := List.mem_range.mp hv; omega
  by_cases hfirst : v = 0
  · subst v
    exact alongR 0 (by simp) (by omega) r hr0 hr1
  by_cases hlast : v = V
  · subst v
    exact alongR V (by simp) (by omega) r hr0 hr1
  have hvlo : 1 ≤ v := by omega
  have hvhi : v ≤ V-1 := by omega
  have hlarge : 2 ≤ V := by omega
  have hc : ConvexCarrier (fun v => fastCarriers r v) 1 (V-1) :=
    carrierV r 1 (V-1) hr0 (by omega) (by omega) (by omega)
  have hz : ConvexOn (fun v => fastZero (R-r) (V-v)) 1 (V-1) := by
    apply reverse (f := fastZero (R-r)) V 1 (V-1) (by omega)
    rw [show V-(V-1) = 1 by omega]
    exact zeroV (R-r) 1 (V-1) (by omega) (by omega) (by omega) (by omega)
  exact check_between row (fun v => fastCarriers r v)
    (fun v => fastZero (R-r) (V-v)) 1 (V-1) v hc hz
    (alongR 1 (by simp) (by omega) r hr0 hr1)
    (alongR (V-1) (by simp) (by omega) r hr0 hr1) hvlo hvhi

end ProximityPrize.SubmissionLower.BoundaryTailConvexity
