import ProximityPrize.SubmissionLower.Numeric2Aux
import ProximityPrize.SubmissionLower.FrontAssembly82200 -- serialize candidate build

set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

namespace CurveListSparsePackets
open Finset CJ0
open scoped BigOperators
open CJ1 (total total_eq_sum entryZ fastChoose right_witness)
local instance : Fact (Nat.Prime CJ0.p) := ⟨KoalaBear.is_prime⟩

private theorem entryZ_cast (r c : CJ0.Jet) : (entryZ r c : ZMod CJ0.p) = CJ0.blockEntry r c := by
  unfold entryZ CJ0.blockEntry
  split <;> simp [fastChoose, ← Nat.choose_eq_descFactorial_div_factorial, *]

structure Axes where
  outer : Bool → ℕ → ℕ
  fiber : Bool → ℕ → ℕ → ℕ → ℕ
  point : Bool → ℕ → ℕ → ℕ → ℕ → Jet

abbrev Axis (S : Axes) (side : Bool) (q u : ℕ) := (i : Fin (S.outer side q)) × Fin (S.fiber side q u i)
def size (S : Axes) (side : Bool) (q u : ℕ) := total (S.fiber side q u) (S.outer side q)

theorem card_axis (S : Axes) (side : Bool) (q u : ℕ) : Fintype.card (Axis S side q u) = size S side q u := by
  simp only [Axis, Fintype.card_sigma, Fintype.card_fin, size, total_eq_sum, Finset.sum_fin_eq_sum_range]
  exact Finset.sum_congr rfl (fun i hi => by simp [Finset.mem_range.mp hi])

def packet (S : Axes) (q u : ℕ) : Matrix (Axis S true q u) (Axis S false q u) (ZMod CJ0.p) :=
  fun r c => blockEntry (S.point true q u r.1 r.2) (S.point false q u c.1 c.2)

theorem rank_le_nominal (S : Axes) (q u : ℕ) :
    (packet S q u).rank ≤ min (size S true q u) (size S false q u) := by
  refine le_min ((packet S q u).rank_le_card_height.trans_eq (card_axis ..))
    ((packet S q u).rank_le_card_width.trans_eq (card_axis ..))

theorem rank_of_coverage (S : Axes) (s : Source) (q u : ℕ)
    (r : ↥(blockRows s.m q ((u : ℤ)-s.J)) → Axis S true q u)
    (c : ↥(blockCols s q ((u : ℤ)-s.J)) → Axis S false q u)
    (hr : ∀ i, S.point true q u (r i).1 (r i).2 = i.val)
    (hc : ∀ i, S.point false q u (c i).1 (c i).2 = i.val) :
    (blockMatrix s q ((u : ℤ)-s.J)).rank ≤ (packet S q u).rank := by
  have h : blockMatrix s q ((u : ℤ)-s.J) = (packet S q u).submatrix r c := by
    apply Matrix.ext
    intro i j
    change blockEntry i.val j.val = blockEntry (S.point true q u (r i).1 (r i).2)
      (S.point false q u (c j).1 (c j).2)
    rw [hr,hc]
  rw [h]
  exact Matrix.rank_submatrix_le _ _ _

private def orientedEntry (S : Axes) (side : Bool) (q u i k b t : ℕ) : ℤ :=
  if side then entryZ (S.point true q u b t) (S.point false q u i k)
  else entryZ (S.point true q u i k) (S.point false q u b t)

private def oriented (S : Axes) (side : Bool) (q u : ℕ) :
    Matrix (Axis S (!side) q u) (Axis S side q u) (ZMod CJ0.p) :=
  fun r c => (orientedEntry S side q u r.1 r.2 c.1 c.2 : ZMod CJ0.p)

theorem rank_oriented (S : Axes) (side : Bool) (q u : ℕ) : (oriented S side q u).rank = (packet S q u).rank := by
  cases side
  · congr 1
    ext r c
    exact entryZ_cast ..
  · exact (congrArg Matrix.rank (show oriented S true q u = (packet S q u).transpose by
      ext r c; exact entryZ_cast ..)).trans (Matrix.rank_transpose _)

structure Witness where
  onRows : Bool
  cap : ℕ
  free : List (ℕ × ℕ)
  vectors : List (List (ℕ × ℕ × ℤ))

private def decode (S : Axes) (side : Bool) (q u i k : ℕ) : Option (Axis S side q u) :=
  if hi : i < S.outer side q then
    if hk : k < S.fiber side q u i then some ⟨⟨i,hi⟩,⟨k,hk⟩⟩ else none
  else none

def Guard (S : Axes) (q u : ℕ) (w : Witness) : Prop :=
  size S w.onRows q u ≤ w.cap+w.free.length ∧
  ∀ j : Fin w.free.length, w.free[j].1 < S.outer w.onRows q ∧
    w.free[j].2 < S.fiber w.onRows q u w.free[j].1
instance (S : Axes) (q u : ℕ) (w : Witness) : Decidable (Guard S q u w) := by unfold Guard; infer_instance

def freeAxis (S : Axes) (q u : ℕ) (w : Witness) (hw : Guard S q u w) (j : Fin w.free.length) : Axis S w.onRows q u :=
  ⟨⟨w.free[j].1,(hw.2 j).1⟩,⟨w.free[j].2,(hw.2 j).2⟩⟩

def atoms (S : Axes) (q u : ℕ) (w : Witness) (j : Fin w.free.length) : List (Axis S w.onRows q u × ℤ) :=
  (w.vectors[j.val]?.getD []).filterMap fun (i,k,v) => (decode S w.onRows q u i k).map (fun c => (c,v))

def atCoeff {ι : Type*} [DecidableEq ι] (xs : List (ι × ℤ)) (i : ι) : ℤ :=
  (xs.map fun (j,v) => if i = j then v else 0).sum

def Dots (S : Axes) (q u : ℕ) (w : Witness) : Prop :=
  ∀ (r : Axis S (!w.onRows) q u) (j : Fin w.free.length),
    ((atoms S q u w j).map (fun (c,v) => orientedEntry S w.onRows q u r.1 r.2 c.1 c.2*v)).sum % (CJ0.p : ℤ) = 0
instance (S : Axes) (q u : ℕ) (w : Witness) : Decidable (Dots S q u w) := by unfold Dots; infer_instance

def Identity (S : Axes) (q u : ℕ) (w : Witness) (hw : Guard S q u w) : Prop :=
  ∀ i j : Fin w.free.length, atCoeff (atoms S q u w j) (freeAxis S q u w hw i) = if i=j then 1 else 0
instance (S : Axes) (q u : ℕ) (w : Witness) (hw : Guard S q u w) : Decidable (Identity S q u w hw) := by unfold Identity; infer_instance

theorem sum_atoms {ι : Type*} [Fintype ι] [DecidableEq ι] (xs : List (ι × ℤ)) (f : ι → ℤ) :
    (∑ i, (f i : ZMod CJ0.p) * (atCoeff xs i : ZMod CJ0.p)) =
      (((xs.map fun (i,v) => f i*v).sum : ℤ) : ZMod CJ0.p) := by
  induction xs with
  | nil => simp [atCoeff]
  | cons x xs ih =>
    rcases x with ⟨j,v⟩
    have he (i : ι) : atCoeff ((j,v)::xs) i = (if i=j then v else 0)+atCoeff xs i := rfl
    calc
      _ = (∑ i, if i=j then (f i : ZMod CJ0.p)*(v : ZMod CJ0.p) else 0) +
          ∑ i, (f i : ZMod CJ0.p)*(atCoeff xs i : ZMod CJ0.p) := by
        simp only [he, Int.cast_add, mul_add, sum_add_distrib]
        congr 1
        apply sum_congr rfl
        intro i _
        by_cases h : i=j <;> simp [h]
      _ = _ := by simp [ih, Finset.sum_ite_eq']

theorem rank_witness (S : Axes) (q u : ℕ) (w : Witness) (hw : Guard S q u w)
    (hd : Dots S q u w) (hi : Identity S q u w hw) : (packet S q u).rank ≤ w.cap := by
  let V : Matrix (Axis S w.onRows q u) (Fin w.free.length) (ZMod CJ0.p) :=
    fun c j => (atCoeff (atoms S q u w j) c : ZMod CJ0.p)
  have hm : oriented S w.onRows q u * V = 0 := by
    ext r j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    change (∑ c, (orientedEntry S w.onRows q u r.1 r.2 c.1 c.2 : ZMod CJ0.p) *
      (atCoeff (atoms S q u w j) c : ZMod CJ0.p)) = 0
    rw [sum_atoms, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.dvd_of_emod_eq_zero (hd r j)
  have hf : V.submatrix (freeAxis S q u w hw) id = 1 := by
    ext i j
    change (atCoeff (atoms S q u w j) (freeAxis S q u w hw i) : ZMod CJ0.p) = _
    rw [hi i j]
    by_cases h : i=j <;> simp [Matrix.one_apply,h]
  have hr := right_witness (oriented S w.onRows q u) V (freeAxis S q u w hw) hm hf
  rw [rank_oriented,card_axis] at hr
  exact Nat.le_of_add_le_add_right (hr.trans hw.1)

end CurveListSparsePackets
