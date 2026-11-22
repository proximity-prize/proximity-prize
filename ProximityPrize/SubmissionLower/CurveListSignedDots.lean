import ProximityPrize.SubmissionLower.CurveListSparsePackets

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

namespace CurveListSignedDots
open CJ0 CurveListSparsePackets
open CJ1 (entryZ)
open CurveListPascalCache (chooseFast chooseFast_eq)
open private orientedEntry entryFast_eq from ProximityPrize.SubmissionLower.CurveListSparsePackets

/-- Accumulate each sign in `Nat`; only the final difference needs `Int`. -/
private abbrev Parts := Nat × Nat
private def value (a : Parts) : Int := (a.1 : Int) - a.2

private theorem parity_sign (n : Nat) :
    (-1 : Int)^n = if n % 2 = 0 then 1 else -1 := by
  have h := Nat.mod_add_div n 2
  calc
    _ = (-1 : Int)^(n % 2 + 2 * (n / 2)) := congrArg ((-1 : Int) ^ ·) h.symm
    _ = (-1 : Int)^(n % 2) := by rw [pow_add, pow_mul, show (-1 : Int)^2 = 1 by decide, one_pow, mul_one]
    _ = _ := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

private def signed (positive : Bool) (a : Nat) : Int → Parts
  | .ofNat b => if positive then (a*b, 0) else (0, a*b)
  | .negSucc b => if positive then (0, a*(b+1)) else (a*(b+1), 0)

private theorem signed_eq (positive : Bool) (a : Nat) (v : Int) :
    value (signed positive a v) = (if positive then 1 else -1) * (a : Int) * v := by
  cases positive <;> cases v <;>
    simp [signed, value, Int.negSucc_eq, Nat.cast_mul, Nat.cast_add] <;> ring

private def term (r c : Jet) (v : Int) : Parts :=
  if c.b ≤ r.b ∧ c.c ≤ r.c ∧ r.a + (r.b-c.b) + (r.c-c.c) = c.a then
    signed (decide ((r.c-c.c)%2 = 0)) (chooseFast c.a r.a * chooseFast (c.a-r.a) (r.b-c.b)) v
  else (0,0)

private theorem term_eq (r c : Jet) (v : Int) : value (term r c v) = entryZ r c * v := by
  by_cases hg : c.b ≤ r.b ∧ c.c ≤ r.c ∧ r.a + (r.b-c.b) + (r.c-c.c) = c.a
  · simp only [term, entryZ, if_pos hg, signed_eq, chooseFast_eq, Nat.cast_mul, parity_sign]
    by_cases h : (r.c-c.c)%2 = 0 <;> simp [h, mul_assoc]
  · simp [term, entryZ, hg, value]

private def orientedTerm (S : Axes) (side : Bool) (q u i k b t : Nat) (v : Int) : Parts :=
  if side then term (S.point true q u b t) (S.point false q u i k) v
  else term (S.point true q u i k) (S.point false q u b t) v

private theorem orientedTerm_eq (S : Axes) (side : Bool) (q u i k b t : Nat) (v : Int) :
    value (orientedTerm S side q u i k b t v) = orientedEntry S side q u i k b t * v := by
  cases side <;> simp [orientedTerm, orientedEntry, term_eq, entryFast_eq]

private def sumParts {α : Type} (f : α → Parts) : List α → Parts
  | [] => (0,0)
  | x::xs =>
    let a := f x
    let b := sumParts f xs
    (a.1+b.1, a.2+b.2)

private theorem sumParts_eq {α : Type} (f : α → Parts) (xs : List α) :
    value (sumParts f xs) = (xs.map fun x => value (f x)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    simp only [sumParts, value, Nat.cast_add]
    ring

def FastDots (S : Axes) (q u : Nat) (w : Witness) : Prop :=
  ∀ (r : Axis S (!w.onRows) q u) (j : Fin w.free.length),
    value (sumParts (fun (c,v) => orientedTerm S w.onRows q u r.1 r.2 c.1 c.2 v)
      (atoms S q u w j)) % (CJ0.p : Int) = 0

instance (S : Axes) (q u : Nat) (w : Witness) : Decidable (FastDots S q u w) := by
  unfold FastDots
  infer_instance

theorem dots_of_fast (S : Axes) (q u : Nat) (w : Witness) (h : FastDots S q u w) : Dots S q u w := by
  intro r j
  simpa only [sumParts_eq, orientedTerm_eq] using h r j

theorem rank_witness_fast (S : Axes) (q u : Nat) (w : Witness) (hw : Guard S q u w)
    (hd : FastDots S q u w) (hi : Identity S q u w hw) : (packet S q u).rank ≤ w.cap :=
  rank_witness S q u w hw (dots_of_fast S q u w hd) hi

end CurveListSignedDots
