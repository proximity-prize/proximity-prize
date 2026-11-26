import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-! Soundness of finite rational LP certificates used by the 6402 price cover.
All profile coordinates are nonnegative. Original equalities are supplied as
two inequalities, so every stored multiplier is nonnegative. -/

namespace ProximityPrize.SubmissionBinaryLower.B6402LinearCertificate
open scoped BigOperators
set_option autoImplicit false

structure Row where
  entries : List (ℕ × ℚ)
  bound : ℚ
  deriving Inhabited,Repr

def coeff (r : Row) (i : ℕ) : ℚ :=
  (r.entries.map fun p => if p.1=i then p.2 else 0).sum

def dot {n : ℕ} (f x : Fin n → ℚ) : ℚ := ∑ j, f j*x j

def lhs {n : ℕ} (r : Row) (x : Fin n → ℚ) : ℚ := dot (fun j => coeff r j.val) x

abbrev Weights := List (ℕ × ℚ)

def dualCoeff (src : Array Row) (ws : Weights) (j : ℕ) : ℚ :=
  (ws.map fun w => w.2 * coeff (src[w.1]?.getD ⟨[],0⟩) j).sum

def rhs (src : Array Row) (ws : Weights) : ℚ :=
  (ws.map fun w => w.2 * (src[w.1]?.getD ⟨[],0⟩).bound).sum

def certifies (n : ℕ) (src : Array Row) (ws : Weights) (target : Row) (strict : Bool) : Bool :=
  ws.all (fun w => decide (0≤w.2)) &&
  decide (∀ j : Fin n, coeff target j.val ≤ dualCoeff src ws j.val) &&
  (if strict then decide (rhs src ws < target.bound) else decide (rhs src ws ≤ target.bound))

private theorem accumulated_bound {n : ℕ} (src : Array Row) (ws : Weights) (x : Fin n → ℚ)
    (hn : ∀ w∈ws, 0≤w.2)
    (input : ∀ r∈src.toList, lhs r x ≤ r.bound) :
    dot (fun j => dualCoeff src ws j.val) x ≤ rhs src ws := by
  induction ws with
  | nil => simp [dot,dualCoeff,rhs]
  | cons w rest ih =>
    have tail := ih (fun v hv => hn v (List.mem_cons_of_mem _ hv))
    have hrow : lhs (src[w.1]?.getD ⟨[],0⟩) x ≤ (src[w.1]?.getD ⟨[],0⟩).bound := by
      by_cases hi : w.1<src.size
      · simpa [hi] using input src[w.1] (by simp)
      · simp [Array.getElem?_eq_none (by omega : src.size≤w.1),lhs,dot,coeff]
    have onestep := mul_le_mul_of_nonneg_left hrow (hn w List.mem_cons_self)
    simp only [dualCoeff,rhs,List.map_cons,List.sum_cons] at *
    change (∑ j, (w.2 * coeff (src[w.1]?.getD ⟨[],0⟩) j.val + _) * x j) ≤ _
    simp only [add_mul,Finset.sum_add_distrib,mul_assoc,←Finset.mul_sum]
    exact add_le_add onestep tail

theorem sound {n : ℕ} (src : Array Row) (ws : Weights) (target : Row) (strict : Bool)
    (checked : certifies n src ws target strict = true) (x : Fin n → ℚ)
    (xnonneg : ∀ j, 0≤x j) (input : ∀ r∈src.toList, lhs r x ≤ r.bound) :
    if strict then lhs target x < target.bound else lhs target x ≤ target.bound := by
  unfold certifies at checked
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨hn,hc⟩,hb⟩ := checked
  have h1 : lhs target x ≤ dot (fun j => dualCoeff src ws j.val) x :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hc j) (xnonneg j))
  have h2 := accumulated_bound src ws x hn input
  cases strict <;> simp_all <;> linarith only [h1,h2,hb]

#print axioms sound
end ProximityPrize.SubmissionBinaryLower.B6402LinearCertificate
