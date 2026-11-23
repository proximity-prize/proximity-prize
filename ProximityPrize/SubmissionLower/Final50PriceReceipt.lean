import ProximityPrize.SubmissionLower.Final50PriceLayer

set_option Elab.async false
set_option maxRecDepth 16000

namespace Final50PriceReceipt

open K1_13 (Shape)
open K1_13_8 (fastRemaining)
open Final50Price (layerNeed symbolCount)
open Final50PriceLayer (availableMass)
open scoped BigOperators
open private P3_6_8_1.sumBelow P3_6_8_1.sumBelow_eq P3_6_8_1.sumBelow_add
  from ProximityPrize.SubmissionLower.GoldBranch6N8

private def prefixTerm (b j i : Nat) : Nat :=
  fastRemaining ((i + 1) * b) ((i + 1) * j)

private def checkPrefix (f : Nat → Nat) (first total : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (last, cost) :: rest =>
      (decide (first ≤ last) &&
        decide (total + P3_6_8_1.sumBelow (fun i => f (first + i)) (last - first) = cost)) &&
        checkPrefix f last cost rest

private def prefixValue (n : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (last, cost) :: rest => if n = last then some cost else prefixValue n rest

private theorem prefixValue_eq (f : Nat → Nat) (first total : Nat) (rows : List (Nat × Nat))
    (hfirst : P3_6_8_1.sumBelow f first = total) (valid : checkPrefix f first total rows = true)
    {n cost : Nat} (found : prefixValue n rows = some cost) :
    P3_6_8_1.sumBelow f n = cost := by
  induction rows generalizing first total with
  | nil => simp [prefixValue] at found
  | cons row rest ih =>
    obtain ⟨last, amount⟩ := row
    have h := Bool.and_eq_true_iff.mp valid
    have hcheck := Bool.and_eq_true_iff.mp h.1
    have hle : first ≤ last := of_decide_eq_true hcheck.1
    have hlast : P3_6_8_1.sumBelow f last = amount := by
      conv_lhs => rw [← Nat.add_sub_of_le hle]
      rw [P3_6_8_1.sumBelow_add, hfirst]
      exact of_decide_eq_true hcheck.2
    by_cases hn : n = last
    · subst n
      simpa [show amount = cost from by simpa [prefixValue] using found] using hlast
    · exact ih last amount hlast h.2 (by simpa [prefixValue, hn] using found)

/-- One cumulative result for each used prefix length. Consecutive results
check disjoint ranges of layer terms. -/
structure Prefix (b j : Nat) where
  values : List (Nat × Nat)
  checked : checkPrefix (prefixTerm b j) 0 0 values = true

def makePrefix (b j : Nat) (values : List (Nat × Nat))
    (valid : checkPrefix (prefixTerm b j) 0 0 values = true := by decide +kernel) :
    Prefix b j :=
  ⟨values, valid⟩

def emptyPrefix : Prefix 0 0 := ⟨[], rfl⟩

private def headLength (r : Shape) (l : Nat) : Nat :=
  min l (1650 / r.j)

private def headCost (r : Shape) (table : Prefix r.b r.j) (l : Nat) : Option Nat :=
  if r.j = 0 then some (l * symbolCount)
  else if headLength r l = 0 then some 0
  else prefixValue (headLength r l) table.values

private def tailTerm (r : Shape) (b j l i : Nat) : Nat :=
  fastRemaining (l * r.b + (i + 1) * (r.b + b))
    (l * r.j + (i + 1) * (r.j + j))

private def tailLength (r : Shape) (b j l : Nat) : Nat :=
  min ((4012 - l * r.b) / (r.b + b)) ((1650 - l * r.j) / (r.j + j))

private theorem pastLimit (cap offset stride i : Nat) (positive : 0 < stride)
    (past : (cap - offset) / stride ≤ i) : cap < offset + (i + 1) * stride := by
  have h : cap - offset < (i + 1) * stride := by
    apply Nat.lt_of_not_ge
    intro h
    have h' := (Nat.le_div_iff_mul_le positive).2 h
    omega
  omega

private theorem tailSum_eq (r : Shape) (b j l : Nat) (hb : 0 < b) (hj : 0 < j) :
    (∑ i ∈ Finset.range (1650 / (r.j + j)), tailTerm r b j l i) =
      P3_6_8_1.sumBelow (tailTerm r b j l) (tailLength r b j l) := by
  rw [P3_6_8_1.sumBelow_eq]
  apply K1_13_8.sum_range_truncate
  · intro i hi
    simp only [tailLength, min_le_iff] at hi
    rcases hi with hwidth | hindex
    · have h := pastLimit 4012 (l * r.b) (r.b + b) i (by omega) hwidth
      simp [tailTerm, fastRemaining, Nat.not_le_of_lt h]
    · have h := pastLimit 1650 (l * r.j) (r.j + j) i (by omega) hindex
      simp [tailTerm, fastRemaining, Nat.not_le_of_lt h]
  · exact (min_le_right _ _).trans (Nat.div_le_div_right (Nat.sub_le _ _))

private theorem availableMass_eq (r : Shape) (table : Prefix r.b r.j) (b j l : Nat)
    (hr : r.j = 0 → r.b = 0) (hb : 0 < b) (hj : 0 < j) {cost : Nat}
    (hc : headCost r table l = some cost) :
    availableMass r ⟨b,j,0⟩ l =
      cost + P3_6_8_1.sumBelow (tailTerm r b j l) (tailLength r b j l) := by
  rw [← tailSum_eq r b j l hb hj]
  by_cases hz : r.j = 0
  · have hcost : l * symbolCount = cost := by simpa [headCost, hz] using hc
    simp [Final50PriceLayer.availableMass, K1_13_8.zeroMass, tailTerm, hz, hr hz, hcost]
  · have hhead : P3_6_8_1.sumBelow (prefixTerm r.b r.j) (headLength r l) = cost := by
      by_cases he : headLength r l = 0
      · simpa [P3_6_8_1.sumBelow, he] using (show 0 = cost from by simpa [headCost, hz, he] using hc)
      · exact prefixValue_eq (prefixTerm r.b r.j) 0 0 _ rfl table.checked
          (by simpa [headCost, hz, he] using hc)
    simpa only [Final50PriceLayer.availableMass, K1_13_8.availableMass, hz, ite_false,
      headLength, prefixTerm, tailTerm, P3_6_8_1.sumBelow_eq] using congrArg
      (fun n => n + ∑ i ∈ Finset.range (1650 / (r.j + j)), tailTerm r b j l i) hhead

private def checkTail (f : Nat → Nat) (offset length : Nat) : List Nat → Bool
  | [] => decide (length = 0)
  | v :: vs =>
      decide (P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 48) = v) &&
        checkTail f (offset + min length 48) (length - 48) vs

private theorem checkTail_eq (f : Nat → Nat) (offset length : Nat) (values : List Nat)
    (h : checkTail f offset length values = true) :
    P3_6_8_1.sumBelow f (offset + length) =
      P3_6_8_1.sumBelow f offset + values.sum := by
  induction values generalizing offset length with
  | nil =>
    have hz : length = 0 := of_decide_eq_true h
    simp [hz]
  | cons v vs ih =>
    have hv : P3_6_8_1.sumBelow (fun k => f (offset + k)) (min length 48) = v :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    have hr := (Bool.and_eq_true_iff.mp h).2
    have hs : min length 48 + (length - 48) = length := by omega
    calc
      _ = P3_6_8_1.sumBelow f (offset + min length 48 + (length - 48)) := by rw [Nat.add_assoc, hs]
      _ = P3_6_8_1.sumBelow f (offset + min length 48) + vs.sum := ih _ _ hr
      _ = _ := by rw [P3_6_8_1.sumBelow_add, hv, List.sum_cons, Nat.add_assoc]

def checks (r : Shape) (table : Prefix r.b r.j) (b j l : Nat) (values : List Nat) : Bool :=
  if 0 < b ∧ 0 < j then
    match headCost r table l with
    | some cost => checkTail (tailTerm r b j l) 0 (tailLength r b j l) values &&
        decide (cost + values.sum < layerNeed)
    | none => false
  else false

theorem paid (r : Shape) (table : Prefix r.b r.j) (b j l : Nat) (values : List Nat)
    (hr : r.j = 0 → r.b = 0) (h : checks r table b j l values = true) :
    0 < j ∧ availableMass r ⟨b,j,0⟩ l < layerNeed := by
  by_cases hp : 0 < b ∧ 0 < j
  · cases hc : headCost r table l with
    | none => simp [checks, hp, hc] at h
    | some cost =>
      simp only [checks, if_pos hp, hc, Bool.and_eq_true] at h
      have ht := checkTail_eq (tailTerm r b j l) 0 (tailLength r b j l) values h.1
      simp only [Nat.zero_add, P3_6_8_1.sumBelow] at ht
      refine ⟨hp.2, ?_⟩
      rw [availableMass_eq r table b j l hr hp.1 hp.2 hc, ht]
      exact of_decide_eq_true h.2
  · simp [checks, hp] at h

end Final50PriceReceipt
