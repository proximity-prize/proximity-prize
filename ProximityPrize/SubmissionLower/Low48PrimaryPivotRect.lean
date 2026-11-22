import ProximityPrize.SubmissionLower.Low48PrimaryPivotCore
import ProximityPrize.SubmissionLower.PortLowBase
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Intervals

set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false

namespace Low48PrimaryPivot
open K1_13 (Geom)
open K1_13_2 K1_13_2_3 Finset
open scoped BigOperators

/-- Twice the triangular number of the positive part of an integer. -/
def twiceTri (x : ℤ) : ℤ := max 0 x * (max 0 x + 1)

private theorem tri_step (x : ℤ) : twiceTri (x+1) - twiceTri x = 2 * max 0 (x+1) := by
  by_cases hx : 0 ≤ x
  · simp only [twiceTri, max_eq_right hx, max_eq_right (show 0 ≤ x+1 by omega)]
    ring
  · have h1 : x+1 ≤ 0 := by omega
    simp [twiceTri, max_eq_left h1, max_eq_left (le_of_not_ge hx)]

private theorem sum_ramp (a b k : ℤ) (h : a ≤ b) :
    (∑ l ∈ Ico a b, 2 * max 0 (l-k+1)) = twiceTri (b-k) - twiceTri (a-k) := by
  rw [Int.Ico_eq_finset_map, sum_map]
  let n := (b-a).toNat
  have hn : a+(n : ℤ) = b := by dsimp [n]; omega
  have eq (l : ℕ) :
      2 * max 0 (a+(l : ℤ)-k+1) =
        twiceTri (a+((l+1 : ℕ) : ℤ)-k) - twiceTri (a+(l : ℤ)-k) := by
    push_cast
    rw [show a+((l : ℤ)+1)-k = a+(l : ℤ)-k+1 by ring, tri_step]
  change (∑ l ∈ range n, 2 * max 0 (a+(l : ℤ)-k+1)) = _
  simp_rw [eq]
  rw [sum_range_sub (fun l : ℕ => twiceTri (a+(l : ℤ)-k)) n, hn]
  simp

private theorem cut_card (q0 q1 l k : ℤ) (hq : q0 ≤ q1) :
    (((Ico q0 q1).filter (fun q => k ≤ l-q)).card : ℤ) =
      max 0 (l-k+1-q0) - max 0 (l-k+1-q1) := by
  have eq : (Ico q0 q1).filter (fun q => k ≤ l-q) = Ico q0 (min q1 (l-k+1)) := by
    ext q
    simp only [mem_filter, mem_Ico, lt_min_iff]
    omega
  rw [eq, Int.card_Ico]
  omega

def cutFee (l0 l1 q0 q1 k : ℤ) : ℤ :=
  twiceTri (l1-k-q0) - twiceTri (l0-k-q0) -
    (twiceTri (l1-k-q1) - twiceTri (l0-k-q1))

private theorem sum_cut (l0 l1 q0 q1 k : ℤ) (hl : l0 ≤ l1) (hq : q0 ≤ q1) :
    2 * ↑(((Ico l0 l1).product (Ico q0 q1)).filter (fun x => k ≤ x.1-x.2)).card =
      cutFee l0 l1 q0 q1 k := by
  rw [natCast_card_filter (fun x : ℤ × ℤ => k ≤ x.1-x.2)]
  have hprod :
      (∑ x ∈ (Ico l0 l1).product (Ico q0 q1), if k ≤ x.1-x.2 then (1 : ℤ) else 0) =
        ∑ l ∈ Ico l0 l1, ∑ q ∈ Ico q0 q1, if k ≤ l-q then (1 : ℤ) else 0 :=
    sum_product (Ico l0 l1) (Ico q0 q1) (fun x : ℤ × ℤ => if k ≤ x.1-x.2 then (1 : ℤ) else 0)
  rw [hprod]
  unfold cutFee
  have eq (l : ℤ) :
      (∑ q ∈ Ico q0 q1, (if k ≤ l-q then (1 : ℤ) else 0)) =
        max 0 (l-k+1-q0) - max 0 (l-k+1-q1) := by
    rw [← cut_card q0 q1 l k hq, natCast_card_filter]
  simp_rw [eq, mul_sum, mul_sub]
  rw [sum_sub_distrib]
  have ramp (q : ℤ) : (∑ l ∈ Ico l0 l1, 2 * max 0 (l-k+1-q)) =
      twiceTri (l1-k-q) - twiceTri (l0-k-q) := by
    have h (l : ℤ) : l-k+1-q = l-(k+q)+1 := by ring
    simp_rw [h]
    simpa only [sub_add_eq_sub_sub] using sum_ramp l0 l1 (k+q) hl
  rw [ramp, ramp]

def fee2 (l0 l1 q0 q1 a b : ℤ) : ℤ :=
  cutFee l0 l1 q0 q1 a - cutFee l0 l1 q0 q1 b

private theorem band_card (l0 l1 q0 q1 a b : ℤ)
    (hl : l0 ≤ l1) (hq : q0 ≤ q1) (hab : a ≤ b) :
    2 * ↑(((Ico l0 l1).product (Ico q0 q1)).filter
      (fun x => a ≤ x.1-x.2 ∧ x.1-x.2 < b)).card = fee2 l0 l1 q0 q1 a b := by
  let S := (Ico l0 l1).product (Ico q0 q1)
  let A := S.filter (fun x => a ≤ x.1-x.2 ∧ x.1-x.2 < b)
  let B := S.filter (fun x => b ≤ x.1-x.2)
  have disjoint : Disjoint A B := by
    refine disjoint_left.mpr ?_
    intro x hx hy
    have ha := (mem_filter.mp hx).2.2
    have hb := (mem_filter.mp hy).2
    omega
  have union : A ∪ B = S.filter (fun x => a ≤ x.1-x.2) := by
    ext x
    by_cases h : x ∈ S
    · simp only [A, B, mem_union, mem_filter, h, true_and]
      omega
    · simp [A, B, h]
  have hcard : (A.card : ℤ) + B.card = ((S.filter (fun x => a ≤ x.1-x.2)).card : ℤ) := by
    exact_mod_cast ((card_union_of_disjoint disjoint).symm.trans (congrArg card union))
  have hA := sum_cut l0 l1 q0 q1 a hl hq
  have hB := sum_cut l0 l1 q0 q1 b hl hq
  change 2 * (A.card : ℤ) = _
  change 2 * ((S.filter (fun x => a ≤ x.1-x.2)).card : ℤ) = _ at hA
  change 2 * (B.card : ℤ) = _ at hB
  unfold fee2
  omega

def indexLo (w : Window) : ℤ := 1650-w.offsetHi
def indexHi (w : Window) (p : Triple) : ℤ :=
  max (indexLo w) (min (1651-(w.offsetLo : ℤ)) (p.index+1 : ℤ))
def orderHi (w : Window) : ℤ := 4651-w.diagonalLo
def orderLo (w : Window) (p : Triple) : ℤ :=
  min (orderHi w) (max (4650-(w.diagonalHi : ℤ)) (p.contact+1 : ℤ))

def columnFee2 (w : Window) (p : Triple) : ℤ :=
  if p.index ≤ 1650 then
    fee2 (indexLo w) (indexHi w p) (orderLo w p) (orderHi w)
      ((w.gradeLo : ℤ)-3000) ((w.gradeHi : ℤ)-3000)
  else 0

def debit (w : Window) : ℕ :=
  ∑ i : BlockIndex, if w.Contains i then ∑ q : Column, charge i q else 0

private theorem column_le_fee_on (w : Window) (hgrade : w.gradeLo ≤ w.gradeHi)
    (q : Column) (rows : Finset BlockIndex) :
    2 * ↑(∑ i ∈ rows, if w.Contains i then charge i q else 0) ≤
      columnFee2 w (columnPoint q) := by
  let p := columnPoint q
  by_cases hp : p.index ≤ 1650
  · rw [columnFee2, ite_eq_left hp]
    let S := rows.filter (fun i => w.Contains i ∧ pays i q)
    let R := ((Ico (indexLo w) (indexHi w p)).product (Ico (orderLo w p) (orderHi w))).filter
      (fun x => (w.gradeLo : ℤ)-3000 ≤ x.1-x.2 ∧ x.1-x.2 < (w.gradeHi : ℤ)-3000)
    have hsum : (∑ i ∈ rows, if w.Contains i then charge i q else 0) = S.card := by
      calc
        _ = ∑ i ∈ rows, if w.Contains i ∧ pays i q then 1 else 0 := by
          apply sum_congr rfl
          intro i _
          by_cases hw : w.Contains i <;> simp [charge,hw]
        _ = _ := sum_boole _ _
    have hc : S.card ≤ R.card := by
      let f (i : BlockIndex) : ℤ × ℤ := (1650-i.2.val,4650-(i.1.val : ℤ)-i.2.val)
      refine card_le_card_of_injOn f ?_ ?_
      · intro i hi
        change i ∈ rows.filter (fun i => w.Contains i ∧ pays i q) at hi
        have hm : w.Contains i ∧ pays i q :=
          ((Finset.mem_filter (s := rows)
            (p := fun i => w.Contains i ∧ pays i q)).mp hi).2
        obtain ⟨hw,hpays⟩ := hm
        obtain ⟨hgl,hgh,hol,hoh,hdl,hdh⟩ := hw
        have hpos : 0 ≤ (initialFlag i).order := by
          dsimp [pays,p] at hpays
          have h := hpays.2.2
          omega
        obtain ⟨_, hidx, hcontact⟩ := hpays
        change -offset i ≤ (p.index : ℤ) at hidx
        change p.contact < (initialFlag i).order.toNat at hcontact
        change f i ∈ R
        simp only [initialFlag, offset] at hidx hcontact hpos
        apply Finset.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · change f i ∈ (Ico (indexLo w) (indexHi w p)) ×ˢ (Ico (orderLo w p) (orderHi w))
          rw [Finset.mem_product]
          simp only [mem_Ico, f, indexLo, indexHi, orderLo, orderHi]
          omega
        · dsimp [f]
          omega
      · intro i _ j _ he
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        simp only [f] at h1 h2
        exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    have hf := band_card (indexLo w) (indexHi w p) (orderLo w p) (orderHi w)
      ((w.gradeLo : ℤ)-3000) ((w.gradeHi : ℤ)-3000)
      (le_max_left _ _) (min_le_left _ _) (by omega)
    change 2 * (R.card : ℤ) = _ at hf
    rw [hsum, ← hf]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (by decide)
  · rw [columnFee2, ite_eq_right hp]
    have hz (i : BlockIndex) : charge i q = 0 := by
      unfold charge pays
      simp [p,hp]
    simp [hz]

private theorem debit_le_fee_on (w : Window) (hgrade : w.gradeLo ≤ w.gradeHi)
    (rows : Finset BlockIndex) (columns : Finset Column) :
    2 * ↑(∑ i ∈ rows, if w.Contains i then ∑ q ∈ columns, charge i q else 0) ≤
      ∑ q ∈ columns, columnFee2 w (columnPoint q) := by
  have h (i : BlockIndex) :
      (if w.Contains i then ∑ q ∈ columns, charge i q else 0) =
        ∑ q ∈ columns, if w.Contains i then charge i q else 0 := by
    split <;> simp [*]
  simp_rw [h]
  rw [sum_comm]
  push_cast
  rw [mul_sum]
  apply sum_le_sum
  intro q _
  have hq := column_le_fee_on w hgrade q rows
  push_cast at hq
  exact hq

theorem debit_le_fee (w : Window) (hgrade : w.gradeLo ≤ w.gradeHi) :
    2 * (debit w : ℤ) ≤ ∑ q : Column, columnFee2 w (columnPoint q) :=
  debit_le_fee_on w hgrade univ univ

#print axioms debit_le_fee
end Low48PrimaryPivot
