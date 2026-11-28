import ProximityPrize.SubmissionLower.Z6970ExpandedRankRegion
import ProximityPrize.SubmissionLower.Wide50EulerPrimaryBlock

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ExpandedTaper6970
open K1_13_2 (Flag residualFlag factorFlag)
open K1_13_2_3 (Powers)
open Wide50EulerPrimary (oldCountI kernelLowerI oldCount_eq kernelLower_eq)
open scoped BigOperators

def valuePower (q a : ℕ) : ℕ :=
  let d := min q (cap q)
  if 3514 ≤ q then min d (3000+d-(q+4*a)) else 0

def rowFlag (q a : ℕ) : Flag :=
  ⟨(min q (cap q) : ℕ), -((a : ℤ)-1679), 1679, 500, 3000-(q : ℤ)-((a : ℤ)-1679)⟩

def activeRowFlag (q a : ℕ) : Flag :=
  {(rowFlag q a) with upper := min 1679 (2999-((a : ℤ)-1679))}

def remainderCell (q a : ℕ) : ℕ :=
  let F := rowFlag q a
  if F.order ≤ 0 then 0 else
    let C := oldCountI (activeRowFlag q a)
    let K := max 0 (max (kernelLowerI F)
      (kernelLowerI {F with degree := F.degree - valuePower q a}))
    (min C (oldCountI F-K)).toNat

private theorem rowFlag_eq (i : BlockIndex) :
    rowFlag i.1.val i.2.val = initialFlag (cap i.1.val) i := rfl

private theorem activeRowFlag_eq (i : BlockIndex) :
    activeRowFlag i.1.val i.2.val = activeFlag (cap i.1.val) i := rfl

private theorem stripValue (F : Flag) (a : ℕ) :
    residualFlag F (Powers.expand ⟨a,0,0⟩) = {F with degree := F.degree-(a : ℤ)} := by
  simp [residualFlag, factorFlag, Powers.expand, Fin.sum_univ_succ, sub_sub]

theorem remainderCell_eq (i : BlockIndex) :
    remainderCell i.1.val i.2.val = bound (cap i.1.val) i (power i) := by
  let F := initialFlag (cap i.1.val) i
  have hpow : power i = Powers.expand ⟨valuePower i.1.val i.2.val,0,0⟩ := rfl
  have hstrip := stripValue F (valuePower i.1.val i.2.val)
  unfold remainderCell bound
  simp only [rowFlag_eq i,activeRowFlag_eq i,oldCount_eq,kernelLower_eq,hpow]
  change _ = (if F.order ≤ 0 then 0 else
    (min (oldCountI (activeFlag (cap i.1.val) i))
      (oldCountI F - max 0 (max (kernelLowerI F)
        (kernelLowerI (residualFlag F (Powers.expand ⟨valuePower i.1.val i.2.val,0,0⟩)))))).toNat)
  rw [hstrip]
  rfl

def remainderRow (q : ℕ) : ℕ :=
  if 1679 ≤ q ∧ q < 3514 then 0 else
    TaperBudget.sumRange (remainderCell q) (4679-q)

theorem remainderRow_eq (q : Fin 4025) :
    remainderRow q.val = ∑ a : Fin 4679,
      if plateau (q,a) then 0 else bound (cap q.val) (q,a) (power (q,a)) := by
  unfold remainderRow
  by_cases hq : 1679 ≤ q.val ∧ q.val < 3514
  · simp [hq,plateau]
  · rw [if_neg hq]
    let m := 4679 - q.val
    have hm : m ≤ 4679 := Nat.sub_le _ _
    have hz (a : ℕ) (ha : m ≤ a) : remainderCell q.val a = 0 := by
      unfold remainderCell rowFlag
      dsimp only
      have h : ((4679 : ℤ)-q.val-a) ≤ 0 := by dsimp [m] at ha; omega
      simp [show (3000 : ℤ) - q.val - ((a : ℤ)-1679) ≤ 0 by omega]
    calc
      TaperBudget.sumRange (remainderCell q.val) m =
          TaperBudget.sumRange (remainderCell q.val) 4679 := by
        simp only [TaperBudget.sumRange_eq]
        symm
        calc
          _ = ∑ a ∈ Finset.range (m+(4679-m)), remainderCell q.val a := by
            rw [show m+(4679-m)=4679 by omega]
          _ = _ := by
            rw [Finset.sum_range_add]
            have he : (∑ a ∈ Finset.range (4679-m), remainderCell q.val (m+a)) = 0 :=
              Finset.sum_eq_zero fun a _ => hz _ (Nat.le_add_right _ _)
            rw [he,add_zero]
      _ = ∑ a : Fin 4679, remainderCell q.val a.val :=
        TaperBudget.sumRange_fin _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        have hn : ¬ plateau (q,a) := hq
        rw [if_neg hn]
        exact remainderCell_eq (q,a)

theorem remainder_total :
    (∑ i : BlockIndex, if plateau i then 0 else bound (cap i.1.val) i (power i)) =
      TaperBudget.sumRange remainderRow 4025 := by
  rw [TaperBudget.sumRange_fin, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  exact (remainderRow_eq q).symm

end ExpandedTaper6970
