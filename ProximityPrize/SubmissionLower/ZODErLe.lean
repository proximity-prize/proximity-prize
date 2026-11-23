import ProximityPrize.SubmissionLower.ZrgYIVd
import ProximityPrize.SubmissionLower.ZAOw7gb
set_option Elab.async false
set_option maxHeartbeats 1300000
section
set_option autoImplicit true
set_option maxRecDepth 800
namespace qzVScmb
open P5 (p)
open P5_7_2 (fO)
open q7F2qKe (originCutter originBudget aur)


open Finset
open private au9 from ProximityPrize.SubmissionLower.ZAOw7gb
private theorem active_small (b:fO) (k :Fin 4) :q7F2qKe.BC b k<p :=
  (au9 b k).trans_lt (by fin_cases b <;> fin_cases k <;> decide)
theorem guards (b:fO) :Guards b where
  anchor_mem:=stage_0 b
  anchor_small:=stage_small b
  staged_ode := fun _=>staged
  fibre_J:= by
    intro i hi e
    cases e
    · by_cases hm:i<last b
      · change (originCutter b i).J≤(originCutter b i).B
        rw [originCutter,List.getElem?_eq_getElem hm]
        exact (intro_guard (List.getElem_mem hm)).1
      · have he :i=last b:=le_antisymm hi (Nat.le_of_not_gt hm)
        subst i
        exact (final_valid b).1
    · exact budget_J b i
  rescue_weight:= by
    obtain ⟨_,hJ,hBJ,hB,hU⟩:=final_valid b
    exact matrix_mono (s :=aur (originBudget b (last b)))
      (t:=originCutter b (last b)) hJ hBJ hB hU
  bq6:=active_small b
end qzVScmb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qzVScmb
noncomputable section
open Polynomial Finset
open scoped Classical BigOperators

open P5_7_2 (fO)
open q7F2qKe (origins originBudget originCutter fibreShape)
open cu (Jet)

open pI (oU)

open akZ (btm yE ajz cN5)
private theorem aby {b:fO} {f q:Jet}
    (h : ∀ j,yE f j≤originBudget b (last b) j) (e :Bool)
    (hc:oU q (if e then btm f else aOm b f)) :
    oU q (fibreShape b (last b) e) := by
  cases e with
  | false =>
    have hh:=List.getElem?_length (P5_7_2.introduction b)
    simp only [Bool.false_eq_true,ite_false,fibreShape,originCutter,hh] at hc ⊢
    intro j i hn
    obtain ⟨hB,hJ,hU⟩:=hc j i hn
    exact ⟨hB.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (h 0) 1)) _),
      hJ.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (h 1) 1)) _),
      hU.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (h 2)) _)⟩
  | true =>
    intro j i hn
    obtain ⟨hB,hJ,hU⟩:=hc j i hn
    exact ⟨hB.trans (h 0),hJ.trans (h 1),hU.trans (h 2)⟩
private theorem tail_partition {b:fO} {D T:Finset Jet} (hT:T⊆D) (o:Jet→Origin b)
    (h : ∀ i≤last b,∀ j,
      ajz (D.filter fun f=>i≤(o f).val) j≤originBudget b i j)
    (i:ℕ) (hi:i∈origins b) (j:Fin 3) :
    ∑ n∈(origins b).filter (i ≤ ·),∑ f∈T.filter (fun f=>(o f).val=n),yE f j ≤
      originBudget b i j:= by
  let E :=T.filter fun f=>i≤(o f).val
  have hm : ∀ f∈E,(o f).val∈(origins b).filter (i ≤ ·) := fun f hf =>
    mem_filter.mpr ⟨mem_range.mpr (o f).isLt,(mem_filter.mp hf).2⟩
  refine le_trans ?_ ((cN5 (filter_subset_filter _ hT) j).trans
    (h i (Nat.le_of_lt_succ (mem_range.mp hi)) j))
  change _ ≤ ∑ f∈E,yE f j
  rw [← sum_fiberwise_of_maps_to hm]
  apply sum_le_sum
  intro n hn
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _=>Nat.zero_le _)
  intro f hf
  obtain ⟨hf,he⟩:=mem_filter.mp hf
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨hf,he ▸ (mem_filter.mp hn).2⟩,he⟩
end
end qzVScmb
end
