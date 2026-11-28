import ProximityPrize.SubmissionLower.Z6970PlateauGain
import ProximityPrize.SubmissionLower.Z6970ExpandedTriangle

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace ExpandedPlateauSum6970
open ExpandedPivotOpt6970 (Column Triple columnPoint)
open ExpandedTaper6970 (triangle)
open ExpandedPlateauIntegral6970 (value delta receipt_eq)
open KoalaLinearWindow (Span)
open Finset
open scoped BigOperators

private def splitIndex : Fin 3 × Fin 560 ≃ Fin 1680 where
  toFun q := ⟨3*q.2.val+q.1.val,by have := q.1.isLt; have := q.2.isLt; omega⟩
  invFun b := ⟨⟨b.val%3,by omega⟩,⟨b.val/3,by have := b.isLt; omega⟩⟩
  left_inv q := by
    obtain ⟨r,t⟩ := q
    apply Prod.ext <;> apply Fin.ext <;> dsimp <;> have := r.isLt <;> omega
  right_inv b := by apply Fin.ext; dsimp; omega

private theorem span_ok (c f r x : ℕ) :
    x < spanLength c f r ↔ 3*x+r+2*c+3*f ≤ 1679 := by
  unfold spanLength
  omega

private theorem cut_sum (n cap : ℕ) (g : ℕ → ℤ) (hn : n ≤ cap) :
    (∑ x : Fin cap, if x.val < n then g x.val else 0) = ∑ x ∈ range n, g x := by
  rw [Fin.sum_univ_eq_sum_range (fun x => if x < n then g x else 0)]
  have hcut : (range cap).filter (fun i => i < n) = range n := by
    ext i
    simp only [mem_filter,mem_range]
    omega
  rw [← sum_filter, hcut]

private theorem residue_eq (f : Fin 501) (c : Fin 840) (r : Fin 3) :
    (∑ x : Fin 560, triangle (f,c,splitIndex (r,x))) = strip f.val c.val r.val := by
  let n := spanLength c.val f.val r.val
  let L := lines c.val f.val r.val
  let g (x : ℕ) := delta (value (L.1.at x) x L.2)
  have hn : n ≤ 560 := by dsimp [n,spanLength]; omega
  have atx (x : Fin 560) : triangle (f,c,splitIndex (r,x)) =
      if x.val < n then g x.val else 0 := by
    have hidx : (columnPoint (f,c,splitIndex (r,x))).index = 3*x.val+r.val+2*c.val+3*f.val := rfl
    by_cases h : x.val < n
    · have bound := (span_ok c.val f.val r.val x.val).mp h
      have fee := exact_argument c.val f.val r.val x.val r.isLt (by have := f.isLt;omega) bound
      let P : Triple := columnPoint (f,c,splitIndex (r,x))
      change 3000+(P.index : ℤ)-(P.contact : ℤ)-1679 = _ at fee
      rw [if_pos h]
      unfold triangle
      dsimp only
      rw [if_pos (hidx.trans_le bound)]
      change Low48PrimaryPivot.twiceTri (3000+(P.index:ℤ)-(P.contact:ℤ)-1679) -
        Low48PrimaryPivot.twiceTri (3000+(P.index:ℤ)-(P.contact:ℤ)-3514) = _
      have he : 3000+(P.index:ℤ)-(P.contact:ℤ)-3514 =
          (3000+(P.index:ℤ)-(P.contact:ℤ)-1679)-1835 := by ring
      rw [he,fee]
      rfl
    · have high : ¬ (columnPoint (f,c,splitIndex (r,x))).index ≤ 1679 := by
        rw [hidx,←span_ok]
        exact h
      simp [triangle,high,h]
  rw [sum_congr rfl (fun x _ => atx x), cut_sum n 560 g hn]
  unfold strip
  by_cases hz : n = 0
  · simp only [show spanLength c.val f.val r.val = 0 from hz,ite_true]
    simp [hz]
  · rw [if_neg hz,receipt_eq,Span.sum_eq_range]
    simp [n,L,g,Span.size]

private theorem inner_eq (f : Fin 501) (c : Fin 840) :
    (∑ b : Fin 1680, triangle (f,c,b)) = column f.val c.val := by
  rw [←splitIndex.sum_comp (fun b => triangle (f,c,b)),Fintype.sum_prod_type]
  simp_rw [residue_eq]
  simp [Fin.sum_univ_succ,column,add_assoc]

theorem global_sum : (∑ q : Column, triangle q) = chunk 0 501 := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type,inner_eq]
  have outer (f : Fin 501) : (∑ c : Fin 840, column f.val c.val) = row f.val := by
    let n := (1681-3*f.val)/2
    have hn : n ≤ 840 := by dsimp [n]; omega
    have elem (c : Fin 840) : column f.val c.val = if c.val < n then column f.val c.val else 0 := by
      split
      · rfl
      · rename_i h
        have zero (r : ℕ) : spanLength c.val f.val r = 0 := by
          dsimp [n] at h
          unfold spanLength
          omega
        simp [column,strip,zero]
    rw [sum_congr rfl (fun c _ => elem c),cut_sum n 840 (column f.val) hn]
    exact (sumN_eq (column f.val) n).symm
  simp_rw [outer]
  rw [Fin.sum_univ_eq_sum_range (fun x => row x)]
  simp [chunk,sumN_eq]

end ExpandedPlateauSum6970
