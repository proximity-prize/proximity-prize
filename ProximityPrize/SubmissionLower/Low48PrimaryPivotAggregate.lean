import ProximityPrize.SubmissionLower.Low48PrimaryPivotRect
import ProximityPrize.SubmissionLower.KoalaPiecewiseTriangle

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace Low48PrimaryPivot
open K1_13_2_3 Finset KoalaPiecewiseTriangle
open scoped BigOperators

private def contactExpr (c f r : ℕ) : Expr :=
  .lower (.const (1650-(f : ℤ)))
    (.lower (.affine ⟨3300-2*(r : ℤ)-3*(c : ℤ)-4*(f : ℤ),-5⟩)
      (.lower (.affine ⟨4950-3*(r : ℤ)-5*(c : ℤ)-7*(f : ℤ),-9⟩)
        (.affine ⟨1650-(r:ℤ)-(c:ℤ)-(f:ℤ)+(1650-(c:ℤ)-3*(f:ℤ))/2,-3⟩)))

private theorem contactExpr_eq (c f r t : ℕ) (hr : r < 3)
    (h:(Triple.mk (3*t+r) c f).index≤1650) :
    (contactExpr c f r).at t=((Triple.mk (3*t+r) c f).contact:ℤ):=by
  rw [contact_eq]
  simp only [contactExpr,Expr.at,Expr.const,Line.at,zero_mul,add_zero,Triple.room,Triple.index] at *
  omega

private def highIndexExpr (w : Window) (c f r : ℕ) : Expr :=
  .upper (.const (indexLo w)) (.lower (.const (1651-(w.offsetLo : ℤ)))
    (.affine ⟨(r:ℤ)+2*(c:ℤ)+3*(f:ℤ)+1,3⟩))

private def lowOrderExpr (w : Window) (c f r : ℕ) : Expr :=
  .lower (.const (orderHi w))
    (.upper (.const (4650-(w.diagonalHi:ℤ))) (.sub (contactExpr c f r) (.const (-1))))

private def fixedResidue (w : Window) (c f r : ℕ) : ℤ :=
  let n:=(1653-(2*c+3*f+r))/3
  sumBand ⟨indexLo w,orderHi w,(w.gradeLo : ℤ)-3000,(w.gradeHi : ℤ)-3000⟩
    (highIndexExpr w c f r) (lowOrderExpr w c f r) 0 n

private theorem fixedResidue_eq (w : Window) (c f r : ℕ) (hr : r < 3) :
    fixedResidue w c f r =
      ∑ t ∈ range ((1653-(2*c+3*f+r))/3),columnFee2 w ⟨3*t+r,c,f⟩:=by
  unfold fixedResidue
  simp only [sumBand_eq,zero_add]
  apply sum_congr rfl
  intro t ht
  have hn : (Triple.mk (3*t+r) c f).index ≤ 1650 := by
    have h:=mem_range.mp ht
    simp only [Triple.index]
    omega
  have hc:=contactExpr_eq c f r t hr hn
  have hhi : (highIndexExpr w c f r).at (t : ℤ) = indexHi w ⟨3*t+r,c,f⟩ := by
    simp only [Expr.at,Expr.const,Line.at,zero_mul,add_zero,highIndexExpr,indexHi,Triple.index]
    push_cast
    congr 1
    congr 1
    ring
  have hlo : (lowOrderExpr w c f r).at (t : ℤ) = orderLo w ⟨3*t+r,c,f⟩ := by
    simp [lowOrderExpr,Expr.at,Expr.const,Line.at,orderLo,hc]
  rw [hhi,hlo,columnFee2,ite_eq_left hn]
  rfl

private theorem sum_by_three (g : ℕ → ℤ) (u : ℕ) :
    (∑ b ∈ range (u+1), g b) =
      ∑ r ∈ range 3, ∑ t ∈ range ((u+3-r)/3),g (3*t+r):=by
  classical
  let idx (r:ℕ):=range ((u+3-r)/3)
  rw [sum_sigma' (range 3) idx (fun r t => g (3*t+r))]
  let f (b:ℕ) (_:b ∈ range (u+1)):Sigma (fun _:ℕ => ℕ):=⟨b%3,b/3⟩
  refine sum_bij f ?_ ?_ ?_ ?_
  · intro b hb
    have h:=mem_range.mp hb
    simp only [f,idx,mem_sigma,mem_range]
    omega
  · intro a ha b hb he
    have he1:=congrArg Sigma.fst he
    have he2:=congrArg (fun p:Sigma (fun _:ℕ => ℕ) => p.snd) he
    dsimp [f] at he1 he2
    omega
  · rintro ⟨r,t⟩ hx
    simp only [idx,mem_sigma,mem_range] at hx
    refine ⟨3*t+r,mem_range.mpr (by omega), ?_⟩
    have h1:(3*t+r)%3=r:=by omega
    have h2:(3*t+r)/3=t:=by omega
    simp [f,h1,h2]
  · intro b _
    have h:3*(b/3)+b%3=b:=by omega
    simpa only [f,h]

private theorem sum_take {N m : ℕ} (h : m ≤ N) (g : ℕ → ℤ) :
    (∑ i ∈ range N,if i < m then g i else 0) = ∑ i ∈ range m,g i:=by
  rw [← sum_filter]
  congr 1
  ext i
  simp only [mem_filter,mem_range]
  omega

private def atSecond (w : Window) (f c : ℕ) : ℤ :=
  fixedResidue w c f 0+fixedResidue w c f 1+fixedResidue w c f 2

def feeSlab (w : Window) (f : ℕ) : ℤ :=
  ((List.range ((1650-3*f)/2+1)).map (atSecond w f)).sum

def feeCompute (w : Window) : ℤ :=
  ((List.range 551).map (feeSlab w)).sum

private theorem row_eq (w : Window) (f c : ℕ) (hfc : 2*c+3*f ≤ 1650) :
    (∑ b ∈ range 1651,columnFee2 w ⟨b,c,f⟩)=atSecond w f c:=by
  let u:=1650-(2*c+3*f)
  have hz (b : ℕ) :
      columnFee2 w ⟨b,c,f⟩=if b < u+1 then columnFee2 w ⟨b,c,f⟩ else 0:=by
    dsimp [u]
    by_cases h:b+2*c+3*f≤1650
    · rw [ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega), columnFee2, ite_eq_right]
      simpa [Triple.index] using h
  rw [sum_congr rfl (fun b _ => hz b)]
  rw [sum_take (by dsimp [u]; omega),sum_by_three]
  apply Eq.trans _ (show (∑ r ∈ range 3, fixedResidue w c f r) = _ by
    simp [atSecond,sum_range_succ])
  apply sum_congr rfl
  intro r hr
  rw [fixedResidue_eq w c f r (mem_range.mp hr)]
  have he:(u+3-r)/3=(1653-(2*c+3*f+r))/3:=by dsimp [u]; omega
  rw [he]

theorem fee_eq_compute (w : Window) :
    (∑ q:Column,columnFee2 w (columnPoint q))=feeCompute w:=by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [columnPoint]
  rw [Fin.sum_univ_eq_sum_range (fun f : ℕ =>
      ∑ c:Fin 826, ∑ b:Fin 1651,columnFee2 w ⟨b,c,f⟩) 551]
  unfold feeCompute
  change (∑ f ∈ range 551, ∑ c : Fin 826, ∑ b : Fin 1651, columnFee2 w ⟨b,c,f⟩) =
    ∑ f ∈ range 551,feeSlab w f
  apply sum_congr rfl
  intro f hf
  have hF:=mem_range.mp hf
  rw [Fin.sum_univ_eq_sum_range (fun c : ℕ =>
      ∑ b:Fin 1651,columnFee2 w ⟨b,c,f⟩) 826]
  have hb (c : ℕ) : (∑ b : Fin 1651, columnFee2 w ⟨b,c,f⟩) =
      ∑ b ∈ range 1651,columnFee2 w ⟨b,c,f⟩ :=
    Fin.sum_univ_eq_sum_range (fun b:ℕ => columnFee2 w ⟨b,c,f⟩) 1651
  simp_rw [hb]
  let m:=(1650-3*f)/2+1
  have hcut (c : ℕ) : (∑ b ∈ range 1651, columnFee2 w ⟨b,c,f⟩) =
      if c < m then atSecond w f c else 0:=by
    by_cases hc:c < m
    · rw [ite_eq_left hc]
      exact row_eq w f c (by dsimp [m] at hc; omega)
    · rw [ite_eq_right hc]
      apply sum_eq_zero
      intro b _
      rw [columnFee2,ite_eq_right]
      simp only [Triple.index]
      dsimp [m] at hc
      omega
  simp_rw [hcut]
  rw [sum_take (by dsimp [m]; omega)]
  rfl

#print axioms fee_eq_compute
end Low48PrimaryPivot
