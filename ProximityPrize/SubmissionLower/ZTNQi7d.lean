import ProximityPrize.SubmissionLower.ZhEC96c
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace qOj34lc
noncomputable section
open Polynomial Finset
open scoped WithZero
open qziIa4d (scaledChart)
open qFD8jve (aFA)
open private efc adG cTA b4s bHf from ProximityPrize.SubmissionLower.Y
open private gauss₂ coeff_le_gauss₂ from ProximityPrize.SubmissionLower.ZhEC96c
variable {E :Type} [Field E]
private theorem val_X (v :Valuation E ℤᵐ⁰) :adG v Polynomial.X=1 := by
 simp [adG,support_X]
private theorem val_const (v :Valuation E ℤᵐ⁰) (f :E[X]) :
  gauss₂ v (C f)=adG v f := by
 change adG (b4s v) ((C f :E[X][X]).map _)= _
 rw [Polynomial.map_C,cTA,bHf]
private theorem val_outer (v :Valuation E ℤᵐ⁰) :gauss₂ v Polynomial.X=1 := by
 change adG (b4s v) ((Polynomial.X:E[X][X]).map _)= _
 rw [Polynomial.map_X,val_X]
private theorem taylor_bound (v :Valuation E ℤᵐ⁰) {x :E} (hx :v x≤1)
   (f :E[X]) (B:ℤᵐ⁰) (hf : ∀ j,v (f.coeff j)≤B) :
   adG v (taylor x f)≤B:= by
 change efc v ((taylorAlgHom x) f)≤B
 conv_lhs=>arg 2; arg 2; rw [← sum_C_mul_X_pow_eq f,Polynomial.sum_def]
 rw [map_sum]
 apply (efc v).map_sum_le
 intro i _
 have hc (y :E) :taylorAlgHom x (C y)=C y :=taylor_C x y
 have ht:taylorAlgHom x (Polynomial.X:E[X])=Polynomial.X+C x :=taylor_X x
 simp only [map_mul,map_pow,hc,ht]
 have hX:efc v (Polynomial.X+C x)≤1 :=
   (efc v).map_add_le (show adG v Polynomial.X≤1 by rw [val_X])
     (show adG v (C x)≤1 by rw [cTA]; exact hx)
 rw [← mul_one B]
 exact mul_le_mul' ((cTA v _).trans_le (hf i)) (pow_le_one₀ bot_le hX)
theorem chart_bound (v :Valuation E ℤᵐ⁰) {f G:E[X][X]} {x t a b:E} {h k n:ℕ}
   (hf :aFA v f h) (hx :v x≤1) (ht:v t≤1)
   (ha :v a≤WithZero.exp (k :ℤ)) (hb:v b≤WithZero.exp (k :ℤ))
   (he :scaledChart f x t a b=C ((Polynomial.X:E[X])^n)*G) :
   aFA v G (h+f.natDegree*k) := by
 let w:=gauss₂ v
 let B:=WithZero.exp (k :ℤ)
 have hC (a :E) :w (C (C a))=v a :=(val_const v _).trans (cTA v a)
 have hX:w (C (Polynomial.X:E[X]))=1 :=(val_const v _).trans (val_X v)
 have hY:w Polynomial.X=1 :=val_outer v
 have hbX:w (C (C b*(Polynomial.X:E[X])))≤B:= by
   rw [map_mul,map_mul,hX,hC,mul_one]
   exact hb
 have hbtX:w (C (C (b*t)*(Polynomial.X:E[X])))≤B:= by
   rw [map_mul,map_mul,hX,hC,mul_one,map_mul,← mul_one B]
   exact mul_le_mul' hb ht
 have hAw:w (C (C a+C (b*t)*(Polynomial.X:E[X]))*Polynomial.X)≤B:= by
   rw [map_mul,hY,mul_one,map_add]
   exact w.map_add_le (by rw [hC]; exact ha) hbtX
 have hL:=w.map_add_le hbX hAw
 have hR:w (C (C b)*Polynomial.X)≤B:= by
   rw [map_mul,hY,mul_one,hC]
   exact hb
 have hall:w (scaledChart f x t a b)≤WithZero.exp ((h+f.natDegree*k :ℕ) :ℤ) := by
   unfold scaledChart
   rw [Polynomial.sum_def]
   apply w.map_sum_le
   intro i hi
   rw [map_mul,map_mul,map_pow,map_pow,val_const]
   have hr :=mul_le_mul' (mul_le_mul' (taylor_bound v hx _ _ (hf i)) (pow_le_pow_left' hL i))
     (pow_le_pow_left' hR (f.natDegree-i))
   refine hr.trans_eq ?_
   rw [mul_assoc,← pow_add,Nat.add_sub_of_le (le_natDegree_of_mem_supp i hi)]
   dsimp [B]
 rw [he,map_mul,Polynomial.C_pow,map_pow,hX,one_pow,one_mul] at hall
 exact fun i j=>(coeff_le_gauss₂ v G i j).trans hall
end
end qOj34lc
