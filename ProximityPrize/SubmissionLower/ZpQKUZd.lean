import ProximityPrize.SubmissionLower.ZULJdud
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qApzjua
noncomputable section
open Polynomial
open cu (L)
open qNu3xvc
open P5_7_1_7_4_3_4 (Pencil PencilBound)
open qZu9hjc (physicalDeriv jacobian HE)
open q53i3jb (eval_false)
open qFD8jve (sheetPole)
open E7 (CurvePlace poleOrder Tq)
open scoped WithZero nonZeroDivisors
variable {E F G:Type} [Field E] [CommRing F] [CommRing G]
theorem pairEval_comp (j:F →+* G) (e :E →+* F) (x y :F) :
  j.comp (pairEval e x y)=pairEval (j.comp e) (j x) (j y) := by
 apply RingHom.ext
 intro g
 simp only [pairEval,RingHom.comp_apply,coe_eval₂RingHom,hom_eval₂]
 congr 1
 apply RingHom.ext
 intro q
 simp only [RingHom.comp_apply,coe_eval₂RingHom,hom_eval₂]
theorem root_coordinates (A:Equation E) :
   pairEval (seed A) (amm A) (jU A false)=KM A false := by
 have h:eval₂RingHom (seed A) (amm A)=(a7W A).comp Polynomial.C:= by
   apply Polynomial.ringHom_ext
   · intro c
     exact eval₂_C _ _
   · exact eval₂_X _ _
 unfold pairEval
 rw [h]
 rfl
theorem root_hom_ext {A:Equation E} {u v :EC A →+* F}
  (hseed :u.comp (seed A)=v.comp (seed A))
  (hx :u (amm A)=v (amm A)) (hy :u (jU A false)=v (jU A false)) :
  u=v := by
 have he :u.comp (KM A false)=v.comp (KM A false) := by
  rw [← root_coordinates,pairEval_comp,pairEval_comp,hseed,hx,hy]
 apply IsLocalization.ringHom_ext (AdjoinRoot A.f)⁰
 apply RingHom.ext
 intro q
 obtain ⟨g,rfl⟩:=AdjoinRoot.mk_surjective q
 change u (a7W A g)=v (a7W A g)
 simpa only [RingHom.comp_apply,eval_false] using RingHom.congr_fun he g
theorem root_zero (A:Equation E) :KM A false A.f=0:= by
 rw [eval_false]
 exact (congrArg (algebraMap (AdjoinRoot A.f) (EC A)) (AdjoinRoot.mk_self (f :=A.f))).trans
  (map_zero _)
theorem map_pencilJac (j:F →+* G) (e :E[X][X] →+* F) (f n d:E[X][X]) (t:F) :
  j (pencilJac e f n d t)=pencilJac (j.comp e) f n d (j t) := by
 simp only [pencilJac,map_sub,map_mul,RingHom.comp_apply]
private theorem coeff_physical (g:E[X][X]) (i:ℕ) :
   (physicalDeriv g).coeff i=(g.coeff i).derivative := by
 classical
 by_cases h:i∈g.support
 · simp [physicalDeriv,sum_def,coeff_monomial,h]
 · simp [physicalDeriv,sum_def,coeff_monomial,h,notMem_support_iff.mp h]
variable [Algebra L E] {A:Equation E}
theorem jac_cut {F:Type} [Field F] (e :E →+* F) (x y :F) (C:Pencil A) (z :L) :
   jacobian e x y A.f (cut C z) =
     pencilJac (pairEval e x y) A.f C.num C.den (e (algebraMap L E z)) := by
 let c:=Polynomial.C (Polynomial.C (algebraMap L E z))
 have h:physicalDeriv (cut C z)=physicalDeriv C.num - c*physicalDeriv C.den:= by
   ext i
   simp [cut,c,coeff_physical,coeff_sub,coeff_C_mul,derivative_sub]
 have h' : (cut C z).derivative=C.num.derivative - c*C.den.derivative := by
   simp [cut,c,derivative_sub]
 change pairEval e x y _ *pairEval e x y _ - pairEval e x y _ *pairEval e x y _ = _
 rw [h,h']
 simp [pencilJac,c,pairEval]
theorem dSE (C:Pencil A) (z :L) {a :ℕ} (ha :A.b+A.d*A.s≤a) :
    (cut C z).natDegree≤A.d∧HE (cut C z) A.s (a+A.s+1) ∧
      ∀ w:CurvePlace L E,sheetPole w.value (cut C z)≤ sheetPole w.value A.f := by
  let c:=Polynomial.C (algebraMap L E z)
  constructor
  · exact (natDegree_sub_le _ _).trans (max_le C.num_weight.1
      ((natDegree_C_mul_le _ _).trans C.den_weight.1))
  constructor
  · intro i hi
    change (cut C z).coeff i≠0 at hi
    have coeff : (cut C z).coeff i=C.num.coeff i - c*C.den.coeff i:= by
      simp [cut,c,coeff_sub,coeff_C_mul]
    have h (g:E[X][X]) (hg:PencilBound A g) (hn:g.coeff i≠0) :=
      (hg.2 i).resolve_right hn
    have hb: ((cut C z).coeff i).natDegree+i*A.s≤A.b+A.d*A.s+A.s+1 := by
      rw [coeff] at hi ⊢
      by_cases hn:C.num.coeff i=0
      · have hd:C.den.coeff i≠0:= fun hd=>hi (by simp [hn,hd])
        rw [hn,zero_sub,natDegree_neg]
        exact (Nat.add_le_add_right (natDegree_C_mul_le _ _) _).trans (h _ C.den_weight hd)
      · by_cases hd:C.den.coeff i=0
        · simpa only [hd,mul_zero,sub_zero] using h _ C.num_weight hn
        · apply (Nat.add_le_add_right (natDegree_sub_le _ _) _).trans
          rw [← max_add_add_right]
          exact max_le (h _ C.num_weight hn)
            ((Nat.add_le_add_right (natDegree_C_mul_le _ _) _).trans (h _ C.den_weight hd))
    exact hb.trans (by omega)
  · intro w
    unfold sheetPole Tq
    apply Finset.sup_le
    intro ij _
    change poleOrder w.value (((cut C z).coeff ij.1).coeff ij.2)≤ sheetPole w.value A.f
    by_cases hz : ((cut C z).coeff ij.1).coeff ij.2=0
    · simp [poleOrder,hz]
    · unfold poleOrder
      change _≤Int.toNat (sheetPole w.value A.f :ℤ)
      refine Int.toNat_le_toNat ((WithZero.log_le_iff_le_exp (w.value.ne_zero_iff.mpr hz)).mpr ?_)
      simp only [cut,coeff_sub,coeff_C_mul]
      apply (w.value.map_sub _ _).trans (max_le (C.num_height w _ _) ?_)
      rw [map_mul]
      by_cases h:z=0
      · simp [h]
      · rw [w.on_constants z h,one_mul]
        exact C.den_height w _ _
end
end qApzjua
