import ProximityPrize.SubmissionLower.ZbIpgzb
import ProximityPrize.SubmissionLower.ZpAvArb
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import ProximityPrize.SubmissionLower.ZpQKUZd
import ProximityPrize.SubmissionLower.ZJVClxb
import ProximityPrize.SubmissionLower.Z4ocXpc
import ProximityPrize.SubmissionLower.ZnGdvBe
import ProximityPrize.SubmissionLower.ZMbf7Xa
import ProximityPrize.SubmissionLower.ZUItRVc
set_option Elab.async false
open _root_ renaming Algebra → zZE, CommRing → za6, Field → zrb, Fin.sum_univ_eq_sum_range → zdx, Finset.mul_sum → zxw, Finset.sum_add_distrib → zfW, Finset.sum_congr → zUo, Finset.sum_eq_single → zi6, Finsupp.single → zhf, Fintype.sum_sigma → zla, Function.Injective → zq4, Ideal.Quotient.mk → zVv, IsFractionRing.injective → zxb, MvPolynomial → z3y, MvPolynomial.X → z9v, MvPolynomial.eval → zY9, MvPolynomial.eval₂_comp_left → zqI, MvPolynomial.ringHom_ext → zXT, Nat.add_left_comm → zWn, Nat.lt_succ_of_le → zB1, Nat.lt_succ_self → zTO, Nat.zero_lt_succ → zA8, Polynomial → zM1, Polynomial.C → z1z, Polynomial.C_injective → zmy, Polynomial.X → z7y, Polynomial.eval_C → zFf, Polynomial.eval_map_apply → zdm, PowerSeries → zpm, PowerSeries.C → zMG, PowerSeries.X → zWv, PowerSeries.constantCoeff → zbO, PowerSeries.constantCoeff_C → zr8, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs
section
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace qxqqTXa
noncomputable section
open Polynomial Finset
open scoped Classical
open cu (L)
open qNu3xvc P5_7_1_7_4_3_4 qfbIfsd
open qFQL0Vc (parameter constants alpha beta ic beta_zero beta_polar)
open q2tSkEc (top L4 actual_top)
open q7P6kQb
open private actual_affine from ProximityPrize.SubmissionLower.ZbIpgzb
variable {E :Type} [zrb E] [zZE L E] {A:Equation E}
abbrev Third (A:Equation E) :=Slot A.s (baseCap A 2) (ordCap A 2)
def free (r :Index A) :Prop :=r.1=2∧r.2.1.val<A.d - 1
def tweak (z w:Index A→L) (r :Index A) :L:=z r+if free r then w r else 0
private def gaugePow (C:Pencil A) (y :Series E) :Series E :=
 (1+PowerSeries.C (constants (E :=E) C.tilt)*y)^(A.d-2)
private theorem args_eq (C:Pencil A) (z :Index A→L) (v :Series E) (r :Index A) :
  args C z v r=ic C z r+PowerSeries.C (beta C r)*v := by
 unfold args ic
 nth_rw 1 [actual_affine C r]
 simp only [map_add,map_mul,coe_eval₂RingHom,eval₂_C,eval₂_X]
 exact add_right_comm _ _ _
private theorem gauge_degree (C:Pencil A) :
  (gaugeForm C.tilt A.d).natDegree≤A.d-2 := by
 have h: (1+Polynomial.C C.tilt*z7y).natDegree≤1 :=
  (natDegree_add_le _ _).trans (by simpa using natDegree_C_mul_le C.tilt z7y)
 simpa only [mul_one,gaugeForm] using natDegree_pow_le_of_le (A.d-2) h
private theorem beta_lower (C:Pencil A) (hd:2≤A.d) (r :Index A) (h : ¬ free r) :beta C r=0:= by
 rcases r with ⟨t,k⟩
 by_cases ht:t=2
 · subst t
   have hk :A.d-1≤k.1.val := by
    exact Nat.le_of_not_gt (fun hl=>h ⟨rfl,hl⟩)
   have hg:=coeff_eq_zero_of_natDegree_lt
    ((gauge_degree C).trans_lt (show A.d-2<k.1.val by omega))
   simp [beta_polar,hg]
 · exact beta_zero C _ ht
private theorem slope (C:Pencil A) (x y :Series E) :
   form (zMG ∘ beta C) 2 x y = -gaugePow C y := by
 let m:=PowerSeries.C.comp (constants (E :=E))
 have hg: (gaugeForm C.tilt A.d).eval₂ m y=gaugePow C y := by
   simp [gaugeForm,gaugePow,m,eval₂_pow]
 have hd: (gaugeForm C.tilt A.d).natDegree<A.d-1+1 :=(gauge_degree C).trans_lt (by omega)
 rw [← hg,eval₂_eq_sum_range' _ hd,← zdx,← sum_neg_distrib]
 unfold form
 rw [zla]
 apply sum_congr rfl
 intro i _
 change (∑ j:Fin (A.b+(A.d-1-i.val)*A.s+1),_)= _
 rw [sum_eq_single (0:Fin (A.b+(A.d-1-i.val)*A.s+1))]
 · simp [m,beta_polar]
 · intro j _ hj
   have hj' : j.val≠0:= fun he=>hj (Fin.ext he)
   simp [beta_polar,hj']
 · simp
omit [zZE L E] in
private theorem top_row {M:Type} [CommSemiring M] (a :Index A→M) (t:Fin 3) (x :M) :
   top a t x = ∑ j:Fin (baseCap A t+1),
     a ⟨t,⟨⟨ordCap A t,zTO _⟩,⟨j,by simpa using j.isLt⟩⟩⟩*x^j.val := by
 let i:Fin (ordCap A t+1) :=⟨ordCap A t,zTO _⟩
 unfold top
 rw [zla,sum_eq_single i]
 · let e :Fin (baseCap A t+1) ≃ Fin (baseCap A t+(ordCap A t - i.val)*A.s+1) :=
     finCongr (by simp [i])
   symm
   apply Fintype.sum_equiv e
   intro j
   simp only [i,Fin.val_mk,ite_true]
   rfl
 · intro j _ hj
   have hj' : j.val≠ordCap A t:= fun h=>hj (Fin.ext h)
   simp [hj']
 · simp
omit [zZE L E] in
private theorem value_add {M:Type} [za6 M] (a b:Index A→M) (x y t:M)
   (hb : ∀ r,¬ free r→b r=0) :
   L4 (fun r=>a r+b r*t) x y =
     L4 a x y+form b 2 x y*t:= by
 have ht (k :Fin 3) (hk : ¬ (k=2∧ordCap A k<A.d-1)) :
     top (fun r=>a r+b r*t) k x=top a k x := by
   rw [top_row,top_row]
   apply sum_congr rfl
   intro j _
   let r :Index A:=⟨k,⟨⟨ordCap A k,zTO _⟩,⟨j,by simpa using j.isLt⟩⟩⟩
   change (a r+b r*t)*x^j.val=a r*x^j.val
   rw [hb r (show ¬free r from hk),zero_mul,add_zero]
 have hf :form (fun r=>a r+b r*t) 2 x y=form a 2 x y+form b 2 x y*t:= by
   simp only [form,sum_mul,← sum_add_distrib]
   apply sum_congr rfl
   intro k _
   ring
 rw [L4,hf,ht 0 (by simp),ht 2 (by simp),L4]
 ring
private def perturb (w:Index A→L) (r :Index A) :Series E :=
 if free r then zMG (constants (E :=E) (w r)) else 0
private theorem args_tweak (C:Pencil A) (z w:Index A→L) (v :Series E) (r :Index A) :
  args C (tweak z w) v r =
   (args C z 0 r+perturb w r*zWv)+PowerSeries.C (beta C r)*v := by
 by_cases h:free r <;> simp [args_eq,ic,tweak,perturb,h,add_mul,add_assoc]
private theorem djo (C:Pencil A) (hd:2≤A.d) (z w:Index A→L) (x y v :Series E) :
    L4 (args C (tweak z w) v) x y =
      L4 (args C z 0) x y+form (perturb w) 2 x y*zWv -
        gaugePow C y*v := by
  rw [funext (args_tweak C z w v)]
  rw [value_add _ _ _ _ _ (fun r hr=> by simp [beta_lower C hd r hr]),
    value_add _ _ _ _ _ (fun r hr=> by simp [perturb,hr])]
  rw [show (fun r=>zMG (beta C r))=zMG ∘ beta C from rfl,slope]
  ring
theorem keep_forms {C:Pencil A} {F:Fiber C} {z :Index A→L} (u:Arc F z)
    (w:Index A→L) (i:Fin F.size) (v :Series E) :
    form (args C (tweak z w) v) 0 (u.xy i).1 (u.xy i).2=0 ∧
    form (args C (tweak z w) v) 1 (u.xy i).1 (u.xy i).2=0:= by
  have h (k :Fin 3) (hk :k≠2) :
      form (args C (tweak z w) v) k (u.xy i).1 (u.xy i).2 =
        form (args C z 0) k (u.xy i).1 (u.xy i).2 := by
    unfold form
    apply sum_congr rfl
    intro j _
    simp [args_tweak,perturb,free,hk,beta_zero C ⟨k,j⟩ hk]
  exact ⟨(h 0 (by decide)).trans (u.zero₀ i),(h 1 (by decide)).trans (u.zero₁ i)⟩
variable {C:Pencil A} {F:Fiber C} {z :Index A→L}
def value (u:Arc F z) (w:Index A→L) (i:Fin F.size) :Series E :=
  (L4 (args C z 0) (u.xy i).1 (u.xy i).2 +
    form (perturb w) 2 (u.xy i).1 (u.xy i).2*zWv) *
      (gaugePow C (u.xy i).2)⁻¹
theorem gauge_center (u:Arc F z) (i:Fin F.size) :
  zbO (gaugePow C (u.xy i).2)=gaugeAt C (F.point i).2^(A.d-2) := by
 have hy :zbO (u.xy i).2=(F.point i).2 :=congrArg Prod.snd (u.center i)
 simp [gaugePow,gaugeAt,constants,parameter,RatFunc.algebraMap_C,hy]
theorem gK3 (hd:2≤A.d) (u:Arc F z) (w:Index A→L) (i:Fin F.size) :
  L4 (args C (tweak z w) (value u w i)) (u.xy i).1 (u.xy i).2=0:= by
 have h:zbO (gaugePow C (u.xy i).2)≠0:= by
  rw [gauge_center]
  exact pow_ne_zero _ (F.unitGauge i)
 rw [djo C hd,value,mul_left_comm,PowerSeries.mul_inv_cancel _ h,mul_one,sub_self]
def normalized (u:Arc F z) (i:Fin F.size) (k :Third A) :Series E :=
  if k.1.val<A.d-1 then
    (u.xy i).1^k.2.val*(u.xy i).2^k.1.val*(gaugePow C (u.xy i).2)⁻¹ else 0
theorem normalized_center (u:Arc F z) (i:Fin F.size) (k :Third A) (hk :k.1.val<A.d-1) :
   zbO (normalized u i k) =
     (F.point i).1^k.2.val*(F.point i).2^k.1.val /
         gaugeAt C (F.point i).2^(A.d-2) := by
 have hx :zbO (u.xy i).1=(F.point i).1 :=congrArg Prod.fst (u.center i)
 have hy :zbO (u.xy i).2=(F.point i).2 :=congrArg Prod.snd (u.center i)
 simp [normalized,hk,hx,hy,gauge_center,PowerSeries.constantCoeff_inv,div_eq_mul_inv]
theorem value_change (u:Arc F z) (w:Index A→L) (i:Fin F.size) :
   value u w i=value u (fun _=>0) i+PowerSeries.X *
     ∑ k :Third A,normalized u i k*zMG (constants (E :=E) (w ⟨2,k⟩)) := by
 have hz : (perturb (fun _=>0) :Index A→Series E)=0:= by
   funext r
   simp [perturb]
 rw [value,value,hz,add_mul,form,form]
 simp only [Pi.zero_apply,zero_mul,sum_const_zero,perturb,normalized,free,
   true_and,mul_sum,sum_mul,add_zero]
 congr 1
 apply sum_congr rfl
 intro k _
 split_ifs <;> ring
private theorem tied_top (C:Pencil A) (hd:2≤A.d) (x :Closure E) :
   top (alpha C) 2 x=(A.d:Closure E)*top (alpha C) 0 x := by
 rw [top_row,top_row,mul_sum]
 apply sum_congr rfl
 intro j _
 have h:=congrArg ((parameter (E :=E)).comp (evalRingHom (0:E[X]))) (actual_top C hd j)
 have hc:alpha C ⟨2,⟨⟨A.d-1,Nat.lt_succ_self _⟩,⟨j,by simpa using j.isLt⟩⟩⟩ =
     (A.d:Closure E)*alpha C ⟨0,⟨⟨A.d,Nat.lt_succ_self _⟩,⟨j,by simpa using j.isLt⟩⟩⟩:= by
   simpa [alpha,const₂,← coeff_zero_eq_eval_zero] using h
 exact (congrArg (fun a=>a*x^j.val) hc).trans (mul_assoc _ _ _)
omit [zZE L E] in
private theorem slot_eval {M:Type} [CommSemiring M] (m:E →+* M) (p:E[X][X])
   {d b s :ℕ} (hd:p.natDegree≤d)
   (hw : ∀ i:Fin (d+1),(p.coeff i).natDegree≤b+(d-i.val)*s) (x y :M) :
   (∑ k :Slot s b d,m ((p.coeff k.1).coeff k.2)*x^k.2.val*y^k.1.val) =
     p.eval₂ (eval₂RingHom m x) y := by
 rw [zla,eval₂_eq_sum_range' _ (zB1 hd),← zdx]
 apply sum_congr rfl
 intro i _
 rw [coe_eval₂RingHom,eval₂_eq_sum_range' _ (zB1 (hw i)),
   ← zdx,sum_mul]
omit [zZE L E] in
private theorem derivative_weight (A:Equation E) (hd:2≤A.d)
    (i:Fin (A.d-1+1)) :
    (A.f.derivative.coeff i).natDegree≤A.b+(A.d-1-i.val)*A.s := by
  rcases A.weight (i.val+1) with h | h
  · have he :A.d=(A.d-1-i.val)+(i.val+1) := by have :=i.isLt; omega
    have hw: (A.f.coeff (i.val+1)).natDegree≤A.b+(A.d-1-i.val)*A.s := by
      calc
        _≤A.b+A.d*A.s-(i.val+1)*A.s :=Nat.le_sub_of_add_le h
        _ = _:= by
          rw [show A.b+A.d*A.s=(A.b+(A.d-1-i.val)*A.s)+(i.val+1)*A.s from
            (congrArg (fun n=>A.b+n*A.s) he).trans (by ring),Nat.add_sub_cancel]
    rw [coeff_derivative,← Nat.cast_succ,← C_eq_natCast]
    exact (natDegree_mul_C_le _ _).trans hw
  · simp [coeff_derivative,h]
private theorem center_ratio (hd:2≤A.d) (i:Fin F.size) :
    form (alpha C) 2 (F.point i).1 (F.point i).2 /
      gaugeAt C (F.point i).2^(A.d-2)=F.value i:= by
  obtain ⟨σ,hσ,hpt,hv⟩:=F.realized i
  let m:E →+* Closure E :=(parameter (E :=E)).comp z1z
  have hseed (a :E) :σ (seed A a)=m a := by
    rw [← C.base_seed]
    simpa [m,parameter,RatFunc.algebraMap_C] using zLs hσ (RatFunc.C a)
  have hc: ((σ.comp (a7W A)).comp z1z) =
      eval₂RingHom m (σ (amm A)) := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa [seed] using hseed a
    · simp [amm]
  have hp:σ (polar A false) =
      form (alpha C) 2 (F.point i).1 (F.point i).2 := by
    change σ (A.f.derivative.eval₂ ((a7W A).comp z1z) (jU A false))= _
    rw [hom_eval₂,← RingHom.comp_assoc,hc,hpt]
    symm
    simpa [form,alpha,actual,const₂,m] using
      slot_eval m A.f.derivative (natDegree_derivative_le A.f) (derivative_weight A hd)
        (σ (amm A)) (σ (jU A false))
  have hg:σ (gauge A C.tilt)=gaugeAt C (F.point i).2 := by
    simp [P5_7_1_7_4_3_4.gauge,gaugeAt,constant,hseed,m,parameter,RatFunc.algebraMap_C,hpt]
  rw [hv,relativePolar,map_div₀,map_pow,hp,hg]
theorem value_center (hd:2≤A.d) (u:Arc F z) (w:Index A→L) (i:Fin F.size) :
  zbO (value u w i)=F.value i:= by
 have hx :zbO (u.xy i).1=(F.point i).1 :=congrArg Prod.fst (u.center i)
 have hy :zbO (u.xy i).2=(F.point i).2 :=congrArg Prod.snd (u.center i)
 have harg (r :Index A) :zbO (args C z 0 r)=alpha C r := by
  simp [args_eq,ic]
 rw [value,map_mul,PowerSeries.constantCoeff_inv,gauge_center,map_add,map_mul,
  PowerSeries.constantCoeff_X,mul_zero,add_zero,← div_eq_mul_inv,← center_ratio hd i]
 congr 1
 simp only [L4,top,form,map_add,map_sub,map_mul,map_natCast,map_pow,map_sum,
  apply_ite,map_zero,hx,hy,harg]
 have h:=tied_top C hd (F.point i).1
 unfold top at h
 rw [h,sub_self,zero_mul,add_zero]
end
end qxqqTXa
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace qxqqTXa
noncomputable section
open Polynomial Finset
open scoped Classical
open cu (L)
open qNu3xvc P5_7_1_7_4_3_4 qfbIfsd q7P6kQb
open qFQL0Vc (constants)
local notation "MC" => MvPolynomial.C
local notation "MX" => MvPolynomial.X
private theorem nonzero_at {D:Type} [za6 D] [IsDomain D] [Infinite D] (p:D[X])
  (hp:p≠0) : ∃ x,(evalRingHom x) p≠0:= by
 by_contra! h
 exact hp (eq_zero_of_infinite_isRoot p (Set.infinite_univ.mono fun x _=>h x))
private theorem avoid {D J:Type} [za6 D] [IsDomain D] (j:L →+* D)
  (hj:zq4 j) (P:z3y J D) (hP:P≠0) :
  ∃ w:J→L,zY9 (j ∘ w) P≠0:= by
 by_contra! h
 apply hP
 apply MvPolynomial.funext_set (fun _=>Set.range j)
  (fun _=>Set.infinite_range_of_injective hj)
 intro x hx
 choose w hw using fun i=>hx i (Set.mem_univ i)
 rw [← funext hw,map_zero]
 exact h w
variable {E :Type} [zrb E] [zZE L E] {A:Equation E}
private def detector (f :E[X][X][X] →+* Series E) (C:Pencil A)
  (R:z3y (Index A) L) (z :Index A→L) :
  z3y (Index A) (Series E) :=
 R.eval₂ (MvPolynomial.C.comp (f.comp (Polynomial.C.comp (const₂.comp (algebraMap L E)))))
  (fun r=>MC (f (deformArg (actual C r) (z r))) +
    if free r then MX r*MC (f z7y) else 0)
private theorem detector_eval (f :E[X][X][X] →+* Series E) (j:L →+* Series E)
   (hj:f.comp (Polynomial.C.comp (const₂.comp (algebraMap L E)))=j)
   (C:Pencil A) (R:z3y (Index A) L) (z w:Index A→L) :
   zY9 (j ∘ w) (detector f C R z)=f (deform R (actual C) (tweak z w)) := by
 let e :=zY9 (j ∘ w)
 change e (detector f C R z)= _
 rw [detector,deform,zqI e,
   zqI (S₁:=E[X][X][X]) (S₂:=Series E) f,hj]
 congr 1
 · ext a
   simp [e]
 · funext r
   have hc (a :L) :f (z1z (const₂ (algebraMap L E a)))=j a :=
     zLs hj a
   by_cases hr :free r <;>
     simp [e,tweak,hr,deformArg,hc,add_mul,add_assoc]
variable {C:Pencil A} {F:Fiber C} {z :Index A→L}
private def branch (u:Arc F z) (i:Fin F.size) :z3y (Index A) (Series E) :=
 MC (value u (fun _=>0) i)+MC zWv *
  ∑ k :Third A,MC (normalized u i k)*MX ⟨2,k⟩
private theorem branch_eval (u:Arc F z) (i:Fin F.size) (w:Index A→L) :
   zY9 ((PowerSeries.C.comp (constants (E :=E))) ∘ w) (branch u i) =
     value u w i:= by
 rw [value_change]
 simp [branch,MvPolynomial.eval_C]
private theorem branch_coeff (u:Arc F z) (i:Fin F.size) (k :Third A) :
  (branch u i).coeff (zhf ⟨2,k⟩ 1)=zWv*normalized u i k := by
 have hs : (zhf (⟨2,k⟩:Index A) (1 :ℕ))≠0:= by simp
 simp [branch,MvPolynomial.coeff_C_of_ne_zero hs,MvPolynomial.coeff_C_mul,
  MvPolynomial.coeff_X,Finsupp.single_eq_single_iff]
private theorem branch_ne (u:Arc F z) (hsep:Ak F) (i k :Fin F.size)
  (hne :i≠k) (hc:F.value i=F.value k) :branch u i - branch u k≠0:= by
 obtain ⟨s,hs,h⟩:=hsep i k hne hc
 intro hz
 have he :=congrArg (fun p:z3y (Index A) (Series E)=>p.coeff (zhf ⟨2,s⟩ 1))
  (sub_eq_zero.mp hz)
 rw [branch_coeff,branch_coeff] at he
 have hn:=congrArg zbO (mul_left_cancel₀ PowerSeries.X_ne_zero he)
 rw [normalized_center u i s hs,normalized_center u k s hs] at hn
 exact h hn
theorem proof :q7P6kQb.c4 := by
 intro E _ _ A hd C _ F hsep R z hz u
 let:Infinite E :=Infinite.of_injective _ (algebraMap L E).injective
 let:Infinite E[X] :=Infinite.of_injective _ (zmy (R:=E))
 let:Infinite E[X][X] :=Infinite.of_injective _ (zmy (R:=E[X]))
 obtain ⟨a,ha⟩:=nonzero_at _ hz
 obtain ⟨b,hb⟩:=nonzero_at _ ha
 obtain ⟨c,hc⟩:=nonzero_at _ hb
 let j:=PowerSeries.C.comp (constants (E :=E))
 let m:=PowerSeries.C.comp ((qFQL0Vc.parameter (E :=E)).comp z1z)
 let f :=m.comp ((evalRingHom c).comp ((evalRingHom b).comp (evalRingHom a)))
 have hf :f (deform R (actual C) z)≠0:= fun h=>hc (m.injective (h.trans m.map_zero.symm))
 have hj:f.comp (Polynomial.C.comp (const₂.comp (algebraMap L E)))=j:= by
   ext a
   simp [f,j,m,constants,const₂]
 let D:=detector f C R z
 have hD:D ≠0:= by
   have hzero :tweak z (fun _=>0)=z := by
     funext r
     simp [tweak]
   intro h
   exact hf (by
     rw [← hzero,← detector_eval f j hj,show detector f C R z=0 from h,map_zero])
 let pairs :=(univ :Finset (Fin F.size×Fin F.size)).filter
   (fun p=>p.1≠p.2∧F.value p.1=F.value p.2)
 let d (p:Fin F.size×Fin F.size) :=branch u p.1 - branch u p.2
 let P:=D * ∏ p∈pairs,d p
 have hP:P≠0:=mul_ne_zero hD (prod_ne_zero_iff.mpr fun p hp =>
   branch_ne u hsep p.1 p.2 (mem_filter.mp hp).2.1 (mem_filter.mp hp).2.2)
 obtain ⟨w,hw⟩:=avoid j (PowerSeries.C_injective.comp (constants (E :=E)).injective) P hP
 simp only [P,map_mul,map_prod,mul_ne_zero_iff,prod_ne_zero_iff] at hw
 refine ⟨tweak z w,value u w,?_,?_,value_center hd u w,fun i => ?_⟩
 · intro h
   apply hw.1
   simp [D,detector_eval f j hj,h]
 · intro i k hv
   by_contra hn
   have hck :F.value i=F.value k := by
     rw [← value_center hd u w i,← value_center hd u w k,hv]
   apply hw.2 (i,k) (mem_filter.mpr ⟨mem_univ _,hn,hck⟩)
   change zY9 ((PowerSeries.C.comp (constants (E :=E))) ∘ w)
     (branch u i - branch u k)=0
   rw [map_sub,branch_eval,branch_eval,hv,sub_self]
 · exact ⟨(keep_forms u w i _).1,(keep_forms u w i _).2,gK3 hd u w i⟩
end
end qxqqTXa
end
end
section
set_option backward.isDefEq.respectTransparency false
namespace qloRzZa
noncomputable section
open Polynomial
open cu (L)
open qNu3xvc (Equation KM polar seed)
open P5_7_1_7_4_3_4 (Pencil relativePolar)
open qfbIfsd (Slot baseCap ordCap)
open q7P6kQb (tu Closure Fiber block aMq gaugeAt)
open qZu9hjc (atPair physicalDeriv jacobian)
open qApzjua (pairEval pairEval_comp root_coordinates root_zero)
open scoped Classical
private def alongX {K M:Type} [zrb K] [zrb M] (e :K →+* M)
  (y :M) (f :K[X][X]) :M[X] :=
 f.sum fun i c=>c.map e*C (y ^i)
private theorem alongX_eval {K M:Type} [zrb K] [zrb M] (e :K →+* M)
  (f :K[X][X]) (x y :M) : (alongX e y f).eval x=atPair e x y f := by
 rw [atPair,eval₂_eq_sum]
 simp only [alongX,sum_def,eval_finsetSum,eval_mul,eval_map,eval_C,coe_eval₂RingHom]
private theorem alongX_derivative {K M:Type} [zrb K] [zrb M] (e :K →+* M)
  (f :K[X][X]) (x y :M) :
  (alongX e y f).derivative.eval x=atPair e x y (physicalDeriv f) := by
 rw [atPair,physicalDeriv,eval₂_sum]
 simp only [alongX,sum_def,derivative_sum,derivative_mul,derivative_C,
  mul_zero,add_zero,derivative_map,eval_finsetSum,eval_mul,eval_map,eval_C,
  eval₂_monomial,coe_eval₂RingHom]
private theorem alongX_degree {K M:Type} [zrb K] [zrb M] (e :K →+* M)
  (f :K[X][X]) (y :M) (n:ℕ) (h : ∀ i,(f.coeff i).natDegree≤n) :
  (alongX e y f).natDegree≤n:= by
 rw [alongX,sum_def]
 apply natDegree_sum_le_of_forall_le
 intro i _
 exact (natDegree_mul_C_le _ _).trans (natDegree_map_le.trans (h i))
variable {E :Type} [zrb E] [zZE L E] {A:Equation E}
private theorem block_degree (C:Pencil A) (t:Fin 3) {n:ℕ}
   (h : ∀ k :Slot A.s (baseCap A t) (ordCap A t),k.2.val≤n) (i:ℕ) :
   ((block C t).coeff i).natDegree≤n:= by
 simp only [block,finsetSum_coeff]
 apply natDegree_sum_le_of_forall_le
 intro k _
 rw [coeff_monomial]
 split
 · exact (natDegree_monomial_le _).trans (h k)
 · simp
private theorem same_x (C:Pencil A) (F:Fiber C) (hb:A.b+A.s=0)
  (i j:Fin F.size) (hy : (F.point i).2=(F.point j).2) :
  (F.point i).1=(F.point j).1 := by
 have hb₀:A.b=0:= by omega
 have hs₀:A.s=0:= by omega
 let e :=algebraMap (tu E) (Closure E)
 let x :=(F.point i).1
 let x' := (F.point j).1
 let y :=(F.point i).2
 let p:=alongX e y (block C 0)
 let q:=alongX e y (block C 1)
 have hp:p.natDegree≤0:= by
  apply alongX_degree
  apply block_degree
  intro k
  have hk :=k.2.isLt
  change k.2.val<A.b+(A.d - k.1.val)*A.s+1 at hk
  simpa [hb₀,hs₀] using hk
 have hq:q.natDegree≤1 := by
  apply alongX_degree
  apply block_degree
  intro k
  have hk :=k.2.isLt
  change k.2.val<A.b+A.s+1+(A.d - k.1.val)*A.s+1 at hk
  simp only [hb₀,hs₀,Nat.mul_zero,Nat.zero_add,Nat.add_zero] at hk
  omega
 have hp' : p.derivative.eval x=0:= by
  rw [eq_C_of_natDegree_le_zero hp]
  simp
 have hq' : q.derivative.eval x≠0:= by
  intro h
  apply F.simple i
  change jacobian e x y (block C 0) (block C 1)=0
  simp only [jacobian,← alongX_derivative]
  change p.derivative.eval x*_-_ *q.derivative.eval x=0
  rw [hp',h,zero_mul,mul_zero,sub_self]
 have h₁:q.eval x=0:= by
  rw [alongX_eval,aMq]
  exact F.zero₁ i
 have h₂:q.eval x' = 0:= by
  rw [alongX_eval,show y=(F.point j).2 from hy,aMq]
  exact F.zero₁ j
 have hlin:=eq_X_add_C_of_natDegree_le_one hq
 have ha :q.coeff 1≠0:= by
  intro h
  apply hq'
  rw [hlin]
  simp [h]
 rw [hlin] at h₁ h₂
 apply mul_left_cancel₀ ha
 apply add_right_cancel (b:=q.coeff 0)
 simpa only [eval_add,eval_mul,eval_C,eval_X] using h₁.trans h₂.symm
private theorem quadratic {K:Type} [zrb K] (p:K[X]) (hd:p.natDegree≤2)
  (htwo: (2 :K)≠0) (y z :K) (hy :p.eval y=0) (hz :p.eval z=0)
  (hv :p.derivative.eval y=p.derivative.eval z)
  (hn:p.derivative.eval y≠0) :y=z := by
 by_contra hne
 have hp:=eq_quadratic_of_degree_le_two (degree_le_of_natDegree_le hd)
 have hder (v :K) :p.derivative.eval v=p.coeff 2*2*v+p.coeff 1 := by
  conv_lhs=>rw [hp]
  simp only [derivative_add,derivative_C_mul_X_sq,derivative_C_mul_X,derivative_C,
    add_zero,eval_add,eval_mul,eval_C,eval_X]
 have ha :p.coeff 2=0:= by
  by_contra ha
  rw [hder,hder] at hv
  exact hne (mul_left_cancel₀ (mul_ne_zero ha htwo) (add_right_cancel hv))
 have hb:p.coeff 1=0:= by
  by_contra hb
  rw [hp] at hy hz
  apply hne
  apply mul_left_cancel₀ hb
  apply add_right_cancel (b:=p.coeff 0)
  simpa [ha] using hy.trans hz.symm
 exact hn (by simp [hder,ha,hb])
private def pO (E :Type) [zrb E] :E →+* Closure E :=
 (algebraMap (tu E) (Closure E)).comp RatFunc.C
private theorem two_ne : (2 :Closure E)≠0:= by
 let m:=(pO E).comp ((algebraMap L E).comp (algebraMap K1.K L))
 let _:CharP (Closure E) K1.p:=charP_of_injective_ringHom m.injective _
 intro h
 exact (show ¬ K1.p≤2 by decide)
  (Nat.le_of_dvd (by decide) ((CharP.cast_eq_zero_iff (Closure E) K1.p 2).mp h))
private def alongY (A:Equation E) (x :Closure E) : (Closure E)[X] :=
 A.f.map (eval₂RingHom (pO E) x)
private theorem quadratic_data (C:Pencil A) (F:Fiber C) (hd:A.d = 2)
   (i:Fin F.size) :
   let q:=alongY A (F.point i).1
   q.eval (F.point i).2=0∧q.derivative.eval (F.point i).2=F.value i∧F.value i≠0:= by
 obtain ⟨σ,hσ,hpt,hv⟩:=F.realized i
 have hs :σ.comp (seed A)=pO E := by
   ext c
   change σ (seed A c)=algebraMap (tu E) (Closure E) (RatFunc.C c)
   rw [← C.base_seed]
   exact zLs hσ (RatFunc.C c)
 have he :pairEval (pO E) (F.point i).1 (F.point i).2=σ.comp (KM A false) := by
   rw [hpt,← hs,← pairEval_comp,root_coordinates]
 have hv' : F.value i=σ (polar A false) := by
   simpa [relativePolar,hd] using hv
 refine ⟨?_,?_,?_⟩
 · rw [alongY,eval_map]
   change pairEval (pO E) (F.point i).1 (F.point i).2 A.f=0
   rw [he,zQb,root_zero,map_zero]
 · rw [alongY,derivative_map,eval_map]
   change pairEval (pO E) (F.point i).1 (F.point i).2 A.f.derivative= _
   exact (zLs he A.f.derivative).trans hv'.symm
 · rw [hv']
   exact fun h=>C.polar_ne (σ.injective (h.trans (map_zero σ).symm))
omit [zZE L E] in
private theorem flat_sections (hb:A.b+A.s=0) (x z :Closure E) :
  alongY A x=alongY A z := by
 have hb₀:A.b=0:= by omega
 have hs₀:A.s=0:= by omega
 apply Polynomial.ext
 intro i
 have h: (A.f.coeff i).natDegree≤0:= by
  rcases A.weight i with h | h <;> simp_all
 simp only [alongY,coeff_map,coe_eval₂RingHom]
 rw [eq_C_of_natDegree_le_zero h,eval₂_C,eval₂_C]
private abbrev Lower (A:Equation E) :=Slot A.s (baseCap A 2) (ordCap A 2)
private def unitSlot (A:Equation E) :Lower A :=
 ⟨⟨0,zA8 _⟩,⟨0,zA8 _⟩⟩
private def ordinateSlot (A:Equation E) (hd:3≤A.d) :Lower A :=
 ⟨⟨1,by change 1<A.d - 1+1; omega⟩,⟨0,zA8 _⟩⟩
private def abscissaSlot (A:Equation E) (hd:2≤A.d) (hb:0<A.b+A.s) :Lower A :=
 ⟨⟨0,zA8 _⟩,⟨1,by
   change 1<A.b+(A.d - 1)*A.s+1
   have hs :=Nat.mul_le_mul_right A.s (show 1≤A.d - 1 by omega)
   rw [one_mul] at hs
   omega⟩⟩
theorem proof :q7P6kQb.c2 := by
  intro E _ _ A hd C _ F i j hij hv
  by_contra h
  let x (k :Fin F.size) :=(F.point k).1
  let y (k :Fin F.size) :=(F.point k).2
  let g (k :Fin F.size) :=gaugeAt C (y k)^(A.d - 2)
  have agree (k :Lower A) (hk :k.1.val<A.d - 1) :
      x i^k.2.val*y i^k.1.val/g i=x j^k.2.val*y j^k.1.val/g j :=
    Classical.byContradiction fun hn=>h ⟨k,hk,hn⟩
  have hg:g i=g j:= by
    have hu:=agree (unitSlot A) (show 0<A.d - 1 by omega)
    simpa only [unitSlot,pow_zero,mul_one,one_div,inv_inj] using hu
  have equalMonomial (k :Lower A) (hk :k.1.val<A.d - 1) :
      x i^k.2.val*y i^k.1.val=x j^k.2.val*y j^k.1.val := by
    have h' := agree k hk
    rw [← hg] at h'
    exact (div_left_inj' (pow_ne_zero _ (F.unitGauge i))).mp h'
  have hx (hb:0<A.b+A.s) :x i=x j:= by
    simpa only [abscissaSlot,pow_zero,pow_one,mul_one] using
      equalMonomial (abscissaSlot A hd hb) (show 0<A.d - 1 by omega)
  have hy :y i=y j:= by
    by_cases hd' : 3≤A.d
    · simpa only [ordinateSlot,pow_zero,pow_one,one_mul] using
        equalMonomial (ordinateSlot A hd') (show 1<A.d - 1 by omega)
    have hd₂:A.d = 2 := by omega
    have hq:alongY A (x i)=alongY A (x j) := by
      by_cases hb:0<A.b+A.s
      · rw [hx hb]
      · exact flat_sections (by omega) _ _
    obtain ⟨hi₀,hi₁,hi₂⟩:=quadratic_data C F hd₂ i
    obtain ⟨hj₀,hj₁,_⟩:=quadratic_data C F hd₂ j
    change (alongY A (x i)).eval (y i)=0 at hi₀
    change (alongY A (x i)).derivative.eval (y i)=F.value i at hi₁
    change (alongY A (x j)).eval (y j)=0 at hj₀
    change (alongY A (x j)).derivative.eval (y j)=F.value j at hj₁
    rw [← hq] at hj₀ hj₁
    refine quadratic _ ((natDegree_map_le (p:=A.f)).trans hd₂.le) two_ne _ _ hi₀ hj₀
      (hi₁.trans (hv.trans hj₁.symm)) (fun h₀=>hi₂ (hi₁.symm.trans h₀))
  apply hij
  apply F.distinct
  exact Prod.ext (by
    by_cases hb:0<A.b+A.s
    · exact hx hb
    · exact same_x C F (by omega) i j hy) hy
end
end qloRzZa
end
section
section
namespace qDTrBfa
noncomputable section
open scoped Classical Matrix

open MvPolynomial
open qfbIfsd (Slot Vars form)
open qBl3Pad
open q2tSkEc (caps orders bzm)
open qEAs6me (Coeff tie tied)
open private includePair includePair_X form_incidence from ProximityPrize.SubmissionLower.ZStcUwb
private theorem tie_includePair {s b d:ℕ}
  (p:PairCoeffs s (caps b s) (orders d) 2) :tie (includePair p)=includePair p:= by
 have h: (tie (s :=s) (b:=b) (d:=d)).comp (includePair (k :=2))=includePair := by
  apply zXT
  · intro c
    simp [includePair,tie]
  · intro v
    rw [zQb,includePair_X,tie,eval₂Hom_X']
    exact dite_eq_right fun h=>v.property h.1
 exact zLs h p
private def genericThird {s b d:ℕ} (v :bzm s b d) :
  zM1 (MY s (caps b s) (orders d) 2) :=
 if v=⟨2,zeroSlot s (caps b s 2) (orders d 2)⟩ then z7y
 else z1z (pairCoeff 2 v)
private theorem genericThird_other {s b d:ℕ} (v :bzm s b d) (hv :v.1≠2) :
  genericThird v=z1z (pairCoeff 2 v) := by
 exact ite_eq_right (fun h=>hv (congrArg Sigma.fst h))
private theorem genericThird_tied {s b d:ℕ} (hd:2≤d)
    (w:Slot s (caps b s 2) (orders d 2)) :
    tied genericThird ⟨2,w⟩ =
      (if w=zeroSlot s (caps b s 2) (orders d 2) then z7y else 0) +
      z1z (tied (pairCoeff 2) ⟨2,w⟩) := by
  by_cases h:w.1.val=orders d 2
  · have hz :w≠zeroSlot s (caps b s 2) (orders d 2) := by
      intro hw
      have hn:orders d 2=0:=h.symm.trans (congrArg (fun i=>i.1.val) hw)
      change d - 1=0 at hn
      omega
    rw [ite_eq_right hz,zero_add]
    have h02 : (0:Fin 3)≠2 := by decide
    unfold tied
    rw [dite_eq_left ⟨rfl,h⟩,dite_eq_left ⟨rfl,h⟩,genericThird_other _ h02,
      map_mul,map_natCast]
  · rw [tied,dite_eq_right (fun hk=>h hk.2),tied,dite_eq_right (fun hk=>h hk.2)]
    have hw: (⟨2,w⟩:bzm s b d)=⟨2,zeroSlot s (caps b s 2) (orders d 2)⟩ ↔
        w=zeroSlot s (caps b s 2) (orders d 2) := by simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and]
    have hz :pairCoeff 2 (⟨2,w⟩:bzm s b d)=0:= by
      rw [pairCoeff,dite_eq_right (fun hn=>hn rfl)]
    simp only [genericThird,hw,hz,Polynomial.C_0,add_zero]
set_option maxHeartbeats 900000 in
private theorem norm_relation {s :ℕ} {b e :Fin 3→ℕ} {k :Fin 3}
    (σ:jo s b e →+* jo s b e)
    (hfix : ∀ p:PairCoeffs s b e k,σ (includePair p)=includePair p)
    (ε:jo s b e →+* zM1 (MY s b e k))
    (hε : ∀ p:PairCoeffs s b e k,
      ε (includePair p)=z1z (algebraMap _ (MY s b e k) p))
    (c:Slot s (b k) (e k)→MY s b e k)
    (hc : ∀ w:Slot s (b k) (e k),ε (σ (z9v ⟨k,w⟩)) =
      (if w=zeroSlot s (b k) (e k) then z7y else 0)+Polynomial.C (c w))
    (hfinite :Module.Finite (MY s b e k) (PairAlgebra s b e k)) :
    ∃ S:jo s b e,incidence s b e S=0∧σ S≠0:= by
  classical
  let O:=PairCoeffs s b e k
  let F:=MY s b e k
  let A:=PairAlgebra s b e k
  let E :=FractionRing (Chart s b e)
  let γ:Chart s b e →+* E :=algebraMap _ _
  let φ:jo s b e →+* E :=γ.comp (incidence s b e)
  let jPair :O →+* jo s b e :=includePair
  let ι:=Fin (Module.finrank F A)
  let B:Module.Basis ι F A:=Module.finBasis F A
  let z :=zeroSlot s (b k) (e k)
  let q:=zVv (Ib s b e k)
  let u (w:Slot s (b k) (e k)) :A :=
    q ((z9v 0:lK s b e k)^w.2.val*z9v 1^w.1.val)
  have u_zero :u z=1 := by simp [u,z,zeroSlot]
  have hγ:zq4 γ:=zxb (Chart s b e) E
  by_cases hinj:zq4 (φ.comp jPair)
  swap
  · obtain ⟨p,r,hpr,hn⟩:=Function.not_injective_iff.mp hinj
    refine ⟨jPair (p-r),?_,?_⟩
    · apply hγ
      change (φ.comp jPair) (p-r)=γ 0
      rw [map_sub,hpr,sub_self,map_zero]
    · rw [hfix]
      exact (map_ne_zero_iff _ (rename_injective _ Subtype.val_injective)).2 (sub_ne_zero.mpr hn)
  let g:F →+* E :=IsFractionRing.lift hinj
  have hg (p:O) :g (algebraMap O F p)=φ (jPair p) :=IsLocalization.lift_eq _ p
  let x :E :=γ (z9v (.inl 0))
  let y :E :=γ (z9v (.inl 1))
  have hform (t:Fin 3) :form (fun v=>φ (z9v v)) t x y=0:= by
    have hv (v :Vars s b e) :φ (z9v v)=γ (incidenceArg v) := by
      simp [φ,incidence]
    simpa only [form,map_sum,map_mul,map_pow,map_zero,hv,x,y]
      using congrArg γ (form_incidence (s :=s) (b:=b) (e :=e) t)
  let f :lK s b e k →+* E :=eval₂Hom g ![x,y]
  have hf : ∀ p∈Ib s b e k,f p=0:= by
    have hle :Ib s b e k≤RingHom.ker f := by
      apply Ideal.span_le.mpr
      rintro _ ⟨t,ht,rfl⟩
      change f (pairForm s b e k t)=0
      have hcoef (w:Slot s (b t) (e t)) :
          g (pairCoeff k ⟨t,w⟩)=φ (z9v ⟨t,w⟩) := by
        rw [pairCoeff,dite_eq_left (show t≠k from ht),hg]
        change φ (includePair (z9v (⟨⟨t,w⟩,ht⟩:OtherVars s b e k)))= _
        rw [includePair_X]
      simpa [pairForm,form,f,hcoef] using hform t
    exact fun p hp=>hle hp
  let ψ:A →+* E :=Ideal.Quotient.lift _ f hf
  have hψ (a :F) :ψ (algebraMap F A a)=g a := by
    change f (C a)=g a
    simp [f]
  have hψs (c:F) (p:A) :ψ (c•p)=g c*ψ p:= by
    rw [Algebra.smul_def c p,map_mul,hψ]
  have hψu (w:Slot s (b k) (e k)) :ψ (u w)=x^w.2.val*y ^w.1.val := by
    change f ((z9v 0:lK s b e k)^w.2.val*z9v 1^w.1.val)= _
    simp [f]
  have hsum : ∑ w:Slot s (b k) (e k),φ (z9v ⟨k,w⟩)*ψ (u w)=0:= by
    simpa only [form,hψu,mul_assoc] using hform k
  let a (v :ι×ι×Slot s (b k) (e k)) :F:=B.repr (u v.2.2*B v.2.1) v.1
  obtain ⟨den,hden⟩:=IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) a
  choose num hnum using hden
  simp only [Algebra.smul_def] at hnum
  let D:Matrix ι ι (jo s b e) := fun i j =>
    ∑ w:Slot s (b k) (e k),jPair (num (i,j,w))*z9v ⟨k,w⟩
  have hD {M:Type} [za6 M] (ev :jo s b e →+* M) (lift:F →+* M)
      (h : ∀ p:O,ev (jPair p)=lift (algebraMap O F p)) :
      D.map ev=lift (algebraMap O F (den:O))•(Matrix.of fun i j =>
        ∑ w:Slot s (b k) (e k),ev (z9v ⟨k,w⟩)*lift (a (i,j,w))) := by
    apply Matrix.ext
    intro i j
    change ev (D i j)=lift (algebraMap O F (den:O)) *
      ∑ w,ev (z9v ⟨k,w⟩)*lift (a (i,j,w))
    simp only [D,map_sum,map_mul,h,hnum,zxw]
    exact zUo rfl fun w _=> by ring
  let τ:=ε.comp σ
  have hτ (p:O) :τ (jPair p)=z1z (algebraMap O F p) := by
    rw [show τ (jPair p)=ε (σ (includePair p)) from rfl,hfix,hε]
  let M:Matrix ι ι F:= fun i j =>
    -(∑ w:Slot s (b k) (e k),c w*a (i,j,w))
  have hmat :D.map τ=z1z (algebraMap O F (den:O))•M.charmatrix := by
    rw [hD τ z1z hτ]
    congr 1
    apply Matrix.ext
    intro i j
    change (∑ w,τ (z9v ⟨k,w⟩)*z1z (a (i,j,w)))= _
    simp only [zQb,τ,hc,add_mul,zfW,← map_mul,← map_sum]
    rw [zi6 z]
    · rw [ite_eq_left rfl]
      have hz :a (i,j,z)=if i=j then 1 else 0:= by
        change B.repr (u z*B j) i= _
        rw [u_zero,one_mul,Module.Basis.repr_self_apply]
        by_cases hij:i=j
        · subst j; rfl
        · rw [ite_eq_right (Ne.symm hij),ite_eq_right hij]
      rw [hz,Matrix.charmatrix_apply]
      by_cases hij:i=j
      · subst j
        simp [M]
      · simp [M,hij]
    · intro w _ hw
      simp [show w≠zeroSlot s (b k) (e k) from hw]
    · simp
  have hDne :σ D.det≠0:= by
    intro hz
    have he :=τ.map_det D
    change τ D.det=(D.map τ).det at he
    have hzero :τ D.det=0:= by
      change ε (σ D.det)=0
      rw [hz,map_zero]
    rw [hzero,hmat,Matrix.det_smul] at he
    have hn:algebraMap O F (den:O)≠0 :=
      (map_ne_zero_iff _ (zxb O F)).2
        (mem_nonZeroDivisors_iff_ne_zero.mp den.property)
    exact (mul_ne_zero (pow_ne_zero _ (Polynomial.C_ne_zero.mpr hn))
      M.charpoly_monic.ne_zero) he.symm
  have hker : (fun i=>ψ (B i)) ᵥ* (D.map φ)=0:= by
    rw [hD φ g (fun p=>(hg p).symm),Matrix.vecMul_smul]
    suffices h: (fun i=>ψ (B i)) ᵥ* (Matrix.of fun i j =>
        ∑ w:Slot s (b k) (e k),φ (z9v ⟨k,w⟩)*g (a (i,j,w)))=0 by
      rw [h,smul_zero]
    funext j
    rw [Matrix.vecMul_apply_eq_sum,Pi.zero_apply]
    simp only [Matrix.of_apply,zxw]
    rw [Finset.sum_comm]
    have hcol (w:Slot s (b k) (e k)) :
        ∑ i:ι,ψ (B i)*g (a (i,j,w))=ψ (u w)*ψ (B j) := by
      simpa only [a,map_sum,hψs,map_mul,mul_comm (g _) (ψ _)]
        using congrArg ψ (B.sum_repr (u w*B j))
    calc
      _ = ∑ w,φ (z9v ⟨k,w⟩)*(∑ i:ι,ψ (B i)*g (a (i,j,w))) := by
        refine zUo rfl fun w _ => ?_
        rw [zxw]
        exact zUo rfl fun i _=> by ring
      _=(∑ w,φ (z9v ⟨k,w⟩)*ψ (u w))*ψ (B j) := by
        rw [Finset.sum_mul]
        simp only [hcol,mul_assoc]
      _=0:= by rw [hsum,zero_mul]
  have hvec: (fun i=>ψ (B i))≠0:= by
    intro h
    have hz (i:ι) :ψ (B i)=0:=congrFun h i
    have he :=congrArg ψ (B.sum_repr (1 :A))
    simp only [map_sum,hψs,hz,mul_zero,Finset.sum_const_zero,
      map_one,zero_ne_one] at he
  have hdet: (D.map φ).det=0 :=
    Matrix.exists_vecMul_eq_zero_iff.mp ⟨_,hvec,hker⟩
  refine ⟨D.det,?_,hDne⟩
  apply hγ
  rw [map_zero]
  change φ D.det=0
  rw [φ.map_det]
  exact hdet
private def testThird {s b d:ℕ} : Coeff s b d →+*
  zM1 (MY s (caps b s) (orders d) 2) :=
 eval₂Hom ((Polynomial.C.comp (algebraMap (PairCoeffs s (caps b s) (orders d) 2)
  (MY s (caps b s) (orders d) 2))).comp C) genericThird
private theorem testThird_pair {s b d:ℕ} (p:PairCoeffs s (caps b s) (orders d) 2) :
   testThird (includePair p)=z1z (algebraMap _ (MY s (caps b s) (orders d) 2) p) := by
 let F:=MY s (caps b s) (orders d) 2
 have he :testThird.comp (includePair (k :=2)) =
     (z1z:F →+* zM1 F).comp (algebraMap _ F) := by
   apply zXT
   · intro c
     simp [testThird,includePair,F]
   · intro v
     rw [zQb,includePair_X,testThird,eval₂Hom_X',genericThird_other _ v.property]
     rw [zQb,pairCoeff,dite_eq_left v.property]
 exact zLs he p
private theorem testThird_tie_X {s b d:ℕ} (v :bzm s b d) :
  testThird (tie (z9v v))=tied genericThird v := by
 rw [tie,eval₂Hom_X']
 unfold tied
 split_ifs <;> simp [testThird]
theorem survives (s b d:ℕ) (hd:2≤d)
  (hfinite :Module.Finite (MY s (caps b s) (orders d) 2)
    (PairAlgebra s (caps b s) (orders d) 2)) :
  ∃ S:Coeff s b d,incidence s (caps b s) (orders d) S=0∧tie S≠0 :=
 norm_relation tie tie_includePair testThird testThird_pair
  (fun w=>tied (pairCoeff 2) ⟨2,w⟩)
  (fun w=>(testThird_tie_X ⟨2,w⟩).trans (genericThird_tied hd w)) hfinite
end
end qDTrBfa
end
section
namespace qDTrBfa
open q2tSkEc (caps orders)
open private order_ne from ProximityPrize.SubmissionLower.Zg9AXud
theorem proof :qEAs6me.c2 := by
 intro s b d hd
 exact survives s b d hd
  (qVEB2pd.proof s (caps b s) (orders d)
    (fun t=>Nat.pos_of_ne_zero (order_ne hd t)) (zA8 (b+s)) 2).1
end qDTrBfa
end
section
set_option backward.isDefEq.respectTransparency false
namespace qirQQEe
noncomputable section
open scoped BigOperators Classical
open PowerSeries (constantCoeff coeff)
open Polynomial (evalRingHom mapRingHom)
open q2tSkEc (bzm caps orders top)
open qEAs6me (tied topSlot topPoly topPoly_map top_eq_eval)
open qVAMdHe (first rL insertU deformArg rev jet delta)
open qfbIfsd (Slot)
open private liftRoot from ProximityPrize.SubmissionLower.Z6IMoUa
open private topPoly_tied from ProximityPrize.SubmissionLower.ZPRNTid
open private deformArg_map from ProximityPrize.SubmissionLower.ZuY7OPe
variable {s b d:ℕ}
private def tail {M:Type} [CommSemiring M]
   (a :bzm s b d→M) (t:Fin 3) (x v :M) :M :=
 ∑ i:Slot s (caps b s t) (orders d t),
   if i.1.val=orders d t then 0 else
     a ⟨t,i⟩*x^i.2.val*v^(orders d t - i.1.val - 1)
private theorem rev_split {M:Type} [CommSemiring M]
    (a :bzm s b d→M) (t:Fin 3) (x v :M) :
    rev a t x v=(topPoly a t).eval x+v*tail a t x v := by
  rw [top_eq_eval,rev,top,tail,zxw,← zfW]
  apply zUo rfl
  intro i _
  by_cases h:i.1.val=orders d t
  · simp [h]
  · have hi:=i.1.isLt
    have he :v^(orders d t - i.1.val) =
        v^(orders d t - i.1.val - 1)*v := by
      rw [← pow_succ]
      congr 1
      omega
    rw [ite_eq_right h,ite_eq_right h,zero_add,he]
    ac_rfl
private theorem tail_zero {M:Type} [CommSemiring M]
   (a :bzm s b d→M) (t:Fin 3) (x :M) :
   tail a t x 0=jet a t x := by
 rw [tail,jet]
 apply zUo rfl
 intro i _
 by_cases h:i.1.val=orders d t
 · simp [h]
 · by_cases hn:orders d t - i.1.val=1
   · simp [h,hn]
   · have hi:=i.1.isLt
     have he :orders d t - i.1.val - 1≠0:= by omega
     simp [h,hn,zero_pow he]
private theorem rev_map {M N :Type} [CommSemiring M] [CommSemiring N]
  (f :M →+* N) (a :bzm s b d→M) (t:Fin 3) (x v :M) :
  f (rev a t x v)=rev (f ∘ a) t (f x) (f v) := by
 simp only [rev,map_sum,map_mul,map_pow,Function.comp_apply]
private theorem tail_map {M N :Type} [CommSemiring M] [CommSemiring N]
  (f :M →+* N) (a :bzm s b d→M) (t:Fin 3) (x v :M) :
  f (tail a t x v)=tail (f ∘ a) t (f x) (f v) := by
 rw [tail,map_sum,tail]
 apply zUo rfl
 intro i _
 split_ifs <;> simp
private def key (s b d:ℕ) (t:Fin 3) :bzm s b d :=
 ⟨t,topSlot s b d t 0⟩
private theorem tail_deform {M:Type} [CommSemiring M]
    (a :bzm s b d→M) (u e :M) (t:Fin 3) (x v :M) :
    tail (deformArg a u e) t x v=tail a t x v := by
  rw [tail,tail]
  apply zUo rfl
  intro i _
  by_cases h:i.1.val=orders d t
  · simp [h]
  · have hn (j:Fin 3) : (⟨t,i⟩:bzm s b d)≠key s b d j:= by
      intro he
      exact (show (⟨t,i⟩:bzm s b d).2.1.val ≠
        orders d (⟨t,i⟩:bzm s b d).1 from h)
        (he ▸ (show (key s b d j).2.1.val=orders d (key s b d j).1 from rfl))
    have h0: (⟨t,i⟩:bzm s b d)≠first s b d:=hn 0
    have h2 : (⟨t,i⟩:bzm s b d)≠rL s b d:=hn 2
    simp [h,deformArg,tied,insertU,h0,h2]
private theorem top_bump {M:Type} [CommSemiring M]
    (a :bzm s b d→M) (k t:Fin 3) (x e :M) :
    (topPoly (fun r=>a r+if r=key s b d k then e else 0) t).eval x =
      (topPoly a t).eval x+if t=k then e else 0:= by
  simp only [topPoly,Polynomial.eval_finsetSum,Polynomial.eval_monomial,add_mul,
    zfW]
  congr 1
  by_cases h:t=k
  · subst k
    rw [ite_eq_left rfl,zi6 (0:Fin (caps b s t+1))]
    · simp [key]
    · intro j _ hj
      have hn: (⟨t,topSlot s b d t j⟩:bzm s b d)≠key s b d t:= by
        intro he
        exact hj (Fin.ext (congrArg (fun r :bzm s b d=>r.2.2.val) he))
      simp [hn]
    · simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro j _
    have hn: (⟨t,topSlot s b d t j⟩:bzm s b d)≠key s b d k :=
      fun he=>h (congrArg Sigma.fst he)
    simp [hn]
private theorem rev_deform {M:Type} [za6 M]
   (a :bzm s b d→M) (ha :a (first s b d)=0) (u e x v :M) :
   rev (deformArg a u e) 0 x v=rev a 0 x v+u ∧
   rev (deformArg a u e) 1 x v=rev a 1 x v ∧
   rev (deformArg a u e) 2 x v =
     (d:M)*((topPoly a 0).eval x+u)+e+v*tail a 2 x v := by
 have ht (t:Fin 3) :
     (topPoly (deformArg a u e) t).eval x =
     (topPoly (tied (insertU a u)) t).eval x+if t=2 then e else 0 :=
   top_bump (tied (insertU a u)) 2 t x e
 have hi (t:Fin 3) :
     (topPoly (insertU a u) t).eval x=(topPoly a t).eval x+if t=0 then u else 0:= by
   have h:insertU a u=fun r=>a r+if r=key s b d 0 then u else 0:= by
     funext r
     change insertU a u r=a r+if r=first s b d then u else 0
     by_cases hr :r=first s b d
     · simp [insertU,hr,ha]
     · simp [insertU,hr]
   rw [h,top_bump]
 have hf (t:Fin 3) (ht:t≠2) :
     topPoly (tied (insertU a u)) t=topPoly (insertU a u) t:= by
   simp [topPoly,tied,ht]
 refine ⟨?_,?_,?_⟩
 · rw [rev_split,tail_deform,ht,hf 0 (by decide),hi,rev_split]
   simp only [ite_true,show (0:Fin 3)≠2 by decide,ite_false,add_zero]
   ac_rfl
 · rw [rev_split,tail_deform,ht,hf 1 (by decide),hi,rev_split]
   simp only [show (1 :Fin 3)≠2 by decide,show (1 :Fin 3)≠0 by decide,ite_false,
     add_zero]
 · rw [rev_split,tail_deform,ht,topPoly_tied,hi]
   simp
private theorem top_scalar {M:Type} [CommSemiring M]
  (hb:b=0) (a :bzm s b d→M) (x :M) :
  (topPoly a 0).eval x=a (first s b d) := by
 subst b
 simp [topPoly,first]
private theorem series_root {E :Type} [zrb E]
    (p:zM1 (zpm E)) (α:E)
    (h: (p.map constantCoeff).eval α=0)
    (h' : (p.map constantCoeff).derivative.eval α≠0) :
    ∃ x,p.eval x=0∧constantCoeff x= α:= by
  let I:Ideal (zpm E) := .span {zWv}
  have hI:RingHom.ker (constantCoeff (R:=E))=I :=
    PowerSeries.ker_coeff_eq_max_ideal.trans PowerSeries.maximalIdeal_eq_span_X
  have hm (f :zM1 (zpm E)) :
      constantCoeff (f.eval (zMG α)) =
        (f.map constantCoeff).eval α:= by
    rw [← zdm,zr8]
  have h₁:p.eval (zMG α)∈I:= by
    rw [← hI,RingHom.mem_ker,hm,h]
  have h₂:IsUnit (zVv I (p.derivative.eval (zMG α))) := by
    apply IsUnit.map
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    apply isUnit_iff_ne_zero.mpr
    rw [hm,← Polynomial.derivative_map]
    exact h'
  obtain ⟨x,hx,hx'⟩:=liftRoot p (zMG α) h₁ h₂
  rw [← hI,RingHom.mem_ker,map_sub,zr8,sub_eq_zero] at hx'
  exact ⟨x,hx,hx'⟩
private theorem lift_second {E :Type} [zrb E] (a :bzm s b d→E) (α:E)
    (h: (topPoly a 1).eval α=0) (h' : (topPoly a 1).derivative.eval α≠0) :
    ∃ x,rev (zMG ∘ a) 1 x zWv=0 ∧
      constantCoeff x= α:= by
  let A:=zpm E
  let f :E →+* A:=zMG
  let c:A →+* zM1 A:=z1z
  let p:=rev (c ∘ f ∘ a) 1 z7y (c zWv)
  have hp:p.map constantCoeff=topPoly a 1 := by
    change mapRingHom constantCoeff p= _
    dsimp only [p]
    rw [rev_map]
    change rev (mapRingHom constantCoeff ∘ c ∘ f ∘ a) 1
      (Polynomial.X.map constantCoeff) ((c zWv).map constantCoeff)= _
    have hz : (c zWv).map constantCoeff=0:= by
      change (z1z (zWv:zpm E)).map constantCoeff=0
      rw [Polynomial.map_C,PowerSeries.constantCoeff_X,map_zero]
    rw [Polynomial.map_X,hz,rev_split,zero_mul,add_zero]
    have ha :mapRingHom constantCoeff ∘ c ∘ f ∘ a =
        z1z ∘ a := by
      funext r
      change (z1z (f (a r))).map constantCoeff=z1z (a r)
      rw [Polynomial.map_C,zr8]
    rw [ha,← topPoly_map,Polynomial.eval_map,Polynomial.eval₂_C_X]
  rw [← hp] at h h'
  obtain ⟨x,hx,hα⟩:=series_root p α h h'
  refine ⟨x,?_,hα⟩
  change evalRingHom x p=0 at hx
  dsimp only [p] at hx
  rw [rev_map] at hx
  have hC:evalRingHom x ∘ c ∘ f ∘ a=f ∘ a := by
    funext i
    exact zFf
  rw [hC,show evalRingHom x z7y=x from Polynomial.eval_X,
    show evalRingHom x (c zWv)=zWv from zFf] at hx
  exact hx
private theorem chart_residue {E :Type} [zrb E] (a :bzm s b d→E)
   (x v :zpm E) (hv :constantCoeff v=0) (t:Fin 3) :
   constantCoeff (tail (zMG ∘ a) t x v) =
     jet a t (constantCoeff x) := by
 rw [tail_map,hv]
 have ha :constantCoeff ∘ zMG ∘ a=a :=
   funext fun i=>zr8 (a i)
 rw [ha,tail_zero]
theorem proof :qVAMdHe.c2 := by
  intro E _ s b d _ a α ha h₁ h₂ hδ
  obtain ⟨x₀,hx₀,hα⟩:=lift_second a α h₁ h₂
  let A:bzm s b d→zpm E :=zMG ∘ a
  let u₀ := -rev A 0 x₀ zWv
  let T (x v :zpm E) :=tail A 2 x v-(d:zpm E)*tail A 0 x v
  let e₀ := -(zWv*T x₀ zWv)
  have ha₀:A (first s b d)=0:= by simp [A,ha]
  have hT (x v :zpm E) (hv :constantCoeff v=0) :
      constantCoeff (T x v)=delta a (constantCoeff x) := by
    simp only [T,map_sub,map_mul,map_natCast,A,chart_residue a x v hv,delta]
  have he₀:constantCoeff e₀=0:= by simp [e₀]
  have he₁:coeff 1 e₀ = -delta a α:= by
    rw [show e₀= _ from rfl,map_neg,PowerSeries.coeff_one_mul,hT _ _ PowerSeries.constantCoeff_X,
      hα,PowerSeries.coeff_one_X,PowerSeries.constantCoeff_X,mul_zero,add_zero,one_mul]
  have heU:IsUnit (coeff 1 e₀) := by simpa [he₁] using hδ
  let v :=e₀.substInvOfIsUnit heU
  have hv :constantCoeff v=0:=PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hS:=PowerSeries.HasSubst.of_constantCoeff_zero' hv
  let f :zpm E →+* zpm E :=(PowerSeries.substAlgHom (R:=E) hS).toRingHom
  have fX:f zWv=v :=PowerSeries.substAlgHom_X hS
  have fs (z :zpm E) :f z=z.subst v := by
    change (PowerSeries.substAlgHom (R:=E) hS) z= _
    exact congrFun (PowerSeries.coe_substAlgHom (R:=E) hS) z
  have fe :f e₀=PowerSeries.X :=
    (fs _).trans (PowerSeries.subst_substInvOfIsUnit_right _ he₀ heU)
  have fC:f ∘ A=A:= by
    funext i
    exact (PowerSeries.substAlgHom (R:=E) hS).commutes (a i)
  have fc (z :zpm E) :constantCoeff (f z)=constantCoeff z := by
    rw [fs]
    simpa [PowerSeries.constantCoeff_eq] using PowerSeries.constantCoeff_subst_of_constantCoeff_zero hv z
  have htop (x :zpm E) :
      constantCoeff ((topPoly A 0).eval x) =
        (topPoly a 0).eval (constantCoeff x) := by
    rw [← zdm,topPoly_map]
    have h:constantCoeff ∘ A=a :=
      funext fun i=>zr8 (a i)
    rw [h]
  have hu₀:constantCoeff u₀ = -(topPoly a 0).eval α:= by
    dsimp only [u₀]
    rw [rev_split,map_neg,map_add,map_mul,
      PowerSeries.constantCoeff_X,zero_mul,add_zero,htop,hα]
  have hrev : ∀ t,rev (deformArg A u₀ e₀) t x₀ zWv=0:= by
    obtain ⟨h0,h1,h2⟩:=rev_deform A ha₀ u₀ e₀ x₀ zWv
    intro t
    fin_cases t
    · exact h0.trans (add_neg_cancel _)
    · exact h1.trans hx₀
    · refine h2.trans ?_
      dsimp only [u₀,e₀,T]
      rw [rev_split]
      ring
  have hfinal (t:Fin 3) :rev (deformArg A (f u₀) zWv) t (f x₀) v=0:= by
    have hm:=congrArg f (hrev t)
    rwa [rev_map,show f ∘ deformArg A u₀ e₀=deformArg (f ∘ A) (f u₀) (f e₀) from
      funext (deformArg_map f A u₀ e₀),fC,fe,fX,map_zero] at hm
  have hEf : -(v*T (f x₀) v)=PowerSeries.X:= by
    rw [← fe]
    simp only [e₀,T,map_neg,map_mul,map_sub,map_natCast,fX,tail_map,fC]
  have hvne :v≠0:= by
    intro h
    have hz : (zWv:zpm E)=0:= by simpa [h] using hEf.symm
    exact PowerSeries.X_ne_zero hz
  refine ⟨f x₀,f u₀,v,(fc _).trans hα,(fc _).trans hu₀,hv,hvne,?_,hfinal⟩
  intro hb
  have hu:f u₀ = -rev A 0 (f x₀) v := by
    dsimp only [u₀]
    rw [map_neg,rev_map,fC,fX]
  have htop₀: (topPoly A 0).eval (f x₀)=0:= by
    exact (top_scalar hb _ _).trans ha₀
  have hαf :constantCoeff (f x₀)= α:=(fc _).trans hα
  have hvc : -(coeff 1 v*delta a α)=1 := by
    have hh:=congrArg (coeff 1) hEf
    simpa only [map_neg,PowerSeries.coeff_one_mul,hT _ _ hv,hαf,hv,mul_zero,add_zero,
      PowerSeries.coeff_one_X] using hh
  have hv' : coeff 1 v = -(delta a α)⁻¹:= by
    rw [← neg_one_mul]
    exact (eq_mul_inv_iff_mul_eq₀ hδ).2 (neg_eq_iff_eq_neg.mp hvc)
  rw [hu,rev_split,htop₀,zero_add,map_neg,PowerSeries.coeff_one_mul]
  dsimp only [A]
  rw [chart_residue a (f x₀) v hv,hαf,hv,mul_zero,add_zero,hv']
  rw [neg_mul,neg_neg,mul_comm,div_eq_mul_inv]
end
end qirQQEe
end
section
set_option backward.isDefEq.respectTransparency false
namespace qgDJA5b
noncomputable section
open Polynomial qNu3xvc P5_7_1_7_4_3_4 qfbIfsd
open q7P6kQb
open qZu9hjc (atPair)
open qApzjua (pairEval pairEval_comp root_coordinates root_hom_ext root_zero)
open qLXroAb (dx)
open qfzuawb (map₂ coeff_map₂)
open qJm9rWb (charpoly_embeddings)
open private at_map dx_map dy_map dx_linear dy_linear from ProximityPrize.SubmissionLower.ZJVClxb
open cu (L)
open scoped BigOperators
private theorem rebuild {B:Type} [zrb B] (p:B[X][X]) {b d s :ℕ}
    (hd:p.natDegree≤d) (hb : ∀ i≤d,(p.coeff i).natDegree≤b+(d-i)*s) :
    (∑ i:Slot s b d,
      monomial i.1.val (monomial i.2.val ((p.coeff i.1.val).coeff i.2.val)))=p:= by
  rw [zla]
  calc
    _ = ∑ i:Fin (d+1),monomial i.val (p.coeff i.val) := by
      apply zUo rfl
      intro i _
      change (∑ j:Fin (b+(d-i.val)*s+1),
        monomial i.val (monomial j.val ((p.coeff i.val).coeff j.val)))= _
      rw [← map_sum (monomial i.val)]
      apply congrArg (monomial i.val)
      exact (zdx (fun j=>monomial j ((p.coeff i.val).coeff j)) _).trans
        (as_sum_range' _ _ (zB1 (hb _ (Nat.le_of_lt_succ i.isLt)))).symm
    _=p:= by
      exact (zdx (fun i=>monomial i (p.coeff i)) _).trans
        (as_sum_range' _ _ (zB1 hd)).symm
private theorem mapped_bounds {E B:Type} [zrb E] [zrb B] (j:E →+* B)
   {p:E[X][X]} {b d s :ℕ} (hd:p.natDegree≤d)
   (hb : ∀ i,(p.coeff i).natDegree+i*s≤b+d*s∨p.coeff i=0) :
   (map₂ j p).natDegree≤d ∧
     ∀ i≤d,((map₂ j p).coeff i).natDegree≤b+(d-i)*s := by
 refine ⟨natDegree_map_le.trans hd,fun i hi => ?_⟩
 change ((p.map (mapRingHom j)).coeff i).natDegree≤_
 rw [coeff_map]
 apply natDegree_map_le.trans
 change (p.coeff i).natDegree≤_
 rcases hb i with h | h
 · rw [show d*s=(d-i)*s+i*s by rw [← Nat.add_mul,Nat.sub_add_cancel hi]] at h
   omega
 · simp [h]
variable {E :Type} [zrb E] [zZE L E] {A:Equation E}
private theorem bmn (C:Pencil A) :block C 0=map₂ RatFunc.C A.f := by
 have h:=mapped_bounds (RatFunc.C:E →+* tu E) le_rfl A.weight
 rw [← rebuild _ h.1 h.2]
 apply zUo rfl
 intro i _
 simp [afe,actual,const₂,coeff_map₂,RatFunc.algebraMap_C]
private theorem dzt (C:Pencil A) :block C 1 =
   map₂ RatFunc.C C.num - const₂ RatFunc.X*map₂ RatFunc.C C.den:= by
 let j:E →+* tu E :=RatFunc.C
 let n:=map₂ j C.num
 let d:=map₂ j C.den
 let c: (tu E)[X][X] :=const₂ RatFunc.X
 have hn:=mapped_bounds j C.num_weight.1
   (b:=A.b+A.s+1) (s :=A.s) (by
     simpa only [Nat.add_assoc,zWn,Nat.add_comm] using C.num_weight.2)
 have hd:=mapped_bounds j C.den_weight.1
   (b:=A.b+A.s+1) (s :=A.s) (by
     simpa only [Nat.add_assoc,zWn,Nat.add_comm] using C.den_weight.2)
 change block C 1=n - c*d
 have hg: (n - c*d).natDegree≤A.d :=
   (natDegree_sub_le _ _).trans
     (max_le hn.1 ((natDegree_C_mul_le _ _).trans hd.1))
 have hb (i:ℕ) (hi:i≤A.d) :
     ((n - c*d).coeff i).natDegree≤A.b+A.s+1+(A.d-i)*A.s := by
   rw [show c=z1z (z1z RatFunc.X) from rfl,coeff_sub,coeff_C_mul]
   exact (natDegree_sub_le _ _).trans
     (max_le (hn.2 i hi) ((natDegree_C_mul_le _ _).trans (hd.2 i hi)))
 rw [← rebuild _ hg hb]
 apply zUo rfl
 intro i _
 suffices he :afe C ⟨1,i⟩=((n - c*d).coeff i.1.val).coeff i.2.val by rw [he]
 let a :=(C.num.coeff i.1.val).coeff i.2.val
 let b:=(C.den.coeff i.1.val).coeff i.2.val
 rw [show c=z1z (z1z RatFunc.X) from rfl,coeff_sub,coeff_C_mul,
   coeff_sub,coeff_C_mul]
 simp only [n,d,coeff_map₂]
 change algebraMap E[X] (tu E) ((z1z (z1z a) -
   z1z (z1z b)*z1z (z7y:E[X])).coeff 0) =
     j a - RatFunc.X*j b
 rw [← Polynomial.C_mul,← Polynomial.C_sub,coeff_C_zero,map_sub,map_mul,
   RatFunc.algebraMap_C,RatFunc.algebraMap_C,RatFunc.algebraMap_X,mul_comm (j b)]
theorem proof :q7P6kQb.c1 := by
  classical
  intro E _ _ A _ C _
  let _:=C.base.toAlgebra
  let _:=C.finite
  let _:=C.separable
  let B:=tu E
  let Ω:=Closure E
  let k :=algebraMap B Ω
  let j:E →+* B:=RatFunc.C
  let _:Infinite E :=Infinite.of_injective _ (algebraMap L E).injective
  let _:Infinite B:=Infinite.of_injective _ j.injective
  let H :=EC A →ₐ[B] Ω
  let e :=(Fintype.equivFin H).symm
  let x (σ:H) :=σ (amm A)
  let y (σ:H) :=σ (jU A false)
  let u:B:=RatFunc.X
  let t:=C.base RatFunc.X
  let m:=map₂ j
  let ev :=KM A false
  have hseed (σ:H) :σ.toRingHom.comp (seed A)=k.comp j:= by
    apply RingHom.ext
    intro a
    exact (congrArg σ (C.base_seed a).symm).trans (σ.commutes (j a))
  have ht (σ:H) :k u=σ t:=(σ.commutes RatFunc.X).symm
  have hEval (σ:H) (p:E[X][X]) :
      atPair k (x σ) (y σ) (m p)=σ (ev p) := by
    change pairEval k (x σ) (y σ) (m p)= _
    calc
      _=pairEval (k.comp j) (x σ) (y σ) p:=at_map j k _ _ p
      _ = _:= by
        have he :=zLs
          (pairEval_comp σ.toRingHom (seed A) (amm A) (jU A false)) p
        rw [root_coordinates] at he
        rw [← hseed σ]
        exact he.symm
  have hCut (σ:H) (p q:E[X][X]) :
      atPair k (x σ) (y σ) (m p-Polynomial.C (z1z u)*m q) =
        σ (ev p - t*ev q) := by
    let f :=pairEval k (x σ) (y σ)
    have hc:f (z1z (z1z u))=k u:= by simp [f,pairEval]
    change f (m p-Polynomial.C (z1z u)*m q)= _
    rw [map_sub,map_mul,hc,ht σ,show f (m p)= _ from hEval σ p,
      show f (m q)= _ from hEval σ q,map_sub,map_mul]
  have hGauge (σ:H) :gaugeAt C (y σ)=σ (P5_7_1_7_4_3_4.gauge A C.tilt) := by
    have hc:=zLs (hseed σ) (algebraMap L E C.tilt)
    change σ (seed A (algebraMap L E C.tilt))=k (j (algebraMap L E C.tilt)) at hc
    simp only [gaugeAt,P5_7_1_7_4_3_4.gauge,constant,map_add,map_one,map_mul,hc,y]
    rfl
  refine ⟨{
    size :=Fintype.card H
    point := fun i=>(x (e i),y (e i))
    value := fun i=>e i (relativePolar C)
    distinct := ?_
    realized:= fun i=>⟨(e i).toRingHom,RingHom.ext (e i).commutes,rfl,rfl⟩
    simple := ?_
    zero₀ := ?_
    zero₁ := ?_
    unitGauge := ?_
    product := ?_ }⟩
  · intro i l h
    apply e.injective
    exact AlgHom.coe_ringHom_injective
      (root_hom_ext ((hseed (e i)).trans (hseed (e l)).symm)
        (congrArg Prod.fst h) (congrArg Prod.snd h))
  · intro i
    let σ:=e i
    change atPair k (x σ) (y σ) (dx (block C 0)) *
        atPair k (x σ) (y σ) (block C 1).derivative -
      atPair k (x σ) (y σ) (block C 0).derivative *
        atPair k (x σ) (y σ) (dx (block C 1))≠0
    have h0:block C 0=m A.f :=bmn C
    have h1 :block C 1=m C.num-Polynomial.C (z1z u)*m C.den :=
      dzt C
    have hdx (p:E[X][X]) :dx (m p)=m (dx p) :=dx_map j p
    have hdy (p:E[X][X]) : (m p).derivative=m p.derivative :=dy_map j p
    rw [h0,h1,dx_linear u (m C.den) (m C.num),dy_linear u (m C.den) (m C.num),hdy A.f]
    simp only [hdx,hdy,hEval,hCut,← map_mul,← map_sub]
    exact (map_ne_zero_iff σ σ.injective).mpr (q4izpTc.proof A C)
  · intro i
    rw [← aMq,bmn]
    change atPair k (x (e i)) (y (e i)) (m A.f)=0
    rw [hEval,root_zero,map_zero]
  · intro i
    rw [← aMq,dzt]
    change atPair k (x (e i)) (y (e i)) (m C.num-Polynomial.C (z1z u)*m C.den)=0
    rw [hCut]
    have hz :ev C.num=t*ev C.den:=((eq_div_iff C.den_ne).mp C.base_X).symm
    rw [hz,sub_self,map_zero]
  · intro i
    rw [hGauge]
    exact (map_ne_zero_iff (e i) (e i).injective).mpr C.gauge_ne
  · change (Algebra.lmul B (EC A) (relativePolar C)).charpoly.map k= _
    rw [charpoly_embeddings]
    symm
    exact Fintype.prod_equiv e _ _ (fun _=>rfl)
end
end qgDJA5b
end
end
