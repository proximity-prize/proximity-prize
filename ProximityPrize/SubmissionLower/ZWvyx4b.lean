import ProximityPrize.SubmissionLower.ZeoK8Ne
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qWIOgVd
noncomputable section
open Polynomial
open P5 (K p)
open cu (L FX jz)
open P5_7_7 (Dg phys embed seedDerivative)
open qGnV2ac (atPair coeff_seedDerivative)
open q7kdBxd (Input)
private def fiber (F:Dg) (z :K) :FX[X] :=
 (embed F).map (evalRingHom (jz z))
private abbrev changeFiber {a :L} (D:Chart a) (u v :FX) (huv :u*v=1) :FX[X] ≃+* FX[X] :=
 (mapEquiv D.changeX).trans (scaleY u v huv)
private theorem fiber_repr {a :L} (D:Chart a) {F G:Dg} (z :K)
   {m u v :FX} (huv :u*v=1)
   (h : ∀ i,(embed G).coeff i =
     C (m*u^i)*((embed F).coeff i).map D.changeX.toRingHom) :
   fiber G z=C m*changeFiber D u v huv (fiber F z) := by
 ext i
 have hd:D.changeX.toRingHom (jz z)=jz z :=D.constant _
 have he :=eval_map_apply (p:=(embed F).coeff i) D.changeX.toRingHom (jz z)
 rw [hd] at he
 change (fiber G z).coeff i=(C m*scaleY u v huv ((fiber F z).map D.changeX.toRingHom)).coeff i
 simp only [coeff_C_mul,scaleY_coeff,fiber,coeff_map,h,map_mul,coe_evalRingHom,eval_C,he]
 ring
private theorem fiber_deriv (F:Dg) (z :K) :
  fiber F.derivative z=(fiber F z).derivative := by
 simp only [fiber,embed,coe_mapRingHom,derivative_map]
private theorem deriv_change {a :L} (D:Chart a) (u v :FX) (huv :u*v=1) (m:FX)
   (f :FX[X]) :
   (C m*changeFiber D u v huv f).derivative =
     C (m*u)*changeFiber D u v huv f.derivative := by
 change (C m*scaleY u v huv (f.map D.changeX.toRingHom)).derivative =
   C (m*u)*scaleY u v huv (f.derivative.map D.changeX.toRingHom)
 rw [derivative_C_mul,scaleY_apply,derivative_comp,derivative_C_mul_X,scaleY_apply,
   derivative_map,map_mul]
 ring
private theorem eval_change {a :L} (D:Chart a) (u v :FX) (huv :u*v=1)
  (f :FX[X]) (t:FX) :
  (changeFiber D u v huv f).eval (v*D.changeX t)=D.changeX (f.eval t) := by
 change (scaleY u v huv (f.map D.changeX.toRingHom)).eval _ = _
 rw [scaleY_apply,eval_comp]
 rw [show (C u*(Polynomial.X:FX[X])).eval (v*D.changeX t)=D.changeX t by
  rw [eval_mul,eval_C,eval_X,← mul_assoc,huv,one_mul]]
 exact eval_map_apply (p:=f) D.changeX.toRingHom t
private theorem pair_fiber (F:Dg) (z :K) (P Q:L[X]) :
  atPair F z P Q=(fiber F z).eval (phys P/phys Q) :=
 eval₂_eq_eval_map _
theorem at_pair {J:Input} {a :L} {D:Chart a} (R:Rechart J D) (z :K)
   (P Q P' Q' : L[X])
   (h:phys P' / phys Q' = x^J.s*D.changeX (phys P/phys Q)) :
   atPair R.F z P' Q' = R.scalar*D.changeX (atPair J.F z P Q) ∧
   atPair R.F.derivative z P' Q' =
     (R.scalar*(x^J.s)⁻¹)*D.changeX (atPair J.F.derivative z P Q) ∧
   atPair (seedDerivative R.F) z P' Q' =
     R.scalar*D.changeX (atPair (seedDerivative J.F) z P Q) := by
 let v :=x^J.s
 have hv :=pow_ne_zero J.s x_ne
 have huv :v⁻¹*v=1 :=inv_mul_cancel₀ hv
 have he :=fiber_repr D z huv R.coeff
 have hs (i:ℕ) : (embed (seedDerivative R.F)).coeff i =
     C (R.scalar*(v⁻¹)^i)*((embed (seedDerivative J.F)).coeff i).map D.changeX.toRingHom:= by
   have hd:=congrArg derivative (R.coeff i)
   simpa only [embed_coeff,coeff_seedDerivative,derivative_C_mul,derivative_map,v] using hd
 change phys P' / phys Q' = v*D.changeX (phys P/phys Q) at h
 simp only [pair_fiber,h,he,fiber_repr D z huv hs,fiber_deriv,deriv_change,eval_mul,
   eval_C,eval_change]
 exact ⟨trivial,rfl,trivial⟩
private theorem bD9 {A:Type*} [CommRing A] [IsDomain A] [CharP A p]
   {f :A[X]} {l:ℕ} (hd:f.natDegree=l) (hl:2≤l) (hp:l<p) :
   f.derivative.natDegree=l-1 := by
 have hn: (l:A)≠0 :=
   fun h=>(not_le_of_gt hp) (Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff A p l).mp h))
 apply natDegree_eq_of_le_of_coeff_ne_zero
 · exact (natDegree_derivative_le _).trans (hd ▸ le_rfl)
 have hc:f.coeff l≠0:= by
   rw [← hd]
   exact leadingCoeff_ne_zero.mpr fun h=> by simp [h] at hd; omega
 rw [coeff_derivative,← Nat.cast_succ,show (l-1)+1=l by omega,show (l-1).succ=l by omega]
 exact mul_ne_zero hc hn
private theorem regular_fiber {F:Dg} {l:ℕ} (hd:F.natDegree=l)
    (hl:2≤l) (hp:l<p) (z :K) :
    ((embed F).resultant (embed F.derivative)).eval (jz z)≠0 ↔
      (fiber F z).natDegree=l∧IsCoprime (fiber F z) (fiber F z).derivative := by
  let _:CharP FX p:=charP_of_injective_ringHom jz.injective p
  let _:CharP FX[X] p:=charP_of_injective_ringHom C_injective p
  have hF: (embed F).natDegree=l:=(embed_degree F).trans hd
  have hD: (embed F.derivative).natDegree=l-1 := by
    rw [show embed F.derivative=(embed F).derivative by
      simp only [embed,coe_mapRingHom,derivative_map]]
    exact bD9 hF hl hp
  have hres : ((embed F).resultant (embed F.derivative)).eval (jz z) =
      (fiber F z).resultant (fiber F z).derivative l (l-1) := by
    rw [← fiber_deriv,fiber,fiber,resultant_map_map,hF,hD]
    rfl
  rw [hres]
  have hb: (fiber F z).natDegree≤l:= by
    rw [← hF]
    exact natDegree_map_le
  constructor
  · intro hn
    have hf : (fiber F z).natDegree=l:= by
      by_contra! hf
      have hlt:=lt_of_le_of_ne hb hf
      have hlt' : (fiber F z).derivative.natDegree<l-1 := by
        have :=natDegree_derivative_le (fiber F z)
        omega
      exact hn (resultant_eq_zero_of_lt_lt _ _ _ _ hlt hlt')
    have hd' := bD9 hf hl hp
    rw [← hd',← hf] at hn
    refine ⟨hf,?_⟩
    by_contra hn'
    exact hn (resultant_eq_zero_iff.mpr
      ⟨Or.inl (fun hz=> by simp [hz] at hf; omega),hn'⟩)
  · rintro ⟨hf,hc⟩
    have hd' := bD9 hf hl hp
    rw [← hd',← hf]
    exact resultant_ne_zero _ _ hc
theorem regular_ordinate {J:Input} {a :L} {D:Chart a} (R:Rechart J D) (z :K)
  (h: ((embed J.F).resultant (embed J.F.derivative)).eval (jz z)≠0) :
  ((embed R.F).resultant (embed R.F.derivative)).eval (jz z)≠0:= by
 obtain ⟨hd,hc⟩:=(regular_fiber J.Ca.jU J.Ca.two_le J.Ca.tame z).mp h
 apply (regular_fiber R.Ca.jU R.Ca.two_le R.Ca.tame z).mpr
 let u:=(x^J.s)⁻¹
 have hu:u≠0:=inv_ne_zero (pow_ne_zero _ x_ne)
 have huv :u*x^J.s=1 :=inv_mul_cancel₀ (pow_ne_zero _ x_ne)
 have he :=fiber_repr D z huv R.coeff
 rw [he,deriv_change]
 refine ⟨?_,(isCoprime_mul_units_left (R.scalar_ne.isUnit.map C)
  ((mul_ne_zero R.scalar_ne hu).isUnit.map C) _ _).mpr (hc.map (changeFiber D u _ huv).toRingHom)⟩
 rw [natDegree_C_mul R.scalar_ne]
 change (scaleY u _ huv ((fiber J.F z).map D.changeX.toRingHom)).natDegree=J.l
 rw [scaleY_apply,natDegree_comp,natDegree_C_mul hu,natDegree_X,
  mul_one,natDegree_map_eq_of_injective D.changeX.injective,hd]
end
end qWIOgVd
