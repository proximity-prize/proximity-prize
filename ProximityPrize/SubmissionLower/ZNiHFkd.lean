import ProximityPrize.SubmissionLower.ZocsBpe
import ProximityPrize.SubmissionLower.Zay1XCa
set_option Elab.async false
namespace qU4m8Td
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K)
open cu (L j9)
open E7 (CurvePlace)
open qb0hmCe (CurveModel)
open q1kuFjb (IntSeries residue Ua map_liftAt liftAt_reduce expansion_coeff)

open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet Variation)
open qxPDCsa
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
private theorem pair_outside {bad:Set L} (h:bad.Finite) :
   ∃ a :Fin 2→L,Function.Injective a ∧ ∀ i,a i∉bad:= by
 obtain ⟨a,ha⟩:=h.exists_notMem
 obtain ⟨b,hb⟩:=(h.union (Set.finite_singleton a)).exists_notMem
 have hba :b≠a := fun he=>hb (Or.inr he)
 refine ⟨![a,b],?_,?_⟩
 · intro i j hij
   fin_cases i <;> fin_cases j
   · rfl
   · exact (hba hij.symm).elim
   · exact (hba hij).elim
   · rfl
 · intro i
   fin_cases i
   · exact ha
   · exact fun he=>hb (Or.inl he)
private theorem map_evaluation {R T:Type} [CommSemiring R] [CommSemiring T]
  (m:R →+* T) (g:R[X]) (u:R) :
  m (g.eval u)=(g.map m).eval (m u) := by
 rw [eval_map,eval₂_hom]
private theorem eval_bound {E :Type} [Field E] [Algebra L E]
  (v :CurvePlace L E) (g:E[X][X]) (r :L) {b:ℤᵐ⁰}
  (h : ∀ i j,v.value ((g.coeff i).coeff j)≤b) :
  BoundedAt v.value (g.eval (C (algebraMap L E r))) b:= by
 intro j
 simp only [eval_eq_sum,Polynomial.sum_def,← map_pow,finsetSum_coeff,coeff_mul_C]
 apply v.value.map_sum_le
 intro i _
 rw [map_mul]
 have hc (a :L) :v.value (algebraMap L E a)≤1 := by
  by_cases ha :a=0
  · simp [ha]
  exact (v.on_constants a ha).le
 exact (mul_le_mul' (h i j) (hc (r^i))).trans_eq (mul_one _)
private theorem finite_degree (F:Sheet Cq z S) {D W:ℕ} (hw:F.weight D W) (a :L) :
   (finiteRef F a).natDegree≤W:= by
 rw [finiteRef,eval_eq_sum_range]
 apply natDegree_sum_le_of_forall_le
 intro j _
 rw [← map_pow]
 apply (natDegree_mul_C_le _ _).trans
 by_cases hj:F.f.coeff j=0
 · simp [hj]
 · exact (Nat.le_add_right _ _).trans (hw j hj)
private theorem finite_bound (F:Sheet Cq z S) (a :L) :Bound F (finiteRef F a) 1 := by
 intro v
 simpa only [finiteRef,one_mul] using
  eval_bound v F.f a (qrezXJe.sheet_bound v.value F.f)
theorem reduce_finite (F:Sheet Cq z S) {γ:K} (hγ:γ∈F.marks) (r :L) :
   reduce (F.atPlace γ hγ) (finiteRef F r)=(specialize F hγ).eval (C r) := by
 let a :=F.atPlace γ hγ
 have hf (i j:ℕ) : (Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰)
     (a ((F.f.coeff i).coeff j))≤1 :=
   (F.value γ hγ _).symm ▸ F.integral γ hγ i j
 let g:=Ua a F.f hf
 let eqv :=LaurentSeries.powerSeriesEquivSubring L
 let u:IntSeries :=eqv (PowerSeries.C r)
 have hu:IntSeries.subtype u=a (algebraMap L Cq.E r) := by
   change ((eqv (PowerSeries.C r) :IntSeries) :LaurentSeries L)= _
   rw [LaurentSeries.powerSeriesEquivSubring_coe_apply,a.commutes,
     LaurentSeries.algebraMap_apply,PowerSeries.coe_C]
 have hr :residue u=r := by
   change PowerSeries.constantCoeff (eqv.symm (eqv (PowerSeries.C r)))= _
   rw [RingEquiv.symm_apply_apply,PowerSeries.constantCoeff_C]
 have hmap :=map_liftAt a F.f hf
 change g.map (mapRingHom IntSeries.subtype)=F.f.map (mapRingHom a.toRingHom) at hmap
 have hcoe : (g.eval (C u)).map IntSeries.subtype=(finiteRef F r).map a.toRingHom:= by
   change mapRingHom IntSeries.subtype (g.eval (C u)) =
     mapRingHom a.toRingHom (F.f.eval (C (algebraMap L Cq.E r)))
   rw [map_evaluation,map_evaluation,hmap,coe_mapRingHom,coe_mapRingHom,map_C,map_C,hu]
   rfl
 have hspec :g.map (mapRingHom residue)=specialize F hγ:=liftAt_reduce a F.f hf
 have hred:=map_evaluation (mapRingHom residue) g (C u)
 rw [coe_mapRingHom,hspec,map_C,hr] at hred
 rw [← hred]
 apply Polynomial.ext
 intro j
 have hc:=congrArg (fun f : (LaurentSeries L)[X]=>f.coeff j) hcoe
 simp only [coeff_map,Subring.subtype_apply,AlgHom.toRingHom_eq_coe] at hc
 rw [reduce,coeff_map,q1kuFjb.fWQ,hc,expansion_coeff,coeff_C_zero]
 rfl
private theorem specialize_ne (F:Sheet Cq z S) {γ:K} (hγ:γ∈F.marks) :
  specialize F hγ≠0:= by
 intro h
 have hc:=congrArg
  (fun f :L[X][X]=>(f.coeff F.d).coeff (F.f.coeff F.d).natDegree) h
 rw [specialize,expansion_coeff,coeff_natDegree,F.normalized,map_one] at hc
 simp at hc
private theorem primitive_slice_ne (f :L[X][X]) (x :L) :
  f.primPart.map (evalRingHom x)≠0:= by
 intro h
 let t:L[X] :=Polynomial.X - C x
 have hd:Polynomial.C (R:=L[X]) t∣f.primPart:= by
  apply (C_dvd_iff_dvd_coeff t f.primPart).mpr
  intro i
  apply dvd_iff_isRoot.mpr
  have hi:=congrArg (fun g:L[X]=>g.coeff i) h
  rwa [coeff_map,coeff_zero] at hi
 have hc:=dvd_content_iff_C_dvd.mpr hd
 rw [content_primPart] at hc
 exact not_isUnit_X_sub_C x (isUnit_of_dvd_one hc)
private theorem content_order (f :L[X][X]) (hf :f≠0) (a x :L)
    (h: (f.primPart.map (evalRingHom x)).eval a≠0) :
    (f.eval (C a)).rootMultiplicity x=f.content.rootMultiplicity x := by
  have hval : (f.primPart.eval (C a)).eval x≠0:= by
    rw [show (f.primPart.eval (C a)).eval x =
        (f.primPart.map (evalRingHom x)).eval a by
      simpa only [coe_evalRingHom,eval_C] using
        map_evaluation (evalRingHom x) f.primPart (C a)]
    exact h
  have hp:f.primPart.eval (C a)≠0:= fun hz=>hval (by simp [hz])
  conv_lhs=>rw [f.eq_C_content_mul_primPart]
  rw [eval_mul,eval_C,rootMultiplicity_mul (mul_ne_zero (content_eq_zero_iff.ne.mpr hf) hp),
    rootMultiplicity_eq_zero hval,add_zero]
private theorem finite_pair {F:Sheet Cq z S} (V:Variation F) :
    ∃ a :Fin 2→L,Function.Injective a∧(∀ i,finiteRef F (a i)≠0) ∧
      (∀ γ∈V.marks,∀ i,j9 (S γ)≠C (a i)) ∧
      ∀ γ (hγ:γ∈V.marks) x,(V.den γ).eval x=0 → ∀ i,
        (reduce (F.atPlace γ (V.Bp hγ)) (finiteRef F (a i))).rootMultiplicity x =
          (contentAt F (V.Bp hγ)).rootMultiplicity x := by
  let bad0:Set L := {a | finiteRef F a=0}
  have h0:bad0.Finite :=(finite_setOfPred_isRoot F.irreducible.ne_zero).preimage
    (C_injective.comp (algebraMap L Cq.E).injective).injOn
  let bad1 :Set L := ↑(V.marks.image fun γ=>(j9 (S γ)).coeff 0)
  let bad (γ:V.marks) (x :L) :Set L :=
    {a | ((specialize F (V.Bp γ.property)).primPart.map (evalRingHom x)).IsRoot a}
  let bad2 := ⋃ γ:V.marks,⋃ x ∈ {x | (V.den γ).IsRoot x},bad γ x
  have h2 :bad2.Finite :=Set.finite_iUnion fun γ =>
    (finite_setOfPred_isRoot (V.den_ne γ γ.property)).biUnion fun x _ =>
      finite_setOfPred_isRoot (primitive_slice_ne _ x)
  obtain ⟨a,ha,hout⟩:=pair_outside ((h0.union (Finset.finite_toSet _)).union h2 :
    (bad0∪bad1∪bad2).Finite)
  refine ⟨a,ha,fun i hi=>hout i (Or.inl (Or.inl hi)),?_,?_⟩
  · intro γ hγ i he
    apply hout i
    exact Or.inl (Or.inr (mem_image.mpr ⟨γ,hγ,by rw [he,coeff_C_zero]⟩))
  · intro γ hγ x hx i
    rw [reduce_finite]
    exact content_order _ (specialize_ne F (V.Bp hγ)) (a i) x fun he =>
      hout i (Or.inr (Set.mem_iUnion.mpr ⟨⟨γ,hγ⟩,Set.mem_biUnion hx he⟩))
private theorem infinity_coeff (F:Sheet Cq z S) (D i:ℕ) :
   (Zq F D).coeff i =
     (F.f.coeff i).reflect ((F.f.support.sup fun k=>(F.f.coeff k).natDegree+k*D)-i*D) := by
 rw [Zq,Polynomial.sum_def,finsetSum_coeff,Finset.sum_eq_single i]
 · rw [coeff_monomial_same]
 · intro b _ hb
   rw [coeff_monomial_of_ne _ (Ne.symm hb)]
 · intro hi
   rw [coeff_monomial_same,notMem_support_iff.mp hi,reflect_zero]
private theorem infinity_bound (F:Sheet Cq z S) (D:ℕ) (a :L) :
  Bound F (infinityRef F D a) 1 := by
 intro v
 simp only [infinityRef,one_mul]
 apply eval_bound
 intro i j
 rw [infinity_coeff,coeff_reflect]
 exact qrezXJe.sheet_bound v.value F.f _ _
private theorem infinity_pair (F:Sheet Cq z S) (D:ℕ) :
   ∃ b:Fin 2→L,Function.Injective b ∧ ∀ i,(infinityRef F D (b i)).coeff 0≠0:= by
 let g:=(Zq F D).map (evalRingHom (0:Cq.E))
 have hs :F.f.support.Nonempty :=nonempty_support_iff.mpr F.irreducible.ne_zero
 obtain ⟨i,hi,hmax⟩:=exists_mem_eq_sup F.f.support hs
   (fun k=>(F.f.coeff k).natDegree+k*D)
 have hg:g≠0:= by
   intro hz
   have hc:=congrArg (fun f :Cq.E[X]=>f.coeff i) hz
   simp only [g,coeff_map,coe_evalRingHom,← coeff_zero_eq_eval_zero,infinity_coeff,
     coeff_reflect,revAt_zero,hmax,Nat.add_sub_cancel,coeff_natDegree,coeff_zero] at hc
   exact (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hi)) hc
 obtain ⟨b,hb,hout⟩:=pair_outside ((finite_setOfPred_isRoot hg).preimage
   (algebraMap L Cq.E).injective.injOn)
 refine ⟨b,hb,fun j h=>hout j ?_⟩
 change g.eval (algebraMap L Cq.E (b j))=0
 rw [infinityRef,coeff_zero_eq_eval_zero] at h
 simpa only [g,coe_evalRingHom,eval_C] using
   (map_evaluation (evalRingHom (0:Cq.E)) (Zq F D)
     (C (algebraMap L Cq.E (b j)))).symm.trans h
theorem proof :qxPDCsa.c2 := by
 intro q Cq z S F V D W h
 obtain ⟨a,ha,hne,hav,hc⟩:=finite_pair V
 obtain ⟨b,hb,hi⟩:=infinity_pair F D
 exact ⟨⟨a,b,ha,hb,hne,fun i=>finite_degree F h (a i),
  fun i=>finite_bound F (a i),hi,fun i=>infinity_bound F D (b i),hav,hc⟩⟩
end
end qU4m8Td
