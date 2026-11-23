import ProximityPrize.SubmissionLower.ZQ2Yete
import ProximityPrize.SubmissionLower.ZsE91Ed
set_option Elab.async false
set_option autoImplicit true
open Polynomial renaming coe_eval₂RingHom→qz0,eval₂RingHom→qz1
open RingHom renaming comp_apply→qz2
namespace qhFwyvc
noncomputable section
open Polynomial
open P5 (K)
open cu (L FX)
open E7 (CurvePlace)
open P5_7_7 (phys)
open qNu3xvc qoCymac
open qqi5QRb (pointVal pointPrime)
open private val_poly_lt from ProximityPrize.SubmissionLower.ZsE91Ed
open scoped WithZero
variable {E :Type} [Field E] [Algebra L E]
private def seedConst (w:CurvePlace L E) (c:L) :Integers w :=
 ⟨algebraMap L E c,by
   by_cases hc:c=0
   · simp [hc]
   · exact (w.on_constants c hc).le⟩
private theorem reduceSeed_const {A:Equation E} (S:Sections A) (γ:K) (hγ:γ∈S.marks)
  (c:L) :reduceSeed S γ hγ (seedConst (S.place γ) c)=c:= by
 rw [reduceSeed_eq]
 change ((S.atPlace γ hγ) (algebraMap L E c)).coeff 0=c
 rw [AlgHom.commutes,LaurentSeries.algebraMap_apply,HahnSeries.C_apply]
 exact HahnSeries.coeff_single_same _ _
private def aEM (A:Equation E) (w:CurvePlace L E) (r :Bool) :
   Integers w →+* Chart A w r :=
 ((seed A).comp w.value.valuationSubring.subtype).codRestrict (Chart A w r).toSubring
   (fun a=>(aee A w r a).property)
private def yAt (A:Equation E) (w:CurvePlace L E) (r :Bool) :Chart A w r :=
 ⟨jU A r,Algebra.subset_adjoin (Or.inr (by simp))⟩
private def jAt (A:Equation E) (w:CurvePlace L E) (r :Bool) :Chart A w r :=
 ⟨jet A r,Algebra.subset_adjoin (Or.inr (by simp))⟩
private def baseEval (A:Equation E) (w:CurvePlace L E) (r :Bool) :
  nC w →+* Chart A w r :=
 qz1 (qz1 (aEM A w r) (xAt A w r)) (yAt A w r)
private def yZ (A:Equation E) (w:CurvePlace L E) (r :Bool) :
  (nC w)[X] →+* Chart A w r :=
 qz1 (baseEval A w r) (jAt A w r)
private theorem baseEval_coe (A:Equation E) (w:CurvePlace L E) (r :Bool) (f :nC w) :
   (baseEval A w r f :EC A)=ek A w r f := by
 rw [generic_eq]
 let i:=(Chart A w r).val.toRingHom
 have hi:i.comp (qz1 (aEM A w r) (xAt A w r)) =
     qz1 ((seed A).comp w.value.valuationSubring.subtype) (amm A) := by
   apply Polynomial.ringHom_ext
   · intro a
     simp only [qz2,qz0,eval₂_C]
     rfl
   · simp only [qz2,qz0,eval₂_X]
     rfl
 change i (f.eval₂ (qz1 (aEM A w r) (xAt A w r)) (yAt A w r))= _
 rw [hom_eval₂,hi]
 rfl
private theorem jetEval_coe (A:Equation E) (w:CurvePlace L E) (r :Bool)
  (f : (nC w)[X]) :
  (yZ A w r f :EC A)=f.eval₂ (ek A w r) (jet A r) := by
 let i:=(Chart A w r).val.toRingHom
 have hi:i.comp (baseEval A w r)=ek A w r :=
  RingHom.ext (baseEval_coe A w r)
 change i (f.eval₂ (baseEval A w r) (jAt A w r))= _
 rw [hom_eval₂,hi]
 rfl
private theorem jetEval_surj (A:Equation E) (w:CurvePlace L E) (r :Bool) :
    Function.Surjective (yZ A w r) := by
  let f :=yZ A w r
  let g:=(Chart A w r).val.toRingHom.comp f
  let T:Subalgebra L (EC A) :=
    { g.rangeS with
      algebraMap_mem' := fun c=>⟨C (C (C (seedConst w c))),by
        simp only [g,f,qz2,yZ,baseEval,qz0,eval₂_C]
        rfl⟩ }
  have h:Chart A w r≤T:=Algebra.adjoin_le (by
    rintro _ (⟨a,rfl⟩ | ha)
    · exact ⟨C (C (C a)),by
        simp only [g,f,qz2,yZ,baseEval,qz0,eval₂_C]
        rfl⟩
    · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
      rcases ha with he | he | he
      · subst he
        exact ⟨C (C Polynomial.X),by simp [g,f,yZ,baseEval]; rfl⟩
      · subst he
        exact ⟨C Polynomial.X,by simp [g,f,yZ,baseEval]; rfl⟩
      · subst he
        exact ⟨Polynomial.X,by simp [g,f,yZ]; rfl⟩)
  intro a
  obtain ⟨b,hb⟩:=(show (a :EC A)∈g.rangeS from h a.property)
  exact ⟨b,Subtype.ext hb⟩
private theorem ker_fraction {R F T:Type} [CommRing R] [Field F] [Field T]
  (g:R →+* F) (s :R →+* T) (h : ∀ b,g b=0→s b=0)
  (p q:R) (hq:s q≠0) (f :R[X]) (hg:f.eval₂ g (g p/g q)=0) :
  f.eval₂ s (s p/s q)=0:= by
 have hgq:g q≠0:= fun hg=>hq (h q hg)
 have hmul :g q*(g p/g q)=g p:= by rw [mul_comm,div_mul_cancel₀ _ hgq]
 have hc: (f.scaleRoots q).eval₂ g (g p)=0:= by
  rw [← hmul,scaleRoots_eval₂_mul,hg,mul_zero]
 have hs : (f.scaleRoots q).eval₂ s (s p)=0:= by
  have he :g ((f.scaleRoots q).eval p)=0:= by rw [← eval₂_id,hom_eval₂,RingHom.comp_id,hc]
  have he' := h _ he
  rwa [← eval₂_id,hom_eval₂,RingHom.comp_id] at he'
 have hmul' : s q*(s p/s q)=s p:= by rw [mul_comm,div_mul_cancel₀ _ hq]
 rw [← hmul',scaleRoots_eval₂_mul] at hs
 exact (mul_eq_zero.mp hs).resolve_left (pow_ne_zero _ hq)
private theorem polyVal_le (x :L) (f :L[X]) :pointVal x (phys f)≤1 :=
 (pointPrime x).valuation_le_one (K:=FX) f
private theorem polyVal_eq (x :L) {f :L[X]} (h:f.eval x≠0) :
  pointVal x (phys f)=1 :=
 le_antisymm (polyVal_le x f) (le_of_not_gt fun he=>h ((val_poly_lt x f).mp he))
private theorem eval_regular {R:Type} [Semiring R]
   (v :Valuation FX ℤᵐ⁰) (i:R →+* FX) (x :FX)
   (hi : ∀ a,v (i a)≤1) (hx :v x≤1) (f :R[X]) :
   v (qz1 i x f)≤1 := by
 induction f using Polynomial.induction_on' with
 | add p q hp hq =>
   rw [map_add]
   exact (v.map_add _ _).trans (max_le hp hq)
 | monomial n a =>
   rw [qz0,eval₂_monomial,map_mul,map_pow]
   exact mul_le_of_le_one_right' (pow_le_one₀ zero_le hx) |>.trans (hi a)
private theorem specialized_regular {A:Equation E} (S:Sections A)
  (γ:K) (hγ:γ∈S.marks) (x :L) (r :Bool)
  (h:pointVal x (sectionOrdinate (S.P γ) (S.Q γ) r)≤1)
  (p:nC (S.place γ)) :pointVal x (aJB S γ hγ r p)≤1 := by
 rw [specialized_eq]
 let i:=phys.comp (Polynomial.C.comp (reduceSeed S γ hγ))
 let z :=phys Polynomial.X
 have hi (a :Integers (S.place γ)) :pointVal x (i a)≤1 :=
  polyVal_le x (Polynomial.C (reduceSeed S γ hγ a))
 have he (b: (Integers (S.place γ))[X]) :pointVal x (qz1 i z b)≤1 :=
  eval_regular (pointVal x) i z hi (polyVal_le x Polynomial.X) b
 exact eval_regular (pointVal x) (qz1 i z) _ he h p
private theorem descend {R C T:Type} [Semiring R] [Semiring C] [Semiring T]
   (f :R →+* C) (s :R →+* T) (hf :Function.Surjective f)
   (h : ∀ p q,f p=f q→s p=s q) :
   ∃ m:C →+* T,∀ p,m (f p)=s p:= by
 let i:=Function.surjInv hf
 have hi:Function.RightInverse i f :=Function.rightInverse_surjInv hf
 refine ⟨{ toFun:=s ∘ i
           map_one' := (h _ 1 ((hi 1).trans f.map_one.symm)).trans s.map_one
           map_zero' := (h _ 0 ((hi 0).trans f.map_zero.symm)).trans s.map_zero
           map_mul' := fun a b=>(h _ (i a*i b) (by
             rw [hi,map_mul,hi,hi])).trans (s.map_mul _ _)
           map_add' := fun a b=>(h _ (i a+i b) (by
             rw [hi,map_add,hi,hi])).trans (s.map_add _ _) },?_⟩
 exact fun p=>h _ p (hi (f p))
set_option maxHeartbeats 450000 in
theorem assemble {A:Equation E} (S:Sections A) (γ:K) (hγ:γ∈S.marks)
    (δ:Derivation L E E) (x :L) (r :Bool) (J:EM A (S.place γ) δ r)
    (hk :RingHom.ker (ek A (S.place γ) r)≤RingHom.ker (aJB S γ hγ r))
    (hden: (denominator (S.P γ) (S.Q γ) r).eval x≠0)
    (hs :aJB S γ hγ r J.sep≠0)
    (hj:aJB S γ hγ r J.dx/aJB S γ hγ r J.sep =
      sectionJet (S.P γ) (S.Q γ) r)
    (hv :aJB S γ hγ r J.num/aJB S γ hγ r J.sep =
      aIF (S.P γ) (S.Q γ) r*(phys (S.num γ)/phys (S.den γ))) :
    Nonempty (MarkChart A S γ hγ δ x r) := by
  let g:=ek A (S.place γ) r
  let s :=aJB S γ hγ r
  let f :=yZ A (S.place γ) r
  have hjet:jet A r=g J.dx/g J.sep:= by
    change jet A r=(KM A r) (includeCoeffs (S.place γ) J.dx) /
      (KM A r) (includeCoeffs (S.place γ) J.sep)
    rw [J.dx_map,J.sep_map,map_neg,jet,polar]
  let q0:=qz1 s (s J.dx/s J.sep)
  have hfiber (p q: (nC (S.place γ))[X]) (hp:f p=f q) :q0 p=q0 q:= by
    let:Ring (nC (S.place γ)) :=
      @Polynomial.ring (Polynomial (Integers (S.place γ))) (@Polynomial.ring _ inferInstance)
    let b: (nC (S.place γ))[X] :=p-q
    have hb:b+q=p:=sub_add_cancel p q
    have he :b.eval₂ g (jet A r)+q.eval₂ g (jet A r)=p.eval₂ g (jet A r) := by
      simpa only [map_add,qz0] using congrArg (qz1 g (jet A r)) hb
    have hqp:p.eval₂ g (jet A r)=q.eval₂ g (jet A r) := by
      rw [← jetEval_coe,← jetEval_coe]
      exact congrArg (fun z :Chart A (S.place γ) r=>(z :EC A)) hp
    have hpg:b.eval₂ g (g J.dx/g J.sep)=0:= by
      rw [← hjet]
      exact add_right_cancel (he.trans (hqp.trans (zero_add _).symm))
    have hz (a :nC (S.place γ)) (ha :g a=0) :s a=0:= by
      apply (RingHom.mem_ker (f :=aJB S γ hγ r)).mp
      apply hk
      exact (RingHom.mem_ker (f :=ek A (S.place γ) r)).mpr ha
    have hz' : q0 b=0:= by
      change b.eval₂ s (s J.dx/s J.sep)=0
      exact ker_fraction g s hz J.dx J.sep hs b hpg
    have hh:=congrArg q0 hb
    rw [map_add,hz',zero_add] at hh
    exact hh.symm
  obtain ⟨m,hm⟩:=descend f q0 (jetEval_surj A (S.place γ) r) hfiber
  have q2 (a :Integers (S.place γ)) :
      m (aee A (S.place γ) r a)=algebraMap L FX ((S.atPlace γ hγ a).coeff 0) := by
    have h:=hm (C (C (C a)))
    simp only [f,yZ,baseEval,q0,s,specialized_eq,qz0,eval₂_C,
      qz2,reduceSeed_eq] at h
    exact h.trans (IsScalarTower.algebraMap_apply L L[X] FX _).symm
  let M:Chart A (S.place γ) r →ₐ[L] FX :=
    { m with
      commutes' := fun c=> by
        change m (aee A (S.place γ) r (seedConst (S.place γ) c))= _
        rw [q2,← reduceSeed_eq,reduceSeed_const] }
  have q1 (p:nC (S.place γ)) :M (baseEval A (S.place γ) r p)=s p:= by
    change m (baseEval A (S.place γ) r p)=s p
    have h:=hm (C p)
    simpa only [f,yZ,qz0,eval₂_C,q0] using h
  have hq:=polyVal_eq x hden
  refine ⟨{
    map :=M
    regular := ?_
    seed_eq :=q2
    physical_eq := ?_
    sep:=baseEval A (S.place γ) r J.sep
    num :=baseEval A (S.place γ) r J.num
    sep_eq := by rw [baseEval_coe]; exact congrArg (KM A r) J.sep_map
    num_eq := by
      rw [baseEval_coe]
      change (KM A r) (includeCoeffs (S.place γ) J.num)= _
      rw [J.num_map,map_neg]
    simple := by rw [q1]; exact hs
    gK6 := ?_ }⟩
  · have ho:pointVal x (sectionOrdinate (S.P γ) (S.Q γ) r)≤1 := by
      rw [sectionOrdinate,map_div₀,hq,div_one]
      exact polyVal_le x _
    have hd:pointVal x (s J.dx/s J.sep)≤1 := by
      rw [hj,sectionJet,map_div₀,map_pow,hq,one_pow,div_one]
      exact polyVal_le x _
    intro z
    obtain ⟨p,rfl⟩:=jetEval_surj A (S.place γ) r z
    change pointVal x (m (f p))≤1
    rw [hm]
    exact eval_regular (pointVal x) s (s J.dx/s J.sep)
      (specialized_regular S γ hγ x r ho) hd p
  · have h:=q1 (Polynomial.C Polynomial.X)
    simpa only [baseEval,s,specialized_eq,qz0,eval₂_C,eval₂_X] using h
  · refine ⟨aIF (S.P γ) (S.Q γ) r,?_,?_⟩
    · cases r
      · change pointVal x (phys (S.Q γ))=1 at hq
        change pointVal x (phys (S.Q γ)^2)⁻¹=1
        rw [map_inv₀,map_pow,hq,one_pow,inv_one]
      · change pointVal x (phys (S.P γ))=1 at hq
        change pointVal x (-(phys (S.P γ)^2)⁻¹)=1
        rw [(pointVal x).map_neg,map_inv₀,map_pow,hq,one_pow,inv_one]
    · rw [q1,q1]
      exact hv
end
end qhFwyvc
