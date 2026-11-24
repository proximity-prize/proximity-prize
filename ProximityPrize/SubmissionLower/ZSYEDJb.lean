import ProximityPrize.SubmissionLower.ZTV7u3a
import ProximityPrize.SubmissionLower.ZXn7V0b
set_option Elab.async false
set_option autoImplicit true
namespace qYzLClc
noncomputable section
open MvPolynomial
open cu (L)
open qe6nVeb (SeedPlane immersedAt)
open q7YMR4d (SmoothAt simpleQuadratic quadraticAt)
local notation "T" => (PowerSeries.X:PowerSeries L)
local notation "PC" => (PowerSeries.C:L →+* PowerSeries L)
local notation "ct" => (PowerSeries.constantCoeff :PowerSeries L →+* L)
private theorem ps_algMap:algebraMap L (PowerSeries L)=PC :=
 RingHom.ext fun _=>PowerSeries.C_eq_algebraMap.symm
private theorem smooth (q:SeedPlane) (a :Fin 2→L) (h:SmoothAt q a) :
   immersedAt q a := by
 obtain ⟨h₀,i,hi⟩:=h
 let b:Fin 2→PowerSeries L:= fun j=>PC (a j)+if j=i then 0 else T
 have hb:ct ∘ b=a := by
   funext j
   by_cases hj:j=i <;> simp [b,hj]
 have hm:map ct (map PC q)=q:= by
   rw [map_map,PowerSeries.constantCoeff_comp_C,map_id]
 obtain ⟨t,ht,hs,hq⟩:=lift_plane i b (map PC q)
   (by rwa [hb,hm]) (by rwa [hb,hm])
 refine ⟨t,fun j=>(ht j).trans (congrFun hb j),?_,?_⟩
 · let j:=i.succAbove (0:Fin 1)
   have hj:j≠i:=Fin.succAbove_ne i _
   refine ⟨j,?_⟩
   rw [hs j hj]
   simp [b,hj,PowerSeries.coeff_X]
 · simpa only [ps_algMap,← eval₂_eq_eval_map] using hq
private def translate (a :Fin 2→L) :SeedPlane →ₐ[L] SeedPlane :=
 aeval fun i=>MvPolynomial.X i+C (a i)
private theorem d3d {S:Type*} [CommRing S] (f :L →+* S) (v :Fin 2→S)
  (a :Fin 2→L) (q:SeedPlane) :
  eval₂ f v (translate a q)=eval₂ f (fun i=>v i+f (a i)) q:= by
 rw [translate,aeval_def,MvPolynomial.algebraMap_eq,← eval₂_assoc]
 simp only [eval₂_add,eval₂_X,eval₂_C]
private theorem translate_deriv (a :Fin 2→L) (i:Fin 2) (q:SeedPlane) :
    pderiv i (translate a q)=translate a (pderiv i q) := by
  induction q using MvPolynomial.induction_on with
  | C c=>simp [translate,MvPolynomial.algebraMap_eq]
  | add p q hp hq=>simp only [map_add,hp,hq]
  | mul_X p j hp =>
    rw [map_mul,Derivation.leibniz,smul_eq_mul,smul_eq_mul,hp,
      Derivation.leibniz,smul_eq_mul,smul_eq_mul,map_add,map_mul,map_mul]
    have hx :pderiv i (translate a (MvPolynomial.X j))=translate a (pderiv i (MvPolynomial.X j)) := by
      by_cases hj:j=i
      · subst j
        simp [translate]
      · simp [translate,pderiv_X_of_ne hj]
    rw [hx]
private theorem translate_coeff_zero (a :Fin 2→L) (q:SeedPlane) :
  (translate a q).coeff 0=eval a q:= by
 rw [← MvPolynomial.constantCoeff_eq,← eval_zero,← eval₂_id,d3d]
 simp
private theorem degree_ge_two {q:SeedPlane} {a :Fin 2→L} (h:eval a q=0)
   (hd : ∀ i,eval a (pderiv i q)=0) {m:Fin 2 →₀ ℕ} (hm:m∈(translate a q).support) :
   2≤ m.degree := by
 have hn:=mem_support_iff.mp hm
 by_contra! hn'
 have hh:m.degree=0∨m.degree=1 := by omega
 rcases hh with h₀ | h₁
 · have hm' := (Finsupp.degree_eq_zero_iff m).mp h₀
   subst m
   exact hn ((translate_coeff_zero a q).trans h)
 · have hh:m∈Set.range (fun i:Fin 2=>Finsupp.single i 1) := by
     rw [Finsupp.range_single_one]
     exact h₁
   obtain ⟨i,rfl⟩:=hh
   apply hn
   have he : (pderiv i (translate a q)).coeff 0=0:= by
     rw [translate_deriv,translate_coeff_zero,hd]
   simpa [coeff_pderiv] using he
private def blowup (p:SeedPlane) :MvPolynomial (Fin 2) (PowerSeries L) :=
 ∑ m∈p.support,monomial m (PC (p.coeff m)*T^(m.degree-2))
private theorem blowup_red (p:SeedPlane) (h : ∀ m∈p.support,2≤ m.degree) :
   map ct (blowup p)=homogeneousComponent 2 p:= by
 rw [blowup,map_sum,homogeneousComponent_apply,Finset.sum_filter]
 apply Finset.sum_congr rfl
 intro m hm
 rw [map_monomial,map_mul,PowerSeries.constantCoeff_C,map_pow,PowerSeries.constantCoeff_X]
 by_cases he :m.degree=2
 · simp [he]
 · have hp:m.degree - 2≠0:= by have :=h m hm; omega
   simp [he,zero_pow hp]
private theorem blowup_eval (p:SeedPlane) (h : ∀ m∈p.support,2≤ m.degree)
  (v :Fin 2→PowerSeries L) :
  eval₂ PC (fun i=>T*v i) p=T^2*eval v (blowup p) := by
 rw [eval₂_eq,blowup,map_sum,Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro m hm
 rw [← eval₂_id,eval₂_monomial,RingHom.id_apply]
 simp only [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
  ← Finsupp.degree_apply,Finsupp.prod]
 have hn:m.degree=2+(m.degree - 2) := by have :=h m hm; omega
 conv_lhs=>rw [hn,pow_add]
 ring
private theorem singular (q:SeedPlane) (a :Fin 2→L) (h:eval a q=0)
    (hd : ∀ i,eval a (pderiv i q)=0) (hs :simpleQuadratic q a) :
    immersedAt q a := by
  obtain ⟨v,⟨j,hj⟩,h₀,i,hi⟩:=hs
  let p:=translate a q
  have hdeg : ∀ m∈p.support,2≤ m.degree := fun _ hm=>degree_ge_two h hd hm
  have hred:map ct (blowup p)=quadraticAt q a :=blowup_red p hdeg
  have hb:ct ∘ (PC ∘ v)=v := by
    funext k
    exact PowerSeries.constantCoeff_C _
  obtain ⟨w,hw,_,hz⟩:=lift_plane i (PC ∘ v) (blowup p)
    (by rwa [hred,hb]) (by rwa [hred,hb])
  refine ⟨fun k=>T*w k+PC (a k),?_,⟨j,?_⟩,?_⟩
  · intro k
    simp
  · have hc:PowerSeries.coeff 1 (T*w j)=ct (w j) := by
      simpa only [pow_one,zero_add,PowerSeries.coeff_zero_eq_constantCoeff_apply] using
        PowerSeries.coeff_X_pow_mul (w j) 1 0
    simpa [hc,hw j,PowerSeries.coeff_C] using hj
  · rw [ps_algMap,← d3d,blowup_eval p hdeg,hz,mul_zero]
theorem proof :q7YMR4d.c1 :=⟨smooth,singular⟩
end
end qYzLClc
