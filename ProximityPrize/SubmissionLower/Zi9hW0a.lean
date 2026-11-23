import ProximityPrize.SubmissionLower.ZDI0Pnd
set_option Elab.async false
open _root_ renaming CommRing → za6, Fintype.sum_sum_type → zbt, Function.Injective → zq4, Ideal.span → zye, IsFractionRing.injective → zxb, IsLocalization → zNo, MvPolynomial.C → znf, Polynomial → zM1, Polynomial.C → z1z, Polynomial.algebra → z86, Polynomial.coe_mapRingHom → zKC, Polynomial.eval₂RingHom → zqf, Polynomial.isLocalization → zyz, Polynomial.mapRingHom → zhd, Polynomial.map_injective → zTo, Set.range → zxp
set_option backward.isDefEq.respectTransparency false
namespace qYVN5fe
noncomputable section
open Polynomial Finset Finsupp
open cu (L)
open qAW6lac (Index jo block aMp Vanishes)
open scoped nonZeroDivisors
theorem form_map {A B:Type} [za6 A] [za6 B] {d s W:ℕ}
  (f :A →+* B) (u:Index d s W→A) (j:Fin 3) :
  (form u j).map (zhd f)=form (fun i=>f (u i)) j:= by
 simp only [form,Polynomial.map_sum]
 apply Finset.sum_congr rfl
 intro i _
 split <;> simp [zKC,Polynomial.map_monomial]
private theorem eval_form {A B:Type} [za6 A] [za6 B] {d s W:ℕ}
   (f :A →+* B) (u:Index d s W→A) (x y :B) (j:Fin 3) :
   (zqf (zqf f x) y) (form u j) =
     ∑ i,if block i=j then f (u i)*x^xDeg i*y ^yDeg i else 0:= by
 rw [form,map_sum]
 apply Finset.sum_congr rfl
 intro i _
 split <;> simp [Polynomial.eval₂_monomial]
private theorem universal_vanishing {d s W:ℕ} (k :Fin 3) (Q:SplitRing d s W k)
   (hQ:z1z (z1z Q)∈zye (zxp (splitForm d s W k))) :
   Vanishes ((splitCoeff d s W k).symm Q) := by
 intro B _ _ u x y h₀ h₁ h₂
 let f :=(MvPolynomial.eval₂Hom (algebraMap L B) u).comp (splitCoeff d s W k).symm.toRingHom
 let ev :=zqf (zqf f x) y
 have he :zye (zxp (splitForm d s W k))≤RingHom.ker ev := by
   apply Ideal.span_le.mpr
   rintro _ ⟨j,rfl⟩
   change ev (splitForm d s W k j)=0
   rw [splitForm,eval_form]
   have hu (i:Index d s W) :f (splitCoeff d s W k (MvPolynomial.X i))=u i:= by
     simp [f]
   simp only [hu,zbt]
   fin_cases j <;> simpa [block,xDeg,yDeg,aMp] using (by first | exact h₀ | exact h₁ | exact h₂)
 have h:=he hQ
 change ev (z1z (z1z Q))=0 at h
 simpa [ev,f] using h
private theorem sum_coeff {A B:Type} (Q:MvPolynomial (A ⊕ B) L) (e :A ⊕ B →₀ ℕ) :
  let z :=sumFinsuppAddEquivProdFinsupp e
  ((MvPolynomial.sumRingEquiv L A B Q).coeff z.1).coeff z.2= Q.coeff e := by
 let E :=sumFinsuppAddEquivProdFinsupp (α:=A) (β:=B) (M:=ℕ)
 change (AddMonoidAlgebra.mapDomainRingEquiv L E Q).coeff (E e)= Q.coeff e
 simp
theorem block_degree_le {d s W:ℕ} (k :Fin 3) (Q:jo d s W)
   (m:Index d s W →₀ ℕ) (hm:m∈Q.support) :
   m.sum (fun i n=>if block i=k then n else 0)≤(splitCoeff d s W k Q).totalDegree := by
 classical
 let e :=iS d s W k
 let m' := m.mapDomain e
 let a :=(sumFinsuppAddEquivProdFinsupp m').1
 let b:=(sumFinsuppAddEquivProdFinsupp m').2
 have hc: ((splitCoeff d s W k Q).coeff a).coeff b= Q.coeff m:= by
   exact (sum_coeff (MvPolynomial.rename e Q) m').trans
     (MvPolynomial.coeff_rename_mapDomain e e.injective Q m)
 have ha :a∈(splitCoeff d s W k Q).support :=
   MvPolynomial.mem_support_iff.mpr fun h =>
     (MvPolynomial.mem_support_iff.mp hm) (by simpa [h] using hc.symm)
 have hd:a.degree=m.sum (fun i n=>if block i=k then n else 0) := by
   rw [Finsupp.degree_eq_sum,Finsupp.sum_fintype _ _ (by simp)]
   rw [← Equiv.sum_comp e.symm (fun i=>if block i=k then m i else 0),zbt]
   have hmoving (x :Moving d s W k) :block x.val=k :=x.prop
   have hfixed (x :Fixed d s W k) :block x.val≠k :=x.prop
   simp [a,m',e,iS,hmoving,hfixed]
 exact hd ▸ MvPolynomial.le_totalDegree ha
private theorem clear_constant {A B:Type} [za6 A] [za6 B] [Algebra A B]
   (D:Submonoid A) [zNo D B] (hi:zq4 (algebraMap A B))
   (I:Ideal (lK A)) (N :B)
   (hI:z1z (z1z N) ∈
     I.map (zhd (zhd (algebraMap A B)))) :
   ∃ (Q:A) (v :D),z1z (z1z Q)∈I ∧
     algebraMap A B Q=N*algebraMap A B v.val := by
 let _:Algebra (zM1 A) (zM1 B) :=z86 A B
 let _:Algebra (lK A) (lK B) :=z86 (zM1 A) (zM1 B)
 let D₁:=D.map (z1z:A →+* zM1 A)
 let D₂:=D₁.map (z1z:zM1 A →+* lK A)
 have loc₁:zNo D₁ (zM1 B) :=zyz D B
 have loc₂ : @zNo (lK A) _ D₂ (lK B) _ _ :=
   @zyz (zM1 A) _ D₁ (zM1 B) _ _ loc₁
 let f :=algebraMap A B
 let ψ:=zhd (zhd f)
 have hψ:zq4 ψ:=zTo _ (zTo _ hi)
 obtain ⟨⟨z,r⟩,hz⟩:=(IsLocalization.mem_map_algebraMap_iff D₂ (lK B) (I:=I)).mp hI
 obtain ⟨_,⟨v,hv,rfl⟩,hr⟩:=r.prop
 have he :ψ z.val=z1z (z1z (N*f v)) := by
   change z1z (z1z N)*ψ r.val=ψ z.val at hz
   rw [← hr] at hz
   simpa only [ψ,zKC,Polynomial.map_C,← map_mul] using hz.symm
 let Q:=(z.val.coeff 0).coeff 0
 have hQ:f Q=N*f v := by
   simpa only [Q,ψ,zKC,coeff_map,coeff_C_zero] using
     congrArg (fun t:lK B=>(t.coeff 0).coeff 0) he
 have hzc:z.val=z1z (z1z Q) := by
   apply hψ
   simpa only [ψ,zKC,Polynomial.map_C,hQ] using he
 exact ⟨Q,⟨v,hv⟩,hzc ▸ z.prop,hQ⟩
theorem clear_norm {d s W:ℕ} (k :Fin 3) (N :LocalRing d s W k) (hN :N≠0)
   (hI:z1z (z1z N)∈zye (zxp (localForm d s W k))) :
   ∃ Q:jo d s W,Q≠0∧Vanishes Q∧(splitCoeff d s W k Q).totalDegree≤N.totalDegree := by
 let A:=SplitRing d s W k
 let B:=LocalRing d s W k
 let _:Algebra A B:=MvPolynomial.algebraMvPolynomial
 let D:Submonoid A:=((FixedRing d s W k)⁰).map znf
 let φ:=localizeCoeff d s W k
 let ψ:=zhd (zhd φ)
 let I:Ideal (lK A) :=zye (zxp (splitForm d s W k))
 have hφ:zq4 φ :=
   MvPolynomial.map_injective _ (zxb (FixedRing d s W k) (Ground d s W k))
 have :zNo D B:=MvPolynomial.isLocalization _ _
 have hmap :I.map ψ=zye (zxp (localForm d s W k)) := by
   change (zye (zxp (splitForm d s W k))).map ψ= _
   have he :ψ ∘ splitForm d s W k=localForm d s W k :=funext fun j=>form_map φ _ j
   rw [Ideal.map_span,← Set.range_comp,he]
 obtain ⟨Q,⟨_,v,hv,rfl⟩,hconst,hQ⟩ :=
   clear_constant D hφ I N (hmap ▸ hI)
 change φ Q=N*φ (znf v) at hQ
 have hC:φ (znf v)=znf (algebraMap _ _ v) :=MvPolynomial.map_C _ _
 rw [hC] at hQ
 have hQ0:φ Q≠0:= by
   rw [hQ]
   exact mul_ne_zero hN (MvPolynomial.C_ne_zero.mpr
     ((map_ne_zero_iff _ (zxb _ _)).mpr (mem_nonZeroDivisors_iff_ne_zero.mp hv)))
 have hdeg:Q.totalDegree=(φ Q).totalDegree := by
   simp only [MvPolynomial.totalDegree,φ,localizeCoeff,
     MvPolynomial.support_map_of_injective _ (zxb (FixedRing d s W k) (Ground d s W k))]
 refine ⟨(splitCoeff d s W k).symm Q,?_,universal_vanishing k Q hconst,?_⟩
 · exact (map_ne_zero_iff _ (splitCoeff d s W k).symm.injective).mpr (fun h=>hQ0 (by simp [h]))
 · rw [RingEquiv.apply_symm_apply,hdeg,hQ]
   simpa using MvPolynomial.totalDegree_mul N (znf (algebraMap _ _ v))
end
end qYVN5fe
