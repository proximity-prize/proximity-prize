import ProximityPrize.SubmissionLower.A1
import ProximityPrize.SubmissionLower.C
import ProximityPrize.SubmissionLower.A2
import ProximityPrize.SubmissionLower.A3
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
open _root_ renaming DecidableEq→nX,Dr.capCoeff→nq,Dr.capExponents→p5,Dr.dimension→ oY,Fin.append→vj,Fin.lastCases_castSucc→xW,Fin.lastCases_last→v9,Finite→ oZ,Finite.to_wellFoundedGT→sS,Finset.le_sup→qJ,Finset.mem_univ→qG,Finset.sum_add_distrib→wY,Finset.sum_congr→p6,Finset.sup_le→u9,Finsupp.add_apply→v8,Finsupp.mapDomain→t3,Finsupp.mapDomain_single→vH,Finsupp.single→n5,Finsupp.single_apply→xm,Finsupp.weight→pL,Finsupp.weight_apply→vG,Finsupp.weight_single→uz,Fintype→ oD,Fintype.equivFin→qx,Fintype.ofFinite→pU,Function.Injective→sH,Ideal→lI,Ideal.Quotient.mk→wA,Ideal.Quotient.mkₐ→ oq,Jq.Generator→nI,Jq.Represents→qm,LinearOrder→th,LinearOrder.lift'→t7,List.length_cons→qy,Module.finrank→lV,MonomialOrder→t6,MonomialOrder.degLex→vk,MvPolynomial→cy,MvPolynomial.X→c9,MvPolynomial.degreeOf_X→pQ,MvPolynomial.degreeOf_add_le→qM,MvPolynomial.degreeOf_mul_le→p7,MvPolynomial.eval→u5,MvPolynomial.homogeneousComponent→x7,MvPolynomial.mem_support_iff→xL,MvPolynomial.monomial→ oy,MvPolynomial.restrictSupport→ ov,MvPolynomial.restrictSupport_eq_span→uh
open _root_ renaming MvPolynomial.restrictTotalDegree→sI,MvPolynomial.weightedTotalDegree_aeval_le_of_le→wB,MvPolynomial.weightedTotalDegree_piSingle→ oj,Nat.add_le_add_right→vi,Nat.le_add_right→t4,Nat.lt_of_succ_le→xI,Option.some.inj→vh,Polynomial→lz,Polynomial.C→mD,Polynomial.aeval_def→vw,Polynomial.le_natDegree_of_mem_supp→vZ,Polynomial.mem_support_iff→wR,Polynomial.toMvPolynomial→vl,RingHom.ker→pz,Set.add_mem_add→uJ,Set.mem_ofPred_eq→xu,Submodule→qU,Submodule.span_le→t9,WellFoundedGT→t8,XT.Exponent→lJ,aKs.proof→ ox,congrArg→ oK,dN.GeoField→aU,dN.GeoJets→pC,ite_eq_left→u8,ite_eq_right→qz,le_antisymm→uW,map_mul→pG,map_sum→p9,max_le→ oz,succ_nsmul→t5
set_option autoImplicit true
section
namespace Jq
noncomputable section
open dN vS B8 MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def c1 :Prop :=
  ∀ (σ:Type) [oZ σ] (s :σ→Fin 5) (A C:Finset (σ →₀ ℕ)),
    zJ C⊆zJ A → ∃ p q:Form,
      qm p (fun t=>DL s A t) ∧
      qm q (fun t=>DL s C t)∧OQ (p - q)
def c2 :Prop :=
  ∀ (B:lS) (P:lI g9) (t:jJ),(∀ j,0<t j) → ∀ N :ℕ,
    KQ (slot B) (x8 B P) (N•t) =
      affineHilbertFunction (RM B P t) N
private theorem bxV {p q:Form} {a :jJ}
  (hp:p.totalDegree≤a.degree) (hq:q.totalDegree≤a.degree)
  (h:OQ (p - q)) :q.coeff a≤p.coeff a := by
 have hd: (p - q).totalDegree≤a.degree :=
  (totalDegree_sub p q).trans (oz hp hq)
 exact sub_nonneg.mp (by simpa only [coeff_sub] using h a hd)
theorem of_children (hcounts :c1) (hdiag:c2) :
  B8.c1 := by
 intro B _ P I i hi hdim D hbox hreg
 change tW B (i9 P D) I≤tW B P (insert i I)
 let P₁:=i9 P D
 let P₂:=i9 P (D^2)
 obtain ⟨f,g,hf,hg,hcf,hle₁,hcg,hle₂⟩:=b2l B P i D hbox hreg
 obtain ⟨hhom₁,hex₁⟩:=a4I (slot B) (x8 B P)
  (afL B P) i f hf
 obtain ⟨hhom₂,hex₂⟩:=a4I (slot B) (x8 B P₂)
  (afL B P₂) i g hg
 rw [hcf] at hex₁
 rw [hcg] at hex₂
 obtain ⟨p,_,hp,_,_⟩:=a4h hcounts (nI B) (slot B) (x8 B P) (x8 B P)
  (afL B P) (afL B P) le_rfl
 obtain ⟨q,p₂,hq,hp₂,hpos₂⟩:=a4h hcounts (nI B) (slot B)
  (x8 B P ⊔ Ideal.span {f}) (x8 B P₂) hhom₁
  (afL B P₂) hle₁
 obtain ⟨r,p₁,hr,hp₁,hpos₁⟩:=a4h hcounts (nI B) (slot B)
  (x8 B P₂ ⊔ Ideal.span {g}) (x8 B P₁) hhom₂
  (afL B P₁) hle₂
 have hqeq :q=auj i p:=bpq i hq hp hp hex₁
 have hreq :r=p₂ - previous i p₁:=bpq i hr hp₂ hp₁ hex₂
 have hreg₂ :IsLeftRegular (wA P (D^2)) := by
  rw [map_pow]
  exact IsLeftRegular.pow 2 hreg
 have hdp:=a4y B P hdim hp (hdiag B P)
 have hdp₁:=a4y B P₁ (aC0 hreg hdim) hp₁ (hdiag B P₁)
 have hdp₂:=a4y B P₂ (aC0 hreg₂ hdim) hp₂ (hdiag B P₂)
 have hdq:q.totalDegree≤I.card:= by
  rw [hqeq]
  exact blI i hdp
 have hdr :r.totalDegree≤I.card:= by
  rw [hreq]
  exact (totalDegree_sub _ _).trans (oz hdp₂ (ccz i hdp₁))
 have hdeg:=aJC I
 have hm₂:=bxV (hdq.trans_eq hdeg.symm) (hdp₂.trans_eq hdeg.symm) hpos₂
 have hm₁:=bxV (hdr.trans_eq hdeg.symm) (hdp₁.trans_eq hdeg.symm) hpos₁
 rw [hqeq,blH i hi hdp] at hm₂
 rw [hreq,coeff_sub,bKH i (squarefree I) (hdp₁.trans_eq hdeg.symm)] at hm₁
 have hscaled:2*p₁.coeff (squarefree I)≤p.coeff (squarefree (insert i I)) := by
  linarith only [hm₁,hm₂]
 rw [c0q B P₁ I hp₁ (hdiag B P₁),c0q B P (insert i I) hp (hdiag B P)]
 rw [Finset.card_insert_of_notMem hi,pow_succ]
 refine (div_le_div_iff₀ (pow_pos (by norm_num : (0:ℚ)<2) I.card)
  (mul_pos (pow_pos (by norm_num : (0:ℚ)<2) I.card) (by norm_num))).mpr ?_
 convert mul_le_mul_of_nonneg_right hscaled
  (pow_nonneg (by norm_num : (0:ℚ)≤2) I.card) using 1 <;> ring
end
end Jq
end
section
namespace cyq
noncomputable section
open dN vS B8 Jq MvPolynomial
open scoped Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra
private theorem diagonal_add (B:lS) (s t:jJ) :
    H7 B (s+t:jJ)=H7 B s+H7 B t:= by
  ext m
  constructor
  · rintro ⟨u,hu,rfl⟩
    let v (i:Fin 5) (j:Fin (s i)) :=u i (Fin.castAdd (t i) j)
    let w (i:Fin 5) (j:Fin (t i)) :=u i (Fin.natAdd (s i) j)
    refine ⟨∑ i,∑ j,v i j,⟨v,fun i j=>hu i _,rfl⟩,
      ∑ i,∑ j,w i j,⟨w,fun i j=>hu i _,rfl⟩,?_⟩
    simp only [v,w,← wY]
    exact p6 rfl (fun i _=>(Fin.sum_univ_add (u i)).symm)
  · rintro ⟨a,⟨v,hv,rfl⟩,b,⟨w,hw,rfl⟩,rfl⟩
    refine ⟨fun i=>vj (v i) (w i),?_,?_⟩
    · intro i
      exact Fin.addCases (fun j=> by simpa only [Fin.append_left] using hv i j)
        (fun j=> by simpa only [Fin.append_right] using hw i j)
    · change (∑ i,∑ j,v i j)+(∑ i,∑ j,w i j) =
          ∑ i,∑ j:Fin (s i+t i),vj (v i) (w i) j
      rw [← wY]
      refine p6 rfl fun i _ => ?_
      simpa only [Fin.append_left,Fin.append_right] using
        (Fin.sum_univ_add (vj (v i) (w i))).symm
private theorem diagonal_zero (B:lS) :H7 B (0:jJ)=0:= by
 ext m
 rw [Set.mem_zero]
 constructor
 · rintro ⟨u,_,rfl⟩
   simp
 · rintro rfl
   exact ⟨fun _ j=>j.elim0,fun _ j=>j.elim0,by simp⟩
private theorem aHz (B:lS) (t:jJ) (n:ℕ) :
   H7 B (n•t:jJ)=n•H7 B t:= by
 induction n with
 | zero=>simpa only [zero_smul] using diagonal_zero B
 | succ n ih=>simp only [succ_nsmul,diagonal_add,ih]
private theorem asK (B:lS) (i:Fin 5) :0∈Nl (B i) :=
 cBb _
private theorem a9G (B:lS) (t:jJ) :0∈H7 B t :=
 ⟨fun _ _=>0,fun i _=>asK B i,by simp⟩
private theorem bqy {B:lS} (v :nI B) :
    v.2.val∈H7 B (jT (slot B) v) := by
  classical
  let a (i:Fin 5) :Exponent:=if i=v.1 then v.2.val else 0
  refine ⟨fun i _=>a i,?_,?_⟩
  · intro i _
    by_cases h:i=v.1
    · subst i
      simpa only [a,u8 rfl] using v.2.property
    · simpa only [a,qz h] using asK B i
  · symm
    calc
      (∑ i,∑ _j:Fin (jT (slot B) v i),a i) =
          ∑ i,(jT (slot B) v i)•a i :=
        p6 rfl fun i _=>Fin.sum_const _ _
      _=v.2.val := by
        change (∑ i,(n5 v.1 (1 :ℕ) i)•a i)= _
        refine (Finset.sum_eq_single v.1 ?_ ?_).trans ?_
        · intro i _ h
          simp [a,h]
        · simp
        · simp [a]
private theorem aX1 (B:lS) (d:nI B →₀ ℕ) (c:aU) :
   DM B (oy d c) =
     oy (pL (fun v :nI B=>v.2.val) d) c:= by
 rw [DM,aeval_monomial,Finsupp.prod,vG,Finsupp.sum]
 simp only [monomial_pow,one_pow,← monomial_sum_one,algebraMap_eq,C_mul_monomial,mul_one]
private theorem bxq (B:lS) (d:nI B →₀ ℕ) :
    pL (fun v :nI B=>v.2.val) d ∈
      H7 B (pL (jT (slot B)) d) := by
  induction d using Finsupp.induction_linear with
  | zero=>simpa only [map_zero] using a9G B (0:jJ)
  | add a b ha hb=>simpa only [map_add,diagonal_add] using Set.add_mem_add ha hb
  | single v n =>
      have hmem:n•v.2.val∈n•H7 B (jT (slot B) v) := by
        induction n with
        | zero=>simp
        | succ n ih =>
            simpa only [t5] using uJ ih (bqy v)
      simpa only [uz ,aHz] using hmem
private theorem bxt {B:lS} {g:jJ} {m:Exponent}
  (hm:m∈H7 B g) :
  ∃ a :vJ B,a∈dO (slot B) g∧DM B a=oy m 1 := by
 classical
 obtain ⟨u,hu,rfl⟩:=hm
 let v (i:Fin 5) (j:Fin (g i)) :nI B:=⟨i,⟨u i j,hu i j⟩⟩
 let d:nI B →₀ ℕ := ∑ i,∑ j,n5 (v i j) 1
 have hg:pL (jT (slot B)) d=g:= by
  simp only [d,p9,uz ,one_smul,jT,slot,v,Fin.sum_const]
  ext i
  rw [Finsupp.finsetSum_apply]
  simp [zY,xm]
 refine ⟨oy d 1,isWeightedHomogeneous_monomial _ _ _ hg,?_⟩
 simp only [aX1,d,p9,uz ,one_smul,v]
private theorem bxr (B:lS) (g:jJ) :
    (dO (slot B) g).map (DM B).toLinearMap =
      ov aU (H7 B g) := by
  apply uW
  · have hpiece :dO (slot B) g =
        ov aU {d | pL (jT (slot B)) d=g} :=
      weightedHomogeneousSubmodule_eq_finsupp_supported _ _ _
    rw [Submodule.map_le_iff_le_comap,hpiece,uh,t9]
    rintro _ ⟨d,hd,rfl⟩
    change DM B (oy d 1)∈ov aU (H7 B g)
    rw [aX1,monomial_mem_restrictSupport]
    exact Or.inl ((show pL (jT (slot B)) d=g from hd) ▸
      bxq B d)
  · rw [uh,t9]
    rintro _ ⟨m,hm,rfl⟩
    obtain ⟨a,ha,heq⟩:=bxt hm
    exact ⟨a,ha,heq⟩
private theorem aDS {S:Set Exponent} {n:ℕ} {m:Exponent} (hm:m∈n•S) :
   ∃ a :cy S aU,a.totalDegree≤n ∧
     monomialMap aU S a=oy m 1 := by
 induction n generalizing m with
 | zero =>
     rw [zero_smul,Set.mem_zero] at hm
     subst m
     exact ⟨1,by simp,by simp⟩
 | succ n ih =>
     rw [t5] at hm
     obtain ⟨b,hb,c,hc,rfl⟩:=hm
     obtain ⟨a,ha,hφ⟩:=ih hb
     refine ⟨a*c9 ⟨c,hc⟩,(totalDegree_mul _ _).trans ?_,?_⟩
     · simpa only [totalDegree_X] using vi ha 1
     · rw [pG,hφ,monomialMap_X,monomial_mul_monomial,one_mul]
private theorem affine_image (S:Set Exponent) (h0:0∈S) (n:ℕ) :
   (sI S aU n).map (monomialMap aU S).toLinearMap =
     ov aU (n•S) := by
 apply uW
 · rintro _ ⟨a,ha,rfl⟩
   exact monomialMap_mem_restrictSupport_nsmul h0 ((mem_restrictTotalDegree S n a).mp ha)
 · rw [uh,t9]
   rintro _ ⟨m,hm,rfl⟩
   obtain ⟨a,ha,hφ⟩:=aDS hm
   exact ⟨a,(mem_restrictTotalDegree S n a).mpr ha,hφ⟩
private theorem aWH {A:Type*} [CommRing A] [Algebra aU A]
    (V:qU aU A) (I:lI A) (P:lI g9) (φ:A →ₐ[aU] g9)
    (hle :I≤P.comap φ) (hker : ∀ a∈V,φ a∈P→a∈I) :
    lV aU (V.map (oq aU I).toLinearMap) =
      lV aU ((V.map φ.toLinearMap).map
        (oq aU P).toLinearMap) := by
  let W:=V.map (oq aU I).toLinearMap
  let f :=Ideal.quotientMapₐ P φ hle
  have hinj:sH (f.toLinearMap.domRestrict W) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨x,hx⟩ hx0
    obtain ⟨a,ha,rfl⟩:=Submodule.mem_map.mp hx
    change wA P (φ a)=0 at hx0
    apply Subtype.ext
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hker a ha (Ideal.Quotient.eq_zero_iff_mem.mp hx0))
  have hmap :W.map f.toLinearMap =
      (V.map φ.toLinearMap).map (oq aU P).toLinearMap:= by
    simp only [W,← Submodule.map_comp,← AlgHom.comp_toLinearMap,f,
      Ideal.quotient_map_comp_mkₐ]
  rw [← hmap,← LinearMap.range_domRestrict W f.toLinearMap]
  exact (LinearEquiv.ofInjective _ hinj).finrank_eq
theorem proof :Jq.c2 := by
  intro B P t _ n
  let S:=H7 B t
  change lV aU
      ((dO (slot B) (n•t)).map (oq aU (x8 B P)).toLinearMap) =
    lV aU
      ((sI S aU n).map
        (oq aU (RM B P t)).toLinearMap)
  have hle :x8 B P≤P.comap (DM B) :=
    Ideal.toIdeal_homogeneousCore_le (dO (slot B)) _
  have hgraded:=aWH (dO (slot B) (n•t)) (x8 B P) P
    (DM B) hle (fun _ ha=>(avx ha).mpr)
  have haffine :=aWH (sI S aU n) (RM B P t) P
    (monomialMap aU S) le_rfl (fun _ _ h=>h)
  rw [hgraded,haffine,bxr B (n•t),affine_image S (a9G B t) n,
    aHz]
end
end cyq
end
section
namespace as5
open Jq MvPolynomial
open scoped BigOperators
private theorem bLk {σ:Type} [oD σ] (s :σ→Fin 5)
  (b:σ →₀ ℕ) (A:Finset (σ →₀ ℕ)) (hA : ∀ a∈A,a≤b) :
  qm (∑ u∈Ax (b:=b) A,ayh s u) (fun t=>DL s A t) := by
 refine ⟨b.degree+1,fun t ht => ?_⟩
 change eval (fun j=>(t j:ℚ)) (∑ u∈Ax (b:=b) A,ayh s u) =
  (DL s A t:ℚ)
 rw [p9,dej s b A hA,Nat.cast_sum]
 exact p6 rfl fun u _=>cEu s u t (fun j=>xI (ht j))
theorem proof :Jq.c1 := by
 classical
 intro σ _ s A C h
 let _:=pU σ
 let b:=(A∪C).sup id
 let U:=Ax (b:=b) A
 let V:=Ax (b:=b) C
 refine ⟨∑ u∈U,ayh s u,∑ u∈V,ayh s u,?_,?_,?_⟩
 · exact bLk s b A (fun _ ha=>qJ (f :=id) (Finset.mem_union_left C ha))
 · exact bLk s b C (fun _ hc=>qJ (f :=id) (Finset.mem_union_right A hc))
 · rw [← Finset.sum_sdiff (dGp (b:=b) h) (f :=ayh s),add_sub_cancel_right]
   exact bO6 _ _ (fun u _=>bCn s u)
end as5
end
section
namespace aA8
noncomputable section
open dN lB XT MvPolynomial
open Jq (jJ Form OQ KQ dO zJ DL a8M)
open scoped Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def c1 :Prop :=
  ∀ (A:Fin 4→Set lJ) (B:Set lJ),admissible A B →
    ∀ (P:lI pC) (t:jJ),
      KQ (bOJ A B) (csa A B P) t =
        aH8 A B P (t 4) (fun i=>t i.castSucc)
def c2 :Prop :=
  ∀ (σ:Type) [oZ σ] (s :σ→Fin 5) (T:Finset (σ →₀ ℕ)),
    ∃ p:Form,qm p (fun t=>DL s T t)∧OQ p
private theorem eiU (σ:Type) [oZ σ] (s :σ→Fin 5)
  (J:lI (cy σ aU)) (hJ:J.IsHomogeneous (dO s)) :
  ∃ T:Finset (σ →₀ ℕ),∀ t:jJ,KQ s J t=DL s T t:= by
 let _:=pU σ
 let _:th σ:=t7 _ (qx σ).injective
 have :t8 σ:=sS
 let m:t6 σ:=vk
 obtain ⟨T,hT⟩:=m.exists_finset_standardExponents_iff J
 have hstandard:m.standardExponents J=zJ T:=Set.ext hT
 refine ⟨T,fun t => ?_⟩
 rw [a8M s m J hJ t,hstandard]
 rfl
private theorem edx (himage :c1) (hcounts :c2)
   {A:Fin 4→Set lJ} {B:Set lJ} (hAB:admissible A B) (P:lI pC) :
   ∃ p:Form,qm p (fun t=>(aH8 A B P (t 4) (fun i=>t i.castSucc) :ℚ)) ∧
     OQ p:= by
 let : ∀ j,oZ (Vu A B j) := fun j=> by
   refine Fin.lastCases ?_ (fun i => ?_) j
   · unfold Vu
     rw [v9]
     exact hAB.2.1.to_subtype
   · unfold Vu
     rw [xW]
     exact (hAB.1 i).1.to_subtype
 let J:=csa A B P
 let s :=bOJ A B
 have hJ:J.IsHomogeneous (dO s) :=
   ((P.comap (dgy A B)).homogeneousCore (dO s)).isHomogeneous
 obtain ⟨T,hT⟩:=eiU (bk8 A B) s J hJ
 obtain ⟨p,⟨N,hN⟩,hp⟩:=hcounts (bk8 A B) s T
 refine ⟨p,⟨N,fun t ht => ?_⟩,hp⟩
 exact (hN t ht).trans
   (oK (fun n:ℕ=>(n:ℚ)) ((hT t).symm.trans (himage A B hAB P t)))
private theorem byS {S:Set lJ} (h:0∈S) (n:ℕ) :0∈n•S:= by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [t5]
   simpa only [zero_add] using uJ ih h
private theorem ebf {K R:Type} [Field K] [CommRing R] [Algebra K R]
    (e :R ≃ₐ[K] K) (S:qU K R) (h:1∈S) :
    lV K S=1 := by
  have htop:S = ⊤ := by
    apply top_unique
    intro r _
    have hs : (e r)•(1 :R)=r := by
      apply e.toLinearEquiv.injective
      calc
        e.toLinearEquiv ((e r)•(1 :R))=(e r)•(e 1) :=
          e.toLinearEquiv.map_smul (e r) 1
        _=e.toLinearEquiv r := by
          change (e r)•(e 1)=e r
          have he :e (1 :R)=(1 :K) :=map_one e
          rw [he,smul_eq_mul,mul_one]
    exact hs ▸ S.smul_mem (e r) h
  calc
    lV K S=lV K (⊤ : qU K R) :=
      oK (fun T:qU K R=>lV K T) htop
    _=lV K R:=finrank_top K R
    _=lV K K:=e.toLinearEquiv.finrank_eq
    _=1 :=Module.finrank_self K
private theorem d2I {K:Type} [Field K] (y :Fin 4→K)
   {T:Set lJ} (hT:0∈T) :
   lV K ((ov K T).map
     (oq K (pz (eval y))).toLinearMap)=1 := by
 let f :cy (Fin 4) K →ₐ[K] K:=aeval y
 have hf :Function.Surjective f := fun c=>⟨C c,by simp [f]⟩
 let e :=Ideal.quotientKerAlgEquivOfSurjective hf
 let q:=oq K (pz f.toRingHom)
 have h1 : (1 :cy (Fin 4) K)∈ov K T:= by
   rw [MvPolynomial.one_def]
   exact (monomial_mem_restrictSupport K).mpr (Or.inl hT)
 have hm:1∈(ov K T).map q.toLinearMap :=
   Submodule.mem_map.mpr ⟨1,h1,q.map_one⟩
 exact ebf e _ hm
private theorem eMp {A:Fin 4→Set lJ} {B:Set lJ} (hAB:admissible A B)
   (y :KE) (b:ℕ) (w:GG) :lO A B (oF y) b w=1 := by
 have hzero {S T:Set lJ} (hs :0∈S) (ht:0∈T) :0∈S+T:= by
   simpa only [zero_add] using uJ hs ht
 have hz :0∈aza A B b w :=
   hzero (hzero (hzero (hzero (byS hAB.2.2.1 b)
     (byS (hAB.1 0).2 (w 0)))
     (byS (hAB.1 1).2 (w 1)))
     (byS (hAB.1 2).2 (w 2)))
     (byS (hAB.1 3).2 (w 3))
 unfold lO
 rw [d2I y hz,Nat.cast_one]
theorem of_children (himage :c1) (hcounts :c2) :XT.c1 := by
 classical
 intro A B hAB
 have hex (i:Fin 5) (P:lI pC) (hd:W3 P=4 - i.val) :
     ∃ d:ℝ,0≤d∧aAV A B P i.val d:= by
   obtain ⟨p,hp,hpos⟩:=edx himage hcounts hAB P
   exact eAW hp i ((eM3 hAB P hp).trans_eq hd) hpos
 let D (i:Fin 5) (P:lI pC) :ℝ :=
   if i=4∧P∈Set.range oF then 1
   else if hd:W3 P=4 - i.val then Classical.choose (hex i P hd) else 0
 refine ⟨D,?_,fun y=>u8 ⟨rfl,⟨y,rfl⟩⟩⟩
 intro i P _ hd
 by_cases h:i=4∧P∈Set.range oF
 · have hD:D i P=1 :=u8 h
   rw [hD]
   obtain ⟨rfl,y,rfl⟩:=h
   refine ⟨zero_le_one,0,?_⟩
   have hz :acC (4 :Fin 5).val=[] := by decide
   intro b w s _ _
   have he :4-(4 :Fin 5).val=0:= by decide
   rw [hz,he]
   change lO A B (oF y) b w=(s :ℝ)^(0:ℕ)*1
   rw [eMp hAB y b w,pow_zero,mul_one]
 · have hD:D i P=Classical.choose (hex i P hd) := by
     dsimp only [D]
     rw [qz h,dite_eq_left hd]
   rw [hD]
   exact Classical.choose_spec (hex i P hd)
end
end aA8
end
section
namespace cyB
noncomputable section
open dN Jq XT aA8 as7
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
private theorem gsQ (A:Fin 4→Set lJ) (B:Set lJ) :
   Vu A B=aFa A B:= by
 funext j
 refine Fin.lastCases ?_ (fun i => ?_) j
 · rw [Vu,v9,bxc]
 · rw [Vu,xW,crV]
theorem proof :aA8.c1 := by
 intro A B hAB P t
 let rankFor (S:Fin 5→Set lJ) :ℕ :=
   let s : ((j:Fin 5)×S j)→Fin 5:=Sigma.fst
   let f :cy ((j:Fin 5)×S j) aU →ₐ[aU] GeoJets :=
     aeval fun v=>oy v.2.val 1
   KQ s ((P.comap f).homogeneousCore (dO s)).toIdeal t
 have hRank :KQ (bOJ A B) (csa A B P) t =
     KQ (slot A B) (xJ A B P) t :=
   oK rankFor (gsQ A B)
 rw [hRank]
 have h:=bRB.proof A B hAB P (bqO t)
 change (KQ (slot A B) (xJ A B P) (Uf (bqO t)) :ℝ) =
   (aH8 A B P (t 4) (fun i=>t i.castSucc) :ℝ) at h
 rw [eEe] at h
 exact_mod_cast h
end
end cyB
end
section
namespace cyC
open Jq as5 MvPolynomial
open scoped BigOperators
theorem proof :aA8.c2 := by
 classical
 intro σ _ s T
 let _:=pU σ
 let b:=T.sup id
 have hb : ∀ a∈T,a≤b:= fun _ ha=>qJ (f :=id) ha
 refine ⟨∑ u∈Ax (b:=b) T,ayh s u,?_,?_⟩
 · refine ⟨b.degree+1,fun t ht => ?_⟩
   change eval (fun j=>(t j:ℚ)) (∑ u∈Ax (b:=b) T,ayh s u) =
     (DL s T t:ℚ)
   rw [p9,dej s b T hb,Nat.cast_sum]
   exact p6 rfl fun u _=>cEu s u t (fun j=>xI (ht j))
 · exact bO6 _ _ (fun u _=>bCn s u)
end cyC
end
section
namespace bav
noncomputable section
open aR dN Dr Kd lB MvPolynomial Filter
open ap8 (buL bO7 bD4 aES aQe)
private def eaL (σ:Type) [oZ σ] :t6 σ:= by
 classical
 let _:oD σ:=pU σ
 let _:th σ:=t7 (qx σ) (qx σ).injective
 let _:t8 σ:=sS
 exact vk
private theorem edw {ι:Type} [oD ι] [nX ι] (s :ι→Shape)
    (hs : ∀ i,bF (s i)) (J:lI pC) (used :List ι) :
    let H := fun a=>(Sn J (p5 (ku s a)) :ℚ)
    ∃ F:cy ι ℚ,(∀ᶠ a in atTop,eval (fun i=>(a i:ℚ)) F=H a) ∧
      ∀ᶠ a in atTop,0≤uU used H a := by
  classical
  let σ:=Kb s
  let m:=eaL σ
  let I:=HW s J
  let slot:=Fd s
  obtain ⟨A,hA⟩:=m.exists_finset_standardExponents_iff I
  have hzero :zJ ({0} : Finset (σ →₀ ℕ)) = ∅ := by
    ext e
    simp [zJ,zero_le]
  obtain ⟨⟨F,hF⟩,hpos⟩:=aKr.proof slot A {0}
    (by rw [hzero]; exact Set.empty_subset _)
  have hcount (a :ι→ℕ) :
      DL slot A a - DL slot {0} a =
        (Sn J (p5 (ku s a)) :ℚ) := by
    have hset :m.standardExponents I=zJ A:=Set.ext hA
    have hstd:=aXV slot m I (ox s J).1 a
    rw [hset] at hstd
    have he :DL slot A a=lO slot I a :=hstd.symm
    rw [he,(ox s J).2 a,gLV s hs]
    simp [DL,hzero]
  exact ⟨F,by simpa only [hcount] using hF,by simpa only [hcount] using hpos used⟩
private theorem bD3 {ι:Type} [nX ι]
   (used :List ι) {F G: (ι→ℕ)→ℚ} {u:ι→ℕ}
   (h : ∀ a≥u,F a=G a) (a :ι→ℕ) (ha :u≤a) :
   uU used F a=uU used G a := by
 induction used generalizing a with
 | nil=>exact h a ha
 | cons i rest ih =>
   simp only [uU,ih a ha,ih (a+step i) (ha.trans fun j=>t4 _ _)]
theorem proof :bzI.c2 := by
 intro J _ hJ p q hp hq
 let s :Fin 3→Shape := ![⟨3, 3,1⟩,p,q]
 let used :List (Fin 3) :=[1, 2]
 have hs (i:Fin 3) :bF (s i) := by
   fin_cases i
   · change bF ⟨3, 3,1⟩
     exact ⟨by decide,by decide⟩
   · exact hp
   · exact hq
 have hbase :0<(s 0).t:= by
   change 0<(1 :ℕ)
   decide
 obtain ⟨F,hF,hpos⟩:=edw s hs J used
 obtain ⟨u,hu⟩:=eventually_atTop.mp hF
 have hray (v :Fin 3→ℕ) (hv :0<v 0) :=
   gLW s J 0 hs hbase F u hu v hv used.length hJ.le
 have hdeg:F.totalDegree≤used.length :=
   (bO7 F u (oY J) (fun v hv=>(hray v (hv 0)).1)).trans hJ.le
 let G:= fun v :Fin 3→ℕ=>eval (fun i=>(v i:ℚ)) (x7 used.length F)
 have hG (v :Fin 3→ℕ) (hv :step 0≤v) :
     G v=nq J used.length (ku s v) := by
   have hv₀:0<v 0 :=
     Nat.zero_lt_one.trans_le (by simpa [step] using hv 0)
   exact (buL F u v hdeg).symm.trans (hray v hv₀).2
 obtain ⟨a,ha,hau⟩:=(hpos.and (eventually_ge_atTop u)).exists
 have hnon :0≤uU used (fun v=>nq J used.length (ku s v)) (step 0) := calc
   _≤uU used (fun v=>(Sn J (p5 (ku s v)) :ℚ)) a :=ha
   _=uU used (fun v=>eval (fun i=>(v i:ℚ)) F) a :=
     (bD3 used hu a hau).symm
   _=uU used G (step 0) :=bD4 used (by decide) F hdeg a (step 0)
   _ = _:=bD3 used hG (step 0) le_rfl
 have hs₀:s 0=⟨3, 3,1⟩:=rfl
 have hs₁:s 1=p:=rfl
 have hs₂:s 2=q:=rfl
 have hpol:0≤BE (nq J 2) [p,q] ⟨3, 3,1⟩:= by
   simpa only [used,uU,aES,aQe,hs₀,hs₁,hs₂,BE,
     qy ,List.length_nil,Nat.reduceAdd] using hnon
 unfold tW
 exact div_nonneg hpol (by positivity)
end
end bav
end
section
set_option backward.isDefEq.respectTransparency false
namespace cxG
noncomputable section
open K1 BN aez wT Qo MvPolynomial
private abbrev aoq {F:Type*} [Field F] :=
 vl (R:=F) (0:Fin 5)
private def azN {F:Type*} [Field F] (z :Fin 5) (A:Fin 2→lz F) :
  cy (Fin 5) F :=
 aoq (A 0)+aoq (A 1)*c9 z
private def bJ7 {F:Type*} [Field F] (O:Fin 2→Fin 2→lz F) :
  cy (Fin 5) F :=
 azN 3 (fun j=>O j 0)+azN 3 (fun j=>O j 1)*c9 4
private theorem evW (P:lz K) :
  xx (aoq P)=mD (Om P) := by
 have h: (xx (F:=K)).toRingHom.comp (aoq (F:=K)).toRingHom =
    Polynomial.C.comp Om:= by
  apply Polynomial.ringHom_ext
  · intro a
    simp [aoq,Om,xx,finSuccEquiv_apply]
  · simp [aoq,Om,aI3]
 exact RingHom.congr_fun h P
private theorem eLJ (U V:Fin 2→lz K)
  (O:Fin 2→Fin 2→lz K) :
  aEc U V O =
    azN 4 U*c9 1+azN 3 V*c9 2 - bJ7 O:= by
 have h1 :xx (F:=K) (c9 1)=mD (c9 1) :=
  aI3 1
 have h2 :xx (F:=K) (c9 2)=Polynomial.X :=
  aI3 2
 have h3:xx (F:=K) (c9 3)=mD (c9 2) :=
  aI3 3
 have h4 :xx (F:=K) (c9 4)=mD (c9 3) :=
  aI3 4
 apply (xx (F:=K)).injective
 simp only [bgd,azN,bJ7,map_sub,map_add,pG,
  evW,h1,h2,h3,h4,denominator,numerator,qW]
 ring
variable {F:Type*} [Field F]
private theorem bIo (P:lz F) (e :Fin 5 →₀ ℕ) :
    e∈(aoq P).support ↔ ∃ n∈P.support,e=n5 0 n:= by
  classical
  let f :Unit→Fin 5:= fun _=>0
  have hf :sH f := fun _ _ _=>Subsingleton.elim _ _
  change e∈(vl (0:Fin 5) P).support↔_
  rw [Polynomial.toMvPolynomial_eq_rename_comp]
  change e∈(rename f ((uniqueAlgEquiv F Unit).symm P)).support↔_
  rw [support_rename_of_injective hf,Finset.mem_image]
  constructor
  · rintro ⟨d,hd,rfl⟩
    refine ⟨d default,?_,?_⟩
    · simpa only [xL,coeff_uniqueAlgEquiv_symm,wR] using hd
    · calc
        t3 f d=t3 f (n5 default (d default)) :=
          oK (t3 f) (Finsupp.unique_single d)
        _=n5 0 (d default) := by rw [vH]
  · rintro ⟨n,hn,rfl⟩
    refine ⟨n5 default n,?_,?_⟩
    · simpa only [xL,coeff_uniqueAlgEquiv_symm,Finsupp.single_eq_same,
        wR] using hn
    · rw [vH]
private theorem cXu (P:lz F) (i:Fin 5) :
    (aoq P).degreeOf i=if i=0 then P.natDegree else 0:= by
  rw [degreeOf_eq_sup]
  apply uW
  · apply u9
    intro e he
    obtain ⟨n,hn,rfl⟩:=(bIo P e).mp he
    by_cases hi:i=0
    · subst i
      simpa using vZ n hn
    · simp [hi]
  · by_cases hi:i=0
    · subst i
      by_cases hz :P=0
      · simp [hz]
      have he :=(bIo P (n5 0 P.natDegree)).mpr
        ⟨P.natDegree,Polynomial.natDegree_mem_support_of_nonzero hz,rfl⟩
      simpa using qJ (f := fun e :Fin 5 →₀ ℕ=>e 0) he
    · simp [hi]
private theorem c3Q (A:Fin 2→lz F) {z :Fin 5} (hz :z≠0) :
  Disjoint (aoq (A 0)).support (aoq (A 1)*c9 z).support := by
 apply Finset.disjoint_left.mpr
 intro e he he'
 obtain ⟨n,_,rfl⟩:=(bIo (A 0) e).mp he
 rw [support_mul_X] at he'
 obtain ⟨d,hd,heq⟩:=Finset.mem_map.mp he'
 obtain ⟨m,_,rfl⟩:=(bIo (A 1) d).mp hd
 have h:=oK (fun a :Fin 5 →₀ ℕ=>a z) heq
 simp [v8 ,Ne.symm hz] at h
private theorem c3R (A:Fin 2→lz F) {z :Fin 5} (hz :z≠0)
   (hA : ∃ j,A j≠0) :azN z A≠0:= by
 have hn (j:Fin 2) (hj:A j≠0) :aoq (A j)≠0:= by
   intro h
   exact hj ((Polynomial.toMvPolynomial_injective (0:Fin 5)) (h.trans (map_zero aoq).symm))
 have hs : (azN z A).support =
     (aoq (A 0)).support∪(aoq (A 1)*c9 z).support :=
   Finsupp.support_add_eq (c3Q A hz)
 apply support_nonempty.mp
 rw [hs]
 obtain ⟨j,hj⟩:=hA
 fin_cases j
 · exact (support_nonempty.mpr (hn 0 hj)).mono Finset.subset_union_left
 · exact (support_nonempty.mpr (mul_ne_zero (hn 1 hj) (X_ne_zero z))).mono Finset.subset_union_right
private theorem c3P (A:Fin 2→lz F) {z :Fin 5} (hz :z≠0) :
  (azN z A).degreeOf 0=max (A 0).natDegree (A 1).natDegree := by
 rw [azN,← oj,cwT _ _ _ (c3Q A hz),
  oj,oj,
  degreeOf_mul_X_of_ne _ (Ne.symm hz)]
 simp [cXu]
private theorem cbx (A:Fin 2→lz F) (i z :Fin 5) (d:ℕ)
   (hA : ∀ j,(A j).natDegree≤d) :
   (azN z A).degreeOf i≤(if i=0 then d else 0)+(if i=z then 1 else 0) := by
 have h (j:Fin 2) : (aoq (A j)).degreeOf i≤ if i=0 then d else 0:= by
   rw [cXu]
   split <;> simp [hA]
 refine (qM i _ _).trans (oz ?_ ?_)
 · exact (h 0).trans (t4 _ _)
 · exact (p7 i _ _).trans (by rw [pQ]; exact vi (h 1) _)
private theorem eIp (O:Fin 2→Fin 2→lz F) (i:Fin 5) (d:ℕ)
   (hO : ∀ j l,(O j l).natDegree≤d) :
   (bJ7 O).degreeOf i ≤
     (if i=0 then d else 0)+(if i=3 then 1 else 0)+(if i=4 then 1 else 0) := by
 have h (l:Fin 2) :=cbx (fun j=>O j l) i 3 d (fun j=>hO j l)
 refine (qM i _ _).trans (oz ?_ ?_)
 · exact (h 0).trans (t4 _ _)
 · exact (p7 i _ _).trans (by rw [pQ]; exact vi (h 1) _)
theorem proof :aez.c1 := by
 intro u deleted h U V W j
 let A:=azN 4 U
 let B:=azN 3 V
 let O:=bJ7 W.output
 have hA : ∀ l,(U l).natDegree≤h:= by
   intro l
   have hh:=W.height_eq
   unfold uO at hh
   fin_cases l
   · change (U 0).natDegree≤h
     omega
   · change (U 1).natDegree≤h
     omega
 have hB : ∀ l,(V l).natDegree≤h:= by
   intro l
   have hh:=W.height_eq
   unfold uO at hh
   fin_cases l
   · change (V 0).natDegree≤h
     omega
   · change (V 1).natDegree≤h
     omega
 have hO : ∀ k l,(W.output k l).natDegree≤131071+h:= by
   intro k l
   by_cases hz :W.output k l=0
   · simp [hz]
   · have hh:=W.output_degree k l
     rw [Polynomial.degree_eq_natDegree hz,Nat.cast_lt] at hh
     omega
 have hAd (i:Fin 5) :=cbx U i 4 h hA
 have hBd (i:Fin 5) :=cbx V i 3 h hB
 have hOd (i:Fin 5) :=eIp W.output i (131071+h) hO
 have hAm:yV A:=⟨by simpa [A] using hAd 1,by simpa [A] using hAd 2⟩
 have hBm:yV B:=⟨by simpa [B] using hBd 1,by simpa [B] using hBd 2⟩
 have hOm:yV O:=⟨by simpa [O] using hOd 1,by simpa [O] using hOd 2⟩
 have hheight:max (A.degreeOf 0) (B.degreeOf 0)=h:= by
   simpa [A,B,c3P _ (by decide : (4 :Fin 5)≠0),
     c3P _ (by decide : (3:Fin 5)≠0),uO] using W.height_eq
 rw [eLJ]
 change (A*c9 1+B*c9 2 - O).weightedTotalDegree _ = _
 rw [cYi _ _ _ _ (c3R U (by decide) W.U_ne)
   (c3R V (by decide) W.V_ne) hAm hBm hOm,
   bfU _ _ hAm,bfU _ _ hBm,
   bfU _ _ hOm]
 fin_cases j
 · have hOx :O.degreeOf 0≤131071+h:= by simpa [O] using hOd 0
   simp [vO,GA]
   omega
 · simp [vO,GA]
 · have hAs :A.degreeOf 3=0:= by simpa [A] using hAd 3
   have hBs :B.degreeOf 3≤1 := by simpa [B] using hBd 3
   have hOs :O.degreeOf 3≤1 := by simpa [O] using hOd 3
   simp [vO,GA,hAs]
   omega
 · have hAt:A.degreeOf 4≤1 := by simpa [A] using hAd 4
   have hBt:B.degreeOf 4=0:= by simpa [B] using hBd 4
   have hOt:O.degreeOf 4≤1 := by simpa [O] using hOd 4
   simp [vO,GA,hBt]
   omega
end
end cxG
end
section
set_option backward.isDefEq.respectTransparency false
namespace bju
noncomputable section
open MvPolynomial Qo
variable {F:Type*} [Field F]
private def qW (j:Fin 5) (a b:F) :cy (Fin 5) F:=C a+MvPolynomial.X j*C b
def afY (x a b c d:F) (U V:cy (Fin 5) F) :cy (Fin 5) F :=
 Wj x U*qW 3 a b+Wj x V*qW 4 c d
theorem b9R (x a b c d:F) (U V:cy (Fin 5) F)
  (hU:yV U) (hV:yV V) :
  aa2 x a b c d (U*c9 1+V*c9 2)=afY x a b c d U V:= by
 simp only [map_add,pG,bs0 x a b c d U hU,bs0 x a b c d V hV]
 simp [aa2,aDV,afY,qW]
theorem dcH (q:ℕ) (x a b c d:F) (U V:cy (Fin 5) F) :
    XD q (afY x a b c d U V) =
      (graph q U).eval (mD x)*(mD a+Polynomial.X*mD b) +
      (graph q V).eval (mD x) *
        (mD c+Polynomial.X ^q*mD d) := by
  simp only [afY,map_add,pG,← bFp]
  simp [qW,XD]
theorem cbj (x y a b c d:F) (U V:cy (Fin 5) F) :
  Wj y (afY x a b c d U V)=afY x a b c d U V:= by
 have h: (Wj y).comp (Wj x)=Wj x := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [Wj]
 simp only [afY,map_add,pG,← AlgHom.comp_apply (Wj y) (Wj x),h]
 simp [qW,Wj]
private theorem cJP (j:Fin 5) (x :F) (Q:cy (Fin 5) F) :
  (Wj x Q).degreeOf j≤Q.degreeOf j:= by
 rw [← oj j (Wj x Q),← oj j Q]
 apply wB
 intro i
 rw [oj]
 fin_cases i <;> simp [Pi.single_apply,pQ,eq_comm]
private theorem cJO (j:Fin 5) (x :F) (Q:cy (Fin 5) F)
   (h3:j≠3) (h4 :j≠4) : (Wj x Q).degreeOf j=0:= by
 have h:=wB (fun _:Fin 5=>0) (Pi.single j 1)
   (![C x,0,0,c9 3,c9 4] :Fin 5→cy (Fin 5) F) Q (by
     intro i
     rw [oj]
     fin_cases i <;> simp [pQ,h3,h4])
 have hz :Q.weightedTotalDegree (fun _=>(0:ℕ))=0:= by
   simp [weightedTotalDegree,vG]
 rw [oj,hz] at h
 exact Nat.eq_zero_of_le_zero h
private theorem cJQ (i j:Fin 5) (a b:F) :
   (qW j a b).degreeOf i≤ if i=j then 1 else 0:= by
 refine (qM i _ _).trans (oz ?_ ?_)
 · simp
 · exact (degreeOf_mul_C_le (c9 j) i b).trans_eq (pQ i j)
theorem bZ6 (j:Fin 5) (x a b c d:F) (U V:cy (Fin 5) F) :
   (afY x a b c d U V).degreeOf j ≤
     if j=3 then YF U V else if j=4 then aab U V else 0:= by
 refine (qM j _ _).trans (oz ?_ ?_)
 · refine (p7 j _ _).trans ?_
   have hp:=cJQ j 3 a b
   have hu:=cJP j x U
   by_cases h3:j=3
   · subst j
     simp [YF] at hp hu ⊢
     omega
   by_cases h4 :j=4
   · subst j
     simp [aab,h3] at hp hu ⊢
     omega
   rw [cJO j x U h3 h4]
   simpa [h3,h4] using hp
 · refine (p7 j _ _).trans ?_
   have hp:=cJQ j 4 c d
   have hv :=cJP j x V
   by_cases h3:j=3
   · subst j
     simp [YF] at hp hv ⊢
     omega
   by_cases h4 :j=4
   · subst j
     simp [aab,h3] at hp hv ⊢
     omega
   rw [cJO j x V h3 h4]
   simpa [h3,h4] using hp
private def brO (f :lz F) :cy (Fin 5) F :=
 Polynomial.aeval (c9 0) f
private theorem eJW (x :F) (f :lz F) :
  Wj x (brO f)=C (f.eval x) := by
 rw [brO,← Polynomial.aeval_algHom_apply (Wj x)]
 simp only [Wj,aeval_X,Matrix.cons_val_zero,vw ,algebraMap_eq]
 exact Polynomial.eval₂_at_apply _ _
private theorem dVh (j:Fin 5) (f :lz F) :
  (brO f).degreeOf j≤f.natDegree*(c9 0:cy (Fin 5) F).degreeOf j:= by
 rw [brO,vw ,Polynomial.eval₂_eq_sum,Polynomial.sum]
 refine (degreeOf_sum_le j _ _).trans (u9 fun n hn => ?_)
 rw [algebraMap_eq]
 exact (degreeOf_C_mul_le _ j _).trans ((degreeOf_pow_le j _ n).trans
  (Nat.mul_le_mul_right _ (vZ n hn)))
def interpolant {N :ℕ} (x :Fin N→F) (v :Fin N→cy (Fin 5) F) :
    cy (Fin 5) F :=
  ∑ i,brO (Lagrange.basis Finset.univ x i)*v i
theorem cbi {N :ℕ} (x :Fin N→F) (hx :sH x)
   (v :Fin N→cy (Fin 5) F) (hv : ∀ i,Wj (x i) (v i)=v i)
   (j:Fin N) :Wj (x j) (interpolant x v)=v j:= by
 rw [interpolant,p9]
 simp only [pG,eJW]
 rw [Finset.sum_eq_single_of_mem j (qG j)]
 · rw [Lagrange.eval_basis_self hx.injOn (qG j),map_one,one_mul,hv]
 · intro i _ hij
   rw [Lagrange.eval_basis_of_ne hij (qG j),map_zero,zero_mul]
theorem bZ2 {N :ℕ} (x :Fin N→F) (hx :sH x)
  (v :Fin N→cy (Fin 5) F) (j:Fin 5) (b:ℕ)
  (hv : ∀ i,(v i).degreeOf j≤b) :
  (interpolant x v).degreeOf j≤(N - 1)*(c9 0:cy (Fin 5) F).degreeOf j+b:= by
 refine (degreeOf_sum_le j _ _).trans (u9 fun i hi => ?_)
 have h:=dVh j (Lagrange.basis Finset.univ x i)
 rw [Lagrange.natDegree_basis hx.injOn hi,Finset.card_univ,Fintype.card_fin] at h
 exact (p7 j _ _).trans (Nat.add_le_add h (hv i))
end
end bju
end
section
namespace baD
noncomputable section
open K1 cu qQ aZb
private theorem aWl (i j:Fin 4) :
   Function.Commute (ER i) (ER j) := by
 intro Q
 by_cases hij:i=j
 · subst j
   rfl
 apply MvPolynomial.ext
 intro d
 simp only [ER,MvPolynomial.coeff_pderiv,v8 ,xm,
   qz hij,qz (Ne.symm hij),add_zero]
 rw [add_right_comm d (n5 i 1) (n5 j 1)]
 ring
private theorem fXv {q:zI} {P:Jet} {k :ℕ}
   {y v :HR} (hyv :aF5 q y v) (hk :k<p)
   (h : ∀ a b:ℕ,a+b<k→A5 1 b (A5 0 a P)∈q.asIdeal) :
   Qr.bQ5 (pz (Qr.aaU y v)) P k := by
 let T:=gT.iJ
 let g:= Qr.aaU y v
 have iter0 (r :ℕ) (Q:Jet) : (ER 0)^[r] (T Q) =
     r.factorial•T (A5 0 r Q) :=bNJ 0 r Q
 have iter1 (r :ℕ) (Q:Jet) : (ER 1)^[r] (T Q) =
     r.factorial•T (A5 1 r Q) :=bNJ 1 r Q
 have scale (i:Fin 4) (n r :ℕ) (Q:gT.Ambient) :
     (ER i)^[r] (n•Q)=n•(ER i)^[r] Q:= by
   have hcomm:Function.Commute (ER i) (fun A:gT.Ambient=>n•A) :=
     fun A=>map_nsmul (MvPolynomial.pderiv (R:=FX) i) n A
   exact (hcomm.iterate_left r) Q
 intro a b hab
 have hforward:T (A5 1 b (A5 0 a P))∈pz g:= by
   change A5 1 b (A5 0 a P)∈(pz g).comap T
   rw [ddb hyv]
   exact h a b hab
 have hcomm:=((aWl 0 1).iterate_iterate a b) (T P)
 change (ER 0)^[a] ((ER 1)^[b] (T P)) =
   (ER 1)^[b] ((ER 0)^[a] (T P)) at hcomm
 have hleft: (ER 0)^[a] ((ER 1)^[b] (T P)) =
     b.factorial•a.factorial•T (A5 0 a (A5 1 b P)) := by
   rw [iter1,scale,iter0]
 have hright: (ER 1)^[b] ((ER 0)^[a] (T P)) =
     a.factorial•b.factorial•T (A5 1 b (A5 0 a P)) := by
   rw [iter0,scale,iter1]
 have he :=oK g (hleft.symm.trans (hcomm.trans hright))
 simp only [map_nsmul,RingHom.mem_ker.mp hforward,nsmul_zero] at he
 let:CharP HR p :=
   charP_of_injective_ringHom (algebraMap K HR).injective p
 have hp:=CharP.char_is_prime_of_two_le K p (by decide)
 have hfac (n:ℕ) (hn:n<p) : (n.factorial:HR)≠0:= by
   intro hz
   exact (not_le_of_gt hn)
     (hp.dvd_factorial.mp ((CharP.cast_eq_zero_iff HR p _).mp hz))
 simp only [nsmul_eq_mul] at he
 exact RingHom.mem_ker.mpr
   ((mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (hfac b (by omega)))).resolve_left
     (hfac a (by omega)))
theorem proof :YZ.c1 := by
 intro q P k hq hk hP y v hyv
 let I:=pz (Qr.aaU y v)
 have hjet:Qr.cxB P y v k :=
  aZb.proof I (ep4 hq hyv) P k hk (fXv hyv hk hP) y v rfl
 exact eam (aUO P) y v k hjet
end
end baD
end
section
namespace bau
noncomputable section
open aR dN vS Dr lB Kd ap8 Filter
private lemma boW {ι:Type} [nX ι] (used :List ι)
   (H G: (ι→ℕ)→ℚ) (a :ι→ℕ) :
   uU used (fun b=>H b-G b) a=uU used H a - uU used G a := by
 induction used generalizing a with
 | nil=>rfl
 | cons i rest ih=>simp only [uU,ih]; ring
private lemma boV {ι:Type} [nX ι] (used :List ι)
   (H : (ι→ℕ)→ℚ) (a v :ι→ℕ) :
   uU used (fun b=>H (b+v)) a=uU used H (a+v) := by
 induction used generalizing a with
 | nil=>rfl
 | cons i rest ih=>simp only [uU,ih,add_right_comm a (step i) v]
private lemma auS {ι:Type} {Q: (ι→ℕ)→Prop} (v :ι→ℕ)
  (h : ∀ᶠ a in atTop,Q a) : ∀ᶠ a in atTop,Q (a+v) := by
 obtain ⟨u,hu⟩:=eventually_atTop.mp h
 exact eventually_atTop.mpr ⟨u,fun a ha=>hu (a+v) (ha.trans (le_add_of_nonneg_right zero_le))⟩
private lemma wD {ι:Type} [nX ι] (used :List ι) (v :ι→ℕ)
  (B C G H : (ι→ℕ)→ℚ) (heq : ∀ a,B (a+v)+H a=G (a+v))
  (hpos : ∀ᶠ a in atTop,0≤uU used (fun b=>B b - C b) a) :
  ∀ᶠ a in atTop,uU used C (a+v)≤uU used G (a+v) - uU used H a := by
 have hid : (fun a=>B (a+v))=fun a=>G (a+v) - H a := by
  funext a
  linarith [heq a]
 filter_upwards [auS v hpos] with a ha
 rw [boW] at ha
 rw [← boV used B,hid,boW,boV] at ha
 linarith
private lemma b5z {ι σ:Type} [oD ι] [nX ι] (slot:σ→ι) :
  aiD slot (⊤ : lI (cy σ aU)) := by
 intro f hf a
 exact Submodule.mem_top
private lemma b5Z {ι σ:Type} [nX ι] (slot:σ→ι) (a :ι→ℕ) :
  lO slot (⊤ : lI (cy σ aU)) a=0:= by
 have :Subsingleton (cy σ aU ⧸ (⊤ : lI (cy σ aU))) :=
  (Ideal.Quotient.subsingleton_iff).2 rfl
 simp [lO,Module.finrank_eq_zero_of_subsingleton]
theorem a4H
  {ι σ:Type} [oD ι] [nX ι] [oZ σ]
  (slot:σ→ι) (I K:lI (cy σ aU))
  (hI:aiD slot I) (hK:aiD slot K) (hle :I≤K) :
  let H := fun a=>lO slot I a-lO slot K a
  (∃ P:cy ι ℚ,∀ᶠ a in atTop,u5 (fun i=>(a i:ℚ)) P=H a) ∧
  ∀ used :List ι,∀ᶠ a in atTop,0≤uU used H a := by
 classical
 let _:=pU σ
 let _:th σ:=t7 _ (qx σ).injective
 have :t8 σ:=sS
 let m:t6 σ:=vk
 obtain ⟨A,hA⟩:=m.exists_finset_standardExponents_iff I
 obtain ⟨B,hB⟩:=m.exists_finset_standardExponents_iff K
 have hAB:zJ B⊆zJ A:= by
  intro e he
  exact (hA e).mp (fun f hf=>(hB e).mpr he f (hle hf))
 have eqI:lO slot I=DL slot A:= by
  funext a
  rw [aXV slot m I hI a]
  simp only [DL,hA,zJ,xu]
 have eqK:lO slot K=DL slot B:= by
  funext a
  rw [aXV slot m K hK a]
  simp only [DL,hB,zJ,xu]
 rw [eqI,eqK]
 exact aKr.proof slot A B hAB
theorem cNl
    {ι:Type} [oD ι] [nX ι] (fF:ι→Shape) (J:lI pC)
    (base :ι) (used :List ι) (hsh : ∀ i,bF (fF i))
    (hbase :ChamberBox (fF base))
    (hn:used.Nodup) (hd:oY J≤used.length) :
    ∀ᶠ a in atTop,uU used (lO (Fd fF) (HW fF J)) a =
      BE (nq J used.length) (used.map fF) (fF base) := by
  let slot:=Fd fF
  let I:=HW fF J
  have hI:=(ox fF J).1
  have hall:=(a4H slot I ⊤ hI (b5z slot) le_top).1
  rw [show (fun a=>lO slot I a-lO slot ⊤ a)=lO slot I by
    funext a; simp [b5Z]] at hall
  obtain ⟨P,hP⟩:=hall
  have hrank :lO slot I=fun a=>(Sn J (p5 (ku fF a)) :ℚ) := by
    funext a
    rw [(ox fF J).2 a,eOX fF hsh a]
  rw [hrank] at hP ⊢
  obtain ⟨u,hu⟩:=eventually_atTop.mp hP
  let K:= fun a=>(Sn J (p5 (ku fF a)) :ℚ)
  have hcompare (v :ι→ℕ) (hv :0<v base) :=
    fT9 fF hsh J P u v (by
      change 0 < ∑ i,v i*(fF i).t
      have hle :=Finset.single_le_sum (f := fun i=>v i*(fF i).t)
        (fun _ _=>Nat.zero_le _) (qG base)
      exact (Nat.mul_pos hv hbase.2.2).trans_le hle) hu _ hd
  have hdeg:P.totalDegree≤used.length :=
    bO7 P u _ fun v hv=>(hcompare v (hv base)).1
  let F:= fun v :ι→ℕ =>
    u5 (fun i=>(v i:ℚ)) (x7 used.length P)
  have hright:=cKj used F
    (fun v=>nq J used.length (ku fF v)) (step base) fun v hv =>
      (buL P u v hdeg).symm.trans (hcompare v (by
        have h:step base base≤v base :=hv base
        exact Nat.succ_le_iff.mp (by simpa [step] using h))).2
  filter_upwards [eventually_ge_atTop u] with a ha
  change uU used K a= _
  calc
    _=uU used (fun v=>u5 (fun i=>(v i:ℚ)) P) a :=
      cKj used K _ a fun v hv=>(hu v (ha.trans hv)).symm
    _=uU used F (step base) :=bD4 used hn P hdeg a (step base)
    _ = _:= by rw [hright,dV2,aQe]
theorem proof :
    bjC.c1 := by
  classical
  intro J p boxes hp hboxes _ hdim D hD hreg
  let ι:=Option (Option (Fin boxes.length))
  let base :ι:=none
  let i:ι:=some none
  let emb:Fin boxes.length→ι:= fun k=>some (some k)
  let rest:=(List.finRange boxes.length).map emb
  let fF:ι→Shape
    | none=>⟨3, 3,1⟩
    | some none=>p
    | some (some k)=>boxes.get k
  have hsh (k :ι) :bF (fF k) := by
    cases k with
    | none =>
      change bF ⟨3, 3,1⟩
      exact ⟨by decide,by decide⟩
    | some k=>cases k with
      | none=>exact hp
      | some k=>exact hboxes _ (List.get_mem _ _)
  have hbaseBox :ChamberBox (fF base) := by
    change ChamberBox (⟨3, 3,1⟩:Shape)
    exact ⟨by decide,by decide,by decide⟩
  have hi:i∉rest:= by
    intro h
    obtain ⟨k,_,hk⟩:=List.mem_map.mp h
    change (some (some k) :Option (Option (Fin boxes.length)))=some none at hk
    have hinner : (some k :Option (Fin boxes.length))=none :=vh hk
    cases hinner
  have hn:rest.Nodup:=(List.nodup_finRange _).map
    (fun _ _ h=>vh (vh h))
  have hn' : (i :: rest).Nodup:=List.nodup_cons.mpr ⟨hi,hn⟩
  have hmap :rest.map fF=boxes := by
    simp [rest,List.map_map,Function.comp_def,emb,fF]
  have hlen:rest.length=boxes.length:= by simp [rest]
  let slot:=Fd fF
  let I:=HW fF J
  let I₁:=HW fF (cut J D)
  let I₂:=HW fF (cut J (D^2))
  have hgraded₂:=(ox fF (cut J (D^2))).1
  obtain ⟨B,C,hB,hC,hBI,hCI,heqB,heqC⟩ :=
    bjA.proof fF i J D hD hreg (ox fF J).1 hgraded₂
  have hposB:=(a4H slot B I₂ hB hgraded₂ hBI).2 rest
  have hposC:=(a4H slot C I₁ hC (ox fF (cut J D)).1 hCI).2 rest
  have hspendB:=wD rest (step i) (lO slot B) (lO slot I₂) (lO slot I)
    (lO slot I) heqB hposB
  have hspendC:=wD rest (step i) (lO slot C) (lO slot I₁) (lO slot I₂)
    (lO slot I₁) heqC hposC
  have hd₁:oY (cut J D)≤ rest.length:= by
    have hdrop:oY (cut J D)≤oY J - 1 :=aCR hreg
    omega
  have hd₀:oY J≤(i :: rest).length:= by simpa [hlen] using hdim
  have hr₀:=cNl fF J base (i :: rest) hsh hbaseBox hn' hd₀
  have hr₁:=cNl fF (cut J D) base rest hsh hbaseBox hn hd₁
  have hfinal : ∀ᶠ _a in (atTop:Filter (ι→ℕ)),
      2*BE (nq (cut J D) boxes.length) boxes ⟨3, 3,1⟩ ≤
        BE (nq J (p :: boxes).length) (p :: boxes) ⟨3, 3,1⟩:= by
    filter_upwards [hspendB,hspendC,hr₀,hr₁,auS (step i) hr₁] with a hb hc h₀ h₁ h₁'
    rw [List.map_cons,hmap,qy ,hlen] at h₀
    rw [hlen,hmap] at h₁ h₁'
    change uU rest (lO slot I) (a+step i) - uU rest (lO slot I) a =
      BE (nq J (boxes.length+1)) (p :: boxes) ⟨3, 3,1⟩ at h₀
    change uU rest (lO slot I₁) a =
      BE (nq (cut J D) boxes.length) boxes ⟨3, 3,1⟩ at h₁
    change uU rest (lO slot I₁) (a+step i) =
      BE (nq (cut J D) boxes.length) boxes ⟨3, 3,1⟩ at h₁'
    simp only [qy]
    linarith [hb,hc,h₀,h₁,h₁']
  obtain ⟨_,hfinal⟩:=hfinal.exists
  unfold tW
  rw [qy ,pow_succ,mul_comm ((2 :ℚ)^boxes.length) 2,← div_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (le_div_iff₀ (by norm_num : (0:ℚ)<2)).2 (by simpa [mul_comm] using hfinal)
end
end bau
end
