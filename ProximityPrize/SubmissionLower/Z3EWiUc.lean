import ProximityPrize.SubmissionLower.ZgdIx1d
import ProximityPrize.SubmissionLower.ZFFuWqa
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ArkLib.Data.Finset.PairwiseIntersection
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Visible
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finsupp.Interval
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Sym.NatCard
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.Topology.Algebra.MvPolynomial
import ProximityPrize.SubmissionLower.AC
set_option Elab.async false
set_option maxHeartbeats 1600000
open _root_ renaming AddCommGroup→vj,AddMonoidAlgebra.single→t9,AddMonoidAlgebra.single_mul_single→Av,AlgEquiv.apply_symm_apply→qy,AlgHom.coe_ringHom_injective→G7,AlgHom.commutes→yo,AlgHom.id→wB,Algebra→c9,Algebra.IsAlgebraic→GB,Algebra.TensorProduct.cancelBaseChange→GR,Algebra.TensorProduct.comm→yJ,Algebra.TensorProduct.comm_tmul→G5,Algebra.TensorProduct.includeRight→Gn,Algebra.TensorProduct.lift_tmul→Cy,Algebra.TensorProduct.map→zm,Algebra.TensorProduct.tmul_mul_tmul→zi,Algebra.algebraMap→aU,Algebra.ofId→yB,AlgebraicIndependent→zg,CommRing→n5,DFunLike.congr_fun→zh,DQ.SourceRing→lz,DQ.specialize→t6,Field→mD,Finset.mem_image_of_mem→Fz,Finset.mem_singleton→Et,Finset.mem_univ→yU,Finset.smul_sum→wA,Finset.sum_congr→uz,Finsupp.comapDomain_sumElim_comapDomain→G0,Finsupp.optionElim_some→FV,Finsupp.single→zf,Finsupp.weight→ oY,Finsupp.weight_apply→Du,Finsupp.weight_eq_sum→Aa,Fintype.sum_option→z7,Fintype.sum_sum_type→Gk,Fintype.univ_bool→Ef,Function.Injective→sS,Function.Surjective→G2,Function.iterate_succ_apply'→EK,Ideal→ oD,Ideal.Quotient.eq_zero_iff_mem→Ar,Ideal.Quotient.mk→ ox,Ideal.Quotient.mkₐ→G9,Ideal.map_map→wY,Ideal.mem_span_singleton_sup→Gr,Ideal.span→t3
open _root_ renaming IsAlgebraic→zS,IsDomain→th,IsFractionRing→t4,IsFractionRing.injective→wR,IsLocalization→uh,IsLocalization.mk'_mem_map_algebraMap_iff→Fa,IsLocalization.mul_mk'_eq_mk'_of_mul→FK,IsScalarTower→vh,IsScalarTower.algebraMap_apply→Dz,IsScalarTower.of_algebraMap_eq→u9,IsScalarTower.toAlgHom→vk,LinearMap.finrank_le_finrank_of_surjective→G6,Module.Finite→ oZ,Module.Finite.equiv→y5,Module.Finite.of_surjective→Ea,Module.finBasis→xL,Module.finrank→pG,MvPolynomial→lJ,MvPolynomial.C→nq,MvPolynomial.X→cy,MvPolynomial.affineHilbertPolynomial→vl,MvPolynomial.algebraMap_eq→t7,MvPolynomial.algebraMvPolynomial→Bf,MvPolynomial.algebraTensorAlgEquiv→u5,MvPolynomial.algebraTensorAlgEquiv_tmul→FR,MvPolynomial.coeff_weightedHomogeneousComponent→Eg,MvPolynomial.commAlgEquiv→t5,MvPolynomial.eval→qz,MvPolynomial.eval₂Hom_C→vH,MvPolynomial.eval₂Hom_X'→G4,MvPolynomial.induction_on'→EP,MvPolynomial.isLocalization→Dw,MvPolynomial.isWeightedHomogeneous_X→zk,MvPolynomial.map→lI,MvPolynomial.map_X→qm,MvPolynomial.map_map→C4,MvPolynomial.mem_restrictBidegree→qG,MvPolynomial.mem_restrictBidegree_iff_weightedTotalDegree_le→Au,MvPolynomial.mem_support_iff→G8,MvPolynomial.monomial→ oj,MvPolynomial.monomial_add_single→xu,MvPolynomial.mul_mem_restrictBidegree→pL,MvPolynomial.optionEquivLeft→u8,MvPolynomial.pderiv_eq_zero_of_degreeOf_eq_zero→G3,MvPolynomial.quotientBidegreeLE→vG,MvPolynomial.renameEquiv_apply→z8,MvPolynomial.restrictBidegree→sH,MvPolynomial.ringHom_ext→v8
open _root_ renaming MvPolynomial.smul_eq_C_mul→GF,MvPolynomial.support_X→Dv,MvPolynomial.support_map_subset→C9,MvPolynomial.weightedHomogeneousComponent→uJ,MvPolynomial.weightedTotalDegree_pderiv_le_sub→F9,Nat.add_comm→p5,Nat.add_left_comm→FU,Nat.add_sub_of_le→G1,Nat.eq_zero_of_le_zero→Gj,Nat.mul_le_mul_left→Df,Nat.sub_le_sub_right→Ee,Nat.zero_add→uW,Option→lV,Polynomial→ oq,Polynomial.C→ ov,Polynomial.X→pQ,Polynomial.aeval→ oy,Polynomial.aeval_C→xI,Polynomial.aeval_X→zE,Polynomial.degreeLT→xm,Polynomial.derivative_map→FQ,Polynomial.eval_map→ze,Polynomial.le_natDegree_of_ne_zero→Gi,Polynomial.map→x7,Polynomial.ringHom_ext→C5,Prod.mk_add_mk→yL,Prod.snd_sum→zc,RingHom.congr_fun→t8,RingHom.ext→vi,Set.range→p9,Submodule.span→vw,Submodule.subset_span→xW,Submodule.sum_mem→GY,Submonoid→v9,Submonoid.powers→yQ,Subsingleton.elim→yl,aqf.Affine→nX,congrArg→ oz,cu.Equation→qU,inferInstance→vZ,map_add→pC,map_mul→nI,map_ne_zero_iff→zR,map_one→pU,map_pow→sI,map_sub→p7,map_sum→pz,map_zero→ oK
open _root_ renaming mul_assoc→qJ,mul_comm→qx,mul_one→qM,nonZeroDivisors→zd,nonZeroDivisors.ne_zero→z9,one_mul→p6
set_option autoImplicit true
section
namespace aqf
noncomputable section
open DQ ane
def c1 :Prop :=
  ∀ (n:ℕ) (J:oD (lz n)),J.IsPrime →
    (vl J).natDegree=1 → ∃ N :ℕ,
    ∀ u v :ℕ,N≤u→N≤v →
      (∀ p∈Yy J (u+1,v),
        avS J*p∈Yy J (u+1,v)→p∈Yy J (u,v)) ∧
      (∀ p∈Yy J (u,v+1),
        avS J*p∈Yy J (u+1,v)→p∈Yy J (u,v))
def c2 :Prop :=
 ∀ (n:ℕ) (J:oD (lz n)),Nonempty (cxk J)
private theorem transfer {n:ℕ} {J:oD (lz n)} (T:cxk J)
   (d e f :ℕ×ℕ)
   (h : ∀ p∈Yy J d,avS J*p∈Yy J e →
     p∈Yy J f)
   (x :agD J) (hx :x∈box J d.1 d.2)
   (hq:aaK J (aD3 n)*x∈box J e.1 e.2) :x∈box J f.1 f.2 := by
 obtain ⟨s,hs,p,q,hp,hq',hpe,hqe⟩:=T.clear_boxes d e x _ hx hq
 have he :avS J*p=q:=T.injective_toSlice (by
   rw [nI,T.ab6,hpe,hqe,mul_smul_comm])
 have hm:=T.map_box f p (h p hp (he.symm ▸ hq'))
 rw [hpe] at hm
 simpa [smul_smul,hs] using (box J f.1 f.2).smul_mem s⁻¹ hm
theorem of_children (h1 :c1) (h2 :c2) :ane.c2 := by
 intro n J hJ hdim
 obtain ⟨T⟩:=h2 n J
 obtain ⟨N,hN⟩:=h1 n J hJ hdim
 refine ⟨N,fun u v hu hv=>⟨?_,?_⟩⟩
 · exact transfer T (u+1,v) (u+1,v) (u,v) (hN u v hu hv).1
 · exact transfer T (u,v+1) (u+1,v) (u,v) (hN u v hu hv).2
end
end aqf
end
section
namespace aR1
noncomputable section
open akS
open scoped Polynomial TensorProduct
variable {F A:Type} [mD F] [n5 A] [c9 F A]
private def aCr {ι:Type} (a :A) (w:ι→A) (d:ℕ) :
  Submodule F A :=
 vw F (p9 fun ij:Fin d×ι=>a^(ij.1 :ℕ)*w ij.2)
private instance {ι:Type} [Finite ι] (a :A) (w:ι→A) (d:ℕ) :
  oZ F (aCr (F:=F) a w d) :=
 Module.Finite.span_of_finite F (Set.finite_range _)
private theorem cM7 {ι:Type} (a :A) (w:ι→A)
   {d:ℕ} (i:ι) (p:F[X]) (hp:p.degree<d) :
   oy a p*w i∈aCr (F:=F) a w d:= by
 let L:xm F d →ₗ[F] A :=
   (LinearMap.mulRight F (w i)).comp
     ((oy a).toLinearMap.comp (xm F d).subtype)
 let x :xm F d:=⟨p,Polynomial.mem_degreeLT.mpr hp⟩
 change L x∈aCr (F:=F) a w d
 rw [← (Polynomial.degreeLT.basis F d).sum_repr x,pz]
 apply GY
 intro j _
 rw [map_smul]
 apply Submodule.smul_mem
 apply xW
 refine ⟨⟨j,i⟩,?_⟩
 simp [L]
private theorem eNr {ι:Type} (a :A) (w:ι→A)
   (W:Submodule F A) (hW:W=vw F (p9 w)) (k :ℕ) :
   abb a W k≤aCr a w (k+1) := by
 have hbase (d:ℕ) (hd:0<d) :W≤aCr a w d:= by
   rw [hW]
   apply Submodule.span_le.mpr
   rintro _ ⟨i,rfl⟩
   apply xW
   exact ⟨⟨⟨0,hd⟩,i⟩,by simp⟩
 induction k with
 | zero=>exact hbase 1 (by decide)
 | succ k ih =>
   change W ⊔ (abb a W k).map (LinearMap.mulLeft F a)≤aCr a w (k+1+1)
   refine sup_le (hbase _ (by omega)) ((Submodule.map_mono ih).trans ?_)
   apply Submodule.map_le_iff_le_comap.mpr
   apply Submodule.span_le.mpr
   rintro _ ⟨⟨j,i⟩,rfl⟩
   change a*(a^(j:ℕ)*w i)∈aCr (F:=F) a w (k+1+1)
   rw [← qJ,← pow_succ']
   apply xW
   exact ⟨⟨j.succ,i⟩,rfl⟩
private theorem ekN (a :A) (W:Submodule F A)
    {m r :ℕ} (w:Fin m→A) (v :Fin r→A)
    (hW:W=vw F (p9 w))
    (b:F[X]) (hb:b≠0) (q:Fin m→Fin r→F[X])
    (hrel : ∀ i,oy a b*w i = ∑ j,oy a (q i j)*v j) :
    ∃ C:ℕ,∀ k :ℕ,pG F (abb a W k)≤C+k*r := by
  classical
  let D:=Finset.univ.sup (fun ij:Fin m×Fin r=>(q ij.1 ij.2).natDegree)
  have hD (i:Fin m) (j:Fin r) : (q i j).natDegree≤D :=
    Finset.le_sup (s :=Finset.univ) (f := fun ij:Fin m×Fin r=>(q ij.1 ij.2).natDegree)
      (yU (i,j))
  refine ⟨(b.natDegree+1)*m+(D + 1)*r,fun k => ?_⟩
  let U:=aCr (F:=F) a w (b.natDegree+1)
  let V:=aCr (F:=F) a v (k+D + 1)
  have hUV:aCr a w (k+1)≤U ⊔ V:= by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨l,i⟩,rfl⟩
    let p:F[X] :=pQ ^(l:ℕ)
    have hrem: (p % b).degree<b.natDegree+1 :=
      (Polynomial.degree_mod_lt p hb).trans (Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_self _))
    have hl: (p/b).natDegree≤k :=Polynomial.natDegree_le_of_degree_le
      ((Polynomial.degree_div_le p b).trans
        (Polynomial.degree_X_pow_le _ |>.trans (by exact_mod_cast Nat.le_of_lt_succ l.isLt)))
    have hquot (j:Fin r) : (p/b*q i j).degree<k+D + 1 := by
      have h:=(Polynomial.natDegree_mul_le (p:=p/b) (q:=q i j)).trans
        (Nat.add_le_add hl (hD i j))
      exact (Polynomial.degree_le_of_natDegree_le h).trans_lt (by exact_mod_cast Nat.lt_succ_self _)
    have hsplit :a^(l:ℕ)*w i =
        (∑ j,oy a (p/b*q i j)*v j) +
          oy a (p % b)*w i:= by
      have h:=oz (fun x :F[X]=>oy a x*w i)
        (EuclideanDomain.div_add_mod p b).symm
      change oy a p*w i= _ at h
      rw [Polynomial.aeval_X_pow] at h
      simp only [pC,nI,add_mul] at h ⊢
      rw [h,qx (oy a b) (oy a (p/b)),
        qJ,hrel i,Finset.mul_sum]
      simp only [qJ]
    change a^(l:ℕ)*w i∈U ⊔ V
    rw [hsplit]
    exact (U ⊔ V).add_mem
      ((show V≤U ⊔ V from le_sup_right) (V.sum_mem fun j _=>cM7 a v j _ (hquot j)))
      ((show U≤U ⊔ V from le_sup_left) (cM7 a w i _ hrem))
  have bound (d e :ℕ) (u:Fin e→A) :
      pG F (aCr (F:=F) a u d)≤d*e := by
    let gen:Fin d×Fin e→A:= fun ij=>a^(ij.1 :ℕ)*u ij.2
    change (p9 gen).finrank F≤d*e
    have hc:Fintype.card (Fin d×Fin e)=d*e := by simp [Fintype.card_prod]
    exact hc ▸ finrank_range_le_card (R:=F) gen
  have h:=(Submodule.finrank_mono ((eNr a w W hW k).trans hUV)).trans
    ((Submodule.finrank_add_le_finrank_add_finrank U V).trans (Nat.add_le_add (bound _ _ w) (bound _ _ v)))
  simpa only [Nat.add_mul,Nat.add_assoc,FU,p5] using h
theorem ekM (a :A) (W:Submodule F A) [oZ F W]
    (E :Type) [mD E] [c9 F[X] E] [t4 F[X] E]
    (hfinite :letI:c9 F[X] A:=bgf a; oZ E (E ⊗[F[X]] A)) :
    letI:c9 F[X] A:=bgf a
    ∃ C:ℕ,∀ k :ℕ,pG F (abb a W k) ≤
      C+k*pG E (E ⊗[F[X]] A) := by
  classical
  let:c9 F[X] A:=bgf a
  let:oZ E (E ⊗[F[X]] A) :=hfinite
  let R:=F[X]
  let S:=zd R
  let T:=E ⊗[R] A
  let f :A →ₗ[R] T:=TensorProduct.mk R E A 1
  let:IsLocalizedModule S f :=IsLocalization.tensorProduct_isLocalizedModule S E
  let bW:=xL F W
  let w:=W.subtype ∘ bW
  have hW:W=vw F (p9 w) := by
    rw [show p9 w=W.subtype '' p9 bW from Set.range_comp _ _,
      ← Submodule.map_span,bW.span_eq,Submodule.map_subtype_top]
  let bT:=xL E T
  obtain ⟨s,hs⟩:=IsLocalizedModule.exist_integer_multiples_of_finite S f bT
  choose v hv using hs
  let c (ij:Fin (pG F W)×Fin (pG E T)) :=
    bT.repr (f (w ij.1)) ij.2
  obtain ⟨d,hd⟩:=IsLocalization.exist_integer_multiples_of_finite S c
  choose g hg using hd
  have hlift (i:Fin (pG F W)) :
      f ((s.val*d.val)•w i)=f (∑ j,g (i,j)•v j) := by
    calc
      _=s.val•(d.val•f (w i)) := by rw [map_smul,mul_smul]
      _=s.val•(d.val • ∑ j,c (i,j)•bT j) := by rw [← bT.sum_repr (f (w i))]
      _ = ∑ j,g (i,j)•f (v j) := by
        rw [wA,wA]
        apply uz rfl
        intro j _
        rw [← smul_assoc d.val (c (i,j)) (bT j),← hg (i,j),algebraMap_smul E,
          smul_comm s.val (g (i,j)),← hv j]
      _ = _:= by simp
  choose t ht using fun i=>IsLocalizedModule.exists_of_eq (S:=S) (f :=f) (hlift i)
  let e := ∏ i,t i
  let b:=e.val*(s.val*d.val)
  have hb:b≠0:=mem_nonZeroDivisors_iff_ne_zero.mp
    (show b∈S from mul_mem e.property (mul_mem s.property d.property))
  refine ekN a W w v hW b hb (fun i j=>e.val*g (i,j)) ?_
  intro i
  change b•w i = ∑ j,(e.val*g (i,j))•v j
  have he (x :A) :e.val•x=(∏ j∈Finset.univ.erase i,t j).val•(t i).val•x := by
    rw [← mul_smul]
    congr 1
    exact oz Subtype.val (Finset.prod_erase_mul Finset.univ t (yU i)).symm
  rw [show b=e.val*(s.val*d.val) from rfl,mul_smul]
  simp only [mul_smul,← wA]
  rw [he,he]
  exact oz _ (by simpa only [Submonoid.smul_def,mul_smul] using ht i)
end
end aR1
end
section
namespace czC
noncomputable section
open cu DQ ane aqf MvPolynomial
open scoped BigOperators TensorProduct
variable {n:ℕ} (J:oD (lz n))
private def baseChange :jY n ⊗[FX] nX J ≃ₐ[jY n] agD J:= by
 let E :=jY n
 let R:=lz n
 let e₀:E ⊗[FX] R ≃ₐ[E] auc n:=u5 FX E
 let i:R →+* E ⊗[FX] R :=
  (Gn (A:=E) (R:=FX)).toRingHom
 have hmap :e₀.toAlgHom.toRingHom.comp i=lI (aU FX E) := by
  apply vi
  intro p
  change e₀ (1 ⊗ₜ[FX] p)=lI (aU FX E) p
  simpa only [e₀,one_smul] using FR FX E 1 p
 have hI:Gu J=(J.map i).map e₀.toAlgHom.toRingHom:= by
  rw [wY i e₀.toAlgHom.toRingHom,hmap]
 exact (Algebra.TensorProduct.tensorQuotientEquiv E R E J).trans
  (Ideal.quotientEquivAlg (J.map i) (Gu J) e₀ hI)
private theorem baseChange_tmul (c:jY n) (p:lz n) :
   baseChange J (c ⊗ₜ[FX] ox J p) =
     c•aaK J (lI (aU FX (jY n)) p) := by
 change aaK J (u5 FX (jY n) (c ⊗ₜ[FX] p))= _
 rw [FR]
 exact (G9 (jY n) (Gu J)).toLinearMap.map_smul c _
private def bxO:UG J ≃ₐ[FX] lz n ⊗[FX] nX J:= by
 let e :nX J ⊗[FX] lz n ≃ₐ[nX J] UG J :=
  u5 FX (nX J)
 exact (e.symm.restrictScalars FX).trans
  (yJ FX (nX J) (lz n))
private def extend:lz n ⊗[FX] nX J →ₐ[FX] jY n ⊗[FX] nX J :=
 zm (vk FX (lz n) (jY n))
  (wB FX (nX J))
private def toSlice :UG J →ₐ[FX] agD J :=
 ((baseChange J).toAlgHom.restrictScalars FX).comp ((extend J).comp (bxO J).toAlgHom)
private theorem gBZ:sS (toSlice J) := by
 have hext:sS (extend J) := by
  change sS (TensorProduct.map
   (vk FX (lz n) (jY n)).toLinearMap
   (wB FX (nX J)).toLinearMap)
  exact TensorProduct.map_injective_of_flat_flat _ _
   (wR (lz n) (jY n)) Function.injective_id
 exact (baseChange J).injective.comp (hext.comp (bxO J).injective)
private theorem bO0 (p r :lz n) :
    toSlice J (C (ox J p)*lI (aU FX (nX J)) r) =
      aU (lz n) (jY n) r •
        aaK J (lI (aU FX (jY n)) p) := by
  have hC (a :nX J) :bxO J (C a)=(1 :lz n) ⊗ₜ[FX] a := by
    change yJ FX (nX J) (lz n)
      ((u5 FX (nX J)).symm (oj 0 a))= _
    rw [algebraTensorAlgEquiv_symm_monomial,G5 ,
      monomial_zero',C_1]
  have hr :bxO J (lI (aU FX (nX J)) r) =
      r ⊗ₜ[FX] (1 :nX J) := by
    change yJ FX (nX J) (lz n)
      ((u5 FX (nX J)).symm
        (lI (aU FX (nX J)) r))= _
    simp only [algebraTensorAlgEquiv_symm_map,G5]
  change baseChange J (extend J (bxO J
    (C (ox J p)*lI (aU FX (nX J)) r)))= _
  rw [nI,hC,hr,zi ,p6,qM]
  change baseChange J (zm
    (vk FX (lz n) (jY n)) (wB FX (nX J))
    (r ⊗ₜ[FX] ox J p))= _
  rw [Algebra.TensorProduct.map_tmul]
  exact baseChange_tmul J _ p
private theorem gBY:toSlice J (avS J)=aaK J (aD3 n) := by
 have hy :toSlice J (C (jU J))=aaK J (cy none) := by
   simpa only [pU,qM,one_smul,qm] using
     bO0 J (cy none) 1
 have hb:toSlice J (cy none)=aaK J (C (Qd (n:=n) none)) := by
   change _=aU (jY n) (agD J) (Qd (n:=n) none)
   rw [Algebra.algebraMap_eq_smul_one]
   simpa only [Qd,pU,C_1,p6,qm] using
     bO0 J 1 (cy none)
 rw [avS,p7,hy,hb,aD3]
 exact (p7 (ox (Gu J)) _ _).symm
private theorem gB0 (d:ℕ×ℕ) (p:UG J)
   (hp:p∈Yy J d) :toSlice J p∈box J d.1 d.2 := by
 classical
 have hp' (m:lV (Fin n) →₀ ℕ) :p.coeff m∈Oh J d:=hp m
 have hexpand:toSlice J p =
     ∑ m∈p.support,toSlice J (oj m (p.coeff m)) := by
   rw [← pz ,← as_sum]
 rw [hexpand]
 apply (box J d.1 d.2).sum_mem
 intro m _
 obtain ⟨f,hf,hf'⟩:=mem_quotientBidegreeLE.mp (hp' m)
 have hm:C (ox J f) *
     lI (aU FX (nX J)) (oj m 1) =
     oj m (p.coeff m) := by
   rw [map_monomial,pU,C_mul_monomial,qM,hf']
 rw [← hm,bO0]
 apply (box J d.1 d.2).smul_mem
 exact mem_quotientBidegreeLE.mpr ⟨_,mem_restrictBidegree.mpr fun v hv =>
   mem_restrictBidegree.mp hf v (C9 _ _ hv),rfl⟩
private theorem cFF (d:ℕ×ℕ) (P:auc n)
    (hP:P∈sH (Fin n) (jY n) d.1 d.2) (s :jY n)
    (hclear : ∀ m∈P.support,∃ r :lz n,
      aU (lz n) (jY n) r=s*P.coeff m) :
    ∃ p∈Yy J d,toSlice J p=s•aaK J P:= by
  classical
  choose! r hr using hclear
  let term (m:lV (Fin n) →₀ ℕ) :UG J :=
    C (ox J (oj m 1))*lI (aU FX (nX J)) (r m)
  refine ⟨∑ m∈P.support,term m,(Yy J d).sum_mem ?_,?_⟩
  · intro m hm
    have hmon :oj m (1 :FX)∈sH (Fin n) FX d.1 d.2 :=
      mem_restrictBidegree.mpr fun v hv=> by
        have hvm:v=m:=Finset.mem_singleton.mp (support_monomial_subset hv)
        exact hvm ▸ mem_restrictBidegree.mp hP m hm
    have hclass :ox J (oj m 1)∈Oh J d :=
      mem_quotientBidegreeLE.mpr ⟨_,hmon,rfl⟩
    intro v
    change (term m).coeff v∈Oh J d
    dsimp only [term]
    rw [coeff_C_mul,coeff_map,qx ,← Algebra.smul_def]
    exact (Oh J d).smul_mem ((r m).coeff v) hclass
  · rw [pz]
    calc
      (∑ m∈P.support,toSlice J (term m)) =
          ∑ m∈P.support,s•aaK J (oj m (P.coeff m)) := by
        apply uz rfl
        intro m hm
        dsimp only [term]
        rw [bO0,hr m hm,← smul_smul]
        congr 1
        let π:=(G9 (jY n) (Gu J)).toLinearMap
        change P.coeff m•π (lI (aU FX (jY n))
          (oj m 1))=π (oj m (P.coeff m))
        rw [← π.map_smul,map_monomial,pU,smul_monomial,smul_eq_mul,qM]
      _=s•aaK J P:= by
        rw [← wA,← pz ,← as_sum]
private theorem gBX (d e :ℕ×ℕ) (x t:agD J)
    (hx :x∈box J d.1 d.2) (ht:t∈box J e.1 e.2) :
    ∃ (s :jY n) (_:s≠0) (p q:UG J),
      p∈Yy J d∧q∈Yy J e ∧
        toSlice J p=s•x∧toSlice J q=s•t:= by
  classical
  obtain ⟨P,hP,rfl⟩:=mem_quotientBidegreeLE.mp hx
  obtain ⟨Q,hQ,rfl⟩:=mem_quotientBidegreeLE.mp ht
  let coeffs :=P.support.image P.coeff∪Q.support.image Q.coeff
  obtain ⟨b,hb⟩:=IsLocalization.exist_integer_multiples
    (zd (lz n)) coeffs id
  let s :=aU (lz n) (jY n) (b:lz n)
  have hs :s≠0:= by
    intro h
    apply mem_nonZeroDivisors_iff_ne_zero.mp b.property
    exact (wR (lz n) (jY n)) (h.trans (oK _).symm)
  have hclear (c:jY n) (hc:c∈coeffs) :
      ∃ r :lz n,aU (lz n) (jY n) r=s*c:= by
    simpa only [s,IsLocalization.IsInteger,RingHom.mem_rangeS,id_eq,Algebra.smul_def]
      using hb c hc
  obtain ⟨p,hp,hpx⟩:=cFF J d P hP s fun m hm =>
    hclear _ (Finset.mem_union_left _ (Fz _ hm))
  obtain ⟨q,hq,hqt⟩:=cFF J e Q hQ s fun m hm =>
    hclear _ (Finset.mem_union_right _ (Fz _ hm))
  exact ⟨s,hs,p,q,hp,hq,hpx,hqt⟩
theorem proof :aqf.c2 := by
 intro n J
 exact ⟨{
   toSlice :=toSlice J
   injective_toSlice :=gBZ J
   ab6:=gBY J
   map_box :=gB0 J
   clear_boxes :=gBX J
 }⟩
end
end czC
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace czy
open aiO
open scoped TensorProduct
noncomputable section
private abbrev bJY {k A:Type} [mD k] [n5 A] [c9 k A]
   (y :A) :c9 (oq k) A :=
 (oy y :oq k →ₐ[k] A).toRingHom.toAlgebra
private abbrev aV9 {k ι:Type} [mD k] (offset :ι) :
  oq k →ₐ[k] lJ ι k :=
 oy (cy offset)
private abbrev b93 {k ι:Type} [mD k] (offset :ι) :
   c9 (oq k) (lJ ι k) :=
 (aV9 offset).toRingHom.toAlgebra
private theorem c2c {k ι A:Type} [mD k] [n5 A] [c9 k A]
  (offset :ι) (y :A) (a :k) :
  No offset (nq y) (nq a) =
    nq (aU k A a) := by
 classical
 simp [No]
private theorem c2d {k ι A:Type} [mD k] [n5 A] [c9 k A]
  (offset :ι) (y :A) :
  No (k :=k) offset (nq y) (cy offset)=nq y := by
 classical
 simp [No]
private theorem c2e {k ι A:Type} [mD k] [n5 A] [c9 k A]
  (offset :ι) (y :A) (i:E8 offset) :
  No (k :=k) offset (nq y) (cy i.val)=cy i:= by
 classical
 simp [No,i.property]
private def eMX {k ι A:Type} [mD k] [n5 A] [c9 k A]
    (offset :ι) (y :A) :
    letI:=b93 (k :=k) offset
    letI:=bJY (k :=k) y
    letI:=ami (k :=k) offset (nq y)
    lJ (E8 offset) A ≃ₐ[lJ ι k] lJ ι k ⊗[oq k] A:= by
  classical
  let S:=oq k
  let T:=lJ ι k
  let U:=lJ (E8 offset) A
  letI:c9 S T:=b93 offset
  letI:c9 S A:=bJY y
  letI:c9 T U:=ami offset (nq y)
  let V:=T ⊗[S] A
  letI:c9 S U:=Algebra.restrictScalars S T U
  let:=u9 (R:=S) (S:=T) (A:=U) fun _=>rfl
  let right:A →ₐ[S] V:=Gn
  let left:T →ₐ[T] V:=Algebra.TensorProduct.includeLeft
  let eval :U →+* V :=
    MvPolynomial.eval₂Hom right.toRingHom (fun i=>left (cy i.val))
  have balance (p:S) :right (oy y p)=left (aV9 offset p) :=
    right.commutes p
  have forwardCommutes :eval.comp (No offset (nq y))=left.toRingHom:= by
    apply v8
    · intro a
      change eval (No (k :=k) offset (nq y) (nq a)) =
        left (nq a)
      rw [c2c]
      calc
        eval (nq (aU k A a))=right (aU k A a) :=
          vH _ _ _
        _=left (nq a) := by
          simpa only [xI,t7] using balance (ov a)
    · intro i
      by_cases hi:i=offset
      · subst i
        change eval (No (k :=k) offset (nq y) (cy offset)) =
          left (cy offset)
        rw [c2d]
        calc
          eval (nq y)=right y :=vH _ _ _
          _=left (cy offset) := by
            simpa only [zE,aV9] using balance pQ
      · change eval (No (k :=k) offset (nq y) (cy i)) =
          left (cy i)
        rw [c2e offset y ⟨i,hi⟩]
        exact G4 _ _ _
  let forward:U →ₐ[T] V :=
    { toRingHom:=eval
      commutes' a :=zh forwardCommutes a }
  have coordCommutes :MvPolynomial.C.comp (aU S A)=aU S U:= by
    apply C5
    · intro a
      change nq (oy y (ov a)) =
        No offset (nq y) (aV9 offset (ov a))
      rw [xI,aV9,xI,t7,
        c2c]
    · change nq (oy y pQ) =
        No offset (nq y) (aV9 offset pQ)
      rw [zE,aV9,zE,c2d]
  let coord:A →ₐ[S] U :=
    { toRingHom:=nq
      commutes' p:=zh coordCommutes p }
  let backward:V →ₐ[T] U :=
    Algebra.TensorProduct.lift (yB T U) coord (fun _ _=>qx _ _)
  have backward_left (p:T) :backward (p ⊗ₜ[S] (1 :A))=aU T U p :=
    (Cy (yB T U) coord (fun _ _=>qx _ _) p 1).trans
      (by rw [pU,qM]; rfl)
  have backward_right (a :A) :backward ((1 :T) ⊗ₜ[S] a)=nq a :=
    (Cy (yB T U) coord (fun _ _=>qx _ _) 1 a).trans
      (by rw [pU,p6]; rfl)
  refine AlgEquiv.ofAlgHom forward backward ?_ ?_
  · apply G7
    apply Algebra.TensorProduct.ringHom_ext
    · apply vi
      intro p
      change forward (backward (p ⊗ₜ[S] (1 :A)))=p ⊗ₜ[S] (1 :A)
      rw [backward_left]
      exact forward.commutes p
    · apply vi
      intro a
      change forward (backward ((1 :T) ⊗ₜ[S] a))=right a
      rw [backward_right]
      exact vH _ _ _
  · apply G7
    apply v8
    · intro a
      change backward (eval (nq a))=nq a
      rw [show eval (nq a)=right a from vH _ _ _]
      exact backward_right a
    · intro i
      change backward (eval (cy i))=cy i
      rw [show eval (cy i)=left (cy i.val) from
        G4 _ _ _]
      change backward (aU T V (cy i.val))=cy i
      rw [yo]
      exact c2e offset y i
private abbrev bte (k :Type) [mD k] :=FractionRing (oq k)
private abbrev czR {k A:Type} [mD k] [n5 A] [c9 k A] (y :A) :=
 letI:=bJY (k :=k) y
 bte k ⊗[oq k] A
private def d5u {S T U A K F:Type}
   [n5 S] [n5 T] [n5 U] [n5 A] [mD K] [mD F]
   [c9 S A] [c9 S T] [c9 T U] [c9 T F] [c9 S F]
   [c9 S K] [c9 K F] [vh S T F] [vh S K F]
   (e :U ≃ₐ[T] T ⊗[S] A) : (F ⊗[T] U) ≃ₗ[F] F ⊗[K] (K ⊗[S] A) :=
 ((Algebra.TensorProduct.congr (AlgEquiv.refl:F ≃ₐ[F] F) e).trans
   ((GR S T F F A).trans
     (GR S K F F A).symm)).toLinearEquiv
private theorem evx {K F M N :Type} [mD K] [mD F] [c9 K F]
   [vj M] [Module K M] [vj N] [Module F N]
   (e :N ≃ₗ[F] F ⊗[K] M) (d:ℕ) :JR F N d↔JR K M d:= by
 have hr :=e.finrank_eq.trans (Module.finrank_baseChange (R:=F) (S:=K) (M' := M))
 constructor
 · intro h
   let:oZ F N :=h.1
   let:oZ F (F ⊗[K] M) :=y5 e
   exact ⟨Module.Finite.of_finite_tensorProduct_of_faithfullyFlat F,hr.symm.trans_le h.2⟩
 · intro h
   let:oZ K M:=h.1
   exact ⟨y5 e.symm,hr.trans_le h.2⟩
private abbrev b94 {k ι:Type} [mD k] (offset :ι) :
   oq k →+* Jo k ι :=
 (aU (lJ ι k) (Jo k ι)).comp (aV9 offset).toRingHom
private theorem c2f {k ι:Type} [mD k] (offset :ι) :
   sS (b94 (k :=k) offset) :=
 (wR (lJ ι k) (Jo k ι)).comp
   (transcendental_iff_injective.mp (MvPolynomial.transcendental_X k offset))
private abbrev eF2 {k ι:Type} [mD k] (offset :ι) :
   c9 (bte k) (Jo k ι) :=
 (IsFractionRing.lift (K:=bte k) (g:=b94 offset)
   (c2f offset)).toAlgebra
private theorem cXl {k ι A:Type} [mD k] [n5 A] [c9 k A]
   (offset :ι) (y :A) (d:ℕ) :
   JR (Jo k ι) (Gd k offset (nq y)) d ↔
     JR (bte k) (czR (k :=k) y) d:= by
 let S:=oq k
 let T:=lJ ι k
 let F:=Jo k ι
 let K:=bte k
 let U:=lJ (E8 offset) A
 let sT:c9 S T:=b93 offset
 let sA:c9 S A:=bJY y
 let tU:c9 T U:=ami offset (nq y)
 let sF:c9 S F:=(b94 offset).toAlgebra
 let kF:c9 K F:=eF2 offset
 let towerSTF := @u9 S T F _ _ _ sT vZ sF fun _=>rfl
 let towerSKF := @u9 S K F _ _ _ vZ kF sF fun p =>
   (IsFractionRing.lift_algebraMap (K:=K) (c2f (k :=k) offset) p).symm
 let e := @d5u S T U A K F _ _ _ _ _ _ sA sT tU vZ sF
   vZ kF towerSTF towerSKF (eMX (k :=k) offset y)
 exact @evx K F (czR (k :=k) y) (Gd k offset (nq y))
   _ _ kF _ _ _ _ e d
theorem proof :aiO.c3:= by
 intro k ι ι' A _ _ _ offset offset' y d h
 exact (cXl (k :=k) offset' y d).mpr
  ((cXl (k :=k) offset y d).mp h)
end
end czy
end
section
namespace vq
noncomputable section
open K1 cu MN MvPolynomial
open scoped Polynomial BigOperators
local notation "Y" => MvPolynomial.X (R:=FX) (none :Option (Fin 2))
local notation "Pdy" => pderiv (R:=FX) (none :Option (Fin 2))
abbrev flatten (f :qU) :Ai:=(u8 FX (Fin 2)).symm f
abbrev separant (f :Ai) :Ai:=Pdy f
def zD (f P:Ai) :Ai :=
 separant f*D6 P - D6 f*Pdy P
def BA (f :Ai) :ℕ→Ai
 | 0 => -D6 f
 | n+1=>separant f*zD f (BA f n) -
     C ((2*n+1 :ℕ) :FX)*zD f (separant f)*BA f n
abbrev vf (z :K) (S:K[X]) :Ai →+* FX:=eval (Ul z S)
theorem alU (z :K) (S:K[X]) (f :qU) :
  vf z S (flatten f)=yq f z S:= by
 change eval (Ul z S) (flatten f)= _
 rw [show Ul z S=fun i=>i.elim (kr S) ![jz z,(jz z)^p] by
  funext i
  cases i <;> rfl]
 rw [optionEquivLeft_elim_eval,qy ,ze]
 rfl
theorem aNA (z :K) (S:K[X]) (f :qU) :
  vf z S (separant (flatten f))=yq f.derivative z S:= by
 have h:separant (flatten f)=flatten f.derivative := by
  apply (u8 FX (Fin 2)).injective
  rw [optionEquivLeft_pderiv_none,qy ,qy]
 rw [h,alU]
private theorem anS (m:ℕ) (a v :FX) :
   a*(a*Dx (a^m*v))-(m:FX)*(a*Dx a)*(a^m*v) =
     a^(m+2)*Dx v := by
 cases m with
 | zero=>simp [pow_two,mul_assoc]
 | succ m =>
   rw [apZ,bzc,Nat.succ_sub_one,pow_add a (m+1) 2,pow_succ' a m]
   ring
abbrev ZC (S:K[X]) (n:ℕ) :FX :=
 kr (((Polynomial.derivative (R:=K))^[n]) S)
end
end vq
end
section
namespace aZa
noncomputable section
open K1 cu DQ vq MvPolynomial
open scoped Polynomial
variable {n:ℕ}
abbrev vf (t:Fin n→L) (S:K[X]) :lz n →+* FX :=
 qz (ZS t S)
abbrev jU:lz n:=cy none
abbrev separant (P:lz n) :lz n:=pderiv none P
private theorem dmS (a :L) :Dx (aU L FX a)=0:= by
 let:CharP FX p:=charP_of_injective_ringHom jz.injective p
 obtain ⟨b,rfl⟩:=IsAlgClosed.exists_pow_nat_eq a (n:=p) (by decide)
 rw [sI,bzc,CharP.cast_eq_zero FX p,zero_mul,zero_mul]
def D6:lz n →+ lz n :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom Dx).comp AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)
theorem aG6 (P:lz n) (m:lV (Fin n) →₀ ℕ) :
 (D6 P).coeff m=Dx (P.coeff m) :=rfl
private theorem cbs (a :FX) :D6 (C a :lz n)=C (Dx a) := by
 classical
 ext m
 by_cases h: (0:lV (Fin n) →₀ ℕ)=m <;> simp [aG6,coeff_C,h]
private theorem cbt (Q:lz n) (i:lV (Fin n)) :
  D6 (Q*cy i)=D6 Q*cy i:= by
 classical
 ext m
 simp only [aG6,coeff_mul_X']
 split <;> simp
private theorem aKe (t:Fin n→L) (S:K[X]) (P:lz n) :
    Dx (vf t S P)=vf t S (D6 P) +
      kr S.derivative*vf t S (separant P) := by
  classical
  let ev :=vf t S
  change Dx (ev P)=ev (D6 P)+kr S.derivative*ev (pderiv none P)
  induction P using MvPolynomial.induction_on with
  | C a=>simp [ev,cbs]
  | add P Q hP hQ =>
    simp only [pC,hP,hQ,mul_add]
    ring
  | mul_X P i hP =>
    have hi:Dx (ZS t S i) =
        kr S.derivative*ev (pderiv none (cy i)) := by
      cases i with
      | none=>simp [ZS,ev,aYD]
      | some j=>simp [ZS,ev,pderiv_X,dmS]
    simp only [nI,apZ,hP,cbt,pderiv_mul,pC]
    rw [show ev (cy i)=ZS t S i by simp [ev],hi]
    ring
def zD (f P:lz n) :lz n :=
 separant f*D6 P - D6 f*separant P
def BA (f :lz n) :ℕ→lz n
 | 0 => -D6 f
 | i+1=>separant f*zD f (BA f i) -
     C ((2*i+1 :ℕ) :FX)*zD f (separant f)*BA f i
private theorem bpI (f P:lz n) (t:Fin n→L) (S:K[X])
  (hf :vf t S f=0) :
  vf t S (zD f P)=vf t S (separant f)*Dx (vf t S P) := by
 have h:=aKe t S f
 rw [hf,oK] at h
 rw [aKe,zD,p7,nI,nI]
 linear_combination -vf t S (separant P)*(Eq.symm h)
private theorem anS (m:ℕ) (a v :FX) :
   a*(a*Dx (a^m*v))-(m:FX)*(a*Dx a)*(a^m*v) =
     a^(m+2)*Dx v := by
 cases m with
 | zero=>simp [pow_two,mul_assoc]
 | succ m =>
   rw [apZ,bzc,Nat.succ_sub_one,pow_add a (m+1) 2,pow_succ' a m]
   ring
theorem aNv (f :lz n) (t:Fin n→L) (S:K[X])
   (hf :vf t S f=0) (i:ℕ) :
   vf t S (BA f i)=vf t S (separant f)^(2*i+1)*ZC S (i+1) := by
 induction i with
 | zero =>
   have h:=aKe t S f
   rw [hf,oK] at h
   simp only [BA,map_neg,Nat.mul_zero,uW,pow_one]
   change -vf t S (D6 f)=vf t S (separant f)*kr S.derivative
   linear_combination -(Eq.symm h)
 | succ i ih =>
   rw [BA,p7,nI,nI,nI,eval_C,bpI _ _ _ _ hf,
     bpI _ _ _ _ hf,ih,anS,
     show 2*(i+1)+1=2*i+1+2 by omega,aYD]
   congr 1
   exact oz kr (EK _ _ _).symm
end
end aZa
end
section
namespace czx
open aiO
open scoped TensorProduct nonZeroDivisors
noncomputable section
set_option backward.isDefEq.respectTransparency false
private theorem gG1 {T F P:Type} [n5 T] [th T]
    [mD F] [c9 T F] [t4 T F] [n5 P] [th P] [c9 T P]
    [oZ F (F ⊗[T] P)] (p:P) (hp:p≠0) :
    IsUnit (1 ⊗ₜ[T] p:F ⊗[T] P) := by
  let W:=F ⊗[T] P
  let:c9 P W:=Algebra.TensorProduct.rightAlgebra
  let M:=Algebra.algebraMapSubmonoid P T⁰
  let:uh M W:=IsLocalization.tensorRight F T⁰
  change IsUnit (aU P W p)
  by_cases hinj:sS (aU T P)
  · have hreg:M≤P⁰:= by
      rintro _ ⟨t,ht,rfl⟩
      exact mem_nonZeroDivisors_iff_ne_zero.mpr
        ((zR _ hinj).2 (z9 ht))
    let:th W:=IsLocalization.isDomain_of_le_nonZeroDivisors W hreg
    have hp' : aU P W p≠0 :=
      (zR _ (IsLocalization.injective W hreg)).2 hp
    exact isUnit_iff_exists_inv.mpr
      ((IsField.of_isDomain_of_finite F W).mul_inv_cancel hp')
  · rw [injective_iff_map_eq_zero] at hinj
    push Not at hinj
    obtain ⟨t,ht,hne⟩:=hinj
    have hzero : (0:P)∈M:=⟨t,mem_nonZeroDivisors_iff_ne_zero.mpr hne,ht⟩
    let:Unique W:=IsLocalization.uniqueOfZeroMem hzero
    rw [yl (aU P W p) 1]
    exact isUnit_one
private theorem gAY {T F P Q:Type} [n5 T] [th T]
    [mD F] [c9 T F] [t4 T F] [n5 P] [th P] [c9 T P]
    [n5 Q] [c9 T Q] [c9 P Q] [vh T P Q]
    (N :v9 P) [uh N Q] (hN :N≤P⁰) {d:ℕ}
    (h:JR F (F ⊗[T] P) d) :JR F (F ⊗[T] Q) d:= by
  let:oZ F (F ⊗[T] P) :=h.1
  let f : (F ⊗[T] P) →ₐ[F] (F ⊗[T] Q) :=
    zm (wB F F) (vk T P Q)
  have hf (a :F) (p:P) :f (a ⊗ₜ[T] p)=a ⊗ₜ[T] aU P Q p:=rfl
  have hright (q:Q) : (1 ⊗ₜ[T] q:F ⊗[T] Q)∈f.range := by
    obtain ⟨⟨p,m⟩,hpm⟩:=IsLocalization.surj N q
    change q*aU P Q (m:P)=aU P Q p at hpm
    obtain ⟨v,hv⟩:=isUnit_iff_exists_inv.mp
      (gG1 (T:=T) (F:=F) (m:P) (z9 (hN m.2)))
    refine ⟨(1 ⊗ₜ[T] p)*v,?_⟩
    calc
      f ((1 ⊗ₜ[T] p)*v)=(1 ⊗ₜ[T] aU P Q p)*f v := by rw [nI,hf]
      _=((1 ⊗ₜ[T] q)*f (1 ⊗ₜ[T] (m:P)))*f v := by
        rw [hf,zi ,p6,hpm]
      _=1 ⊗ₜ[T] q:= by rw [qJ,← nI,hv,pU,qM]
  have hsurj:G2 f := by
    intro z
    change z∈f.range
    induction z using TensorProduct.inductionOn with
    | tmul a q =>
      rw [← p6 q,← qM a,← zi]
      refine f.range.mul_mem ⟨a ⊗ₜ[T] 1,?_⟩ (hright q)
      change f (a ⊗ₜ[T] 1)=a ⊗ₜ[T] 1
      rw [hf,pU]
    | add a b ha hb=>exact f.range.add_mem ha hb
  exact ⟨Ea f.toLinearMap hsurj,
    (G6 (f :=f.toLinearMap) hsurj).trans h.2⟩
private theorem c2g {k ι A B:Type} [mD k] [n5 A] [n5 B]
   [c9 k A] [c9 k B] (offset :ι) (u:lJ (E8 offset) A)
   (f :A →ₐ[k] B) :
   (lI f.toRingHom).comp (No (k :=k) offset u) =
     No (k :=k) offset (lI f.toRingHom u) := by
 classical
 apply v8
 · intro a
   simp [No,RingHom.comp_apply]
 · intro i
   by_cases hi:i=offset
   · simp [No,hi]
   · simp [No,hi]
private theorem edT {k ι A B:Type} [mD k] [n5 A] [th A]
    [mD B] [c9 k A] [c9 k B] (base :A →ₐ[k] B)
    (hfrac : let _ := base.toRingHom.toAlgebra; t4 A B)
    (offset :ι) (u:lJ (E8 offset) A) {d:ℕ}
    (h:JR (Jo k ι) (Gd k offset u) d) :
    JR (Jo k ι) (Gd k offset (lI base.toRingHom u)) d:= by
  let:c9 A B:=base.toRingHom.toAlgebra
  let:t4 A B:=hfrac
  let T:=lJ ι k
  let P:=lJ (E8 offset) A
  let Q:=lJ (E8 offset) B
  let:c9 T P:=ami (k :=k) offset u
  let:c9 T Q:=ami (k :=k) offset (lI base.toRingHom u)
  let:c9 P Q:=Bf
  let:vh T P Q:=u9 fun t =>
    (t8 (c2g offset u base) t).symm
  let N :v9 P:=A⁰.map nq
  let:uh N Q:=Dw A⁰ B
  have hN :N≤P⁰:= by
    rintro _ ⟨a,ha,rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      ((zR _ (MvPolynomial.C_injective (E8 offset) A)).2
        (z9 ha))
  exact gAY N hN h
private theorem evy {F U W:Type} [mD F]
  [vj U] [vj W] [Module F U] [Module F W] {n d:ℕ}
  (e :W ≃ₗ[F] (Fin n→U)) (h:JR F U d) :JR F W (n*d) := by
 let:oZ F U:=h.1
 refine ⟨y5 e.symm,?_⟩
 rw [e.finrank_eq,Module.finrank_pi_fintype]
 simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] using
  Df n h.2
private theorem d5E {k ι B E :Type} [mD k] [mD B] [mD E]
   [c9 k B] [c9 k E] [c9 B E] [oZ B E]
   (cover :B →ₐ[k] E) (hcover : ∀ b,cover b=aU B E b)
   (offset :ι) (v :lJ (E8 offset) B) {d:ℕ}
   (h:JR (Jo k ι) (Gd k offset v) d) :
   JR (Jo k ι) (Gd k offset (lI cover.toRingHom v))
     (pG B E*d) := by
 let F:=Jo k ι
 let T:=lJ ι k
 let P:=lJ (E8 offset) B
 let Q:=lJ (E8 offset) E
 let:c9 T P:=ami (k :=k) offset v
 let:c9 T Q:=ami (k :=k) offset (lI cover.toRingHom v)
 let:c9 P Q:=Bf
 have hmap :cover.toRingHom=aU B E :=vi hcover
 let:vh T P Q:=u9 fun t=> by
   have heq :=t8 (c2g (k :=k) offset v cover) t
   change No (k :=k) offset (lI cover.toRingHom v) t =
     lI (aU B E) (No (k :=k) offset v t)
   rw [← hmap]
   exact heq.symm
 let n:=pG B E
 let e₀:Q ≃ₗ[P] (Fin n→P) :=
   (Algebra.IsPushout.equiv B P E Q).symm.toLinearEquiv.trans
     (Algebra.TensorProduct.equivPiOfFiniteBasis P (xL B E))
 let e : (F ⊗[T] Q) ≃ₗ[F] (Fin n→F ⊗[T] P) :=
   ((e₀.restrictScalars T).baseChange T F _ _).trans (TensorProduct.piRight T F F _)
 exact evy e h
theorem proof :aiO.c2 := by
 intro k ι A B E _ _ _ _ _ _ _ _ _ _ base cover hfrac hcover offset u d h
 have hb:=edT base hfrac offset u h
 have he :=d5E cover hcover offset _ hb
 rwa [C4] at he
end
end czx
end
section
namespace czr
noncomputable section
open cu Cu
open MvPolynomial
local instance gRK (C₀:sQ) :c9 L (oO C₀) :=
 (zT C₀).toAlgebra
variable (C₀:sQ)
private theorem dc8 (f :sQ) :
    aeval (Wt C₀) f =
      aU (abz C₀) (oO C₀)
        (ox (auG C₀) f) := by
  let q:sQ →ₐ[L] oO C₀ :=
    ⟨(aU (abz C₀) (oO C₀)).comp
      (ox (auG C₀)),fun _=>rfl⟩
  have hq:aeval (Wt C₀)=q :=
    MvPolynomial.algHom_ext fun i=>aeval_X (Wt C₀) i
  exact zh hq f
private theorem dc9 (f :sQ) :
  aeval (Wt C₀) f=0↔C₀∣f := by
 rw [dc8]
 rw [map_eq_zero_iff _ (wR (abz C₀) (oO C₀)),
  Ar,Ideal.mem_span_singleton]
variable [hC:Fact (Irreducible C₀)]
private theorem en3 {i j:Fin 2} (hij:i≠j) (hj:j∈C₀.vars) :
  zg L (fun _:Unit=>Wt C₀ i) := by
 classical
 refine algebraicIndependent_iff.mpr fun f hf => ?_
 let r :Unit→Fin 2 := fun _=>i
 have hz :aeval (Wt C₀) (rename r f)=0:= by
  rw [aeval_rename]
  exact hf
 obtain ⟨g,hg⟩:=(dc9 C₀ _).mp hz
 by_contra hf0
 have hr :rename r f≠0:= by
  intro h
  apply hf0
  apply rename_injective r (Function.injective_of_subsingleton _)
  simpa only [oK] using h
 have hg0:g≠0:= by
  intro h
  exact hr (by simp [hg,h])
 have hd: (rename r f).degreeOf j=0:= by
  by_contra hd
  obtain ⟨a,_,ha⟩:=mem_vars_rename r f (mem_vars_iff_degreeOf_ne_zero.mpr hd)
  exact hij ha
 rw [hg,degreeOf_mul_eq hC.out.ne_zero hg0] at hd
 exact (mem_vars_iff_degreeOf_ne_zero.mp hj) (Nat.eq_zero_of_add_eq_zero_right hd)
private theorem dsQ
   (A:Subalgebra L (oO C₀))
   (h : ∀ i,zS A (Wt C₀ i)) :
   GB A (oO C₀) := by
 have hle :Algebra.adjoin L (p9 (Wt C₀)) ≤
     (Subalgebra.algebraicClosure A (oO C₀)).restrictScalars L:= by
   refine Algebra.adjoin_le ?_
   rintro _ ⟨i,rfl⟩
   exact h i
 have him (a :abz C₀) :
     zS A (aU (abz C₀) (oO C₀) a) := by
   obtain ⟨f,rfl⟩:=Ideal.Quotient.mk_surjective (I:=auG C₀) a
   apply hle
   rw [Algebra.adjoin_range_eq_range_aeval]
   exact ⟨f,dc8 C₀ f⟩
 refine ⟨fun x => ?_⟩
 obtain ⟨r,s,_,rfl⟩:=IsFractionRing.div_surjective (abz C₀) x
 rw [div_eq_mul_inv]
 exact (him r).mul (him s).inv
theorem proof :UI.c1 := by
  classical
  intro C₀ hC
  have hvars :C₀.vars.Nonempty := by
    by_contra h
    have hconst:=vars_eq_empty_iff_eq_C.mp (Finset.not_nonempty_iff_eq_empty.mp h)
    have hcoeff :C₀.coeff 0≠0:= by
      intro he
      exact hC.out.ne_zero (by simpa only [he,oK] using hconst)
    exact hC.out.not_isUnit (hconst ▸ (isUnit_iff_ne_zero.mpr hcoeff).map nq)
  obtain ⟨j,hj⟩:=hvars
  let i:=j.succAbove (0:Fin 1)
  have hcover (k :Fin 2) :k=i∨k=j:= by
    by_cases hk :k=j
    · exact Or.inr hk
    · obtain ⟨l,rfl⟩:=Fin.exists_succAbove_eq hk
      exact Or.inl (oz j.succAbove (yl l 0))
  let x :Unit→ oO C₀:= fun _=>Wt C₀ i
  have hi:zg L x :=en3 C₀ (j.succAbove_ne 0) hj
  refine ⟨i,hi.isTranscendenceBasis_iff_isAlgebraic.mpr ?_⟩
  let A:=Algebra.adjoin L (p9 x)
  change GB A (oO C₀)
  have hjalg:zS A (Wt C₀ j) := by
    by_contra h
    have hind:=(hi.option_iff_transcendental (Wt C₀ j)).mpr h
    let e :Fin 2 ≃ lV Unit :=
      (finSuccEquiv' j).trans (Equiv.optionCongr (Equiv.ofUnique (Fin 1) Unit))
    have hindices : (fun o:lV Unit=>o.elim (Wt C₀ j) x) ∘ e =
        Wt C₀:= by
      funext k
      rcases hcover k with rfl | rfl
      · simp [e,i,x,finSuccEquiv'_succAbove]
      · simp [e,finSuccEquiv'_at]
    have hpair :zg L (Wt C₀) :=
      hindices ▸ hind.comp e e.injective
    exact hC.out.ne_zero (hpair.eq_zero_of_aeval_eq_zero C₀
      ((dc9 C₀ C₀).mpr (dvd_refl C₀)))
  apply dsQ C₀ A
  intro k
  rcases hcover k with rfl | rfl
  · exact isAlgebraic_algebraMap (⟨Wt C₀ i,Algebra.subset_adjoin ⟨(),rfl⟩⟩:A)
  · exact hjalg
end
end czr
end
section
namespace MN
noncomputable section
open Finset K1 MvPolynomial
open scoped BigOperators Polynomial
private theorem bWt {α β:Type*} (U:Finset α) (Ps :Finset β)
  (part:β→Finset α) (h : ∀ γ∈U,∃ P∈Ps,γ∈part P) :
  U.card ≤ ∑ P∈Ps,(part P).card:= by
 classical
 exact (card_le_card fun γ hγ=>mem_biUnion.mpr (h γ hγ)).trans card_biUnion_le
private theorem aM6 {k σ:Type*} [mD k] [Finite σ]
  (P:oD (lJ σ k)) (hP:P.IsPrime)
  (hdim: (vl P).natDegree=1) :
  ∃ δ:ℕ,0<δ∧affineDegree P=(δ:ℚ) := by
 let H :=vl P
 have hlin:H=ov (H.coeff 0)+Polynomial.C (H.coeff 1)*Polynomial.X:= by
  have hH :H.natDegree<2 := by change (vl P).natDegree<2; omega
  simpa [Finset.sum_range_succ] using H.as_sum_range_C_mul_X_pow' hH
 have evalH (u:ℚ) :H.eval u=H.coeff 0+H.coeff 1*u:= by
  conv_lhs=>rw [hlin]
  simp
 obtain ⟨N,hN⟩:=exists_eval_affineHilbertPolynomial P
 let m:=affineHilbertFunction P (N+1)
 let n:=affineHilbertFunction P N
 have hdiff :affineDegree P=(m:ℚ)-(n:ℚ) := by
  rw [affineDegree,hdim,Nat.factorial_one,Nat.cast_one,p6,Polynomial.leadingCoeff,hdim]
  dsimp only [m,n]
  rw [← hN (N+1) (by omega),← hN N le_rfl]
  change H.coeff 1=H.eval ((N+1 :ℕ) :ℚ) - H.eval (N :ℚ)
  rw [evalH,evalH,Nat.cast_add,Nat.cast_one]
  ring
 have hmn:n< m:= by
  have hpos :=affineDegree_pos hP.ne_top
  rw [hdiff] at hpos
  exact_mod_cast sub_pos.mp hpos
 exact ⟨m-n,Nat.sub_pos_of_lt hmn,hdiff.trans (Nat.cast_sub hmn.le).symm⟩
end
end MN
end
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace czB
noncomputable section
open cu DQ aqf MvPolynomial
variable {n:ℕ} (J:oD (lz n))
local instance :n5 (yH J) :=
 Subalgebra.toCommRing (R:=FX) (A:=AddMonoidAlgebra (nX J) (ℕ×ℕ)) (yH J)
private theorem eK9 (d:ℕ×ℕ) {x :nX J} (hx :x∈Oh J d)
  (h:x=0) :dO d x hx=0:= by
 subst x
 apply Subtype.ext
 change t9 d 0=0
 exact AddMonoidAlgebra.single_zero _
private def brN (d:ℕ×ℕ) (p:UG J) (hp:p∈Yy J d) :
  lJ (lV (Fin n)) (yH J) :=
 AddMonoidAlgebra.ofCoeff (Finsupp.onFinset p.support
  (fun m=>dO d (p.coeff m) (hp m)) fun m hm=> by
    by_contra h
    have hz :=MvPolynomial.notMem_support_iff.mp h
    exact hm (eK9 J d (hp m) hz))
private theorem bXO (d:ℕ×ℕ) (p:UG J) (hp:p∈Yy J d)
 (m:lV (Fin n) →₀ ℕ) :
 (brN J d p hp).coeff m=dO d (p.coeff m) (hp m) :=rfl
private def bev :lJ (lV (Fin n)) (yH J) :=
 C (aAI J) - C (U J)*cy none
private theorem gKK (d:ℕ×ℕ) (p:UG J)
   (hp:p∈Yy J d) (m:lV (Fin n) →₀ ℕ) :
   (yH J).val ((bev J*brN J d p hp).coeff m) =
     t9 ((1,0)+d) ((avS J*p).coeff m) := by
 classical
 have hy : (yH J).val (aAI J)=t9 (1,0) (jU J) :=rfl
 have hu: (yH J).val (U J)=t9 (1,0) 1 :=rfl
 have hc:avS J*p=C (jU J)*p-MvPolynomial.X none*p:= by
   unfold avS
   exact sub_mul (C (jU J)) (cy none) p
 rw [bev,sub_mul,qJ,hc]
 simp only [coeff_sub,coeff_C_mul,coeff_X_mul',bXO,p7,nI,biu,hy,hu]
 split_ifs <;> simp only [biu,oK,Av,
   AddMonoidAlgebra.single_sub,p6,mul_zero,sub_zero]
private theorem ey3 {R:Type*} [n5 R] (q:yH J →+* R)
    (d:ℕ×ℕ) (N :ℕ) (hN :N≤d.1) (p:UG J)
    (hp:p∈Yy J d) :
    lI q (brN J d p hp) ∈
      (t3 {C (q (aAI J)),C (q (U J))} :
        oD (lJ (lV (Fin n)) R))^N := by
  classical
  let f :yH J →+* lJ (lV (Fin n)) R:=C.comp q
  have hI: (ayB J).map f =
      (t3 {C (q (aAI J)),C (q (U J))} :
        oD (lJ (lV (Fin n)) R)) := by
    rw [ayB,Ideal.map_span,Set.image_pair,Set.pair_comm]
    rfl
  rw [← hI,← Ideal.map_pow f (ayB J) N,
    ← support_sum_monomial_coeff (lI q (brN J d p hp))]
  refine Ideal.sum_mem _ fun m _ => ?_
  rw [coeff_map,bXO,monomial_eq,qx]
  apply Ideal.mul_mem_left
  exact Ideal.mem_map_of_mem f
    (Ideal.pow_le_pow_right hN (eLe J d.1 d.2 (hp m)))
private theorem cNk (e :ℕ×ℕ) :
    ∃ N :ℕ,∀ d:ℕ×ℕ,N≤(e+d).1 →
      ∀ p∈Yy J (e+d),
        avS J*p∈Yy J ((1,0)+d) →
        p∈Yy J d:= by
  classical
  let a :yH J:=dO e 1 (bmv J e)
  let I:oD (yH J) :=t3 {a}
  let q:=ox I
  obtain ⟨N,hN⟩:=emQ (σ:=Fin n) (q (aAI J)) (q (U J))
  refine ⟨N,fun d hd p hp hpq => ?_⟩
  let r :=brN J (e+d) p hp
  have hkill:lI q (bev J*r)=0:= by
    apply MvPolynomial.eq_zero_iff.mpr
    intro m
    rw [coeff_map,Ar]
    have hm: (bev J*r).coeff m =
        a*dO ((1,0)+d) ((avS J*p).coeff m) (hpq m) := by
      apply Subtype.ext
      change (yH J).val ((bev J*r).coeff m) =
        (yH J).val (a*dO ((1,0)+d) ((avS J*p).coeff m) (hpq m))
      rw [gKK,nI,show (yH J).val a=t9 e 1
        from rfl,biu,Av,p6,add_left_comm e]
    rw [hm,qx]
    exact I.mul_mem_left _ (Ideal.subset_span (Set.mem_singleton a))
  have hz :=hN (lI q r) (ey3 J q _ N hd p hp) (by
    simpa only [bev,nI,p7,map_C,qm] using hkill)
  intro m
  have hm:=MvPolynomial.eq_zero_iff.mp hz m
  rw [coeff_map] at hm
  exact (eLf J e d (hp m)).mp
    (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [r,bXO] using hm))
theorem proof :aqf.c1 := by
 intro n J _ _
 obtain ⟨Nu,hu⟩:=cNk J (1,0)
 obtain ⟨Nv,hv⟩:=cNk J (0,1)
 refine ⟨max Nu Nv,fun u v hN _=>⟨?_,?_⟩⟩
 · have hdeg:Nu≤((1,0)+(u,v) :ℕ×ℕ).1 := by
    have h:=(le_max_left Nu Nv).trans hN
    change Nu≤1+u
    omega
   simpa only [yL,uW,p5 1 u] using hu (u,v) hdeg
 · have hdeg:Nv≤((0,1)+(u,v) :ℕ×ℕ).1 := by
    simpa only [yL,uW] using (le_max_right Nu Nv).trans hN
   simpa only [yL,uW,p5 1 u,p5 1 v] using
    hv (u,v) hdeg
end
end czB
end
section
namespace aZa
noncomputable section
open K1 cu DQ MvPolynomial
open scoped Polynomial BigOperators
variable {n:ℕ}
private abbrev incl:=aU L[X] FX
abbrev center :FX:=incl pQ
private def aaD (n:ℕ) :oq (DT n) →+* lJ (Fin n) FX :=
 Polynomial.eval₂RingHom (lI (aU L FX)) (C center)
abbrev flatten (f :XO n) :lz n :=
 (u8 FX (Fin n)).symm (f.map (aaD n))
private theorem aUo (t:Fin n→L) :
    (qz (fun j=>aU L FX (t j))).comp (aaD n) =
      incl.comp (Polynomial.mapRingHom (qz t)) := by
  apply C5
  · intro q
    change qz (fun j=>aU L FX (t j))
      ((ov q).eval₂ (lI (aU L FX)) (C center)) =
        incl ((ov q).map (qz t))
    rw [Polynomial.eval₂_C,Polynomial.map_C,MvPolynomial.eval_map]
    exact (MvPolynomial.eval₂_comp (aU L FX) t q).symm.trans
      (Dz L L[X] FX _)
  · change qz (fun j=>aU L FX (t j))
      (Polynomial.X.eval₂ (lI (aU L FX)) (C center)) =
        incl (Polynomial.X.map (qz t))
    rw [Polynomial.eval₂_X,eval_C,Polynomial.map_X]
theorem alU (t:Fin n→L) (S:K[X]) (f :XO n) :
  vf t S (flatten f)=incl ((t6 f t).eval (j9 S)) := by
 change qz (ZS t S) (flatten f)= _
 rw [show ZS t S=fun i=>i.elim (kr S) (fun j=>aU L FX (t j)) by
  funext i
  cases i <;> rfl]
 rw [optionEquivLeft_elim_eval,qy ,ze,
  Polynomial.eval₂_map,aUo,t6,ze,Polynomial.hom_eval₂]
 rfl
theorem aNA (t:Fin n→L) (S:K[X]) (f :XO n) :
   vf t S (separant (flatten f)) =
     incl ((t6 f t).derivative.eval (j9 S)) := by
 have h:separant (flatten f)=flatten f.derivative := by
   apply (u8 FX (Fin n)).injective
   rw [optionEquivLeft_pderiv_none,qy ,qy ,
     FQ]
 rw [h,alU,t6,t6,FQ]
abbrev box (n a b:ℕ) :=sH (Fin n) FX a b
private theorem bbL (P:oq (DT n))
  (hP : ∀ j,(P.coeff j).totalDegree≤1) : (aaD n P).totalDegree≤1 := by
 change (P.eval₂ (lI (aU L FX)) (C center)).totalDegree≤1
 rw [Polynomial.eval₂_eq_sum_range]
 refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
 refine (totalDegree_mul _ _).trans ?_
 rw [← sI (C:FX →+* lJ (Fin n) FX),totalDegree_C,add_zero]
 refine le_trans ?_ (hP j)
 exact Finset.sup_mono (C9 (aU L FX) (P.coeff j))
theorem Xh {f :XO n} {g:ℕ} (hf :aKg f g) :
  flatten f∈box n g 1 := by
 rw [qG]
 intro m hm
 have hc:m.some∈((f.map (aaD n)).coeff (m none)).support := by
  rw [G8] at hm ⊢
  have h:=optionEquivLeft_coeff_coeff FX (flatten f) (m none) m.some
  simp only [qy ,FV] at h
  exact h.trans_ne hm
 have hc' : (f.map (aaD n)).coeff (m none)≠0:= by
  intro h
  simp [h] at hc
 refine ⟨(Gi hc').trans (Polynomial.natDegree_map_le.trans hf.1),
  (le_totalDegree hc).trans ?_⟩
 rw [Polynomial.coeff_map]
 exact bbL _ (hf.2 (m none))
private theorem avO {P:lz n} {a b:ℕ}
  (hP:P∈box n a b) :D6 P∈box n a b:= by
 rw [qG] at hP ⊢
 intro m hm
 apply hP m
 contrapose! hm
 rw [notMem_support_iff] at hm ⊢
 rw [aG6,hm,oK]
theorem Ur {P:lz n} {a b:ℕ}
  (hP:P∈box n a b) :separant P∈box n (a-1) b:= by
 rw [Au] at hP ⊢
 exact ⟨(F9 _ _ _).trans (Ee hP.1 1),
  (weightedTotalDegree_pderiv_le _ _ _).trans hP.2⟩
private theorem aFc {f P:lz n} {g b a c:ℕ}
    (hf :f∈box n g b) (hP:P∈box n a c) (hg:0<g) :
    zD f P∈box n (a+(g-1)) (c+b) := by
  have h1 :=pL (Ur hf) (avO hP)
  unfold zD
  apply (box _ _ _).sub_mem
  · simpa only [p5] using h1
  · by_cases ha :a=0
    · have hzero :P.degreeOf none=0:= by
        apply Gj
        apply degreeOf_le_iff.mpr
        intro m hm
        simpa only [ha] using ((mem_restrictBidegree.mp hP) m hm).1
      rw [show separant P=0 from G3 hzero,mul_zero]
      exact (box _ _ _).zero_mem
    · have h2 :=pL (avO hf) (Ur hP)
      rwa [show g+(a-1)=a+(g-1) by omega,p5 b c] at h2
theorem bCJ {f :lz n} {g b:ℕ} (hg:0<g)
   (hf :f∈box n g b) (i:ℕ) :
   BA f i∈box n (1+(2*i+1)*(g-1)) ((2*i+1)*b) := by
 induction i with
 | zero =>
   have h:=(box _ _ _).neg_mem (avO hf)
   simpa only [BA,Nat.mul_zero,Nat.zero_add,Nat.one_mul,show 1+(g-1)=g by omega]
     using h
 | succ i ih =>
   have ha :=Ur hf
   have h1 :=pL ha (aFc hf ih hg)
   have h2 :=pL (aFc hf ha hg) ih
   have h2' := (box _ _ _).smul_mem (((2*i+1 :ℕ) :FX)) h2
   rw [BA]
   apply (box _ _ _).sub_mem
   · convert h1 using 2 <;> ring
   · rw [qJ,← GF]
     convert h2' using 2 <;> ring
theorem aGR {P:lz n} {a b:ℕ} (hP:P∈box n a b) (i:ℕ) :
   P^i∈box n (i*a) (i*b) := by
 induction i with
 | zero =>
   simp only [pow_zero,Nat.zero_mul,qG]
   simp [support_one]
 | succ i ih =>
   simpa only [pow_succ,Nat.succ_mul] using pL ih hP
theorem bf1 :jU (n:=n)∈box n 1 0:= by
 classical
 rw [qG,Dv]
 intro m hm
 rw [Et] at hm
 subst m
 simp
end
end aZa
end
section
namespace aqe
noncomputable section
open cu DQ ane MvPolynomial
def c1 :Prop :=
  ∀ (n:ℕ) (k :Type) [mD k] (I:oD (lJ (lV (Fin n)) k)),
    (∀ (u v :ℕ) (x :lJ (lV (Fin n)) k ⧸ I),
      x∈vG I u v ↔
        ∃ p:Dq n k,awV p (u,v)∧an3 I p=x) ∧
    (∀ (side :Bool),bkS (lW I side) ∧
      ∀ (u v :ℕ) (p:Dq n k),
        awV p ((u,v)+amR side) →
          (p∈lW I side↔an3 I p∈vG I u v))
def c2 :Prop :=
  ∀ (n:ℕ) (I:oD (Dq n FX))
    (p:Dq n (jY n)),aog n*p∈aHN I →
    ∀ i:lV (Fin n),∃ e :ℕ,cy (af6 i)^e*p∈aHN I
private theorem dVN (n:ℕ) :ew (aog n)=aD8 n:= by
 simp [aog,aD8,ew,af6,pad]
private theorem dyX (n:ℕ) :awV (aog n) (0,1) := by
 unfold aog
 apply IsWeightedHomogeneous.sub
 · apply IsWeightedHomogeneous.sum
   intro j _
   exact (zk (jY n) (ahj n) (af6 (some j))).C_mul _
 · exact (zk (jY n) (ahj n) (af6 none)).C_mul _
private theorem eJQ {n:ℕ} {k :Type} [mD k]
  {p:Dq n k} {a b:ℕ} (hp:awV p (a,b)) :
  p.IsWeightedHomogeneous (acu n) b:= by
 intro d hd
 have hweight:oY (acu n) d=(oY (ahj n) d).2 := by
  simp only [Du,Finsupp.sum,zc,Prod.smul_snd,acu]
 exact hweight.trans (oz Prod.snd (hp hd))
private theorem dzT {n:ℕ} (J:oD (lz n)) (side :Bool) :
  lW (Gu J) side=aHN (lW J side) := by
 simp only [lW,aHN,Ideal.map_sup,Ideal.map_span,Set.image_singleton,
  qm,ene J]
theorem of_children (h1 :c1) (h2 :c2) :ane.c1 := by
  intro n J _ _
  obtain ⟨hlift,hboundary⟩:=h1 n (jY n) (Gu J)
  have hlarge (side :Bool) :
      ∃ N :ℕ,∀ (v :ℕ) (p:Dq n (jY n)),N≤v →
        p.IsWeightedHomogeneous (acu n) v →
        aog n*p∈lW (Gu J) side →
        p∈lW (Gu J) side := by
    apply eul _ (aog n) (hboundary side).1
    intro p hp i
    rw [dzT J side] at hp ⊢
    exact h2 n (lW J side) p hp i
  obtain ⟨Nu,hNu⟩:=hlarge false
  obtain ⟨Nv,hNv⟩:=hlarge true
  have step (side :Bool) (u v :ℕ) (x :agD J)
      (hx :x∈box J ((u,v)+amR side).1 ((u,v)+amR side).2)
      (hqx :aaK J (aD8 n)*x∈box J u (v+1))
      (hreg : ∀ (p:Dq n (jY n)),
        p.IsWeightedHomogeneous (acu n) ((u,v)+amR side).2 →
        aog n*p∈lW (Gu J) side →
        p∈lW (Gu J) side) :
      x∈box J u v := by
    obtain ⟨p,hp,he⟩:=(hlift _ _ _).mp hx
    have hprod:awV (aog n*p) ((u,v+1)+amR side) := by
      have ht:=(dyX n).mul hp
      convert ht using 1
      cases side <;> simp [amR,p5 ,FU]
    have hq:an3 (Gu J) (aog n)=aaK J (aD8 n) := by
      change ox (Gu J) (ew (aog n))= _
      rw [dVN]
    have hmem:aog n*p∈lW (Gu J) side := by
      apply ((hboundary side).2 u (v+1) _ hprod).mpr
      simpa only [nI,hq,he] using hqx
    rw [← he]
    exact ((hboundary side).2 u v p hp).mp (hreg p (eJQ hp) hmem)
  refine ⟨max Nu Nv,?_⟩
  intro u v _ hv
  have hu' : Nu≤v :=(le_max_left _ _).trans hv
  have hv' : Nv≤v+1 :=(le_max_right _ _).trans (hv.trans (Nat.le_succ _))
  constructor
  · intro x hx hqx
    exact step false u v x hx hqx (fun p=>hNu v p hu')
  · intro x hx hqx
    exact step true u v x hx hqx (fun p=>hNv (v+1) p hv')
end
end aqe
end
section
namespace vq
noncomputable section
open cu MN MvPolynomial
local notation "Y" => MvPolynomial.X (R:=FX) (none :Option (Fin 2))
abbrev box (a b:ℕ) :=sH (Fin 2) FX a b
end
end vq
end
section
namespace czA
noncomputable section
open cu DQ aqe MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial Polynomial.algebra
private theorem exd {R:Type*} [n5 R] (a b:R) (q:oq R)
    (h: (ov a*pQ+Polynomial.C b)*q=0) :
    ∃ e :ℕ,ov a^e*q=0:= by
  let S:=Localization.Away a
  let M:v9 (oq R) :=(yQ a).map ov
  let:uh M (oq S) :=Polynomial.isLocalization _ _
  let f :=aU (oq R) (oq S)
  have hz :f q=0:= by
    change x7 (aU R S) q=0
    rcases subsingleton_or_nontrivial S with hS | hS
    · let:=hS
      exact yl _ _
    · let:=hS
      have hu:IsUnit (aU R S a) :=
        IsLocalization.map_units S (⟨a,Submonoid.mem_powers a⟩:yQ a)
      have hu' : IsUnit
          (ov (aU R S a)*pQ +
            ov (aU R S b)).leadingCoeff := by
        rwa [Polynomial.leadingCoeff_linear hu.ne_zero]
      apply (Polynomial.isUnit_leadingCoeff_mul_right_eq_zero_iff hu').mp
      have hm:=oz f h
      change x7 (aU R S) _=x7 (aU R S) 0 at hm
      simpa only [Polynomial.map_mul,Polynomial.map_add,Polynomial.map_C,Polynomial.map_X,
        Polynomial.map_zero] using hm
  obtain ⟨m,hm⟩:=(IsLocalization.map_eq_zero_iff M (oq S) q).mp hz
  have hmem:=m.property
  change (m:oq R)∈(yQ a).map ov at hmem
  rw [Submonoid.map_powers] at hmem
  obtain ⟨e,he⟩:=hmem
  change ov a^e=(m:oq R) at he
  exact ⟨e,by simpa only [he] using hm⟩
private theorem bHq {R σ:Type*} [n5 R] [Fintype σ]
    (a :σ→R) (q:lJ σ R)
    (h: (∑ j,C (a j)*cy j)*q=0) (i:σ) :
    ∃ e :ℕ,C (a i)^e*q=0:= by
  classical
  let E :=(renameEquiv R (Equiv.optionSubtypeNe i).symm).trans
    (u8 R {j:σ // j≠i})
  have hC (r :R) :E (C r)=ov (C r) := by
    simp [E,z8]
  have hi:E (cy i)=Polynomial.X:= by
    simp [E,z8]
  let s :Finset σ:=Finset.univ.erase i
  let b:lJ {j:σ // j≠i} R :=
    ∑ j∈s.attach,C (a j.val)*cy ⟨j.val,(Finset.mem_erase.mp j.property).1⟩
  have hb:E (∑ j∈s,C (a j)*cy j)=ov b:= by
    rw [← Finset.sum_attach s]
    simp only [b,pz ,nI,hC]
    apply uz rfl
    intro j _
    rw [show E (cy (j:σ))=ov (cy ⟨j.val,
      (Finset.mem_erase.mp j.property).1⟩) by
      simp [E,z8 ,
        Equiv.optionSubtypeNe_symm_of_ne (Finset.mem_erase.mp j.property).1]]
  have hg:E (∑ j,C (a j)*cy j) =
      ov (C (a i))*pQ+Polynomial.C b:= by
    rw [← Finset.sum_erase_add _ _ (yU i),pC,nI,hi,hC,hb,add_comm]
  have hz : (ov (C (a i))*pQ+Polynomial.C b)*E q=0:= by
    simpa only [nI,oK,hg] using oz E h
  obtain ⟨e,he⟩:=exd (C (a i)) b (E q) hz
  refine ⟨e,E.injective ?_⟩
  simpa only [nI,sI,oK,hC] using he
private def aws (n:ℕ) :lV (Fin n)→Dq n FX
 | none => -MvPolynomial.X (af6 none)
 | some i=>MvPolynomial.X (af6 (some i))
theorem proof :aqe.c2 := by
  classical
  intro n I p hp i
  let A:=Dq n FX
  let R:=lz n
  let B:=Dq n R
  let L:=Dq n (jY n)
  let M:v9 B:=(zd R).map C
  let:uh M L:=Dw _ _
  let j:A →+* B:=lI (C:FX →+* R)
  let J:oD B:=I.map j
  let g:B := ∑ k,j (aws n k)*C (cy k :R)
  let E :=(t5 FX (aex n) (lV (Fin n))).toRingHom
  have hE :E.comp j=C:= by
    apply v8
    · intro r
      change t5 FX (aex n) (lV (Fin n)) (lI C (C r))=C (C r)
      rw [map_C,commAlgEquiv_C,map_C]
    · intro k
      change t5 FX (aex n) (lV (Fin n)) (lI C (cy k)) =
        C (cy k)
      rw [qm,commAlgEquiv_X]
  let Q:B →+* lJ (lV (Fin n)) (A ⧸ I) :=
    (lI (ox I)).comp E
  have hQ:RingHom.ker Q=J:= by
    change (RingHom.ker (lI (ox I))).comap E=J
    rw [MvPolynomial.ker_map,Ideal.mk_ker,← hE,← wY]
    exact Ideal.comap_map_of_bijective E (t5 FX (aex n) (lV (Fin n))).bijective
  have hQj (x :A) :Q (j x)=C (ox I x) := by
    have hx :=t8 hE x
    change E (j x)=C x at hx
    simp [Q,hx]
  have hQX (k :lV (Fin n)) :Q (C (cy k :R))=cy k := by
    change lI (ox I)
      (t5 FX (aex n) (lV (Fin n)) (C (cy k)))=cy k
    rw [commAlgEquiv_C_X,qm]
  have hQg:Q g = ∑ k,C (ox I (aws n k))*cy k := by
    simp only [g,pz ,nI,hQj,hQX]
  have hj: (aU B L).comp j=lI (aU FX (jY n)) := by
    apply vi
    intro x
    change lI (aU R (jY n)) (lI C x)= _
    rw [C4] <;> rfl
  have hJ:J.map (aU B L)=aHN I:= by
    change (I.map j).map (aU B L)=aHN I
    rw [wY ,hj,aHN]
  have hg:aU B L g=aog n:= by
    have hj' (x :A) :aU B L (j x)=lI (aU FX (jY n)) x :=
      t8 hj x
    have hCX (k :lV (Fin n)) :
        aU B L (C (cy k :R))=C (Qd k) := by
      change lI (aU R (jY n)) (C (cy k))= _
      rw [map_C] <;> rfl
    have hterm (k :lV (Fin n)) :
        aU B L (j (aws n k)*C (cy k :R)) =
          C (Qd k)*lI (aU FX (jY n))
            (aws n k) := by
      rw [nI,hj',hCX,qx]
    calc
      aU B L g = ∑ k,C (Qd k) *
          lI (aU FX (jY n)) (aws n k) := by
        simp only [g,pz ,hterm]
      _=aog n:= by
        rw [z7]
        simp only [aws,qm,map_neg,aog,sub_eq_add_neg]
        rw [add_comm]
        exact oz (fun z :L =>
          (∑ k :Fin n,C (Qd (some k))*cy (af6 (some k)))+z)
          (mul_neg (C (Qd (n:=n) none) :L) (cy (af6 none)))
  obtain ⟨q,s,rfl⟩:=IsLocalization.exists_mk'_eq M p
  rw [← hg,← hJ,FK,
    Fa] at hp
  obtain ⟨d,hd,hmem⟩:=hp
  have hz :Q g*Q (d*q)=0:= by
    rw [← nI,← RingHom.mem_ker,hQ,← mul_left_comm]
    exact hmem
  rw [hQg] at hz
  obtain ⟨e,he⟩:=bHq (fun k=>ox I (aws n k))
    (Q (d*q)) hz i
  have ht:d*(j (aws n i)^e*q)∈J:= by
    rw [← hQ,RingHom.mem_ker,mul_left_comm,nI,sI,hQj]
    exact he
  have hpow:aU B L (j (aws n i))^e* IsLocalization.mk' L q s ∈
      aHN I:= by
    rw [← hJ,← sI,FK,
      Fa]
    exact ⟨d,hd,ht⟩
  refine ⟨e,?_⟩
  have hji:aU B L (j (aws n i)) =
      lI (aU FX (jY n)) (aws n i) :=
    t8 hj _
  rw [hji] at hpow
  cases i with
  | some k=>simpa [aws] using hpow
  | none =>
    simp only [aws,map_neg,qm,← neg_one_mul (cy (af6 none) :L),
      mul_pow,qJ] at hpow
    exact ((aHN I).unit_mul_mem_iff_mem (isUnit_one.neg.pow e)).mp hpow
end
end czA
end
section
namespace czz
noncomputable section
open aqe MvPolynomial
private def tag : (ℕ×ℕ) →+ (Bool →₀ ℕ) where
 toFun d:=zf false d.1+Finsupp.single true d.2
 map_zero' := by simp
 map_add' d e := by
  ext i
  cases i <;> simp
@[simp] private theorem gyR (d:ℕ×ℕ) :tag d false=d.1 := by
  simp [tag]
@[simp] private theorem gyV (d:ℕ×ℕ) :tag d true=d.2 := by
  simp [tag]
private theorem tag_injective :sS tag := by
 intro d e h
 exact Prod.ext (by simpa using DFunLike.congr_fun h false)
  (by simpa using zh  h true)
private theorem dgz (side :Bool) :tag (amR side)=zf side 1 := by
 ext i
 cases side <;> cases i <;> simp [amR]
private theorem gyU (m:Bool →₀ ℕ) :tag (m false,m true)=m:= by
 ext i
 cases i <;> simp
variable {n:ℕ} {k :Type} [mD k]
private theorem dlT (e :lV (Fin n) →₀ ℕ) (t:Bool →₀ ℕ) :
   oY (ahj n) (e.sumElim t)=(e none+t false,e.some.degree+t true) := by
 apply Prod.ext
 · simp [Aa ,Prod.fst_sum,Gk,
    z7,Ef ,ahj,group,amR]
 · simp [Aa ,zc,Gk,
    z7,Ef ,ahj,group,amR,Finsupp.degree_eq_sum,
    Finsupp.some_apply]
private theorem cKe (e :lV (Fin n) →₀ ℕ) (t:Bool →₀ ℕ) (c:k) :
  ew (oj (e.sumElim t) c)=oj e c:= by
 rw [ew,aeval_monomial,Finsupp.prod_sumElim,t7,monomial_eq]
 simp [Finsupp.prod]
private theorem dVQ {p:Dq n k} {u v :ℕ}
  (h:awV p (u,v)) :
  ew p∈sH (Fin n) k u v := by
 rw [p.as_sum,pz]
 apply GY
 intro d hd
 have hw:=h (mem_support_iff.mp hd)
 rw [← G0 d,dlT] at hw
 rw [← G0 d,cKe]
 apply mem_restrictBidegree.mpr
 intro m hm
 have he :=Finset.mem_singleton.mp (support_monomial_subset hm)
 subst m
 have hu:=oz Prod.fst hw
 have hv :=oz Prod.snd hw
 exact ⟨(Nat.le_add_right _ _).trans_eq hu,(Nat.le_add_right _ _).trans_eq hv⟩
private theorem enn (p:lJ (lV (Fin n)) k) (u v :ℕ)
   (h:p∈sH (Fin n) k u v) :
   ∃ q:Dq n k,awV q (u,v)∧ew q=p:= by
 classical
 let lift (e :lV (Fin n) →₀ ℕ) :Dq n k :=
   oj (e.sumElim (tag (u-e none,v-e.some.degree))) (p.coeff e)
 refine ⟨∑ e∈p.support,lift e,?_,?_⟩
 · apply IsWeightedHomogeneous.sum
   intro e he
   obtain ⟨hu,hv⟩:=mem_restrictBidegree.mp h e he
   apply isWeightedHomogeneous_monomial
   rw [dlT,gyR,gyV,G1 hu,G1 hv]
 · rw [pz]
   conv_rhs=>rw [p.as_sum]
   exact uz rfl fun e _=>cKe _ _ _
variable (I:oD (lJ (lV (Fin n)) k))
private theorem cXM (u v :ℕ) (x :lJ (lV (Fin n)) k ⧸ I) :
   x∈vG I u v ↔
     ∃ p:Dq n k,awV p (u,v)∧an3 I p=x := by
 rw [mem_quotientBidegreeLE]
 constructor
 · rintro ⟨p,hp,rfl⟩
   obtain ⟨q,hq,he⟩:=enn p u v hp
   exact ⟨q,hq,by simp [an3,he]⟩
 · rintro ⟨p,hp,rfl⟩
   exact ⟨ew p,dVQ hp,rfl⟩
@[simp] private theorem dVJ (side :Bool) :
   an3 I (cy (pad side))=1 := by
  simp [an3,ew,pad]
private theorem cT4 (i:aex n) :
  acf I (cy i)=C (an3 I (cy i))*cy (group i) := by
 simp [acf]
@[simp] private theorem eiS (side :Bool) :
   acf I (cy (pad side))=cy side := by
  rw [cT4,dVJ,pU,p6]
  rfl
private theorem b5y (d:aex n →₀ ℕ) (c:k) :
    acf I (oj d c) =
      oj (tag (oY (ahj n) d)) (an3 I (oj d c)) := by
  classical
  induction d using Finsupp.induction with
  | zero =>
      simp only [oK,monomial_zero']
      rw [← t7,yo ,yo ,
        Dz k (lJ (lV (Fin n)) k ⧸ I),
        t7]
  | single_add i e d _ _ ih =>
      rw [add_comm (zf i e) d]
      simp only [xu,nI,sI,pC,Finsupp.weight_single,ih]
      rw [cT4,C_mul_X_eq_monomial,monomial_pow,monomial_mul_monomial,
        map_nsmul tag,show ahj n i=amR (group i) from rfl,dgz]
private theorem bHw {d:ℕ×ℕ} {p:Dq n k}
  (hp:awV p d) :
  acf I p=oj (tag d) (an3 I p) := by
 conv_lhs=>rw [p.as_sum,pz]
 conv_rhs=>rw [p.as_sum,pz ,pz]
 exact uz rfl fun e he=> by
  rw [b5y,hp (mem_support_iff.mp he)]
private theorem cHv {D:Type} [AddCommMonoid D] [DecidableEq D]
   (w:aex n→D) (s :D) (d:aex n →₀ ℕ) (c:k) :
   uJ w s (oj d c) =
     if oY w d=s then oj d c else 0:= by
 classical
 ext e
 by_cases h:d=e
 · subst e
   by_cases hw:oY w d=s <;>
     simp [Eg ,hw]
 · by_cases hw:oY w d=s <;>
     simp [Eg ,h,hw]
private theorem cGb {D:Type} [AddCommMonoid D] [DecidableEq D]
    (w:aex n→D) (f :ℕ×ℕ→D)
    (hf : ∀ d:aex n →₀ ℕ,oY w d=f (oY (ahj n) d))
    (s :D) (p:Dq n k) (b:ℕ×ℕ) :
    (acf I (uJ w s p)).coeff (tag b) =
      if f b=s then (acf I p).coeff (tag b) else 0:= by
  classical
  induction p using EP with
  | monomial d c =>
      rw [cHv,hf]
      by_cases h:oY (ahj n) d=b
      · rw [h]
        split <;> simp [b5y, *]
      · have ht:tag (oY (ahj n) d)≠tag b:= fun ht =>
          h (tag_injective ht)
        split <;> simp [b5y,ht]
  | add a b ha hb =>
      simp only [pC,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,ha,hb]
      split <;> simp
private theorem eng:bkS (aze I) := by
 intro p hp v
 change acf I p=0 at hp
 change acf I (uJ (acu n) v p)=0
 have hw (d:aex n →₀ ℕ) :
     oY (acu n) d=(oY (ahj n) d).2 := by
   simp only [Du,Finsupp.sum,zc,Prod.smul_snd,acu]
 ext m
 rw [← gyU m,cGb I (acu n) Prod.snd hw,hp]
 simp
private theorem gtE (side :Bool) (a :Dq n k) (v :ℕ) :
    uJ (acu n) v (a*cy (pad side)) ∈
      t3 ({cy (pad side)} : Set (Dq n k)) := by
  classical
  induction a using EP with
  | monomial d c =>
      rw [show oj d c*cy (pad side) =
          oj (d+Finsupp.single (pad side) 1) c by rw [xu,pow_one],
        cHv]
      split
      · rw [xu,pow_one]
        exact Ideal.mem_span_singleton'.mpr ⟨oj d c,rfl⟩
      · exact (t3 _).zero_mem
  | add a b ha hb =>
      rw [add_mul,pC]
      exact (t3 _).add_mem ha hb
private theorem dz0 (side :Bool) :bkS (lW I side) := by
 intro p hp v
 rw [lW,sup_comm,Gr] at hp
 obtain ⟨a,b,hb,rfl⟩:=hp
 rw [pC]
 exact (lW I side).add_mem (Ideal.mem_sup_right (gtE side a v))
  (Ideal.mem_sup_left (eng I b hb v))
private theorem dzV (side :Bool) (u v :ℕ) (p:Dq n k)
    (hp:awV p ((u,v)+amR side)) :
    p∈lW I side↔an3 I p∈vG I u v := by
  classical
  rw [cXM,lW,sup_comm,Gr]
  constructor
  · rintro ⟨a,b,hb,he⟩
    change acf I b=0 at hb
    have heval :acf I a*cy side=acf I p:= by
      simpa only [pC,nI,eiS,hb,add_zero] using oz (acf I) he
    let q:=uJ (ahj n) (u,v) a
    have hq:awV q (u,v) :=
      weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have hc: (acf I a).coeff (tag (u,v))=an3 I p:= by
      have h:=oz (fun f :lJ Bool (lJ (lV (Fin n)) k ⧸ I) =>
        f.coeff (tag ((u,v)+amR side))) heval
      rw [bHw I hp] at h
      simpa only [pC,dgz,coeff_mul_X,coeff_monomial,ite_true] using h
    refine ⟨q,hq,?_⟩
    have h:=cGb I (ahj n) id (fun _=>rfl) (u,v) a (u,v)
    simp only [id_eq,ite_true] at h
    change (acf I q).coeff (tag (u,v))= _ at h
    simpa only [bHw I hq,coeff_monomial,ite_true,hc] using h
  · rintro ⟨q,hq,he⟩
    have hmul :awV (q*cy (pad side)) ((u,v)+amR side) :=
      hq.mul (zk k (ahj n) (pad side))
    refine ⟨q,p - q*cy (pad side),?_,by ring⟩
    change acf I (p - q*cy (pad side))=0
    rw [p7,bHw I hp,bHw I hmul]
    simp [he]
theorem proof :aqe.c1 := by
 intro n k _ I
 exact ⟨cXM I,fun side=>⟨dz0 I side,dzV I side⟩⟩
end
end czz
end
section
namespace baF
noncomputable section
open K1 cu MN MvPolynomial
open scoped Polynomial
private abbrev ι:FX →+* BK:=aU FX BK
private def closedPoint (z :K) (S:K[X]) :lV (Fin 2)→BK :=
 ι ∘ Ul z S
end
end baF
end
section
namespace aR1
open DQ Cu akS
open scoped Polynomial
theorem proof :akS.c2 := by
 intro n H B _ hH W hW
 let:c9 (e7 n)[X] (Mb B) :=bgf (aoe B)
 let:c9 (e7 n)[X] (jY n) :=ami n
 let:=eF7 n
 let:=hH.finite
 let:=hW
 let f :=(a8l B).toLinearMap
 have hf :G2 f :=gnB B
 have hfinite :oZ (jY n) (axw B) :=Ea f hf
 have hlen:pG (jY n) (axw B)≤H :=
  (G6 hf).trans hH.length
 obtain ⟨C,hC⟩:=ekM (aoe B) W (jY n) hfinite
 exact ⟨C,fun k=>(hC k).trans (Nat.add_le_add_left (Df k hlen) C)⟩
end aR1
end
