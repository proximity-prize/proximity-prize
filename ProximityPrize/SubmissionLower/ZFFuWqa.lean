import ProximityPrize.SubmissionLower.ZgdIx1d
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
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open _root_ renaming AddMonoidAlgebra→yB,AddMonoidAlgebra.coeff_single→xI,AddMonoidAlgebra.single→ oq,AddMonoidAlgebra.single_mul_single→Bf,AdjoinRoot.of→vj,Algebra→nq,Algebra.IsAlgebraic→EP,Algebra.TensorProduct.includeRight→wA,Algebra.TensorProduct.tmul_mul_tmul→FQ,Algebra.TensorProduct.tmul_one_eq_one_tmul→zg,Algebra.algebraMap→aU,Algebra.toModule→zm,CommRing→ ox,DFunLike.congr_fun→qz,DQ.SourceRing→ oZ,Field→lV,Fin.castLE→p9,Finset.mem_univ→sI,Finset.sum_coe_sort→Dz,Finsupp.degree_apply→FV,Finsupp.single_apply→zR,Fintype.sum_prod_type→z7,FractionRing→uz,FractionRing.algEquiv→Gi,Function.Injective→p6,Ideal→lI,Ideal.Quotient.lift→Ee,Ideal.Quotient.liftₐ→Et,Ideal.Quotient.mk→lz,Ideal.Quotient.mk_surjective→FK,Ideal.mul_mem_left→C4,Ideal.pow_mem_pow→Av,Ideal.span→p7,Ideal.subset_span→vw,Irreducible→qM,IsFractionRing.injective→t5,IsFractionRing.lift→Df,IsFractionRing.lift_algebraMap→t3,IsFractionRing.map→t9,IsFractionRing.ringHom_ext→xW,IsLocalRing.ResidueField→zE,IsLocalRing.residue→nX,IsLocalRing.residue_ne_zero_iff_isUnit→yU,IsLocalization.Away.algebraMap_isUnit→Cy,IsLocalization.map_eq→uW,IsNoetherianRing→yQ,IsScalarTower.algebraMap_apply→qm,IsTranscendenceBasis→v9
open _root_ renaming LinearIndependent→xL,LinearMap.ker→vk,LinearMap.mulLeft→pz,LinearMap.pow_mulLeft→Gj,Module.Finite→qU,Module.finrank→u9,MvPolynomial→mD,MvPolynomial.C→c9,MvPolynomial.X→cy,MvPolynomial.aeval→t8,MvPolynomial.aeval_C→zk,MvPolynomial.aeval_X→uJ,MvPolynomial.affineHilbertPolynomial→vH,MvPolynomial.algHom_C→zh,MvPolynomial.algHom_ext→FU,MvPolynomial.eval→pL,MvPolynomial.eval_X→zf,MvPolynomial.eval₂Hom→pG,MvPolynomial.eval₂Hom_C→v8,MvPolynomial.eval₂Hom_X'→xm,MvPolynomial.map→n5,MvPolynomial.map_C→wR,MvPolynomial.map_X→vi,MvPolynomial.map_eval₂Hom→Fa,MvPolynomial.optionEquivLeft→qJ,MvPolynomial.rename→qx,MvPolynomial.ringHom_ext→ oK,MvPolynomial.zeroLocus→sH,Nat.add_le_add_left→x7,Nat.le_add_right→vl,Nat.le_mul_of_pos_left→C9,Nat.le_of_not_gt→u8,Nat.mul_le_mul_right→F9,Nat.mul_succ→yL,Nat.sub_add_cancel→z8,Option→lJ,Polynomial→zc,Polynomial.C→ ov,Polynomial.X→pC,Polynomial.aeval→vG,Polynomial.coe_eval₂RingHom→yl,Polynomial.coe_mapRingHom→Dv,Polynomial.coeff_C_mul→Fz,Polynomial.coeff_eq_zero_of_natDegree_lt→Ef,Polynomial.coeff_monomial_of_ne→EK,Polynomial.coeff_zero→ze,Polynomial.eval₂RingHom→wY,Polynomial.eval₂_C→Du
open _root_ renaming Polynomial.eval₂_X→C5,Polynomial.ext→zi,Polynomial.hom_eval₂→th,Polynomial.mapRingHom→wB,Polynomial.map_C→zS,Polynomial.map_map→FR,Polynomial.ringHom_ext→yo,RatFunc→ oy,RingHom.comp_apply→nI,RingHom.congr_fun→y5,RingHom.ext→t6,RingHom.id→z9,RingHom.ker→pQ,Semiring→t7,Set.mem_singleton→Eg,Submodule→pU,Submodule.map_comp→Ar,Submodule.mem_bot→Dw,Subtype.ext→sS,Subtype.val→Aa,Subtype.val_injective→xu,TensorProduct.inductionOn→Au,TrivSqZeroExt.ext→vZ,Valuation.pos_iff→Ea,ValuationSubring→yJ,congrArg→ oD,dite_eq_left→uh,finProdFinEquiv→zd,map_add→t4,map_mul→ oj,map_pow→u5,map_sub→qG,map_sum→qy,map_zero→ oY,mul_assoc→vh,mul_comm→ oz,one_mul→p5
set_option autoImplicit true
section
open private Cu.pD from ProximityPrize.SubmissionLower.ZgdIx1d
namespace akS
noncomputable section
open K1 cu Cu MvPolynomial
open scoped TensorProduct
private theorem interpolate {F A ι:Type} [lV F] [ox A] [nq F A]
    [Fintype ι] [DecidableEq ι] (f :ι→A →ₐ[F] F) (hf :p6 f) :
    ∃ r :ι→A,∀ i j,f j (r i)=if i=j then 1 else 0:= by
  classical
  have hsep (i j:ι) : ∃ x :A,f i x=1∧(i≠j→f j x=0) := by
    by_cases h:i=j
    · exact ⟨1,map_one _,fun hn=>(hn h).elim⟩
    · have hd : ∃ y :A,f i y≠f j y := by
        by_contra! hn
        exact h (hf (AlgHom.ext hn))
      obtain ⟨y,hy⟩:=hd
      let d:=f i y - f j y
      have hd₀:d≠0:=sub_ne_zero.mpr hy
      refine ⟨aU F A d⁻¹*(y-algebraMap F A (f j y)),?_,?_⟩
      · simpa only [oj,qG,AlgHom.commutes,Algebra.algebraMap_self_apply] using
          inv_mul_cancel₀ hd₀
      · intro _
        simp
  choose s hs using hsep
  refine ⟨fun i => ∏ k∈Finset.univ.erase i,s i k,?_⟩
  intro i j
  rw [map_prod]
  split_ifs with hij
  · subst j
    exact Finset.prod_eq_one fun k _=>(hs i k).1
  · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hij,sI j⟩)
      ((hs i j).2 hij)
private theorem bHQ {F A ι:Type} [lV F] [ox A] [nq F A]
    [IsDomain A] [Fintype ι] [DecidableEq ι] (f :ι→A →ₐ[F] F) (r :ι→A)
    (hr : ∀ i j,f j (r i)=if i=j then 1 else 0)
    (a :A) (ha :a≠0) (hf : ∀ i,f i a=0) (k :ℕ) :
    xL F (fun ij:Fin (k+1)×ι=>a^(ij.1 :ℕ)*r ij.2) := by
  induction k with
  | zero =>
    refine Fintype.linearIndependent_iff.mpr fun c hc ⟨i,j⟩ => ?_
    have hi:i=0:=Fin.eq_zero _
    subst i
    have hh:=oD (f j) hc
    simpa [z7,hr,eq_comm] using hh
  | succ k ih =>
    refine Fintype.linearIndependent_iff.mpr fun c hc ⟨i,j⟩ => ?_
    have hsplit :
        (∑ u:ι,c (0,u)•r u) +
            a*(∑ ij:Fin (k+1)×ι,c (ij.1.succ,ij.2)•(a^(ij.1 :ℕ)*r ij.2))=0:= by
      rw [z7,Fin.sum_univ_succ] at hc
      simpa only [z7,Fin.val_zero,Fin.val_succ,pow_zero,p5 ,
        pow_succ',Finset.mul_sum,mul_smul_comm,vh] using hc
    have hc₀ (u:ι) :c (0,u)=0:= by
      have hh:=oD (f u) hsplit
      simpa [hf,hr,eq_comm] using hh
    have htail: (∑ ij:Fin (k+1)×ι,
        c (ij.1.succ,ij.2)•(a^(ij.1 :ℕ)*r ij.2))=0:= by
      have hz :=hsplit
      simp only [hc₀,zero_smul,Finset.sum_const_zero,zero_add] at hz
      exact (mul_eq_zero.mp hz).resolve_left ha
    refine Fin.cases (hc₀ j) (fun i => ?_) i
    exact Fintype.linearIndependent_iff.mp ih (fun ij=>c (ij.1.succ,ij.2)) htail (i,j)
theorem d4l {n:ℕ} (B:lI (Gc n)) [B.IsPrime]
    (q:N4 n) (hq:aa4 n q∉B)
    (V:Finset K) (pt:K→Fin 2 ⊕ Fin n→FX) (hinj:Set.InjOn pt (V:Set K))
    (hpt : ∀ γ∈V,pt γ∈sH FX B∧t8 (pt γ) (aa4 n q)=0) :
    ∃ r : (↥V)→tu B,∀ k,
      xL (e7 n) (fun ij:Fin (k+1)×(↥V) =>
        ajy B ((lz B (aa4 n q))^(ij.1 :ℕ)*r ij.2)) := by
  classical
  let pts : (↥V)→sH FX B:= fun i=>⟨pt i.1,(hpt i.1 i.2).1⟩
  let e :=zeroLocusPointHom B ∘ pts
  have he :p6 e :=(zeroLocusPointHom_injective B).comp (fun i j h =>
    sS (hinj i.2 j.2 (oD Aa h)))
  obtain ⟨r,hr⟩:=interpolate e he
  refine ⟨r,fun k => ?_⟩
  let a :=lz B (aa4 n q)
  have ha :a≠0:=mt Ideal.Quotient.eq_zero_iff_mem.mp hq
  have hz (i: (↥V)) :e i a=0:=(hpt i.1 i.2).2
  exact Module.Flat.linearIndependent_one_tmul (S:=e7 n)
    (bHQ e r hr a ha hz k)
theorem c3x {n:ℕ} (B:lI (Gc n)) (q:N4 n) :
    pD B (n5 (aU FX (e7 n)) q) =
      ajy B (lz B (aa4 n q)) := by
  let f :N4 n →+* Mb B :=
    (pD B).toRingHom.comp (n5 (aU FX (e7 n)))
  let g:N4 n →+* Mb B :=
    (ajy B).toRingHom.comp ((lz B).comp (aa4 n))
  have h:f=g:= by
    apply oK
    · intro x
      change pD B (n5 (aU FX (e7 n)) (c9 x)) =
        ajy B (lz B (qx Sum.inr (c9 x)))
      rw [wR,MvPolynomial.rename_C,pD,zk]
      change aU (e7 n) (Mb B) (aU FX (e7 n) x) =
        ajy B (aU FX (tu B) x)
      rw [AlgHom.commutes]
      rfl
    · intro i
      change pD B (n5 (aU FX (e7 n))
        (cy i)) =
        ajy B (lz B (qx Sum.inr (cy i)))
      rw [vi ,MvPolynomial.rename_X,pD,uJ]
  exact qz h q
theorem eJS {n d:ℕ} (B:lI (Gc n)) (q:N4 n)
  (h:q.totalDegree≤d) :
  ajy B (lz B (aa4 n q))∈aIU B d:= by
 refine ⟨n5 (aU FX (e7 n)) q,?_,c3x B q⟩
 exact (mem_restrictTotalDegree _ _ _).2 (le_trans (by
  rw [totalDegree_eq,totalDegree_eq]
  exact Finset.sup_mono (support_map_subset _ _)) h)
theorem ey8 {F A:Type} [lV F] [ox A] [nq F A]
    (a b:A) {W U:pU F A} (h:W.map (pz F b)≤U) (k :ℕ) :
    (abb a W k).map (pz F b)≤abb a U k := by
  induction k with
  | zero=>exact h
  | succ k ih =>
    change (W ⊔ (abb a W k).map (pz F a)).map (pz F b) ≤
      U ⊔ (abb a U k).map (pz F a)
    rw [Submodule.map_sup,← Ar]
    refine sup_le (h.trans le_sup_left) ?_
    rw [show (pz F b).comp (pz F a) =
        (pz F a).comp (pz F b) by
      ext y
      exact mul_left_comm b a y,Ar]
    exact (Submodule.map_mono ih).trans le_sup_right
end
end akS
end
section
namespace bz1
noncomputable section
open aiN
open scoped Polynomial RatFunc
attribute [local instance] Polynomial.algebra
theorem b8y {E F:Type} [lV E] [lV F]
  (f :E →+* F) (p:E[X]) :
  ZR f (aU E[X] (Jv E) p) =
    aU F[X] (Jv F) (p.map f) :=
 by
  unfold ZR t9
  rw [uW]
  rfl
theorem eyS {E F G:Type} [lV E] [lV F] [lV G]
  (f :E →+* F) (h:F →+* G) :
  (ZR h).comp (ZR f)=ZR (h.comp f) := by
 apply xW (A:=E[X])
 intro p
 simp only [nI,b8y,FR]
theorem cJ3 {E F:Type} [lV E] [lV F] (f :E →+* F) :
   an8 (ZR f)=an8 f := by
 let:nq E F:=f.toAlgebra
 let:nq (Jv E) (Jv F) :=(ZR f).toAlgebra
 let e :=Gi E[X] (oy E)
 let e' := Gi F[X] (oy F)
 have h: (aU (oy E) (oy F)).comp e.toRingHom =
     e'.toRingHom.comp (ZR f) := by
   apply xW (A:=E[X])
   intro p
   simp only [nI,b8y]
   change aU (oy E) (oy F) (e (aU E[X] (Jv E) p)) =
     e' (aU F[X] (Jv F) (p.map f))
   rw [e.commutes,e'.commutes,← qm E[X] (oy E) (oy F),
     qm E[X] F[X] (oy F)]
   rfl
 calc
   an8 (ZR f)=u9 (oy E) (oy F) :=
     Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv e'.toRingEquiv h
   _=u9 E[X] F[X] :=IsFractionRing.finrank_eq E[X] (oy E) F[X] (oy F)
   _=an8 f :=oD Cardinal.toNat (rank_polynomial_polynomial E F)
theorem cJS {E F:Type} [lV E] [lV F] [nq E F] :
  an8 (aU E F)=u9 E F:= by
 unfold an8
 rw [toAlgebra_algebraMap]
theorem degree_comp {E F G:Type} [lV E] [lV F] [lV G]
  (f :E →+* F) (h:F →+* G) :
  an8 f*an8 h=an8 (h.comp f) := by
 let:nq E F:=f.toAlgebra
 let:nq F G:=h.toAlgebra
 let:nq E G:=(h.comp f).toAlgebra
 let:IsScalarTower E F G :=
  IsScalarTower.of_algebraMap_eq (R:=E) (S:=F) (A:=G) fun _=>rfl
 exact Module.finrank_mul_finrank E F G
end
end bz1
end
section
namespace UI
noncomputable section
open K1 cu gT DQ Cu
open scoped Polynomial BigOperators
variable {C₀:sQ} [Fact (qM C₀)] {J:lI kM} {g:ℕ}
variable (R:wJ C₀ J g)
def width :ℕ :=
 (Finset.univ.sup fun j:Fin (g+1)=>(R.equation.coeff j).natDegree)+1
abbrev size :=(g+1)*width R
def coeff (i:Fin (size R)) :oO C₀ :=
 let jk :=finProdFinEquiv.symm i
 (R.equation.coeff jk.1).coeff jk.2
private theorem cGe (j:Fin (g+1)) :
  (R.equation.coeff j).natDegree<width R :=
 Nat.lt_succ_of_le (Finset.le_sup (f := fun i:Fin (g+1) =>
  (R.equation.coeff i).natDegree) (sI j))
theorem cGg : ∃ i,coeff R i≠0:= by
 have hR:R.equation≠0:= by
  intro h
  exact R.irreducible.ne_zero (by simp [h])
 let j:Fin (g+1) :=⟨R.equation.natDegree,by rw [R.degree]; omega⟩
 let k :Fin (width R) :=⟨(R.equation.coeff j).natDegree,cGe R j⟩
 refine ⟨zd (j,k),?_⟩
 simpa [coeff,j,k,Polynomial.coeff_natDegree] using
  Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hR)
private def aFn {F:Type*} [t7 F] {n:ℕ} (v :Fin n→F) :F[X] :=
 ∑ i:Fin n,Polynomial.monomial (i:ℕ) (v i)
private theorem dig {F:Type*} [t7 F] {n:ℕ} (v :Fin n→F) (k :ℕ) :
   (aFn v).coeff k=if h:k<n then v ⟨k,h⟩ else 0:= by
 rw [aFn,Polynomial.finsetSum_coeff]
 split_ifs with h
 · refine (Finset.sum_eq_single (⟨k,h⟩:Fin n) ?_ (fun hn=>(hn (sI _)).elim)).trans ?_
   · intro b _ hb
     exact EK _ (fun he=>hb (Fin.ext he.symm))
   · exact Polynomial.coeff_monomial_same _ _
 · exact Finset.sum_eq_zero (fun b _ =>
     EK _ (fun he=>h (he.symm ▸ b.isLt)))
private theorem bx8 {F:Type*} [t7 F] {n:ℕ} (v :Fin n→F)
  {k :ℕ} (h:k<n) : (aFn v).coeff k=v ⟨k,h⟩:= by
 rw [dig,uh h]
private theorem bx7 {F:Type*} [t7 F] {n:ℕ} (v :Fin n→F)
  {k :ℕ} (h:n≤k) : (aFn v).coeff k=0:= by
 rw [dig,dite_eq_right (Nat.not_lt.mpr h)]
private def auy :XO (size R) :=
 aFn (n:=g+1) fun j =>
  aFn (n:=width R) fun k=>cy (zd (j,k))
private theorem bWQ:aKg (auy R) g:= by
 refine ⟨Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun _ h=>bx7 _ h),?_⟩
 intro j k
 unfold auy
 by_cases hj:j<g+1
 · rw [bx8 _ hj]
   by_cases hk :k<width R
   · simp [bx8 _ hk]
   · simp [bx7 _ (u8 hk)]
 · simp [bx7 _ (u8 hj)]
def a2k (ℓ:Fin (size R)→L) :oO C₀ :=
 ∑ i,zT C₀ (ℓ i)*coeff R i
def cZd (ℓ:Fin (size R)→L) (h:a2k R ℓ≠0) :
    yI R (size R) where
  coordinate i:=coeff R i/a2k R ℓ
  scale :=Units.mk0 (a2k R ℓ)⁻¹ (inv_ne_zero h)
  equation :=auy R
  degree :=bWQ R
  generic_eq := by
    apply zi
    intro j
    apply zi
    intro k
    simp only [Polynomial.coeff_map,Dv,Fz ,
      Units.val_mk0]
    by_cases hj:j<g+1
    · let j' : Fin (g+1) :=⟨j,hj⟩
      rw [auy,bx8 _ hj]
      by_cases hk :k<width R
      · rw [bx8 _ hk]
        rw [xm]
        simp only [coeff,Equiv.symm_apply_apply,div_eq_mul_inv]
        exact oz _ _
      · rw [bx7 _ (u8 hk),
          Ef
            ((cGe R j').trans_le (u8 hk))]
        rw [oY ,mul_zero]
    · have hr :R.equation.coeff j=0 :=
        Ef (by rw [R.degree]; omega)
      rw [auy,bx7 _ (u8 hj),
        ze,oY ,hr,ze,mul_zero]
  coordinates_are_coefficients := by
    intro i
    let jk :=(zd (m:=g+1) (n:=width R)).symm i
    refine ⟨jk.1,jk.2,?_⟩
    simp only [coeff,jk,div_eq_mul_inv,Fz ,Units.val_mk0]
    exact oz _ _
  normalized:= by
    refine ⟨ℓ,?_⟩
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    exact div_self h
private theorem b2j {F:Type*} [lV F] (V:yJ F)
  {n:ℕ} (a :Fin n→F) (ha : ∃ i,a i≠0) :
  ∃ j,a j≠0 ∧ ∀ i,a i/a j∈V:= by
 classical
 obtain ⟨i,hi⟩:=ha
 obtain ⟨j,-,hj⟩:=Finset.exists_max_image Finset.univ (fun i=>V.valuation (a i))
  ⟨i,sI _⟩
 have hpos :=(Ea V.valuation).2 hi
 have hjpos :=hpos.trans_le (hj i (sI i))
 have hjn:a j≠0:=(Ea V.valuation).1 hjpos
 refine ⟨j,hjn,fun i=>(V.valuation_le_one_iff _).1 ?_⟩
 rw [map_div₀,div_le_iff₀ hjpos,p5]
 exact hj i (sI i)
private theorem UC {F:Type*} [CommSemiring F] {n:ℕ}
  (a :Fin n→F) (x :F) :
  (aFn a).eval x = ∑ i:Fin n,x^(i:ℕ)*a i:= by
 rw [aFn,Polynomial.eval_finsetSum]
 simp [Polynomial.eval_monomial,oz]
private theorem dij {F:Type*} [t7 F] {n:ℕ}
  (a :Fin n→F) (ha : ∃ i,a i≠0) :aFn a≠0:= by
 obtain ⟨i,hi⟩:=ha
 intro h
 have hc:=oD (fun p:F[X]=>p.coeff i) h
 exact hi (by simpa only [bx8 _ i.isLt,Polynomial.coeff_zero]
  using hc)
private theorem P5 {ι:Type*} [Finite ι] {n:ℕ}
   (a :Fin n→ oO C₀) (ha : ∃ i,a i≠0)
   (b:ι→Fin n→L) (hb : ∀ j,∃ i,b j i≠0) :
   ∃ ℓ:Fin n→L,(∑ i,zT C₀ (ℓ i)*a i)≠0 ∧
     ∀ j,(∑ i,ℓ i*b j i)≠0:= by
 have hF : ∀ᶠ x :L in Filter.cofinite,
     (aFn a).eval (zT C₀ x)≠0:= by
   have hf :=((Polynomial.finite_setOfPred_isRoot (dij a ha)).preimage
     (zT C₀).injective.injOn).compl_mem_cofinite
   exact Filter.Eventually.mono hf (fun _ h=> by
     simpa only [Set.mem_preimage,Set.mem_ofPred_eq,Polynomial.IsRoot] using h)
 have hL : ∀ᶠ x :L in Filter.cofinite,∀ j,
     (aFn (b j)).eval x≠0 :=
   Filter.eventually_all.2 fun j=>Polynomial.eventually_eval_ne_zero_cofinite
     (dij (b j) (hb j))
 obtain ⟨x,hx,hy⟩:=(hF.and hL).exists
 refine ⟨fun i=>x^(i:ℕ),?_,?_⟩
 · rw [UC] at hx
   simpa only [u5] using hx
 · intro j
   rw [← UC]
   exact hy j
theorem bnF {ι:Type*} [Finite ι] (z :ι→K) (S:ι→K[X])
    (M : ∀ j,akV R (z j) (S j)) (hM : ∀ j,(M j).by2) :
    ∃ A:yI R (size R),
      ∀ j i,LW R (A.coordinate i)∈(M j).V:= by
  classical
  let a (i:Fin (size R)) :=LW R (coeff R i)
  have ha : ∃ i,a i≠0:= by
    obtain ⟨i,hi⟩:=cGg R
    exact ⟨i,(map_ne_zero (LW R)).2 hi⟩
  choose pivot hp hv using fun j=>b2j (M j).V a ha
  let u (j:ι) (i:Fin (size R)) : (M j).V:=⟨a i/a (pivot j),hv j i⟩
  have hu (j:ι) (i:Fin (size R)) :
      ∃ k :L,nX (M j).V (u j i) =
        nX (M j).V ((M j).constant k) := by
    have he :LW R (coeff R i/ coeff R (pivot j))=a i/a (pivot j) := by
      simp [a]
    obtain ⟨k,hk⟩:=hM j (coeff R i/ coeff R (pivot j)) (by rw [he]; exact hv j i)
    have hsub:u j i=⟨LW R (coeff R i/ coeff R (pivot j)),
        by rw [he]; exact hv j i⟩:=sS he.symm
    exact ⟨k,hsub ▸ hk⟩
  choose b hb using hu
  have hb₀ (j:ι) : ∃ i,b j i≠0:= by
    refine ⟨pivot j,?_⟩
    have hu1 :u j (pivot j)=1 :=sS (div_self (hp j))
    intro hzero
    simpa [hzero,hu1] using hb j (pivot j)
  obtain ⟨ℓ,hℓ,hℓb⟩:=P5 (coeff R) (cGg R) b hb₀
  refine ⟨cZd R ℓ hℓ,?_⟩
  intro j i
  let d: (M j).V := ∑ k,(M j).constant (ℓ k)*u j k
  have hd:IsUnit d:= by
    apply (yU _).mp
    have he :=(map_ne_zero ((nX (M j).V).comp (M j).constant)).2 (hℓb j)
    simpa [d,hb j,qy ,oj,nI] using he
  have hconst (k :L) : ((M j).constant k :EC R) =
      LW R (zT C₀ k) := by
    change ((M j).V.toSubring.subtype.comp (M j).Aw)
      (c9 (aU L FX k))= _
    rw [(M j).generic_eq]
    simp only [ek,nI,LG,v8 ,
      AdjoinRoot.mk_C]
    change vj (K8 R) (Mr C₀ (aU L FX k))= _
    unfold LW
    rw [nI]
    congr 1
    rw [qm L L[X] FX]
    unfold Mr t9
    rw [uW]
    simp [Mu,F5]
  have hdval : (d:EC R)=LW R (a2k R ℓ)/a (pivot j) := by
    change (M j).V.toSubring.subtype d= _
    simp only [d,a2k,qy ,oj,Finset.sum_div,mul_div_assoc]
    exact Finset.sum_congr rfl (fun k _=>congrArg₂ (· * ·) (hconst (ℓ k)) rfl)
  have hdv :=((M j).V.valuation_eq_one_iff d).1 hd
  rw [hdval] at hdv
  have hcancel:LW R ((cZd R ℓ hℓ).coordinate i) =
      (a i/a (pivot j))/(LW R (a2k R ℓ)/a (pivot j)) := by
    change LW R (coeff R i/a2k R ℓ)= _
    rw [map_div₀]
    exact (div_div_div_cancel_right₀ (hp j) _ _).symm
  apply ((M j).V.valuation_le_one_iff _).1
  rw [hcancel,map_div₀,hdv,div_one]
  exact (M j).V.valuation_le_one (u j i)
end
end UI
end
section
open private Cu.KK XW.bpV from ProximityPrize.SubmissionLower.ZgdIx1d
namespace UI
noncomputable section
open K1 cu gT DQ Cu
open scoped Polynomial
variable {C₀:sQ} [Fact (qM C₀)] {J:lI kM} {g:ℕ}
variable {R:wJ C₀ J g}
private def KK:FX:=aU L[X] FX pC
private theorem b2z :Mr C₀ KK=F5 C₀ Polynomial.X:= by
 unfold Mr KK t9
 rw [uW]
 simp [F5]
private theorem bpV (a :L) :
  Mr C₀ (aU L FX a)=Mu C₀ (zT C₀ a) := by
 rw [qm L L[X] FX]
 unfold Mr t9
 rw [uW]
 simp [Mu,F5]
private def qw (n:ℕ) :DT n →+* oZ n :=
 pG (MvPolynomial.C.comp (aU L FX))
  (fun i=>cy (some i))
private def bps {n:ℕ} (A:yI R n) :oZ n :=
 A.equation.eval₂ (wY (qw n) (c9 KK))
  (cy none)
private theorem d1v {n:ℕ} (A:yI R n) :
   bps A∈SO A:= by
 let F:=y7 C₀
 let e :=pG (zT C₀) A.coordinate
 have hp: (adq A).comp (qw n) =
     (ov :F →+* F[X]).comp ((Mu C₀).comp e) := by
   apply oK
   · intro a
     simp [qw,adq,bpV,e]
   · intro i
     simp [qw,adq,e]
 have hx : (adq A).comp (wY (qw n)
     (c9 KK)) =
     (ov :F →+* F[X]).comp ((F5 C₀).comp (wB e)) := by
   apply yo
   · intro a
     simpa [Mu] using y5 hp a
   · simp [adq,b2z]
 change adq A (bps A)∈p7 {K8 R}
 rw [bps,th,hx]
 have hy :adq A (cy none)=Polynomial.X:= by simp [adq]
 rw [hy]
 change (A.equation.map ((F5 C₀).comp (wB e)))∈_
 rw [← FR,A.generic_eq,Polynomial.map_mul,zS]
 exact C4 _ _ (vw (Eg _))
private theorem d1u {n:ℕ} (A:yI R n)
    (t:Fin n→L) (S:K[X]) :
    pL (ZS t S) (bps A) =
      aU L[X] FX ((specialize A.equation t).eval (j9 S)) := by
  let e :=pL t
  have hp: (pL (ZS t S)).comp (qw n) =
      (aU L FX).comp e := by
    apply oK
    · intro a
      simp [qw,e]
    · intro i
      simp [qw,ZS,e]
  have hx : (pL (ZS t S)).comp
      (wY (qw n) (c9 KK)) =
      (aU L[X] FX).comp (wB e) := by
    apply yo
    · intro a
      simp only [nI,yl,Du,
        Dv,zS]
      rw [← nI,hp,nI,qm L L[X] FX]
      rfl
    · simp [KK]
  rw [bps,th,hx,zf ,ZS,kr]
  rw [specialize,Polynomial.eval_map,th]
section Lift
variable {z :K} {S:K[X]} (M:akV R z S)
local notation "res" => IsLocalRing.residue M.V
local notation "inc" => M.V.toSubring.subtype
private def aih (i:Fin 2) :M.V :=
 M.Aw (cy (p9 (by decide :2≤3) i))
private def caL:M.V:=M.Aw (cy 2)
private theorem cTN (x :FX) :
  inc (M.fx x)=vj (K8 R) (Mr C₀ x) := by
 change ((inc).comp M.Aw) (c9 x)= _
 rw [M.generic_eq]
 simp [ek,LG]
private theorem b4I (i:Fin 2) :
  inc (aih M i)=LW R (Wt C₀ i) := by
 change ((inc).comp M.Aw) (cy (p9 (by decide :2≤3) i))= _
 rw [M.generic_eq]
 fin_cases i <;> simp [ek,LG,LW]
private theorem ege :inc (caL M)=AdjoinRoot.root (K8 R) := by
 change ((inc).comp M.Aw) (cy 2)= _
 rw [M.generic_eq]
 simp [ek,LG]
private theorem goD (a b y :FX) (i:Fin 2) :
  (![a,b,y] :Fin 3→FX) (p9 (by decide :2≤3) i) = ![a,b] i:= by
 fin_cases i <;> rfl
private theorem b8Q (i:Fin 2) :
   res (aih M i)=((res).comp M.fx)
     (![jz z,(jz z)^p] i) := by
 change ((res).comp M.Aw) (cy (p9 (by decide :2≤3) i))= _
 rw [M.marked_eq]
 simp only [nI,aEE,zf]
 change res (M.fx (![jz z,(jz z)^p,kr S]
   (p9 (by decide :2≤3) i))) =
   res (M.fx (![jz z,(jz z)^p] i))
 rw [goD]
private theorem ezH :res (caL M)=((res).comp M.fx) (kr S) := by
 change ((res).comp M.Aw) (cy 2)= _
 rw [M.marked_eq]
 simp [aEE,akV.fx]
private theorem cMW {F E Q O σ:Type*} [lV F] [lV E]
  [ox Q] [ox O] (inj:O →+* Q) (hi:p6 inj)
  (r :O →+* E) (k :F →+* E) (u:mD σ F →+* O)
  (pt:σ→F) (he :r.comp u=k.comp (pL pt))
  (f :mD σ F) (hf : (inj.comp u) f=0) :
  pL pt f=0:= by
 have hz :u f=0:=hi (by simpa only [nI,oY] using hf)
 apply k.injective
 simpa only [nI,hz,oY] using (y5 he f).symm
variable {n:ℕ} (A:yI R n)
variable (q:Fin n→M.V) (t:Fin n→L)
private theorem dyD
   (hg : ∀ i,inc (q i)=LW R (A.coordinate i))
   (ht : ∀ i,res (q i)=res (M.constant (t i))) :
   aCn z t∈sH FX (EF A) := by
 let ev :=pG M.fx (Sum.elim (aih M) q)
 have hgen: (inc).comp ev=(vj (K8 R)).comp (W8 A) := by
   apply oK
   · intro x
     simpa [ev,W8] using cTN M x
   · intro i
     cases i with
     | inl j=>simpa [ev,W8,LW] using b4I M j
     | inr j=>simpa [ev,W8,LW] using hg j
 have hmark : (res).comp ev=((res).comp M.fx).comp (pL (aCn z t)) := by
   apply oK
   · intro x
     simp [ev]
   · intro i
     cases i with
     | inl j=>simpa [ev,aCn] using b8Q M j
     | inr j=>simpa [ev,akV.constant,aCn] using ht j
 apply MvPolynomial.mem_zeroLocus_iff_le_ker_aeval.mpr
 intro f hf
 change pL (aCn z t) f=0
 apply cMW inc xu res _ ev _ hmark
 rw [hgen,nI,show W8 A f=0 from hf,oY]
private theorem gs9
   (hg : ∀ i,inc (q i)=LW R (A.coordinate i))
   (ht : ∀ i,res (q i)=res (M.constant (t i))) :
   ZS t S∈sH FX (SO A) := by
 let ev :=pG M.fx (fun i:lJ (Fin n)=>i.elim (caL M) q)
 have hgen: (inc).comp ev=(AdjoinRoot.mk (K8 R)).comp (adq A) := by
   apply oK
   · intro x
     simpa [ev,adq] using cTN M x
   · intro i
     cases i with
     | none=>simpa [ev,adq] using ege M
     | some j=>simpa [ev,adq,LW] using hg j
 have hmark : (res).comp ev=((res).comp M.fx).comp (pL (ZS t S)) := by
   apply oK
   · intro x
     simp [ev]
   · intro i
     cases i with
     | none=>simpa [ev,ZS] using ezH M
     | some j=>simpa [ev,akV.constant,ZS] using ht j
 apply MvPolynomial.mem_zeroLocus_iff_le_ker_aeval.mpr
 intro f hf
 change pL (ZS t S) f=0
 apply cMW inc xu res _ ev _ hmark
 rw [hgen,nI]
 exact AdjoinRoot.mk_eq_zero.mpr (Ideal.mem_span_singleton.mp hf)
end Lift
theorem gtQ {n:ℕ} (A:yI R n)
   {z :K} {S:K[X]} (M:akV R z S) (hM:M.by2)
   (hreg : ∀ i,LW R (A.coordinate i)∈M.V) :
   ∃ t:Fin n→L,
     aCn z t∈sH FX (EF A) ∧
     ZS t S∈sH FX (SO A) ∧
     (specialize A.equation t).eval (j9 S)=0:= by
 classical
 let q (i:Fin n) :M.V:=⟨LW R (A.coordinate i),hreg i⟩
 choose t ht using fun i=>hM (A.coordinate i) (hreg i)
 have hbase :=dyD M A q t (fun _=>rfl) ht
 have hsource :=gs9 M A q t (fun _=>rfl) ht
 refine ⟨t,hbase,hsource,?_⟩
 apply t5 L[X] FX
 rw [oY ,← d1u A t S]
 have he :=(MvPolynomial.mem_zeroLocus_iff_le_ker_aeval.mp hsource) (d1v A)
 exact he
end
end UI
end
section
namespace akS
noncomputable section
open K1 cu Cu MvPolynomial
def c1 :Prop :=
  ∀ (n:ℕ) (B:lI (Gc n)),B.IsPrime →
    (vH B).natDegree≤1 →
    ∃ D:ℕ,∀ k :ℕ,aIU B (D + k) ≤
      abb (F:=e7 n) (aoe B) (aIU B D) k
def c2 :Prop :=
  ∀ (n H :ℕ) (B:lI (Gc n)),B.IsPrime→a9K B H →
    ∀ W:pU (e7 n) (Mb B),qU (e7 n) W →
    ∃ C:ℕ,∀ k :ℕ,
      u9 (e7 n) (abb (F:=e7 n) (aoe B) W k)≤C+k*H
theorem of_children (h₁:c1) (h₂:c2) :Cu.c5:= by
  classical
  intro n H B hB hH q hq V pt hinj hpt
  let:B.IsPrime :=hB
  obtain ⟨D,hD⟩:=h₁ n B hB hH.dimension
  obtain ⟨r,hr⟩:=d4l B q hq V pt hinj hpt
  let mulMark (j : ↥V) :Mb B →ₗ[e7 n] Mb B :=
    pz (e7 n) (ajy B (r j))
  let pieces (j : ↥V) :pU (e7 n) (Mb B) :=
    (aIU B D).map (mulMark j)
  let W:=iSup pieces
  have c32 (j : ↥V) :qU (e7 n) (pieces j) := by
    dsimp only [pieces]
    infer_instance
  let : ∀ j,qU (e7 n) (pieces j) :=c32
  let:qU (e7 n) W:=Submodule.finite_iSup pieces
  obtain ⟨C,hC⟩:=h₂ n H B hB hH W inferInstance
  have hcount (k :ℕ) : (k+1)*V.card≤C+(k*q.totalDegree)*H := by
    let S:=abb (F:=e7 n) (aoe B) W (k*q.totalDegree)
    let v (ij:Fin (k+1)×(↥V)) :=
      ajy B ((lz B (aa4 n q))^(ij.1 :ℕ)*r ij.2)
    have hmem (ij:Fin (k+1)×(↥V)) :v ij∈S:= by
      obtain ⟨i,j⟩:=ij
      have hdeg: (q^(i:ℕ)).totalDegree≤D + k*q.totalDegree :=
        ((totalDegree_pow q (i:ℕ)).trans
          (F9 _ (Nat.le_of_lt_succ i.isLt))).trans (Nat.le_add_left _ _)
      have hp:=hD (k*q.totalDegree) (eJS B _ hdeg)
      have hj:pieces j≤W:=le_iSup pieces j
      have hm: (abb (F:=e7 n) (aoe B) (aIU B D)
          (k*q.totalDegree)).map (mulMark j)≤S :=
        ey8 (F:=e7 n) (A:=Mb B) (aoe B)
          (ajy B (r j)) (W:=aIU B D) (U:=W) hj (k*q.totalDegree)
      apply hm
      refine Submodule.mem_map.mpr ⟨_,hp,?_⟩
      simp only [mulMark,v,LinearMap.mulLeft_apply,oj,u5]
      exact oz _ _
    let w:Fin (k+1)×(↥V)→S:= fun ij=>⟨v ij,hmem ij⟩
    have hw:xL (e7 n) w :=
      LinearIndependent.of_comp S.subtype (hr k)
    have h:=hw.fintype_card_le_finrank
    exact (by simpa [S,Fintype.card_prod] using h.trans (hC (k*q.totalDegree)))
  by_contra! hn
  have hbad:=Nat.mul_le_mul_left (C+1) (Nat.succ_le_of_lt hn)
  have ht:=hbad.trans (hcount C)
  rw [yL,Nat.mul_assoc,Nat.succ_mul C (q.totalDegree*H)] at ht
  omega
end
end akS
end
section
open private Cu.b7z from ProximityPrize.SubmissionLower.ZgdIx1d
namespace UI
noncomputable section
open K1 cu gT Cu
open scoped Polynomial
variable {C₀:sQ} [Fact (qM C₀)] {J:lI kM} {g:ℕ}
variable (R:wJ C₀ J g)
theorem etI:pQ (ek R)=J:= by
 refine Eq.trans ?_ R.contraction.symm
 ext f
 change AdjoinRoot.mk (K8 R) (LG C₀ f)=0 ↔
  LG C₀ f∈p7 {K8 R}
 rw [AdjoinRoot.mk_eq_zero,Ideal.mem_span_singleton]
private theorem b7z {A F E :Type*} [ox A] [lV F] [lV E]
   (j:A →+* F) (m:A →+* E) (s :E →+* A)
   (hm:pQ j≤pQ m) (hs :m.comp s=z9 E) :
   ∃ (V:yJ F) (a :A →+* V),
     V.toSubring.subtype.comp a=j ∧
     (nX V).comp a=((nX V).comp (a.comp s)).comp m:= by
 let B:=j.range
 let q:A →+* B:=j.rangeRestrict
 let e :A ⧸ pQ j →+* E :=Ee _ m hm
 let mB:B →+* E :=e.comp j.quotientKerEquivRange.symm.toRingHom
 have hq (f :A) :mB (q f)=m f := by
   change e (j.quotientKerEquivRange.symm (j.rangeRestrict f))= _
   rw [RingHom.quotientKerEquivRange,RingEquiv.symm_trans_apply,
     RingHom.quotientKerEquivOfSurjective_symm_apply j.rangeRestrict_surjective,
     Ideal.quotEquivOfEq_symm,Ideal.quotEquivOfEq_mk]
   rfl
 obtain ⟨V,hBV,hnon⟩:=(pQ mB).image_subset_nonunits_valuationSubring
   (RingHom.ker_ne_top mB)
 let a :A →+* V:=j.codRestrict V.toSubring (fun f=>hBV ⟨f,rfl⟩)
 refine ⟨V,a,rfl,?_⟩
 apply t6
 intro f
 let b:A:=f - s (m f)
 have hb:q b∈pQ mB:= by
   change mB (q b)=0
   rw [hq]
   simp only [b,qG,← nI m s,hs,RingHom.id_apply,sub_self]
 have hv :a b∈IsLocalRing.maximalIdeal V :=
   V.coe_mem_nonunits_iff.mp (hnon ⟨q b,hb,rfl⟩)
 have hz :=(IsLocalRing.residue_eq_zero_iff _).2 hv
 simpa only [b,qG,sub_eq_zero,nI] using hz
theorem d4q {z :K} {S:K[X]} (hm:aSf J z S) :
  Nonempty (akV R z S) := by
 have hk :pQ (ek R)≤pQ (aEE z S) :=
  (etI R).symm ▸ hm
 have hc: (aEE z S).comp c9=z9 FX:= by
  apply t6
  intro x
  simp [aEE]
 obtain ⟨V,a,hgen,hmark⟩ :=
  b7z (ek R) (aEE z S) c9 hk hc
 exact ⟨⟨V,a,hgen,hmark⟩⟩
end
end UI
end
section
namespace czw
open aiO
open scoped TensorProduct
noncomputable section
variable {k ι σ:Type} [lV k]
local notation "F" => Jo k ι
local notation "P" => MvPolynomial ι k
local notation "A" => MvPolynomial σ k
local notation "V" => MvPolynomial σ F
private abbrev EG:A →+* V :=
 n5 (aU k F)
private theorem cZo (offset :ι) (u:mD (E8 offset) A)
    {D:Type} [ox D] [nq F D] (f :V →ₐ[F] D) :
    f (anY offset u) =
      pG (f.toRingHom.comp EG)
        (fun i=>aU F D (ahI i.val)) u -
        aU F D (ahI offset) := by
  rw [anY,qG,zh]
  change f.toRingHom (pG EG
    (fun i=>c9 (ahI i.val)) u)-_ = _
  rw [Fa]
  have hX: (fun i:E8 offset=>f.toRingHom (c9 (ahI (k :=k) i.val))) =
      (fun i=>aU F D (ahI i.val)) :=funext fun i=>f.commutes _
  rw [hX]
private def aXt (offset :ι) (I:lI A) (u:mD (E8 offset) A) :
    bbf offset I u ≃ₐ[F]
      Gd k offset (n5 (lz I) u) := by
  classical
  let v :=n5 (lz I) u
  let B:=mD (E8 offset) (A ⧸ I)
  letI:=ami (k :=k) offset v
  letI:Module P B:=zm
  let T:=Gd k offset v
  let J:=I.map EG ⊔ p7 {anY offset u}
  let S:=V ⧸ J
  let q:V →ₐ[F] S:=Ideal.Quotient.mkₐ F J
  let r :B →ₐ[P] T:=wA
  let j:A →+* T:=r.toRingHom.comp (MvPolynomial.C.comp (lz I))
  let f :V →ₐ[F] T:=t8 (fun s=>j (cy s))
  have offset_C (a :k) :
      No (k :=k) offset v (c9 a) =
        c9 (lz I (c9 a)) := by
    rw [No,v8]
    rfl
  have offset_X (i:E8 offset) :
      No (k :=k) offset v (cy i.val)=cy i:= by
    rw [No,xm,dite_eq_right i.property]
  have offset_self :No (k :=k) offset v (cy offset)=v := by
    rw [No,xm,uh rfl]
  have scalar_relation (p:P) :
      r (No (k :=k) offset v p)=aU F T (aU P F p) :=
    r.commutes p
  have other_relation (i:E8 offset) :
      r (cy i)=aU F T (ahI i.val) := by
    have h:=scalar_relation (cy i.val)
    rw [offset_X] at h
    exact h
  have offset_relation :r v=aU F T (ahI offset) := by
    have h:=scalar_relation (cy offset)
    rw [offset_self] at h
    exact h
  have f_coeff :f.toRingHom.comp EG=j:= by
    apply oK
    · intro a
      change f (EG (c9 a)) =
        r (c9 (lz I (c9 a)))
      rw [EG,wR,zh]
      have h:=scalar_relation (c9 a)
      rw [offset_C] at h
      exact h.symm
    · intro s
      change f (EG (cy s))=j (cy s)
      rw [EG,vi]
      exact uJ _ _
  have f_u:pG j (fun i=>aU F T (ahI i.val)) u=r v := by
    dsimp only [v]
    rw [MvPolynomial.map_eq_eval₂Hom_C_comp]
    change _=r.toRingHom (pG _ _ u)
    rw [Fa]
    change _=pG j (fun i=>r (cy i)) u
    simp_rw [other_relation]
  have f_cut:f (anY offset u)=0:= by
    rw [cZo,f_coeff,f_u,offset_relation,sub_self]
  have f_kills :J≤pQ f.toRingHom:= by
    apply sup_le
    · apply (Ideal.map_le_iff_le_comap).mpr
      intro a ha
      have h:f.toRingHom (EG a)=j a :=qz f_coeff a
      change f.toRingHom (EG a)=0
      rw [h]
      have hz :lz I a=0:=Ideal.Quotient.eq_zero_iff_mem.mpr ha
      simp only [j,nI,hz,oY]
    · apply Ideal.span_le.mpr
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst a
      exact RingHom.mem_ker.mpr f_cut
  let forward:S →ₐ[F] T:=Et J f fun a ha =>
    RingHom.mem_ker.mp (f_kills ha)
  have forward_mk (p:V) :forward (q p)=f p:=rfl
  have q_kills (a :A) (ha :a∈I) : (q.toRingHom.comp EG) a=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show I.map EG≤J from le_sup_left) (Ideal.mem_map_of_mem _ ha))
  let j' : (A ⧸ I) →+* S:=Ee I (q.toRingHom.comp EG) q_kills
  let g₀:B →+* S:=pG j'
    (fun i=>aU F S (ahI i.val))
  have j'_mk (a :A) :j' (lz I a)=(q.toRingHom.comp EG) a :=rfl
  have g_C (a :A) :g₀ (c9 (lz I a))=q (EG a) :=
    (v8 _ _ _).trans (j'_mk a)
  have g_X (i:E8 offset) :
      g₀ (cy i)=aU F S (ahI i.val) :=
    xm _ _ _
  have g_offset :g₀ v=aU F S (ahI offset) := by
    have h:q (anY offset u)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((show p7 {anY offset u} ≤ J from le_sup_right)
          (vw (by simp)))
    have hq:=cZo (D:=S) offset u q
    rw [hq,sub_eq_zero] at h
    have hj:j'.comp (lz I)=q.toRingHom.comp EG :=
      t6 j'_mk
    change pG j'
      (fun i:E8 offset=>aU F S (ahI i.val))
      (n5 (lz I) u)= _
    rw [MvPolynomial.eval₂Hom_map_hom (S₂:=S),hj]
    exact h
  have g_scalar :g₀.comp (No (k :=k) offset v) =
      (aU F S).comp (aU P F) := by
    apply oK
    · intro a
      change g₀ (No (k :=k) offset v (c9 a)) =
        aU F S (aU P F (c9 a))
      rw [offset_C,g_C,EG,wR,zh]
      rfl
    · intro i
      change g₀ (No (k :=k) offset v (cy i)) =
        aU F S (ahI i)
      by_cases hi:i=offset
      · subst i
        rw [offset_self]
        exact g_offset
      · rw [offset_X (⟨i,hi⟩:E8 offset)]
        exact g_X ⟨i,hi⟩
  let uZ:P →+* S:=(aU F S).comp (aU P F)
  letI scalarAlgebra :nq P S:=uZ.toAlgebra' fun c x=> by
    exact oz (uZ c) x
  letI:SMul P S:=scalarAlgebra.toSMul
  letI:IsScalarTower P F S :=
    IsScalarTower.of_algebraMap_eq' (R:=P) (S:=F) (show aU P S=uZ from rfl)
  let g:B →ₐ[P] S:=⟨g₀,qz g_scalar⟩
  let back :T →ₐ[F] S:=AlgHom.liftEquiv P F B S g
  have back_right (b:B) :back (r b)=g₀ b:= by
    change (AlgHom.liftEquiv P F B S g) (1 ⊗ₜ[P] b)=g b
    simp only [AlgHom.liftEquiv_tmul,one_smul]
  refine AlgEquiv.ofAlgHom forward back ?_ ?_
  · apply AlgHom.coe_ringHom_injective
    apply Algebra.TensorProduct.ringHom_ext (R:=P)
    · apply t6
      intro a
      change forward (back (aU F T a))=aU F T a
      rw [back.commutes,forward.commutes]
    · apply oK
      · intro a
        obtain ⟨a,rfl⟩:=FK a
        change forward (back (r (c9 (lz I a)))) =
          r (c9 (lz I a))
        rw [back_right,g_C,forward_mk]
        exact qz f_coeff a
      · intro i
        change forward (back (r (cy i)))=r (cy i)
        rw [back_right,g_X,forward.commutes,other_relation]
  · apply Ideal.Quotient.algHom_ext F
    apply FU
    intro s
    change back (forward (q (cy s)))=q (cy s)
    rw [forward_mk]
    change back (t8 (fun s=>j (cy s)) (cy s))= _
    rw [uJ]
    change back (r (c9 (lz I (cy s))))= _
    rw [back_right,g_C,EG,vi]
theorem proof :aiO.c1 := by
 intro k ι σ _ offset I u d
 let e :=(aXt offset I u).toLinearEquiv
 simp only [JR,Module.Finite.equiv_iff e,e.finrank_eq]
end
end czw
end
section
namespace ane
noncomputable section
open cu DQ MvPolynomial
open scoped Polynomial
def c1 :Prop :=
  ∀ (n:ℕ) (J:lI (oZ n)),J.IsPrime →
    (vH J).natDegree=1 →
    bQo J (aD8 n) 0 1
def c2 :Prop :=
  ∀ (n:ℕ) (J:lI (oZ n)),J.IsPrime →
    (vH J).natDegree=1 →
    bQo J (aD3 n) 1 0
private theorem b6A (f :ℕ→ℕ) (d N m:ℕ)
   (h : ∀ i:ℕ,N≤ i→f (i+1)≤f i+d) :
   f (N+m)≤f N+m*d:= by
 induction m with
 | zero=>simp
 | succ m ih =>
     rw [← Nat.add_assoc,Nat.succ_mul]
     exact (h (N+m) (vl _ _)).trans (by omega)
theorem of_children (h1 :c1) (h2 :c2) :DQ.c3:= by
  intro n a b Dparam Dy ha hb J hJ hdim hslice
  obtain ⟨N₁,h₁⟩:=dfD (h1 n J hJ hdim)
  obtain ⟨N₂,h₂⟩:=dfD (h2 n J hJ hdim)
  let N₀:=max N₁ N₂
  let F (u v :ℕ) :=u9 (jY n) (box J u v)
  let H (N :ℕ) :=F (a*N) (b*N)
  let d:=b*Dparam+a*Dy
  let _:qU (jY n) (Gl J (aD8 n)) :=hslice.parameter_finite
  let _:qU (jY n) (Gl J (aD3 n)) :=hslice.a6j
  have hstep (N :ℕ) (hN :N₀≤N) :H (N+1)≤H N+d:= by
    have hu:N₀≤a*N :=hN.trans (C9 N ha)
    have hv :N₀≤b*N :=hN.trans (C9 N hb)
    have hp (v :ℕ) (hv' : b*N≤v) :F (a*N) (v+1)≤F (a*N) v+Dparam :=
      (cSd J (aD8 n) (a*N) v (a*N) (v+1)
        (h₁ _ _ ((le_max_left _ _).trans hu) ((le_max_left _ _).trans (hv.trans hv')))).trans
        (x7 hslice.parameter_length _)
    have hy (u:ℕ) (hu' : a*N≤u) :
        F (u+1) (b*N+b)≤F u (b*N+b)+Dy :=
      (cSd J (aD3 n) u (b*N+b) (u+1) (b*N+b)
        (h₂ _ _ ((le_max_right _ _).trans (hu.trans hu'))
          ((le_max_right _ _).trans (hv.trans (vl _ _))))).trans
        (x7 hslice.ordinate_length _)
    have hp' := b6A (F (a*N)) Dparam (b*N) b hp
    have hy' := b6A (fun u=>F u (b*N+b)) Dy (a*N) a hy
    dsimp only [H,d]
    rw [yL,yL]
    omega
  have hlin (N :ℕ) (hN :N₀≤N) :H N≤H N₀+N*d:= by
    have h:=b6A H d N₀ (N-N₀) hstep
    rw [Nat.add_sub_of_le hN] at h
    exact h.trans (x7 (F9 d (Nat.sub_le _ _)) _)
  let R:ℚ[X] :=ov (d:ℚ)*pC+Polynomial.C (H N₀:ℚ)
  have hR:R.natDegree≤1 :=Polynomial.natDegree_linear_le
  have hRcoeff :R.coeff 1=(d:ℚ) := by
    simp [R]
  have hdim' : (vH (br4 a b J)).natDegree=1 :=
    (natDegree_affineHilbertPolynomial_comap_bidegreeMap ha hb J).trans hdim
  have hdeg:=affineDegree_le_of_eventually_affineHilbertFunction_le hdim' hR (by
    filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
    have h:=(affineHilbertFunction_comap_bidegreeMap_le J a b N).trans
      ((ea6 J (a*N) (b*N)).trans (hlin N hN))
    change affineHilbertFunction (br4 a b J) N≤H N₀+N*d at h
    calc
      _≤(H N₀:ℚ)+(N :ℚ)*(d:ℚ) := by exact_mod_cast h
      _=R.eval (N :ℚ) := by
        simp only [R,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
        rw [add_comm (H N₀:ℚ),oz (N :ℚ)])
  simpa only [Nat.factorial_one,Nat.cast_one,p5 ,hRcoeff,d] using hdeg
end
end ane
end
section
namespace UI
noncomputable section
open K1 cu gT DQ Cu
open scoped Polynomial
def c1 :Prop :=
  ∀ (C₀:sQ) [Fact (qM C₀)],
    letI:nq L (oO C₀) :=(zT C₀).toAlgebra
    ∃ i:Fin 2,v9 L (fun _:Unit=>Wt C₀ i)
def c2 :Prop :=
  ∀ (C₀:sQ) [Fact (qM C₀)] (J:lI kM) (g:ℕ)
    (R:wJ C₀ J g) (z :K) (S:K[X]) (M:akV R z S) (i:Fin 2),
    letI:nq L (oO C₀) :=(zT C₀).toAlgebra
    v9 L (fun _:Unit=>Wt C₀ i) →
    M.by2
theorem of_children (h1 :c1) (h2 :c2) :Cu.c2 := by
 classical
 intro C₀ _ J g R T z s hmark
 obtain ⟨i,hi⟩:=h1 C₀
 let I := ↥(T:Set K)
 let M (j:I) :akV R (z j) (s j) :=
   Classical.choice (d4q R (hmark j j.property))
 have hM (j:I) : (M j).by2 :=h2 C₀ J g R (z j) (s j) (M j) i hi
 obtain ⟨A,hreg⟩:=bnF R (z ∘ (Aa :I→K)) (s ∘ Aa) M hM
 choose t ht using fun j:I=>gtQ A (M j) (hM j) (hreg j)
 let p (γ:K) :=if hγ:γ∈T then t ⟨γ,hγ⟩ else fun _=>0
 refine ⟨size R,A,p,?_,?_,?_⟩
 · intro γ hγ
   simpa only [p,uh hγ] using (ht ⟨γ,hγ⟩).1
 · intro γ hγ
   simpa only [p,uh hγ] using (ht ⟨γ,hγ⟩).2.1
 · intro γ hγ
   simpa only [p,uh hγ] using (ht ⟨γ,hγ⟩).2.2
end
end UI
end
section
namespace aqf
noncomputable section
open cu DQ ane MvPolynomial
abbrev Affine {k σ:Type*} [lV k] (J:lI (mD (lJ σ) k)) :=
 mD (lJ σ) k ⧸ J
abbrev Oh {k σ:Type*} [lV k] (J:lI (mD (lJ σ) k))
 (d:ℕ×ℕ) :=quotientBidegreeLE J d.1 d.2
abbrev jU {k σ:Type*} [lV k] (J:lI (mD (lJ σ) k)) :Affine J :=
 lz J (cy none)
variable {n:ℕ} (J:lI (oZ n))
abbrev UG:=mD (lJ (Fin n)) (Affine J)
def Yy (d:ℕ×ℕ) :pU FX (UG J) where
  carrier := {p | ∀ m,p.coeff m∈Oh J d}
  zero_mem' m:=(Oh J d).zero_mem
  add_mem' hp hq m:=(Oh J d).add_mem (hp m) (hq m)
  smul_mem' c p hp:= by
    change ∀ m,(c•p).coeff m∈Oh J d
    intro m
    rw [MvPolynomial.coeff_smul]
    exact (Oh J d).smul_mem c (hp m)
def avS:UG J:=c9 (jU J)-MvPolynomial.X none
structure cxk where
  toSlice :UG J →ₐ[FX] agD J
  injective_toSlice :p6 toSlice
  ab6:toSlice (avS J)=aaK J (aD3 n)
  map_box : ∀ (d:ℕ×ℕ) (p:UG J),
    p∈Yy J d→toSlice p∈box J d.1 d.2
  clear_boxes : ∀ (d e :ℕ×ℕ) (x t:agD J),
    x∈box J d.1 d.2→t∈box J e.1 e.2 →
      ∃ (s :jY n) (_:s≠0) (p q:UG J),
        p∈Yy J d∧q∈Yy J e ∧
          toSlice p=s•x∧toSlice q=s•t
end
end aqf
end
section
namespace aqf
noncomputable section
open MvPolynomial
variable {k σ:Type*} [lV k]
theorem bmv (J:lI (mD (lJ σ) k)) (d:ℕ×ℕ) :
  (1 :Affine J)∈Oh J d:= by
 refine mem_quotientBidegreeLE.mpr ⟨1,?_,map_one _⟩
 rw [mem_restrictBidegree]
 intro m hm
 obtain rfl :m=0:= by simpa [support_one] using hm
 simp
private theorem bmu {J:lI (mD (lJ σ) k)} {d e :ℕ×ℕ}
  {x y :Affine J} (hx :x∈Oh J d) (hy :y∈Oh J e) :
  x*y∈Oh J (d+e) := by
 obtain ⟨p,hp,rfl⟩:=mem_quotientBidegreeLE.mp hx
 obtain ⟨q,hq,rfl⟩:=mem_quotientBidegreeLE.mp hy
 exact mem_quotientBidegreeLE.mpr ⟨p*q,mul_mem_restrictBidegree hp hq,oj ..⟩
def yH (J:lI (mD (lJ σ) k)) :
    Subalgebra k (yB (Affine J) (ℕ×ℕ)) where
  carrier := {p | ∀ d,p.coeff d∈Oh J d}
  zero_mem' d:=(Oh J d).zero_mem
  add_mem' hx hy d:=(Oh J d).add_mem (hx d) (hy d)
  one_mem' := by
    classical
    intro d
    change (oq 0 1 :yB (Affine J) (ℕ×ℕ)).coeff d∈_
    rw [xI,zR]
    split
    · exact bmv J d
    · exact (Oh J d).zero_mem
  mul_mem' {p q} hp hq:= by
    classical
    intro d
    simp only [AddMonoidAlgebra.coeff_mul,Finsupp.sum]
    refine (Oh J d).sum_mem fun i _=>(Oh J d).sum_mem fun j _ => ?_
    split
    · rename_i h
      rw [← h]
      exact bmu (hp i) (hq j)
    · exact (Oh J d).zero_mem
  algebraMap_mem' c:= by
    classical
    intro d
    change (oq 0 (aU k (Affine J) c)).coeff d∈_
    rw [xI,zR]
    split
    · change lz J (c9 c)∈Oh J d
      refine mem_quotientBidegreeLE.mpr ⟨_,mem_restrictBidegree.mpr fun m hm => ?_,rfl⟩
      obtain rfl :=Finset.mem_singleton.mp (support_C_subset hm)
      simp
    · exact (Oh J d).zero_mem
def dO {J:lI (mD (lJ σ) k)} (d:ℕ×ℕ)
    (x :Affine J) (hx :x∈Oh J d) :yH J :=
  ⟨oq d x,by
    classical
    intro e
    change (oq d x).coeff e∈Oh J e
    rw [xI,zR]
    split
    · rename_i h
      subst e
      exact hx
    · exact (Oh J e).zero_mem⟩
variable (J:lI (mD (lJ σ) k))
def U:yH J:=dO (1,0) 1 (bmv J _)
def V:yH J:=dO (0,1) 1 (bmv J _)
private def byw:lJ σ→ℕ×ℕ
 | none=>(1,0)
 | some _=>(0,1)
private theorem dAh (i:lJ σ) :lz J (cy i) ∈
  Oh J (byw i) := by
 refine mem_quotientBidegreeLE.mpr ⟨cy i,?_,rfl⟩
 rw [mem_restrictBidegree]
 intro m hm
 obtain rfl :m=Finsupp.single i 1 := by simpa only [support_X,Finset.mem_singleton] using hm
 cases i <;> simp [byw,Finsupp.some_single_none,Finsupp.some_single_some]
def coordinate (i:lJ σ) :yH J :=
 dO (byw i) (lz J (cy i)) (dAh J i)
abbrev aAI:yH J:=coordinate J none
def ayB:lI (yH J) :=p7 {U J,aAI J}
@[simp] theorem biu {d:ℕ×ℕ} {x :Affine J} (hx :x∈Oh J d) :
   (yH J).val (dO d x hx)=oq d x :=rfl
private theorem gKL (i:lJ σ) : (yH J).val (coordinate J i) =
 oq (byw i) (lz J (cy i)) :=rfl
private theorem gKM (c:k) : (yH J).val (aU k (yH J) c) =
 oq 0 (lz J (c9 c)) :=rfl
private theorem single_pow (d:ℕ×ℕ) (x :Affine J) (a :ℕ) :
   (oq d x :yB (Affine J) (ℕ×ℕ))^a =
     oq (a•d) (x^a) := by
 induction a with
 | zero=>simp [AddMonoidAlgebra.one_def]
 | succ a ih=>rw [pow_succ,ih,AddMonoidAlgebra.single_mul_single,succ_nsmul,
     pow_succ]
private theorem cbG (u v :ℕ) (m:lJ σ →₀ ℕ) (c:k)
    (hu:m none≤u) (hv :m.some.degree≤v) :
    ∃ (h:lz J (monomial m c)∈Oh J (u,v)),
      dO (u,v) (lz J (monomial m c)) h =
        (U J^(u - m none)*aAI J^m none) *
          (aU k (yH J) c*V J^(v - m.some.degree) *
            m.some.prod (fun i a=>coordinate J (some i)^a)) := by
  classical
  have hm:monomial m c∈restrictBidegree σ k u v := by
    exact mem_restrictBidegree.mpr fun e he=> by
      obtain rfl :=Finset.mem_singleton.mp (support_monomial_subset he)
      exact ⟨hu,hv⟩
  have hinj:p6 (yH J).val :=xu
  refine ⟨mem_quotientBidegreeLE.mpr ⟨_,hm,rfl⟩,hinj ?_⟩
  simp only [Finsupp.prod,oj,u5 ,map_prod,gKM,U,V,aAI,gKL,
    biu,byw,single_pow,AddMonoidAlgebra.prod_single,
    Bf ,one_pow,Prod.smul_mk,nsmul_eq_mul,mul_one,mul_zero,
    p5]
  congr 1
  · have hv' : (∑ i∈m.some.support,m (some i))≤v := by
      simpa [FV] using hv
    ext <;> simp [FV,Prod.fst_sum,Prod.snd_sum,z8 hu,
      z8 hv']
  · rw [monomial_eq,Finsupp.prod_option_index _ _ (by simp) (by intros; rw [pow_add]),
      oj ,oj ,u5 ,Finsupp.prod,map_prod]
    simp only [u5 ]
    ac_rfl
private theorem c34 (u v :ℕ) (p:mD (lJ σ) k)
   (hp:p∈restrictBidegree σ k u v) (m:p.support) :
   lz J (monomial m.val (p.coeff m.val))∈Oh J (u,v) :=
 (cbG J u v m.val _ (mem_restrictBidegree.mp hp _ m.property).1 (mem_restrictBidegree.mp hp _ m.property).2).choose
private theorem c33 (u v :ℕ) (p:mD (lJ σ) k)
   (hp:p∈restrictBidegree σ k u v) :
   dO (u,v) (lz J p) (mem_quotientBidegreeLE.mpr ⟨p,hp,rfl⟩) =
     ∑ m:p.support,dO (u,v) _ (c34 J u v p hp m) := by
 classical
 apply sS
 change (yH J).val (dO (u,v) (lz J p) (mem_quotientBidegreeLE.mpr ⟨p,hp,rfl⟩)) =
   (yH J).val (∑ m:p.support,dO (u,v) _ (c34 J u v p hp m))
 rw [qy]
 change oq (u,v) (lz J p) =
   ∑ m:p.support,oq (u,v)
     (lz J (monomial m.val (p.coeff m.val)))
 rw [Dz p.support (fun m=>oq (u,v)
   (lz J (monomial m (p.coeff m))))]
 simp only [← AddMonoidAlgebra.singleAddHom_apply,← qy ,support_sum_monomial_coeff]
theorem eLe (u v :ℕ) {x :Affine J} (hx :x∈Oh J (u,v)) :
    dO (u,v) x hx∈ayB J^u:= by
  classical
  obtain ⟨p,hp,rfl⟩:=mem_quotientBidegreeLE.mp hx
  rw [c33 J u v p hp]
  refine (ayB J^u).sum_mem fun m _ => ?_
  rw [(cbG J u v m.val _ (mem_restrictBidegree.mp hp _ m.property).1 (mem_restrictBidegree.mp hp _ m.property).2).choose_spec]
  rw [oz (U J^(u - m.val none)*aAI J^m.val none)]
  apply C4
  have hdeg:u - m.val none+m.val none=u:=z8
    (mem_restrictBidegree.mp hp _ m.property).1
  have htwo: (ayB J).IsTwoSided:= by
    constructor
    intro a b ha
    rw [oz a b]
    exact (ayB J).mul_mem_left b ha
  have hpow:ayB J^(u - m.val none)*ayB J^m.val none =
      ayB J^u:=(@Ideal.IsTwoSided.pow_add _ _ (ayB J) htwo _ _).symm.trans
        (oD (fun i:ℕ=>ayB J^i) hdeg)
  rw [← hpow]
  apply Ideal.mul_mem_mul
  · exact Av (vw (by simp :U J ∈ {U J,aAI J})) _
  · exact Av (vw (by simp :aAI J ∈ {U J,aAI J})) _
theorem eLf (e d:ℕ×ℕ) {x :Affine J}
    (hx :x∈Oh J (e+d)) :
    dO (e+d) x hx∈p7 {dO e 1 (bmv J e)} ↔ x∈Oh J d:= by
  constructor
  · intro h
    obtain ⟨r,hr⟩:=Ideal.mem_span_singleton'.mp h
    rw [oz r] at hr
    have hc:=oD (fun z :yH J=>((yH J).val z).coeff (e+d)) hr
    have he : ((yH J).val r).coeff d=x := by
      simpa only [oj,biu,AddMonoidAlgebra.coeff_single_mul_add,p5 ,
        xI,Finsupp.single_eq_same] using hc
    rw [← he]
    exact r.property d
  · intro h
    refine Ideal.mem_span_singleton'.mpr ⟨dO d x h,?_⟩
    rw [oz (dO d x h)]
    apply (show p6 (yH J).val from xu)
    simp only [oj,biu,Bf ,p5]
instance gRG [Finite σ] :yQ (yH J) := by
 classical
 let f :mD (Bool ⊕ lJ σ) k →ₐ[k] yH J :=
   t8 (Sum.elim (fun b=>if b then U J else V J) (coordinate J))
 have hU:U J∈f.range :=⟨cy (.inl true),by simp [f]⟩
 have hV:V J∈f.range :=⟨cy (.inl false),by simp [f]⟩
 have hcoord (i:lJ σ) :coordinate J i∈f.range :=⟨cy (.inr i),by simp [f]⟩
 have hpiece (u v :ℕ) (x :Affine J) (hx :x∈Oh J (u,v)) :
     dO (u,v) x hx∈f.range := by
   obtain ⟨p,hp,rfl⟩:=mem_quotientBidegreeLE.mp hx
   rw [c33 J u v p hp]
   refine f.range.sum_mem fun m _ => ?_
   rw [(cbG J u v m.val _ (mem_restrictBidegree.mp hp _ m.property).1 (mem_restrictBidegree.mp hp _ m.property).2).choose_spec]
   refine f.range.mul_mem (f.range.mul_mem (f.range.pow_mem hU _)
     (f.range.pow_mem (hcoord none) _)) (f.range.mul_mem
     (f.range.mul_mem (f.range.algebraMap_mem _) (f.range.pow_mem hV _)) ?_)
   change (∏ i∈m.val.some.support,coordinate J (some i)^m.val.some i)∈f.range
   exact f.range.prod_mem (f := fun i:σ=>coordinate J (some i)^m.val.some i)
     (fun i _=>f.range.pow_mem (hcoord (some i)) _)
 apply isNoetherianRing_of_surjective _ _ f.toRingHom
 intro p
 change p∈f.range
 suffices p = ∑ d:p.val.coeff.support,dO d.val (p.val.coeff d.val) (p.property d.val) by
   rw [this]
   exact f.range.sum_mem fun d _=>hpiece d.val.1 d.val.2 _ _
 apply sS
 change (yH J).val p=(yH J).val (∑ d:p.val.coeff.support,
   dO d.val (p.val.coeff d.val) (p.property d.val))
 rw [qy]
 change p.val = ∑ d:p.val.coeff.support,oq d.val (p.val.coeff d.val)
 rw [Dz p.val.coeff.support
   (fun d=>oq d (p.val.coeff d))]
 exact (AddMonoidAlgebra.sum_coeff_single p.val).symm
end
end aqf
end
section
namespace aR1
open scoped Polynomial
noncomputable abbrev bgf {F A:Type} [lV F] [ox A] [nq F A]
 (a :A) :nq F[X] A:=(vG (R:=F) a).toRingHom.toAlgebra
end aR1
end
section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
namespace aR1
noncomputable section
open cu DQ Cu akS
open scoped Polynomial TensorProduct
private def bwB (n:ℕ) :N4 n →+* oZ n :=
 (qx some).toRingHom
private def vV (n:ℕ) :e7 n →+* jY n :=
 Df (K:=e7 n) (g:=(aU (oZ n) (jY n)).comp (bwB n))
  ((t5 (oZ n) (jY n)).comp (MvPolynomial.rename_injective _ (Option.some_injective (Fin n))))
def ajU (n:ℕ) : (e7 n)[X] →+* jY n :=
 wY (vV n) (Qd (n:=n) none)
abbrev ami (n:ℕ) :nq (e7 n)[X] (jY n) :=
 (ajU n).toAlgebra
attribute [local instance] ami
local instance (priority :=2000) offsetModule (n:ℕ) :
   Module (e7 n)[X] (jY n) :=
 @zm _ _ _ _ (ami n)
private def aJy (n:ℕ) :oZ n →+* (e7 n)[X] :=
 (wB (aU (N4 n) (e7 n))).comp
   (qJ FX (Fin n)).toRingEquiv.toRingHom
private theorem gtb (n:ℕ) :
   p6 (aJy n) :=
 (Polynomial.map_injective _ (t5 _ _)).comp
   (qJ FX (Fin n)).injective
private theorem eGb (n:ℕ) :
   (ajU n).comp (aJy n)=aU (oZ n) (jY n) := by
 apply oK
 · intro c
   simp [aJy,ajU,vV,bwB,
     nI,t3]
 · intro i
   cases i <;> simp [aJy,ajU,vV,bwB,
     nI,t3 ,Qd]
private def a8C (n:ℕ) :jY n →+* uz (e7 n)[X] :=
 Df (K:=jY n)
  (g:=(aU (e7 n)[X] (uz (e7 n)[X])).comp
    (aJy n))
  ((t5 (e7 n)[X] (uz (e7 n)[X])).comp
    (gtb n))
private theorem eF6 (n:ℕ) :p6 (ajU n) := by
  let m:=aU (e7 n)[X] (uz (e7 n)[X])
  have he : (a8C n).comp (ajU n)=m:= by
    apply yo
    · have hc: (a8C n).comp (vV n)=m.comp Polynomial.C:= by
        apply xW (A:=N4 n)
        intro c
        simp only [nI,vV,t3 ,
          a8C]
        change m (aJy n (qx some c)) =
          m (ov (aU (N4 n) (e7 n) c))
        have h: (qJ FX (Fin n)) (qx some c) =
            Polynomial.C c:= by
          have hcomp: (qJ FX (Fin n)).toAlgHom.comp
              (qx some)=Polynomial.CAlgHom (R:=FX) := by
            apply FU
            intro i
            simp
          exact qz hcomp c
        change m (Polynomial.map (aU (N4 n) (e7 n))
          (qJ FX (Fin n) (qx some c)))= _
        rw [h,zS]
      intro c
      simpa [ajU,nI] using qz hc c
    · simp only [nI,ajU,yl,C5 ,
        Qd,a8C,t3]
      change m (Polynomial.map (aU (N4 n) (e7 n))
        (qJ FX (Fin n) (cy none)))=m pC
      rw [MvPolynomial.optionEquivLeft_X_none,Polynomial.map_X]
  intro x y h
  have h' := oD (a8C n) h
  change ((a8C n).comp (ajU n)) x =
    ((a8C n).comp (ajU n)) y at h'
  rw [he] at h'
  exact t5 (e7 n)[X] (uz (e7 n)[X]) h'
private theorem edO {R E :Type} [ox R] [lV E]
  (f :R →+* E) (hf :p6 f)
  (h : ∀ z :E,∃ x y :R,z=f x/f y) :
  @IsFractionRing R _ E _ f.toAlgebra := by
 let:nq R E :=f.toAlgebra
 let:FaithfulSMul R E :=(faithfulSMul_iff_algebraMap_injective R E).mpr hf
 exact IsFractionRing.of_field R E h
theorem eF7 (n:ℕ) :
  @IsFractionRing (e7 n)[X] _ (jY n) _ (ami n) := by
 apply edO (ajU n) (eF6 n)
 intro x
 obtain ⟨r,s,_,rfl⟩:=IsFractionRing.div_surjective (oZ n) x
 use aJy n r,aJy n s
 change _=((ajU n).comp (aJy n)) r /
  ((ajU n).comp (aJy n)) s
 rw [eGb]
theorem eF1 (n:ℕ) :ajU n pC= Qd (n:=n) none :=
 C5 _ _
private theorem gsD {n:ℕ} (i:Fin n) :
  vV n (aU (N4 n) (e7 n) (cy i)) =
   Qd (some i) := by
 simp [vV,bwB,t3 ,Qd]
private theorem gsC (n:ℕ) (x :FX) :
  vV n (aU FX (e7 n) x)=aU FX (jY n) x := by
 change vV n (aU (N4 n) (e7 n) (c9 x)) =
  aU (oZ n) (jY n) (c9 x)
 simp [vV,bwB,t3]
local instance {n:ℕ} (B:lI (Gc n)) :
  nq (e7 n)[X] (Mb B) :=
 bgf (aoe B)
local instance (priority :=2000) graphModule {n:ℕ} (B:lI (Gc n)) :
   Module (e7 n)[X] (Mb B) :=
 @zm _ _ _ _
   (show nq (e7 n)[X] (Mb B) from bgf (aoe B))
abbrev axw {n:ℕ} (B:lI (Gc n)) :=
 jY n ⊗[(e7 n)[X]] Mb B
private abbrev bnT {n:ℕ} (B:lI (Gc n)) :
   tu B →+* axw B :=
 (wA (A:=jY n)).toRingHom.comp
   (ajy B).toRingHom
private theorem coA {n:ℕ} (B:lI (Gc n)) (c:e7 n) :
   (1 :jY n) ⊗ₜ[(e7 n)[X]] aU (e7 n) (Mb B) c =
     aU (jY n) (axw B) (vV n c) := by
 have h:=zg
   (A:=jY n) (B:=Mb B) (ov c)
 change ajU n (ov c) ⊗ₜ[(e7 n)[X]] (1 :Mb B) =
   1 ⊗ₜ[(e7 n)[X]] vG (aoe B) (ov c) at h
 rw [ajU,yl,Du,Polynomial.aeval_C] at h
 exact h.symm
private abbrev i9 {n:ℕ} (B:lI (Gc n)) :
  lI (mD (Fin 2 ⊕ Fin n) (jY n)) :=
 B.map (n5 (aU FX (jY n))) ⊔ p7 {blL n}
private def aJp {n:ℕ} (B:lI (Gc n)) :
  mD (Fin 2 ⊕ Fin n) (jY n) →ₐ[jY n] axw B :=
 t8 (fun i=>bnT B (lz B (cy i)))
private theorem dco {n:ℕ} (B:lI (Gc n)) :
    (aJp B).toRingHom.comp (n5 (aU FX (jY n))) =
      (bnT B).comp (lz B) := by
  apply oK
  · intro c
    change aJp B (n5 (aU FX (jY n)) (c9 c)) =
      bnT B (lz B (c9 c))
    have hc:lz B (c9 c)=aU FX (tu B) c:=rfl
    rw [wR,hc]
    change aJp B (c9 (aU FX (jY n) c)) =
      (1 :jY n) ⊗ₜ[(e7 n)[X]] ajy B (aU FX (tu B) c)
    have hscalar :ajy B (aU FX (tu B) c) =
        aU (e7 n) (Mb B) (aU FX (e7 n) c) := by
      exact (zg
        (A:=e7 n) (B:=tu B) c).symm
    rw [aJp,zk,hscalar,coA,gsC]
  · intro i
    change aJp B (n5 (aU FX (jY n)) (cy i)) =
      bnT B (lz B (cy i))
    rw [vi]
    exact uJ _ _
private theorem gnt {n:ℕ} (B:lI (Gc n)) :
    aJp B (blL n)=0:= by
  let incl:Mb B →ₐ[(e7 n)[X]] axw B :=
    wA
  have h₀:incl (aoe B) =
      aU (jY n) (axw B) (Qd (n:=n) none) := by
    have h:=zg
      (A:=jY n) (B:=Mb B) (pC: (e7 n)[X])
    change (ajU n pC) ⊗ₜ[(e7 n)[X]] (1 :Mb B) =
      1 ⊗ₜ[(e7 n)[X]] vG (aoe B) pC at h
    rw [eF1,Polynomial.aeval_X] at h
    exact h.symm
  have hi (i:Fin n) :
      incl (aU (e7 n) (Mb B)
        (aU (N4 n) (e7 n) (cy i))) =
      aU (jY n) (axw B) (Qd (some i)) := by
    rw [← gsD i]
    exact coA B _
  simp only [blL,aJp,qG,qy ,oj,
    zk,uJ]
  apply sub_eq_zero.mpr
  rw [← h₀]
  change _=incl (∑ i:Fin n,
    (aU (N4 n) (e7 n) (cy i)) •
      ajy B (lz B (cy (Sum.inr i))))
  rw [qy]
  simp only [Algebra.smul_def,oj,hi]
  rfl
def a8l {n:ℕ} (B:lI (Gc n)) :
    aAM B →ₐ[jY n] axw B :=
  Et (i9 B) (aJp B) <| by
    change i9 B≤pQ (aJp B).toRingHom
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro p hp
      change ((aJp B).toRingHom.comp (n5
       (aU FX (jY n)))) p=0
      rw [dco]
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
    · intro p hp
      obtain rfl :=Set.mem_singleton_iff.mp hp
      exact gnt B
theorem gnB {n:ℕ} (B:lI (Gc n)) :
    Function.Surjective (a8l B) := by
  let f :=a8l B
  let incl:Mb B →ₐ[(e7 n)[X]] axw B :=
    wA
  have hcoord (b:tu B) :bnT B b∈f.range := by
    obtain ⟨p,rfl⟩:=FK b
    refine ⟨lz (i9 B)
      (n5 (aU FX (jY n)) p),?_⟩
    exact qz (dco B) p
  have hincl (x :Mb B) :incl x∈f.range := by
    induction x using Au with
    | add x y hx hy=>rw [map_add]; exact f.range.add_mem hx hy
    | tmul c b =>
      have h: (c ⊗ₜ[FX] b:Mb B) =
          aU (e7 n) (Mb B) c*ajy B b:= by
        change _=(c ⊗ₜ[FX] (1 :tu B))*(1 ⊗ₜ[FX] b)
        simp only [FQ,mul_one,p5]
      rw [h,oj]
      apply f.range.mul_mem _ (hcoord b)
      rw [show incl (aU (e7 n) (Mb B) c)= _ from coA B c]
      exact f.range.algebraMap_mem _
  intro z
  change z∈f.range
  induction z using Au with
  | add x y hx hy=>exact f.range.add_mem hx hy
  | tmul s x =>
    have h: (s ⊗ₜ[(e7 n)[X]] x :axw B) =
        aU (jY n) (axw B) s*incl x := by
      change _=(s ⊗ₜ[(e7 n)[X]] (1 :Mb B)) *
        (1 ⊗ₜ[(e7 n)[X]] x)
      simp only [FQ,mul_one,p5]
    rw [h]
    exact f.range.mul_mem (f.range.algebraMap_mem _) (hincl x)
end
end aR1
end
section
namespace vq
noncomputable section
open K1 cu MN
open scoped Polynomial
private abbrev Dual:=TrivSqZeroExt FX FX
private abbrev incl:=aU L[X] FX
private def a6I:L[X] →+* Dual where
  toFun g:=(incl g,incl g.derivative)
  map_zero' := by apply vZ <;> simp
  map_one' := by apply vZ <;> simp
  map_add' g h:= by
    apply vZ
    · change incl (g+h)=incl g+incl h
      exact t4 _ _ _
    · change incl ((g+h).derivative)=incl g.derivative+incl h.derivative
      rw [t4 ,t4]
  map_mul' g h:= by
    apply vZ
    · change incl (g*h)=incl g*incl h
      exact oj _ _ _
    · change incl ((g*h).derivative) =
        incl g*incl h.derivative+incl g.derivative*incl h
      rw [Polynomial.derivative_mul,t4 ,oj,oj,add_comm]
private theorem eMU (g:L[X]) : (a6I g).fst=incl g:=rfl
private def ar4 :FX →+* Dual :=
  IsLocalization.lift (M:=nonZeroDivisors L[X]) (g:=a6I)
    (fun g=>TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
      (isUnit_iff_ne_zero.mpr (by
        rw [eMU]
        simpa only [oY] using (t5 L[X] FX).ne (mem_nonZeroDivisors_iff_ne_zero.mp g.2))))
private theorem a7v (g:L[X]) :ar4 (incl g)=a6I g:= by
 exact IsLocalization.lift_eq _ _
private theorem c6U (a :FX) : (ar4 a).fst=a := by
 have h: (TrivSqZeroExt.fstHom FX FX FX).toRingHom.comp ar4=z9 FX:= by
  apply IsLocalization.ringHom_ext (nonZeroDivisors L[X])
  apply t6
  intro g
  exact oD TrivSqZeroExt.fst (a7v g)
 exact y5 h a
def Dx :FX →+ FX :=
 (TrivSqZeroExt.sndHom (R:=FX) (M:=FX)).toAddMonoidHom.comp ar4.toAddMonoidHom
theorem apZ (a b:FX) :Dx (a*b)=a*Dx b+Dx a*b:= by
 change (ar4 (a*b)).snd= _
 rw [oj]
 change (ar4 a).fst*Dx b+Dx a*(ar4 b).fst= _
 rw [c6U,c6U]
theorem aYD (g:K[X]) :Dx (kr g)=kr g.derivative := by
 change (ar4 (incl (j9 g))).snd= _
 rw [a7v]
 change incl (j9 g).derivative=incl (j9 g.derivative)
 rw [j9,Polynomial.derivative_map,j9]
private theorem dmT (z :K) :Dx (jz z)=0:= by
 change (ar4 (incl (ov (aU K L z)))).snd= _
 rw [a7v]
 change incl (Polynomial.derivative (ov (aU K L z)))= _
 simp
theorem bzc (a :FX) (n:ℕ) :Dx (a^n)=(n:FX)*a^(n - 1)*Dx a := by
 cases n with
 | zero =>
   change (ar4 (a^0)).snd= _
   simp
 | succ n =>
   induction n with
   | zero=>simp
   | succ n ih =>
     rw [pow_succ a (n+1),apZ,ih]
     push_cast
     simp only [pow_succ a n]
     ring
open MvPolynomial
def D6:Ai →+ Ai :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom Dx).comp AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)
theorem aG6 (P:Ai) (m:lJ (Fin 2) →₀ ℕ) :
 (D6 P).coeff m=Dx (P.coeff m) :=rfl
private theorem cbs (a :FX) :D6 (C a)=C (Dx a) := by
 ext m
 classical
 by_cases h: (0:lJ (Fin 2) →₀ ℕ)=m <;> simp [aG6,coeff_C,h]
private theorem cbt (Q:Ai) (i:lJ (Fin 2)) :
  D6 (Q*cy i)=D6 Q*cy i:= by
 classical
 ext m
 simp only [aG6,coeff_mul_X']
 split <;> simp
theorem aKe (z :K) (S:K[X]) (P:Ai) :
    Dx (eval (Ul z S) P) =
      eval (Ul z S) (D6 P) +
        kr S.derivative*eval (Ul z S) (pderiv none P) := by
  classical
  let ev :=eval (Ul z S)
  change Dx (ev P)=ev (D6 P)+kr S.derivative*ev (pderiv none P)
  induction P using MvPolynomial.induction_on with
  | C a=>simp [ev,cbs]
  | add P Q hP hQ =>
    simp only [t4 ,hP,hQ,mul_add]
    ring
  | mul_X P i hP =>
    have hi:Dx (Ul z S i) =
        kr S.derivative*ev (pderiv none (cy i)) := by
      cases i with
      | none=>simp [Ul,ev,aYD]
      | some j =>
        fin_cases j <;> simp [Ul,ev,pderiv_X,dmT,bzc]
    simp only [oj,apZ,hP,cbt,pderiv_mul,t4]
    rw [show ev (cy i)=Ul z S i by simp [ev],hi]
    ring
end
end vq
end
section
namespace aqf
noncomputable section
private theorem eM6 {R:Type*} [ox R] (a b:R) (p:zc R)
    (h:IsUnit a∨IsUnit b)
    (hp: (ov a-Polynomial.C b*pC)*p=0) :p=0:= by
  rcases h with ha | hb
  · apply zi
    intro n
    simp only [ze]
    induction n with
    | zero =>
        have he :=oD (fun f :zc R=>f.coeff 0) hp
        apply ha.mul_left_inj.mp
        simpa [sub_mul,vh,oz a] using he
    | succ n ih =>
        have he :=oD (fun f :zc R=>f.coeff (n+1)) hp
        apply ha.mul_left_inj.mp
        simpa [sub_mul,vh,Polynomial.coeff_X_mul,ih,oz a] using he
  · obtain ⟨b',hb'⟩:=hb.exists_right_inv
    have he :ov a-Polynomial.C b*pC =
        ov (-b)*(pC-Polynomial.C (b' * a)) := by
      rw [mul_sub,← Polynomial.C_mul,neg_mul,← vh,hb',p5 ,Polynomial.C_neg]
      simp [sub_eq_add_neg,add_comm]
    rw [he,vh] at hp
    exact (Polynomial.monic_X_sub_C (b' * a)).mul_right_eq_zero_iff.mp
      ((IsUnit.mul_right_eq_zero (hb.neg.map ov)).mp hp)
private theorem c3T {R σ:Type*} [ox R] (a b s :R)
   (hs :s=a∨s=b) (p:mD (lJ σ) R)
   (hp: (c9 a-MvPolynomial.C b*cy none)*p=0) :
   ∃ j:ℕ,(c9 s)^j*p=0:= by
 let L:=Localization.Away s
 let g:=n5 (aU R L) (σ:=lJ σ)
 let e :=qJ L σ
 have hu:IsUnit (aU R L a)∨IsUnit (aU R L b) := by
   rcases hs with rfl | rfl
   · exact Or.inl (Cy _)
   · exact Or.inr (Cy _)
 have hh:e (g p)=0:= by
   apply eM6 _ _ _ (hu.imp (fun h=>h.map c9)
     (fun h=>h.map c9))
   simpa [g,e] using oD (fun z=>e (g z)) hp
 have hzero :g p=0:=e.injective (hh.trans (oY e).symm)
 let _:nq (mD (lJ σ) R) (mD (lJ σ) L) :=
   MvPolynomial.algebraMvPolynomial (R:=R) (S:=L)
 have hz :aU (mD (lJ σ) R) (mD (lJ σ) L) p=0:=hzero
 obtain ⟨t,ht⟩:=(IsLocalization.map_eq_zero_iff
   ((Submonoid.powers s).map (c9 (σ:=lJ σ)))
   (mD (lJ σ) L) p).mp hz
 obtain ⟨r,hr,he⟩:=t.property
 obtain ⟨j,rfl⟩:=hr
 refine ⟨j,?_⟩
 rw [← u5 (c9 (σ:=lJ σ)),he]
 exact ht
private theorem c6w {R:Type*} [ox R] [yQ R]
  (T:pU R R) (s :R) (hs : ∀ t∈T,∃ j:ℕ,s^j*t=0) :
  s∈T.annihilator.radical:= by
 let f :Module.End R R:=pz R s
 obtain ⟨n,hn⟩:=monotone_stabilizes_iff_noetherian.mpr inferInstance f.iterateKer
 refine Ideal.mem_radical_iff.mpr ⟨n,Submodule.mem_annihilator.mpr fun t ht => ?_⟩
 obtain ⟨j,hj⟩:=hs t ht
 have hm:t∈vk (f^(n+j)) := by
  simp [LinearMap.mem_ker,f,Gj,pow_add,hj]
 have he :vk (f^n)=vk (f^(n+j)) :=
  hn (n+j) (vl n j)
 rw [← he] at hm
 simpa [f,Gj,smul_eq_mul] using hm
theorem emQ {R σ:Type*} [ox R] [yQ R] [Finite σ] (a b:R) :
   ∃ N :ℕ,∀ p∈(p7 {c9 a,c9 b} :
     lI (mD (lJ σ) R))^N,
     (c9 a-MvPolynomial.C b*cy none)*p=0→p=0:= by
 let Q:=mD (lJ σ) R
 let I:lI Q:=p7 {c9 a,c9 b}
 let q:Q:=c9 a-MvPolynomial.C b*cy none
 let T:pU Q Q:=vk (pz Q q)
 have hi:I≤T.annihilator.radical:= by
   apply Ideal.span_le.mpr
   intro s hs
   rcases (show s=c9 a∨s=c9 b from by simpa using hs) with rfl | rfl
   · exact c6w T _ fun p hp=>c3T a b a (Or.inl rfl) p hp
   · exact c6w T _ fun p hp=>c3T a b b (Or.inr rfl) p hp
 obtain ⟨l,hl⟩:=Ideal.exists_pow_le_of_le_radical_of_fg hi (IsNoetherian.noetherian I)
 obtain ⟨k,hk⟩:=I.exists_pow_inf_eq_pow_smul T
 refine ⟨k+l,fun p hp hqp => ?_⟩
 have hsmul :p∈I ^(k+l)•(⊤ : pU Q Q) := by
   simpa [Ideal.smul_eq_mul] using hp
 have hmem:p∈I ^(k+l)•(⊤ : pU Q Q) ⊓ T:=⟨hsmul,hqp⟩
 rw [hk _ (vl k l),Nat.add_sub_cancel_left] at hmem
 have hs :I ^l•(I ^k•(⊤ : pU Q Q) ⊓ T)≤(⊥ : pU Q Q) :=
   Submodule.smul_le.mpr fun s hs x hx=>(Dw Q).mpr
     (Submodule.mem_annihilator.mp (hl hs) x hx.2)
 exact (Dw Q).mp (hs hmem)
end
end aqf
end
section
namespace czs
noncomputable section
open K1 cu gT Cu UI
open scoped Polynomial
private theorem fWV {k F E :Type} [lV k] [lV F] [lV E]
   [nq k F] (f :F →+* E) (V:yJ E) (c:k →+* V)
   (hc : ∀ b,(c b:E)=f (aU k F b))
   {t d:F} (ht:v9 k (fun _:Unit=>t))
   (hd:d≠0) (u:V) (hu: (u:E)=f d) (hu0:nX V u=0)
   (a :F) (x :V) (hx : (x :E)=f a) :
   letI:nq k (zE V) :=
     ((nX V).comp c).toAlgebra
   IsAlgebraic k (nX V x) := by
 classical
 let res :=nX V
 let _:nq k (zE V) :=(res.comp c).toAlgebra
 by_contra htr
 have hres (q:k[X]) (hq:q≠0) :res (q.eval₂ c x)≠0:= by
   rw [th]
   exact fun h=>hq ((transcendental_iff.mp htr) q h)
 have hinc:V.toSubring.subtype.comp c=f.comp (aU k F) :=
   t6 hc
 have hval (q:k[X]) :
     V.toSubring.subtype (q.eval₂ c x)=f (vG a q) := by
   rw [th,hinc,show V.toSubring.subtype x=f a from hx,
     Polynomial.aeval_def,th]
 have ha :Transcendental k a :=transcendental_iff.mpr fun q hq=> by
   by_contra hq0
   have he :q.eval₂ c x=0:= by
     apply V.toSubring.subtype_injective
     rw [hval,hq,oY ,oY]
   exact hres q hq0 (by rw [he,oY])
 have haBasis :v9 k (fun _:Unit=>a) :=
   ((algebraicIndependent_singleton_iff ()).mpr ha).isTranscendenceBasis_of_trdeg_le_of_finite
     ht.cardinalMk_eq_trdeg.ge
 let A:=Algebra.adjoin k (Set.range (fun _:Unit=>a))
 have halg:EP A F:=haBasis.isAlgebraic
 have hrange :Set.range (fun _:Unit=>a) = {a} := by simp
 let v :=V.valuation.comap f
 let _:v.IsTrivialOn A:= by
   constructor
   intro b hb
   have hmem: (b:F)∈Algebra.adjoin k ({a} : Set F) := by
     rw [← hrange]
     exact b.property
   obtain ⟨q,hq⟩:=Algebra.adjoin_mem_exists_aeval k a hmem
   have hq0:q≠0:= by
     intro h
     apply hb
     apply sS
     simpa [h] using hq.symm
   have hunit :=(yU (q.eval₂ c x)).mp (hres q hq0)
   change V.valuation (f (b:F))=1
   rw [← hq,← hval]
   exact (V.valuation_eq_one_iff _).mp hunit
 have hdv :v d≠1 := by
   intro h
   have he :V.valuation (u:E)=1 := by
     rw [hu]
     exact h
   exact (yU u).mpr
     ((V.valuation_eq_one_iff u).mpr he) hu0
 exact (v.transcendental_of_ne_one _ d hd hdv) (halg.isAlgebraic d)
private theorem fWT {k E :Type} [lV k] [IsAlgClosed k] [lV E]
  [nq k E] {x :E} (hx :IsAlgebraic k x) : ∃ b:k,x=aU k E b:= by
 let A:=IntermediateField.adjoin k ({x} : Set E)
 let _:EP k A:=IntermediateField.isAlgebraic_adjoin_simple hx.isIntegral
 have hA:A = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic A
 have hxA:x∈A:=IntermediateField.subset_adjoin k _ (Eg x)
 rw [hA] at hxA
 obtain ⟨b,hb⟩:=IntermediateField.mem_bot.mp hxA
 exact ⟨b,hb.symm⟩
variable {C₀:sQ} [Fact (qM C₀)] {J:lI kM} {g:ℕ}
variable {R:wJ C₀ J g} {z :K} {S:K[X]} (M:akV R z S)
private theorem cTK (b:L) :
  (M.constant b:EC R)=LW R (zT C₀ b) := by
 change (M.V.toSubring.subtype.comp M.Aw) (c9 (aU L FX b))= _
 rw [M.generic_eq]
 simp only [UI.ek,nI,LG,v8 ,
  AdjoinRoot.mk_C]
 change vj (K8 R) (Mr C₀ (aU L FX b))= _
 unfold LW
 rw [nI]
 congr 1
 rw [qm L L[X] FX]
 unfold Mr t9
 rw [uW]
 simp [Mu,F5]
private def aQc (i:Fin 2) :kM :=
 cy (p9 (by decide :2≤3) i)
private theorem efM (i:Fin 2) :
  (M.Aw (aQc i) :EC R)=LW R (Wt C₀ i) := by
 change (M.V.toSubring.subtype.comp M.Aw) (aQc i)= _
 rw [M.generic_eq]
 fin_cases i <;> simp [aQc,UI.ek,LG,LW]
private def b8O (z :K) (i:Fin 2) :L :=
 ![aU K L z,(aU K L z)^p] i
private theorem gn5 (z :K) :
  jz z=aU L FX (aU K L z) := by
 rw [qm L L[X] FX]
 rfl
private theorem ezx (a :L) (e :ℕ) (y :FX) (i:Fin 2) :
   (![aU L FX a,(aU L FX a)^e,y] :Fin 3→FX)
     (p9 (by decide :2≤3) i)=aU L FX (![a,a^e] i) := by
 fin_cases i
 · rfl
 · exact (u5 (aU L FX) a e).symm
private theorem ezC (i:Fin 2) :
   nX M.V (M.Aw (aQc i)) =
     nX M.V (M.constant (b8O z i)) := by
 change ((nX M.V).comp M.Aw) (aQc i)= _
 rw [M.marked_eq]
 simp only [aQc,nI,aEE,zf]
 change nX M.V (M.fx (![jz z,(jz z)^p,kr S]
   (p9 (by decide :2≤3) i))) =
   nX M.V (M.fx (aU L FX (b8O z i)))
 rw [gn5,ezx]
 rfl
theorem proof :UI.c2 := by
 intro C₀ _ J g R z S M i
 let _:nq L (oO C₀) :=(zT C₀).toAlgebra
 intro hi a ha
 let t:=Wt C₀ i
 let b:=b8O z i
 let d:=t - aU L (oO C₀) b
 have hd:d≠0:= by
  have htr :Transcendental L t:=hi.1.transcendental ()
  intro h
  refine htr ⟨pC-Polynomial.C b,Polynomial.X_sub_C_ne_zero b,?_⟩
  simpa using h
 let u:M.V:=M.Aw (aQc i)-M.constant b
 have hu: (u:EC R)=LW R d:= by
  change (M.Aw (aQc i) :EC R)-(M.constant b:EC R)= _
  simp only [efM,cTK,d,t,qG]
  rfl
 have hu0:nX M.V u=0:= by
  change nX M.V (M.Aw (aQc i)-M.constant b)=0
  rw [qG,ezC,sub_self]
 let x :M.V:=⟨LW R a,ha⟩
 let _:nq L (zE M.V) :=
  ((nX M.V).comp M.constant).toAlgebra
 have hx :=fWV (LW R) M.V M.constant (cTK M)
  hi hd u hu hu0 a x rfl
 exact fWT hx
end
end czs
end
