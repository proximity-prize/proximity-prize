import ProximityPrize.SubmissionLower.C
import ProximityPrize.SubmissionLower.B4
import ProximityPrize.SubmissionLower.AB
set_option Elab.async false
open _root_ renaming Algebra.algebraMap→xL,CommRing→zc,DFunLike.congr_fun→vl,Fin.last→aU,Fin.sum_univ_eq_sum_range→KA,Fin.sum_univ_three→EK,Fin.sum_univ_two→zi,Fin.val→ oj,Finset→ oz,Finset.card_le_card→xW,Finset.filter_subset→FK,Finset.mem_univ→u9,Finset.mul_sum→sH,Finset.prod_mul_distrib→KH,Finset.prod_pow_eq_pow_sum→JW,Finset.range→t3,Finset.sum_add_distrib→vi,Finset.sum_congr→pQ,Finset.sum_const→Ef,Finset.sum_eq_single_of_mem→LR,Finset.sum_eq_zero→y5,Finset.sum_le_sum→yQ,Finset.sum_mul→vk,Finset.sup_le_iff→JM,Finsupp.degree_apply→Mk,Finsupp.degree_eq_sum→ In,Finsupp.single→uh,Finsupp.weight→qM,Finsupp.weight_single→FQ,Fintype.card→Bf,Function.Injective→sS,Ideal→uz,Ideal.Quotient.mk→pU,Ideal.Quotient.mkₐ→GF,Ideal.kerLiftAlg_injective→Mw,Ideal.span→G2,Ideal.span_singleton_prime→Mz,IsFractionRing.injective→GR,IsLocalization.Away.algebraMap_isUnit→G7,IsScalarTower.toAlgHom→HZ,KoalaBear.Field→C9,LinearMap.finrank_le_finrank_of_injective→FU,LinearMap.ker→Eg,LinearMap.mulLeft→G4,Matrix.blockDiagonal'→z7,Matrix.blockDiagonal'_apply_eq→KI,Matrix.blockDiagonal'_apply_ne→ Iw,Matrix.rank_eq_finrank_span_cols→G5
open _root_ renaming Matrix.rank_submatrix_le→G9,Module.finrank→qJ,MulZeroClass.mul_zero→zf,MulZeroClass.zero_mul→uW,Multiset.toFinset_prod_dvd_prod→Kv,MvPolynomial→u5,MvPolynomial.C→ ov,MvPolynomial.X→c9,MvPolynomial.aeval→qm,MvPolynomial.aeval_eq_eval→Gr,MvPolynomial.affineDegree→ ox,MvPolynomial.affineHilbertPolynomial→pL,MvPolynomial.algHom_ext→LQ,MvPolynomial.coeff_C_mul→Dw,MvPolynomial.coeff_homogeneousComponent→ IT,MvPolynomial.coeff_map→Aa,MvPolynomial.coeff_monomial→Dz,MvPolynomial.eval→cy,MvPolynomial.eval_map→LP,MvPolynomial.eval₂→t9,MvPolynomial.eval₂Hom→u8,MvPolynomial.eval₂Hom_monomial→ II,MvPolynomial.eval₂_comp→G8,MvPolynomial.hom_eval₂→JK,MvPolynomial.homogeneousComponent→Du,MvPolynomial.le_weightedTotalDegree→Ee,MvPolynomial.map→lV,MvPolynomial.mem_support_iff→GB,MvPolynomial.monomial→qU,MvPolynomial.optionEquivLeft→Gj,MvPolynomial.optionEquivRight→G1,MvPolynomial.pderiv→pC,MvPolynomial.pderiv_eq_zero_of_degreeOf_eq_zero→Mj,MvPolynomial.pderiv_mul→Fa,MvPolynomial.restrictWeightedDegree→zR,MvPolynomial.ringHom_ext→Ar,MvPolynomial.weightedTotalDegree→Au,MvPolynomial.weightedTotalDegree_le_of_dvd→Fz,MvPolynomial.weightedTotalDegree_one→zS,MvPolynomial.weightedTotalDegree_piSingle→t4,MvPolynomial.weightedTotalDegree_prod→J4,MvPolynomial.zeroLocus→qy,Nat.add_assoc→FR,Nat.add_comm→ze,Nat.add_le_add→v8,Nat.add_le_add_left→x7,Nat.add_le_add_right→C4,Nat.add_mul→z9
open _root_ renaming Nat.add_sub_cancel→G6,Nat.cast_nonneg→zh,Nat.cast_sub→wY,Nat.eq_zero_of_le_zero→Kl,Nat.exists_eq_add_of_le→JQ,Nat.le_add_right→yl,Nat.le_of_lt_succ→wR,Nat.mul_comm→zE,Nat.mul_le_mul_left→ oY,Nat.sub_add_cancel→G0,Nat.sub_le_sub_right→v9,Nat.sub_pos_of_lt→Ml,Option→t6,Pi.single→vw,Polynomial→yJ,Polynomial.Bivariate.swap→zk,Polynomial.C→lJ,Polynomial.X→nX,Polynomial.X_pow_dvd_taylor_iff_X_sub_C_pow_dvd→Lf,Polynomial.coeff_C_mul_X_pow→Kz,Polynomial.coeff_eq_zero_of_natDegree_lt→ IU,Polynomial.coeff_map→zm,Polynomial.derivative→pz,Polynomial.evalRingHom→qz,Polynomial.hasseDeriv→vZ,Polynomial.induction_on'→Hw,Polynomial.natDegree_lt_iff_degree_lt→Ea,PolynomialDifferential.DifferentialPolynomial→qx,PolynomialDifferential.TaylorExponentSufficient→Et,PolynomialDifferential.degreeOf_initialJetSeparant_le→Gn,PolynomialDifferential.differentialSpecialization→ oZ,PolynomialDifferential.rationalTaylorNumerator→F9,PolynomialDifferential.rationalTaylorPolynomial→yo,PolynomialDifferential.universalTaylorResidual→FV,ProximityPrize.Benchmark.IRSProfile.card_index→Kp,ReedSolomon.HiddenDerivative.LocalPolynomial→xu,ReedSolomon.HiddenDerivative.SourceColumn.polynomial_eq_sourceMonomial→Gk,ReedSolomon.HiddenDerivative.localConstraintMatrix→vh,ReedSolomon.HiddenDerivative.localT→nI,ReedSolomon.HiddenDerivative.localY→ oK,ReedSolomon.HiddenDerivative.sourceMonomial→wB,ReedSolomon.HiddenDerivative.unscaledLocalSubstitution→GY,RingHom.ext→Dv,RingHom.id→G3,Set.range→Df,Sigma→t5,StrongNormalizationMonoid→LO,Submodule→zg
open _root_ renaming Submodule.finrank_mono→ Il,Submodule.span→z8,Submodule.sum_mem→Gi,Subtype.ext→xm,Subtype.val→uJ,UniqueFactorizationMonoid.normalizedFactors→yB,UniqueFactorizationMonoid.strongNormalizationMonoid→Kh,add_le_add→Av,add_zero→xI,congrArg→ oD,congrFun→wA,i4.Chart→nq,i4.Family→vj,i4.Source→lz,i4.center→lI,i4.column→ oy,i4.embed→ oq,i4.errors→p7,i4.indexWeight→Cy,ite_eq_left→Kc,ite_eq_right→yL,jA.Lower→p5,jA.translate→n5,le_rfl→th,map_add→qG,map_mul→mD,map_pow→pG,map_prod→yU,map_sum→zd,map_zero→p6,mul_assoc→vG,mul_comm→p9,mul_le_mul_of_nonneg_left→t8,mul_nonneg→vH,one_mul→sI,smul_eq_mul→C5,sub_eq_zero→EP,zero_add→t7
set_option autoImplicit true
section
namespace i4
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
theorem cqa (A:ℕ) (s :lz) (hs :Rz s)
   (hw:s.m≤ s.m*A-N*s.B) :
   Bf (apU A s)+N*(∑ j∈s.E,j.q) =
     s.m*A*s.E.card + ∑ j∈s.E,j.v := by
 classical
 have hbase :N*s.B≤ s.m*A:= by have :=hs.multiplicity; omega
 have hone (j:Jet) (hj:j∈s.E) :
     width A s j+N*j.q=s.m*A+j.v := by
   have h:=(oY N (hs.support j hj).1).trans hbase
   unfold width
   omega
 rw [Fintype.card_sigma]
 simp only [Fintype.card_fin,Finset.sum_coe_sort]
 rw [sH,← vi]
 calc
   _ = ∑ j∈s.E,(s.m*A+j.v) :=pQ rfl hone
   _ = _:= by rw [vi ,Ef ,C5 ,p9 s.E.card]
private theorem bYf (A:ℕ) (s :lz) :sS (oy A s) := by
 rintro ⟨⟨⟨c,b,a⟩,hj⟩,x⟩ ⟨⟨⟨c',b',a'⟩,hj'⟩,x'⟩ he
 have hc:c=c' := oD (fun z :SourceColumn 2=>z.higher 1) he
 have hb:b=b' := oD (fun z :SourceColumn 2=>z.higher 0) he
 have ha :a=a' := oD SourceColumn.y₀ he
 subst c'; subst b'; subst a'
 have hx :x.val=x'.val :=oD SourceColumn.x he
 rw [Fin.ext hx]
theorem interpolant {A:ℕ} {s :lz} (hs :Rz s)
   (hw:s.m≤ s.m*A-N*s.B) (w:Node→K)
   (hr :Vv A s w<Bf (apU A s)) :
   ∃ Q:qx K 2,ato s Q ∧
     differentialWeightedDegree N Q<s.m*A ∧
     ∀ i,SatisfiesLocalConstraints s.m (node i) (w i) Q:= by
 classical
 let cols :=oy A s
 let M:=vh s.m (fun i=>node i) w cols
 have hdep : ¬ LinearIndependent K M.col:= by
   intro hi
   have he :M.rank=Bf (apU A s) :=
     M.rank_eq_finrank_span_cols.trans (finrank_span_eq_card hi)
   exact (Nat.ne_of_lt hr) he
 obtain ⟨v,hv,j,hj⟩:=Fintype.not_linearIndependent_iff.mp hdep
 let Q:=SourceColumn.interpolant cols v
 have hQ:Q≠0:= fun hz=>hj (wA ((SourceColumn.interpolant_eq_zero_iff
   (bYf A s)).mp hz) j)
 have hker :M.mulVec v=0:= by
   funext row
   have h:=wA hv row
   simpa only [Matrix.mulVec,dotProduct,Finset.sum_apply,Pi.smul_apply,
     C5 ,Pi.zero_apply,p9,Matrix.col_apply] using h
 have hlocal:=(localConstraintMatrix_mulVec_eq_zero_iff _ _ _ _ _).mp hker
 have hbase :N*s.B≤ s.m*A:= by have :=hs.multiplicity; omega
 have hpos :0<s.m*A:= by have :=hs.multiplicity; omega
 have hsupp (u) (hu:u∈Q.support) : ∃ i,u=(cols i).exponent:= by
   apply amZ.ef8 (G3 K) cols v u
   simpa only [MvPolynomial.map_id] using hu
 have ht:jetTotalDegree Q≤ s.B:= by
   apply (jetTotalDegree_le_iff _ _).mpr
   intro u hu
   obtain ⟨i,rfl⟩:=hsupp u hu
   simpa [cols,oy ,Jet.q,zi ,FR] using (hs.support _ i.1.property).1
 have hi:Q.weightedTotalDegree Cy≤ s.J:= by
   apply Finset.sup_le
   intro u hu
   obtain ⟨i,rfl⟩:=hsupp u hu
   simpa [cols,oy ,Cy ,SourceColumn.weight_exponent,zi ,
     Jet.v,zE] using (hs.support _ i.1.property).2.1
 have hc:jetDegree Q (aU 2)≤ s.C:= by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro u hu
   obtain ⟨i,rfl⟩:=hsupp u hu
   change (cols i).exponent (some (1 :Fin 2).succ)≤ s.C
   rw [SourceColumn.exponent_succ]
   exact (hs.support _ i.1.property).2.2
 refine ⟨Q,⟨hQ,ht,hi,hc⟩,?_,hlocal⟩
 apply (Finset.sup_lt_iff hpos).mpr
 intro u hu
 obtain ⟨i,rfl⟩:=hsupp u hu
 have hx :=i.2.isLt
 have hq:=(oY N (hs.support _ i.1.property).1).trans hbase
 simp only [width,Jet.q,Jet.v,N] at hx hq
 rw [SourceColumn.weight_exponent]
 simp [cols,oy ,differentialWeight,zi ,N]
 omega
theorem specializes {A:ℕ} {s :lz} {w:Node→K} {Q:qx K 2}
   (hwt:differentialWeightedDegree N Q<s.m*A)
   (hlocal : ∀ i,SatisfiesLocalConstraints s.m (node i) (w i) Q) :
   ∀ f∈close A w,oZ Q f=0:= by
 intro f hf
 have hd:f.natDegree≤N := by
   by_cases hz :f=0
   · simp [hz]
   · have h:=(Ea hz).2 hf.1
     exact wR h
 let lg:=ReedSolomon.polynomialAgreementSet node w f
 apply differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
   node w lg hwt (fun i _=>hlocal i) f hd node.injective.injOn hf.2
 intro i hi
 exact (Finset.mem_filter.mp hi).2
end
end i4
end
section
namespace i4
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark
open private aDW from ProximityPrize.SubmissionLower.ZgdIx1d
open private azg from ProximityPrize.SubmissionLower.B4
theorem Wq {A:ℕ} {w:Node→K} {T:oz K[X]}
    (h: (T:Set K[X])⊆close A w) (hA:aRk A) (cap:ℕ)
    (hsection : ∀ i:Node,(∃ γ∈T,γ.eval (node i)≠w i) →
      (T.filter fun γ=>γ.eval (node i)=w i).card≤ cap) :
    (gap A)*T.card≤p7 A*cap+(gap A) := by
  classical
  have hd:=hA.gt_degree
  have hn:=hA.lt_length
  by_cases hm:T.card≤1
  · have hb:=oY (gap A) hm
    simp only [Nat.mul_one] at hb
    omega
  let lg (γ:K[X]) :oz Node :=univ.filter fun i=>γ.eval (node i)=w i
  let common :oz Node :=univ.filter fun i => ∀ γ∈T,γ.eval (node i)=w i
  let nodes :oz Node :=univ \ common
  have common_le (γ:K[X]) (hγ:γ∈T) :common⊆lg γ:= by
    intro i hi
    exact mem_filter.mpr ⟨u9 _,(mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ:K[X]) (hγ:γ∈T) :A≤(lg γ).card:= by
    exact (h hγ).2
  have degree (a :K[X]) (ha :a∈T) :a.natDegree≤N := by
    by_cases hz :a=0
    · simp [hz]
    · have hdeg:=(Ea hz).2 (h ha).1
      exact wR hdeg
  have pair_count (a :K[X]) (ha :a∈T) (b:K[X]) (hb:b∈T) (hab:a≠b) :
      (lg a∩lg b).card≤N := by
    refine (gR.kL.agd node node.injective
      (a-b) (sub_ne_zero.mpr hab) _ ?_).trans
      ((natDegree_sub_le _ _).trans (max_le (degree a ha) (degree b hb)))
    intro i hi
    change (a-b).eval (node i)=0
    rw [eval_sub,(mem_filter.mp (mem_inter.mp hi).1).2,(mem_filter.mp (mem_inter.mp hi).2).2,
      sub_self]
  obtain ⟨a,ha,b,hb,hab⟩:=one_lt_card.mp (by omega :1<T.card)
  have hcommon :common.card≤N :=
    (xW (subset_inter (common_le a ha) (common_le b hb))).trans
      (pair_count a ha b hb hab)
  let x :=A - common.card
  let t:=N - common.card
  have ht:t=x-(gap A) := by dsimp [t,x,gap]; omega
  have hx :gap A≤x := by dsimp [x,gap]; omega
  have hnodes :nodes.card=x + p7 A:= by
    rw [card_sdiff_of_subset (subset_univ common),card_univ,Kp]
    change n - common.card=(A-common.card)+(n-A)
    have hbound:=hcommon.trans hd.le
    omega
  have exists_trim (γ:K[X]) : ∃ B:oz Node,γ∈T→B⊆lg γ \ common∧B.card=x := by
    by_cases hγ:γ∈T
    · have hc:=hit_count γ hγ
      have hsize :x≤(lg γ \ common).card:= by
        rw [card_sdiff_of_subset (common_le γ hγ)]
        dsimp [x]
        omega
      obtain ⟨B,hB,hcard⟩:=exists_subset_card_eq hsize
      exact ⟨B,fun _=>⟨hB,hcard⟩⟩
    · exact ⟨∅,fun h=>(hγ h).elim⟩
  choose B hB using exists_trim
  have into_nodes (γ:K[X]) (hγ:γ∈T) :B γ⊆nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨u9 _,(mem_sdiff.mp ((hB γ hγ).1 hi)).2⟩
  have overlap (a :K[X]) (ha :a∈T) (b:K[X]) (hb:b∈T) (hab:a≠b) :
      (B a∩B b).card≤t:= by
    have cover : (B a∩B b)∪common⊆lg a∩lg b:= by
      intro i hi
      rcases mem_union.mp hi with hi | hi
      · exact mem_inter.mpr ⟨(mem_sdiff.mp ((hB a ha).1 (mem_inter.mp hi).1)).1,
          (mem_sdiff.mp ((hB b hb).1 (mem_inter.mp hi).2)).1⟩
      · exact mem_inter.mpr ⟨common_le a ha hi,common_le b hb hi⟩
    have disj:Disjoint (B a∩B b) common :=disjoint_left.mpr fun i hi hi' =>
      (mem_sdiff.mp (into_nodes a ha (mem_inter.mp hi).1)).2 hi'
    have hc:=(xW cover).trans (pair_count a ha b hb hab)
    rw [card_union_of_disjoint disj] at hc
    dsimp [t]
    omega
  have occ_le (i:Node) (hi:i∈nodes) : (T.filter fun γ=>i∈B γ).card≤ cap:= by
    have proper : ∃ γ∈T,γ.eval (node i)≠w i:= by
      by_contra! hc
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨u9 _,hc⟩)
    refine (xW ?_).trans (hsection i proper)
    intro γ hγ
    obtain ⟨hγ,hi⟩:=mem_filter.mp hγ
    exact mem_filter.mpr ⟨hγ,(mem_filter.mp (mem_sdiff.mp ((hB γ hγ).1 hi)).1).2⟩
  obtain ⟨second,first⟩:=aDW T nodes B x t cap
    (fun γ hγ=>⟨into_nodes γ hγ,(hB γ hγ).2⟩) overlap occ_le
  rw [hnodes,ht] at second
  rw [hnodes] at first
  exact azg (p7 A) _ _ _ _ (by omega) (Ml hd) hx (Ml hn) second first
end
end i4
end
section
namespace i4
noncomputable section
open Finset MvPolynomial
open scoped Polynomial BigOperators
open private aM6 from ProximityPrize.SubmissionLower.Z3EWiUc
private def VA (x a :K) :jo :=
 (∑ i:Fin k,C (oq x^i.val)*c9 i) - C (oq a)
private theorem aQ5 (x a :K) : (VA x a).totalDegree≤1 := by
 apply (totalDegree_sub_C_le _ _).trans
 apply totalDegree_finsetSum_le
 intro i _
 simpa only [totalDegree_C,totalDegree_X,t7] using
  (totalDegree_mul (C (oq x^i.val)) (c9 i))
private theorem b9D {f :K[X]} (h:f.degree<k) :f.natDegree<k := by
 by_cases hz :f=0
 · rw [hz,Polynomial.natDegree_zero]
   exact Nat.zero_lt_succ _
 · exact (Ea hz).2 h
private theorem aFp {f :K[X]} (h:f.degree<k) (x a :K) :
   qm (Gp f) (VA x a)=0↔f.eval x=a := by
 have heval :f.eval x = ∑ j:Fin k,f.coeff j.val*x^j.val := by
   rw [KA (fun j=>f.coeff j*x^j)]
   exact Polynomial.eval_eq_sum_range' (b9D h) x
 have hmap :oq (∑ j:Fin k,f.coeff j.val*x^j.val) =
     ∑ j:Fin k,oq x^j.val*oq (f.coeff j.val) := by
   rw [zd]
   exact pQ rfl fun _ _=> by rw [mD,pG,p9]
 simp only [VA,Gp,map_sub,zd ,mD,aeval_C,aeval_X,EP ,
   Algebra.algebraMap_self_apply]
 rw [heval,← hmap]
 exact embed.injective.eq_iff
private theorem bXE {A w} {Γ:oz K[X]} (h: (Γ:Set K[X])⊆close A w) :
   Set.InjOn Gp (Γ:Set K[X]) := by
 intro f hf g hg heq
 apply Polynomial.ext
 intro j
 by_cases hj:j<k
 · exact embed.injective (wA heq ⟨j,hj⟩)
 · have hfj:=(b9D (h hf).1).trans_le (Nat.le_of_not_gt hj)
   have hgj:=(b9D (h hg).1).trans_le (Nat.le_of_not_gt hj)
   rw [IU hfj,IU hgj]
private theorem cw2 {A w} {Γ:oz K[X]} (h: (Γ:Set K[X])⊆close A w) (P:uz jo)
  (hdim: (pL P).natDegree=0)
  (hpoints : ∀ γ∈Γ,Gp γ∈qy nU P) :
  (Γ.card:ℚ)≤ox P:= by
 classical
 let A:=Γ.image (Gp)
 have hA:A.card=Γ.card:=card_image_of_injOn (bXE h)
 have hsub: (A:Set _)⊆qy nU P:= by
  intro y hy
  obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hy
  exact hpoints γ hγ
 obtain ⟨hfinite,hdegree⟩ :=
  finite_zeroLocus_and_ncard_le_affineDegree (K:=nU) P hdim
 have hn:=Set.ncard_le_ncard hsub hfinite
 rw [Set.ncard_coe_finset,hA] at hn
 exact (Nat.cast_le.mpr hn).trans hdegree
private theorem bv5 {A w} {Γ:oz K[X]} (h: (Γ:Set K[X])⊆close A w) {P:uz jo}
    (hP:P.IsPrime) (hpoints : ∀ γ∈Γ,Gp γ∈qy nU P)
    (x a :K) (hmiss : ∃ γ∈Γ,γ.eval x≠a)
    {c:ℚ} (hc:0≤ c)
    (bound : ∀ (V:oz K[X]),V⊆Γ → ∀ (Q:uz jo),Q.IsPrime →
      (pL Q).natDegree+1=(pL P).natDegree →
      (∀ γ∈V,Gp γ∈qy nU Q) →
      (V.card:ℚ)≤ c*ox Q) :
    ((Γ.filter fun γ=>γ.eval x=a).card:ℚ)≤ c*ox P:= by
  classical
  let prime :=hP
  let cut:=VA x a
  let Ps :=(P ⊔ G2 {cut}).minimalPrimesFinset
  let U:=Γ.filter fun γ=>γ.eval x=a
  let part (Q:uz jo) :=U.filter fun f=>Gp f∈qy nU Q
  have hproper :cut∉P:= by
    obtain ⟨γ,hγ,hv⟩:=hmiss
    intro hm
    exact hv ((aFp (h hγ).1 x a).mp (hpoints γ hγ _ hm))
  have hcover :U⊆Ps.biUnion part:= by
    intro γ hγ
    obtain ⟨hγΓ,hv⟩:=mem_filter.mp hγ
    have hp:Gp γ∈qy nU (P ⊔ G2 {cut}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr
        ⟨hpoints γ hγΓ,(aFp (h hγΓ).1 x a).mpr hv⟩
    obtain ⟨Q,hQ,hγQ⟩:=exists_retainedMinimalPrime_of_mem_zeroLocus _ 1 _ hp (by simp)
    exact mem_biUnion.mpr ⟨Q,Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,
      mem_filter.mpr ⟨hγ,hγQ⟩⟩
  have hsum:U.card ≤ ∑ Q∈Ps,(part Q).card :=
    (xW hcover).trans card_biUnion_le
  have hdeg: (∑ Q∈Ps,ox Q)≤ox P:= by
    simpa only [Ps,Nat.cast_one,sI] using
      principalCut_sum_affineDegree_minimalPrimes_le hproper (aQ5 x a)
  change (U.card:ℚ)≤ c*ox P
  calc
    _ ≤ ∑ Q∈Ps,((part Q).card:ℚ) := by exact_mod_cast hsum
    _ ≤ ∑ Q∈Ps,c*ox Q:= by
      apply yQ
      intro Q hQ
      have hmin:=Ideal.mem_minimalPrimesFinset.mp hQ
      exact bound _ ((FK _ _).trans (FK _ _)) Q hmin.isPrime
        (principalCut_natDegree_affineHilbertPolynomial_add_one hproper hmin)
        (fun _ hγ=>(mem_filter.mp hγ).2)
    _≤ c*ox P:= by rw [← sH]; exact t8 hdeg hc
private theorem aTZ {A w} {T:oz K[X]} (hT: (T:Set K[X])⊆close A w)
    (hA:aRk A) {P:uz jo} (hp:P.IsPrime)
    (hd: (pL P).natDegree=1)
    (hpoints : ∀ f∈T,Gp f∈qy nU P) :
    ((gap A:ℕ) :ℚ)*T.card≤(p7 A:ℚ)*ox P+gap A ∧
    (T.card:ℚ)≤2*ox P:= by
  classical
  obtain ⟨δ,hδ,hdeg⟩:=aM6 P hp hd
  have hcap:=Wq hT hA δ fun i hi=> by
    have hc:=bv5 hT hp hpoints (node i) (w i) hi (c:=1) zero_le_one
      (fun _ hV Q _ hdim hpts=> by
        rw [sI]
        exact cw2 (fun _ hf=>hT (hV hf)) Q (by omega) hpts)
    rw [sI,hdeg] at hc
    exact_mod_cast hc
  rw [hdeg]
  refine ⟨by exact_mod_cast hcap,?_⟩
  suffices hn:T.card≤2*δ by exact_mod_cast hn
  by_contra! hbad
  have hstep:=oY (gap A) (show 2*δ+1≤T.card by omega)
  rw [Nat.mul_add,Nat.mul_one] at hstep
  have hstrict :=Nat.mul_lt_mul_of_pos_right hA.beta_lt_two hδ
  rw [p9 2 (gap A),vG] at hstrict
  omega
private theorem a8X {A w} {T:oz K[X]} (hT: (T:Set K[X])⊆close A w)
   (hA:aRk A) {P:uz jo} (hp:P.IsPrime)
   (hd: (pL P).natDegree=2)
   (hpoints : ∀ f∈T,Gp f∈qy nU P) :
   (gap A:ℚ)*T.card≤(p7 A:ℚ)*(2*ox P)+gap A:= by
 classical
 let cost:=2*ox P
 have hcost:0≤ cost:=vH (by decide) (affineDegree_nonneg P)
 have hn:=Wq hT hA ⌊cost⌋₊ fun i hi=> by
   apply (Nat.le_floor_iff hcost).mpr
   apply bv5 hT hp hpoints (node i) (w i) hi (c:=2) (by decide)
   exact fun _ hV _ hprime hdim hpts =>
     (aTZ (fun _ hf=>hT (hV hf)) hA hprime (by omega) hpts).2
 have hq: (gap A:ℚ)*T.card≤(p7 A:ℚ)*(⌊cost⌋₊ : ℚ)+gap A:= by exact_mod_cast hn
 exact hq.trans (Av (t8 (Nat.floor_le hcost)
   (zh (p7 A))) th)
theorem cOg {A w r budget} {T:oz K[X]} (hT: (T:Set K[X])⊆close A w)
    (hA:aRk A) (hr :r=1∨r=2) (F:vj r) (hg:bQ7 F budget)
    (hcover : ∀ f∈T,∃ i,Gp f∈(F.bY i).aN8) :
    (gap A:ℚ)*T.card≤(p7 A:ℚ)*(r*budget:ℕ)+(gap A:ℚ)*F.count:= by
  classical
  let part (i:Fin F.count) :=T.filter fun f=>Gp f∈(F.bY i).aN8
  have hc:T.card ≤ ∑ i,(part i).card:= by
    apply (xW (t:=univ.biUnion part) ?_).trans card_biUnion_le
    intro f hf
    obtain ⟨i,hi⟩:=hcover f hf
    exact mem_biUnion.mpr ⟨i,u9 _,mem_filter.mpr ⟨hf,hi⟩⟩
  have hone (i:Fin F.count) : (gap A:ℚ)*(part i).card ≤
      (p7 A:ℚ)*r*ox (F.bY i).ideal+gap A:= by
    have hsub: (part i:Set K[X])⊆close A w:= fun _ hf=>hT (mem_filter.mp hf).1
    have hp : ∀ f∈part i,Gp f∈qy nU (F.bY i).ideal :=
      fun _ hf=>zeroLocus_vanishingIdeal_le _ (mem_filter.mp hf).2
    rcases hr with h | h
    · have hh:=(aTZ hsub hA (hg.prime i) ((hg.dimension i).trans h) hp).1
      simpa only [h,Nat.cast_one,mul_one] using hh
    · have hh:=a8X hsub hA (hg.prime i) ((hg.dimension i).trans h) hp
      simpa only [h,Nat.cast_ofNat,vG] using hh
  have hq: (T.card:ℚ) ≤ ∑ i,((part i).card:ℚ) := by exact_mod_cast hc
  calc
    _≤(gap A:ℚ) * ∑ i,((part i).card:ℚ) :=t8 hq (zh _)
    _ = ∑ i,(gap A:ℚ)*(part i).card:=sH ..
    _≤_:=yQ fun i _=>hone i
    _=(p7 A:ℚ)*r*(∑ i,ox (F.bY i).ideal)+(gap A:ℚ)*F.count:= by
      rw [vi ,← sH,Ef ,nsmul_eq_mul,card_univ,Fintype.card_fin,p9 (F.count:ℚ)]
    _≤_:= by
      rw [Nat.cast_mul,← vG]
      exact Av (t8 hg.total
        (vH (zh _) (zh _))) th
end
end i4
end
section
namespace i4
noncomputable section
open Polynomial PolynomialDifferential Finset
open scoped BigOperators
def c1 :Prop :=
  ∀ A s cut,Rz s→s.m≤ s.m*A-N*s.B→cut≤ s.B+1→axY s cut →
    aWf A s≤aWw s cut
def c2 :Prop :=
  ∀ A s,Rz s→s.m≤ s.m*A-N*s.B → ∀ w:Node→K,
    Vv A s w≤n*aWf A s
def c3:Prop :=
  ∀ s,Rz s → ∀ Q,ato s Q →
    ∃ F:vj 2,bQQ s F∧cxn F Q
def c4 :Prop :=
 ∀ s,Rz s → ∀ F:vj 2,bQQ s F→bQ7 F (R₂ s)
def c5:Prop :=
  ∀ s,Rz s → ∀ Q,ato s Q →
    ∃ Q₁,bRZ s Q₁ ∧ ∀ f :K[X],f.degree<k →
      oZ Q f=0 → ¬ ae8 Q f →
      oZ Q₁ f=0
def c6:Prop :=
  ∀ s,Rz s → ∀ Q₁,bRZ s Q₁ →
    ∃ F:vj 1,cxu s F∧cxn F Q₁
def c7:Prop :=
 ∀ s,Rz s → ∀ F:vj 1,cxu s F→bQ7 F (R₁ s)
def c8:Prop :=
  ∀ s,Rz s → ∀ Q₁,bRZ s Q₁ →
    ∃ G:yJ K[X],G≠0∧G.natDegree≤H s*(H s-1) ∧
      ∀ f :K[X],f.degree<k→ oZ Q₁ f=0 →
        ¬ ae8 Q₁ f→G.eval f=0
private theorem combine {u v b h r₂ r₁ x y z :ℕ}
  (hx :v*x≤u*(2*r₂)+v*b) (hy :v*y≤u*r₁+v*h) (hz :z≤h*(h-1)) :
  v*(x+y+z)≤u*(2*r₂+r₁)+v*(b+h^2) := by
 have htail:h+h*(h-1)=h^2 := by
  cases h with
  | zero=>rfl
  | succ h=>rw [Nat.succ_sub_one]; ring
 calc
  _=v*x+v*y+v*z := by ring
  _≤(u*(2*r₂)+v*b)+(u*r₁+v*h)+v*(h*(h-1)) :=
    v8 (v8 hx hy) (oY v hz)
  _ = _:= by rw [← htail]; ring
end
end i4
end
section
namespace a9M
noncomputable section
open i4 (Jet alu)
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
abbrev LocalExponent:=LocalVariable 2 →₀ ℕ
def rowJet (e :LocalExponent) :Jet :=
 ⟨e (oK (1 :Fin 2)),e (oK (0:Fin 2)),e (localE 2)⟩
def aJn (e :LocalExponent) :ℤ :=
 (e (nI 2) :ℤ)-(rowJet e).a-(rowJet e).v
def aG9 (x :ℕ) (j:Jet) :ℤ:=(x :ℤ) - j.v
private def exponent (t h d l:ℕ) :LocalExponent :=
 uh (nI 2) t+Finsupp.single (localE 2) h +
  uh (oK (0:Fin 2)) d+Finsupp.single (oK (1 :Fin 2)) l
private theorem exponent_eq_iff (t h d l:ℕ) (e :LocalExponent) :
    exponent t h d l=e ↔
      t=e (nI 2)∧h=(rowJet e).a∧d=(rowJet e).b∧l=(rowJet e).c:= by
  classical
  constructor
  · intro he
    have atVar (v :LocalVariable 2) :=vl he v
    exact ⟨by simpa [exponent,localT,localE,localAux,localY] using atVar (localT 2),
      by simpa [exponent,rowJet,Jet.a,nI ,localE,localAux,oK ] using atVar (localE 2),
      by simpa [exponent,rowJet,Jet.b,localT,localE,localAux,localY] using
        atVar (oK  (0:Fin 2)),
      by simpa [exponent,rowJet,Jet.c,localT,localE,localAux,localY] using
        atVar (oK  (1 :Fin 2))⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    ext v
    rcases v with _ | (_ | j)
    · simp [exponent,nI,localE,localAux,oK]
    · simp [exponent,rowJet,Jet.a,nI,localE,localAux,oK]
    · fin_cases j <;> simp [exponent,rowJet,Jet.b,Jet.c,nI,localE,localAux,oK]
variable {F:Type*} [zc F]
private theorem eId (x a b c:ℕ) :
    GY 2 (0:F) 0 (wB x a ![b,c]) =
      ∑ h∈t3 (a+1),∑ j∈t3 (a-h+1),
        qU (exponent (x+h+j+2*(a-h-j)) h (b+j) (c+(a-h-j)))
          ((-1 :F)^(a-h-j)*(a.choose h:F)*((a-h).choose j:F)) := by
  classical
  let localX:xu F 2 :=c9 (nI 2)
  let hiddenTerm:xu F 2 :=localX*c9 (localE 2)
  let jetOne :xu F 2 :=c9 (oK (0:Fin 2))
  let jetTwo:xu F 2 :=c9 (oK (1 :Fin 2))
  let firstTerm:=localX*jetOne
  let secondTerm := -(localX^2*jetTwo)
  have h₀:GY 2 (0:F) 0 (c9 (some 0))=hiddenTerm+(firstTerm+secondTerm) := by
    simp [localCorrection,zi ,hiddenTerm,firstTerm,secondTerm,localX,jetOne,jetTwo]
    ac_rfl
  rw [wB,Fin.prod_univ_two,mD,mD,mD,
    pG,pG,pG,pG,h₀]
  simp only [unscaledLocalSubstitution_X,unscaledLocalSubstitution_Y_succ,C_0,t7,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  change localX^x*(hiddenTerm+(firstTerm+secondTerm))^a*(jetOne^b*jetTwo^c)= _
  rw [add_pow hiddenTerm (firstTerm+secondTerm),sH,vk]
  refine pQ rfl fun h _ => ?_
  rw [add_pow firstTerm secondTerm]
  simp only [sH,vk]
  refine pQ rfl fun j _ => ?_
  have hW:secondTerm=qU (uh (nI 2) 2 +
      uh (oK (1 :Fin 2)) 1) (-1) := by
    change -(c9 (nI 2)^2*c9 (oK (1 :Fin 2)))= _
    rw [ X_pow_eq_monomial]
    simp only [c9,monomial_mul_monomial,sI,map_neg]
  have hE :hiddenTerm=qU (uh (nI 2) 1 +
      uh (localE 2) 1) 1 := by simp [hiddenTerm,localX,c9]
  have hV:firstTerm=qU (uh (nI 2) 1 +
      uh (oK (0:Fin 2)) 1) 1 := by simp [firstTerm,localX,jetOne,c9]
  have hcast (n:ℕ) : (n:xu F 2)=qU 0 (n:F) := by
    rw [monomial_zero',map_natCast]
  rw [hE,hV,hW]
  simp only [localX,jetOne,jetTwo,X_pow_eq_monomial,monomial_pow,
    hcast,monomial_mul_monomial,sI,mul_one,one_pow]
  apply congrArg₂ (fun a b=>(qU a b:xu F 2))
  · apply Finsupp.ext
    intro v
    rcases v with _ | (_ | u)
    · simp [exponent,nI,localE,localAux,oK,zE,FR]
    · simp [exponent,nI,localE,localAux,oK]
    · fin_cases u <;>
        simp [exponent,nI,localE,localAux,oK,ze]
  · ring
theorem eH6 (x :ℕ) (j:Jet) (e :LocalExponent) :
    (GY 2 (0:ZMod i4.p) 0
       (wB x j.a ![j.b,j.c])).coeff e =
      if aJn e=aG9 x j then alu (rowJet e) j else 0:= by
  classical
  let r :=rowJet e
  let P:Prop :=aJn e=aG9 x j ∧
    (j.b≤ r.b∧j.c≤ r.c∧r.a+(r.b-j.b)+(r.c-j.c)=j.a)
  have hexp (h u:ℕ) (hh:h≤j.a) (hu:u≤j.a-h) :
      exponent (x+h+u+2*(j.a-h-u)) h (j.b+u) (j.c+(j.a-h-u))=e ↔
        P∧h=r.a∧u=r.b-j.b:= by
    rw [exponent_eq_iff]
    change (x+h+u+2*(j.a-h-u)=e (nI 2) ∧
      h=r.a∧j.b+u=r.b∧j.c+(j.a-h-u)=r.c) ↔
      ((e (nI 2) :ℤ) - r.a-(r.b+2*r.c:ℕ) =
       (x :ℤ)-(j.b+2*j.c:ℕ) ∧
         (j.b≤ r.b∧j.c≤ r.c∧r.a+(r.b-j.b)+(r.c-j.c)=j.a)) ∧
       h=r.a∧u=r.b-j.b
    omega
  rw [eId]
  simp_rw [coeff_sum,Dz]
  by_cases hp:P
  · obtain ⟨hg,hb,hc,ha⟩:=hp
    have hh:r.a≤j.a := by omega
    have hu:r.b-j.b≤j.a-r.a := by omega
    rw [LR r.a (Finset.mem_range.mpr (by omega))]
    · rw [Finset.sum_eq_single_of_mem (r.b-j.b) (Finset.mem_range.mpr (by omega))]
      · rw [Kc  ((hexp _ _ hh hu).2 ⟨⟨hg,hb,hc,ha⟩,rfl,rfl⟩),Kc  hg]
        change _=alu r j
        rw [alu,Kc  ⟨hb,hc,ha⟩,show j.a-r.a-(r.b-j.b)=r.c-j.c by omega]
      · intro u hmem hne
        rw [yL  (fun he=>hne ((hexp _ _ hh (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem))).1 he).2.2)]
    · intro h hmem hne
      apply y5
      intro u humem
      rw [yL (fun he=>hne ((hexp _ _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp humem))).1 he).2.1)]
  · have hz := fun h u (hh:h≤j.a) (hu:u≤j.a-h) he =>
      hp ((hexp h u hh hu).1 he).1
    have hzero : (if aJn e=aG9 x j then alu r j else 0)=0:= by
      split
      · rename_i hg
        exact yL (fun hb=>hp ⟨hg,hb⟩)
      · rfl
    rw [hzero]
    apply y5
    intro h hmem
    apply y5
    intro u humem
    rw [yL (hz h u (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem)) (Nat.lt_succ_iff.mp (Finset.mem_range.mp humem)))]
end
end a9M
end
section
namespace a9M
noncomputable section
open scoped BigOperators Matrix
theorem fS3 {F I:Type*} [Field F] [Fintype I]
    {R C:I→Type*} [∀ i,Fintype (C i)] [DecidableEq I]
    (M : ∀ i,Matrix (R i) (C i) F) :
    (z7 M).rank ≤ ∑ i,(M i).rank := by
  let Φ:=(z7 M).mulVecLin
  let φ:= fun i=>(M i).mulVecLin
  let project :Φ.range →ₗ[F] ∀ i,(φ i).range :=
    { toFun y i:=⟨fun r=>y.val ⟨i,r⟩,by
        obtain ⟨v,hv⟩:=y.property
        refine ⟨fun c=>v ⟨i,c⟩,?_⟩
        rw [← hv]
        funext r
        change (∑ c:C i,M i r c*v ⟨i,c⟩) =
          ∑ j:t5 C,z7 M ⟨i,r⟩ j*v j
        rw [← Finset.univ_sigma_univ,Finset.sum_sigma,Finset.sum_eq_single i]
        · simp [KI]
        · intro j _ hji
          apply y5
          intro c _
          rw [Iw _ _ _ (Ne.symm hji),uW]
        · simp⟩
      map_add' x y := by ext i r; rfl
      map_smul' t x := by ext i r; rfl }
  have hinj:sS project := by
    intro x y h
    apply xm
    funext ⟨i,r⟩
    exact wA (oD uJ (wA h i)) r
  change qJ F Φ.range ≤ ∑ i,qJ F (φ i).range
  exact (FU hinj).trans_eq
    (Module.finrank_pi_fintype F)
end
end a9M
end
section
namespace apQ
noncomputable section
open i4 PolynomialDifferential
open scoped BigOperators Polynomial
abbrev Equation :=qx K 2
def RG:K[X] →+* nU :=
 (xL FX nU).comp (xL K[X] FX)
def dR (G:Equation) :qx nU 2 :=
 lV oq G
def initial (G:Equation) :BL 2 :=
 initialJetEquation lI (dR G)
def T4 (G:Equation) :BL 2 :=
 initialJetSeparant lI (dR G)
def ahT (f :K[X]) :Fin 3→nU :=
 polynomialJet lI (f.map oq)
def bmP (G:Equation) (τ l:ℕ) :BL 2 :=
 commonTaylorNumerator lI (dR G) τ l
abbrev bmO (G:Equation) (l:Fin k) :BL 2 :=
 bmP G t l.val
def bns (G:Equation) (τ:ℕ) {L:ℕ} (i:Fin L) :BL 2 :=
  ∑ l:Fin L,ov (((nX-Polynomial.C lI)^l.val).coeff i.val) *
    bmP G τ l.val
abbrev VT (G:Equation) (i:Fin k) :BL 2 :=
 bns G t i
def bY (G:Equation) (P:BL 2) :nq 2 :=
 ⟨P,T4 G^t,VT G⟩
structure bQP (Q:Equation) where
 count:ℕ
 source :Fin count→Equation
 equation :Fin count→BL 2
 source_irreducible : ∀ i,Irreducible (source i)
 source_dvd : ∀ i,source i∣Q
 irreducible : ∀ i,Irreducible (equation i)
 component : ∀ i,equation i∣initial (source i)
 regular : ∀ i,¬ equation i∣T4 (source i)
 bKQ: (∏ i,equation i)∣initial Q
 Eh : ∀ f :K[X],ae8 Q f →
  ∃ i,oZ (source i) f=0 ∧
    cy (ahT f) (equation i)=0 ∧
    cy (ahT f) (T4 (source i))≠0
end
end apQ
end
section
namespace apQ
noncomputable section
open i4 Polynomial PolynomialDifferential
open scoped BigOperators
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
theorem ayP:Et 2 k t:= by
 intro l
 have hl:=l.isLt
 unfold t
 omega
theorem bch:sS RG :=
 (xL FX nU).injective.comp (GR K[X] FX)
theorem b6h (G:Equation) :
    initial G=lV RG (G1 K (Fin 3) G) := by
  let a :Equation →+* BL 2 :=
    (qm (fun j:t6 (Fin 3)=>j.elim (ov lI)
      c9)).toRingHom.comp (lV oq)
  let b:Equation →+* BL 2 :=(lV RG).comp
    (G1 K (Fin 3)).toAlgHom.toRingHom
  have he :a=b:= by
    apply Ar
    · intro c
      change a (ov c)=b (ov c)
      simp [a,b]
      rfl
    · intro j
      cases j with
      | none =>
        simp [a,b]
        rfl
      | some j=>simp [a,b]
  exact vl he G
theorem b6i:sS initial := by
 intro P Q h
 rw [b6h,b6h] at h
 exact (G1 K (Fin 3)).injective
  (MvPolynomial.map_injective _ bch h)
theorem b6j {G:Equation} (hG:G≠0) :initial G≠0:= by
 intro h
 apply hG
 exact b6i (h.trans (by simp [initial,dR,initialJetEquation]))
private theorem auQ (P:K[X]) : (P.map oq).eval lI=RG P:= by
 rw [eval_map]
 change eval₂RingHom oq lI P=RG P
 have h:eval₂RingHom oq lI=RG:= by
   apply Polynomial.ringHom_ext
   · intro a
     change eval₂ oq lI (lJ a)=RG (lJ a)
     rw [eval₂_C]
     rfl
   · change eval₂ oq lI nX=RG nX
     rw [eval₂_X]
     rfl
 rw [h]
theorem bHS (G:Equation) (f :K[X]) :
   cy (ahT f) (initial G) =
     RG (oZ G f) := by
 rw [initial,← Gr,aeval_initialJetEquation,ahT,
   ← eval_differentialSpecialization,dR,← map_differentialSpecialization,auQ]
theorem eom (G:Equation) (f :K[X]) :
   cy (ahT f) (T4 G) =
     RG (oZ (separant G (aU 2)) f) := by
 have he :T4 G=initial (separant G (aU 2)) := by
   rw [T4,initialJetSeparant,initial,dR,dR,map_separant]
   rfl
 rw [he,bHS]
private theorem dMx (G:Equation) (u:Fin 3→nU) {L:ℕ} (i:Fin L) :
    (yo lI (dR G) L u).coeff i.val =
      ∑ l:Fin L,((nX-Polynomial.C lI)^l.val).coeff i.val *
        rationalTaylorCoefficient lI (dR G) u l.val := by
  rw [yo ,centeredCoefficientPrefix,zd ,finsetSum_coeff]
  apply pQ rfl
  intro l _
  rw [taylor_monomial,coeff_C_mul,map_neg,← sub_eq_add_neg,p9]
private theorem d1Z (G:Equation) (u:Fin 3→nU)
   (h:cy u (T4 G)≠0) {L τ:ℕ}
   (hτ:Et 2 L τ) (i:Fin L) :
   cy u (bns G τ i) /
     cy u (T4 G^τ) =
     (yo lI (dR G) L u).coeff i.val := by
 have hpow:cy u (T4 G)^τ≠0:=pow_ne_zero _ h
 rw [dMx,bns,zd ,pG,Finset.sum_div]
 apply pQ rfl
 intro l _
 rw [mD,MvPolynomial.eval_C,bmP]
 rw [← Gr (f :=u),
   aeval_commonTaylorNumerator lI (dR G) u (hτ l) h]
 change _ *(cy u (T4 G)^τ*_) /
   cy u (T4 G)^τ= _
 field_simp
theorem cFr (G:Equation) (P:BL 2) (u:Fin 3→nU)
  (h:cy u (T4 G)≠0) (i:Fin k) :
  (bY G P).output u i=(yo lI (dR G) k u).coeff i.val := by
 simp only [Chart.output,bY]
 exact d1Z G u h (L:=k) (τ:=t) ayP i
private theorem fUf {L:ℕ} (P:nU[X]) (hp:P.degree<L) (j:ℕ) :
   (∑ i:Fin L,(i.val.choose j:nU)*lI ^(i.val-j)*P.coeff i.val) =
     (vZ j P).eval center := by
 rw [hasseDeriv_apply,← Polynomial.sum_fin
   (fun i c=>monomial (i - j) ((i.choose j:nU)*c)) (by simp) hp,eval_finsetSum]
 apply pQ rfl
 intro i _
 rw [eval_monomial]
 ring
theorem a2o (G:Equation) (P:BL 2) (u:Fin 3→nU)
  (h:cy u (T4 G)≠0) (j:Fin 3) :
  awb ((bY G P).output u) j.val=u j:= by
 let U:=yo lI (dR G) k u
 have hout: (bY G P).output u=(fun i:Fin k=>U.coeff i.val) := by
  funext i
  exact cFr G P u h i
 have he :awb ((bY G P).output u) j.val=awb (fun i=>U.coeff i.val) j.val :=
  oD (fun y :Fin k→nU=>awb y j.val) hout
 have hd:U.degree<k :=degree_centeredCoefficientPrefix_lt _ _ _
 have hj:awb (fun i=>U.coeff i.val) j.val=(vZ j.val U).eval center :=
  fUf (L:=k) U hd j.val
 refine he.trans (hj.trans ?_)
 exact wA (polynomialJet_rationalTaylorPolynomial lI (dR G)
  (by decide :2<k) u) j
theorem dIj (G:Equation) (P:BL 2) (f :K[X])
  (hf :f.degree<k) (hg:oZ G f=0)
  (hsep:cy (ahT f) (T4 G)≠0) :
  (bY G P).output (ahT f)=Gp f := by
 have hsol:oZ (dR G) (f.map oq)=0:= by
  rw [dR,← map_differentialSpecialization,hg,Polynomial.map_zero]
 have hsep' : jetEvaluation (separant (dR G) (aU 2)) lI (ahT f)≠0:= by
  simpa only [T4,← Gr,aeval_initialJetSeparant] using hsep
 have hd: (f.map oq).degree<k :=(Polynomial.degree_map_eq_of_injective embed.injective f) ▸ hf
 let:CharP nU p:=charP_of_injective_ringHom embed.injective p
 have hbin (i:ℕ) (hlo:2< i) (hhi:i<k) : (i.choose 2 :nU)≠0 :=
  yP.bQq.c1j 2 th i hlo (Nat.lt_succ_of_lt hhi)
 have hrec:=rationalTaylorPolynomial_polynomialJet lI (dR G) (f.map oq)
  hsol hsep' hd hbin
 funext i
 rw [cFr G P (ahT f) hsep i,ahT,hrec,zm]
 rfl
end
end apQ
end
section
namespace apQ
noncomputable section
open i4 PolynomialDifferential MvPolynomial
open scoped BigOperators
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
private theorem dl3 {σ R S:Type*} [CommSemiring R] [CommSemiring S]
  (φ:R →+* S) (hφ:sS φ) (w:σ→ℕ) (P:u5 σ R) :
  (lV φ P).weightedTotalDegree w=P.weightedTotalDegree w:= by
 unfold Au
 rw [support_map_of_injective P hφ]
theorem b6k (w:Fin 3→ℕ) (G:Equation) :
  (initial G).weightedTotalDegree w=G.weightedTotalDegree (fun j=>j.elim 0 w) := by
 rw [b6h,dl3 _ bch,weightedTotalDegree_optionEquivRight]
private theorem b7J (w:t6 (Fin 3)→ℕ) (G:Equation) :
  (dR G).weightedTotalDegree w=G.weightedTotalDegree w :=
 dl3 oq embed.injective w G
private theorem cX0 (G:Equation) :jetTotalDegree (dR G)=jetTotalDegree G :=
 b7J jetDegreeWeight G
private theorem eww (G:Equation) :
  jetDegree (dR G) (aU 2)=jetDegree G (aU 2) := by
 simpa only [jetDegree,t4] using
  b7J (vw (some (aU 2)) 1) G
theorem eHq {s :lz} {G Q:Equation} (hQ:ato s Q) (h:G∣Q) :
  ato s G:= by
 refine ⟨ne_zero_of_dvd_ne_zero hQ.1 h,
  (Fz jetDegreeWeight h hQ.1).trans hQ.2.1,
  (Fz Cy h hQ.1).trans hQ.2.2.1,?_⟩
 have htop:=Fz (vw (some (aU 2)) 1) h hQ.1
 rw [t4 ,t4] at htop
 exact htop.trans hQ.2.2.2
private theorem gCt: (fun j:t6 (Fin 3)=>j.elim 0 (1 :Fin 3→ℕ)) =
  jetDegreeWeight:= by
 funext j
 cases j <;> rfl
private theorem gCe : (fun j:t6 (Fin 3) =>
  j.elim 0 (vw (aU 2) 1))=vw (some (aU 2)) (1 :ℕ) := by
 funext j
 cases j <;> simp [Pi.single_apply]
theorem d52 {s :lz} {Q:Equation} (hQ:ato s Q) (F:bQP Q) :
   (∑ i,(F.equation i).totalDegree)≤ s.B ∧
   (∑ i,(F.equation i).weightedTotalDegree oj)≤ s.J ∧
   (∑ i,(F.equation i).degreeOf (aU 2))≤ s.C:= by
 have hn:=b6j hQ.1
 have h (w:Fin 3→ℕ) :
     (∑ i,(F.equation i).weightedTotalDegree w)≤(initial Q).weightedTotalDegree w :=
   sum_weightedTotalDegree_le_of_prod_dvd w Finset.univ F.equation hn F.bKQ
 have ht:=h (1 :Fin 3→ℕ)
 have hi:=h oj
 have hc:=h (vw (aU 2) 1)
 rw [b6k,gCt] at ht
 rw [b6k] at hi
 rw [b6k,gCe,t4] at hc
 simp only [zS] at ht
 simp only [t4] at hc
 exact ⟨ht.trans hQ.2.1,hi.trans hQ.2.2.1,hc.trans hQ.2.2.2⟩
theorem d5P {Q:Equation} (F:bQP Q) :
  F.count ≤ ∑ i,(F.equation i).totalDegree := by
 classical
 have h (i:Fin F.count) :1≤(F.equation i).totalDegree := by
  by_contra! hh
  have hdeg: (F.equation i).totalDegree=0:= by omega
  have he :=totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hz : (F.equation i).coeff 0≠0:= fun hz =>
    (F.irreducible i).ne_zero (he.trans (by rw [hz,p6]))
  exact (F.irreducible i).not_isUnit (he.symm ▸ (isUnit_iff_ne_zero.mpr hz).map ov)
 calc
  F.count = ∑ _:Fin F.count,(1 :ℕ) := by simp
  _≤_:=yQ fun i _=>h i
private theorem cJR {P:BL 2} {d:ℕ}
    (hP:P.weightedTotalDegree oj≤d) :P.degreeOf (aU 2)≤d/2 := by
  classical
  apply degreeOf_le_iff.mpr
  intro m hm
  have hweight:2*m (aU 2)≤qM oj m:= by
    rw [Finsupp.weight_apply,Finsupp.sum_fintype _ _ (by simp)]
    have hsum:m (aU 2)•(aU 2).val ≤ ∑ i,m i•oj i :=
      Finset.single_le_sum (fun i _=>Nat.zero_le (m i•oj i))
        (u9 (aU 2))
    simpa only [Fin.val_last,C5 ,zE 2] using hsum
  have h:=hweight.trans ((Ee oj hm).trans hP)
  omega
private theorem bX2 (G:Equation) {L τ:ℕ} (i:Fin L) (w:Fin 3→ℕ) (d:ℕ)
  (h : ∀ l:Fin L,(bmP G τ l.val).weightedTotalDegree w≤d) :
  (bns G τ i).weightedTotalDegree w≤d:= by
 classical
 apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
 rw [bns]
 apply Gi
 intro l _
 apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
 apply (weightedTotalDegree_mul_le _ _ _).trans
 simpa only [weightedTotalDegree_C,t7] using h l
private theorem b6d:amZ.kO 0 1 3=i4.indexWeight:= by
 funext i
 cases i <;> simp [amZ.kO,Cy]
private theorem cF3:amZ.U6 0 1 (2+1)=Fin.val := by
 funext i
 simp [amZ.U6]
private theorem cXZ {s :lz} {G:Equation} (hG:ato s G) :
  (dR G).weightedTotalDegree (amZ.kO 0 1 3)≤ s.J:= by
 rw [b7J,b6d]
 exact hG.2.2.1
private theorem gpy {s :lz} {G:Equation} (hG:ato s G) :
  (T4 G).weightedTotalDegree oj≤ s.J - 2 := by
 simpa only [T4,cF3,t7,sI] using
  (amZ.b6g 0 1 lI (dR G)).trans
    (v9 (cXZ hG) (0+1*2))
private theorem dGD {s :lz} (hs :Rz s) {G:Equation}
  (hG:ato s G) (l:Fin k) :
  (bmO G l).weightedTotalDegree oj≤D s := by
 have hJ:=hs.index_top
 have hC:=hs.top_pos
 have hcap:0+1*2≤ s.J:= by omega
 have h:=amZ.dN8 0 1 s.J k t lI (dR G)
  ayP hcap (cXZ hG) l
 have hl:l.val≤k - 1 := by have :=l.isLt; omega
 have hi: (bmO G l).weightedTotalDegree oj≤t*(s.J - 2)+l.val := by
  simpa only [bmP,cF3,t7,xI,sI] using h
 exact hi.trans (x7 hl _)
private theorem dGF {s :lz} {G:Equation} (hG:ato s G) (l:Fin k) :
  (bmO G l).totalDegree≤a₀ s := by
 apply (totalDegree_commonTaylorNumerator_le lI (dR G) (ayP l)).trans
 rw [rationalTaylorCutDegreeBound,cX0]
 exact x7 (oY _ (v9 hG.2.1 1)) _
theorem b0p {s :lz} {G:Equation} (hG:ato s G) :
    bHP s (T4 G^t) := by
  have ht: (T4 G).totalDegree≤ s.B - 1 := by
    apply (totalDegree_initialJetSeparant_le lI (dR G)).trans
    rw [cX0]
    exact v9 hG.2.1 1
  have htop: (T4 G).degreeOf (aU 2)≤ s.C - 1 := by
    apply (Gn lI (dR G)).trans
    change jetDegree (dR G) (aU 2) - 1≤ s.C - 1
    rw [eww]
    exact v9 hG.2.2.2 1
  have hi: (T4 G^t).weightedTotalDegree oj≤D s :=
    ((weightedTotalDegree_pow_le oj _ _).trans
      (oY _ (gpy hG))).trans (yl _ _)
  refine ⟨(totalDegree_pow _ _).trans ((oY _ ht).trans ?_),hi,?_⟩
  · simpa only [a₀,ze] using yl (t*(s.B - 1)) 1
  · apply le_min
    · exact (degreeOf_pow_le _ _ _).trans
        ((oY _ htop).trans (yl _ _))
    · exact cJR hi
theorem eFC {s :lz} (hs :Rz s) {G:Equation} (hG:ato s G)
   (hTop : ∀ l,(bmO G l).degreeOf (aU 2)≤t*(s.C - 1)+k - 2)
   (i:Fin k) :bHP s (VT G i) := by
 have hi:=bX2 G (τ:=t) i oj (D s) (dGD hs hG)
 refine ⟨?_,hi,le_min ?_ (cJR hi)⟩
 · rw [← zS]
   apply bX2 (τ:=t)
   intro l
   simpa only [zS] using dGF hG l
 · rw [← t4]
   apply bX2 (τ:=t)
   intro l
   simpa only [t4] using hTop l
end
end apQ
end
section
namespace a9M
noncomputable section
open i4 (Rz axY Jet apU aCq aTf GU alu aWw p)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators Matrix
local instance :Fact (Nat.Prime p) :=⟨KoalaBear.is_prime⟩
abbrev bjT (s :lz) :=Unit×LowContactIndex 2 s.m
abbrev bAg (A:ℕ) (s :lz) :=apU A s
private def origin (A:ℕ) (s :lz) :Matrix (bjT s) (bAg A s) (ZMod p) :=
 vh s.m (fun _:Unit=>0) (fun _=>0) (oy A s)
private theorem caO {A s} (r :bjT s) (j:bAg A s) :
    origin A s r j =
      if aJn r.2.val=aG9 j.2.val j.1.val then
        alu (rowJet r.2.val) j.1.val else 0:= by
  rw [origin,localConstraintMatrix_apply,Gk]
  exact eH6 j.2.val j.1.val r.2.val
abbrev sP (s :lz) (cut:ℕ) :=(q:Fin cut)×Fin (s.m+s.J-q.val)
private def balance {s cut} (i:sP s cut) :ℤ:=(i.2.val :ℤ) - s.J
private structure bjo (s :lz) (cut q:ℕ) (g:ℤ) :Prop where
 cV:q<cut
 lower : -(s.J:ℤ)≤g
 upper :g+q<(s.m:ℤ)
private def bml {s cut q g} (h:bjo s cut q g) :sP s cut :=
 ⟨⟨q,h.cV⟩,⟨(g+s.J).toNat,by
   change (g+s.J).toNat<s.m+s.J-q
   have :=h.lower
   have :=h.upper
   omega⟩⟩
private theorem bBs {s cut q g} (h:bjo s cut q g) :
  balance (bml h)=g:= by
 have :=h.lower
 simp only [balance,bml]
 omega
private theorem dzc {s cut} {i j:sP s cut}
  (hq:i.1.val=j.1.val) (hg:balance i=balance j) :i=j:= by
 rcases i with ⟨qi,ui⟩
 rcases j with ⟨qj,uj⟩
 have hgrade :qi=qj:=Fin.ext hq
 subst qj
 have hoffset :ui=uj:=Fin.ext (by simp only [balance] at hg; omega)
 subst uj
 rfl
private theorem cfQ {s :lz} (r :bjT s) :
   rowJet r.2.val∈aCq s.m (rowJet r.2.val).q (aJn r.2.val) := by
 let j:=rowJet r.2.val
 have hcontact :=r.2.property
 rw [localContactOrder_eq] at hcontact
 change r.2.val (nI 2)+2*j.a<s.m at hcontact
 have hweight:aJn r.2.val+(j.v :ℤ)+3*(j.a :ℤ) =
     (r.2.val (nI 2) :ℤ)+2*(j.a :ℤ) := by
   change (r.2.val (nI 2) :ℤ) - j.a - j.v+j.v+3*j.a= _
   omega
 refine Finset.mem_filter.mpr ⟨?_,by rw [hweight]; omega⟩
 change j∈(t3 (j.q+1)).sigma
   (fun c=>(t3 (j.q-c+1)).sigma fun b => {j.q-(b+c)})
 generalize j=i
 rcases i with ⟨c,b,a⟩
 simp only [Finset.mem_sigma,Finset.mem_range,Finset.mem_singleton,Jet.q,Jet.a,Jet.b,Jet.c]
 omega
private theorem caP {A s cut} (hs :Rz s) (htail:axY s cut)
   (r :bjT s) (j:bAg A s) (hn:origin A s r j≠0) :
   (rowJet r.2.val).q=j.1.val.q∧aJn r.2.val=aG9 j.2.val j.1.val ∧
     bjo s cut j.1.val.q (aG9 j.2.val j.1.val) := by
 let i:=rowJet r.2.val
 let c:=j.1.val
 have hg:aJn r.2.val=aG9 j.2.val c:= by
   by_contra hn'
   exact hn (by rw [caO,yL hn'])
 have hbc:c.b≤ i.b∧c.c≤ i.c∧i.a+(i.b-c.b)+(i.c-c.c)=c.a := by
   by_contra hn'
   exact hn (by rw [caO,Kc hg,alu,yL hn'])
 obtain ⟨hb,hc,ha⟩:=hbc
 have hq:i.q=c.q:= by simp only [Jet.q]; omega
 have hcontact :=r.2.property
 rw [localContactOrder_eq] at hcontact
 change r.2.val (nI 2)+2*i.a<s.m at hcontact
 have heq : (r.2.val (nI 2) :ℤ) - i.a-(i.b+2*i.c:ℕ) =
     (j.2.val :ℤ)-(c.b+2*c.c:ℕ) :=hg
 have hsmall:c.a<s.m:= by omega
 have hgrade :c.q<cut:= by
   by_contra! hbig
   exact (Nat.not_le_of_gt hsmall) (htail c j.1.property hbig)
 have hv :=(hs.support c j.1.property).2.1
 refine ⟨hq,hg,hgrade,?_,?_⟩
 · change -(s.J:ℤ)≤(j.2.val :ℤ) - c.v
   change c.v≤ s.J at hv
   omega
 · change (j.2.val :ℤ)-(c.b+2*c.c:ℕ)+(c.a+c.b+c.c:ℕ)<(s.m:ℤ)
   omega
private def bbE (A:ℕ) (s :lz) :oz (bjT s) :=
 localConstraintSupportedRows s.m (fun _:Unit=>(0:ZMod p)) (fun _=>0) (oy A s)
private def blj (A:ℕ) (s :lz) :oz (bAg A s) := by
 classical
 exact Finset.univ.filter fun j => ∃ r,origin A s r j≠0
private theorem cAD {A s cut} (hs :Rz s) (htail:axY s cut)
  (r :bbE A s) :
  bjo s cut (rowJet r.val.2.val).q (aJn r.val.2.val) := by
 obtain ⟨j,hj⟩:=(mem_localConstraintSupportedRows_iff _ _ _ _ _).mp r.property
 obtain ⟨hq,hg,h⟩:=caP hs htail r.val j hj
 rwa [hq,hg]
private theorem cAB {A s cut} (hs :Rz s) (htail:axY s cut)
  (j:blj A s) :
  bjo s cut j.val.1.val.q (aG9 j.val.2.val j.val.1.val) := by
 classical
 obtain ⟨r,hr⟩:=(Finset.mem_filter.mp j.property).2
 exact (caP hs htail r j.val hr).2.2
private abbrev bQn {s cut} (i:sP s cut) :Type := ↥(aCq s.m i.1.val (balance i))
private abbrev bQk {s cut} (i:sP s cut) :Type := ↥(aTf s i.1.val (balance i))
private def c83 {A s cut} (hs :Rz s) (htail:axY s cut) (r :bbE A s) :
   t5 (bQn (s :=s) (cut:=cut)) :=
 let h:=cAD hs htail r
 ⟨bml h,⟨rowJet r.val.2.val,by
   change rowJet r.val.2.val ∈
     aCq s.m (rowJet r.val.2.val).q (balance (bml h))
   rw [bBs]
   exact cfQ r.val⟩⟩
private def cGM {A s cut} (hs :Rz s) (htail:axY s cut) (j:blj A s) :
   t5 (bQk (s :=s) (cut:=cut)) :=
 let h:=cAB hs htail j
 ⟨bml h,⟨j.val.1.val,by
   apply Finset.mem_filter.mpr
   refine ⟨j.val.1.property,rfl,?_⟩
   rw [bBs]
   simp [aG9]⟩⟩
private def Bs (s :lz) (cut:ℕ) :
  Matrix (t5 (bQn (s :=s) (cut:=cut))) (t5 (bQk (s :=s) (cut:=cut)))
   (ZMod p) :=
 z7 fun i=>GU s i.1.val (balance i)
private theorem eJj {s cut} (r :t5 (bQn (s :=s) (cut:=cut)))
  (c:t5 (bQk (s :=s) (cut:=cut))) (h:r.1=c.1) :
  Bs s cut r c=alu r.2.val c.2.val := by
 rcases r with ⟨i,r⟩
 rcases c with ⟨j,c⟩
 change i=j at h
 subst j
 exact KI _ _ _ _
private theorem eIc {A s cut} (hs :Rz s) (htail:axY s cut) :
   (origin A s).submatrix (uJ :bbE A s→_) (uJ :blj A s→_) =
     (Bs s cut).submatrix (c83 hs htail) (cGM hs htail) := by
 ext r c
 let i:=c83 hs htail r
 let j:=cGM hs htail c
 change origin A s r.val c.val=Bs s cut i j
 have hr :balance i.1=aJn r.val.2.val :=
   bBs (cAD hs htail r)
 have hc:balance j.1=aG9 c.val.2.val c.val.1.val :=
   bBs (cAB hs htail c)
 by_cases hij:i.1=j.1
 · rw [eJj i j hij,caO,Kc (hr.symm.trans ((oD balance hij).trans hc))]
   rfl
 · have hz :origin A s r.val c.val=0:= by
     by_contra hn
     obtain ⟨hq,hg,_⟩:=caP hs htail r.val c.val hn
     exact hij (dzc hq (hr.trans (hg.trans hc.symm)))
   rw [hz]
   exact (Iw _ _ _ hij).symm
private theorem eIa (A:ℕ) (s :lz) :
  (origin A s).rank =
    ((origin A s).submatrix (uJ :bbE A s→_) id).rank := by
 symm
 apply Matrix.rank_submatrix_eq_of_ne_zero_mem_range
 exact localConstraintMatrix_ne_zero_mem_range _ _ _ _
private theorem gxA (A:ℕ) (s :lz) :
    ((origin A s).submatrix (uJ :bbE A s→_) id).rank ≤
      ((origin A s).submatrix (uJ :bbE A s→_)
        (uJ :blj A s→_)).rank := by
  classical
  apply yP.C52.fTe
  intro j
  by_cases hj:j∈blj A s
  · exact Or.inr ⟨⟨j,hj⟩,rfl⟩
  · left
    funext r
    change origin A s r.val j=0
    by_contra hn
    exact hj (Finset.mem_filter.mpr ⟨u9 _,r.val,hn⟩)
private theorem eJk (s :lz) (cut:ℕ) : (Bs s cut).rank≤aWw s cut:= by
 calc
  (Bs s cut).rank ≤ ∑ i:sP s cut,(GU s i.1.val (balance i)).rank :=
    fS3 (fun i:sP s cut=>GU s i.1.val (balance i))
  _=aWw s cut:= by
    rw [Fintype.sum_sigma]
    simp only [aWw,balance,Finset.sum_fin_eq_sum_range]
    refine pQ rfl fun q hq => ?_
    rw [dite_eq_left (Finset.mem_range.mp hq)]
    refine pQ rfl fun u hu => ?_
    rw [dite_eq_left (Finset.mem_range.mp hu)]
    rfl
theorem proof :i4.c1 := by
 intro A s cut hs _ _ htail
 change (origin A s).rank≤aWw s cut
 rw [eIa]
 apply (gxA A s).trans
 rw [eIc hs htail]
 exact (G9 _ _ _).trans (eJk s cut)
end
end a9M
end
section
namespace cw9
noncomputable section
open i4 MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
private theorem eyF {s :lz} (hs :Rz s) {c b a :ℕ}
   (h: (⟨c,b,a⟩:Jet)∈s.E) {a' : ℕ} (ha :a' ≤ a) :
   (⟨c,b,a'⟩:Jet)∈s.E := by
 induction a with
 | zero =>
   rw [Kl ha]
   exact h
 | succ a ih =>
   rcases Nat.eq_or_lt_of_le ha with hEq | hlt
   · rw [hEq]
     exact h
   · exact ih (hs.lower _ h (Nat.succ_pos a)) (wR hlt)
private def bhv (F:Type*) [Field F] (A:ℕ) (s :lz) :
  zg F (qx F 2) :=
 z8 F (Df fun i:apU A s=>(oy A s i).polynomial)
private theorem dNL {F:Type*} [Field F] {A:ℕ} {s :lz}
  (i:apU A s) : (oy A s i).polynomial∈bhv F A s :=
 Submodule.subset_span (Set.mem_range_self i)
private theorem gDP {F:Type*} [Field F] {A:ℕ} {s :lz}
    (hs :Rz s) (center received :F) (i:apU A s) :
    globalPointTranslation center received (oy A s i).polynomial∈bhv F A s := by
  classical
  let col:=oy A s i
  change globalPointTranslation center received col.polynomial∈bhv F A s
  rw [Gk]
  simp only [wB,mD,pG,yU,globalPointTranslation_X,
    globalPointTranslation_Y_zero,globalPointTranslation_Y_succ]
  rw [add_comm (ov center),add_comm (ov received),add_pow,add_pow,
    vk,vk]
  apply Gi
  intro x hx
  rw [sH,vk]
  apply Gi
  intro a ha
  have hx' : x≤ i.2.val :=wR (Finset.mem_range.mp hx)
  have ha' : a≤ i.1.val.a :=wR (Finset.mem_range.mp ha)
  let j:Jet:=⟨i.1.val.c,i.1.val.b,a⟩
  have hj:j∈s.E := by
    rcases i with ⟨⟨⟨c,b,a₀⟩,hi⟩,i⟩
    exact eyF hs hi ha'
  have hq:j.q≤ i.1.val.q :=
    C4 (C4 ha' _) _
  have hwidth :width A s i.1.val≤width A s j :=
    C4 (Nat.sub_le_sub_left (oY N hq) _) _
  let l:apU A s :=⟨⟨j,hj⟩,⟨x,(hx'.trans_lt i.2.isLt).trans_le hwidth⟩⟩
  let coeff :F:=center^(col.x - x)*(col.x.choose x :F) *
    received^(col.y₀-a)*(col.y₀.choose a :F)
  have hterm :
      (c9 none^x*ov center^(col.x - x)*(col.x.choose x :qx F 2) *
        (c9 (some 0)^a*ov received^(col.y₀-a) *
          (col.y₀.choose a :qx F 2))) *
        (∏ j,c9 (some j.succ)^col.higher j) =
      coeff•(oy A s l).polynomial:= by
    rw [smul_eq_C_mul,Gk]
    change _=ov coeff*wB x a col.higher
    simp only [coeff,wB,mD,pG,map_natCast]
    ac_rfl
  rw [hterm]
  exact (bhv F A s).smul_mem coeff (dNL l)
private def aWq {F:Type*} [Field F] (A:ℕ) (s :lz)
  (center received :F) :Matrix (LowContactIndex 2 s.m) (apU A s) F :=
 fun row i=>localConstraintCoordinatesAt s.m center received (oy A s i).polynomial row
private theorem eMv {F:Type*} [Field F] {A:ℕ} {s :lz}
   (hs :Rz s) (center received :F) :
   (aWq A s center received).rank≤(aWq A s (0:F) 0).rank := by
 classical
 let L:=localConstraintCoordinatesAt (R:=F) (d:=2) s.m 0 0
 have hmap : (bhv F A s).map L =
     z8 F (Df (aWq A s (0:F) 0).col) := by
   rw [bhv,Submodule.map_span,← Set.range_comp]
   rfl
 have hspan:z8 F (Df (aWq A s center received).col) ≤
     z8 F (Df (aWq A s (0:F) 0).col) := by
   apply Submodule.span_le.mpr
   rintro _ ⟨i,rfl⟩
   rw [← hmap]
   exact ⟨globalPointTranslation center received (oy A s i).polynomial,
     gDP hs center received i,
     (yP.C42.dPU s.m center received (oy A s i).polynomial).symm⟩
 rw [G5 ,G5]
 have :=FiniteDimensional.span_of_finite (K:=F)
   (Set.finite_range (aWq A s (0:F) 0).col)
 exact Il hspan
private theorem dPe {R S ι κ:Type*} [zc R] [zc S]
   (φ:R →+* S) (m:ℕ) (centers received :ι→R) (cols :κ→SourceColumn 2) :
   (vh m centers received cols).map φ =
     vh m (fun i=>φ (centers i)) (fun i=>φ (received i)) cols := by
 ext row j
 simp only [Matrix.map_apply,localConstraintMatrix_apply]
 rw [← Aa ,map_unscaledLocalSubstitution]
 simp [SourceColumn.polynomial]
set_option maxHeartbeats 800000 in
private theorem eEu (A:ℕ) (s :lz) :
   (aWq A s (0:K) 0).rank≤aWf A s := by
 let φ:C9 →+* K:=xL C9 K
 let P:=vh s.m
   (fun _:Unit=>(0:C9)) (fun _=>0) (oy A s)
 let row:LowContactIndex 2 s.m→Unit×LowContactIndex 2 s.m:= fun r=>((),r)
 have hmap :P.map φ =
     vh s.m (fun _:Unit=>(0:K)) (fun _=>0) (oy A s) := by
   simpa only [p6] using
     dPe φ s.m (fun _:Unit=>(0:C9)) (fun _=>0) (oy A s)
 calc
   _=((P.map φ).submatrix row (id :apU A s→apU A s)).rank := by
     rw [hmap]
     rfl
   _≤(P.map φ).rank :=G9 _ _ _
   _≤P.rank :=Matrix.rank_map_le φ P
   _ = _:=rfl
private theorem gwH {ι:Type*} [Fintype ι] (r :ℕ) :
  (∑ _:ι,r)=Bf ι*r := by
 simp
theorem proof :i4.c2 := by
 intro A s hs _ w
 let M:=vh s.m (fun i=>node i) w (oy A s)
 change M.rank≤n*aWf A s
 apply (Matrix.rank_prod_rows_le_sum M).trans
 calc
   _ ≤ ∑ _:Node,aWf A s := by
     apply yQ
     intro i _
     change (aWq A s (node i) (w i)).rank≤aWf A s
     exact (eMv hs (node i) (w i)).trans (eEu A s)
   _ = _:= by rw [gwH,Kp]
end
end cw9
end
section
namespace apQ
noncomputable section
open i4 PolynomialDifferential
open scoped BigOperators
set_option maxRecDepth 4000
def c1 :Prop :=
 ∀ Q:Equation,Q≠0→Nonempty (bQP Q)
def c2 :Prop :=
  ∀ s,Rz s → ∀ G:Equation,ato s G → ∀ l:Fin k,
    (bmO G l).degreeOf (aU 2)≤t*(s.C - 1)+k - 2
theorem of_children (h1 :c1) (h2 :c2) :i4.c3:= by
 intro s hs Q hQ
 obtain ⟨F⟩:=h1 Q hQ.1
 let T:vj 2 :=⟨F.count,fun i=>bY (F.source i) (F.equation i)⟩
 have htotal:=d52 hQ F
 have hlocal (i:Fin F.count) :=eHq hQ (F.source_dvd i)
 refine ⟨T,⟨(d5P F).trans htotal.1,?_,htotal.1,htotal.2.1,htotal.2.2,?_⟩,?_⟩
 · intro i
   refine ⟨F.irreducible i,fun hd=>F.regular i ((F.irreducible i).prime.dvd_of_dvd_pow hd),?_⟩
   intro u hu j
   apply a2o
   intro hz
   exact hu.2 (by
     change cy u (T4 (F.source i)^t)=0
     rw [pG,hz,zero_pow (by decide :t≠0)])
 · intro i
   simp only [T,bY]
   refine ⟨b0p (hlocal i),?_⟩
   intro j
   exact eFC (G:=F.source i) hs (hlocal i) (h2 s hs (F.source i) (hlocal i)) j
 · intro f hf hr
   obtain ⟨i,hz,hp,hsep⟩:=F.Eh f hr
   refine ⟨i,?_⟩
   change Gp f∈(bY (F.source i) (F.equation i)).aN8
   refine ⟨ahT f,⟨hp,?_⟩,?_⟩
   · change cy (ahT f) (T4 (F.source i)^t)≠0
     rw [pG]
     exact pow_ne_zero _ hsep
   · exact dIj (F.source i) (F.equation i) f hf hz hsep
end
end apQ
end
section
namespace aFz
noncomputable section
open i4 MvPolynomial
def J8 {r :ℕ} (T:nq r) :uz (BL r) :=
 G2 {T.equation}
def GS (a d e :ℕ) :zg nU (BL 2) :=
  restrictSupport nU
    {u:Fin 3 →₀ ℕ | u.degree≤a∧u.weight oj≤d∧u (aU 2)≤e}
theorem aIz {a d e :ℕ} {P:BL 2} :
   P∈GS a d e ↔
     P.totalDegree≤a∧P.weightedTotalDegree oj≤d∧P.degreeOf (aU 2)≤e := by
 rw [GS,mem_restrictSupport_iff,totalDegree,Au,
   JM,JM,degreeOf_le_iff]
 exact ⟨fun h=>⟨fun _ hu=>(h hu).1,fun _ hu=>(h hu).2.1,fun _ hu=>(h hu).2.2⟩,
   fun ⟨ha,hd,he⟩ _ hu=>⟨ha _ hu,hd _ hu,he _ hu⟩⟩
theorem dyi {a d e a' d' e' : ℕ} (ha :a≤a') (hd:d≤d') (he :e≤e') :
  GS a d e≤GS a' d' e' := by
 intro P hP
 obtain ⟨h₁,h₂,h₃⟩:=aIz.mp hP
 exact aIz.mpr ⟨h₁.trans ha,h₂.trans hd,h₃.trans he⟩
instance (a d e :ℕ) :Module.Finite nU (GS a d e) :=
 Module.Finite.of_injective
  (Submodule.inclusion (show GS a d e≤ restrictTotalDegree (Fin 3) nU a from
    fun _ hP=>(mem_restrictTotalDegree _ _ _).mpr (aIz.mp hP).1))
  (Submodule.inclusion_injective _)
theorem bJy {a d e b j c:ℕ} {P Q:BL 2}
  (hP:P∈GS a d e) (hQ:Q∈GS b j c) :
  P*Q∈GS (a+b) (d+j) (e+c) := by
 obtain ⟨hP₁,hP₂,hP₃⟩:=aIz.mp hP
 obtain ⟨hQ₁,hQ₂,hQ₃⟩:=aIz.mp hQ
 exact aIz.mpr
  ⟨(totalDegree_mul _ _).trans (v8 hP₁ hQ₁),
   (weightedTotalDegree_mul_le _ _ _).trans (v8 hP₂ hQ₂),
   (degreeOf_mul_le _ _ _).trans (v8 hP₃ hQ₃)⟩
def aEl (T:nq 2) (a d e :ℕ) :
    zg nU (BL 2 ⧸ J8 T) :=
  (GS a d e).map (GF nU (J8 T)).toLinearMap
theorem eQt (T:nq 2) {a d e a' d' e' : ℕ}
  (ha :a≤a') (hd:d≤d') (he :e≤e') :
  aEl T a d e≤aEl T a' d' e' :=
 Submodule.map_mono (dyi ha hd he)
instance (T:nq 2) (a d e :ℕ) :Module.Finite nU (aEl T a d e) := by
 unfold aEl
 infer_instance
def anJ (a d e :ℚ) :ℚ :=
 (e+1)*(d+1-e)*(2*a+2 - d)/2
end
end aFz
end
section
namespace cxa
noncomputable section
open i4 apQ Polynomial PolynomialDifferential UniqueFactorizationMonoid
open scoped BigOperators
local instance :LO Equation :=
 Kh
local instance :LO (BL 2) :=
 Kh
private def cVd:Equation →+* BL 2 :=
 (qm (fun j:t6 (Fin 3) =>
   j.elim (ov lI) c9)).toRingHom.comp (lV oq)
private theorem cfE {G G' : Equation} {f :K[X]}
   (ha :Associated G G') (hG:oZ G f=0)
   (hS:oZ (separant G (aU 2)) f≠0) :
   oZ G' f=0 ∧
     oZ (separant G' (aU 2)) f≠0:= by
 obtain ⟨u,rfl⟩:=ha
 let ev :=differentialSpecializationHom f (d:=2)
 have hu:ev (u:Equation)≠0:=(u.isUnit.map ev).ne_zero
 change ev G=0 at hG
 change ev (separant G (aU 2))≠0 at hS
 change ev (G*u)=0∧ev (separant (G*u) (aU 2))≠0
 refine ⟨by rw [mD,hG,uW],?_⟩
 rw [separant,Fa ,qG,mD,mD,hG,uW,xI]
 exact mul_ne_zero hS hu
private theorem cfC {P:BL 2} (hP:P≠0) (u:Fin 3→nU)
  (h:cy u P=0) :
  ∃ g∈yB P,cy u g=0:= by
 have hd:=map_dvd (cy u) (prod_normalizedFactors hP).symm.dvd
 rw [h,zero_dvd_iff,map_multiset_prod,Multiset.prod_eq_zero_iff,Multiset.mem_map] at hd
 exact hd
theorem proof :apQ.c1 := by
  classical
  intro Q hQ
  let native :=(yB Q).toFinset
  let geometric (G:Equation) :=
    (yB (initial G)).toFinset.filter fun g => ¬ g∣T4 G
  let pairs :=native.sigma geometric
  let n:=pairs.card
  let e :Fin n ≃ ↥pairs :=(Fintype.equivFinOfCardEq (Fintype.card_coe pairs)).symm
  let entry (i:Fin n) :=(e i).val
  have hmember (i:Fin n) : (entry i).1∈native∧(entry i).2∈geometric (entry i).1 :=
    Finset.mem_sigma.mp (e i).property
  have hnative (i:Fin n) : (entry i).1∈yB Q :=
    Multiset.mem_toFinset.mp (hmember i).1
  have hgeometric (i:Fin n) :
      (entry i).2∈yB (initial (entry i).1) ∧
        ¬ (entry i).2∣T4 (entry i).1 := by
    obtain ⟨hm,hd⟩:=Finset.mem_filter.mp (hmember i).2
    exact ⟨Multiset.mem_toFinset.mp hm,hd⟩
  have hprod: (∏ a∈pairs,a.2)∣initial Q:= by
    have hnativeProd: (∏ G∈native,G)∣Q :=
      (Kv _).trans (prod_normalizedFactors hQ).dvd
    have hm:=map_dvd cVd hnativeProd
    rw [yU] at hm
    change (∏ a∈native.sigma geometric,a.2)∣cVd Q
    rw [Finset.prod_sigma]
    refine (Finset.prod_dvd_prod_of_dvd _ _ (fun G hG => ?_)).trans hm
    have hGne :=b6j (ne_zero_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hG))
    change (∏ g∈geometric G,g)∣initial G
    exact (Finset.prod_dvd_prod_of_subset _ _ id (FK _ _)).trans
      ((Kv _).trans (prod_normalizedFactors hGne).dvd)
  refine ⟨⟨n,fun i=>(entry i).1,fun i=>(entry i).2,
    fun i=>irreducible_of_normalized_factor _ (hnative i),
    fun i=>dvd_of_mem_normalizedFactors (hnative i),
    fun i=>irreducible_of_normalized_factor _ (hgeometric i).1,
    fun i=>dvd_of_mem_normalizedFactors (hgeometric i).1,
    fun i=>(hgeometric i).2,?_,?_⟩⟩
  · have heq : (∏ i:Fin n,(entry i).2) = ∏ a∈pairs,a.2 := by
      calc
        _ = ∏ a : ↥pairs,a.val.2 :=e.prod_comp (fun a : ↥pairs=>a.val.2)
        _ = _:=Finset.prod_coe_sort pairs (fun a=>a.2)
    rw [heq]
    exact hprod
  · intro f hreg
    obtain ⟨G,hGir,hGdvd,hGroot,hGsep⟩:=hreg
    obtain ⟨G',hGnative,hGassoc⟩:=exists_mem_normalizedFactors_of_dvd hQ hGir hGdvd
    obtain ⟨hroot,hsep⟩:=cfE hGassoc hGroot hGsep
    have hinitial :cy (ahT f) (initial G')=0:= by
      rw [bHS,hroot,p6]
    have hinitialSep:cy (ahT f) (T4 G')≠0:= by
      rw [eom]
      exact map_ne_zero_iff RG bch |>.mpr hsep
    have hne :=b6j (ne_zero_of_mem_normalizedFactors hGnative)
    obtain ⟨g,hgmem,hgroot⟩:=cfC hne (ahT f) hinitial
    have hgreg : ¬ g∣T4 G' := by
      intro hdvd
      have hm:=map_dvd (cy (ahT f)) hdvd
      rw [hgroot,zero_dvd_iff] at hm
      exact hinitialSep hm
    have hpair : (⟨G',g⟩:t5 fun _:Equation=>BL 2)∈pairs :=
      Finset.mem_sigma.mpr ⟨Multiset.mem_toFinset.mpr hGnative,
        Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hgmem,hgreg⟩⟩
    let a : ↥pairs :=⟨⟨G',g⟩,hpair⟩
    refine ⟨e.symm a,?_⟩
    change oZ (e (e.symm a)).val.1 f=0 ∧
      cy (ahT f) (e (e.symm a)).val.2=0 ∧
      cy (ahT f) (T4 (e (e.symm a)).val.1)≠0
    rw [e.apply_symm_apply]
    exact ⟨hroot,hgroot,hinitialSep⟩
end
end cxa
end
section
namespace cxb
noncomputable section
open i4 PolynomialDifferential MvPolynomial
open scoped BigOperators
set_option maxRecDepth 4000
private def U6 {L:ℕ} (i:Fin L) :ℕ:=i.val - 1
private def kO (L:ℕ) :t6 (Fin L)→ℕ :=
 fun i=>i.elim 0 U6
private theorem ep3 :
   kO 3=vw (some (aU 2)) 1 := by
 funext i
 cases i with
 | none=>simp [kO]
 | some j=>fin_cases j <;> decide
section Field
variable {F:Type*} [Field F]
private theorem cuu (L j:ℕ) :
  SupportWeightOffset (qM (kO L))
   (qM (amZ.aUb 1 L)) (j - 1)
   (universalTaylorJet (F:=F) L j) := by
 classical
 apply SupportWeightOffset.sum
 intro i hi
 apply SupportWeightOffset.monomial
 have hj:=(Finset.mem_filter.mp hi).2
 simp only [qG,FQ,C5 ,kO,
  amZ.aUb,U6,Option.elim_some,Option.elim_none,
  zf ,t7,sI,xI,mul_one]
 omega
private theorem cfh (L h:ℕ) (x :F) (Q:qx F 2)
    {c:ℕ} (hQ:Q.degreeOf (some (aU 2))≤ c)
    {m:Fin L →₀ ℕ}
    (hm:m∈((Gj F (Fin L) (FV L x Q)).coeff h).support) :
    qM U6 m≤h+c:= by
  have hres :SupportWeightOffset (qM (kO L))
      (qM (amZ.aUb 1 L))
      (Q.weightedTotalDegree (kO 3)) (FV L x Q) := by
    apply supportWeightOffset_aeval
    intro i
    cases i with
    | none =>
      apply SupportWeightOffset.add
      · exact SupportWeightOffset.C x
      · apply SupportWeightOffset.monomial
        simp [kO,amZ.aUb,FQ]
    | some j=>exact cuu L j.val
  have hw:=hres (m.optionElim h) ((mem_support_coeff_optionEquivLeft F).mp hm)
  change qM (fun i:t6 (Fin L)=>i.elim 0 U6) (m.optionElim h) ≤
    qM (fun i:t6 (Fin L)=>i.elim 1 (fun _=>0)) (m.optionElim h) +
      Q.weightedTotalDegree (kO 3) at hw
  rw [Finsupp.weight_elim_one_zero,Finsupp.optionElim_apply_none,
    Finsupp.weight_optionElim,uW,t7,ep3,
    t4] at hw
  exact hw.trans (x7 hQ h)
private theorem eop (l:ℕ) (hl:l<3) :
   (c9 (⟨l,hl⟩:Fin 3) :u5 (Fin 3) F).degreeOf (aU 2)≤l - 1 := by
 rw [degreeOf_X]
 split
 · rename_i he
   have he' := oD oj he
   change 2=l at he'
   omega
 · exact Nat.zero_le _
private theorem fTF (x :F) (Q:qx F 2) {c:ℕ}
    (hc:0<c) (hQ:Q.degreeOf (some (aU 2))≤ c) (l:ℕ) :
    (F9 x Q l).degreeOf (aU 2) ≤
      (2*(l - 2) - 1)*(c - 1)+(l - 1) := by
  have hsep:=(Gn x Q).trans (v9 hQ 1)
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [F9]
    split_ifs with hl
    · exact (eop (F:=F) l hl).trans (Nat.le_add_left _ _)
    · let R:=(Gj F (Fin l) (FV l x Q)).coeff (l - 2)
      have hden : ∀ m∈R.support,
          qM (fun i:Fin l=>2*(i.val - 2) - 1) m≤2*(l - 2) - 2 :=
        fun m hm=>denominator_weight_le_of_mem_universalTaylorResidual_coeff
          (r :=2) (K:=l) (h:=l - 2) (by omega) x Q m hm
      have hw : ∀ m∈R.support,qM U6 m≤(l - 2)+c :=
        fun _ hm=>cfh l (l - 2) x Q hQ hm
      have hd:=degreeOf_clearedSubstitution (aU 2) (initialJetSeparant x Q)
        (fun i:Fin l=>F9 x Q i.val)
        (fun i=>2*(i.val - 2) - 1) U6 (2*(l - 2) - 2) (c - 1)
        ((l - 2)+c) R hsep (fun i=>ih i.val i.isLt) hden hw
      have hstep:2*(l - 2) - 1=(2*(l - 2) - 2)+1 := by omega
      have hbudget: (l - 2)+c=(c - 1)+(l - 1) := by omega
      refine (degreeOf_mul_le _ _ _).trans ?_
      simp only [degreeOf_neg,degreeOf_C,t7]
      apply hd.trans
      rw [hstep,z9,sI,hbudget,FR]
private theorem dN7 (x :F) (Q:qx F 2) {c L τ:ℕ}
  (hc:0<c) (hQ:Q.degreeOf (some (aU 2))≤ c) (hτ:Et 2 L τ)
  (l:Fin L) :
  (commonTaylorNumerator x Q τ l.val).degreeOf (aU 2)≤τ*(c - 1)+(l.val - 1) := by
 have hsep:=(Gn x Q).trans (v9 hQ 1)
 let d:=2*(l.val - 2) - 1
 have he :τ - d+d=τ:=G0 (hτ l)
 unfold commonTaylorNumerator
 apply (degreeOf_mul_le _ _ _).trans
 apply (v8 (fTF x Q hc hQ l.val)
  ((degreeOf_pow_le _ _ _).trans (oY (τ - d) hsep))).trans
 change d*(c - 1)+(l.val - 1)+(τ - d)*(c - 1)≤_
 rw [Nat.add_right_comm,← z9,ze d (τ - d),he]
end Field
theorem proof :apQ.c2 := by
 intro s hs G hG l
 have htop: (apQ.dR G).degreeOf (some (aU 2))≤ s.C:= by
  change (lV oq G).degreeOf (some (aU 2))≤ s.C
  have hGtop:=hG.2.2.2
  simp only [jetDegree,degreeOf_def] at hGtop
  simp only [degreeOf_def]
  exact (Multiset.count_le_of_le _ (degrees_map_le (p:=G) (f :=oq))).trans hGtop
 have hb:=dN7 lI (apQ.dR G) hs.top_pos htop apQ.ayP l
 have hl:l.val - 1≤k - 2 := by have :=l.isLt; omega
 apply hb.trans
 rw [Nat.add_sub_assoc (by decide :2≤k)]
 exact x7 hl _
end
end cxb
end
section
namespace aFz
noncomputable section
open i4 MvPolynomial
section
variable {r :ℕ}
abbrev VF (T:nq r) :=
 Localization.Away (pU (J8 T) T.denominator)
def localize (T:nq r) :BL r →ₐ[nU] VF T :=
  (HZ nU (BL r ⧸ J8 T) (VF T)).comp
    (GF nU (J8 T))
def aOc (T:nq r) :VF T :=
 IsLocalization.Away.invSelf (pU (J8 T) T.denominator)
theorem cKm (T:nq r) :
  localize T T.denominator*aOc T=1 :=
 IsLocalization.Away.mul_invSelf (pU (J8 T) T.denominator)
def qR (T:nq r) :jo →ₐ[nU] VF T :=
 qm fun i=>localize T (T.numerator i)*aOc T
private theorem enS {T:nq r} {y :Fin (r+1)→nU}
  (hy :y∈T.aa0) :y∈qy nU (J8 T) := by
 apply mem_zeroLocus_iff_le_ker_aeval.mpr
 apply (Ideal.span_singleton_le_iff_mem _).mpr
 exact RingHom.mem_ker.mpr hy.1
private def Bt {T:nq r} {y :Fin (r+1)→nU} (hy :y∈T.aa0) :
  (BL r ⧸ J8 T) →ₐ[nU] nU :=
 Ideal.Quotient.liftₐ (J8 T) (qm y) fun q hq=>enS hy q hq
private def amk {T:nq r} {y :Fin (r+1)→nU} (hy :y∈T.aa0) :
  VF T →ₐ[nU] nU :=
 IsLocalization.Away.liftAlgHom (f :=Bt hy)
  (pU (J8 T) T.denominator) (isUnit_iff_ne_zero.mpr hy.2)
private theorem aII {T:nq r} {y :Fin (r+1)→nU} (hy :y∈T.aa0)
  (q:BL r) :amk hy (localize T q)=eval y q :=
 IsLocalization.Away.lift_eq (g:=(Bt hy).toRingHom)
  (pU (J8 T) T.denominator) (isUnit_iff_ne_zero.mpr hy.2)
  (pU (J8 T) q)
private theorem bfV {T:nq r} {y :Fin (r+1)→nU} (hy :y∈T.aa0)
  (q:jo) :amk hy (qR T q)=eval (T.output y) q:= by
 have hu:=oD (amk hy) (cKm T)
 rw [mD,aII,map_one] at hu
 have hi:amk hy (aOc T)=(eval y T.denominator)⁻¹:= by
  rw [← one_div]
  exact (eq_div_iff hy.2).mpr ((p9 _ _).trans hu)
 have h: (amk hy).comp (qR T)=qm (T.output y) := by
  apply LQ
  intro i
  change amk hy (qR T (c9 i))=qm (T.output y) (c9 i)
  rw [qR,aeval_X,mD,aII,hi,aeval_X,Chart.output,div_eq_mul_inv]
 exact vl h q
private theorem cMz {T:nq r} [(J8 T).IsPrime]
    (hD:T.denominator∉J8 T) {z :VF T}
    (hz : ∀ y (hy :y∈T.aa0),amk hy z=0) :z=0:= by
  obtain ⟨m,a,ha⟩:=IsLocalization.Away.surj
    (pU (J8 T) T.denominator) z
  obtain ⟨q,rfl⟩:=Ideal.Quotient.mk_surjective a
  change z*localize T T.denominator^m=localize T q at ha
  have hq:q∈J8 T:= by
    have hmul :T.denominator*q∈J8 T:= by
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K:=nU) (J8 T)]
      intro y hy
      change eval y (T.denominator*q)=0
      by_cases hyD:eval y T.denominator=0
      · rw [mD,hyD,uW]
      · have hy' : y∈T.aa0:=⟨hy _ (Ideal.subset_span (by simp)),hyD⟩
        have he :=oD  (amk hy') ha
        rw [mD ,pG ,aII,aII,hz y hy',uW ] at he
        rw [mD ,← he,zf ]
    exact (‹(J8 T).IsPrime›.mem_or_mem hmul).resolve_left hD
  have hq0:localize T q=0:= by
    change xL (BL r ⧸ J8 T) (VF T)
      (pU (J8 T) q)=0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq,p6]
  rw [hq0] at ha
  exact ((G7 (S:=VF T)
    (pU (J8 T) T.denominator)).pow m).mul_right_cancel
      (ha.trans (uW _).symm)
theorem bHO (T:nq r) [(J8 T).IsPrime]
   (hD:T.denominator∉J8 T) :T.ideal=RingHom.ker (qR T).toRingHom:= by
 ext q
 change q∈vanishingIdeal nU T.aN8↔qR T q=0
 constructor
 · intro hq
   apply cMz hD
   intro y hy
   rw [bfV hy]
   exact hq _ ⟨y,hy,rfl⟩
 · intro hq
   rintro _ ⟨y,hy,rfl⟩
   change eval (T.output y) q=0
   rw [← bfV hy,hq,p6]
private def KT (j:ℕ) :jo :=
 ∑ i:Fin k,C ((i.val.choose j:nU)*lI ^(i.val-j))*c9 i
private theorem d2w (y :Fin k→nU) (j:ℕ) :
  eval y (KT j)=awb y j:= by
 simp [KT,awb]
private theorem dH7 (T:nq r) (hT:aAQ T) [(J8 T).IsPrime]
  (hD:T.denominator∉J8 T) :
  (qR T).comp (qm fun j:Fin (r+1)=>KT j.val)=localize T:= by
 apply LQ
 intro j
 change qR T (qm (fun j:Fin (r+1)=>KT j.val) (c9 j)) =
  localize T (c9 j)
 rw [aeval_X,← EP]
 apply cMz hD
 intro y hy
 rw [map_sub,bfV,aII,d2w,eval_X,hT.recover y hy j,sub_self]
theorem enK (T:nq r) (hT:aAQ T) :
   T.ideal.IsPrime∧(pL T.ideal).natDegree=r := by
 have hprime : (J8 T).IsPrime :=
   Mz hT.irreducible.ne_zero |>.mpr hT.irreducible.prime
 let:=hprime
 have hD:T.denominator∉J8 T :=
   fun h=>hT.nonvanishing (Ideal.mem_span_singleton.mp h)
 have hne :pU (J8 T) T.denominator≠0 :=
   mt Ideal.Quotient.eq_zero_iff_mem.mp hD
 let:IsDomain (VF T) :=Localization.Away.isDomain hne
 have hreg:=(IsRegular.of_ne_zero hne).1
 have hsource : (pL (J8 T)).natDegree=r := by
   have h:=natDegree_affineHilbertPolynomial_span_singleton_add_one
     hT.irreducible.ne_zero hprime.ne_top
   rw [Nat.card_fin] at h
   exact Nat.add_right_cancel h
 rw [bHO T hD]
 refine ⟨RingHom.ker_isPrime _,Eq.trans (le_antisymm ?_ ?_) hsource⟩
 · let E :=awayPresentationEquiv (J8 T) T.denominator
   exact (natDegree_affineHilbertPolynomial_le_of_injective
     (E.symm.toAlgHom.comp (Ideal.kerLiftAlg (qR T)))
     (E.symm.injective.comp (Mw (qR T)))).trans
     (natDegree_affineHilbertPolynomial_awayPresentationIdeal_le (J8 T) T.denominator)
 · exact natDegree_affineHilbertPolynomial_le_of_away_range (J8 T) T.denominator hreg
     (qR T)
     (fun q=>⟨_,vl (dH7 T hT hD) q⟩) th
end
end
end aFz
end
section
namespace aFz
noncomputable section
open i4 MvPolynomial Filter
open scoped BigOperators
def c1 :Prop :=
  ∀ (T:nq 2) (a d e :ℕ),aAQ T →
    T.denominator∈GS a d e →
    (∀ i,T.numerator i∈GS a d e) →
    ∀ m:ℕ,affineHilbertFunction T.ideal m ≤
      qJ nU (aEl T (m*a) (m*d) (m*e))
def c2 :Prop :=
  ∀ (a d e :ℕ),d≤a→2*e≤d →
    (qJ nU (GS a d e) :ℚ)=anJ a d e
private theorem eQs (T:nq 2) (a d e b j c:ℕ)
   (hn:T.equation≠0) (hf :T.equation∈GS b j c) :
   qJ nU (aEl T (a+b) (d+j) (e+c)) +
     qJ nU (GS a d e) ≤
     qJ nU (GS (a+b) (d+j) (e+c)) := by
 let W:=GS (a+b) (d+j) (e+c)
 let F:=(GF nU (J8 T)).toLinearMap.domRestrict W
 have hF:LinearMap.range F=aEl T (a+b) (d+j) (e+c) :=
   LinearMap.range_domRestrict W _
 let mul :=(G4 nU T.equation).domRestrict (GS a d e)
 have hmul (p:GS a d e) :mul p∈W:= by
   simpa only [mul,W,LinearMap.domRestrict_apply,LinearMap.mulLeft_apply,ze]
     using bJy hf p.property
 let g:GS a d e →ₗ[nU] W:=mul.codRestrict W hmul
 have hg (p:GS a d e) :g p∈Eg F:= by
   apply LinearMap.mem_ker.mpr
   change pU (J8 T) (T.equation*p.val)=0
   exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨p.val,rfl⟩)
 let G:=g.codRestrict (Eg F) hg
 have hG:sS G:= by
   intro p q hpq
   have he :T.equation*p.val=T.equation*q.val :=
     oD (fun x :Eg F=>x.val.val) hpq
   exact xm (mul_left_cancel₀ hn he)
 have hRank :=F.finrank_range_add_finrank_ker
 rw [hF] at hRank
 exact (x7 (FU hG) _).trans_eq hRank
private def aJJ (a d e b j c:ℚ) :ℚ :=
 2*e*(d-e)*b+e*(2*a-2*d+e)*j+(d-2*e)*(2*a-d)*c
private abbrev qE (P:BL 2) :ℕ :=
 P.weightedTotalDegree oj
private theorem dyj (a d e b j c:ℚ) :
    ∃ u v :ℚ,∀ x :ℚ,
      anJ (x*a+j+2*c+b) (x*d+2*c+j) (x*e+c) -
        anJ (x*a+j+2*c) (x*d+2*c) (x*e) =
      (aJJ a d e b j c/2)*x^2+u*x+v := by
  let f (x :ℚ) :=
    anJ (x*a+j+2*c+b) (x*d+2*c+j) (x*e+c) -
      anJ (x*a+j+2*c) (x*d+2*c) (x*e)
  refine ⟨f 1 - f 0-aJJ a d e b j c/2,f 0,fun x => ?_⟩
  dsimp [f,anJ,aJJ]
  ring
private theorem dVw
    (I:uz jo) (hdim: (pL I).natDegree=2)
    (q u v :ℚ) (hle : ∀ᶠ m:ℕ in atTop,
      (pL I).eval (m:ℚ)≤q*(m:ℚ)^2+u*(m:ℚ)+v) :
    ox I≤2*q:= by
  let P:yJ ℚ:=lJ q*nX ^2 +
    lJ u*nX+Polynomial.C v
  have hP : ∀ᶠ m:ℕ in atTop,(pL I).eval (m:ℚ)≤P.eval (m:ℚ) := by
    filter_upwards [hle] with m hm
    simpa [P] using hm
  obtain ⟨hnat,hlead⟩:=Polynomial.natDegree_le_of_eventually_eval_natCast_le
    (eventually_eval_affineHilbertPolynomial_nonneg I) hP
  have hdeg:P.natDegree=2 := by
    apply le_antisymm
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro i hi
      have h₀:i≠0:= by omega
      have h₁:i≠1 := by omega
      have h₂:i≠2 := by omega
      simp only [P,Polynomial.coeff_add,Kz ,
        Polynomial.coeff_C_mul_X,Polynomial.coeff_C]
      simp [h₀,h₁,h₂]
    · simpa only [hdim] using hnat
  have hc:P.leadingCoeff=q:= by
    rw [Polynomial.leadingCoeff,hdeg]
    simp [P]
  have hcoeff :=hlead (hdim.trans hdeg.symm)
  rw [hc] at hcoeff
  rw [ox ,hdim]
  exact t8 hcoeff (by norm_num)
private theorem adr (h1 :c1) (h2 :c2)
    (T:nq 2) (hT:aAQ T) (hdim: (pL T.ideal).natDegree=2)
    (a d e :ℕ) (hda :d≤a) (hed:2*e≤d)
    (hD:T.denominator∈GS a d e) (hN : ∀ i,T.numerator i∈GS a d e) :
    ox T.ideal≤aJJ a d e T.equation.totalDegree
      (qE T.equation)
      (T.equation.degreeOf (aU 2)) := by
  let b:=T.equation.totalDegree
  let j:=qE T.equation
  let c:=T.equation.degreeOf (aU 2)
  have hf :T.equation∈GS b j c:=aIz.mpr ⟨th,th,th⟩
  obtain ⟨u,v,hexpand⟩:=dyj a d e b j c
  have hle : ∀ᶠ m:ℕ in atTop,(pL T.ideal).eval (m:ℚ) ≤
      (aJJ a d e b j c/2)*(m:ℚ)^2+u*(m:ℚ)+v := by
    filter_upwards [eventually_eval_affineHilbertPolynomial T.ideal] with m hm
    have hma :=oY m hda
    have hme :2*(m*e)≤ m*d:= by
      simpa only [Nat.mul_left_comm 2 m e] using oY m hed
    have hmono:qJ nU (aEl T (m*a) (m*d) (m*e)) ≤
        qJ nU (aEl T (m*a+j+2*c+b) (m*d+2*c+j) (m*e+c)) :=
      Il (eQt T (by omega) (by omega) (by omega))
    have hdimNat :=(C4 ((h1 T a d e hT hD hN m).trans hmono) _).trans
      (eQs T (m*a+j+2*c) (m*d+2*c) (m*e) b j c hT.irreducible.ne_zero hf)
    have hdimRat :=(Nat.cast_le (α:=ℚ)).mpr hdimNat
    rw [Nat.cast_add,
      h2 (m*a+j+2*c) (m*d+2*c) (m*e) (by omega) (by omega),
      h2 (m*a+j+2*c+b) (m*d+2*c+j) (m*e+c) (by omega) (by omega)] at hdimRat
    push_cast at hdimRat
    rw [hm,← hexpand (m:ℚ)]
    exact le_sub_iff_add_le.mpr hdimRat
  calc
    _≤2*(aJJ a d e b j c/2) :=
      dVw T.ideal hdim (aJJ a d e b j c/2) u v hle
    _ = _:= by ring
private theorem Tn (s :lz) (hs :Rz s) :
   D s≤a₀ s∧2*e s≤D s := by
 constructor
 · have hC:=hs.top_pos
   have hJ:=hs.index_top
   have hB:=hs.aQV
   change 262137*(s.J-2)+131072 - 1≤1+262137*(s.B-1)
   omega
 · have he :e s≤D s/2 :=min_le_right _ _
   omega
private theorem d6h (s :lz) (hs :Rz s) (F:vj 2) (hF:bQQ s F)
    (hdeg : ∀ i,ox (F.bY i).ideal ≤
      aJJ (a₀ s) (D s) (e s) (F.bY i).equation.totalDegree
        (qE (F.bY i).equation)
        ((F.bY i).equation.degreeOf (aU 2))) :
    (∑ i,ox (F.bY i).ideal)≤(R₂ s :ℚ) := by
  obtain ⟨hda,hde⟩:=Tn s hs
  let a :ℚ:=a₀ s
  let d:ℚ:=D s
  let e₀:ℚ:=e s
  have hdaQ:d≤a := by
    change (D s :ℚ)≤(a₀ s :ℚ)
    exact_mod_cast hda
  have hdeQ:2*e₀≤d:= by
    change 2*(e s :ℚ)≤(D s :ℚ)
    exact_mod_cast hde
  have heQ:0≤e₀:=zh _
  let u:=2*e₀*(d-e₀)
  let v :=e₀*(2*a-2*d+e₀)
  let w:=(d-2*e₀)*(2*a-d)
  have hu:0≤u:=vH (vH (by norm_num) heQ) (by linarith)
  have hv :0≤v :=vH heQ (by linarith)
  have hw:0≤w:=vH (by linarith) (by linarith)
  have hb: (∑ i,((F.bY i).equation.totalDegree :ℚ))≤(s.B:ℚ) := by
    exact_mod_cast hF.total
  have hj: (∑ i,(qE (F.bY i).equation :ℚ))≤(s.J:ℚ) := by
    exact_mod_cast hF.index
  have hc: (∑ i,((F.bY i).equation.degreeOf (aU 2) :ℚ))≤(s.C:ℚ) := by
    exact_mod_cast hF.top
  have hD' : D s≤2*a₀ s := by omega
  have hJ' : s.J≤2*s.B:= by have :=hs.aQV; omega
  have he' : e s≤D s := by omega
  have hC' : 2*s.C*e s≤ s.C*D s+e s*s.J:= by
    calc
      _=s.C*(2*e s) := by ring
      _≤ s.C*D s :=oY _ hde
      _≤_:=yl _ _
  calc
    _ ≤ ∑ i,aJJ a d e₀ (F.bY i).equation.totalDegree
        (qE (F.bY i).equation)
        ((F.bY i).equation.degreeOf (aU 2)) :=yQ fun i _=>hdeg i
    _=u*(∑ i,((F.bY i).equation.totalDegree :ℚ)) +
        v*(∑ i,(qE (F.bY i).equation :ℚ)) +
        w*(∑ i,((F.bY i).equation.degreeOf (aU 2) :ℚ)) := by
      simp only [aJJ,u,v,w,sH,vi]
    _≤u*s.B+v*s.J+w*s.C :=
      Av (Av (t8 hb hu) (t8 hj hv))
        (t8 hc hw)
    _=(R₂ s :ℚ) := by
      dsimp [u,v,w,a,d,e₀,R₂]
      push_cast [wY hD',wY hJ',wY he',wY hC']
      ring
theorem of_children (h1 :c1) (h2 :c2) :i4.c4 := by
 intro s hs F hF
 have hg:= fun i=>enK (F.bY i) (hF.bct i)
 refine ⟨fun i=>(hg i).1,fun i=>(hg i).2,d6h s hs F hF ?_⟩
 obtain ⟨hda,hde⟩:=Tn s hs
 intro i
 exact adr h1 h2 (F.bY i) (hF.bct i) (hg i).2 (a₀ s) (D s) (e s)
  hda hde (aIz.mpr (hF.bands i).1) (fun j=>aIz.mpr ((hF.bands i).2 j))
end
end aFz
end
section
namespace cxc
noncomputable section
open i4 aFz MvPolynomial
theorem proof :aFz.c1 := by
  intro T a d e hT hD hN m
  let: (J8 T).IsPrime :=
    (Mz hT.irreducible.ne_zero).mpr hT.irreducible.prime
  have hD' : T.denominator∉J8 T :=
    fun h=>hT.nonvanishing (Ideal.mem_span_singleton.mp h)
  rw [bHO T hD']
  let j:=HZ nU (BL 2 ⧸ J8 T) (VF T)
  let δ:=localize T T.denominator
  have hδ:IsUnit δ :=
    G7 (S:=VF T)
      (pU (J8 T) T.denominator)
  let y (i:Fin k) :=localize T (T.numerator i)*aOc T
  have hy (i:Fin k) :δ*y i=localize T (T.numerator i) := by
    change localize T T.denominator*(localize T (T.numerator i)*aOc T)= _
    rw [mul_left_comm _ (localize T (T.numerator i)),cKm,mul_one]
  let V (n:ℕ) :zg nU (VF T) :=
    (aEl T (n*a) (n*d) (n*e)).map j.toLinearMap
  let W (n:ℕ) :zg nU (VF T) :=
    (V n).comap (G4 nU (δ^n))
  have hW (n:ℕ) (z :VF T) :
      z∈W n ↔ ∃ P∈GS (n*a) (n*d) (n*e),localize T P=δ^n*z := by
    change δ^n*z∈V n↔_
    simp only [V,aEl,← Submodule.map_comp,← AlgHom.comp_toLinearMap,
      Submodule.mem_map,AlgHom.toLinearMap_apply,localize,j]
  have hOne : (1 :BL 2)∈GS 0 0 0:= by
    have hw:Au oj (1 :BL 2)=0:= by
      rw [← C_1,weightedTotalDegree_C]
    exact aIz.mpr ⟨totalDegree_one.le,hw.le,(degreeOf_one _).le⟩
  have hpow (n:ℕ) :
      T.denominator^n∈GS (n*a) (n*d) (n*e) := by
    induction n with
    | zero=>simpa only [pow_zero,Nat.zero_mul] using hOne
    | succ n ih=>simpa only [pow_succ,Nat.succ_mul] using bJy ih hD
  have hmono:Monotone W:= by
    intro n l hnl z hz
    obtain ⟨P,hP,heq⟩:=(hW _ _).mp hz
    refine (hW _ _).mpr ⟨T.denominator^(l - n)*P,?_,?_⟩
    · simpa only [← z9,G0 hnl] using
        bJy (hpow (l - n)) hP
    · rw [mD,pG,heq,← vG,← pow_add,G0 hnl]
  have hmul (i:Fin k) (n:ℕ) (z :VF T) (hz :z∈W n) :
      y i*z∈W (n+1) := by
    obtain ⟨P,hP,heq⟩:=(hW _ _).mp hz
    refine (hW _ _).mpr ⟨P*T.numerator i,?_,?_⟩
    · simpa only [z9,Nat.one_mul] using bJy hP (hN i)
    · rw [mD,heq,← hy i,pow_succ]
      ac_rfl
  have h0: (1 :VF T)∈W 0 :=
    (hW _ _).mpr ⟨1,by simpa only [Nat.zero_mul] using hOne,by simp⟩
  have hclear (P:jo) (hP:P.totalDegree≤ m) :qR T P∈W m:= by
    change qm y P∈W m
    simpa only [Nat.one_mul] using
      (aeval_mem_of_forall_mul_mem y hmono h0 hmul hP)
  let Q:=RingHom.ker (qR T).toRingHom
  let ι: (jo ⧸ Q) →ₐ[nU] VF T:=Ideal.kerLiftAlg (qR T)
  have hmem (x :quotientDegreeLE Q m) :δ^m*ι x.val∈V m:= by
    obtain ⟨P,hP,heq⟩:=mem_quotientDegreeLE.mp x.property
    change ι x.val∈W m
    rw [← heq]
    change qR T P∈W m
    exact hclear P hP
  let L:quotientDegreeLE Q m →ₗ[nU] V m :=
    (((G4 nU (δ^m)).comp ι.toLinearMap).domRestrict
      (quotientDegreeLE Q m)).codRestrict (V m) hmem
  have hL:sS L:= by
    intro x z hxz
    have h:δ^m*ι x.val=δ^m*ι z.val :=oD uJ hxz
    exact xm (Mw (qR T) ((hδ.pow m).mul_left_cancel h))
  exact (FU hL).trans (Submodule.finrank_map_le _ _)
end
end cxc
end
section
namespace cxd
noncomputable section
open i4 aFz MvPolynomial
open scoped BigOperators
private abbrev dmD (a d e :ℕ) :Set (Fin 3 →₀ ℕ) :=
 {u | u.degree≤a∧u.weight oj≤d∧u (aU 2)≤e}
private theorem boR (u:Fin 3 →₀ ℕ) :
  u.degree=u 0+u 1+u 2 := by
 rw [In,EK,add_assoc]
private theorem degree_fin_two (u:Fin 2 →₀ ℕ) :u.degree=u 0+u 1 := by
 rw [In,zi]
private theorem cU7 (u:Fin 3 →₀ ℕ) :
  u.weight oj=u 1+2*u 2 := by
 simp [Finsupp.weight_eq_sum,EK,zE]
private def dyh (a d e :ℕ) (hda :d≤a) (hed:2*e≤d) :
  dmD a d e ≃ Σ z :Fin (e+1),
   cappedDegreeExponents (Fin 2) 1 (a - z) (d - 2*z) where
 toFun u:= by
  have htotal:=u.property.1
  have hindex :=u.property.2.1
  have htop:=u.property.2.2
  rw [boR] at htotal
  rw [cU7] at hindex
  change u.val 2≤e at htop
  let z :Fin (e+1) :=⟨u.val 2,Nat.lt_succ_of_le htop⟩
  refine ⟨z,⟨Finsupp.equivFunOnFinite.symm ![u.val 0,u.val 1],?_⟩⟩
  rw [mem_cappedDegreeExponents,degree_fin_two]
  change u.val 0+u.val 1≤a - u.val 2∧u.val 1≤d - 2*u.val 2
  omega
 invFun p:= by
  obtain ⟨z,u⟩:=p
  have htotal:=u.property.1
  rw [degree_fin_two] at htotal
  have hindex :=u.property.2
  have hz :=z.isLt
  let v :Fin 3 →₀ ℕ:=Finsupp.equivFunOnFinite.symm ![u.val 0,u.val 1,z.val]
  refine ⟨v,?_⟩
  change v.degree≤a∧v.weight oj≤d∧v (aU 2)≤e
  rw [boR,cU7]
  change u.val 0+u.val 1+z.val≤a∧u.val 1+2*z.val≤d∧z.val≤e
  omega
 left_inv u:= by
  apply xm
  ext i
  fin_cases i <;> rfl
 right_inv p:= by
  rcases p with ⟨⟨z,hz⟩,u⟩
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply xm
  ext i
  fin_cases i <;> rfl
private theorem bxb (d e :ℕ) (hed:2*e≤d) :
    (∑ z∈t3 (e+1),(d - 2*z+1))=(e+1)*(d+1-e) := by
  calc
    _ = ∑ z∈t3 (e+1),(d - 2*(e - z)+1) := by
      symm
      simpa only [G6] using
        Finset.sum_range_reflect (fun z=>d - 2*z+1) (e+1)
    _ = ∑ z∈t3 (e+1),((d - 2*e+1)+2*z) := by
      apply pQ rfl
      intro z hz
      have hz' := Finset.mem_range.mp hz
      omega
    _ = _:= by
      rw [vi ,Ef ,Finset.card_range,Nat.nsmul_eq_mul,
        ← sH,p9 2 (∑ z∈t3 (e+1),z),
        Finset.sum_range_id_mul_two,G6,← Nat.mul_add]
      congr 1
      omega
private theorem gEX (a d e :ℕ) (hda :d≤a) (hed:2*e≤d) :
    2*qJ nU (GS a d e)=(e+1)*(d+1-e)*(2*a+2 - d) := by
  rw [GS,Module.finrank_eq_nat_card_basis (basisRestrictSupport nU _),
    Nat.card_congr (dyh a d e hda hed),Nat.card_sigma,sH]
  calc
    _ = ∑ z :Fin (e+1),(d - 2*z.val+1)*(2*a+2 - d) := by
      apply pQ rfl
      intro z _
      have hz :=z.isLt
      have hcap:d - 2*z.val≤a - z.val := by omega
      rw [Nat.card_coe_set_eq,two_mul_ncard_cappedDegreeExponents_fin_two _ _ hcap]
      congr 1
      omega
    _ = _:= by
      rw [← vk,KA (fun z=>d - 2*z+1),
        bxb d e hed]
theorem proof :aFz.c2 := by
 intro a d e hda hed
 have he :e≤d+1 := by omega
 have hd:d≤2*a+2 := by omega
 have h:=oD (fun n:ℕ=>(n:ℚ)) (gEX a d e hda hed)
 push_cast [wY he,wY hd] at h
 unfold anJ
 apply (eq_div_iff (by norm_num : (2 :ℚ)≠0)).2
 rw [p9]
 exact h
end
end cxd
end
section
namespace anj
noncomputable section
open aR jA MvPolynomial
open scoped Polynomial BigOperators
private theorem al5:sS qV :=
 GR ao[X] iP
theorem afo {σ:Type*} (f :u5 σ iP) :
    ∃ (d:ao[X]) (P:u5 σ ao[X]),d≠0∧P.support=f.support ∧
      lV qV P=C (qV d)*f := by
  classical
  let M:=nonZeroDivisors (ao[X])
  let d:=IsLocalization.commonDenom M f.support f.coeff
  let num :=IsLocalization.integerMultiple M f.support f.coeff
  let P:u5 σ ao[X] := ∑ a : ↥f.support,qU a.val (num a)
  have hd: (d:ao[X])≠0:=nonZeroDivisors.coe_ne_zero d
  have hi:qV (d:ao[X])≠0:=(map_ne_zero_iff qV al5).mpr hd
  have hP:lV qV P=C (qV d)*f := by
    ext m
    simp only [Aa ,Dw ,P,coeff_sum]
    by_cases hm:m∈f.support
    · let a : ↥f.support :=⟨m,hm⟩
      rw [LR a (u9 a)]
      · have hn:=IsLocalization.map_integerMultiple M f.support f.coeff a
        change qV (num a)=(d:ao[X])•f.coeff a.val at hn
        rw [Algebra.smul_def] at hn
        simpa [a] using hn
      · intro b _ hba
        have hb:b.val≠m:= fun h=>hba (xm h)
        simp [Dz ,hb]
    · have hz :f.coeff m=0:= by simpa [MvPolynomial.mem_support_iff] using hm
      have hz' : (∑ a : ↥f.support,(qU  a.val (num a) :u5  σ ao[X]).coeff m)=0:= by
        apply y5
        intro a _
        have ha :a.val≠m:= fun h=>hm (h ▸ a.property)
        simp [Dz ,ha]
      rw [hz',hz,p6 ,zf ]
  refine ⟨d,P,hd,?_,hP⟩
  rw [← support_map_of_injective P al5,hP]
  ext m
  simp [GB,Dw ,hi]
private def lX (P:jK) :jK :=
 ∑ m∈P.support,qU m (pz (P.coeff m))
@[simp] private theorem ajn (P:jK) (m:mA →₀ ℕ) :
    (lX P).coeff m=pz (P.coeff m) := by
  classical
  rw [lX,coeff_sum]
  simp only [Dz ,Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [notMem_support_iff.mp hm,p6]
private theorem aTO (c:ao[X]) :
  lX (C c)=C (pz c) := by
 ext m
 by_cases hm:0=m <;> simp [coeff_C,hm]
private theorem aCH (P Q:jK) :
  lX (P+Q)=lX P+lX Q:= by
 ext m
 simp
private theorem bnr (P:jK) (j:mA) :
  lX (P*c9 j)=lX P*c9 j:= by
 ext m
 rw [ajn,coeff_mul_X',coeff_mul_X']
 split_ifs <;> simp
private theorem aNu (P:jK) (a :mA→ao[X]) :
    pz (eval a P)=eval a (lX P) +
      ∑ i,pz (a i)*eval a (pC i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [aTO]
  | add P Q hP hQ =>
    simp only [qG,aCH,hP,hQ,mul_add,vi]
    ring
  | mul_X P j ih =>
    rw [mD,eval_X,Polynomial.derivative_mul,ih,bnr,
      mD,eval_X]
    simp only [Fa ,qG,mD,eval_X,mul_add,vi]
    have left: (∑ i,pz (a i)*(eval a (pC i P)*a j)) =
        (∑ i,pz (a i)*eval a (pC i P))*a j:= by
      simp only [vk,vG]
    have right: (∑ i,pz (a i)*(eval a P*eval a (pC i (c9 j)))) =
        pz (a j)*eval a P:= by
      simp [pderiv_X,Pi.single_apply,mul_ite]
    rw [left,right]
    ring
private def afx {R:Type*} [zc R] (r P:VP R) :VP R :=
 r+MvPolynomial.X (some 1)*pC (some 0) P +
   C (2 :R)*(c9 (some 2)*pC (some 1) P)
private def ZW (z :ao) (S:ao[X]) :mA→ao[X] :=
 fun i=>i.elim (lJ z) (jet S)
private theorem aNh (S:ao[X]) (k :ℕ) :
  pz (vZ k S) =
   lJ ((k+1 :ℕ) :ao)*vZ (k+1) S:= by
 have h:=LinearMap.congr_fun (Polynomial.hasseDeriv_comp (R:=ao) 1 k) S
 simpa [Polynomial.hasseDeriv_one',Nat.choose_one_right,nsmul_eq_mul,
  Polynomial.C_eq_natCast,ze,add_mul] using h
private theorem b1V (P:jK) (z :ao) (S:ao[X])
   (htop:P.degreeOf (some 2)=0) :
   eval (ZW z S) (afx (lX P) P) =
     pz (eval (ZW z S) P) := by
 have hzero :=Mj htop
 have h₀:pz (ZW z S (some 0)) =
     ZW z S (some 1) := by
   simp [ZW,jet]
 have h₁:pz (ZW z S (some 1)) =
     lJ (2 :ao)*ZW z S (some 2) := by
   simpa [ZW,jet] using aNh S 1
 have hz :pz (ZW z S none)=0 :=
   Polynomial.derivative_C
 rw [aNu,Fintype.sum_option,EK]
 simp only [afx,qG,mD,eval_X,eval_C,h₀,h₁,hzero,hz,p6,zf ,
   xI,uW]
 rw [map_ofNat (lJ:ao →+* ao[X])]
 ring
private theorem aUp (z :ao) (S:ao[X]) (P:jK) :
   eval (ED (DI z) (jW S)) (lV qV P) =
     qV (eval (ZW z S) P) := by
 have hpoint :ED (DI z) (jW S)=qV ∘ ZW z S:= by
   funext i
   cases i with
   | none=>exact RingHom.congr_fun (IsScalarTower.algebraMap_eq ao ao[X] iP) z
   | some i=>rfl
 rw [hpoint,LP]
 exact (G8 qV (ZW z S) P).symm
private theorem bZ4 {P Q:ko} (h:P.support⊆Q.support)
  (i:mA) :P.degreeOf i≤Q.degreeOf i:= by
 apply degreeOf_le_iff.mpr
 intro m hm
 exact le_degreeOf_of_mem_support i (h hm)
private theorem c0T (w:mA→ℕ) (i j:mA) (P:ko) (d:ℕ)
   (h:w j≤w i+d) :
   (c9 j*pC i P).weightedTotalDegree w≤P.weightedTotalDegree w+d:= by
 apply Finset.sup_le
 intro m hm
 rw [GB,coeff_X_mul'] at hm
 split_ifs at hm with hj
 · have hn:m-Finsupp.single j 1+Finsupp.single i 1∈P.support := by
     rw [coeff_pderiv] at hm
     exact MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hm)
   have hw:=Ee w hn
   have he :=Finsupp.weight_sub_single_add (w:=w) (Finsupp.mem_support_iff.mp hj)
   rw [qG,FQ,one_smul] at hw
   omega
 · exact (hm rfl).elim
private theorem a3y (w:mA→ℕ) (r P:ko) (d:ℕ)
  (hr :r.support⊆P.support)
  (h₀:w (some 1)≤w (some 0)+d) (h₁:w (some 2)≤w (some 1)+d) :
  (afx r P).weightedTotalDegree w≤P.weightedTotalDegree w+d:= by
 rw [← mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
 have hr' : r∈zR w (P.weightedTotalDegree w+d) := by
  apply mem_restrictWeightedDegree.mpr
  intro m hm
  exact (Ee w (hr hm)).trans (yl _ _)
 have h₀' := mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr (c0T w _ _ P d h₀)
 have h₁' := mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr (c0T w _ _ P d h₁)
 unfold afx
 rw [MvPolynomial.C_mul']
 exact (zR w _).add_mem ((zR w _).add_mem hr' h₀')
  ((zR w _).smul_mem (2 :iP) h₁')
private theorem bwf (P:ko) :
  P.weightedTotalDegree (vw none 1)=gY P:= by
 rw [gY,degreeOf_eq_sup,Au]
 simp only [Finsupp.weight_single_one_apply]
private theorem a6u {P:ko} {i j k :mA} (h:P.degreeOf k=0) :
  pC k (c9 j*pC i P)=pC k (c9 j:ko)*pC i P:= by
 have hzero :pC k (pC i P)=0 :=
  Mj (Kl ((degreeOf_pderiv_le i k P).trans_eq h))
 rw [Fa ,hzero,zf ,xI]
end
end anj
end
section
namespace anj
noncomputable section
open K1 aR jA aFP
open scoped Polynomial BigOperators
private theorem ct0 (F:ko) (z :iP) (y :Fin 3→iP) :
   (n5 (ED z y) F).coeff 0=cy (ED z y) F:= by
 let e :ko →+* iP:=cy (fun _=>0)
 have he :e.comp (n5 (ED z y))=cy (ED z y) := by
   apply Ar
   · intro x
     simp [e,n5]
   · intro i
     simp [e,n5]
 rw [← MvPolynomial.constantCoeff_eq,← MvPolynomial.eval_zero']
 exact vl he F
private theorem bxX {ι:Type*} (s :oz ι) (q:ι→p5)
  (hn : ∀ i∈s,q i≠0) :
  (∏ i∈s,q i).totalDegree = ∑ i∈s,(q i).totalDegree := by
 simp only [← zS]
 exact J4 _ s q hn
private theorem index_prod {ι:Type*} (s :oz ι) (q:ι→p5)
  (hn : ∀ i∈s,q i≠0) :
  H9 (∏ i∈s,q i) = ∑ i∈s,H9 (q i) := by
 simp only [aOE]
 exact J4 _ s q hn
private theorem bpE {ι:Type*} {s :oz ι} {q:ι→p5}
   {y :Fin 3→iP} (hq:cy y (∏ i∈s,q i)≠0)
   {i:ι} (hi:i∈s) :cy y (q i)≠0 :=
 (Finset.prod_ne_zero_iff.mp (by simpa only [yU] using hq)) i hi
end
end anj
end
section
namespace anj
open jA Polynomial
open scoped Polynomial BigOperators
private theorem cfq {R:Type*} [zc R]
    (F G:R[X]) (z :R) {m n:ℕ} (hF:F.natDegree≤ m) (hG:G.natDegree≤n) :
    resultant (F.taylor z) (G.taylor z) m n=resultant F G m n:= by
  obtain ⟨a,rfl⟩:=JQ hF
  obtain ⟨b,rfl⟩:=JQ hG
  have expand (P Q:R[X]) :
      resultant P Q (P.natDegree+a) (Q.natDegree+b) =
        (-1)^((Q.natDegree+b)*a)*Q.coeff (Q.natDegree+b)^a *
          (P.leadingCoeff^b*resultant P Q) := by
    rw [resultant_add_left_deg _ _ _ _ _ th,
      resultant_add_right_deg _ _ _ _ _ th,coeff_natDegree]
  have coeff_preserved :
      (G.taylor z).coeff (G.natDegree+b)=G.coeff (G.natDegree+b) := by
    by_cases hb:b=0
    · simp [hb]
    · have hlt:G.natDegree<G.natDegree+b:= by omega
      rw [IU  hlt,
        IU  (by simpa only [natDegree_taylor] using hlt)]
  have h:=expand (F.taylor z) (G.taylor z)
  rw [resultant_taylor] at h
  simp only [natDegree_taylor,leadingCoeff_taylor,coeff_preserved] at h
  exact h.trans (expand F G).symm
private def weight (d i:ℕ) :ℕ:=d - 7800*i
end anj
end
section
namespace anj
noncomputable section
open aR jA Polynomial
open scoped BigOperators
set_option maxRecDepth 4000
private def BZ (v :Fin 3→iP) :p5 →+* iP[X] :=
 u8 C (fun i=>C (v i)*nX)
private theorem fUa (v :Fin 3→iP) (a :Fin 3 →₀ ℕ) (c:iP) :
   BZ v (qU a c) =
     monomial a.degree (cy v (qU a c)) := by
 rw [← C_mul_X_pow_eq_monomial]
 simp only [BZ,II,MvPolynomial.eval_monomial,mul_pow,
   Finsupp.prod]
 rw [KH,JW,Mk,← vG]
 simp only [mD,yU,pG]
private theorem bgD (v :Fin 3→iP) (Q:p5) (j:ℕ) :
   (BZ v Q).coeff j=cy v (Du j Q) := by
 classical
 induction Q using MvPolynomial.induction_on' with
 | monomial a c =>
   rw [fUa,coeff_monomial,
     MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl)]
   by_cases h:a.degree=j
   · simp [h]
   · simp [h,Ne.symm h]
 | add Q R hQ hR =>
   rw [qG,coeff_add,hQ,hR,qG,qG]
private theorem b7S (F:ko) (z :iP) (y v :Fin 3→iP) :
    ((qN F).map ((BZ v).comp (n5 y))).comp (nX+C (C z)) =
      (qN (n5 (ED z y) F)).map (BZ v) := by
  let e :=(Gj iP (Fin 3)).toRingHom
  let left:=(compRingHom (nX+C (C z))).comp ((mapRingHom ((BZ v).comp (n5 y))).comp e)
  let right:=(mapRingHom (BZ v)).comp (e.comp (n5 (ED z y)))
  have he :left=right:= by
    apply Ar
    · intro r
      simp [left,right,e,n5 ,BZ]
    · intro i
      cases i <;>
        simp [left,right,e,n5 ,BZ,ED]
  exact vl he F
private theorem caz (Q:p5) (y :Fin 3→iP) (d:ℕ)
  (h : ∀ v,nX ^d∣BZ v (n5 y Q)) :
  Qu Q y d:= by
 let _:Infinite iP:=Infinite.of_injective DI DI.injective
 intro a ha
 change d≤a.degree
 by_contra! ha'
 have hm:Du a.degree (n5 y Q)=0:= by
  apply MvPolynomial.funext
  intro v
  rw [p6,← bgD]
  exact (X_pow_dvd_iff (n:=d) (f :=BZ v (n5 y Q))).mp (h v) a.degree ha'
 have hc:=oD (fun P:p5=>P.coeff a) hm
 simp [IT] at hc
 exact (MvPolynomial.mem_support_iff.mp ha) hc
end
end anj
end
section
namespace anj
noncomputable section
open Polynomial K1 aR jA Rk gR ProximityPrize.Benchmark
open scoped BigOperators
set_option maxRecDepth 12000
private def line (Q:af 3) (T U:ao[X]) :yJ ao[X] :=
 t9 lJ
  (fun i=>lJ (jet T i)+Polynomial.C (jet U i)*nX) Q
private theorem bdm (Q:af 3) (T U:ao[X]) (c:ao) :
   (line Q T U).eval (lJ c)=cK Q (T+c•U) := by
 change (qz (lJ c))
   (t9 lJ
     (fun i=>lJ (jet T i)+Polynomial.C (jet U i)*nX) Q)= _
 rw [JK]
 have hC: (qz (C c)).comp C=G3 ao[X] :=Dv fun p=> by simp
 rw [hC]
 change cy _ Q=cy (jet (T+c•U)) Q
 have heq : (fun i:Fin 3=>(qz (C c))
     (lJ (jet T i)+Polynomial.C (jet U i)*nX)) =
     jet (T+c•U) := by
   funext i
   simp only [coe_evalRingHom,eval_mul,eval_C,eval_X,jet,qG]
   rw [(vZ i.val).map_smul,Algebra.smul_def,algebraMap_eq,p9]
 rw [heq]
private theorem bhI (F:yJ ao[X]) (i j:ℕ) :
   ((zk F).coeff i).coeff j=(F.coeff j).coeff i:= by
 induction F using Hw with
 | add P Q hp hq=>simp [hp,hq]
 | monomial n P =>
   induction P using Hw with
   | add P Q hp hq=>simp only [map_add,Polynomial.coeff_add,hp,hq]
   | monomial m c =>
     rw [Bivariate.swap_monomial_monomial]
     by_cases hi:m=i <;> by_cases hj:n=j <;> simp [Polynomial.coeff_monomial,hi,hj]
private theorem bnl (F:yJ ao[X]) (x :ao) (r :ℕ)
    (h : ∀ c:ao,(nX - C x)^r∣F.eval (C c)) (j:ℕ) :
    (nX - C x)^r∣F.coeff j:= by
  let f :ao[X] →+* ao[X] :=(taylorAlgHom x).toRingHom
  let A:=F.map f
  have heval (c:ao) :A.eval (C c)=taylor x (F.eval (C c)) := by
    change (F.map f).eval (C c)=f (F.eval (C c))
    have hC:f (C c)=C c:=taylor_C _ _
    rw [← hC,eval_map,eval₂_at_apply]
    rw [hC]
  have hzero (i:ℕ) (hi:i< r) : (zk A).coeff i=0:= by
    apply eq_zero_of_infinite_isRoot
    have hz (c:ao) : ((zk A).coeff i).eval c=0:= by
      have hs : (zk A).map (qz c)=A.eval (C c) := by
        simpa [Polynomial.aeval_def] using (Bivariate.aveal_eq_map_swap c A).symm
      change qz c ((zk A).coeff i)=0
      rw [← zm,hs,heval]
      exact X_pow_dvd_iff.mp ((Lf _ _ _).mpr (h c)) i hi
    simpa [IsRoot,hz] using (Set.infinite_univ : (Set.univ :Set ao).Infinite)
  apply (Lf _ _ _).mp
  apply X_pow_dvd_iff.mpr
  intro i hi
  change (f (F.coeff j)).coeff i=0
  rw [← zm,← bhI,hzero i hi,Polynomial.coeff_zero]
private theorem b2g (L:ao[X]) (x :ao) (hx :L.eval x≠0)
   (v :Fin 3→ao) :
   ∃ V:ao[X],V.natDegree≤2 ∧ ∀ i:Fin 3,(jet (L*V) i).eval x=v i:= by
 classical
 let B:=(nX - C x)^3
 have hB:B.Monic:=(monic_X_sub_C x).pow _
 have hdeg:B.natDegree=3:= by simp [B,natDegree_pow]
 have hcop:IsCoprime L B:= by
   apply (irreducible_X_sub_C x).coprime_pow_of_not_dvd
   simpa [dvd_iff_isRoot,IsRoot] using hx
 obtain ⟨a,b,hab⟩:=hcop
 let F:=taylor (-x) (ofFn 3 v)
 let V:=(a*F) %ₘ B
 have hdiv :B∣L*V-F:= by
   refine ⟨-(b*F+L*((a*F) /ₘ B)),?_⟩
   dsimp only [V]
   rw [modByMonic_eq_sub_mul_div]
   linear_combination F*hab
 have hjet:=(X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero (L*V-F) x 3).mp hdiv
 refine ⟨V,?_,fun i => ?_⟩
 · have hne :B≠1 := by
     intro h
     rw [h,natDegree_one] at hdeg
     omega
   have hsmall:=natDegree_modByMonic_lt (a*F) hB hne
   rw [hdeg] at hsmall
   exact wR hsmall
 · have h:=hjet i.val i.isLt
   rw [map_sub,eval_sub,EP] at h
   change (vZ i.val (L*V)).eval x=v i
   rw [h,← taylor_coeff,show F=taylor (-x) (ofFn 3 v) from rfl,taylor_taylor,
     add_neg_cancel,taylor_zero,ofFn_coeff_eq_val_of_lt v i.isLt]
private theorem bXP (P:u5 (Fin 3) ao) (v :Fin 3→ao) (j:ℕ) :
   (t9 lJ (fun i=>lJ (v i)*nX) P).coeff j =
     cy v (Du j P) := by
 classical
 rw [MvPolynomial.eval₂_eq,Polynomial.finsetSum_coeff,MvPolynomial.homogeneousComponent_apply]
 change _=u8 (G3 _) v _
 rw [zd ,Finset.sum_filter]
 apply pQ rfl
 intro m _
 rw [II]
 simp only [Finsupp.prod,mul_pow,KH,← pG lJ,
   ← yU lJ,← mD lJ,← vG,JW,
   Kz ,RingHom.id_apply,Mk]
 split_ifs <;> simp_all
private theorem b7M (P:af 3) (S U:ao[X]) (x :ao) :
    (line P S U).map (qz x) =
      t9 lJ (fun i:Fin 3=>lJ ((jet U i).eval x) *
        nX) (lV (qz x) (Z8 P S)) := by
  let f :=qz x
  let g (i:Fin 3) :ao[X] :=lJ (f (jet U i))*nX
  change (mapRingHom f) (t9 lJ
    (fun i:Fin 3=>lJ (jet S i)+Polynomial.C (jet U i)*nX) P) =
    u8 lJ g
      (lV f (t9 ov
        (fun i=>c9 i+MvPolynomial.C (jet S i)) P))
  rw [JK,MvPolynomial.eval₂Hom_map_hom]
  change _=u8 (Polynomial.C.comp f) g
    (u8 ov
      (fun i=>c9 i+MvPolynomial.C (jet S i)) P)
  rw [MvPolynomial.map_eval₂Hom]
  have hl: (mapRingHom f).comp lJ=Polynomial.C.comp f :=Dv fun p=> by simp
  have hr : (u8 (Polynomial.C.comp f) g).comp ov =
      Polynomial.C.comp f :=Dv fun p=> by simp
  rw [hl,hr]
  congr 1
  funext i
  simp [g,add_comm]
private theorem bfX (P:af 3) (S L:ao[X]) (hL:L≠0) (d:ℕ)
    (h : ∀ (V:ao[X]),V.natDegree≤2 → ∀ j<d,(line P S (L*V)).coeff j=0) :
    wU P S d:= by
  intro m hm
  change d≤ m.degree
  by_contra! hlt
  have hz (x :ao) (hx :L.eval x≠0) : ((Z8 P S).coeff m).eval x=0:= by
    let A:=lV (qz x) (Z8 P S)
    let Q:=Du m.degree A
    have hQ:Q=0:= by
      apply (MvPolynomial.homogeneousComponent_isHomogeneous _ _).eq_zero_of_forall_eval_eq_zero
      intro v
      obtain ⟨V,hV,hv⟩:=b2g L x hx v
      have heval :=oD (qz x) (h V hV m.degree hlt)
      rw [p6,← zm,b7M] at heval
      let along (u:Fin 3→ao) :=
        (t9 lJ (fun i=>lJ (u i)*nX) A).coeff
          m.degree
      have hdir :=oD along (funext hv)
      have hvanish:along v=0:=hdir.symm.trans heval
      simpa only [along,bXP] using hvanish
    have hcoeff :=oD (fun F:u5 (Fin 3) ao=>F.coeff m) hQ
    simpa [Q,IT,A,Aa]
      using hcoeff
  have hzero : (Z8 P S).coeff m=0:= by
    apply eq_zero_of_infinite_isRoot
    refine (finite_setOfPred_isRoot hL).infinite_compl.mono ?_
    intro x hx
    exact hz x hx
  exact MvPolynomial.mem_support_iff.mp hm hzero
private theorem ctZ (Q:af 3) (T:ao[X]) :
   n5 (jW T) (lV qV Q) =
     lV qV (Z8 Q T) := by
 let left:=(n5 (jW T)).comp (lV qV)
 let right:=(lV qV).comp (u8 ov
   (fun i:Fin 3=>c9 i+MvPolynomial.C (jet T i)))
 have h:left=right:= by
   apply Ar
   · intro r
     simp [left,right,n5]
   · intro i
     simp [left,right,n5 ,jW]
 exact vl h Q
end
end anj
end
section
namespace anj
noncomputable section
open K1 aR jA Rk
open scoped Polynomial BigOperators
private theorem bXJ {F:p5} {x :Fin 3→iP}
  {d:ℕ} (h:Qu F x d) (a :Fin 3 →₀ ℕ) (ha :a.degree<d) :
  (n5 x F).coeff a=0:= by
 by_contra hz
 exact (not_le_of_gt ha) (h a (MvPolynomial.mem_support_iff.mpr hz))
private theorem cU2 :sS qV :=
 GR ao[X] iP
private theorem aNv {Q:af 3} {R:p5} {d:ao[X]}
   (hQ:lV qV Q=ov (qV d)*R) (S:ao[X])
   (hR:cy (jW S) R=0) :cK Q S=0:= by
 have hcomm:qV (cK Q S) =
     cy (jW S) (lV qV Q) := by
   rw [cK,LP]
   exact G8 qV (jet S) Q
 apply cU2
 rw [p6,hcomm,hQ,mD,hR,zf]
private theorem b8H (Q:af 3) (S:ao[X]) :
   lV qV (Z8 Q S) =
     n5 (jW S) (lV qV Q) := by
 have hc: (lV (σ:=Fin 3) qV).comp ov =
     MvPolynomial.C.comp qV:= by
   apply Dv
   intro x
   simp
 unfold aR.Z8
 rw [MvPolynomial.eval₂_comp_left]
 change _=t9 ov
   (fun i=>c9 i+MvPolynomial.C (jW S i)) (lV qV Q)
 rw [MvPolynomial.eval₂_map,hc]
 congr 1
 funext i
 simp [jW]
private theorem cav {Q:af 3} {R:p5} {d:ao[X]}
   (hQ:lV qV Q=ov (qV d)*R)
   (S:ao[X]) {m:ℕ} (hR:Qu R (jW S) m) :wU Q S m:= by
 have hs :lV qV (Z8 Q S) =
     ov (qV d)*n5 (jW S) R:= by
   rw [b8H,hQ,mD,n5 ,MvPolynomial.eval₂Hom_C]
 intro a ha
 apply hR
 have hcoeff :=oD (fun P:p5=>P.coeff a) hs
 simp only [Aa ,Dw] at hcoeff
 rw [GB] at ha ⊢
 intro hz
 rw [hz,zf] at hcoeff
 exact ha (cU2 (hcoeff.trans (p6 _).symm))
end
end anj
end
