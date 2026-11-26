import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdA2
import ProximityPrize.SubmissionLower.DdAA
import ProximityPrize.SubmissionLower.DdAE
import ProximityPrize.SubmissionLower.DdB4
import ProximityPrize.SubmissionLower.DdBG
import ProximityPrize.SubmissionLower.DdZ3EWiUc
import ProximityPrize.SubmissionLower.Fast055
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_CodingTheory_ReedSolomon_MutualCorrelatedAgreement_Johnson_Agreement
import ProximityPrize.SubmissionLower.LibraryArkLib_Data_Finset_PairwiseIntersection
import ProximityPrize.SubmissionLower.LibraryArkLib_ToMathlib_LinearAlgebra_FiniteDimensional
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_MvPolynomial_Coeff
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Polynomial_Basis
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_Polynomial_Degree_IsMonicOfDegree
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_TrivSqZeroExt_Ideal
import ProximityPrize.SubmissionLower.LibraryMathlib_Analysis_BoxIntegral_UnitPartition
import ProximityPrize.SubmissionLower.LibraryMathlib_Analysis_Convex_Measure
import ProximityPrize.SubmissionLower.LibraryMathlib_Analysis_Convex_Visible
import ProximityPrize.SubmissionLower.LibraryMathlib_Combinatorics_Pigeonhole
import ProximityPrize.SubmissionLower.LibraryMathlib_Data_Finsupp_Interval
import ProximityPrize.SubmissionLower.LibraryMathlib_Data_Set_Card_Arithmetic
import ProximityPrize.SubmissionLower.LibraryMathlib_Data_Sym_NatCard
import ProximityPrize.SubmissionLower.LibraryMathlib_GroupTheory_CosetCover
import ProximityPrize.SubmissionLower.LibraryMathlib_LinearAlgebra_FreeModule_Norm
import ProximityPrize.SubmissionLower.LibraryMathlib_LinearAlgebra_TensorProduct_Free
import ProximityPrize.SubmissionLower.LibraryMathlib_NumberTheory_FunctionField
import ProximityPrize.SubmissionLower.LibraryMathlib_NumberTheory_RatFunc_Ostrowski
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_DedekindDomain_Factorization
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Finiteness_Descent
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Flat_Equalizer
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_GradedAlgebra_Radical
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Ideal_IsPrincipalPowQuotient
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Localization_NormTrace
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_OrderOfVanishing_Basic
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_PowerSeries_Inverse
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RamificationInertia_Basic
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Regular_Flat
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RingHom_Surjective
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_RingHom_Unramified
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Spectrum_Prime_Homeomorph
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Valuation_Discrete_RankOne
import ProximityPrize.SubmissionLower.LibraryMathlib_RingTheory_Valuation_LocalSubring
import ProximityPrize.SubmissionLower.LibraryMathlib_Topology_Algebra_MvPolynomial
import ProximityPrize.SubmissionLower.R6966ProofProtocolProfile

section Merged6967_DdCS
set_option Elab.async false



























































set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming Algebra.algebraMap→xL,CommRing→zc,DFunLike.congr_fun→vl,Fin.last→aU,Fin.sum_univ_eq_sum_range→KA,Fin.sum_univ_three→EK,Fin.sum_univ_two→zi,Fin.val→ oj,Finset→ oz,Finset.card_le_card→xW,Finset.filter_subset→FK,Finset.mem_univ→u9,Finset.mul_sum→sH,Finset.prod_mul_distrib→KH,Finset.prod_pow_eq_pow_sum→JW,Finset.range→t3,Finset.sum_add_distrib→vi,Finset.sum_congr→pQ,Finset.sum_const→Ef,Finset.sum_eq_single_of_mem→LR,Finset.sum_eq_zero→y5,Finset.sum_le_sum→yQ,Finset.sum_mul→vk,Finset.sup_le_iff→JM,Finsupp.degree_apply→Mk,Finsupp.degree_eq_sum→ In,Finsupp.single→uh,Finsupp.weight→qM,Finsupp.weight_single→FQ,Fintype.card→Bf,Function.Injective→sS,Ideal→uz,Ideal.Quotient.mk→pU,Ideal.Quotient.mkₐ→GF,Ideal.kerLiftAlg_injective→Mw,Ideal.span→G2,Ideal.span_singleton_prime→Mz,IsFractionRing.injective→GR,IsLocalization.Away.algebraMap_isUnit→G7,IsScalarTower.toAlgHom→HZ,KoalaBear.Field→C9,LinearMap.finrank_le_finrank_of_injective→FU,LinearMap.ker→Eg,LinearMap.mulLeft→G4,Matrix.blockDiagonal'→z7,Matrix.blockDiagonal'_apply_eq→KI,Matrix.blockDiagonal'_apply_ne→ Iw,Matrix.rank_eq_finrank_span_cols→G5
open _root_ renaming Matrix.rank_submatrix_le→G9,Module.finrank→qJ,MulZeroClass.mul_zero→zf,MulZeroClass.zero_mul→uW,Multiset.toFinset_prod_dvd_prod→Kv,MvPolynomial→u5,MvPolynomial.C→ ov,MvPolynomial.X→c9,MvPolynomial.aeval→qm,MvPolynomial.aeval_eq_eval→Gr,MvPolynomial.affineDegree→ ox,MvPolynomial.affineHilbertPolynomial→pL,MvPolynomial.algHom_ext→LQ,MvPolynomial.coeff_C_mul→Dw,MvPolynomial.coeff_homogeneousComponent→ IT,MvPolynomial.coeff_map→Aa,MvPolynomial.coeff_monomial→Dz,MvPolynomial.eval→cy,MvPolynomial.eval_map→LP,MvPolynomial.eval₂→t9,MvPolynomial.eval₂Hom→u8,MvPolynomial.eval₂Hom_monomial→ II,MvPolynomial.eval₂_comp→G8,MvPolynomial.hom_eval₂→JK,MvPolynomial.homogeneousComponent→Du,MvPolynomial.le_weightedTotalDegree→Ee,MvPolynomial.map→lV,MvPolynomial.mem_support_iff→GB,MvPolynomial.monomial→qU,MvPolynomial.optionEquivLeft→Gj,MvPolynomial.optionEquivRight→G1,MvPolynomial.pderiv→pC,MvPolynomial.pderiv_eq_zero_of_degreeOf_eq_zero→Mj,MvPolynomial.pderiv_mul→Fa,MvPolynomial.restrictWeightedDegree→zR,MvPolynomial.ringHom_ext→Ar,MvPolynomial.weightedTotalDegree→Au,MvPolynomial.weightedTotalDegree_le_of_dvd→Fz,MvPolynomial.weightedTotalDegree_one→zS,MvPolynomial.weightedTotalDegree_piSingle→t4,MvPolynomial.weightedTotalDegree_prod→J4,MvPolynomial.zeroLocus→qy,Nat.add_assoc→FR,Nat.add_comm→ze,Nat.add_le_add→v8,Nat.add_le_add_left→x7,Nat.add_le_add_right→C4,Nat.add_mul→z9
open _root_ renaming Nat.add_sub_cancel→G6,Nat.cast_nonneg→zh,Nat.cast_sub→wY,Nat.eq_zero_of_le_zero→Kl,Nat.exists_eq_add_of_le→JQ,Nat.le_add_right→yl,Nat.le_of_lt_succ→wR,Nat.mul_comm→zE,Nat.mul_le_mul_left→ oY,Nat.sub_add_cancel→G0,Nat.sub_le_sub_right→v9,Nat.sub_pos_of_lt→Ml,Option→t6,Pi.single→vw,Polynomial→yJ,Polynomial.Bivariate.swap→zk,Polynomial.C→lJ,Polynomial.X→nX,Polynomial.X_pow_dvd_taylor_iff_X_sub_C_pow_dvd→Lf,Polynomial.coeff_C_mul_X_pow→Kz,Polynomial.coeff_eq_zero_of_natDegree_lt→ IU,Polynomial.coeff_map→zm,Polynomial.derivative→pz,Polynomial.evalRingHom→qz,Polynomial.hasseDeriv→vZ,Polynomial.induction_on'→Hw,Polynomial.natDegree_lt_iff_degree_lt→Ea,PolynomialDifferential.DifferentialPolynomial→qx,PolynomialDifferential.TaylorExponentSufficient→Et,PolynomialDifferential.degreeOf_initialJetSeparant_le→Gn,PolynomialDifferential.differentialSpecialization→ oZ,PolynomialDifferential.rationalTaylorNumerator→F9,PolynomialDifferential.rationalTaylorPolynomial→yo,PolynomialDifferential.universalTaylorResidual→FV,ProximityPrize.Benchmark.IRSProfile.card_index→Kp,ReedSolomon.HiddenDerivative.LocalPolynomial→xu,ReedSolomon.HiddenDerivative.SourceColumn.polynomial_eq_sourceMonomial→Gk,ReedSolomon.HiddenDerivative.localConstraintMatrix→vh,ReedSolomon.HiddenDerivative.localT→nI,ReedSolomon.HiddenDerivative.localY→ oK,ReedSolomon.HiddenDerivative.sourceMonomial→wB,ReedSolomon.HiddenDerivative.unscaledLocalSubstitution→GY,RingHom.ext→Dv,RingHom.id→G3,Set.range→Df,Sigma→t5,StrongNormalizationMonoid→LO,Submodule→zg
open _root_ renaming Submodule.finrank_mono→ Il,Submodule.span→z8,Submodule.sum_mem→Gi,Subtype.ext→xm,Subtype.val→uJ,UniqueFactorizationMonoid.normalizedFactors→yB,UniqueFactorizationMonoid.strongNormalizationMonoid→Kh,add_le_add→Av,add_zero→xI,congrArg→ oD,congrFun→wA,i4.Chart→nq,i4.Family→vj,i4.Source→lz,i4.center→lI,i4.column→ oy,i4.embed→ oq,i4.errors→p7,i4.indexWeight→Cy,ite_eq_left→Kc,ite_eq_right→yL,le_rfl→th,map_add→qG,map_mul→mD,map_pow→pG,map_prod→yU,map_sum→zd,map_zero→p6,mul_assoc→vG,mul_comm→p9,mul_le_mul_of_nonneg_left→t8,mul_nonneg→vH,one_mul→sI,smul_eq_mul→C5,sub_eq_zero→EP,zero_add→t7
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
theorem bYf (A:ℕ) (s :lz) :sS (oy A s) := by
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
open MN (aDW)
open aZw (azg)
theorem Wq {A:ℕ} {w:Node→K} {T:oz (Polynomial K)}
    (h: (T:Set (Polynomial K))⊆close A w) (hA:aRk A) (cap:ℕ)
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
  let lg (γ:(Polynomial K)) :oz Node :=univ.filter fun i=>γ.eval (node i)=w i
  let common :oz Node :=univ.filter fun i => ∀ γ∈T,γ.eval (node i)=w i
  let nodes :oz Node :=univ \ common
  have common_le (γ:(Polynomial K)) (hγ:γ∈T) :common⊆lg γ:= by
    intro i hi
    exact mem_filter.mpr ⟨u9 _,(mem_filter.mp hi).2 γ hγ⟩
  have hit_count (γ:(Polynomial K)) (hγ:γ∈T) :A≤(lg γ).card:= by
    exact (h hγ).2
  have degree (a :(Polynomial K)) (ha :a∈T) :a.natDegree≤N := by
    by_cases hz :a=0
    · simp [hz]
    · have hdeg:=(Ea hz).2 (h ha).1
      exact wR hdeg
  have pair_count (a :(Polynomial K)) (ha :a∈T) (b:(Polynomial K)) (hb:b∈T) (hab:a≠b) :
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
  have exists_trim (γ:(Polynomial K)) : ∃ B:oz Node,γ∈T→B⊆lg γ \ common∧B.card=x := by
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
  have into_nodes (γ:(Polynomial K)) (hγ:γ∈T) :B γ⊆nodes := by
    intro i hi
    exact mem_sdiff.mpr ⟨u9 _,(mem_sdiff.mp ((hB γ hγ).1 hi)).2⟩
  have overlap (a :(Polynomial K)) (ha :a∈T) (b:(Polynomial K)) (hb:b∈T) (hab:a≠b) :
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
open MN (aM6)
private def VA (x a :K) :jo :=
 (∑ i:Fin k,C (oq x^i.val)*c9 i) - C (oq a)
private theorem aQ5 (x a :K) : (VA x a).totalDegree≤1 := by
 apply (totalDegree_sub_C_le _ _).trans
 apply totalDegree_finsetSum_le
 intro i _
 simpa only [totalDegree_C,totalDegree_X,t7] using
  (totalDegree_mul (C (oq x^i.val)) (c9 i))
private theorem b9D {f :(Polynomial K)} (h:f.degree<k) :f.natDegree<k := by
 by_cases hz :f=0
 · rw [hz,Polynomial.natDegree_zero]
   exact Nat.zero_lt_succ _
 · exact (Ea hz).2 h
private theorem aFp {f :(Polynomial K)} (h:f.degree<k) (x a :K) :
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
private theorem bXE {A w} {Γ:oz (Polynomial K)} (h: (Γ:Set (Polynomial K))⊆close A w) :
   Set.InjOn Gp (Γ:Set (Polynomial K)) := by
 intro f hf g hg heq
 apply Polynomial.ext
 intro j
 by_cases hj:j<k
 · exact embed.injective (wA heq ⟨j,hj⟩)
 · have hfj:=(b9D (h hf).1).trans_le (Nat.le_of_not_gt hj)
   have hgj:=(b9D (h hg).1).trans_le (Nat.le_of_not_gt hj)
   rw [IU hfj,IU hgj]
private theorem cw2 {A w} {Γ:oz (Polynomial K)} (h: (Γ:Set (Polynomial K))⊆close A w) (P:uz jo)
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
private theorem bv5 {A w} {Γ:oz (Polynomial K)} (h: (Γ:Set (Polynomial K))⊆close A w) {P:uz jo}
    (hP:P.IsPrime) (hpoints : ∀ γ∈Γ,Gp γ∈qy nU P)
    (x a :K) (hmiss : ∃ γ∈Γ,γ.eval x≠a)
    {c:ℚ} (hc:0≤ c)
    (bound : ∀ (V:oz (Polynomial K)),V⊆Γ → ∀ (Q:uz jo),Q.IsPrime →
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
theorem aTZ {A w} {T:oz (Polynomial K)} (hT: (T:Set (Polynomial K))⊆close A w)
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
private theorem a8X {A w} {T:oz (Polynomial K)} (hT: (T:Set (Polynomial K))⊆close A w)
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
theorem cOg {A w r budget} {T:oz (Polynomial K)} (hT: (T:Set (Polynomial K))⊆close A w)
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
    have hsub: (part i:Set (Polynomial K))⊆close A w:= fun _ hf=>hT (mem_filter.mp hf).1
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
    ∃ Q₁,bRZ s Q₁ ∧ ∀ f :(Polynomial K),f.degree<k →
      oZ Q f=0 → ¬ ae8 Q f →
      oZ Q₁ f=0
def c6:Prop :=
  ∀ s,Rz s → ∀ Q₁,bRZ s Q₁ →
    ∃ F:vj 1,cxu s F∧cxn F Q₁
def c7:Prop :=
 ∀ s,Rz s → ∀ F:vj 1,cxu s F→bQ7 F (R₁ s)
def c8:Prop :=
  ∀ s,Rz s → ∀ Q₁,bRZ s Q₁ →
    ∃ G:yJ (Polynomial K),G≠0∧G.natDegree≤H s*(H s-1) ∧
      ∀ f :(Polynomial K),f.degree<k→ oZ Q₁ f=0 →
        ¬ ae8 Q₁ f→G.eval f=0
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
def RG:(Polynomial K) →+* nU :=
 (xL FX nU).comp (xL (Polynomial K) FX)
def dR (G:Equation) :qx nU 2 :=
 lV oq G
def initial (G:Equation) :BL 2 :=
 initialJetEquation lI (dR G)
def T4 (G:Equation) :BL 2 :=
 initialJetSeparant lI (dR G)
def ahT (f :(Polynomial K)) :Fin 3→nU :=
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
 Eh : ∀ f :(Polynomial K),ae8 Q f →
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
 (xL FX nU).injective.comp (GR (Polynomial K) FX)
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
private theorem auQ (P:(Polynomial K)) : (P.map oq).eval lI=RG P:= by
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
theorem bHS (G:Equation) (f :(Polynomial K)) :
   cy (ahT f) (initial G) =
     RG (oZ G f) := by
 rw [initial,← Gr,aeval_initialJetEquation,ahT,
   ← eval_differentialSpecialization,dR,← map_differentialSpecialization,auQ]
theorem eom (G:Equation) (f :(Polynomial K)) :
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
private theorem fUf {L:ℕ} (P:(Polynomial nU)) (hp:P.degree<L) (j:ℕ) :
   (∑ i:Fin L,(i.val.choose j:nU)*lI ^(i.val-j)*P.coeff i.val) =
     (vZ j P).eval center := by
 rw [hasseDeriv_apply,← Polynomial.sum_fin
   (fun i c=>monomial (i - j) ((i.choose j:nU)*c)) (by simp) hp,eval_finsetSum]
 apply pQ rfl
 intro i _
 rw [eval_monomial]
 ring
set_option maxRecDepth 200000 in
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
theorem dIj (G:Equation) (P:BL 2) (f :(Polynomial K))
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
def cVd:Equation →+* BL 2 :=
 (qm (fun j:t6 (Fin 3) =>
   j.elim (ov lI) c9)).toRingHom.comp (lV oq)
theorem cfE {G G' : Equation} {f :(Polynomial K)}
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
  | ind l ih =>
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
open aR MvPolynomial
open scoped Polynomial BigOperators
end
end anj
end
section
namespace anj
noncomputable section
open DdK1 aR
open scoped Polynomial BigOperators
end
end anj
end
section
namespace anj
open Polynomial
open scoped Polynomial BigOperators
end anj
end
section
namespace anj
noncomputable section
open aR Polynomial
open scoped BigOperators
set_option maxRecDepth 4000
end
end anj
end
section
namespace anj
noncomputable section
open Polynomial DdK1 aR gR ProximityPrize.Benchmark
open scoped BigOperators
set_option maxRecDepth 12000
def line (Q:af 3) (T U:(Polynomial ao)) :yJ (Polynomial ao) :=
 t9 lJ
  (fun i=>lJ (jet T i)+Polynomial.C (jet U i)*nX) Q
theorem bdm (Q:af 3) (T U:(Polynomial ao)) (c:ao) :
   (line Q T U).eval (lJ c)=cK Q (T+c•U) := by
 change (qz (lJ c))
   (t9 lJ
     (fun i=>lJ (jet T i)+Polynomial.C (jet U i)*nX) Q)= _
 rw [JK]
 have hC: (qz (C c)).comp C=G3 (Polynomial ao) :=Dv fun p=> by simp
 rw [hC]
 change cy _ Q=cy (jet (T+c•U)) Q
 have heq : (fun i:Fin 3=>(qz (C c))
     (lJ (jet T i)+Polynomial.C (jet U i)*nX)) =
     jet (T+c•U) := by
   funext i
   simp only [coe_evalRingHom,eval_mul,eval_C,eval_X,jet,qG]
   rw [(vZ i.val).map_smul,Algebra.smul_def,algebraMap_eq,p9]
 rw [heq]
private theorem b2g (L:(Polynomial ao)) (x :ao) (hx :L.eval x≠0)
   (v :Fin 3→ao) :
   ∃ V:(Polynomial ao),V.natDegree≤2 ∧ ∀ i:Fin 3,(jet (L*V) i).eval x=v i:= by
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
 simp only [Finsupp.prod,mul_pow,KH,← pG (lJ (R:=ao)),
   ← yU (lJ (R:=ao)),← mD (lJ (R:=ao)),← vG,JW,
   Kz ,RingHom.id_apply,Mk]
 split_ifs <;> simp_all
private theorem b7M (P:af 3) (S U:(Polynomial ao)) (x :ao) :
    (line P S U).map (qz x) =
      t9 lJ (fun i:Fin 3=>lJ ((jet U i).eval x) *
        nX) (lV (qz x) (Z8 P S)) := by
  let f :=qz x
  let g (i:Fin 3) :(Polynomial ao) :=lJ (f (jet U i))*nX
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
theorem bfX (P:af 3) (S L:(Polynomial ao)) (hL:L≠0) (d:ℕ)
    (h : ∀ (V:(Polynomial ao)),V.natDegree≤2 → ∀ j<d,(line P S (L*V)).coeff j=0) :
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
end
end anj
end
section
namespace anj
noncomputable section
open DdK1 aR
open scoped Polynomial BigOperators
end
end anj
end

end Merged6967_DdCS

section Merged6967_Fast051
set_option Elab.async false





























set_option Elab.async false
set_option autoImplicit true
section
namespace K1_13_8
open K1_13
open scoped BigOperators
def zeroShape : Shape := ⟨0,0,0⟩
def layerCount : ℕ := 1 + (3000 * 180265 - 1) / 46597
def Valid (a : Shape) : Prop := 1 ≤ a.t ∧ 3 * a.t ≤ a.j ∧ a.j ≤ 3 * a.b
def RetainedBox (a : Shape) : Prop :=
  a.b ≤ 19 ∧ a.j ≤ 6 ∧
  (4 ≤ a.j → a.b ≤ 17) ∧ (5 ≤ a.j → a.b ≤ 13) ∧ (6 ≤ a.j → a.b ≤ 6)
instance (a : Shape) : Decidable (Valid a) := by unfold Valid; infer_instance
instance (a : Shape) : Decidable (RetainedBox a) := by unfold RetainedBox; infer_instance
instance (a : Shape) : Decidable (FatEligible a) := by unfold FatEligible; infer_instance
def coefficients (r s : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  match r, s with
  | 0,0 => (1,22,57,36,0)
  | 0,1 => (2,29,63,36,0)
  | 0,2 => (4,37,69,36,0)
  | 0,3 => (7,46,75,36,0)
  | 0,4 => (11,56,81,36,0)
  | 0, _ => (16,67,87,36,0)
  | 1,0 => (1,63,314,468,216)
  | 1,1 => (3,92,377,504,216)
  | 1,2 => (7,129,446,540,216)
  | 1,3 => (14,175,521,576,216)
  | 1,4 => (25,231,602,612,216)
  | 1, _ => (41,298,689,648,216)
  | 2,0 => (1,38,172,243,108)
  | 2,1 => (2,54,205,261,108)
  | 2,2 => (5,75,241,279,108)
  | 2,3 => (9,100,280,297,108)
  | 2,4 => (16,131,322,315,108)
  | 2, _ => (25,167,367,333,108)
  | _, 0 => (1,30,125,168,72)
  | _, 1 => (2,42,148,180,72)
  | _, 2 => (4,57,173,192,72)
  | _, 3 => (8,76,200,204,72)
  | _, 4 => (13,98,229,216,72)
  | _, _ => (20,124,260,228,72)
def coefficient (r j : ℕ) : ℕ :=
  let q := j / 6
  let (a, b, c, d, e) := coefficients r (j % 6)
  let p₂ := q * (q - 1)
  let p₃ := p₂ * (q - 2)
  a + b * q + c * (p₂ / 2) + d * (p₃ / 6) + e * (p₃ * (q - 3) / 24)
def shifted (r j v : ℕ) : ℕ := if v ≤ j then coefficient r (j - v) else 0
def across (b r j v : ℕ) : ℕ :=
  shifted r j v - shifted r j (v + r * (b + 1))
def fastSymbols (b j : ℕ) : ℕ :=
  (b + 1) * coefficient 0 j + across b 2 j 3 + across b 2 j 4 + across b 2 j 5 -
    (across b 1 j 1 + across b 1 j 2 + across b 1 j 3 + across b 3 j 6)
def fastRemaining (b j : ℕ) : ℕ :=
  if b ≤ 4012 ∧ j ≤ 1650 then fastSymbols (4012 - b) (1650 - j) else 0
def zeroMass (b j : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (1650 / j), fastRemaining ((k + 1) * b) ((k + 1) * j)
def availableMass (r y : Shape) (L : ℕ) : ℕ :=
  (if r.j = 0 then L * fastRemaining 0 0
    else ∑ k ∈ Finset.range (min L (1650 / r.j)),
      fastRemaining ((k + 1) * r.b) ((k + 1) * r.j)) +
  ∑ k ∈ Finset.range (1650 / (r.j + y.j)),
    fastRemaining (L * r.b + (k + 1) * (r.b + y.b))
      (L * r.j + (k + 1) * (r.j + y.j))
end K1_13_8
end
section
namespace K1_13_8
open K1_13
open scoped BigOperators
theorem sum_range_mono {k m : ℕ} {f g : ℕ → ℕ} (hkm : k ≤ m)
    (hfg : ∀ i < k, f i ≤ g i) :
    (∑ i ∈ Finset.range k, f i) ≤ ∑ i ∈ Finset.range m, g i :=
  (Finset.sum_le_sum fun i hi => hfg i (Finset.mem_range.mp hi)).trans
    (Finset.sum_le_sum_of_subset (Finset.range_mono hkm))
theorem symbols_mono {b₁ b₂ j₁ j₂ : ℕ} (hb : b₁ ≤ b₂) (hj : j₁ ≤ j₂) :
    symbols b₁ j₁ ≤ symbols b₂ j₂ := by
  unfold symbols
  apply sum_range_mono (by omega)
  intro z _
  apply sum_range_mono (by omega)
  intro y _
  apply sum_range_mono (by omega)
  intro x _
  omega
theorem remaining_anti {b₁ b₂ j₁ j₂ : ℕ} (hb : b₁ ≤ b₂) (hj : j₁ ≤ j₂) :
    remaining b₂ j₂ ≤ remaining b₁ j₁ := by
  by_cases h : b₂ ≤ 4012 ∧ j₂ ≤ 1650
  · have h' : b₁ ≤ 4012 ∧ j₁ ≤ 1650 := ⟨hb.trans h.1, hj.trans h.2⟩
    simpa [remaining, h, h'] using
      (symbols_mono (b₁ := 4012 - b₂) (b₂ := 4012 - b₁)
        (j₁ := 1650 - j₂) (j₂ := 1650 - j₁) (by omega) (by omega))
  · simp [remaining, h]
theorem fastRemaining_zero {b j : ℕ} (h : 1650 < j) : fastRemaining b j = 0 := by
  simp [fastRemaining, show ¬ j ≤ 1650 by omega]
theorem sum_range_truncate {f : ℕ → ℕ} {k m : ℕ}
    (hz : ∀ i, m ≤ i → f i = 0) (h : m ≤ k) :
    (∑ i ∈ Finset.range k, f i) = ∑ i ∈ Finset.range m, f i := by
  symm
  apply Finset.sum_subset (Finset.range_mono h)
  intro i _ hi
  exact hz i (by simpa using hi)
theorem sum_range_min {f : ℕ → ℕ} (k m : ℕ)
    (hz : ∀ i, m ≤ i → f i = 0) :
    (∑ i ∈ Finset.range k, f i) = ∑ i ∈ Finset.range (min k m), f i := by
  by_cases h : m ≤ k
  · rw [min_eq_right h]
    exact sum_range_truncate hz h
  · rw [min_eq_left (by omega : k ≤ m)]
theorem index_over {j k : ℕ} (hj : 0 < j) (hk : 1650 / j ≤ k) :
    1650 < (k + 1) * j :=
  (Nat.div_lt_iff_lt_mul hj).mp (by omega)
section
set_option maxRecDepth 8192
set_option maxHeartbeats 0
end
def layerTerm (r y : Shape) (L k : ℕ) : ℕ :=
  remaining ((k + 1) * r.b + (k + 1 - L) * y.b)
    ((k + 1) * r.j + (k + 1 - L) * y.j)
theorem availableMass_eq_sum (hcount : ∀ b j, remaining b j = fastRemaining b j)
    {r y : Shape} {L N : ℕ} (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j + y.j) (hN : L + 1650 / (r.j + y.j) ≤ N) :
    (∑ k ∈ Finset.range N, layerTerm r y L k) = availableMass r y L := by
  have hL : L ≤ N := (Nat.le_add_right _ _).trans hN
  conv_lhs => rw [← Nat.add_sub_of_le hL, Finset.sum_range_add]
  unfold availableMass
  congr 1
  · have hfirst : (∑ k ∈ Finset.range L, layerTerm r y L k) =
        ∑ k ∈ Finset.range L, fastRemaining ((k + 1) * r.b) ((k + 1) * r.j) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hz : k + 1 - L = 0 := by
        have := Finset.mem_range.mp hk
        omega
      simp [layerTerm, hz, hcount]
    rw [hfirst]
    rcases hr with rfl | hp
    · simp [zeroShape]
    · simp only [ite_eq_right (Nat.ne_of_gt hp)]
      exact sum_range_min L (1650 / r.j)
        (fun k hk => fastRemaining_zero (index_over hp hk))
  · have htail (k : ℕ) :
        layerTerm r y L (L + k) = fastRemaining (L * r.b + (k + 1) * (r.b + y.b))
          (L * r.j + (k + 1) * (r.j + y.j)) := by
      have hz : L + k + 1 - L = k + 1 := by omega
      rw [layerTerm, hz, hcount]
      congr 1 <;> ring
    simp_rw [htail]
    apply sum_range_truncate _ (by omega)
    intro k hk
    apply fastRemaining_zero
    exact (index_over hj hk).trans_le (Nat.le_add_left _ _)
theorem availableMass_mono (hcount : ∀ b j, remaining b j = fastRemaining b j)
    {r y : Shape} {L₁ L₂ : ℕ} (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j + y.j) (hL : L₁ ≤ L₂) :
    availableMass r y L₁ ≤ availableMass r y L₂ := by
  let N := L₂ + 1650 / (r.j + y.j)
  rw [← availableMass_eq_sum hcount hr hj (N := N) (Nat.add_le_add_right hL _),
    ← availableMass_eq_sum hcount hr hj (N := N) le_rfl]
  exact Finset.sum_le_sum fun k _ => remaining_anti
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : k + 1 - L₂ ≤ k + 1 - L₁)) _)
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : k + 1 - L₂ ≤ k + 1 - L₁)) _)
theorem ceilDiv_anti (a : ℕ) {l u : ℕ} (hl : 0 < l) (h : l ≤ u) :
    ceilDiv a u ≤ ceilDiv a l := by
  have hu : 0 < u := hl.trans_le h
  have hceil (d q : ℕ) (hd : 0 < d) : ceilDiv a d ≤ q ↔ a ≤ q * d := by
    rw [ceilDiv, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hd, Nat.succ_mul]
    omega
  exact (hceil u _ hu).mpr <|
    ((hceil l _ hl).mp le_rfl).trans (Nat.mul_le_mul_left _ h)
end K1_13_8
end
section
namespace K1_13_8
open K1_13
open scoped BigOperators
def c1 : Prop := ∀ b j, remaining b j = fastRemaining b j
end K1_13_8
end
section
namespace K1_13_8_2
open K1_13 K1_13_8
structure Threshold where
  b : ℕ
  j : ℕ
  l : ℕ
def orderFor (b j : ℕ) : List Threshold → ℕ
  | [] => 1
  | s :: rest =>
      max (if s.b ≤ b ∧ s.j ≤ j then s.l else 1) (orderFor b j rest)
end K1_13_8_2
end
section
namespace K1_13_8_2
open K1_13
def Chamber (p : Shape) : Prop := p.j ≤ p.b ∧ 3 * p.t ≤ p.j
def signedMixed (p q r s : Shape) : ℤ :=
  difference (difference (difference (difference volume32 p) q) r) s ⟨0, 0, 0⟩
private theorem signed_add (p a q r s : Shape) :
    signedMixed (p.plus a) q r s = signedMixed p q r s + signedMixed a q r s := by
  simp only [signedMixed, difference, volume32, Shape.plus, Nat.cast_add, Nat.cast_zero]
  ring
theorem signed_rotate (p q r s : Shape) :
    signedMixed p q r s = signedMixed q r s p := by
  simp only [signedMixed, difference, volume32, Shape.plus, Nat.cast_add, Nat.cast_zero]
  ring
private theorem chamber_coords (p : Shape) (h : Chamber p) :
    (p.b : ℤ) = (↑(p.b - p.j) : ℤ) + ↑(p.j - 3 * p.t) + 3 * p.t ∧
    (p.j : ℤ) = (↑(p.j - 3 * p.t) : ℤ) + 3 * p.t := by
  obtain ⟨hb, hj⟩ := h
  constructor <;> exact_mod_cast (by omega : _)
theorem signed_nonneg (d q r s : Shape) (hq : Chamber q) (hr : Chamber r)
    (hs : Chamber s) : 0 ≤ signedMixed d q r s := by
  obtain ⟨hqb, hqj⟩ := chamber_coords q hq
  obtain ⟨hrb, hrj⟩ := chamber_coords r hr
  obtain ⟨hsb, hsj⟩ := chamber_coords s hs
  simp only [signedMixed, difference, volume32, Shape.plus, Nat.cast_add, Nat.cast_zero]
  rw [hqb, hqj, hrb, hrj, hsb, hsj]
  ring_nf
  positivity
private theorem mixed_mono_first {p p' : Shape} (h : InBox p p') {q r s : Shape}
    (hq : Chamber q) (hr : Chamber r) (hs : Chamber s) :
    mixed32 p q r s ≤ mixed32 p' q r s := by
  let d : Shape := ⟨p'.b - p.b, p'.j - p.j, p'.t - p.t⟩
  have hp : p.plus d = p' := by
    obtain ⟨pb, pj, pt⟩ := p
    obtain ⟨qb, qj, qt⟩ := p'
    obtain ⟨hb, hj, ht⟩ := h
    simp [Shape.plus, d, Nat.add_sub_of_le hb, Nat.add_sub_of_le hj, Nat.add_sub_of_le ht]
  change (signedMixed p q r s).toNat ≤ (signedMixed p' q r s).toNat
  apply Int.toNat_le_toNat
  rw [← hp, signed_add]
  exact le_add_of_nonneg_right (signed_nonneg d q r s hq hr hs)
private theorem mixed_rotate (p q r s : Shape) :
    mixed32 p q r s = mixed32 q r s p := congrArg Int.toNat (signed_rotate p q r s)
theorem mixed_mono {p q r s p' q' r' s' : Shape}
    (hp : InBox p p') (hq : InBox q q') (hr : InBox r r') (hs : InBox s s')
    (hp' : Chamber p') (hq' : Chamber q') (hr' : Chamber r')
    (hqs : Chamber q) (hrs : Chamber r) (hss : Chamber s) :
    mixed32 p q r s ≤ mixed32 p' q' r' s' := by
  calc
    mixed32 p q r s ≤ mixed32 p' q r s := mixed_mono_first hp hqs hrs hss
    _ = mixed32 q r s p' := mixed_rotate _ _ _ _
    _ ≤ mixed32 q' r s p' := mixed_mono_first hq hrs hss hp'
    _ = mixed32 r s p' q' := mixed_rotate _ _ _ _
    _ ≤ mixed32 r' s p' q' := mixed_mono_first hr hss hp' hq'
    _ = mixed32 s p' q' r' := mixed_rotate _ _ _ _
    _ ≤ mixed32 s' p' q' r' := mixed_mono_first hs hp' hq' hr'
    _ = mixed32 p' q' r' s' := mixed_rotate _ _ _ _
end K1_13_8_2
end
section
namespace K1_13_8_4
open K1_13
def TotalLE (a A : Shape) : Prop := a.b ≤ A.b ∧ a.j = A.j ∧ a.t = A.t
def IndexFits (a : Shape) : Prop := 3 * a.t ≤ a.j
theorem TotalLE.refl (a : Shape) : TotalLE a a := ⟨le_rfl, rfl, rfl⟩
private def mixedZ (p q r s : Shape) : ℤ :=
  difference (difference (difference (difference volume32 p) q) r) s ⟨0, 0, 0⟩
private def indexCubic (a : Shape) : ℤ :=
  let j : ℤ := a.j
  let t : ℤ := a.t
  8*j^2*t - 24*j*t^2 + 24*t^3
private def unusedIndex (a : Shape) : ℤ := (a.j : ℤ) - 3 * (a.t : ℤ)
private def totalCoeff (q r s : Shape) : ℤ :=
  let u := unusedIndex q
  let v := unusedIndex r
  let w := unusedIndex s
  let x : ℤ := q.t
  let y : ℤ := r.t
  let z : ℤ := s.t
  16 * (u*v*z + u*y*w + x*v*w) + 48 * (u*y*z + x*v*z + x*y*w) + 144*x*y*z
private theorem totalCoeff_nonneg {q r s : Shape}
    (hq : IndexFits q) (hr : IndexFits r) (hs : IndexFits s) : 0 ≤ totalCoeff q r s := by
  have nonneg {a : Shape} (ha : IndexFits a) : 0 ≤ unusedIndex a := by
    have h : 3 * a.t ≤ a.j := ha
    unfold unusedIndex
    omega
  have hq' := nonneg hq
  have hr' := nonneg hr
  have hs' := nonneg hs
  unfold totalCoeff
  positivity
private theorem difference_sub (f g : Shape → ℤ) (a x : Shape) :
    difference f a x - difference g a x = difference (fun y => f y - g y) a x := by
  unfold difference
  ring
private theorem difference_comm (f : Shape → ℤ) (a b : Shape) :
    difference (difference f a) b = difference (difference f b) a := by
  funext x
  have h : (x.plus b).plus a = (x.plus a).plus b := by
    cases x
    cases a
    cases b
    simp [Shape.plus, Nat.add_right_comm]
  simp only [difference, h]
  ring
set_option maxHeartbeats 2000000 in
private theorem mixed_first {p P q r s : Shape}
    (hp : TotalLE p P) (hq : IndexFits q) (hr : IndexFits r) (hs : IndexFits s) :
    mixed32 p q r s ≤ mixed32 P q r s := by
  rcases hp with ⟨hb, hj, ht⟩
  let d : ℤ := (P.b : ℤ) - (p.b : ℤ)
  have hd : 0 ≤ d := by
    dsimp [d]
    omega
  have hfirst (x : Shape) :
      difference volume32 P x - difference volume32 p x = d * indexCubic (x.plus p) := by
    simp only [difference, volume32, indexCubic, Shape.plus, hj, ht, Nat.cast_add, d]
    ring
  change (mixedZ p q r s).toNat ≤ (mixedZ P q r s).toNat
  apply Int.toNat_le_toNat
  apply sub_nonneg.mp
  unfold mixedZ
  simp only [difference_sub, hfirst]
  have hcoeff :
      difference (difference (difference (fun x => d * indexCubic (x.plus p)) q) r)
        s ⟨0, 0, 0⟩ = d * totalCoeff q r s := by
    simp only [difference, indexCubic, totalCoeff, unusedIndex,
      Shape.plus, Nat.cast_add, Nat.cast_zero]
    ring
  rw [hcoeff]
  exact mul_nonneg hd (totalCoeff_nonneg hq hr hs)
private theorem swap12 (a b c d : Shape) : mixed32 a b c d = mixed32 b a c d := by
  unfold mixed32
  rw [difference_comm volume32 a b]
private theorem swap23 (a b c d : Shape) : mixed32 a b c d = mixed32 a c b d := by
  unfold mixed32
  rw [difference_comm (difference volume32 a) b c]
private theorem swap34 (a b c d : Shape) : mixed32 a b c d = mixed32 a b d c := by
  unfold mixed32
  rw [difference_comm (difference (difference volume32 a) b) c d]
theorem mixed_totalLE {p P q Q r R s S : Shape}
    (hp : TotalLE p P) (hq : TotalLE q Q) (hr : TotalLE r R) (hs : TotalLE s S)
    (hP : IndexFits P) (hQ : IndexFits Q) (hR : IndexFits R)
    (hq' : IndexFits q) (hr' : IndexFits r) (hs' : IndexFits s) :
    mixed32 p q r s ≤ mixed32 P Q R S := by
  calc
    _ ≤ mixed32 P q r s := mixed_first hp hq' hr' hs'
    _ ≤ mixed32 P Q r s := by
      rw [swap12 P q, swap12 P Q]
      exact mixed_first hq hP hr' hs'
    _ ≤ mixed32 P Q R s := by
      rw [swap23 P Q r, swap12 P r, swap23 P Q R, swap12 P R]
      exact mixed_first hr hP hQ hs'
    _ ≤ _ := by
      rw [swap34 P Q R s, swap23 P Q s, swap12 P s,
        swap34 P Q R S, swap23 P Q S, swap12 P S]
      exact mixed_first hs hP hQ hR
theorem TotalLE.indexFits {a A : Shape} (h : TotalLE a A) (ha : IndexFits a) :
    IndexFits A := by
  unfold IndexFits at *
  rw [← h.2.1, ← h.2.2]
  exact ha
theorem mixed_mono_total {p P q Q r R s S : Shape}
    (hp : TotalLE p P) (hq : TotalLE q Q) (hr : TotalLE r R) (hs : TotalLE s S)
    (hp' : IndexFits p) (hq' : IndexFits q) (hr' : IndexFits r) (hs' : IndexFits s) :
    mixed32 p q r s ≤ mixed32 P Q R S :=
  mixed_totalLE hp hq hr hs (hp.indexFits hp') (hq.indexFits hq') (hr.indexFits hr') hq' hr' hs'
end K1_13_8_4
end
section
namespace K1_13_8_1
open K1_13_8
def row (r : ℕ) (j : ℤ) : ℤ :=
  if 0 ≤ j then coefficient r j.toNat else 0
theorem row_neg (r : ℕ) {j : ℤ} (h : j < 0) : row r j = 0 := by
  simp [row, not_le.mpr h]
theorem row_nonneg (r : ℕ) (j : ℤ) : 0 ≤ row r j := by
  unfold row
  split <;> omega
theorem row_nat (r j : ℕ) : row r j = coefficient r j := by simp [row]
def difference (w : ℤ) (f : ℤ → ℤ) (j : ℤ) : ℤ := f j - f (j - w)
def step (j : ℤ) : ℤ := if 0 ≤ j then 1 else 0
private def polynomial (r s : ℕ) (q : ℤ) : ℤ :=
  let (a, b, c, d, e) := coefficients r s
  24 * a + 24 * b * q + 12 * c * q * (q - 1) +
    4 * d * q * (q - 1) * (q - 2) + e * q * (q - 1) * (q - 2) * (q - 3)
private theorem scaled_coefficient (r q s : ℕ) (hq : 3 ≤ q) (hs : s < 6) :
    24 * (coefficient r (6 * q + s) : ℤ) = polynomial r s q := by
  have hdiv : (6 * q + s) / 6 = q := by omega
  have hmod : (6 * q + s) % 6 = s := by omega
  unfold coefficient polynomial
  rw [hdiv, hmod]
  generalize coefficients r s = t
  rcases t with ⟨a, b, c, d, e⟩
  have hd₂ : 2 ∣ q * (q - 1) := by
    simpa [Nat.descFactorial_succ, mul_comm] using Nat.factorial_dvd_descFactorial q 2
  have hd₃ : 6 ∣ q * (q - 1) * (q - 2) := by
    simpa [Nat.descFactorial_succ, Nat.factorial_succ, mul_comm, mul_left_comm, mul_assoc] using
      Nat.factorial_dvd_descFactorial q 3
  have hd₄ : 24 ∣ q * (q - 1) * (q - 2) * (q - 3) := by
    simpa [Nat.descFactorial_succ, Nat.factorial_succ, mul_comm, mul_left_comm, mul_assoc] using
      Nat.factorial_dvd_descFactorial q 4
  have h₂ := congrArg (fun n : ℕ => (n : ℤ)) (Nat.mul_div_cancel' hd₂)
  have h₃ := congrArg (fun n : ℕ => (n : ℤ)) (Nat.mul_div_cancel' hd₃)
  have h₄ := congrArg (fun n : ℕ => (n : ℤ)) (Nat.mul_div_cancel' hd₄)
  simp only [Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Int.ofNat_sub (show 1 ≤ q by omega),
    Int.ofNat_sub (show 2 ≤ q by omega), Int.ofNat_sub hq] at h₂ h₃ h₄
  simp only [Nat.cast_add, Nat.cast_mul]
  linear_combination 12 * (c : ℤ) * h₂ + 4 * (d : ℤ) * h₃ + (e : ℤ) * h₄
private theorem scaled_shift (r q i v : ℕ) (hq : 3 ≤ q) (hv : v ≤ i) :
    24 * row r (6 * (q : ℤ) + i - v) = polynomial r ((i - v) % 6)
      ((q : ℤ) + ((i - v) / 6 : ℕ)) := by
  have h : 6 * (q : ℤ) + i - v =
      ((6 * (q + (i - v) / 6) + (i - v) % 6 : ℕ) : ℤ) := by omega
  rw [h, row_nat, scaled_coefficient r _ _ (by omega) (by omega), Nat.cast_add]
theorem core_step (j : ℤ) :
    difference 1 (difference 2 (difference 3 (row 0))) j = step j := by
  by_cases hn : j < 0
  · simp [difference, step, not_le.mpr hn, row_neg _ hn, row_neg, show j - 3 < 0 by omega,
      show j - 2 < 0 by omega, show j - 2 - 3 < 0 by omega,
      show j - 1 < 0 by omega, show j - 1 - 3 < 0 by omega,
      show j - 1 - 2 < 0 by omega, show j - 1 - 2 - 3 < 0 by omega]
  by_cases hs : j < 24
  · interval_cases j <;> decide
  let q := j.toNat / 6 - 1
  let s := j.toNat % 6
  have hq : 3 ≤ q := by dsimp [q]; omega
  have hsr : s < 6 := by dsimp [s]; omega
  have hj : j = 6 * (q : ℤ) + ((6 + s : ℕ) : ℤ) := by dsimp [q, s]; omega
  have hstep : step j = 1 := by simp [step, show 0 ≤ j by omega]
  have h := scaled_shift 0 q (6 + s) 0 hq (by omega)
  have h₁ := scaled_shift 0 q (6 + s) 1 hq (by omega)
  have h₂ := scaled_shift 0 q (6 + s) 2 hq (by omega)
  have h₄ := scaled_shift 0 q (6 + s) 4 hq (by omega)
  have h₅ := scaled_shift 0 q (6 + s) 5 hq (by omega)
  have h₆ := scaled_shift 0 q (6 + s) 6 hq (by omega)
  have hp : polynomial 0 ((6 + s - 0) % 6) ((q : ℤ) + ((6 + s - 0) / 6 : ℕ)) -
      polynomial 0 ((6 + s - 1) % 6) ((q : ℤ) + ((6 + s - 1) / 6 : ℕ)) -
      polynomial 0 ((6 + s - 2) % 6) ((q : ℤ) + ((6 + s - 2) / 6 : ℕ)) +
      polynomial 0 ((6 + s - 4) % 6) ((q : ℤ) + ((6 + s - 4) / 6 : ℕ)) +
      polynomial 0 ((6 + s - 5) % 6) ((q : ℤ) + ((6 + s - 5) / 6 : ℕ)) -
      polynomial 0 ((6 + s - 6) % 6) ((q : ℤ) + ((6 + s - 6) / 6 : ℕ)) = 24 := by
    clear_value q s
    interval_cases s <;> norm_num [polynomial, coefficients] <;> ring
  rw [← h, ← h₁, ← h₂, ← h₄, ← h₅, ← h₆] at hp
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, sub_zero, ← hj] at hp
  simp only [difference, hstep]
  rw [show j - 2 - 3 = j - 5 by omega, show j - 1 - 3 = j - 4 by omega,
    show j - 1 - 2 = j - 3 by omega, show j - 3 - 3 = j - 6 by omega]
  omega
theorem extra_step (r : ℕ) (hr : 1 ≤ r) (hr' : r ≤ 3) (j : ℤ) :
    difference r (row r) j = row 0 j := by
  by_cases hn : j < 0
  · simp [difference, row_neg _ hn, row_neg _ (show j - r < 0 by omega)]
  by_cases hs : j < 24
  · interval_cases r <;> interval_cases j <;> decide
  let q := j.toNat / 6 - 1
  let s := j.toNat % 6
  have hq : 3 ≤ q := by dsimp [q]; omega
  have hsr : s < 6 := by dsimp [s]; omega
  have hj : j = 6 * (q : ℤ) + ((6 + s : ℕ) : ℤ) := by dsimp [q, s]; omega
  have h₁ := scaled_shift r q (6 + s) 0 hq (by omega)
  have h₂ := scaled_shift r q (6 + s) r hq (by omega)
  have h₃ := scaled_shift 0 q (6 + s) 0 hq (by omega)
  have hp : polynomial r ((6 + s - 0) % 6) ((q : ℤ) + ((6 + s - 0) / 6 : ℕ)) -
      polynomial r ((6 + s - r) % 6) ((q : ℤ) + ((6 + s - r) / 6 : ℕ)) =
      polynomial 0 ((6 + s - 0) % 6) ((q : ℤ) + ((6 + s - 0) / 6 : ℕ)) := by
    clear_value q s
    interval_cases r <;> interval_cases s <;> norm_num [polynomial, coefficients] <;> ring
  rw [← h₁, ← h₂, ← h₃] at hp
  simp only [Nat.cast_zero, sub_zero, ← hj] at hp
  unfold difference
  omega
end K1_13_8_1
end
section
namespace K1_13_8_1
open scoped BigOperators
private def count (base : ℕ → ℤ → ℤ) : ℕ → ℕ → ℤ → ℤ
  | 0, b, j => base b j
  | k + 1, b, j =>
      ∑ i ∈ Finset.range (b + 1), count base k (b - i) (j - ((k : ℤ) + 1) * i)
private def exactBase (_ : ℕ) (j : ℤ) : ℤ := step j
private def boxBase (b : ℕ) (j : ℤ) : ℤ := ((b : ℤ) + 1) * step j
private theorem count_zero_degree (base : ℕ → ℤ → ℤ) (k : ℕ) (j : ℤ) :
    count base k 0 j = base 0 j := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [count] using ih
private theorem count_succ_degree (base : ℕ → ℤ → ℤ) (k b : ℕ) (j : ℤ) :
    count base (k + 1) (b + 1) j =
      count base k (b + 1) j + count base (k + 1) b (j - ((k : ℤ) + 1)) := by
  simp only [count]
  rw [Finset.sum_range_succ', add_comm]
  simp only [Nat.sub_zero, Nat.cast_zero, mul_zero, sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show b + 1 - (i + 1) = b - i by omega]
  congr 1
  push_cast
  ring
private theorem count_neg (base : ℕ → ℤ → ℤ)
    (hn : ∀ b j, j < 0 → base b j = 0) (k b : ℕ) (j : ℤ) (hj : j < 0) :
    count base k b j = 0 := by
  induction k generalizing b j with
  | zero => exact hn b j hj
  | succ k ih =>
      apply Finset.sum_eq_zero
      intro i _
      apply ih
      have h : 0 ≤ ((k : ℤ) + 1) * (i : ℤ) := by positivity
      omega
private theorem count_clip (base : ℕ → ℤ → ℤ)
    (hn : ∀ b j, j < 0 → base b j = 0) (k b j : ℕ) :
    count base (k + 1) b j =
      ∑ i ∈ Finset.range (min b (j / (k + 1)) + 1),
        count base k (b - i) (j - (k + 1) * i : ℕ) := by
  let w := k + 1
  let f := fun i : ℕ => count base k (b - i) ((j : ℤ) - (w : ℤ) * i)
  change (∑ i ∈ Finset.range (b + 1), f i) = _
  have hw : 0 < w := by dsimp [w]; omega
  calc
    _ = ∑ i ∈ Finset.range (min b (j / w) + 1), f i := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (min_le_left _ _)))
      intro i hi hout
      have hib := Finset.mem_range.mp hi
      have hij : j / w < i := by
        have h := mt Finset.mem_range.mpr hout
        omega
      have hs := (Nat.div_lt_iff_lt_mul hw).mp hij
      unfold f
      apply count_neg base hn
      rw [← Nat.cast_mul, mul_comm w i]
      exact sub_neg.mpr (by exact_mod_cast hs)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hm := Finset.mem_range.mp hi
      have hij : i ≤ j / w := by omega
      have hs := (Nat.le_div_iff_mul_le hw).mp hij
      rw [mul_comm] at hs
      unfold f
      rw [← Nat.cast_mul, Int.ofNat_sub hs]
private theorem boxBase_neg (b : ℕ) (j : ℤ) (h : j < 0) : boxBase b j = 0 := by
  simp [boxBase, step, not_le.mpr h]
private theorem symbols_count (b j : ℕ) :
    (K1_13.symbols b j : ℤ) = count boxBase 3 b j := by
  rw [count_clip boxBase boxBase_neg 2]
  simp_rw [count_clip boxBase boxBase_neg 1, count_clip boxBase boxBase_neg 0]
  simp [K1_13.symbols, count, boxBase, step, Nat.cast_sum, Nat.cast_add]
private theorem box_eq_sum (k b : ℕ) (j : ℤ) :
    count boxBase k b j = ∑ d ∈ Finset.range (b + 1), count exactBase k d j := by
  induction k generalizing b j with
  | zero => simp [count, boxBase, exactBase, Nat.cast_add]
  | succ k ihk =>
      induction b generalizing j with
      | zero => simp [count_zero_degree, boxBase, exactBase]
      | succ b ihb =>
          rw [count_succ_degree, ihk, ihb]
          conv_rhs => rw [Finset.sum_range_succ']
          simp_rw [count_succ_degree exactBase, Finset.sum_add_distrib]
          rw [Finset.sum_range_succ' (fun d => count exactBase k d j) (b + 1)]
          simp only [count_zero_degree]
          abel
private def shift (w : ℤ) (f : ℤ → ℤ) (j : ℤ) : ℤ := f (j - w)
private def factors (a : ℤ) : ℕ → (ℤ → ℤ) → (ℤ → ℤ)
  | 0, f => f
  | k + 1, f => factors a k (difference (a + k) f)
private theorem factors_first (a : ℤ) (k : ℕ) (f : ℤ → ℤ) :
    factors a (k + 1) f = factors (a + 1) k (difference a f) := by
  induction k generalizing f with
  | zero => simp [factors]
  | succ k ih =>
      rw [factors, ih, factors]
      have h : a + ((k + 1 : ℕ) : ℤ) = a + 1 + k := by omega
      rw [h]
      congr 1
      funext j
      simp only [difference]
      rw [show j - a - (a + 1 + k) = j - (a + 1 + k) - a by ring]
      ring
private theorem factors_sub (a : ℤ) (k : ℕ) (f g : ℤ → ℤ) :
    factors a k (fun j => f j - g j) = fun j => factors a k f j - factors a k g j := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih =>
      have h : difference (a + k) (fun j => f j - g j) =
          fun j => difference (a + k) f j - difference (a + k) g j := by
        funext j
        simp only [difference]
        ring
      simpa only [factors, h] using ih (difference (a + k) f) (difference (a + k) g)
private theorem factors_shift (a w : ℤ) (k : ℕ) (f : ℤ → ℤ) :
    factors a k (shift w f) = shift w (factors a k f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      have h : difference (a + k) (shift w f) = shift w (difference (a + k) f) := by
        funext j
        simp only [difference, shift]
        rw [show j - (a + k) - w = j - w - (a + k) by ring]
      simpa only [factors, h] using ih (difference (a + k) f)
private def denominator : ℕ → ℤ → ℤ
  | 0 => difference 1 (difference 2 (difference 3 (row 0)))
  | 1 => difference 2 (difference 3 (row 0))
  | 2 => difference 3 (row 0)
  | _ => row 0
private theorem denominator_diff (k : ℕ) (hk : k < 3) :
    difference ((k : ℤ) + 1) (denominator (k + 1)) = denominator k := by
  interval_cases k <;> rfl
def gaussian (k b : ℕ) : ℤ → ℤ := factors ((b : ℤ) + 1) k (denominator k)
private theorem gaussian_zero (k : ℕ) (hk : k ≤ 3) (j : ℤ) : gaussian k 0 j = step j := by
  induction k with
  | zero => exact core_step j
  | succ k ih =>
      have hd := denominator_diff k (by omega)
      simpa only [gaussian, factors, Nat.cast_zero, zero_add, add_comm (1 : ℤ) k, hd] using
        ih (by omega)
private theorem gaussian_succ (k b : ℕ) (hk : k < 3) (j : ℤ) :
    gaussian (k + 1) (b + 1) j =
      gaussian k (b + 1) j + gaussian (k + 1) b (j - ((k : ℤ) + 1)) := by
  let a := (b : ℤ) + 1
  let w := (k : ℤ) + 1
  let f := denominator (k + 1)
  have ha : ((b + 1 : ℕ) : ℤ) + 1 = a + 1 := by rfl
  simp only [gaussian, ha]
  change factors (a + 1) (k + 1) f j =
    factors (a + 1) k (denominator k) j + factors a (k + 1) f (j - w)
  rw [factors_first a k]
  apply sub_eq_iff_eq_add.mp
  change factors (a + 1) k (difference (a + 1 + k) f) j -
      shift w (factors (a + 1) k (difference a f)) j = _
  rw [← factors_shift, ← congrFun (factors_sub _ _ _ _) j]
  have h : (fun j => difference (a + 1 + k) f j - shift w (difference a f) j) =
      difference w f := by
    funext j
    simp only [difference, shift, w]
    rw [show j - (a + 1 + k) = j - ((k : ℤ) + 1) - a by ring]
    ring
  rw [h, denominator_diff k hk]
private theorem exact_gaussian (k b : ℕ) (hk : k ≤ 3) (j : ℤ) :
    count exactBase k b j = gaussian k b j := by
  induction k generalizing b j with
  | zero => exact (core_step j).symm
  | succ k ihk =>
      induction b generalizing j with
      | zero => exact (count_zero_degree _ _ _).trans (gaussian_zero _ hk _).symm
      | succ b ihb =>
          rw [count_succ_degree, gaussian_succ k b (by omega), ihk _ (by omega), ihb]
theorem symbols_gaussian (b j : ℕ) :
    (K1_13.symbols b j : ℤ) = ∑ d ∈ Finset.range (b + 1), gaussian 3 d j := by
  rw [symbols_count, box_eq_sum]
  exact Finset.sum_congr rfl fun d _ => exact_gaussian 3 d (by omega) j
theorem gaussian_expand (d : ℕ) (j : ℤ) :
    gaussian 3 d j =
      row 0 j - (row 0 (j - (1 + d)) + row 0 (j - (2 + d)) + row 0 (j - (3 + d))) +
        (row 0 (j - (3 + 2 * d)) + row 0 (j - (4 + 2 * d)) + row 0 (j - (5 + 2 * d))) -
        row 0 (j - (6 + 3 * d)) := by
  simp only [gaussian, factors, denominator, difference]
  push_cast
  ring_nf
end K1_13_8_1
end
section
namespace K1_13_8_1
open K1_13_8
open scoped BigOperators
private theorem sum_shifted (b r : ℕ) (hr : 1 ≤ r) (hr' : r ≤ 3) (j v : ℤ) :
    (∑ d ∈ Finset.range (b + 1), row 0 (j - (v + (r : ℤ) * d))) =
      row r (j - v) - row r (j - (v + (r : ℤ) * ((b : ℤ) + 1))) := by
  induction b with
  | zero =>
      simpa [difference, sub_sub] using (extra_step r hr hr' (j - v)).symm
  | succ b ih =>
      rw [Finset.sum_range_succ, ih]
      have h := extra_step r hr hr' (j - (v + (r : ℤ) * ((b : ℤ) + 1)))
      simp only [difference] at h
      simp only [Nat.cast_succ]
      rw [show j - (v + (r : ℤ) * ((b : ℤ) + 1)) - r =
        j - (v + (r : ℤ) * ((b : ℤ) + 1 + 1)) by ring] at h
      omega
private theorem shifted_cast (r j v : ℕ) :
    (shifted r j v : ℤ) = row r ((j : ℤ) - v) := by
  unfold shifted
  split
  · rw [← Int.ofNat_sub ‹v ≤ j›, row_nat]
  · have h : (j : ℤ) - v < 0 := by omega
    simp [row_neg _ h]
private theorem across_cast (b r j v : ℕ) (hr : 1 ≤ r) (hr' : r ≤ 3) :
    (across b r j v : ℤ) = row r ((j : ℤ) - v) -
      row r ((j : ℤ) - (v + (r : ℤ) * ((b : ℤ) + 1))) := by
  have h₁ := shifted_cast r j v
  have h₂ := shifted_cast r j (v + r * (b + 1))
  push_cast at h₂
  have hn : 0 ≤ row r ((j : ℤ) - v) - row r ((j : ℤ) - (v + (r : ℤ) * ((b : ℤ) + 1))) := by
    rw [← sum_shifted b r hr hr']
    exact Finset.sum_nonneg fun _ _ => row_nonneg _ _
  unfold across
  rw [Int.ofNat_sub (by omega), h₁, h₂]
private theorem cast_sub_of_eq {count positive negative : ℕ}
    (h : (count : ℤ) = (positive : ℤ) - (negative : ℤ)) :
    count = positive - negative := by omega
theorem symbols_eq_fast (b j : ℕ) : K1_13.symbols b j = fastSymbols b j := by
  unfold fastSymbols
  apply cast_sub_of_eq
  rw [symbols_gaussian]
  simp only [gaussian_expand, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    across_cast b 1 j _ (by decide) (by decide),
    across_cast b 2 j _ (by decide) (by decide),
    across_cast b 3 j _ (by decide) (by decide), ← row_nat]
  have h (v : ℤ) :
      (∑ d ∈ Finset.range (b + 1), row 0 (j - (v + (d : ℤ)))) =
        row 1 (j - v) - row 1 (j - (v + ((b : ℤ) + 1))) := by
    simpa only [Nat.cast_one, one_mul] using sum_shifted b 1 (by decide) (by decide) j v
  have h₂ (v : ℤ) :
      (∑ d ∈ Finset.range (b + 1), row 0 (j - (v + 2 * d))) =
        row 2 (j - v) - row 2 (j - (v + 2 * ((b : ℤ) + 1))) := by
    simpa only [Nat.cast_ofNat] using sum_shifted b 2 (by decide) (by decide) j v
  have h₃ :
      (∑ d ∈ Finset.range (b + 1), row 0 (j - (6 + 3 * d))) =
        row 3 (j - 6) - row 3 (j - (6 + 3 * ((b : ℤ) + 1))) := by
    simpa only [Nat.cast_ofNat] using sum_shifted b 3 (by decide) (by decide) j 6
  rw [h 1, h 2, h 3, h₂ 3, h₂ 4, h₂ 5, h₃]
  norm_num
  ring
theorem proof : K1_13_8.c1 := by
  intro b j
  simp only [K1_13.remaining, fastRemaining, symbols_eq_fast]
end K1_13_8_1
end
section
namespace K1_14_2_2_2
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_3_2
open scoped BigOperators
def afterGcd (s : Shape) (x y : ℕ) : Shape :=
  ⟨s.m, s.B-y, min s.J (s.B-y), s.U-x⟩
abbrev cheapZero : Shape := (stageAt 0).cheap
abbrev layeredZero : Shape := (stageAt 0).layered
structure PreparedPair (P Q : Jet) (G H : ODE) where
  seedContent : Seeds
  cheap : Jet
  layered : Jet
  ordinary : Finset Equation
  gcdSeed : ℕ
  gcdY : ℕ
  seedContent_ne : seedContent ≠ 0
  seedContent_degree : seedContent.totalDegree ≤ 1899+8441
  gcdSeed_le : gcdSeed ≤ 1899
  gcdY_le : gcdY ≤ 82
  cheap_caps : RowCaps cheap (afterGcd cheapZero gcdSeed gcdY)
  layered_caps : RowCaps layered (afterGcd layeredZero gcdSeed gcdY)
  proper : ProperPair cheap layered
  ordinary_factors : ∀ f ∈ ordinary, Irreducible f ∧ 0 < f.natDegree
  ordinary_seed : ∑ f ∈ ordinary, ordinarySeedDegree f ≤ gcdSeed
  ordinary_y : ∑ f ∈ ordinary, f.natDegree ≤ gcdY
  cover : ∀ z S, jetAt P z S = 0 → jetAt Q z S = 0 →
    fixedAt G S = 0 ∨ fixedAt H S = 0 ∨ graphEval z seedContent = 0 ∨
    (jetAt cheap z S = 0 ∧ jetAt layered z S = 0) ∨ ∃ f ∈ ordinary, atMark f z S = 0
structure FiniteSections (I : Ideal Ambient) : Prop where
  seeds : Module.Finite SeedField (OverSeeds I)
  ordinate : Module.Finite SectionField (OverOrdinate I)
  mixed : Module.Finite SectionField (OverMixed I)
  jets : Module.Finite SeedField (OverJets I)
def ComponentsOn (P Q : Jet) (S : Finset (Ideal Ambient)) : Prop :=
  ∀ I ∈ S, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ toJet P ∈ I ∧ toJet Q ∈ I
def residualBudget (s t : Shape) : Fin 4 → ℕ :=
  ![s.B*t.J + t.B*s.J - s.J*t.J,
    s.U*t.J + t.U*s.J, s.U*t.B + t.U*s.B, s.U*t.U]
def ordinaryBudget (x y : ℕ) : Fin 4 → ℕ := ![y, x, 2*x*y, x*x]
end
end K1_14_2_2_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace K1_14_2_2_2
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_3_2 Polynomial
open scoped BigOperators Classical
theorem length_le_mass {S : Finset (Ideal Ambient)} {I : Ideal Ambient} (hI : I ∈ S)
    (k : Fin 4) : sectionDegree I k ≤ mass S k :=
  Finset.single_le_sum (f := fun J => sectionDegree J k) (fun _ _ => Nat.zero_le _) hI
private theorem eval_ordinate (z : K) (R : (Polynomial K)) (f : (Polynomial FX)) :
    jetMarkHom z R (ordinateIncl f) = f.eval (atX R) := by
  have hC : (jetMarkHom z R).comp MvPolynomial.C = RingHom.id FX :=
    RingHom.ext fun c => by simp [jetMarkHom]
  have hY : jetMarkHom z R (MvPolynomial.X 2) = atX R := by simp [jetMarkHom]
  change jetMarkHom z R (f.eval₂ MvPolynomial.C (MvPolynomial.X 2)) = f.eval (atX R)
  rw [Polynomial.hom_eval₂, hC, hY, Polynomial.eval₂_id]
theorem ordinate_eq {I : Ideal Ambient} (hI : I.IsPrime)
    (hn : ¬ Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl))
    {z z' : K} {R R' : (Polynomial K)} (h : OnJet I z R) (h' : OnJet I z' R') : atX R = atX R' := by
  let : I.IsPrime := hI
  let φ := (Ideal.Quotient.mk I).comp ordinateIncl
  let J := RingHom.ker φ
  have hJ : J.IsMaximal :=
    (RingHom.ker_isPrime φ).isMaximal_of_ne_bot
      (fun eq => hn ((RingHom.injective_iff_ker_eq_bot φ).mpr eq))
  have heval {w : K} {S : (Polynomial K)} (hS : OnJet I w S) :
      J ≤ RingHom.ker (evalRingHom (atX S)) := by
    intro f hf
    have hm : ordinateIncl f ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp hf)
    exact RingHom.mem_ker.mpr ((eval_ordinate w S f).symm.trans (RingHom.mem_ker.mp (hS hm)))
  have heq := hJ.eq_of_le (RingHom.ker_ne_top _) (heval h)
  have hlin : (Polynomial.X (R := FX) - Polynomial.C (atX R)) ∈ J := by
    rw [heq]
    apply RingHom.mem_ker.mpr
    simp
  have hv := RingHom.mem_ker.mp (heval h' hlin)
  simpa [sub_eq_zero, eq_comm] using hv
end
end K1_14_2_2_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace K1_14_2_2_2
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_3_2 Polynomial
open scoped BigOperators Classical
def c2 : Prop :=
  ∀ f : Equation, Irreducible f → 0 < f.natDegree → f.natDegree < p →
    ∃ g a, K1_14_3.IsClearing f g a ∧ ProperPair (C f) (K1_14_3.ordinaryCutter g) ∧
      ∀ z S, atMark f z S = 0 → jetAt (K1_14_3.ordinaryCutter g) z S = 0
def c3 : Prop :=
  ∀ P Q : Jet, ProperPair P Q →
    ∃ S : Finset (Ideal Ambient), ComponentsOn P Q S ∧
      ∀ z R, jetAt P z R = 0 → jetAt Q z R = 0 → ∃ I ∈ S, OnJet I z R
def c4 : Prop :=
  ∀ P Q : Jet, ProperPair P Q → ∀ s t,
    s.J ≤ s.B → t.J ≤ t.B → RowCaps P s → RowCaps Q t →
    ∀ S, ComponentsOn P Q S →
      (∀ I ∈ S, FiniteSections I) ∧ Fits S (residualBudget s t)
def c6 : Prop :=
  ∀ I : Ideal Ambient, I.IsPrime → ringKrullDim (CoordinateRing I) = 2 →
    FiniteSections I → sectionDegree I 0 = 0 →
    ∃ C : K1_14_3.SeedCover, C.curve.totalDegree ≤ sectionDegree I 2 ∧
      C.points.card ≤ sectionDegree I 3 ∧ ∀ z R, OnJet I z R → C.Covers z
end
end K1_14_2_2_2
end
section
namespace K1_14_2_2_2_5
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 Polynomial
open K1_14_3 (Slice)
abbrev SliceField : Slice → Type
  | .seed | .jets => SeedField
  | .ordinate | .mixed => SectionField
instance (s : Slice) : Field (SliceField s) := by
  cases s <;> infer_instance
abbrev Plane (F : Type) [Field F] := MvPolynomial (Fin 2) F
def lineElim (mixed : Bool) : SectionAmbient →ₐ[SectionField] Plane SectionField :=
  MvPolynomial.aeval
    ![MvPolynomial.C (sliceParameter 2) - MvPolynomial.C (sliceParameter 0) * MvPolynomial.X 0,
      MvPolynomial.X 0,
      MvPolynomial.C (sliceParameter 3) -
        MvPolynomial.C (if mixed then sliceParameter 1 else 0) * MvPolynomial.X 1,
      MvPolynomial.X 1]
def sliceEval : (s : Slice) → Ambient →+* Plane (SliceField s)
  | .seed => mapGenericSeed
  | .ordinate => (lineElim false).toRingHom.comp sectionBase
  | .mixed => (lineElim true).toRingHom.comp sectionBase
  | .jets => mapGenericJets
abbrev SliceQuotient (s : Slice) (I : Ideal Ambient) :=
  CoordinateRing (I.map (sliceEval s))
end
end K1_14_2_2_2_5
end
section
set_option autoImplicit false
namespace K1_14_2_2_2_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2
open K1_14_3 (Slice)
def SliceField : Slice → Type
  | .seed | .jets => SeedField
  | .ordinate | .mixed => SectionField
instance (s : Slice) : Field (SliceField s) := by
  cases s <;> unfold SliceField <;> infer_instance
def coefficients (s : Slice) : FX →+* SliceField s :=
  match s with
  | .seed | .jets => algebraMap FX SeedField
  | .ordinate | .mixed => algebraMap FX SectionField
abbrev Plane (F : Type) [Field F] := MvPolynomial (Fin 2) F
def seedCoordinates (s : Slice) : Fin 2 → Plane (SliceField s) :=
  match s with
  | .seed => fun i => MvPolynomial.C (generic i)
  | .ordinate | .mixed =>
    ![MvPolynomial.C (sliceParameter 2) - MvPolynomial.C (sliceParameter 0) * MvPolynomial.X 0,
      MvPolynomial.X 0]
  | .jets => MvPolynomial.X
def ordinateCoordinate (s : Slice) : Plane (SliceField s) :=
  match s with
  | .seed => MvPolynomial.X 0
  | .ordinate => MvPolynomial.C (sliceParameter 3)
  | .mixed => MvPolynomial.C (sliceParameter 3) - MvPolynomial.C (sliceParameter 1) * MvPolynomial.X 1
  | .jets => MvPolynomial.C (generic 0)
def derivativeCoordinate (s : Slice) : Plane (SliceField s) :=
  match s with
  | .jets => MvPolynomial.C (generic 1)
  | .seed | .ordinate | .mixed => MvPolynomial.X 1
def coordinates (s : Slice) : Fin 4 → Plane (SliceField s) :=
  ![seedCoordinates s 0, seedCoordinates s 1, ordinateCoordinate s, derivativeCoordinate s]
def planeMap (s : Slice) : Ambient →+* Plane (SliceField s) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (coefficients s)) (coordinates s)
def rowMap (s : Slice) : Jet →+* Plane (SliceField s) := (planeMap s).comp toJet
def PrimeTransport (s : Slice) : Prop :=
  ∀ I : Ideal Ambient, I.IsPrime →
    I.map (planeMap s) = ⊤ ∨
      (I.map (planeMap s)).IsPrime ∧ (I.map (planeMap s)).comap (planeMap s) = I
structure PlaneProper {F : Type} [Field F] (P Q : Plane F) : Prop where
  left_ne : P ≠ 0
  right_ne : Q ≠ 0
  no_common : ∀ D : Plane F, Irreducible D → D ∣ P → ¬ D ∣ Q
def PlaneCaps (s : Slice) (d : Shape) (P : Plane (SliceField s)) : Prop :=
  match s with
  | .seed => P.totalDegree ≤ d.B ∧ P.degreeOf 1 ≤ d.J
  | .ordinate => P.degreeOf 0 ≤ d.U ∧ P.degreeOf 1 ≤ d.J
  | .mixed => P.degreeOf 0 ≤ d.U ∧ P.degreeOf 1 ≤ d.B
  | .jets => P.totalDegree ≤ d.U
abbrev PairQuotient {F : Type} [Field F] (P Q : Plane F) :=
  Plane F ⧸ Ideal.span ({P, Q} : Set (Plane F))
def ColengthAtMost {F : Type} [Field F] (P Q : Plane F) (n : ℕ) : Prop :=
  Module.Finite F (PairQuotient P Q) ∧ Module.finrank F (PairQuotient P Q) ≤ n
end
end K1_14_2_2_2_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_2_5
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 Polynomial
open K1_14_3 (Slice)
open scoped BigOperators
private def lineCut (mixed : Bool) : Ideal SectionAmbient :=
  Ideal.span {sectionSeedLine, (if mixed then sectionJetLine else
    MvPolynomial.X 2 - MvPolynomial.C (sliceParameter 3))}
private def freeIncl : Plane SectionField →ₐ[SectionField] SectionAmbient :=
  MvPolynomial.rename ![1, 3]
private theorem lineElim_surjective (mixed : Bool) : Function.Surjective (lineElim mixed) := by
  have h : (lineElim mixed).comp freeIncl = AlgHom.id _ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [lineElim, freeIncl]
  intro q
  exact ⟨freeIncl q, DFunLike.congr_fun h q⟩
private theorem lineElim_ker (mixed : Bool) :
    RingHom.ker (lineElim mixed).toRingHom = lineCut mixed := by
  let π := Ideal.Quotient.mkₐ SectionField (lineCut mixed)
  have hconst (a : SectionField) :
      π (MvPolynomial.C a) = algebraMap SectionField (SectionAmbient ⧸ lineCut mixed) a :=
    π.commutes a
  have hseed : π sectionSeedLine = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hjet : π (if mixed then sectionJetLine else
      MvPolynomial.X 2 - MvPolynomial.C (sliceParameter 3)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have h : (π.comp freeIncl).comp (lineElim mixed) = π := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [lineElim, freeIncl]
      simp only [sectionSeedLine, map_sub, map_add, map_mul, hconst] at hseed
      linear_combination -hseed
    · simp [lineElim, freeIncl]
    · cases mixed <;> simp [lineElim, freeIncl]
      · simp only [Bool.false_eq_true, ite_false, map_sub, hconst] at hjet
        linear_combination -hjet
      · simp only [ite_true, sectionJetLine, map_sub, map_add, map_mul, hconst] at hjet
        linear_combination -hjet
    · simp [lineElim, freeIncl]
  apply le_antisymm
  · intro q hq
    have hq' : lineElim mixed q = 0 := hq
    have he := DFunLike.congr_fun h q
    simp only [AlgHom.comp_apply, hq', map_zero] at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he.symm
  · apply Ideal.span_le.mpr
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · change lineElim mixed sectionSeedLine = 0
      simp [sectionSeedLine, lineElim]
    · change lineElim mixed (if mixed then sectionJetLine else _) = 0
      cases mixed <;> simp [sectionJetLine, lineElim]
private def lineQuotientEquiv (mixed : Bool) (I : Ideal Ambient) :
    CoordinateRing (I.map sectionBase ⊔ lineCut mixed) ≃ₐ[SectionField]
      CoordinateRing (I.map ((lineElim mixed).toRingHom.comp sectionBase)) := by
  let e := lineElim mixed
  let J := I.map sectionBase
  let J' := J.map e.toRingHom
  have he : Function.Surjective e.toRingHom := lineElim_surjective mixed
  have hh : J'.comap e.toRingHom = J ⊔ lineCut mixed := by
    change (J.map e.toRingHom).comap e.toRingHom = _
    rw [Ideal.comap_map_of_surjective _ he, ← RingHom.ker_eq_comap_bot]
    exact congrArg (J ⊔ ·) (lineElim_ker mixed)
  let g := Ideal.quotientMapₐ J' e hh.ge
  have hg : Function.Bijective g := ⟨Ideal.quotientMap_injective' (H := hh.ge) hh.le,
    Ideal.quotientMap_surjective (H := hh.ge) he⟩
  change CoordinateRing (J ⊔ lineCut mixed) ≃ₐ[SectionField]
    CoordinateRing (I.map (e.toRingHom.comp sectionBase))
  rw [← Ideal.map_map]
  exact AlgEquiv.ofBijective g hg
def ordinateEquiv (I : Ideal Ambient) :
    OverOrdinate I ≃ₐ[SectionField] SliceQuotient .ordinate I :=
  lineQuotientEquiv false I
def mixedEquiv (I : Ideal Ambient) :
    OverMixed I ≃ₐ[SectionField] SliceQuotient .mixed I :=
  lineQuotientEquiv true I
end
end K1_14_2_2_2_5
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1000000
namespace K1_14_2_2_2_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_3_2 Polynomial
open K1_14_3 (Slice)
theorem toJet_seed (A : Seeds) : toJet (C (C A)) = rootIncl (rootSeeds A) := by
  simp [toJet, toRoot]
theorem toJet_ordinate : toJet (C (Polynomial.X (R := Seeds))) = MvPolynomial.X 2 := by
  simp [toJet, toRoot, rootIncl]
theorem toJet_derivative : toJet (Polynomial.X (R := Equation)) = MvPolynomial.X 3 := by
  simp [toJet]
private def fromAmbient : Ambient →+* Jet :=
  MvPolynomial.eval₂Hom (C.comp (C.comp MvPolynomial.C))
    ![C (C (MvPolynomial.X 0)), C (C (MvPolynomial.X 1)), C Polynomial.X, Polynomial.X]
private theorem fromAmbient_seed :
    fromAmbient.comp (rootIncl.comp rootSeeds) =
      (C : Equation →+* Jet).comp (C : Seeds →+* Equation) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [fromAmbient, rootIncl, rootSeeds]
  · intro i
    fin_cases i <;> simp [fromAmbient, rootIncl, rootSeeds]
private theorem left_inverse : fromAmbient.comp toJet = RingHom.id Jet := by
  apply Polynomial.ringHom_ext
  · intro A
    change ((fromAmbient.comp toJet).comp (C : Equation →+* Jet)) A = (C : Equation →+* Jet) A
    suffices h : (fromAmbient.comp toJet).comp (C : Equation →+* Jet) = C from
      RingHom.congr_fun h A
    apply Polynomial.ringHom_ext
    · intro B
      change fromAmbient (toJet (C (C B))) = C (C B)
      rw [toJet_seed]
      exact RingHom.congr_fun fromAmbient_seed B
    · simp [RingHom.comp_apply, toJet_ordinate, fromAmbient]
  · simp [RingHom.comp_apply, toJet_derivative, fromAmbient]
private theorem right_inverse : toJet.comp fromAmbient = RingHom.id Ambient := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [fromAmbient, toJet_seed, rootIncl, rootSeeds]
  · intro i
    fin_cases i <;> simp [fromAmbient, toJet_seed, toJet_ordinate, toJet_derivative,
      rootIncl, rootSeeds]
private def jetEquiv : Jet ≃+* Ambient :=
  { toJet with
    invFun := fromAmbient
    left_inv := RingHom.congr_fun left_inverse
    right_inv := RingHom.congr_fun right_inverse }
private theorem transport_injective {A T : Type} [CommRing A] [IsDomain A]
    [CommRing T] [Nontrivial T] (g : A →+* T)
    (ht : ∀ I : Ideal A, I.IsPrime →
      I.map g = ⊤ ∨ (I.map g).IsPrime ∧ (I.map g).comap g = I) :
    Function.Injective g := by
  have h := ht ⊥ Ideal.isPrime_bot
  rw [Ideal.map_bot] at h
  exact (RingHom.injective_iff_ker_eq_bot g).mpr (h.resolve_left bot_ne_top).2
private theorem map_proper {R A T : Type}
    [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [CommRing T] [IsDomain T] [UniqueFactorizationMonoid T]
    (e : R ≃+* A) (g : A →+* T)
    (ht : ∀ I : Ideal A, I.IsPrime →
      I.map g = ⊤ ∨ (I.map g).IsPrime ∧ (I.map g).comap g = I)
    (P Q : R) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hcop : ∀ a : R, Irreducible a → a ∣ P → ¬ a ∣ Q) :
    let f := g.comp e.toRingHom
    f P ≠ 0 ∧ f Q ≠ 0 ∧ ∀ D : T, Irreducible D → D ∣ f P → ¬ D ∣ f Q := by
  let f := g.comp e.toRingHom
  change f P ≠ 0 ∧ f Q ≠ 0 ∧ ∀ D : T, Irreducible D → D ∣ f P → ¬ D ∣ f Q
  have hf : Function.Injective f := (transport_injective g ht).comp e.injective
  refine ⟨(map_ne_zero_iff f hf).mpr hP, (map_ne_zero_iff f hf).mpr hQ, ?_⟩
  intro D hD hdP hdQ
  have hprime := hD.prime
  have hex : ∀ B : R, B ≠ 0 → D ∣ f B → ∃ a : R, Irreducible a ∧ a ∣ B ∧ D ∣ f a := by
    intro B
    induction B using WfDvdMonoid.induction_on_irreducible with
    | zero => simp
    | unit B hB =>
      intro _ h
      exact (hD.not_isUnit (isUnit_of_dvd_unit h (hB.map f))).elim
    | mul B a hB ha ih =>
      intro _ h
      rw [map_mul] at h
      rcases hprime.dvd_mul.mp h with h | h
      · exact ⟨a, ha, dvd_mul_right a B, h⟩
      · obtain ⟨b, hb, hba, hbd⟩ := ih hB h
        exact ⟨b, hb, hba.trans ⟨a, mul_comm a B⟩, hbd⟩
  obtain ⟨a, ha, haP, hDa⟩ := hex P hP hdP
  have ha' : Irreducible (e a) := ha.map e.toMulEquiv
  let I : Ideal A := Ideal.span {e a}
  have hI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime ha'.prime
  have hspan : I.map g = Ideal.span {f a} := by
    change (Ideal.span {e a}).map g = _
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hnt : I.map g ≠ ⊤ := by
    rw [hspan]
    exact fun h => hD.not_isUnit (isUnit_of_dvd_unit hDa (Ideal.span_singleton_eq_top.mp h))
  have htrans := (ht I hI).resolve_left hnt
  have hJ : (Ideal.span {f a}).IsPrime := hspan ▸ htrans.1
  have hfa : f a ≠ 0 := (map_ne_zero_iff f hf).mpr ha.ne_zero
  have haf : Prime (f a) := (Ideal.span_singleton_prime hfa).mp hJ
  have had : f a ∣ D := (hD.associated_of_dvd haf.irreducible hDa).dvd'
  have hQmem : e Q ∈ I := by
    rw [← htrans.2]
    change f Q ∈ I.map g
    rw [hspan, Ideal.mem_span_singleton]
    exact had.trans hdQ
  have hdiv : e a ∣ e Q := Ideal.mem_span_singleton.mp hQmem
  exact hcop a ha haP ((map_dvd_iff e).mp hdiv)
theorem rowMap_proper (s : Slice) (ht : PrimeTransport s) (P Q : Jet)
    (hp : ProperPair P Q) : PlaneProper (rowMap s P) (rowMap s Q) := by
  let : CommRing Equation := @AddMonoidAlgebra.commRing Seeds ℕ inferInstance _
  let : CommRing Jet := @AddMonoidAlgebra.commRing Equation ℕ inferInstance _
  let : UniqueFactorizationMonoid FX := PrincipalIdealRing.to_uniqueFactorizationMonoid
  let : UniqueFactorizationMonoid Ambient := MvPolynomial.uniqueFactorizationMonoid (Fin 4)
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid (Plane (SliceField s)) :=
    MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  obtain ⟨hP, hQ, hcop⟩ :=
    map_proper jetEquiv (planeMap s) ht P Q hp.left_ne hp.right_ne hp.no_common
  exact ⟨hP, hQ, hcop⟩
end
end K1_14_2_2_2_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace K1_14_2_2_2_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 Polynomial
open K1_14_3 (Slice)
open scoped BigOperators
private abbrev baseMap (s : Slice) :=
  (MvPolynomial.C : SliceField s →+* Plane (SliceField s)).comp (coefficients s)
private theorem eval_seed (s : Slice) (A : Seeds) :
    rowMap s (C (C A)) = MvPolynomial.eval₂Hom (baseMap s) (seedCoordinates s) A := by
  have h : (planeMap s).comp (rootIncl.comp rootSeeds) =
      MvPolynomial.eval₂Hom (baseMap s) (seedCoordinates s) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rootSeeds, rootIncl, planeMap, MvPolynomial.eval₂Hom_C]
    · intro i
      fin_cases i <;> simp [rootSeeds, rootIncl, planeMap, coordinates, MvPolynomial.eval₂Hom_X']
  change planeMap s (toJet (C (C A))) = _
  rw [toJet_seed]
  exact RingHom.congr_fun h A
private theorem eval_y (s : Slice) :
    rowMap s (C (Polynomial.X (R := Seeds))) = ordinateCoordinate s := by
  simp [rowMap, toJet_ordinate, planeMap, coordinates]
private theorem eval_v (s : Slice) :
    rowMap s (Polynomial.X (R := Equation)) = derivativeCoordinate s := by
  simp [rowMap, toJet_derivative, planeMap, coordinates]
private theorem sum_degree_le {F ι : Type} [Field F] (D : Plane F → ℕ)
    (h0 : D 0 = 0) (hadd : ∀ f g, D (f + g) ≤ max (D f) (D g))
    (T : Finset ι) (a : ι → Plane F) (N : ℕ) (h : ∀ i ∈ T, D (a i) ≤ N) :
    D (∑ i ∈ T, a i) ≤ N := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [h0]
  | @insert i T hi ih =>
    rw [Finset.sum_insert hi]
    exact (hadd _ _).trans (max_le (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))))
private theorem degree_bound (s : Slice) (P : Jet) (d : Shape) (h : RowCaps P d)
    (D : Plane (SliceField s) → ℕ) (h0 : D 0 = 0) (h1 : D 1 = 0)
    (hadd : ∀ f g, D (f + g) ≤ max (D f) (D g))
    (hmul : ∀ f g, D (f * g) ≤ D f + D g)
    (hpow : ∀ f n, D (f ^ n) ≤ n * D f)
    (hconst : ∀ a : SliceField s, D (MvPolynomial.C a) = 0)
    (u e j N : ℕ)
    (hu : ∀ i, D (seedCoordinates s i) ≤ u)
    (he : D (ordinateCoordinate s) ≤ e) (hj : D (derivativeCoordinate s) ≤ j)
    (hN : ∀ v y, y + v ≤ d.B → v ≤ d.J → d.U * u + y * e + v * j ≤ N) :
    D (rowMap s P) ≤ N := by
  classical
  have hseed (A : Seeds) : D (rowMap s (C (C A))) ≤ A.totalDegree * u := by
    rw [eval_seed]
    conv_lhs => rw [A.as_sum]
    rw [map_sum]
    apply sum_degree_le D h0 hadd
    intro m hm
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
    apply (hmul _ _).trans
    rw [show baseMap s (A.coeff m) =
      MvPolynomial.C (coefficients s (A.coeff m)) from rfl, hconst, zero_add]
    unfold Finsupp.prod
    refine (m.support.apply_prod_le_sum_apply D (by rw [h1]) hmul).trans ?_
    calc
      _ ≤ ∑ i ∈ m.support, m i * u :=
        Finset.sum_le_sum fun i _ => (hpow _ _).trans (Nat.mul_le_mul_left _ (hu i))
      _ = m.degree * u := by rw [← Finset.sum_mul, Finsupp.degree_apply]
      _ ≤ _ := Nat.mul_le_mul_right u (MvPolynomial.le_totalDegree hm)
  conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
  rw [map_sum]
  apply sum_degree_le D h0 hadd
  intro v hv
  rw [map_mul, map_pow, eval_v]
  refine (hmul _ _).trans ?_
  have hv' := (hpow (derivativeCoordinate s) v).trans (Nat.mul_le_mul_left v hj)
  have hc : D (rowMap s (C (P.coeff v))) ≤ N - v * j := by
    conv_lhs => rw [(P.coeff v).as_sum_support_C_mul_X_pow]
    rw [map_sum, map_sum]
    apply sum_degree_le D h0 hadd
    intro y hy
    rw [map_mul, map_mul, map_pow, map_pow, eval_y]
    have hrow := h v y (mem_support_iff.mp hy)
    have hs := (hseed ((P.coeff v).coeff y)).trans (Nat.mul_le_mul_right u hrow.2.2)
    have ht := (hpow (ordinateCoordinate s) y).trans (Nat.mul_le_mul_left y he)
    have hn := hN v y hrow.1 hrow.2.1
    exact (hmul _ _).trans (by omega)
  obtain ⟨y, hy⟩ := support_nonempty.mpr (mem_support_iff.mp hv)
  have hrow := h v y (mem_support_iff.mp hy)
  have hn := hN v y hrow.1 hrow.2.1
  omega
private theorem totalDegree_bound (s : Slice) (P : Jet) (d : Shape) (h : RowCaps P d)
    (u e j N : ℕ)
    (hu : ∀ i, (seedCoordinates s i).totalDegree ≤ u)
    (he : (ordinateCoordinate s).totalDegree ≤ e) (hj : (derivativeCoordinate s).totalDegree ≤ j)
    (hN : ∀ v y, y + v ≤ d.B → v ≤ d.J → d.U * u + y * e + v * j ≤ N) :
    (rowMap s P).totalDegree ≤ N :=
  degree_bound s P d h MvPolynomial.totalDegree MvPolynomial.totalDegree_zero
    MvPolynomial.totalDegree_one MvPolynomial.totalDegree_add MvPolynomial.totalDegree_mul
    MvPolynomial.totalDegree_pow MvPolynomial.totalDegree_C u e j N hu he hj hN
private theorem degreeOf_bound (i : Fin 2) (s : Slice) (P : Jet) (d : Shape) (h : RowCaps P d)
    (u e j N : ℕ)
    (hu : ∀ a, (seedCoordinates s a).degreeOf i ≤ u)
    (he : (ordinateCoordinate s).degreeOf i ≤ e) (hj : (derivativeCoordinate s).degreeOf i ≤ j)
    (hN : ∀ v y, y + v ≤ d.B → v ≤ d.J → d.U * u + y * e + v * j ≤ N) :
    (rowMap s P).degreeOf i ≤ N :=
  degree_bound s P d h (MvPolynomial.degreeOf i) (MvPolynomial.degreeOf_zero i)
    (MvPolynomial.degreeOf_one i) (MvPolynomial.degreeOf_add_le i) (MvPolynomial.degreeOf_mul_le i)
    (MvPolynomial.degreeOf_pow_le i) (fun a => MvPolynomial.degreeOf_C a i) u e j N hu he hj hN
private theorem seed_line_total :
    (MvPolynomial.C (sliceParameter 2) -
      MvPolynomial.C (sliceParameter 0) * MvPolynomial.X (0 : Fin 2)).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp)
    ((MvPolynomial.totalDegree_mul _ _).trans (by simp)))
private theorem ordinate_line_degree :
    (MvPolynomial.C (sliceParameter 3) -
      MvPolynomial.C (sliceParameter 1) * MvPolynomial.X (1 : Fin 2)).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp)
    ((MvPolynomial.totalDegree_mul _ _).trans (by simp)))
theorem rowMap_caps (s : Slice) (P : Jet) (d : Shape) (h : RowCaps P d) :
    PlaneCaps s d (rowMap s P) := by
  classical
  have seed_deg0 : ∀ i, (seedCoordinates .ordinate i).degreeOf 0 ≤ 1 := by
    rw [Fin.forall_fin_two]
    constructor
    · apply (MvPolynomial.degreeOf_le_totalDegree _ _).trans
      simpa only [seedCoordinates, Matrix.cons_val_zero] using seed_line_total
    · simp [seedCoordinates]
  have seed_deg1 : ∀ i, (seedCoordinates .ordinate i).degreeOf 1 ≤ 0 := by
    rw [Fin.forall_fin_two]
    constructor
    · change (MvPolynomial.C (sliceParameter 2) -
          MvPolynomial.C (sliceParameter 0) * MvPolynomial.X (0 : Fin 2)).degreeOf 1 ≤ 0
      apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
      apply max_le
      · simp
      · exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by simp [MvPolynomial.degreeOf_X])
    · simp [seedCoordinates, MvPolynomial.degreeOf_X]
  have ordinate_deg0 : (ordinateCoordinate .mixed).degreeOf 0 ≤ 0 := by
    change (MvPolynomial.C (sliceParameter 3) -
      MvPolynomial.C (sliceParameter 1) * MvPolynomial.X (1 : Fin 2)).degreeOf 0 ≤ 0
    apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
    apply max_le
    · simp
    · exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by simp [MvPolynomial.degreeOf_X])
  cases s
  · refine ⟨totalDegree_bound .seed P d h 0 1 1 d.B ?_ (by simp [ordinateCoordinate])
        (by simp [derivativeCoordinate]) (by intro v y hB hJ; omega),
      degreeOf_bound 1 .seed P d h 0 0 1 d.J ?_
        (by simp [ordinateCoordinate, MvPolynomial.degreeOf_X])
        (by simp [derivativeCoordinate]) (by intro v y hB hJ; omega)⟩
    all_goals intro i; fin_cases i <;> simp [seedCoordinates]
  · exact ⟨degreeOf_bound 0 .ordinate P d h 1 0 0 d.U seed_deg0
        (by simp [ordinateCoordinate]) (by simp [derivativeCoordinate, MvPolynomial.degreeOf_X])
        (by intro v y hB hJ; omega),
      degreeOf_bound 1 .ordinate P d h 0 0 1 d.J seed_deg1
        (by simp [ordinateCoordinate]) (by simp [derivativeCoordinate]) (by intro v y hB hJ; omega)⟩
  · exact ⟨degreeOf_bound 0 .mixed P d h 1 0 0 d.U seed_deg0 ordinate_deg0
        (by simp [derivativeCoordinate, MvPolynomial.degreeOf_X]) (by intro v y hB hJ; omega),
      degreeOf_bound 1 .mixed P d h 0 1 1 d.B seed_deg1
        ((MvPolynomial.degreeOf_le_totalDegree _ _).trans
          (by simpa only [ordinateCoordinate] using ordinate_line_degree))
        (by simp [derivativeCoordinate]) (by intro v y hB hJ; omega)⟩
  · exact totalDegree_bound .jets P d h 1 0 0 d.U (by simp [seedCoordinates])
      (by simp [ordinateCoordinate]) (by simp [derivativeCoordinate]) (by intro v y hB hJ; omega)
end
end K1_14_2_2_2_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_14_2_2_2_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2
section LinearCuts
variable {k : Type} [CommRing k]
private abbrev Four (F : Type) [CommSemiring F] := MvPolynomial (Fin 4) F
private def cutValues (a b u v : k) : Fin 4 → MvPolynomial (Fin 2) k :=
  ![MvPolynomial.C u - MvPolynomial.C a * MvPolynomial.X 0, MvPolynomial.X 0,
    MvPolynomial.C v - MvPolynomial.C b * MvPolynomial.X 1, MvPolynomial.X 1]
private def cutMap (a b u v : k) : Four k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval (cutValues a b u v)
private def seedEquation (a u : k) : Four k :=
  MvPolynomial.X (0 : Fin 4) + MvPolynomial.C a * MvPolynomial.X 1 - MvPolynomial.C u
private def jetEquation (b v : k) : Four k :=
  MvPolynomial.X (2 : Fin 4) + MvPolynomial.C b * MvPolynomial.X 3 - MvPolynomial.C v
private def lineIdeal (a b u v : k) : Ideal (Four k) :=
  Ideal.span {seedEquation a u, jetEquation b v}
private theorem cut_surjective (a b u v : k) : Function.Surjective (cutMap a b u v) := by
  let restore : MvPolynomial (Fin 2) k →ₐ[k] Four k := MvPolynomial.aeval ![MvPolynomial.X 1, MvPolynomial.X 3]
  have h : (cutMap a b u v).comp restore = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [cutMap, cutValues, restore]
  intro f
  exact ⟨restore f, AlgHom.congr_fun h f⟩
private theorem cut_ker (a b u v : k) :
    RingHom.ker (cutMap a b u v).toRingHom = lineIdeal a b u v := by
  let q := Ideal.Quotient.mkₐ k (lineIdeal a b u v)
  let restore : MvPolynomial (Fin 2) k →ₐ[k] (Four k ⧸ lineIdeal a b u v) :=
    MvPolynomial.aeval ![q (MvPolynomial.X 1), q (MvPolynomial.X 3)]
  have hs : q (seedEquation a u) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
  have hj : q (jetEquation b v) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have h : restore.comp (cutMap a b u v) = q := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, cutMap, MvPolynomial.aeval_X]
    fin_cases i
    · rw [show cutValues a b u v (⟨0, by decide⟩ : Fin 4) =
        MvPolynomial.C u - MvPolynomial.C a * MvPolynomial.X 0 from rfl]
      simp only [map_sub, map_mul, restore, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        Matrix.cons_val_zero]
      apply sub_eq_iff_eq_add.mpr
      symm
      apply sub_eq_zero.mp
      change q (MvPolynomial.X (0 : Fin 4)) + _ - _ = 0
      simpa only [seedEquation, map_sub, map_add, map_mul, ← MvPolynomial.algebraMap_eq,
        AlgHom.commutes] using hs
    · rw [show cutValues a b u v (⟨1, by decide⟩ : Fin 4) = MvPolynomial.X 0 from rfl]
      simp [restore]
    · rw [show cutValues a b u v (⟨2, by decide⟩ : Fin 4) =
        MvPolynomial.C v - MvPolynomial.C b * MvPolynomial.X 1 from rfl]
      simp only [map_sub, map_mul, restore, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        Matrix.cons_val_one, Matrix.cons_val_zero]
      apply sub_eq_iff_eq_add.mpr
      symm
      apply sub_eq_zero.mp
      change q (MvPolynomial.X (2 : Fin 4)) + _ - _ = 0
      simpa only [jetEquation, map_sub, map_add, map_mul, ← MvPolynomial.algebraMap_eq,
        AlgHom.commutes] using hj
    · rw [show cutValues a b u v (⟨3, by decide⟩ : Fin 4) = MvPolynomial.X 1 from rfl]
      simp [restore]
  apply le_antisymm
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hx' := AlgHom.congr_fun h x
    have hx0 : cutMap a b u v x = 0 := RingHom.mem_ker.mp hx
    rw [AlgHom.comp_apply, hx0, map_zero] at hx'
    exact hx'.symm
  · apply Ideal.span_le.mpr
    intro x hx
    apply RingHom.mem_ker.mpr
    rcases (Set.mem_insert_iff.mp hx) with rfl | hx
    · simp [cutMap, cutValues, seedEquation, ← MvPolynomial.algebraMap_eq]
    · obtain rfl := Set.mem_singleton_iff.mp hx
      simp [cutMap, cutValues, jetEquation, ← MvPolynomial.algebraMap_eq]
private def cutEquiv {F : Type} [CommRing F] (g : F →+* k)
    (I : Ideal (MvPolynomial (Fin 4) F)) (a b u v : k) :
    (Four k ⧸ (I.map (MvPolynomial.map g) ⊔ lineIdeal a b u v)) ≃ₐ[k]
      (MvPolynomial (Fin 2) k ⧸ I.map ((cutMap a b u v).toRingHom.comp (MvPolynomial.map g))) := by
  let cut := cutMap a b u v
  let J := I.map (cut.toRingHom.comp (MvPolynomial.map g))
  have h : I.map (MvPolynomial.map g) ⊔ lineIdeal a b u v = J.comap cut.toRingHom := by
    unfold J
    rw [← Ideal.map_map, Ideal.comap_map_of_surjective cut.toRingHom (cut_surjective a b u v)]
    exact congrArg (I.map (MvPolynomial.map g) ⊔ ·) (cut_ker a b u v).symm
  let f := Ideal.quotientMapₐ J cut h.le
  exact AlgEquiv.ofBijective f
    ⟨Ideal.quotientMap_injective' (H := h.le) h.ge,
      Ideal.quotientMap_surjective (H := h.le) (cut_surjective a b u v)⟩
private theorem cut_on_map {F : Type} [CommRing F] (g : F →+* k) (a b u v : k) :
    (cutMap a b u v).toRingHom.comp (MvPolynomial.map g) =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp g) (cutValues a b u v) := by
  apply RingHom.ext
  intro p
  change MvPolynomial.aeval (cutValues a b u v) (MvPolynomial.map g p) = _
  rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.eval₂Hom_map_hom, MvPolynomial.algebraMap_eq]
end LinearCuts
def ordinateEquiv (I : Ideal Ambient) :
    OverOrdinate I ≃ₐ[SectionField] (Plane SectionField ⧸ I.map (planeMap .ordinate)) := by
  have hcoords : cutValues (sliceParameter 0) (0 : SectionField)
      (sliceParameter 2) (sliceParameter 3) = coordinates .ordinate := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · change MvPolynomial.C (sliceParameter 3) -
        MvPolynomial.C (0 : SectionField) * MvPolynomial.X (1 : Fin 2) =
          MvPolynomial.C (sliceParameter 3)
      simp
    · rfl
  have hmap : (cutMap (sliceParameter 0) 0 (sliceParameter 2) (sliceParameter 3)).toRingHom.comp
      (MvPolynomial.map (algebraMap FX SectionField)) = planeMap .ordinate := by
    rw [cut_on_map, hcoords]
    rfl
  rw [← hmap]
  have hline : jetEquation (0 : SectionField) (sliceParameter 3) =
      MvPolynomial.X (2 : Fin 4) - MvPolynomial.C (sliceParameter 3) := by
    simp [jetEquation, MvPolynomial.C_0]
  have hsrc : I.map sectionBase ⊔ Ideal.span
      {sectionSeedLine, MvPolynomial.X 2 - MvPolynomial.C (sliceParameter 3)} =
      I.map (MvPolynomial.map (algebraMap FX SectionField)) ⊔
        lineIdeal (sliceParameter 0) 0 (sliceParameter 2) (sliceParameter 3) := by
    unfold lineIdeal
    rw [hline]
    rfl
  exact (Ideal.quotientEquivAlgOfEq SectionField hsrc).trans
    (cutEquiv (algebraMap FX SectionField) I (sliceParameter 0) 0 (sliceParameter 2)
      (sliceParameter 3))
def mixedEquiv (I : Ideal Ambient) :
    OverMixed I ≃ₐ[SectionField] (Plane SectionField ⧸ I.map (planeMap .mixed)) := by
  have hcoords : cutValues (sliceParameter 0) (sliceParameter 1)
      (sliceParameter 2) (sliceParameter 3) = coordinates .mixed := by
    funext i
    fin_cases i <;> rfl
  have hmap : (cutMap (sliceParameter 0) (sliceParameter 1) (sliceParameter 2)
      (sliceParameter 3)).toRingHom.comp (MvPolynomial.map (algebraMap FX SectionField)) =
      planeMap .mixed := by
    rw [cut_on_map, hcoords]
    rfl
  rw [← hmap]
  exact cutEquiv (algebraMap FX SectionField) I (sliceParameter 0) (sliceParameter 1)
    (sliceParameter 2) (sliceParameter 3)
end
end K1_14_2_2_2_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_14_2_2_2_4
noncomputable section
open K1_14 K1_14_2 K1_14_2_2_2
open K1_14_3 (Slice)
open scoped BigOperators
private theorem sum_quotient_le {k R ι : Type} [Field k] [CommRing R] [Algebra k R]
    (L : Ideal R) (J : ι → Ideal R) (qs : Finset ι) [Module.Finite k (R ⧸ L)]
    (hcont : ∀ q ∈ qs, L ≤ J q)
    (hprime : ∀ q ∈ qs, J q = ⊤ ∨ (J q).IsPrime)
    (hdisjoint : ∀ q ∈ qs, ∀ r ∈ qs, J q ≠ ⊤ → J r ≠ ⊤ → J q = J r → q = r) :
    (∑ q ∈ qs, Module.finrank k (R ⧸ J q)) ≤ Module.finrank k (R ⧸ L) := by
  classical
  let T := qs.filter fun q => J q ≠ ⊤
  let J' : T → Ideal R := fun q => J q
  have hT (q : T) : (q : ι) ∈ qs := (Finset.mem_filter.mp q.property).1
  have hne (q : T) : J q ≠ ⊤ := (Finset.mem_filter.mp q.property).2
  have hle (q : T) : L ≤ J q := hcont q (hT q)
  let (q : T) : Module.Finite k (R ⧸ J' q) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ k (hle q)).toLinearMap
      (Ideal.Quotient.factor_surjective (hle q))
  have hJM (q : T) : (J q).IsMaximal := by
    let : (J' q).IsPrime := (hprime q (hT q)).resolve_left (hne q)
    let : IsArtinianRing (R ⧸ J' q) := IsArtinianRing.of_finite k _
    exact Ideal.Quotient.maximal_of_isField (J' q) (IsArtinianRing.isField_of_isDomain _)
  have hcop : Pairwise fun q r => IsCoprime (J' q) (J' r) := by
    intro q r hqr
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply (hJM q).coprime_of_ne
    · exact hJM r
    · exact fun h => hqr (Subtype.ext (hdisjoint q (hT q) r (hT r) (hne q) (hne r) h))
  let f : R ⧸ L →ₗ[k] ∀ q : T, R ⧸ J' q :=
    LinearMap.pi fun q => (Ideal.Quotient.factorₐ k (hle q)).toLinearMap
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨y, hy⟩ := Ideal.quotientInfToPiQuotient_surj hcop x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨Ideal.Quotient.mk L a, ?_⟩
    funext q
    exact congrFun hy q
  have hd := LinearMap.finrank_le_finrank_of_surjective hsurj
  rw [Module.finrank_pi_fintype] at hd
  change (∑ q : T, Module.finrank k (R ⧸ J q)) ≤ _ at hd
  rw [Finset.sum_coe_sort T (fun q => Module.finrank k (R ⧸ J q))] at hd
  change (∑ q ∈ qs.filter (fun q => J q ≠ ⊤), Module.finrank k (R ⧸ J q)) ≤ _ at hd
  rw [Finset.sum_filter] at hd
  convert hd using 1
  symm
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : J q = ⊤
  · let : Subsingleton (R ⧸ J q) := Ideal.Quotient.subsingleton_iff.mpr h
    have hzero : Module.finrank k (R ⧸ J q) = 0 := Module.finrank_eq_zero_of_subsingleton k _
    simp only [hzero, ite_self]
  · simp [h]
abbrev ComponentQuotient (s : Slice) (I : Ideal Ambient) :=
  Plane (SliceField s) ⧸ I.map (planeMap s)
abbrev ComponentFinite (s : Slice) (I : Ideal Ambient) :=
  Module.Finite (SliceField s) (ComponentQuotient s I)
def componentLength (s : Slice) (I : Ideal Ambient) : ℕ :=
  Module.finrank (SliceField s) (ComponentQuotient s I)
theorem plane_lengths (s : Slice) (P Q : Jet) (S : Finset (Ideal Ambient))
    (hS : ComponentsOn P Q S) (ht : PrimeTransport s) (n : ℕ)
    (hB : ColengthAtMost (rowMap s P) (rowMap s Q) n) :
    (∀ I ∈ S, ComponentFinite s I) ∧ (∑ I ∈ S, componentLength s I) ≤ n := by
  let L := Ideal.span ({rowMap s P, rowMap s Q} : Set (Plane (SliceField s)))
  let J (I : Ideal Ambient) := I.map (planeMap s)
  let : Module.Finite (SliceField s) (Plane (SliceField s) ⧸ L) := hB.1
  have hcont (I : Ideal Ambient) (hi : I ∈ S) : L ≤ J I := by
    change Ideal.span ({rowMap s P, rowMap s Q} : Set (Plane (SliceField s))) ≤ J I
    rw [Ideal.span_insert, sup_le_iff]
    exact ⟨(Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ (hS I hi).2.2.1),
      (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ (hS I hi).2.2.2)⟩
  refine ⟨fun I hi => Module.Finite.of_surjective
    (Ideal.Quotient.factorₐ (SliceField s) (hcont I hi)).toLinearMap
    (Ideal.Quotient.factor_surjective (hcont I hi)), ?_⟩
  refine (sum_quotient_le L J S hcont (fun I hi => (ht I (hS I hi).1).imp_right And.left) ?_)
    |>.trans hB.2
  intro I hi I' hi' hn hn' heq
  rw [← ((ht I (hS I hi).1).resolve_left hn).2,
    ← ((ht I' (hS I' hi').1).resolve_left hn').2, show I.map (planeMap s) = I'.map (planeMap s) from heq]
end
end K1_14_2_2_2_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_2_4
noncomputable section
open K1 K1_14 K1_14_2
theorem seed_planeMap : planeMap .seed = mapGenericSeed := rfl
theorem jets_planeMap : planeMap .jets = mapGenericJets := rfl
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev Iterated := MvPolynomial (Fin 2) Seeds
private def chart (e : Fin 4 ≃ Fin 2 ⊕ Fin 2) : Ambient ≃+* Iterated :=
  ((MvPolynomial.renameEquiv FX e).trans
    (MvPolynomial.sumAlgEquiv FX (Fin 2) (Fin 2))).toRingEquiv
private theorem chart_map (e : Fin 4 ≃ Fin 2 ⊕ Fin 2) :
    (algebraMap Iterated FibreRing).comp (chart e).toRingHom =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap FX SeedField))
        (Sum.elim MvPolynomial.X (fun i => MvPolynomial.C (generic i)) ∘ e) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [chart]
    rfl
  · intro i
    rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', Function.comp_apply]
    change algebraMap Iterated FibreRing
      (MvPolynomial.sumAlgEquiv FX (Fin 2) (Fin 2)
        (MvPolynomial.renameEquiv FX e (MvPolynomial.X i))) = _
    rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, MvPolynomial.algebraMap_def]
    cases e i <;> simp [generic]
private theorem localize_plane (e : Fin 4 ≃ Fin 2 ⊕ Fin 2)
    (I : Ideal Ambient) (hI : I.IsPrime) :
    let f := (algebraMap Iterated FibreRing).comp (chart e).toRingHom
    I.map f = ⊤ ∨ (I.map f).IsPrime ∧ (I.map f).comap f = I := by
  dsimp only
  let S : Submonoid Iterated := (nonZeroDivisors Seeds).map MvPolynomial.C
  let J := I.map (chart e).toRingHom
  rw [← Ideal.map_map]
  by_cases ht : J.map (algebraMap Iterated FibreRing) = ⊤
  · exact Or.inl ht
  have hJ : J.IsPrime := by
    change (I.map (chart e : Ambient →+* Iterated)).IsPrime
    rw [Ideal.map_comap_of_equiv (chart e)]
    exact hI.comap _
  have hd := (IsLocalization.map_algebraMap_ne_top_iff_disjoint S FibreRing J).mp ht
  refine Or.inr ⟨IsLocalization.isPrime_of_isPrime_disjoint S FibreRing J hJ hd, ?_⟩
  rw [← Ideal.comap_comap]
  have hcontract : (J.map (algebraMap Iterated FibreRing)).comap (algebraMap Iterated FibreRing) = J :=
    IsLocalization.under_map_of_isPrime_disjoint S FibreRing hJ hd
  change ((J.map (algebraMap Iterated FibreRing)).comap (algebraMap Iterated FibreRing)).comap
    (chart e).toRingHom = I
  rw [hcontract]
  exact Ideal.comap_map_of_bijective _ (chart e).bijective
theorem seed_transport : PrimeTransport .seed := by
  intro I hI
  rw [seed_planeMap]
  let e : Fin 4 ≃ Fin 2 ⊕ Fin 2 := (finSumFinEquiv (m := 2) (n := 2)).symm.trans (Equiv.sumComm (Fin 2) (Fin 2))
  have h : (algebraMap Iterated FibreRing).comp (chart e).toRingHom = mapGenericSeed := by
    rw [chart_map]
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [mapGenericSeed]
    · intro i
      simp only [mapGenericSeed, MvPolynomial.eval₂Hom_X', Function.comp_apply]
      fin_cases i <;> rfl
  exact h ▸ localize_plane e I hI
theorem jets_transport : PrimeTransport .jets := by
  intro I hI
  rw [jets_planeMap]
  let e : Fin 4 ≃ Fin 2 ⊕ Fin 2 := (finSumFinEquiv (m := 2) (n := 2)).symm
  have h : (algebraMap Iterated FibreRing).comp (chart e).toRingHom = mapGenericJets := by
    rw [chart_map]
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [mapGenericJets]
    · intro i
      simp only [mapGenericJets, MvPolynomial.eval₂Hom_X', Function.comp_apply]
      fin_cases i <;> rfl
  exact h ▸ localize_plane e I hI
end
end K1_14_2_2_2_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_14_2_2_2_4
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2
open K1_14_3 (Slice)
open scoped BigOperators
def c1 : Prop := PrimeTransport .ordinate ∧ PrimeTransport .mixed
def c2 : Prop :=
  ∀ (F : Type) [Field F] (P Q : Plane F) (b j c k : ℕ),
    j ≤ b → k ≤ c → PlaneProper P Q →
    P.totalDegree ≤ b → P.degreeOf 1 ≤ j → Q.totalDegree ≤ c → Q.degreeOf 1 ≤ k →
    ColengthAtMost P Q (b*k + c*j - j*k)
def c3 : Prop :=
  ∀ (F : Type) [Field F] (P Q : Plane F) (u j v k : ℕ),
    PlaneProper P Q →
    P.degreeOf 0 ≤ u → P.degreeOf 1 ≤ j → Q.degreeOf 0 ≤ v → Q.degreeOf 1 ≤ k →
    ColengthAtMost P Q (u*k + v*j)
private theorem quotient_properties {F : Type} [CommRing F]
    (I : Ideal (MvPolynomial (Fin 4) F)) (J : Ideal (MvPolynomial (Fin 2) F))
    (e : (MvPolynomial (Fin 4) F ⧸ I) ≃ₐ[F] (MvPolynomial (Fin 2) F ⧸ J)) :
    (Module.Finite F (MvPolynomial (Fin 2) F ⧸ J) →
      Module.Finite F (MvPolynomial (Fin 4) F ⧸ I)) ∧
    Module.finrank F (MvPolynomial (Fin 4) F ⧸ I) =
      Module.finrank F (MvPolynomial (Fin 2) F ⧸ J) := by
  refine ⟨?_, e.toLinearEquiv.finrank_eq⟩
  intro h
  let : Module.Finite F (MvPolynomial (Fin 2) F ⧸ J) := h
  exact Module.Finite.of_surjective e.symm.toLinearEquiv.toLinearMap e.symm.surjective
private theorem seed_rank (I : Ideal Ambient) :
    Module.finrank SeedField (OverSeeds I) = componentLength .seed I := rfl
private theorem ordinate_rank (I : Ideal Ambient) :
    Module.finrank SectionField (OverOrdinate I) = componentLength .ordinate I := by
  have h := (quotient_properties (F := SectionField) _ _ (ordinateEquiv I)).2
  exact h
private theorem mixed_rank (I : Ideal Ambient) :
    Module.finrank SectionField (OverMixed I) = componentLength .mixed I := by
  have h := (quotient_properties (F := SectionField) _ _ (mixedEquiv I)).2
  exact h
private theorem jets_rank (I : Ideal Ambient) :
    Module.finrank SeedField (OverJets I) = componentLength .jets I := rfl
private theorem ordinate_finite (I : Ideal Ambient) (h : ComponentFinite .ordinate I) :
    Module.Finite SectionField (OverOrdinate I) := by
  have hf := (quotient_properties (F := SectionField) _ _ (ordinateEquiv I)).1
  exact hf h
private theorem mixed_finite (I : Ideal Ambient) (h : ComponentFinite .mixed I) :
    Module.Finite SectionField (OverMixed I) := by
  have hf := (quotient_properties (F := SectionField) _ _ (mixedEquiv I)).1
  exact hf h
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_14_2_2_2.c4 := by
  intro P Q hp s t hs ht hP hQ S hS
  have hcap (k : Slice) (R : Jet) (d : Shape) (hR : RowCaps R d) := rowMap_caps k R d hR
  have hseed := plane_lengths .seed P Q S hS seed_transport _
    (h2 (SliceField .seed) _ _ s.B s.J t.B t.J hs ht (rowMap_proper .seed seed_transport P Q hp)
      (hcap .seed P s hP).1 (hcap .seed P s hP).2
      (hcap .seed Q t hQ).1 (hcap .seed Q t hQ).2)
  have hord := plane_lengths .ordinate P Q S hS h1.1 _
    (h3 (SliceField .ordinate) _ _ s.U s.J t.U t.J (rowMap_proper .ordinate h1.1 P Q hp)
      (hcap .ordinate P s hP).1 (hcap .ordinate P s hP).2
      (hcap .ordinate Q t hQ).1 (hcap .ordinate Q t hQ).2)
  have hmix := plane_lengths .mixed P Q S hS h1.2 _
    (h3 (SliceField .mixed) _ _ s.U s.B t.U t.B (rowMap_proper .mixed h1.2 P Q hp)
      (hcap .mixed P s hP).1 (hcap .mixed P s hP).2
      (hcap .mixed Q t hQ).1 (hcap .mixed Q t hQ).2)
  have hjcap (R : Jet) (d : Shape) (hR : RowCaps R d) :
      (rowMap .jets R).totalDegree ≤ d.U := hcap .jets R d hR
  have hj : ColengthAtMost (rowMap .jets P) (rowMap .jets Q) (s.U * t.U) := by
    have h := h2 (SliceField .jets) _ _ s.U s.U t.U t.U le_rfl le_rfl (rowMap_proper .jets jets_transport P Q hp)
      (hjcap P s hP) ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (hjcap P s hP))
      (hjcap Q t hQ) ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (hjcap Q t hQ))
    rw [Nat.mul_comm t.U s.U, Nat.add_sub_cancel] at h
    exact h
  have hjets := plane_lengths .jets P Q S hS jets_transport _ hj
  constructor
  · intro I hI
    exact ⟨hseed.1 I hI, ordinate_finite I (hord.1 I hI), mixed_finite I (hmix.1 I hI),
      hjets.1 I hI⟩
  intro i
  fin_cases i
  · change (∑ I ∈ S, Module.finrank SeedField (OverSeeds I)) ≤ s.B*t.J + t.B*s.J - s.J*t.J
    simpa only [seed_rank] using hseed.2
  · change (∑ I ∈ S, Module.finrank SectionField (OverOrdinate I)) ≤ s.U*t.J + t.U*s.J
    simpa only [ordinate_rank] using hord.2
  · change (∑ I ∈ S, Module.finrank SectionField (OverMixed I)) ≤ s.U*t.B + t.U*s.B
    simpa only [mixed_rank] using hmix.2
  · change (∑ I ∈ S, Module.finrank SeedField (OverJets I)) ≤ s.U*t.U
    simpa only [jets_rank] using hjets.2
end
end K1_14_2_2_2_4
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_2_4_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2_4 MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev Indices := Fin 2 ⊕ Fin 4
private abbrev Coefficients := MvPolynomial (Fin 4) FX
private abbrev Extended := MvPolynomial (Fin 2) Ambient
private abbrev Flat := MvPolynomial Indices FX
private abbrev Target := Plane SectionField
private abbrev nest : Flat ≃ₐ[FX] Extended := sumAlgEquiv FX (Fin 2) (Fin 4)
private def shifted (op : Flat → Flat → Flat) (a b : FX) : Fin 4 → Flat :=
  ![op (MvPolynomial.X (.inr 0)) (C a * MvPolynomial.X (.inl 0) * MvPolynomial.X (.inr 1)),
    MvPolynomial.X (.inr 1),
    op (MvPolynomial.X (.inr 2)) (C b * MvPolynomial.X (.inl 1) * MvPolynomial.X (.inr 3)),
    MvPolynomial.X (.inr 3)]
private def shearMap (op : Flat → Flat → Flat) (a b : FX) : Flat →ₐ[FX] Flat :=
  aeval (Sum.elim (fun i => MvPolynomial.X (.inl i)) (shifted op a b))
private def shear (a b : FX) : Flat ≃ₐ[FX] Flat := by
  refine AlgEquiv.ofAlgHom (shearMap (· - ·) a b) (shearMap (· + ·) a b) ?_ ?_
  · apply algHom_ext
    rintro (i | i)
    · simp [shearMap]
    · fin_cases i <;> simp [shearMap, shifted, algebraMap_eq]
  · apply algHom_ext
    rintro (i | i)
    · simp [shearMap]
    · fin_cases i <;> simp [shearMap, shifted, algebraMap_eq]
private def indices : Indices ≃ Indices where
  toFun := Sum.elim ![Sum.inr 0, Sum.inr 1] ![Sum.inr 2, Sum.inl 0, Sum.inr 3, Sum.inl 1]
  invFun := Sum.elim ![Sum.inr 1, Sum.inr 3] ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 2]
  left_inv := by rintro (i | i) <;> fin_cases i <;> rfl
  right_inv := by rintro (i | i) <;> fin_cases i <;> rfl
private def regroup : Flat ≃ₐ[FX] Extended :=
  (renameEquiv FX indices).trans nest
private def chart (b : FX) : Extended ≃+* Extended :=
  ((nest.symm.trans (shear 1 b)).trans regroup).toRingEquiv
private def finish : Flat →+* Target :=
  (algebraMap Extended Target).comp regroup.toRingEquiv.toRingHom
private theorem finish_X (i : Indices) :
    finish (MvPolynomial.X i) = Sum.elim MvPolynomial.X (fun j => C (sliceParameter j)) (indices i) := by
  change algebraMap Extended Target (nest (renameEquiv FX indices (MvPolynomial.X i))) = _
  rw [renameEquiv_apply, rename_X, MvPolynomial.algebraMap_def]
  cases indices i <;> simp [sliceParameter]
private theorem finish_C (c : FX) : finish (C c) = C (algebraMap FX SectionField c) := by
  change algebraMap Extended Target (nest (renameEquiv FX indices (C c))) = _
  rw [renameEquiv_apply, rename_C, sumAlgEquiv_C_inl, MvPolynomial.algebraMap_def, map_C]
  rfl
private def lineMap (b : FX) : Ambient →+* Target :=
  ((algebraMap Extended Target).comp (chart b).toRingHom).comp C
private theorem lineMap_eval (b : FX) :
    lineMap b = eval₂Hom (C.comp (algebraMap FX SectionField))
      (![C (sliceParameter 2) - C (sliceParameter 0) * MvPolynomial.X 0, MvPolynomial.X 0,
         C (sliceParameter 3) - C (algebraMap FX SectionField b) * C (sliceParameter 1) * MvPolynomial.X 1,
         MvPolynomial.X 1] : Fin 4 → Target) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change finish (shear 1 b (nest.symm (C (C c)))) = _
    rw [sumAlgEquiv_symm_C_C]
    change finish (shearMap (· - ·) 1 b (C c)) = _
    rw [show shearMap (· - ·) 1 b (C c) = C c by simp [algebraMap_eq]]
    rw [finish_C, eval₂Hom_C, RingHom.comp_apply]
  · intro i
    change finish (shear 1 b (nest.symm (C (MvPolynomial.X i)))) = _
    rw [sumAlgEquiv_symm_C_X]
    change finish (shearMap (· - ·) 1 b (MvPolynomial.X (.inr i))) = _
    rw [shearMap, aeval_X, Sum.elim_inr, eval₂Hom_X']
    fin_cases i <;> simp [shifted, finish_X, finish_C, indices]
private theorem ordinate_lineMap : lineMap 0 = planeMap .ordinate := by
  change lineMap 0 = eval₂Hom (C.comp (algebraMap FX SectionField))
    (coordinates .ordinate : Fin 4 → Target)
  rw [lineMap_eval]
  apply congrArg (eval₂Hom (C.comp (algebraMap FX SectionField)))
  funext i
  fin_cases i <;> simp [coordinates, seedCoordinates, ordinateCoordinate, derivativeCoordinate] <;> rfl
private theorem mixed_lineMap : lineMap 1 = planeMap .mixed := by
  change lineMap 1 = eval₂Hom (C.comp (algebraMap FX SectionField))
    (coordinates .mixed : Fin 4 → Target)
  rw [lineMap_eval]
  apply congrArg (eval₂Hom (C.comp (algebraMap FX SectionField)))
  funext i
  fin_cases i <;> simp [coordinates, seedCoordinates, ordinateCoordinate, derivativeCoordinate]
private theorem polynomial_prime {R σ : Type} [CommRing R] (I : Ideal R) (hI : I.IsPrime) :
    (I.map (C : R →+* MvPolynomial σ R)).IsPrime := by
  let : I.IsPrime := hI
  let q : MvPolynomial σ R →+* MvPolynomial σ (R ⧸ I) :=
    MvPolynomial.map (Ideal.Quotient.mk I)
  have hq : RingHom.ker q = I.map C := by
    dsimp only [q]
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
  rw [← hq]
  exact RingHom.ker_isPrime q
private theorem line_transport (b : FX) (I : Ideal Ambient) (hI : I.IsPrime) :
    I.map (lineMap b) = ⊤ ∨
      (I.map (lineMap b)).IsPrime ∧ (I.map (lineMap b)).comap (lineMap b) = I := by
  let C₀ : Ambient →+* Extended := C
  let e := chart b
  let L := algebraMap Extended Target
  let E := I.map C₀
  let J := E.map e.toRingHom
  let S : Submonoid Extended := (nonZeroDivisors Coefficients).map C
  have hE : E.IsPrime := polynomial_prime I hI
  have hEback : E.comap C₀ = I := by
    ext p
    constructor
    · intro hp
      change C p ∈ I.map C₀ at hp
      simpa using (MvPolynomial.mem_map_C_iff.mp hp 0)
    · exact Ideal.mem_map_of_mem C₀
  have hJ : J.IsPrime := by
    change (E.map (e : Extended →+* Extended)).IsPrime
    rw [Ideal.map_comap_of_equiv e]
    exact hE.comap _
  have hmap : I.map (lineMap b) = J.map L := by
    change I.map ((L.comp e.toRingHom).comp C₀) = _
    rw [← Ideal.map_map, ← Ideal.map_map]
  rw [hmap]
  by_cases ht : J.map L = ⊤
  · exact Or.inl ht
  have hd := (IsLocalization.map_algebraMap_ne_top_iff_disjoint S Target J).mp ht
  refine Or.inr ⟨IsLocalization.isPrime_of_isPrime_disjoint S Target J hJ hd, ?_⟩
  have hback : (J.map L).comap L = J :=
    IsLocalization.under_map_of_isPrime_disjoint S Target hJ hd
  change (J.map L).comap ((L.comp e.toRingHom).comp C₀) = I
  rw [← Ideal.comap_comap, ← Ideal.comap_comap, hback]
  have heback : J.comap e.toRingHom = E := Ideal.comap_map_of_bijective _ e.bijective
  rw [heback, hEback]
theorem proof : K1_14_2_2_2_4.c1 := by
  constructor
  · intro I hI
    rw [← ordinate_lineMap]
    exact line_transport 0 I hI
  · intro I hI
    rw [← mixed_lineMap]
    exact line_transport 1 I hI
end
end K1_14_2_2_2_4_1
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_2_3
noncomputable section
open K1_14 K1_14_2 K1_14_3_2
open scoped BigOperators
private def lastEquiv (F : Type*) [CommRing F] (n : ℕ) :
    Polynomial (MvPolynomial (Fin n) F) ≃+* MvPolynomial (Fin (n + 1)) F :=
  (MvPolynomial.optionEquivLeft F (Fin n)).symm.toRingEquiv.trans
    (MvPolynomial.renameEquiv F (finSuccEquivLast (n := n)).symm).toRingEquiv
private theorem lastEquiv_X (F : Type*) [CommRing F] (n : ℕ) :
    lastEquiv F n Polynomial.X = MvPolynomial.X (Fin.last n) := by
  change MvPolynomial.rename _ ((MvPolynomial.optionEquivLeft F (Fin n)).symm Polynomial.X) = _
  simp
private theorem lastEquiv_C (F : Type*) [CommRing F] (n : ℕ)
    (a : MvPolynomial (Fin n) F) :
    lastEquiv F n (Polynomial.C a) = MvPolynomial.rename Fin.castSucc a := by
  have h : (MvPolynomial.optionEquivLeft F (Fin n)).symm (Polynomial.C a) =
      MvPolynomial.rename some a := by
    change (Polynomial.aevalTower (MvPolynomial.rename some) (MvPolynomial.X none))
      (Polynomial.C a) = _
    simp
  change MvPolynomial.rename _
    ((MvPolynomial.optionEquivLeft F (Fin n)).symm (Polynomial.C a)) = _
  have he : (finSuccEquivLast (n := n)).symm ∘ some = Fin.castSucc := by
    funext i
    simp
  rw [h, MvPolynomial.rename_rename, he]
private theorem castLE_succ (n : ℕ) :
    (Fin.castLE (Nat.le_succ n) : Fin n → Fin (n + 1)) = Fin.castSucc := by
  funext i
  apply Fin.ext
  rfl
def jetEquiv : Jet ≃+* Ambient :=
  (Polynomial.mapEquiv (lastEquiv FX 2)).trans (lastEquiv FX 3)
theorem jetEquiv_apply (P : Jet) : jetEquiv P = toJet P := by
  have hroot : (lastEquiv FX 2).toRingHom = toRoot := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa [toRoot, rootSeeds, castLE_succ] using lastEquiv_C FX 2 a
    · simpa [toRoot, Polynomial.coe_eval₂RingHom] using lastEquiv_X FX 2
  have hjet : jetEquiv.toRingHom = toJet := by
    apply Polynomial.ringHom_ext
    · intro a
      change lastEquiv FX 3 ((Polynomial.C a).map (lastEquiv FX 2).toRingHom) =
        toJet (Polynomial.C a)
      rw [Polynomial.map_C, lastEquiv_C, hroot]
      simp [toJet, rootIncl, castLE_succ]
    · change lastEquiv FX 3 (Polynomial.X.map (lastEquiv FX 2).toRingHom) =
        toJet Polynomial.X
      rw [Polynomial.map_X, lastEquiv_X]
      simp [toJet]
  exact RingHom.congr_fun hjet P
private theorem maximal_height (F : Type*) [Field F] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) F)) [m.IsMaximal] : m.height = n := by
  induction n with
  | zero =>
    have hd : ringKrullDim (MvPolynomial (Fin 0) F) = 0 := by
      rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.isEmptyRingEquiv F (Fin 0)),
        ringKrullDim_eq_zero_of_field]
    have h := Ideal.height_le_ringKrullDim_of_isPrime (I := m)
    rw [hd] at h
    exact le_antisymm (by exact_mod_cast h) (by simp)
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv F n).toRingEquiv
    let M := m.map e
    have : M.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let p := M.comap (Polynomial.C : MvPolynomial (Fin n) F →+* _)
    have : p.IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing M
    have : M.LiesOver p := ⟨rfl⟩
    rw [← e.height_map m, Polynomial.height_eq_height_add_one p M, ih p]
    simp
private theorem isolating_maximal {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsJacobsonRing R] {J I : Ideal R} (hI : I ∈ J.minimalPrimes) :
    ∃ m : Ideal R, m.IsMaximal ∧ I ≤ m ∧
      ∀ q ∈ J.minimalPrimes, q ≤ m → q = I := by
  classical
  let fmin := J.finite_minimalPrimes_of_isNoetherianRing
  let s := fmin.toFinset.erase I
  have hs (q : s) : ∃ x : R, x ∈ q.val ∧ x ∉ I := by
    obtain ⟨hne, hq⟩ := Finset.mem_erase.mp q.property
    have hmin : q.val ∈ J.minimalPrimes := fmin.mem_toFinset.mp hq
    by_contra! h
    exact hne (le_antisymm h (hI.2 hmin.1 h))
  choose f hf hfi using hs
  let x : R := ∏ q : s, f q
  have : I.IsPrime := hI.isPrime
  have hxI : x ∉ I := by
    intro hx
    obtain ⟨q, _, hq⟩ := Ideal.IsPrime.prod_mem_iff.mp hx
    exact hfi q hq
  have hrad : I.jacobson = I := (isJacobsonRing_iff_prime_eq.mp inferInstance) _ hI.isPrime
  have hm : ∃ m : Ideal R, m.IsMaximal ∧ I ≤ m ∧ x ∉ m := by
    by_contra! h
    apply hxI
    rw [← hrad, Ideal.jacobson, Ideal.mem_sInf]
    intro m hm
    exact h m hm.2 hm.1
  obtain ⟨m, hm, hIm, hxm⟩ := hm
  refine ⟨m, hm, hIm, fun q hq hqm => ?_⟩
  by_contra hne
  let i : s := ⟨q, Finset.mem_erase.mpr ⟨hne, fmin.mem_toFinset.mpr hq⟩⟩
  exact hxm (hqm (q.mem_of_dvd (Finset.dvd_prod_of_mem f (Finset.mem_univ i)) (hf i)))
private theorem quotient_dim_lower {a b : Ambient} {I : Ideal Ambient}
    (hI : I ∈ (Ideal.span {a, b}).minimalPrimes) :
    2 ≤ ringKrullDim (CoordinateRing I) := by
  classical
  let J : Ideal Ambient := Ideal.span {a, b}
  obtain ⟨m, hm, hIm, honly⟩ := isolating_maximal hI
  have : m.IsPrime := hm.isPrime
  have hJm : J ≤ m := hI.le.trans hIm
  let M : Ideal (Ambient ⧸ J) := m.map (Ideal.Quotient.mk J)
  let m' : PrimeSpectrum (Ambient ⧸ J) :=
    ⟨M, Ideal.isPrime_map_quotientMk_of_isPrime hJm⟩
  have henc : ({a, b} : Set Ambient).encard ≤ 2 := by
    simpa [one_add_one_eq_two] using Set.encard_insert_le ({b} : Set Ambient) a
  have hmheight : m.height = (4 : ℕ∞) := by
    simpa only [Nat.cast_ofNat] using maximal_height FX 4 m
  have hquot : (4 : ℕ∞) ≤ Ideal.height (R := Ambient ⧸ J) M + 2 := by
    rw [← hmheight]
    exact (Ideal.height_le_height_add_encard_of_subset {a, b}
      (show ({a, b} : Set Ambient) ⊆ m from Ideal.span_le.mp hJm)).trans
        (add_le_add le_rfl henc)
  have htall : 1 < Order.height m' := by
    rw [← PrimeSpectrum.height_eq_orderHeight (R := Ambient ⧸ J) m']
    by_contra! h
    have hbad : (4 : ℕ∞) ≤ 1 + 2 := hquot.trans (add_le_add h le_rfl)
    exact (by decide : ¬ (4 : ℕ∞) ≤ 1 + 2) hbad
  obtain ⟨q, p, hpq, hqm⟩ := Order.one_lt_height_iff.mp htall
  let e := J.primeSpectrumQuotientOrderIsoZeroLocus
  have hm' : (e m').val.asIdeal = m := by
    change (m.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = m
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, J.mk_ker,
      sup_eq_left.mpr hJm]
  have habove (r : PrimeSpectrum (Ambient ⧸ J)) (hr : r ≤ m') :
      I ≤ (e r).val.asIdeal := by
    have hrm : (e r).val.asIdeal ≤ m := hm' ▸ e.monotone hr
    have : (e r).val.asIdeal.IsPrime := (e r).val.isPrime
    obtain ⟨u, hu, hule⟩ := Ideal.exists_minimalPrimes_le
      (show J ≤ (e r).val.asIdeal from (e r).property)
    exact honly u hu (hule.trans hrm) ▸ hule
  let liftPrime (r : PrimeSpectrum (Ambient ⧸ J)) (hr : r ≤ m') :
      PrimeSpectrum (CoordinateRing I) :=
    I.primeSpectrumQuotientOrderIsoZeroLocus.symm ⟨(e r).val, habove r hr⟩
  have hmono {r t : PrimeSpectrum (Ambient ⧸ J)} {hr : r ≤ m'} {ht : t ≤ m'}
      (hlt : r < t) : liftPrime r hr < liftPrime t ht :=
    I.primeSpectrumQuotientOrderIsoZeroLocus.symm.strictMono (e.strictMono hlt)
  let p₀ := liftPrime p (hpq.trans hqm).le
  let p₁ := liftPrime q hqm.le
  let p₂ := liftPrime m' le_rfl
  have h₀₁ : p₀ < p₁ := hmono (hr := (hpq.trans hqm).le) (ht := hqm.le) hpq
  have h₁₂ : p₁ < p₂ := hmono (hr := hqm.le) (ht := le_rfl) hqm
  have htall' : 1 < Order.height p₂ :=
    Order.one_lt_height_iff.mpr ⟨p₁, p₀, h₀₁, h₁₂⟩
  have htwo : (2 : ℕ∞) ≤ Order.height p₂ := by
    simpa only [one_add_one_eq_two] using (ENat.add_one_le_iff ENat.one_ne_top).mpr htall'
  exact (WithBot.coe_le_coe.mpr htwo).trans (Order.height_le_krullDim p₂)
private theorem quotient_dim_upper {a b : Ambient} (ha : a ≠ 0)
    (hcop : ∀ D : Ambient, Irreducible D → D ∣ a → ¬ D ∣ b)
    {I : Ideal Ambient} [I.IsPrime] (haI : a ∈ I) (hbI : b ∈ I) :
    ringKrullDim (CoordinateRing I) ≤ 2 := by
  have hI₀ : I ≠ ⊥ := fun h => ha (by simpa [h] using haI)
  obtain ⟨D, hD, hprime⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹I.IsPrime› hI₀
  let T : Ideal Ambient := Ideal.span {D}
  have : T.IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hT₀ : (⊥ : Ideal Ambient) < T :=
    bot_lt_iff_ne_bot.mpr (fun h => hprime.ne_zero (Ideal.span_singleton_eq_bot.mp h))
  have hTI : T < I := by
    refine lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem I).mpr hD) ?_
    intro he
    exact hcop D hprime.irreducible
      (Ideal.mem_span_singleton.mp (he ▸ haI : a ∈ T))
      (Ideal.mem_span_singleton.mp (he ▸ hbI : b ∈ T))
  have hd : ringKrullDim Ambient = 4 := by simp [Ambient, ringKrullDim_eq_zero_of_field]
  have hbound : ringKrullDim (CoordinateRing I) + 2 ≤ 4 := by
    calc
      _ = (ringKrullDim (CoordinateRing I) + 1) + 1 := by rw [add_assoc]; norm_num
      _ ≤ ringKrullDim (CoordinateRing T) + 1 :=
        add_le_add (Ideal.ringKrullDim_quotient_succ_le_of_lt hTI) le_rfl
      _ ≤ ringKrullDim (Ambient ⧸ (⊥ : Ideal Ambient)) :=
        Ideal.ringKrullDim_quotient_succ_le_of_lt hT₀
      _ = 4 := (RingEquiv.quotientBot Ambient).ringKrullDim.trans hd
  exact (ENat.WithBot.add_le_add_natCast_right_iff (c := 2)).mp
    (by simpa only [Nat.cast_ofNat, show (2 : WithBot ℕ∞) + 2 = 4 by decide] using hbound)
theorem proof : K1_14_2_2_2.c3 := by
  classical
  intro P Q h
  let a := toJet P
  let b := toJet Q
  have ha : a ≠ 0 := by
    rw [show a = jetEquiv P from (jetEquiv_apply P).symm]
    exact map_ne_zero_iff jetEquiv jetEquiv.injective |>.mpr h.left_ne
  have hcop (D : Ambient) (hD : Irreducible D) (hDa : D ∣ a) : ¬ D ∣ b := by
    obtain ⟨d, rfl⟩ := jetEquiv.surjective D
    rw [show a = jetEquiv P from (jetEquiv_apply P).symm, map_dvd_iff] at hDa
    rw [show b = jetEquiv Q from (jetEquiv_apply Q).symm, map_dvd_iff]
    exact h.no_common d ((MulEquiv.irreducible_iff jetEquiv).mp hD) hDa
  let J : Ideal Ambient := Ideal.span {a, b}
  let fmin := J.finite_minimalPrimes_of_isNoetherianRing
  let S := fmin.toFinset
  refine ⟨S, ?_, ?_⟩
  · intro I hI
    have hmin : I ∈ J.minimalPrimes := fmin.mem_toFinset.mp hI
    have : I.IsPrime := hmin.isPrime
    have haI : a ∈ I := hmin.le (Ideal.subset_span (by simp))
    have hbI : b ∈ I := hmin.le (Ideal.subset_span (by simp))
    exact ⟨hmin.isPrime, le_antisymm (quotient_dim_upper ha hcop haI hbI)
      (quotient_dim_lower hmin), haI, hbI⟩
  · intro z R hP hQ
    let e := jetMarkHom z R
    have : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
    have hJ : J ≤ RingHom.ker e := by
      refine Ideal.span_le.mpr ?_
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact (eval_toJet z R P).trans hP
      · exact (eval_toJet z R Q).trans hQ
    obtain ⟨I, hI, hIe⟩ := Ideal.exists_minimalPrimes_le hJ
    exact ⟨I, fmin.mem_toFinset.mpr hI, hIe⟩
end
end K1_14_2_2_2_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_2_1
noncomputable section
open K1_14 K1_14_2_2 K1_14_3_2 Polynomial
private def jetVariables : Jet →+* MvPolynomial (Fin 2) Seeds :=
  (MvPolynomial.finSuccEquiv Seeds 1).symm.toRingHom.comp
    (Polynomial.mapRingHom (MvPolynomial.uniqueAlgEquiv Seeds (Fin 1)).symm.toRingHom)
private theorem coeff_jetVariables (P : Jet) (d : Fin 2 →₀ ℕ) :
    (jetVariables P).coeff d = (P.coeff (d 0)).coeff (d 1) := by
  let Q := P.map (MvPolynomial.uniqueAlgEquiv Seeds (Fin 1)).symm.toRingHom
  change ((MvPolynomial.finSuccEquiv Seeds 1).symm Q).coeff d = _
  rw [← Finsupp.cons_tail d, ← MvPolynomial.finSuccEquiv_coeff_coeff,
    AlgEquiv.apply_symm_apply]
  simp only [Q, Polynomial.coeff_map]
  change ((MvPolynomial.uniqueAlgEquiv Seeds (Fin 1)).symm (P.coeff (d 0))).coeff d.tail = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv_symm]
  rfl
private theorem jetVariables_injective : Function.Injective jetVariables :=
  (MvPolynomial.finSuccEquiv Seeds 1).symm.injective.comp
    (Polynomial.map_injective _ (MvPolynomial.uniqueAlgEquiv Seeds (Fin 1)).symm.injective)
def seedVariables : Jet →+* MvPolynomial (Fin 2) (MvPolynomial (Fin 2) FX) :=
  (MvPolynomial.commAlgEquiv FX (Fin 2) (Fin 2)).toRingHom.comp jetVariables
theorem coeff_seedVariables (P : Jet) (e d : Fin 2 →₀ ℕ) :
    ((seedVariables P).coeff e).coeff d = ((P.coeff (d 0)).coeff (d 1)).coeff e := by
  rw [← coeff_jetVariables]
  change ((MvPolynomial.commAlgEquiv FX (Fin 2) (Fin 2) (jetVariables P)).coeff e).coeff d =
    ((jetVariables P).coeff d).coeff e
  simp [MvPolynomial.commAlgEquiv, AddMonoidAlgebra.commAlgEquiv,
    AddMonoidAlgebra.curryAlgEquiv, AddMonoidAlgebra.curryRingEquiv,
    AddMonoidAlgebra.curryAddEquiv, AddMonoidAlgebra.coeff_domCongr]
theorem seedVariables_injective : Function.Injective seedVariables :=
  (MvPolynomial.commAlgEquiv FX (Fin 2) (Fin 2)).injective.comp jetVariables_injective
def jetDegree (P : Jet) : ℕ := (jetVariables P).totalDegree
def seedDegree (P : Jet) : ℕ := (seedVariables P).totalDegree
theorem jetDegree_mul {P Q : Jet} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    jetDegree (P * Q) = jetDegree P + jetDegree Q := by
  unfold jetDegree
  rw [map_mul, MvPolynomial.totalDegree_mul_of_isDomain
    ((map_ne_zero_iff _ jetVariables_injective).mpr hP)
    ((map_ne_zero_iff _ jetVariables_injective).mpr hQ)]
theorem seedDegree_mul {P Q : Jet} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    seedDegree (P * Q) = seedDegree P + seedDegree Q := by
  unfold seedDegree
  rw [map_mul, MvPolynomial.totalDegree_mul_of_isDomain
    ((map_ne_zero_iff _ seedVariables_injective).mpr hP)
    ((map_ne_zero_iff _ seedVariables_injective).mpr hQ)]
private theorem sum_exponents (d : Fin 2 →₀ ℕ) : (d.sum fun _ e => e) = d 1 + d 0 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two, Nat.add_comm]
theorem jetDegree_le (P : Jet) (b : ℕ) :
    jetDegree P ≤ b ↔ ∀ j i, (P.coeff j).coeff i ≠ 0 → i+j ≤ b := by
  constructor
  · intro h j i hji
    let d : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![j, i]
    have hd : d ∈ (jetVariables P).support := by
      rw [MvPolynomial.mem_support_iff, coeff_jetVariables]
      exact hji
    have hsum := (MvPolynomial.le_totalDegree hd).trans h
    rw [sum_exponents] at hsum
    exact hsum
  · intro h
    apply Finset.sup_le
    intro d hd
    rw [sum_exponents]
    rw [MvPolynomial.mem_support_iff, coeff_jetVariables] at hd
    exact h _ _ hd
theorem seedDegree_le (P : Jet) (u : ℕ) :
    seedDegree P ≤ u ↔ ∀ j i, ((P.coeff j).coeff i).totalDegree ≤ u := by
  constructor
  · intro h j i
    apply Finset.sup_le
    intro e he
    apply (MvPolynomial.le_totalDegree (p := seedVariables P) ?_).trans h
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    let d : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![j, i]
    have hzero := congrArg (fun a : MvPolynomial (Fin 2) FX => a.coeff d) hz
    rw [coeff_seedVariables, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hzero
    exact (MvPolynomial.mem_support_iff.mp he) hzero
  · intro h
    apply Finset.sup_le
    intro e he
    obtain ⟨d, hd⟩ : ∃ d, ((seedVariables P).coeff e).coeff d ≠ 0 := by
      by_contra! hz
      apply MvPolynomial.mem_support_iff.mp he
      ext d
      rw [hz, AddMonoidAlgebra.coeff_zero]
      rfl
    rw [coeff_seedVariables] at hd
    exact (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hd)).trans (h _ _)
theorem rowCaps_iff (P : Jet) (s : K1_14.Shape) :
    RowCaps P s ↔ jetDegree P ≤ s.B ∧ P.natDegree ≤ s.J ∧ seedDegree P ≤ s.U := by
  rw [jetDegree_le, seedDegree_le]
  constructor
  · intro h
    refine ⟨fun j i hji => (h j i hji).1, natDegree_le_iff_coeff_eq_zero.mpr ?_, ?_⟩
    · intro j hj
      apply Polynomial.ext
      intro i
      rw [coeff_zero]
      by_contra hi
      exact (Nat.not_le_of_lt hj) (h j i hi).2.1
    · intro j i
      by_cases hz : (P.coeff j).coeff i = 0
      · simp [hz]
      · exact (h j i hz).2.2
  · rintro ⟨hB, hJ, hU⟩ j i hi
    have hj : P.coeff j ≠ 0 := by intro hz; simp [hz] at hi
    exact ⟨hB j i hi, (le_natDegree_of_ne_zero hj).trans hJ, hU j i⟩
theorem jetDegree_C (f : Equation) : jetDegree (C f) = f.natDegree := by
  apply le_antisymm
  · apply (jetDegree_le _ _).mpr
    intro j i hi
    cases j with
    | zero => simpa using le_natDegree_of_ne_zero (by simpa using hi : f.coeff i ≠ 0)
    | succ j => simp at hi
  · by_cases hf : f = 0
    · simp [hf]
    · have hc : ((C f : Jet).coeff 0).coeff f.natDegree ≠ 0 := by
        simpa [coeff_natDegree] using leadingCoeff_ne_zero.mpr hf
      simpa using (jetDegree_le _ _).mp le_rfl 0 f.natDegree hc
theorem seedDegree_C (f : Equation) : seedDegree (C f) = ordinarySeedDegree f := by
  apply le_antisymm
  · apply (seedDegree_le _ _).mpr
    intro j i
    cases j with
    | zero =>
      simp only [coeff_C_zero]
      by_cases hi : f.coeff i = 0
      · simp [hi]
      · exact Finset.le_sup (f := fun y => (f.coeff y).totalDegree) (mem_support_iff.mpr hi)
    | succ j => simp
  · apply Finset.sup_le
    intro i _
    simpa using (seedDegree_le (C f) _).mp le_rfl 0 i
theorem seedDegree_seed (a : Seeds) : seedDegree (C (C a)) = a.totalDegree := by
  rw [seedDegree_C]
  by_cases ha : a = 0
  · simp [ha, ordinarySeedDegree]
  · simp [ordinarySeedDegree, support_C ha]
end
end K1_14_2_2_2_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_2_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_3_2 Polynomial
theorem extractSeed (P : Jet) (hP : P ≠ 0) :
    ∃ (a : Seeds) (R : Jet), P = C (C a) * R ∧
      ∀ b : Seeds, C (C b) ∣ R → IsUnit b := by
  classical
  revert hP
  refine (wellFounded_dvdNotUnit (α := Jet)).induction
    (C := fun P => P ≠ 0 → ∃ (a : Seeds) (R : Jet), P = C (C a) * R ∧
      ∀ b : Seeds, C (C b) ∣ R → IsUnit b) P ?_
  intro P ih hP
  by_cases h : ∃ b : Seeds, ¬ IsUnit b ∧ C (C b) ∣ P
  · obtain ⟨b, hb, Q, hQ⟩ := h
    have hQ0 : Q ≠ 0 := fun hz => hP (by simpa [hz] using hQ)
    have hlt : DvdNotUnit Q P :=
      ⟨hQ0, C (C b), fun hu => hb (isUnit_C.mp (isUnit_C.mp hu)), hQ.trans (mul_comm _ _)⟩
    obtain ⟨a, R, hR, hstrip⟩ := ih Q hlt hQ0
    exact ⟨b*a, R, by rw [C_mul, C_mul, mul_assoc, ← hR, ← hQ], hstrip⟩
  · exact ⟨1, P, by simp, fun b hb => by by_contra hu; exact h ⟨b, hu, hb⟩⟩
theorem exists_fixedIncl (D : Jet) (h : ¬ UsesSeed D) : ∃ G : ODE, D = fixedIncl G := by
  let e : Seeds →+* FX := MvPolynomial.eval (fun _ => 0)
  refine ⟨D.map (Polynomial.mapRingHom e), ?_⟩
  apply Polynomial.ext
  intro j
  apply Polynomial.ext
  intro i
  simp only [fixedIncl, K1_14_3.fixedEmbedding, Polynomial.coe_mapRingHom, coeff_map]
  have hzero : ((D.coeff j).coeff i).totalDegree = 0 :=
    Nat.eq_zero_of_not_pos (fun hp => h ⟨j,i,hp⟩)
  obtain hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero
  rw [hc]
  simp [e]
end
end K1_14_2_2_2_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_2_1
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open scoped BigOperators
theorem divisor_caps {P R : Jet} {s : Shape} (hP : P ≠ 0)
    (h : RowCaps P s) (hd : R ∣ P) : RowCaps R s := by
  obtain ⟨V, hV⟩ := hd
  have hmul : R * V ≠ 0 := hV ▸ hP
  obtain ⟨hb, hj, hu⟩ := (rowCaps_iff P s).mp h
  rw [hV, jetDegree_mul (left_ne_zero_of_mul hmul) (right_ne_zero_of_mul hmul)] at hb
  rw [hV, natDegree_mul (left_ne_zero_of_mul hmul) (right_ne_zero_of_mul hmul)] at hj
  rw [hV, seedDegree_mul (left_ne_zero_of_mul hmul) (right_ne_zero_of_mul hmul)] at hu
  exact (rowCaps_iff R s).mpr ⟨by omega, by omega, by omega⟩
theorem seedContent_cap {P : Jet} {a : Seeds} {s : Shape}
    (hP : P ≠ 0) (h : RowCaps P s) (hd : C (C a) ∣ P) : a.totalDegree ≤ s.U := by
  have hu := ((rowCaps_iff _ _).mp (divisor_caps hP h hd)).2.2
  rwa [seedDegree_seed] at hu
end
end K1_14_2_2_2_1
end
section
namespace K1_13_1_1
set_option maxRecDepth 30000
set_option Elab.async false
set_option maxHeartbeats 4000000
end K1_13_1_1
end
section
namespace K1_14_3_8
noncomputable section
open K1_14 K1_14_3 Polynomial
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
def Allowed (h W q j : ℕ) : Prop :=
  q * (131071 - h) ≤ W + j ∧ contactPower h fullShape W ≤ j + (q-j)/5
instance (h W q j : ℕ) : Decidable (Allowed h W q j) := by
  unfold Allowed
  infer_instance
end
end K1_14_3_8
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace K1_6
open K1 Polynomial
open FrobeniusLocator ProximityPrize.Benchmark
theorem lift_common_divisor {G : (Polynomial Frac)} {U V : Bivar} (hG : G ≠ 0)
    (hU : G ∣ extendSeed U) (hV : G ∣ extendSeed V) :
    ∃ D : Bivar, D ≠ 0 ∧ G.natDegree ≤ D.natDegree ∧ D ∣ U ∧ D ∣ V := by
  let φ : (Polynomial K) →+* Frac := algebraMap (Polynomial K) Frac
  have hφ : Function.Injective φ := IsFractionRing.injective (Polynomial K) Frac
  let Q : Bivar := IsLocalization.integerNormalization (nonZeroDivisors (Polynomial K)) G
  let D := Q.primPart
  obtain ⟨a, ha, hQ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (Polynomial K)) G
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hscale : C (φ Q.content) * D.map φ = C (φ a) * G := by
    calc
      C (φ Q.content) * D.map φ = Q.map φ := by
        rw [← Polynomial.map_C, ← Polynomial.map_mul, ← Q.eq_C_content_mul_primPart]
      _ = C (φ a) * G := by
        simpa only [Algebra.smul_def, Polynomial.algebraMap_apply] using hQ
  have hscale0 : C (φ a) * G ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr (fun hz => ha0 (hφ (hz.trans (map_zero φ).symm)))) hG
  have hDmap : D.map φ ≠ 0 := by
    intro hz
    exact hscale0 (by rw [← hscale, hz, mul_zero])
  have hcontent : φ Q.content ≠ 0 := by
    intro hz
    exact hscale0 (by rw [← hscale, hz, map_zero, zero_mul])
  have hD : D ≠ 0 := fun hz => hDmap (by rw [hz, Polynomial.map_zero])
  have hGtoD : G ∣ D.map φ := by
    apply (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcontent)).dvd_mul_left.mp
    rw [hscale]
    exact dvd_mul_left _ _
  have hDtoG : D.map φ ∣ G := by
    have ha' : φ a ≠ 0 := fun hz => ha0 (hφ (hz.trans (map_zero φ).symm))
    apply (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha')).dvd_mul_left.mp
    rw [← hscale]
    exact dvd_mul_left _ _
  have hdeg := natDegree_le_of_dvd hGtoD hDmap
  rw [natDegree_map_eq_of_injective hφ] at hdeg
  exact ⟨D, hD, hdeg,
    Q.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hDtoG.trans hU),
    Q.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (hDtoG.trans hV)⟩
theorem specialize_factor {D P A : Bivar} {γ : K} (hD : D ≠ 0)
    (hP : P = D * A) (hγ : atSlope P γ ≠ 0) :
    atSlope P γ = atSlope D γ * atSlope A γ ∧
      (atSlope P γ).natDegree + D.natDegree ≤ P.natDegree + (atSlope D γ).natDegree := by
  have heq : atSlope P γ = atSlope D γ * atSlope A γ := by rw [hP, atSlope, Polynomial.map_mul]; rfl
  have hDγ : atSlope D γ ≠ 0 := by
    intro hz
    exact hγ (by rw [heq, hz, zero_mul])
  have hAγ : atSlope A γ ≠ 0 := by
    intro hz
    exact hγ (by rw [heq, hz, mul_zero])
  have hA : A ≠ 0 := fun hz => hAγ (by rw [hz, atSlope, Polynomial.map_zero])
  refine ⟨heq, ?_⟩
  have hdeg : (atSlope A γ).natDegree ≤ A.natDegree := natDegree_map_le
  rw [heq, natDegree_mul hDγ hAγ, hP, natDegree_mul hD hA]
  omega
theorem eval_atSlope (P : Bivar) (γ x : K) :
    (atSlope P γ).eval x = (P.eval (C x)).eval γ := by
  simpa only [atSlope, coe_evalRingHom, eval_C] using
    (Polynomial.eval_map_apply (evalRingHom γ) (C x) (p := P))
theorem root_outside_of_dvd_locator {F ι : Type} [Field F] [Fintype ι]
    [DecidableEq ι] (x : ι → F) (hx : Function.Injective x) (errors fixed : Finset ι) (D : (Polynomial F))
    (hD : D ∣ locator x errors) (hdeg : fixed.card < D.natDegree) :
    ∃ i ∉ fixed, D.eval (x i) = 0 := by
  classical
  let S := Finset.univ.filter (fun i : ι => D.eval (x i) = 0)
  have hcard : D.natDegree = S.card := Principal.divisor_domain_roots x hx errors D hD
  have hNot : ¬ S ⊆ fixed := fun h => by
    have := Finset.card_le_card h
    omega
  obtain ⟨i, hiS, hiFixed⟩ := Finset.not_subset.mp hNot
  exact ⟨i, hiFixed, (Finset.mem_filter.mp hiS).2⟩
theorem common_node_count {F ι : Type} [Field F] [Fintype ι]
    (U V : ι → (Polynomial F)) (H : ℕ) (Γ : Finset F)
    (hU : ∀ i, (U i).natDegree ≤ H) (hV : ∀ i, (V i).natDegree ≤ H)
    (hNew : ∀ γ ∈ Γ, ∃ i, ¬ (U i = 0 ∧ V i = 0) ∧ (U i).eval γ = 0 ∧ (V i).eval γ = 0) :
    Γ.card ≤ Fintype.card ι * H := by
  classical
  let Q (i : ι) := if U i = 0 then V i else U i
  have hCover : Γ ⊆ (Finset.univ : Finset ι).biUnion (fun i => (Q i).roots.toFinset) := by
    intro γ hγ
    obtain ⟨i, hNZ, hu, hv⟩ := hNew γ hγ
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
    rw [Multiset.mem_toFinset]
    by_cases h : U i = 0
    · rw [show Q i = V i by simp [Q, h]]
      exact (mem_roots (fun hz => hNZ ⟨h, hz⟩)).mpr hv
    · rw [show Q i = U i by simp [Q, h]]
      exact (mem_roots h).mpr hu
  refine (Finset.card_le_card hCover).trans
    ((Finset.card_biUnion_le_card_mul _ _ H ?_).trans_eq (by rw [Finset.card_univ]))
  intro i _
  refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
  change (if U i = 0 then V i else U i).natDegree ≤ H
  split_ifs
  · exact hV i
  · exact hU i
end K1_6
end
section
namespace K1_13_7_1
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_1 K1_13_6
theorem weight_le_of_support_subset {R S : Type*} [CommSemiring R] [CommSemiring S]
    (w : Fin 4 → ℕ) {P : MvPolynomial (Fin 4) R} {Q : MvPolynomial (Fin 4) S}
    (h : P.support ⊆ Q.support) :
    P.weightedTotalDegree w ≤ Q.weightedTotalDegree w :=
  Finset.sup_mono h
theorem weight_const_mul_le {R : Type*} [CommSemiring R] (w : Fin 4 → ℕ)
    (a : R) (P : MvPolynomial (Fin 4) R) :
    (MvPolynomial.C a * P).weightedTotalDegree w ≤ P.weightedTotalDegree w := by
  simpa only [weightedTotalDegree_C, zero_add] using
    weightedTotalDegree_mul_le w (MvPolynomial.C a) P
theorem weight_X_le {R : Type*} [CommSemiring R] (w : Fin 4 → ℕ) (i : Fin 4) :
    (MvPolynomial.X i : MvPolynomial (Fin 4) R).weightedTotalDegree w ≤ w i :=
  mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp (X_mem_restrictWeightedDegree _ _ _ le_rfl)
theorem TaylorChart.pullback_fits (C : TaylorChart) {h : Shape} (hC : C.Fits h) (a : AffineForm) :
    GeoFits (C.pullback a) h := by
  classical
  have hw (w : Fin 4 → ℕ) (d : ℕ) (hD : C.denom.weightedTotalDegree w ≤ d)
      (hN : ∀ i, (C.numerator i).weightedTotalDegree w ≤ d) :
      (C.pullback a).weightedTotalDegree w ≤ d := by
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.add_mem
    · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((weight_const_mul_le _ _ _).trans hD)
    · apply Submodule.sum_mem
      intro i _
      exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
        ((weight_const_mul_le _ _ _).trans (hN i))
  refine ⟨?_, hw Fin.val h.j hC.1.2.1 (fun i => (hC.2 i).2.1), ?_⟩
  · simpa only [weightedTotalDegree_one] using hw 1 h.b
      (by simpa only [weightedTotalDegree_one] using hC.1.1)
      (fun i => by simpa only [weightedTotalDegree_one] using (hC.2 i).1)
  · simpa only [weightedTotalDegree_piSingle] using hw (Pi.single (3 : Fin 4) 1) h.t
      (by simpa only [weightedTotalDegree_piSingle] using hC.1.2.2)
      (fun i => by simpa only [weightedTotalDegree_piSingle] using (hC.2 i).2.2)
theorem toGeneric_fits {P : Row 4} {p : Shape} (hP : InBox (shape P) p) :
    GeoFits (toGeneric P) p := by
  classical
  have hw (w : Fin 4 → ℕ) :=
    weight_le_of_support_subset w (MvPolynomial.support_map_subset genericCoeffs P)
  refine ⟨?_, ?_, ?_⟩
  · exact (by simpa only [toGeneric, weightedTotalDegree_one] using hw 1 :
      (toGeneric P).totalDegree ≤ P.totalDegree).trans hP.1
  · exact (hw Fin.val).trans (by simpa only [shape, indexDegree_eq] using hP.2.1)
  · exact (by simpa only [toGeneric, weightedTotalDegree_piSingle] using hw (Pi.single (3 : Fin 4) 1) :
      (toGeneric P).degreeOf 3 ≤ P.degreeOf 3).trans hP.2.2
theorem top_le_index {R : Type*} [CommSemiring R] (P : MvPolynomial (Fin 4) R) :
    3 * P.degreeOf 3 ≤ P.weightedTotalDegree Fin.val := by
  classical
  rw [MvPolynomial.degreeOf_eq_sup, Nat.mul_comm 3, ← Nat.le_div_iff_mul_le (by decide : 0 < 3)]
  apply Finset.sup_le
  intro m hm
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 3)]
  have h := Finsupp.apply_smul_le_weight (fun i : Fin 4 => i.val) m (3 : Fin 4)
  have hm' := le_weightedTotalDegree (fun i : Fin 4 => i.val) hm
  have hthree : (3 : Fin 4).val = 3 := rfl
  simpa only [smul_eq_mul, hthree, Nat.mul_comm] using h.trans hm'
theorem shape_chamber (P : Row 4) : Chamber (shape P).chamber := by
  refine ⟨le_max_right _ _, ?_⟩
  change 3 * P.degreeOf 3 ≤ indexDegree P
  rw [indexDegree_eq]
  exact top_le_index P
theorem chart_chamber (L : ℕ) (p : Shape) : Chamber (chart L p) := by
  let i := 2*L*(p.j - 3) + L + 3
  refine ⟨le_max_right _ _, ?_⟩
  change 3 * min _ (i / 3) ≤ i
  have h := min_le_right (2 * L * (p.t - 1) + L + 1) (i / 3)
  omega
end
end K1_13_7_1
end
section
namespace K1_13_7_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_7_1 MvPolynomial
private def translate (a : GeoPoint) : GeoJets →ₐ[GeoField] GeoJets :=
  bind₁ (fun i => MvPolynomial.X i - C (a i))
private theorem translate_inverse (a : GeoPoint) (f : GeoJets) :
    translate (-a) (translate a f) = f := by
  unfold translate
  rw [bind₁_bind₁]
  have hi (i : Fin 4) :
      bind₁ (fun j => MvPolynomial.X j - C ((-a) j)) (MvPolynomial.X i - C (a i)) = MvPolynomial.X i := by
    simp
  simp only [hi, bind₁_X_left, AlgHom.id_apply]
private theorem eval_translate (a y : GeoPoint) (f : GeoJets) :
    eval (y + a) (translate a f) = eval y f := by
  change aeval (y + a) (bind₁ (fun i => MvPolynomial.X i - C (a i)) f) = aeval y f
  rw [aeval_bind₁]
  simp
private theorem translate_fits (a : GeoPoint) {f : GeoJets} {p : Shape}
    (hf : GeoFits f p) : GeoFits (translate a f) p := by
  have hw (w : Fin 4 → ℕ) :
      (translate a f).weightedTotalDegree w ≤ f.weightedTotalDegree w := by
    apply weightedTotalDegree_bind₁_le_of_le w w
    intro i
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    exact Submodule.sub_mem _
      (X_mem_restrictWeightedDegree _ _ _ le_rfl)
      (C_mem_restrictWeightedDegree _ _ _)
  refine ⟨?_, (hw Fin.val).trans hf.2.1, ?_⟩
  · simpa only [weightedTotalDegree_one] using (hw 1).trans
      (show f.weightedTotalDegree 1 ≤ p.b by simpa only [weightedTotalDegree_one] using hf.1)
  · simpa only [weightedTotalDegree_piSingle] using (hw (Pi.single (3 : Fin 4) 1)).trans
      (show f.weightedTotalDegree (Pi.single (3 : Fin 4) 1) ≤ p.t by
        simpa only [weightedTotalDegree_piSingle] using hf.2.2)
private theorem isolated_translate (a y : GeoPoint) {f g u v : GeoJets}
    (hy : Isolated f g u v y) :
    Isolated (translate a f) (translate a g) (translate a u) (translate a v) (y + a) := by
  let T : GeoJets →+* GeoJets := (translate a).toRingHom
  let J : Ideal GeoJets := Ideal.span ({f, g, u, v} : Set GeoJets)
  have hsurj : Function.Surjective T := by
    intro z
    refine ⟨translate (-a) z, ?_⟩
    change translate a (translate (-a) z) = z
    simpa only [neg_neg] using (translate_inverse (-a) z)
  have hinj : Function.Injective T :=
    (show Function.LeftInverse (translate (-a)) T from translate_inverse a).injective
  have hcomap : (J.map T).comap T = J := by
    rw [Ideal.comap_map_of_surjective T hsurj]
    rw [Ideal.comap_bot_of_injective T hinj, sup_bot_eq]
  have hk : (RingHom.ker (eval (y + a))).comap T = RingHom.ker (eval y) := by
    ext z
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    change eval (y + a) (translate a z) = 0 ↔ eval y z = 0
    rw [eval_translate]
  have h' : RingHom.ker (eval y) ∈ (Ideal.comap T (J.map T)).minimalPrimes := by
    rw [hcomap]
    exact hy
  rw [← hk, Ideal.comap_minimalPrimes_eq_of_surjective hsurj] at h'
  obtain ⟨P, hP, heq⟩ := h'
  have heq' : P = RingHom.ker (eval (y + a)) :=
    Ideal.comap_injective_of_surjective T hsurj heq
  change RingHom.ker (eval (y + a)) ∈
    (Ideal.span ({T f, T g, T u, T v} : Set GeoJets)).minimalPrimes
  rw [← heq']
  simpa only [J, Ideal.map_span, Set.image_insert_eq, Set.image_singleton] using hP
theorem move_to_torus {p h : Shape} {f g u v : GeoJets}
    (hf : GeoFits f p) (hg : GeoFits g p) (hu : GeoFits u h) (hv : GeoFits v h)
    (points : Finset GeoPoint) (hpts : ∀ y ∈ points, Isolated f g u v y) :
    ∃ f' g' u' v', GeoFits f' p ∧ GeoFits g' p ∧ GeoFits u' h ∧ GeoFits v' h ∧
      ∃ points' : Finset GeoPoint, points'.card = points.card ∧
        ∀ y ∈ points', Isolated f' g' u' v' y ∧ ∀ i, y i ≠ 0 := by
  classical
  have ha (i : Fin 4) : ∃ a : GeoField, a ∉ points.image (fun y => -y i) :=
    Infinite.exists_notMem_finset _
  choose a ha using ha
  let e : GeoPoint ↪ GeoPoint :=
    ⟨fun y => y + a, fun _ _ h => add_right_cancel h⟩
  refine ⟨translate a f, translate a g, translate a u, translate a v,
    translate_fits a hf, translate_fits a hg, translate_fits a hu, translate_fits a hv,
    points.map e, Finset.card_map e, ?_⟩
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
  refine ⟨isolated_translate a z (hpts z hz), ?_⟩
  intro i hi
  apply ha i
  exact Finset.mem_image.mpr ⟨z, hz, (eq_neg_of_add_eq_zero_right hi).symm⟩
end
end K1_13_7_1_1
end
section
namespace K1_14_3R
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
def chainCutter (g : ClearedEquation) : Jet :=
  C (liftEquation (clearedDx g)) +
    Polynomial.X (R := Equation) * C (liftEquation g.derivative)
def compatible (P Q : Jet) (q : Surface) : Prop :=
  ∀ f : Equation, Irreducible f → 0 < f.natDegree → C f ∣ P → C f ∣ Q →
    C f ∈ q.asIdeal → ∀ g a, IsClearing f g a →
      chainCutter g ∈ q.asIdeal
end
end K1_14_3R
end
section
set_option maxSynthPendingDepth 8
namespace K1_14_3R
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
open K1_14_2_1 (cutoffCount rawVolume movingCeiling)
open K1_14_2_1 (worstBase worstSlope surplusBase surplusSlope volume_eq)
private def Certificate (s : Shape) (r mode : ℕ) : Prop :=
  0 < worstBase s + 3555 * worstSlope s r ∧
  0 < worstBase s + 32680 * worstSlope s r ∧
  0 < surplusBase s + 3555 * surplusSlope s r mode ∧
  0 < surplusBase s + 32680 * surplusSlope s r mode
private def stageCheck (i : Fin 4) : Prop :=
  Certificate (cheapShape i) (reserve i) 0 ∧
  Certificate (layeredShape i) (reserve i) 1
private instance (i : Fin 4) : Decidable (stageCheck i) := by
  unfold stageCheck Certificate
  infer_instance
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem certificates : ∀ i : Fin 4, stageCheck i := by decide +kernel
theorem fixed_of_no_seed (G : Jet) (hn : ¬ K1_14_2.UsesSeed G) :
    G ∈ Set.range fixedEmbedding := by
  let ev := MvPolynomial.eval (fun _ : Fin 2 => (0 : FX))
  refine ⟨G.map (Polynomial.mapRingHom ev), ?_⟩
  ext j y e
  have hd : ((G.coeff j).coeff y).totalDegree = 0 :=
    Nat.eq_zero_of_not_pos fun hp => hn ⟨j, y, hp⟩
  have he := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd
  have hid : MvPolynomial.C (ev ((G.coeff j).coeff y)) = (G.coeff j).coeff y := by
    conv_lhs => rw [he]
    simpa [ev] using he.symm
  exact congrArg (fun a : Seeds => a.coeff e)
    (by simpa only [fixedEmbedding, Polynomial.coe_mapRingHom, coeff_map] using hid :
      (((fixedEmbedding (G.map (Polynomial.mapRingHom ev))).coeff j).coeff y) =
        (G.coeff j).coeff y)
end
end K1_14_3R
end
section
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
namespace K1_14_3R
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
open scoped BigOperators
private def seedValues (z : K) : Fin 2 → L :=
  ![algebraMap K L z, (algebraMap K L z) ^ p]
private def specializeSeeds (z : K) : ClearedSeeds →+* (Polynomial L) :=
  MvPolynomial.eval (fun i => C (seedValues z i))
private theorem specialize_monomial (z : K) (e : Fin 2 →₀ ℕ) (a : (Polynomial L)) :
    specializeSeeds z (MvPolynomial.monomial e a) =
      a * C (e.prod fun i n => seedValues z i ^ n) := by
  simp [specializeSeeds, MvPolynomial.eval_monomial, Finsupp.prod, map_prod, map_pow]
private theorem specialize_dxSeed (z : K) (c : ClearedSeeds) :
    specializeSeeds z (∑ e ∈ c.support, MvPolynomial.monomial e (c.coeff e).derivative) =
      (specializeSeeds z c).derivative := by
  conv_rhs => rw [c.as_sum]
  simp only [map_sum, specialize_monomial, derivative_mul, derivative_C,
    mul_zero, add_zero]
private theorem specialize_chain (g : ClearedEquation) (z : K) (T : (Polynomial L)) :
    (g.eval₂ (specializeSeeds z) T).derivative =
      (clearedDx g).eval₂ (specializeSeeds z) T +
        T.derivative * g.derivative.eval₂ (specializeSeeds z) T := by
  conv_lhs => rw [eval₂_eq_sum]
  rw [clearedDx, derivative_apply g]
  simp only [eval₂_sum, eval₂_monomial, eval₂_mul, eval₂_C, eval₂_X_pow,
    map_mul, map_natCast, specialize_dxSeed]
  simp only [Polynomial.sum, derivative_sum,
    derivative_mul, derivative_pow, Finset.sum_add_distrib, Finset.mul_sum]
  apply congrArg (_ + ·)
  apply Finset.sum_congr rfl
  intro j hj
  simp only [eval₂_natCast, map_natCast]
  ring
private theorem specialize_lift (g : ClearedEquation) (z : K) (S : (Polynomial K)) :
    atMark (liftEquation g) z S =
      algebraMap (Polynomial L) FX (g.eval₂ (specializeSeeds z) (liftPoly S)) := by
  unfold atMark liftEquation atX
  rw [coe_mapRingHom, eval₂_map, hom_eval₂]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [specializeSeeds, graphEval]
  · intro i
    fin_cases i <;> simp [specializeSeeds, graphEval, seedValues, seedEmbedding]
theorem chainCutter_zero {f : Equation} {g : ClearedEquation} {a : (Polynomial L)}
    (ha : IsClearing f g a) {z : K} {S : (Polynomial K)} (hzero : atMark f z S = 0) :
    jetAt (chainCutter g) z S = 0 := by
  have hg : atMark (liftEquation g) z S = 0 := by
    rw [ha.2]
    simpa [atMark, eval₂_mul] using
      mul_eq_zero_of_right ((graphEval z) (MvPolynomial.C (algebraMap (Polynomial L) FX a))) hzero
  rw [specialize_lift] at hg
  have ht : g.eval₂ (specializeSeeds z) (liftPoly S) = 0 :=
    (IsFractionRing.injective (Polynomial L) FX) (by simpa only [map_zero] using hg)
  have hd := specialize_chain g z (liftPoly S)
  rw [ht, derivative_zero] at hd
  have hn := congrArg (algebraMap (Polynomial L) FX) hd.symm
  rw [map_add, map_mul, map_zero, ← specialize_lift, ← specialize_lift] at hn
  simpa only [chainCutter, jetAt, eval₂_add, eval₂_mul, eval₂_C, eval₂_X,
    coe_eval₂RingHom, atMark, atX, liftPoly, derivative_map] using hn
end
end K1_14_3R
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 600000
namespace K1_14_3R
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
open scoped BigOperators
private def asSeedPoly : Equation →+* MvPolynomial (Fin 2) (Polynomial FX) :=
  eval₂RingHom (MvPolynomial.map C) (MvPolynomial.C (Polynomial.X (R := FX)))
private theorem asSeedPoly_coeff (f : Equation) (e : Fin 2 →₀ ℕ) (y : ℕ) :
    ((asSeedPoly f).coeff e).coeff y = (f.coeff y).coeff e := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_add, hf, hg]
  | monomial n c =>
    simp only [asSeedPoly, coe_eval₂RingHom, eval₂_monomial, ← map_pow]
    rw [mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, mul_comm,
      C_mul_X_pow_eq_monomial, coeff_monomial, Finsupp.single_apply, coeff_monomial, Finsupp.single_apply]
    split <;> simp
private theorem total_asSeedPoly_le (f : Equation) (U : ℕ)
    (hs : ∀ y, (f.coeff y).totalDegree ≤ U) : (asSeedPoly f).totalDegree ≤ U := by
  apply Finset.sup_le
  intro e he
  obtain ⟨y, hy⟩ : ∃ y, ((asSeedPoly f).coeff e).coeff y ≠ 0 := by
    by_contra! hz
    exact (MvPolynomial.mem_support_iff.mp he) (Polynomial.ext (by simpa using hz))
  rw [asSeedPoly_coeff] at hy
  exact (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hy)).trans (hs y)
private theorem seed_cap_of_dvd {f A : Equation} (hdiv : f ∣ A) (hn : A ≠ 0)
    {U : ℕ} (hA : ∀ y, (A.coeff y).totalDegree ≤ U) (y : ℕ) :
    (f.coeff y).totalDegree ≤ U := by
  have hn' : asSeedPoly A ≠ 0 := by
    intro hz
    apply hn
    ext n e
    simp [← asSeedPoly_coeff A e n, hz]
  have h := (MvPolynomial.totalDegree_le_of_dvd_of_isDomain (map_dvd asSeedPoly hdiv) hn').trans
    (total_asSeedPoly_le A U hA)
  apply Finset.sup_le
  intro e he
  apply (MvPolynomial.le_totalDegree (p := asSeedPoly f) ?_).trans h
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  exact (MvPolynomial.mem_support_iff.mp he) (by rw [← asSeedPoly_coeff, hz, coeff_zero])
private def liftSeed : ClearedSeeds →+* Seeds := MvPolynomial.map (algebraMap (Polynomial L) FX)
private theorem liftSeed_injective : Function.Injective liftSeed :=
  MvPolynomial.map_injective _ (IsFractionRing.injective (Polynomial L) FX)
private theorem liftSeed_degree (b : ClearedSeeds) :
    (liftSeed b).totalDegree = b.totalDegree := by
  unfold liftSeed MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective _ (IsFractionRing.injective (Polynomial L) FX)]
private theorem lift_coeff (g : ClearedEquation) (y : ℕ) :
    (liftEquation g).coeff y = liftSeed (g.coeff y) := coeff_map _ _
private theorem clearing_coeff {f : Equation} {g : ClearedEquation} {a : (Polynomial L)}
    (ha : IsClearing f g a) (y : ℕ) :
    liftSeed (g.coeff y) = MvPolynomial.C (algebraMap (Polynomial L) FX a) * f.coeff y := by
  rw [← lift_coeff, ha.2, coeff_C_mul]
private def dxSeed (b : ClearedSeeds) : ClearedSeeds :=
  ∑ e ∈ b.support, MvPolynomial.monomial e (b.coeff e).derivative
private theorem dxSeed_degree (b : ClearedSeeds) : (dxSeed b).totalDegree ≤ b.totalDegree :=
  MvPolynomial.totalDegree_finsetSum_le fun _ he =>
    (MvPolynomial.totalDegree_monomial_le _ _).trans (MvPolynomial.le_totalDegree he)
private theorem dx_coeff (g : ClearedEquation) (y : ℕ) :
    (clearedDx g).coeff y = dxSeed (g.coeff y) := by
  classical
  unfold clearedDx
  rw [coeff_sum, Polynomial.sum_def, Finset.sum_eq_single y]
  · simp [dxSeed]
  · intro j _ hj
    exact coeff_monomial_of_ne _ (Ne.symm hj)
  · intro hy
    have hzero : g.coeff y = 0 := by simpa [Polynomial.mem_support_iff] using hy
    simp [hzero]
private theorem lift_derivative {f : Equation} {g : ClearedEquation} {a : (Polynomial L)}
    (ha : IsClearing f g a) :
    liftEquation g.derivative = C (MvPolynomial.C (algebraMap (Polynomial L) FX a)) * f.derivative := by
  have hmap : liftEquation g.derivative = (liftEquation g).derivative :=
    (derivative_map g liftSeed).symm
  rw [hmap, ha.2, derivative_mul, derivative_C, zero_mul, zero_add]
private theorem degree_scalar (x : FX) (b : Seeds) :
    (MvPolynomial.C x * b).totalDegree ≤ b.totalDegree := by
  simpa using MvPolynomial.totalDegree_mul (MvPolynomial.C x) b
theorem chainCutter_caps_of_dvd {s : Shape} {Q : Jet} (hQ : Q ≠ 0)
    (hc : RowCaps Q s) (hj : 1 ≤ s.J) {f : Equation} (hf : C f ∣ Q)
    {g : ClearedEquation} {a : (Polynomial L)} (ha : IsClearing f g a) :
    RowCaps (chainCutter g) s := by
  have hn := leadingCoeff_ne_zero.mpr hQ
  have hfQ : f ∣ Q.leadingCoeff := (C_dvd_iff_dvd_coeff _ _).mp hf Q.natDegree
  have ht : (Q.coeff Q.natDegree).coeff Q.leadingCoeff.natDegree ≠ 0 := by
    rw [coeff_natDegree, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hn
  have hy : f.natDegree ≤ s.B := (natDegree_le_of_dvd hfQ hn).trans
    ((Nat.le_add_right _ _).trans (hc _ _ ht).1)
  have hu (y : ℕ) : (f.coeff y).totalDegree ≤ s.U := by
    apply seed_cap_of_dvd hfQ hn _ y
    intro j
    by_cases hz : (Q.coeff Q.natDegree).coeff j = 0
    · simpa only [← coeff_natDegree, hz, MvPolynomial.totalDegree_zero] using Nat.zero_le s.U
    · exact (hc _ _ hz).2.2
  intro v y hv
  cases v with
  | zero =>
    simp only [chainCutter, coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero,
      lift_coeff, dx_coeff] at hv ⊢
    have hfy : f.coeff y ≠ 0 := by
      intro hz
      have hg : g.coeff y = 0 := liftSeed_injective (by simp [clearing_coeff ha y, hz])
      exact hv (by simp [hg, dxSeed])
    refine ⟨(le_natDegree_of_ne_zero hfy).trans hy, Nat.zero_le _, ?_⟩
    rw [liftSeed_degree]
    refine (dxSeed_degree _).trans ?_
    rw [← liftSeed_degree, clearing_coeff ha y]
    exact (degree_scalar _ _).trans (hu y)
  | succ v =>
    simp only [chainCutter, coeff_add, coeff_C_succ, coeff_X_mul, zero_add] at hv ⊢
    cases v with
    | zero =>
      rw [coeff_C_zero, lift_derivative ha, coeff_C_mul] at hv ⊢
      have hdy : f.derivative.coeff y ≠ 0 := fun hz => hv (by simp [hz])
      have hdegree := le_natDegree_of_ne_zero hdy
      have hpos : f.natDegree ≠ 0 := by
        intro hz
        exact hdy (by rw [eq_C_of_natDegree_eq_zero hz, derivative_C, coeff_zero])
      have hlt := natDegree_derivative_lt hpos
      refine ⟨by omega, hj, (degree_scalar _ _).trans ?_⟩
      rw [coeff_derivative]
      have hcast : (↑y + 1 : Seeds) = MvPolynomial.C (↑y + 1 : FX) := by simp
      rw [hcast, mul_comm]
      exact (degree_scalar _ _).trans (hu (y+1))
    | succ v => simp [coeff_C_succ] at hv
attribute [local instance] MvPolynomial.algebraMvPolynomial Polynomial.algebra
  Polynomial.isLocalization in
private theorem exists_clearing (f : Equation) : ∃ g a, IsClearing f g a := by
  let D := (nonZeroDivisors ((Polynomial L))).map (MvPolynomial.C : (Polynomial L) →+* ClearedSeeds)
  obtain ⟨⟨g, ⟨_, d, hd, rfl⟩⟩, he⟩ := IsLocalization.surj (D.map C) f
  obtain ⟨a, ha, rfl⟩ := hd
  refine ⟨g, a, mem_nonZeroDivisors_iff_ne_zero.mp ha, ?_⟩
  change f * liftEquation (C (MvPolynomial.C a)) = liftEquation g at he
  simpa [liftEquation, mul_comm] using he.symm
private theorem derivative_nonzero {f : Equation} (hd : 0 < f.natDegree)
    (hp : f.natDegree < p) (hf : f ≠ 0) : f.derivative ≠ 0 := by
  let _ : CharP FX p := charP_of_injective_algebraMap (IsFractionRing.injective (Polynomial L) FX) p
  let _ : CharP Seeds p := charP_of_injective_ringHom (f := (MvPolynomial.C : FX →+* Seeds))
    (MvPolynomial.C_injective (Fin 2) FX) p
  have hc : (f.natDegree : Seeds) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff Seeds p]
    exact fun h => (not_le_of_gt hp) (Nat.le_of_dvd hd h)
  intro hzero
  have h := congrArg (fun A : Equation => A.coeff (f.natDegree - 1)) hzero
  have hs : f.natDegree - 1 + 1 = f.natDegree := by omega
  rw [coeff_zero, coeff_derivative, ← Nat.cast_succ, Nat.succ_eq_add_one, hs, coeff_natDegree] at h
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hf) hc h
theorem chainCutter_proper {f : Equation} (hi : Irreducible f) (hd : 0 < f.natDegree)
    (hp : f.natDegree < p) {g : ClearedEquation} {a : (Polynomial L)} (ha : IsClearing f g a) :
    K1_14_3_2.ProperPair (C f) (chainCutter g) := by
  have hC : (C f : Jet) ≠ 0 := C_ne_zero.mpr hi.ne_zero
  have ha' : algebraMap (Polynomial L) FX a ≠ 0 := by
    intro hz
    exact ha.1 ((IsFractionRing.injective (Polynomial L) FX) (by simpa only [map_zero] using hz))
  have hu : IsUnit (C (MvPolynomial.C (algebraMap (Polynomial L) FX a)) : Equation) :=
    ((isUnit_iff_ne_zero.mpr ha').map (MvPolynomial.C : FX →+* Seeds)).map
      (C : Seeds →+* Equation)
  have hder := derivative_nonzero hd hp hi.ne_zero
  have hCutter : (chainCutter g).coeff 1 = liftEquation g.derivative := by
    simp [chainCutter]
  have hder' : liftEquation g.derivative ≠ 0 := by
    rw [lift_derivative ha]
    exact mul_ne_zero hu.ne_zero hder
  have hOrd : IsRelPrime f (liftEquation g.derivative) := by
    apply hi.isRelPrime_iff_not_dvd.mpr
    rw [lift_derivative ha, hu.dvd_mul_left]
    exact fun hf => (not_le_of_gt (natDegree_derivative_lt hd.ne')) (natDegree_le_of_dvd hf hder)
  refine ⟨hC, fun h => hder' (hCutter.symm.trans (by simp [h])), ?_⟩
  intro D hD hleft hright
  have hdeg : D.natDegree ≤ 0 := by simpa using natDegree_le_of_dvd hleft hC
  have heq := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hdeg)
  rw [heq] at hleft hright
  have h0 : D.coeff 0 ∣ f := by simpa using (C_dvd_iff_dvd_coeff _ _).mp hleft 0
  have h1 := (C_dvd_iff_dvd_coeff _ _).mp hright 1
  rw [hCutter] at h1
  apply hD.not_isUnit
  rw [heq]
  exact (hOrd h0 h1).map (C : Equation →+* Jet)
theorem ordinary_graph (f : Equation) (hi : Irreducible f) (hd : 0 < f.natDegree)
    (hp : f.natDegree < p) :
    ∃ g a, IsClearing f g a ∧ K1_14_3_2.ProperPair (C f) (chainCutter g) ∧
      ∀ z S, atMark f z S = 0 → jetAt (chainCutter g) z S = 0 := by
  obtain ⟨g, a, ha⟩ := exists_clearing f
  exact ⟨g, a, ha, chainCutter_proper hi hd hp ha, fun _ _ => chainCutter_zero ha⟩
end
end K1_14_3R
end
section
namespace K1_14_2_2R
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 Polynomial
def chainCompatible (P Q : Jet) (I : Ideal Ambient) : Prop :=
  ∀ f : Equation, Irreducible f → 0 < f.natDegree → C f ∣ P → C f ∣ Q →
    toJet (C f) ∈ I → ∀ g a, K1_14_3.IsClearing f g a →
      toJet (K1_14_3R.chainCutter g) ∈ I
end
end K1_14_2_2R
end
section
namespace K1_13_6_1
noncomputable section
open Polynomial K1 K1_13 K1_13_6
open scoped BigOperators
theorem mem_markIdeal {P : Row 4} {S : (Polynomial Geom)} :
    toGeneric P ∈ markIdeal S ↔ atJet P S = 0 := by
  unfold markIdeal
  rw [RingHom.mem_ker]
  change MvPolynomial.eval _ (MvPolynomial.map genericCoeffs P) = 0 ↔ _
  rw [MvPolynomial.eval_map]
  change MvPolynomial.eval₂ genericCoeffs (⇑genericCoeffs ∘ jet S) P = 0 ↔ _
  rw [← MvPolynomial.eval₂_comp]
  have injective : Function.Injective genericCoeffs :=
    (algebraMap GenericField GeoField).injective.comp
      (IsFractionRing.injective (Polynomial Geom) GenericField)
  exact map_eq_zero_iff _ injective
private theorem atJet_eq_shift_constant (P : Row 4) (S : (Polynomial Geom)) :
    atJet P S = (shiftJet P S).coeff 0 := by
  let f := MvPolynomial.C (σ := Fin 4) (R := (Polynomial Geom))
  let g : Fin 4 → Row 4 := fun i => MvPolynomial.X i + MvPolynomial.C (jet S i)
  change (MvPolynomial.eval (jet S)) P =
    (MvPolynomial.constantCoeff.comp (MvPolynomial.eval₂Hom f g)) P
  congr 1
  ext <;> simp [f, g]
theorem orderAt_vanishes {P : Row 4} {S : (Polynomial Geom)} {l : ℕ}
    (hl : 0 < l) (h : OrderAt P S l) : atJet P S = 0 := by
  rw [atJet_eq_shift_constant]
  by_contra he
  have h0 := h 0 (MvPolynomial.mem_support_iff.mpr he)
  simp at h0
  omega
theorem mark_surface {f Q : Row 4} {S : (Polynomial Geom)} {l : ℕ}
    (hl : 0 < l) (hf : OnFactor f S) (hQ : OrderAt Q S l) :
    ∃ surface, (intersectionIdeal f Q).IsMinimalPrime surface ∧ surface ≤ markIdeal S := by
  have h : intersectionIdeal f Q ≤ markIdeal S := by
    apply Ideal.span_le.mpr
    intro P hP
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
    rcases hP with rfl | rfl
    · exact mem_markIdeal.mpr hf.1
    · exact mem_markIdeal.mpr (orderAt_vanishes hl hQ)
  have : (markIdeal S).IsPrime := RingHom.ker_isPrime (evalGeneric S)
  exact Ideal.exists_minimalPrimes_le h
theorem mark_curve {surface : Ideal GeoJets} {P : Row 4} {S : (Polynomial Geom)}
    (hZ : surface ≤ markIdeal S) (hP : atJet P S = 0) :
    ∃ C, (divisorIdeal surface P).IsMinimalPrime C ∧ C ≤ markIdeal S := by
  have h : divisorIdeal surface P ≤ markIdeal S :=
    sup_le hZ ((Ideal.span_singleton_le_iff_mem _).2 (mem_markIdeal.mpr hP))
  have : (markIdeal S).IsPrime := RingHom.ker_isPrime (evalGeneric S)
  exact Ideal.exists_minimalPrimes_le h
theorem tangentCut_vanishes (g P : Row 4) (S : (Polynomial Geom)) (a : ℕ)
    (hg : atJet g S = 0) (hP : atJet P S = 0) : atJet (tangentCut g P a) S = 0 := by
  induction a with
  | zero => exact hP
  | succ a ih =>
    rw [tangentCut, Function.iterate_succ_apply']
    rw [eval_flowNumerator _ _ _ hg]
    change atJet (separant g) S * derivative (atJet (tangentCut g P a) S) = 0
    rw [ih, map_zero, mul_zero]
end
end K1_13_6_1
end
section
namespace K1_13_6_1_4
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
open scoped BigOperators
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) (P : GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h → P ∉ surface → GeoFits P a →
    6 * (∑ C ∈ (surface ⊔ Ideal.span {P}).minimalPrimesFinset,
      sectionDegree C (h.scale 6)) ≤ surfaceDegree surface (a.scale 6) (h.scale 6)
def c2 : Prop :=
  ∀ (surface : Ideal GeoJets) (a b h : Shape) (m n : ℕ),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber b → FullChamber h → 0 < m →
    surfaceDegree surface (((a.scale m).plus (b.scale n)).scale 6) (h.scale 6) ≤
      m * surfaceDegree surface (a.scale 6) (h.scale 6) +
      n * surfaceDegree surface (b.scale 6) (h.scale 6)
def c3 : Prop :=
  ∀ (F G : GeoJets) (p q a h : Shape),
    F ≠ 0 → G ≠ 0 → IsRelPrime F G →
    FullChamber p → FullChamber q → FullChamber a → FullChamber h →
    GeoFits F p → GeoFits G q →
    ∀ (surfaces : Finset (Ideal GeoJets)) (v : Ideal GeoJets → ℕ),
      (∀ surface ∈ surfaces, ∃ hs : (pairIdeal F G).IsMinimalPrime surface,
        cycleLength (pairIdeal F G) surface hs.isPrime = (v surface : ℕ∞)) →
      32 * (∑ surface ∈ surfaces, v surface *
        surfaceDegree surface (a.scale 6) (h.scale 6)) ≤ 36 * mixed32 p q a h
end
end K1_13_6_1_4
end
section
namespace K1_13_6_1_4_2
noncomputable section
open K1_13 K1_13_6
def exponents (p : Shape) : Set (Fin 4 → ℕ) :=
  {e | e 0 + e 1 + e 2 + e 3 ≤ p.b ∧
    e 1 + 2 * e 2 + 3 * e 3 ≤ p.j ∧ e 3 ≤ p.t}
def latticeIndices (p : Shape) : Set (Fin 4 →₀ ℕ) :=
  {e | (fun i => e i) ∈ exponents (p.scale 6)}
instance (p : Shape) : Finite (latticeIndices p) := by
  refine ((Finsupp.finite_of_degree_le (6 * p.b)).subset ?_).to_subtype
  intro e he
  change e.degree ≤ 6 * p.b
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_four]
  have he' : e 0 + e 1 + e 2 + e 3 ≤ 6 * p.b := he.1
  simpa only [Nat.add_assoc] using he'
def topCoeff (surface : Ideal GeoJets) (p : Shape) : ℚ :=
  (MvPolynomial.affineHilbertPolynomial
    (surface.comap (MvPolynomial.monomialMap GeoField (latticeIndices p)).toRingHom)).coeff 2
end
end K1_13_6_1_4_2
end
section
namespace K1_13_6_1_4_2
open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1 K1_13_6_1_4
open scoped BigOperators Pointwise
theorem mem_exponents_iff (p : Shape) (m : SectionIndex p) :
    (fun i => (m i).val) ∈ exponents p ↔ m ∈ boxMonomials p := by
  norm_num [exponents, boxMonomials, Fin.sum_univ_four]
theorem exponents_eq_image (p : Shape) :
    exponents p = (fun m : SectionIndex p => fun i => (m i).val) ''
      (boxMonomials p : Set (SectionIndex p)) := by
  ext e
  constructor
  · intro he
    have hsum : (∑ i, e i) ≤ p.b := by
      have hb : e 0 + e 1 + e 2 + e 3 ≤ p.b := he.1
      simpa [Fin.sum_univ_four, Nat.add_assoc] using hb
    let m : SectionIndex p := fun i => ⟨e i, Nat.lt_succ_of_le
      ((Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hsum)⟩
    exact ⟨m, (mem_exponents_iff p m).mp he, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact (mem_exponents_iff p m).mpr hm
theorem exponents_zero : exponents ⟨0, 0, 0⟩ = ({0} : Set (Fin 4 → ℕ)) := by
  ext e
  constructor
  · intro he
    have hb : e 0 + e 1 + e 2 + e 3 ≤ 0 := he.1
    apply Set.mem_singleton_iff.mpr
    funext i
    fin_cases i
    · change e 0 = 0
      omega
    · change e 1 = 0
      omega
    · change e 2 = 0
      omega
    · change e 3 = 0
      omega
  · rintro rfl
    simp [exponents]
private theorem split_cap {x a b : ℕ} (h : x ≤ a + b) :
    ∃ u v : ℕ, u ≤ a ∧ v ≤ b ∧ u + v = x := by
  refine ⟨min x a, x - min x a, min_le_right _ _, ?_, ?_⟩
  · omega
  · omega
theorem exponents_plus (p q : Shape) (hp : Chamber p) (hq : Chamber q)
    (hpj : p.j % 2 = 0) (hqj : q.j % 2 = 0)
    (hpt : p.t % 2 = 0) :
    exponents (p.plus q) = exponents p + exponents q := by
  ext e
  change _ ↔ ∃ u ∈ exponents p, ∃ v ∈ exponents q, u + v = e
  constructor
  · intro he
    obtain ⟨htotal, hindex, htop⟩ : e 0 + e 1 + e 2 + e 3 ≤ p.b + q.b ∧
        e 1 + 2 * e 2 + 3 * e 3 ≤ p.j + q.j ∧ e 3 ≤ p.t + q.t := he
    obtain ⟨hpb, hpc⟩ := hp
    obtain ⟨hqb, hqc⟩ := hq
    let u3 := min (e 3) p.t
    let v3 := e 3 - u3
    have hu3 : u3 ≤ p.t := min_le_right _ _
    have hv3 : v3 ≤ q.t := by dsimp [u3, v3]; omega
    have huv3 : u3 + v3 = e 3 := by dsimp [u3, v3]; omega
    let jp := p.j - 3 * u3
    let jq := q.j - 3 * v3
    have hjp : jp + 3 * u3 = p.j := by dsimp [jp]; omega
    have hjq : jq + 3 * v3 = q.j := by dsimp [jq]; omega
    have hweight : e 1 + 2 * e 2 ≤ jp + jq := by omega
    have hparity : jp % 2 = 0 ∨ jq % 2 = 0 := by
      by_cases h : e 3 ≤ p.t
      · have hz : v3 = 0 := by simp [v3, u3, min_eq_left h]
        right
        omega
      · have ht : u3 = p.t := min_eq_right (by omega)
        left
        omega
    have hcapacity : e 2 ≤ jp / 2 + jq / 2 := by
      rcases hparity with h | h <;> omega
    obtain ⟨u2, v2, hu2, hv2, huv2⟩ := split_cap hcapacity
    have hindex1 : e 1 ≤ (jp - 2 * u2) + (jq - 2 * v2) := by omega
    obtain ⟨u1, v1, hu1, hv1, huv1⟩ := split_cap hindex1
    have hspentP : u1 + 2 * u2 + 3 * u3 ≤ p.j := by omega
    have hspentQ : v1 + 2 * v2 + 3 * v3 ≤ q.j := by omega
    have htotal0 : e 0 ≤ (p.b - (u1 + u2 + u3)) + (q.b - (v1 + v2 + v3)) := by omega
    obtain ⟨u0, v0, hu0, hv0, huv0⟩ := split_cap htotal0
    refine ⟨![u0, u1, u2, u3], ?_, ![v0, v1, v2, v3], ?_, ?_⟩
    · change u0 + u1 + u2 + u3 ≤ p.b ∧ u1 + 2 * u2 + 3 * u3 ≤ p.j ∧ u3 ≤ p.t
      exact ⟨by omega, hspentP, hu3⟩
    · change v0 + v1 + v2 + v3 ≤ q.b ∧ v1 + 2 * v2 + 3 * v3 ≤ q.j ∧ v3 ≤ q.t
      exact ⟨by omega, hspentQ, hv3⟩
    · funext i
      fin_cases i
      · exact huv0
      · exact huv1
      · exact huv2
      · exact huv3
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨hub, huj, hut⟩ : u 0 + u 1 + u 2 + u 3 ≤ p.b ∧
        u 1 + 2 * u 2 + 3 * u 3 ≤ p.j ∧ u 3 ≤ p.t := hu
    obtain ⟨hvb, hvj, hvt⟩ : v 0 + v 1 + v 2 + v 3 ≤ q.b ∧
        v 1 + 2 * v 2 + 3 * v 3 ≤ q.j ∧ v 3 ≤ q.t := hv
    change (u 0 + v 0) + (u 1 + v 1) + (u 2 + v 2) + (u 3 + v 3) ≤ p.b + q.b ∧
      (u 1 + v 1) + 2 * (u 2 + v 2) + 3 * (u 3 + v 3) ≤ p.j + q.j ∧
      u 3 + v 3 ≤ p.t + q.t
    exact ⟨by omega, by omega, by omega⟩
theorem chamber_scale {p : Shape} (hp : Chamber p) (k : ℕ) :
    Chamber (p.scale k) := by
  refine ⟨Nat.mul_le_mul_left k hp.1, ?_⟩
  change 3 * (k * p.t) ≤ k * p.j
  rw [Nat.mul_left_comm 3 k]
  exact Nat.mul_le_mul_left k hp.2
theorem chamber_plus {p q : Shape} (hp : Chamber p) (hq : Chamber q) :
    Chamber (p.plus q) := by
  obtain ⟨hpb, hpt⟩ := hp
  obtain ⟨hqb, hqt⟩ := hq
  change p.j + q.j ≤ p.b + q.b ∧ 3 * (p.t + q.t) ≤ p.j + q.j
  omega
theorem exponents_plus_scaled {p q : Shape} (hp : Chamber p) (hq : Chamber q) :
    exponents ((p.plus q).scale 6) = exponents (p.scale 6) + exponents (q.scale 6) := by
  rw [show (p.plus q).scale 6 = (p.scale 6).plus (q.scale 6) from by
    cases p
    cases q
    simp [Shape.plus, Shape.scale, Nat.mul_add]]
  apply exponents_plus _ _ (chamber_scale hp 6) (chamber_scale hq 6) <;>
    change 6 * _ % 2 = 0 <;> omega
theorem latticeIndices_zero (p : Shape) : (0 : Fin 4 →₀ ℕ) ∈ latticeIndices p := by
  simp [latticeIndices, exponents]
theorem latticeIndices_single {p : Shape} (hp : FullChamber p) (i : Fin 4) :
    Finsupp.single i 1 ∈ latticeIndices p := by
  obtain ⟨⟨hpb, hpj⟩, hpt⟩ := hp
  fin_cases i <;> norm_num [latticeIndices, exponents, Shape.scale, Finsupp.single_apply] <;> omega
theorem latticeIndices_plus {p q : Shape} (hp : Chamber p) (hq : Chamber q) :
    latticeIndices (p.plus q) = latticeIndices p + latticeIndices q := by
  ext e
  change (fun i => e i) ∈ exponents ((p.plus q).scale 6) ↔
    ∃ u ∈ latticeIndices p, ∃ v ∈ latticeIndices q, u + v = e
  rw [exponents_plus_scaled hp hq]
  constructor
  · rintro ⟨u, hu, v, hv, he⟩
    refine ⟨Finsupp.equivFunOnFinite.symm u, hu, Finsupp.equivFunOnFinite.symm v, hv, ?_⟩
    ext i
    exact congrFun he i
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨fun i => u i, hu, fun i => v i, hv, rfl⟩
theorem latticeIndices_scale {p : Shape} (hp : Chamber p) (n : ℕ) :
    latticeIndices (p.scale n) = n • latticeIndices p := by
  induction n with
  | zero =>
    rw [show p.scale 0 = ⟨0, 0, 0⟩ from by simp [Shape.scale]]
    ext e
    change (fun i => e i) ∈ exponents ⟨0, 0, 0⟩ ↔ e ∈ (0 : ℕ) • latticeIndices p
    rw [exponents_zero, zero_smul, Set.mem_zero, Set.mem_singleton_iff]
    constructor
    · intro he
      ext i
      exact congrFun he i
    · rintro rfl
      rfl
  | succ n ih =>
    rw [show p.scale (n + 1) = (p.scale n).plus p from by
      cases p
      simp [Shape.scale, Shape.plus, Nat.add_mul]]
    rw [latticeIndices_plus (chamber_scale hp n) hp, ih, succ_nsmul]
private theorem monomial_preimage {S : Set (Fin 4 →₀ ℕ)} {n : ℕ}
    {e : Fin 4 →₀ ℕ} (he : e ∈ n • S) :
    ∃ P : MvPolynomial S GeoField, P.totalDegree ≤ n ∧
      MvPolynomial.monomialMap GeoField S P = MvPolynomial.monomial e 1 := by
  induction n generalizing e with
  | zero =>
    rw [zero_smul, Set.mem_zero] at he
    subst e
    exact ⟨1, by simp, by simp⟩
  | succ n ih =>
    rw [succ_nsmul] at he
    obtain ⟨u, hu, v, hv, rfl⟩ := he
    obtain ⟨P, hP, hmap⟩ := ih hu
    refine ⟨P * MvPolynomial.X ⟨v, hv⟩, ?_, ?_⟩
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by
        rw [MvPolynomial.totalDegree_X]
        omega)
    · rw [map_mul, hmap, MvPolynomial.monomialMap_X, MvPolynomial.monomial_mul_monomial, mul_one]
theorem monomialMap_filtration {p : Shape} (hp : Chamber p) (n : ℕ) :
    (MvPolynomial.restrictTotalDegree (latticeIndices p) GeoField n).map
      (MvPolynomial.monomialMap GeoField (latticeIndices p)).toLinearMap =
      MvPolynomial.restrictSupport GeoField (latticeIndices (p.scale n)) := by
  rw [latticeIndices_scale hp n]
  apply le_antisymm
  · rintro _ ⟨P, hP, rfl⟩
    exact MvPolynomial.monomialMap_mem_restrictSupport_nsmul (latticeIndices_zero p)
      ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hP)
  · rw [MvPolynomial.restrictSupport_eq_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨P, hP, hmap⟩ := monomial_preimage he
    exact ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hP, hmap⟩
end K1_13_6_1_4_2
end
section
namespace K1_13_6_1_4_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1_4
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h →
    (surfaceDegree surface (a.scale 6) (h.scale 6) : ℚ) =
      topCoeff surface (a.plus h) - topCoeff surface a - topCoeff surface h
def c2 : Prop :=
  ∀ (surface : Ideal GeoJets) (a b h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber b → FullChamber h →
    ∃ (aa bb hh ab ah bh : ℚ), ∀ i j k : ℕ, 0 < i + j + k →
      topCoeff surface (((a.scale i).plus (b.scale j)).plus (h.scale k)) =
        aa * (i : ℚ)^2 + bb * (j : ℚ)^2 + hh * (k : ℚ)^2 +
        ab * (i : ℚ) * (j : ℚ) + ah * (i : ℚ) * (k : ℚ) + bh * (j : ℚ) * (k : ℚ)
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1_4.c2 := by
  intro surface a b h m n hs hdim ha hb hh hm
  let p := (a.scale m).plus (b.scale n)
  have hp : FullChamber p := by
    refine ⟨chamber_plus (chamber_scale ha.1 m) (chamber_scale hb.1 n), ?_⟩
    change 0 < m * a.t + n * b.t
    have hpos := Nat.mul_pos hm ha.2
    omega
  obtain ⟨qa, qb, qh, qab, qah, qbh, hquad⟩ := h2 surface a b h hs hdim ha hb hh
  have htest : topCoeff surface h = qh := by
    simpa [Shape.scale, Shape.plus] using hquad 0 0 1 (by decide)
  have mixed (i j : ℕ) (hij : 0 < i + j) :
      topCoeff surface (((a.scale i).plus (b.scale j)).plus h) -
        topCoeff surface ((a.scale i).plus (b.scale j)) - topCoeff surface h =
        (i : ℚ) * qah + (j : ℚ) * qbh := by
    have hbase := hquad i j 0 (by omega)
    have hsum := hquad i j 1 (by omega)
    simp [Shape.scale, Shape.plus] at hbase hsum ⊢
    rw [hbase, hsum, htest]
    ring
  have hA : (surfaceDegree surface (a.scale 6) (h.scale 6) : ℚ) = qah := by
    refine (h1 surface a h hs hdim ha hh).trans ?_
    simpa [Shape.scale, Shape.plus] using mixed 1 0 (by decide)
  have hB : (surfaceDegree surface (b.scale 6) (h.scale 6) : ℚ) = qbh := by
    refine (h1 surface b h hs hdim hb hh).trans ?_
    simpa [Shape.scale, Shape.plus] using mixed 0 1 (by decide)
  have htotal :
      (surfaceDegree surface (p.scale 6) (h.scale 6) : ℚ) =
        (m : ℚ) * (surfaceDegree surface (a.scale 6) (h.scale 6) : ℚ) +
        (n : ℚ) * (surfaceDegree surface (b.scale 6) (h.scale 6) : ℚ) := by
    rw [hA, hB, h1 surface p h hs hdim hp hh]
    exact mixed m n (by omega)
  exact le_of_eq (by exact_mod_cast htotal)
end
end K1_13_6_1_4_2
end
section
namespace K1_13_6_1_4_2_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1 K1_13_6_1_4 K1_13_6_1_4_2
def piece {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin 4) k)) (p : Shape) :
    Submodule k (MvPolynomial (Fin 4) k ⧸ I) :=
  (MvPolynomial.restrictSupport k (latticeIndices p)).map (Ideal.Quotient.mkₐ k I).toLinearMap
abbrev Coeff (a h : Shape) := PairSectionField (a.scale 6) (h.scale 6)
def extendIdeal (surface : Ideal GeoJets) (a h : Shape) :
    Ideal (MvPolynomial (Fin 4) (Coeff a h)) :=
  surface.map (MvPolynomial.map (algebraMap GeoField (Coeff a h)))
abbrev SurfaceRing (surface : Ideal GeoJets) (a h : Shape) :=
  MvPolynomial (Fin 4) (Coeff a h) ⧸ extendIdeal surface a h
def leftSection (a h : Shape) : MvPolynomial (Fin 4) (Coeff a h) :=
  sectionWith (a.scale 6) (Sum.inl : SectionIndex (a.scale 6) → PairSectionIndex (a.scale 6) (h.scale 6))
def rightSection (a h : Shape) : MvPolynomial (Fin 4) (Coeff a h) :=
  sectionWith (h.scale 6) (Sum.inr : SectionIndex (h.scale 6) → PairSectionIndex (a.scale 6) (h.scale 6))
def cutIdeal (surface : Ideal GeoJets) (a h : Shape) :
    Ideal (MvPolynomial (Fin 4) (Coeff a h)) :=
  extendIdeal surface a h ⊔ Ideal.span {leftSection a h, rightSection a h}
abbrev CutRing (surface : Ideal GeoJets) (a h : Shape) :=
  MvPolynomial (Fin 4) (Coeff a h) ⧸ cutIdeal surface a h
def cutMap (surface : Ideal GeoJets) (a h : Shape) :
    SurfaceRing surface a h →ₐ[Coeff a h] CutRing surface a h :=
  Ideal.quotientMapₐ _ (AlgHom.id _ _) (by
    change extendIdeal surface a h ≤ cutIdeal surface a h
    exact le_sup_left)
def biPiece (surface : Ideal GeoJets) (a h : Shape) (i j : ℕ) :
    Submodule (Coeff a h) (SurfaceRing surface a h) :=
  piece (extendIdeal surface a h) ((a.scale i).plus (h.scale j))
def leftMul (surface : Ideal GeoJets) (a h : Shape) :
    SurfaceRing surface a h →ₗ[Coeff a h] SurfaceRing surface a h :=
  LinearMap.mulLeft _ (Ideal.Quotient.mk (extendIdeal surface a h) (leftSection a h))
def rightMul (surface : Ideal GeoJets) (a h : Shape) :
    SurfaceRing surface a h →ₗ[Coeff a h] SurfaceRing surface a h :=
  LinearMap.mulLeft _ (Ideal.Quotient.mk (extendIdeal surface a h) (rightSection a h))
end
end K1_13_6_1_4_2_1
end
section
namespace K1_13_6_1_4_2_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1_4 K1_13_6_1_4_2 MvPolynomial
instance {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin 4) k)) (p : Shape) :
    Module.Finite k (piece I p) := by
  let := Module.Finite.of_basis (basisRestrictSupport k (latticeIndices p))
  unfold piece
  infer_instance
instance (surface : Ideal GeoJets) (a h : Shape) (i j : ℕ) :
    Module.Finite (Coeff a h) (biPiece surface a h i j) := by
  unfold biPiece
  infer_instance
theorem quotientDegreeLE_le_cutPiece (surface : Ideal GeoJets) (a h : Shape)
    (ha : FullChamber a) {N i j : ℕ} (hi : N ≤ i) :
    quotientDegreeLE (cutIdeal surface a h) N ≤
      (biPiece surface a h i j).map (cutMap surface a h).toLinearMap := by
  intro x hx
  obtain ⟨P, hP, rfl⟩ := mem_quotientDegreeLE.mp hx
  have hat := ha.2
  have haj := ha.1.2
  have hab := ha.1.1
  have haT : i ≤ i * a.t := Nat.le_mul_of_pos_right i hat
  have haJ : 3 * i ≤ i * a.j := by
    rw [Nat.mul_comm 3 i]
    exact Nat.mul_le_mul_left _ (by omega)
  have haB : i ≤ i * a.b := by
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hmem : P ∈ restrictSupport (Coeff a h) (latticeIndices ((a.scale i).plus (h.scale j))) := by
    intro e he
    have hdeg := (le_totalDegree he).trans hP
    change e.degree ≤ N at hdeg
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_four] at hdeg
    change e 0 + e 1 + e 2 + e 3 ≤ 6 * (i * a.b + j * h.b) ∧
      e 1 + 2 * e 2 + 3 * e 3 ≤ 6 * (i * a.j + j * h.j) ∧
      e 3 ≤ 6 * (i * a.t + j * h.t)
    exact ⟨by omega, by omega, by omega⟩
  refine ⟨Ideal.Quotient.mk (extendIdeal surface a h) P, ⟨P, hmem, rfl⟩, ?_⟩
  rfl
theorem mixed_difference (surface : Ideal GeoJets) (a h : Shape) (i j : ℕ)
    (hl : Function.Injective (leftMul surface a h))
    (hr : Function.Injective (rightMul surface a h))
    (hinter : (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊓
        (biPiece surface a h (i + 1) j).map (rightMul surface a h) =
      (biPiece surface a h i j).map ((leftMul surface a h).comp (rightMul surface a h)))
    (hker : biPiece surface a h (i + 1) (j + 1) ⊓ LinearMap.ker (cutMap surface a h).toLinearMap =
        (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊔
          (biPiece surface a h (i + 1) j).map (rightMul surface a h)) :
    (Module.finrank (Coeff a h) (biPiece surface a h (i + 1) (j + 1)) : ℚ) -
      (Module.finrank (Coeff a h) (biPiece surface a h i (j + 1)) : ℚ) -
      (Module.finrank (Coeff a h) (biPiece surface a h (i + 1) j) : ℚ) +
      (Module.finrank (Coeff a h) (biPiece surface a h i j) : ℚ) =
      (Module.finrank (Coeff a h)
        ((biPiece surface a h (i + 1) (j + 1)).map (cutMap surface a h).toLinearMap) : ℚ) := by
  let W := biPiece surface a h (i + 1) (j + 1)
  let q := (cutMap surface a h).toLinearMap
  let f := q.comp W.subtype
  let U := (biPiece surface a h i (j + 1)).map (leftMul surface a h)
  let V := (biPiece surface a h (i + 1) j).map (rightMul surface a h)
  have hmap : (LinearMap.ker f).map W.subtype = U ⊔ V := by
    rw [← hker]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hx, hqx⟩
      exact ⟨⟨x, hx⟩, hqx, rfl⟩
  have hrange : LinearMap.range f = W.map q := by
    dsimp only [f]
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hK : Module.finrank (Coeff a h) (LinearMap.ker f) = Module.finrank (Coeff a h) ↑(U ⊔ V) := by
    rw [← hmap]
    exact (Submodule.equivMapOfInjective _ Subtype.val_injective _).finrank_eq
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, hK] at hsum
  have huv := Submodule.finrank_sup_add_finrank_inf_eq U V
  change Module.finrank (Coeff a h) ↑(U ⊔ V) + Module.finrank (Coeff a h)
    ↑((biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊓
      (biPiece surface a h (i + 1) j).map (rightMul surface a h)) =
    Module.finrank (Coeff a h) U + Module.finrank (Coeff a h) V at huv
  have hcomp : Function.Injective ((leftMul surface a h).comp (rightMul surface a h)) :=
    fun _ _ hxy => hr (hl hxy)
  rw [hinter, ← (Submodule.equivMapOfInjective _ hcomp (biPiece surface a h i j)).finrank_eq] at huv
  have hu := (Submodule.equivMapOfInjective _ hl (biPiece surface a h i (j + 1))).finrank_eq
  have hv := (Submodule.equivMapOfInjective _ hr (biPiece surface a h (i + 1) j)).finrank_eq
  change Module.finrank (Coeff a h) (biPiece surface a h i (j + 1)) = _ at hu
  change Module.finrank (Coeff a h) (biPiece surface a h (i + 1) j) = _ at hv
  rw [show Module.finrank (Coeff a h) U = _ from hu.symm,
    show Module.finrank (Coeff a h) V = _ from hv.symm] at huv
  have hnat : Module.finrank (Coeff a h) W + Module.finrank (Coeff a h) (biPiece surface a h i j) =
      Module.finrank (Coeff a h) (W.map q) +
        Module.finrank (Coeff a h) (biPiece surface a h i (j + 1)) +
        Module.finrank (Coeff a h) (biPiece surface a h (i + 1) j) := by omega
  have hrat := congrArg (fun x : ℕ => (x : ℚ)) hnat
  push_cast at hrat
  change (Module.finrank (Coeff a h) W : ℚ) - _ - _ + _ = (Module.finrank (Coeff a h) (W.map q) : ℚ)
  linarith
end
end K1_13_6_1_4_2_1
end
section
namespace K1_13_6_1_4_2_1
noncomputable section
open K1_13 K1_13_6 K1_13_7_1 K1_13_6_1_4 K1_13_6_1_4_2 MvPolynomial
open scoped TensorProduct Polynomial
section ScalarExtension
variable {k L : Type*} [Field k] [Field L] [Algebra k L]
private abbrev mapIdeal (I : Ideal (MvPolynomial (Fin 4) k)) : Ideal (MvPolynomial (Fin 4) L) :=
  I.map (MvPolynomial.map (algebraMap k L))
private def baseQuot (I : Ideal (MvPolynomial (Fin 4) k)) :
    L ⊗[k] (MvPolynomial (Fin 4) k ⧸ I) ≃ₐ[L] MvPolynomial (Fin 4) L ⧸ mapIdeal I := by
  let e := algebraTensorAlgEquiv (σ := Fin 4) k L
  refine (Algebra.TensorProduct.tensorQuotientEquiv L (MvPolynomial (Fin 4) k) L I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change I.map (MvPolynomial.map (algebraMap k L)) =
    (I.map (Algebra.TensorProduct.includeRight (A := L)).toRingHom).map
      e.toRingEquiv.toRingHom
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro P
  change MvPolynomial.map (algebraMap k L) P = e (1 ⊗ₜ[k] P)
  simp [e]
private theorem baseQuot_tmul (I : Ideal (MvPolynomial (Fin 4) k)) (c : L)
    (P : MvPolynomial (Fin 4) k) :
    baseQuot I (c ⊗ₜ[k] Ideal.Quotient.mk I P) =
      c • Ideal.Quotient.mk (mapIdeal I) (MvPolynomial.map (algebraMap k L) P) := by
  unfold baseQuot
  simp only [AlgEquiv.trans_apply, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk, MvPolynomial.algebraTensorAlgEquiv_tmul]
  exact map_smul (Ideal.Quotient.mkₐ L (mapIdeal I)) c _
private theorem finrank_piece_baseChange (I : Ideal (MvPolynomial (Fin 4) k)) (p : Shape) :
    Module.finrank L (piece (mapIdeal (L := L) I) p) = Module.finrank k (piece I p) := by
  classical
  let W := piece I p
  let V := piece (mapIdeal (L := L) I) p
  let f : L ⊗[k] W →ₗ[L] MvPolynomial (Fin 4) L ⧸ mapIdeal I :=
    (baseQuot I).toLinearEquiv.toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.lTensor L L W.subtype)
  have hcalc (c : L) (z : W) : f (c ⊗ₜ[k] z) = baseQuot I (c ⊗ₜ[k] z.val) := rfl
  have hinj : Function.Injective f := (baseQuot I).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap W.subtype Subtype.val_injective)
  have hrange : LinearMap.range f = V := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.inductionOn with
      | tmul c z =>
        obtain ⟨P, hP, he⟩ := z.property
        have hval : Ideal.Quotient.mk I P = z.val := he
        rw [hcalc, ← hval, baseQuot_tmul]
        apply V.smul_mem
        refine ⟨_, ?_, rfl⟩
        intro e he
        exact hP (support_map_subset (algebraMap k L) P he)
      | add x y hx hy => simpa only [map_add] using V.add_mem hx hy
    · change piece (mapIdeal (L := L) I) p ≤ _
      unfold piece
      rw [restrictSupport_eq_span, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
      let z : W := ⟨Ideal.Quotient.mk I (monomial e 1),
        ⟨monomial e 1, by
          rw [restrictSupport_eq_span]
          exact Submodule.subset_span ⟨e, he, rfl⟩, rfl⟩⟩
      refine ⟨(1 : L) ⊗ₜ[k] z, ?_⟩
      rw [hcalc, show z.val = Ideal.Quotient.mk I (monomial e 1) from rfl, baseQuot_tmul]
      simp [MvPolynomial.map_monomial]
  let e := (LinearEquiv.ofInjective f hinj).trans (LinearEquiv.ofEq _ _ hrange)
  exact e.finrank_eq.symm.trans Module.finrank_baseChange
end ScalarExtension
private abbrev hilbertIdeal (surface : Ideal GeoJets) (p : Shape) :=
  surface.comap (monomialMap GeoField (latticeIndices p)).toRingHom
private abbrev hilbertPoly (surface : Ideal GeoJets) (p : Shape) :=
  affineHilbertPolynomial (hilbertIdeal surface p)
private theorem hilbertFunction_eq_piece (surface : Ideal GeoJets) {p : Shape}
    (hp : Chamber p) (n : ℕ) :
    affineHilbertFunction (hilbertIdeal surface p) n =
      Module.finrank GeoField (piece surface (p.scale n)) := by
  let φ := (Ideal.Quotient.mkₐ GeoField surface).comp (monomialMap GeoField (latticeIndices p))
  have hker : RingHom.ker φ.toRingHom = hilbertIdeal surface p := by
    ext x
    simp [φ, RingHom.mem_ker, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem]
  let j := Ideal.kerLiftAlg φ
  let V := quotientDegreeLE (RingHom.ker φ.toRingHom) n
  have hmap : V.map j.toLinearMap = piece surface (p.scale n) := by
    change ((restrictTotalDegree (latticeIndices p) GeoField n).map
      (Ideal.Quotient.mkₐ _ _).toLinearMap).map _ = _
    rw [← Submodule.map_comp, show j.toLinearMap.comp (Ideal.Quotient.mkₐ _ _).toLinearMap =
      φ.toLinearMap from rfl]
    change (restrictTotalDegree (latticeIndices p) GeoField n).map
      ((Ideal.Quotient.mkₐ GeoField surface).toLinearMap.comp
        (monomialMap GeoField (latticeIndices p)).toLinearMap) = _
    rw [Submodule.map_comp, monomialMap_filtration hp]
    rfl
  rw [← hker]
  exact (Submodule.equivMapOfInjective _ (Ideal.kerLiftAlg_injective φ) V).finrank_eq.trans
    (congrArg (fun S : Submodule GeoField (GeoJets ⧸ surface) => Module.finrank GeoField S) hmap)
private theorem ringKrullDim_ge_of_finite_injective {k A : Type*}
    [Field k] [CommRing A] [IsDomain A] {d : ℕ}
    (f : MvPolynomial (Fin d) k →+* A) (hf : Function.Injective f) (hfin : f.Finite) :
    (d : WithBot ℕ∞) ≤ ringKrullDim A := by
  let B := MvPolynomial (Fin d) k
  let algebra := f.toAlgebra
  let := algebra
  let faithful : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hf
  let finite : Module.Finite B A := hfin
  have hB : ringKrullDim B = (d : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  obtain ⟨b, hb, hbheight⟩ := Ideal.exists_isPrime_le_height (n := d) hB.ge
  obtain ⟨z, hz⟩ := Algebra.IsIntegral.comap_surjective B A (⟨b, hb⟩ : PrimeSpectrum B)
  have hzb : z.asIdeal.under B = b := congrArg PrimeSpectrum.asIdeal hz
  have hzheight := Ideal.height_under_le_height (R := B) z.asIdeal
  rw [hzb] at hzheight
  calc
    _ ≤ (z.asIdeal.height : WithBot ℕ∞) := WithBot.coe_le_coe.mpr (hbheight.trans hzheight)
    _ ≤ ringKrullDim A := Ideal.height_le_ringKrullDim_of_isPrime
private theorem hilbertPoly_degree_le (surface : Ideal GeoJets) (hs : surface.IsPrime)
    (hdim : ringKrullDim (GeoJets ⧸ surface) = 2) (p : Shape) :
    (hilbertPoly surface p).natDegree ≤ 2 := by
  let := hs
  obtain ⟨d, f, hf, hfin⟩ :=
    exists_finite_inj_algHom_of_fg GeoField (GeoJets ⧸ surface)
  have hdeg := natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective f hfin hf
  rw [Nat.card_fin] at hdeg
  have hd₀ := ringKrullDim_ge_of_finite_injective f.toRingHom hf hfin
  rw [hdim] at hd₀
  have hd : d ≤ 2 := by exact_mod_cast hd₀
  let f₀ := monomialMap GeoField (latticeIndices p)
  have hmono : Function.Injective (Ideal.quotientMapₐ surface f₀ le_rfl) :=
    Ideal.quotientMap_injective (I := surface) (f := f₀.toRingHom)
  exact (natDegree_affineHilbertPolynomial_le_of_injective _ hmono).trans (hdeg.trans_le hd)
private theorem piece_le {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin 4) k)) {p q : Shape}
    (hb : p.b ≤ q.b) (hj : p.j ≤ q.j) (ht : p.t ≤ q.t) :
    piece I p ≤ piece I q := by
  apply Submodule.map_mono
  apply restrictSupport_mono
  intro e he
  exact ⟨he.1.trans (Nat.mul_le_mul_left 6 hb), he.2.1.trans (Nat.mul_le_mul_left 6 hj),
    he.2.2.trans (Nat.mul_le_mul_left 6 ht)⟩
private theorem axis_bounds {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin 4) k))
    {p : Shape} (hp : FullChamber p) (q : Shape) (N : ℕ) :
    ∃ s : ℕ, ∀ n : ℕ,
      piece I (p.scale n) ≤ piece I ((p.scale n).plus (q.scale N)) ∧
      piece I ((p.scale n).plus (q.scale N)) ≤ piece I (p.scale (n + s)) := by
  let s := N * (q.b + q.j + q.t)
  have hpb := hp.1.1
  have hpj := hp.1.2
  have hpt := hp.2
  have hb : N * q.b ≤ s * p.b :=
    (Nat.mul_le_mul_left N (by omega : q.b ≤ q.b + q.j + q.t)).trans
      (Nat.le_mul_of_pos_right s (by omega))
  have hj : N * q.j ≤ s * p.j :=
    (Nat.mul_le_mul_left N (by omega : q.j ≤ q.b + q.j + q.t)).trans
      (Nat.le_mul_of_pos_right s (by omega))
  have ht : N * q.t ≤ s * p.t :=
    (Nat.mul_le_mul_left N (by omega : q.t ≤ q.b + q.j + q.t)).trans
      (Nat.le_mul_of_pos_right s hp.2)
  refine ⟨s, fun n => ⟨piece_le I (Nat.le_add_right ..) (Nat.le_add_right ..)
    (Nat.le_add_right ..), piece_le I ?_ ?_ ?_⟩⟩
  · simpa [Shape.scale, Shape.plus, Nat.add_mul] using Nat.add_le_add_left hb (n * p.b)
  · simpa [Shape.scale, Shape.plus, Nat.add_mul] using Nat.add_le_add_left hj (n * p.j)
  · simpa [Shape.scale, Shape.plus, Nat.add_mul] using Nat.add_le_add_left ht (n * p.t)
private theorem rectangle (H : ℕ → ℕ → ℚ) (d : ℚ) (N : ℕ)
    (hd : ∀ i j : ℕ, N ≤ i → N ≤ j →
      H (i + 1) (j + 1) - H i (j + 1) - H (i + 1) j + H i j = d) :
    ∀ i j : ℕ,
      H (N + i) (N + j) + H N N = H (N + i) N + H N (N + j) + d * (i : ℚ) * (j : ℚ) := by
  intro i
  induction i with
  | zero => intro j; simp [add_comm]
  | succ i ih =>
    intro j
    induction j with
    | zero => simp
    | succ j ihj =>
      have hstep := hd (N + i) (N + j) (by omega) (by omega)
      have h₁ := ih (j + 1)
      have h₂ := ih j
      simp only [← Nat.add_assoc, Nat.cast_add, Nat.cast_one] at h₁ ihj ⊢
      linear_combination hstep + h₁ + ihj - h₂
private def shift (P : (Polynomial ℚ)) (n : ℕ) : (Polynomial ℚ) :=
  P.comp (Polynomial.X + Polynomial.C (n : ℚ))
private theorem shift_degree (P : (Polynomial ℚ)) (n : ℕ) :
    (shift P n).natDegree ≤ P.natDegree := by
  have hh := Polynomial.natDegree_comp_le (p := P) (q := Polynomial.X + Polynomial.C (n : ℚ))
  rw [Polynomial.natDegree_X_add_C, mul_one] at hh
  exact hh
private theorem shift_coeff (P : (Polynomial ℚ)) (n : ℕ) (h : P.natDegree ≤ 2) :
    (shift P n).coeff 2 = P.coeff 2 := by
  by_cases he : P.natDegree = 2
  · have hl : P.leadingCoeff = P.coeff 2 := by rw [← Polynomial.coeff_natDegree, he]
    have hh := Polynomial.coeff_comp_degree_mul_degree (p := P)
      (q := Polynomial.X + Polynomial.C (n : ℚ)) (by rw [Polynomial.natDegree_X_add_C]; decide)
    rw [he, Polynomial.natDegree_X_add_C, Polynomial.leadingCoeff_X_add_C, mul_one,
      one_pow, mul_one, hl] at hh
    exact hh
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((shift_degree P n).trans_lt (by omega)),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < 2)]
private theorem left_axis (a h : Shape) (n : ℕ) :
    (a.scale n).plus (h.scale 0) = a.scale n := by
  cases a
  cases h
  simp [Shape.scale, Shape.plus]
private theorem right_axis (a h : Shape) (n : ℕ) :
    (a.scale 0).plus (h.scale n) = h.scale n := by
  cases a
  cases h
  simp [Shape.scale, Shape.plus]
private theorem plus_comm (a h : Shape) : a.plus h = h.plus a := by
  cases a
  cases h
  simp [Shape.plus, Nat.add_comm]
private theorem scale_plus (a h : Shape) (n : ℕ) :
    (a.plus h).scale n = (a.scale n).plus (h.scale n) := by
  cases a
  cases h
  simp [Shape.scale, Shape.plus, Nat.mul_add]
private def pieceRank {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin 4) k))
    (p : Shape) : ℕ :=
  Module.finrank k (piece I p)
private theorem exists_eval_finrank_piece (surface : Ideal GeoJets) (a h : Shape)
    {p : Shape} (hp : Chamber p) :
    ∃ M : ℕ, ∀ n ≥ M, (hilbertPoly surface p).eval (n : ℚ) =
      (pieceRank (extendIdeal surface a h) (p.scale n) : ℚ) := by
  obtain ⟨M, hM⟩ := exists_eval_affineHilbertPolynomial (hilbertIdeal surface p)
  exact ⟨M, fun n hn => by
    rw [hM n hn, hilbertFunction_eq_piece surface hp n]
    unfold pieceRank
    exact_mod_cast (finrank_piece_baseChange (L := Coeff a h) surface (p.scale n)).symm⟩
theorem polarize (surface : Ideal GeoJets) (a h : Shape) (hs : surface.IsPrime)
    (hdim : ringKrullDim (GeoJets ⧸ surface) = 2) (ha : FullChamber a) (hh : FullChamber h)
    (hmix : ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      (Module.finrank (Coeff a h) (biPiece surface a h (i + 1) (j + 1)) : ℚ) -
        (Module.finrank (Coeff a h) (biPiece surface a h i (j + 1)) : ℚ) -
        (Module.finrank (Coeff a h) (biPiece surface a h (i + 1) j) : ℚ) +
        (Module.finrank (Coeff a h) (biPiece surface a h i j) : ℚ) =
        (surfaceDegree surface (a.scale 6) (h.scale 6) : ℚ)) :
    (surfaceDegree surface (a.scale 6) (h.scale 6) : ℚ) =
      topCoeff surface (a.plus h) - topCoeff surface a - topCoeff surface h := by
  let I := extendIdeal surface a h
  let H (i j : ℕ) : ℚ :=
    pieceRank (extendIdeal surface a h) ((a.scale i).plus (h.scale j))
  let d : ℚ := surfaceDegree surface (a.scale 6) (h.scale 6)
  obtain ⟨N, hN⟩ := hmix
  have hrect := rectangle H d N hN
  obtain ⟨r, hr⟩ := axis_bounds I ha h N
  obtain ⟨s, ht⟩ := axis_bounds I hh a N
  have hre (n : ℕ) : H n 0 ≤ H n N ∧ H n N ≤ H (n + r) 0 := by
    simp only [H, left_axis]
    unfold pieceRank
    exact ⟨by exact_mod_cast Submodule.finrank_mono (hr n).1,
      by exact_mod_cast Submodule.finrank_mono (hr n).2⟩
  have hse (n : ℕ) : H 0 n ≤ H N n ∧ H N n ≤ H 0 (n + s) := by
    simp only [H, right_axis]
    rw [plus_comm (a.scale N) (h.scale n)]
    unfold pieceRank
    exact ⟨by exact_mod_cast Submodule.finrank_mono (ht n).1,
      by exact_mod_cast Submodule.finrank_mono (ht n).2⟩
  let P := hilbertPoly surface a
  let Q := hilbertPoly surface h
  let R := hilbertPoly surface (a.plus h)
  obtain ⟨MP, hMP⟩ := exists_eval_finrank_piece surface a h ha.1
  obtain ⟨MQ, hMQ⟩ := exists_eval_finrank_piece surface a h hh.1
  obtain ⟨MR, hMR⟩ := exists_eval_finrank_piece surface a h (chamber_plus ha.1 hh.1)
  have hPe (n : ℕ) (hn : MP ≤ n) : P.eval (n : ℚ) = H n 0 := by
    simpa only [P, H, left_axis] using hMP n hn
  have hQe (n : ℕ) (hn : MQ ≤ n) : Q.eval (n : ℚ) = H 0 n := by
    simpa only [Q, H, right_axis] using hMQ n hn
  have hRe (n : ℕ) (hn : MR ≤ n) : R.eval (n : ℚ) = H n n := by
    simpa only [R, H, scale_plus] using hMR n hn
  have hshift (A : (Polynomial ℚ)) (b n : ℕ) :
      (shift A b).eval (n : ℚ) = A.eval ((n + b : ℕ) : ℚ) := by
    simp [shift, Polynomial.eval_comp, Nat.cast_add]
  let C0 := Polynomial.C (H N N)
  let S := Polynomial.C d * Polynomial.X ^ 2
  let lower := shift P N + shift Q N + S - C0
  let upper := shift P (N + r) + shift Q (N + s) + S - C0
  let diag := shift R N
  have hbounds : ∀ᶠ n : ℕ in Filter.atTop,
      lower.eval (n : ℚ) ≤ diag.eval (n : ℚ) ∧ diag.eval (n : ℚ) ≤ upper.eval (n : ℚ) := by
    refine Filter.eventually_atTop.mpr ⟨max MP (max MQ MR), fun n hn => ?_⟩
    have hL := hre (N + n)
    have hU := hse (N + n)
    have hrec := hrect n n
    have hnP : MP ≤ n + N := by omega
    have hnQ : MQ ≤ n + N := by omega
    have hnR : MR ≤ n + N := by omega
    have hnPr : MP ≤ n + (N + r) := by omega
    have hnQs : MQ ≤ n + (N + s) := by omega
    simp only [lower, upper, diag, C0, S, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C, hshift,
      hPe _ hnP, hQe _ hnQ, hRe _ hnR, hPe _ hnPr, hQe _ hnQs, pow_two]
    rw [show n + N = N + n by omega, show n + (N + r) = N + n + r by omega,
      show n + (N + s) = N + n + s by omega]
    exact ⟨by nlinarith only [hL.1, hU.1, hrec], by nlinarith only [hL.2, hU.2, hrec]⟩
  have hp := hilbertPoly_degree_le surface hs hdim a
  have hq := hilbertPoly_degree_le surface hs hdim h
  have hd := hilbertPoly_degree_le surface hs hdim (a.plus h)
  have hdeg (i j : ℕ) : (shift P i + shift Q j + S - C0).natDegree ≤ 2 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · exact (Polynomial.natDegree_add_le _ _).trans
          (max_le ((shift_degree P i).trans hp) ((shift_degree Q j).trans hq))
      · exact Polynomial.natDegree_C_mul_X_pow_le _ _
    · simp [C0]
  have hlo := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
    (hdeg N N) ((shift_degree R N).trans hd) (hbounds.mono fun _ h => h.1)
  have hhi := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
    ((shift_degree R N).trans hd) (hdeg (N + r) (N + s)) (hbounds.mono fun _ h => h.2)
  have hc (i j : ℕ) : (shift P i + shift Q j + S - C0).coeff 2 = P.coeff 2 + Q.coeff 2 + d := by
    simp [S, C0, shift_coeff P i hp, shift_coeff Q j hq]
  change (shift P N + shift Q N + S - C0).coeff 2 ≤ (shift R N).coeff 2 at hlo
  change (shift R N).coeff 2 ≤ (shift P (N + r) + shift Q (N + s) + S - C0).coeff 2 at hhi
  rw [hc, shift_coeff R N hd] at hlo
  rw [hc, shift_coeff R N hd] at hhi
  change d = R.coeff 2 - P.coeff 2 - Q.coeff 2
  linarith
private abbrev cutPiece (surface : Ideal GeoJets) (a h : Shape) (i j : ℕ) :=
  (biPiece surface a h i j).map (cutMap surface a h).toLinearMap
private theorem cutPiece_mono (surface : Ideal GeoJets) (a h : Shape)
    {i j i' j' : ℕ} (hi : i ≤ i') (hj : j ≤ j') :
    cutPiece surface a h i j ≤ cutPiece surface a h i' j' := by
  apply Submodule.map_mono
  exact piece_le _ (Nat.add_le_add (Nat.mul_le_mul_right _ hi) (Nat.mul_le_mul_right _ hj))
    (Nat.add_le_add (Nat.mul_le_mul_right _ hi) (Nat.mul_le_mul_right _ hj))
    (Nat.add_le_add (Nat.mul_le_mul_right _ hi) (Nat.mul_le_mul_right _ hj))
private theorem rectangle_le (H : ℕ → ℕ → ℚ) (d : ℚ) (N : ℕ)
    (hle : ∀ i j : ℕ, N ≤ i → N ≤ j →
      d ≤ H (i + 1) (j + 1) - H i (j + 1) - H (i + 1) j + H i j) :
    ∀ i j : ℕ, H (N + i) N + H N (N + j) + d * (j : ℚ) * (i : ℚ) ≤
      H (N + i) (N + j) + H N N := by
  have vertical (i j : ℕ) :
      d * (j : ℚ) ≤ H (N + i + 1) (N + j) - H (N + i) (N + j) -
        H (N + i + 1) N + H (N + i) N := by
    induction j with
    | zero => simp
    | succ j hj =>
      have hstep := hle (N + i) (N + j) (by omega) (by omega)
      simp only [← Nat.add_assoc, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      linarith only [hj, hstep]
  intro i j
  induction i with
  | zero => simp [add_comm]
  | succ i hi =>
    have hstep := vertical i j
    simp only [← Nat.add_assoc, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
    linarith only [hi, hstep]
theorem exists_stable_cutPiece (surface : Ideal GeoJets) (a h : Shape)
    (hprime : surface.IsPrime) (hdim : ringKrullDim (GeoJets ⧸ surface) = 2)
    (ha : FullChamber a) (hh : FullChamber h) (N : ℕ)
    (hdiff : ∀ i j : ℕ, N ≤ i → N ≤ j →
      (Module.finrank (Coeff a h) (biPiece surface a h (i + 1) (j + 1)) : ℚ) -
        (Module.finrank (Coeff a h) (biPiece surface a h i (j + 1)) : ℚ) -
        (Module.finrank (Coeff a h) (biPiece surface a h (i + 1) j) : ℚ) +
        (Module.finrank (Coeff a h) (biPiece surface a h i j) : ℚ) =
        (Module.finrank (Coeff a h)
          ((biPiece surface a h (i + 1) (j + 1)).map (cutMap surface a h).toLinearMap) : ℚ)) :
    ∃ M : ℕ, ∀ i j : ℕ, M ≤ i → M ≤ j →
      (biPiece surface a h i j).map (cutMap surface a h).toLinearMap = ⊤ := by
  classical
  let H (i j : ℕ) : ℚ :=
    pieceRank (extendIdeal surface a h) ((a.scale i).plus (h.scale j))
  let E (n : ℕ) := Module.finrank (Coeff a h) (cutPiece surface a h n n)
  let R := hilbertPoly surface (a.plus h)
  obtain ⟨MR, hMR⟩ := exists_eval_finrank_piece surface a h (chamber_plus ha.1 hh.1)
  have hRe (n : ℕ) (hn : MR ≤ n) : R.eval (n : ℚ) = H n n := by
    simpa only [R, H, scale_plus] using hMR n hn
  have hr := hilbertPoly_degree_le surface hprime hdim (a.plus h)
  have hbound (k : ℕ) : (E k : ℚ) ≤ R.coeff 2 := by
    let T := max N k
    have hTk : k ≤ T := le_max_right _ _
    have hTN : N ≤ T := le_max_left _ _
    have hl (i j : ℕ) (hi : T ≤ i) (hj : T ≤ j) :
        (E k : ℚ) ≤ H (i + 1) (j + 1) - H i (j + 1) - H (i + 1) j + H i j := by
      have heq : H (i + 1) (j + 1) - H i (j + 1) - H (i + 1) j + H i j =
          (Module.finrank (Coeff a h) (cutPiece surface a h (i + 1) (j + 1)) : ℚ) :=
        hdiff i j (hTN.trans hi) (hTN.trans hj)
      rw [heq]
      exact_mod_cast Submodule.finrank_mono
        (cutPiece_mono surface a h (hTk.trans (hi.trans (Nat.le_succ _)))
          (hTk.trans (hj.trans (Nat.le_succ _))))
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        (Polynomial.C (E k : ℚ) * Polynomial.X ^ 2).eval (n : ℚ) ≤
          (shift R T + Polynomial.C (H T T)).eval (n : ℚ) := by
      refine Filter.eventually_atTop.mpr ⟨MR, fun n hn => ?_⟩
      have hrec := rectangle_le H (E k : ℚ) T hl n n
      have hnonneg (i j : ℕ) : 0 ≤ H i j := Nat.cast_nonneg _
      have hRn := hRe (T + n) (by omega)
      simp only [shift, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, ← Nat.cast_add]
      rw [Nat.add_comm n T, hRn, pow_two]
      nlinarith only [hrec, hnonneg (T + n) T, hnonneg T (T + n)]
    have hdeg : (shift R T + Polynomial.C (H T T)).natDegree ≤ 2 :=
      (Polynomial.natDegree_add_le _ _).trans <| max_le ((shift_degree R T).trans hr) (by simp)
    have hcompare := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le
      (Polynomial.natDegree_C_mul_X_pow_le (E k : ℚ) 2) hdeg hev
    simpa [Polynomial.coeff_C_mul_X_pow, shift_coeff R T hr] using hcompare
  obtain ⟨B, hB⟩ := exists_nat_gt (R.coeff 2)
  have hB' (n : ℕ) : E n ≤ B := by exact_mod_cast (hbound n).trans hB.le
  let S := (Finset.range (B + 1)).filter fun k => ∃ n, E n = k
  have hmem (n : ℕ) : E n ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hB' n)), ⟨n, rfl⟩⟩
  have hS : S.Nonempty := ⟨E 0, hmem 0⟩
  obtain ⟨M, hM⟩ := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  have hmax (n : ℕ) : E n ≤ E M := by
    rw [hM]
    exact Finset.le_max' S (E n) (hmem n)
  have htop : cutPiece surface a h M M = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n, hx⟩ := exists_mem_quotientDegreeLE (cutIdeal surface a h) x
    let m := max n M
    have hm : cutPiece surface a h M M = cutPiece surface a h m m :=
      Submodule.eq_of_le_of_finrank_le
        (cutPiece_mono surface a h (le_max_right _ _) (le_max_right _ _)) (hmax m)
    rw [hm]
    exact quotientDegreeLE_le_cutPiece surface a h ha (le_max_left _ M) hx
  exact ⟨M, fun i j hi hj => top_unique (htop ▸ cutPiece_mono surface a h hi hj)⟩
end
end K1_13_6_1_4_2_1
end
section
namespace K1_13_6_1_4_2_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1_4 K1_13_6_1_4_2
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h →
    Function.Injective (leftMul surface a h) ∧ Function.Injective (rightMul surface a h) ∧
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊓
        (biPiece surface a h (i + 1) j).map (rightMul surface a h) =
      (biPiece surface a h i j).map ((leftMul surface a h).comp (rightMul surface a h))
def c2 : Prop :=
  ∀ (surface : Ideal GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h →
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      biPiece surface a h (i + 1) (j + 1) ⊓ LinearMap.ker (cutMap surface a h).toLinearMap =
      (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊔
        (biPiece surface a h (i + 1) j).map (rightMul surface a h)
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1_4_2.c1 := by
  intro surface a h hprime hdim ha hh
  obtain ⟨hl, hr, N₁, hN₁⟩ := h1 surface a h hprime hdim ha hh
  obtain ⟨N₂, hN₂⟩ := h2 surface a h hprime hdim ha hh
  let N := max N₁ N₂
  have difference (i j : ℕ) (hi : N ≤ i) (hj : N ≤ j) :=
    mixed_difference surface a h i j hl hr
      (hN₁ i j ((le_max_left _ _).trans hi) ((le_max_left _ _).trans hj))
      (hN₂ i j ((le_max_right _ _).trans hi) ((le_max_right _ _).trans hj))
  obtain ⟨M, hM⟩ := exists_stable_cutPiece surface a h hprime hdim ha hh N difference
  apply polarize surface a h hprime hdim ha hh
  refine ⟨max N M, fun i j hi hj => ?_⟩
  have hcut := difference i j ((le_max_left _ _).trans hi) ((le_max_left _ _).trans hj)
  rw [hM (i + 1) (j + 1) ((le_max_right _ _).trans (hi.trans (Nat.le_succ _)))
    ((le_max_right _ _).trans (hj.trans (Nat.le_succ _))), finrank_top] at hcut
  exact hcut
end
end K1_13_6_1_4_2_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace K1_13_6_1_4_2_1_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1 K1_13_6_1_4
  K1_13_6_1_4_2 K1_13_6_1_4_2_1 MvPolynomial
open scoped Pointwise
variable {k : Type*} [Field k]
abbrev Affine (I : Ideal (MvPolynomial (Fin 4) k)) :=
  MvPolynomial (Fin 4) k ⧸ I
abbrev box (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) (d : ℕ × ℕ) :=
  piece I ((a.scale d.1).plus (h.scale d.2))
theorem monomial_mem_box {I : Ideal (MvPolynomial (Fin 4) k)} {a h : Shape}
    {d : ℕ × ℕ} {e : Fin 4 →₀ ℕ} (he : e ∈ latticeIndices ((a.scale d.1).plus (h.scale d.2)))
    (c : k) : Ideal.Quotient.mk I (monomial e c) ∈ box I a h d :=
  ⟨_, (monomial_mem_restrictSupport k).mpr (Or.inl he), rfl⟩
private theorem scalar_mem_box (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (d : ℕ × ℕ) (c : k) : algebraMap k (Affine I) c ∈ box I a h d := by
  change Ideal.Quotient.mk I (MvPolynomial.C c) ∈ box I a h d
  simpa only [monomial_zero'] using
    (monomial_mem_box (I := I) (d := d) (latticeIndices_zero ((a.scale d.1).plus (h.scale d.2))) c)
theorem one_mem_box (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (d : ℕ × ℕ) : (1 : Affine I) ∈ box I a h d := by
  simpa only [map_one] using scalar_mem_box I a h d 1
theorem box_mul {I : Ideal (MvPolynomial (Fin 4) k)} {a h : Shape}
    {d e : ℕ × ℕ} {x y : Affine I} (hx : x ∈ box I a h d) (hy : y ∈ box I a h e) :
    x * y ∈ box I a h (d + e) := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  refine ⟨p * q, ?_, map_mul (Ideal.Quotient.mk I) _ _⟩
  have hm := Submodule.mul_mem_mul hp hq
  rw [← restrictSupport_add k] at hm
  refine restrictSupport_mono k ?_ hm
  rintro _ ⟨u, hu, v, hv, rfl⟩
  obtain ⟨hub, huj, hut⟩ := hu
  obtain ⟨hvb, hvj, hvt⟩ := hv
  simp only [latticeIndices, Set.mem_ofPred_eq, exponents, Finsupp.add_apply,
    Shape.scale, Shape.plus, Prod.fst_add, Prod.snd_add, Nat.add_mul, Nat.mul_add] at *
  exact ⟨by omega, by omega, by omega⟩
def rees (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) :
    Subalgebra k (AddMonoidAlgebra (Affine I) (ℕ × ℕ)) where
  carrier := {p | ∀ d, p.coeff d ∈ box I a h d}
  zero_mem' d := (box I a h d).zero_mem
  add_mem' hx hy d := (box I a h d).add_mem (hx d) (hy d)
  one_mem' := by
    classical
    intro d
    change (AddMonoidAlgebra.single 0 1 : AddMonoidAlgebra (Affine I) (ℕ × ℕ)).coeff d ∈ _
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split
    · exact one_mem_box I a h d
    · exact (box I a h d).zero_mem
  mul_mem' {p q} hp hq := by
    classical
    intro d
    change (p * q).coeff d ∈ box I a h d
    simp only [AddMonoidAlgebra.coeff_mul, Finsupp.sum]
    refine (box I a h d).sum_mem fun i _ => (box I a h d).sum_mem fun j _ => ?_
    split
    · rename_i he
      rw [← he]
      exact box_mul (hp i) (hq j)
    · exact (box I a h d).zero_mem
  algebraMap_mem' c := by
    classical
    intro d
    change (AddMonoidAlgebra.single 0 (algebraMap k (Affine I) c)).coeff d ∈ _
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split
    · exact scalar_mem_box I a h d c
    · exact (box I a h d).zero_mem
def homogeneous {I : Ideal (MvPolynomial (Fin 4) k)} {a h : Shape} (d : ℕ × ℕ)
    (x : Affine I) (hx : x ∈ box I a h d) : rees I a h :=
  ⟨AddMonoidAlgebra.single d x, by
    classical
    intro e
    change (AddMonoidAlgebra.single d x).coeff e ∈ box I a h e
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split
    · rename_i he
      subst e
      exact hx
    · exact (box I a h e).zero_mem⟩
@[simp] theorem val_homogeneous {I : Ideal (MvPolynomial (Fin 4) k)} {a h : Shape}
    {d : ℕ × ℕ} {x : Affine I} (hx : x ∈ box I a h d) :
    (rees I a h).val (homogeneous d x hx) = AddMonoidAlgebra.single d x := rfl
theorem left_axis (a h : Shape) : (a.scale 1).plus (h.scale 0) = a := by
  cases a
  cases h
  simp [Shape.scale, Shape.plus]
theorem right_axis (a h : Shape) : (a.scale 0).plus (h.scale 1) = h := by
  cases a
  cases h
  simp [Shape.scale, Shape.plus]
def leftGen (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) (e : latticeIndices a) :
    rees I a h :=
  homogeneous (1, 0) (Ideal.Quotient.mk I (monomial e.val 1))
    (monomial_mem_box (by simpa only [left_axis] using e.property) 1)
def rightGen (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) (e : latticeIndices h) :
    rees I a h :=
  homogeneous (0, 1) (Ideal.Quotient.mk I (monomial e.val 1))
    (monomial_mem_box (by simpa only [right_axis] using e.property) 1)
def pairGen (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (e : latticeIndices a × latticeIndices h) : rees I a h :=
  leftGen I a h e.1 * rightGen I a h e.2
def irrelevant (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) : Ideal (rees I a h) :=
  Ideal.span (Set.range (pairGen I a h))
def shift (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) : rees I a h :=
  homogeneous (1, 1) 1 (one_mem_box I a h _)
theorem section_mem_support {σ : Type*} (p : Shape) (f : SectionIndex (p.scale 6) → σ) :
    sectionWith (p.scale 6) f ∈ restrictSupport _ (latticeIndices p) := by
  classical
  unfold sectionWith
  apply Submodule.sum_mem
  intro m hm
  let e : Fin 4 →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => (m i).val
  have he : e ∈ latticeIndices p := (mem_exponents_iff (p.scale 6) m).mpr hm
  have hprod : (∏ i : Fin 4, MvPolynomial.X i ^ (m i).val : MvPolynomial (Fin 4)
      (FractionRing (MvPolynomial σ GeoField))) = monomial e 1 := by
    rw [monic_monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
    rfl
  rw [hprod, C_mul_monomial]
  exact (monomial_mem_restrictSupport _).mpr (Or.inl he)
abbrev baseIdeal (surface : Ideal GeoJets) (a h : Shape) := extendIdeal surface a h
abbrev Rees (surface : Ideal GeoJets) (a h : Shape) := rees (baseIdeal surface a h) a h
abbrev leftClass (surface : Ideal GeoJets) (a h : Shape) :=
  Ideal.Quotient.mk (baseIdeal surface a h) (leftSection a h)
abbrev rightClass (surface : Ideal GeoJets) (a h : Shape) :=
  Ideal.Quotient.mk (baseIdeal surface a h) (rightSection a h)
theorem leftClass_mem (surface : Ideal GeoJets) (a h : Shape) :
    leftClass surface a h ∈ box (baseIdeal surface a h) a h (1, 0) := by
  rw [show box (baseIdeal surface a h) a h (1, 0) = piece (baseIdeal surface a h) a
    from congrArg (piece (baseIdeal surface a h)) (left_axis a h)]
  exact ⟨_, section_mem_support a Sum.inl, rfl⟩
theorem rightClass_mem (surface : Ideal GeoJets) (a h : Shape) :
    rightClass surface a h ∈ box (baseIdeal surface a h) a h (0, 1) := by
  rw [show box (baseIdeal surface a h) a h (0, 1) = piece (baseIdeal surface a h) h
    from congrArg (piece (baseIdeal surface a h)) (right_axis a h)]
  exact ⟨_, section_mem_support h Sum.inr, rfl⟩
def leftHom (surface : Ideal GeoJets) (a h : Shape) : Rees surface a h :=
  homogeneous (1, 0) (leftClass surface a h) (leftClass_mem surface a h)
def rightHom (surface : Ideal GeoJets) (a h : Shape) : Rees surface a h :=
  homogeneous (0, 1) (rightClass surface a h) (rightClass_mem surface a h)
def homCutIdeal (surface : Ideal GeoJets) (a h : Shape) : Ideal (Rees surface a h) :=
  Ideal.span {leftHom surface a h, rightHom surface a h}
def homBoundaryIdeal (surface : Ideal GeoJets) (a h : Shape) : Ideal (Rees surface a h) :=
  homCutIdeal surface a h ⊔ Ideal.span ({shift (baseIdeal surface a h) a h} : Set (Rees surface a h))
end
end K1_13_6_1_4_2_1_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace K1_13_6_1_4_2_1_2
noncomputable section
open K1_13 K1_13_6 K1_13_7_1 K1_13_6_1_4
  K1_13_6_1_4_2 K1_13_6_1_4_2_1 MvPolynomial
private theorem sup_pow_le {R : Type*} [CommRing R] (J P : Ideal R) (m : ℕ) :
    (J ⊔ P) ^ m ≤ J ⊔ P ^ m := by
  induction m with
  | zero => exact le_sup_right
  | succ m ih =>
    rw [pow_succ, pow_succ P]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [Ideal.mul_sup, Ideal.sup_mul, Ideal.sup_mul]
    exact sup_le (sup_le (Ideal.mul_le_left.trans le_sup_left)
      (Ideal.mul_le_right.trans le_sup_left))
      (sup_le (Ideal.mul_le_left.trans le_sup_left) le_sup_right)
theorem exists_pow_saturation_le {R T : Type*} [CommRing R] [IsNoetherianRing R]
    (g : T → R) (J : Ideal R) (s : R)
    (hg : ∀ t, ∃ m : ℕ, g t ^ m ∈ J ⊔ Ideal.span {s}) :
    ∃ N : ℕ, ∀ x ∈ Ideal.span (Set.range g) ^ N, (∃ m : ℕ, s ^ m * x ∈ J) → x ∈ J := by
  let B := Ideal.span (Set.range g)
  have hb : B ≤ (J ⊔ Ideal.span {s}).radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact hg t
  let C : ℕ →o Submodule R R :=
    ⟨fun m => J.colon {s ^ m}, by
      intro i j hij x hx
      simp only [Submodule.mem_colon_singleton, smul_eq_mul] at hx ⊢
      rw [show j = j - i + i by omega, pow_add]
      simpa only [mul_comm x, mul_assoc] using J.mul_mem_left (s ^ (j - i)) (by
        simpa only [mul_comm x] using hx)⟩
  obtain ⟨m, hm⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance C
  have hC (i : ℕ) : C i ≤ C m := by
    rcases le_total i m with h | h
    · exact C.monotone h
    · exact (hm i h).ge
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hb B.fg_of_isNoetherianRing
  have hpow : B ^ (n * m) ≤ J ⊔ Ideal.span {s ^ m} := by
    rw [pow_mul, ← Ideal.span_singleton_pow]
    exact (Ideal.pow_right_mono hn m).trans (sup_pow_le J _ m)
  have hmul : B ^ (n * m) * (C m : Ideal R) ≤ J := by
    refine (Ideal.mul_mono_left hpow).trans ?_
    rw [Ideal.sup_mul]
    refine sup_le Ideal.mul_le_left (Ideal.mul_le.mpr ?_)
    intro p hp x hx
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    have hx' : x * s ^ m ∈ J := Submodule.mem_colon_singleton.mp hx
    simpa only [mul_assoc, mul_comm (s ^ m) x] using J.mul_mem_left t hx'
  obtain ⟨k, hk⟩ := B.exists_pow_inf_eq_pow_smul (C m)
  refine ⟨k + n * m, fun x hx ⟨i, hi⟩ => ?_⟩
  have hxi : x ∈ C i := by
    apply Submodule.mem_colon_singleton.mpr
    change x * s ^ i ∈ J
    rwa [mul_comm]
  have h := hk (k + n * m) (Nat.le_add_right _ _)
  simp only [Ideal.smul_eq_mul, Ideal.mul_top, Nat.add_sub_cancel_left] at h
  have hx' : x ∈ B ^ (k + n * m) ⊓ C m := ⟨hx, hC i hxi⟩
  rw [h] at hx'
  exact hmul (Ideal.mul_mono_right inf_le_right hx')
variable {surface : Ideal GeoJets} {a h : Shape}
theorem cut_eq_zero_iff (x : SurfaceRing surface a h) :
    cutMap surface a h x = 0 ↔ x ∈ Ideal.span {leftClass surface a h, rightClass surface a h} := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (cutIdeal surface a h) p = 0 ↔ _
  have hspan : (Ideal.span {leftSection a h, rightSection a h}).map
      (Ideal.Quotient.mk (baseIdeal surface a h)) =
      Ideal.span {leftClass surface a h, rightClass surface a h} := by
    rw [Ideal.map_span]
    simp
  rw [← hspan, Ideal.mem_quotient_iff_mem_sup, Ideal.Quotient.eq_zero_iff_mem, cutIdeal, sup_comm]
private theorem left_coeff (r : Rees surface a h) (i j : ℕ) :
    ((rees (baseIdeal surface a h) a h).val (r * leftHom surface a h)).coeff (i + 1, j + 1) =
      leftMul surface a h (r.val.coeff (i, j + 1)) := by
  simp only [map_mul, leftHom, val_homogeneous]
  rw [show (i + 1, j + 1) = (i, j + 1) + (1, 0) by rfl,
    AddMonoidAlgebra.coeff_mul_single_add]
  exact mul_comm _ _
private theorem right_coeff (r : Rees surface a h) (i j : ℕ) :
    ((rees (baseIdeal surface a h) a h).val (r * rightHom surface a h)).coeff (i + 1, j + 1) =
      rightMul surface a h (r.val.coeff (i + 1, j)) := by
  simp only [map_mul, rightHom, val_homogeneous]
  rw [show (i + 1, j + 1) = (i + 1, j) + (0, 1) by rfl,
    AddMonoidAlgebra.coeff_mul_single_add]
  exact mul_comm _ _
theorem hom_mem_cut_iff (i j : ℕ) (x : SurfaceRing surface a h)
    (hx : x ∈ box (baseIdeal surface a h) a h (i + 1, j + 1)) :
    homogeneous (I := baseIdeal surface a h) (a := a) (h := h) (i + 1, j + 1) x hx ∈
        homCutIdeal surface a h ↔
      x ∈ (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊔
        (biPiece surface a h (i + 1) j).map (rightMul surface a h) := by
  constructor
  · intro hxJ
    obtain ⟨r, t, he⟩ := Ideal.mem_span_pair.mp hxJ
    have hc := congrArg (fun z : Rees surface a h =>
      ((rees (baseIdeal surface a h) a h).val z).coeff (i + 1, j + 1)) he
    change ((rees (baseIdeal surface a h) a h).val
      (r * leftHom surface a h + t * rightHom surface a h)).coeff (i + 1, j + 1) =
      ((rees (baseIdeal surface a h) a h).val
        (homogeneous (i + 1, j + 1) x hx)).coeff (i + 1, j + 1) at hc
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, left_coeff, right_coeff,
      val_homogeneous, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at hc
    have hr : r.val.coeff (i, j + 1) ∈ biPiece surface a h i (j + 1) :=
      r.property (i, j + 1)
    have ht : t.val.coeff (i + 1, j) ∈ biPiece surface a h (i + 1) j :=
      t.property (i + 1, j)
    exact Submodule.mem_sup.mpr ⟨_, Submodule.mem_map_of_mem (f := leftMul surface a h) hr,
      _, Submodule.mem_map_of_mem (f := rightMul surface a h) ht, hc⟩
  · intro hm
    obtain ⟨_, ⟨y, hy, rfl⟩, _, ⟨z, hz, rfl⟩, he⟩ := Submodule.mem_sup.mp hm
    change y ∈ box (baseIdeal surface a h) a h (i, j + 1) at hy
    change z ∈ box (baseIdeal surface a h) a h (i + 1, j) at hz
    refine Ideal.mem_span_pair.mpr
      ⟨homogeneous (i, j + 1) y hy, homogeneous (i + 1, j) z hz, Subtype.ext ?_⟩
    change (rees (baseIdeal surface a h) a h).val
      (homogeneous (i, j + 1) y hy * leftHom surface a h +
        homogeneous (i + 1, j) z hz * rightHom surface a h) =
      (rees (baseIdeal surface a h) a h).val (homogeneous (i + 1, j + 1) x hx)
    simp only [map_add, map_mul, leftHom, rightHom, val_homogeneous,
      AddMonoidAlgebra.single_mul_single]
    change AddMonoidAlgebra.single (i + 1, j + 1) (y * leftClass surface a h) +
      AddMonoidAlgebra.single (i + 1, j + 1) (z * rightClass surface a h) =
      AddMonoidAlgebra.single (i + 1, j + 1) x
    rw [← AddMonoidAlgebra.singleAddHom_apply, ← AddMonoidAlgebra.singleAddHom_apply,
      ← map_add, AddMonoidAlgebra.singleAddHom_apply]
    rw [mul_comm y, mul_comm z]
    exact congrArg (AddMonoidAlgebra.single (i + 1, j + 1)) he
private theorem degreeLE_le_box (ha : FullChamber a) {N i j : ℕ} (hi : N ≤ i) :
    quotientDegreeLE (baseIdeal surface a h) N ≤ biPiece surface a h i j := by
  intro x hx
  obtain ⟨P, hP, rfl⟩ := mem_quotientDegreeLE.mp hx
  have haT : i ≤ i * a.t := Nat.le_mul_of_pos_right i ha.2
  have haJ : 3 * i ≤ i * a.j := by
    rw [Nat.mul_comm 3 i]
    exact Nat.mul_le_mul_left _ (by have := ha.1.2; have := ha.2; omega)
  have haB : i ≤ i * a.b := by
    exact Nat.le_mul_of_pos_right _ (by have := ha.1.1; have := ha.1.2; have := ha.2; omega)
  refine ⟨P, ?_, rfl⟩
  intro e he
  have hd := (le_totalDegree he).trans hP
  change e.degree ≤ N at hd
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_four] at hd
  change e 0 + e 1 + e 2 + e 3 ≤ 6 * (i * a.b + j * h.b) ∧
    e 1 + 2 * e 2 + 3 * e 3 ≤ 6 * (i * a.j + j * h.j) ∧
    e 3 ≤ 6 * (i * a.t + j * h.t)
  exact ⟨by omega, by omega, by omega⟩
private theorem val_shift_pow (n : ℕ) :
    (rees (baseIdeal surface a h) a h).val (shift (baseIdeal surface a h) a h ^ n) =
      AddMonoidAlgebra.single (n, n) 1 := by
  induction n with
  | zero => simp only [pow_zero, map_one, AddMonoidAlgebra.one_def]; rfl
  | succ n ih =>
    rw [pow_succ, map_mul, ih]
    change (AddMonoidAlgebra.single (n, n) 1 : AddMonoidAlgebra
      (SurfaceRing surface a h) (ℕ × ℕ)) * AddMonoidAlgebra.single (1, 1) 1 = _
    rw [AddMonoidAlgebra.single_mul_single, mul_one, Prod.mk_add_mk]
theorem exists_shift_pow_mem_cut (ha : FullChamber a) (i j : ℕ)
    (x : SurfaceRing surface a h) (hx : x ∈ box (baseIdeal surface a h) a h (i + 1, j + 1))
    (hzero : cutMap surface a h x = 0) :
    ∃ n : ℕ, shift (baseIdeal surface a h) a h ^ n *
      homogeneous (i + 1, j + 1) x hx ∈ homCutIdeal surface a h := by
  obtain ⟨u, v, he⟩ := Ideal.mem_span_pair.mp ((cut_eq_zero_iff x).mp hzero)
  obtain ⟨nu, hu⟩ := exists_mem_quotientDegreeLE (baseIdeal surface a h) u
  obtain ⟨nv, hv⟩ := exists_mem_quotientDegreeLE (baseIdeal surface a h) v
  let n := max nu nv
  let f : Rees surface a h :=
    shift (baseIdeal surface a h) a h ^ n * homogeneous (i + 1, j + 1) x hx
  have hf : (rees (baseIdeal surface a h) a h).val f =
      AddMonoidAlgebra.single (n + i + 1, n + j + 1) x := by
    dsimp only [f]
    rw [map_mul, val_shift_pow, val_homogeneous, AddMonoidAlgebra.single_mul_single,
      one_mul, Prod.mk_add_mk, Nat.add_assoc, Nat.add_assoc]
  have hfx : x ∈ box (baseIdeal surface a h) a h (n + i + 1, n + j + 1) := by
    have hc := f.property (n + i + 1, n + j + 1)
    change ((rees (baseIdeal surface a h) a h).val f).coeff (n + i + 1, n + j + 1) ∈
      box (baseIdeal surface a h) a h (n + i + 1, n + j + 1) at hc
    simpa only [hf, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using hc
  have hf' : f = homogeneous (n + i + 1, n + j + 1) x hfx := Subtype.ext hf
  refine ⟨n, ?_⟩
  change f ∈ _
  rw [hf', hom_mem_cut_iff]
  have hui : nu ≤ n + i := (le_max_left _ _).trans (Nat.le_add_right _ _)
  have hvi : nv ≤ n + i + 1 :=
    (le_max_right nu nv).trans ((Nat.le_add_right n i).trans (Nat.le_succ _))
  exact Submodule.mem_sup.mpr ⟨_, ⟨u, degreeLE_le_box ha hui hu, rfl⟩,
    _, ⟨v, degreeLE_le_box ha hvi hv, rfl⟩, by
      change leftClass surface a h * u + rightClass surface a h * v = x
      rwa [mul_comm (leftClass surface a h) u, mul_comm (rightClass surface a h) v]⟩
end
end K1_13_6_1_4_2_1_2
end
section
namespace K1_13_6_1_4_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_1
open MvPolynomial
def sliceMap (h : Shape) : GeoJets →+* SectionJets h :=
  MvPolynomial.map (algebraMap GeoField (SectionField h))
def sliceIdeal (J : Ideal GeoJets) (h : Shape) : Ideal (SectionJets h) :=
  J.map (sliceMap h) ⊔ Ideal.span {genericSection h}
def FitsBox {k : Type} [Field k] (Q : MvPolynomial (Fin 4) k) (a : Shape) : Prop :=
  Q.totalDegree ≤ a.b ∧ Q.weightedTotalDegree Fin.val ≤ a.j ∧ Q.degreeOf 3 ≤ a.t
abbrev CutField (k : Type) [Field k] (a : Shape) :=
  FractionRing (MvPolynomial (SectionIndex a) k)
def cutPolynomial (k : Type) [Field k] (a : Shape) :
    MvPolynomial (Fin 4) (CutField k a) :=
  ∑ m ∈ boxMonomials a,
    MvPolynomial.C (algebraMap (MvPolynomial (SectionIndex a) k) (CutField k a) (MvPolynomial.X m)) *
      ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val
def genericCutLength {k : Type} [Field k] (I : Ideal (MvPolynomial (Fin 4) k))
    (a : Shape) : ℕ :=
  Module.finrank (CutField k a) (MvPolynomial (Fin 4) (CutField k a) ⧸
    (I.map (MvPolynomial.map (algebraMap k (CutField k a))) ⊔
      Ideal.span {cutPolynomial k a}))
end
end K1_13_6_1_4_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_1_4_2_1_2
noncomputable section
open K1_13 K1_13_6 K1_13_7_1 K1_13_6_1_4
  K1_13_6_1_4_2 K1_13_6_1_4_2_1 MvPolynomial
def c1 : Prop :=
  ∀ {k : Type} [Field k] (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape),
    Chamber a → Chamber h →
    IsNoetherianRing (rees I a h) ∧
    ∀ (i j : ℕ) (x : Affine I) (hx : x ∈ box I a h (i, j)) (n : ℕ),
      n ≤ i → n ≤ j → homogeneous (i, j) x hx ∈ irrelevant I a h ^ n
def c2 : Prop :=
  ∀ (surface : Ideal GeoJets) (a h : Shape),
    surface.IsPrime → ringKrullDim (GeoJets ⧸ surface) = 2 →
    FullChamber a → FullChamber h →
    ∀ e : latticeIndices a × latticeIndices h,
      ∃ m : ℕ, pairGen (baseIdeal surface a h) a h e ^ m ∈ homBoundaryIdeal surface a h
private theorem image_sum_le (surface : Ideal GeoJets) (a h : Shape) (i j : ℕ) :
    (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊔
      (biPiece surface a h (i + 1) j).map (rightMul surface a h) ≤
    biPiece surface a h (i + 1) (j + 1) ⊓ LinearMap.ker (cutMap surface a h).toLinearMap := by
  intro x hx
  obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
  change u ∈ box (baseIdeal surface a h) a h (i, j + 1) at hu
  change v ∈ box (baseIdeal surface a h) a h (i + 1, j) at hv
  have hu' := box_mul hu (leftClass_mem surface a h)
  have hv' := box_mul hv (rightClass_mem surface a h)
  have hsum : leftClass surface a h * u + rightClass surface a h * v ∈
      biPiece surface a h (i + 1) (j + 1) := by
    rw [mul_comm (leftClass surface a h) u, mul_comm (rightClass surface a h) v]
    exact (biPiece surface a h (i + 1) (j + 1)).add_mem hu' hv'
  refine ⟨hsum, (cut_eq_zero_iff _).mpr ?_⟩
  apply Ideal.mem_span_pair.mpr
  refine ⟨u, v, ?_⟩
  change u * leftClass surface a h + v * rightClass surface a h =
    leftClass surface a h * u + rightClass surface a h * v
  rw [mul_comm u, mul_comm v]
private theorem boundary_bound (surface : Ideal GeoJets) (a h : Shape)
    (hNoeth : IsNoetherianRing (Rees surface a h))
    (hchart : ∀ e : latticeIndices a × latticeIndices h,
      ∃ m : ℕ, pairGen (baseIdeal surface a h) a h e ^ m ∈ homBoundaryIdeal surface a h) :
    ∃ N : ℕ, ∀ f ∈ irrelevant (baseIdeal surface a h) a h ^ N,
      (∃ m : ℕ, shift (baseIdeal surface a h) a h ^ m * f ∈ homCutIdeal surface a h) →
      f ∈ homCutIdeal surface a h :=
  @exists_pow_saturation_le (Rees surface a h) (latticeIndices a × latticeIndices h)
    inferInstance hNoeth (pairGen (baseIdeal surface a h) a h)
    (homCutIdeal surface a h) (shift (baseIdeal surface a h) a h) hchart
private theorem ker_le_image_sum (surface : Ideal GeoJets) (a h : Shape) (ha : FullChamber a)
    (i j N : ℕ)
    (hpower : ∀ (x : SurfaceRing surface a h) (hx : x ∈ box (baseIdeal surface a h) a h (i + 1, j + 1)),
      homogeneous (i + 1, j + 1) x hx ∈ irrelevant (baseIdeal surface a h) a h ^ N)
    (hbound : ∀ f ∈ irrelevant (baseIdeal surface a h) a h ^ N,
      (∃ m : ℕ, shift (baseIdeal surface a h) a h ^ m * f ∈ homCutIdeal surface a h) →
      f ∈ homCutIdeal surface a h) :
    biPiece surface a h (i + 1) (j + 1) ⊓ LinearMap.ker (cutMap surface a h).toLinearMap ≤
      (biPiece surface a h i (j + 1)).map (leftMul surface a h) ⊔
        (biPiece surface a h (i + 1) j).map (rightMul surface a h) := by
  rintro x ⟨hx, hxzero⟩
  change x ∈ box (baseIdeal surface a h) a h (i + 1, j + 1) at hx
  apply (hom_mem_cut_iff i j x hx).mp
  exact hbound _ (hpower x hx) (exists_shift_pow_mem_cut ha i j x hx hxzero)
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1_4_2_1.c2 := by
  intro surface a h hs hdim ha hh
  obtain ⟨hNoeth, hpower⟩ := h1 (baseIdeal surface a h) a h ha.1 hh.1
  obtain ⟨N, hbound⟩ := boundary_bound surface a h hNoeth (h2 surface a h hs hdim ha hh)
  refine ⟨N, fun i j hi hj => le_antisymm ?_ (image_sum_le surface a h i j)⟩
  exact ker_le_image_sum surface a h ha i j N
    (fun x hx => hpower (i + 1) (j + 1) x hx N
      (hi.trans (Nat.le_succ i)) (hj.trans (Nat.le_succ j))) hbound
end
end K1_13_6_1_4_2_1_2
end
section
namespace K1_13_7_2_3
open K1_13_6
structure ProperComponent (surface : Ideal GeoJets) (P : GeoJets) (C : Ideal GeoJets) : Prop where
  prime : surface.IsPrime
  height : surface.height = 2
  proper : P ∉ surface
  component : (surface ⊔ Ideal.span {P}).IsMinimalPrime C
end K1_13_7_2_3
end

end Merged6967_Fast051

section Merged6967_R6960Front6960ListCells1
set_option Elab.async false


set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6960ListBank
open scoped BigOperators

private def allowance_10 (u : ℕ) : ℕ :=
  nominal 10 u

private theorem bound_10 (u : ℕ) :
    (CJ0.blockMatrix source 10 ((u : ℤ)-24)).rank ≤ allowance_10 u := by
  unfold allowance_10
  exact (block_rank_le 10 _).trans (rank_le_nominal 10 _)

theorem grade_10 : (∑ u ∈ Finset.range (81-10), (CJ0.blockMatrix source 10 ((u : ℤ)-24)).rank) ≤ 3102 := by
  refine (Finset.sum_le_sum fun u _ => bound_10 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_10)]
  decide +kernel

private def allowance_11 (u : ℕ) : ℕ :=
  nominal 11 u

private theorem bound_11 (u : ℕ) :
    (CJ0.blockMatrix source 11 ((u : ℤ)-24)).rank ≤ allowance_11 u := by
  unfold allowance_11
  exact (block_rank_le 11 _).trans (rank_le_nominal 11 _)

theorem grade_11 : (∑ u ∈ Finset.range (81-11), (CJ0.blockMatrix source 11 ((u : ℤ)-24)).rank) ≤ 3542 := by
  refine (Finset.sum_le_sum fun u _ => bound_11 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_11)]
  decide +kernel

private def allowance_12 (u : ℕ) : ℕ :=
  nominal 12 u

private theorem bound_12 (u : ℕ) :
    (CJ0.blockMatrix source 12 ((u : ℤ)-24)).rank ≤ allowance_12 u := by
  unfold allowance_12
  exact (block_rank_le 12 _).trans (rank_le_nominal 12 _)

theorem grade_12 : (∑ u ∈ Finset.range (81-12), (CJ0.blockMatrix source 12 ((u : ℤ)-24)).rank) ≤ 3960 := by
  refine (Finset.sum_le_sum fun u _ => bound_12 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_12)]
  decide +kernel

private def matrix_13_45 : CJ1.Block where
  bank := .leftLow
  cap := 98
  free := [(11, 0)]
  vectors := [
    [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_13_45 : (CJ0.blockMatrix source 13 ((45 : ℤ)-24)).rank ≤ 98 :=
  Fast.cell (z := matrix_13_45) (Fast.bands [(0, 0, 11), (1, 1, 11), (2, 2, 11), (3, 3, 11), (4, 4, 10), (5, 5, 9), (6, 6, 8), (7, 7, 7), (8, 8, 6), (9, 9, 5), (10, 10, 4), (11, 11, 3), (12, 12, 2), (13, 13, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_13 (u : ℕ) : ℕ :=
  match u with
  | 45 => 98
  | u => nominal 13 u

private theorem bound_13 (u : ℕ) :
    (CJ0.blockMatrix source 13 ((u : ℤ)-24)).rank ≤ allowance_13 u := by
  unfold allowance_13
  split
  · exact cell_13_45
  · exact (block_rank_le 13 _).trans (rank_le_nominal 13 _)

theorem grade_13 : (∑ u ∈ Finset.range (81-13), (CJ0.blockMatrix source 13 ((u : ℤ)-24)).rank) ≤ 4356 := by
  refine (Finset.sum_le_sum fun u _ => bound_13 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_13)]
  decide +kernel

private def matrix_14_43 : CJ1.Block where
  bank := .rightLow
  cap := 109
  free := [(14, 0)]
  vectors := [
    [[1, 10, 45, 120, 210, 252, 210, 120, 45, 10, 1], [2130706419, 2130706303, 2130705893, 2130705113, 2130704333, 2130704165, 2130704753, 2130705593, 2130706163, 2130706383, 2130706429], [91, 780, 2970, 6600, 9450, 9072, 5880, 2520, 675, 100, 6], [2130706069, 2130703573, 2130696533, 2130686633, 2130681233, 2130685265, 2130694673, 2130702233, 2130705533, 2130706333, 2130706429], [1001, 7150, 22275, 39600, 44100, 31752, 14700, 4200, 675, 50, 1], [2130704431, 2130693563, 2130670793, 2130650993, 2130653513, 2130674681, 2130694673, 2130703913, 2130706163, 2130706423], [3003, 17160, 41580, 55440, 44100, 21168, 5880, 840, 45], [2130703001, 2130689273, 2130670793, 2130666833, 2130681233, 2130697361, 2130704753, 2130706313], [3003, 12870, 22275, 19800, 9450, 2268, 210], [2130704431, 2130699283, 2130696533, 2130699833, 2130704333, 2130706181], [1001, 2860, 2970, 1320, 210], [2130706069, 2130705653, 2130705893, 2130706313], [91, 130, 45], [2130706419, 2130706423], [1]]
  ]
private theorem cell_14_43 : (CJ0.blockMatrix source 14 ((43 : ℤ)-24)).rank ≤ 109 :=
  Fast.cell (z := matrix_14_43) (Fast.bands [(0, 0, 15), (1, 0, 14), (2, 0, 13), (3, 0, 12), (4, 0, 11), (5, 0, 10), (6, 0, 9), (7, 0, 8), (8, 0, 7), (9, 0, 6), (10, 1, 4), (11, 2, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_14_44 : CJ1.Block where
  bank := .leftLow
  cap := 107
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_14_44 : (CJ0.blockMatrix source 14 ((44 : ℤ)-24)).rank ≤ 107 :=
  Fast.cell (z := matrix_14_44) (Fast.bands [(0, 0, 11), (1, 1, 11), (2, 2, 11), (3, 3, 11), (4, 4, 11), (5, 5, 10), (6, 6, 9), (7, 7, 8), (8, 8, 7), (9, 9, 6), (10, 10, 5), (11, 11, 4), (12, 12, 3), (13, 13, 2), (14, 14, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_14 (u : ℕ) : ℕ :=
  match u with
  | 43 => 109
  | 44 => 107
  | u => nominal 14 u

private theorem bound_14 (u : ℕ) :
    (CJ0.blockMatrix source 14 ((u : ℤ)-24)).rank ≤ allowance_14 u := by
  unfold allowance_14
  split
  · exact cell_14_43
  · exact cell_14_44
  · exact (block_rank_le 14 _).trans (rank_le_nominal 14 _)

theorem grade_14 : (∑ u ∈ Finset.range (81-14), (CJ0.blockMatrix source 14 ((u : ℤ)-24)).rank) ≤ 4730 := by
  refine (Finset.sum_le_sum fun u _ => bound_14 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_14)]
  decide +kernel

private def matrix_15_42 : CJ1.Block where
  bank := .leftLow
  cap := 118
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 12], [0, 0, 0, 11], [0, 0, 0, 10], [0, 0, 0, 9], [0, 0, 0, 8], [0, 0, 0, 7], [0, 0, 0, 6], [0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_15_42 : (CJ0.blockMatrix source 15 ((42 : ℤ)-24)).rank ≤ 118 :=
  Fast.cell (z := matrix_15_42) (Fast.bands [(0, 0, 10), (1, 1, 11), (2, 2, 11), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 10), (7, 7, 9), (8, 8, 8), (9, 9, 7), (10, 10, 6), (11, 11, 5), (12, 12, 4), (13, 13, 3), (14, 14, 2), (15, 15, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_15_43 : CJ1.Block where
  bank := .leftLow
  cap := 115
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_15_43 : (CJ0.blockMatrix source 15 ((43 : ℤ)-24)).rank ≤ 115 :=
  Fast.cell (z := matrix_15_43) (Fast.bands [(0, 0, 10), (1, 1, 11), (2, 2, 11), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 10), (7, 7, 9), (8, 8, 8), (9, 9, 7), (10, 10, 6), (11, 11, 5), (12, 12, 4), (13, 13, 3), (14, 14, 2), (15, 15, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_15 (u : ℕ) : ℕ :=
  match u with
  | 42 => 118
  | 43 => 115
  | u => nominal 15 u

private theorem bound_15 (u : ℕ) :
    (CJ0.blockMatrix source 15 ((u : ℤ)-24)).rank ≤ allowance_15 u := by
  unfold allowance_15
  split
  · exact cell_15_42
  · exact cell_15_43
  · exact (block_rank_le 15 _).trans (rank_le_nominal 15 _)

theorem grade_15 : (∑ u ∈ Finset.range (81-15), (CJ0.blockMatrix source 15 ((u : ℤ)-24)).rank) ≤ 5040 := by
  refine (Finset.sum_le_sum fun u _ => bound_15 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_15)]
  decide +kernel

private def matrix_16_41 : CJ1.Block where
  bank := .leftLow
  cap := 126
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 12], [0, 0, 0, 0, 11], [0, 0, 0, 0, 10], [0, 0, 0, 0, 9], [0, 0, 0, 0, 8], [0, 0, 0, 0, 7], [0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_16_41 : (CJ0.blockMatrix source 16 ((41 : ℤ)-24)).rank ≤ 126 :=
  Fast.cell (z := matrix_16_41) (Fast.bands [(0, 0, 9), (1, 1, 10), (2, 2, 11), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 10), (8, 8, 9), (9, 9, 8), (10, 10, 7), (11, 11, 6), (12, 12, 5), (13, 13, 4), (14, 14, 3), (15, 15, 2), (16, 16, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_16_42 : CJ1.Block where
  bank := .leftLow
  cap := 122
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_16_42 : (CJ0.blockMatrix source 16 ((42 : ℤ)-24)).rank ≤ 122 :=
  Fast.cell (z := matrix_16_42) (Fast.bands [(0, 0, 9), (1, 1, 10), (2, 2, 11), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 10), (8, 8, 9), (9, 9, 8), (10, 10, 7), (11, 11, 6), (12, 12, 5), (13, 13, 4), (14, 14, 3), (15, 15, 2), (16, 16, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_16 (u : ℕ) : ℕ :=
  match u with
  | 41 => 126
  | 42 => 122
  | u => nominal 16 u

private theorem bound_16 (u : ℕ) :
    (CJ0.blockMatrix source 16 ((u : ℤ)-24)).rank ≤ allowance_16 u := by
  unfold allowance_16
  split
  · exact cell_16_41
  · exact cell_16_42
  · exact (block_rank_le 16 _).trans (rank_le_nominal 16 _)

theorem grade_16 : (∑ u ∈ Finset.range (81-16), (CJ0.blockMatrix source 16 ((u : ℤ)-24)).rank) ≤ 5289 := by
  refine (Finset.sum_le_sum fun u _ => bound_16 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_16)]
  decide +kernel

private def matrix_17_40 : CJ1.Block where
  bank := .leftLow
  cap := 133
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_17_40 : (CJ0.blockMatrix source 17 ((40 : ℤ)-24)).rank ≤ 133 :=
  Fast.cell (z := matrix_17_40) (Fast.bands [(0, 0, 8), (1, 1, 9), (2, 2, 10), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 10), (9, 9, 9), (10, 10, 8), (11, 11, 7), (12, 12, 6), (13, 13, 5), (14, 14, 4), (15, 15, 3), (16, 16, 2), (17, 17, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_17_41 : CJ1.Block where
  bank := .leftLow
  cap := 128
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_17_41 : (CJ0.blockMatrix source 17 ((41 : ℤ)-24)).rank ≤ 128 :=
  Fast.cell (z := matrix_17_41) (Fast.bands [(0, 0, 8), (1, 1, 9), (2, 2, 10), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 10), (9, 9, 9), (10, 10, 8), (11, 11, 7), (12, 12, 6), (13, 13, 5), (14, 14, 4), (15, 15, 3), (16, 16, 2), (17, 17, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_17 (u : ℕ) : ℕ :=
  match u with
  | 40 => 133
  | 41 => 128
  | u => nominal 17 u

private theorem bound_17 (u : ℕ) :
    (CJ0.blockMatrix source 17 ((u : ℤ)-24)).rank ≤ allowance_17 u := by
  unfold allowance_17
  split
  · exact cell_17_40
  · exact cell_17_41
  · exact (block_rank_le 17 _).trans (rank_le_nominal 17 _)

theorem grade_17 : (∑ u ∈ Finset.range (81-17), (CJ0.blockMatrix source 17 ((u : ℤ)-24)).rank) ≤ 5480 := by
  refine (Finset.sum_le_sum fun u _ => bound_17 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_17)]
  decide +kernel

private def matrix_18_39 : CJ1.Block where
  bank := .leftLow
  cap := 139
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_18_39 : (CJ0.blockMatrix source 18 ((39 : ℤ)-24)).rank ≤ 139 :=
  Fast.cell (z := matrix_18_39) (Fast.bands [(0, 0, 7), (1, 1, 8), (2, 2, 9), (3, 3, 10), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 11), (9, 9, 10), (10, 10, 9), (11, 11, 8), (12, 12, 7), (13, 13, 6), (14, 14, 5), (15, 15, 4), (16, 16, 3), (17, 17, 2), (18, 18, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_18_40 : CJ1.Block where
  bank := .leftLow
  cap := 133
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_18_40 : (CJ0.blockMatrix source 18 ((40 : ℤ)-24)).rank ≤ 133 :=
  Fast.cell (z := matrix_18_40) (Fast.bands [(0, 0, 7), (1, 1, 8), (2, 2, 9), (3, 3, 10), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 11), (9, 9, 10), (10, 10, 9), (11, 11, 8), (12, 12, 7), (13, 13, 6), (14, 14, 5), (15, 15, 4), (16, 16, 3), (17, 17, 2), (18, 18, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_18 (u : ℕ) : ℕ :=
  match u with
  | 39 => 139
  | 40 => 133
  | u => nominal 18 u

private theorem bound_18 (u : ℕ) :
    (CJ0.blockMatrix source 18 ((u : ℤ)-24)).rank ≤ allowance_18 u := by
  unfold allowance_18
  split
  · exact cell_18_39
  · exact cell_18_40
  · exact (block_rank_le 18 _).trans (rank_le_nominal 18 _)

theorem grade_18 : (∑ u ∈ Finset.range (81-18), (CJ0.blockMatrix source 18 ((u : ℤ)-24)).rank) ≤ 5616 := by
  refine (Finset.sum_le_sum fun u _ => bound_18 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_18)]
  decide +kernel

private def matrix_19_38 : CJ1.Block where
  bank := .leftLow
  cap := 144
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_19_38 : (CJ0.blockMatrix source 19 ((38 : ℤ)-24)).rank ≤ 144 :=
  Fast.cell (z := matrix_19_38) (Fast.bands [(0, 0, 6), (1, 1, 7), (2, 2, 8), (3, 3, 9), (4, 4, 10), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 11), (9, 9, 11), (10, 10, 10), (11, 11, 9), (12, 12, 8), (13, 13, 7), (14, 14, 6), (15, 15, 5), (16, 16, 4), (17, 17, 3), (18, 18, 2), (19, 19, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_19_39 : CJ1.Block where
  bank := .leftLow
  cap := 137
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_19_39 : (CJ0.blockMatrix source 19 ((39 : ℤ)-24)).rank ≤ 137 :=
  Fast.cell (z := matrix_19_39) (Fast.bands [(0, 0, 6), (1, 1, 7), (2, 2, 8), (3, 3, 9), (4, 4, 10), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 11), (9, 9, 11), (10, 10, 10), (11, 11, 9), (12, 12, 8), (13, 13, 7), (14, 14, 6), (15, 15, 5), (16, 16, 4), (17, 17, 3), (18, 18, 2), (19, 19, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_19 (u : ℕ) : ℕ :=
  match u with
  | 38 => 144
  | 39 => 137
  | u => nominal 19 u

private theorem bound_19 (u : ℕ) :
    (CJ0.blockMatrix source 19 ((u : ℤ)-24)).rank ≤ allowance_19 u := by
  unfold allowance_19
  split
  · exact cell_19_38
  · exact cell_19_39
  · exact (block_rank_le 19 _).trans (rank_le_nominal 19 _)

theorem grade_19 : (∑ u ∈ Finset.range (81-19), (CJ0.blockMatrix source 19 ((u : ℤ)-24)).rank) ≤ 5700 := by
  refine (Finset.sum_le_sum fun u _ => bound_19 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_19)]
  decide +kernel

end Front6960ListBank

end Merged6967_R6960Front6960ListCells1

section Merged6967_R6960Front6960ListCells2
set_option Elab.async false


set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6960ListBank
open scoped BigOperators

private def matrix_20_37 : CJ1.Block where
  bank := .leftLow
  cap := 148
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_20_37 : (CJ0.blockMatrix source 20 ((37 : ℤ)-24)).rank ≤ 148 :=
  Fast.cell (z := matrix_20_37) (Fast.bands [(0, 0, 5), (1, 1, 6), (2, 2, 7), (3, 3, 8), (4, 4, 9), (5, 5, 10), (6, 6, 11), (7, 7, 11), (8, 8, 11), (9, 9, 11), (10, 10, 11), (11, 11, 10), (12, 12, 9), (13, 13, 8), (14, 14, 7), (15, 15, 6), (16, 16, 5), (17, 17, 4), (18, 18, 3), (19, 19, 2), (20, 20, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_20_38 : CJ1.Block where
  bank := .leftLow
  cap := 140
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_20_38 : (CJ0.blockMatrix source 20 ((38 : ℤ)-24)).rank ≤ 140 :=
  Fast.cell (z := matrix_20_38) (Fast.bands [(0, 0, 5), (1, 1, 6), (2, 2, 7), (3, 3, 8), (4, 4, 9), (5, 5, 10), (6, 6, 11), (7, 7, 11), (8, 8, 11), (9, 9, 11), (10, 10, 11), (11, 11, 10), (12, 12, 9), (13, 13, 8), (14, 14, 7), (15, 15, 6), (16, 16, 5), (17, 17, 4), (18, 18, 3), (19, 19, 2), (20, 20, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_20 (u : ℕ) : ℕ :=
  match u with
  | 37 => 148
  | 38 => 140
  | u => nominal 20 u

private theorem bound_20 (u : ℕ) :
    (CJ0.blockMatrix source 20 ((u : ℤ)-24)).rank ≤ allowance_20 u := by
  unfold allowance_20
  split
  · exact cell_20_37
  · exact cell_20_38
  · exact (block_rank_le 20 _).trans (rank_le_nominal 20 _)

theorem grade_20 : (∑ u ∈ Finset.range (81-20), (CJ0.blockMatrix source 20 ((u : ℤ)-24)).rank) ≤ 5735 := by
  refine (Finset.sum_le_sum fun u _ => bound_20 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_20)]
  decide +kernel

private def matrix_21_36 : CJ1.Block where
  bank := .leftLow
  cap := 151
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_21_36 : (CJ0.blockMatrix source 21 ((36 : ℤ)-24)).rank ≤ 151 :=
  Fast.cell (z := matrix_21_36) (Fast.bands [(0, 0, 4), (1, 1, 5), (2, 2, 6), (3, 3, 7), (4, 4, 8), (5, 5, 9), (6, 6, 10), (7, 7, 11), (8, 8, 11), (9, 9, 11), (10, 10, 11), (11, 11, 11), (12, 12, 10), (13, 13, 9), (14, 14, 8), (15, 15, 7), (16, 16, 6), (17, 17, 5), (18, 18, 4), (19, 19, 3), (20, 20, 2), (21, 21, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_21_37 : CJ1.Block where
  bank := .leftLow
  cap := 142
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_21_37 : (CJ0.blockMatrix source 21 ((37 : ℤ)-24)).rank ≤ 142 :=
  Fast.cell (z := matrix_21_37) (Fast.bands [(0, 0, 4), (1, 1, 5), (2, 2, 6), (3, 3, 7), (4, 4, 8), (5, 5, 9), (6, 6, 10), (7, 7, 11), (8, 8, 11), (9, 9, 11), (10, 10, 11), (11, 11, 11), (12, 12, 10), (13, 13, 9), (14, 14, 8), (15, 15, 7), (16, 16, 6), (17, 17, 5), (18, 18, 4), (19, 19, 3), (20, 20, 2), (21, 21, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_21 (u : ℕ) : ℕ :=
  match u with
  | 36 => 151
  | 37 => 142
  | u => nominal 21 u

private theorem bound_21 (u : ℕ) :
    (CJ0.blockMatrix source 21 ((u : ℤ)-24)).rank ≤ allowance_21 u := by
  unfold allowance_21
  split
  · exact cell_21_36
  · exact cell_21_37
  · exact (block_rank_le 21 _).trans (rank_le_nominal 21 _)

theorem grade_21 : (∑ u ∈ Finset.range (81-21), (CJ0.blockMatrix source 21 ((u : ℤ)-24)).rank) ≤ 5724 := by
  refine (Finset.sum_le_sum fun u _ => bound_21 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_21)]
  decide +kernel

private def matrix_22_35 : CJ1.Block where
  bank := .leftLow
  cap := 153
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_22_35 : (CJ0.blockMatrix source 22 ((35 : ℤ)-24)).rank ≤ 153 :=
  Fast.cell (z := matrix_22_35) (Fast.bands [(0, 0, 3), (1, 1, 4), (2, 2, 5), (3, 3, 6), (4, 4, 7), (5, 5, 8), (6, 6, 9), (7, 7, 10), (8, 8, 11), (9, 9, 11), (10, 10, 11), (11, 11, 11), (12, 12, 11), (13, 13, 10), (14, 14, 9), (15, 15, 8), (16, 16, 7), (17, 17, 6), (18, 18, 5), (19, 19, 4), (20, 20, 3), (21, 21, 2), (22, 22, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_22_36 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_22_36 : (CJ0.blockMatrix source 22 ((36 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_22_36) (Fast.bands [(0, 0, 3), (1, 1, 4), (2, 2, 5), (3, 3, 6), (4, 4, 7), (5, 5, 8), (6, 6, 9), (7, 7, 10), (8, 8, 11), (9, 9, 11), (10, 10, 11), (11, 11, 11), (12, 12, 11), (13, 13, 10), (14, 14, 9), (15, 15, 8), (16, 16, 7), (17, 17, 6), (18, 18, 5), (19, 19, 4), (20, 20, 3), (21, 21, 2), (22, 22, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_22 (u : ℕ) : ℕ :=
  match u with
  | 35 => 153
  | 36 => 143
  | u => nominal 22 u

private theorem bound_22 (u : ℕ) :
    (CJ0.blockMatrix source 22 ((u : ℤ)-24)).rank ≤ allowance_22 u := by
  unfold allowance_22
  split
  · exact cell_22_35
  · exact cell_22_36
  · exact (block_rank_le 22 _).trans (rank_le_nominal 22 _)

theorem grade_22 : (∑ u ∈ Finset.range (81-22), (CJ0.blockMatrix source 22 ((u : ℤ)-24)).rank) ≤ 5670 := by
  refine (Finset.sum_le_sum fun u _ => bound_22 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_22)]
  decide +kernel

private def matrix_23_34 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_23_34 : (CJ0.blockMatrix source 23 ((34 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_23_34) (Fast.bands [(0, 0, 2), (1, 1, 3), (2, 2, 4), (3, 3, 5), (4, 4, 6), (5, 5, 7), (6, 6, 8), (7, 7, 9), (8, 8, 10), (9, 9, 11), (10, 10, 11), (11, 11, 11), (12, 12, 11), (13, 13, 11), (14, 14, 10), (15, 15, 9), (16, 16, 8), (17, 17, 7), (18, 18, 6), (19, 19, 5), (20, 20, 4), (21, 21, 3), (22, 22, 2), (23, 23, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_23_35 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_23_35 : (CJ0.blockMatrix source 23 ((35 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_23_35) (Fast.bands [(0, 0, 2), (1, 1, 3), (2, 2, 4), (3, 3, 5), (4, 4, 6), (5, 5, 7), (6, 6, 8), (7, 7, 9), (8, 8, 10), (9, 9, 11), (10, 10, 11), (11, 11, 11), (12, 12, 11), (13, 13, 11), (14, 14, 10), (15, 15, 9), (16, 16, 8), (17, 17, 7), (18, 18, 6), (19, 19, 5), (20, 20, 4), (21, 21, 3), (22, 22, 2), (23, 23, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_23 (u : ℕ) : ℕ :=
  match u with
  | 34 => 154
  | 35 => 143
  | u => nominal 23 u

private theorem bound_23 (u : ℕ) :
    (CJ0.blockMatrix source 23 ((u : ℤ)-24)).rank ≤ allowance_23 u := by
  unfold allowance_23
  split
  · exact cell_23_34
  · exact cell_23_35
  · exact (block_rank_le 23 _).trans (rank_le_nominal 23 _)

theorem grade_23 : (∑ u ∈ Finset.range (81-23), (CJ0.blockMatrix source 23 ((u : ℤ)-24)).rank) ≤ 5576 := by
  refine (Finset.sum_le_sum fun u _ => bound_23 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_23)]
  decide +kernel

private def matrix_24_33 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_24_33 : (CJ0.blockMatrix source 24 ((33 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_24_33) (Fast.bands [(0, 0, 1), (1, 1, 2), (2, 2, 3), (3, 3, 4), (4, 4, 5), (5, 5, 6), (6, 6, 7), (7, 7, 8), (8, 8, 9), (9, 9, 10), (10, 10, 11), (11, 11, 11), (12, 12, 11), (13, 13, 11), (14, 14, 11), (15, 15, 10), (16, 16, 9), (17, 17, 8), (18, 18, 7), (19, 19, 6), (20, 20, 5), (21, 21, 4), (22, 22, 3), (23, 23, 2), (24, 24, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_24_34 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_24_34 : (CJ0.blockMatrix source 24 ((34 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_24_34) (Fast.bands [(0, 0, 1), (1, 1, 2), (2, 2, 3), (3, 3, 4), (4, 4, 5), (5, 5, 6), (6, 6, 7), (7, 7, 8), (8, 8, 9), (9, 9, 10), (10, 10, 11), (11, 11, 11), (12, 12, 11), (13, 13, 11), (14, 14, 11), (15, 15, 10), (16, 16, 9), (17, 17, 8), (18, 18, 7), (19, 19, 6), (20, 20, 5), (21, 21, 4), (22, 22, 3), (23, 23, 2), (24, 24, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_24 (u : ℕ) : ℕ :=
  match u with
  | 33 => 154
  | 34 => 143
  | u => nominal 24 u

private theorem bound_24 (u : ℕ) :
    (CJ0.blockMatrix source 24 ((u : ℤ)-24)).rank ≤ allowance_24 u := by
  unfold allowance_24
  split
  · exact cell_24_33
  · exact cell_24_34
  · exact (block_rank_le 24 _).trans (rank_le_nominal 24 _)

theorem grade_24 : (∑ u ∈ Finset.range (81-24), (CJ0.blockMatrix source 24 ((u : ℤ)-24)).rank) ≤ 5445 := by
  refine (Finset.sum_le_sum fun u _ => bound_24 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_24)]
  decide +kernel

private def matrix_25_32 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_25_32 : (CJ0.blockMatrix source 25 ((32 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_25_32) (Fast.bands [(1, 1, 1), (2, 2, 2), (3, 3, 3), (4, 4, 4), (5, 5, 5), (6, 6, 6), (7, 7, 7), (8, 8, 8), (9, 9, 9), (10, 10, 10), (11, 11, 11), (12, 12, 11), (13, 13, 11), (14, 14, 11), (15, 15, 11), (16, 16, 10), (17, 17, 9), (18, 18, 8), (19, 19, 7), (20, 20, 6), (21, 21, 5), (22, 22, 4), (23, 23, 3), (24, 24, 2), (25, 25, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_25_33 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_25_33 : (CJ0.blockMatrix source 25 ((33 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_25_33) (Fast.bands [(1, 1, 1), (2, 2, 2), (3, 3, 3), (4, 4, 4), (5, 5, 5), (6, 6, 6), (7, 7, 7), (8, 8, 8), (9, 9, 9), (10, 10, 10), (11, 11, 11), (12, 12, 11), (13, 13, 11), (14, 14, 11), (15, 15, 11), (16, 16, 10), (17, 17, 9), (18, 18, 8), (19, 19, 7), (20, 20, 6), (21, 21, 5), (22, 22, 4), (23, 23, 3), (24, 24, 2), (25, 25, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_25 (u : ℕ) : ℕ :=
  match u with
  | 32 => 154
  | 33 => 143
  | u => nominal 25 u

private theorem bound_25 (u : ℕ) :
    (CJ0.blockMatrix source 25 ((u : ℤ)-24)).rank ≤ allowance_25 u := by
  unfold allowance_25
  split
  · exact cell_25_32
  · exact cell_25_33
  · exact (block_rank_le 25 _).trans (rank_le_nominal 25 _)

theorem grade_25 : (∑ u ∈ Finset.range (81-25), (CJ0.blockMatrix source 25 ((u : ℤ)-24)).rank) ≤ 5280 := by
  refine (Finset.sum_le_sum fun u _ => bound_25 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_25)]
  decide +kernel

private def matrix_26_31 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_26_31 : (CJ0.blockMatrix source 26 ((31 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_26_31) (Fast.bands [(2, 2, 1), (3, 3, 2), (4, 4, 3), (5, 5, 4), (6, 6, 5), (7, 7, 6), (8, 8, 7), (9, 9, 8), (10, 10, 9), (11, 11, 10), (12, 12, 11), (13, 13, 11), (14, 14, 11), (15, 15, 11), (16, 16, 11), (17, 17, 10), (18, 18, 9), (19, 19, 8), (20, 20, 7), (21, 21, 6), (22, 22, 5), (23, 23, 4), (24, 24, 3), (25, 25, 2), (26, 26, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_26_32 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_26_32 : (CJ0.blockMatrix source 26 ((32 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_26_32) (Fast.bands [(2, 2, 1), (3, 3, 2), (4, 4, 3), (5, 5, 4), (6, 6, 5), (7, 7, 6), (8, 8, 7), (9, 9, 8), (10, 10, 9), (11, 11, 10), (12, 12, 11), (13, 13, 11), (14, 14, 11), (15, 15, 11), (16, 16, 11), (17, 17, 10), (18, 18, 9), (19, 19, 8), (20, 20, 7), (21, 21, 6), (22, 22, 5), (23, 23, 4), (24, 24, 3), (25, 25, 2), (26, 26, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_26 (u : ℕ) : ℕ :=
  match u with
  | 31 => 154
  | 32 => 143
  | u => nominal 26 u

private theorem bound_26 (u : ℕ) :
    (CJ0.blockMatrix source 26 ((u : ℤ)-24)).rank ≤ allowance_26 u := by
  unfold allowance_26
  split
  · exact cell_26_31
  · exact cell_26_32
  · exact (block_rank_le 26 _).trans (rank_le_nominal 26 _)

theorem grade_26 : (∑ u ∈ Finset.range (81-26), (CJ0.blockMatrix source 26 ((u : ℤ)-24)).rank) ≤ 5115 := by
  refine (Finset.sum_le_sum fun u _ => bound_26 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_26)]
  decide +kernel

private def matrix_27_30 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_27_30 : (CJ0.blockMatrix source 27 ((30 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_27_30) (Fast.bands [(3, 3, 1), (4, 4, 2), (5, 5, 3), (6, 6, 4), (7, 7, 5), (8, 8, 6), (9, 9, 7), (10, 10, 8), (11, 11, 9), (12, 12, 10), (13, 13, 11), (14, 14, 11), (15, 15, 11), (16, 16, 11), (17, 17, 11), (18, 18, 10), (19, 19, 9), (20, 20, 8), (21, 21, 7), (22, 22, 6), (23, 23, 5), (24, 24, 4), (25, 25, 3), (26, 26, 2), (27, 27, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_27_31 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_27_31 : (CJ0.blockMatrix source 27 ((31 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_27_31) (Fast.bands [(3, 3, 1), (4, 4, 2), (5, 5, 3), (6, 6, 4), (7, 7, 5), (8, 8, 6), (9, 9, 7), (10, 10, 8), (11, 11, 9), (12, 12, 10), (13, 13, 11), (14, 14, 11), (15, 15, 11), (16, 16, 11), (17, 17, 11), (18, 18, 10), (19, 19, 9), (20, 20, 8), (21, 21, 7), (22, 22, 6), (23, 23, 5), (24, 24, 4), (25, 25, 3), (26, 26, 2), (27, 27, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_27 (u : ℕ) : ℕ :=
  match u with
  | 30 => 154
  | 31 => 143
  | u => nominal 27 u

private theorem bound_27 (u : ℕ) :
    (CJ0.blockMatrix source 27 ((u : ℤ)-24)).rank ≤ allowance_27 u := by
  unfold allowance_27
  split
  · exact cell_27_30
  · exact cell_27_31
  · exact (block_rank_le 27 _).trans (rank_le_nominal 27 _)

theorem grade_27 : (∑ u ∈ Finset.range (81-27), (CJ0.blockMatrix source 27 ((u : ℤ)-24)).rank) ≤ 4950 := by
  refine (Finset.sum_le_sum fun u _ => bound_27 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_27)]
  decide +kernel

private def matrix_28_29 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_28_29 : (CJ0.blockMatrix source 28 ((29 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_28_29) (Fast.bands [(4, 4, 1), (5, 5, 2), (6, 6, 3), (7, 7, 4), (8, 8, 5), (9, 9, 6), (10, 10, 7), (11, 11, 8), (12, 12, 9), (13, 13, 10), (14, 14, 11), (15, 15, 11), (16, 16, 11), (17, 17, 11), (18, 18, 11), (19, 19, 10), (20, 20, 9), (21, 21, 8), (22, 22, 7), (23, 23, 6), (24, 24, 5), (25, 25, 4), (26, 26, 3), (27, 27, 2), (28, 28, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_28_30 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_28_30 : (CJ0.blockMatrix source 28 ((30 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_28_30) (Fast.bands [(4, 4, 1), (5, 5, 2), (6, 6, 3), (7, 7, 4), (8, 8, 5), (9, 9, 6), (10, 10, 7), (11, 11, 8), (12, 12, 9), (13, 13, 10), (14, 14, 11), (15, 15, 11), (16, 16, 11), (17, 17, 11), (18, 18, 11), (19, 19, 10), (20, 20, 9), (21, 21, 8), (22, 22, 7), (23, 23, 6), (24, 24, 5), (25, 25, 4), (26, 26, 3), (27, 27, 2), (28, 28, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_28 (u : ℕ) : ℕ :=
  match u with
  | 29 => 154
  | 30 => 143
  | u => nominal 28 u

private theorem bound_28 (u : ℕ) :
    (CJ0.blockMatrix source 28 ((u : ℤ)-24)).rank ≤ allowance_28 u := by
  unfold allowance_28
  split
  · exact cell_28_29
  · exact cell_28_30
  · exact (block_rank_le 28 _).trans (rank_le_nominal 28 _)

theorem grade_28 : (∑ u ∈ Finset.range (81-28), (CJ0.blockMatrix source 28 ((u : ℤ)-24)).rank) ≤ 4785 := by
  refine (Finset.sum_le_sum fun u _ => bound_28 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_28)]
  decide +kernel

private def matrix_29_28 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_29_28 : (CJ0.blockMatrix source 29 ((28 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_29_28) (Fast.bands [(5, 5, 1), (6, 6, 2), (7, 7, 3), (8, 8, 4), (9, 9, 5), (10, 10, 6), (11, 11, 7), (12, 12, 8), (13, 13, 9), (14, 14, 10), (15, 15, 11), (16, 16, 11), (17, 17, 11), (18, 18, 11), (19, 19, 11), (20, 20, 10), (21, 21, 9), (22, 22, 8), (23, 23, 7), (24, 24, 6), (25, 25, 5), (26, 26, 4), (27, 27, 3), (28, 28, 2), (29, 29, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_29_29 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_29_29 : (CJ0.blockMatrix source 29 ((29 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_29_29) (Fast.bands [(5, 5, 1), (6, 6, 2), (7, 7, 3), (8, 8, 4), (9, 9, 5), (10, 10, 6), (11, 11, 7), (12, 12, 8), (13, 13, 9), (14, 14, 10), (15, 15, 11), (16, 16, 11), (17, 17, 11), (18, 18, 11), (19, 19, 11), (20, 20, 10), (21, 21, 9), (22, 22, 8), (23, 23, 7), (24, 24, 6), (25, 25, 5), (26, 26, 4), (27, 27, 3), (28, 28, 2), (29, 29, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_29 (u : ℕ) : ℕ :=
  match u with
  | 28 => 154
  | 29 => 143
  | u => nominal 29 u

private theorem bound_29 (u : ℕ) :
    (CJ0.blockMatrix source 29 ((u : ℤ)-24)).rank ≤ allowance_29 u := by
  unfold allowance_29
  split
  · exact cell_29_28
  · exact cell_29_29
  · exact (block_rank_le 29 _).trans (rank_le_nominal 29 _)

theorem grade_29 : (∑ u ∈ Finset.range (81-29), (CJ0.blockMatrix source 29 ((u : ℤ)-24)).rank) ≤ 4620 := by
  refine (Finset.sum_le_sum fun u _ => bound_29 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_29)]
  decide +kernel

end Front6960ListBank

end Merged6967_R6960Front6960ListCells2

section Merged6967_R6960Front6960ListCells3
set_option Elab.async false


set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6960ListBank
open scoped BigOperators

private def matrix_30_27 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_30_27 : (CJ0.blockMatrix source 30 ((27 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_30_27) (Fast.bands [(6, 6, 1), (7, 7, 2), (8, 8, 3), (9, 9, 4), (10, 10, 5), (11, 11, 6), (12, 12, 7), (13, 13, 8), (14, 14, 9), (15, 15, 10), (16, 16, 11), (17, 17, 11), (18, 18, 11), (19, 19, 11), (20, 20, 11), (21, 21, 10), (22, 22, 9), (23, 23, 8), (24, 24, 7), (25, 25, 6), (26, 26, 5), (27, 27, 4), (28, 28, 3), (29, 29, 2), (30, 30, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_30_28 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_30_28 : (CJ0.blockMatrix source 30 ((28 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_30_28) (Fast.bands [(6, 6, 1), (7, 7, 2), (8, 8, 3), (9, 9, 4), (10, 10, 5), (11, 11, 6), (12, 12, 7), (13, 13, 8), (14, 14, 9), (15, 15, 10), (16, 16, 11), (17, 17, 11), (18, 18, 11), (19, 19, 11), (20, 20, 11), (21, 21, 10), (22, 22, 9), (23, 23, 8), (24, 24, 7), (25, 25, 6), (26, 26, 5), (27, 27, 4), (28, 28, 3), (29, 29, 2), (30, 30, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_30 (u : ℕ) : ℕ :=
  match u with
  | 27 => 154
  | 28 => 143
  | u => nominal 30 u

private theorem bound_30 (u : ℕ) :
    (CJ0.blockMatrix source 30 ((u : ℤ)-24)).rank ≤ allowance_30 u := by
  unfold allowance_30
  split
  · exact cell_30_27
  · exact cell_30_28
  · exact (block_rank_le 30 _).trans (rank_le_nominal 30 _)

theorem grade_30 : (∑ u ∈ Finset.range (81-30), (CJ0.blockMatrix source 30 ((u : ℤ)-24)).rank) ≤ 4455 := by
  refine (Finset.sum_le_sum fun u _ => bound_30 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_30)]
  decide +kernel

private def matrix_31_26 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_31_26 : (CJ0.blockMatrix source 31 ((26 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_31_26) (Fast.bands [(7, 7, 1), (8, 8, 2), (9, 9, 3), (10, 10, 4), (11, 11, 5), (12, 12, 6), (13, 13, 7), (14, 14, 8), (15, 15, 9), (16, 16, 10), (17, 17, 11), (18, 18, 11), (19, 19, 11), (20, 20, 11), (21, 21, 11), (22, 22, 10), (23, 23, 9), (24, 24, 8), (25, 25, 7), (26, 26, 6), (27, 27, 5), (28, 28, 4), (29, 29, 3), (30, 30, 2), (31, 31, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_31_27 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_31_27 : (CJ0.blockMatrix source 31 ((27 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_31_27) (Fast.bands [(7, 7, 1), (8, 8, 2), (9, 9, 3), (10, 10, 4), (11, 11, 5), (12, 12, 6), (13, 13, 7), (14, 14, 8), (15, 15, 9), (16, 16, 10), (17, 17, 11), (18, 18, 11), (19, 19, 11), (20, 20, 11), (21, 21, 11), (22, 22, 10), (23, 23, 9), (24, 24, 8), (25, 25, 7), (26, 26, 6), (27, 27, 5), (28, 28, 4), (29, 29, 3), (30, 30, 2), (31, 31, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_31 (u : ℕ) : ℕ :=
  match u with
  | 26 => 154
  | 27 => 143
  | u => nominal 31 u

private theorem bound_31 (u : ℕ) :
    (CJ0.blockMatrix source 31 ((u : ℤ)-24)).rank ≤ allowance_31 u := by
  unfold allowance_31
  split
  · exact cell_31_26
  · exact cell_31_27
  · exact (block_rank_le 31 _).trans (rank_le_nominal 31 _)

theorem grade_31 : (∑ u ∈ Finset.range (81-31), (CJ0.blockMatrix source 31 ((u : ℤ)-24)).rank) ≤ 4290 := by
  refine (Finset.sum_le_sum fun u _ => bound_31 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_31)]
  decide +kernel

private def matrix_32_25 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_32_25 : (CJ0.blockMatrix source 32 ((25 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_32_25) (Fast.bands [(8, 8, 1), (9, 9, 2), (10, 10, 3), (11, 11, 4), (12, 12, 5), (13, 13, 6), (14, 14, 7), (15, 15, 8), (16, 16, 9), (17, 17, 10), (18, 18, 11), (19, 19, 11), (20, 20, 11), (21, 21, 11), (22, 22, 11), (23, 23, 10), (24, 24, 9), (25, 25, 8), (26, 26, 7), (27, 27, 6), (28, 28, 5), (29, 29, 4), (30, 30, 3), (31, 31, 2), (32, 32, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_32_26 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_32_26 : (CJ0.blockMatrix source 32 ((26 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_32_26) (Fast.bands [(8, 8, 1), (9, 9, 2), (10, 10, 3), (11, 11, 4), (12, 12, 5), (13, 13, 6), (14, 14, 7), (15, 15, 8), (16, 16, 9), (17, 17, 10), (18, 18, 11), (19, 19, 11), (20, 20, 11), (21, 21, 11), (22, 22, 11), (23, 23, 10), (24, 24, 9), (25, 25, 8), (26, 26, 7), (27, 27, 6), (28, 28, 5), (29, 29, 4), (30, 30, 3), (31, 31, 2), (32, 32, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_32 (u : ℕ) : ℕ :=
  match u with
  | 25 => 154
  | 26 => 143
  | u => nominal 32 u

private theorem bound_32 (u : ℕ) :
    (CJ0.blockMatrix source 32 ((u : ℤ)-24)).rank ≤ allowance_32 u := by
  unfold allowance_32
  split
  · exact cell_32_25
  · exact cell_32_26
  · exact (block_rank_le 32 _).trans (rank_le_nominal 32 _)

theorem grade_32 : (∑ u ∈ Finset.range (81-32), (CJ0.blockMatrix source 32 ((u : ℤ)-24)).rank) ≤ 4125 := by
  refine (Finset.sum_le_sum fun u _ => bound_32 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_32)]
  decide +kernel

private def matrix_33_24 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_33_24 : (CJ0.blockMatrix source 33 ((24 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_33_24) (Fast.bands [(9, 9, 1), (10, 10, 2), (11, 11, 3), (12, 12, 4), (13, 13, 5), (14, 14, 6), (15, 15, 7), (16, 16, 8), (17, 17, 9), (18, 18, 10), (19, 19, 11), (20, 20, 11), (21, 21, 11), (22, 22, 11), (23, 23, 11), (24, 24, 10), (25, 25, 9), (26, 26, 8), (27, 27, 7), (28, 28, 6), (29, 29, 5), (30, 30, 4), (31, 31, 3), (32, 32, 2), (33, 33, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_33_25 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_33_25 : (CJ0.blockMatrix source 33 ((25 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_33_25) (Fast.bands [(9, 9, 1), (10, 10, 2), (11, 11, 3), (12, 12, 4), (13, 13, 5), (14, 14, 6), (15, 15, 7), (16, 16, 8), (17, 17, 9), (18, 18, 10), (19, 19, 11), (20, 20, 11), (21, 21, 11), (22, 22, 11), (23, 23, 11), (24, 24, 10), (25, 25, 9), (26, 26, 8), (27, 27, 7), (28, 28, 6), (29, 29, 5), (30, 30, 4), (31, 31, 3), (32, 32, 2), (33, 33, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_33 (u : ℕ) : ℕ :=
  match u with
  | 24 => 154
  | 25 => 143
  | u => nominal 33 u

private theorem bound_33 (u : ℕ) :
    (CJ0.blockMatrix source 33 ((u : ℤ)-24)).rank ≤ allowance_33 u := by
  unfold allowance_33
  split
  · exact cell_33_24
  · exact cell_33_25
  · exact (block_rank_le 33 _).trans (rank_le_nominal 33 _)

theorem grade_33 : (∑ u ∈ Finset.range (81-33), (CJ0.blockMatrix source 33 ((u : ℤ)-24)).rank) ≤ 3960 := by
  refine (Finset.sum_le_sum fun u _ => bound_33 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_33)]
  decide +kernel

private def matrix_34_23 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_34_23 : (CJ0.blockMatrix source 34 ((23 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_34_23) (Fast.bands [(10, 10, 1), (11, 11, 2), (12, 12, 3), (13, 13, 4), (14, 14, 5), (15, 15, 6), (16, 16, 7), (17, 17, 8), (18, 18, 9), (19, 19, 10), (20, 20, 11), (21, 21, 11), (22, 22, 11), (23, 23, 11), (24, 24, 11), (25, 25, 10), (26, 26, 9), (27, 27, 8), (28, 28, 7), (29, 29, 6), (30, 30, 5), (31, 31, 4), (32, 32, 3), (33, 33, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_34_24 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_34_24 : (CJ0.blockMatrix source 34 ((24 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_34_24) (Fast.bands [(10, 10, 1), (11, 11, 2), (12, 12, 3), (13, 13, 4), (14, 14, 5), (15, 15, 6), (16, 16, 7), (17, 17, 8), (18, 18, 9), (19, 19, 10), (20, 20, 11), (21, 21, 11), (22, 22, 11), (23, 23, 11), (24, 24, 11), (25, 25, 10), (26, 26, 9), (27, 27, 8), (28, 28, 7), (29, 29, 6), (30, 30, 5), (31, 31, 4), (32, 32, 3), (33, 33, 2), (34, 34, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_34 (u : ℕ) : ℕ :=
  match u with
  | 23 => 154
  | 24 => 143
  | u => nominal 34 u

private theorem bound_34 (u : ℕ) :
    (CJ0.blockMatrix source 34 ((u : ℤ)-24)).rank ≤ allowance_34 u := by
  unfold allowance_34
  split
  · exact cell_34_23
  · exact cell_34_24
  · exact (block_rank_le 34 _).trans (rank_le_nominal 34 _)

theorem grade_34 : (∑ u ∈ Finset.range (81-34), (CJ0.blockMatrix source 34 ((u : ℤ)-24)).rank) ≤ 3796 := by
  refine (Finset.sum_le_sum fun u _ => bound_34 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_34)]
  decide +kernel

private def matrix_35_22 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_35_22 : (CJ0.blockMatrix source 35 ((22 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_35_22) (Fast.bands [(11, 11, 1), (12, 12, 2), (13, 13, 3), (14, 14, 4), (15, 15, 5), (16, 16, 6), (17, 17, 7), (18, 18, 8), (19, 19, 9), (20, 20, 10), (21, 21, 11), (22, 22, 11), (23, 23, 11), (24, 24, 11), (25, 25, 11), (26, 26, 10), (27, 27, 9), (28, 28, 8), (29, 29, 7), (30, 30, 6), (31, 31, 5), (32, 32, 4), (33, 33, 3), (34, 35, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_35_23 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_35_23 : (CJ0.blockMatrix source 35 ((23 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_35_23) (Fast.bands [(11, 11, 1), (12, 12, 2), (13, 13, 3), (14, 14, 4), (15, 15, 5), (16, 16, 6), (17, 17, 7), (18, 18, 8), (19, 19, 9), (20, 20, 10), (21, 21, 11), (22, 22, 11), (23, 23, 11), (24, 24, 11), (25, 25, 11), (26, 26, 10), (27, 27, 9), (28, 28, 8), (29, 29, 7), (30, 30, 6), (31, 31, 5), (32, 32, 4), (33, 33, 3), (34, 34, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_35 (u : ℕ) : ℕ :=
  match u with
  | 22 => 154
  | 23 => 143
  | u => nominal 35 u

private theorem bound_35 (u : ℕ) :
    (CJ0.blockMatrix source 35 ((u : ℤ)-24)).rank ≤ allowance_35 u := by
  unfold allowance_35
  split
  · exact cell_35_22
  · exact cell_35_23
  · exact (block_rank_le 35 _).trans (rank_le_nominal 35 _)

theorem grade_35 : (∑ u ∈ Finset.range (81-35), (CJ0.blockMatrix source 35 ((u : ℤ)-24)).rank) ≤ 3633 := by
  refine (Finset.sum_le_sum fun u _ => bound_35 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_35)]
  decide +kernel

private def matrix_36_21 : CJ1.Block where
  bank := .leftLow
  cap := 153
  free := [(10, 3), (11, 0), (11, 1)]
  vectors := [
    [[596892563, 1117989245, 335817862, 741115284, 1482230585, 370557778, 370558305, 1482233220, 1806477468, 1667535297, 972778593, 383331640, 24483499, 458490, 687735, 916980, 533765522, 1066506184, 533765522, 916980, 687735, 458490, 968773850, 1153923097], [596892563, 521096682, 1945427613, 926394104, 555836481, 1945427730, 555837008, 926396212, 880081256, 787454041, 11625658, 24308194, 175305, 283185, 404550, 512430, 533253092, 533253092, 512430, 404550, 283185, 175305], [596892563, 2054910552, 2021223494, 1035877043, 1650665871, 294761859, 261075149, 665321063, 214760193, 995887517, 799046786, 1355967841, 774913897, 1356075721, 775035262, 1356183601, 1307775924, 1356183601, 775035262, 1356075721], [596892563, 1458017989, 563205505, 472671538, 1177994333, 1247473959, 1144307623, 1651719873, 1713832985, 1065363177, 1864390042, 1622284232, 1283336098, 72739623, 702295639, 653887962, 653887962, 702295639], [596892563, 861125426, 1832786512, 770591459, 407402874, 840071085, 304236538, 833755697, 532679500, 532683677, 1331706365, 290577867, 992758231, 1210687825, 1622314247, 1162280148], [596892563, 264232863, 1568553649, 1332744243, 1205365064, 1765412454, 752695442, 1864368900, 799017033, 1864373077, 1598039721, 823244579, 169513652, 1041174173], [596892563, 1798046733, 1901213349, 1562237327, 1773834170, 671635772, 1864368315, 585, 799016448, 1065356629, 532683092, 290561487], [596892563, 1201154170, 700059179, 862178148, 57899640, 266338344, 1598029971, 532677047, 266339401, 799017228], [596892563, 604261607, 95797572, 509516757, 1331691528, 1065353249, 532676722, 325], [596892563, 7369044, 428457272, 1864368130, 1598029831, 1598029851], [596892563, 347397788, 1864368129, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_36_21 : (CJ0.blockMatrix source 36 ((21 : ℤ)-24)).rank ≤ 153 :=
  Fast.cell (z := matrix_36_21) (Fast.bands [(12, 12, 1), (13, 13, 2), (14, 14, 3), (15, 15, 4), (16, 16, 5), (17, 17, 6), (18, 18, 7), (19, 19, 8), (20, 20, 9), (21, 21, 10), (22, 22, 11), (23, 23, 11), (24, 24, 11), (25, 25, 11), (26, 26, 11), (27, 27, 10), (28, 28, 9), (29, 29, 8), (30, 30, 7), (31, 31, 6), (32, 32, 5), (33, 33, 4), (34, 35, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_36_22 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_36_22 : (CJ0.blockMatrix source 36 ((22 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_36_22) (Fast.bands [(12, 12, 1), (13, 13, 2), (14, 14, 3), (15, 15, 4), (16, 16, 5), (17, 17, 6), (18, 18, 7), (19, 19, 8), (20, 20, 9), (21, 21, 10), (22, 22, 11), (23, 23, 11), (24, 24, 11), (25, 25, 11), (26, 26, 11), (27, 27, 10), (28, 28, 9), (29, 29, 8), (30, 30, 7), (31, 31, 6), (32, 32, 5), (33, 33, 4), (34, 34, 3), (35, 36, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_36 (u : ℕ) : ℕ :=
  match u with
  | 21 => 153
  | 22 => 143
  | u => nominal 36 u

private theorem bound_36 (u : ℕ) :
    (CJ0.blockMatrix source 36 ((u : ℤ)-24)).rank ≤ allowance_36 u := by
  unfold allowance_36
  split
  · exact cell_36_21
  · exact cell_36_22
  · exact (block_rank_le 36 _).trans (rank_le_nominal 36 _)

theorem grade_36 : (∑ u ∈ Finset.range (81-36), (CJ0.blockMatrix source 36 ((u : ℤ)-24)).rank) ≤ 3471 := by
  refine (Finset.sum_le_sum fun u _ => bound_36 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_36)]
  decide +kernel

private def matrix_37_20 : CJ1.Block where
  bank := .leftLow
  cap := 152
  free := [(10, 2), (10, 3), (11, 0), (11, 1)]
  vectors := [
    [[1246421154, 1600135250, 2130706178, 833752034, 1852767980, 740995400, 833178199, 1665196998, 1937533611, 161995502, 959015177, 1152124671, 887037019, 1635537233, 1332933833, 977145593, 631444133, 378195833, 288520583, 390736883, 656202593, 1011990833, 17043412, 1564654440], [1275897330, 1296951728, 1482230347, 370555468, 1667493354, 1852696076, 1296522098, 1387919481, 1198775977, 1003192037, 1211028350, 1074963979, 1960309973, 1834252193, 1669843073, 1489251953, 1330546988, 1236003653, 1234466363, 1327431953, 1487795573, 1672432193], [1305373506, 934815854, 252652758, 1431698226, 1237986887, 261005027, 1574554775, 293571583, 1074159364, 1008404346, 2104919274, 332323526, 283238126, 793374455, 1674563230, 1198543544, 936503431, 1683355043, 349205932, 220586409], [1334849682, 513727628, 661108372, 1162202128, 686364244, 741063569, 206106124, 1195057418, 1850184611, 2123676909, 1048786894, 1708977357, 1196191022, 479026434, 1111788407, 1554358347, 849748294, 749858360], [1364325858, 33687050, 665319284, 850597156, 92632261, 1557988921, 1372587374, 555264143, 2128964334, 2126125883, 2120205098, 947375330, 1512142874, 716105812, 693418387, 2030807378], [1393802034, 1625400553, 353714022, 1667508588, 1772776258, 1608530557, 324127629, 2130321534, 1064208079, 2127765833, 2124135323, 180853453, 1237003157, 1322611171], [1423278210, 1027455271, 1945427547, 404244132, 1903315187, 92621395, 2130632754, 2130453713, 2129967578, 2128845938, 2126644193, 1541880764], [1452754386, 370557637, 1267475521, 126326091, 1991744959, 2130694764, 2130659048, 2130544973, 1064885509, 2129545208], [1482230562, 1785414084, 538992905, 1760148570, 2130705034, 2130699413, 2130677443, 2130606463], [1511706738, 1010611746, 1528550256, 2130706334, 2130705758, 2130702713], [1541182914, 1296951742, 1]],
    [[120010145, 1572764533, 1875948086, 1273792211, 370560090, 92653937, 1574939857, 834035101, 1297909255, 651300568, 1952709630, 117611214, 1001885708, 60062190, 96741390, 139839450, 1247029879, 1277627344, 1288388374, 1275914749, 178352610, 135254550, 1447477051, 998388722], [1480125121, 231598527, 1736988966, 1204312595, 1019035455, 1296962918, 52142, 370760580, 1019705768, 835678473, 1324921049, 979096058, 20685990, 35977980, 55908810, 77781480, 1162330594, 108378945, 1173860269, 97199880, 77754510, 55396380], [709533664, 431615435, 488462366, 1069564311, 1448545022, 572688454, 555874766, 353858790, 219431095, 603448434, 3134703, 1749998727, 1755959097, 1183468128, 225549703, 623680029, 1890990941, 1119542689, 1407426601, 1593222524], [2069648640, 42108824, 80006781, 1709618373, 517939684, 6293, 1739122028, 101162616, 949870958, 855738, 1067369224, 391576616, 879294336, 1562004749, 889529451, 410320766, 26133930, 1188686823], [1299057183, 1193785127, 330554273, 654792324, 1366432171, 1336959700, 1012736738, 764344955, 532889090, 1598588256, 533956052, 632099026, 1118335136, 830360744, 1898462073, 1610148381], [528465726, 1755937911, 1059036904, 648475968, 1168520466, 290554116, 46333200, 47073, 1598169786, 1065712309, 1598831421, 1938571255, 1407012923, 1844202776], [1888580702, 1728567176, 2084386736, 1124305638, 65269118, 1459072923, 9048, 31005, 532767137, 532904222, 1065849394, 1647396883], [1117989245, 1111672922, 1094829398, 336870629, 741115573, 1443, 5850, 19890, 1598087301, 142350], [347397788, 2035961582, 40003385, 1088513097, 1065353392, 1065354094, 1065356824, 1065365599], [1707512764, 240020290, 370557642, 13, 1065353304, 475], [936921307, 1783308645, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[884285279, 530571183, 255, 1296954399, 277938453, 1389711033, 1297528234, 465509435, 193172822, 1968710931, 1171691256, 978581762, 1243669415, 495169200, 797772600, 1153560840, 1499262300, 1752510600, 1842185850, 1739969550, 1474503840, 1118715600, 2113663021, 566051993], [854809103, 833754705, 648476086, 1760150965, 463213079, 278010357, 834184335, 742786952, 931930456, 1127514396, 919678083, 1055742455, 170396460, 296454240, 460863360, 641454480, 800159445, 894702780, 896240070, 803274480, 642910860, 458274240], [825332927, 1195890579, 1878053675, 699008207, 892719546, 1869701406, 556151658, 1837134850, 1056547069, 1122302087, 25787160, 1798382907, 1847468307, 1337331978, 456143203, 932162889, 1194203002, 447351390, 1781500501, 1910120024], [795856751, 1616978805, 1469598061, 968504305, 1444342189, 1389642864, 1924600309, 935649015, 280521822, 7029525, 1081919539, 421729076, 934515411, 1651679999, 1018918026, 576348086, 1280958139, 1380848073], [766380575, 2097019383, 1465387149, 1280109277, 2038074172, 572717512, 758119059, 1575442290, 1742100, 4580550, 10501335, 1183331103, 618563559, 1414600621, 1437288046, 99899055], [736904399, 505305880, 1776992411, 463197845, 357930175, 522175876, 1806578804, 384900, 1066498354, 2940600, 6571110, 1949852980, 893703276, 808095262], [707428223, 1103251162, 185278886, 1726462301, 227391246, 2038085038, 73680, 252720, 738855, 1860495, 4062240, 588825669], [677952047, 1760148796, 863230912, 2004380342, 138961474, 11670, 47385, 161460, 1065820924, 1161225], [648475871, 345292349, 1591713528, 370557863, 1400, 7020, 28990, 99970], [618999695, 1120094687, 602156177, 100, 675, 3720], [589523519, 833754691], [0, 1]]
  ]
private theorem cell_37_20 : (CJ0.blockMatrix source 37 ((20 : ℤ)-24)).rank ≤ 152 :=
  Fast.cell (z := matrix_37_20) (Fast.bands [(13, 13, 1), (14, 14, 2), (15, 15, 3), (16, 16, 4), (17, 17, 5), (18, 18, 6), (19, 19, 7), (20, 20, 8), (21, 21, 9), (22, 22, 10), (23, 23, 11), (24, 24, 11), (25, 25, 11), (26, 26, 11), (27, 27, 11), (28, 28, 10), (29, 29, 9), (30, 30, 8), (31, 31, 7), (32, 32, 6), (33, 33, 5), (34, 35, 3), (35, 37, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_37_21 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_37_21 : (CJ0.blockMatrix source 37 ((21 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_37_21) (Fast.bands [(13, 13, 1), (14, 14, 2), (15, 15, 3), (16, 16, 4), (17, 17, 5), (18, 18, 6), (19, 19, 7), (20, 20, 8), (21, 21, 9), (22, 22, 10), (23, 23, 11), (24, 24, 11), (25, 25, 11), (26, 26, 11), (27, 27, 11), (28, 28, 10), (29, 29, 9), (30, 30, 8), (31, 31, 7), (32, 32, 6), (33, 33, 5), (34, 34, 4), (35, 36, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_37 (u : ℕ) : ℕ :=
  match u with
  | 20 => 152
  | 21 => 143
  | u => nominal 37 u

private theorem bound_37 (u : ℕ) :
    (CJ0.blockMatrix source 37 ((u : ℤ)-24)).rank ≤ allowance_37 u := by
  unfold allowance_37
  split
  · exact cell_37_20
  · exact cell_37_21
  · exact (block_rank_le 37 _).trans (rank_le_nominal 37 _)

theorem grade_37 : (∑ u ∈ Finset.range (81-37), (CJ0.blockMatrix source 37 ((u : ℤ)-24)).rank) ≤ 3311 := by
  refine (Finset.sum_le_sum fun u _ => bound_37 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_37)]
  decide +kernel

private def matrix_38_19 : CJ1.Block where
  bank := .leftLow
  cap := 150
  free := [(9, 5), (10, 1), (10, 2), (10, 3), (11, 0), (11, 1)]
  vectors := [
    [[1072347360, 23331407, 163504600, 1131731598, 614296949, 256539940, 2055697716, 1474841236, 1393552600, 675932165, 564566265, 2003275404, 2042783992, 1839510649, 305660, 728906440, 455902751, 1366600685, 1038879568, 893187281, 929523824, 965801033, 1184167305, 1952839958], [965112624, 1804357058, 2121653636, 790760504, 1904940764, 186492925, 439443485, 1708471826, 1690367473, 753947449, 84391722, 385499953, 61132, 1821226856, 1347804462, 1475363089, 801628971, 237141818, 492120626, 364621333, 1602921716, 1475363089], [857877888, 1669145748, 1361640971, 300668992, 683420199, 128111615, 387238108, 1918401555, 1180084780, 1006473924, 385478377, 1420490134, 1893998832, 855990395, 601070921, 728589992, 2039830464, 164102839, 182315611, 291562576], [750643152, 1748403910, 1823175263, 1400517852, 1831145950, 635173817, 1751175243, 895989630, 1928563318, 1332452621, 236750753, 1420482942, 1420493730, 1547987629, 1311262048, 1274859878, 874230137, 1147404636], [643408416, 2042131544, 1053845871, 1996893952, 732273630, 1343086707, 967012968, 956693436, 1924313771, 710236976, 1538847081, 236752551, 1775602329, 1293015114, 755795876, 1639046994], [536173680, 419622217, 862655020, 425323104, 1913887986, 1393154214, 1050177278, 1924313336, 1065353579, 2012334812, 1302100591, 1775593194, 2012341917, 919676662], [428938944, 1142288795, 927898502, 1842389363, 1464177755, 1143661236, 503842284, 710235555, 232, 473490921, 2012335218, 1420473662], [321704208, 2079424845, 927872109, 1180083563, 1947380695, 1214077743, 14, 1420471004, 1775588839, 355118111], [214469472, 1100323934, 540871633, 620393725, 1214077740, 2, 710235486, 710235507], [107234736, 335692495, 1897603507, 1608653005, 868065584, 1]],
    [[90228237, 2023100950, 1447880518, 1275726265, 1227213948, 533159871, 1655760404, 893418105, 1741561117, 1056904793, 1337806079, 1403499713, 2028616821, 940777137, 1821469758, 2024898889, 96661794, 174529792, 873259115, 1807799469, 587260516, 57693935, 2045703871, 115778955], [730102352, 1547953675, 910627164, 492381560, 1188669237, 2067883728, 2098849532, 319949465, 1252715280, 1934487812, 1951861114, 480485553, 1878810570, 1499613611, 358876280, 2075084697, 298337409, 1303230754, 1530196905, 714169683, 207392430, 184747147], [1951078226, 180459476, 1738387991, 1553389382, 1692533, 1712278769, 1705970421, 384864302, 1687687990, 128528669, 1591463014, 1898417342, 1427218175, 1673685518, 232312828, 176969443, 1372497920, 1709605236, 982573393, 1747356103], [1622449426, 438725942, 39767404, 1117819417, 421033717, 175746687, 1644061471, 22401796, 1969484228, 1028410372, 1924830896, 1037574230, 1220237455, 1386856273, 277144355, 1848737769, 1741673898, 346863937], [1874922385, 579447796, 1802099661, 1420670217, 757105226, 1389563745, 1886722683, 810738035, 2014687923, 1092179150, 252541549, 1708933647, 585949714, 1785133572, 762687238, 1856767563], [577790670, 990026194, 1584384543, 200438744, 980860173, 1374870206, 90711092, 631400819, 216658275, 2035422722, 829565149, 510287060, 1367879442, 1386239620], [1992467147, 2057862292, 1693645251, 1933754244, 499545388, 1586468962, 573867469, 35370320, 1181656339, 1044694846, 135332229, 915224885], [1857538950, 2039650813, 1531396241, 1370828492, 965358579, 565471779, 4298700, 17042080, 58397000, 174040885], [173006079, 1322792913, 1855056090, 346017586, 564590994, 291180, 1546635, 6916790], [1200281400, 294689748, 437067704, 801289706, 946975398], [677952047, 1]],
    [[1736818954, 591498005, 1879957558, 1541809679, 326714409, 1069150405, 1424798889, 2119934791, 1071188650, 393380635, 1010436494, 293288124, 372254203, 1109971985, 1181335979, 1129579231, 285672016, 1744268627, 209938647, 1901923607, 1893496665, 1765012606, 229082035, 1145802338], [459885905, 1848124683, 1720459882, 1497953352, 636217435, 624077073, 2079462986, 893304419, 391193062, 852820844, 967760270, 1953656534, 411670176, 917245847, 840630189, 1471209118, 275014630, 860952098, 152068098, 1151942719, 1978782570, 355707641], [861691257, 622402231, 568041013, 747554895, 6010133, 433443446, 1946494186, 658821819, 1324909436, 860905012, 1407532385, 1582129299, 1939960070, 2021067518, 450286256, 2080887383, 463757544, 1158396821, 1002809395, 1346632879], [811528577, 400941178, 1952524093, 55588775, 98524373, 583165598, 1802400090, 902172050, 145516660, 2052022485, 1416659202, 1013186100, 1339262408, 445037896, 315939213, 1318036948, 666077225, 307071721], [309397865, 408939187, 299804773, 1808151001, 260100323, 1700686247, 712319222, 2021949731, 12920719, 1475543359, 412355744, 742221555, 1383714676, 1046364381, 1552768112, 404261588], [1486005554, 2002300354, 108209110, 1747900846, 240248895, 141416016, 984484383, 65784819, 674212161, 1633815838, 532827350, 507293740, 2100682461, 1979456517], [79938778, 144809476, 1033548536, 2016566899, 392806577, 1353349217, 312090176, 230868537, 690891366, 1522628870, 174839776, 1386449733], [352610403, 453783515, 19826291, 759682354, 1956661138, 550228803, 1419757842, 1891128236, 227024322, 444497129], [173313996, 23713701, 1952769588, 428973266, 550374593, 1420422902, 946723778, 235592917], [1672755990, 210504130, 1189796235, 445162121, 1473081908], [589523519, 0, 1]],
    [[1117344418, 1219362396, 752300234, 1727958718, 1978423020, 1382876636, 1672387158, 287997929, 840384368, 1160796405, 1788171144, 1145166862, 1278099407, 707457319, 1579471062, 1946597752, 2098329051, 1232172087, 1641397740, 13155026, 1991089552, 696879820, 752103745, 2022210954], [48371162, 854209307, 2128661659, 1374751838, 1046531257, 862803116, 868319983, 1785371295, 913544223, 408088912, 582942376, 944529956, 654741700, 97092682, 468703318, 1521986240, 1392359073, 1412167146, 956852681, 1082226184, 1858411039, 864677877], [625852877, 883697468, 1270589229, 1272890821, 1759582121, 1324057312, 94011673, 795648775, 1323010871, 1600677710, 1873077644, 1992425928, 1302693506, 1637804589, 225162935, 1134569083, 101178801, 2097165411, 1921770539, 1432995866], [719083130, 629874832, 879031009, 65217815, 1587692108, 1773330565, 1966563714, 1357682480, 1631877405, 1692621373, 284110972, 364920039, 1538200453, 511802147, 1385432781, 543428900, 1235464927, 660168322], [328061921, 1545495785, 749426292, 283066830, 1489732820, 585857363, 753494340, 1919418687, 937897273, 1253756938, 1832401229, 1943882565, 758174618, 1719220627, 1606857896, 315376259], [1583495683, 821901847, 2033118465, 404539760, 1343267012, 1901739310, 613285763, 668404512, 1067501609, 953087763, 784732249, 1567458535, 626575547, 1528613145], [223971550, 2042553837, 845235710, 1827727436, 894951307, 1438702742, 312716969, 710585436, 1865521622, 476813509, 955393093, 1536078916], [510902388, 268086842, 1048929602, 928985648, 843785649, 2088222774, 42350, 1420639622, 178138609, 889525480], [313581764, 1212668114, 1471136511, 248885986, 490184313, 1065356049, 1242927333, 710304126], [1762716111, 2067639173, 1192831376, 2127671221, 1578301005], [596892563, 0, 0, 1]],
    [[1950249959, 215210966, 1365651830, 1709960336, 1806984970, 1064386691, 949892058, 343870223, 778290632, 16896847, 1585800708, 1454413452, 204179224, 249152159, 618473350, 211615088, 1937382845, 1781646849, 384188203, 645813928, 956185401, 2015318563, 170005124, 1899148523], [670501729, 1165505516, 309452105, 1145943313, 1884074392, 125645410, 63713802, 1490807503, 1755982306, 392437242, 357690649, 1169735327, 503791726, 1262185644, 1412953873, 111243472, 1534031615, 1654951358, 1201019056, 702367067, 1715921573, 1761212139], [359256414, 1769787481, 784636884, 1154634102, 2127321367, 836855328, 849472024, 1360977829, 886036886, 1873649105, 1078486838, 464578182, 1406976516, 914041830, 1666080777, 1776767547, 1516417026, 842202394, 165559647, 766700660], [1016514014, 1253254549, 2051171625, 2025774032, 1288638999, 1779213059, 973289924, 2085902841, 322444419, 73885689, 411751074, 55557973, 1820937956, 1487700320, 1576417723, 563937328, 778065070, 1436978559], [511568096, 971810841, 657213544, 1420072432, 616495981, 1482285376, 487967500, 509230371, 232037020, 2077054566, 1625623335, 843545572, 958807005, 691145722, 605331957, 547877740], [975125093, 150654045, 1092643780, 1729828945, 168986087, 1511672454, 1949284256, 867904795, 1697389883, 190567422, 471576135, 1110132313, 1525653982, 1488933626], [276478572, 145688282, 874122364, 393904378, 1131615657, 1088474948, 982971495, 2059965793, 1898100188, 41316741, 1860041975, 300256663], [546334966, 182111240, 1198620384, 1519755882, 199989280, 999762875, 2122109033, 2096622273, 2013912433, 1782624663], [1784694275, 1615827040, 551300686, 1438671265, 1001524445, 2130124073, 2127613163, 2116872853], [1860850066, 1541326937, 1256571028, 528127021, 236755637], [774802339], [1]],
    [[393887479, 1539208428, 250748875, 588896754, 1803992024, 1061556028, 705907544, 10771642, 1059517783, 1737325798, 1120269939, 1837418309, 1758452231, 1020734448, 949370454, 1001127202, 1845034417, 386437806, 1920767786, 228782826, 237209768, 365693827, 1901624398, 984904095], [1670820528, 282581750, 410246551, 632753081, 1494488998, 1506629360, 51243447, 1237402014, 1739513371, 1277885589, 1162946163, 177049900, 1719036257, 1213460586, 1290076244, 659497315, 1855691803, 1269754335, 1978638335, 978763714, 151923863, 1774998792], [1269015176, 1508304202, 1562665420, 1383151538, 2124696300, 1697262987, 184212247, 1471884614, 805796997, 1269801421, 723174049, 548577134, 190746363, 109638915, 1680420177, 49819050, 1666948889, 972309612, 1127897038, 784073554], [1319177856, 1729765255, 178182340, 2075117658, 2032182060, 1547540835, 328306343, 1228534383, 1985189773, 78683949, 714047231, 1117520333, 791444025, 1685668537, 1814767220, 812669485, 1464629208, 1823634712], [1821308568, 1721767246, 1830901660, 322555432, 1870606110, 430020186, 1418387211, 108756702, 2117785715, 655163074, 1718350689, 1388484878, 746991757, 1084342052, 577938321, 1726444845], [644700879, 128406079, 2022497323, 382805587, 1890457538, 1989290417, 1146222050, 2064921615, 1456494272, 496890595, 1597879083, 1623412693, 30023972, 151249916], [2050767655, 1985896957, 1097157897, 114139534, 1737899856, 777357216, 1818616258, 1899837896, 1439815067, 608077563, 1955866657, 744256700], [1778096030, 1676922918, 2110880142, 1371024079, 174045295, 1580477631, 710948591, 239578197, 1903682111, 1686209304], [1957392437, 2106992732, 177936845, 1701733167, 1580331841, 710283531, 1183982655, 1895113516], [457950443, 1920202303, 940910198, 1685544313, 657624525], [1541182914], [0, 1]]
  ]
private theorem cell_38_19 : (CJ0.blockMatrix source 38 ((19 : ℤ)-24)).rank ≤ 150 :=
  Fast.cell (z := matrix_38_19) (Fast.bands [(14, 14, 1), (15, 15, 2), (16, 16, 3), (17, 17, 4), (18, 18, 5), (19, 19, 6), (20, 20, 7), (21, 21, 8), (22, 22, 9), (23, 23, 10), (24, 24, 11), (25, 25, 11), (26, 26, 11), (27, 27, 11), (28, 28, 11), (29, 29, 10), (30, 30, 9), (31, 31, 8), (32, 32, 7), (33, 33, 6), (34, 35, 4), (35, 37, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_38_20 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_38_20 : (CJ0.blockMatrix source 38 ((20 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_38_20) (Fast.bands [(14, 14, 1), (15, 15, 2), (16, 16, 3), (17, 17, 4), (18, 18, 5), (19, 19, 6), (20, 20, 7), (21, 21, 8), (22, 22, 9), (23, 23, 10), (24, 24, 11), (25, 25, 11), (26, 26, 11), (27, 27, 11), (28, 28, 11), (29, 29, 10), (30, 30, 9), (31, 31, 8), (32, 32, 7), (33, 33, 6), (34, 34, 5), (35, 36, 3), (36, 38, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_38 (u : ℕ) : ℕ :=
  match u with
  | 19 => 150
  | 20 => 143
  | u => nominal 38 u

private theorem bound_38 (u : ℕ) :
    (CJ0.blockMatrix source 38 ((u : ℤ)-24)).rank ≤ allowance_38 u := by
  unfold allowance_38
  split
  · exact cell_38_19
  · exact cell_38_20
  · exact (block_rank_le 38 _).trans (rank_le_nominal 38 _)

theorem grade_38 : (∑ u ∈ Finset.range (81-38), (CJ0.blockMatrix source 38 ((u : ℤ)-24)).rank) ≤ 3153 := by
  refine (Finset.sum_le_sum fun u _ => bound_38 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_38)]
  decide +kernel

private def matrix_39_18 : CJ1.Block where
  bank := .rightLow
  cap := 148
  free := [(20, 0), (21, 0), (22, 0), (23, 0), (24, 0)]
  vectors := [
    [[0, 0, 0, 1, 4, 6, 4, 1], [0, 0, 6, 16, 8, 2130706421, 2130706419, 2130706429], [0, 0, 15, 6, 2130706359, 2130706325, 2130706394, 10, 6], [0, 20, 2130706363, 2130706229, 2130706409, 216, 150, 20, 2130706429], [0, 15, 2130706273, 2130706398, 636, 621, 0, 2130706268, 2130706393, 1], [6, 2130706277, 476, 924, 2130705935, 2130705137, 2130705929, 24, 26], [1, 2130706359, 708, 2130706041, 2130703794, 2130705263, 924, 672, 87, 2130706427], [2130706419, 416, 2130704645, 2130705069, 3290, 3240, 384, 2130706121, 2130706367], [91, 2130705029, 2541, 4840, 2130705488, 2130703193, 2130705332, 2130706397, 15], [2130706069, 3146, 2130705113, 2130699173, 2130703673, 1170, 704, 80], [1001, 2130701571, 2130704255, 5808, 4137, 498, 2130706303, 2130706413], [2130704431, 5148, 5544, 2130704717, 2130703871, 2130705797, 2130706393], [3003, 2130703001, 2130700394, 2130705201, 595, 204, 15], [2130703001, 858, 3828, 1540, 140, 2130706427], [3003, 858, 2130705113, 2130705753, 2130706328, 2130706427], [2130704431, 2130705289, 84, 116, 14], [1001, 676, 123, 8, 1], [2130706069, 2130706199, 2130706385, 2130706429], [91, 46, 6], [2130706419, 2130706429], [1]],
    [[0, 0, 0, 14, 57, 87, 59, 15], [0, 0, 84, 231, 126, 2130706268, 2130706229, 2130706373], [0, 0, 210, 105, 2130705404, 2130704858, 2130705827, 135, 90], [0, 280, 2130705488, 2130703493, 2130705894, 3024, 2229, 320, 2130706373], [0, 210, 2130704228, 2130705698, 8820, 9261, 378, 2130704063, 2130705818, 15], [84, 2130704270, 6342, 13524, 2130700553, 2130687911, 2130698621, 213, 396], [14, 2130705404, 9681, 2130702198, 2130669389, 2130687470, 12054, 9954, 1410, 2130706342], [2130706238, 5736, 2130682538, 2130684797, 43575, 47880, 7434, 2130702113, 2130705404], [1260, 2130687284, 32304, 70059, 2130699188, 2130661073, 2130689297, 2130705614, 231], [2130701428, 42276, 2130693926, 2130606003, 2130661073, 13860, 10339, 1302], [13650, 2130642512, 2130669044, 75141, 61362, 9555, 2130704816, 2130706118], [2130679406, 65208, 81873, 2130690593, 2130671006, 2130696437, 2130705698], [40040, 2130666536, 2130622283, 2130683410, 6615, 2940, 245], [2130661388, 5148, 50127, 23562, 2940], [38610, 15873, 2130691352, 2130696968, 2130704753, 2130706328], [2130681408, 2130689273, 2130705860, 1292, 189], [12012, 9321, 2196, 225, 21], [2130702338, 2130703469, 2130705728, 2130706367], [910, 501, 69, 2130706432], [2130706328, 2130706409, 3], [0, 2130706430], [1]],
    [[0, 0, 0, 105, 434, 673, 464, 120], [0, 0, 630, 1778, 1044, 2130705225, 2130704849, 2130705953], [0, 0, 1575, 924, 2130698789, 2130694211, 2130701445, 960, 720], [0, 2100, 2130699573, 2130683893, 2130700959, 22512, 17608, 2720, 2130705953], [0, 1575, 2130690123, 2130699398, 65240, 73101, 5796, 2130688383, 2130701393, 120], [630, 2130690347, 45528, 104664, 2130670243, 2130566069, 2130642425, 472, 3216], [105, 2130698761, 71134, 2130682255, 2130430024, 2130547253, 82320, 78036, 12148, 2130705697], [2130704977, 42456, 2130534291, 2130530125, 307020, 372792, 71484, 2130675185, 2130697881], [9360, 2130566009, 222682, 534138, 2130693518, 2130372113, 2130566132, 2130697451, 1897], [2130669473, 306176, 2130646339, 2129970753, 2130325073, 81690, 79674, 11284], [100100, 2130251849, 2130391591, 514734, 474957, 91140, 2130696717, 2130703787], [2130509873, 449592, 627242, 2130643469, 2130451661, 2130624533, 2130699335], [288288, 2130451321, 2130091577, 2130499919, 34055, 21784, 2135], [2130386113, 5148, 345246, 184184, 29400, 910], [270270, 133848, 2130617531, 2130639323, 2130692678, 2130705453], [2130534833, 2130577161, 2130691735, 6388, 1204], [80080, 65832, 18374, 2542, 231], [2130680225, 2130687089, 2130701431, 2130705905], [5460, 2776, 322, 2130706411], [2130705873, 2130706409, 46], [0, 2130706409, 1], [0, 2130706431], [1]],
    [[0, 0, 0, 560, 2345, 3689, 2584, 680], [0, 0, 3360, 9695, 6062, 2130700177, 2130697729, 2130703713], [0, 0, 8400, 5565, 2130666120, 2130639374, 2130677533, 4760, 4080], [0, 11200, 2130670908, 2130584157, 2130670194, 118440, 98192, 16320, 2130703713], [0, 8400, 2130620508, 2130662088, 342370, 406161, 46914, 2130609703, 2130677193, 680], [3360, 2130621278, 233534, 571074, 2130552573, 2129956439, 2130338261, 2130701809, 18496], [560, 2130665728, 372617, 2130610722, 2129245939, 2129781068, 390726, 429618, 73916, 2130702217], [2130698698, 223832, 2129820094, 2129709613, 1535345, 2035320, 462882, 2130550697, 2130656113], [49504, 2129972009, 1102385, 2868547, 123165, 2128979645, 2129904947, 2130640598, 11033], [2130511953, 1584376, 2130525042, 2126891523, 2128506893, 308280, 426139, 69166], [523600, 2128389989, 2128900926, 2504337, 2557212, 582435, 2130673092, 2130690690], [2129685413, 2231736, 3364801, 2130614825, 2129436206, 2130244013, 2130658462], [1485120, 2129522393, 2127533846, 2129484058, 93905, 108290, 13181], [2129072801, 2130611481, 1691415, 983906, 190610, 11564], [1361360, 755898, 2130333500, 2130382668, 2130631043, 2130699958], [2129855583, 2130028041, 2130594072, 15404, 4039], [388960, 329368, 98707, 16969, 1771], [2130582673, 2130615017, 2130683484, 2130703903], [24752, 11876, 575, 2130706180], [2130704053, 2130706409, 299], [0, 2130706409, 23], [0, 2130706409], [0, 2130706432], [1]],
    [[0, 0, 0, 2380, 10080, 16065, 11424, 3060], [0, 0, 14280, 42000, 27720, 2130680729, 2130668489, 2130694193], [0, 0, 35700, 26040, 2130537173, 2130414617, 2130574241, 18360, 18360], [0, 47600, 2130559433, 2130179753, 2130525049, 494208, 433296, 77520, 2130694193], [0, 35700, 2130345233, 2130493283, 1430184, 1783656, 266112, 2130297923, 2130571793, 3060], [14280, 2130346913, 958440, 2468424, 2130204113, 2127533249, 2129040209, 2130651353, 84456], [2380, 2130534233, 1558620, 2130417529, 2124570569, 2126503073, 1447656, 1859760, 356184, 2130687257], [2130673673, 941640, 2127054617, 2126284961, 6121920, 8764560, 2285136, 2130113729, 2130471425], [208845, 2127638249, 4384488, 12208416, 1217790, 2123665553, 2127132317, 2130337505, 50949], [2129889617, 6558576, 2130403745, 2114961913, 2120843153, 787752, 1762544, 336168], [2187900, 2121242849, 2122653509, 9737640, 10818612, 2808120, 2130671237, 2130632057], [2126465273, 8914776, 14270520, 438768, 2125723721, 2128704713, 2130451577], [6126120, 2126255129, 2117678825, 2125183377, 72030, 390600, 64624], [2124023393, 2129930801, 6641184, 4104408, 897960, 87360], [5513508, 3308448, 2129448869, 2129476553, 2130405713, 2130672497], [2127303033, 2127888761, 2130142601, 8320, 2130706097], [1531530, 1319448, 408360, 73536, 10626], [2130229073, 2130355121, 2130621857, 2130700361], [92820, 42816, 828, 2130704409], [2130697865, 2130706409, 552], [0, 2130706409, 276], [0, 2130706409], [0, 2130706409], [], [1]]
  ]
private theorem cell_39_18 : (CJ0.blockMatrix source 39 ((18 : ℤ)-24)).rank ≤ 148 :=
  Fast.cell (z := matrix_39_18) (Fast.bands [(0, 16, 24), (1, 17, 22), (2, 18, 20), (3, 19, 18), (4, 20, 16), (5, 21, 14), (6, 22, 12), (7, 23, 10), (8, 24, 8), (9, 25, 6), (10, 26, 4), (11, 27, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_39_19 : CJ1.Block where
  bank := .leftLow
  cap := 142
  free := [(10, 2), (11, 0)]
  vectors := [
    [[1494772513, 544149643, 2065146237, 2097926356, 262240973, 826059654, 6562013, 1245669446, 786815484, 1737634917, 1921695913, 723010809, 3851316, 1973916060, 503382399, 2016718045, 383066849, 1829359279, 1339127452, 1829359279, 383066849, 2016718045, 503382399], [1494772513, 1180083563, 885062674, 1212863682, 1180083724, 1776682363, 360586083, 885083363, 2032438554, 1835902796, 721727037, 1283772, 2567544, 1971348516, 662740316, 1353977729, 1159795553, 669563726, 669563726, 1159795553, 1353977729], [1494772513, 1816017483, 1199751624, 13112058, 1166971666, 609710697, 1881581819, 1134207977, 898230577, 1573606139, 1278827331, 853162874, 1280111103, 691237413, 2102209336, 1382474826, 1908027160, 892242999, 1908027160], [1494772513, 321244970, 878506654, 1265311837, 2032366262, 708050868, 1173530951, 2091383459, 1573487471, 118668, 1278708663, 1705160644, 1705656892, 1116286954, 985922382, 396552444, 1511474716], [1494772513, 957178890, 2052034197, 1343984073, 688382189, 19668679, 1153862272, 1573455107, 32364, 86304, 1278622359, 426538285, 1279118607, 1967874780, 1148754035], [1494772513, 1593112810, 458921387, 885062686, 1934025936, 216349176, 1573447016, 8091, 24273, 62031, 1278560328, 1278684390, 434217], [1494772513, 98340297, 360581090, 524481596, 1409544340, 1573445189, 1827, 6264, 18009, 44022, 1278516306], [1494772513, 734274217, 1757013306, 898174723, 1147303537, 426141652, 1704566608, 426146089, 1704578353], [1494772513, 1370208137, 386805169, 1147303474, 63, 426141589, 1278425019], [1494772513, 2006142057, 1147303465, 9, 54], [1494772513, 1147303464, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_39_19 : (CJ0.blockMatrix source 39 ((19 : ℤ)-24)).rank ≤ 142 :=
  Fast.cell (z := matrix_39_19) (Fast.bands [(15, 15, 1), (16, 16, 2), (17, 17, 3), (18, 18, 4), (19, 19, 5), (20, 20, 6), (21, 21, 7), (22, 22, 8), (23, 23, 9), (24, 24, 10), (25, 25, 11), (26, 26, 11), (27, 27, 11), (28, 28, 11), (29, 29, 11), (30, 30, 10), (31, 31, 9), (32, 32, 8), (33, 33, 7), (34, 34, 6), (35, 36, 4), (36, 38, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_39 (u : ℕ) : ℕ :=
  match u with
  | 18 => 148
  | 19 => 142
  | u => nominal 39 u

private theorem bound_39 (u : ℕ) :
    (CJ0.blockMatrix source 39 ((u : ℤ)-24)).rank ≤ allowance_39 u := by
  unfold allowance_39
  split
  · exact cell_39_18
  · exact cell_39_19
  · exact (block_rank_le 39 _).trans (rank_le_nominal 39 _)

theorem grade_39 : (∑ u ∈ Finset.range (81-39), (CJ0.blockMatrix source 39 ((u : ℤ)-24)).rank) ≤ 2997 := by
  refine (Finset.sum_le_sum fun u _ => bound_39 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_39)]
  decide +kernel

end Front6960ListBank

end Merged6967_R6960Front6960ListCells3

section Merged6967_R6960Front6960ListCells4
set_option Elab.async false


set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6960ListBank
open scoped BigOperators

private def matrix_40_17 : CJ1.Block where
  bank := .rightLow
  cap := 145
  free := [(21, 0), (22, 0), (23, 0), (24, 0)]
  vectors := [
    [[0, 0, 0, 1, 3, 3, 1], [0, 0, 0, 7, 14, 3, 2130706425, 2130706429], [0, 0, 21, 7, 2130706370, 2130706373, 2130706428, 6], [0, 0, 35, 2130706349, 2130706230, 0, 129, 40, 2130706429], [0, 35, 2130706188, 2130706349, 567, 378, 2130706373, 2130706378, 1], [0, 21, 2130706111, 588, 1092, 2130706055, 2130705677, 2130706310, 32], [7, 2130706202, 1253, 2130706335, 2130703850, 2130705551, 546, 192, 2130706426], [1, 2130706345, 1137, 2130703893, 2130703948, 2520, 2058, 48, 2130706328], [2130706419, 507, 2130703163, 2299, 5985, 0, 2130704711, 2130706118, 21], [91, 2130704665, 5973, 1210, 2130699713, 2130703913, 483, 182], [2130706069, 4147, 2130699536, 2130700262, 3444, 2583, 203, 2130706398], [1001, 2130699569, 4257, 8184, 441, 2130705341, 2130706258], [2130704431, 8151, 396, 2130700658, 2130704718, 84, 35], [3003, 2130699569, 2130702968, 2002, 980, 84], [2130703001, 3861, 3399, 55, 2130706223, 2130706412], [3003, 2130705289, 2130704684, 2130706101, 2130706426], [2130704431, 2130706290, 474, 113, 7], [1001, 312, 2130706400, 2130706423], [2130706069, 2130706290, 2130706418, 2130706432], [91, 32, 3], [2130706419, 2130706430], [1]],
    [[0, 0, 0, 14, 43, 44, 15], [0, 0, 0, 98, 204, 52, 2130706319, 2130706373], [0, 0, 294, 126, 2130705551, 2130705540, 2130706343, 90], [0, 0, 490, 2130705313, 2130703479, 2130706265, 1858, 620, 2130706373], [0, 490, 2130703073, 2130704893, 7896, 5796, 2130705708, 2130705593, 15], [0, 294, 2130701981, 7644, 16100, 2130702149, 2130695345, 2130704385, 486], [98, 2130703227, 16982, 686, 2130670103, 2130691733, 7476, 3013, 2130706327], [14, 2130705209, 15598, 2130673345, 2130668003, 32592, 31164, 1512, 2130704811], [2130706238, 6996, 2130662310, 25938, 86310, 5880, 2130681737, 2130701231, 322], [1260, 2130682279, 78506, 26620, 2130614873, 2130665273, 5754, 2884], [2130701428, 55926, 2130620281, 2130611327, 40572, 38850, 3934, 2130705887], [13650, 2130615485, 45122, 117216, 14238, 2130691313, 2130703535], [2130679406, 105248, 19239, 2130629279, 2130678013, 364, 560], [40040, 2130621491, 2130649739, 22484, 14700, 1540], [2130661388, 43758, 49698, 4290, 2130703703, 2130706083], [38610, 2130697281, 2130682915, 2130700641, 2130706167], [2130681408, 2130701285, 5459, 1702, 126], [12012, 5226, 38, 2130706325], [2130702338, 2130704379, 2130706125, 2130706411], [910, 396, 46], [2130706328, 2130706409, 1], [0, 2130706431], [1]],
    [[0, 0, 0, 105, 329, 344, 120], [0, 0, 0, 735, 1582, 464, 2130705569, 2130705953], [0, 0, 2205, 1127, 2130699854, 2130699373, 2130705593, 720], [0, 0, 3675, 2130698397, 2130683634, 2130703913, 14192, 5120, 2130705953], [0, 3675, 2130681688, 2130692643, 58401, 46914, 2130702103, 2130699593, 120], [0, 2205, 2130673407, 53634, 125020, 2130682199, 2130620501, 2130688369, 3936], [735, 2130682570, 123809, 17346, 2130436268, 2130579719, 53298, 25196, 2130705577], [105, 2130697305, 114941, 2130473453, 2130399378, 220920, 247842, 18984, 2130693073], [2130704977, 51816, 2130385858, 158147, 652365, 87612, 2130521507, 2130660758, 2633], [9360, 2130529049, 557809, 250690, 2130052493, 2130359513, 31899, 24366], [2130669473, 406276, 2130120606, 2129958290, 240492, 303555, 39459, 2130701890], [100100, 2130055289, 260161, 869352, 164493, 2130600173, 2130680862], [2130509873, 737880, 209253, 2130173978, 2130467138, 2130700483, 4781], [288288, 2130131001, 2130254168, 121506, 112210, 14924], [2130386113, 275418, 366267, 57035, 2130689843, 2130703318], [270270, 2130668681, 2130547032, 2130656877, 2130702632], [2130534833, 2130657241, 29827, 12489, 1211], [80080, 39624, 3931, 2130706143], [2130680225, 2130692549, 2130703648, 2130706180], [5460, 2216, 299], [2130705873, 2130706409, 23], [0, 2130706409], [0, 2130706432], [1]],
    [[0, 0, 0, 560, 1785, 1904, 680], [0, 0, 0, 3920, 8680, 2856, 2130701809, 2130703713], [0, 0, 11760, 6860, 2130671657, 2130667061, 2130700993, 4080], [0, 0, 19600, 2130665273, 2130582169, 2130686561, 76296, 29920, 2130703713], [0, 19600, 2130576583, 2130622937, 305676, 266112, 2130690623, 2130666993, 680], [0, 11760, 2130531993, 269304, 682920, 2130617729, 2130239729, 2130594233, 22576], [3920, 2130580013, 644056, 144956, 2129287673, 2129954969, 260400, 149124, 2130701537], [560, 2130657993, 603624, 2129531281, 2128998153, 1053360, 1371216, 149856, 2130628505], [2130698698, 273336, 2129043341, 689216, 3466890, 670320, 2129752697, 2130423185, 15249], [49504, 2129777529, 2838912, 1534280, 2127411953, 2128709585, 87024, 145768], [2130511953, 2107976, 2127837149, 2126621033, 972552, 1622880, 274204, 2130679657], [523600, 2127368969, 1075800, 4522848, 1114848, 2130218393, 2130546777], [2129685413, 3716856, 1345212, 2128115537, 2129362363, 2130611513, 28924], [1485120, 2127888761, 2128236977, 439208, 564760, 101640], [2129072801, 1266408, 1884036, 388520, 2130655613, 2130686777], [1361360, 2130611481, 2129942681, 2130438673, 2130672777], [2129855583, 2130417001, 115620, 54496, 8246], [388960, 205608, 29664, 3448], [2130582673, 2130639769, 2130692981, 2130704409], [24752, 9496, 552], [2130704053, 2130706409, 276], [0, 2130706409], [0, 2130706409], [], [1]]
  ]
private theorem cell_40_17 : (CJ0.blockMatrix source 40 ((17 : ℤ)-24)).rank ≤ 145 :=
  Fast.cell (z := matrix_40_17) (Fast.bands [(0, 17, 24), (1, 18, 22), (2, 19, 20), (3, 20, 18), (4, 21, 16), (5, 22, 14), (6, 23, 12), (7, 24, 10), (8, 25, 8), (9, 26, 6), (10, 27, 4), (11, 28, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_40_18 : CJ1.Block where
  bank := .leftLow
  cap := 141
  free := [(10, 1), (10, 2), (11, 0)]
  vectors := [
    [[937510827, 1534108508, 2130704309, 426117565, 1704371224, 595360325, 1357233200, 2102880833, 323297869, 1375601628, 16412979, 705474776, 1385408499, 817271101, 1838833641, 1056151015, 1600171440, 411724452, 547214612, 1713528702, 1430066062, 978700921, 1508104307], [1107967342, 2130706325, 1278422058, 426121723, 852127064, 936545731, 2125836953, 1257888567, 352306057, 622572970, 226982907, 628693193, 1057117954, 291634755, 251677837, 1547591429, 1514154433, 531094373, 1649644593, 1525458531, 647725782], [1278423857, 255684679, 767052809, 1193179700, 1960127007, 2129964417, 678182760, 1178240270, 1993134512, 1119940372, 1711096385, 725157148, 955509547, 1374764508, 1934872279, 1559291317, 1600571804, 1049044668, 115602180], [1448880372, 170456436, 1107966107, 1107954645, 2130610953, 1874460566, 1872338182, 1097233429, 1241812408, 2022718553, 147841093, 1925413134, 436254508, 1570991205, 658652386, 421733353, 1172746284], [1619336887, 1875021596, 681825064, 2130696513, 1704492532, 340497044, 168515250, 1270842916, 2105462513, 2058060041, 669853178, 23584909, 920096308, 775949393, 52419809], [1789793402, 1107967293, 2130705658, 1278416333, 852228813, 1363351060, 1277048713, 2125447283, 2113561604, 2082462497, 1160205180, 1450709482, 1650896648], [1960249917, 2130706393, 1704564568, 1278418373, 426102879, 1278212512, 2129756393, 2127130211, 2119244879, 2099074625, 1628794480], [2130706432, 681826030, 2045477772, 2045474408, 2130680343, 2130563927, 1277787333, 1702187332, 1697026579], [170456514, 1022739070, 1534108382, 2130704094, 2130690053, 852191828, 851872418], [340913029, 1022739080, 2130706317, 2130705263, 2130697541], [511369544, 1]],
    [[1630263589, 1853168271, 1311204118, 1376765936, 1901260293, 1042500054, 275834930, 1477194941, 1384492182, 1051831862, 388281494, 739329015, 376145196, 902661905, 973859174, 1702787557, 1866746673, 360828489, 1314948533, 1544215109, 127565671, 571225624, 1274734270], [39336119, 1529737960, 1343984193, 174828664, 732100564, 537666186, 874502224, 744560492, 71115686, 1404974597, 615231055, 112971936, 240921212, 622371685, 289621905, 1752695121, 5786780, 234039905, 959906824, 476043513, 2121758060], [579115082, 126749723, 1472919227, 718978034, 1263135734, 382490377, 520385402, 337669310, 1181842585, 153987774, 31605244, 499878705, 1430984879, 1723488292, 233579409, 191199385, 1034238950, 2120560462, 58997917], [1118894045, 1905616426, 1186639676, 2060776513, 54640703, 583528117, 1840258830, 968916021, 144810782, 8148536, 1725553560, 1752153172, 521652485, 760410082, 1582040848, 1564489988, 1995481932], [1658673008, 474218770, 2104482429, 1092670716, 808581270, 314720440, 758459909, 142620818, 1909476, 5491092, 1292200855, 1734935524, 485260965, 265885821, 1303583411], [67745538, 93969621, 1584371509, 1070817138, 21857484, 548543197, 142151540, 399156, 1299954, 3653536, 861223308, 445313001, 36184750], [607524501, 764868979, 1245643805, 961549989, 338730624, 142063235, 72471, 272397, 871479, 2400533, 431880288], [1147303464, 356210411, 576929773, 1833500493, 1420472966, 10962, 852331415, 426323221, 426716374], [1687082427, 998700350, 1197566302, 1420471139, 1281, 1278430920, 1278455595], [96154957, 561632363, 1420470965, 96, 717], [635933920, 0, 1]],
    [[1193195606, 596597925, 2124, 1704588868, 426335209, 1535346108, 773473233, 27825600, 1807408564, 755104805, 2114293454, 1425231658, 745297934, 1313435332, 291872792, 1074555418, 530534993, 1718981981, 1583491821, 417177731, 700640371, 1152005512, 622602126], [1022739091, 108, 852284375, 1704584710, 1278579369, 1194160702, 4869480, 872817866, 1778400376, 1508133463, 1903723527, 1502013240, 1073588479, 1839071678, 1879028596, 583115004, 616552000, 1599612060, 481061840, 605247902, 1482980651], [852282576, 1875021754, 1363653624, 937526733, 170579426, 742016, 1452523673, 952466163, 137571921, 1010766062, 419610048, 1405549285, 1175196886, 755941925, 195834154, 571415116, 530134629, 1081661765, 2015104253], [681826061, 1960249997, 1022740326, 1022751788, 95480, 256245867, 258368251, 1033473004, 888894026, 107987880, 1982865340, 205293299, 1694451925, 559715228, 1472054047, 1708973080, 957960149], [511369546, 255684837, 1448881369, 9920, 426213901, 1790209389, 1962191183, 859863518, 25243920, 72646392, 1460853255, 2107121524, 1210610125, 1354757040, 2078286624], [340913031, 1022739140, 775, 852290100, 1278477620, 767355373, 853657721, 5259150, 17144829, 48243936, 970501253, 679996951, 479809785], [170456516, 40, 426141865, 852288060, 1704603554, 852493922, 950040, 3576222, 11461554, 31631808, 501911953], [1, 1448880403, 85228661, 85232025, 26091, 142506, 852919100, 428519101, 433679854], [1960249919, 1107967363, 596598051, 2340, 16380, 1278514605, 1278834015], [1789793404, 1107967353, 117, 1170, 8892], [1619336889], [1]]
  ]
private theorem cell_40_18 : (CJ0.blockMatrix source 40 ((18 : ℤ)-24)).rank ≤ 141 :=
  Fast.cell (z := matrix_40_18) (Fast.bands [(16, 16, 1), (17, 17, 2), (18, 18, 3), (19, 19, 4), (20, 20, 5), (21, 21, 6), (22, 22, 7), (23, 23, 8), (24, 24, 9), (25, 25, 10), (26, 26, 11), (27, 27, 11), (28, 28, 11), (29, 29, 11), (30, 30, 11), (31, 31, 10), (32, 32, 9), (33, 33, 8), (34, 34, 7), (35, 36, 5), (36, 38, 3), (37, 40, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_40 (u : ℕ) : ℕ :=
  match u with
  | 17 => 145
  | 18 => 141
  | u => nominal 40 u

private theorem bound_40 (u : ℕ) :
    (CJ0.blockMatrix source 40 ((u : ℤ)-24)).rank ≤ allowance_40 u := by
  unfold allowance_40
  split
  · exact cell_40_17
  · exact cell_40_18
  · exact (block_rank_le 40 _).trans (rank_le_nominal 40 _)

theorem grade_40 : (∑ u ∈ Finset.range (81-40), (CJ0.blockMatrix source 40 ((u : ℤ)-24)).rank) ≤ 2844 := by
  refine (Finset.sum_le_sum fun u _ => bound_40 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_40)]
  decide +kernel

private def matrix_41_16 : CJ1.Block where
  bank := .rightLow
  cap := 142
  free := [(22, 0), (23, 0), (24, 0)]
  vectors := [
    [[0, 0, 0, 0, 1, 2, 1], [0, 0, 0, 8, 10, 2130706431, 2130706429], [0, 0, 0, 28, 0, 2130706380, 2130706413, 6], [0, 0, 56, 2130706321, 2130706265, 52, 60, 2130706429], [0, 0, 70, 2130706069, 2130706391, 504, 115, 2130706363, 1], [0, 56, 2130705845, 812, 1008, 2130705929, 2130706107, 38], [0, 28, 2130705873, 2058, 2130706265, 2130704081, 2130706265, 325, 2130706425], [8, 2130706113, 2472, 2130702793, 2130703745, 2352, 840, 2130706281], [1, 2130706331, 1657, 2130700185, 2520, 5880, 2130705845, 2130705641, 28], [2130706419, 598, 2130701317, 9680, 2520, 2130700553, 2130705425, 336], [91, 2130704301, 10406, 2130697721, 2130698789, 2688, 1092, 2130706377], [2130706069, 5148, 2130691957, 2640, 8064, 168, 2130705985], [1001, 2130697567, 13695, 3696, 2130702023, 2130705621, 70], [2130704431, 11154, 2130698249, 2130700889, 980, 364], [3003, 2130696137, 2112, 3520, 210, 2130706377], [2130703001, 6864, 968, 2130705289, 2130706265], [3003, 2130703287, 2130705256, 120, 28], [2130704431, 858, 500, 32], [1001, 2130706381, 2130706335, 2130706425], [2130706069, 2130706381, 4], [91, 18, 1], [2130706419, 2130706431], [1]],
    [[0, 0, 0, 0, 14, 29, 15], [0, 0, 0, 112, 149, 2130706409, 2130706373], [0, 0, 0, 392, 36, 2130705673, 2130706118, 90], [0, 0, 784, 2130704949, 2130703913, 647, 920, 2130706373], [0, 0, 980, 2130701463, 2130705299, 7224, 1970, 2130705368, 15], [0, 784, 2130698327, 10360, 15456, 2130699881, 2130701284, 576], [0, 392, 2130698677, 27636, 1050, 2130672329, 2130702401, 5036, 2130706312], [112, 2130701989, 33720, 2130660303, 2130662753, 31752, 13944, 2130704098], [14, 2130705014, 22775, 2130623185, 23940, 87612, 2130702317, 2130693833, 428], [2130706238, 8256, 2130637077, 123640, 51660, 2130624113, 2130687617, 5256], [1260, 2130677274, 138358, 2130606245, 2130585305, 32340, 18144, 2130705565], [2130701428, 69576, 2130519609, 10032, 118188, 8400, 2130699237], [13650, 2130588458, 167673, 73920, 2130647213, 2130691663, 1106], [2130679406, 145288, 2130617993, 2130617729, 9310, 6104], [40040, 2130576446, 9372, 51260, 5460, 2130705523], [2130661388, 82368, 24244, 2130691737, 2130703367], [38610, 2130672256, 2130686490, 624, 476], [2130681408, 6864, 7396, 760], [12012, 1131, 2130705223, 2130706285], [2130702338, 2130705289, 2130706417], [910, 291, 23], [2130706328, 2130706409], [0, 2130706432], [1]],
    [[0, 0, 0, 0, 105, 224, 120], [0, 0, 0, 840, 1176, 2130706289, 2130705953], [0, 0, 0, 2940, 504, 2130700661, 2130703793, 720], [0, 0, 5880, 2130695849, 2130686561, 4056, 7520, 2130705953], [0, 0, 7350, 2130669977, 2130694589, 54432, 17790, 2130697793, 120], [0, 5880, 2130646457, 71400, 122976, 2130663089, 2130663113, 4656], [0, 2940, 2130648809, 199836, 27720, 2130448889, 2130661073, 41604, 2130705457], [840, 2130673337, 247248, 2130389753, 2130348593, 218736, 122976, 2130687305], [105, 2130695849, 168108, 2130108209, 115290, 670320, 10584, 2130599585, 3489], [2130704977, 61176, 2130200465, 856680, 468720, 2130120785, 2130522977, 43848], [9360, 2130492089, 993036, 2130076793, 2129750345, 176400, 160524, 2130699257], [2130669473, 506376, 2129398313, 2130646241, 867888, 123480, 2130644777], [100100, 2129858729, 1123452, 643104, 2130322763, 2130564473, 9324], [2130509873, 1026168, 2130177377, 2130024521, 15960, 54600], [288288, 2129810681, 2130687029, 357720, 66780, 2130698537], [2130386113, 545688, 215688, 2130624593, 2130676697], [270270, 2130497081, 2130556613, 2130697649, 4326], [2130534833, 30888, 48144, 9048], [80080, 13416, 2130701381, 2130704969], [2130680225, 2130698009, 2130705305], [5460, 1656, 276], [2130705873, 2130706409], [0, 2130706409], [], [1]]
  ]
private theorem cell_41_16 : (CJ0.blockMatrix source 41 ((16 : ℤ)-24)).rank ≤ 142 :=
  Fast.cell (z := matrix_41_16) (Fast.bands [(0, 18, 24), (1, 19, 22), (2, 20, 20), (3, 21, 18), (4, 22, 16), (5, 23, 14), (6, 24, 12), (7, 25, 10), (8, 26, 8), (9, 27, 6), (10, 28, 4), (11, 29, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_41_17 : CJ1.Block where
  bank := .leftLow
  cap := 139
  free := [(9, 4), (10, 0), (10, 1), (10, 2), (11, 0)]
  vectors := [
    [[1734635998, 1761369631, 164349046, 169013978, 1218892211, 1671031646, 1307437000, 2087649393, 1813146925, 307484281, 541267976, 1098936153, 779960, 1148881383, 1712119299, 871045231, 264556133, 1929384516, 1541196776, 2088722286, 2088722286, 737293243, 383993508], [708889825, 347626939, 1331388749, 378666663, 1834931997, 1514666770, 1718129984, 1315782013, 731507202, 304419759, 1098683193, 227664, 499596, 820483505, 48559126, 1290538805, 121013105, 1152407447, 169873241, 1262885081, 1972832982], [1813850085, 985376593, 1539785492, 1316855702, 1165514646, 1380280894, 1232080074, 135733559, 777884313, 1098613629, 1420532790, 1420619218, 316200, 1202539634, 1881983361, 1102057141, 603156477, 439792926, 1751328704], [788103912, 1543912160, 1973713622, 1973982754, 1469542435, 794563119, 447923279, 1860142009, 83973851, 1420486414, 1014662966, 101557573, 1623593128, 367190767, 1631805769, 1046739894, 1694835007], [1893064172, 2023233640, 1686641053, 1182021304, 1670852071, 754911201, 202924682, 83969759, 608776774, 608783594, 1623422008, 1217607116, 1522055395, 648016683, 1428627383], [867317999, 292634600, 1862742132, 1875929529, 752309558, 676414780, 388355542, 1521933875, 2356, 1623402168, 202941546, 1420508982, 811772384], [1972278259, 613527906, 1555484773, 440118133, 1149905064, 388355387, 124, 1217547007, 1550, 1420475347, 1319019609], [946532086, 855207125, 1949043323, 1623395378, 388355363, 18, 81, 913160207, 608774263], [2051492346, 1017672257, 2096885696, 388355360, 2, 11, 50], [1025746173, 1100923302, 2078225979, 220417907, 1]],
    [[708488496, 1464285837, 321496648, 1746900030, 1995647691, 1476930476, 1167834871, 2094858623, 908995131, 82887001, 1226359122, 2064422459, 1610267597, 1452401701, 1379383903, 2128744028, 1580063378, 1720984991, 572600966, 73614069, 1774774981, 1952652614, 1414110663], [104962775, 939462372, 1622665482, 1370187872, 1850029608, 650787828, 854472298, 914434681, 2107391495, 287334780, 1418571509, 1290092313, 1710049205, 950595379, 231516282, 2125964574, 1293356987, 775354265, 936515108, 1266018422, 1114630316], [566790329, 1621692221, 2057970324, 632230306, 1125069329, 658613408, 1609772553, 10210790, 305188156, 1365782759, 427576673, 823036576, 303774026, 1326985541, 621531230, 2054947953, 1616510283, 1540634018, 1373423569], [2093971158, 314915559, 882181787, 1931253431, 1183687699, 762539406, 1038325841, 1866962158, 1559023800, 325772642, 1110986245, 1462461441, 218824628, 1980453303, 510582700, 1239356685, 1004933061], [425092396, 215191860, 1611483701, 1556771028, 381890834, 925068602, 1943648568, 1788427181, 1641601380, 1103741417, 240116494, 1764990739, 1844049115, 894185488, 607919656], [1952273342, 257167732, 1369940948, 343116140, 1704656716, 1304949337, 2096503899, 1318415559, 2094541934, 1902131129, 1468586687, 1596425733, 1005188691], [283394697, 1506196216, 1543031627, 1538734054, 160111552, 1716341649, 235845675, 841766603, 411271188, 1800851139, 1049919400], [1810575760, 766217487, 1385527755, 152649551, 1672475424, 22657050, 117869895, 669717787, 270671878], [141697232, 1233291019, 152201700, 603642920, 1066495429, 1073745334, 1114674274], [1668878412, 1842063420, 1962764182, 918385100], [1]],
    [[1663630211, 1023362637, 246553531, 40832119, 1643782500, 932208642, 386133398, 516422340, 1281263537, 2119574926, 859206283, 1694595729, 1309854236, 174367618, 1357450687, 1484672518, 1114053690, 447421800, 2115169671, 1100172862, 833371008, 1294140713, 1860698348], [325378672, 1527176448, 446005835, 697152344, 2050597396, 1685211724, 1110726846, 1815205640, 1268171184, 1486330069, 1849763665, 899550004, 705449638, 685586458, 415155663, 1800462926, 943340837, 1320104381, 876988356, 263188114, 1311405723], [52480345, 446080327, 1689814295, 550454827, 1060784339, 1735427508, 668052319, 108995781, 1787036879, 808578973, 1818709730, 201299689, 1472655626, 1677286012, 406447690, 627355160, 1317395123, 969627405, 1888778033], [844935230, 976133937, 1028577929, 750071553, 773682194, 1608708017, 1830856957, 841363712, 286082637, 2117820699, 597271459, 1087896410, 403425206, 1140301016, 1645055969, 1823049545, 927216407], [572036894, 2051984075, 1905015027, 1406220554, 1530518066, 691896469, 1161982328, 1411983231, 695987545, 1069049778, 487082405, 545211301, 1047121252, 1468944293, 1188502675], [1364491770, 477571105, 1369724553, 1590005954, 1615270209, 1210869731, 240182502, 1538146367, 1643237633, 1823678059, 220874063, 1526299049, 2068785026], [1091593425, 1579661123, 734718310, 1464124447, 151590517, 269275371, 2112662108, 1902326686, 788480029, 190406254, 1232173518], [1884048292, 31488060, 1312008074, 152158909, 272625315, 2128977758, 2121680468, 112469017, 307089426], [1611149938, 1159818012, 152192728, 1338242893, 1065266929, 1064711764, 1061562124], [272898363, 1768591343, 2036242011, 183683455], [0, 1]],
    [[488068229, 582533268, 1593660297, 482862511, 1433059989, 1287963735, 48197306, 470310352, 1156660642, 651889972, 1534562551, 452481761, 440923481, 1922489620, 127860414, 1414276083, 1350405786, 1212852706, 67391425, 1604288522, 1456339966, 414749855, 1007955224], [545796727, 1404726994, 1401230986, 747002542, 220661511, 1213818298, 1722139262, 1586993208, 450057721, 810117822, 1099333377, 816540013, 330081901, 1006745352, 570487342, 1949971354, 245471582, 1575362222, 1928703142, 901750361, 959044853], [958642964, 690992774, 612274028, 477593757, 1775756215, 1813348938, 1841958829, 2072055550, 1195810187, 196740477, 716903396, 1796400710, 1895420737, 1710705961, 72474688, 2080313892, 1305410952, 257319909, 1226602572], [1726606940, 1637390257, 465328118, 1705629355, 409458425, 1309178926, 1850609112, 1231350408, 296478396, 157104156, 132694501, 1689124728, 1471046823, 1669817410, 452366946, 2084620657, 2098837031], [718982222, 1047859793, 68225519, 1969775707, 1287590316, 630180376, 1929817211, 255116646, 1552256401, 1616882845, 1479543166, 1554185517, 2005346738, 1194745545, 1986335229], [66475243, 2118461031, 659504928, 1418727131, 832730981, 507554900, 1008821756, 1679110373, 17893200, 1273577926, 306440847, 1440631854, 1418480003], [1899792436, 1653134321, 1346998610, 1390734935, 152215212, 1007756756, 659556, 1981304611, 1075517104, 1097517979, 1611008470], [1957520935, 717232879, 1238538831, 862430027, 1007634581, 62856, 329745, 153649312, 462071136], [239660740, 376109921, 1572664291, 2072978235, 1065356305, 1065376519, 1065491959], [1007624717, 1695118663, 2109714236, 1579661594], [0, 0, 1]],
    [[467076222, 1107343796, 1884152902, 2089874314, 486923933, 1198497791, 1744573035, 1614284093, 849442896, 11131507, 1271500150, 436110705, 820852197, 1956338815, 773255746, 646033915, 1016652743, 1683284633, 15536762, 1030533571, 1297335425, 836565720, 270008085], [1805327761, 603529985, 1684700598, 1433554089, 80109037, 445494709, 1019979587, 315500793, 862535249, 644376364, 280942769, 1231156429, 1425256795, 1445119975, 1715550770, 330243507, 1187365596, 810602052, 1253718077, 1867518319, 819300710], [2078226088, 1684626106, 440892138, 1580251606, 1069922094, 395278925, 1462654114, 2021710652, 343669554, 1322127461, 311996703, 1929406744, 658050807, 453420421, 1724258743, 1503351273, 813311310, 1161079028, 241928400], [1285771203, 1154572496, 1102128504, 1380634880, 1357024239, 521998416, 299849476, 1289342721, 1844623797, 12885734, 1533434974, 1042810023, 1727281227, 990405417, 485650464, 307656888, 1203490026], [1558669539, 78722358, 225691406, 724485879, 600188367, 1438809964, 968724105, 718723203, 1434718888, 1061656655, 1643624028, 1585495132, 1083585181, 661762140, 942203758], [766214663, 1653135328, 760981880, 540700479, 515436224, 919836702, 1890523932, 592560066, 487468800, 307028374, 1909832370, 604407384, 61921407], [1039113008, 551045310, 1395988123, 666581986, 1979115916, 1861431063, 18044325, 228379747, 1342226404, 1940300179, 898532915], [246658141, 2099218373, 818698359, 1978547524, 1858081119, 1728675, 9025965, 2018237416, 1823617007], [519556495, 970888421, 1978513705, 792463541, 1065439504, 1065994669, 1069144309], [1857808070, 362115090, 94464423, 1947022978], [], [1]]
  ]
private theorem cell_41_17 : (CJ0.blockMatrix source 41 ((17 : ℤ)-24)).rank ≤ 139 :=
  Fast.cell (z := matrix_41_17) (Fast.bands [(17, 17, 1), (18, 18, 2), (19, 19, 3), (20, 20, 4), (21, 21, 5), (22, 22, 6), (23, 23, 7), (24, 24, 8), (25, 25, 9), (26, 26, 10), (27, 27, 11), (28, 28, 11), (29, 29, 11), (30, 30, 11), (31, 31, 11), (32, 32, 10), (33, 33, 9), (34, 34, 8), (35, 36, 6), (36, 38, 4), (37, 40, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_41 (u : ℕ) : ℕ :=
  match u with
  | 16 => 142
  | 17 => 139
  | u => nominal 41 u

private theorem bound_41 (u : ℕ) :
    (CJ0.blockMatrix source 41 ((u : ℤ)-24)).rank ≤ allowance_41 u := by
  unfold allowance_41
  split
  · exact cell_41_16
  · exact cell_41_17
  · exact (block_rank_le 41 _).trans (rank_le_nominal 41 _)

theorem grade_41 : (∑ u ∈ Finset.range (81-41), (CJ0.blockMatrix source 41 ((u : ℤ)-24)).rank) ≤ 2694 := by
  refine (Finset.sum_le_sum fun u _ => bound_41 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_41)]
  decide +kernel

private def matrix_42_15 : CJ1.Block where
  bank := .rightLow
  cap := 138
  free := [(23, 0), (24, 0)]
  vectors := [
    [[0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 9, 4, 2130706429], [0, 0, 0, 36, 2130706415, 2130706398, 6], [0, 0, 0, 84, 2130706265, 2130706352, 80, 2130706429], [0, 0, 126, 2130705887, 168, 360, 2130706348, 1], [0, 0, 126, 2130705425, 1344, 504, 2130705848, 44], [0, 84, 2130705257, 3402, 2130705257, 2130704753, 486, 2130706424], [0, 36, 2130705545, 4830, 2130700385, 2130705257, 2184, 2130706226], [9, 2130706010, 4224, 2130695093, 5292, 4116, 2130704921, 36], [1, 2130706317, 2268, 2130694553, 16380, 0, 2130701729, 552], [2130706419, 689, 2130699107, 21780, 2130692321, 2130701141, 2856, 2130706349], [91, 2130703937, 15840, 2130679505, 5292, 6048, 2130705509], [2130706069, 6149, 2130682376, 22176, 2520, 2130703031, 126], [1001, 2130695565, 26136, 2130695345, 2130702023, 1008], [2130704431, 14157, 2130686237, 1980, 2520, 2130706307], [3003, 2130692705, 10692, 1320, 2130705719], [2130703001, 9867, 2130702968, 2130705377, 84], [3003, 2130701285, 396, 312], [2130704431, 1859, 162, 2130706397], [1001, 2130706017, 2130706361], [2130706069, 39, 9], [91, 4], [2130706419, 2130706432], [1]],
    [[0, 0, 0, 0, 14, 15], [0, 0, 0, 0, 126, 66, 2130706373], [0, 0, 0, 504, 2130706226, 2130705893, 90], [0, 0, 0, 1176, 2130704201, 2130705029, 1220, 2130706373], [0, 0, 1764, 2130698999, 1512, 5715, 2130705143, 15], [0, 0, 1764, 2130692573, 17136, 9576, 2130697343, 666], [0, 1176, 2130690179, 45360, 2130695849, 2130678713, 7479, 2130706297], [0, 504, 2130694121, 65520, 2130630833, 2130678209, 34776, 2130703265], [126, 2130700556, 57816, 2130557123, 52920, 72324, 2130682745, 549], [14, 2130704819, 31212, 2130546713, 204120, 31752, 2130628817, 8568], [2130706238, 9516, 2130606839, 285120, 2130552965, 2130600593, 45864, 2130705137], [1260, 2130672269, 211860, 2130369041, 21168, 105840, 2130691817], [2130701428, 83226, 2130391910, 255024, 79380, 2130649733, 1974], [13650, 2130561431, 330264, 2130606641, 2130619493, 16380], [2130679406, 185328, 2130465269, 2130694553, 44730, 2130704417], [40040, 2130531401, 114048, 38280, 2130694337], [2130661388, 120978, 2130680198, 2130685049, 1386], [38610, 2130647231, 2130702077, 5688], [2130681408, 18876, 5238, 2130705809], [12012, 2130703469, 2130704885], [2130702338, 2130706199, 171], [910, 186], [2130706328, 2130706409], [], [1]]
  ]
private theorem cell_42_15 : (CJ0.blockMatrix source 42 ((15 : ℤ)-24)).rank ≤ 138 :=
  Fast.cell (z := matrix_42_15) (Fast.bands [(0, 19, 24), (1, 20, 22), (2, 21, 20), (3, 22, 18), (4, 23, 16), (5, 24, 14), (6, 25, 12), (7, 26, 10), (8, 27, 8), (9, 28, 6), (10, 29, 4), (11, 30, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_42_16 : CJ1.Block where
  bank := .leftLow
  cap := 137
  free := [(9, 2), (9, 3), (9, 4), (10, 0), (10, 1), (10, 2), (11, 0)]
  vectors := [
    [[801426217, 1549365917, 920681754, 810260847, 1941843545, 800449242, 1049179929, 238992982, 1848334735, 1805416356, 1802526321, 281208411, 483213209, 1537652052, 163039765, 1094932081, 561193385, 1379502032, 1793618375, 126910973, 226072992, 802400096, 1711559568], [1404687952, 305138439, 1459932209, 1878217685, 311640, 2085322665, 515352604, 1908446410, 1284017054, 1877726596, 183961245, 1072038107, 1219017292, 82554749, 60547158, 980322636, 1511579771, 1185006405, 551403742, 1166418336, 1699227416], [1267901857, 775296688, 1737185443, 644494508, 2043191792, 1279482579, 459040215, 50437639, 2106680606, 1778285210, 1019761731, 1997278686, 931412435, 1610750568, 2018239467, 460412774, 1049480364, 1395270809, 537500222], [61203010, 1676155793, 368271253, 2118441149, 199999706, 714961583, 1575438116, 480756365, 26064615, 5637248, 1724293697, 1327063823, 766357819, 1125151180, 1179181008, 1546978614, 1111876365], [1716139355, 912784138, 2093879779, 2104405360, 1068016079, 885116589, 1326978100, 992186241, 1759872226, 1900874683, 1094563912, 2038661112, 1409729387, 257987493, 803773056], [1641433104, 1971122661, 1696673686, 252528870, 329697313, 368334756, 1499808693, 1185990477, 2046201511, 607490984, 1933559526, 2044276569, 1952147043], [1637925768, 1133746256, 2009703274, 530483986, 815453544, 1420472242, 1436331533, 2060333072, 808576174, 1370742512, 926800229], [1375752425, 264102371, 2094931526, 1246857170, 1010108885, 599739234, 378756423, 1941338212, 119195424], [525048153, 414391709, 336704187, 528730513, 1909742095, 1444134710, 899590378], [886654463, 1825568228, 1]],
    [[529395705, 1381143419, 1824150331, 1215622711, 859958374, 1092754678, 1550254724, 1948429330, 168772040, 585107769, 2011525904, 163168819, 1625192482, 425361667, 2045821458, 1202158162, 620128802, 1180119835, 940922745, 342278194, 944992632, 1759206645, 1164546564], [237525636, 2073124403, 38372611, 1763351448, 491624203, 1988171544, 720430045, 34397880, 1756155694, 491833725, 970674884, 692031697, 621447446, 1420433292, 1198661426, 308267861, 1745857081, 876183671, 1382634009, 497334688, 2103057349], [1738039003, 1696607122, 404322044, 981879825, 407684341, 802840439, 131645564, 1675337520, 1472684540, 824600505, 1624459633, 398089076, 57334459, 116549666, 1829819137, 356370022, 22582409, 1653250694, 995845729], [1448981547, 343254447, 1123021633, 121000224, 335670164, 693583691, 1186793456, 1164634550, 753102854, 397355966, 1284029126, 1946571097, 1291020356, 550393962, 1627691621, 1855375010, 353219542], [49811875, 1779014120, 515202441, 270998241, 2069645649, 750790392, 1237489913, 243588846, 2056604431, 349285134, 57637023, 1967762298, 1303917963, 592429752, 1196910935], [350695027, 659880156, 1685183228, 2100007213, 320888813, 1544455666, 1657072495, 2028538036, 321698060, 476076088, 1912243802, 967068, 912431712], [900383177, 1708250740, 139098624, 525016337, 28183388, 1065347094, 757539120, 1232505752, 130680314, 262905865, 1775947193], [247628499, 536570330, 1233017364, 2015716010, 1609867443, 23675026, 1136370566, 649292023, 430811718], [1202596033, 692981121, 1399051162, 1408633753, 47349356, 603701505, 1633545126], [183331520, 877084447, 0, 1]],
    [[843726216, 1732055342, 582757427, 630974765, 276299273, 1404144187, 1215627028, 1939696659, 1228110187, 686287996, 320766159, 218763059, 1834864406, 139670542, 446131423, 295240889, 395072073, 2030466373, 12970676, 1321084865, 575932294, 870293336, 1288197386], [1396015961, 1541184975, 139185412, 225298899, 692030337, 1136414825, 1336898691, 1564965554, 1044064224, 1499767896, 1032981973, 1137359790, 1228371493, 922661227, 925635245, 1713385575, 676662391, 604001472, 1008166421, 1487815551, 1450932544], [597846567, 2120513964, 1593806611, 852890056, 1288949346, 1114545126, 1439037994, 1248179866, 1677184015, 672817578, 1645415201, 100789947, 793014738, 438177419, 1851241636, 427772953, 1626054866, 1635800974, 263350682], [92229439, 1413394618, 2112495290, 1346817145, 1345200000, 275364482, 308760158, 915684526, 619964109, 413918902, 1431256558, 171272267, 1412724871, 1121443105, 1948892738, 855231795, 96176092], [1522175982, 1444665791, 455452603, 1741334472, 755504132, 1626072049, 1461086032, 287612976, 68179390, 340068072, 1345007422, 1402258799, 1086684881, 60734217, 343441988], [138578302, 1928533583, 623082044, 1672131971, 633980199, 1769954343, 473503831, 1521996867, 954004347, 129443749, 245289241, 2037353630, 155436459], [1845860670, 268571340, 586919868, 7660263, 1984150013, 1420471782, 94703178, 1856784701, 365378239, 1685829699, 1049853141], [1894915192, 80545386, 196923409, 2103649842, 1089027740, 1467820147, 142048503, 487027387, 1166858920], [1928753273, 538882858, 565933666, 1396796437, 1515169008, 1207400292, 1846612394], [1459679885, 638084572, 0, 0, 1]],
    [[473482510, 1775322414, 705765636, 1371193553, 1729098257, 613972474, 559136673, 820191237, 1426707775, 316950030, 2130432988, 1856830622, 1365679441, 2020816890, 820825672, 502738961, 775573526, 285191381, 1289642886, 404408374, 555211943, 1715625510, 82871345], [2130700732, 710046180, 1062255006, 2097354117, 1864866733, 456479606, 1973359433, 248988418, 369082512, 771835558, 1256351167, 845748831, 1795637224, 251581842, 157880197, 934652126, 530700441, 1198741194, 406255239, 2029804430, 1192597094], [710231468, 1301968751, 708166087, 333345353, 303536039, 1080359597, 327836456, 526850160, 54340322, 2118809827, 2070056113, 1172770099, 991843194, 554495762, 196468501, 1518005265, 683278167, 1109098872, 1181643999], [1538840846, 2130621785, 708916246, 1643630492, 606159095, 787604054, 132781894, 2030269802, 1851626845, 1525668227, 789174083, 809722605, 309311663, 1245628943, 2043614028, 1151696836, 1378519430], [1420469262, 1775536758, 709444120, 1412475022, 1360160662, 347968775, 326293401, 1929852071, 1599707822, 2129794722, 1975232009, 1206432313, 2054376745, 1290209914, 1340601319], [1420469978, 946951397, 1064916504, 705889257, 914541517, 1226827988, 1168533858, 174702706, 1933519000, 1861430276, 1630117466, 92402352, 373856440], [473489823, 355103247, 710022373, 826505666, 694580861, 2036936393, 1660795537, 1174600164, 928685516, 726996289, 232221465], [1775588492, 710229671, 1420386203, 2129868158, 2124390214, 2092092585, 1931665136, 1244170952, 1862838245], [2130706381, 591861417, 1420449127, 1065131768, 2128968697, 1054101658, 2068152032], [473490319, 710235484], [1]],
    [[1518676942, 1504667093, 500133189, 1040149139, 645989473, 890406547, 999094747, 208741848, 961054165, 143600393, 1136884777, 1256623539, 956196285, 1435999560, 1041134051, 447828571, 688256504, 1704876385, 1096294921, 41062811, 738336145, 2088654787, 1401522480], [2004442781, 1967629736, 1736367558, 1533500743, 20334720, 1880029647, 1863612484, 1476867251, 1407546466, 1294341544, 2026125450, 1625119672, 347452591, 445038084, 931767199, 1840849030, 1004576754, 682705950, 1324795547, 530395591, 1993961915], [1857134557, 1720007405, 1444831213, 1843032751, 574305206, 1785700108, 1294955702, 1057471923, 956963716, 1416146821, 684824087, 196113239, 441473580, 1769661307, 1331305925, 109155554, 547853634, 220084932, 885602189], [350943, 198872541, 1052303818, 1954648332, 1370735559, 1408859596, 171525250, 1725201363, 1583280783, 193609993, 1235045003, 1876295168, 672474532, 941248538, 775177289, 1104933024, 639255589], [1749809911, 1146902893, 1599407910, 1447410535, 499313702, 1047173360, 94891787, 680436919, 472064286, 1057730685, 61395654, 232759048, 660374412, 1545026767, 2082787814], [1767697268, 1958849353, 1499421361, 600105546, 193762851, 1067739512, 708179764, 1271764964, 436750016, 2024676901, 477731906, 1528897605, 1610495022], [1108318120, 73655255, 689209139, 1718768155, 2026772939, 717896756, 1584878638, 1725458984, 654986791, 1001133271, 727384385], [825977573, 1497282107, 518742203, 31637268, 268843795, 1960321732, 916123713, 688311299, 1228607512], [1974980733, 1626351694, 1509909965, 1388924506, 1073396588, 900603572, 810275391], [1348219840, 163091109], [0, 1]],
    [[1033247585, 1802702405, 96102809, 439569191, 576236991, 339811155, 2065771133, 1365948097, 1987888411, 757955287, 1645932353, 1487788371, 1157436775, 996308789, 222713603, 611961553, 1721119363, 829272677, 79700274, 245942881, 792864088, 1153540204, 494092428], [1188582092, 1132329335, 1317266067, 2080839794, 1638290480, 611034848, 1305481276, 2129285594, 56820019, 772235458, 1610096914, 2089561923, 1192262817, 1642424252, 579461989, 730044768, 247867542, 443109846, 1974880103, 1134845270, 1846122061], [1783075496, 672409857, 257055049, 2102318073, 1810194302, 1324705881, 1614687271, 384556594, 153908598, 699312849, 1867780934, 2065371776, 1941431864, 1003296457, 577161435, 605771731, 1157297179, 231281648, 298432321], [144664100, 2041107257, 284292805, 1027610892, 742518900, 777572561, 1889996172, 30470761, 1233701103, 554659175, 366818085, 1789112589, 1653839535, 1565315804, 1440095249, 1165876901, 901855660], [2124109939, 499188145, 2017592535, 59668732, 1996172489, 518250340, 1936113281, 1714268808, 78048784, 296319095, 2094933311, 189183180, 1491280727, 1900934438, 873082760], [787936450, 1995673919, 42491382, 650732410, 1753974304, 1130534797, 36602341, 1645237439, 1187367206, 995866900, 795372380, 868335126, 254336112], [1986905668, 1860776435, 935648555, 2115186480, 1591404006, 1775295925, 1213847131, 1982546557, 1232180187, 1728344303, 1996576117], [918247463, 1851549471, 805621225, 1546732182, 1428341316, 15656292, 401827147, 328655431, 581209566], [1302017437, 1629062995, 1186356215, 939088311, 386677487, 402427236, 23460533], [466151893, 889109598], [0, 0, 1]],
    [[1941309707, 1207379856, 709891490, 280296447, 1673579848, 439850644, 82431757, 1682971603, 1452023966, 181689684, 1322001768, 592874484, 691296939, 1287761254, 926532617, 587945781, 881256544, 1177034449, 1371499570, 1962732649, 1166297296, 1370357983, 1148330818], [852282133, 1988644691, 1065113099, 849694438, 2110060073, 296060554, 1882447778, 876099205, 1569849346, 1089344726, 2051326172, 1564255087, 564236550, 1603113600, 1138392076, 1440241200, 1745256341, 262994078, 254507144, 433892506, 568223535], [1136376452, 1766108773, 1079396210, 1773885607, 1643915868, 1196230179, 376710516, 1022796871, 1197768544, 1066980836, 426120615, 2068020941, 757820418, 881000991, 911867474, 1561138105, 533372435, 515350692, 707604022], [2069152480, 255678099, 710131362, 188323385, 559971168, 6885254, 383743067, 2055455138, 521361036, 1931459192, 1302074166, 1058053875, 691874082, 64306715, 176348136, 1609501228, 379574479], [795463600, 71019402, 568125177, 709596971, 563376652, 198416484, 708836546, 458083274, 2029476354, 1302807498, 974746867, 1989992706, 60602634, 327692173, 1374851996], [852282494, 331440852, 1065317819, 1278072017, 1607246269, 694632165, 2053424410, 1803657425, 1778461339, 1629244981, 1850121434, 688238692, 698770801], [1515168978, 923304922, 1562500453, 2012160725, 1419186383, 2123043869, 1240202695, 475620810, 667143468, 1889537083, 476521819], [2059682868, 369321955, 1647739137, 852211995, 851753754, 1701351900, 835826297, 1631763355, 782903497], [1761383980, 89963030, 284092281, 213051415, 1278274183, 1916674584, 420840664], [2026538563, 142047096], [], [1]]
  ]
private theorem cell_42_16 : (CJ0.blockMatrix source 42 ((16 : ℤ)-24)).rank ≤ 137 :=
  Fast.cell (z := matrix_42_16) (Fast.bands [(18, 18, 1), (19, 19, 2), (20, 20, 3), (21, 21, 4), (22, 22, 5), (23, 23, 6), (24, 24, 7), (25, 25, 8), (26, 26, 9), (27, 27, 10), (28, 28, 11), (29, 29, 11), (30, 30, 11), (31, 31, 11), (32, 32, 11), (33, 33, 10), (34, 34, 9), (35, 36, 7), (36, 38, 5), (37, 40, 3), (38, 42, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_42_17 : CJ1.Block where
  bank := .leftLow
  cap := 131
  free := [(10, 1)]
  vectors := [
    [[228289975, 152193318, 684869950, 1826320101, 1598032461, 1065371143, 532775204, 609223990, 1828066353, 1832141644, 625656615, 42975796, 96695541, 193391082, 1562887751, 2074479115, 1250864751, 114738078, 133861091, 1262330850, 133861091, 114738078], [228289975, 2054609776, 760966607, 1065353494, 532678967, 532692176, 83028, 609140962, 1218925391, 613216253, 12440362, 30535434, 66160107, 127230975, 1435656776, 638822339, 612042412, 1633402099, 631165425, 631165425], [228289975, 1826319801, 1065353239, 255, 532678712, 13464, 69564, 609071398, 609853993, 3362260, 9078102, 21457332, 44702775, 82528200, 1353128576, 1416400196, 1326348649, 307053450], [228289975, 1598029826, 1598029846, 532676842, 1870, 11594, 57970, 609013428, 840565, 2521695, 6556407, 14900925, 29801850, 52726350, 1300402226, 115997970], [228289975, 1369739851, 228289995, 304386847, 1826321456, 304396571, 1826367832, 913352029, 1218194969, 915033159, 1222229681, 923377677, 1237130606, 946302177], [228289975, 1141449876, 1217546552, 1217546728, 608774728, 1826328276, 39556, 913312473, 304882496, 610150663, 612079018, 311298659], [228289975, 913159901, 304386651, 913160077, 1826321084, 7192, 32364, 913280109, 1522308820, 1218548276], [228289975, 684869926, 1750223158, 1293643352, 532677732, 1598035893, 532702904, 380577205], [228289975, 456579951, 1293643207, 145, 532677587, 1065358306], [228289975, 228289976, 1065353231, 1065353347], [228289975, 1]]
  ]
private theorem cell_42_17 : (CJ0.blockMatrix source 42 ((17 : ℤ)-24)).rank ≤ 131 :=
  Fast.cell (z := matrix_42_17) (Fast.bands [(18, 18, 1), (19, 19, 2), (20, 20, 3), (21, 21, 4), (22, 22, 5), (23, 23, 6), (24, 24, 7), (25, 25, 8), (26, 26, 9), (27, 27, 10), (28, 28, 11), (29, 29, 11), (30, 30, 11), (31, 31, 11), (32, 32, 11), (33, 33, 10), (34, 34, 9), (35, 35, 8), (36, 37, 6), (37, 39, 4), (38, 41, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_42 (u : ℕ) : ℕ :=
  match u with
  | 15 => 138
  | 16 => 137
  | 17 => 131
  | u => nominal 42 u

private theorem bound_42 (u : ℕ) :
    (CJ0.blockMatrix source 42 ((u : ℤ)-24)).rank ≤ allowance_42 u := by
  unfold allowance_42
  split
  · exact cell_42_15
  · exact cell_42_16
  · exact cell_42_17
  · exact (block_rank_le 42 _).trans (rank_le_nominal 42 _)

theorem grade_42 : (∑ u ∈ Finset.range (81-42), (CJ0.blockMatrix source 42 ((u : ℤ)-24)).rank) ≤ 2547 := by
  refine (Finset.sum_le_sum fun u _ => bound_42 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_42)]
  decide +kernel

private def matrix_43_14 : CJ1.Block where
  bank := .rightLow
  cap := 134
  free := [(24, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 10, 2130706429], [0, 0, 0, 0, 45, 2130706383, 6], [0, 0, 0, 120, 2130706163, 100, 2130706429], [0, 0, 0, 210, 2130705593, 675, 2130706333, 1], [0, 0, 252, 2130704753, 2520, 2130705533, 50], [0, 0, 210, 2130704165, 5880, 2130702233, 675, 2130706423], [0, 120, 2130704333, 9072, 2130694673, 4200, 2130706163], [0, 45, 2130705113, 9450, 2130685265, 14700, 2130703913, 45], [10, 2130705893, 6600, 2130681233, 31752, 2130694673, 840], [1, 2130706303, 2970, 2130686633, 44100, 2130674681, 5880, 2130706313], [2130706419, 780, 2130696533, 39600, 2130653513, 21168, 2130704753], [91, 2130703573, 22275, 2130650993, 44100, 2130697361, 210], [2130706069, 7150, 2130670793, 55440, 2130681233, 2268], [1001, 2130693563, 41580, 2130666833, 9450, 2130706181], [2130704431, 17160, 2130670793, 19800, 2130704333], [3003, 2130689273, 22275, 2130699833, 210], [2130703001, 12870, 2130696533, 1320], [3003, 2130699283, 2970, 2130706313], [2130704431, 2860, 2130705893], [1001, 2130705653, 45], [2130706069, 130], [91, 2130706423], [2130706419], [1]]
  ]
private theorem cell_43_14 : (CJ0.blockMatrix source 43 ((14 : ℤ)-24)).rank ≤ 134 :=
  Fast.cell (z := matrix_43_14) (Fast.bands [(0, 20, 24), (1, 21, 22), (2, 22, 20), (3, 23, 18), (4, 24, 16), (5, 25, 14), (6, 26, 12), (7, 27, 10), (8, 28, 8), (9, 29, 6), (10, 30, 4), (11, 31, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_43_15 : CJ1.Block where
  bank := .rightLow
  cap := 134
  free := [(20, 1), (21, 1), (22, 0), (22, 1), (23, 0), (24, 0)]
  vectors := [
    [[0, 0, 0, 2130706432, 2130706431, 2130706432], [0, 0, 0, 2130706426, 2130706425, 3, 4], [0, 0, 2130706412, 7, 48, 15, 2130706427], [0, 0, 2130706398, 98, 112, 2130706369, 2130706383, 4], [0, 2130706398, 245, 2130706370, 2130706041, 2130706383, 60, 2130706432], [0, 2130706412, 308, 2130705782, 2130705929, 490, 216, 2130706400], [2130706426, 217, 2130705271, 609, 1470, 2130706335, 2130706201, 7], [2130706432, 82, 2130705431, 2380, 714, 2130704669, 2130706041, 112], [13, 2130705995, 2706, 2130703808, 2130703787, 882, 448, 2130706412], [0, 2130706355, 1408, 2130701758, 840, 3234, 168, 2130706230], [0, 286, 2130703408, 5247, 1764, 2130704459, 2130705992, 35], [0, 2130705718, 4554, 2130702869, 2130703577, 441, 210], [0, 1287, 2130701549, 924, 1995, 161, 2130706398], [0, 2130704717, 3696, 693, 2130705733, 2130706314], [0, 1716, 2130704552, 2130705608, 70, 21], [0, 2130705146, 550, 374, 28], [0, 715, 2130706411, 2130706355, 2130706426], [0, 2130706147, 2130706385, 3], [0, 78, 17, 1], [0, 2130706420, 2130706431], [0, 1]],
    [[0, 0, 0, 2130706420, 2130706406, 2130706419], [0, 0, 0, 2130706342, 2130706321, 36, 56], [0, 0, 2130706160, 63, 644, 225, 2130706349], [0, 0, 2130705978, 1218, 1596, 2130705649, 2130705713, 56], [0, 2130705978, 3115, 2130705992, 2130701141, 2130705523, 855, 2130706419], [0, 2130706160, 3948, 2130698544, 2130698873, 6174, 3248, 2130705965], [2130706342, 2793, 2130691859, 5901, 20286, 2130706139, 2130703045, 99], [2130706420, 1058, 2130693707, 28700, 13146, 2130683501, 2130699965, 1616], [168, 2130700834, 33726, 2130677768, 2130667919, 9702, 6804, 2130706132], [0, 2130705432, 17788, 2130649838, 2520, 43806, 4536, 2130703430], [0, 3640, 2130668802, 60291, 31164, 2130681947, 2130699188, 511], [0, 2130697424, 55462, 2130670397, 2130664601, 3549, 3234], [0, 16016, 2130648782, 2772, 26775, 3479, 2130705908], [0, 2130685412, 41448, 14553, 2130698173, 2130704452], [0, 20592, 2130687392, 2130693728, 210, 329], [0, 2130691418, 3982, 5082, 588], [0, 8008, 979, 2130705551, 2130706314], [0, 2130703430, 2130705501, 2130706412], [0, 728, 251, 21], [0, 2130706342, 2130706411], [0, 0, 2130706432], [0, 1]],
    [[0, 0, 0, 2130706423, 2130706411, 2130706421], [0, 0, 0, 2130706363, 2130706336, 22, 47], [0, 0, 2130706223, 6, 509, 210, 2130706364], [0, 0, 2130706083, 840, 1392, 2130705931, 2130705813, 45], [0, 2130706083, 2254, 210, 2130702281, 2130705403, 710, 2130706422], [0, 2130706223, 2898, 2130701379, 2130699503, 4164, 2915, 2130706055], [2130706363, 2058, 2130696395, 1554, 16170, 1140, 2130703570, 78], [2130706423, 776, 2130697517, 17780, 14532, 2130690263, 2130700097, 1316], [120, 2130702535, 22188, 2130693203, 2130674093, 4410, 5928, 2130706195], [2130706432, 2130705773, 11683, 2130672323, 2130697613, 32340, 6090, 2130703955], [13, 2200, 2130683322, 31230, 31164, 2130691397, 2130699713, 406], [2130706355, 2130701483, 31405, 2130694697, 2130673169, 2130706139, 2730], [286, 7920, 2130677096, 2130697865, 18270, 3878, 2130706013], [2130705718, 2130697193, 17886, 14994, 2130702163, 2130704683], [1287, 7920, 2130700757, 2130696743, 2130705803, 266], [2130704717, 2130701483, 2130705795, 3180, 588], [1716, 2200, 1540, 2130706061, 2130706335], [2130705146, 2130705773, 2130705744, 2130706367], [715, 120, 137, 18], [2130706147, 2130706423, 2130706426], [78, 0, 2130706432], [2130706420], [1]],
    [[0, 0, 0, 2130706342, 2130706238, 2130706328], [0, 0, 0, 2130705796, 2130705601, 225, 420], [0, 0, 2130704522, 273, 4592, 1800, 2130705803], [0, 0, 2130703248, 8190, 11928, 2130701449, 2130700883, 420], [0, 2130703248, 21385, 2130705488, 2130668801, 2130697963, 6525, 2130706328], [0, 2130704522, 27300, 2130654528, 2130648473, 40278, 26096, 2130702878], [2130705796, 19383, 2130607523, 30345, 145530, 6762, 2130679945, 750], [2130706342, 7358, 2130619115, 188300, 110670, 2130552965, 2130649985, 12488], [1170, 2130667801, 227766, 2130534758, 2130422723, 48510, 55272, 2130704122], [0, 2130699503, 121528, 2130333368, 2130683753, 301350, 52920, 2130682640], [0, 25025, 2130452586, 380457, 249900, 2130557963, 2130643118, 3997], [0, 2130645008, 367774, 2130504077, 2130406553, 1155, 26670], [0, 108108, 2130333467, 2130687029, 174825, 37205, 2130702212], [0, 2130566293, 257664, 118503, 2130663733, 2130688828], [0, 135135, 2130597302, 2130617498, 2130699923, 2765], [0, 2130609908, 15994, 30954, 6300], [0, 50050, 9988, 2130703031, 2130705348], [0, 2130688415, 2130700041, 2130705530], [0, 4095, 1343, 231], [0, 2130705978, 2130706411], [0, 0, 2130706411], [], [0, 1]],
    [[0, 0, 0, 2130706293, 2130706117, 2130706256], [0, 0, 0, 2130705453, 2130705012, 276, 694], [0, 0, 2130703493, 2130706301, 7252, 3220, 2130705413], [0, 0, 2130701533, 11340, 20496, 2130699972, 2130697113, 666], [0, 2130701533, 31052, 5670, 2130647297, 2130689493, 10620, 2130706270], [0, 2130703493, 40194, 2130639709, 2130602693, 55272, 44905, 2130700789], [2130705453, 28644, 2130569429, 8148, 232260, 26040, 2130662949, 1164], [2130706293, 10828, 2130583385, 234430, 227640, 2130485933, 2130604625, 19873], [1680, 2130652284, 302184, 2130555233, 2130232505, 41160, 92064, 2130702849], [2130706420, 2130697193, 161294, 2130252653, 2130533813, 452760, 108780, 2130668429], [168, 30800, 2130390205, 393660, 478632, 2130517097, 2130598073, 6188], [2130705432, 2130637133, 423830, 2130595985, 2130224861, 2130678125, 42840], [3640, 110880, 2130319772, 2130542129, 248220, 67900, 2130699923], [2130697424, 2130577073, 224268, 232092, 2130659883, 2130677901], [16016, 110880, 2130647165, 2130566813, 2130690053, 4228], [2130685412, 2130637133, 2130686809, 41880, 10374], [20592, 30800, 25025, 2130703337, 2130704809], [2130691418, 2130697193, 2130696391, 2130704885], [8008, 1680, 1756, 324], [2130703430, 2130706293, 2130706407], [728, 0, 2130706410], [2130706342], [], [1]],
    [[0, 0, 0, 2130705383, 2130704011, 2130705038], [0, 0, 0, 2130699083, 2130695366, 1782, 5475], [0, 0, 2130684383, 2130704039, 54894, 26370, 2130698378], [0, 0, 2130669683, 82320, 159552, 2130663551, 2130631573, 5265], [0, 2130669683, 229614, 59220, 2130261401, 2130558278, 84870, 2130705143], [0, 2130684383, 298998, 2130231203, 2129893103, 379764, 369705, 2130661415], [2130699083, 213738, 2129701205, 2130688163, 1750770, 286020, 2130353465, 9278], [2130705383, 80976, 2129794877, 1670340, 1828260, 2129149703, 2129832497, 160356], [12600, 2130303020, 2214108, 2129765213, 2127099053, 101430, 764568, 2130677600], [2130706342, 2130637133, 1195503, 2127444323, 2129167973, 3268692, 1027530, 2130394835], [1170, 231000, 2128379372, 2708910, 3732624, 2129551013, 2129771513, 50406], [2130699503, 2130186683, 3085665, 2130148937, 2127150209, 2130252203, 359730], [25025, 831600, 2127940571, 2129296745, 1680210, 633990, 2130652463], [2130645008, 2129736233, 1547766, 1773954, 2130518903, 2130457163], [108108, 831600, 2130351617, 2129712743, 2130506093, 35994], [2130566293, 2130186683, 2130525395, 257340, 98028], [135135, 231000, 187935, 3708, 2130691985], [2130609908, 2130637133, 2130638444, 2130688127], [50050, 12600, 9147, 3138], [2130688415, 2130705383, 813], [4095, 0, 2130706157], [2130705978], [], [], [1]]
  ]
private theorem cell_43_15 : (CJ0.blockMatrix source 43 ((15 : ℤ)-24)).rank ≤ 134 :=
  Fast.cell (z := matrix_43_15) (Fast.bands [(0, 21, 23), (1, 22, 21), (2, 23, 19), (3, 24, 17), (4, 25, 15), (5, 26, 13), (6, 27, 11), (7, 28, 9), (8, 29, 7), (9, 30, 5), (10, 31, 3), (11, 32, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_43_16 : CJ1.Block where
  bank := .leftLow
  cap := 130
  free := [(10, 0), (10, 1)]
  vectors := [
    [[1065353145, 1065350544, 2130657584, 2130124349, 1060267363, 1030608496, 1937458763, 1231118810, 685936588, 468709196, 1169760710, 869113591, 506830329, 610078234, 181705907, 328032134, 358570004, 1890196314, 1035709913, 1361338526, 736108877, 860591175], [532676544, 2130704093, 1065311536, 2130222362, 528553652, 2103244922, 1981774958, 1454692457, 1641858709, 1859483165, 1835671031, 970722796, 182370656, 687118307, 1156838240, 1009742731, 12463795, 1068155068, 251750140, 1393783681], [2130706376, 2130704411, 2130671342, 2130309218, 2127407753, 2109276794, 2017326089, 1628593481, 232652693, 178662819, 1369156485, 1826698274, 1038216408, 1487181468, 1624334276, 1399986221, 1522949196, 86569665], [1598029775, 1065351498, 1598000766, 2130385728, 2128108068, 2114228741, 2045571691, 1762480993, 771512828, 2049760509, 650346597, 2070533019, 756046073, 781052280, 617336182, 892467186], [1065353174, 1065351787, 2130682871, 2130452674, 2128698053, 2118254477, 2067774201, 1864415441, 1169436299, 1260595816, 340429796, 1673605550, 927300880, 189514361], [532676573, 2130705278, 2130687854, 2130510809, 2129190347, 2121491249, 2085019253, 1941074969, 1459727894, 80479397, 931017939, 15022398], [2130706405, 2130705538, 2130692345, 2130560857, 2129596633, 2124061025, 2098234553, 1997949305, 1668742697, 745796933], [1598029804, 1065352567, 532666541, 2130603513, 1597251066, 1060718422, 510177560, 2039512772], [1065353203, 1065352798, 2130699938, 2130639443, 1064840134, 1062264673], [532676602, 2130706231, 1065349867, 2130669284], [1]],
    [[1065353219, 1065353310, 1710, 20387, 1065531427, 1066571164, 6776217, 31550640, 125413794, 431980846, 1304093120, 1350333043, 1880721431, 552936998, 1689451773, 488250909, 920660649, 1841114978, 1159456912, 1594995226, 661410606, 1973694481], [1598029827, 82, 1065354678, 16983, 1598174541, 964257, 5230764, 23746008, 92015781, 308864160, 908146426, 228438579, 1189162103, 603864503, 1689522003, 719091832, 178684799, 882147651, 120564152, 1317685965], [2, 71, 1233, 13965, 116025, 753984, 3989832, 17669256, 66781440, 218546900, 626052812, 1582890876, 1424058235, 732815301, 7632402, 1450190223, 97586198, 765893736], [532676610, 1065353277, 532677632, 11305, 91630, 581196, 3002846, 12985280, 47912205, 152982830, 427175133, 1051409268, 164036017, 199694834, 1358654151, 1410256715], [1065353218, 1065353267, 833, 8976, 71060, 440572, 2226048, 9414328, 33958826, 105911190, 288481908, 691402920, 1466251020, 632154307], [1598029826, 41, 660, 6952, 53878, 327360, 1621796, 6724520, 23763267, 72506148, 192835500, 450183240], [1, 32, 504, 5208, 39680, 237336, 1157912, 4725144, 16408548, 49085400], [532676609, 1065353240, 1598030189, 3720, 532704702, 1065519981, 1598836902, 3260673], [1065353217, 1065353232, 240, 2465, 1065371994, 1065465577], [1598029825, 8, 1065353347, 1421], [0, 1]]
  ]
private theorem cell_43_16 : (CJ0.blockMatrix source 43 ((16 : ℤ)-24)).rank ≤ 130 :=
  Fast.cell (z := matrix_43_16) (Fast.bands [(19, 19, 1), (20, 20, 2), (21, 21, 3), (22, 22, 4), (23, 23, 5), (24, 24, 6), (25, 25, 7), (26, 26, 8), (27, 27, 9), (28, 28, 10), (29, 29, 11), (30, 30, 11), (31, 31, 11), (32, 32, 11), (33, 33, 11), (34, 34, 10), (35, 35, 9), (36, 37, 7), (37, 39, 5), (38, 41, 3), (39, 43, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_43 (u : ℕ) : ℕ :=
  match u with
  | 14 => 134
  | 15 => 134
  | 16 => 130
  | u => nominal 43 u

private theorem bound_43 (u : ℕ) :
    (CJ0.blockMatrix source 43 ((u : ℤ)-24)).rank ≤ allowance_43 u := by
  unfold allowance_43
  split
  · exact cell_43_14
  · exact cell_43_15
  · exact cell_43_16
  · exact (block_rank_le 43 _).trans (rank_le_nominal 43 _)

theorem grade_43 : (∑ u ∈ Finset.range (81-43), (CJ0.blockMatrix source 43 ((u : ℤ)-24)).rank) ≤ 2404 := by
  refine (Finset.sum_le_sum fun u _ => bound_43 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_43)]
  decide +kernel

private def matrix_44_14 : CJ1.Block where
  bank := .rightLow
  cap := 131
  free := [(21, 1), (22, 1), (23, 0), (24, 0)]
  vectors := [
    [[0, 0, 0, 0, 2130706432, 2130706432], [0, 0, 0, 2130706425, 2130706430, 4], [0, 0, 0, 2130706405, 20, 30, 2130706427], [0, 0, 2130706377, 140, 48, 2130706363, 4], [0, 0, 2130706363, 378, 2130706237, 2130706173, 75, 2130706432], [0, 2130706377, 574, 2130705425, 2130706237, 440, 2130706394], [0, 2130706405, 532, 2130704417, 1176, 980, 2130706061, 8], [2130706425, 300, 2130704193, 3864, 0, 2130705061, 160], [2130706432, 95, 2130704981, 5460, 2130702317, 2130704669, 980, 2130706405], [13, 2130705917, 4180, 2130698033, 1764, 2352, 2130706069], [0, 2130706355, 1694, 2130698513, 8232, 1176, 2130704921, 56], [0, 286, 2130702693, 10296, 2130701729, 2130704249, 504], [0, 2130705718, 5841, 2130697193, 840, 1386, 2130706363], [0, 1287, 2130699833, 5544, 840, 2130705999], [0, 2130704717, 5412, 2130704453, 2130705733, 56], [0, 1716, 2130703265, 220, 224], [0, 2130705146, 1265, 132, 2130706405], [0, 715, 2130706125, 2130706373], [0, 2130706147, 30, 8], [0, 78, 4], [0, 2130706420, 2130706432], [0, 1]],
    [[0, 0, 0, 0, 2130706420, 2130706419], [0, 0, 0, 2130706329, 2130706385, 56], [0, 0, 0, 2130706069, 224, 435, 2130706349], [0, 0, 2130705705, 1736, 840, 2130705433, 56], [0, 0, 2130705523, 4788, 2130704473, 2130702513, 1065, 2130706419], [0, 2130705705, 7336, 2130694337, 2130702121, 6440, 2130705881], [0, 2130706069, 6832, 2130681359, 11760, 15680, 2130701057, 113], [2130706329, 3864, 2130678153, 45696, 7056, 2130685657, 2296], [2130706420, 1226, 2130687953, 67200, 2130663509, 2130674681, 14504, 2130706033], [168, 2130699833, 52360, 2130607313, 7056, 37632, 2130701113], [0, 2130705432, 21428, 2130609413, 89376, 31164, 2130683249, 812], [0, 3640, 2130659793, 121968, 2130666449, 2130667457, 7560], [0, 2130697424, 71478, 2130602945, 2130699713, 22554, 2130705397], [0, 16016, 2130627761, 55440, 21000, 2130699657], [0, 2130685412, 62040, 2130692573, 2130693553, 854], [0, 20592, 2130672377, 2130703353, 3752], [0, 2130691418, 11990, 3696, 2130705985], [0, 8008, 2130704409, 2130705257], [0, 2130703430, 2130706229, 140], [0, 728, 160], [0, 2130706342, 2130706411], [], [0, 1]],
    [[0, 0, 0, 0, 2130706423, 2130706422], [0, 0, 0, 2130706353, 2130706393, 43], [0, 0, 0, 2130706153, 155, 340, 2130706370], [0, 0, 2130705873, 1280, 705, 2130705673, 41], [0, 0, 2130705733, 3570, 2130705193, 2130703383, 790, 2130706423], [0, 2130705873, 5488, 2130697823, 2130702673, 4850, 2130706033], [0, 2130706153, 5110, 2130688289, 7350, 12200, 2130702488, 80], [2130706353, 2880, 2130685923, 31584, 7350, 2130690913, 1645], [2130706423, 905, 2130693113, 47040, 2130679385, 2130681443, 10520, 2130706153], [120, 2130701768, 36400, 2130640073, 0, 27930, 2130702673], [2130706432, 2130705773, 14465, 2130641633, 55860, 25872, 2130689843, 560], [13, 2200, 2130676458, 77760, 2130685853, 2130677537, 5250], [2130706355, 2130701483, 43560, 2130644273, 2130697193, 15876, 2130705733], [286, 7920, 2130661223, 30240, 15960, 2130701841], [2130705718, 2130697193, 33330, 2130701033, 2130697543, 560], [1287, 7920, 2130689603, 2130703233, 2450], [2130704717, 2130701483, 5225, 2520, 2130706153], [1716, 2200, 2130705828, 2130705713], [2130705146, 2130705773, 2130706238, 80], [715, 120, 85], [2130706147, 2130706423, 2130706423], [78], [2130706420], [1]],
    [[0, 0, 0, 0, 2130706293, 2130706270], [0, 0, 0, 2130705313, 2130705793, 638], [0, 0, 0, 2130702513, 1855, 5160, 2130705497], [0, 0, 2130698593, 17200, 11760, 2130694993, 610], [0, 0, 2130696633, 48930, 2130694113, 2130659008, 11860, 2130706284], [0, 2130698593, 75824, 2130594293, 2130638673, 74200, 2130700433], [0, 2130702513, 70910, 2130461489, 73500, 196000, 2130646478, 1200], [2130705313, 40080, 2130425593, 405888, 161700, 2130463953, 24920], [2130706293, 12625, 2130522593, 630210, 2130412433, 2130283073, 162400, 2130702198], [1680, 2130641663, 496400, 2129852993, 2130579425, 449820, 2130648753], [2130706420, 2130697193, 199540, 2129838833, 649740, 489216, 2130444773, 8560], [168, 30800, 2130296683, 1009440, 2130577073, 2130217217, 81900], [2130705432, 2130637133, 587565, 2129947073, 2130444773, 258552, 2130695583], [3640, 110880, 2130109133, 312480, 299040, 2130633073], [2130697424, 2130577073, 425040, 3600, 2130553623, 8848], [16016, 110880, 2130506453, 2130622033, 40600], [2130685412, 2130637133, 50875, 48480, 2130701883], [20592, 30800, 1430, 2130693713], [2130691418, 2130697193, 2130700733, 1360], [8008, 1680, 1730], [2130703430, 2130706293, 2130706248], [728], [2130706342], [], [1]]
  ]
private theorem cell_44_14 : (CJ0.blockMatrix source 44 ((14 : ℤ)-24)).rank ≤ 131 :=
  Fast.cell (z := matrix_44_14) (Fast.bands [(0, 22, 23), (1, 23, 21), (2, 24, 19), (3, 25, 17), (4, 26, 15), (5, 27, 13), (6, 28, 11), (7, 29, 9), (8, 30, 7), (9, 31, 5), (10, 32, 3), (11, 33, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_44_15 : CJ1.Block where
  bank := .leftLow
  cap := 128
  free := [(9, 2), (9, 3), (10, 0), (10, 1)]
  vectors := [
    [[560968955, 1159010621, 1551200730, 1369735321, 1331651889, 655328945, 162358221, 578014955, 643088876, 696400181, 199385376, 358497818, 633365926, 1278523349, 1152398132, 1961029189, 1311830419, 84134657, 1087699367, 1402997865, 1029628601, 1229570730], [544383786, 1281935997, 11706891, 81946916, 1720926639, 1720762248, 2006711024, 1077907384, 2087135661, 2036447067, 599733745, 212795589, 466828864, 596637012, 2099928029, 1527611393, 900565870, 2081318739, 807714510, 1298148832], [1229253711, 1849734144, 1229253502, 2130704054, 1598009811, 1884722771, 613901364, 816158569, 876477166, 1265238208, 1006812723, 109875715, 546905556, 431424381, 927358305, 2062545893, 1379529093, 444294934], [484872297, 758039780, 1761930173, 1707295185, 1761916767, 1925742029, 545856282, 325619534, 237290134, 1855532904, 1058759640, 1237666590, 1562209399, 2057897470, 760292279, 499812228], [441945977, 163900489, 245850645, 2037047936, 76087876, 1896505799, 772368113, 864946787, 896053708, 1784542331, 2028899227, 158508215, 1177214185, 231997183], [1100474751, 93657422, 1656565656, 1972658872, 1919971860, 398009157, 327613702, 631337821, 1846417755, 550678266, 1792715565, 215838344], [329752186, 573651730, 263411477, 1763881154, 679013323, 655582044, 163791785, 1591676036, 1473130872, 1210793502], [260484715, 1630224564, 936574242, 304386465, 717063185, 143402655, 40916706, 181183034], [892672338, 1159010642, 2101438484, 901452668, 1864367567, 163896069], [95608622, 1317057548, 1]],
    [[327296370, 1672511702, 1874884443, 702188932, 923922397, 2075346963, 695320038, 841882589, 1145213508, 1455593123, 1233002709, 587627565, 126484133, 775857471, 669767610, 127013901, 1153361944, 224434394, 594050516, 1778122383, 1910003204, 860397140], [50179388, 2032245029, 2081697792, 1875813243, 201770061, 892429531, 184072809, 691110341, 849481145, 1604030582, 808936836, 2126374295, 249455747, 106121297, 686989488, 1268548843, 665353874, 303237165, 315218036, 287302418], [1011096501, 294536457, 614344290, 690643018, 2075604002, 1499420521, 152953655, 1257288136, 685049666, 496371191, 604285278, 1448171799, 60913196, 7477536, 1712131573, 1062400989, 1141180029, 1657806282], [1079341276, 1268109433, 1918483566, 1877791183, 640061088, 1952403138, 1362118821, 1081966941, 1557930271, 576642761, 1877472128, 843585604, 1335923565, 286966751, 72884659, 1065933260], [254913713, 1238861672, 822328355, 1817438604, 1687247512, 554038049, 145200683, 1428418691, 738107624, 1476986249, 1068624449, 988874776, 643711108, 1080352589], [668520245, 754103755, 1713002395, 1726970333, 1881384475, 552582488, 655621600, 1629727728, 838577491, 1307681835, 1586255051, 1835353089], [189454439, 361146263, 1490888963, 1672753957, 1418910325, 458923526, 753953835, 1784226659, 1245849959, 61577521], [948422728, 607299777, 223163040, 974037246, 1167791193, 1511983202, 1040774490, 1260892869], [814718679, 2039874878, 1143791311, 737552234, 1331691590, 2032366654], [1919048725, 944769281, 0, 1]],
    [[1393154452, 1966814972, 1147466573, 1929678, 1082185497, 1098888240, 1960350103, 451716556, 549976918, 1682970935, 1597332819, 1507415373, 375945057, 1598024862, 2097116430, 1756027418, 433320493, 2087012241, 166223639, 810330843, 698490866, 1690089682], [1311204155, 819509506, 1311327866, 657034090, 995620278, 1065469470, 1599395714, 1936179400, 1508247090, 1088315312, 864940907, 384555329, 1681946148, 1250566930, 1887806310, 1870559240, 395630095, 543679101, 1206372038, 319282546], [1311204111, 491706803, 1311295452, 1033872, 8635830, 220779767, 963241649, 1568516069, 768356915, 1749456275, 606794161, 1379177422, 980299843, 1193981929, 184257996, 11363646, 394379894, 391319373], [1393154320, 737556104, 1311269125, 164621406, 1317111073, 529940496, 1023115209, 1408169727, 1260207116, 1559802946, 491555127, 1240604954, 456503981, 818880807, 403508916, 1732374484], [1557054782, 1311206650, 1966850197, 164380941, 3873705, 1499841389, 1441420632, 1727681267, 920172822, 615053558, 2076933597, 1042473621, 1310165488, 902471158], [1802905497, 1966807682, 163928632, 1475405362, 1969205380, 1982012020, 571361183, 845721599, 1850127551, 1441171729, 676153974, 1153362772], [32, 327802008, 1802921644, 819674361, 1476472021, 992093118, 1357024744, 1680525677, 1942815563, 557814199], [409751253, 409751735, 491709367, 84072, 410430155, 86365271, 351760377, 1258098506], [901452727, 1966806104, 983405618, 819531675, 1065603414, 1312966842], [1475104454, 491701490], [1]],
    [[599992875, 479994015, 825350799, 760904270, 1331147838, 160170485, 1618045382, 2101752131, 316501896, 113384744, 1204315852, 601124206, 98499131, 930722856, 1807536084, 1145784142, 1835145669, 1479452880, 747989269, 1056048717, 1936512149, 807122323], [193168434, 111217965, 1791194246, 1884809223, 1228857309, 1226592021, 354123885, 1553450807, 407658250, 1864384893, 1026394972, 234758982, 135473104, 436087150, 1535362890, 97441113, 1585688756, 479466558, 1664367699, 1760782666], [573651727, 1756076557, 573648746, 2130672692, 1597748121, 735698469, 276812372, 1757259031, 1717460031, 1844765655, 1093413754, 2047843155, 564713872, 571968437, 149506208, 1978649447, 2110916172, 710674767], [1741442754, 921940156, 1106326197, 1270205139, 1106134398, 613373463, 485041235, 1117396295, 1277447201, 346398537, 1782845167, 998673686, 1166170286, 55676586, 1064855390, 268496819], [1565835082, 1639004859, 1393152736, 585342975, 989128363, 397227695, 1025947890, 425844597, 1484151852, 739251166, 636484286, 2062624151, 431020454, 1199401087], [46828711, 1545347464, 2031194471, 1387290519, 1849653955, 1240454913, 1144665383, 831248680, 1711512115, 600479074, 1997288671, 684415779], [1445836507, 409751202, 1949244615, 1404855524, 1615544291, 163608389, 1637475542, 695619394, 1940589231, 825050451], [1501445604, 131705737, 538529919, 1826316868, 1044842272, 634964103, 2006973708, 60689737], [213656002, 479994300, 1914123538, 1557053647, 1864359302, 1638943899], [1843880567, 1223400122], [0, 1]]
  ]
private theorem cell_44_15 : (CJ0.blockMatrix source 44 ((15 : ℤ)-24)).rank ≤ 128 :=
  Fast.cell (z := matrix_44_15) (Fast.bands [(20, 20, 1), (21, 21, 2), (22, 22, 3), (23, 23, 4), (24, 24, 5), (25, 25, 6), (26, 26, 7), (27, 27, 8), (28, 28, 9), (29, 29, 10), (30, 30, 11), (31, 31, 11), (32, 32, 11), (33, 33, 11), (34, 34, 11), (35, 35, 10), (36, 37, 8), (37, 39, 6), (38, 41, 4), (39, 43, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_44 (u : ℕ) : ℕ :=
  match u with
  | 14 => 131
  | 15 => 128
  | u => nominal 44 u

private theorem bound_44 (u : ℕ) :
    (CJ0.blockMatrix source 44 ((u : ℤ)-24)).rank ≤ allowance_44 u := by
  unfold allowance_44
  split
  · exact cell_44_14
  · exact cell_44_15
  · exact (block_rank_le 44 _).trans (rank_le_nominal 44 _)

theorem grade_44 : (∑ u ∈ Finset.range (81-44), (CJ0.blockMatrix source 44 ((u : ℤ)-24)).rank) ≤ 2265 := by
  refine (Finset.sum_le_sum fun u _ => bound_44 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_44)]
  decide +kernel

private def matrix_45_13 : CJ1.Block where
  bank := .rightLow
  cap := 127
  free := [(22, 1), (24, 0)]
  vectors := [
    [[0, 0, 0, 0, 2130706432], [0, 0, 0, 0, 2130706424, 4], [0, 0, 0, 2130706397, 45, 2130706427], [0, 0, 0, 2130706349, 216, 2130706343, 4], [0, 0, 2130706307, 588, 2130705893, 90, 2130706432], [0, 0, 2130706307, 1008, 2130704669, 720, 2130706388], [0, 2130706349, 1134, 2130702905, 2940, 2130705893, 9], [0, 2130706397, 840, 2130701897, 7056, 2130703493, 216], [2130706424, 396, 2130702653, 10584, 2130697613, 1764, 2130706397], [2130706432, 108, 2130704453, 10080, 2130690557, 7056, 2130705845], [13, 2130705839, 5940, 2130688793, 15876, 2130702905, 84], [0, 2130706355, 1980, 2130694553, 21168, 2130695849, 1008], [0, 286, 2130701978, 16632, 2130688793, 4536, 2130706307], [0, 2130705718, 7128, 2130689801, 10080, 2130705299], [0, 1287, 2130698117, 11880, 2130702653, 126], [0, 2130704717, 7128, 2130700493, 840], [0, 1716, 2130701978, 1980, 2130706349], [0, 2130705146, 1980, 2130706037], [0, 715, 2130705839, 36], [0, 2130706147, 108], [0, 78, 2130706424], [0, 2130706420], [0, 1]],
    [[0, 0, 0, 0, 2130706423], [0, 0, 0, 0, 2130706343, 39], [0, 0, 0, 2130706073, 440, 2130706376], [0, 0, 0, 2130705593, 2115, 2130705573, 37], [0, 0, 2130705173, 5760, 2130701258, 840, 2130706424], [0, 0, 2130705173, 9870, 2130689513, 6750, 2130706023], [0, 2130705593, 11088, 2130672623, 27600, 2130701483, 80], [0, 2130706073, 8190, 2130663089, 66150, 2130679433, 1935], [2130706343, 3840, 2130670523, 98784, 2130625583, 15840, 2130706118], [2130706423, 1035, 2130687833, 93240, 2130561785, 63210, 2130701273], [120, 2130700988, 54000, 2130547673, 141120, 2130675563, 720], [2130706432, 2130705773, 17325, 2130602033, 185220, 2130614705, 8610], [13, 2200, 2130669308, 141120, 2130556493, 38304, 2130705383], [2130706355, 2130701483, 56430, 2130570353, 83160, 2130697109], [286, 7920, 2130644063, 93600, 2130676193, 1008], [2130705718, 2130697193, 50490, 2130661433, 6510], [1287, 7920, 2130676733, 14400, 2130705803], [2130704717, 2130701483, 12375, 2130703673], [1716, 2200, 2130702968, 240], [2130705146, 2130705773, 585], [715, 120, 2130706388], [2130706147, 2130706423], [78], [2130706420], [1]]
  ]
private theorem cell_45_13 : (CJ0.blockMatrix source 45 ((13 : ℤ)-24)).rank ≤ 127 :=
  Fast.cell (z := matrix_45_13) (Fast.bands [(0, 23, 23), (1, 24, 21), (2, 25, 19), (3, 26, 17), (4, 27, 15), (5, 28, 13), (6, 29, 11), (7, 30, 9), (8, 31, 7), (9, 32, 5), (10, 33, 3), (11, 34, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_45_14 : CJ1.Block where
  bank := .leftLow
  cap := 126
  free := [(9, 0), (9, 1), (9, 2), (9, 3), (10, 0), (10, 1)]
  vectors := [
    [[1065317099, 1064028769, 1041404413, 780517711, 1753806128, 1742741039, 1504678970, 226501275, 2074787841, 1388782446, 585331417, 629271003, 699177217, 1095776815, 303302882, 1738031989, 847735691, 1745484652, 890510665, 1408032840, 42955794, 22941645], [2130679976, 2129758601, 2113940537, 1935370369, 1509122849, 1263797904, 1249588934, 236126783, 161582999, 1629253146, 1831415896, 231220570, 801257532, 420378520, 2106498355, 333671751, 675223599, 1205955453, 392132965, 885418456], [2130687751, 2130052339, 1054026079, 935921736, 1032474473, 1141360928, 620636643, 368245609, 1223583208, 325785256, 1615440279, 1722358052, 451398606, 1938335557, 1643616573, 217096603, 320184843, 1305011518], [1065340627, 2130275352, 1058035371, 2048545263, 378796104, 1837927300, 1664216243, 893963719, 1758389543, 1629078473, 1316878713, 1281478915, 1518750848, 670739467, 722711350, 1729175107], [1065345240, 1065085764, 1060893394, 1016013734, 657894539, 517647336, 327747483, 564194996, 856398694, 1982330106, 586049426, 968710751, 86861832, 1084693400], [2130701793, 2130553753, 2128197107, 2103230485, 839898971, 652960625, 473575292, 945555938, 242967715, 339204428, 1658941707, 994536541], [2130704056, 2130629386, 1064098178, 1051653635, 2018038185, 1386974521, 164896414, 1995461934, 1717444890, 1338094707], [1065352232, 2130674784, 1064837179, 2125019185, 2083099888, 1808479661, 299204299, 1701847545], [1065352957, 1065344823, 1065213451, 1063757129, 2116643608, 2028824996], [1]],
    [[1598033571, 1598167141, 1600512063, 1627548252, 259875616, 1807035489, 1282269956, 498644748, 1886910389, 401090028, 596365222, 348786922, 1117547190, 1737504413, 319420608, 2039864891, 2047119239, 278200297, 1838962705, 396995548, 609167801, 1651661557], [2736, 97983, 1732887, 20189764, 707070956, 1191413727, 313093887, 4121124, 1177578233, 680204509, 1708400881, 1645251732, 1594216354, 160294275, 723402029, 795391210, 9324700, 2120537522, 440264594, 1224792217], [1925, 67383, 1599196723, 546013451, 113213835, 761419155, 496509307, 178533445, 15630614, 1821681725, 1993295515, 47321124, 1354492240, 1442285010, 796713671, 485215399, 73627424, 1771600383], [1065354508, 1065397439, 533427521, 8435490, 1668574101, 1533764527, 2038502098, 1337106803, 1561176034, 1437346730, 323303697, 459645812, 1097975364, 1793120055, 59151996, 1062025469], [532677422, 532703903, 533132072, 537720522, 1639736541, 1872591219, 1497755930, 562715511, 314326126, 1196869337, 854062655, 1117985406, 285719458, 1174352613], [470, 15480, 1065607976, 2794186, 1621002057, 150892544, 823753700, 1706304679, 613098995, 2023557751, 29661928, 915937497], [1065353455, 1065360962, 532803074, 1599413985, 11416724, 75591516, 417641238, 1974777562, 1735403475, 1744402285], [1065353314, 1065356362, 1598081313, 569824, 1602820371, 32566275, 1251238997, 912155067], [1598029850, 1598030646, 1598043580, 1598187911, 1066755439, 1075578428], [0, 1]],
    [[2130706181, 2130697199, 425974397, 850298066, 408668803, 2009188665, 1435305863, 1746367338, 410162434, 393528854, 659397119, 491403381, 183440588, 1061627895, 44913997, 1373391219, 520356376, 1962051998, 6013768, 1723578572, 1063855888, 1889853818], [426141103, 426134713, 852166325, 850928074, 2119003962, 772305164, 401950778, 1687172673, 1371807060, 2067735440, 2102022114, 1738756248, 1454062716, 1050268407, 835101435, 1085290723, 1041502931, 1756860194, 287334839, 456461759], [1278423731, 2130701925, 1278345787, 2129813877, 2123126339, 375130699, 1847431217, 1222387146, 953130051, 1846581706, 1277027156, 1299292931, 1897935570, 1539269392, 1716456639, 1510533102, 1246722192, 1547340909], [1491494417, 1704562198, 2130656352, 2130143531, 2125995461, 820973102, 1106380419, 1327462145, 1012739284, 1240927566, 237699146, 1246074572, 1354352007, 1235343433, 409549926, 859006119], [2130706379, 2130704621, 2130676175, 2130371023, 2127929721, 2112402125, 2030707809, 1665647905, 254565353, 1868240740, 352115106, 671923892, 2127857863, 1080241280], [2130706402, 2130705411, 426124445, 852097558, 424617417, 2120677249, 2075843625, 170071565, 1944636095, 983229687, 1055805486, 940426208], [426141271, 426140779, 852274266, 852191414, 2129952449, 421134861, 398403181, 720772538, 309670626, 160450841], [213070637, 2130706229, 1278420507, 2130669169, 1065038582, 1276275969, 2118398224, 1217812201], [426141285, 1704565094, 2130705549, 2130696197, 2130614967, 425469809], [0, 0, 1]],
    [[1598029833, 1598030127, 1598035287, 1171953492, 1278995813, 856261272, 1620805443, 1708358469, 1207234519, 1585584659, 814167574, 1088722726, 1452063125, 1076116013, 803490051, 1512583901, 285065584, 912640758, 210929035, 1477509703, 1550223109, 1354198995], [6, 852282788, 1704568945, 1704609413, 1385341730, 2615382, 1719298465, 1348740273, 1035802456, 623432267, 1238486779, 2006404962, 1167566519, 646580448, 1892522700, 582243407, 270781493, 1854302170, 1768089811, 1028518198], [1278423864, 147, 1598032371, 1384988300, 247401, 427807120, 541933529, 1641669594, 1882571344, 637414932, 1173320239, 1497909269, 1956459430, 875166510, 1300945902, 291996745, 838562727, 399215762], [852282576, 1491494599, 1384960811, 18326, 1598183305, 640232819, 325220855, 1730805884, 106235822, 377860054, 2045313289, 1664737260, 887915445, 453157869, 274734058, 30755940], [532676610, 532676667, 532677590, 532687501, 1598120099, 320201775, 855541684, 15176546, 61303275, 217706335, 1538620707, 655679526, 633839015, 510011600], [1, 33, 1065353761, 1704571137, 745796674, 852608402, 1785476, 8347680, 1738468594, 1399552243, 1236304088, 1086750756], [1065353217, 1917635806, 106535589, 1171891479, 852306958, 162316, 853184016, 1708848342, 1722272210, 916688012], [1278423860, 1065353223, 1598029932, 852283770, 532686753, 1278493368, 1065752822, 1973305], [319605965, 2024171113, 319605993, 1598030152, 1065356161, 1917657531], [0, 0, 0, 1]],
    [[2130699629, 2130457538, 2126214488, 2077352795, 1661345177, 998745577, 508765842, 1214569589, 1117987358, 240490851, 1626333378, 289278779, 1654900452, 1284083786, 977785632, 352739800, 664302880, 1661719222, 1924231488, 2095891389, 501468149, 1407551440], [2130701511, 2130530501, 2127599363, 2094538217, 1818404492, 2127489592, 766568409, 173859651, 1986155684, 1884627027, 367976764, 1767039683, 1096521640, 1878979746, 1491942524, 928097172, 607947285, 609576096, 223335444, 26559301], [2130703010, 2130586817, 2128637177, 2107065767, 1929978038, 779571137, 1014631640, 814779349, 370840312, 1916043092, 1132176774, 1274346083, 982161155, 655391813, 1465681479, 372644195, 1320119523, 286620110], [1065350953, 2130629027, 2129392652, 2115942803, 2007105998, 1308544001, 1868388087, 149447498, 1606203583, 1373854392, 1247088386, 1883100876, 626941395, 1954165656, 1812332854, 95402866], [2130705033, 2130659498, 2129922818, 2122015543, 2058675053, 1655047997, 1657024970, 639755478, 1994162232, 1953955519, 1246284784, 1997704486, 2108107606, 690625514], [2130705644, 2130680423, 2130277448, 2125985945, 2091734357, 1873454273, 718557233, 1905898052, 753122201, 1442613542, 1724896829, 856835290], [2130706046, 2130693821, 2130499493, 2128427717, 2111780537, 2004443681, 1427501441, 908718226, 999320435, 292980936], [1065353066, 2130701537, 2130625517, 2129801457, 1057660024, 2077807475, 1825263092, 614458427], [2130706397, 2130705242, 2130686132, 2130468923, 2128562753, 2114812142], [], [1]],
    [[1065353446, 1065361609, 639363363, 214869179, 1720388164, 110011767, 1694994112, 1132984836, 1474089725, 188218164, 1220650463, 1032377290, 2124301457, 1090840094, 1049394693, 1811316848, 288416117, 1382917112, 1409226610, 1068716360, 1136947255, 1890538810], [1704565312, 1704571064, 1278528357, 1279640343, 1075859533, 1350239439, 1683078933, 227913818, 948130755, 1213490755, 917819248, 758527558, 162439667, 791771339, 645938156, 1808697839, 1166036133, 990011666, 1480972003, 1256481073], [852282688, 4011, 1917705180, 1066146187, 6736050, 1749935491, 1317673141, 1830189741, 604517126, 413219812, 1062938662, 843947504, 730619443, 435882065, 595111317, 1297253620, 174651131, 2066826271], [1704565222, 426143872, 1065397111, 493548, 1069488526, 1305958770, 2069315772, 710315760, 752095291, 1759637800, 179641862, 1087404098, 862599308, 337960094, 1551848773, 336368903], [1065353263, 1065354776, 1065379273, 1065642514, 1067754186, 1081232602, 87091884, 406833460, 1649188530, 1618171196, 1567483670, 1544371890, 1836443720, 34168398], [26, 858, 1704579319, 1278580111, 640504761, 8554128, 47071640, 1925667364, 50235034, 684829770, 1811614384, 1713349027], [1704565159, 1704565558, 213077417, 213145484, 623832, 1708742260, 1727912536, 1390116339, 1743466491, 1703964600], [852282578, 157, 1917638400, 29376, 1065604487, 854020520, 10089477, 902609672], [639211931, 1491494540, 1065353854, 1065360771, 68991, 1705081996], [], [0, 1]]
  ]
private theorem cell_45_14 : (CJ0.blockMatrix source 45 ((14 : ℤ)-24)).rank ≤ 126 :=
  Fast.cell (z := matrix_45_14) (Fast.bands [(21, 21, 1), (22, 22, 2), (23, 23, 3), (24, 24, 4), (25, 25, 5), (26, 26, 6), (27, 27, 7), (28, 28, 8), (29, 29, 9), (30, 30, 10), (31, 31, 11), (32, 32, 11), (33, 33, 11), (34, 34, 11), (35, 35, 11), (36, 37, 9), (37, 39, 7), (38, 41, 5), (39, 43, 3), (40, 45, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_45_15 : CJ1.Block where
  bank := .leftLow
  cap := 120
  free := [(10, 0)]
  vectors := [
    [[1, 40, 780, 9880, 91390, 658008, 3838380, 18643560, 76904685, 273438880, 847660528, 181095007, 1325440614, 1379690715, 1899865510, 1872629262, 1061615093, 1373415047, 452820851, 1309315987, 1481317108], [1, 39, 741, 9139, 82251, 575757, 3262623, 15380937, 61523748, 211915132, 635745396, 1676056044, 1780091003, 1730306145, 169559365, 1703069897, 1489251629, 2014869851, 568657433], [1, 38, 703, 8436, 73815, 501942, 2760681, 12620256, 48903492, 163011640, 472733756, 1203322288, 576768715, 1153537430, 1146728368, 556341529, 932910100], [1, 37, 666, 7770, 66045, 435897, 2324784, 10295472, 38608020, 124403620, 348330136, 854992152, 1852482996, 1431760867, 1845673934], [1, 36, 630, 7140, 58905, 376992, 1947792, 8347680, 30260340, 94143280, 254186856, 600805296, 1251677700], [1, 35, 595, 6545, 52360, 324632, 1623160, 6724520, 23535820, 70607460, 183579396], [1, 34, 561, 5984, 46376, 278256, 1344904, 5379616, 18156204], [1, 33, 528, 5456, 40920, 237336, 1107568], [1, 32, 496, 4960, 35960], [1, 31, 465], [1]]
  ]
private theorem cell_45_15 : (CJ0.blockMatrix source 45 ((15 : ℤ)-24)).rank ≤ 120 :=
  Fast.cell (z := matrix_45_15) (Fast.bands [(21, 21, 1), (22, 22, 2), (23, 23, 3), (24, 24, 4), (25, 25, 5), (26, 26, 6), (27, 27, 7), (28, 28, 8), (29, 29, 9), (30, 30, 10), (31, 31, 11), (32, 32, 11), (33, 33, 11), (34, 34, 11), (35, 35, 11), (36, 36, 10), (37, 38, 8), (38, 40, 6), (39, 42, 4), (40, 44, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_45 (u : ℕ) : ℕ :=
  match u with
  | 13 => 127
  | 14 => 126
  | 15 => 120
  | u => nominal 45 u

private theorem bound_45 (u : ℕ) :
    (CJ0.blockMatrix source 45 ((u : ℤ)-24)).rank ≤ allowance_45 u := by
  unfold allowance_45
  split
  · exact cell_45_13
  · exact cell_45_14
  · exact cell_45_15
  · exact (block_rank_le 45 _).trans (rank_le_nominal 45 _)

theorem grade_45 : (∑ u ∈ Finset.range (81-45), (CJ0.blockMatrix source 45 ((u : ℤ)-24)).rank) ≤ 2129 := by
  refine (Finset.sum_le_sum fun u _ => bound_45 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_45)]
  decide +kernel

private def matrix_46_13 : CJ1.Block where
  bank := .rightLow
  cap := 123
  free := [(19, 2), (20, 2), (21, 1), (22, 1), (23, 0), (24, 0)]
  vectors := [
    [[0, 0, 0, 1, 1], [0, 0, 0, 7, 2, 2130706429], [0, 0, 21, 2130706412, 2130706408, 6], [0, 0, 35, 2130706321, 2130706412, 60, 2130706429], [0, 35, 2130706188, 196, 175, 2130706368, 1], [0, 21, 2130706139, 700, 0, 2130706118, 34], [7, 2130706230, 1071, 2130705453, 2130705943, 273, 2130706426], [1, 2130706357, 875, 2130704249, 490, 784, 2130706314], [2130706421, 374, 2130704228, 2646, 490, 2130705845, 21], [0, 66, 2130705333, 3570, 2130704669, 2130705453, 224], [0, 2130706213, 2145, 2130702611, 294, 700, 2130706398], [0, 0, 495, 2130703529, 2646, 504, 2130706188], [0, 0, 2130705641, 2772, 2130705383, 2130705992, 35], [0, 0, 924, 2130704585, 105, 154], [0, 0, 2130705641, 825, 105, 2130706412], [0, 0, 495, 2130706213, 2130706384], [0, 0, 2130706213, 22, 7], [0, 0, 66, 4], [0, 0, 2130706421, 2130706432], [0, 0, 1]],
    [[0, 0, 0, 12, 13], [0, 0, 0, 84, 32, 2130706381], [0, 0, 252, 2130706209, 2130706093, 78], [0, 0, 420, 2130705145, 2130706013, 800, 2130706381], [0, 420, 2130703563, 1960, 2520, 2130705573, 13], [0, 252, 2130702961, 7840, 1176, 2130702093, 448], [84, 2130704025, 12348, 2130696633, 2130698593, 3696, 2130706341], [12, 2130705529, 10220, 2130682241, 1960, 11368, 2130704837], [2130706290, 4400, 2130681233, 27048, 10780, 2130698201, 280], [0, 780, 2130693673, 39480, 2130692321, 2130690753, 3080], [0, 2130703859, 24420, 2130666449, 2130702905, 10360, 2130705957], [0, 0, 5720, 2130674225, 24696, 10752, 2130702933], [0, 0, 2130697424, 29568, 2130699713, 2130699125, 490], [0, 0, 10296, 2130687953, 2130704333, 2352], [0, 0, 2130697853, 7260, 2520, 2130706125], [0, 0, 5148, 2130705113, 2130705565], [0, 0, 2130704288, 2130706257, 112], [0, 0, 572, 136], [0, 0, 2130706355, 2130706413], [], [0, 0, 1]],
    [[0, 0, 0, 9, 10], [0, 0, 0, 63, 27, 2130706394], [0, 0, 189, 2130706280, 2130706172, 57], [0, 0, 315, 2130705509, 2130706064, 594, 2130706396], [0, 315, 2130704354, 1260, 1935, 2130705812, 9], [0, 189, 2130703913, 5418, 1260, 2130703238, 315], [63, 2130704690, 8631, 2130700259, 2130700343, 2637, 2130706370], [9, 2130705785, 7119, 2130690305, 0, 8316, 2130705326], [2130706334, 3006, 2130689612, 16758, 8820, 2130700637, 189], [1, 495, 2130698153, 25074, 2130699377, 2130694967, 2100], [2130706421, 2130704948, 14985, 2130682619, 2130702023, 7182, 2130706118], [0, 66, 2970, 2130687857, 13230, 8064, 2130704102], [0, 2130706213, 2130702275, 15876, 2130704039, 2130701456, 315], [0, 495, 4158, 2130697361, 2130704354, 1512], [0, 2130705641, 2130703463, 3105, 1701, 2130706244], [0, 924, 1485, 2130706073, 2130705908], [0, 2130705641, 2130705938, 2130706271, 63], [0, 495, 99, 72], [0, 2130706213, 2130706424, 2130706424], [0, 66], [0, 2130706421], [0, 1]],
    [[0, 0, 0, 117, 138], [0, 0, 0, 819, 414, 2130705894], [0, 0, 2457, 2130704660, 2130702725, 789], [0, 0, 4095, 2130694841, 2130700340, 8352, 2130705920], [0, 4095, 2130679910, 13440, 28395, 2130697730, 125], [0, 2457, 2130674051, 66402, 25200, 2130660578, 4410], [819, 2130683942, 108801, 2130640283, 2130612563, 37521, 2130705551], [117, 2130698045, 90867, 2130510377, 2130678209, 122808, 2130690746], [2130705146, 38682, 2130495320, 186102, 149940, 2130622265, 2673], [12, 6435, 2130600773, 305802, 2130662333, 2130529151, 30240], [2130706290, 2130687128, 188865, 2130432131, 2130601475, 107478, 2130701918], [0, 780, 38610, 2130476825, 129654, 136584, 2130672098], [0, 2130703859, 2130652379, 189756, 4158, 2130628124, 4599], [0, 5720, 54054, 2130605129, 2130659246, 23058], [0, 2130697424, 2130667823, 28485, 29673, 2130703598], [0, 10296, 19305, 1260, 2130697928], [0, 2130697853, 2130699998, 2130702347, 987], [0, 5148, 1287, 1332], [0, 2130704288, 2130706316, 2130706280], [0, 572], [0, 2130706355], [], [0, 1]],
    [[0, 0, 0, 45, 55], [0, 0, 0, 315, 180, 2130706224], [0, 0, 945, 2130705848, 2130704958, 298], [0, 0, 1575, 2130702233, 2130703733, 3210, 2130706244], [0, 1575, 2130696668, 3900, 11295, 2130703178, 45], [0, 945, 2130694463, 22890, 12000, 2130688928, 1610], [315, 2130698138, 38367, 2130687533, 2130668783, 13905, 2130706118], [45, 2130703373, 32025, 2130641669, 2130687533, 46680, 2130700763], [2130705983, 13350, 2130635768, 53802, 61950, 2130675533, 945], [10, 2025, 2130672053, 95970, 0, 2130639023, 10800], [2130706323, 2130701033, 57645, 2130628523, 2130657923, 39060, 2130704858], [1, 550, 9450, 2130641273, 27930, 52668, 2130694358], [2130706421, 2130704783, 2130695093, 49140, 11550, 2130678272, 1575], [66, 3300, 9450, 2130683753, 2130686798, 7938], [2130706213, 2130701813, 2130701033, 4005, 10605, 2130705488], [495, 4620, 2025, 1980, 2130703598], [2130705641, 2130703133, 2130705983, 2130704903, 315], [924, 1650, 45, 420], [2130705641, 2130705883, 0, 2130706388], [495, 110], [2130706213, 2130706423], [66], [2130706421], [1]],
    [[0, 0, 0, 630, 805], [0, 0, 0, 4410, 2790, 2130703365], [0, 0, 13230, 2130699143, 2130684413, 4387], [0, 0, 22050, 2130649313, 2130663143, 47710, 2130703643], [0, 22050, 2130571613, 42600, 172035, 2130658073, 666], [0, 13230, 2130540113, 304920, 204600, 2130442643, 23940], [4410, 2130590723, 525294, 2130497483, 2130117533, 208800, 2130701743], [630, 2130663593, 443730, 2129848877, 2130328433, 715920, 2130621383], [2130700088, 186660, 2129739593, 635040, 1011150, 2130236153, 14175], [130, 28800, 2130227393, 1279740, 181692, 2129646353, 163800], [2130705003, 2130628808, 797310, 2129733293, 2129842073, 605430, 2130682583], [12, 7150, 137700, 2129818673, 244020, 862596, 2130520583], [2130706290, 2130684983, 2130538223, 647640, 288120, 2130257999, 24150], [780, 42900, 143640, 2130434273, 2130357623, 124740], [2130703859, 2130646373, 2130621383, 20790, 176610, 2130691691], [5720, 60060, 33750, 46440, 2130660443], [2130697424, 2130663533, 2130698108, 2130678533, 5040], [10296, 21450, 1080, 7200], [2130697853, 2130699283, 2130706388, 2130705683], [5148, 1430], [2130704288, 2130706303], [572], [2130706355], [], [1]]
  ]
private theorem cell_46_13 : (CJ0.blockMatrix source 46 ((13 : ℤ)-24)).rank ≤ 123 :=
  Fast.cell (z := matrix_46_13) (Fast.bands [(0, 25, 22), (1, 26, 20), (2, 27, 18), (3, 28, 16), (4, 29, 14), (5, 30, 12), (6, 31, 10), (7, 32, 8), (8, 33, 6), (9, 34, 4), (10, 35, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_46_14 : CJ1.Block where
  bank := .leftLow
  cap := 119
  free := [(9, 2), (10, 0)]
  vectors := [
    [[189832524, 1551389938, 903340988, 739692398, 530223266, 785524000, 1109598345, 1865893670, 472575582, 695270453, 1124659417, 1869643882, 212139853, 1471044316, 1435999077, 61222203, 1949547635, 1304034124, 774074129, 1106659091, 1185372253], [1875414418, 1492476396, 1963784741, 432032766, 88371450, 628419200, 1512161117, 648276636, 1002475278, 199780708, 315128875, 334393887, 1292209552, 166357920, 942083242, 2124386491, 71619573, 2067200998, 437403155], [1430289879, 193105499, 2061973976, 1865595598, 1109539293, 824795982, 412431032, 805323790, 805849634, 1422924894, 514873193, 1238143228, 49907376, 108132648, 514710575, 672750599, 582252720], [985165340, 1914690113, 1993241509, 1521933251, 824790321, 68737457, 27676, 1718440199, 913669929, 711988291, 1222820788, 14009088, 33052692, 69607656, 131335200], [540040801, 265110939, 422213723, 1924509104, 1443382353, 412398630, 1718332487, 913254789, 913528557, 1218786076, 3644256, 9441936, 21688056], [94916262, 1636487276, 274929867, 985165393, 1535025507, 1718314535, 1420486414, 1116153423, 1217809936, 867680, 2494580], [1780498156, 1767406258, 216016324, 526948943, 196378804, 913162037, 405860100, 304436215, 608959198], [1335373617, 657867885, 1040805910, 2022698302, 1217546772, 304388167, 1521941187], [890249078, 438578590, 1413925008, 202924442, 202924586], [445124539, 1109538373, 1]],
    [[1724857582, 1826319539, 1521928135, 1724794161, 1216959026, 300122637, 1496683415, 1396519975, 75767203, 670641023, 1535114022, 542688418, 689783750, 1768750679, 549256222, 1105465713, 1168631544, 1238153835, 1412625854, 450780983, 790264682], [913159894, 1217546308, 1826315558, 913107677, 912687283, 1518580459, 2111295197, 210103487, 1434472119, 1325410063, 85308137, 516828829, 1732139155, 1963713282, 1251286305, 745907628, 1760316246, 911514312, 832912137], [101462206, 101462020, 2130702918, 1521890886, 1521559070, 2128110254, 2115994752, 1147590501, 932914688, 1835703464, 943413628, 1200467660, 463803270, 1364173562, 557886125, 408976341, 337270964], [1420470951, 608773108, 2130703584, 1521899655, 2130416168, 2128732631, 2119739818, 2079561185, 709088937, 714087182, 1204956313, 646933939, 1228284947, 719442982, 2056368591], [608773263, 608773139, 1521930925, 2130680603, 2130486878, 2129239418, 2122690865, 876390357, 768913977, 727136896, 671485593, 433204762, 1748739385], [1927782008, 101462113, 2130704743, 1420451802, 1420310447, 2129647265, 704515771, 379922452, 1117159056, 1794480433, 1147581609], [1116084320, 1217546463, 1521931974, 710222076, 608661494, 912424509, 1112124695, 286518623, 540087098], [304386632, 1826319756, 1521932420, 304378135, 1217474436, 303904167, 1519299867], [1623395377, 1927781992, 1826319450, 1623391008, 1623355048], [811697689, 1521933171], [1]]
  ]
private theorem cell_46_14 : (CJ0.blockMatrix source 46 ((14 : ℤ)-24)).rank ≤ 119 :=
  Fast.cell (z := matrix_46_14) (Fast.bands [(22, 22, 1), (23, 23, 2), (24, 24, 3), (25, 25, 4), (26, 26, 5), (27, 27, 6), (28, 28, 7), (29, 29, 8), (30, 30, 9), (31, 31, 10), (32, 32, 11), (33, 33, 11), (34, 34, 11), (35, 35, 11), (36, 36, 11), (37, 38, 9), (38, 40, 7), (39, 42, 5), (40, 44, 3), (41, 46, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_46 (u : ℕ) : ℕ :=
  match u with
  | 13 => 123
  | 14 => 119
  | u => nominal 46 u

private theorem bound_46 (u : ℕ) :
    (CJ0.blockMatrix source 46 ((u : ℤ)-24)).rank ≤ allowance_46 u := by
  unfold allowance_46
  split
  · exact cell_46_13
  · exact cell_46_14
  · exact (block_rank_le 46 _).trans (rank_le_nominal 46 _)

theorem grade_46 : (∑ u ∈ Finset.range (81-46), (CJ0.blockMatrix source 46 ((u : ℤ)-24)).rank) ≤ 1998 := by
  refine (Finset.sum_le_sum fun u _ => bound_46 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_46)]
  decide +kernel

private def matrix_47_12 : CJ1.Block where
  bank := .rightLow
  cap := 120
  free := [(20, 2), (22, 1), (24, 0)]
  vectors := [
    [[0, 0, 0, 0, 1], [0, 0, 0, 8, 2130706429], [0, 0, 0, 28, 2130706393, 6], [0, 0, 56, 2130706265, 80, 2130706429], [0, 0, 70, 2130706041, 420, 2130706353, 1], [0, 56, 2130705873, 1176, 2130705873, 40], [0, 28, 2130705929, 1960, 2130704473, 420, 2130706425], [8, 2130706153, 2016, 2130702513, 1960, 2130706265], [1, 2130706345, 1260, 2130701729, 4900, 2130705257, 28], [2130706421, 440, 2130703073, 7056, 2130702513, 392], [0, 66, 2130705113, 5880, 2130699377, 1960, 2130706377], [0, 2130706213, 2640, 2130699377, 4704, 2130705873], [0, 0, 495, 2130702737, 5880, 2130704417, 70], [0, 0, 2130705641, 3696, 2130703073, 504], [0, 0, 924, 2130703793, 1260, 2130706377], [0, 0, 2130705641, 1320, 2130706153], [0, 0, 495, 2130705993, 28], [0, 0, 2130706213, 88], [0, 0, 66, 2130706425], [0, 0, 2130706421], [0, 0, 1]],
    [[0, 0, 0, 0, 9], [0, 0, 0, 72, 2130706398], [0, 0, 0, 252, 2130706082, 51], [0, 0, 504, 2130704957, 684, 2130706400], [0, 0, 630, 2130702989, 3600, 2130705767, 8], [0, 504, 2130701519, 10080, 2130701753, 324], [0, 252, 2130702023, 16758, 2130690053, 3420, 2130706370], [72, 2130703997, 17136, 2130673799, 15960, 2130705101], [9, 2130705677, 10584, 2130667625, 39690, 2130697109, 216], [2130706334, 3600, 2130679217, 56448, 2130675563, 3024], [1, 495, 2130696173, 45864, 2130651749, 14994, 2130706013], [2130706421, 2130704948, 19440, 2130653513, 35280, 2130702275], [0, 66, 2970, 2130680729, 42336, 2130691817, 504], [0, 2130706213, 2130702275, 24192, 2130683249, 3528], [0, 495, 4158, 2130690233, 8316, 2130706055], [0, 2130705641, 2130703463, 7560, 2130704669], [0, 924, 1485, 2130704093, 168], [0, 2130705641, 2130705938, 432], [0, 495, 99, 2130706397], [0, 2130706213, 2130706424], [0, 66], [0, 2130706421], [0, 1]],
    [[0, 0, 0, 0, 45], [0, 0, 0, 360, 2130706263], [0, 0, 0, 1260, 2130704723, 241], [0, 0, 2520, 2130699233, 3250, 2130706281], [0, 0, 3150, 2130689633, 17145, 2130703343, 36], [0, 2520, 2130682493, 48000, 2130684653, 1470], [0, 1260, 2130685013, 79590, 2130630233, 15570, 2130706153], [360, 2130694673, 80892, 2130555233, 72600, 2130700493], [45, 2130702833, 49350, 2130528269, 179550, 2130664913, 945], [2130705983, 16320, 2130583793, 252252, 2130569933, 13200], [10, 2025, 2130662153, 199920, 2130468293, 64890, 2130704633], [2130706323, 2130701033, 79920, 2130482993, 149940, 2130688793], [1, 550, 9450, 2130605633, 173460, 2130645701, 2100], [2130706421, 2130704783, 2130695093, 90720, 2130614033, 14364], [66, 3300, 9450, 2130648113, 32340, 2130704921], [2130706213, 2130701813, 2130701033, 26280, 2130699713], [495, 4620, 2025, 2130698513, 630], [2130705641, 2130703133, 2130705983, 1440], [924, 1650, 45, 2130706313], [2130705641, 2130705883], [495, 110], [2130706213, 2130706423], [66], [2130706421], [1]]
  ]
private theorem cell_47_12 : (CJ0.blockMatrix source 47 ((12 : ℤ)-24)).rank ≤ 120 :=
  Fast.cell (z := matrix_47_12) (Fast.bands [(0, 26, 22), (1, 27, 20), (2, 28, 18), (3, 29, 16), (4, 30, 14), (5, 31, 12), (6, 32, 10), (7, 33, 8), (8, 34, 6), (9, 35, 4), (10, 36, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_47_13 : CJ1.Block where
  bank := .leftLow
  cap := 117
  free := [(9, 0), (9, 1), (9, 2), (10, 0)]
  vectors := [
    [[1498, 1704623845, 427272973, 14315772, 133681444, 982862894, 385481447, 1563958805, 1677913021, 1757604578, 1844827142, 865431031, 706252088, 1888059167, 592717420, 36585048, 251149450, 1564941169, 1723846559, 1925439528, 833725028], [426142486, 45952, 867012, 10743616, 524509827, 709771296, 367403583, 1816729335, 747490659, 795106715, 781127771, 411393670, 624306, 1138128931, 1366981977, 1591057005, 1501347623, 2081457363, 1196726413], [568189316, 34993, 1705211714, 1286280166, 922907078, 1353191585, 787712301, 719141929, 1563182417, 31393059, 1534834560, 423879250, 1181829138, 233773583, 771378949, 55880233, 1097209292], [426141988, 426167009, 426607272, 431702653, 475329538, 1196054102, 697698018, 1928954934, 538188675, 661383077, 1070862779, 2127764752, 2036905517, 362978496, 1665765829], [502, 18041, 321096, 429915547, 32952906, 227796345, 1297229472, 1987938638, 1229313062, 323954664, 360862355, 1782695416, 1995938833], [1420471291, 1704576996, 426349215, 712653539, 20953401, 144136608, 1386564012, 526003160, 1395053597, 1463795365, 341920480], [426141489, 7049, 122710, 1423121, 438495853, 1790017564, 915148381, 241379591, 1389116748], [1278423962, 3540, 1704627013, 1279150599, 858722290, 1750284244, 269289064], [1846612277, 426142510, 426163309, 1846885075, 428741021], [1]],
    [[2130706337, 852278811, 1278351312, 2129788469, 2122131685, 2067638935, 45772451, 1901188665, 64023224, 1791801317, 1880901633, 1342556151, 1957251106, 2098335927, 858299887, 1716599774, 352283693, 1183729653, 1587438263, 1572359817, 1076391593], [1278423783, 2130703490, 2130650889, 2130017901, 1272116863, 2085175935, 1008684447, 782557709, 593972139, 2087581445, 649483023, 179159713, 1917759338, 1102161121, 1572160540, 316270803, 1914921241, 562130470, 1239476052], [994329609, 2130704194, 852241185, 1704061977, 421615232, 394018264, 1943418094, 782648275, 1632842098, 595686170, 1749173523, 1040057525, 728035886, 1825437754, 790114291, 1871194609, 1138566061], [1278423815, 1278422216, 1278394061, 1278067942, 1275273147, 404101060, 299329603, 1940285943, 2105449775, 1634779030, 621019053, 1124643276, 335994880, 1000342182, 1078051064], [2130706401, 2130705282, 2130685926, 1278182529, 2128596731, 2116104062, 2047450106, 1729183025, 888257790, 337291927, 1935739566, 369908402, 1108851162], [1420470934, 852281819, 1278410603, 710081025, 2129365541, 2121466202, 941782569, 173132381, 1080939297, 461386614, 677412790], [1278423847, 2130705986, 2130698628, 2130615636, 1277633336, 846800930, 1246990207, 1977990265, 1491877033], [1704565140, 2130706210, 852278652, 1704518821, 425728813, 849343426, 2113350897], [568188380, 1278423784, 1278422472, 568170956, 1278256311], [0, 1]],
    [[3, 1704565264, 426143555, 28712, 268294, 1974024, 864192518, 1339004463, 265040139, 1012345308, 1283861581, 459171509, 1236091458, 1180028609, 989897547, 1979795094, 1771495997, 1253225953, 1824270799, 1006702268, 221183267], [426141289, 92, 1737, 21541, 426338689, 1425684, 434591206, 42249597, 181774710, 1535196176, 987017261, 1152828443, 678159576, 1804761037, 60569894, 915086823, 731108712, 1147546687, 869785082], [568188384, 70, 1704566441, 1278439607, 852424298, 853288988, 5870753, 1307335719, 548715523, 1448168097, 1483405924, 53949822, 162794782, 2062704771, 1227903364, 745838811, 283979049], [426141288, 426141338, 426142219, 426152431, 426240010, 852973637, 856261124, 871636400, 933367718, 1148963758, 1383963365, 1044981044, 1092457198, 1784546882, 135528101], [1, 36, 642, 426148849, 66171, 458388, 2615382, 12620256, 904747742, 190419856, 609241512, 1730524656, 125236058], [1420470956, 1704565170, 426141702, 710240324, 42126, 290598, 569842260, 860249970, 33066088, 119696456, 381280284], [426141287, 14, 245, 2856, 426166195, 1704738084, 427133733, 4823104, 20173560], [1278423860, 7, 1704565270, 1278425325, 852295650, 1704658444, 551056], [1846612242, 426141289, 426141331, 1846612803, 426146693], [0, 0, 1]],
    [[87, 1278427263, 852348110, 828584, 7737938, 56930536, 2048213480, 45165860, 1274194824, 1638322387, 1163785858, 52176199, 500824234, 372300932, 1993722328, 218970337, 1252584778, 1909661617, 1153237036, 2049824385, 562807670], [852282642, 2632, 49624, 614952, 857917730, 40723384, 1093946978, 1210515384, 958783934, 63225066, 1092058485, 1785832569, 2031470767, 929642781, 1147923283, 771844747, 1794153206, 195601400, 1196288228], [1136376817, 1974, 1278460334, 426584929, 1708561139, 1732986874, 166177249, 1246916845, 82579036, 51614339, 2111519305, 871004406, 959516858, 249119549, 24971594, 104904953, 2083660453], [852282612, 852283996, 852308382, 852591390, 855024140, 1723815166, 1815816628, 117459635, 1862542139, 1599660504, 477967997, 890753893, 2043635843, 1978828261, 35299179], [27, 972, 17362, 852487718, 1802787, 12554976, 72068304, 350046048, 1039113071, 1094180366, 210811760, 353929593, 268718129], [710235495, 1278424475, 852293454, 1420598738, 1119552, 7791168, 1181132696, 1922235540, 912030416, 1201965679, 59973099], [852282583, 346, 6125, 72352, 852922562, 1282931607, 878522114, 129296288, 548048380], [426141291, 158, 1278426727, 426176205, 1704884868, 1280760119, 14109216], [1562518052, 852282618, 852283466, 1562530021, 852403746], [], [1]]
  ]
private theorem cell_47_13 : (CJ0.blockMatrix source 47 ((13 : ℤ)-24)).rank ≤ 117 :=
  Fast.cell (z := matrix_47_13) (Fast.bands [(23, 23, 1), (24, 24, 2), (25, 25, 3), (26, 26, 4), (27, 27, 5), (28, 28, 6), (29, 29, 7), (30, 30, 8), (31, 31, 9), (32, 32, 10), (33, 33, 11), (34, 34, 11), (35, 35, 11), (36, 36, 11), (37, 38, 10), (38, 40, 8), (39, 42, 6), (40, 44, 4), (41, 46, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_47 (u : ℕ) : ℕ :=
  match u with
  | 12 => 120
  | 13 => 117
  | u => nominal 47 u

private theorem bound_47 (u : ℕ) :
    (CJ0.blockMatrix source 47 ((u : ℤ)-24)).rank ≤ allowance_47 u := by
  unfold allowance_47
  split
  · exact cell_47_12
  · exact cell_47_13
  · exact (block_rank_le 47 _).trans (rank_le_nominal 47 _)

theorem grade_47 : (∑ u ∈ Finset.range (81-47), (CJ0.blockMatrix source 47 ((u : ℤ)-24)).rank) ≤ 1870 := by
  refine (Finset.sum_le_sum fun u _ => bound_47 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_47)]
  decide +kernel

private def matrix_48_12 : CJ1.Block where
  bank := .leftLow
  cap := 115
  free := [(8, 3), (8, 4), (9, 0), (9, 1), (9, 2), (10, 0)]
  vectors := [
    [[1048052788, 2118775183, 230825400, 1387080624, 189934443, 2079047486, 1639611370, 1406138125, 1986996746, 1007894837, 1638233683, 1752727390, 1281681354, 367439664, 203336320, 1159919108, 1212242627, 992975672, 1674736393, 40909904, 246705555], [791117347, 1663429392, 1765394423, 436399690, 1748399908, 634622144, 1460770152, 783758126, 1884401698, 1996980293, 1130953285, 1928999396, 1233238821, 1498152741, 328848379, 1245104388, 222450345, 823238364, 388629814], [720552345, 410515330, 1849562699, 827997242, 462115456, 2114437665, 283561709, 1242254257, 242841745, 2016697748, 741217633, 506704205, 1555260230, 1131710520, 1413534162, 231021898, 1634207078], [441784529, 1431082542, 182413914, 303306709, 1599490360, 95888918, 1990128768, 365145957, 392921392, 780178010, 1810880683, 1766478552, 721772465, 1292578031, 284562839], [1690947079, 851647853, 658675825, 543156729, 2125479007, 1475440141, 1972650205, 1785058189, 227454424, 1895179831, 406686971, 1966835625, 1021364192], [1942760309, 638433966, 1030868431, 490892480, 635459708, 1347872088, 949940925, 1594898771, 2128168696, 1192413310, 947562810], [802650966, 74543730, 1747810041, 1828374937, 1166021426, 1472122183, 1083023795, 958311253, 1616562456], [6752230, 21373006, 2008884744, 1036380859, 1334007433, 1413171391, 1084717924], [1291197281, 787904234, 79722745, 1]],
    [[312272732, 1104928904, 286776160, 489034726, 1330042920, 1942895996, 665151026, 603455280, 254649442, 1809025087, 1336769741, 390281435, 190002138, 484628773, 642536773, 952971810, 168117916, 210428425, 1518580240, 2102875789, 1423608532], [571355723, 1779444101, 301194250, 1356031792, 1651852544, 575421904, 1389851882, 394162353, 1846666765, 1909904519, 1947293504, 308695327, 621544972, 235057609, 1362490863, 1275492956, 600543910, 1065670012, 157576132], [1262660918, 795193609, 1693922774, 77896422, 174453413, 1363698842, 1248672536, 2108434204, 2047164400, 1442003077, 775014898, 1834437623, 2779688, 1914387212, 100457415, 758485625, 1239776327], [1738259408, 394405106, 169826367, 1059474893, 1331912885, 942875596, 1096969626, 109270977, 632808518, 911146643, 562735677, 2074941810, 1939104925, 1044552088, 1545883630], [1350222284, 1149609040, 717580855, 412755516, 1916082385, 294910317, 1040597238, 1864620185, 1703573765, 179482934, 808303780, 1595531395, 1989209555], [1581327070, 1963638629, 476852000, 152277614, 1207642843, 2091571810, 949754531, 1244646194, 122833226, 218809044, 1777316321], [1783644857, 69629861, 1435364307, 1257815752, 1687945904, 1894392002, 1197127613, 1543495181, 217331068], [1309246736, 1684553659, 1818905501, 1172816415, 1091909858, 1857616776, 648251982], [1640910231, 702151551, 265569602, 0, 1]],
    [[399188549, 2094541499, 1210102627, 2055569312, 1564789021, 1993974995, 1344343509, 808700928, 1841776937, 1377256798, 2013802644, 333745726, 360461450, 529861088, 437575695, 552506487, 1461466537, 2044654965, 493257416, 2015430101, 1076233214], [482396505, 1945120757, 2095923061, 1510777895, 660370654, 456956987, 874077480, 1452397760, 1502645283, 1179309273, 812144387, 539519487, 1969385313, 832474994, 1782581516, 1819759636, 1847188353, 1722696788, 1066582690], [1875132501, 1921680489, 1149306876, 1239228075, 1854048754, 335725717, 376712826, 1351759590, 1400014606, 1252445261, 1838198649, 1648124720, 15529589, 426305716, 71630753, 807855015, 1498261081], [1465947574, 972399916, 1196973286, 807418953, 584958565, 675625677, 482429993, 943521349, 456181948, 1141948028, 1800695131, 1183464989, 741240013, 1510126032, 851150219], [404805627, 1968428379, 1754199127, 685575157, 10712218, 1010787033, 379708201, 1288930077, 1770558035, 2050034154, 726672394, 949006499, 1860503842], [1972376996, 1050353174, 2001632155, 1312841091, 829612064, 70212613, 2124974474, 420205332, 1766313288, 543403771, 330953651], [926506285, 412438150, 1631397911, 470261454, 901287637, 117014330, 683061593, 1306189248, 895123578], [547863830, 1910504410, 1693206586, 1745786627, 169657759, 1556499437, 206337353], [1986413534, 669811012, 1179047020], [1]],
    [[613104676, 159516603, 479527496, 1669877013, 1314318433, 843878106, 1061471036, 235479104, 1420135252, 1178312861, 641444478, 746869604, 1733069865, 314303912, 983631863, 685771968, 271833608, 520455189, 1590050540, 336866133, 1540738334], [872158089, 1265628526, 273310099, 1239341327, 1192784084, 2078587619, 1155280345, 173518013, 830107514, 1465210459, 287610651, 1859531642, 1083772812, 1334280380, 766141646, 752877465, 552559565, 482432477, 941831303], [1496042357, 400374445, 478762473, 1376459041, 1497027946, 1164366142, 1361496198, 1633835852, 1836354694, 539730827, 1099588559, 1443193325, 2573453, 1610845558, 1596140677, 431468075, 884473931], [1202628042, 1883108862, 1839355293, 394644271, 2045994158, 2756357, 1436362982, 1383841827, 2065816564, 1693887619, 233032233, 1576424027, 476653672, 1587344746, 2086834740], [840492139, 246759000, 1810702674, 1379426763, 95474952, 1671106355, 204519019, 988815384, 347823949, 2113890163, 2113420591, 1185370880, 932636761], [1258211643, 1544889133, 915625688, 962239020, 861933709, 958857357, 1784095253, 58444987, 1367852816, 1747422546, 1146166512], [1173657116, 2044636256, 576390149, 1606085756, 1724946396, 344658608, 908937841, 836357876, 1382175617], [1435405553, 1010948683, 946944398, 527554151, 1115520539, 1509288585, 2053005184], [761327516, 706586047, 875863521], [0, 1]],
    [[565761458, 1092463781, 555363957, 295336744, 839678067, 817623075, 823564879, 1025756670, 1162951331, 2037690601, 1311408431, 759963452, 782864607, 1564999557, 222129555, 1788946333, 1669379720, 1580626036, 2063442970, 466930867, 1927972315], [817827590, 706512810, 1689349320, 978752414, 1803995252, 1477586114, 1582321134, 682741413, 1432403041, 1528896863, 1314901208, 1730620876, 2110561221, 1645054028, 1796759724, 1561868769, 151029280, 549343419, 311943364], [1062193995, 546123840, 2097591841, 1522441374, 1851812463, 1797915950, 700993982, 497734512, 763999363, 1872120624, 1217596663, 281990992, 825686234, 1512035514, 2039949298, 238092323, 214913000], [1826460376, 1527134490, 139347136, 2096181761, 728541531, 498788585, 1455717299, 85791452, 23757535, 1672361070, 889622767, 1295841642, 1654857440, 270074656, 1960229829], [1507520003, 324277134, 1189943251, 8821922, 587184699, 1259017244, 67502865, 247683427, 1842724324, 514792766, 705031795, 2119620619, 555088479], [632972579, 24711066, 1609713362, 944906602, 107757978, 1715718216, 1013970989, 1582611830, 1166015876, 1402903547, 1905704369], [1861124240, 1605196768, 412112104, 472951175, 171725585, 1221480529, 1054903772, 1320395671, 604377341], [1458161823, 1801389477, 278299735, 1877263341, 1204719274, 1948272100, 2120983952], [2082391464, 1630664917, 48900568], [0, 0, 1]],
    [[1955533499, 2024246375, 593394398, 677972035, 624167708, 560844807, 1468664753, 386301014, 59791830, 648709608, 843781155, 1725676470, 280311956, 1904500522, 203808004, 1231796193, 1830037822, 2111563781, 1378692693, 1424562868, 1109775732], [1942395618, 328330476, 977035454, 355105929, 826608662, 1608606890, 399576383, 302175624, 1156380095, 1042287598, 1490883573, 286815920, 470779844, 1924334499, 1425058283, 1248632992, 1309698163, 1718602574, 610394838], [1236539513, 1752509174, 1425676743, 2081765473, 317253236, 659672425, 1302349942, 1441986416, 2008042780, 973649331, 1007739758, 1016589070, 1237532605, 1606902319, 564070662, 306094155, 1752507571], [366627420, 780975969, 1605145819, 394184665, 1238379039, 1131444639, 964515881, 68031152, 6424407, 432414021, 758659023, 780142537, 570352584, 403912416, 878689403], [1992028008, 436807582, 1816270895, 1797264154, 214434954, 118261559, 1384550855, 2049064223, 319831585, 1551478074, 207418674, 237969632, 1487450934], [249284214, 1628431790, 1889383904, 577264298, 1883587623, 632919053, 648847373, 225938700, 1392655982, 1599008302, 1178748009], [2059177573, 1018920993, 78823560, 1570327193, 1089634604, 81608737, 900939004, 1781610152, 86899467], [1558251022, 1679524379, 480264151, 397157487, 1243710419, 460918734, 1214367793], [1405873230, 305429326, 1271686435], [], [1]]
  ]
private theorem cell_48_12 : (CJ0.blockMatrix source 48 ((12 : ℤ)-24)).rank ≤ 115 :=
  Fast.cell (z := matrix_48_12) (Fast.bands [(24, 24, 1), (25, 25, 2), (26, 26, 3), (27, 27, 4), (28, 28, 5), (29, 29, 6), (30, 30, 7), (31, 31, 8), (32, 32, 9), (33, 33, 10), (34, 34, 11), (35, 35, 11), (36, 36, 11), (37, 38, 10), (38, 40, 9), (39, 42, 7), (40, 44, 5), (41, 46, 3), (42, 48, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_48_13 : CJ1.Block where
  bank := .leftLow
  cap := 109
  free := [(9, 1)]
  vectors := [
    [[1807872125, 1355904095, 1162203535, 1291337580, 1937009240, 1937031626, 2001731673, 1163021034, 1359480766, 1821383998, 44589181, 1291917490, 851629344, 2129198981, 1214423954, 1698736332, 203234519, 937507627, 1420466506, 560706599], [1807872125, 1678738403, 1614171565, 1807872448, 129136792, 1807894834, 193836839, 969184195, 390296571, 1431087427, 744208187, 547709303, 303920041, 1825278940, 1519851447, 178884885, 24349634, 913157993], [1807872125, 2001572711, 1743305287, 64567161, 64569631, 1743325203, 581218069, 387966126, 2330445, 1428756982, 1446157638, 1232258098, 1202368376, 622910564, 896940883, 1412650435], [1807872125, 193700586, 1549604701, 645668893, 1549607171, 193718032, 387500037, 466089, 1864356, 1426892626, 19265012, 1212993086, 2120081723, 633535274], [1807872125, 516534894, 1033069807, 1743305519, 1937008085, 387416380, 83657, 382432, 1481924, 1425410702, 724560743, 488432343], [1807872125, 839369202, 193700605, 1549604914, 387403171, 13209, 70448, 311984, 1169940, 1424240762], [1807872125, 1162203510, 1162203528, 387401386, 1785, 11424, 59024, 252960], [1807872125, 1485037818, 1807872143, 710235676, 1420472542, 710245315], [1807872125, 1807872126, 17, 710235659], [1807872125, 1]]
  ]
private theorem cell_48_13 : (CJ0.blockMatrix source 48 ((13 : ℤ)-24)).rank ≤ 109 :=
  Fast.cell (z := matrix_48_13) (Fast.bands [(24, 24, 1), (25, 25, 2), (26, 26, 3), (27, 27, 4), (28, 28, 5), (29, 29, 6), (30, 30, 7), (31, 31, 8), (32, 32, 9), (33, 33, 10), (34, 34, 11), (35, 35, 11), (36, 36, 11), (37, 37, 11), (38, 39, 10), (39, 41, 8), (40, 43, 6), (41, 45, 4), (42, 47, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_48 (u : ℕ) : ℕ :=
  match u with
  | 12 => 115
  | 13 => 109
  | u => nominal 48 u

private theorem bound_48 (u : ℕ) :
    (CJ0.blockMatrix source 48 ((u : ℤ)-24)).rank ≤ allowance_48 u := by
  unfold allowance_48
  split
  · exact cell_48_12
  · exact cell_48_13
  · exact (block_rank_le 48 _).trans (rank_le_nominal 48 _)

theorem grade_48 : (∑ u ∈ Finset.range (81-48), (CJ0.blockMatrix source 48 ((u : ℤ)-24)).rank) ≤ 1747 := by
  refine (Finset.sum_le_sum fun u _ => bound_48 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_48)]
  decide +kernel

private def matrix_49_11 : CJ1.Block where
  bank := .rightLow
  cap := 112
  free := [(18, 3), (20, 2), (22, 1), (24, 0)]
  vectors := [
    [[0, 0, 0, 2130706432], [0, 0, 0, 2130706426, 4], [0, 0, 2130706412, 35, 2130706427], [0, 0, 2130706398, 126, 2130706363, 4], [0, 2130706398, 245, 2130706118, 70, 2130706432], [0, 2130706412, 280, 2130705698, 420, 2130706398], [2130706426, 189, 2130705453, 1225, 2130706118, 7], [2130706432, 70, 2130705677, 1960, 2130705208, 126], [11, 2130706118, 1764, 2130703983, 735, 2130706412], [0, 2130706378, 840, 2130703787, 1960, 2130706188], [0, 165, 2130704963, 2646, 2130705453, 35], [0, 0, 2130706103, 1764, 2130704669, 280], [0, 0, 462, 2130704963, 756, 2130706398], [0, 0, 0, 2130705971, 840, 2130706244], [0, 0, 0, 330, 2130706118, 21], [0, 0, 0, 2130706268, 70], [0, 0, 0, 55, 2130706426], [0, 0, 0, 2130706422], [0, 0, 0, 1]],
    [[0, 0, 0, 2130706425], [0, 0, 0, 2130706377, 31], [0, 0, 2130706265, 272, 2130706388], [0, 0, 2130706153, 980, 2130705905, 29], [0, 2130706153, 1904, 2130704053, 512, 2130706426], [0, 2130706265, 2170, 2130700889, 3080, 2130706185], [2130706377, 1456, 2130699083, 8960, 2130704193, 48], [2130706425, 532, 2130700833, 14210, 2130697753, 868], [80, 2130704165, 12544, 2130689283, 5040, 2130706293], [2130706432, 2130706073, 5712, 2130688401, 13230, 2130704809], [11, 960, 2130697025, 17248, 2130700063, 224], [0, 2130706378, 2130704753, 10584, 2130695457, 1750], [0, 165, 2016, 2130698201, 4480, 2130706223], [0, 0, 2130706103, 2130704753, 4368, 2130705369], [0, 0, 462, 960, 2130704921, 112], [0, 0, 2130705971, 2130706073, 308], [0, 0, 330, 80, 2130706405], [0, 0, 2130706268, 2130706425], [0, 0, 55], [0, 0, 2130706422], [0, 0, 1]],
    [[0, 0, 0, 2130706397], [0, 0, 0, 2130706181, 135], [0, 0, 2130705677, 1188, 2130706243], [0, 0, 2130705173, 4284, 2130704192, 119], [0, 2130705173, 8316, 2130696317, 2115, 2130706405], [0, 2130705677, 9450, 2130682913, 12744, 2130705434], [2130706181, 6300, 2130675437, 36960, 2130697397, 189], [2130706397, 2268, 2130683123, 58086, 2130671573, 3420], [324, 2130697277, 50274, 2130638393, 19740, 2130705893], [2130706424, 2130705137, 21840, 2130636755, 51030, 2130700217], [90, 3024, 2130672329, 64386, 2130682493, 840], [2130706432, 2130706028, 2130701897, 36456, 2130666743, 6426], [11, 1080, 4536, 2130679385, 15750, 2130705677], [0, 2130706378, 2130704543, 2130703409, 13776, 2130702779], [0, 165, 2268, 1296, 2130701813, 378], [0, 2130706103, 2130704543, 2130706109, 924], [0, 462, 1080, 36, 2130706349], [0, 2130705971, 2130706028], [0, 330, 90], [0, 2130706268, 2130706424], [0, 55], [0, 2130706422], [0, 1]],
    [[0, 0, 0, 2130706313], [0, 0, 0, 2130705593, 435], [0, 0, 2130703913, 3840, 2130705838], [0, 0, 2130702233, 13860, 2130699383, 364], [0, 2130702233, 26880, 2130674573, 6500, 2130706349], [0, 2130703913, 30450, 2130632513, 39195, 2130703423], [2130705593, 20160, 2130609623, 113280, 2130679208, 560], [2130706313, 7140, 2130634613, 176400, 2130601913, 10125], [960, 2130679133, 149688, 2130504833, 58080, 2130704858], [2130706388, 2130703073, 61950, 2130505085, 148050, 2130688433], [405, 6720, 2130613823, 181440, 2130638183, 2400], [2130706423, 2130704813, 2130698033, 95550, 2130596813, 18060], [100, 3780, 6720, 2130637343, 42840, 2130704333], [2130706432, 2130705983, 2130700763, 2130703073, 34650, 2130696605], [11, 1200, 5670, 960, 2130694883, 1008], [2130706378, 2130704333, 2130702653, 2130706313, 2310], [165, 2520, 1620, 0, 2130706223], [2130706103, 2130704333, 2130706028], [462, 1200, 45], [2130705971, 2130705983], [330, 100], [2130706268, 2130706423], [55], [2130706422], [1]]
  ]
private theorem cell_49_11 : (CJ0.blockMatrix source 49 ((11 : ℤ)-24)).rank ≤ 112 :=
  Fast.cell (z := matrix_49_11) (Fast.bands [(0, 29, 21), (1, 30, 19), (2, 31, 17), (3, 32, 15), (4, 33, 13), (5, 34, 11), (6, 35, 9), (7, 36, 7), (8, 37, 5), (9, 38, 3), (10, 39, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_49_12 : CJ1.Block where
  bank := .leftLow
  cap := 108
  free := [(9, 0), (9, 1)]
  vectors := [
    [[2130706383, 2130704351, 2130663901, 2130138173, 2125121413, 2087650693, 1859626897, 697857457, 2036786042, 47728306, 1203091806, 1806559668, 939146381, 1434417547, 1833712244, 1935858814, 1844071391, 580682403, 1294046359, 1703743557], [1420470911, 1420469150, 2130670353, 1419999182, 1415931572, 2096436665, 1919376197, 1036585353, 1541640744, 1911838719, 2092972344, 1992024634, 381802156, 1466747891, 1195229353, 100800028, 2035240055, 980178832], [710235439, 2130704893, 2130676313, 709849811, 2127070593, 2103801217, 1968032233, 1304906393, 672527566, 2078562662, 1976877430, 331116766, 1169396237, 1723479740, 1004592960, 1184947154], [2130706400, 2130705147, 2130681798, 2130397189, 2127845926, 2109924347, 2007302516, 1515468953, 1636399618, 932779981, 385241827, 920700123, 392581777, 482433953], [1420470928, 1420469912, 2130686825, 2130464601, 2128506043, 2114969075, 2038683733, 1679006437, 234512969, 911764161, 731831328, 2036046750], [710235456, 2130705621, 2130691411, 2130523653, 2129063078, 2119082513, 2063481429, 1804572449, 779425733, 127056797], [2130706417, 2130705841, 2130695573, 2130574973, 2129528333, 2122396901, 2082828449, 1899753953], [1420470945, 1420470572, 2130699328, 710148211, 709441351, 2125030609], [710235473, 2130706247, 2130702693, 1420421338], [1]],
    [[1065353218, 1065353279, 1065354494, 1065370293, 167895, 1294657, 8152235, 43090385, 1260384046, 1832549419, 1587703053, 680053017, 987526170, 1597611427, 371295739, 2018528042, 1791793138, 1278115521, 1874554748, 1120779168], [710235479, 710235532, 1065354303, 710249691, 710372281, 1032954, 6369883, 32973512, 146132610, 1272908476, 1548415631, 1446002302, 1066023292, 1146086130, 454205599, 1645808792, 12061359, 1570451283], [355117740, 1065353263, 910, 1420482612, 109915, 813371, 4916782, 24949470, 1173718909, 763851898, 1353522456, 1837886039, 1137936917, 843553977, 4242848, 1329461067], [1, 39, 1065353964, 9386, 1065440037, 630591, 1069095637, 18643560, 1144821391, 293946796, 953618094, 604925271, 591447551, 1029075285], [1775588695, 1775588726, 1065353815, 1065360598, 1065420353, 1065833014, 1068155726, 1079090891, 57579918, 919433749, 1375866341, 1869447126], [1420470956, 25, 1065353679, 5624, 50505, 356643, 1067411619, 9963360, 41181888, 1567753402], [1065353217, 1065353235, 339, 4095, 1065389809, 1065610435, 1476552, 7095528], [710235478, 710235490, 1065353444, 1420473732, 355142828, 178024], [355117739, 1065353223, 1065353344, 1775590346], [0, 1]]
  ]
private theorem cell_49_12 : (CJ0.blockMatrix source 49 ((12 : ℤ)-24)).rank ≤ 108 :=
  Fast.cell (z := matrix_49_12) (Fast.bands [(25, 25, 1), (26, 26, 2), (27, 27, 3), (28, 28, 4), (29, 29, 5), (30, 30, 6), (31, 31, 7), (32, 32, 8), (33, 33, 9), (34, 34, 10), (35, 35, 11), (36, 36, 11), (37, 37, 11), (38, 39, 10), (39, 41, 9), (40, 43, 7), (41, 45, 5), (42, 47, 3), (43, 49, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_49 (u : ℕ) : ℕ :=
  match u with
  | 11 => 112
  | 12 => 108
  | u => nominal 49 u

private theorem bound_49 (u : ℕ) :
    (CJ0.blockMatrix source 49 ((u : ℤ)-24)).rank ≤ allowance_49 u := by
  unfold allowance_49
  split
  · exact cell_49_11
  · exact cell_49_12
  · exact (block_rank_le 49 _).trans (rank_le_nominal 49 _)

theorem grade_49 : (∑ u ∈ Finset.range (81-49), (CJ0.blockMatrix source 49 ((u : ℤ)-24)).rank) ≤ 1627 := by
  refine (Finset.sum_le_sum fun u _ => bound_49 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_49)]
  decide +kernel

end Front6960ListBank

end Merged6967_R6960Front6960ListCells4

section Merged6967_R6960Front6960ListCells5
set_option Elab.async false


set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6960ListBank
open scoped BigOperators

private def matrix_50_11 : CJ1.Block where
  bank := .leftLow
  cap := 106
  free := [(8, 2), (8, 3), (9, 0), (9, 1)]
  vectors := [
    [[1617399883, 426141277, 1782045184, 38737473, 213044268, 735854403, 1083376791, 1852152790, 226701581, 1754667449, 1180511125, 1122289687, 554766290, 718458690, 1059683309, 1095133439, 1571502979, 1671449824, 731820462, 683876046], [167873840, 1975745958, 309920792, 1020154507, 1743286504, 890876716, 890087876, 149898625, 906136332, 613812935, 930628248, 1516355579, 1709670218, 1075595496, 829812970, 1944845124, 652389108, 339661879], [929762807, 968502919, 1084723174, 2130705109, 1549591779, 464781894, 386768917, 2088568602, 2114969075, 2067007603, 624613633, 1212731790, 415909564, 521087746, 536136738, 1974982310], [1772360351, 1423699295, 1452754319, 1452753511, 338967530, 958752551, 1123049146, 2128485656, 2120452475, 2089379875, 279292179, 272475979, 1791377747, 2111549915], [564960039, 968502922, 1375274111, 1123462852, 590781508, 1859484738, 2130445620, 424735849, 1271912955, 1962389446, 332928267, 869186718], [1568974737, 1491494502, 1297793896, 135590109, 891019675, 426117355, 852126707, 851428517, 848275340, 409832323], [522991579, 619841871, 19370049, 2053226059, 2130704921, 852269864, 852195965, 425649565], [1688423431, 242125731, 1084723273, 1420470911, 2130705838, 1278418124], [803857427, 116220351, 1]],
    [[823736153, 1692031580, 51138057, 867854816, 1310804585, 738739303, 78928904, 1314506706, 787608119, 427729722, 46087977, 20530141, 258809341, 631890466, 1568133796, 971404457, 1888087939, 1554000489, 1578829257, 352689499], [995857932, 400558703, 2075634711, 209525967, 1818318445, 1672104868, 1881068022, 951726630, 1385672947, 482025129, 1273606179, 1760969367, 1079116396, 87201577, 971837332, 2083028824, 86890334, 215902712], [628577388, 1705324757, 2008083663, 1844225016, 1355498328, 1590035774, 151300690, 1134836551, 1599434946, 1578329364, 603577378, 1069323007, 928599440, 740348460, 867106689, 1139556127], [1852600954, 832417412, 578727979, 2100661220, 1120663110, 591247166, 505042750, 1750423873, 609695000, 713930680, 875493430, 1364670420, 1708717617, 168596480], [406515764, 1530750070, 1673516086, 1558421633, 825432206, 940835210, 355141758, 304514981, 1979103084, 1186089204, 59062777, 385766632], [551734684, 1157116834, 1680569607, 1919168604, 843981411, 1065355492, 532691214, 989335573, 1978879752, 255133328], [157551281, 1329724673, 143715526, 747130842, 532676762, 1065354468, 1598038141, 608819546], [1354671988, 1536074123, 1893192621, 1124539512, 1242912153, 1242912686], [2012390372, 1263665720, 0, 1]],
    [[665845905, 1065359186, 177680308, 1777213162, 992650027, 480654648, 983105710, 1881193091, 1006294454, 306699523, 1216202412, 775382516, 1278762577, 1088103529, 1651517703, 682381661, 2113765931, 1767557762, 1303100772, 464267339], [59186402, 887798881, 1775679147, 1303286476, 899353870, 621523844, 384171474, 1049846347, 1060889452, 1408948465, 1088139119, 515113898, 441938689, 2034687518, 423087727, 1465717424, 1857692489, 84817661], [1775588778, 710238798, 710300511, 840075, 1606081261, 416170252, 1624223914, 2015789230, 141016241, 150556631, 2103426278, 523594671, 1274564699, 1743530444, 641068973, 83349507], [1553640167, 2086319032, 1509295014, 1509818704, 848786734, 351135158, 782959547, 1846464977, 1694427739, 1620921704, 222625862, 1252858169, 1374359110, 2710748], [1524047002, 177560379, 1331720214, 177920631, 1113145117, 25433837, 1932794140, 824654853, 542231077, 154559365, 495735941, 98028847], [1686809283, 799015800, 621472778, 444107517, 1067334474, 1080246364, 625510561, 2089941319, 1187566590, 852448161], [2041927010, 1242912524, 976582049, 104925, 533682902, 1073108387, 1647810113, 272012444], [458693750, 932184213, 887797180, 651086458, 1953527719, 1956321125], [1198522369, 1420470962], [1]],
    [[859546341, 1065353046, 952357740, 32237047, 976115096, 1320042847, 348334353, 1070419068, 749078966, 1707721725, 6292161, 1558716235, 669434511, 2006367650, 1828447820, 1132365629, 118229432, 99182344, 1615371521, 1699508916], [317453733, 1468895971, 613382582, 1560331659, 1274863586, 917531116, 193775738, 1641479538, 380789309, 782058490, 570313268, 66743771, 1239558150, 363474234, 2045627432, 374588497, 701289343, 590965001], [419684598, 1872438890, 903934173, 2130682068, 48192167, 740757166, 844541970, 1685511889, 1335272151, 729866235, 756778007, 2123649720, 723165173, 863013906, 688473794, 1866531360], [1166238936, 343011384, 1121847908, 1121832558, 1036948007, 309552708, 1106530928, 494806877, 1959807133, 745159782, 125523582, 1784784501, 1064053278, 1824215495], [426410314, 1339762333, 169487154, 758649868, 1690744142, 1548857773, 1771001502, 2106792482, 957585074, 1231958370, 292614998, 629249052], [330905165, 799014885, 815156116, 1799794895, 1452694949, 1064910715, 529943446, 1583668654, 1000078427, 95543801], [879723489, 1049211487, 1170274105, 1355900830, 532645817, 1065119441, 1596548840, 2122705213], [2072865286, 157381720, 1081494837, 1361283459, 1953135614, 1953050172], [1779624123, 451968031], [0, 1]]
  ]
private theorem cell_50_11 : (CJ0.blockMatrix source 50 ((11 : ℤ)-24)).rank ≤ 106 :=
  Fast.cell (z := matrix_50_11) (Fast.bands [(26, 26, 1), (27, 27, 2), (28, 28, 3), (29, 29, 4), (30, 30, 5), (31, 31, 6), (32, 32, 7), (33, 33, 8), (34, 34, 9), (35, 35, 10), (36, 36, 11), (37, 37, 11), (38, 39, 10), (39, 41, 9), (40, 43, 8), (41, 45, 6), (42, 47, 4), (43, 49, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_50 (u : ℕ) : ℕ :=
  match u with
  | 11 => 106
  | u => nominal 50 u

private theorem bound_50 (u : ℕ) :
    (CJ0.blockMatrix source 50 ((u : ℤ)-24)).rank ≤ allowance_50 u := by
  unfold allowance_50
  split
  · exact cell_50_11
  · exact (block_rank_le 50 _).trans (rank_le_nominal 50 _)

theorem grade_50 : (∑ u ∈ Finset.range (81-50), (CJ0.blockMatrix source 50 ((u : ℤ)-24)).rank) ≤ 1513 := by
  refine (Finset.sum_le_sum fun u _ => bound_50 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_50)]
  decide +kernel

private def matrix_51_10 : CJ1.Block where
  bank := .rightLow
  cap := 104
  free := [(16, 4), (18, 3), (20, 2), (22, 1), (24, 0)]
  vectors := [
    [[0, 0, 0, 1], [0, 0, 6, 2130706429], [0, 0, 15, 2130706403, 6], [0, 20, 2130706343, 60, 2130706429], [0, 15, 2130706293, 225, 2130706373, 1], [6, 2130706313, 420, 2130706133, 30], [1, 2130706379, 420, 2130705733, 225, 2130706427], [2130706423, 216, 2130705593, 700, 2130706343], [0, 45, 2130705929, 1050, 2130706013, 15], [0, 2130706313, 756, 2130705593, 140], [0, 0, 210, 2130705677, 420, 2130706413], [0, 0, 2130706181, 504, 2130706313], [0, 0, 0, 210, 2130706217, 15], [0, 0, 0, 2130706313, 54], [0, 0, 0, 0, 45, 2130706427], [0, 0, 0, 0, 2130706423], [0, 0, 0, 0, 1]],
    [[0, 0, 0, 7], [0, 0, 42, 2130706406], [0, 0, 105, 2130706230, 39], [0, 140, 2130705824, 392, 2130706408], [0, 105, 2130705488, 1470, 2130706055, 6], [42, 2130705628, 2730, 2130704543, 182], [7, 2130706076, 2695, 2130702058, 1365, 2130706398], [2130706370, 1344, 2130701288, 4200, 2130705908], [1, 252, 2130703493, 6125, 2130704018, 84], [2130706423, 2130705845, 4116, 2130701778, 770], [0, 45, 882, 2130702611, 2205, 2130706328], [0, 2130706313, 2130705551, 2352, 2130705838], [0, 0, 210, 588, 2130705509, 70], [0, 0, 2130706181, 2130706181, 210], [0, 0, 0, 210, 63, 2130706412], [0, 0, 0, 2130706313, 2130706426], [0, 0, 0, 45], [0, 0, 0, 2130706423], [0, 0, 0, 1]],
    [[0, 0, 0, 28], [0, 0, 168, 2130706329], [0, 0, 420, 2130705649, 145], [0, 560, 2130704081, 1464, 2130706343], [0, 420, 2130702793, 5488, 2130705065, 21], [168, 2130703353, 10136, 2130699601, 640], [28, 2130705089, 9870, 2130690753, 4788, 2130706313], [2130706209, 4760, 2130688373, 14560, 2130704641], [8, 784, 2130696633, 20650, 2130698313, 280], [2130706361, 2130704865, 12936, 2130691313, 2520], [1, 288, 1960, 2130695065, 6930, 2130706097], [2130706423, 2130705761, 2130704865, 6664, 2130704613], [0, 45, 1008, 784, 2130703913, 210], [0, 2130706313, 2130705425, 2130706209, 560], [0, 0, 210, 672, 28, 2130706377], [0, 0, 2130706181, 2130706145], [0, 0, 210, 72], [0, 0, 2130706313, 2130706425], [0, 0, 45], [0, 0, 2130706423], [0, 0, 1]],
    [[0, 0, 0, 84], [0, 0, 504, 2130706133], [0, 0, 1260, 2130704165, 405], [0, 1680, 2130699629, 4104, 2130706188], [0, 1260, 2130695933, 15372, 2130702698, 56], [504, 2130697613, 28224, 2130687821, 1710], [84, 2130702653, 27090, 2130664097, 12744, 2130706118], [2130705845, 12600, 2130658679, 38304, 2130701753], [36, 1764, 2130681863, 52920, 2130685517, 720], [2130706145, 2130703493, 30996, 2130668633, 6384], [9, 1008, 2940, 2130680099, 17010, 2130705593], [2130706352, 2130704417, 2130704669, 15120, 2130702023], [1, 324, 2520, 588, 2130700763, 504], [2130706423, 2130705677, 2130704417, 2130706349, 1260], [0, 45, 1134, 1008, 0, 2130706307], [0, 2130706313, 2130705299, 2130706145], [0, 210, 756, 36], [0, 2130706181, 2130706109], [0, 210, 81], [0, 2130706313, 2130706424], [0, 45], [0, 2130706423], [0, 1]],
    [[0, 0, 0, 210], [0, 0, 1260, 2130705713], [0, 0, 3150, 2130700973, 945], [0, 4200, 2130690053, 9600, 2130705873], [0, 3150, 2130681233, 35910, 2130697883, 126], [1260, 2130685433, 65520, 2130663953, 3850], [210, 2130697613, 61950, 2130610673, 28575, 2130705733], [2130705173, 27720, 2130600593, 84960, 2130696083], [120, 3150, 2130654773, 114660, 2130660713, 1575], [2130705593, 2130702233, 63252, 2130625793, 13800], [45, 2520, 3150, 2130653513, 35910, 2130704633], [2130706073, 2130702233, 2130705173, 30240, 2130697193], [10, 1260, 4200, 210, 2130695093, 1050], [2130706343, 2130703913, 2130703913, 0, 2520], [1, 360, 3150, 840, 0, 2130706181], [2130706423, 2130705593, 2130703913, 2130706313], [45, 1260, 1260], [2130706313, 2130705173, 2130706073], [210, 840, 45], [2130706181, 2130706073], [210, 90], [2130706313, 2130706423], [45], [2130706423], [1]]
  ]
private theorem cell_51_10 : (CJ0.blockMatrix source 51 ((10 : ℤ)-24)).rank ≤ 104 :=
  Fast.cell (z := matrix_51_10) (Fast.bands [(0, 32, 20), (1, 33, 18), (2, 34, 16), (3, 35, 14), (4, 36, 12), (5, 37, 10), (6, 38, 8), (7, 39, 6), (8, 40, 4), (9, 41, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_51_11 : CJ1.Block where
  bank := .leftLow
  cap := 99
  free := [(9, 0)]
  vectors := [
    [[1, 44, 946, 13244, 135751, 1086008, 7059052, 38320568, 177232627, 708930508, 350550345, 1277219833, 1914324716, 778572040, 2028367579, 1926028725, 1227051479, 266326550, 399489825], [1, 43, 903, 12341, 123410, 962598, 6096454, 32224114, 145008513, 563921995, 1917334783, 1490591483, 423733233, 354838807, 1673528772, 252499953, 974551526], [1, 42, 861, 11480, 111930, 850668, 5245786, 26978328, 118030185, 445891810, 1471442973, 19148510, 404584723, 2080960517, 1723274688], [1, 41, 820, 10660, 101270, 749398, 4496388, 22481940, 95548245, 350343565, 1121099408, 1028755535, 1506535621], [1, 40, 780, 9880, 91390, 658008, 3838380, 18643560, 76904685, 273438880, 847660528], [1, 39, 741, 9139, 82251, 575757, 3262623, 15380937, 61523748], [1, 38, 703, 8436, 73815, 501942, 2760681], [1, 37, 666, 7770, 66045], [1, 36, 630], [1]]
  ]
private theorem cell_51_11 : (CJ0.blockMatrix source 51 ((11 : ℤ)-24)).rank ≤ 99 :=
  Fast.cell (z := matrix_51_11) (Fast.bands [(27, 27, 1), (28, 28, 2), (29, 29, 3), (30, 30, 4), (31, 31, 5), (32, 32, 6), (33, 33, 7), (34, 34, 8), (35, 35, 9), (36, 36, 10), (37, 37, 11), (38, 38, 11), (39, 40, 10), (40, 42, 9), (41, 44, 8), (42, 46, 6), (43, 48, 4), (44, 50, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_51 (u : ℕ) : ℕ :=
  match u with
  | 10 => 104
  | 11 => 99
  | u => nominal 51 u

private theorem bound_51 (u : ℕ) :
    (CJ0.blockMatrix source 51 ((u : ℤ)-24)).rank ≤ allowance_51 u := by
  unfold allowance_51
  split
  · exact cell_51_10
  · exact cell_51_11
  · exact (block_rank_le 51 _).trans (rank_le_nominal 51 _)

theorem grade_51 : (∑ u ∈ Finset.range (81-51), (CJ0.blockMatrix source 51 ((u : ℤ)-24)).rank) ≤ 1401 := by
  refine (Finset.sum_le_sum fun u _ => bound_51 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_51)]
  decide +kernel

private def matrix_52_10 : CJ1.Block where
  bank := .leftLow
  cap := 98
  free := [(8, 2), (9, 0)]
  vectors := [
    [[1023574659, 888954863, 960906832, 1011969635, 489738895, 1343888024, 1146663239, 924184467, 343179589, 1639986520, 327596055, 1478208044, 1434583667, 1195729139, 621926267, 488602679, 173701669, 906973706, 2053386711], [1620079619, 1480817761, 1186046835, 1833614578, 1687390633, 714886466, 1453023760, 1216540896, 1654083461, 1765519521, 1203642212, 1807143567, 1583607627, 834918300, 885353632, 1016481855, 1630377228], [85878146, 879670739, 396896303, 1223183413, 1578301965, 1211585264, 1318391153, 566577275, 815816989, 870301758, 923600473, 1825860810, 771596628, 272268649, 1502483671], [682383106, 1216220230, 382970116, 1555090825, 422428357, 334234020, 385326244, 1448509452, 2089772785, 240075817, 1944944264, 1692521087, 412027244], [1278888066, 359759801, 803076721, 687025226, 199609226, 1346202245, 1490128525, 905341255, 829230017, 1225594157, 166021358], [1875393026, 440995885, 1316024565, 482774487, 1199973441, 2005373986, 76613883, 1183828356, 1065805597], [341191553, 1459928482, 1580622095, 420106639, 745051257, 1023577023, 2012348343], [937696513, 1285851159, 1255677758, 1852182739, 431711981], [1534201473, 2049470349, 1]],
    [[125335667, 292449661, 1378687211, 1462176541, 1962835607, 1999206068, 1254037333, 312683735, 1774241685, 1707540944, 212564389, 1527584920, 184597878, 1090789691, 1961093799, 281683473, 395209599, 438810372, 1023796835], [1295135278, 292449697, 584895479, 1838196838, 1210970797, 1164940644, 1764661907, 1621234805, 132873462, 1022880538, 2001162394, 1568738856, 1931329469, 837363253, 457824175, 383052556, 2056098461], [334228456, 83556944, 2005367230, 1420423122, 1419992622, 622914881, 1939345385, 1957504038, 141034254, 495100943, 442872469, 2100665266, 40629338, 133965378, 320720963], [1504028067, 1796477835, 626675565, 1963554901, 2046781757, 1125168813, 1193445675, 529697445, 1811362557, 358380163, 1608074413, 2074514058, 855570076], [543121245, 1169799504, 2088925750, 543093239, 1294862033, 457462521, 488096516, 55126649, 1812029503, 165198842, 1347609496], [1712920856, 334228384, 1378690886, 208872921, 1963398492, 374516823, 115946694, 2081045107, 1906325705], [752014034, 1420470908, 2005369806, 1462236721, 250543978, 124336999, 2124318975], [1921813645, 167114210, 1086242044, 125328969, 125262924], [960906823, 835571156], [1]]
  ]
private theorem cell_52_10 : (CJ0.blockMatrix source 52 ((10 : ℤ)-24)).rank ≤ 98 :=
  Fast.cell (z := matrix_52_10) (Fast.bands [(28, 28, 1), (29, 29, 2), (30, 30, 3), (31, 31, 4), (32, 32, 5), (33, 33, 6), (34, 34, 7), (35, 35, 8), (36, 36, 9), (37, 37, 10), (38, 38, 11), (39, 40, 10), (40, 42, 9), (41, 44, 8), (42, 46, 7), (43, 48, 5), (44, 50, 3), (45, 52, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_52 (u : ℕ) : ℕ :=
  match u with
  | 10 => 98
  | u => nominal 52 u

private theorem bound_52 (u : ℕ) :
    (CJ0.blockMatrix source 52 ((u : ℤ)-24)).rank ≤ allowance_52 u := by
  unfold allowance_52
  split
  · exact cell_52_10
  · exact (block_rank_le 52 _).trans (rank_le_nominal 52 _)

theorem grade_52 : (∑ u ∈ Finset.range (81-52), (CJ0.blockMatrix source 52 ((u : ℤ)-24)).rank) ≤ 1296 := by
  refine (Finset.sum_le_sum fun u _ => bound_52 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_52)]
  decide +kernel

private def matrix_53_9 : CJ1.Block where
  bank := .leftLow
  cap := 96
  free := [(8, 0), (8, 1), (8, 2), (9, 0)]
  vectors := [
    [[1826320665, 1826357646, 1827136776, 1837925598, 1948369206, 1013259654, 522862104, 1830283541, 395716997, 1761037003, 1500729974, 2115139948, 149780803, 824766620, 810713386, 1853418302, 1001882412, 1781892209, 1306904505], [674, 28946, 1065967450, 769553631, 88962829, 728300589, 643660387, 234195624, 812841586, 1400741894, 1054851895, 361321935, 714546875, 802579667, 669199548, 872921811, 209942774], [1065353723, 304408013, 1826766396, 6155252, 62955582, 509434512, 1264010009, 2095472252, 116188384, 290603967, 425020852, 1249569562, 26114418, 637605821, 728642855], [760966946, 456595026, 1217857241, 308620346, 42889485, 344291883, 1974318571, 1204655708, 1956112905, 41846846, 956197321, 87018751, 470796060], [1217546776, 304396597, 913363254, 2751920, 332144029, 1439859236, 252647008, 1238840279, 890647958, 492612482, 376661160], [304386780, 1826325771, 761088047, 153838631, 321060086, 1352097419, 1659102461, 1278696014, 1984848438], [152193391, 608776294, 913222008, 1218401582, 465443625, 1899812424, 504995832], [760966609, 760967644, 1826342301, 1826647551, 764623502], [1]],
    [[608773219, 608771185, 608728309, 608134220, 1667401538, 2074834727, 683766852, 1450348356, 1219096316, 709580704, 1099046939, 761109725, 1324270090, 1600322043, 566053298, 1149094675, 1725557676, 851519089, 377628558], [2130706396, 2130704843, 1597996060, 75624225, 1060454248, 1025208825, 794719494, 1653393219, 940143339, 1480499560, 493005007, 117606932, 1403980190, 1535094366, 65271761, 1230860752, 658773547], [1598029797, 1521931994, 1674101966, 2130368120, 2127241810, 2102634881, 1943412365, 1073407125, 1319811551, 894813906, 1522852304, 1516671700, 1726554745, 1808874620, 492149961], [1141449855, 684869100, 760949555, 456347518, 1062994384, 1046385079, 483029201, 1120547469, 1680779618, 514880377, 1367880785, 1579662147, 1988838032], [760966570, 1521932623, 1369728730, 2130555553, 1520407375, 1814070364, 223208813, 761781992, 75449370, 700562237, 254746602], [456579942, 1674126159, 76090037, 1293553114, 455663527, 753546368, 26431742, 403182771, 601519750], [228289971, 913159737, 304383263, 1826273038, 684382068, 604708621, 1037329879], [76096657, 1141449819, 1674125271, 1674108509, 1141246947], [0, 1]],
    [[1826319801, 1826319856, 1826321016, 1826337098, 761148722, 1514073, 1075699382, 364128155, 601731191, 1599074395, 1030806270, 411170707, 814415950, 1079565900, 1266802123, 1829993091, 578518825, 1789804165, 1815341862], [1, 43, 532677522, 228302769, 1065485979, 1066441869, 1072696993, 1107237689, 205973053, 886163135, 2078955597, 1330788956, 1896933836, 1334742657, 1343771574, 1403634087, 207010121], [532676609, 304386665, 760967247, 9168, 93972, 762026, 5088018, 28740426, 368306962, 901121555, 1183402832, 1162561939, 396729237, 77737067, 860088793], [1293643192, 2054609797, 152193778, 1369746155, 1065417279, 1065868894, 1829741279, 1236763239, 473582611, 622727583, 1933027831, 1724674968, 1904711600], [152193317, 304386648, 1978513418, 4100, 304428159, 1217880336, 915374149, 1534372651, 516848391, 559514874, 2018116814], [1369739850, 760966592, 228290155, 1750225597, 1369764885, 152396333, 229650054, 2062326681, 1711846400], [684869925, 608773271, 913159992, 1217547817, 2054623207, 1826431878, 1066126165], [228289975, 1293643193, 760966617, 760967088, 1293648904], [0, 0, 1]],
    [[1521933206, 1521934897, 1521970564, 1522465623, 462198075, 46842609, 1386666137, 341756297, 1408650230, 939493143, 1078638402, 72193029, 1848429657, 1373173190, 298145654, 56578324, 460377260, 1351904612, 1525174107], [30, 1290, 532704059, 2054995176, 1069368148, 1098438556, 1289831599, 223187342, 2118961706, 2079812616, 605624936, 894285712, 540445196, 272547521, 1019652883, 815916328, 707435788], [532676630, 608774188, 456599307, 268782, 2773527, 22666194, 152640540, 870051078, 2071550237, 1968764910, 760240039, 833426517, 422212090, 335545672, 121883163], [989256573, 1445837129, 1369752783, 1674304959, 1067186839, 1080291874, 1622298970, 875267324, 1963503995, 1281013069, 590761085, 961649143, 153908669], [1369739859, 608773651, 760974587, 110700, 609915298, 313739747, 1889512068, 1274500293, 1628100203, 1872831634, 251600805], [1674126488, 456580158, 2054614176, 837125239, 1674778616, 1375186041, 2092101543, 1663916222, 1242541948], [1902416460, 1217546621, 1826321766, 304415858, 1446159863, 1524764047, 1085699794], [2054609775, 989256578, 456580497, 456589488, 989377235], [], [1]]
  ]
private theorem cell_53_9 : (CJ0.blockMatrix source 53 ((9 : ℤ)-24)).rank ≤ 96 :=
  Fast.cell (z := matrix_53_9) (Fast.bands [(29, 29, 1), (30, 30, 2), (31, 31, 3), (32, 32, 4), (33, 33, 5), (34, 34, 6), (35, 35, 7), (36, 36, 8), (37, 37, 9), (38, 38, 10), (39, 40, 10), (40, 42, 9), (41, 44, 8), (42, 46, 7), (43, 48, 6), (44, 50, 4), (45, 52, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_53 (u : ℕ) : ℕ :=
  match u with
  | 9 => 96
  | u => nominal 53 u

private theorem bound_53 (u : ℕ) :
    (CJ0.blockMatrix source 53 ((u : ℤ)-24)).rank ≤ allowance_53 u := by
  unfold allowance_53
  split
  · exact cell_53_9
  · exact (block_rank_le 53 _).trans (rank_le_nominal 53 _)

theorem grade_53 : (∑ u ∈ Finset.range (81-53), (CJ0.blockMatrix source 53 ((u : ℤ)-24)).rank) ≤ 1193 := by
  refine (Finset.sum_le_sum fun u _ => bound_53 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_53)]
  decide +kernel

private def matrix_54_9 : CJ1.Block where
  bank := .leftLow
  cap := 89
  free := [(8, 1)]
  vectors := [
    [[728925885, 1569994215, 168213693, 336427731, 953215067, 336463404, 168460161, 1571402758, 735792538, 28992535, 1172625596, 351073242, 2089316839, 547352272, 985800865, 682570890, 523466187, 1299770877], [728925885, 841068330, 1457851796, 1009282368, 2074639132, 392530705, 1906635889, 1795473302, 1071025669, 1088673299, 83952297, 267120945, 1822195894, 855862811, 129938054, 552632836], [728925885, 112142445, 1345709351, 1794279450, 280359682, 112171023, 1794464866, 1008436, 1070017233, 18656066, 65296231, 201824714, 1620371180, 1366198064], [728925885, 1513922993, 1962492791, 1962493092, 448573023, 1794304433, 160433, 848003, 1069169230, 1080193269, 1115809395, 1216721752], [728925885, 784997108, 1177495683, 784997409, 1794282047, 22386, 138047, 709956, 1068459274, 11733995], [728925885, 56071223, 1121424460, 1794279382, 2665, 19721, 118326, 591630], [728925885, 1457851771, 1794279122, 260, 2405, 17316], [728925885, 728925886, 1065353236, 1065353457], [728925885, 1]]
  ]
private theorem cell_54_9 : (CJ0.blockMatrix source 54 ((9 : ℤ)-24)).rank ≤ 89 :=
  Fast.cell (z := matrix_54_9) (Fast.bands [(30, 30, 1), (31, 31, 2), (32, 32, 3), (33, 33, 4), (34, 34, 5), (35, 35, 6), (36, 36, 7), (37, 37, 8), (38, 38, 9), (39, 39, 10), (40, 41, 10), (41, 43, 9), (42, 45, 8), (43, 47, 7), (44, 49, 6), (45, 51, 4), (46, 53, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_54 (u : ℕ) : ℕ :=
  match u with
  | 9 => 89
  | u => nominal 54 u

private theorem bound_54 (u : ℕ) :
    (CJ0.blockMatrix source 54 ((u : ℤ)-24)).rank ≤ allowance_54 u := by
  unfold allowance_54
  split
  · exact cell_54_9
  · exact (block_rank_le 54 _).trans (rank_le_nominal 54 _)

theorem grade_54 : (∑ u ∈ Finset.range (81-54), (CJ0.blockMatrix source 54 ((u : ℤ)-24)).rank) ≤ 1096 := by
  refine (Finset.sum_le_sum fun u _ => bound_54 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_54)]
  decide +kernel

private def matrix_55_8 : CJ1.Block where
  bank := .leftLow
  cap := 88
  free := [(8, 0), (8, 1)]
  vectors := [
    [[2130706395, 2130704686, 532637100, 532090712, 1058945359, 1010245642, 1210049328, 1430185781, 1095786603, 1486993315, 1877737313, 1004952231, 115847596, 1061998579, 53943173, 1230959834, 1585044310, 599083250], [266338271, 1065351722, 1065320029, 1064869684, 793816938, 2086752908, 228356804, 357701408, 457215500, 822071928, 1160206765, 1920682393, 170691369, 169587081, 1582963049, 1880027303], [532676580, 1598028573, 2130679109, 2130314789, 528532064, 1563515133, 1895314199, 779906411, 1340333058, 1872421880, 1263056121, 758291963, 1287259881, 547159462], [799014889, 1598028806, 266316401, 1065043638, 2127473091, 1038764532, 353593272, 1116082303, 1197505560, 2092344525, 1859261060, 572559996], [1065353198, 1065352421, 532659698, 532439905, 2128255453, 2110715735, 931833785, 315767867, 1723473149, 944564125], [1331691507, 2130705851, 1598017494, 2130534028, 1596244941, 2116153934, 2033659392, 1587767582], [1598029816, 532676230, 2130698283, 2130590343, 1064129949, 1055231774], [1864368125, 532676424, 799010559, 2130639249], [1]],
    [[1, 46, 532677649, 532692047, 1065522094, 1066805563, 1608253365, 1658579619, 307766910, 1362649145, 521691818, 857893150, 790474075, 1394528014, 946123377, 938427940, 1407638379, 1815759785], [266338305, 1065353256, 1065354094, 1065366004, 799152378, 1162161, 540719855, 46834095, 1033003578, 2083243304, 1768411361, 1549393558, 173828969, 1949440167, 1575537103, 999297732], [532676609, 1598029858, 726, 10406, 532786699, 1598946144, 6244546, 35799478, 1774064934, 1285915273, 705015599, 951063784, 48827812, 1803290850], [799014913, 1598029852, 266338890, 1065361494, 86387, 1066062824, 537449490, 26998582, 1995278592, 19161344, 179849103, 1383905658], [1065353217, 1065353238, 532677065, 532682994, 66010, 537264, 1068933111, 1085399613, 1161463510, 1465344399], [1331691521, 16, 1598030163, 4715, 1598078461, 394953, 2622893, 14613261], [1598029825, 532676619, 230, 3250, 1065387179, 1065631956], [1864368129, 532676614, 799015044, 1976], [0, 1]]
  ]
private theorem cell_55_8 : (CJ0.blockMatrix source 55 ((8 : ℤ)-24)).rank ≤ 88 :=
  Fast.cell (z := matrix_55_8) (Fast.bands [(31, 31, 1), (32, 32, 2), (33, 33, 3), (34, 34, 4), (35, 35, 5), (36, 36, 6), (37, 37, 7), (38, 38, 8), (39, 39, 9), (40, 41, 9), (41, 43, 9), (42, 45, 8), (43, 47, 7), (44, 49, 6), (45, 51, 5), (46, 53, 3), (47, 55, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_55 (u : ℕ) : ℕ :=
  match u with
  | 8 => 88
  | u => nominal 55 u

private theorem bound_55 (u : ℕ) :
    (CJ0.blockMatrix source 55 ((u : ℤ)-24)).rank ≤ allowance_55 u := by
  unfold allowance_55
  split
  · exact cell_55_8
  · exact (block_rank_le 55 _).trans (rank_le_nominal 55 _)

theorem grade_55 : (∑ u ∈ Finset.range (81-55), (CJ0.blockMatrix source 55 ((u : ℤ)-24)).rank) ≤ 1002 := by
  refine (Finset.sum_le_sum fun u _ => bound_55 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_55)]
  decide +kernel

private def allowance_56 (u : ℕ) : ℕ :=
  nominal 56 u

private theorem bound_56 (u : ℕ) :
    (CJ0.blockMatrix source 56 ((u : ℤ)-24)).rank ≤ allowance_56 u := by
  unfold allowance_56
  exact (block_rank_le 56 _).trans (rank_le_nominal 56 _)

theorem grade_56 : (∑ u ∈ Finset.range (81-56), (CJ0.blockMatrix source 56 ((u : ℤ)-24)).rank) ≤ 914 := by
  refine (Finset.sum_le_sum fun u _ => bound_56 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_56)]
  decide +kernel

private def matrix_57_7 : CJ1.Block where
  bank := .leftLow
  cap := 79
  free := [(7, 2), (8, 0)]
  vectors := [
    [[1203986519, 262279221, 836795611, 756862915, 524558670, 354703430, 1121570293, 337302459, 929660190, 1290881156, 1199164929, 655959228, 2022540953, 356066804, 890167010, 597240934, 1052182897], [1203986519, 1188999135, 1778502909, 1109066439, 1546198664, 939211199, 182359094, 154943365, 774716825, 516164331, 683000598, 2103665063, 2049582323, 437190914, 755239706], [1203986519, 2115719049, 1793490293, 1446282579, 99916085, 839295114, 1473770413, 811879385, 2093543873, 553326891, 129673707, 1973991356, 567673507], [1203986519, 911732530, 881757763, 564524816, 1666097702, 1303903845, 169866568, 642012817, 1451531056, 1232502268, 838038185], [1203986519, 1838452444, 1174011752, 1521219497, 144878205, 1159025640, 1141547361, 1631171889, 1688786310], [1203986519, 634465925, 539545827, 981673670, 1293910968, 1995821105, 2015810310], [1203986519, 1561185839, 1109066421, 2003313682, 1418805821], [1203986519, 357199320, 1]],
    [[1378839333, 132388561, 2045777967, 1538705432, 264784646, 1051681025, 789810308, 477448982, 848896208, 2115655921, 1219726863, 339590194, 691952026, 1096672367, 1676327701, 532592925, 707637358], [1378839333, 884255661, 1161522306, 377183126, 2018307953, 1164079505, 1756437236, 851718179, 2127884462, 2118477892, 1231955404, 1238341223, 1584317236, 1643061564, 1469758598], [1378839333, 1636122761, 1656105978, 851783581, 1166524372, 2128261566, 1758882103, 1223542509, 904341953, 1214135939, 17819465, 1220521758, 1690334948], [1378839333, 257283428, 1398822550, 1583667464, 1713563341, 414698225, 1344183878, 2010065064, 1024983322, 189152617, 2086347012], [1378839333, 1009150528, 389672022, 1193995442, 519567899, 2025836759, 1449053552, 561011512, 331639877], [1378839333, 1761017628, 759360827, 434634615, 84933284, 1940903475, 469834262], [1378839333, 382178295, 377182532, 57452083, 2075757561], [1378839333, 1134045395], [1]]
  ]
private theorem cell_57_7 : (CJ0.blockMatrix source 57 ((7 : ℤ)-24)).rank ≤ 79 :=
  Fast.cell (z := matrix_57_7) (Fast.bands [(33, 33, 1), (34, 34, 2), (35, 35, 3), (36, 36, 4), (37, 37, 5), (38, 38, 6), (39, 39, 7), (40, 40, 8), (41, 42, 8), (42, 44, 8), (43, 46, 8), (44, 48, 7), (45, 50, 6), (46, 52, 5), (47, 54, 4), (48, 56, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_57 (u : ℕ) : ℕ :=
  match u with
  | 7 => 79
  | u => nominal 57 u

private theorem bound_57 (u : ℕ) :
    (CJ0.blockMatrix source 57 ((u : ℤ)-24)).rank ≤ allowance_57 u := by
  unfold allowance_57
  split
  · exact cell_57_7
  · exact (block_rank_le 57 _).trans (rank_le_nominal 57 _)

theorem grade_57 : (∑ u ∈ Finset.range (81-57), (CJ0.blockMatrix source 57 ((u : ℤ)-24)).rank) ≤ 828 := by
  refine (Finset.sum_le_sum fun u _ => bound_57 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_57)]
  decide +kernel

private def allowance_58 (u : ℕ) : ℕ :=
  nominal 58 u

private theorem bound_58 (u : ℕ) :
    (CJ0.blockMatrix source 58 ((u : ℤ)-24)).rank ≤ allowance_58 u := by
  unfold allowance_58
  exact (block_rank_le 58 _).trans (rank_le_nominal 58 _)

theorem grade_58 : (∑ u ∈ Finset.range (81-58), (CJ0.blockMatrix source 58 ((u : ℤ)-24)).rank) ≤ 749 := by
  refine (Finset.sum_le_sum fun u _ => bound_58 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_58)]
  decide +kernel

private def matrix_59_6 : CJ1.Block where
  bank := .leftLow
  cap := 70
  free := [(7, 0), (7, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2103728105, 1815959273], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4496388, 45402552], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2130048425, 2125113365], [0, 0, 0, 0, 0, 0, 0, 0, 82251, 565212], [0, 0, 0, 0, 0, 0, 2130697997, 2130662477], [0, 0, 0, 0, 666, 2340], [0, 0, 2130706397, 2130706369], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2108224493], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3838380], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2130130676], [0, 0, 0, 0, 0, 0, 0, 0, 0, 73815], [0, 0, 0, 0, 0, 0, 0, 2130698663], [0, 0, 0, 0, 0, 630], [0, 0, 0, 2130706398], [0, 1]]
  ]
private theorem cell_59_6 : (CJ0.blockMatrix source 59 ((6 : ℤ)-24)).rank ≤ 70 :=
  Fast.cell (z := matrix_59_6) (Fast.bands [(35, 35, 1), (36, 36, 2), (37, 37, 3), (38, 38, 4), (39, 39, 5), (40, 40, 6), (41, 41, 7), (42, 43, 7), (43, 45, 7), (44, 47, 7), (45, 49, 7), (46, 51, 6), (47, 53, 5), (48, 55, 4), (49, 57, 3), (50, 59, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_59 (u : ℕ) : ℕ :=
  match u with
  | 6 => 70
  | u => nominal 59 u

private theorem bound_59 (u : ℕ) :
    (CJ0.blockMatrix source 59 ((u : ℤ)-24)).rank ≤ allowance_59 u := by
  unfold allowance_59
  split
  · exact cell_59_6
  · exact (block_rank_le 59 _).trans (rank_le_nominal 59 _)

theorem grade_59 : (∑ u ∈ Finset.range (81-59), (CJ0.blockMatrix source 59 ((u : ℤ)-24)).rank) ≤ 672 := by
  refine (Finset.sum_le_sum fun u _ => bound_59 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_59)]
  decide +kernel

end Front6960ListBank

end Merged6967_R6960Front6960ListCells5

section Merged6967_R6960Front6960ListCells6
set_option Elab.async false


set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6960ListBank
open scoped BigOperators

private def matrix_60_6 : CJ1.Block where
  bank := .leftLow
  cap := 63
  free := [(7, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2103728105], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4496388], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2130048425], [0, 0, 0, 0, 0, 0, 0, 0, 82251], [0, 0, 0, 0, 0, 0, 2130697997], [0, 0, 0, 0, 666], [0, 0, 2130706397], [1]]
  ]
private theorem cell_60_6 : (CJ0.blockMatrix source 60 ((6 : ℤ)-24)).rank ≤ 63 :=
  Fast.cell (z := matrix_60_6) (Fast.bands [(36, 36, 1), (37, 37, 2), (38, 38, 3), (39, 39, 4), (40, 40, 5), (41, 41, 6), (42, 42, 7), (43, 44, 7), (44, 46, 7), (45, 48, 7), (46, 50, 7), (47, 52, 6), (48, 54, 5), (49, 56, 4), (50, 58, 3), (51, 60, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_60 (u : ℕ) : ℕ :=
  match u with
  | 6 => 63
  | u => nominal 60 u

private theorem bound_60 (u : ℕ) :
    (CJ0.blockMatrix source 60 ((u : ℤ)-24)).rank ≤ allowance_60 u := by
  unfold allowance_60
  split
  · exact cell_60_6
  · exact (block_rank_le 60 _).trans (rank_le_nominal 60 _)

theorem grade_60 : (∑ u ∈ Finset.range (81-60), (CJ0.blockMatrix source 60 ((u : ℤ)-24)).rank) ≤ 601 := by
  refine (Finset.sum_le_sum fun u _ => bound_60 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_60)]
  decide +kernel

private def matrix_61_5 : CJ1.Block where
  bank := .leftLow
  cap := 60
  free := [(6, 0), (6, 1), (6, 2), (7, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7059052, 73157448, 440646024], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129743835, 2122311683, 2086957793], [0, 0, 0, 0, 0, 0, 0, 0, 111930, 788840, 3458780], [0, 0, 0, 0, 0, 0, 2130695773, 2130649493, 2130504764], [0, 0, 0, 0, 780, 2808, 7530], [0, 0, 2130706394, 2130706362, 2130706305], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6096454, 62949432], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129855765, 2123313723], [0, 0, 0, 0, 0, 0, 0, 0, 0, 101270, 711360], [0, 0, 0, 0, 0, 0, 0, 2130696553, 2130653822], [0, 0, 0, 0, 0, 741, 2660], [0, 0, 0, 2130706395, 2130706364], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5245786], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129957035], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 91390], [0, 0, 0, 0, 0, 0, 0, 0, 2130697294], [0, 0, 0, 0, 0, 0, 703], [0, 0, 0, 0, 2130706396], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 161869968], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2108224493], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2632032], [0, 0, 0, 0, 0, 0, 0, 0, 2130459680], [0, 0, 0, 0, 0, 0, 16872], [0, 0, 0, 0, 2130705767], [], [1]]
  ]
private theorem cell_61_5 : (CJ0.blockMatrix source 61 ((5 : ℤ)-24)).rank ≤ 60 :=
  Fast.cell (z := matrix_61_5) (Fast.bands [(37, 37, 1), (38, 38, 2), (39, 39, 3), (40, 40, 4), (41, 41, 5), (42, 42, 6), (43, 44, 6), (44, 46, 6), (45, 48, 6), (46, 50, 6), (47, 52, 6), (48, 54, 5), (49, 56, 4), (50, 58, 3), (51, 60, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_61 (u : ℕ) : ℕ :=
  match u with
  | 5 => 60
  | u => nominal 61 u

private theorem bound_61 (u : ℕ) :
    (CJ0.blockMatrix source 61 ((u : ℤ)-24)).rank ≤ allowance_61 u := by
  unfold allowance_61
  split
  · exact cell_61_5
  · exact (block_rank_le 61 _).trans (rank_le_nominal 61 _)

theorem grade_61 : (∑ u ∈ Finset.range (81-61), (CJ0.blockMatrix source 61 ((u : ℤ)-24)).rank) ≤ 533 := by
  refine (Finset.sum_le_sum fun u _ => bound_61 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_61)]
  decide +kernel

private def matrix_62_5 : CJ1.Block where
  bank := .leftLow
  cap := 54
  free := [(6, 0), (6, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7059052, 73157448], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129743835, 2122311683], [0, 0, 0, 0, 0, 0, 0, 0, 111930, 788840], [0, 0, 0, 0, 0, 0, 2130695773, 2130649493], [0, 0, 0, 0, 780, 2808], [0, 0, 2130706394, 2130706362], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6096454], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129855765], [0, 0, 0, 0, 0, 0, 0, 0, 0, 101270], [0, 0, 0, 0, 0, 0, 0, 2130696553], [0, 0, 0, 0, 0, 741], [0, 0, 0, 2130706395], [0, 1]]
  ]
private theorem cell_62_5 : (CJ0.blockMatrix source 62 ((5 : ℤ)-24)).rank ≤ 54 :=
  Fast.cell (z := matrix_62_5) (Fast.bands [(38, 38, 1), (39, 39, 2), (40, 40, 3), (41, 41, 4), (42, 42, 5), (43, 43, 6), (44, 45, 6), (45, 47, 6), (46, 49, 6), (47, 51, 6), (48, 53, 6), (49, 55, 5), (50, 57, 4), (51, 59, 3), (52, 61, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_62 (u : ℕ) : ℕ :=
  match u with
  | 5 => 54
  | u => nominal 62 u

private theorem bound_62 (u : ℕ) :
    (CJ0.blockMatrix source 62 ((u : ℤ)-24)).rank ≤ allowance_62 u := by
  unfold allowance_62
  split
  · exact cell_62_5
  · exact (block_rank_le 62 _).trans (rank_le_nominal 62 _)

theorem grade_62 : (∑ u ∈ Finset.range (81-62), (CJ0.blockMatrix source 62 ((u : ℤ)-24)).rank) ≤ 471 := by
  refine (Finset.sum_le_sum fun u _ => bound_62 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_62)]
  decide +kernel

private def matrix_63_4 : CJ1.Block where
  bank := .rightLow
  cap := 50
  free := [(4, 2), (6, 2), (8, 2), (10, 2), (12, 2)]
  vectors := [
    [[1], [2130706429], [0, 6], [0, 2130706429], [0, 0, 1]],
    [[1], [2130706430], [1, 3], [2130706429, 2130706432], [0, 6], [0, 2130706429], [0, 0, 1]],
    [[1], [2130706431], [2, 1], [2130706427], [1, 6], [2130706429, 2130706431], [0, 6], [0, 2130706429], [0, 0, 1]],
    [[1], [2130706432], [3], [2130706427], [3, 3], [2130706424], [1, 9], [2130706429, 2130706430], [0, 6], [0, 2130706429], [0, 0, 1]],
    [[1], [], [4], [2130706429], [6], [2130706421], [4, 6], [2130706421], [1, 12], [2130706429, 2130706429], [0, 6], [0, 2130706429], [0, 0, 1]]
  ]
private theorem cell_63_4 : (CJ0.blockMatrix source 63 ((4 : ℤ)-24)).rank ≤ 50 :=
  Fast.cell (z := matrix_63_4) (Fast.bands [(0, 50, 14), (1, 51, 12), (2, 52, 10), (3, 53, 8), (4, 54, 6), (5, 55, 4), (6, 56, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_63_5 : CJ1.Block where
  bank := .leftLow
  cap := 48
  free := [(6, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7059052], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129743835], [0, 0, 0, 0, 0, 0, 0, 0, 111930], [0, 0, 0, 0, 0, 0, 2130695773], [0, 0, 0, 0, 780], [0, 0, 2130706394], [1]]
  ]
private theorem cell_63_5 : (CJ0.blockMatrix source 63 ((5 : ℤ)-24)).rank ≤ 48 :=
  Fast.cell (z := matrix_63_5) (Fast.bands [(39, 39, 1), (40, 40, 2), (41, 41, 3), (42, 42, 4), (43, 43, 5), (44, 44, 6), (45, 46, 6), (46, 48, 6), (47, 50, 6), (48, 52, 6), (49, 54, 6), (50, 56, 5), (51, 58, 4), (52, 60, 3), (53, 62, 2)]) (by decide +kernel) (by decide +kernel)

private def allowance_63 (u : ℕ) : ℕ :=
  match u with
  | 4 => 50
  | 5 => 48
  | u => nominal 63 u

private theorem bound_63 (u : ℕ) :
    (CJ0.blockMatrix source 63 ((u : ℤ)-24)).rank ≤ allowance_63 u := by
  unfold allowance_63
  split
  · exact cell_63_4
  · exact cell_63_5
  · exact (block_rank_le 63 _).trans (rank_le_nominal 63 _)

theorem grade_63 : (∑ u ∈ Finset.range (81-63), (CJ0.blockMatrix source 63 ((u : ℤ)-24)).rank) ≤ 411 := by
  refine (Finset.sum_le_sum fun u _ => bound_63 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_63)]
  decide +kernel

private def matrix_64_4 : CJ1.Block where
  bank := .leftLow
  cap := 45
  free := [(5, 0), (5, 1), (5, 2), (6, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129335679, 2118488843, 2065545953], [0, 0, 0, 0, 0, 0, 0, 0, 148995, 1072764, 4812990], [0, 0, 0, 0, 0, 0, 2130693189, 2130634193, 2130444647], [0, 0, 0, 0, 903, 3318, 9105], [0, 0, 2130706391, 2130706355, 2130706289], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129484674, 2119846353], [0, 0, 0, 0, 0, 0, 0, 0, 0, 135751, 974939], [0, 0, 0, 0, 0, 0, 0, 2130694092, 2130639275], [0, 0, 0, 0, 0, 861, 3157], [0, 0, 0, 2130706392, 2130706357], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129620425], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 123410], [0, 0, 0, 0, 0, 0, 0, 0, 2130694953], [0, 0, 0, 0, 0, 0, 820], [0, 0, 0, 0, 2130706393], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2095411173], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3850392], [0, 0, 0, 0, 0, 0, 0, 0, 2130370643], [0, 0, 0, 0, 0, 0, 21320], [0, 0, 0, 0, 2130705653], [], [1]]
  ]
private theorem cell_64_4 : (CJ0.blockMatrix source 64 ((4 : ℤ)-24)).rank ≤ 45 :=
  Fast.cell (z := matrix_64_4) (Fast.bands [(40, 40, 1), (41, 41, 2), (42, 42, 3), (43, 43, 4), (44, 44, 5), (45, 46, 5), (46, 48, 5), (47, 50, 5), (48, 52, 5), (49, 54, 5), (50, 56, 5), (51, 58, 4), (52, 60, 3), (53, 62, 2), (54, 64, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_64 (u : ℕ) : ℕ :=
  match u with
  | 4 => 45
  | u => nominal 64 u

private theorem bound_64 (u : ℕ) :
    (CJ0.blockMatrix source 64 ((u : ℤ)-24)).rank ≤ allowance_64 u := by
  unfold allowance_64
  split
  · exact cell_64_4
  · exact (block_rank_le 64 _).trans (rank_le_nominal 64 _)

theorem grade_64 : (∑ u ∈ Finset.range (81-64), (CJ0.blockMatrix source 64 ((u : ℤ)-24)).rank) ≤ 358 := by
  refine (Finset.sum_le_sum fun u _ => bound_64 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_64)]
  decide +kernel

private def matrix_65_3 : CJ1.Block where
  bank := .rightLow
  cap := 40
  free := [(4, 1), (6, 1), (8, 1), (10, 1)]
  vectors := [
    [[], [2130706432], [3], [0, 2130706430], [0, 1]],
    [[], [2130706432], [2], [2130706432, 2130706432], [3], [0, 2130706430], [0, 1]],
    [[], [2130706432], [1], [2130706431], [4], [2130706432, 2130706431], [3], [0, 2130706430], [0, 1]],
    [[], [2130706432], [], [2130706430], [3], [2130706430], [6], [2130706432, 2130706430], [3], [0, 2130706430], [0, 1]]
  ]
private theorem cell_65_3 : (CJ0.blockMatrix source 65 ((3 : ℤ)-24)).rank ≤ 40 :=
  Fast.cell (z := matrix_65_3) (Fast.bands [(0, 53, 13), (1, 54, 11), (2, 55, 9), (3, 56, 7), (4, 57, 5), (5, 58, 3), (6, 59, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_65_4 : CJ1.Block where
  bank := .leftLow
  cap := 40
  free := [(5, 0), (5, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129335679, 2118488843], [0, 0, 0, 0, 0, 0, 0, 0, 148995, 1072764], [0, 0, 0, 0, 0, 0, 2130693189, 2130634193], [0, 0, 0, 0, 903, 3318], [0, 0, 2130706391, 2130706355], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129484674], [0, 0, 0, 0, 0, 0, 0, 0, 0, 135751], [0, 0, 0, 0, 0, 0, 0, 2130694092], [0, 0, 0, 0, 0, 861], [0, 0, 0, 2130706392], [0, 1]]
  ]
private theorem cell_65_4 : (CJ0.blockMatrix source 65 ((4 : ℤ)-24)).rank ≤ 40 :=
  Fast.cell (z := matrix_65_4) (Fast.bands [(41, 41, 1), (42, 42, 2), (43, 43, 3), (44, 44, 4), (45, 45, 5), (46, 47, 5), (47, 49, 5), (48, 51, 5), (49, 53, 5), (50, 55, 5), (51, 57, 5), (52, 59, 4), (53, 61, 3), (54, 63, 2), (55, 65, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_65 (u : ℕ) : ℕ :=
  match u with
  | 3 => 40
  | 4 => 40
  | u => nominal 65 u

private theorem bound_65 (u : ℕ) :
    (CJ0.blockMatrix source 65 ((u : ℤ)-24)).rank ≤ allowance_65 u := by
  unfold allowance_65
  split
  · exact cell_65_3
  · exact cell_65_4
  · exact (block_rank_le 65 _).trans (rank_le_nominal 65 _)

theorem grade_65 : (∑ u ∈ Finset.range (81-65), (CJ0.blockMatrix source 65 ((u : ℤ)-24)).rank) ≤ 307 := by
  refine (Finset.sum_le_sum fun u _ => bound_65 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_65)]
  decide +kernel

private def matrix_66_3 : CJ1.Block where
  bank := .leftLow
  cap := 36
  free := [(4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 194580, 1426920, 6527400, 23839200], [0, 0, 0, 0, 0, 0, 2130690218, 2130616388, 2130373793, 2129684753], [0, 0, 0, 0, 1035, 3870, 10825, 26840], [0, 0, 2130706388, 2130706348, 2130706273, 2130706133], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 178365, 1305480, 5959800], [0, 0, 0, 0, 0, 0, 0, 2130691253, 2130622283, 2130396145], [0, 0, 0, 0, 0, 990, 3696, 10321], [0, 0, 0, 2130706389, 2130706350, 2130706277], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 163185, 1191960], [0, 0, 0, 0, 0, 0, 0, 0, 2130692243, 2130627915], [0, 0, 0, 0, 0, 0, 946, 3526], [0, 0, 0, 0, 2130706390, 2130706352], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 148995], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2130693189], [0, 0, 0, 0, 0, 0, 0, 903], [0, 0, 0, 0, 0, 2130706391], [0, 0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5483016, 49466340], [0, 0, 0, 0, 0, 0, 0, 0, 2130259448, 2127448409], [0, 0, 0, 0, 0, 0, 26488, 146286], [0, 0, 0, 0, 2130705530, 2130703073], [], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4887036], [0, 0, 0, 0, 0, 0, 0, 0, 0, 2130299180], [0, 0, 0, 0, 0, 0, 0, 24682], [0, 0, 0, 0, 0, 2130705572], [], [0, 1]]
  ]
private theorem cell_66_3 : (CJ0.blockMatrix source 66 ((3 : ℤ)-24)).rank ≤ 36 :=
  Fast.cell (z := matrix_66_3) (Fast.bands [(42, 42, 1), (43, 43, 2), (44, 44, 3), (45, 45, 4), (46, 47, 4), (47, 49, 4), (48, 51, 4), (49, 53, 4), (50, 55, 4), (51, 57, 4), (52, 59, 4), (53, 61, 3), (54, 63, 2), (55, 65, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_66_4 : CJ1.Block where
  bank := .leftLow
  cap := 35
  free := [(5, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2129335679], [0, 0, 0, 0, 0, 0, 0, 0, 148995], [0, 0, 0, 0, 0, 0, 2130693189], [0, 0, 0, 0, 903], [0, 0, 2130706391], [1]]
  ]
private theorem cell_66_4 : (CJ0.blockMatrix source 66 ((4 : ℤ)-24)).rank ≤ 35 :=
  Fast.cell (z := matrix_66_4) (Fast.bands [(42, 42, 1), (43, 43, 2), (44, 44, 3), (45, 45, 4), (46, 46, 5), (47, 48, 5), (48, 50, 5), (49, 52, 5), (50, 54, 5), (51, 56, 5), (52, 58, 5), (53, 60, 4), (54, 62, 3), (55, 64, 2), (56, 66, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_66 (u : ℕ) : ℕ :=
  match u with
  | 3 => 36
  | 4 => 35
  | u => nominal 66 u

private theorem bound_66 (u : ℕ) :
    (CJ0.blockMatrix source 66 ((u : ℤ)-24)).rank ≤ allowance_66 u := by
  unfold allowance_66
  split
  · exact cell_66_3
  · exact cell_66_4
  · exact (block_rank_le 66 _).trans (rank_le_nominal 66 _)

theorem grade_66 : (∑ u ∈ Finset.range (81-66), (CJ0.blockMatrix source 66 ((u : ℤ)-24)).rank) ≤ 262 := by
  refine (Finset.sum_le_sum fun u _ => bound_66 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_66)]
  decide +kernel

private def matrix_67_2 : CJ1.Block where
  bank := .rightLow
  cap := 30
  free := [(4, 1), (6, 1), (8, 1)]
  vectors := [
    [[], [], [1], [2130706431], [0, 1]],
    [[], [], [1], [2130706432], [1], [2130706431], [0, 1]],
    [[], [], [1], [], [2], [2130706431], [1], [2130706431], [0, 1]]
  ]
private theorem cell_67_2 : (CJ0.blockMatrix source 67 ((2 : ℤ)-24)).rank ≤ 30 :=
  Fast.cell (z := matrix_67_2) (Fast.bands [(0, 56, 12), (1, 57, 10), (2, 58, 8), (3, 59, 6), (4, 60, 4), (5, 61, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_67_3 : CJ1.Block where
  bank := .leftLow
  cap := 32
  free := [(4, 0), (4, 1), (4, 2), (5, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 194580, 1426920, 6527400], [0, 0, 0, 0, 0, 0, 2130690218, 2130616388, 2130373793], [0, 0, 0, 0, 1035, 3870, 10825], [0, 0, 2130706388, 2130706348, 2130706273], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 178365, 1305480], [0, 0, 0, 0, 0, 0, 0, 2130691253, 2130622283], [0, 0, 0, 0, 0, 990, 3696], [0, 0, 0, 2130706389, 2130706350], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 163185], [0, 0, 0, 0, 0, 0, 0, 0, 2130692243], [0, 0, 0, 0, 0, 0, 946], [0, 0, 0, 0, 2130706390], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5483016], [0, 0, 0, 0, 0, 0, 0, 0, 2130259448], [0, 0, 0, 0, 0, 0, 26488], [0, 0, 0, 0, 2130705530], [], [1]]
  ]
private theorem cell_67_3 : (CJ0.blockMatrix source 67 ((3 : ℤ)-24)).rank ≤ 32 :=
  Fast.cell (z := matrix_67_3) (Fast.bands [(43, 43, 1), (44, 44, 2), (45, 45, 3), (46, 46, 4), (47, 48, 4), (48, 50, 4), (49, 52, 4), (50, 54, 4), (51, 56, 4), (52, 58, 4), (53, 60, 4), (54, 62, 3), (55, 64, 2), (56, 66, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_67 (u : ℕ) : ℕ :=
  match u with
  | 2 => 30
  | 3 => 32
  | u => nominal 67 u

private theorem bound_67 (u : ℕ) :
    (CJ0.blockMatrix source 67 ((u : ℤ)-24)).rank ≤ allowance_67 u := by
  unfold allowance_67
  split
  · exact cell_67_2
  · exact cell_67_3
  · exact (block_rank_le 67 _).trans (rank_le_nominal 67 _)

theorem grade_67 : (∑ u ∈ Finset.range (81-67), (CJ0.blockMatrix source 67 ((u : ℤ)-24)).rank) ≤ 220 := by
  refine (Finset.sum_le_sum fun u _ => bound_67 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_67)]
  decide +kernel

private def matrix_68_2 : CJ1.Block where
  bank := .rightLow
  cap := 27
  free := [(3, 0), (4, 1), (5, 0), (6, 1), (8, 1), (10, 1)]
  vectors := [
    [[], [], [2130706432], [1]],
    [[], [], [2130706432], [], [0, 1]],
    [[], [], [2130706432], [], [2130706432], [1]],
    [[], [], [2130706431], [], [2130706432], [], [0, 1]],
    [[], [], [2130706432], [], [], [], [1], [2130706431], [0, 1]],
    [[], [], [], [], [1], [], [2], [2130706431], [1], [2130706431], [0, 1]]
  ]
private theorem cell_68_2 : (CJ0.blockMatrix source 68 ((2 : ℤ)-24)).rank ≤ 27 :=
  Fast.cell (z := matrix_68_2) (Fast.bands [(0, 58, 11), (1, 59, 9), (2, 60, 7), (3, 61, 5), (4, 62, 3), (5, 63, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_68_3 : CJ1.Block where
  bank := .leftLow
  cap := 28
  free := [(4, 0), (4, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 194580, 1426920], [0, 0, 0, 0, 0, 0, 2130690218, 2130616388], [0, 0, 0, 0, 1035, 3870], [0, 0, 2130706388, 2130706348], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 178365], [0, 0, 0, 0, 0, 0, 0, 2130691253], [0, 0, 0, 0, 0, 990], [0, 0, 0, 2130706389], [0, 1]]
  ]
private theorem cell_68_3 : (CJ0.blockMatrix source 68 ((3 : ℤ)-24)).rank ≤ 28 :=
  Fast.cell (z := matrix_68_3) (Fast.bands [(44, 44, 1), (45, 45, 2), (46, 46, 3), (47, 47, 4), (48, 49, 4), (49, 51, 4), (50, 53, 4), (51, 55, 4), (52, 57, 4), (53, 59, 4), (54, 61, 4), (55, 63, 3), (56, 65, 2), (57, 67, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_68 (u : ℕ) : ℕ :=
  match u with
  | 2 => 27
  | 3 => 28
  | u => nominal 68 u

private theorem bound_68 (u : ℕ) :
    (CJ0.blockMatrix source 68 ((u : ℤ)-24)).rank ≤ allowance_68 u := by
  unfold allowance_68
  split
  · exact cell_68_2
  · exact cell_68_3
  · exact (block_rank_le 68 _).trans (rank_le_nominal 68 _)

theorem grade_68 : (∑ u ∈ Finset.range (81-68), (CJ0.blockMatrix source 68 ((u : ℤ)-24)).rank) ≤ 183 := by
  refine (Finset.sum_le_sum fun u _ => bound_68 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_68)]
  decide +kernel

private def matrix_69_1 : CJ1.Block where
  bank := .rightLow
  cap := 20
  free := [(4, 0), (6, 0)]
  vectors := [
    [[], [], [], [2130706432], [1]],
    [[], [], [], [2130706432], [], [2130706432], [1]]
  ]
private theorem cell_69_1 : (CJ0.blockMatrix source 69 ((1 : ℤ)-24)).rank ≤ 20 :=
  Fast.cell (z := matrix_69_1) (Fast.bands [(0, 59, 11), (1, 60, 9), (2, 61, 7), (3, 62, 5), (4, 63, 3), (5, 64, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_69_2 : CJ1.Block where
  bank := .leftLow
  cap := 24
  free := [(3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 2130686833, 2130595889, 2130291329, 2129409233], [0, 0, 0, 0, 1176, 4464, 12690, 32016], [0, 0, 2130706385, 2130706341, 2130706257, 2130706097], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 2130688009, 2130602657, 2130317273], [0, 0, 0, 0, 0, 1128, 4277, 12144], [0, 0, 0, 2130706386, 2130706343, 2130706261], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2130689137, 2130609143], [0, 0, 0, 0, 0, 0, 1081, 4094], [0, 0, 0, 0, 2130706387, 2130706345], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 2130690218], [0, 0, 0, 0, 0, 0, 0, 1035], [0, 0, 0, 0, 0, 2130706388], [0, 0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2130122693, 2126377028], [0, 0, 0, 0, 0, 0, 32430, 182160], [0, 0, 0, 0, 2130705398, 2130702518], [], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 2130171338], [0, 0, 0, 0, 0, 0, 0, 30360], [0, 0, 0, 0, 0, 2130705443], [], [0, 1]]
  ]
private theorem cell_69_2 : (CJ0.blockMatrix source 69 ((2 : ℤ)-24)).rank ≤ 24 :=
  Fast.cell (z := matrix_69_2) (Fast.bands [(45, 45, 1), (46, 46, 2), (47, 47, 3), (48, 49, 3), (49, 51, 3), (50, 53, 3), (51, 55, 3), (52, 57, 3), (53, 59, 3), (54, 61, 3), (55, 63, 3), (56, 65, 2), (57, 67, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_69_3 : CJ1.Block where
  bank := .leftLow
  cap := 24
  free := [(4, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 194580], [0, 0, 0, 0, 0, 0, 2130690218], [0, 0, 0, 0, 1035], [0, 0, 2130706388], [1]]
  ]
private theorem cell_69_3 : (CJ0.blockMatrix source 69 ((3 : ℤ)-24)).rank ≤ 24 :=
  Fast.cell (z := matrix_69_3) (Fast.bands [(45, 45, 1), (46, 46, 2), (47, 47, 3), (48, 48, 4), (49, 50, 4), (50, 52, 4), (51, 54, 4), (52, 56, 4), (53, 58, 4), (54, 60, 4), (55, 62, 4), (56, 64, 3), (57, 66, 2), (58, 68, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_69 (u : ℕ) : ℕ :=
  match u with
  | 1 => 20
  | 2 => 24
  | 3 => 24
  | u => nominal 69 u

private theorem bound_69 (u : ℕ) :
    (CJ0.blockMatrix source 69 ((u : ℤ)-24)).rank ≤ allowance_69 u := by
  unfold allowance_69
  split
  · exact cell_69_1
  · exact cell_69_2
  · exact cell_69_3
  · exact (block_rank_le 69 _).trans (rank_le_nominal 69 _)

theorem grade_69 : (∑ u ∈ Finset.range (81-69), (CJ0.blockMatrix source 69 ((u : ℤ)-24)).rank) ≤ 149 := by
  refine (Finset.sum_le_sum fun u _ => bound_69 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_69)]
  decide +kernel

end Front6960ListBank

end Merged6967_R6960Front6960ListCells6

section Merged6967_R6960QuadraticProjection
set_option Elab.async false





set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RetainedShortening
open K1 Polynomial
open scoped Polynomial
structure Word (A d : ℕ) (w : I → K) (s : K → (Polynomial K)) (T : Finset K) : Prop where
  distinct : Set.InjOn s (T : Set K)
  degree : ∀ z ∈ T, (s z).natDegree ≤ d
  hits : ∀ z ∈ T, ∃ B : Finset I, A ≤ B.card ∧ ∀ i ∈ B, (s z).eval (node i) = w i
end RetainedShortening
namespace CurvatureVotes
noncomputable section
open K1 Finset Polynomial RetainedShortening
open scoped BigOperators
def VoteScale (A d k : ℕ) : Prop :=
  262144≤k*(A-d) ∨ (k=5 ∧ 4*262144≤25*(A-d))
private theorem side_product {h m L n : ℕ} (total : h+m=n) (room : 2*L≤n) (hit : h≤L) :
    h*m≤L*(n-L) := by
  obtain ⟨x,hx⟩ := Nat.exists_eq_add_of_le hit
  obtain ⟨y,hy⟩ := Nat.exists_eq_add_of_le (by omega : L≤m)
  have hn : n-L=h+y := by omega
  rw [hn,hy,hx]
  nlinarith [Nat.zero_le (x*y)]
theorem minority_count {A d w s T} (W : Word A d w s T) {L k : ℕ}
    (hd : d<A) (scale : VoteScale A d k)
    (minor : ∀ i : I,
      (T.filter fun z => (s z).eval (node i)=w i).card≤L ∨
      (T.filter fun z => (s z).eval (node i)≠w i).card≤L) :
    T.card≤k*L+1 := by
  classical
  let H (z : K) (i : I) := (s z).eval (node i)=w i
  let hits (z : K) := univ.filter (H z)
  have many (z) (hz : z∈T) : A≤(hits z).card := by
    obtain ⟨B,hB,hw⟩ := W.hits z hz
    exact hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _,hw i hi⟩)
  have pair (z) (hz : z∈T) (y) (hy : y∈T) (ne : z≠y) :
      A-d ≤ (hits z \ hits y).card := by
    have nd : s z-s y ≠ 0 := sub_ne_zero.mpr fun h => ne (W.distinct hz hy h)
    have same := FrobeniusLocator.Strata.root_nodes_card_le node
      ProximityPrize.Benchmark.IRSProfile.domain.injective (s z-s y) nd (hits z ∩ hits y) (by
        intro i hi
        have hz' : (s z).eval (node i)=w i := (mem_filter.mp (mem_inter.mp hi).1).2
        have hy' : (s y).eval (node i)=w i := (mem_filter.mp (mem_inter.mp hi).2).2
        simp [eval_sub,hz',hy'])
    have deg := (natDegree_sub_le _ _).trans (max_le (W.degree _ hz) (W.degree _ hy))
    have split := card_sdiff_add_card_inter (hits z) (hits y)
    have h := many z hz
    omega
  let count (z y : K) := ∑ i : I, (if H z i then 1 else 0)*(if H y i then 0 else 1 : ℕ)
  have cv (z y) : count z y = (hits z \ hits y).card := by
    have eq : hits z \ hits y = univ.filter fun i => H z i ∧ ¬ H y i := by
      ext i; simp [hits]
    rw [eq,card_filter]
    apply sum_congr rfl
    intro i _
    by_cases hz : H z i <;> by_cases hy : H y i <;> simp [hz,hy]
  have row (z) (hz : z∈T) : (T.card-1)*(A-d) ≤ ∑ y∈T,count z y := by
    calc
      _ = ∑ _y∈T.erase z, (A-d) := by simp [card_erase_of_mem hz]
      _ ≤ ∑ y∈T.erase z,count z y := sum_le_sum fun y hy => (pair z hz y
        (mem_of_mem_erase hy) (ne_of_mem_erase hy).symm).trans_eq (cv z y).symm
      _ ≤ _ := sum_le_sum_of_subset (erase_subset _ _)
  have upper (i : I) : (∑ z∈T, if H z i then 1 else 0) *
        (∑ y∈T, if H y i then 0 else 1 : ℕ) ≤ T.card*L := by
    have hc := card_le_card (filter_subset (fun z => H z i) T)
    have mc := card_le_card (filter_subset (fun z => ¬ H z i) T)
    rcases minor i with h|h
    · change (T.filter fun z => H z i).card≤L at h
      rw [card_filter] at h mc
      simp only [ite_not] at mc
      simpa only [Nat.mul_comm T.card] using Nat.mul_le_mul h mc
    · change (T.filter fun z => ¬H z i).card≤L at h
      rw [card_filter] at h hc
      simp only [ite_not] at h
      exact Nat.mul_le_mul hc h
  have full (C : ℕ) (hu : ∀ i : I, (∑ z∈T, if H z i then 1 else 0) *
        (∑ y∈T, if H y i then 0 else 1 : ℕ) ≤ C) :
        T.card*((T.card-1)*(A-d)) ≤ 262144*C := calc
    _ = ∑ _z∈T, (T.card-1)*(A-d) := by simp
    _ ≤ ∑ z∈T, ∑ y∈T, count z y := sum_le_sum row
    _ = ∑ i : I, (∑ z∈T, if H z i then 1 else 0) *
        (∑ y∈T, if H y i then 0 else 1 : ℕ) := by
      unfold count
      simp_rw [show ∀ z, (∑ y∈T, ∑ i : I, (if H z i then 1 else 0)*
          (if H y i then 0 else 1 : ℕ)) = _ from fun z => sum_comm]
      rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul_sum]
    _ ≤ ∑ _i : I, C := sum_le_sum fun i _ => hu i
    _ = _ := by simp
  rcases scale with scale | ⟨rfl,scale⟩
  ·
    by_cases empty : T.card=0
    · omega
    have h := (full _ upper).trans (Nat.mul_le_mul_right (T.card*L) scale)
    have rearranged : T.card*((T.card-1)*(A-d)) ≤ T.card*((k*L)*(A-d)) := by
      simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
    have step := Nat.le_of_mul_le_mul_left rearranged (by omega : 0<T.card)
    have last := Nat.le_of_mul_le_mul_right step (by omega : 0<A-d)
    omega
  · by_contra! bad
    have hr : 2*L≤T.card := by omega
    have hu (i : I) : (∑ z∈T, if H z i then 1 else 0) *
        (∑ y∈T, if H y i then 0 else 1 : ℕ) ≤ L*(T.card-L) := by
      let h := T.filter fun z => H z i
      let m := T.filter fun z => ¬H z i
      have eqn : h.card + m.card=T.card := by
        dsimp [h,m]; exact card_filter_add_card_filter_not ..
      have side : h.card*m.card≤L*(T.card-L) := by
        rcases minor i with hit|miss
        · exact side_product eqn hr hit
        · rw [Nat.mul_comm]
          exact side_product ((Nat.add_comm ..).trans eqn) hr miss
      simpa only [h,m,card_filter,ite_not] using side
    have counted := full _ hu
    let t := T.card-(5*L+2)
    have eqn : T.card=5*L+2+t := by dsimp [t]; omega
    have lt : 25*(L*(T.card-L)) < 4*(T.card*(T.card-1)) := by
      rw [show T.card-L=4*L+2+t by omega,show T.card-1=5*L+1+t by omega,eqn]
      nlinarith [Nat.zero_le (L*t),Nat.zero_le (t*t)]
    have left := Nat.mul_lt_mul_of_pos_right lt (by omega : 0<A-d)
    have right := Nat.mul_le_mul_right (L*(T.card-L)) scale
    nlinarith only [left,right,Nat.mul_le_mul_left 4 counted]
end
end CurvatureVotes
namespace ProximityPrize.SubmissionLower.MatrixRootMultiplicity
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem pow_card_dvd_det_of_eval_columns_eq_zero
    (M : Matrix ι ι (Polynomial K)) (alpha : K) (columns : Finset ι)
    (hzero : ∀ j ∈ columns, ∀ i, (M i j).eval alpha = 0) :
    (Polynomial.X - Polynomial.C alpha) ^ columns.card ∣ M.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro permutation _
  have hpart :
      (∏ j ∈ columns, (Polynomial.X - Polynomial.C alpha)) ∣
        ∏ j ∈ columns, M (permutation j) j := by
    apply Finset.prod_dvd_prod_of_dvd
    intro j hj
    exact Polynomial.dvd_iff_isRoot.mpr (hzero j hj (permutation j))
  have hfull :
      (∏ j ∈ columns, M (permutation j) j) ∣
        ∏ j : ι, M (permutation j) j :=
    Finset.prod_dvd_prod_of_subset columns Finset.univ
      (fun j => M (permutation j) j) (Finset.subset_univ columns)
  have hproduct :
      (Polynomial.X - Polynomial.C alpha) ^ columns.card ∣
        ∏ j : ι, M (permutation j) j := by
    simpa using hpart.trans hfull
  exact dvd_mul_of_dvd_right hproduct _
theorem pow_corank_dvd_det
    (M : Matrix ι ι (Polynomial K)) (alpha : K) :
    (Polynomial.X - Polynomial.C alpha) ^
        (Fintype.card ι - ((Polynomial.evalRingHom alpha).mapMatrix M).rank) ∣
      M.det := by
  classical
  let evalMatrix : Matrix ι ι (Polynomial K) →+* Matrix ι ι K :=
    (Polynomial.evalRingHom alpha).mapMatrix
  let constMatrix : Matrix ι ι K →+* Matrix ι ι (Polynomial K) :=
    (Polynomial.C : K →+* Polynomial K).mapMatrix
  let evaluated : Matrix ι ι K := evalMatrix M
  obtain ⟨V, U, e, hV, hU, hnormal⟩ := Matrix.exists_rank_normal_form evaluated
  let transformed : Matrix ι ι (Polynomial K) := constMatrix V * M * constMatrix U
  have heval_const (B : Matrix ι ι K) : evalMatrix (constMatrix B) = B := by
    ext i j
    simp [evalMatrix, constMatrix, RingHom.mapMatrix_apply, Matrix.map_apply]
  have heval : evalMatrix transformed =
      (Matrix.fromBlocks 1 0 0 0).submatrix e e := by
    change evalMatrix (constMatrix V * M * constMatrix U) = _
    rw [map_mul, map_mul, heval_const, heval_const]
    exact hnormal
  let zeroEmbedding : Fin (Fintype.card ι - evaluated.rank) ↪ ι := {
    toFun := fun j => e.symm (Sum.inr j)
    inj' := by
      intro i j hij
      exact Sum.inr.inj (e.symm.injective hij)
  }
  let zeroColumns : Finset ι := Finset.univ.map zeroEmbedding
  have hcard : zeroColumns.card = Fintype.card ι - evaluated.rank := by
    simp [zeroColumns]
  have hzero : ∀ j ∈ zeroColumns, ∀ i, (transformed i j).eval alpha = 0 := by
    intro j hj i
    obtain ⟨j0, _, rfl⟩ := Finset.mem_map.mp hj
    change evalMatrix transformed i (e.symm (Sum.inr j0)) = 0
    rw [heval]
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
    cases e i <;> rfl
  have hVdet : IsUnit (constMatrix V).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (hV.map constMatrix)
  have hUdet : IsUnit (constMatrix U).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (hU.map constMatrix)
  have hdiv := pow_card_dvd_det_of_eval_columns_eq_zero
    transformed alpha zeroColumns hzero
  rw [hcard] at hdiv
  change (Polynomial.X - Polynomial.C alpha) ^
      (Fintype.card ι - evaluated.rank) ∣
        (constMatrix V * M * constMatrix U).det at hdiv
  rw [Matrix.det_mul, Matrix.det_mul] at hdiv
  exact hVdet.dvd_mul_left.mp (hUdet.dvd_mul_right.mp hdiv)
theorem corank_le_rootMultiplicity_det
    (M : Matrix ι ι (Polynomial K)) (alpha : K) (hdet : M.det ≠ 0) :
    Fintype.card ι - ((Polynomial.evalRingHom alpha).mapMatrix M).rank ≤
      M.det.rootMultiplicity alpha := by
  exact (Polynomial.le_rootMultiplicity_iff hdet).mpr
    (pow_corank_dvd_det M alpha)
theorem sum_rootMultiplicity_le_natDegree
    (P : Polynomial K) (points : Finset K) :
    (∑ alpha ∈ points, P.rootMultiplicity alpha) ≤ P.natDegree := by
  classical
  have hselected :
      (∑ alpha ∈ points, Multiset.count alpha P.roots) ≤ P.roots.card := by
    let all := points ∪ P.roots.toFinset
    calc
      (∑ alpha ∈ points, Multiset.count alpha P.roots) ≤
          ∑ alpha ∈ all, Multiset.count alpha P.roots :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by simp)
      _ = ∑ alpha ∈ P.roots.toFinset, Multiset.count alpha P.roots := by
        symm
        apply Finset.sum_subset (Finset.subset_union_right)
        intro alpha _ hnot
        exact Multiset.count_eq_zero.mpr (by simpa using hnot)
      _ = P.roots.card := Multiset.toFinset_sum_count_eq P.roots
  calc
    (∑ alpha ∈ points, P.rootMultiplicity alpha) =
        ∑ alpha ∈ points, Multiset.count alpha P.roots := by
      apply Finset.sum_congr rfl
      intro alpha _
      exact (Polynomial.count_roots P).symm
    _ ≤ P.roots.card := hselected
    _ ≤ P.natDegree := Polynomial.card_roots' P
theorem sylvester_corank_le_rootMultiplicity_resultant
    (P Q : Polynomial (Polynomial K)) (m n : ℕ) (alpha : K)
    (hresultant : Polynomial.resultant P Q m n ≠ 0) :
    m + n - (Polynomial.sylvester
      (P.map (Polynomial.evalRingHom alpha))
      (Q.map (Polynomial.evalRingHom alpha)) m n).rank ≤
      (Polynomial.resultant P Q m n).rootMultiplicity alpha := by
  simpa only [Fintype.card_fin, Polynomial.resultant,
    ← Polynomial.sylvester_map_map] using
    corank_le_rootMultiplicity_det (Polynomial.sylvester P Q m n) alpha hresultant
theorem sum_sylvester_coranks_le_resultant_natDegree
    (P Q : Polynomial (Polynomial K)) (m n : ℕ) (points : Finset K)
    (hresultant : Polynomial.resultant P Q m n ≠ 0) :
    (∑ alpha ∈ points, (m + n - (Polynomial.sylvester
      (P.map (Polynomial.evalRingHom alpha))
      (Q.map (Polynomial.evalRingHom alpha)) m n).rank)) ≤
      (Polynomial.resultant P Q m n).natDegree := by
  calc
    _ ≤ ∑ alpha ∈ points, (Polynomial.resultant P Q m n).rootMultiplicity alpha :=
      Finset.sum_le_sum fun alpha _ =>
        sylvester_corank_le_rootMultiplicity_resultant P Q m n alpha hresultant
    _ ≤ (Polynomial.resultant P Q m n).natDegree :=
      sum_rootMultiplicity_le_natDegree (Polynomial.resultant P Q m n) points
end
end ProximityPrize.SubmissionLower.MatrixRootMultiplicity
noncomputable section
namespace CurvatureSquares
open Polynomial Finset
open scoped Polynomial BigOperators
open ProximityPrize.SubmissionLower.MatrixRootMultiplicity
def mulBox {L : Type} [Field L] (h : (Polynomial L)) (k n : ℕ)
    (fit : h≠0 → h.natDegree+k≤n) : degreeLT L k →ₗ[L] degreeLT L n where
  toFun u := ⟨h*(u:(Polynomial L)),by
    by_cases zero : h=0
    · simp [zero]
    by_cases uz : (u:(Polynomial L))=0
    · simp [uz]
    have hu := (natDegree_lt_iff_degree_lt uz).mpr (mem_degreeLT.mp u.2)
    apply mem_degreeLT.mpr
    apply (natDegree_lt_iff_degree_lt (mul_ne_zero zero uz)).mp
    rw [natDegree_mul zero uz]; have := fit zero; omega⟩
  map_add' a b := by ext1; exact mul_add ..
  map_smul' a b := by ext1; exact mul_smul_comm ..
theorem cofactor_corank {L : Type} [Field L] [DecidableEq L] (h t : (Polynomial L)) {r e : ℕ}
    (hr : 0<r) (dt : t.natDegree≤e) (fit : (h^2*t).natDegree≤r) :
    (r-e+1)/2 ≤ r+(r-1)-(sylvester (h^2*t) (h^2*t).derivative r (r-1)).rank := by
  classical
  let f:=h^2*t
  let g:=f.derivative
  by_cases zero : f=0
  · change _≤r+(r-1)-(sylvester f f.derivative r (r-1)).rank
    have hz : sylvester (0:(Polynomial L)) 0 r (r-1)=0 := by
      ext i j; cases j using Fin.addCases <;> simp [sylvester]
    rw [zero,derivative_zero,hz,Matrix.rank_zero]; omega
  have hn : h≠0 := fun h => zero (by simp [f,h])
  have tn : t≠0 := fun h => zero (by simp [f,h])
  let D:=h*t
  have dn : D≠0 := mul_ne_zero hn tn
  have df : f.natDegree=2*h.natDegree+t.natDegree := by
    rw [show f=h^2*t from rfl,natDegree_mul (pow_ne_zero _ hn) tn,natDegree_pow]
  have dD : D.natDegree=h.natDegree+t.natDegree := natDegree_mul hn tn
  let s:=D.natDegree
  let k:=r-s
  have ds : f.natDegree≤r := fit
  have gd : g.natDegree≤r-1 := (natDegree_derivative_le f).trans (Nat.sub_le_sub_right ds 1)
  have divides : h∣g := by
    refine ⟨2*h.derivative*t+h*t.derivative,?_⟩
    dsimp [f,g]; rw [derivative_mul,pow_two,derivative_mul]; ring
  obtain ⟨a,da⟩:=divides
  let S:=sylvesterMap f g ds gd
  let U:=mulBox D k r (fun _ => by dsimp [k,s]; omega)
  let V:=mulBox (-a) k (r-1) (fun ne => by
    have an : a≠0 := fun hz => ne (by simp [hz])
    have eq := natDegree_mul hn an
    rw [←da] at eq
    have gt : f.natDegree≠0 := by
      intro zz
      have zf : g=0 := by change f.derivative=0; conv_lhs => rw [eq_C_of_natDegree_eq_zero zz,derivative_C]
      exact (mul_ne_zero hn an) (da ▸ zf)
    have lt := natDegree_derivative_lt gt
    change g.natDegree<f.natDegree at lt
    rw [natDegree_neg]; dsimp [k,s]; omega)
  let lift:=U.prod V
  have inKer (u : degreeLT L k) : lift u∈LinearMap.ker S := by
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change f*((-a)*(u:(Polynomial L)))+g*(D*(u:(Polynomial L)))=0
    rw [da]; dsimp [f,D]; ring
  let Kmap:=lift.codRestrict (LinearMap.ker S) inKer
  have inject : Function.Injective Kmap := by
    intro x y hxy
    apply Subtype.ext
    exact mul_left_cancel₀ dn (congrArg (fun v : LinearMap.ker S => (v.val.1 : (Polynomial L))) hxy)
  have : FiniteDimensional L (degreeLT L r) := Module.Finite.of_basis (degreeLT.basis L r)
  have : FiniteDimensional L (degreeLT L (r-1)) := Module.Finite.of_basis (degreeLT.basis L (r-1))
  have hk := LinearMap.finrank_le_finrank_of_injective (f:=Kmap) inject
  have dim (q : ℕ) : Module.finrank L (degreeLT L q)=q := by
    simpa using Module.finrank_eq_card_basis (degreeLT.basis L q)
  rw [dim] at hk
  have rank := S.finrank_range_add_finrank_ker
  rw [Module.finrank_prod,dim,dim] at rank
  have eq : (sylvester f g r (r-1)).rank=Module.finrank L (LinearMap.range S) := by
    let dom := ((degreeLT.basis L r).prod (degreeLT.basis L (r-1))).reindex finSumFinEquiv
    rw [Matrix.rank_eq_finrank_range_toLin _ (degreeLT.basis L _) dom,
      ← toMatrix_sylvesterMap' f g ds gd, Matrix.toLin_toMatrix]
  change _ ≤ r+(r-1)-(sylvester f g r (r-1)).rank
  rw [eq]; dsimp [k,s] at hk; omega
theorem square_corank {L : Type} [Field L] [DecidableEq L] (h : (Polynomial L)) {r : ℕ}
    (hr : 0<r) (fit : (h^2).natDegree≤r) :
    (r+1)/2 ≤ r+(r-1)-(sylvester (h^2) (h^2).derivative r (r-1)).rank := by
  simpa using cofactor_corank (e:=0) h 1 hr (by simp) (by simpa using fit)
theorem square_fibres {L : Type} [Field L] [DecidableEq L]
    (Q : Polynomial (Polynomial L)) {r v : ℕ} (hr : 0<r) (d : Q.natDegree≤r)
    (seed : ∀ i,(Q.coeff i).natDegree≤v)
    (sep : Q.resultant Q.derivative r (r-1)≠0) (T : Finset L)
    (square : ∀ z∈T, ∃ h:(Polynomial L), Q.map (evalRingHom z)=h^2) :
    T.card≤4*v := by
  have each (z) (hz : z∈T) : (r+1)/2 ≤ r+(r-1)-
      (sylvester (Q.map (evalRingHom z)) (Q.derivative.map (evalRingHom z)) r (r-1)).rank := by
    obtain ⟨h,hh⟩ := square z hz
    have fit : (h^2).natDegree≤r := by rw [← hh]; exact natDegree_map_le.trans d
    have hcor := square_corank h hr fit
    rw [← hh,derivative_map] at hcor
    exact hcor
  have bound := Finset.sum_le_sum each
  simp only [sum_const,nsmul_eq_mul] at bound
  have upper := sum_sylvester_coranks_le_resultant_natDegree Q Q.derivative r (r-1) T sep
  have fee := Polynomial.natDegree_resultant_le_of_coeff_natDegree_le Q Q.derivative r (r-1) v v seed (fun i => by
    rw [coeff_derivative, mul_comm]
    rw [show ((i:(Polynomial L))+1)=C ((i:L)+1) by simp]
    exact (natDegree_C_mul_le ..).trans (seed _))
  have hh : T.card*((r+1)/2) ≤ r*v+(r-1)*v := (bound.trans upper).trans (fee.trans_eq (Nat.add_comm ..))
  have ceil : r≤2*((r+1)/2) := by omega
  have less : r-1≤r := Nat.sub_le _ _
  have a := Nat.mul_le_mul_left T.card ceil
  have b := Nat.mul_le_mul_right v less
  have rr : T.card*r≤4*v*r := by nlinarith only [a,b,hh]
  exact Nat.le_of_mul_le_mul_right rr hr
end CurvatureSquares
end
noncomputable section
namespace CurvatureSquares
open K1 K1_14 Polynomial Finset RetainedShortening CurvatureVotes
open scoped BigOperators Polynomial Classical
variable {F : Type} [Field F]
abbrev Bi (F : Type) [Field F] := Polynomial (Polynomial F)
def height (Q : Bi F) : ℕ := (Bivariate.swap Q).natDegree
theorem coeff_swap {R : Type} [CommRing R] (Q : Polynomial (Polynomial R)) (i j : ℕ) :
    ((Bivariate.swap Q).coeff i).coeff j=(Q.coeff j).coeff i := by
  induction Q using Polynomial.induction_on' with
  | add f g hf hg => simp [hf,hg]
  | monomial n a =>
    rw [Bivariate.swap_monomial,coeff_mul_C,coeff_map,C_mul_X_pow_eq_monomial]
    by_cases h : n=j <;> simp [coeff_monomial,h]
theorem coeff_height (Q : Bi F) (i : ℕ) : (Q.coeff i).natDegree≤height Q := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [← coeff_swap Q, coeff_eq_zero_of_natDegree_lt hj, coeff_zero]
private theorem factor_height {A B : Bi F} (hn : A*B≠0) :
    height (A*B)=height A+height B := by
  have hA := left_ne_zero_of_mul hn
  have hB := right_ne_zero_of_mul hn
  unfold height
  rw [map_mul,natDegree_mul ((map_ne_zero_iff _ Bivariate.swap.injective).mpr hA)
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr hB)]
private theorem square_div {L : Type} [Field L] {x y : (Polynomial L)} (h : x^2 ∣ y^2) : x ∣ y :=
  (IsIntegrallyClosed.pow_dvd_pow_iff (by decide : (2:ℕ)≠0)).mp h
private theorem cancel_sq {L : Type} [Field L] [IsAlgClosed L]
    (c : L) (h w q : (Polynomial L)) (hc : c≠0) (hh : h≠0)
    (eq : C c*h^2*q=w^2) : ∃ s:(Polynomial L), q=s^2 := by
  obtain ⟨r,rc⟩ := IsAlgClosed.exists_pow_nat_eq (k:=L) c (n:=2) (by decide)
  have rn : r≠0 := by intro hz; simp [hz] at rc; exact hc rc.symm
  let D := C r*h
  have dn : D≠0 := mul_ne_zero (C_ne_zero.mpr rn) hh
  have sqD : D^2=C c*h^2 := by
    exact (mul_pow (C r) h 2).trans (by rw [← C_pow,rc])
  have he : D^2*q=w^2 := by rw [sqD]; exact eq
  have dv : D^2∣w^2 := ⟨q,he.symm⟩
  have divides : D∣w := square_div dv
  obtain ⟨v,hv⟩ := divides
  refine ⟨v,?_⟩
  have eq2 : D^2*q=D^2*v^2 := he.trans ((congrArg (fun x:(Polynomial L) => x^2) hv).trans (mul_pow D v 2))
  exact mul_left_cancel₀ (pow_ne_zero _ dn) eq2
theorem squareclass_count {L : Type} [Field L] [IsAlgClosed L] [DecidableEq L]
    (D H R : Bi L) (c : (Polynomial L)) (hn : D≠0) (fac : D=C c*H^2*R)
    (hr : 0<R.natDegree) (sep : R.resultant R.derivative R.natDegree (R.natDegree-1)≠0)
    (T : Finset L) (marks : ∀ z∈T,∃ w:(Polynomial L),D.map (evalRingHom z)=w^2) :
    T.card≤4*height D := by
  classical
  have prod : C c*H^2*R≠0 := fac ▸ hn
  have hch := left_ne_zero_of_mul prod
  have hc : c≠0 := fun h => by simp [h] at hch
  have hH : H≠0 := fun h => by simp [h] at hch
  have qne : H.coeff H.natDegree≠0 := by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hH
  let B := c*H.leadingCoeff
  have Bne : B≠0 := mul_ne_zero hc (by rwa [coeff_natDegree] at qne)
  let E := T.filter fun z => B.eval z=0
  have exc : E.card≤c.natDegree+height H := by
    have sub : E⊆B.roots.toFinset := by
      intro z hz
      exact Multiset.mem_toFinset.mpr ((mem_roots Bne).mpr (mem_filter.mp hz).2)
    have card := (card_le_card sub).trans ((Multiset.toFinset_card_le ..).trans (card_roots' B))
    have ch := coeff_height H H.natDegree
    rw [coeff_natDegree] at ch
    exact card.trans ((natDegree_mul_le (p:=c) (q:=H.leadingCoeff)).trans (Nat.add_le_add_left ch _))
  have reg := square_fibres R hr le_rfl (coeff_height R) sep (T \ E) (by
    intro z hz
    have hmem := (mem_sdiff.mp hz).1
    have be : B.eval z≠0 := fun h => (mem_sdiff.mp hz).2 (mem_filter.mpr ⟨hmem,h⟩)
    have cg : c.eval z≠0 ∧ H.leadingCoeff.eval z≠0 := by simpa [B] using be
    have hh : H.map (evalRingHom z)≠0 := by
      intro h
      have h' := congrArg (fun q:(Polynomial L) => q.coeff H.natDegree) h
      exact cg.2 (by simpa only [coeff_map,coeff_zero,coeff_natDegree,coe_evalRingHom] using h')
    obtain ⟨w,ew⟩ := marks z hmem
    rw [fac,Polynomial.map_mul,Polynomial.map_mul,Polynomial.map_pow,map_C] at ew
    exact cancel_sq _ _ w _ cg.1 hh ew)
  have hsq := factor_height (A:=H) (B:=H) (mul_ne_zero hH hH)
  rw [← pow_two] at hsq
  have tot : height D=c.natDegree+(height H+height H)+height R := by
    rw [fac,factor_height prod,factor_height hch,hsq]
    simp [height,Bivariate.swap_C,natDegree_map_eq_of_injective C_injective]
  have hcard := card_sdiff_add_card_eq_card (filter_subset (fun z => B.eval z=0) T)
  change (T \ E).card+E.card=T.card at hcard
  omega
theorem root_count {ι : Type*} {S : Finset ι} {z : ι→F} (inj : Set.InjOn z (S:Set ι))
    (q : (Polynomial F)) (nz : q≠0) (van : ∀ i∈S,q.eval (z i)=0) : S.card ≤ q.natDegree := by
  classical
  have sub : S.image z⊆q.roots.toFinset := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact Multiset.mem_toFinset.mpr ((mem_roots nz).mpr (van _ hi))
  exact (card_image_of_injOn inj).symm ▸ (card_le_card sub).trans
    ((Multiset.toFinset_card_le ..).trans (card_roots' q))
theorem separable_kernel {L : Type} [Field L] (Q : Bi L) (sf : Squarefree Q)
    (tame : ∀ q : Bi L, Irreducible q → q∣Q → 0<q.natDegree → q.derivative≠0) :
    (Q.map (algebraMap (Polynomial L) (FractionRing (Polynomial L)))).Separable := by
  classical
  let ι:=algebraMap (Polynomial L) (FractionRing (Polynomial L))
  have inj : Function.Injective ι := IsFractionRing.injective _ _
  induction Q using WfDvdMonoid.induction_on_irreducible with
  | zero => exact False.elim (sf.ne_zero rfl)
  | unit u hu =>
    simpa using (separable_one (R:=FractionRing (Polynomial L))).unit_mul (hu.map (mapRingHom ι))
  | mul a q ha hq ih =>
    have facts := squarefree_mul_iff.mp sf
    have other := ih facts.2.2 (fun f irr dv => tame f irr (dv.trans (dvd_mul_left ..)))
    rw [Polynomial.map_mul]
    by_cases h0 : q.natDegree=0
    · have cc:=eq_C_of_natDegree_eq_zero h0
      have cpos : q.coeff 0≠0 := fun h => hq.ne_zero (by rw [cc,h,map_zero])
      rw [cc,map_C]
      exact other.unit_mul (isUnit_C.mpr ((map_ne_zero_iff _ inj).mpr cpos).isUnit)
    · have hp := hq.isPrimitive h0
      have ir := (hp.irreducible_iff_irreducible_map_fraction_map (K:=FractionRing (Polynomial L))).mp hq
      have deriv := tame q hq (dvd_mul_right ..) (Nat.pos_of_ne_zero h0)
      have sep : (q.map ι).Separable := (separable_iff_derivative_ne_zero ir).mpr (by
        rw [derivative_map]; exact (Polynomial.map_ne_zero_iff inj).mpr deriv)
      apply sep.mul other
      apply ir.coprime_iff_not_dvd.mpr
      intro divides
      have dv := hp.dvd_of_fraction_map_dvd_fraction_map divides
      exact hq.not_isUnit (facts.1 dvd_rfl dv)
theorem kernel_test {L : Type} [Field L] (disc : Bi L) :
    ∃ H R : Bi L, disc=H^2*R ∧ Squarefree R ∧
      (R.natDegree=0 ∨ (0<R.natDegree ∧ R.resultant R.derivative R.natDegree (R.natDegree-1)≠0) ∨
        ∃ q:Bi L, Irreducible q ∧ q∣R ∧ 0<q.natDegree ∧ q.derivative=0) := by
  classical
  obtain ⟨H,R,fac,sf⟩ := exists_sq_mul_squarefree disc
  refine ⟨H,R,fac.symm,sf,?_⟩
  by_cases h0 : R.natDegree=0
  · exact Or.inl h0
  right
  by_cases tame : ∀ q:Bi L, Irreducible q → q∣R → 0<q.natDegree → q.derivative≠0
  · left
    refine ⟨Nat.pos_of_ne_zero h0,?_⟩
    let ι:=algebraMap (Polynomial L) (FractionRing (Polynomial L))
    have inj : Function.Injective ι:=IsFractionRing.injective _ _
    have sep:=separable_kernel R sf tame
    have hres:=Polynomial.resultant_derivative_ne_zero_of_separable _ sep
    rw [natDegree_map_eq_of_injective inj,derivative_map,Polynomial.resultant_map_map] at hres
    exact fun h => hres (by rw [h,map_zero])
  · push Not at tame
    exact Or.inr tame
abbrev Ordinate := Polynomial (Bi K1_14.L)
abbrev Slope := Polynomial Ordinate
def xView : Ordinate →+* Ordinate := Bivariate.swap.toRingHom
def zView : Ordinate →+* Ordinate :=
  Bivariate.swap.toRingHom.comp (mapRingHom Bivariate.swap.toRingHom)
theorem xView_inj : Function.Injective xView := Bivariate.swap.injective
theorem zView_inj : Function.Injective zView :=
  Bivariate.swap.injective.comp (Polynomial.map_injective _ Bivariate.swap.injective)
private theorem inner_degree {R : Type} [CommRing R] (Q : Polynomial (Polynomial R)) (i : ℕ) :
    (Q.coeff i).natDegree ≤ (Bivariate.swap Q).natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [← coeff_swap Q,coeff_eq_zero_of_natDegree_lt hj,coeff_zero]
theorem coeff_caps (Q : Ordinate) (i : ℕ) :
    (Q.coeff i).natDegree≤(xView Q).natDegree ∧ height (Q.coeff i)≤(zView Q).natDegree := by
  refine ⟨inner_degree Q i,?_⟩
  have h:=inner_degree (Q.map (Bivariate.swap (R:=K1_14.L)).toRingHom) i
  rw [coeff_map] at h
  exact h
def ordEval (z : K1_14.L) (y : (Polynomial K1_14.L)) : Ordinate →+* (Polynomial K1_14.L) :=
  eval₂RingHom (mapRingHom (evalRingHom z)) y
private theorem native_quad (f : Ordinate) (hf : f.natDegree=2) :
    f=C (f.coeff 2)*Polynomial.X^2+C (f.coeff 1)*Polynomial.X+C (f.coeff 0) := by
  have e:=f.as_sum_range_C_mul_X_pow' (n:=3) (by omega)
  simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one,mul_one] at e
  exact e.trans (by ac_rfl)
private theorem no_square (f : Ordinate) (irr : Irreducible f) (hf : f.natDegree=2)
    (two : (2:Bi L)≠0) (h : Bi L) :
    f.coeff 1^2-4*f.coeff 2*f.coeff 0≠h^2 := by
  intro sqr
  let a:=f.coeff 2
  let b:=f.coeff 1
  have an : a≠0 := by simpa [a,← hf] using leadingCoeff_ne_zero.mpr irr.ne_zero
  let B : Ordinate:=C (2*a)*Polynomial.X+C b
  have identity : (B-C h)*(B+C h) = f*C (4*a) := by
    conv_rhs => rw [native_quad f hf]
    have he:=congrArg (C : Bi L→+*Ordinate) sqr
    simp only [map_sub,map_pow,map_mul,map_ofNat] at he
    rw [show (B-C h)*(B+C h)=B^2-(C h)^2 by ring,←he]
    dsimp only [B,a,b]
    simp only [map_mul,map_ofNat]
    ring
  have pr : Prime f:=UniqueFactorizationMonoid.irreducible_iff_prime.mp irr
  have div:=pr.dvd_mul.mp (show f∣(B-C h)*(B+C h) from ⟨C (4*a),identity⟩)
  have deg (t : Bi L) : (C (2*a)*Polynomial.X+C t).natDegree=1 := by
    exact natDegree_linear (mul_ne_zero two an)
  rcases div with d|d
  · have e : B-C h=C (2*a)*Polynomial.X+C (b-h) := by simp [B,map_sub]; ring
    rw [e] at d
    have one:=deg (b-h)
    have ne : C (2*a)*Polynomial.X+C (b-h)≠0 := fun Hz => by rw [Hz,natDegree_zero] at one; contradiction
    have := natDegree_le_of_dvd d ne
    omega
  · have e : B+C h=C (2*a)*Polynomial.X+C (b+h) := by simp [B,map_add,add_assoc]
    rw [e] at d
    have one:=deg (b+h)
    have ne : C (2*a)*Polynomial.X+C (b+h)≠0 := fun Hz => by rw [Hz,natDegree_zero] at one; contradiction
    have := natDegree_le_of_dvd d ne
    omega
theorem node_ne (f : Ordinate) (irr : Irreducible f) (pos : 0<f.natDegree) (x : L) :
    f.map (evalRingHom (C x))≠0 := by
  intro zero
  let q : Bi L:=Polynomial.X-C (C x)
  have d : C q∣f := (C_dvd_iff_dvd_coeff ..).mpr (fun i => by
    change Polynomial.X-C (C x)∣f.coeff i
    apply (dvd_iff_isRoot (p:=f.coeff i)).mpr
    have hz:=congrArg (fun g:Polynomial (Polynomial L) => g.coeff i) zero
    change (f.coeff i).eval (C x)=0
    simpa only [coeff_map,coe_evalRingHom,coeff_zero] using hz)
  obtain ⟨g,eqn⟩:=d
  have nu : ¬IsUnit (C q : Ordinate) := by
    intro u
    have z:=natDegree_eq_zero_of_isUnit (isUnit_C.mp u)
    simp [q] at z
  have gu:=(irr.isUnit_or_isUnit eqn).resolve_left nu
  have h:=natDegree_mul_le (p:=C q) (q:=g)
  rw [←eqn,natDegree_C,natDegree_eq_zero_of_isUnit gu] at h
  omega
theorem node_height (q : Bi L) (x : L) : (q.eval (C x)).natDegree≤height q := by
  rw [eval_eq_sum,sum_def]
  apply (natDegree_sum_le ..).trans
  apply Finset.sup_le
  intro i _
  change ((q.coeff i)*C x^i).natDegree≤_
  rw [← C_pow]
  exact (natDegree_mul_C_le ..).trans (coeff_height q i)
theorem node_eval (q : Bi L) (x z : L) :
    (q.eval (C x)).eval z=(q.map (evalRingHom z)).eval x := by
  have e:=eval₂_hom (p:=q) (evalRingHom z) (C x)
  simpa only [coe_evalRingHom,eval_C,eval_map] using e.symm
theorem irreducible_constant_node {A d w s T} (W : Word A d w s T)
    (φ : K →+* L) (z : K→L) (inj : Set.InjOn z (T:Set K)) {k : ℕ}
    (hd : d<A) (scale : VoteScale A d k) (f : Ordinate) (irr : Irreducible f)
    (hf : f.natDegree=2) (two : (2:Bi L)≠0) (c : (Polynomial L)) (h : Bi L)
    (disc : f.coeff 1^2-4*f.coeff 2*f.coeff 0=C c*h^2)
    (marks : ∀ γ∈T,ordEval (z γ) ((s γ).map φ) f=0) :
    T.card≤k*(zView f).natDegree+1 := by
  classical
  have ns : ¬∃ t:(Polynomial L),c=t^2 := by
    rintro ⟨t,ht⟩
    apply no_square f irr hf two (C t*h)
    rw [disc,ht,map_pow,mul_pow]
  apply minority_count W hd scale
  intro i
  let x:=φ (node i)
  let a:=C (φ (w i))
  let g (n:ℕ):=(f.coeff n).eval (C x)
  let q:=g 2*a^2+g 1*a+g 0
  have height_g (n:ℕ) : (g n).natDegree≤(zView f).natDegree :=
    (node_height ..).trans (coeff_caps f n).2
  have qd : q.natDegree≤(zView f).natDegree := by
    change (g 2*C (φ (w i))^2+g 1*C (φ (w i))+g 0).natDegree≤_
    rw [←C_pow]
    exact (natDegree_add_le ..).trans (max_le ((natDegree_add_le ..).trans
      (max_le ((natDegree_mul_C_le ..).trans (height_g 2)) ((natDegree_mul_C_le ..).trans (height_g 1)))) (height_g 0))
  have eqn (γ) (mem : γ∈T) : (g 2).eval (z γ)*(φ ((s γ).eval (node i)))^2+
      (g 1).eval (z γ)*(φ ((s γ).eval (node i)))+(g 0).eval (z γ)=0 := by
    have e:=marks γ mem
    rw [native_quad f hf] at e
    simp only [map_add,map_mul,map_pow,ordEval,coe_eval₂RingHom,eval₂_C,eval₂_X] at e
    have atx:=congrArg (eval x) e
    simpa only [g,node_eval,eval_add,eval_mul,eval_pow,eval_zero,eval_map_apply,x,
      coe_mapRingHom] using atx
  by_cases proper : q≠0
  · left
    apply (root_count (inj.mono (filter_subset _ _)) q proper _).trans qd
    intro γ mem
    obtain ⟨hm,hit⟩:=mem_filter.mp mem
    simpa [q,a,hit] using eqn γ hm
  · have zero : q=0:=not_ne_iff.mp proper
    have dx := congrArg (eval (C x)) disc
    simp only [eval_sub,eval_pow,eval_mul,eval_ofNat,eval_C] at dx
    change g 1^2-4*g 2*g 0=c*(h.eval (C x))^2 at dx
    have sq : (2*g 2*a+g 1)^2=c*(h.eval (C x))^2 := by
      change g 2*a^2+g 1*a+g 0=0 at zero
      linear_combination dx + 4*g 2*zero
    have hzero : h.eval (C x)=0 := by
      by_contra hn
      have dv : (h.eval (C x))^2∣(2*g 2*a+g 1)^2 := ⟨c,by rw [sq,mul_comm]⟩
      obtain ⟨t,ht⟩:=(IsIntegrallyClosed.pow_dvd_pow_iff (by decide : (2:ℕ)≠0)).mp dv
      apply ns
      exact ⟨t,mul_left_cancel₀ (pow_ne_zero 2 hn) (by rw [←mul_pow,←ht,sq,mul_comm])⟩
    have root : 2*g 2*a+g 1=0 := by simpa [hzero] using sq
    have gn : g 2≠0 := by
      intro h2
      have h1 : g 1=0 := by simpa [h2] using root
      have h0 : g 0=0 := by simpa [q,h2,h1] using zero
      apply node_ne f irr (by omega) x
      rw [native_quad f hf]
      change (f.coeff 2).eval (C x)=0 at h2
      change (f.coeff 1).eval (C x)=0 at h1
      change (f.coeff 0).eval (C x)=0 at h0
      simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,map_C,map_X,coe_evalRingHom,
        h2,h1,h0,map_zero,zero_mul,zero_add]
    right
    apply (root_count (inj.mono (filter_subset _ _)) (g 2) gn _).trans (height_g 2)
    intro γ mem
    obtain ⟨hm,miss⟩:=mem_filter.mp mem
    have e:=eqn γ hm
    have ez:=congrArg (eval (z γ)) zero
    have er:=congrArg (eval (z γ)) root
    simp only [q,a,eval_add,eval_mul,eval_pow,eval_C,eval_ofNat,eval_zero] at ez er
    have val : (g 2).eval (z γ)*(φ ((s γ).eval (node i))-φ (w i))^2=0 := by
      linear_combination e - ez - (φ ((s γ).eval (node i))-φ (w i))*er
    exact (mul_eq_zero.mp val).resolve_right (pow_ne_zero _ (sub_ne_zero.mpr (φ.injective.ne miss)))
theorem irreducible_quadratic_chart {A d w s T} (W : Word A d w s T)
    (φ : K →+* L) (z : K→L) (inj : Set.InjOn z (T:Set K)) {k : ℕ}
    (hd : d<A) (scale : VoteScale A d k) (f : Ordinate) (irr : Irreducible f)
    (hf : f.natDegree=2) (two : (2:Bi L)≠0)
    (marks : ∀ γ∈T,ordEval (z γ) ((s γ).map φ) f=0) :
    T.card≤max 8 k*(zView f).natDegree+1 ∨
      let Δ:=f.coeff 1^2-4*f.coeff 2*f.coeff 0
      Δ≠0 ∧ ∃ H R q : Bi L, Δ=H^2*R ∧ Squarefree R ∧ Irreducible q ∧ q∣R ∧
        0<q.natDegree ∧ q.derivative=0 := by
  classical
  let Δ:=f.coeff 1^2-4*f.coeff 2*f.coeff 0
  have nz : Δ≠0 := by simpa [Δ] using no_square f irr hf two 0
  obtain ⟨H,R,fac,sf,test⟩:=kernel_test Δ
  rcases test with vert|sep|wild
  · left
    have eqn : Δ=C (R.coeff 0)*H^2 := by
      calc Δ = H^2*R := fac
           _ = C (R.coeff 0)*H^2 := by conv_lhs => rw [eq_C_of_natDegree_eq_zero vert]; rw [mul_comm]
    have h:=irreducible_constant_node W φ z inj hd scale f irr hf two _ _ eqn marks
    exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (le_max_right 8 k)) 1)
  · left
    have weight : height Δ≤2*(zView f).natDegree := by
      unfold Δ height
      simp only [map_sub,map_pow,map_mul,map_ofNat]
      apply (natDegree_sub_le ..).trans
      apply max_le
      · rw [natDegree_pow]; have := (coeff_caps f 1).2; unfold height at this; omega
      · have a:=natDegree_mul_le (p:=(4:Bi L)*Bivariate.swap (f.coeff 2)) (q:=Bivariate.swap (f.coeff 0))
        have b:=natDegree_mul_le (p:=(4:Bi L)) (q:=Bivariate.swap (f.coeff 2))
        rw [natDegree_ofNat] at b
        have h2:=(coeff_caps f 2).2
        have h0:=(coeff_caps f 0).2
        unfold height at h2 h0
        omega
    have count:=squareclass_count Δ H R 1 nz (by simpa using fac) sep.1 sep.2 (T.image z) (by
      intro x hx
      obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hx
      let m:=evalRingHom (z γ)
      let y:=(s γ).map φ
      have e:=marks γ hγ
      rw [native_quad f hf] at e
      simp only [map_add,map_mul,map_pow,ordEval,coe_eval₂RingHom,eval₂_C,eval₂_X,coe_mapRingHom] at e
      refine ⟨2*((f.coeff 2).map m)*y+(f.coeff 1).map m,?_⟩
      simp only [Δ,Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_mul,Polynomial.map_ofNat]
      dsimp only [m,y]
      linear_combination -4*((f.coeff 2).map (evalRingHom (z γ)))*e)
    rw [card_image_of_injOn inj] at count
    exact (count.trans (Nat.mul_le_mul_left 4 weight)).trans (by
      have h:=Nat.mul_le_mul_right (zView f).natDegree (le_max_left 8 k)
      omega)
  · exact Or.inr ⟨nz,H,R,wild.choose,fac,sf,wild.choose_spec⟩
theorem irreducible_linear_node {A d w s T} (W : Word A d w s T)
    (φ : K →+* L) (z : K→L) (inj : Set.InjOn z (T:Set K)) {k : ℕ}
    (hd : d<A) (scale : VoteScale A d k) (f : Ordinate) (irr : Irreducible f)
    (hf : f.natDegree=1) (marks : ∀ γ∈T,ordEval (z γ) ((s γ).map φ) f=0) :
    T.card≤k*(zView f).natDegree+1 := by
  classical
  apply minority_count W hd scale
  intro i
  let x:=φ (node i)
  let g (n:ℕ):=(f.coeff n).eval (C x)
  let q:=g 1*C (φ (w i))+g 0
  have cap (n:ℕ) : (g n).natDegree≤(zView f).natDegree := (node_height ..).trans (coeff_caps f n).2
  have eqn (γ) (hm : γ∈T) : (g 1).eval (z γ)*φ ((s γ).eval (node i))+(g 0).eval (z γ)=0 := by
    have e:=marks γ hm
    rw [eq_X_add_C_of_natDegree_le_one hf.le] at e
    simp only [map_add,map_mul,ordEval,coe_eval₂RingHom,eval₂_C,eval₂_X,coe_mapRingHom] at e
    simpa only [g,node_eval,eval_add,eval_mul,eval_zero,x,eval_map_apply] using congrArg (eval x) e
  by_cases proper : q≠0
  · left
    apply (root_count (inj.mono (filter_subset _ _)) q proper _).trans
        ((natDegree_add_le ..).trans (max_le ((natDegree_mul_C_le ..).trans (cap 1)) (cap 0)))
    intro γ mem
    obtain ⟨hm,hit⟩:=mem_filter.mp mem
    simpa [q,hit] using eqn γ hm
  · right
    have zero:=not_ne_iff.mp proper
    have nz : g 1≠0 := by
      intro ho
      have hz : g 0=0 := by simpa [q,ho] using zero
      apply node_ne f irr (by omega) x
      rw [eq_X_add_C_of_natDegree_le_one hf.le]
      change (f.coeff 1).eval (C x)=0 at ho
      change (f.coeff 0).eval (C x)=0 at hz
      simp only [Polynomial.map_add,Polynomial.map_mul,map_C,map_X,coe_evalRingHom,
        ho,hz,map_zero,zero_mul,zero_add]
    apply (root_count (inj.mono (filter_subset _ _)) (g 1) nz _).trans (cap 1)
    intro γ mem
    obtain ⟨hm,miss⟩:=mem_filter.mp mem
    have ez:=congrArg (eval (z γ)) zero
    simp only [q,eval_add,eval_mul,eval_C,eval_zero] at ez
    have h : (g 1).eval (z γ)*(φ ((s γ).eval (node i))-φ (w i))=0 := by
      linear_combination eqn γ hm - ez
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr (φ.injective.ne miss))
variable {E : Type*} [Field E]
theorem derivative_ne_zero_of_natDegree_pos_lt_char
    (p : ℕ) [CharP E p] (f : (Polynomial E))
    (hpos : 0 < f.natDegree) (hlt : f.natDegree < p) : f.derivative ≠ 0 := by
  intro hzero
  have hf : f ≠ 0 := by
    intro heq
    simp [heq] at hpos
  have hn : f.natDegree - 1 + 1 = f.natDegree := by omega
  have hcoeff : f.coeff f.natDegree * (f.natDegree : E) = 0 := by
    have heq := congrArg (fun q : (Polynomial E) ↦ q.coeff (f.natDegree - 1)) hzero
    simpa only [coeff_derivative, coeff_zero, ← Nat.cast_add_one, hn] using heq
  have hlead : f.coeff f.natDegree ≠ 0 := by
    simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hf
  have hcast : (f.natDegree : E) ≠ 0 := by
    intro hz
    have hdiv : p ∣ f.natDegree := (CharP.cast_eq_zero_iff E p _).mp hz
    have hd : f.natDegree = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
    omega
  exact (mul_ne_zero hlead hcast) hcoeff
theorem degree_two_count {A d w s T} (W : Word A d w s T)
    (φ : K →+* K1_14.L) (z : K→K1_14.L) (inj : Set.InjOn z (T:Set K)) {k : ℕ}
    (hd : d<A) (scale : VoteScale A d k)
    (F : Ordinate) (irr : Irreducible F) (deg : F.natDegree=2) (tame : 2*(xView F).natDegree<p)
    (marks : ∀ γ∈T,ordEval (z γ) ((s γ).map φ) F=0) :
    T.card≤max 8 k*(zView F).natDegree+2 := by
  have two : (2:K1_14.L)≠0 := by
    have h : ((2:ℕ):K)≠0 := fun a => (by decide : ¬p∣2) ((CharP.cast_eq_zero_iff K p 2).mp a)
    have hn : (2:K)≠0 := by exact_mod_cast h
    simpa only [map_ofNat,map_zero] using φ.injective.ne hn
  have large : (2:Bi K1_14.L)≠0 := by
    simpa only [map_ofNat] using (C_ne_zero.mpr (C_ne_zero.mpr two))
  have alt:=irreducible_quadratic_chart W φ z inj hd scale F irr deg large marks
  apply (alt.resolve_right ?_).trans (by omega)
  rintro ⟨nonzero,H,R,q,fac,_,_,div,pos,dzero⟩
  have small := natDegree_le_of_dvd (div.trans (fac ▸ dvd_mul_left ..)) nonzero
  have bound : (F.coeff 1^2-4*F.coeff 2*F.coeff 0).natDegree≤2*(xView F).natDegree := by
    apply (natDegree_sub_le ..).trans
    apply max_le
    · rw [natDegree_pow]; have := (coeff_caps F 1).1; omega
    · have h:=natDegree_mul_le (p:=(4:Bi K1_14.L)*F.coeff 2) (q:=F.coeff 0)
      have h':=natDegree_mul_le (p:=(4:Bi K1_14.L)) (q:=F.coeff 2)
      rw [natDegree_ofNat] at h'
      have := (coeff_caps F 2).1; have := (coeff_caps F 0).1; omega
  let ι:=algebraMap (Polynomial K1_14.L) (FractionRing (Polynomial K1_14.L))
  let : CharP (FractionRing (Polynomial K1_14.L)) p := charP_of_injective_ringHom
    ((ι.comp Polynomial.C).comp φ).injective p
  have eq:= natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial K1_14.L) (FractionRing (Polynomial K1_14.L))) q
  exact derivative_ne_zero_of_natDegree_pos_lt_char p (q.map ι)
    (eq ▸ pos) (eq ▸ (small.trans bound).trans_lt tame) (by rw [derivative_map,dzero,Polynomial.map_zero])
private theorem low_factor {A d w s T} (W : Word A d w s T)
    (φ : K →+* K1_14.L) (z : K→K1_14.L) (inj : Set.InjOn z (T:Set K)) {k : ℕ}
    (hd : d<A) (scale : VoteScale A d k)
    (F : Ordinate) (irr : Irreducible F) (deg : F.natDegree≤2) (tame : 2*(xView F).natDegree<p)
    (marks : ∀ γ∈T,ordEval (z γ) ((s γ).map φ) F=0) :
    T.card≤(max 8 k)*(zView F).natDegree+2*F.natDegree := by
  have nz:=irr.ne_zero
  by_cases zero : F.natDegree=0
  · have cn : F.coeff 0≠0 := by simpa only [← coeff_natDegree,zero] using leadingCoeff_ne_zero.mpr nz
    have hn:=leadingCoeff_ne_zero.mpr cn
    let P:=(F.coeff 0).leadingCoeff
    have dz : P.natDegree≤(zView F).natDegree := by
      apply le_trans _ (coeff_caps F 0).2
      simpa only [P,← coeff_natDegree] using coeff_height (F.coeff 0) (F.coeff 0).natDegree
    have sub : T.image z ⊆ P.roots.toFinset := by
      intro x hx
      obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hx
      apply Multiset.mem_toFinset.mpr ((mem_roots hn).mpr ?_)
      have m:=marks γ hγ
      rw [eq_C_of_natDegree_eq_zero zero] at m
      simp only [ordEval,coe_eval₂RingHom,eval₂_C,coe_mapRingHom] at m
      have hc:=congrArg (fun b : (Polynomial K1_14.L) => b.coeff (F.coeff 0).natDegree) m
      simpa only [coeff_map,coe_evalRingHom,coeff_natDegree,coeff_zero,P,IsRoot] using hc
    have h:=(card_le_card sub).trans ((Multiset.toFinset_card_le ..).trans (card_roots' P))
    rw [card_image_of_injOn inj] at h
    have le:=Nat.mul_le_mul_right (zView F).natDegree (show 1≤max 8 k by omega)
    exact (h.trans dz).trans (by omega)
  by_cases two : F.natDegree=2
  · have h:=degree_two_count W φ z inj hd scale F irr two tame marks; omega
  have one : F.natDegree=1 := by omega
  have h:=irreducible_linear_node W φ z inj hd scale F irr one marks
  have c:=Nat.mul_le_mul_right (zView F).natDegree (le_max_right 8 k)
  omega
theorem projected_low_count {A d w s T} (W : Word A d w s T)
    (φ : K →+* K1_14.L) (z : K→K1_14.L) (inj : Set.InjOn z (T:Set K)) {k : ℕ}
    (hd : d<A) (scale : VoteScale A d k) (P : Ordinate) :
    P≠0 → 2*(xView P).natDegree<p →
    (∀ γ∈T,∃ f:Ordinate, Irreducible f ∧ f∣P ∧ f.natDegree≤2 ∧ ordEval (z γ) ((s γ).map φ) f=0) →
    T.card≤(max 8 k)*(zView P).natDegree+2*P.natDegree := by
  classical
  induction P using WfDvdMonoid.induction_on_irreducible generalizing T with
  | zero => simp
  | unit P unit =>
    intro _ _ cov
    have emp : T=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro γ hγ; obtain ⟨f,irr,dv,_⟩:=cov γ hγ
      exact irr.not_isUnit (isUnit_of_dvd_unit dv unit)
    simp [emp]
  | mul a q ha irr ih =>
    intro _ tame cov
    let U:=T.filter (fun γ => ∃ f:Ordinate, Irreducible f ∧ f∣a ∧
      f.natDegree≤2 ∧ ordEval (z γ) ((s γ).map φ) f=0)
    have usub : U⊆T := filter_subset _ _
    have subword (V) (h : V⊆T) : Word A d w s V :=
      ⟨W.distinct.mono h,fun γ hm => W.degree γ (h hm),fun γ hm => W.hits γ (h hm)⟩
    have eqx : (xView (q*a)).natDegree=(xView q).natDegree+(xView a).natDegree := by
      rw [map_mul,natDegree_mul ((map_ne_zero_iff _ xView_inj).mpr irr.ne_zero) ((map_ne_zero_iff _ xView_inj).mpr ha)]
    rw [eqx] at tame
    have reg := ih (subword U usub) (inj.mono usub) ha (by omega) (fun γ h => (mem_filter.mp h).2)
    let V:=T \ U
    have vsub : V⊆T := sdiff_subset
    have rest (γ) (hγ : γ∈V) : q.natDegree≤2 ∧ ordEval (z γ) ((s γ).map φ) q=0 := by
      have mem:=vsub hγ
      obtain ⟨f,ir,dv,degree,zero⟩:=cov γ mem
      have fp : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp ir
      have fq : f∣q := (fp.dvd_mul.mp dv).resolve_right (fun fa =>
        (mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨mem, f,ir,fa,degree,zero⟩))
      have assoc := ir.associated_of_dvd irr fq
      refine ⟨(natDegree_le_of_dvd assoc.symm.dvd ir.ne_zero).trans degree,?_⟩
      obtain ⟨b,hb⟩:=fq
      rw [hb,map_mul,zero,zero_mul]
    have rem : V.card≤(max 8 k)*(zView q).natDegree+2*q.natDegree := by
      obtain em|⟨γ,hγ⟩ := V.eq_empty_or_nonempty
      · simp [em]
      exact low_factor (subword V vsub) φ z (inj.mono vsub) hd scale q irr (rest _ hγ).1
        (by omega) (fun x hx => (rest x hx).2)
    have sc:=card_sdiff_add_card_eq_card usub
    change V.card+U.card=T.card at sc
    rw [map_mul,natDegree_mul ((map_ne_zero_iff _ zView_inj).mpr irr.ne_zero) ((map_ne_zero_iff _ zView_inj).mpr ha),
        natDegree_mul irr.ne_zero ha]
    nlinarith only [sc,reg,rem]
end CurvatureSquares
end
#print axioms CurvatureSquares.projected_low_count

end Merged6967_R6960QuadraticProjection
