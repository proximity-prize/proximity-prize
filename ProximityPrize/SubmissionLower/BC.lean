import ArkLib.Data.MvPolynomial.WeightedOrder
import ArkLib.Data.Polynomial.SpecializationAvoidance
import ArkLib.ToMathlib.LinearAlgebra.Matrix.Rank
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertBidegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCappedDegree
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.FLT.MasonStothers
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Smooth.Field
import ProximityPrize.SubmissionLower.BB
set_option Elab.async false
set_option maxHeartbeats 3000000
open _root_ renaming AddCommGroup→Bf,AdjoinRoot→qJ,Algebra→n5,Algebra.FiniteType→xu,Algebra.FormallySmooth→FK,Algebra.IsAlgebraic→JW,Algebra.IsPushout→X8,Algebra.TensorProduct.includeRight→Wl,Algebra.TensorProduct.rightAlgebra→Np,Algebra.algebraMap→aU,Algebra.algebraMapSubmonoid→HZ,Algebra.linearMap→ IU,Algebra.lmul→ Iw,Algebra.smul_def→vi,Algebra.trdeg→J4,Cardinal.toNat_add→NY,Classical.propDecidable→KI,CommRing→lz,DecidableEq→ ox,ExpChar→t3,FaithfulSMul→Kl,Field→cy,Fin.prod_univ_succ→Qx,Fin.sum_univ_eq_sum_range→Vl,Fin.sum_univ_succ→Pc,Finite.of_injective→Un,FiniteDimensional→RJ,Finset→nI,Finset.card_filter_add_card_filter_not→WW,Finset.card_image_of_injective→Vq,Finset.card_univ→zk,Finset.mem_filter→Ee,Finset.mem_univ→u5,Finset.mul_sum→sI,Finset.sum_add_distrib→VO,Finset.sum_apply→yQ,Finset.sum_comm→zS,Finset.sum_congr→pC,Finset.sum_const→GR,Finset.sum_const_zero→SW,Finset.sum_eq_single_of_mem→Xp,Finset.sum_eq_zero→S2,Finset.sum_le_sum→G9,Finset.sum_mul→yL,Finset.univ→vj,Finsupp.prod_fintype→Nr,Finsupp.sum_fintype→N0,Finsupp.weight_apply→Pj
open _root_ renaming Fintype→lJ,Fintype.card→lV,Fintype.card_fin→t8,Fintype.equivFinOfCardEq→G2,FractionRing→G4,Function.Injective→mD,Function.Surjective→yU,Ideal→nX,Ideal.Quotient.eq_zero_iff_mem→Ml,Ideal.Quotient.mk→p7,Ideal.Quotient.mk_surjective→uh,Ideal.annihilator_quotient→XJ,Ideal.map_pow→ II,Ideal.mem_map_of_mem→NX,Ideal.mem_sup_left→PD,Ideal.mem_sup_right→XB,Ideal.mul_mem_mul→VS,Ideal.ofList→wY,Ideal.ofList_cons→Mw,Ideal.pow_le_pow_right→Fa,Ideal.pow_mem_pow→MK,Ideal.radical_mono→Ww,Ideal.smul_top_eq_map→UY,Ideal.span→nq,Ideal.span_singleton_eq_bot→Wm,Ideal.span_singleton_le_iff_mem→Gj,Ideal.subset_span→Dw,Infinite→Cy,IntermediateField.adjoin→Ye,IntermediateField.subset_adjoin→WX,IsAlgebraic→p6,IsAssociatedPrime→G5,IsDomain→t5,IsFractionRing.injective→Gn,IsIntegral→v9,IsIntegral.of_pow→Te,IsLocalRing→t4,IsLocalRing.CotangentSpace→x7,IsLocalRing.ResidueField→pG,IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal→Xu,IsLocalRing.maximalIdeal→lI,IsLocalRing.residue_eq_zero_iff→JQ,IsLocalRing.residue_surjective→C4,IsNoetherianRing→zm,IsReduced→Et,IsSMulRegular→FQ
open _root_ renaming IsScalarTower→vl,IsScalarTower.algebraMap_apply→Pr,IsScalarTower.algebraMap_smul→KH,IsScalarTower.of_algHom→PA,Lagrange.coeff_eq_sum→Pk,Lagrange.degree_interpolate_lt→SM,Lagrange.eval_interpolate_at_node→Up,Lagrange.interpolate→Re,LinearIndepOn→ Il,LinearIndependent→vw,LinearMap.finrank_le_finrank_of_injective→UZ,LinearMap.finrank_range_add_finrank_ker→t6,LinearMap.id→LO,LinearMap.ker→ oK,LinearMap.range→ In,List.mem_cons_of_mem→Kz,List.perm_append_comm→Yc,Localization.AtPrime→yB,Localization.Away→SL,Matrix→c9,Matrix.cramer_apply→yJ,Matrix.det_transpose→JK,Matrix.map_apply→Du,Matrix.map_updateCol→Qw,Matrix.mulVec→th,Matrix.mulVec_cramer→WK,Matrix.mulVec_mulVec→UP,Matrix.mulVec_single_one→WY,Matrix.mulVec_smul→Lf,Matrix.mulVec_sub→LQ,Matrix.rank_eq_finrank_span_cols→Mj,Matrix.rank_eq_finrank_span_row→Gi,Matrix.row→EP,Matrix.submatrix_apply→NI,Matrix.updateCol_ne→Rm,Matrix.updateCol_self→Vz,Module.Basis→ze,Module.Finite→pz,Module.Flat→z9,Module.annihilator→qz,Module.finrank→ oz,Module.finrank_fintype_fun_eq_card→zd,Module.finrank_pi_fintype→Mk,Module.length→t7,Module.length_eq_of_surjective→Ob,Module.length_le_of_surjective→SU,Module.length_quotient→Sv,Module.rank→GF
open _root_ renaming Module.rank_lt_aleph0→wR,ModuleCat.of→z8,MvPolynomial→ ov,MvPolynomial.X→zh,MvPolynomial.affineHilbertFunction→qM,MvPolynomial.affineHilbertPolynomial→uW,MvPolynomial.eval→p9,MvPolynomial.eval₂Hom→zR,MvPolynomial.eventually_eval_affineHilbertPolynomial→TH,MvPolynomial.le_degreeOf_of_mem_support→u8,MvPolynomial.natDegree_aeval_le_weightedTotalDegree→Vs,MvPolynomial.quotientDegreeLE→qm,MvPolynomial.ringHom_ext→xL,Nat.add_le_add_right→WD,Nat.add_mul_mod_self_left→XG,Nat.cast_add→zg,Nat.eq_of_mul_eq_mul_left→MS,Nat.exists_eq_succ_of_ne_zero→Yi,Nat.mod_eq_of_lt→F9,Option→vH,Order.coheight→FU,Pi.single→v8,Pi.single_apply→G6,Pi.single_eq_same→Pv,Pi.smul_apply→qx,Pi.sub_apply→LP,Pi.zero_apply→u9,Polynomial.C→uJ,Polynomial.C_mul_X_pow_eq_monomial→Kv,Polynomial.X→qU,Polynomial.aeval→Dz,Polynomial.card_le_degree_of_subset_roots→Fz,Polynomial.coe_evalRingHom→Ok,Polynomial.coeff_monomial→R9,Polynomial.coeff_zero→QL,Polynomial.derivative→uz,Polynomial.evalRingHom→ oq,Polynomial.eval_eq_sum_range'→S1,Polynomial.eval_mul→vh,Polynomial.finsetSum_coeff→TZ,Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity→Yo,Polynomial.map_map→Xg,Polynomial.map_mul→Qy,Polynomial.map_prod→VH,Polynomial.mem_roots→xW,Polynomial.monomial→yo,Polynomial.natDegree_C_mul_le→Sd,Polynomial.natDegree_le_of_eventually_eval_natCast_le→LR
open _root_ renaming Polynomial.natDegree_lt_iff_degree_lt→Mz,Polynomial.natDegree_mul→G3,Polynomial.natDegree_mul_le→FR,Polynomial.natDegree_sum_le_of_forall_le→Ea,RingHom.comp_apply→RP,RingHom.congr_fun→P7,RingHom.ker→qG,RingHom.ker_eq_comap_bot→RD,RingHom.mapMatrix_apply→yl,RingHom.mem_ker→FV,RingHomInvPair.of_ringEquiv→Ts,Set.InjOn→Gk,Set.Subsingleton.finite→NZ,Set.mem_range_self→EK,Set.range→ oZ,Set.subset_univ→Df,Submodule→pL,Submodule.eq_of_le_of_finrank_eq→Xo,Submodule.factor→MO,Submodule.factor_surjective→SD,Submodule.mem_span_range_iff_exists_fun→NW,Submodule.span→pU,Submodule.subset_span→Dv,Submodule.sum_mem→Kp,Subsingleton→Ef,Subtype.ext→vk,Subtype.val→Av,WithBot→vZ,add_sub_cancel_right→ IT,add_zero→wB,associatedPrimes→xm,associatedPrimes.finite→Xx,biUnion_associatedPrimes_eq_compl_regular→OJ,congrArg→ oj,congrFun→ oy,div_eq_mul_inv→KA,dotProduct→sS,exists_linearIndependent'→Pf,faithfulSMul_iff_algebraMap_injective→Hw,finrank_span_eq_card→G1,finrank_span_singleton→TI,frobenius→zE,frobenius_def→Gr,inferInstance→xI,injective_iff_map_eq_zero→PM,integralClosure→wA
open _root_ renaming inv_mul_cancel₀→G8,isAlgebraic_algebraMap→SC,isIntegral_algebraMap→C9,isReduced_of_injective→Kh,iterateFrobenius→t9,iterateFrobenius_def→Oc,iterateFrobenius_inj→RC,le_antisymm→z7,le_sup_left→G7,le_sup_right→X4,liftOfDerivationToSquareZero_apply→Nj,map_add→Aa,map_mul→ oD,map_sub→sH,map_sum→ oY,map_zero→p5,mul_assoc→Ar,mul_comm→qy,mul_left_cancel₀→Au,mul_ne_zero→zi,nonZeroDivisors→JM,pow_add→vG,pow_ne_zero→Kc,ringKrullDim→y5,smul_eq_mul→pQ,sub_eq_zero→G0,sub_self→zc,trdeg_add_eq→zf,trdeg_eq_zero→GY,true_and→Eg
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace baC
noncomputable section
open scoped nonZeroDivisors
theorem finite_quotient {F B:Type} [cy F] [lz B] [IsDedekindDomain B]
  [n5 F B] [xu F B] (J:nX B) (hJ:J ≠ ⊥) :
  pz F (B ⧸ J) := by
 apply (Module.finite_iff_krullDimLE_zero F (B ⧸ J)).2
 apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.2
 intro P hP
 exact hP.1.1.isMaximal (ne_bot_of_le_ne_bot hJ hP.1.2)
private theorem c6K {F M N :Type} [cy F] [Bf M] [Module F M]
  [Bf N] [Module F N] (g:M →ₗ[F] N) (hg:mD g)
  (U:pL F M) :
  GF F (N ⧸ U.map g)=GF F (N ⧸ g.range)+Module.rank F (M ⧸ U) := by
 let e :M ≃ₗ[F] g.range :=LinearEquiv.ofInjective g hg
 let eq : (M ⧸ U) ≃ₗ[F] (↥g.range ⧸ U.map g.rangeRestrict) :=
  Submodule.Quotient.equiv U _ e rfl
 rw [LinearMap.rank_quot_submodule_map_eq,← eq.rank_eq]
variable {F A:Type} [cy F] [lz A] [t5 A] [n5 F A]
local notation "K" => FractionRing A
local notation "B" => integralClosure A (FractionRing A)
private theorem ceo {R S:Type} [lz R] [lz S] [n5 R S]
  (b:S) : (Iw R S b).range=(nq {b} : nX S).restrictScalars R:= by
 ext x
 change (∃ y,b*y=x)↔x∈nq {b}
 rw [Ideal.mem_span_singleton]
 exact exists_congr fun _=>eq_comm
private theorem dOI [pz A B] :
  ∃ d:A,d≠0 ∧ ∀ b:B,d•b∈(IU A B).range := by
 obtain ⟨s,hs⟩:=(Module.Finite.fg_top (R:=A) (M:=B))
 obtain ⟨d,hd⟩:=IsLocalization.exist_integer_multiples (JM A) s
  (aU B K)
 refine ⟨d,mem_nonZeroDivisors_iff_ne_zero.mp d.property,?_⟩
 let m:B →ₗ[A] B:=d.val•LO
 have hle :pU A (↑s :Set B)≤(IU A B).range.comap m:= by
  apply Submodule.span_le.2
  intro b hb
  obtain ⟨a,ha⟩:=hd b hb
  refine ⟨a,vk ?_⟩
  change aU A K a=aU B K (d.val•b)
  simpa only [vi ,oD,← Pr A B K] using ha
 rw [hs] at hle
 exact fun b=>hle (Submodule.mem_top (x :=b))
theorem dOp [xu F A] [pz A B]
    [IsDedekindDomain B] (a :A) (ha :a≠0) :
    pz F (A ⧸ nq {a}) ∧
      oz F (A ⧸ nq {a}) =
        oz F (B ⧸ nq {aU A B a}) := by
  let:xu F B:=Algebra.FiniteType.trans ‹Algebra.FiniteType F A› xI
  let i:A →ₗ[F] B:=(Algebra.algHom F A B).toLinearMap
  have hi:mD i:= by
    intro x y h
    exact Gn A K (oj Av h)
  let U:=i.range
  let b:=aU A B a
  have hb:b≠0:= fun he=>ha (hi (he.trans (p5 _).symm))
  let g:=Iw F B b
  have hg:mD g:= fun x y h=>Au hb h
  let P:=(nq {a} : nX A).restrictScalars F
  have hmap :P.map i=U.map g:= by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨z,rfl⟩:=Ideal.mem_span_singleton.mp (show y∈nq {a} from hy)
      exact ⟨i z,⟨z,rfl⟩,(oD (aU A B) a z).symm⟩
    · rintro ⟨_,⟨z,rfl⟩,rfl⟩
      exact ⟨a*z,Ideal.mem_span_singleton.mpr ⟨z,rfl⟩,oD (aU A B) a z⟩
  obtain ⟨d,hd,hdcon⟩:=dOI (A:=A)
  let u:=Iw F B (aU A B d)
  have hu:u.range≤U:= by
    rintro _ ⟨x,rfl⟩
    obtain ⟨y,hy⟩:=hdcon x
    exact ⟨y,hy.trans (vi d x)⟩
  have hdB:aU A B d≠0:= fun he=>hd (hi (he.trans (p5 _).symm))
  have hfd:pz F (B ⧸ nq {aU A B d}) :=
    finite_quotient _ (by simpa only [ne_eq,Wm] using hdB)
  have :pz F (B ⧸ u.range) := by
    rw [show u.range=(nq {aU A B d} : nX B).restrictScalars F
      from ceo _]
    exact hfd
  have :pz F (B ⧸ U) :=
    Module.Finite.of_surjective (MO hu) (SD hu)
  have hfb:pz F (B ⧸ nq {b}) :=
    finite_quotient _ (by simpa only [ne_eq,Wm] using hb)
  have :pz F (B ⧸ g.range) := by
    rw [show g.range=(nq {b} : nX B).restrictScalars F from ceo _]
    exact hfb
  have h₁:=c6K i hi P
  have h₂:=c6K g hg U
  rw [hmap,h₂] at h₁
  have :pz F (A ⧸ P) := by
    apply (Module.rank_lt_aleph0_iff).mp
    apply (Cardinal.add_lt_aleph0_iff.mp (_ :
      GF F (B ⧸ U)+Module.rank F (A ⧸ P)<Cardinal.aleph0)).2
    rw [← h₁]
    exact Cardinal.add_lt_aleph0 (wR F _) (wR F _)
  refine ⟨‹Module.Finite F (A ⧸ P)›,?_⟩
  have he :=oj Cardinal.toNat h₁
  rw [NY (wR F _) (wR F _),
    NY (wR F _) (wR F _)] at he
  have he' : oz F (B ⧸ g.range)+Module.finrank F (B ⧸ U) =
      oz F (B ⧸ U)+Module.finrank F (A ⧸ P) :=he
  have hr :oz F (A ⧸ P)=oz F (B ⧸ g.range) := by omega
  rw [show g.range=(nq {b} : nX B).restrictScalars F from ceo _] at hr
  exact hr
end
end baC
end
section
namespace bjD
open Ideal IsLocalRing RingTheory.Sequence CategoryTheory Abelian
open scoped Pointwise
universe u v
section Local
variable {k :Type v} [cy k] [Cy k]
variable {R:Type u} [lz R] [zm R] [t4 R] [n5 k R]
include k in
omit [t4 R] in
private theorem buW {M:Type u} [Bf M] [Module R M] [pz R M]
    (a :R) (J:nX R)
    (h : ∀ P∈xm R M,a∈P → ¬ J≤P) :
    ∃ b∈J,FQ M (a+b) := by
  classical
  let A := {P∈xm R M | a∈P}
  have hA:A.Finite :=(Xx R M).subset fun _ hP=>hP.1
  have hav : ¬ ((J:Set R) ⊆ ⋃ P∈A,(P:Set R)) := by
    intro hall
    obtain ⟨P,hP,hJP⟩ :=
      (J.subset_union_prime_finite hA (f :=id) ⊥ ⊥
        (fun P hP _ _=>(show G5 P M from hP.1).isPrime)).mp hall
    exact h P hP.1 hP.2 hJP
  obtain ⟨b,hb,hbA⟩:=Set.not_subset.mp hav
  have hb' (P:nX R) (hP:P∈xm R M) (haP:a∈P) :
      b∉P:= fun hbP=>hbA (Set.mem_iUnion₂.mpr ⟨P,⟨hP,haP⟩,hbP⟩)
  let bad (P:nX R) := {t:k | a+algebraMap k R t*b∈P}
  have hbad (P:nX R) (hP:P∈xm R M) : (bad P).Finite := by
    apply NZ
    intro s hs t ht
    by_contra hst
    have hp:P.IsPrime :=(show G5 P M from hP).isPrime
    have hd:aU k R (s - t)*b∈P:= by
      rw [sH,sub_mul]
      simpa only [add_sub_add_left_eq_sub] using P.sub_mem hs ht
    have hbP:b∈P:=(hp.mem_or_mem hd).resolve_left fun hz =>
      hp.ne_top (P.eq_top_of_isUnit_mem hz ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hst)).map
        (aU k R)))
    have haP:a∈P:= by
      simpa only [IT] using P.sub_mem hs (P.mul_mem_left (aU k R s) hbP)
    exact hb' P hP haP hbP
  have hfinite :=(Xx R M).biUnion hbad
  obtain ⟨t,ht⟩:=hfinite.exists_notMem
  refine ⟨aU k R t*b,J.mul_mem_left _ hb,?_⟩
  by_contra hreg
  have hh:a+algebraMap k R t*b ∈ ⋃ P∈xm R M,(P:Set R) := by
    rwa [OJ R M]
  obtain ⟨P,hP,hhP⟩:=Set.mem_iUnion₂.mp hh
  exact ht (Set.mem_iUnion₂.mpr ⟨P,hP,hhP⟩)
private abbrev aLV (R:Type u) [lz R] [t4 R] :=
 z8 R (R ⧸ lI R)
omit [zm R] [t4 R] in
private theorem aHM (N M:ModuleCat.{u} R) {a :R}
  (ha :FQ M a) {n:ℕ} (h : ∀ i<n+1,Ef (Ext N M i)) :
  ∀ i<n,Ef (Ext N (z8 R (QuotSMulTop a M)) i) := by
 intro i hi
 have h₀:=AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h i (by omega))
 have h₁:=AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h (i+1) (by omega))
 exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
  (Ext.covariant_sequence_exact₃' N ha.smulShortComplex_shortExact i (i+1) rfl)
  (h₀.eq_zero_of_src _) (h₁.eq_zero_of_tgt _)
include k in
private theorem byD (rs :List R) (M:ModuleCat.{u} R) [pz R M]
    (hm : ∀ a∈rs,a∈lI R)
    (hI:lI R≤(wY rs ⊔ qz R M).radical)
    (hext : ∀ i< rs.length,Ef (Ext (aLV R) M i)) :
    IsWeaklyRegular M rs := by
  induction rs generalizing M with
  | nil=>exact IsWeaklyRegular.nil R M
  | cons a rs ih =>
    have hHom:Ef (aLV R →ₗ[R] M) :=
      (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton_congr.mp
        (hext 0 (by simp))
    obtain ⟨r,hr,hreg⟩:=IsSMulRegular.subsingleton_linearMap_iff.mp hHom
    have hAnn:qz R (aLV R)=lI R :=
      XJ
    have hrm:r∈lI R:=hAnn ▸ hr
    let J:=wY rs
    have hJm:J≤ lI R:=Ideal.span_le.mpr
      (fun z hz=>hm z (Kz _ hz))
    obtain ⟨b,hb,hab⟩:=buW (k :=k) (M:=M) a J (by
      intro P hP haP hJP
      have hassoc:G5 P M:=hP
      have hprime :=hassoc.isPrime
      have hle :wY (a :: rs) ⊔ qz R M≤P:= by
        rw [Mw]
        exact sup_le (sup_le ((Gj P).mpr haP) hJP)
          (by simpa only [Submodule.annihilator_top] using hassoc.annihilator_le)
      have hrP:=hprime.radical_le_iff.mpr hle (hI hrm)
      have hru:r ∈ ⋃ P∈xm R M,(P:Set R) :=
        Set.mem_iUnion₂.mpr ⟨P,hP,hrP⟩
      rw [OJ R M] at hru
      exact hru hreg)
    let M' := z8 R (QuotSMulTop (a+b) M)
    have habann:a+b∈qz R M' := QuotSMulTop.mem_annihilator M (a+b)
    have hann:qz R M≤qz R M' :=
      (Submodule.mkQ _).annihilator_le_of_surjective (Submodule.mkQ_surjective _)
    have hle :wY (a :: rs) ⊔ qz R M ≤
        J ⊔ qz R M' := by
      rw [Mw]
      refine sup_le (sup_le ((Gj _).mpr ?_) G7)
        (hann.trans X4)
      have hsum:a+b∈J ⊔ qz R M' := XB habann
      have hb' : b∈J ⊔ qz R M' := PD hb
      simpa only [IT] using (J ⊔ qz R M').sub_mem hsum hb'
    have htail:=ih M' (fun z hz=>hm z (Kz _ hz))
      (hI.trans (Ww hle)) (aHM _ M hab hext)
    have hcons :IsWeaklyRegular M ((a+b) :: rs) :=IsWeaklyRegular.cons hab htail
    have happ:IsWeaklyRegular M (rs ++ [a+b]) :=
      Xu hcons
        (show List.Perm ([a+b] ++ rs) (rs ++ [a+b]) from Yc) (by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Ideal.add_mem _ (hm a List.mem_cons_self) (hJm hb)
        · exact hm z (Kz _ hz))
    obtain ⟨hrs,hlast⟩:=(isWeaklyRegular_append_iff M rs [a+b]).mp happ
    let T:pL R M:=J • ⊤
    have hlast' : FQ (M ⧸ T) (a+b) :=(isWeaklyRegular_singleton_iff _ _).mp hlast
    have ha :FQ (M ⧸ T) a := by
      rw [isSMulRegular_quotient_iff_mem_of_smul_mem] at hlast' ⊢
      intro x hx
      apply hlast'
      have hbT:b•x∈T:= by
        apply (Submodule.smul_mono_left ((Gj J).mpr hb) :
          nq {b} • (⊤ : pL R M)≤T)
        rw [Submodule.ideal_span_singleton_smul]
        exact Submodule.smul_mem_pointwise_smul x b ⊤ trivial
      rw [add_smul]
      exact T.add_mem hx hbT
    have hnew :IsWeaklyRegular M (rs ++ [a]) :=
      (isWeaklyRegular_append_iff M rs [a]).mpr
        ⟨hrs,(isWeaklyRegular_singleton_iff _ _).mpr ha⟩
    have hp:List.Perm (a :: rs) (rs ++ [a]) :=
      show List.Perm ([a] ++ rs) (rs ++ [a]) from Yc
    exact Xu hnew hp.symm
      (fun z hz=>hm z (hp.mem_iff.mpr hz))
include k in
theorem bPS (ref rs :List R) (hlen:ref.length=rs.length)
  (hmem : ∀ a∈ref,a∈lI R) (href :IsRegular R ref)
  (hrad: (wY rs).radical=lI R) :
  IsWeaklyRegular R rs := by
 let N :=aLV R
 have hAnn:qz R N=lI R:=XJ
 have hSupp:Module.support R N⊆PrimeSpectrum.zeroLocus (lI R) := by
  rw [Module.support_eq_zeroLocus,hAnn]
 have hlt:lI R•(⊤ : pL R R) < ⊤ := by
  change lI R•(⊤ : nX R) < ⊤
  rw [Ideal.smul_eq_mul,Ideal.mul_top]
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top.lt_top
 have hext:=ModuleCat.subsingleton_ext_of_exists_isRegular _ N hSupp
  (z8 R R) hlt ref hmem href
 exact byD (k :=k) rs (z8 R R)
  (fun a ha=>hrad ▸ (wY rs).le_radical (Dw ha))
  (hrad ▸ Ww G7) (fun i hi=>hext i (hlen ▸ hi))
end Local
end bjD
end
section
namespace gR
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type*} [cy F] [lJ ι] [ox ι]
def weight (x :ι→F) (i:ι) :F :=
 (∏ j∈(vj :nI ι).erase i,(x i - x j))⁻¹
def oX (x :ι→F) (u:ι→F) (j:ℕ) :F :=
 ∑ i,weight x i*u i*x i^j
theorem dl1 (x :ι→F) (hx :mD x)
  (q:F[X]) (hq:q.degree<(lV ι - 1 :ℕ)) :
  ∑ i,weight x i*q.eval (x i)=0:= by
 have hlt:q.degree<(lV ι:ℕ) :=
  hq.trans_le (by exact_mod_cast Nat.sub_le (lV ι) 1)
 have h:=Pk (s :=vj) (v :=x)
  (fun a _ b _ hab=>hx hab) (by simpa using hlt)
 rw [zk,Polynomial.coeff_eq_zero_of_degree_lt hq] at h
 simpa [weight,KA,qy] using h.symm
def QO (x :ι→F) (u v :ι→F) (L t:ℕ) :
    c9 (Fin L) (Fin (t+1)) F[X] :=
  fun i j=>C (oX x u (i.val+j.val)) +
    X*C (oX x v (i.val+j.val))
def mL (x :ι→F) (S:nI ι) :F[X] :=
 ∏ i∈S,(X - C (x i))
theorem S8 (x :ι→F) (S:nI ι) : (mL x S).Monic :=
 Polynomial.monic_prod_of_monic S _ (fun _ _=>monic_X_sub_C _)
theorem ZQ (x :ι→F) (S:nI ι) :
  (mL x S).natDegree=S.card:= by
 rw [mL,Polynomial.natDegree_prod_of_monic S _ (fun _ _=>monic_X_sub_C _)]
 simp
theorem arK (x :ι→F) (S:nI ι) (i:ι) (hi:i∈S) :
  (mL x S).eval (x i)=0:= by
 simp only [mL,eval_prod,eval_sub,eval_X,eval_C]
 exact Finset.prod_eq_zero hi (zc _)
theorem bw8 (E :F[X]) (t:ℕ) (hE :E.natDegree≤t) (a :F) :
  (∑ j:Fin (t+1),E.coeff j.val*a^j.val)=E.eval a := by
 rw [Vl (fun j=>E.coeff j*a^j) (t+1)]
 exact (S1 (by omega) a).symm
theorem cUx (x :ι→F) (hx :mD x)
    (u v :ι→F) (γ:F) (k L t:ℕ) (hsize :k+L+t≤lV ι)
    (P E :F[X]) (hP:P.degree<k) (hE :E.natDegree≤t)
    (hagree : ∀ a,E.eval (x a)*(u a+γ*v a)=E.eval (x a)*P.eval (x a)) :
    (fun i j=>((QO x u v L t) i j).eval γ) *ᵥ
      (fun j:Fin (t+1)=>E.coeff j.val)=0:= by
  funext i
  simp only [th,sS ,QO,eval_add,vh,eval_C,eval_X,
    u9]
  change (∑ j:Fin (t+1),
    ((oX x u (i.val+j.val))+γ*oX x v (i.val+j.val)) *
      E.coeff j.val)=0
  have hsum: (∑ j:Fin (t+1),
      ((oX x u (i.val+j.val))+γ*oX x v (i.val+j.val)) *
        E.coeff j.val) =
      ∑ a,weight x a*(E.eval (x a)*(u a+γ*v a))*x a^i.val := by
    simp only [oX,sI,← VO,yL]
    rw [zS]
    apply pC rfl
    intro a _
    rw [← bw8 E t hE (x a)]
    simp only [yL,sI,vG]
    apply pC rfl
    intro j _
    ring
  rw [hsum]
  simp_rw [hagree]
  have hq: (E*P*X ^i.val).degree<(↑(lV ι - 1) :vZ ℕ) := by
    by_cases hp0:P=0
    · simp [hp0]
    have hpn:P.natDegree<k :=(Mz hp0).mpr hP
    have hn: (E*P*X ^i.val).natDegree≤t+P.natDegree+i.val := by
      calc
        _≤(E*P).natDegree+(X ^i.val :F[X]).natDegree :=FR
        _≤(E.natDegree+P.natDegree)+i.val := by
          simpa using WD (FR (p:=E) (q:=P)) i.val
        _≤t+P.natDegree+i.val := by omega
    have hb: (E*P*X ^i.val).natDegree<lV ι - 1 := by
      have :=i.isLt
      omega
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hb)
  have hz :=dl1 x hx (E*P*X ^i.val) hq
  simpa only [vh,eval_pow,eval_X,Ar] using hz
variable (p:ℕ) [t3 F p]
theorem gL9 (x :ι→F) (hfixed : ∀ i,x i^p=x i) (i:ι) :
  zE F p (weight x i)=weight x i:= by
 simp only [weight,map_inv₀,map_prod,sH,Gr,hfixed]
theorem bxn (x :ι→F) (hfixed : ∀ i,x i^p=x i)
  (u:ι→F) (j:ℕ) :
  oX x (fun i=>u i^p) j=(oX x u j)^p:= by
 change (∑ i,weight x i*u i^p*x i^j) =
  zE F p (∑ i,weight x i*u i*x i^j)
 rw [oY]
 apply pC rfl
 intro i _
 rw [oD,oD,map_pow,gL9 p x hfixed i]
 simp only [Gr,hfixed]
theorem b8d {B:Type*} [cy B] (φ:B →+* F) (x :ι→B) (S:nI ι) :
  (mL x S).map φ=mL (fun i=>φ (x i)) S:= by
 simp [mL,VH]
theorem ex5 (x :ι→F) (hfixed : ∀ i,x i^p=x i)
  (S:nI ι) : (mL x S).map (zE F p)=mL x S:= by
 simp [mL,VH,hfixed,Gr]
def AI (x :ι→F) (u v :ι→F) (L t:ℕ) :
    c9 (Fin 2×Fin L) (Fin (t+1)) F[X] :=
  fun i j=>if i.1=0 then QO x u v L t i.2 j else
    C ((oX x u (i.2.val+j.val))^p) +
      X ^p*C ((oX x v (i.2.val+j.val))^p)
theorem b8c (x :ι→F) (hx :mD x)
   (hfixed : ∀ i,x i^p=x i) (u v :ι→F) (γ:F)
   (k L t:ℕ) (hsize :k+L+t≤lV ι)
   (P:F[X]) (hP:P.degree<k) (S:nI ι) (hS:S.card≤t)
   (hagree : ∀ a,a∉S→u a+γ*v a=P.eval (x a)) :
   (fun i j=>((AI p x u v L t) i j).eval γ) *ᵥ
     (fun j:Fin (t+1)=>(mL x S).coeff j.val)=0:= by
 have hE : (mL x S).natDegree≤t:=(ZQ x S).trans_le hS
 have ha : ∀ a,(mL x S).eval (x a)*(u a+γ*v a) =
     (mL x S).eval (x a)*P.eval (x a) := by
   intro a
   by_cases h:a∈S
   · simp [arK x S a h]
   · rw [hagree a h]
 have hfirst:=cUx x hx u v γ k L t hsize P (mL x S) hP hE ha
 have hcoeff : ∀ j,zE F p ((mL x S).coeff j)=(mL x S).coeff j:= by
   intro j
   have hc:=oj (fun q:F[X]=>q.coeff j) (ex5 p x hfixed S)
   simpa only [Polynomial.coeff_map] using hc
 funext i
 rcases i with ⟨b,i⟩
 fin_cases b
 · simpa [AI,th,sS ,QO] using oy hfirst i
 · have hh:=oj (zE F p) (oy hfirst i)
   simp only [th,sS ,QO,eval_add,vh,eval_C,eval_X,
     u9,oY ,oD,Aa ,p5 ,hcoeff] at hh
   simpa [AI,th,sS ,Gr,qy] using hh
end
end gR
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F:Type*} [cy F]
local instance gPG (P:Prop) :Decidable P:=KI P
theorem bsR {c:Type*} [lJ c] [ox c]
   (M:c9 c c F[X]) (d:c→ℕ) (hM : ∀ i j,(M i j).natDegree≤d i) :
   M.det.natDegree ≤ ∑ i,d i:= by
 rw [Matrix.det_apply]
 apply Ea
 intro σ _
 have hs : (Equiv.Perm.sign σ • ∏ i,M (σ i) i).natDegree =
     (∏ i,M (σ i) i).natDegree := by
   rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
   · rw [h,one_smul]
   · rw [h,Units.neg_smul,one_smul,natDegree_neg]
 rw [hs]
 calc
   _ ≤ ∑ i,(M (σ i) i).natDegree :=Polynomial.natDegree_prod_le _ _
   _ ≤ ∑ i,d (σ i) :=G9 (fun i _=>hM (σ i) i)
   _ = ∑ i,d i:=Equiv.sum_comp σ d
variable {ι:Type*} [lJ ι] [ox ι]
theorem bHF (x :ι→F) (u v :ι→F) (L t:ℕ)
  (i:Fin L) (j:Fin (t+1)) : (QO x u v L t i j).natDegree≤1 := by
 unfold QO
 compute_degree
theorem a8L (p:ℕ) [t3 F p] (x :ι→F) (u v :ι→F)
   (L t:ℕ) (i:Fin 2×Fin L) (j:Fin (t+1)) :
   (AI p x u v L t i j).natDegree≤ if i.1=0 then 1 else p:= by
 unfold AI
 split_ifs with h
 · exact bHF x u v L t i.2 j
 · compute_degree
end
end gR
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.apT
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {R c:Type*} [lz R] [lJ c] [ox c]
def aTh (A:c9 c c R) (b:c→R) :c9 c (vH c) R :=
 fun i j=> match j with | none=>b i | some j=>A i j
def vector (A:c9 c c R) (b:c→R) :vH c→R :=
 fun j=> match j with | none=>A.det | some j => -(A.cramer b j)
theorem c0W (A:c9 c c R) (b:c→R) (E :vH c→R) :
  (aTh A b).mulVec E=A.mulVec (fun j=>E (some j))+E none•b:= by
 funext i
 simp only [th,sS ,Fintype.sum_option,aTh,
  Pi.add_apply,qx ,pQ]
 ring
theorem bA5 (A:c9 c c R) (b:c→R) :
  (aTh A b).mulVec (vector A b)=0:= by
 rw [c0W]
 change A.mulVec (-(A.cramer b))+A.det•b=0
 rw [Matrix.mulVec_neg,WK]
 exact neg_add_cancel _
theorem ezl {S:Type*} [lz S] (φ:R →+* S)
   (A:c9 c c R) (b:c→R) (j:vH c) :
   vector (A.map φ) (φ ∘ b) j=φ (vector A b j) := by
 cases j with
 | none=>exact (φ.map_det A).symm
 | some j =>
   change -((A.map φ).cramer (φ ∘ b) j)=φ (-(A.cramer b j))
   rw [map_neg,yJ,yJ]
   congr 1
   rw [← Qw]
   exact (φ.map_det _).symm
theorem dRw (A:c9 c c R) (v :c→R) :
  A.cramer (A.mulVec v)=A.det•v := by
 rw [Matrix.cramer_eq_adjugate_mulVec,UP ,
  Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec]
theorem cZn {S:Type*} [lz S] (φ:R →+* S)
  (A:c9 c c R) (b:c→R) (j:c) :
  (A.map φ).cramer (φ ∘ b) j=φ (A.cramer b j) := by
 rw [yJ,yJ,← Qw]
 exact (φ.map_det _).symm
section Field
variable {K:Type*} [cy K]
theorem etU (A:c9 c c K) (b:c→K) (hA:A.det≠0)
   (E :vH c→K) (hE : (aTh A b).mulVec E=0) (hfree :E none=0) :
   E=0:= by
 rw [c0W,hfree,zero_smul,wB] at hE
 have hz :=Matrix.eq_zero_of_mulVec_eq_zero hA hE
 funext j
 cases j with
 | none=>exact hfree
 | some j=>exact congrFun hz j
theorem etS (A:c9 c c K) (b:c→K) (hA:A.det≠0)
  (E :vH c→K) (hE : (aTh A b).mulVec E=0) :
  E=(E none/A.det)•vector A b:= by
 have hz : (aTh A b).mulVec (E-(E none/A.det)•vector A b)=0:= by
  rw [LQ,Lf ,hE,bA5,smul_zero,sub_zero]
 have hfree : (E-(E none/A.det)•vector A b) none=0:= by
  change E none-(E none/A.det)*A.det=0
  rw [div_mul_cancel₀ _ hA,zc]
 have heq :=etU A b hA _ hz hfree
 exact sub_eq_zero.mp heq
variable {row:Type*}
end Field
section Polynomial
variable {F:Type*} [cy F]
theorem bPI (A:c9 c c F[X]) (b:c→F[X])
   (d:c→ℕ) (hA : ∀ i j,(A i j).natDegree≤d i)
   (hb : ∀ i,(b i).natDegree≤d i) (j:vH c) :
   (vector A b j).natDegree ≤ ∑ i,d i:= by
 cases j with
 | none=>exact gR.bsR A d hA
 | some j =>
   change (-(A.cramer b j)).natDegree≤_
   rw [natDegree_neg,yJ]
   apply gR.bsR _ d
   intro i k
   by_cases hkj:k=j
   · subst k
     simpa only [Vz] using hb i
   · simpa only [Rm hkj] using hA i k
end Polynomial
end
end gR.apT
end
section
namespace gR.aRz
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {K:Type*} [cy K]
theorem bFA {row:Type*} [lJ row] {m:ℕ} (A:c9 row (Fin m) K)
   (hker : ∀ v,A.mulVec v=0→v=0) :
   ∃ rows :Fin m→ row,(A.submatrix rows id).det≠0:= by
 have hk :oK A.mulVecLin = ⊥ := by
   rw [LinearMap.ker_eq_bot']
   intro v hv
   exact hker v (by simpa only [Matrix.mulVecLin_apply] using hv)
 have hr :A.rank=m:= by
   have h:=t6 A.mulVecLin
   rw [hk,finrank_bot,wB,Module.finrank_fin_fun] at h
   exact h
 rw [Gi] at hr
 obtain ⟨κ,a,ha,hsp,hli⟩:=Pf K A.row
 have :Finite κ:=Un a ha
 have :lJ κ:=Fintype.ofFinite κ
 have hc:lV κ=m:= by
   rw [← G1 hli,hsp,hr]
 let e :Fin m ≃ κ:=(G2 hc).symm
 refine ⟨a ∘ e,?_⟩
 have hli' : vw K (A.submatrix (a ∘ e) id).row:= by
   have heq : (A.submatrix (a ∘ e) id).row=(A.row ∘ a) ∘ e := by
     funext i j
     rfl
   rw [heq]
   exact hli.comp e e.injective
 exact ((Matrix.isUnit_iff_isUnit_det _).mp
   (Matrix.linearIndependent_rows_iff_isUnit.mp hli')).ne_zero
theorem cWG {row col:Type*} [lJ col]
  (M:c9 row col K) (hnull:oz K (oK M.mulVecLin)=1)
  (E :col→K) (hE :E≠0) (hME :M.mulVec E=0) :
  ∀ v,M.mulVec v=0 → ∃ a :K,v=a•E := by
 have hspan:K ∙ E=oK M.mulVecLin:= by
  apply Xo
  · apply Submodule.span_le.mpr
    intro v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact hME
  · rw [TI hE,hnull]
 intro v hv
 have hmem:v∈K ∙ E := by rw [hspan]; exact hv
 obtain ⟨a,ha⟩:=Submodule.mem_span_singleton.mp hmem
 exact ⟨a,ha.symm⟩
theorem eFB {row col:Type*} [lJ col]
  (M:c9 row col K) (hr :M.rank+1=lV col) :
  oz K (oK M.mulVecLin)=1 := by
 have h:=t6 M.mulVecLin
 rw [zd] at h
 change M.rank+_ = _ at h
 omega
end
end gR.aRz
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.zQ
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col:Type*} [cy F] [cy K] [lJ col] [ox col]
structure RowBasis (φ:F[X] →+* K) (M:c9 row col F[X]) (r :ℕ) where
 rows :Fin r→ row
 cols :Fin r→ col
 minor_ne : (M.submatrix rows cols).det≠0
 spans : ∀ i,∃ a :Fin r→K,∀ j,
  φ (M i j) = ∑ q,a q*φ (M (rows q) j)
def pivot {r :ℕ} {φ:F[X] →+* K} {M:c9 row col F[X]}
    (B:RowBasis φ M r) :c9 (Fin r) (Fin r) F[X] :=M.submatrix B.rows B.cols
def bvf {r :ℕ} {φ:F[X] →+* K} {M:c9 row col F[X]}
    (B:RowBasis φ M r) (i:row) :Fin r→F[X] :=
  (pivot B).transpose.cramer (fun q=>M i (B.cols q))
theorem fZv (φ:F[X] →+* K) (hφ:mD φ)
   (M:c9 row col F[X]) (r :ℕ) (B:RowBasis φ M r) (i:row) (j:col) :
   (pivot B).det*M i j = ∑ q,bvf B i q*M (B.rows q) j:= by
 obtain ⟨a,ha⟩:=B.spans i
 let A:=(pivot B).map φ
 have hsolve :A.transpose.mulVec a=fun q=>φ (M i (B.cols q)) := by
   funext q
   change (∑ l,φ (M (B.rows l) (B.cols q))*a l)= _
   simpa only [qy] using (ha (B.cols q)).symm
 have hc : ∀ q,φ (bvf B i q)=φ (pivot B).det*a q:= by
   intro q
   have hm:=apT.cZn φ (pivot B).transpose
     (fun q=>M i (B.cols q)) q
   have hcr :=oy (apT.dRw A.transpose a) q
   rw [hsolve,JK] at hcr
   have hd:=φ.map_det (pivot B)
   rw [yl] at hd
   change φ (bvf B i q)= _
   calc
     _=((pivot B).transpose.map φ).cramer (fun q=>φ (M i (B.cols q))) q:=hm.symm
     _=A.det*a q:=hcr
     _ = _:= by rw [← hd]
 apply hφ
 rw [oD,oY]
 simp only [oD,hc]
 rw [ha j,sI]
 apply pC rfl
 intro q hq
 ring
theorem etN (φ:F[X] →+* K) (hφ:mD φ)
    (M:c9 row col F[X]) (r :ℕ) (B:RowBasis φ M r)
    (γ:F) (hγ: (pivot B).det.eval γ≠0) (v :col→F) :
    (M.map (oq γ)).mulVec v=0 ↔
      ((M.submatrix B.rows id).map (oq γ)).mulVec v=0:= by
  constructor
  · intro h
    funext i
    exact oy h (B.rows i)
  · intro h
    funext i
    apply (mul_eq_zero.mp (show (pivot B).det.eval γ *
      ((M.map (oq γ)).mulVec v) i=0 from ?_)).resolve_left hγ
    have heval : ∀ j,(pivot B).det.eval γ*(M i j).eval γ =
        ∑ q,(bvf B i q).eval γ*(M (B.rows q) j).eval γ:= by
      intro j
      have hrel :=oj (oq γ) (fZv φ hφ M r B i j)
      simp only [oD,oY] at hrel
      exact hrel
    change (pivot B).det.eval γ*(∑ j,(M i j).eval γ*v j)=0
    rw [sI]
    simp_rw [← Ar,heval,yL]
    rw [zS]
    apply S2
    intro q hq
    have hz :=oy h q
    change (∑ j,(M (B.rows q) j).eval γ*v j)=0 at hz
    calc
      _=(bvf B i q).eval γ*(∑ j,(M (B.rows q) j).eval γ*v j) := by
        rw [sI]
        apply pC rfl
        intro j hj
        ring
      _=0:= by rw [hz,mul_zero]
theorem a3O [lJ row] (φ:F[X] →+* K) (M:c9 row col F[X])
    (r :ℕ) (hr : (M.map φ).rank=r) :Nonempty (RowBasis φ M r) := by
  classical
  let N :=M.map φ
  have hr' : oz K (pU K (oZ N.row))=r := by
    rw [← Gi]
    exact hr
  obtain ⟨κ,a,ha,hsp,hli⟩:=Pf K N.row
  have :Finite κ:=Un a ha
  have :lJ κ:=Fintype.ofFinite κ
  have hc:lV κ=r := by
    rw [← G1 hli,hsp,hr']
  let e :Fin r ≃ κ:=(G2 hc).symm
  let rows :=a ∘ e
  have hli' : vw K (fun q:Fin r=>N.row (rows q)) :=
    hli.comp e e.injective
  have hspace :pU K (oZ (fun q:Fin r=>N.row (rows q))) =
      pU K (oZ N.row) := by
    rw [← hsp]
    congr 1
    apply Set.Subset.antisymm
    · rintro _ ⟨q,rfl⟩
      exact ⟨e q,rfl⟩
    · rintro _ ⟨q,rfl⟩
      obtain ⟨l,hl⟩:=e.surjective q
      exact ⟨l,by simp only [rows,Function.comp_apply,hl]⟩
  let T:=N.submatrix rows id
  obtain ⟨cols,hcols⟩:=aRz.bFA T.transpose (by
    intro v hv
    have hsum: (∑ q,v q•N.row (rows q))=0:= by
      funext j
      have h:=oy hv j
      change (∑ q,N (rows q) j*v q)=0 at h
      simpa only [yQ,qx ,pQ,qy ,
        EP ,u9] using h
    funext q
    exact Fintype.linearIndependent_iff.mp hli' v hsum q)
  have hminorK: (N.submatrix rows cols).det≠0:= by
    have heq :T.transpose.submatrix cols id=(N.submatrix rows cols).transpose := by
      ext i j
      rfl
    rw [heq,JK] at hcols
    exact hcols
  refine ⟨⟨rows,cols,?_,?_⟩⟩
  · intro hzero
    apply hminorK
    have hmap :=φ.map_det (M.submatrix rows cols)
    rw [yl,hzero,p5] at hmap
    exact hmap.symm
  · intro i
    have hmem:N.row i∈pU K (oZ (fun q:Fin r=>N.row (rows q))) := by
      rw [hspace]
      exact Dv (EK i)
    obtain ⟨v,hv⟩:=(NW K).mp hmem
    refine ⟨v,?_⟩
    intro j
    have h:=oy hv j
    simpa only [N,EP ,Du,yQ,
      qx ,pQ] using h.symm
theorem buH [lJ row] (φ:F[X] →+* K) (hφ:mD φ)
  (M:c9 row col F[X]) (r :ℕ) (B:RowBasis φ M r)
  (γ:F) (hγ: (pivot B).det.eval γ≠0) :
  (M.map (oq γ)).rank=r := by
 let N :=M.map (oq γ)
 let T:=(M.submatrix B.rows id).map (oq γ)
 change N.rank=r
 have hminor : (N.submatrix B.rows B.cols).det≠0:= by
  have hmap :=(oq γ).map_det (pivot B)
  rw [yl] at hmap
  intro h0
  apply hγ
  have heq :N.submatrix B.rows B.cols=(pivot B).map (oq γ) :=rfl
  rw [heq,← hmap] at h0
  exact h0
 have hTrank :T.rank=r := by
  have hminorRank :=Matrix.rank_of_det_ne_zero hminor
  have hlo:=Matrix.rank_submatrix_le T id B.cols
  have hhi:=Matrix.rank_le_card_height T
  change (N.submatrix B.rows B.cols).rank≤T.rank at hlo
  rw [hminorRank,t8] at hlo
  rw [t8] at hhi
  omega
 have hker :oK N.mulVecLin=oK T.mulVecLin:= by
  ext v
  exact etN φ hφ M r B γ hγ v
 have hN :=t6 N.mulVecLin
 have hT:=t6 T.mulVecLin
 change N.rank+Module.finrank F (oK N.mulVecLin)= _ at hN
 change T.rank+Module.finrank F (oK T.mulVecLin)= _ at hT
 rw [hker] at hN
 rw [hTrank] at hT
 omega
theorem dO8 [lJ row] (φ:F[X] →+* K) (hφ:mD φ)
   (M:c9 row col F[X]) (r :ℕ) (B:RowBasis φ M r)
   (V:pL F (col→F)) (hV:oz F V=lV col - r)
   (hsub : ∀ γ v,v∈V→(M.map (oq γ)).mulVec v=0)
   (γ:F) (hγ: (pivot B).det.eval γ≠0) :
   oK (M.map (oq γ)).mulVecLin=V:= by
 have hrank :=buH φ hφ M r B γ hγ
 have hn:=t6 (M.map (oq γ)).mulVecLin
 change (M.map (oq γ)).rank+_ = _ at hn
 rw [hrank,zd] at hn
 have hdim:oz F (oK (M.map (oq γ)).mulVecLin)=lV col - r := by omega
 symm
 apply Xo
 · intro v hv
   exact hsub γ v hv
 · rw [hV,hdim]
theorem aVV (φ:F[X] →+* K) (M:c9 row col F[X]) (r :ℕ)
  (B:RowBasis φ M r) (d:row→ℕ) (hdeg : ∀ i j,(M i j).natDegree≤d i) :
  (pivot B).det.natDegree ≤ ∑ q,d (B.rows q) := by
 exact gR.bsR _ _
  (fun i j=>hdeg (B.rows i) (B.cols j))
end
end gR.zQ
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.asZ
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
section Ring
variable {R row col:Type*} [lz R] [lJ col] [ox col]
variable {r :ℕ}
def inclusion (cols :Fin r→ col) :c9 col (Fin r) R :=
 fun j q=>(v8 (cols q) (1 :R) :col→R) j
theorem gpq (M:c9 row col R) (rows :Fin r→ row)
  (cols :Fin r→ col) :
  M.submatrix rows id*inclusion cols=M.submatrix rows cols := by
 ext i q
 change (M.submatrix rows id).mulVec (v8 (cols q) 1) i= _
 rw [WY]
 rfl
def bnx (M:c9 row col R) (rows :Fin r→ row) (cols :Fin r→ col) :
    (col→R) →ₗ[R] (col→R) :=
  (M.submatrix rows cols).det•LO -
    (inclusion cols).mulVecLin.comp
      ((M.submatrix rows cols).cramer.comp (M.submatrix rows id).mulVecLin)
def aJb (M:c9 row col R) (rows :Fin r→ row) (cols :Fin r→ col)
    (j:col) :col→R:=bnx M rows cols (v8 j 1)
theorem bX7 (M:c9 row col R) (rows :Fin r→ row)
    (cols :Fin r→ col) (v :col→R) :
    bnx M rows cols v=(M.submatrix rows cols).det•v -
      (inclusion cols).mulVec ((M.submatrix rows cols).cramer
        ((M.submatrix rows id).mulVec v)) :=rfl
theorem ceF (M:c9 row col R) (rows :Fin r→ row)
    (cols :Fin r→ col) (j:col) :
    aJb M rows cols j=(M.submatrix rows cols).det•v8 j 1 -
      (inclusion cols).mulVec ((M.submatrix rows cols).cramer
        (fun q=>M (rows q) j)) := by
  rw [aJb,bX7,WY]
  rfl
theorem gpn (M:c9 row col R) (rows :Fin r→ row)
  (cols :Fin r→ col) (v :col→R) :
  (M.submatrix rows id).mulVec (bnx M rows cols v)=0:= by
 rw [bX7,LQ,Lf ,
  UP ,gpq,WK,zc]
theorem gpm (M:c9 row col R) (rows :Fin r→ row)
  (cols :Fin r→ col) (j:col) :
  (M.submatrix rows id).mulVec (aJb M rows cols j)=0 :=
 gpn M rows cols _
theorem dNa (M:c9 row col R) (rows :Fin r→ row)
  (cols :Fin r→ col) (v :col→R)
  (hv : (M.submatrix rows id).mulVec v=0) :
  bnx M rows cols v=(M.submatrix rows cols).det•v := by
 rw [bX7,hv,p5 ,Matrix.mulVec_zero,sub_zero]
theorem gxa (M:c9 row col R) (rows :Fin r→ row)
  (cols :Fin r→ col) (v :col→R) :
  ∑ j,v j•aJb M rows cols j=bnx M rows cols v := by
 simp only [aJb,← map_smul,← oY]
 congr 1
 ext j
 simp [G6]
theorem cZy {S:Type*} [lz S] (ψ:R →+* S)
   (M:c9 row col R) (rows :Fin r→ row) (cols :Fin r→ col) (j c:col) :
   aJb (M.map ψ) rows cols j c=ψ (aJb M rows cols j c) := by
 have hsub: (M.map ψ).submatrix rows cols=(M.submatrix rows cols).map ψ:=rfl
 have hd:=ψ.map_det (M.submatrix rows cols)
 rw [yl] at hd
 have hc: ((M.submatrix rows cols).map ψ).cramer
     (fun q=>ψ (M (rows q) j)) =
     fun q=>ψ ((M.submatrix rows cols).cramer (fun q=>M (rows q) j) q) := by
   funext q
   exact apT.cZn ψ _ _ q
 have hs : ∀ a :col,ψ ((v8 a (1 :R) :col→R) c) =
     (v8 a (1 :S) :col→S) c:= by
   intro a
   by_cases h:a=c <;> simp [h]
 simp only [ceF,LP ,qx ,pQ]
 rw [hsub,← hd,sH,oD,hs]
 congr 1
 change (∑ q,(v8 (cols q) (1 :S) :col→S) c *
     ((M.submatrix rows cols).map ψ).cramer (fun q=>ψ (M (rows q) j)) q)= _
 rw [hc]
 simp only [th,sS ,inclusion,oY ,oD]
 apply pC rfl
 intro q hq
 rw [hs]
end Ring
section Field
variable {K row col:Type*} [cy K] [lJ col] [ox col]
variable {r :ℕ}
theorem fT5 (M:c9 row col K) (rows :Fin r→ row) (cols :Fin r→ col)
   (hdet: (M.submatrix rows cols).det≠0) (v :col→K)
   (hv : (M.submatrix rows id).mulVec v=0) :
   v = ∑ j,(v j/(M.submatrix rows cols).det)•aJb M rows cols j:= by
 have heq :=gxa M rows cols v
 rw [dNa _ _ _ _ hv] at heq
 calc
   v=(M.submatrix rows cols).det⁻¹•((M.submatrix rows cols).det•v) := by
     rw [smul_smul,G8 hdet,one_smul]
   _ = _:= by
     rw [← heq,Finset.smul_sum]
     apply pC rfl
     intro j hj
     rw [smul_smul,KA,qy]
end Field
section Polynomial
variable {F K row col:Type*} [cy F] [cy K] [lJ col] [ox col]
variable {φ:F[X] →+* K} {M:c9 row col F[X]} {r :ℕ}
def vector (B:zQ.RowBasis φ M r) (j:col) :col→F[X] :=
 aJb M B.rows B.cols j
theorem cTO (B:zQ.RowBasis φ M r) (v :col→K) :
    (M.map φ).mulVec v=0↔((M.submatrix B.rows id).map φ).mulVec v=0:= by
  constructor
  · intro h
    funext q
    exact oy h (B.rows q)
  · intro h
    funext i
    obtain ⟨a,ha⟩:=B.spans i
    change (∑ j,φ (M i j)*v j)=0
    simp_rw [ha,yL]
    rw [zS]
    apply S2
    intro q hq
    have hz :=oy h q
    change (∑ j,φ (M (B.rows q) j)*v j)=0 at hz
    calc
      _=a q*(∑ j,φ (M (B.rows q) j)*v j) := by
        rw [sI]
        apply pC rfl
        intro j hj
        ring
      _=0:= by rw [hz,mul_zero]
theorem bA5 (B:zQ.RowBasis φ M r) (hφ:mD φ)
  (j:col) :M.mulVec (vector B j)=0:= by
 have hsel:=gpm (M.map φ) B.rows B.cols j
 have hfull:=(cTO B _).mpr hsel
 funext i
 apply hφ
 have h:=oy hfull i
 simpa only [vector,th,sS ,oY ,oD,p5 ,
  Du,cZy,u9] using h
theorem ef9 (B:zQ.RowBasis φ M r) (hφ:mD φ)
   (v :col→K) (hv : (M.map φ).mulVec v=0) :
   v = ∑ j,(v j/φ (zQ.pivot B).det) •
     (fun c=>φ (vector B j c)) := by
 have hd:=φ.map_det (zQ.pivot B)
 rw [yl] at hd
 have hd' : φ (zQ.pivot B).det =
     ((M.map φ).submatrix B.rows B.cols).det:=hd
 have hdet: ((M.map φ).submatrix B.rows B.cols).det≠0:= by
   rw [← hd']
   exact fun h=>B.minor_ne (hφ (h.trans (p5 φ).symm))
 have hsel:=(cTO B v).mp hv
 have heq :=fT5 (M.map φ) B.rows B.cols hdet v hsel
 have hmap : ∀ j,aJb (M.map φ) B.rows B.cols j =
     fun c=>φ (vector B j c) := fun j=>funext (cZy φ M B.rows B.cols j)
 simpa only [← hd',hmap] using heq
theorem bPI (B:zQ.RowBasis φ M r)
    (d:row→ℕ) (hdeg : ∀ i j,(M i j).natDegree≤d i) (j c:col) :
    (vector B j c).natDegree ≤ ∑ q,d (B.rows q) := by
  classical
  rw [vector,ceF]
  simp only [LP ,qx ,pQ]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · by_cases hj:j=c
    · subst c
      simpa only [qx ,pQ,Pv,mul_one,
        zQ.pivot] using
        zQ.aVV φ M r B d hdeg
    · simp [qx ,G6,hj]
  · change (∑ q,inclusion B.cols c q *
      (M.submatrix B.rows B.cols).cramer (fun q=>M (B.rows q) j) q).natDegree≤_
    apply Ea
    intro q hq
    by_cases hq:B.cols q=c
    · simp only [inclusion,hq,Pv,one_mul,yJ]
      apply gR.bsR _ (fun q=>d (B.rows q))
      intro i k
      by_cases hk :k=q
      · subst k
        simpa only [Vz] using hdeg (B.rows i) j
      · simpa only [Rm hk,NI] using
          hdeg (B.rows i) (B.cols k)
    · simp [inclusion,G6,hq]
end Polynomial
end
end gR.asZ
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.zQ
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col:Type*} [cy F] [cy K] [lJ col] [ox col]
variable {φ:F[X] →+* K} {M:c9 row col F[X]} {r :ℕ}
theorem ghA (B:RowBasis φ M r) :mD B.rows := by
 intro i j hij
 by_contra hne
 apply B.minor_ne
 apply Matrix.det_zero_of_row_eq hne
 funext k
 simp only [NI,hij]
end
end gR.zQ
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.zQ
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col:Type*} [cy F] [cy K]
 [lJ row] [lJ col] [ox col]
theorem d4M (φ:F[X] →+* K) (M:c9 row col F[X])
    (r :ℕ) (hr : (M.map φ).rank=r) (S:Set row)
    (hS:Il K (M.map φ).row S) :
    ∃ B:RowBasis φ M r,S⊆oZ B.rows := by
  classical
  let N :=M.map φ
  let T:=hS.extend (Df S)
  have hST:S⊆T:=hS.subset_extend (Df S)
  have hli:vw K (fun i:T=>N.row i.val) :=
    (hS.linearIndepOn_extend (Df S)).linearIndependent_restrict
  have hspace :pU K (oZ (fun i:T=>N.row i.val)) =
      pU K (oZ N.row) := by
    have heq :=hS.span_image_extend_eq_span_image (Df S)
    have hl:oZ (fun i:T=>N.row i.val)=N.row '' T:= by
      ext v
      constructor
      · rintro ⟨i,rfl⟩
        exact ⟨i.val,i.property,rfl⟩
      · rintro ⟨i,hi,rfl⟩
        exact ⟨⟨i,hi⟩,rfl⟩
    rw [hl]
    simpa only [Set.image_univ] using heq
  have hcard:lV T=r := by
    rw [← G1 hli,hspace,← Gi]
    exact hr
  let e :Fin r ≃ T:=(G2 hcard).symm
  let rows :Fin r→ row:= fun q=>(e q).val
  have hli' : vw K (fun q:Fin r=>N.row (rows q)) :=
    hli.comp e e.injective
  let A:=N.submatrix rows id
  obtain ⟨cols,hcols⟩:=aRz.bFA A.transpose (by
    intro v hv
    have hsum: (∑ q,v q•N.row (rows q))=0:= by
      funext j
      have h:=oy hv j
      change (∑ q,N (rows q) j*v q)=0 at h
      simpa only [yQ,qx ,pQ,qy ,
        EP ,u9] using h
    funext q
    exact Fintype.linearIndependent_iff.mp hli' v hsum q)
  have hminorK: (N.submatrix rows cols).det≠0:= by
    have heq :A.transpose.submatrix cols id=(N.submatrix rows cols).transpose := by
      funext i j
      rfl
    rw [heq,JK] at hcols
    exact hcols
  have hminor : (M.submatrix rows cols).det≠0:= by
    intro hzero
    apply hminorK
    have hmap :=φ.map_det (M.submatrix rows cols)
    rw [yl,hzero,p5] at hmap
    exact hmap.symm
  have hspace' : pU K (oZ (fun q:Fin r=>N.row (rows q))) =
      pU K (oZ N.row) := by
    rw [← hspace]
    congr 1
    ext v
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨e q,rfl⟩
    · rintro ⟨q,rfl⟩
      obtain ⟨l,hl⟩:=e.surjective q
      exact ⟨l,by simp only [rows,hl]⟩
  refine ⟨⟨rows,cols,hminor,?_⟩,?_⟩
  · intro i
    have hm:N.row i∈pU K (oZ (fun q:Fin r=>N.row (rows q))) := by
      rw [hspace']
      exact Dv (EK i)
    obtain ⟨a,ha⟩:=(NW K).mp hm
    refine ⟨a,?_⟩
    intro j
    have h:=oy ha j
    simpa only [N,EP ,Du,yQ,
      qx ,pQ] using h.symm
  · intro i hi
    obtain ⟨q,hq⟩:=e.surjective ⟨i,hST hi⟩
    exact ⟨q,oj Av hq⟩
end
end gR.zQ
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.zQ
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col:Type*} [cy F] [cy K]
 [lJ row] [ox row] [lJ col] [ox col]
variable {φ:F[X] →+* K} {M:c9 row col F[X]} {r :ℕ}
theorem gps (B:RowBasis φ M r) (S:nI row)
   (hS: (S:Set row)⊆oZ B.rows) (p:ℕ) :
   (∑ q,if B.rows q∈S then 1 else p)=S.card+p*(r - S.card) := by
 classical
 have hc: (Finset.univ.filter (fun q=>B.rows q∈S)).card=S.card:= by
   apply Finset.card_bij (fun q _=>B.rows q)
   · intro q hq
     exact (Finset.mem_filter.mp hq).2
   · intro i hi j hj hij
     exact ghA B hij
   · intro i hi
     obtain ⟨q,hq⟩:=hS hi
     exact ⟨q,by simp [hq,hi],hq⟩
 have hn: (Finset.univ.filter (fun q=>B.rows q∉S)).card=r - S.card:= by
   have hpart:=WW
     (s :=(vj :nI (Fin r))) (fun q=>B.rows q∈S)
   rw [hc,zk,t8] at hpart
   omega
 rw [Finset.sum_ite]
 simp only [GR,pQ,Nat.mul_one,hc,hn]
 simp [Nat.mul_comm]
theorem d4N (φ:F[X] →+* K) (M:c9 row col F[X])
   (r :ℕ) (hr : (M.map φ).rank=r) (S:nI row)
   (hS:Il K (M.map φ).row (S:Set row)) (p:ℕ)
   (hdeg : ∀ i j,(M i j).natDegree≤ if i∈S then 1 else p) :
   ∃ B:RowBasis φ M r,
     (∑ q,if B.rows q∈S then 1 else p)=S.card+p*(r - S.card) ∧
     (pivot B).det.natDegree≤S.card+p*(r - S.card) := by
 obtain ⟨B,hcontains⟩:=d4M φ M r hr (S:Set row) hS
 have heq :=gps B S hcontains p
 refine ⟨B,heq,?_⟩
 rw [← heq]
 exact aVV φ M r B (fun i=>if i∈S then 1 else p) hdeg
end
end gR.zQ
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.zQ
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K col:Type*} [cy F] [cy K] [lJ col] [ox col]
def azJ (L:ℕ) :Fin L→Fin 2×Fin L:= fun i=>(0,i)
def aIK (L:ℕ) :nI (Fin 2×Fin L) :=
 Finset.univ.filter (fun i=>i.1=0)
theorem eHD (L:ℕ) :
   (aIK L:Set (Fin 2×Fin L))=oZ (azJ L) := by
 ext i
 constructor
 · intro hi
   have h0:i.1=0:=(Finset.mem_filter.mp hi).2
   exact ⟨i.2,by ext <;> simp [azJ,h0]⟩
 · rintro ⟨i,rfl⟩
   simp [aIK,azJ]
theorem c2J (L:ℕ) : (aIK L).card=L:= by
 classical
 have heq : (aIK L).card=(vj :nI (Fin L)).card:= by
  apply Finset.card_bij (fun i _=>i.2)
  · intro i hi
    exact u5 _
  · intro i hi j hj hij
    have hi0:=(Finset.mem_filter.mp hi).2
    have hj0:=(Finset.mem_filter.mp hj).2
    exact Prod.ext (hi0.trans hj0.symm) hij
  · intro j hj
    exact ⟨(0,j),by simp [aIK],rfl⟩
 simpa using heq
theorem d4W (φ:F[X] →+* K) (L s p:ℕ)
   (M:c9 (Fin 2×Fin L) col F[X]) (hr : (M.map φ).rank=s)
   (hfirst:vw K (fun i=>(M.map φ).row (azJ L i)))
   (hdeg : ∀ i j,(M i j).natDegree≤ if i.1=0 then 1 else p) :
   ∃ B:RowBasis φ M s,
     (∑ q,if (B.rows q).1=0 then 1 else p)=L+p*(s-L) ∧
     (pivot B).det.natDegree≤L+p*(s-L) := by
 classical
 have hinj:mD (azJ L) := by
   intro i j hij
   exact oj Prod.snd hij
 have hS:Il K (M.map φ).row (aIK L:Set (Fin 2×Fin L)) := by
   rw [eHD]
   exact (linearIndepOn_range_iff hinj _).mpr hfirst
 have hdeg' : ∀ i j,(M i j).natDegree≤ if i∈aIK L then 1 else p:= by
   intro i j
   simpa only [aIK,Ee,u5 ,Eg] using hdeg i j
 obtain ⟨B,hledger,hminor⟩:=d4N φ M s hr (aIK L) hS p hdeg'
 rw [c2J] at hledger hminor
 refine ⟨B,?_,?_⟩
 · simpa only [aIK,Ee,u5 ,Eg ,
     c2J] using hledger
 · exact hminor
theorem ebL (φ:F[X] →+* K) (L:ℕ)
  (M:c9 (Fin 2×Fin L) col F[X])
  (hfirst: ((M.map φ).submatrix (azJ L) id).rank=L) :
  vw K (fun i=>(M.map φ).row (azJ L i)) := by
 have hli:vw K ((M.map φ).submatrix (azJ L) id).row:= by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  rw [Set.finrank,← Gi ,t8 ,hfirst]
 exact hli
end
end gR.zQ
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
local instance gPI (P:Prop) :Decidable P:=KI P
variable {F ι:Type*} [cy F] [lJ ι] [ox ι]
def specialize {d:ℕ} (v :Fin (d+1)→F[X]) (γ:F) :F[X] :=
 ∑ j,C ((v j).eval γ)*X ^j.val
def avE {d:ℕ} (v :Fin (d+1)→F[X]) (x :F) :F[X] :=
 ∑ j,C (x^j.val)*v j
theorem b9P {d:ℕ} (v :Fin (d+1)→F[X]) (x γ:F) :
  (avE v x).eval γ=(specialize v γ).eval x := by
 simp only [avE,specialize,eval_finsetSum,vh,eval_C,eval_pow,eval_X]
 apply pC rfl
 intro j _
 ring
theorem bsZ {d B:ℕ} (v :Fin (d+1)→F[X])
  (hv : ∀ j,(v j).natDegree≤B) (x :F) :
  (avE v x).natDegree≤B:= by
 apply Ea
 intro j _
 exact (Sd _ _).trans (hv j)
theorem de9 {d:ℕ} (v :Fin (d+1)→F[X]) (γ:F) :
  (specialize v γ).natDegree≤d:= by
 apply Ea
 intro j _
 have h:=Sd ((v j).eval γ) (X ^j.val :F[X])
 simp only [natDegree_X_pow] at h
 exact h.trans (by omega)
theorem eOw (x :ι→F) (V:F→F[X])
   (q:ι→F[X]) (p d:ℕ) (hd:0<d)
   (hq : ∀ i,q i≠0) (hdeg : ∀ i,(q i).natDegree≤p*d)
   (heval : ∀ i γ,(q i).eval γ=(V γ).eval (x i))
   (Γ:nI F)
   (hroots : ∀ γ∈Γ,d≤(Finset.univ.filter
     (fun i=>(V γ).eval (x i)=0)).card) :
   Γ.card≤p*lV ι:= by
 classical
 have hnode (i:ι) :
     (Γ.filter (fun γ=>(V γ).eval (x i)=0)).card≤p*d:= by
   apply le_trans (b:=(q i).natDegree)
   · apply Fz
     intro γ hγ
     apply (xW (hq i)).mpr
     change (q i).eval γ=0
     rw [heval]
     exact (Finset.mem_filter.mp hγ).2
   · exact hdeg i
 have hswap: (∑ γ∈Γ,(Finset.univ.filter
     (fun i=>(V γ).eval (x i)=0)).card) =
     ∑ i:ι,(Γ.filter (fun γ=>(V γ).eval (x i)=0)).card:= by
   simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
   exact zS
 have hleft:Γ.card*d ≤ ∑ γ∈Γ,(Finset.univ.filter
     (fun i=>(V γ).eval (x i)=0)).card:= by
   calc
     Γ.card*d = ∑ _γ∈Γ,d:= by simp
     _≤_:=G9 hroots
 have hright: (∑ i:ι,(Γ.filter
     (fun γ=>(V γ).eval (x i)=0)).card)≤lV ι*(p*d) := by
   calc
     _ ≤ ∑ _i:ι,p*d:=G9 (fun i _=>hnode i)
     _ = _:= by simp
 rw [hswap] at hleft
 nlinarith
theorem eOx (x :ι→F) (V:F→F[X])
   (q:ι→F[X]) (p d δ:ℕ) (hd:0<d)
   (hq : ∀ i,q i≠0) (hdeg : ∀ i,(q i).natDegree≤p*d)
   (heval : ∀ i γ,(q i).eval γ=(V γ).eval (x i))
   (Δ:F[X]) (hΔ:Δ≠0) (hΔdeg:Δ.natDegree≤δ)
   (Γ:nI F)
   (hroots : ∀ γ∈Γ,Δ.eval γ≠0→d≤(Finset.univ.filter
     (fun i=>(V γ).eval (x i)=0)).card) :
   Γ.card≤δ+p*lV ι:= by
 classical
 let E :=Γ.filter (fun γ=>Δ.eval γ=0)
 let R:=Γ.filter (fun γ=>Δ.eval γ≠0)
 have hE :E.card≤δ:= by
   apply le_trans (b:=Δ.natDegree)
   · apply Fz
     intro γ hγ
     exact (xW hΔ).mpr (Finset.mem_filter.mp hγ).2
   · exact hΔdeg
 have hR:R.card≤p*lV ι:= by
   apply eOw x V q p d hd hq hdeg heval R
   intro γ hγ
   obtain ⟨hγΓ,hγΔ⟩:=Finset.mem_filter.mp hγ
   exact hroots γ hγΓ hγΔ
 have hsum:E.card+R.card=Γ.card:= by
   exact WW _
 omega
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.M4
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F col:Type*} [cy F] [lJ col]
def IsPrimitive (P:col→F[X]) :Prop :=nq (oZ P) = ⊤
theorem a6R (P:col→F[X]) :
  IsPrimitive P ↔ ∃ a :col→F[X],∑ i,a i*P i=1 := by
 rw [IsPrimitive,Ideal.eq_top_iff_one,Ideal.mem_span_range_iff_exists_fun]
theorem b2i (P:col→F[X]) (hP:P≠0) :
    ∃ (g:F[X]) (Q:col→F[X]),g≠0 ∧
      (∀ i,P i=g*Q i)∧IsPrimitive Q:= by
  classical
  let I:=nq (oZ P)
  let g:=Submodule.IsPrincipal.generator I
  have hg:g≠0:= by
    intro hg
    have hI:I = ⊥ := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mpr hg
    apply hP
    funext i
    have hm:P i∈I:=Dw (EK i)
    rw [hI] at hm
    exact hm
  have hdiv : ∀ i,∃ q:F[X],P i=g*q:= by
    intro i
    have hm:P i∈I:=Dw (EK i)
    obtain ⟨q,hq⟩:=(Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp hm
    exact ⟨q,by simpa only [pQ,qy] using hq⟩
  choose Q hQ using hdiv
  refine ⟨g,Q,hg,hQ,(a6R Q).mpr ?_⟩
  have hgm:g∈I:=Submodule.IsPrincipal.generator_mem I
  obtain ⟨a,ha⟩:=Ideal.mem_span_range_iff_exists_fun.mp hgm
  refine ⟨a,?_⟩
  have heq :g*(∑ i,a i*Q i)=g*1 := by
    rw [sI,mul_one]
    calc
      _ = ∑ i,a i*P i:= by
        apply pC rfl
        intro i hi
        rw [hQ i]
        ring
      _=g:=ha
  exact Au hg heq
theorem bFs (P:col→F[X]) (hP:IsPrimitive P) (γ:F) :
  (fun i=>(P i).eval γ)≠0:= by
 obtain ⟨a,ha⟩:=(a6R P).mp hP
 intro hzero
 have heval :=oj (oq γ) ha
 simp only [oY ,oD,map_one,Ok] at heval
 have hz : ∀ i,(P i).eval γ=0:= fun i=>oy hzero i
 simp only [hz,mul_zero,SW] at heval
 exact zero_ne_one heval
theorem cNz (P:col→F[X]) (hP:IsPrimitive P) (γ:F) :
  ∃ i,(P i).eval γ≠0:= by
 by_contra h
 push_neg at h
 exact bFs P hP γ (funext h)
theorem c1I (P Q:col→F[X]) (g:F[X]) (hg:g≠0)
   (hPQ : ∀ i,P i=g*Q i) (i:col) :
   (Q i).natDegree≤(P i).natDegree := by
 by_cases hQ:Q i=0
 · simp [hQ]
 · rw [hPQ i,G3 hg hQ]
   omega
theorem c1J {row:Type*} [ox col]
  (M:c9 row col F[X]) (P Q:col→F[X]) (g:F[X]) (hg:g≠0)
  (hPQ : ∀ i,P i=g*Q i) (hM:M.mulVec P=0) :
  M.mulVec Q=0:= by
 have heq :P=g•Q:= by
  funext i
  exact hPQ i
 rw [heq,Lf] at hM
 funext i
 have hi:=oy hM i
 change g*(M.mulVec Q) i=0 at hi
 exact (mul_eq_zero.mp hi).resolve_left hg
end
end gR.M4
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.asZ
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col:Type*} [cy F] [cy K] [lJ col] [ox col]
variable {φ:F[X] →+* K} {M:c9 row col F[X]} {r :ℕ}
theorem gK8 (B:zQ.RowBasis φ M r) (j c:col)
  (hc:c∉oZ B.cols) :
  vector B j c=if j=c then (zQ.pivot B).det else 0:= by
 rw [vector,ceF]
 simp only [LP ,qx ,pQ,th,sS]
 have hzero : ∀ q,inclusion B.cols c q=(0:F[X]) := by
  intro q
  have hq:B.cols q≠c:= fun h=>hc ⟨q,h⟩
  simp [inclusion,hq]
 simp only [hzero,zero_mul,SW,sub_zero]
 by_cases hj:j=c <;> simp [hj,zQ.pivot]
end
end gR.asZ
end
section
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace gR.Bx
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F row col:Type*} [cy F] [lJ row] [lJ col] [ox col]
abbrev lN (F:Type*) [cy F] :=G4 F[X]
def adJ (M:c9 row col F[X]) :ℕ :=
 (M.map (aU F[X] (lN F))).rank
def ay6 (M:c9 row col F[X]) :ℕ :=
  oz (lN F)
    (oK (M.map (aU F[X] (lN F))).mulVecLin)
theorem cep (M:c9 row col F[X]) :
  adJ M+ay6 M=lV col:= by
 simpa only [adJ,ay6,Matrix.rank,zd] using
  t6
   (M.map (aU F[X] (lN F))).mulVecLin
theorem d4g (M:c9 row col F[X]) :
  Nonempty (zQ.RowBasis (aU F[X] (lN F)) M (adJ M)) :=
 zQ.a3O _ M _ rfl
end
end gR.Bx
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
local instance gPF (P:Prop) :Decidable P:=KI P
variable {F ι:Type*} [cy F] [lJ ι] [ox ι]
theorem aVH (x :ι→F) (hx :mD x)
  (S:nI ι) (i:ι) : (mL x S).eval (x i)=0↔i∈S:= by
 simp only [mL,eval_prod,eval_sub,eval_X,eval_C,
  Finset.prod_eq_zero_iff,G0 ,hx.eq_iff]
 simp
theorem cYK (x :ι→F) (H S:nI ι) (hHS:H⊆S) :
  mL x H*mL x (S \ H)=mL x S:= by
 simpa only [mL,qy] using
  (Finset.prod_sdiff (f := fun i=>(X-C (x i) :F[X])) hHS)
theorem fWg (x :ι→F) (hx :mD x)
  (H S:nI ι) (V Q:F[X])
  (hfactor :mL x S=mL x H*V*Q) :
  V∣mL x (S \ H) ∧ ∀ i,V.eval (x i)=0→i∉H := by
 have hHS:H⊆S:= by
  intro i hi
  apply (aVH x hx S i).mp
  rw [hfactor,vh,vh,arK x H i hi,zero_mul,zero_mul]
 have hcancel:mL x (S \ H)=V*Q:= by
  apply Au (S8 x H).ne_zero
  rw [cYK x H S hHS,hfactor]
  ring
 refine ⟨⟨Q,hcancel⟩,?_⟩
 intro i hi
 have hz : (mL x (S \ H)).eval (x i)=0:= by
  rw [hcancel,vh,hi,zero_mul]
 exact (Finset.mem_sdiff.mp ((aVH x hx _ i).mp hz)).2
theorem fX7 (x :ι→F) (H :nI ι) (V:F[X])
   (havoid : ∀ i,V.eval (x i)=0→i∉H) :
   (Finset.univ.filter (fun i : {i // i∉H} => V.eval (x i.val)=0)).card =
     (Finset.univ.filter (fun i=>V.eval (x i)=0)).card:= by
 classical
 let D:=Finset.univ.filter (fun i : {i // i∉H} => V.eval (x i.val)=0)
 have himage :D.image Av =
     Finset.univ.filter (fun i=>V.eval (x i)=0) := by
   ext i
   simp only [Finset.mem_image,Ee,u5 ,Eg]
   constructor
   · rintro ⟨j,hj,rfl⟩
     exact (Finset.mem_filter.mp hj).2
   · intro hi
     exact ⟨⟨i,havoid i hi⟩,Finset.mem_filter.mpr ⟨u5 _,hi⟩,rfl⟩
 rw [← himage,Vq _ Subtype.val_injective]
theorem bIF (x :ι→F) (S:nI ι) :
  (mL x S).roots=S.val.map x := by
 rw [mL,Polynomial.roots_prod _ _ (S8 x S).ne_zero]
 simp only [Polynomial.roots_X_sub_C,Multiset.bind_singleton]
theorem bIG (x :ι→F) (S:nI ι) : (mL x S).Splits := by
 exact Polynomial.Splits.prod (fun i _=>Polynomial.Splits.X_sub_C (x i))
theorem cK0 (x :ι→F) (hx :mD x)
   (S:nI ι) (V:F[X]) (hV:V∣mL x S) :
   V.natDegree=(Finset.univ.filter (fun i=>V.eval (x i)=0)).card:= by
 classical
 have hE0:=(S8 x S).ne_zero
 have hV0:V≠0:=ne_zero_of_dvd_ne_zero hE0 hV
 have hsplits :=(bIG x S).of_dvd hE0 hV
 have hle :=Polynomial.roots.le_of_dvd hE0 hV
 rw [bIF] at hle
 have hnodup:V.roots.Nodup:=Multiset.nodup_of_le hle (S.nodup.map hx)
 have himage : (Finset.univ.filter (fun i=>V.eval (x i)=0)).image x =
     V.roots.toFinset := by
   ext a
   simp only [Finset.mem_image,Ee,u5 ,Eg ,
     Multiset.mem_toFinset]
   constructor
   · rintro ⟨i,hi,rfl⟩
     exact (xW hV0).mpr hi
   · intro ha
     have hEa :=Multiset.mem_of_le hle ha
     obtain ⟨i,hiS,hia⟩:=Multiset.mem_map.mp hEa
     refine ⟨i,?_,hia⟩
     change V.eval (x i)=0
     rw [hia]
     exact (xW hV0).mp ha
 calc
   V.natDegree=V.roots.card:=hsplits.natDegree_eq_card_roots
   _=V.roots.toFinset.card:=(Multiset.toFinset_card_of_nodup hnodup).symm
   _=((Finset.univ.filter (fun i=>V.eval (x i)=0)).image x).card :=
     oj Finset.card himage.symm
   _ = _:=Vq _ hx
theorem eey (H V Q:F[X]) (h d q:ℕ)
    (hH :H.natDegree=h) (hV:V.natDegree≤d) (hQ:Q.natDegree≤q)
    (htotal: (H*V*Q).natDegree=h+d+q) :V.natDegree=d:= by
  have htotal_le : (H*V*Q).natDegree≤h+V.natDegree+q:= by
    calc
      _≤(H*V).natDegree+Q.natDegree :=FR
      _≤H.natDegree+V.natDegree+Q.natDegree :=
        WD FR _
      _≤_:= by omega
  omega
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Bx
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F ι:Type*} [cy F] [lJ ι] [ox ι]
theorem guF (p:ℕ) [t3 F p] (x u v :ι→F) (L t:ℕ) :
  (AI p x u v L t).submatrix (zQ.azJ L) id =
    QO x u v L t:= by
 funext i j
 simp [AI,zQ.azJ]
theorem d4e (p:ℕ) [t3 F p] (x u v :ι→F)
    (L t r :ℕ)
    (hr :adJ (AI p x u v L t)=t+1-r)
    (hfirst:adJ (QO x u v L t)=L) :
    ∃ B:zQ.RowBasis (aU F[X] (lN F))
        (AI p x u v L t) (t+1-r),
      (∑ q,if (B.rows q).1=0 then 1 else p)=L+p*(t+1-r-L) ∧
      (zQ.pivot B).det.natDegree≤L+p*(t+1-r-L) := by
  let φ:=aU F[X] (lN F)
  have hfirst' : (((AI p x u v L t).map φ).submatrix
      (zQ.azJ L) id).rank=L:= by
    have heq : ((AI p x u v L t).map φ).submatrix
        (zQ.azJ L) id=(QO x u v L t).map φ:= by
      funext i j
      exact oj φ (oy (oy (guF p x u v L t) i) j)
    rw [heq]
    exact hfirst
  exact zQ.d4W φ L (t+1-r) p _ hr
    (zQ.ebL φ L _ hfirst')
    (a8L p x u v L t)
end
end gR.Bx
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.asZ
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F K row col:Type*} [cy F] [cy K] [lJ row]
 [lJ col] [ox col]
variable {φ:F[X] →+* K} {M:c9 row col F[X]} {r :ℕ}
theorem d4D (B:zQ.RowBasis φ M r)
    (hφ:mD φ) (hnull:r+1=lV col)
    (d:row→ℕ) (hdeg : ∀ i j,(M i j).natDegree≤d i) :
    ∃ Q:col→F[X],M4.IsPrimitive Q∧M.mulVec Q=0 ∧
      (∀ c,(Q c).natDegree ≤ ∑ q,d (B.rows q)) ∧
      ∀ (γ:F),(zQ.pivot B).det.eval γ≠0 →
        ∀ v :col→F,(M.map (oq γ)).mulVec v=0 →
          ∃ a :F,v=a•(fun c=>(Q c).eval γ) := by
  classical
  obtain ⟨j,hj⟩ : ∃ j:col,j∉oZ B.cols := by
    by_contra h
    push Not at h
    have hsurj:yU B.cols := fun j=>h j
    have hc:=Fintype.card_le_of_surjective B.cols hsurj
    rw [t8] at hc
    omega
  have hP:vector B j≠0:= by
    intro hzero
    have h:=gK8 B j j hj
    rw [if_pos rfl] at h
    apply B.minor_ne
    simpa only [zQ.pivot,u9] using
      h.symm.trans (oy hzero j)
  obtain ⟨g,Q,hg,hPQ,hprim⟩:=M4.b2i (vector B j) hP
  have hQ:M.mulVec Q=0:=M4.c1J
    M (vector B j) Q g hg hPQ (bA5 B hφ j)
  refine ⟨Q,hprim,hQ,?_,?_⟩
  · intro c
    exact (M4.c1I _ _ _ hg hPQ c).trans
      (bPI B d hdeg j c)
  · intro γ hγ v hv
    have hR:=zQ.buH φ hφ M r B γ hγ
    have hdim:oz F
        (oK (M.map (oq γ)).mulVecLin)=1 := by
      have hh:=t6 (M.map (oq γ)).mulVecLin
      change (M.map (oq γ)).rank+_ = _ at hh
      rw [hR,zd] at hh
      omega
    have hQγ: (M.map (oq γ)).mulVec (fun c=>(Q c).eval γ)=0:= by
      funext i
      have h:=oj (oq γ) (oy hQ i)
      simpa only [th,sS ,oY ,oD,p5 ,
        Du,Ok,u9] using h
    exact aRz.cWG _ hdim _
      (M4.bFs Q hprim γ) hQγ v hv
end
end gR.asZ
end
section
namespace gR
noncomputable section
open Polynomial Finset
variable {F ι:Type*} [cy F] [lJ ι] [ox ι]
def NM (x :ι→F) (w:ι→F) (k :ℕ) (S:nI ι) :Prop :=
 ∃ P:F[X],P.degree<k ∧ ∀ i∈S,P.eval (x i)=w i
theorem dh3 (x :ι→F) (hx :mD x)
  (w:ι→F) (k A:ℕ) (hkA:k<A) (S:nI ι)
  (hAS:A≤S.card) (hbad : ¬ NM x w k S) :
  ∃ T:nI ι,T⊆S∧T.card=A ∧ ¬ NM x w k T:= by
 classical
 obtain ⟨B,hBS,hBcard⟩:=Finset.exists_subset_card_eq (show k≤S.card by omega)
 have hBinj:Gk x (B:Set ι) := fun a _ b _ h=>hx h
 let q:=Re B x w
 have hqdeg:q.degree<(k :vZ ℕ) := by
  simpa only [q,hBcard] using SM w hBinj
 have hqval : ∀ i∈B,q.eval (x i)=w i :=
  fun i hi=>Up w hBinj hi
 obtain ⟨a,haS,ha⟩ : ∃ a∈S,q.eval (x a)≠w a := by
  by_contra hh
  push Not at hh
  exact hbad ⟨q,hqdeg,hh⟩
 have haB:a∉B:= fun hh=>ha (hqval a hh)
 have hins :insert a B⊆S:=Finset.insert_subset_iff.mpr ⟨haS,hBS⟩
 have hsmall: (insert a B).card≤A:= by
  rw [Finset.card_insert_of_notMem haB,hBcard]
  omega
 obtain ⟨T,hBT,hTS,hTcard⟩:=Finset.exists_subsuperset_card_eq hins hsmall hAS
 refine ⟨T,hTS,hTcard,?_⟩
 rintro ⟨P,hP,hPv⟩
 have hpq:P=q:=Polynomial.eq_of_degrees_lt_of_eval_index_eq B hBinj
  (by simpa only [hBcard] using hP) (by simpa only [hBcard] using hqdeg)
  (fun i hi=>(hPv i (hBT (Finset.mem_insert_of_mem hi))).trans (hqval i hi).symm)
 exact ha (hpq ▸ hPv a (hBT (Finset.mem_insert_self a B)))
theorem gEp (x :ι→F) (hx :mD x)
   (u v :ι→F) (k A:ℕ) (hkA:k<A) (S:nI ι)
   (hAS:A≤S.card) (hbad : ¬ (NM x u k S∧NM x v k S)) :
   ∃ T:nI ι,T⊆S∧T.card=A ∧
     ¬ (NM x u k T∧NM x v k T) := by
 classical
 by_cases hu:NM x u k S
 · obtain ⟨T,hTS,hTcard,hTbad⟩:=dh3 x hx v k A hkA S hAS
     (fun hv=>hbad ⟨hu,hv⟩)
   exact ⟨T,hTS,hTcard,fun h=>hTbad h.2⟩
 · obtain ⟨T,hTS,hTcard,hTbad⟩:=dh3 x hx u k A hkA S hAS hu
   exact ⟨T,hTS,hTcard,fun h=>hTbad h.1⟩
theorem d3E (x :ι→F) (hx :mD x)
  (u v :ι→F) (γ:F) (k A:ℕ) (hkA:k<A) (S:nI ι)
  (hAS:A≤S.card) (P:F[X]) (hP:P.degree<k)
  (hfold : ∀ i∈S,P.eval (x i)=u i+γ*v i)
  (hbad : ¬ (NM x u k S∧NM x v k S)) :
  ∃ T:nI ι,T⊆S∧T.card=A∧P.degree<k ∧
    (∀ i∈T,P.eval (x i)=u i+γ*v i) ∧
    ¬ (NM x u k T∧NM x v k T) := by
 obtain ⟨T,hTS,hcard,hbadT⟩:=gEp x hx u v k A hkA S hAS hbad
 exact ⟨T,hTS,hcard,hP,fun i hi=>hfold i (hTS hi),hbadT⟩
end
end gR
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι:Type*} [cy F] [lJ ι] [ox ι]
def bRS (x :ι→F) (w:ι→F) (E :F[X]) (L:ℕ) :Prop :=
 ∀ j<L,∑ i,weight x i*(E.eval (x i)*w i)*x i^j=0
theorem b2F (x :ι→F) (hx :mD x)
    (w:ι→F) (k L:ℕ) (S:nI ι)
    (hsize :k+L+S.card=lV ι)
    (hmom:bRS x w (mL x S) L) :
    NM x w k (vj \ S) := by
  classical
  let T:=vj \ S
  let P:=Re T x w
  have hTcard:T.card=lV ι - S.card:= by
    simp [T,Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  have hPinj:Gk x (T:Set ι) :=hx.injOn
  have hPval : ∀ i∈T,P.eval (x i)=w i :=
    fun i hi=>Up w hPinj hi
  refine ⟨P,?_,hPval⟩
  by_contra hP
  have hp0:P≠0:= by
    intro hz
    simp [hz] at hP
  have hPnat :k≤P.natDegree := by
    have hnot:=not_lt.mp hP
    exact_mod_cast hnot.trans Polynomial.degree_le_natDegree
  have hPbound:P.natDegree<lV ι - S.card:= by
    apply (Mz hp0).mpr
    simpa only [P,hTcard] using SM w hPinj
  let j:=lV ι - 1 - S.card-P.natDegree
  have hj:j<L:= by omega
  have htop:S.card+P.natDegree+j=lV ι - 1 := by omega
  let Q:=mL x S*P*X ^j
  have hE0:mL x S≠0:=(S8 x S).ne_zero
  have hQdeg:Q.natDegree=lV ι - 1 := by
    dsimp [Q]
    rw [G3 (zi hE0 hp0) (Kc _ X_ne_zero),
      G3 hE0 hp0,ZQ,natDegree_X_pow,htop]
  have hQlt:Q.degree<(lV ι:vZ ℕ) := by
    apply Polynomial.degree_le_natDegree.trans_lt
    rw [hQdeg]
    exact_mod_cast (show lV ι - 1<lV ι by omega)
  have hcoeff :=Pk (s :=vj) (v :=x)
    (fun a _ b _ hab=>hx hab) (by simpa using hQlt)
  have hpoint (i:ι) :
      (mL x S).eval (x i)*P.eval (x i) =
      (mL x S).eval (x i)*w i:= by
    by_cases hi:i∈S
    · simp [arK x S i hi]
    · rw [hPval i (Finset.mem_sdiff.mpr ⟨u5 _,hi⟩)]
  have hsum : ∑ i,weight x i*Q.eval (x i)=0:= by
    dsimp [Q]
    simp only [vh,eval_pow,eval_X]
    simp_rw [hpoint]
    simpa only [Ar] using hmom j hj
  have hz :Q.coeff (lV ι - 1)=0:= by
    have hc:Q.coeff (lV ι - 1) =
        ∑ i,weight x i*Q.eval (x i) := by
      simpa only [zk,weight,KA,qy] using hcoeff
    exact hc.trans hsum
  have hQ0:Q≠0:=zi (zi hE0 hp0) (Kc _ X_ne_zero)
  apply (Polynomial.leadingCoeff_ne_zero.mpr hQ0)
  simpa only [Polynomial.leadingCoeff,hQdeg] using hz
theorem cUy (x :ι→F) (w:ι→F) (E :F[X]) (L t:ℕ)
  (hE :E.natDegree≤t)
  (hrec : ∀ i:Fin L,∑ j:Fin (t+1),
    oX x w (i.val+j.val)*E.coeff j.val=0) :
  bRS x w E L:= by
 intro i hi
 have hh:=hrec ⟨i,hi⟩
 have hsum: (∑ j:Fin (t+1),oX x w (i+j.val)*E.coeff j.val) =
    ∑ a,weight x a*(E.eval (x a)*w a)*x a^i:= by
  simp only [oX,yL]
  rw [zS]
  apply pC rfl
  intro a _
  rw [← bw8 E t hE (x a)]
  simp only [yL,sI,vG]
  apply pC rfl
  intro j _
  ring
 exact hsum.symm.trans hh
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.kL
noncomputable section
open Matrix Finset
open scoped BigOperators
variable {K:Type*} [cy K]
def aVg (s :Fin 2→ℕ→K) (rows cols :ℕ) :
    c9 (Fin 2×Fin rows) (Fin cols) K :=
  fun b j=>s b.1 (b.2.val+j.val)
def az2 (s :Fin 2→ℕ→K) (m H :ℕ) :
    c9 (Fin (m-H)) (Fin 2×Fin (H+1)) K :=
  (aVg s (H+1) (m-H)).transpose
theorem c76 (s :Fin 2→ℕ→K) (m H :ℕ)
    (v :Fin 2×Fin (H+1)→K) :
    (az2 s m H).mulVec v=0 ↔
      ∀ j:Fin (m-H),∑ b:Fin 2,∑ i:Fin (H+1),
        v (b,i)*s b (i.val+j.val)=0:= by
  simp only [funext_iff,th,sS ,az2,aVg,
    Matrix.transpose_apply,u9,Fintype.sum_prod_type,qy]
theorem dOt (s :Fin 2→ℕ→K) (m H :ℕ) :
    oz K (oK (az2 s m H).mulVecLin)+(m-H) =
      2*(H+1)+Module.finrank K
        (oK (aVg s (H+1) (m-H)).mulVecLin) := by
  have hr :=t6 (az2 s m H).mulVecLin
  have hk :=t6
    (aVg s (H+1) (m-H)).mulVecLin
  change (az2 s m H).rank+_ = _ at hr
  change (aVg s (H+1) (m-H)).rank+_ = _ at hk
  rw [zd ,Fintype.card_prod,t8 ,
    t8] at hr
  rw [zd ,t8] at hk
  have he : (az2 s m H).rank=(aVg s (H+1) (m-H)).rank :=
    Matrix.rank_transpose _
  omega
def aKl (s :Fin 2→ℕ→K) (m a b c:ℕ) :Prop :=
  ∀ H<m,oz K
    (oK (aVg s (H+1) (m-H)).mulVecLin) =
      (m-H-a)+(m-H-b)+(m-H-c)
theorem fVV (s :Fin 2→ℕ→K)
   (m a b c H :ℕ) (hc:c≤m) (hsum:a+b+c=2*m+2)
   (ha :a≤b) (hb:b≤m-H) (hH :m+1-c≤H) (hHm:H<m)
   (hHF:aKl s m a b c) :
   oz K (oK (az2 s m H).mulVecLin) =
     H-(m+1-c)+1 := by
 have hd:=dOt s m H
 rw [hHF H hHm] at hd
 omega
theorem eAu (s :Fin 2→ℕ→K)
  (m a b c:ℕ) (hc:c≤m) (hsum:a+b+c=2*m+2)
  (ha :a≤b) (hb:b<c) (hc2 :1<c)
  (hHF:aKl s m a b c) :
  oz K (oK (az2 s m (m+1-c)).mulVecLin)=1 := by
 have h:=fVV s m a b c (m+1-c) hc hsum ha
  (by omega) (by omega) (by omega) hHF
 simpa using h
end
end gR.kL
end
section
namespace gR.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι:Type} [cy F] [lJ ι] [ox ι]
theorem b2G (x :ι→F) (hx :mD x)
  (w:ι→F) (k :ℕ) (hk :k≤lV ι)
  (hzero : ∀ j<lV ι-k,oX x w j=0) :
  NM x w k Finset.univ := by
 have hmom:bRS x w (mL x ∅) (lV ι-k) := by
  intro j hj
  simpa [oX,mL] using hzero j hj
 simpa using b2F x hx w k (lV ι-k) ∅
  (by simp; omega) hmom
theorem aAt (x u v :ι→F) (a b:F) (j:ℕ) :
  oX x (fun i=>a*u i+b*v i) j=a*oX x u j+b*oX x v j:= by
 simp only [oX,mul_add,add_mul,VO,sI]
 congr 1 <;> apply pC rfl <;> intro i _ <;> ring
end
end gR.Principal
end
section
namespace yP.C52
open scoped BigOperators Matrix
noncomputable section
theorem fTe
   {F R C C' : Type*} [cy F] [lJ C] [lJ C']
   (M:c9 R C F) (rep:C' → C)
   (h : ∀ c,M.col c=0 ∨ ∃ j,M.col c=M.col (rep j)) :
   M.rank≤(M.submatrix id rep).rank := by
 classical
 rw [Mj,Mj]
 have :=FiniteDimensional.span_of_finite (K:=F)
   (Set.finite_range (M.submatrix id rep).col)
 apply Submodule.finrank_mono
 apply Submodule.span_le.mpr
 rintro _ ⟨c,rfl⟩
 rcases h c with hz | ⟨j,hj⟩
 · rw [hz]
   exact Submodule.zero_mem _
 · rw [hj]
   exact Dv ⟨j,rfl⟩
end
end yP.C52
end
section
set_option maxRecDepth 10000
namespace wT
open Finset
def V (D w B s t:ℕ) :ℕ :=
  ∑ i∈range (B+1),∑ j∈range (B+1-i),
    (D+1-w*(i+j))*(s+1-i)*(t+1-j)
def J (m s t:ℕ) :ℕ :=
  ∑ i∈range m,∑ j∈range (m-i),
    (m-i-j)*(s+1-i)*(t+1-j)
end wT
end
section
namespace wT
noncomputable section
open Polynomial Finset
def aCC {R:Type*} [lz R] (B:ℕ) (Q:R[X]) (a b:R) :R :=
 ∑ j∈range (B+1),Q.coeff j*a^j*b^(B-j)
theorem cFH {R:Type*} [lz R]
  (B:ℕ) (Q:R[X]) (hQ:Q.natDegree≤B) (a b y :R) (hy :b*y=a) :
  aCC B Q a b=b^B*Q.eval y := by
 rw [S1 (show Q.natDegree<B+1 by omega),sI]
 unfold aCC
 apply pC rfl
 intro j hj
 have hjB:j≤B:= by have :=mem_range.mp hj; omega
 rw [← hy,mul_pow]
 have hb:b^j*b^(B-j)=b^B:= by rw [← vG,Nat.add_sub_of_le hjB]
 calc
  Q.coeff j*(b^j*y^j)*b^(B-j)= Q.coeff j*y^j*(b^j*b^(B-j)) := by ring
  _=b^B*(Q.coeff j*y^j) := by rw [hb]; ring
theorem dLI {R:Type*} [lz R]
  (B:ℕ) (Q:R[X]) (hQ:Q.natDegree≤B) (a b y :R)
  (hy :b*y=a) (hroot :Q.eval y=0) :aCC B Q a b=0:= by
 rw [cFH B Q hQ a b y hy,hroot,mul_zero]
theorem dLH {K:Type*} [cy K]
  (B:ℕ) (Q:K[X]) (hQ:Q.natDegree≤B) (a b:K) (hb:b≠0)
  (hnot : ¬ (C b*X-C a)∣Q) :aCC B Q a b≠0:= by
 have heq :C b*X-C a=C b*(X-C (a/b)) := by
  rw [mul_sub,← C_mul]
  have hba :b*(a/b)=a := by field_simp
  rw [hba]
 have hroot :Q.eval (a/b)≠0:= by
  intro hz
  apply hnot
  rw [heq]
  have hd: (X-C (a/b))∣Q:=(dvd_iff_isRoot).mpr hz
  have hu:C b∣(1 :K[X]) :=(isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb)).dvd
  simpa using mul_dvd_mul hu hd
 rw [cFH B Q hQ a b (a/b) (by field_simp)]
 exact zi (Kc B hb) hroot
theorem cZm {R S:Type*} [lz R] [lz S]
  (f :R →+* S) (B:ℕ) (Q:R[X]) (a b:R) :
  f (aCC B Q a b)=aCC B (Q.map f) (f a) (f b) := by
 simp [aCC]
theorem dLG {R K:Type*} [lz R] [t5 R]
   [IsGCDMonoid R] [cy K] [n5 R K] [IsFractionRing R K]
   (B:ℕ) (Q:R[X]) (hQ:Q.natDegree≤B) (a b:R) (hb:b≠0)
   (hprimitive : (C b*X-C a).IsPrimitive) (hnot : ¬ (C b*X-C a)∣Q) :
   aCC B Q a b≠0:= by
 have hmap : ¬ (C (aU R K b)*X-C (aU R K a))∣Q.map (aU R K) := by
   simpa only [Polynomial.map_sub,Qy ,Polynomial.map_C,Polynomial.map_X] using
     (not_congr (hprimitive.dvd_iff_fraction_map_dvd_fraction_map K)).mp hnot
 have hdeg: (Q.map (aU R K)).natDegree≤B:=(natDegree_map_le).trans hQ
 have hb' : aU R K b≠0:= by simpa using (Gn R K).ne hb
 have hn:=dLH B (Q.map (aU R K)) hdeg
   (aU R K a) (aU R K b) hb' hmap
 rw [← cZm] at hn
 exact fun hz=>hn (by rw [hz,p5])
end
end wT
end
section
namespace aiH
noncomputable section
open Polynomial
theorem cNI {R:Type*} [lz R] [t5 R]
   (p B:ℕ) [CharP R p] (f :R[X]) (hf :f≠0) (hdegree :f.natDegree≤B)
   (hsmall:B<p) (y :R) (hroot :f.IsRoot y) :
   ∃ j<B,(uz^[j] f).IsRoot y ∧ ¬(uz (uz^[j] f)).IsRoot y := by
 let μ:=f.rootMultiplicity y
 have hμpos :0<μ:=(rootMultiplicity_pos hf).mpr hroot
 have hμle :μ≤B:= by
   have hd:=natDegree_le_of_dvd (f.pow_rootMultiplicity_dvd y) hf
   have hle :μ≤f.natDegree := by simpa [μ,natDegree_pow] using hd
   exact hle.trans hdegree
 have hnzd : ∀ m≤μ,m≠0→(m:R)∈JM R:= by
   intro m hm hmn
   apply mem_nonZeroDivisors_of_ne_zero
   intro hz
   have hd:p∣m:=(CharP.cast_eq_zero_iff R p m).mp hz
   have hp:p≤m:=Nat.le_of_dvd (Nat.pos_of_ne_zero hmn) hd
   omega
 have hnext : ¬(uz^[μ] f).IsRoot y := by
   intro hnext
   have hall : ∀ m≤μ,(uz^[m] f).IsRoot y := by
     intro m hm
     rcases lt_or_eq_of_le hm with hh | rfl
     · exact Yo hh
     · exact hnext
   have hc:=lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors' hf hall hnzd
   exact (Nat.lt_irrefl μ) hc
 refine ⟨μ-1,by omega,Yo (by omega),?_⟩
 have he :uz (uz^[μ-1] f)=uz^[μ] f := by
   simpa only [Nat.succ_eq_add_one,Nat.sub_add_cancel hμpos] using (Function.iterate_succ_apply' uz (μ-1) f).symm
 rwa [he]
end
end aiH
end
section
namespace aY4
noncomputable section
open MvPolynomial Filter
open scoped BigOperators
variable {k σ τ F E :Type} [cy k] [Finite σ] [Finite τ]
variable [cy F] [cy E] [n5 k F] [n5 k E] [n5 F E]
variable {P:nX (ov σ k)} {Q:nX (ov τ k)}
local notation "A" => MvPolynomial τ k ⧸ Q
local notation "B" => MvPolynomial σ k ⧸ P
theorem eyD (g:A →ₐ[k] B) (i:A →ₐ[k] F) (j:B →ₐ[k] E)
   (hi:mD i) (hcomm : ∀ a,j (g a)=aU F E (i a))
   (hg : ∀ t,g (p7 Q (zh t))∈qm P 1)
   {ι:Type} [lJ ι] (e :ze ι F E)
   (u:ι→B) (hu : ∀ l,j (u l)=e l) :
   ∃ C:ℕ,∀ n:ℕ,lV ι*qM Q n ≤
     qM P (n+C) := by
 classical
 choose d hd using fun l=>exists_mem_quotientDegreeLE P (u l)
 obtain ⟨C,hC⟩:=Finite.exists_le d
 refine ⟨C,fun n => ?_⟩
 let T: (ι→qm Q n) →ₗ[k] B :=
   ∑ l,(LinearMap.mulRight k (u l)).comp
     (g.toLinearMap.comp ((qm Q n).subtype.comp (LinearMap.proj l)))
 have hT (x :ι→qm Q n) :T x = ∑ l,g (x l)*u l:= by
   simp [T]
 let S:=T.codRestrict (qm P (n+C)) fun x=> by
   rw [hT]
   refine Kp _ fun l _=>mul_mem_quotientDegreeLE ?_ ?_
   · simpa only [one_mul] using map_mem_quotientDegreeLE g hg (x l).property
   · exact quotientDegreeLE_mono P (hC l) (hd l)
 have hcoords (x :ι→qm Q n) :
     j (T x)=e.equivFun.symm (fun l=>i (x l)) := by
   simp only [hT,oY ,oD,hcomm,hu,Module.Basis.equivFun_symm_apply,vi]
 have hinj:mD S:= by
   intro x y h
   have h' : T x=T y :=oj Av h
   have h'' := e.equivFun.symm.injective ((hcoords x).symm.trans ((oj j h').trans (hcoords y)))
   exact funext fun l=>vk (hi (oy h'' l))
 have h:=UZ hinj
 rwa [Mk,GR,zk,nsmul_eq_mul] at h
variable [vl k F E]
omit [Finite σ] in
theorem upper_bound (g:A →ₐ[k] B) (i:A →ₐ[k] F) (j:B →ₐ[k] E)
    (hi:mD i) (hj:mD j)
    (hcomm : ∀ a,j (g a)=aU F E (i a))
    {ι κ:Type} [lJ ι] [lJ κ] (e :ze ι F E)
    (v :κ→B)
    (hgen : ∀ n (x :B),x∈qm P n → ∃ a :κ→A,
      (∀ l,a l∈qm Q n) ∧ ∑ l,g (a l)*v l=x)
    {d:F} (hd:d≠0) (b:κ→ι→A)
    (hb : ∀ l r,i (b l r)=d*e.equivFun (j (v l)) r) :
    ∃ C:ℕ,∀ n:ℕ,qM P n ≤
      lV ι*qM Q (n+C) := by
  classical
  choose levels hlevels using fun s :κ×ι=>exists_mem_quotientDegreeLE Q (b s.1 s.2)
  obtain ⟨C,hC⟩:=Finite.exists_le levels
  refine ⟨C,fun n => ?_⟩
  let W:=(qm Q (n+C)).map i.toLinearMap
  let T (r :ι) :B →ₗ[k] F :=
    (LinearMap.mulLeft k d).comp (((LinearMap.proj r).comp
      e.equivFun.toLinearMap).restrictScalars k |>.comp j.toLinearMap)
  have hT (r :ι) (x :B) :T r x=d*e.equivFun (j x) r :=rfl
  have hmem (r :ι) (x :qm P n) :T r x∈W:= by
    obtain ⟨a,ha,hax⟩:=hgen n x x.property
    refine Submodule.mem_map.mpr ⟨∑ l,a l*b l r,?_,?_⟩
    · exact Kp _ fun l _ =>
        mul_mem_quotientDegreeLE (ha l) (quotientDegreeLE_mono Q (hC (l,r)) (hlevels (l,r)))
    · change i (∑ l,a l*b l r)=T r x
      have hm (l:κ) :j (g (a l)*v l)=(i (a l))•j (v l) := by
        rw [oD,hcomm,vi]
      rw [hT,← hax,oY ,oY ,oY ,yQ,sI]
      refine pC rfl fun l _ => ?_
      rw [oD,hb,hm,map_smul]
      simp only [qx ,pQ]
      ring
  let S:qm P n →ₗ[k] (ι→W) :=
    LinearMap.pi fun r=>((T r).domRestrict _).codRestrict W (hmem r)
  have hinj:mD S:= by
    intro x y h
    apply vk
    apply hj
    apply e.equivFun.injective
    funext r
    apply Au hd
    exact oj (fun f :ι→W=>(f r :F)) h
  have hrw:oz k W=qM Q (n+C) :=
    (Submodule.equivMapOfInjective i.toLinearMap hi (qm Q (n+C))).finrank_eq.symm
  have h:=UZ hinj
  rwa [Mk,GR,zk,nsmul_eq_mul,hrw] at h
theorem dVz {d C₁ C₂:ℕ} (hd:d≠0)
   (hdeg: (uW P).natDegree=(uW Q).natDegree)
   (hl : ∀ n,d*qM Q n≤qM P (n+C₁))
   (hu : ∀ n,qM P n≤d*qM Q (n+C₂)) :
   affineDegree P=(d:ℚ)*affineDegree Q:= by
 open Polynomial in
 let HS:=uW P
 let HT:=uJ (d:ℚ)*uW Q
 have hd' : (d:ℚ)≠0:=Nat.cast_ne_zero.mpr hd
 have hdeg' : HS.natDegree=HT.natDegree := by
   rw [show HT.natDegree=(uW Q).natDegree from natDegree_C_mul hd']
   exact hdeg
 have hshift (c:ℕ) :Tendsto (fun n:ℕ=>n+c) atTop atTop :=
   tendsto_atTop_mono (fun n=>Nat.le_add_right n c) tendsto_id
 have hS : ∀ᶠ n:ℕ in atTop,HS.eval (n:ℚ)=qM P n :=
   TH _
 have hT : ∀ᶠ n:ℕ in atTop,HT.eval (n:ℚ)=(d*qM Q n:ℕ) := by
   filter_upwards [TH Q] with n hn
   simp [HT,hn]
 have hlo : ∀ᶠ n:ℕ in atTop,HT.eval (n:ℚ)≤(taylor (C₁:ℚ) HS).eval (n:ℚ) := by
   filter_upwards [hT,(hshift C₁).eventually hS] with n hn hn'
   rw [taylor_eval,← zg ,hn,hn']
   exact_mod_cast hl n
 have hup : ∀ᶠ n:ℕ in atTop,HS.eval (n:ℚ)≤(taylor (C₂:ℚ) HT).eval (n:ℚ) := by
   filter_upwards [hS,(hshift C₂).eventually hT] with n hn hn'
   rw [taylor_eval,← zg ,hn,hn']
   exact_mod_cast hu n
 have hTpos : ∀ᶠ n:ℕ in atTop,0≤HT.eval (n:ℚ) :=
   hT.mono fun n h=>h.symm ▸ Nat.cast_nonneg (α:=ℚ) (d*qM Q n)
 have lc₁:=(LR hTpos hlo).2
   (hdeg'.symm.trans (natDegree_taylor _ _).symm)
 have lc₂:=(LR
   (eventually_eval_affineHilbertPolynomial_nonneg P) hup).2
   (hdeg'.trans (natDegree_taylor _ _).symm)
 rw [leadingCoeff_taylor] at lc₁ lc₂
 have he :=lc₂.antisymm lc₁
 change (HS.natDegree.factorial:ℚ)*HS.leadingCoeff =
   (d:ℚ)*((((uW Q).natDegree.factorial:ℕ) :ℚ) *
     (uW Q).leadingCoeff)
 rw [show HS.natDegree=(uW Q).natDegree from hdeg,he,
   show HT.leadingCoeff= _ from leadingCoeff_C_mul_of_isUnit hd'.isUnit _]
 ring
end
end aY4
end
section
namespace bzE
noncomputable section
open scoped TensorProduct
private theorem eQF {R S:Type*} [lz R] [lz S]
  [n5 R S] [z9 R S] (q:nX R) [q.IsPrime]
  (h:Et (S ⊗[R] q.ResidueField)) :
  Et (S ⧸ q.map (aU R S)) := by
 let f : (R ⧸ q) →ₐ[R] q.ResidueField:=IsScalarTower.toAlgHom R _ _
 have hf :mD f :=Ideal.injective_algebraMap_quotient_residueField q
 let e :=Algebra.TensorProduct.map (AlgHom.id R S) f
 have he :mD e :=
  Module.Flat.lTensor_preserves_injective_linearMap (M:=S) f.toLinearMap hf
 have :Et (S ⊗[R] (R ⧸ q)) :=Kh e he
 let baseChange :=Algebra.TensorProduct.quotIdealMapEquivTensorQuot S q
 exact Kh baseChange baseChange.injective
variable {k E R S:Type*} [cy k] [cy E] [lz R] [lz S]
 [n5 k E] [n5 k R] [n5 k S] [n5 R S] [n5 E S]
 [vl k R S] [vl k E S] [ X8 k R E S]
 [IsPurelyInseparable k E]
include k E in
private theorem cA6 (x :S) :
  ∃ n>0,∃ y :R,aU R S y=x^n:= by
 let e :=Algebra.IsPushout.equiv k R E S
 obtain ⟨n,hn,y,hy⟩:=IsPurelyInseparable.exists_pow_mem_range_tensorProduct (e.symm x)
 refine ⟨n,hn,y,?_⟩
 simpa [Algebra.TensorProduct.algebraMap_apply,Algebra.IsPushout.equiv_tmul,e] using
  oj e hy
include k E in
private theorem exR (P:nX S) [P.IsPrime]
  (q:nX R) [q.IsPrime] (hq:q=P.comap (aU R S)) :
  IsLocalization (HZ S q.primeCompl) (yB P) := by
 let M:=HZ S q.primeCompl
 have hle :M≤P.primeCompl:= by
  rintro _ ⟨x,hx,rfl⟩
  apply Ideal.mem_primeCompl_iff.mpr
  intro hp
  apply Ideal.mem_primeCompl_iff.mp hx
  rw [hq]
  exact hp
 refine (IsLocalization.iff_of_le_of_exists_dvd (S:=yB P) M
  P.primeCompl hle ?_).mpr xI
 intro x hx
 obtain ⟨n,hn,y,hy⟩:=cA6 (k :=k) (E :=E) (R:=R) x
 refine ⟨x^n,⟨y,?_,hy⟩,dvd_pow_self x hn.ne'⟩
 change y∉q
 rw [hq,Ideal.mem_comap,hy]
 exact P.primeCompl.pow_mem hx _
include k E in
private def exw (P:nX S) [P.IsPrime]
  (q:nX R) [q.IsPrime] (hq:q=P.comap (aU R S)) :
  let L:=yB P
  S ⊗[R] q.ResidueField ≃+* L ⧸ (q.map (aU R S)).map (aU S L) := by
 let L:=yB P
 let M:=HZ S q.primeCompl
 let B:=Localization M
 letI:IsLocalization M L:=exR (k :=k) (E :=E) P q hq
 let e :=IsLocalization.algEquiv M B L
 letI:n5 S (q.Fiber S) :=Np
 refine (Algebra.TensorProduct.comm R S q.ResidueField).toRingEquiv.trans ?_
 refine (Ideal.Fiber.algEquivAux₁ (S:=S) q).toRingEquiv.trans ?_
 refine Ideal.quotientEquiv _ _ e.toRingEquiv ?_
 have hcomp:e.toRingEquiv.toRingHom.comp (aU S B)=aU S L :=
  RingHom.ext e.commutes
 exact ((Ideal.map_map (aU S B) e.toRingEquiv.toRingHom).trans
  (oj (q.map (aU R S)).map hcomp)).symm
include k E in
theorem dWB (P:nX S) [P.IsPrime]
    (h : let L := yB P
      ((P.comap (aU R S)).map (aU R S)).map (aU S L) =
        lI L) :
    (P.comap (aU R S)).map (aU R S)=P:= by
  let q:=P.comap (aU R S)
  have :q.IsPrime :=Ideal.comap_isPrime _ _
  let L:=yB P
  let e :S ⊗[R] q.ResidueField ≃+* pG L :=
    (exw (k :=k) (E :=E) P q rfl).trans (Ideal.quotEquivOfEq h)
  have hred:Et (S ⊗[R] q.ResidueField) :=
    Kh e e.injective
  have hpush:X8 k R E S:=xI
  have :z9 R S:=Module.Flat.isBaseChange k R E S hpush.out
  let J:=q.map (aU R S)
  have hrad:J.IsRadical:=(Ideal.isRadical_iff_quotient_reduced J).mpr
    (eQF q hred)
  refine z7 Ideal.map_comap_le ?_
  intro x hx
  obtain ⟨n,hn,y,hy⟩:=cA6 (k :=k) (E :=E) (R:=R) x
  have hyq:y∈q:= by
    change aU R S y∈P
    rw [hy]
    exact P.pow_mem_of_mem hx n hn
  exact hrad ⟨n,hy ▸ NX (aU R S) hyq⟩
end
end bzE
end
section
set_option backward.isDefEq.respectTransparency false
namespace bzV
open scoped Polynomial
open MvPolynomial
private theorem eoc {k A:Type} [cy k] [Cy k]
  [lz A] [n5 k A] (y v :A)
  (hvar : ¬ p6 k y ∨ ¬ p6 k v) :
  {t:k | ¬ p6 k (y+algebraMap k A t*v)}.Infinite := by
 apply Set.infinite_of_finite_compl
 apply NZ
 intro t ht u hu
 change ¬ ¬ p6 k (y+algebraMap k A t*v) at ht
 change ¬ ¬ p6 k (y+algebraMap k A u*v) at hu
 by_contra htu
 have ht' := isAlgebraic_iff_isIntegral.mp (not_not.mp ht)
 have hu' := isAlgebraic_iff_isIntegral.mp (not_not.mp hu)
 have hdiff :v9 k (aU k A (t - u)*v) := by
  convert ht'.sub hu' using 1
  rw [sH]
  ring
 have hv :v9 k v := by
  have h:=(C9 (R:=k) (A:=A) (x :=(t - u)⁻¹)).mul hdiff
  rw [← Ar,← oD,G8 (sub_ne_zero.mpr htu),map_one,one_mul] at h
  exact h
 have hy :v9 k y := by
  have h:=ht'.sub ((C9 (R:=k) (A:=A) (x :=t)).mul hv)
  rwa [IT] at h
 exact hvar.elim (fun h=>h hy.isAlgebraic) (fun h=>h hv.isAlgebraic)
theorem eJ4 {k A:Type} [cy k] [Cy k]
    [lz A] [n5 k A] (y v :A)
    (hvar : ¬ p6 k y ∨ ¬ p6 k v) :
    mD (zR (σ:=Fin 2)
      (Polynomial.C.comp (aU k A))
      ![qU,uJ y+Polynomial.X*uJ v]) := by
  let f :ov (Fin 2) k →+* A[X] :=
    zR (Polynomial.C.comp (aU k A))
      ![qU,uJ y+Polynomial.X*uJ v]
  apply (PM f).mpr
  intro P hP
  let good:Set k := {t | ¬ p6 k (y+algebraMap k A t*v)}
  let box :Fin 2→Set k := ![good,Set.univ]
  have hbox (i:Fin 2) : (box i).Infinite := by
    fin_cases i
    · exact eoc y v hvar
    · exact Set.infinite_univ
  apply MvPolynomial.funext_set box hbox
  intro a ha
  have ht:a 0∈good:=ha 0 (Set.mem_univ _)
  let Yn:=y+algebraMap k A (a 0)*v
  let fixSlope :ov (Fin 2) k →+* k[X] :=
    zR uJ ![uJ (a 0),qU]
  have hfix : (Dz Yn).toRingHom.comp fixSlope =
      (oq (aU k A (a 0))).comp f := by
    apply xL
    · intro c
      simp [fixSlope,f]
    · intro i
      fin_cases i
      · simp [fixSlope,f,Yn]
      · simp [fixSlope,f,Yn]
        exact qy _ _
  have hfixP:fixSlope P=0:= by
    apply (transcendental_iff_injective.mp ht)
    change ((Dz Yn).toRingHom.comp fixSlope) P= _
    rw [hfix]
    simp [hP]
  have heval : (oq (a 1)).comp fixSlope=p9 a := by
    apply xL
    · intro c
      simp [fixSlope]
    · intro i
      fin_cases i <;> simp [fixSlope]
  rw [← heval]
  simp [hfixP]
theorem aSS {k A:Type} [cy k] [lz A] [t5 A]
    [n5 k A] [xu k A] :
    ∃ n:ℕ,y5 A=(n:vZ ℕ∞)∧J4 k A=(n:Cardinal) := by
  obtain ⟨n,g,hg_inj,hg_fin⟩:=exists_finite_inj_algHom_of_fg k A
  let B:=ov (Fin n) k
  let:n5 B A:=g.toRingHom.toAlgebra
  let:vl k B A:=PA g
  have :pz B A:=hg_fin
  have :Algebra.IsIntegral B A:=Algebra.IsIntegral.of_finite B A
  have :Kl B A:=(Hw B A).mpr hg_inj
  have hdim:y5 B=(n:vZ ℕ∞) := by
    simp [B,MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field]
  refine ⟨n,?_,?_⟩
  · apply z7
    · rw [← hdim]
      apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (aU B A))
      intro a b hab
      exact Ideal.IsIntegral.under_lt_under (R:=B) (show a.asIdeal<b.asIdeal from hab)
    · obtain ⟨l,hlen⟩:=Order.le_krullDim_iff.mp hdim.ge
      have :=l.head.isPrime
      have hle : (⊥ : nX A).under B≤l.head.asIdeal:= by
        change Ideal.comap (aU B A) ⊥ ≤ l.head.asIdeal
        rw [← RD,
          (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective B A)]
        exact bot_le
      obtain ⟨P,_,hP,hPhead⟩:=Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal
        (⊥ : nX A) hle
      let:P.IsPrime :=hP
      let:P.LiesOver l.head.asIdeal:=⟨hPhead.symm⟩
      obtain ⟨L,hL,_,_⟩:=Ideal.exists_ltSeries_of_hasGoingUp l P
      exact Order.le_krullDim_iff.mpr ⟨L,hL.trans hlen⟩
  · have h:=zf k B (A:=A)
    rw [GY (R:=B) (A:=A),wB] at h
    simpa [B,MvPolynomial.trdeg_of_isDomain] using h.symm
theorem eJ2 (k :Type) [cy k] :
  J4 k (G4 (ov (Fin 2) k))=2 := by
 let P:=ov (Fin 2) k
 let F:=G4 P
 have :JW P F:=IsLocalization.isAlgebraic _ (JM P)
 have :Kl P F:=(Hw P F).mpr
  (Gn P F)
 rw [← zf k P (A:=F),GY (R:=P) (A:=F),wB]
 simp [P]
theorem dsH {k E A B:Type}
  [cy k] [cy E] [lz A] [lz B] [t5 A] [t5 B]
  [n5 k E] [n5 k A] [n5 k B] [n5 E B] [vl k E B]
  [xu k A] [xu E B]
  (f :A[X] →ₐ[k] B) (hf :mD f)
  (hAlg : let : n5 A[X] B := f.toRingHom.toAlgebra; JW A[X] B)
  (hE :J4 k E=2) (d:ℕ)
  (hdim:y5 A=((d+1 :ℕ) :vZ ℕ∞)) :
  y5 B=(d:vZ ℕ∞) := by
 let:n5 A[X] B:=f.toRingHom.toAlgebra
 let:vl k A[X] B:=PA f
 have :Kl A[X] B:=(Hw _ _).mpr hf
 have :JW A[X] B:=hAlg
 obtain ⟨n,hdimA,htrdegA⟩:=aSS (k :=k) (A:=A)
 obtain ⟨m,hdimB,htrdegB⟩:=aSS (k :=E) (A:=B)
 have hn:n=d+1 := by exact_mod_cast hdimA.symm.trans hdim
 have hSlope :=zf k A (A:=A[X])
 rw [htrdegA,Polynomial.trdeg_of_isDomain] at hSlope
 have hSlice :=zf k A[X] (A:=B)
 rw [GY (R:=A[X]) (A:=B),wB,← hSlope] at hSlice
 have h:=zf k E (A:=B)
 rw [hE,htrdegB,← hSlice] at h
 have hm: (2+m:ℕ)=n+1 := by exact_mod_cast h
 rw [hdimB,show m=d by omega]
end bzV
end
section
namespace bzS
noncomputable section
open Polynomial
variable {M E :Type*} [cy M] [cy E] [n5 M E]
def aN1 (x y :E) :ov (Fin 3) M →+* ov (Fin 2) E :=
  zR (MvPolynomial.C.comp (aU M E))
    ![zh 0,zh 1,
      MvPolynomial.C x+MvPolynomial.X 0*MvPolynomial.C y]
private theorem cA9 (x y :E) (P:ov (Fin 3) M)
   (hP:aN1 x y P=0) (b:Fin 3→M) (hb:p9 b P≠0) :
   p6 M (x+algebraMap M E (b 0)*y) := by
 let f :ov (Fin 3) M →+* M[X] :=
   zR C ![C (b 0),C (b 1),X]
 let v :E :=x+algebraMap M E (b 0)*y
 have he : (oq (b 2)).comp f=p9 b:= by
   apply xL
   · intro c
     simp [f]
   · intro i
     fin_cases i <;> simp [f]
 have hf :f P≠0:= by
   intro hz
   apply hb
   rw [← he,RP ,hz,p5]
 let s :ov (Fin 2) E →+* E :=
   p9 ![aU M E (b 0),aU M E (b 1)]
 have hs : (Dz v).toRingHom.comp f=s.comp (aN1 x y) := by
   apply xL
   · intro c
     simp [f,s,aN1]
   · intro i
     fin_cases i <;> simp [f,s,aN1,v]
 refine ⟨f P,hf,?_⟩
 change ((Dz v).toRingHom.comp f) P=0
 rw [hs,RP ,hP,p5]
theorem efz [Cy M] (x y :E)
  (ht : ¬ (p6 M x∧p6 M y)) :
  mD (aN1 (M:=M) x y) := by
 classical
 apply (PM (aN1 (M:=M) x y)).mpr
 intro P hP
 by_contra hp
 have hex (Q:ov (Fin 3) M) (hQ:Q≠0) :
    ∃ b:Fin 3→M,p9 b Q≠0:= by
  by_contra! h
  apply hQ
  exact MvPolynomial.funext (fun b=> by rw [h b,p5])
 obtain ⟨b,hb⟩:=hex P hp
 have hlin: (zh 0-MvPolynomial.C (b 0) :ov (Fin 3) M)≠0 :=
  fun h=> by
    have he :=oj (p9 ![b 0+1,(0:M),0]) h
    simp at he
 obtain ⟨d,hd⟩:=hex (P*(zh 0-MvPolynomial.C (b 0))) (zi hp hlin)
 have hd' : p9 d P*(d 0 - b 0)≠0:= by simpa using hd
 have hdb:=right_ne_zero_of_mul hd'
 have hb_alg:=cA9 x y P hP b hb
 have hd_alg:=cA9 x y P hP d (left_ne_zero_of_mul hd')
 have hdiff :p6 M (aU M E (d 0 - b 0)*y) := by
  have h:=hd_alg.sub hb_alg
  convert h using 1
  rw [sH]
  ring
 have hy :p6 M y := by
  have h:=(SC (A:=E) ((d 0 - b 0)⁻¹)).mul hdiff
  have hn:aU M E (d 0 - b 0)≠0 :=
    (map_ne_zero_iff (aU M E) (aU M E).injective).mpr hdb
  rw [map_inv₀,← Ar,G8 hn,one_mul] at h
  exact h
 have hx :p6 M x := by
  simpa using hb_alg.sub ((SC (A:=E) (b 0)).mul hy)
 exact ht ⟨hx,hy⟩
end
end bzS
end
section
namespace aKu
open Polynomial Algebra TensorProduct
noncomputable section
variable {A:Type*} [lz A]
abbrev bRQ (F:A[X]) :=SL (AdjoinRoot.of F F.leadingCoeff)
theorem cW4 [t5 A] (F:A[X]) (hF:F.leadingCoeff≠0) :
   z9 A (bRQ F) := by
 let a :=F.leadingCoeff
 let R:=SL a
 let:t5 R:=Localization.Away.isDomain hF
 let p:=F.map (aU A R)
 obtain ⟨u,hu⟩:=IsLocalization.Away.algebraMap_isUnit (S:=R) a
 let g:=C (↑u⁻¹:R)*p
 have hg:g.Monic:= by
   apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
   change (↑u⁻¹:R)*(F.map (aU A R)).leadingCoeff=1
   rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ (hu ▸ Units.ne_zero u),
     ← hu,Units.inv_mul]
 let q:=F.map (Wl:A →ₐ[A] R ⊗[A] A).toRingHom
 let e :=Algebra.TensorProduct.rid A R R
 have hq:q.map e=p:= by
   rw [show q=F.map (Wl:A →ₐ[A] R ⊗[A] A).toRingHom from rfl,
     Xg]
   congr 1
   apply RingHom.ext
   intro x
   change e (1 ⊗ₜ[A] x)=aU A R x
   simp [e,vi]
 have hassoc:Associated (q.map e) g:= by
   rw [hq]
   exact associated_unit_mul_right _ _ (IsUnit.map uJ (u⁻¹).isUnit)
 let e₀:R ⊗[A] qJ F ≃ₐ[A] bRQ F:= by
   let:n5 (qJ F) (R ⊗[A] qJ F) :=Np
   exact (IsLocalization.Away.tensorRightEquiv (R:=A) (A:=R) (r :=a)
     (qJ F)).restrictScalars A
 let e₁:R ⊗[A] qJ F ≃ₐ[R] qJ q:=AdjoinRoot.tensorAlgEquiv F q rfl
 let e₂:qJ q ≃ₐ[R] qJ g:=AdjoinRoot.mapAlgEquiv e q g hassoc
 let:Module.Free R (qJ g) :=hg.free_adjoinRoot
 let:z9 R (qJ g) :=Module.Flat.of_free
 let:z9 A (qJ g) :=Module.Flat.trans A R (qJ g)
 exact Module.Flat.of_linearEquiv (e₀.symm.trans ((e₁.trans e₂).restrictScalars A)).toLinearEquiv
end
end aKu
end
section
namespace aKx
open scoped BigOperators nonZeroDivisors
open Module
abbrev bzg (A:Type) [lz A] (p n:ℕ) [t3 A p] :=
 (t9 A p n).range
def cxA (A:Type) [lz A] :Prop :=
  ∀ (p n:ℕ) [t3 A p] (w:nI A),
    ∃ T:pL (bzg A p n) A,T.FG∧(w:Set A)⊆T ∧
      ∀ (s :bzg A p n) (a :A),s≠0→s•a∈T→a∈T
theorem b29 (A K L:Type) [lz A] [t5 A]
    [IsPrincipalIdealRing A] [cy K] [cy L] [n5 A K] [IsFractionRing A K]
    [n5 K L] [n5 A L] [vl A K L] [RJ K L]
    (hA:cxA A) :pz A (wA A L) := by
  classical
  let E :=separableClosure K L
  let B:=wA A L
  let C:=wA A E
  have :vl A E L:=IsScalarTower.of_algebraMap_eq fun _=>rfl
  have :pz A C:=IsIntegralClosure.finite A K E C
  have :IsTorsionFree A E := .trans_faithfulSMul A K E
  have :Module.Free A C:=IsIntegralClosure.module_free A K E C
  let p:=ringExpChar L
  have :t3 L p:=ringExpChar.expChar L
  have hAL:mD (aU A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (aU K L).injective.comp (Gn A K)
  have :t3 A p:=(aU A L).expChar hAL p
  have :t3 E p:=(aU E L).expChar (aU E L).injective p
  let n:=IsPurelyInseparable.exponent E L
  let S:=bzg A p n
  let σ:A →+* S:=(t9 A p n).rangeRestrict
  let e :A ≃+* S:=RingEquiv.ofBijective σ
    ⟨fun _ _ h=>RC A p n (oj Av h),
      (t9 A p n).rangeRestrict_surjective⟩
  have :RingHomInvPair (e :A →+* S) (e.symm:S →+* A) :=Ts e
  have :RingHomInvPair (e.symm:S →+* A) (e :A →+* S) :=Ts e.symm
  have :zm S:=isNoetherianRing_of_ringEquiv A e
  let φ:L →+* E :=IsPurelyInseparable.iterateFrobenius E L p (n:=n) le_rfl
  have hφ (b:L) :aU E L (φ b)=b^p^n :=
    IsPurelyInseparable.algebraMap_iterateFrobenius E p le_rfl b
  have hmem (b:B) :φ b.val∈wA A E := by
    change v9 A (φ b.val)
    apply (IntermediateField.coe_isIntegral_iff (R:=A)).mp
    change v9 A (aU E L (φ b.val))
    rw [hφ]
    exact (show v9 A b.val from b.property).pow _
  let g:B →+* C :=
    (φ.comp (wA A L).val.toRingHom).codRestrict (wA A E).toSubring hmem
  let f :B →ₛₗ[(e :A →+* S)] C :=
    { g with
      map_smul' a b:= by
        apply vk
        apply (aU E L).injective
        change aU E L (φ (a•b.val)) =
          aU E L ((a^p^n)•φ b.val)
        simp only [vi]
        rw [hφ,mul_pow,oD,← Pr A E L,map_pow,hφ] }
  have hf :mD f := by
    intro b b' hb
    apply vk
    apply RC L p n
    change b.val^p^n=b'.val^p^n
    rw [← hφ,← hφ]
    exact oj (fun c:C=>aU E L c.val) hb
  obtain ⟨ι,b,hb⟩:=FiniteDimensional.exists_is_basis_integral A K L
  let J:=Module.Free.ChooseBasisIndex A C
  let v :ze J A C:=Module.Free.chooseBasis A C
  let w (i:ι) :B:=⟨b i,hb i⟩
  let r :B →ₛₗ[(e :A →+* S)] (J→A) :=
    (v.equivFun.toLinearMap.restrictScalars S).comp f
  have hr :mD r :=v.equivFun.injective.comp hf
  let coeffs :=(vj :nI (ι×J)).image (fun ij=>r (w ij.1) ij.2)
  obtain ⟨T,hT,hcoeffs,hsat⟩:=hA p n coeffs
  have hw (i:ι) (j:J) :r (w i) j∈T :=
    hcoeffs (Finset.mem_image.mpr ⟨(i,j),u5 _,rfl⟩)
  have hr_mem (z :B) (j:J) :r z j∈T:= by
    obtain ⟨d,hd⟩:=IsLocalization.exist_integer_multiples_of_finite A⁰ (b.repr z.val)
    choose a ha using hd
    have hdenom: (d:A)•z = ∑ i,a i•w i:= by
      apply vk
      change (d:A)•z.val=(wA A L).val (∑ i,a i•w i)
      rw [oY]
      calc
        _ = ∑ i,(b.repr ((d:A)•z.val) i)•b i:=(b.sum_repr _).symm
        _ = _:= by
          apply pC rfl
          intro i _
          have hrepr :b.repr ((d:A)•z.val) i=aU A K (a i) := by
            rw [← KH K (d:A) z.val,
              LinearEquiv.map_smul,Finsupp.smul_apply]
            exact (KH K (d:A) _).trans (ha i).symm
          rw [hrepr]
          exact KH K (a i) (b i)
    have hd0: (e :A →+* S) d≠0 :=
      e.map_ne_zero_iff.mpr (mem_nonZeroDivisors_iff_ne_zero.mp d.property)
    apply hsat ((e :A →+* S) d) _ hd0
    have h:=oy (oj r hdenom) j
    simp only [map_smulₛₗ,oY ,qx ,yQ] at h
    rw [h]
    exact Kp T (fun i _=>T.smul_mem _ (hw i j))
  have :pz S T:=Module.Finite.of_fg hT
  let q:B →ₛₗ[(e :A →+* S)] (J→T) :=
    { toFun:= fun z j=>⟨r z j,hr_mem z j⟩
      map_add' := fun a b=> by
        ext j
        exact oy (Aa r a b) j
      map_smul' := fun a b=> by
        ext j
        exact oy (map_smulₛₗ r a b) j }
  apply Module.Finite.of_injective q
  intro a b hab
  exact hr (funext fun j=>oj (fun u:J→T=>(u j:A)) hab)
end aKx
end
section
namespace aKx
open Polynomial
open scoped Polynomial
theorem cch (k :Type) [cy k] :cxA k[X] := by
  classical
  intro p n _ w
  have :t3 k p:=Polynomial.C.expChar Polynomial.C_injective p
  let R:=(t9 k p n).fieldRange
  let S:=bzg k[X] p n
  let D:=w.biUnion fun a=>a.coeffs
  let K:=Ye R (D:Set k)
  let f :K →+* k :=K.subtype
  have hr (a :k) :v9 R a := by
    apply Te (expChar_pow_pos k p n)
    exact C9 (x :=(t9 k p n).rangeRestrictField a)
  let V:Subalgebra S k[X] :=
    { (mapRingHom f).range.toSubsemiring with
      algebraMap_mem' := fun s=> by
        obtain ⟨a,ha⟩:=s.property
        let g:k →+* K:=(aU R K).comp (t9 k p n).rangeRestrictField
        change ∃ b:K[X],b.map f=(s :k[X])
        refine ⟨(expand k (p^n) a).map g,?_⟩
        rw [ Xg]
        change (expand k (p^n) a).map (t9 k p n)=(s :k[X])
        rw [map_iterateFrobenius_expand,← Oc,ha] }
  let U:Subalgebra S k[X] :=Algebra.adjoin S (insert X (C '' (D:Set k)))
  have huX:X∈U:=Algebra.subset_adjoin (Set.mem_insert _ _)
  have huC (a :k) (ha :a∈K) :C a∈U:= by
    change a∈K.toSubalgebra at ha
    change a∈(Ye R (D:Set k)).toSubalgebra at ha
    rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun a _=>(hr a).isAlgebraic)] at ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha=>exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨a,ha,rfl⟩)
    | algebraMap r =>
      obtain ⟨c,hc⟩:=r.property
      have hs :C (r :k)∈(t9 k[X] p n).range := by
        refine ⟨C c,?_⟩
        rw [Oc,← map_pow]
        exact oj C hc
      exact U.algebraMap_mem ⟨_,hs⟩
    | add a b _ _ ha hb=>simpa only [map_add] using U.add_mem ha hb
    | mul a b _ _ ha hb=>simpa only [map_mul] using U.mul_mem ha hb
  have hVU:V=U:= by
    apply z7
    · intro a ha
      obtain ⟨b,rfl⟩ : ∃ b:K[X],b.map f=a :=ha
      induction b using Polynomial.induction_on' with
      | add a b ha hb=>simpa only [Polynomial.map_add] using U.add_mem ha hb
      | monomial i c =>
        rw [Polynomial.map_monomial,← Kv]
        exact U.mul_mem (huC c c.property) (U.pow_mem huX i)
    · apply Algebra.adjoin_le
      rintro _ (rfl | ⟨c,hc,rfl⟩)
      · exact ⟨X,Polynomial.map_X f⟩
      · exact ⟨C ⟨c,WX R _ hc⟩,Polynomial.map_C f⟩
  refine ⟨V.toSubmodule,?_,?_,?_⟩
  · rw [hVU]
    apply fg_adjoin_of_finite ((D.finite_toSet.image C).insert X)
    intro a _
    apply Te (expChar_pow_pos k[X] p n)
    exact C9 (x :=(t9 k[X] p n).rangeRestrict a)
  · intro a ha
    change a∈Polynomial.lifts f
    apply (Polynomial.lifts_iff_coeffs_subset_range a).mpr
    intro c hc
    have hD:c∈D:=Finset.mem_biUnion.mpr ⟨a,ha,hc⟩
    exact ⟨⟨c,WX R _ hD⟩,rfl⟩
  · intro s a hs0 hs
    change (s :k[X])*a∈V at hs
    obtain ⟨s',hs'⟩ : ∃ s' : K[X],s'.map f=(s :k[X]) :=V.algebraMap_mem s
    obtain ⟨b,hb⟩ : ∃ b:K[X],b.map f=(s :k[X])*a :=hs
    have hd:s'.map f∣b.map f :=⟨a,by rw [hb,hs']⟩
    obtain ⟨a',ha'⟩:=(Polynomial.map_dvd_map' f).mp hd
    refine ⟨a',?_⟩
    change a'.map f=a
    apply Au (show (s :k[X])≠0 from fun h=>hs0 (vk h))
    rw [← hs',← Qy ,← ha',hb,hs']
end aKx
end
section
namespace aRV
noncomputable section
open IsLocalRing KaehlerDifferential MvPolynomial
open scoped TensorProduct
variable {k R:Type*} [cy k] [lz R] [t4 R] [n5 k R]
private theorem Cj [FK k R]
   [FK k (pG R)] {n:ℕ}
   (b:ze (Fin n) (pG R) (x7 R)) :
   ∃ (f :R →ₐ[k] gQ (pG R) n 2),
     (∀ r,constant (pG R) n 2 (by decide) (f r)=residue R r) ∧
     ∀ i,∃ x∈lI R,f x=jet (pG R) n 2 (X i) := by
 let K:=pG R
 let S:=gQ K n 2
 let J:=aug K n 2
 obtain ⟨l,hl⟩:=(Algebra.FormallySmooth.iff_split_injection (R:=k)
   (P:=R) (A:=K) C4).mp xI
 have hk :qG (aU R K)=lI R:= by
   rw [ResidueField.algebraMap_eq,ker_residue]
 let e : (qG (aU R K)).Cotangent ≃ₗ[R] x7 R :=
   Ideal.Cotangent.equivOfEq _ _ hk
 let τ:Ω[R⁄k] →ₗ[R] K ⊗[R] Ω[R⁄k] :=TensorProduct.mk R K _ 1
 let D₀:Derivation k R (x7 R) :=
   (e.toLinearMap.comp (l.comp τ)).compDer (D k R)
 let v (i:Fin n) :J:=⟨jet K n 2 (X i),dqI K n 2 i⟩
 let L:x7 R →ₗ[K] J:=b.constr K v
 let δ:Derivation k R J:=(L.restrictScalars R).compDer D₀
 let f :=liftOfDerivationToSquareZero J (bbP K n 2) δ
 refine ⟨f,?_,?_⟩
 · intro r
   rw [Nj,Aa]
   have hδ: (δ r :S)∈RingHom.ker (constant K n 2 (by decide)) := by
     rw [b62]
     exact (δ r).2
   rw [RingHom.mem_ker.mp hδ,zero_add]
   exact bYD K n 2 (by decide) (residue R r)
 · intro i
   obtain ⟨x,hx⟩:=(lI R).toCotangent_surjective (b i)
   let x' : qG (aU R K) :=⟨x,by
     rw [ResidueField.algebraMap_eq,ker_residue]
     exact x.2⟩
   have hD:D₀ (x :R)=b i:= by
     change e (l (1 ⊗ₜ[R] D k R (x :R)))=b i
     rw [← kerCotangentToTensor_toCotangent k R K x']
     have h:=DFunLike.congr_fun hl ((qG (aU R K)).toCotangent x')
     change l (kerCotangentToTensor k R K _)= _ at h
     rw [h,LinearMap.id_apply]
     dsimp only [e]
     rw [Ideal.Cotangent.equivOfEq_toCotangent]
     exact hx
   refine ⟨x,x.2,?_⟩
   rw [Nj]
   change (L (D₀ (x :R)) :S)+algebraMap K S (residue R x)= _
   dsimp only [L]
   rw [hD,Module.Basis.constr_basis,(JQ _).mpr x.2,p5 ,wB]
private theorem eu3 {S:Type*} [lz S] (J I:nX S) (t:ℕ)
    (hJ:J^t = ⊥) (h:J≤I ⊔ J^2) :J≤I:= by
  have step (s :ℕ) :J^(s+1)≤I ⊔ J^(s+1+1) := by
    calc
      J^(s+1)=J*J^s :=pow_succ' _ _
      _≤(I ⊔ J^2)*J^s :=Ideal.mul_mono_left h
      _≤I ⊔ J^(s+1+1) := by
        rw [Ideal.sup_mul,← vG,show 2+s=s+1+1 by omega]
        exact sup_le_sup (Ideal.mul_le_left) le_rfl
  have all (s :ℕ) :J≤I ⊔ J^s := by
    induction s with
    | zero=>simp
    | succ s ih =>
      cases s with
      | zero=>simpa only [Nat.zero_add,pow_one] using (le_sup_right:J≤I ⊔ J)
      | succ s=>exact ih.trans (sup_le le_sup_left (step s))
  simpa [hJ] using all t
omit [t4 R] in
private theorem gxM {S K:Type*} [lz S] [lz K]
    (f :R →+* S) (a :S →+* K) (I:nX R) (J:nX S) (t:ℕ)
    (hJ:J^t = ⊥) (hmap :I.map f=J)
    (ha :qG a=J) (hs :yU (a.comp f)) :
    Function.Surjective f := by
  let:n5 R S:=f.toAlgebra
  let A:pL R S:=In (IU R S)
  have htop:A ⊔ I•(⊤ : pL R S) = ⊤ := by
    rw [UY ,show aU R S=f from rfl,hmap]
    apply eq_top_iff.mpr
    intro y _
    obtain ⟨x,hx⟩:=hs (a y)
    refine Submodule.mem_sup.mpr ⟨f x,⟨x,rfl⟩,y - f x,?_,by ring⟩
    rw [Submodule.restrictScalars_mem,← ha,FV,sH]
    exact sub_eq_zero.mpr hx.symm
  have hs' (s :ℕ) :A ⊔ I ^s•(⊤ : pL R S) = ⊤ := by
    induction s with
    | zero=>rw [pow_zero,Ideal.one_eq_top,Submodule.top_smul,sup_top_eq]
    | succ s ih =>
      calc
        A ⊔ I ^(s+1)•(⊤ : pL R S)
            = A ⊔ I•(I ^s•(⊤ : pL R S)) := by rw [pow_succ',mul_smul]
        _=A ⊔ I•(A ⊔ I ^s•(⊤ : pL R S)) := by
          rw [Submodule.smul_sup,← sup_assoc,sup_eq_left.mpr (Submodule.smul_le_right:I•A≤A)]
        _ = ⊤ := by rw [ih,htop]
  have hzero :I ^t•(⊤ : pL R S) = ⊥ := by
    rw [UY ,show aU R S=f from rfl,II,hmap,hJ]
    rfl
  have hA:=hs' t
  rw [hzero,sup_bot_eq] at hA
  exact LinearMap.range_eq_top.mp hA
theorem d4n [FK k R]
   [FK k (pG R)] {n t:ℕ} (ht:2≤t)
   (b:ze (Fin n) (pG R) (x7 R)) :
   ∃ f : (R ⧸ lI R^t) →+* gQ (pG R) n t,
     Function.Surjective f := by
 let K:=pG R
 let S:=gQ K n t
 let J:=aug K n t
 let a :S →+* K:=constant K n t (by omega)
 let π:S →ₐ[k] gQ K n 2 :=
   Ideal.Quotient.factorₐ k (Fa ht)
 have hπ:qG π=J^2 := by
   change qG (Ideal.Quotient.factor (Fa ht :
     Vars K n^t≤Vars K n^2))=J^2
   rw [Ideal.Quotient.factor_ker,II]
 have hnil:IsNilpotent (qG π) := by
   rw [hπ]
   refine ⟨t,?_⟩
   change (J^2)^t=(⊥ : nX S)
   rw [← pow_mul,qy 2 t,pow_mul,show J^t = ⊥ from bbP K n t]
   exact Ideal.bot_pow (by decide)
 have hs :yU π :=
   Ideal.Quotient.factor_surjective (Fa ht)
 obtain ⟨f₂,hconst,hx⟩:=Cj (k :=k) b
 let f :=Algebra.FormallySmooth.liftOfSurjective f₂ π hs hnil
 have hf (r :R) :π (f r)=f₂ r :=
   Algebra.FormallySmooth.liftOfSurjective_apply f₂ π hs hnil r
 have hconst' (r :R) :a (f r)=residue R r := by
   have ha (y :S) :a y=constant K n 2 (by decide) (π y) := by
     obtain ⟨p,rfl⟩:=uh  y
     rfl
   rw [ha,hf,hconst]
 have hker :qG a=J:=b62 K n t _
 have hm: (lI R).map f.toRingHom≤J:= by
   apply Ideal.map_le_iff_le_comap.mpr
   intro r hr
   rw [Ideal.mem_comap,← hker,FV]
   change a (f r)=0
   rw [hconst']
   exact (JQ _).mpr hr
 have hmap : (lI R).map f.toRingHom=J:= by
   refine z7 hm (eu3 J _ t (bbP K n t) ?_)
   refine ((duX K n t).le).trans (Ideal.span_le.mpr ?_)
   rintro _ ⟨i,rfl⟩
   obtain ⟨x,hx₁,hx₂⟩:=hx i
   refine Submodule.mem_sup.mpr ⟨f x,NX _ hx₁,jet K n t (X i) - f x,?_,
     by ring⟩
   change _∈J^2
   rw [← hπ,FV,sH,G0 ,hf,hx₂]
   rfl
 have hsurj:=gxM f.toRingHom a _ J t (bbP K n t)
   hmap hker (fun c=> by
     obtain ⟨r,hr⟩:=C4 (R:=R) c
     exact ⟨r,(hconst' r).trans hr⟩)
 have hkill:lI R^t≤qG f.toRingHom:= by
   rw [← Ideal.map_eq_bot_iff_le_ker,II,hmap]
   exact bbP K n t
 exact ⟨Ideal.Quotient.lift _ f.toRingHom hkill,
   hsurj.of_comp (g:=p7 _)⟩
end
end aRV
end
section
namespace aRV
noncomputable section
open MvPolynomial IsLocalRing
open scoped BigOperators
private abbrev Mono (n t:ℕ) :=Σ j:Fin t,Sym (Fin n) j.val
private def exponent {n t:ℕ} (a :Mono n t) :Fin n →₀ ℕ:=a.2.val.toFinsupp
private theorem bdB {n t:ℕ} (a :Mono n t) :
  (exponent a).degree=a.1.val := by
 change (a.2.val.toFinsupp).sum (fun _ j=>j)=a.1.val
 exact (Multiset.toFinsupp_sum_eq _).trans a.2.property
private theorem exponent_injective (n t:ℕ) :mD (@exponent n t) := by
 rintro ⟨d,a⟩ ⟨e,b⟩ h
 have hde :d=e :=Fin.ext ((bdB ⟨d,a⟩).symm.trans
  ((oj Finsupp.degree h).trans (bdB ⟨e,b⟩)))
 subst e
 exact oj (Sigma.mk d) (vk (Multiset.toFinsupp.injective h))
private theorem card_mono (n t:ℕ) (ht:0<t) :
  lV (Mono n t)=(t+n - 1).choose n:= by
 classical
 rw [Fintype.card_sigma]
 simp only [Sym.card_sym_eq_multichoose,t8 ,Vl]
 obtain ⟨u,rfl⟩:=Yi ht.ne'
 rw [Nat.sum_range_multichoose]
 congr 1
 omega
private theorem evQ (K:Type*) [cy K] (n t:ℕ) (ht:0<t) :
    ((t+n - 1).choose n:ℕ∞)≤t7 K (gQ K n t) := by
  classical
  let coeff (a :Mono n t) :gQ K n t →ₗ[K] K :=
    ((Vars K n^t).restrictScalars K).liftQ (lcoeff K (exponent a)) (by
      intro p hp
      exact (mem_pow_idealOfVars_iff' t p).mp hp _ (by
        rw [bdB]
        exact a.1.isLt))
  let f :gQ K n t →ₗ[K] (Mono n t→K) :=LinearMap.pi coeff
  have hsurj:yU f := by
    intro c
    refine ⟨jet K n t (∑ a,monomial (exponent a) (c a)),?_⟩
    funext a
    change (∑ b,monomial (exponent b) (c b)).coeff (exponent a)=c a
    rw [coeff_sum,Finset.sum_eq_single a]
    · simp
    · intro b _ hba
      simp [coeff_monomial,(exponent_injective n t).ne hba]
    · simp
  have h:=SU f hsurj
  rw [Module.length_pi_of_fintype] at h
  simpa [card_mono n t ht] using h
theorem evK (K:Type*) [cy K] (n t:ℕ) (ht:0<t) :
   ((t+n - 1).choose n:ℕ∞)≤t7 (gQ K n t) (gQ K n t) := by
 let S:=gQ K n t
 let J:=aug K n t
 let f :=constant K n t ht
 have hf :yU f :=dPb K n t ht
 have hker :qG f=J:=b62 K n t ht
 have hmax :J.IsMaximal:=hker ▸ RingHom.ker_isMaximal_of_surjective f hf
 have hnil:nilradical S=J:= by
   let:J.IsPrime :=hmax.isPrime
   refine z7 (nilradical_le_prime J) (fun x hx => ?_)
   apply mem_nilradical.mpr
   refine ⟨t,?_⟩
   exact Ideal.mem_bot.mp ((show J^t = ⊥ from bbP K n t) ▸ MK hx t)
 let: (nilradical S).IsMaximal:=hnil.symm ▸ hmax
 let:t4 S:=IsLocalRing.of_isMaximal_nilradical S
 have hm:lI S=J:=(IsLocalRing.eq_maximalIdeal hmax).symm
 let:IsLocalHom (aU K S) :=⟨fun x hx=> by
   apply isUnit_iff_ne_zero.mpr
   rintro rfl
   simp at hx⟩
 have hres :yU (aU K (pG S)) := by
   intro y
   obtain ⟨x,rfl⟩:=C4 y
   refine ⟨f x,?_⟩
   change residue S (aU K S (f x))=residue S x
   rw [← G0 ,← sH,JQ,hm,← hker,
     FV,sH,bYD,zc]
 have hlen:t7 (pG K) (pG S)=1 := by
   rw [← Ob (M:=pG S) (C4 (R:=K)),
     Ob hres,Module.length_eq_one]
 have h:=evQ K n t ht
 rwa [IsLocalRing.length_restrictScalars K S S,hlen,mul_one] at h
end
end aRV
end
section
namespace cu
noncomputable section
open MvPolynomial Finset
variable {F:Type*} [cy F]
def QN (p:ℕ) (e :Fin 2 →₀ ℕ) :ℕ:=e 0+p*e 1
def Vg (p:ℕ) :ov (Fin 2) F →ₐ[F] Polynomial F :=
 aeval ![qU,qU^p]
theorem bqK (p:ℕ) (hp:0<p) :
  Gk (QN p) {e :Fin 2 →₀ ℕ | e 0<p} := by
 intro e he f hf h
 have hm:=oj (fun n:ℕ=>n%p) h
 simp only [QN,XG,F9 he,F9 hf] at hm
 have hmul :p*e 1=p*f 1 := by unfold QN at h; omega
 have h1 :e 1=f 1 :=MS hp hmul
 ext i
 fin_cases i <;> assumption
theorem b34 (p:ℕ) (e :Fin 2 →₀ ℕ) (a :F) :
  Vg p (monomial e a)=yo (QN p e) a := by
 rw [Vg,aeval_monomial]
 simp [Nr,Qx ,QN,← pow_mul,← vG,Kv]
theorem b32 (p:ℕ) (hp:0<p) (Q:ov (Fin 2) F)
   (hdegree :Q.degreeOf 0<p) (e :Fin 2 →₀ ℕ) (he :e∈Q.support) :
   (Vg p Q).coeff (QN p e)=Q.coeff e := by
 classical
 have hex :Vg p Q=∑ f∈Q.support,yo (QN p f) (Q.coeff f) := by
   conv_lhs=>rw [Q.as_sum]
   simp only [oY ,b34]
 rw [hex,TZ]
 trans ((yo (QN p e) (Q.coeff e)).coeff (QN p e))
 · apply Xp e he
   intro f hf hfe
   rw [R9,ite_eq_right]
   intro h
   apply hfe
   apply bqK p hp
   · exact (u8 0 hf).trans_lt hdegree
   · exact (u8 0 he).trans_lt hdegree
   · exact h
 · simp
theorem bG0 (p:ℕ) (hp:0<p) (Q:ov (Fin 2) F)
  (hQ:Q≠0) (hdegree :Q.degreeOf 0<p) :Vg p Q≠0:= by
 obtain ⟨e,he⟩:=support_nonempty.mpr hQ
 intro hz
 have hh:=b32 p hp Q hdegree e he
 rw [hz,QL] at hh
 exact (mem_support_iff.mp he) hh.symm
theorem b33 (p a b:ℕ) (Q:ov (Fin 2) F)
  (hA:Q.degreeOf 0≤a) (hB:Q.degreeOf 1≤b) :
  (Vg p Q).natDegree≤a+p*b:= by
 apply (Vs ![qU,qU^p] Q).trans
 apply Finset.sup_le
 intro e he
 have h0:=(u8 0 he).trans hA
 have h1 :=(u8 1 he).trans hB
 simp [Pj,N0 ,Pc,pQ]
 nlinarith
theorem bqt (p a b:ℕ) (hp:0<p)
    (Q:ov (Fin 2) F) (hQ:Q≠0) (hA:Q.degreeOf 0≤a) (ha :a<p)
    (hB:Q.degreeOf 1≤b) (Γ:nI F)
    (hΓ : ∀ γ∈Γ,p9 ![γ,γ^p] Q=0) :Γ.card≤a+p*b:= by
  have hn:=bG0 p hp Q hQ (hA.trans_lt ha)
  have hcard:Γ.card≤(Vg p Q).natDegree := by
    apply Fz
    intro γ hγ
    apply (xW hn).mpr
    have he : (Vg p Q).eval γ=p9 ![γ,γ^p] Q:= by
      have hmap : (oq γ).comp (Vg (F:=F) p).toRingHom=
          p9 ![γ,γ^p] := by
        apply xL
        · intro c
          simp [Vg]
        · intro i
          fin_cases i <;> simp [Vg]
      exact P7 hmap Q
    change (Vg p Q).eval γ=0
    rw [he]
    exact hΓ γ hγ
  exact hcard.trans (b33 p a b Q hA hB)
end
end cu
end
section
namespace BN
noncomputable section
open MvPolynomial Finset
variable {F:Type*} [cy F]
def QN (p:ℕ) (e :Fin 2 →₀ ℕ) :ℕ:=e 0+p*e 1
def Vg (p:ℕ) :ov (Fin 2) F →ₐ[F] Polynomial F :=
 aeval ![qU,qU^p]
theorem bqK (p:ℕ) (hp:0<p) :
  Gk (QN p) {e :Fin 2 →₀ ℕ | e 0<p} := by
 intro e he f hf h
 have hm:=oj (fun n:ℕ=>n%p) h
 simp only [QN,XG,F9 he,F9 hf] at hm
 have hmul :p*e 1=p*f 1 := by unfold QN at h; omega
 have h1 :e 1=f 1 :=MS hp hmul
 ext i
 fin_cases i <;> assumption
theorem b34 (p:ℕ) (e :Fin 2 →₀ ℕ) (a :F) :
  Vg p (monomial e a)=yo (QN p e) a := by
 rw [Vg,aeval_monomial]
 simp [Nr,Qx ,QN,← pow_mul,← vG,Kv]
theorem b32 (p:ℕ) (hp:0<p) (Q:ov (Fin 2) F)
   (hdegree :Q.degreeOf 0<p) (e :Fin 2 →₀ ℕ) (he :e∈Q.support) :
   (Vg p Q).coeff (QN p e)=Q.coeff e := by
 classical
 have hex :Vg p Q=∑ f∈Q.support,yo (QN p f) (Q.coeff f) := by
   conv_lhs=>rw [Q.as_sum]
   simp only [oY ,b34]
 rw [hex,TZ]
 trans ((yo (QN p e) (Q.coeff e)).coeff (QN p e))
 · apply Xp e he
   intro f hf hfe
   have hdistinct :QN p f≠QN p e := by
     intro h
     apply hfe
     apply bqK p hp
     · exact (u8 0 hf).trans_lt hdegree
     · exact (u8 0 he).trans_lt hdegree
     · exact h
   simp [R9,hdistinct]
 · simp
theorem bG0 (p:ℕ) (hp:0<p) (Q:ov (Fin 2) F)
  (hQ:Q≠0) (hdegree :Q.degreeOf 0<p) :Vg p Q≠0:= by
 obtain ⟨e,he⟩:=support_nonempty.mpr hQ
 intro hz
 have hh:=b32 p hp Q hdegree e he
 rw [hz,QL] at hh
 exact (mem_support_iff.mp he) hh.symm
theorem b33 (p a b:ℕ) (Q:ov (Fin 2) F)
  (hA:Q.degreeOf 0≤a) (hB:Q.degreeOf 1≤b) :
  (Vg p Q).natDegree≤a+p*b:= by
 apply (Vs ![qU,qU^p] Q).trans
 apply Finset.sup_le
 intro e he
 have h0:=(u8 0 he).trans hA
 have h1 :=(u8 1 he).trans hB
 simp [Pj,N0 ,Pc,pQ]
 nlinarith
theorem bqt (p a b:ℕ) (hp:0<p)
    (Q:ov (Fin 2) F) (hQ:Q≠0) (hA:Q.degreeOf 0≤a) (ha :a<p)
    (hB:Q.degreeOf 1≤b) (Γ:nI F)
    (hΓ : ∀ γ∈Γ,p9 ![γ,γ^p] Q=0) :Γ.card≤a+p*b:= by
  have hn:=bG0 p hp Q hQ (hA.trans_lt ha)
  have hcard:Γ.card≤(Vg p Q).natDegree := by
    apply Fz
    intro γ hγ
    apply (xW hn).mpr
    have he : (Vg p Q).eval γ=p9 ![γ,γ^p] Q:= by
      have hmap : (oq γ).comp (Vg (F:=F) p).toRingHom=
          p9 ![γ,γ^p] := by
        apply xL
        · intro c
          simp [Vg]
        · intro i
          fin_cases i <;> simp [Vg]
      exact P7 hmap Q
    change (Vg p Q).eval γ=0
    rw [he]
    exact hΓ γ hγ
  exact hcard.trans (b33 p a b Q hA hB)
end
end BN
end
section
namespace aFY
noncomputable section
open IsLocalRing
theorem ew9 {R:Type*} [lz R] [t4 R] [zm R]
    {x f g:R} {n:ℕ} (hx :x∈lI R)
    (hd:1<(lI R).height)
    (hf :f∈(lI R)^n ⊔ nq {x})
    (hg:g∈(lI R)^n ⊔ nq {x}) :
    (n:ℕ∞)≤t7 R (R ⧸ nq {f,g}) := by
  let m:=lI R
  let A:nX R:=nq {x}
  let J (i:ℕ) :=A ⊔ m^i
  have hno (i:ℕ) : ¬ m^i≤A:= by
    intro h
    have hmin:m∈A.minimalPrimes := by
      refine ⟨⟨xI,(Gj m).mpr hx⟩,?_⟩
      intro P hP _
      exact fun z hz=>hP.1.mem_of_pow_mem i (hP.2 (h (MK hz i)))
    let _:A.IsPrincipal:=⟨⟨x,rfl⟩⟩
    exact (not_le_of_gt hd)
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing A hmin)
  have hstep (i:ℕ) :J (i+1)<J i:= by
    refine lt_of_le_of_ne (sup_le_sup_left (Fa (Nat.le_succ i)) _) ?_
    intro he
    apply hno i
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (I:=m) (IsNoetherian.noetherian _)
    · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · change m^i≤A ⊔ m•m^i
      rw [pQ,← pow_succ']
      change m^i≤J (i+1)
      rw [he]
      exact X4
  have hlength (i:ℕ) : (i:ℕ∞)≤FU (J i:pL R R) := by
    induction i with
    | zero=>simp
    | succ i ih =>
        rw [Nat.cast_succ]
        exact (add_le_add_left ih 1).trans
          (Order.coheight_add_one_le (show (J (i+1) :pL R R)<J i from hstep i))
  rw [Sv]
  apply (hlength n).trans
  apply Order.coheight_anti
  apply Ideal.span_le.mpr
  simpa [J,A,m,Set.insert_subset_iff,Set.singleton_subset_iff,sup_comm] using And.intro hf hg
def triangle :ℕ→ℕ
 | 0=>0
 | k+1=>triangle k+(k+1)
private theorem bih (k :ℕ) :2*triangle k=k*(k+1) := by
 induction k with
 | zero=>rfl
 | succ k ih =>
    change 2*(triangle k+(k+1))=(k+1)*(k+1+1)
    nlinarith
private theorem gEk (k :ℕ) :
  triangle (k+k+1)=(k+1)^2+(triangle k+triangle k) := by
 have h:=bih k
 have H :=bih (k+k+1)
 nlinarith
def a5U {R:Type*} [lz R] (A B:nX R) (x :R)
    (hx : ∀ r∈A,r*x∈B) : (R ⧸ A) →ₗ[R] (R ⧸ B) :=
  A.liftQ ((LO :R →ₗ[R] R).smulRight (p7 B x)) (by
    intro r hr
    simpa [vi ,← oD,Ml] using hx r hr)
theorem aV1 {R:Type*} [lz R] (A B:nX R) (x :R)
  (hx : ∀ r∈A,r*x∈B) (r :R) :
  a5U A B x hx (p7 A r)=p7 B (r*x) := by
 change r•p7 B x= _
 simp [vi]
theorem guq {R:Type*} [lz R] (m:nX R)
    (hh : ∀ i,t7 R (R ⧸ m^i)=(triangle i:ℕ∞))
    {f g:R} {n:ℕ} (hn:0<n) (hf :f∈m^n) (hg:g∈m^n) :
    (↑(n^2 :ℕ) :ℕ∞)≤t7 R (R ⧸ nq {f,g}) := by
  obtain ⟨k,rfl⟩:=Yi hn.ne'
  let T:=m^(k+k+1)
  let J:nX R:=nq {f,g}
  have hmul (x :R) (hx :x∈m^(k+1)) (r :R) (hr :r∈m^k) :
      r*x∈T:= by
    have h:=VS hr hx
    rwa [← vG,← Nat.add_assoc] at h
  let F:=a5U (m^k) T f (hmul f hf)
  let G:=a5U (m^k) T g (hmul g hg)
  let H :=LinearMap.coprod F G
  let q:=MO (show (T:pL R R)≤T ⊔ J from G7)
  have hker :oK q=In H := by
    ext z
    obtain ⟨z,rfl⟩:=uh z
    change p7 (T ⊔ J) z=0↔p7 T z∈In H
    rw [Ml]
    constructor
    · rintro hz
      obtain ⟨a,ha,b,hb,rfl⟩:=Submodule.mem_sup.mp hz
      obtain ⟨c,d,rfl⟩:=Ideal.mem_span_pair.mp hb
      refine ⟨(p7 _ c,p7 _ d),?_⟩
      simp [H,F,G,aV1,Aa ,
        Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    · rintro ⟨⟨c,d⟩,he⟩
      obtain ⟨c,rfl⟩:=uh c
      obtain ⟨d,rfl⟩:=uh d
      have he' : p7 T (c*f+d*g)=p7 T z := by
        simpa [H,F,G,aV1,Aa] using he
      rw [Ideal.Quotient.eq] at he'
      have hz :z=(-(c*f+d*g - z))+(c*f+d*g) := by ring
      rw [hz]
      exact (T ⊔ J).add_mem (PD (T.neg_mem he'))
        (XB (Ideal.mem_span_pair.mpr ⟨c,d,rfl⟩))
  have hq:=Module.length_eq_add_of_exact (oK q).subtype q
    (Submodule.subtype_injective _) (SD _)
    (LinearMap.exact_subtype_ker_map q)
  have hsmall:=SU H.rangeRestrict H.surjective_rangeRestrict
  rw [← hker,Module.length_prod,hh] at hsmall
  have hsum: (↑((k+1)^2 :ℕ) :ℕ∞)+((triangle k :ℕ∞)+triangle k) ≤
      t7 R (R ⧸ (T ⊔ J:nX R))+((triangle k :ℕ∞)+triangle k) := by
    rw [← zg ,← zg ,← gEk,← hh]
    change t7 R (R ⧸ T)≤_
    rw [hq,zg ,add_comm (t7 R ↥(oK q))]
    exact add_le_add_right hsmall _
  exact ((ENat.add_le_add_iff_right (by rw [← Nat.cast_add]; exact ENat.natCast_ne_top _)).mp hsum).trans
    (SU  (MO  (show J≤T ⊔ J from X4 ))
      (SD  _))
end
end aFY
end
