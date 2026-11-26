import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdAA
import ProximityPrize.SubmissionLower.DdAE
import ProximityPrize.SubmissionLower.DdBG
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

section Merged6967_DdZ3EWiUc
set_option Elab.async false























































set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open _root_ renaming AddCommGroup→vj,AddMonoidAlgebra.single→t9,AddMonoidAlgebra.single_mul_single→Av,AlgEquiv.apply_symm_apply→qy,AlgHom.coe_ringHom_injective→G7,AlgHom.commutes→yo,AlgHom.id→wB,Algebra→c9,Algebra.IsAlgebraic→GB,Algebra.TensorProduct.cancelBaseChange→GR,Algebra.TensorProduct.comm→yJ,Algebra.TensorProduct.comm_tmul→G5,Algebra.TensorProduct.includeRight→Gn,Algebra.TensorProduct.lift_tmul→Cy,Algebra.TensorProduct.map→zm,Algebra.TensorProduct.tmul_mul_tmul→zi,Algebra.algebraMap→aU,Algebra.ofId→yB,AlgebraicIndependent→zg,CommRing→n5,DFunLike.congr_fun→zh,Field→mD,Finset.mem_image_of_mem→Fz,Finset.mem_singleton→Et,Finset.mem_univ→yU,Finset.smul_sum→wA,Finset.sum_congr→uz,Finsupp.comapDomain_sumElim_comapDomain→G0,Finsupp.optionElim_some→FV,Finsupp.single→zf,Finsupp.weight→ oY,Finsupp.weight_apply→Du,Finsupp.weight_eq_sum→Aa,Fintype.sum_option→z7,Fintype.sum_sum_type→Gk,Fintype.univ_bool→Ef,Function.Injective→sS,Function.Surjective→G2,Function.iterate_succ_apply'→EK,Ideal→ oD,Ideal.Quotient.eq_zero_iff_mem→Ar,Ideal.Quotient.mk→ ox,Ideal.Quotient.mkₐ→G9,Ideal.map_map→wY,Ideal.mem_span_singleton_sup→Gr,Ideal.span→t3
open _root_ renaming IsAlgebraic→zS,IsDomain→th,IsFractionRing→t4,IsFractionRing.injective→wR,IsLocalization→uh,IsLocalization.mk'_mem_map_algebraMap_iff→Fa,IsLocalization.mul_mk'_eq_mk'_of_mul→FK,IsScalarTower→vh,IsScalarTower.algebraMap_apply→Dz,IsScalarTower.of_algebraMap_eq→u9,IsScalarTower.toAlgHom→vk,LinearMap.finrank_le_finrank_of_surjective→G6,Module.Finite→ oZ,Module.Finite.equiv→y5,Module.Finite.of_surjective→Ea,Module.finBasis→xL,Module.finrank→pG,MvPolynomial→lJ,MvPolynomial.C→nq,MvPolynomial.X→cy,MvPolynomial.affineHilbertPolynomial→vl,MvPolynomial.algebraMap_eq→t7,MvPolynomial.algebraMvPolynomial→Bf,MvPolynomial.algebraTensorAlgEquiv→u5,MvPolynomial.algebraTensorAlgEquiv_tmul→FR,MvPolynomial.coeff_weightedHomogeneousComponent→Eg,MvPolynomial.commAlgEquiv→t5,MvPolynomial.eval→qz,MvPolynomial.eval₂Hom_C→vH,MvPolynomial.eval₂Hom_X'→G4,MvPolynomial.induction_on'→EP,MvPolynomial.isLocalization→Dw,MvPolynomial.isWeightedHomogeneous_X→zk,MvPolynomial.map→lI,MvPolynomial.map_X→qm,MvPolynomial.map_map→C4,MvPolynomial.mem_restrictBidegree→qG,MvPolynomial.mem_restrictBidegree_iff_weightedTotalDegree_le→Au,MvPolynomial.mem_support_iff→G8,MvPolynomial.monomial→ oj,MvPolynomial.monomial_add_single→xu,MvPolynomial.mul_mem_restrictBidegree→pL,MvPolynomial.optionEquivLeft→u8,MvPolynomial.pderiv_eq_zero_of_degreeOf_eq_zero→G3,MvPolynomial.quotientBidegreeLE→vG,MvPolynomial.renameEquiv_apply→z8,MvPolynomial.restrictBidegree→sH,MvPolynomial.ringHom_ext→v8
open _root_ renaming MvPolynomial.smul_eq_C_mul→GF,MvPolynomial.support_X→Dv,MvPolynomial.support_map_subset→C9,MvPolynomial.weightedHomogeneousComponent→uJ,MvPolynomial.weightedTotalDegree_pderiv_le_sub→F9,Nat.add_comm→p5,Nat.add_left_comm→FU,Nat.add_sub_of_le→G1,Nat.eq_zero_of_le_zero→Gj,Nat.mul_le_mul_left→Df,Nat.sub_le_sub_right→Ee,Nat.zero_add→uW,Option→lV,Polynomial→ oq,Polynomial.C→ ov,Polynomial.X→pQ,Polynomial.aeval→ oy,Polynomial.aeval_C→xI,Polynomial.aeval_X→zE,Polynomial.degreeLT→xm,Polynomial.derivative_map→FQ,Polynomial.eval_map→ze,Polynomial.le_natDegree_of_ne_zero→Gi,Polynomial.map→x7,Polynomial.ringHom_ext→C5,Prod.mk_add_mk→yL,Prod.snd_sum→zc,RingHom.congr_fun→t8,RingHom.ext→vi,Set.range→p9,Submodule.span→vw,Submodule.subset_span→xW,Submodule.sum_mem→GY,Submonoid→v9,Submonoid.powers→yQ,Subsingleton.elim→yl,congrArg→ oz,inferInstance→vZ,map_add→pC,map_mul→nI,map_ne_zero_iff→zR,map_one→pU,map_pow→sI,map_sub→p7,map_sum→pz,map_zero→ oK
open _root_ renaming mul_assoc→qJ,mul_comm→qx,mul_one→qM,nonZeroDivisors→zd,nonZeroDivisors.ne_zero→z9,one_mul→p6
set_option autoImplicit true
section
namespace aqf
noncomputable section
open DQ ane
end
end aqf
end
section
namespace aR1
noncomputable section
open akS
open scoped Polynomial TensorProduct
variable {F A:Type} [mD F] [n5 A] [c9 F A]
end
end aR1
end
section
namespace czC
noncomputable section
open cu DQ ane aqf MvPolynomial
open scoped BigOperators TensorProduct
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
end
end czy
end
section
namespace vq
noncomputable section
open DdK1 cu MN MvPolynomial
open scoped Polynomial BigOperators
end
end vq
end
section
namespace aZa
noncomputable section
open DdK1 cu DQ vq MvPolynomial
open scoped Polynomial
variable {n:ℕ}
end
end aZa
end
section
namespace czx
open aiO
open scoped TensorProduct nonZeroDivisors
noncomputable section
set_option backward.isDefEq.respectTransparency false
end
end czx
end
section
namespace czr
noncomputable section
open cu Cu
open MvPolynomial
variable (C₀:sQ)
end
end czr
end
section
namespace MN
noncomputable section
open Finset DdK1 MvPolynomial
open scoped BigOperators Polynomial
theorem aM6 {k σ:Type*} [mD k] [Finite σ]
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
end
end czB
end
section
namespace aZa
noncomputable section
open DdK1 cu DQ MvPolynomial
open scoped Polynomial BigOperators
variable {n:ℕ}
end
end aZa
end
section
namespace aqe
noncomputable section
open cu DQ ane MvPolynomial
end
end aqe
end
section
namespace vq
noncomputable section
open cu MN MvPolynomial
end
end vq
end
section
namespace czA
noncomputable section
open cu DQ aqe MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial Polynomial.algebra
end
end czA
end
section
namespace czz
noncomputable section
open aqe MvPolynomial
variable {n:ℕ} {k :Type} [mD k]
variable (I:oD (lJ (lV (Fin n)) k))
end
end czz
end
section
namespace baF
noncomputable section
open DdK1 cu MN MvPolynomial
open scoped Polynomial
end
end baF
end
section
namespace aR1
open DQ Cu akS
open scoped Polynomial
end aR1
end

end Merged6967_DdZ3EWiUc

section Merged6967_Fast042
set_option Elab.async false











set_option Elab.async false

-- merged module Numeric2Aux
section Merged_Numeric2Aux
set_option Elab.async false
set_option autoImplicit true
section
namespace CJ0
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem ProximityPrize.Benchmark
open Sol1.OneCount (A16 R16 scalarCode squaredCode flatten flatten_injective
  flatten_rows_mem flatten_agreement_le)
open Sol1.FiniteRowProjection
open scoped NNReal
theorem scalar_word_count {A cap} (hlist : ScalarList A cap) (w : Node → K) (P : Finset (Node → K))
    (hP : ∀ f ∈ P, f ∈ scalarCode ∧ A ≤ agreementCard f w) : P.card ≤ cap := by
  classical
  have : NeZero (k : ℕ) := ⟨by decide⟩
  choose poly hdegree heval using fun f : P ↦
    ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (hP f.val f.property).1
  have hinj : Function.Injective poly := by
    intro f g hfg
    apply Subtype.ext
    funext i
    calc
      f.val i = (poly f).eval (IRSProfile.domain i) := (heval f i).symm
      _ = (poly g).eval (IRSProfile.domain i) := by rw [hfg]
      _ = g.val i := heval g i
  let polys : Finset (Polynomial K) := Finset.univ.image poly
  have hpolyscard : polys.card = P.card := by
    dsimp [polys]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hpolys : (polys : Set (Polynomial K)) ⊆
      close A w := by
    intro q hq
    obtain ⟨f,_hf,rfl⟩ := Finset.mem_image.mp hq
    refine ⟨?_, ?_⟩
    · have hd : (poly f).natDegree < k := hdegree f
      exact (Polynomial.degree_le_natDegree).trans_lt (by exact_mod_cast hd)
    · refine (hP f.val f.property).2.trans (Finset.card_le_card ?_)
      intro i hi
      apply (ReedSolomon.mem_polynomialAgreementSet node w (poly f) i).mpr
      have hfw : f.val i = w i := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
      exact (heval f i).trans hfw
  obtain ⟨hfinite,hbound⟩ := hlist w
  have hcount := (Set.ncard_le_ncard hpolys hfinite).trans hbound
  have hcount' : polys.card ≤ cap := by simpa only [Set.ncard_coe_finset] using hcount
  rwa [hpolyscard] at hcount'
theorem squared_word_count {A cap} (hlist : ScalarList A cap)
    (hroom : (cap+1)^2 ≤ Fintype.card K) (w : Node → A16) (P : Finset (Node → A16))
    (hP : ∀ f ∈ P, f ∈ squaredCode ∧ A ≤ agreementCard f w) : P.card ≤ cap := by
  classical
  let flattened := P.image flatten
  have hflat : ∀ f ∈ flattened,
      (∀ r : R16, (fun i ↦ f i r) ∈ scalarCode) ∧
        A ≤ agreementCard f (flatten w) := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨hcode,hagree⟩ := hP g hg
    exact ⟨flatten_rows_mem g hcode,hagree.trans (flatten_agreement_le g w)⟩
  have hcount := finset_vector_list_card_le scalarCode A cap hroom
    (scalar_word_count hlist) (flatten w) flattened hflat
  have hcard : flattened.card = P.card := Finset.card_image_of_injective P flatten_injective
  rwa [hcard] at hcount
theorem squared_lambda_le {A cap} (hlist : ScalarList A cap)
    (hroom : (cap+1)^2 ≤ Fintype.card K) (radius : ℝ)
    (hcut : ∀ f w : Node → A16, (δᵣ(w,f) : ℝ) ≤ radius → A ≤ agreementCard f w) :
    Code.Lambda (squaredCode : Set (Node → A16)) radius ≤ (cap : ℕ∞) := by
  classical
  apply Code.Lambda_le_iff_forall_encard_le.mpr
  intro w
  have hfinite : (Code.closeCodewordsRel (squaredCode : Set (Node → A16)) w radius).Finite :=
    Set.toFinite _
  have hcard : hfinite.toFinset.card ≤ cap := by
    apply squared_word_count hlist hroom w hfinite.toFinset
    intro f hf
    obtain ⟨hcode,hclose⟩ := Code.mem_closeCodewordsRel_iff.mp (hfinite.mem_toFinset.mp hf)
    exact ⟨hcode,hcut f w hclose⟩
  calc
    (Code.closeCodewordsRel (squaredCode : Set (Node → A16)) w radius).encard =
        (hfinite.toFinset.card : ℕ∞) := hfinite.encard_eq_coe_toFinset_card
    _ ≤ (cap : ℕ∞) := by exact_mod_cast hcard
end
end CJ0
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace P1
noncomputable section
open Polynomial Matrix CoreDefinitions Code FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators NNReal
export P0 (K I Words node p blockLength k Frac Bivar TypeAtMostOne coefficientBlocks
  extendSeed IsCommonGCD atSlope seed liftX twist amplitudeDegree sixNorm columnRank
  threeU threeV sameDirection relationOn)
structure Rung where
  agreement : ℕ
  numerator : ℕ
  denominator : ℕ
  lowEnd : ℕ
  mcaBound : ℕ
  listBound : ℕ
abbrev target : Rung := ⟨179944,336691697,1073741824,2369,0x3aca17061ce8c43,8491707658716571⟩
abbrev agreement := target.agreement
abbrev radiusNumerator := target.numerator
abbrev radiusDenominator := target.denominator
abbrev t : ℕ := blockLength - agreement
abbrev L : ℕ := agreement - k
abbrev heightCap : ℕ := t + 1 - L - 2
def queryRadius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator
def radius : ℝ := queryRadius
def BadFamily (u : Words) (Γ : Finset K) : Prop :=
  ∀ γ ∈ Γ, IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius
structure BadMarkAt (A : ℕ) (u : Words) (γ : K) where
  support : Finset I
  decoder : (Polynomial K)
  agreement : A ≤ support.card
  degree : decoder.degree < k
  hits : ∀ i ∈ support, decoder.eval (node i) = u 0 i + γ * u 1 i
  nonjoint : ¬ (ExtendsOn node (u 0) k support ∧ ExtendsOn node (u 1) k support)
abbrev BadMark := BadMarkAt agreement
def ordinary (u : Words) := hankel node (u 0) (u 1) L t
def twoBlock (u : Words) := stacked p node (u 0) (u 1) L t
def stackRank (u : Words) := GenericLayer.genericRank (twoBlock u)
def nullity (u : Words) := GenericLayer.genericNullity (twoBlock u)
def Normal (u : Words) (γ : K) : Prop :=
  ((twoBlock u).map (evalRingHom γ)).rank = stackRank u
structure TwoActive (u : Words) where
  a : ℕ
  b : ℕ
  c : ℕ
  ab : a ≤ b
  active : b ≤ t
  inactive : t < c
  top : c ≤ k
  degreeSum : a + b + c = 2 * k + 2
  nullitySum : nullity u + a + b = 2 * (t + 1)
  level : Strata.HasLevelHilbertFunction
    (fun s j => algebraMap (Polynomial K) Frac (Principal.parameterSyndromes p node (u 0) (u 1) s j))
    k a b c
def TwoActive.height {u : Words} (T : TwoActive u) := (k + 1) - T.c
abbrev Relation {u : Words} (T : TwoActive u) :=
  Strata.PolynomialRelationCertificate p node (u 0) (u 1) k T.height
def leftU {u : Words} {T : TwoActive u} (R : Relation T) : Bivar :=
  Principal.assemble (fun j => R.coefficients (0, j))
def leftV {u : Words} {T : TwoActive u} (R : Relation T) : Bivar :=
  Principal.assemble (fun j => R.coefficients (1, j))
def fixedNodes {u : Words} {T : TwoActive u} (R : Relation T) : Finset I := by
  classical
  exact Finset.univ.filter fun i =>
    (leftU R).eval (C (node i)) = 0 ∧ (leftV R).eval (C (node i)) = 0
structure Reduction (u : Words) (T : TwoActive u) (R : Relation T) where
  U : Bivar
  V : Bivar
  output : Bivar
  height : ℕ
  height_eq : height + (fixedNodes R).card = T.height
  max_degree : max U.natDegree V.natDegree = height
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  coprime : IsCoprime (extendSeed U) (extendSeed V)
  U_factor : leftU R = liftX (locator node (fixedNodes R)) * U
  V_factor : leftV R = liftX (locator node (fixedNodes R)) * V
  output_factor : R.output = liftX (locator node (fixedNodes R)) * output
  output_degree : output.degree < (k + height : ℕ)
  deleted_error : ∀ γ, Normal u γ → ∀ M : BadMark u γ, ∀ i ∈ fixedNodes R,
    M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i
structure RankThree (u : Words) (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) where
  rank_eq : columnRank D.U D.V = 3
  α : Fin 2 → (Polynomial K)
  β : Fin 2 → (Polynomial K)
  a : (Polynomial K)
  b : (Polynomial K)
  a_ne : a ≠ 0
  b_ne : b ≠ 0
  α_primitive : IsCoprime (α 0) (α 1)
  β_primitive : IsCoprime (β 0) (β 1)
  first_degree : a.natDegree + amplitudeDegree (β 0) (β 1) ≤ D.height
  second_degree : b.natDegree + amplitudeDegree (α 0) (α 1) ≤ D.height
  same_direction : sameDirection D.U D.V (threeU a β) (threeV b α)
  output : Bivar
  output_degree : output.degree < (k + D.height : ℕ)
  nodes : relationOn u (fixedNodes R) (threeU a β) (threeV b α) output
structure ModelAt (maxHeight : ℕ) (u : Words) (deleted : Finset I) where
  shift : K
  pencil₀ : (Polynomial K)
  pencil₁ : (Polynomial K)
  pencil₀_degree : pencil₀.degree < k
  pencil₁_degree : pencil₁.degree < k
  E : (Polynomial K)
  factor : (Polynomial K)
  Q : (Polynomial K)
  A₀ : (Polynomial K)
  A₁ : (Polynomial K)
  word : I → K
  word_fixed : ∀ i, twist (word i) = word i
  word_deleted : ∀ i ∈ deleted, word i = 0
  E_monic : E.Monic
  E_nodes : ∀ i, E.eval (node i) ≠ 0
  factor_nodes : ∀ i ∉ deleted, factor.eval (node i) ≠ 0
  coprime_factor : IsCoprime E factor
  offset_proper : Q.degree < E.degree
  offset_reduced : IsCoprime Q E
  adjacent_coprime : IsCoprime E (E.map twist)
  amplitudes_primitive : IsCoprime A₀ A₁
  first_amplitude_unit : IsCoprime A₀ E
  height_bound : E.natDegree + amplitudeDegree A₀ A₁ ≤ maxHeight
  first_word : ∀ i ∉ deleted,
    E.eval (node i) * (u 0 i + shift * u 1 i - pencil₀.eval (node i)) =
      factor.eval (node i) * A₀.eval (node i) * word i
  second_word : ∀ i ∉ deleted,
    E.eval (node i) * (u 1 i - pencil₁.eval (node i)) =
      Q.eval (node i) + factor.eval (node i) * A₁.eval (node i) * word i
def ModelAt.overhead {h u deleted} (M : ModelAt h u deleted) : ℤ :=
  (M.E.natDegree : ℤ) - M.factor.natDegree - amplitudeDegree M.A₀ M.A₁
def ModelAt.label {h u deleted} (M : ModelAt h u deleted) (γ : K) : K :=
  γ - M.shift
def ModelAt.amplitude {h u deleted} (M : ModelAt h u deleted) (γ : K) : (Polynomial K) :=
  M.A₀ + Polynomial.C (M.label γ) * M.A₁
def ModelAt.decoder {h u deleted} (M : ModelAt h u deleted) {A : ℕ} {γ : K}
    (B : BadMarkAt A u γ) : (Polynomial K) :=
  B.decoder - M.pencil₀ - Polynomial.C (M.label γ) * M.pencil₁
structure MarkAt {A h : ℕ} {u deleted} (M : ModelAt h u deleted) (γ : K) (S : (Polynomial K)) where
  bad : BadMarkAt A u γ
  avoids_deleted : Disjoint bad.support deleted
  scalar_fixed : S.map twist = S
  scalar_degree : S = 0 ∨ (S.natDegree : ℤ) ≤ (k : ℤ) - 1 + M.overhead
  scalar_hits : ∀ i ∈ bad.support, S.eval (node i) = M.word i
  pole_unit : IsCoprime (M.amplitude γ) M.E
  identity : M.E * M.decoder bad - Polynomial.C (M.label γ) * M.Q =
    M.factor * M.amplitude γ * S
structure FamilyAt (A : ℕ) {h : ℕ} {u deleted} (M : ModelAt h u deleted) (Γ : Finset K) where
  scalar : K → (Polynomial K)
  mark : ∀ γ ∈ Γ, MarkAt (A := A) M γ (scalar γ)
  distinct : Set.InjOn scalar (Γ : Set K)
abbrev AnchorModel := ModelAt heightCap
abbrev AnchoredFamily {u deleted} (M : AnchorModel u deleted) := FamilyAt agreement M
abbrev AnchorModel.overhead {u deleted} (M : AnchorModel u deleted) := ModelAt.overhead M
abbrev AnchorModel.label {u deleted} (M : AnchorModel u deleted) := ModelAt.label M
abbrev AnchorModel.amplitude {u deleted} (M : AnchorModel u deleted) := ModelAt.amplitude M
abbrev AnchorModel.decoder {u deleted} (M : AnchorModel u deleted) {γ : K} (B : BadMark u γ) :=
  ModelAt.decoder M B
structure HighRow where
  lo : ℕ
  hi : ℕ
  prefixFee : ℕ
  retained : ℕ
inductive HighBand where
  | h2370
  | h2390
  | h2410
  | h2420
  | h2440
  | h2460
  | h2480
  | h2500
  | h2520
  | h2530
  | h2540
  | h2550
  | h2560
  | h2570
  | h2585
  | h2590
  | h2600
  | h2601
  | h2611
  | h2621
  | h2640
  | h2670
  | h2700
  | h2750
  | h2800
  | h2900
  | h2950
  | h2980
  | h3000
  | h3050
  | h3100
  | h3200
  | h3400
  | h3555
  | h4000
  | h4800
  | h7773
  | h8000
  | h14500
  | h21473
  | h24000
  | h28323
  | h32433
end
end P1
end
section
namespace CJ1
inductive Bank where
  | leftLow | rightLow | leftHigh | rightHigh
  deriving DecidableEq
def Bank.onRows : Bank → Bool
  | .leftLow | .leftHigh => true
  | .rightLow | .rightHigh => false
structure Block where
  bank : Bank
  cap : Nat
  free : List (Nat × Nat)
  vectors : List (List (List Nat))
def Block.coeff (z : Block) (j i k : Nat) : Nat := (((z.vectors[j]?).getD [])[i]?.getD [])[k]?.getD 0
end CJ1
end
section
namespace CJ1
def total {α : Type*} [AddMonoid α] (f : ℕ → α) : ℕ → α
  | 0 => 0
  | n + 1 => total f n + f n
def fastChoose (n k : ℕ) := n.descFactorial k / k.factorial
def entryZ (r c : CJ0.Jet) : ℤ :=
  if c.b ≤ r.b ∧ c.c ≤ r.c ∧ r.a + (r.b-c.b) + (r.c-c.c) = c.a then
    (-1 : ℤ)^(r.c-c.c) * (fastChoose c.a r.a : ℤ) * (fastChoose (c.a-r.a) (r.b-c.b) : ℤ)
  else 0
end CJ1
end
section
namespace CJ1
open scoped BigOperators
open CJ0 (Jet blockRows blockCols blockMatrix )
theorem total_eq_sum {α : Type*} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    total f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [total]
  | succ n ih => rw [total, Finset.sum_range_succ, ih]
theorem right_witness {F ρ κ : Type*} [Field F] [Fintype ρ] [Fintype κ]
    (M : Matrix ρ κ F) {d : ℕ} (V : Matrix κ (Fin d) F) (free : Fin d → κ)
    (hMV : M * V = 0) (hid : V.submatrix free id = 1) :
    M.rank + d ≤ Fintype.card κ := by
  have h := V.rank_submatrix_le free id
  rw [hid, Matrix.rank_one, Fintype.card_fin] at h
  exact (Nat.add_le_add_left h _).trans (Matrix.rank_add_rank_le_card_of_mul_eq_zero hMV)
end CJ1
end
section
namespace CJ6
def source : CJ0.Source := ⟨52, 71, 20, 9, CJ0.fullBox 71 20 9⟩
end CJ6
end
section
namespace CJ6
open CJ1 (Block total entryZ)
def rowLo (q u h : ℕ) := u + 2*q + h + 1 - 72
def rowHi (q u h : ℕ) := min (q + 1 - h) (u + 2*q + h + 1 - 20)
def rowLen (q u h : ℕ) := rowHi q u h - rowLo q u h
def colLo (u b : ℕ) := (21 - (u+b)) / 2
def colHi (q b : ℕ) := min 10 (min (q-b+1) ((20-b)/2+1))
def colLen (q u b : ℕ) := colHi q b - colLo u b
abbrev Row (q u : ℕ) := (h : Fin (q+1)) × Fin (rowLen q u h)
abbrev Col (q u : ℕ) := (b : Fin (min q 20 + 1)) × Fin (colLen q u b)
def rowAt (q u h i : ℕ) : CJ0.Jet :=
  let d := rowLo q u h + i
  ⟨q - (h+d), d, h⟩
def rowJet (q u : ℕ) (r : Row q u) : CJ0.Jet := rowAt q u r.1 r.2
def colAt (q u b i : ℕ) : CJ0.Jet :=
  let c := colLo u b + i
  ⟨c, b, q - (b+c)⟩
def colJet (q u : ℕ) (s : Col q u) : CJ0.Jet := colAt q u s.1 s.2
def packet (q u : ℕ) : Matrix (Row q u) (Col q u) (ZMod CJ0.p) :=
  fun r s => CJ0.blockEntry (rowJet q u r) (colJet q u s)
def rows (q u : ℕ) := total (rowLen q u) (q+1)
def cols (q u : ℕ) := total (colLen q u) (min q 20 + 1)
def nominal (q u : ℕ) := min (rows q u) (cols q u)
def outer (onRows : Bool) (q : ℕ) := if onRows then q+1 else min q 20+1
def fiber (onRows : Bool) (q u : ℕ) := if onRows then rowLen q u else colLen q u
abbrev Axis (onRows : Bool) (q u : ℕ) :=
  (i : Fin (outer onRows q)) × Fin (fiber onRows q u i)
def orientedEntry (onRows : Bool) (q u i k b t : ℕ) : ℤ :=
  if onRows then entryZ (rowAt q u b t) (colAt q u i k)
  else entryZ (rowAt q u i k) (colAt q u b t)
def dot (q u : ℕ) (z : Block) (j i k : ℕ) : ℤ :=
  total (fun b => total (fun t =>
    let w := z.coeff j b t
    if w = 0 then 0 else orientedEntry z.bank.onRows q u i k b t * (w : ℤ))
    (fiber z.bank.onRows q u b)) (outer z.bank.onRows q)
def Dots (q u : ℕ) (z : Block) : Prop :=
  ∀ j < z.free.length, ∀ i < outer (!z.bank.onRows) q,
    ∀ k < fiber (!z.bank.onRows) q u i, dot q u z j i k % (CJ0.p : ℤ) = 0
def VectorDots (q u : ℕ) (z : Block) (j : ℕ) : Prop :=
  ∀ i < outer (!z.bank.onRows) q,
    ∀ k < fiber (!z.bank.onRows) q u i, dot q u z j i k % (CJ0.p : ℤ) = 0
abbrev Cell := ℕ × ℕ × ℕ
def Checks : List Cell → Prop
  | [] => True
  | (q,u,r)::xs => (CJ0.blockMatrix source q ((u : ℤ)-20)).rank ≤ r ∧ Checks xs
def boundIn (q u d : ℕ) : List Cell → ℕ
  | [] => d
  | (a,b,r)::xs => if q = a ∧ u = b then r else boundIn q u d xs
def rows0 : List Cell := [(35,17,109),(38,14,104)]
def rows1 : List Cell := [(36,16,108),(37,15,106),(38,15,99)]
def rows2 : List Cell := [(39,13,101),(39,14,98),(40,12,98),(40,13,96)]
def rows3 : List Cell := [(41,11,94),(41,12,94),(41,13,89),(42,11,91),(42,12,88)]
def rows4 : List Cell := [(43,10,88),(43,11,86),(44,10,84),(44,11,80)]
def rows5 : List Cell := [(45,9,81),(45,10,79),(46,9,77),(47,8,75),(47,9,71),(48,8,70)]
def rows6 : List Cell := [(49,7,68),(50,7,63),(51,6,61),(53,5,53),(54,5,48),(55,4,45),(56,4,40)]
def rows7 : List Cell := [(57,3,36),(57,4,35),(58,3,32),(59,2,27),(59,3,28),(60,2,24),(60,3,24),(61,1,18),(61,2,21)]
def rows8 : List Cell := [(62,1,16),(62,2,18),(63,0,9),(63,1,14),(63,2,15),(64,0,8),(64,1,12),(65,0,7),(65,1,10),(66,0,6),(66,1,8),(67,0,5),(68,0,4),(69,0,3)]
def cells (q : ℕ) :=
  if q < 35 then [] else
  if q ≤ 38 then rows0 ++ rows1 else
  if q ≤ 40 then rows2 else
  if q ≤ 42 then rows3 else
  if q ≤ 44 then rows4 else
  if q ≤ 48 then rows5 else
  if q ≤ 56 then rows6 else
  if q ≤ 61 then rows7 else
  rows8
def allowance (q u : ℕ) := boundIn q u (nominal q u) (cells q)
def grade (q : ℕ) := CJ1.total (allowance q) (72-q)
end CJ6
end
section
namespace K1_13_2_3_2
open K1_13_2 Finset
open scoped BigOperators
private theorem twice_half (x : ℤ) : 2 * (x * (x - 1) / 2) = x * (x - 1) := by
  have h : (2 : ℤ) ∣ x * (x - 1) := by
    rcases Int.emod_two_eq_zero_or_one x with hx | hx
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ x) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ x - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]
def denPolynomial (q r : ℤ) : ℤ :=
  2 + r * (r + 1) + q * (44 + 14 * r + r * (r - 1)) +
    (57 + 6 * r) * (q * (q - 1)) + 12 * q * (q - 1) * (q - 2)
theorem twice_den (u : ℤ) (h : 0 ≤ u) :
    2 * denominator u = denPolynomial (u / 6) (u % 6) := by
  let q := u / 6
  let r := u % 6
  simp only [denominator, not_lt.mpr h, ite_false, denPolynomial]
  change 2 * (1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)) = _
  have hr := twice_half (r + 1)
  rw [show (r + 1) * (r + 1 - 1) = r * (r + 1) by ring] at hr
  change _ = denPolynomial q r
  unfold denPolynomial
  linear_combination hr + q * twice_half r + (57 + 6 * r) * twice_half q
def denPrefixPolynomial (q r : ℤ) : ℤ :=
  984 * q + 3084 * q * (q - 1) + 1728 * q * (q - 1) * (q - 2) +
    216 * q * (q - 1) * (q - 2) * (q - 3) + (24 * r + 4 * (r - 1) * r * (r + 1)) +
    q * (528 * r + 84 * (r - 1) * r + 4 * (r - 2) * (r - 1) * r) +
    (684 * r + 36 * (r - 1) * r) * q * (q - 1) + 144 * r * q * (q - 1) * (q - 2)
def denPrefix (n : ℤ) : ℤ := denPrefixPolynomial (n / 6) (n % 6)
private theorem denPrefix_step (n : ℤ) (hn : 0 ≤ n) :
    denPrefix (n + 1) = denPrefix n + 24 * denominator n := by
  have hden := twice_den n hn
  have hq : (n + 1) / 6 = n / 6 + (n % 6 + 1) / 6 := by omega
  have hr : (n + 1) % 6 = (n % 6 + 1) % 6 := by omega
  have hlo : 0 ≤ n % 6 := by omega
  have hhi : n % 6 < 6 := by omega
  rw [denPrefix, denPrefix, hq, hr]
  generalize n % 6 = r at hden hlo hhi ⊢
  interval_cases r <;> norm_num [denPrefixPolynomial, denPolynomial] at hden ⊢ <;>
    linear_combination (norm := ring_nf) -12 * hden
private theorem denPrefix_eq (n : ℕ) :
    24 * (∑ u ∈ range n, denominator (u : ℤ)) = denPrefix n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, Nat.cast_succ, denPrefix_step _ (by omega)]
private theorem sum_shift (f : ℤ → ℤ) (hz : ∀ x < 0, f x = 0) (n a : ℕ) :
    (∑ u ∈ range n, f ((u : ℤ) - a)) = ∑ u ∈ range (n - a), f (u : ℤ) := by
  have hzero (b : ℕ) (hb : b ≤ a) : (∑ u ∈ range b, f ((u : ℤ) - a)) = 0 := by
    exact sum_eq_zero fun u hu => hz _ (by have := mem_range.mp hu; omega)
  by_cases h : a ≤ n
  · conv_lhs => rw [← Nat.add_sub_of_le h, sum_range_add]
    rw [hzero a le_rfl, zero_add]
    apply sum_congr rfl
    intro u _
    congr 1
    push_cast
    ring
  · rw [hzero n (by omega), show n - a = 0 by omega, sum_range_zero]
theorem sum_shift_cumulative (d n a : ℕ) :
    (∑ u ∈ range n, cumulative (d : ℤ) ((u : ℤ) - a)) =
      ∑ u ∈ range (n - a), cumulative (d : ℤ) (u : ℤ) :=
  sum_shift _ (fun x hx => by simp [cumulative, hx]) n a
def cumulativePrefix (d n : ℕ) : ℤ :=
  denPrefix n - denPrefix (n - (d + 1) : ℕ) - denPrefix (n - (d + 2) : ℕ) -
    denPrefix (n - (d + 3) : ℕ) + denPrefix (n - (2 * d + 3) : ℕ) +
    denPrefix (n - (2 * d + 4) : ℕ) + denPrefix (n - (2 * d + 5) : ℕ) -
    denPrefix (n - (3 * d + 6) : ℕ)
private theorem cumulative_expand (d u : ℕ) (hu : u ≤ 3 * d) :
    cumulative (d : ℤ) (u : ℤ) =
      denominator u - denominator ((u : ℤ) - (d + 1 : ℕ)) -
        denominator ((u : ℤ) - (d + 2 : ℕ)) - denominator ((u : ℤ) - (d + 3 : ℕ)) +
        denominator ((u : ℤ) - (2 * d + 3 : ℕ)) + denominator ((u : ℤ) - (2 * d + 4 : ℕ)) +
        denominator ((u : ℤ) - (2 * d + 5 : ℕ)) - denominator ((u : ℤ) - (3 * d + 6 : ℕ)) := by
  have hd : ¬ (d : ℤ) < 0 := by omega
  have hu₀ : ¬ (u : ℤ) < 0 := by omega
  simp [cumulative, hd, hu₀, min_eq_left (show (u : ℤ) ≤ 3 * (d : ℤ) by omega)]
  ring_nf
theorem prefix_eq (d n : ℕ) (hn : n ≤ 3 * d + 1) :
    24 * (∑ u ∈ range n, cumulative (d : ℤ) (u : ℤ)) = cumulativePrefix d n := by
  have hs (a : ℕ) : 24 * (∑ u ∈ range n, denominator ((u : ℤ) - a)) =
      denPrefix (n - a : ℕ) := by
    rw [sum_shift _ (fun x hx => by simp [denominator, hx]), denPrefix_eq]
  rw [sum_congr rfl (fun u hu => cumulative_expand d u (by have := mem_range.mp hu; omega))]
  simp only [cumulativePrefix, sum_sub_distrib, sum_add_distrib, mul_sub, mul_add, hs, denPrefix_eq]
end K1_13_2_3_2
end

end Merged_Numeric2Aux

-- merged module Pack_K1_14_3Split
section Merged_Pack_K1_14_3Split
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace K1_14_3
noncomputable section
open K1 K1_14 Polynomial
open scoped BigOperators Classical
def c7 : Prop :=
  ∀ qs : Finset Surface, qs.Nonempty → (∀ q ∈ qs, Parent q) →
    ∃ f : Equation, ProjectedProduct qs f
end
end K1_14_3
end

end Merged_Pack_K1_14_3Split

-- merged module Fast035
section Merged_Fast035
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
namespace K1_14_3_4
noncomputable section
open K1 K1_14 K1_14_3 K1_14_3_2 Polynomial
open scoped BigOperators
def graphCutter (g : ClearedEquation) : Jet :=
  C (liftEquation (clearedDx g)) +
    (Polynomial.X (R := Equation)) * C (liftEquation g.derivative)
structure ThresholdPair (i : Fin 4) (P Q : Jet) (r : ℕ) where
  left : Jet
  right : Jet
  proper : ProperPair left right
  left_caps : RowCaps left (cheapShape i)
  right_caps : RowCaps right (layeredShape i)
  heavy : Finset Equation
  factors : ∀ f ∈ heavy, Irreducible f ∧ 0 < f.natDegree ∧ f.natDegree < p ∧
    C f ∣ P ∧ C f ∣ Q
  seed_budget : (∑ f ∈ heavy, (ordinarySeedDegree f : ℚ)) ≤ (cheapShape i).U / (r : ℚ)
  y_budget : (∑ f ∈ heavy, (f.natDegree : ℚ)) ≤ (cheapShape i).B / (r : ℚ)
  residual_order : ∀ q : Surface, Parent q →
    OrderAt q P (reserve i + 1) → OrderAt q Q (reserve i + 1) →
    (∀ f ∈ heavy, C f ∉ q.asIdeal) →
    OrderAt q left (reserve i + 2 - r) ∧ OrderAt q right (reserve i + 2 - r)
end
end K1_14_3_4
end

end Merged_Fast035

-- merged module Fast042
section Merged_Fast042
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace K1_14_3_2
noncomputable section
open K1 K1_14 K1_14_3 Polynomial
open scoped BigOperators Classical
def c1 : Prop :=
  ∀ P Q : Jet, P ≠ 0 → Q ≠ 0 →
    RowCaps P (cheapShape 0) → RowCaps Q (layeredShape 0) →
    NoMovingCommon P Q → Nonempty (PreparedPair P Q)
end
end K1_14_3_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
namespace K1_14_3_2_7
noncomputable section
open K1_14 K1_14_3
open scoped nonZeroDivisors
variable {B A : Type} [CommRing B] [CommRing A]
abbrev denominators (f : B →+* A) : Submonoid A :=
  (nonZeroDivisors B).map f.toMonoidHom
abbrev Localized (f : B →+* A) := Localization (M := A) (denominators f)
private def localBase (f : B →+* A) : FractionRing B →+* Localized f :=
  IsLocalization.lift (M := nonZeroDivisors B)
    (g := (algebraMap A (Localized f)).comp f)
    (fun b => IsLocalization.map_units (M := denominators f) (Localized f)
      ⟨f b, b, b.property, rfl⟩)
instance (f : B →+* A) : Algebra (FractionRing B) (Localized f) :=
  (localBase f).toAlgebra
@[simp] theorem local_base (f : B →+* A) (b : B) :
    algebraMap (FractionRing B) (Localized f) (algebraMap B (FractionRing B) b) =
      algebraMap A (Localized f) (f b) :=
  IsLocalization.lift_eq _ _
abbrev localizedPrime (f : B →+* A) (I : Ideal A) : Ideal (Localized f) :=
  I.map (algebraMap A (Localized f))
def GenericFibre (f : B →+* A) (I : Ideal A) := Localized f ⧸ localizedPrime f I
instance (f : B →+* A) (I : Ideal A) : CommRing (GenericFibre f I) :=
  inferInstanceAs (CommRing (Localized f ⧸ localizedPrime f I))
instance (f : B →+* A) (I : Ideal A) : Algebra (FractionRing B) (GenericFibre f I) :=
  inferInstanceAs (Algebra (FractionRing B) (Localized f ⧸ localizedPrime f I))
def toFibre (f : B →+* A) (I : Ideal A) : A →+* GenericFibre f I :=
  (Ideal.Quotient.mk _).comp (algebraMap A (Localized f))
@[simp] theorem fibre_base (f : B →+* A) (I : Ideal A) (b : B) :
    algebraMap (FractionRing B) (GenericFibre f I) (algebraMap B (FractionRing B) b) =
      toFibre f I (f b) := by
  change Ideal.Quotient.mk _ (algebraMap (FractionRing B) (Localized f)
    (algebraMap B (FractionRing B) b)) = _
  rw [local_base]
  rfl
variable [IsDomain B]
end
end K1_14_3_2_7
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 4000000
namespace K1_14_3_2_7
noncomputable section
open K1_14 K1_14_3 Polynomial
open scoped TensorProduct nonZeroDivisors
abbrev Four (R : Type) [CommRing R] := Polynomial (Polynomial (MvPolynomial (Fin 2) R))
def scalar {R : Type} [CommRing R] : R →+* Four R := C.comp (C.comp MvPolynomial.C)
def seedVar {R : Type} [CommRing R] (i : Fin 2) : Four R := C (C (MvPolynomial.X i))
def yVar {R : Type} [CommRing R] : Four R :=
  Polynomial.C (R := (Polynomial (MvPolynomial (Fin 2) R))) (Polynomial.X (R := MvPolynomial (Fin 2) R))
def vVar {R : Type} [CommRing R] : Four R :=
  Polynomial.X (R := (Polynomial (MvPolynomial (Fin 2) R)))
def evaluate {R T : Type} [CommRing R] [CommRing T] (a : R →+* T)
    (t : Fin 2 → T) (y v : T) : Four R →+* T :=
  eval₂RingHom (eval₂RingHom (MvPolynomial.eval₂Hom a t) y) v
@[simp] theorem evaluate_scalar {R T : Type} [CommRing R] [CommRing T]
    (a : R →+* T) (t : Fin 2 → T) (y v : T) (c : R) :
    evaluate a t y v (scalar c) = a c := by simp [evaluate, scalar]
@[simp] theorem evaluate_seed {R T : Type} [CommRing R] [CommRing T]
    (a : R →+* T) (t : Fin 2 → T) (y v : T) (i : Fin 2) :
    evaluate a t y v (seedVar i) = t i := by simp [evaluate, seedVar]
@[simp] theorem evaluate_y {R T : Type} [CommRing R] [CommRing T]
    (a : R →+* T) (t : Fin 2 → T) (y v : T) :
    evaluate a t y v yVar = y := by simp [evaluate, yVar]
@[simp] theorem evaluate_v {R T : Type} [CommRing R] [CommRing T]
    (a : R →+* T) (t : Fin 2 → T) (y v : T) :
    evaluate a t y v vVar = v := by simp [evaluate, vVar]
def extendScalars {R G : Type} [CommRing R] [CommRing G] (k : R →+* G) :
    Four R →+* Four G :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (MvPolynomial.map k))
@[simp] theorem extend_scalar {R G : Type} [CommRing R] [CommRing G] (k : R →+* G) (c : R) :
    extendScalars k (scalar c) = scalar (k c) := by simp [extendScalars, scalar]
@[simp] theorem extend_seed {R G : Type} [CommRing R] [CommRing G] (k : R →+* G) (i : Fin 2) :
    extendScalars k (seedVar i) = seedVar i := by simp [extendScalars, seedVar]
@[simp] theorem extend_y {R G : Type} [CommRing R] [CommRing G] (k : R →+* G) :
    extendScalars k yVar = yVar := by simp [extendScalars, yVar]
@[simp] theorem extend_v {R G : Type} [CommRing R] [CommRing G] (k : R →+* G) :
    extendScalars k vVar = vVar := by simp [extendScalars, vVar]
structure Projection (R G B : Type) [CommRing R] [Field G] [CommRing B] where
  intoJet : B →+* Four R
  intoSection : B →+* G
  injective : Function.Injective intoSection
  baseScalar : R →+* B
  baseVar : Fin 2 → B
  ext : ∀ {T : Type} [CommRing T] {f g : B →+* T},
    (∀ a, f (baseScalar a) = g (baseScalar a)) →
    (∀ i, f (baseVar i) = g (baseVar i)) → f = g
  scalar_jet : ∀ a, intoJet (baseScalar a) = scalar a
  coeffMap : R →+* G
  scalar_section : ∀ a, intoSection (baseScalar a) = coeffMap a
  cutSet : Set (Four G)
  cuts : cutSet = Set.range
    (fun i => extendScalars coeffMap (intoJet (baseVar i)) - scalar (intoSection (baseVar i)))
variable {R G B : Type} [CommRing R] [Field G] [CommRing B]
end
end K1_14_3_2_7
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_3_2_5
noncomputable section
open K1_14 K1_14_3 Polynomial
def sectionParameter (i : Fin 4) : SectionField :=
  algebraMap (MvPolynomial (Fin 4) FX) SectionField (MvPolynomial.X i)
def seedLine : SectionSeeds :=
  MvPolynomial.X 0 + MvPolynomial.C (sectionParameter 0) * MvPolynomial.X 1 -
    MvPolynomial.C (sectionParameter 2)
end
end K1_14_3_2_5
end
section
set_option autoImplicit false
namespace K1_14_3_2_3
noncomputable section
open K1 K1_14 K1_14_3
abbrev Plane := MvPolynomial (Fin 2) SectionField
def parameter (i : Fin 4) : SectionField :=
  algebraMap (MvPolynomial (Fin 4) FX) SectionField (MvPolynomial.X i)
def seedCoordinates : Slice → Fin 2 → Plane
  | .seed => ![MvPolynomial.C (parameter 2), MvPolynomial.C (parameter 3)]
  | .ordinate | .mixed =>
    ![MvPolynomial.C (parameter 2) - MvPolynomial.C (parameter 0) * MvPolynomial.X 0,
      MvPolynomial.X 0]
  | .jets => MvPolynomial.X
def ordinateCoordinate : Slice → Plane
  | .seed => MvPolynomial.X 0
  | .ordinate => MvPolynomial.C (parameter 3)
  | .mixed => MvPolynomial.C (parameter 3) - MvPolynomial.C (parameter 1) * MvPolynomial.X 1
  | .jets => MvPolynomial.C (parameter 2)
def derivativeCoordinate : Slice → Plane
  | .jets => MvPolynomial.C (parameter 3)
  | _ => MvPolynomial.X 1
def sliceMap (s : Slice) : SectionJet →ₐ[SectionField] Plane :=
  Polynomial.aevalTower
    (Polynomial.aevalTower (MvPolynomial.aeval (seedCoordinates s)) (ordinateCoordinate s))
    (derivativeCoordinate s)
end
end K1_14_3_2_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1500000
namespace K1_14_3_2_3
noncomputable section
open K1_14_3 Polynomial
private abbrev t (i : Fin 2) : SectionJet := C (C (MvPolynomial.X i))
private abbrev y : SectionJet := C (Polynomial.X (R := SectionSeeds))
private abbrev v : SectionJet := Polynomial.X (R := Polynomial SectionSeeds)
private def free : Slice → Fin 2 → SectionJet
  | .seed => ![y, v]
  | .ordinate | .mixed => ![t 1, v]
  | .jets => ![t 0, t 1]
private abbrev CutQuotient (s : Slice) := SectionJet ⧸ Ideal.span (sectionEquations s)
private def cutMk (s : Slice) : SectionJet →ₐ[SectionField] CutQuotient s :=
  Ideal.Quotient.mkₐ _ _
private def restore (s : Slice) : Plane →ₐ[SectionField] CutQuotient s :=
  MvPolynomial.aeval (cutMk s ∘ free s)
@[simp] private theorem slice_t (s : Slice) (i : Fin 2) :
    sliceMap s (t i) = seedCoordinates s i := by
  simp [sliceMap]
@[simp] private theorem slice_y (s : Slice) :
    sliceMap s y = ordinateCoordinate s := by simp [sliceMap]
@[simp] private theorem slice_v (s : Slice) :
    sliceMap s v = derivativeCoordinate s := by simp [sliceMap]
@[simp] private theorem slice_scalar (s : Slice) (i : Fin 4) :
    sliceMap s (sectionScalar i) = MvPolynomial.C (parameter i) :=
  (sliceMap s).commutes (parameter i)
@[simp] private theorem restore_const (s : Slice) (i : Fin 4) :
    restore s (MvPolynomial.C (parameter i)) = cutMk s (sectionScalar i) :=
  (restore s).commutes (parameter i)
@[simp] private theorem restore_X (s : Slice) (i : Fin 2) :
    restore s (MvPolynomial.X i) = cutMk s (free s i) := by simp [restore]
end
end K1_14_3_2_3
end

end Merged_Fast042

end Merged6967_Fast042
