import ArkLib.Data.CodingTheory.ListDecodability.AgreementRadius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdBD
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming AddHom.coe_mk→Ar,Algebra.algebraMap→vG,Classical.decEq→t9,Classical.propDecidable→zi,CompPoly.Extension.Ext.ofBase→z9,CompPoly.Extension.Ext.ofBaseRingHom→EK,Decidable→xm,DecidableEq→lz,EuclideanDomain.mul_div_cancel'→uW,ExpChar→ oy,Field→lI,Fin.castSucc→zS,Fin.sum_univ_castSucc→GB,Fin.sum_univ_three→Gr,Fin.sum_univ_two→zh,Finset→lJ,Finset.card_image_of_injective→Ea,Finset.card_sdiff_of_subset→ Il,Finset.card_univ→uh,Finset.mem_univ→qU,Finset.mul_sum→wB,Finset.subset_univ→zg,Finset.sum_add_distrib→Ef,Finset.sum_coe_sort→Av,Finset.sum_congr→pG,Finset.sum_subset→G2,Finset.univ→ oY,Fintype→c9,Fintype.card→aU,Fintype.card_coe→vl,Fintype.card_fin→sS,Fintype.card_prod→HZ,Fintype.card_subtype_compl→Gn,Fintype.sum_option→JK,Fintype.sum_prod_type→ IU,Function.Injective→cy,Function.Surjective→vh,GCDMonoid.gcd→ oj,GCDMonoid.gcd_dvd_left→v9,GCDMonoid.gcd_dvd_right→yB,IsCoprime→pz,KoalaBear.Field→FQ,KoalaBear.card_ext6→ Iw,KoalaBear.ext6Params→Aa,Lagrange.degree_interpolate_lt→GY,Lagrange.eval_interpolate_at_node→G8,Lagrange.interpolate→GR,LinearMap.coe_mk→Eg
open _root_ renaming LinearMap.comp_apply→ In,LinearMap.finrank_range_add_finrank_ker→t8,LinearMap.finrank_range_of_inj→FV,LinearMap.ker→n5,LinearMap.range→p7,LinearMap.range_comp_of_range_eq_top→Gi,Matrix→ oD,Matrix.cons_val_one→Gj,Matrix.cons_val_two→ IT,Matrix.cons_val_zero→G9,Matrix.det_diagonal→xI,Matrix.diagonal→yU,Matrix.map_apply→xu,Matrix.mulVec→p9,Matrix.mulVecLin_apply→G6,Matrix.mul_diagonal→Cy,Matrix.of→pL,Matrix.of_apply→Au,Matrix.rank_eq_finrank_span_row→zk,Matrix.rank_le_card_width→G4,Matrix.rank_mul_eq_left_of_det_ne_zero→G1,Matrix.rank_transpose→G5,Matrix.transpose_apply→wA,Module.finrank→nI,Module.finrank_fintype_fun_eq_card→t3,Multiset.le_iff_subset→Hw,Nat.add_le_add_left→JM,Pi.smul_apply→xL,Pi.zero_apply→zc,Polynomial→p6,Polynomial.C→lV,Polynomial.X→nq,Polynomial.card_le_degree_of_subset_roots→Ee,Polynomial.coe_evalRingHom→qz,Polynomial.coeff_map→wR,Polynomial.degreeLT→ ox,Polynomial.degreeLTEquiv→z8,Polynomial.degree_add_le→vZ,Polynomial.degree_sub_le→yJ,Polynomial.eq_C_of_natDegree_eq_zero→ II,Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero→GF,Polynomial.eval→EP,Polynomial.evalRingHom→nX,Polynomial.eval_C→pC,Polynomial.eval_X→qy,Polynomial.eval_add→qm,Polynomial.eval_finsetSum→qx,Polynomial.eval_map_apply→Dz
open _root_ renaming Polynomial.eval_mul→ oq,Polynomial.eval_pow→t7,Polynomial.eval_smul→C9,Polynomial.eval_sub→ze,Polynomial.map_map→Fa,Polynomial.map_mul→Bf,Polynomial.mem_roots→t5,Polynomial.natDegree_lt_iff_degree_lt→qJ,Polynomial.natDegree_map_eq_of_injective→FK,Polynomial.natDegree_mul→uz,Polynomial.natDegree_smul_le→G3,Polynomial.smul_eq_C_mul→C5,ProximityPrize.Benchmark.IRSProfile.Field→zm,ProximityPrize.Benchmark.IRSProfile.Index→vw,ProximityPrize.Benchmark.IRSProfile.domain→uJ,ProximityPrize.Benchmark.IRSProfile.interleaving→Dw,ReedSolomon.code→yo,RingHom.id_apply→z7,Set.range→t4,Submodule→th,Submodule.coe_add→Gk,Submodule.coe_smul→G7,Submodule.map_comp→F9,Submodule.span→qM,Subtype.ext→u8,Subtype.val→zE,Subtype.val_injective→FR,add_comm→y5,add_zero→wY,congrArg→ oz,congrFun→ ov,dotProduct→p5,frobenius→qG,gcd_ne_zero_of_right→Fz,isCoprime_div_gcd_div_gcd→G0
open _root_ renaming le_antisymm→Du,left_div_gcd_ne_zero→Df,map_add→vi,map_mul→pU,map_ne_zero→FU,map_zero→zf,max_lt→u9,mul_add→vH,mul_assoc→vk,mul_comm→xW,mul_inv_cancel₀→Dv,mul_ne_zero→pQ,one_mul→ oZ,one_ne_zero→C4,right_div_gcd_ne_zero→zR,smul_eq_mul→vj
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset CoreDefinitions Code LinearCode
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace gR.kL
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F:Type} [lI F]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F:Type} [lI F] [lz F]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F:Type} [lI F] [lz F]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι β:Type} [lI F] [c9 ι] [c9 β]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [lz F] [c9 ι]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.kL
noncomputable section
open Matrix Polynomial Finset
open scoped BigOperators
variable {F row col:Type} [lI F] [c9 row] [c9 col]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [lz F] [c9 ι]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F V W:Type} [lI F] [AddCommGroup V] [Module F V]
 [AddCommGroup W] [Module F W] [FiniteDimensional F V]
section Coordinates
variable {ι:Type} [c9 ι] [lz ι]
end Coordinates
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [lz F] [c9 ι] [lz ι]
theorem agd (x :ι→F) (hx :cy x) (P:(Polynomial F)) (hP:P≠0)
  (S:lJ ι) (hS : ∀ i∈S,P.eval (x i)=0) :S.card≤P.natDegree := by
 have h: (S.image x).card≤P.natDegree :=Ee
  (fun a ha=>(t5 hP).mpr (by
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ha
    exact hS i hi))
 simpa only [Ea S hx] using h
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι β:Type} [lI F] [lz F] [c9 ι] [lz ι] [c9 β]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F β:Type} [lI F] [lz F]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F β:Type} [lI F] [lz F] [c9 β]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [lz F] [c9 ι] [lz ι]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι β:Type} [lI F] [lz F] [c9 ι] [lz ι] [c9 β]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 F] [c9 ι] [lz ι]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F J:Type*} [lI F]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset CoreDefinitions Code LinearCode
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 F] [c9 ι] [lz ι]
end
end gR.Principal
end
section
namespace gR.kL
noncomputable section
open Polynomial Matrix
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
namespace bz4
noncomputable section
open Polynomial Matrix Finset gR
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
end
end bz4
end
section
set_option backward.isDefEq.respectTransparency false
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι K:Type} [lI F] [lI K] [c9 ι] [lz ι]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K ι:Type} [lI F] [lI K] [c9 ι] [lz ι]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K ι:Type} [lI F] [lI K] [c9 ι] [lz ι]
end
end gR.Principal
end
section
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K ι:Type} [lI F] [lI K] [c9 ι] [lz ι]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K ι:Type} [lI F] [lI K] [c9 ι] [lz ι]
end
end gR.Principal
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
end
end gR.kL
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace gR.kL
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F ι:Type} [lI F] [c9 ι] [lz ι]
end
end gR.kL
end
section
namespace yP.FM
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
end
end yP.FM
end
section
namespace yP.C42
noncomputable section
open ProximityPrize.Benchmark
open scoped NNReal
end
end yP.C42
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.constructorNameAsVariable false
namespace gR.Native
noncomputable section
open Polynomial Finset Matrix CoreDefinitions Code
open ProximityPrize.Benchmark
open scoped BigOperators
abbrev K:=zm
abbrev I:=vw
abbrev p:ℕ:=2130706433
instance gRe :CharP K p :=
 charP_of_injective_algebraMap
  (R:=FQ) (A:=K) (vG FQ K).injective p
end
end gR.Native
end
section
namespace amZ
universe u
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open yP.C42
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
theorem ef8 {R E κ:Type*} [CommSemiring R] [CommSemiring E] [c9 κ]
  {d:ℕ} (psi:R →+* E) (cols :κ→SourceColumn d) (v :κ→R)
  (u:JetVariable d →₀ ℕ)
  (hu:u∈(MvPolynomial.map psi (SourceColumn.interpolant cols v)).support) :
  ∃ j:κ,u=(cols j).exponent:= by
 classical
 have hs :=MvPolynomial.support_map_subset psi (SourceColumn.interpolant cols v) hu
 obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum hs)
 exact ⟨j,by simpa [SourceColumn.interpolant] using MvPolynomial.support_monomial_subset hj⟩
end
end amZ
end
section
namespace yP.aLT.Native
set_option maxRecDepth 10000
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
end
end yP.aLT.Native
end
section
namespace yP.baR
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
open yP.aLT yP.a92
end
end yP.baR
end
section
namespace yP.baR
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark
open yP.a92
end
end yP.baR
end
