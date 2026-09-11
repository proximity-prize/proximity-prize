import ProximityPrize.SubmissionLower.Part.F003_05
section Compact_PackedLegacyCore1
section PackedLegacy_AY
namespace ProximityPrize.SubmissionLower.RCN012
open Polynomial Polynomial.Bivariate RCN002 RCN005 RCN371 RCN011 RCN009 RCN013
noncomputable section
variable {A:Type} [Field A]

theorem bivariateEquiv_coeff_natDegree_le_of_support
   (f:MvPolynomial (Fin 2) A) (height:ℕ → ℕ)
   (hsupport:∀ d∈f.support,d 1 ≤ height (d 0)) (i:ℕ):
   ((bivariateEquiv A f).coeff i).natDegree ≤ height i:=by
 rw [show (bivariateEquiv A f).coeff i=
     MvPolynomial.uniqueAlgEquiv A (Fin 1)
       ((MvPolynomial.finSuccEquiv A 1 f).coeff i) by
   simp [bivariateEquiv]]
 apply (uniqueAlgEquiv_natDegree_le A _).trans
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hs:=hsupport (d.cons i)
   (MvPolynomial.mem_support_coeff_finSuccEquiv.mp hd)
 simpa only [show (1:Fin 2)=(0:Fin 1).succ by decide,
   Finsupp.cons_succ,Finsupp.cons_zero] using hs
theorem bivariateEquiv_totalDegree_le_of_support
   (f:MvPolynomial (Fin 2) A) (cap:ℕ)
   (hsupport:∀ d∈f.support,d 0+d 1 ≤ cap):
   totalDegree (bivariateEquiv A f) ≤ cap:=by
 classical
 have houter:f.degreeOf 0 ≤ cap:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (Nat.le_add_right (d 0) (d 1)).trans (hsupport d hd)
 unfold totalDegree
 apply Finset.sup_le
 intro i hi
 have hiCap:i ≤ cap:=by
   exact (Polynomial.le_natDegree_of_mem_supp i hi).trans
     ((bivariateEquiv_natDegree A f).trans_le houter)
 have hcoeff:((bivariateEquiv A f).coeff i).natDegree ≤ cap-i:=by
   apply bivariateEquiv_coeff_natDegree_le_of_support f (fun j => cap-j)
   intro d hd
   have hs:=hsupport d hd
   omega
 omega
variable (K:Type) [Field K]
theorem planeMap_totalDegree_le_of_rational_support
   (order:Fin 3 ≃ Fin 3) (F:Original K) (cap:ℕ)
   (hsupport:∀ d∈(rationalMap K order F).support,
     d 0+d 1 ≤ cap):
   totalDegree (planeMap K order F) ≤ cap:=by
 exact bivariateEquiv_totalDegree_le_of_support
   (rationalMap K order F) cap hsupport
theorem rationalMap_joint_support_of_original
   (order:Fin 3 ≃ Fin 3) (F:Original K) (cap:ℕ)
   (hsupport:∀ d∈F.support,
     d (order 1)+d (order 2) ≤ cap):
   ∀ e∈(rationalMap K order F).support,e 0+e 1 ≤ cap:=by
 classical
 intro e he
 rw [rationalMap_eq_firstMap] at he
 obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp
   (support_firstMap_subset K
     (algebraMap (Polynomial K) (RatFunc K))
     (MvPolynomial.rename order.symm F) he)
 rw [MvPolynomial.support_rename_of_injective order.symm.injective] at hd
 obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hd
 simpa only [Finsupp.tail_apply,Finsupp.mapDomain_equiv_apply,
   Equiv.symm_symm,
   show (0:Fin 2).succ=(1:Fin 3) by decide,
   show (1:Fin 2).succ=(2:Fin 3) by decide] using hsupport u hu
theorem ordinary_resultant_natDegree_le_totalDegree
   (B H:A[X][Y]) (n mCap totalB totalH cap:ℕ)
   (hHne:H≠0) (hBouter:B.natDegree ≤ n)
   (hHouter:H.natDegree ≤ mCap)
   (hBtotal:totalDegree B ≤ totalB)
   (hHtotal:totalDegree H ≤ totalH)
   (hbudget:∀ m,m ≤ mCap →
     m*totalB+n*totalH-m*n ≤ cap):
   (Polynomial.resultant B H).natDegree ≤ cap:=by
 by_cases hres:Polynomial.resultant B H=0
 · simp [hres]
 · have hfixed:=bivariate_resultant_natDegree_le_totalDegree
     B H n H.natDegree
   have hdegreeCap:
       H.natDegree*totalDegree B+n*totalDegree H-H.natDegree*n ≤
         H.natDegree*totalB+n*totalH-H.natDegree*n:=by
     exact Nat.sub_le_sub_right
       (Nat.add_le_add (Nat.mul_le_mul_left H.natDegree hBtotal)
         (Nat.mul_le_mul_left n hHtotal)) _
   have hfixedCap:
       (Polynomial.resultant B H n H.natDegree).natDegree ≤ cap:=
     hfixed.trans (hdegreeCap.trans (hbudget H.natDegree hHouter))
   have hcoeff:H.coeff H.natDegree≠0:=by
     rw [Polynomial.coeff_natDegree]
     exact Polynomial.leadingCoeff_ne_zero.mpr hHne
   let factor:A[X]:=
     (-1)^(H.natDegree*(n-B.natDegree))*
       H.coeff H.natDegree^(n-B.natDegree)
   have hfactor:factor≠0:=by
     apply _root_.mul_ne_zero
     · exact pow_ne_zero _ (by norm_num)
     · exact pow_ne_zero _ hcoeff
   have hpad:=Polynomial.resultant_add_left_deg
     (f:=B) (g:=H) (m:=B.natDegree)
     (k:=n-B.natDegree) (n:=H.natDegree) le_rfl
   have hsum:B.natDegree+(n-B.natDegree)=n:=
     Nat.add_sub_of_le hBouter
   rw [hsum] at hpad
   change Polynomial.resultant B H n H.natDegree=
     factor*Polynomial.resultant B H at hpad
   calc
     (Polynomial.resultant B H).natDegree ≤
         (factor*Polynomial.resultant B H).natDegree:=by
       rw [Polynomial.natDegree_mul hfactor hres]
       omega
     _=(Polynomial.resultant B H n H.natDegree).natDegree:=by rw [hpad]
     _ ≤ cap:=hfixedCap
theorem planeMap_trapezoid_resultant_natDegree_le
   (order:Fin 3 ≃ Fin 3) (G T:Original K)
   (n mCap totalG totalT cap:ℕ) (hTne:T≠0)
   (hGouter:(planeMap K order G).natDegree ≤ n)
   (hTouter:(planeMap K order T).natDegree ≤ mCap)
   (hGsupport:∀ d∈(rationalMap K order G).support,
     d 0+d 1 ≤ totalG)
   (hTsupport:∀ d∈(rationalMap K order T).support,
     d 0+d 1 ≤ totalT)
   (hbudget:∀ m,m ≤ mCap →
     m*totalG+n*totalT-m*n ≤ cap):
   (Polynomial.resultant (planeMap K order G)
     (planeMap K order T)).natDegree ≤ cap:=by
 apply ordinary_resultant_natDegree_le_totalDegree
   (planeMap K order G) (planeMap K order T)
     n mCap totalG totalT cap
 · intro hzero
   apply hTne
   apply planeMap_injective K order
   simpa only [map_zero] using hzero
 · exact hGouter
 · exact hTouter
 · exact planeMap_totalDegree_le_of_rational_support
     K order G totalG hGsupport
 · exact planeMap_totalDegree_le_of_rational_support
     K order T totalT hTsupport
 · exact hbudget
end
end ProximityPrize.SubmissionLower.RCN012
end PackedLegacy_AY

/-! Packed from ProximityPrize.SubmissionLower.Y. -/
section PackedLegacy_Y
namespace ProximityPrize.SubmissionLower.RCN003
open RCN002 RCN005
 RCN371 RCN011
 RCN009 RCN013 RCN010
 RCN004 RCN007 RCN001
open RCN012
noncomputable section
variable (K:Type) [Field K]
def JointOrderCertificate (order:Fin 3 ≃ Fin 3)
   (G H:Original K) (p:ℕ):Prop:=
 ∃ order':Fin 3 ≃ Fin 3,
   order' 0=order 0∧
   originalMixedDegree K order' G H=originalMixedDegree K order G H∧
   0 < (planeMap K order' G).natDegree∧
   (planeMap K order' G).natDegree < p∧
   (Polynomial.resultant (planeMap K order' G)
     (planeMap K order' H)).natDegree < p
private def singleSummary (P:Ideal (Original K)) [P.IsPrime]
   (A:Algebra (RatFunc K) (CoordinateField K P)) (B:ℕ):Prop:=
 letI:=A
 FiniteDimensional (RatFunc K) (CoordinateField K P)∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
   Module.finrank (RatFunc K) (CoordinateField K P) ≤ B
private def fieldsSummary (P:Ideal (Original K)) [P.IsPrime]
   (A:Algebra (RatFunc K) (CoordinateField K P)):Prop:=
 letI:=A
 FiniteDimensional (RatFunc K) (CoordinateField K P)∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K P)
private def familySummary {I:Type} [Fintype I]
   (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
   (A:∀ i,Algebra (RatFunc K) (CoordinateField K (P i))) (B:ℕ):Prop:=
 letI:=A
 (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
   Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
   (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤ B
theorem finite_separable_at_of_original_coordinate_gate
   (P:Ideal (Original K)) [P.IsPrime] (i:Fin 3)
   (hi:Transcendental K (coordinate K P i))
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P)
   (hproper:¬ G∣H) (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixed:coordinateMixedDegree K G H i < p):
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     rationalBaseAlgebra K P i hi
   FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
 let order:Fin 3 ≃ Fin 3:=Equiv.swap 0 i
 have hbase:order 0=i:=Equiv.swap_apply_left _ _
 have ht:Transcendental K (coordinate K P (order 0)):=by
   simpa only [hbase] using hi
 have hresult:
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       rationalBaseAlgebra K P (order 0) ht
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     rationalBaseAlgebra K P (order 0) ht
   have h:=original_finite_separable_finrank_bound K order P ht p G H
     hG hGmem hHmem hproper (hdegree (order 1)) (hdegree (order 2)) hmixed
   exact ⟨h.1,h.2.1⟩
 change fieldsSummary K P (rationalBaseAlgebra K P (order 0) ht) at hresult
 change fieldsSummary K P (rationalBaseAlgebra K P i hi)
 rw [rationalBaseAlgebra_congr K P (order 0) i hbase ht hi] at hresult
 exact hresult
end
end ProximityPrize.SubmissionLower.RCN003
end PackedLegacy_Y

/-! Packed from ProximityPrize.SubmissionLower.K8. -/
section PackedLegacy_K8
namespace ProximityPrize.SubmissionLower.RCN176
open RCN002 RCN007 RCN004 RCN001 RCN003 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
def JointRProvider (G T:MvPolynomial (Fin 3) Ω) (p:ℕ):Prop:=
 ∀ (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime],G∈P →
   Transcendental Ω (coordinate Ω P 1) →
     JointOrderCertificate Ω (Equiv.swap 0 1) G T p
end
end ProximityPrize.SubmissionLower.RCN176
end PackedLegacy_K8

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.K9. -/
section PackedLegacy_K9
namespace ProximityPrize.SubmissionLower.RCN177
open scoped BigOperators
open RCN174 RCN081 RCN313
 RCN136
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
def seedDegree (P:Poly4 K):ℕ:=
 MvPolynomial.weightedTotalDegree seedWeights P
@[simp] theorem seedDegree_neg (P:Poly4 K):
   seedDegree (-P)=seedDegree P:=by
 unfold seedDegree
 rw [←degree_weightedLift,map_neg,MvPolynomial.degreeOf_neg,
   degree_weightedLift]
end
end ProximityPrize.SubmissionLower.RCN177
end PackedLegacy_K9

/-! Packed from ProximityPrize.SubmissionLower.L0. -/
section PackedLegacy_L0
namespace ProximityPrize.SubmissionLower.RCN178
open scoped Classical BigOperators
open RCN051 RCN068 RCN136 RCN238 RCN243 RCN065 RCN231 RCN319 RCN001 RCN174 RCN306 RCN176 RCN177 RCN003 RCN012 RCN011 RCN009 RCN013 RCN371
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
variable [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
 {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
end
end ProximityPrize.SubmissionLower.RCN178
end PackedLegacy_L0

/-! Packed from ProximityPrize.SubmissionLower.Z9. -/
section PackedLegacy_Z9
namespace ProximityPrize.SubmissionLower.RCN222
open scoped Classical BigOperators
open RCN051 RCN068 RCN070 RCN135 RCN136 RCN138 RCN137 RCN267 RCN081 RCN306 RCN238 RCN243 RCN231 RCN174 RCN319 RCN178 RCN177
noncomputable section
variable (K:Type) [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)
def originalDegreeVector (F:MvPolynomial (Fin 4) K):DegreeVector:=
 ⟨F.degreeOf 1,F.degreeOf 2,F.degreeOf 3⟩
theorem selectedPoint_eq_initialPoint (selected:K → Polynomial K) (γ:K):
   selectedPoint (polynomialEmbedding K) selected γ=
     fun i:Fin 3 => initialPoint K (selected γ) γ i.succ:=rfl
theorem selectedPoint_surface_evaluation
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (γ:K):
   MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
     (surfaceMap (polynomialEmbedding K) F)=
       polynomialEmbedding K (specialization K (selected γ) γ F):=by
 rw [selectedPoint_eq_initialPoint]
 simpa only [canonical_geometricSurfaceMap] using
   eval_at_actual_generic_initial_point K (selected γ) γ F
theorem selectedPoint_regular_of_specialization
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (γ:K)
   (hregular:specialization K (selected γ) γ (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   MvPolynomial.eval₂Hom ((polynomialEmbedding K).comp Polynomial.C)
     (polynomialPoint ((polynomialEmbedding K).comp Polynomial.C)
       (selected γ) γ ((polynomialEmbedding K) Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0:=
 (initialPoint_regular_iff K F (selected γ) γ).mpr hregular
abbrev GeometricFactor (F:MvPolynomial (Fin 4) K):=
 {g:MvPolynomial (Fin 3) (GenericField K)//g∈surfaceFactors (polynomialEmbedding K) F}
def geometricSeeds (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (Γ:Finset K) (g:GeometricFactor K F):Finset K:=by
 classical
 exact Γ.filter (fun γ =>
   MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ) g.1=0)
theorem geometricSeeds_subset
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (Γ:Finset K) (g:GeometricFactor K F):geometricSeeds K F selected Γ g ⊆ Γ:=by
 classical
 exact Finset.filter_subset _ _
theorem card_le_sum_geometricSeeds
   (F:MvPolynomial (Fin 4) K) (hF:F≠0)
   (selected:K → Polynomial K) (Γ:Finset K)
   (hsolutions:∀ γ∈Γ,specialization K (selected γ) γ F=0):
   Γ.card ≤ ∑ g:GeometricFactor K F,(geometricSeeds K F selected Γ g).card:=by
 classical
 have hcover:Γ ⊆ Finset.univ.biUnion (geometricSeeds K F selected Γ):=by
   intro γ hγ
   have hz:MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
       (surfaceMap (polynomialEmbedding K) F)=0:=by
     rw [selectedPoint_surface_evaluation,hsolutions γ hγ,map_zero]
   obtain ⟨g,hg,hzg⟩:=exists_surfaceFactor_zero (polynomialEmbedding K)
     (polynomialEmbedding_injective K) F hF
     (selectedPoint (polynomialEmbedding K) selected γ) hz
   exact Finset.mem_biUnion.mpr ⟨⟨g,hg⟩,Finset.mem_univ _,
     Finset.mem_filter.mpr ⟨hγ,hzg⟩⟩
 exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le
theorem geometricFactor_degree_le
   (F:MvPolynomial (Fin 4) K) (hF:F≠0) (g:GeometricFactor K F) (i:Fin 3):
   g.1.degreeOf i ≤ F.degreeOf i.succ:=by
 have hdiv:=(surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2).2
 exact (coordinate_degree_le_of_dvd i g.1 _ hdiv
   (surfaceMap_ne_zero (polynomialEmbedding K) (polynomialEmbedding_injective K) F hF)).trans
     (surfaceMap_degreeOf_le (polynomialEmbedding K) F i)
theorem geometricFactor_sum_degree_le
   (F:MvPolynomial (Fin 4) K) (hF:F≠0) (i:Fin 3):
   (∑ g:GeometricFactor K F,g.1.degreeOf i) ≤ F.degreeOf i.succ:=by
 classical
 have hb:=surfaceFactors_degree_budget (polynomialEmbedding K)
   (polynomialEmbedding_injective K) F hF i
 rw [←Finset.sum_attach (surfaceFactors (polynomialEmbedding K) F)
   (fun g => g.degreeOf i)] at hb
 simpa only [Finset.attach_eq_univ] using hb
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
end
end ProximityPrize.SubmissionLower.RCN222
end PackedLegacy_Z9

/-! Packed from ProximityPrize.SubmissionLower.DW. -/
section PackedLegacy_DW
namespace ProximityPrize.SubmissionLower.RCN052
open scoped Classical BigOperators
open RCN260 RCN318 RCN294 RCN286 RCN169 RCN167 RCN290 RCN082 RCN081 RCN174 RCN319 RCN136 RCN137 RCN138 RCN135 RCN222 RCN243 RCN068 RCN238 RCN001
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev RegularIndex (Q:MvPolynomial (Fin 4) K):=
 ↥(positiveRFactors Q)
abbrev ImplicitIndex (Q:MvPolynomial (Fin 4) K):=
 ↥(implicitPairSet (singularAuxiliary Q))
def regularPairSeeds (Q T:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (F:RegularIndex Q):Finset K:=
 Gamma.filter fun gamma↦
   RegularSolution F.1 (selected gamma) gamma∧
     specialization K (selected gamma) gamma T=0
def implicitSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (q:ImplicitIndex Q):Finset K:=
 Gamma.filter fun gamma↦LiftedSolutionPair q.1 (selected gamma) gamma
def singularSeeds (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K):Finset K:=
 Finset.univ.biUnion (implicitSeeds Q selected Gamma) ∪
   exceptionalSeeds (singularAuxiliary Q) Gamma selected
theorem regularPairSeeds_subset (Q T:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K) (F:RegularIndex Q):
   regularPairSeeds Q T selected Gamma F ⊆ Gamma:=
 Finset.filter_subset _ _
theorem implicitSeeds_subset (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K) (q:ImplicitIndex Q):
   implicitSeeds Q selected Gamma q ⊆ Gamma:=
 Finset.filter_subset _ _
theorem regularPairSeeds_data (Q T:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K) (F:RegularIndex Q)
   (gamma:K) (hgamma:gamma∈regularPairSeeds Q T selected Gamma F):
   RegularSolution F.1 (selected gamma) gamma∧
     specialization K (selected gamma) gamma T=0:=
 (Finset.mem_filter.mp hgamma).2
theorem singularSeeds_card_le_sum
   (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K):
   (singularSeeds Q selected Gamma).card ≤
     (∑ q:ImplicitIndex Q,(implicitSeeds Q selected Gamma q).card)+
       (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card:=by
 exact (Finset.card_union_le _ _).trans
   (Nat.add_le_add_right Finset.card_biUnion_le _)
theorem card_le_regular_sum_add_singular
   (Q T:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s p:ℕ) [CharP K p]
   (hs:1 ≤ s) (hsmall:s < p) (hw:1 ≤ w)
   (hDw:w < (2*s-1)*D)
   (hj:1 ≤ (2*s-1)*L) (hjSmall:(2*s-1)*L < p)
   (hbox:Q∈globalCoefficientBox K D w L s)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hQsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hTsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma T=0):
   Gamma.card ≤
     (∑ F:RegularIndex Q,(regularPairSeeds Q T selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=by
 classical
 have hdecomp:=selected_seed_decomposition Q hQ D w L s p hs hsmall hw
   hDw hj hjSmall hbox Gamma selected hQsolution
 let regularUnion:=Finset.univ.biUnion (regularPairSeeds Q T selected Gamma)
 have hsub:Gamma ⊆ regularUnion ∪ singularSeeds Q selected Gamma:=by
   intro gamma hgamma
   by_cases hexc:gamma∈exceptionalSeeds (singularAuxiliary Q) Gamma selected
   · exact Finset.mem_union_right _ (Finset.mem_union_right _ hexc)
   · obtain ⟨F,hF,hreg⟩ | ⟨q,hq,himp⟩:=hdecomp.2.1 gamma hgamma hexc
     · apply Finset.mem_union_left
       exact Finset.mem_biUnion.mpr ⟨⟨F,hF⟩,Finset.mem_univ _,
         Finset.mem_filter.mpr ⟨hgamma,hreg,hTsolution gamma hgamma⟩⟩
     · apply Finset.mem_union_right
       apply Finset.mem_union_left
       exact Finset.mem_biUnion.mpr ⟨⟨q,hq⟩,Finset.mem_univ _,
         Finset.mem_filter.mpr ⟨hgamma,himp⟩⟩
 calc
   Gamma.card ≤ (regularUnion ∪ singularSeeds Q selected Gamma).card:=
     Finset.card_le_card hsub
   _ ≤ regularUnion.card+(singularSeeds Q selected Gamma).card:=
     Finset.card_union_le _ _
   _ ≤ (∑ F:RegularIndex Q,
         (regularPairSeeds Q T selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=
     Nat.add_le_add_right Finset.card_biUnion_le _
theorem regularFactor_not_dvd_second
   (Q T:MvPolynomial (Fin 4) K) (hrel:IsRelPrime Q T)
   (F:RegularIndex Q):¬ F.1∣T:=by
 obtain ⟨hirr,hdiv,_⟩:=positiveRFactors_spec Q F.1 F.2
 intro hFT
 exact hirr.not_isUnit (hrel hdiv hFT)
theorem geometricFactor_not_dvd_second
   (Q T:MvPolynomial (Fin 4) K) (hrel:IsRelPrime Q T)
   (F:RegularIndex Q)
   (g:MvPolynomial (Fin 3) (GenericField K))
   (hg:g∈surfaceFactors (polynomialEmbedding K) F.1):
   ¬ g∣surfaceMap (polynomialEmbedding K) T:=by
 obtain ⟨hFirr,_hFdiv,hFRpos⟩:=positiveRFactors_spec Q F.1 F.2
 obtain ⟨hgirred,hgdiv⟩:=
   surfaceFactors_spec (polynomialEmbedding K) F.1 g hg
 have hpos:0 < F.1.degreeOf 1+F.1.degreeOf 2+F.1.degreeOf 3:=by
   omega
 have hgeo:g∣geometricSurfaceMap K (GenericField K) F.1:=by
   simpa only [canonical_geometricSurfaceMap] using hgdiv
 intro hgT
 apply regularFactor_not_dvd_second Q T hrel F
 apply (geometric_factor_dvd_iff K (GenericField K) F.1 T hFirr hpos
   g hgirred hgeo).mp
 simpa only [canonical_geometricSurfaceMap] using hgT
def regularVector (P:UnequalParameters)
   (F:MvPolynomial (Fin 4) K):RCN223.DegreeVector:=
 ⟨F.degreeOf 2*P.rightZ+F.degreeOf 3*P.rightR,
   F.degreeOf 1*P.rightZ+F.degreeOf 3*P.rightY,
   F.degreeOf 1*P.rightR+F.degreeOf 2*P.rightY⟩
def regularCapAt (v:RCN223.DegreeVector):Fin 3 → ℕ:=
 ![v.y,v.r,v.z]
theorem sum_coordinateMixedDegree_geometricFactors_le
   (P:UnequalParameters) (F T:MvPolynomial (Fin 4) K) (hF:F≠0)
   (hTY:T.degreeOf 1 ≤ P.rightY) (hTR:T.degreeOf 2 ≤ P.rightR)
   (hTZ:T.degreeOf 3 ≤ P.rightZ) (i:Fin 3):
   (∑ g:GeometricFactor K F,
     coordinateMixedDegree (GenericField K) g.1
       (surfaceMap (polynomialEmbedding K) T) i) ≤
     regularCapAt (regularVector P F) i:=by
 classical
 have hsum (j:Fin 3):
     (∑ g:GeometricFactor K F,g.1.degreeOf j) ≤ F.degreeOf j.succ:=
   geometricFactor_sum_degree_le K F hF j
 have hsum0:(∑ g:GeometricFactor K F,g.1.degreeOf 0) ≤ F.degreeOf 1:=by
   simpa using hsum 0
 have hsum1:(∑ g:GeometricFactor K F,g.1.degreeOf 1) ≤ F.degreeOf 2:=by
   simpa using hsum 1
 have hsum2:(∑ g:GeometricFactor K F,g.1.degreeOf 2) ≤ F.degreeOf 3:=by
   have h:=hsum 2
   rw [show (2:Fin 3).succ=(3:Fin 4) by decide] at h
   exact h
 have hT0:(surfaceMap (polynomialEmbedding K) T).degreeOf 0 ≤ P.rightY:=
   (surfaceMap_degreeOf_le (polynomialEmbedding K) T 0).trans hTY
 have hT1:(surfaceMap (polynomialEmbedding K) T).degreeOf 1 ≤ P.rightR:=
   (surfaceMap_degreeOf_le (polynomialEmbedding K) T 1).trans hTR
 have hT2:(surfaceMap (polynomialEmbedding K) T).degreeOf 2 ≤ P.rightZ:=
   (surfaceMap_degreeOf_le (polynomialEmbedding K) T 2).trans hTZ
 have hi:i=0∨i=1∨i=2:=by omega
 rcases hi with rfl | rfl | rfl
 · change (∑ geom:GeometricFactor K F,
       ((surfaceMap (polynomialEmbedding K) T).degreeOf 1*geom.1.degreeOf 2+
         geom.1.degreeOf 1*(surfaceMap (polynomialEmbedding K) T).degreeOf 2)) ≤
       F.degreeOf 2*P.rightZ+F.degreeOf 3*P.rightR
   rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.sum_mul]
   simpa only [Nat.add_comm,Nat.mul_comm] using
     Nat.add_le_add (Nat.mul_le_mul hT1 hsum2)
       (Nat.mul_le_mul hsum1 hT2)
 · change (∑ geom:GeometricFactor K F,
       ((surfaceMap (polynomialEmbedding K) T).degreeOf 0*geom.1.degreeOf 2+
         geom.1.degreeOf 0*(surfaceMap (polynomialEmbedding K) T).degreeOf 2)) ≤
       F.degreeOf 1*P.rightZ+F.degreeOf 3*P.rightY
   rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.sum_mul]
   simpa only [Nat.add_comm,Nat.mul_comm] using
     Nat.add_le_add (Nat.mul_le_mul hT0 hsum2)
       (Nat.mul_le_mul hsum0 hT2)
 · simp only [RCN001.coordinateMixedDegree_two,
     regularCapAt,regularVector,Matrix.cons_val_two]
   change (∑ geom:GeometricFactor K F,
       ((surfaceMap (polynomialEmbedding K) T).degreeOf 0*geom.1.degreeOf 1+
         geom.1.degreeOf 0*(surfaceMap (polynomialEmbedding K) T).degreeOf 1)) ≤
       F.degreeOf 1*P.rightR+F.degreeOf 2*P.rightY
   rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.sum_mul]
   simpa only [Nat.add_comm,Nat.mul_comm] using
     Nat.add_le_add (Nat.mul_le_mul hT0 hsum1)
       (Nat.mul_le_mul hsum0 hT1)
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem regularPairSeeds_bound
   (P:UnequalParameters) (Q T:MvPolynomial (Fin 4) K)
   (hrel:IsRelPrime Q T) (F:RegularIndex Q)
   (p:ℕ) [CharP K p]
   (hFY:F.1.degreeOf 1 ≤ P.leftY)
   (hFR:F.1.degreeOf 2 ≤ P.leftR)
   (hFZ:F.1.degreeOf 3 ≤ P.leftZ)
   (hTY:T.degreeOf 1 ≤ P.rightY)
   (hTR:T.degreeOf 2 ≤ P.rightR)
   (hTZ:T.degreeOf 3 ≤ P.rightZ)
   (hleftR:1 ≤ P.leftR)
   (hleftYSmall:P.leftY < p) (hleftRSmall:P.leftR < p)
   (hleftZSmall:P.leftZ < p)
   (hmixedYSmall:P.mixedCost.y < p)
   (hmixedRSmall:P.mixedCost.r < p)
   (hmixedZSmall:P.mixedCost.z < p)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=P.n)
   (hw:1 ≤ P.w) (hchar:P.w < p) (hwa:P.w < P.a)
   (han:P.a ≤ P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u₀ i+gamma*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors):
   (regularPairSeeds Q T selected Gamma F).card*P.gap ≤
     (P.n-P.w)*dot P.agreement (regularVector P F.1)+
       (P.errors+1)*P.gap*(regularVector P F.1).z:=by
 classical
 let phi:=polynomialEmbedding K
 let Delta:=regularPairSeeds Q T selected Gamma F
 let carrierCap:RCN051.DegreeVector:=
   ⟨P.leftY,P.leftR,P.leftZ⟩
 let cutCap:RCN051.DegreeVector:=
   ⟨P.rightY,P.rightR,P.rightZ⟩
 have hFspec:=positiveRFactors_spec Q F.1 F.2
 have hFne:F.1≠0:=hFspec.1.ne_zero
 have hDeltaSub:Delta ⊆ Gamma:=regularPairSeeds_subset Q T selected Gamma F
 have hDeltaData (gamma:K) (hgamma:gamma∈Delta):
     RegularSolution F.1 (selected gamma) gamma∧
       specialization K (selected gamma) gamma T=0:=
   regularPairSeeds_data Q T selected Gamma F gamma hgamma
 have hcover:=card_le_sum_geometricSeeds K F.1 hFne selected Delta
   (fun gamma hgamma => (hDeltaData gamma hgamma).1.1)
 letI:CharP (GenericField K) p:=genericField_charP K p
 have hsingle (g:GeometricFactor K F.1):
     (geometricSeeds K F.1 selected Delta g).card*P.gap ≤
       (P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.agreement i*
           coordinateMixedDegree (GenericField K) g.1
             (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           coordinateMixedDegree (GenericField K) g.1
             (surfaceMap phi T) 2:=by
   have hgSpec:=surfaceFactors_spec phi F.1 g.1 g.2
   have hsub:=geometricSeeds_subset K F.1 selected Delta g
   have hgCaps:HasCaps g.1 carrierCap:=by
     intro i
     have hi:=geometricFactor_degree_le K F.1 hFne g i
     fin_cases i
     · exact hi.trans hFY
     · exact hi.trans hFR
     · exact hi.trans hFZ
   have hTCaps:HasCaps (surfaceMap phi T) cutCap:=by
     intro i
     fin_cases i
     · exact (surfaceMap_degreeOf_le phi T 0).trans hTY
     · exact (surfaceMap_degreeOf_le phi T 1).trans hTR
     · exact (surfaceMap_degreeOf_le phi T 2).trans hTZ
   have hcarrierSmall:∀ i,capAt carrierCap i < p:=by
     intro i
     fin_cases i
     · exact hleftYSmall
     · exact hleftRSmall
     · exact hleftZSmall
   have hgates:=actual_characteristic_gates g.1 (surfaceMap phi T)
     carrierCap cutCap p hgCaps hTCaps hcarrierSmall
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitY,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedYSmall)
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitR,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedRSmall)
     (by simpa [carrierCap,cutCap,RCN051.mixed,
         RCN051.unitZ,UnequalParameters.mixedCost,
         capAt,Nat.add_comm,Nat.mul_comm] using hmixedZSmall)
   have hregular:∀ gamma∈geometricSeeds K F.1 selected Delta g,
       MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
         (RCN231.polynomialPoint (phi.comp Polynomial.C)
           (selected gamma) gamma (phi Polynomial.X))
         (MvPolynomial.pderiv (2:Fin 4) F.1)≠0:=by
     intro gamma hgamma
     exact selectedPoint_regular_of_specialization K F.1 selected gamma
       (hDeltaData gamma (hsub hgamma)).1.2
   have hTpoint:∀ gamma∈geometricSeeds K F.1 selected Delta g,
       MvPolynomial.eval (selectedPoint phi selected gamma) (surfaceMap phi T)=0:=by
     intro gamma hgamma
     rw [selectedPoint_surface_evaluation,
       (hDeltaData gamma (hsub hgamma)).2,map_zero]
   have hcap (node:ι):∀ j,
       (agreementPolynomial phi F.1 P.w (x node) (u₀ node) (u₁ node)).degreeOf j ≤
         regularCapAt P.agreement j:=by
     have h:=surface_agreement_caps phi F.1 P.leftY P.leftR P.leftZ hleftR
       hFY hFR hFZ P.w (fun j => (j.factorial:K)⁻¹)
       (x node) (u₀ node) (u₁ node)
     intro j
     have hj:
         (agreementPolynomial phi F.1 P.w (x node) (u₀ node) (u₁ node)).degreeOf j ≤
           capAt (agreementCaps P.leftY P.leftR P.leftZ P.w) j:=by
       simpa [agreementPolynomial] using h j
     fin_cases j
     · apply hj.trans
       change P.leftAgreement.y ≤ max P.leftAgreement.y P.rightAgreement.y
       exact le_max_left _ _
     · apply hj.trans
       change P.leftAgreement.r ≤ max P.leftAgreement.r P.rightAgreement.r
       exact le_max_left _ _
     · apply hj.trans
       change P.leftAgreement.z ≤ max P.leftAgreement.z P.rightAgreement.z
       exact le_max_left _ _
   have hcount:=proper_cut_seed_bound phi F.1 g.1 (surfaceMap phi T)
     hgSpec.1 hgSpec.2 (geometricFactor_not_dvd_second Q T hrel F g.1 g.2)
     selected (geometricSeeds K F.1 selected Delta g) nodes x u₀ u₁ hinj
     p P.w P.a P.errors hw hchar hwa (by simpa [hnodes] using han)
     hgates.1 hgates.2
     (fun gamma hgamma => hdegree gamma (hDeltaSub (hsub hgamma)))
     (fun gamma hgamma => (hDeltaData gamma (hsub hgamma)).1.1)
     hregular (fun gamma hgamma => (Finset.mem_filter.mp hgamma).2)
     hTpoint
     (fun gamma hgamma => hagreement gamma (hDeltaSub (hsub hgamma)))
     (noLargeSelectedPencil_mono selected Gamma _ P.w P.errors
       (fun _ hgamma => hDeltaSub (hsub hgamma)) hnoPencil)
     (regularCapAt P.agreement) (fun node _ => hcap node)
   simpa [hnodes,UnequalParameters.gap] using hcount
 have hbudget (i:Fin 3):=
   sum_coordinateMixedDegree_geometricFactors_le P F.1 T hFne hTY hTR hTZ i
 have hfubini:
     (∑ g:GeometricFactor K F.1,∑ i:Fin 3,
         regularCapAt P.agreement i*
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)=
       ∑ i:Fin 3,regularCapAt P.agreement i*
         (∑ g:GeometricFactor K F.1,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Delta.card*P.gap ≤
       (∑ g:GeometricFactor K F.1,
         (geometricSeeds K F.1 selected Delta g).card)*P.gap:=
     Nat.mul_le_mul_right P.gap hcover
   _=∑ g:GeometricFactor K F.1,
       (geometricSeeds K F.1 selected Delta g).card*P.gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g:GeometricFactor K F.1,
       ((P.n-P.w)*(∑ i:Fin 3,regularCapAt P.agreement i*
         coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i)+
         (P.errors+1)*P.gap*
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2):=
     Finset.sum_le_sum (fun g _ => hsingle g)
   _=(P.n-P.w)*(∑ i:Fin 3,regularCapAt P.agreement i*
         (∑ g:GeometricFactor K F.1,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) i))+
       (P.errors+1)*P.gap*
         (∑ g:GeometricFactor K F.1,
           coordinateMixedDegree (GenericField K) g.1 (surfaceMap phi T) 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ (P.n-P.w)*(∑ i:Fin 3,
         regularCapAt P.agreement i*regularCapAt (regularVector P F.1) i)+
       (P.errors+1)*P.gap*regularCapAt (regularVector P F.1) 2:=
     Nat.add_le_add
       (Nat.mul_le_mul_left _ (Finset.sum_le_sum
         (fun i _ => Nat.mul_le_mul_left _ (hbudget i))))
       (Nat.mul_le_mul_left _ (hbudget 2))
   _=(P.n-P.w)*dot P.agreement (regularVector P F.1)+
       (P.errors+1)*P.gap*(regularVector P F.1).z:=by
     simp [Fin.sum_univ_three,regularCapAt,dot]
theorem all_regularPairSeeds_bound
   (P:UnequalParameters) (Q T:MvPolynomial (Fin 4) K)
   (hQ:Q≠0) (hrel:IsRelPrime Q T)
   (D w L s p:ℕ) [CharP K p]
   (hbox:Q∈globalCoefficientBox K D w L s) (hwBox:1 ≤ w)
   (hY:(D-1)/w ≤ P.leftY)
   (hR:s ≤ P.leftR) (hZ:L ≤ P.leftZ)
   (hTY:T.degreeOf 1 ≤ P.rightY)
   (hTR:T.degreeOf 2 ≤ P.rightR)
   (hTZ:T.degreeOf 3 ≤ P.rightZ)
   (hleftR:1 ≤ P.leftR)
   (hleftYSmall:P.leftY < p) (hleftRSmall:P.leftR < p)
   (hleftZSmall:P.leftZ < p)
   (hmixedYSmall:P.mixedCost.y < p)
   (hmixedRSmall:P.mixedCost.r < p)
   (hmixedZSmall:P.mixedCost.z < p)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=P.n)
   (hw:1 ≤ P.w) (hchar:P.w < p) (hwa:P.w < P.a)
   (han:P.a ≤ P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u₀ i+gamma*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors):
   ∀ F:RegularIndex Q,
     (regularPairSeeds Q T selected Gamma F).card*P.gap ≤
       (P.n-P.w)*dot P.agreement (regularVector P F.1)+
         (P.errors+1)*P.gap*(regularVector P F.1).z:=by
 intro F
 have hFbox:=(directFactor_data Q F.1 hQ D w L s hbox F.2).2.2
 have hFcaps:=degree_bounds_of_mem_box F.1 D w L s hwBox hFbox
 exact regularPairSeeds_bound P Q T hrel F p
   (hFcaps.1.trans (by simpa using hY))
   (hFcaps.2.1.trans hR) (hFcaps.2.2.trans hZ)
   hTY hTR hTZ hleftR hleftYSmall hleftRSmall hleftZSmall
   hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma nodes x u₀ u₁
   hinj hnodes hw hchar hwa han hdegree hagreement hnoPencil
def implicitVector (q:(_:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K):
   RCN223.DegreeVector:=
 ⟨pairYCost (K:=K) q,pairRCost (K:=K) q,pairZCost (K:=K) q⟩
theorem regularVector_budgets
   (P:UnequalParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s:ℕ) (hw:0 < w)
   (hbox:Q∈globalCoefficientBox K D w L s)
   (hY:(D-1)/w ≤ P.leftY)
   (hR:s ≤ P.leftR) (hZ:L ≤ P.leftZ):
   (∑ F:RegularIndex Q,(regularVector P F.1).y) ≤ P.mixedCost.y∧
     (∑ F:RegularIndex Q,(regularVector P F.1).r) ≤ P.mixedCost.r∧
     (∑ F:RegularIndex Q,(regularVector P F.1).z) ≤ P.mixedCost.z:=by
 classical
 have hb:=directFactor_input_budgets Q hQ D w L s hw hbox
 have hbY:(∑ F:RegularIndex Q,F.1.degreeOf (1:Fin 4)) ≤ (D-1)/w:=by
   rw [←Finset.sum_subtype (positiveRFactors Q) (fun _↦Iff.rfl)]
   exact hb.1
 have hbR:(∑ F:RegularIndex Q,F.1.degreeOf (2:Fin 4)) ≤ s:=by
   rw [←Finset.sum_subtype (positiveRFactors Q) (fun _↦Iff.rfl)]
   exact hb.2.1
 have hbZ:(∑ F:RegularIndex Q,F.1.degreeOf (3:Fin 4)) ≤ L:=by
   rw [←Finset.sum_subtype (positiveRFactors Q) (fun _↦Iff.rfl)]
   exact hb.2.2
 simp only [regularVector,Finset.sum_add_distrib]
 constructor
 · rw [←Finset.sum_mul, ←Finset.sum_mul]
   exact Nat.add_le_add
     (Nat.mul_le_mul_right P.rightZ (hbR.trans hR))
     (Nat.mul_le_mul_right P.rightR (hbZ.trans hZ))
 constructor
 · rw [←Finset.sum_mul, ←Finset.sum_mul]
   exact Nat.add_le_add
     (Nat.mul_le_mul_right P.rightZ (hbY.trans hY))
     (Nat.mul_le_mul_right P.rightY (hbZ.trans hZ))
 · rw [←Finset.sum_mul, ←Finset.sum_mul]
   exact Nat.add_le_add
     (Nat.mul_le_mul_right P.rightR (hbY.trans hY))
     (Nat.mul_le_mul_right P.rightY (hbR.trans hR))
theorem dot_sum_right {I:Type} [Fintype I]
   (v:I → RCN223.DegreeVector)
   (a:RCN223.DegreeVector):
   dot a (RCN294.sumVector v)=∑ i,dot a (v i):=by
 calc
   _=dot (RCN294.sumVector v) a:=by
     simp only [dot]
     ring
   _=∑ i,dot (v i) a:=
     RCN294.dot_sum_left v a
   _=_:=by
     apply Finset.sum_congr rfl
     intro i _
     simp only [dot]
     ring
theorem sum_regular_counts_bound
   (P:UnequalParameters) (Q T:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hcost:
     (∑ F:RegularIndex Q,(regularVector P F.1).y) ≤ P.mixedCost.y∧
     (∑ F:RegularIndex Q,(regularVector P F.1).r) ≤ P.mixedCost.r∧
     (∑ F:RegularIndex Q,(regularVector P F.1).z) ≤ P.mixedCost.z)
   (hcount:∀ F:RegularIndex Q,
     (regularPairSeeds Q T selected Gamma F).card*P.gap ≤
       (P.n-P.w)*dot P.agreement (regularVector P F.1)+
         (P.errors+1)*P.gap*(regularVector P F.1).z):
   (∑ F:RegularIndex Q,(regularPairSeeds Q T selected Gamma F).card)*
       P.gap ≤ P.regularNumerator:=by
 calc
   _=∑ F:RegularIndex Q,
       (regularPairSeeds Q T selected Gamma F).card*P.gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ F:RegularIndex Q,
       ((P.n-P.w)*dot P.agreement (regularVector P F.1)+
         (P.errors+1)*P.gap*(regularVector P F.1).z):=
     Finset.sum_le_sum fun F _↦hcount F
   _=(P.n-P.w)*dot P.agreement
         (RCN294.sumVector fun F:RegularIndex Q↦
           regularVector P F.1)+
       (P.errors+1)*P.gap*
         (RCN294.sumVector fun F:RegularIndex Q↦
           regularVector P F.1).z:=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,
       ←dot_sum_right]
     simp only [RCN294.sumVector]
   _ ≤ (P.n-P.w)*dot P.agreement P.mixedCost+
       (P.errors+1)*P.gap*P.mixedCost.z:=by
     apply Nat.add_le_add
     · exact Nat.mul_le_mul_left _ (Nat.add_le_add
         (Nat.add_le_add
           (Nat.mul_le_mul_left P.agreement.y hcost.1)
           (Nat.mul_le_mul_left P.agreement.r hcost.2.1))
         (Nat.mul_le_mul_left P.agreement.z hcost.2.2))
     · exact Nat.mul_le_mul_left _ hcost.2.2
   _=P.regularNumerator:=rfl
end
end ProximityPrize.SubmissionLower.RCN052
end PackedLegacy_DW

/-! Packed from ProximityPrize.SubmissionLower.BP. -/
section PackedLegacy_BP
namespace ProximityPrize.SubmissionLower.RCN157
open RCN136 RCN319
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K Omega:Type} [Field K] [Field Omega]
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
def embedX (K:Type) [Field K]:Polynomial K →+*Poly4 K:=
 Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (0:Fin 4))
@[simp] theorem embedX_C (a:K):
   embedX K (Polynomial.C a)=MvPolynomial.C a:=by
 simp [embedX]
@[simp] theorem embedX_X:
   embedX K Polynomial.X=MvPolynomial.X (0:Fin 4):=by
 simp [embedX]
@[simp] theorem pderiv_embedX_R (P:Polynomial K):
   MvPolynomial.pderiv (2:Fin 4) (embedX K P)=0:=by
 induction P using Polynomial.induction_on' with
 | add P Q hP hQ => simp [hP,hQ]
 | monomial n a =>
     simp [embedX,MvPolynomial.pderiv_X]
@[simp] theorem specialization_embedX (C:Polynomial K) (gamma:K)
   (P:Polynomial K):
   specialization K C gamma (embedX K P)=P:=by
 change ((specialization K C gamma).toRingHom.comp (embedX K)) P=
   (RingHom.id (Polynomial K)) P
 congr 1
 apply Polynomial.ringHom_ext
 · intro a
   simp [embedX,specialization,RingHom.comp_apply]
 · simp [embedX,specialization,RingHom.comp_apply]
@[simp] theorem specialization_X (C:Polynomial K) (gamma:K)
   (i:Fin 4):
   specialization K C gamma (MvPolynomial.X i)=
     ![Polynomial.X,C,C.derivative,Polynomial.C gamma] i:=by
 simp [specialization]
@[simp] theorem surfaceMap_embedX (phi:Polynomial K →+*Omega)
   (P:Polynomial K):
   surfaceMap phi (embedX K P)=MvPolynomial.C (phi P):=by
 change ((surfaceMap phi).comp (embedX K)) P=
   (MvPolynomial.C.comp phi) P
 congr 1
 apply Polynomial.ringHom_ext
 · intro a
   simp [embedX,surfaceMap,RingHom.comp_apply]
 · simp [embedX,surfaceMap,RingHom.comp_apply]
@[simp] theorem surfaceMap_X_one (phi:Polynomial K →+*Omega):
   surfaceMap phi (MvPolynomial.X (1:Fin 4))=
     MvPolynomial.X (0:Fin 3):=by
 simpa using surfaceMap_X_succ phi (0:Fin 3)
@[simp] theorem surfaceMap_X_two (phi:Polynomial K →+*Omega):
   surfaceMap phi (MvPolynomial.X (2:Fin 4))=
     MvPolynomial.X (1:Fin 3):=by
 simpa using surfaceMap_X_succ phi (1:Fin 3)
@[simp] theorem surfaceMap_X_three (phi:Polynomial K →+*Omega):
   surfaceMap phi (MvPolynomial.X (3:Fin 4))=
     MvPolynomial.X (2:Fin 3):=by
 simpa using surfaceMap_X_succ phi (2:Fin 3)
def globalResidualImage (P0 P1 V:Polynomial K) (i:Fin 4):Poly4 K:=
 ![MvPolynomial.X 0,
   embedX K P0+MvPolynomial.X 3*embedX K P1+
     embedX K V*MvPolynomial.X 1,
   embedX K P0.derivative+MvPolynomial.X 3*embedX K P1.derivative+
     embedX K V.derivative*MvPolynomial.X 1+
     embedX K V*MvPolynomial.X 2,
   MvPolynomial.X 3] i
def globalResidualHom (P0 P1 V:Polynomial K):Poly4 K →ₐ[K] Poly4 K:=
 MvPolynomial.aeval (globalResidualImage P0 P1 V)
@[simp] theorem globalResidualHom_X (P0 P1 V:Polynomial K) (i:Fin 4):
   globalResidualHom P0 P1 V (MvPolynomial.X i)=
     globalResidualImage P0 P1 V i:=by
 simp [globalResidualHom]
theorem specialization_globalResidualHom
   (P0 P1 V C:Polynomial K) (gamma:K) (F:Poly4 K):
   specialization K C gamma (globalResidualHom P0 P1 V F)=
     specialization K
       (P0+Polynomial.C gamma*P1+V*C) gamma F:=by
 let S:=P0+Polynomial.C gamma*P1+V*C
 have hSderiv:S.derivative=
     P0.derivative+Polynomial.C gamma*P1.derivative+
       V.derivative*C+V*C.derivative:=by
   simp only [S,Polynomial.derivative_add,Polynomial.derivative_mul,
     Polynomial.derivative_C,zero_mul,zero_add]
   ring
 have hhom:
     (specialization K C gamma).comp (globalResidualHom P0 P1 V)=
       specialization K S gamma:=by
   apply MvPolynomial.algHom_ext
   intro i
   fin_cases i <;>
     simp [globalResidualImage,hSderiv,S] <;> ring
 exact DFunLike.congr_fun hhom F
theorem globalResidual_solution
   (P0 P1 V C:Polynomial K) (gamma:K) (F:Poly4 K)
   (hsolution:specialization K
     (P0+Polynomial.C gamma*P1+V*C) gamma F=0):
   specialization K C gamma (globalResidualHom P0 P1 V F)=0:=by
 rw [specialization_globalResidualHom]
 exact hsolution
theorem pderiv_globalResidualHom_R
   (P0 P1 V:Polynomial K) (F:Poly4 K):
   MvPolynomial.pderiv (2:Fin 4) (globalResidualHom P0 P1 V F)=
     embedX K V*globalResidualHom P0 P1 V
       (MvPolynomial.pderiv (2:Fin 4) F):=by
 induction F using MvPolynomial.induction_on with
 | C a => simp
 | add F G hF hG => simp [hF,hG,mul_add]
 | mul_X F i hF =>
     fin_cases i <;>
       simp [globalResidualImage,hF,Derivation.leibniz] <;> ring
theorem eval_globalResidualHom_polynomialPoint
   (coefficients:K →+*Omega) (P0 P1 V C:Polynomial K)
   (gamma:K) (xi:Omega) (F:Poly4 K):
   MvPolynomial.eval₂Hom coefficients
       (RCN231.polynomialPoint coefficients C gamma xi)
       (globalResidualHom P0 P1 V F)=
     MvPolynomial.eval₂Hom coefficients
       (RCN231.polynomialPoint coefficients
         (P0+Polynomial.C gamma*P1+V*C) gamma xi) F:=by
 rw [RCN231.eval_polynomialPoint_eq_specialization,
   RCN231.eval_polynomialPoint_eq_specialization,
   specialization_globalResidualHom]
theorem globalResidual_regular_at_polynomialPoint
   (coefficients:K →+*Omega) (P0 P1 V C:Polynomial K)
   (gamma:K) (xi:Omega) (F:Poly4 K)
   (hV:V.eval₂ coefficients xi≠0)
   (hregular:MvPolynomial.eval₂Hom coefficients
     (RCN231.polynomialPoint coefficients
       (P0+Polynomial.C gamma*P1+V*C) gamma xi)
     (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   MvPolynomial.eval₂Hom coefficients
     (RCN231.polynomialPoint coefficients C gamma xi)
     (MvPolynomial.pderiv (2:Fin 4)
       (globalResidualHom P0 P1 V F))≠0:=by
 rw [pderiv_globalResidualHom_R,map_mul,
   eval_globalResidualHom_polynomialPoint]
 have hembed:MvPolynomial.eval₂Hom coefficients
     (RCN231.polynomialPoint coefficients C gamma xi)
     (embedX K V)=V.eval₂ coefficients xi:=by
   change ((MvPolynomial.eval₂Hom coefficients
     (RCN231.polynomialPoint coefficients C gamma xi)).comp
       (embedX K)) V=(Polynomial.eval₂RingHom coefficients xi) V
   congr 1
   apply Polynomial.ringHom_ext
   · intro a
     simp [embedX,RCN231.polynomialPoint,
       RingHom.comp_apply]
   · simp [embedX,RCN231.polynomialPoint,
       RingHom.comp_apply]
 rw [hembed]
 exact mul_ne_zero hV hregular
abbrev Poly3 (Omega:Type) [Field Omega]:=MvPolynomial (Fin 3) Omega
def componentResidualImage
   (aY v bY aR bR cR:Omega) (i:Fin 3):Poly3 Omega:=
 ![MvPolynomial.C aY+MvPolynomial.C v*MvPolynomial.X 0+
     MvPolynomial.C bY*MvPolynomial.X 2,
   MvPolynomial.C aR+MvPolynomial.C v*MvPolynomial.X 1+
     MvPolynomial.C bR*MvPolynomial.X 0+
     MvPolynomial.C cR*MvPolynomial.X 2,
   MvPolynomial.X 2] i
def componentResidualHom
   (aY v bY aR bR cR:Omega):Poly3 Omega →ₐ[Omega] Poly3 Omega:=
 MvPolynomial.aeval (componentResidualImage aY v bY aR bR cR)
@[simp] theorem componentResidualHom_X
   (aY v bY aR bR cR:Omega) (i:Fin 3):
   componentResidualHom aY v bY aR bR cR (MvPolynomial.X i)=
     componentResidualImage aY v bY aR bR cR i:=by
 simp [componentResidualHom]
theorem surfaceMap_globalResidualHom
   (phi:Polynomial K →+*Omega) (P0 P1 V:Polynomial K) (F:Poly4 K):
   surfaceMap phi (globalResidualHom P0 P1 V F)=
     componentResidualHom (phi P0) (phi V) (phi P1)
       (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
       (surfaceMap phi F):=by
 have hhom:
     (surfaceMap phi).comp (globalResidualHom P0 P1 V).toRingHom=
       (componentResidualHom (phi P0) (phi V) (phi P1)
         (phi P0.derivative) (phi V.derivative) (phi P1.derivative)).toRingHom.comp
         (surfaceMap phi):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [RingHom.comp_apply,globalResidualHom,componentResidualHom]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,globalResidualImage,componentResidualImage,
         globalResidualHom,componentResidualHom] <;> ring
 exact RingHom.congr_fun hhom F
end
end ProximityPrize.SubmissionLower.RCN157
end PackedLegacy_BP

/-! Packed from ProximityPrize.SubmissionLower.AA. -/
section PackedLegacy_AA
namespace ProximityPrize.SubmissionLower.RCN234
open scoped BigOperators
open RCN081 RCN167 RCN313
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
def wt (weights:Fin 4 → ℕ) (P:Poly4 K):ℕ:=
 MvPolynomial.weightedTotalDegree weights P
theorem wt_mul_le (weights:Fin 4 → ℕ) (P Q:Poly4 K):
   wt weights (P*Q) ≤ wt weights P+wt weights Q:=
 weighted_mul_le weights P Q
theorem wt_add_le (weights:Fin 4 → ℕ) (P Q:Poly4 K):
   wt weights (P+Q) ≤ max (wt weights P) (wt weights Q):=
 weighted_add_le weights P Q
theorem wt_sub_le (weights:Fin 4 → ℕ) (P Q:Poly4 K):
   wt weights (P-Q) ≤ max (wt weights P) (wt weights Q):=by
 unfold wt
 rw [←degree_weightedLift,map_sub]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_sub_le (4:Fin 5)
     (weightedLift K weights P) (weightedLift K weights Q)
theorem wt_neg (weights:Fin 4 → ℕ) (P:Poly4 K):
   wt weights (-P)=wt weights P:=by
 unfold wt
 rw [←degree_weightedLift,map_neg,MvPolynomial.degreeOf_neg,
   degree_weightedLift]
theorem wt_pow_le (weights:Fin 4 → ℕ) (P:Poly4 K) (n:ℕ):
   wt weights (P^n) ≤ n*wt weights P:=by
 unfold wt
 rw [←degree_weightedLift,map_pow]
 simpa only [degree_weightedLift] using
   MvPolynomial.degreeOf_pow_le (4:Fin 5) (weightedLift K weights P) n
theorem wt_C (weights:Fin 4 → ℕ) (c:K):
   wt weights (MvPolynomial.C c:Poly4 K)=0:=by
 unfold wt MvPolynomial.weightedTotalDegree
 simp
theorem wt_X (weights:Fin 4 → ℕ) (i:Fin 4):
   wt weights (MvPolynomial.X i:Poly4 K)=weights i:=by
 unfold wt
 exact weighted_X weights i
theorem wt_natCast (weights:Fin 4 → ℕ) (n:ℕ):
   wt weights (n:Poly4 K)=0:=by
 rw [←map_natCast (MvPolynomial.C:K →+*Poly4 K),wt_C]
theorem wt_sum_le (weights:Fin 4 → ℕ) (I:Finset ℕ)
   (f:ℕ → Poly4 K) (a:ℕ) (hf:∀ i∈I,wt weights (f i) ≤ a):
   wt weights (∑ i∈I,f i) ≤ a:=by
 unfold wt
 rw [←degree_weightedLift,map_sum]
 apply (MvPolynomial.degreeOf_sum_le (4:Fin 5) I
   (fun i => weightedLift K weights (f i))).trans
 apply Finset.sup_le
 intro i hi
 rw [degree_weightedLift]
 exact hf i hi
theorem wt_pderiv_le (weights:Fin 4 → ℕ) (P:Poly4 K)
   (i:Fin 4) (A:ℕ) (hP:wt weights P ≤ A):
   wt weights (MvPolynomial.pderiv i P) ≤ A-weights i:=
 pderiv_weight_sub_bound weights P i A hP
theorem wt_polyH_le (weights:Fin 4 → ℕ) (F:Poly4 K)
   (C:ℕ) (hF:wt weights F ≤ C):
   wt weights (polyH K F) ≤ C-weights 2:=
 wt_pderiv_le weights F 2 C hF
theorem wt_polyG_le (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hF:wt weights F ≤ C):
   wt weights (polyG K F) ≤ C+weights 2:=by
 have hx:=wt_pderiv_le weights F 0 C hF
 have hy:=wt_pderiv_le weights F 1 C hF
 have hR:wt weights (MvPolynomial.X (2:Fin 4):Poly4 K)=weights 2:=
   weighted_X weights 2
 have hm:=wt_mul_le weights (MvPolynomial.X (2:Fin 4):Poly4 K)
   (MvPolynomial.pderiv 1 F)
 have hsum:=wt_add_le weights (MvPolynomial.pderiv 0 F)
   (MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv 1 F)
 unfold polyG
 rw [wt_neg]
 exact hsum.trans (max_le (by omega) (by omega))
theorem numeratorStep_wt_le_minkowski
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F M:Poly4 K) (b A C:ℕ) (hR:weights 2 ≤ C)
   (hRR:2*weights 2 ≤ C) (hA:weights 2 ≤ A)
   (hF:wt weights F ≤ C) (hM:wt weights M ≤ A):
   wt weights (numeratorStep K F b M) ≤
     A+C+(C-weights 2):=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly4 K:=MvPolynomial.X (2:Fin 4)
 let Hcap:=C-weights 2
 have hH:wt weights H ≤ Hcap:=wt_polyH_le weights F C hF
 have hG:wt weights G ≤ C+weights 2:=wt_polyG_le weights hX F C hF
 have hRwt:wt weights R=weights 2:=weighted_X weights 2
 have hHC:Hcap ≤ C:=Nat.sub_le C (weights 2)
 have hRH:weights 2+Hcap=C:=by
   dsimp [Hcap]
   omega
 have hRH2:weights 2 ≤ Hcap:=by
   dsimp [Hcap]
   omega
 have hMX:wt weights (MvPolynomial.pderiv 0 M) ≤ A:=by
   have h:=wt_pderiv_le weights M 0 A hM
   rw [hX,Nat.sub_zero] at h
   exact h
 have hMY:wt weights (MvPolynomial.pderiv 1 M) ≤ A:=
   (wt_pderiv_le weights M 1 A hM).trans (Nat.sub_le A (weights 1))
 have hMR:wt weights (MvPolynomial.pderiv 2 M) ≤ A-weights 2:=
   wt_pderiv_le weights M 2 A hM
 have hHX:wt weights (MvPolynomial.pderiv 0 H) ≤ Hcap:=by
   have h:=wt_pderiv_le weights H 0 Hcap hH
   rw [hX,Nat.sub_zero] at h
   exact h
 have hHY:wt weights (MvPolynomial.pderiv 1 H) ≤ Hcap:=
   (wt_pderiv_le weights H 1 Hcap hH).trans
     (Nat.sub_le Hcap (weights 1))
 have hHR:wt weights (MvPolynomial.pderiv 2 H) ≤ Hcap-weights 2:=
   wt_pderiv_le weights H 2 Hcap hH
 have hH2:wt weights (H^2) ≤ 2*Hcap:=
   (wt_pow_le weights H 2).trans (Nat.mul_le_mul_left 2 hH)
 have htermX:wt weights (H^2*MvPolynomial.pderiv 0 M) ≤
     A+C+Hcap:=by
   have h:=wt_mul_le weights (H^2) (MvPolynomial.pderiv 0 M)
   omega
 have htermY:wt weights (R*H^2*MvPolynomial.pderiv 1 M) ≤
     A+C+Hcap:=by
   have h1:=wt_mul_le weights R (H^2)
   have h2:=wt_mul_le weights (R*H^2) (MvPolynomial.pderiv 1 M)
   omega
 have htermR:wt weights (G*H*MvPolynomial.pderiv 2 M) ≤
     A+C+Hcap:=by
   have h1:=wt_mul_le weights G H
   have h2:=wt_mul_le weights (G*H) (MvPolynomial.pderiv 2 M)
   omega
 have hinnerX:wt weights (H*MvPolynomial.pderiv 0 H) ≤ C+Hcap:=by
   have h:=wt_mul_le weights H (MvPolynomial.pderiv 0 H)
   omega
 have hinnerY:wt weights (R*H*MvPolynomial.pderiv 1 H) ≤ C+Hcap:=by
   have h1:=wt_mul_le weights R H
   have h2:=wt_mul_le weights (R*H) (MvPolynomial.pderiv 1 H)
   omega
 have hinnerR:wt weights (G*MvPolynomial.pderiv 2 H) ≤ C+Hcap:=by
   have h:=wt_mul_le weights G (MvPolynomial.pderiv 2 H)
   omega
 have hinner:wt weights
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H) ≤ C+Hcap:=by
   exact (wt_add_le weights _ _).trans
     (max_le ((wt_add_le weights _ _).trans (max_le hinnerX hinnerY)) hinnerR)
 have hn:wt weights (((2*b:ℕ):Poly4 K))=0:=wt_natCast weights (2*b)
 have hnM:wt weights (((2*b:ℕ):Poly4 K)*M) ≤ A:=by
   have h:=wt_mul_le weights (((2*b:ℕ):Poly4 K)) M
   omega
 have hlast:wt weights (((2*b:ℕ):Poly4 K)*M*
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H)) ≤ A+C+Hcap:=by
   have h:=wt_mul_le weights (((2*b:ℕ):Poly4 K)*M)
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H)
   omega
 change wt weights
     (H^2*MvPolynomial.pderiv 0 M+
       R*H^2*MvPolynomial.pderiv 1 M+
       G*H*MvPolynomial.pderiv 2 M-
       ((2*b:ℕ):Poly4 K)*M*
         (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
           G*MvPolynomial.pderiv 2 H)) ≤ A+C+Hcap
 exact (wt_sub_le weights _ _).trans
   (max_le ((wt_add_le weights _ _).trans
     (max_le ((wt_add_le weights _ _).trans (max_le htermX htermY)) htermR)) hlast)
theorem numerator_wt_le_minkowski
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hR:weights 2 ≤ C)
   (hRR:2*weights 2 ≤ C) (hbase:weights 2 ≤ weights 1)
   (hF:wt weights F ≤ C) (b:ℕ):
   wt weights (numerator K F b) ≤
     weights 1+b*(C+(C-weights 2)):=by
 induction b with
 | zero =>
     rw [numerator_zero]
     unfold wt
     rw [weighted_X]
     simp
 | succ b ih =>
     rw [numerator_succ]
     have h:=numeratorStep_wt_le_minkowski weights hX F (numerator K F b) b
       (weights 1+b*(C+(C-weights 2))) C hR hRR
       (hbase.trans (Nat.le_add_right _ _)) hF ih
     convert h using 1 <;> ring
theorem shiftedX_wt_eq_zero (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (x:K):
   wt weights (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)=0:=by
 apply Nat.eq_zero_of_le_zero
 apply (wt_sub_le weights _ _).trans
 rw [wt_C,wt_X,hX]
 simp
theorem affineSeedPolynomial_wt_le (weights:Fin 4 → ℕ) (u₀ u₁:K):
   wt weights (affineSeedPolynomial u₀ u₁) ≤ weights 3:=by
 unfold affineSeedPolynomial
 apply (wt_add_le weights _ _).trans
 apply max_le
 · rw [wt_C]
   exact Nat.zero_le _
 · have hm:=wt_mul_le weights (MvPolynomial.X (3:Fin 4):Poly4 K)
     (MvPolynomial.C u₁)
   rw [wt_X,wt_C,Nat.add_zero] at hm
   exact hm
theorem commonNumeratorTerm_wt_le_minkowski
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hR:weights 2 ≤ C)
   (hRR:2*weights 2 ≤ C) (hbase:weights 2 ≤ weights 1)
   (hF:wt weights F ≤ C) (w j:ℕ) (hj:j ≤ w)
   (coeffs:ℕ → K) (x:K):
   wt weights (commonNumeratorTerm F w coeffs x j) ≤
     weights 1+w*(C+(C-weights 2)):=by
 let Hcap:=C-weights 2
 let Qcap:=C+Hcap
 have hHC:Hcap ≤ C:=Nat.sub_le _ _
 have hM:wt weights (numerator K F j) ≤ weights 1+j*Qcap:=by
   simpa only [Hcap,Qcap] using
     numerator_wt_le_minkowski weights hX F C hR hRR hbase hF j
 have hCM:wt weights (MvPolynomial.C (coeffs j)*numerator K F j) ≤
     weights 1+j*Qcap:=by
   have hm:=wt_mul_le weights (MvPolynomial.C (coeffs j)) (numerator K F j)
   rw [wt_C,Nat.zero_add] at hm
   exact hm.trans hM
 have hH:wt weights (polyH K F) ≤ Hcap:=wt_polyH_le weights F C hF
 have hHP:wt weights (polyH K F^(2*(w-j))) ≤
     2*(w-j)*Hcap:=by
   exact (wt_pow_le weights (polyH K F) (2*(w-j))).trans
     (Nat.mul_le_mul_left _ hH)
 have hSX:=shiftedX_wt_eq_zero weights hX x
 have h1:=wt_mul_le weights
   (MvPolynomial.C (coeffs j)*numerator K F j)
   (polyH K F^(2*(w-j)))
 have h2:=wt_mul_le weights
   (MvPolynomial.C (coeffs j)*numerator K F j*
     polyH K F^(2*(w-j)))
   ((MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^j)
 have hSXP:wt weights
     ((MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)^j) ≤ 0:=by
   have hp:=wt_pow_le weights
     (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K) j
   rw [hSX,Nat.mul_zero] at hp
   exact hp
 have hraw:wt weights (commonNumeratorTerm F w coeffs x j) ≤
     (weights 1+j*Qcap)+2*(w-j)*Hcap:=by
   simpa only [commonNumeratorTerm,Nat.add_zero] using
     h2.trans (Nat.add_le_add (h1.trans (Nat.add_le_add hCM hHP)) hSXP)
 have hunit:2*Hcap ≤ Qcap:=by
   dsimp [Qcap]
   omega
 have hmul:=Nat.mul_le_mul_left (w-j) hunit
 have hwj:j+(w-j)=w:=by omega
 apply hraw.trans
 calc
   (weights 1+j*Qcap)+2*(w-j)*Hcap=
       weights 1+j*Qcap+(w-j)*(2*Hcap):=by ring
   _ ≤ weights 1+j*Qcap+(w-j)*Qcap:=
     Nat.add_le_add_left hmul _
   _=weights 1+(j+(w-j))*Qcap:=by ring
   _=weights 1+w*Qcap:=by rw [hwj]
theorem clearedTaylorNumerator_wt_le_minkowski
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hR:weights 2 ≤ C)
   (hRR:2*weights 2 ≤ C) (hbase:weights 2 ≤ weights 1)
   (hF:wt weights F ≤ C) (w:ℕ) (coeffs:ℕ → K) (x:K):
   wt weights (clearedTaylorNumerator F w coeffs x) ≤
     weights 1+w*(C+(C-weights 2)):=by
 unfold clearedTaylorNumerator
 apply wt_sum_le
 intro j hj
 apply commonNumeratorTerm_wt_le_minkowski weights hX F C hR hRR hbase hF
 have:=Finset.mem_range.mp hj
 omega
theorem agreementNumerator_wt_le_minkowski
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hR:weights 2 ≤ C)
   (hRR:2*weights 2 ≤ C) (hbase:weights 2 ≤ weights 1)
   (hF:wt weights F ≤ C) (w:ℕ) (coeffs:ℕ → K)
   (x u₀ u₁:K):
   wt weights (agreementNumerator F w coeffs x u₀ u₁) ≤
     max (weights 1) (weights 3)+w*(C+(C-weights 2)):=by
 let Hcap:=C-weights 2
 let Qcap:=C+Hcap
 have hHC:Hcap ≤ C:=Nat.sub_le _ _
 have hTaylor:=clearedTaylorNumerator_wt_le_minkowski weights hX F C hR hRR
   hbase hF w coeffs x
 have hA:=affineSeedPolynomial_wt_le weights u₀ u₁
 have hH:wt weights (polyH K F) ≤ Hcap:=wt_polyH_le weights F C hF
 have hHP:wt weights (polyH K F^(2*w)) ≤ 2*w*Hcap:=
   (wt_pow_le weights (polyH K F) (2*w)).trans
     (Nat.mul_le_mul_left _ hH)
 have hprod:=wt_mul_le weights (affineSeedPolynomial u₀ u₁)
   (polyH K F^(2*w))
 have hunit:2*Hcap ≤ Qcap:=by
   dsimp [Qcap]
   omega
 have hmul:=Nat.mul_le_mul_left w hunit
 have hright:wt weights
     (affineSeedPolynomial u₀ u₁*polyH K F^(2*w)) ≤
     max (weights 1) (weights 3)+w*Qcap:=by
   apply hprod.trans
   calc
     wt weights (affineSeedPolynomial u₀ u₁)+
         wt weights (polyH K F^(2*w)) ≤ weights 3+2*w*Hcap:=
       Nat.add_le_add hA hHP
     _=weights 3+w*(2*Hcap):=by ring
     _ ≤ max (weights 1) (weights 3)+w*Qcap:=
       Nat.add_le_add (Nat.le_max_right _ _) hmul
 unfold agreementNumerator
 apply (wt_sub_le weights _ _).trans
 apply max_le
 · simpa only [Hcap,Qcap] using
     hTaylor.trans (Nat.add_le_add_right (Nat.le_max_left _ _) _)
 · simpa only [Hcap,Qcap] using hright
end
end ProximityPrize.SubmissionLower.RCN234
end PackedLegacy_AA

/-! Packed from ProximityPrize.SubmissionLower.FO. -/
section PackedLegacy_FO
namespace ProximityPrize.SubmissionLower.RCN235
open scoped BigOperators Matrix
open ProximityPrize.SubmissionLower.RCN234
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
def shearImage (i:Fin 4):Poly4 K:=
 ![MvPolynomial.X 0,MvPolynomial.X 1,
   MvPolynomial.X 2-MvPolynomial.X 3,MvPolynomial.X 3] i
def shearMap:Poly4 K →+*Poly4 K:=
 MvPolynomial.eval₂Hom MvPolynomial.C shearImage
def pullShearWeights (weights:Fin 4 → ℕ):Fin 4 → ℕ:=
 ![weights 0,weights 1,max (weights 2) (weights 3),weights 3]
theorem shearImage_wt_le (weights:Fin 4 → ℕ) (i:Fin 4):
   wt weights (shearImage (K:=K) i) ≤ pullShearWeights weights i:=by
 fin_cases i
 · simp [shearImage,pullShearWeights,wt_X]
 · simp [shearImage,pullShearWeights,wt_X]
 · dsimp [shearImage,pullShearWeights]
   exact (wt_sub_le weights _ _).trans (by rw [wt_X,wt_X])
 · simp [shearImage,pullShearWeights,wt_X]
theorem wt_finset_prod_le_sum {ι:Type*} [DecidableEq ι]
   (weights:Fin 4 → ℕ) (I:Finset ι) (f:ι → Poly4 K):
   wt weights (∏ i∈I,f i) ≤ ∑ i∈I,wt weights (f i):=by
 induction I using Finset.induction_on with
 | empty =>
     simp only [Finset.prod_empty,Finset.sum_empty]
     unfold wt MvPolynomial.weightedTotalDegree
     simp
 | @insert i I hi ih =>
     simp only [Finset.prod_insert hi,Finset.sum_insert hi]
     exact (wt_mul_le weights _ _).trans (Nat.add_le_add le_rfl ih)
theorem wt_finset_sum_le {ι:Type*} [DecidableEq ι]
   (weights:Fin 4 → ℕ) (I:Finset ι) (f:ι → Poly4 K) (cap:ℕ)
   (hf:∀ i∈I,wt weights (f i) ≤ cap):
   wt weights (∑ i∈I,f i) ≤ cap:=by
 unfold wt
 rw [←RCN081.degree_weightedLift,map_sum]
 apply (MvPolynomial.degreeOf_sum_le (4:Fin 5) I
   (fun i => RCN081.weightedLift K weights (f i))).trans
 apply Finset.sup_le
 intro i hi
 rw [RCN081.degree_weightedLift]
 exact hf i hi
theorem shear_monomial_product_wt_le
   (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ):
   wt weights (∏ i∈d.support,shearImage (K:=K) i^d i) ≤
     Finsupp.weight (pullShearWeights weights) d:=by
 apply (wt_finset_prod_le_sum weights d.support
   (fun i => shearImage (K:=K) i^d i)).trans
 calc
   (∑ i∈d.support,wt weights (shearImage (K:=K) i^d i)) ≤
       ∑ i∈d.support,d i*pullShearWeights weights i:=by
     apply Finset.sum_le_sum
     intro i hi
     exact (wt_pow_le weights (shearImage (K:=K) i) (d i)).trans
       (Nat.mul_le_mul_left _ (shearImage_wt_le weights i))
   _=Finsupp.weight (pullShearWeights weights) d:=by
     rw [Finsupp.weight_apply]
     simp only [Finsupp.sum,nsmul_eq_mul]
     simp
end
end ProximityPrize.SubmissionLower.RCN235
end PackedLegacy_FO

/-! Packed from ProximityPrize.SubmissionLower.AH. -/
section PackedLegacy_AH
namespace ProximityPrize.SubmissionLower.RCN295
open scoped Classical BigOperators WithZero
open RCN187
noncomputable section
variable {K L σ:Type*} [Field K] [Field L] [Fintype σ]
local instance:DecidableEq K:=Classical.decEq K
def exponentPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):ℤ:=
 ∑ i,(d i:ℤ)*poleOrder v (x i)
def exponentValuationWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):ℤ:=
 ∑ i,(d i:ℤ)*(v (x i)).log
def exponentSetValuationWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ)):ℤ:=
 (insert (0:ℤ) (E.image (exponentValuationWeight v x))).max'
   ⟨0,Finset.mem_insert_self (0:ℤ) _⟩
def ExponentSetDownwardClosed (E:Finset (σ →₀ ℕ)):Prop:=
 ∀ d∈E,∀ e:σ →₀ ℕ,e ≤ d → e∈E
def exponentSetPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ)):ℤ:=
 (insert (0:ℤ) (E.image (exponentPoleWeight v x))).max'
   ⟨0,Finset.mem_insert_self (0:ℤ) _⟩
def supportPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K):ℤ:=
 exponentSetPoleWeight v x F.support
theorem supportPoleWeight_nonneg
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K):
   0 ≤ supportPoleWeight v x F:=by
 unfold supportPoleWeight exponentSetPoleWeight
 exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
theorem exponentPoleWeight_le_supportPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K)
   (d:σ →₀ ℕ) (hd:d∈F.support):
   exponentPoleWeight v x d ≤ supportPoleWeight v x F:=by
 unfold supportPoleWeight exponentSetPoleWeight
 apply Finset.le_max'
 exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hd,rfl⟩)
theorem exponentSetPoleWeight_mono
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) {E D:Finset (σ →₀ ℕ)} (hED:E ⊆ D):
   exponentSetPoleWeight v x E ≤ exponentSetPoleWeight v x D:=by
 unfold exponentSetPoleWeight
 apply Finset.max'_le
 intro z hz
 obtain rfl | hz:=Finset.mem_insert.mp hz
 · exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
 · obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp hz
   apply Finset.le_max'
   exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hED hd,rfl⟩)
theorem supportPoleWeight_le_exponentSetPoleWeight
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (F:MvPolynomial σ K) (E:Finset (σ →₀ ℕ))
   (hFE:F.support ⊆ E):
   supportPoleWeight v x F ≤ exponentSetPoleWeight v x E:=
 exponentSetPoleWeight_mono v x hFE
def poleTruncation
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):σ →₀ ℕ:=by
 classical
 exact d.filter (fun i↦0 ≤ (v (x i)).log)
def naturalPoleWeights
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:σ → L):σ → ℕ:=
 fun i↦(poleOrder v (x i)).toNat
theorem valuation_monomial_le_exp_support
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ c:K,v (coeff c) ≤ 1)
   (x:σ → L) (F:MvPolynomial σ K)
   (d:σ →₀ ℕ) (hd:d∈F.support) (c:K):
   v (MvPolynomial.eval₂Hom coeff x (MvPolynomial.monomial d c)) ≤
     WithZero.exp (supportPoleWeight v x F):=by
 classical
 apply WithZero.le_exp_of_log_le
 calc
   (v (MvPolynomial.eval₂Hom coeff x
       (MvPolynomial.monomial d c))).log ≤
       poleOrder v (MvPolynomial.eval₂Hom coeff x
         (MvPolynomial.monomial d c)):=
     le_max_right _ _
   _ ≤ exponentPoleWeight v x d:=by
     by_cases hc:c=0
     · subst c
       simp [exponentPoleWeight,poleOrder]
       positivity
     · have hmono:=poleOrder_eval_le_box v coeff hcoeff x
         (fun i↦d i) (MvPolynomial.monomial d c) (fun i↦by
           rw [MvPolynomial.degreeOf_monomial_eq d i hc])
       simpa only [exponentPoleWeight] using hmono
   _ ≤ supportPoleWeight v x F:=
     exponentPoleWeight_le_supportPoleWeight v x F d hd
end
end ProximityPrize.SubmissionLower.RCN295
end PackedLegacy_AH
end Compact_PackedLegacyCore1
