import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.E4
namespace ProximityPrize.SubmissionLower.ContactFreshCoefficientFieldGenerationResearch
open ContactDifferentialRing ContactPolynomialSolutions ContactPolynomialRecovery
open ContactGlobalPolynomiality ContactTranslation
open ContactReconstructionFieldMembershipResearch
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 15000
set_option synthInstance.maxHeartbeats 200000
variable {k L:Type*} [Field k] [Field L] [Algebra k L]
local instance:DecidableEq k:=Classical.decEq k
local instance:DecidableEq L:=Classical.decEq L
def freshPoint (P:Polynomial L) (γ:L):Fin 4 → RatFunc L:=
 polynomialPoint (algebraMap L (RatFunc L)) P γ RatFunc.X
def jetField (P:Polynomial L) (γ:L):IntermediateField k (RatFunc L):=
 IntermediateField.adjoin k (Set.range (freshPoint P γ))
def coefficientField (P:Polynomial L) (γ:L):IntermediateField k (RatFunc L):=
 IntermediateField.adjoin k
   (insert RatFunc.X (insert (algebraMap L (RatFunc L) γ)
     (Set.range (fun j:ℕ => algebraMap L (RatFunc L) (P.coeff j)))))
@[simp] theorem freshPoint_X (P:Polynomial L) (γ:L):
   freshPoint P γ 0=RatFunc.X:=rfl
@[simp] theorem freshPoint_Z (P:Polynomial L) (γ:L):
   freshPoint P γ 3=algebraMap L (RatFunc L) γ:=rfl
theorem fresh_eval_eq (P:Polynomial L) (γ:L) (Q:Poly4 L):
   MvPolynomial.eval₂Hom (algebraMap L (RatFunc L)) (freshPoint P γ) Q=
     algebraMap (Polynomial L) (RatFunc L) (specialization L P γ Q):=by
 rw [freshPoint,eval_polynomialPoint_eq_specialization]
 exact RatFunc.aeval_X_left_eq_algebraMap _
theorem freshPoint_regular (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0):
   MvPolynomial.eval₂Hom (algebraMap L (RatFunc L)) (freshPoint P γ)
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0:=by
 rw [fresh_eval_eq]
 exact RatFunc.algebraMap_ne_zero hreg
theorem coefficient_mem_of_freshPoint_mem
   (E:IntermediateField k (RatFunc L))
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (hv:∀ i,freshPoint P γ i∈E)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w) (j:ℕ):
   algebraMap L (RatFunc L) (P.coeff j)∈E:=by
 apply solution_coeff_mem_of_regular_point E.toSubfield (algebraMap k L)
   (algebraMap L (RatFunc L)) _ F P γ RatFunc.X hsolution
   (freshPoint_regular F P γ hreg) hv p w hw hP j
 intro a
 change algebraMap k (RatFunc L) a∈E
 exact E.algebraMap_mem a
theorem coefficient_mem_jetField
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w) (j:ℕ):
   algebraMap L (RatFunc L) (P.coeff j)∈jetField (k:=k) P γ:=by
 apply coefficient_mem_of_freshPoint_mem (jetField (k:=k) P γ)
   F P γ hsolution hreg _ p w hw hP j
 intro i
 exact IntermediateField.subset_adjoin k _ ⟨i,rfl⟩
theorem jetField_le_coefficientField (P:Polynomial L) (γ:L):
   jetField (k:=k) P γ ≤ coefficientField (k:=k) P γ:=by
 let E:=coefficientField (k:=k) P γ
 have hX:(RatFunc.X:RatFunc L)∈E:=
   IntermediateField.subset_adjoin k _ (Or.inl rfl)
 have hγ:algebraMap L (RatFunc L) γ∈E:=
   IntermediateField.subset_adjoin k _ (Or.inr (Or.inl rfl))
 have hc:∀ j,algebraMap L (RatFunc L) (P.coeff j)∈E:=
   fun j => IntermediateField.subset_adjoin k _ (Or.inr (Or.inr ⟨j,rfl⟩))
 apply IntermediateField.adjoin_le_iff.mpr
 rintro x ⟨i,rfl⟩
 fin_cases i
 · exact hX
 · exact polynomial_eval_mem E.toSubfield (algebraMap L (RatFunc L)) P hc
     RatFunc.X hX
 · apply polynomial_eval_mem E.toSubfield (algebraMap L (RatFunc L))
     P.derivative _ RatFunc.X hX
   intro j
   rw [Polynomial.coeff_derivative,map_mul]
   exact E.mul_mem (hc _) (by simpa using E.natCast_mem (j+1))
 · exact hγ
theorem coefficientField_le_jetField
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w):
   coefficientField (k:=k) P γ ≤ jetField (k:=k) P γ:=by
 apply IntermediateField.adjoin_le_iff.mpr
 intro x hx
 rcases hx with rfl | hx
 · exact IntermediateField.subset_adjoin k _ ⟨0,rfl⟩
 rcases hx with rfl | hx
 · exact IntermediateField.subset_adjoin k _ ⟨3,rfl⟩
 obtain ⟨j,rfl⟩:=hx
 exact coefficient_mem_jetField F P γ hsolution hreg p w hw hP j
theorem fresh_jetField_eq_coefficientField
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w):
   jetField (k:=k) P γ=coefficientField (k:=k) P γ:=
 le_antisymm (jetField_le_coefficientField P γ)
   (coefficientField_le_jetField F P γ hsolution hreg p w hw hP)
end
end ProximityPrize.SubmissionLower.ContactFreshCoefficientFieldGenerationResearch
