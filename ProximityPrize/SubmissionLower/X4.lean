import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.AX
import ProximityPrize.SubmissionLower.W7
namespace ProximityPrize.SubmissionLower.ActualPlaneCoordinateDegree
open ActualCurveCoordinateField ActualCurveRationalProjection
 TrivariateRationalCollection ActualPlaneCoordinateKernel
noncomputable section
theorem order_cover (order:Fin 3 ≃ Fin 3) (l:Fin 3):
   l=order 0∨l=order 2∨l=order 1:=by
 have h:∀ i:Fin 3,i=0∨i=2∨i=1:=by decide
 rcases h (order.symm l) with hl | hl | hl
 · exact Or.inl (by simpa only [Equiv.apply_symm_apply] using congrArg order hl)
 · exact Or.inr (Or.inl (by simpa only [Equiv.apply_symm_apply] using congrArg order hl))
 · exact Or.inr (Or.inr (by simpa only [Equiv.apply_symm_apply] using congrArg order hl))
variable (K:Type) [Field K]
section Component
variable (order:Fin 3 ≃ Fin 3) (P:Ideal (Original K)) [P.IsPrime]
variable (ht:Transcendental K (coordinate K P (order 0)))
theorem actual_generators:
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   IntermediateField.adjoin (RatFunc K)
     ({coordinate K P (order 2),coordinate K P (order 1)}:Set (CoordinateField K P))=⊤:=
 adjoin_two_coordinates_over_ratFunc_eq_top K P (order 0) (order 2) (order 1) ht
   (order_cover order)
theorem planeEval_eq_actual:
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   PlaneFunctionFieldDegree.planeEval (RatFunc K) (CoordinateField K P)
     (coordinate K P (order 2)) (coordinate K P (order 1))=
       actualPlaneEvaluation K order P ht:=rfl
theorem relationIdeal_eq_actual:
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   PlaneFunctionFieldDegree.relationIdeal (RatFunc K) (CoordinateField K P)
     (coordinate K P (order 2)) (coordinate K P (order 1))=
       actualRelationKernel K order P ht:=rfl
theorem actual_finite_separable_finrank_bound
   (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:G∈P) (hHmem:H∈P) (hproper:¬ G∣H)
   (hpositive:0 < (planeMap K order G).natDegree)
   (hRdegree:(planeMap K order G).natDegree < p)
   (hresultantDegree:(Polynomial.resultant (planeMap K order G) (planeMap K order H)
     (planeMap K order G).natDegree (planeMap K order H).natDegree).natDegree < p):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
   FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
     Module.finrank (RatFunc K) (CoordinateField K P) ≤
       (planeMap K order H).natDegree*Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*Polynomial.Bivariate.degreeX (planeMap K order H):=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P (order 0) ht
 letI:CharP (RatFunc K) p:=
   charP_of_injective_algebraMap (algebraMap K (RatFunc K)).injective p
 have hirr:=planeMap_irreducible_of_component
   (K:=K) (order:=order) (P:=P) (ht:=ht) G hG hGmem
 have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
   intro h
   exact hproper ((planeMap_dvd_iff_of_component
     (K:=K) (order:=order) (P:=P) (ht:=ht) G H hG hGmem).mp h)
 have hGroots:PlaneFunctionFieldDegree.planeEval (RatFunc K) (CoordinateField K P)
     (coordinate K P (order 2)) (coordinate K P (order 1)) (planeMap K order G)=0:=by
   change actualPlaneEvaluation K order P ht (planeMap K order G)=0
   exact (actualPlane_root_iff K order P ht G).mpr hGmem
 have hHroots:PlaneFunctionFieldDegree.planeEval (RatFunc K) (CoordinateField K P)
     (coordinate K P (order 2)) (coordinate K P (order 1)) (planeMap K order H)=0:=by
   change actualPlaneEvaluation K order P ht (planeMap K order H)=0
   exact (actualPlane_root_iff K order P ht H).mpr hHmem
 exact PlaneSmallCharacteristicDegree.finite_separable_finrank_le_planar_bound
   (RatFunc K) (CoordinateField K P) p (planeMap K order G) (planeMap K order H)
   hirr hpositive hproperPlane hRdegree hresultantDegree
   (coordinate K P (order 2)) (coordinate K P (order 1))
   (actual_generators K order P ht) hGroots hHroots
end Component
section FiniteFamily
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
variable (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
theorem actual_finite_separable_sum_finrank_bound
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P) (p:ℕ) [CharP K p] (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i) (hHmem:∀ i,H∈P i)
   (hproper:¬ G∣H)
   (hpositive:0 < (planeMap K order G).natDegree)
   (hRdegree:(planeMap K order G).natDegree < p)
   (hresultantDegree:(Polynomial.resultant (planeMap K order G) (planeMap K order H)
     (planeMap K order G).natDegree (planeMap K order H).natDegree).natDegree < p):
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
     fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
   (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i))∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i)))∧
     (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
       (planeMap K order H).natDegree*Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*Polynomial.Bivariate.degreeX (planeMap K order H):=by
 classical
 letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
   fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   letI:CharP (RatFunc K) p:=
     charP_of_injective_algebraMap (algebraMap K (RatFunc K)).injective p
   have hirr:=planeMap_irreducible_of_component
     (K:=K) (order:=order) (P:=P i₀) (ht:=ht i₀) G hG (hGmem i₀)
   have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
     intro h
     exact hproper ((planeMap_dvd_iff_of_component
       (K:=K) (order:=order) (P:=P i₀) (ht:=ht i₀) G H hG (hGmem i₀)).mp h)
   have hkernels:Function.Injective (fun i =>
       PlaneFunctionFieldDegree.relationIdeal (RatFunc K) (CoordinateField K (P i))
         (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))):=by
     change Function.Injective (fun i => actualRelationKernel K order (P i) (ht i))
     exact actualRelationKernel_family_injective K order P ht hinj
   have hGroots:∀ i,
       PlaneFunctionFieldDegree.planeEval (RatFunc K) (CoordinateField K (P i))
         (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))
           (planeMap K order G)=0:=by
     intro i
     change actualPlaneEvaluation K order (P i) (ht i) (planeMap K order G)=0
     exact (actualPlane_root_iff K order (P i) (ht i) G).mpr (hGmem i)
   have hHroots:∀ i,
       PlaneFunctionFieldDegree.planeEval (RatFunc K) (CoordinateField K (P i))
         (coordinate K (P i) (order 2)) (coordinate K (P i) (order 1))
           (planeMap K order H)=0:=by
     intro i
     change actualPlaneEvaluation K order (P i) (ht i) (planeMap K order H)=0
     exact (actualPlane_root_iff K order (P i) (ht i) H).mpr (hHmem i)
   exact PlaneSmallCharacteristicDegree.finite_separable_sum_finrank_le_planar_bound
     (RatFunc K) (fun i => CoordinateField K (P i)) p
     (planeMap K order G) (planeMap K order H) hirr hpositive hproperPlane
     hRdegree hresultantDegree
     (fun i => coordinate K (P i) (order 2)) (fun i => coordinate K (P i) (order 1))
     (fun i => actual_generators K order (P i) (ht i)) hkernels hGroots hHroots
 · letI:IsEmpty I:=⟨fun i => hI ⟨i⟩⟩
   constructor
   · intro i
     exact isEmptyElim i
   · simp
end FiniteFamily
end
end ProximityPrize.SubmissionLower.ActualPlaneCoordinateDegree
