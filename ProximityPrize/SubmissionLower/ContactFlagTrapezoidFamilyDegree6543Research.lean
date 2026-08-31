import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ArbitraryPlaneEvaluationFamilyResearch
import ProximityPrize.SubmissionLower.ActualPlaneJointProjection
namespace ProximityPrize.SubmissionLower.ContactFlagTrapezoidFamilyDegree6543Research
open scoped Classical BigOperators
open TrivariateRationalCollection ActualPlaneCoordinateKernel
  ActualPlaneCoordinateCaps ActualPlanePositiveOrder
  ActualPlaneCharacteristicFreeDegreeResearch
  CharacteristicFreeMatrixMultiplicityResearch
  CharacteristicFreeProjectionAdapter ArbitraryRationalProjectionResearch
  ArbitraryPlaneEvaluationFamilyResearch ActualPlaneJointProjection
noncomputable section
theorem sum_finrank_le_ordinary_resultant_without_separability
    {F:Type} [Field F] {I:Type*} [Fintype I]
    (E:I → Type) [∀ i,Field (E i)] [∀ i,Algebra F (E i)]
    [∀ i,FiniteDimensional F (E i)]
    (P Q:Polynomial (Polynomial F))
    (hP:Irreducible P) (hpositive:0 < P.natDegree)
    (hproper:¬ P∣Q)
    (y r:∀ i,E i)
    (hgen:∀ i,IntermediateField.adjoin F
      ({y i,r i}:Set (E i))=⊤)
    (hkernels:Function.Injective (fun i↦
      PlaneFunctionFieldDegree.relationIdeal F (E i) (y i) (r i)))
    (hProot:∀ i,PlaneFunctionFieldDegree.planeEval F (E i)
      (y i) (r i) P=0)
    (hQroot:∀ i,PlaneFunctionFieldDegree.planeEval F (E i)
      (y i) (r i) Q=0):
    (∑ i,Module.finrank F (E i)) ≤
      (Polynomial.resultant P Q).natDegree:=by
  classical
  letI:DecidableEq F:=Classical.decEq F
  have hspecial:∀ f∈
      (Finset.univ.image (fun i↦minpoly F (y i))),
        P.map (AdjoinRoot.mk f)≠0:=by
    intro f hf
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hf
    letI:Fact (Irreducible (minpoly F (y i))):=
      ⟨minpoly.irreducible (IsIntegral.of_finite F (y i))⟩
    have hcoeff:Polynomial.eval₂RingHom
        (algebraMap F (AdjoinRoot (minpoly F (y i))))
          (AdjoinRoot.root (minpoly F (y i)))=
        AdjoinRoot.mk (minpoly F (y i)):=by
      apply Polynomial.ringHom_ext
      · intro c
        simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
          AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
      · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,
          AdjoinRoot.mk_X]
    have h:=PlaneCoefficientExtension.bimap_specialization_ne_zero
      (algebraMap F (AdjoinRoot (minpoly F (y i)))) P
      (hP.isPrimitive (Nat.ne_of_gt hpositive))
      (AdjoinRoot.root (minpoly F (y i)))
    rw [PlaneCoefficientExtension.bimap_specialization,hcoeff] at h
    exact h
  have hresultant:Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=
    PlaneResultantIrreducible.irreducible_resultant_ne_zero_of_not_dvd
      P Q hP hpositive hproper
  simpa only using
    (sum_finrank_le_resultant_of_relationIdeal_injective
      (K:=F) E P Q P.natDegree Q.natDegree le_rfl le_rfl y r hgen
        hkernels hProot hQroot hspecial hresultant)
variable (K:Type) [Field K]
theorem finite_sum_finrank_bound_trapezoid
    (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
    (E:I → Type)
    [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
    (e:∀ i,Original K →ₐ[K] E i)
    (ht:∀ i,Transcendental K (e i (MvPolynomial.X (order 0))))
    (hgen:∀ i,
      letI:Algebra (RatFunc K) (E i):=
        (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
          (ht i)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc K)
        ({e i (MvPolynomial.X (order 2)),e i (MvPolynomial.X (order 1))}:
          Set (E i))=⊤)
    (hkernels:Function.Injective (fun i↦RingHom.ker (e i).toRingHom))
    (G H:Original K) (hG:Irreducible G)
    (hGroot:∀ i,e i G=0) (hHroot:∀ i,e i H=0)
    (hproper:¬ G∣H) (hpositive:0 < (planeMap K order G).natDegree)
    (n mCap totalG totalH cap:ℕ) (hHne:H≠0)
    (hGouter:(planeMap K order G).natDegree ≤ n)
    (hHouter:(planeMap K order H).natDegree ≤ mCap)
    (hGsupport:∀ d∈(rationalMap K order G).support,
      d 0+d 1 ≤ totalG)
    (hHsupport:∀ d∈(rationalMap K order H).support,
      d 0+d 1 ≤ totalH)
    (hbudget:∀ m,m ≤ mCap →
      m*totalG+n*totalH-m*n ≤ cap):
    letI:∀ i,Algebra (RatFunc K) (E i):=fun i↦
      (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
        (ht i)).toRingHom.toAlgebra
    (∀ i,FiniteDimensional (RatFunc K) (E i))∧
      (∑ i,Module.finrank (RatFunc K) (E i)) ≤ cap:=by
  classical
  letI:∀ i,Algebra (RatFunc K) (E i):=fun i↦
    (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
      (ht i)).toRingHom.toAlgebra
  by_cases hI:Nonempty I
  · let i₀:I:=Classical.choice hI
    have hirr:Irreducible (planeMap K order G):=
      planeMap_irreducible_of_evaluation K (E i₀) order (e i₀)
        G hG (hGroot i₀) (ht i₀)
    have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
      intro hdiv
      exact hproper ((planeMap_dvd_iff_of_evaluation K (E i₀) order (e i₀)
        G H hG (hGroot i₀) (ht i₀)).mp hdiv)
    have hbase:=finite_sum_finrank_bound K order E e ht hgen hkernels
      G H hG hGroot hHroot hproper hpositive
    have hfinite:∀ i,FiniteDimensional (RatFunc K) (E i):=hbase.1
    letI:∀ i,FiniteDimensional (RatFunc K) (E i):=hfinite
    have hGroots:∀ i,
        PlaneFunctionFieldDegree.planeEval (RatFunc K) (E i)
          (e i (MvPolynomial.X (order 2)))
          (e i (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
      intro i
      change planeEvaluation K (E i) order (e i) (ht i)
        (planeMap K order G)=0
      rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
      exact hGroot i
    have hHroots:∀ i,
        PlaneFunctionFieldDegree.planeEval (RatFunc K) (E i)
          (e i (MvPolynomial.X (order 2)))
          (e i (MvPolynomial.X (order 1))) (planeMap K order H)=0:=by
      intro i
      change planeEvaluation K (E i) order (e i) (ht i)
        (planeMap K order H)=0
      rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
      exact hHroot i
    have hrelation:Function.Injective (fun i↦
        PlaneFunctionFieldDegree.relationIdeal (RatFunc K) (E i)
          (e i (MvPolynomial.X (order 2)))
          (e i (MvPolynomial.X (order 1)))):=by
      intro i j hij
      apply hkernels
      change relationKernel K (E i) order (e i) (ht i)=
        relationKernel K (E j) order (e j) (ht j) at hij
      have hc:=congrArg (Ideal.comap (planeMap K order)) hij
      simpa only [relationKernel_contract] using hc
    refine ⟨hfinite,?_⟩
    exact (sum_finrank_le_ordinary_resultant_without_separability E
      (planeMap K order G) (planeMap K order H) hirr hpositive hproperPlane
      (fun i↦e i (MvPolynomial.X (order 2)))
      (fun i↦e i (MvPolynomial.X (order 1))) hgen hrelation
      hGroots hHroots).trans
        (planeMap_trapezoid_resultant_natDegree_le K order G H
          n mCap totalG totalH cap hHne hGouter hHouter
          hGsupport hHsupport hbudget)
  · letI:IsEmpty I:=⟨fun i↦hI ⟨i⟩⟩
    exact ⟨fun i↦isEmptyElim i,by simp⟩
end
end ProximityPrize.SubmissionLower.ContactFlagTrapezoidFamilyDegree6543Research
