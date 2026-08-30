import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAdaptiveComponentSeparatorResearch
import ProximityPrize.SubmissionLower.ActualCurveJointProjectionBounds
namespace ProximityPrize.SubmissionLower.ContactWeakSeparableSeparatorResearch
open scoped Classical
open ActualCurveCoordinateField ActualCurveRationalProjection
  ActualCurveScalarTowers ActualCurveZeroCount
open CoordinateBoxZeroCount ContactRegularComponentCover
open ContactSparsePoleSupportResearch ContactSparsePoleZeroCountResearch
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
structure SeparableLiteralCoordinate
    (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime] where
  index:Fin 3
  transcendental:Transcendental Omega (coordinate Omega P index)
  finite:
    letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
      rationalBaseAlgebra Omega P index transcendental
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)
  separable:
    letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
      rationalBaseAlgebra Omega P index transcendental
    Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P)
theorem rationalBaseEmbedding_surjective_of_other_coordinates_algebraic
    (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (hS:Transcendental Omega (coordinate Omega P 1))
    (hY:IsAlgebraic Omega (coordinate Omega P 0))
    (hZ:IsAlgebraic Omega (coordinate Omega P 2)):
    Function.Surjective (rationalBaseEmbedding Omega P 1 hS):=by
  letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
    rationalBaseAlgebra Omega P 1 hS
  letI:IsScalarTower Omega (RatFunc Omega) (CoordinateField Omega P):=
    rationalBaseScalarTower Omega P 1 hS
  obtain ⟨y,hy⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P 0 hY
  obtain ⟨z,hz⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P 2 hZ
  have hYbot:coordinate Omega P 0∈
      (⊥:IntermediateField (RatFunc Omega) (CoordinateField Omega P)):=by
    rw [IntermediateField.mem_bot]
    refine ⟨algebraMap Omega (RatFunc Omega) y,?_⟩
    rw [←IsScalarTower.algebraMap_apply Omega (RatFunc Omega)
      (CoordinateField Omega P)]
    exact hy
  have hZbot:coordinate Omega P 2∈
      (⊥:IntermediateField (RatFunc Omega) (CoordinateField Omega P)):=by
    rw [IntermediateField.mem_bot]
    refine ⟨algebraMap Omega (RatFunc Omega) z,?_⟩
    rw [←IsScalarTower.algebraMap_apply Omega (RatFunc Omega)
      (CoordinateField Omega P)]
    exact hz
  have hadjoinBot:IntermediateField.adjoin (RatFunc Omega)
      ({coordinate Omega P 2,coordinate Omega P 0}:
        Set (CoordinateField Omega P))=⊥:=by
    rw [IntermediateField.adjoin_eq_bot_iff]
    intro x hx
    rcases hx with (rfl | hx)
    · exact hZbot
    · simpa using hx ▸ hYbot
  have hadjoinTop:IntermediateField.adjoin (RatFunc Omega)
      ({coordinate Omega P 2,coordinate Omega P 0}:
        Set (CoordinateField Omega P))=⊤:=
    adjoin_two_coordinates_over_ratFunc_eq_top Omega P 1 2 0 hS
      (by intro i;fin_cases i <;> simp)
  have htopbot:
      (⊤:IntermediateField (RatFunc Omega) (CoordinateField Omega P))=⊥:=
    hadjoinTop.symm.trans hadjoinBot
  intro x
  obtain ⟨a,ha⟩:=
    IntermediateField.mem_bot.mp (by rw [←htopbot];trivial:
      x∈(⊥:IntermediateField (RatFunc Omega) (CoordinateField Omega P)))
  refine ⟨a,?_⟩
  exact ha
theorem finite_separable_at_S_of_other_coordinates_algebraic
    (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (hS:Transcendental Omega (coordinate Omega P 1))
    (hY:IsAlgebraic Omega (coordinate Omega P 0))
    (hZ:IsAlgebraic Omega (coordinate Omega P 2)):
    letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
      rationalBaseAlgebra Omega P 1 hS
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)∧
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=by
  letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
    rationalBaseAlgebra Omega P 1 hS
  have hsurj:Function.Surjective
      (algebraMap (RatFunc Omega) (CoordinateField Omega P)):=by
    have hs:=
      rationalBaseEmbedding_surjective_of_other_coordinates_algebraic P hS hY hZ
    exact hs
  letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega P):=
    FiniteDimensional.of_surjective
      (Algebra.linearMap (RatFunc Omega) (CoordinateField Omega P)) hsurj
  have hsep:Algebra.IsSeparable
      (RatFunc Omega) (CoordinateField Omega P):=by
    constructor
    intro x
    obtain ⟨a,rfl⟩:=hsurj x
    exact isSeparable_algebraMap a
  exact ⟨inferInstance,hsep⟩
theorem finite_zero_points_le_exponentSet_of_literalCoordinate
    (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (D:SeparableLiteralCoordinate P)
    (E:Finset (Fin 3 →₀ ℕ)) (q:ℕ)
    (hpole:
      letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
        rationalBaseAlgebra Omega P D.index D.transcendental
      ∀ W:Finset (Place Omega (CoordinateField Omega P)),
        (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega P) E) ≤
          (q:ℤ))
    (F:MvPolynomial (Fin 3) Omega) (hFE:F.support ⊆ E) (hF:F∉P)
    (S:Finset (Fin 3 → Omega))
    (hSP:∀ v∈S,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hSF:∀ v∈S,MvPolynomial.aeval v F=0):
    S.card ≤ q:=by
  classical
  let i0:=D.index
  let htr:=D.transcendental
  letI:Algebra (Polynomial Omega) (CoordinateRing Omega P):=
    quotientPolynomialAlgebra Omega P i0
  letI:Algebra (Polynomial Omega) (CoordinateField Omega P):=
    polynomialBaseAlgebra Omega P i0
  letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
    rationalBaseAlgebra Omega P i0 htr
  letI:=quotientBaseScalarTower Omega P i0
  letI:=polynomialBaseScalarTower Omega P i0
  letI:=quotientFractionScalarTower Omega P i0
  letI:=polynomialRationalScalarTower Omega P i0 htr
  letI:=rationalBaseScalarTower Omega P i0 htr
  letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega P):=
    D.finite
  letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=
    D.separable
  let liftPoint:{v:Fin 3 → Omega//v∈S} →
      (CoordinateRing Omega P →ₐ[Omega] Omega):=
    fun v↦pointHom Omega P ⟨v.1,hSP v.1 v.2⟩
  have hinj:Function.Injective liftPoint:=by
    intro v w hvw
    have h:=pointHom_injective Omega P hvw
    apply Subtype.ext
    exact congrArg (fun z:PointOn Omega P↦z.val) h
  let points:=S.attach.image liftPoint
  have hpoints:∀ psi∈points,psi (MvPolynomial.eval₂Hom
      (algebraMap Omega (CoordinateRing Omega P))
      (quotientCoordinate Omega P) F)=0:=by
    intro psi hpsi
    obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hpsi
    rw [quotient_eval_eq_mk]
    exact hSF v.1 v.2
  have hpole':∀ W:Finset (Place Omega (CoordinateField Omega P)),
      (∑ v∈W,exponentSetPoleWeight v.val
        (fun i↦algebraMap (CoordinateRing Omega P) (CoordinateField Omega P)
          (quotientCoordinate Omega P i)) E) ≤ (q:ℤ):=by
    intro W
    simpa only [quotientCoordinate_fraction] using hpole W
  have hcount:=finite_model_zero_points_le_exponentSet
    (K:=Omega) (L:=CoordinateField Omega P) (σ:=Fin 3)
    (CoordinateRing Omega P) (quotientCoordinate Omega P) E F hFE
    (quotient_eval_ne_zero_of_not_mem Omega P F hF) q hpole' points hpoints
  have hcard:points.card=S.card:=by
    change (S.attach.image liftPoint).card=S.card
    rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
  rwa [hcard] at hcount
theorem exists_separableLiteralCoordinate_of_YZ_gates
    (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (hnonpoint:∀ v:Fin 3 → Omega,
      P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hY:∀ h:Transcendental Omega (coordinate Omega P 0),
      letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
        rationalBaseAlgebra Omega P 0 h
      FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)∧
        Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P))
    (hZ:∀ h:Transcendental Omega (coordinate Omega P 2),
      letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
        rationalBaseAlgebra Omega P 2 h
      FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)∧
        Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P)):
    Nonempty (SeparableLiteralCoordinate P):=by
  by_cases hy:Transcendental Omega (coordinate Omega P 0)
  · exact ⟨⟨0,hy,(hY hy).1,(hY hy).2⟩⟩
  by_cases hz:Transcendental Omega (coordinate Omega P 2)
  · exact ⟨⟨2,hz,(hZ hz).1,(hZ hz).2⟩⟩
  have hyalg:IsAlgebraic Omega (coordinate Omega P 0):=not_not.mp hy
  have hzalg:IsAlgebraic Omega (coordinate Omega P 2):=not_not.mp hz
  obtain ⟨i,hi⟩:=
    exists_transcendental_coordinate_of_ne_point_kernel Omega P hnonpoint
  have hi1:i=(1:Fin 3):=by
    fin_cases i <;> simp_all
  subst i
  have hs:=finite_separable_at_S_of_other_coordinates_algebraic
    P hi hyalg hzalg
  exact ⟨⟨1,hi,hs.1,hs.2⟩⟩
end
end ProximityPrize.SubmissionLower.ContactWeakSeparableSeparatorResearch
