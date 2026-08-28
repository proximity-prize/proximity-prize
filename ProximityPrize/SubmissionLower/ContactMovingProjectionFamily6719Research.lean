import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactCommonProjectionChoice6676Research
import ProximityPrize.SubmissionLower.ContactMovingFiberCount6676Research

/-! .

 -/
namespace ProximityPrize.SubmissionLower.ContactMovingProjectionFamily6719Research
open scoped Classical BigOperators WithZero
open ActualCurveCoordinateField ContactRegularComponentCover CoordinateBoxZeroCount
open ContactWeakSeparableSeparatorResearch ArbitraryRationalProjectionResearch
open ContactMovingProjection6676Research ContactMovingProjectionDegree6676Research
open ContactCommonProjectionChoice6676Research ContactMovingFiberCount6676Research
open ContactFlagBezout6543Research ContactLocalPoleBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000

variable {K : Type} [Field K] [IsAlgClosed K]
local notation "Poly" => MvPolynomial (Fin 3) K

/-- .
 -/
theorem exists_separable_moving_coordinates (F A H G : Poly)
    (base : ∀ C : RegularComponent K F A H,SeparableLiteralCoordinate C.1) :
    ∃ (Q U : Poly) (J : ∀ C : RegularComponent K F A H,SeparableCoordinate K (CoordinateField K C.1)),
      PolynomialInFlag (2 • unitAllFlag) Q ∧ PolynomialInFlag unitYZFlag U ∧
      ∀ C : RegularComponent K F A H,
        U ∉ C.1 ∧ SeparableCoordinate.value K (CoordinateField K C.1) (J C)=movingValue C.1 H G Q U ∧
        (∀ v : Place K (CoordinateField K C.1),
          poleOrder v.val (SeparableCoordinate.value K (CoordinateField K C.1) (J C))=
            movingPoleTarget C.1 H G v) ∧
        (∀ v ∈ movingRelevantPlaces (base C) (movingRatio C.1 H G),
          v.val (coordinateEvaluation K C.1 U)=WithZero.exp
            (max (poleOrder v.val (coordinate K C.1 0)) (poleOrder v.val (coordinate K C.1 2)))) := by
  obtain ⟨Q,U,hQ,hU,h⟩ := exists_common_original_projection F A H G base
  have gate (C : RegularComponent K F A H) := moving_projection_gate (base C) H G Q U (h C).2.1
  let J : ∀ C : RegularComponent K F A H,SeparableCoordinate K (CoordinateField K C.1) :=
    fun C ↦ {
      embedding := elementEmbedding K (CoordinateField K C.1) (movingValue C.1 H G Q U) (gate C).choose
      finite := (gate C).choose_spec.1
      separable := (gate C).choose_spec.2.1 }
  have hv (C : RegularComponent K F A H) :
      SeparableCoordinate.value K (CoordinateField K C.1) (J C)=movingValue C.1 H G Q U :=
    elementEmbedding_variable K (CoordinateField K C.1) _ (gate C).choose
  refine ⟨Q,U,J,hQ,hU,fun C ↦ ⟨(h C).1,hv C,?_,(h C).2.2.2⟩⟩
  intro v
  rw [hv C]
  exact (h C).2.2.1 v

variable {E : Type} [Field E] [IsAlgClosed E]
variable [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]

/-- .

 -/
theorem exists_moving_projection_family (F H G : Poly) (k : ℕ) (B : Fin (k+1) → Poly)
    (base : ∀ C : RegularComponent K F (filteredCut k B H G) H,SeparableLiteralCoordinate C.1)
    (hF : F ≠ 0)
    (hderiv : H ∈ Ideal.span ({F,MvPolynomial.pderiv (1 : Fin 3) F} : Set Poly))
    (p : FlagDegree) (hFp : PolynomialInFlag p F) (a b s : ℕ) (C0 : FlagDegree)
    (hH : PolynomialInFlag (⟨a,b+1,s+1⟩ : FlagDegree) H)
    (hG : PolynomialInFlag (⟨a,b,s+3⟩ : FlagDegree) G)
    (c : Fin (k+1) → FlagDegree) (hB : ∀ j,PolynomialInFlag (c j) (B j))
    (hc : ∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩ : FlagDegree)+
      j.val • (⟨a,b,s+3⟩ : FlagDegree)=C0+k • (⟨2*a,2*b+1,2*s+3⟩ : FlagDegree))
    (pchar : ℕ) [CharP E pchar]
    (hmix : 2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3)) < pchar) :
    ∃ J : ∀ C : RegularComponent K F (filteredCut k B H G) H,
        SeparableCoordinate K (CoordinateField K C.1),
      (∀ (C : RegularComponent K F (filteredCut k B H G) H)
          (v : Place K (CoordinateField K C.1)),
        poleOrder v.val (SeparableCoordinate.value K (CoordinateField K C.1) (J C))=
          movingPoleTarget C.1 H G v) ∧
      (∑ C : RegularComponent K F (filteredCut k B H G) H,
        SeparableCoordinate.degree K (CoordinateField K C.1) (J C)) ≤
        flagMixed p (⟨a,b+1,s+3⟩ : FlagDegree) (C0+k • (⟨a,b+1,s+2⟩ : FlagDegree)) := by
  classical
  obtain ⟨Q,U,J,hQ,hU,hJ⟩ := exists_separable_moving_coordinates F (filteredCut k B H G) H G base
  letI : ∀ C : RegularComponent K F (filteredCut k B H G) H,
      Algebra (RatFunc K) (CoordinateField K C.1) := fun C ↦ (J C).embedding.toRingHom.toAlgebra
  letI : ∀ C : RegularComponent K F (filteredCut k B H G) H,
      IsScalarTower K (RatFunc K) (CoordinateField K C.1) := fun C ↦
        IsScalarTower.of_algebraMap_eq fun a ↦ ((J C).embedding.commutes a).symm
  letI : ∀ C : RegularComponent K F (filteredCut k B H G) H,
      FiniteDimensional (RatFunc K) (CoordinateField K C.1) := fun C ↦ (J C).finite
  letI : ∀ C : RegularComponent K F (filteredCut k B H G) H,
      Algebra.IsSeparable (RatFunc K) (CoordinateField K C.1) := fun C ↦ (J C).separable
  have hj (C : RegularComponent K F (filteredCut k B H G) H) :
      algebraMap (RatFunc K) (CoordinateField K C.1) (rationalVariable K)=movingValue C.1 H G Q U :=
    (hJ C).2.1
  have hdeg : p.zOnly+p.yz+p.all < pchar := by
    nlinarith
  obtain ⟨hN,hA⟩ := fiber_small_flags (E := E) a b s k C0 H G Q U B c hH hG hQ hU hB hc
  have hcount := sum_moving_degrees_le (E := E) F H G Q U k B hj (fun C ↦ (hJ C).1)
    hF hderiv p (⟨a,b+1,s+3⟩ : FlagDegree) (C0+k • (⟨a,b+1,s+2⟩ : FlagDegree))
    hFp hN hA pchar hdeg hmix
  refine ⟨J,fun C v ↦ (hJ C).2.2.1 v,?_⟩
  simpa only [SeparableCoordinate.degree] using hcount

end
end ProximityPrize.SubmissionLower.ContactMovingProjectionFamily6719Research
