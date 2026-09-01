import ProximityPrize.SubmissionLower.DT
import ProximityPrize.SubmissionLower.X3
import ProximityPrize.SubmissionLower.X1
import ProximityPrize.SubmissionLower.EO

namespace ProximityPrize.SubmissionLower.CommonShearFiberPrototype

open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN007 RCN022 RCN023 RCN045 RCN067 RCN142 RCN231
  RCN238 RCN319 RCN344 RCN370 RCN372

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
variable (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]

theorem eval₂Hom_shear_at_add
    {A : Type} [CommRing A] [Algebra Ω A]
    (F : MvPolynomial (Fin 3) Ω) (y r z : A) (a : Ω) :
    MvPolynomial.eval₂Hom (algebraMap Ω A)
        ![y, r + algebraMap Ω A a * z, z] (shearAlgHom a F) =
      MvPolynomial.eval₂Hom (algebraMap Ω A) ![y, r, z] F := by
  have hhom :
      (MvPolynomial.eval₂Hom (algebraMap Ω A)
          ![y, r + algebraMap Ω A a * z, z]).comp
          (shearAlgHom a).toRingHom =
        MvPolynomial.eval₂Hom (algebraMap Ω A) ![y, r, z] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [RingHom.comp_apply, shearAlgHom]
    · intro i
      fin_cases i <;>
        simp [RingHom.comp_apply, shearAlgHom, shearImage] <;> ring
  exact RingHom.congr_fun hhom F

def shearedRingCoordinatesAt (a : Ω) : Fin 3 → CoordinateRing Ω P :=
  ![quotientCoordinate Ω P 0,
    quotientCoordinate Ω P 1 +
      algebraMap Ω (CoordinateRing Ω P) a * quotientCoordinate Ω P 2,
    quotientCoordinate Ω P 2]

theorem shearedPolynomialTransportAt_of_degree
    (a : Ω) (A : MvPolynomial (Fin 3) Ω) (cap : Fin 3 → ℕ)
    (hcap : ∀ i, A.degreeOf i ≤ cap i) :
    ∃ B : MvPolynomial (Fin 3) Ω,
      (∀ i, B.degreeOf i ≤ shearedPolynomialCap cap i) ∧
        MvPolynomial.eval₂Hom (algebraMap Ω (CoordinateRing Ω P))
          (shearedRingCoordinatesAt P a) B = Ideal.Quotient.mk P A := by
  refine ⟨shearAlgHom a A, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact (shear_degreeOf_zero_le a A).trans (hcap 0)
    · exact (shear_degreeOf_one_le a A).trans (hcap 1)
    · exact (shear_degreeOf_two_le a A).trans
        (Nat.add_le_add (hcap 2) (hcap 1))
  · rw [← quotient_eval_eq_mk]
    have h := eval₂Hom_shear_at_add
        (A := CoordinateRing Ω P) A
        (quotientCoordinate Ω P 0) (quotientCoordinate Ω P 1)
        (quotientCoordinate Ω P 2) a
    change MvPolynomial.eval₂Hom (algebraMap Ω (CoordinateRing Ω P))
      (shearedRingCoordinatesAt P a) (shearAlgHom a A) = _
    rw [show shearedRingCoordinatesAt P a =
        ![quotientCoordinate Ω P 0,
          quotientCoordinate Ω P 1 +
            algebraMap Ω (CoordinateRing Ω P) a * quotientCoordinate Ω P 2,
          quotientCoordinate Ω P 2] by rfl]
    rw [h]
    congr 2
    funext i
    fin_cases i <;> rfl

def shearCoordinateDataAt (a : Ω)
    (hS : Transcendental Ω
      (coordinate Ω P 1 + a • coordinate Ω P 2))
    (hfiniteS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra;
      FiniteDimensional (RatFunc Ω) (CoordinateField Ω P))
    (hsepS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)) :
    Coordinate Ω (CoordinateField Ω P) :=
  Sum.inr {
    embedding := elementEmbedding Ω (CoordinateField Ω P)
      (coordinate Ω P 1 + a • coordinate Ω P 2) hS
    finite := hfiniteS
    separable := hsepS }

theorem shearCoordinateDataAt_value (a : Ω)
    (hS : Transcendental Ω
      (coordinate Ω P 1 + a • coordinate Ω P 2))
    (hfiniteS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Ω) (CoordinateField Ω P))
    (hsepS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)) :
    coordinateValue Ω (CoordinateField Ω P)
      (shearCoordinateDataAt P a hS hfiniteS hsepS) =
        coordinate Ω P 1 + a • coordinate Ω P 2 := by
  exact elementEmbedding_variable Ω (CoordinateField Ω P)
    (coordinate Ω P 1 + a • coordinate Ω P 2) hS

theorem shearCoordinateDataAt_degree (a : Ω)
    (hS : Transcendental Ω
      (coordinate Ω P 1 + a • coordinate Ω P 2))
    (hfiniteS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Ω) (CoordinateField Ω P))
    (hsepS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)) :
    coordinateDegree Ω (CoordinateField Ω P)
      (shearCoordinateDataAt P a hS hfiniteS hsepS) =
        (letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
          (elementEmbedding Ω (CoordinateField Ω P)
            (coordinate Ω P 1 + a • coordinate Ω P 2)
            hS).toRingHom.toAlgebra;
          Module.finrank (RatFunc Ω) (CoordinateField Ω P)) := by
  rfl

theorem finite_zero_points_le_global_of_common_shear
    (hfinite : ProjectionsFinite Ω P)
    (hnonpoint : ∀ v : Fin 3 → Ω,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hZ : Transcendental Ω (coordinate Ω P 2))
    (hsepY : ∀ hY : Transcendental Ω (coordinate Ω P 0),
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        rationalBaseAlgebra Ω P 0 hY
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (hsepZ : ∀ hZ' : Transcendental Ω (coordinate Ω P 2),
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        rationalBaseAlgebra Ω P 2 hZ'
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (a : Ω)
    (hS : Transcendental Ω
      (coordinate Ω P 1 + a • coordinate Ω P 2))
    (hfiniteS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Ω) (CoordinateField Ω P))
    (hsepS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (A : MvPolynomial (Fin 3) Ω) (hA : A ∉ P)
    (cap : Fin 3 → ℕ) (hcap : ∀ i, A.degreeOf i ≤ cap i)
    (points : Finset (Fin 3 → Ω))
    (hpointsP : ∀ v ∈ points,
      P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hpointsA : ∀ v ∈ points, MvPolynomial.aeval v A = 0) :
    points.card ≤ globalShearCost P
      (letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra;
        Module.finrank (RatFunc Ω) (CoordinateField Ω P)) cap := by
  classical
  let embeddingS := elementEmbedding Ω (CoordinateField Ω P)
    (coordinate Ω P 1 + a • coordinate Ω P 2) hS
  let dS : ℕ :=
    letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
      embeddingS.toRingHom.toAlgebra
    Module.finrank (RatFunc Ω) (CoordinateField Ω P)
  obtain ⟨B, hBcap, hBquot⟩ :=
    shearedPolynomialTransportAt_of_degree P a A cap hcap

  letI : Algebra (Polynomial Ω) (CoordinateRing Ω P) :=
    quotientPolynomialAlgebra Ω P 2
  letI : Algebra (Polynomial Ω) (CoordinateField Ω P) :=
    polynomialBaseAlgebra Ω P 2
  letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
    rationalBaseAlgebra Ω P 2 hZ
  letI := quotientBaseScalarTower Ω P 2
  letI := polynomialBaseScalarTower Ω P 2
  letI := quotientFractionScalarTower Ω P 2
  letI := polynomialRationalScalarTower Ω P 2 hZ
  letI := rationalBaseScalarTower Ω P 2 hZ
  letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω P) :=
    hfinite 2 hZ
  letI : Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P) :=
    hsepZ hZ

  let c : Fin 3 → Coordinate Ω (CoordinateField Ω P) :=
    ![actualCoordinateDataAt P hfinite 0 hsepY,
      shearCoordinateDataAt P a hS hfiniteS hsepS,
      actualCoordinateDataAt P hfinite 2 hsepZ]
  have hc : ∀ j,
      coordinateValue Ω (CoordinateField Ω P) (c j) =
        algebraMap (CoordinateRing Ω P) (CoordinateField Ω P)
          (shearedRingCoordinatesAt P a j) := by
    intro j
    fin_cases j
    · change coordinateValue Ω (CoordinateField Ω P)
          (actualCoordinateDataAt P hfinite 0 hsepY) =
        algebraMap (CoordinateRing Ω P) (CoordinateField Ω P)
          (quotientCoordinate Ω P 0)
      rw [quotientCoordinate_fraction]
      exact actualCoordinateDataAt_value P hfinite 0 hsepY
    · change coordinateValue Ω (CoordinateField Ω P)
          (shearCoordinateDataAt P a hS hfiniteS hsepS) =
        algebraMap (CoordinateRing Ω P) (CoordinateField Ω P)
          (quotientCoordinate Ω P 1 +
            algebraMap Ω (CoordinateRing Ω P) a * quotientCoordinate Ω P 2)
      rw [map_add, map_mul, quotientCoordinate_fraction,
        quotientCoordinate_fraction]
      rw [← IsScalarTower.algebraMap_apply Ω (CoordinateRing Ω P)
        (CoordinateField Ω P)]
      simpa only [Algebra.smul_def] using
        shearCoordinateDataAt_value P a hS hfiniteS hsepS
    · change coordinateValue Ω (CoordinateField Ω P)
          (actualCoordinateDataAt P hfinite 2 hsepZ) =
        algebraMap (CoordinateRing Ω P) (CoordinateField Ω P)
          (quotientCoordinate Ω P 2)
      rw [quotientCoordinate_fraction]
      exact actualCoordinateDataAt_value P hfinite 2 hsepZ
  have hcdegree : ∀ j,
      coordinateDegree Ω (CoordinateField Ω P) (c j) =
        globalShearDegree P dS j := by
    intro j
    fin_cases j
    · exact actualCoordinateDataAt_degree P hfinite 0 hsepY
    · exact shearCoordinateDataAt_degree P a hS hfiniteS hsepS
    · exact actualCoordinateDataAt_degree P hfinite 2 hsepZ
  have hBnonzero :
      MvPolynomial.eval₂Hom
        (algebraMap Ω (CoordinateRing Ω P))
        (shearedRingCoordinatesAt P a) B ≠ 0 := by
    rw [hBquot]
    intro hzero
    exact hA (Ideal.Quotient.eq_zero_iff_mem.mp hzero)

  let liftPoint : {v : Fin 3 → Ω // v ∈ points} →
      (CoordinateRing Ω P →ₐ[Ω] Ω) :=
    fun v => pointHom Ω P ⟨v.1, hpointsP v.1 v.2⟩
  have hlift_injective : Function.Injective liftPoint := by
    intro v w hvw
    have hpoint := pointHom_injective Ω P hvw
    apply Subtype.ext
    exact congrArg (fun z : PointOn Ω P => z.val) hpoint
  let modelPoints := points.attach.image liftPoint
  have hmodelPoints : ∀ ψ ∈ modelPoints,
      ψ (MvPolynomial.eval₂Hom
        (algebraMap Ω (CoordinateRing Ω P))
        (shearedRingCoordinatesAt P a) B) = 0 := by
    intro ψ hψ
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hψ
    calc
      liftPoint v (MvPolynomial.eval₂Hom
          (algebraMap Ω (CoordinateRing Ω P))
          (shearedRingCoordinatesAt P a) B) =
          liftPoint v (Ideal.Quotient.mk P A) :=
            congrArg (fun q => liftPoint v q) hBquot
      _ = MvPolynomial.aeval v.1 A := pointHom_mk Ω P _ A
      _ = 0 := hpointsA v.1 v.2
  have hcount := finite_model_zero_points_le_box
    Ω (CoordinateField Ω P) (CoordinateRing Ω P)
    (shearedRingCoordinatesAt P a) c hc (shearedPolynomialCap cap)
    B hBcap hBnonzero modelPoints hmodelPoints
  have hcountNat : modelPoints.card ≤
      ∑ j, shearedPolynomialCap cap j *
        coordinateDegree Ω (CoordinateField Ω P) (c j) := by
    exact_mod_cast hcount
  have hsum :
      (∑ j, shearedPolynomialCap cap j *
        coordinateDegree Ω (CoordinateField Ω P) (c j)) =
        globalShearCost P dS cap := by
    unfold globalShearCost
    apply Finset.sum_congr rfl
    intro j _
    rw [hcdegree j]
  rw [hsum] at hcountNat
  have hcard : modelPoints.card = points.card := by
    change (points.attach.image liftPoint).card = points.card
    rw [Finset.card_image_of_injective _ hlift_injective,
      Finset.card_attach]
  rw [hcard] at hcountNat
  exact hcountNat

variable {K : Type} [Field K]
variable (φ : Polynomial K →+* Ω)
local instance : DecidableEq K := Classical.decEq K

theorem globalShearFiberCertificate_of_common_shear
    (hfinite : ProjectionsFinite Ω P)
    (hnonpoint : ∀ v : Fin 3 → Ω,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hZ : Transcendental Ω (coordinate Ω P 2))
    (hsepY : ∀ hY : Transcendental Ω (coordinate Ω P 0),
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        rationalBaseAlgebra Ω P 0 hY
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (hsepZ : ∀ hZ' : Transcendental Ω (coordinate Ω P 2),
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        rationalBaseAlgebra Ω P 2 hZ'
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (a : Ω)
    (hS : Transcendental Ω
      (coordinate Ω P 1 + a • coordinate Ω P 2))
    (hfiniteS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Ω) (CoordinateField Ω P))
    (hsepS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Γ : Finset K) (p w : ℕ) [CharP Ω p] (hchar : w < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom
      (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ
        (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : ∀ γ ∈ Γ, P ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
    (cap : Fin 3 → ℕ) :
    GlobalShearFiberCertificate φ P F selected Γ w
      (letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra;
        Module.finrank (RatFunc Ω) (CoordinateField Ω P)) cap := by
  classical
  intro x u₀ u₁ hproper hcap
  let fiber := Γ.filter (fun γ => (selected γ).eval x = u₀ + γ * u₁)
  let points := fiber.image (selectedPoint φ selected)
  have hpointsP : ∀ v ∈ points,
      P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hv
    have hγ' : γ ∈ Γ.filter
        (fun η => (selected η).eval x = u₀ + η * u₁) := by
      simpa only [fiber] using hγ
    exact hpoint γ (Finset.mem_filter.mp hγ').1
  have hpointsA : ∀ v ∈ points,
      MvPolynomial.aeval v (agreementPolynomial φ F w x u₀ u₁) = 0 := by
    intro v hv
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hv
    have hγ' : γ ∈ Γ.filter
        (fun η => (selected η).eval x = u₀ + η * u₁) := by
      simpa only [fiber] using hγ
    obtain ⟨hγΓ, hagree⟩ := Finset.mem_filter.mp hγ'
    exact (selected_agreement_zero_iff φ F selected p w hchar γ
      (hdegree γ hγΓ) (hsolution γ hγΓ) (hregular γ hγΓ)
      x u₀ u₁).mpr hagree
  have hcount := finite_zero_points_le_global_of_common_shear P
    hfinite hnonpoint hZ hsepY hsepZ a hS hfiniteS hsepS
    (agreementPolynomial φ F w x u₀ u₁) hproper cap hcap
    points hpointsP hpointsA
  have hcard : points.card = fiber.card :=
    Finset.card_image_of_injective _ (selectedPoint_injective φ selected)
  have hfiber : fiber.card ≤ globalShearCost P
      (letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra;
        Module.finrank (RatFunc Ω) (CoordinateField Ω P)) cap := by
    rwa [← hcard]
  simpa only [fiber] using hfiber

theorem globalShearFiberCertificate_of_algebraic_z
    (hfinite : ProjectionsFinite Ω P)
    (hnonpoint : ∀ v : Fin 3 → Ω,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hZalg : IsAlgebraic Ω (coordinate Ω P 2))
    (a : Ω) (dS : ℕ)
    (hSdegree : Transcendental Ω
      (coordinate Ω P 1 + a • coordinate Ω P 2) → 1 ≤ dS)
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Γ : Finset K) (w : ℕ)
    (hpoint : ∀ γ ∈ Γ, P ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
    (cap : Fin 3 → ℕ) (hcapY : 1 ≤ cap 0) (hcapS : 1 ≤ cap 1) :
    GlobalShearFiberCertificate φ P F selected Γ w dS cap := by
  apply globalShearFiberCertificate_of_seedCoordinate_isAlgebraic
    φ P F selected Γ w dS cap hpoint hZalg
  exact globalShearCost_pos_of_seedCoordinate_isAlgebraic
    Ω P hfinite hnonpoint hZalg a dS cap hSdegree hcapY hcapS

end

end ProximityPrize.SubmissionLower.CommonShearFiberPrototype
