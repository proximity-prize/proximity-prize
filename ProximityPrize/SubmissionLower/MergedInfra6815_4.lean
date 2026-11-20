import ProximityPrize.SubmissionLower.LowerFoundation
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.GenericSlicePoints6807
open scoped Classical BigOperators
open RCN002 RCN072 RCN264 RCN207 RCN208 RCN134 RCN084
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 300000

variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
local notation "Poly" => MvPolynomial (Fin 3) K
local notation "PE" => MvPolynomial (Fin 3) E

theorem filteredCut_zero {R : Type*} [CommRing R] (A H G : R) :
    filteredCut 0 (fun _ : Fin 1 => A) H G = A := by
  simp [filteredCut, Fin.sum_univ_succ]

def sliceEquation (ell : Poly) : PE :=
  MvPolynomial.C (algebraMap (RatFunc K) E (RCN202.rationalVariable K)) -
    scalarPolynomialMap K E ell

abbrev gateOneComponent (F A R : Poly) (C : RegularComponent K F A R) :
    RegularComponent K F (filteredCut 0 (fun _ : Fin 1 => A) 1 0) 1 :=
  ⟨C.1, by
    classical
    apply (mem_regularComponents K).mpr
    constructor
    · simpa only [filteredCut_zero] using regularComponent_mem K F A R C
    · intro h
      have hz : coordinateEvaluation K C.1 (1 : Poly) = 0 := by
        apply RingHom.mem_ker.mp
        change (1 : Poly) ∈ RingHom.ker (coordinateEvaluation K C.1).toRingHom
        rwa [coordinateEvaluation_ker K C.1]
      exact one_ne_zero (by simpa only [map_one] using hz)⟩

omit [IsAlgClosed E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E] in
theorem scalar_eval_embedding (P : Ideal Poly) [P.IsPrime]
    (f : CoordinateField K P →ₐ[K] E) (A : Poly) :
    MvPolynomial.eval (embeddingPoint P f) (scalarPolynomialMap K E A) =
      f (coordinateEvaluation K P A) := by
  have h := AlgHom.congr_fun (embeddingPoint_aeval P f) A
  change MvPolynomial.eval (embeddingPoint P f)
    (MvPolynomial.map (algebraMap K E) A) = _
  rw [MvPolynomial.eval_map]
  exact h

omit [IsAlgClosed E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E] in
theorem scalar_eval_ne_zero (P : Ideal Poly) [P.IsPrime]
    (f : CoordinateField K P →ₐ[K] E) (A : Poly) (hA : A ∉ P) :
    MvPolynomial.eval (embeddingPoint P f) (scalarPolynomialMap K E A) ≠ 0 := by
  rw [scalar_eval_embedding]
  intro h
  apply hA
  rw [← coordinateEvaluation_ker K P]
  exact (map_eq_zero_iff f f.injective).mp h

theorem embedding_point_certificate
    (F A R ell : Poly) (C : RegularComponent K F A R)
    [Algebra (RatFunc K) (CoordinateField K C.1)]
    [IsScalarTower K (RatFunc K) (CoordinateField K C.1)]
    [FiniteDimensional (RatFunc K) (CoordinateField K C.1)]
    (hj : algebraMap (RatFunc K) (CoordinateField K C.1)
      (RCN202.rationalVariable K) = coordinateEvaluation K C.1 ell)
    (f : CoordinateField K C.1 →ₐ[RatFunc K] E) :
    let mu := scalarPolynomialMap K E
    let v := embeddingPoint C.1 (f.restrictScalars K)
    MvPolynomial.eval v (mu F) = 0 ∧
      MvPolynomial.eval v (sliceEquation (E := E) ell) = 0 ∧
      MvPolynomial.aeval v (mu A) = 0 ∧
      MvPolynomial.eval v (mu R) ≠ 0 ∧
      IsolatedPoint (mu F) (sliceEquation (E := E) ell) (mu A) v := by
  let C0 := gateOneComponent F A R C
  have hj0 : algebraMap (RatFunc K) (CoordinateField K C0.1)
      (RCN202.rationalVariable K) = movingValue C0.1 1 0 ell 1 := by
    simpa only [movingValue, map_one, map_zero, mul_zero, zero_div, add_zero]
      using hj
  have h1 : (1 : Poly) ∉ C0.1 := regularComponent_H_not_mem K _ _ _ C0
  have hcert := RCN202.embedding_point_certificate F 1 0 ell 1 0
    (fun _ : Fin 1 => A) C0 hj0 h1 f
  have hc :
      MvPolynomial.eval (embeddingPoint C.1 (f.restrictScalars K))
        (scalarPolynomialMap K E F) = 0 ∧
      MvPolynomial.eval (embeddingPoint C.1 (f.restrictScalars K))
        (sliceEquation (E := E) ell) = 0 ∧
      MvPolynomial.aeval (embeddingPoint C.1 (f.restrictScalars K))
        (scalarPolynomialMap K E A) = 0 ∧
      MvPolynomial.eval (embeddingPoint C.1 (f.restrictScalars K)) (1 : PE) ≠ 0 ∧
      IsolatedPoint (scalarPolynomialMap K E F) (sliceEquation (E := E) ell)
        (scalarPolynomialMap K E A) (embeddingPoint C.1 (f.restrictScalars K)) := by
    simpa only [map_one, map_zero,
      movingEquation, eliminatedCut, filteredCut_zero, one_mul, mul_zero,
      sub_zero, sliceEquation] using hcert
  exact ⟨hc.1, hc.2.1, hc.2.2.1,
    scalar_eval_ne_zero C.1 (f.restrictScalars K) R
      (regularComponent_H_not_mem K F A R C), hc.2.2.2.2⟩

section WeightedEmbeddings
variable {I : Type} [Fintype I]
  (P : I → Ideal (MvPolynomial (Fin 3) K)) [∀ i, (P i).IsPrime]
  [∀ i, Algebra (RatFunc K) (CoordinateField K (P i))]
  [∀ i, IsScalarTower K (RatFunc K) (CoordinateField K (P i))]
  [∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i))]
  [∀ i, Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i))]

theorem weighted_embedding_sum (weight : I → ℕ) :
    (∑ z : (Σ i, CoordinateField K (P i) →ₐ[RatFunc K] E), weight z.1) =
      ∑ i, weight i * Module.finrank (RatFunc K) (CoordinateField K (P i)) := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, AlgHom.card, mul_comm]

end WeightedEmbeddings
end
end ProximityPrize.SubmissionLower.GenericSlicePoints6807
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.FirstCutMultiplicityTransport6807
open RCN244 RCN135 RCN095 RCN074 RCN218 RCN186 RCN310 RCN313 RCN086 RCN217 RCN248
noncomputable section
set_option autoImplicit false
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

end
end ProximityPrize.SubmissionLower.FirstCutMultiplicityTransport6807
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.ActualSliceMultiplicity6807
open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN007 RCN055 RCN074 RCN086 RCN095
open RCN134 RCN135 RCN136 RCN208 RCN217 RCN244 RCN248 RCN313
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
variable {K I E : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "PK4" => MvPolynomial (Fin 4) K

def originalToSlice (D : Ideal PE) : PK4 →+* CoordinateRing E D :=
  (Ideal.Quotient.mk D).comp ((scalarPolynomialMap Ω E).comp
    (surfaceMap (polynomialEmbedding K)))

def slicePoint (S : Stage K I Gamma x p flag errorCap stageSupport)
    (C : FirstTailComponent S) (emb : CoordinateField Ω C.1 →ₐ[Ω] E)
    (D : Ideal PE)
    (hD : D ≤ RingHom.ker
      (MvPolynomial.aeval (embeddingPoint C.1 emb) : PE →ₐ[E] E).toRingHom) :
    PointOn E D := ⟨embeddingPoint C.1 emb, hD⟩

theorem originalToSlice_point_value
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (C : FirstTailComponent S) (emb : CoordinateField Ω C.1 →ₐ[Ω] E)
    (D : Ideal PE) [D.IsPrime]
    (hD : D ≤ RingHom.ker
      (MvPolynomial.aeval (embeddingPoint C.1 emb) : PE →ₐ[E] E).toRingHom)
    (F : PK4) :
    pointHom E D (slicePoint S C emb D hD) (originalToSlice (K := K) D F) =
      emb (coordinateEvaluation Ω C.1 (surfaceMap (polynomialEmbedding K) F)) := by
  change MvPolynomial.eval (embeddingPoint C.1 emb)
    (scalarPolynomialMap Ω E (surfaceMap (polynomialEmbedding K) F)) = _
  exact GenericSlicePoints6807.scalar_eval_embedding C.1 emb _

theorem slice_point_kernel_contracts
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (C : FirstTailComponent S) (emb : CoordinateField Ω C.1 →ₐ[Ω] E)
    (D : Ideal PE) [D.IsPrime]
    (hD : D ≤ RingHom.ker
      (MvPolynomial.aeval (embeddingPoint C.1 emb) : PE →ₐ[E] E).toRingHom) :
    Ideal.comap (originalToSlice (K := K) D)
      (RingHom.ker (pointHom E D (slicePoint S C emb D hD)).toRingHom) =
        componentPrime S C := by
  ext F
  change pointHom E D (slicePoint S C emb D hD) (originalToSlice D F) = 0 ↔
    surfaceMap (polynomialEmbedding K) F ∈ C.1
  rw [originalToSlice_point_value S C emb D hD,
    map_eq_zero_iff emb emb.injective]
  change surfaceMap (polynomialEmbedding K) F ∈
    RingHom.ker (coordinateEvaluation Ω C.1).toRingHom ↔ _
  rw [coordinateEvaluation_ker Ω C.1]

theorem original_factor_zero
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (C : FirstTailComponent S) (D : Ideal PE) [D.IsPrime]
    (hcarrier : scalarPolynomialMap Ω E S.G ∈ D) :
    originalToSlice (K := K) D (originalData S C).factor = 0 := by
  change Ideal.Quotient.mk D
    (scalarPolynomialMap Ω E
      (surfaceMap (polynomialEmbedding K) (originalData S C).factor)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact D.mem_of_dvd (map_dvd (scalarPolynomialMap Ω E)
    (originalData S C).factor_dvd) hcarrier

def firstTailInSlice
    (S : Stage K I Gamma x p flag errorCap stageSupport) (D : Ideal PE) :
    CoordinateRing E D :=
  Ideal.Quotient.mk D (scalarPolynomialMap Ω E
    (globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1)))

def firstTailScalarInSlice (D : Ideal PE) : CoordinateRing E D :=
  Ideal.Quotient.mk D (scalarPolynomialMap Ω E
    (MvPolynomial.C ((-(polynomialEmbedding K) Polynomial.X)^(RCN326.w+1))))

theorem firstTailInSlice_factorization
    (S : Stage K I Gamma x p flag errorCap stageSupport) (D : Ideal PE) :
    firstTailInSlice S D = originalToSlice (K := K) D
      (numerator K S.F (RCN326.w+1)) * firstTailScalarInSlice (K := K) D := by
  simp only [firstTailInSlice, firstTailScalarInSlice, originalToSlice,
    globalTailCut_eq, map_mul, RingHom.comp_apply]

theorem actual_first_tail_mem_point_power
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (C : FirstTailComponent S) (emb : CoordinateField Ω C.1 →ₐ[Ω] E)
    (D : Ideal PE) [D.IsPrime]
    (hD : D ≤ RingHom.ker
      (MvPolynomial.aeval (embeddingPoint C.1 emb) : PE →ₐ[E] E).toRingHom)
    (hcarrier : scalarPolynomialMap Ω E S.G ∈ D) :
    firstTailInSlice S D ∈
      (RingHom.ker (pointHom E D (slicePoint S C emb D hD)).toRingHom) ^
        localMultiplicity S (canonicalLocalDVRFamily S hproper) C := by
  let phi := pointHom E D (slicePoint S C emb D hD)
  let J := RingHom.ker phi.toRingHom
  letI : J.IsMaximal := RCN017.pointKernel_isMaximal phi
  have hf := original_factor_zero S C D hcarrier
  have hc := slice_point_kernel_contracts S C emb D hD
  have h := proper_global_tail_mem_projected_primary S hproper C
    (originalToSlice (K := K) D) 0 (firstTailInSlice S D)
    (firstTailScalarInSlice (K := K) D) J
    (by rw [hf]; exact Ideal.zero_mem _)
    (J.zero_mem) hc (firstTailInSlice_factorization S D)
  simpa [J] using h

theorem original_H_point_ne_zero
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (C : FirstTailComponent S) (emb : CoordinateField Ω C.1 →ₐ[Ω] E)
    (D : Ideal PE) [D.IsPrime]
    (hD : D ≤ RingHom.ker
      (MvPolynomial.aeval (embeddingPoint C.1 emb) : PE →ₐ[E] E).toRingHom) :
    pointHom E D (slicePoint S C emb D hD)
      (originalToSlice (K := K) D (polyH K S.F)) ≠ 0 := by
  rw [originalToSlice_point_value S C emb D hD]
  intro hz
  have he := (map_eq_zero_iff emb emb.injective).mp hz
  apply RCN312.firstTailComponent_regularity_not_mem S C
  rw [← coordinateEvaluation_ker Ω C.1]
  exact he

theorem scalar_surfaceMap (F : PK4) :
    scalarPolynomialMap Ω E (surfaceMap (polynomialEmbedding K) F) =
      surfaceMap ((algebraMap Ω E).comp (polynomialEmbedding K)) F := by
  simp only [RCN208.scalarPolynomialMap, RCN136.surfaceMap,
    RingHom.comp_apply, MvPolynomial.map_map]

theorem firstTailScalar_point_value
    (D : Ideal PE) [D.IsPrime] (point : PointOn E D) :
    pointHom E D point (firstTailScalarInSlice (K := K) D) =
      algebraMap Ω E ((-(polynomialEmbedding K) Polynomial.X)^(RCN326.w+1)) := by
  simp only [firstTailScalarInSlice, pointHom_mk,
    RCN208.scalarPolynomialMap, MvPolynomial.map_C, MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]

theorem firstTailScalar_point_ne_zero
    (D : Ideal PE) [D.IsPrime] (point : PointOn E D) :
    pointHom E D point (firstTailScalarInSlice (K := K) D) ≠ 0 := by
  rw [firstTailScalar_point_value]
  exact (map_ne_zero (algebraMap Ω E)).mpr (tail_scalar_ne_zero (polynomialEmbedding K)
    (polynomialEmbedding_injective K) (RCN326.w+1))

theorem firstTailInSlice_normal_form
    (S : Stage K I Gamma x p flag errorCap stageSupport) (D : Ideal PE) :
    firstTailInSlice S D = firstTailScalarInSlice (K := K) D *
      (originalToSlice (K := K) D (polyH K S.F))^3 *
        originalToSlice (K := K) D (baseNumerator S.F (RCN326.w-1)) := by
  rw [firstTailInSlice_factorization,
    show RCN326.w+1 = (RCN326.w-1)+2 by decide,
    numerator_eq_H_cube, map_mul, map_pow]
  ring

theorem originalToSlice_fraction_value (D : Ideal PE) [D.IsPrime] (F : PK4) :
    algebraMap (CoordinateRing E D) (CoordinateField E D)
      (originalToSlice (K := K) D F) =
      coordinateEvaluation E D
        (surfaceMap ((algebraMap Ω E).comp (polynomialEmbedding K)) F) := by
  change coordinateEvaluation E D
    (scalarPolynomialMap Ω E (surfaceMap (polynomialEmbedding K) F)) = _
  rw [scalar_surfaceMap]

theorem firstTailInSlice_ne_zero
    (S : Stage K I Gamma x p flag errorCap stageSupport) (D : Ideal PE)
    (hproper : scalarPolynomialMap Ω E
      (globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1)) ∉ D) :
    firstTailInSlice S D ≠ 0 := by
  intro hz
  exact hproper (Ideal.Quotient.eq_zero_iff_mem.mp hz)

theorem normalized_first_tail_identity {A L : Type*}
    [CommRing A] [Field L] (ev : A →+* L)
    (tail base H kappa : A) (w : ℕ)
    (hrel : tail = kappa * H^3 * base)
    (hH : ev H ≠ 0) (hk : ev kappa ≠ 0) :
    ev tail / ev (kappa * H^(w+3)) = ev base / (ev H)^w := by
  rw [hrel]
  simp only [map_mul, map_pow]
  rw [pow_add]
  field_simp
  <;> ring

end
end ProximityPrize.SubmissionLower.ActualSliceMultiplicity6807
end MergedPart2
