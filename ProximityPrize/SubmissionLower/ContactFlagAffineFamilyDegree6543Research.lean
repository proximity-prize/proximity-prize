import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagTriangularProjectionResearch
import ProximityPrize.SubmissionLower.ContactFlagTrapezoidFamilyDegree6543Research

/-!
# Exact family degrees in nested affine flag coordinates

This module evaluates the flag-transformed equations at

`U = Y + λ Z`, `V = S + μ Y + ν Z`, `Z = Z`

inside every original component field.  It proves that contraction of the
new evaluation kernel recovers the original component prime and that any two
non-base flag coordinates generate the field over the remaining rational
base.  The final theorem combines these facts with the characteristic-free
exact trapezoid family theorem.
-/

namespace ProximityPrize.SubmissionLower.ContactFlagAffineFamilyDegree6543Research

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveRationalProjection
  ArbitraryRationalProjectionResearch ActualPlaneCoordinateKernel
  TrivariateRationalCollection
open ContactFlagTriangularProjectionResearch
open ContactFlagTrapezoidFamilyDegree6543Research

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable (K : Type) [Field K]
variable (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]

def affineU (lam : K) : CoordinateField K P :=
  coordinate K P 0 + lam • coordinate K P 2

def affineV (μ ν : K) : CoordinateField K P :=
  coordinate K P 1 + μ • coordinate K P 0 + ν • coordinate K P 2

/-- Evaluation in the literal flag coordinates `(U,V,Z)`. -/
def flagEvaluation (lam μ ν : K) :
    MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K P :=
  MvPolynomial.aeval ![affineU K P lam, affineV K P μ ν,
    coordinate K P 2]

@[simp] theorem flagEvaluation_X_zero (lam μ ν : K) :
    flagEvaluation K P lam μ ν (MvPolynomial.X 0) = affineU K P lam := by
  simp [flagEvaluation]

@[simp] theorem flagEvaluation_X_one (lam μ ν : K) :
    flagEvaluation K P lam μ ν (MvPolynomial.X 1) = affineV K P μ ν := by
  simp [flagEvaluation]

@[simp] theorem flagEvaluation_X_two (lam μ ν : K) :
    flagEvaluation K P lam μ ν (MvPolynomial.X 2) = coordinate K P 2 := by
  simp [flagEvaluation]

/-- Evaluation after the inverse flag substitution is the original
coordinate evaluation. -/
theorem flagEvaluation_flag (lam μ ν : K)
    (F : MvPolynomial (Fin 3) K) :
    flagEvaluation K P lam μ ν (flagAlgHom lam μ ν F) =
      coordinateEvaluation K P F := by
  change MvPolynomial.eval₂Hom (algebraMap K (CoordinateField K P))
      ![coordinate K P 0 + lam • coordinate K P 2,
        coordinate K P 1 + μ • coordinate K P 0 + ν • coordinate K P 2,
        coordinate K P 2] (flagAlgHom lam μ ν F) = _
  rw [show lam • coordinate K P 2 =
      algebraMap K (CoordinateField K P) lam * coordinate K P 2 by
        simp [Algebra.smul_def],
    show μ • coordinate K P 0 =
      algebraMap K (CoordinateField K P) μ * coordinate K P 0 by
        simp [Algebra.smul_def],
    show ν • coordinate K P 2 =
      algebraMap K (CoordinateField K P) ν * coordinate K P 2 by
        simp [Algebra.smul_def],
    eval₂Hom_flag_at_affine]
  rw [coordinateEvaluation_eq_aeval]
  have hx : (![coordinate K P 0, coordinate K P 1, coordinate K P 2] :
      Fin 3 → CoordinateField K P) = coordinate K P := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  exact (MvPolynomial.aeval_eq_eval₂Hom (coordinate K P) F).symm

/-- Contracting the transformed evaluation kernel along the flag
automorphism recovers the original prime. -/
theorem flagEvaluation_kernel_contract (lam μ ν : K) :
    (RingHom.ker (flagEvaluation K P lam μ ν).toRingHom).comap
        (flagAlgHom lam μ ν).toRingHom = P := by
  rw [RingHom.comap_ker]
  have hcomp : (flagEvaluation K P lam μ ν).comp (flagAlgHom lam μ ν) =
      coordinateEvaluation K P := by
    apply AlgHom.ext
    intro F
    exact flagEvaluation_flag K P lam μ ν F
  have hring := congrArg
    (fun f : MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K P ↦
      f.toRingHom) hcomp
  rw [show (flagEvaluation K P lam μ ν).toRingHom.comp
      (flagAlgHom lam μ ν).toRingHom =
      (coordinateEvaluation K P).toRingHom from hring,
    coordinateEvaluation_ker]

private theorem top_of_affine_flag_mem
    [Algebra (RatFunc K) (CoordinateField K P)]
    [IsScalarTower K (RatFunc K) (CoordinateField K P)]
    (lam μ ν : K)
    (L : IntermediateField (RatFunc K) (CoordinateField K P))
    (hU : affineU K P lam ∈ L) (hV : affineV K P μ ν ∈ L)
    (hZ : coordinate K P 2 ∈ L) : L = ⊤ := by
  have hlam : algebraMap K (CoordinateField K P) lam ∈ L := by
    have h := L.algebraMap_mem (algebraMap K (RatFunc K) lam)
    simpa only [IsScalarTower.algebraMap_apply K (RatFunc K)
      (CoordinateField K P)] using h
  have hμ : algebraMap K (CoordinateField K P) μ ∈ L := by
    have h := L.algebraMap_mem (algebraMap K (RatFunc K) μ)
    simpa only [IsScalarTower.algebraMap_apply K (RatFunc K)
      (CoordinateField K P)] using h
  have hν : algebraMap K (CoordinateField K P) ν ∈ L := by
    have h := L.algebraMap_mem (algebraMap K (RatFunc K) ν)
    simpa only [IsScalarTower.algebraMap_apply K (RatFunc K)
      (CoordinateField K P)] using h
  have hY : coordinate K P 0 ∈ L := by
    have h := L.sub_mem hU (L.mul_mem hlam hZ)
    simpa only [affineU, Algebra.smul_def, add_sub_cancel_right] using h
  have hS : coordinate K P 1 ∈ L := by
    have h := L.sub_mem hV
      (L.add_mem (L.mul_mem hμ hY) (L.mul_mem hν hZ))
    have heq : affineV K P μ ν -
        (algebraMap K (CoordinateField K P) μ * coordinate K P 0 +
          algebraMap K (CoordinateField K P) ν * coordinate K P 2) =
        coordinate K P 1 := by
      simp only [affineV, Algebra.smul_def]
      ring
    rwa [heq] at h
  have hcoords : Set.range (coordinate K P) ⊆ L.restrictScalars K := by
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact hY
    · exact hS
    · exact hZ
  have htop : L.restrictScalars K = ⊤ := by
    apply top_unique
    rw [← adjoin_coordinates_eq_top K P]
    exact IntermediateField.adjoin_le_iff.mpr hcoords
  exact (IntermediateField.restrictScalars_eq_top_iff (K := K)).mp htop

/-- With `U` as rational base, `(Z,V)` generate the component field. -/
theorem flag_generators_u (lam μ ν : K)
    (hU : Transcendental K (affineU K P lam)) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      (elementEmbedding K (CoordinateField K P) (affineU K P lam)
        hU).toRingHom.toAlgebra
    IntermediateField.adjoin (RatFunc K)
      ({coordinate K P 2, affineV K P μ ν} :
        Set (CoordinateField K P)) = ⊤ := by
  letI : Algebra (RatFunc K) (CoordinateField K P) :=
    (elementEmbedding K (CoordinateField K P) (affineU K P lam)
      hU).toRingHom.toAlgebra
  letI : IsScalarTower K (RatFunc K) (CoordinateField K P) :=
    IsScalarTower.of_algebraMap_eq fun c ↦
      ((elementEmbedding K (CoordinateField K P) (affineU K P lam)
        hU).commutes c).symm
  let L : IntermediateField (RatFunc K) (CoordinateField K P) :=
    IntermediateField.adjoin (RatFunc K)
      {coordinate K P 2, affineV K P μ ν}
  have hZ : coordinate K P 2 ∈ L :=
    IntermediateField.mem_adjoin_pair_left _ _ _
  have hV : affineV K P μ ν ∈ L :=
    IntermediateField.mem_adjoin_pair_right _ _ _
  have hbase := L.algebraMap_mem
    (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
  have hUmem : affineU K P lam ∈ L := by
    change elementEmbedding K (CoordinateField K P) (affineU K P lam) hU
      (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ∈ L at hbase
    rwa [elementEmbedding_variable] at hbase
  exact top_of_affine_flag_mem K P lam μ ν L hUmem hV hZ

/-- With `V` as rational base, `(Z,U)` generate the component field. -/
theorem flag_generators_v (lam μ ν : K)
    (hV : Transcendental K (affineV K P μ ν)) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      (elementEmbedding K (CoordinateField K P) (affineV K P μ ν)
        hV).toRingHom.toAlgebra
    IntermediateField.adjoin (RatFunc K)
      ({coordinate K P 2, affineU K P lam} :
        Set (CoordinateField K P)) = ⊤ := by
  letI : Algebra (RatFunc K) (CoordinateField K P) :=
    (elementEmbedding K (CoordinateField K P) (affineV K P μ ν)
      hV).toRingHom.toAlgebra
  letI : IsScalarTower K (RatFunc K) (CoordinateField K P) :=
    IsScalarTower.of_algebraMap_eq fun c ↦
      ((elementEmbedding K (CoordinateField K P) (affineV K P μ ν)
        hV).commutes c).symm
  let L : IntermediateField (RatFunc K) (CoordinateField K P) :=
    IntermediateField.adjoin (RatFunc K)
      {coordinate K P 2, affineU K P lam}
  have hZ : coordinate K P 2 ∈ L :=
    IntermediateField.mem_adjoin_pair_left _ _ _
  have hU : affineU K P lam ∈ L :=
    IntermediateField.mem_adjoin_pair_right _ _ _
  have hbase := L.algebraMap_mem
    (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
  have hVmem : affineV K P μ ν ∈ L := by
    change elementEmbedding K (CoordinateField K P) (affineV K P μ ν) hV
      (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ∈ L at hbase
    rwa [elementEmbedding_variable] at hbase
  exact top_of_affine_flag_mem K P lam μ ν L hU hVmem hZ

/-- With `Z` as rational base, `(U,V)` generate the component field. -/
theorem flag_generators_z (lam μ ν : K)
    (hZ : Transcendental K (coordinate K P 2)) :
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      (elementEmbedding K (CoordinateField K P) (coordinate K P 2)
        hZ).toRingHom.toAlgebra
    IntermediateField.adjoin (RatFunc K)
      ({affineU K P lam, affineV K P μ ν} :
        Set (CoordinateField K P)) = ⊤ := by
  letI : Algebra (RatFunc K) (CoordinateField K P) :=
    (elementEmbedding K (CoordinateField K P) (coordinate K P 2)
      hZ).toRingHom.toAlgebra
  letI : IsScalarTower K (RatFunc K) (CoordinateField K P) :=
    IsScalarTower.of_algebraMap_eq fun c ↦
      ((elementEmbedding K (CoordinateField K P) (coordinate K P 2)
        hZ).commutes c).symm
  let L : IntermediateField (RatFunc K) (CoordinateField K P) :=
    IntermediateField.adjoin (RatFunc K)
      {affineU K P lam, affineV K P μ ν}
  have hU : affineU K P lam ∈ L :=
    IntermediateField.mem_adjoin_pair_left _ _ _
  have hV : affineV K P μ ν ∈ L :=
    IntermediateField.mem_adjoin_pair_right _ _ _
  have hbase := L.algebraMap_mem
    (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
  have hZmem : coordinate K P 2 ∈ L := by
    change elementEmbedding K (CoordinateField K P) (coordinate K P 2) hZ
      (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) ∈ L at hbase
    rwa [elementEmbedding_variable] at hbase
  exact top_of_affine_flag_mem K P lam μ ν L hU hV hZmem

section Family

variable {I : Type} [Fintype I]
variable (Q : I → Ideal (MvPolynomial (Fin 3) K)) [∀ i, (Q i).IsPrime]

theorem flagEvaluation_kernel_family_injective
    (hinj : Function.Injective Q) (lam μ ν : K) :
    Function.Injective (fun i ↦
      RingHom.ker (flagEvaluation K (Q i) lam μ ν).toRingHom) := by
  intro i j hij
  apply hinj
  have hc := congrArg (Ideal.comap (flagAlgHom lam μ ν).toRingHom) hij
  simpa only [flagEvaluation_kernel_contract] using hc

/-- Exact trapezoid family-degree theorem for any one of the literal flag
coordinates used as rational base.  All support arithmetic remains explicit
in the hypotheses, so there is no rectangular fallback. -/
theorem finite_sum_flag_finrank_trapezoid
    (hinj : Function.Injective Q) (lam μ ν : K)
    (order : Fin 3 ≃ Fin 3)
    (ht : ∀ i, Transcendental K
      (flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 0))))
    (hgen : ∀ i,
      letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
        (elementEmbedding K (CoordinateField K (Q i))
          (flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 0)))
          (ht i)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc K)
        ({flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 2)),
          flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 1))} :
          Set (CoordinateField K (Q i))) = ⊤)
    (G H : MvPolynomial (Fin 3) K) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ Q i) (hHmem : ∀ i, H ∈ Q i)
    (hproper : ¬ G ∣ H)
    (hpositive : 0 <
      (planeMap K order (flagAlgHom lam μ ν G)).natDegree)
    (n mCap totalG totalH cap : ℕ) (hHne : H ≠ 0)
    (hGouter : (planeMap K order
      (flagAlgHom lam μ ν G)).natDegree ≤ n)
    (hHouter : (planeMap K order
      (flagAlgHom lam μ ν H)).natDegree ≤ mCap)
    (hGsupport : ∀ d ∈ (rationalMap K order
      (flagAlgHom lam μ ν G)).support, d 0 + d 1 ≤ totalG)
    (hHsupport : ∀ d ∈ (rationalMap K order
      (flagAlgHom lam μ ν H)).support, d 0 + d 1 ≤ totalH)
    (hbudget : ∀ m, m ≤ mCap →
      m * totalG + n * totalH - m * n ≤ cap) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) :=
      fun i ↦ (elementEmbedding K (CoordinateField K (Q i))
        (flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 0)))
        (ht i)).toRingHom.toAlgebra
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (Q i))) ≤ cap := by
  let e : ∀ i, MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K (Q i) :=
    fun i ↦ flagEvaluation K (Q i) lam μ ν
  have hGroot : ∀ i, e i (flagAlgHom lam μ ν G) = 0 := by
    intro i
    rw [show e i (flagAlgHom lam μ ν G) = coordinateEvaluation K (Q i) G
      from flagEvaluation_flag K (Q i) lam μ ν G]
    change G ∈ RingHom.ker (coordinateEvaluation K (Q i)).toRingHom
    rw [coordinateEvaluation_ker]
    exact hGmem i
  have hHroot : ∀ i, e i (flagAlgHom lam μ ν H) = 0 := by
    intro i
    rw [show e i (flagAlgHom lam μ ν H) = coordinateEvaluation K (Q i) H
      from flagEvaluation_flag K (Q i) lam μ ν H]
    change H ∈ RingHom.ker (coordinateEvaluation K (Q i)).toRingHom
    rw [coordinateEvaluation_ker]
    exact hHmem i
  exact finite_sum_finrank_bound_trapezoid K order
    (fun i ↦ CoordinateField K (Q i)) e ht hgen
    (flagEvaluation_kernel_family_injective K Q hinj lam μ ν)
    (flagAlgHom lam μ ν G) (flagAlgHom lam μ ν H)
    ((flag_irreducible_iff lam μ ν G).mpr hG)
    hGroot hHroot (by simpa only [flag_dvd_iff] using hproper) hpositive
    n mCap totalG totalH cap (flag_ne_zero lam μ ν hHne)
    hGouter hHouter hGsupport hHsupport hbudget

end Family

end

end ProximityPrize.SubmissionLower.ContactFlagAffineFamilyDegree6543Research

#print axioms ProximityPrize.SubmissionLower.ContactFlagAffineFamilyDegree6543Research.flagEvaluation_kernel_contract
#print axioms ProximityPrize.SubmissionLower.ContactFlagAffineFamilyDegree6543Research.flag_generators_u
#print axioms ProximityPrize.SubmissionLower.ContactFlagAffineFamilyDegree6543Research.flag_generators_v
#print axioms ProximityPrize.SubmissionLower.ContactFlagAffineFamilyDegree6543Research.flag_generators_z
#print axioms ProximityPrize.SubmissionLower.ContactFlagAffineFamilyDegree6543Research.finite_sum_flag_finrank_trapezoid
