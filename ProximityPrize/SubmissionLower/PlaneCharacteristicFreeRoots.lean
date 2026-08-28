import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.PlaneCharacteristicFreeDegree
import ProximityPrize.SubmissionLower.PlaneRootSeparability
import ProximityPrize.SubmissionLower.PlaneFunctionFieldDegree
import ProximityPrize.SubmissionLower.PlaneSmallCharacteristicDegree
import ProximityPrize.SubmissionLower.PlaneCoefficientExtension

/-!
# Characteristic-free degree from actual proper plane roots

The proper resultant first makes the inner generator integral.  A
nonzero specialization of the irreducible plane equation makes the
outer generator integral over the first simple extension.  Their two
power bases then feed the full-corank resultant theorem, with no
separability or characteristic-size hypothesis.
-/

namespace ProximityPrize.SubmissionLower.PlaneCharacteristicFreeRoots

open PlaneFunctionFieldDegree

noncomputable section

variable (K E : Type) [Field K] [Field E] [Algebra K E]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq E := Classical.decEq E

theorem finite_finrank_le_resultant_natDegree
    (P Q : Polynomial (Polynomial K))
    (hirreducible : Irreducible P) (hpositive : 0 < P.natDegree)
    (hproper : ¬ P ∣ Q)
    (y r : E)
    (hgenerate : IntermediateField.adjoin K ({y, r} : Set E) = ⊤)
    (hP : planeEval K E y r P = 0)
    (hQ : planeEval K E y r Q = 0) :
    FiniteDimensional K E ∧
      Module.finrank K E ≤
        (Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree := by
  classical
  have hresne :=
    PlaneResultantIrreducible.irreducible_resultant_ne_zero_of_not_dvd
      P Q hirreducible hpositive hproper
  have hPeval : Polynomial.eval₂
      (Polynomial.eval₂RingHom (algebraMap K E) y) r P = 0 := by
    rw [← PlaneSmallCharacteristicDegree.planeEval_eq_eval₂]
    exact hP
  have hQeval : Polynomial.eval₂
      (Polynomial.eval₂RingHom (algebraMap K E) y) r Q = 0 := by
    rw [← PlaneSmallCharacteristicDegree.planeEval_eq_eval₂]
    exact hQ
  have hresroot := PlaneRootSeparability.resultant_aeval_eq_zero_of_common_root
    P Q P.natDegree Q.natDegree le_rfl le_rfl
      (Or.inl (Nat.ne_of_gt hpositive)) y r hPeval hQeval
  have hy : IsIntegral K y :=
    IsAlgebraic.isIntegral ⟨Polynomial.resultant P Q P.natDegree Q.natDegree,
      hresne, hresroot⟩
  let A : IntermediateField K E := IntermediateField.adjoin K {y}
  let yA : A := ⟨y, IntermediateField.mem_adjoin_simple_self K y⟩
  let g : Polynomial K →+* A :=
    Polynomial.eval₂RingHom (algebraMap K A) yA
  let Py : Polynomial A := P.map g
  have hPyne : Py ≠ 0 := by
    have h := PlaneCoefficientExtension.bimap_specialization_ne_zero
      (algebraMap K A) P (hirreducible.isPrimitive (Nat.ne_of_gt hpositive)) yA
    rw [PlaneCoefficientExtension.bimap_specialization] at h
    exact h
  have hcoefficient : (algebraMap A E).comp g =
      Polynomial.eval₂RingHom (algebraMap K E) y := by
    apply Polynomial.ringHom_ext
    · intro c
      change algebraMap A E
        (Polynomial.eval₂ (algebraMap K A) yA (Polynomial.C c)) =
          Polynomial.eval₂ (algebraMap K E) y (Polynomial.C c)
      rw [Polynomial.eval₂_C, Polynomial.eval₂_C]
      exact (IsScalarTower.algebraMap_apply K A E c).symm
    · change algebraMap A E
        (Polynomial.eval₂ (algebraMap K A) yA Polynomial.X) =
          Polynomial.eval₂ (algebraMap K E) y Polynomial.X
      rw [Polynomial.eval₂_X, Polynomial.eval₂_X]
      rfl
  have hPyroot : Polynomial.aeval r Py = 0 := by
    change Polynomial.eval₂ (algebraMap A E) r (P.map g) = 0
    rw [Polynomial.eval₂_map, hcoefficient]
    exact hPeval
  have hQyroot : Polynomial.eval₂ (algebraMap A E) r (Q.map g) = 0 := by
    rw [Polynomial.eval₂_map, hcoefficient]
    exact hQeval
  have hr : IsIntegral A r := IsAlgebraic.isIntegral ⟨Py, hPyne, hPyroot⟩
  have htop : IntermediateField.adjoin A {r} = ⊤ := by
    apply IntermediateField.restrictScalars_injective K
    rw [IntermediateField.adjoin_adjoin_left, IntermediateField.restrictScalars_top]
    simpa only [Set.singleton_union] using hgenerate
  let eTop : IntermediateField.adjoin A {r} ≃ₐ[A] E :=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  let pbA : PowerBasis K A := IntermediateField.adjoin.powerBasis hy
  let pbE : PowerBasis A E :=
    (IntermediateField.adjoin.powerBasis hr).map eTop
  letI : FiniteDimensional K A := IntermediateField.adjoin.finiteDimensional hy
  letI : FiniteDimensional A (IntermediateField.adjoin A {r}) :=
    IntermediateField.adjoin.finiteDimensional hr
  letI : FiniteDimensional A E :=
    Module.Finite.of_surjective eTop.toLinearMap eTop.surjective
  letI : FiniteDimensional K E := FiniteDimensional.trans K A E
  have hgenA : pbA.gen = yA := by rfl
  have hgenE : pbE.gen = r := by
    simp only [pbE, PowerBasis.map_gen,
      IntermediateField.adjoin.powerBasis_gen]
    rfl
  have hdim : pbE.dim ≤ P.natDegree + Q.natDegree := by
    have hmin : minpoly A r ∣ Py := minpoly.dvd A r hPyroot
    calc
      pbE.dim = (minpoly A r).natDegree := by
        simpa [hgenE] using pbE.natDegree_minpoly.symm
      _ ≤ Py.natDegree := Polynomial.natDegree_le_of_dvd hmin hPyne
      _ ≤ P.natDegree := Polynomial.natDegree_map_le
      _ ≤ P.natDegree + Q.natDegree := Nat.le_add_right _ _
  refine ⟨inferInstance, ?_⟩
  exact PlaneCharacteristicFreeDegree.finrank_le_resultant_natDegree
    yA r pbA pbE hgenA hgenE P Q P.natDegree Q.natDegree
    le_rfl le_rfl hdim hPyroot hQyroot hresne

end

end ProximityPrize.SubmissionLower.PlaneCharacteristicFreeRoots

#print axioms ProximityPrize.SubmissionLower.PlaneCharacteristicFreeRoots.finite_finrank_le_resultant_natDegree
