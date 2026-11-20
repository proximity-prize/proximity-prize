/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833FactorResultant
import ArkLib.Data.Polynomial.Differential.JetDegree

namespace KoalaFactorResultant
open ProximityPrize.SubmissionLower RCN082 RCN136
open MvPolynomial PolynomialDifferential
noncomputable section
set_option maxHeartbeats 3000000
variable {F E : Type*} [Field F] [Field E]

def twoSlot : Fin 4 → JetVariable 2 := ![none,some 0,some 2,some 1]
def oneSlot : JetVariable 1 → Fin 4
  | none => 0
  | some i => ![1,3] i

theorem twoSlot_injective : Function.Injective twoSlot := by decide +kernel
theorem oneSlot_injective : Function.Injective oneSlot := by decide +kernel

theorem twoWeight (H : MvPolynomial (Fin 4) F) :
    jetTotalDegree (rename twoSlot H) = weightedTotalDegree weights H := by
  unfold jetTotalDegree
  rw [weightedTotalDegree_rename_of_injective twoSlot_injective]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem twoDegree (H : MvPolynomial (Fin 4) F) :
    jetDegree (rename twoSlot H) 2 = H.degreeOf 2 :=
  degreeOf_rename_of_injective twoSlot_injective 2

theorem twoSeparant (H : MvPolynomial (Fin 4) F) :
    separant (rename twoSlot H) 2 = rename twoSlot (pderiv 2 H) :=
  pderiv_rename twoSlot_injective 2 H

def coords (φ : Polynomial F →+* E) (P : Polynomial F) : Fin 3 → E :=
  ![φ P,φ (Polynomial.hasseDeriv 2 P),φ (Polynomial.hasseDeriv 1 P)]

theorem evaluation_two (φ : Polynomial F →+* E) (P : Polynomial F) (H : MvPolynomial (Fin 4) F) :
    eval (coords φ P) (surfaceMap φ H) = φ (differentialSpecialization (rename twoSlot H) P) := by
  induction H using MvPolynomial.induction_on with
  | C c => simp [differentialSpecialization,differentialSpecializationHom]
  | add a b ha hb =>
    simpa only [differentialSpecialization,map_add] using congrArg₂ (·+·) ha hb
  | mul_X a i ha =>
    simp only [map_mul, rename_X, differentialSpecialization, map_mul] at ha ⊢
    congr 1
    fin_cases i
    · change eval (coords φ P) (surfaceMap φ (MvPolynomial.X (0 : Fin 4))) = φ (differentialSpecialization (MvPolynomial.X none : DifferentialPolynomial F 2) P)
      rw [surfaceMap_X_zero, eval_C]
      change φ Polynomial.X = φ (differentialSpecialization (MvPolynomial.X none : DifferentialPolynomial F 2) P)
      rw [differentialSpecialization_x]
    · change eval (coords φ P) (surfaceMap φ (MvPolynomial.X (0 : Fin 3).succ)) = φ (differentialSpecialization (MvPolynomial.X (some 0) : DifferentialPolynomial F 2) P)
      rw [surfaceMap_X_succ, eval_X]
      change φ P = φ (differentialSpecialization (MvPolynomial.X (some 0) : DifferentialPolynomial F 2) P)
      rw [differentialSpecialization_jet]
      change φ P = φ ((Polynomial.hasseDeriv 0) P)
      rw [Polynomial.hasseDeriv_zero,LinearMap.id_apply]
    · change eval (coords φ P) (surfaceMap φ (MvPolynomial.X (1 : Fin 3).succ)) = φ (differentialSpecialization (MvPolynomial.X (some 2) : DifferentialPolynomial F 2) P)
      rw [surfaceMap_X_succ, eval_X]
      change φ _ = φ (differentialSpecialization (MvPolynomial.X (some 2) : DifferentialPolynomial F 2) P)
      rw [differentialSpecialization_jet]
      rfl
    · change eval (coords φ P) (surfaceMap φ (MvPolynomial.X (2 : Fin 3).succ)) = φ (differentialSpecialization (MvPolynomial.X (some 1) : DifferentialPolynomial F 2) P)
      rw [surfaceMap_X_succ, eval_X]
      change φ _ = φ (differentialSpecialization (MvPolynomial.X (some 1) : DifferentialPolynomial F 2) P)
      rw [differentialSpecialization_jet]
      rfl

theorem onePresentation (S : MvPolynomial (Fin 4) F) (hT : S.degreeOf 2 = 0) :
    ∃ B : DifferentialPolynomial F 1, rename oneSlot B = S := by
  apply exists_rename_eq_of_vars_subset_range S oneSlot oneSlot_injective
  intro i hi
  have hn : i ≠ 2 := by
    rintro rfl
    exact (mem_vars_iff_degreeOf_ne_zero.mp hi) hT
  fin_cases i
  · exact ⟨none,rfl⟩
  · exact ⟨some 0,rfl⟩
  · exact False.elim (hn rfl)
  · exact ⟨some 1,rfl⟩

theorem oneWeight (B : DifferentialPolynomial F 1) :
    weightedTotalDegree weights (rename oneSlot B) = jetTotalDegree B := by
  rw [weightedTotalDegree_rename_of_injective oneSlot_injective]
  unfold jetTotalDegree
  congr 1
  funext i
  cases i with
  | none => rfl
  | some j => fin_cases j <;> rfl

theorem evaluation_one (P : Polynomial F) (B : DifferentialPolynomial F 1) :
    differentialSpecialization (rename twoSlot (rename oneSlot B)) P =
    differentialSpecialization B P := by
  induction B using MvPolynomial.induction_on with
  | C c => simp [differentialSpecialization,differentialSpecializationHom]
  | add a b ha hb =>
    simpa only [differentialSpecialization,map_add] using congrArg₂ (·+·) ha hb
  | mul_X a i ha =>
    simp only [map_mul, rename_X, differentialSpecialization, map_mul] at ha ⊢
    congr 1
    cases i with
    | none => simp [oneSlot,twoSlot,differentialSpecializationHom]
    | some j => fin_cases j <;> simp [oneSlot,twoSlot,differentialSpecializationHom]

#print axioms evaluation_two
#print axioms evaluation_one
end
end KoalaFactorResultant
