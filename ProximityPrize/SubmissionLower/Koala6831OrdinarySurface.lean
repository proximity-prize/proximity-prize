import ProximityPrize.SubmissionLower.Koala6831OrdinaryCarrier
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.Ring
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic.LinearCombination
import ProximityPrize.SubmissionLower.Koala6831BivariateSeeds
import ProximityPrize.SubmissionLower.Koala6831CarrierPrime
import ProximityPrize.SubmissionLower.Koala6831OrdinaryIncidence

namespace ProximityPrize.SubmissionLower.Koala6831Ordinary

open RCN136 RCN095 MvPolynomial
open scoped Classical Polynomial BigOperators

variable {K E : Type*} [Field K] [Field E]

private def valueSwap : Fin 3 ≃ Fin 3 := Equiv.swap 0 1

noncomputable def ordinarySurface (φ : K[X] →+* E) :
    Carrier K →+* MvPolynomial (Fin 3) E :=
  (MvPolynomial.renameEquiv E valueSwap).toRingHom.comp (surfaceMap φ)

@[simp] theorem ordinarySurface_C (φ : K[X] →+* E) (a : K) :
    ordinarySurface φ (MvPolynomial.C a) = MvPolynomial.C (φ (Polynomial.C a)) := by
  simp [ordinarySurface, MvPolynomial.renameEquiv_apply]

@[simp] theorem ordinarySurface_value (φ : K[X] →+* E) :
    ordinarySurface φ (MvPolynomial.X 1) = MvPolynomial.X 1 := by
  change (MvPolynomial.renameEquiv E valueSwap) (surfaceMap φ
    (MvPolynomial.X (Fin.succ (0 : Fin 3)))) = _
  rw [surfaceMap_X_succ]
  simp [MvPolynomial.renameEquiv_apply, valueSwap]

theorem ordinarySurface_injective (φ : K[X] →+* E) (hφ : Function.Injective φ) :
    Function.Injective (ordinarySurface φ) :=
  (MvPolynomial.renameEquiv E valueSwap).injective.comp (surfaceMap_injective φ hφ)

noncomputable def ordinaryPoint (φ : K[X] →+* E) (selected : K → K[X]) (p : ℕ) (g : K) :
    Fin 3 → E := ![φ (Polynomial.C g), φ (selected g), φ (Polynomial.C (g ^ p))]

theorem ordinaryPoint_injective (φ : K[X] →+* E) (hφ : Function.Injective φ)
    (selected : K → K[X]) (p : ℕ) : Function.Injective (ordinaryPoint φ selected p) := by
  intro g h heq
  apply Polynomial.C_injective
  apply hφ
  exact congrFun heq (0 : Fin 3)

theorem eval_ordinarySurface (φ : K[X] →+* E) (selected : K → K[X]) (p : ℕ) (g : K)
    (F : Carrier K) :
    MvPolynomial.eval (ordinaryPoint φ selected p g) (ordinarySurface φ F) =
      φ (MvPolynomial.aeval
        ![Polynomial.X, selected g, Polynomial.C g, Polynomial.C (g ^ p)] F) := by
  change MvPolynomial.eval (ordinaryPoint φ selected p g)
    (MvPolynomial.renameEquiv E valueSwap (surfaceMap φ F)) = _
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename, eval_surfaceMap]
  let v : Fin 4 → K[X] := ![Polynomial.X, selected g, Polynomial.C g, Polynomial.C (g ^ p)]
  have hcoords : Fin.cases (φ Polynomial.X) (ordinaryPoint φ selected p g ∘ valueSwap) =
      fun i ↦ φ (v i) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · change ordinaryPoint φ selected p g (valueSwap j) = φ (v j.succ)
      fin_cases j <;> rfl
  have heval : MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
       (Fin.cases (φ Polynomial.X) (ordinaryPoint φ selected p g ∘ valueSwap)) =
       φ.comp (MvPolynomial.aeval v).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp [hcoords]
  exact RingHom.congr_fun heval F

theorem ordinarySurface_degree_caps (φ : K[X] →+* E) (F : Carrier K) (y t : ℕ)
    (hcap : ∀ d ∈ F.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ t) :
    (ordinarySurface φ F).degreeOf 1 ≤ y ∧ (ordinarySurface φ F).totalDegree ≤ t := by
  constructor
  · change (MvPolynomial.renameEquiv E valueSwap (surfaceMap φ F)).degreeOf 1 ≤ y
    rw [MvPolynomial.renameEquiv_apply, ← show valueSwap (0 : Fin 3) = 1 by simp [valueSwap],
      MvPolynomial.degreeOf_rename_of_injective valueSwap.injective]
    apply (surfaceMap_degreeOf_le φ F 0).trans
    exact MvPolynomial.degreeOf_le_iff.mpr (fun d hd ↦ (hcap d hd).1)
  · change (MvPolynomial.renameEquiv E valueSwap (surfaceMap φ F)).totalDegree ≤ t
    rw [MvPolynomial.totalDegree_renameEquiv]
    apply Finset.sup_le
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (support_surfaceMap_subset φ F he)
    rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
    simpa [Finsupp.tail_apply, Fin.sum_univ_succ, Nat.add_assoc] using (hcap d hd).2

end ProximityPrize.SubmissionLower.Koala6831Ordinary
