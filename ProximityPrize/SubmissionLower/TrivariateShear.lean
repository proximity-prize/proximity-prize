import ProximityPrize.Benchmark.TargetLower
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace ProximityPrize.SubmissionLower.TrivariateShear

open scoped Classical BigOperators

noncomputable section

variable {K : Type} [Field K]

local instance : DecidableEq K := Classical.decEq K

abbrev Poly3 (K : Type) [Field K] := MvPolynomial (Fin 3) K

section WeightedDegree

def weightEmbed (weights : Fin 3 → ℕ) : (Fin 3 →₀ ℕ) →+ (Fin 4 →₀ ℕ) where
  toFun d := Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
    Finsupp.single 2 (d 2) + Finsupp.single 3 (Finsupp.weight weights d)
  map_zero' := by simp
  map_add' d e := by
    ext i
    fin_cases i <;> simp [Finsupp.add_apply, map_add]

theorem weightEmbed_castSucc (weights : Fin 3 → ℕ) (d : Fin 3 →₀ ℕ) (i : Fin 3) :
    weightEmbed weights d i.castSucc = d i := by
  fin_cases i <;> simp [weightEmbed]

theorem weightEmbed_last (weights : Fin 3 → ℕ) (d : Fin 3 →₀ ℕ) :
    weightEmbed weights d (3 : Fin 4) = Finsupp.weight weights d := by
  simp [weightEmbed]

theorem weightEmbed_injective (weights : Fin 3 → ℕ) :
    Function.Injective (weightEmbed weights) := by
  intro d e h
  ext i
  have hi := congrArg (fun b : Fin 4 →₀ ℕ ↦ b i.castSucc) h
  simpa only [weightEmbed_castSucc] using hi

def weightedLift (weights : Fin 3 → ℕ) : Poly3 K →+* MvPolynomial (Fin 4) K :=
  AddMonoidAlgebra.mapDomainRingHom K (weightEmbed weights)

theorem support_weightedLift (weights : Fin 3 → ℕ) (F : Poly3 K) :
    (weightedLift weights F).support = F.support.image (weightEmbed weights) := by
  change (Finsupp.mapDomain (weightEmbed weights) (AddMonoidAlgebra.coeff F)).support =
    Finset.image (weightEmbed weights) (AddMonoidAlgebra.coeff F).support
  exact Finsupp.mapDomain_support_of_injective (weightEmbed_injective weights) _

theorem degree_weightedLift (weights : Fin 3 → ℕ) (F : Poly3 K) :
    (weightedLift weights F).degreeOf (3 : Fin 4) =
      MvPolynomial.weightedTotalDegree weights F := by
  change (weightedLift weights F).degreeOf (3 : Fin 4) =
    F.support.sup (Finsupp.weight weights)
  rw [MvPolynomial.degreeOf_eq_sup, support_weightedLift, Finset.sup_image]
  apply congrArg (fun f : (Fin 3 →₀ ℕ) → ℕ ↦ F.support.sup f)
  funext d
  exact weightEmbed_last weights d

def wt (weights : Fin 3 → ℕ) (F : Poly3 K) : ℕ :=
  MvPolynomial.weightedTotalDegree weights F

theorem wt_mul_le (weights : Fin 3 → ℕ) (F G : Poly3 K) :
    wt weights (F * G) ≤ wt weights F + wt weights G := by
  unfold wt
  rw [← degree_weightedLift, map_mul]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_mul_le (3 : Fin 4)
      (weightedLift weights F) (weightedLift weights G)

theorem wt_sub_le (weights : Fin 3 → ℕ) (F G : Poly3 K) :
    wt weights (F - G) ≤ max (wt weights F) (wt weights G) := by
  unfold wt
  rw [← degree_weightedLift, map_sub]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_sub_le (3 : Fin 4)
      (weightedLift weights F) (weightedLift weights G)

theorem wt_pow_le (weights : Fin 3 → ℕ) (F : Poly3 K) (n : ℕ) :
    wt weights (F ^ n) ≤ n * wt weights F := by
  unfold wt
  rw [← degree_weightedLift, map_pow]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_pow_le (3 : Fin 4) (weightedLift weights F) n

theorem wt_C (weights : Fin 3 → ℕ) (c : K) :
    wt weights (MvPolynomial.C c : Poly3 K) = 0 := by
  unfold wt MvPolynomial.weightedTotalDegree
  simp

theorem wt_X (weights : Fin 3 → ℕ) (i : Fin 3) :
    wt weights (MvPolynomial.X i : Poly3 K) = weights i := by
  unfold wt MvPolynomial.weightedTotalDegree
  simp [MvPolynomial.support_X, Finsupp.weight_single]

theorem wt_finset_prod_le_sum {ι : Type*} [DecidableEq ι]
    (weights : Fin 3 → ℕ) (I : Finset ι) (f : ι → Poly3 K) :
    wt weights (∏ i ∈ I, f i) ≤ ∑ i ∈ I, wt weights (f i) := by
  induction I using Finset.induction_on with
  | empty => simp [wt, MvPolynomial.weightedTotalDegree]
  | @insert i I hi ih =>
      simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      exact (wt_mul_le weights (f i) (∏ j ∈ I, f j)).trans
        (Nat.add_le_add le_rfl ih)

theorem wt_finset_sum_le {ι : Type*} [DecidableEq ι]
    (weights : Fin 3 → ℕ) (I : Finset ι) (f : ι → Poly3 K) (cap : ℕ)
    (hf : ∀ i ∈ I, wt weights (f i) ≤ cap) :
    wt weights (∑ i ∈ I, f i) ≤ cap := by
  unfold wt
  rw [← degree_weightedLift, map_sum]
  apply (MvPolynomial.degreeOf_sum_le (3 : Fin 4) I
    (fun i ↦ weightedLift weights (f i))).trans
  apply Finset.sup_le
  intro i hi
  rw [degree_weightedLift]
  exact hf i hi

theorem weight_fin3 (weights : Fin 3 → ℕ) (d : Fin 3 →₀ ℕ) :
    Finsupp.weight weights d =
      d 0 * weights 0 + d 1 * weights 1 + d 2 * weights 2 := by
  have hd : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
      Finsupp.single 2 (d 2) := by
    ext i
    fin_cases i <;> simp
  rw [hd, map_add, map_add]
  simp [Finsupp.weight_single, Nat.mul_comm]

end WeightedDegree

end

end ProximityPrize.SubmissionLower.TrivariateShear
