/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833FrobeniusModule
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Roots

namespace KoalaFrontier
open Finset Polynomial
open scoped BigOperators Polynomial
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Finite equal-size witnesses with uniformly bounded intersections. -/
theorem witness_second_moment [DecidableEq I] (E : J → Finset I) (A D : ℕ)
    (weights : ∀ j, (E j).card = A)
    (overlaps : ∀ j k, j ≠ k → ((E j) ∩ (E k)).card ≤ D) :
    (Fintype.card J * A)^2 ≤ Fintype.card I *
      (Fintype.card J*A + Fintype.card J*(Fintype.card J-1)*D) := by
  classical
  let u (j : J) (i : I) : ℕ := if i∈E j then 1 else 0
  let c (i : I) := ∑ j, u j i
  have su j : ∑ i, u j i = A := by simp [u,weights]
  have sc : ∑ i, c i = Fintype.card J*A := by
    simp only [c]
    rw [Finset.sum_comm]
    simp [su]
  have uv j k : ∑ i, u j i*u k i = (E j∩E k).card := by
    calc
      _ = ∑ i : I, if i∈(E j∩E k) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases a : i∈E j <;> by_cases b : i∈E k <;> simp [u,a,b]
      _ = _ := by
        rw [← Finset.card_filter]
        congr 1
        ext i
        simp
  have allpairs : ∑ i, c i ^ 2 = ∑ j, ∑ k, (E j∩E k).card := by
    calc
      _ = ∑ i, ∑ j, ∑ k, u j i * u k i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_two,show c i = ∑ j, u j i from rfl,Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
      _ = ∑ j, ∑ k, ∑ i, u j i * u k i := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := by simp only [uv]
  have rowbound j : ∑ k, (E j∩E k).card ≤ A+(Fintype.card J-1)*D := by
    calc
      _ = ∑ k ∈ Finset.univ.erase j, (E j∩E k).card + (E j∩E j).card :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
      _ ≤ ∑ _k ∈ Finset.univ.erase j, D + A := by
        gcongr
        · exact overlaps _ _ (Finset.ne_of_mem_erase ‹_›).symm
        · simp [weights]
      _ = _ := by simp [Nat.add_comm]
  have cauchy := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset I)) (f := c)
  rw [sc,allpairs] at cauchy
  refine cauchy.trans (Nat.mul_le_mul_left _ ?_)
  have b := Finset.sum_le_sum (s := (Finset.univ : Finset J)) (fun j _ => rowbound j)
  simpa [Nat.mul_add,Nat.mul_assoc] using b

/-- Each distinct quotient word has A agreements, the evaluation map is injective,
    and quotients have degree at most D. This is the usual Johnson inequality. -/
theorem polynomial_witness_bound {K : Type*} [Field K] (x : I ↪ K) (T : J → K[X])
    (inj : Function.Injective T) (W : I → K) (A D : ℕ)
    (hd : ∀ j, (T j).natDegree ≤ D)
    (good : ∀ j, ∃ E : Finset I, A ≤ E.card ∧ ∀ i∈E, (T j).eval (x i) = W i) :
    (Fintype.card J * A)^2 ≤ Fintype.card I *
      (Fintype.card J*A + Fintype.card J*(Fintype.card J-1)*D) := by
  classical
  choose E cap ev using good
  choose S sub sz using fun j => exists_subset_card_eq (cap j)
  apply witness_second_moment S A D sz
  intro j k ne
  have nz : T j-T k≠0 := sub_ne_zero.mpr (inj.ne ne)
  have b : ((S j∩S k).image x).card ≤ (T j-T k).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a,b⟩ := Finset.mem_inter.mp hi
    apply (Polynomial.mem_roots nz).mpr
    simp [Polynomial.IsRoot,ev j i (sub j a),ev k i (sub k b)]
  rw [Finset.card_image_of_injective _ x.injective] at b
  exact b.trans ((natDegree_sub_le _ _).trans (max_le (hd j) (hd k)))

#print axioms witness_second_moment
#print axioms polynomial_witness_bound
end KoalaFrontier
