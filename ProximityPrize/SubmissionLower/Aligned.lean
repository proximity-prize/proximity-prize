/- Apache-2.0. Bome2017. Reuse of the nondivisible-determinant invariant and
   twisted row from Bome2017's 69.69 research after Lucieno and BitWonka. -/
import ProximityPrize.SubmissionLower.Mid6833GenuineResidual
namespace KoalaNight.Aligned
open Polynomial ProximityPrize.SubmissionLower
open Koala6831Separation Frontier6969.GenuineMoving
open scoped Polynomial Classical
set_option autoImplicit false
variable {K : Type} [Field K]

/-- An aligned primitive left direction can always be used in the physical flow.
The degree of the conjugated left pair agrees with its original degree. -/
theorem left_degree (σ : K →+* K) (A B : Fin 2 → K[X])
    (cpA : IsCoprime (A 0) (A 1)) (cpB : IsCoprime (B 0) (B 1))
    (aligned : twist σ A B = 0) : pairDegree A ≤ pairDegree B := by
  let a := (A 0).map σ
  let b := (A 1).map σ
  have cross : a * B 1 = b * B 0 := sub_eq_zero.mp aligned
  have cp : IsCoprime a b := cpA.map (Polynomial.mapRingHom σ)
  obtain ⟨u,v,unit⟩ := cp
  let k := u * B 0 + v * B 1
  have z : B 0 = k*a := by
    dsimp only [k]
    linear_combination -B 0*unit - v*cross
  have o : B 1 = k*b := by
    dsimp only [k]
    linear_combination -B 1*unit + u*cross
  have nk : k≠0 := by
    intro n
    obtain ⟨c,d,eqn⟩ := cpB
    rw [z,o,n] at eqn
    simpa using eqn
  have deg (P : K[X]) : P.natDegree ≤ (k * P).natDegree := by
    by_cases nz : P = 0
    · simp [nz]
    rw [natDegree_mul nk nz]
    omega
  have zeroD : (A 0).natDegree ≤ (B 0).natDegree := by
    rw [z]
    simpa only [a,Polynomial.natDegree_map] using deg a
  have oneD : (A 1).natDegree ≤ (B 1).natDegree := by
    rw [o]
    simpa only [b,Polynomial.natDegree_map] using deg b
  exact max_le_max zeroD oneD

theorem seeds_le_word_list (S : Finset K) (d a₀ a₁ c₀ c₁ : K[X])
    (P T : K → K[X]) (nondiv : ¬ d ∣ a₀*c₁-a₁*c₀)
    (row : ∀ g∈S, d*P g+(c₀+C g*c₁)=(a₀+C g*a₁)*T g)
    (L : ℕ) (words : (S.image T).card≤L) : S.card≤L := by
  classical
  have inj := Frontier6969.Moving.injective S d a₀ a₁ c₀ c₁ P T nondiv row
  have on : Set.InjOn T (↑S) := by
    intro g hg h hh eq
    have same : (⟨g,hg⟩ : ↥S) = ⟨h,hh⟩ := inj eq
    exact congrArg Subtype.val same
  rwa [Finset.card_image_of_injOn on] at words
#print axioms left_degree
#print axioms seeds_le_word_list
end KoalaNight.Aligned
