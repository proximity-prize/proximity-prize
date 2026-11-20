import ProximityPrize.SubmissionLower.Koala6844VirtualHighLiteralSum
import ProximityPrize.SubmissionLower.Koala6844VirtualHighPowerEnvelope
import ProximityPrize.SubmissionLower.Koala6844VirtualHighProperCut
import ProximityPrize.SubmissionLower.Koala6844VirtualHighBounds


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open scoped Classical BigOperators
open RCN001 RCN007 RCN264 RCN271 RCN341

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

def rectangleCoordinate (r : Rectangle) : Fin 3 → ℕ :=
  ![r.value, r.first, r.second]

private def complementaryRectangleDegree (f g : Rectangle) : Fin 3 → ℕ :=
  ![g.first * f.second + f.first * g.second,
    g.value * f.second + f.value * g.second,
    g.value * f.first + f.value * g.first]

private theorem sum_complementaryRectangleDegree (f g h : Rectangle) :
    (∑ i, rectangleCoordinate h i * complementaryRectangleDegree f g i) =
      mixedDegree f g h := by
  rw [Fin.sum_univ_three]
  change h.value * (g.first * f.second + f.first * g.second) +
    h.first * (g.value * f.second + f.value * g.second) +
    h.second * (g.value * f.first + f.value * g.first) = _
  unfold mixedDegree
  ring

variable {Ω A : Type} [Field Ω] [IsAlgClosed Ω] [Fintype A]
variable {G T H : MvPolynomial (Fin 3) Ω}

private theorem mixedCoordinate_le_rectangle
    (surface firstTail : Rectangle)
    (surfaceCap : ∀ i, G.degreeOf i ≤ rectangleCoordinate surface i)
    (firstCap : ∀ i, T.degreeOf i ≤ rectangleCoordinate firstTail i)
    (i : Fin 3) :
    coordinateMixedDegree Ω G T i ≤ complementaryRectangleDegree surface firstTail i := by
  fin_cases i
  · simpa [rectangleCoordinate, complementaryRectangleDegree] using
      Nat.add_le_add (Nat.mul_le_mul (firstCap 1) (surfaceCap 2))
        (Nat.mul_le_mul (surfaceCap 1) (firstCap 2))
  · simpa [rectangleCoordinate, complementaryRectangleDegree] using
      Nat.add_le_add (Nat.mul_le_mul (firstCap 0) (surfaceCap 2))
        (Nat.mul_le_mul (surfaceCap 0) (firstCap 2))
  · simpa [rectangleCoordinate, complementaryRectangleDegree] using
      Nat.add_le_add (Nat.mul_le_mul (firstCap 0) (surfaceCap 1))
        (Nat.mul_le_mul (surfaceCap 0) (firstCap 1))

theorem sum_residual_curve_counts_le_mixedDegree
    (component : A → RegularComponent Ω G T H) (hinj : Function.Injective component)
    (μ : A → ℕ) (positive : ∀ a, 1 ≤ μ a)
    (primary : ∀ a, ∃ s ∉ (component a).1,
      s * T ∈ Ideal.span {G} ⊔ (component a).1 ^ μ a)
    (hG : Irreducible G) (hproper : ¬ G ∣ T)
    (surface firstTail laterTail : Rectangle)
    (surfaceCap : ∀ i, G.degreeOf i ≤ rectangleCoordinate surface i)
    (firstCap : ∀ i, T.degreeOf i ≤ rectangleCoordinate firstTail i)
    (count : A → ℕ)
    (localCount : ∀ a, count a ≤ ∑ i, (μ a * rectangleCoordinate laterTail i) *
      actualCoordinateDegree Ω (component a).1 i) :
    (∑ a, count a) ≤ mixedDegree surface firstTail laterTail := by
  rw [← sum_complementaryRectangleDegree]
  apply sum_regular_counts_le_rectangular count μ (rectangleCoordinate laterTail)
    (complementaryRectangleDegree surface firstTail)
    (fun a i => actualCoordinateDegree Ω (component a).1 i) localCount
  intro i
  exact (sum_weighted_literal_degree_le component hinj μ positive primary hG hproper i).trans
    (mixedCoordinate_le_rectangle surface firstTail surfaceCap firstCap i)


end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

