import ProximityPrize.SubmissionLower.Koala6831RankFour
import ProximityPrize.SubmissionLower.Koala6831SeparationCoordinates
import ProximityPrize.SubmissionLower.Koala6831SeparationRank
import Mathlib.RingTheory.Localization.FractionRing

namespace ProximityPrize.SubmissionLower.Koala6831Separation

open Polynomial
open Koala6831Comparison (SymbolicRow)
open Koala6831CoefficientSystem (coefficientPolynomial matrix_node_equation)
open scoped BigOperators Matrix Polynomial

set_option maxHeartbeats 1600000

variable {K I : Type*} [Field K]

abbrev NodeField (K : Type*) [Field K] := FractionRing K[X]

noncomputable def asRational : (Seeds K)[X] →+* Seeds (NodeField K) :=
  (MvPolynomial.map (algebraMap K[X] (NodeField K))).comp regroup

theorem asRational_injective : Function.Injective (asRational (K := K)) :=
  (MvPolynomial.map_injective _ (IsFractionRing.injective _ _)).comp regroup_injective

private theorem columns_degree (q : SymbolicRow (Seeds K)) (δ : ℕ)
    (hfirst : q.first.natDegree ≤ δ) (hsecond : q.second.natDegree ≤ δ) :
    ∀ j, (Koala6831RankFour.columns q j).natDegree ≤ δ := by
  intro j
  fin_cases j
  · exact hfirst
  · exact (Polynomial.natDegree_C_mul_le _ _).trans hfirst
  · exact hsecond
  · exact (Polynomial.natDegree_C_mul_le _ _).trans hsecond

private theorem columns_asRational (q : SymbolicRow (Seeds K)) (j : Fin 4) :
    asRational (Koala6831RankFour.columns q j) =
      seedColumns (asRational q.first) (asRational q.second) j := by
  have hX (i : Fin 2) :
      asRational (Polynomial.C (MvPolynomial.X i : Seeds K)) = MvPolynomial.X i := by
    simp [asRational]
  fin_cases j
  · rfl
  · change asRational (Polynomial.C (MvPolynomial.X 0) * q.first) = _
    rw [map_mul, hX]
    rfl
  · rfl
  · change asRational (Polynomial.C (MvPolynomial.X 1) * q.second) = _
    rw [map_mul, hX]
    rfl

private theorem coeff_asRational (P : (Seeds K)[X]) (key : Fin 2 →₀ ℕ) (cap : ℕ)
    (hP : P.natDegree ≤ cap) :
    (asRational P).coeff key = algebraMap K[X] (NodeField K) (coefficientPolynomial P key cap) := by
  change (MvPolynomial.map (algebraMap K[X] (NodeField K)) (regroup P)).coeff key = _
  rw [MvPolynomial.coeff_map, coeff_regroup_eq _ _ _ hP]

theorem rational_relation_and_span (domain : I ↪ K) (nodes : Finset I)
    (q : SymbolicRow (Seeds K)) (word : I → Fin 4 → K) (w δ : ℕ)
    (hfirst0 : q.first ≠ 0) (hsecond0 : q.second ≠ 0)
    (hfirst : q.first.natDegree ≤ δ) (hsecond : q.second.natDegree ≤ δ)
    (hbeta : q.beta.natDegree ≤ w + δ) (hcard : w + 4 * δ < nodes.card)
    (hgood : ∀ i ∈ nodes,
      q.atNode (MvPolynomial.C (domain i))
        (MvPolynomial.C (word i 0) + MvPolynomial.X 0 * MvPolynomial.C (word i 1))
        (MvPolynomial.C (word i 2) + MvPolynomial.X 1 * MvPolynomial.C (word i 3)) = 0)
    (hsingular : ∀ keys : Fin 4 → (Fin 2 →₀ ℕ), (Koala6831RankFour.matrix q keys δ).det = 0) :
    let cols := seedColumns (asRational q.first) (asRational q.second)
    (∃ v : Fin 4 → NodeField K, v ≠ 0 ∧ ∑ j, v j • cols j = 0) ∧
      asRational q.beta ∈ Submodule.span (NodeField K) (Set.range cols) := by
  classical
  let φ := algebraMap K[X] (NodeField K)
  let cols := seedColumns (asRational q.first) (asRational q.second)
  let cs := coefficients ∘ cols
  have hcols := columns_degree q δ hfirst hsecond
  have hentry (j : Fin 4) (key : Fin 2 →₀ ℕ) :
      cs j key = φ (coefficientPolynomial (Koala6831RankFour.columns q j) key δ) := by
    change (seedColumns (asRational q.first) (asRational q.second) j).coeff key = _
    rw [← columns_asRational q j, coeff_asRational _ _ _ (hcols j)]
  have hneg : (-q.beta).natDegree ≤ w + δ := by simpa using hbeta
  let rhs := coefficients (asRational (-q.beta))
  have hr (key : Fin 2 →₀ ℕ) :
      rhs key = φ (coefficientPolynomial (-q.beta) key (w + δ)) :=
    coeff_asRational _ _ _ hneg
  have hm (keys : Fin 4 → (Fin 2 →₀ ℕ)) :
      φ.mapMatrix (Koala6831RankFour.matrix q keys δ) =
        Matrix.of (fun i j ↦ cs j (keys i)) := by
    ext i j
    exact (hentry j (keys i)).symm
  have hcs (keys : Fin 4 → (Fin 2 →₀ ℕ)) :
      (Matrix.of fun i j ↦ cs j (keys i)).det = 0 := by
    rw [← hm, ← RingHom.map_det, hsingular keys, map_zero]
  have haug (keys : Fin 4 → (Fin 2 →₀ ℕ)) (slot : Fin 4) :
      ((Matrix.of fun i j ↦ cs j (keys i)).updateCol slot (fun i ↦ rhs (keys i))).det = 0 := by
    let right (i : Fin 4) := coefficientPolynomial (-q.beta) (keys i) (w + δ)
    have haug0 : ((Koala6831RankFour.matrix q keys δ).updateCol slot right).det = 0 := by
      apply Koala6831Cramer.augmented_minor_eq_zero domain nodes _ right word w δ slot
        (hsingular keys)
      · exact fun _ _ ↦ Koala6831CoefficientSystem.coefficientPolynomial_degree _ _ _
      · exact fun _ ↦ Koala6831CoefficientSystem.coefficientPolynomial_degree _ _ _
      · exact hcard
      · intro i hi
        exact matrix_node_equation (Koala6831RankFour.columns q) (-q.beta) keys w δ (domain i)
          (word i) hcols hneg (Koala6831RankFour.equation_of_good_node q (domain i) (word i)
            (hgood i hi))
    have he : φ.mapMatrix ((Koala6831RankFour.matrix q keys δ).updateCol slot right) =
        (Matrix.of fun i j ↦ cs j (keys i)).updateCol slot (fun i ↦ rhs (keys i)) := by
      rw [RingHom.mapMatrix_apply, Matrix.map_updateCol, ← RingHom.mapMatrix_apply, hm]
      congr 1
      funext i
      exact (hr (keys i)).symm
    rw [← he, ← RingHom.map_det, haug0, map_zero]
  obtain ⟨v, hv, hsum⟩ := exists_relation_of_singular_minors cs hcs
  have hvsum : ∑ j, v j • cols j = 0 := by
    apply coefficients_injective
    simpa only [map_sum, map_smul, map_zero, cs, Function.comp_apply] using hsum
  have hn₀ : asRational q.first ≠ 0 :=
    fun he ↦ hfirst0 (asRational_injective (he.trans (map_zero _).symm))
  have hn₁ : asRational q.second ≠ 0 :=
    fun he ↦ hsecond0 (asRational_injective (he.trans (map_zero _).symm))
  obtain ⟨slot, hslot⟩ := exists_independent_triple hn₀ hn₁
  have hslot' : LinearIndependent (NodeField K) (cs ∘ slot.succAbove) :=
    hslot.map' coefficients (LinearMap.ker_eq_bot.mpr coefficients_injective)
  have hmem := mem_span_of_singular_augmented_minors cs rhs slot hslot'
    (fun keys ↦ haug keys slot)
  have hmem' : rhs ∈ (Submodule.span (NodeField K) (Set.range (cols ∘ slot.succAbove))).map
      coefficients := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact hmem
  obtain ⟨z, hz, he⟩ := hmem'
  have hz' : z = asRational (-q.beta) := coefficients_injective he
  have hmFull : asRational (-q.beta) ∈ Submodule.span (NodeField K) (Set.range cols) := by
    rw [← hz']
    apply Submodule.span_mono _ hz
    rintro y ⟨j, rfl⟩
    exact ⟨slot.succAbove j, rfl⟩
  exact ⟨⟨v, hv, hvsum⟩, by simpa only [map_neg, neg_neg] using Submodule.neg_mem _ hmFull⟩

end ProximityPrize.SubmissionLower.Koala6831Separation
