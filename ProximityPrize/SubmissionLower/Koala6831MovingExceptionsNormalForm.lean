import ProximityPrize.SubmissionLower.Koala6831MovingExceptions
import ProximityPrize.SubmissionLower.Koala6831MovingNormalizedWords
import ProximityPrize.SubmissionLower.Koala6831PrimitiveDiscard
import ProximityPrize.SubmissionLower.Koala6831SeparationNormalForm

namespace ProximityPrize.SubmissionLower.Koala6831Moving

open Koala6831Comparison (SymbolicRow primitiveSelected)
open Koala6831Separation (NormalForm Seeds pairDegree regroup regroup_C regroup_X)
open Koala6831BivariateSeeds (coordinates)

noncomputable section

variable {K I : Type*} [Field K]

private theorem evaluate_seed_regroup (v : Fin 2 → K) (P : Polynomial (Seeds K)) :
    MvPolynomial.eval (Polynomial.C ∘ v) (regroup P) = P.map (MvPolynomial.eval v) := by
  have hcoeff : (MvPolynomial.eval (Polynomial.C ∘ v)).comp (MvPolynomial.map Polynomial.C) =
      (Polynomial.C : K →+* Polynomial K).comp (MvPolynomial.eval v) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval_C]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.map_X, MvPolynomial.eval_X, Function.comp_apply]
  have h : (MvPolynomial.eval (Polynomial.C ∘ v)).comp regroup =
      Polynomial.mapRingHom (MvPolynomial.eval v) := by
    apply Polynomial.ringHom_ext
    · intro a
      change MvPolynomial.eval (Polynomial.C ∘ v) (regroup (Polynomial.C a)) =
        (Polynomial.C a).map (MvPolynomial.eval v)
      rw [regroup_C, Polynomial.map_C]
      exact DFunLike.congr_fun hcoeff a
    · change MvPolynomial.eval (Polynomial.C ∘ v) (regroup (Polynomial.X : Polynomial (Seeds K))) =
        (Polynomial.X : Polynomial (Seeds K)).map (MvPolynomial.eval v)
      rw [regroup_X, MvPolynomial.eval_C, Polynomial.map_X]
  exact DFunLike.congr_fun h P

def leftFlowData {q : SymbolicRow (Seeds K)} {w delta : ℕ} (N : NormalForm q w delta) :
    FlowData K := ⟨N.d₀, N.A 0, N.A 1, N.C 0, N.C 1⟩

theorem normalForm_specialized_compatibility {q : SymbolicRow (Seeds K)} {w delta : ℕ}
    (N : NormalForm q w delta) (sigma : K →+* K) (p : ℕ)
    (selected : K → Polynomial K) (g : K)
    (hz : primitiveSelected sigma p q selected g = 0) :
    affineDenominator (N.A 0) (N.A 1) g *
      (N.d₁ * (selected g).map sigma - affineDenominator (N.D 0) (N.D 1) (g ^ p)) =
    affineDenominator (N.B 0) (N.B 1) (g ^ p) *
      (N.d₀ * selected g + affineDenominator (N.C 0) (N.C 1) g) := by
  let v := coordinates g (g ^ p)
  let evaluate := MvPolynomial.eval (Polynomial.C ∘ v)
  have hβ := congrArg evaluate N.beta_eq
  have hfirst := congrArg evaluate N.first_eq
  have hsecond := congrArg evaluate N.second_eq
  have hzero : q.beta.map (MvPolynomial.eval v) + q.first.map (MvPolynomial.eval v) * selected g +
      q.second.map (MvPolynomial.eval v) * (selected g).map sigma = 0 := hz
  rw [← evaluate_seed_regroup v q.beta, ← evaluate_seed_regroup v q.first,
    ← evaluate_seed_regroup v q.second] at hzero
  change evaluate (regroup q.beta) + evaluate (regroup q.first) * selected g +
    evaluate (regroup q.second) * (selected g).map sigma = 0 at hzero
  rw [hβ, hfirst, hsecond] at hzero
  simp only [evaluate, Koala6831SeparationFactors.affine, map_add, map_mul, map_neg,
    MvPolynomial.eval_C, MvPolynomial.eval_X,
    Function.comp_apply, v, coordinates, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false] at hzero
  unfold affineDenominator
  linear_combination -hzero

theorem normalForm_exists_retained_normalized_words {q : SymbolicRow (Seeds K)} {w delta : ℕ}
    (N : NormalForm q w delta) (sigma : K →+* K) (p : ℕ) (hdelta : delta < p)
    (nodes : Finset I) (x : I → K) (u₀ u₁ : I → K)
    (hgood : ∀ i ∈ nodes,
      q.atNode (MvPolynomial.C (x i)) (Koala6831SeparationFactors.affine 0 (u₀ i) (u₁ i))
        (Koala6831SeparationFactors.affine 1 (sigma (u₀ i)) (sigma (u₁ i))) = 0)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hselected : ∀ g ∈ seeds, primitiveSelected sigma p q selected g = 0) :
    ∃ retained ⊆ seeds,
      seeds.card ≤ retained.card + (nodes.card + 1 + (p + 1) * delta) ∧
      ∃ fixed : I → K, ∃ normalized : K → Polynomial K,
        (∀ i ∈ nodes, N.d₀.eval (x i) * u₀ i + (N.C 0).eval (x i) = (N.A 0).eval (x i) * fixed i ∧
          N.d₀.eval (x i) * u₁ i + (N.C 1).eval (x i) = (N.A 1).eval (x i) * fixed i) ∧
        ∀ g ∈ retained, (normalized g).natDegree ≤ w + delta ∧
          N.d₀ * selected g + affineDenominator (N.C 0) (N.C 1) g =
            affineDenominator (N.A 0) (N.A 1) g * normalized g ∧
          ∀ i ∈ nodes, (selected g).eval (x i) = u₀ i + g * u₁ i →
            (normalized g).eval (x i) = fixed i := by
  classical
  obtain ⟨retained, hsub, hcard, hden⟩ := exists_retained_affine_seeds nodes x
    (N.A 0) (N.A 1) (N.B 0) (N.B 1) p delta N.A_coprime N.B_coprime
    (by simpa only [pairDegree] using (Nat.le_of_add_left_le N.second_degree))
    (by simpa only [pairDegree] using (Nat.le_of_add_left_le N.first_degree)) hdelta seeds
  let B := leftFlowData N
  have hex (g : ↥retained) : ∃ poly : Polynomial K, poly.natDegree ≤ w + delta ∧
      N.d₀ * selected g.1 + affineDenominator (N.C 0) (N.C 1) g.1 =
        affineDenominator (N.A 0) (N.A 1) g.1 * poly := by
    exact B.exists_normalized_selected_word g.1 (selected g.1)
      (affineDenominator (N.B 0) (N.B 1) (g.1 ^ p))
      (N.d₁ * (selected g.1).map sigma - affineDenominator (N.D 0) (N.D 1) (g.1 ^ p)) w delta
      (hdegree g.1 (hsub g.2)) (Nat.le_of_add_right_le N.first_degree)
      (le_max_left _ _ |>.trans (Nat.le_of_add_left_le N.left_degree))
      (le_max_right _ _ |>.trans (Nat.le_of_add_left_le N.left_degree))
      (hden g.1 g.2).2.1
      (normalForm_specialized_compatibility N sigma p selected g.1 (hselected g.1 (hsub g.2)))
  choose chosen hnormDegree hnormIdentity using hex
  let normalized (g : K) : Polynomial K := if hg : g ∈ retained then chosen ⟨g, hg⟩ else 0
  have hfixed (i : ↥nodes) : ∃ u : K,
      N.d₀.eval (x i.1) * u₀ i.1 + (N.C 0).eval (x i.1) = (N.A 0).eval (x i.1) * u ∧
      N.d₀.eval (x i.1) * u₁ i.1 + (N.C 1).eval (x i.1) = (N.A 1).eval (x i.1) * u := by
    let received : Fin 2 → K := ![u₀ i.1, u₁ i.1]
    obtain ⟨u, hleft, _⟩ := N.fixedWord (x i.1) received (sigma ∘ received) (hgood i.1 i.2)
    exact ⟨u, by simpa [received, mul_comm] using hleft 0, by simpa [received, mul_comm] using hleft 1⟩
  choose chosenValue hvalues using hfixed
  let fixed (i : I) : K := if hi : i ∈ nodes then chosenValue ⟨i, hi⟩ else 0
  have hf i (hi : i ∈ nodes) := hvalues ⟨i, hi⟩
  refine ⟨retained, hsub, hcard, fixed, normalized, ?_, ?_⟩
  · intro i hi
    simpa only [fixed, dif_pos hi] using hf i hi
  · intro g hg
    have hnorm : N.d₀ * selected g + affineDenominator (N.C 0) (N.C 1) g =
        affineDenominator (N.A 0) (N.A 1) g * normalized g := by
      simpa only [normalized, dif_pos hg] using hnormIdentity ⟨g, hg⟩
    refine ⟨by simpa only [normalized, dif_pos hg] using hnormDegree ⟨g, hg⟩, hnorm, ?_⟩
    intro i hi hagree
    have hvalue := hf i hi
    exact B.normalized_agrees_at (selected g) (normalized g) (x i) g (u₀ i) (u₁ i) (fixed i)
      hagree (by simpa only [B, leftFlowData, fixed, dif_pos hi] using hvalue.1)
      (by simpa only [B, leftFlowData, fixed, dif_pos hi] using hvalue.2) ((hden g hg).2.2 i hi) hnorm

end

end ProximityPrize.SubmissionLower.Koala6831Moving
