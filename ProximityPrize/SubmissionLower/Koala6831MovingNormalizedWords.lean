import ProximityPrize.SubmissionLower.Koala6831MovingDerivation
import ProximityPrize.SubmissionLower.Koala6831Cramer

namespace ProximityPrize.SubmissionLower.Koala6831Moving

open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K

def FlowData.seedDenominator (B : FlowData K) (g : K) : Polynomial K :=
  B.a0 + Polynomial.C g * B.a1

def FlowData.seedOffset (B : FlowData K) (g : K) : Polynomial K :=
  B.c0 + Polynomial.C g * B.c1

theorem FlowData.exists_normalized_selected_word (B : FlowData K)
    (g : K) (P otherDen otherNumerator : Polynomial K) (w δ : ℕ)
    (hdegree : P.natDegree ≤ w) (hcontent : B.d0.natDegree ≤ δ)
    (hc₀ : B.c0.natDegree ≤ w + δ) (hc₁ : B.c1.natDegree ≤ w + δ)
    (hcoprime : IsRelPrime (B.seedDenominator g) otherDen)
    (hcompat : B.seedDenominator g * otherNumerator =
      otherDen * (B.d0 * P + B.seedOffset g)) :
    ∃ Q : Polynomial K, Q.natDegree ≤ w + δ ∧
      B.d0 * P + B.seedOffset g = B.seedDenominator g * Q := by
  let numerator := B.d0 * P + B.seedOffset g
  have hdiv : B.seedDenominator g ∣ numerator :=
    hcoprime.dvd_of_dvd_mul_left ⟨otherNumerator, hcompat.symm⟩
  have hNum : numerator.natDegree ≤ w + δ := by
    unfold numerator FlowData.seedOffset
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simpa only [Nat.add_comm δ w] using Polynomial.natDegree_mul_le_of_le hcontent hdegree
    · exact (Polynomial.natDegree_add_le _ _).trans (max_le hc₀
        ((Polynomial.natDegree_C_mul_le _ _).trans hc₁))
  by_cases hnum : numerator = 0
  · exact ⟨0, by simp, hnum.trans (mul_zero _).symm⟩
  · obtain ⟨Q, hQ⟩ := hdiv
    have hdivQ : Q ∣ numerator := ⟨B.seedDenominator g, hQ.trans (mul_comm _ _)⟩
    exact ⟨Q, (Polynomial.natDegree_le_of_dvd hdivQ hnum).trans hNum, hQ⟩

theorem FlowData.normalized_agrees_at (B : FlowData K) (P Q : Polynomial K)
    (x g u₀ u₁ normalized : K)
    (hP : P.eval x = u₀ + g * u₁)
    (h₀ : B.d0.eval x * u₀ + B.c0.eval x = B.a0.eval x * normalized)
    (h₁ : B.d0.eval x * u₁ + B.c1.eval x = B.a1.eval x * normalized)
    (hden : (B.seedDenominator g).eval x ≠ 0)
    (hQ : B.d0 * P + B.seedOffset g = B.seedDenominator g * Q) :
    Q.eval x = normalized := by
  apply mul_left_cancel₀ hden
  have heval := congrArg (Polynomial.eval x) hQ
  simp only [FlowData.seedOffset, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, hP] at heval
  rw [← heval]
  simp only [FlowData.seedDenominator, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  linear_combination h₀ + g * h₁

theorem FlowData.normalized_fiber_card_le (B : FlowData K)
    (seeds : Finset K) (selected normalized : K → Polynomial K) (Q : Polynomial K)
    (w e : ℕ) (hd₀ : B.d0 ≠ 0)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hnorm : ∀ g ∈ seeds,
      B.d0 * selected g + B.seedOffset g = B.seedDenominator g * normalized g)
    (hno : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (seeds.filter (fun g => selected g = P₀ + Polynomial.C g * P₁)).card ≤ e + 1) :
    (seeds.filter fun g => normalized g = Q).card ≤ e + 1 := by
  classical
  let fiber := seeds.filter (fun g => normalized g = Q)
  apply Koala6831Cramer.card_le_of_common_denominator fiber selected B.d0
    (B.a0 * Q - B.c0) (B.a1 * Q - B.c1) hd₀ w e
  · exact fun g hg => hdegree g (Finset.mem_filter.mp hg).1
  · intro g hg
    obtain ⟨hseed, hQ⟩ := Finset.mem_filter.mp hg
    have he := hnorm g hseed
    simp only [FlowData.seedOffset, FlowData.seedDenominator, hQ] at he
    linear_combination he
  · intro P₀ P₁ h₀ h₁
    apply (Finset.card_le_card ?_).trans (hno P₀ P₁ h₀ h₁)
    intro g hg
    obtain ⟨hf, hp⟩ := Finset.mem_filter.mp hg
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).1, hp⟩

theorem FlowData.normalized_seed_card_le (B : FlowData K)
    (seeds : Finset K) (selected normalized : K → Polynomial K) (w e : ℕ)
    (hd₀ : B.d0 ≠ 0) (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hnorm : ∀ g ∈ seeds,
      B.d0 * selected g + B.seedOffset g = B.seedDenominator g * normalized g)
    (hno : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (seeds.filter (fun g => selected g = P₀ + Polynomial.C g * P₁)).card ≤ e + 1) :
    seeds.card ≤ (seeds.image normalized).card * (e + 1) := by
  classical
  let fiber (Q : Polynomial K) := seeds.filter (fun g => normalized g = Q)
  have hcover : seeds ⊆ (seeds.image normalized).biUnion fiber := by
    intro g hg
    exact Finset.mem_biUnion.mpr ⟨normalized g, Finset.mem_image_of_mem _ hg,
      Finset.mem_filter.mpr ⟨hg, rfl⟩⟩
  calc
    _ ≤ ((seeds.image normalized).biUnion fiber).card := Finset.card_le_card hcover
    _ ≤ ∑ Q ∈ seeds.image normalized, (fiber Q).card := Finset.card_biUnion_le
    _ ≤ ∑ _Q ∈ seeds.image normalized, (e + 1) := Finset.sum_le_sum (fun Q _ =>
      B.normalized_fiber_card_le seeds selected normalized Q w e hd₀ hdegree hnorm hno)
    _ = _ := by simp

end

end ProximityPrize.SubmissionLower.Koala6831Moving
