import ProximityPrize.SubmissionLower.Koala6844NormalizationNorm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases


namespace ProximityPrize.SubmissionLower.Koala6844Normalization

open Polynomial

noncomputable section

variable {K I : Type*} [Field K]

def affineWedge (A B : Fin 2 → Polynomial K) : Polynomial K :=
  A 0 * B 1 - A 1 * B 0

theorem affineWedge_zero_proportional {A B : Fin 2 → Polynomial K}
    (hA : IsCoprime (A 0) (A 1)) (hB : IsCoprime (B 0) (B 1))
    (h : affineWedge A B = 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ j, B j = C c * A j := by
  obtain ⟨a, b, hab⟩ := hA
  let l := a * B 0 + b * B 1
  have hcross : A 0 * B 1 = A 1 * B 0 := sub_eq_zero.mp h
  have h0 : B 0 = l * A 0 := by
    dsimp only [l]
    linear_combination -B 0 * hab - b * hcross
  have h1 : B 1 = l * A 1 := by
    dsimp only [l]
    linear_combination -B 1 * hab + a * hcross
  obtain ⟨u, v, huv⟩ := hB
  have hUnit : IsUnit l := by
    apply isUnit_iff_dvd_one.mpr
    refine ⟨u * A 0 + v * A 1, ?_⟩
    rw [← huv, h0, h1]
    ring
  let c := l.coeff 0
  have hl : l = C c := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hUnit)
  have hc : c ≠ 0 := by
    intro hz
    apply hUnit.ne_zero
    simpa [hz] using hl
  have hcoeff (j : Fin 2) : B j = l * A j := by
    fin_cases j
    · exact h0
    · exact h1
  exact ⟨c, hc, fun j => (hcoeff j).trans (by rw [hl])⟩

theorem affineWedge_zero_factor {A E : Fin 2 → Polynomial K}
    (hA : IsCoprime (A 0) (A 1)) (h : affineWedge A E = 0) :
    ∃ F : Polynomial K, ∀ j, E j = F * A j := by
  obtain ⟨a, b, hab⟩ := hA
  have hcross : A 0 * E 1 = A 1 * E 0 := sub_eq_zero.mp h
  refine ⟨a * E 0 + b * E 1, ?_⟩
  intro j
  fin_cases j
  · change E 0 = (a * E 0 + b * E 1) * A 0
    linear_combination -E 0 * hab - b * hcross
  · change E 1 = (a * E 0 + b * E 1) * A 1
    linear_combination -E 1 * hab + a * hcross

private theorem wedge_natDegree_le {A E : Fin 2 → Polynomial K} {a e : ℕ}
    (hA : ∀ j, (A j).natDegree ≤ a) (hE : ∀ j, (E j).natDegree ≤ e) :
    (affineWedge A E).natDegree ≤ a + e :=
  (natDegree_sub_le _ _).trans
    (max_le (natDegree_mul_le_of_le (hA 0) (hE 1))
      (natDegree_mul_le_of_le (hA 1) (hE 0)))

theorem exists_fixed_frobenius_difference (σ : K ≃+* K)
    (x : I ↪ K) (nodes : Finset I) (seeds : Finset K)
    (selected normalized : K → Polynomial K) (received : Fin 2 → I → K)
    (fixed : I → K) (d0 d1 : Polynomial K) (A C0 D : Fin 2 → Polynomial K) (w δ : ℕ)
    (hA : IsCoprime (A 0) (A 1))
    (hnode : ∀ i ∈ nodes, σ (x i) = x i)
    (hcard : w + 2 * δ < nodes.card)
    (hd0 : d0.natDegree + affineDegree A ≤ δ)
    (hd1 : d1.natDegree + affineDegree A ≤ δ)
    (hC : affineDegree A + affineDegree C0 ≤ w + δ)
    (hD : affineDegree A + affineDegree D ≤ w + δ)
    (hnonzero : ∀ g ∈ seeds, specializeAffine A g ≠ 0)
    (hleft : ∀ i ∈ nodes, ∀ j,
      d0.eval (x i) * received j i + (C0 j).eval (x i) = fixed i * (A j).eval (x i))
    (hright : ∀ i ∈ nodes, ∀ j,
      d1.eval (x i) * σ (received j i) - (D j).eval (x i) =
        fixed i * ((A j).map σ.toRingHom).eval (x i))
    (hleftWitness : ∀ g ∈ seeds,
      specializeAffine A g * normalized g = d0 * selected g + specializeAffine C0 g)
    (hrightWitness : ∀ g ∈ seeds,
      (specializeAffine A g).map σ.toRingHom * normalized g =
        d1 * (selected g).map σ.toRingHom - specializeAffine D (σ g)) :
    ∃ F : Polynomial K, ∀ g ∈ seeds,
      d1 * (normalized g).map σ.toRingHom - d0.map σ.toRingHom * normalized g = F := by
  classical
  let B (j : Fin 2) := (A j).map σ.toRingHom
  let E (j : Fin 2) := d1 * (C0 j).map σ.toRingHom + d0.map σ.toRingHom * D j
  have hdegB (j : Fin 2) : (B j).natDegree ≤ affineDegree A := by
    rw [show (B j).natDegree = (A j).natDegree by simp [B]]
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hdegE (j : Fin 2) : (E j).natDegree ≤ w + 2 * δ - affineDegree A := by
    have hcl : (C0 j).natDegree ≤ affineDegree C0 := by
      fin_cases j
      · exact le_max_left _ _
      · exact le_max_right _ _
    have hdl : (D j).natDegree ≤ affineDegree D := by
      fin_cases j
      · exact le_max_left _ _
      · exact le_max_right _ _
    unfold E
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact natDegree_mul_le.trans (by simp only [natDegree_map]; omega)
    · exact natDegree_mul_le.trans (by simp only [natDegree_map]; omega)
  have hdeg : (affineWedge B E).natDegree ≤ w + 2 * δ := by
    have h := wedge_natDegree_le hdegB hdegE
    omega
  have hvanish (i : I) (hi : i ∈ nodes) : (affineWedge B E).eval (x i) = 0 := by
    let b := d1.eval (x i) * σ (fixed i) - (d0.map σ.toRingHom).eval (x i) * fixed i
    have hE (j : Fin 2) : (E j).eval (x i) = b * (B j).eval (x i) := by
      have hmap (P : Polynomial K) : (P.map σ.toRingHom).eval (x i) = σ (P.eval (x i)) := by
        have he : (P.map σ.toRingHom).eval (σ (x i)) = σ (P.eval (x i)) :=
          eval_map_apply σ.toRingHom (p := P) (x i)
        rwa [hnode i hi] at he
      have hL := congrArg σ (hleft i hi j)
      simp only [map_add, map_mul, ← hmap] at hL
      have hR := hright i hi j
      simp only [E, B, b, eval_add, eval_mul]
      linear_combination d1.eval (x i) * hL -
        (d0.map σ.toRingHom).eval (x i) * hR
    simp only [affineWedge, eval_sub, eval_mul, hE]
    ring
  have hwedge : affineWedge B E = 0 := by
    by_contra hne
    have hbound : (nodes.image x).card ≤ (affineWedge B E).natDegree := by
      apply card_le_degree_of_subset_roots
      intro t ht
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      exact (mem_roots hne).mpr (hvanish i hi)
    rw [Finset.card_image_of_injective _ x.injective] at hbound
    omega
  obtain ⟨F, hFE⟩ := affineWedge_zero_factor
    (by exact hA.map (mapRingHom σ.toRingHom)) hwedge
  refine ⟨F, ?_⟩
  intro g hg
  have hBmap : (specializeAffine A g).map σ.toRingHom = specializeAffine B (σ g) := by
    simp only [specializeAffine, B, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] <;> rfl
  have hCmap : (specializeAffine C0 g).map σ.toRingHom =
      specializeAffine (fun j => (C0 j).map σ.toRingHom) (σ g) := by
    simp only [specializeAffine, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] <;> rfl
  have hFirst := congrArg (Polynomial.map σ.toRingHom) (hleftWitness g hg)
  simp only [Polynomial.map_add, Polynomial.map_mul, hBmap, hCmap] at hFirst
  have hSecond := hrightWitness g hg
  rw [hBmap] at hSecond
  have hn : specializeAffine B (σ g) ≠ 0 := by
    rw [← hBmap]
    exact (Polynomial.map_ne_zero_iff σ.injective).2 (hnonzero g hg)
  apply mul_left_cancel₀ hn
  have hEs := congrArg (fun Z : Fin 2 → Polynomial K => specializeAffine Z (σ g))
    (funext hFE)
  simp only [specializeAffine, E] at hEs hFirst hSecond ⊢
  linear_combination d1 * hFirst - d0.map σ.toRingHom * hSecond + hEs

end

end ProximityPrize.SubmissionLower.Koala6844Normalization
