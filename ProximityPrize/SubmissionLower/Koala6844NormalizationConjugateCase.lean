import ProximityPrize.SubmissionLower.Koala6844NormalizationCleanup
import ProximityPrize.SubmissionLower.Koala6844NormalizationConjugate
import ProximityPrize.SubmissionLower.Koala6844NormalizationFamily


namespace ProximityPrize.SubmissionLower.Koala6844Normalization

open Polynomial
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

variable {K I : Type*} [Field K] [DecidableEq K] [DecidableEq I]

private theorem card_le_of_fixed_normalized
    (seeds : Finset K) (selected normalized : K → Polynomial K)
    (A C0 : Fin 2 → Polynomial K) (d0 : Polynomial K) (hd0 : d0 ≠ 0)
    (hEq : ∀ g ∈ seeds, specializeAffine A g * normalized g =
      d0 * selected g + specializeAffine C0 g)
    (hdeg : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071)
    (hPencil : ∀ P0 P1 : Polynomial K, P0.natDegree ≤ 131071 → P1.natDegree ≤ 131071 →
      (seeds.filter fun g => selected g = P0 + C g * P1).card ≤ 81185)
    (hfixed : ∀ g ∈ seeds, ∀ h ∈ seeds, normalized g = normalized h) :
    seeds.card ≤ 81185 := by
  by_cases he : seeds.Nonempty
  · obtain ⟨g0, hg0⟩ := he
    let Q := normalized g0
    apply Koala6844Cramer.card_le_of_common_denominator seeds selected d0
      (A 0 * Q - C0 0) (A 1 * Q - C0 1) hd0 131071 81184 hdeg _ hPencil
    intro g hg
    have h := hEq g hg
    rw [hfixed g hg g0 hg0] at h
    change specializeAffine A g * Q = _ at h
    simp only [specializeAffine] at h
    linear_combination -h
  · simp [Finset.not_nonempty_iff_eq_empty.mp he]

theorem center_conjugate_koalabear
    (x : I ↪ K)
    (σ : K ≃+* K) (hσ : ∀ g : K, σ g = g ^ 2130706433)
    (nodes : Finset I) (seeds : Finset K)
    (selected normalized : K → Polynomial K) (received : Fin 2 → I → K)
    (fixed : I → K) (d0 d1 : Polynomial K) (A C0 D : Fin 2 → Polynomial K) (δ : ℕ)
    (hd0 : d0 ≠ 0) (hd1 : d1 ≠ 0) (hContent : IsCoprime d0 d1)
    (hA : IsCoprime (A 0) (A 1))
    (hnode : ∀ i ∈ nodes, σ (x i) = x i)
    (hcard : 131071 + 2 * δ < nodes.card)
    (hWeight : affineDegree A ≤ 131071 + d0.natDegree)
    (hd0cap : d0.natDegree + affineDegree A ≤ δ)
    (hd1cap : d1.natDegree + affineDegree A ≤ δ)
    (hC : affineDegree A + affineDegree C0 ≤ 131071 + δ)
    (hD : affineDegree A + affineDegree D ≤ 131071 + δ)
    (hDen0 : ∀ g ∈ seeds, specializeAffine A g ≠ 0)
    (hDen : ∀ g ∈ seeds, ∀ i ∈ nodes, (specializeAffine A g).eval (x i) ≠ 0)
    (hleft : ∀ i ∈ nodes, ∀ j,
      d0.eval (x i) * received j i + (C0 j).eval (x i) = fixed i * (A j).eval (x i))
    (hright : ∀ i ∈ nodes, ∀ j,
      d1.eval (x i) * σ (received j i) - (D j).eval (x i) =
        fixed i * ((A j).map σ.toRingHom).eval (x i))
    (hLeft : ∀ g ∈ seeds,
      specializeAffine A g * normalized g = d0 * selected g + specializeAffine C0 g)
    (hRight : ∀ g ∈ seeds,
      (specializeAffine A g).map σ.toRingHom * normalized g =
        d1 * (selected g).map σ.toRingHom - specializeAffine D (σ g))
    (hDeg : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071)
    (hAgr : ∀ g ∈ seeds, 180960 ≤ (nodes.filter fun i =>
      (selected g).eval (x i) = received 0 i + g * received 1 i).card)
    (hNormAgr : ∀ g ∈ seeds, 180960 ≤
      (nodes.filter fun i => (normalized g).eval (x i) = fixed i).card)
    (hPencil : ∀ P0 P1 : Polynomial K, P0.natDegree ≤ 131071 → P1.natDegree ≤ 131071 →
      (seeds.filter fun g => selected g = P0 + C g * P1).card ≤ 81185)
    (inactiveCount :
      ∀ (S : Finset K) (P Q : K → Polynomial K) (V : I → K)
        (B : Fin 2 → Polynomial K) (C1 D1 : Polynomial K),
      (∀ i ∈ nodes, (d0 * d1).eval (x i) ≠ 0) →
      d1 ∣ D1 →
      (∀ g ∈ S, IsCoprime ((specializeAffine B g).map σ.toRingHom) d1) →
      (∀ g ∈ S, specializeAffine B g * Q g = d0 * P g + C g * C1) →
      (∀ g ∈ S, (specializeAffine B g).map σ.toRingHom * Q g =
        d1 * (P g).map σ.toRingHom + C (σ g) * D1) →
      (∀ g ∈ S, d1 * (Q g).map σ.toRingHom = d0.map σ.toRingHom * Q g) →
      (∀ g ∈ S, (P g).natDegree ≤ 131071) →
      (∀ g ∈ S, (Q g).natDegree ≤ 131071 + d0.natDegree) →
      (∀ g ∈ S, 180960 ≤ (nodes.filter fun i => (Q g).eval (x i) = V i).card) →
      (∀ P0 P1 : Polynomial K, P0.natDegree ≤ 131071 → P1.natDegree ≤ 131071 →
        (S.filter fun g => P g = P0 + C g * P1).card ≤ 81185) →
      S.card ≤ 8847637042363535) :
    seeds.card ≤ 8847637042363535 + (1 + d0.natDegree + d1.natDegree) ∨
    ∃ data : CenteredVirtualData x nodes σ 131071 180960 81184 δ,
      seeds.card ≤ data.seeds.card + (1 + d0.natDegree + d1.natDegree) := by
  classical
  by_cases hSame : ∀ g ∈ seeds, ∀ h ∈ seeds, normalized g = normalized h
  · exact Or.inl ((card_le_of_fixed_normalized seeds selected normalized A C0 d0 hd0
      hLeft hDeg hPencil hSame).trans (by omega))
  push Not at hSame
  obtain ⟨s, hs, t, ht, hst⟩ := hSame
  obtain ⟨F, hF⟩ := exists_fixed_frobenius_difference σ x nodes seeds selected normalized received
    fixed d0 d1 A C0 D 131071 δ hA hnode hcard hd0cap hd1cap hC hD hDen0 hleft hright hLeft hRight
  have hDiff : d1 * (normalized s - normalized t).map σ.toRingHom =
      d0.map σ.toRingHom * (normalized s - normalized t) :=
    homogeneous_difference σ.toRingHom (d0 := d0) (d1 := d1) (E := F)
      (hF s hs) (hF t ht)
  have eDegree : d1.natDegree = d0.natDegree :=
    content_degree_eq σ.toRingHom hd0 hd1 (sub_ne_zero.mpr hst) hDiff
  have eNode (i : I) (hi : i ∈ nodes) : d0.eval (x i) ≠ 0 ∧ d1.eval (x i) ≠ 0 :=
    content_eval_ne_zero σ.toRingHom hd0 hd1 (sub_ne_zero.mpr hst) hContent hDiff (hnode i hi)
  obtain ⟨keep, hsub, hsize, hvalid⟩ := exists_virtual_coprime_seeds σ A d0 d1 hd0 hd1 hA seeds
  by_cases hSmall : keep.card ≤ 1
  · exact Or.inl (by omega)
  obtain ⟨r, hr⟩ := Finset.card_pos.mp (show 0 < keep.card by omega)
  let G := keep.image (fun g => g - r)
  have hGcard : G.card = keep.card := card_centered_seeds keep r
  let P0 := selected r
  let Q0 := normalized r
  let A' := centerAffine A r
  let P' (g : K) := selected (r + g) - P0
  let Q' (g : K) := normalized (r + g) - Q0
  let C1 := C0 1 - A 1 * Q0
  let D1 := -D 1 - (A 1).map σ.toRingHom * Q0
  let U := centerReceived received x r P0
  let V (i : I) := fixed i - Q0.eval (x i)
  have old (g : K) (hg : g ∈ G) : r + g ∈ seeds :=
    hsub (mem_centered_seeds.mp hg)
  have hP0 := hDeg r (hsub hr)
  have hA'deg : affineDegree A' = affineDegree A := affine_degree_center (hvalid r hr).1
  have hA'0 : (A' 0).coeff (affineDegree A') ≠ 0 := by
    rw [hA'deg]
    change (specializeAffine A r).coeff (affineDegree A) ≠ 0
    rw [← (hvalid r hr).1]
    exact leadingCoeff_ne_zero.mpr (hDen0 r (hsub hr))
  have hQ'zero : Q' 0 = 0 := by simp [Q', Q0]
  have hG0 : 0 ∈ G := Finset.mem_image.mpr ⟨r, hr, sub_self _⟩
  have hP'deg (g : K) (hg : g ∈ G) : (P' g).natDegree ≤ 131071 :=
    (natDegree_sub_le _ _).trans (max_le (hDeg _ (old g hg)) hP0)
  have hHom (g : K) (hg : g ∈ G) :
      d1 * (Q' g).map σ.toRingHom = d0.map σ.toRingHom * Q' g :=
    homogeneous_difference σ.toRingHom (hF (r + g) (old g hg)) (hF r (hsub hr))
  have hEqL (g : K) (hg : g ∈ G) :
    specializeAffine A' g * Q' g = d0 * P' g + C g * C1 :=
    center_left_equation A C0 d0 r g P0 (selected (r + g)) Q0 (normalized (r + g))
      (hLeft r (hsub hr)) (hLeft _ (old g hg))
  have hEqR (g : K) (hg : g ∈ G) :
    (specializeAffine A' g).map σ.toRingHom * Q' g =
      d1 * (P' g).map σ.toRingHom + C (σ g) * D1 :=
    center_right_equation σ.toRingHom A D d1 r g P0 (selected (r + g)) Q0 (normalized (r + g))
      (hRight r (hsub hr)) (hRight _ (old g hg))
  have hFull (g : K) (hg : g ∈ G) :
      (specializeAffine A' g).natDegree = affineDegree A' := by
    rw [show A' = centerAffine A r from rfl, specialize_centerAffine, hA'deg]
    exact (hvalid _ (mem_centered_seeds.mp hg)).1
  have hDen0' (g : K) (hg : g ∈ G) : specializeAffine A' g ≠ 0 := by
    rw [show A' = centerAffine A r from rfl, specialize_centerAffine]
    exact hDen0 _ (old g hg)
  by_cases hInf : C1.natDegree ≤ 131071 + d0.natDegree
  · have hQ'deg (g : K) (hg : g ∈ G) :
        (Q' g).natDegree ≤ 131071 + d0.natDegree - affineDegree A' :=
      centered_degree_le A' d0 C1 (P' g) (Q' g) g 131071
        (hDen0' g hg) (hFull g hg) (hP'deg g hg) hInf (hEqL g hg)
    have hCop0 (g : K) (hg : g ∈ G) : IsCoprime (specializeAffine A' g) d0 := by
      rw [show A' = centerAffine A r from rfl, specialize_centerAffine]
      exact (hvalid _ (mem_centered_seeds.mp hg)).2.1
    have hCop1 (g : K) (hg : g ∈ G) :
        IsCoprime ((specializeAffine A' g).map σ.toRingHom) d1 := by
      rw [show A' = centerAffine A r from rfl, specialize_centerAffine]
      exact (hvalid _ (mem_centered_seeds.mp hg)).2.2
    have hNormClose (g : K) (hg : g ∈ G) :
        180960 ≤ (nodes.filter fun i => (Q' g).eval (x i) = V i).card :=
      centered_normalized_agreement_cap x nodes fixed Q0 (normalized (r + g)) 180960
        (hNormAgr _ (old g hg))
    have hKeepPencil (p₀ p₁ : Polynomial K) (h₀ : p₀.natDegree ≤ 131071)
        (h₁ : p₁.natDegree ≤ 131071) :
        (keep.filter fun g => selected g = p₀ + C g * p₁).card ≤ 81185 :=
      (Finset.card_le_card (Finset.filter_subset_filter _ hsub)).trans (hPencil p₀ p₁ h₀ h₁)
    have hPencil' (p₀ p₁ : Polynomial K) (h₀ : p₀.natDegree ≤ 131071)
        (h₁ : p₁.natDegree ≤ 131071) :
        (G.filter fun g => P' g = p₀ + C g * p₁).card ≤ 81185 :=
      centered_pencil_cap keep selected r 131071 81184 hP0 hKeepPencil p₀ p₁ h₀ h₁
    by_cases hInactive : d1 ∣ D1
    · have hDomain (i : I) (hi : i ∈ nodes) : (d0 * d1).eval (x i) ≠ 0 := by
        rw [eval_mul]
        exact mul_ne_zero (eNode i hi).1 (eNode i hi).2
      have hI := inactiveCount G P' Q' V A' C1 D1 hDomain hInactive hCop1 hEqL hEqR hHom hP'deg
        (fun g hg => (hQ'deg g hg).trans (Nat.sub_le _ _)) hNormClose hPencil'
      exact Or.inl (by omega)
    · have hD1deg : D1.natDegree ≤ 131071 + d1.natDegree := by
        obtain ⟨s, hs, t, ht, hne⟩ := Finset.one_lt_card.mp (show 1 < G.card by omega)
        have hnonzero : ∃ g ∈ G, g ≠ 0 := by
          by_cases hz : s = 0
          · exact ⟨t, ht, by simpa [hz, ne_comm] using hne⟩
          · exact ⟨s, hs, hz⟩
        obtain ⟨g, hg, hgn⟩ := hnonzero
        by_cases hD1 : D1 = 0
        · simp [hD1]
        have hExpr : C (σ g) * D1 =
            (specializeAffine A' g).map σ.toRingHom * Q' g -
                d1 * (P' g).map σ.toRingHom := by
          linear_combination -(hEqR g hg)
        have he := congrArg natDegree hExpr
        have hs0 : σ g ≠ 0 := (_root_.map_ne_zero σ).2 hgn
        rw [natDegree_mul (C_ne_zero.mpr hs0) hD1, natDegree_C, zero_add] at he
        rw [he]
        refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · refine natDegree_mul_le.trans ?_
          rw [natDegree_map, hFull g hg]
          have hq := hQ'deg g hg
          have hcap := hWeight
          rw [← hA'deg] at hcap
          omega
        · refine natDegree_mul_le.trans ?_
          rw [natDegree_map]
          have hp := hP'deg g hg
          omega
      let data : CenteredVirtualData x nodes σ 131071 180960 81184 δ := {
        seeds := G
        zero_mem := hG0
        selected := P'
        normalized := Q'
        received := U
        fixedWord := V
        A0 := A'
        C1 := C1
        D1 := D1
        d0 := d0
        d1 := d1
        d0_ne := hd0
        d1_ne := hd1
        coprime_content := hContent
        coprime_A0 := center_affine_coprime r hA
        degree_content := eDegree
        support_le := by simpa only [hA'deg] using hd0cap
        degree_C1 := hInf
        degree_D1 := hD1deg
        content0_off_domain := fun i hi => (eNode i hi).1
        content1_off_domain := fun i hi => (eNode i hi).2
        active := hInactive
        selected_degree := hP'deg
        normalized_degree := hQ'deg
        denominator_degree := hFull
        denominator_ne := hDen0'
        denominator_on_domain := fun g hg i hi => by
          rw [show A' = centerAffine A r from rfl, specialize_centerAffine]
          exact hDen _ (old g hg) i hi
        coprime_denominator0 := hCop0
        coprime_denominator1 := hCop1
        equation0 := hEqL
        equation1 := hEqR
        homogeneous := hHom
        received_equation := fun i hi => center_fixed_word received x i d0 A C0 r (fixed i) P0 Q0
          (hleft i hi) (hLeft r (hsub hr))
        agreements := fun g hg =>
          centered_agreement_cap x nodes received selected r g 180960 (hAgr _ (old g hg))
        normalized_agreements := hNormClose
        pencil := hPencil' }
      refine Or.inr ⟨data, ?_⟩
      change seeds.card ≤ G.card + (1 + d0.natDegree + d1.natDegree)
      omega
  · have hBig := infinity_excess_card_le σ.toRingHom 2130706433 131071 (by decide) hσ A' d0 d1 C1
      hd1 G P' Q' hA'0 hQ'zero hFull hP'deg (by omega) hEqL hHom
    exact Or.inl (by omega)

end

end ProximityPrize.SubmissionLower.Koala6844Normalization
