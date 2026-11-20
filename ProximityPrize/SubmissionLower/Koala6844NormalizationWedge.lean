import ProximityPrize.SubmissionLower.Koala6844NormalizationConjugate
import ProximityPrize.SubmissionLower.Koala6844Primitive


namespace ProximityPrize.SubmissionLower.Koala6844Normalization

open Polynomial

noncomputable section

variable {K I : Type*} [Field K] [DecidableEq K] [DecidableEq I]

private theorem sub_mul_deg_le {P Q R S : Polynomial K} {a b : ℕ}
    (hP : P.natDegree ≤ a) (hQ : Q.natDegree ≤ b)
    (hR : R.natDegree ≤ a) (hS : S.natDegree ≤ b) :
    (P * Q - R * S).natDegree ≤ a + b :=
  (natDegree_sub_le _ _).trans
    (max_le (natDegree_mul_le_of_le hP hQ) (natDegree_mul_le_of_le hR hS))

theorem card_le_of_two_affine_equations
    (x : I ↪ K) (nodes : Finset I) (seeds : Finset K)
    (selected : K → Polynomial K) (received : Fin 2 → I → K)
    (m00 m01 m10 m11 n0 n1 : Polynomial K) (w A e b0 b1 : ℕ)
    (hM00 : m00.natDegree ≤ b0) (hM01 : m01.natDegree ≤ b0)
    (hM10 : m10.natDegree ≤ b1) (hM11 : m11.natDegree ≤ b1)
    (hN0 : n0.natDegree ≤ w + b0) (hN1 : n1.natDegree ≤ w + b1)
    (hdet : m00 * m11 - m01 * m10 ≠ 0) (hweight : w + (b0 + b1) < A)
    (h0 : ∀ i ∈ nodes, m00.eval (x i) * received 0 i +
      m01.eval (x i) * received 1 i = n0.eval (x i))
    (h1 : ∀ i ∈ nodes, m10.eval (x i) * received 0 i +
      m11.eval (x i) * received 1 i = n1.eval (x i))
    (hdeg : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hAgr : ∀ g ∈ seeds, A ≤ (nodes.filter fun i =>
      (selected g).eval (x i) = received 0 i + g * received 1 i).card)
    (hPencil : ∀ P0 P1 : Polynomial K, P0.natDegree ≤ w → P1.natDegree ≤ w →
      (seeds.filter fun g => selected g = P0 + C g * P1).card ≤ e + 1) :
    seeds.card ≤ e + 1 := by
  classical
  let Δ := m00 * m11 - m01 * m10
  let P0 := n0 * m11 - m01 * n1
  let P1 := m00 * n1 - n0 * m10
  have hΔ : Δ.natDegree ≤ b0 + b1 := sub_mul_deg_le hM00 hM11 hM01 hM10
  have hP0 : P0.natDegree ≤ w + (b0 + b1) := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_mul_le_of_le hN0 hM11).trans (by omega)
    · exact (natDegree_mul_le_of_le hM01 hN1).trans (by omega)
  have hP1 : P1.natDegree ≤ w + (b0 + b1) := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_mul_le_of_le hM00 hN1).trans (by omega)
    · exact (natDegree_mul_le_of_le hN0 hM10).trans (by omega)
  apply Koala6844Cramer.card_le_of_common_denominator seeds selected Δ P0 P1 hdet w e hdeg
    _ hPencil
  intro g hg
  refine Koala6844Cramer.equation_of_node_agreement x
    (nodes.filter fun i => (selected g).eval (x i) = received 0 i + g * received 1 i)
    Δ (selected g) P0 P1 g w (b0 + b1)
    hΔ (hdeg g hg) hP0 hP1 (hweight.trans_le (hAgr g hg)) ?_
  intro i hi
  obtain ⟨hn, hreceived⟩ := Finset.mem_filter.mp hi
  have l := h0 i hn
  have r := h1 i hn
  simp only [Δ, P0, P1, eval_sub, eval_mul, hreceived]
  linear_combination (m11.eval (x i) - g * m10.eval (x i)) * l +
    (g * m00.eval (x i) - m01.eval (x i)) * r

theorem nonconjugate_card_le (σ : K ≃+* K) (x : I ↪ K) (nodes : Finset I)
    (seeds : Finset K) (selected : K → Polynomial K) (received : Fin 2 → I → K)
    (fixed : I → K) (A B C0 D : Fin 2 → Polynomial K) (d0 d1 : Polynomial K)
    (w agreement e δ : ℕ)
    (hd0 : d0 ≠ 0) (hd1 : d1 ≠ 0)
    (hdeg0 : d0.natDegree + affineDegree B ≤ δ)
    (hdeg1 : d1.natDegree + affineDegree A ≤ δ)
    (hdegC : affineDegree B + affineDegree C0 ≤ w + δ)
    (hdegD : affineDegree A + affineDegree D ≤ w + δ)
    (hWedge : affineWedge A (fun j => (B j).map σ.symm.toRingHom) ≠ 0)
    (hfixed : ∀ i ∈ nodes, σ (x i) = x i)
    (hweight : w + 2 * δ < agreement)
    (hleft : ∀ i ∈ nodes, ∀ j,
      d0.eval (x i) * received j i + (C0 j).eval (x i) = fixed i * (A j).eval (x i))
    (hright : ∀ i ∈ nodes, ∀ j,
      d1.eval (x i) * σ (received j i) - (D j).eval (x i) = fixed i * (B j).eval (x i))
    (hdeg : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hAgr : ∀ g ∈ seeds, agreement ≤ (nodes.filter fun i =>
      (selected g).eval (x i) = received 0 i + g * received 1 i).card)
    (hPencil : ∀ P0 P1 : Polynomial K, P0.natDegree ≤ w → P1.natDegree ≤ w →
      (seeds.filter fun g => selected g = P0 + C g * P1).card ≤ e + 1) :
    seeds.card ≤ e + 1 := by
  classical
  let B' (j : Fin 2) := (B j).map σ.symm.toRingHom
  let D' (j : Fin 2) := (D j).map σ.symm.toRingHom
  let d1' := d1.map σ.symm.toRingHom
  let a := affineDegree A
  let b := affineDegree B
  let b0 := δ + a - b
  let b1 := δ + b - a
  have hab0 : a + d0.natDegree ≤ b0 := by unfold b0; change d0.natDegree + b ≤ δ at hdeg0; omega
  have hab1 : b + d1.natDegree ≤ b1 := by unfold b1; change d1.natDegree + a ≤ δ at hdeg1; omega
  have hbSum : b0 + b1 ≤ 2 * δ := by
    unfold b0 b1
    change d0.natDegree + b ≤ δ at hdeg0
    change d1.natDegree + a ≤ δ at hdeg1
    omega
  have hCA : a + affineDegree C0 ≤ w + b0 := by unfold b0; change b + affineDegree C0 ≤ _ at hdegC; omega
  have hDB : b + affineDegree D ≤ w + b1 := by unfold b1; change a + affineDegree D ≤ _ at hdegD; omega
  have hPair (U : Fin 2 → Polynomial K) (j : Fin 2) : (U j).natDegree ≤ affineDegree U := by
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hB' (j : Fin 2) : (B' j).natDegree ≤ b := by simpa [B', b] using hPair B j
  have hD' (j : Fin 2) : (D' j).natDegree ≤ affineDegree D := by simpa [D'] using hPair D j
  have hd1' : d1' ≠ 0 := (Polynomial.map_ne_zero_iff σ.symm.injective).2 hd1
  have hDen : d0 * A 1 * (-(d1' * B' 0)) - (-(d0 * A 0)) * (d1' * B' 1) ≠ 0 := by
    rw [show d0 * A 1 * (-(d1' * B' 0)) - (-(d0 * A 0)) * (d1' * B' 1) =
      d0 * d1' * affineWedge A B' by unfold affineWedge; ring]
    exact mul_ne_zero (mul_ne_zero hd0 hd1') hWedge
  apply card_le_of_two_affine_equations x nodes seeds selected received
    (d0 * A 1) (-(d0 * A 0)) (d1' * B' 1) (-(d1' * B' 0))
    (A 0 * C0 1 - A 1 * C0 0) (B' 1 * D' 0 - B' 0 * D' 1)
    w agreement e b0 b1 _ _ _ _ _ _ hDen (by omega) _ _ hdeg hAgr hPencil
  · exact natDegree_mul_le.trans (by have := hPair A 1; change (A 1).natDegree ≤ a at this; omega)
  · rw [natDegree_neg]
    exact natDegree_mul_le.trans (by have := hPair A 0; change (A 0).natDegree ≤ a at this; omega)
  · exact natDegree_mul_le.trans (by have hb := hB' 1; simp only [d1', natDegree_map]; omega)
  · rw [natDegree_neg]
    exact natDegree_mul_le.trans (by have hb := hB' 0; simp only [d1', natDegree_map]; omega)
  · exact (sub_mul_deg_le (hPair A 0) (hPair C0 1) (hPair A 1) (hPair C0 0)).trans hCA
  · exact (sub_mul_deg_le (hB' 1) (hD' 0) (hB' 0) (hD' 1)).trans hDB
  · intro i hi
    have L0 := hleft i hi 0
    have L1 := hleft i hi 1
    simp only [eval_mul, eval_neg, eval_sub]
    linear_combination (A 1).eval (x i) * L0 - (A 0).eval (x i) * L1
  · intro i hi
    have hSymm : σ.symm (x i) = x i := by simpa using (congrArg σ.symm (hfixed i hi)).symm
    have hamm (P : Polynomial K) :
        σ.symm (P.eval (x i)) = (P.map σ.symm.toRingHom).eval (x i) := by
      have he : σ.symm (P.eval (x i)) = (P.map σ.symm.toRingHom).eval (σ.symm (x i)) :=
        (eval_map_apply σ.symm.toRingHom (p := P) (x i)).symm
      rwa [hSymm] at he
    have R0 := congrArg σ.symm (hright i hi 0)
    have R1 := congrArg σ.symm (hright i hi 1)
    simp only [map_sub, map_mul, RingEquiv.symm_apply_apply] at R0 R1
    rw [hamm d1, hamm (D 0), hamm (B 0)] at R0
    rw [hamm d1, hamm (D 1), hamm (B 1)] at R1
    change d1'.eval (x i) * received 0 i - (D' 0).eval (x i) =
      σ.symm (fixed i) * (B' 0).eval (x i) at R0
    change d1'.eval (x i) * received 1 i - (D' 1).eval (x i) =
      σ.symm (fixed i) * (B' 1).eval (x i) at R1
    simp only [eval_mul, eval_neg, eval_sub]
    linear_combination (B' 1).eval (x i) * R0 - (B' 0).eval (x i) * R1

end

end ProximityPrize.SubmissionLower.Koala6844Normalization
