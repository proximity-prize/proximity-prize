import ProximityPrize.SubmissionLower.Koala6844VirtualCRT
import ProximityPrize.SubmissionLower.Koala6844VirtualMatrix

namespace ProximityPrize.SubmissionLower.Koala6844VirtualCRT

open Polynomial
open scoped BigOperators Classical

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {K : Type} [Field K]

def coordinates (d : K[X]) (hd : d ≠ 0) (Q : K[X]) :=
  (AdjoinRoot.powerBasisAux hd).repr (AdjoinRoot.mk d Q)

private def representative (d Q : K[X]) (hd : d ≠ 0) : K[X] :=
  ∑ i : Fin d.natDegree, C (coordinates d hd Q i) * (Polynomial.X : K[X]) ^ i.val

private theorem mk_representative (d Q : K[X]) (hd : d ≠ 0) :
    AdjoinRoot.mk d (representative d Q hd) = AdjoinRoot.mk d Q := by
  let basis := AdjoinRoot.powerBasisAux hd
  have hBasis (i : Fin d.natDegree) : basis i = AdjoinRoot.root d ^ i.val :=
    (AdjoinRoot.powerBasis hd).basis_eq_pow (show Fin (AdjoinRoot.powerBasis hd).dim from i)
  rw [representative, map_sum]
  calc
    _ = ∑ i : Fin d.natDegree, coordinates d hd Q i • basis i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X, hBasis]
      rw [Algebra.smul_def]
      rfl
    _ = _ := basis.sum_repr (AdjoinRoot.mk d Q)

private def remainderMap (D : K[X]) : K[X] →ₗ[K] K[X] :=
  Polynomial.modByMonicHom (D * C D.leadingCoeff⁻¹)

private theorem remainderMap_apply (D P : K[X]) : remainderMap D P = P % D := by
  rw [Polynomial.mod_def]
  rfl

theorem crt_lift_repr (d₀ d₁ : K[X]) (hd₀ : d₀ ≠ 0) (hd₁ : d₁ ≠ 0)
    (hcoprime : IsCoprime d₀ d₁) :
    ∃ B₀ : Fin d₀.natDegree → K[X], ∃ B₁ : Fin d₁.natDegree → K[X],
      (∀ i, (B₀ i).degree < (d₀ * d₁).degree) ∧
      (∀ i, (B₁ i).degree < (d₀ * d₁).degree) ∧
      ∀ Q : K[X], Q % (d₀ * d₁) =
        (∑ i, coordinates d₀ hd₀ Q i • B₀ i) + (∑ i, coordinates d₁ hd₁ Q i • B₁ i) := by
  obtain ⟨u, v, h⟩ := hcoprime
  let D := d₀ * d₁
  let raw₀ (i : Fin d₀.natDegree) := (v * d₁) * (Polynomial.X : K[X]) ^ i.val
  let raw₁ (i : Fin d₁.natDegree) := (u * d₀) * (Polynomial.X : K[X]) ^ i.val
  refine ⟨fun i => raw₀ i % D, fun i => raw₁ i % D,
    fun i => Polynomial.degree_mod_lt _ (mul_ne_zero hd₀ hd₁),
    fun i => Polynomial.degree_mod_lt _ (mul_ne_zero hd₀ hd₁), ?_⟩
  intro Q
  let P₀ := representative d₀ Q hd₀
  let P₁ := representative d₁ Q hd₁
  let F := (v * d₁) * P₀ + (u * d₀) * P₁
  have hone₀ : AdjoinRoot.mk d₀ (v * d₁) = 1 := by
    have he := congrArg (AdjoinRoot.mk d₀) h
    simpa only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one] using he
  have hone₁ : AdjoinRoot.mk d₁ (u * d₀) = 1 := by
    have he := congrArg (AdjoinRoot.mk d₁) h
    simpa only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero, add_zero, map_one] using he
  have hmk₀ : AdjoinRoot.mk d₀ F = AdjoinRoot.mk d₀ Q := by
    dsimp only [F]
    rw [map_add, map_mul, hone₀, one_mul, map_mul (AdjoinRoot.mk d₀) (u * d₀),
      map_mul (AdjoinRoot.mk d₀) u, AdjoinRoot.mk_self, mul_zero, zero_mul, add_zero]
    exact mk_representative d₀ Q hd₀
  have hmk₁ : AdjoinRoot.mk d₁ F = AdjoinRoot.mk d₁ Q := by
    dsimp only [F]
    rw [map_add, map_mul (AdjoinRoot.mk d₁) (v * d₁), map_mul (AdjoinRoot.mk d₁) v,
      AdjoinRoot.mk_self, mul_zero, zero_mul, zero_add,
      map_mul (AdjoinRoot.mk d₁) (u * d₀), hone₁, one_mul]
    exact mk_representative d₁ Q hd₁
  have hDvd : D ∣ Q - F :=
    (show IsCoprime d₀ d₁ from ⟨u, v, h⟩).mul_dvd
      (AdjoinRoot.mk_eq_mk.mp hmk₀.symm) (AdjoinRoot.mk_eq_mk.mp hmk₁.symm)
  have hmod : Q % D = F % D := by
    apply sub_eq_zero.mp
    rw [← Polynomial.sub_mod]
    exact EuclideanDomain.mod_eq_zero.mpr hDvd
  have hF : F = (∑ i, coordinates d₀ hd₀ Q i • raw₀ i) +
      (∑ i, coordinates d₁ hd₁ Q i • raw₁ i) := by
    dsimp only [F, P₀, P₁, raw₀, raw₁, representative]
    rw [Finset.mul_sum, Finset.mul_sum]
    simp only [Polynomial.smul_eq_C_mul, mul_left_comm]
  change Q % D = _
  rw [hmod, ← remainderMap_apply, hF, map_add, map_sum, map_sum]
  simp only [map_smul, remainderMap_apply]

end
end ProximityPrize.SubmissionLower.Koala6844VirtualCRT


namespace ProximityPrize.SubmissionLower.Koala6844VirtualCRT

open Polynomial Koala6844Normalization
open scoped BigOperators Classical

noncomputable section
set_option autoImplicit false

theorem centered_cleared_crt {K I : Type} [Field K] [DecidableEq K] [DecidableEq I]
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K} {w agreement errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ w agreement errors excess) :
    ∃ Δ₀ Δ₁ : K[X], ∃ N₀ B₀ : Fin data.d0.natDegree → K[X],
    ∃ N₁ B₁ : Fin data.d1.natDegree → K[X],
      Δ₀.natDegree ≤ data.d0.natDegree ∧ Δ₁.natDegree ≤ data.d1.natDegree ∧
      (∀ i, (N₀ i).natDegree ≤ data.d0.natDegree ∧
        (B₀ i).degree < (data.d0 * data.d1).degree) ∧
      (∀ i, (N₁ i).natDegree ≤ data.d1.natDegree ∧
        (B₁ i).degree < (data.d0 * data.d1).degree) ∧
      ∀ g ∈ data.seeds, Δ₀.eval g ≠ 0 ∧ Δ₁.eval (σ g) ≠ 0 ∧
        (Δ₀.eval g * Δ₁.eval (σ g)) • (data.normalized g % (data.d0 * data.d1)) =
          (∑ i, ((N₀ i).eval g * Δ₁.eval (σ g)) • B₀ i) +
          (∑ i, ((N₁ i).eval (σ g) * Δ₀.eval g) • B₁ i) := by
  obtain ⟨Δ₀, N₀, hΔ₀, hN₀, hC₀⟩ := Koala6844VirtualMatrix.affine_residue_coordinates
    data.d0 (data.A0 0) (data.A0 1) data.C1 data.d0_ne
  obtain ⟨Δ₁, N₁, hΔ₁, hN₁, hC₁⟩ := Koala6844VirtualMatrix.affine_residue_coordinates
    data.d1 ((data.A0 0).map σ.toRingHom) ((data.A0 1).map σ.toRingHom) data.D1 data.d1_ne
  obtain ⟨B₀, B₁, hB₀, hB₁, hCRT⟩ := crt_lift_repr data.d0 data.d1 data.d0_ne data.d1_ne data.coprime_content
  refine ⟨Δ₀, Δ₁, N₀, B₀, N₁, B₁, hΔ₀, hΔ₁, fun i => ⟨hN₀ i, hB₀ i⟩,
    fun i => ⟨hN₁ i, hB₁ i⟩, ?_⟩
  intro g hg
  have hdiv₀ : data.d0 ∣ specializeAffine data.A0 g * data.normalized g - C g * data.C1 := by
    rw [data.equation0 g hg, add_sub_cancel_right]
    exact dvd_mul_right _ _
  have hdiv₁ : data.d1 ∣ (specializeAffine data.A0 g).map σ.toRingHom * data.normalized g -
      C (σ g) * data.D1 := by
    rw [data.equation1 g hg, add_sub_cancel_right]
    exact dvd_mul_right _ _
  have hmap : (specializeAffine data.A0 g).map σ.toRingHom =
      (data.A0 0).map σ.toRingHom + C (σ g) * (data.A0 1).map σ.toRingHom := by
    rw [specializeAffine, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
    rfl
  obtain ⟨hne₀, heval₀⟩ := hC₀ g (data.normalized g) (data.coprime_denominator0 g hg) hdiv₀
  obtain ⟨hne₁, heval₁⟩ := hC₁ (σ g) (data.normalized g)
    (hmap ▸ data.coprime_denominator1 g hg) (hmap ▸ hdiv₁)
  refine ⟨hne₀, hne₁, ?_⟩
  rw [hCRT, smul_add, Finset.smul_sum, Finset.smul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, mul_comm (Δ₀.eval g) (Δ₁.eval (σ g)), mul_assoc]
    rw [show Δ₀.eval g * coordinates data.d0 data.d0_ne (data.normalized g) i =
      (N₀ i).eval g from heval₀ i, mul_comm]
  · apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, mul_assoc]
    rw [show Δ₁.eval (σ g) * coordinates data.d1 data.d1_ne (data.normalized g) i =
      (N₁ i).eval (σ g) from heval₁ i, mul_comm]

end
end ProximityPrize.SubmissionLower.Koala6844VirtualCRT

