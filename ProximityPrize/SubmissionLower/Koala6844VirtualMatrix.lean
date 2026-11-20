import ProximityPrize.SubmissionLower.Koala6844Primitive
import Mathlib.RingTheory.AdjoinRoot



namespace ProximityPrize.SubmissionLower.Koala6844VirtualMatrix

open Polynomial Matrix

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000

variable {K : Type} [Field K]

private def pencil {m : ℕ} (M₀ M₁ : Matrix (Fin m) (Fin m) K) :
    Matrix (Fin m) (Fin m) K[X] :=
  fun i j => C (M₀ i j) + (Polynomial.X : K[X]) * C (M₁ i j)

private theorem pencil_entry_degree {m : ℕ} (M₀ M₁ : Matrix (Fin m) (Fin m) K)
    (i j : Fin m) : ((pencil M₀ M₁) i j).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simp
  · exact Polynomial.natDegree_mul_C_le (Polynomial.X : K[X]) (M₁ i j) |>.trans (by simp)

private theorem mk_C_mul {d : K[X]} (t : K) (P : K[X]) :
    AdjoinRoot.mk d (C t * P) = t • AdjoinRoot.mk d P := by
  rw [map_mul, AdjoinRoot.mk_C, Algebra.smul_def]
  rfl

private theorem mk_isUnit_of_coprime {d A : K[X]} (h : IsCoprime A d) :
    IsUnit (AdjoinRoot.mk d A) := by
  obtain ⟨u, v, h⟩ := h
  have he := congrArg (AdjoinRoot.mk d) h
  simp only [map_add, map_mul, AdjoinRoot.mk_self, mul_zero, add_zero, map_one] at he
  exact IsUnit.of_mul_eq_one (AdjoinRoot.mk d u) (by simpa only [mul_comm] using he)

theorem affine_residue_coordinates (d A₀ A₁ B : K[X]) (hd : d ≠ 0) :
    ∃ Δ : K[X], ∃ N : Fin d.natDegree → K[X],
      Δ.natDegree ≤ d.natDegree ∧ (∀ i, (N i).natDegree ≤ d.natDegree) ∧
      ∀ t : K, ∀ P : K[X],
        IsCoprime (A₀ + C t * A₁) d →
        (d ∣ (A₀ + C t * A₁) * P - C t * B) →
        Δ.eval t ≠ 0 ∧
        ∀ i, Δ.eval t *
          (AdjoinRoot.powerBasisAux hd).repr (AdjoinRoot.mk d P) i = (N i).eval t := by
  classical
  let b := AdjoinRoot.powerBasisAux hd
  let M : AdjoinRoot d →ₐ[K] Matrix (Fin d.natDegree) (Fin d.natDegree) K :=
    Algebra.leftMulMatrix b
  let L := pencil (M (AdjoinRoot.mk d A₀)) (M (AdjoinRoot.mk d A₁))
  let v : Fin d.natDegree → K[X] := fun i => (Polynomial.X : K[X]) * C (b.repr (AdjoinRoot.mk d B) i)
  have hL i j : (L i j).natDegree ≤ 1 := pencil_entry_degree _ _ i j
  have hv j : (v j).natDegree ≤ 0 + 1 := by
    simpa only [v, Nat.zero_add, Polynomial.natDegree_X] using
      (Polynomial.natDegree_mul_C_le (Polynomial.X : K[X]) (b.repr (AdjoinRoot.mk d B) j))
  refine ⟨L.det, fun i => (L.updateCol i v).det, ?_, ?_, ?_⟩
  · simpa using Koala6844Cramer.det_natDegree_le_of_column_bounds L (fun _ => 1) hL
  · intro i
    simpa using Koala6844Cramer.cramer_natDegree_le L v i 0 1 hL hv
  · intro t P hcoprime hdiv
    let A := A₀ + C t * A₁
    have hmat : (evalRingHom t).mapMatrix L = M (AdjoinRoot.mk d A) := by
      rw [show AdjoinRoot.mk d A = AdjoinRoot.mk d A₀ + t • AdjoinRoot.mk d A₁ by
        change AdjoinRoot.mk d (A₀ + C t * A₁) = _
        rw [map_add, mk_C_mul], map_add, map_smul]
      ext i j
      change (C (M (AdjoinRoot.mk d A₀) i j) + Polynomial.X *
          C (M (AdjoinRoot.mk d A₁) i j)).eval t =
        M (AdjoinRoot.mk d A₀) i j + t * M (AdjoinRoot.mk d A₁) i j
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_C]
    have hdet : L.det.eval t ≠ 0 := by
      have hu : IsUnit (M (AdjoinRoot.mk d A)) := (mk_isUnit_of_coprime hcoprime).map M
      have hnum : (M (AdjoinRoot.mk d A)).det ≠ 0 :=
        isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
      change (evalRingHom t) L.det ≠ 0
      rw [(evalRingHom t).map_det, hmat]
      exact hnum
    have heq : AdjoinRoot.mk d A * AdjoinRoot.mk d P = t • AdjoinRoot.mk d B := by
      apply sub_eq_zero.mp
      rw [← map_mul, ← mk_C_mul, ← map_sub]
      exact (AdjoinRoot.mk_eq_zero (f := d)).mpr hdiv
    refine ⟨hdet, fun i => Koala6844Cramer.eval_cramer_identity L v t
      (fun j => b.repr (AdjoinRoot.mk d P) j) i ?_⟩
    rw [hmat]
    change (Algebra.leftMulMatrix b (AdjoinRoot.mk d A)) *ᵥ b.repr (AdjoinRoot.mk d P) = _
    rw [Algebra.leftMulMatrix_mulVec_repr, heq, map_smul]
    ext j
    change t * b.repr (AdjoinRoot.mk d B) j =
      (Polynomial.X * C (b.repr (AdjoinRoot.mk d B) j)).eval t
    rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]

end

end ProximityPrize.SubmissionLower.Koala6844VirtualMatrix

