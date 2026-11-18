/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- 68.33 terminal specialization, derived from Lucieno PR 618, BitWonka PR 581 and Bome2017’s accepted 68.32 proof. Apache-2.0. -/
import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.K6833Residual

open scoped Classical BigOperators
open SecondJetSupport SecondJetBasis SecondJetGlobalSupport
open SecondJetWeightedSupport SecondJetRelaxedGlobalSupport

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

private abbrev Poly5 := SecondJetSupport.Poly (K := K)

def sourceMiddle (e : Fin 5 →₀ ℕ) : ℕ :=
  e 1 + e 2 + e 3

private def middleWeights : Fin 5 → ℤ := ![0,1,1,1,0]

private theorem middleWeight_eq (e : Fin 5 →₀ ℕ) :
    weight middleWeights e = (sourceMiddle e : ℤ) := by
  simp [weight, middleWeights, sourceMiddle, Fin.sum_univ_five,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

private theorem localize_monomial_one (x u₀ u₁ : K) (e : Fin 5 →₀ ℕ) :
    localize x u₀ u₁ (MvPolynomial.monomial e (1 : K)) =
      (MvPolynomial.C x + MvPolynomial.X 0)^e 0 *
        MvPolynomial.X 1^e 1 *
        (MvPolynomial.C u₀ + MvPolynomial.C u₁ * MvPolynomial.X 4 +
          MvPolynomial.X 0 * MvPolynomial.X 2)^e 2 *
        MvPolynomial.X 3^e 3 * MvPolynomial.X 4^e 4 := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_five, map_mul, map_pow,
      map_one, one_mul, localize, MvPolynomial.aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  · intro i
    simp

private theorem strict_pow_difference {A B : Poly5 (K := K)}
    (hA : LinearBound middleWeights 1 A) (hB : LinearBound middleWeights 1 B)
    (hDiff : LinearBound middleWeights 0 (A-B)) (d : ℕ) :
    LinearBound middleWeights ((d : ℤ)-1) (A^d-B^d) := by
  induction d with
  | zero => simp [LinearBound]
  | succ d ih =>
    have hw : A^(d+1)-B^(d+1) = (A-B)*A^d + B*(A^d-B^d) := by
      simp only [pow_succ]
      ring
    rw [hw]
    exact ((hDiff.mul (hA.pow d)).mono (by push_cast; ring_nf; omega)).add
      ((hB.mul ih).mono (by push_cast; ring_nf; omega))

theorem local_difference_middle_lt (x u₀ u₁ : K) (e d : Fin 5 →₀ ℕ)
    (hd : d ∈ (localize x u₀ u₁ (MvPolynomial.monomial e (1 : K)) -
      localize x 0 0 (MvPolynomial.monomial e (1 : K))).support) :
    sourceMiddle d < sourceMiddle e := by
  let A : Poly5 (K := K) := MvPolynomial.C u₀ + MvPolynomial.C u₁ * MvPolynomial.X 4 +
    MvPolynomial.X 0 * MvPolynomial.X 2
  let B : Poly5 (K := K) := MvPolynomial.C (0 : K) +
    MvPolynomial.C (0 : K) * MvPolynomial.X 4 + MvPolynomial.X 0 * MvPolynomial.X 2
  have hx (u v : K) (j : Fin 5) :
      LinearBound middleWeights (middleWeights j) (localize x u v (MvPolynomial.X j)) :=
    localize_X_bound middleWeights rfl rfl (by decide) x u v j
  have hA : LinearBound middleWeights 1 A := by
    simpa only [A, middleWeights, localize, MvPolynomial.aeval_X, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_succ, Matrix.cons_val_zero,
      Function.comp_apply] using hx u₀ u₁ 2
  have hB : LinearBound middleWeights 1 B := by
    simpa only [B, middleWeights, localize, MvPolynomial.aeval_X, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_succ, Matrix.cons_val_zero,
      Function.comp_apply] using hx 0 0 2
  have hDiff : LinearBound middleWeights 0 (A-B) := by
    rw [show A-B = MvPolynomial.C u₀ + MvPolynomial.C u₁ * MvPolynomial.X 4 by
      simp only [A, B, map_zero, zero_mul, zero_add]
      ring]
    exact (linear_C middleWeights u₀).add ((linear_C middleWeights u₁).mul
      (linear_X (K := K) middleWeights 4))
  have hX : LinearBound middleWeights 0 (MvPolynomial.C x + MvPolynomial.X 0) := by
    simpa only [middleWeights, localize, MvPolynomial.aeval_X, Matrix.cons_val_zero] using hx 0 0 0
  have hS : LinearBound middleWeights 1 (MvPolynomial.X 1 : Poly5 (K := K)) :=
    linear_X (K := K) middleWeights 1
  have hR : LinearBound middleWeights 1 (MvPolynomial.X 3 : Poly5 (K := K)) :=
    linear_X (K := K) middleWeights 3
  have hZ : LinearBound middleWeights 0 (MvPolynomial.X 4 : Poly5 (K := K)) :=
    linear_X (K := K) middleWeights 4
  have hf := (((((hX.pow (e 0)).mul (hS.pow (e 1))).mul
    (strict_pow_difference hA hB hDiff (e 2))).mul (hR.pow (e 3))).mul (hZ.pow (e 4)))
  rw [localize_monomial_one, localize_monomial_one] at hd
  change d ∈ (((MvPolynomial.C x + MvPolynomial.X 0)^e 0 *
      MvPolynomial.X 1^e 1 * A^e 2 * MvPolynomial.X 3^e 3 * MvPolynomial.X 4^e 4) -
      ((MvPolynomial.C x + MvPolynomial.X 0)^e 0 *
      MvPolynomial.X 1^e 1 * B^e 2 * MvPolynomial.X 3^e 3 * MvPolynomial.X 4^e 4)).support at hd
  rw [show (MvPolynomial.C x + MvPolynomial.X 0)^e 0 *
      MvPolynomial.X 1^e 1 * A^e 2 * MvPolynomial.X 3^e 3 * MvPolynomial.X 4^e 4 -
      (MvPolynomial.C x + MvPolynomial.X 0)^e 0 *
      MvPolynomial.X 1^e 1 * B^e 2 * MvPolynomial.X 3^e 3 * MvPolynomial.X 4^e 4 =
      (MvPolynomial.C x + MvPolynomial.X 0)^e 0 *
      MvPolynomial.X 1^e 1 * (A^e 2-B^e 2) * MvPolynomial.X 3^e 3 * MvPolynomial.X 4^e 4 by
        ring] at hd
  have h := hf d hd
  rw [middleWeight_eq] at h
  unfold sourceMiddle at h ⊢
  simp only [mul_zero, mul_one, zero_add, add_zero] at h
  omega

def localColumn (m : ℕ) (x u₀ u₁ : K) (e : Fin 5 →₀ ℕ) : Jet (MvPolynomial (Fin 3) K) :=
  truncateOuter (K := K) m (flatEquiv (K := K) (localize x u₀ u₁ (MvPolynomial.monomial e 1)))

theorem zero_word_column_eq_zero (m : ℕ) (x : K) (e : Fin 5 →₀ ℕ)
    (hay : m ≤ e 2) : localColumn m x 0 0 e = 0 := by
  have hexp : MvPolynomial.X (0 : Fin 5)^m ∣
      localize x 0 0 (MvPolynomial.monomial e (1 : K)) := by
    rw [localize_monomial_one]
    simp only [map_zero, zero_mul, zero_add, mul_pow]
    have h0 : MvPolynomial.X (0 : Fin 5)^m ∣ (MvPolynomial.X 0 : Poly5 (K := K))^e 2 :=
      pow_dvd_pow _ hay
    have h1 : MvPolynomial.X (0 : Fin 5)^m ∣
        (MvPolynomial.X 0 : Poly5 (K := K))^e 2 * MvPolynomial.X 2^e 2 :=
      dvd_mul_of_dvd_left h0 _
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h1 _) _) _
  obtain ⟨Q,hQ⟩ := hexp
  apply (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mpr
  refine ⟨flatEquiv (K := K) Q, ?_⟩
  rw [hQ, map_mul, map_pow, flatEquiv_X]
  rfl

theorem inactive_column_mem_lower (m L B s U w : ℕ) (D : ℕ → ℕ)
    (hw : 2 ≤ w) (x u₀ u₁ : K) (e : Fin 5 →₀ ℕ)
    (hB : 2*e 1+e 3 ≤ B) (hs : e 1 ≤ s)
    (hU : sourceMiddle e ≤ U) (hL : e 1+e 2+e 3+e 4 ≤ L)
    (hD : e 0+w*e 2+(w-1)*e 3+(w-2)*e 1 < D (e 1))
    (hinactive : ¬ (sourceMiddle e = U ∧ e 2 < m)) :
    localColumn m x u₀ u₁ e ∈
      SecondJetRelaxedSpace.source (K := K) m L B s (U-1) (fun h => (D h+B-1)/w) := by
  by_cases htop : sourceMiddle e = U
  · have hy : m ≤ e 2 := Nat.le_of_not_gt (fun hy => hinactive ⟨htop,hy⟩)
    have hword := truncated_local_monomial_mem x u₀ u₁ m L B s U w D hw e (1 : K) hB hs hU hL hD
    have hzero := truncated_local_monomial_mem x (0:K) (0:K) m L B s U w D hw e 1 hB hs hU hL hD
    let P := localize x u₀ u₁ (MvPolynomial.monomial e (1 : K)) -
      localize x 0 0 (MvPolynomial.monomial e (1 : K))
    have hEq : truncateOuter (K := K) m (flatEquiv (K := K) P) = localColumn m x u₀ u₁ e := by
      simp only [P, map_sub]
      change localColumn m x u₀ u₁ e - localColumn m x 0 0 e = _
      rw [zero_word_column_eq_zero m x e hy, sub_zero]
    rw [← hEq]
    have hdiff := (SecondJetRelaxedSpace.source (K := K) m L B s U (fun h => (D h+B-1)/w)).sub_mem hword hzero
    have hdiff' : truncateOuter (K := K) m (flatEquiv (K := K) P) ∈
        SecondJetRelaxedSpace.source (K := K) m L B s U (fun h => (D h+B-1)/w) := by
      simpa only [P,map_sub] using hdiff
    rw [← flatEquiv_truncFlat, SecondJetRelaxedSpace.mem_source_iff] at hdiff' ⊢
    simp only [AlgEquiv.symm_apply_apply] at hdiff' ⊢
    intro d hd
    obtain ⟨hAllowed, hB', hU', hcap⟩ := hdiff' d hd
    have hlower := local_difference_middle_lt x u₀ u₁ e d (support_truncFlat m P d hd).2
    exact ⟨hAllowed, hB', by unfold sourceMiddle at hlower htop; omega, hcap⟩
  · exact truncated_local_monomial_mem x u₀ u₁ m L B s (U-1) w D hw e (1:K) hB hs
      (by unfold sourceMiddle at hU htop; omega) hL hD

end

end ProximityPrize.SubmissionLower.K6833Residual
