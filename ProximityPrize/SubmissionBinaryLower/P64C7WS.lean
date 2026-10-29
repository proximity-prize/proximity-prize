import ProximityPrize.SubmissionBinaryLower.P64FoundTrunc

/-!
# Lemma WS (dlt.md section 2): `V`-degrees below `ν` span modulo `(U^s, V^s, R)`

In line coordinates `S = R(x_i + U, y_i(Z) + V, Z)` over a field `K` (dlt.md uses `K = F(Z)`),
with `S(0, V) = V^ν · R''(V)` and `R''(0)` a unit. Every bivariate is congruent modulo
`J = (U^s, V^s, S)` to one supported on `U^a V^b` with `a < s` and `b < min(ν, s)`.

Proof: `V^ν ≡ -U·w·S₁ (mod J)` where `w R'' ≡ 1 (mod V^s)` and `S = S(0, V) + U·S₁`, then
descending induction on the `U`-exponent.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7

open Polynomial P64Found

variable {K : Type*} [CommRing K]

/-- The ideal `(U^s, V^s, S)`. -/
noncomputable def boxIdeal (s : ℕ) (S : Polynomial (Polynomial K)) : Ideal (Polynomial (Polynomial K)) :=
  Ideal.span {C (X ^ s), X ^ s, S}

/-- `g` is supported on `U^a V^b` with `a < s` and `b < t`. -/
def InBox (s t : ℕ) (g : Polynomial (Polynomial K)) : Prop :=
  ∀ a b, (s ≤ a ∨ t ≤ b) → (g.coeff b).coeff a = 0

lemma inBox_zero (s t : ℕ) : InBox s t (0 : Polynomial (Polynomial K)) := by
  intro a b _
  simp

lemma InBox.add {s t : ℕ} {f g : Polynomial (Polynomial K)} (hf : InBox s t f)
    (hg : InBox s t g) : InBox s t (f + g) := by
  intro a b h
  simp [hf a b h, hg a b h]

lemma U_pow_mem (s : ℕ) (S : Polynomial (Polynomial K)) : C (X ^ s) ∈ boxIdeal s S :=
  Ideal.subset_span (by simp)

lemma V_pow_mem (s : ℕ) (S : Polynomial (Polynomial K)) :
    (X ^ s : Polynomial (Polynomial K)) ∈ boxIdeal s S :=
  Ideal.subset_span (by simp)

lemma S_mem (s : ℕ) (S : Polynomial (Polynomial K)) : S ∈ boxIdeal s S :=
  Ideal.subset_span (by simp)

lemma U_pow_mul_mem (s : ℕ) (S : Polynomial (Polynomial K)) {a : ℕ} (ha : s ≤ a)
    (f : Polynomial (Polynomial K)) : C (X ^ a) * f ∈ boxIdeal s S := by
  have : (C (X ^ a) : Polynomial (Polynomial K)) = C (X ^ s) * C (X ^ (a - s)) := by
    rw [← C_mul, ← pow_add, Nat.add_sub_cancel' ha]
  rw [this, mul_assoc]
  exact Ideal.mul_mem_right _ _ (U_pow_mem s S)

lemma atU0_eq_map (f : Polynomial (Polynomial K)) :
    atU0 f = (f.map (constantCoeff (R := K))).map C := by
  simp [atU0, Polynomial.map_map]

/-- `V^t ≡ -U·B (mod J)` with `t = min(ν, s)`. -/
lemma exists_V_pow_add_U_mul_mem (s ν : ℕ) (S : Polynomial (Polynomial K)) (R'' : K[X])
    (hS0 : S.map (constantCoeff (R := K)) = X ^ ν * R'') (hu : IsUnit (R''.coeff 0)) :
    ∃ B, (X ^ min ν s : Polynomial (Polynomial K)) + C X * B ∈ boxIdeal s S := by
  by_cases hνs : ν ≤ s
  · rw [min_eq_left hνs]
    obtain ⟨w, q, hq⟩ := exists_mul_sub_one_X_pow_dvd hu s
    obtain ⟨S₁, hS₁⟩ := exists_eq_atU0_add_U_mul S
    refine ⟨(w.map C) * S₁, ?_⟩
    -- X^ν = X^ν (1 - w R'') + w X^ν R'' and w X^ν R'' = w·S(0,V) = w (S - U S₁)
    have hlift : atU0 S = (X ^ ν : Polynomial (Polynomial K)) * R''.map C := by
      rw [atU0_eq_map, hS0, Polynomial.map_mul, Polynomial.map_pow, map_X]
    have key : (X ^ ν : Polynomial (Polynomial K)) + C X * ((w.map C) * S₁) =
        -(X ^ ν * q.map C * X ^ s) + (w.map C) * S := by
      have hwq : (w.map C) * (R''.map C) - 1 = (X ^ s * q).map C := by
        rw [← hq, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one]
      have hX : ((X : K[X]) ^ s * q).map C = (X ^ s : Polynomial (Polynomial K)) * q.map C := by
        rw [Polynomial.map_mul, Polynomial.map_pow, map_X]
      rw [hX] at hwq
      have hS' : S = (X ^ ν : Polynomial (Polynomial K)) * R''.map C + C X * S₁ := by
        rw [← hlift]; exact hS₁
      rw [hS']
      linear_combination (-(X ^ ν : Polynomial (Polynomial K))) * hwq
    rw [key]
    exact add_mem (neg_mem (Ideal.mul_mem_left _ _ (V_pow_mem s S)))
      (Ideal.mul_mem_left _ _ (S_mem s S))
  · rw [min_eq_right (by omega)]
    exact ⟨0, by simpa using V_pow_mem s S⟩

/-- Lemma WS. -/
theorem exists_inBox_sub_mem [Nontrivial K] (s ν : ℕ) (S : Polynomial (Polynomial K)) (R'' : K[X])
    (hS0 : S.map (constantCoeff (R := K)) = X ^ ν * R'') (hu : IsUnit (R''.coeff 0))
    (f : Polynomial (Polynomial K)) :
    ∃ g, InBox s (min ν s) g ∧ f - g ∈ boxIdeal s S := by
  obtain ⟨B, hB⟩ := exists_V_pow_add_U_mul_mem s ν S R'' hS0 hu
  set t := min ν s
  have main : ∀ k a (f : Polynomial (Polynomial K)), s ≤ a + k →
      ∃ g, InBox s t g ∧ C (X ^ a) * f - g ∈ boxIdeal s S := by
    intro k
    induction k with
    | zero =>
        intro a f ha
        exact ⟨0, inBox_zero s t, by rw [sub_zero]; exact U_pow_mul_mem s S (by omega) f⟩
    | succ k ih =>
        intro a f ha
        by_cases hsa : s ≤ a
        · exact ⟨0, inBox_zero s t, by rw [sub_zero]; exact U_pow_mul_mem s S hsa f⟩
        obtain ⟨f₁, hf₁⟩ := exists_eq_atU0_add_U_mul f
        set f0 := f.map (constantCoeff (R := K))
        set lo := (f0 %ₘ X ^ t).map (C : K →+* K[X])
        set hi := (f0 /ₘ X ^ t).map (C : K →+* K[X])
        have hsplit : atU0 f = lo + X ^ t * hi := by
          have h0 := modByMonic_add_div f0 (X ^ t)
          rw [atU0_eq_map]
          change f0.map C = _
          conv_lhs => rw [← h0]
          simp [lo, hi, Polynomial.map_add, Polynomial.map_mul]
        obtain ⟨g', hg', hmem⟩ := ih (a + 1) (f₁ - B * hi) (by omega)
        refine ⟨C (X ^ a) * lo + g', ?_, ?_⟩
        · refine InBox.add ?_ hg'
          intro a' b hab
          rw [coeff_C_mul]
          have hlo : lo.coeff b = C ((f0 %ₘ X ^ t).coeff b) := by simp [lo, coeff_map]
          rw [hlo, mul_comm, coeff_C_mul, coeff_X_pow]
          rcases hab with hab | hab
          · have : a' ≠ a := by
              intro h; subst h
              omega
            simp [this]
          · have hdeg : ((f0 %ₘ X ^ t)).coeff b = 0 := by
              apply coeff_eq_zero_of_degree_lt
              calc (f0 %ₘ X ^ t).degree < (X ^ t : K[X]).degree :=
                    degree_modByMonic_lt _ (monic_X_pow t)
                _ ≤ t := degree_X_pow_le t
                _ ≤ b := by exact_mod_cast hab
            simp [hdeg]
        · have e : C (X ^ a) * f - (C (X ^ a) * lo + g') =
              (C (X ^ (a + 1)) * (f₁ - B * hi) - g') +
                C (X ^ a) * hi * (X ^ t + C X * B) := by
            rw [hf₁, hsplit, pow_succ, C_mul]
            ring
          rw [e]
          exact add_mem hmem (Ideal.mul_mem_left _ _ hB)
  obtain ⟨g, hg, hmem⟩ := main s 0 f (by omega)
  exact ⟨g, hg, by simpa using hmem⟩

end P64C7
end ProximityPrize.SubmissionBinaryLower
