import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSingularDegreeBounds

/-!
# Exact R-coefficient tools for reduced contact-Taylor numerators

All coefficients are lifted into the original four-variable polynomial ring.
The degree cancellation below does not divide by a leading coefficient.
-/

namespace ProximityPrize.SubmissionLower.ContactReducedCoefficient6643Research

open ContactSingularAuxiliary ContactSingularDegreeBounds ContactFactorCaps

noncomputable section

variable {K : Type*} [Field K]

theorem embedCoefficients_injective : Function.Injective (embedCoefficients K) := by
  intro P Q h
  exact Polynomial.C_injective ((collectR K).symm.injective h)

@[simp] theorem liftedCoefficient_zero (n : ℕ) :
    liftedCoefficient (0 : MvPolynomial (Fin 4) K) n = 0 := by
  simp [liftedCoefficient]

@[simp] theorem liftedCoefficient_add (P Q : MvPolynomial (Fin 4) K) (n : ℕ) :
    liftedCoefficient (P + Q) n = liftedCoefficient P n + liftedCoefficient Q n := by
  simp [liftedCoefficient]

@[simp] theorem liftedCoefficient_sub (P Q : MvPolynomial (Fin 4) K) (n : ℕ) :
    liftedCoefficient (P - Q) n = liftedCoefficient P n - liftedCoefficient Q n := by
  simp [liftedCoefficient]

@[simp] theorem liftedCoefficient_neg (P : MvPolynomial (Fin 4) K) (n : ℕ) :
    liftedCoefficient (-P) n = -liftedCoefficient P n := by
  simp [liftedCoefficient]

theorem liftedCoefficient_eq_zero_iff (P : MvPolynomial (Fin 4) K) (n : ℕ) :
    liftedCoefficient P n = 0 ↔ (collectR K P).coeff n = 0 := by
  change embedCoefficients K ((collectR K P).coeff n) = 0 ↔ _
  rw [← map_zero (embedCoefficients K), embedCoefficients_injective.eq_iff]

theorem liftedCoefficient_eq_zero_of_degree_lt (P : MvPolynomial (Fin 4) K)
    (n : ℕ) (hP : P.degreeOf 2 < n) : liftedCoefficient P n = 0 := by
  apply (liftedCoefficient_eq_zero_iff P n).mpr
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [collectR_natDegree])

theorem collectR_X_R :
    collectR K (MvPolynomial.X (2 : Fin 4)) = Polynomial.X := by
  simp [collectR, MvPolynomial.renameEquiv_apply,
    Equiv.optionSubtypeNe_symm_apply]

theorem collectR_pderiv_R (P : MvPolynomial (Fin 4) K) :
    collectR K (MvPolynomial.pderiv (2 : Fin 4) P) = (collectR K P).derivative := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp [collectR, MvPolynomial.renameEquiv_apply]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      by_cases hi : i = 2
      · subst i
        simp [map_mul, collectR_X_R, Polynomial.derivative_mul, hP]
        ring
      · have hX := collectR_X_other (K := K) (⟨i, hi⟩ : RemainingCoordinates)
        simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_of_ne hi,
          mul_zero, add_zero, map_mul, hX, Polynomial.derivative_mul,
          Polynomial.derivative_C, mul_zero, add_zero, hP]

theorem liftedCoefficient_pderiv_R (P : MvPolynomial (Fin 4) K) (n : ℕ) :
    liftedCoefficient (MvPolynomial.pderiv (2 : Fin 4) P) n =
      MvPolynomial.C ((n + 1 : ℕ) : K) * liftedCoefficient P (n + 1) := by
  unfold liftedCoefficient
  rw [collectR_pderiv_R, Polynomial.coeff_derivative, map_mul]
  simp only [map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one]
  ring

private theorem optionCoefficient_pderiv_some {σ : Type*}
    (P : MvPolynomial (Option σ) K) (i : σ) (n : ℕ) :
    (MvPolynomial.optionEquivLeft K σ (MvPolynomial.pderiv (some i) P)).coeff n =
      MvPolynomial.pderiv i ((MvPolynomial.optionEquivLeft K σ P).coeff n) := by
  classical
  ext e
  rw [MvPolynomial.optionEquivLeft_coeff_coeff, MvPolynomial.coeff_pderiv,
    MvPolynomial.coeff_pderiv, MvPolynomial.optionEquivLeft_coeff_coeff]
  have he : e.optionElim n + Finsupp.single (some i) 1 =
      (e + Finsupp.single i 1).optionElim n := by
    ext j
    cases j with
    | none => simp
    | some j =>
        simp only [Finsupp.add_apply, Finsupp.optionElim_apply_some]
        rw [Finsupp.single_apply_left
          (show Function.Injective (some : σ → Option σ) from fun _ _ h => Option.some.inj h)]
  rw [he, Finsupp.optionElim_apply_some]

theorem liftedCoefficient_pderiv_other (P : MvPolynomial (Fin 4) K)
    (i : Fin 4) (hi : i ≠ 2) (n : ℕ) :
    liftedCoefficient (MvPolynomial.pderiv i P) n =
      MvPolynomial.pderiv i (liftedCoefficient P n) := by
  have hindex : (Equiv.optionSubtypeNe (2 : Fin 4)).symm i = some ⟨i, hi⟩ := by
    simp [Equiv.optionSubtypeNe_symm_apply, hi]
  have hrename :
      MvPolynomial.rename (Equiv.optionSubtypeNe (2 : Fin 4)).symm
        (MvPolynomial.pderiv i P) =
      MvPolynomial.pderiv (some (⟨i, hi⟩ : RemainingCoordinates))
        (MvPolynomial.rename (Equiv.optionSubtypeNe (2 : Fin 4)).symm P) := by
    rw [← MvPolynomial.pderiv_rename
      (Equiv.optionSubtypeNe (2 : Fin 4)).symm.injective i P, hindex]
  have hc : (collectR K (MvPolynomial.pderiv i P)).coeff n =
      MvPolynomial.pderiv (⟨i, hi⟩ : RemainingCoordinates) ((collectR K P).coeff n) := by
    change (MvPolynomial.optionEquivLeft K RemainingCoordinates
      (MvPolynomial.rename (Equiv.optionSubtypeNe (2 : Fin 4)).symm
        (MvPolynomial.pderiv i P))).coeff n = _
    rw [hrename, optionCoefficient_pderiv_some]
    rfl
  unfold liftedCoefficient
  rw [hc, embedCoefficients_eq_rename, embedCoefficients_eq_rename]
  exact (MvPolynomial.pderiv_rename Subtype.val_injective
    (⟨i, hi⟩ : RemainingCoordinates) ((collectR K P).coeff n)).symm

theorem liftedCoefficient_pderiv_R_top (P : MvPolynomial (Fin 4) K) (a : ℕ)
    (ha : 0 < a) :
    liftedCoefficient (MvPolynomial.pderiv (2 : Fin 4) P) (a - 1) =
      MvPolynomial.C (a : K) * liftedCoefficient P a := by
  simpa only [Nat.sub_add_cancel ha] using liftedCoefficient_pderiv_R P (a - 1)

theorem liftedCoefficient_mul_top (P Q : MvPolynomial (Fin 4) K) (a b : ℕ)
    (hP : P.degreeOf 2 ≤ a) (hQ : Q.degreeOf 2 ≤ b) :
    liftedCoefficient (P * Q) (a + b) =
      liftedCoefficient P a * liftedCoefficient Q b := by
  unfold liftedCoefficient
  rw [map_mul, Polynomial.coeff_mul_add_eq_of_natDegree_le
    (by rwa [collectR_natDegree]) (by rwa [collectR_natDegree]), map_mul]

theorem liftedCoefficient_zero_degree (P : MvPolynomial (Fin 4) K)
    (hP : P.degreeOf 2 = 0) : liftedCoefficient P 0 = P := by
  have hC : collectR K P = Polynomial.C ((collectR K P).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (by rwa [collectR_natDegree])
  change (collectR K).symm (Polynomial.C ((collectR K P).coeff 0)) = P
  rw [← hC, AlgEquiv.symm_apply_apply]

theorem liftedCoefficient_mul_degree_zero_left (P Q : MvPolynomial (Fin 4) K)
    (n : ℕ) (hP : P.degreeOf 2 = 0) :
    liftedCoefficient (P * Q) n = P * liftedCoefficient Q n := by
  have hC : collectR K P = Polynomial.C ((collectR K P).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (by rwa [collectR_natDegree])
  unfold liftedCoefficient
  rw [map_mul, hC, Polynomial.coeff_C_mul, map_mul]
  change liftedCoefficient P 0 * _ = _
  rw [liftedCoefficient_zero_degree P hP]

@[simp] theorem liftedCoefficient_C_mul (c : K) (P : MvPolynomial (Fin 4) K)
    (n : ℕ) : liftedCoefficient (MvPolynomial.C c * P) n =
      MvPolynomial.C c * liftedCoefficient P n :=
  liftedCoefficient_mul_degree_zero_left _ P n (MvPolynomial.degreeOf_C c 2)

@[simp] theorem liftedCoefficient_natCast_mul (c : ℕ)
    (P : MvPolynomial (Fin 4) K) (n : ℕ) :
    liftedCoefficient ((c : MvPolynomial (Fin 4) K) * P) n =
      (c : MvPolynomial (Fin 4) K) * liftedCoefficient P n := by
  simpa only [map_natCast] using liftedCoefficient_C_mul (c : K) P n

theorem liftedCoefficient_X_R_pow (n : ℕ) :
    liftedCoefficient ((MvPolynomial.X (2 : Fin 4) : MvPolynomial (Fin 4) K) ^ n) n =
      1 := by
  simp [liftedCoefficient, map_pow, collectR_X_R]

theorem liftedCoefficient_X_R_mul (P : MvPolynomial (Fin 4) K) (n : ℕ) :
    liftedCoefficient (MvPolynomial.X (2 : Fin 4) * P) (n + 1) =
      liftedCoefficient P n := by
  unfold liftedCoefficient
  rw [map_mul, collectR_X_R, Polynomial.coeff_X_mul]

/-- The original monomial has exactly the extracted R exponent, and every
other coordinate is unchanged. -/
theorem liftedCoefficient_support_exact
    (P : MvPolynomial (Fin 4) K) (n : ℕ) (e : Fin 4 →₀ ℕ)
    (he : e ∈ (liftedCoefficient P n).support) :
    ∃ d ∈ P.support, d 2 = n ∧ e 2 = 0 ∧ ∀ i, i ≠ 2 → e i = d i := by
  classical
  have heR : e 2 = 0 := by
    have hh := MvPolynomial.monomial_le_degreeOf (2 : Fin 4) he
    rw [liftedCoefficient_R_degree] at hh
    omega
  change e ∈ (embedCoefficients K ((collectR K P).coeff n)).support at he
  rw [embedCoefficients_eq_rename,
    MvPolynomial.support_rename_of_injective Subtype.val_injective] at he
  obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp he
  have hopt : u.optionElim n ∈
      (MvPolynomial.rename (Equiv.optionSubtypeNe (2 : Fin 4)).symm P).support :=
    (MvPolynomial.mem_support_coeff_optionEquivLeft (R := K)).mp hu
  rw [MvPolynomial.support_rename_of_injective
    (Equiv.optionSubtypeNe (2 : Fin 4)).symm.injective] at hopt
  obtain ⟨d, hd, hdu⟩ := Finset.mem_image.mp hopt
  refine ⟨d, hd, ?_, heR, ?_⟩
  · have huv := congrArg
      (fun f : Option RemainingCoordinates →₀ ℕ =>
        f ((Equiv.optionSubtypeNe (2 : Fin 4)).symm 2)) hdu
    rw [Finsupp.mapDomain_apply (Equiv.optionSubtypeNe (2 : Fin 4)).symm.injective] at huv
    simpa [Equiv.optionSubtypeNe_symm_apply] using huv
  · intro i hi
    have hev : e i = u ⟨i, hi⟩ := by
      rw [← heu]
      exact Finsupp.mapDomain_apply Subtype.val_injective u ⟨i, hi⟩
    have huv := congrArg
      (fun f : Option RemainingCoordinates →₀ ℕ =>
        f ((Equiv.optionSubtypeNe (2 : Fin 4)).symm i)) hdu
    rw [Finsupp.mapDomain_apply (Equiv.optionSubtypeNe (2 : Fin 4)).symm.injective] at huv
    have hindex : (Equiv.optionSubtypeNe (2 : Fin 4)).symm i = some ⟨i, hi⟩ := by
      simp [Equiv.optionSubtypeNe_symm_apply, hi]
    rw [hindex, Finsupp.optionElim_apply_some] at huv
    exact hev.trans huv.symm

/-- A nonzero coefficient loses the full weight of its extracted R power. -/
theorem liftedCoefficient_weight_add_le (weights : Fin 4 → ℕ)
    (P : MvPolynomial (Fin 4) K) (n : ℕ) (hn : liftedCoefficient P n ≠ 0) :
    MvPolynomial.weightedTotalDegree weights (liftedCoefficient P n) + n * weights 2 ≤
      MvPolynomial.weightedTotalDegree weights P := by
  classical
  obtain ⟨e, he, hmax⟩ := Finset.exists_mem_eq_sup
    (liftedCoefficient P n).support (MvPolynomial.support_nonempty.mpr hn)
    (Finsupp.weight weights)
  obtain ⟨d, hd, hdR, heR, heq⟩ := liftedCoefficient_support_exact P n e he
  have hw : Finsupp.weight weights e + n * weights 2 = Finsupp.weight weights d := by
    rw [weight_fin4, weight_fin4, hdR, heR,
      heq 0 (by decide), heq 1 (by decide), heq 3 (by decide)]
    omega
  change (liftedCoefficient P n).support.sup (Finsupp.weight weights) + _ ≤ _
  rw [hmax, hw]
  exact MvPolynomial.le_weightedTotalDegree weights hd

theorem liftedCoefficient_weight_le_sub (weights : Fin 4 → ℕ)
    (P : MvPolynomial (Fin 4) K) (n : ℕ) :
    MvPolynomial.weightedTotalDegree weights (liftedCoefficient P n) ≤
      MvPolynomial.weightedTotalDegree weights P - n * weights 2 := by
  by_cases hn : liftedCoefficient P n = 0
  · simp [hn, MvPolynomial.weightedTotalDegree]
  · have h := liftedCoefficient_weight_add_le weights P n hn
    omega

theorem liftedCoefficient_eq_zero_of_weight_lt (weights : Fin 4 → ℕ)
    (P : MvPolynomial (Fin 4) K) (n : ℕ)
    (hP : MvPolynomial.weightedTotalDegree weights P < n * weights 2) :
    liftedCoefficient P n = 0 := by
  by_contra hn
  have h := liftedCoefficient_weight_add_le weights P n hn
  omega

/-- Vanishing of the one possible top coefficient removes that degree,
including when the polynomial itself becomes zero. -/
theorem degreeR_le_sub_one_of_top_zero (P : MvPolynomial (Fin 4) K) (t : ℕ)
    (ht : 0 < t) (hP : P.degreeOf 2 ≤ t) (hzero : liftedCoefficient P t = 0) :
    P.degreeOf 2 ≤ t - 1 := by
  rw [← collectR_natDegree]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases heq : n = t
  · subst n
    exact (liftedCoefficient_eq_zero_iff P t).mp hzero
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (by rw [collectR_natDegree]; omega)

theorem degreeR_sub_cancel_top (W F q : MvPolynomial (Fin 4) K) (t s k : ℕ)
    (ht : 0 < t) (hW : W.degreeOf 2 ≤ t) (hF : F.degreeOf 2 ≤ s)
    (hq : q.degreeOf 2 = 0) (hks : k + s = t)
    (hcoeff : liftedCoefficient W t = q * liftedCoefficient F s) :
    (W - q * MvPolynomial.X (2 : Fin 4) ^ k * F).degreeOf 2 ≤ t - 1 := by
  have hR : ((MvPolynomial.X (2 : Fin 4) : MvPolynomial (Fin 4) K) ^ k).degreeOf 2 ≤ k := by
    simpa using MvPolynomial.degreeOf_pow_le (2 : Fin 4)
      (MvPolynomial.X (2 : Fin 4) : MvPolynomial (Fin 4) K) k
  have hqR : (q * MvPolynomial.X (2 : Fin 4) ^ k).degreeOf 2 ≤ k := by
    have h := MvPolynomial.degreeOf_mul_le (2 : Fin 4) q
      ((MvPolynomial.X (2 : Fin 4)) ^ k)
    omega
  have hprod : (q * MvPolynomial.X (2 : Fin 4) ^ k * F).degreeOf 2 ≤ t := by
    have h := ContactTaylorNumerators.degree_mul_bound (2 : Fin 4) hqR hF
    omega
  apply degreeR_le_sub_one_of_top_zero _ t ht
    (ContactTaylorNumerators.degree_sub_bound (2 : Fin 4) hW hprod)
  rw [liftedCoefficient_sub, ← hks,
    liftedCoefficient_mul_top _ F k s hqR hF,
    liftedCoefficient_mul_degree_zero_left _ _ k hq,
    liftedCoefficient_X_R_pow, mul_one, hks, hcoeff, sub_self]


end
end ProximityPrize.SubmissionLower.ContactReducedCoefficient6643Research

