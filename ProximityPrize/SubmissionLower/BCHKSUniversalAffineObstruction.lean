import ProximityPrize.SubmissionLower.BCHKSUniversalNumerator
import ProximityPrize.SubmissionLower.BCHKSBaseZAffine
import ProximityPrize.SubmissionLower.BCHKSYZFactorCap

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxHeartbeats 4000000

variable {F : Type} [Field F]

/-- The branch-independent cleared affine obstruction.  The coefficient
`num i` represents the `i`th implicit coefficient with denominator
`s^(denominatorExponent i)`. -/
noncomputable def universalAffineObstruction
    (num : ℕ → F[X][Y]) (s : F[X][Y]) (E k : ℕ) (dx u₀ u₁ : F) : F[X][Y] :=
  (∑ i ∈ Finset.range (k + 1),
      Polynomial.C (Polynomial.C (dx ^ i)) * num i *
        s ^ (E - FiniteHenselWeight.denominatorExponent i)) -
    Polynomial.C (Polynomial.C u₀ + Polynomial.X * Polynomial.C u₁) * s ^ E

lemma bivariate_degreeX_one :
    Polynomial.Bivariate.degreeX (1 : F[X][Y]) = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro i hi
  have hi0 : i = 0 := by
    by_contra hine
    exact (Polynomial.mem_support_iff.mp hi) (by simp [Polynomial.coeff_one, hine])
  subst i
  simp

lemma bivariate_degreeX_pow_le (p : F[X][Y]) (n : ℕ) :
    Polynomial.Bivariate.degreeX (p ^ n) ≤ n * Polynomial.Bivariate.degreeX p := by
  induction n with
  | zero => simpa [bivariate_degreeX_one]
  | succ n ih =>
      rw [pow_succ]
      calc
        Polynomial.Bivariate.degreeX (p ^ n * p) ≤
            Polynomial.Bivariate.degreeX (p ^ n) +
              Polynomial.Bivariate.degreeX p :=
          Polynomial.Bivariate.degreeX_mul_le _ _
        _ ≤ n * Polynomial.Bivariate.degreeX p +
              Polynomial.Bivariate.degreeX p := Nat.add_le_add_right ih _
        _ = (n + 1) * Polynomial.Bivariate.degreeX p := by ring

lemma bivariate_degreeX_C (p : F[X]) :
    Polynomial.Bivariate.degreeX (Polynomial.C p : F[X][Y]) = p.natDegree := by
  unfold Polynomial.Bivariate.degreeX
  by_cases hp : p = 0
  · subst p
    simp
  · rw [Polynomial.support_C hp]
    simp

lemma bivariate_degreeX_scalar_C (a : F) :
    Polynomial.Bivariate.degreeX (Polynomial.C (Polynomial.C a) : F[X][Y]) = 0 := by
  rw [bivariate_degreeX_C]
  simp

lemma bivariate_degreeX_affine_C_le (u₀ u₁ : F) :
    Polynomial.Bivariate.degreeX
      (Polynomial.C (Polynomial.C u₀ + Polynomial.X * Polynomial.C u₁) : F[X][Y]) ≤ 1 := by
  rw [bivariate_degreeX_C]
  calc
    (Polynomial.C u₀ + Polynomial.X * Polynomial.C u₁).natDegree ≤
        max (Polynomial.C u₀).natDegree
          (Polynomial.X * Polynomial.C u₁).natDegree := Polynomial.natDegree_add_le _ _
    _ ≤ 1 := by
      apply max_le
      · simp
      · calc
          (Polynomial.X * Polynomial.C u₁).natDegree ≤
              Polynomial.X.natDegree + (Polynomial.C u₁).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ 1 := by simp

lemma natDegree_pow_le (p : F[X][Y]) (n : ℕ) :
    (p ^ n).natDegree ≤ n * p.natDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      calc
        (p ^ n * p).natDegree ≤ (p ^ n).natDegree + p.natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ n * p.natDegree + p.natDegree := Nat.add_le_add_right ih _
        _ = (n + 1) * p.natDegree := by ring

lemma bivariate_degreeX_sub_le (p q : F[X][Y]) :
    Polynomial.Bivariate.degreeX (p - q) ≤
      max (Polynomial.Bivariate.degreeX p) (Polynomial.Bivariate.degreeX q) := by
  unfold Polynomial.Bivariate.degreeX
  apply Finset.sup_le
  intro i hi
  calc
    ((p - q).coeff i).natDegree = (p.coeff i - q.coeff i).natDegree := by
      rw [Polynomial.coeff_sub]
    _ ≤ max (p.coeff i).natDegree (q.coeff i).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ ≤ max (p.support.sup fun j ↦ (p.coeff j).natDegree)
        (q.support.sup fun j ↦ (q.coeff j).natDegree) := by
      exact max_le_max (Polynomial.Bivariate.coeff_natDegree_le_degreeX p i)
        (Polynomial.Bivariate.coeff_natDegree_le_degreeX q i)

/-- Degree contract for the universal affine obstruction.  The strict slope
caps `degY s≤d-1`, `degZ s≤D-1` absorb the extra affine factor `Z`.
The hypotheses on `num` are the exact output expected from the universal
numerator recurrence. -/
theorem universalAffineObstruction_degree_bounds
    (num : ℕ → F[X][Y]) (s : F[X][Y]) (E k d D : ℕ) (dx u₀ u₁ : F)
    (hE : E = FiniteHenselWeight.denominatorExponent k)
    (hk : 0 < k) (hd : 1 ≤ d) (hD : 1 ≤ D)
    (hsY : s.natDegree ≤ d - 1)
    (hsZ : Polynomial.Bivariate.degreeX s ≤ D - 1)
    (hnumY0 : (num 0).natDegree ≤ 1)
    (hnumZ0 : Polynomial.Bivariate.degreeX (num 0) ≤ 0)
    (hnumY : ∀ i, 0 < i → i ≤ k →
      (num i).natDegree ≤ FiniteHenselWeight.denominatorExponent i * d)
    (hnumZ : ∀ i, 0 < i → i ≤ k →
      Polynomial.Bivariate.degreeX (num i) ≤
        FiniteHenselWeight.denominatorExponent i * D) :
    (universalAffineObstruction num s E k dx u₀ u₁).natDegree ≤ E * d ∧
    Polynomial.Bivariate.degreeX (universalAffineObstruction num s E k dx u₀ u₁) ≤
      E * D := by
  have hEpos : 1 ≤ E := by
    rw [hE]
    simp [FiniteHenselWeight.denominatorExponent]
    omega
  have hexp (i : ℕ) (hi : i ≤ k) :
      FiniteHenselWeight.denominatorExponent i ≤ E := by
    rw [hE]
    exact denominatorExponent_mono hi
  let terms : ℕ → F[X][Y] := fun i ↦
    Polynomial.C (Polynomial.C (dx ^ i)) * num i *
      s ^ (E - FiniteHenselWeight.denominatorExponent i)
  have htermY : ∀ i ∈ Finset.range (k + 1), (terms i).natDegree ≤ E * d := by
    intro i hi
    have hik : i ≤ k := by simp only [Finset.mem_range] at hi; omega
    have heik := hexp i hik
    have hpow : (s ^ (E - FiniteHenselWeight.denominatorExponent i)).natDegree ≤
        (E - FiniteHenselWeight.denominatorExponent i) * (d - 1) :=
      (natDegree_pow_le s _).trans (Nat.mul_le_mul_left _ hsY)
    have hbase : (Polynomial.C (Polynomial.C (dx ^ i)) * num i).natDegree ≤
        (num i).natDegree := by
      simpa using Polynomial.natDegree_C_mul_le (Polynomial.C (dx ^ i)) (num i)
    calc
      (terms i).natDegree ≤
          (Polynomial.C (Polynomial.C (dx ^ i)) * num i).natDegree +
            (s ^ (E - FiniteHenselWeight.denominatorExponent i)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (num i).natDegree +
          (E - FiniteHenselWeight.denominatorExponent i) * (d - 1) :=
        Nat.add_le_add hbase hpow
      _ ≤ E * d := by
        by_cases hi0 : i = 0
        · subst i
          simp only [FiniteHenselWeight.denominatorExponent_zero, Nat.sub_zero]
          nlinarith [Nat.sub_add_cancel hd]
        · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
          have hn := hnumY i hipos hik
          nlinarith [Nat.add_sub_of_le heik, Nat.sub_add_cancel hd]
  have htermZ : ∀ i ∈ Finset.range (k + 1),
      Polynomial.Bivariate.degreeX (terms i) ≤ E * D := by
    intro i hi
    have hik : i ≤ k := by simp only [Finset.mem_range] at hi; omega
    have heik := hexp i hik
    have hpow : Polynomial.Bivariate.degreeX
        (s ^ (E - FiniteHenselWeight.denominatorExponent i)) ≤
        (E - FiniteHenselWeight.denominatorExponent i) * (D - 1) :=
      (bivariate_degreeX_pow_le s _).trans (Nat.mul_le_mul_left _ hsZ)
    have hscalar : Polynomial.Bivariate.degreeX
        (Polynomial.C (Polynomial.C (dx ^ i)) : F[X][Y]) = 0 :=
      bivariate_degreeX_scalar_C _
    have hbase : Polynomial.Bivariate.degreeX
        (Polynomial.C (Polynomial.C (dx ^ i)) * num i) ≤
          Polynomial.Bivariate.degreeX (num i) := by
      calc
        _ ≤ Polynomial.Bivariate.degreeX
              (Polynomial.C (Polynomial.C (dx ^ i)) : F[X][Y]) +
            Polynomial.Bivariate.degreeX (num i) :=
          Polynomial.Bivariate.degreeX_mul_le _ _
        _ = _ := by rw [hscalar, zero_add]
    calc
      Polynomial.Bivariate.degreeX (terms i) ≤
          Polynomial.Bivariate.degreeX
              (Polynomial.C (Polynomial.C (dx ^ i)) * num i) +
            Polynomial.Bivariate.degreeX
              (s ^ (E - FiniteHenselWeight.denominatorExponent i)) :=
        Polynomial.Bivariate.degreeX_mul_le _ _
      _ ≤ Polynomial.Bivariate.degreeX (num i) +
          (E - FiniteHenselWeight.denominatorExponent i) * (D - 1) :=
        Nat.add_le_add hbase hpow
      _ ≤ E * D := by
        by_cases hi0 : i = 0
        · subst i
          simp only [FiniteHenselWeight.denominatorExponent_zero, Nat.sub_zero]
          nlinarith [Nat.sub_add_cancel hD]
        · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
          have hn := hnumZ i hipos hik
          nlinarith [Nat.add_sub_of_le heik, Nat.sub_add_cancel hD]
  have hsumY : (∑ i ∈ Finset.range (k + 1), terms i).natDegree ≤ E * d :=
    YZFactorCap.natDegree_sum_le_of_forall _ _ _ htermY
  have hsumZ : Polynomial.Bivariate.degreeX
      (∑ i ∈ Finset.range (k + 1), terms i) ≤ E * D :=
    YZFactorCap.degreeX_sum_le_of_forall _ _ _ htermZ
  let affine : F[X][Y] :=
    Polynomial.C (Polynomial.C u₀ + Polynomial.X * Polynomial.C u₁)
  have haffY : (affine * s ^ E).natDegree ≤ E * d := by
    calc
      (affine * s ^ E).natDegree ≤ affine.natDegree + (s ^ E).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 0 + E * (d - 1) := by
        apply Nat.add_le_add
        · simpa only [affine, Polynomial.natDegree_C] using (Nat.le_refl 0)
        · exact (natDegree_pow_le s E).trans (Nat.mul_le_mul_left E hsY)
      _ ≤ E * d := by
        simp only [zero_add]
        exact Nat.mul_le_mul_left E (Nat.sub_le d 1)
  have haffZ : Polynomial.Bivariate.degreeX (affine * s ^ E) ≤ E * D := by
    calc
      Polynomial.Bivariate.degreeX (affine * s ^ E) ≤
          Polynomial.Bivariate.degreeX affine +
            Polynomial.Bivariate.degreeX (s ^ E) :=
        Polynomial.Bivariate.degreeX_mul_le _ _
      _ ≤ 1 + E * (D - 1) := by
        apply Nat.add_le_add
        · exact bivariate_degreeX_affine_C_le u₀ u₁
        · exact (bivariate_degreeX_pow_le s E).trans
            (Nat.mul_le_mul_left E hsZ)
      _ ≤ E * D := by nlinarith [Nat.sub_add_cancel hD]
  unfold universalAffineObstruction
  change ((∑ i ∈ Finset.range (k + 1), terms i) - affine * s ^ E).natDegree ≤
      E * d ∧ Polynomial.Bivariate.degreeX
        ((∑ i ∈ Finset.range (k + 1), terms i) - affine * s ^ E) ≤ E * D
  exact ⟨(Polynomial.natDegree_sub_le _ _).trans (max_le hsumY haffY),
    (bivariate_degreeX_sub_le _ _).trans (max_le hsumZ haffZ)⟩

/-- Common-root specialization of the universal obstruction. -/
theorem biEval_universalAffineObstruction_eq_zero
    (num : ℕ → F[X][Y]) (s : F[X][Y]) (E k : ℕ) (dx u₀ u₁ z y : F)
    (c : ℕ → F)
    (hexp : ∀ i, i ≤ k → FiniteHenselWeight.denominatorExponent i ≤ E)
    (hnum : ∀ i, i ≤ k →
      biEval (num i) y z = c i * biEval s y z ^
        FiniteHenselWeight.denominatorExponent i)
    (haffine : (∑ i ∈ Finset.range (k + 1), c i * dx ^ i) = u₀ + z * u₁) :
    biEval (universalAffineObstruction num s E k dx u₀ u₁) y z = 0 := by
  let φ : F[X][Y] →+* F :=
    (Polynomial.evalRingHom y).comp
      (Polynomial.mapRingHom (Polynomial.evalRingHom z))
  change φ (universalAffineObstruction num s E k dx u₀ u₁) = 0
  have hconst (a : F) : φ (Polynomial.C (Polynomial.C a)) = a := by
    simp [φ, RingHom.comp_apply]
  have haffC : φ (Polynomial.C
      (Polynomial.C u₀ + Polynomial.X * Polynomial.C u₁)) = u₀ + z * u₁ := by
    change Polynomial.eval y (Polynomial.map (Polynomial.evalRingHom z)
      (Polynomial.C (Polynomial.C u₀ + Polynomial.X * Polynomial.C u₁))) = _
    simp only [Polynomial.map_C, Polynomial.coe_evalRingHom, Polynomial.eval_C,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  unfold universalAffineObstruction
  rw [map_sub, map_sum, map_mul, map_pow]
  simp only [map_mul, map_pow]
  simp_rw [hconst]
  rw [haffC]
  rw [show (∑ i ∈ Finset.range (k + 1),
      dx ^ i * φ (num i) * φ s ^
          (E - FiniteHenselWeight.denominatorExponent i)) =
      (∑ i ∈ Finset.range (k + 1), c i * dx ^ i) * φ s ^ E by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := by simp only [Finset.mem_range] at hi; omega
    have hni : φ (num i) = c i * φ s ^
        FiniteHenselWeight.denominatorExponent i := by
      change Polynomial.eval y (Polynomial.map (Polynomial.evalRingHom z) (num i)) =
        c i * Polynomial.eval y (Polynomial.map (Polynomial.evalRingHom z) s) ^
          FiniteHenselWeight.denominatorExponent i
      exact hnum i hik
    rw [hni]
    have he := Nat.add_sub_of_le (hexp i hik)
    calc
      dx ^ i * (c i * φ s ^ FiniteHenselWeight.denominatorExponent i) *
          φ s ^ (E - FiniteHenselWeight.denominatorExponent i) =
          c i * dx ^ i * (φ s ^ FiniteHenselWeight.denominatorExponent i *
            φ s ^ (E - FiniteHenselWeight.denominatorExponent i)) := by ring
      _ = c i * dx ^ i * φ s ^ E := by rw [← pow_add, he]]
  rw [haffine]
  ring

/-! ## Relation to the existing regular numerator -/

/-- If the abstract universal numerators represent the existing finite-Hensel
coefficients after evaluation at the generic root, the old explicit regular
base-Z numerator is precisely a branch-dependent power of `W` times the image
of the branch-independent obstruction.  This lets the existing final alignment
consumer be reused after the new raw-resultant selection. -/
theorem embedding_explicitBaseZGammaDifferenceRegular_eq_universalAffineObstruction
    {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (x₀ dx u₀ u₁ : F) (R : F[X][X][Y])
    (hHyp : HenselNumerators.Hypotheses x₀ R H)
    (hzeta : HenselNumerators.zeta R x₀ H ≠ 0)
    (N k : ℕ) (hkN : k ≤ N)
    (num : ℕ → F[X][Y]) (s : F[X][Y])
    (E : ℕ) (hE : E = FiniteHenselWeight.denominatorExponent k)
    (hs : Polynomial.eval₂ (liftToFunctionField (H := H))
        (initialValue (H := H)) s = HenselNumerators.zeta R x₀ H)
    (hnum : ∀ i, i ≤ k →
      Polynomial.eval₂ (liftToFunctionField (H := H))
          (initialValue (H := H)) (num i) =
        finiteAlpha (R := R) (H := H) x₀ N i *
          HenselNumerators.zeta R x₀ H ^
            FiniteHenselWeight.denominatorExponent i) :
    embeddingOf𝒪Into𝕃 H
        (explicitBaseZGammaDifferenceRegular x₀ dx u₀ u₁
          R hHyp hzeta N k hkN) =
      Wfield (H := H) ^
          (k + 1 + (R.natDegree - 2) * E) *
        Polynomial.eval₂ (liftToFunctionField (H := H))
          (initialValue (H := H))
          (universalAffineObstruction num s E k dx u₀ u₁) := by
  let φ : F[X][Y] →+* 𝕃 H := Polynomial.eval₂RingHom
    (liftToFunctionField (H := H)) (initialValue (H := H))
  have hphi (p : F[X][Y]) : φ p = Polynomial.eval₂
      (liftToFunctionField (H := H)) (initialValue (H := H)) p := rfl
  have hconst (a : F) : φ (Polynomial.C (Polynomial.C a)) =
      fieldTo𝕃 (H := H) a := by
    simp [φ, fieldTo𝕃]
  have haffC : φ (Polynomial.C
      (Polynomial.C u₀ + Polynomial.X * Polynomial.C u₁)) =
      fieldTo𝕃 (H := H) u₀ +
        liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (H := H) u₁ := by
    simp [φ, fieldTo𝕃]
    ring
  let diff : 𝕃 H :=
    evaluatedFiniteAlpha (R := R) (H := H) x₀ dx N k -
      (fieldTo𝕃 (H := H) u₀ +
        liftToFunctionField (H := H) Polynomial.X * fieldTo𝕃 (H := H) u₁)
  have hG : φ (universalAffineObstruction num s E k dx u₀ u₁) =
      diff * HenselNumerators.zeta R x₀ H ^ E := by
    unfold universalAffineObstruction
    rw [map_sub, map_sum, map_mul, map_pow]
    simp only [map_mul, map_pow]
    simp_rw [hconst]
    rw [haffC]
    have hsphi : φ s = HenselNumerators.zeta R x₀ H := by
      simpa only [hphi] using hs
    rw [hsphi]
    have hsum : (∑ i ∈ Finset.range (k + 1),
        fieldTo𝕃 (H := H) dx ^ i * φ (num i) *
          HenselNumerators.zeta R x₀ H ^
            (E - FiniteHenselWeight.denominatorExponent i)) =
        evaluatedFiniteAlpha (R := R) (H := H) x₀ dx N k *
          HenselNumerators.zeta R x₀ H ^ E := by
      unfold evaluatedFiniteAlpha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := by simp only [Finset.mem_range] at hi; omega
      have hni : φ (num i) = finiteAlpha (R := R) (H := H) x₀ N i *
          HenselNumerators.zeta R x₀ H ^
            FiniteHenselWeight.denominatorExponent i := by
        simpa only [hphi] using hnum i hik
      rw [hni]
      have hei : FiniteHenselWeight.denominatorExponent i ≤ E := by
        rw [hE]
        exact denominatorExponent_mono hik
      have he := Nat.add_sub_of_le hei
      calc
        fieldTo𝕃 (H := H) dx ^ i *
            (finiteAlpha (R := R) (H := H) x₀ N i *
              HenselNumerators.zeta R x₀ H ^
                FiniteHenselWeight.denominatorExponent i) *
              HenselNumerators.zeta R x₀ H ^
                (E - FiniteHenselWeight.denominatorExponent i) =
            finiteAlpha (R := R) (H := H) x₀ N i *
              fieldTo𝕃 (H := H) dx ^ i *
              (HenselNumerators.zeta R x₀ H ^
                  FiniteHenselWeight.denominatorExponent i *
                HenselNumerators.zeta R x₀ H ^
                  (E - FiniteHenselWeight.denominatorExponent i)) := by ring
        _ = finiteAlpha (R := R) (H := H) x₀ N i *
              fieldTo𝕃 (H := H) dx ^ i *
              HenselNumerators.zeta R x₀ H ^ E := by
            rw [← pow_add, he]
    rw [hsum]
    dsimp only [diff]
    ring
  calc
    embeddingOf𝒪Into𝕃 H
        (explicitBaseZGammaDifferenceRegular x₀ dx u₀ u₁
          R hHyp hzeta N k hkN) =
        diff * commonDenominator (R := R) (H := H) x₀ hHyp k := by
      simpa only [diff] using
        embedding_explicitBaseZGammaDifferenceRegular x₀ dx u₀ u₁
          R hHyp hzeta N k hkN
    _ = Wfield (H := H) ^ (k + 1 + (R.natDegree - 2) * E) *
        φ (universalAffineObstruction num s E k dx u₀ u₁) := by
      rw [hG]
      unfold commonDenominator
      rw [etaField_eq]
      rw [hE]
      have hpow : Wfield (H := H) ^
          (k + 1 + (R.natDegree - 2) * FiniteHenselWeight.denominatorExponent k) =
          Wfield (H := H) ^ (k + 1) *
            (Wfield (H := H) ^ (R.natDegree - 2)) ^
              FiniteHenselWeight.denominatorExponent k := by
        rw [pow_add, pow_mul]
      rw [hpow, mul_pow]
      ring
    _ = _ := by rfl

end ProximityPrize.SubmissionLower


