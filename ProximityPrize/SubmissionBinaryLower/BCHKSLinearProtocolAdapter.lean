import ProximityPrize.SubmissionBinaryLower.BCHKSLinearResultantWitness
import ProximityPrize.SubmissionBinaryLower.BCHKSDegreeTwoSelectedFinal
import ProximityPrize.SubmissionBinaryLower.BCHKSLinearSelectedCore

namespace ProximityPrize.SubmissionBinaryLower

open ProximityPrize.Benchmark Polynomial
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000


private theorem natDegree_eval_affine_le_totalDegree
    {F : Type} [Field F] (S : F[X][X]) (a b : F) :
    (Polynomial.eval (Polynomial.C a + Polynomial.X * Polynomial.C b) S).natDegree ≤
      Polynomial.Bivariate.totalDegree S := by
  classical
  rw [Polynomial.eval_eq_sum_range]
  apply (Polynomial.natDegree_sum_le _ _).trans
  rw [Finset.fold_max_le]
  constructor
  · exact Nat.zero_le _
  intro i hi
  simp only [Function.comp_apply]
  have haff : (Polynomial.C a + Polynomial.X * Polynomial.C b : F[X]).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
      (Polynomial.natDegree_mul_le.trans (by simp)))
  have hpow : ((Polynomial.C a + Polynomial.X * Polynomial.C b : F[X]) ^ i).natDegree ≤ i := by
    calc
      _ ≤ i * (Polynomial.C a + Polynomial.X * Polynomial.C b : F[X]).natDegree :=
        Polynomial.natDegree_pow_le
      _ ≤ i * 1 := Nat.mul_le_mul_left i haff
      _ = i := by omega
  by_cases hc : S.coeff i = 0
  · simp [hc]
  · have his : i ∈ S.support := Polynomial.mem_support_iff.mpr hc
    exact Polynomial.natDegree_mul_le.trans
      ((Nat.add_le_add_left hpow _).trans (by
        simpa [Nat.add_comm] using Polynomial.Bivariate.coeff_totalDegree_le S his))


private theorem natDegree_eval_affineQ_le
    {F : Type} [Field F] (S : F[X][X]) (a b : F) (q D : ℕ)
    (hS : ∀ i ∈ S.support, (S.coeff i).natDegree + q * i ≤ D) :
    (Polynomial.eval (Polynomial.C a + Polynomial.X ^ q * Polynomial.C b) S).natDegree ≤ D := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  have haff : (Polynomial.C a + Polynomial.X ^ q * Polynomial.C b : F[X]).natDegree ≤ q := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le (by simp)
    exact Polynomial.natDegree_mul_le.trans (by simp)
  have hpow : ((Polynomial.C a + Polynomial.X ^ q * Polynomial.C b : F[X]) ^ i).natDegree ≤
      q * i := by
    calc
      _ ≤ i * (Polynomial.C a + Polynomial.X ^ q * Polynomial.C b : F[X]).natDegree :=
        Polynomial.natDegree_pow_le
      _ ≤ i * q := Nat.mul_le_mul_left i haff
      _ = q * i := Nat.mul_comm _ _
  exact Polynomial.natDegree_mul_le.trans ((Nat.add_le_add_left hpow _).trans (hS i hi))

private theorem linear_specializations_commuteQ
    {F : Type*} [Field F] (R : F[X][X][X]) (x z a b : F) (q : ℕ) :
    (Polynomial.eval (Polynomial.C a + Polynomial.X ^ q * Polynomial.C b)
      (triSpecializeX R x)).eval z =
      (linearHSpecialization R z x).eval (a + z ^ q * b) := by
  induction R using Polynomial.induction_on' with
  | add R S hR hS =>
      simpa [triSpecializeX, linearHSpecialization] using congrArg₂ (· + ·) hR hS
  | monomial n A =>
      simp [triSpecializeX, linearHSpecialization, Polynomial.map_monomial,
        Polynomial.eval_monomial, eval_map_eval_eq_eval_eval_C, mul_comm b (z ^ q)]

private theorem linear_specializations_commute
    {F : Type*} [Field F] (R : F[X][X][X]) (x z a b : F) :
    (Polynomial.eval (Polynomial.C a + Polynomial.X * Polynomial.C b)
      (triSpecializeX R x)).eval z =
      (linearHSpecialization R z x).eval (a + z * b) := by
  induction R using Polynomial.induction_on' with
  | add R S hR hS =>
      simpa [triSpecializeX, linearHSpecialization] using congrArg₂ (· + ·) hR hS
  | monomial n A =>
      simp [triSpecializeX, linearHSpecialization, Polynomial.map_monomial,
        Polynomial.eval_monomial, eval_map_eval_eq_eval_eval_C, mul_comm b z]


private theorem biEval_linearH_commute
    {F : Type*} [Field F] (R : F[X][X][X]) (x z a : F) :
    biEval (triSpecializeX R x) a z =
      (linearHSpecialization R z x).eval a := by
  induction R using Polynomial.induction_on' with
  | add R S hR hS =>
      simpa [triSpecializeX, linearHSpecialization, biEval] using congrArg₂ (· + ·) hR hS
  | monomial n A =>
      simp [triSpecializeX, linearHSpecialization, biEval, Polynomial.map_monomial,
        Polynomial.eval_monomial, eval_map_eval_eq_eval_eval_C]

/-- Convert the indexed IRS agreement table to the field-coordinate protocol
used by the degree-one resultant argument. -/
theorem bchksLinearProtocolAdapter
    (U : Fin 2 → BinaryIRSProfile.Index → BinaryIRSProfile.Field)
    (P : BinaryIRSProfile.Field → BinaryIRSProfile.Field[X])
    (Arow : BinaryIRSProfile.Field → Finset BinaryIRSProfile.Index)
    (R : Polynomial (Polynomial (Polynomial BinaryIRSProfile.Field)))
    (T : Finset BinaryIRSProfile.Field) (q : ℕ) (hq1 : 1 ≤ q)
    (hPdeg : ∀ z ∈ T, (P z).natDegree ≤ 1048575)
    (hvan : ∀ z ∈ T, triEval R z (P z) = 0)
    (hrow : ∀ z ∈ T, 1484152 ≤ (Arow z).card)
    (hagree : ∀ z ∈ T, ∀ i ∈ Arow z,
      Polynomial.eval (BinaryIRSProfile.domain i) (P z) =
        U (0 : Fin 2) i + z ^ q * U (1 : Fin 2) i)
    (hRi : Irreducible R)
    (hYZq : YZCapQ R q 87534)
    (hWeighted : ∀ j a, ((R.coeff j).coeff a) ≠ 0 →
      a + 1048575 * j < 326513440)
    (hRdeg : R.natDegree = 1)
    (hTmargin : (613000 + 1) + 2 * 326513440 * 87534 < T.card) :
    ∃ Tgood : Finset BinaryIRSProfile.Field, Tgood ⊆ T ∧
      613000 + 1 < Tgood.card ∧
      ∃ p₀ p₁ : BinaryIRSProfile.Field[X], p₀.natDegree ≤ 1048575 ∧
        p₁.natDegree ≤ 1048575 ∧ ∀ z ∈ Tgood,
          P z = p₀ + Polynomial.C (z ^ q) * p₁ := by
  classical
  have hYZ : YZCap R 87534 := hYZq.toYZCap hq1
  obtain ⟨Res, hRes, hResdeg, hregular⟩ :=
    exists_linear_resultant_witness R hRi hRdeg hYZ hWeighted T P hvan
  let Bad : Finset BinaryIRSProfile.Field := Res.roots.toFinset
  let Tgood := T.filter fun z => z ∉ Bad
  have hBad : Bad.card ≤ (2 * 326513440 - 1048575) * 87534 := by
    calc
      Bad.card ≤ Res.roots.card := Multiset.toFinset_card_le _
      _ ≤ Res.natDegree := Polynomial.card_roots' Res
      _ ≤ _ := hResdeg
  have hsub : Tgood ⊆ T := Finset.filter_subset _ _
  have hpart : Tgood.card + (T.filter fun z => z ∈ Bad).card = T.card := by
    simpa [Tgood] using Finset.filter_card_add_filter_neg_card_eq_card
      (s := T) (p := fun z => z ∉ Bad)
  have hbadT : (T.filter fun z => z ∈ Bad).card ≤ Bad.card :=
    Finset.card_le_card (by intro z hz; exact (Finset.mem_filter.mp hz).2)
  have hTgood : 613000 + 1 < Tgood.card := by omega
  have hlarge : 2 * 326513440 + 613000 + 1 ≤ Tgood.card := by
    have hsaved : 2 * 326513440 < 1048575 * 87534 := by norm_num
    omega
  let PT : Tgood → BinaryIRSProfile.Field[X] := fun z => P z
  obtain ⟨Afield, hAfield, Fib, hFib, hinc⟩ :=
    exists_large_domain_fibers U Tgood Arow PT 1 1 1 q
      (by intro z hz; exact hrow z (hsub hz)) hlarge
      (by intro z i hi; exact hagree z (hsub z.property) i hi)
  have hFibBig : ∀ x : Afield, 87534 < (Fib x).card := by
    intro x
    have := hFib x
    norm_num at this ⊢
    omega
  have hne : ∀ x : Afield, (Fib x).Nonempty := fun x =>
    Finset.card_pos.mp (Nat.zero_lt_of_lt (hFibBig x))
  let zpick : ∀ x : Afield, Tgood := fun x => Classical.choose (hne x)
  have hzpick (x : Afield) : zpick x ∈ Fib x := Classical.choose_spec (hne x)
  let idx : Afield → BinaryIRSProfile.Index := fun x =>
    Classical.choose (hinc x (zpick x) (hzpick x))
  have hidx (x : Afield) : BinaryIRSProfile.domain (idx x) = (x : BinaryIRSProfile.Field) :=
    (Classical.choose_spec (hinc x (zpick x) (hzpick x))).1
  let U₀f : BinaryIRSProfile.Field → BinaryIRSProfile.Field := fun x =>
    if hx : x ∈ Afield then U 0 (idx ⟨x, hx⟩) else 0
  let U₁f : BinaryIRSProfile.Field → BinaryIRSProfile.Field := fun x =>
    if hx : x ∈ Afield then U 1 (idx ⟨x, hx⟩) else 0
  have halign : ∀ x : Afield, ∀ z ∈ Fib x,
      (P z).eval (x : BinaryIRSProfile.Field) = U₀f x + (z : BinaryIRSProfile.Field) ^ q * U₁f x := by
    intro x z hz
    obtain ⟨i, hi, he⟩ := hinc x z hz
    have hii : i = idx x := BinaryIRSProfile.domain.injective (hi.trans (hidx x).symm)
    subst i
    simpa [U₀f, U₁f, x.property] using he
  let QQ : BinaryIRSProfile.Field → BinaryIRSProfile.Field[X] := fun x =>
    Polynomial.eval (Polynomial.C (U₀f x) + Polynomial.X ^ q * Polynomial.C (U₁f x))
      (triSpecializeX R x)
  have hQdeg : ∀ x, (QQ x).natDegree ≤ 87534 := by
    intro x
    apply natDegree_eval_affineQ_le
    intro i hi
    have hspec : triSpecializeX R x = Polynomial.Bivariate.evalX (Polynomial.C x) R := by
      unfold triSpecializeX
      rw [← Polynomial.Bivariate.evalX_eq_map]
    rw [hspec] at hi ⊢
    exact evalX_coeff_le_of_yzCapQ x R hYZq i hi
  let Fibf : Afield → Finset BinaryIRSProfile.Field := fun x => (Fib x).image Subtype.val
  have hFibfcard : ∀ x : Afield, 87534 < (Fibf x).card := by
    intro x
    rw [show (Fibf x).card = (Fib x).card by
      exact Finset.card_image_iff.mpr fun a _ b _ h => Subtype.ext h]
    exact hFibBig x
  have hcore := bchksLinearSelectedCore 1048575 87534 q Tgood Afield P U₀f U₁f
    QQ (linearHSpecialization R)
    (by intro z hz; exact hPdeg z (hsub hz)) hAfield Fibf hFibfcard
    (by intro x hx; exact hQdeg x)
    (by
      intro x z hz
      obtain ⟨zs, hzs, heq⟩ := Finset.mem_image.mp hz
      subst z
      rw [show (QQ x).eval (zs : BinaryIRSProfile.Field) =
        (linearHSpecialization R (zs : BinaryIRSProfile.Field) x).eval
          (U₀f x + (zs : BinaryIRSProfile.Field) ^ q * U₁f x) by
          exact linear_specializations_commuteQ R x zs (U₀f x) (U₁f x) q]
      rw [← halign x zs hzs]
      rw [show (linearHSpecialization R (zs : BinaryIRSProfile.Field) (x : BinaryIRSProfile.Field)).eval
          ((P (zs : BinaryIRSProfile.Field)).eval (x : BinaryIRSProfile.Field)) =
          (triEval R (zs : BinaryIRSProfile.Field) (P (zs : BinaryIRSProfile.Field))).eval (x : BinaryIRSProfile.Field) by
        rw [eval_triEval_eq_biEval_triSpecializeX]
        symm
        exact biEval_linearH_commute R (x : BinaryIRSProfile.Field) (zs : BinaryIRSProfile.Field)
          ((P (zs : BinaryIRSProfile.Field)).eval (x : BinaryIRSProfile.Field))]
      rw [hvan zs (hsub zs.property)]
      simp)
    (by
      intro z hz x hx
      apply hregular z (hsub hz)
      intro he
      have : z ∈ Bad := by
        dsimp [Bad]
        simp only [Multiset.mem_toFinset]
        exact (Polynomial.mem_roots hRes).2 he
      exact (Finset.mem_filter.mp hz).2 this)
    (by
      intro z hz x hx
      rw [show (linearHSpecialization R z x).eval ((P z).eval x) =
        (triEval R z (P z)).eval x by
          rw [eval_triEval_eq_biEval_triSpecializeX]
          symm
          exact biEval_linearH_commute R x z ((P z).eval x)]
      rw [hvan z (hsub hz)]
      simp)
    (by
      intro z hz x hx hQ
      rw [← show (QQ x).eval z =
        (linearHSpecialization R z x).eval (U₀f x + z ^ q * U₁f x) by
          exact linear_specializations_commuteQ R x z (U₀f x) (U₁f x) q, hQ]
      simp)
  exact ⟨Tgood, hsub, hTgood, hcore⟩

end ProximityPrize.SubmissionBinaryLower
