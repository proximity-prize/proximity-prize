import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower
namespace BCHKSSubstitutionVanish

noncomputable def specializeZ {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F) :
    Polynomial (Polynomial F) :=
  Polynomial.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) Q

noncomputable def triEval {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F) (P : Polynomial F) :
    Polynomial F := Polynomial.eval P (specializeZ Q z)

lemma map_comp_X_add_C {F : Type*} [Field F]
    (A : Polynomial (Polynomial F)) (x : Polynomial F) (z : F) :
    Polynomial.map (Polynomial.evalRingHom z)
        (A.comp (Polynomial.X + Polynomial.C x)) =
      (Polynomial.map (Polynomial.evalRingHom z) A).comp
        (Polynomial.X + Polynomial.C (Polynomial.eval z x)) := by
  rw [Polynomial.map_comp]
  simp

lemma specializeZ_shift {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (x y : Polynomial F) (z : F) :
    specializeZ (Polynomial.Bivariate.shift Q x y) z =
      Polynomial.Bivariate.shift (specializeZ Q z)
        (Polynomial.eval z x) (Polynomial.eval z y) := by
  induction Q using Polynomial.induction_on' with
  | add Q R hQ hR =>
      calc
        specializeZ (Polynomial.Bivariate.shift (Q + R) x y) z =
            specializeZ (Polynomial.Bivariate.shift Q x y) z +
              specializeZ (Polynomial.Bivariate.shift R x y) z := by
                simp [Polynomial.Bivariate.shift, specializeZ]
        _ = Polynomial.Bivariate.shift (specializeZ Q z)
              (Polynomial.eval z x) (Polynomial.eval z y) +
            Polynomial.Bivariate.shift (specializeZ R z)
              (Polynomial.eval z x) (Polynomial.eval z y) := by rw [hQ, hR]
        _ = Polynomial.Bivariate.shift (specializeZ (Q + R) z)
              (Polynomial.eval z x) (Polynomial.eval z y) := by
                simp [Polynomial.Bivariate.shift, specializeZ]
  | monomial n A =>
      simp [Polynomial.Bivariate.shift, specializeZ, Polynomial.monomial_comp,
        Polynomial.map_monomial, map_comp_X_add_C]


lemma comp_eval_eq_shift_eval_tail {F : Type*} [Field F]
    (B : Polynomial (Polynomial F)) (P : Polynomial F) (ω y : F) :
    (Polynomial.eval P B).comp (Polynomial.X + Polynomial.C ω) =
      Polynomial.eval (P.comp (Polynomial.X + Polynomial.C ω) - Polynomial.C y)
        (Polynomial.Bivariate.shift B ω y) := by
  induction B using Polynomial.induction_on' with
  | add B C hB hC =>
      calc
        (Polynomial.eval P (B + C)).comp (Polynomial.X + Polynomial.C ω) =
            (Polynomial.eval P B).comp (Polynomial.X + Polynomial.C ω) +
              (Polynomial.eval P C).comp (Polynomial.X + Polynomial.C ω) := by simp
        _ = Polynomial.eval (P.comp (Polynomial.X + Polynomial.C ω) - Polynomial.C y)
              (Polynomial.Bivariate.shift B ω y) +
            Polynomial.eval (P.comp (Polynomial.X + Polynomial.C ω) - Polynomial.C y)
              (Polynomial.Bivariate.shift C ω y) := by rw [hB, hC]
        _ = Polynomial.eval (P.comp (Polynomial.X + Polynomial.C ω) - Polynomial.C y)
              (Polynomial.Bivariate.shift (B + C) ω y) := by
                simp [Polynomial.Bivariate.shift]
  | monomial n A =>
      simp [Polynomial.Bivariate.shift, Polynomial.monomial_comp,
        Polynomial.eval_monomial, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_C, Polynomial.coe_compRingHom_apply]

lemma X_dvd_comp_sub_C_eval {F : Type*} [Field F]
    (P : Polynomial F) (ω y : F) (hmatch : Polynomial.eval ω P = y) :
    Polynomial.X ∣ P.comp (Polynomial.X + Polynomial.C ω) - Polynomial.C y := by
  rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_sub, Polynomial.eval_comp]
  simp [hmatch]

lemma X_pow_dvd_mul_pow_of_total_coeff_zero {F : Type*} [Field F]
    {A U : Polynomial F} {m b : Nat}
    (hU : Polynomial.X ∣ U)
    (hzero : ∀ a, a + b < m → A.coeff a = 0) :
    Polynomial.X ^ m ∣ A * U ^ b := by
  by_cases hb : b < m
  · have hA : Polynomial.X ^ (m - b) ∣ A := by
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      exact hzero d (by omega)
    have hUb : Polynomial.X ^ b ∣ U ^ b := pow_dvd_pow_of_dvd hU b
    rcases hA with ⟨A', hA'⟩
    rcases hUb with ⟨U', hU'⟩
    refine ⟨A' * U', ?_⟩
    rw [hA', hU']
    ring_nf
    rw [← pow_add]
    have hmb : m - b + b = m := Nat.sub_add_cancel (Nat.le_of_lt hb)
    rw [hmb]
  · have hbm : m ≤ b := Nat.le_of_not_gt hb
    have hXb : (Polynomial.X : Polynomial F) ^ m ∣ Polynomial.X ^ b :=
      pow_dvd_pow Polynomial.X hbm
    have hUb : Polynomial.X ^ b ∣ U ^ b := pow_dvd_pow_of_dvd hU b
    exact dvd_mul_of_dvd_right (dvd_trans hXb hUb) A

lemma X_pow_dvd_eval_of_total_coeff_zero {F : Type*} [Field F]
    {B : Polynomial (Polynomial F)} {U : Polynomial F} {m : Nat}
    (hU : Polynomial.X ∣ U)
    (hzero : ∀ a b, a + b < m → (B.coeff b).coeff a = 0) :
    Polynomial.X ^ m ∣ Polynomial.eval U B := by
  rw [Polynomial.eval_eq_sum]
  apply Finset.dvd_sum
  intro b hb
  exact X_pow_dvd_mul_pow_of_total_coeff_zero (m := m) (b := b) hU
    (fun a ha => hzero a b ha)


/-- .
 -/
lemma specialize_shift_total_coeff_zero {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (ω z : F) (yZ : Polynomial F)
    (m : Nat)
    (hvan : ∀ s t h, s + t < m →
      ((((Polynomial.Bivariate.shift Q (Polynomial.C ω) yZ).coeff t).coeff s).coeff h) = 0) :
    ∀ s t, s + t < m →
      (((Polynomial.Bivariate.shift (specializeZ Q z) ω (Polynomial.eval z yZ)).coeff t).coeff s) = 0 := by
  intro s t hst
  have hpoly :
      ((Polynomial.Bivariate.shift Q (Polynomial.C ω) yZ).coeff t).coeff s = 0 := by
    apply Polynomial.ext
    intro h
    exact hvan s t h hst
  have hshift := specializeZ_shift Q (Polynomial.C ω) yZ z
  simp only [Polynomial.eval_C] at hshift
  rw [← hshift]
  simp [specializeZ, hpoly]

/-- .

 -/
theorem rootMultiplicity_triEval_ge_of_shift_coeff_zero
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (ω z : F)
    (yZ P : Polynomial F) (m : Nat)
    (hvan : ∀ s t h, s + t < m →
      ((((Polynomial.Bivariate.shift Q (Polynomial.C ω) yZ).coeff t).coeff s).coeff h) = 0)
    (hmatch : Polynomial.eval ω P = Polynomial.eval z yZ)
    (hne : triEval Q z P ≠ 0) :
    m ≤ (triEval Q z P).rootMultiplicity ω := by
  let y := Polynomial.eval z yZ
  let B := specializeZ Q z
  let U := P.comp (Polynomial.X + Polynomial.C ω) - Polynomial.C y
  have hzero : ∀ a b, a + b < m →
      (((Polynomial.Bivariate.shift B ω y).coeff b).coeff a) = 0 := by
    exact specialize_shift_total_coeff_zero Q ω z yZ m hvan
  have hU : Polynomial.X ∣ U :=
    X_dvd_comp_sub_C_eval P ω y (by simpa [y] using hmatch)
  have hdvd : Polynomial.X ^ m ∣
      (triEval Q z P).comp (Polynomial.X + Polynomial.C ω) := by
    rw [show triEval Q z P = Polynomial.eval P B by rfl]
    rw [comp_eval_eq_shift_eval_tail B P ω y]
    exact X_pow_dvd_eval_of_total_coeff_zero hU hzero
  rw [Polynomial.rootMultiplicity_eq_rootMultiplicity]
  have hshiftne :
      (triEval Q z P).comp (Polynomial.X + Polynomial.C ω) ≠ 0 := by
    exact (Polynomial.comp_X_add_C_eq_zero_iff.not.mpr hne)
  rw [Polynomial.le_rootMultiplicity_iff hshiftne]
  simpa using hdvd


/-- .
 -/
theorem mul_card_le_natDegree_of_rootMultiplicity
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (R : Polynomial F) (ω : ι ↪ F) (A : Finset ι) (m : Nat)
    (hmult : ∀ i ∈ A, m ≤ R.rootMultiplicity (ω i)) :
    m * A.card ≤ R.natDegree := by
  let xs : Finset F := A.map ω
  have hselected :
      ∑ x ∈ xs, Multiset.count x R.roots ≤ R.roots.card := by
    let all := xs ∪ R.roots.toFinset
    calc
      ∑ x ∈ xs, Multiset.count x R.roots ≤
          ∑ x ∈ all, Multiset.count x R.roots :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by simp)
      _ = ∑ x ∈ R.roots.toFinset, Multiset.count x R.roots := by
        symm
        apply Finset.sum_subset (Finset.subset_union_right)
        intro x hxall hxroots
        exact Multiset.count_eq_zero.mpr (by simpa using hxroots)
      _ = R.roots.card := Multiset.toFinset_sum_count_eq R.roots
  calc
    m * A.card = ∑ i ∈ A, m := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ A, R.rootMultiplicity (ω i) :=
      Finset.sum_le_sum fun i hi => hmult i hi
    _ = ∑ x ∈ xs, R.rootMultiplicity x := by
      symm
      exact Finset.sum_map A ω (fun x => R.rootMultiplicity x)
    _ = ∑ x ∈ xs, Multiset.count x R.roots := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (Polynomial.count_roots R).symm
    _ ≤ R.roots.card := hselected
    _ ≤ R.natDegree := Polynomial.card_roots' R

/-- .

 -/
theorem triEval_eq_zero_of_many_shift_vanishing
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F)
    (P : Polynomial F) (ω : ι ↪ F) (A : Finset ι)
    (yZ : ι → Polynomial F) (m DX : Nat)
    (hvan : ∀ i ∈ A, ∀ s t h, s + t < m →
      ((((Polynomial.Bivariate.shift Q (Polynomial.C (ω i)) (yZ i)).coeff t).coeff s).coeff h) = 0)
    (hmatch : ∀ i ∈ A, Polynomial.eval (ω i) P = Polynomial.eval z (yZ i))
    (hdegree : (triEval Q z P).natDegree ≤ DX)
    (hmany : DX < m * A.card) :
    triEval Q z P = 0 := by
  by_contra hne
  have hmult : ∀ i ∈ A, m ≤ (triEval Q z P).rootMultiplicity (ω i) := by
    intro i hi
    exact rootMultiplicity_triEval_ge_of_shift_coeff_zero
      Q (ω i) z (yZ i) P m (hvan i hi) (hmatch i hi) hne
  have hrootdeg := mul_card_le_natDegree_of_rootMultiplicity
    (triEval Q z P) ω A m hmult
  omega


/-- .
 -/
theorem triEval_natDegree_le_of_weighted_X_cap
    {F : Type*} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F) (P : Polynomial F)
    (k DX : Nat) (hP : P.natDegree ≤ k)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 → a + k * j ≤ DX) :
    (triEval Q z P).natDegree ≤ DX := by
  rw [triEval, Polynomial.eval_eq_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  let A : Polynomial F := (specializeZ Q z).coeff j
  have hAeq : A = Polynomial.map (Polynomial.evalRingHom z) (Q.coeff j) := by
    simp [A, specializeZ]
  have hA0 : A ≠ 0 := by
    exact Polynomial.mem_support_iff.mp hj
  have hAdeg : A.natDegree + k * j ≤ DX := by
    have hlead : A.coeff A.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hA0
    have horig : (Q.coeff j).coeff A.natDegree ≠ 0 := by
      intro horig0
      apply hlead
      calc
        A.coeff A.natDegree =
            Polynomial.eval z ((Q.coeff j).coeff A.natDegree) := by
          rw [hAeq, Polynomial.coeff_map]
          rfl
        _ = 0 := by rw [horig0]; simp
    exact hcap j A.natDegree horig
  calc
    (A * P ^ j).natDegree ≤ A.natDegree + (P ^ j).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ A.natDegree + j * k := by
      exact Nat.add_le_add_left (Polynomial.natDegree_pow_le_of_le j hP) A.natDegree
    _ = A.natDegree + k * j := by rw [Nat.mul_comm j k]
    _ ≤ DX := hAdeg


/-- .

 -/
theorem triEval_eq_zero_of_many_shift_vanishing_of_weighted_X_cap
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F)
    (P : Polynomial F) (ω : ι ↪ F) (A : Finset ι)
    (yZ : ι → Polynomial F) (m k DX : Nat)
    (hvan : ∀ i ∈ A, ∀ s t h, s + t < m →
      ((((Polynomial.Bivariate.shift Q (Polynomial.C (ω i)) (yZ i)).coeff t).coeff s).coeff h) = 0)
    (hmatch : ∀ i ∈ A, Polynomial.eval (ω i) P = Polynomial.eval z (yZ i))
    (hP : P.natDegree ≤ k)
    (hcap : ∀ j a, ((Q.coeff j).coeff a) ≠ 0 → a + k * j ≤ DX)
    (hmany : DX < m * A.card) :
    triEval Q z P = 0 := by
  apply triEval_eq_zero_of_many_shift_vanishing Q z P ω A yZ m DX
    hvan hmatch (triEval_natDegree_le_of_weighted_X_cap Q z P k DX hP hcap) hmany

end BCHKSSubstitutionVanish
end ProximityPrize.SubmissionLower
