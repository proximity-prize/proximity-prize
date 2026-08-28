import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower

open scoped BigOperators

namespace BCHKSConcreteGS

set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 4000000

def n : ℕ := 262144
def k : ℕ := 131071
def m : ℕ := 602
def DX : ℕ := 111624646
def DY : ℕ := 852
def DZ : ℕ := 519143

/-- Coefficients of `X^a Y^j Z^h`. -/
abbrev VarIndex := Σ j : Fin DY, Fin (DX - k * (j : ℕ)) × Fin (DZ - (j : ℕ))

/-- The coefficient constraints, ordered as point, Y order, X order, Z order. -/
abbrev ConIndex := Fin n × Σ t : Fin m, Fin (m - (t : ℕ)) × Fin (DZ - (t : ℕ))

private noncomputable def evalConstraint {F : Type} [Field F]
    (x y : Polynomial F) (s t d : ℕ) :
    Polynomial (Polynomial (Polynomial F)) →ₗ[F] F where
  toFun Q := ((((Polynomial.Bivariate.shift Q x y).coeff t).coeff s).coeff d)
  map_add' Q R := by simp [Polynomial.Bivariate.shift]
  map_smul' a Q := by simp [Polynomial.Bivariate.shift]

private theorem prod_heq {α α' β β' : Type} {a : α} {a' : α'} {b : β} {b' : β'}
    (ha : a ≍ a') (hb : b ≍ b') : (a, b) ≍ (a', b') := by
  cases ha
  cases hb
  rfl

noncomputable def polyMap {F : Type} [Field F] :
    (VarIndex → F) →ₗ[F] Polynomial (Polynomial (Polynomial F)) :=
  Finsupp.linearCombination F (fun q : VarIndex =>
    Polynomial.monomial (q.1 : ℕ)
      (Polynomial.monomial (q.2.1 : ℕ) (Polynomial.monomial (q.2.2 : ℕ) 1))) ∘ₗ
    (Finsupp.linearEquivFunOnFinite F F VarIndex).symm.toLinearMap

noncomputable def constraintMap {F : Type} [Field F]
    (ω : Fin n ↪ F) (u₀ u₁ : Fin n → F) :
    (VarIndex → F) →ₗ[F] (ConIndex → F) :=
  LinearMap.pi (fun q =>
    evalConstraint
      (Polynomial.C (ω q.1))
      (Polynomial.C (u₀ q.1) + Polynomial.X * Polynomial.C (u₁ q.1))
      (q.2.2.1 : ℕ) (q.2.1 : ℕ) (q.2.2.2 : ℕ) ∘ₗ polyMap)

open scoped BigOperators in
theorem polyMap_eq_sum {F : Type} [Field F] (c : VarIndex → F) :
    polyMap c = ∑ q : VarIndex, c q •
      Polynomial.monomial (q.1 : ℕ)
        (Polynomial.monomial (q.2.1 : ℕ) (Polynomial.monomial (q.2.2 : ℕ) 1)) := by
  unfold polyMap
  rw [Finsupp.linearCombination_eq_fintype_linearCombination,
    Fintype.linearCombination_apply]

open scoped BigOperators in
theorem polyMap_coeff_pair {F : Type} [Field F] (c : VarIndex → F) (a j : ℕ) :
    ((polyMap c).coeff j).coeff a =
      ∑ q : VarIndex, if (q.1 : ℕ) = j ∧ (q.2.1 : ℕ) = a then
        Polynomial.monomial (q.2.2 : ℕ) (c q) else 0 := by
  classical
  rw [polyMap_eq_sum, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hj : (q.1 : ℕ) = j
  · by_cases ha : (q.2.1 : ℕ) = a
    · simp [hj, ha, Polynomial.smul_monomial]
    · simp [hj, ha, Polynomial.coeff_smul, Polynomial.coeff_monomial]
  · simp [hj, Polynomial.coeff_smul, Polynomial.coeff_monomial]

open scoped BigOperators in
theorem polyMap_coeff_index {F : Type} [Field F] (c : VarIndex → F) (q : VarIndex) :
    ((((polyMap c).coeff (q.1 : ℕ)).coeff (q.2.1 : ℕ)).coeff (q.2.2 : ℕ)) = c q := by
  classical
  rw [polyMap_coeff_pair]
  change (∑ r ∈ Finset.univ, (if (r.1 : ℕ) = (q.1 : ℕ) ∧
      (r.2.1 : ℕ) = (q.2.1 : ℕ) then
      Polynomial.monomial (r.2.2 : ℕ) (c r) else 0)).coeff (q.2.2 : ℕ) = c q
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single q]
  · simp
  · intro r hr hrq
    by_cases he : (r.1 : ℕ) = (q.1 : ℕ) ∧ (r.2.1 : ℕ) = (q.2.1 : ℕ)
    · have hh : (r.2.2 : ℕ) ≠ (q.2.2 : ℕ) := by
        intro hh
        apply hrq
        apply Sigma.ext (Fin.ext he.1)
        apply prod_heq
        · apply (Fin.heq_ext_iff (congrArg
            (fun z : Fin DY => DX - k * (z : ℕ)) (Fin.ext he.1))).mpr
          exact he.2
        · apply (Fin.heq_ext_iff (congrArg
            (fun z : Fin DY => DZ - (z : ℕ)) (Fin.ext he.1))).mpr
          exact hh
      rw [if_pos he]
      simp only [Polynomial.coeff_monomial, if_neg hh]
    · simp [he]
  · simp

theorem polyMap_ne_zero {F : Type} [Field F] (c : VarIndex → F) (hc : c ≠ 0) :
    polyMap c ≠ 0 := by
  intro hQ
  apply hc
  funext q
  have h := polyMap_coeff_index c q
  rw [hQ] at h
  simpa using h.symm

/-- Closed form for the quadratic summand occurring in both dimension
counts.  Multiplying by six avoids division in the induction. -/
private theorem six_mul_sum_affine_product
    (N : Nat) (A B C : Int) :
    6 * (∑ j ∈ Finset.range N, (A - C * (j : Int)) * (B - (j : Int))) =
      (N : Int) *
        (6 * A * B - 3 * (A + C * B) * ((N : Int) - 1) +
          C * ((N : Int) - 1) * (2 * (N : Int) - 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring

open scoped BigOperators in
theorem card_var : Fintype.card VarIndex = 24691251830218528 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin, Finset.sum_fin_eq_sum_range]
  have hk (j : Nat) (hj : j ∈ Finset.range DY) : k * j ≤ DX := by
    rw [Finset.mem_range] at hj
    norm_num [k, DY, DX] at *
    omega
  have hz (j : Nat) (hj : j ∈ Finset.range DY) : j ≤ DZ := by
    rw [Finset.mem_range] at hj
    norm_num [DY, DZ] at *
    omega
  have hcast :
      ((∑ j ∈ Finset.range DY, (DX - k * j) * (DZ - j) : Nat) : Int) =
        ∑ j ∈ Finset.range DY,
          ((DX : Int) - (k : Int) * (j : Int)) * ((DZ : Int) - (j : Int)) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.cast_mul, Nat.cast_sub (hk j hj), Nat.cast_sub (hz j hj),
      Nat.cast_mul]
  have hformula := six_mul_sum_affine_product DY (DX : Int) (DZ : Int) (k : Int)
  have h6 :
      (6 : Int) * ((∑ j ∈ Finset.range DY, (DX - k * j) * (DZ - j) : Nat) : Int) =
        6 * (24691251830218528 : Int) := by
    rw [hcast, hformula]
    norm_num [DY, DX, DZ, k]
  have heq :
      ((∑ j ∈ Finset.range DY, (DX - k * j) * (DZ - j) : Nat) : Int) =
        24691251830218528 := by
    nlinarith
  exact_mod_cast heq

open scoped BigOperators in
theorem card_con : Fintype.card ConIndex = 24691251826655232 := by
  rw [Fintype.card_prod, Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin, Finset.sum_fin_eq_sum_range]
  have hm (t : Nat) (ht : t ∈ Finset.range m) : t ≤ m := by
    exact (Finset.mem_range.mp ht).le
  have hz (t : Nat) (ht : t ∈ Finset.range m) : t ≤ DZ := by
    have := Finset.mem_range.mp ht
    norm_num [m, DZ] at *
    omega
  have hcast :
      ((∑ t ∈ Finset.range m, (m - t) * (DZ - t) : Nat) : Int) =
        ∑ t ∈ Finset.range m,
          ((m : Int) - (t : Int)) * ((DZ : Int) - (t : Int)) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Nat.cast_mul, Nat.cast_sub (hm t ht), Nat.cast_sub (hz t ht)]
  have hformula := six_mul_sum_affine_product m (m : Int) (DZ : Int) 1
  have h6 :
      (6 : Int) * ((∑ t ∈ Finset.range m, (m - t) * (DZ - t) : Nat) : Int) =
        6 * (94189650828 : Int) := by
    rw [hcast]
    calc
      (6 : Int) * ∑ t ∈ Finset.range m,
          ((m : Int) - (t : Int)) * ((DZ : Int) - (t : Int)) =
        (m : Int) *
          (6 * (m : Int) * (DZ : Int) -
            3 * ((m : Int) + (DZ : Int)) * ((m : Int) - 1) +
            ((m : Int) - 1) * (2 * (m : Int) - 1)) := by
              simpa using hformula
      _ = 6 * (94189650828 : Int) := by norm_num [m, DZ]
  have heq :
      ((∑ t ∈ Finset.range m, (m - t) * (DZ - t) : Nat) : Int) =
        94189650828 := by
    nlinarith
  have heqNat : (∑ t ∈ Finset.range m, (m - t) * (DZ - t) : Nat) =
      94189650828 := by exact_mod_cast heq
  have hif : (∑ t ∈ Finset.range m,
      if h : t < m then (m - t) * (DZ - t) else 0) =
      ∑ t ∈ Finset.range m, (m - t) * (DZ - t) := by
    apply Finset.sum_congr rfl
    intro t ht
    simp [Finset.mem_range.mp ht]
  rw [hif]
  rw [heqNat]
  norm_num [n]

theorem card_con_lt_var : Fintype.card ConIndex < Fintype.card VarIndex := by
  rw [card_con, card_var]
  norm_num

structure KernelWitness {F : Type} [Field F]
    (ω : Fin n ↪ F) (u₀ u₁ : Fin n → F) where
  c : VarIndex → F
  c_ne_zero : c ≠ 0
  constraints : constraintMap ω u₀ u₁ c = 0

theorem exists_kernelWitness {F : Type} [Field F]
    (ω : Fin n ↪ F) (u₀ u₁ : Fin n → F) : Nonempty (KernelWitness ω u₀ u₁) := by
  have hfinrank : Module.finrank F (ConIndex → F) < Module.finrank F (VarIndex → F) := by
    simpa only [Module.finrank_fintype_fun_eq_card] using card_con_lt_var
  have hker : LinearMap.ker (constraintMap ω u₀ u₁) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hfinrank
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨{ c := c, c_ne_zero := hc0, constraints := hc }⟩

private theorem innerMonomial_shift_coeff {F : Type} [Field F]
    (a h : ℕ) (x : F) (s : ℕ) :
    (((Polynomial.monomial a (Polynomial.monomial h 1) :
      Polynomial (Polynomial F)).comp
        (Polynomial.X + Polynomial.C (Polynomial.C x))).coeff s) =
      Polynomial.monomial h (x ^ (a - s) * (a.choose s : F)) := by
  rw [Polynomial.monomial_comp, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]
  rw [← Polynomial.C_eq_natCast]
  rw [← map_pow, ← map_mul, Polynomial.monomial_mul_C, one_mul]

private theorem outerAffine_map {F : Type} [Field F]
    (x y₀ y₁ : F) :
    Polynomial.map
      (Polynomial.compRingHom (Polynomial.X + Polynomial.C (Polynomial.C x)))
      (Polynomial.X + Polynomial.C
        (Polynomial.C (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁))) =
      Polynomial.X + Polynomial.C
        (Polynomial.C (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)) := by
  simp [Polynomial.coe_compRingHom_apply]

private theorem basis_shift_coeff_formula {F : Type} [Field F] (q : VarIndex)
    (x y₀ y₁ : F) (s t : ℕ) :
    ((Polynomial.Bivariate.shift
      (Polynomial.monomial (q.1 : ℕ)
        (Polynomial.monomial (q.2.1 : ℕ) (Polynomial.monomial (q.2.2 : ℕ) 1)))
      (Polynomial.C x)
      (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)).coeff t).coeff s =
    Polynomial.monomial (q.2.2 : ℕ)
      (x ^ ((q.2.1 : ℕ) - s) * ((q.2.1 : ℕ).choose s : F) *
        ((q.1 : ℕ).choose t : F)) *
      (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁) ^ ((q.1 : ℕ) - t) := by
  classical
  unfold Polynomial.Bivariate.shift
  rw [Polynomial.monomial_comp, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, outerAffine_map]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  rw [← Polynomial.C_eq_natCast]
  rw [← map_pow, ← map_mul, Polynomial.coeff_mul_C]
  rw [Polynomial.coe_compRingHom_apply, innerMonomial_shift_coeff]
  rw [← Polynomial.C_eq_natCast]
  calc
    Polynomial.monomial (q.2.2 : ℕ)
        (x ^ ((q.2.1 : ℕ) - s) * ((q.2.1 : ℕ).choose s : F)) *
        ((Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁) ^ ((q.1 : ℕ) - t) *
          Polynomial.C ((q.1 : ℕ).choose t : F)) =
      (Polynomial.monomial (q.2.2 : ℕ)
        (x ^ ((q.2.1 : ℕ) - s) * ((q.2.1 : ℕ).choose s : F)) *
          Polynomial.C ((q.1 : ℕ).choose t : F)) *
        (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁) ^ ((q.1 : ℕ) - t) := by ring
    _ = _ := by rw [Polynomial.monomial_mul_C]

private theorem basis_shift_coeff_natDegree_le {F : Type} [Field F] (q : VarIndex)
    (x y₀ y₁ : F) (s t : ℕ) :
    (((Polynomial.Bivariate.shift
      (Polynomial.monomial (q.1 : ℕ)
        (Polynomial.monomial (q.2.1 : ℕ) (Polynomial.monomial (q.2.2 : ℕ) 1)))
      (Polynomial.C x)
      (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)).coeff t).coeff s).natDegree ≤
      (q.2.2 : ℕ) + ((q.1 : ℕ) - t) := by
  rw [basis_shift_coeff_formula]
  have hL : (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁).natDegree ≤ 1 := by
    rw [show Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁ =
      Polynomial.C y₁ * Polynomial.X + Polynomial.C y₀ by ring]
    exact Polynomial.natDegree_linear_le
  have hpow := Polynomial.natDegree_pow_le_of_le ((q.1 : ℕ) - t) hL
  have hmono := Polynomial.natDegree_monomial_le
    (m := (q.2.2 : ℕ))
    (x ^ ((q.2.1 : ℕ) - s) * ((q.2.1 : ℕ).choose s : F) * ((q.1 : ℕ).choose t : F))
  calc
    _ ≤ (Polynomial.monomial (q.2.2 : ℕ)
          (x ^ ((q.2.1 : ℕ) - s) * ((q.2.1 : ℕ).choose s : F) *
            ((q.1 : ℕ).choose t : F))).natDegree +
        ((Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁) ^ ((q.1 : ℕ) - t)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (q.2.2 : ℕ) + ((q.1 : ℕ) - t) := by
      exact add_le_add hmono (by simpa only [mul_one] using hpow)

open scoped BigOperators in
private theorem shift_coeff_eq_sum {F : Type} [Field F] (c : VarIndex → F)
    (x y : Polynomial F) (s t : ℕ) :
    ((Polynomial.Bivariate.shift (polyMap c) x y).coeff t).coeff s =
      ∑ q : VarIndex, c q •
        ((Polynomial.Bivariate.shift
          (Polynomial.monomial (q.1 : ℕ)
            (Polynomial.monomial (q.2.1 : ℕ) (Polynomial.monomial (q.2.2 : ℕ) 1)))
          x y).coeff t).coeff s := by
  ext d
  change evalConstraint x y s t d (polyMap c) = _
  rw [polyMap_eq_sum, map_sum]
  simp only [map_smul]
  change (∑ q : VarIndex, c q • evalConstraint x y s t d
      (Polynomial.monomial (q.1 : ℕ)
        (Polynomial.monomial (q.2.1 : ℕ) (Polynomial.monomial (q.2.2 : ℕ) 1)))) = _
  rw [Polynomial.finsetSum_coeff]
  rfl

private theorem index_yz_lt (q : VarIndex) : (q.2.2 : ℕ) + (q.1 : ℕ) < DZ := by
  have h := q.2.2.isLt
  omega

private theorem shift_coeff_natDegree_lt {F : Type} [Field F] (c : VarIndex → F)
    (x y₀ y₁ : F) (s t : ℕ) (ht : t < m) :
    (((Polynomial.Bivariate.shift (polyMap c)
      (Polynomial.C x)
      (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)).coeff t).coeff s).natDegree <
      DZ - t := by
  rw [shift_coeff_eq_sum]
  show (∑ q : VarIndex, c q •
      ((Polynomial.Bivariate.shift
        (Polynomial.monomial (q.1 : ℕ)
          (Polynomial.monomial (q.2.1 : ℕ) (Polynomial.monomial (q.2.2 : ℕ) 1)))
        (Polynomial.C x)
        (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)).coeff t).coeff s).natDegree < DZ - t
  have htDZ : t < DZ := by norm_num [m, DZ] at ht ⊢; omega
  apply lt_of_le_of_lt
  · show _ ≤ DZ - t - 1
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro q hq
    by_cases htj : t ≤ (q.1 : ℕ)
    · calc
        _ ≤ (((Polynomial.Bivariate.shift
            (Polynomial.monomial (q.1 : ℕ)
              (Polynomial.monomial (q.2.1 : ℕ)
                (Polynomial.monomial (q.2.2 : ℕ) 1)))
            (Polynomial.C x)
            (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)).coeff t).coeff s).natDegree :=
          Polynomial.natDegree_smul_le _ _
        _ ≤ (q.2.2 : ℕ) + ((q.1 : ℕ) - t) :=
          basis_shift_coeff_natDegree_le q x y₀ y₁ s t
        _ ≤ DZ - t - 1 := by
          have hsum := index_yz_lt q
          omega
    · have hjt : (q.1 : ℕ) < t := by omega
      rw [basis_shift_coeff_formula]
      have hchoose : (q.1 : ℕ).choose t = 0 := Nat.choose_eq_zero_of_lt hjt
      rw [hchoose]
      simp
  · omega

theorem constraintMap_apply {F : Type} [Field F]
    (ω : Fin n ↪ F) (u₀ u₁ : Fin n → F) (c : VarIndex → F) (q : ConIndex) :
    constraintMap ω u₀ u₁ c q =
      ((((Polynomial.Bivariate.shift (polyMap c)
        (Polynomial.C (ω q.1))
        (Polynomial.C (u₀ q.1) + Polynomial.X * Polynomial.C (u₁ q.1))).coeff
          (q.2.1 : ℕ)).coeff (q.2.2.1 : ℕ)).coeff (q.2.2.2 : ℕ)) := by
  rfl

private theorem witness_shift_vanish {F : Type} [Field F]
    (ω : Fin n ↪ F) (u₀ u₁ : Fin n → F) (w : KernelWitness ω u₀ u₁) :
    ∀ i s t, s + t < m →
      ((Polynomial.Bivariate.shift (polyMap w.c)
        (Polynomial.C (ω i))
        (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i))).coeff t).coeff s = 0 := by
  intro i s t hst
  apply Polynomial.ext
  intro d
  by_cases hd : d < DZ - t
  · let ft : Fin m := ⟨t, by omega⟩
    have hs : s < m - (ft : ℕ) := by
      apply Nat.lt_sub_of_add_lt
      simpa [ft] using hst
    let q : ConIndex :=
      (i, ⟨ft, ⟨⟨s, hs⟩, ⟨d, by simpa [ft] using hd⟩⟩⟩)
    have hzero := congrFun w.constraints q
    simp only [Pi.zero_apply] at hzero
    rw [constraintMap_apply] at hzero
    exact hzero
  · have hdeg := shift_coeff_natDegree_lt w.c (ω i) (u₀ i) (u₁ i) s t (by omega)
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg (by omega))


private theorem finsetMaxGetD_le (s : Finset ℕ) (B : ℕ)
    (h : ∀ a ∈ s, a ≤ B) : Option.getD (Finset.max s) 0 ≤ B := by
  have hmax : Finset.max s ≤ (B : WithBot ℕ) := by
    apply Finset.max_le
    intro a ha
    exact WithBot.coe_le_coe.mpr (h a ha)
  have hunbot : (Finset.max s).unbotD 0 ≤ B := by
    rw [WithBot.unbotD_le_iff]
    · exact hmax
    · intro hbot
      omega
  have heq : (Finset.max s).unbotD 0 = Option.getD (Finset.max s) 0 := by
    cases Finset.max s <;> rfl
  rw [← heq]
  exact hunbot

private theorem weighted_lt_of_support {F : Type} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0)
    (hcaps : ∀ j a, (Q.coeff j).coeff a ≠ 0 →
      j < DY ∧ a + k * j < DX ∧ ((Q.coeff j).coeff a).natDegree + j < DZ) :
    Polynomial.Bivariate.natWeightedDegree Q 1 k < DX := by
  unfold Polynomial.Bivariate.natWeightedDegree
  obtain ⟨j, hj, hsup⟩ := Finset.exists_mem_eq_sup Q.support
    (Polynomial.nonempty_support_iff.mpr hQ)
    (fun j => 1 * (Q.coeff j).natDegree + k * j)
  rw [hsup]
  norm_num
  have hc : Q.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hi : (Q.coeff j).natDegree ∈ (Q.coeff j).support :=
    Polynomial.natDegree_mem_support_of_nonzero hc
  exact (hcaps j (Q.coeff j).natDegree (Polynomial.mem_support_iff.mp hi)).2.1

private theorem natDegreeY_lt_of_support {F : Type} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0)
    (hcaps : ∀ j a, (Q.coeff j).coeff a ≠ 0 →
      j < DY ∧ a + k * j < DX ∧ ((Q.coeff j).coeff a).natDegree + j < DZ) :
    Polynomial.Bivariate.natDegreeY Q < DY := by
  unfold Polynomial.Bivariate.natDegreeY
  have hj : Q.natDegree ∈ Q.support := Polynomial.natDegree_mem_support_of_nonzero hQ
  have hc : Q.coeff Q.natDegree ≠ 0 := Polynomial.mem_support_iff.mp hj
  obtain ⟨a, ha⟩ := Polynomial.nonempty_support_iff.mpr hc
  exact (hcaps Q.natDegree a (Polynomial.mem_support_iff.mp ha)).1

private theorem DYZ_lt_of_support {F : Type} [Field F]
    (Q : Polynomial (Polynomial (Polynomial F)))
    (hcaps : ∀ j a, (Q.coeff j).coeff a ≠ 0 →
      j < DY ∧ a + k * j < DX ∧ ((Q.coeff j).coeff a).natDegree + j < DZ) :
    Trivariate.D_YZ Q < DZ := by
  unfold Trivariate.D_YZ
  have hle : Option.getD
      (Finset.max (Finset.image
        (fun j => Option.getD
          (Finset.max (Finset.image
            (fun a => j + (Polynomial.Bivariate.coeff Q a j).natDegree)
            (Q.coeff j).support)) 0)
        Q.support)) 0 ≤ DZ - 1 := by
    apply finsetMaxGetD_le
    intro outer houter
    rw [Finset.mem_image] at houter
    obtain ⟨j, hj, rfl⟩ := houter
    apply finsetMaxGetD_le
    intro inner hinner
    rw [Finset.mem_image] at hinner
    obtain ⟨a, ha, rfl⟩ := hinner
    have hcap := (hcaps j a (Polynomial.mem_support_iff.mp ha)).2.2
    unfold Polynomial.Bivariate.coeff
    omega
  norm_num [DZ] at hle ⊢
  omega

/-- The concrete BCHKS interpolation polynomial. Besides nonzeroness and all
multiplicity equations, its support satisfies the three strict integer caps. -/
theorem exists_interpolant {F : Type} [Field F]
    (ω : Fin n ↪ F) (u₀ u₁ : Fin n → F) :
    ∃ Q : Polynomial (Polynomial (Polynomial F)),
      Q ≠ 0 ∧
      (∀ i s t, s + t < m →
        ((Polynomial.Bivariate.shift Q
          (Polynomial.C (ω i))
          (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i))).coeff t).coeff s = 0) ∧
      (∀ j a, ((Q.coeff j).coeff a) ≠ 0 →
        j < DY ∧ a + k * j < DX ∧ ((Q.coeff j).coeff a).natDegree + j < DZ) := by
  obtain ⟨w⟩ := exists_kernelWitness ω u₀ u₁
  refine ⟨polyMap w.c, polyMap_ne_zero w.c w.c_ne_zero, witness_shift_vanish ω u₀ u₁ w, ?_⟩
  intro j a hcoeff
  have hex : ∃ q : VarIndex, (q.1 : ℕ) = j ∧ (q.2.1 : ℕ) = a := by
    by_contra hn
    apply hcoeff
    rw [polyMap_coeff_pair]
    apply Finset.sum_eq_zero
    intro q hq
    rw [if_neg]
    exact fun he => hn ⟨q, he⟩
  obtain ⟨q, hj, ha⟩ := hex
  have hjlt : j < DY := by simpa [← hj] using q.1.isLt
  have halt : a + k * j < DX := by
    have h := q.2.1.isLt
    rw [← hj, ← ha]
    omega
  refine ⟨hjlt, halt, ?_⟩
  rw [polyMap_coeff_pair]
  have hjDZ : j < DZ := by norm_num [DY, DZ] at hjlt ⊢; omega
  have hzle : (∑ r : VarIndex,
      if (r.1 : ℕ) = j ∧ (r.2.1 : ℕ) = a then
        Polynomial.monomial (r.2.2 : ℕ) (w.c r) else 0).natDegree ≤ DZ - j - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro r hr
    by_cases he : (r.1 : ℕ) = j ∧ (r.2.1 : ℕ) = a
    · rw [if_pos he]
      apply (Polynomial.natDegree_monomial_le (w.c r)).trans
      have hh := r.2.2.isLt
      rw [← he.1]
      omega
    · rw [if_neg he]
      simp only [Polynomial.natDegree_zero]
      omega
  omega


/-- Standard degree formulations of the three support caps (and the resulting
`X`-degree cap), packaged with the concrete interpolation equations. -/
theorem exists_interpolant_with_degree_caps {F : Type} [Field F]
    (ω : Fin n ↪ F) (u₀ u₁ : Fin n → F) :
    ∃ Q : Polynomial (Polynomial (Polynomial F)),
      Q ≠ 0 ∧
      (∀ i s t, s + t < m →
        ((Polynomial.Bivariate.shift Q
          (Polynomial.C (ω i))
          (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i))).coeff t).coeff s = 0) ∧
      Polynomial.Bivariate.natWeightedDegree Q 1 k < DX ∧
      Polynomial.Bivariate.degreeX Q < DX ∧
      Polynomial.Bivariate.natDegreeY Q < DY ∧
      Trivariate.D_YZ Q < DZ := by
  obtain ⟨Q, hQ, hvan, hcaps⟩ := exists_interpolant ω u₀ u₁
  have hw := weighted_lt_of_support Q hQ hcaps
  have hx : Polynomial.Bivariate.degreeX Q < DX :=
    (Polynomial.Bivariate.degreeX_le_natWeightedDegree Q k).trans_lt hw
  exact ⟨Q, hQ, hvan, hw, hx, natDegreeY_lt_of_support Q hQ hcaps,
    DYZ_lt_of_support Q hcaps⟩

end BCHKSConcreteGS
end ProximityPrize.SubmissionLower
