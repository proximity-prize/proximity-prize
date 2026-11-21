import ProximityPrize.SubmissionLower.ThetaDeriv

/-!
The theta operator on four jet variables.

`Do` is the Euler derivation of the grading by partial sums, written as the Euler derivation of
the index weight plus an index-lowering part.  After the shear `X 0 ↦ X 0 + X 1 - X 2 + X 3`
it becomes `Dc`, the Euler derivation of the contact weight plus a contact-raising part.
The product `(Do - (u - δ + 1)) ⋯ (Do - u)` maps index at most `u` to index at most `u - δ`,
lowers the index by at most `3 δ`, and its kernel has contact order at least `u + 1 - δ`.
-/

namespace ThetaCore
open MvPolynomial ThetaDeriv

section General
variable {σ R : Type*} [CommRing R]

theorem single_le_of_mem (e : σ →₀ ℕ) (i : σ) (hi : i ∈ e.support) :
    Finsupp.single i 1 ≤ e := by
  classical
  rw [Finsupp.le_def]
  intro j
  by_cases h : j = i
  · subst h
    simpa using Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  · simp [Finsupp.single_apply, Ne.symm h]

theorem X_mem_upper (ω : σ → ℕ) (j : σ) {a : ℤ} (h : ((ω j : ℕ) : ℤ) ≤ a) :
    (X j : MvPolynomial σ R) ∈ upper (R := R) ω a := by
  show monomial (Finsupp.single j 1) (1 : R) ∈ upper (R := R) ω a
  apply monomial_mem_upper
  rw [Finsupp.weight_single, one_smul]
  exact h

/-- A derivation whose values on the variables gain `c` units of weighted order gains `c`
units on every polynomial. -/
theorem mkDerivation_mem_order_add (ω : σ → ℕ) (c : ℕ) (f : σ → MvPolynomial σ R)
    (hf : ∀ i, f i ∈ restrictWeightedOrder (R := R) ω (ω i + c)) {a : ℕ}
    {p : MvPolynomial σ R} (hp : p ∈ restrictWeightedOrder (R := R) ω a) :
    mkDerivation R f p ∈ restrictWeightedOrder (R := R) ω (a + c) := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum]
  refine Submodule.sum_mem _ fun e he => ?_
  have hae : a ≤ e.weight ω := mem_restrictWeightedOrder.mp hp e he
  rw [mkDerivation_monomial]
  refine Submodule.smul_mem _ _ ?_
  rw [Finsupp.sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [smul_eq_mul]
  have hw := weight_sub_single ω e i hi
  have hm : monomial (e - Finsupp.single i 1) ((e i : ℕ) : R) ∈
      restrictWeightedOrder (R := R) ω ((e - Finsupp.single i 1).weight ω) :=
    (monomial_mem_restrictWeightedOrder ω _ _ _).mpr (Or.inl le_rfl)
  exact restrictWeightedOrder_anti ω (by omega) (mul_mem_restrictWeightedOrder hm (hf i))

theorem linear_mem_of_monomial (S : Submodule R (MvPolynomial σ R))
    (T : MvPolynomial σ R →ₗ[R] MvPolynomial σ R) (p : MvPolynomial σ R)
    (h : ∀ e ∈ p.support, T (monomial e (p.coeff e)) ∈ S) : T p ∈ S := by
  rw [← p.support_sum_monomial_coeff, map_sum]
  exact Submodule.sum_mem _ h

/-- The Euler derivation of the weight `ω`. -/
noncomputable def euler (ω : σ → ℕ) : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  mkDerivation R fun i => C ((ω i : ℕ) : R) * X i

theorem euler_monomial (ω : σ → ℕ) (e : σ →₀ ℕ) (r : R) :
    euler (R := R) ω (monomial e r) = monomial e (((e.weight ω : ℕ) : R) * r) := by
  classical
  have h : ∀ i ∈ e.support,
      monomial (e - Finsupp.single i 1) ((e i : ℕ) : R) *
          (C ((ω i : ℕ) : R) * X i : MvPolynomial σ R) =
        monomial e (((e i : ℕ) : R) * ((ω i : ℕ) : R)) := by
    intro i hi
    rw [C_mul_X_eq_monomial, monomial_mul_monomial,
      tsub_add_cancel_of_le (single_le_of_mem e i hi)]
  calc euler (R := R) ω (monomial e r)
      = r • ∑ i ∈ e.support, monomial (e - Finsupp.single i 1) ((e i : ℕ) : R) *
            (C ((ω i : ℕ) : R) * X i : MvPolynomial σ R) := mkDerivation_monomial _ _ _ _
    _ = r • ∑ i ∈ e.support, monomial e (((e i : ℕ) : R) * ((ω i : ℕ) : R)) := by
          rw [Finset.sum_congr rfl h]
    _ = r • monomial e (∑ i ∈ e.support, ((e i : ℕ) : R) * ((ω i : ℕ) : R)) := by
          rw [map_sum]
    _ = monomial e (((e.weight ω : ℕ) : R) * r) := by
          rw [smul_monomial]
          refine congrArg (monomial e) ?_
          rw [Finsupp.weight_apply, Finsupp.sum]
          simp only [smul_eq_mul, Nat.cast_sum, Nat.cast_mul]
          exact mul_comm _ _

theorem euler_mem_order (ω ω' : σ → ℕ) {a : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ restrictWeightedOrder (R := R) ω' a) :
    euler (R := R) ω p ∈ restrictWeightedOrder (R := R) ω' a := by
  refine linear_mem_of_monomial _ (euler (R := R) ω).toLinearMap p fun e he => ?_
  show euler (R := R) ω (monomial e (p.coeff e)) ∈ _
  rw [euler_monomial]
  exact (monomial_mem_restrictWeightedOrder ω' _ _ _).mpr
    (Or.inl (mem_restrictWeightedOrder.mp hp e he))

theorem euler_mem_upper (ω ω' : σ → ℕ) {a : ℤ} {p : MvPolynomial σ R}
    (hp : p ∈ upper (R := R) ω' a) : euler (R := R) ω p ∈ upper (R := R) ω' a := by
  refine linear_mem_of_monomial _ (euler (R := R) ω).toLinearMap p fun e he => ?_
  show euler (R := R) ω (monomial e (p.coeff e)) ∈ _
  rw [euler_monomial]
  exact monomial_mem_upper ω' e _ (mem_upper.mp hp e he)

theorem euler_sub_mem_order (ω : σ → ℕ) {a : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ restrictWeightedOrder (R := R) ω a) :
    euler (R := R) ω p - ((a : ℕ) : R) • p ∈ restrictWeightedOrder (R := R) ω (a + 1) := by
  refine linear_mem_of_monomial _
    ((euler (R := R) ω).toLinearMap - ((a : ℕ) : R) • LinearMap.id) p fun e he => ?_
  show euler (R := R) ω (monomial e (p.coeff e)) - ((a : ℕ) : R) • monomial e (p.coeff e) ∈ _
  have hae : a ≤ e.weight ω := mem_restrictWeightedOrder.mp hp e he
  rw [euler_monomial, smul_monomial, smul_eq_mul]
  by_cases h : e.weight ω = a
  · rw [h, sub_self]
    exact Submodule.zero_mem _
  · have h1 : a + 1 ≤ e.weight ω := by omega
    exact Submodule.sub_mem _
      ((monomial_mem_restrictWeightedOrder ω _ _ _).mpr (Or.inl h1))
      ((monomial_mem_restrictWeightedOrder ω _ _ _).mpr (Or.inl h1))

theorem euler_sub_mem_upper (ω : σ → ℕ) {w : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ upper (R := R) ω (w : ℤ)) :
    euler (R := R) ω p - ((w : ℕ) : R) • p ∈ upper (R := R) ω ((w : ℤ) - 1) := by
  refine linear_mem_of_monomial _
    ((euler (R := R) ω).toLinearMap - ((w : ℕ) : R) • LinearMap.id) p fun e he => ?_
  show euler (R := R) ω (monomial e (p.coeff e)) - ((w : ℕ) : R) • monomial e (p.coeff e) ∈ _
  have hwe : ((e.weight ω : ℕ) : ℤ) ≤ w := mem_upper.mp hp e he
  rw [euler_monomial, smul_monomial, smul_eq_mul]
  by_cases h : e.weight ω = w
  · rw [h, sub_self]
    exact Submodule.zero_mem _
  · have h1 : ((e.weight ω : ℕ) : ℤ) ≤ (w : ℤ) - 1 := by omega
    exact Submodule.sub_mem _ (monomial_mem_upper ω e _ h1) (monomial_mem_upper ω e _ h1)

/-- Euler derivation plus an order-raising part: `D - a` raises order `a`. -/
theorem sum_sub_mem_order (ω : σ → ℕ) (g : σ → MvPolynomial σ R)
    (hg : ∀ i, g i ∈ restrictWeightedOrder (R := R) ω (ω i + 1)) {a : ℕ}
    {p : MvPolynomial σ R} (hp : p ∈ restrictWeightedOrder (R := R) ω a) :
    (euler (R := R) ω + mkDerivation R g) p - ((a : ℕ) : R) • p ∈
      restrictWeightedOrder (R := R) ω (a + 1) := by
  have h : (euler (R := R) ω + mkDerivation R g) p - ((a : ℕ) : R) • p =
      (euler (R := R) ω p - ((a : ℕ) : R) • p) + mkDerivation R g p := by
    show euler (R := R) ω p + mkDerivation R g p - ((a : ℕ) : R) • p = _
    abel
  rw [h]
  exact Submodule.add_mem _ (euler_sub_mem_order ω hp) (mkDerivation_mem_order_add ω 1 g hg hp)

/-- Euler derivation plus a weight-lowering part: `D - w` lowers the bound `w`. -/
theorem sum_sub_mem_upper (ω : σ → ℕ) (g : σ → MvPolynomial σ R)
    (hg : ∀ i, g i ∈ upper (R := R) ω ((ω i : ℤ) - 1)) {w : ℕ}
    {p : MvPolynomial σ R} (hp : p ∈ upper (R := R) ω (w : ℤ)) :
    (euler (R := R) ω + mkDerivation R g) p - ((w : ℕ) : R) • p ∈
      upper (R := R) ω ((w : ℤ) - 1) := by
  have h : (euler (R := R) ω + mkDerivation R g) p - ((w : ℕ) : R) • p =
      (euler (R := R) ω p - ((w : ℕ) : R) • p) + mkDerivation R g p := by
    show euler (R := R) ω p + mkDerivation R g p - ((w : ℕ) : R) • p = _
    abel
  rw [h]
  exact Submodule.add_mem _ (euler_sub_mem_upper ω hp) (mkDerivation_mem_upper ω 1 g hg hp)

theorem sum_mem_order (ω ω' : σ → ℕ) (c : ℕ) (g : σ → MvPolynomial σ R)
    (hg : ∀ i, g i ∈ restrictWeightedOrder (R := R) ω' (ω' i - c)) {a : ℕ}
    {p : MvPolynomial σ R} (hp : p ∈ restrictWeightedOrder (R := R) ω' a) :
    (euler (R := R) ω + mkDerivation R g) p ∈ restrictWeightedOrder (R := R) ω' (a - c) := by
  show euler (R := R) ω p + mkDerivation R g p ∈ _
  exact Submodule.add_mem _
    (restrictWeightedOrder_anti ω' (Nat.sub_le a c) (euler_mem_order ω ω' hp))
    (mkDerivation_mem_order ω' c g hg hp)

theorem sum_mem_upper (ω ω' : σ → ℕ) (g : σ → MvPolynomial σ R)
    (hg : ∀ i, g i ∈ upper (R := R) ω' ((ω' i : ℤ) - 0)) {a : ℤ}
    {p : MvPolynomial σ R} (hp : p ∈ upper (R := R) ω' a) :
    (euler (R := R) ω + mkDerivation R g) p ∈ upper (R := R) ω' a := by
  show euler (R := R) ω p + mkDerivation R g p ∈ _
  have h := mkDerivation_mem_upper ω' 0 g hg hp
  rw [sub_zero] at h
  exact Submodule.add_mem _ (euler_mem_upper ω ω' hp) h

/-- The operator `D - w`. -/
noncomputable def shift (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (w : ℕ) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  D.toLinearMap - ((w : ℕ) : R) • LinearMap.id

theorem shift_apply (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (w : ℕ)
    (p : MvPolynomial σ R) : shift D w p = D p - ((w : ℕ) : R) • p := rfl

/-- The product `(D - (u - n + 1)) ⋯ (D - u)`, the factor `D - u` applied first. -/
noncomputable def desc (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (u : ℕ) :
    ℕ → (MvPolynomial σ R →ₗ[R] MvPolynomial σ R)
  | 0 => LinearMap.id
  | n + 1 => shift D (u - n) ∘ₗ desc D u n

theorem desc_zero (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (u : ℕ)
    (x : MvPolynomial σ R) : desc D u 0 x = x := rfl

theorem desc_succ (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (u n : ℕ)
    (x : MvPolynomial σ R) : desc D u (n + 1) x = shift D (u - n) (desc D u n x) := rfl

theorem desc_mem (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (u : ℕ)
    (S : Submodule R (MvPolynomial σ R)) (hD : ∀ p, p ∈ S → D p ∈ S) :
    ∀ n x, x ∈ S → desc D u n x ∈ S := by
  intro n
  induction n with
  | zero => intro x hx; rw [desc_zero]; exact hx
  | succ n ih =>
    intro x hx
    rw [desc_succ, shift_apply]
    exact S.sub_mem (hD _ (ih x hx)) (S.smul_mem _ (ih x hx))

end General

section Jet
variable {k : Type*} [Field k]

/-- The index weight. -/
def ωo : Fin 4 → ℕ := Fin.val
/-- The contact weight after the shear. -/
def ωc : Fin 4 → ℕ := ![3, 0, 1, 2]
/-- The degree weight. -/
def ωg : Fin 4 → ℕ := fun _ => 1

/-- The index-lowering part of the derivation. -/
noncomputable def nU : Fin 4 → MvPolynomial (Fin 4) k :=
  ![0, -X 0, X 0 - X 1, -X 0 + X 1 - X 2]
/-- The contact-raising part of the sheared derivation. -/
noncomputable def nC : Fin 4 → MvPolynomial (Fin 4) k :=
  ![0, -X 0 + X 2 - X 3, X 0 + X 3, -X 0]
/-- The shear. -/
noncomputable def shear : Fin 4 → MvPolynomial (Fin 4) k :=
  ![X 0 + X 1 - X 2 + X 3, X 1, X 2, X 3]

/-- Euler derivation of the grading by partial sums. -/
noncomputable def Do : Derivation k (MvPolynomial (Fin 4) k) (MvPolynomial (Fin 4) k) :=
  euler ωo + mkDerivation k nU
/-- The same derivation after the shear. -/
noncomputable def Dc : Derivation k (MvPolynomial (Fin 4) k) (MvPolynomial (Fin 4) k) :=
  euler ωc + mkDerivation k nC

theorem nU_mem (S : Submodule k (MvPolynomial (Fin 4) k)) :
    ∀ i : Fin 4, (∀ j : Fin 4, j < i → (X j : MvPolynomial (Fin 4) k) ∈ S) →
      nU (k := k) i ∈ S := by
  intro i
  fin_cases i <;> intro h
  · exact S.zero_mem
  · exact S.neg_mem (h 0 (by decide))
  · exact S.sub_mem (h 0 (by decide)) (h 1 (by decide))
  · exact S.sub_mem (S.add_mem (S.neg_mem (h 0 (by decide))) (h 1 (by decide)))
      (h 2 (by decide))

theorem nC_mem (S : Submodule k (MvPolynomial (Fin 4) k)) :
    ∀ i : Fin 4, (∀ j : Fin 4, ωc i < ωc j → (X j : MvPolynomial (Fin 4) k) ∈ S) →
      nC (k := k) i ∈ S := by
  intro i
  fin_cases i <;> intro h
  · exact S.zero_mem
  · exact S.sub_mem (S.add_mem (S.neg_mem (h 0 (by decide))) (h 2 (by decide)))
      (h 3 (by decide))
  · exact S.add_mem (h 0 (by decide)) (h 3 (by decide))
  · exact S.neg_mem (h 0 (by decide))

theorem gen (i : Fin 4) :
    bind₁ (shear (k := k)) (Do (k := k) (X i)) = Dc (k := k) (bind₁ shear (X i)) := by
  fin_cases i <;>
    simp [Do, Dc, euler, nU, nC, shear, ωo, ωc, mkDerivation_X, map_ofNat] <;>
    ring

theorem intertwine (p : MvPolynomial (Fin 4) k) :
    bind₁ (shear (k := k)) (Do (k := k) p) = Dc (k := k) (bind₁ shear p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [derivation_C, map_zero, bind₁_C_right]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [Derivation.leibniz, map_add, map_mul, smul_eq_mul, hp, gen i]

theorem intertwine_desc (u : ℕ) : ∀ (n : ℕ) (x : MvPolynomial (Fin 4) k),
    bind₁ (shear (k := k)) (desc Do u n x) = desc Dc u n (bind₁ shear x) := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    rw [desc_succ, desc_succ, shift_apply, shift_apply, map_sub, map_smul, intertwine, ih]

/-! ### Index side -/

theorem Do_shift_upper {w : ℕ} {p : MvPolynomial (Fin 4) k}
    (hp : p ∈ upper (R := k) ωo (w : ℤ)) :
    shift (Do (k := k)) w p ∈ upper (R := k) ωo ((w : ℤ) - 1) := by
  rw [shift_apply]
  refine sum_sub_mem_upper ωo nU (fun i => nU_mem _ i fun j hj => ?_) hp
  apply X_mem_upper
  have hji : j.val < i.val := hj
  simp only [ωo]
  omega

theorem Do_order {a : ℕ} {p : MvPolynomial (Fin 4) k}
    (hp : p ∈ restrictWeightedOrder (R := k) ωo a) :
    Do (k := k) p ∈ restrictWeightedOrder (R := k) ωo (a - 3) := by
  refine sum_mem_order ωo ωo 3 nU (fun i => ?_) hp
  have h : ωo i - 3 = 0 := by
    have := i.isLt
    simp only [ωo]
    omega
  rw [h, restrictWeightedOrder_zero]
  exact Submodule.mem_top

theorem Do_grade_order {a : ℕ} {p : MvPolynomial (Fin 4) k}
    (hp : p ∈ restrictWeightedOrder (R := k) ωg a) :
    Do (k := k) p ∈ restrictWeightedOrder (R := k) ωg a := by
  have h := sum_mem_order (R := k) ωo ωg 0 nU
    (fun i => nU_mem _ i fun j _ => X_mem_restrictWeightedOrder ωg j (by simp [ωg])) hp
  exact h

theorem Do_grade_upper {a : ℤ} {p : MvPolynomial (Fin 4) k}
    (hp : p ∈ upper (R := k) ωg a) : Do (k := k) p ∈ upper (R := k) ωg a :=
  sum_mem_upper ωo ωg nU
    (fun i => nU_mem _ i fun j _ => X_mem_upper ωg j (by simp [ωg])) hp

theorem desc_upper (u : ℕ) : ∀ n : ℕ, n ≤ u + 1 → ∀ x : MvPolynomial (Fin 4) k,
    x ∈ upper (R := k) ωo (u : ℤ) →
      desc (Do (k := k)) u n x ∈ upper (R := k) ωo ((u : ℤ) - n) := by
  intro n
  induction n with
  | zero =>
    intro _ x hx
    rw [desc_zero]
    exact upper_mono ωo (by simp) hx
  | succ n ih =>
    intro hn x hx
    rw [desc_succ]
    have h1 := ih (by omega) x hx
    have h2 : desc (Do (k := k)) u n x ∈ upper (R := k) ωo ((u - n : ℕ) : ℤ) :=
      upper_mono ωo (by omega) h1
    exact upper_mono ωo (by push_cast; omega) (Do_shift_upper h2)

theorem desc_order (u : ℕ) {a : ℕ} : ∀ (n : ℕ) (x : MvPolynomial (Fin 4) k),
    x ∈ restrictWeightedOrder (R := k) ωo a →
      desc (Do (k := k)) u n x ∈ restrictWeightedOrder (R := k) ωo (a - 3 * n) := by
  intro n
  induction n with
  | zero => intro x hx; rw [desc_zero]; exact hx
  | succ n ih =>
    intro x hx
    rw [desc_succ, shift_apply]
    have h1 := ih x hx
    have h2 := Do_order h1
    exact Submodule.sub_mem _ (restrictWeightedOrder_anti ωo (by omega) h2)
      (Submodule.smul_mem _ _ (restrictWeightedOrder_anti ωo (by omega) h1))

/-! ### Contact side -/

theorem nC_order (i : Fin 4) :
    nC (k := k) i ∈ restrictWeightedOrder (R := k) ωc (ωc i + 1) :=
  nC_mem _ i fun j hj => X_mem_restrictWeightedOrder ωc j hj

theorem Dc_order {a : ℕ} {p : MvPolynomial (Fin 4) k}
    (hp : p ∈ restrictWeightedOrder (R := k) ωc a) :
    Dc (k := k) p ∈ restrictWeightedOrder (R := k) ωc a := by
  have h := sum_mem_order (R := k) ωc ωc 0 nC
    (fun i => restrictWeightedOrder_anti ωc (by omega) (nC_order i)) hp
  exact h

/-- If `v` has contact order `a` and `(Dc - w) v` has order `a + 1` with `a < w`, then `v` has
order `a + 1`. -/
theorem peel_one {a w : ℕ} (haw : a < w) (hne : ((w - a : ℕ) : k) ≠ 0)
    {v : MvPolynomial (Fin 4) k} (hv : v ∈ restrictWeightedOrder (R := k) ωc a)
    (hs : shift (Dc (k := k)) w v ∈ restrictWeightedOrder (R := k) ωc (a + 1)) :
    v ∈ restrictWeightedOrder (R := k) ωc (a + 1) := by
  have h1 := sum_sub_mem_order (R := k) ωc nC nC_order hv
  rw [shift_apply] at hs
  have h2 : ((w - a : ℕ) : k) • v =
      (Dc (k := k) v - ((a : ℕ) : k) • v) - (Dc (k := k) v - ((w : ℕ) : k) • v) := by
    rw [Nat.cast_sub haw.le, sub_smul]
    abel
  have h3 : ((w - a : ℕ) : k) • v ∈ restrictWeightedOrder (R := k) ωc (a + 1) := by
    rw [h2]
    exact Submodule.sub_mem _ h1 hs
  have h4 := Submodule.smul_mem _ (((w - a : ℕ) : k)⁻¹) h3
  rwa [inv_smul_smul₀ hne] at h4

theorem peel (u a : ℕ) (hchar : ∀ n : ℕ, 0 < n → n ≤ u → ((n : ℕ) : k) ≠ 0) :
    ∀ n : ℕ, a + n ≤ u → ∀ z : MvPolynomial (Fin 4) k,
      z ∈ restrictWeightedOrder (R := k) ωc a →
      desc (Dc (k := k)) u n z ∈ restrictWeightedOrder (R := k) ωc (a + 1) →
      z ∈ restrictWeightedOrder (R := k) ωc (a + 1) := by
  intro n
  induction n with
  | zero => intro _ z _ h; rw [desc_zero] at h; exact h
  | succ n ih =>
    intro hn z hz h
    rw [desc_succ] at h
    have hmem := desc_mem (Dc (k := k)) u (restrictWeightedOrder (R := k) ωc a)
      (fun p hp => Dc_order hp) n z hz
    have hstep := peel_one (k := k) (a := a) (w := u - n) (by omega)
      (hchar (u - n - a) (by omega) (by omega)) hmem h
    exact ih (by omega) z hz hstep

/-- A polynomial killed by `(Dc - (u - δ + 1)) ⋯ (Dc - u)` has contact order `u + 1 - δ`. -/
theorem contact_of_desc_eq_zero (u δ : ℕ)
    (hchar : ∀ n : ℕ, 0 < n → n ≤ u → ((n : ℕ) : k) ≠ 0)
    (z : MvPolynomial (Fin 4) k) (hz : desc (Dc (k := k)) u δ z = 0) :
    ∀ a : ℕ, a + δ ≤ u + 1 → z ∈ restrictWeightedOrder (R := k) ωc a := by
  intro a
  induction a with
  | zero =>
    intro _
    rw [restrictWeightedOrder_zero]
    exact Submodule.mem_top
  | succ a ih =>
    intro ha
    refine peel u a hchar δ (by omega) z (ih (by omega)) ?_
    rw [hz]
    exact Submodule.zero_mem _

/-- The kernel of the theta operator has contact order `u + 1 - δ` after the shear. -/
theorem shear_order_of_desc_eq_zero (u δ : ℕ) (hδ : δ ≤ u + 1)
    (hchar : ∀ n : ℕ, 0 < n → n ≤ u → ((n : ℕ) : k) ≠ 0)
    (x : MvPolynomial (Fin 4) k) (hx : desc (Do (k := k)) u δ x = 0) :
    bind₁ (shear (k := k)) x ∈ restrictWeightedOrder (R := k) ωc (u + 1 - δ) := by
  refine contact_of_desc_eq_zero u δ hchar _ ?_ _ (by omega)
  rw [← intertwine_desc, hx, map_zero]

#print axioms shear_order_of_desc_eq_zero
#print axioms desc_upper
#print axioms desc_order

end Jet

end ThetaCore
