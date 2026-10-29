import ProximityPrize.SubmissionBinaryLower.P64Algebra

/-!
# The flow series along a bad curve, division-free (class 6, Lemma HD)

hb.md Theorem BE runs elem.md Lemma HD along a bad curve `C_z`. Here the flow series is built
over `B⟦t⟧` (`B = F[X]` in use) without the fraction field of `F[X, Y, Z]/(R)`: after the
substitution `V = s·φ`, `W = s²·t` (`s = R_Y(X, P_z, z)`) the equation of the curve becomes
`φ + g(φ, t) = 0` with `g` polynomial (`red_spec`), solved modulo `t^(m+1)` by iteration
(`iter`), with uniqueness (`eq_mod_of_residual`).

Orders at `x_i` and degrees in `X` are both handled by an abstract `Grading` (an `ℤ`-indexed
multiplicative family of additive subsets) and linear coefficient profiles `Prof`.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Flow

open PowerSeries

/-- An `ℤ`-indexed multiplicative family of additive subsets of `B`. -/
structure Grading (B : Type*) [CommRing B] where
  mem : ℤ → B → Prop
  zero_mem : ∀ n, mem n 0
  add_mem : ∀ {n : ℤ} {x y : B}, mem n x → mem n y → mem n (x + y)
  neg_mem : ∀ {n : ℤ} {x : B}, mem n x → mem n (-x)
  mul_mem : ∀ {n m : ℤ} {x y : B}, mem n x → mem m y → mem (n + m) (x * y)
  one_mem : mem 0 1

variable {B : Type*} [CommRing B]

namespace Grading

variable (G : Grading B)

lemma congr_mem {n m : ℤ} {x : B} (h : n = m) (hx : G.mem n x) : G.mem m x := h ▸ hx

lemma sum_mem {ι : Type*} (s : Finset ι) {n : ℤ} (f : ι → B) (h : ∀ i ∈ s, G.mem n (f i)) :
    G.mem n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using G.zero_mem n
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact G.add_mem (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma pow_mem {n : ℤ} {x : B} (hx : G.mem n x) (k : ℕ) : G.mem (k * n) (x ^ k) := by
  induction k with
  | zero => simpa using G.one_mem
  | succ k ih =>
      rw [pow_succ]
      exact G.congr_mem (by push_cast; ring) (G.mul_mem ih hx)

/-- The grading by divisibility by powers of `π`. -/
def ord (π : B) : Grading B where
  mem n x := π ^ n.toNat ∣ x
  zero_mem _ := dvd_zero _
  add_mem h h' := dvd_add h h'
  neg_mem h := (dvd_neg).mpr h
  mul_mem {n m x y} h h' := by
    refine dvd_trans ?_ (mul_dvd_mul h h')
    rw [← pow_add]
    exact pow_dvd_pow _ (by omega)
  one_mem := by simp

lemma ord_mono (π : B) {n m : ℤ} {x : B} (h : n ≤ m) (hx : (ord π).mem m x) :
    (ord π).mem n x :=
  dvd_trans (pow_dvd_pow _ (by omega)) hx

lemma ord_of_nat (π : B) {n : ℕ} {x : B} (hx : π ^ n ∣ x) : (ord π).mem n x := by
  simpa [ord] using hx

end Grading

/-- The grading by `X`-degree on `K[X]`: `mem n p` iff `p = 0` or `natDegree p ≤ n`. -/
def degGrading (K : Type*) [Field K] : Grading (Polynomial K) where
  mem n p := p = 0 ∨ (p.natDegree : ℤ) ≤ n
  zero_mem _ := Or.inl rfl
  add_mem {n x y} hx hy := by
    by_cases hxy : x + y = 0
    · exact Or.inl hxy
    right
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · simp at hxy
      · simpa using hy
    rcases hy with rfl | hy
    · simpa using hx
    have := Polynomial.natDegree_add_le x y
    omega
  neg_mem {n x} hx := by
    rcases hx with rfl | hx
    · simp
    · right; simpa using hx
  mul_mem {n m x y} hx hy := by
    rcases hx with rfl | hx
    · simp
    rcases hy with rfl | hy
    · simp
    right
    have := Polynomial.natDegree_mul_le (p := x) (q := y)
    push_cast
    omega
  one_mem := Or.inr (by simp)

lemma degGrading_mono {K : Type*} [Field K] {n m : ℤ} {p : Polynomial K} (h : n ≤ m)
    (hp : (degGrading K).mem n p) : (degGrading K).mem m p := by
  rcases hp with hp | hp
  · exact Or.inl hp
  · exact Or.inr (hp.trans h)

/-- Linear coefficient profile: `coeff k g ∈ G (α + β·k)` for all `k`. -/
def Prof (G : Grading B) (α β : ℤ) (g : B⟦X⟧) : Prop := ∀ k : ℕ, G.mem (α + β * k) (coeff k g)

namespace Prof

variable {G : Grading B} {α α' β : ℤ} {g g' : B⟦X⟧}

lemma congr (h : α = α') (hg : Prof G α β g) : Prof G α' β g := h ▸ hg

lemma zero : Prof G α β 0 := fun k => by simpa using G.zero_mem _

lemma add (hg : Prof G α β g) (hg' : Prof G α β g') : Prof G α β (g + g') := fun k => by
  simpa using G.add_mem (hg k) (hg' k)

lemma neg (hg : Prof G α β g) : Prof G α β (-g) := fun k => by
  simpa using G.neg_mem (hg k)

lemma sum {ι : Type*} (s : Finset ι) (f : ι → B⟦X⟧) (h : ∀ i ∈ s, Prof G α β (f i)) :
    Prof G α β (∑ i ∈ s, f i) := fun k => by
  rw [map_sum]
  exact G.sum_mem s _ fun i hi => h i hi k

lemma mul (hg : Prof G α β g) (hg' : Prof G α' β g') : Prof G (α + α') β (g * g') := fun k => by
  rw [coeff_mul]
  refine G.sum_mem _ _ fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  refine G.congr_mem ?_ (G.mul_mem (hg p.1) (hg' p.2))
  rw [← hp']
  push_cast
  ring

lemma pow (hg : Prof G α β g) (n : ℕ) : Prof G (n * α) β (g ^ n) := by
  induction n with
  | zero =>
      intro k
      rw [pow_zero, coeff_one]
      split_ifs with hk
      · subst hk; simpa using G.one_mem
      · exact G.zero_mem _
  | succ n ih =>
      rw [pow_succ]
      exact (ih.mul hg).congr (by push_cast; ring)

lemma C_mem {c : B} {γ : ℤ} (hc : G.mem γ c) : Prof G γ β (C c) := fun k => by
  rw [coeff_C]
  split_ifs with hk
  · subst hk; simpa using hc
  · exact G.zero_mem _

lemma X_mem : Prof G (-β) β (X : B⟦X⟧) := fun k => by
  rw [coeff_X]
  split_ifs with hk
  · subst hk; simpa using G.one_mem
  · exact G.zero_mem _

end Prof

/-! ### Bivariate evaluation -/

/-- `g(x, y)` for `g ∈ B[W][V]` (outer `V`, inner `W`). -/
noncomputable def Ev (x y : B⟦X⟧) : Polynomial (Polynomial B) →+* B⟦X⟧ :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom C y) x

lemma Ev_apply (x y : B⟦X⟧) (g : Polynomial (Polynomial B)) :
    Ev x y g = g.eval₂ (Polynomial.eval₂RingHom C y) x := rfl

lemma Ev_eq_sum (x y : B⟦X⟧) (g : Polynomial (Polynomial B)) (N : ℕ) (hN : g.natDegree < N) :
    Ev x y g = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range ((g.coeff a).natDegree + 1),
      C ((g.coeff a).coeff b) * y ^ b * x ^ a := by
  rw [Ev_apply, Polynomial.eval₂_eq_sum_range' _ hN]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range, Finset.sum_mul]

lemma Ev_monomial (x y : B⟦X⟧) (a b : ℕ) (c : B) :
    Ev x y (Polynomial.monomial a (Polynomial.monomial b c)) = C c * y ^ b * x ^ a := by
  simp [Ev_apply, Polynomial.eval₂_monomial]

/-- Profiles through bivariate evaluation. -/
theorem prof_Ev {G : Grading B} {αx αy β γ : ℤ} {x y : B⟦X⟧} (hx : Prof G αx β x)
    (hy : Prof G αy β y) (g : Polynomial (Polynomial B))
    (hg : ∀ a b : ℕ, G.mem (γ - a * αx - b * αy) ((g.coeff a).coeff b)) :
    Prof G γ β (Ev x y g) := by
  rw [Ev_eq_sum x y g (g.natDegree + 1) (Nat.lt_succ_self _)]
  refine Prof.sum _ _ fun a _ => Prof.sum _ _ fun b _ => ?_
  exact (((Prof.C_mem (hg a b)).mul (hy.pow b)).mul (hx.pow a)).congr (by ring)

lemma constantCoeff_Ev (x y : B⟦X⟧) (g : Polynomial (Polynomial B)) (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) : constantCoeff (Ev x y g) = (g.coeff 0).coeff 0 := by
  rw [Ev_eq_sum x y g (g.natDegree + 1) (Nat.lt_succ_self _), map_sum]
  rw [Finset.sum_eq_single 0]
  · rw [map_sum, Finset.sum_eq_single 0]
    · simp
    · intro b _ hb
      simp [map_mul, map_pow, hy, zero_pow hb]
    · intro h; simp at h
  · intro a _ ha
    rw [map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [map_mul, map_pow, hx, zero_pow ha]
  · intro h; simp at h

lemma constantCoeff_eval₂_C (q : Polynomial B) (y : B⟦X⟧) (hy : constantCoeff y = 0) :
    constantCoeff (q.eval₂ C y) = q.coeff 0 := by
  rw [Polynomial.eval₂_eq_sum_range, map_sum, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    simp [map_mul, map_pow, hy, zero_pow hb]
  · intro h; simp at h

/-! ### Reduction `f(s·V, s²·W) = s²·(V + g(V, W))` -/

/-- Coefficients of the reduced polynomial. -/
noncomputable def redCoeff (f : Polynomial (Polynomial B)) (s : B) (a b : ℕ) : B :=
  if 2 ≤ a + 2 * b then (f.coeff a).coeff b * s ^ (a + 2 * b - 2) else 0

/-- The reduced polynomial `g` with `f(sV, s²W) = s²(V + g(V, W))`. -/
noncomputable def red (f : Polynomial (Polynomial B)) (s : B) : Polynomial (Polynomial B) :=
  ∑ a ∈ Finset.range (f.natDegree + 2), ∑ b ∈ Finset.range ((f.coeff a).natDegree + 1),
    Polynomial.monomial a (Polynomial.monomial b (redCoeff f s a b))

lemma coeff_red (f : Polynomial (Polynomial B)) (s : B) (a b : ℕ) :
    ((red f s).coeff a).coeff b = redCoeff f s a b := by
  classical
  simp only [red, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  simp only [apply_ite (fun p : Polynomial B => p.coeff b), Polynomial.coeff_monomial,
    Polynomial.coeff_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_range]
  split_ifs with ha hb
  · rfl
  · have : (f.coeff a).coeff b = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [redCoeff, this]
  · have : f.coeff a = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [redCoeff, this]

lemma red_coeff_zero_zero (f : Polynomial (Polynomial B)) (s : B) :
    ((red f s).coeff 0).coeff 0 = 0 := by
  simp [coeff_red, redCoeff]

lemma red_coeff_one_zero (f : Polynomial (Polynomial B)) (s : B) :
    ((red f s).coeff 1).coeff 0 = 0 := by
  simp [coeff_red, redCoeff]

theorem red_spec (f : Polynomial (Polynomial B)) (s : B) (h00 : (f.coeff 0).coeff 0 = 0)
    (h10 : (f.coeff 1).coeff 0 = s) (x y : B⟦X⟧) :
    Ev (C s * x) (C (s ^ 2) * y) f = C (s ^ 2) * (x + Ev x y (red f s)) := by
  classical
  rw [Ev_eq_sum _ _ f (f.natDegree + 2) (by omega)]
  have hred : Ev x y (red f s) = ∑ a ∈ Finset.range (f.natDegree + 2),
      ∑ b ∈ Finset.range ((f.coeff a).natDegree + 1), C (redCoeff f s a b) * y ^ b * x ^ a := by
    simp only [red, map_sum, Ev_monomial]
  rw [hred]
  have hterm : ∀ a b, C ((f.coeff a).coeff b) * (C (s ^ 2) * y) ^ b * (C s * x) ^ a =
      C (s ^ 2) * (C (redCoeff f s a b) * y ^ b * x ^ a) +
        (if a = 1 ∧ b = 0 then C (s ^ 2) * x else 0) := by
    intro a b
    by_cases h2 : 2 ≤ a + 2 * b
    · have hne : ¬ (a = 1 ∧ b = 0) := by omega
      rw [if_neg hne, add_zero, redCoeff, if_pos h2, mul_pow, mul_pow, ← map_pow, ← map_pow,
        ← pow_mul]
      have : s ^ (2 * b) * s ^ a = s ^ 2 * s ^ (a + 2 * b - 2) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      calc C ((f.coeff a).coeff b) * (C (s ^ (2 * b)) * y ^ b) * (C (s ^ a) * x ^ a)
          = C ((f.coeff a).coeff b * (s ^ (2 * b) * s ^ a)) * y ^ b * x ^ a := by
            simp only [map_mul]; ring
        _ = _ := by rw [this]; simp only [map_mul]; ring
    · rw [redCoeff, if_neg h2]
      rcases (by omega : (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 0)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [h00]
      · simp only [h10, pow_two, map_mul, map_zero, mul_zero, zero_add, true_and, if_true,
          pow_zero, pow_one, mul_one]
        ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [mul_add, add_comm]
  congr 1
  rw [Finset.sum_eq_single 1]
  · simp
  · intro a _ ha
    exact Finset.sum_eq_zero fun b _ => by simp [ha]
  · intro h; simp at h

/-! ### Contraction, iteration and uniqueness -/

/-- One step of the Taylor estimate: if `x ≡ x' (mod t^k)`, `k ≥ 1`, both without constant
term, and `g` has no `V`-linear term at `t⁰`, then `g(x, y) ≡ g(x', y) (mod t^(k+1))`. -/
theorem contract (g : Polynomial (Polynomial B)) (hg : ((g.coeff 1).coeff 0) = 0) (y : B⟦X⟧)
    (hy : constantCoeff y = 0) {k : ℕ} (hk : 1 ≤ k) {x x' : B⟦X⟧} (hx' : constantCoeff x' = 0)
    (hxx : (X : B⟦X⟧) ^ k ∣ x - x') : (X : B⟦X⟧) ^ (k + 1) ∣ Ev x y g - Ev x' y g := by
  set Gp : Polynomial B⟦X⟧ := g.map (Polynomial.eval₂RingHom C y) with hGp
  have hev : ∀ u, Ev u y g = Gp.eval u := fun u => by
    rw [Ev_apply, hGp, Polynomial.eval_map]
  obtain ⟨c, hc⟩ := Polynomial.binomExpansion Gp x' (x - x')
  rw [hev, hev, show x = x' + (x - x') by ring, hc]
  have hd : (X : B⟦X⟧) ∣ Gp.derivative.eval x' := by
    rw [X_dvd_iff]
    have h1 : constantCoeff (Gp.derivative.eval x') =
        (Gp.derivative.map constantCoeff).eval (constantCoeff x') := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom]
    rw [h1, hx', ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
      Polynomial.coeff_derivative]
    simp only [hGp, Polynomial.coeff_map, Polynomial.coe_eval₂RingHom]
    rw [map_mul, constantCoeff_eval₂_C _ _ hy, hg, zero_mul]
  obtain ⟨d, hd⟩ := hd
  obtain ⟨e, he⟩ := hxx
  refine ⟨d * e + c * e ^ 2 * X ^ (k - 1), ?_⟩
  rw [hd, he]
  have : (X : B⟦X⟧) ^ (2 * k) = X ^ (k + 1) * X ^ (k - 1) := by
    rw [← pow_add]; congr 1; omega
  calc Gp.eval x' + X * d * (X ^ k * e) + c * (X ^ k * e) ^ 2 - Gp.eval x'
      = X ^ (k + 1) * (d * e) + c * e ^ 2 * X ^ (2 * k) := by ring
    _ = _ := by rw [this]; ring

/-- The iterates `φ₀ = 0`, `φ_{m+1} = -g(φ_m, t)`. -/
noncomputable def iter (g : Polynomial (Polynomial B)) : ℕ → B⟦X⟧
  | 0 => 0
  | m + 1 => -Ev (iter g m) X g

variable (g : Polynomial (Polynomial B)) (h00 : (g.coeff 0).coeff 0 = 0)
  (h10 : (g.coeff 1).coeff 0 = 0)
include h00

lemma constantCoeff_iter (m : ℕ) : constantCoeff (iter g m) = 0 := by
  cases m with
  | zero => simp [iter]
  | succ m =>
      rw [iter, map_neg, constantCoeff_Ev (iter g m) X g (constantCoeff_iter m) (by simp), h00, neg_zero]

include h10

lemma iter_succ_sub (m : ℕ) : (X : B⟦X⟧) ^ (m + 1) ∣ iter g (m + 1) - iter g m := by
  induction m with
  | zero =>
      rw [zero_add, pow_one, X_dvd_iff, iter, iter, sub_zero, map_neg,
        constantCoeff_Ev (iter g 0) X g (by simp [iter]) (by simp), h00, neg_zero]
  | succ m ih =>
      have := contract g h10 X (by simp) (by omega) (constantCoeff_iter g h00 m) ih
      rw [show iter g (m + 1 + 1) - iter g (m + 1) =
        -(Ev (iter g (m + 1)) X g - Ev (iter g m) X g) by simp only [iter]; ring]
      exact (dvd_neg).mpr this

/-- The iterate solves `φ + g(φ, t) ≡ 0 (mod t^(m+1))`. -/
lemma iter_residual (m : ℕ) : (X : B⟦X⟧) ^ (m + 1) ∣ iter g m + Ev (iter g m) X g := by
  have := iter_succ_sub g h00 h10 m
  rw [show iter g m + Ev (iter g m) X g = -(iter g (m + 1) - iter g m) by simp only [iter]; ring]
  exact (dvd_neg).mpr this

omit h00 in
/-- **Uniqueness**: two solutions of `φ + g(φ, t) ≡ 0 (mod t^(m+1))` without constant term agree
modulo `t^(m+1)`. -/
theorem eq_mod_of_residual (m : ℕ) {x x' : B⟦X⟧} (hx : constantCoeff x = 0)
    (hx' : constantCoeff x' = 0) (hr : (X : B⟦X⟧) ^ (m + 1) ∣ x + Ev x X g)
    (hr' : (X : B⟦X⟧) ^ (m + 1) ∣ x' + Ev x' X g) : (X : B⟦X⟧) ^ (m + 1) ∣ x - x' := by
  have key : ∀ k, 1 ≤ k → k ≤ m + 1 → (X : B⟦X⟧) ^ k ∣ x - x' := by
    intro k hk1 hkm
    induction k with
    | zero => omega
    | succ k ih =>
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [zero_add, pow_one, X_dvd_iff, map_sub, hx, hx', sub_zero]
        have hc := contract g h10 X (by simp) hk hx' (ih hk (by omega))
        have h1 : (X : B⟦X⟧) ^ (k + 1) ∣ x + Ev x X g :=
          dvd_trans (pow_dvd_pow _ hkm) hr
        have h2 : (X : B⟦X⟧) ^ (k + 1) ∣ x' + Ev x' X g :=
          dvd_trans (pow_dvd_pow _ hkm) hr'
        have := dvd_sub (dvd_sub h1 h2) hc
        rwa [show x + Ev x X g - (x' + Ev x' X g) - (Ev x X g - Ev x' X g) = x - x' by ring]
          at this
  exact key (m + 1) (by omega) le_rfl

omit h00 h10 in
/-- Profiles of the iterates. -/
theorem prof_iter {G : Grading B} {α β : ℤ}
    (hg : ∀ a b : ℕ, G.mem (α - a * α + b * β) ((g.coeff a).coeff b)) (m : ℕ) :
    Prof G α β (iter g m) := by
  induction m with
  | zero => exact Prof.zero
  | succ m ih =>
      refine (prof_Ev ih Prof.X_mem g fun a b => ?_).neg
      exact G.congr_mem (by ring) (hg a b)

end P64C6Flow
end ProximityPrize.SubmissionBinaryLower
