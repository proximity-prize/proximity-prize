import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.Separable
namespace ProximityPrize.SubmissionLower.HFree6812

open WithZero Polynomial

section Core

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (v : Valuation L ℤᵐ⁰) (D : Derivation K L L)

def Tame (Λ : ℤᵐ⁰) (z : L) : Prop := v z ≤ 1 ∧ v (D z) ≤ Λ

omit [Field K] [Algebra K L] in
theorem v_natCast_le_one (n : ℕ) : v (n : L) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (v.map_add _ _).trans (max_le ih (by simp))

omit [Field K] [Algebra K L] in
theorem v_nsmul_le (n : ℕ) (x : L) : v (n • x) ≤ v x := by
  rw [nsmul_eq_mul, v.map_mul]
  exact mul_le_of_le_one_left' (v_natCast_le_one v n)

def tameSubring (Λ : ℤᵐ⁰) : Subring L where
  carrier := {z | Tame v D Λ z}
  mul_mem' := by
    rintro a b ⟨ha, hDa⟩ ⟨hb, hDb⟩
    refine ⟨by rw [v.map_mul]; exact mul_le_one' ha hb, ?_⟩
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    refine (v.map_add _ _).trans (max_le ?_ ?_) <;> rw [v.map_mul]
    · exact (mul_le_mul_left ha _).trans (by rw [one_mul]; exact hDb)
    · exact (mul_le_mul_left hb _).trans (by rw [one_mul]; exact hDa)
  one_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, hDa⟩ ⟨hb, hDb⟩
    exact ⟨(v.map_add _ _).trans (max_le ha hb),
      by rw [map_add]; exact (v.map_add _ _).trans (max_le hDa hDb)⟩
  zero_mem' := ⟨by simp, by simp⟩
  neg_mem' := by
    rintro a ⟨ha, hDa⟩
    exact ⟨by rw [v.map_neg]; exact ha, by rw [map_neg, v.map_neg]; exact hDa⟩

theorem Tame.mono {Λ Λ' : ℤᵐ⁰} (h : Λ ≤ Λ') {z : L} (hz : Tame v D Λ z) :
    Tame v D Λ' z :=
  ⟨hz.1, hz.2.trans h⟩

def ResiduallySeparable (Λ : ℤᵐ⁰) : Prop :=
  ∀ z : L, v z ≤ 1 → ∃ μ : L[X], (∀ j, Tame v D Λ (μ.coeff j)) ∧
    v (μ.eval z) < 1 ∧ v (μ.derivative.eval z) = 1

theorem ResiduallySeparable.mono {Λ Λ' : ℤᵐ⁰} (h : Λ ≤ Λ')
    (hsep : ResiduallySeparable v D Λ) : ResiduallySeparable v D Λ' := by
  intro z hz
  obtain ⟨μ, hμ, h1, h2⟩ := hsep z hz
  exact ⟨μ, fun j => (hμ j).mono v D h, h1, h2⟩

def CrudeBound (C : ℤ) : Prop := ∀ z : L, v z ≤ 1 → v (D z) ≤ exp C

theorem derivation_eval (μ : L[X]) (z : L) :
    D (μ.eval z) = μ.derivative.eval z * D z + ∑ n ∈ μ.support, z ^ n * D (μ.coeff n) := by
  rw [Polynomial.eval_eq_sum, Polynomial.derivative_eval, Polynomial.sum_def,
    Polynomial.sum_def, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Derivation.leibniz, Derivation.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

theorem derivation_eval_sub_le (Λ : ℤᵐ⁰) (μ : L[X]) (hμ : ∀ j, Tame v D Λ (μ.coeff j))
    (z : L) (hz : v z ≤ 1) :
    v (D (μ.eval z) - μ.derivative.eval z * D z) ≤ Λ := by
  rw [derivation_eval, add_sub_cancel_left]
  refine v.map_sum_le fun n _ => ?_
  rw [v.map_mul, v.map_pow]
  exact (mul_le_mul_left (pow_le_one' hz n) _).trans (by rw [one_mul]; exact (hμ n).2)

theorem exists_eq_pi_mul (π : L) (hπ : v π = exp (-1)) (x : L) (hx : v x < 1) :
    ∃ e : L, v e ≤ 1 ∧ x = π * e := by
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, v.map_zero] at hπ; exact exp_ne_zero hπ.symm
  refine ⟨x / π, ?_, by field_simp⟩
  have hx' : v x ≤ exp (-1) := by
    rw [← lt_mul_exp_iff_le exp_ne_zero, ← exp_add]; simpa using hx
  rw [map_div₀, hπ, div_le_iff₀ exp_pos, one_mul]
  exact hx'

theorem bootstrap (π : L) (hπ : v π = exp (-1)) (Λ : ℤᵐ⁰) (hπΛ : v (D π) ≤ Λ) (C : ℤ)
    (hcont : CrudeBound v D C) (hsep : ResiduallySeparable v D Λ) :
    ∀ N : ℕ, ∀ z : L, v z ≤ 1 → v (D z) ≤ max Λ (exp (C - N)) := by
  intro N
  induction N with
  | zero => intro z hz; simpa using le_max_of_le_right (hcont z hz)
  | succ N ih =>
    intro z hz
    obtain ⟨μ, hμ, hμz, hμ'⟩ := hsep z hz
    obtain ⟨e, he, hμe⟩ := exists_eq_pi_mul v π hπ _ hμz
    have hkey : μ.derivative.eval z * D z =
        π * D e + e * D π - (D (μ.eval z) - μ.derivative.eval z * D z) := by
      rw [hμe, Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
    have hvz : v (D z) = v (μ.derivative.eval z * D z) := by rw [v.map_mul, hμ', one_mul]
    rw [hvz, hkey]
    refine (v.map_sub _ _).trans (max_le ((v.map_add _ _).trans (max_le ?_ ?_)) ?_)
    · rw [v.map_mul, hπ]
      refine (mul_le_mul_right (ih e he) _).trans ?_
      rw [mul_max]
      refine max_le_max ?_ ?_
      · exact mul_le_of_le_one_left' (by rw [← exp_zero, exp_le_exp]; omega)
      · rw [← exp_add]; simp only [exp_le_exp]; push_cast; omega
    · rw [v.map_mul]
      exact le_max_of_le_left ((mul_le_mul_left he _).trans (by rw [one_mul]; exact hπΛ))
    · exact le_max_of_le_left (derivation_eval_sub_le v D Λ μ hμ z hz)

theorem integral_bound_gen (π : L) (hπ : v π = exp (-1)) (Λ : ℤᵐ⁰) (hΛ : 1 ≤ Λ)
    (hπΛ : v (D π) ≤ Λ) (C : ℤ) (hcont : CrudeBound v D C)
    (hsep : ResiduallySeparable v D Λ) :
    ∀ u : L, v u ≤ 1 → v (D u) ≤ Λ := by
  intro u hu
  refine (bootstrap v D π hπ Λ hπΛ C hcont hsep C.toNat u hu).trans (max_le le_rfl ?_)
  refine le_trans ?_ hΛ
  rw [← exp_zero, exp_le_exp]; omega

omit [Field K] [Algebra K L] in
theorem pi_ne_zero (π : L) (hπ : v π = exp (-1)) : π ≠ 0 := by
  intro h; rw [h, v.map_zero] at hπ; exact exp_ne_zero hπ.symm

theorem exp_neg_one_pow (k : ℕ) : (exp (-1 : ℤ)) ^ k = exp (-(k : ℤ)) := by
  rw [← exp_nsmul]; congr 1; simp

omit [Field K] [Algebra K L] in

theorem unit_part (π : L) (hπ : v π = exp (-1)) (f : L) (n : ℕ)
    (hf : v f = exp (-(n : ℤ))) :
    v (f / π ^ n) = 1 ∧ f = f / π ^ n * π ^ n := by
  have hπn : π ^ n ≠ 0 := pow_ne_zero _ (pi_ne_zero v π hπ)
  refine ⟨?_, by field_simp⟩
  rw [map_div₀, v.map_pow, hπ, exp_neg_one_pow, hf, div_self exp_ne_zero]

theorem order_of_integral (π : L) (hπ : v π = exp (-1)) (θ : ℤ)
    (hint : ∀ u : L, v u ≤ 1 → v (D u) ≤ exp θ) (hπθ : v (D π) ≤ exp (θ - 1)) :
    ∀ f : L, v (D f) ≤ exp θ * v f := by
  have hI : ∀ f : L, v f ≤ 1 → v (D f) ≤ exp θ * v f := by
    intro f hf
    by_cases hf0 : f = 0
    · simp [hf0]
    have hvf : v f ≠ 0 := (Valuation.ne_zero_iff v).2 hf0
    have hm : v f = exp (v f).log := (exp_log hvf).symm
    have hm0 : (v f).log ≤ 0 := by
      rw [← exp_le_exp, ← hm, exp_zero]; exact hf
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (v f).log = -(n : ℤ) := ⟨((v f).log).natAbs, by omega⟩
    rw [hn] at hm
    obtain ⟨hu, hfu⟩ := unit_part v π hπ f n hm
    set u := f / π ^ n
    rw [hm, hfu, Derivation.leibniz, Derivation.leibniz_pow]
    simp only [smul_eq_mul]
    refine (v.map_add _ _).trans (max_le ?_ ?_)
    · cases n with
      | zero => simp
      | succ k =>
        rw [v.map_mul, hu, one_mul]
        refine (v_nsmul_le v _ _).trans ?_
        rw [v.map_mul, v.map_pow, hπ, Nat.add_sub_cancel, exp_neg_one_pow]
        refine (mul_le_mul_right hπθ _).trans ?_
        rw [← exp_add, ← exp_add, exp_le_exp]; push_cast; omega
    · rw [v.map_mul, v.map_pow, hπ, exp_neg_one_pow, mul_comm (exp θ)]
      exact mul_le_mul_right (hint u hu.le) _
  intro f
  by_cases hf : v f ≤ 1
  · exact hI f hf
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have hvf : v f ≠ 0 := (Valuation.ne_zero_iff v).2 hf0
  have hg : v f⁻¹ ≤ 1 := by
    rw [map_inv₀]; exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hf))
  have h := hI f⁻¹ hg
  rw [← inv_inv f, Derivation.leibniz_inv, smul_eq_mul, v.map_mul, v.map_neg, v.map_pow,
    inv_inv]
  calc v f ^ 2 * v (D f⁻¹) ≤ v f ^ 2 * (exp θ * v f⁻¹) := mul_le_mul_right h _
    _ = exp θ * v f := by rw [map_inv₀]; field_simp

theorem pole_le_of_le (θ : ℤ) (hθ : 0 ≤ θ) (f g : L) (h : v g ≤ exp θ * v f) :
    max 0 (v g).log ≤ max 0 (v f).log + θ := by
  by_cases hg : v g = 0
  · rw [hg, log_zero]; omega
  have hf : v f ≠ 0 := by
    intro hf; rw [hf, mul_zero] at h; exact hg (le_antisymm h zero_le)
  have hlog : (v g).log ≤ θ + (v f).log := by
    rw [← log_exp θ, ← log_mul exp_ne_zero hf, log_le_log hg (mul_ne_zero exp_ne_zero hf)]
    exact h
  omega

theorem integral_bound (π : L) (hπ : v π = exp (-1)) (s : ℤ) (hs : 0 ≤ s) (C : ℤ)
    (hcont : CrudeBound v D C) (hsep : ResiduallySeparable v D (exp s)) :
    ∀ u : L, v u ≤ 1 → v (D u) ≤ max (exp s) (v (D π)) :=
  integral_bound_gen v D π hπ _ (le_max_of_le_left (by rw [← exp_zero, exp_le_exp]; exact hs))
    (le_max_right _ _) C hcont (hsep.mono v D (le_max_left _ _))

theorem derivation_order (π : L) (hπ : v π = exp (-1)) (s θ : ℤ) (hs : 0 ≤ s)
    (hsθ : s ≤ θ) (hπθ : v (D π) ≤ exp (θ - 1)) (C : ℤ)
    (hcont : CrudeBound v D C) (hsep : ResiduallySeparable v D (exp s)) (f : L) :
    v (D f) ≤ exp θ * v f := by
  refine order_of_integral v D π hπ θ (fun u hu => ?_) hπθ f
  refine (integral_bound v D π hπ s hs C hcont hsep u hu).trans (max_le ?_ ?_)
  · rw [exp_le_exp]; exact hsθ
  · exact hπθ.trans (by rw [exp_le_exp]; omega)

theorem pi_bound_general [v.IsTrivialOn K] (π : L) (hπ : v π = exp (-1)) (s T : ℤ)
    (hint : ∀ u : L, v u ≤ 1 → v (D u) ≤ max (exp s) (v (D π)))
    (f : L) (n : ℕ) (hn : (n : K) ≠ 0) (hf : v f = exp (-(n : ℤ)))
    (hDf : v (D f) ≤ exp T) :
    v (D π) ≤ exp (max s (T + n) - 1) := by
  by_contra hlt
  rw [not_le] at hlt
  have hDπ0 : v (D π) ≠ 0 := (exp_pos.trans hlt).ne'
  have hd : v (D π) = exp (v (D π)).log := (exp_log hDπ0).symm
  rw [hd, exp_lt_exp] at hlt
  have hn1 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hu, hfu⟩ := unit_part v π hπ f (k + 1) hf
  set u := f / π ^ (k + 1)
  have hvn : v ((k + 1 : ℕ) : L) = 1 := by
    rw [← map_natCast (algebraMap K L)]; exact Valuation.IsTrivialOn.eq_one _ hn
  rw [hfu, Derivation.leibniz, Derivation.leibniz_pow] at hDf
  simp only [smul_eq_mul] at hDf
  have hA : v (u * ((k + 1) • (π ^ (k + 1 - 1) * D π))) = exp ((v (D π)).log - k) := by
    rw [v.map_mul, hu, one_mul, nsmul_eq_mul, v.map_mul, hvn, one_mul,
      v.map_mul, v.map_pow, hπ, Nat.add_sub_cancel, exp_neg_one_pow, hd, ← exp_add, log_exp]
    congr 1; ring
  have hs1 : s - 1 < (v (D π)).log := lt_of_le_of_lt (by omega) hlt
  have hB : v (π ^ (k + 1) * D u) < exp ((v (D π)).log - k) := by
    rw [v.map_mul, v.map_pow, hπ, exp_neg_one_pow]
    have h1 := hint u hu.le
    rw [hd] at h1
    refine lt_of_le_of_lt (mul_le_mul_right h1 _) ?_
    rw [mul_max, ← exp_add, ← exp_add]
    apply max_lt <;> rw [exp_lt_exp] <;> push_cast <;> omega
  rw [v.map_add_eq_of_lt_left (by rw [hA]; exact hB), hA, exp_le_exp] at hDf
  have hT1 : T + ((k + 1 : ℕ) : ℤ) - 1 < (v (D π)).log := lt_of_le_of_lt (by omega) hlt
  push_cast at hT1
  omega

theorem theta_of_element [v.IsTrivialOn K] (π : L) (hπ : v π = exp (-1)) (s : ℤ)
    (hs : 0 ≤ s) (C : ℤ) (hcont : CrudeBound v D C) (hsep : ResiduallySeparable v D (exp s))
    (f : L) (n : ℕ) (hn : (n : K) ≠ 0) (hf : v f = exp (-(n : ℤ))) (T : ℤ)
    (hDf : v (D f) ≤ exp T) :
    ∀ g : L, v (D g) ≤ exp (max s (T + n)) * v g := by
  have h1 := pi_bound_general v D π hπ s T (integral_bound v D π hπ s hs C hcont hsep)
    f n hn hf hDf
  exact derivation_order v D π hπ s (max s (T + n)) hs (le_max_left _ _) h1 C hcont hsep

theorem infinity_theta [v.IsTrivialOn K] (π : L) (hπ : v π = exp (-1)) (s : ℤ)
    (hs : 0 ≤ s) (C : ℤ) (hcont : CrudeBound v D C) (hsep : ResiduallySeparable v D (exp s))
    (c : L) (P : ℕ) (hP : (P : K) ≠ 0) (hc : v c = exp (P : ℤ)) (Q : ℤ)
    (hQ : v (D c) ≤ exp Q) :
    ∀ g : L, v (D g) ≤ exp (max s (max 0 (Q - 2 * P) + P)) * v g := by
  have hc0 : c ≠ 0 := by intro h; rw [h, v.map_zero] at hc; exact exp_ne_zero hc.symm
  have hu : v c⁻¹ = exp (-(P : ℤ)) := by rw [map_inv₀, hc, exp_neg]
  have hDu : v (D c⁻¹) ≤ exp (max 0 (Q - 2 * P)) := by
    rw [Derivation.leibniz_inv, smul_eq_mul, v.map_mul, v.map_neg, v.map_pow, hu]
    calc exp (-(P : ℤ)) ^ 2 * v (D c) ≤ exp (-(P : ℤ)) ^ 2 * exp Q := mul_le_mul_right hQ _
      _ ≤ exp (max 0 (Q - 2 * P)) := by
        rw [sq, ← exp_add, ← exp_add, exp_le_exp]; omega
  exact theta_of_element v D π hπ s hs C hcont hsep c⁻¹ P hP hu _ hDu

end Core

section Bridges

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (v : Valuation L ℤᵐ⁰) (D : Derivation K L L)

theorem continuity_of_localization (R : Subring L) (C : ℤ)
    (hR : ∀ r ∈ R, Tame v D (exp C) r)
    (hloc : ∀ z : L, v z ≤ 1 → ∃ r ∈ R, ∃ u ∈ R, v u = 1 ∧ z = r / u) :
    CrudeBound v D C := by
  intro z hz
  obtain ⟨r, hr, u, hu, hu1, rfl⟩ := hloc z hz
  rw [Derivation.leibniz_div, smul_eq_mul, v.map_mul, v.map_pow, map_inv₀, hu1, inv_one,
    one_pow, one_mul]
  simp only [smul_eq_mul]
  refine (v.map_sub _ _).trans (max_le ?_ ?_) <;> rw [v.map_mul]
  · rw [hu1, one_mul]; exact (hR r hr).2
  · exact (mul_le_mul_left (hR r hr).1 _).trans (by rw [one_mul]; exact (hR u hu).2)

theorem tame_inv (Λ : ℤᵐ⁰) (u : L) (hu : Tame v D Λ u) (hu1 : v u = 1) :
    Tame v D Λ u⁻¹ := by
  refine ⟨by rw [map_inv₀, hu1, inv_one], ?_⟩
  rw [Derivation.leibniz_inv, smul_eq_mul, v.map_mul, v.map_neg, v.map_pow, map_inv₀, hu1,
    inv_one, one_pow, one_mul]
  exact hu.2

noncomputable def residue (z : L) : IsLocalRing.ResidueField v.valuationSubring :=
  open Classical in
  if h : v z ≤ 1 then IsLocalRing.residue v.valuationSubring ⟨z, h⟩ else 0

theorem residue_of_le (z : L) (hz : v z ≤ 1) :
    residue v z = IsLocalRing.residue v.valuationSubring ⟨z, hz⟩ := by
  simp [residue, hz]

theorem residue_eq_zero_iff_lt_one (z : L) (hz : v z ≤ 1) : residue v z = 0 ↔ v z < 1 := by
  rw [residue_of_le v z hz, IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff]
  exact (Valuation.isEquiv_iff_val_lt_one.1 v.isEquiv_valuation_valuationSubring).symm

def tameIn (Λ : ℤᵐ⁰) : Subring v.valuationSubring :=
  (tameSubring v D Λ).comap v.valuationSubring.subtype

noncomputable def tameResidue (Λ : ℤᵐ⁰) :
    tameIn v D Λ →+* IsLocalRing.ResidueField v.valuationSubring :=
  (IsLocalRing.residue v.valuationSubring).comp (tameIn v D Λ).subtype

theorem tameResidue_apply (Λ : ℤᵐ⁰) (a : tameIn v D Λ) :
    tameResidue v D Λ a = residue v ((a : v.valuationSubring) : L) := by
  rw [residue_of_le v _ (a : v.valuationSubring).2]; rfl

theorem closure_residue_subset_range (Λ : ℤᵐ⁰) (S : Set L) (hS : ∀ z ∈ S, Tame v D Λ z) :
    (Subfield.closure (residue v '' S) : Set (IsLocalRing.ResidueField v.valuationSubring)) ⊆
      Set.range (tameResidue v D Λ) := by
  have hsub : Subring.closure (residue v '' S) ≤ (tameResidue v D Λ).range := by
    refine Subring.closure_le.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨⟨z, (hS z hz).1⟩, hS z hz⟩, by rw [tameResidue_apply]⟩
  intro c hc
  obtain ⟨y, hy, w, hw, rfl⟩ := Subfield.mem_closure_iff.1 hc
  obtain ⟨y', rfl⟩ := hsub hy
  obtain ⟨w', rfl⟩ := hsub hw
  by_cases hw0 : tameResidue v D Λ w' = 0
  · exact ⟨0, by rw [hw0, div_zero, map_zero]⟩
  set wL : L := ((w' : v.valuationSubring) : L)
  have hwt : Tame v D Λ wL := w'.2
  have hw1 : v wL = 1 := by
    rw [tameResidue_apply] at hw0
    exact le_antisymm hwt.1 (not_lt.1 fun h => hw0 ((residue_eq_zero_iff_lt_one v wL hwt.1).2 h))
  have hwi : Tame v D Λ wL⁻¹ := tame_inv v D Λ wL hwt hw1
  let winv : tameIn v D Λ := ⟨⟨wL⁻¹, hwi.1⟩, hwi⟩
  have hprod : tameResidue v D Λ w' * tameResidue v D Λ winv = 1 := by
    rw [← map_mul, ← map_one (tameResidue v D Λ)]
    congr 1
    apply Subtype.ext; apply Subtype.ext
    change wL * wL⁻¹ = 1
    exact mul_inv_cancel₀ (by intro h; rw [h, v.map_zero] at hw1; exact zero_ne_one hw1)
  refine ⟨y' * winv, ?_⟩
  rw [map_mul, eq_inv_of_mul_eq_one_right hprod, div_eq_mul_inv]

theorem residuallySeparable_of_residue (Λ : ℤᵐ⁰) (S : Set L) (hS : ∀ z ∈ S, Tame v D Λ z)
    (hres : ∀ x : IsLocalRing.ResidueField v.valuationSubring,
      ∃ p : (IsLocalRing.ResidueField v.valuationSubring)[X],
        (∀ j, p.coeff j ∈ Subfield.closure (residue v '' S)) ∧
        p.eval x = 0 ∧ p.derivative.eval x ≠ 0) :
    ResiduallySeparable v D Λ := by
  intro z hz
  set O := v.valuationSubring
  let z' : O := ⟨z, hz⟩
  obtain ⟨p, hpc, hp0, hp1⟩ := hres (IsLocalRing.residue O z')
  have hlift : p ∈ Polynomial.lifts (tameResidue v D Λ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact closure_residue_subset_range v D Λ S hS (hpc n)
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts p).1 hlift
  set qO : O[X] := q.map (tameIn v D Λ).subtype
  have hqO : qO.map (IsLocalRing.residue O) = p := by
    rw [Polynomial.map_map]; exact hq
  refine ⟨qO.map O.subtype, fun j => ?_, ?_, ?_⟩
  · rw [Polynomial.coeff_map, Polynomial.coeff_map]
    exact (q.coeff j).2
  · have he : (qO.map O.subtype).eval z = ((qO.eval z' : O) : L) := by
      rw [Polynomial.eval_map O.subtype, show z = O.subtype z' from rfl,
        Polynomial.eval₂_at_apply]; rfl
    have hr : residue v ((qO.eval z' : O) : L) = 0 := by
      rw [residue_of_le v _ (qO.eval z').2, ← hp0, ← hqO,
        Polynomial.eval_map (IsLocalRing.residue O), Polynomial.eval₂_at_apply]
    rw [he]
    exact (residue_eq_zero_iff_lt_one v _ (qO.eval z').2).1 hr
  · have he : (qO.map O.subtype).derivative.eval z = ((qO.derivative.eval z' : O) : L) := by
      rw [Polynomial.derivative_map, Polynomial.eval_map O.subtype,
        show z = O.subtype z' from rfl, Polynomial.eval₂_at_apply]; rfl
    have hr : residue v ((qO.derivative.eval z' : O) : L) ≠ 0 := by
      rw [residue_of_le v _ (qO.derivative.eval z').2]
      intro h
      apply hp1
      rw [← hqO, Polynomial.derivative_map, Polynomial.eval_map (IsLocalRing.residue O),
        Polynomial.eval₂_at_apply]
      exact h
    rw [he]
    exact le_antisymm (qO.derivative.eval z').2
      (not_lt.1 fun h => hr ((residue_eq_zero_iff_lt_one v _ (qO.derivative.eval z').2).2 h))

theorem residuallySeparable_of_isSeparable (Λ : ℤᵐ⁰) (S : Set L) (hS : ∀ z ∈ S, Tame v D Λ z)
    [Algebra.IsSeparable (Subfield.closure (residue v '' S))
      (IsLocalRing.ResidueField v.valuationSubring)] :
    ResiduallySeparable v D Λ := by
  refine residuallySeparable_of_residue v D Λ S hS fun x => ?_
  set F := Subfield.closure (residue v '' S)
  have hsx : IsSeparable F x := Algebra.IsSeparable.isSeparable F x
  refine ⟨(minpoly F x).map (algebraMap F _), fun j => ?_, ?_, ?_⟩
  · rw [Polynomial.coeff_map]; exact ((minpoly F x).coeff j).2
  · rw [Polynomial.eval_map_algebraMap]; exact minpoly.aeval F x
  · rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap]
    exact Polynomial.Separable.aeval_derivative_ne_zero hsx (minpoly.aeval F x)

end Bridges

end ProximityPrize.SubmissionLower.HFree6812
