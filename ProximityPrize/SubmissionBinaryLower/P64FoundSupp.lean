import ProximityPrize.SubmissionBinaryLower.P64Algebra

/-!
# Shared foundations: trivariates supported on a finite exponent set

Trivariates are `Polynomial (Polynomial (Polynomial F))` (outer `V`, middle `U`, inner `Z`, the
coordinates of `P64LineOrder.lineShift`). Exponent triples are `(a, b, l)` for `U^a V^b Z^l`.

* `c3 f a b l`, `mono3 a b l`, `coeff_mono3`.
* `supp T`: the `F`-subspace of trivariates supported on `T`; `finrank_supp`: its dimension is
  `T.card`. `comb3 T` / `extr3 T` are the coefficient maps, `comb3_extr3` and `mem_supp_iff_eq`.
* `WtLE α β γ k f`: every monomial of `f` has `α a + β b + γ l ≤ k`; `WtLE.mul` adds the bounds
  (any weights: `V`-degree, `(V, Z)`-degree, twisted weights).
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64Found

open Polynomial Module

section Coeff

variable {F : Type*} [CommSemiring F]

/-- Coefficient of `U^a V^b Z^l`. -/
noncomputable def c3 (f : Polynomial (Polynomial (Polynomial F))) (a b l : ℕ) : F :=
  ((f.coeff b).coeff a).coeff l

/-- The monomial `U^a V^b Z^l`. -/
noncomputable def mono3 (a b l : ℕ) : Polynomial (Polynomial (Polynomial F)) :=
  monomial b (monomial a (monomial l 1))

lemma c3_mono3 (a b l a' b' l' : ℕ) :
    c3 (mono3 (F := F) a b l) a' b' l' = if a = a' ∧ b = b' ∧ l = l' then 1 else 0 := by
  unfold c3 mono3
  rw [coeff_monomial]
  by_cases hb : b = b'
  · rw [if_pos hb, coeff_monomial]
    by_cases ha : a = a'
    · rw [if_pos ha, coeff_monomial]
      by_cases hl : l = l'
      · simp [ha, hb, hl]
      · simp [hl]
    · simp [ha]
  · simp [hb]

lemma c3_add (f g : Polynomial (Polynomial (Polynomial F))) (a b l : ℕ) :
    c3 (f + g) a b l = c3 f a b l + c3 g a b l := by simp [c3]

lemma c3_zero (a b l : ℕ) : c3 (0 : Polynomial (Polynomial (Polynomial F))) a b l = 0 := by
  simp [c3]

lemma c3_smul (c : F) (f : Polynomial (Polynomial (Polynomial F))) (a b l : ℕ) :
    c3 (c • f) a b l = c * c3 f a b l := by simp [c3, coeff_smul]

lemma c3_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial (Polynomial (Polynomial F)))
    (a b l : ℕ) : c3 (∑ i ∈ s, f i) a b l = ∑ i ∈ s, c3 (f i) a b l := by
  simp [c3, finsetSum_coeff]

lemma ext_c3 {f g : Polynomial (Polynomial (Polynomial F))} (h : ∀ a b l, c3 f a b l = c3 g a b l) :
    f = g := by
  ext b a l
  exact h a b l

lemma c3_mul (f g : Polynomial (Polynomial (Polynomial F))) (a b l : ℕ) :
    c3 (f * g) a b l = ∑ bb ∈ Finset.HasAntidiagonal.antidiagonal b,
      ∑ aa ∈ Finset.HasAntidiagonal.antidiagonal a, ∑ ll ∈ Finset.HasAntidiagonal.antidiagonal l, c3 f aa.1 bb.1 ll.1 * c3 g aa.2 bb.2 ll.2 := by
  simp only [c3, coeff_mul, finsetSum_coeff]

end Coeff

section Weight

variable {F : Type*} [CommSemiring F]

/-- Every monomial `U^a V^b Z^l` of `f` has weight `α a + β b + γ l ≤ k`. -/
def WtLE (α β γ k : ℕ) (f : Polynomial (Polynomial (Polynomial F))) : Prop :=
  ∀ a b l, c3 f a b l ≠ 0 → α * a + β * b + γ * l ≤ k

theorem WtLE.mul {α β γ k k' : ℕ} {f g : Polynomial (Polynomial (Polynomial F))}
    (hf : WtLE α β γ k f) (hg : WtLE α β γ k' g) : WtLE α β γ (k + k') (f * g) := by
  intro a b l hne
  by_contra hlt
  apply hne
  rw [c3_mul]
  refine Finset.sum_eq_zero fun bb hbb => Finset.sum_eq_zero fun aa haa =>
    Finset.sum_eq_zero fun ll hll => ?_
  simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hbb haa hll
  by_cases h1 : c3 f aa.1 bb.1 ll.1 = 0
  · rw [h1, zero_mul]
  by_cases h2 : c3 g aa.2 bb.2 ll.2 = 0
  · rw [h2, mul_zero]
  exfalso
  have e1 := hf _ _ _ h1
  have e2 := hg _ _ _ h2
  apply hlt
  rw [← hbb, ← haa, ← hll]
  nlinarith

lemma WtLE.mono {α β γ k k' : ℕ} {f : Polynomial (Polynomial (Polynomial F))}
    (hf : WtLE α β γ k f) (hk : k ≤ k') : WtLE α β γ k' f :=
  fun a b l h => (hf a b l h).trans hk

end Weight

section Supp

variable {F : Type*} [Field F]

/-- Trivariates supported on `T`. -/
def supp (T : Finset (ℕ × ℕ × ℕ)) : Submodule F (Polynomial (Polynomial (Polynomial F))) where
  carrier := {f | ∀ a b l, (a, b, l) ∉ T → c3 f a b l = 0}
  add_mem' hf hg a b l h := by rw [c3_add, hf a b l h, hg a b l h, add_zero]
  zero_mem' a b l _ := c3_zero a b l
  smul_mem' c f hf a b l h := by rw [c3_smul, hf a b l h, mul_zero]

lemma mem_supp {T : Finset (ℕ × ℕ × ℕ)} {f : Polynomial (Polynomial (Polynomial F))} :
    f ∈ supp T ↔ ∀ a b l, (a, b, l) ∉ T → c3 f a b l = 0 := Iff.rfl

lemma supp_mono {T T' : Finset (ℕ × ℕ × ℕ)} (h : T ⊆ T') : supp (F := F) T ≤ supp T' :=
  fun _ hf a b l hn => hf a b l (fun hm => hn (h hm))

/-- Combination of monomials indexed by `T`. -/
noncomputable def comb3 (T : Finset (ℕ × ℕ × ℕ)) :
    (T → F) →ₗ[F] Polynomial (Polynomial (Polynomial F)) :=
  Fintype.linearCombination F (fun q : T => mono3 (F := F) q.1.1 q.1.2.1 q.1.2.2)

/-- Coefficient extraction on `T`. -/
noncomputable def extr3 (T : Finset (ℕ × ℕ × ℕ)) :
    Polynomial (Polynomial (Polynomial F)) →ₗ[F] (T → F) where
  toFun f q := c3 f q.1.1 q.1.2.1 q.1.2.2
  map_add' f g := by ext q; simp [c3_add]
  map_smul' c f := by ext q; simp [c3_smul]

lemma c3_comb3 (T : Finset (ℕ × ℕ × ℕ)) (c : T → F) (a b l : ℕ) :
    c3 (comb3 T c) a b l = if h : (a, b, l) ∈ T then c ⟨(a, b, l), h⟩ else 0 := by
  rw [comb3, Fintype.linearCombination_apply, c3_sum]
  simp only [c3_smul, c3_mono3]
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨(a, b, l), h⟩]
    · simp
    · intro q hq
      have : ¬(q.1.1 = a ∧ q.1.2.1 = b ∧ q.1.2.2 = l) := by
        rintro ⟨h1, h2, h3⟩
        apply hq
        ext <;> simp [h1, h2, h3]
      simp [this]
  · refine Finset.sum_eq_zero fun q _ => ?_
    have : ¬(q.1.1 = a ∧ q.1.2.1 = b ∧ q.1.2.2 = l) := by
      rintro ⟨h1, h2, h3⟩
      apply h
      have : q.1 = (a, b, l) := by ext <;> simp [h1, h2, h3]
      exact this ▸ q.2
    simp [this]

lemma comb3_mem_supp (T : Finset (ℕ × ℕ × ℕ)) (c : T → F) : comb3 T c ∈ supp T := by
  intro a b l h
  rw [c3_comb3, dif_neg h]

lemma comb3_extr3 {T : Finset (ℕ × ℕ × ℕ)} {f : Polynomial (Polynomial (Polynomial F))}
    (hf : f ∈ supp T) : comb3 T (extr3 T f) = f := by
  refine ext_c3 fun a b l => ?_
  rw [c3_comb3]
  split_ifs with h
  · rfl
  · exact (hf a b l h).symm

lemma extr3_comb3 (T : Finset (ℕ × ℕ × ℕ)) (c : T → F) : extr3 T (comb3 T c) = c := by
  ext q
  change c3 (comb3 T c) q.1.1 q.1.2.1 q.1.2.2 = c q
  rw [c3_comb3, dif_pos q.2]

lemma comb3_injective (T : Finset (ℕ × ℕ × ℕ)) : Function.Injective (comb3 (F := F) T) :=
  Function.LeftInverse.injective (extr3_comb3 T)

lemma range_comb3 (T : Finset (ℕ × ℕ × ℕ)) : LinearMap.range (comb3 (F := F) T) = supp T := by
  ext f
  constructor
  · rintro ⟨c, rfl⟩
    exact comb3_mem_supp T c
  · intro hf
    exact ⟨_, comb3_extr3 hf⟩

theorem finrank_supp (T : Finset (ℕ × ℕ × ℕ)) : finrank F (supp (F := F) T) = T.card := by
  rw [← range_comb3, LinearMap.finrank_range_of_inj (comb3_injective T),
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

instance (T : Finset (ℕ × ℕ × ℕ)) : Module.Finite F (supp (F := F) T) := by
  rw [← range_comb3]
  infer_instance

end Supp

end P64Found
end ProximityPrize.SubmissionBinaryLower
