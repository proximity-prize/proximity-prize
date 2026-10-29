import ProximityPrize.SubmissionBinaryLower.P64C7WS

/-!
# Lemma HS and the basis extraction of Theorem DLT (dlt.md section 2)

Over a field `K`, with `S` of order at least `μ` and `S(0, V) = V^ν R''(V)`, `R''(0) ≠ 0`:

* `finrank_range_tri_ge` (Lemma HS): the monomials `U^a V^b` with `a + b < s` span a subspace of
  `K[U, V] / (U^s, V^s, S)` of dimension at least `|tri s| - |tri (s - μ)|`
  `= s(s+1)/2 - (s-μ)(s-μ+1)/2 = λ_s`. Only superadditivity of the order is used: an element of the
  ideal of total degree `< s` is the truncation of `G·S`, which depends only on `G` below `s - μ`.
* `exists_indep_monomials` (Lemmas WS + HS): a set `Λ` of exponents `(a, b)` with `a < s`,
  `b < min(ν, s)`, `|Λ| ≥ λ_s`, whose monomials are linearly independent modulo the ideal.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C7

open Polynomial P64Found Module

variable {K : Type*} [Field K]

/-- Exponents `(a, b)` with `a + b < k`. -/
def tri (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range k).biUnion (fun n => Finset.HasAntidiagonal.antidiagonal n)

lemma mem_tri {k : ℕ} {p : ℕ × ℕ} : p ∈ tri k ↔ p.1 + p.2 < k := by
  simp [tri]

lemma card_tri (k : ℕ) : (tri k).card = k * (k + 1) / 2 := by
  rw [tri, Finset.card_biUnion]
  · simp only [Finset.Nat.card_antidiagonal]
    have h := Finset.sum_range_succ' (fun i => i) k
    simp only [add_zero] at h
    rw [← h, Finset.sum_range_id, Nat.add_sub_cancel, mul_comm]
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hq
    exact hij (hp.symm.trans hq)

/-- Coefficients of a combination of monomials indexed by a finset. -/
lemma coeff_sum_mono (T : Finset (ℕ × ℕ)) (c : T → K) (a b : ℕ) :
    ((∑ q : T, c q • mono (K := K) q.1.1 q.1.2).coeff b).coeff a =
      if h : (a, b) ∈ T then c ⟨(a, b), h⟩ else 0 := by
  rw [finsetSum_coeff, finsetSum_coeff]
  simp only [coeff_smul, smul_eq_mul, coeff_mono]
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨(a, b), h⟩]
    · simp
    · intro q hq
      have : ¬(q.1.1 = a ∧ q.1.2 = b) := by
        rintro ⟨h1, h2⟩
        apply hq
        ext <;> simp [h1, h2]
      simp [this]
  · refine Finset.sum_eq_zero fun q _ => ?_
    have : ¬(q.1.1 = a ∧ q.1.2 = b) := by
      rintro ⟨h1, h2⟩
      apply h
      have : q.1 = (a, b) := Prod.ext h1 h2
      exact this ▸ q.2
    simp [this]

/-- Combination of monomials indexed by `T`. -/
noncomputable def comb (T : Finset (ℕ × ℕ)) : (T → K) →ₗ[K] Polynomial (Polynomial K) :=
  Fintype.linearCombination K (fun q : T => mono (K := K) q.1.1 q.1.2)

lemma comb_apply (T : Finset (ℕ × ℕ)) (c : T → K) :
    comb T c = ∑ q : T, c q • mono (K := K) q.1.1 q.1.2 := rfl

/-- Coefficient extraction on `T`. -/
noncomputable def extr (T : Finset (ℕ × ℕ)) : Polynomial (Polynomial K) →ₗ[K] (T → K) where
  toFun f q := (f.coeff q.1.2).coeff q.1.1
  map_add' f g := by ext q; simp
  map_smul' c f := by ext q; simp [coeff_smul]

/-- A polynomial supported on `T` is the combination of its coefficients. -/
lemma eq_comb_extr {T : Finset (ℕ × ℕ)} {g : Polynomial (Polynomial K)}
    (hg : ∀ a b, (a, b) ∉ T → (g.coeff b).coeff a = 0) : comb T (extr T g) = g := by
  ext b a
  rw [comb_apply, coeff_sum_mono]
  split_ifs with h
  · rfl
  · exact (hg a b h).symm

section Quot

variable (s μ : ℕ) (S : Polynomial (Polynomial K))

/-- The class map of the monomials of `tri s` to `K[U, V] / (U^s, V^s, S)`. -/
noncomputable def psi : (tri s → K) →ₗ[K] (Polynomial (Polynomial K) ⧸ boxIdeal s S) :=
  (Ideal.Quotient.mkₐ K (boxIdeal s S)).toLinearMap ∘ₗ comb (tri s)

/-- Coefficients below `s` of `S·G`, for `G` supported on `tri (s - μ)`. -/
noncomputable def theta : (tri (s - μ) → K) →ₗ[K] (tri s → K) :=
  extr (tri s) ∘ₗ LinearMap.mulLeft K S ∘ₗ comb (tri (s - μ))

lemma ker_psi_le (hS : OrdAtLeast μ S) : LinearMap.ker (psi s S) ≤ LinearMap.range (theta s μ S) := by
  intro c hc
  rw [LinearMap.mem_ker, psi, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, boxIdeal] at hc
  obtain ⟨A, z, hz, hAz⟩ := Ideal.mem_span_insert.mp hc
  obtain ⟨B, z', hz', hBz⟩ := Ideal.mem_span_insert.mp hz
  obtain ⟨G, hG⟩ := Ideal.mem_span_singleton'.mp hz'
  refine ⟨extr (tri (s - μ)) G, ?_⟩
  ext q
  have hq := mem_tri.mp q.2
  -- the truncation of G agrees with G below s - μ
  have hdiff : OrdAtLeast (s - μ) (G - comb (tri (s - μ)) (extr (tri (s - μ)) G)) := by
    intro a b hab
    rw [coeff_sub, coeff_sub, comb_apply, coeff_sum_mono, dif_pos (mem_tri.mpr hab)]
    simp [extr]
  have h0 := ordAtLeast_mul hdiff hS
  have hA := ordAtLeast_mul (ordAtLeast_zero_left A) (ordAtLeast_U_pow (K := K) s)
  have hB := ordAtLeast_mul (ordAtLeast_zero_left B) (ordAtLeast_V_pow (K := K) s)
  have hc' : c q = ((comb (tri s) c).coeff q.1.2).coeff q.1.1 := by
    rw [comb_apply, coeff_sum_mono, dif_pos (by simpa using q.2)]
  rw [hc', hAz, hBz, ← hG]
  simp only [theta, extr, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.mulLeft_apply]
  have e1 := hA q.1.1 q.1.2 (by omega)
  have e2 := hB q.1.1 q.1.2 (by omega)
  have e3 := h0 q.1.1 q.1.2 (by omega)
  rw [sub_mul, coeff_sub, coeff_sub, sub_eq_zero] at e3
  rw [coeff_add, coeff_add, coeff_add, coeff_add, e1, e2, zero_add, zero_add, e3, mul_comm]
  rfl

/-- Lemma HS: the classes of `tri s` span at least `λ_s` dimensions. -/
theorem finrank_range_psi_ge (hS : OrdAtLeast μ S) :
    (tri s).card - (tri (s - μ)).card ≤ finrank K (LinearMap.range (psi s S)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (psi s S)
  have h2 : finrank K (LinearMap.ker (psi s S)) ≤ (tri (s - μ)).card := by
    calc finrank K (LinearMap.ker (psi s S))
        ≤ finrank K (LinearMap.range (theta s μ S)) := Submodule.finrank_mono (ker_psi_le s μ S hS)
      _ ≤ finrank K (tri (s - μ) → K) := LinearMap.finrank_range_le _
      _ = (tri (s - μ)).card := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h1
  omega

end Quot

/-- Lemmas WS and HS: a set `Λ` of at least `λ_s` exponents `(a, b)` with `a < s`, `b < min(ν, s)`
whose monomials are linearly independent modulo `(U^s, V^s, S)`. -/
theorem exists_indep_monomials (s μ ν : ℕ) (S : Polynomial (Polynomial K)) (R'' : K[X])
    (hS : OrdAtLeast μ S) (hS0 : S.map (constantCoeff (R := K)) = X ^ ν * R'')
    (hu : R''.coeff 0 ≠ 0) :
    ∃ Λ : Finset (ℕ × ℕ), (∀ p ∈ Λ, p.1 < s ∧ p.2 < min ν s) ∧
      (tri s).card - (tri (s - μ)).card ≤ Λ.card ∧
      ∀ c : ℕ × ℕ → K, (∑ p ∈ Λ, c p • mono (K := K) p.1 p.2) ∈ boxIdeal s S →
        ∀ p ∈ Λ, c p = 0 := by
  classical
  set t := min ν s
  set box := Finset.range s ×ˢ Finset.range t
  set Q := Polynomial (Polynomial K) ⧸ boxIdeal s S
  let mk := (Ideal.Quotient.mkₐ K (boxIdeal s S)).toLinearMap
  let v : box → Q := fun q => mk (mono q.1.1 q.1.2)
  -- the box monomials span the quotient (Lemma WS)
  have hspan : LinearMap.range (psi s S) ≤ Submodule.span K (Set.range v) := by
    rintro _ ⟨c, rfl⟩
    obtain ⟨g, hg, hmem⟩ := exists_inBox_sub_mem s ν S R'' hS0 (isUnit_iff_ne_zero.mpr hu)
      (comb (tri s) c)
    have hgc : g = comb box (extr box g) := by
      refine (eq_comb_extr fun a b hab => hg a b ?_).symm
      simp only [box, Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hab
      exact hab
    have : psi s S c = mk g := by
      simp only [psi, mk, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq.mpr hmem
    rw [this, hgc, comb_apply, map_sum]
    exact Submodule.sum_mem _ fun q _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  have : Module.Finite K (Submodule.span K (Set.range v)) :=
    Module.Finite.span_of_finite K (Set.finite_range v)
  have hdim := (finrank_range_psi_ge s μ S hS).trans (Submodule.finrank_mono hspan)
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K v
  letI : Fintype κ := Fintype.ofInjective a ha
  have hcard := finrank_span_eq_card hli
  rw [hsp] at hcard
  have hinj : Function.Injective (fun k => (a k : ℕ × ℕ)) := Subtype.val_injective.comp ha
  refine ⟨Finset.univ.image (fun k => (a k : ℕ × ℕ)), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hp
    have := (a k).2
    simp only [box, Finset.mem_product, Finset.mem_range] at this
    exact this
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← hcard]
    exact hdim
  · intro c hc p hp
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.sum_image (fun x _ y _ h => hinj h)] at hc
    have h0 : ∑ k' : κ, c (a k' : ℕ × ℕ) • (v ∘ a) k' = 0 := by
      have h1 : mk (∑ k' : κ, c (a k' : ℕ × ℕ) • mono (K := K) (a k' : ℕ × ℕ).1 (a k').1.2) = 0 := by
        show Ideal.Quotient.mkₐ K _ _ = 0
        rw [Ideal.Quotient.mkₐ_eq_mk]
        exact (Ideal.Quotient.eq_zero_iff_mem).mpr hc
      rw [map_sum] at h1
      simp only [map_smul] at h1
      exact h1
    exact Fintype.linearIndependent_iff.mp hli _ h0 k

end P64C7
end ProximityPrize.SubmissionBinaryLower
