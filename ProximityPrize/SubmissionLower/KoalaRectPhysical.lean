import ProximityPrize.SubmissionLower.KoalaRectSource
import ProximityPrize.SubmissionLower.KoalaRectCutoff -- serialize candidate build

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 16
set_option autoImplicit false

namespace KoalaRect
noncomputable section
open Polynomial K1_14 K1_14_1 K1_14_1_6
open K1 (I)
open scoped BigOperators
open private Low Low.mk cut localGen high_gen mul_add_pow_mem mul_shift_pow_mem
  collect_adapted move_v shiftedY mem_of_monomials product_eq_monomial seed_scalar
  K1_14_1_6.seedC K1_14_1_6.sx K1_14_1_6.sy K1_14_1_6.sv K1_14_1_6.physical_x
  K1_14_1_6.physical_y K1_14_1_6.physical_v K1_14_1_6.physical_seed from ProximityPrize.SubmissionLower.Fast065

abbrev RectGen (s : Shape) (U : Fin 2 → ℕ) :=
  (Σ q : Fin (s.B+1), Σ k : Fin (min q.val s.J+1),
    Fin (s.m + min q.val s.J - (q.val + 2*k.val))) × AxisIndex U

theorem rectGen_card (s : Shape) (U : Fin 2 → ℕ) :
    Fintype.card (RectGen s U) = shapeSum s (fun q k => s.m + min q s.J - (q + 2*k)) * area U := by
  unfold RectGen
  rw [Fintype.card_prod, axis_card, shapeSum]
  congr 1
  simp only [Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range
    (fun q : ℕ => ∑ k : Fin (min q s.J+1), (s.m + min q s.J - (q + 2*k.val)))]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact Fin.sum_univ_eq_sum_range (fun k => s.m + min q s.J - (q + 2*k)) (min q s.J+1)

def rectGenerators (s : Shape) (U : Fin 2 → ℕ) (i : RectGen s U) : Low s.m → L :=
  cut s (localGen i.1.1.val (min i.1.1.val s.J) i.1.2.1.val i.1.2.2.val (axisExponent i.2))

def rectSpan (s : Shape) (U : Fin 2 → ℕ) : Submodule L (Low s.m → L) :=
  Submodule.span L (Set.range (rectGenerators s U))

abbrev rectPreimage (s : Shape) (U : Fin 2 → ℕ) : Submodule L Source :=
  (rectSpan s U).comap (cut s)

theorem rect_gen_mem (s : Shape) (U : Fin 2 → ℕ) (q k a : ℕ) (e : Fin 2 →₀ ℕ)
    (hq : q ≤ s.B) (hk : k ≤ min q s.J) (he : ∀ z, e z ≤ U z) :
    localGen q (min q s.J) k a e ∈ rectPreimage s U := by
  change cut s _ ∈ rectSpan s U
  have hd : min q s.J ≤ q := min_le_left _ _
  by_cases ha : a < s.m + min q s.J - (q+2*k)
  · obtain ⟨i, rfl⟩ := exists_axisIndex e he
    exact Submodule.subset_span
      ⟨(⟨⟨q, Nat.lt_succ_of_le hq⟩, ⟨⟨k, Nat.lt_succ_of_le hk⟩, ⟨a, ha⟩⟩⟩, i), rfl⟩
  · rw [LinearMap.mem_ker.mp (high_gen s q (min q s.J) k a e (by omega))]
    exact (rectSpan s U).zero_mem

theorem shifted_rect_mem (s : Shape) (U : Fin 2 → ℕ) (a b j : ℕ) (e : Fin 2 →₀ ℕ)
    (hq : b+j ≤ s.B) (hj : j ≤ s.J) (he : ∀ z, e z ≤ U z) :
    K1_14_1_6.seedC (MvPolynomial.monomial e 1) * K1_14_1_6.sx^a * shiftedY^b * K1_14_1_6.sv^j ∈ rectPreimage s U := by
  let q := b+j
  let d := min q s.J
  have hd : d ≤ q := min_le_left _ _
  have hjd : j ≤ d := le_min (Nat.le_add_left _ _) hj
  let p := K1_14_1_6.seedC (MvPolynomial.monomial e 1) * K1_14_1_6.sx^a * K1_14_1_6.sv^j * shiftedY^(q-d)
  have hpow : shiftedY^b = shiftedY^(q-d) * shiftedY^(d-j) := by
    rw [← pow_add, show q-d+(d-j) = b by dsimp only [q] at *; omega]
  have hexpand : p * (K1_14_1_6.sy + K1_14_1_6.sx*K1_14_1_6.sv)^(d-j) ∈ rectPreimage s U := by
    apply mul_add_pow_mem
    intro k hk
    have hV : d-k = j+(d-j-k) := by omega
    have hgen := rect_gen_mem s U q k (a+(d-j-k)) e hq (by omega) he
    change localGen q d k (a+(d-j-k)) e ∈ _ at hgen
    rw [localGen, hV] at hgen
    dsimp only [p]
    rw [collect_adapted]
    exact hgen
  dsimp only [p] at hexpand
  change (K1_14_1_6.seedC (MvPolynomial.monomial e 1) * K1_14_1_6.sx^a * K1_14_1_6.sv^j * shiftedY^(q-d)) *
    shiftedY^(d-j) ∈ rectPreimage s U at hexpand
  rw [move_v (K1_14_1_6.seedC (MvPolynomial.monomial e 1) * K1_14_1_6.sx^a), mul_assoc
    (K1_14_1_6.seedC (MvPolynomial.monomial e 1) * K1_14_1_6.sx^a), ← hpow] at hexpand
  exact hexpand

theorem translated_rect_mem (s : Shape) (U : Fin 2 → ℕ) (x r : L) (a b j : ℕ)
    (e : Fin 2 →₀ ℕ) (hq : b+j ≤ s.B) (hj : j ≤ s.J) (he : ∀ z, e z ≤ U z) :
    K1_14_1_6.seedC (MvPolynomial.monomial e 1) * (K1_14_1_6.sx + algebraMap L Source x)^a *
      (shiftedY + algebraMap L Source r)^b * K1_14_1_6.sv^j ∈ rectPreimage s U := by
  let p := K1_14_1_6.seedC (MvPolynomial.monomial e 1) * K1_14_1_6.sv^j
  have h : (p * (shiftedY + algebraMap L Source r)^b) *
      (K1_14_1_6.sx + algebraMap L Source x)^a ∈ rectPreimage s U := by
    apply mul_shift_pow_mem
    intro t _
    have h' : (p * K1_14_1_6.sx^t) * (shiftedY + algebraMap L Source r)^b ∈ rectPreimage s U := by
      apply mul_shift_pow_mem
      intro k hk
      dsimp only [p]
      rw [move_v]
      exact shifted_rect_mem s U t k j e (by omega) hj he
    rw [mul_right_comm]
    exact h'
  rw [mul_right_comm p] at h
  dsimp only [p] at h
  rw [move_v] at h
  exact h

theorem atPhysical_rect (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) (x r : L)
    (P : rectAmbient h s W U) : cut s (atPhysical x r P.val) ∈ rectSpan s U := by
  change P.val ∈ (rectPreimage s U).comap (atPhysical x r).toLinearMap
  apply mem_of_monomials
  intro j b a e hne
  have hel : trueEligible h s W j b a e := by
    by_contra hn
    exact hne (P.property.1 j b a e hn)
  obtain ⟨hq, hj, _, _⟩ := hel
  have he := P.property.2 j b a e hne
  change atPhysical x r _ ∈ rectPreimage s U
  rw [← product_eq_monomial, seed_scalar, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, map_smul]
  apply (rectPreimage s U).smul_mem
  simp only [map_mul, map_pow, K1_14_1_6.physical_x, K1_14_1_6.physical_y, K1_14_1_6.physical_v, K1_14_1_6.physical_seed]
  exact translated_rect_mem s U x r a b j e hq hj he

theorem rectPhysical_bound (h : ℕ) (word : I → L) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) :
    Module.finrank L (rectAmbient h s W U) ≤
      area U * P1_7_1.nodeRows s + Module.finrank L (rectContacted h word s W U) := by
  classical
  by_cases hzero : Module.finrank L (rectAmbient h s W U) = 0
  · simp [hzero]
  let _ : Module.Finite L (rectAmbient h s W U) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hzero)
  let _ : Module.Finite L (rectSpan s U) := Module.Finite.span_of_finite L (Set.finite_range _)
  let f : rectAmbient h s W U →ₗ[L] (I → rectSpan s U) :=
    LinearMap.pi fun i => LinearMap.codRestrict (rectSpan s U)
      (((cut s).comp (atPhysical (nodeL i) (word i)).toLinearMap).domRestrict (rectAmbient h s W U))
      (atPhysical_rect h s W U (nodeL i) (word i))
  let g : LinearMap.ker f →ₗ[L] rectContacted h word s W U :=
    LinearMap.codRestrict _ ((rectAmbient h s W U).subtype.comp (LinearMap.ker f).subtype) (by
      intro P
      refine ⟨⟨P.val.property.1, ?_⟩, P.val.property.2⟩
      intro i a b j e hab
      have hz := LinearMap.mem_ker.mp P.property
      exact congrArg (fun t : I → rectSpan s U => (t i).val (Low.mk j b a e hab)) hz)
  have hg : Function.Injective g := by
    intro P Q hPQ
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun R : rectContacted h word s W U => R.val) hPQ
  have hle : rectContacted h word s W U ≤ rectAmbient h s W U :=
    fun _ hP => ⟨hP.1.1, hP.2⟩
  let _ : Module.Finite L (rectContacted h word s W U) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hk := LinearMap.finrank_le_finrank_of_injective hg
  have hn := f.finrank_range_add_finrank_ker
  have hspan : Module.finrank L (rectSpan s U) ≤ Fintype.card (RectGen s U) :=
    finrank_range_le_card (R := L) (rectGenerators s U)
  have htarget : Module.finrank L (I → rectSpan s U) ≤ area U * P1_7_1.nodeRows s := by
    rw [Module.finrank_pi_fintype]
    apply (Finset.sum_le_sum (fun (_ : I) _ => hspan)).trans_eq
    rw [rectGen_card, Finset.sum_const, Finset.card_univ, ProximityPrize.Benchmark.IRSProfile.card_index,
      smul_eq_mul, P1_7_1.nodeRows]
    ac_rfl
  have hr := (LinearMap.range f).finrank_le.trans htarget
  omega

end
end KoalaRect
