import ProximityPrize.SubmissionLower.Rect51PoleWindowSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1500000

namespace Rect51PoleWindow
noncomputable section

open Polynomial
open K1 (I)
open K1_14 (L Shape shapeSum)
open K1_14_1
open scoped BigOperators Polynomial
open private SeedSquare exponentSquare exists_exponentSquare
  from ProximityPrize.SubmissionLower.Rect51PoleWindowSource
open private K1_14_1_6.Low K1_14_1_6.Low.mk K1_14_1_6.cut
  K1_14_1_6.localGen K1_14_1_6.high_gen K1_14_1_6.sx
  K1_14_1_6.sy K1_14_1_6.sv K1_14_1_6.seedC
  K1_14_1_6.shiftedY K1_14_1_6.mul_add_pow_mem K1_14_1_6.mul_shift_pow_mem
  K1_14_1_6.collect_adapted K1_14_1_6.move_v K1_14_1_6.mem_of_monomials
  K1_14_1_6.product_eq_monomial K1_14_1_6.seed_scalar K1_14_1_6.physical_x
  K1_14_1_6.physical_y K1_14_1_6.physical_v K1_14_1_6.physical_seed
  from ProximityPrize.SubmissionLower.Fast065

private abbrev GenIdx (s : Shape) (U : ℕ) :=
  (Σ q : Fin (s.B+1), Σ k : Fin (min q.val s.J+1),
    Fin (s.m + min q.val s.J - (q.val + 2*k.val))) × SeedSquare U

private theorem gen_card (s : Shape) (U : ℕ) :
    Fintype.card (GenIdx s U) =
      shapeSum s (fun q k => s.m + min q s.J - (q + 2*k)) * (U+1)^2 := by
  unfold GenIdx SeedSquare
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [← pow_two, shapeSum]
  congr 1
  simp only [Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range
    (fun q : ℕ => ∑ k : Fin (min q s.J+1), (s.m + min q s.J - (q + 2*k.val)))]
  refine Finset.sum_congr rfl ?_
  intro q _
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ => s.m + min q s.J - (q + 2*k)) (min q s.J+1)

private def generators (s : Shape) (U : ℕ) (i : GenIdx s U) : K1_14_1_6.Low s.m → L :=
  K1_14_1_6.cut s (K1_14_1_6.localGen i.1.1.val (min i.1.1.val s.J) i.1.2.1.val i.1.2.2.val (exponentSquare i.2))

private def localSpan (s : Shape) (U : ℕ) : Submodule L (K1_14_1_6.Low s.m → L) :=
  Submodule.span L (Set.range (generators s U))

private abbrev preimage (s : Shape) (U : ℕ) : Submodule L Source := (localSpan s U).comap (K1_14_1_6.cut s)

private theorem gen_mem (s : Shape) (U : ℕ) (q k a : ℕ) (e : Fin 2 →₀ ℕ)
    (hq : q ≤ s.B) (hk : k ≤ min q s.J) (he : ∀ t : Fin 2, e t ≤ U) :
    K1_14_1_6.localGen q (min q s.J) k a e ∈ preimage s U := by
  change K1_14_1_6.cut s _ ∈ localSpan s U
  have hd : min q s.J ≤ q := min_le_left _ _
  by_cases ha : a < s.m + min q s.J - (q+2*k)
  · obtain ⟨i, rfl⟩ := exists_exponentSquare he
    exact Submodule.subset_span
      ⟨(⟨⟨q, Nat.lt_succ_of_le hq⟩, ⟨⟨k, Nat.lt_succ_of_le hk⟩, ⟨a, ha⟩⟩⟩, i), rfl⟩
  · rw [LinearMap.mem_ker.mp (K1_14_1_6.high_gen s q (min q s.J) k a e (by omega))]
    exact (localSpan s U).zero_mem
private theorem shifted_mono_mem (s : Shape) (U : ℕ) (a b j : ℕ) (e : Fin 2 →₀ ℕ)
    (hq : b+j ≤ s.B) (hj : j ≤ s.J) (he : ∀ t : Fin 2, e t ≤ U) :
    K1_14_1_6.seedC (MvPolynomial.monomial e 1) * K1_14_1_6.sx^a * K1_14_1_6.shiftedY^b * K1_14_1_6.sv^j ∈ preimage s U := by
  let q := b+j
  let d := min q s.J
  have hd : d ≤ q := min_le_left _ _
  have hjd : j ≤ d := le_min (Nat.le_add_left _ _) hj
  let p := K1_14_1_6.seedC (MvPolynomial.monomial e 1) * K1_14_1_6.sx^a * K1_14_1_6.sv^j * K1_14_1_6.shiftedY^(q-d)
  have hpow : K1_14_1_6.shiftedY^b = K1_14_1_6.shiftedY^(q-d) * K1_14_1_6.shiftedY^(d-j) := by
    rw [← pow_add, show q-d+(d-j) = b by dsimp only [q] at *; omega]
  have hexpand : p * (K1_14_1_6.sy + K1_14_1_6.sx*K1_14_1_6.sv)^(d-j) ∈ preimage s U := by
    apply K1_14_1_6.mul_add_pow_mem
    intro k hk
    have hV : d-k = j+(d-j-k) := by omega
    have hgen := gen_mem s U q k (a+(d-j-k)) e hq (by omega) he
    change K1_14_1_6.localGen q d k (a+(d-j-k)) e ∈ _ at hgen
    rw [K1_14_1_6.localGen, hV] at hgen
    dsimp only [p]
    rw [K1_14_1_6.collect_adapted]
    exact hgen
  dsimp only [p] at hexpand
  change (K1_14_1_6.seedC (MvPolynomial.monomial e 1) * K1_14_1_6.sx^a * K1_14_1_6.sv^j * K1_14_1_6.shiftedY^(q-d)) *
    K1_14_1_6.shiftedY^(d-j) ∈ preimage s U at hexpand
  rw [K1_14_1_6.move_v (K1_14_1_6.seedC (MvPolynomial.monomial e 1) * K1_14_1_6.sx^a), mul_assoc
    (K1_14_1_6.seedC (MvPolynomial.monomial e 1) * K1_14_1_6.sx^a), ← hpow] at hexpand
  exact hexpand
private theorem translated_mono_mem (s : Shape) (U : ℕ) (x r : L) (a b j : ℕ) (e : Fin 2 →₀ ℕ)
    (hq : b+j ≤ s.B) (hj : j ≤ s.J) (he : ∀ t : Fin 2, e t ≤ U) :
    K1_14_1_6.seedC (MvPolynomial.monomial e 1) * (K1_14_1_6.sx + algebraMap L Source x)^a *
      (K1_14_1_6.shiftedY + algebraMap L Source r)^b * K1_14_1_6.sv^j ∈ preimage s U := by
  let p := K1_14_1_6.seedC (MvPolynomial.monomial e 1) * K1_14_1_6.sv^j
  have h : (p * (K1_14_1_6.shiftedY + algebraMap L Source r)^b) *
      (K1_14_1_6.sx + algebraMap L Source x)^a ∈ preimage s U := by
    apply K1_14_1_6.mul_shift_pow_mem
    intro t _
    have h' : (p * K1_14_1_6.sx^t) * (K1_14_1_6.shiftedY + algebraMap L Source r)^b ∈ preimage s U := by
      apply K1_14_1_6.mul_shift_pow_mem
      intro k hk
      dsimp only [p]
      rw [K1_14_1_6.move_v]
      exact shifted_mono_mem s U t k j e (by omega) hj he
    rw [mul_right_comm]
    exact h'
  rw [mul_right_comm p] at h
  dsimp only [p] at h
  rw [K1_14_1_6.move_v] at h
  exact h
private theorem atPhysical_mem (h : ℕ) (s : Shape) (U : ℕ) (W : ℕ) (x r : L)
    (P : ↥(ambient h s W ⊓ square U : Submodule L Source)) :
    K1_14_1_6.cut s (atPhysical x r P.val) ∈ localSpan s U := by
  change P.val ∈ (preimage s U).comap (atPhysical x r).toLinearMap
  apply K1_14_1_6.mem_of_monomials
  intro j b a e hne
  have hel : trueEligible h s W j b a e := by
    by_contra hn
    exact hne (P.property.1 j b a e hn)
  obtain ⟨hq, hj, _, _⟩ := hel
  have he := mem_square_iff.mp P.property.2 j b a e hne
  change atPhysical x r _ ∈ preimage s U
  rw [← K1_14_1_6.product_eq_monomial, K1_14_1_6.seed_scalar, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, map_smul]
  apply (preimage s U).smul_mem
  simp only [map_mul, map_pow, K1_14_1_6.physical_x, K1_14_1_6.physical_y, K1_14_1_6.physical_v, K1_14_1_6.physical_seed]
  exact translated_mono_mem s U x r a b j e hq hj he
private def nodeMap (h : ℕ) (word : I → L) (s : Shape) (U : ℕ) (W : ℕ) (i : I) :
    (ambient h s W ⊓ square U : Submodule L Source) →ₗ[L] localSpan s U :=
  LinearMap.codRestrict (localSpan s U)
    (((K1_14_1_6.cut s).comp (atPhysical (nodeL i) (word i)).toLinearMap).domRestrict (ambient h s W ⊓ square U))
    (atPhysical_mem h s U W (nodeL i) (word i))
private theorem localSpan_finrank (s : Shape) (U : ℕ) :
    Module.finrank L (localSpan s U) ≤
      shapeSum s (fun q k => s.m + min q s.J - (q + 2*k)) * (U+1)^2 := by
  rw [← gen_card]
  exact finrank_range_le_card (R := L) (generators s U)
/-- Total node debit with separate seed-degree caps. -/
def rectPhysicalDebit (s : Shape) (U : ℕ) : ℕ :=
  (U+1)^2 * 262144 * shapeSum s (fun q k => s.m + min q s.J - (q + 2*k))

theorem rectPhysicalBound (h : ℕ) (word : I → L) (s : Shape) (W U : ℕ) :
    Module.finrank L (ambient h s W ⊓ square U : Submodule L Source) ≤
      rectPhysicalDebit s U + Module.finrank L (contacted h word s W ⊓ square U : Submodule L Source) := by
  classical
  by_cases hzero : Module.finrank L (ambient h s W ⊓ square U : Submodule L Source) = 0
  · simp [hzero]
  let A : Submodule L Source := ambient h s W ⊓ square U
  let T : Submodule L Source := contacted h word s W ⊓ square U
  have : Module.Finite L A :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hzero)
  have : Module.Finite L (localSpan s U) :=
    Module.Finite.span_of_finite L (Set.finite_range (generators s U))
  let f : A →ₗ[L] (I → localSpan s U) :=
    LinearMap.pi (nodeMap h word s U W)
  let g : LinearMap.ker f →ₗ[L] T :=
    LinearMap.codRestrict T
      (A.subtype.comp (LinearMap.ker f).subtype) (by
        intro P
        refine ⟨⟨P.val.property.1, ?_⟩, P.val.property.2⟩
        intro i a b j e hab
        have hz := LinearMap.mem_ker.mp P.property
        exact congrArg (fun z : I → localSpan s U => (z i).val (K1_14_1_6.Low.mk j b a e hab)) hz)
  have hg : Function.Injective g := by
    intro P Q hPQ
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun R : T => R.val) hPQ
  have hle : T ≤ A := inf_le_inf inf_le_left le_rfl
  have : Module.Finite L T :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hker := LinearMap.finrank_le_finrank_of_injective hg
  have hnull := f.finrank_range_add_finrank_ker
  have htarget : Module.finrank L (I → localSpan s U) ≤ rectPhysicalDebit s U := by
    rw [Module.finrank_pi_fintype]
    calc
      (∑ _ : I, Module.finrank L (localSpan s U)) ≤
          ∑ _ : I, (shapeSum s (fun q k => s.m + min q s.J - (q + 2*k))) * (U+1)^2 :=
        Finset.sum_le_sum (fun _ _ => localSpan_finrank s U)
      _ = rectPhysicalDebit s U := by
        rw [Finset.sum_const, Finset.card_univ, ProximityPrize.Benchmark.IRSProfile.card_index,
          smul_eq_mul, rectPhysicalDebit]
        ac_rfl
  have hrange := (LinearMap.range f).finrank_le.trans htarget
  change Module.finrank L A ≤ rectPhysicalDebit s U + Module.finrank L T
  omega
#print axioms rectPhysicalBound
end
end Rect51PoleWindow
