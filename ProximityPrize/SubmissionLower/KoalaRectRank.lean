import ProximityPrize.SubmissionLower.KoalaRectSource
import ProximityPrize.SubmissionLower.PortHighBase

-- merged module KoalaRectPhysical
section Merged_KoalaRectPhysical
set_option Elab.async false
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

private abbrev RectGen (s : Shape) (U : Fin 2 → ℕ) :=
  (Σ q : Fin (s.B+1), Σ k : Fin (min q.val s.J+1),
    Fin (s.m + min q.val s.J - (q.val + 2*k.val))) × AxisIndex U

private theorem rectGen_card (s : Shape) (U : Fin 2 → ℕ) :
    Fintype.card (RectGen s U) = shapeSum s (fun q k => s.m + min q s.J - (q + 2*k)) * area U := by
  unfold RectGen
  rw [Fintype.card_prod, axis_card, shapeSum]
  congr 1
  simp only [Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range
    (fun q : ℕ => ∑ k : Fin (min q s.J+1), (s.m + min q s.J - (q + 2*k.val)))]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  exact Fin.sum_univ_eq_sum_range (fun k => s.m + min q s.J - (q + 2*k)) (min q s.J+1)

private def rectGenerators (s : Shape) (U : Fin 2 → ℕ) (i : RectGen s U) : Low s.m → L :=
  cut s (localGen i.1.1.val (min i.1.1.val s.J) i.1.2.1.val i.1.2.2.val (axisExponent i.2))

private def rectSpan (s : Shape) (U : Fin 2 → ℕ) : Submodule L (Low s.m → L) :=
  Submodule.span L (Set.range (rectGenerators s U))

private abbrev rectPreimage (s : Shape) (U : Fin 2 → ℕ) : Submodule L Source :=
  (rectSpan s U).comap (cut s)

private theorem rect_gen_mem (s : Shape) (U : Fin 2 → ℕ) (q k a : ℕ) (e : Fin 2 →₀ ℕ)
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

private theorem shifted_rect_mem (s : Shape) (U : Fin 2 → ℕ) (a b j : ℕ) (e : Fin 2 →₀ ℕ)
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

private theorem translated_rect_mem (s : Shape) (U : Fin 2 → ℕ) (x r : L) (a b j : ℕ)
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

private theorem atPhysical_rect (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) (x r : L)
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

#print axioms rectPhysical_bound
end
end KoalaRect
end Merged_KoalaRectPhysical

set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

namespace KoalaRect
noncomputable section
open K1_14 K1_14_1 K1_14_1_8
open K1 (I)
open scoped BigOperators Polynomial
open private Position boundaryMap sourceCoord boundaryDegree sourceCoord_degree jetCoords coords_center
  independent_at_fraction strict_of_ker trueWidth trueWidth_eq_add completeFinite
  from ProximityPrize.SubmissionLower.Fast065
open private zero_of_strict_cutoff from ProximityPrize.SubmissionLower.UpperBranch1

private def rectInclusion {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : rectComplete Crt word s W U →ₗ[L] complete Crt word s W :=
  Submodule.inclusion inf_le_left

private instance rectCompleteFinite {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : Module.Finite L (rectComplete Crt word s W U) := by
  let _ : Module.Finite L (complete Crt word s W) := completeFinite Crt word s W
  exact Module.Finite.of_injective (rectInclusion Crt word s W U)
    (Submodule.inclusion_injective inf_le_left)

private def rectBoundary {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : rectComplete Crt word s W U →ₗ[L] (Position → L) :=
  (boundaryMap Crt word s W).comp (rectInclusion Crt word s W U)

private theorem rectBoundary_rank {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) :
    Module.finrank L (rectBoundary Crt word s W U).range ≤
      Module.finrank FX (rectEvaluated Crt word s W U) := by
  classical
  let R := rectEvaluated Crt word s W U
  have : Module.Finite FX R := by
    change Module.Finite FX (Submodule.span FX ((rectComplete Crt word s W U).map centerEval.toLinearMap : Set Jet))
    exact Module.Finite.of_fg ((Module.Finite.iff_fg.mp inferInstance).span (A := FX))
  let F := rectBoundary Crt word s W U
  let b := Module.finBasis L F.range
  have hex (k : Fin (Module.finrank L F.range)) :
      ∃ P : rectComplete Crt word s W U, F P = (b k : Position → L) := (b k).property
  choose P hP using hex
  have hli : LinearIndependent L (fun k t =>
      (sourceCoord (P k : Source) t).coeff (boundaryDegree h s W t)) := by
    change LinearIndependent L (F ∘ P)
    have heq : F ∘ P = fun k => ((b k : F.range) : Position → L) := funext hP
    rw [heq]
    exact b.linearIndependent.map' F.range.subtype F.range.ker_subtype
  have heval : LinearIndependent FX (fun k => centerEval (P k : Source)) := by
    apply LinearIndependent.of_comp jetCoords
    have hf : jetCoords ∘ (fun k => centerEval (P k : Source)) =
        fun k t => algebraMap L[X] FX (sourceCoord (P k : Source) t) :=
      funext fun k => funext fun t => coords_center (P k : Source) t
    rw [hf]
    exact independent_at_fraction (fun k => sourceCoord (P k : Source))
      (boundaryDegree h s W) (fun k => sourceCoord_degree (rectInclusion Crt word s W U (P k))) hli
  let u (k : Fin (Module.finrank L F.range)) : R :=
    ⟨centerEval (P k : Source), Submodule.subset_span ⟨_, (P k).property, rfl⟩⟩
  have hu : LinearIndependent FX u := LinearIndependent.of_comp R.subtype heval
  simpa [F, R] using hu.fintype_card_le_finrank

private theorem rectStrict {h : ℕ} {D : PoleData h} {Crt : CRTLift D} {word : I → L}
    {s : Shape} {W : ℕ} {U : Fin 2 → ℕ} (P : (rectBoundary Crt word s W U).ker)
    {j i a : ℕ} {e : Fin 2 →₀ ℕ} (hn : coeffAt (P.1 : Source) j i a e ≠ 0) :
    a + (i+j)*(131071+h) < W+(s.B+s.J)*(2*h)+j := by
  let q : (boundaryMap Crt word s W).ker :=
    ⟨rectInclusion Crt word s W U P.1, LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp P.property)⟩
  exact strict_of_ker q hn

theorem rectTelescope {h : ℕ} (hraw : h ≤ 131070) {D : PoleData h}
    (Crt : CRTLift D) (word : I → L) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) :
    Module.finrank L (rectComplete Crt word s W U) ≤
      ∑ t ∈ Finset.range (W+1), Module.finrank FX (rectEvaluated Crt word s t U) := by
  induction W with
  | zero =>
    let F := rectBoundary Crt word s 0 U
    have hker : F.ker = ⊥ := by
      apply bot_unique
      intro P hP
      rw [Submodule.mem_bot]
      apply Subtype.ext
      apply zero_of_strict_cutoff hraw Crt s (P : Source) P.property.1.2
      intro j i a e hn
      simpa only [zero_add] using rectStrict (⟨P, hP⟩ : F.ker) hn
    have hr := F.finrank_range_add_finrank_ker
    rw [hker, finrank_bot, add_zero] at hr
    simpa [← hr, F] using rectBoundary_rank Crt word s 0 U
  | succ W ih =>
    rw [Finset.sum_range_succ]
    let F := rectBoundary Crt word s (W+1) U
    have hmem (P : F.ker) : (P.1 : Source) ∈ rectComplete Crt word s W U := by
      refine ⟨⟨⟨?_, P.1.property.1.1.2⟩, P.1.property.1.2⟩, P.1.property.2⟩
      intro j i a e hb
      by_contra hn
      have he : trueEligible h s (W+1) j i a e := by
        by_contra hh
        exact hn (P.1.property.1.1.1 j i a e hh)
      have hl := rectStrict P hn
      exact hb ⟨he.1, he.2.1, he.2.2.1, by omega⟩
    let f := ((rectComplete Crt word s (W+1) U).subtype.comp F.ker.subtype).codRestrict _ hmem
    have hfound : Function.Injective f := by
      intro P Q he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : rectComplete Crt word s W U => (x : Source)) he
    have hker := LinearMap.finrank_le_finrank_of_injective hfound
    have hr := F.finrank_range_add_finrank_ker
    have ha := rectBoundary_rank Crt word s (W+1) U
    change Module.finrank L F.range ≤ _ at ha
    omega

theorem rectAmbient_volume (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ)
    (hraw : h ≤ 131071) (hbox : U 0 + U 1 ≤ s.U) (hw : rawWidthCond h s W) :
    Module.finrank L (rectAmbient h s W U) =
      area U * shapeSum s (fun q j => W+1+j - q*(131071-h)) +
        2*h*area U*P1_7_1.poleRows s := by
  rw [rectAmbient_finrank _ _ _ _ hbox]
  have hsum : shapeSum s (trueWidth h s W) =
      shapeSum s (fun q j => W+1+j - q*(131071-h)) + 2*h*P1_7_1.poleRows s := by
    unfold P1_7_1.poleRows shapeSum
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro j hj
    exact trueWidth_eq_add hraw hw (by simpa using hq) (by simpa using hj)
  rw [hsum]
  ring

#print axioms rectTelescope
#print axioms rectAmbient_volume
end
end KoalaRect