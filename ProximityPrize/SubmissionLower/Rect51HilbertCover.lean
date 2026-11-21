import ProximityPrize.SubmissionLower.Rect51HilbertCore

set_option autoImplicit false
set_option Elab.async false

namespace Rect51Hilbert
noncomputable section
open K1_14 (FX Seeds Equation)
open HighCore82706Tangent_3 (JetRing ordinate seedVar)
open MvPolynomial
open scoped BigOperators

open private layer_profile eq_of_eventual from ProximityPrize.SubmissionLower.Rect51HilbertCore

theorem inclusion_gap {Q R : Ideal JetRing} {p q : HilbertPoly}
    (hQR : Q ≤ R) (hp : IsProfile Q p) (hq : IsProfile R q) :
    NonnegativeTop (p-q) := by
  have hle (d : Degree) : kernelLayer Q d ≤ kernelLayer R d := by
    intro f hf
    have hz : Ideal.Quotient.mk Q (dehom f) = 0 := (Submodule.mem_bot FX).mp hf.2
    exact ⟨hf.1, (Submodule.mem_bot FX).mpr
      (Ideal.Quotient.eq_zero_iff_mem.mpr (hQR (Ideal.Quotient.eq_zero_iff_mem.mp hz)))⟩
  obtain ⟨r, hr, N, hN⟩ := layer_profile (kernelLayer Q) (kernelLayer R)
    (kernelLayer_stable Q) (kernelLayer_stable R) hle
  suffices he : p-q = r by rwa [he]
  apply eq_of_eventual
  obtain ⟨Np, hNp⟩ := hp
  obtain ⟨Nq, hNq⟩ := hq
  let B := max (max Np Nq) N
  refine ⟨B, fun h t b c hh ht hb hc => ?_⟩
  have hp' : Np ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hq' : Nq ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have hn' : N ≤ B := le_max_right _ _
  let d := nefDegree h t b c
  have hQ := congrArg (fun n : ℕ => (n : ℚ)) (kernelLayer_rank Q d)
  have hR := congrArg (fun n : ℕ => (n : ℚ)) (kernelLayer_rank R d)
  simp only [Nat.cast_add] at hQ hR
  change (_ : ℚ) + (hilbert Q h t b c : ℚ) = _ at hQ
  change (_ : ℚ) + (hilbert R h t b c : ℚ) = _ at hR
  change MvPolynomial.eval _ (p-q) = _
  rw [map_sub]
  change evalHilbert p h t b c - evalHilbert q h t b c = _
  linarith only [hQ, hR, hNp h t b c (hp'.trans hh) (hp'.trans ht) (hp'.trans hb) (hp'.trans hc),
    hNq h t b c (hq'.trans hh) (hq'.trans ht) (hq'.trans hb) (hq'.trans hc),
    hN h t b c (hn'.trans hh) (hn'.trans ht) (hn'.trans hb) (hn'.trans hc)]

private def factorMap {I P : Ideal JetRing} (h : I ≤ P) : (JetRing ⧸ I) →ₐ[FX] JetRing ⧸ P where
  toRingHom := Ideal.Quotient.factor h
  commutes' _ := rfl
theorem hilbert_mono {I P : Ideal JetRing} (h : I ≤ P) (a b c f : ℕ) :
    hilbert P a b c f ≤ hilbert I a b c f := by
  let d := nefDegree a b c f
  let F := (factorMap h).toLinearMap
  have hF (x : gradedPiece I d) : F x.val ∈ gradedPiece P d := by
    obtain ⟨q, hq, he⟩ := Submodule.mem_map.mp x.prop
    exact Submodule.mem_map.mpr ⟨q, hq, by rw [← he]; rfl⟩
  let L := (F.comp (gradedPiece I d).subtype).codRestrict (gradedPiece P d) hF
  apply LinearMap.finrank_le_finrank_of_surjective (f := L)
  intro x
  obtain ⟨q, hq, he⟩ := Submodule.mem_map.mp x.prop
  exact ⟨⟨qmap I q, Submodule.mem_map.mpr ⟨q, hq, rfl⟩⟩, Subtype.ext he⟩
set_option maxHeartbeats 500000 in
private theorem dehom_surjective : Function.Surjective dehom := by
  let s : Seeds →+* Cox :=
    MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X (if i = 0 then seed₀ 1 else seed₁ 1))
  let y : Equation →+* Cox := Polynomial.eval₂RingHom s (MvPolynomial.X h₁)
  let v : JetRing →+* Cox := Polynomial.eval₂RingHom y (MvPolynomial.X v₁)
  have hs : dehom.toRingHom.comp s =
      (Polynomial.C : Equation →+* JetRing).comp (Polynomial.C : Seeds →+* Equation) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change dehom (MvPolynomial.eval₂Hom MvPolynomial.C _ (MvPolynomial.C a)) =
        Polynomial.C (Polynomial.C (MvPolynomial.C a))
      rw [MvPolynomial.eval₂Hom_C]
      change MvPolynomial.aeval affineCoord (MvPolynomial.C a) = _
      rw [MvPolynomial.aeval_C]
      rfl
    · intro i
      change dehom (MvPolynomial.eval₂Hom MvPolynomial.C _ (MvPolynomial.X i)) = _
      rw [MvPolynomial.eval₂Hom_X']
      change MvPolynomial.aeval affineCoord (MvPolynomial.X (if i = 0 then seed₀ 1 else seed₁ 1)) =
        Polynomial.C (Polynomial.C (MvPolynomial.X i))
      rw [MvPolynomial.aeval_X]
      fin_cases i <;> rfl
  have hy : dehom.toRingHom.comp y = Polynomial.C := by
    apply Polynomial.ringHom_ext
    · intro a
      change dehom ((Polynomial.C a).eval₂ s (MvPolynomial.X h₁)) =
        Polynomial.C (Polynomial.C a)
      rw [Polynomial.eval₂_C]
      exact DFunLike.congr_fun hs a
    · change dehom ((Polynomial.X : Equation).eval₂ s (MvPolynomial.X h₁)) = Polynomial.C Polynomial.X
      rw [Polynomial.eval₂_X]
      simp [dehom, affineCoord, h₁, ordinate]
  have hv : dehom.toRingHom.comp v = RingHom.id JetRing := by
    apply Polynomial.ringHom_ext
    · intro a
      change dehom ((Polynomial.C a).eval₂ y (MvPolynomial.X v₁)) = Polynomial.C a
      rw [Polynomial.eval₂_C]
      exact DFunLike.congr_fun hy a
    · change dehom ((Polynomial.X : JetRing).eval₂ y (MvPolynomial.X v₁)) = Polynomial.X
      rw [Polynomial.eval₂_X]
      simp [dehom, affineCoord, v₁]
  exact fun x => ⟨v x, DFunLike.congr_fun hv x⟩
private theorem pad_monomial (m : CoxVar →₀ ℕ) (a : FX) (k : ℕ)
    (h₁' : (Finsupp.weight coxWeight m).1 ≤ 3*k)
    (hv' : (Finsupp.weight coxWeight m).2.1 ≤ k)
    (hs₀ : (Finsupp.weight coxWeight m).2.2.1 ≤ k)
    (hs₁ : (Finsupp.weight coxWeight m).2.2.2 ≤ k) :
    ∃ p : Cox, p.IsWeightedHomogeneous coxWeight (nefDegree k k k k) ∧
      dehom p = dehom (monomial m a) := by
  let w := Finsupp.weight coxWeight m
  let i := 3*k - w.1
  let j := k - w.2.1
  let b := k - w.2.2.1
  let c := k - w.2.2.2
  refine ⟨monomial m a * (MvPolynomial.X h₀)^i * (MvPolynomial.X v₀)^j *
    (MvPolynomial.X (seed₀ 0))^b * (MvPolynomial.X (seed₁ 0))^c, ?_, ?_⟩
  · have hw := ((((isWeightedHomogeneous_monomial coxWeight m a rfl).mul
        ((isWeightedHomogeneous_X FX coxWeight h₀).pow i)).mul
        ((isWeightedHomogeneous_X FX coxWeight v₀).pow j)).mul
        ((isWeightedHomogeneous_X FX coxWeight (seed₀ 0)).pow b)).mul
        ((isWeightedHomogeneous_X FX coxWeight (seed₁ 0)).pow c)
    have he : w + i • coxWeight h₀ + j • coxWeight v₀ + b • coxWeight (seed₀ 0) +
        c • coxWeight (seed₁ 0) = nefDegree k k k k := by
      change (w.1+i*1+j*0+b*0+c*0, w.2.1+i*0+j*1+b*0+c*0,
        w.2.2.1+i*0+j*0+b*1+c*0, w.2.2.2+i*0+j*0+b*0+c*1) = (k+2*k,k,k,k)
      have ha : w.1 ≤ 3*k := h₁'
      have hb : w.2.1 ≤ k := hv'
      change w.2.2.1 ≤ k at hs₀
      change w.2.2.2 ≤ k at hs₁
      dsimp [i,j,b,c]
      congr 1
      · omega
      · congr 1
        · omega
        · congr 1 <;> omega
    rwa [← he]
  · simp [dehom, affineCoord, h₀, v₀, seed₀, seed₁]
private theorem lift_big (x : JetRing) :
    ∃ n, ∀ k, n ≤ k → ∃ p : Cox,
      p.IsWeightedHomogeneous coxWeight (nefDegree k k k k) ∧ dehom p = x := by
  classical
  obtain ⟨q, hq⟩ := dehom_surjective x
  let size := fun m : CoxVar →₀ ℕ =>
    let w := Finsupp.weight coxWeight m
    w.1 + w.2.1 + w.2.2.1 + w.2.2.2
  refine ⟨q.support.sup size, fun k hk => ?_⟩
  have hex (m : q.support) : ∃ p : Cox,
      p.IsWeightedHomogeneous coxWeight (nefDegree k k k k) ∧
        dehom p = dehom (monomial m.val (q.coeff m.val)) := by
    have hm : size m.val ≤ k := (Finset.le_sup m.prop).trans hk
    change (Finsupp.weight coxWeight m.val).1 + (Finsupp.weight coxWeight m.val).2.1 +
      (Finsupp.weight coxWeight m.val).2.2.1 + (Finsupp.weight coxWeight m.val).2.2.2 ≤ k at hm
    exact pad_monomial m.val (q.coeff m.val) k (by omega) (by omega) (by omega) (by omega)
  choose f hd hf using hex
  refine ⟨∑ m, f m, (weightedHomogeneousSubmodule FX coxWeight _).sum_mem
    (fun m _ => hd m), ?_⟩
  rw [map_sum]
  simp_rw [hf]
  rw [Finset.sum_coe_sort q.support (fun m => dehom (monomial m (q.coeff m))),
    ← map_sum, ← MvPolynomial.as_sum, hq]
private def mulQuotient (I P : Ideal JetRing) (s : JetRing)
    (h : ∀ p ∈ I, s * p ∈ P) : (JetRing ⧸ I) →ₗ[FX] JetRing ⧸ P :=
  (I.restrictScalars FX).liftQ ((Ideal.Quotient.mkₐ FX P).toLinearMap ∘ₗ LinearMap.mulLeft FX s)
    (fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr (h p hp))
private theorem mul_mem_iInf {ι : Type} {P : ι → Ideal JetRing} {s : ι → JetRing}
    (hmem : ∀ i j, i ≠ j → s i ∈ P j) (i : ι) :
    ∀ p ∈ P i, s i * p ∈ ⨅ j, P j := by
  classical
  intro p hp
  refine Ideal.mem_iInf.mpr fun j => ?_
  by_cases hij : i = j
  · subst hij
    exact (P i).mul_mem_left _ hp
  · exact (P j).mul_mem_right _ (hmem i j hij)
theorem separator_bound {ι : Type} [Fintype ι] (I : Ideal JetRing) (P : ι → Ideal JetRing)
    (hp : ∀ i, (P i).IsPrime) (hinc : Pairwise fun i j => ¬P i ≤ P j) (hI : ∀ i, I ≤ P i) :
    ∃ k, ∀ h t b c, (∑ i, hilbert (P i) h t b c) ≤ hilbert I (h+k) (t+k) (b+k) (c+k) := by
  classical
  obtain ⟨sep, hsep⟩ := Ideal.exists_separators_of_pairwise_not_le hp hinc
  choose n hn using fun i => lift_big (sep i)
  let k := Finset.univ.sup n
  have hk (i : ι) : n i ≤ k := Finset.le_sup (Finset.mem_univ i)
  choose lift hd he using fun i => hn i k (hk i)
  let Q := ⨅ j, P j
  let F (i : ι) := mulQuotient (P i) Q (sep i)
    (mul_mem_iInf (fun i j h => (hsep i j).mpr h) i)
  have hF (i : ι) (p : JetRing) :
      F i (Ideal.Quotient.mk (P i) p) = Ideal.Quotient.mk Q (sep i * p) := rfl
  refine ⟨k, fun h t b c => ?_⟩
  let d := nefDegree h t b c
  let d' := nefDegree (h+k) (t+k) (b+k) (c+k)
  let Φ : ((i : ι) → gradedPiece (P i) d) →ₗ[FX] JetRing ⧸ Q :=
    ∑ i, F i ∘ₗ (gradedPiece (P i) d).subtype ∘ₗ LinearMap.proj i
  have hΦ (x : (i : ι) → gradedPiece (P i) d) : Φ x ∈ gradedPiece Q d' := by
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.subtype_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨q, hq, hx⟩ := Submodule.mem_map.mp (x i).prop
    change q.IsWeightedHomogeneous coxWeight d at hq
    change qmap (P i) q = (x i).val at hx
    rw [← hx, show qmap (P i) q = Ideal.Quotient.mk (P i) (dehom q) from rfl]
    have hsum : nefDegree k k k k + d = d' := by
      change (k+2*k+(h+2*t), k+t, k+b, k+c) = (h+k+2*(t+k), t+k, b+k, c+k)
      congr 1
      · omega
      · congr 1
        · omega
        · congr 1 <;> omega
    exact Submodule.mem_map.mpr ⟨lift i * q, hsum ▸ (hd i).mul hq, by
      change Ideal.Quotient.mk Q (dehom (lift i * q)) = F i (Ideal.Quotient.mk (P i) (dehom q))
      rw [map_mul, he, hF]⟩
  have hker (x : (i : ι) → gradedPiece (P i) d) (hx : Φ x = 0) : x = 0 := by
    funext i
    apply Subtype.ext
    have hfac := congrArg (Ideal.Quotient.factor (iInf_le P i)) hx
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.subtype_apply, map_sum, map_zero] at hfac
    rw [Finset.sum_eq_single i] at hfac
    · obtain ⟨q, _, hq⟩ := Submodule.mem_map.mp (x i).prop
      change Ideal.Quotient.mk (P i) (dehom q) = (x i).val at hq
      rw [← hq, hF, Ideal.Quotient.factor_mk, map_mul] at hfac
      have := hp i
      have hnz : Ideal.Quotient.mk (P i) (sep i) ≠ 0 := fun hz =>
        (hsep i i).mp (Ideal.Quotient.eq_zero_iff_mem.mp hz) rfl
      simp only [Pi.zero_apply, ZeroMemClass.coe_zero, ← hq]
      exact (mul_eq_zero.mp hfac).resolve_left hnz
    · intro j _ hji
      obtain ⟨q, _, hq⟩ := Submodule.mem_map.mp (x j).prop
      change Ideal.Quotient.mk (P j) (dehom q) = (x j).val at hq
      rw [← hq, hF, Ideal.Quotient.factor_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((P i).mul_mem_right _ ((hsep j i).mpr hji))
    · simp
  have hdim : (∑ i, hilbert (P i) h t b c) ≤ hilbert Q (h+k) (t+k) (b+k) (c+k) := by
    have (i : ι) : Module.Free FX (gradedPiece (P i) d) := Module.Free.of_divisionRing FX _
    change (∑ i, Module.finrank FX (gradedPiece (P i) d)) ≤ Module.finrank FX (gradedPiece Q d')
    rw [← Module.finrank_pi_fintype]
    apply LinearMap.finrank_le_finrank_of_injective (f := Φ.codRestrict _ hΦ)
    intro x y heq
    exact sub_eq_zero.mp (hker _ ((map_sub Φ x y).trans (sub_eq_zero.mpr (congrArg Subtype.val heq))))
  exact hdim.trans (hilbert_mono (le_iInf hI) _ _ _ _)
end
end Rect51Hilbert

#print axioms Rect51Hilbert.inclusion_gap
#print axioms Rect51Hilbert.separator_bound
