import ProximityPrize.SubmissionLower.Rect51HilbertProfiles

set_option autoImplicit false
set_option Elab.async false

namespace Rect51Hilbert
noncomputable section
open HighCore82706Tangent_3 (JetRing)
open K1_14 (FX)
open MvPolynomial

private theorem layer_profile (A B : Layer)
    (hA : Stable A) (hB : Stable B) (hab : ∀ d, A d ≤ B d) :
    ∃ p : HilbertPoly, NonnegativeTop p ∧
      EventuallyInChamber fun h t s₀ s₁ =>
        (Module.finrank FX (A (nefDegree h t s₀ s₁)) : ℚ) + evalHilbert p h t s₀ s₁ =
          (Module.finrank FX (B (nefDegree h t s₀ s₁)) : ℚ) := by
  obtain ⟨U, V, hU, hV, _, hrank⟩ := initial_rank A B hA hB hab
  obtain ⟨blocks, hblocks⟩ := orthant_partition U V hU hV
  obtain ⟨p, hpos, N, hN⟩ := block_profile blocks
  refine ⟨p, hpos, N, fun h t s₀ s₁ hh ht hs₀ hs₁ => ?_⟩
  change (Module.finrank FX (A (nefDegree h t s₀ s₁)) : ℚ) + evalHilbert p h t s₀ s₁ =
    (Module.finrank FX (B (nefDegree h t s₀ s₁)) : ℚ)
  rw [← hN h t s₀ s₁ hh ht hs₀ hs₁, ← hblocks]
  exact_mod_cast hrank (nefDegree h t s₀ s₁)

private theorem eq_of_eventual {p q : HilbertPoly}
    (h : EventuallyInChamber fun h t s₀ s₁ => evalHilbert p h t s₀ s₁ = evalHilbert q h t s₀ s₁) :
    p = q := by
  obtain ⟨N, hN⟩ := h
  let S : Fin 4 → Set ℚ := fun _ => Set.range (fun n : ℕ => ((N+n : ℕ) : ℚ))
  have hS (i : Fin 4) : (S i).Infinite := by
    apply Set.infinite_range_of_injective
    intro a b hab
    change ((N+a : ℕ) : ℚ) = ((N+b : ℕ) : ℚ) at hab
    have hc : N+a = N+b := by exact_mod_cast hab
    omega
  apply MvPolynomial.funext_set S hS
  intro x hx
  have htail (i : Fin 4) : ∃ n : ℕ, N ≤ n ∧ (n : ℚ) = x i := by
    obtain ⟨n, hn⟩ := hx i (Set.mem_univ i)
    exact ⟨N+n, Nat.le_add_right N n, hn⟩
  obtain ⟨a, ha, hea⟩ := htail 0
  obtain ⟨b, hb, heb⟩ := htail 1
  obtain ⟨c, hc, hec⟩ := htail 2
  obtain ⟨d, hd, hed⟩ := htail 3
  have he : x = ![(a : ℚ), (b : ℚ), (c : ℚ), (d : ℚ)] := by
    funext i
    fin_cases i
    · exact hea.symm
    · exact heb.symm
    · exact hec.symm
    · exact hed.symm
  rw [he]
  exact hN a b c d ha hb hc hd

private theorem eval_difference (p q : HilbertPoly) {a b c f h t s₀ s₁ : ℕ}
    (ha : a ≤ h) (hb : b ≤ t) (hc : c ≤ s₀) (hf : f ≤ s₁) :
    evalHilbert (difference p ![a,b,c,f] - q) h t s₀ s₁ =
      evalHilbert p h t s₀ s₁ - evalHilbert p (h-a) (t-b) (s₀-c) (s₁-f) - evalHilbert q h t s₀ s₁ := by
  let x : Fin 4 → ℚ := ![(h : ℚ), (t : ℚ), (s₀ : ℚ), (s₁ : ℚ)]
  have hx : (fun i : Fin 4 => aeval x (MvPolynomial.X i - MvPolynomial.C (![a, b, c, f] i : ℚ))) =
      ![((h-a : ℕ) : ℚ), ((t-b : ℕ) : ℚ), ((s₀-c : ℕ) : ℚ), ((s₁-f : ℕ) : ℚ)] := by
    funext i
    fin_cases i <;> simp [x, Nat.cast_sub ha, Nat.cast_sub hb, Nat.cast_sub hc, Nat.cast_sub hf]
  change aeval x (p - bind₁ (fun i : Fin 4 => MvPolynomial.X i - MvPolynomial.C (![a, b, c, f] i : ℚ)) p - q) =
    aeval x p - aeval ![((h-a : ℕ) : ℚ), ((t-b : ℕ) : ℚ), ((s₀-c : ℕ) : ℚ), ((s₁-f : ℕ) : ℚ)] p - aeval x q
  rw [map_sub, map_sub, aeval_bind₁, hx]

theorem profile_exists (Q : Ideal JetRing) : ∃ p : HilbertPoly, IsProfile Q p ∧ NonnegativeTop p := by
    obtain ⟨p, hpos, N, hN⟩ := layer_profile (kernelLayer Q) homogeneous
      (kernelLayer_stable Q) homogeneous_stable (kernelLayer_stable Q).1
    refine ⟨p, ⟨N, fun h t s₀ s₁ hh ht hs₀ hs₁ => ?_⟩, hpos⟩
    have hr := congrArg (fun n : ℕ => (n : ℚ)) (kernelLayer_rank Q (nefDegree h t s₀ s₁))
    simp only [Nat.cast_add] at hr
    change (_ : ℚ) + (hilbert Q h t s₀ s₁ : ℚ) = _ at hr
    linarith only [hr, hN h t s₀ s₁ hh ht hs₀ hs₁]

theorem cut_gap_cox {Q R : Ideal JetRing} {a b c f : ℕ}
    (S : CoxSection Q (nefDegree a b c f)) (hQR : Q ≤ R) (hmem : S.affine ∈ R)
    (hreg : IsLeftRegular (Ideal.Quotient.mk Q S.affine))
    {p q : HilbertPoly} (hp : IsProfile Q p) (hq : IsProfile R q) :
    NonnegativeTop (difference p ![a,b,c,f] - q) := by
    let A := cutLayer Q (nefDegree a b c f) (Ideal.Quotient.mk Q S.affine)
    obtain ⟨r, hr, Nr, hNr⟩ := layer_profile A (kernelLayer R)
      (cutLayer_stable _ _ _) (kernelLayer_stable R) (cutLayer_le hQR _ hmem)
    suffices he : difference p ![a,b,c,f] - q = r by rwa [he]
    apply eq_of_eventual
    obtain ⟨Np, hNp⟩ := hp
    obtain ⟨Nq, hNq⟩ := hq
    refine ⟨Np + Nq + Nr + 2*S.order + a + b + c + f, fun h t s₀ s₁ hh ht hs₀ hs₁ => ?_⟩
    have ha : a ≤ h := by omega
    have hb : b ≤ t := by omega
    have hc : c ≤ s₀ := by omega
    have hf : f ≤ s₁ := by omega
    have hp0 := hNp h t s₀ s₁ (by omega) (by omega) (by omega) (by omega)
    have hp1 := hNp (h-a) (t-b) (s₀-c) (s₁-f) (by omega) (by omega) (by omega) (by omega)
    have hq0 := hNq h t s₀ s₁ (by omega) (by omega) (by omega) (by omega)
    have hR := hNr h t s₀ s₁ (by omega) (by omega) (by omega) (by omega)
    have hcut := cutLayer_rank S hreg (h := h-a) (t := t-b) (s₀ := s₀-c) (s₁ := s₁-f) (by omega)
    rw [Nat.sub_add_cancel ha, Nat.sub_add_cancel hb, Nat.sub_add_cancel hc, Nat.sub_add_cancel hf] at hcut
    let d := nefDegree h t s₀ s₁
    have hcut' : (Module.finrank FX (kernelLayer Q d) : ℚ) +
        (hilbert Q (h-a) (t-b) (s₀-c) (s₁-f) : ℚ) = (Module.finrank FX (A d) : ℚ) := by
      exact_mod_cast hcut
    have hk (I : Ideal JetRing) : (Module.finrank FX (kernelLayer I d) : ℚ) +
        (hilbert I h t s₀ s₁ : ℚ) = (Module.finrank FX (homogeneous d) : ℚ) := by
      exact_mod_cast kernelLayer_rank I d
    change evalHilbert (difference p ![a,b,c,f] - q) h t s₀ s₁ = evalHilbert r h t s₀ s₁
    rw [eval_difference p q ha hb hc hf]
    change (Module.finrank FX (A d) : ℚ) + evalHilbert r h t s₀ s₁ =
      (Module.finrank FX (kernelLayer R d) : ℚ) at hR
    linarith only [hR, hcut', hk Q, hk R, hp0, hp1, hq0]

#print axioms profile_exists
#print axioms cut_gap_cox
end
end Rect51Hilbert
