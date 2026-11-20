import ProximityPrize.SubmissionLower.HighSource6921Rank

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

namespace HighSource6921

noncomputable section
open K1 K1_14 K1_14_1 Polynomial
open scoped Polynomial BigOperators

theorem chart_poles {u del} (M : K21.AnchorModel u del) {Γ} (F : K21.AnchoredFamily M Γ)
    (H : L[X]) (hH : H21.AdjacentChart M F H) :
    ∃ D : PoleData M.overhead.toNat,
      (∀ i k, (D.block i).eval (nodeL k) ≠ 0) ∧
      ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ) := by
  let σ := frobenius L p
  rcases hH with ⟨hm, hd, _, hm', hd', _, hcop, hnode, hdet, hdet', hmarks⟩
  let A := liftPoly (M.factor * M.A₀)
  let B := liftPoly (M.factor * M.A₁)
  let Q := liftPoly M.Q
  have hdet0 : IsCoprime (Q * A) H := by
    simpa [Q, A, liftPoly, mul_assoc] using hdet
  have hdet1 : IsCoprime (Q.map σ * A.map σ) (H.map σ) := by
    simpa [Q, A, liftPoly, mul_assoc, σ, Polynomial.map_mul] using hdet'
  let D : PoleData M.overhead.toNat :=
    ⟨![H, H.map σ], ![Q, Q.map σ], ![A, A.map σ], ![B, B.map σ],
      fun i => by fin_cases i <;> first | exact hm | exact hm',
      fun i => by fin_cases i <;> first | exact hd | exact hd',
      hcop, fun i => by fin_cases i <;> first | exact hdet0 | exact hdet1⟩
  refine ⟨D, ?_, ?_⟩
  · intro i k
    fin_cases i
    · exact (hnode k).1
    · exact (hnode k).2
  · intro γ hγ i
    let z := algebraMap K L (M.label γ)
    have hz : liftPoly (M.factor * M.amplitude γ) = A + (@Polynomial.C L _) z * B := by
      simp [A, B, z, K21.AnchorModel.amplitude, liftPoly, mul_add, mul_left_comm]
    obtain ⟨h₀, h₁, hr₀, hr₁⟩ := hmarks γ hγ
    fin_cases i
    · change IsCoprime (A + (@Polynomial.C L _) z * B) H ∧
        H ∣ (A + (@Polynomial.C L _) z * B) * liftPoly (F.scalar γ) + (@Polynomial.C L _) z * Q
      rw [← hz]
      exact ⟨h₀, hr₀⟩
    · have hσ : (liftPoly (M.factor * M.amplitude γ)).map σ =
          A.map σ + (@Polynomial.C L _) (z^p) * B.map σ := by
        rw [hz, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
        rfl
      change IsCoprime (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) (H.map σ) ∧
        H.map σ ∣ (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) * liftPoly (F.scalar γ) +
          (@Polynomial.C L _) (z^p) * Q.map σ
      rw [← hσ]
      exact ⟨h₁, hr₁⟩

/-- Construct the actual two-block source for the new agreement and full height interval. -/
theorem proof : H21.c1 := by
  have h1 := CRT.proof
  have h2 := Necessary.proof
  have h3 := Hasse.proof
  have h4 := Weight.proof
  have h5 := Ambient.proof
  have h6 := Physical.proof
  have h7 := Pole.proof
  have h8 := Telescope.proof
  intro u del M Γ F hlo hhi H hH
  have lo : 2448 ≤ M.overhead.toNat := by omega
  have hi : M.overhead.toNat ≤ 32872 := by omega
  obtain ⟨D, hnode, hres⟩ := chart_poles M F H hH
  obtain ⟨Crt⟩ := h1 _ lo hi D
  let word (i : I) : L := algebraMap K L (M.word i)
  refine ⟨evaluated Crt word, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro s _ s' _ hm hB hJ hU W W' hW
    exact evaluated_mono Crt word hm hB hJ hU hW
  · intro s _ W hW P hP γ hγ
    let B := F.mark γ hγ
    have hdegree : (liftPoly (F.scalar γ)).natDegree ≤ 131071 + M.overhead.toNat := by
      rw [liftPoly, Polynomial.natDegree_map]
      rcases B.scalar_degree with hzero | hd
      · simp [hzero]
      · omega
    refine h2 _ lo hi D Crt word hnode _ _ (hres γ hγ) hdegree
      B.bad.support B.bad.agreement ?_ s W hW P hP
    intro k hk
    rw [liftPoly, nodeL, Polynomial.eval_map, Polynomial.eval₂_hom, B.scalar_hits k hk]
  · intro s _ W P hP j i hne
    exact evaluated_shape Crt word hP j i hne
  · intro s _ W P hP hne
    exact h4 _ lo hi D Crt word s W P hP hne
  · intro s _ W P hP i r
    exact h3 _ lo hi D Crt word s W P hP i r
  · intro s _ W _ hW
    have hvol := h5 _ lo hi s W hW
    have hcontact := h6 _ lo hi word s W
    have hpole := h7 _ lo hi D Crt word s W
    have hsum := h8 _ lo hi D Crt word s W
    change rawVolumeAt M.overhead.toNat s W ≤
      (physicalDebit s + poleSeedDebit M.overhead.toNat s) +
        ∑ t ∈ Finset.range (W+1), Module.finrank FX (evaluated Crt word s t)
    omega

end
end HighSource6921
