import ProximityPrize.SubmissionLower.Part.G017


section Compact_SecondJetSpace
/-! The finite source space for the local second-jet map. -/
namespace ProximityPrize.SubmissionLower.SecondJetSpace
open scoped BigOperators
open SecondJetBasis SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def bound (m L s1 s2 : ℕ) : Fin 5 → ℕ := ![m,s2+1,m,s1+1,L+1]

def Index (m L s1 s2 : ℕ) :=
  {d : ∀ k, Fin (bound m L s1 s2 k) //
    (d 2).val ≤ (d 0).val ∧ (d 1).val+(d 2).val+(d 3).val+(d 4).val ≤ L}

instance (m L s1 s2 : ℕ) : Fintype (Index m L s1 s2) := by
  unfold Index
  infer_instance

def exponent {m L s1 s2 : ℕ} (d : Index m L s1 s2) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => (d.val k).val)

@[simp] theorem exponent_apply {m L s1 s2 : ℕ} (d : Index m L s1 s2) (k : Fin 5) :
    exponent d k = (d.val k).val := by simp [exponent]

theorem exponent_injective (m L s1 s2 : ℕ) :
    Function.Injective (exponent (m := m) (L := L) (s1 := s1) (s2 := s2)) := by
  intro d e h
  apply Subtype.ext
  funext k
  apply Fin.ext
  simpa only [exponent_apply] using congrArg (fun f : Fin 5 →₀ ℕ => f k) h

theorem exponent_allowed {m L s1 s2 : ℕ} (d : Index m L s1 s2) :
    Allowed m L s1 s2 (exponent d) := by
  have h0 : (d.val 0).val < m := (d.val 0).isLt
  have h1 : (d.val 1).val < s2+1 := (d.val 1).isLt
  have h3 : (d.val 3).val < s1+1 := (d.val 3).isLt
  simp only [Allowed, exponent_apply]
  exact ⟨h0,d.property.1,by omega,by omega,d.property.2⟩

theorem mem_range_exponent (m L s1 s2 : ℕ) (d : Fin 5 →₀ ℕ) :
    d ∈ Set.range (exponent (m := m) (L := L) (s1 := s1) (s2 := s2)) ↔
      Allowed m L s1 s2 d := by
  constructor
  · rintro ⟨e,rfl⟩
    exact exponent_allowed e
  · intro h
    dsimp only [Allowed] at h
    have hb : ∀ k, d k < bound m L s1 s2 k := by
      intro k
      fin_cases k
      · exact h.1
      · change d 1 < s2+1
        omega
      · change d 2 < m
        omega
      · change d 3 < s1+1
        omega
      · change d 4 < L+1
        omega
    let e : Index m L s1 s2 := ⟨fun k => ⟨d k,hb k⟩,h.2.1,h.2.2.2.2⟩
    refine ⟨e,?_⟩
    ext k
    simp [e]

def sourceMap (m L s1 s2 : ℕ) : (Index m L s1 s2 → K) →ₗ[K]
    Jet (MvPolynomial (Fin 3) K) :=
  (flatEquiv (K := K)).toLinearMap.comp (FiniteMonomials.reconstruct exponent)

def source (m L s1 s2 : ℕ) : Submodule K (Jet (MvPolynomial (Fin 3) K)) :=
  (sourceMap (K := K) m L s1 s2).range

instance source_finite (m L s1 s2 : ℕ) : FiniteDimensional K (source (K := K) m L s1 s2) := by
  unfold source
  infer_instance

theorem sourceMap_injective (m L s1 s2 : ℕ) :
    Function.Injective (sourceMap (K := K) m L s1 s2) :=
  (flatEquiv (K := K)).injective.comp
    (FiniteMonomials.reconstruct_injective _ (exponent_injective m L s1 s2))

theorem finrank_source (m L s1 s2 : ℕ) :
    Module.finrank K (source (K := K) m L s1 s2) = Fintype.card (Index m L s1 s2) := by
  unfold source
  rw [← (LinearEquiv.ofInjective (sourceMap (K := K) m L s1 s2)
    (sourceMap_injective m L s1 s2)).finrank_eq]
  simp

theorem mem_source_iff (m L s1 s2 : ℕ) (P : Jet (MvPolynomial (Fin 3) K)) :
    P ∈ source (K := K) m L s1 s2 ↔
      ∀ d ∈ ((flatEquiv (K := K)).symm P).support, Allowed m L s1 s2 d := by
  have hm : P ∈ source (K := K) m L s1 s2 ↔
      (flatEquiv (K := K)).symm P ∈ (FiniteMonomials.reconstruct (K := K)
        (exponent (m := m) (L := L) (s1 := s1) (s2 := s2))).range := by
    constructor
    · rintro ⟨c,hc⟩
      refine ⟨c,?_⟩
      have h := congrArg (flatEquiv (K := K)).symm hc
      simpa [sourceMap] using h
    · rintro ⟨c,hc⟩
      refine ⟨c,?_⟩
      have h := congrArg (flatEquiv (K := K)) hc
      simpa [sourceMap] using h
  rw [hm, FiniteMonomials.mem_range_iff _ (exponent_injective m L s1 s2)]
  simp only [mem_range_exponent]

theorem truncated_monomial_term_mem (m L s1 s2 r h a b i j z : ℕ)
    (hi : i+a+b ≤ r) (hj : j+a+b ≤ s1) (hh : h+a ≤ s2)
    (hL : i+j+h+a+b+z ≤ L) :
    truncateOuter (K := K) m (term (K := K) SecondJetLocal.v r h a b
      (MvPolynomial.X 0^i*MvPolynomial.X 1^j*MvPolynomial.X 2^z)) ∈
        source (K := K) m L s1 s2 := by
  change truncateOuter (K := K) m (term (K := K)
    (MvPolynomial.X 0-MvPolynomial.X 1) r h a b _) ∈ _
  rw [← flatEquiv_vector, ← flatEquiv_truncFlat, mem_source_iff]
  simpa only [AlgEquiv.symm_apply_apply] using
    (vector_allowed (K := K) m L s1 s2 r h a b i j z hi hj hh hL)

end
end ProximityPrize.SubmissionLower.SecondJetSpace

end Compact_SecondJetSpace
