import ProximityPrize.SubmissionLower.PartG019


section Compact_SecondJetFacetSpace
/-! The second-jet source space with a shared R/S degree cap. -/
namespace ProximityPrize.SubmissionLower.SecondJetFacetSpace
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetFacetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def Index (m L B s : ℕ) :=
  {d : SecondJetSpace.Index m L B s // (d.val 1).val+(d.val 3).val ≤ B}

instance (m L B s : ℕ) : Fintype (Index m L B s) := by
  unfold Index
  infer_instance

def exponent {m L B s : ℕ} (d : Index m L B s) : Fin 5 →₀ ℕ :=
  SecondJetSpace.exponent d.val

@[simp] theorem exponent_apply {m L B s : ℕ} (d : Index m L B s) (k : Fin 5) :
    exponent d k = (d.val.val k).val := by simp [exponent]

theorem exponent_injective (m L B s : ℕ) :
    Function.Injective (exponent (m := m) (L := L) (B := B) (s := s)) :=
  (SecondJetSpace.exponent_injective m L B s).comp Subtype.val_injective

theorem mem_range_exponent (m L B s : ℕ) (d : Fin 5 →₀ ℕ) :
    d ∈ Set.range (exponent (m := m) (L := L) (B := B) (s := s)) ↔
      Allowed m L B s d ∧ d 1+d 3 ≤ B := by
  constructor
  · rintro ⟨e,rfl⟩
    exact ⟨SecondJetSpace.exponent_allowed e.val,e.property⟩
  · rintro ⟨hd, hrs⟩
    obtain ⟨e,he⟩ := (SecondJetSpace.mem_range_exponent m L B s d).mpr hd
    have hrs' : (e.val 1).val+(e.val 3).val ≤ B := by
      simpa only [← he, SecondJetSpace.exponent_apply] using hrs
    exact ⟨⟨e,hrs'⟩,he⟩

def sourceMap (m L B s : ℕ) : (Index m L B s → K) →ₗ[K]
    Jet (MvPolynomial (Fin 3) K) :=
  (flatEquiv (K := K)).toLinearMap.comp (FiniteMonomials.reconstruct exponent)

def source (m L B s : ℕ) : Submodule K (Jet (MvPolynomial (Fin 3) K)) :=
  (sourceMap (K := K) m L B s).range

instance source_finite (m L B s : ℕ) : FiniteDimensional K (source (K := K) m L B s) := by
  unfold source
  infer_instance

theorem sourceMap_injective (m L B s : ℕ) :
    Function.Injective (sourceMap (K := K) m L B s) :=
  (flatEquiv (K := K)).injective.comp
    (FiniteMonomials.reconstruct_injective _ (exponent_injective m L B s))

theorem finrank_source (m L B s : ℕ) :
    Module.finrank K (source (K := K) m L B s) = Fintype.card (Index m L B s) := by
  unfold source
  rw [← (LinearEquiv.ofInjective (sourceMap (K := K) m L B s)
    (sourceMap_injective m L B s)).finrank_eq]
  simp

theorem mem_source_iff (m L B s : ℕ) (P : Jet (MvPolynomial (Fin 3) K)) :
    P ∈ source (K := K) m L B s ↔
      ∀ d ∈ ((flatEquiv (K := K)).symm P).support,
        Allowed m L B s d ∧ d 1+d 3 ≤ B := by
  have hm : P ∈ source (K := K) m L B s ↔
      (flatEquiv (K := K)).symm P ∈ (FiniteMonomials.reconstruct (K := K)
        (exponent (m := m) (L := L) (B := B) (s := s))).range := by
    constructor
    · rintro ⟨c,hc⟩
      refine ⟨c,?_⟩
      have h := congrArg (flatEquiv (K := K)).symm hc
      simpa [sourceMap] using h
    · rintro ⟨c,hc⟩
      refine ⟨c,?_⟩
      have h := congrArg (flatEquiv (K := K)) hc
      simpa [sourceMap] using h
  rw [hm, FiniteMonomials.mem_range_iff _ (exponent_injective m L B s)]
  simp only [mem_range_exponent]

theorem truncated_monomial_term_mem (m L B s r h a b i j z : ℕ)
    (hi : i+a+b ≤ r) (hj : j+h+a+b ≤ B) (hh : h+a ≤ s)
    (hL : i+j+h+a+b+z ≤ L) :
    truncateOuter (K := K) m (term (K := K) SecondJetLocal.v r h a b
      (MvPolynomial.X 0^i*MvPolynomial.X 1^j*MvPolynomial.X 2^z)) ∈
        source (K := K) m L B s := by
  change truncateOuter (K := K) m (term (K := K)
    (MvPolynomial.X 0-MvPolynomial.X 1) r h a b _) ∈ _
  rw [← flatEquiv_vector, ← flatEquiv_truncFlat, mem_source_iff]
  simp only [AlgEquiv.symm_apply_apply]
  intro d hd
  exact ⟨vector_allowed (K := K) m L B s r h a b i j z hi (by omega) hh hL d hd,
    (((vector_rs (K := K) r h a b i j z).mono hj).truncFlat m) d hd⟩

end
end ProximityPrize.SubmissionLower.SecondJetFacetSpace

end Compact_SecondJetFacetSpace
