import ProximityPrize.SubmissionLower.PartG069


section Compact_SecondJetRelaxedSpace
/-! The clipped local source for degree-sensitive weighted second jets. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedSpace
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetWeightedSupport SecondJetWeightedLocal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def Index (m L B s U : ℕ) (caps : ℕ → ℕ) :=
  {d : SecondJetSpace.Index m L B s // 2*(d.val 1).val+(d.val 3).val ≤ B ∧
    (d.val 1).val+(d.val 2).val+(d.val 3).val ≤ U ∧
    (d.val 1).val+(d.val 2).val+(d.val 3).val ≤ caps (d.val 1).val}

instance (m L B s U : ℕ) (caps : ℕ → ℕ) : Fintype (Index m L B s U caps) := by
  unfold Index
  infer_instance

def exponent {m L B s U : ℕ} {caps : ℕ → ℕ} (d : Index m L B s U caps) : Fin 5 →₀ ℕ :=
  SecondJetSpace.exponent d.val

@[simp] theorem exponent_apply {m L B s U : ℕ} {caps : ℕ → ℕ} (d : Index m L B s U caps) (k : Fin 5) :
    exponent d k = (d.val.val k).val := by simp [exponent]

theorem exponent_injective (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Function.Injective (exponent (m := m) (L := L) (B := B) (s := s) (U := U) (caps := caps)) :=
  (SecondJetSpace.exponent_injective m L B s).comp Subtype.val_injective

theorem mem_range_exponent (m L B s U : ℕ) (caps : ℕ → ℕ) (d : Fin 5 →₀ ℕ) :
    d ∈ Set.range (exponent (m := m) (L := L) (B := B) (s := s) (U := U) (caps := caps)) ↔
      Allowed m L B s d ∧ 2*d 1+d 3 ≤ B ∧ d 1+d 2+d 3 ≤ U ∧ d 1+d 2+d 3 ≤ caps (d 1) := by
  constructor
  · rintro ⟨e,rfl⟩
    exact ⟨SecondJetSpace.exponent_allowed e.val,e.property⟩
  · rintro ⟨hd, hrs⟩
    obtain ⟨e,he⟩ := (SecondJetSpace.mem_range_exponent m L B s d).mpr hd
    have hrs' : 2*(e.val 1).val+(e.val 3).val ≤ B ∧ (e.val 1).val+(e.val 2).val+(e.val 3).val ≤ U ∧ (e.val 1).val+(e.val 2).val+(e.val 3).val ≤ caps (e.val 1).val := by
      simpa only [← he, SecondJetSpace.exponent_apply] using hrs
    exact ⟨⟨e,hrs'⟩,he⟩

def sourceMap (m L B s U : ℕ) (caps : ℕ → ℕ) : (Index m L B s U caps → K) →ₗ[K]
    Jet (MvPolynomial (Fin 3) K) :=
  (flatEquiv (K := K)).toLinearMap.comp (FiniteMonomials.reconstruct exponent)

def source (m L B s U : ℕ) (caps : ℕ → ℕ) : Submodule K (Jet (MvPolynomial (Fin 3) K)) :=
  (sourceMap (K := K) m L B s U caps).range

instance source_finite (m L B s U : ℕ) (caps : ℕ → ℕ) : FiniteDimensional K (source (K := K) m L B s U caps) := by
  unfold source
  infer_instance

theorem sourceMap_injective (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Function.Injective (sourceMap (K := K) m L B s U caps) :=
  (flatEquiv (K := K)).injective.comp
    (FiniteMonomials.reconstruct_injective _ (exponent_injective m L B s U caps))

theorem finrank_source (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Module.finrank K (source (K := K) m L B s U caps) = Fintype.card (Index m L B s U caps) := by
  unfold source
  rw [← (LinearEquiv.ofInjective (sourceMap (K := K) m L B s U caps)
    (sourceMap_injective m L B s U caps)).finrank_eq]
  simp

theorem mem_source_iff (m L B s U : ℕ) (caps : ℕ → ℕ) (P : Jet (MvPolynomial (Fin 3) K)) :
    P ∈ source (K := K) m L B s U caps ↔
      ∀ d ∈ ((flatEquiv (K := K)).symm P).support,
        Allowed m L B s d ∧ 2*d 1+d 3 ≤ B ∧ d 1+d 2+d 3 ≤ U ∧ d 1+d 2+d 3 ≤ caps (d 1) := by
  have hm : P ∈ source (K := K) m L B s U caps ↔
      (flatEquiv (K := K)).symm P ∈ (FiniteMonomials.reconstruct (K := K)
        (exponent (m := m) (L := L) (B := B) (s := s) (U := U) (caps := caps))).range := by
    constructor
    · rintro ⟨c,hc⟩
      refine ⟨c,?_⟩
      have h := congrArg (flatEquiv (K := K)).symm hc
      simpa [sourceMap] using h
    · rintro ⟨c,hc⟩
      refine ⟨c,?_⟩
      have h := congrArg (flatEquiv (K := K)) hc
      simpa [sourceMap] using h
  rw [hm, FiniteMonomials.mem_range_iff _ (exponent_injective m L B s U caps)]
  simp only [mem_range_exponent]

theorem truncated_weightedTerm_mem (m L B s U : ℕ) (caps : ℕ → ℕ)
    (r h a b : ℕ) (e : Fin 3 →₀ ℕ)
    (hi : e 0+a+b ≤ r) (hS : h+a ≤ s)
    (hB : 2*h+2*a+b+e 1-min a (e 1) ≤ B)
    (hU : e 0+e 1+h+a+b ≤ U)
    (hL : e 0+e 1+h+a+b+e 2 ≤ L)
    (hcaps : ∀ j, h ≤ j → j ≤ h+a → e 0+e 1+h+a+b ≤ caps j) :
    truncateOuter (K := K) m (SecondJetWeightedBasis.weightedTerm r h a b e) ∈
      source (K := K) m L B s U caps := by
  rw [← flatEquiv_weightedVector, ← flatEquiv_truncFlat, mem_source_iff]
  simp only [AlgEquiv.symm_apply_apply]
  intro d hd
  have ht := support_truncFlat m _ d hd
  obtain ⟨h0,hA,hR,hlo,hhi,hM,hT,hRS⟩ := weightedVector_support r h a b
    (e 0) (e 1) (e 2) (min a (e 1)) (min_le_left _ _) (min_le_right _ _) d ht.2
  refine ⟨?_,hRS.trans hB,hM.trans hU,hM.trans (hcaps (d 1) hlo hhi)⟩
  dsimp only [Allowed]
  exact ⟨ht.1,by omega,by omega,by omega,hT.trans hL⟩

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedSpace

end Compact_SecondJetRelaxedSpace
