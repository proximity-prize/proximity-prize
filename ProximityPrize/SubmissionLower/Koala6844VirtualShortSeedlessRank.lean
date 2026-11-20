import ProximityPrize.SubmissionLower.Koala6844VirtualShortBasis


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetLocal
open SecondJetRelaxedSpace SecondJetRelaxedRank
open SecondJetWeightedBasis SecondJetWeightedSupport SecondJetWeightedLocal

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000

variable {K : Type*} [Field K]

abbrev SeedlessIndex (m B s U : ℕ) :=
  {i : SecondJetRelaxedSpace.Index m U B s U (fun _ => U) //
    SecondJetRelaxedSpace.exponent i 4 = 0}

private def seedlessExponent {m B s U : ℕ} (i : SeedlessIndex m B s U) : Fin 5 →₀ ℕ :=
  SecondJetRelaxedSpace.exponent i.val

private theorem seedlessExponent_injective (m B s U : ℕ) :
    Function.Injective (seedlessExponent (m := m) (B := B) (s := s) (U := U)) :=
  (SecondJetRelaxedSpace.exponent_injective m U B s U (fun _ => U)).comp Subtype.val_injective

def seedlessSourceMap (m B s U : ℕ) : (SeedlessIndex m B s U → K) →ₗ[K] Jet (Base (K := K)) :=
  (flatEquiv (K := K)).toLinearMap.comp (FiniteMonomials.reconstruct seedlessExponent)

def seedlessSource (m B s U : ℕ) : Submodule K (Jet (Base (K := K))) :=
  (seedlessSourceMap (K := K) m B s U).range

instance seedlessSource_finite (m B s U : ℕ) : FiniteDimensional K (seedlessSource (K := K) m B s U) := by
  unfold seedlessSource
  infer_instance

theorem seedlessSource_finrank (m B s U : ℕ) :
    Module.finrank K (seedlessSource (K := K) m B s U) = Fintype.card (SeedlessIndex m B s U) := by
  have hi : Function.Injective (seedlessSourceMap (K := K) m B s U) :=
    (flatEquiv (K := K)).injective.comp
      (FiniteMonomials.reconstruct_injective _ (seedlessExponent_injective m B s U))
  unfold seedlessSource
  rw [← (LinearEquiv.ofInjective (seedlessSourceMap (K := K) m B s U) hi).finrank_eq]
  simp

private theorem seedlessExponent_mem_range (m B s U : ℕ) (d : Fin 5 →₀ ℕ) :
    d ∈ Set.range (seedlessExponent (m := m) (B := B) (s := s) (U := U)) ↔
      d ∈ Set.range
        (SecondJetRelaxedSpace.exponent (m := m) (L := U) (B := B) (s := s)
          (U := U) (caps := fun _ => U)) ∧ d 4 = 0 := by
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨⟨i.val,rfl⟩,i.property⟩
  · rintro ⟨⟨i,rfl⟩,hz⟩
    exact ⟨⟨i,hz⟩,rfl⟩

theorem mem_seedlessSource (m B s U : ℕ) (P : Jet (Base (K := K))) :
    P ∈ seedlessSource (K := K) m B s U ↔
      P ∈ SecondJetRelaxedSpace.source (K := K) m U B s U (fun _ => U) ∧
        ∀ d ∈ ((flatEquiv (K := K)).symm P).support, d 4 = 0 := by
  have hm : P ∈ seedlessSource (K := K) m B s U ↔
      (flatEquiv (K := K)).symm P ∈ (FiniteMonomials.reconstruct (K := K)
        (seedlessExponent (m := m) (B := B) (s := s) (U := U))).range := by
    constructor
    · rintro ⟨c,hc⟩
      refine ⟨c,?_⟩
      have h := congrArg (flatEquiv (K := K)).symm hc
      simpa [seedlessSourceMap] using h
    · rintro ⟨c,hc⟩
      refine ⟨c,?_⟩
      have h := congrArg (flatEquiv (K := K)) hc
      simpa [seedlessSourceMap] using h
  rw [hm, FiniteMonomials.mem_range_iff _ (seedlessExponent_injective m B s U)]
  simp only [seedlessExponent_mem_range, forall_and,
    mem_source_iff, SecondJetRelaxedSpace.mem_range_exponent]

abbrev SeedlessKernelBlock (m B s U r h : ℕ) :=
  {e : SecondJetRelaxedRank.Block m U B s U (fun _ => U) r h // (e.val 2).val = 0}

private def kernelSeedlessExponent {m B s U r h : ℕ}
    (e : SeedlessKernelBlock m B s U r h) : Fin 3 →₀ ℕ :=
  SecondJetRelaxedRank.exponent e.val

private theorem kernelSeedlessExponent_injective (m B s U r h : ℕ) :
    Function.Injective (kernelSeedlessExponent (m := m) (B := B) (s := s)
      (U := U) (r := r) (h := h)) :=
  (SecondJetRelaxedRank.exponent_injective m U B s U (fun _ => U) r h).comp Subtype.val_injective

private theorem weightedTerm_seed_free (m r h a b : ℕ) (e : Fin 3 →₀ ℕ) (hz : e 2 = 0) :
    ∀ d ∈ ((flatEquiv (K := K)).symm
      (truncateOuter (K := K) m (weightedTerm (K := K) r h a b e))).support, d 4 = 0 := by
  rw [← flatEquiv_weightedVector, ← flatEquiv_truncFlat, AlgEquiv.symm_apply_apply]
  intro d hd
  have ht := support_truncFlat m _ d hd
  have hw := weightedVector_bound (K := K) ![0,0,0,0,1] r h a b
    (e 0) (e 1) (e 2) (min a (e 1)) d ht.2
  norm_num [weight, Fin.sum_univ_five, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, hz] at hw
  omega

private theorem kernelTerm_mem_seedlessSource (m B s U : ℕ) (r : Fin m)
    (h : Fin (s+1)) (e : SeedlessKernelBlock m B s U r.val h.val) :
    truncateOuter (K := K) m
      (weightedTerm (K := K) r.val h.val (a m s r.val h.val) (b m s r.val h.val)
        (kernelSeedlessExponent e)) ∈ seedlessSource (K := K) m B s U := by
  rw [mem_seedlessSource]
  have hzero : kernelSeedlessExponent e 2 = 0 := by
    simpa only [kernelSeedlessExponent, SecondJetRelaxedRank.exponent_apply] using e.property
  refine ⟨?_, weightedTerm_seed_free _ _ _ _ _ (kernelSeedlessExponent e) hzero⟩
  have hb := budgets m s r.val h.val (Nat.le_of_lt r.isLt) (Nat.le_of_lt_succ h.isLt)
  have he := e.val.property
  apply truncated_weightedTerm_mem
  · simp only [kernelSeedlessExponent, SecondJetRelaxedRank.exponent_apply]
    omega
  · exact hb.2.1
  · simp only [kernelSeedlessExponent, SecondJetRelaxedRank.exponent_apply]
    omega
  · simp only [kernelSeedlessExponent, SecondJetRelaxedRank.exponent_apply]
    omega
  · simp only [kernelSeedlessExponent, SecondJetRelaxedRank.exponent_apply]
    omega
  · intro j _ _
    simp only [kernelSeedlessExponent, SecondJetRelaxedRank.exponent_apply]
    omega

def seedlessContactMap (m B s U : ℕ) :
    seedlessSource (K := K) m B s U →ₗ[K] Target (K := K) :=
  (SecondJetRank.contactMap (K := K) m).comp (seedlessSource (K := K) m B s U).subtype

theorem seedless_local_rank_bound (m B s U : ℕ) :
    Module.finrank K (seedlessContactMap (K := K) m B s U).range +
      (∑ r : Fin m, ∑ h : Fin (s+1),
        Fintype.card (SeedlessKernelBlock m B s U r.val h.val)) ≤
      Fintype.card (SeedlessIndex m B s U) := by
  let am (r : Fin m) (h : Fin (s+1)) := a m s r.val h.val
  let bm (r : Fin m) (h : Fin (s+1)) := b m s r.val h.val
  let ex (r : Fin m) (h : Fin (s+1)) :
      SeedlessKernelBlock m B s U r.val h.val → Fin 3 →₀ ℕ := kernelSeedlessExponent
  have hW (p : Parameters (K := K)
      (I := fun r h => SeedlessKernelBlock m B s U r.val h.val)) :
      truncateOuter (K := K) m (weightedMake am bm ex p) ∈ seedlessSource (K := K) m B s U := by
    simp only [weightedMake_apply, map_sum, map_smul]
    apply Submodule.sum_mem
    intro r _
    apply Submodule.sum_mem
    intro h _
    apply Submodule.sum_mem
    intro e _
    apply Submodule.smul_mem
    exact kernelTerm_mem_seedlessSource m B s U r h e
  have hzero (p : Parameters (K := K)
      (I := fun r h => SeedlessKernelBlock m B s U r.val h.val)) :
      seedlessContactMap (K := K) m B s U ⟨truncateOuter (K := K) m (weightedMake am bm ex p), hW p⟩ = 0 := by
    change contact (K := K) (truncateOuter (K := K) m (weightedMake am bm ex p)) %ₘ Polynomial.X^m = 0
    apply (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mpr
    apply truncateOuter_contact (K := K) (contact (K := K)).toRingHom Polynomial.X m _ contact_X
    change Polynomial.X^m ∣ contact (K := K) _
    rw [weightedMake_apply, map_sum]
    apply Finset.dvd_sum
    intro r _
    rw [map_sum]
    apply Finset.dvd_sum
    intro h _
    rw [map_sum]
    apply Finset.dvd_sum
    intro e _
    rw [map_smul, Algebra.smul_def]
    apply dvd_mul_of_dvd_right
    apply weightedTerm_vanishes
    exact le_of_eq (budgets m s r.val h.val (Nat.le_of_lt r.isLt)
      (Nat.le_of_lt_succ h.isLt)).2.2.symm
  have h := finite_source_rank (seedlessSource (K := K) m B s U)
    (seedlessContactMap (K := K) m B s U) am bm ex
    (fun r h => kernelSeedlessExponent_injective m B s U r.val h.val) hW hzero
  rwa [seedlessSource_finrank] at h

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
