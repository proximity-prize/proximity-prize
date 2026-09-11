import ProximityPrize.SubmissionLower.PartG022


section Compact_SecondJetFacetRank
/-! Local rank saving with a shared R/S degree cap. -/
namespace ProximityPrize.SubmissionLower.SecondJetFacetRank
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetLocal SecondJetFacetSpace
open SecondJetRank (q a b budgets Block blockExponent blockExponent_injective block_monomial contactMap)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

abbrev Parameters (m L B s : ℕ) :=
  ∀ r : Fin m, ∀ h : Fin (s+1), Block m L (B-h.val) s r.val h.val → K

def embed (m L B s : ℕ) : Parameters (K := K) m L B s →ₗ[K]
    (Fin m → Fin (s+1) → Base (K := K)) :=
  LinearMap.pi (fun r => LinearMap.pi (fun h =>
    (FiniteMonomials.reconstruct blockExponent).comp
      ((LinearMap.proj h : (∀ h : Fin (s+1), Block m L (B-h.val) s r.val h.val → K) →ₗ[K]
        (Block m L (B-h.val) s r.val h.val → K)).comp (LinearMap.proj r))))

theorem embed_apply (m L B s : ℕ) (p : Parameters (K := K) m L B s)
    (r : Fin m) (h : Fin (s+1)) :
    embed m L B s p r h = FiniteMonomials.reconstruct blockExponent (p r h) := rfl

theorem embed_injective (m L B s : ℕ) : Function.Injective (embed (K := K) m L B s) := by
  intro p z hpz
  funext r h d
  have he := congrFun (congrFun hpz r) h
  have hh := FiniteMonomials.reconstruct_injective blockExponent
    (blockExponent_injective m L (B-h.val) s r.val h.val) he
  exact congrFun hh d

def make (m L B s : ℕ) : Parameters (K := K) m L B s →ₗ[K] Jet (Base (K := K)) :=
  ((truncateOuter (K := K) m).comp (pack (K := K) SecondJetLocal.v
    (fun r h => a m s r.val h.val) (fun r h => b m s r.val h.val))).comp (embed m L B s)

theorem make_mem_source (m L B s : ℕ) (hsB : s ≤ B) (p : Parameters (K := K) m L B s) :
    make m L B s p ∈ source (K := K) m L B s := by
  change truncateOuter (K := K) m (pack (K := K) SecondJetLocal.v _ _ (embed m L B s p)) ∈ _
  simp_rw [pack_apply, map_sum, embed_apply, FiniteMonomials.reconstruct_apply, map_sum]
  apply Submodule.sum_mem
  intro r _
  apply Submodule.sum_mem
  intro h _
  apply Submodule.sum_mem
  intro d _
  have hs : MvPolynomial.monomial (blockExponent d) (p r h d) =
      (p r h d) • MvPolynomial.monomial (blockExponent d) (1 : K) := by
    simpa only [smul_eq_mul, mul_one] using
      (map_smul (MvPolynomial.monomial (blockExponent d)) (p r h d) (1 : K))
  rw [hs, map_smul, map_smul]
  apply Submodule.smul_mem
  rw [block_monomial]
  have hb := budgets m s r.val h.val (Nat.le_of_lt r.isLt) (Nat.le_of_lt_succ h.isLt)
  have hd := d.property
  have hh : h.val ≤ B := (Nat.le_of_lt_succ h.isLt).trans hsB
  apply truncated_monomial_term_mem
  · omega
  · omega
  · exact hb.2.1
  · omega

def restrictedMap (m L B s : ℕ) : source (K := K) m L B s →ₗ[K] Target (K := K) :=
  (contactMap (K := K) m).comp (source (K := K) m L B s).subtype

theorem make_zero (m L B s : ℕ) (p : Parameters (K := K) m L B s) :
    contactMap (K := K) m (make m L B s p) = 0 := by
  change (contact (K := K) (make m L B s p)) %ₘ Polynomial.X^m = 0
  apply (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mpr
  change Polynomial.X^m ∣ contact (K := K)
    (truncateOuter (K := K) m (pack (K := K) SecondJetLocal.v _ _ (embed m L B s p)))
  apply truncateOuter_contact (K := K) (contact (K := K)).toRingHom Polynomial.X m _ contact_X
  rw [pack_apply, map_sum]
  apply Finset.dvd_sum
  intro r _
  rw [map_sum]
  apply Finset.dvd_sum
  intro h _
  exact term_vanishes m r.val h.val _ _ _
    (budgets m s r.val h.val (Nat.le_of_lt r.isLt) (Nat.le_of_lt_succ h.isLt)).2.2

theorem local_rank_bound (m L B s : ℕ) (hsB : s ≤ B) :
    Module.finrank K (restrictedMap (K := K) m L B s).range +
      (∑ r : Fin m, ∑ h : Fin (s+1), Fintype.card (Block m L (B-h.val) s r.val h.val)) ≤
        Fintype.card (Index m L B s) := by
  have h := finite_source_rank (source (K := K) m L B s)
    (restrictedMap (K := K) m L B s) SecondJetLocal.v (v_ne_zero (K := K))
    (fun r h => a m s r.val h.val) (fun r h => b m s r.val h.val)
    (embed m L B s) (embed_injective m L B s)
    (make_mem_source m L B s hsB) (make_zero m L B s)
  rw [finrank_source] at h
  simpa [Parameters, Module.finrank_pi_fintype] using h

end
end ProximityPrize.SubmissionLower.SecondJetFacetRank

end Compact_SecondJetFacetRank
