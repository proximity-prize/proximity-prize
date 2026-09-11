import ProximityPrize.SubmissionLower.Part.G021


section Compact_SecondJetRank
/-! Finite independent kernel vectors for the local second-jet contact map. -/
namespace ProximityPrize.SubmissionLower.SecondJetRank
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetLocal SecondJetSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K : Type*} [Field K]

def q (m s2 r h : ℕ) := max ((m-r+1)/2) (m-r-(s2-h))
def a (m s2 r h : ℕ) := min (q m s2 r h) (s2-h)
def b (m s2 r h : ℕ) := q m s2 r h-a m s2 r h

theorem budgets (m s2 r h : ℕ) (hr : r ≤ m) (hh : h ≤ s2) :
    a m s2 r h+b m s2 r h=q m s2 r h ∧ h+a m s2 r h ≤ s2 ∧
      m ≤ r+2*a m s2 r h+b m s2 r h :=
  exponent_budget m r s2 h hr hh

def Block (m L s1 s2 r h : ℕ) :=
  {d : Fin 3 → Fin (L+1) //
    (d 0).val+q m s2 r h ≤ r ∧ (d 1).val+q m s2 r h ≤ s1 ∧
      (d 0).val+(d 1).val+(d 2).val+h+q m s2 r h ≤ L}

instance (m L s1 s2 r h : ℕ) : Fintype (Block m L s1 s2 r h) := by
  unfold Block
  infer_instance

def blockExponent {m L s1 s2 r h : ℕ} (d : Block m L s1 s2 r h) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => (d.val k).val)

@[simp] theorem blockExponent_apply {m L s1 s2 r h : ℕ}
    (d : Block m L s1 s2 r h) (k : Fin 3) : blockExponent d k = (d.val k).val := by
  simp [blockExponent]

theorem blockExponent_injective (m L s1 s2 r h : ℕ) :
    Function.Injective (blockExponent (m := m) (L := L) (s1 := s1) (s2 := s2) (r := r) (h := h)) := by
  intro d e hde
  apply Subtype.ext
  funext k
  apply Fin.ext
  simpa only [blockExponent_apply] using congrArg (fun f : Fin 3 →₀ ℕ => f k) hde

abbrev Parameters (m L s1 s2 : ℕ) :=
  ∀ r : Fin m, ∀ h : Fin (s2+1), Block m L s1 s2 r.val h.val → K

def embed (m L s1 s2 : ℕ) : Parameters (K := K) m L s1 s2 →ₗ[K]
    (Fin m → Fin (s2+1) → Base (K := K)) :=
  LinearMap.pi (fun r => LinearMap.pi (fun h =>
    (FiniteMonomials.reconstruct blockExponent).comp
      ((LinearMap.proj h : (∀ h : Fin (s2+1), Block m L s1 s2 r.val h.val → K) →ₗ[K]
        (Block m L s1 s2 r.val h.val → K)).comp (LinearMap.proj r))))

theorem embed_apply (m L s1 s2 : ℕ) (p : Parameters (K := K) m L s1 s2)
    (r : Fin m) (h : Fin (s2+1)) :
    embed m L s1 s2 p r h = FiniteMonomials.reconstruct blockExponent (p r h) := rfl

theorem embed_injective (m L s1 s2 : ℕ) : Function.Injective (embed (K := K) m L s1 s2) := by
  intro p z hpz
  funext r h d
  have he := congrFun (congrFun hpz r) h
  have hh := FiniteMonomials.reconstruct_injective blockExponent
    (blockExponent_injective m L s1 s2 r.val h.val) he
  exact congrFun hh d

theorem block_monomial (m L s1 s2 r h : ℕ) (d : Block m L s1 s2 r h) :
    MvPolynomial.monomial (blockExponent d) (1 : K) =
      MvPolynomial.X 0^(d.val 0).val * MvPolynomial.X 1^(d.val 1).val *
        MvPolynomial.X 2^(d.val 2).val := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp [Fin.prod_univ_three]
  · intro i
    simp

def make (m L s1 s2 : ℕ) : Parameters (K := K) m L s1 s2 →ₗ[K] Jet (Base (K := K)) :=
  ((truncateOuter (K := K) m).comp (pack (K := K) SecondJetLocal.v
    (fun r h => a m s2 r.val h.val) (fun r h => b m s2 r.val h.val))).comp (embed m L s1 s2)

theorem make_mem_source (m L s1 s2 : ℕ) (p : Parameters (K := K) m L s1 s2) :
    make m L s1 s2 p ∈ source (K := K) m L s1 s2 := by
  change truncateOuter (K := K) m (pack (K := K) SecondJetLocal.v _ _ (embed m L s1 s2 p)) ∈ _
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
  have hb := budgets m s2 r.val h.val (Nat.le_of_lt r.isLt) (Nat.le_of_lt_succ h.isLt)
  have hd := d.property
  apply truncated_monomial_term_mem
  · omega
  · omega
  · exact hb.2.1
  · have hd := d.property.2.2
    omega


def contactMap (m : ℕ) : Jet (Base (K := K)) →ₗ[K] Target (K := K) :=
  ((Polynomial.modByMonicHom (Polynomial.X^m : Target (K := K))).restrictScalars K).comp
    (contact (K := K)).toLinearMap

def restrictedMap (m L s1 s2 : ℕ) : source (K := K) m L s1 s2 →ₗ[K] Target (K := K) :=
  (contactMap (K := K) m).comp (source (K := K) m L s1 s2).subtype

theorem make_zero (m L s1 s2 : ℕ) (p : Parameters (K := K) m L s1 s2) :
    contactMap (K := K) m (make m L s1 s2 p) = 0 := by
  change (contact (K := K) (make m L s1 s2 p)) %ₘ Polynomial.X^m = 0
  apply (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mpr
  change Polynomial.X^m ∣ contact (K := K)
    (truncateOuter (K := K) m (pack (K := K) SecondJetLocal.v _ _ (embed m L s1 s2 p)))
  apply truncateOuter_contact (K := K) (contact (K := K)).toRingHom Polynomial.X m _ contact_X
  rw [pack_apply, map_sum]
  apply Finset.dvd_sum
  intro r _
  rw [map_sum]
  apply Finset.dvd_sum
  intro h _
  exact term_vanishes m r.val h.val _ _ _
    (budgets m s2 r.val h.val (Nat.le_of_lt r.isLt) (Nat.le_of_lt_succ h.isLt)).2.2

/-- An explicit finite-family upper bound on the local contact rank. The
cardinalities can subsequently be replaced by closed arithmetic sums. -/
theorem local_rank_bound (m L s1 s2 : ℕ) :
    Module.finrank K (restrictedMap (K := K) m L s1 s2).range +
      (∑ r : Fin m, ∑ h : Fin (s2+1), Fintype.card (Block m L s1 s2 r.val h.val)) ≤
        Fintype.card (Index m L s1 s2) := by
  have h := finite_source_rank (source (K := K) m L s1 s2)
    (restrictedMap (K := K) m L s1 s2) SecondJetLocal.v (v_ne_zero (K := K))
    (fun r h => a m s2 r.val h.val) (fun r h => b m s2 r.val h.val)
    (embed m L s1 s2) (embed_injective m L s1 s2)
    (make_mem_source m L s1 s2) (make_zero m L s1 s2)
  rw [finrank_source] at h
  simpa [Parameters, Module.finrank_pi_fintype] using h

end
end ProximityPrize.SubmissionLower.SecondJetRank

end Compact_SecondJetRank
