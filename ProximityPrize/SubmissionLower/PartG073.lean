import ProximityPrize.SubmissionLower.PartG072


section Compact_SecondJetRelaxedRank
/-! A rank bound for the clipped second-jet space using the independent U/J/V
family. Its finite cardinalities are explicit; numerical receipts are separate. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedRank
open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetLocal SecondJetRelaxedSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

def q (m s r h : ℕ) := max ((m-r+1)/2) (m-r-(s-h))
def a (m s r h : ℕ) := m-r-q m s r h
def b (m s r h : ℕ) := q m s r h-a m s r h

theorem budgets (m s r h : ℕ) (hr : r ≤ m) (hh : h ≤ s) :
    a m s r h+b m s r h = q m s r h ∧ h+a m s r h ≤ s ∧
      r+2*a m s r h+b m s r h = m := by
  dsimp [a,b,q]
  omega

def Block (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ) :=
  {e : Fin 3 → Fin (L+1) //
    (e 0).val+q m s r h ≤ r ∧ (e 1).val+q m s r h+2*h ≤ B ∧
    m-r+2*h ≤ B ∧ (e 0).val+(e 1).val+h+q m s r h ≤ U ∧
    (e 0).val+(e 1).val+h+q m s r h+(e 2).val ≤ L ∧
    ∀ j : Fin (a m s r h+1),
      (e 0).val+(e 1).val+h+q m s r h ≤ caps (h+j.val)}

instance (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ) :
    Fintype (Block m L B s U caps r h) := by
  unfold Block
  infer_instance

def exponent {m L B s U : ℕ} {caps : ℕ → ℕ} {r h : ℕ}
    (e : Block m L B s U caps r h) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => (e.val j).val)

@[simp] theorem exponent_apply {m L B s U : ℕ} {caps : ℕ → ℕ} {r h : ℕ}
    (e : Block m L B s U caps r h) (j : Fin 3) : exponent e j = (e.val j).val := by
  simp [exponent]

theorem exponent_injective (m L B s U : ℕ) (caps : ℕ → ℕ) (r h : ℕ) :
    Function.Injective (exponent (m := m) (L := L) (B := B) (s := s) (U := U)
      (caps := caps) (r := r) (h := h)) := by
  intro e f hef
  apply Subtype.ext
  funext j
  apply Fin.ext
  simpa only [exponent_apply] using congrArg (fun g : Fin 3 →₀ ℕ => g j) hef

abbrev Parameters (m L B s U : ℕ) (caps : ℕ → ℕ) :=
  ∀ r : Fin m, ∀ h : Fin (s+1), Block m L B s U caps r.val h.val → K

def make (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Parameters (K := K) m L B s U caps →ₗ[K] Jet (Base (K := K)) :=
  (truncateOuter (K := K) m).comp (SecondJetWeightedBasis.weightedMake
    (fun r h => a m s r.val h.val) (fun r h => b m s r.val h.val)
    (fun _ _ => exponent))

theorem make_mem_source (m L B s U : ℕ) (caps : ℕ → ℕ)
    (p : Parameters (K := K) m L B s U caps) :
    make m L B s U caps p ∈ source (K := K) m L B s U caps := by
  simp only [make, LinearMap.comp_apply, SecondJetWeightedBasis.weightedMake_apply, map_sum, map_smul]
  apply Submodule.sum_mem
  intro r _
  apply Submodule.sum_mem
  intro h _
  apply Submodule.sum_mem
  intro e _
  apply Submodule.smul_mem
  have hb := budgets m s r.val h.val (Nat.le_of_lt r.isLt) (Nat.le_of_lt_succ h.isLt)
  have he := e.property
  apply truncated_weightedTerm_mem
  · simp only [exponent_apply]
    omega
  · exact hb.2.1
  · simp only [exponent_apply]
    omega
  · simp only [exponent_apply]
    omega
  · simp only [exponent_apply]
    omega
  · intro j hj hj'
    have hd := he.2.2.2.2.2 (⟨j-h.val, by omega⟩ : Fin (a m s r.val h.val+1))
    simp only [exponent_apply]
    dsimp at hd
    have hjj : h.val+(j-h.val)=j := by omega
    rw [hjj] at hd
    omega

def restrictedMap (m L B s U : ℕ) (caps : ℕ → ℕ) :
    source (K := K) m L B s U caps →ₗ[K] Target (K := K) :=
  (SecondJetRank.contactMap (K := K) m).comp (source (K := K) m L B s U caps).subtype

theorem make_zero (m L B s U : ℕ) (caps : ℕ → ℕ)
    (p : Parameters (K := K) m L B s U caps) :
    SecondJetRank.contactMap (K := K) m (make m L B s U caps p) = 0 := by
  change contact (K := K) (make m L B s U caps p) %ₘ Polynomial.X^m = 0
  apply (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mpr
  change Polynomial.X^m ∣ contact (K := K) (truncateOuter (K := K) m _)
  apply truncateOuter_contact (K := K) (contact (K := K)).toRingHom Polynomial.X m _ contact_X
  change Polynomial.X^m ∣ contact (K := K) _
  rw [SecondJetWeightedBasis.weightedMake_apply, map_sum]
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
  apply SecondJetWeightedLocal.weightedTerm_vanishes
  exact le_of_eq (budgets m s r.val h.val (Nat.le_of_lt r.isLt)
    (Nat.le_of_lt_succ h.isLt)).2.2.symm

theorem local_rank_bound (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Module.finrank K (restrictedMap (K := K) m L B s U caps).range +
      (∑ r : Fin m, ∑ h : Fin (s+1), Fintype.card (Block m L B s U caps r.val h.val)) ≤
        Fintype.card (Index m L B s U caps) := by
  have h := SecondJetWeightedBasis.finite_source_rank
    (source (K := K) m L B s U caps) (restrictedMap (K := K) m L B s U caps)
    (fun r h => a m s r.val h.val) (fun r h => b m s r.val h.val)
    (fun _ _ => exponent) (fun r h => exponent_injective m L B s U caps r.val h.val)
    (make_mem_source m L B s U caps) (make_zero m L B s U caps)
  rwa [finrank_source] at h

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedRank

end Compact_SecondJetRelaxedRank
