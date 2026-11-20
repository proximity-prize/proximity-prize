import ProximityPrize.SubmissionLower.Koala6844VirtualShortInterpolant

namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetSupport SecondJetBasis SecondJetGlobalSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {K N : Type*} [Field K]

def jointContactMap (D : ℕ → ℕ) (w wQ L B s U q m : ℕ)
    (den num : Poly (K := K)) (x u0 u1 : N → K) :
    (NormalizedIndex D w wQ L B s U q → K) →ₗ[K]
      ∀ i, (normalizedContactMap D w wQ L B s U q m den num (x i) (u0 i) (u1 i)).range :=
  LinearMap.pi fun i => (normalizedContactMap D w wQ L B s U q m den num
    (x i) (u0 i) (u1 i)).rangeRestrict

theorem normalizedContactKernel_finrank [Fintype N]
    (D : ℕ → ℕ) (w wQ L B s U q m localRank : ℕ)
    (den num : Poly (K := K)) (x u0 u1 : N → K)
    (hlocal : ∀ i, Module.finrank K
      (normalizedContactMap D w wQ L B s U q m den num (x i) (u0 i) (u1 i)).range ≤ localRank) :
    Fintype.card (NormalizedIndex D w wQ L B s U q) - Fintype.card N * localRank ≤
      Module.finrank K (jointContactMap D w wQ L B s U q m den num x u0 u1).ker := by
  classical
  let f i := normalizedContactMap D w wQ L B s U q m den num (x i) (u0 i) (u1 i)
  letI : ∀ i, AddCommGroup (f i).range := fun _ => inferInstance
  letI : ∀ i, Module K (f i).range := fun i => (f i).range.module
  letI : ∀ i, FiniteDimensional K (f i).range := fun i => by
    change FiniteDimensional K (normalizedContactMap D w wQ L B s U q m den num (x i) (u0 i) (u1 i)).range
    infer_instance
  letI : ∀ i, Module.Free K (f i).range := fun _ => inferInstance
  let g := jointContactMap D w wQ L B s U q m den num x u0 u1
  have hdim : Module.finrank K (∀ i, (f i).range) ≤ Fintype.card N * localRank := by
    rw [Module.finrank_pi_fintype]
    calc
      _ ≤ ∑ _ : N, localRank := Finset.sum_le_sum (fun i _ => hlocal i)
      _ = _ := by simp
  have hrange : Module.finrank K g.range ≤ Module.finrank K (∀ i, (f i).range) :=
    g.range.finrank_le
  have hsum := g.finrank_range_add_finrank_ker
  have hsource : Module.finrank K (NormalizedIndex D w wQ L B s U q → K) =
      Fintype.card (NormalizedIndex D w wQ L B s U q) := by simp
  change _ ≤ Module.finrank K g.ker
  omega

theorem normalizedContactKernel_contact
    (D : ℕ → ℕ) (w wQ L B s U q m : ℕ) (den num : Poly (K := K)) (x u0 u1 : N → K)
    (c : (jointContactMap D w wQ L B s U q m den num x u0 u1).ker) (i : N) :
    Polynomial.X^m ∣ SecondJetLocal.contact (K := K)
      (flatEquiv (K := K) (localize (x i) (u0 i) (u1 i)
        (clearAux den num q (reconstructNormalized D w wQ L B s U q c.val)))) := by
  have hz := congrArg Subtype.val (congrFun (LinearMap.mem_ker.mp c.property) i)
  change SecondJetRank.contactMap (K := K) m (flatEquiv (K := K)
    (localize (x i) (u0 i) (u1 i)
      (clearAux den num q (reconstructNormalized D w wQ L B s U q c.val)))) = 0 at hz
  exact (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mp hz

theorem normalizedClearing_injective
    (D : ℕ → ℕ) (w wQ L B s U q : ℕ) (hsB : 2*s ≤ B) (hUL : U ≤ L) (hqU : q ≤ U)
    (den num : Poly (K := K)) (a₀ a₁ b₀ b₁ : MvPolynomial (Fin 4) K)
    (hA : asSeed 4 den = Polynomial.C a₀ + Polynomial.C a₁ * Polynomial.X)
    (hB : asSeed 4 num = Polynomial.C b₀ + Polynomial.C b₁ * Polynomial.X)
    (ha : a₁ ≠ 0) (hc : a₁*b₀ ≠ a₀*b₁) :
    Function.Injective ((clearAuxLinear den num q).comp (reconstructNormalized D w wQ L B s U q)) := by
  classical
  apply (LinearMap.ker_eq_bot.mp ?_)
  rw [Submodule.eq_bot_iff]
  intro c hker
  by_contra hcn
  let P := reconstructNormalized (K := K) D w wQ L B s U q c
  have hP : P ≠ 0 := by
    intro hp
    apply hcn
    apply reconstructNormalized_injective (K := K) D w wQ L B s U q
    simpa only [map_zero] using hp
  have hsupp (j e) (he : e ∈ (P.coeff j).support) :=
    reconstructed_normalized_bounds D w wQ L B s U q hsB hUL hqU c j e he
  have hq : P.natDegree ≤ q := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    by_contra hj'
    have he : (P.coeff j).support.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (fun h => hj' (MvPolynomial.support_eq_empty.mp h))
    obtain ⟨e, he⟩ := he
    exact (not_le_of_gt hj) (hsupp j e he).1
  have hclear := clearAux_ne_zero_mv den num a₀ a₁ b₀ b₁ q hA hB ha hc P hP hq
    (fun j hj e he => (hsupp j e he).2.2.2.2.2.2 hj)
  exact hclear (LinearMap.mem_ker.mp hker)

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
