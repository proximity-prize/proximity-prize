import ProximityPrize.SubmissionLower.Part.G025


section Compact_SecondJetGlobalMap
/-! Global interpolation from finite monomial families and the checked local
rank bound. Concrete coefficient counts and specialization are separate. -/
namespace ProximityPrize.SubmissionLower.SecondJetGlobalMap
open scoped BigOperators
open SecondJetSupport SecondJetBasis SecondJetGlobalSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K I N : Type*} [Field K] [Fintype I] [Fintype N]

def coefficientLocal (e : I → Fin 5 →₀ ℕ) (m : ℕ) (x u0 u1 : K) :
    (I → K) →ₗ[K] Jet (MvPolynomial (Fin 3) K) :=
  (truncateOuter (K := K) m).comp ((flatEquiv (K := K)).toLinearMap.comp
    ((localize x u0 u1).toLinearMap.comp (FiniteMonomials.reconstruct e)))

theorem coefficientLocal_mem (e : I → Fin 5 →₀ ℕ) (m L B s : ℕ) (x u0 u1 : K)
    (hB : ∀ i, e i 1+e i 3 ≤ B) (hs : ∀ i, e i 1 ≤ s)
    (hL : ∀ i, e i 1+e i 2+e i 3+e i 4 ≤ L) (c : I → K) :
    coefficientLocal e m x u0 u1 c ∈ SecondJetFacetSpace.source (K := K) m L B s := by
  change truncateOuter (K := K) m (flatEquiv (K := K)
    (localize x u0 u1 (FiniteMonomials.reconstruct e c))) ∈ _
  rw [FiniteMonomials.reconstruct_apply]
  simp_rw [map_sum]
  apply Submodule.sum_mem
  intro i _
  exact truncated_local_monomial_mem x u0 u1 m L B s (e i) (c i) (hB i) (hs i) (hL i)

theorem untruncate_contact {C : Type*} [CommRing C]
    (φ : Jet (MvPolynomial (Fin 3) K) →+* C) (t : C) (m : ℕ)
    (P : Jet (MvPolynomial (Fin 3) K)) (hε : φ Polynomial.X = t)
    (hP : t^m ∣ φ (truncateOuter (K := K) m P)) : t^m ∣ φ P := by
  have hd : t^m ∣ φ ((Polynomial.X^m : Jet (MvPolynomial (Fin 3) K)) *
      (P /ₘ Polynomial.X^m)) := by
    simp only [map_mul, map_pow, hε]
    exact dvd_mul_right _ _
  have heq := congrArg φ (Polynomial.modByMonic_add_div P (Polynomial.X^m))
  rw [map_add] at heq
  exact heq ▸ dvd_add hP hd

theorem exists_global_contact (e : I → Fin 5 →₀ ℕ) (he : Function.Injective e)
    (m L B s : ℕ) (hsB : s ≤ B) (hLm : m+B+s ≤ L)
    (hB : ∀ i, e i 1+e i 3 ≤ B) (hs : ∀ i, e i 1 ≤ s)
    (hL : ∀ i, e i 1+e i 2+e i 3+e i 4 ≤ L)
    (x u0 u1 : N → K)
    (hcard : Fintype.card N*SecondJetFacetCounts.rankBound m L B s < Fintype.card I) :
    ∃ P : Poly (K := K), P ≠ 0 ∧ (∀ d ∈ P.support, d ∈ Set.range e) ∧
      ∀ n, Polynomial.X^m ∣ SecondJetLocal.contact (K := K)
        (flatEquiv (K := K) (localize (x n) (u0 n) (u1 n) P)) := by
  classical
  let f := SecondJetFacetRank.restrictedMap (K := K) m L B s
  letI : AddCommGroup f.range := inferInstance
  letI : Module K f.range := f.range.module
  letI : FiniteDimensional K f.range := by
    change FiniteDimensional K (SecondJetFacetRank.restrictedMap (K := K) m L B s).range
    infer_instance
  let ell (n : N) : (I → K) →ₗ[K] SecondJetFacetSpace.source (K := K) m L B s :=
    (coefficientLocal e m (x n) (u0 n) (u1 n)).codRestrict _
      (coefficientLocal_mem e m L B s (x n) (u0 n) (u1 n) hB hs hL)
  let g : (I → K) →ₗ[K] (N → f.range) :=
    LinearMap.pi (fun n => f.rangeRestrict.comp (ell n))
  have hdim : Module.finrank K (N → f.range) ≤
      Fintype.card N*SecondJetFacetCounts.rankBound m L B s := by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    exact Nat.mul_le_mul_left _ (SecondJetFacetCounts.local_rank_le_count m L B s hsB hLm)
  have hrange := g.range.finrank_le
  have hsum := g.finrank_range_add_finrank_ker
  have hpos : 0 < Module.finrank K g.ker := by
    have hdimI : Module.finrank K (I → K) = Fintype.card I := by simp
    omega
  have hne : g.ker ≠ ⊥ := by
    intro h
    rw [h] at hpos
    simp at hpos
  obtain ⟨c,hc,hc0⟩ := (Submodule.ne_bot_iff _).mp hne
  have hcz : g c = 0 := LinearMap.mem_ker.mp hc
  refine ⟨FiniteMonomials.reconstruct e c,?_,?_,?_⟩
  · intro hz
    apply hc0
    apply FiniteMonomials.reconstruct_injective e he
    simpa only [map_zero] using hz
  · exact (FiniteMonomials.mem_range_iff e he _).mp ⟨c,rfl⟩
  · intro n
    have hz := congrArg Subtype.val (congrFun hcz n)
    change SecondJetRank.contactMap (K := K) m (coefficientLocal e m (x n) (u0 n) (u1 n) c) = 0 at hz
    have hd : Polynomial.X^m ∣ SecondJetLocal.contact (K := K)
        (coefficientLocal e m (x n) (u0 n) (u1 n) c) :=
      (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mp hz
    exact untruncate_contact (SecondJetLocal.contact (K := K)).toRingHom Polynomial.X m _
      SecondJetLocal.contact_X hd

end
end ProximityPrize.SubmissionLower.SecondJetGlobalMap

end Compact_SecondJetGlobalMap
