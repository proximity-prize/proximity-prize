import ProximityPrize.SubmissionLower.Part.G075


section Compact_SecondJetRelaxedGlobalMap
/-! Global interpolation from the clipped weighted local rank bound. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalMap
open scoped BigOperators
open SecondJetSupport SecondJetBasis SecondJetGlobalSupport
open SecondJetGlobalMap (coefficientLocal untruncate_contact)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K I N : Type*} [Field K] [Fintype I] [Fintype N]

def rankBound (m L B s U : ℕ) (caps : ℕ → ℕ) : ℕ :=
  Fintype.card (SecondJetRelaxedSpace.Index m L B s U caps) -
    ∑ r : Fin m, ∑ h : Fin (s+1),
      Fintype.card (SecondJetRelaxedRank.Block m L B s U caps r.val h.val)

theorem local_rank_le_count (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Module.finrank K (SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps).range ≤
      rankBound m L B s U caps := by
  have hh := SecondJetRelaxedRank.local_rank_bound (K := K) m L B s U caps
  unfold rankBound
  omega

theorem coefficientLocal_mem (e : I → Fin 5 →₀ ℕ) (m L B s U w : ℕ) (D : ℕ → ℕ)
    (hw : 2 ≤ w) (x u0 u1 : K)
    (hB : ∀ i, 2*e i 1+e i 3 ≤ B) (hs : ∀ i, e i 1 ≤ s)
    (hU : ∀ i, e i 1+e i 2+e i 3 ≤ U)
    (hL : ∀ i, e i 1+e i 2+e i 3+e i 4 ≤ L)
    (hD : ∀ i, e i 0+w*e i 2+(w-1)*e i 3+(w-2)*e i 1 < D (e i 1)) (c : I → K) :
    coefficientLocal e m x u0 u1 c ∈
      SecondJetRelaxedSpace.source (K := K) m L B s U (fun h => (D h+B-1)/w) := by
  change truncateOuter (K := K) m (flatEquiv (K := K)
    (localize x u0 u1 (FiniteMonomials.reconstruct e c))) ∈ _
  rw [FiniteMonomials.reconstruct_apply]
  simp_rw [map_sum]
  apply Submodule.sum_mem
  intro i _
  exact SecondJetRelaxedGlobalSupport.truncated_local_monomial_mem
    x u0 u1 m L B s U w D hw (e i) (c i) (hB i) (hs i) (hU i) (hL i) (hD i)

theorem exists_global_contact (e : I → Fin 5 →₀ ℕ) (he : Function.Injective e)
    (m L B s U w : ℕ) (D : ℕ → ℕ) (hw : 2 ≤ w)
    (hB : ∀ i, 2*e i 1+e i 3 ≤ B) (hs : ∀ i, e i 1 ≤ s)
    (hU : ∀ i, e i 1+e i 2+e i 3 ≤ U)
    (hL : ∀ i, e i 1+e i 2+e i 3+e i 4 ≤ L)
    (hD : ∀ i, e i 0+w*e i 2+(w-1)*e i 3+(w-2)*e i 1 < D (e i 1))
    (x u0 u1 : N → K)
    (hcard : Fintype.card N*rankBound m L B s U (fun h => (D h+B-1)/w) < Fintype.card I) :
    ∃ P : Poly (K := K), P ≠ 0 ∧ (∀ d ∈ P.support, d ∈ Set.range e) ∧
      ∀ n, Polynomial.X^m ∣ SecondJetLocal.contact (K := K)
        (flatEquiv (K := K) (localize (x n) (u0 n) (u1 n) P)) := by
  classical
  let caps := fun h => (D h+B-1)/w
  let f := SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps
  letI : AddCommGroup f.range := inferInstance
  letI : Module K f.range := f.range.module
  letI : FiniteDimensional K f.range := by
    change FiniteDimensional K (SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps).range
    infer_instance
  let ell (n : N) : (I → K) →ₗ[K] SecondJetRelaxedSpace.source (K := K) m L B s U caps :=
    (coefficientLocal e m (x n) (u0 n) (u1 n)).codRestrict _
      (coefficientLocal_mem e m L B s U w D hw (x n) (u0 n) (u1 n) hB hs hU hL hD)
  let g : (I → K) →ₗ[K] (N → f.range) :=
    LinearMap.pi (fun n => f.rangeRestrict.comp (ell n))
  have hdim : Module.finrank K (N → f.range) ≤ Fintype.card N*rankBound m L B s U caps := by
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    exact Nat.mul_le_mul_left _ (local_rank_le_count m L B s U caps)
  dsimp only [caps] at hdim
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
end ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalMap

end Compact_SecondJetRelaxedGlobalMap
