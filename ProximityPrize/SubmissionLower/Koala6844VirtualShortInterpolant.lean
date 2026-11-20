import ProximityPrize.SubmissionLower.Koala6844VirtualShortBasis
import ProximityPrize.SubmissionLower.Koala6844VirtualShortElimination


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetSupport SecondJetBasis SecondJetGlobalSupport

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000

variable {K N : Type*} [Field K]

private abbrev Aux (K : Type*) [Field K] := Polynomial (Poly (K := K))

def clearAuxLinear (A B : Poly (K := K)) (q : ℕ) : Aux K →ₗ[K] Poly (K := K) where
  toFun := clearAux A B q
  map_add' := clearAux_add A B q
  map_smul' := by
    intro c P
    simp [clearAux, Polynomial.coeff_smul, Finset.smul_sum]

def normalizedContactMap (D : ℕ → ℕ) (w wQ L B s U q m : ℕ)
    (den num : Poly (K := K)) (x u0 u1 : K) :
    (NormalizedIndex D w wQ L B s U q → K) →ₗ[K] SecondJetLocal.Target (K := K) :=
  (SecondJetRank.contactMap (K := K) m).comp
    ((flatEquiv (K := K)).toLinearMap.comp ((localize x u0 u1).toLinearMap.comp
      ((clearAuxLinear den num q).comp (reconstructNormalized D w wQ L B s U q))))

theorem exists_normalized_global_contact [Fintype N]
    (D : ℕ → ℕ) (w wQ L B s U q m localRank : ℕ)
    (hsB : 2*s ≤ B) (hUL : U ≤ L) (hqU : q ≤ U)
    (den num : Poly (K := K)) (x u0 u1 : N → K)
    (a₀ a₁ b₀ b₁ : MvPolynomial (Fin 4) K)
    (hA : asSeed 4 den = Polynomial.C a₀ + Polynomial.C a₁ * Polynomial.X)
    (hB : asSeed 4 num = Polynomial.C b₀ + Polynomial.C b₁ * Polynomial.X)
    (ha : a₁ ≠ 0) (hc : a₁*b₀ ≠ a₀*b₁)
    (hlocal : ∀ i, Module.finrank K
      (normalizedContactMap D w wQ L B s U q m den num (x i) (u0 i) (u1 i)).range ≤ localRank)
    (hgap : Fintype.card N * localRank < Fintype.card (NormalizedIndex D w wQ L B s U q)) :
    ∃ P : Aux K, P.natDegree ≤ q ∧ clearAux den num q P ≠ 0 ∧
      (∀ j e, e ∈ (P.coeff j).support →
        2*e 1+e 3 ≤ B ∧ e 1 ≤ s ∧ e 1+e 2+e 3+j ≤ U ∧ e 1+e 2+e 3+e 4 ≤ L ∧
          e 0+w*e 2+(w-1)*e 3+(w-2)*e 1+wQ*j < D (e 1) ∧ (0 < j → e 4 = 0)) ∧
      ∀ i, Polynomial.X^m ∣ SecondJetLocal.contact (K := K)
        (flatEquiv (K := K) (localize (x i) (u0 i) (u1 i) (clearAux den num q P))) := by
  classical
  let f i := normalizedContactMap D w wQ L B s U q m den num (x i) (u0 i) (u1 i)
  letI : ∀ i, AddCommGroup (f i).range := fun _ => inferInstance
  letI : ∀ i, Module K (f i).range := fun i => (f i).range.module
  letI : ∀ i, FiniteDimensional K (f i).range := fun i => by
    change FiniteDimensional K (normalizedContactMap D w wQ L B s U q m den num (x i) (u0 i) (u1 i)).range
    infer_instance
  letI : ∀ i, Module.Free K (f i).range := fun _ => inferInstance
  let g : (NormalizedIndex D w wQ L B s U q → K) →ₗ[K] (∀ i, (f i).range) :=
    LinearMap.pi fun i => (f i).rangeRestrict
  have hdim : Module.finrank K (∀ i, (f i).range) ≤ Fintype.card N * localRank := by
    rw [Module.finrank_pi_fintype]
    calc
      _ ≤ ∑ _ : N, localRank := Finset.sum_le_sum (fun i _ => hlocal i)
      _ = _ := by simp
  have hrange := g.range.finrank_le
  have hsum := g.finrank_range_add_finrank_ker
  have hsource : Module.finrank K (NormalizedIndex D w wQ L B s U q → K) =
      Fintype.card (NormalizedIndex D w wQ L B s U q) := by simp
  have hpos : 0 < Module.finrank K g.ker := by omega
  have hne : g.ker ≠ ⊥ := by
    intro h
    rw [h] at hpos
    simp at hpos
  obtain ⟨c, hcg, hcn⟩ := (Submodule.ne_bot_iff _).mp hne
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
  have hclear : clearAux den num q P ≠ 0 := by
    exact clearAux_ne_zero_mv den num a₀ a₁ b₀ b₁ q hA hB ha hc P hP hq
      (fun j hj e he => (hsupp j e he).2.2.2.2.2.2 hj)
  refine ⟨P, hq, hclear, (fun j e he => (hsupp j e he).2), ?_⟩
  intro i
  have hz := congrArg Subtype.val (congrFun (LinearMap.mem_ker.mp hcg) i)
  change SecondJetRank.contactMap (K := K) m (flatEquiv (K := K)
    (localize (x i) (u0 i) (u1 i) (clearAux den num q P))) = 0 at hz
  exact (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow m)).mp hz

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
