/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- 68.33 terminal specialization, derived from Lucieno PR 618, BitWonka PR 581 and Bome2017’s accepted 68.32 proof. Apache-2.0. -/
import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.K6833Residual

open scoped BigOperators
open SecondJetBasis SecondJetLocal

noncomputable section

set_option maxHeartbeats 500000

variable {K N : Type*} [Field K]

def lowerNodeSpace (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Submodule K (N → Target (K := K)) :=
  Submodule.pi Set.univ fun _ =>
    (SecondJetRelaxedRank.restrictedMap (K := K) m L B s (U-1) caps).range

theorem lowerNodeSpace_mem (m L B s U : ℕ) (caps : ℕ → ℕ)
    (Q : N → Target (K := K))
    (hQ : ∀ n, ∃ P : SecondJetRelaxedSpace.source (K := K) m L B s (U-1) caps,
      SecondJetRank.contactMap m (P : Jet (Base (K := K))) = Q n) :
    Q ∈ lowerNodeSpace m L B s U caps := by
  apply Submodule.mem_pi.mpr
  intro n _
  exact hQ n

private def piSpaceEquiv {V : Type*} [AddCommGroup V] [Module K V] (W : Submodule K V) :
    (Submodule.pi Set.univ (fun (_ : N) => W)) ≃ₗ[K] (N → W) where
  toFun Q n := ⟨Q.1 n, (Submodule.mem_pi.mp Q.2) n (Set.mem_univ n)⟩
  invFun Q := ⟨fun n => (Q n).1, Submodule.mem_pi.mpr (fun n _ => (Q n).2)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem piSpace_range_finite {A V : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup V] [Module K V] [Fintype N] (f : A →ₗ[K] V)
    (hA : FiniteDimensional K A) :
    FiniteDimensional K (Submodule.pi Set.univ (fun (_ : N) => f.range)) := by
  have := hA
  have := LinearMap.finiteDimensional_range f
  let equiv := piSpaceEquiv (N := N) f.range
  exact FiniteDimensional.of_injective equiv.toLinearMap equiv.injective

private theorem piSpace_range_rank {A V : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup V] [Module K V] [Fintype N] (f : A →ₗ[K] V)
    (hA : FiniteDimensional K A) :
    Module.finrank K (Submodule.pi Set.univ (fun (_ : N) => f.range)) =
      Fintype.card N * Module.finrank K f.range := by
  have := hA
  have := LinearMap.finiteDimensional_range f
  have : ∀ _ : N, Module.Free K f.range := fun _ => inferInstance
  have : ∀ _ : N, Module.Finite K f.range := fun _ => inferInstance
  rw [(piSpaceEquiv (N := N) f.range).finrank_eq, Module.finrank_pi_fintype]
  simp

instance lowerNodeSpace_finite [Fintype N] (m L B s U : ℕ) (caps : ℕ → ℕ) :
    FiniteDimensional K (lowerNodeSpace (K := K) (N := N) m L B s U caps) := by
  have h := piSpace_range_finite (N := N)
    (SecondJetRelaxedRank.restrictedMap (K := K) m L B s (U-1) caps)
    (SecondJetRelaxedSpace.source_finite (K := K) m L B s (U-1) caps)
  exact h

theorem lowerNodeSpace_rank [Fintype N] (m L B s U : ℕ) (caps : ℕ → ℕ) :
    Module.finrank K (lowerNodeSpace (K := K) (N := N) m L B s U caps) ≤
      Fintype.card N * SecondJetRelaxedGlobalMap.rankBound m L B s (U-1) caps := by
  unfold lowerNodeSpace
  rw [piSpace_range_rank (N := N)
    (SecondJetRelaxedRank.restrictedMap (K := K) m L B s (U-1) caps)
    (SecondJetRelaxedSpace.source_finite (K := K) m L B s (U-1) caps)]
  exact Nat.mul_le_mul_left _ (SecondJetRelaxedGlobalMap.local_rank_le_count (K := K)
    m L B s (U-1) caps)

end

end ProximityPrize.SubmissionLower.K6833Residual
