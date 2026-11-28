import ProximityPrize.SubmissionLower.Z6970ExpandedPrimarySupport
import ProximityPrize.SubmissionLower.Z6970ExpandedNodeRank

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3000000

namespace ExpandedWidePrimary6970

noncomputable section

open K1_13 (Geom Row Shape shape InBox Contact embed)
open K1_13_2 (Local toRow)
open P3 (I K node)
open ExpandedPrimary6970 (nodeMap wordMap row_bounds primaryBox TrueWeightLE JetsBounded contact_of_word_kernel)
open ExpandedColumns6970
open ExpandedTaper6970 (BlockIndex debit)
open scoped BigOperators
open ExpandedPrimary6970 (local_range_finite)
open P0_9_2 (map_independent_family)

open PolynomialDifferential ReedSolomon.HiddenDerivative

private theorem sumConstant {ι : Type*} [Fintype ι] (n : ℕ) :
    (∑ _ : ι, n) = Fintype.card ι * n := by
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]

theorem word_rank (A D : ℕ) (hD : 3<D) (w : I → K) :
    Module.finrank Geom (LinearMap.range (wordMap A D w)) ≤ 262144 * rankCharge := by
  letI : Fact (3<D) := ⟨hD⟩
  let nmap (i : I) := nodeMap (A:=A) (D:=D) (embed (node i)) (embed (w i))
  let B (i : I) := LinearMap.range (nmap i)
  let f : Source A D →ₗ[Geom] (∀ i, B i) := LinearMap.pi fun i => (nmap i).rangeRestrict
  let g : (∀ i, B i) →ₗ[Geom] (I → Local) :=
    LinearMap.pi fun i => (B i).subtype.comp (LinearMap.proj i)
  have hw : wordMap A D w = g.comp f := rfl
  rw [hw]
  calc
    _ ≤ Module.finrank Geom (LinearMap.range g) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range f g)
    _ ≤ Module.finrank Geom (∀ i, B i) := g.finrank_range_le
    _ = ∑ i, Module.finrank Geom (B i) := Module.finrank_pi_fintype Geom
    _ ≤ ∑ _ : I, rankCharge := Finset.sum_le_sum fun i _ => rank_at_position _ _
    _ = _ := by
      have hc : Fintype.card I = 262144 := Fintype.card_fin _
      exact (sumConstant (ι := I) rankCharge).trans
        (congrArg (fun n : ℕ => n*rankCharge) hc)

end
end ExpandedWidePrimary6970
