import ProximityPrize.SubmissionLower.Z6970ExpandedWordRank
import ProximityPrize.SubmissionLower.Z6970ExpandedColumnsExact

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

noncomputable def sourceRank (A D : ℕ) : ℕ := (3000*A*427286700047 + 528262870825850 - D*1015009542543574) - 262144 * rankCharge

noncomputable def layerNeed (A D : ℕ) : ℕ := sourceRank A D / (A-D+3) + 1

private theorem primary_kernel_from_rank (n base cut ker upper : ℕ)
    (hs : cut+ker=base) (hc : cut ≤ upper) (hn : n ≤ base-upper) : n ≤ ker := by omega

theorem primary_family (A D : ℕ) (hA : 0<A) (hD : 3<D) (hBudget : D*4024 ≤ 3000*A)
    (w : I → K) {n : ℕ} (hn : n ≤ sourceRank A D) :
    ∃ e : Fin n → Row 4, LinearIndependent Geom e ∧
      ∀ i, InBox (shape (e i)) primaryBox ∧ TrueWeightLE D (e i) (3000*A-1) ∧
        JetsBounded (e i) ∧ Contact w (e i) := by
  letI : Fact (3<D) := ⟨hD⟩
  let lift : LinearMap.ker (wordMap A D w) →ₗ[Geom] Row 4 :=
    toRow.toLinearMap.comp ((Source A D).subtype.comp (LinearMap.ker (wordMap A D w)).subtype)
  have hinj : Function.Injective lift := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact toRow.injective hab
  have hdim := (wordMap A D w).finrank_range_add_finrank_ker
  have hcols := ExpandedColumns6970.exact_finrank A D hA hD hBudget
  have hr := word_rank A D hD w
  have hker : n ≤ Module.finrank Geom (LinearMap.ker (wordMap A D w)) := by
    apply primary_kernel_from_rank n (Module.finrank Geom (Source A D))
      (Module.finrank Geom (LinearMap.range (wordMap A D w))) _ (262144 * rankCharge) hdim hr
    rw [hcols]
    exact hn
  let admissible (P : Row 4) :=
    InBox (shape P) primaryBox ∧ TrueWeightLE D P (3000*A-1) ∧ JetsBounded P ∧ Contact w P
  refine map_independent_family (V := LinearMap.ker (wordMap A D w)) (W := Row 4)
    (n := n) lift hinj admissible ?_ hker
  intro Q
  obtain ⟨hbox,hweight,hJets⟩ := row_bounds Q.1
  exact ⟨hbox,hweight,hJets,contact_of_word_kernel w Q.1 (LinearMap.mem_ker.mp Q.2)⟩




end
end ExpandedWidePrimary6970
