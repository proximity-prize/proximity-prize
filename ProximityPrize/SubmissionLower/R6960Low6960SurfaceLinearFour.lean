import ProximityPrize.SubmissionLower.GoldBranch6N8
import ProximityPrize.SubmissionLower.Final50Price
import ProximityPrize.SubmissionLower.KoalaRetainedCut
import ProximityPrize.SubmissionLower.R6960Low6960AnchorColumns
import ProximityPrize.SubmissionLower.R6960Low6960Retained
import ProximityPrize.SubmissionLower.UpperBranch5
import ProximityPrize.SubmissionLower.RingHomShortcuts

set_option Elab.async false

-- merged module R6960Low6960Inventory
section Merged_R6960Low6960Inventory

-- merged module Euler50Price
section Merged_Euler50Price

set_option Elab.async false
namespace Euler50Price
noncomputable section
open P3 (I K node)
open K1_13 (Geom extend Row Shape shape Fits InBox Contact chart liftedChart mixed32 ceilDiv atJet
  OnFactor FatEligible OrderAt indexDegree)
open scoped BigOperators Polynomial





def ActiveFits (f : Row 4) (K : ℕ) : Prop :=
  ∀ m ∈ f.support, m 0 + 2*m 1 + 2*m 2 + 2*m 3 ≤ K





















































end
end Euler50Price

end Merged_Euler50Price

-- merged module Euler50GeoCover
section Merged_Euler50GeoCover
set_option Elab.async false
namespace Euler50GeoLead
open K1_13 (Geom Row shape indexDegree)
open K1_13_1 (topView topView_degree anchorLead anchorLead_ne indexDegree_eq)
open MvPolynomial
open scoped Polynomial
theorem term_weight (P : Row 4) (m : Fin 3 →₀ ℕ) (hm : m ∈ (anchorLead P).support) :
    ∃ u ∈ P.support, ∀ w : Fin 4 → ℕ,
      m.weight (fun i => w i.castSucc) + (shape P).t * w 3 = u.weight w := by
  classical
  let k := (topView P).natDegree
  let c := rename finSuccEquivLast P
  have hc : c.coeff (m.optionElim k) = (anchorLead P).coeff m :=
    (optionEquivLeft_coeff_coeff _ _ _ _).symm
  have hs : m.optionElim k ∈ c.support :=
    mem_support_iff.mpr (by rw [hc]; exact mem_support_iff.mp hm)
  rw [show c = rename finSuccEquivLast P from rfl,
    support_rename_of_injective finSuccEquivLast.injective] at hs
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hs
  refine ⟨u, hu, fun w => ?_⟩
  let w' : Option (Fin 3) → ℕ := fun v => v.elim (w 3) (fun i => w i.castSucc)
  have hlast : finSuccEquivLast (3 : Fin 4) = none := finSuccEquivLast_last
  have hw : ∀ i : Fin 4, w' (finSuccEquivLast i) = w i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [w', hlast, show Fin.last 3 = (3 : Fin 4) by rfl]
    · simp [w']
  have hweight : (m.optionElim k).weight w' = u.weight w := by
    rw [← he]
    simp only [Finsupp.weight_apply, smul_eq_mul]
    rw [Finsupp.sum_mapDomain_index (by simp) (by intros; rw [Nat.add_mul])]
    simp only [hw]
  rw [Finsupp.weight_optionElim] at hweight
  simpa only [w', Option.elim, k, topView_degree, smul_eq_mul, Nat.add_comm, Nat.mul_comm] using hweight
theorem lead_degree (P : Row 4) (hP : P ≠ 0) :
    (anchorLead P).totalDegree + (shape P).t ≤ P.totalDegree := by
  classical
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup _ ((support_nonempty.mpr (anchorLead_ne hP))) (fun m => m.weight (1 : Fin 3 → ℕ))
  obtain ⟨u, hu, hw⟩ := term_weight P m hm
  have h := (hw (1 : Fin 4 → ℕ)).le.trans (le_weightedTotalDegree _ hu)
  rw [← weightedTotalDegree_one, weightedTotalDegree, he, ← weightedTotalDegree_one]
  have hconst : (fun i : Fin 3 => (1 : Fin 4 → ℕ) i.castSucc) = (1 : Fin 3 → ℕ) := rfl
  rw [hconst] at h
  simpa only [Pi.one_apply, Nat.mul_one] using h
theorem lead_index (P : Row 4) (hP : P ≠ 0) :
    indexDegree (anchorLead P) + 3 * (shape P).t ≤ indexDegree P := by
  classical
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup _ (support_nonempty.mpr (anchorLead_ne hP)) (fun m => m.weight (fun i : Fin 3 => i.val))
  obtain ⟨u, hu, hw⟩ := term_weight P m hm
  rw [indexDegree_eq, weightedTotalDegree, he, indexDegree_eq]
  simpa [Nat.mul_comm] using (hw (fun i => i.val)).le.trans (le_weightedTotalDegree _ hu)
end Euler50GeoLead
namespace Euler50GeoCover
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P3 (K I node)
open Euler50Price (ActiveFits)
open K1_13 (Geom embed extend Row shape InBox atJet indexDegree jet OnFactor)
open K1_13_1 (anchorLead anchorLead_ne anchorLead_mul indexDegree_eq eval_anchorLead
  atJet_eq_anchorLead_of_top_zero)
open scoped BigOperators Polynomial
open K1_13_1 (coeff_flatten anchorLead_term index_bounds)
def activeDegree (f : Row 4) : ℕ :=
  MvPolynomial.weightedTotalDegree (![1, 2, 2, 2] : Fin 4 → ℕ) f
private theorem activeWeight_at (m : Fin 4 →₀ ℕ) :
    m.weight (![1, 2, 2, 2] : Fin 4 → ℕ) = m 0 + 2*m 1 + 2*m 2 + 2*m 3 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, smul_eq_mul, Nat.mul_comm]
theorem activeFits_iff (f : Row 4) (K : ℕ) : ActiveFits f K ↔ activeDegree f ≤ K := by
  unfold ActiveFits activeDegree MvPolynomial.weightedTotalDegree
  rw [Finset.sup_le_iff]
  simp only [activeWeight_at]
section FactorCover
open MvPolynomial UniqueFactorizationMonoid
end FactorCover
end
end Euler50GeoCover

end Merged_Euler50GeoCover

-- merged module Final50GeoCover
section Merged_Final50GeoCover

set_option Elab.async false
namespace Final50GeoCover
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P3 (K I node)
open Final50Price (TrueWeightLE anchorCutoff physicalDegree Fits  SmallFactor ActiveFits)
open K1_13 (Geom embed extend Row shape InBox atJet indexDegree jet OnFactor)
open K1_13_1 (anchorLead anchorLead_ne anchorLead_mul indexDegree_eq eval_anchorLead
  atJet_eq_anchorLead_of_top_zero)
open scoped BigOperators Polynomial
open K1_13_1 (coeff_flatten anchorLead_term index_bounds)

abbrev activeDegree := Euler50GeoCover.activeDegree

theorem activeFits_iff (f : Row 4) (K : ℕ) : ActiveFits f K ↔ activeDegree f ≤ K :=
  Euler50GeoCover.activeFits_iff f K



























section FactorCover
open MvPolynomial UniqueFactorizationMonoid
end FactorCover

end
end Final50GeoCover

end Merged_Final50GeoCover

-- merged module KoalaRetainedWitness
section Merged_KoalaRetainedWitness
set_option autoImplicit false
set_option Elab.async false
namespace KoalaRetainedCut
noncomputable section
open MvPolynomial
open K1_13 (Row Geom Shape shape InBox OrderAt atJet extend embed indexDegree)
open Final50Price (primaryBox primaryCutoff TrueWeightLE ActiveFits physicalDegree)
open P0_9_3_2 (translateTop topHasse topHasse_zero topHasse_coeff source_support sum_add_top total_add_top apply_add_top erase_top_add topHasse_order exact_hasse_not_dvd)
open scoped Polynomial BigOperators




























































































































































end
end KoalaRetainedCut

end Merged_KoalaRetainedWitness

-- merged module KoalaRetainedCover
section Merged_KoalaRetainedCover
set_option autoImplicit false
set_option Elab.async false
namespace KoalaRetainedCut
noncomputable section
open P3 (K)
open K1_13 (Geom Row shape topLead atJet jet extend OnFactor)
open K1_13_1 (anchorLead anchorLead_mul eval_anchorLead atJet_eq_anchorLead_of_top_zero)
open UniqueFactorizationMonoid MvPolynomial
open scoped Polynomial BigOperators
theorem anchor_factors {P : Row 4} (hP : P ≠ 0) :
    ∃ (n : ℕ) (f : Fin n → Row 4),
      (∀ i, Irreducible (f i) ∧ 0 < (shape (f i)).t ∧ f i ∣ P) ∧
      (∀ i j, i ≠ j → ¬ Associated (f i) (f j)) ∧ (∏ i, f i) ∣ P ∧
      ∀ S : (Polynomial Geom), atJet P S = 0 → atJet (anchorLead P) S = 0 ∨ ∃ i, OnFactor (f i) S := by
  classical
  let _ : StrongNormalizationMonoid (Row 4) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := normalizedFactors P
  let T := A.toFinset.filter fun q => 0 < (shape q).t
  let n := Fintype.card ↥T
  let e : Fin n ≃ ↥T := (Fintype.equivFin ↥T).symm
  let f : Fin n → Row 4 := fun i => (e i).val
  have hT (q) (hq : q ∈ T) : q ∈ A ∧ 0 < (shape q).t := by simpa [T] using hq
  have hfi (i : Fin n) : f i ∈ A ∧ 0 < (shape (f i)).t := hT _ (e i).property
  refine ⟨n,f,fun i => ⟨irreducible_of_normalized_factor _ (hfi i).1,(hfi i).2,
    dvd_of_mem_normalizedFactors (hfi i).1⟩,?_,?_,?_⟩
  · intro i j hij hassoc
    apply hij
    apply e.injective
    exact Subtype.ext (mem_normalizedFactors_eq_of_associated (hfi i).1 (hfi j).1 hassoc)
  · have heq : (∏ i, f i) = ∏ q ∈ T, q := by
      rw [show (∏ i, f i) = ∏ q : ↥T, q.val from e.prod_comp Subtype.val]
      exact Finset.prod_coe_sort T id
    rw [heq]
    exact ((Finset.prod_dvd_prod_of_subset T A.toFinset id (Finset.filter_subset _ _)).trans
      (Multiset.toFinset_prod_dvd_prod A)).trans (prod_normalizedFactors hP).dvd
  · intro S hz
    by_cases hg : atJet (anchorLead P) S = 0
    · exact Or.inl hg
    right
    have hSA : MvPolynomial.eval (jet S) A.prod = 0 := by
      have hdiv := _root_.map_dvd (MvPolynomial.eval (jet S)) (prod_normalizedFactors hP).symm.dvd
      change atJet P S ∣ MvPolynomial.eval (jet S) A.prod at hdiv
      rw [hz,zero_dvd_iff] at hdiv
      exact hdiv
    rw [map_multiset_prod,Multiset.prod_eq_zero_iff,Multiset.mem_map] at hSA
    obtain ⟨q,hq,hqS⟩ := hSA
    have hqlead : atJet (anchorLead q) S ≠ 0 := by
      intro hzero
      obtain ⟨R,hR⟩ := dvd_of_mem_normalizedFactors hq
      apply hg
      rw [hR,anchorLead_mul,atJet,map_mul]
      exact mul_eq_zero_of_left hzero _
    have hqt : 0 < (shape q).t := by
      by_contra! h
      apply hqlead
      rw [← atJet_eq_anchorLead_of_top_zero q S (Nat.eq_zero_of_le_zero h)]
      exact hqS
    have hqT : q ∈ T := Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hq,hqt⟩
    let j := e.symm ⟨q,hqT⟩
    have hj : f j = q := congrArg Subtype.val (e.apply_symm_apply ⟨q,hqT⟩)
    exact ⟨j,by rw [hj,OnFactor,← eval_anchorLead]; exact ⟨hqS,hqlead⟩⟩
theorem topLead_off_lower {P f : Row 4} {S : (Polynomial Geom)} (h : f ∣ P)
    (hoff : atJet (anchorLead P) S ≠ 0) : topLead f S ≠ 0 := by
  obtain ⟨G,rfl⟩ := h
  rw [anchorLead_mul,atJet,map_mul] at hoff
  rw [← eval_anchorLead]
  exact left_ne_zero_of_mul hoff
theorem priority_pieces {n : ℕ} {P : Row 4} {f : Fin n → Row 4} (hdiv : ∀ i, f i ∣ P)
    {Γ : Finset K} (s : K → (Polynomial K)) (book : Finset K) (z : Finset (Fin n))
    (hbase : ∀ γ ∈ Γ, atJet (anchorLead P) (extend (s γ)) = 0 ∨ ∃ i, OnFactor (f i) (extend (s γ))) :
    ∃ (low : Finset K) (piece : Fin n → Finset K),
      low ⊆ Γ ∧ (∀ γ ∈ low, atJet (anchorLead P) (extend (s γ)) = 0) ∧
      (∀ i, piece i ⊆ Γ) ∧ (∀ i γ, γ ∈ piece i → γ ∉ book ∧ OnFactor (f i) (extend (s γ))) ∧
      (∀ i ∉ z, ∀ γ ∈ piece i, atJet (∏ j ∈ z, f j) (extend (s γ)) ≠ 0) ∧
      Γ.card ≤ book.card + low.card + ∑ i, (piece i).card := by
  classical
  let S (γ : K) := extend (s γ)
  let H := ∏ j ∈ z, f j
  let low := Γ.filter (fun γ => atJet (anchorLead P) (S γ)=0)
  let piece (i : Fin n) := Γ.filter (fun γ => γ∉book ∧ OnFactor (f i) (S γ) ∧
    (i∈z ∨ atJet H (S γ) ≠ 0))
  refine ⟨low,piece,Finset.filter_subset _ _,fun γ h => (Finset.mem_filter.mp h).2,
    fun i => Finset.filter_subset _ _,fun i _ h => ⟨(Finset.mem_filter.mp h).2.1,
      (Finset.mem_filter.mp h).2.2.1⟩,fun i hi _ h => (Finset.mem_filter.mp h).2.2.2.resolve_left hi,?_⟩
  have full : Γ ⊆ book ∪ low ∪ Finset.univ.biUnion piece := by
    intro γ hγ
    by_cases hb : γ∈book
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
    by_cases hg : atJet (anchorLead P) (S γ)=0
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ,hg⟩))
    apply Finset.mem_union_right
    by_cases hH : atJet H (S γ)=0
    · have hp : ∏ j∈z, atJet (f j) (S γ) = 0 := by
        simpa only [H,atJet,map_prod] using hH
      obtain ⟨i,hi,hzero⟩ := Finset.prod_eq_zero_iff.mp hp
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr
        ⟨hγ,hb,⟨hzero,topLead_off_lower (hdiv i) hg⟩,Or.inl hi⟩⟩
    · obtain ⟨i,hon⟩ := (hbase γ hγ).resolve_left hg
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr
        ⟨hγ,hb,hon,Or.inr hH⟩⟩
  exact (Finset.card_le_card full).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le))
end
end KoalaRetainedCut

end Merged_KoalaRetainedCover

-- merged module R6960Low6960Inventory
section Merged_R6960Low6960Inventory
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
namespace Lower6960.Low
noncomputable section
open Finset Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P3 (K I node)
open K1_13 (Geom extend Row Shape shape InBox atJet indexDegree OnFactor)
open K1_13_1 (anchorLead anchorLead_ne indexDegree_eq)
open Final50Price (ActiveFits)
open Final50GeoCover (activeDegree activeFits_iff)
open K1_13_1 (coeff_flatten anchorLead_term index_bounds)
open scoped BigOperators Polynomial Classical







































section FactorCover
open MvPolynomial UniqueFactorizationMonoid




































end FactorCover








































































end
end Lower6960.Low

end Merged_R6960Low6960Inventory

end Merged_R6960Low6960Inventory

-- merged module R6960Low6960Monotone
section Merged_R6960Low6960Monotone

-- merged module Final50FatReserve
section Merged_Final50FatReserve
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
namespace Final50FatReserve
open K1_13 (Shape chart ceilDiv mixed32)
open K1_13_8 (Valid)
open K1_13_8_4 (TotalLE IndexFits mixed_mono_total)
open Final50Price (fatPrice linearChart taylorLength physicalDegree incidenceGap
  resultantBox commonBox fatOrder divisorOrder isolatedOrder)









































































































































































































































































end Final50FatReserve

end Merged_Final50FatReserve

-- merged module R6960Low6960RetainedFees
section Merged_R6960Low6960RetainedFees
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16000
namespace Lower6960.Low
open Finset
open K1_13 (Shape chart ceilDiv mixed32 shape)
open K1_13_8 (Valid)

open K1_13_8_4 (TotalLE)
open scoped BigOperators Classical






















































































































































































































































































































































































































































end Lower6960.Low

end
end Merged_R6960Low6960RetainedFees

-- merged module R6960Low6960Width
section Merged_R6960Low6960Width

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6960.Low
open Finset Polynomial
open P3 (K)
open K1_13 (Shape shape)
open K1_13_8 (Valid zeroShape)


open P3_6_8 (shapeSum shapeSum_empty shapeSum_valid_or_empty)
open scoped Classical BigOperators







































end Lower6960.Low

end
end Merged_R6960Low6960Width

-- merged module R6960Low6960Prices
section Merged_R6960Low6960Prices

set_option Elab.async false
namespace Low6960Prices
noncomputable section
open P3 (I K node)
open K1_13 (Geom extend Row Shape shape Fits InBox Contact chart liftedChart mixed32 ceilDiv atJet
  OnFactor FatEligible OrderAt indexDegree)
open scoped BigOperators Polynomial









































































































































































end
end Low6960Prices

end Merged_R6960Low6960Prices

-- merged module R6960Low6960Monotone
section Merged_R6960Low6960Monotone
set_option Elab.async false
section
namespace Low6960Monotone
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)




























































































end Low6960Monotone
end

namespace Low6960Monotone
open K1_13 (Shape)






























end Low6960Monotone

end Merged_R6960Low6960Monotone

end Merged_R6960Low6960Monotone

-- merged module R6960Low6960SurfaceLinearFour
section Merged_R6960Low6960SurfaceLinearFour

-- merged module R6960Low6960SharedPrice
section Merged_R6960Low6960SharedPrice
set_option Elab.async false
set_option autoImplicit false
namespace Low6960SharedPrice
open K1_13 (Shape chart ceilDiv mixed32 shape OnFactor extend)


open scoped Polynomial













































































































































































end Low6960SharedPrice

end Merged_R6960Low6960SharedPrice

-- merged module R6960Low6960SurfaceLinearFour
section Merged_R6960Low6960SurfaceLinearFour
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Low6960SharedPrice
open K1_13 (Shape chart difference volume32)
open K1_13_8 (Valid)

open K1_13_8_2 (signedMixed signed_rotate signed_nonneg)








































end Low6960SharedPrice

end Merged_R6960Low6960SurfaceLinearFour

end Merged_R6960Low6960SurfaceLinearFour
