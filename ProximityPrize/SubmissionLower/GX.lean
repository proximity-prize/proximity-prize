import ProximityPrize.SubmissionLower.GY
namespace ProximityPrize.SubmissionLower.ContactTwoTailMultiplicityAggregation6732Research
open scoped Classical BigOperators
open ContactRegularComponentCover ContactFlagBezout6543Research
open ContactPrimeFlagBudgetFamilyResearch
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Omega Seed:Type} [Field Omega]
variable {G T1 H:MvPolynomial (Fin 3) Omega}
variable {flag tailFlag1 tailFlag2:FlagDegree}
def delayedComponents
   (active:RegularComponent Omega G T1 H → Prop):
   Finset (RegularComponent Omega G T1 H):=by
 classical
 exact Finset.univ.filter active
structure DelayedBranchFlagBudget
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (active:RegularComponent Omega G T1 H → Prop) where
 multiplicity:RegularComponent Omega G T1 H → ℕ
 cost:RegularComponent Omega G T1 H → ℕ
 cost_le:∀ C,active C →
   cost C ≤ multiplicity C*B.weightedCost tailFlag2 C
 divisor_le:
   (∑ C∈delayedComponents active,
     multiplicity C*B.weightedCost tailFlag2 C) ≤
       flagMixed flag tailFlag1 tailFlag2
theorem delayed_component_sum_le_flagMixed
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (active:RegularComponent Omega G T1 H → Prop)
   (D:DelayedBranchFlagBudget (tailFlag2:=tailFlag2) B active)
   (S:Finset Seed) (point:Seed → Fin 3 → Omega)
   (hcomponent:∀ C,active C →
     (componentSeeds Omega G T1 H S point C).card ≤ D.cost C):
   (∑ C∈delayedComponents active,
     (componentSeeds Omega G T1 H S point C).card) ≤
       flagMixed flag tailFlag1 tailFlag2:=by
 classical
 calc
   _ ≤ ∑ C∈delayedComponents active,D.cost C:=by
     apply Finset.sum_le_sum
     intro C hC
     exact hcomponent C (Finset.mem_filter.mp hC).2
   _ ≤ ∑ C∈delayedComponents active,
       D.multiplicity C*B.weightedCost tailFlag2 C:=by
     apply Finset.sum_le_sum
     intro C hC
     exact D.cost_le C (Finset.mem_filter.mp hC).2
   _ ≤ flagMixed flag tailFlag1 tailFlag2:=D.divisor_le
theorem delayed_seed_union_card_le_flagMixed
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (active:RegularComponent Omega G T1 H → Prop)
   (D:DelayedBranchFlagBudget (tailFlag2:=tailFlag2) B active)
   [DecidableEq Seed]
   (S:Finset Seed) (point:Seed → Fin 3 → Omega)
   (hcomponent:∀ C,active C →
     (componentSeeds Omega G T1 H S point C).card ≤ D.cost C):
   ((delayedComponents active).biUnion
     (componentSeeds Omega G T1 H S point)).card ≤
       flagMixed flag tailFlag1 tailFlag2:=by
 classical
 exact Finset.card_biUnion_le.trans
   (delayed_component_sum_le_flagMixed B active D S point hcomponent)
def DelayedBranchFlagBudget.immediate
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (active:RegularComponent Omega G T1 H → Prop):
   DelayedBranchFlagBudget (tailFlag2:=tailFlag2) B active where
 multiplicity:=fun _ => 1
 cost:=fun C => B.weightedCost tailFlag2 C
 cost_le:=by simp
 divisor_le:=by
   calc
     (∑ C∈delayedComponents active,
         1*B.weightedCost tailFlag2 C)=
         ∑ C∈delayedComponents active,
           B.weightedCost tailFlag2 C:=by simp
     _ ≤
         ∑ C:RegularComponent Omega G T1 H,
           B.weightedCost tailFlag2 C:=by
       exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
     _ ≤ flagMixed flag tailFlag1 tailFlag2:=
       B.sum_weightedCost_le tailFlag2
end
end ProximityPrize.SubmissionLower.ContactTwoTailMultiplicityAggregation6732Research
