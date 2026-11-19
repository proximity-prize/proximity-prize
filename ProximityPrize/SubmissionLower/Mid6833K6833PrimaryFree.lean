/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from the independent full-domain primary proof of Bome2017 after Lucieno (PR 618) and BitWonka. Exact 68.33 constants and physical hypotheses are new. -/
import ProximityPrize.SubmissionLower.Koala6831MovingExceptionsRfree
namespace ProximityPrize.SubmissionLower.Koala6831Moving

open scoped BigOperators
open Koala6831MovingSources LocatorDerivativeChain LocatorLowQuotient
open RCN081 RCN156 RCN234

noncomputable section

variable {K : Type} [Field K]
local instance primary319DecidableEq : DecidableEq K := Classical.decEq _

section FixedProfile

open RCN318

def primary319FreeParameters : TightParameters := ⟨262144, weight, 181049, (319*181049), 65864, 1⟩

set_option maxRecDepth 80000 in

theorem primary319_free_count [CharP K 2130706433] {I : Type}
    (H : ExceptionPoly K) (hH : H ≠ 0)
    (hbox : H ∈ nestedCoefficientBox K (319*181049) weight 65864 440 98)
    (seeds : Finset K) (selected : K → Polynomial K) (nodes : Finset I)
    (x u₀ u₁ : I → K) (hinj : Set.InjOn x nodes) (hnodes : nodes.card = 262144)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ weight)
    (hsol : ∀ g ∈ seeds, RCN319.specialization K (selected g) g (freeAndTailCarrier H) = 0)
    (hagree : ∀ g ∈ seeds, 181049 ≤
      (nodes.filter fun i => (selected g).eval (x i) = u₀ i + g * u₁ i).card)
    (hpencil : RCN238.NoLargeSelectedPencil selected seeds weight 81095) :
    seeds.card ≤ 59780054304029 := by
  let J := freeAndTailCarrier H
  let params := primary319FreeParameters
  have hweights := nested_mem_weights hbox hH
  have hsmall : H.degreeOf 2 < 2130706433 := by
    apply lt_of_le_of_lt (b := 98) ?_ (by decide +kernel)
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    exact (hbox hd).2.2.1
  have hJ : J ≠ 0 := freeAndTailCarrier_ne_zero H hH _ hsmall
  have hJR : J.degreeOf 2 = 0 := freeAndTailCarrier_R_degree H
  have hJBox : J ∈ RCN174.globalCoefficientBox K params.D params.w params.L params.s := by
    intro d hd
    have ht := (MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans
      ((freeAndTailCarrier_weight_le H hH residualTotalWeights).trans hweights.1)
    have hr := (MvPolynomial.monomial_le_degreeOf (2 : Fin 4) hd).trans_eq hJR
    have hx := (MvPolynomial.le_weightedTotalDegree (contactWeights weight) hd).trans_lt
      ((freeAndTailCarrier_weight_le H hH (contactWeights weight)).trans_lt hweights.2.2.2)
    have ht' : d 1 + d 2 + d 3 ≤ 65864 := by
      simpa [weight_fin4, residualTotalWeights] using ht
    exact ⟨by change d 1 + d 3 ≤ 65864; omega,
      hr.trans (by decide +kernel),
      by simpa [weight_fin4, contactWeights, Nat.mul_comm, params, primary319FreeParameters] using hx⟩
  have herrors : params.errors = 81095 := by decide +kernel
  have hpencil' : RCN238.NoLargeSelectedPencil selected seeds params.w params.errors := by
    rw [herrors]
    exact hpencil
  have hcount := rfree_seed_count_le params J hJ 2130706433 hJBox hJR rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) selected seeds nodes x u₀ u₁ hinj hnodes
    hdegree hsol hagree hpencil'
  exact hcount.trans (by decide +kernel)

end FixedProfile

end

end ProximityPrize.SubmissionLower.Koala6831Moving
#print axioms ProximityPrize.SubmissionLower.Koala6831Moving.primary319_free_count
