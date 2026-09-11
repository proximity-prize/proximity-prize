import ProximityPrize.SubmissionLower.BoundaryTailInitial
import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.BoundaryTailDegreeAwareChain
open scoped Classical BigOperators
open RCN174 RCN319 RCN081 RCN082 RCN167 RCN286 RCN052 RCN260 RCN318 RCN267 RCN313
  RCN135 RCN138 RCN136 RCN238 RCN293 RCN231 RCN243 LocatorDerivativeChain
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq _
local instance : StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
variable {Iota : Type}
local instance : DecidableEq Iota := Classical.decEq _



/-- Keep the derivative stages and the one tail of each factor correlated. -/
theorem factor_charge_le
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K) (Gamma : Finset K)
    (stage : ℕ → ℕ) (tail unit : ℕ)
    (hstages : ∀ j ∈ Finset.Ico 1 (chainLength F),
      (chainSeeds F j selected Gamma).card ≤ stage j)
    (htail : (tailSeeds F selected Gamma).card ≤ tail)
    (hreceipt : (∑ j ∈ Finset.Ico 1 (F.degreeOf 2), stage j) + tail ≤
      F.degreeOf 2 * unit) :
    (∑ j ∈ Finset.Ico 1 (chainLength F), (chainSeeds F j selected Gamma).card) +
      (tailSeeds F selected Gamma).card ≤ F.degreeOf 2 * unit := by
  have hsub : Finset.Ico 1 (chainLength F) ⊆ Finset.Ico 1 (F.degreeOf 2) := by
    intro j hj
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hj).1,
      (Finset.mem_Ico.mp hj).2.trans_le (chainLength_le F)⟩
  exact (Nat.add_le_add
    ((Finset.sum_le_sum hstages).trans (Finset.sum_le_sum_of_subset hsub)) htail).trans hreceipt

/-- The degree budget applies to the combined chain-and-tail charge. -/
theorem cover_count_le_degree
    (Q T : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (D w L s p regular unit tail : ℕ) [CharP K p]
    (hw : 0 < w) (hsmall : s < p)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hQsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ Q = 0)
    (hTsolution : ∀ γ ∈ Gamma, specialization K (selected γ) γ T = 0)
    (hregular : (∑ F : RegularIndex Q,
      (regularPairSeeds Q T selected Gamma F).card) ≤ regular)
    (hfactor : ∀ F ∈ positiveRFactors Q,
      (∑ j ∈ Finset.Ico 1 (chainLength F), (chainSeeds F j selected Gamma).card) +
        (tailSeeds F selected Gamma).card ≤ F.degreeOf 2 * unit)
    (hfree : (rfreeSeeds Q selected Gamma).card ≤ tail) :
    Gamma.card ≤ regular + s * unit + tail := by
  have hR : ∀ F ∈ positiveRFactors Q, F.degreeOf 2 ≤ s := fun F hF =>
    degreeOf_R_le_of_mem_box F D w L s (directFactor_data Q F hQ D w L s hbox hF).2.2
  have hcover := cover Q T hQ p s hsmall hR selected Gamma hQsolution hTsolution
  have hbudget := (directFactor_input_budgets Q hQ D w L s hw hbox).2.1
  have hsum :
      (∑ F ∈ positiveRFactors Q,
        ∑ j ∈ Finset.Ico 1 (chainLength F), (chainSeeds F j selected Gamma).card) +
      (∑ F ∈ positiveRFactors Q, (tailSeeds F selected Gamma).card) ≤ s * unit := by
    rw [← Finset.sum_add_distrib]
    calc
      _ ≤ ∑ F ∈ positiveRFactors Q, F.degreeOf 2 * unit := Finset.sum_le_sum hfactor
      _ = (∑ F ∈ positiveRFactors Q, F.degreeOf 2) * unit := (Finset.sum_mul ..).symm
      _ ≤ s * unit := Nat.mul_le_mul_right unit hbudget
  have hA : (Finset.univ.biUnion fun F : RegularIndex Q =>
      regularPairSeeds Q T selected Gamma F).card ≤ regular :=
    Finset.card_biUnion_le.trans hregular
  have hB : ((positiveRFactors Q).biUnion fun F =>
      (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma).card ≤
      ∑ F ∈ positiveRFactors Q,
        ∑ j ∈ Finset.Ico 1 (chainLength F), (chainSeeds F j selected Gamma).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun F _ => Finset.card_biUnion_le)
  have hC : ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma).card ≤
      ∑ F ∈ positiveRFactors Q, (tailSeeds F selected Gamma).card := Finset.card_biUnion_le
  have hcard := Finset.card_le_card hcover
  have h1 := Finset.card_union_le
    ((Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q T selected Gamma F) ∪
      ((positiveRFactors Q).biUnion fun F =>
        (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma) ∪
      ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma))
    (rfreeSeeds Q selected Gamma)
  have h2 := Finset.card_union_le
    ((Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q T selected Gamma F) ∪
      ((positiveRFactors Q).biUnion fun F =>
        (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma))
    ((positiveRFactors Q).biUnion fun F => tailSeeds F selected Gamma)
  have h3 := Finset.card_union_le
    (Finset.univ.biUnion fun F : RegularIndex Q => regularPairSeeds Q T selected Gamma F)
    ((positiveRFactors Q).biUnion fun F =>
      (Finset.Ico 1 (chainLength F)).biUnion fun j => chainSeeds F j selected Gamma)
  omega


/-- Numeric pair parameters retain both the factor degree and the derivative index. -/
def stageParameters (errors totalCap degree stage : ℕ) : UnequalParameters :=
  ⟨262144, 131071, 262144 - errors, 153, degree - stage, totalCap,
    153, degree, totalCap⟩

def factorCost (errors totalCap tail degree : ℕ) : ℕ :=
  (∑ j ∈ Finset.Ico 1 degree, (stageParameters errors totalCap degree j).regularCountCap) + tail

def fixedUnit : ℕ := 106630157151757



def residualUnit : ℕ := 215521363518693




end
end ProximityPrize.SubmissionLower.BoundaryTailDegreeAwareChain



/-! Shared factor budgets and derivative counts using actual coordinate degrees. -/
namespace ProximityPrize.SubmissionLower.BoundaryTailSharedDegreeBudget
open scoped Classical BigOperators
open RCN238 RCN081 RCN071 RCN167 RCN174 RCN319 RCN052 RCN260 RCN313 LocatorDerivativeChain
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq _

/-- Factors charged on the two sides of a product share every weighted degree.
The factor families may overlap: multiplicity in the product pays for that overlap. -/
theorem two_family_weight_budget {A B : Type*} [DecidableEq A] [DecidableEq B]
    (weights : Fin 4 → ℕ) (fs : Finset A) (bs : Finset B)
    (f : A → MvPolynomial (Fin 4) K) (g : B → MvPolynomial (Fin 4) K)
    (H Q : MvPolynomial (Fin 4) K) (hH : H ≠ 0) (hQ : Q ≠ 0)
    (hf : (∏ a ∈ fs, f a) ∣ H) (hg : (∏ b ∈ bs, g b) ∣ Q) :
    (∑ a ∈ fs, MvPolynomial.weightedTotalDegree weights (f a)) +
      (∑ b ∈ bs, MvPolynomial.weightedTotalDegree weights (g b)) ≤
        MvPolynomial.weightedTotalDegree weights (H * Q) := by
  rw [weightedTotalDegree_mul weights H Q hH hQ]
  exact Nat.add_le_add
    (sum_weightedTotalDegree_le_of_prod_dvd weights fs f H hH hf)
    (sum_weightedTotalDegree_le_of_prod_dvd weights bs g Q hQ hg)

/-- Debit the routed family before allocating a budget to all remaining factors. -/
theorem split_weight_budget {A B : Type*} [DecidableEq A] [DecidableEq B]
    (weights : Fin 4 → ℕ) (fs us : Finset A) (bs : Finset B) (hus : us ⊆ fs)
    (f : A → MvPolynomial (Fin 4) K) (g : B → MvPolynomial (Fin 4) K)
    (H Q : MvPolynomial (Fin 4) K) (hH : H ≠ 0) (hQ : Q ≠ 0)
    (hf : (∏ a ∈ fs, f a) ∣ H) (hg : (∏ b ∈ bs, g b) ∣ Q)
    (cap : ℕ) (hcap : MvPolynomial.weightedTotalDegree weights (H * Q) ≤ cap) :
    (∑ a ∈ fs \ us, MvPolynomial.weightedTotalDegree weights (f a)) +
      (∑ b ∈ bs, MvPolynomial.weightedTotalDegree weights (g b)) ≤
        cap - ∑ a ∈ us, MvPolynomial.weightedTotalDegree weights (f a) := by
  have hb := (two_family_weight_budget weights fs bs f g H Q hH hQ hf hg).trans hcap
  have hs := Finset.sum_sdiff hus (f := fun a => MvPolynomial.weightedTotalDegree weights (f a))
  omega

/-- A common factor and the quotient use the same slope budget of the selected polynomial. -/
theorem split_slope_charge {A B : Type*} [DecidableEq A] [DecidableEq B]
    (fs us : Finset A) (bs : Finset B) (hus : us ⊆ fs)
    (f : A → MvPolynomial (Fin 4) K) (g : B → MvPolynomial (Fin 4) K)
    (H Q : MvPolynomial (Fin 4) K) (hH : H ≠ 0) (hQ : Q ≠ 0)
    (hf : (∏ a ∈ fs, f a) ∣ H) (hg : (∏ b ∈ bs, g b) ∣ Q)
    (cap unitU unitRest : ℕ) (hcap : (H * Q).degreeOf 2 ≤ cap)
    (costA : A → ℕ) (costB : B → ℕ)
    (hu : ∀ a ∈ us, costA a ≤ (f a).degreeOf 2 * unitU)
    (ha : ∀ a ∈ fs \ us, costA a ≤ (f a).degreeOf 2 * unitRest)
    (hb : ∀ b ∈ bs, costB b ≤ (g b).degreeOf 2 * unitRest) :
    (∑ a ∈ fs, costA a) + (∑ b ∈ bs, costB b) ≤
      (∑ a ∈ us, (f a).degreeOf 2) * unitU +
        (cap - ∑ a ∈ us, (f a).degreeOf 2) * unitRest := by
  have hdA := sum_degreeOf_le_of_prod_dvd fs f H hH hf (2 : Fin 4)
  have hdB := sum_degreeOf_le_of_prod_dvd bs g Q hQ hg (2 : Fin 4)
  have heq := MvPolynomial.degreeOf_mul_eq (n := (2 : Fin 4)) hH hQ
  have hs := Finset.sum_sdiff hus (f := fun a => (f a).degreeOf 2)
  have hd : (∑ a ∈ fs \ us, (f a).degreeOf 2) + (∑ b ∈ bs, (g b).degreeOf 2) ≤
      cap - ∑ a ∈ us, (f a).degreeOf 2 := by omega
  have hcu := Finset.sum_le_sum hu
  have hca := Finset.sum_le_sum ha
  have hcb := Finset.sum_le_sum hb
  rw [← Finset.sum_mul] at hcu hca hcb
  have hrest := Nat.add_le_add hca hcb
  rw [← Nat.add_mul] at hrest
  have hrest' := hrest.trans (Nat.mul_le_mul_right unitRest hd)
  have hcs := Finset.sum_sdiff hus (f := costA)
  omega

/-- Coordinate degrees suffice for the mixed-degree budget; no ambient box is needed. -/
theorem regularVector_budgets_actual
    (P : UnequalParameters) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hY : Q.degreeOf 1 ≤ P.leftY) (hR : Q.degreeOf 2 ≤ P.leftR)
    (hZ : Q.degreeOf 3 ≤ P.leftZ) :
    (∑ F : RegularIndex Q, (regularVector P F.1).y) ≤ P.mixedCost.y ∧
    (∑ F : RegularIndex Q, (regularVector P F.1).r) ≤ P.mixedCost.r ∧
    (∑ F : RegularIndex Q, (regularVector P F.1).z) ≤ P.mixedCost.z := by
  have hi (i : Fin 4) : (∑ F : RegularIndex Q, F.1.degreeOf i) ≤ Q.degreeOf i := by
    rw [← Finset.sum_subtype (positiveRFactors Q) (fun _ => Iff.rfl)]
    exact sum_degreeOf_le_of_prod_dvd (positiveRFactors Q) id Q hQ
      (positiveRFactors_product_dvd Q hQ) i
  have hy := (hi 1).trans hY
  have hr := (hi 2).trans hR
  have hz := (hi 3).trans hZ
  simp only [regularVector, Finset.sum_add_distrib]
  constructor
  · rw [← Finset.sum_mul, ← Finset.sum_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hr) (Nat.mul_le_mul_right P.rightR hz)
  constructor
  · rw [← Finset.sum_mul, ← Finset.sum_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hy) (Nat.mul_le_mul_right P.rightY hz)
  · rw [← Finset.sum_mul, ← Finset.sum_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_right P.rightR hy) (Nat.mul_le_mul_right P.rightY hr)

theorem dR_degree_le (j : ℕ) (F : MvPolynomial (Fin 4) K) (i : Fin 4) :
    (dR j F).degreeOf i ≤ F.degreeOf i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [dR_succ]
    exact pderiv_degree_bound 2 i (dR j F) (F.degreeOf i) ih

variable {I : Type}
local instance : DecidableEq I := Classical.decEq _

/-- The derivative stage can use the actual Y, R and Z degrees of its factor. -/
theorem chainSeeds_card_le_actual
    (P : UnequalParameters) (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (p : ℕ) [CharP K p] (hpos : 0 < F.degreeOf 2) (hsmall : F.degreeOf 2 < p)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ chainLength F)
    (hgap : 0 < P.gap)
    (hY : F.degreeOf 1 ≤ P.leftY) (hR : F.degreeOf 2 - j ≤ P.leftR)
    (hZ : F.degreeOf 3 ≤ P.leftZ)
    (hY' : F.degreeOf 1 ≤ P.rightY) (hR' : F.degreeOf 2 ≤ P.rightR)
    (hZ' : F.degreeOf 3 ≤ P.rightZ)
    (hleftR : 1 ≤ P.leftR)
    (hleftYSmall : P.leftY < p) (hleftRSmall : P.leftR < p) (hleftZSmall : P.leftZ < p)
    (hmixedYSmall : P.mixedCost.y < p) (hmixedRSmall : P.mixedCost.r < p)
    (hmixedZSmall : P.mixedCost.z < p)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = P.n) (hw : 1 ≤ P.w) (hchar : P.w < p)
    (hwa : P.w < P.a) (han : P.a ≤ P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma, P.a ≤ (nodes.filter (fun i =>
      (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma P.w P.errors) :
    (chainSeeds F j selected Gamma).card ≤ P.regularCountCap := by
  have hne := dR_ne_zero F hF.ne_zero p hsmall j hj
  have hrel := isRelPrime_dR F hF p hpos hsmall j hj1 hj
  have hy := (dR_degree_le j F 1).trans hY
  have hr := (dR_R_degree_le j F).trans hR
  have hz := (dR_degree_le j F 3).trans hZ
  have hcount (G : RegularIndex (dR j F)) := regularPairSeeds_bound P (dR j F) F hrel G p
    ((degreeOf_le_of_dvd 1 G.1 (dR j F) (positiveRFactors_spec _ _ G.2).2.1 hne).trans hy)
    ((degreeOf_le_of_dvd 2 G.1 (dR j F) (positiveRFactors_spec _ _ G.2).2.1 hne).trans hr)
    ((degreeOf_le_of_dvd 3 G.1 (dR j F) (positiveRFactors_spec _ _ G.2).2.1 hne).trans hz)
    hY' hR' hZ' hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma nodes x u0 u1
    hinj hnodes hw hchar hwa han hdegree hagreement hno
  have hsum := sum_regular_counts_bound P (dR j F) F selected Gamma
    (regularVector_budgets_actual P (dR j F) hne hy hr hz) hcount
  have hc := P.regular_count_le _ hgap hsum
  exact (Finset.card_le_card (chainSeeds_subset_regularPairSeeds F j hne selected Gamma)).trans
    (Finset.card_biUnion_le.trans hc)


/-- Concrete arithmetic at the worst state of the exploratory 68.3 ledger. -/
def stage (y z d j : ℕ) : UnequalParameters :=
  ⟨262144, 131071, 181363, y, d - j, z, y, d, z⟩

def charge (y z d : ℕ) : ℕ :=
  (∑ j ∈ Finset.Ico 1 d, (stage y z d j).regularCountCap) + 5000000000000




theorem parent_tail_receipt :
    (⟨262144, 131071, 181363, 20131293, 14914, 1⟩ : RCN318.TightParameters).countCap =
      4677353824485 := by decide +kernel

/-- This checks a scalar ledger only, not the missing phase bound or ProtocolClaim. -/
theorem worst_state_ledger :
    271848174527595670 + 29 * 85564688689540 + 4 * 5000000000000 +
      2 * 5000000000000 + 531797511073303 < 274980723107224037 := by decide +kernel

end
end ProximityPrize.SubmissionLower.BoundaryTailSharedDegreeBudget





/-!
Sharper derivative-chain accounting. The derivative polynomial supplies the
agreement equations, so its own degrees suffice in the agreement numerator.
The right-hand polynomial supplies the geometric intersection only. The Y/Z
caps below apply to the derivative itself and may therefore also use the
weighted degree lost under repeated R differentiation.

The aggregation structure is adapted from the promoted submission and the
actual-degree chain proof from jsign's PR506; the asymmetric numerator and
separate derivative caps are the changes made here.
-/
namespace ProximityPrize.SubmissionLower.BoundaryTailChainHelper
open AsymmetricHelper
open scoped Classical BigOperators
open RCN238 RCN081 RCN071 RCN167 RCN174 RCN319 RCN052 RCN260 RCN313 RCN294
  LocatorDerivativeChain BoundaryTailSharedDegreeBudget
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

/-- Nonzero derivatives lose their iteration count from both cumulative
middle and total degree. These caps can be passed directly to the chain
count theorem below. -/
theorem dR_middle_total_caps (F : MvPolynomial (Fin 4) K) (j y t : ℕ)
    (hne : dR j F ≠ 0)
    (hy : RCN234.wt RCN156.residualYSWeights F ≤ y)
    (ht : RCN234.wt RCN156.residualTotalWeights F ≤ t) :
    (dR j F).degreeOf 1 ≤ y - j ∧
      (dR j F).degreeOf 3 ≤ t - j := by
  have hdy := LocatorArbitraryPowerContact.iteratePderivR_weight_le_sub
    RCN156.residualYSWeights F j y hne hy
  have hdt := LocatorArbitraryPowerContact.iteratePderivR_weight_le_sub
    RCN156.residualTotalWeights F j t hne ht
  constructor
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    have h := MvPolynomial.le_weightedTotalDegree RCN156.residualYSWeights hd
    rw [RCN081.weight_fin4] at h
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
      RCN234.wt RCN156.residualYSWeights (dR j F) at h
    change RCN234.wt RCN156.residualYSWeights (dR j F) ≤ y - j * 1 at hdy
    omega
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    have h := MvPolynomial.le_weightedTotalDegree RCN156.residualTotalWeights hd
    rw [RCN081.weight_fin4] at h
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
      RCN234.wt RCN156.residualTotalWeights (dR j F) at h
    change RCN234.wt RCN156.residualTotalWeights (dR j F) ≤ t - j * 1 at hdt
    omega

theorem sum_regular_counts_bound_left
   (P:UnequalParameters) (Q T:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hcost:
     (∑ F:RegularIndex Q,(regularVector P F.1).y) ≤ P.mixedCost.y∧
     (∑ F:RegularIndex Q,(regularVector P F.1).r) ≤ P.mixedCost.r∧
     (∑ F:RegularIndex Q,(regularVector P F.1).z) ≤ P.mixedCost.z)
   (hcount:∀ F:RegularIndex Q,
     (regularPairSeeds Q T selected Gamma F).card*P.gap ≤
       (P.n-P.w)*dot P.leftAgreement (regularVector P F.1)+
         (P.errors+1)*P.gap*(regularVector P F.1).z):
   (∑ F:RegularIndex Q,(regularPairSeeds Q T selected Gamma F).card)*
       P.gap ≤ leftRegularNumerator P:=by
 calc
   _=∑ F:RegularIndex Q,
       (regularPairSeeds Q T selected Gamma F).card*P.gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ F:RegularIndex Q,
       ((P.n-P.w)*dot P.leftAgreement (regularVector P F.1)+
         (P.errors+1)*P.gap*(regularVector P F.1).z):=
     Finset.sum_le_sum fun F _↦hcount F
   _=(P.n-P.w)*dot P.leftAgreement
         (RCN294.sumVector fun F:RegularIndex Q↦
           regularVector P F.1)+
       (P.errors+1)*P.gap*
         (RCN294.sumVector fun F:RegularIndex Q↦
           regularVector P F.1).z:=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,
       ←dot_sum_right]
     simp only [RCN294.sumVector]
   _ ≤ (P.n-P.w)*dot P.leftAgreement P.mixedCost+
       (P.errors+1)*P.gap*P.mixedCost.z:=by
     apply Nat.add_le_add
     · exact Nat.mul_le_mul_left _ (Nat.add_le_add
         (Nat.add_le_add
           (Nat.mul_le_mul_left P.leftAgreement.y hcost.1)
           (Nat.mul_le_mul_left P.leftAgreement.r hcost.2.1))
         (Nat.mul_le_mul_left P.leftAgreement.z hcost.2.2))
     · exact Nat.mul_le_mul_left _ hcost.2.2
   _=leftRegularNumerator P:=rfl

theorem chainSeeds_card_le_left
    (P : UnequalParameters) (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (p : ℕ) [CharP K p] (hpos : 0 < F.degreeOf 2) (hsmall : F.degreeOf 2 < p)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ chainLength F)
    (hgap : 0 < P.gap)
    (hY : (dR j F).degreeOf 1 ≤ P.leftY) (hR : F.degreeOf 2 - j ≤ P.leftR)
    (hZ : (dR j F).degreeOf 3 ≤ P.leftZ)
    (hY' : F.degreeOf 1 ≤ P.rightY) (hR' : F.degreeOf 2 ≤ P.rightR)
    (hZ' : F.degreeOf 3 ≤ P.rightZ)
    (hleftR : 1 ≤ P.leftR)
    (hleftYSmall : P.leftY < p) (hleftRSmall : P.leftR < p) (hleftZSmall : P.leftZ < p)
    (hmixedYSmall : P.mixedCost.y < p) (hmixedRSmall : P.mixedCost.r < p)
    (hmixedZSmall : P.mixedCost.z < p)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = P.n) (hw : 1 ≤ P.w) (hchar : P.w < p)
    (hwa : P.w < P.a) (han : P.a ≤ P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma, P.a ≤ (nodes.filter (fun i =>
      (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma P.w P.errors) :
    (chainSeeds F j selected Gamma).card ≤ leftRegularCountCap P := by
  have hne := dR_ne_zero F hF.ne_zero p hsmall j hj
  have hrel := isRelPrime_dR F hF p hpos hsmall j hj1 hj
  have hy := hY
  have hr := (dR_R_degree_le j F).trans hR
  have hz := hZ
  have hcount (G : RegularIndex (dR j F)) := regularPairSeeds_bound_left P (dR j F) F hrel G p
    ((degreeOf_le_of_dvd 1 G.1 (dR j F) (positiveRFactors_spec _ _ G.2).2.1 hne).trans hy)
    ((degreeOf_le_of_dvd 2 G.1 (dR j F) (positiveRFactors_spec _ _ G.2).2.1 hne).trans hr)
    ((degreeOf_le_of_dvd 3 G.1 (dR j F) (positiveRFactors_spec _ _ G.2).2.1 hne).trans hz)
    hY' hR' hZ' hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall selected Gamma nodes x u0 u1
    hinj hnodes hw hchar hwa han hdegree hagreement hno
  have hsum := sum_regular_counts_bound_left P (dR j F) F selected Gamma
    (regularVector_budgets_actual P (dR j F) hne hy hr hz) hcount
  have hc : (∑ G : RegularIndex (dR j F),
      (regularPairSeeds (dR j F) F selected Gamma G).card) ≤ leftRegularCountCap P :=
    (Nat.le_div_iff_mul_le hgap).mpr hsum
  exact (Finset.card_le_card (chainSeeds_subset_regularPairSeeds F j hne selected Gamma)).trans
    (Finset.card_biUnion_le.trans hc)



end
end ProximityPrize.SubmissionLower.BoundaryTailChainHelper


/-! Carrier-only chain accounting at error 80811. The polynomial endpoint
argument is adapted from jsign PR506's shared-chain proof. Using the derivative
carrier's agreement degrees replaces its old cross term by the smaller one
proved in `stageNumerator` below. This file alone is not a protocol claim. -/
namespace ProximityPrize.SubmissionLower.AsymmetricChainPolynomial80811
open scoped BigOperators
open RCN238 RCN223 RCN260 RCN313 RCN294 BoundaryTailChainHelper AsymmetricHelper
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def stage (y z d j : ℕ) : UnequalParameters :=
  ⟨262144,131071,181333,y,d-j,z,y,d,z⟩

def charge (y z d : ℕ) : ℕ :=
  (∑ j ∈ Finset.Ico 1 d, leftRegularCountCap (stage y z d j)) + 9000000000000

def kTerm (y z : ℕ) : ℕ :=
  131073 * (z + y + 524284*y*z) + 50262*80812*y
def mTerm (y z : ℕ) : ℕ := 131073*131071*y*z

theorem stageNumerator (y z d j : ℕ) (hj : j ≤ d) :
    leftRegularNumerator (stage y z d j) =
      (2*d-j)*kTerm y z + (2*(d-j)-1)*2*mTerm y z := by
  simp only [stage, leftRegularNumerator, UnequalParameters.gap,
    UnequalParameters.errors, UnequalParameters.leftAgreement,
    UnequalParameters.mixedCost, dot]
  norm_num only
  have hsub : (d-j)+d = 2*d-j := by omega
  dsimp [kTerm, mTerm]
  calc
    _ = ((d-j)+d) * (131073*(z+y+524284*y*z)+50262*80812*y) +
        (2*(d-j)-1)*2*(131073*131071*y*z) := by ring
    _ = _ := by rw [hsub]

def numerator (y z d : ℕ) : ℕ :=
  (d-1)*(3*d*kTerm y z + 4*mTerm y z*(d-1)) + 2*50262*9000000000000

theorem sum_stage_numerators (y z d : ℕ) (hd : d ≤ 33) :
    2 * (∑ j ∈ Finset.Ico 1 d, leftRegularNumerator (stage y z d j)) =
      (d-1)*(3*d*kTerm y z + 4*mTerm y z*(d-1)) := by
  have heq : (∑ j ∈ Finset.Ico 1 d, leftRegularNumerator (stage y z d j)) =
      ∑ j ∈ Finset.Ico 1 d, ((2*d-j)*kTerm y z + (2*(d-j)-1)*(2*mTerm y z)) := by
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [Nat.mul_assoc] using stageNumerator y z d j (Finset.mem_Ico.mp hj).2.le
  have hsum : 2 * (∑ j ∈ Finset.Ico 1 d, (2*d-j)) = 3*d*(d-1) := by
    interval_cases d <;> decide +kernel
  have hsum' : (∑ j ∈ Finset.Ico 1 d, (2*(d-j)-1)) = (d-1)*(d-1) := by
    interval_cases d <;> decide +kernel
  rw [heq, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hsum']
  nlinarith only [congrArg (fun x => x * kTerm y z) hsum]

theorem charge_mul_le (y z d : ℕ) (hd : d ≤ 33) :
    charge y z d * (2*50262) ≤ numerator y z d := by
  have hsum : (∑ j ∈ Finset.Ico 1 d, leftRegularCountCap (stage y z d j))*50262 ≤
      ∑ j ∈ Finset.Ico 1 d, leftRegularNumerator (stage y z d j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    simp only [leftRegularCountCap, UnequalParameters.gap, stage,
      (show (181333 - 131071 : ℕ) = 50262 by decide +kernel)]
    exact Nat.div_mul_le_self _ _
  have heq := sum_stage_numerators y z d hd
  dsimp [charge, numerator]
  nlinarith


/-- Endpoint domination for a convex quadratic after division by its positive index. -/
theorem quadratic_between (A C W r d : ℤ)
    (hA : 0 ≤ A) (hd : 1 ≤ d) (hdr : d ≤ r)
    (h1 : A + C ≤ W) (hr : A*r*r+C ≤ W*r) :
    A*d*d+C ≤ W*d := by
  by_cases hreq : r = 1
  · have hdeq : d = 1 := by omega
    simpa [hdeq] using h1
  have hr1 : 0 < r-1 := by omega
  have hp := mul_le_mul_of_nonneg_right h1 (show 0 ≤ r-d by omega)
  have hq := mul_le_mul_of_nonneg_right hr (show 0 ≤ d-1 by omega)
  have hc : 0 ≤ A*(r-1)*(d-1)*(r-d) :=
    mul_nonneg (mul_nonneg (mul_nonneg hA (by omega)) (by omega)) (by omega)
  have hm : (r-1)*(A*d*d+C) ≤ (r-1)*(W*d) := by nlinarith
  exact (mul_le_mul_iff_right₀ hr1).mp hm

theorem numerator_identity (y z d : ℕ) (hd : 1 ≤ d) :
    (numerator y z d : ℤ) + d*(3*(kTerm y z : ℤ)+8*(mTerm y z : ℤ)) =
      (3*(kTerm y z : ℤ)+4*(mTerm y z : ℤ))*d*d +
        4*(mTerm y z : ℤ)+2*50262*9000000000000 := by
  unfold numerator
  have h2 : 1 ≤ 2*d := by omega
  push_cast [Nat.cast_sub hd, Nat.cast_sub h2]
  ring

theorem charge_le_of_endpoints (y z d r u : ℕ)
    (hd : 1 ≤ d) (hdr : d ≤ r) (hr : r ≤ 33)
    (htail : 9000000000000 ≤ u)
    (hend : numerator y z r ≤ r*(2*50262)*u) :
    charge y z d ≤ d*u := by
  have hn1 := numerator_identity y z 1 (by decide +kernel)
  have hnr := numerator_identity y z r (by omega)
  have hnd := numerator_identity y z d hd
  have he : (numerator y z d : ℤ) ≤ d*(2*50262)*(u : ℤ) := by
    have htc : (9000000000000 : ℤ) ≤ u := by exact_mod_cast htail
    have hec : (numerator y z r : ℤ) ≤ r*(2*50262)*(u : ℤ) := by exact_mod_cast hend
    have h := quadratic_between
      (3*(kTerm y z : ℤ)+4*(mTerm y z : ℤ))
      (4*(mTerm y z : ℤ)+2*50262*9000000000000)
      ((2*50262)*(u : ℤ)+3*(kTerm y z : ℤ)+8*(mTerm y z : ℤ))
      r d (by positivity) (by exact_mod_cast hd) (by exact_mod_cast hdr)
      (by nlinarith) (by nlinarith)
    nlinarith
  have hn : numerator y z d ≤ d*(2*50262)*u := by exact_mod_cast he
  have hcharge := (charge_mul_le y z d (hdr.trans hr)).trans hn
  nlinarith


def zCoeff (y d : ℕ) : ℕ :=
  (d-1)*(3*d*131073*(1+524284*y)+4*131073*131071*y*(d-1))
def constant (y d : ℕ) : ℕ :=
  (d-1)*3*d*(131073+50262*80812)*y + 2*50262*9000000000000

theorem numerator_linear (y z d : ℕ) :
    numerator y z d = zCoeff y d*z + constant y d := by
  unfold numerator kTerm mTerm zCoeff constant
  ring

def unitSlope (y d : ℕ) : ℕ := zCoeff y d / (2*50262*d) + 1
def unitConstant (y d : ℕ) : ℕ := constant y d / (2*50262*d) + 1
def unit (y z d : ℕ) : ℕ :=
  max 9000000000000 (unitSlope y d*z + unitConstant y d)

private theorem le_roundUp_mul (a b : ℕ) (hb : 0 < b) : a ≤ (a/b+1)*b := by
  have hm := Nat.mod_lt a hb
  have he := Nat.mod_add_div a b
  nlinarith

theorem unit_end (y z r : ℕ) (hr : 1 ≤ r) :
    numerator y z r ≤ r*(2*50262)*unit y z r := by
  have hb : 0 < 2*50262*r := by omega
  have ha := le_roundUp_mul (zCoeff y r) (2*50262*r) hb
  have hc := le_roundUp_mul (constant y r) (2*50262*r) hb
  have ham := Nat.mul_le_mul_right z ha
  have hmax : unitSlope y r*z + unitConstant y r ≤ unit y z r := le_max_right _ _
  rw [numerator_linear]
  change zCoeff y r*z + constant y r ≤ _
  dsimp [unitSlope, unitConstant] at hmax
  norm_num only [Nat.reduceMul] at ha hc ham ⊢
  nlinarith [Nat.mul_le_mul_left (100570*r) hmax]

theorem charge_le_unit (y z d r : ℕ) (hd : 1 ≤ d) (hdr : d ≤ r) (hr : r ≤ 33) :
    charge y z d ≤ d*unit y z r :=
  charge_le_of_endpoints y z d r (unit y z r) hd hdr hr
    (le_max_left _ _) (unit_end y z r (by omega))

end ProximityPrize.SubmissionLower.AsymmetricChainPolynomial80811


/-! Shared factor-family counting for the proposed error-80811 profile.
The aggregation framework is adapted from jsign PR506. Its AsymmetricChainPolynomial80811.stage count is
replaced by the checked derivative-carrier numerator and polynomial bound.
This module does not assert a protocol claim. -/

namespace ProximityPrize.SubmissionLower.Lower80811.Counting
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238
  RCN243 RCN260 RCN267 RCN275 RCN286 RCN294 RCN303 RCN313 RCN318 RCN319
open LocatorDerivativeChain BoundaryTailSharedDegreeBudget AsymmetricChainPolynomial80811 BoundaryTailChainHelper AsymmetricHelper
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600
local instance : StrongNormalizationMonoid P4 := UniqueFactorizationMonoid.strongNormalizationMonoid

structure Input (u0 u1 : I → K) (selected : K → Polynomial K) (Gamma : Finset K) : Prop where
  degree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071
  agreement : ∀ gamma ∈ Gamma, 181333 ≤ ((Finset.univ : Finset I).filter (fun i =>
    (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma*u1 i)).card
  noPencil : NoLargeSelectedPencil selected Gamma 131071 80811

variable {u0 u1 : I → K} {selected : K → Polynomial K} {Gamma : Finset K}

theorem Input.restrict (inp : Input u0 u1 selected Gamma) (Delta : Finset K) (h : Delta ⊆ Gamma) :
    Input u0 u1 selected Delta :=
  ⟨fun g hg => inp.degree g (h hg), fun g hg => inp.agreement g (h hg),
    noLargeSelectedPencil_mono selected Gamma Delta 131071 80811 h inp.noPencil⟩

def tailParameters : TightParameters := ⟨262144,131071,181333,20127963,27312,1⟩

theorem freePolynomial_count (inp : Input u0 u1 selected Gamma)
    (J : P4) (hJ : J ≠ 0) (hbox : J ∈ RCN174.globalCoefficientBox K 20127963 131071 27312 1)
    (hR : J.degreeOf 2 = 0) (hsol : ∀ g ∈ Gamma, specialization K (selected g) g J = 0) :
    Gamma.card ≤ 9000000000000 := by
  have h := rfree_seed_count_le tailParameters J hJ 2130706433 hbox hR (by rfl)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num [tailParameters, TightParameters.kappa])
    (by norm_num [tailParameters, TightParameters.algebraicCap, TightParameters.kappa])
    (by norm_num [tailParameters, TightParameters.implicitYCap, TightParameters.kappa])
    (by norm_num [tailParameters, TightParameters.algebraicCap, TightParameters.kappa])
    (by norm_num [tailParameters, TightParameters.implicitYCap, TightParameters.algebraicCap, TightParameters.kappa])
    (by decide +kernel) (by decide +kernel) selected Gamma Finset.univ IRSProfile.domain u0 u1
    IRSProfile.domain.injective.injOn (by rw [Finset.card_univ]; exact Fintype.card_fin _)
    inp.degree hsol inp.agreement (by
      simpa only [tailParameters, TightParameters.errors, (show (262144 - 181333 : ℕ) = 80811 by decide +kernel)] using inp.noPencil)
  have ht : tailParameters.countCap ≤ 9000000000000 := by
    norm_num [tailParameters, TightParameters.countCap, TightParameters.gap,
      TightParameters.errors, TightParameters.kappa, TightParameters.algebraicCap,
      TightParameters.implicitYCap, TightParameters.tightNumerator,
      TightParameters.coreNumerator, TightParameters.agreement,
      TightParameters.aggregateCost, RCN294.dot]
  exact h.trans ht

theorem factor_tail_count (inp : Input u0 u1 selected Gamma)
    (F : P4) (hF : F ≠ 0) (hbox : F ∈ RCN174.globalCoefficientBox K 20127963 131071 27312 33) :
    (tailSeeds F selected Gamma).card ≤ 9000000000000 := by
  have hsmall : F.degreeOf 2 < 2130706433 :=
    (degreeOf_R_le_of_mem_box F 20127963 131071 27312 33 hbox).trans_lt (by decide +kernel)
  have hJ := dR_ne_zero F hF 2130706433 hsmall (chainLength F) le_rfl
  have hb := mem_box_slope_one (dR (chainLength F) F) 20127963 131071 27312 33
    (dR_mem_box _ F 20127963 131071 27312 33 hbox) (chainLength_spec F)
  exact freePolynomial_count (inp.restrict _ (tailSeeds_subset F selected Gamma)) _ hJ hb
    (chainLength_spec F) (fun _ hg => (Finset.mem_filter.mp hg).2)

theorem freePart_count (inp : Input u0 u1 selected Gamma)
    (Q : P4) (hQ : Q ≠ 0) (hbox : Q ∈ RCN174.globalCoefficientBox K 20127963 131071 27312 33) :
    (rfreeSeeds Q selected Gamma).card ≤ 9000000000000 := by
  have hb := mem_box_slope_one (rfreeProduct Q) 20127963 131071 27312 33
    (mem_globalCoefficientBox_of_dvd _ Q 20127963 131071 27312 33 hQ
      (rfreeProduct_dvd Q hQ) hbox) (rfreeProduct_R_degree Q)
  exact freePolynomial_count (inp.restrict _ (rfreeSeeds_subset Q selected Gamma)) _
    (rfreeProduct_ne_zero Q hQ) hb (rfreeProduct_R_degree Q)
    (fun _ hg => (Finset.mem_filter.mp hg).2)

def factorCharge (F : P4) (selected : K → Polynomial K) (Gamma : Finset K) : ℕ :=
  (∑ j ∈ Finset.Ico 1 (chainLength F), (chainSeeds F j selected Gamma).card) +
    (tailSeeds F selected Gamma).card

theorem factorCharge_le_unit (inp : Input u0 u1 selected Gamma)
    (F : P4) (hF : Irreducible F) (hpos : 0 < F.degreeOf 2)
    (hbox : F ∈ RCN174.globalCoefficientBox K 20127963 131071 27312 33)
    (y z r : ℕ) (hy : y ≤ 153) (hz : z ≤ 27312) (hr : r ≤ 33)
    (hFY : F.degreeOf 1 ≤ y) (hFZ : F.degreeOf 3 ≤ z) (hFR : F.degreeOf 2 ≤ r) :
    factorCharge F selected Gamma ≤ F.degreeOf 2 * unit y z r := by
  have hd : F.degreeOf 2 ≤ 33 := hFR.trans hr
  apply BoundaryTailDegreeAwareChain.factor_charge_le F selected Gamma
    (fun j => leftRegularCountCap (AsymmetricChainPolynomial80811.stage y z (F.degreeOf 2) j)) 9000000000000 (unit y z r)
  · intro j hj
    have hj1 := (Finset.mem_Ico.mp hj).1
    have hjl := (Finset.mem_Ico.mp hj).2
    have hjd : j < F.degreeOf 2 := hjl.trans_le (chainLength_le F)
    have hleft : F.degreeOf 2-j ≤ 33 := (Nat.sub_le _ _).trans hd
    exact BoundaryTailChainHelper.chainSeeds_card_le_left (AsymmetricChainPolynomial80811.stage y z (F.degreeOf 2) j) F hF 2130706433
      hpos (hd.trans_lt (by decide +kernel)) j hj1 hjl.le
      (by norm_num [AsymmetricChainPolynomial80811.stage, UnequalParameters.gap])
      ((dR_degree_le j F 1).trans hFY) le_rfl
      ((dR_degree_le j F 3).trans hFZ) hFY le_rfl hFZ
      (by dsimp [AsymmetricChainPolynomial80811.stage]; omega) (by dsimp [AsymmetricChainPolynomial80811.stage]; omega) (by dsimp [AsymmetricChainPolynomial80811.stage]; omega)
      (by dsimp [AsymmetricChainPolynomial80811.stage]; omega)
      (by
        dsimp [AsymmetricChainPolynomial80811.stage, UnequalParameters.mixedCost]
        exact (Nat.add_le_add (Nat.mul_le_mul hleft hz) (Nat.mul_le_mul hz hd)).trans_lt (by decide +kernel))
      (by
        dsimp [AsymmetricChainPolynomial80811.stage, UnequalParameters.mixedCost]
        exact (Nat.add_le_add (Nat.mul_le_mul hy hz) (Nat.mul_le_mul hz hy)).trans_lt (by decide +kernel))
      (by
        dsimp [AsymmetricChainPolynomial80811.stage, UnequalParameters.mixedCost]
        exact (Nat.add_le_add (Nat.mul_le_mul hy hd) (Nat.mul_le_mul hleft hy)).trans_lt (by decide +kernel))
      selected Gamma Finset.univ IRSProfile.domain u0 u1 IRSProfile.domain.injective.injOn
      (by rw [Finset.card_univ]; exact Fintype.card_fin _) (by norm_num [AsymmetricChainPolynomial80811.stage]) (by norm_num [AsymmetricChainPolynomial80811.stage]) (by norm_num [AsymmetricChainPolynomial80811.stage]) (by norm_num [AsymmetricChainPolynomial80811.stage])
      inp.degree inp.agreement (by simpa only [AsymmetricChainPolynomial80811.stage, UnequalParameters.errors, (show (262144 - 181333 : ℕ) = 80811 by decide +kernel)] using inp.noPencil)
  · exact factor_tail_count inp F hF.ne_zero hbox
  · exact charge_le_unit y z (F.degreeOf 2) r hpos hFR hr

end
end ProximityPrize.SubmissionLower.Lower80811.Counting



namespace ProximityPrize.SubmissionLower.Lower80811.Budgets
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN071 RCN081 RCN095 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN243 RCN260 RCN266 RCN319
open RCN286 RCN267 RCN180 LocatorBatchProductRoute
open LocatorFactorAggregate LocatorBatchPhase6800 LocatorPhase6800Oracle Counting BoundaryTailSharedDegreeBudget AsymmetricChainPolynomial80811
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _

theorem degreeY_le (F : P4) : F.degreeOf 1 ≤ wt residualYSWeights F := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*0 ≤ wt residualYSWeights F at h
  omega

theorem degreeZ_le (F : P4) : F.degreeOf 3 ≤ wt residualTotalWeights F := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*1 ≤ wt residualTotalWeights F at h
  omega

theorem factor_coordinates (H : P4) (A : Finset (RegularIndex H)) (F : RegularIndex H) (hF : F ∈ A) :
    F.1.degreeOf 1 ≤ middle (regularAggregateFlag H A) ∧
    F.1.degreeOf 2 ≤ (regularAggregateFlag H A).all ∧
    F.1.degreeOf 3 ≤ total (regularAggregateFlag H A) := by
  have hm := regularAggregateFlag_mono H (Finset.singleton_subset_iff.mpr hF)
  have hc := originalCumulativeFlag_cumulative F.1
  have hy : F.1.degreeOf 1 ≤ middle (regularCumulativeFlag H F) := by
    rw [regularCumulativeFlag, middle, hc.2.1]
    exact degreeY_le F.1
  have hz : F.1.degreeOf 3 ≤ total (regularCumulativeFlag H F) := by
    rw [regularCumulativeFlag, total, hc.2.2]
    exact degreeZ_le F.1
  have hr : F.1.degreeOf 2 = (regularCumulativeFlag H F).all := by
    rw [regularCumulativeFlag, originalCumulativeFlag_all]
  simpa only [regularAggregateFlag, sumFlag, Finset.sum_singleton] using
    And.intro (hy.trans hm.2.1) (And.intro (hr.le.trans hm.1) (hz.trans hm.2.2))

theorem aggregate_pair_weight (H Q : P4) (hH : H ≠ 0) (hQ : Q ≠ 0) (weights : Fin 4 → ℕ) :
    wt weights (regularProduct H Finset.univ) + wt weights (regularProduct Q Finset.univ) ≤
      wt weights (H*Q) := by
  simp only [wt]
  rw [weightedTotalDegree_mul weights H Q hH hQ]
  exact Nat.add_le_add
    (weightedTotalDegree_le_of_dvd weights _ H (regularProduct_dvd_carrier H _) hH)
    (weightedTotalDegree_le_of_dvd weights _ Q (regularProduct_dvd_carrier Q _) hQ)

theorem aggregate_pair_caps (H Q : P4) (hH : H ≠ 0) (hQ : Q ≠ 0)
    (hbox : H*Q ∈ RCN100.globalCoefficientBox K 20127963 131071 27312 33) :
    (regularAggregateFlag H Finset.univ).all+(regularAggregateFlag Q Finset.univ).all ≤ 33 ∧
    middle (regularAggregateFlag H Finset.univ)+middle (regularAggregateFlag Q Finset.univ) ≤ 153 ∧
    total (regularAggregateFlag H Finset.univ)+total (regularAggregateFlag Q Finset.univ) ≤ 27312 := by
  have hc := (mem_flagGlobalCoefficientBox_iff (H*Q) 20127963 131071 27312 33 (by decide +kernel)).mp hbox
  have hw := residualYS_mul_le_contact_add_slope (H*Q) 131071 (by decide +kernel)
  have hy : wt residualYSWeights (H*Q) ≤ 153 := by omega
  rw [regularAggregateFlag_all, regularAggregateFlag_all,
    regularAggregateFlag_middle, regularAggregateFlag_middle,
    regularAggregateFlag_total, regularAggregateFlag_total]
  exact ⟨(aggregate_pair_weight H Q hH hQ _).trans hc.2.1,
    (aggregate_pair_weight H Q hH hQ _).trans hy,
    (aggregate_pair_weight H Q hH hQ _).trans hc.1⟩

theorem split_aggregate (H : P4) (U : Finset (RegularIndex H)) :
    let N := (Finset.univ : Finset (RegularIndex H)) \ U
    (regularAggregateFlag H U).all+(regularAggregateFlag H N).all = (regularAggregateFlag H Finset.univ).all ∧
    middle (regularAggregateFlag H U)+middle (regularAggregateFlag H N) = middle (regularAggregateFlag H Finset.univ) ∧
    total (regularAggregateFlag H U)+total (regularAggregateFlag H N) = total (regularAggregateFlag H Finset.univ) := by
  simp only [regularAggregateFlag, sumFlag_all, sumFlag_middle, sumFlag_total]
  exact ⟨by rw [Nat.add_comm]; exact Finset.sum_sdiff (Finset.subset_univ _),
    by rw [Nat.add_comm]; exact Finset.sum_sdiff (Finset.subset_univ _),
    by rw [Nat.add_comm]; exact Finset.sum_sdiff (Finset.subset_univ _)⟩

theorem joint_charge (H Q : P4) (hH : H ≠ 0) (hQ : Q ≠ 0)
    (hbox : H*Q ∈ RCN100.globalCoefficientBox K 20127963 131071 27312 33)
    (hHbox : H ∈ RCN174.globalCoefficientBox K 20127963 131071 27312 33)
    (hQbox : Q ∈ RCN174.globalCoefficientBox K 20127963 131071 27312 33)
    (U : Finset (RegularIndex H)) (u0 u1 : I → K) (selected : K → Polynomial K)
    (Gamma Delta : Finset K) (inpH : Input u0 u1 selected Gamma) (inpQ : Input u0 u1 selected Delta)
    (hr : (regularAggregateFlag H U).all ≤ 31)
    (hy : middle (regularAggregateFlag H U) ≤ 142)
    (ht : total (regularAggregateFlag H U) ≤ 7501) :
    let p := regularAggregateFlag H U
    (∑ F : RegularIndex H, factorCharge F.1 selected Gamma) +
      (∑ F : RegularIndex Q, factorCharge F.1 selected Delta) ≤
      p.all*unit (middle p) (total p) p.all +
      (33-p.all)*unit (153-middle p) (27312-total p) (33-p.all) := by
  let p := regularAggregateFlag H U
  let N := (Finset.univ : Finset (RegularIndex H)) \ U
  have hb := aggregate_pair_caps H Q hH hQ hbox
  have hs := split_aggregate H U
  have hnR : (regularAggregateFlag H N).all ≤ 33-p.all := by dsimp only [p,N]; omega
  have hnY : middle (regularAggregateFlag H N) ≤ 153-middle p := by dsimp only [p,N]; omega
  have hnT : total (regularAggregateFlag H N) ≤ 27312-total p := by dsimp only [p,N]; omega
  have hqR : (regularAggregateFlag Q Finset.univ).all ≤ 33-p.all := by dsimp only [p]; omega
  have hqY : middle (regularAggregateFlag Q Finset.univ) ≤ 153-middle p := by dsimp only [p]; omega
  have hqT : total (regularAggregateFlag Q Finset.univ) ≤ 27312-total p := by dsimp only [p]; omega
  have hsum : (∑ F ∈ U, F.1.degreeOf 2) = p.all := by
    simp only [p, regularAggregateFlag, sumFlag_all, regularCumulativeFlag, originalCumulativeFlag_all]
  have hprodBox := RCN101.flag_box_to_ordinary K 20127963 131071 27312 33 (H*Q) hbox
  have hc := split_slope_charge (Finset.univ : Finset (RegularIndex H)) U
    (Finset.univ : Finset (RegularIndex Q)) (Finset.subset_univ _) (fun F => F.1) (fun F => F.1)
    H Q hH hQ (regularProduct_dvd_carrier H _) (regularProduct_dvd_carrier Q _)
    33 (unit (middle p) (total p) p.all) (unit (153-middle p) (27312-total p) (33-p.all))
    (degreeOf_R_le_of_mem_box (H*Q) 20127963 131071 27312 33 hprodBox)
    (fun F => factorCharge F.1 selected Gamma) (fun F => factorCharge F.1 selected Delta)
    (fun F hF => by
      have hf := directFactor_data H F.1 hH 20127963 131071 27312 33 hHbox F.2
      have hd := factor_coordinates H U F hF
      exact factorCharge_le_unit inpH F.1 hf.1 hf.2.1 hf.2.2 _ _ _
        (hy.trans (by decide +kernel)) (ht.trans (by decide +kernel)) (hr.trans (by decide +kernel)) hd.1 hd.2.2 hd.2.1)
    (fun F hF => by
      have hf := directFactor_data H F.1 hH 20127963 131071 27312 33 hHbox F.2
      have hd := factor_coordinates H N F hF
      exact factorCharge_le_unit inpH F.1 hf.1 hf.2.1 hf.2.2 _ _ _
        (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _)
        (hd.1.trans hnY) (hd.2.2.trans hnT) (hd.2.1.trans hnR))
    (fun F _ => by
      have hf := directFactor_data Q F.1 hQ 20127963 131071 27312 33 hQbox F.2
      have hd := factor_coordinates Q Finset.univ F (Finset.mem_univ _)
      exact factorCharge_le_unit inpQ F.1 hf.1 hf.2.1 hf.2.2 _ _ _
        (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _)
        (hd.1.trans hqY) (hd.2.2.trans hqT) (hd.2.1.trans hqR))
  simpa only [hsum] using hc

end
end ProximityPrize.SubmissionLower.Lower80811.Budgets
