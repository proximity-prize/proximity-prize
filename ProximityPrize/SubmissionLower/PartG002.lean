import ProximityPrize.SubmissionLower.PartG001


section Compact_AsymmetricLocator
namespace ProximityPrize.SubmissionLower.AsymmetricHelper
open scoped Classical BigOperators
open UniqueFactorizationMonoid RCN081 RCN156 RCN234 RCN260 LocatorCoprimeQuotient
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

def leftRegularNumerator (P : UnequalParameters) : ℕ :=
  (P.n - P.w) * RCN294.dot P.leftAgreement P.mixedCost +
    (P.errors + 1) * P.gap * P.mixedCost.z

def leftRegularCountCap (P : UnequalParameters) : ℕ :=
  leftRegularNumerator P / P.gap




theorem leftRegularNumerator_le (P : UnequalParameters) :
    leftRegularNumerator P ≤ P.regularNumerator := by
  have hdot : RCN294.dot P.leftAgreement P.mixedCost ≤
      RCN294.dot P.agreement P.mixedCost := by
    unfold RCN294.dot UnequalParameters.agreement
    exact Nat.add_le_add
      (Nat.add_le_add
        (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
        (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)))
      (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hdot) _
theorem regularSeeds_count_le_left_intersection
    (P:UnequalParameters) (H Q:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H) (hrel:IsRelPrime F.1 Q)
    (p:ℕ) [CharP K p]
    (hFY:F.1.degreeOf 1 ≤ P.leftY) (hFR:F.1.degreeOf 2 ≤ P.leftR)
    (hFZ:F.1.degreeOf 3 ≤ P.leftZ)
    (hQY:Q.degreeOf 1 ≤ P.rightY) (hQR:Q.degreeOf 2 ≤ P.rightR)
    (hQZ:Q.degreeOf 3 ≤ P.rightZ)
    (hleftR:1 ≤ P.leftR)
    (hleftYSmall:P.leftY < p) (hleftRSmall:P.leftR < p)
    (hleftZSmall:P.leftZ < p)
    (hmixedYSmall:P.mixedCost.y < p) (hmixedRSmall:P.mixedCost.r < p)
    (hmixedZSmall:P.mixedCost.z < p)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (nodes:Finset I) (x u0 u1:I → K) (hinj:Set.InjOn x nodes)
    (hnodes:nodes.card = P.n)
    (hw:1 ≤ P.w) (hchar:P.w < p) (hwa:P.w < P.a) (han:P.a ≤ P.n)
    (hdegree:∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement:∀ gamma ∈ Gamma, P.a ≤
      (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hno:RCN238.NoLargeSelectedPencil selected Gamma P.w P.errors)
    (hQzero:∀ gamma ∈ RCN140.regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma Q = 0) :
    (RCN140.regularSeeds H selected Gamma F).card ≤ leftRegularCountCap P:=by
  let Fself:=regularIndexSelf H F
  have hcount:=regularPairSeeds_bound_left P F.1 Q hrel Fself p
    hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall
    selected Gamma nodes x u0 u1 hinj hnodes hw hchar hwa han hdegree hagreement hno
  have heq:RCN052.regularPairSeeds F.1 Q selected Gamma Fself =
      RCN140.regularSeeds H selected Gamma F:=by
    ext gamma
    simp only [RCN052.regularPairSeeds, RCN140.regularSeeds, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, h.2.1⟩
    · intro h
      exact ⟨h.1, h.2, hQzero gamma (Finset.mem_filter.mpr h)⟩
  rw [heq] at hcount
  have hv:=regularVector_le_mixedCost P F.1 hFY hFR hFZ
  have hdot:RCN294.dot P.leftAgreement (RCN052.regularVector P F.1) ≤
      RCN294.dot P.leftAgreement P.mixedCost :=
    Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left P.leftAgreement.y hv.1)
        (Nat.mul_le_mul_left P.leftAgreement.r hv.2.1))
      (Nat.mul_le_mul_left P.leftAgreement.z hv.2.2)
  unfold leftRegularCountCap
  apply (Nat.le_div_iff_mul_le (by unfold UnequalParameters.gap; omega)).mpr
  exact hcount.trans (Nat.add_le_add (Nat.mul_le_mul_left (P.n - P.w) hdot)
    (Nat.mul_le_mul_left ((P.errors + 1) * P.gap) hv.2.2))

end
end ProximityPrize.SubmissionLower.AsymmetricHelper

end Compact_AsymmetricLocator
