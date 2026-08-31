import ProximityPrize.SubmissionLower.DW
import ProximityPrize.SubmissionLower.Z4
import ProximityPrize.SubmissionLower.LocatorLowQuotient
namespace ProximityPrize.SubmissionLower.LocatorCoprimeQuotient
open scoped Classical BigOperators
open UniqueFactorizationMonoid
open RCN081 RCN156 RCN234 RCN260
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:StrongNormalizationMonoid (MvPolynomial (Fin 4) K) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid
theorem isRelPrime_of_weight_lt (weights:Fin 4 → ℕ)
    (F Q:MvPolynomial (Fin 4) K) (hF:Irreducible F) (hQ:Q ≠ 0)
    (hlt:wt weights Q<wt weights F):IsRelPrime F Q:=by
  apply hF.isRelPrime_iff_not_dvd.mpr
  intro hdiv
  exact (not_lt_of_ge (weightedTotalDegree_le_of_dvd weights F Q hdiv hQ)) hlt
theorem isRelPrime_of_weight_sub_bound (weights:Fin 4 → ℕ)
    (F Q:MvPolynomial (Fin 4) K) (hF:Irreducible F) (hQ:Q ≠ 0)
    (B:ℕ) (hbound:wt weights Q≤B - wt weights F)
    (hhalf:B<2*wt weights F):IsRelPrime F Q:=by
  apply isRelPrime_of_weight_lt weights F Q hF hQ
  omega
private theorem regular_mem_normalizedFactors
    (H:MvPolynomial (Fin 4) K) (F:RCN266.RegularIndex H) :
    F.1 ∈ normalizedFactors H:=by
  have hactive:F.1 ∈ RCN082.activeFactors H :=
    (Finset.mem_filter.mp F.2).1
  have hnf:F.1 ∈ (normalizedFactors H).toFinset :=
    (Finset.mem_filter.mp hactive).1
  exact Multiset.mem_toFinset.mp hnf
def regularIndexSelf (H:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H):RCN052.RegularIndex F.1:=by
  have hF:=RCN167.positiveRFactors_spec H F.1 F.2
  refine ⟨F.1,?_⟩
  change F.1 ∈ (RCN082.activeFactors F.1).filter (fun G => 0<G.degreeOf 2)
  refine Finset.mem_filter.mpr ⟨?_,hF.2.2⟩
  change F.1 ∈ (normalizedFactors F.1).toFinset.filter
    (fun G => 0<G.degreeOf 1+G.degreeOf 2+G.degreeOf 3)
  refine Finset.mem_filter.mpr ⟨?_,by omega⟩
  apply Multiset.mem_toFinset.mpr
  rw [normalizedFactors_irreducible hF.1,
    normalize_normalized_factor F.1 (regular_mem_normalizedFactors H F)]
  exact Multiset.mem_singleton_self _
@[simp] theorem regularIndexSelf_val (H:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H):(regularIndexSelf H F).1=F.1:=rfl
theorem regularVector_le_mixedCost (P:UnequalParameters)
    (F:MvPolynomial (Fin 4) K)
    (hY:F.degreeOf 1≤P.leftY) (hR:F.degreeOf 2≤P.leftR)
    (hZ:F.degreeOf 3≤P.leftZ) :
    (RCN052.regularVector P F).y≤P.mixedCost.y ∧
      (RCN052.regularVector P F).r≤P.mixedCost.r ∧
      (RCN052.regularVector P F).z≤P.mixedCost.z:=by
  exact ⟨Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hR)
      (Nat.mul_le_mul_right P.rightR hZ),
    Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hY)
      (Nat.mul_le_mul_right P.rightY hZ),
    Nat.add_le_add (Nat.mul_le_mul_right P.rightR hY)
      (Nat.mul_le_mul_right P.rightY hR)⟩
theorem regularSeeds_count_le_intersection
    (P:UnequalParameters) (H Q:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H) (hrel:IsRelPrime F.1 Q)
    (p:ℕ) [CharP K p]
    (hFY:F.1.degreeOf 1≤P.leftY) (hFR:F.1.degreeOf 2≤P.leftR)
    (hFZ:F.1.degreeOf 3≤P.leftZ)
    (hQY:Q.degreeOf 1≤P.rightY) (hQR:Q.degreeOf 2≤P.rightR)
    (hQZ:Q.degreeOf 3≤P.rightZ)
    (hleftR:1≤P.leftR)
    (hleftYSmall:P.leftY<p) (hleftRSmall:P.leftR<p)
    (hleftZSmall:P.leftZ<p)
    (hmixedYSmall:P.mixedCost.y<p) (hmixedRSmall:P.mixedCost.r<p)
    (hmixedZSmall:P.mixedCost.z<p)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (nodes:Finset I) (x u0 u1:I → K) (hinj:Set.InjOn x nodes)
    (hnodes:nodes.card=P.n)
    (hw:1≤P.w) (hchar:P.w<p) (hwa:P.w<P.a) (han:P.a≤P.n)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree≤P.w)
    (hagreement:∀ gamma ∈ Gamma,P.a ≤
      (nodes.filter (fun i => (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.NoLargeSelectedPencil selected Gamma P.w P.errors)
    (hQzero:∀ gamma ∈ RCN140.regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma Q=0) :
    (RCN140.regularSeeds H selected Gamma F).card≤P.regularCountCap:=by
  let Fself:=regularIndexSelf H F
  have hcount:=RCN052.regularPairSeeds_bound P F.1 Q hrel Fself p
    hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall
    selected Gamma nodes x u0 u1 hinj hnodes hw hchar hwa han hdegree hagreement hno
  have heq:RCN052.regularPairSeeds F.1 Q selected Gamma Fself =
      RCN140.regularSeeds H selected Gamma F:=by
    ext gamma
    simp only [RCN052.regularPairSeeds,RCN140.regularSeeds,Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1,h.2.1⟩
    · intro h
      exact ⟨h.1,h.2,hQzero gamma (Finset.mem_filter.mpr h)⟩
  rw [heq] at hcount
  have hv:=regularVector_le_mixedCost P F.1 hFY hFR hFZ
  have hdot:RCN294.dot P.agreement (RCN052.regularVector P F.1) ≤
      RCN294.dot P.agreement P.mixedCost :=
    Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left P.agreement.y hv.1)
        (Nat.mul_le_mul_left P.agreement.r hv.2.1))
      (Nat.mul_le_mul_left P.agreement.z hv.2.2)
  apply P.regular_count_le _ (by unfold UnequalParameters.gap; omega)
  exact hcount.trans (Nat.add_le_add (Nat.mul_le_mul_left (P.n - P.w) hdot)
    (Nat.mul_le_mul_left ((P.errors+1)*P.gap) hv.2.2))
theorem regularSeeds_count_le_intersection_of_product
    (P:UnequalParameters) (H Q:MvPolynomial (Fin 4) K)
    (F:RCN266.RegularIndex H) (hrel:IsRelPrime F.1 Q)
    (p:ℕ) [CharP K p]
    (hFY:F.1.degreeOf 1≤P.leftY) (hFR:F.1.degreeOf 2≤P.leftR)
    (hFZ:F.1.degreeOf 3≤P.leftZ)
    (hQY:Q.degreeOf 1≤P.rightY) (hQR:Q.degreeOf 2≤P.rightR)
    (hQZ:Q.degreeOf 3≤P.rightZ)
    (hleftR:1≤P.leftR)
    (hleftYSmall:P.leftY<p) (hleftRSmall:P.leftR<p)
    (hleftZSmall:P.leftZ<p)
    (hmixedYSmall:P.mixedCost.y<p) (hmixedRSmall:P.mixedCost.r<p)
    (hmixedZSmall:P.mixedCost.z<p)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (nodes:Finset I) (x u0 u1:I → K) (hinj:Set.InjOn x nodes)
    (hnodes:nodes.card=P.n)
    (hw:1≤P.w) (hchar:P.w<p) (hwa:P.w<P.a) (han:P.a≤P.n)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree≤P.w)
    (hagreement:∀ gamma ∈ Gamma,P.a ≤
      (nodes.filter (fun i => (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
    (hno:RCN238.NoLargeSelectedPencil selected Gamma P.w P.errors)
    (hproduct:∀ gamma ∈ RCN140.regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2:Fin 4) (F.1*Q))=0) :
    (RCN140.regularSeeds H selected Gamma F).card≤P.regularCountCap:=by
  apply regularSeeds_count_le_intersection P H Q F hrel p
    hFY hFR hFZ hQY hQR hQZ hleftR hleftYSmall hleftRSmall hleftZSmall
    hmixedYSmall hmixedRSmall hmixedZSmall
    selected Gamma nodes x u0 u1 hinj hnodes hw hchar hwa han hdegree hagreement hno
  intro gamma hgamma
  obtain ⟨hFzero,hregular⟩:=(Finset.mem_filter.mp hgamma).2
  have hmul :
      RCN319.specialization K (selected gamma) gamma (MvPolynomial.pderiv (2:Fin 4) F.1) *
        RCN319.specialization K (selected gamma) gamma Q=0:=by
    simpa only [MvPolynomial.pderiv_mul,map_add,map_mul,
      hFzero,zero_mul,add_zero] using hproduct gamma hgamma
  exact (mul_eq_zero.mp hmul).resolve_left hregular
end
end ProximityPrize.SubmissionLower.LocatorCoprimeQuotient
