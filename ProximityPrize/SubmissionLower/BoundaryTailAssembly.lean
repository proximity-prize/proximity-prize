import ProximityPrize.SubmissionLower.BoundaryTailRegularBridge
import ProximityPrize.SubmissionLower.BoundaryTailPairGeometry

namespace ProximityPrize.SubmissionLower.Lower80811.Assembly
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN130 RCN140 RCN156 RCN167 RCN174 RCN180 RCN234 RCN238 RCN243 RCN259 RCN260 RCN266 RCN286 RCN319
open Lower80811.Selection Lower80811.InitialBridge Lower80811.Initial
open LocatorFactorAggregate LocatorBatchProductRoute LocatorDerivativeChain
open LocatorBatchPhase6800 (regularAggregateFlag)
open LocatorPhase6800Oracle (rawFlag)
open Counting AsymmetricChainPolynomial80811
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq _
local instance : DecidableEq I := Classical.decEq _
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4

def combined (p : FlagDegree) : ℕ :=
  PhaseSemantics.phaseCap 6 p + initialAComplement p +
    p.all*unit (middle p) (total p) p.all +
    (33-p.all)*unit (153-middle p) (27312-total p) (33-p.all) +
    18000000000000+1078597675256405

/-- Numerical ledger receipt, including the empty universal-factor state. -/
def LedgerReceiptSound (budget : ℕ) : Prop :=
  combined ⟨0,0,0⟩ ≤ budget ∧
  ∀ r v z : ℕ, 1 ≤ r → r ≤ 31 → r+v ≤ 142 → r+v+z ≤ 7501 →
    combined (rawFlag r v z) ≤ budget

theorem combined_bound {budget : ℕ} (hledger : LedgerReceiptSound budget) (H : P4) (U : Finset (RegularIndex H))
    (hr : (regularAggregateFlag H U).all ≤ 31)
    (hy : middle (regularAggregateFlag H U) ≤ 142)
    (ht : total (regularAggregateFlag H U) ≤ 7501) :
    combined (regularAggregateFlag H U) ≤ budget := by
  let p := regularAggregateFlag H U
  by_cases hp : p.all = 0
  · have hu : U = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro F hF
      have hd := (Budgets.factor_coordinates H U F hF).2.1
      have hpos := (positiveRFactors_spec H F.1 F.2).2.2
      change (regularAggregateFlag H U).all = 0 at hp
      omega
    subst U
    change combined ⟨0,0,0⟩ ≤ budget
    exact hledger.1
  · have hc := hledger.2 p.all p.yz p.zOnly (by omega) hr
      (by simpa only [p,middle,Nat.add_comm] using hy)
      (by simpa only [p,total,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht)
    have he : rawFlag p.all p.yz p.zOnly = p := by cases p; rfl
    simpa only [he] using hc


theorem selected_pair_count_le
    {zero : ℕ → ℕ → ℕ} {split : FlagDegree → ℕ} {budget : ℕ}
    (hbaseReceipt : BoundaryTailBaseOracle.Receipt zero split (PhaseSemantics.phaseCap 0))
    (hpref : PhaseSemantics.PrefixReceiptSound)
    (hthreshold : PhaseSemantics.ThresholdReceiptSound)
    (hruns : PhaseSemantics.RunReceiptSound) (hledger : LedgerReceiptSound budget)
    (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K) (inp : Input u0 u1 selected Gamma) :
    Gamma.card ≤ budget := by
  let H : P4 := gcd12 S.QA S.QB
  let Q : P4 := quotientB S.QA S.QB
  let T : P4 := quotientA S.QA S.QB
  let phi : K → P4 →+* Polynomial K := fun g => (specialization K (selected g) g).toRingHom
  let D := LocatorCover.fixed phi Gamma S.QA S.QB
  let E := LocatorCover.residual phi Gamma S.QA S.QB
  let U := initialAUniversalFactors u0 u1 H
  let p := regularAggregateFlag H U
  have hH : H ≠ 0 := gcd_ne_zero_of_left S.QA_ne
  have hQeq : S.QB = H*Q := b_eq_gcd12_mul_quotientB S.QA S.QB
  have hTeq : S.QA = H*T := a_eq_gcd12_mul_quotientA S.QA S.QB
  have hQ : Q ≠ 0 := by
    intro hz
    exact S.QB_ne (by rw [hQeq,hz,mul_zero])
  have hT : T ≠ 0 := by
    intro hz
    exact S.QA_ne (by rw [hTeq,hz,mul_zero])
  have hb := flag_box_to_ordinary K 20127963 131071 27312 33 S.QB S.QB_flag
  have ha := flag_box_to_ordinary K 36266600 131071 7506 62 S.QA S.QA_flag
  have hHbox : H ∈ RCN174.globalCoefficientBox K 20127963 131071 27312 33 :=
    mem_globalCoefficientBox_of_dvd H S.QB 20127963 131071 27312 33 S.QB_ne
      (gcd_dvd_right S.QA S.QB) hb
  have hQbox : Q ∈ RCN174.globalCoefficientBox K 20127963 131071 27312 33 :=
    mem_globalCoefficientBox_of_dvd Q S.QB 20127963 131071 27312 33 S.QB_ne
      ⟨H,hQeq.trans (mul_comm H Q)⟩ hb
  have hTbox : T ∈ RCN174.globalCoefficientBox K 36266600 131071 7506 62 :=
    mem_globalCoefficientBox_of_dvd T S.QA 36266600 131071 7506 62 S.QA_ne
      ⟨H,hTeq.trans (mul_comm H T)⟩ ha
  have hTcaps : T.degreeOf 1 ≤ 276 ∧ T.degreeOf 2 ≤ 62 ∧ T.degreeOf 3 ≤ 7506 := by
    simpa only [Nat.reduceSub,Nat.reduceDiv] using
      degree_bounds_of_mem_box T 36266600 131071 7506 62 (by decide +kernel) hTbox
  have hsubD : D ⊆ Gamma := by
    intro g hg
    have hm : g ∈ Gamma ∧ (phi g) H = 0 := by
      simpa only [D,H,LocatorCover.fixed,Finset.mem_filter] using hg
    exact hm.1
  have hsubE : E ⊆ Gamma := by
    intro g hg
    have hm : g ∈ Gamma ∧ (phi g) H ≠ 0 := by
      simpa only [E,H,LocatorCover.residual,Finset.mem_filter] using hg
    exact hm.1
  have inpD := inp.restrict D hsubD
  have inpE := inp.restrict E hsubE
  have hparents (g : K) (hg : g ∈ Gamma) :
      specialization K (selected g) g S.QA = 0 ∧ specialization K (selected g) g S.QB = 0 :=
    S.universal_vanishing g (selected g)
      ((Finset.univ : Finset I).filter (fun i =>
        (selected g).eval (IRSProfile.domain i) = u0 i+g*u1 i))
      (inp.degree g hg) (inp.agreement g hg) (fun _ hi => (Finset.mem_filter.mp hi).2)
  have hsolD : ∀ g ∈ D, specialization K (selected g) g H = 0 :=
    LocatorCover.fixed_vanish phi Gamma S.QA S.QB
  have hsolE : ∀ g ∈ E, specialization K (selected g) g T = 0 ∧ specialization K (selected g) g Q = 0 :=
    LocatorCover.residual_vanish phi Gamma S.QA S.QB
      (fun g hg => (hparents g hg).1) (fun g hg => (hparents g hg).2)
  have hcD := Geometry.cover_count H H hH hHbox selected D hsolD hsolD
  have hcE := Geometry.cover_count Q T hQ hQbox selected E
    (fun g hg => (hsolE g hg).2) (fun g hg => (hsolE g hg).1)
  have hrD : (∑ F : RegularIndex H, (RCN052.regularPairSeeds H H selected D F).card) ≤
      (∑ F : RegularIndex H, (regularSeeds H selected D F).card) :=
    Finset.sum_le_sum (fun F _ => Finset.card_le_card
      (LocatorFixedChain.regularPairSeeds_self_subset H selected D F))
  have hrE := Geometry.pair_count inpE Q T hQ (firstQuotients_isRelPrime S.QA_ne).symm hQbox hTcaps
  have hfreeD := freePart_count inpD H hH hHbox
  have hfreeE := freePart_count inpE Q hQ hQbox
  have hreg := RegularBridge.regular_count hbaseReceipt hpref hthreshold hruns u0 u1 S selected Gamma inp
  change p.all ≤ 31 ∧ middle p ≤ 142 ∧ total p ≤ 7501 ∧
    (∑ F : RegularIndex H, (regularSeeds H selected D F).card) ≤
      PhaseSemantics.phaseCap 6 p+initialAComplement p at hreg
  have hprod : H*Q ∈ RCN100.globalCoefficientBox K 20127963 131071 27312 33 := by
    rw [← hQeq]
    exact S.QB_flag
  have hcharge := Budgets.joint_charge H Q hH hQ hprod hHbox hQbox U
    u0 u1 selected D E inpD inpE hreg.1 hreg.2.1 hreg.2.2.1
  have hbound := combined_bound hledger H U hreg.1 hreg.2.1 hreg.2.2.1
  change combined p ≤ budget at hbound
  change (∑ F : RegularIndex H, factorCharge F.1 selected D)+
    (∑ F : RegularIndex Q, factorCharge F.1 selected E) ≤
      p.all*unit (middle p) (total p) p.all +
      (33-p.all)*unit (153-middle p) (27312-total p) (33-p.all) at hcharge
  have hpart : D.card+E.card = Gamma.card := LocatorCover.partition_card phi Gamma S.QA S.QB
  have hcfixed : D.card ≤ (∑ F : RegularIndex H, (RCN052.regularPairSeeds H H selected D F).card) +
      (∑ F : RegularIndex H, factorCharge F.1 selected D)+(rfreeSeeds H selected D).card := by
    simpa only [RCN052.RegularIndex,RCN266.RegularIndex] using hcD
  have hcresidual : E.card ≤ (∑ F : RegularIndex Q, (RCN052.regularPairSeeds Q T selected E F).card) +
      (∑ F : RegularIndex Q, factorCharge F.1 selected E)+(rfreeSeeds Q selected E).card := by
    simpa only [RCN052.RegularIndex,RCN266.RegularIndex] using hcE
  have hrresidual : (∑ F : RegularIndex Q, (RCN052.regularPairSeeds Q T selected E F).card) ≤ 1078597675256405 := by
    simpa only [RCN052.RegularIndex,RCN266.RegularIndex] using hrE
  unfold combined at hbound
  omega



theorem selected_pair_count
    {zero : ℕ → ℕ → ℕ} {split : FlagDegree → ℕ} {budget : ℕ}
    (hbaseReceipt : BoundaryTailBaseOracle.Receipt zero split (PhaseSemantics.phaseCap 0))
    (hbudget : budget < 274980722141397184)
    (hpref : PhaseSemantics.PrefixReceiptSound)
    (hthreshold : PhaseSemantics.ThresholdReceiptSound)
    (hruns : PhaseSemantics.RunReceiptSound) (hledger : LedgerReceiptSound budget)
    (u0 u1 : I → K) (S : SelectedPair u0 u1)
    (selected : K → Polynomial K) (Gamma : Finset K) (inp : Input u0 u1 selected Gamma) :
    Gamma.card < 274980722141397184 := by
  exact lt_of_le_of_lt
    (selected_pair_count_le hbaseReceipt hpref hthreshold hruns hledger u0 u1 S selected Gamma inp)
    hbudget

end
end ProximityPrize.SubmissionLower.Lower80811.Assembly
