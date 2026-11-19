/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. The primary factor cover and aggregate comparison are adapted from
Bome2017's 68.32 construction, after Lucieno and BitWonka. -/
import ProximityPrize.SubmissionLower.Mid6833K6833PrimaryRoute
import ProximityPrize.SubmissionLower.Mid6833K6833PrimaryReady
import ProximityPrize.SubmissionLower.Mid6833K6833FlowPaidCaps
import ProximityPrize.SubmissionLower.Koala6831MovingPaidStageCounts
namespace ProximityPrize.SubmissionLower.K6833PrimaryBridge
open ProximityPrize.Benchmark Genuine6969
open RCN095 RCN156 RCN238 RCN266 RCN319 Koala6831Moving
open K6833PrimaryReady K6833PrimaryRoute K6833FlowSources K6833FlowAdaptive
open Koala6831MovingPaid (regularFiber mem_regularFiber)
open LocatorBatchProductRoute (regularProduct regularProduct_dvd_carrier)
open LocatorFactorAggregate LocatorLowQuotient
open LocatorPhase6800Oracle (sumFlag_all)
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 2200000
def RegularBudget : Prop :=
  ∀(original : Finset F) (R : Ready Dmn original) (H : P4 F), H≠0 →
    H∈nestedCoefficientBox F Stage.primary.cutoff 131071 65864 440 98 →
    (∀i∈R.good,ContactOrderBridge.ContactAtLeast F (Dmn i) (R.u₀ i) (R.u₁ i) 319 H) →
    ∀(Γ : Finset F), Γ⊆R.seeds → ∀(A : Finset (RegularIndex H)),
    (∀f∈A,¬f.1∣R.flow.flow f.1) → (A.card : ENat)<ENat.card F →
    Below (aggregateFlag H A) K6833FlowPaid.primaryIncoming →
    Γ⊆A.biUnion (regularFiber H Γ R.selected) →
    (A.biUnion (regularFiber H Γ R.selected)).card≤262932826822788554

private theorem below_trans {a b c : FlagDegree} (ab : Below a b) (bc : Below b c) : Below a c :=
  ⟨ab.1.trans bc.1,ab.2.1.trans bc.2.1,ab.2.2.trans bc.2.2⟩

theorem combined_prices (δ : ℕ) (lo : 2223≤δ) :
    K6833PrimaryReady.normalizationBudget + 11624541508801261 + (33735-δ+1)*6*(2130706433+1) +
      262932826822788554≤274980690694301924 := by
  unfold normalizationBudget
  omega

private theorem factor_card_le_slope {k : Type} [Field k] (H : P4 k) (A : Finset (RegularIndex H)) :
    A.card≤(aggregateFlag H A).all := by
  calc
    _ = ∑ f∈A, 1 := by simp
    _ ≤ ∑ f∈A, (contactFlag f.1).all := Finset.sum_le_sum fun f _ => RCN130.regularCumulativeFlag_positive H f
    _ = _ := by
      change _ = (contactFlag (regularProduct H A)).all
      rw [contactFlag_regularProduct,sumFlag_all]

theorem seed_count (bounds : RegularBudget) (original : Finset F) (R : Ready Dmn original) :
    original.card ≤ 274577820983174072 := by
  classical
  letI := Koala6831BenchmarkField.characteristic
  obtain ⟨H,hn,box,contact,Γ,sub,fee,regular⟩ :=
    exists_primary_and_transverse_subfamily R.flow Finset.univ R.good (Finset.subset_univ _)
      (Finset.card_univ.trans R.nodes_card) Dmn R.u₀ R.u₁ R.word R.seeds R.selected R.normalized
      R.degree R.agreement (fun g hg i _ => R.agree_good g hg i) R.pencil R.scale_ne R.affine_ne
      R.denominator_ne R.normalization R.normalized_degree R.normalized_agreement
  let A := Finset.univ.filter (fun f : RegularIndex H => ¬f.1∣R.flow.flow f.1)
  have trans (f : RegularIndex H) (hf : f∈A) : ¬f.1∣R.flow.flow f.1 := (Finset.mem_filter.mp hf).2
  have cover : Γ⊆A.biUnion (regularFiber H Γ R.selected) := by
    intro g hg
    obtain ⟨f,fz,fu,ft⟩ := regular g hg
    exact Finset.mem_biUnion.mpr ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ft⟩,
      mem_regularFiber.mpr ⟨hg,fz,fu⟩⟩
  have cap : Below (aggregateFlag H A) K6833FlowPaid.primaryIncoming := by
    obtain ⟨ht,hy,hr,_⟩ := nested_mem_weights box hn
    apply below_trans (contactFlag_below_of_dvd hn (regularProduct_dvd_carrier H A))
    simp only [Below,contactFlag_all,contactFlag_middle,contactFlag_total]
    exact ⟨hr,hy,ht⟩
  have card : (A.card : ENat)<ENat.card F := by
    have ac : A.card≤98 := (factor_card_le_slope H A).trans cap.1
    have hb := ENat.card_le_card_of_injective Dmn.injective
    rw [ENat.card_eq_coe_fintype_card,IRSProfile.card_index] at hb
    exact (show (A.card : ENat)<262144 by exact_mod_cast ac.trans_lt (by decide : 98<262144)).trans_le hb
  have r := (Finset.card_le_card cover).trans (bounds original R H hn box contact Γ sub A trans card cap cover)
  have norm := R.count
  unfold normalizationBudget at norm
  omega
#print axioms combined_prices
#print axioms seed_count
end
end ProximityPrize.SubmissionLower.K6833PrimaryBridge
