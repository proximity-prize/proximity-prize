import ProximityPrize.SubmissionLower.Left6836Ready
import ProximityPrize.SubmissionLower.Left6836Tangent
import ProximityPrize.SubmissionLower.Koala6831MovingExceptionsRfree
import ProximityPrize.SubmissionLower.Koala6831MovingFoldCount
import ProximityPrize.SubmissionLower.Koala6831MovingPaidStageCounts
import ProximityPrize.SubmissionLower.Mid6833OpenRange
import ProximityPrize.SubmissionLower.Night6836FlowKernel
section BP0
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from the independent full-domain primary proof of Bome2017 after Lucieno (PR 618) and BitWonka. Exact 68.33 constants and physical hypotheses are new. -/
namespace ProximityPrize.SubmissionLower.Koala6831Moving

open scoped BigOperators
open Koala6831MovingSources LocatorDerivativeChain LocatorLowQuotient
open RCN081 RCN156 RCN234

noncomputable section

variable {K : Type} [Field K]
local instance night322DecidableEq : DecidableEq K := Classical.decEq _

section FixedProfile

open RCN318

def night322FreeParameters : TightParameters := ⟨262144, weight, 181039, (322*181039), 83491, 1⟩

set_option maxRecDepth 80000 in

theorem night322_free_count [CharP K 2130706433] {I : Type}
    (H : ExceptionPoly K) (hH : H ≠ 0)
    (hbox : H ∈ nestedCoefficientBox K (322*181039) weight 83491 444 99)
    (seeds : Finset K) (selected : K → Polynomial K) (nodes : Finset I)
    (x u₀ u₁ : I → K) (hinj : Set.InjOn x nodes) (hnodes : nodes.card = 262144)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ weight)
    (hsol : ∀ g ∈ seeds, RCN319.specialization K (selected g) g (freeAndTailCarrier H) = 0)
    (hagree : ∀ g ∈ seeds, 181039 ≤
      (nodes.filter fun i => (selected g).eval (x i) = u₀ i + g * u₁ i).card)
    (hpencil : RCN238.NoLargeSelectedPencil selected seeds weight 81105) :
    seeds.card ≤ 76485858048800 := by
  let J := freeAndTailCarrier H
  let params := night322FreeParameters
  have hweights := nested_mem_weights hbox hH
  have hsmall : H.degreeOf 2 < 2130706433 := by
    apply lt_of_le_of_lt (b := 99) ?_ (by decide +kernel)
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
    have ht' : d 1 + d 2 + d 3 ≤ 83491 := by
      simpa [weight_fin4, residualTotalWeights] using ht
    exact ⟨by change d 1 + d 3 ≤ 83491; omega,
      hr.trans (by decide +kernel),
      by simpa [weight_fin4, contactWeights, Nat.mul_comm, params, night322FreeParameters] using hx⟩
  have herrors : params.errors = 81105 := by decide +kernel
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
#print axioms ProximityPrize.SubmissionLower.Koala6831Moving.night322_free_count

end BP0

section BP1
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from the independent full-domain primary proof of Bome2017 after Lucieno (PR 618) and BitWonka. Exact 68.33 constants and physical hypotheses are new. -/
namespace ProximityPrize.SubmissionLower.Koala6831MovingFoldCount

open scoped Classical BigOperators
open Koala6831Moving Koala6831MovingPairIncidence
open Koala6831OrdinaryIncidence (lengthAverage nodeAverage)
open RCN081 RCN095 RCN130 RCN135 RCN136 RCN137 RCN138 RCN156 RCN167 RCN222 RCN234 RCN243
open RCN238 RCN263 RCN266 RCN267 RCN275 RCN293 RCN319
open LocatorDerivativeChain

noncomputable section

variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

private def night322FoldSupport : ResidualSupportParameters :=
  ⟨99, 444, 83491, by decide, by decide, by decide, by decide⟩

open Koala6831MovingSources LocatorLowQuotient

theorem night322_fold_count [CharP K 2130706433]
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0)
    (hbox : H ∈ nestedCoefficientBox K 58294558 weight 83491 444 99)
    (Γ : Finset K) (selected : K → Polynomial K)
    {Node : Type*} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (hnodes : nodes.card = 262144)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ weight)
    (hagreement : ∀ γ ∈ Γ, 181039 ≤
      (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ weight 81105) :
    (foldedSeeds H Γ selected).card ≤ 7320416915948884 := by
  have hweights := nested_mem_weights hbox hH
  have hData : ResidualSupportData night322FoldSupport H :=
    ⟨hweights.2.2.1, hweights.2.1, hweights.1⟩
  have hAn : 181039 ≤ nodes.card := by rw [hnodes]; decide +kernel
  have h := folded_seed_card_le night322FoldSupport (by decide +kernel) (by decide +kernel)
    H hH hData 2130706433 selected Γ nodes x u₀ u₁ hx weight 181039 81105
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hAn
    (by decide +kernel) (by decide +kernel) hdegree hagreement hnoPencil
  rw [hnodes] at h
  exact h.trans (by decide +kernel)

theorem night322_regular_seeds [CharP K 2130706433]
    (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0)
    (hbox : H ∈ nestedCoefficientBox K 58294558 weight 83491 444 99)
    (Γ : Finset K) (selected : K → Polynomial K)
    {Node : Type} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (hnodes : nodes.card = 262144)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ weight)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ H = 0)
    (hagreement : ∀ γ ∈ Γ, 181039 ≤
      (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ weight 81105) :
    ∃ Γreg : Finset K, Γreg ⊆ Γ ∧ Γ.card ≤ Γreg.card + 7396902773997684 ∧
      ∀ γ ∈ Γreg, ∃ F : RegularIndex H, specialization K (selected γ) γ F.1 = 0 ∧
        specialization K (selected γ) γ (RCN313.polyH K F.1) ≠ 0 := by
  classical
  let free := Γ.filter fun γ => specialization K (selected γ) γ (freeAndTailCarrier H) = 0
  let fold := foldedSeeds H Γ selected
  let discarded := free ∪ fold
  let regular := Γ \ discarded
  have hfreeSub : free ⊆ Γ := Finset.filter_subset _ _
  have hfoldSub : fold ⊆ Γ := fun γ hγ => (mem_foldedSeeds.mp hγ).1
  have hdiscSub : discarded ⊆ Γ := Finset.union_subset hfreeSub hfoldSub
  have hfree := night322_free_count H hH hbox free selected nodes x u₀ u₁ hx hnodes
    (fun γ hγ => hdegree γ (hfreeSub hγ)) (fun γ hγ => (Finset.mem_filter.mp hγ).2)
    (fun γ hγ => hagreement γ (hfreeSub hγ))
    (noLargeSelectedPencil_mono selected Γ free weight 81105 hfreeSub hnoPencil)
  have hfold := night322_fold_count H hH hbox Γ selected nodes x u₀ u₁ hx hnodes
    hdegree hagreement hnoPencil
  have hdisc : discarded.card ≤ 7396902773997684 :=
    (Finset.card_union_le free fold).trans (Nat.add_le_add hfree hfold)
  refine ⟨regular, Finset.sdiff_subset, ?_, ?_⟩
  · have h := Finset.card_sdiff_of_subset hdiscSub
    have hle := Finset.card_le_card hdiscSub
    change regular.card = Γ.card - discarded.card at h
    omega
  · intro γ hγ
    obtain ⟨hΓ, hdis⟩ := Finset.mem_sdiff.mp hγ
    rcases primary_regular_fold_or_free H hH (selected γ) γ (hsolution γ hΓ) with h | ⟨F, hF, h⟩
    · exact (hdis (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hΓ, h⟩))).elim
    · rcases h with h | ⟨hfold, htail⟩
      · exact ⟨F, hF, h⟩
      · exact (hdis (Finset.mem_union_right _ (mem_foldedSeeds.mpr ⟨hΓ, F, hF, hfold, htail⟩))).elim

end

end ProximityPrize.SubmissionLower.Koala6831MovingFoldCount
#print axioms ProximityPrize.SubmissionLower.Koala6831MovingFoldCount.night322_regular_seeds

end BP1

section BP2
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adapted from the independent full-domain primary proof of Bome2017 after Lucieno (PR 618) and BitWonka. Exact 68.33 constants and physical hypotheses are new. -/

namespace ProximityPrize.SubmissionLower.Night6836PrimaryRoute

open scoped Classical
open Koala6831Moving Night6836FlowSources Koala6831MovingFoldCount
open LocatorLowQuotient RCN238 RCN266 RCN313 RCN319

noncomputable section

variable {K Node : Type} [Field K] [CharP K 2130706433]

theorem exists_primary_and_regular_subfamily
    (nodes good : Finset Node) (hgood : good ⊆ nodes) (hnodes : nodes.card = 262144)
    (x : Node ↪ K) (u₀ u₁ : Node → K)
    (Γ : Finset K) (selected : K → Polynomial K)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ weight)
    (hagreement : ∀ γ ∈ Γ, agreement ≤
      (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hgoodAgree : ∀ γ ∈ Γ, ∀ i ∈ nodes,
      (selected γ).eval (x i) = u₀ i + γ * u₁ i → i ∈ good)
    (hnoPencil : NoLargeSelectedPencil selected Γ weight 81105) :
    ∃ H : MvPolynomial (Fin 4) K, H ≠ 0 ∧
      H ∈ nestedCoefficientBox K Stage.primary.cutoff weight 83491 444 99 ∧
      (∀ i ∈ good, ContactOrderBridge.ContactAtLeast K (x i) (u₀ i) (u₁ i) Stage.primary.multiplicity H) ∧
      ∃ regular : Finset K, regular ⊆ Γ ∧ Γ.card ≤ regular.card + 7396902773997684 ∧
        ∀ γ ∈ regular, ∃ F : RegularIndex H, specialization K (selected γ) γ F.1 = 0 ∧
          specialization K (selected γ) γ (polyH K F.1) ≠ 0 := by
  classical
  let xgood (i : ↥good) := x i.1
  let u₀good (i : ↥good) := u₀ i.1
  let u₁good (i : ↥good) := u₁ i.1
  have hcard : Fintype.card (↥good) ≤ 262144 := by
    rw [Fintype.card_coe, ← hnodes]
    exact Finset.card_le_card hgood
  obtain ⟨v, hv⟩ := Stage.primary.exists_source K xgood u₀good u₁good hcard
  let H := Stage.primary.reconstruct K xgood u₀good u₁good v
  have hbox : H ∈ nestedCoefficientBox K Stage.primary.cutoff weight 83491 444 99 :=
    Stage.primary.reconstruct_mem_box K xgood u₀good u₁good v
  have hcontact (i : Node) (hi : i ∈ good) :
      ContactOrderBridge.ContactAtLeast K (x i) (u₀ i) (u₁ i) Stage.primary.multiplicity H :=
    Stage.primary.reconstruct_contact K xgood u₀good u₁good v ⟨i, hi⟩
  have hsolution (γ : K) (hγ : γ ∈ Γ) : specialization K (selected γ) γ H = 0 := by
    let support := nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)
    exact specialization_zero_of_box_and_agreement x u₀ u₁ Stage.primary H (selected γ) γ support hbox
      (fun i hi => hcontact i (hgoodAgree γ hγ i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2))
      (hdegree γ hγ) (hagreement γ hγ) (fun i hi => (Finset.mem_filter.mp hi).2)
  exact ⟨H, hv, hbox, hcontact, night322_regular_seeds H hv hbox Γ selected nodes x u₀ u₁
    x.injective.injOn hnodes hdegree hsolution hagreement hnoPencil⟩

theorem exists_primary_and_transverse_subfamily [Fintype Node]
    (B : FlowData K) (nodes good : Finset Node) (hgood : good ⊆ nodes) (hnodes : nodes.card = 262144)
    (x : Node ↪ K) (u₀ u₁ received : Node → K)
    (Γ : Finset K) (selected normalized : K → Polynomial K)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ weight)
    (hagreement : ∀ γ ∈ Γ, agreement ≤
      (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hgoodAgree : ∀ γ ∈ Γ, ∀ i ∈ nodes,
      (selected γ).eval (x i) = u₀ i + γ * u₁ i → i ∈ good)
    (hnoPencil : NoLargeSelectedPencil selected Γ weight 81105)
    (hd0 : B.d0 ≠ 0) (ha : B.A ≠ 0)
    (hden : ∀ γ ∈ Γ, B.seedDenominator γ ≠ 0)
    (hnorm : ∀ γ ∈ Γ,
      B.d0 * selected γ + B.seedOffset γ = B.seedDenominator γ * normalized γ)
    (hnormDegree : ∀ γ ∈ Γ, (normalized γ).natDegree ≤ Left6836List.w)
    (hnormAgree : ∀ γ ∈ Γ, Left6836List.agreements ≤
      (nodes.filter (fun i => (normalized γ).eval (x i) = received i)).card) 
    (nondivisible : ¬B.d0 ∣ B.a0*B.c1-B.a1*B.c0) :
    ∃ H : MvPolynomial (Fin 4) K, H ≠ 0 ∧
      H ∈ nestedCoefficientBox K Stage.primary.cutoff weight 83491 444 99 ∧
      (∀ i ∈ good, ContactOrderBridge.ContactAtLeast K (x i) (u₀ i) (u₁ i) Stage.primary.multiplicity H) ∧
      ∃ retained : Finset K, retained ⊆ Γ ∧ Γ.card ≤ retained.card + 7396977036826001 ∧
        ∀ γ ∈ retained, ∃ F : RegularIndex H, specialization K (selected γ) γ F.1 = 0 ∧
          specialization K (selected γ) γ (polyH K F.1) ≠ 0 ∧ ¬ F.1 ∣ B.flow F.1 := by
  classical
  obtain ⟨H, hH, hbox, hcontact, regular, hsub, hcost, hregular⟩ :=
    exists_primary_and_regular_subfamily nodes good hgood hnodes x u₀ u₁ Γ selected
      hdegree hagreement hgoodAgree hnoPencil
  obtain ⟨retained, hret, htangentCost, htangent⟩ :=
    B.left6836_screen_tangent_seeds H hH hbox regular selected normalized nodes x received x.injective.injOn
      hnodes hd0 ha (fun γ hγ => hden γ (hsub hγ)) (fun γ hγ => hdegree γ (hsub hγ))
      (fun γ hγ => hnorm γ (hsub hγ)) (fun γ hγ => hnormDegree γ (hsub hγ))
      (fun γ hγ => hnormAgree γ (hsub hγ))
      nondivisible
  refine ⟨H, hH, hbox, hcontact, retained, hret.trans hsub, ?_, ?_⟩
  · change regular.card ≤ retained.card + 74262828317 at htangentCost
    omega
  · intro γ hγ
    obtain ⟨F, hF, hreg⟩ := hregular γ (hret hγ)
    exact ⟨F, hF, hreg, htangent γ hγ F hF⟩

end

end ProximityPrize.SubmissionLower.Night6836PrimaryRoute





#print axioms ProximityPrize.SubmissionLower.Night6836PrimaryRoute.exists_primary_and_transverse_subfamily

end BP2

section BP3
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. The primary factor cover and aggregate comparison are adapted from
Bome2017's 68.32 construction, after Lucieno and BitWonka. -/
namespace ProximityPrize.SubmissionLower.Night6836PrimaryBridge
open ProximityPrize.Benchmark Genuine6969
open RCN095 RCN156 RCN238 RCN266 RCN319 Koala6831Moving
open Left6836Ready Night6836PrimaryRoute Night6836FlowSources Night6836FlowAdaptive
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
    H∈nestedCoefficientBox F Stage.primary.cutoff 131071 83491 444 99 →
    (∀i∈R.good,ContactOrderBridge.ContactAtLeast F (Dmn i) (R.u₀ i) (R.u₁ i) 322 H) →
    ∀(Γ : Finset F), Γ⊆R.seeds → ∀(A : Finset (RegularIndex H)),
    (∀f∈A,¬f.1∣R.flow.flow f.1) → (A.card : ENat)<ENat.card F →
    Below (aggregateFlag H A) Night6836FlowPaid.primaryIncoming →
    Γ⊆A.biUnion (regularFiber H Γ R.selected) →
    (A.biUnion (regularFiber H Γ R.selected)).card≤267159171641512934

private theorem below_trans {a b c : FlagDegree} (ab : Below a b) (bc : Below b c) : Below a c :=
  ⟨ab.1.trans bc.1,ab.2.1.trans bc.2.1,ab.2.2.trans bc.2.2⟩

theorem combined_prices (δ : ℕ) (lo : 2134≤δ) :
    Left6836Ready.normalizationBudget + 7396977036826001 + (33735-δ+1)*6*(2130706433+1) +
      267159171641512934≤274980640798883310 := by
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
    original.card ≤ 274576633290519702 := by
  classical
  letI := Koala6831BenchmarkField.characteristic
  obtain ⟨H,hn,box,contact,Γ,sub,fee,regular⟩ :=
    exists_primary_and_transverse_subfamily R.flow Finset.univ R.good (Finset.subset_univ _)
      (Finset.card_univ.trans R.nodes_card) Dmn R.u₀ R.u₁ R.word R.seeds R.selected R.normalized
      R.degree R.agreement (fun g hg i _ => R.agree_good g hg i) R.pencil R.scale_ne R.affine_ne
      R.denominator_ne R.normalization R.normalized_degree R.normalized_agreement R.nondivisible
  let A := Finset.univ.filter (fun f : RegularIndex H => ¬f.1∣R.flow.flow f.1)
  have trans (f : RegularIndex H) (hf : f∈A) : ¬f.1∣R.flow.flow f.1 := (Finset.mem_filter.mp hf).2
  have cover : Γ⊆A.biUnion (regularFiber H Γ R.selected) := by
    intro g hg
    obtain ⟨f,fz,fu,ft⟩ := regular g hg
    exact Finset.mem_biUnion.mpr ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ft⟩,
      mem_regularFiber.mpr ⟨hg,fz,fu⟩⟩
  have cap : Below (aggregateFlag H A) Night6836FlowPaid.primaryIncoming := by
    obtain ⟨ht,hy,hr,_⟩ := nested_mem_weights box hn
    apply below_trans (contactFlag_below_of_dvd hn (regularProduct_dvd_carrier H A))
    simp only [Below,contactFlag_all,contactFlag_middle,contactFlag_total]
    exact ⟨hr,hy,ht⟩
  have card : (A.card : ENat)<ENat.card F := by
    have ac : A.card≤99 := (factor_card_le_slope H A).trans cap.1
    have hb := ENat.card_le_card_of_injective Dmn.injective
    rw [ENat.card_eq_coe_fintype_card,IRSProfile.card_index] at hb
    exact (show (A.card : ENat)<262144 by exact_mod_cast ac.trans_lt (by decide : 99<262144)).trans_le hb
  have r := (Finset.card_le_card cover).trans (bounds original R H hn box contact Γ sub A trans card cap cover)
  have norm := R.count
  unfold normalizationBudget at norm
  omega
#print axioms combined_prices
#print axioms seed_count
end
end ProximityPrize.SubmissionLower.Night6836PrimaryBridge

end BP3

section BP4
/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
namespace ProximityPrize.SubmissionLower.Night6836PrimaryBridge
open ProximityPrize.Benchmark Genuine6969 K6969Global Koala6831Separation Koala6831Comparison
open Koala6831BenchmarkPrimitive (Received SelectionMap agreementSet)
open Koala6831BenchmarkField (prime frobenius)
open scoped Classical
set_option maxRecDepth 80000
set_option maxHeartbeats 3000000

theorem short_of_regularBudget (bounds : RegularBudget) :
    Intermediate.OpenAt 181039 274980640798883310 2133 9615 := by
  intro U S P q N hard fit pencil lo hi _
  obtain ⟨R⟩ := Left6836Ready.ready_of_hard Dmn frobenius
    Koala6831BenchmarkField.domain_fixed Koala6831BenchmarkField.frobenius_apply IRSProfile.card_index U S P q
    hard.actual fit pencil (primitiveExcess 131071 q) (by omega) N hard.aligned hard.finiteFailure
  have price := seed_count bounds S R
  have degree : 33735-primitiveExcess 131071 q+1≤31602 := by omega
  unfold prime
  omega
#print axioms short_of_regularBudget
end ProximityPrize.SubmissionLower.Night6836PrimaryBridge

end BP4
