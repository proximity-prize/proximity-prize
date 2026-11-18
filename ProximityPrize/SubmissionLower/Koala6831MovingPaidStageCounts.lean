import ProximityPrize.SubmissionLower.Koala6831MovingPaidCaps
import ProximityPrize.SubmissionLower.Koala6831MovingSchedule

namespace ProximityPrize.SubmissionLower.Koala6831MovingPaid

open scoped Classical BigOperators
open RCN081 RCN095 RCN130 RCN135 RCN136 RCN156 RCN167 RCN234 RCN238 RCN243 RCN266 RCN275 RCN313 RCN319
open Koala6831Moving Koala6831MovingAdaptive Koala6831MovingCarrierPairs Koala6831MovingSources
open LocatorBatchProductRoute (regularProduct regularProduct_ne_zero regularCofactor regularFactor_mul_cofactor)
open LocatorFactorAggregate LocatorLowQuotient
open LocatorPhase6800Oracle (sumFlag sumFlag_all sumFlag_middle sumFlag_total)
open Koala6831MovingStages (adaptiveGate adaptiveGate_mono)

noncomputable section

variable {K : Type} [Field K]

def regularFiber (H : P4 K) (Γ : Finset K) (selected : K → Polynomial K) (F : RegularIndex H) :
    Finset K := by
  classical
  exact Γ.filter fun γ => specialization K (selected γ) γ F.1 = 0 ∧
    specialization K (selected γ) γ (polyH K F.1) ≠ 0

@[simp] theorem mem_regularFiber {H : P4 K} {Γ : Finset K} {selected : K → Polynomial K}
    {F : RegularIndex H} {γ : K} :
    γ ∈ regularFiber H Γ selected F ↔ γ ∈ Γ ∧
      specialization K (selected γ) γ F.1 = 0 ∧
      specialization K (selected γ) γ (polyH K F.1) ≠ 0 := by
  simp only [regularFiber, Finset.mem_filter]

theorem regularFiber_subset (H : P4 K) (Γ : Finset K) (selected : K → Polynomial K)
    (F : RegularIndex H) : regularFiber H Γ selected F ⊆ Γ :=
  fun _ h => (mem_regularFiber.mp h).1

private theorem surface_in_partner_flag (s : Stage) (gain : ℕ) {cutoff : ℕ}
    {Q : P4 K} (hQ : Q ≠ 0)
    (hbox : Q ∈ nestedCoefficientBox K cutoff weight
      (s.numbers.totalCap + gain) s.numbers.middleCap s.numbers.slopeCap) :
    PolynomialInFlag (stagePartnerFlag s gain) (surfaceMap (polynomialEmbedding K) Q) := by
  obtain ⟨hT, hY, hR, _⟩ := nested_mem_weights hbox hQ
  obtain ⟨hmapR, hmapY, hmapT⟩ := surfaceMap_nested_weights_le (polynomialEmbedding K) Q
  let D := surfaceMap (polynomialEmbedding K) Q
  obtain ⟨hD₁, hD₂, hD₃⟩ := surfaceCumulativeFlag_cumulative D
  obtain ⟨h₁, h₂, h₃⟩ := stagePartnerFlag_cumulative s gain
  intro d hd
  have hm := polynomialIn_surfaceCumulativeFlag D d hd
  rw [InFlag, hD₃, hD₂, hD₁] at hm
  change d 1 ≤ (stagePartnerFlag s gain).all ∧
    d 0 + d 1 ≤ middle (stagePartnerFlag s gain) ∧
    d 0 + d 1 + d 2 ≤ total (stagePartnerFlag s gain)
  rw [h₁, h₂, h₃]
  exact ⟨hm.1.trans (hmapR.trans hR), hm.2.1.trans (hmapY.trans hY), hm.2.2.trans (hmapT.trans hT)⟩

private theorem stage_support_of_factor {H : P4 K} {A : Finset (RegularIndex H)}
    {F : RegularIndex H} (hF : F ∈ A) (incoming : FlagDegree) (hpos : 0 < incoming.all)
    (hfit : Below (aggregateFlag H A) incoming) :
    ResidualSupportData (stageSupport incoming hpos) F.1 := by
  have hdiv : F.1 ∣ regularProduct H A :=
    ⟨regularCofactor H A F, (regularFactor_mul_cofactor H A F hF).symm⟩
  have h := contactFlag_below_of_dvd (regularProduct_ne_zero H A) hdiv
  refine ⟨h.1.trans hfit.1, ?_, ?_⟩
  · change _ ≤ max 2 (middle incoming)
    rw [← contactFlag_middle]
    exact (h.2.1.trans hfit.2.1).trans (le_max_right _ _)
  · change _ ≤ max 2 (total incoming)
    rw [← contactFlag_total]
    exact (h.2.2.trans hfit.2.2).trans (le_max_right _ _)

private theorem stage_support_small (incoming : FlagDegree) (hpos : 0 < incoming.all)
    (hcap : Below incoming primaryIncoming) (s : Stage) (gain : ℕ) :
    (stageSupport incoming hpos).total < 2130706433 ∧
      middle (stagePartnerFlag s gain) * (stageSupport incoming hpos).s +
        (stageSupport incoming hpos).ys * (stagePartnerFlag s gain).all < 2130706433 := by
  have hT : (stageSupport incoming hpos).total ≤ 53188 :=
    max_le (by decide +kernel) (hcap.2.2.trans_eq (by decide +kernel))
  have hY : (stageSupport incoming hpos).ys ≤ 360 :=
    max_le (by decide +kernel) (hcap.2.1.trans_eq (by decide +kernel))
  have hR : (stageSupport incoming hpos).s ≤ 80 := hcap.1
  have hy : middle (stagePartnerFlag s gain) ≤ 30394 := by
    rw [(stagePartnerFlag_cumulative s gain).2.1]
    cases s <;> decide +kernel
  have hr : (stagePartnerFlag s gain).all ≤ 6776 := by
    rw [(stagePartnerFlag_cumulative s gain).1]
    cases s <;> decide +kernel
  exact ⟨hT.trans_lt (by decide +kernel),
    (Nat.add_le_add (Nat.mul_le_mul hy hR) (Nat.mul_le_mul hY hr)).trans_lt (by decide +kernel)⟩

theorem regularFiber_le_paid_factor [CharP K 2130706433]
    (H : P4 K) (A : Finset (RegularIndex H)) (F : RegularIndex H) (hF : F ∈ A)
    (incoming : FlagDegree) (hpos : 0 < incoming.all) (hfit : Below (aggregateFlag H A) incoming)
    (hcap : Below incoming primaryIncoming) (s : Stage) (gain : ℕ)
    (Γ : Finset K) (selected : K → Polynomial K)
    {Node : Type*} (nodes : Finset Node) (x u₀ u₁ : Node → K) (hx : Set.InjOn x nodes)
    (hnodes : nodes.card = 262144)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ weight)
    (hagreement : ∀ γ ∈ Γ, agreement ≤
      (nodes.filter (fun i => (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ weight 81060)
    (Q : P4 K) (hrel : IsRelPrime F.1 Q)
    (hbox : Q ∈ nestedCoefficientBox K (s.multiplicity * agreement) weight
      (s.numbers.totalCap + gain) s.numbers.middleCap s.numbers.slopeCap)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ Q = 0) :
    (regularFiber H Γ selected F).card ≤
      flagMixed (contactFlag F.1) (stagePartnerFlag s gain) (stageScaledCut incoming hpos) / agreementScale := by
  classical
  let fiber := regularFiber H Γ selected F
  obtain ⟨hirr, _, hr⟩ := positiveRFactors_spec H F.1 F.2
  have hnF : ¬ F.1 ∣ Q := fun hd => hirr.not_isUnit (hrel dvd_rfl hd)
  have hnQ : Q ≠ 0 := fun hz => hnF (hz ▸ dvd_zero _)
  have hData := stage_support_of_factor hF incoming hpos hfit
  have ⟨hT, hmix⟩ := stage_support_small incoming hpos hcap s gain
  have hRchar : F.1.degreeOf 2 < 2130706433 :=
    (hData.coordinate_bounds.2.1.trans ((stageSupport incoming hpos).s_le_ys.trans
      (stageSupport incoming hpos).ys_le_total)).trans_lt hT
  have hsize : agreement ≤ nodes.card := by rw [hnodes]; decide +kernel
  have hsub : fiber ⊆ Γ := regularFiber_subset H Γ selected F
  have hcount := regular_carrier_seed_card_mul_le (stageSupport incoming hpos) F.1 Q hirr hnF
    2130706433 hr hRchar hData (stagePartnerFlag s gain) (surface_in_partner_flag s gain hnQ hbox)
    selected fiber nodes x u₀ u₁ hx weight agreement 81060
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hsize hT hmix
    (fun γ hγ => hdegree γ (hsub hγ))
    (fun γ hγ => (mem_regularFiber.mp hγ).2.1) (fun γ hγ => hsolution γ (hsub hγ))
    (fun γ hγ => (mem_regularFiber.mp hγ).2.2) (fun γ hγ => hagreement γ (hsub hγ))
    (noLargeSelectedPencil_mono selected Γ fiber weight 81060 hsub hnoPencil)
  apply (Nat.le_div_iff_mul_le agreementScale_pos).mpr
  rw [hnodes] at hcount
  rw [show weight = 131071 by decide +kernel, show agreement = 181084 by decide +kernel] at hcount
  simpa only [agreementScale_eq, stageScaledCut, fiber] using hcount

theorem paid_union_le_stagePrice
    (H : P4 K) (A U : Finset (RegularIndex H)) (hUA : U ⊆ A)
    (Γ : Finset K) (selected : K → Polynomial K) (incoming : FlagDegree)
    (hpos : 0 < incoming.all) (hfit : Below (aggregateFlag H A) incoming) (s : Stage) (gain : ℕ)
    (hcount : ∀ F ∈ U, (regularFiber H Γ selected F).card ≤
      flagMixed (contactFlag F.1) (stagePartnerFlag s gain) (stageScaledCut incoming hpos) / agreementScale) :
    (U.biUnion (regularFiber H Γ selected)).card ≤ stagePrice incoming hpos s gain := by
  classical
  let right := stagePartnerFlag s gain
  let cut := stageScaledCut incoming hpos
  apply (Nat.le_div_iff_mul_le agreementScale_pos).mpr
  have hsum : (∑ F ∈ U, flagMixed (contactFlag F.1) right cut) =
      flagMixed (aggregateFlag H U) right cut := by
    change _ = flagMixed (contactFlag (regularProduct H U)) right cut
    rw [contactFlag_regularProduct]
    simp only [mixed_expansion, sumFlag_all, sumFlag_middle, sumFlag_total,
      Finset.sum_add_distrib, Finset.mul_sum]
  calc
    _ ≤ (∑ F ∈ U, (regularFiber H Γ selected F).card) * agreementScale :=
      Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ F ∈ U, (regularFiber H Γ selected F).card * agreementScale := Finset.sum_mul _ _ _
    _ ≤ ∑ F ∈ U, flagMixed (contactFlag F.1) right cut :=
      Finset.sum_le_sum fun F hF => (Nat.le_div_iff_mul_le agreementScale_pos).mp (hcount F hF)
    _ = _ := hsum
    _ ≤ _ := mixed_mono_first
      ⟨(aggregateFlag_mono H hUA).1.trans hfit.1,
       (aggregateFlag_mono H hUA).2.1.trans hfit.2.1,
       (aggregateFlag_mono H hUA).2.2.trans hfit.2.2⟩ right cut

end

end ProximityPrize.SubmissionLower.Koala6831MovingPaid
