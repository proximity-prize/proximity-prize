import ProximityPrize.SubmissionLower.Koala6831ResidualLocalTopAvoidance
import ProximityPrize.SubmissionLower.Koala6831MovingPartition

namespace ProximityPrize.SubmissionLower.Koala6831Residual

open scoped Classical BigOperators
open RCN095 RCN130 RCN140 RCN156 RCN234 RCN266 RCN275 RCN286 RCN319
open LocatorBatchProductRoute LocatorFactorAggregate
open LocatorPhase6800Oracle (sumFlag)
open Koala6831Moving (contactFlag_regularProduct contactFlag_below_of_dvd
  contactFlag_all contactFlag_middle contactFlag_total)

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

variable {K N : Type} [Field K] [Fintype N]

def jetSmallEnvelope (f : Envelope) (cfg : Fin 3 → JetProfile) : Envelope :=
  (⟨f.slope, f.middle, jetSourceCap cfg⟩ : Envelope).pad 0

def Envelope.paddedSupport (f : Envelope) (tailRoom : ℕ) : ResidualSupportParameters where
  s := (f.pad tailRoom).slope
  ys := (f.pad tailRoom).middle
  total := (f.pad tailRoom).total
  one_le_s := by simp only [Envelope.pad]; omega
  s_le_ys := by simp only [Envelope.pad]; omega
  ys_le_total := by simp only [Envelope.pad]; omega
  two_le_ys := by simp only [Envelope.pad]; omega

private theorem weight_le_padded (F : MvPolynomial (Fin 4) K) (f : Envelope) (tailRoom : ℕ)
    (hf : wt residualSWeights F ≤ f.slope ∧ wt residualYSWeights F ≤ f.middle ∧
      wt residualTotalWeights F ≤ f.total) :
    ResidualSupportData (f.paddedSupport tailRoom) F := by
  constructor <;> simp only [Envelope.paddedSupport, Envelope.pad] <;> omega

private theorem cumulative_below_envelope (F : MvPolynomial (Fin 4) K) (f : Envelope)
    (hshape : f.slope ≤ f.middle ∧ f.middle ≤ f.total)
    (h : Below (originalCumulativeFlag F) f.flag) :
    wt residualSWeights F ≤ f.slope ∧ wt residualYSWeights F ≤ f.middle ∧
      wt residualTotalWeights F ≤ f.total := by
  obtain ⟨h₀, h₁, h₂⟩ := h
  change (originalCumulativeFlag F).all ≤ f.flag.all at h₀
  change middle (originalCumulativeFlag F) ≤ middle f.flag at h₁
  change total (originalCumulativeFlag F) ≤ total f.flag at h₂
  rw [contactFlag_all] at h₀
  rw [contactFlag_middle] at h₁
  rw [contactFlag_total] at h₂
  simp only [Envelope.flag, middle, total] at h₀ h₁ h₂
  exact ⟨h₀, by omega, by omega⟩

theorem profile_totalCap_le_jetSourceCap (cfg : Fin 3 → JetProfile) (j : Fin 3) :
    (cfg j).totalCap ≤ jetSourceCap cfg := by
  fin_cases j
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

def RetainedProfileSources (ids : Fin 18 × Fin 18 × Fin 18)
    (F : MvPolynomial (Fin 4) K) (nodes : N ↪ K) (u₀ u₁ : N → K) : Prop :=
  ∃ source : Fin 3 → MovingFiberThreeSources6811.Source F,
    ∀ j, let p := cellConfig ids j
      ProfileInterpolant p nodes u₀ u₁ (source j).P ∧
        (source j).B = p.secondCap ∧ (source j).U = p.middleCap ∧
        (source j).T = p.totalCap ∧ (source j).s = p.slopeCap ∧
        (source j).k = p.derivativeOrder ∧ (source j).n0 = p.minimumOrder

theorem route_regular_factor [CharP K 2130706433]
    (H : MvPolynomial (Fin 4) K) (remaining : Finset (RegularIndex H))
    (f : Envelope) (ids : Fin 18 × Fin 18 × Fin 18)
    (hshape : f.slope ≤ f.middle ∧ f.middle ≤ f.total)
    (hfit : Below (originalCumulativeFlag (regularProduct H remaining)) f.flag)
    (hN : Fintype.card N ≤ 262144) (nodes : N ↪ K) (u₀ u₁ : N → K)
    (F : RegularIndex H) (hF : F ∈ remaining) :
    let cfg := cellConfig ids
    let large := f.paddedSupport 2
    let small := (⟨f.slope, f.middle, jetSourceCap cfg⟩ : Envelope).paddedSupport 0
    (wt residualTotalWeights F.1 ≤ jetSourceCap cfg ∧ ResidualSupportData small F.1) ∨
      (jetSourceCap cfg < wt residualTotalWeights F.1 ∧ ResidualSupportData large F.1 ∧
        ((∃ j : Fin 3, ∃ Q,
          ProperProfileHelper F.1 Q (cfg j) large.s large.ys large.total nodes u₀ u₁) ∨
          RetainedProfileSources ids F.1 nodes u₀ u₁)) := by
  let cfg := cellConfig ids
  let large := f.paddedSupport 2
  have hdiv : F.1 ∣ regularProduct H remaining :=
    ⟨regularCofactor H remaining F, (regularFactor_mul_cofactor H remaining F hF).symm⟩
  have hbelow := contactFlag_below_of_dvd (regularProduct_ne_zero H remaining) hdiv
  have hb : Below (originalCumulativeFlag F.1) f.flag :=
    ⟨hbelow.1.trans hfit.1, hbelow.2.1.trans hfit.2.1, hbelow.2.2.trans hfit.2.2⟩
  have hweight := cumulative_below_envelope F.1 f hshape hb
  by_cases hsmall : wt residualTotalWeights F.1 ≤ jetSourceCap cfg
  · exact Or.inl ⟨hsmall, weight_le_padded _ _ _ ⟨hweight.1, hweight.2.1, hsmall⟩⟩
  have hlarge : ResidualSupportData large F.1 := weight_le_padded _ _ _ hweight
  apply Or.inr
  have hlargeDegree := Nat.lt_of_not_ge hsmall
  refine ⟨hlargeDegree, hlarge, ?_⟩
  have hcap (j : Fin 3) : (cfg j).totalCap < wt residualTotalWeights F.1 :=
    (profile_totalCap_le_jetSourceCap cfg j).trans_lt hlargeDegree
  have hirr := (RCN167.positiveRFactors_spec H F.1 F.2).1
  exact exists_cell_helper_or_sources ids hN F.1 large.s large.ys large.total
    nodes u₀ u₁ hirr hcap large.one_le_s (large.one_le_s.trans large.s_le_ys)
    (large.one_le_s.trans (large.s_le_ys.trans large.ys_le_total))
    ⟨hlarge.s_weight, hlarge.ys_weight, hlarge.total_weight⟩

def terminalScale : ℕ := 271926681406380

def jetFlagCharge (cuts : TailCorrections) (f : Envelope) (cfg : Fin 3 → JetProfile) (left : FlagDegree) : ℕ :=
  ((List.finRange 3).map
    (fun i => (![left.zOnly, left.yz, left.all] : Fin 3 → ℕ) i *
      jetChargeAxisWithCorrections cuts f cfg i)).sum

theorem jetFlagCharge_div (cuts : TailCorrections) (f : Envelope) (cfg : Fin 3 → JetProfile) :
    jetFlagCharge cuts f cfg f.flag / terminalScale = jetPriceWithCorrections cuts f cfg := rfl

private theorem three_charge_value (left : FlagDegree) (c : Fin 3 → ℕ) :
    ((List.finRange 3).map (fun i => (![left.zOnly, left.yz, left.all] : Fin 3 → ℕ) i * c i)).sum =
      left.zOnly * c 0 + left.yz * c 1 + left.all * c 2 := by
  change left.zOnly * c 0 + (left.yz * c 1 + (left.all * c 2 + 0)) = _
  rw [Nat.add_zero, Nat.add_assoc]

theorem jetFlagCharge_eq (cuts : TailCorrections) (f : Envelope) (cfg : Fin 3 → JetProfile) (left : FlagDegree) :
    jetFlagCharge cuts f cfg left =
      left.zOnly * jetChargeAxisWithCorrections cuts f cfg 0 +
        left.yz * jetChargeAxisWithCorrections cuts f cfg 1 +
        left.all * jetChargeAxisWithCorrections cuts f cfg 2 :=
  three_charge_value left (jetChargeAxisWithCorrections cuts f cfg)

theorem jetFlagCharge_mono (cuts : TailCorrections) (f : Envelope) (cfg : Fin 3 → JetProfile)
    {p q : FlagDegree} (hg : jetMonotoneWithCorrections cuts f cfg = true) (hpq : Below p q) :
    jetFlagCharge cuts f cfg p ≤ jetFlagCharge cuts f cfg q := by
  let c := jetChargeAxisWithCorrections cuts f cfg
  have hc : c 0 ≤ c 1 ∧ c 1 ≤ c 2 := of_decide_eq_true hg
  rw [jetFlagCharge_eq, jetFlagCharge_eq]
  change p.zOnly * c 0 + p.yz * c 1 + p.all * c 2 ≤ q.zOnly * c 0 + q.yz * c 1 + q.all * c 2
  rw [RCN131.linear_cost_cumulative _ _ _ _ hc.1 hc.2, RCN131.linear_cost_cumulative _ _ _ _ hc.1 hc.2]
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hpq.2.2)
    (Nat.mul_le_mul_left _ hpq.2.1)) (Nat.mul_le_mul_left _ hpq.1)

private theorem rawCharge_increments (cuts : TailCorrections) (f : Envelope) (left : FlagDegree) :
    rawChargeWithCorrections cuts f left =
      left.zOnly * rawChargeWithCorrections cuts f unitZFlag +
      left.yz * rawChargeWithCorrections cuts f unitYZFlag +
      left.all * rawChargeWithCorrections cuts f unitAllFlag := by
  simp only [rawChargeWithCorrections, flagMixed, unitZFlag, unitYZFlag, unitAllFlag]
  ring

theorem rawCharge_mul_le_jetFlagCharge (cuts : TailCorrections) (f : Envelope)
    (cfg : Fin 3 → JetProfile) (left : FlagDegree) :
    rawChargeWithCorrections cuts (jetSmallEnvelope f cfg) left * terminalScale ≤
      jetFlagCharge cuts f cfg left := by
  let short := jetSmallEnvelope f cfg
  have h₀ : rawChargeWithCorrections cuts short unitZFlag * terminalScale ≤
      jetChargeAxisWithCorrections cuts f cfg 0 := by
    unfold jetChargeAxisWithCorrections
    exact le_max_left _ _
  have h₁ : rawChargeWithCorrections cuts short unitYZFlag * terminalScale ≤
      jetChargeAxisWithCorrections cuts f cfg 1 := by
    unfold jetChargeAxisWithCorrections
    exact le_max_left _ _
  have h₂ : rawChargeWithCorrections cuts short unitAllFlag * terminalScale ≤
      jetChargeAxisWithCorrections cuts f cfg 2 := by
    unfold jetChargeAxisWithCorrections
    exact le_max_left _ _
  rw [rawCharge_increments]
  rw [jetFlagCharge_eq]
  simp only [Nat.add_mul, Nat.mul_assoc]
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ h₀)
    (Nat.mul_le_mul_left _ h₁)) (Nat.mul_le_mul_left _ h₂)

private theorem sum_jetFlagCharge {I : Type} (f : Envelope) (cfg : Fin 3 → JetProfile)
    (cuts : TailCorrections) (S : Finset I) (left : I → FlagDegree) :
    (∑ i ∈ S, jetFlagCharge cuts f cfg (left i)) = jetFlagCharge cuts f cfg (sumFlag S left) := by
  simp only [jetFlagCharge_eq, sumFlag, Finset.sum_add_distrib, Finset.sum_mul]

theorem jet_residue_card_le
    (H : MvPolynomial (Fin 4) K) (remaining : Finset (RegularIndex H))
    (f : Envelope) (cfg : Fin 3 → JetProfile) (cuts : TailCorrections)
    (hfit : Below (originalCumulativeFlag (regularProduct H remaining)) f.flag)
    (hmono : jetMonotoneWithCorrections cuts f cfg = true)
    (seeds : Finset K) (fiber : RegularIndex H → Finset K)
    (hcover : seeds ⊆ remaining.biUnion fiber)
    (hcount : ∀ F ∈ remaining, (fiber F).card * terminalScale ≤
      jetFlagCharge cuts f cfg (originalCumulativeFlag F.1)) :
    seeds.card ≤ jetPriceWithCorrections cuts f cfg := by
  rw [← jetFlagCharge_div]
  apply (Nat.le_div_iff_mul_le (show 0 < terminalScale by decide)).mpr
  calc
    _ ≤ (remaining.biUnion fiber).card * terminalScale :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hcover)
    _ ≤ (∑ F ∈ remaining, (fiber F).card) * terminalScale :=
      Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ F ∈ remaining, (fiber F).card * terminalScale :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ F ∈ remaining, jetFlagCharge cuts f cfg (originalCumulativeFlag F.1) :=
      Finset.sum_le_sum hcount
    _ = jetFlagCharge cuts f cfg (originalCumulativeFlag (regularProduct H remaining)) := by
      rw [sum_jetFlagCharge]
      exact congrArg (jetFlagCharge cuts f cfg) (contactFlag_regularProduct H remaining).symm
    _ ≤ _ := jetFlagCharge_mono cuts f cfg hmono hfit

theorem routed_jet_residue_card_le [CharP K 2130706433]
    (H : MvPolynomial (Fin 4) K) (remaining : Finset (RegularIndex H))
    (f : Envelope) (ids : Fin 18 × Fin 18 × Fin 18) (cuts : TailCorrections)
    (hshape : f.slope ≤ f.middle ∧ f.middle ≤ f.total)
    (hfit : Below (originalCumulativeFlag (regularProduct H remaining)) f.flag)
    (hmono : jetMonotoneWithCorrections cuts f (cellConfig ids) = true)
    (hN : Fintype.card N ≤ 262144) (nodes : N ↪ K) (u₀ u₁ : N → K)
    (seeds : Finset K) (fiber : RegularIndex H → Finset K)
    (hcover : seeds ⊆ remaining.biUnion fiber)
    (hraw : ∀ F ∈ remaining, wt residualTotalWeights F.1 ≤ jetSourceCap (cellConfig ids) →
      ResidualSupportData ((⟨f.slope, f.middle, jetSourceCap (cellConfig ids)⟩ : Envelope).paddedSupport 0) F.1 →
      (fiber F).card ≤ rawChargeWithCorrections cuts (jetSmallEnvelope f (cellConfig ids))
        (originalCumulativeFlag F.1))
    (hhelper : ∀ F ∈ remaining, jetSourceCap (cellConfig ids) < wt residualTotalWeights F.1 →
      ResidualSupportData (f.paddedSupport 2) F.1 →
      ∀ (j : Fin 3) (Q : MvPolynomial (Fin 4) K),
        ProperProfileHelper F.1 Q (cellConfig ids j)
          (f.paddedSupport 2).s (f.paddedSupport 2).ys (f.paddedSupport 2).total nodes u₀ u₁ →
        (fiber F).card * terminalScale ≤ jetFlagCharge cuts f (cellConfig ids)
          (originalCumulativeFlag F.1))
    (hgraph : ∀ F ∈ remaining, jetSourceCap (cellConfig ids) < wt residualTotalWeights F.1 →
      ResidualSupportData (f.paddedSupport 2) F.1 →
      RetainedProfileSources ids F.1 nodes u₀ u₁ →
        (fiber F).card * terminalScale ≤ jetFlagCharge cuts f (cellConfig ids)
          (originalCumulativeFlag F.1)) :
    seeds.card ≤ jetPriceWithCorrections cuts f (cellConfig ids) := by
  apply jet_residue_card_le H remaining f (cellConfig ids) cuts hfit hmono seeds fiber hcover
  intro F hF
  rcases route_regular_factor H remaining f ids hshape hfit hN nodes u₀ u₁ F hF with
    ⟨hsmall, hdata⟩ | ⟨hlarge, hdata, ⟨j, Q, hQ⟩ | hsources⟩
  · exact (Nat.mul_le_mul_right _ (hraw F hF hsmall hdata)).trans
      (rawCharge_mul_le_jetFlagCharge cuts f (cellConfig ids) (originalCumulativeFlag F.1))
  · exact hhelper F hF hlarge hdata j Q hQ
  · exact hgraph F hF hlarge hdata hsources

end

end ProximityPrize.SubmissionLower.Koala6831Residual

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
