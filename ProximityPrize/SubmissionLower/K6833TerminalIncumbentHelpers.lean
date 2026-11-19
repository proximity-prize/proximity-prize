/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- 68.33 terminal specialization, derived from Lucieno PR 618, BitWonka PR 581 and Bome2017’s accepted 68.32 proof. Apache-2.0. -/
import ProximityPrize.SubmissionLower.K6833TerminalLedger
import ProximityPrize.SubmissionLower.K6833TerminalHelperPrice

namespace ProximityPrize.SubmissionLower.K6833Residual

open scoped Classical
open RCN095 RCN130 RCN156 RCN234 RCN238 RCN243 RCN275 RCN286 RCN313 RCN319
open LocatorFactorAggregate
open Koala6831Moving (contactFlag_all contactFlag_middle contactFlag_total)

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

variable {K N : Type} [Field K] [Fintype N]

def Envelope.endpointSupport (f : Envelope) (hmin : 1 ≤ f.slope ∧ 2 ≤ f.middle)
    (hshape : f.slope ≤ f.middle ∧ f.middle ≤ f.total) : ResidualSupportParameters :=
  ⟨f.slope, f.middle, f.total, hmin.1, hshape.1, hshape.2, hmin.2⟩

theorem endpointSupport_of_flag_below (F : MvPolynomial (Fin 4) K) (f : Envelope)
    (hmin : 1 ≤ f.slope ∧ 2 ≤ f.middle) (hshape : f.slope ≤ f.middle ∧ f.middle ≤ f.total)
    (hf : Below (originalCumulativeFlag F) f.flag) :
    ResidualSupportData (f.endpointSupport hmin hshape) F := by
  obtain ⟨h₀, h₁, h₂⟩ := hf
  change (originalCumulativeFlag F).all ≤ f.flag.all at h₀
  change middle (originalCumulativeFlag F) ≤ middle f.flag at h₁
  change total (originalCumulativeFlag F) ≤ total f.flag at h₂
  rw [contactFlag_all] at h₀
  rw [contactFlag_middle] at h₁
  rw [contactFlag_total] at h₂
  simp only [Envelope.flag, middle, total] at h₀ h₁ h₂
  constructor <;> simp only [Envelope.endpointSupport] <;> omega

theorem incumbent_jet_pair_gates (f : Envelope) (cfg : Fin 3 → JetProfile) (j : Fin 3)
    (h : jetGatesWithCorrections TailCorrections.original f cfg = true) :
    let p := cfg j
    let supp := f.paddedSupport 2
    p.secondCap ≤ p.middleCap ∧ p.middleCap ≤ p.totalCap ∧
      p.middleCap * f.slope + f.middle * p.secondCap < 2130706433 ∧
      (helperEnvelope p supp).middle * f.slope + f.middle * (helperEnvelope p supp).slope < 2130706433 := by
  simp only [jetGatesWithCorrections, Bool.and_eq_true, List.all_eq_true] at h
  have hj := h.2 j (by simp)
  have hshape := of_decide_eq_true hj.1.1
  have hl := (of_decide_eq_true hj.1.2).2.2
  have hh := (of_decide_eq_true hj.2).2.2
  have hs : f.slope ≤ (f.pad 2).slope := le_max_right _ _
  have hm : f.middle ≤ (f.pad 2).middle := le_max_left _ _
  have hle (right : Envelope) :
      right.middle * f.slope + f.middle * right.slope ≤
        (f.pad 2).middle * right.slope + (f.pad 2).slope * right.middle := by
    rw [Nat.add_comm, Nat.mul_comm right.middle]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ hm) (Nat.mul_le_mul_right _ hs)
  exact ⟨hshape.2.1, hshape.2.2.1, (hle (cfg j).leading).trans_lt hl,
    (hle ((cfg j).helper (f.pad 2))).trans_lt hh⟩

theorem incumbent_profile_helper_count [CharP K 2130706433]
    (f : Envelope) (cfg : Fin 3 → JetProfile) (j : Fin 3)
    (hmin : 1 ≤ f.slope ∧ 2 ≤ f.middle) (hshape : f.slope ≤ f.middle ∧ f.middle ≤ f.total)
    (hTotal : f.total < 2130706433)
    (hg : jetGatesWithCorrections TailCorrections.original f cfg = true)
    (F Q : MvPolynomial (Fin 4) K) (hirr : Irreducible F) (hpos : 0 < F.degreeOf (2 : Fin 4))
    (hF : Below (originalCumulativeFlag F) f.flag)
    (nodes : N ↪ K) (u₀ u₁ : N → K) (hN : Fintype.card N ≤ 262144) (hn : 181049 ≤ Fintype.card N)
    (hQ : ProperProfileHelper F Q (cfg j) (f.paddedSupport 2).s
      (f.paddedSupport 2).ys (f.paddedSupport 2).total nodes u₀ u₁)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071)
    (hregular : ∀ g ∈ seeds, RegularSolution F (selected g) g)
    (hagreement : ∀ g ∈ seeds, 181049 ≤
      (Finset.univ.filter (fun i => (selected g).eval (nodes i) = u₀ i + g * u₁ i)).card)
    (hpencil : NoLargeSelectedPencil selected seeds 131071 81095) :
    seeds.card * terminalScale ≤ jetFlagCharge TailCorrections.original f cfg (originalCumulativeFlag F) := by
  let supp := f.endpointSupport hmin hshape
  obtain ⟨h₁, h₂, _, hpair⟩ := incumbent_jet_pair_gates f cfg j hg
  have hbound := proper_profile_helper_card_mul_le (cfg j) (f.paddedSupport 2) supp F Q
    hirr hpos (endpointSupport_of_flag_below F f hmin hshape hF) hTotal h₁ h₂ hpair
    nodes u₀ u₁ hn hQ selected seeds hdegree hregular hagreement hpencil
  exact helper_count_mul_le_jetFlagCharge TailCorrections.original (Fintype.card N) seeds.card
    f cfg j (originalCumulativeFlag F) supp rfl rfl rfl hN hbound

theorem individual_profile_helper_count [CharP K 2130706433]
    (f : Envelope) (cfg : Fin 3 → JetProfile) (j : Fin 3)
    (hmin : 1 ≤ f.slope ∧ 2 ≤ f.middle) (hshape : f.slope ≤ f.middle ∧ f.middle ≤ f.total)
    (hTotal : f.total < 2130706433)
    (hg : jetGatesWithCorrections TailCorrections.original f cfg = true)
    (F Q : MvPolynomial (Fin 4) K) (hirr : Irreducible F) (hpos : 0 < F.degreeOf (2 : Fin 4))
    (hF : Below (originalCumulativeFlag F) f.flag)
    (nodes : N ↪ K) (u₀ u₁ : N → K) (hN : Fintype.card N ≤ 262144) (hn : 181049 ≤ Fintype.card N)
    (hQ : ProperProfileHelper F Q (cfg j) (f.paddedSupport 2).s
      (f.paddedSupport 2).ys (f.paddedSupport 2).total nodes u₀ u₁)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071)
    (hregular : ∀ g ∈ seeds, RegularSolution F (selected g) g)
    (hagreement : ∀ g ∈ seeds, 181049 ≤
      (Finset.univ.filter (fun i => (selected g).eval (nodes i) = u₀ i + g * u₁ i)).card)
    (hpencil : NoLargeSelectedPencil selected seeds 131071 81095) :
    seeds.card * terminalScale ≤ flagMixed (originalCumulativeFlag F) ((cfg j).helper (f.pad 2)).flag
      (shortenedDirection f (pencilBudget * residualPriceScale)) := by
  let supp := f.endpointSupport hmin hshape
  obtain ⟨h₁, h₂, _, hpair⟩ := incumbent_jet_pair_gates f cfg j hg
  have hbound := proper_profile_helper_card_mul_le (cfg j) (f.paddedSupport 2) supp F Q
    hirr hpos (endpointSupport_of_flag_below F f hmin hshape hF) hTotal h₁ h₂ hpair
    nodes u₀ u₁ hn hQ selected seeds hdegree hregular hagreement hpencil
  exact terminal_pair_count_scaled_le (Fintype.card N) seeds.card f _ _ supp rfl rfl rfl hN hbound

end

end ProximityPrize.SubmissionLower.K6833Residual

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
