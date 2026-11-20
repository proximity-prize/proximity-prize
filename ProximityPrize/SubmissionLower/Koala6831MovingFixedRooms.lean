/- Originally by Lucieno, Proximity Prize PR 618, Apache-2.0. Retuned for 81,066 errors.
-/
import ProximityPrize.SubmissionLower.Koala6831MovingPartition
import ProximityPrize.SubmissionLower.Koala6831MovingSources
import ProximityPrize.SubmissionLower.Koala6831MovingLedger

namespace ProximityPrize.SubmissionLower.Koala6831Moving

open ContactOrderBridge Koala6831MovingLedger Koala6831MovingSources LocatorFactorAggregate LocatorLowQuotient
open LocatorBatchProductRoute (regularProduct regularProduct_dvd_carrier regularProduct_ne_zero)
open LocatorPhase6800Oracle (sumFlag)
open RCN095

noncomputable section

variable {K I : Type} [Field K] [Fintype I]

def stageContactFlag (s : Stage) : FlagDegree :=
  ⟨s.numbers.totalCap - s.numbers.middleCap, s.numbers.middleCap - s.numbers.slopeCap,
    s.numbers.slopeCap⟩

@[simp] theorem stageContactFlag_all (s : Stage) : (stageContactFlag s).all = s.numbers.slopeCap := rfl

@[simp] theorem stageContactFlag_middle (s : Stage) : middle (stageContactFlag s) = s.numbers.middleCap := by
  cases s <;> decide +kernel

@[simp] theorem stageContactFlag_total (s : Stage) : total (stageContactFlag s) = s.numbers.totalCap := by
  cases s <;> decide +kernel

def stageRoomFamily (s : Stage) (nodes u₀ u₁ : I → K) : Set (P4 K) :=
  Set.range (s.reconstruct K nodes u₀ u₁)

def stageRoomResidual (s : Stage) (nodes u₀ u₁ : I → K)
    (H : P4 K) (A : Finset (RCN266.RegularIndex H)) : Finset (RCN266.RegularIndex H) :=
  roomResidualFactors H A (stageRoomFamily s nodes u₀ u₁) s.roomOrder

theorem stageRoomResidual_subset (s : Stage) (nodes u₀ u₁ : I → K)
    (H : P4 K) (A : Finset (RCN266.RegularIndex H)) :
    stageRoomResidual s nodes u₀ u₁ H A ⊆ A :=
  roomResidualFactors_subset H A _ _

theorem stageRoom_residual_caps (s : Stage) (nodes u₀ u₁ : I → K)
    (hcard : Fintype.card I ≤ 262144) (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (incoming : FlagDegree) (hincoming : Below (contactFlag (regularProduct H A)) incoming) :
    let residual := contactFlag (regularProduct H (stageRoomResidual s nodes u₀ u₁ H A))
    residual.all ≤ min incoming.all (s.numbers.slopeCap / (s.roomOrder + 1)) ∧
    middle residual ≤ min (middle incoming) (s.numbers.middleCap / (s.roomOrder + 1)) ∧
    total residual ≤ min (total incoming) (s.numbers.totalCap / (s.roomOrder + 1)) := by
  obtain ⟨v, hv⟩ := s.exists_source K nodes u₀ u₁ hcard
  have hbox : s.reconstruct K nodes u₀ u₁ v ∈ nestedCoefficientBox K s.cutoff weight
      (total (stageContactFlag s)) (middle (stageContactFlag s)) (stageContactFlag s).all := by
    simpa only [stageContactFlag_total, stageContactFlag_middle, stageContactFlag_all] using
      s.reconstruct_mem_box K nodes u₀ u₁ v
  have h := room_residual_caps H A (stageRoomFamily s nodes u₀ u₁) s.roomOrder incoming
    (stageContactFlag s) hincoming ⟨v, rfl⟩ hv hbox
  simpa only [stageRoomResidual, stageContactFlag_total, stageContactFlag_middle, stageContactFlag_all] using h

theorem two_room_residue_caps (nodes u₀ u₁ : I → K) (hcard : Fintype.card I ≤ 262144)
    (H : P4 K) (hH : H ≠ 0) (A : Finset (RCN266.RegularIndex H))
    (hprimary : H ∈ nestedCoefficientBox K Stage.primary.cutoff weight
      Stage.primary.numbers.totalCap Stage.primary.numbers.middleCap Stage.primary.numbers.slopeCap) :
    let first := stageRoomResidual Stage.room1 nodes u₀ u₁ H A
    let second := stageRoomResidual Stage.room2 nodes u₀ u₁ H first
    Below (contactFlag (regularProduct H first)) ⟨15120, 179, 52⟩ ∧
      Below (contactFlag (regularProduct H second)) ⟨15213, 108, 30⟩ := by
  let first := stageRoomResidual Stage.room1 nodes u₀ u₁ H A
  let firstCap : FlagDegree := ⟨15120, 179, 52⟩
  obtain ⟨hT, hY, hR, _⟩ := nested_mem_weights hprimary hH
  have hproduct := contactFlag_below_of_dvd hH (regularProduct_dvd_carrier H A)
  have hincoming : Below (contactFlag (regularProduct H A)) (stageContactFlag Stage.primary) := by
    refine ⟨hproduct.1.trans ?_, hproduct.2.1.trans ?_, hproduct.2.2.trans ?_⟩
    · simpa only [contactFlag_all, stageContactFlag_all] using hR
    · simpa only [contactFlag_middle, stageContactFlag_middle] using hY
    · simpa only [contactFlag_total, stageContactFlag_total] using hT
  have hfirstRaw := stageRoom_residual_caps Stage.room1 nodes u₀ u₁ hcard H A _ hincoming
  have hfirst : Below (contactFlag (regularProduct H first)) firstCap := by
    exact ⟨hfirstRaw.1.trans (by dsimp only [firstCap]; decide +kernel),
      hfirstRaw.2.1.trans (by dsimp only [firstCap]; decide +kernel),
      hfirstRaw.2.2.trans (by dsimp only [firstCap]; decide +kernel)⟩
  have hsecondRaw := stageRoom_residual_caps Stage.room2 nodes u₀ u₁ hcard H first _ hfirst
  exact ⟨hfirst, hsecondRaw.1.trans (by dsimp only [firstCap]; decide +kernel),
    hsecondRaw.2.1.trans (by dsimp only [firstCap]; decide +kernel),
    hsecondRaw.2.2.trans (by dsimp only [firstCap]; decide +kernel)⟩

theorem FlowData.exists_vanishing_stage_room_partner [CharP K 2130706433]
    (B : FlowData K) (nodes : I ↪ K) (u₀ u₁ normalized : I → K)
    (h₀ : ∀ i, B.d0.eval (nodes i) * u₀ i + B.c0.eval (nodes i) =
      B.a0.eval (nodes i) * normalized i)
    (h₁ : ∀ i, B.d0.eval (nodes i) * u₁ i + B.c1.eval (nodes i) =
      B.a1.eval (nodes i) * normalized i)
    (hden : B.d0.natDegree + max B.a0.natDegree B.a1.natDegree ≤ 9553)
    (hminor : (B.a1 * B.c0 - B.a0 * B.c1).natDegree ≤ weight + 9553)
    (s : Stage) (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    {F : RCN266.RegularIndex H} (hFA : F ∈ A) (htrans : ¬ F.1 ∣ B.flow F.1)
    (hremoved : F ∉ stageRoomResidual s nodes u₀ u₁ H A)
    (Γ : Finset K) (selected : K → Polynomial K) (support : K → Finset I)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ weight)
    (hcard : ∀ γ ∈ Γ, agreement ≤ (support γ).card)
    (hvalues : ∀ γ ∈ Γ, ∀ i ∈ support γ, (selected γ).eval (nodes i) = u₀ i + γ * u₁ i) :
    ∃ Q : P4 K, IsRelPrime F.1 Q ∧
      Q ∈ nestedCoefficientBox K (s.multiplicity * agreement) weight
        (s.numbers.totalCap + s.roomOrder) s.numbers.middleCap s.numbers.slopeCap ∧
      ∀ γ ∈ Γ, RCN319.specialization K (selected γ) γ Q = 0 := by
  have hsources : ∀ P ∈ stageRoomFamily s nodes u₀ u₁,
      P ∈ nestedCoefficientBox K s.cutoff weight s.numbers.totalCap s.numbers.middleCap s.numbers.slopeCap ∧
        ∀ i, ContactAtLeast K (nodes i) (u₀ i) (u₁ i) s.multiplicity P := by
    rintro _ ⟨v, rfl⟩
    exact ⟨s.reconstruct_mem_box K nodes u₀ u₁ v, s.reconstruct_contact K nodes u₀ u₁ v⟩
  have hchar : s.roomOrder < 2130706433 := by cases s <;> decide +kernel
  obtain ⟨Q, hrel, hbox, hcontact⟩ := B.exists_partner_of_not_mem_roomResidual nodes u₀ u₁ normalized
    h₀ h₁ H A (stageRoomFamily s nodes u₀ u₁) s.room_cutoff hchar
    (by decide +kernel) (by decide +kernel) hden hminor hsources hFA hremoved htrans
  refine ⟨Q, hrel, hbox, ?_⟩
  classical
  intro γ hγ
  exact specialization_zero_of_box_and_agreement nodes u₀ u₁ s Q (selected γ) γ
    (support γ) hbox (fun i _ => hcontact i) (hdegree γ hγ) (hcard γ hγ) (hvalues γ hγ)

set_option maxHeartbeats 1000000 in

theorem stageRoom_card_add_credit_of_subset [DecidableEq K]
    (s : Stage) (nodes u₀ u₁ : I → K) (H : P4 K)
    (A final : Finset (RCN266.RegularIndex H))
    (hfinal : final ⊆ stageRoomResidual s nodes u₀ u₁ H A)
    (seeds : RCN266.RegularIndex H → Finset K)
    (incoming right cut : FlagDegree) {denominator : ℕ} (hdenominator : 0 < denominator)
    (hincoming : Below (contactFlag (regularProduct H A)) incoming)
    (hcount : ∀ F ∈ A \ stageRoomResidual s nodes u₀ u₁ H A,
      (seeds F).card ≤ flagMixed (contactFlag F.1) right cut / denominator) :
    ((A \ stageRoomResidual s nodes u₀ u₁ H A).biUnion seeds).card +
      flagMixed (creditFlag (contactFlag (regularProduct H final))) right cut / denominator ≤
      flagMixed incoming right cut / denominator := by
  let R := stageRoomResidual s nodes u₀ u₁ H A
  let removed := sumFlag (A \ R) (fun F => contactFlag F.1)
  have hdiv : regularProduct H final ∣ regularProduct H R :=
    Finset.prod_dvd_prod_of_subset final R (fun F => F.1) hfinal
  have hsubset := contactFlag_below_of_dvd (regularProduct_ne_zero H R) hdiv
  have hsplit : Below (removed + contactFlag (regularProduct H R)) incoming :=
    room_partition_flag H A (stageRoomFamily s nodes u₀ u₁) s.roomOrder incoming hincoming
  have hbounds : Below (removed + contactFlag (regularProduct H final)) incoming := by
    simp only [Below, middle, total, add_all, add_yz, add_zOnly] at hsubset hsplit ⊢
    omega
  exact room_card_add_credit_le (A \ R) (fun F => contactFlag F.1) seeds
    (contactFlag (regularProduct H final)) incoming right cut hdenominator hbounds hcount

def transverseRoomFactors (B : FlowData K) (H : P4 K) : Finset (RCN266.RegularIndex H) := by
  classical
  exact Finset.univ.filter fun F => ¬ F.1 ∣ B.flow F.1

end

end ProximityPrize.SubmissionLower.Koala6831Moving

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
