import ProximityPrize.SubmissionLower.Koala6831MovingPartner
import ProximityPrize.SubmissionLower.Koala6831MovingStages

namespace ProximityPrize.SubmissionLower.Koala6831Moving

open scoped BigOperators
open ContactOrderBridge Koala6831MovingStages LocatorFactorAggregate LocatorLowQuotient
open LocatorBatchProductRoute (regularProduct regularFactor_ne_zero regularProduct_ne_zero)
open LocatorPhase6800Oracle (sumFlag sumFlag_all sumFlag_middle sumFlag_total)
open LocatorTwoFactorAvoidance (regularIndex_isRelPrime_of_ne wt_pow_eq)
open RCN081 RCN095 RCN156 RCN234

noncomputable section

variable {K : Type} [Field K]
local instance partitionDecidableEq : DecidableEq K := Classical.decEq _

abbrev contactFlag (P : P4 K) : FlagDegree := RCN130.originalCumulativeFlag P

@[simp] theorem contactFlag_all (P : P4 K) : (contactFlag P).all = wt residualSWeights P := rfl

@[simp] theorem contactFlag_middle (P : P4 K) : middle (contactFlag P) = wt residualYSWeights P :=
  (RCN130.originalCumulativeFlag_cumulative P).2.1

@[simp] theorem contactFlag_total (P : P4 K) : total (contactFlag P) = wt residualTotalWeights P :=
  (RCN130.originalCumulativeFlag_cumulative P).2.2

private theorem flag_eq_of_cumulative {a b : FlagDegree}
    (hR : a.all = b.all) (hY : middle a = middle b) (hT : total a = total b) : a = b := by
  cases a with
  | mk za ya ra =>
    cases b with
    | mk zb yb rb =>
      simp only [middle, total] at hR hY hT
      have hy : ya = yb := by omega
      have hz : za = zb := by omega
      cases hR; cases hy; cases hz
      rfl

theorem contactFlag_regularProduct (H : P4 K) (A : Finset (RCN266.RegularIndex H)) :
    contactFlag (regularProduct H A) = sumFlag A (fun F => contactFlag F.1) := by
  classical
  have h (weights : Fin 4 → ℕ) : wt weights (regularProduct H A) =
      ∑ F ∈ A, wt weights F.1 :=
    RCN071.weightedTotalDegree_prod_eq weights A (fun F => F.1)
      (fun F _ => regularFactor_ne_zero H F)
  apply flag_eq_of_cumulative <;> simp only [contactFlag_all, contactFlag_middle,
    contactFlag_total, sumFlag_all, sumFlag_middle, sumFlag_total, h]

theorem contactFlag_pow (P : P4 K) (hP : P ≠ 0) (n : ℕ) :
    contactFlag (P ^ n) = n • contactFlag P := by
  apply flag_eq_of_cumulative
  · simp only [contactFlag_all, nsmul_all, wt_pow_eq _ P hP]
  · rw [contactFlag_middle, wt_pow_eq _ P hP]
    simp only [middle, nsmul_yz, nsmul_all, ← Nat.mul_add]
    exact congrArg (n * ·) (contactFlag_middle P).symm
  · rw [contactFlag_total, wt_pow_eq _ P hP]
    simp only [total, nsmul_zOnly, nsmul_yz, nsmul_all, ← Nat.mul_add]
    exact congrArg (n * ·) (contactFlag_total P).symm

theorem contactFlag_below_of_dvd {P Q : P4 K} (hQ : Q ≠ 0) (h : P ∣ Q) :
    Below (contactFlag P) (contactFlag Q) := by
  simpa only [Below, contactFlag_all, contactFlag_middle, contactFlag_total, wt] using
    And.intro (weightedTotalDegree_le_of_dvd residualSWeights P Q h hQ)
      (And.intro (weightedTotalDegree_le_of_dvd residualYSWeights P Q h hQ)
        (weightedTotalDegree_le_of_dvd residualTotalWeights P Q h hQ))

private theorem below_trans {a b c : FlagDegree} (h₁ : Below a b) (h₂ : Below b c) :
    Below a c := ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩

private theorem exists_exact_order {A : Type*} [Monoid A] (F P : A) (roomOrder : ℕ)
    (h : ¬ F ^ (roomOrder + 1) ∣ P) :
    ∃ j ≤ roomOrder, ∃ S, P = F ^ j * S ∧ ¬ F ∣ S := by
  classical
  induction roomOrder with
  | zero =>
      refine ⟨0, le_rfl, P, by simp, ?_⟩
      simpa only [zero_add, pow_one] using h
  | succ k ih =>
      by_cases hdiv : F ^ (k + 1) ∣ P
      · obtain ⟨S, hS⟩ := hdiv
        refine ⟨k + 1, le_rfl, S, hS, ?_⟩
        rintro ⟨R, hR⟩
        exact h ⟨R, calc
          P = F ^ (k + 1) * (F * R) := by rw [hS, hR]
          _ = (F ^ (k + 1) * F) * R := (mul_assoc _ _ _).symm
          _ = F ^ (k + 1 + 1) * R := by rw [← pow_succ]⟩
      · obtain ⟨j, hj, S, hS, hexact⟩ := ih hdiv
        exact ⟨j, hj.trans (Nat.le_succ _), S, hS, hexact⟩

theorem regularProduct_pow_dvd_of_each (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (P : P4 K) (n : ℕ) (hdvd : ∀ F ∈ A, F.1 ^ n ∣ P) :
    regularProduct H A ^ n ∣ P := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [regularProduct]
  | @insert F A hFA ih =>
      have hcop : IsRelPrime F.1 (regularProduct H A) := by
        unfold regularProduct
        apply IsRelPrime.prod_right
        intro G hG
        apply regularIndex_isRelPrime_of_ne H F G
        exact fun h => hFA (Subtype.ext h ▸ hG)
      have hpow : IsRelPrime (F.1 ^ n) (regularProduct H A ^ n) := hcop.pow_left.pow_right
      have hins : regularProduct H (insert F A) = F.1 * regularProduct H A := by
        simp only [regularProduct, Finset.prod_insert hFA]
      rw [hins, mul_pow]
      exact hpow.mul_dvd (hdvd F (Finset.mem_insert_self F A))
        (ih fun G hG => hdvd G (Finset.mem_insert_of_mem hG))

def roomResidualFactors (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (source : Set (P4 K)) (roomOrder : ℕ) : Finset (RCN266.RegularIndex H) := by
  classical
  exact A.filter fun F => ∀ P ∈ source, F.1 ^ (roomOrder + 1) ∣ P

theorem mem_roomResidualFactors (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (source : Set (P4 K)) (roomOrder : ℕ) (F : RCN266.RegularIndex H) :
    F ∈ roomResidualFactors H A source roomOrder ↔
      F ∈ A ∧ ∀ P ∈ source, F.1 ^ (roomOrder + 1) ∣ P := by
  classical
  exact Finset.mem_filter

theorem roomResidualFactors_subset (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (source : Set (P4 K)) (roomOrder : ℕ) : roomResidualFactors H A source roomOrder ⊆ A :=
  fun F hF => ((mem_roomResidualFactors H A source roomOrder F).mp hF).1

theorem roomResidual_power_dvd (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (source : Set (P4 K)) (roomOrder : ℕ) {P : P4 K} (hP : P ∈ source) :
    regularProduct H (roomResidualFactors H A source roomOrder) ^ (roomOrder + 1) ∣ P :=
  regularProduct_pow_dvd_of_each H _ P _ fun F hF =>
    ((mem_roomResidualFactors H A source roomOrder F).mp hF).2 P hP

private theorem sumFlag_split {ι : Type} [DecidableEq ι] {A R : Finset ι} (hR : R ⊆ A)
    (flag : ι → FlagDegree) : sumFlag (A \ R) flag + sumFlag R flag = sumFlag A flag := by
  apply flag_eq_of_cumulative
  · simpa only [add_all, sumFlag_all] using Finset.sum_sdiff (f := fun i => (flag i).all) hR
  · have hmiddle (P Q : FlagDegree) : middle (P + Q) = middle P + middle Q := by
      simp only [middle, add_yz, add_all]
      omega
    simpa only [hmiddle, sumFlag_middle] using Finset.sum_sdiff (f := fun i => middle (flag i)) hR
  · have htotal (P Q : FlagDegree) : total (P + Q) = total P + total Q := by
      simp only [total, add_zOnly, add_yz, add_all]
      omega
    simpa only [htotal, sumFlag_total] using Finset.sum_sdiff (f := fun i => total (flag i)) hR

theorem room_partition_flag [DecidableEq K] (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (source : Set (P4 K)) (roomOrder : ℕ) (incoming : FlagDegree)
    (hincoming : Below (contactFlag (regularProduct H A)) incoming) :
    Below (sumFlag (A \ roomResidualFactors H A source roomOrder) (fun F => contactFlag F.1) +
      contactFlag (regularProduct H (roomResidualFactors H A source roomOrder))) incoming := by
  classical
  rw [contactFlag_regularProduct H _, sumFlag_split (roomResidualFactors_subset H A source roomOrder)]
  simpa only [contactFlag_regularProduct H A] using hincoming

theorem room_residual_caps (H : P4 K) (A : Finset (RCN266.RegularIndex H))
    (source : Set (P4 K)) (roomOrder : ℕ) (incoming cap : FlagDegree)
    (hincoming : Below (contactFlag (regularProduct H A)) incoming)
    {P : P4 K} (hP : P ∈ source) (hPne : P ≠ 0) {cutoff w : ℕ}
    (hbox : P ∈ nestedCoefficientBox K cutoff w (total cap) (middle cap) cap.all) :
    let residual := contactFlag (regularProduct H (roomResidualFactors H A source roomOrder))
    residual.all ≤ min incoming.all (cap.all / (roomOrder + 1)) ∧
    middle residual ≤ min (middle incoming) (middle cap / (roomOrder + 1)) ∧
    total residual ≤ min (total incoming) (total cap / (roomOrder + 1)) := by
  let R := roomResidualFactors H A source roomOrder
  let J := regularProduct H R
  have hsub : J ∣ regularProduct H A :=
    Finset.prod_dvd_prod_of_subset R A (fun F => F.1) (roomResidualFactors_subset H A source roomOrder)
  have hleft : Below (contactFlag J) incoming :=
    below_trans (contactFlag_below_of_dvd (regularProduct_ne_zero H A) hsub) hincoming
  have hpow : J ^ (roomOrder + 1) ∣ P := roomResidual_power_dvd H A source roomOrder hP
  obtain ⟨hT, hY, hR, _⟩ := nested_mem_weights hbox hPne
  have hright : Below (contactFlag P) cap := by
    simpa only [Below, contactFlag_all, contactFlag_middle, contactFlag_total] using
      And.intro hR (And.intro hY hT)
  exact room_remaining_caps roomOrder _ incoming cap hleft
    (by simpa only [contactFlag_pow J (regularProduct_ne_zero H R)] using
      below_trans (contactFlag_below_of_dvd hPne hpow) hright)

theorem FlowData.exists_partner_of_not_mem_roomResidual {p : ℕ} [CharP K p]
    (B : FlowData K) {I : Type*} (node u₀ u₁ normalized : I → K)
    (h₀ : ∀ i, B.d0.eval (node i) * u₀ i + B.c0.eval (node i) =
      B.a0.eval (node i) * normalized i)
    (h₁ : ∀ i, B.d0.eval (node i) * u₁ i + B.c1.eval (node i) =
      B.a1.eval (node i) * normalized i)
    (H : P4 K) (A : Finset (RCN266.RegularIndex H)) (source : Set (P4 K))
    {roomOrder w delta m cutoff finalCutoff totalCap middleCap slopeCap : ℕ}
    (hroom : cutoff + roomOrder * (2 * delta) ≤ finalCutoff) (hp : roomOrder < p)
    (hw : 0 < w) (hdelta : 0 < delta)
    (hden : B.d0.natDegree + max B.a0.natDegree B.a1.natDegree ≤ delta)
    (hminor : (B.a1 * B.c0 - B.a0 * B.c1).natDegree ≤ w + delta)
    (hsources : ∀ P ∈ source,
      P ∈ nestedCoefficientBox K cutoff w totalCap middleCap slopeCap ∧
        ∀ i, ContactAtLeast K (node i) (u₀ i) (u₁ i) m P)
    {F : RCN266.RegularIndex H} (hFA : F ∈ A)
    (hFnot : F ∉ roomResidualFactors H A source roomOrder) (htrans : ¬ F.1 ∣ B.flow F.1) :
    ∃ Q : P4 K, IsRelPrime F.1 Q ∧
      Q ∈ nestedCoefficientBox K finalCutoff w (totalCap + roomOrder) middleCap slopeCap ∧
      ∀ i, ContactAtLeast K (node i) (u₀ i) (u₁ i) m Q := by
  classical
  have hfail : ¬ ∀ P ∈ source, F.1 ^ (roomOrder + 1) ∣ P := fun h =>
    hFnot ((mem_roomResidualFactors H A source roomOrder F).mpr ⟨hFA, h⟩)
  push Not at hfail
  obtain ⟨P, hP, horder⟩ := hfail
  obtain ⟨j, hj, S, hS, hSnot⟩ := exists_exact_order F.1 P roomOrder horder
  have hij : cutoff + j * (2 * delta) ≤ finalCutoff :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) cutoff).trans hroom
  obtain ⟨hbox, hcontact⟩ := hsources P hP
  rw [hS] at hbox hcontact
  obtain ⟨Q, hrel, hQbox, hQcontact⟩ := B.exists_contact_partner_of_room node u₀ u₁ normalized
    h₀ h₁ (RCN167.positiveRFactors_spec H F.1 F.2).1 hSnot htrans (hj.trans_lt hp)
    hw hdelta hden hminor hij hbox hcontact
  refine ⟨Q, hrel, ?_, hQcontact⟩
  intro d hd
  obtain ⟨ht, hy, hr, hw'⟩ := hQbox hd
  exact ⟨ht.trans (Nat.add_le_add_left hj totalCap), hy, hr, hw'⟩

end

end ProximityPrize.SubmissionLower.Koala6831Moving
