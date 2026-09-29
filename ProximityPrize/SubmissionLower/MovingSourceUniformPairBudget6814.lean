import ProximityPrize.SubmissionLower.MovingSourcePairEnvelope6814

/-! Every power-avoidance cofactor fits one common mixed ledger price.
Only the actual source/cofactor degree charges are used; native-failure
arithmetic and enumeration of the 803/807 rows are unnecessary here. -/
namespace ProximityPrize.SubmissionLower.MovingSourceUniformPairBudget6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 20000
open RCN095 MovingSourcePairEnvelope6814 MovingSourceCoupledClearing6814
open MovingSourceNativeEnvelope6814

variable {K : Type} [Field K]
local notation "Poly" => WholeSpaceCube6814.Poly (K:=K)

theorem cofactor_pair_prices (J Q : Poly) (m e : ℕ) (hm : 0<m) (he : e<copies3 m)
    (hb : copies3 m*slope J≤31) (hu : copies3 m*middle J≤98) (ht : copies3 m*total J≤995)
    (hcb : e*slope J+slope Q≤31) (hcu : e*middle J+middle Q≤98)
    (hct : e*total J+total Q≤1700) (hcs : e*order J+order Q≤14) :
    flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitZFlag≤6014 ∧
    flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitYZFlag≤83483 ∧
    flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitYZFlag≤min m (3-e*m)*28420 ∧
    flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitAllFlag≤min m (3-e*m)*98890 := by
  have hj := ordinaryFlag_cumulative J
  have hq := ordinaryFlag_cumulative Q
  have hnj := source_nested J
  have hnq := source_nested Q
  have hpos := copies3_pos m hm
  have hb1 := Nat.mul_le_mul_right (slope J) hpos
  have hu1 := Nat.mul_le_mul_right (middle J) hpos
  have ht1 := Nat.mul_le_mul_right (total J) hpos
  have capJ : CumulativeLe (ordinaryFlag J) ⟨897,82,31⟩ := by
    change (ordinaryFlag J).all≤31 ∧ (ordinaryFlag J).yz+(ordinaryFlag J).all≤113 ∧
      (ordinaryFlag J).zOnly+(ordinaryFlag J).yz+(ordinaryFlag J).all≤1010
    omega
  have capQ : CumulativeLe (ordinaryFlag Q) ⟨1602,81,31⟩ := by
    change (ordinaryFlag Q).all≤31 ∧ (ordinaryFlag Q).yz+(ordinaryFlag Q).all≤112 ∧
      (ordinaryFlag Q).zOnly+(ordinaryFlag Q).yz+(ordinaryFlag Q).all≤1714
    omega
  have raw (axis : FlagDegree) := mixed_mono_pair _ _ _ _ axis capJ capQ
  refine ⟨(raw unitZFlag).trans_eq (by decide +kernel),
    (raw unitYZFlag).trans_eq (by decide +kernel),?_⟩
  by_cases hm1 : m=1
  · subst m
    norm_num [copies3] at he hb hu ht
    have cap : CumulativeLe (ordinaryFlag J) ⟨299,27,10⟩ := by
      change (ordinaryFlag J).all≤10 ∧ (ordinaryFlag J).yz+(ordinaryFlag J).all≤37 ∧
        (ordinaryFlag J).zOnly+(ordinaryFlag J).yz+(ordinaryFlag J).all≤336
      omega
    have hy : flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitYZFlag≤27246 :=
      (mixed_mono_pair _ _ _ _ unitYZFlag cap capQ).trans_eq (by decide +kernel)
    have ha : flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitAllFlag≤96906 :=
      (mixed_mono_pair _ _ _ _ unitAllFlag cap capQ).trans_eq (by decide +kernel)
    have hd : min 1 (3-e*1)=1 := by omega
    rw [hd]
    exact ⟨hy.trans (by decide),ha.trans (by decide)⟩
  by_cases hm2 : m=2
  · subst m
    norm_num [copies3] at he hb hu ht
    have cap : CumulativeLe (ordinaryFlag J) ⟨448,41,15⟩ := by
      change (ordinaryFlag J).all≤15 ∧ (ordinaryFlag J).yz+(ordinaryFlag J).all≤56 ∧
        (ordinaryFlag J).zOnly+(ordinaryFlag J).yz+(ordinaryFlag J).all≤504
      omega
    interval_cases e
    · have hy : flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitYZFlag≤40869 :=
        (mixed_mono_pair _ _ _ _ unitYZFlag cap capQ).trans_eq (by decide +kernel)
      have ha : flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitAllFlag≤146160 :=
        (mixed_mono_pair _ _ _ _ unitAllFlag cap capQ).trans_eq (by decide +kernel)
      change flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitYZFlag≤56840 ∧
        flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitAllFlag≤197780
      exact ⟨hy.trans (by decide),ha.trans (by decide)⟩
    · have hc := half_pair_bounds (ordinaryFlag J) (ordinaryFlag Q)
        cap.1 cap.2.1 cap.2.2 (by omega) (by omega) (by omega)
      change flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitYZFlag≤28420 ∧
        flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitAllFlag≤98890
      exact ⟨hc.1.trans (by decide),hc.2.trans (by decide)⟩
  have hm3 : 3≤m := by omega
  have hc : copies3 m=1 := by unfold copies3; exact Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [hc] at he
  have he0 : e=0 := by omega
  subst e
  have hd : min m (3-0*m)=3 := by omega
  rw [hd]
  have hy : flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitYZFlag≤83483 := (raw unitYZFlag).trans_eq (by decide +kernel)
  have ha : flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitAllFlag≤294146 := (raw unitAllFlag).trans_eq (by decide +kernel)
  exact ⟨hy.trans (by decide),ha.trans (by decide)⟩

#print axioms cofactor_pair_prices
end
end ProximityPrize.SubmissionLower.MovingSourceUniformPairBudget6814
