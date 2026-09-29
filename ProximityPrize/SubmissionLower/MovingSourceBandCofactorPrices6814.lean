import ProximityPrize.SubmissionLower.MovingSourceBandNativeExit6814
import ProximityPrize.SubmissionLower.MovingSourceNativeFailurePair6814

/-! Retain the m/e distinctions in the cofactor price. The tight cell's
last case uses order<=10 from native failure; all other cases use the
already proved source/cofactor degree envelopes. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandCofactorPrices6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 25000
open RCN095 MovingSourceBandReceipts6814 MovingSourceBandIdentity6814
open MovingSourceCoupledClearing6814 MovingSourceNativeEnvelope6814 MovingSourcePairEnvelope6814

def bucket (m e : ℕ) : Fin 4 := if m=1 then 0 else if m=2 then (if e=0 then 1 else 2) else 3
def pairOrder (j : Fin 4) : ℕ := ![1,2,1,3] j
def uCap (i : Fin 11) (j : Fin 4) : ℕ := ![27246,40869,25974,if i=5 then 83328 else 83483] j
def vCap (i : Fin 11) (j : Fin 4) : ℕ := ![96906,146160,92848,if i=5 then 285576 else 294146] j

theorem bucket_order (m e : ℕ) (hm : 0<m) (he : e<copies3 m) :
    min m (3-e*m)=pairOrder (bucket m e) := by
  by_cases hm1 : m=1
  · subst m
    norm_num [copies3] at he
    simp [bucket,pairOrder]
    omega
  by_cases hm2 : m=2
  · subst m
    norm_num [copies3] at he
    interval_cases e <;> decide
  have hq : copies3 m=1 := by
    unfold copies3
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [hq] at he
  have he0 : e=0 := by omega
  subst e
  simp [bucket,hm1,hm2,pairOrder]
  omega

theorem cofactor_receipts (i : Fin 11) (j : Fin 4) :
    max (identityPrice (cell i).total (cell i).middle (cell i).slope)
      (numericPrice (cell i) (pairOrder j) (uCap i j) (vCap i j)+numericLeading (cell i))<
        270000000000000000 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem source_total_low (i : Fin 11) : 2985<(cell i).L := by fin_cases i <;> decide +kernel

variable {K : Type} [Field K]
local notation "Poly" => WholeSpaceCube6814.Poly (K:=K)

theorem cofactor_prices (i : Fin 11) (J Q : Poly) (m e : ℕ) (hm : 0<m) (he : e<copies3 m)
    (hb : copies3 m*slope J≤31) (hu : copies3 m*middle J≤98) (ht : copies3 m*total J≤995)
    (hcb : e*slope J+slope Q≤31) (hcu : e*middle J+middle Q≤98)
    (hct : e*total J+total Q≤1700) (hcs : e*order J+order Q≤14)
    (hsmall : i=5 → 3≤m → order J≤10) :
    flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitYZFlag≤uCap i (bucket m e) ∧
    flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitAllFlag≤vCap i (bucket m e) := by
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
  by_cases hm1 : m=1
  · subst m
    norm_num [copies3] at he hb hu ht
    have cap : CumulativeLe (ordinaryFlag J) ⟨299,27,10⟩ := by
      change (ordinaryFlag J).all≤10 ∧ (ordinaryFlag J).yz+(ordinaryFlag J).all≤37 ∧
        (ordinaryFlag J).zOnly+(ordinaryFlag J).yz+(ordinaryFlag J).all≤336
      omega
    change flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitYZFlag≤27246 ∧
      flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitAllFlag≤96906
    exact ⟨(mixed_mono_pair _ _ _ _ unitYZFlag cap capQ).trans_eq (by decide +kernel),
      (mixed_mono_pair _ _ _ _ unitAllFlag cap capQ).trans_eq (by decide +kernel)⟩
  by_cases hm2 : m=2
  · subst m
    norm_num [copies3] at he hb hu ht
    have cap : CumulativeLe (ordinaryFlag J) ⟨448,41,15⟩ := by
      change (ordinaryFlag J).all≤15 ∧ (ordinaryFlag J).yz+(ordinaryFlag J).all≤56 ∧
        (ordinaryFlag J).zOnly+(ordinaryFlag J).yz+(ordinaryFlag J).all≤504
      omega
    interval_cases e
    · change flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitYZFlag≤40869 ∧
        flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitAllFlag≤146160
      exact ⟨(mixed_mono_pair _ _ _ _ unitYZFlag cap capQ).trans_eq (by decide +kernel),
        (mixed_mono_pair _ _ _ _ unitAllFlag cap capQ).trans_eq (by decide +kernel)⟩
    · exact half_pair_bounds (ordinaryFlag J) (ordinaryFlag Q)
        cap.1 cap.2.1 cap.2.2 (by omega) (by omega) (by omega)
  have hm3 : 3≤m := by omega
  have hc : copies3 m=1 := by unfold copies3; exact Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [hc] at he
  have he0 : e=0 := by omega
  subst e
  have hbucket : bucket m 0=3 := by simp [bucket,hm1,hm2]
  rw [hbucket]
  by_cases hi : i=5
  · subst i
    change flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitYZFlag≤83328 ∧
      flagMixed (ordinaryFlag J) (ordinaryFlag Q) unitAllFlag≤285576
    exact MovingSourceNativeFailurePair6814.bounded_order_pair_prices J Q
      (by omega) (by omega) (by omega) (hsmall rfl hm3) (by omega) (by omega) (by omega) (by omega)
  · simp only [uCap,vCap,hi,if_false,Matrix.cons_val_succ,Matrix.cons_val_zero]
    exact ⟨(mixed_mono_pair _ _ _ _ unitYZFlag capJ capQ).trans_eq (by decide +kernel),
      (mixed_mono_pair _ _ _ _ unitAllFlag capJ capQ).trans_eq (by decide +kernel)⟩

#print axioms cofactor_prices
#print axioms cofactor_receipts
end
end ProximityPrize.SubmissionLower.MovingSourceBandCofactorPrices6814
