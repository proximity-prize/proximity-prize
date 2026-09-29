import ProximityPrize.SubmissionLower.MovingSourceBandNativeArithmetic6814

/-! Spend the native leading exception inside the existing 120e12
reserve, and exclude padded owners from the failure branch at270e15. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandNativeExit6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 25000
open RCN095 RCN135 RCN136 RCN156 RCN234 RCN260
open MovingSourceBandGeometry6814 MovingSourceBandReceipts6814 MovingSourceBandNativeCount6814
open MovingSourceBandLeading6814 MovingSourceBandIdentity6814 MovingFiberThreeSources6811
open MovingSourceBandNativeArithmetic6814 MovingSourceBandNativeForms6814 MovingSourceNativeEnvelope6814

theorem leading_reserve (i : Fin 11) (b u t : ℕ) (hb : b≤31) (hu : u≤98) (ht : t≤995) :
    Gates (cell i).total (cell i).middle (cell i).slope b u t ∧
    AsymmetricHelper.leftRegularCountCap (pair (cell i).total (cell i).middle (cell i).slope b u t)≤120000000000000 := by
  fin_cases i <;>
    norm_num [Gates,pair,cell,AsymmetricHelper.leftRegularCountCap,AsymmetricHelper.leftRegularNumerator,
      UnequalParameters.gap,UnequalParameters.errors,UnequalParameters.leftAgreement,UnequalParameters.mixedCost,RCN294.dot] <;>
    omega

theorem padded_scalar_fits (i : Fin 11) (m s b t : ℕ)
    (hm : 0<m) (hs : 2≤s) (hms : m≤s) (hsb : 2*s≤b) (hbt : b≤t)
    (hB : copies3 m*b≤31) (hT : copies3 m*t≤995) (hex : 3≤m → 5≤s) :
    scalar i m s b b t<3*269880000000000000*m := by
  have hl := scalar_linear i m s b b t hms hsb le_rfl hbt
  generalize hv : scalar i m s b b t=v at hl ⊢
  by_cases hm1 : m=1
  · subst m
    norm_num [copies3] at hB hT
    fin_cases i <;> norm_num [form] at hl <;> omega
  by_cases hm2 : m=2
  · subst m
    norm_num [copies3] at hB hT
    fin_cases i <;> norm_num [form] at hl <;> omega
  have hm3 : 3≤m := by omega
  have hs5 := hex hm3
  have hq : copies3 m=1 := by
    unfold copies3
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [hq] at hB hT
  fin_cases i <;> norm_num [form] at hl <;> omega

theorem failure_five_order_le_ten (m s b u t : ℕ)
    (hm : 3≤m) (hb : b≤31) (hu : u≤98) (ht : t≤995)
    (hf : Failure 5 m s b u t) : s≤10 := by
  change 355688123463259200*m+67309222137259641*s≤
    29746364480525841*b+7705577043726672*u+110916132481287*t at hf
  omega

variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K}

theorem native_small_packet_count (i : Fin 11)
    (P : Packet x (cell i).total (cell i).middle (cell i).slope) (S : Source P.F)
    (hk : S.k<2130706433) (hFT : S.T<wt residualTotalWeights P.F)
    (hB : S.B≤31) (hU : S.U≤98) (hT : S.T≤995)
    (hfit : nativeNumerator S (cell i).total (cell i).middle (cell i).slope
      ⟨(cell i).total-(cell i).middle,(cell i).middle-(cell i).slope,(cell i).slope⟩<
      3*269880000000000000*S.d) :
    P.seeds.card<270000000000000000 := by
  have hb := leading_reserve i (S.B-2*S.n0) (S.U-S.n0) (S.T-S.n0) (by omega) (by omega) (by omega)
  have hh := native_packet_count P S hk hFT hb.1
  have hd : 0<3*S.d := by dsimp [Source.d]; omega
  have hmain : nativeNumerator S (cell i).total (cell i).middle (cell i).slope
      ⟨(cell i).total-(cell i).middle,(cell i).middle-(cell i).slope,(cell i).slope⟩/(3*S.d)<
      269880000000000000 := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hfit
  have hlead : leadingPrice S (cell i).total (cell i).middle (cell i).slope≤120000000000000 := hb.2
  have hidentity := (receipts i).2.2.2.2
  apply hh.trans_lt
  apply max_lt_iff.mpr
  constructor
  · exact lt_of_le_of_lt (le_max_left _ _) hidentity
  · omega

#print axioms padded_scalar_fits
#print axioms failure_five_order_le_ten
#print axioms native_small_packet_count
end
end ProximityPrize.SubmissionLower.MovingSourceBandNativeExit6814
