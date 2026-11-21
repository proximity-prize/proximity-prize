import ProximityPrize.SubmissionLower.Effective70Poles
import ProximityPrize.SubmissionLower.High52Regular

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000
set_option maxHeartbeats 5000000

namespace Rect52RegularSmall
noncomputable section

open Polynomial Finset
open High52 (asLooseModel asLooseFamily AnchorModel AnchoredFamily K agreement blockLength p
  Reduced RegularCount persistentFee FixedWord count_cover fee_of_bound Invoice scale
  degreeAt muNum lambdaNum quotientOrder ordinateFee seedFee)
open K1_14 (Equation SeedBound)
open P1_7_7 (poleProduct sheet_cover curve_scale_of_cut)
open private coordinate_bounds from ProximityPrize.SubmissionLower.UpperBranch7

theorem interval_invoice {lo hi w : ℕ} (hw : 0 < w) (hwlo : lo ≤ w) (hwhi : w ≤ hi)
    (hhi : hi ≤ 33463)
    (e v : ℕ) :
    Invoice (131071+w) w e v (ordinateFee lo hi e) (seedFee lo hi v)
      (scale hi) := by
  have hdhi : degreeAt hi < agreement := by
    change 131071 + hi < 179905
    omega
  have hd : 131071+w < agreement := (Nat.add_le_add_left hwhi _).trans_lt hdhi
  have hA : agreement ≤ blockLength := by decide
  have hD : 0 < scale hi := Nat.mul_pos (by decide) (Nat.sub_pos_of_lt hdhi)
  have hm : scale hi ≤ muNum hi :=
    Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hA _)
  have hpos : 1 ≤ 2*hi := by omega
  refine ⟨hD, hm.trans (Nat.le_add_right _ _), ?_, hd, ?_⟩
  · exact hm.trans ((by
      simpa only [one_mul] using Nat.mul_le_mul_right (muNum hi) hpos :
      muNum hi ≤ 2*hi*muNum hi).trans (Nat.le_add_right _ _))
  · intro s hs
    have hord : (131071+w) - 2*w ≤ quotientOrder lo := by
      unfold quotientOrder P1_7.quotientOrder
      omega
    exact coordinate_bounds hA (Nat.add_le_add_left hwhi _) hdhi hwhi hord hs
theorem persistent_count {h lo hi u del} (M : AnchorModel u del)
    {Γ} (F : AnchoredFamily M Γ) (hw : 0 < h) (hwlo : lo ≤ h) (hwhi : h ≤ hi)
    (hhi : hi ≤ 33463) (hactual : M.overhead.toNat ≤ h)
    {H} (hH : Effective70Poles.Chart h (asLooseModel M) (asLooseFamily M F) H)
    {f : Equation} {v : ℕ} (hf : Reduced f) (hseed : SeedBound f v) :
    RegularCount M F f (persistentFee lo hi f.natDegree v) := by
  intro T hT hroots
  let w := h
  let d := 131071 + w
  let e := f.natDegree
  have h2w : 2 * w ≤ d := by dsimp only [d]; omega
  have hInv := interval_invoice hw hwlo hwhi hhi e v
  have hdp : d < p := hInv.degree.trans (by decide)
  have hword : FixedWord M.word T F.scalar d := by
    refine ⟨F.distinct.mono hT, ?_, ?_⟩
    · intro γ hγ
      exact (High52.degree_at_height M F γ (hT hγ)).trans (Nat.add_le_add_left hactual _)
    · intro γ hγ
      let mark := F.mark γ (hT hγ)
      exact ⟨mark.bad.support, mark.bad.agreement, mark.scalar_hits⟩
  have hz : Set.InjOn M.label (T : Set K) := fun _ _ _ _ h => sub_left_inj.mp h
  obtain ⟨CRT, hCRT⟩ := Effective70Poles.crt_chart (asLooseModel M) (asLooseFamily M F) H hw hH
  obtain ⟨hmonic, hdeg, hcenter, hnodes⟩ :=
    Effective70Poles.pole_data (M := asLooseModel M) (F := asLooseFamily M F) hH
  have hchart := P1_7_7_2.proof d w e v hw h2w hdp (poleProduct H) hmonic hdeg hcenter hnodes
    f hf.1 le_rfl hseed T M.label F.scalar M.word hword.degree hroots CRT
    (fun γ hγ => hCRT γ (hT hγ))
  obtain ⟨Ps, hPs, hcard, hsum, hcover⟩ := sheet_cover
    (hInv.scale_pos.trans_le hInv.ordinate) (hInv.scale_pos.trans_le hInv.seed)
    f hf.1 (show f.natDegree ≤ e from le_rfl) hseed T M.label F.scalar hroots
  have hcount := count_cover hInv P1_7_7_3.proof (curve_scale_of_cut P1_7_7_3.proof) hword hchart hz Ps hPs hcover
  apply fee_of_bound hInv.scale_pos
  refine hcount.trans (add_le_add hsum ?_)
  have hc : (Ps.card : ℚ) ≤ e := by exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_left hc (sq_nonneg (((scale hi : ℕ) : ℚ)))

end
end Rect52RegularSmall

#print axioms Rect52RegularSmall.persistent_count
