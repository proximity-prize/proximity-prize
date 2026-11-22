import ProximityPrize.SubmissionLower.Peer653High53FamilyInvoice

-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Family.lean.

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace Peer653High53
noncomputable section
open Polynomial MvPolynomial
open Peer653High53 (AnchorModel AnchoredFamily Band I K agreement node p)
open K1_14 (Equation FX L SeedBound seedEmbedding liftPoly)
open K1_14_1 (PoleData CRTLift MarkResidues seedPair)
open P1_7_7 (CRTChart poleProduct sheet_cover curve_scale_of_cut)
open scoped BigOperators
theorem persistent_count {b : Band} {u del} (M : AnchorModel u del)
    {Γ} (F : AnchoredFamily M Γ) (hband : InBand b M.overhead)
    {H} (hH : AdjacentChart M F H) (i : GradeIndex b) {f : Equation}
    (hf : Reduced f) (hseed : SeedBound f ((grades b).get i).seedCap) :
    RegularCount M F f (persistentFee (start b) (finish b) f.natDegree ((grades b).get i).seedCap) := by
  intro T hT hroots
  let w := M.overhead.toNat
  let d := 131071 + w
  let e := f.natDegree
  let v := ((grades b).get i).seedCap
  obtain ⟨hwlo, hwhi⟩ := window_nat hband
  obtain ⟨hlo, hhi, _, _, _⟩ := terminal_guards b
  have hw : 0 < w := hlo.trans_le hwlo
  have h2w : 2 * w ≤ d := by dsimp only [d]; omega
  have hInv := band_invoice hwlo hwhi e v
  have hdp : d < p := hInv.degree.trans (by decide)
  have hword : FixedWord M.word T F.scalar d := by
    refine ⟨F.distinct.mono hT, ?_, ?_⟩
    · intro γ hγ
      rcases (F.mark γ (hT hγ)).scalar_degree with hz | hdeg
      · simp only [hz, natDegree_zero, Nat.zero_le]
      · change ((F.scalar γ).natDegree : ℤ) ≤ 131072 - 1 + M.overhead at hdeg
        have hd' : ((F.scalar γ).natDegree : ℤ) ≤ 131071 + (w : ℤ) := by
          dsimp only [w]
          omega
        exact_mod_cast hd'
    · intro γ hγ
      let mark := F.mark γ (hT hγ)
      exact ⟨mark.bad.support, mark.bad.agreement, mark.scalar_hits⟩
  have hz : Set.InjOn M.label (T : Set K) := fun _ _ _ _ h => sub_left_inj.mp h
  obtain ⟨CRT, hCRT⟩ := High53Model.crt_chart M F H hw hH
  obtain ⟨hmonic, hdeg, hcenter, hnodes⟩ :=
    High53Model.pole_data (M := M) (F := F) hH
  have hchart := P1_7_7_2.proof d w e v hw h2w hdp (poleProduct H) hmonic hdeg hcenter hnodes
    f hf.1 le_rfl hseed T M.label F.scalar M.word hword.degree hroots CRT
    (fun γ hγ => hCRT γ (hT hγ))
  obtain ⟨Ps, hPs, hcard, hsum, hcover⟩ := sheet_cover
    (hInv.scale_pos.trans_le hInv.ordinate) (hInv.scale_pos.trans_le hInv.seed)
    f hf.1 (show f.natDegree ≤ e from le_rfl) hseed T M.label F.scalar hroots
  have hcount := count_cover hInv P1_7_7_3.proof (curve_scale_of_cut P1_7_7_3.proof) hword hchart hz Ps hPs hcover
  apply fee_of_bound hInv.scale_pos
  refine hcount.trans (add_le_add hsum ?_)
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) (sq_nonneg (scale (finish b) : ℚ))
end
end Peer653High53
end
