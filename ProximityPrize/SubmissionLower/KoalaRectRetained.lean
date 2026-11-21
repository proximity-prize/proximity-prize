import ProximityPrize.SubmissionLower.KoalaRectTerminal

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace KoalaRect
noncomputable section
open Polynomial MvPolynomial
open HighCore82219
open KoalaRectReceipts (paidCap)
open K1_14 (Equation FX L SeedBound seedEmbedding liftPoly atMark graphEval)
open K1_14_4 (seedDegree seedDegree_le_iff)
open K1_14_3 (ProjectedProduct)
open K1_14_1 (PoleData CRTLift MarkResidues seedPair)
open P1_7_7 (CRTChart poleProduct sheet_cover curve_scale_of_cut)
open scoped BigOperators

theorem seedBound_of_axis {f : Equation} {v : ℕ}
    (h : axisDegree f 0 + axisDegree f 1 ≤ v) : SeedBound f v := by
  classical
  intro i
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro e he
  have h0 := MvPolynomial.le_degreeOf_of_mem_support 0 he
  have h1 := MvPolynomial.le_degreeOf_of_mem_support 1 he
  have c0 := ((axisDegree_le_iff f 0 _).mp le_rfl i)
  have c1 := ((axisDegree_le_iff f 1 _).mp le_rfl i)
  change e.sum (fun _ n => n) ≤ v
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  omega

theorem persistent_at_cap {b : Band} {u del} (M : AnchorModel u del)
    {Γ} (F : AnchoredFamily M Γ) (hband : InBand b M.overhead)
    {H} (hH : AdjacentChart M F H) {f : Equation} (hf : Reduced f) {v : ℕ}
    (hseed : SeedBound f v) :
    RegularCount M F f (persistentFee (start b) (finish b) f.natDegree v) := by
  intro T hT hroots
  let w := M.overhead.toNat
  let d := 131071 + w
  let e := f.natDegree
  obtain ⟨hwlo, hwhi⟩ := window_nat hband
  obtain ⟨hlo, _, _, _, _⟩ := terminal_guards b
  have hw : 0 < w := hlo.trans_le hwlo
  have h2w : 2*w ≤ d := by
    have hh := (height_guards b).2
    dsimp only [d]
    change finish b ≤ 33425 at hh
    omega
  have hInv := band_invoice hwlo hwhi e v
  have hdp : d < K1.p := hInv.degree.trans (by decide)
  have hword : FixedWord M.word T F.scalar d := by
    refine ⟨F.distinct.mono hT, ?_, ?_⟩
    · intro γ hγ
      rcases (F.mark γ (hT hγ)).scalar_degree with hz | hdeg
      · simp only [hz, natDegree_zero, Nat.zero_le]
      · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at hdeg
        have hd' : ((F.scalar γ).natDegree : ℤ) ≤ 131071 + (w : ℤ) := by
          dsimp only [w]
          omega
        exact_mod_cast hd'
    · intro γ hγ
      let mark := F.mark γ (hT hγ)
      exact ⟨mark.bad.support, mark.bad.agreement, mark.scalar_hits⟩
  have hz : Set.InjOn M.label (T : Set K1.K) := fun _ _ _ _ h => sub_left_inj.mp h
  obtain ⟨CRT, hCRT⟩ := FrontCore82219.crt_chart M F H hw hH
  obtain ⟨hmonic, hdeg, hcenter, hnodes⟩ := FrontCore82219.pole_data (M := M) (F := F) hH
  have hchart := P1_7_7_2.proof d w e v hw h2w hdp (poleProduct H) hmonic hdeg hcenter hnodes
    f hf.1 le_rfl hseed T M.label F.scalar M.word hword.degree hroots CRT
    (fun γ hγ => hCRT γ (hT hγ))
  obtain ⟨Ps, hPs, hcard, hsum, hcover⟩ := sheet_cover
    (hInv.scale_pos.trans_le hInv.ordinate) (hInv.scale_pos.trans_le hInv.seed)
    f hf.1 (show f.natDegree ≤ e from le_rfl) hseed T M.label F.scalar hroots
  have hcount := count_cover hInv P1_7_7_3.proof (curve_scale_of_cut P1_7_7_3.proof) hword hchart hz Ps hPs hcover
  apply fee_of_bound hInv.scale_pos
  exact hcount.trans (add_le_add hsum (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) (by positivity)))

theorem small_ordinate {u del Γ} (M : AnchorModel u del) (F : AnchoredFamily M Γ)
    (hw : InBand .h2367 M.overhead) {H} (hH : AdjacentChart M F H) {f : Equation}
    (hf : Reduced f) (he : f.natDegree ≤ 2) (hseed : SeedBound f (paidCap f.natDegree))
    {T : Finset K1.K} (hT : T ⊆ Γ)
    (hr : ∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0) : T.card ≤ retainedCap .h2367 := by
  classical
  let e := f.natDegree
  let v := paidCap e
  have hepos : 1 ≤ e := hf.1
  change e ≤ 2 at he
  have hone : e = 1 ∨ e = 2 := by omega
  have hsep : singularDegree e v < K1.p := by
    rcases hone with hh | hh <;> simp only [v, hh] <;> decide
  have hfee : singularFee e v + persistentFee (start .h2367) (finish .h2367) e v ≤ retainedCap .h2367 := by
    rcases hone with hh | hh <;> simp only [v, hh] <;> decide +kernel
  let bad := T.filter fun γ => graphEval (M.label γ) (f.resultant f.derivative) = 0
  have hb : bad ⊆ T := Finset.filter_subset _ _
  have hbad := FrontCore82219.resultant_count M hf hseed hsep bad
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hreg : ∀ γ ∈ T \ bad, regularRoot f (M.label γ) (F.scalar γ) := by
    intro γ hγ
    obtain ⟨ht, hn⟩ := Finset.mem_sdiff.mp hγ
    exact P1_7.regular_of_resultant hf.1 (hr γ ht) (fun hz => hn (Finset.mem_filter.mpr ⟨ht,hz⟩))
  have hpart := Finset.card_sdiff_add_card_eq_card hb
  have hreg' := persistent_at_cap M F hw hH hf hseed _ (Finset.sdiff_subset.trans hT) hreg
  change bad.card ≤ singularFee e v at hbad
  change (T \ bad).card ≤ persistentFee (start .h2367) (finish .h2367) e v at hreg'
  omega

def RectPrice : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand .h2367 M.overhead → M.shift ∉ Γ → ∀ H, AdjacentChart M F H →
    ∀ C : ChartSource .h2367 M F, ∀ pairs : Pairs .h2367 M.overhead.toNat C.rows,
    ∀ Q : PrefixInventory .h2367 M F pairs, ∀ f : Equation, Reduced f →
    ProjectedProduct Q.parents f → 3 ≤ f.natDegree → f.natDegree < 28 → 0 < seedDegree f →
    axisDegree f 0 + axisDegree f 1 ≤ paidCap f.natDegree → ∀ T : Finset K1.K, T ⊆ Γ →
    (∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0) →
    T.card ≤ retainedCap .h2367

theorem retained_of_price (hbank : P3_7_1.BankOK (terminal .h2367)) (hPrice : RectPrice) : RetainedCountAt .h2367 := by
  intro u del M Γ F hw hshift H hH C pairs Q f hf hprod T hT hr
  obtain ⟨he, haxes⟩ := paid_degrees hbank hw C Q hf hprod
  by_cases hz : seedDegree f = 0
  · have hc := FrontCore82219.fixed_count M F T hT hf.1 ((seedDegree_le_iff f 0).mp hz.le) hr
    exact hc.trans ((show f.natDegree ≤ 28 by omega).trans (by decide))
  by_cases he2 : f.natDegree ≤ 2
  · exact small_ordinate M F hw hH hf he2 (seedBound_of_axis haxes) hT hr
  exact hPrice u del M Γ F hw hshift H hH C pairs Q f hf hprod (by omega) he
    (Nat.pos_of_ne_zero hz) haxes T hT hr

end
end KoalaRect
