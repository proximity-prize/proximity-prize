import ProximityPrize.SubmissionLower.Bridge6925Cover
import ProximityPrize.SubmissionLower.HighMassBridge6921

set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace Bridge6925
open K21 H21 Polynomial

private theorem banks_eq {w : ℤ} (hw : w ≤ 3554) :
    P0_10.scheduled w = H21.scheduled w := by
  simp only [P0_10.scheduled, P0_10.freeShape, P0_10.movingShape, P0_10.fullShape,
    P0_10.terminalShape, H21.scheduled, H21.terminalShape, H21.band, ite_eq_left hw]
  rfl

private theorem source_restrict {u del Γ} {M : AnchorModel u del} (F : AnchoredFamily M Γ)
    {rows : Banks} (hw : M.overhead ≤ 3554) (hr : H21.JetSource M F rows)
    {T : Finset K} (hs : T ⊆ Γ) :
    P0_10.JetSource M (⟨F.scalar, fun z hz => F.mark z (hs hz), F.distinct.mono hs⟩ :
      AnchoredFamily M T) rows := by
  let mem {s} (h : s ∈ P0_10.scheduled M.overhead) : s ∈ H21.scheduled M.overhead :=
    banks_eq hw ▸ h
  exact ⟨fun _ h _ h' => hr.nested _ (mem h) _ (mem h'),
    fun _ h W hW P hP z hz => hr.necessary _ (mem h) W hW P hP z (hs hz),
    fun _ h => hr.shape _ (mem h), fun _ h => hr.leading _ (mem h),
    fun _ h => hr.shift _ (mem h), fun _ h => hr.floor_bound _ (mem h)⟩

theorem first : H21.c2 := by
  classical
  intro u del M Γ F lo hi H chart rows hr
  let T := Γ.erase M.shift
  have sub : T ⊆ Γ := Finset.erase_subset _ _
  let G : AnchoredFamily M T := ⟨F.scalar, fun z hz => F.mark z (sub hz), F.distinct.mono sub⟩
  have src : P0_10.JetSource M G rows := source_restrict F hi hr sub
  have center : M.shift ∉ T := Finset.notMem_erase _ _
  obtain ⟨pairs⟩ := P0_10_2.proof u del M T G lo hi rows src
  have degree : P0_10R.c3 := by
    intro u' del' M' Γ' F' hl hu banks source f hf hd
    have mem {s} (h : s ∈ H21.scheduled M'.overhead) : s ∈ P0_10.scheduled M'.overhead :=
      (banks_eq hu).symm ▸ h
    have raw : H21.JetSource M' F' banks :=
      ⟨fun _ h _ h' => source.nested _ (mem h) _ (mem h'), fun _ h => source.necessary _ (mem h),
       fun _ h => source.shape _ (mem h), fun _ h => source.leading _ (mem h),
       fun _ h => source.shift _ (mem h), fun _ h => source.floor_bound _ (mem h)⟩
    have same : (HighMassBridge6921.choose M'.overhead).fullBank = P0_10.fullShape M'.overhead := by
      simp only [HighMassBridge6921.choose, P0_10.fullShape, P0_10.terminalShape, H21.terminalShape,
        H21.band, ite_eq_left hu]
      rfl
    have q := HighMassBridge6921.ordinate raw hl (hu.trans (by decide : (3554 : ℤ) ≤ 32970)) f hf
      (by rw [same]; exact hd)
    simpa only [H21.band,ite_eq_left hu] using q
  have result := P0_10R.Bridge.cover P0_10R_1.proof P0_10R_2.proof P0_10R_Late.proof degree
    u del M T G lo hi center rows src pairs
  have erased : Γ.card - 1 ≤ T.card := Finset.pred_card_le_card_erase
  have room : P0.highPrefix M.overhead + 1 ≤ K21.highPrefix M.overhead := by
    unfold P0.highPrefix K21.highPrefix
    rw [ite_eq_left hi]
  rcases result with cheap | long
  · exact Or.inl (by omega)
  · obtain ⟨C⟩ := long
    refine Or.inr ⟨C.kept,C.subset.trans sub,?_,C.equation,
      ⟨C.projected.positive,C.y_bound,C.projected.primitive,C.projected.separable⟩,C.divides,?_⟩
    · have ha := Finset.card_sdiff_add_card_eq_card C.subset
      have hb := Finset.card_sdiff_add_card_eq_card (C.subset.trans sub)
      have := C.paid
      omega
    · intro z hz
      obtain ⟨q,hq,hmark⟩ := C.covers z hz
      have hz' := RingHom.mem_ker.mp (hmark (C.projected.vanishes q hq))
      simpa only [coe_eval₂RingHom, eval₂_C, atMark, G] using hz'
end Bridge6925
