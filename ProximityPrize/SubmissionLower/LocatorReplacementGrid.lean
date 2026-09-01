import ProximityPrize.SubmissionLower.LocatorFactorReplacement
namespace ProximityPrize.SubmissionLower.LocatorReplacementGrid
open RCN095 LocatorFactorAggregate LocatorFactorReplacement
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
abbrev CoarseCell:=Fin 16 × Fin 19 × Fin 19
def coarseR (c:CoarseCell):ℕ:=c.1.val+1
def coarseYlo (c:CoarseCell):ℕ:=coarseR c+4*c.2.1.val
def coarseYhi (c:CoarseCell):ℕ:=min 76 (coarseYlo c+3)
def coarseTlo (c:CoarseCell):ℕ:=128*c.2.2.val
def coarseThi (c:CoarseCell):ℕ:=min 2382 (coarseTlo c+127)
def HardCoarse (c:CoarseCell):Prop:=
  (coarseR c=8 ∧ coarseYlo c=48 ∧ coarseTlo c=1280) ∨
  (coarseR c=9 ∧ coarseYlo c=41 ∧ coarseTlo c=1280) ∨
  (coarseR c=9 ∧ coarseYlo c=45 ∧ coarseTlo c=1280) ∨
  (coarseR c=9 ∧ coarseYlo c=49 ∧ coarseTlo c=1152) ∨
  (coarseR c=9 ∧ coarseYlo c=53 ∧ coarseTlo c=1152) ∨
  (coarseR c=10 ∧ coarseYlo c=38 ∧ coarseTlo c=1280) ∨
  (coarseR c=10 ∧ coarseYlo c=42 ∧ coarseTlo c=1152) ∨
  (coarseR c=10 ∧ coarseYlo c=42 ∧ coarseTlo c=1280) ∨
  (coarseR c=10 ∧ coarseYlo c=46 ∧ coarseTlo c=1152) ∨
  (coarseR c=10 ∧ coarseYlo c=50 ∧ coarseTlo c=1024) ∨
  (coarseR c=10 ∧ coarseYlo c=50 ∧ coarseTlo c=1152) ∨
  (coarseR c=11 ∧ coarseYlo c=39 ∧ coarseTlo c=1280) ∨
  (coarseR c=11 ∧ coarseYlo c=43 ∧ coarseTlo c=1152) ∨
  (coarseR c=11 ∧ coarseYlo c=47 ∧ coarseTlo c=1024) ∨
  (coarseR c=11 ∧ coarseYlo c=47 ∧ coarseTlo c=1152) ∨
  (coarseR c=12 ∧ coarseYlo c=44 ∧ coarseTlo c=1152)
instance (c:CoarseCell):Decidable (HardCoarse c):=by unfold HardCoarse;infer_instance
structure FineCell where
  parent:{c:CoarseCell // HardCoarse c}
  yi:Fin 4
  ti:Fin 4
deriving DecidableEq,Fintype
def fineR (c:FineCell):ℕ:=coarseR c.parent.1
def fineY (c:FineCell):ℕ:=coarseYlo c.parent.1+c.yi.val
def fineTlo (c:FineCell):ℕ:=coarseTlo c.parent.1+32*c.ti.val
def fineThi (c:FineCell):ℕ:=fineTlo c+31
def HardFine (_c:FineCell):Prop:=False
instance (c:FineCell):Decidable (HardFine c):=by unfold HardFine;infer_instance
structure UnitCell where
  parent:{c:FineCell // HardFine c}
  ti:Fin 32
deriving DecidableEq,Fintype
def unitR (c:UnitCell):ℕ:=fineR c.parent.1
def unitY (c:UnitCell):ℕ:=fineY c.parent.1
def unitT (c:UnitCell):ℕ:=fineTlo c.parent.1+c.ti.val
abbrev Cell:=CoarseCell ⊕ (FineCell ⊕ UnitCell)
def r:Cell→ℕ
  | .inl c=>coarseR c
  | .inr (.inl c)=>fineR c
  | .inr (.inr c)=>unitR c
def ylo:Cell→ℕ
  | .inl c=>coarseYlo c
  | .inr (.inl c)=>fineY c
  | .inr (.inr c)=>unitY c
def yhi:Cell→ℕ
  | .inl c=>coarseYhi c
  | .inr (.inl c)=>fineY c
  | .inr (.inr c)=>unitY c
def tlo:Cell→ℕ
  | .inl c=>coarseTlo c
  | .inr (.inl c)=>fineTlo c
  | .inr (.inr c)=>unitT c
def thi:Cell→ℕ
  | .inl c=>coarseThi c
  | .inr (.inl c)=>fineThi c
  | .inr (.inr c)=>unitT c
theorem yhi_le_76 (c:Cell):yhi c≤76:=by
  rcases c with c|c
  · exact Nat.min_le_left _ _
  · rcases c with c|c
    · have hp:=c.parent.2
      simp only [yhi,fineY]
      rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> omega
    · exact c.parent.2.elim
theorem thi_le_2319 (c:Cell):thi c≤2382:=by
  rcases c with c|c
  · exact Nat.min_le_left _ _
  · rcases c with c|c
    · have hp:=c.parent.2
      have hti:=c.ti.isLt
      simp only [thi,fineThi,fineTlo]
      rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> omega
    · exact c.parent.2.elim
def Leaf:Cell→Prop
  | .inl c=>¬HardCoarse c
  | .inr (.inl c)=>¬HardFine c
  | .inr (.inr _)=>True
instance (c:Cell):Decidable (Leaf c):=by
  rcases c with c|c
  · simp only [Leaf];infer_instance
  · rcases c with c|c
    · simp only [Leaf];infer_instance
    · simp only [Leaf];infer_instance
def Valid (c:Cell):Prop:=ylo c≤76 ∧ ylo c≤thi c ∧ Leaf c
instance (c:Cell):Decidable (Valid c):=by unfold Valid;infer_instance
def ordinaryCap (c:Cell):FlagDegree:=cap (thi c) (min (yhi c) (thi c)) (r c)
def ordinaryCost (c:Cell):ℕ:=paddedCost 131072 131073 (ordinaryCap c)
def gridRestCap (c:Cell):FlagDegree:=
  cap (2382-max (tlo c) (ylo c))
    (min (76-ylo c) (2382-max (tlo c) (ylo c)))
    (min (16-r c) (min (76-ylo c) (2382-max (tlo c) (ylo c))))
def gridRestCost (c:Cell):ℕ:=
  if (gridRestCap c).all=0 then 0 else paddedCost 131072 131073 (gridRestCap c)
structure InCell (p:FlagDegree) (c:Cell):Prop where
  all_eq:p.all=r c
  ylo_le:ylo c≤middle p
  middle_le_yhi:middle p≤yhi c
  tlo_le:tlo c≤total p
  total_le_thi:total p≤thi c
  leaf:Leaf c
def coarseCellOf (p:FlagDegree) (hslo:1≤p.all) (hshi:p.all≤16)
    (hy:middle p≤76) (ht:total p≤2382):CoarseCell:=
  (⟨p.all-1,by omega⟩,⟨(middle p-p.all)/4,by omega⟩,
    ⟨total p/128,by omega⟩)
theorem coarseCellOf_bounds (p:FlagDegree) (hslo:1≤p.all) (hshi:p.all≤16)
    (hy:middle p≤76) (ht:total p≤2382):
    p.all=coarseR (coarseCellOf p hslo hshi hy ht) ∧
      coarseYlo (coarseCellOf p hslo hshi hy ht)≤middle p ∧
      middle p≤coarseYhi (coarseCellOf p hslo hshi hy ht) ∧
      coarseTlo (coarseCellOf p hslo hshi hy ht)≤total p ∧
      total p≤coarseThi (coarseCellOf p hslo hshi hy ht):=by
  have hmy:=all_le_middle p
  refine ⟨?_,?_,?_,?_,?_⟩
  · change p.all=p.all-1+1;omega
  · change (p.all-1+1)+4*((middle p-p.all)/4)≤middle p;omega
  · change middle p≤min 76 ((p.all-1+1)+4*((middle p-p.all)/4)+3)
    exact le_min hy (by omega)
  · change 128*(total p/128)≤total p;omega
  · change total p≤min 2382 (128*(total p/128)+127)
    exact le_min ht (by omega)
def fineCellOf (p:FlagDegree) (c:CoarseCell) (hc:HardCoarse c)
    (hylo:coarseYlo c≤middle p) (hyhi:middle p≤coarseYhi c)
    (htlo:coarseTlo c≤total p) (hthi:total p≤coarseThi c):FineCell:=
  ⟨⟨c,hc⟩,⟨middle p-coarseYlo c,by
      have hcap:coarseYhi c≤coarseYlo c+3:=Nat.min_le_right _ _
      omega⟩,
    ⟨(total p-coarseTlo c)/32,by
      have hcap:coarseThi c≤coarseTlo c+127:=Nat.min_le_right _ _
      omega⟩⟩
theorem fineCellOf_bounds (p:FlagDegree) (c:CoarseCell) (hc:HardCoarse c)
    (hylo:coarseYlo c≤middle p) (hyhi:middle p≤coarseYhi c)
    (htlo:coarseTlo c≤total p) (hthi:total p≤coarseThi c)
    (hr:p.all=fineR (fineCellOf p c hc hylo hyhi htlo hthi)):
    p.all=fineR (fineCellOf p c hc hylo hyhi htlo hthi) ∧
      fineY (fineCellOf p c hc hylo hyhi htlo hthi)=middle p ∧
      fineTlo (fineCellOf p c hc hylo hyhi htlo hthi)≤total p ∧
      total p≤fineThi (fineCellOf p c hc hylo hyhi htlo hthi):=by
  refine ⟨hr,?_,?_,?_⟩
  · simp only [fineY,fineCellOf];omega
  · simp only [fineTlo,fineCellOf];omega
  · simp only [fineThi,fineTlo,fineCellOf];omega
def unitCellOf (p:FlagDegree) (c:FineCell) (hc:HardFine c)
    (htlo:fineTlo c≤total p) (hthi:total p≤fineThi c):UnitCell:=
  ⟨⟨c,hc⟩,⟨total p-fineTlo c,by simp only [fineThi] at hthi;omega⟩⟩
theorem unitCellOf_bounds (p:FlagDegree) (c:FineCell) (hc:HardFine c)
    (htlo:fineTlo c≤total p) (hthi:total p≤fineThi c):
    unitT (unitCellOf p c hc htlo hthi)=total p:=by
  simp only [unitT,unitCellOf];omega
def cellOf (p:FlagDegree) (hslo:1≤p.all) (hshi:p.all≤16)
    (hy:middle p≤76) (ht:total p≤2382):Cell:=
  let c:=coarseCellOf p hslo hshi hy ht
  if hc:HardCoarse c then
    let hb:=coarseCellOf_bounds p hslo hshi hy ht
    let f:=fineCellOf p c hc hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2
    if hf:HardFine f then
      let hfb:=fineCellOf_bounds p c hc hb.2.1 hb.2.2.1 hb.2.2.2.1
        hb.2.2.2.2 hb.1
      .inr (.inr (unitCellOf p f hf hfb.2.2.1 hfb.2.2.2))
    else .inr (.inl f)
  else .inl c
theorem cellOf_bounds (p:FlagDegree) (hslo:1≤p.all) (hshi:p.all≤16)
    (hy:middle p≤76) (ht:total p≤2382):
    InCell p (cellOf p hslo hshi hy ht):=by
  let c:=coarseCellOf p hslo hshi hy ht
  have hb:=coarseCellOf_bounds p hslo hshi hy ht
  by_cases hc:HardCoarse c
  · let f:=fineCellOf p c hc hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2
    have hfb:=fineCellOf_bounds p c hc hb.2.1 hb.2.2.1 hb.2.2.2.1
      hb.2.2.2.2 hb.1
    by_cases hf:HardFine f
    · have hu:=unitCellOf_bounds p f hf hfb.2.2.1 hfb.2.2.2
      simp only [cellOf,c,hc,dite_true,f,hf]
      exact ⟨by change p.all=fineR f;exact hfb.1,
        by change fineY f≤middle p;exact hfb.2.1.le,
        by change middle p≤fineY f;exact hfb.2.1.symm.le,
        by simpa [tlo] using hu.le,by simpa [thi] using hu.ge,trivial⟩
    · simp only [cellOf,c,hc,dite_true,f,hf]
      exact ⟨by change p.all=fineR f;exact hfb.1,
        by change fineY f≤middle p;exact hfb.2.1.le,
        by change middle p≤fineY f;exact hfb.2.1.symm.le,
        by change fineTlo f≤total p;exact hfb.2.2.1,
        by change total p≤fineThi f;exact hfb.2.2.2,
        by change ¬HardFine f;exact hf⟩
  · simp only [cellOf,c,hc,dite_false]
    exact ⟨by simpa [r] using hb.1,by simpa [ylo] using hb.2.1,
      by simpa [yhi] using hb.2.2.1,by simpa [tlo] using hb.2.2.2.1,
      by simpa [thi] using hb.2.2.2.2,by simpa [Leaf]⟩
theorem ylo_le_thi_of_inCell (p:FlagDegree) (c:Cell) (h:InCell p c):
    ylo c≤thi c:=(h.ylo_le.trans (middle_le_total p)).trans h.total_le_thi
theorem valid_of_inCell (p:FlagDegree) (c:Cell) (h:InCell p c):Valid c:=by
  have hyhi:yhi c≤76:=yhi_le_76 c
  exact ⟨(h.ylo_le.trans h.middle_le_yhi).trans hyhi,
    ylo_le_thi_of_inCell p c h,h.leaf⟩
theorem ordinaryCap_cumulative (c:Cell) (h:Valid c):
    (ordinaryCap c).all=r c ∧ middle (ordinaryCap c)=min (yhi c) (thi c) ∧
      total (ordinaryCap c)=thi c:=by
  have hry:r c≤ylo c:=by
    rcases c with c|c
    · change coarseR c≤coarseYlo c
      dsimp [coarseYlo]
      omega
    · rcases c with c|c
      · have hp:=c.parent.2
        change fineR c≤fineY c
        simp only [fineR,fineY]
        rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> omega
      · exact c.parent.2.elim
  have hryhi:r c≤yhi c:=by
    rcases c with c|c
    · change coarseR c≤coarseYhi c
      have hry':coarseR c≤coarseYlo c:=by simpa only [r,ylo] using hry
      have hv:coarseYlo c≤76:=by simpa only [Valid,ylo] using h.1
      exact le_min (hry'.trans hv) (by omega)
    · rcases c with c|c
      · change fineR c≤fineY c
        simpa only [r,ylo] using hry
      · change unitR c≤unitY c
        simpa only [r,ylo] using hry
  exact cap_cumulative _ _ _ (le_min hryhi (hry.trans h.2.1))
    (Nat.min_le_right _ _)
theorem below_ordinaryCap (p:FlagDegree) (c:Cell) (h:InCell p c):
    Below p (ordinaryCap c):=by
  have hc:=ordinaryCap_cumulative c (valid_of_inCell p c h)
  unfold Below
  rw [hc.1,hc.2.1,hc.2.2]
  exact ⟨h.all_eq.le,le_min h.middle_le_yhi
    ((middle_le_total p).trans h.total_le_thi),h.total_le_thi⟩
theorem paddedCost_le_ordinaryCost (p:FlagDegree) (c:Cell) (h:InCell p c):
    paddedCost 131072 131073 p≤ordinaryCost c:=
  paddedCost_mono 131072 131073 (below_ordinaryCap p c h)
theorem count_le_ordinaryCost (p:FlagDegree) (c:Cell) (count:ℕ)
    (h:InCell p c) (hstage:count≤paddedCost 131072 131073 p):
    count≤ordinaryCost c:=hstage.trans (paddedCost_le_ordinaryCost p c h)
theorem gridRestCap_cumulative (c:Cell):
    (gridRestCap c).all=
        min (16-r c) (min (76-ylo c) (2382-max (tlo c) (ylo c))) ∧
      middle (gridRestCap c)=min (76-ylo c) (2382-max (tlo c) (ylo c)) ∧
      total (gridRestCap c)=2382-max (tlo c) (ylo c):=
  cap_cumulative _ _ _ (Nat.min_le_right _ _) (Nat.min_le_right _ _)
theorem remainingCap_below_gridRestCap (p:FlagDegree) (c:Cell) (h:InCell p c):
    Below (remainingCap 2382 76 16 p) (gridRestCap c):=by
  have heq:=h.all_eq
  have hylo:=h.ylo_le
  have htlo:=h.tlo_le
  have hr:16-p.all≤16-r c:=by omega
  have hy:76-middle p≤76-ylo c:=by omega
  have htmax:max (tlo c) (ylo c)≤total p:=
    max_le htlo (hylo.trans (middle_le_total p))
  have ht:2382-total p≤2382-max (tlo c) (ylo c):=by omega
  have hp:=remainingCap_cumulative 2382 76 16 p
  have hg:=gridRestCap_cumulative c
  unfold Below
  rw [hp.1,hp.2.1,hp.2.2,hg.1,hg.2.1,hg.2.2]
  exact ⟨min_le_min hr (min_le_min hy ht),min_le_min hy ht,ht⟩
theorem remainingCost_le_gridRestCost (p:FlagDegree) (c:Cell) (h:InCell p c):
    remainingCost 2382 76 16 131072 131073 p≤gridRestCost c:=by
  have hb:=remainingCap_below_gridRestCap p c h
  by_cases hg:(gridRestCap c).all=0
  · have hs:=hb.1
    have hp:(remainingCap 2382 76 16 p).all=0:=by omega
    rw [remainingCost,gridRestCost,if_pos hp,if_pos hg]
  · by_cases hp:(remainingCap 2382 76 16 p).all=0
    · rw [remainingCost,if_pos hp];exact Nat.zero_le _
    · rw [remainingCost,gridRestCost,if_neg hp,if_neg hg]
      exact paddedCost_mono 131072 131073 hb
theorem cellCost_le_of_grid_bound {bound:ℕ} (p:FlagDegree) (c:Cell) (q:ℕ)
    (h:InCell p c) (hq:q+gridRestCost c≤bound):
    cellCost 2382 76 16 131072 131073 p q≤bound:=by
  calc
    _=min (paddedCost 131072 131073 p) q+
        remainingCost 2382 76 16 131072 131073 p:=rfl
    _≤q+gridRestCost c:=Nat.add_le_add (Nat.min_le_right _ _)
      (remainingCost_le_gridRestCost p c h)
    _≤bound:=hq
end ProximityPrize.SubmissionLower.LocatorReplacementGrid
