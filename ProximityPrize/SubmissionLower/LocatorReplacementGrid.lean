import ProximityPrize.SubmissionLower.LocatorFactorReplacement
namespace ProximityPrize.SubmissionLower.LocatorReplacementGrid
open RCN095 LocatorFactorAggregate LocatorFactorReplacement
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev Cell:=Fin 17 × Fin 79 × Fin 160
def r (c:Cell):ℕ:=c.1.val+1
def y (c:Cell):ℕ:=c.2.1.val
def bin (c:Cell):ℕ:=c.2.2.val
def tlo (c:Cell):ℕ:=max (y c) (16*bin c)
def thi (c:Cell):ℕ:=min 2556 (16*bin c+15)
def Valid (c:Cell):Prop:=r c≤y c ∧ tlo c≤thi c
instance (c:Cell):Decidable (Valid c):=by unfold Valid;infer_instance

structure InCell (p:FlagDegree) (c:Cell):Prop where
  all_eq:p.all=r c
  middle_eq:middle p=y c
  tlo_le:tlo c≤total p
  total_le_thi:total p≤thi c

def cellOf (p:FlagDegree) (hslo:1≤p.all) (hshi:p.all≤17)
    (hy:middle p≤78) (ht:total p≤2556):Cell:=
  (⟨p.all-1,by omega⟩,⟨middle p,by omega⟩,⟨total p/16,by omega⟩)

theorem cellOf_values (p:FlagDegree) (hslo:1≤p.all) (hshi:p.all≤17)
    (hy:middle p≤78) (ht:total p≤2556):
    r (cellOf p hslo hshi hy ht)=p.all ∧
      y (cellOf p hslo hshi hy ht)=middle p ∧
      tlo (cellOf p hslo hshi hy ht)≤total p ∧
      total p≤thi (cellOf p hslo hshi hy ht):=by
  have hyt:middle p≤total p:=middle_le_total p
  simp only [cellOf,r,y,tlo,thi,bin]
  constructor
  · omega
  constructor
  · trivial
  constructor
  · exact max_le hyt (by omega)
  · exact le_min ht (by omega)

theorem cellOf_valid (p:FlagDegree) (hslo:1≤p.all) (hshi:p.all≤17)
    (hy:middle p≤78) (ht:total p≤2556):
    Valid (cellOf p hslo hshi hy ht):=by
  have hv:=cellOf_values p hslo hshi hy ht
  exact ⟨by rw [hv.1,hv.2.1];exact all_le_middle p,
    hv.2.2.1.trans hv.2.2.2⟩

theorem cellOf_bounds (p:FlagDegree) (hslo:1≤p.all) (hshi:p.all≤17)
    (hy:middle p≤78) (ht:total p≤2556):
    InCell p (cellOf p hslo hshi hy ht):=by
  have hv:=cellOf_values p hslo hshi hy ht
  exact ⟨hv.1.symm,hv.2.1.symm,hv.2.2.1,hv.2.2.2⟩

theorem below_cell_cap (p:FlagDegree) (c:Cell) (h:InCell p c):
    Below p (cap (thi c) (y c) (r c)):=by
  apply below_cap_of_bounds
  · rw [←h.all_eq,←h.middle_eq]
    exact all_le_middle p
  · rw [←h.middle_eq]
    exact (middle_le_total p).trans h.total_le_thi
  · exact h.all_eq.le
  · exact h.middle_eq.le
  · exact h.total_le_thi

theorem remainingCap_below_cellRest (p:FlagDegree) (c:Cell) (h:InCell p c):
    Below (remainingCap 2556 78 17 p)
      (remainingCap 2556 78 17 (cap (tlo c) (y c) (r c))):=by
  have hp:=remainingCap_cumulative 2556 78 17 p
  have hc:=remainingCap_cumulative 2556 78 17 (cap (tlo c) (y c) (r c))
  have hcap:=cap_cumulative (tlo c) (y c) (r c)
    (by rw [←h.all_eq,←h.middle_eq];exact all_le_middle p)
    (le_max_left _ _)
  have ht:2556-total p≤2556-tlo c:=
    Nat.sub_le_sub_left h.tlo_le 2556
  unfold Below
  rw [hp.1,hp.2.1,hp.2.2,hc.1,hc.2.1,hc.2.2,
    hcap.1,hcap.2.1,hcap.2.2,h.all_eq,h.middle_eq]
  exact ⟨min_le_min le_rfl (min_le_min le_rfl ht),min_le_min le_rfl ht,ht⟩

theorem remainingCost_le_cellRest (p:FlagDegree) (c:Cell) (h:InCell p c):
    remainingCost 2556 78 17 131072 131073 p≤
      remainingCost 2556 78 17 131072 131073
        (cap (tlo c) (y c) (r c)):=by
  have hb:=remainingCap_below_cellRest p c h
  by_cases hc:(remainingCap 2556 78 17 (cap (tlo c) (y c) (r c))).all=0
  · have hs:=hb.1
    have hp:(remainingCap 2556 78 17 p).all=0:=by omega
    rw [remainingCost,if_pos hp,remainingCost,if_pos hc]
  · by_cases hp:(remainingCap 2556 78 17 p).all=0
    · rw [remainingCost,if_pos hp]
      exact Nat.zero_le _
    · rw [remainingCost,if_neg hp,remainingCost,if_neg hc]
      exact paddedCost_mono 131072 131073 hb

theorem cellCost_le_of_cell_bound {bound:ℕ} (p:FlagDegree) (c:Cell) (q:ℕ)
    (h:InCell p c)
    (hq:q+remainingCost 2556 78 17 131072 131073
      (cap (tlo c) (y c) (r c))≤bound):
    cellCost 2556 78 17 131072 131073 p q≤bound:=by
  calc
    _≤q+remainingCost 2556 78 17 131072 131073 p:=
      Nat.add_le_add (Nat.min_le_right _ _) le_rfl
    _≤q+remainingCost 2556 78 17 131072 131073
        (cap (tlo c) (y c) (r c)):=
      Nat.add_le_add_left (remainingCost_le_cellRest p c h) q
    _≤bound:=hq

end ProximityPrize.SubmissionLower.LocatorReplacementGrid
