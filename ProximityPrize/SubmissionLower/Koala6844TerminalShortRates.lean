import ProximityPrize.SubmissionLower.Koala6844TerminalRates


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open RCN095 RCN146 LocatorHybridCells Koala6844Receipts

set_option autoImplicit false
set_option maxRecDepth 14000
set_option maxHeartbeats 3000000

private theorem identity_axis (g : Flag) (hr : 3 ≤ g.r) (hy : g.r+2 ≤ g.y) (ht : g.y ≤ g.t)
    (j : Fin 3) :
    (nodes-degree)*pencilLimit*(rawIdentity g).axis j.val ≤ agreementGap*(rawRatesAt g).axis j.val := by
  let f := geometryFlag (axisFlag j.val)
  have hb : 1 ≤ cellB g.y g.r := by unfold cellB; omega
  have hs : 1 ≤ cellS g.r := by unfold cellS; omega
  have h := rawIdentityAbsorption f (cellA g.t g.y) (cellB g.y g.r) (cellS g.r) (by omega) hb hs
  rw [← MovingFiberOrdinaryHigh6815.bound_eq_abs f g.t g.y g.r hr hy,
    ← rawRates_eq_bound g hr hy ht] at h
  change 131073 * 81188 * identityCurveDegree f (cellA g.t g.y) (cellB g.y g.r) (cellS g.r)
    Lower80788.HybridIdentityC2.w ≤ _ at h
  rw [Lower80788.HybridIdentityC2.identityDegree_linear] at h
  have h0 : nodes-degree = 131073 := rfl
  have h1 : pencilLimit = 81188 := rfl
  have h2 : agreementGap = 49886 := rfl
  fin_cases j <;>
    simpa only [f,rawIdentity,axisFlag,geometryFlag,increments,FlagIncrements.axis,dot,
      Fin.val_zero,Fin.val_one,show (2 : Fin 3).val = 2 from rfl,Nat.reduceEqDiff,ite_true,ite_false,
      cellA,cellB,cellS,Nat.sub_sub,h0,h1,h2,mul_one,one_mul,mul_zero,zero_mul,add_zero,zero_add] using h

theorem short_rates_raw (f : Flag)
    (hpos : 1 ≤ f.r) (hry : f.r ≤ f.y) (hyt : f.y ≤ f.t)
    (hR : f.r ≤ 20) (hY : f.y ≤ 84) (hT : f.t ≤ 3873) :
    let g := padFlag f
    GraphGates g.t g.y g.r ∧ shortRates f = ⟨rawRatesAt g,1⟩ := by
  dsimp only
  let g := padFlag f
  have hr : 3 ≤ g.r := Nat.le_max_left _ _
  have hy : g.r+2 ≤ g.y := Nat.le_max_right _ _
  have ht : g.y ≤ g.t := by exact Nat.le_max_right _ _
  have hR' : g.r ≤ 20 := max_le (by decide) hR
  have hY' : g.y ≤ 84 := max_le hY (by omega)
  have hT' : g.t ≤ 3873 := max_le hT (by omega)
  have hearly : g.r * (earlyCut g).middle + g.y * (earlyCut g).slope < prime := by
    have hm : (earlyCut g).middle ≤ 1 + 262144*81 := by
      simp only [earlyCut,show degree = 131071 from rfl,Nat.reduceAdd,Nat.reduceMul]
      omega
    have hs : (earlyCut g).slope ≤ 262144*19 := by
      simp only [earlyCut,show degree = 131071 from rfl,Nat.reduceAdd,Nat.reduceMul]
      omega
    exact (Nat.add_le_add (Nat.mul_le_mul hR' hm) (Nat.mul_le_mul hY' hs)).trans_lt (by decide)
  have hsharp : g.r * ((2*(g.y-g.r)-1)*degree+1) + g.y * (2*g.r-1)*degree < prime := by
    have hm : (2*(g.y-g.r)-1)*degree+1 ≤ 161*131071+1 := by
      rw [show degree = 131071 from rfl]
      omega
    have hs : 2*g.r-1 ≤ 39 := by omega
    exact (Nat.add_le_add (Nat.mul_le_mul hR' hm)
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul hY' hs))).trans_lt (by decide)
  have hmoving : 2*g.t*(g.t+1) < prime :=
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hT') (Nat.succ_le_succ hT')).trans_lt (by decide)
  have hn : pencilLimit ≤ (normalCut g).middle := by
    simp only [normalCut,show degree = 131071 from rfl,show pencilLimit = 81188 from rfl,Nat.reduceAdd]
    omega
  have hgraph : goodGraph g = true := decide_eq_true ⟨by omega,hmoving,hearly,hsharp,hn⟩
  have hraw : rawGeometryGate f = true := by
    unfold rawGeometryGate wellOrdered
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true ⟨hpos,hry,hyt⟩,decide_eq_true ⟨hmoving,hearly,hn,hsharp⟩⟩
  have hidentity : (rawIdentity g).all (fun i cost =>
      decide ((nodes-degree)*pencilLimit*cost ≤ agreementGap*(rawRatesAt g).axis i)) = true := by
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true (identity_axis g hr hy ht 0),
        decide_eq_true (identity_axis g hr hy ht 1)⟩,decide_eq_true (identity_axis g hr hy ht 2)⟩
  refine ⟨graphGates_of_goodGraph g hr hy hgraph,?_⟩
  have he : rawGeometryRates f = some (rawRatesAt g) := by
    unfold rawGeometryRates
    change (if rawGeometryGate f && (rawIdentity g).all (fun i cost =>
        decide ((nodes-degree)*pencilLimit*cost ≤ agreementGap*(rawRatesAt g).axis i)) then
          some (rawRatesAt g) else none) = _
    rw [hraw, hidentity]
    rfl
  rw [shortRates,he]

theorem short_factor_payment (f : Flag)
    (hpos : 1≤f.r) (hry : f.r≤f.y) (hyt : f.y≤f.t)
    (hR : f.r≤20) (hY : f.y≤84) (hT : f.t≤3873)
    (left : FlagDegree) (n : Nat)
    (h : n ≤ MovingFiberOrdinaryHigh6815.bound left (padFlag f).t (padFlag f).y (padFlag f).r) :
    (shortRates f).denominator * n ≤ dot (increments left) (shortRates f).numerator := by
  rw [(short_rates_raw f hpos hry hyt hR hY hT).2]
  rw [show (Rates.mk (rawRatesAt (padFlag f)) 1).denominator * n = n by simp]
  have ht : (padFlag f).y ≤ (padFlag f).t := by exact Nat.le_max_right _ _
  exact (rawRates_eq_bound (padFlag f) (Nat.le_max_left _ _) (Nat.le_max_right _ _) ht left).symm ▸ h

end ProximityPrize.SubmissionLower.Koala6844Terminal
