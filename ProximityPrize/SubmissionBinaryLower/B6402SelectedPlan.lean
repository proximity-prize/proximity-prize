import ProximityPrize.SubmissionBinaryLower.B6402PricedCell
import ProximityPrize.SubmissionBinaryLower.B6402EndpointSound
import ProximityPrize.SubmissionBinaryLower.B6402GridRouting
import ProximityPrize.SubmissionBinaryLower.B6402HardBin

namespace ProximityPrize.SubmissionBinaryLower.B6402SelectedPlan
open B6401Params hiding A
open B6402HybridP64 (A)
open B6402PricedCell B6402CellBounds B6402EndpointBudget B6402OrderProfile B6402ProfileCosts
open B6402HardAuxiliary B6402DimensionBudget B6402InterpolationPrice B6402RectCover
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem order_two_card {I : Type*} [Fintype I] (k : I → ℕ) : (marked k).card=count k 2 := by
  classical
  unfold marked count; congr 1
  apply Finset.filter_congr; intro i _; omega

theorem partition {K : Type} {I : Type*} [Field K] [Fintype I] (k : I → ℕ) (x : I ↪ K)
    (F : B6401ContactKerD.ContactPoly (Polynomial K)) :
    (regular k x F).card+(exceptional k x F).card=(marked k).card := by
  classical
  unfold regular exceptional
  simpa only [not_ne_iff] using Finset.card_filter_add_card_filter_not (s:=marked k) (p:=fun i => P64LineOrder.evalXAt (F.coeff 1) (x i)≠0)

structure Applies (p : Prepared) (q WF H nr nb n2 : ℕ) (gapHi : ℚ) : Prop where
  exponent : p.plan.q=q
  positive_slope : 1≤p.plan.s
  multiplicity : p.plan.b≤p.plan.m
  ordinate : 2≤p.plan.J
  layers : 2*p.plan.m≤p.plan.J+p.plan.s
  degree : p.plan.W/(wY-1)≤p.plan.J
  height : H≤p.plan.cap-p.plan.s*H
  total : p.plan.cap-p.plan.s*H+p.plan.s*H=p.plan.cap
  globalCap : q*(p.plan.W/(wY-1))≤p.plan.cap-p.plan.s*H-H+1
  localCap : q*(p.plan.s+2*p.plan.m)≤p.plan.cap-p.plan.s*H-H+1
  load : p.plan.W<2*((p.plan.m-p.plan.b)*A+p.plan.b*n2)
  weight : p.plan.W+p.plan.s*(WF-(wY-1))≤p.side.spatial+2*p.plan.b*nr
  ydegree : p.side.spatial/wY≤p.side.ordinate
  gap : p.side.gap0+2*p.plan.b*nb≤p.side.delta
  gapLt : (p.plan.s:ℚ)*gapHi*N<(p.side.gap0:ℚ)+1
  scalar : p.plan.J+4*p.plan.s≤51897

theorem admissible {I : Type*} [Fintype I] {n : ℕ} (h5 : 5≤n) (x : Fin n → ℚ) (v : ℚ) (k : I → ℕ)
    (WF H q nr nb price : ℕ) (gapHi : ℚ) (box : Box) (p : Prepared)
    (valid : numerical p box q price gapHi=true) (fund : Funds h5 x v p)
    (inside : Contains box (x ⟨2,by omega⟩) (x ⟨n-1,by omega⟩) v)
    (h0 : x ⟨0,by omega⟩=(count k 0:ℚ)/N) (h1 : x ⟨1,by omega⟩=(count k 1:ℚ)/N)
    (h2 : x ⟨2,by omega⟩=(count k 2:ℚ)/N) (h3 : x ⟨3,by omega⟩=(count k 3:ℚ)/N)
    (hx : x ⟨4,by omega⟩=(totalExcess k:ℚ)/N) (hc : x ⟨n-1,by omega⟩=(WF:ℚ)/wY)
    (hv : v=(nb:ℚ)/N) (split : nr+nb=count k 2)
    (lh : 5*q≤H) (rh : H≤1811+q) :
    Applies p q WF H nr nb (count k 2) gapHi ∧
    Binary6402NativeCaps.allowance (p.plan.m-p.plan.b) p.side.ordinate p.side.spatial p.side.delta q p.plan.cap price p.w=true ∧
    let T:=p.plan.cap-p.plan.s*H
    (∑ i,fee (primaryOrder p.plan.m p.plan.b (k i)) p.plan.s q T H (k i))+
     (nr:ℤ)*(regularCost p.plan.J p.plan.s p.plan.m p.plan.b*(T+p.plan.s*H+1):ℕ)+
     (nb:ℤ)*(exceptionalCost p.plan.s p.plan.b*(T+1+(p.plan.J+16*p.plan.b+2)*H):ℕ) <
         sourceSize wY p.plan.W p.plan.s q T-sourceSize wY (p.plan.W-WF) (p.plan.s-1) q (T-H) := by
  classical
  simp only [numerical,Bool.and_eq_true,decide_eq_true_eq] at valid
  obtain ⟨⟨ok,cap⟩,eq,cl,ch,strict,loR,hiR,cR,gR,wR,_⟩ := valid
  rcases fund with ⟨lower,upper,hfund⟩
  rw [h2] at lower; rw [hv] at upper
  have cLow := inside.2.1.1
  have cHi := inside.2.1.2
  rw [←cl,hc] at cLow
  rw [←ch,hc] at cHi
  have ⟨hlo,hhi,hw⟩ := round_profile p.low p.high p.plan.hi (count k 2) p.side.least nb p.side.mostBad WF
    lower upper cHi loR hiR p.plan.WFhi cR
  have hh : H≤1811+p.plan.q := eq.symm ▸ rh
  have checks := from_cell p.plan p.side ok (count k 2) nr nb WF H hlo hhi split hw hh
  dsimp only at checks
  obtain ⟨s1,bm,j2,mj,wj,load,weight,yo,gap,ht,tt,cg,cc,scalar⟩ := checks
  refine ⟨⟨eq,s1,bm,j2,mj,wj,ht,tt,eq ▸ cg,eq ▸ cc,load,weight,yo,gap,gR,scalar⟩,cap,?_⟩
  have hpaid := hfund H (by rw [eq]; exact_mod_cast lh) (by rw [eq]; exact_mod_cast rh)
  rw [h0,h1,h2,h3,hx,hc,hv] at hpaid
  have hm : 0<p.plan.m := by
    simp only [B6402CellBounds.valid,decide_eq_true_eq] at ok
    exact Nat.zero_lt_of_lt ok.2.1
  have cw : ((WF:ℚ)/wY)*wY≤WF := by rw [div_mul_cancel₀ _ (by decide : (wY:ℚ)≠0)]
  have use := B6402EndpointSound.paid p.plan k WF H _ nr nb hm tt ht (hw.trans wR) hw split _ cw cLow cHi strict hpaid
  exact eq ▸ use

#print axioms admissible
end ProximityPrize.SubmissionBinaryLower.B6402SelectedPlan
