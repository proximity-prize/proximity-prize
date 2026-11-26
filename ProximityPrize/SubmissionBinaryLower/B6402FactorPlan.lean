import ProximityPrize.SubmissionBinaryLower.B6402HardFactor

namespace ProximityPrize.SubmissionBinaryLower.B6402FactorPlan
open B6402HardFactor
open Polynomial ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open B6401Params hiding A
open B6402HybridP64 (A linePow BadOn6402)
open B6401ContactKerD B6401QuotInterp B6401ResLineOrd B6402MixedDegree
open B6402Table4Common B6402GridProfile B6402GridRouting B6402PricedCell B6402BucketBudget
open B6402SelectedPlan B6402HardAuxiliary B6402OrderProfile B6402ResidualGap
open B6401FactorBound (G_val)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000
local notation "K" => BinaryIRSProfile.Field
local notation "I" => BinaryIRSProfile.Index

private theorem bad_subset {L : Type} [Field L] [CharP L 2] {J : Type*} [Fintype J] [DecidableEq J]
    (k : J → ℕ) (x : J ↪ L) (F : ContactPoly (Polynomial L)) :
    exceptional k x F ⊆ marked k := Finset.filter_subset _ _

private theorem bad_value {L : Type} [Field L] [CharP L 2] {J : Type*} [Fintype J] [DecidableEq J]
    (k : J → ℕ) (x : J ↪ L) (F : ContactPoly (Polynomial L)) (i : J) (hi : i∈exceptional k x F) :
    P64LineOrder.evalXAt (F.coeff 1) (x i)=0 := (Finset.mem_filter.mp hi).2

theorem select {u₀ u₁ : I → K} {q : ℕ} (hq : q=1 ∨ q=2) (f : Model u₀ u₁ q)
    (D : KerD45Data) (wD : D.W_F=f.WF) (kD : D.k=f.k) (key : Key) (route : Feasible D key)
    (cl : lo key≤(f.WF:ℚ)/wY) (ch : (f.WF:ℚ)/wY≤hi key) (endc : hi key≤28/5)
    (den : 0<key.gap.2.2.2) (rep : Replacement key q)
    : ∃ p : Prepared,
      let H := mixed q f.F
      let T := p.plan.cap-p.plan.s*H
      let good := regular f.k BinaryIRSProfile.domain f.F
      let bad := exceptional f.k BinaryIRSProfile.domain f.F
      Applies p q f.WF H good.card bad.card (count f.k 2) (gapHi key) ∧
      Binary6402NativeCaps.allowance (p.plan.m-p.plan.b) p.side.ordinate p.side.spatial p.side.delta q p.plan.cap (budget key q) p.w=true ∧
      (∑ i,(B6402ProfileCosts.fee (primaryOrder p.plan.m p.plan.b (f.k i)) p.plan.s q T H (f.k i)))+
        (good.card:ℤ)*(B6402InterpolationPrice.regularCost p.plan.J p.plan.s p.plan.m p.plan.b*(T+p.plan.s*H+1):ℕ)+
        (bad.card:ℤ)*(B6402InterpolationPrice.exceptionalCost p.plan.s p.plan.b*(T+1+(p.plan.J+16*p.plan.b+2)*H):ℕ) <
        B6402DimensionBudget.sourceSize wY p.plan.W p.plan.s q T -
          B6402DimensionBudget.sourceSize wY (p.plan.W-f.WF) (p.plan.s-1) q (T-H) := by
  classical
  let H := mixed q f.F
  let axis := BinaryIRSProfile.domain
  let good := regular f.k axis f.F
  let bad := exceptional f.k axis f.F
  let v : ℚ := bad.card/N
  have sub : bad⊆marked f.k := bad_subset f.k axis f.F
  have Hlo : 5*q≤H := quartic_lower q f.F f.quartic
  have Hhi : H≤1811+q := (at_most_input q f.F).trans (by rw [f.slope,mul_one]; exact Nat.add_le_add_right f.qz q)
  have hN : Fintype.card I=N := by rw [BinaryIRSProfile.card_index]; rfl
  have nr : (marked f.k).card≤N := hN ▸ Finset.card_le_univ _
  have wl := f.lower
  have vroot := B6402QuarticProfile.quartic_sites wY f.WF (by decide) axis f.F f.fw.le f.quartic bad
     (bad_value f.k axis f.F)
  have vlim := B6402QuarticProfile.normalized (N:=N) (w:=wY) (WF:=f.WF) (by decide) (by decide) (Finset.card_le_card sub) vroot
  obtain ⟨hn,x,nn,a0,a1,a2,a3,at',ac,ub,eq⟩ := route
  have ds := B6402ProfileMatch.counts D
  rw [ds.1,kD] at a0
  rw [ds.2.1,kD] at a1
  rw [ds.2.2.1,kD] at a2
  rw [ds.2.2.2.1,kD] at a3
  rw [ds.2.2.2.2,kD] at at'
  rw [wD] at ac
  have nc := order_two_card f.k
  have pv : v≤x ⟨2,by omega⟩ := by rw [a2,←nc]; exact vlim.1
  have vd : 2097152*v≤(x ⟨arity key.branch-1,by omega⟩-5)*1048575+1 := by rw [ac]; exact vlim.2
  have mx : x ⟨2,by omega⟩≤1 := by
    rw [a2,←nc,div_le_one (by decide : (0:ℚ)<N)]
    exact_mod_cast nr
  obtain ⟨p,box,inside,ok,funds⟩ := rep hn.le x v nn (by dsimp [v]; positivity) mx (ac ▸ cl) (ac ▸ ch) endc pv vd ub eq
  have parts : good.card+bad.card=count f.k 2 := (partition f.k axis f.F).trans nc
  obtain ⟨a,cap,pay⟩ := admissible hn.le x v f.k f.WF H q good.card bad.card _ _ box p ok funds inside a0 a1 a2 a3 at' ac rfl parts Hlo Hhi
  exact ⟨p,a,cap,pay⟩

#print axioms select
end ProximityPrize.SubmissionBinaryLower.B6402FactorPlan
