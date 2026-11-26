import ProximityPrize.SubmissionBinaryLower.B6402ProfileMatch
import ProximityPrize.SubmissionBinaryLower.B6402HardBin
import ProximityPrize.SubmissionBinaryLower.Binary6402QuotBridge

namespace ProximityPrize.SubmissionBinaryLower.B6402HardFactor
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

structure Model (u₀ u₁ : I → K) (q : ℕ) where
  WF : ℕ
  fc : KerDIdx wY WF 1 → K[X]
  F : ContactPoly (Polynomial K)
  eq : F=∑ e,cC (fc e)*kerDBasisPoly e.1
  fw : wdeg wY F=WF
  qz : wYZ q F≤1811
  slope : F.natDegree=1
  invariant : contactDeriv F=0
  irreducible : Irreducible F
  lifted : Irreducible (liftCRat F)
  degree : ∀ j,(F.coeff j).natDegree≤5
  quartic : (F.coeff 1).natDegree=4
  lower : wY-1≤WF
  k : I → ℕ
  ord : ∀ i,twOrdGE (B6402PrimarySystem.localized (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) fc) (k i)
  exactOrd : ∀ i,∃ a b,a+b=k i ∧ twCoeff (B6402PrimarySystem.localized (BinaryIRSProfile.domain i) (linePow u₀ u₁ q i) fc) a b≠0

def Upper (key : Key) (WF : ℕ) (k : I → ℕ) (S : Finset I) : Prop :=
  key.gap.2.2.1<key.gap.2.2.2 → (G_val WF k S:ℚ)≤gapHi key*N

private theorem bad_subset {L : Type} [Field L] [CharP L 2] {J : Type*} [Fintype J] [DecidableEq J]
    (k : J → ℕ) (x : J ↪ L) (F : ContactPoly (Polynomial L)) :
    exceptional k x F ⊆ marked k := Finset.filter_subset _ _

private theorem bad_value {L : Type} [Field L] [CharP L 2] {J : Type*} [Fintype J] [DecidableEq J]
    (k : J → ℕ) (x : J ↪ L) (F : ContactPoly (Polynomial L)) (i : J) (hi : i∈exceptional k x F) :
    P64LineOrder.evalXAt (F.coeff 1) (x i)=0 := (Finset.mem_filter.mp hi).2

theorem replacement {u₀ u₁ : I → K} {q : ℕ} (hq : q=1 ∨ q=2) (f : Model u₀ u₁ q)
    (D : KerD45Data) (wD : D.W_F=f.WF) (kD : D.k=f.k) (key : Key) (route : Feasible D key)
    (cl : lo key≤(f.WF:ℚ)/wY) (ch : (f.WF:ℚ)/wY≤hi key) (endc : hi key≤28/5)
    (den : 0<key.gap.2.2.2) (rep : Replacement key q)
    (S : Finset K) (P : K → K[X]) (Az : K → Finset I)
    (hP : ∀ z∈S,(P z).natDegree≤wY) (hA : ∀ z∈S,A≤(Az z).card)
    (matchP : ∀ z∈S,∀ i,i∈Az z ↔ (P z).eval (BinaryIRSProfile.domain i)=u₀ i+z^q*u₁ i)
    (onF : ∀ z∈S,evalContact (evalZContact f.F z) (P z)=0) (badP : ∀ z∈S,BadOn6402 u₀ u₁ (Az z))
    (gap : ∀ z∈S,Upper key f.WF f.k (Az z)) :
    S.card≤budget key q+N*1813 := by
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
  let T:=p.plan.cap-p.plan.s*H
  have gu : gapHi key<1 := by
    simp only [numerical,Bool.and_eq_true,decide_eq_true_eq] at ok
    obtain ⟨⟨_,_⟩,_,_,_,_,_,_,_,_,_,g⟩ := ok
    exact g
  have ng : key.gap.2.2.1<key.gap.2.2.2 := by
    unfold gapHi at gu
    have hden : (0:ℚ)<key.gap.2.2.2 := by exact_mod_cast den
    have h' := (div_lt_one hden).mp gu
    exact_mod_cast h'
  have gbound z (hz : z∈S) : (p.plan.s:ℤ)*((f.WF:ℤ)-(wY-1:ℕ)-(∑ i∈Az z,charge (f.k i)))≤p.side.gap0 := by
    rw [B6402ProfileMatch.charge_gap]
    have h := mul_le_mul_of_nonneg_left (gap z hz ng) (Nat.cast_nonneg (α:=ℚ) p.plan.s)
    have h2 := a.gapLt
    rw [mul_assoc] at h2
    have h3 := h.trans_lt h2
    have h4 : (p.plan.s:ℤ)*G_val f.WF f.k (Az z)<(p.side.gap0:ℤ)+1 := by exact_mod_cast h3
    omega
  have bound := B6402HardBin.labels u₀ u₁ hq a.positive_slope a.height a.degree a.ordinate a.layers a.multiplicity
    a.globalCap a.localCap f.k f.fc f.F f.eq f.fw wl rfl f.slope f.invariant f.irreducible f.lifted f.degree f.quartic
    f.ord f.exactOrd (by simpa only [primaryOrder,mi,B6402ProfileCosts.fee] using pay)
    (by simpa only [nc] using a.load) a.weight a.ydegree a.gap p.w (by simpa only [a.total] using cap)
    S P Az hP hA matchP onF badP gbound
  have goodN : good.card≤N := hN ▸ Finset.card_le_univ _
  exact bound.trans (Nat.add_le_add_left (Nat.mul_le_mul goodN (by rcases hq with rfl|rfl <;> omega : H≤1813)) _)

#print axioms replacement
end ProximityPrize.SubmissionBinaryLower.B6402HardFactor
