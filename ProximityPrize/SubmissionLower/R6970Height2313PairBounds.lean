import ProximityPrize.SubmissionLower.Z6969Pack0666

set_option Elab.async false

-- Source: Research6969.MeasuredBound
section Z6969Source0857
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.MeasuredBound
open _root_.Research6969
noncomputable section
open K1_14 (Jet Equation Shape L)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (SeedField Surface Parent)
open Research6966
open PadeNativeQuotient (Native)
open PhysicalWindow (Request Cover Triangular Rectangle)
open Finset
open scoped Classical
set_option maxHeartbeats 1300000
set_option maxRecDepth 9000

inductive Kind where | triangle | either (side:ℕ)
deriving DecidableEq

structure Test where
  source:Request
  kind:Kind
  fits:TerminalWitness.Fits source 2308 2313 SpreadCatalogue.shape
  verified:match kind with
    | .triangle=>∃ends,Cover (Triangular source) 2313 2308 ends
    | .either side=>side≤source.shape.U ∧ ∃ends,Cover (Rectangle source side) 2313 2308 ends

def Test.seedFloor (t:Test):ℕ:=match t.kind with
  | .triangle=>t.source.seed
  | .either _=>2*t.source.seed-1

def Test.degreeCap (t:Test):ℕ:=(t.source.shape.B+(t.source.jet-1)*t.source.shape.J)/(t.source.reserve+1)
def Test.totalCap (t:Test) (u:ℕ):ℕ:=(t.source.shape.U+t.source.shape.J*u)/(t.source.reserve+1)

theorem Test.bounds (t:Test) {h:ℕ} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    (lo:2308≤h) (hi:h≤2313) {S:Finset Surface} (geo:∀q∈S,Parent q)
    (pass:∀q∈S,TerminalBanks.Pass Crt word 179730 SpreadCatalogue.shape q)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (actual:G.graphDegree=t.source.jet)
    {H:Equation} (on:NativeWitnessBank.witnessed N S H) (low:t.seedFloor≤seedDegree N.poly)
    (positive:0<seedDegree N.poly) (phys:HelperPhysicalModel.Model Crt N.poly)
    (weight:t.source.weight≤RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw):
    H.natDegree≤t.degreeCap ∧ (t.kind=.triangle → ∀u,seedDegree N.poly≤u→K1_14_4.seedDegree H≤t.totalCap u) := by
  have uses:=NearTerminal.seeded_of_positive positive
  have cut (n a b:ℕ) (bound:(t.source.reserve+1)*n≤a+b):n≤(a+b)/(t.source.reserve+1):=
    (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (by simpa [Nat.mul_comm n] using bound)
  have checked:=t.verified
  cases mode:t.kind with
  | triangle=>
    rw [mode] at checked
    obtain ⟨ends,cert⟩:=checked
    have sl:t.source.seed≤seedDegree N.poly:=by simpa [Test.seedFloor,mode] using low
    have applyAt (v:ℕ) (bound:seedDegree N.poly≤v):=
      TerminalWitness.triangular t.fits cert lo hi (by omega) (by omega) Crt word N gp phys on actual uses weight sl
        (fun j i=>(K1_14_2_2_2_1.seedDegree_le ..).mp bound j i) geo pass
    have deg:=(applyAt _ le_rfl).1
    rw [actual] at deg
    exact ⟨cut _ _ _ deg,fun _ v h=>cut _ _ _ (applyAt v h).2⟩
  | either side=>
    rw [mode] at checked
    obtain ⟨space,ends,cert⟩:=checked
    have minSeed:2*t.source.seed-1≤seedDegree N.poly:=by simpa [Test.seedFloor,mode] using low
    have sum:=PowerBox.seed_sum N.poly
    have pick:∃z:Fin 2,t.source.seed≤PadeNativeQuotient.axis N.poly z:=by
      by_cases yes:t.source.seed≤PadeNativeQuotient.axis N.poly 0
      · exact ⟨0,yes⟩
      · exact ⟨1,by omega⟩
    obtain ⟨z,atZ⟩:=pick
    let n:=seedDegree N.poly
    have high:=(K1_14_2_2_2_1.seedDegree_le N.poly n).mp le_rfl
    have deg:=(TerminalWitness.rectangle t.fits cert space lo hi (by omega) (by omega) Crt word N gp phys on
      actual uses weight z atZ (fun _=>n) (fun j i z=>(MvPolynomial.degreeOf_le_totalDegree ..).trans (high j i)) geo pass).1
    rw [actual] at deg
    exact ⟨cut _ _ _ deg,fun h=>by contradiction⟩

end
end Research6970.Height2313.Research6969.MeasuredBound
end Z6969Source0857

-- Source: Research6969.CaseBounds
section Z6969Source0863
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.CaseBounds
open _root_.Research6969
noncomputable section
open K1_14 (Equation FX L)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (SeedField Surface Parent)
open Research6966
open PadeNativeQuotient (Native)
open _root_.Research6970.Height2313.Research6969.MeasuredBound (Test Kind)
open Finset
set_option maxHeartbeats 1400000
set_option maxRecDepth 11000

structure Cap where
  grade:ℕ
  seed:ℕ
deriving DecidableEq

def Cap.step (c:Cap) (t:Test) (a lo wt:ℕ) (high:Option ℕ):Cap:=
  if t.source.jet=a ∧ 0<t.seedFloor ∧ t.seedFloor≤lo ∧ t.source.weight≤wt then
    ⟨min c.grade t.degreeCap,match high with
      | some v=>if t.kind=.triangle then min c.seed (t.totalCap v) else c.seed
      | none=>c.seed⟩
  else c

def run (a lo wt:ℕ) (high:Option ℕ) : List Test→Cap→Cap
  | [],c=>c
  | t::rest,c=>run a lo wt high rest (c.step t a lo wt high)

theorem sound (ts:List Test) {a lo wt h:ℕ} {high:Option ℕ} {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (floor:2308≤h) (ceil:h≤2313) {S:Finset Surface}
    (geo:∀q∈S,Parent q) (pass:∀q∈S,TerminalBanks.Pass Crt word 179730 SpreadCatalogue.shape q)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (deg:G.graphDegree=a)
    {H:Equation} (on:NativeWitnessBank.witnessed N S H) (low:lo≤seedDegree N.poly)
    (up:∀ v,high=some v→seedDegree N.poly≤v)
    (phys:HelperPhysicalModel.Model Crt N.poly) (physical:wt≤RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw)
    (c:Cap) (grade:H.natDegree≤c.grade) (seed:K1_14_4.seedDegree H≤c.seed):
    H.natDegree≤(run a lo wt high ts c).grade ∧ K1_14_4.seedDegree H≤(run a lo wt high ts c).seed := by
  induction ts generalizing c with
  | nil=>exact ⟨grade,seed⟩
  | cons t tail ih=>
    apply ih
    · dsimp only [Cap.step]
      split
      · rename_i accepted
        obtain ⟨same,pos,minimal,pole⟩:=accepted
        have bounds:=t.bounds Crt word floor ceil geo pass N gp (deg.trans same.symm) on
          (minimal.trans low) (pos.trans_le (minimal.trans low)) phys (pole.trans physical)
        exact le_min grade bounds.1
      · exact grade
    · dsimp only [Cap.step]
      split
      · rename_i accepted
        obtain ⟨same,pos,minimal,pole⟩:=accepted
        cases hHigh:high with
        | none=>exact seed
        | some v=>
          simp only
          split_ifs with tri
          · have bounds:=t.bounds Crt word floor ceil geo pass N gp (deg.trans same.symm) on
              (minimal.trans low) (pos.trans_le (minimal.trans low)) phys (pole.trans physical)
            exact le_min seed (bounds.2 tri v (up v hHigh))
          · exact seed
      · exact seed

end
end Research6970.Height2313.Research6969.CaseBounds
end Z6969Source0863

-- Source: Research6969.AxisTests
section Z6969Source1019
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.AxisTests
open _root_.Research6969
noncomputable section
open K1_14 (Equation FX L)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (Surface SeedField Parent)
open Research6966
open PadeNativeQuotient (Native)
open PhysicalWindow (Request Rectangle Cover)
open Finset
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

structure Test where
  source:Request
  width:ℕ
  fits:TerminalWitness.Fits source 2308 2313 SpreadCatalogue.shape
  space:width≤source.shape.U
  verified:∃ends,Cover (Rectangle source width) 2313 2308 ends

def step (t:Test) (a lo low high weight:ℕ) (p:_root_.Research6970.Height2313.Research6969.CaseBounds.Cap):_root_.Research6970.Height2313.Research6969.CaseBounds.Cap:=
  if 0<lo ∧ t.source.jet=a ∧ t.source.seed≤low ∧ t.source.weight≤weight then
    ⟨min p.grade ((t.source.shape.B+(a-1)*t.source.shape.J)/(t.source.reserve+1)),
      min p.seed ((t.width+t.source.shape.J*high)/(t.source.reserve+1))⟩
  else p

def run (a lo low high weight:ℕ):List Test→_root_.Research6970.Height2313.Research6969.CaseBounds.Cap→_root_.Research6970.Height2313.Research6969.CaseBounds.Cap
  | [],c=>c
  | t::ts,c=>run a lo low high weight ts (step t a lo low high weight c)

theorem sound {h} {D:PoleData h} (ts:List Test) (Crt:CRTLift D) (word:K1.I→L)
    (lo:2308≤h) (hi:h≤2313) {S:Finset Surface} (geo:∀q∈S,Parent q)
    (pass:∀q∈S,TerminalBanks.Pass Crt word 179730 SpreadCatalogue.shape q)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) {H:Equation} (on:NativeWitnessBank.witnessed N S H)
    {degree totalLow low high wt:ℕ} (actual:G.graphDegree=degree) (positive:totalLow≤seedDegree N.poly)
    (lAxis:low≤PadeNativeQuotient.axis N.poly 1) (hAxis:PadeNativeQuotient.axis N.poly 1≤high)
    (model:HelperPhysicalModel.Model Crt N.poly) (phys:wt≤RawPhysicalDegree.weight (131071-h) (131071-h-1) model.raw)
    (c:_root_.Research6970.Height2313.Research6969.CaseBounds.Cap) (grade:H.natDegree≤c.grade) (axis:KoalaRect.axisDegree H 1≤c.seed):
    H.natDegree≤(run degree totalLow low high wt ts c).grade ∧
    KoalaRect.axisDegree H 1≤(run degree totalLow low high wt ts c).seed:=by
  induction ts generalizing c with
  | nil=>exact ⟨grade,axis⟩
  | cons t ts ih=>
    by_cases enabled:0<totalLow ∧ t.source.jet=degree ∧ t.source.seed≤low ∧ t.source.weight≤wt
    · obtain ⟨pos,d,need,w⟩:=enabled
      have use:=NearTerminal.seeded_of_positive (pos.trans_le positive)
      obtain ⟨ends,cert⟩:=t.verified
      have height (j i z):((N.poly.coeff j).coeff i).degreeOf z≤PadeNativeQuotient.axis N.poly z:=
        (PadeNativeQuotient.axis_le N.poly z _).mp le_rfl j i
      obtain ⟨g,s⟩:=TerminalWitness.rectangle t.fits cert t.space lo hi (by omega) (by omega) Crt word N gp model on
        (actual.trans d.symm) use (w.trans phys) 1 (need.trans lAxis) (PadeNativeQuotient.axis N.poly)
        height geo pass
      rw [actual] at g
      have deg':H.natDegree≤(t.source.shape.B+(degree-1)*t.source.shape.J)/(t.source.reserve+1):=
        (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (by simpa only [Nat.mul_comm H.natDegree] using g)
      have bound:KoalaRect.axisDegree H 1≤(t.width+t.source.shape.J*high)/(t.source.reserve+1):=
        (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (by
          rw [Nat.mul_comm]
          exact s.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hAxis) _))
      have en:0<totalLow ∧ t.source.jet=degree ∧ t.source.seed≤low ∧ t.source.weight≤wt:=⟨pos,d,need,w⟩
      apply ih <;> simp only [step,ite_eq_left en]
      · exact le_min grade deg'
      · exact le_min axis bound
    · apply ih <;> simpa only [step,ite_eq_right enabled] using ‹_›

end
end Research6970.Height2313.Research6969.AxisTests
end Z6969Source1019
