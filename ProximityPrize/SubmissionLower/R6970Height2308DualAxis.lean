import ProximityPrize.SubmissionLower.R6970Height2313PairBounds
import ProximityPrize.SubmissionLower.Z6969FastTri

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Research6969.Geometry2308.DualAxis

open _root_.Research6969 _root_.Research6966
open PhysicalWindow (Request)
open HelperWindowIntervals (box bound cutoff)
open HelperAvoidance (rectSlots debitAt)
open K1_14 (L Equation)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (Parent Surface SeedField)
open PadeNativeQuotient (Native axis)
open Finset
open scoped Finset Classical

def floors (other first : ℕ) : Fin 2 → ℕ := ![other, first]

def fastSlots (U v other first k : ℕ) : ℕ :=
  if k*other ≤ U-v ∧ k*first ≤ v then
    (U-v-k*other+1)*(v-k*first+1)
  else 0

theorem fastSlots_eq (U v other first k : ℕ) :
    fastSlots U v other first k = rectSlots (box U v) (floors other first) k := by
  have both : (∀ z : Fin 2, k * (floors other first) z ≤ (box U v) z) ↔
      k*other ≤ U-v ∧ k*first ≤ v := by
    constructor
    · intro h
      exact ⟨by simpa [floors, box] using h 0, by simpa [floors, box] using h 1⟩
    · intro h z
      fin_cases z
      · simpa [floors, box] using h.1
      · simpa [floors, box] using h.2
  unfold fastSlots rectSlots
  by_cases ok : k*other ≤ U-v ∧ k*first ≤ v
  · simp [ok, both.mpr ok, KoalaRect.area, floors, box]
  · have bad : ¬ ∀ z : Fin 2, k * (floors other first) z ≤ (box U v) z := fun h => ok (both.mp h)
    simp [ok, bad]

def Cert (r : Request) (v other lo hi : ℕ) : Prop :=
  KoalaRect.area (box r.shape.U v)*r.bank.nodeRows+
    hi*((r.shape.U-v) + v + 2)*r.bank.poleMoment+
      bound r.shape 179730 r.reserve lo hi r.jet 1 r.weight r.shape.J
        (rectSlots (box r.shape.U v) (floors other r.seed)) <
    KoalaRect.area (box r.shape.U v) *
      HelperWindowPrefix.volume (cutoff r.shape 179730 hi r.reserve)
        r.shape.B r.shape.J (131071-lo)

def fast (r : Request) (v other lo hi : ℕ) : Bool :=
  let area := (r.shape.U-v+1)*(v+1)
  Nat.blt
    (area*r.bank.nodeRows+hi*((r.shape.U-v)+v+2)*r.bank.poleMoment+
      PhysicalWindow.Fast.boundG (fastSlots r.shape.U v other r.seed)
        r.shape.m r.shape.B r.shape.J r.reserve lo hi r.jet 1 r.weight r.shape.J)
    (area * PhysicalWindow.Fast.volF (cutoff r.shape 179730 hi r.reserve)
      r.shape.B r.shape.J (131071-lo))

theorem of_fast (r : Request) (v other lo hi : ℕ) (ok : fast r v other lo hi = true) :
    Cert r v other lo hi := by
  unfold fast at ok
  rw [Nat.blt_eq, PhysicalWindow.Fast.boundG_eq r.shape _ _
    (fun k => fastSlots_eq _ _ _ _ _), PhysicalWindow.Fast.volF_eq] at ok
  simpa [Cert, KoalaRect.area, box] using ok

structure Test where
  source : Request
  side : ℕ
  other : ℕ
  fits : TerminalWitness.Fits source 2308 2313 SpreadCatalogue.shape
  space : side ≤ source.shape.U
  checked : ∀ h, 2308≤h → h≤2313 → Cert source side other h h

def axisCap (t : Test) (high : ℕ) : ℕ :=
  (t.side+t.source.shape.J*high)/(t.source.reserve+1)

def Eligible (t : Test) (degree lo W axisLo axisHi : ℕ) : Prop :=
  0<lo ∧ t.other+axisHi≤lo ∧ t.source.seed≤axisLo ∧ t.source.jet=degree ∧ t.source.weight≤W

instance (t : Test) (degree lo W axisLo axisHi : ℕ) : Decidable (Eligible t degree lo W axisLo axisHi) := by
  unfold Eligible
  infer_instance

def tighten (t : Test) (degree lo W axisLo axisHi previous : ℕ) : ℕ :=
  if Eligible t degree lo W axisLo axisHi then min previous (axisCap t axisHi) else previous

theorem Test.bound (t : Test) {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2308 ≤ h) (hi : h ≤ 2313) {S : Finset Surface}
    (geo : ∀ q∈S, Parent q) (pass : ∀ q∈S, TerminalBanks.Pass Crt word 179730 SpreadCatalogue.shape q)
    {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive) {H : Equation}
    (on : NativeWitnessBank.witnessed N S H) (actual : G.graphDegree = t.source.jet)
    (positive : 0 < seedDegree N.poly)
    (axisLow : ∀ a, floors t.other t.source.seed a ≤ axis N.poly a)
    (physical : HelperPhysicalModel.Model Crt N.poly)
    (weight : t.source.weight ≤ RawPhysicalDegree.weight (131071-h) (131071-h-1) physical.raw)
    (upper : ℕ) (high : axis N.poly 1 ≤ upper) :
    KoalaRect.axisDegree H 1 ≤ axisCap t upper := by
  have hp : 0<h := by omega
  have legal : h≤131070 := hi.trans (by decide)
  have narrow : t.source.shape.J < 131071-h :=
    t.fits.narrow.trans_le (Nat.sub_le_sub_left hi 131071)
  let U := box t.source.shape.U t.side
  let lower := floors t.other t.source.seed
  have slots : U 0 + U 1 ≤ t.source.shape.U := by
    change t.source.shape.U-t.side+t.side≤t.source.shape.U
    rw [Nat.sub_add_cancel t.space]
  have all :=
    HelperWindowIntervals.positive t.source.shape 179730 t.source.reserve h h h
      t.source.jet 1 t.source.weight t.source.shape.J (KoalaRect.area U) (U 0+U 1+2)
      t.source.bank.nodeRows t.source.bank.poleMoment (rectSlots U lower)
      hp le_rfl le_rfl narrow
      (fun k hk => Or.inr (Or.inr (by simpa only [Nat.mul_one] using hk)))
      (t.checked h lo hi)
  have paid : KoalaRect.rectDebit h t.source.bank.nodeRows t.source.bank.poleMoment U+
      (∑ W∈range (t.source.top h),debitAt t.source.shape h (t.source.top h) W
        G.graphDegree 1 t.source.weight (rectSlots U lower)) <
      KoalaRect.area U*K1_14.shapeSum t.source.shape (fun q k=>t.source.top h+k-q*(131071-h)) := by
    rw [actual]
    simpa only [KoalaRect.rectDebit, PhysicalWindow.Request.top] using all
  have wide := _root_.Lower6960.HelperSource.width_at_height t.source.bank 179730
      2308 h t.source.reserve lo (legal.trans (by decide)) t.fits.push t.fits.wide
  change t.source.shape.B*(131071-h) < t.source.top h at wide
  have top : 0<t.source.top h := (Nat.zero_le _).trans_lt wide
  have cut : t.source.top h-1+2*h*t.source.reserve<t.source.shape.m*179730 := by
    change 0 < t.source.shape.m*179730 - 2*h*t.source.reserve at top
    change t.source.shape.m*179730 - 2*h*t.source.reserve - 1 + 2*h*t.source.reserve < _
    omega
  have height (j k : ℕ) (axis : Fin 2) :
      ((N.poly.coeff j).coeff k).degreeOf axis ≤ PadeNativeQuotient.axis N.poly axis :=
    (PadeNativeQuotient.axis_le N.poly axis _).mp le_rfl j k
  have d := NativeWitnessBank.rectangle hp legal Crt word N gp physical
    on U lower (PadeNativeQuotient.axis N.poly)
    (NearTerminal.seeded_of_positive positive)
    t.fits.seedChar t.fits.rank.moment.2 weight axisLow height slots wide.le top
    t.fits.rank.nodes.le t.fits.rank.moment.1 paid cut t.fits.shape t.fits.order geo pass
  unfold axisCap
  apply (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr
  rw [Nat.mul_comm]
  exact (d.2 1).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ high) _)

theorem Test.tighten_bound (t : Test) {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2308 ≤ h) (hi : h ≤ 2313) {S : Finset Surface}
    (geo : ∀ q∈S, Parent q) (pass : ∀ q∈S, TerminalBanks.Pass Crt word 179730 SpreadCatalogue.shape q)
    {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive) {H : Equation}
    (on : NativeWitnessBank.witnessed N S H) {degree sl W al ah previous : ℕ}
    (actual : G.graphDegree=degree) (seedLow : sl≤seedDegree N.poly)
    (left : al≤axis N.poly 1) (right : axis N.poly 1≤ah)
    (physical : HelperPhysicalModel.Model Crt N.poly)
    (weight : W≤RawPhysicalDegree.weight (131071-h) (131071-h-1) physical.raw)
    (old : KoalaRect.axisDegree H 1≤previous) :
    KoalaRect.axisDegree H 1 ≤ tighten t degree sl W al ah previous := by
  unfold tighten
  split
  · rename_i ok
    obtain ⟨positive, enough, one, jet, mass⟩ := ok
    have sum := PowerBox.seed_sum N.poly
    have other : t.other≤axis N.poly 0 := by omega
    have axisLow (a : Fin 2) : floors t.other t.source.seed a≤axis N.poly a := by
      fin_cases a
      · simpa [floors] using other
      · simpa [floors] using one.trans left
    exact le_min old (t.bound Crt word lo hi geo pass N gp on (actual.trans jet.symm)
      (positive.trans_le seedLow) axisLow physical (mass.trans weight) ah right)
  · exact old

end Research6970.Height2313.Research6969.Geometry2308.DualAxis
