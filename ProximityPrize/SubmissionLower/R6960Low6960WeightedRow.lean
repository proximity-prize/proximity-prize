import ProximityPrize.SubmissionLower.FadicChunk
import ProximityPrize.SubmissionLower.R6960Low6960FractionContact
import ProximityPrize.SubmissionLower.R6960Low6960WeightedCut

set_option Elab.async false

-- merged module ChargeTable
section Merged_ChargeTable

set_option autoImplicit false
namespace KoalaFarBridge
open FadicGate (Entry)

abbrev FeeBox := ℕ × ℕ × ℕ

structure GateRate where
  b : ℕ
  j : ℕ
  t : ℕ
  sep : ℕ
  unit : ℕ
  split : ℕ
  bl : ℕ
  jl : ℕ
  tl : ℕ
  deriving DecidableEq

def boxFee (g : GateRate) (z : FeeBox) : ℕ :=
  g.b * max z.1 z.2.1 + g.j * z.2.1 + g.t * min z.2.2 (z.2.1/3)

def residual (g : GateRate) (z : FeeBox) (a : ℕ) : FeeBox :=
  (z.1-a*g.bl, z.2.1-a*g.jl, z.2.2-a*g.tl)

def maxDepth (g : GateRate) (z : FeeBox) : ℕ :=
  min (z.1/g.bl) (min (z.2.1/g.jl) (z.2.2/g.tl))

def localLength (r a d e : ℕ) : ℕ := e*(24*(r-e*a)+d*(e-1))

/-- The same check is used at an f-adic depth and at the actual valuation of a plain row. -/
def chargeCheck (g : GateRate) (r a : ℕ) (z : FeeBox) (d : ℕ) : Bool :=
  (List.range g.split).all fun k =>
    let e := k+1
    let len := localLength r a d e
    decide (0 < len ∧ (g.split+1-e)*(24*boxFee g z+d*g.sep) ≤ g.split*g.unit*len)

theorem charge_of_check (g : GateRate) {r a d e : ℕ} {z : FeeBox}
    (h : chargeCheck g r a z d = true) (he : 1 ≤ e) (hs : e ≤ g.split) :
    0 < localLength r a d e ∧
      (g.split+1-e)*(24*boxFee g z+d*g.sep) ≤ g.split*g.unit*localLength r a d e := by
  unfold chargeCheck at h
  have hi : e-1 ∈ List.range g.split := List.mem_range.mpr (by omega)
  have hv := of_decide_eq_true (List.all_eq_true.mp h (e-1) hi)
  simpa only [Nat.sub_add_cancel he] using hv

def plainCheck (g : GateRate) (r : ℕ) (z : FeeBox) (ds : List ℕ) : Bool :=
  (List.range (maxDepth g z+1)).all fun a => chargeCheck g r a (residual g z a) (ds.getD a 0)

theorem plain_at (g : GateRate) {r a : ℕ} {z : FeeBox} {ds : List ℕ}
    (h : plainCheck g r z ds = true) (ha : a ≤ maxDepth g z) :
    chargeCheck g r a (residual g z a) (ds.getD a 0) = true :=
  List.all_eq_true.mp h a (List.mem_range.mpr (by omega))

def depthCheck (g : GateRate) (r : ℕ) (boxes : List Entry) (ds : List ℕ) : Bool :=
  (List.range boxes.length).all fun a =>
    match boxes.getD a none with
    | none => true
    | some z => chargeCheck g r a z (ds.getD a 0)

theorem depth_at (g : GateRate) {r a : ℕ} {z : FeeBox} {boxes : List Entry} {ds : List ℕ}
    (h : depthCheck g r boxes ds = true) (ha : a < boxes.length) (he : boxes.getD a none = some z) :
    chargeCheck g r a z (ds.getD a 0) = true := by
  have hv := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  change (match boxes.getD a none with
    | none => true
    | some v => chargeCheck g r a v (ds.getD a 0)) = true at hv
  rw [he] at hv
  exact hv

def rowCheck (g : GateRate) (r : ℕ) (boxes : List Entry) (ds : List ℕ) (z : FeeBox) (pd : List ℕ) : Bool :=
  depthCheck g r boxes ds && plainCheck g r z pd

/-- Reuse the first full-source schedule at every later level. -/
theorem charge_mono (g : GateRate) {r R a d e : ℕ} {z : FeeBox} (hr : R ≤ r)
    (h : 0 < localLength R a d e ∧
      (g.split+1-e)*(24*boxFee g z+d*g.sep) ≤ g.split*g.unit*localLength R a d e) :
    0 < localLength r a d e ∧
      (g.split+1-e)*(24*boxFee g z+d*g.sep) ≤ g.split*g.unit*localLength r a d e := by
  have hL : localLength R a d e ≤ localLength r a d e := by
    unfold localLength
    gcongr
  exact ⟨h.1.trans_le hL,h.2.trans (Nat.mul_le_mul_left _ hL)⟩

end KoalaFarBridge

end Merged_ChargeTable

-- merged module R6960Low6960WeightedRow
section Merged_R6960Low6960WeightedRow

set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

namespace Low6960WeightedRow
noncomputable section
open K1_13 (Row Geom Shape shape InBox)
open K1_13_6 (GeoJets GenericField toGeneric intersectionIdeal cycleLength)
open K1_13_6_1_2 (VanishesTo hassePartial multiOrder)
open Low6960SharedPrice (Rate coord)
open Low6960WeightedRate (Envelope Pays Fits split unit)
open KoalaFarBridge (GateRate FeeBox residual maxDepth chargeCheck)
open Low6960WeightedTally (Relevant)
open Low6960WeightedCut (order)
open Low6960SharedRational
open MvPolynomial
open scoped ENat Polynomial
open Low6960FractionContact (contact_clear proper_after_clear frac_map)
open Low6960SharedChooseCut (valuation_factorization)

def castBox (z : FeeBox) : Shape := ⟨z.1,z.2.1,z.2.2⟩

def rate (p : Envelope) : GateRate :=
  ⟨p.coeff.b,p.coeff.j,p.coeff.t,p.sep,unit,split,p.widthLow,p.indexLow,p.topLow⟩

def Ready {f : Row 4} {u : Rate} (P : Finset (Ideal GeoJets)) : Prop :=
  ∃ (n : ℕ) (G : Row 4), 0 < n ∧ ¬ f ∣ G ∧
    (∀ N > 0, ∀ p ∈ P, ∃ h : (intersectionIdeal f (G^N)).IsMinimalPrime p,
      ((N*n*(u.split+1-order f (u.split+1) p) : ℕ) : ℕ∞) ≤
        cycleLength (intersectionIdeal f (G^N)) p h.isPrime) ∧
    Low6960SharedPrice.surface u.kind (shape f) (shape G).chamber ≤
      Low6960SharedPrice.surfaceScale u.kind * (u.split*u.amount) * n

def Contacts (P : Finset (Ideal GeoJets)) (r : ℕ) (v : FractionJet) : Prop :=
  ∀ p ∈ P, ∀ m : Fin 4 →₀ ℕ, multiOrder m < r → hassePartial m (toGeometric v) ∈ p

private theorem rowBox {Q : Row 4} {B J T : ℕ}
    (h : ∀ m ∈ Q.support, m ∈ FadicGate.slopeBox B J T) : InBox (shape Q) ⟨B,J,T⟩ := by
  refine ⟨?_,?_,?_⟩
  · change Q.totalDegree ≤ B
    rw [← weightedTotalDegree_one]
    exact Finset.sup_le fun m hm => (h m hm).1
  · change K1_13.indexDegree Q ≤ J
    rw [K1_13_1.indexDegree_eq]
    exact Finset.sup_le fun m hm => (h m hm).2.1
  · change Q.degreeOf 3 ≤ T
    rw [← weightedTotalDegree_piSingle (3 : Fin 4)]
    have he : Pi.single (3 : Fin 4) (1 : ℕ) = FadicGate.topWeight := by
      funext i
      simp [Pi.single_apply, FadicGate.topWeight, eq_comm]
    rw [he]
    exact Finset.sup_le fun m hm => by
      rw [FadicGate.w_top]
      exact (h m hm).2.2

private theorem localCut {f C H : Row 4} {p : Envelope} {u : Rate} {z : FeeBox} {r a d R : ℕ}
    (hf : Low6960Prices.SmallFactor f) (hp : Pays p (shape f) u) (hproper : ¬ f ∣ C)
    (hC : InBox (shape C) (castBox z)) (hR : R ≤ r) (hcheck : chargeCheck (rate p) R a z d = true)
    (P : Finset (Ideal GeoJets)) (hs : ∀ q ∈ P, Relevant f u (order f (u.split+1)) q)
    (hv : ∀ q (hq : q ∈ P), @VanishesTo _ _ q (hs q hq).1 (toGeneric (f^a*(C+f*H))) r) :
    Ready (f := f) (u := u) P := by
  have hk := hp.2.1
  have hsplit := hp.2.2.1
  have hamount := hp.2.2.2.1
  have hfitted := hp.2.2.2.2.1
  apply Low6960WeightedCut.of_contact hf hproper u (fun _ => hfitted) r a d (castBox z) hC P hs hv
  · rw [hk, hsplit]
    change 10 ≤ 1920*(10*u.amount)
    omega
  · intro e he hse
    have hse' : e ≤ (rate p).split := by
      change e ≤ split
      rwa [← hsplit]
    obtain ⟨hpos, hfee⟩ := KoalaFarBridge.charge_mono (rate p) hR
      (KoalaFarBridge.charge_of_check _ hcheck he hse')
    exact ⟨hpos, Low6960WeightedRate.transfer hp (castBox z) r a d e hfee⟩

theorem adic {f : Row 4} {p : Envelope} {u : Rate} {r a : ℕ}
    (hf : Low6960Prices.SmallFactor f) (hp : Pays p (shape f) u) (z : FeeBox) (d : ℕ)
    (hcheck : chargeCheck (rate p) r a z d = true)
    {v c h : FractionJet} (hv : v = (toFraction f)^a * (c + toFraction f * h))
    (hc : ¬ toFraction f ∣ c) (hbox : c ∈ restrictSupport GenericField (FadicGate.slopeBox z.1 z.2.1 z.2.2))
    (P : Finset (Ideal GeoJets)) (hs : ∀ q ∈ P, Relevant f u (order f (u.split+1)) q)
    (hcontact : Contacts P r v) : Ready (f := f) (u := u) P := by
  obtain ⟨dc, C, hdc, hS, hC⟩ := clear_denominators c
  obtain ⟨dh, H, hdh, _, hH⟩ := clear_denominators h
  let C' := MvPolynomial.C dh*C
  let H' := MvPolynomial.C dc*H
  let k := algebraMap (Polynomial Geom) GenericField dc * algebraMap (Polynomial Geom) GenericField dh
  have h0 : k ≠ 0 := mul_ne_zero
    ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericField)).mpr hdc)
    ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial Geom) GenericField)).mpr hdh)
  have hC' : toFraction C' = MvPolynomial.C k*c := calc
    _ = MvPolynomial.C (algebraMap (Polynomial Geom) GenericField dh) * toFraction C := by
      simp only [C', frac_map, map_mul, MvPolynomial.map_C]
    _ = _ := by simp only [hC, ← mul_assoc, ← map_mul, k, mul_comm (algebraMap (Polynomial Geom) GenericField dh)]
  have hH' : toFraction H' = MvPolynomial.C k*h := calc
    _ = MvPolynomial.C (algebraMap (Polynomial Geom) GenericField dc) * toFraction H := by
      simp only [H', frac_map, map_mul, MvPolynomial.map_C]
    _ = _ := by simp only [hH, ← mul_assoc, ← map_mul, k]
  let φ : Row 4 →+* FractionJet := MvPolynomial.map (algebraMap (Polynomial Geom) GenericField)
  have hQ : toFraction (f^a*(C'+f*H')) = MvPolynomial.C k*v := calc
    φ (f^a*(C'+f*H')) = (φ f)^a*(φ C'+φ f*φ H') := by simp only [map_mul, map_pow, map_add]
    _ = _ := by
      change (toFraction f)^a*(toFraction C'+toFraction f*toFraction H') = _
      rw [hC', hH', hv]
      ring
  have hCbox : InBox (shape C') (castBox z) := rowBox (Q := C') fun m hm => by
    apply (mem_restrictSupport_iff GenericField).mp hbox
    rw [← hS]
    by_contra hw
    have hz := notMem_support_iff.mp hw
    exact (mem_support_iff.mp hm) (by simp [C', coeff_C_mul, hz])
  refine localCut (H := H') hf hp (proper_after_clear h0 hC' hc) hCbox le_rfl hcheck P hs ?_
  intro q hq
  letI := (hs q hq).1
  exact contact_clear hQ (hcontact q hq)

theorem plain {f : Row 4} {p : Envelope} {u : Rate} {r R : ℕ}
    (hf : Low6960Prices.SmallFactor f) (hp : Pays p (shape f) u)
    (hsize : 0 < p.widthLow ∧ 0 < p.indexLow ∧ 0 < p.topLow)
    (z : FeeBox) (ds : List ℕ) (hR : R ≤ r) (hcheck : KoalaFarBridge.plainCheck (rate p) R z ds = true)
    {v : FractionJet} (hv : v ≠ 0) (hbox : v ∈ restrictSupport GenericField (FadicGate.slopeBox z.1 z.2.1 z.2.2))
    (P : Finset (Ideal GeoJets)) (hs : ∀ q ∈ P, Relevant f u (order f (u.split+1)) q)
    (hcontact : Contacts P r v) : Ready (f := f) (u := u) P := by
  obtain ⟨_, Q, _, hS, hQ⟩ := clear_denominators v
  have hQ0 : Q ≠ 0 := by
    intro hzero
    apply hv (support_eq_empty.mp ?_)
    rw [← hS, hzero, support_zero]
  have ht : 0 < f.totalDegree := hf.2.1.trans_le (degreeOf_le_totalDegree _ _)
  obtain ⟨a,C,hQC,hC0,hproper⟩ := valuation_factorization hf.1.ne_zero ht hQ0
  have hbound : InBox (shape Q) (castBox z) := rowBox (Q := Q) fun m hm =>
    (mem_restrictSupport_iff GenericField).mp hbox (hS ▸ hm)
  have hb := Low6960SharedChooseCut.shape_product hf.1.ne_zero hC0 hQC 0
  have hj := Low6960SharedChooseCut.shape_product hf.1.ne_zero hC0 hQC 1
  have ht' := Low6960SharedChooseCut.shape_product hf.1.ne_zero hC0 hQC 2
  change (shape Q).b = a*(shape f).b+(shape C).b at hb
  change (shape Q).j = a*(shape f).j+(shape C).j at hj
  change (shape Q).t = a*(shape f).t+(shape C).t at ht'
  have hlow := hp.1
  have hB := Nat.mul_le_mul_left a hlow.1
  have hJ := Nat.mul_le_mul_left a hlow.2.2.1
  have hT := Nat.mul_le_mul_left a hlow.2.2.2.2.1
  have h1 := hbound.1
  have h2 := hbound.2.1
  have h3 := hbound.2.2
  change (shape Q).b ≤ z.1 at h1
  change (shape Q).j ≤ z.2.1 at h2
  change (shape Q).t ≤ z.2.2 at h3
  have hdepth : a ≤ maxDepth (rate p) z := by
    change a ≤ min (z.1/p.widthLow) (min (z.2.1/p.indexLow) (z.2.2/p.topLow))
    exact le_min ((Nat.le_div_iff_mul_le hsize.1).mpr (by omega))
      (le_min ((Nat.le_div_iff_mul_le hsize.2.1).mpr (by omega))
        ((Nat.le_div_iff_mul_le hsize.2.2).mpr (by omega)))
  have hCbox : InBox (shape C) (castBox (residual (rate p) z a)) := by
    refine ⟨?_,?_,?_⟩ <;> simp only [castBox, KoalaFarBridge.residual, rate] <;> omega
  refine localCut (H := 0) hf hp hproper hCbox hR (KoalaFarBridge.plain_at _ hcheck hdepth) P hs ?_
  intro q hq
  letI := (hs q hq).1
  have hvan := contact_clear hQ (hcontact q hq)
  simpa only [hQC, mul_zero, add_zero] using hvan

end
end Low6960WeightedRow

end Merged_R6960Low6960WeightedRow
