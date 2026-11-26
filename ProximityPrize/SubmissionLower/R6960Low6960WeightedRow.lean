import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdAE
import ProximityPrize.SubmissionLower.DdB6
import ProximityPrize.SubmissionLower.DdCS
import ProximityPrize.SubmissionLower.FadicChunk
import ProximityPrize.SubmissionLower.R6960Low6960FractionContact
import ProximityPrize.SubmissionLower.R6960Low6960Tiles0

section Merged6967_R6960Low6960WeightedRow
set_option Elab.async false




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

#print axioms adic
#print axioms plain
end
end Low6960WeightedRow

end Merged_R6960Low6960WeightedRow

end Merged6967_R6960Low6960WeightedRow

section Merged6967_R6960RetainedCompressionProjection
set_option Elab.async false






set_option Elab.async false

-- merged module R6960TerminalMarked
section Merged_R6960TerminalMarked
noncomputable section
set_option Elab.async false
namespace Lower6960.TerminalMarked
open Polynomial Finset
open K1 (K)
open K1_14 (Equation FX Seeds seedEmbedding graphEval atMark atX)
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open KoalaRect (axisDegree axisDegree_le_iff)
open RescueGeometry (Model Family)
open scoped Polynomial Classical
def determinant (f : Equation) : Seeds :=
  f.resultant f.derivative f.natDegree (f.natDegree-1)
theorem det_axis (f : Equation) (i : Fin 2) :
    (determinant f).degreeOf i≤(2*f.natDegree-1)*axisDegree f i := by
  have coeffs := (axisDegree_le_iff f i _).mp le_rfl
  have der (j : ℕ) : (f.derivative.coeff j).degreeOf i≤axisDegree f i := by
    rw [coeff_derivative]
    have eq : ((j:Seeds)+1)=MvPolynomial.C ((j:FX)+1) := by simp
    rw [eq]
    apply (MvPolynomial.degreeOf_mul_le ..).trans
    rw [MvPolynomial.degreeOf_C,Nat.add_zero]
    exact coeffs (j+1)
  exact (ThirdPole.resultant_axis f f.derivative _ _ _ _ i coeffs der).trans
    (by rw [←Nat.add_mul]; apply Nat.mul_le_mul_right; omega)
theorem bad_labels (f : Equation) (sep : (f.map (algebraMap Seeds K1_14_2.SeedField)).Separable)
    (degree : f.natDegree<48) (axes : axisDegree f 0+axisDegree f 1≤2400)
    (T : Finset K) (label : K→K) (inj : Set.InjOn label (T:Set K)) :
    (T.filter (fun γ=>graphEval (label γ) (determinant f)=0)).card≤
      (2*f.natDegree-1)*(axisDegree f 0+K1.p*axisDegree f 1) := by
  classical
  let B:=T.filter (fun γ=>graphEval (label γ) (determinant f)=0)
  let coord (γ : K) := seedEmbedding (label γ)
  have eq : (B.image coord).card=B.card :=
    card_image_of_injOn (fun x hx y hy h=>inj (mem_filter.mp hx).1 (mem_filter.mp hy).1 (seedEmbedding.injective h))
  have small : (2*f.natDegree-1)*axisDegree f 0<K1.p :=
    (Nat.mul_le_mul (by omega : 2*f.natDegree-1≤93) (by omega : axisDegree f 0≤2400)).trans_lt (by decide)
  have nz : determinant f≠0 := resultant_derivative_ne_zero_of_separable_map_fractionField f sep
  have cap := K1_10.frobenius_coefficient_exception_count K1.p _ _ (by decide) _ nz
    (det_axis f 0) small (det_axis f 1) (B.image coord) (by
      intro z hz
      obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hz
      exact (mem_filter.mp hγ).2)
  rw [eq] at cap
  exact cap.trans_eq (by ring)
def simpleSheet (f : Equation) (label : K) (word : (Polynomial K)) : Prop :=
  let q:=f.map (graphEval label)
  q.natDegree=f.natDegree ∧ q.Separable ∧
  ∃ H Q : (Polynomial FX), q=(Polynomial.X-C (atX word))*Q ∧ H.eval (atX word)=1 ∧ Q∣H ∧
    let e:=AdjoinRoot.mk q H
    e^2=e ∧ e≠0 ∧ e≠1
def excCap : ℕ := 93*2400*K1.p
def paidCap : ℕ := MainGeometry.prefixCap+TerminalSmall.smallCap+excCap
theorem good_remainder {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (lo : 2359≤M.overhead.toNat)
    (hi : M.overhead.toNat≤33579) (regular : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Γ.card≤paidCap ∨ ∃ (T : Finset K) (f : Equation),T⊆Γ ∧ Γ.card≤paidCap+T.card ∧
      3≤f.natDegree ∧ f.natDegree<48 ∧ axisDegree f 0+axisDegree f 1≤2400 ∧
      (∀ j : Fin 2,axisDegree f j<(TerminalReceipts.witness f.natDegree).order 1) ∧
      ∀ γ∈T,simpleSheet f (M.label γ) (F.scalar γ) ∧
        ∃ q : Equation,Irreducible q ∧ q∣f ∧ 3≤q.natDegree ∧ atMark q (M.label γ) (F.scalar γ)=0 := by
  classical
  rcases TerminalSmall.higher_remainder F Crt lo hi regular residues with all | ⟨U,f,sub,price,prim,sep,deg,axes,graded,marks⟩
  · exact Or.inl (all.trans (by unfold paidCap; omega))
  let B:=U.filter (fun γ=>graphEval (M.label γ) (determinant f)=0)
  let T:=U\B
  have cost := bad_labels f sep deg axes U M.label (fun _ _ _ _ eq=>sub_left_inj.mp eq)
  have bc : B.card≤excCap := by
    apply cost.trans
    have scale : axisDegree f 0+K1.p*axisDegree f 1≤K1.p*2400 := by
      change axisDegree f 0+2130706433*axisDegree f 1≤2130706433*2400; omega
    exact (Nat.mul_le_mul (by omega : 2*f.natDegree-1≤93) scale).trans_eq (by unfold excCap; ring)
  have count : T.card+B.card=U.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  rcases T.eq_empty_or_nonempty with empty | ⟨z,hz⟩
  · left; rw [empty,card_empty,zero_add] at count; unfold paidCap; omega
  have size : 3≤f.natDegree := by
    obtain ⟨q,_,dv,de,_⟩ := marks z (mem_sdiff.mp hz).1
    exact de.trans (natDegree_le_of_dvd dv prim.ne_zero)
  refine Or.inr ⟨T,f,sdiff_subset.trans sub,by unfold paidCap; omega,size,deg,axes,graded,?_⟩
  intro γ hγ
  have hu := (mem_sdiff.mp hγ).1
  have safe : graphEval (M.label γ) (determinant f)≠0 :=
    fun zero=>(mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨hu,zero⟩)
  refine ⟨?_,marks γ hu⟩
  obtain ⟨q,_,⟨g,eq⟩,_,hit⟩ := marks γ hu
  have root : (f.map (graphEval (M.label γ))).eval (atX (F.scalar γ))=0 := by
    change eval₂ (graphEval (M.label γ)) (atX (F.scalar γ)) q=0 at hit
    rw [eval_map,eq,eval₂_mul,hit,zero_mul]
  have full := natDegree_map_eq_of_resultant_derivative_padded_ne_zero _ _ le_rfl safe
  exact ⟨full,separable_map_of_resultant_derivative_padded_ne_zero _ _ le_rfl (by omega) safe,
    MarkedRoot.sheet (by omega) _ root
      (eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero _ _ le_rfl (by omega) safe _ root)⟩
#print axioms good_remainder
end Lower6960.TerminalMarked

end
end Merged_R6960TerminalMarked

-- merged module R6960RetainedCompressionProjection
section Merged_R6960RetainedCompressionProjection
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000
namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Finset
open K1 (K p)
open K1_14 (L FX Equation Seeds seedEmbedding graphEval atX)
open CurvatureSquares (Ordinate zView ordEval)
open KoalaRect (axisDegree axisDegree_le_iff)
open scoped Polynomial nonZeroDivisors
abbrev RationalOrdinate := Polynomial (Polynomial FX)
abbrev incl := algebraMap (Polynomial L) FX
private def graph : Seeds →+* (Polynomial FX) := (K1_14.frobeniusGraph (F := FX) p).toRingHom
def project (f : Equation) : RationalOrdinate := f.map graph
def intoFraction (P : Ordinate) : RationalOrdinate :=
  P.map ((mapRingHom incl).comp Bivariate.swap.toRingHom)
private theorem incl_inj : Function.Injective incl := IsFractionRing.injective (Polynomial L) FX
private theorem coeff_into (P : Ordinate) (i j : ℕ) :
    ((intoFraction P).coeff i).coeff j = incl ((Bivariate.swap (P.coeff i)).coeff j) := by
  simp [intoFraction]
private theorem into_degree (P : Ordinate) : (intoFraction P).natDegree=P.natDegree :=
  natDegree_map_eq_of_injective ((Polynomial.map_injective incl incl_inj).comp Bivariate.swap.injective) P
private theorem degree_project (f : Equation) (small : axisDegree f 0<p) :
    (project f).natDegree=f.natDegree := by
  by_cases nz : f=0
  · simp [nz,project]
  apply natDegree_map_of_leadingCoeff_ne_zero graph
  exact K1_14.frobeniusGraph_ne_zero p (by decide) f.leadingCoeff
    (leadingCoeff_ne_zero.mpr nz) (((axisDegree_le_iff f 0 _).mp le_rfl f.natDegree).trans_lt small)
private theorem projected_coeff (f : Equation) (i : ℕ) :
    ((project f).coeff i).natDegree≤axisDegree f 0+p*axisDegree f 1 := by
  rw [project, coeff_map]
  exact K1_14.frobeniusGraph_degree p _ _ (f.coeff i)
    ((axisDegree_le_iff f 0 _).mp le_rfl i) ((axisDegree_le_iff f 1 _).mp le_rfl i)
private theorem graph_eval (z : K) :
    (evalRingHom (seedEmbedding z)).comp graph=graphEval z := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [graph, K1_14.frobeniusGraph, graphEval]
  · intro i
    fin_cases i <;> simp [graph, K1_14.frobeniusGraph, graphEval]
theorem specialize_project (f : Equation) (z : K) :
    (project f).map (evalRingHom (seedEmbedding z))=f.map (graphEval z) := by
  rw [project, Polynomial.map_map, graph_eval]
theorem clear_abscissa (G : RationalOrdinate) :
    ∃ (d : (Polynomial L)) (P : Ordinate), d≠0 ∧ intoFraction P=C (C (incl d))*G := by
  classical
  let S := G.support.sigma (fun i => (G.coeff i).support)
  let coeffs (x : Σ _ : ℕ, ℕ) : FX := (G.coeff x.1).coeff x.2
  let den := IsLocalization.commonDenom (nonZeroDivisors (Polynomial L)) S coeffs
  let ints := IsLocalization.integerMultiple (nonZeroDivisors (Polynomial L)) S coeffs
  let value (i j : ℕ) : (Polynomial L) := if h : (⟨i,j⟩ : Σ _ : ℕ, ℕ) ∈ S then ints ⟨⟨i,j⟩,h⟩ else 0
  let raw : Ordinate :=
    ∑ i∈G.support, monomial i (∑ j∈(G.coeff i).support, monomial j (value i j))
  let P := raw.map Bivariate.swap.toRingHom
  have degree (i j : ℕ) : (raw.coeff i).coeff j = value i j := by
    by_cases hi : i∈G.support
    · by_cases hj : j∈(G.coeff i).support
      · simp [raw, Polynomial.finsetSum_coeff, coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq',
          hi, hj]
      · have hnot : (⟨i,j⟩ : Σ _ : ℕ, ℕ) ∉ S := fun m => hj (Finset.mem_sigma.mp m).2
        simp [raw, Polynomial.finsetSum_coeff, coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq',
          hi, hj, value, hnot]
    · have hnot : (⟨i,j⟩ : Σ _ : ℕ, ℕ) ∉ S := fun m => hi (Finset.mem_sigma.mp m).1
      simp [raw, Polynomial.finsetSum_coeff, coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq',
        hi, value, hnot]
  refine ⟨den,P,nonZeroDivisors.coe_ne_zero den,?_⟩
  ext i j
  rw [coeff_into,show P.coeff i=Bivariate.swap (raw.coeff i) from coeff_map ..,
    Bivariate.swap_swap_apply, degree, coeff_C_mul, coeff_C_mul]
  by_cases h : (⟨i,j⟩ : Σ _ : ℕ, ℕ) ∈ S
  · have prop := IsLocalization.map_integerMultiple (nonZeroDivisors (Polynomial L)) S coeffs ⟨⟨i,j⟩,h⟩
    change incl (ints ⟨⟨i,j⟩,h⟩)=(den : (Polynomial L)) • (G.coeff i).coeff j at prop
    rw [Algebra.smul_def] at prop
    simpa only [value, dite_eq_left h] using prop
  · have zero : (G.coeff i).coeff j=0 := by
      by_contra ne
      have hj := mem_support_iff.mpr ne
      exact h (Finset.mem_sigma.mpr ⟨mem_support_iff.mpr (fun z => by simpa [z] using ne),hj⟩)
    simp [value, h,zero]
def specialize (P : Ordinate) (z : L) : Polynomial (Polynomial L) :=
  P.map (mapRingHom (evalRingHom z))
theorem eval_swap {F : Type*} [Field F] (Q : Polynomial (Polynomial F)) (z : F) :
    (Bivariate.swap Q).eval (C z) = Q.map (evalRingHom z) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, eval_add, hP, hQ, Polynomial.map_add]
  | monomial n a =>
    rw [Bivariate.swap_monomial, eval_mul, eval_C, eval_map_apply, map_monomial,
      coe_evalRingHom, C_mul_X_pow_eq_monomial]
theorem specialize_into (P : Ordinate) (z : L) :
    (intoFraction P).map (evalRingHom (incl (C z)))=(specialize P z).map incl := by
  ext i
  simp only [intoFraction, specialize, coeff_map, RingHom.comp_apply, coe_mapRingHom,
    coe_evalRingHom, eval_map]
  change (Bivariate.swap (P.coeff i)).eval₂ incl (incl (C z)) =
    incl ((P.coeff i).map (evalRingHom z))
  have mapped := Polynomial.hom_eval₂ (p := Bivariate.swap (P.coeff i))
    (f := RingHom.id (Polynomial L)) (g := incl) (C z)
  rw [RingHom.comp_id] at mapped
  rw [← mapped]
  exact congrArg incl (eval_swap (P.coeff i) z)
private theorem z_coeff (P : Ordinate) (i j : ℕ) :
    ((zView P).coeff j).coeff i = (Bivariate.swap (P.coeff i)).coeff j := by
  change ((Bivariate.swap (P.map Bivariate.swap.toRingHom)).coeff j).coeff i =
    (Bivariate.swap (P.coeff i)).coeff j
  rw [CurvatureSquares.coeff_swap, coeff_map]
  rfl
theorem integral_project_with_width (f : Equation) (nz : f≠0) (small : axisDegree f 0<p)
    (width : ℕ) (coeffs : ∀ i,((project f).coeff i).natDegree≤width) :
    ∃ (d : (Polynomial L)) (P : Ordinate), d≠0 ∧ P≠0 ∧ P.natDegree=f.natDegree ∧
      (zView P).natDegree≤width ∧
      ∀ z : K, (specialize P (algebraMap K L z)).map incl = C (incl d)*f.map (graphEval z) := by
  obtain ⟨d,P,hd,eq⟩ := clear_abscissa (project f)
  have dn : incl d≠0 := (map_ne_zero_iff incl incl_inj).mpr hd
  have pn : project f≠0 := by
    intro z
    have hl := degree_project f small
    unfold project at z
    have killed := congrArg (fun V : RationalOrdinate => V.coeff f.natDegree) z
    have hp : graph f.leadingCoeff≠0 :=
      K1_14.frobeniusGraph_ne_zero p (by decide) _ (leadingCoeff_ne_zero.mpr nz)
        (((axisDegree_le_iff f 0 _).mp le_rfl f.natDegree).trans_lt small)
    exact hp (by simpa only [coeff_map,coeff_natDegree,coeff_zero] using killed)
  refine ⟨d,P,hd,fun h => ?_,?_,?_,?_⟩
  · rw [h,intoFraction,Polynomial.map_zero] at eq
    exact (mul_ne_zero (C_ne_zero.mpr (C_ne_zero.mpr dn)) pn) eq.symm
  · rw [← into_degree P,eq,natDegree_C_mul (C_ne_zero.mpr dn),degree_project f small]
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    apply Polynomial.ext
    intro i
    rw [z_coeff,coeff_zero]
    apply incl_inj
    rw [← coeff_into,eq,coeff_C_mul,coeff_C_mul,coeff_eq_zero_of_natDegree_lt
      ((coeffs i).trans_lt hj),mul_zero,map_zero]
  · intro z
    have label : incl (C (algebraMap K L z))=seedEmbedding z := rfl
    rw [← specialize_into, label, eq, Polynomial.map_mul, Polynomial.map_C, specialize_project]
    simp only [coe_evalRingHom, eval_C]
theorem integral_project (f : Equation) (nz : f≠0) (small : axisDegree f 0<p) :
    ∃ (d : (Polynomial L)) (P : Ordinate), d≠0 ∧ P≠0 ∧ P.natDegree=f.natDegree ∧
      (zView P).natDegree≤axisDegree f 0+p*axisDegree f 1 ∧
      ∀ z : K, (specialize P (algebraMap K L z)).map incl = C (incl d)*f.map (graphEval z) :=
  integral_project_with_width f nz small _ (projected_coeff f)
#print axioms integral_project
end
end Lower6960.RetainedCompression

end Merged_R6960RetainedCompressionProjection

end Merged6967_R6960RetainedCompressionProjection

section Merged6967_R6966ProofNativeGraphExceptional
set_option Elab.async false



set_option Elab.async false

namespace Research6966.NativeGraphExceptional
open Polynomial Finset
open K1_14 (Seeds Equation FX seedEmbedding graphEval atX)
open K1_14_3 (SeedField SeedClosure)
open PadeNativeQuotient (Native)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private abbrev φ:=K1_14_3.seedGeneric
private abbrev f:=algebraMap SeedField SeedClosure
def den {G:Pade.Row SeedField} (N:Native G) : Equation := N.poly.coeff 1
def rhs {G:Pade.Row SeedField} (N:Native G) : Equation := -N.poly.coeff 0

theorem den_ne {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) : den N≠0 := by
  change N.poly.coeff 1≠0
  rw [←NativeGraphMarks.slope_degree N gp,coeff_natDegree]
  exact leadingCoeff_ne_zero.mpr N.primitive.ne_zero

theorem coprime_generic {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) :
    IsCoprime ((den N).map φ) ((rhs N).map φ) := by
  have A:(den N).map φ=C N.scalar*(G.map f).a := by
    have eq:=congrArg (fun P:SeedClosure[X][X]=>P.coeff 1) N.eq
    simpa [K1_14_3.fibreRow,K1_14_1.jetConstant,Pade.Row.polynomial,coeff_C_mul,den] using eq
  have B:(rhs N).map φ=C N.scalar*(G.map f).b := by
    have eq:=congrArg (fun P:SeedClosure[X][X]=> -(P.coeff 0)) N.eq
    simpa [K1_14_3.fibreRow,K1_14_1.jetConstant,Pade.Row.polynomial,coeff_C_mul,rhs] using eq
  obtain ⟨l,w,bez⟩:=((G.primitive_map f).mpr gp).2
  have cop:IsCoprime ((den N).map φ) ((rhs N).map φ) := by
    refine ⟨C N.scalar⁻¹*l,C N.scalar⁻¹*w,?_⟩
    rw [A,B]
    calc
      _ = (C N.scalar⁻¹*C N.scalar)*(l*(G.map f).a+w*(G.map f).b) := by ring
      _ = 1 := by rw [bez,←C_mul,inv_mul_cancel₀ N.nonzero,map_one,one_mul]
  exact cop

theorem proper {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) :
    (den N).resultant (rhs N)≠0 := by
  have inj:Function.Injective φ:=f.injective.comp (IsFractionRing.injective Seeds SeedField)
  have nonzero:=Polynomial.resultant_ne_zero _ _ (coprime_generic N gp)
  intro zero
  apply nonzero
  rw [natDegree_map_eq_of_injective inj,natDegree_map_eq_of_injective inj,
    Polynomial.resultant_map_map,zero,map_zero]

/-- Count the actual labels at which the differential denominator vanishes
identically in physical X. The mixed axis price uses the Frobenius curve
only once. -/
theorem singular_count {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (width:Fin 2→ℕ)
    (axes:∀ j i z,((N.poly.coeff j).coeff i).degreeOf z≤width z)
    (small:(2*G.graphDegree-1)*width 0<K1.p) (T:Finset K1.K) (label:K1.K→K1.K)
    (inject:Set.InjOn label (T:Set K1.K)) (y:K1.K→FX)
    (zero:∀ γ∈T,(den N).eval₂ (graphEval (label γ)) (y γ)=0)
    (law:∀ γ∈T,(rhs N).eval₂ (graphEval (label γ)) (y γ)=0) :
    T.card≤(2*G.graphDegree-1)*(width 0+K1.p*width 1) := by
  classical
  let e:=2*G.graphDegree-1
  let z (γ:K1.K):=seedEmbedding (label γ)
  let marks:=T.image z
  have inj:Set.InjOn z (T:Set K1.K):=fun _ hx _ hy eq=>inject hx hy (seedEmbedding.injective eq)
  have size:marks.card=T.card:=Finset.card_image_iff.mpr inj
  have capA (i:ℕ) (j:Fin 2):((den N).coeff i).degreeOf j≤width j:=axes 1 i j
  have capB (i:ℕ) (j:Fin 2):((rhs N).coeff i).degreeOf j≤width j:=by
    simpa [rhs,coeff_neg] using axes 0 i j
  obtain ⟨ac,bc⟩:=NativeGraphMarks.equation_degrees N gp
  have pos:0<G.graphDegree:=by unfold Pade.Row.graphDegree;omega
  have combined:(den N).natDegree+(rhs N).natDegree≤e:=by dsimp only [den,rhs,e];omega
  have sumCap (j:Fin 2):(rhs N).natDegree*width j+(den N).natDegree*width j≤e*width j:=by
    rw [←Nat.add_mul,Nat.add_comm];exact Nat.mul_le_mul_right _ combined
  rw [←size]
  by_cases ord:(den N).natDegree≠0 ∨ (rhs N).natDegree≠0
  · have count:=Lower6960.ThirdPole.count_common K1.p (by decide) (den N) (rhs N)
      (width 0) (width 1) (width 0) (width 1) (fun i=>⟨capA i 0,capA i 1⟩)
      (fun i=>⟨capB i 0,capB i 1⟩) ord (proper N gp) ((sumCap 0).trans_lt small) marks (by
        rintro _ hx;obtain ⟨γ,mem,rfl⟩:=mem_image.mp hx
        refine ⟨y γ,?_,?_⟩
        · rw [eval_map];exact zero γ mem
        · rw [eval_map];exact law γ mem)
    exact count.trans ((Nat.add_le_add (sumCap 0) (Nat.mul_le_mul_left K1.p (sumCap 1))).trans_eq (by dsimp [e];ring))
  · have d0:(den N).natDegree=0:=by tauto
    let C₀:Seeds:=(den N).coeff 0
    have cne:C₀≠0:=by
      change (den N).coeff 0≠0;rw [←d0,coeff_natDegree];exact leadingCoeff_ne_zero.mpr (den_ne N gp)
    have ep:1≤e:=by dsimp [e];omega
    have short:width 0≤e*width 0:=by simpa only [one_mul] using Nat.mul_le_mul_right (width 0) ep
    have count:=K1_10.frobenius_coefficient_exception_count K1.p (width 0) (width 1) (by decide) C₀ cne
      (capA 0 0) (short.trans_lt small) (capA 0 1) marks (by
        rintro _ hx;obtain ⟨γ,mem,rfl⟩:=mem_image.mp hx
        have eq:den N=C C₀:=eq_C_of_natDegree_eq_zero d0
        have root:=zero γ mem
        rw [eq,eval₂_C] at root
        exact root)
    exact count.trans (by simpa only [one_mul] using Nat.mul_le_mul_right (width 0+K1.p*width 1) ep)

#print axioms proper
#print axioms singular_count
end
end Research6966.NativeGraphExceptional

end Merged6967_R6966ProofNativeGraphExceptional

section Merged6967_R6966ProofPhysicalChartAtMark
set_option Elab.async false


set_option Elab.async false

namespace Research6966.PhysicalChartAtMark
open Finset Polynomial
open K1_14 (L FX Seeds Jet)
open K1_14_1 (SeedPoly PoleData CRTLift poleProduct rawBlock crtPolynomial)
open K1_14_1_2 (RegularRing regularSeeds specialize includeGeneric includeGeneric_injective localLift map_localLift specialize_localLift)
open PhysicalPrimitiveCoeffs (R phys rawCoeff)
open K1_14_1_4 (centerBase evalRaw)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 750000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false

private abbrev B:=K1_14_3.SeedField
abbrev AtSeeds (t:Fin 2→L) := (RegularRing t)[X]

instance (t:Fin 2→L) : IsDomain (RegularRing t) :=
  (includeGeneric_injective t).isDomain (includeGeneric t)

def embed (t:Fin 2→L) : R→+*AtSeeds t := mapRingHom (algebraMap SeedPoly (RegularRing t))
def liftGeneric (t:Fin 2→L) : AtSeeds t→+*K1_14_1.SeedField[X] := mapRingHom (includeGeneric t)
def atSeeds (t:Fin 2→L) : AtSeeds t→+*L[X] := mapRingHom (specialize t)
def H {h} (D:PoleData h) (t:Fin 2→L) : AtSeeds t := embed t (phys (poleProduct D))

theorem generic_comp (t:Fin 2→L) : (liftGeneric t).comp (embed t)=rawCoeff := by
  have base:(includeGeneric t).comp (algebraMap SeedPoly (RegularRing t))=algebraMap SeedPoly K1_14_1.SeedField :=
    IsLocalization.lift_comp _
  apply RingHom.ext
  intro P
  change (P.map _).map _=P.map _
  rw [Polynomial.map_map,base]

theorem actual_comp (t:Fin 2→L) : (atSeeds t).comp (embed t)=mapRingHom (MvPolynomial.eval t) := by
  have base:(specialize t).comp (algebraMap SeedPoly (RegularRing t))=MvPolynomial.eval t:=IsLocalization.lift_comp _
  apply RingHom.ext
  intro P
  change (P.map _).map _=P.map _
  rw [Polynomial.map_map,base]

theorem generic_H {h} (D:PoleData h) (t:Fin 2→L) : liftGeneric t (H D t)=rawBlock D := by
  rw [H,←RingHom.comp_apply,generic_comp]
  change ((poleProduct D).map MvPolynomial.C).map _=_
  rw [Polynomial.map_map];rfl

theorem actual_H {h} (D:PoleData h) (t:Fin 2→L) : atSeeds t (H D t)=poleProduct D := by
  rw [H,←RingHom.comp_apply,actual_comp]
  change ((poleProduct D).map MvPolynomial.C).map (MvPolynomial.eval t)=_
  have eq:(MvPolynomial.eval t).comp (MvPolynomial.C:L→+*SeedPoly)=RingHom.id L:=RingHom.ext (fun _=>MvPolynomial.eval_C _)
  rw [Polynomial.map_map,eq,Polynomial.map_id]

theorem Hnz {h} (D:PoleData h) (t:Fin 2→L) : H D t≠0 := by
  intro z
  have n:= (K1_14_1_4.rawBlock_monic D).ne_zero
  exact n ((generic_H D t).symm.trans (z ▸ map_zero _))

abbrev Chart {h} (D:PoleData h) (t:Fin 2→L) := Localization.Away (H D t)
def into {h} (D:PoleData h) (t:Fin 2→L) : R→+*Chart D t:=(algebraMap (AtSeeds t) (Chart D t)).comp (embed t)
def direct : R→+*B:=(algebraMap Seeds B).comp centerBase

theorem direct_eq : evalRaw.comp rawCoeff=direct := K1_14_1_4.evalRaw_generic
theorem direct_injective : Function.Injective direct :=
  (IsFractionRing.injective Seeds B).comp PadeRawField.center_injective

private theorem regular_H {h} (D:PoleData h) (t:Fin 2→L) :
    Submonoid.powers (H D t)≤nonZeroDivisors (AtSeeds t) := by
  intro x hx
  obtain ⟨n,rfl⟩:=hx
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n (Hnz D t))

instance {h} (D:PoleData h) (t:Fin 2→L) : IsDomain (Chart D t) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (Chart D t) (regular_H D t)

private def toBase (t:Fin 2→L) : AtSeeds t→+*B:=evalRaw.comp (liftGeneric t)
private theorem toBase_inj (t:Fin 2→L) : Function.Injective (toBase t) :=
  PadeRawField.eval_injective.comp (map_injective _ (includeGeneric_injective t))

def genericMap {h} (D:PoleData h) (t:Fin 2→L) : Chart D t→+*B :=
  IsLocalization.Away.lift (H D t) (g:=toBase t)
    (((map_ne_zero_iff _ (toBase_inj t)).mpr (Hnz D t)).isUnit)

theorem generic_atBase {h} (D:PoleData h) (t:Fin 2→L) (x:AtSeeds t) :
    genericMap D t (algebraMap _ _ x)=toBase t x := IsLocalization.Away.lift_eq _ _ _

theorem generic_atSource {h} (D:PoleData h) (t:Fin 2→L) :
    (genericMap D t).comp (into D t)=direct := by
  apply RingHom.ext
  intro x
  change genericMap D t (algebraMap _ _ (embed t x))=_
  rw [generic_atBase]
  exact (RingHom.congr_fun (congrArg (fun g=>evalRaw.comp g) (generic_comp t)) x).trans (RingHom.congr_fun direct_eq x)

theorem into_injective {h} (D:PoleData h) (t:Fin 2→L) : Function.Injective (into D t) := by
  intro x y id
  exact direct_injective ((RingHom.congr_fun (generic_atSource D t) x).symm.trans
    ((congrArg (genericMap D t) id).trans (RingHom.congr_fun (generic_atSource D t) y)))

theorem generic_injective {h} (D:PoleData h) (t:Fin 2→L) : Function.Injective (genericMap D t) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (H D t)) _).mpr
  intro x y
  rw [generic_atBase,generic_atBase,(toBase_inj t).eq_iff,
    (IsLocalization.injective (Chart D t) (regular_H D t)).eq_iff]

theorem into_clears {h} (D:PoleData h) (t:Fin 2→L) : GlobalPrimitive.Clears (into D t) :=
  GlobalPrimitive.clear_comp _ _ (GlobalPrimitive.lift_clear _ (GlobalPrimitive.clear_localization (regularSeeds t)))
    (GlobalPrimitive.clear_localization (Submonoid.powers (H D t)))

theorem generic_clears {h} (D:PoleData h) (t:Fin 2→L) : GlobalPrimitive.Clears (genericMap D t) := by
  have all:GlobalPrimitive.Clears direct:=GlobalPrimitive.clear_comp _ _ PhysicalPrimitiveCoeffs.native_clears
    (GlobalPrimitive.clear_localization (nonZeroDivisors Seeds))
  intro x
  obtain ⟨a,b,unit,id⟩:=all x
  refine ⟨into D t a,into D t b,?_,?_⟩
  · exact (RingHom.congr_fun (generic_atSource D t) b) ▸ unit
  · exact (RingHom.congr_fun (generic_atSource D t) a).trans
      (id.trans (congrArg (·*x) (RingHom.congr_fun (generic_atSource D t) b).symm))

/-- The same localized chart specializes at every regular code node. -/
def atNode {h} (D:PoleData h) (t:Fin 2→L) (x:L) (nx:(poleProduct D).eval x≠0) : Chart D t→+*L :=
  IsLocalization.Away.lift (H D t) (g:=(evalRingHom x).comp (atSeeds t)) (by
    change IsUnit ((atSeeds t (H D t)).eval x);rw [actual_H];exact nx.isUnit)

/-- It also specializes to the entire rational physical line of each mark. -/
def atLine {h} (D:PoleData h) (t:Fin 2→L) : Chart D t→+*FX :=
  IsLocalization.Away.lift (H D t) (g:=(algebraMap L[X] FX).comp (atSeeds t)) (by
    change IsUnit (algebraMap L[X] FX (atSeeds t (H D t)))
    rw [actual_H]
    exact ((map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).mpr ((D.monic 0).mul (D.monic 1)).ne_zero).isUnit)

#print axioms generic_atSource
#print axioms generic_clears
end
end Research6966.PhysicalChartAtMark

end Merged6967_R6966ProofPhysicalChartAtMark

section Merged6967_R6966ProofPhysicalSeparant
set_option Elab.async false


set_option Elab.async false

namespace Research6966.PhysicalSeparant
open Polynomial
open K1_14_1 (jetConstant)
open K1_14_1_4 (doubleMap)
open RegularPhysicalChart (transform)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 450000
variable {R S:Type*} [CommRing R] [CommRing S]

def value (f:R→+*S) (y v:S) : R[X][X]→+*S:=eval₂RingHom (eval₂RingHom f y) v

private theorem natural (f:R→+*S) (a b u d:R) (y v:S) :
    (value f y v).comp (transform a b u d)=value f (f a*y+f b) (f a*v+f u*y+f d) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro c;simp [value,transform,K1_14_1_4.substitute,jetConstant]
    · simp [value,transform,K1_14_1_4.substitute,jetConstant,RegularPhysicalChart.yVar,RegularPhysicalChart.vVar]
  · simp [value,transform,K1_14_1_4.substitute,jetConstant,RegularPhysicalChart.yVar,RegularPhysicalChart.vVar]

private theorem linear_value (f:R→+*S) (y v:S) (P:R[X][X]) (deg:P.natDegree≤1) :
    value f y v P=(P.coeff 1).eval₂ f y*v+(P.coeff 0).eval₂ f y := by
  have eq:=congrArg (value f y v) (eq_X_add_C_of_natDegree_le_one deg)
  simpa only [value,coe_eval₂RingHom,eval₂_add,eval₂_mul,eval₂_C,eval₂_X] using eq

theorem compare (f:R→+*S) (a b u d c:R) (P Q:R[X][X]) (p:P.natDegree≤1) (q:Q.natDegree≤1)
    (eq:transform a b u d P=jetConstant c*Q) (y:S) :
    f a*(P.coeff 1).eval₂ f (f a*y+f b)=f c*(Q.coeff 1).eval₂ f y := by
  have atV (v:S) : (P.coeff 1).eval₂ f (f a*y+f b)*(f a*v+f u*y+f d)+(P.coeff 0).eval₂ f (f a*y+f b)=
      f c*((Q.coeff 1).eval₂ f y*v+(Q.coeff 0).eval₂ f y) := by
    rw [←linear_value f _ _ P p,←linear_value f _ _ Q q]
    have input:=RingHom.congr_fun (natural f a b u d y v) P
    rw [←input,RingHom.comp_apply,eq,map_mul]
    simp [value,jetConstant]
  have one:=atV 1;have zero:=atV 0
  linear_combination one-zero

theorem nonzero_iff [IsDomain S] (f:R→+*S) (a b u d c:R) (ua:IsUnit a) (uc:IsUnit c)
    (P Q:R[X][X]) (p:P.natDegree≤1) (q:Q.natDegree≤1)
    (eq:transform a b u d P=jetConstant c*Q) (y:S) :
    (Q.coeff 1).eval₂ f y≠0 ↔ (P.coeff 1).eval₂ f (f a*y+f b)≠0 := by
  have both:=compare f a b u d c P Q p q eq y
  have left: f a≠0:=(ua.map f).ne_zero
  have right:f c≠0:=(uc.map f).ne_zero
  have identical: (f c*(Q.coeff 1).eval₂ f y=0) ↔
      (f a*(P.coeff 1).eval₂ f (f a*y+f b)=0) := by rw [both]
  exact not_congr (by simpa only [mul_eq_zero,or_iff_right right,or_iff_right left] using identical)

#print axioms nonzero_iff
end
end Research6966.PhysicalSeparant

end Merged6967_R6966ProofPhysicalSeparant
