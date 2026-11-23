import ProximityPrize.SubmissionLower.Z1LucWb
import ProximityPrize.SubmissionLower.ZpYo3sb
import ProximityPrize.SubmissionLower.ZPuXYRc
import ProximityPrize.SubmissionLower.ZL8vffb
import ProximityPrize.SubmissionLower.Z7iuxgb
import ProximityPrize.SubmissionLower.ZMwIPwd
import ProximityPrize.SubmissionLower.ZqKag5d
import ProximityPrize.SubmissionLower.ZnGdvBe
set_option Elab.async false
open _root_ renaming Finset → zJe, Nat.cast_le → z9h, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.pos_of_ne_zero → zOl
set_option maxHeartbeats 1000000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qXdgDRd
noncomputable section
open Polynomial Finset
open P5 (K p blockLength)
open P5_7 (OneSeedEquation atNative NativeSeedBound farAgreement)
open P5_7_7
open private all_factors from ProximityPrize.SubmissionLower.ZPSk6xb
private theorem d5P {D e rate w U z S} (guard :Guards D e rate)
    (hD:D ≤P6.dw) (hep:e<p) (hloss :gap D ≤2*P5_7.gap D)
    (node :NodeBound e) (poles :PoleBound (width D) e)
    (M:StrongMarks D w U z S) (J:DualWord D w U S) (hU:U.Nonempty)
    (f :OneSeedEquation) (hf :Irreducible f) (hfe :f.natDegree≤e)
    (T:zJe K) (hT:T⊆U) (hr : ∀ γ∈T,atNative f (z γ) (S γ)=0) :
    gap D *T.card≤gap D *f.natDegree+rate*gY f := by
  obtain ⟨hrate,hx⟩:=guard
  have m:=M.restrict hT
  by_cases h0:f.natDegree=0
  · have hc:=degree_zero_count m.Kw hf.ne_zero h0 hr
    exact (Nat.mul_le_mul hrate hc).trans (Nat.le_add_left _ _)
  by_cases hz :gY f=0
  · have hs :=(bv9 f 0).mp hz.le
    exact (zBI _ (seed_zero_count m.sections hf.ne_zero hs hr)).trans
      (Nat.le_add_right _ _)
  have hh:0<gY f :=zOl hz
  obtain ⟨x,hok,hprice⟩:=hx f.natDegree (zOl h0) hfe
  apply LE.le.trans ?_ (Nat.le_add_left _ _)
  by_cases hlinear :f.natDegree=1
  · have hn:linearPrice≤ rate := by rwa [jX,ite_eq_left hlinear] at hprice
    have hc:=linear_count m.toUJ hh ((Nat.sub_le _ _).trans (by decide :farAgreement≤blockLength))
      (q1tes5a.proof D w T z S m.toUJ f hlinear hr)
    calc
      gap D *T.card≤(2*P5_7.gap D)*T.card:=Nat.mul_le_mul_right _ hloss
      _=2*(P5_7.gap D*T.card) := by rw [Nat.mul_assoc]
      _≤linearPrice*gY f := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hc
      _≤_:=Nat.mul_le_mul_right _ hn
  have h₂:2≤f.natDegree := by omega
  have hok :=hok.resolve_left hlinear
  rw [jX,ite_eq_right hlinear] at hprice
  obtain ⟨hlo,hhi⟩:=max_le_iff.mp hprice
  obtain ⟨F,hF⟩:=qwGrtCa.proof J f hf h₂ T z hT hr
  obtain ⟨hw,hdegree⟩:=chart_bounds J M hU
  let u:=J.u₀-shift
  let s :=J.u₁-J.u₀
  by_cases hlow:BelowAt F.F u s x.W
  · exact (low_count node poles J M hD f F x h₂ hfe (hfe.trans_lt hep) hh hw rfl hok hlow hT hF).trans
      (ztf _ hlo)
  obtain ⟨a,H,G,B,hrel,hdG,hdB,hs,hN,hcop⟩ :=
    aIF F.F x F.irred F.generic_irred F.jU h₂ hh F.raw_height hw hok hlow
  have hGr : ∀ γ∈T,nativeEval (z γ) (dualValue J γ) (embed G)=0:= by
    intro γ hγ
    obtain ⟨hQ,hP⟩:=hdegree γ (hT hγ)
    exact transfer J (by omega) a hrel hdG hdB hN (hT hγ) (z γ) hQ hP (hF γ hγ)
  have hG: (embed G).natDegree≤f.natDegree+x.g:=natDegree_map_le.trans hdG
  have he : (embed F.F).natDegree=f.natDegree := by
    unfold embed
    rw [coe_mapRingHom,natDegree_map_eq_of_injective
      (Polynomial.map_injective _ (IsFractionRing.injective _ _)),F.jU]
  have hc:=ePy ((bv9 _ _).mp F.height.le) hs
    (he.symm ▸ zOl h0) hcop m.Kw hF hGr
  rw [he] at hc
  have hc' : T.card≤highRate f.natDegree x*gY f := by
    apply hc.trans
    apply (Nat.add_le_add_left (ztf _ hG) _).trans_eq
    unfold highRate
    ring
  calc
    gap D *T.card≤gap D *(highRate f.natDegree x*gY f) :=zBI _ hc'
    _=(highRate f.natDegree x*gap D)*gY f := by ring
    _≤_:=ztf _ hhi
theorem native_count {D e bw H rate w T z S} (guard :Guards D e rate)
    (hD:D <P6.dw) (hshift:shift≤D) (hep:e<p)
    (hloss :gap D ≤2*P5_7.gap D) (hfee :0<bw)
    (hbudget:gap D*e+rate*H≤gap D*(bw-1))
    (node :NodeBound e) (poles :PoleBound (width D) e) (M:StrongMarks D w T z S)
    (f :OneSeedEquation) (hf :f≠0) (he :f.natDegree≤e) (hH :NativeSeedBound f H)
    (hr : ∀ γ∈T,atNative f (z γ) (S γ)=0) :T.card≤bw:= by
  classical
  rcases q20JTGa.proof D w T z S M.toUJ with hsmall | ⟨U,hU,hcard,⟨J⟩⟩
  · exact hsmall.trans hfee
  by_cases hu:U.Nonempty
  · have heq :P5_7.gap (D-shift)=gap D:= by
      have hs :farAgreement+shift=P6.dw:= by decide
      unfold P5_7.gap gap
      omega
    have hsingle :=d5P guard hD.le hep hloss node poles (M.restrict hU) J hu
    have hb:=all_factors (D:=D-shift) (by simpa only [heq] using hsingle)
      f hf he U (Subset.refl U) (fun γ hγ=>hr γ (hU hγ))
    rw [heq] at hb
    have hmul :=hb.trans ((Nat.add_le_add (zBI (gap D) he)
      (zBI rate ((bv9 f H).mpr hH))).trans hbudget)
    have huc:=Nat.le_of_mul_le_mul_left hmul (Nat.sub_pos_of_lt hD)
    exact hcard.trans (by omega)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hu,card_empty,zero_add] at hcard
    exact hcard.trans hfee
end
end qXdgDRd
end
section
set_option autoImplicit true
namespace qcuQADa
open P6_7 (RectTail)
open P6_7_2 (Bs)
open qXdgDRd (gap)
abbrev degree (b:RectTail) :=131071+(Bs b).hi
abbrev Ya (b:RectTail) (e a rate :ℕ) :Prop :=
  gap (degree b)*e+rate*(a+P6.p*a)≤gap (degree b)*((Bs b).retainedFee-1)
end qcuQADa
end
section
set_option autoImplicit true
namespace q4Pefpa
noncomputable section
open Polynomial
open cu (L)
open qQ9yWTb (Raw)
end
end q4Pefpa
end
section
set_option autoImplicit true
namespace qy95ATd
noncomputable section
open Polynomial
open P6 (K p blockLength)
open P6_7_3 (Input degree retainedFee)
open qQ9yWTb (Raw embed height Moving Witness highDigits highRate base)
open P5_7_7 (DualWord dualValue)
open cu (L qD)
abbrev G:=qXdgDRd.gap degree
abbrev width :=qXdgDRd.width degree
abbrev WordChart (x :Input) (T:zJe K) :=DualWord degree x.M.word T x.F.scalar
abbrev left {x :Input} {U:zJe K} (J:WordChart x U) :=J.u₀-qXdgDRd.shift
abbrev right {x :Input} {U:zJe K} (J:WordChart x U) :=left J+(J.u₁-J.u₀)
abbrev weight {x :Input} {U:zJe K} (J:WordChart x U) :=q4Pefpa.load (left J) (right J)
def root {x :Input} {U:zJe K} (J:WordChart x U) (f :Raw) (γ:K) :Prop :=
  (embed f).eval₂ (qD (x.M.label γ)) (dualValue J γ)=0
def modulus (w:Witness) :=w.W+1+w.j*width
def polar (e W:ℕ) :=(6*e-2)*W-(3*e*e-2*e+1)*width
def lowRate (e W:ℕ) :=
  (7+6*e)*G+2*e*blockLength+polar e W+(2*e-1)
def B (e W v :ℕ) :ℚ:=((lowRate e W:ℚ)*v)/G+base e
def Good (e u:ℕ) (w:Witness) :Prop :=
  let E :=e+w.g
  let L:=width
  3≤e∧e<p∧0< u∧u<p∧0<w.cz∧0<w.ct∧w.j≤w.g ∧
  e*L≤w.W∧E*L< modulus w ∧
  ((w.cz+1)*u+1)*((w.ct+1)*u+1)*(L*E*(E+1)/2+L*w.j*(w.j+1)/2) <
    (w.g+1)*(w.cz*u+1)*(w.ct*u+1)*modulus w ∧
  e*(e-1)*L≤(2*e-2)*w.W∧(2*e-2)*w.W-e*(e-1)*L<p ∧
  (3*e*e-2*e+1)*L≤(6*e-2)*w.W∧highDigits e w.cz w.g*u<p
def gu (e u:ℕ) (w:Witness) :Prop :=
  let d:=3*G^2
  let b:=base e*G
  let c:=lowRate e w.W
  d*(highRate e w*u+(e+1))+10*b^2≤d*retainedFee ∧
  d*(e+1)+10*(c*u+b)^2≤d*retainedFee
def site (x :Input) (γ:K) :Fin 2→L :=
  let z :=algebraMap K L (x.M.label γ)
  ![z,z^p]
structure SplitData (x :Input) (T:zJe K) (e u W:ℕ) where
  U:zJe K
  sub:U⊆T
  bY:WordChart x U
  high:zJe K
  low:zJe K
  high_sub:high⊆U
  low_sub:low⊆U
  card:T.card≤high.card+low.card+(e+1)
  F:Raw
  Q:Raw
  F_moving:Moving F
  Q_moving:Moving Q
  F_degree :F.natDegree≤e
  Q_degree :Q.natDegree≤e
  seed :height F+height Q≤u
  high_weight : ∀ q:Raw,Irreducible q→q∣F→W<weight bY q
  low_weight : ∀ q:Raw,Irreducible q→q∣Q→weight bY q≤W
  high_root : ∀ γ∈high,root bY F γ
  low_root : ∀ γ∈low,root bY Q γ
end
end qy95ATd
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace q6nKpZc
noncomputable section
open Finset Polynomial
open scoped BigOperators Classical
open P6 (K p jG)
open P6_7_4 (bkU)
open P5_7_2 (A fO row)
open q7F2qKe (cL aSz origins stops projectionCap pointFee globalCap originFreeCap stopPrice factorBill dot_mass)
open cu (Jet)
open gT (Ambient)
open pI (dual acW pN)
open TD (J2 FP cK6)
open ac6.Bridge (aQF cbq)
def c1 :Prop :=
  ∀ (b:fO),2≤b.val → ∀ u del (M:jG u del) Γ (F:P1.bje A M Γ),
    Input b M F→Nonempty (TopPair M F b)
def c2 :Prop :=
  ∀ (b:fO),2≤b.val → ∀ u del (M:jG u del) Γ (F:P1.bje A M Γ)
    (x :Input b M F),TopPair M F b→FixedTariff F b→Nonempty (aAT F b x)
def c3:Prop :=
  ∀ (b:fO),2≤b.val → ∀ u del (M:jG u del) Γ (F:P1.bje A M Γ)
    (x :Input b M F) (C:aAT F b x),Nonempty (Timeline C)
def c4 :Prop :=
  ∀ (b:fO),2≤b.val → ∀ u del (M:jG u del) Γ (F:P1.bje A M Γ),
    Input b M F → ∀ dm a h:ℚ,aSz b dm a h → ∀ C:acW,
      (C.cost 0:ℚ)≤dm→C.cost 0<p →
      ((aHl F C).card:ℚ)≤a*C.cost 0+h*C.cost 1+C.cost 0
def c5:Prop := ∀ (b:fO),2≤b.val→Nonempty (cL b)
open private card_union_cast card_biUnion_cast le_ceil from ProximityPrize.SubmissionLower.Z77J3Nc
section
variable {b u del M Γ F} {x : @Input b u del M Γ F} {C:aAT F b x}
variable (R:Timeline C)
private def PN (o:ℕ) (f :Jet) (j:ℕ) (I:Ideal Ambient) :zJe K :=
  if j=0 then Γ.filter (I0 F I) else aHl F (R.cuts o f j I)
private def lossPaid :zJe K :=
  (origins b).biUnion fun o=>(C.factors o).biUnion fun f =>
    C.line o f∪(stops b).biUnion fun j=>(R.stopped o f j).biUnion (PN R o f j)
private def pointPaid :zJe K :=
  (origins b).biUnion fun o=>(C.factors o).biUnion fun f =>
    ((stops b).filter (0 < ·)).biUnion fun j=>(R.stopped o f j).biUnion fun I =>
      (R.cuts o f j I).direct
private theorem points_paid : (pointPaid R).card≤pointFee b:= by
  unfold pointPaid
  exact card_biUnion_le.trans ((sum_le_sum fun _ _=>card_biUnion_le.trans
    (sum_le_sum fun _ _=>card_biUnion_le.trans (sum_le_sum fun _ _=>card_biUnion_le))).trans
    R.total_points)
private theorem individual_projection {o f j I} (ho:o∈origins b) (hf :f∈C.factors o)
    (hj:j∈stops b) (hj0:0<j) (hI:I∈R.stopped o f j) :
    ((R.cuts o f j I).cost 0:ℚ)≤projectionCap b:= by
  let cost i g k Q:=((R.cuts i g k Q).cost 0:ℚ)
  let s :=(stops b).filter (0 < ·)
  have nn i g k Q:0≤ cost i g k Q:=Nat.cast_nonneg _
  calc
    _ ≤ ∑ Q∈R.stopped o f j,cost o f j Q:=single_le_sum (fun Q _=>nn o f j Q) hI
    _ ≤ ∑ k∈s,∑ Q∈R.stopped o f k,cost o f k Q :=
      single_le_sum (fun k _=>sum_nonneg fun Q _=>nn o f k Q) (mem_filter.mpr ⟨hj,hj0⟩)
    _ ≤ ∑ g∈C.factors o,∑ k∈s,∑ Q∈R.stopped o g k,cost o g k Q :=
      single_le_sum (fun g _=>sum_nonneg fun k _=>sum_nonneg fun Q _=>nn o g k Q) hf
    _ ≤ ∑ i∈origins b,∑ g∈C.factors i,∑ k∈s,∑ Q∈R.stopped i g k,cost i g k Q :=
      single_le_sum (fun i _=>sum_nonneg fun g _=>sum_nonneg fun k _ =>
        sum_nonneg fun Q _=>nn i g k Q) ho
    _≤_:=R.total_projection
private def rounding (o:ℕ) (f :Jet) (j:ℕ) (I:Ideal Ambient) :ℚ :=
  if 0<j then (R.cuts o f j I).cost 0 else 0
private theorem cell_paid (hb:2≤b.val) (hcurve :c4) (D:cL b)
    {o f j I} (ho:o∈origins b) (hf :f∈C.factors o)
    (hj:j∈stops b) (hI:I∈R.stopped o f j) :
    ((PN R o f j I).card:ℚ)≤FP (stopPrice b D.a D.h o j) (fun k=>pN I k) +
      rounding R o f j I:= by
  have htest :=R.stopped_at o ho f hf j hj I hI
  have hind:=R.individual o ho f hf j hj I hI
  by_cases hz :j=0
  · subst j
    have ha :=(C.DN o ho f hf I htest.1).1
    have hbad : ¬ dual I:= by simpa [Pass] using htest.2.1
    simpa [PN,stopPrice,rounding] using rank_tariff F x.vo I ha hbad hind
  · have hj0:=zOl hz
    let Q:=R.cuts o f j I
    have hrate :=D.bgt o ho j hj hj0
    have hd:=individual_projection R ho hf hj hj0 hI
    have hc:=R.cut_cost o ho f hf j hj hj0 I hI
    have hbound:=(le_min hd (hc 0)).trans (D.individual_bound o ho j hj hj0 _ hind)
    have hchar :Q.cost 0<p:=(Nat.cast_lt (α:=ℚ)).mp (hd.trans_lt D.projection_small)
    simp only [PN,ite_eq_right hz,stopPrice,rounding,ite_eq_left hj0,← cK6]
    exact (hcurve b hb u del M Γ F x _ _ _ hrate Q hbound hchar).trans
      (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hc 0) (hrate.1.trans hrate.2.1))
        (mul_le_mul_of_nonneg_left (hc 1) hrate.2.2.2.1)) le_rfl)
private theorem loss_paid (hb:2≤b.val) (hcurve :c4) (D:cL b) :
    ((lossPaid R).card:ℚ) ≤
      (∑ i∈stops b,FP (D.global i) (globalCap b i)) +
      (∑ o∈origins b,FP (D.free o) (originFreeCap b o)) +
      factorBill b D.residual+projectionCap b:= by
  let Ya o f j:=FP (stopPrice b D.a D.h o j) (J2 (R.stopped o f j))
  let rem o f j := ∑ I∈R.stopped o f j,rounding R o f j I
  have hc o (ho:o∈origins b) f (hf :f∈C.factors o) j (hj:j∈stops b) :
      (((R.stopped o f j).biUnion (PN R o f j)).card:ℚ)≤Ya o f j+rem o f j:= by
    refine (card_biUnion_cast _ _).trans ((sum_le_sum fun I hI =>
      cell_paid R hb hcurve D ho hf hj hI).trans_eq ?_)
    rw [sum_add_distrib,dot_mass]
  have hround : (∑ o∈origins b,∑ f∈C.factors o,∑ j∈stops b,rem o f j)≤projectionCap b:= by
    simpa only [rem,rounding,sum_ite_irrel,sum_const_zero,sum_filter] using R.total_projection
  calc
    _ ≤ ∑ o∈origins b,∑ f∈C.factors o,((C.line o f).card+(∑ j∈stops b,(Ya o f j+rem o f j))) := by
      exact (card_biUnion_cast _ _).trans (sum_le_sum fun o ho =>
        (card_biUnion_cast _ _).trans (sum_le_sum fun f hf=>(card_union_cast _ _).trans
          (add_le_add le_rfl ((card_biUnion_cast _ _).trans (sum_le_sum fun j hj=>hc o ho f hf j hj)))))
    _=(∑ o∈origins b,∑ f∈C.factors o,((∑ j∈stops b,Ya o f j)+(C.line o f).card)) +
        ∑ o∈origins b,∑ f∈C.factors o,∑ j∈stops b,rem o f j:= by
      simp only [sum_add_distrib]
      ring
    _≤_:=add_le_add (weak_dual R D) hround
private def keptSurfaces :zJe qQ.zI :=
  (origins b).attach.biUnion fun o=>(C.factors o.1).attach.biUnion fun f =>
    (R.Bp o.1 f.1).attach.image fun I =>
      let hm:=(R.kept_at o.1 o.2 f.1 f.2 I.1 I.2).1
      aQF I.1 (C.DN o.1 o.2 f.1 f.2 I.1 hm).1.prime
include R in
private theorem inventory (hb:2≤b.val) (hcurve :c4) (D:cL b) :
    Nonempty (bkU b M F x.banks) := by
  let gH :=C.zo∪pointPaid R∪lossPaid R
  have hsize : (gH.card:ℚ)≤(row b).prefixFee := by
    have hbase :=add_le_add ((z9h (α:=ℚ)).mpr C.early_price)
      ((z9h (α:=ℚ)).mpr (points_paid R))
    have hl:=loss_paid R hb hcurve D
    have hinv :=(card_union_cast _ _).trans (add_le_add
      ((card_union_cast _ _).trans hbase) hl)
    have h:=le_ceil (projectionCap b)
    have hbudget:=D.budget
    push_cast at hbudget
    change ((C.zo∪pointPaid R∪lossPaid R).card:ℚ)≤(row b).prefixFee
    linarith only [hinv,h,hbudget]
  refine ⟨⟨gH,(z9h (α:=ℚ)).mp hsize,keptSurfaces R,?_,?_,?_⟩⟩
  · intro q hq
    obtain ⟨o,_,hf⟩:=mem_biUnion.mp hq
    obtain ⟨f,_,hI⟩:=mem_biUnion.mp hf
    obtain ⟨I,_,rfl⟩:=mem_image.mp hI
    obtain ⟨hm,hd,_⟩:=R.kept_at o.1 o.2 f.1 f.2 I.1 I.2
    exact cbq (C.DN o.1 o.2 f.1 f.2 I.1 hm).1
      (C.DN o.1 o.2 f.1 f.2 I.1 hm).2.1 hd
  · intro q hq
    obtain ⟨o,_,hf⟩:=mem_biUnion.mp hq
    obtain ⟨f,_,hI⟩:=mem_biUnion.mp hf
    obtain ⟨I,_,rfl⟩:=mem_image.mp hI
    exact (R.kept_at o.1 o.2 f.1 f.2 I.1 I.2).2.2
  · intro γ hγ
    rcases C.Eh γ hγ with h | ⟨o,ho,f,hf,hl | ⟨I,hI,hm⟩⟩
    · exact Or.inl (mem_union_left _ (mem_union_left _ h))
    · exact Or.inl (mem_union_right _ (mem_biUnion.mpr ⟨o,ho,mem_biUnion.mpr
        ⟨f,hf,mem_union_left _ hl⟩⟩))
    rcases R.exhaust o ho f hf I hI with hi | ⟨j,hj,hs⟩
    · let q:=aQF I (C.DN o ho f hf I (R.kept_at o ho f hf I hi).1).1.prime
      refine Or.inr ⟨q,?_,?_⟩
      · exact mem_biUnion.mpr ⟨⟨o,ho⟩,mem_attach _ _,mem_biUnion.mpr
          ⟨⟨f,hf⟩,mem_attach _ _,mem_image.mpr ⟨⟨I,hi⟩,mem_attach _ _,rfl⟩⟩⟩
      · intro P hP
        apply RingHom.mem_ker.mpr
        change cu.rD P (M.label γ) (F.scalar γ)=0
        rw [← gT.aNB]
        exact RingHom.mem_ker.mp (hm hP)
    · have pay_loss (hc:γ∈PN R o f j I) :γ∈gH :=
        mem_union_right _ (mem_biUnion.mpr ⟨o,ho,mem_biUnion.mpr
          ⟨f,hf,mem_union_right _ (mem_biUnion.mpr ⟨j,hj,mem_biUnion.mpr ⟨I,hs,hc⟩⟩)⟩⟩)
      by_cases hz :j=0
      · exact Or.inl (pay_loss (by simp [PN,hz,hγ,hm]))
      · have hp:=zOl hz
        rcases R.cut_cover o ho f hf j hj hp I hs γ hγ hm with h | h
        · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_biUnion.mpr
            ⟨o,ho,mem_biUnion.mpr ⟨f,hf,mem_biUnion.mpr
              ⟨j,mem_filter.mpr ⟨hj,hp⟩,mem_biUnion.mpr ⟨I,hs,h⟩⟩⟩⟩)))
        · exact Or.inl (pay_loss (by simp [PN,hz,aHl,hγ,h]))
end
private theorem on_input (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5)
    {b u del M Γ F} (hb:2≤b.val) (x : @Input b u del M Γ F) :
    Nonempty (bkU b M F x.banks) := by
  obtain ⟨top⟩:=h1 b hb u del M Γ F x
  obtain ⟨C⟩:=h2 b hb u del M Γ F x top (@fixed_tariff b u del M Γ F x.vo)
  obtain ⟨R⟩:=h3 b hb u del M Γ F x C
  obtain ⟨receipt⟩:=h5 b hb
  exact @inventory b u del M Γ F x C R hb h4 receipt
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) :P6_7_4.c4 := by
  intro b hb u del M Γ F hw hs H bY D h0 hD1 hnode hres crt donors
  let x : @Input b u del M Γ F:=⟨hw,hs,H,bY,D,h0,hD1,hnode,hres,crt,donors⟩
  change Nonempty (bkU b M F x.banks)
  exact @on_input h1 h2 h3 h4 h5 b u del M Γ F hb x
end
end q6nKpZc
end
section
set_option autoImplicit true
namespace qStwLub
theorem proof :P6_7_6.c1 :=qcsMxUc.proof
end qStwLub
end
section
set_option autoImplicit true
namespace qCDYuIa
theorem proof :P6_7_6.c2 :=qCgnalc.proof
end qCDYuIa
end
