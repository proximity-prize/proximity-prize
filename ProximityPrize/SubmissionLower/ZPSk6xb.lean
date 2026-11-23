import ProximityPrize.SubmissionLower.ZQpU10d
import ProximityPrize.SubmissionLower.ZjZXRjd
import ProximityPrize.SubmissionLower.DT
import ProximityPrize.SubmissionLower.Z3BnLje
import ProximityPrize.SubmissionLower.ZCvigsb
set_option Elab.async false
section
set_option autoImplicit true
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace qyWKMud
noncomputable section
open Polynomial Finset
open P5 (K p blockLength)
open P5_7 (OneSeedEquation atNative NativeSeedBound NativeGuard NativeWitness WitnessOK gap numerator nativeFee)
open cu (L)
open P5_7_7
open scoped Classical
def c1 :Prop :=
  ∀ {D w U S} (J:DualWord D w U S) (f :OneSeedEquation),Irreducible f →
    2≤f.natDegree →
    ∀ (T:Finset K) (z :K→K),T⊆U →
      (∀ γ∈T,atNative f (z γ) (S γ)=0) →
      ∃ F:Changed J f,∀ γ∈T,atDual J F.F (z γ) γ=0
def c2 :Prop :=
  ∀ {D w U S} (J:DualWord D w U S) (F:Dg) (l h:ℕ)
    (x :NativeWitness),Irreducible F→ Irreducible (embed F) →
    F.natDegree=l→2≤l→0<h→(∀ i,(F.coeff i).natDegree≤h) →
    WitnessOK D l x → ¬ Jm J F x.W →
    let E :=l+x.g
    let M:=x.W+1+x.j*P5_7.normalWidth D
    ∃ (a :L) (H G B:Dg),
      H*F=G+C (C (((Polynomial.X:L[X]) - C a)^M))*B ∧
      G.natDegree≤E∧B.natDegree≤E ∧
      NativeSeedBound (embed G) ((x.c+1)*h) ∧
      P5_7_7R.atm G E J.u₀ (J.u₁-J.u₀) M ∧
      IsCoprime (ek (embed F)) (ek (embed G))
open qGnV2ac in
open P5_7 (normalWidth) in
private theorem variation (node :qGnV2ac.c1) (poles :qGnV2ac.c2)
    {D w U z S} (J:DualWord D w U S) (M:UJ D w U z S)
    (f :OneSeedEquation) (F:Changed J f) (x :NativeWitness)
    (hl:2≤f.natDegree) (hp:f.natDegree<p) (hh:0<gY f)
    (hok :WitnessOK D f.natDegree x) (hbelow:Jm J F.F x.W)
    {T:Finset K} (ht:T⊆U) (hr : ∀ γ∈T,atDual J F.F (z γ) γ=0) :
    Nonempty (Variation J T z F.F f.natDegree (gY f) (poleRate D f.natDegree x)) := by
  let l:=f.natDegree
  let h:=gY f
  let s :=J.u₁-J.u₀
  obtain ⟨G,r,hrec,hd,hi,hgi,hg,hm⟩ :=
    compress F.F h F.irred F.generic_irred F.raw_height (raw_moving (F.height.symm ▸ hh))
  have H :EquationBounds G l h:=⟨hi,hd.trans F.jU,hl,hp,hg,hm⟩
  let z' γ:=z γ^(p^r)
  have hroot (γ:K) (hγ:γ∈T) :atDual J G (z' γ) γ=0:= by
    change atPair G (z γ^(p^r)) (J.P γ) (J.Q γ)=0
    rw [← pullback_atPair,← hrec]
    exact hr γ hγ
  obtain ⟨C,hC,hout,hseed,hP,hQ⟩ :=
    choose_sections J H hgi ht (powered_seeds r (M.Kw.mono ht)) hroot
  have hw:2*J.u₀+s=normalWidth D:= by
    have :=J.width
    have :=J.order
    dsimp only [s]
    omega
  have hok' := hok
  change WitnessOK D l x at hok'
  rw [WitnessOK,ite_eq_right (show l≠1 by change 2≤l at hl; omega)] at hok'
  obtain ⟨_,_,hW,_,_,_,hchar,_⟩:=hok'
  have hwt:HE G s (x.W-l*J.u₀) := by
    intro i j hj
    have he : (F.F.coeff i).coeff (j*(p^r))=(G.coeff i).coeff j:= by
      rw [hrec,pullback_coeff]
    have hb:=hbelow i (j*(p^r)) (he.symm ▸ hj)
    rw [he,F.jU] at hb
    change ((G.coeff i).coeff j).natDegree+l*J.u₀+i*s≤x.W at hb
    omega
  have hb:=poles G l h J.u₀ s (normalWidth D) x.W H hw hW hwt hchar C
  have hreldeg (γ:K) :pN C s γ=relativeDegree J γ:= by
    unfold pN relativeDegree s
    rw [hP,hQ]
  have hbudget :
      ∑ γ∈C.CF,max (C.B γ).natDegree ((C.A γ).natDegree-relativeDegree J γ) ≤
        poleRate D l x*h:= by
    change _≤((6*l-4)*x.W-(3*l*l-4*l+2)*normalWidth D)*h
    refine (le_of_eq ?_).trans hb
    exact sum_congr rfl fun γ _=> by rw [hreldeg]
  refine ⟨{
    reducedEquation :=G
    compression :=r
    recovered:=hrec
    good:=C.CF
    Bp:=hC
    zJ:=hout
    A:=C.A
    B:=C.B
    nonzero :=C.nonzero
    denominator :=C.pole_denominator
    reduced:=C.reduced
    simple := fun γ hγ=> by
      change atPair G.derivative (z' γ) (J.P γ) (J.Q γ)≠0
      simpa only [hseed,hP,hQ] using C.simple γ hγ
    formula := fun γ hγ=> by
      change phys (C.A γ)/phys (C.B γ)=zD G (z' γ) (J.P γ) (J.Q γ)
      simpa only [hseed,hP,hQ] using C.formula γ hγ
    node_budget := ?_
    pole_budget:=hbudget }⟩
  intro i
  have heq : (C.CF.filter fun γ => ¬ hit w S γ i∧(C.A γ).eval (base i)≠0) =
      C.CF.filter (fun γ =>
        (C.P γ).eval (base i)*J.a₀.eval (base i) =
        (C.Q γ).eval (base i)*J.a₁.eval (base i)∧(C.A γ).eval (base i)≠0) := by
    ext γ
    simp only [mem_filter,hP,hQ]
    exact and_congr_right fun hg=>and_congr (J.dual_hits γ (ht (hC hg)) i).symm Iff.rfl
  rw [heq]
  exact node G l h H C (base i) _ _ (J.target i)
private theorem restrict {D w U z S} (M:UJ D w U z S) {T:Finset K} (hT:T⊆U) :
   UJ D w T z S :=
 ⟨M.Kw.mono hT,M.sections.mono hT,fun γ hγ=>M.degree γ (hT hγ),
   fun γ hγ=>M.dw γ (hT hγ)⟩
private theorem d5P (h1 :P5_7_7.c1) (bY:qyWKMud.c1) (high:qyWKMud.c2)
    (node :qGnV2ac.c1) (poles :qGnV2ac.c2)
    {D e rate w U z S} (guard :NativeGuard D e rate)
    (M:UJ D w U z S) (J:DualWord D w U S)
    (f :OneSeedEquation) (hf :Irreducible f) (hfe :f.natDegree≤e)
    (T:Finset K) (hT:T⊆U) (hr : ∀ γ∈T,atNative f (z γ) (S γ)=0) :
    gap D *T.card≤gap D *f.natDegree+rate*gY f := by
  obtain ⟨_,hD,hA,_,_,hep,hrate,hx⟩:=guard
  have m:=restrict M hT
  by_cases h0:f.natDegree=0
  · have hc:=degree_zero_count m.Kw hf.ne_zero h0 hr
    exact (Nat.mul_le_mul hrate hc).trans (Nat.le_add_left _ _)
  by_cases hz :gY f=0
  · have hs :=(bv9 f 0).mp hz.le
    exact (Nat.mul_le_mul_left _ (seed_zero_count m.sections hf.ne_zero hs hr)).trans
      (Nat.le_add_right _ _)
  have hh:0<gY f :=Nat.pos_of_ne_zero hz
  obtain ⟨x,hok,hprice⟩:=hx f.natDegree (Nat.pos_of_ne_zero h0) hfe
  apply LE.le.trans ?_ (Nat.le_add_left _ _)
  by_cases hlinear :f.natDegree=1
  · have hn:blockLength≤ rate := by
      rwa [numerator,ite_eq_left hlinear] at hprice
    exact (linear_count m hh ((Nat.sub_le _ _).trans hA.le)
      (h1 D w T z S m f hlinear hr)).trans (Nat.mul_le_mul_right _ hn)
  have h2 :2≤f.natDegree := by omega
  have hn:f.natDegree≠1 := by omega
  have hprices :exclusions f.natDegree*gap D + nodeRate f.natDegree*blockLength +
        poleRate D f.natDegree x≤ rate∧highRate f.natDegree x*gap D ≤ rate := by
    rw [numerator,ite_eq_right hn] at hprice
    exact max_le_iff.mp hprice
  obtain ⟨F,hF⟩:=bY J f hf h2 T z hT hr
  by_cases hlow:Jm J F.F x.W
  · obtain ⟨V⟩:=variation node poles J M f F x h2 (hfe.trans_lt hep) hh hok hlow hT hF
    exact (variation_count J M hD.le hT V).trans (Nat.mul_le_mul_right _ hprices.1)
  obtain ⟨a,H,G,B,hrel,hdG,hdB,hs,hN,hcop⟩ :=
    high J F.F f.natDegree (gY f) x F.irred F.generic_irred F.jU
      h2 hh F.raw_height hok hlow
  have hGr : ∀ γ∈T,nativeEval (z γ) (dualValue J γ) (embed G)=0 :=
    fun γ hγ=>P5_7_7R.transfer J (by omega) a hrel hdG hdB hN
      (hT hγ) (z γ) (m.dw γ hγ) (hF γ hγ)
  have hG: (embed G).natDegree≤f.natDegree+x.g:=natDegree_map_le.trans hdG
  have he : (embed F.F).natDegree=f.natDegree := by
    unfold embed
    rw [coe_mapRingHom,natDegree_map_eq_of_injective
      (Polynomial.map_injective _ (IsFractionRing.injective _ _)),F.jU]
  have hc:=ePy ((bv9 _ _).mp F.height.le) hs
    (he.symm ▸ Nat.pos_of_ne_zero h0) hcop m.Kw hF hGr
  rw [he] at hc
  have hc' : T.card≤highRate f.natDegree x*gY f := by
    apply hc.trans
    apply (Nat.add_le_add_left (Nat.mul_le_mul_right _ hG) _).trans_eq
    unfold highRate
    ring
  calc
    gap D *T.card≤gap D *(highRate f.natDegree x*gY f) :=
      Nat.mul_le_mul_left _ hc'
    _=(highRate f.natDegree x*gap D)*gY f := by ring
    _≤_:=Nat.mul_le_mul_right _ hprices.2
private theorem all_factors {D e rate :ℕ} {U:Finset K} {z :K→K} {S:K→K[X]}
    (single : ∀ f :OneSeedEquation,Irreducible f→f.natDegree≤e →
      ∀ T⊆U,(∀ γ∈T,atNative f (z γ) (S γ)=0) →
        gap D *T.card≤gap D *f.natDegree+rate*gY f)
    (f :OneSeedEquation) (hf :f≠0) (he :f.natDegree≤e)
    (T:Finset K) (hT:T⊆U) (hroot : ∀ γ∈T,atNative f (z γ) (S γ)=0) :
    gap D *T.card≤gap D *f.natDegree+rate*gY f := by
  revert hf he T hT hroot
  induction f using WfDvdMonoid.induction_on_irreducible with
  | zero =>
    intro h
    exact (h rfl).elim
  | unit f hu =>
    intro _ _ T _ hr
    have hT:T = ∅ := eq_empty_iff_forall_notMem.mpr fun γ hγ =>
      (hu.map (nativeEval (z γ) (cu.kr (S γ)))).ne_zero (hr γ hγ)
    simp [hT]
  | mul a i ha hi ih =>
    intro _ he T hT hr
    let A:=T.filter fun γ=>atNative i (z γ) (S γ)=0
    let B:=T \ A
    have hA:A⊆T:=filter_subset _ _
    have hB:B⊆T:=sdiff_subset
    have hdeg:=natDegree_mul hi.ne_zero ha
    have hseed :=acG hi.ne_zero ha
    have hn:i.natDegree+a.natDegree≤e :=hdeg ▸ he
    have hRa : ∀ γ∈A,atNative i (z γ) (S γ)=0 :=
      fun γ hγ=>(mem_filter.mp hγ).2
    have hRb : ∀ γ∈B,atNative a (z γ) (S γ)=0:= by
      intro γ hγ
      have h:=hr γ (hB hγ)
      rw [atNative_mul] at h
      exact (mul_eq_zero.mp h).resolve_left fun hz =>
        (mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨hB hγ,hz⟩)
    have h1 :=single i hi (by omega) A (hA.trans hT) hRa
    have h2 :=ih ha (by omega) B (hB.trans hT) hRb
    have hp:B.card+A.card=T.card:=card_sdiff_add_card_eq_card hA
    rw [← hp,hdeg,hseed,Nat.mul_add]
    exact (Nat.add_le_add h2 h1).trans_eq (by ring)
private theorem dGl (q a b c:ℕ) (hq:0<q) (h:q*a≤q*b+c) :
  a≤b+(c+q-1)/q:= by
 have hm:=Nat.mod_lt (c+q-1) hq
 have he :=Nat.mod_add_div (c+q-1) q
 have hc:c≤q*((c+q-1)/q) := by omega
 apply Nat.le_of_mul_le_mul_left _ hq
 rw [Nat.mul_add]
 exact h.trans (Nat.add_le_add_left hc _)
theorem of_children (h1 :P5_7_7.c1) (h2 :P5_7_7.c2)
   (bY:qyWKMud.c1) (high:qyWKMud.c2)
   (node :qGnV2ac.c1) (poles :qGnV2ac.c2) :P5_7.c7:= by
 intro D e H rate guard w T z S hz hs hd hh f hf he hH hr
 by_cases hzero :H=0
 · rw [nativeFee,ite_eq_left hzero]
   exact (seed_zero_count hs hf (hzero ▸ hH) hr).trans he
 rw [nativeFee,ite_eq_right hzero]
 have M:UJ D w T z S:=⟨hz,hs,hd,fun γ hγ=> by
   obtain ⟨A,hA,hsites⟩:=hh γ hγ
   exact hA.trans (card_le_card fun i hi=>mem_sites.mpr (hsites i hi))⟩
 rcases h2 D w T z S M with hsmall | ⟨U,hU,hcard,⟨J⟩⟩
 · exact hsmall.trans ((Nat.le_add_left 1 e).trans (Nat.le_add_right _ _))
 have hb:=all_factors (d5P h1 bY high node poles guard (restrict M hU) J)
   f hf he U (Subset.refl U) (fun γ hγ=>hr γ (hU hγ))
 have hc:=hb.trans
   (Nat.add_le_add (Nat.mul_le_mul_left (gap D) he)
     (Nat.mul_le_mul_left rate ((bv9 f H).mpr hH)))
 have hgap:0<gap D:=Nat.sub_pos_of_lt guard.2.1
 have hu:=dGl _ _ _ _ hgap hc
 exact hcard.trans ((Nat.add_le_add_right hu 1).trans_eq (by ac_rfl))
end
end qyWKMud
end
