import ProximityPrize.SubmissionLower.KoalaTwoCutProof
import ProximityPrize.SubmissionLower.Pr657High6955Finish
import ProximityPrize.SubmissionLower.Front6955On6960
import ProximityPrize.SubmissionLower.KoalaH2430Receipt
import ProximityPrize.SubmissionLower.KoalaH2430TerminalProof
import ProximityPrize.SubmissionLower.KoalaH2430PlainCut

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 18000

open FrontCore82258 (effectiveHeight)

namespace KoalaH2430
noncomputable section

open Polynomial Finset HighCore82258
open K1_14 (Equation FX L SeedBound seedEmbedding liftPoly atMark graphEval)
open K1_14_4 (seedDegree seedDegree_le_iff)
open KoalaRect (axisDegree axisDegree_le_iff seedBound_of_axis)
open K1_14_1 (PoleData CRTLift MarkResidues seedPair evaluated)
open P1_7_7 (CRTChart poleProduct sheet_cover curve_scale_of_cut localOrd localSeed)
open KoalaH2430Receipt (h cap prefixFee2430 paidCap guards charge)
open HighCore82258Upper (Input ResidueLift Factors componentMarks mem_componentMarks root_component ratio_le_ceil)
open scoped BigOperators
open private coordinate_bounds from ProximityPrize.SubmissionLower.UpperBranch7

private theorem singleton_invoice (k : ℕ) (hlo : 2429 ≤ k) (hhi : k ≤ 2430) (e v : ℕ) :
    Invoice (131071+k) k e v (ordinateFee k k e) (seedFee k k v) (scale k) := by
  have hm : scale k ≤ muNum k := by interval_cases k <;> decide
  have hlarge : muNum k ≤ 2*k*muNum k := by interval_cases k <;> decide
  refine ⟨?_,hm.trans (Nat.le_add_right _ _),hm.trans (hlarge.trans (Nat.le_add_right _ _)),?_,?_⟩
  · interval_cases k <;> decide
  · interval_cases k <;> decide
  · intro i hi
    have hg : degreeAt k < agreement := by interval_cases k <;> decide
    have hord : 131071+k-2*k ≤ quotientOrder k := by interval_cases k <;> decide
    exact coordinate_bounds (A := agreement) (n := blockLength) (d := 131071+k)
      (hi := degreeAt k) (ell := quotientOrder k) (w := k) (e := e) (v := v) (s := i)
      (by decide) le_rfl hg (height := k) le_rfl hord hi


private theorem persistent_at_cap {k : ℕ} (hlo : 2429 ≤ k) (hhi : k ≤ 2430) {u del} (M : AnchorModel u del)
    {Γ} (F:AnchoredFamily M Γ) (hwk : (effectiveHeight M) = k)
    {H} (hH:AdjacentChart M F H) {f:Equation} (hf:Reduced f) {v:ℕ}
    (hseed:SeedBound f v) :
    RegularCount M F f (persistentFee k k f.natDegree v):=by
  intro T hT hroots
  let w:=(effectiveHeight M).toNat
  let d:=131071+w
  let e:=f.natDegree
  have hwEq : w = k := by simp [w, hwk]
  have hw : 0 < w := by rw [hwEq]; omega
  have h2w : 2*w ≤ d := by rw [show d=131071+w from rfl,hwEq]; omega
  have hInv : Invoice d w e v (ordinateFee k k e) (seedFee k k v) (scale k) := by
    rw [show d=131071+w from rfl, hwEq]
    exact singleton_invoice k hlo hhi e v
  have hdp:d < K1.p:=hInv.degree.trans (by decide)
  have hword : FixedWord M.word T F.scalar d := by
    refine ⟨F.distinct.mono hT, ?_, ?_⟩
    · intro γ hγ
      rcases (F.mark γ (hT hγ)).scalar_degree with hz | hdeg
      · simp only [hz,natDegree_zero,Nat.zero_le]
      · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at hdeg
        have hd' : ((F.scalar γ).natDegree : ℤ) ≤ 131071 + (w : ℤ) := by
          dsimp only [w]
          have heff := FrontCore82258.overhead_le_effective M
          omega
        exact_mod_cast hd'
    · intro γ hγ
      let mark:=F.mark γ (hT hγ)
      exact ⟨mark.bad.support,mark.bad.agreement,mark.scalar_hits⟩
  have hz:Set.InjOn M.label (T:Set K1.K):=fun _ _ _ _ h => sub_left_inj.mp h
  obtain ⟨CRT,hCRT⟩:=FrontCore82258.crt_chart M F H hw hH
  obtain ⟨hmonic,hdeg,hcenter,hnodes⟩:=FrontCore82258.pole_data (M:=M) (F:=F) hH
  have hchart := P1_7_7_2.proof d w e v hw h2w hdp (poleProduct H) hmonic hdeg hcenter hnodes
    f hf.1 le_rfl hseed T M.label F.scalar M.word hword.degree hroots CRT
    (fun γ hγ => hCRT γ (hT hγ))
  obtain ⟨Ps, hPs, hcard, hsum, hcover⟩ := sheet_cover
    (hInv.scale_pos.trans_le hInv.ordinate) (hInv.scale_pos.trans_le hInv.seed)
    f hf.1 (show f.natDegree≤e from le_rfl) hseed T M.label F.scalar hroots
  have hcount:=count_cover hInv P1_7_7_3.proof (curve_scale_of_cut P1_7_7_3.proof) hword hchart hz Ps hPs hcover
  apply fee_of_bound hInv.scale_pos
  exact hcount.trans (add_le_add hsum (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) (by positivity)))

theorem small_ordinate_near {k : ℕ} (hlo : 2429 ≤ k) (hhi : k ≤ 2430) {u del Γ} (M : AnchorModel u del) (F : AnchoredFamily M Γ)
    (hw:(effectiveHeight M) = k) {H} (hH:AdjacentChart M F H) {f:Equation}
    (hf:Reduced f) {v : ℕ} (hseed:SeedBound f v) (hsep : singularDegree f.natDegree v < K1.p)
    {T:Finset K1.K} (hT:T ⊆ Γ)
    (hr : ∀ γ ∈ T,atMark f (M.label γ) (F.scalar γ)=0):T.card ≤ singularFee f.natDegree v +
      persistentFee k k f.natDegree v:=by
  classical
  let e:=f.natDegree
  let bad:=T.filter fun γ => graphEval (M.label γ) (f.resultant f.derivative)=0
  have hb:bad ⊆ T:=Finset.filter_subset _ _
  have hbad := FrontCore82258.resultant_count M hf hseed hsep bad
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hreg : ∀ γ ∈ T \ bad, regularRoot f (M.label γ) (F.scalar γ) := by
    intro γ hγ
    obtain ⟨ht,hn⟩:=Finset.mem_sdiff.mp hγ
    exact P1_7.regular_of_resultant hf.1 (hr γ ht) (fun hz => hn (Finset.mem_filter.mpr ⟨ht,hz⟩))
  have hpart:=Finset.card_sdiff_add_card_eq_card hb
  have hreg' := persistent_at_cap hlo hhi M F hw hH hf hseed _ (Finset.sdiff_subset.trans hT) hreg
  change bad.card≤singularFee e v at hbad
  change (T \ bad).card≤persistentFee k k e v at hreg'
  change T.card ≤ singularFee e v + persistentFee k k e v
  rw [← hpart, Nat.add_comm (singularFee e v)]
  exact Nat.add_le_add hreg' hbad

private theorem small_ordinate {u del Γ} (M : AnchorModel u del) (F : AnchoredFamily M Γ)
    (hw:(effectiveHeight M) = 2430) {H} (hH:AdjacentChart M F H) {f:Equation}
    (hf:Reduced f) (he:f.natDegree≤2) (hseed:SeedBound f (paidCap f.natDegree))
    {T:Finset K1.K} (hT:T ⊆ Γ)
    (hr : ∀ γ ∈ T,atMark f (M.label γ) (F.scalar γ)=0):T.card ≤ singularFee f.natDegree (paidCap f.natDegree) +
      persistentFee h h f.natDegree (paidCap f.natDegree) :=
  small_ordinate_near (by decide) (by decide) M F hw hH hf hseed
    (guards hf.1 (by omega)).1 hT hr

/-- The missing singleton inventory. It exposes the projected curve, the marks
that survive the prefixFee2430, and the terminal bank vanishing certificate. The extra one reserves the erased shift. -/
structure RetainedTrace {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ) where
  parents : Finset K1_14_3.Surface
  parents_nonempty : parents.Nonempty
  equation : Equation
  projected : K1_14_3.ProjectedProduct parents equation
  marks : Finset K1.K
  marks_sub : marks ⊆ Γ
  covers : ∀ γ ∈ marks, ∃ q ∈ parents, MarkOn M F q γ
  geometric : ∀ q ∈ parents, K1_14_3.Parent q
  poles : PoleData 2430
  crt : CRTLift poles
  terminal_pass : ∀ q ∈ parents, ∀ P ∈ evaluated crt (crtWord M)
    KoalaH2430Terminal.terminal.shape (KoalaH2430Terminal.terminal.shape.m*agreement-1),
    P ∈ q.asIdeal
  prefix_paid : (Γ \ marks).card + 1 ≤
    prefixFee2430 equation.natDegree

/-- The singleton prefix and terminal-bank geometry still required. The left
case is the exhausted inventory. -/
def PrefixTerminalGeometry : Prop :=
  ∀ {u del Γ} (M : AnchorModel u del) (F : AnchoredFamily M Γ),
    (effectiveHeight M) = 2430 → M.shift ∉ Γ →
      Γ.card + 1 ≤ prefixFee2430 0 ∨ Nonempty (RetainedTrace M F)

open KoalaTwoSectionPrice (properCharge properBudget surfaceDegree singleCut liftIndex liftIndex_spec)

private theorem paid_le_446 (e : ℕ) (hl : 7≤e) (hh : e≤21) :
    paidCap e≤446 := by
  interval_cases e <;> decide

theorem regular_count_near (J : Input)
    (hlo : 2429 ≤ J.lo) (hhi : J.hi ≤ 2695) {a b : ℕ}
    (haxes : ∀ i,(J.f.coeff i).degreeOf 0≤a ∧ (J.f.coeff i).degreeOf 1≤b)
    (hsum : a+b=J.v) (hwidth : ¬ singleCut J.e → J.v≤448) :
    J.marks.card ≤
      properCharge agreement J.lo J.hi J.e a b + flatFee J.hi J.v + J.e := by
  classical
  have weak:=HighCore82258Upper.fixed_word J (Finset.Subset.refl J.marks)
  have word : FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi) :=
    ⟨weak.distinct, weak.degree,fun γ hγ =>
      let m:=J.family.mark γ (J.marks_sub hγ)
      ⟨m.bad.support,m.bad.agreement,m.scalar_hits⟩⟩
  obtain ⟨B⟩:=HighCore82258Upper_1.proof J
  obtain ⟨D⟩:=HighCore82258Upper_2.proof J B
  let T:=componentMarks J D.proper
  let U:=fun j => componentMarks J (D.flat j)
  have hcov : J.marks ⊆ T ∪ univ.biUnion U := by
    intro γ hγ
    rcases root_component J D hγ with ht | ⟨j,hu⟩
    · exact mem_union.mpr (Or.inl (mem_componentMarks.mpr ⟨hγ,ht⟩))
    · exact mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨j,mem_univ _,mem_componentMarks.mpr ⟨hγ,hu⟩⟩))
  have hp : T.card ≤
      properCharge agreement J.lo J.hi J.e a b := by
    by_cases hs : singleCut J.e
    · rw [properCharge,if_pos hs]
      apply ratio_le_ceil (HighCore82258_5.scale_pos J J.agreement_gap)
      obtain ⟨hk,ha,hb⟩:=liftIndex_spec J.hi a b
      let k:=liftIndex J.hi a b
      have hc:=SplitCut.RawCount.proper_count J B D a b k hk
        (by simpa only [Nat.mul_comm] using ha) (by simpa only [Nat.mul_comm] using hb)
        haxes word J.agreement_gap
      refine hc.trans_eq ?_
      simp only [SplitCut.RawCount.rootDegree,SplitCut.RawCount.firstDegree,SplitCut.RawCount.weight,
        properBudget,surfaceDegree,HighCore82258_5.nodeVelocity,
        HighCore82258.lambdaNum,HighCore82258.muNum,HighCore82258.gap,k]
      ring
    · rw [properCharge,if_neg hs]
      have hv := hwidth hs
      unfold singleCut at hs
      have he₀ : 7≤J.e := by omega
      have he₁ : J.e≤21 := by omega
      exact SplitCut.TwoCut.plain_two_cut_near J B D hlo hhi he₀ he₁ word a b (hsum.le.trans hv) haxes
  have hf : (∑ j, (U j).card) ≤ flatFee J.hi J.v + J.e := by
    apply HighCore82258_5.flat_count J J.agreement_gap word D
    intro j
    obtain ⟨E⟩:=HighCore82258Upper_4.of_children HighCore82258Upper_4_1.proof HighCore82258Upper_4_2.proof J B D j
    exact HighCore82258Upper_5.of_children HighCore82258Upper_5_1.proof HighCore82258Upper_5_2.proof J B D j E
  have hmarks := (card_le_card hcov).trans (card_union_le T _)
  have hunion := card_biUnion_le (s := univ) (t := U)
  omega

private theorem retained_bill {u del Γ}
    (M : AnchorModel u del) (F : AnchoredFamily M Γ) (hw : (effectiveHeight M) = 2430)
    (hshift : M.shift ∉ Γ) (Q : RetainedTrace M F) :
    Q.marks.card + prefixFee2430 Q.equation.natDegree ≤
      cap := by
  classical
  let f := Q.equation
  let e := f.natDegree
  let d := seedDegree f
  let T := Q.marks
  change T.card + prefixFee2430 e ≤ cap
  have hf : Reduced f := ⟨Q.projected.positive,Q.projected.primitive,Q.projected.separable⟩
  have hpos : 1 ≤ e := hf.1
  obtain ⟨he, hterminal⟩ :=
    KoalaH2430Terminal.paid_degrees M Q.crt Q.geometric Q.terminal_pass hf Q.projected
  change e < 23 at he
  have hz : ∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ)=0 := by
    intro γ hγ
    obtain ⟨q,hq,hm⟩:=Q.covers γ hγ
    have hz:=RingHom.mem_ker.mp (hm (Q.projected.vanishes q hq))
    simpa only [coe_eval₂RingHom,eval₂_C,atMark] using hz
  by_cases hd : d=0
  · have hzero : SeedBound f 0 := (seedDegree_le_iff f 0).mp hd.le
    have hcount : T.card ≤ e := FrontCore82258.fixed_count M F T Q.marks_sub hf.1 hzero hz
    rw [Nat.add_comm T.card]
    exact (Nat.add_le_add_left hcount _).trans (KoalaH2430Receipt.fixed_budget he)
  obtain ⟨H,hH⟩:=FrontCore82258.adjacent_chart M F
  by_cases hs : e≤2
  · have hcount : T.card ≤ singularFee e (paidCap e) + persistentFee h h e (paidCap e) :=
      small_ordinate M F hw hH hf hs (seedBound_of_axis hterminal) Q.marks_sub hz
    rw [Nat.add_comm T.card]
    exact (Nat.add_le_add_left hcount _).trans (KoalaH2430Receipt.small_paid hpos hs)
  let a := axisDegree f 0
  let z := axisDegree f 1
  let b := paidCap e-a
  let v := a+b
  have hp : a+z ≤ paidCap e := hterminal
  have hv₁ : z≤b := by dsimp only [b]; omega
  have hv : v=paidCap e := by dsimp only [v,b]; omega
  have hseed : SeedBound f v := seedBound_of_axis (show a+z≤v by dsimp [v]; omega)
  have haxes (i : ℕ) : (f.coeff i).degreeOf 0≤a ∧ (f.coeff i).degreeOf 1≤b :=
    ⟨(axisDegree_le_iff f 0 _).mp le_rfl i,(axisDegree_le_iff f 1 _).mp hv₁ i⟩
  obtain ⟨hsep,hflat⟩:=guards hpos he
  have hsep' : singularDegree e v < P1.p :=
    (Nat.mul_le_mul_left (2*e-1) hv.le).trans_lt hsep
  have hflat' : e*degreeAt h+v < P1.p := by rw [hv]; exact hflat
  let bad := T.filter fun γ => graphEval (M.label γ) (f.resultant f.derivative)=0
  let R := T \ bad
  have hsub : bad ⊆ T := filter_subset _ _
  have hbad := FrontCore82258.resultant_count M hf hseed hsep' bad
    (fun _ hγ => (mem_filter.mp hγ).2)
  have hreg : ∀ γ ∈ R, regularRoot f (M.label γ) (F.scalar γ) := by
    intro γ hγ
    obtain ⟨ht,hn⟩:=mem_sdiff.mp hγ
    exact P1_7.regular_of_resultant hf.1 (hz γ ht) (fun he => hn (mem_filter.mpr ⟨ht,he⟩))
  have hw' : (effectiveHeight M).toNat = h := by simp [hw,h]
  let J : Input := {
    words:=u,deleted:=del,model:=M,labels:=Γ,family:=F,shift_out:=hshift,
    block:=H,chart:=hH,marks:=R,marks_sub:=sdiff_subset.trans Q.marks_sub,
    f:=f,regular:=hreg,reduced:=hf,sheets:=by omega,seed_pos:=Nat.pos_of_ne_zero hd,
    v:=v,seed_bound:=hseed,lo:=h,hi:=h,lower:=hw'.ge,upper:=hw'.le,
    positive:=by rw [hw']; decide,
    quotient_pos:=by rw [hw']; decide,
    agreement_gap:=by decide,factorial_guard:=by decide,separant_guard:=hsep',flat_guard:=hflat' }
  have hn := regular_count_near J (by change 2429 ≤ 2430; decide)
    (by change 2430 ≤ 2695; decide) haxes rfl (fun hh => by
    unfold singleCut at hh
    exact (hv.le.trans (paid_le_446 J.e (by omega) (by omega))).trans (by decide))
  change R.card ≤ properCharge agreement h h e a b + flatFee h v + e at hn
  have hg : T.card ≤ charge e a b := by
    unfold charge KoalaTwoSectionPrice.charge
    have hpart:=card_sdiff_add_card_eq_card hsub
    change R.card+bad.card=T.card at hpart
    change bad.card ≤ singularFee e v at hbad
    change _ ≤ properCharge agreement h h e a b + flatFee h v + singularFee e v + e
    omega
  have hcash:=KoalaH2430Receipt.ordinary_paid (e:=e) (by omega) he hv
  omega

private theorem count_at_2430 (prefixGeo : PrefixTerminalGeometry) {u del Γ}
    (M : AnchorModel u del) (F : AnchoredFamily M Γ) (hw : effectiveHeight M = 2430) :
    Γ.card ≤ cap := by
  classical
  let regular := Γ.erase M.shift
  have hreg : regular ⊆ Γ := erase_subset _ _
  have hshift : M.shift ∉ regular := notMem_erase _ _
  let G : AnchoredFamily M regular :=
    ⟨F.scalar,fun γ hγ => F.mark γ (hreg hγ),F.distinct.mono hreg⟩
  have herase : Γ.card-1≤regular.card := pred_card_le_card_erase
  rcases prefixGeo M G hw hshift with hx | trace
  · have hcap : prefixFee2430 0 ≤ cap := by decide
    omega
  · obtain ⟨Q⟩ := trace
    have hbill := retained_bill M G hw hshift Q
    have hpart := card_sdiff_add_card_eq_card Q.marks_sub
    have hprefix := Q.prefix_paid
    omega

theorem effective_singleton (prefixGeo : PrefixTerminalGeometry) {u del Γ}
    (M : AnchorModel u del) (F : AnchoredFamily M Γ) (h : M.overhead ≤ 2430)
    (hE : 2430 ≤ M.E.natDegree) : Γ.card ≤ Front6955On6960.coreBudget :=
  count_at_2430 prefixGeo M F (FrontCore82258.effective_eq_2430 M h hE)

theorem singleton (prefixGeo : PrefixTerminalGeometry) :
    Front6955On6960.HeightBand 2430 2430 := by
  intro u del M Γ F hlo hhi
  apply count_at_2430 prefixGeo M F
  exact (FrontCore82258.effective_eq_overhead M hlo).trans (le_antisymm hhi hlo)

theorem through_suffix (prefixGeo : PrefixTerminalGeometry) :
    Front6955On6960.HeightBand 2430 2695 := by
  intro u del M Γ F hlo hhi
  by_cases hs : M.overhead ≤ 2430
  · exact singleton prefixGeo u del M Γ F hlo hs
  · have hstart : (2431:ℤ)≤M.overhead := by omega
    exact (Pr657High6955.count M F hstart hhi).trans (by decide)

#print axioms effective_singleton
#print axioms singleton
#print axioms through_suffix

end
end KoalaH2430
