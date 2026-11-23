import ProximityPrize.SubmissionLower.KoalaTwoCutProof
import ProximityPrize.SubmissionLower.KoalaH2430RepeatedTariff

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false

namespace SplitCut.TwoCutCoverage
open P1 (I K node)
open HighCore82258 (FixedWord agreement blockLength persistent_card_le section_incidence)
open P1_7_3 (persistentNodes)
open scoped BigOperators

theorem repeated_marks_2430 {word : I → K} {U : Finset K} {S : K → Polynomial K} {d : ℕ}
    (hword:FixedWord word U S d) (hd:d≤133766)
    {ell L k δ:ℕ} (he₀:128376≤ell) (he₁:ell≤L) (he₂:L≤128642)
    (hk:k≤5390) (hδ:0 < δ)
    (hcuts : ∀ x : I, (∃ γ ∈ U, (S γ).eval (node x) ≠ word x) →
      (U.filter fun γ => (S γ).eval (node x) = word x).card ≤
        (ell-(persistentNodes word U S).card+k)*δ) :
    U.card≤(2*(L+2+k))*δ:=by
  classical
  by_cases hlarge:1 < U.card
  · let s := (persistentNodes word U S).card
    have hs:=(persistent_card_le hword hlarge).trans hd
    have hh:=repeated_tariff_2430 (s:=s) hs he₀ he₁ he₂ hk
    have hpos:0 < 179876-s:=by omega
    have h:=section_incidence hword ((ell-s+k)*δ) hcuts
    change (179876-s)*U.card≤(262144-s)*((ell-s+k)*δ) at h
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    rw [← mul_assoc]
    rw [← mul_assoc] at h
    exact h.trans (Nat.mul_le_mul_right δ hh)
  · exact (show U.card≤1 by omega).trans (Nat.succ_le_of_lt (Nat.mul_pos (by omega) hδ))

end SplitCut.TwoCutCoverage

namespace SplitCut.TwoCut
noncomputable section
open MvPolynomial Finset
open P1 (K I p node)
open P1_7 (quotientOrder degreeAt)
open K1_14 (FX seedEmbedding)
open K1_14_6 (Biform)
open HighCore82258 (FixedWord)
open HighCore82258Upper (Input ResidueLift Factors componentMarks mem_componentMarks)
open HighCore82258Upper_3 (JetRing graphIdeal markPoint openFactor CurveMarks oldNumerator)
open HighCore82258Upper_3_2 (mark_regular)
open HighCore82258Upper_3_3 (curveValue wordAt)
open K1_13_6_3_5 (boundaryWeight)
open KoalaRectTaylor (jetToRect rectIdeal Represented EquationAxis taylor_agrees)
open KoalaTwoSectionPrice (liftIndex liftIndex_le graphDegree secondCut)
open P1_7_3 (persistentNodes hits_persistent)
open private small_node_box from ProximityPrize.SubmissionLower.KoalaTwoCutStable
open private firstLength secondLength graph_and_cut_budget from ProximityPrize.SubmissionLower.KoalaTwoCutProof

theorem repeated_count_2430 (J : Input) (B : ResidueLift J) (D : Factors J B) (v w : ℕ)
    (he:4≤J.e) (hlo:2429≤J.lo) (hhi:J.hi≤2695)
    (haxis : ∀ z:Fin 2,EquationAxis z J.f (![v,w] z))
    (hword:FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi))
    (P:Ideal JetRing) [P.IsPrime] (hGraph:graphIdeal J B D≤P)
    (hDim:(affineHilbertPolynomial (eIdeal J v w P)).natDegree=1)
    (U:Finset K) (hSub:U ⊆ J.marks)
    (hOn : ∀ γ ∈ U,P≤RingHom.ker (markPoint J γ).toRingHom) :
    (U.card:ℚ)≤(2*(quotientOrder J.lo+2+liftIndex J.hi v w):ℚ)*affineDegree (eIdeal J v w P):=by
  classical
  let k:=liftIndex J.hi v w
  let L:=quotientOrder J.lo
  let sites:=persistentNodes J.model.word U J.family.scalar
  haveI:(eIdeal J v w P).IsPrime:=Ideal.comap_isPrime (projectJet J v w).toRingHom P
  obtain ⟨δ,hδ,hval⟩:=PointCount.curve_degree_nat (‹(eIdeal J v w P).IsPrime›.ne_top) hDim
  have hword' : FixedWord J.model.word U J.family.scalar (degreeAt J.hi) :=
    ⟨hword.distinct.mono hSub,fun γ hγ => hword.degree γ (hSub hγ),fun γ hγ => hword.hits γ (hSub hγ)⟩
  have hD:degreeAt J.hi≤133766:=by change 131071+J.hi≤133766; omega
  have hL:L≤128642:=by change 131071-J.lo≤128642; omega
  have hmin : 128376 ≤ J.ell := by
    have hu : J.w ≤ 2695 := J.upper.trans hhi
    change 128376≤131071 - J.w
    omega
  have hk:k≤5390:=liftIndex_le hhi _ _
  have h₀:J.ell≤L:=Nat.sub_le_sub_left J.lower _
  have hCuts (x : I) (hfail : ∃ γ ∈ U, (J.family.scalar γ).eval (node x) ≠ J.model.word x) :
      (U.filter fun γ => (J.family.scalar γ).eval (node x) = J.model.word x).card ≤
        (J.ell-sites.card+k)*δ:=by
    obtain ⟨b,a,W⟩:=HighCore82258Upper_3_3_2.proof J sites x
    let f:=KoalaRectTaylor.nodeNumerator J B sites x b a
    have hNode (γ : K) (hγ : γ ∈ U) :
        markPoint J γ f=0↔(J.family.scalar γ).eval (node x)=J.model.word x:=by
      obtain ⟨ho,hcv⟩:=HighCore82258Upper_3_3_1.proof J B γ (hSub hγ)
      have hG p (hp : p ∈ graphIdeal J B D) : markPoint J γ p = 0 :=
        RingHom.mem_ker.mp (hOn γ hγ (hGraph hp))
      have hs i (hi : i ∈ sites) :
          curveValue (markPoint J γ) J B i=algebraMap FX FX (wordAt J i):=by
        rw [hcv i,Algebra.algebraMap_self,RingHom.id_apply,wordAt,hits_persistent hγ hi]
      rw [KoalaRectTaylor.node_zero_iff (markPoint J γ) ho hG W hs,
        hcv x,Algebra.algebraMap_self,RingHom.id_apply,wordAt]
      exact seedEmbedding.injective.eq_iff
    have hf : f ∉ P := by
      obtain ⟨γ,hγ,hn⟩:=hfail
      exact fun hf => hn ((hNode γ hγ).mp (RingHom.mem_ker.mp (hOn γ hγ hf)))
    have hsec:=KoalaRectTaylor.node_section J B D haxis sites x b a
    have hbody:=widen_section he le_rfl (hsec.restrict hGraph)
    let V:=U.filter fun γ => (J.family.scalar γ).eval (node x)=J.model.word x
    have hBound := relative_count J v w he P hDim hbody hf V
      (fun γ hγ => hOn γ (mem_filter.mp hγ).1)
      (fun γ hγ => (hNode γ (mem_filter.mp hγ).1).mpr (mem_filter.mp hγ).2)
    rw [hval] at hBound
    exact_mod_cast hBound
  have hC:=TwoCutCoverage.repeated_marks_2430 hword' hD hmin h₀ hL hk hδ hCuts
  rw [hval]
  exact_mod_cast hC


theorem stable_count_2430 (J : Input) (B : ResidueLift J) (D : Factors J B) (v w : ℕ)
    (he:4≤J.e) (hlo:2429≤J.lo) (hhi:J.hi≤2695)
    (hword:FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi))
    (P:Ideal JetRing) [P.IsPrime] (hGraph:graphIdeal J B D≤P)
    (hOpen:openFactor J B ∉ P) (hfirst:first J B ∈ P) (hsecond:second J B ∈ P)
    (hSimple : ∀ x ∈ P, ∃ t ∉ P,t*x ∈ firstIdeal J B D)
    (hDim:(affineHilbertPolynomial (eIdeal J v w P)).natDegree=1)
    (T U:Finset K) (hGood:GoodNodes J v w T) (hTU:U ⊆ T) (hSub:U ⊆ J.marks)
    (hOn : ∀ γ ∈ U,P≤RingHom.ker (markPoint J γ).toRingHom) :
    (U.card:ℚ)≤(quotientOrder J.lo+2+liftIndex J.hi v w:ℚ)*affineDegree (eIdeal J v w P):=by
  classical
  let L:=quotientOrder J.lo
  let k:=liftIndex J.hi v w
  let r:=J.ell+1
  have hr:0<r:=by dsimp [r]; omega
  have hp : r+1 < p := by
    have hle:J.ell≤131071:=Nat.sub_le _ _
    change J.ell+1+1 < 2130706433
    omega
  have rel₁:=taylor_agrees J B D (r:=r) (j:=r) le_rfl
  have rel₂:=taylor_agrees J B D (r:=r+1) (j:=r+1) le_rfl
  have hOld : oldNumerator J B r ∈ P :=
    (StableFlow.relative_cutoff_mem hGraph hOpen rel₁).mp hfirst
  have hs:=StableFlow.relative_cutoff_stable hGraph hOpen hr hp rel₁ rel₂ hfirst hsecond hSimple
  let C : CurveMarks J B D := {
    prime:=P
    isPrime := ‹P.IsPrime›
    onGraph:=hGraph
    onCutoff:=hOld
    regular:=hOpen
    marks:=U
    sub:=hSub
    liesOn:=hOn }
  haveI:(eIdeal J v w P).IsPrime:=Ideal.comap_isPrime (projectJet J v w).toRingHom P
  obtain ⟨δ,hδ,hval⟩:=PointCount.curve_degree_nat (‹(eIdeal J v w P).IsPrime›.ne_top) hDim
  have hw : FixedWord J.model.word U J.family.scalar (degreeAt J.hi) :=
    ⟨hword.distinct.mono hSub,fun γ hγ => hword.degree γ (hSub hγ),fun γ hγ => hword.hits γ (hSub hγ)⟩
  have hD:degreeAt J.hi≤133766:=by change 131071+J.hi≤133766; omega
  have hL:128376≤L:=by
    have hb := J.lower.trans (J.upper.trans hhi)
    change 128376≤131071-J.lo
    omega
  have hCuts (x : I) (hFail : ∃ γ ∈ U, (J.family.scalar γ).eval (node x) ≠ J.model.word x) :
      (U.filter fun γ => (J.family.scalar γ).eval (node x)=J.model.word x).card≤129*δ:=by
    obtain ⟨g,hg,hn,hits⟩:=hGood B D C hTU hs x hFail
    let V:=U.filter fun γ => (J.family.scalar γ).eval (node x)=J.model.word x
    have hR := relative_count J v w he P hDim (small_node_box J v w he P hg) hn V
      (fun γ hγ => hOn γ (mem_filter.mp hγ).1)
      (fun γ hγ => hits γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2)
    rw [hval] at hR
    exact_mod_cast hR
  have hC:=TwoCutCoverage.stable_marks hw hD hL (k:=k) hδ hCuts
  rw [hval]
  exact_mod_cast hC


private theorem curve_count_2430 (J : Input) (B : ResidueLift J) (D : Factors J B)
    (v w:ℕ) (he:4≤J.e) (hlo:2429≤J.lo) (hhi:J.hi≤2695)
    (haxis : ∀ z:Fin 2,EquationAxis z J.f (![v,w] z))
    (hword:FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi))
    (V T:Finset K) (hV:GoodNodes J v w V) (hTV:T ⊆ V) (hT:T ⊆ componentMarks J D.proper)
    (hCutDim:(affineHilbertPolynomial (eIdeal J v w (firstIdeal J B D))).natDegree≤1)
    (P:Ideal (MvPolynomial (axis J v w) FX)) (hP:P ∈ (eIdeal J v w (firstIdeal J B D)).minimalPrimes)
    (hDim:(affineHilbertPolynomial P).natDegree=1) :
    letI:=Classical.propDecidable
    let U:=T.filter (fun γ => point J v w γ ∈ zeroLocus FX P)
    let m:=boundaryWeight (eIdeal J v w (firstIdeal J B D)) P
    (m=1→(U.card:ℚ)≤secondLength J v w*(affineHilbertPolynomial P).coeff 1) ∧
    (2≤m→(U.card:ℚ)≤(2*(secondLength J v w:ℚ))*(affineHilbertPolynomial P).coeff 1):=by
  classical
  let C:=firstIdeal J B D
  let φ:=projectJet J v w
  change P ∈ (C.comap φ.toRingHom).minimalPrimes at hP
  rw [Ideal.comap_minimalPrimes_eq_of_surjective (projectJet_surjective J v w) C] at hP
  obtain ⟨Q,hQ,rfl⟩:=hP
  haveI:Q.IsPrime:=hQ.isPrime
  let U:=T.filter (fun γ => point J v w γ ∈ zeroLocus FX (Q.comap φ.toRingHom))
  have hOn γ (hγ : γ ∈ U) : Q ≤ RingHom.ker (markPoint J γ).toRingHom :=
    (mark_on_iff J v w γ Q).mp (mem_filter.mp hγ).2
  have hTU:U ⊆ T:=filter_subset _ _
  have hSub:U ⊆ J.marks:=fun γ hγ => (mem_componentMarks.mp (hT (hTU hγ))).1
  have hGraph:graphIdeal J B D≤Q:=le_sup_left.trans hQ.le
  have hfirst:first J B ∈ Q:=hQ.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hdeq : affineDegree (eIdeal J v w Q) =
      (affineHilbertPolynomial (eIdeal J v w Q)).coeff 1:=by
    change (affineHilbertPolynomial (eIdeal J v w Q)).natDegree=1 at hDim
    simp only [affineDegree,Polynomial.leadingCoeff,hDim,Nat.factorial_one,Nat.cast_one,one_mul]
  change (_ → (U.card : ℚ) ≤ _ * (affineHilbertPolynomial (eIdeal J v w Q)).coeff 1) ∧
    (_→(U.card:ℚ)≤_*(affineHilbertPolynomial (eIdeal J v w Q)).coeff 1)
  rw [← hdeq]
  constructor
  · intro hwt
    by_cases hsecond:second J B ∈ Q
    · by_cases hEmpty : U.Nonempty
      · obtain ⟨γ,hγ⟩ := hEmpty
        have hOpen : openFactor J B ∉ Q := fun h =>
          mark_regular J B (hSub hγ) (RingHom.mem_ker.mp (hOn γ hγ h))
        have hQ' : eIdeal J v w Q ∈ (eIdeal J v w C).minimalPrimes :=
          Ideal.minimalPrimes_comap_of_surjective (projectJet_surjective J v w) hQ
        have hSimple:=lift_simple J v w hQ' hwt hCutDim
        simpa only [secondLength, Nat.cast_add, Nat.cast_ofNat] using
          stable_count_2430 J B D v w he hlo hhi hword Q hGraph hOpen hfirst hsecond
            hSimple hDim V U hV (hTU.trans hTV) hSub hOn
      · rw [not_nonempty_iff_eq_empty.mp hEmpty, card_empty, Nat.cast_zero]
        exact mul_nonneg (Nat.cast_nonneg _) (affineDegree_nonneg _)
    · have hell : J.ell ≤ quotientOrder J.lo := Nat.sub_le_sub_left J.lower _
      have hsec := KoalaRectTaylor.numerator_section J B D haxis
        (r:=J.ell+2) (j:=J.ell+2) le_rfl
      have hS:=widen_section he (Nat.add_le_add_right hell 2) (hsec.restrict hGraph)
      exact relative_count J v w he Q hDim hS hsecond U hOn
        (fun γ hγ => (marked_cutoffs J B D).second_zero γ (hT (hTU hγ)))
  · intro _
    simpa only [secondLength, Nat.cast_add, Nat.cast_ofNat] using
      repeated_count_2430 J B D v w he hlo hhi haxis hword Q hGraph hDim U hSub hOn


/-- The standard ruled count at the singleton height. The axes may be
actual or padded as long as their sum meets the compression limit. -/
theorem plain_two_cut_near (J : Input) (B : ResidueLift J) (D : Factors J B)
    (hlo : 2429 ≤ J.lo) (hhi : J.hi ≤ 2695) (he₀ : 7≤J.e) (he₁ : J.e≤21)
    (hword : FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi))
    (v w : ℕ) (hvw : v+w≤448)
    (haxis : ∀ i, (J.f.coeff i).degreeOf 0≤v ∧ (J.f.coeff i).degreeOf 1≤w) :
    (componentMarks J D.proper).card ≤ secondCut J.lo J.hi J.e v w := by
  classical
  have he:4≤J.e:=by omega
  have hhi' : J.hi≤2695:=hhi
  obtain ⟨V,_,hbad,hGood⟩ := Compression.compress_good J v w he₀ he₁
    ((Nat.le_add_right v w).trans hvw) ((Nat.le_add_left w v).trans hvw) hhi' haxis
  let A:=componentMarks J D.proper
  let T:=A ∩ V
  have hA:T ⊆ A:=inter_subset_left
  have hV:T ⊆ V:=inter_subset_right
  have hCard : A.card ≤ T.card + (J.marks \ V).card := by
    apply le_trans (card_le_card (t:=T ∪ (J.marks \ V)) ?_) (card_union_le _ _)
    intro γ hγ
    by_cases hγV:γ ∈ V
    · exact mem_union_left _ (mem_inter.mpr ⟨hγ,hγV⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨(mem_componentMarks.mp hγ).1,hγV⟩)
  have hbound : T.card ≤ graphDegree J.e v w * firstLength J v w * secondLength J v w := by
    by_cases hn:T.Nonempty
    · obtain ⟨γ,hγ⟩ := hn
      let C:=eIdeal J v w (firstIdeal J B D)
      obtain ⟨hD,hP,hC⟩:=graph_and_cut_budget J B D v w he haxis (hA hγ)
      have hOn a (ha : a ∈ T) : point J v w a ∈ zeroLocus FX C :=
        (mark_on_iff J v w a _).mpr (proper_first_mark (marked_cutoffs J B D) (hA ha))
      have hcurve (P : Ideal (MvPolynomial (axis J v w) FX)) (hP' : P ∈ C.minimalPrimes) :=
        curve_count_2430 J B D v w he hlo hhi (axes_of_bounds J haxis) hword V T hGood hV hA
          hD P hP' (hP P hP')
      have hh := TwoCutCoverage.weighted_cover C T (point J v w) hD hOn (secondLength J v w)
        (fun P hP' hwt => (hcurve P hP').1 hwt)
        (fun P hP' hwt => (hcurve P hP').2 hwt)
      have hTotal:=hh.trans (mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg _))
      have hFinish : (T.card : ℚ) ≤
          (graphDegree J.e v w:ℚ)*firstLength J v w*secondLength J v w:=by
        convert hTotal using 1 <;> ring
      exact_mod_cast hFinish
    · rw [not_nonempty_iff_eq_empty.mp hn, card_empty]
      exact Nat.zero_le _
  unfold secondCut
  exact hCard.trans (Nat.add_le_add hbound hbad)


theorem plain_two_cut_2430 (J : Input) (B : ResidueLift J) (D : Factors J B)
    (hlo : J.lo = 2430) (hhi : J.hi = 2430) (he₀ : 7≤J.e) (he₁ : J.e≤21)
    (hword : FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi))
    (v w : ℕ) (hvw : v+w≤446)
    (haxis : ∀ i, (J.f.coeff i).degreeOf 0≤v ∧ (J.f.coeff i).degreeOf 1≤w) :
    (componentMarks J D.proper).card ≤ secondCut J.lo J.hi J.e v w :=
  plain_two_cut_near J B D (by rw [hlo]; decide) (by rw [hhi]; decide)
    he₀ he₁ hword v w (hvw.trans (by decide)) haxis


#print axioms plain_two_cut_2430
end
end SplitCut.TwoCut
