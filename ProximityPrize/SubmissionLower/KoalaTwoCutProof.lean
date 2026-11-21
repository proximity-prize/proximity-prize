import ProximityPrize.SubmissionLower.KoalaTwoSectionCount
import ProximityPrize.SubmissionLower.KoalaRuledSaturated
import ProximityPrize.SubmissionLower.KoalaTwoCutStable
import ProximityPrize.SubmissionLower.KoalaTwoCutMarkedFacts
import ProximityPrize.SubmissionLower.KoalaStableNodes

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false

namespace SplitCut.TwoCut
noncomputable section
open MvPolynomial Finset
open P1 (K p)
open P1_7 (quotientOrder degreeAt)
open K1_14 (FX)
open HighCore82219 (FixedWord start finish)
open HighCore82219Upper (Input ResidueLift Factors componentMarks mem_componentMarks)
open HighCore82219Upper_3 (JetRing graphIdeal markPoint openFactor)
open HighCore82219Upper_3_2 (mark_regular)
open K1_13_6_3_5 (boundaryWeight)
open KoalaRectTaylor (jetToRect rectIdeal Represented EquationAxis)
open KoalaTwoSectionPrice (liftIndex graphDegree secondCut)

abbrev firstLength (J : Input) (v w : ℕ) := quotientOrder J.lo+1+liftIndex J.hi v w
abbrev secondLength (J : Input) (v w : ℕ) := quotientOrder J.lo+2+liftIndex J.hi v w

theorem graph_and_cut_budget (J : Input) (B : ResidueLift J) (D : Factors J B)
    (v w : ℕ) (he : 4 ≤ J.e)
    (haxis : ∀ i, (J.f.coeff i).degreeOf 0 ≤ v ∧ (J.f.coeff i).degreeOf 1 ≤ w)
    {γ : K} (hγ : γ ∈ componentMarks J D.proper) :
    let C := eIdeal J v w (firstIdeal J B D)
    (affineHilbertPolynomial C).natDegree ≤ 1 ∧
    (∀ P ∈ C.minimalPrimes, (affineHilbertPolynomial P).natDegree = 1) ∧
    (affineHilbertPolynomial C).coeff 1 ≤ firstLength J v w * (graphDegree J.e v w : ℚ) := by
  let Q := graphIdeal J B D
  let C := firstIdeal J B D
  let G := rectIdeal Q
  let R := rectIdeal C
  let φ := projectRing J v w
  have hsurj : Function.Surjective φ :=
    Rect.project_surjective (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
      (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  have facts := marked_cutoffs J B D
  have hTop (I : Ideal JetRing) (hOn : I ≤ RingHom.ker (markPoint J γ).toRingHom) :
      rectIdeal I ≠ ⊤ := by
    intro h
    have h1 : jetToRect (1 : JetRing) ∈ rectIdeal I := by simp [h]
    have h1' := RingHom.mem_ker.mp (hOn ((KoalaRectTaylor.jetToRect_mem_rectIdeal).mp h1))
    exact one_ne_zero ((map_one (markPoint J γ)).symm.trans h1')
  have hG : G ≠ ⊤ := hTop Q (proper_graph_mark D hγ)
  have hR : R ≠ ⊤ := hTop C (proper_first_mark facts hγ)
  obtain ⟨hdim, hpure, hdegree⟩ := Rect.graph_sat_budget J D facts.tangent he haxis hG
  have hell : J.ell ≤ quotientOrder J.lo := Nat.sub_le_sub_left J.lower _
  have hsections := KoalaRectTaylor.numerator_section J B D (axes_of_bounds J haxis)
    (r := J.ell+1) (j := J.ell+1) le_rfl
  obtain ⟨S,hS⟩ := widen_section he (Nat.add_le_add_right hell 1) hsections
  have hEq : R = G ⊔ Ideal.span {S.finite} := by
    change rectIdeal (Q ⊔ Ideal.span {first J B}) = _
    rw [rect_sup_span, hS]
  have hs : S.finite ∈ R := by rw [hEq]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hreg : IsLeftRegular (Ideal.Quotient.mk G S.finite) := by
    rw [hS]
    exact Rect.regular_comap jetToRect.symm.toRingHom (jetToRect.symm_apply_apply _) facts.regular
  have hcut := Rect.cut_pure φ.toRingHom hsurj hreg (hEq ▸ hR) (by decide : 0 < 2) hdim hpure
  rw [← hEq] at hcut
  have ha : 0 < J.e-3 := by omega
  have hcoef := (Rect.relative_cut_coeff (show G ≤ R by rw [hEq]; exact le_sup_left)
    ha S hs hreg).2
  have hd : (affineHilbertPolynomial (Rect.embedded G (J.e-3) (max 1 v) (max 1 w))).natDegree = 2 :=
    hdim
  rw [hd] at hcoef
  have hc : (affineHilbertPolynomial (Rect.embedded R (J.e-3) (max 1 v) (max 1 w))).coeff 1 ≤
      firstLength J v w * affineDegree (Rect.embedded G (J.e-3) (max 1 v) (max 1 w)) := by
    simpa [affineDegree, hd, Nat.factorial, mul_assoc] using hcoef
  exact ⟨hcut.1.le, hcut.2, hc.trans (mul_le_mul_of_nonneg_left hdegree (Nat.cast_nonneg _))⟩

private theorem curve_count (J : Input) (B : ResidueLift J) (D : Factors J B)
    (v w : ℕ) (he : 4 ≤ J.e) (hlo : J.lo = start .h2367) (hhi : J.hi = finish .h2367)
    (haxis : ∀ z : Fin 2, EquationAxis z J.f (![v,w] z))
    (hword : FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi))
    (V T : Finset K) (hV : GoodNodes J v w V) (hTV : T ⊆ V) (hT : T ⊆ componentMarks J D.proper)
    (hCutDim : (affineHilbertPolynomial (eIdeal J v w (firstIdeal J B D))).natDegree ≤ 1)
    (P : Ideal (MvPolynomial (axis J v w) FX)) (hP : P ∈ (eIdeal J v w (firstIdeal J B D)).minimalPrimes)
    (hDim : (affineHilbertPolynomial P).natDegree = 1) :
    letI := Classical.propDecidable
    let U := T.filter (fun γ => point J v w γ ∈ zeroLocus FX P)
    let m := boundaryWeight (eIdeal J v w (firstIdeal J B D)) P
    (m = 1 → (U.card : ℚ) ≤ secondLength J v w * (affineHilbertPolynomial P).coeff 1) ∧
    (2 ≤ m → (U.card : ℚ) ≤ (2*(secondLength J v w : ℚ)) * (affineHilbertPolynomial P).coeff 1) := by
  classical
  let C := firstIdeal J B D
  let φ := projectJet J v w
  change P ∈ (C.comap φ.toRingHom).minimalPrimes at hP
  rw [Ideal.comap_minimalPrimes_eq_of_surjective (projectJet_surjective J v w) C] at hP
  obtain ⟨Q,hQ,rfl⟩ := hP
  haveI : Q.IsPrime := hQ.isPrime
  let U := T.filter (fun γ => point J v w γ ∈ zeroLocus FX (Q.comap φ.toRingHom))
  have hOn γ (hγ : γ ∈ U) : Q ≤ RingHom.ker (markPoint J γ).toRingHom :=
    (mark_on_iff J v w γ Q).mp (mem_filter.mp hγ).2
  have hTU : U ⊆ T := filter_subset _ _
  have hSub : U ⊆ J.marks := fun γ hγ => (mem_componentMarks.mp (hT (hTU hγ))).1
  have hGraph : graphIdeal J B D ≤ Q := le_sup_left.trans hQ.le
  have hfirst : first J B ∈ Q := hQ.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hdeq : affineDegree (eIdeal J v w Q) =
      (affineHilbertPolynomial (eIdeal J v w Q)).coeff 1 := by
    change (affineHilbertPolynomial (eIdeal J v w Q)).natDegree = 1 at hDim
    simp only [affineDegree, Polynomial.leadingCoeff, hDim, Nat.factorial_one, Nat.cast_one, one_mul]
  change (_ → (U.card : ℚ) ≤ _ * (affineHilbertPolynomial (eIdeal J v w Q)).coeff 1) ∧
    (_ → (U.card : ℚ) ≤ _ * (affineHilbertPolynomial (eIdeal J v w Q)).coeff 1)
  rw [← hdeq]
  constructor
  · intro hwt
    by_cases hsecond : second J B ∈ Q
    · by_cases hEmpty : U.Nonempty
      · obtain ⟨γ,hγ⟩ := hEmpty
        have hOpen : openFactor J B ∉ Q := fun h =>
          mark_regular J B (hSub hγ) (RingHom.mem_ker.mp (hOn γ hγ h))
        have hQ' : eIdeal J v w Q ∈ (eIdeal J v w C).minimalPrimes :=
          Ideal.minimalPrimes_comap_of_surjective (projectJet_surjective J v w) hQ
        have hSimple := lift_simple J v w hQ' hwt hCutDim
        simpa only [secondLength, Nat.cast_add, Nat.cast_ofNat] using
          stable_count J B D v w he hlo hhi hword Q hGraph hOpen hfirst hsecond
            hSimple hDim V U hV (hTU.trans hTV) hSub hOn
      · rw [not_nonempty_iff_eq_empty.mp hEmpty, card_empty, Nat.cast_zero]
        exact mul_nonneg (Nat.cast_nonneg _) (affineDegree_nonneg _)
    · have hell : J.ell ≤ quotientOrder J.lo := Nat.sub_le_sub_left J.lower _
      have hsec := KoalaRectTaylor.numerator_section J B D haxis
        (r := J.ell+2) (j := J.ell+2) le_rfl
      have hS := widen_section he (Nat.add_le_add_right hell 2) (hsec.restrict hGraph)
      exact relative_count J v w he Q hDim hS hsecond U hOn
        (fun γ hγ => (marked_cutoffs J B D).second_zero γ (hT (hTU hγ)))
  · intro _
    simpa only [secondLength, Nat.cast_add, Nat.cast_ofNat] using
      repeated_count J B D v w he hlo hhi haxis hword Q hGraph hDim U hSub hOn

theorem two_cut_count : KoalaTwoSectionPrice.TwoCutIncidence := by
  classical
  intro J B D hlo hhi he₀ he₁ hword v w hsum hpaid haxis
  have he : 4 ≤ J.e := by omega
  have hvw : v+w ≤ 445 := (hsum.trans hpaid).le.trans (KoalaTwoSectionPrice.paid_le he₀ he₁)
  have hhi' : J.hi ≤ 2465 := hhi.le.trans (by decide)
  obtain ⟨V,_,hbad,hGood⟩ := Compression.compress_good J v w he₀ he₁
    ((Nat.le_add_right v w).trans hvw) ((Nat.le_add_left w v).trans hvw) hhi' haxis
  let A := componentMarks J D.proper
  let T := A ∩ V
  have hA : T ⊆ A := inter_subset_left
  have hV : T ⊆ V := inter_subset_right
  have hCard : A.card ≤ T.card + (J.marks \ V).card := by
    apply le_trans (card_le_card (t := T ∪ (J.marks \ V)) ?_) (card_union_le _ _)
    intro γ hγ
    by_cases hγV : γ ∈ V
    · exact mem_union_left _ (mem_inter.mpr ⟨hγ,hγV⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨(mem_componentMarks.mp hγ).1,hγV⟩)
  have hbound : T.card ≤ graphDegree J.e v w * firstLength J v w * secondLength J v w := by
    by_cases hn : T.Nonempty
    · obtain ⟨γ,hγ⟩ := hn
      let C := eIdeal J v w (firstIdeal J B D)
      obtain ⟨hD,hP,hC⟩ := graph_and_cut_budget J B D v w he haxis (hA hγ)
      have hOn a (ha : a ∈ T) : point J v w a ∈ zeroLocus FX C :=
        (mark_on_iff J v w a _).mpr (proper_first_mark (marked_cutoffs J B D) (hA ha))
      have hcurve (P : Ideal (MvPolynomial (axis J v w) FX)) (hP' : P ∈ C.minimalPrimes) :=
        curve_count J B D v w he hlo hhi (axes_of_bounds J haxis) hword V T hGood hV hA
          hD P hP' (hP P hP')
      have hh := TwoCutCoverage.weighted_cover C T (point J v w) hD hOn (secondLength J v w)
        (fun P hP' hwt => (hcurve P hP').1 hwt)
        (fun P hP' hwt => (hcurve P hP').2 hwt)
      have hTotal := hh.trans (mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg _))
      have hFinish : (T.card : ℚ) ≤
          (graphDegree J.e v w : ℚ)*firstLength J v w*secondLength J v w := by
        convert hTotal using 1 <;> ring
      exact_mod_cast hFinish
    · rw [not_nonempty_iff_eq_empty.mp hn, card_empty]
      exact Nat.zero_le _
  unfold secondCut
  exact hCard.trans (Nat.add_le_add hbound (hbad.trans (by
    calc
      (p+1)*(v+w+256) ≤ (p+1)*(2*(v+w)+256) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ ((p+1)*J.e)*(2*(v+w)+256) :=
        Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega)))))

#print axioms two_cut_count
end
end SplitCut.TwoCut
