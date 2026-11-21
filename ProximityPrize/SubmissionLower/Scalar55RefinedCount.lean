import ProximityPrize.SubmissionLower.Scalar50RefinedLower
import ProximityPrize.SubmissionLower.Scalar55LeadingLower

set_option Elab.async false
set_option autoImplicit true

namespace Scalar55RefinedCount
noncomputable section

open K1 (I K)
open K1_13 (Row Geom atJet extend)
open K1_13_5 (RegularAt NodeFamily)
open K1_13_5_4 (GeometricX jetPoint regularLocus)
open Scalar55LeadingPrice (Messages LowerRow physicalDegree)
open Scalar55LeadingLower (SecondFactors Whole invariantBudget firstWidth firstMixedBudget nodeFamily_count factor_cover)
open Scalar55LeadingLower_1 (properComponents SimpleInvariant CoefficientIdeal ActualSolutionCurve
  coefficientPoint ordinary_bound mem_properComponents)
open ScalarRefined (graphBox liftedBox taylorLength)
open ScalarRefined_1 (LiftedChart lifted_chart)
open scoped Polynomial BigOperators
open private box_mono from ProximityPrize.SubmissionLower.Fast048
open private exists_properComponent componentMarks mem_componentMarks mixedComponent_card
  coefficientFamily coefficientFamily_total mem_coefficientFamily
  from ProximityPrize.SubmissionLower.Scalar55LeadingLower
open private first_count from ProximityPrize.SubmissionLower.Scalar55LeadingLowerBase

private def relaxed {f : Row 3} (T : LiftedChart 1 f) :
    Scalar55LeadingLower_1.LiftedChart 0 f where
  cut := T.cut
  next := T.next
  numerator := T.numerator
  graph_box := box_mono
    (show (graphBox 1).b ≤ (Scalar55LeadingLower.graphBox 0).b by decide)
    (show (graphBox 1).j ≤ (Scalar55LeadingLower.graphBox 0).j by decide)
    (show (graphBox 1).t ≤ (Scalar55LeadingLower.graphBox 0).t by decide)
    le_rfl T.graph_box
  cut_box := box_mono
    (show (liftedBox 1 (taylorLength+1)).b ≤ (Scalar55LeadingLower.liftedBox 0 (taylorLength+1)).b by decide)
    (show (liftedBox 1 (taylorLength+1)).j ≤ (Scalar55LeadingLower.liftedBox 0 (taylorLength+1)).j by decide)
    (show (liftedBox 1 (taylorLength+1)).t ≤ (Scalar55LeadingLower.liftedBox 0 (taylorLength+1)).t by decide)
    le_rfl T.cut_box
  next_box := box_mono
    (show (liftedBox 1 (taylorLength+2)).b ≤ (Scalar55LeadingLower.liftedBox 0 (taylorLength+2)).b by decide)
    (show (liftedBox 1 (taylorLength+2)).j ≤ (Scalar55LeadingLower.liftedBox 0 (taylorLength+2)).j by decide)
    (show (liftedBox 1 (taylorLength+2)).t ≤ (Scalar55LeadingLower.liftedBox 0 (taylorLength+2)).t by decide)
    le_rfl T.next_box
  coefficient_box i := box_mono
    (show (liftedBox 1 taylorLength).b ≤ (Scalar55LeadingLower.liftedBox 0 taylorLength).b by decide)
    (show (liftedBox 1 taylorLength).j ≤ (Scalar55LeadingLower.liftedBox 0 taylorLength).j by decide)
    (show (liftedBox 1 taylorLength).t ≤ (Scalar55LeadingLower.liftedBox 0 taylorLength).t by decide)
    le_rfl (T.coefficient_box i)
  cut_represents := T.cut_represents
  next_represents := T.next_represents
  actual := T.actual

private theorem proper_count {w Γ s n} (hm : Messages w Γ s)
    (f : Fin n → Row 3) (hf : SecondFactors 0 f)
    (marks : ∀ γ ∈ Γ, ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ ¬ Whole (f i)) :
    48805 * Γ.card ≤ 48805 * ScalarRefined.mixedBudget 1 +
      (82268 + 2 * 48805) * invariantBudget 0 := by
  classical
  let top : Fin 1 := 0
  have hfr : ScalarRefined.SecondFactors 1 f :=
    ⟨hf.irreducible, hf.positive, hf.total, hf.index, hf.coordinate⟩
  let Tf (j : Fin n) := Classical.choice (lifted_chart n f hfr j)
  obtain ⟨Mf⟩ := ScalarRefined.mixed_sections 1 n f hfr Tf
  let T (j : Fin n) := relaxed (Tf j)
  let M : Scalar55LeadingLower_1.MixedSections 0 f T :=
    ⟨Mf.length, Mf.degree, Mf.length_eq, Mf.length_pos,
      Mf.total.trans (by decide), Mf.points, Mf.curves⟩
  have h2 := Scalar55LeadingLower_1_2.proof (top := 0)
  have h3 := Scalar55LeadingLower_1_3.proof (top := 0)
  let direct := (properComponents f).filter fun a => ¬ SimpleInvariant (f a.1) a.2
  let isolated := direct.biUnion (componentMarks f Γ s)
  have hmixed : isolated.card ≤ ScalarRefined.mixedBudget 1 := by
    calc
      _ ≤ ∑ a ∈ direct, (componentMarks f Γ s a).card := Finset.card_biUnion_le
      _ ≤ ∑ a ∈ direct, M.length a * M.degree a := Finset.sum_le_sum fun a ha =>
        mixedComponent_card hm M (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
      _ ≤ ∑ a ∈ properComponents f, M.length a * M.degree a :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ _ := Mf.total
  let stable := (properComponents f).filter fun a => SimpleInvariant (f a.1) a.2
  have heach (a : stable) := h2 n f hf a.val (Finset.mem_filter.mp a.property).1
    (Finset.mem_filter.mp a.property).2
  choose Q hQ hrec using heach
  let C := stable.attach.image Q
  have hfresh : ∀ P ∈ C, ∃ i, ¬ Whole (f i) ∧ ActualSolutionCurve (f i) P := by
    intro P hp
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    have ha := (Finset.mem_filter.mp a.property).1
    exact ⟨a.val.1, (mem_properComponents.mp ha).1, hQ a⟩
  obtain ⟨d, hd, hsum⟩ := h3 n f hf (fun i => ordinary_bound (f i)) C hfresh
  have hcut (P : CoefficientIdeal) (hp : P ∈ C) : P.IsPrime ∧
      (MvPolynomial.affineHilbertPolynomial P).natDegree ≤ 1 ∧
      MvPolynomial.affineDegree P ≤ (d P : ℚ) := by
    obtain ⟨i, _, h⟩ := hfresh P hp
    exact ⟨h.prime, h.dimension.le, (hd P hp).2⟩
  let F := coefficientFamily hm C d hcut
  have hFnum : F.n ≤ (invariantBudget 0) := by
    calc
      F.n = ∑ P ∈ C, 1 := Finset.card_eq_sum_ones C
      _ ≤ ∑ P ∈ C, d P := Finset.sum_le_sum fun P hp => (hd P hp).1
      _ ≤ _ := hsum
  have cover : Γ ⊆ isolated ∪ F.labels := by
    intro γ hγ
    obtain ⟨i, hi, hw⟩ := marks γ hγ
    have hdeg : (extend (s γ)).natDegree ≤ physicalDegree := by
      simpa only [Polynomial.natDegree_map] using hm.degree γ hγ
    obtain ⟨P, hp, hy⟩ := exists_properComponent T hdeg hi hw
    by_cases hs : SimpleInvariant (f i) P
    · let a : stable := ⟨(i, P), Finset.mem_filter.mpr ⟨hp, hs⟩⟩
      have hQC : Q a ∈ C := Finset.mem_image.mpr ⟨a, Finset.mem_attach _ _, rfl⟩
      exact Finset.mem_union_right _ (mem_coefficientFamily hm C d hcut hγ hQC
        (hrec a _ hdeg hy))
    · have hγiso : γ ∈ isolated := Finset.mem_biUnion.mpr
        ⟨(i,P), Finset.mem_filter.mpr ⟨hp, hs⟩, mem_componentMarks.mpr ⟨hγ, hy⟩⟩
      exact Finset.mem_union_left _ hγiso
  have htotal := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have hi := nodeFamily_count F hm
  have htot : F.totalCap ≤ invariantBudget 0 := (coefficientFamily_total hm C d hcut).trans_le hsum
  omega

theorem lower_count {w Γ s} (h : Messages w Γ s) (g : Row 3) (hg : LowerRow g)
    (hr : ∀ γ ∈ Γ, atJet g (extend (s γ)) = 0) : Γ.card ≤ 2325506586623926 := by
  classical
  let top : Fin 1 := 0
  have h2 := Scalar55LeadingLower_2.proof (top := 0)
  obtain ⟨n, f, q, hf, hq, hc⟩ := factor_cover g hg
  let first := Γ.filter fun γ => atJet q (extend (s γ)) = 0
  let proper := Γ.filter fun γ => ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ ¬ Whole (f i)
  let whole := Γ.filter fun γ => ∃ i, RegularAt 2 (f i) (extend (s γ)) ∧ Whole (f i)
  have hfirst := first_count (h.mono (Δ := first) (Finset.filter_subset _ _)) q hq
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hpmsg := h.mono (Δ := proper) (Finset.filter_subset _ _)
  have hproper := proper_count hpmsg f hf (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hwmsg := h.mono (Δ := whole) (Finset.filter_subset _ _)
  obtain ⟨W, hW, hn, hcap⟩ := h2 w whole s hwmsg n f hf (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hwhole : 48805 * whole.card ≤ 82268 * W.totalCap + 48805 * W.n :=
    (Nat.mul_le_mul_left _ (Finset.card_le_card hW)).trans (nodeFamily_count W hwmsg)
  have covers : Γ ⊆ first ∪ proper ∪ whole := by
    intro γ hγ
    rcases hc _ (hr γ hγ) with hlow | ⟨i, hreg⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hlow⟩))
    by_cases hw : Whole (f i)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, i, hreg, hw⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hγ, i, hreg, hw⟩))
  have htotal := (Finset.card_le_card covers).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hnumeric : 82268 * (firstMixedBudget top) + 48805 * ((firstWidth top) * (firstWidth top)) +
      (48805 * ScalarRefined.mixedBudget 1 + (82268 + 2 * 48805) * (invariantBudget top)) +
      (82268 * (131071 * Scalar55LeadingPrice.lowerWidth top) + 48805 * Scalar55LeadingPrice.lowerWidth top) ≤ 48805 * 2325506586623926 := by
    decide
  dsimp only [top] at hnumeric
  omega

#print axioms lower_count
end
end Scalar55RefinedCount
