import ProximityPrize.SubmissionLower.HighCore82258Family
import ProximityPrize.SubmissionLower.KoalaRectBridgeCore
import ProximityPrize.SubmissionLower.Pr657Rect2435Axes

set_option autoImplicit false
set_option Elab.async false

namespace KoalaTwoTerminal
noncomputable section

open Finset Polynomial
open K1_14 (Banks Equation SeedBound Jet atMark atX graphEval jetAt)
open K1_14_3 (Surface Parent ProjectedProduct SeedField SeedClosure OnSeedFibre)
open FrontCore82258 (AnchorModel AnchoredFamily)
open HighCore82258 (Bank agreement Listed Source BankPass)
open K1 (K p)
open private K1_14_3_7.toSeed K1_14_3_7.toSeed_injective K1_14_3_7.seedGCD
  from ProximityPrize.SubmissionLower.Fast053
open K1_14_3_7 (toSeed toSeed_injective seedGCD)
open private K1_14.resultant_degree from ProximityPrize.SubmissionLower.Fast023
open K1_14 (resultant_degree)
open scoped BigOperators

open KoalaRect (rectSlots rectGain rectDebit)
open Pr657Rect2435Axes (swap slots_reversed debit_swap gain_swap)

/-- Use the same checked rectangle in either orientation of the seed axes. -/
theorem oriented_axis_cap {A h nodes moment e cap : ℕ} {s : K1_14.Shape}
    {U d actual : Fin 2 → ℕ}
    (hside : U 1 ≤ U 0) (hlo : d 0 ≤ d 1) (hhi : d 1 ≤ d 0+1)
    (hsum : d 0+d 1 = cap+1) (hbox : U 0+U 1 ≤ s.U)
    (hgain : rectDebit h nodes moment U < rectGain A h s e U d)
    (reject : ∀ V order : Fin 2 → ℕ, V 0+V 1 ≤ s.U →
      (∀ r, rectSlots V actual r ≤ rectSlots V order r) →
      rectDebit h nodes moment V < rectGain A h s e V order → False) :
    actual 0+actual 1 ≤ cap := by
  by_contra! hcap
  have hdegree : d 0+d 1 ≤ actual 0+actual 1 := by rw [hsum]; omega
  by_cases hor : actual 0 ≤ actual 1
  · exact reject U d hbox
      (fun r => HighCore82258.oriented_rect_capacity_le hside hor hlo hhi hdegree) hgain
  · refine reject (swap U) (swap d) ?_
      (fun r => slots_reversed r hside (Nat.le_of_not_ge hor) hlo hhi hdegree) ?_
    · simpa [Nat.add_comm] using hbox
    · rwa [debit_swap,gain_swap]

/-- Gauss's lemma moves divisibility back to the primitive seed polynomial. -/
theorem lift_dvd {f g : Equation} (hprim : f.IsPrimitive)
    (hd : f.map toSeed ∣ g.map toSeed) : f ∣ g := by
  let := seedGCD
  exact hprim.dvd_of_fraction_map_dvd_fraction_map (K := SeedField) hd

/-- A factor inherits all terminal leading-coefficient divisibilities. -/
theorem trace_of_dvd {h : ℕ} {t : Bank} {rows : Banks} {f g : Equation}
    (hg : HighCore82258.TerminalTrace h t rows g) (hd : f ∣ g) :
    HighCore82258.TerminalTrace h t rows f :=
  ⟨hg.floor_bound, hg.shape, hg.leading, fun W hW P hP hn =>
    (pow_dvd_pow_of_dvd hd _).trans (hg.divides W hW P hP hn)⟩

theorem resultant_ne_zero_of_not_dvd {f g : Equation}
    (hirr : Irreducible (f.map toSeed)) (hd : ¬ f.map toSeed ∣ g.map toSeed) :
    f.resultant g ≠ 0 := by
  have hcop : IsCoprime (f.map toSeed) (g.map toSeed) :=
    hirr.coprime_iff_not_dvd.mpr hd
  have hres := Polynomial.resultant_ne_zero (f.map toSeed) (g.map toSeed) hcop
  rw [Polynomial.natDegree_map_eq_of_injective toSeed_injective,
    Polynomial.natDegree_map_eq_of_injective toSeed_injective, Polynomial.resultant_map_map] at hres
  exact fun hz => hres (by rw [hz, map_zero])

/-- Padded specialization works even when either ordinate degree drops at a mark. -/
theorem common_roots_count {u del Γ} {M : AnchorModel u del} (F : AnchoredFamily M Γ)
    {f g : Equation} {v : ℕ} (hpos : 0 < f.natDegree)
    (hirr : Irreducible (f.map toSeed)) (hd : ¬ f.map toSeed ∣ g.map toSeed)
    (hf : SeedBound f v) (hg : SeedBound g v)
    (hp : (f.natDegree + g.natDegree) * v < p) (T : Finset K)
    (hF : ∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0)
    (hG : ∀ γ ∈ T, atMark g (M.label γ) (F.scalar γ) = 0) :
    T.card ≤ (p + 1) * ((f.natDegree + g.natDegree) * v) := by
  let R := f.resultant g
  have hn : R ≠ 0 := resultant_ne_zero_of_not_dvd hirr hd
  have hr : R.totalDegree ≤ (f.natDegree + g.natDegree) * v := resultant_degree hf hg
  let S : K1_14_3.SeedCover := ⟨R, hn, ∅⟩
  have hzero (γ : K) (hγ : γ ∈ T) : graphEval (M.label γ) R = 0 := by
    let ψ := graphEval (M.label γ)
    let x := atX (F.scalar γ)
    apply Sol1.C40Primitives.map_resultant_eq_zero_of_common_root ψ f g f.natDegree g.natDegree le_rfl le_rfl
      (Or.inl (Nat.ne_of_gt hpos)) x
    · exact hF γ hγ
    · exact hG γ hγ
  have h := K1_14_3.seed_count (T := T) (label := M.label)
    (fun _ _ _ _ hh => sub_left_inj.mp hh) S (hr.trans_lt hp)
    (fun γ hγ => Or.inl (hzero γ hγ))
  exact (show T.card ≤ (p + 1) * R.totalDegree by
    simpa only [S, Finset.card_empty, Nat.add_zero] using h).trans
    (Nat.mul_le_mul_left _ hr)

/-- No disjointness of parent mark sets is needed. -/
theorem card_le_two_prefixes {Γ A B : Finset K}
    : Γ.card ≤ (Γ \ A).card + (Γ \ B).card + (A ∩ B).card := by
  classical
  have hcov : Γ ⊆ (Γ \ A) ∪ (Γ \ B) ∪ (A ∩ B) := by
    intro γ hγ
    by_cases ha : γ ∈ A
    · by_cases hb : γ ∈ B
      · exact mem_union_right _ (mem_inter.mpr ⟨ha, hb⟩)
      · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨hγ, hb⟩))
    · exact mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨hγ, ha⟩))
  exact (card_le_card hcov).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))

/-- The grade-zero case uses the B-only bill. The positive-grade case
needs a stronger width receipt only when the equations share a factor. -/
theorem count_of_two_traces {u del Γ} {M : AnchorModel u del} (F : AnchoredFamily M Γ)
    {f : Equation} {A : Finset K} {aBill bBill cap v reserve : ℕ}
    (hprim : f.IsPrimitive) (hpos : 0 < f.natDegree)
    (hirr : Irreducible (f.map toSeed)) (hf : SeedBound f v)
    (hsub : A ⊆ Γ) (ha : (Γ \ A).card + reserve ≤ aBill)
    (hA : ∀ γ ∈ A, atMark f (M.label γ) (F.scalar γ) = 0)
    (hB : Γ.card + reserve ≤ bBill ∨ ∃ (g : Equation) (B : Finset K),
      SeedBound g v ∧ (Γ \ B).card ≤ bBill ∧
      (∀ γ ∈ B, atMark g (M.label γ) (F.scalar γ) = 0) ∧
      (f ∣ g → A.card + aBill ≤ cap) ∧
      (f.natDegree + g.natDegree) * v < p ∧
      aBill + bBill + (p + 1) * ((f.natDegree + g.natDegree) * v) ≤ cap)
    (hzero : bBill ≤ cap) : Γ.card + reserve ≤ cap := by
  classical
  rcases hB with hb | ⟨g, B, hg, hb, hz, htransfer, hp, hsum⟩
  · exact hb.trans hzero
  · by_cases hd : f.map toSeed ∣ g.map toSeed
    · have hcount := htransfer (lift_dvd hprim hd)
      have hcard := Finset.card_sdiff_add_card_eq_card hsub
      omega
    · have hcount := common_roots_count F hpos hirr hd hf hg hp (A ∩ B)
        (fun γ hγ => hA γ (mem_inter.mp hγ).1)
        (fun γ hγ => hz γ (mem_inter.mp hγ).2)
      have hparts := card_le_two_prefixes (Γ := Γ) (A := A) (B := B)
      omega

end
end KoalaTwoTerminal

namespace KoalaTwoTerminal
noncomputable section
open Finset Polynomial
open K1_14 (FX L Jet Equation Shape shapeSum)
open K1_14_1
open K1_14_3 (Surface Parent ProjectedProduct)
open KoalaRect
open K1 (I)
open P1_7_1 (nodeRows groupedPoleMoment)
open scoped BigOperators

/-- The rectangular rejection calculation needs divisibility only. This version
lets the projected equation of B contain the irreducible equation of A. -/
theorem rectLoss_of_dvd {h : ℕ} (hpos : 0 < h) (hraw : h ≤ 131070) (hchar : h < K1.p)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L) (A : ℕ) (s : Shape)
    (U d : Fin 2 → ℕ) (hA : 0 < s.m * A) (hsmall : s.m * A < K1.p)
    (hbox : U 0 + U 1 ≤ s.U) (hs : s.B < K1.p) (hwidth : s.B * (131071 - h) ≤ s.m * A)
    {nodes moment E : ℕ} (hnodes : nodeRows s ≤ nodes) (hmoment : groupedPoleMoment s.B s.J ≤ moment)
    (he : 0 < E) {qs : Finset Surface} (hgeo : ∀ q ∈ qs, Parent q)
    (hpass : ∀ q ∈ qs, ∀ P ∈ evaluated Crt word s (s.m * A - 1), P ∈ q.asIdeal)
    {f g : Equation} (hf : f ≠ 0) (hE : E ≤ f.natDegree) (hprod : ProjectedProduct qs g)
    (hfg : f ∣ g) (hslots : ∀ r, rectSlots U (axisDegree f) r ≤ rectSlots U d r) :
    rectGain A h s E U d ≤ rectDebit h nodes moment U := by
  let top := s.m * A
  have htop : top - 1 + 1 = top := by dsimp [top]; omega
  have hrawWidth : rawWidthCond h s (top - 1) := by
    intro q hq j _
    rw [htop]
    exact (Nat.mul_le_mul_right _ hq).trans (hwidth.trans (by omega : top ≤ top + j))
  have hfloor := rectRankFloor hpos hraw hchar Crt word s (top - 1) U hbox hs hrawWidth hnodes hmoment
  rw [htop] at hfloor
  have hcap (W : ℕ) (hW : W ∈ range top) :
      Module.finrank FX (rectEvaluated Crt word s W U) ≤ rectCapacity A h s E U d W := by
    apply rectCutoff_finrank_le _ _ _ _ _ _ _ _ hf hE (by omega) he
    · intro P hP j i hn
      exact evaluated_shape Crt word (rectEvaluated_le Crt word s W U hP) j i hn
    · intro P hP
      exact rectEvaluated_axis Crt word hP
    · intro P hP hn
      exact P0_10_1.leading_bound hpos hraw Crt word s W P (rectEvaluated_le Crt word s W U hP) hn
    · intro P hP hn
      exact (pow_dvd_pow_of_dvd hfg _).trans
        (rectDivides hpos Crt word A s U hsmall hgeo hpass hprod (mem_range.mp hW) hP hn)
    · exact hslots
  have hsum := sum_le_sum (s := range top) hcap
  have htotal := rectCapacity_total A h s E U d (by omega) (by omega)
  change (∑ W ∈ range top, rectCapacity A h s E U d W) + rectGain A h s E U d =
    area U * shapeSum s (fun q j => top + j - q * (131071 - h)) at htotal
  omega

end
end KoalaTwoTerminal

#print axioms KoalaTwoTerminal.lift_dvd
#print axioms KoalaTwoTerminal.count_of_two_traces
#print axioms KoalaTwoTerminal.rectLoss_of_dvd
