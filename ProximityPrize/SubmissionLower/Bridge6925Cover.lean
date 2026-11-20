import ProximityPrize.SubmissionLower.Bridge6925Loss
import ProximityPrize.SubmissionLower.Bridge6925Pairs
import ProximityPrize.SubmissionLower.Fast076
set_option Elab.async false
section PackSource_P0_10RSplit
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
set_option maxRecDepth 4000
set_option maxSynthPendingDepth 8

namespace P0_10R

noncomputable section

section

open Bridge
open P0 (AnchorModel AnchoredFamily K lowCutoff highPrefix)
open P0_10 (BufferedPair JetSource freeShape movingShape fullShape)
open K1_14 (Banks Jet Equation jetAt)
open K1_14_2 (Ambient ODE toJet fixedAt)
open K1_14_2_2 (Active FixedPart Fits mass dual fixedOn orderOn RowCaps)
open K1_14_3 (Surface Parent NoMovingCommon)
open scoped Classical

/-- Cover the reserve-zero input by proper residual and compatibility components
after the fixed, seed-only, nondominant-seed and constant-ordinate exits. -/
def c1 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    lowCutoff + 1 ≤ M.overhead → M.overhead ≤ 3554 → M.shift ∉ Γ →
    ∀ P Q : Jet, P ≠ 0 → Q ≠ 0 → RowCaps P (freeShape M.overhead 0) →
    RowCaps Q (movingShape M.overhead 0) → NoMovingCommon P Q →
    ∀ A : FixedPart P (freeShape M.overhead 0), ∀ B : FixedPart Q (movingShape M.overhead 0),
    (∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 ∧
      jetAt Q (M.label γ) (F.scalar γ) = 0) →
    Nonempty (InitialCover F P Q A.equation B.equation)

/-- Sixfold buffered contact bounds the rank-one exit and the subsequent
doubly dominant inventory by the respective mixed section lengths. -/
def c2 : Prop :=
  ∀ (w : ℤ), lowCutoff + 1 ≤ w → w ≤ 3554 →
    ∀ (rows : Banks) (pair : BufferedPair w rows 1),
    RowCaps pair.free (freeShape w 1) → RowCaps pair.moving (movingShape w 1) →
    ∀ A : FixedPart pair.free (freeShape w 1), ∀ B : FixedPart pair.moving (movingShape w 1),
    ∀ S : Finset (Ideal Ambient), Fits S initialCap →
    (∀ I ∈ S, Active I ∧ Bridge.PairPass pair I ∧
      ¬ fixedOn A.equation I ∧ ¬ fixedOn B.equation I ∧
      orderOn I pair.free 7 ∧ orderOn I pair.moving 7) →
    mass S 1 ≤ 63777 ∧ mass S 2 ≤ 350344 ∧ Fits (S.filter dual) reserveFiveCap

def lateMass : Prop :=
  ∀ (w : ℤ), lowCutoff + 1 ≤ w → w ≤ 3554 →
    ∀ (rows : Banks) (pair : BufferedPair w rows 2),
    RowCaps pair.free (freeShape w 2) → RowCaps pair.moving (movingShape w 2) →
    ∀ A : FixedPart pair.free (freeShape w 2), ∀ B : FixedPart pair.moving (movingShape w 2),
    ∀ S : Finset (Ideal Ambient), Fits S initialCap →
    (∀ I ∈ S, Active I ∧ Bridge.PairPass pair I ∧
      ¬ fixedOn A.equation I ∧ ¬ fixedOn B.equation I ∧
      orderOn I pair.free 26 ∧ orderOn I pair.moving 26) →
    Fits (S.filter dual) lateCap

/-- The full terminal rank floor precludes divisibility at seven distinct ordinates. -/
def c3 : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    lowCutoff + 1 ≤ M.overhead → M.overhead ≤ 3554 →
    ∀ rows, JetSource M F rows → ∀ f : Equation, f ≠ 0 →
    FullDivisibility M.overhead rows f → f.natDegree ≤ 12

end

end
end P0_10R
namespace P0_10R.Bridge

noncomputable section

open P0 (AnchorModel AnchoredFamily K lowCutoff highPrefix)
open P0_10 (BufferedPair JetSource freeShape movingShape fullShape)
open K1_14 (Banks Jet Equation jetAt)
open K1_14_2 (Ambient ODE toJet fixedAt)
open K1_14_2_2 (Active FixedPart Fits mass dual fixedOn orderOn RowCaps)
open K1_14_3 (Surface Parent NoMovingCommon)
open scoped Classical

private theorem fixed_group_count {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    (hw : M.overhead ≤ 3554) {G : ODE} {B J : ℕ}
    (hc : K1_14_2_2.ODECaps G B J) (hb : 2 ≤ B) (hp : B < P0.p) (hj : J ≤ B) :
    (Γ.filter fun γ => fixedAt G (F.scalar γ) = 0).card ≤ fixedPrice B J := by
  exact fixed_count M F hw _ (Finset.filter_subset _ _) B J hb hp hj
    ⟨G, hc, fun _ hγ => (Finset.mem_filter.mp hγ).2⟩

private theorem card_union_bound {A B : Finset K} {a b : ℕ}
    (ha : A.card ≤ a) (hb : B.card ≤ b) : (A ∪ B).card ≤ a+b :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add ha hb)

theorem cover (h1 : c1) (h2 : c2) (nextMass : lateMass) (h3 : c3) :
    ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    lowCutoff + 1 ≤ M.overhead → M.overhead ≤ 3554 → M.shift ∉ Γ →
    ∀ rows, JetSource M F rows →
    ∀ pairs : ∀ i : Fin 3, BufferedPair M.overhead rows i, P0_10R.PrefixCover M F pairs := by
  classical
  intro u del M Γ F hlo hhi hshift rows src pairs
  let P := pairs 0
  let Q := pairs 1
  let E := pairs 2
  have hp₀ := src.shape _ (free_scheduled M.overhead 0) _ _ P.free_mem
  have hq₀ := src.shape _ (moving_scheduled M.overhead 0) _ _ P.moving_mem
  have hp₅ := src.shape _ (free_scheduled M.overhead 1) _ _ Q.free_mem
  have hq₅ := src.shape _ (moving_scheduled M.overhead 1) _ _ Q.moving_mem
  obtain ⟨A₀⟩ := K1_14_2_2_1.proof _ _ P.free_ne hp₀
  obtain ⟨B₀⟩ := K1_14_2_2_1.proof _ _ P.moving_ne hq₀
  obtain ⟨A₅⟩ := K1_14_2_2_1.proof _ _ Q.free_ne hp₅
  obtain ⟨B₅⟩ := K1_14_2_2_1.proof _ _ Q.moving_ne hq₅
  have hPE := src.shape _ (free_scheduled M.overhead 2) _ _ E.free_mem
  have hQE := src.shape _ (moving_scheduled M.overhead 2) _ _ E.moving_mem
  obtain ⟨Af⟩ := K1_14_2_2_1.proof _ _ E.free_ne hPE
  obtain ⟨Bf⟩ := K1_14_2_2_1.proof _ _ E.moving_ne hQE
  obtain ⟨initial⟩ := h1 u del M Γ F hlo hhi hshift P.free P.moving P.free_ne P.moving_ne
    hp₀ hq₀ P.no_moving A₀ B₀ (buffered_zero src hhi 0 P)
  let A := initial.parents
  let S := A.filter fun I => PairPass Q I ∧ ¬ fixedOn A₅.equation I ∧ ¬ fixedOn B₅.equation I
  let B := S.filter dual
  let D := B.filter fun I => PairPass E I ∧ ¬ fixedOn Af.equation I ∧ ¬ fixedOn Bf.equation I
  let C := D.filter (BankPass rows (fullShape M.overhead))
  have hSA : S ⊆ A := Finset.filter_subset _ _
  have hBS : B ⊆ S := Finset.filter_subset _ _
  have hDB : D ⊆ B := Finset.filter_subset _ _
  have hCB : C ⊆ B := (Finset.filter_subset _ _).trans hDB
  have hBA : B ⊆ A := hBS.trans hSA
  obtain ⟨hord, hmix, hBm⟩ := h2 M.overhead hlo hhi rows Q hp₅ hq₅ A₅ B₅ S
    (K1_14_2_2.fits_mono hSA initial.masses) (by
      intro I hI
      obtain ⟨hA, hpass, hfree, hmove⟩ := Finset.mem_filter.mp hI
      have hI' := initial.active I hA
      exact ⟨hI', hpass, hfree, hmove,
        buffered_order src hhi (Or.inl rfl) hI' hpass.1 Q.free_mem,
        buffered_order src hhi (Or.inr rfl) hI' hpass.2.1 Q.moving_mem⟩)
  have hDdual : D ⊆ D.filter dual := by
    intro I hi
    exact Finset.mem_filter.mpr ⟨hi,(Finset.mem_filter.mp (hDB hi)).2⟩
  have hdCap : Fits D lateCap := K1_14_2_2.fits_mono hDdual <|
    nextMass M.overhead hlo hhi rows E hPE hQE Af Bf D
      (K1_14_2_2.fits_mono (hDB.trans hBA) initial.masses) (by
        intro I hI
        obtain ⟨hb,hpass,hf,hg⟩ := Finset.mem_filter.mp hI
        have active := initial.active I (hBA hb)
        exact ⟨active,hpass,hf,hg,
          late_order src hhi (Or.inl rfl) active hpass.1 E.free_mem,
          late_order src hhi (Or.inr rfl) active hpass.2.1 E.moving_mem⟩)
  let R := S.filter fun I => ¬ dual I
  have hRS : R ⊆ S := Finset.filter_subset _ _
  obtain ⟨G, hG, hGon⟩ := rank_equation R
    (fun I hI => ⟨initial.active I (hSA (hRS hI)), (Finset.mem_filter.mp hI).2⟩)
    ((K1_14_2_2.mass_mono hRS 1).trans hord) ((K1_14_2_2.mass_mono hRS 2).trans hmix)
  let U := A.filter fun I => ¬ PairPass Q I
  let V := B \ C
  have hU : U ⊆ A \ B := by
    intro I hI
    obtain ⟨ha, hfail⟩ := Finset.mem_filter.mp hI
    exact Finset.mem_sdiff.mpr ⟨ha, fun hb => hfail (Finset.mem_filter.mp (hBS hb)).2.1⟩
  have hV : V ⊆ B := Finset.sdiff_subset
  obtain ⟨C₅, hC₅, hcover₅⟩ := combined_cuts U stageFiveShape (by decide)
    (fun I hI => initial.active I (Finset.mem_filter.mp hI).1)
    (fun I hI => failed_pair src hhi Q (Finset.mem_filter.mp hI).2)
  let Vm := B.filter fun I => ¬ PairPass E I
  let Ve := D \ C
  have hVm : Vm ⊆ B \ D := by
    intro I hm
    obtain ⟨hb,hfail⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_sdiff.mpr ⟨hb,fun h => hfail (Finset.mem_filter.mp h).2.1⟩
  have hVe : Ve ⊆ D := Finset.sdiff_subset
  obtain ⟨Cm, cm, coverM⟩ := combined_cuts Vm stageLateShape (by decide)
    (fun I hI => initial.active I (hBA (Finset.mem_filter.mp hI).1))
    (fun I hI => failed_late_pair src hhi E (Finset.mem_filter.mp hI).2)
  obtain ⟨Ce, ce, coverE⟩ := combined_cuts Ve terminalFullShape (by decide)
    (fun I hI => initial.active I (hBA (hDB (hVe hI)))) (by
      intro I hI
      obtain ⟨hb, hnot⟩ := Finset.mem_sdiff.mp hI
      exact failed_terminal src hhi (fun h => hnot (Finset.mem_filter.mpr ⟨hb, h⟩)))
  let fixed₄ := Γ.filter fun γ => fixedAt Af.equation (F.scalar γ) = 0
  let fixed₅ := Γ.filter fun γ => fixedAt Bf.equation (F.scalar γ) = 0
  have fshape : freeShape M.overhead 2 = ⟨230,319,66,3650⟩ := by rw [freeShape,ite_eq_left hhi]; rfl
  have mshape := moving_late M.overhead hhi
  have paid₄ : fixed₄.card ≤ fixedPrice 319 66 :=
    fixed_group_count hhi (by simpa only [fshape] using Af.equation_caps) (by decide) (by decide) (by decide)
  have paid₅ : fixed₅.card ≤ fixedPrice 837 168 :=
    fixed_group_count hhi (by simpa only [mshape,stageLateShape] using Bf.equation_caps) (by decide) (by decide) (by decide)
  let Cₜ : K1_14_2_2.CutCover :=
    ⟨(Cm.direct ∪ Ce.direct) ∪ (fixed₄ ∪ fixed₅), Cm.curves ∪ Ce.curves,
      fun I h => (Finset.mem_union.mp h).elim (Cm.geometric I) (Ce.geometric I)⟩
  have hCₜ (fee : Fin 3) : Cₜ.cost fee ≤
      K1_14_2_2.dot (K1_14_2_2.weight stageLateShape fee) (mass Vm) +
      K1_14_2_2.dot (K1_14_2_2.weight terminalFullShape fee) (mass Ve) + extraFee fee := by
    fin_cases fee
    · have h := Nat.add_le_add (cm 0) (ce 0)
      apply Nat.le_trans _ (Nat.le_add_right _ (extraFee 0))
      exact (K1_14_2_2.sum_union_le _ _ _).trans h
    · have h := Nat.add_le_add (cm 1) (ce 1)
      apply Nat.le_trans _ (Nat.le_add_right _ (extraFee 1))
      exact (K1_14_2_2.sum_union_le _ _ _).trans h
    · exact card_union_bound (card_union_bound (cm 2) (ce 2)) (card_union_bound paid₄ paid₅)
  have hcoverₜ (γ) (hΓ : γ ∈ Γ) (hit : ∃ I ∈ V, OnParent F I γ) :
      γ ∈ Cₜ.direct ∨ ∃ I ∈ Cₜ.curves, OnParent F I γ := by
    obtain ⟨I, hI, hm⟩ := hit
    obtain ⟨hb, hn⟩ := Finset.mem_sdiff.mp hI
    by_cases hpass : PairPass E I
    · by_cases hf : fixedOn Af.equation I
      · left
        exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hΓ,fixed_zero hm hf⟩))
      by_cases hg : fixedOn Bf.equation I
      · left
        exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hΓ,fixed_zero hm hg⟩))
      have hd : I ∈ D := Finset.mem_filter.mpr ⟨hb,hpass,hf,hg⟩
      rcases coverE γ hΓ ⟨I,Finset.mem_sdiff.mpr ⟨hd,hn⟩,hm⟩ with h | ⟨J,hj,hmark⟩
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_right _ h))
      · exact Or.inr ⟨J,Finset.mem_union_right _ hj,hmark⟩
    · rcases coverM γ hΓ ⟨I,Finset.mem_filter.mpr ⟨hb,hpass⟩,hm⟩ with h | ⟨J,hj,hmark⟩
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      · exact Or.inr ⟨J,Finset.mem_union_left _ hj,hmark⟩
  obtain ⟨hD, hH, hconst⟩ := loss_bounds A B D U Vm Ve hBA hDB hU hVm hVe initial.masses hBm hdCap
  let curves := C₅.curves ∪ Cₜ.curves
  have massD : K1_14_2_2.curveSeedMass curves ≤ lossSeedCap :=
    (K1_14_2_2.sum_union_le _ _ _).trans ((Nat.add_le_add (hC₅ 0) (hCₜ 0)).trans hD)
  have massH : K1_14_2_2.curveYMass curves ≤ lossYCap :=
    (K1_14_2_2.sum_union_le _ _ _).trans ((Nat.add_le_add (hC₅ 1) (hCₜ 1)).trans hH)
  let lost := Γ.filter fun γ => ∃ I ∈ curves, OnParent F I γ
  have lost_paid : lost.card ≤ curveFee :=
    curve_count root_tariff M F hhi lost (Finset.filter_subset _ _) curves
      (fun I hI => (Finset.mem_union.mp hI).elim (C₅.geometric I) (Cₜ.geometric I))
      massD massH (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  let fixed₀ := Γ.filter fun γ => fixedAt A₀.equation (F.scalar γ) = 0
  let fixed₁ := Γ.filter fun γ => fixedAt B₀.equation (F.scalar γ) = 0
  let fixed₂ := Γ.filter fun γ => fixedAt A₅.equation (F.scalar γ) = 0
  let fixed₃ := Γ.filter fun γ => fixedAt B₅.equation (F.scalar γ) = 0
  let rank := Γ.filter fun γ => fixedAt G (F.scalar γ) = 0
  have shape₀ : freeShape M.overhead 0 = ⟨55,76,16,1299⟩ := by
    rw [freeShape, ite_eq_left hhi]
    rfl
  have shape₁ : movingShape M.overhead 0 = ⟨160,222,46,7106⟩ := by
    rw [movingShape, ite_eq_left hhi]
    rfl
  have shape₂ : freeShape M.overhead 1 = ⟨91,126,27,1931⟩ := by
    rw [freeShape, ite_eq_left hhi]
    rfl
  have shape₃ := moving_five M.overhead hhi
  have fixed₀_paid : fixed₀.card ≤ fixedPrice 76 16 :=
    fixed_group_count hhi (by simpa only [shape₀] using A₀.equation_caps)
      (by decide) (by decide) (by decide)
  have fixed₁_paid : fixed₁.card ≤ fixedPrice 222 46 :=
    fixed_group_count hhi (by simpa only [shape₁] using B₀.equation_caps)
      (by decide) (by decide) (by decide)
  have fixed₂_paid : fixed₂.card ≤ fixedPrice 126 27 :=
    fixed_group_count hhi (by simpa only [shape₂] using A₅.equation_caps)
      (by decide) (by decide) (by decide)
  have fixed₃_paid : fixed₃.card ≤ fixedPrice 369 77 :=
    fixed_group_count hhi (by simpa only [shape₃, stageFiveShape] using B₅.equation_caps)
      (by decide) (by decide) (by decide)
  have rank_paid : rank.card ≤ fixedPrice 350344 63777 :=
    fixed_group_count hhi hG (by decide) (by decide) (by decide)
  let keep := Γ.filter fun γ => ∃ I ∈ C, OnParent F I γ
  let paid := initial.direct ∪ fixed₀ ∪ fixed₁ ∪ fixed₂ ∪ fixed₃ ∪ rank ∪
    (C₅.direct ∪ Cₜ.direct) ∪ lost
  have hpaid : paid.card ≤ highPrefix M.overhead := by
    have hconst' := (Nat.add_le_add (hC₅ 2) (hCₜ 2)).trans hconst
    have hcst : (C₅.direct ∪ Cₜ.direct).card ≤ constantFee :=
      (Finset.card_union_le _ _).trans hconst'
    calc
      _ ≤ initialFee + fixedPrice 76 16 + fixedPrice 222 46 + fixedPrice 126 27 +
          fixedPrice 369 77 + fixedPrice 350344 63777 + constantFee + curveFee := by
        exact card_union_bound
          (card_union_bound
            (card_union_bound
              (card_union_bound
                (card_union_bound
                  (card_union_bound
                    (card_union_bound initial.paid fixed₀_paid) fixed₁_paid)
                  fixed₂_paid)
                fixed₃_paid)
              rank_paid)
            hcst)
          lost_paid
      _ ≤ _ := prefix_ledger _ hhi
  have hremove : Γ \ keep ⊆ paid := by
    intro γ hγ
    obtain ⟨hΓ, hnot⟩ := Finset.mem_sdiff.mp hγ
    have fail_kept (I : Ideal Ambient) (hI : I ∈ C) (hm : OnParent F I γ) : False :=
      hnot (Finset.mem_filter.mpr ⟨hΓ, I, hI, hm⟩)
    have from_five (I : Ideal Ambient) (hI : I ∈ U) (hm : OnParent F I γ) : γ ∈ paid := by
      rcases hcover₅ γ hΓ ⟨I, hI, hm⟩ with hd | ⟨J, hJ, hmark⟩
      · simp only [paid, Finset.mem_union]; exact (Or.inl (Or.inr (Or.inl hd)))
      · have hl : γ ∈ lost :=
          Finset.mem_filter.mpr ⟨hΓ, J, Finset.mem_union_left _ hJ, hmark⟩
        exact Finset.mem_union_right _ hl
    have from_terminal (I : Ideal Ambient) (hI : I ∈ V) (hm : OnParent F I γ) : γ ∈ paid := by
      rcases hcoverₜ γ hΓ ⟨I, hI, hm⟩ with hd | ⟨J, hJ, hmark⟩
      · simp only [paid, Finset.mem_union]; exact (Or.inl (Or.inr (Or.inr hd)))
      · have hl : γ ∈ lost :=
          Finset.mem_filter.mpr ⟨hΓ, J, Finset.mem_union_right _ hJ, hmark⟩
        exact Finset.mem_union_right _ hl
    rcases initial.cover γ hΓ with hd | hf | hg | ⟨I, hI, hm⟩
    · simp only [paid, Finset.mem_union]; exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hd)))))))
    · have h : γ ∈ fixed₀ := Finset.mem_filter.mpr ⟨hΓ, hf⟩
      simp only [paid, Finset.mem_union]; exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))
    · have h : γ ∈ fixed₁ := Finset.mem_filter.mpr ⟨hΓ, hg⟩
      simp only [paid, Finset.mem_union]; exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
    · by_cases ht : PairPass Q I
      · by_cases hf : fixedOn A₅.equation I
        · have h : γ ∈ fixed₂ := Finset.mem_filter.mpr ⟨hΓ, fixed_zero hm hf⟩
          simp only [paid, Finset.mem_union]; exact (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
        by_cases hg : fixedOn B₅.equation I
        · have h : γ ∈ fixed₃ := Finset.mem_filter.mpr ⟨hΓ, fixed_zero hm hg⟩
          simp only [paid, Finset.mem_union]; exact (Or.inl (Or.inl (Or.inl (Or.inr h))))
        have hs : I ∈ S := Finset.mem_filter.mpr ⟨hI, ht, hf, hg⟩
        by_cases hj : dual I
        · have hb : I ∈ B := Finset.mem_filter.mpr ⟨hs, hj⟩
          by_cases hc : I ∈ C
          · exact (fail_kept I hc hm).elim
          · exact from_terminal I (Finset.mem_sdiff.mpr ⟨hb, hc⟩) hm
        · have h : γ ∈ rank :=
            Finset.mem_filter.mpr ⟨hΓ, fixed_zero hm (hGon I (Finset.mem_filter.mpr ⟨hs, hj⟩))⟩
          simp only [paid, Finset.mem_union]; exact (Or.inl (Or.inl (Or.inr h)))
      · exact from_five I (Finset.mem_filter.mpr ⟨hI, ht⟩) hm
  have hprice := (Finset.card_le_card hremove).trans hpaid
  by_cases he : keep = ∅
  · exact Or.inl (by simpa [he] using hprice)
  have hCA : C ⊆ A := hCB.trans hBA
  let toSurface (I : ↥C) := surfaceOf I.1 (initial.active _ (hCA I.2)).prime
  let parents := C.attach.image toSurface
  have hparents : parents.Nonempty := by
    obtain ⟨γ, hg⟩ := Finset.nonempty_iff_ne_empty.mpr he
    obtain ⟨I, hi, _⟩ := (Finset.mem_filter.mp hg).2
    exact ⟨toSurface ⟨I, hi⟩, Finset.mem_image_of_mem _ (Finset.mem_attach _ _)⟩
  have hgeometry : ∀ q ∈ parents, Parent q := by
    intro q hq
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hq
    exact parent_of_dual (initial.active _ (hCA I.2)) (initial.height_two _ (hCA I.2))
      (Finset.mem_filter.mp (hCB I.2)).2
  have ht : ∀ q ∈ parents, P0_10.BankVanishes rows (fullShape M.overhead) q := by
    intro q hq
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp I.2).2
  obtain ⟨f, hf, hfull, hdiv⟩ := terminal_product src hlo hhi parents hparents hgeometry ht
  have hne : f ≠ 0 := by
    rintro rfl
    simpa using hf.positive
  have hdeg := h3 u del M Γ F hlo hhi rows src f hne hfull
  refine Or.inr ⟨{
    kept := keep
    subset := Finset.filter_subset _ _
    paid := hprice
    parents := parents
    geometric := hgeometry
    initial := ?_
    survives := ?_
    terminal := ht
    covers := ?_
    equation := f
    projected := hf
    y_bound := ?_
    divides := hdiv }⟩
  · intro q hq
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hq
    exact initial.initial _ (hCA I.2)
  · intro q hq
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hq
    have hpass : PairPass Q I.1 := (Finset.mem_filter.mp (hBS (hCB I.2))).2.1
    exact surface_pass (initial.active _ (hCA I.2)).prime hpass
  · intro γ hγ
    obtain ⟨I, hi, hm⟩ := (Finset.mem_filter.mp hγ).2
    exact ⟨toSurface ⟨I, hi⟩, Finset.mem_image_of_mem _ (Finset.mem_attach _ _), on_surface _ hm⟩
  · simpa only [P0_10.band, H21.band, ite_eq_left hhi] using hdeg

end
end P0_10R.Bridge

end PackSource_P0_10RSplit
section PackSource_P0_10R_1Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000

namespace P0_10R_1

noncomputable section

open P0 (AnchorModel AnchoredFamily K p)
open P0_10R.Bridge (InitialCover OnParent initialCap initialE₀ initialFee)
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open K1_14_3 (SeedCover seed_count joinCovers joinCovers_degree joinCovers_points
  joinCovers_covers scalar_atX_injective)
open scoped BigOperators Classical
open private K1_14_2_2_2_3.jetEquiv jetEquiv_apply from ProximityPrize.SubmissionLower.Fast051
open private properPair_height from ProximityPrize.SubmissionLower.Fast076

private theorem section_bound : K1_14_2_2_2.c4 :=
  K1_14_2_2_2_4.of_children K1_14_2_2_2_4_1.proof K1_14_2_2_2_4_2.proof K1_14_2_2_2_4_3.proof

private theorem seed_projection : K1_14_2_2_2.c6 :=
  K1_14_2_2_2_6.of_children K1_14_2_2_2_6_1.proof K1_14_2_2_2_6_2.proof

private theorem height_le {I : Ideal Ambient} (hI : I.IsPrime)
    (hdim : ringKrullDim (CoordinateRing I) = 2) : I.height ≤ 2 := by
  let x : PrimeSpectrum Ambient := ⟨I, hI⟩
  have hc : Order.coheight x = 2 := by
    rw [ringKrullDim_quotient] at hdim
    change Order.krullDim (Set.Ici x) = 2 at hdim
    rw [← Order.coheight_eq_krullDim_Ici] at hdim
    exact WithBot.coe_injective hdim
  have hd : ringKrullDim Ambient = 4 := by simp [ringKrullDim_eq_zero_of_field]
  have hh : (↑(Order.height x + Order.coheight x) : WithBot ℕ∞) ≤ ringKrullDim Ambient := by
    rw [ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.mpr (le_iSup (fun y : PrimeSpectrum Ambient =>
      Order.height y + Order.coheight y) x)
  rw [hc, ← x.height_eq_orderHeight, hd] at hh
  have hh' : I.height + 2 ≤ (2 : ℕ∞) + 2 := WithBot.coe_le_coe.mp hh
  exact (ENat.add_le_add_iff_right (by simp : (2 : ℕ∞) ≠ ⊤)).mp hh'

private theorem component_height {P Q : Jet} {I : Ideal Ambient} (hp : ProperPair P Q)
    (hI : I.IsPrime) (hdim : ringKrullDim (CoordinateRing I) = 2)
    (hP : toJet P ∈ I) (hQ : toJet Q ∈ I) : I.height = 2 := by
  let J := I.comap K1_14_2_2_2_3.jetEquiv.toRingHom
  let : J.IsPrime := hI.comap _
  have hP' : P ∈ J := by change K1_14_2_2_2_3.jetEquiv P ∈ I; rwa [jetEquiv_apply]
  have hQ' : Q ∈ J := by change K1_14_2_2_2_3.jetEquiv Q ∈ I; rwa [jetEquiv_apply]
  exact le_antisymm (height_le hI hdim)
    ((K1_14_2_2_2_3.jetEquiv.height_comap I) ▸ properPair_height hp J hP' hQ')

private theorem mem_of_row_dvd {I : Ideal Ambient} {P Q : Jet} (hP : toJet P ∈ I)
    (hd : P ∣ Q) : toJet Q ∈ I :=
  I.mem_of_dvd (map_dvd toJet hd) hP

private theorem ordinary_cover (f : Equation) (hi : Irreducible f) (hd : 0 < f.natDegree)
    (hp : f.natDegree < p) :
    ∃ S : Finset (Ideal Ambient),
      (∀ I ∈ S, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ I.height = 2 ∧
        FiniteSections I ∧ toJet (C f) ∈ I) ∧
      Fits S (ordinaryBudget (ordinarySeedDegree f) f.natDegree) ∧
      ∀ z R, atMark f z R = 0 → ∃ I ∈ S, OnJet I z R := by
  obtain ⟨g, a, hclear, hproper, hfCaps, hgCaps⟩ := K1_14_3_4_2.proof f hi hd hp
  obtain ⟨S, hS, hcover⟩ := K1_14_2_2_2_3.proof _ _ hproper
  obtain ⟨hfinite, hfits⟩ := section_bound _ _ hproper
    ⟨0, f.natDegree, 0, ordinarySeedDegree f⟩ ⟨0, f.natDegree, 1, ordinarySeedDegree f⟩
    (Nat.zero_le _) hd hfCaps hgCaps S hS
  refine ⟨S, ?_, ?_, ?_⟩
  · intro I hI
    obtain ⟨hprime, hdim, hrow, hcut⟩ := hS I hI
    exact ⟨hprime, hdim, component_height hproper hprime hdim hrow hcut, hfinite I hI, hrow⟩
  · intro k
    have h := hfits k
    fin_cases k <;> simpa [residualBudget, ordinaryBudget, two_mul, Nat.add_mul] using h
  · intro z R hz
    exact hcover z R (by simpa [jetAt, atMark] using hz) (K1_14_3R.chainCutter_zero hclear hz)

private theorem cover_count {u del} (M : AnchorModel u del) (T : Finset K)
    (C : SeedCover) (U E : ℕ) (hU : C.curve.totalDegree ≤ U)
    (hp : U < p) (hE : C.points.card ≤ E) (hcov : ∀ γ ∈ T, C.Covers (M.label γ)) :
    T.card ≤ (p+1)*U + E := by
  have hlabel : Function.Injective M.label := fun _ _ h => sub_left_inj.mp h
  exact (seed_count hlabel.injOn C (hU.trans_lt hp) hcov).trans
    (Nat.add_le_add (Nat.mul_le_mul_left _ hU) hE)

/-- The reserve-zero bridge cover using the proper residual and ordinary
chain-rule components, with the three direct projection charges. -/
theorem proof : P0_10R.c1 := by
  classical
  intro u del M Γ F _ hw _ P Q hP hQ hPc hQc hnc A B hrows
  have hfshape : P0_10.freeShape M.overhead 0 = freeZero := by
    simp [P0_10.freeShape, hw, freeZero]
  have hmshape : P0_10.movingShape M.overhead 0 = movingZero := by
    simp [P0_10.movingShape, hw, movingZero]
  revert hPc hQc A B
  rw [hfshape, hmshape]
  intro hPc hQc A B
  obtain ⟨prep⟩ := prepare hP hQ hPc hQc hnc A B
  obtain ⟨residual, hresidual, hresCover⟩ := K1_14_2_2_2_3.proof _ _ prep.proper
  obtain ⟨hresFinite, hresCap⟩ := section_bound _ _ prep.proper _ _
    (min_le_right _ _) (min_le_right _ _) prep.free_caps prep.moving_caps residual hresidual
  have ordinary_exists (f : Equation) (hf : f ∈ prep.ordinary) :=
    ordinary_cover f (prep.ordinary_factors f hf).1 (prep.ordinary_factors f hf).2
      (((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans prep.ordinary_y).trans_lt
        (prep.gcdY_le.trans_lt (by decide : 76 < p)))
  let ordinary (f : Equation) : Finset (Ideal Ambient) :=
    if hf : f ∈ prep.ordinary then Classical.choose (ordinary_exists f hf) else ∅
  have hord (f : Equation) (hf : f ∈ prep.ordinary) :
      (∀ I ∈ ordinary f, I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ I.height = 2 ∧
        FiniteSections I ∧ toJet (C f) ∈ I) ∧
      Fits (ordinary f) (ordinaryBudget (ordinarySeedDegree f) f.natDegree) ∧
      ∀ z R, atMark f z R = 0 → ∃ I ∈ ordinary f, OnJet I z R := by
    simpa only [ordinary, dite_eq_left hf] using Classical.choose_spec (ordinary_exists f hf)
  let S := residual ∪ prep.ordinary.biUnion ordinary
  have hgeom (I : Ideal Ambient) (hi : I ∈ S) :
      I.IsPrime ∧ ringKrullDim (CoordinateRing I) = 2 ∧ I.height = 2 ∧
        FiniteSections I ∧ toJet P ∈ I ∧ toJet Q ∈ I := by
    rcases Finset.mem_union.mp hi with hr | ho
    · obtain ⟨hprime, hdim, hfree, hmoving⟩ := hresidual I hr
      exact ⟨hprime, hdim, component_height prep.proper hprime hdim hfree hmoving,
        hresFinite I hr, mem_of_row_dvd hfree prep.free_dvd, mem_of_row_dvd hmoving prep.moving_dvd⟩
    · obtain ⟨f, hf, hif⟩ := Finset.mem_biUnion.mp ho
      obtain ⟨hprime, hdim, hheight, hfin, hrow⟩ := (hord f hf).1 I hif
      obtain ⟨hP', hQ'⟩ := prep.ordinary_dvd f hf
      exact ⟨hprime, hdim, hheight, hfin, mem_of_row_dvd hrow hP', mem_of_row_dvd hrow hQ'⟩
  have hfit : Fits S initialCap := by
    intro k
    have hOrdCap : mass (prep.ordinary.biUnion ordinary) k ≤ ordinaryBudget prep.gcdSeed prep.gcdY k := by
      calc
        _ ≤ ∑ f ∈ prep.ordinary, mass (ordinary f) k :=
          sum_biUnion_le prep.ordinary ordinary (fun I => sectionDegree I k)
        _ ≤ ∑ f ∈ prep.ordinary, ordinaryBudget (ordinarySeedDegree f) f.natDegree k :=
          Finset.sum_le_sum fun f hf => (hord f hf).2.1 k
        _ ≤ _ := ordinary_sum _ _ _ prep.ordinary_seed prep.ordinary_y k
    exact (sum_union_le (fun I => sectionDegree I k) _ _).trans
      ((Nat.add_le_add (hresCap k) hOrdCap).trans (ledger _ _ prep.gcdSeed_le prep.gcdY_le k))
  let noSeeds := S.filter (fun I => sectionDegree I 0 = 0)
  let constY := S.filter (fun I => 0 < sectionDegree I 0 ∧
    ¬ Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl))
  let parents := S.filter (fun I => 0 < sectionDegree I 0 ∧
    Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl))
  have hparents (I : Ideal Ambient) (hi : I ∈ parents) : Active I := by
    obtain ⟨hI, ha, hy⟩ := Finset.mem_filter.mp hi
    obtain ⟨hprime, hdim, _, hfinite, _⟩ := hgeom I hI
    have hbudget (k : Fin 4) : initialCap k < p := by fin_cases k <;> decide
    have hsmall (k : Fin 4) : sectionDegree I k < p :=
      (length_le_mass hI k).trans_lt ((hfit k).trans_lt (hbudget k))
    exact ⟨hprime, hdim, hfinite.seeds, hfinite.ordinate, hfinite.mixed, hfinite.jets,
      ⟨ha, hsmall 0⟩, hsmall 2, hsmall 3, hy⟩
  have seed_exists (I : Ideal Ambient) (hi : I ∈ noSeeds) :
      ∃ C : SeedCover, C.curve.totalDegree ≤ sectionDegree I 2 ∧
        C.points.card ≤ sectionDegree I 3 ∧ ∀ z R, OnJet I z R → C.Covers z := by
    obtain ⟨hI, hz⟩ := Finset.mem_filter.mp hi
    obtain ⟨hprime, hdim, _, hfinite, _⟩ := hgeom I hI
    exact seed_projection I hprime hdim hfinite hz
  let seedImage (I : Ideal Ambient) : SeedCover :=
    if hi : I ∈ noSeeds then Classical.choose (seed_exists I hi) else ⟨1, one_ne_zero, ∅⟩
  have hseedImage (I : Ideal Ambient) (hi : I ∈ noSeeds) :
      (seedImage I).curve.totalDegree ≤ sectionDegree I 2 ∧
      (seedImage I).points.card ≤ sectionDegree I 3 ∧
      ∀ z R, OnJet I z R → (seedImage I).Covers z := by
    simpa only [seedImage, dite_eq_left hi] using Classical.choose_spec (seed_exists I hi)
  let imageCover := joinCovers noSeeds seedImage
  let seedExits := Γ.filter (fun γ => imageCover.Covers (M.label γ))
  have hseedExits : seedExits.card ≤ (p+1)*828434 + initialE₀ := by
    apply cover_count M _ _ _ _ _ (by decide) _ (fun γ hγ => (Finset.mem_filter.mp hγ).2)
    · calc
        _ ≤ ∑ I ∈ noSeeds, (seedImage I).curve.totalDegree := joinCovers_degree _ _
        _ ≤ mass noSeeds 2 := Finset.sum_le_sum (fun I hi => (hseedImage I hi).1)
        _ ≤ mass S 2 := mass_mono (Finset.filter_subset _ _) 2
        _ ≤ _ := hfit 2
    · calc
        _ ≤ ∑ I ∈ noSeeds, (seedImage I).points.card := joinCovers_points _ _
        _ ≤ mass noSeeds 3 := Finset.sum_le_sum (fun I hi => (hseedImage I hi).2.1)
        _ ≤ mass S 3 := mass_mono (Finset.filter_subset _ _) 3
        _ ≤ initialCap 3 := hfit 3
        _ ≤ _ := by decide
  let onY (I : Ideal Ambient) := Γ.filter (OnParent F I)
  let yExits := constY.biUnion onY
  have hyExits : yExits.card ≤ 6312 := by
    calc
      _ ≤ ∑ I ∈ constY, (onY I).card := Finset.card_biUnion_le
      _ ≤ mass constY 0 := by
        apply Finset.sum_le_sum
        intro I hi
        obtain ⟨hI, ha, hy⟩ := Finset.mem_filter.mp hi
        have hcard : (onY I).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro γ hγ δ hδ
          obtain ⟨hg, hgon⟩ := Finset.mem_filter.mp hγ
          obtain ⟨hd, hdon⟩ := Finset.mem_filter.mp hδ
          exact F.distinct hg hd (scalar_atX_injective (ordinate_eq (hgeom I hI).1 hy hgon hdon))
        exact hcard.trans ha
      _ ≤ mass S 0 := mass_mono (Finset.filter_subset _ _) 0
      _ ≤ _ := hfit 0
  let contentCover : SeedCover := ⟨prep.seedContent, prep.seedContent_ne, ∅⟩
  let contentExits := Γ.filter (fun γ => graphEval (M.label γ) prep.seedContent = 0)
  have hcontentExits : contentExits.card ≤ (p+1)*(1299+7106) := by
    have h := cover_count M contentExits contentCover (1299+7106) 0 prep.seedContent_degree
      (by decide) (by simp [contentCover]) (fun γ hγ => Or.inl (Finset.mem_filter.mp hγ).2)
    simpa only [Nat.add_zero] using h
  let direct := (contentExits ∪ seedExits) ∪ yExits
  refine ⟨⟨parents, hparents, fun I hi => (hgeom I (Finset.mem_filter.mp hi).1).2.2.1,
    fun I hi => (hgeom I (Finset.mem_filter.mp hi).1).2.2.2.2,
    fits_mono (Finset.filter_subset _ _) hfit, direct, ?_, ?_⟩⟩
  · calc
      direct.card ≤ (contentExits ∪ seedExits).card + yExits.card := Finset.card_union_le _ _
      _ ≤ contentExits.card + seedExits.card + yExits.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (p+1)*(1299+7106) + ((p+1)*828434 + initialE₀) + 6312 :=
        Nat.add_le_add (Nat.add_le_add hcontentExits hseedExits) hyExits
      _ = initialFee := by unfold initialFee; ac_rfl
  · intro γ hγ
    obtain ⟨hP', hQ'⟩ := hrows γ hγ
    have fromSurface (I : Ideal Ambient) (hi : I ∈ S) (hon : OnParent F I γ) :
        γ ∈ direct ∨ fixedAt A.equation (F.scalar γ) = 0 ∨
          fixedAt B.equation (F.scalar γ) = 0 ∨ ∃ J ∈ parents, OnParent F J γ := by
      by_cases ha : sectionDegree I 0 = 0
      · have hI : I ∈ noSeeds := Finset.mem_filter.mpr ⟨hi, ha⟩
        have hc : imageCover.Covers (M.label γ) := joinCovers_covers hI
          ((hseedImage I hI).2.2 _ _ hon)
        exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hc⟩)))
      · have hpos := Nat.pos_of_ne_zero ha
        by_cases hy : Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl)
        · exact Or.inr (Or.inr (Or.inr ⟨I, Finset.mem_filter.mpr ⟨hi, hpos, hy⟩, hon⟩))
        · have hI : I ∈ constY := Finset.mem_filter.mpr ⟨hi, hpos, hy⟩
          exact Or.inl (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨I, hI, Finset.mem_filter.mpr ⟨hγ, hon⟩⟩))
    rcases prep.cover _ _ hP' hQ' with hg | hh | hc | hr | ⟨f, hf, hz⟩
    · exact Or.inr (Or.inl hg)
    · exact Or.inr (Or.inr (Or.inl hh))
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hc⟩)))
    · obtain ⟨I, hI, hon⟩ := hresCover _ _ hr.1 hr.2
      exact fromSurface I (Finset.mem_union_left _ hI) hon
    · obtain ⟨I, hI, hon⟩ := (hord f hf).2.2 _ _ hz
      exact fromSurface I (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨f, hf, hI⟩)) hon

end
end P0_10R_1
end PackSource_P0_10R_1Proof
section PackSource_P0_10R_2Aux1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace P0_10R_2

noncomputable section

open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_4 Polynomial
open private factor_caps natDegree_zero_of_factors dvd_of_dvd_residual
  toJet_equiv ambientToJet from ProximityPrize.SubmissionLower.Fast071

/-- Shared ordinary factor and residual caps after removing the two fixed parts. -/
structure SharedGcd {P Q : Jet} {s t : Shape} (A : FixedPart P s) (B : FixedPart Q t) where
  ordinary : Equation
  left : Jet
  right : Jet
  ordinary_ne : ordinary ≠ 0
  left_ne : left ≠ 0
  right_ne : right ≠ 0
  left_factor : P = fixedIncl A.equation * (C ordinary * left)
  right_factor : Q = fixedIncl B.equation * (C ordinary * right)
  relativelyPrime : IsRelPrime (toJet left) (toJet right)
  seed_le : seedDegree ordinary ≤ s.U
  ordinate_le : ordinary.natDegree ≤ s.B
  left_caps : RowCaps left (residualShape s (seedDegree ordinary) ordinary.natDegree)
  right_caps : RowCaps right (residualShape t (seedDegree ordinary) ordinary.natDegree)

theorem sharedGcd {P Q : Jet} {s t : Shape} (A : FixedPart P s) (B : FixedPart Q t)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hPs : RowCaps P s) (hQs : RowCaps Q t)
    (hno : K1_14_3.NoMovingCommon P Q) : Nonempty (SharedGcd A B) := by
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid (D := Seeds)
  let : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D := Equation)
  let gcdJet : GCDMonoid Jet := UniqueFactorizationMonoid.toGCDMonoid Jet
  let D : Jet := gcdJet.gcd A.residual B.residual
  obtain ⟨L, R, hL, hR, hrel⟩ := @extract_gcd Jet _ gcdJet A.residual B.residual
  change A.residual = D * L at hL
  change B.residual = D * R at hR
  have hF : P = fixedIncl A.equation * (D * L) :=
    A.factorization.trans (congrArg (fixedIncl A.equation * ·) hL)
  have hG : Q = fixedIncl B.equation * (D * R) :=
    B.factorization.trans (congrArg (fixedIncl B.equation * ·) hR)
  have hFL := right_ne_zero_of_mul (hF ▸ hP)
  have hGR := right_ne_zero_of_mul (hG ▸ hQ)
  have hDne := left_ne_zero_of_mul hFL
  have hDdeg : D.natDegree = 0 := by
    apply natDegree_zero_of_factors
    intro F hIrr hfd
    by_contra hpos
    have hleft := hfd.trans (gcdJet.gcd_dvd_left A.residual B.residual)
    have hright := hfd.trans (gcdJet.gcd_dvd_right A.residual B.residual)
    obtain ⟨G, hG⟩ := hno F hIrr (dvd_of_dvd_residual A hleft)
      (dvd_of_dvd_residual B hright) (Nat.pos_of_ne_zero hpos)
    exact A.stripped G (hG ▸ hIrr) (hG ▸ hleft)
  let H := D.coeff 0
  have hD : D = C H := eq_C_of_natDegree_eq_zero hDdeg
  have hH : H ≠ 0 := fun hz => hDne (by rw [hD, hz, map_zero])
  rw [hD] at hF hG
  obtain ⟨hFu, hFb, hLc⟩ := factor_caps hP hH hPs hF
  obtain ⟨_, _, hRc⟩ := factor_caps hQ hH hQs hG
  have hprime : IsRelPrime (toJet L) (toJet R) := by
    have hr := (@gcd_isUnit_iff_isRelPrime Jet _ gcdJet L R).mp hrel
    rw [toJet_equiv]
    intro E hEL hER
    have h1 : ambientToJet E ∣ L := by
      simpa using map_dvd ambientToJet.toRingHom hEL
    have h2 : ambientToJet E ∣ R := by
      simpa using map_dvd ambientToJet.toRingHom hER
    simpa using (hr h1 h2).map ambientToJet.symm.toRingHom
  exact ⟨⟨H, L, R, hH, right_ne_zero_of_mul hFL, right_ne_zero_of_mul hGR,
    hF, hG, hprime, hFu, hFb, hLc, hRc⟩⟩

end
end P0_10R_2
end PackSource_P0_10R_2Aux1
section PackSource_P0_10R_2Aux2
set_option autoImplicit true
namespace P0_10R_2

noncomputable section

open K1_14 K1_14_2_2_4
open private numerator numerator_bound seedNumerator ordinateNumerator mixedNumerator
  jetsNumerator ordinate_endpoints mixed_seed_endpoints mixed_ordinate_endpoints
  jets_endpoints from ProximityPrize.SubmissionLower.Fast032

def bridgeFree : Shape := ⟨91, 126, 27, 1931⟩
def bridgeMoving : Shape := ⟨266, 369, 77, 11028⟩

end
end P0_10R_2
end PackSource_P0_10R_2Aux2
section PackSource_P0_10R_2Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

namespace P0_10R_2

noncomputable section

open K1 (p)
open K1_14 (Jet)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 K1_14_2_2_4 Polynomial
open scoped Classical
open private cancel_fixed from_paired_bounds from ProximityPrize.SubmissionLower.Pack_K1_14_2_2_4Split

private theorem cancellation : K1_14_2_2_4.c3 :=
  K1_14_2_2_4_3.of_children K1_14_2_2_4_3_1.proof K1_14_2_2_4_3_2.proof

private theorem sections : K1_14_2_2_4.c5 :=
  K1_14_2_2_4_5.of_children K1_14_2_2_4_5_1.proof K1_14_2_2_4_5_2.proof
    K1_14_2_2_4_5_3.proof K1_14_2_2_4_5_4.proof K1_14_2_2_4_5_5.proof

private theorem paired_stage {P Q : Jet}
    {A : FixedPart P bridgeFree} {B : FixedPart Q bridgeMoving} (G : SharedGcd A B)
    (S : Finset (Ideal Ambient)) (square : Bool) (k : Fin 4) (r cap : ℕ)
    (hr : 0 < r) (hrm : r ≤ 7) (hdual : square = true → ∀ I ∈ S, dual I)
    (hpass : ∀ I ∈ S, Active I ∧ K1_14_2_2R.chainCompatible P Q I ∧
      ¬ fixedOn A.equation I ∧ ¬ fixedOn B.equation I ∧
      orderOn I P 7 ∧ orderOn I Q 7)
    (hnum :
      let x := seedDegree G.ordinary
      let z := G.ordinary.natDegree
      let d := if square then (8 - r)^2 else 8 - r
      d * highCap x z k + highScale r k *
        pairCap (residualShape bridgeFree x z) (residualShape bridgeMoving x z) k <
          highScale r k * d * (cap + 1)) :
    mass S k ≤ cap := by
  let x := seedDegree G.ordinary
  let z := G.ordinary.natDegree
  let s := residualShape bridgeFree x z
  let t := residualShape bridgeMoving x z
  let n := 8 - r
  let d := if square then n^2 else n
  have hxp : x < p := G.seed_le.trans_lt (by decide : bridgeFree.U < p)
  have hzp : z < p := G.ordinate_le.trans_lt (by decide : bridgeFree.B < p)
  have hn : 0 < n := by dsimp [n]; omega
  have hd : 0 < d := by
    unfold d
    split
    · exact Nat.pow_pos hn
    · exact hn
  have hh : highScale r k * mass (S.filter (HighOn G.ordinary r)) k ≤ highCap x z k := by
    apply K1_14_2_2R.high_graph_mass K1_14_2_2_4_4.proof sections G.ordinary P Q
      _ r G.ordinary_ne hzp hr
    · refine ⟨fixedIncl A.equation * G.left, G.left_factor.trans ?_⟩
      ring
    · refine ⟨fixedIncl B.equation * G.right, G.right_factor.trans ?_⟩
      ring
    intro I hI
    obtain ⟨hm, hf⟩ := Finset.mem_filter.mp hI
    exact ⟨(hpass I hm).1, (hpass I hm).2.1, hf⟩
  have hl : d * mass (S.filter fun I => ¬ HighOn G.ordinary r I) k ≤ pairCap s t k := by
    apply sections G.left G.right s t _ k d G.left_ne G.right_ne G.relativelyPrime
      (min_le_right _ _) (min_le_right _ _) G.left_caps G.right_caps hd
    intro I hI
    obtain ⟨hm, hf⟩ := Finset.mem_filter.mp hI
    obtain ⟨ha, _, hA, hB, hP, hQ⟩ := hpass I hm
    rw [G.left_factor] at hP
    rw [G.right_factor] at hQ
    have hlP := cancellation G.ordinary G.left I 7 r G.ordinary_ne hxp hzp ha hr hrm hf
      (cancel_fixed ha.prime _ _ 7 hA hP)
    have hlQ := cancellation G.ordinary G.right I 7 r G.ordinary_ne hxp hzp ha hr hrm hf
      (cancel_fixed ha.prime _ _ 7 hB hQ)
    have hlen := K1_14_2_2_4_4.proof G.left G.right I ha n hn hlP hlQ
    refine ⟨ha, fun _ => ?_⟩
    by_cases hIdual : dual I
    · rw [ite_eq_left hIdual] at hlen
      apply le_trans _ hlen
      apply Nat.cast_le.mpr
      unfold d
      split
      · exact le_rfl
      · simpa only [pow_two, mul_one] using Nat.mul_le_mul_left n (show 1 ≤ n by omega)
    · have hs : square ≠ true := fun he => hIdual (hdual he I hm)
      simpa [d, hs, hIdual] using hlen
  exact from_paired_bounds G.ordinary r (highScale r k) d _ _ cap hh hl hnum

theorem proof : P0_10R.c2 := by
  classical
  intro w _ hhi rows pair
  have hf : P0_10.freeShape w 1 = bridgeFree := by
    rw [P0_10.freeShape, ite_eq_left hhi]
    rfl
  have hm : P0_10.movingShape w 1 = bridgeMoving := by
    rw [P0_10.movingShape, ite_eq_left hhi]
    rfl
  rw [hf, hm]
  intro hP hQ A B S _ hpass
  obtain ⟨G⟩ := sharedGcd A B pair.free_ne pair.moving_ne hP hQ pair.no_moving
  let x := seedDegree G.ordinary
  let z := G.ordinary.natDegree
  have hx : x ≤ 1931 := G.seed_le
  have hz : z ≤ 126 := G.ordinate_le
  have hlocal (I) (hI : I ∈ S) :
      Active I ∧ K1_14_2_2R.chainCompatible pair.free pair.moving I ∧
      ¬ fixedOn A.equation I ∧ ¬ fixedOn B.equation I ∧
      orderOn I pair.free 7 ∧ orderOn I pair.moving 7 :=
    ⟨(hpass I hI).1, (hpass I hI).2.1.2.2, (hpass I hI).2.2⟩
  refine ⟨paired_stage G S false 1 1 63777 (by decide) (by decide) (by simp) hlocal
    (PriceReceipt6925.linear_ordinate x z hx hz),
    paired_stage G S false 2 2 350344 (by decide) (by decide) (by simp) hlocal
    (PriceReceipt6925.linear_mixed x z hx hz), ?_⟩
  intro k
  let T := S.filter dual
  have hdual (_ : true = true) (I) (hI : I ∈ T) : dual I := (Finset.mem_filter.mp hI).2
  have hT (I) (hI : I ∈ T) := hlocal I (Finset.mem_filter.mp hI).1
  fin_cases k
  · exact paired_stage G T true 0 1 358 (by decide) (by decide) hdual hT (PriceReceipt6925.reserve_square 0 x z hx hz)
  · exact paired_stage G T true 1 1 9111 (by decide) (by decide) hdual hT (PriceReceipt6925.reserve_square 1 x z hx hz)
  · exact paired_stage G T true 2 3 84082 (by decide) (by decide) hdual hT (PriceReceipt6925.reserve_square 2 x z hx hz)
  · exact paired_stage G T true 3 3 851802 (by decide) (by decide) hdual hT (PriceReceipt6925.reserve_square 3 x z hx hz)

end
end P0_10R_2
end PackSource_P0_10R_2Proof
section PackSource_P0_10R_LateAux1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace P0_10R_Late

noncomputable section

open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_4 Polynomial
open private factor_caps natDegree_zero_of_factors dvd_of_dvd_residual
  toJet_equiv ambientToJet from ProximityPrize.SubmissionLower.Fast071

/-- Shared ordinary factor and residual caps after removing the two fixed parts. -/
structure SharedGcd {P Q : Jet} {s t : Shape} (A : FixedPart P s) (B : FixedPart Q t) where
  ordinary : Equation
  left : Jet
  right : Jet
  ordinary_ne : ordinary ≠ 0
  left_ne : left ≠ 0
  right_ne : right ≠ 0
  left_factor : P = fixedIncl A.equation * (C ordinary * left)
  right_factor : Q = fixedIncl B.equation * (C ordinary * right)
  relativelyPrime : IsRelPrime (toJet left) (toJet right)
  seed_le : seedDegree ordinary ≤ s.U
  ordinate_le : ordinary.natDegree ≤ s.B
  left_caps : RowCaps left (residualShape s (seedDegree ordinary) ordinary.natDegree)
  right_caps : RowCaps right (residualShape t (seedDegree ordinary) ordinary.natDegree)

theorem sharedGcd {P Q : Jet} {s t : Shape} (A : FixedPart P s) (B : FixedPart Q t)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hPs : RowCaps P s) (hQs : RowCaps Q t)
    (hno : K1_14_3.NoMovingCommon P Q) : Nonempty (SharedGcd A B) := by
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid (D := Seeds)
  let : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D := Equation)
  let gcdJet : GCDMonoid Jet := UniqueFactorizationMonoid.toGCDMonoid Jet
  let D : Jet := gcdJet.gcd A.residual B.residual
  obtain ⟨L, R, hL, hR, hrel⟩ := @extract_gcd Jet _ gcdJet A.residual B.residual
  change A.residual = D * L at hL
  change B.residual = D * R at hR
  have hF : P = fixedIncl A.equation * (D * L) :=
    A.factorization.trans (congrArg (fixedIncl A.equation * ·) hL)
  have hG : Q = fixedIncl B.equation * (D * R) :=
    B.factorization.trans (congrArg (fixedIncl B.equation * ·) hR)
  have hFL := right_ne_zero_of_mul (hF ▸ hP)
  have hGR := right_ne_zero_of_mul (hG ▸ hQ)
  have hDne := left_ne_zero_of_mul hFL
  have hDdeg : D.natDegree = 0 := by
    apply natDegree_zero_of_factors
    intro F hIrr hfd
    by_contra hpos
    have hleft := hfd.trans (gcdJet.gcd_dvd_left A.residual B.residual)
    have hright := hfd.trans (gcdJet.gcd_dvd_right A.residual B.residual)
    obtain ⟨G, hG⟩ := hno F hIrr (dvd_of_dvd_residual A hleft)
      (dvd_of_dvd_residual B hright) (Nat.pos_of_ne_zero hpos)
    exact A.stripped G (hG ▸ hIrr) (hG ▸ hleft)
  let H := D.coeff 0
  have hD : D = C H := eq_C_of_natDegree_eq_zero hDdeg
  have hH : H ≠ 0 := fun hz => hDne (by rw [hD, hz, map_zero])
  rw [hD] at hF hG
  obtain ⟨hFu, hFb, hLc⟩ := factor_caps hP hH hPs hF
  obtain ⟨_, _, hRc⟩ := factor_caps hQ hH hQs hG
  have hprime : IsRelPrime (toJet L) (toJet R) := by
    have hr := (@gcd_isUnit_iff_isRelPrime Jet _ gcdJet L R).mp hrel
    rw [toJet_equiv]
    intro E hEL hER
    have h1 : ambientToJet E ∣ L := by
      simpa using map_dvd ambientToJet.toRingHom hEL
    have h2 : ambientToJet E ∣ R := by
      simpa using map_dvd ambientToJet.toRingHom hER
    simpa using (hr h1 h2).map ambientToJet.symm.toRingHom
  exact ⟨⟨H, L, R, hH, right_ne_zero_of_mul hFL, right_ne_zero_of_mul hGR,
    hF, hG, hprime, hFu, hFb, hLc, hRc⟩⟩

end
end P0_10R_Late
end PackSource_P0_10R_LateAux1
section PackSource_P0_10R_LateAux2
set_option autoImplicit true
namespace P0_10R_Late

noncomputable section

open K1_14 K1_14_2_2_4
open private numerator numerator_bound seedNumerator ordinateNumerator mixedNumerator
  jetsNumerator ordinate_endpoints mixed_seed_endpoints mixed_ordinate_endpoints
  jets_endpoints from ProximityPrize.SubmissionLower.Fast032

def bridgeFree : Shape := ⟨230, 319, 66, 3650⟩
def bridgeMoving : Shape := ⟨600, 837, 168, 25167⟩

end
end P0_10R_Late
end PackSource_P0_10R_LateAux2
section PackSource_P0_10R_LateProof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

namespace P0_10R_Late

noncomputable section

open K1 (p)
open K1_14 (Jet)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 K1_14_2_2_4 Polynomial
open scoped Classical
open private cancel_fixed from_paired_bounds from ProximityPrize.SubmissionLower.Pack_K1_14_2_2_4Split

private theorem cancellation : K1_14_2_2_4.c3 :=
  K1_14_2_2_4_3.of_children K1_14_2_2_4_3_1.proof K1_14_2_2_4_3_2.proof

private theorem sections : K1_14_2_2_4.c5 :=
  K1_14_2_2_4_5.of_children K1_14_2_2_4_5_1.proof K1_14_2_2_4_5_2.proof
    K1_14_2_2_4_5_3.proof K1_14_2_2_4_5_4.proof K1_14_2_2_4_5_5.proof

private theorem paired_stage {P Q : Jet}
    {A : FixedPart P bridgeFree} {B : FixedPart Q bridgeMoving} (G : SharedGcd A B)
    (S : Finset (Ideal Ambient)) (square : Bool) (k : Fin 4) (r cap : ℕ)
    (hr : 0 < r) (hrm : r ≤ 26) (hdual : square = true → ∀ I ∈ S, dual I)
    (hpass : ∀ I ∈ S, Active I ∧ K1_14_2_2R.chainCompatible P Q I ∧
      ¬ fixedOn A.equation I ∧ ¬ fixedOn B.equation I ∧
      orderOn I P 26 ∧ orderOn I Q 26)
    (hnum :
      let x := seedDegree G.ordinary
      let z := G.ordinary.natDegree
      let d := if square then (27 - r)^2 else 27 - r
      d * highCap x z k + highScale r k *
        pairCap (residualShape bridgeFree x z) (residualShape bridgeMoving x z) k <
          highScale r k * d * (cap + 1)) :
    mass S k ≤ cap := by
  let x := seedDegree G.ordinary
  let z := G.ordinary.natDegree
  let s := residualShape bridgeFree x z
  let t := residualShape bridgeMoving x z
  let n := 27 - r
  let d := if square then n^2 else n
  have hxp : x < p := G.seed_le.trans_lt (by decide : bridgeFree.U < p)
  have hzp : z < p := G.ordinate_le.trans_lt (by decide : bridgeFree.B < p)
  have hn : 0 < n := by dsimp [n]; omega
  have hd : 0 < d := by
    unfold d
    split
    · exact Nat.pow_pos hn
    · exact hn
  have hh : highScale r k * mass (S.filter (HighOn G.ordinary r)) k ≤ highCap x z k := by
    apply K1_14_2_2R.high_graph_mass K1_14_2_2_4_4.proof sections G.ordinary P Q
      _ r G.ordinary_ne hzp hr
    · refine ⟨fixedIncl A.equation * G.left, G.left_factor.trans ?_⟩
      ring
    · refine ⟨fixedIncl B.equation * G.right, G.right_factor.trans ?_⟩
      ring
    intro I hI
    obtain ⟨hm, hf⟩ := Finset.mem_filter.mp hI
    exact ⟨(hpass I hm).1, (hpass I hm).2.1, hf⟩
  have hl : d * mass (S.filter fun I => ¬ HighOn G.ordinary r I) k ≤ pairCap s t k := by
    apply sections G.left G.right s t _ k d G.left_ne G.right_ne G.relativelyPrime
      (min_le_right _ _) (min_le_right _ _) G.left_caps G.right_caps hd
    intro I hI
    obtain ⟨hm, hf⟩ := Finset.mem_filter.mp hI
    obtain ⟨ha, _, hA, hB, hP, hQ⟩ := hpass I hm
    rw [G.left_factor] at hP
    rw [G.right_factor] at hQ
    have hlP := cancellation G.ordinary G.left I 26 r G.ordinary_ne hxp hzp ha hr hrm hf
      (cancel_fixed ha.prime _ _ 26 hA hP)
    have hlQ := cancellation G.ordinary G.right I 26 r G.ordinary_ne hxp hzp ha hr hrm hf
      (cancel_fixed ha.prime _ _ 26 hB hQ)
    have hlen := K1_14_2_2_4_4.proof G.left G.right I ha n hn hlP hlQ
    refine ⟨ha, fun _ => ?_⟩
    by_cases hIdual : dual I
    · rw [ite_eq_left hIdual] at hlen
      apply le_trans _ hlen
      apply Nat.cast_le.mpr
      unfold d
      split
      · exact le_rfl
      · simpa only [pow_two, mul_one] using Nat.mul_le_mul_left n (show 1 ≤ n by omega)
    · have hs : square ≠ true := fun he => hIdual (hdual he I hm)
      simpa [d, hs, hIdual] using hlen
  exact from_paired_bounds G.ordinary r (highScale r k) d _ _ cap hh hl hnum

theorem proof : P0_10R.lateMass := by
  classical
  intro w _ hhi rows pair
  have hf : P0_10.freeShape w 2 = bridgeFree := by
    rw [P0_10.freeShape, ite_eq_left hhi]
    rfl
  have hm : P0_10.movingShape w 2 = bridgeMoving := by
    rw [P0_10.movingShape, ite_eq_left hhi]
    rfl
  rw [hf, hm]
  intro hP hQ A B S _ hpass
  obtain ⟨G⟩ := sharedGcd A B pair.free_ne pair.moving_ne hP hQ pair.no_moving
  let x := seedDegree G.ordinary
  let z := G.ordinary.natDegree
  have hx : x ≤ 3650 := G.seed_le
  have hz : z ≤ 319 := G.ordinate_le
  have hlocal (I) (hI : I ∈ S) :
      Active I ∧ K1_14_2_2R.chainCompatible pair.free pair.moving I ∧
      ¬ fixedOn A.equation I ∧ ¬ fixedOn B.equation I ∧
      orderOn I pair.free 26 ∧ orderOn I pair.moving 26 :=
    ⟨(hpass I hI).1, (hpass I hI).2.1.2.2, (hpass I hI).2.2⟩
  intro k
  let T := S.filter dual
  have hdual (_ : true = true) (I) (hI : I ∈ T) : dual I := (Finset.mem_filter.mp hI).2
  have hT (I) (hI : I ∈ T) := hlocal I (Finset.mem_filter.mp hI).1
  fin_cases k
  · exact paired_stage G T true 0 3 169 (by decide) (by decide) hdual hT (LateReceipt6928.reserve_square 0 x z hx hz)
  · exact paired_stage G T true 1 3 3948 (by decide) (by decide) hdual hT (LateReceipt6928.reserve_square 1 x z hx hz)
  · exact paired_stage G T true 2 9 34207 (by decide) (by decide) hdual hT (LateReceipt6928.reserve_square 2 x z hx hz)
  · exact paired_stage G T true 3 8 254458 (by decide) (by decide) hdual hT (LateReceipt6928.reserve_square 3 x z hx hz)

end
end P0_10R_Late
end PackSource_P0_10R_LateProof
