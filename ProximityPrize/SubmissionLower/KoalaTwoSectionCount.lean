import ProximityPrize.SubmissionLower.KoalaRectRetained
import ProximityPrize.SubmissionLower.KoalaTwoSectionPrice
import ProximityPrize.SubmissionLower.KoalaRawCount
import ProximityPrize.SubmissionLower.HighCore82219Regular

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace KoalaTwoSectionPrice
noncomputable section
open Polynomial Finset HighCore82219
open KoalaRect (RectPrice axisDegree axisDegree_le_iff seedBound_of_axis)
open KoalaRectReceipts (paidCap)
open K1_14 (atMark graphEval)
open HighCore82219Upper (Input ResidueLift Factors componentMarks mem_componentMarks root_component ratio_le_ceil)

def TwoCutIncidence : Prop :=
  ∀ (J : Input) (B : ResidueLift J) (D : Factors J B),
    J.lo = start .h2367 → J.hi = finish .h2367 → 7 ≤ J.e → J.e ≤ 21 →
    FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi) →
    ∀ v₀ v₁ : ℕ, v₀+v₁ = J.v → J.v = paidCap J.e →
      (∀ i, (J.f.coeff i).degreeOf 0 ≤ v₀ ∧ (J.f.coeff i).degreeOf 1 ≤ v₁) →
      (componentMarks J D.proper).card ≤ secondCut J.lo J.hi J.e v₀ v₁

private theorem regular_count (incidence : TwoCutIncidence) (J : Input)
    (hlo : J.lo = start .h2367) (hhi : J.hi = finish .h2367) {v₀ v₁ : ℕ}
    (haxes : ∀ i, (J.f.coeff i).degreeOf 0 ≤ v₀ ∧ (J.f.coeff i).degreeOf 1 ≤ v₁)
    (hsum : v₀+v₁ = J.v) (hpaid : J.v = paidCap J.e) :
    J.marks.card ≤
      properCharge agreement J.lo J.hi J.e v₀ v₁ + flatFee J.hi J.v + J.e := by
  classical
  have hweak := HighCore82219Upper.fixed_word J (Finset.Subset.refl J.marks)
  have hword : FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi) :=
    ⟨hweak.distinct, hweak.degree, fun γ hγ =>
      let m := J.family.mark γ (J.marks_sub hγ)
      ⟨m.bad.support, m.bad.agreement, m.scalar_hits⟩⟩
  obtain ⟨B⟩ := HighCore82219Upper_1.proof J
  obtain ⟨D⟩ := HighCore82219Upper_2.proof J B
  let T := componentMarks J D.proper
  let U := fun j => componentMarks J (D.flat j)
  have hcov : J.marks ⊆ T ∪ univ.biUnion U := by
    intro γ hγ
    rcases root_component J D hγ with ht | ⟨j, hu⟩
    · exact mem_union.mpr (Or.inl (mem_componentMarks.mpr ⟨hγ, ht⟩))
    · exact mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨j, mem_univ _, mem_componentMarks.mpr ⟨hγ, hu⟩⟩))
  have hp : T.card ≤ properCharge agreement J.lo J.hi J.e v₀ v₁ := by
    by_cases hsingle : singleCut J.e
    · rw [properCharge, if_pos hsingle]
      apply ratio_le_ceil (HighCore82219_5.scale_pos J J.agreement_gap)
      obtain ⟨hk,hv,hw⟩ := liftIndex_spec J.hi v₀ v₁
      let k := liftIndex J.hi v₀ v₁
      have hcount := SplitCut.RawCount.proper_count J B D v₀ v₁ k hk
        (by simpa only [Nat.mul_comm] using hv) (by simpa only [Nat.mul_comm] using hw)
        haxes hword J.agreement_gap
      refine hcount.trans_eq ?_
      simp only [SplitCut.RawCount.rootDegree, SplitCut.RawCount.firstDegree, SplitCut.RawCount.weight,
        properBudget, surfaceDegree, HighCore82219_5.nodeVelocity,
        HighCore82219.lambdaNum, HighCore82219.muNum, HighCore82219.gap, k]
      ring
    · rw [properCharge, if_neg hsingle]
      unfold singleCut at hsingle
      exact incidence J B D hlo hhi (by omega) (by omega) hword v₀ v₁ hsum hpaid haxes
  have hf : (∑ j, (U j).card) ≤ flatFee J.hi J.v + J.e := by
    apply HighCore82219_5.flat_count J J.agreement_gap hword D
    intro j
    obtain ⟨E⟩ := HighCore82219Upper_4.of_children HighCore82219Upper_4_1.proof HighCore82219Upper_4_2.proof J B D j
    exact HighCore82219Upper_5.of_children HighCore82219Upper_5_1.proof HighCore82219Upper_5_2.proof J B D j E
  calc
    J.marks.card ≤ T.card + (univ.biUnion U).card := (card_le_card hcov).trans (card_union_le _ _)
    _ ≤ properCharge agreement J.lo J.hi J.e v₀ v₁ +
        (flatFee J.hi J.v + J.e) := Nat.add_le_add hp (card_biUnion_le.trans hf)
    _ = _ := by rw [Nat.add_assoc]

theorem rect_price (incidence : TwoCutIncidence) : RectPrice := by
  classical
  intro u del M Γ F hw hshift H hH _ _ _ f hf _ hel heu hvpos haxes T hT hr
  let e := f.natDegree
  let v := paidCap e
  let v₀ := axisDegree f 0
  let v₁ := v - v₀
  have hv₀ : v₀ ≤ v := by change v₀ + axisDegree f 1 ≤ v at haxes; omega
  have hv₁ : axisDegree f 1 ≤ v₁ := by
    change axisDegree f 1 ≤ v - v₀
    change v₀ + axisDegree f 1 ≤ v at haxes
    omega
  have hsum : v₀ + v₁ = v := Nat.add_sub_of_le hv₀
  have hbounds : ∀ i, (f.coeff i).degreeOf 0 ≤ v₀ ∧ (f.coeff i).degreeOf 1 ≤ v₁ :=
    fun i => ⟨(axisDegree_le_iff f 0 _).mp le_rfl i, (axisDegree_le_iff f 1 _).mp hv₁ i⟩
  have hseed := seedBound_of_axis haxes
  obtain ⟨hsep, hflat⟩ := guards hel heu
  let bad := T.filter fun γ => graphEval (M.label γ) (f.resultant f.derivative) = 0
  let R := T \ bad
  have hb : bad ⊆ T := Finset.filter_subset _ _
  have hbad := FrontCore82219.resultant_count M hf hseed hsep bad
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hreg : ∀ γ ∈ R, regularRoot f (M.label γ) (F.scalar γ) := by
    intro γ hγ
    obtain ⟨ht, hn⟩ := Finset.mem_sdiff.mp hγ
    exact P1_7.regular_of_resultant hf.1 (hr γ ht) (fun hz => hn (Finset.mem_filter.mpr ⟨ht,hz⟩))
  obtain ⟨hl, hu⟩ := window_nat hw
  have hl' : 2391 ≤ M.overhead.toNat := hl
  have hu' : M.overhead.toNat ≤ 2490 := hu
  let J : Input := {
    words := u, deleted := del, model := M, labels := Γ, family := F
    shift_out := hshift, block := H, chart := hH, marks := R
    marks_sub := Finset.sdiff_subset.trans hT
    f := f, regular := hreg, reduced := hf, sheets := hel, seed_pos := hvpos
    v := v, seed_bound := hseed
    lo := start .h2367, hi := finish .h2367, lower := hl, upper := hu
    positive := by omega
    quotient_pos := by change 0 < 131071 - M.overhead.toNat; omega
    agreement_gap := by decide
    factorial_guard := by decide
    separant_guard := hsep
    flat_guard := hflat }
  have hregular := regular_count incidence J rfl rfl hbounds hsum rfl
  have hpart := Finset.card_sdiff_add_card_eq_card hb
  have hcharge : charge agreement J.lo J.hi e v₀ v₁ ≤ retainedCap .h2367 :=
    charge_le hel heu hsum
  calc
    T.card = bad.card + J.marks.card := by
      change T.card = bad.card + R.card
      exact hpart.symm.trans (Nat.add_comm _ _)
    _ ≤ singularFee e v +
        (properCharge agreement J.lo J.hi e v₀ v₁ + flatFee J.hi v + e) :=
      Nat.add_le_add hbad hregular
    _ = charge agreement J.lo J.hi e v₀ v₁ := by
      unfold charge
      rw [hsum]
      change singularFee e v +
          (properCharge agreement J.lo J.hi e v₀ v₁ + flatFee J.hi v + e) =
        properCharge agreement J.lo J.hi e v₀ v₁ + flatFee J.hi v + singularFee e v + e
      ac_rfl
    _ ≤ retainedCap .h2367 := hcharge

end
end KoalaTwoSectionPrice
