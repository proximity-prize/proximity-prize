import ProximityPrize.SubmissionLower.Peer653High53FamilyJointLoss

-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Family.lean.

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace Peer653High53
noncomputable section
open Polynomial
open Peer653High53 (Band AnchorModel AnchoredFamily K)
open K1_14 (Banks Equation SeedBound atMark graphEval)
open K1_14_3 (ProjectedProduct)
open K1_14_4 (seedDegree seedDegree_le_iff)
def c1 : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead → M.shift ∉ Γ → ∀ H, AdjacentChart M F H →
    ∃ rows : Banks, Source b M F rows
def c2 : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead → M.shift ∉ Γ → ∀ rows, Source b M F rows →
    Nonempty (Pairs b M.overhead.toNat rows)
def c3 : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead → M.shift ∉ Γ → ∀ H, AdjacentChart M F H →
    ((start b) < 7773 → CurveTariff b M F) →
    ∀ rows, Source b M F rows → ∀ pairs : Pairs b M.overhead.toNat rows,
    Nonempty (PrefixInventory b M F pairs)
def c4 : Prop :=
  ∀ (b : Band) h, (start b) ≤ h → h ≤ (finish b) → ∀ x : Test b,
    debit h (tested b x) < jointGain h (tested b x).shape (threshold b x) (seedThreshold b x)
def c5 : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead → M.shift ∉ Γ → ∀ H, AdjacentChart M F H →
    ∀ (i : GradeIndex b) f, Reduced f → f.natDegree = i.val+1 → 3 ≤ f.natDegree →
    0 < seedDegree f → SeedBound f ((grades b).get i).seedCap →
    RegularCount M F f (tangentFee (start b) (finish b) f.natDegree ((grades b).get i).seedCap)
private theorem retained_count (h5 : c5) {b u del}
    (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hw : InBand b M.overhead) (hshift : M.shift ∉ Γ) {H} (hH : AdjacentChart M F H)
    (T : Finset K) (hT : T ⊆ Γ) (f : Equation) (hf : Reduced f)
    (i : GradeIndex b) (he : f.natDegree = i.val+1) (hs : SeedBound f ((grades b).get i).seedCap)
    (hr : ∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0) : T.card ≤ (retainedCap b) := by
  classical
  let v := ((grades b).get i).seedCap
  have cert := grade_checked b i
  rw [← he] at cert
  have hprice : wholePrice (start b) (finish b) f.natDegree v ≤ (retainedCap b) := cert.fee
  by_cases hzero : seedDegree f = 0
  · have hfix := High53Model.fixed_count M F T hT hf.1 ((seedDegree_le_iff f 0).mp hzero.le) hr
    exact hfix.trans ((sheets_le_price _ _ _ _).trans hprice)
  have hpos := Nat.pos_of_ne_zero hzero
  have hv : v ≠ 0 := Nat.ne_of_gt (hpos.trans_le ((seedDegree_le_iff _ _).mpr hs))
  let bad := T.filter fun γ => graphEval (M.label γ) (f.resultant f.derivative) = 0
  have hb : bad ⊆ T := Finset.filter_subset _ _
  have hbad := High53Model.resultant_count M hf hs cert.separant bad
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
  have hreg : ∀ γ ∈ T \ bad, regularRoot f (M.label γ) (F.scalar γ) := by
    intro γ hγ
    obtain ⟨ht, hn⟩ := Finset.mem_sdiff.mp hγ
    exact P1_7.regular_of_resultant hf.1 (hr γ ht) (fun hz => hn (Finset.mem_filter.mpr ⟨ht,hz⟩))
  have hpartition := Finset.card_sdiff_add_card_eq_card hb
  have hsub : T \ bad ⊆ Γ := Finset.sdiff_subset.trans hT
  apply le_trans _ hprice
  by_cases hsmall : f.natDegree ≤ 2
  · have hreg' := persistent_count M F hw hH i hf hs _ hsub hreg
    simp only [wholePrice, ite_eq_right hv, ite_eq_left hsmall]
    change bad.card ≤ singularFee f.natDegree v at hbad
    change (T \ bad).card ≤ persistentFee (start b) (finish b) f.natDegree v at hreg'
    omega
  · have hreg' := h5 b u del M Γ F hw hshift H hH i f hf he (by omega) hpos hs _ hsub hreg
    simp only [wholePrice, ite_eq_right hv, ite_eq_right hsmall]
    change bad.card ≤ singularFee f.natDegree v at hbad
    change (T \ bad).card ≤ tangentFee (start b) (finish b) f.natDegree v at hreg'
    omega
def HighStatement : Prop :=
  ∀ (b : Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    ((start b) : ℤ) ≤ M.overhead → M.overhead ≤ ((finish b) : ℤ) →
    Γ.card ≤ (prefixFee b) + (retainedCap b) + 1

def RetainedCountAt (b : Band) : Prop :=
  ∀ u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead → M.shift ∉ Γ → ∀ H, AdjacentChart M F H →
    ∀ C : ChartSource b M F, ∀ pairs : Pairs b M.overhead.toNat C.rows,
    ∀ Q : PrefixInventory b M F pairs, ∀ f : Equation, Reduced f →
    ProjectedProduct Q.parents f → ∀ T : Finset K, T ⊆ Γ →
    (∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0) →
    T.card ≤ retainedCap b
end
end Peer653High53
end
