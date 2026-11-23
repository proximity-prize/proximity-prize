import ProximityPrize.SubmissionLower.HighCore82258PrefixHelpers
import ProximityPrize.SubmissionLower.HighCore82258ScheduleData
import ProximityPrize.SubmissionLower.HighCore82258Regular

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

open HighCore82258 (start finish)
set_option maxHeartbeats 3200000

section
namespace HighCore82258_3
noncomputable section
open Polynomial
open HighCore82258 (K p agreement blockLength AnchorModel AnchoredFamily)
open HighCore82258 (Stage stages terminal fullCutoff degreeAt gap fees curveUnit)
open K1_14 (Shape Jet Seeds FX Banks atX jetAt seedHasse graphEval)
open K1_14_2 (Ambient ODE OnJet)
open K1_14_2_2 (Active Fits FixedPart ODECaps fixedOn mass sectionDegree weight dot)
open K1_14_2_2_4 (pairCap residualShape highCap highScale)
open scoped BigOperators Classical
def OnParent {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop := OnJet I (M.label γ) (F.scalar γ)
def BankPass (rows : Banks) (s : Shape) (I : Ideal Ambient) : Prop :=
  ∀ P ∈ rows s (fullCutoff s), K1_14_2.toJet P ∈ I
def PairPass {h rows s} (pair : HighCore82258.BufferedPair h rows s) (I : Ideal Ambient) : Prop :=
  BankPass rows s.free.shape I ∧ BankPass rows s.moving.shape I ∧
    K1_14_2_2R.chainCompatible pair.free pair.moving I
structure InitialCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (b : HighCore82258.Band) (freeFixed movingFixed : ODE) where
  parents : Finset (Ideal Ambient)
  active : ∀ I ∈ parents, Active I
  height_two : ∀ I ∈ parents, I.height = 2
  mass_bound : Fits parents (initialCap b)
  seed : K1_14_3.SeedCover
  seed_le : seed.curve.totalDegree ≤ initialCap b 2
  seed_points : seed.points.card ≤ initialE b
  ordinates : Finset FX
  ordinate_le : ordinates.card ≤ initialCap b 0
  content : Seeds
  content_ne : content ≠ 0
  content_le : content.totalDegree ≤ (stageAt b 0).free.shape.U + (stageAt b 0).moving.shape.U
  covers : ∀ γ ∈ Γ, seed.Covers (M.label γ) ∨ atX (F.scalar γ) ∈ ordinates ∨
    graphEval (M.label γ) content = 0 ∨ K1_14_2.fixedAt freeFixed (F.scalar γ) = 0 ∨
    K1_14_2.fixedAt movingFixed (F.scalar γ) = 0 ∨ ∃ I ∈ parents, OnParent F I γ
end
end HighCore82258_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
namespace HighCore82258_3
noncomputable section
open Polynomial
open HighCore82258 (AnchorModel AnchoredFamily K p agreement)
open HighCore82258 (Stage Listed Source  stages fullCutoff buffered )
open K1_14 (Shape Banks Jet Equation jetAt seedHasse seedEmbedding)
open K1_14_2 (Ambient OnJet jetMarkHom toJet eval_toJet CoordinateRing SeedField
  JetSeedSection JetYSection ODE)
open K1_14_2_2 (Active dual orderOn FixedPart ODECaps fixedOn RowCaps CutCover
  sectionDegree weight dot joinCuts joinCuts_cost sum_dot emptyCut mass)
open K1_14_2_2_3
open K1_14_2_2_7
open private specialize_shiftedWord shift_word from ProximityPrize.SubmissionLower.Fast052
open scoped BigOperators Classical
abbrev StageIndex (b : HighCore82258.Band) := Fin (stages b).length
def pairAt {b h rows} (pairs : HighCore82258.Pairs b h rows) (i : StageIndex b) :
    HighCore82258.BufferedPair h rows (stageAt b i) :=
  pairs _ (stage_mem i.isLt)
structure FixedRows {b h rows} (pairs : HighCore82258.Pairs b h rows) (i : StageIndex b) where
  free : FixedPart (pairAt pairs i).free (stageAt b i).free.shape
  moving : FixedPart (pairAt pairs i).moving (stageAt b i).moving.shape
private theorem envelope_caps {s : Stage} {P : Jet}
    (hb : s.free.shape.J ≤ s.free.shape.B) (hc : s.moving.shape.J ≤ s.moving.shape.B)
    (hP : RowCaps P s.free.shape ∨ RowCaps P s.moving.shape) : RowCaps P (envelope s) := by
  have ha : s.free.shape.B ≤ (envelope s).B :=
    (Nat.sub_add_cancel hb).symm.trans_le
      (Nat.add_le_add (le_max_left _ _) (le_max_left _ _))
  have hd : s.moving.shape.B ≤ (envelope s).B :=
    (Nat.sub_add_cancel hc).symm.trans_le
      (Nat.add_le_add (le_max_right _ _) (le_max_right _ _))
  intro j i h
  rcases hP with hp | hp
  · obtain ⟨hg, hj, hu⟩ := hp j i h
    exact ⟨hg.trans ha, hj.trans (le_max_left _ _), hu.trans (le_max_left _ _)⟩
  · obtain ⟨hg, hj, hu⟩ := hp j i h
    exact ⟨hg.trans hd, hj.trans (le_max_right _ _), hu.trans (le_max_right _ _)⟩
end
end HighCore82258_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1000000
namespace HighCore82258_3
noncomputable section
open HighCore82258 (AnchorModel AnchoredFamily)
open HighCore82258 (stages terminal Source )
open P1_7_4 (massQ_mono)
open K1_14 (Banks)
open K1_14_2 (Ambient)
open K1_14_2_2 (Active Fits dual fixedOn mass)
open scoped Classical
def nextIndex {b : HighCore82258.Band} (i : ℕ) (hi : i < laterCount b) : StageIndex b :=
  ⟨i+1, by change i+1 < (HighCore82258.stages b).length; unfold laterCount at hi; omega⟩
structure Process {b h rows} (pairs : HighCore82258.Pairs b h rows) where
  sched : ScheduleOK b
  parents : Finset (Ideal Ambient)
  fixed : ∀ i : StageIndex b, FixedRows pairs i
  geometry : ∀ I ∈ parents, Active I ∧ I.height = 2
  init_mass : Fits parents (initialCap b)
def Process.Clean {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs)
    (I : Ideal Ambient) : Prop :=
  ∀ i, ¬ fixedOn (R.fixed i).free.equation I ∧ ¬ fixedOn (R.fixed i).moving.equation I
def PassedThrough {b h rows} (pairs : HighCore82258.Pairs b h rows) (i : ℕ) (I : Ideal Ambient) : Prop :=
  ∀ j : StageIndex b, 0 < j.val → j.val ≤ i → PairPass (pairAt pairs j) I
def Process.tested {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  R.parents.filter fun I => R.Clean I ∧ PassedThrough pairs i I
def Process.kept {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  (R.tested i).filter fun I => stopIndex b ≤ i → dual I
def Process.rankExit {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs) :
    Finset (Ideal Ambient) :=
  (R.tested (stopIndex b)).filter fun I => ¬ dual I
def Process.final {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs) :
    Finset (Ideal Ambient) :=
  (R.kept (laterCount b)).filter (BankPass rows (terminal b).shape)
def Process.live {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  if i ≤ laterCount b then R.kept i else R.final
def Process.lost {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  if hi : i < laterCount b then
    (R.kept i).filter fun I => ¬ PairPass (pairAt pairs (nextIndex i hi)) I
  else
    (R.kept i).filter fun I => ¬ BankPass rows (terminal b).shape I
theorem Process.kept_sub {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs)
    (i : ℕ) : R.kept i ⊆ R.tested i :=
  Finset.filter_subset _ _
theorem Process.retains {b h rows} {pairs : HighCore82258.Pairs b h rows} (R : Process pairs)
    {I : Ideal Ambient} (hI : I ∈ R.parents) (hc : R.Clean I)
    (hrank : I ∉ R.rankExit) (hlost : ∀ i ≤ laterCount b, I ∉ R.lost i) :
    I ∈ R.final := by
  have keep : ∀ i ≤ laterCount b, I ∈ R.kept i := by
    intro i hi
    induction i with
    | zero =>
      have ht : I ∈ R.tested 0 :=
        Finset.mem_filter.mpr ⟨hI, hc, fun j hp hj => (Nat.not_lt_of_ge hj hp).elim⟩
      refine Finset.mem_filter.mpr ⟨ht, ?_⟩
      intro hs
      by_contra hd
      exact hrank (Finset.mem_filter.mpr ⟨by simpa [Nat.eq_zero_of_le_zero hs] using ht, hd⟩)
    | succ i ih =>
      have ht : i < laterCount b := hi
      have hprev := ih (Nat.le_of_lt ht)
      have hp : PairPass (pairAt pairs (nextIndex i ht)) I := by
        by_contra hfail
        apply hlost i ht.le
        simpa only [Process.lost, dite_eq_left ht] using Finset.mem_filter.mpr ⟨hprev, hfail⟩
      have htest : I ∈ R.tested (i+1) := by
        refine Finset.mem_filter.mpr ⟨hI, hc, ?_⟩
        intro j hj hji
        rcases hji.lt_or_eq with hj' | he
        · exact (Finset.mem_filter.mp (R.kept_sub i hprev)).2.2 j hj (Nat.le_of_lt_succ hj')
        · rw [show j = nextIndex i ht from Fin.ext he]
          exact hp
      refine Finset.mem_filter.mpr ⟨htest, ?_⟩
      intro hs
      by_cases hh : stopIndex b ≤ i
      · exact (Finset.mem_filter.mp hprev).2 hh
      · have he : stopIndex b = i+1 := by omega
        by_contra hd
        exact hrank (Finset.mem_filter.mpr ⟨by simpa [he] using htest, hd⟩)
  have hk := keep (laterCount b) le_rfl
  refine Finset.mem_filter.mpr ⟨hk, ?_⟩
  by_contra hf
  apply hlost (laterCount b) le_rfl
  simpa only [Process.lost, dite_eq_right (Nat.lt_irrefl _)] using Finset.mem_filter.mpr ⟨hk, hf⟩
end
end HighCore82258_3
end
