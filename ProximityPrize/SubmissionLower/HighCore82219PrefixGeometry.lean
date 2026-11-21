import ProximityPrize.SubmissionLower.HighCore82219PrefixHelpers
import ProximityPrize.SubmissionLower.HighCore82219ScheduleData
import ProximityPrize.SubmissionLower.HighCore82219Regular

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

open HighCore82219 (start finish)
set_option maxHeartbeats 3200000

section
namespace HighCore82219_3
noncomputable section
open Polynomial
open HighCore82219 (K p agreement blockLength AnchorModel AnchoredFamily)
open HighCore82219 (Stage stages terminal fullCutoff degreeAt gap fees curveUnit)
open K1_14 (Shape Jet Seeds FX Banks atX jetAt seedHasse graphEval)
open K1_14_2 (Ambient ODE OnJet)
open K1_14_2_2 (Active Fits FixedPart ODECaps fixedOn mass sectionDegree weight dot)
open K1_14_2_2_4 (pairCap residualShape highCap highScale)
open scoped BigOperators Classical
def OnParent {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop := OnJet I (M.label γ) (F.scalar γ)
def BankPass (rows : Banks) (s : Shape) (I : Ideal Ambient) : Prop :=
  ∀ P ∈ rows s (fullCutoff s), K1_14_2.toJet P ∈ I
def PairPass {h rows s} (pair : HighCore82219.BufferedPair h rows s) (I : Ideal Ambient) : Prop :=
  BankPass rows s.free.shape I ∧ BankPass rows s.moving.shape I ∧
    K1_14_2_2R.chainCompatible pair.free pair.moving I
structure InitialCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (b : HighCore82219.Band) (freeFixed movingFixed : ODE) where
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
end HighCore82219_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
namespace HighCore82219_3
noncomputable section
open Polynomial
open HighCore82219 (AnchorModel AnchoredFamily K p agreement)
open HighCore82219 (Stage Listed Source InBand stages fullCutoff buffered window_nat)
open K1_14 (Shape Banks Jet Equation jetAt seedHasse seedEmbedding)
open K1_14_2 (Ambient OnJet jetMarkHom toJet eval_toJet CoordinateRing SeedField
  JetSeedSection JetYSection ODE)
open K1_14_2_2 (Active dual orderOn FixedPart ODECaps fixedOn RowCaps CutCover
  sectionDegree weight dot joinCuts joinCuts_cost sum_dot emptyCut mass)
open K1_14_2_2_3
open K1_14_2_2_7
open private specialize_shiftedWord shift_word from ProximityPrize.SubmissionLower.Fast052
open scoped BigOperators Classical
abbrev StageIndex (b : HighCore82219.Band) := Fin (stages b).length
def pairAt {b h rows} (pairs : HighCore82219.Pairs b h rows) (i : StageIndex b) :
    HighCore82219.BufferedPair h rows (stageAt b i) :=
  pairs _ (stage_mem i.isLt)
theorem free_listed {b : HighCore82219.Band} (i : StageIndex b) : Listed b (stageAt b i).free :=
  Or.inr (Or.inl ⟨_, stage_mem i.isLt, Or.inl rfl⟩)
theorem moving_listed {b : HighCore82219.Band} (i : StageIndex b) : Listed b (stageAt b i).moving :=
  Or.inr (Or.inl ⟨_, stage_mem i.isLt, Or.inr rfl⟩)
theorem bank_zero {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) {t : HighCore82219.Bank} (ht : Listed b t)
    (hpos : 0 < t.shape.m * agreement) {P : Jet} {W : ℕ}
    (hW : W ≤ fullCutoff t.shape) (hP : P ∈ rows t.shape W) :
    ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 :=
  src.necessary t ht W (by unfold fullCutoff at hW; omega) P hP
private theorem buffer_spend {b w} (hw : InBand b w) {r : ℕ} {s : Shape}
    (guard : BankGuard (finish b) r s) :
    buffered w.toNat r s + 2*w.toNat*r ≤ fullCutoff s := by
  have h := Nat.mul_le_mul_right r (Nat.mul_le_mul_left 2 (window_nat hw).2)
  have h' := h.trans guard.buffer
  unfold buffered
  omega
theorem intro_zero {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) (hw : InBand b M.overhead) {t : HighCore82219.Bank}
    (ht : Listed b t) {r : ℕ} (guard : BankGuard (finish b) r t.shape)
    {P : Jet} (hP : P ∈ rows t.shape (buffered M.overhead.toNat r t.shape))
    (i : Fin 2) (a : ℕ) (ha : a ≤ r) :
    ∀ γ ∈ Γ, jetAt (seedHasse i a P) (M.label γ) (F.scalar γ) = 0 := by
  apply bank_zero src ht guard.pos _ (src.shift t ht _ _ hP i a)
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ ha) _).trans (buffer_spend hw guard)
structure FixedRows {b h rows} (pairs : HighCore82219.Pairs b h rows) (i : StageIndex b) where
  free : FixedPart (pairAt pairs i).free (stageAt b i).free.shape
  moving : FixedPart (pairAt pairs i).moving (stageAt b i).moving.shape
def fixedRows {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) (pairs : HighCore82219.Pairs b M.overhead.toNat rows)
    (i : StageIndex b) : FixedRows pairs i :=
  let pair := pairAt pairs i
  ⟨Classical.choice (K1_14_2_2_1.proof _ _ pair.free_ne
      (src.shape _ (free_listed i) _ _ pair.free_mem)),
    Classical.choice (K1_14_2_2_1.proof _ _ pair.moving_ne
      (src.shape _ (moving_listed i) _ _ pair.moving_mem))⟩
theorem fixed_zero {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {I : Ideal Ambient} {G : ODE} {γ : K} (hm : OnParent F I γ) (hG : fixedOn G I) :
    K1_14_2.fixedAt G (F.scalar γ) = 0 := by
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (hm hG)
theorem on_surface {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {I : Ideal Ambient} (hI : I.IsPrime) {γ : K} (hm : OnParent F I γ) :
    HighCore82219.MarkOn M F (P0_10R.Bridge.surfaceOf I hI) γ := by
  intro P hP
  apply RingHom.mem_ker.mpr
  change jetAt P (M.label γ) (F.scalar γ) = 0
  rw [← eval_toJet]
  exact RingHom.mem_ker.mp (hm hP)
theorem surface_pass {h rows s} {pair : HighCore82219.BufferedPair h rows s}
    {I : Ideal Ambient} (hI : I.IsPrime) (hp : PairPass pair I) :
    HighCore82219.PairPass pair (P0_10R.Bridge.surfaceOf I hI) :=
  ⟨hp.1, hp.2.1, hp.2.2⟩
private theorem shifted_contact {A : Type*} [CommRing A] (a : K1_14.Seeds →+* A)
    {rows : Banks} {s : Shape} {I : Ideal Ambient} {h W r : ℕ} {P : Jet}
    (hn : ∀ W W', W ≤ W' → rows s W ≤ rows s W')
    (hs : K1_14_3.SeedShift h rows s) (hv : BankPass rows s I)
    (hcut : W + 2*h*r ≤ fullCutoff s) (hP : P ∈ rows s W) :
    fibreContact (I.map (specializeJets a)) (specializeJets a (toJet P)) r := by
  intro t ht
  rw [← specialize_shiftedWord]
  apply Ideal.mem_map_of_mem
  exact hv _ (hn _ _ ((Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _).trans hcut)
    (shift_word hs hP t))
theorem buffered_order {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) (hw : InBand b M.overhead)
    {t : HighCore82219.Bank} (ht : Listed b t) {r : ℕ}
    (guard : BankGuard (finish b) r t.shape) (hr : r < p)
    {I : Ideal Ambient} (hactive : Active I) (hv : BankPass rows t.shape I)
    {P : Jet} (hP : P ∈ rows t.shape (buffered M.overhead.toNat r t.shape)) :
    orderOn I P (r+1) := by
  classical
  have hn := src.nested t ht t ht rfl rfl rfl le_rfl
  have hcut := buffer_spend hw guard
  by_cases hd : dual I
  · have hc := shifted_contact (algebraMap K1_14.Seeds SeedField) hn
      (src.shift t ht) hv hcut hP
    rw [← mapGenericJets_eq] at hc
    exact clear_dual hd (K1_14_2_2_3_1.proof I hactive.prime hactive.jet_finite
      hd hactive.jet_lt _ r hr hc)
  · obtain ⟨g, hg, hdeg, he⟩ := K1_14_2_2_3_2.proof I hactive hd
    let _ : I.IsPrime := hactive.prime
    let _ : (I.comap jetInclude).IsPrime := Ideal.IsPrime.comap jetInclude
    let _ : CharP K1_14.FX p := charP_of_injective_ringHom seedEmbedding.injective p
    let _ : CharP (JetImageField I) p :=
      charP_of_injective_ringHom ((jetImageMap I).comp MvPolynomial.C).injective p
    apply clear_rank_one hactive.prime hd
    have hc := shifted_contact (jetImageMap I) hn (src.shift t ht) hv hcut hP
    change fibreContact (I.map (imageFibreMap I)) (imageFibreMap I (toJet P)) r at hc
    rw [he] at hc ⊢
    exact divisor_contact hg hdeg hr hc
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
theorem failed_bank {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) {t : HighCore82219.Bank} (ht : Listed b t)
    (hpos : 0 < t.shape.m * agreement) {I : Ideal Ambient} (hf : ¬ BankPass rows t.shape I) :
    ∃ P : Jet, RowCaps P t.shape ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 := by
  classical
  unfold BankPass at hf
  push Not at hf
  obtain ⟨P, hP, hprop⟩ := hf
  exact ⟨P, src.shape t ht _ P hP, hprop, bank_zero src ht hpos le_rfl hP⟩
theorem failed_pair {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) (sched : ScheduleOK b)
    (pairs : HighCore82219.Pairs b M.overhead.toNat rows) (i : StageIndex b) {I : Ideal Ambient}
    (hf : ¬ PairPass (pairAt pairs i) I) :
    ∃ P : Jet, RowCaps P (envelope (stageAt b i)) ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0 := by
  classical
  let s := stageAt b i
  let pair := pairAt pairs i
  obtain ⟨ga, gc⟩ := sched.stage_guard i i.isLt
  have liftCaps {P : Jet} (h : RowCaps P s.free.shape ∨ RowCaps P s.moving.shape) :
      RowCaps P (envelope s) := envelope_caps ga.ode.jb gc.ode.jb h
  by_cases hP : BankPass rows s.free.shape I
  · by_cases hQ : BankPass rows s.moving.shape I
    · have htest : ¬ K1_14_2_2R.chainCompatible pair.free pair.moving I :=
        fun h => hf ⟨hP, hQ, h⟩
      unfold K1_14_2_2R.chainCompatible at htest
      push Not at htest
      obtain ⟨f, _, _, _, hdiv, hmem, g, a, hclear, hproper⟩ := htest
      have hcaps := src.shape _ (moving_listed i) _ _ pair.moving_mem
      have hG := K1_14_3R.chainCutter_caps_of_dvd pair.moving_ne hcaps gc.ode.jpos hdiv hclear
      refine ⟨K1_14_3R.chainCutter g, liftCaps (Or.inr hG), hproper, ?_⟩
      intro γ _ hγ
      apply K1_14_3R.chainCutter_zero hclear
      have hz := RingHom.mem_ker.mp (hγ hmem)
      simpa only [eval_toJet, jetAt, eval₂_C, coe_eval₂RingHom, K1_14.atMark] using hz
    · obtain ⟨P, hcaps, hproper, hzero⟩ := failed_bank src (moving_listed i) gc.pos hQ
      exact ⟨P, liftCaps (Or.inr hcaps), hproper, fun γ hγ _ => hzero γ hγ⟩
  · obtain ⟨P, hcaps, hproper, hzero⟩ := failed_bank src (free_listed i) ga.pos hP
    exact ⟨P, liftCaps (Or.inl hcaps), hproper, fun γ hγ _ => hzero γ hγ⟩
theorem combined_cuts {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    (A : Finset (Ideal Ambient)) (s : Shape) (hs : s.J ≤ s.B)
    (ha : ∀ I ∈ A, Active I)
    (hcut : ∀ I ∈ A, ∃ P : Jet, RowCaps P s ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0) :
    ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight s fee) (mass A)) ∧
      ∀ γ ∈ Γ, (∃ I ∈ A, OnParent F I γ) → γ ∈ C.direct ∨ ∃ I ∈ C.curves, OnParent F I γ :=
  HighCore82219PrefixHelpers.combined_cuts (F := F) A s hs ha hcut
end
end HighCore82219_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1000000
namespace HighCore82219_3
noncomputable section
open HighCore82219 (AnchorModel AnchoredFamily)
open HighCore82219 (stages terminal Source InBand)
open P1_7_4 (massQ_mono)
open K1_14 (Banks)
open K1_14_2 (Ambient)
open K1_14_2_2 (Active Fits dual fixedOn mass)
open scoped Classical
def nextIndex {b : HighCore82219.Band} (i : ℕ) (hi : i < laterCount b) : StageIndex b :=
  ⟨i+1, by change i+1 < (HighCore82219.stages b).length; unfold laterCount at hi; omega⟩
structure Process {b h rows} (pairs : HighCore82219.Pairs b h rows) where
  sched : ScheduleOK b
  parents : Finset (Ideal Ambient)
  fixed : ∀ i : StageIndex b, FixedRows pairs i
  geometry : ∀ I ∈ parents, Active I ∧ I.height = 2
  init_mass : Fits parents (initialCap b)
def Process.Clean {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs)
    (I : Ideal Ambient) : Prop :=
  ∀ i, ¬ fixedOn (R.fixed i).free.equation I ∧ ¬ fixedOn (R.fixed i).moving.equation I
def PassedThrough {b h rows} (pairs : HighCore82219.Pairs b h rows) (i : ℕ) (I : Ideal Ambient) : Prop :=
  ∀ j : StageIndex b, 0 < j.val → j.val ≤ i → PairPass (pairAt pairs j) I
def Process.tested {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  R.parents.filter fun I => R.Clean I ∧ PassedThrough pairs i I
def Process.kept {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  (R.tested i).filter fun I => stopIndex b ≤ i → dual I
def Process.rankExit {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs) :
    Finset (Ideal Ambient) :=
  (R.tested (stopIndex b)).filter fun I => ¬ dual I
def Process.final {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs) :
    Finset (Ideal Ambient) :=
  (R.kept (laterCount b)).filter (BankPass rows (terminal b).shape)
def Process.live {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  if i ≤ laterCount b then R.kept i else R.final
def Process.lost {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  if hi : i < laterCount b then
    (R.kept i).filter fun I => ¬ PairPass (pairAt pairs (nextIndex i hi)) I
  else
    (R.kept i).filter fun I => ¬ BankPass rows (terminal b).shape I
theorem Process.tested_sub {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs)
    (i : ℕ) : R.tested i ⊆ R.parents :=
  Finset.filter_subset _ _
theorem Process.kept_sub {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs)
    (i : ℕ) : R.kept i ⊆ R.tested i :=
  Finset.filter_subset _ _
theorem Process.final_sub {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs) :
    R.final ⊆ R.kept (laterCount b) :=
  Finset.filter_subset _ _
theorem Process.lost_sub {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs)
    (i : ℕ) : R.lost i ⊆ R.kept i := by
  unfold Process.lost
  split <;> exact Finset.filter_subset _ _
private theorem Process.tested_anti {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs)
    {i j : ℕ} (hij : i ≤ j) : R.tested j ⊆ R.tested i := by
  intro I hI
  obtain ⟨hm, hc, hp⟩ := Finset.mem_filter.mp hI
  exact Finset.mem_filter.mpr ⟨hm, hc, fun k hpos hk => hp k hpos (hk.trans hij)⟩
private theorem Process.kept_anti {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs)
    {i j : ℕ} (hij : i ≤ j) : R.kept j ⊆ R.kept i := by
  intro I hI
  obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hI
  exact Finset.mem_filter.mpr ⟨R.tested_anti hij hm, fun h => hp (h.trans hij)⟩
theorem Process.next_sub {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs)
    {i : ℕ} (hi : i ≤ laterCount b) : R.live (i+1) ⊆ R.live i := by
  rcases hi.lt_or_eq with ht | he
  · simp only [Process.live, ite_eq_left hi, ite_eq_left (Nat.succ_le_of_lt ht)]
    exact R.kept_anti (Nat.le_succ _)
  · subst i
    simpa [Process.live] using R.final_sub
theorem Process.lost_diff {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs)
    {i : ℕ} (hi : i ≤ laterCount b) : R.lost i ⊆ R.live i \ R.live (i+1) := by
  intro I hm
  refine Finset.mem_sdiff.mpr ⟨by simpa only [Process.live, ite_eq_left hi] using R.lost_sub i hm, ?_⟩
  intro hn
  rcases hi.lt_or_eq with ht | he
  · have hf := (Finset.mem_filter.mp
        (show I ∈ (R.kept i).filter _ from by simpa only [Process.lost, dite_eq_left ht] using hm)).2
    have hk : I ∈ R.kept (i+1) := by
      simpa only [Process.live, ite_eq_left (Nat.succ_le_of_lt ht)] using hn
    have hpasses := (Finset.mem_filter.mp (R.kept_sub _ hk)).2.2
    exact hf (hpasses (nextIndex i ht) (by change 0 < i+1; omega) le_rfl)
  · subst i
    have hf := (Finset.mem_filter.mp
        (show I ∈ (R.kept (laterCount b)).filter _ from by
          simpa only [Process.lost, dite_eq_right (Nat.lt_irrefl _)] using hm)).2
    have hf' : I ∈ R.final := by simpa [Process.live] using hn
    exact hf (Finset.mem_filter.mp hf').2
private theorem Process.local_cap {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : HighCore82219.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (estimate : PairedMass) (src : Source b M F rows) (hw : InBand b M.overhead)
    (i : StageIndex b) (hi : 0 < i.val) (square : Bool)
    {A : Finset (Ideal Ambient)} (hA : A ⊆ R.tested i)
    (hdual : square = true → ∀ I ∈ A, dual I) (k : Fin 4) :
    massQ A k ≤ stageCap b i square k := by
  let s := stageAt b i
  let pair := pairAt pairs i
  obtain ⟨ga, gb⟩ := R.sched.stage_guard i i.isLt
  have hr := R.sched.small_reserve _ i.isLt
  have hrpos := R.sched.later_pos (i.val-1) (by have hh : i.val < (HighCore82219.stages b).length := i.isLt; unfold laterCount; omega)
  have hidx : i.val-1+1 = i.val := by omega
  rw [hidx] at hrpos
  exact estimate s.free.shape s.moving.shape s.reserve square pair.free pair.moving
    hrpos hr ga.ode.small gb.ode.small ga.seed_small gb.seed_small ga.ode.jb gb.ode.jb
    pair.free_ne pair.moving_ne
    (src.shape _ (free_listed i) _ _ pair.free_mem)
    (src.shape _ (moving_listed i) _ _ pair.moving_mem) pair.no_moving
    (R.fixed i).free (R.fixed i).moving A hdual (fun I hI => by
      obtain ⟨hp, hc, hpass⟩ := Finset.mem_filter.mp (hA hI)
      have hactive := (R.geometry I hp).1
      have htest := hpass i hi le_rfl
      exact ⟨hactive, htest.2.2, (hc i).1, (hc i).2,
        buffered_order src hw (free_listed i) ga hr hactive htest.1 pair.free_mem,
        buffered_order src hw (moving_listed i) gb hr hactive htest.2.1 pair.moving_mem⟩) k
theorem Process.cap_kept {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : HighCore82219.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (estimate : PairedMass) (src : Source b M F rows) (hw : InBand b M.overhead)
    {i : ℕ} (hi : i ≤ laterCount b) (k : Fin 4) : massQ (R.kept i) k ≤ history b i k := by
  induction i with
  | zero =>
    exact (Nat.cast_le (α := ℚ)).mpr
      ((K1_14_2_2.mass_mono ((R.kept_sub 0).trans (R.tested_sub 0)) k).trans (R.init_mass k))
  | succ i ih =>
    refine le_min ((massQ_mono (R.kept_anti (Nat.le_succ i)) k).trans (ih (by omega))) ?_
    let j := nextIndex i (by omega : i < laterCount b)
    exact R.local_cap estimate src hw j (Nat.succ_pos _) _ (R.kept_sub (i+1))
      (fun h I hI => (Finset.mem_filter.mp hI).2 (of_decide_eq_true h)) k
theorem Process.cap_live {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : HighCore82219.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (estimate : PairedMass) (src : Source b M F rows) (hw : InBand b M.overhead)
    {i : ℕ} (hi : i ≤ laterCount b) (k : Fin 4) : massQ (R.live i) k ≤ history b i k := by
  rw [Process.live, ite_eq_left hi]
  exact R.cap_kept estimate src hw hi k
theorem Process.rank_geometry {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs)
    {I : Ideal Ambient} (hI : I ∈ R.rankExit) : Active I ∧ ¬ dual I :=
  let hm := Finset.mem_filter.mp hI
  ⟨(R.geometry I (R.tested_sub _ hm.1)).1, hm.2⟩
theorem Process.rank_cap {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs)
    (k : Fin 4) : massQ R.rankExit k ≤ rankMass b k := by
  change massQ R.rankExit k ≤ (initialCap b k : ℚ)
  exact (Nat.cast_le (α := ℚ)).mpr ((K1_14_2_2.mass_mono
    ((Finset.filter_subset _ _ : R.rankExit ⊆ R.tested (stopIndex b)).trans
      (R.tested_sub _)) k).trans (R.init_mass k))
theorem Process.retains {b h rows} {pairs : HighCore82219.Pairs b h rows} (R : Process pairs)
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
end HighCore82219_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace HighCore82219_3
noncomputable section
open Polynomial
open HighCore82219 (AnchorModel AnchoredFamily K p)
open HighCore82219 (CurveTariff curveUnit)
open HighCore82219PrefixHelpers (curveMarks mem_curveMarks direct_curve_count)
open K1_14 (Seeds graphEval)
open K1_14_2 (Ambient OnJet SeedField RootSeedSection)
open K1_14_2_2 (CutCover CurveGeometry)
open K1_14_2_3 (SeedSlice seedImage rootImage constantCoefficients DefinedOverConstants seedLength
  yLength)
open private on_root on_seed moving_graph_count seed_graph_count equal_image_degree
  union_card_le from ProximityPrize.SubmissionLower.Fast062
open scoped BigOperators Classical
private theorem projected_curve : K1_14_2_3.c2 :=
  K1_14_2_3_2.of_children K1_14_2_3_2_1.proof K1_14_2_3_2_2.proof
private theorem seed_slice {I : Ideal Ambient} (h : CurveGeometry I) : SeedSlice I :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
private theorem mark_graph {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : seedImage I = Ideal.span {C}) :
    ∀ z ∈ (Γ.filter (OnParent F I)).image M.label, graphEval z C = 0 := by
  intro z hz
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
  apply on_seed (Finset.mem_filter.mp hγ).2
  rw [hC]
  exact Ideal.mem_span_singleton_self C
private theorem translated_card {u del} (M : AnchorModel u del) (T : Finset K) :
    (T.image M.label).card = T.card :=
  Finset.card_image_of_injective _ (fun _ _ hab => sub_left_inj.mp hab)
private theorem direct_count {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : C ≠ 0) (hI : seedImage I = Ideal.span {C})
    (hp : C.totalDegree < p) :
    (Γ.filter (OnParent F I)).card ≤ (p+1)*C.totalDegree := by
  have h := seed_graph_count C hC hp ((Γ.filter (OnParent F I)).image M.label) (mark_graph F hI)
  rwa [translated_card] at h
private theorem interpolate (hi g : ℕ) (a h d H T : ℚ) (hg : 0 < g)
    (hH : 0 ≤ H) (hd : 0 ≤ d) (hu : RateOK hi a h)
    (direct : T ≤ ((p+1 : ℕ) : ℚ)*d)
    (tariff : g ≤ 80 → T ≤ curveUnit hi g * H + g) :
    T ≤ a*(d*g) + h*H + g := by
  let q : ℚ := (p+1 : ℕ)
  have hq : 0 < q := Nat.cast_pos.mpr (Nat.succ_pos p)
  have ha : 0 ≤ a := (show 0 ≤ q/81 by positivity).trans hu.degree
  by_cases large : q ≤ a*g
  · calc
      T ≤ q*d := direct
      _ ≤ (a*g)*d := mul_le_mul_of_nonneg_right large hd
      _ = a*(d*g) := by ring
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        have hgq : (0 : ℚ) ≤ g := Nat.cast_nonneg _
        linarith
  · have hgsmall : g ≤ 80 := by
      by_contra! h
      have hgQ : (81 : ℚ) ≤ g := by exact_mod_cast Nat.succ_le_of_lt h
      have he : q/81*81 = q := by ring
      apply large
      rw [← he]
      exact mul_le_mul hu.degree hgQ (by norm_num) ha
    let θ := a*g/q
    have hθ : 0 ≤ θ := div_nonneg (mul_nonneg ha (Nat.cast_nonneg _)) hq.le
    have hc : 0 ≤ 1-θ := sub_nonneg.mpr ((div_le_iff₀ hq).mpr (by simpa using (le_of_lt (lt_of_not_ge large))))
    have hh : (1-θ)*curveUnit hi g ≤ h := by
      have hf := hu.interpolation g hg hgsmall
      rw [max_eq_right hc] at hf
      exact hf
    calc
      T = θ*T+(1-θ)*T := by ring
      _ ≤ θ*(q*d)+(1-θ)*(curveUnit hi g*H+g) :=
        add_le_add (mul_le_mul_of_nonneg_left direct hθ)
          (mul_le_mul_of_nonneg_left (tariff hgsmall) hc)
      _ = a*(d*g)+((1-θ)*curveUnit hi g)*H+(1-θ)*g := by
        dsimp only [θ]
        field_simp [hq.ne']; ring
      _ ≤ _ := by
        have hlast : (1-θ)*(g : ℚ) ≤ g := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (sub_le_self 1 hθ) (Nat.cast_nonneg (α := ℚ) g)
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hh hH)) hlast
private theorem rated_component {b u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (tariff : CurveTariff b M F) {a h globalCap localCap : ℚ} (hu : RateOK (finish b) a h)
    (hmin : min globalCap localCap ≤ a) {I : Ideal Ambient} (geom : CurveGeometry I)
    (hglobal : (seedLength I : ℚ) ≤ globalCap) (hlocal : (seedLength I : ℚ) ≤ localCap)
    (hp : seedLength I < p) :
    ((Γ.filter (OnParent F I)).card : ℚ) ≤
      a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
  let T := Γ.filter (OnParent F I)
  let D := seedLength I
  let H := yLength I
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg _
  have hH : (0 : ℚ) ≤ H := Nat.cast_nonneg _
  have ha : 0 ≤ a := (show (0 : ℚ) ≤ ((p+1 : ℕ) : ℚ)/81 by positivity).trans hu.degree
  obtain ⟨f, hf, he, hpos, hd⟩ := K1_14_2_3_1.proof I (seed_slice geom)
  have hdq : (f.totalDegree : ℚ) ≤ D := by exact_mod_cast hd
  by_cases hconst : DefinedOverConstants (seedImage I)
  · obtain ⟨Q, hQ, heQ⟩ := hconst
    have hdeg : f.totalDegree = Q.totalDegree := equal_image_degree f hf.ne_zero Q (he.symm.trans heQ)
    obtain ⟨g, hg, hroot, hgD⟩ := projected_curve I Q (seed_slice geom) geom.2.2.2.2 hQ heQ
    have hgcap : g ≤ D := (Nat.le_mul_of_pos_left g (hdeg ▸ hpos)).trans hgD
    have hp' : Module.finrank SeedField (RootSeedSection (rootImage I)) < p := by
      obtain ⟨_, Q', hQ', hQ'proj, _, hlen, _, _⟩ := hroot
      have heQ' : seedImage I = Ideal.span {MvPolynomial.map constantCoefficients Q'} := hQ'proj
      have hdeg' := equal_image_degree f hf.ne_zero Q' (he.symm.trans heQ')
      rw [hlen, ← hdeg', hdeg]
      exact hgD.trans_lt hp
    have hdir : (T.card : ℚ) ≤ ((p+1 : ℕ) : ℚ)*(Q.totalDegree : ℚ) := by
      have hcount := direct_count F hf.ne_zero he (hd.trans_lt hp)
      rw [hdeg] at hcount
      exact_mod_cast hcount
    have htar (hgi : g ≤ 80) : (T.card : ℚ) ≤ curveUnit (finish b) g * H + g :=
      tariff T (Finset.filter_subset _ _) (rootImage I) g H hg hgi hroot hp'
        (fun _ hz => on_root (Finset.mem_filter.mp hz).2)
    have hfirst := interpolate (finish b) g a h Q.totalDegree H T.card hg hH
      (Nat.cast_nonneg _) hu hdir htar
    have hgDq : (Q.totalDegree : ℚ)*g ≤ D := by exact_mod_cast hgD
    have hgcapq : (g : ℚ) ≤ D := by exact_mod_cast hgcap
    exact hfirst.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hgDq ha) le_rfl)
      hgcapq)
  · have hmov := moving_graph_count p f hf (he ▸ hconst)
      (T.image M.label) (mark_graph F he)
    rw [translated_card] at hmov
    have hcard : (T.card : ℚ) ≤ (f.totalDegree : ℚ)^2 := by exact_mod_cast hmov
    have hd0 : (0 : ℚ) ≤ f.totalDegree := Nat.cast_nonneg _
    have har : (f.totalDegree : ℚ) ≤ a :=
      (le_min (hdq.trans hglobal) (hdq.trans hlocal)).trans hmin
    calc
      _ ≤ (f.totalDegree : ℚ)^2 := hcard
      _ ≤ a*D := by rw [pow_two]; exact mul_le_mul har hdq hd0 ha
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        linarith
theorem rated_curve_count {b u del} {M : AnchorModel u del} {Γ}
    (F : AnchoredFamily M Γ) (tariff : CurveTariff b M F)
    {a h globalCap : ℚ} (hu : RateOK (finish b) a h) (C : CutCover)
    (hglobal : (C.cost 0 : ℚ) ≤ globalCap)
    (hdegree : min globalCap (C.cost 0 : ℚ) ≤ a) (hp : C.cost 0 < p) :
    ((curveMarks F C).card : ℚ) ≤ a*(C.cost 0 : ℚ)+h*(C.cost 1 : ℚ)+C.cost 0 := by
  have hsum : ∑ I ∈ C.curves, seedLength I = C.cost 0 := rfl
  have hsumH : ∑ I ∈ C.curves, yLength I = C.cost 1 := rfl
  have hcount (I : Ideal Ambient) (hI : I ∈ C.curves) :
      ((Γ.filter (OnParent F I)).card : ℚ) ≤
        a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
    have hn : seedLength I ≤ C.cost 0 := hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hI
    have hq : (seedLength I : ℚ) ≤ (C.cost 0 : ℚ) := by exact_mod_cast hn
    exact rated_component F tariff hu hdegree (C.geometric I hI) (hq.trans hglobal) hq (hn.trans_lt hp)
  calc
    _ ≤ ∑ I ∈ C.curves, ((Γ.filter (OnParent F I)).card : ℚ) := union_card_le _ _
    _ ≤ ∑ I ∈ C.curves, (a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I) :=
      Finset.sum_le_sum hcount
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum, hsum, hsumH]
end
end HighCore82219_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace HighCore82219_3
noncomputable section
open HighCore82219 (AnchorModel AnchoredFamily K p)
open HighCore82219 (terminal Source InBand fees CurveTariff)
open HighCore82219PrefixHelpers (curveMarks mem_curveMarks direct_curve_count)
open P1_7_4 (massQ_mono dotQ_mono_mass dotQ_scale_add bill_bound flat_bill
  curveMarks direct_curve_count mem_curveMarks)
open K1_14 (Banks Jet jetAt)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (CutCover RowCaps mass)
open scoped Classical BigOperators
theorem cutWeight_nonneg (b : HighCore82219.Band) (fee : Fin 3) (i : ℕ) (k : Fin 4) :
    0 ≤ cutWeight b fee i k := Nat.cast_nonneg _
theorem dot_cast (b : HighCore82219.Band) (fee : Fin 3) (i : ℕ) (S : Finset (Ideal Ambient)) :
    ((K1_14_2_2.dot (K1_14_2_2.weight (cutShape b i) fee) (mass S) : ℕ) : ℚ) =
      dotQ (cutWeight b fee i) (massQ S) := by
  simp only [dotQ, K1_14_2_2.dot, cutWeight, massQ, Nat.cast_sum, Nat.cast_mul]
theorem history_le_initial (b : HighCore82219.Band) (i : ℕ) (k : Fin 4) :
    history b i k ≤ initialCap b k := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact (min_le_left _ _).trans ih
structure FailureBooks {b u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} {pairs : HighCore82219.Pairs b M.overhead.toNat rows} (R : Process pairs) where
  loss : Finset K
  point : Finset K
  loss_le : loss.card ≤ (fees b).loss
  point_le : point.card ≤ (fees b).point
  covers : ∀ i ≤ laterCount b, ∀ γ ∈ Γ, ∀ I ∈ R.lost i,
    OnParent F I γ → γ ∈ point ∨ γ ∈ loss
private theorem properBin {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : HighCore82219.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (src : Source b M F rows) (i : ℕ) :
    ∃ C : CutCover, (∀ fee, (C.cost fee : ℚ) ≤ dotQ (cutWeight b fee i) (massQ (R.lost i))) ∧
      ∀ γ ∈ Γ, (∃ I ∈ R.lost i, OnParent F I γ) →
        γ ∈ C.direct ∨ ∃ I ∈ C.curves, OnParent F I γ := by
  have geom (I : Ideal Ambient) (hI : I ∈ R.lost i) :=
    (R.geometry I (R.tested_sub i (R.kept_sub i (R.lost_sub i hI)))).1
  have hj : (cutShape b i).J ≤ (cutShape b i).B := by
    by_cases hi : i < laterCount b
    · rw [cutShape, ite_eq_left hi]
      exact Nat.le_add_left _ _
    · rw [cutShape, ite_eq_right hi]
      exact R.sched.terminal_guard.ode.jb
  have cutter (I : Ideal Ambient) (hI : I ∈ R.lost i) :
      ∃ P : Jet, RowCaps P (cutShape b i) ∧ toJet P ∉ I ∧
        ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0 := by
    by_cases hi : i < laterCount b
    · rw [cutShape, ite_eq_left hi]
      rw [Process.lost, dite_eq_left hi] at hI
      exact failed_pair src R.sched pairs (nextIndex i hi) (Finset.mem_filter.mp hI).2
    · rw [cutShape, ite_eq_right hi]
      rw [Process.lost, dite_eq_right hi] at hI
      obtain ⟨P, hP, hproper, hzero⟩ := failed_bank src (Or.inl rfl) R.sched.terminal_guard.pos
        (Finset.mem_filter.mp hI).2
      exact ⟨P, hP, hproper, fun γ hγ _ => hzero γ hγ⟩
  obtain ⟨C, hC, hcover⟩ := combined_cuts (R.lost i) (cutShape b i) hj geom cutter
  refine ⟨C, fun fee => ?_, hcover⟩
  rw [← dot_cast]
  exact (Nat.cast_le (α := ℚ)).mpr (hC fee)
theorem failure_books {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : HighCore82219.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (src : Source b M F rows) (hw : InBand b M.overhead) (est : PairedMass)
    (ledger : LossLedger b) (tariff : (start b) < 7773 → CurveTariff b M F) :
    Nonempty (FailureBooks F R) := by
  let n := laterCount b+1
  choose C hcost hcover using properBin R src
  let points := (Finset.range n).biUnion fun i => (C i).direct
  let lost := (Finset.range n).biUnion fun i => curveMarks F (C i)
  have next : ∀ i < n, R.live (i+1) ⊆ R.live i :=
    fun _ hi => R.next_sub (Nat.le_of_lt_succ hi)
  have fail : ∀ i < n, R.lost i ⊆ R.live i \ R.live (i+1) :=
    fun _ hi => R.lost_diff (Nat.le_of_lt_succ hi)
  have caps : ∀ i < n, ∀ k, massQ (R.live i) k ≤ history b i k :=
    fun _ hi => R.cap_live est src hw (Nat.le_of_lt_succ hi)
  have sumD : (∑ i ∈ Finset.range n, ((C i).cost 0 : ℚ)) ≤ seedLimit b :=
    (Finset.sum_le_sum fun i _ => hcost i 0).trans
      (bill_bound n (cutWeight b 0) (history b) R.live R.lost next fail caps)
  have hD (i : ℕ) (hi : i ≤ laterCount b) : ((C i).cost 0 : ℚ) ≤ seedLimit b :=
    (Finset.single_le_sum (fun j _ => Nat.cast_nonneg (α := ℚ) ((C j).cost 0))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).trans sumD
  have hp (i : ℕ) (hi : i ≤ laterCount b) : (C i).cost 0 < p :=
    (Nat.cast_lt (α := ℚ)).mp ((hD i hi).trans_lt ledger.seed_small)
  have points_paid : (points.card : ℚ) ≤ (fees b).point := by
    let start : Mass :=
      ![(initialCap b 0 : ℚ), (initialCap b 1 : ℚ), (initialCap b 2 : ℚ), (initialE b : ℚ)]
    have flat : ∀ i < n, ∀ k, massQ (R.live i) k ≤ start k := by
      intro i hi k
      have hc := (caps i hi k).trans (history_le_initial b i k)
      fin_cases k
      · exact hc
      · exact hc
      · exact hc
      · exact hc.trans ((Nat.cast_le (α := ℚ)).mpr R.sched.initial_e_ge)
    calc
      _ ≤ ∑ i ∈ Finset.range n, ((C i).cost 2 : ℚ) := by
        exact_mod_cast (Finset.card_biUnion_le : points.card ≤
          ∑ i ∈ Finset.range n, (C i).direct.card)
      _ ≤ ∑ i ∈ Finset.range n, dotQ (cutWeight b 2 i) (massQ (R.lost i)) :=
        Finset.sum_le_sum fun i _ => hcost i 2
      _ ≤ weightedBill n (cutWeight b 2) (fun _ => start) :=
        bill_bound n (cutWeight b 2) (fun _ => start) R.live R.lost next fail flat
      _ = pointLimit b := flat_bill _ _ _
      _ ≤ _ := ledger.points
  have hsum : (lost.card : ℚ) ≤ ∑ i ∈ Finset.range n, ((curveMarks F (C i)).card : ℚ) := by
    exact_mod_cast (Finset.card_biUnion_le : lost.card ≤
      ∑ i ∈ Finset.range n, (curveMarks F (C i)).card)
  have loss_paid : (lost.card : ℚ) ≤ (fees b).loss := by
    by_cases hd : (start b) < 7773
    · obtain ⟨a, h, hrate, hpay⟩ := ledger.discount hd
      have per_bin (i : ℕ) (hi : i ∈ Finset.range n) :
          ((curveMarks F (C i)).card : ℚ) ≤
            dotQ (lossWeight b a h i) (massQ (R.lost i)) + (C i).cost 0 := by
        have hi' : i ≤ laterCount b := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        obtain ⟨rate, ha⟩ := hrate i hi'
        have hloc : (C i).cost 0 ≤ dotQ (cutWeight b 0 i) (history b i) :=
          (hcost i 0).trans (dotQ_mono_mass (cutWeight_nonneg b 0 i)
            (fun k => (massQ_mono
              (fun _ hI => (Finset.mem_sdiff.mp (fail i (Finset.mem_range.mp hi) hI)).1) k).trans
                (caps i (Finset.mem_range.mp hi) k)))
        have hr := rated_curve_count F (tariff hd) rate (C i) (hD i hi')
          ((min_le_min le_rfl hloc).trans ha) (hp i hi')
        have a0 : 0 ≤ a i := (show (0 : ℚ) ≤ ((p+1 : ℕ) : ℚ)/81 by positivity).trans rate.degree
        calc
          _ ≤ a i*((C i).cost 0 : ℚ) + h i*((C i).cost 1 : ℚ) + (C i).cost 0 := hr
          _ ≤ a i*dotQ (cutWeight b 0 i) (massQ (R.lost i)) +
                h i*dotQ (cutWeight b 1 i) (massQ (R.lost i)) + (C i).cost 0 :=
            add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hcost i 0) a0)
              (mul_le_mul_of_nonneg_left (hcost i 1) rate.height)) le_rfl
          _ = _ := by rw [dotQ_scale_add]; rfl
      calc
        _ ≤ ∑ i ∈ Finset.range n, ((curveMarks F (C i)).card : ℚ) := hsum
        _ ≤ ∑ i ∈ Finset.range n, (dotQ (lossWeight b a h i) (massQ (R.lost i)) +
            ((C i).cost 0 : ℚ)) := Finset.sum_le_sum per_bin
        _ ≤ weightedBill n (lossWeight b a h) (history b) + seedLimit b := by
          rw [Finset.sum_add_distrib]
          exact add_le_add (bill_bound n (lossWeight b a h) (history b) R.live R.lost next fail caps) sumD
        _ ≤ _ := hpay
    · calc
        _ ≤ ∑ i ∈ Finset.range n, ((curveMarks F (C i)).card : ℚ) := hsum
        _ ≤ ∑ i ∈ Finset.range n, ((p+1 : ℕ) : ℚ)*((C i).cost 0 : ℚ) :=
          Finset.sum_le_sum fun i hi => direct_curve_count F (C i)
            (hp i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
        _ ≤ ((p+1 : ℕ) : ℚ)*seedLimit b := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left sumD (Nat.cast_nonneg _)
        _ ≤ _ := ledger.direct (Nat.le_of_not_gt hd)
  refine ⟨⟨lost, points, (Nat.cast_le (α := ℚ)).mp loss_paid,
    (Nat.cast_le (α := ℚ)).mp points_paid, ?_⟩⟩
  intro i hi γ hγ I hI hm
  have hr := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  rcases hcover i γ hγ ⟨I, hI, hm⟩ with hd | ⟨J, hJ, hj⟩
  · exact Or.inl (Finset.mem_biUnion.mpr ⟨i, hr, hd⟩)
  · exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hr, mem_curveMarks (F := F) hγ hJ hj⟩)
end
end HighCore82219_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1500000
namespace HighCore82219_3
noncomputable section
open Polynomial
open HighCore82219 (K p AnchorModel AnchoredFamily)
open HighCore82219 (InBand stages terminal Source CurveTariff PrefixBooks PrefixInventory fees)
open K1_14 (Jet Banks seedHasse jetAt atX graphEval)
open K1_14_2 (Ambient ODE fixedAt)
open K1_14_2_2 (FixedPart ODECaps fixedOn dual)
open K1_14_3 (SeedCover Surface RowCaps NoMovingCommon)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open scoped BigOperators Classical
def c1 : Prop :=
  ∀ (b : HighCore82219.Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    ScheduleOK b →
    ∀ P Q : Jet, P ≠ 0 → Q ≠ 0 → NoMovingCommon P Q →
    RowCaps P (stageAt b 0).free.shape → RowCaps Q (stageAt b 0).moving.shape →
    ∀ (A : FixedPart P (stageAt b 0).free.shape) (B : FixedPart Q (stageAt b 0).moving.shape),
    (∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 ∧ jetAt Q (M.label γ) (F.scalar γ) = 0) →
    ∀ later : ℕ → Jet,
    (∀ i ∈ introIndices b, later i ≠ 0 ∧ RowCaps (later i) (stageAt b i).free.shape ∧
      ∀ j a, a ≤ (stageAt b i).reserve →
        ∀ γ ∈ Γ, jetAt (seedHasse j a (later i)) (M.label γ) (F.scalar γ) = 0) →
    Nonempty (InitialCover M F b A.equation B.equation)
theorem paired_mass : PairedMass := P1_7_4_2.proof
def c2 : Prop :=
  ∀ (b : HighCore82219.Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b M.overhead →
    ∀ B J : ℕ, ODEGuard B J →
    ∀ G : ODE, ODECaps G B J → ∀ T ⊆ Γ,
    (∀ γ ∈ T, fixedAt G (F.scalar γ) = 0) → T.card ≤ fixedFee (finish b) B J
def c3 : Prop := ∀ b : HighCore82219.Band, ScheduleOK b
def c4 : Prop := ∀ b : HighCore82219.Band, LossLedger b
private def fixedMarks {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (G : ODE) : Finset K := Γ.filter fun γ => fixedAt G (F.scalar γ) = 0
private theorem fixed_paid (hcount : c2) {b u del} {M : AnchorModel u del} {Γ}
    (F : AnchoredFamily M Γ) (hw : InBand b M.overhead) {B J : ℕ}
    (guard : ODEGuard B J) {G : ODE} (cap : ODECaps G B J) :
    (fixedMarks F G).card ≤ fixedFee (finish b) B J :=
  hcount b u del M Γ F hw B J guard G cap _ (Finset.filter_subset _ _)
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
private def fixedBook {b u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} {pairs : HighCore82219.Pairs b M.overhead.toNat rows} (R : Process pairs) : Finset K :=
  Finset.univ.biUnion fun i : StageIndex b =>
    fixedMarks F (R.fixed i).free.equation ∪ fixedMarks F (R.fixed i).moving.equation
private theorem fixed_book_paid (hcount : c2) {b u del} {M : AnchorModel u del} {Γ}
    (F : AnchoredFamily M Γ) (hw : InBand b M.overhead) {rows : Banks}
    {pairs : HighCore82219.Pairs b M.overhead.toNat rows} (R : Process pairs) :
    (fixedBook F R).card ≤ (fees b).fixedODE := by
  let price (i : ℕ) :=
    fixedFee (finish b) (stageAt b i).free.shape.B (stageAt b i).free.shape.J +
      fixedFee (finish b) (stageAt b i).moving.shape.B (stageAt b i).moving.shape.J
  calc
    _ ≤ ∑ i : StageIndex b,
        (fixedMarks F (R.fixed i).free.equation ∪ fixedMarks F (R.fixed i).moving.equation).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ i : StageIndex b, price i := by
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨ga, gb⟩ := R.sched.stage_guard i i.isLt
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add
        (fixed_paid hcount F hw ga.ode (R.fixed i).free.equation_caps)
        (fixed_paid hcount F hw gb.ode (R.fixed i).moving.equation_caps))
    _ = fixedBudget b := Fin.sum_univ_eq_sum_range price (stages b).length
    _ ≤ _ := R.sched.fixed
private theorem mem_fixed_left {b u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} {pairs : HighCore82219.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (i : StageIndex b) {γ : K} (hγ : γ ∈ Γ) (hz : fixedAt (R.fixed i).free.equation (F.scalar γ) = 0) :
    γ ∈ fixedBook F R :=
  Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hz⟩)⟩
private theorem mem_fixed_right {b u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {rows : Banks} {pairs : HighCore82219.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (i : StageIndex b) {γ : K} (hγ : γ ∈ Γ) (hz : fixedAt (R.fixed i).moving.equation (F.scalar γ) = 0) :
    γ ∈ fixedBook F R :=
  Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hz⟩)⟩
private theorem floor_bound {n : ℕ} {r : ℚ} (h : (n : ℚ) ≤ r) : n ≤ r.floor.toNat := by
  have hi : (n : ℤ) ≤ r.floor := Rat.le_floor_iff.mpr (by exact_mod_cast h)
  simpa using Int.toNat_le_toNat hi
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) : HighCore82219.c3 := by
  classical
  intro b u del M Γ F hw _ _ _ tariff rows src pairs
  let sched := h3 b
  let zero : StageIndex b := ⟨0, sched.stages_pos⟩
  let P := pairAt pairs zero
  let fixed := fixedRows src pairs
  obtain ⟨ga, gb⟩ := sched.stage_guard 0 sched.stages_pos
  have hf := src.shape _ (free_listed zero) _ _ P.free_mem
  have hg := src.shape _ (moving_listed zero) _ _ P.moving_mem
  let later (i : ℕ) : Jet := if hi : i < (stages b).length then (pairAt pairs ⟨i, hi⟩).free else 0
  obtain ⟨initial⟩ := h1 b u del M Γ F sched P.free P.moving P.free_ne P.moving_ne
    P.no_moving hf hg (fixed zero).free (fixed zero).moving (fun γ hγ =>
      ⟨bank_zero src (free_listed zero) ga.pos (Nat.sub_le _ _) P.free_mem γ hγ,
        bank_zero src (moving_listed zero) gb.pos (Nat.sub_le _ _) P.moving_mem γ hγ⟩) later (by
      intro i hi
      obtain ⟨_, hsize⟩ := sched.intro_pos i hi
      let j : StageIndex b := ⟨i, hsize⟩
      let pair := pairAt pairs j
      simp only [later, dite_eq_left hsize]
      exact ⟨pair.free_ne, src.shape _ (free_listed j) _ _ pair.free_mem,
        fun k a ha => intro_zero src hw (free_listed j) (sched.stage_guard i hsize).1 pair.free_mem k a ha⟩)
  let R : Process pairs :=
    ⟨sched, initial.parents, fixed, fun I hI => ⟨initial.active I hI, initial.height_two I hI⟩,
      initial.mass_bound⟩
  obtain ⟨losses⟩ := failure_books R src hw paired_mass (h4 b) tariff
  obtain ⟨G, hgcap, hG⟩ := P1_7_4.rank_equation R.rankExit (fun _ hI => R.rank_geometry hI)
    (B := rankB b) (J := rankJ b) (floor_bound (R.rank_cap 1))
    (floor_bound (R.rank_cap 2))
  let seed := Γ.filter fun γ => initial.seed.Covers (M.label γ)
  let contents := Γ.filter fun γ => graphEval (M.label γ) initial.content = 0
  let ords := Γ.filter fun γ => atX (F.scalar γ) ∈ initial.ordinates
  let rank := fixedMarks F G
  have label_inj : Function.Injective M.label := fun _ _ h => sub_left_inj.mp h
  have hseed : seed.card ≤ (fees b).lowSeed := by
    have h := K1_14_3.seed_count (T := seed) label_inj.injOn initial.seed
      (initial.seed_le.trans_lt (sched.initial_small 2)) (fun _ hγ => (Finset.mem_filter.mp hγ).2)
    exact (h.trans (Nat.add_le_add (Nat.mul_le_mul_left _ initial.seed_le) initial.seed_points)).trans
      sched.low_seed
  have hcontents : contents.card ≤ (fees b).content := by
    let C : SeedCover := ⟨initial.content, initial.content_ne, ∅⟩
    have h := K1_14_3.seed_count (T := contents) label_inj.injOn C
      (initial.content_le.trans_lt sched.content_small)
      (fun _ hγ => Or.inl (Finset.mem_filter.mp hγ).2)
    have h' : contents.card ≤ (p+1)*initial.content.totalDegree := by
      simpa only [C, Finset.card_empty, Nat.add_zero] using h
    exact (h'.trans (Nat.mul_le_mul_left _ initial.content_le)).trans sched.content
  have hords : ords.card ≤ initialCap b 0 :=
    (Finset.card_le_card_of_injOn (fun γ => atX (F.scalar γ))
      (fun _ hγ => (Finset.mem_filter.mp hγ).2)
      (fun _ hγ _ hδ h => F.distinct (Finset.mem_filter.mp hγ).1 (Finset.mem_filter.mp hδ).1
        (K1_14_3.scalar_atX_injective h))).trans initial.ordinate_le
  let books : PrefixBooks b :=
    ⟨losses.loss, losses.point, seed, ords ∪ rank, fixedBook F R, contents,
      losses.loss_le, losses.point_le, hseed,
      ((Finset.card_union_le _ _).trans (Nat.add_le_add hords
        (fixed_paid h2 F hw sched.rank_guard hgcap))).trans sched.low_jet,
      fixed_book_paid h2 F hw R, hcontents⟩
  have initial_mem (I : ↥R.final) : I.1 ∈ R.parents :=
    R.tested_sub _ (R.kept_sub _ (R.final_sub I.2))
  let toSurface (I : ↥R.final) : Surface := surfaceOf I.1 (R.geometry _ (initial_mem I)).1.prime
  refine ⟨{
    books := books
    parents := R.final.attach.image toSurface
    geometric := ?_
    stage_pass := ?_
    terminal_pass := ?_
    covers := ?_ }⟩
  · intro q hq
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hq
    have hgeom := R.geometry _ (initial_mem I)
    exact parent_of_dual hgeom.1 hgeom.2
      ((Finset.mem_filter.mp (R.final_sub I.2)).2 sched.stop_le)
  · intro q hq s hs hpositive
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hs
    let j : StageIndex b := ⟨i, hi⟩
    have ht : stageAt b j = s := by
      simpa [j, stageAt, List.getElem?_eq_getElem hi] using he
    clear he
    subst s
    have htest := (Finset.mem_filter.mp (R.kept_sub _ (R.final_sub I.2))).2.2
    have hj : 0 < j.val := by
      by_contra! hbad
      have hz : j.val = 0 := Nat.eq_zero_of_le_zero hbad
      have hr : (stageAt b j).reserve = 0 := by rw [hz, sched.zero]
      omega
    exact surface_pass (R.geometry _ (initial_mem I)).1.prime
      (htest j hj (by have hh : i < (HighCore82219.stages b).length := hi; unfold laterCount; dsimp [j]; omega))
  · intro q hq
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp I.2).2
  · intro γ hγ
    by_cases hpaid : γ ∈ books.union
    · exact Or.inl hpaid
    right
    have forbid_seed (h : γ ∈ seed) : False := hpaid (by
      simp only [PrefixBooks.union, books, Finset.mem_union]; tauto)
    have forbid_contents (h : γ ∈ contents) : False := hpaid (by
      simp only [PrefixBooks.union, books, Finset.mem_union]; tauto)
    have forbid_ords (h : γ ∈ ords) : False := hpaid (by
      simp only [PrefixBooks.union, books, Finset.mem_union]; tauto)
    have forbid_rank (h : γ ∈ rank) : False := hpaid (by
      simp only [PrefixBooks.union, books, Finset.mem_union]; tauto)
    have forbid_fixed (h : γ ∈ fixedBook F R) : False := hpaid (by
      simp only [PrefixBooks.union, books, Finset.mem_union]; tauto)
    have forbid_loss (h : γ ∈ losses.point ∨ γ ∈ losses.loss) : False := hpaid (by
      simp only [PrefixBooks.union, books, Finset.mem_union]; tauto)
    rcases initial.covers γ hγ with hz | ho | hc | ha | hb | ⟨I, hI, hm⟩
    · exact (forbid_seed (Finset.mem_filter.mpr ⟨hγ, hz⟩)).elim
    · exact (forbid_ords (Finset.mem_filter.mpr ⟨hγ, ho⟩)).elim
    · exact (forbid_contents (Finset.mem_filter.mpr ⟨hγ, hc⟩)).elim
    · exact (forbid_fixed (mem_fixed_left F R zero hγ ha)).elim
    · exact (forbid_fixed (mem_fixed_right F R zero hγ hb)).elim
    · have hclean : R.Clean I := fun j =>
        ⟨fun hj => forbid_fixed (mem_fixed_left F R j hγ (fixed_zero hm hj)),
          fun hj => forbid_fixed (mem_fixed_right F R j hγ (fixed_zero hm hj))⟩
      have hnotRank : I ∉ R.rankExit := fun h => forbid_rank
        (Finset.mem_filter.mpr ⟨hγ, fixed_zero hm (hG I h)⟩)
      have hnotLost : ∀ i ≤ laterCount b, I ∉ R.lost i := fun i hi h =>
        forbid_loss (losses.covers i hi γ hγ I h hm)
      let J : ↥R.final := ⟨I, R.retains hI hclean hnotRank hnotLost⟩
      exact ⟨toSurface J, Finset.mem_image_of_mem _ (Finset.mem_attach _ _), on_surface _ hm⟩
end
end HighCore82219_3
end
section
namespace HighCore82219_3_1
noncomputable section
open HighCore82219 (AnchorModel AnchoredFamily)
open HighCore82219_3 (stageAt initialCap OnParent)
open P1_7_4_1 (SectionGeometry)
open K1_14 (Seeds graphEval)
open K1_14_2 (Ambient ODE fixedAt)
open K1_14_2_2 (Fits)
structure AffineCover {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (b : HighCore82219.Band) (G H : ODE) where
  components : Finset (Ideal Ambient)
  geometry : SectionGeometry components
  fits : Fits components (initialCap b)
  content : Seeds
  content_ne : content ≠ 0
  content_le : content.totalDegree ≤ (stageAt b 0).free.shape.U + (stageAt b 0).moving.shape.U
  covers : ∀ γ ∈ Γ, graphEval (M.label γ) content = 0 ∨
    fixedAt G (F.scalar γ) = 0 ∨ fixedAt H (F.scalar γ) = 0 ∨
      ∃ I ∈ components, OnParent F I γ
end
end HighCore82219_3_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
namespace HighCore82219_3_1
noncomputable section
open HighCore82219 (K p AnchorModel AnchoredFamily )
open HighCore82219_3 (ScheduleOK stageAt introIndices initialCap)
open P1_7_4 (sharedBound cornerBound)
open P1_7_4_1 (Stripped proper_cover collect ordinary_component_cover)
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open K1_14_3 (NoMovingCommon)
open K1_14_2_2_2_1 (extractOrdinary)
open scoped BigOperators Classical
open private gcd_caps multiset_prod_ne_zero distinct_le_degree seed_degree_mul
  atMark_prod_eq_zero jetAt_mul jetAt_ordinary from ProximityPrize.SubmissionLower.Fast051
open private sharedBound_zero P1_7_4_1_1.floor_bound from ProximityPrize.SubmissionLower.UpperBranch4
private theorem zero_ledger {b : HighCore82219.Band} (empty : (introIndices b).isEmpty = true)
    {x z : ℕ} (k : Fin 4)
    (hx : x ≤ min (stageAt b 0).free.shape.U (stageAt b 0).moving.shape.U)
    (hz : z ≤ min (stageAt b 0).free.shape.B (stageAt b 0).moving.shape.B)
    (hs : (stageAt b 0).free.shape.J ≤ (stageAt b 0).free.shape.B)
    (ht : (stageAt b 0).moving.shape.J ≤ (stageAt b 0).moving.shape.B) :
    residualBudget (afterGcd (stageAt b 0).free.shape x z)
      (afterGcd (stageAt b 0).moving.shape x z) k + ordinaryBudget x z k ≤ initialCap b k := by
  have h := P1_7_4_2.shared_le_corner (stageAt b 0).free.shape (stageAt b 0).moving.shape
    (r := 1) (m := 1) false k hx hz hs ht
  rw [sharedBound_zero] at h
  simpa only [initialCap, empty, ite_true] using P1_7_4_1_1.floor_bound h
theorem zero_cover {b : HighCore82219.Band} (sched : ScheduleOK b)
    (empty : (introIndices b).isEmpty = true)
    {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {P Q : Jet} (hnc : NoMovingCommon P Q)
    {A : FixedPart P (stageAt b 0).free.shape} {B : FixedPart Q (stageAt b 0).moving.shape}
    (a : Stripped A) (b' : Stripped B)
    (hrows : ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 ∧
      jetAt Q (M.label γ) (F.scalar γ) = 0) :
    Nonempty (AffineCover F b A.equation B.equation) := by
  classical
  let s := (stageAt b 0).free.shape
  let t := (stageAt b 0).moving.shape
  obtain ⟨gs, gt⟩ := sched.stage_guard 0 sched.stages_pos
  have hord (D : Jet) (hD : Irreducible D) (hda : D ∣ a.row) (hdb : D ∣ b'.row) :
      D.natDegree = 0 := by
    by_contra hp
    obtain ⟨G, rfl⟩ := hnc D hD (hda.trans a.row_dvd) (hdb.trans b'.row_dvd)
      (Nat.pos_of_ne_zero hp)
    exact a.no_fixed G hD hda
  obtain ⟨N, L, T, hL, hT, hproper, hN⟩ :=
    extractOrdinary a.row b'.row a.row_ne b'.row_ne a.primitive hord
  let x := ordinarySeedDegree N.prod
  let z := N.prod.natDegree
  have hN0 : ∀ f ∈ N, f ≠ 0 := fun f hf => (hN f hf).1.ne_zero
  have hF := multiset_prod_ne_zero N hN0
  have hAc : RowCaps (C N.prod * L) s := hL ▸ a.row_caps
  have hBc : RowCaps (C N.prod * T) t := hT ▸ b'.row_caps
  obtain ⟨hx, hz, hcL⟩ := gcd_caps hF hproper.left_ne hAc
  obtain ⟨hx', hz', hcT⟩ := gcd_caps hF hproper.right_ne hBc
  obtain ⟨S, hgeom, hS, hcover⟩ :=
    proper_cover hproper (min_le_right _ _) (min_le_right _ _) hcL hcT
  have hs1 : ordinarySeedDegree (1 : Equation) = 0 := by
    rw [← K1_14_2_2_2_1.seedDegree_C]
    simpa only [C_1, MvPolynomial.totalDegree_one] using K1_14_2_2_2_1.seedDegree_seed (1 : Seeds)
  have hseed : (∑ f ∈ N.toFinset, ordinarySeedDegree f) ≤ x :=
    distinct_le_degree ordinarySeedDegree hs1 (fun hf hg => seed_degree_mul hf hg) N hN0
  have hy : (∑ f ∈ N.toFinset, f.natDegree) ≤ z :=
    distinct_le_degree natDegree natDegree_one (fun hf hg => natDegree_mul hf hg) N hN0
  obtain ⟨U, hUgeom, hU, hUcover⟩ := collect N.toFinset
    (fun f => ordinaryBudget (ordinarySeedDegree f) f.natDegree) (fun f z R => atMark f z R = 0)
    (fun f hf => ordinary_component_cover f (hN f (Multiset.mem_toFinset.mp hf)).1
      (hN f (Multiset.mem_toFinset.mp hf)).2
      (((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans hy).trans_lt
        (hz.trans_lt gs.ode.small)))
  refine ⟨{
    components := S ∪ U
    geometry := ?_
    fits := ?_
    content := a.content * b'.content
    content_ne := mul_ne_zero a.content_ne b'.content_ne
    content_le := (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add a.content_le b'.content_le)
    covers := ?_ }⟩
  · intro I hI
    exact (Finset.mem_union.mp hI).elim (hgeom I) (hUgeom I)
  · intro k
    exact (sum_union_le (fun I => sectionDegree I k) _ _).trans
      ((Nat.add_le_add (hS k) ((hU k).trans (ordinary_sum _ _ _ hseed hy k))).trans
        (zero_ledger empty k (le_min hx hx') (le_min hz hz') gs.ode.jb gt.ode.jb))
  · intro γ hγ
    obtain ⟨hp, hq⟩ := hrows γ hγ
    rcases a.covers _ _ hp with h | h | ha
    · exact Or.inl (by rw [map_mul, h, zero_mul])
    · exact Or.inr (Or.inl h)
    rcases b'.covers _ _ hq with h | h | hb
    · exact Or.inl (by rw [map_mul, h, mul_zero])
    · exact Or.inr (Or.inr (Or.inl h))
    apply Or.inr ∘ Or.inr ∘ Or.inr
    by_cases hzero : atMark N.prod (M.label γ) (F.scalar γ) = 0
    · obtain ⟨f, hf, hmark⟩ := atMark_prod_eq_zero hzero
      obtain ⟨I, hI, hon⟩ := hUcover f (Multiset.mem_toFinset.mpr hf) _ _ hmark
      exact ⟨I, Finset.mem_union_right _ hI, hon⟩
    · rw [hL, jetAt_mul, jetAt_ordinary, mul_eq_zero] at ha
      rw [hT, jetAt_mul, jetAt_ordinary, mul_eq_zero] at hb
      obtain ⟨I, hI, hon⟩ := hcover _ _ (ha.resolve_left hzero) (hb.resolve_left hzero)
      exact ⟨I, Finset.mem_union_left _ hI, hon⟩
end
end HighCore82219_3_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1400000
namespace HighCore82219_3_1
noncomputable section
open HighCore82219 (AnchorModel AnchoredFamily)
open HighCore82219_3 (stageAt introIndices initialCap ScheduleOK introAccount introJump introWeight degreeVector)
open P1_7_4_1 (SectionGeometry IntroFactors factorDegree factorMass factorMass_mono
  factorTariff weightedDegree tariff_step ordinary_charge residual_tariff collect proper_cover
  own_J_le_B own_caps retained_mass Stripped initial_factors)
open K1_14 (Jet jetAt seedHasse)
open K1_14_2 (Ambient OnJet)
open K1_14_2_2 (RowCaps FixedPart mass sectionDegree sum_union_le)
open K1_14_2_2_2 (ordinaryBudget)
open K1_14_3 (NoMovingCommon)
open scoped BigOperators Classical
open private irreducible_cut terminal_piece from ProximityPrize.SubmissionLower.UpperBranch4
private theorem intro_components {b : HighCore82219.Band} (sched : ScheduleOK b)
    {P Q : Jet} (hQ : Q ≠ 0) (hnc : NoMovingCommon P Q)
    (hQc : RowCaps Q (stageAt b 0).moving.shape) (later : ℕ → Jet)
    (rows : ∀ i ∈ introIndices b, later i ≠ 0 ∧ RowCaps (later i) (stageAt b i).free.shape) :
    ∀ (is : List ℕ), (∀ i ∈ is, i ∈ introIndices b) →
    ∀ (D : Finset Jet) (cap : Fin 3 → ℕ), IntroFactors P D → (∀ j, factorMass D j ≤ cap j) →
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧
      (∀ k old, mass S k ≤ introAccount b k is cap old + weightedDegree old D) ∧
      ∀ z R, (∀ i ∈ is, ∀ j a, a ≤ (stageAt b i).reserve →
        jetAt (seedHasse j a (later i)) z R = 0) →
        jetAt Q z R = 0 → (∃ f ∈ D, jetAt f z R = 0) → ∃ I ∈ S, OnJet I z R := by
  classical
  intro is
  induction is with
  | nil =>
    intro _ D cap hD hcap
    let t := (stageAt b 0).moving.shape
    have gt := (sched.stage_guard 0 sched.stages_pos).2
    obtain ⟨S, hG, hS, hC⟩ := collect D
      (fun f k => factorTariff t k f + ordinaryBudget (factorDegree f 2) (factorDegree f 0) k)
      (fun f z R => jetAt f z R = 0 ∧ jetAt Q z R = 0)
      (terminal_piece hD hnc hQc gt.ode.jb gt.ode.small hQ)
    refine ⟨S, hG, ?_, ?_⟩
    · intro k old
      have hord : (![cap 0, cap 2, 2*cap 0*cap 2, cap 2*cap 2] : Fin 4 → ℕ) k =
          ordinaryBudget (cap 2) (cap 0) k := by
        fin_cases k <;> try rfl
        change 2*cap 0*cap 2 = 2*cap 2*cap 0
        ring
      have hstep := tariff_step (Finset.empty_subset D) cap old t k hcap
      simp only [Finset.sdiff_empty, weightedDegree, factorMass, Finset.sum_empty,
        mul_zero, Finset.sum_const_zero, Nat.add_zero] at hstep
      have hsum := Nat.add_le_add hstep (ordinary_charge D cap hcap k)
      calc
        _ ≤ ∑ f ∈ D, (factorTariff t k f +
            ordinaryBudget (factorDegree f 2) (factorDegree f 0) k) := hS k
        _ ≤ (weightedDegree old D + introJump cap old t k) +
            ordinaryBudget (cap 2) (cap 0) k := by
          rw [Finset.sum_add_distrib]
          exact hsum
        _ = _ := by
          simp only [introAccount, hord]
          ac_rfl
    · intro z R _ hq ⟨f, hf, hz⟩
      exact hC f hf z R ⟨hz, hq⟩
  | cons i is ih =>
    intro his D cap hD hcap
    have hi := his i (List.mem_cons_self ..)
    have hrest : ∀ l ∈ is, l ∈ introIndices b := fun l hl => his l (List.mem_cons_of_mem _ hl)
    let s := (stageAt b i).free.shape
    let r := (stageAt b i).reserve
    let T := D.filter fun f => ∀ j a, a ≤ r → f ∣ seedHasse j a (later i)
    have hT : T ⊆ D := Finset.filter_subset _ _
    have gt := (sched.stage_guard i (sched.intro_pos i hi).2).1
    obtain ⟨hrow, hc⟩ := rows i hi
    have hTcap (j : Fin 3) :
        factorMass T j ≤ min (cap j) (degreeVector s j / (r+1)) :=
      le_min ((factorMass_mono hT j).trans (hcap j))
        (retained_mass (hD.mono hT) hrow hc gt.seed_small r
          (fun f hf => (Finset.mem_filter.mp hf).2) j)
    obtain ⟨laterCover, hLaterGeom, hLaterCap, hLater⟩ :=
      ih hrest T _ (hD.mono hT) hTcap
    obtain ⟨discard, hDiscardGeom, hDiscardCap, hDiscard⟩ :=
      collect (D \ T) (fun f k => factorTariff s k f)
        (fun f z R => jetAt f z R = 0 ∧
          ∀ j a, a ≤ r → jetAt (seedHasse j a (later i)) z R = 0) (by
        intro f hf
        obtain ⟨hfD, hfT⟩ := Finset.mem_sdiff.mp hf
        have hn : ¬ ∀ j a, a ≤ r → f ∣ seedHasse j a (later i) :=
          fun hall => hfT (Finset.mem_filter.mpr ⟨hfD, hall⟩)
        push Not at hn
        obtain ⟨j, a, ha, hd⟩ := hn
        have hirr := (hD.factors f hfD).1
        obtain ⟨S, hG, hF, hC⟩ := proper_cover (irreducible_cut hirr hd)
          (own_J_le_B hirr.ne_zero) gt.ode.jb (own_caps f) (P1_7_4_1_2.proof s (later i) hc j a)
        exact ⟨S, hG, fun k => (hF k).trans_eq (residual_tariff f s gt.ode.jb k),
          fun z R hr => hC z R hr.1 (hr.2 j a ha)⟩)
    refine ⟨discard ∪ laterCover, ?_, ?_, ?_⟩
    · intro I hI
      exact (Finset.mem_union.mp hI).elim (hDiscardGeom I) (hLaterGeom I)
    · intro k old
      let w := fun j => max (old j) (introWeight s k j)
      let newCap := fun j => min (cap j) (degreeVector s j / (r+1))
      have hstep := tariff_step hT cap old s k hcap
      calc
        _ ≤ mass discard k + mass laterCover k := sum_union_le (fun I => sectionDegree I k) _ _
        _ ≤ (∑ f ∈ D \ T, factorTariff s k f) +
            (introAccount b k is newCap w + weightedDegree w T) :=
          Nat.add_le_add (hDiscardCap k) (hLaterCap k w)
        _ = introAccount b k is newCap w +
            ((∑ f ∈ D \ T, factorTariff s k f) + weightedDegree w T) := by ac_rfl
        _ ≤ introAccount b k is newCap w + (weightedDegree old D + introJump cap old s k) :=
          Nat.add_le_add_left hstep _
        _ = _ := by
          change _ = (introJump cap old s k + introAccount b k is newCap w) + weightedDegree old D
          ac_rfl
    · intro z R hder hq ⟨f, hf, hz⟩
      by_cases h : f ∈ T
      · obtain ⟨I, hI, hMark⟩ := hLater z R
          (fun l hl => hder l (List.mem_cons_of_mem _ hl)) hq ⟨f, h, hz⟩
        exact ⟨I, Finset.mem_union_right _ hI, hMark⟩
      · obtain ⟨I, hI, hMark⟩ := hDiscard f (Finset.mem_sdiff.mpr ⟨hf, h⟩) z R
          ⟨hz, hder i (List.mem_cons_self ..)⟩
        exact ⟨I, Finset.mem_union_left _ hI, hMark⟩
theorem intro_cover {b : HighCore82219.Band} (sched : ScheduleOK b)
    (hne : ¬ (introIndices b).isEmpty = true)
    {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {P Q : Jet} (hQ : Q ≠ 0) (hnc : NoMovingCommon P Q)
    (hQc : RowCaps Q (stageAt b 0).moving.shape)
    {A : FixedPart P (stageAt b 0).free.shape} {B : FixedPart Q (stageAt b 0).moving.shape}
    (a : Stripped A)
    (hrows : ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 ∧
      jetAt Q (M.label γ) (F.scalar γ) = 0)
    (later : ℕ → Jet)
    (hlater : ∀ i ∈ introIndices b, later i ≠ 0 ∧ RowCaps (later i) (stageAt b i).free.shape ∧
      ∀ j r, r ≤ (stageAt b i).reserve →
        ∀ γ ∈ Γ, jetAt (seedHasse j r (later i)) (M.label γ) (F.scalar γ) = 0) :
    Nonempty (AffineCover F b A.equation B.equation) := by
  obtain ⟨D, hD, hcap, hroot⟩ := initial_factors a
  obtain ⟨S, hG, hFit, hC⟩ := intro_components sched hQ hnc hQc later
    (fun i hi => ⟨(hlater i hi).1, (hlater i hi).2.1⟩)
    (introIndices b) (fun _ hi => hi) D _ hD hcap
  refine ⟨{
    components := S
    geometry := hG
    fits := fun k => ?_
    content := a.content
    content_ne := a.content_ne
    content_le := a.content_le.trans (Nat.le_add_right _ _)
    covers := ?_ }⟩
  · rw [initialCap, ite_eq_right hne]
    simpa only [weightedDegree, zero_mul, Finset.sum_const_zero, Nat.add_zero] using hFit k (fun _ => 0)
  · intro γ hγ
    obtain ⟨hp, hq⟩ := hrows γ hγ
    rcases a.covers _ _ hp with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (hC _ _
        (fun i hi j r hr => (hlater i hi).2.2 j r hr γ hγ) hq (hroot _ _ h))))
end
end HighCore82219_3_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
namespace HighCore82219_3_1
noncomputable section
open HighCore82219 (K p AnchorModel AnchoredFamily)
open HighCore82219_3 (introIndices initialCap initialE ScheduleOK InitialCover OnParent)
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open K1_14_3 (SeedCover joinCovers joinCovers_degree joinCovers_points joinCovers_covers)
open scoped BigOperators Classical
open P1_7_4_1 (strip)
open private seed_projection from ProximityPrize.SubmissionLower.PortHighFinish
private theorem finish {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {b : HighCore82219.Band} {G H : ODE} (sched : ScheduleOK b) (C : AffineCover F b G H) :
    Nonempty (InitialCover M F b G H) := by
  classical
  let S := C.components
  let noSeeds := S.filter (fun I => sectionDegree I 0 = 0)
  let constY := S.filter (fun I => 0 < sectionDegree I 0 ∧
    ¬ Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl))
  let parents := S.filter (fun I => 0 < sectionDegree I 0 ∧
    Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl))
  have hparents (I : Ideal Ambient) (hi : I ∈ parents) : Active I := by
    obtain ⟨hI, ha, hy⟩ := Finset.mem_filter.mp hi
    obtain ⟨hprime, hdim, _, hf⟩ := C.geometry I hI
    have hsmall (k : Fin 4) : sectionDegree I k < p :=
      (length_le_mass hI k).trans_lt ((C.fits k).trans_lt (sched.initial_small k))
    exact ⟨hprime, hdim, hf.seeds, hf.ordinate, hf.mixed, hf.jets,
      ⟨ha, hsmall 0⟩, hsmall 2, hsmall 3, hy⟩
  have seed_exists (I : Ideal Ambient) (hi : I ∈ noSeeds) :
      ∃ D : SeedCover, D.curve.totalDegree ≤ sectionDegree I 2 ∧
        D.points.card ≤ sectionDegree I 3 ∧ ∀ z R, OnJet I z R → D.Covers z := by
    obtain ⟨hI, hz⟩ := Finset.mem_filter.mp hi
    obtain ⟨hprime, hdim, _, hf⟩ := C.geometry I hI
    exact seed_projection I hprime hdim hf hz
  let seedImage (I : Ideal Ambient) : SeedCover :=
    if hi : I ∈ noSeeds then Classical.choose (seed_exists I hi) else ⟨1, one_ne_zero, ∅⟩
  have hseedImage (I : Ideal Ambient) (hi : I ∈ noSeeds) :
      (seedImage I).curve.totalDegree ≤ sectionDegree I 2 ∧
      (seedImage I).points.card ≤ sectionDegree I 3 ∧
      ∀ z R, OnJet I z R → (seedImage I).Covers z := by
    simpa only [seedImage, dite_eq_left hi] using Classical.choose_spec (seed_exists I hi)
  let imageCover := joinCovers noSeeds seedImage
  let onY (I : Ideal Ambient) := (Γ.filter (OnParent F I)).image (fun γ => atX (F.scalar γ))
  let ordinates := constY.biUnion onY
  have hy (I : Ideal Ambient) (hi : I ∈ constY) : (onY I).card ≤ sectionDegree I 0 := by
    obtain ⟨hI, ha, hy⟩ := Finset.mem_filter.mp hi
    apply le_trans (b := 1) _ ha
    apply Finset.card_le_one.mpr
    intro x hx y hy'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hy'
    exact ordinate_eq (C.geometry I hI).1 hy
      (Finset.mem_filter.mp hγ).2 (Finset.mem_filter.mp hδ).2
  refine ⟨{
    parents := parents
    active := hparents
    height_two := fun I hi => (C.geometry I (Finset.mem_filter.mp hi).1).2.2.1
    mass_bound := fits_mono (Finset.filter_subset _ _) C.fits
    seed := imageCover
    seed_le := ?_
    seed_points := ?_
    ordinates := ordinates
    ordinate_le := ?_
    content := C.content
    content_ne := C.content_ne
    content_le := C.content_le
    covers := ?_ }⟩
  · calc
      _ ≤ ∑ I ∈ noSeeds, (seedImage I).curve.totalDegree := joinCovers_degree _ _
      _ ≤ mass noSeeds 2 := Finset.sum_le_sum fun I hi => (hseedImage I hi).1
      _ ≤ mass S 2 := mass_mono (Finset.filter_subset _ _) 2
      _ ≤ _ := C.fits 2
  · calc
      _ ≤ ∑ I ∈ noSeeds, (seedImage I).points.card := joinCovers_points _ _
      _ ≤ mass noSeeds 3 := Finset.sum_le_sum fun I hi => (hseedImage I hi).2.1
      _ ≤ mass S 3 := mass_mono (Finset.filter_subset _ _) 3
      _ ≤ initialCap b 3 := C.fits 3
      _ ≤ _ := sched.initial_e_ge
  · calc
      _ ≤ ∑ I ∈ constY, (onY I).card := Finset.card_biUnion_le
      _ ≤ mass constY 0 := Finset.sum_le_sum hy
      _ ≤ mass S 0 := mass_mono (Finset.filter_subset _ _) 0
      _ ≤ _ := C.fits 0
  · intro γ hγ
    rcases C.covers γ hγ with h | h | h | ⟨I, hI, hon⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · by_cases ha : sectionDegree I 0 = 0
      · have hmem : I ∈ noSeeds := Finset.mem_filter.mpr ⟨hI, ha⟩
        exact Or.inl (joinCovers_covers hmem ((hseedImage I hmem).2.2 _ _ hon))
      · have hpos := Nat.pos_of_ne_zero ha
        by_cases hy : Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨I, Finset.mem_filter.mpr ⟨hI, hpos, hy⟩, hon⟩))))
        · exact Or.inr (Or.inl (Finset.mem_biUnion.mpr
            ⟨I, Finset.mem_filter.mpr ⟨hI, hpos, hy⟩,
              Finset.mem_image.mpr ⟨γ, Finset.mem_filter.mpr ⟨hγ, hon⟩, rfl⟩⟩))
theorem proof : HighCore82219_3.c1 := by
  intro b u del M Γ F sched P Q hP hQ hnc hPc hQc A B hrows later hlater
  obtain ⟨a⟩ := strip hP hPc A
  by_cases hempty : (introIndices b).isEmpty = true
  · obtain ⟨tail⟩ := strip hQ hQc B
    obtain ⟨C⟩ := zero_cover sched hempty F hnc a tail hrows
    exact finish sched C
  · obtain ⟨C⟩ := intro_cover (B := B) sched hempty F hQ hnc hQc a hrows later hlater
    exact finish sched C
end
end HighCore82219_3_1
end
section
namespace HighCore82219_3_2
noncomputable section
open Polynomial Finset
open HighCore82219 (K agreement blockLength p)
open HighCore82219 (FixedWord degreeAt persistent_card_le section_incidence)
open HighCore82219_3 (fixedFee)
open P1_7_3 (persistentNodes hits_persistent)
open P1_7_4_3 (mix cast_mixed short_cut)
open K1_13 (Row extend)
open K1_13_5 (RegularAt)
open K1_14_3_6 (power totalCap topCap)
open private weights rho_at_endpoint from ProximityPrize.SubmissionLower.HighCore82219Family
open HighCore82219PrefixHelpers (section_bound fixed_bound)
private theorem word_subset {w T s d} (hw : FixedWord w T s d) {U : Finset K}
    (hU : U ⊆ T) : FixedWord w U s d :=
  ⟨hw.distinct.mono hU, fun γ hγ => hw.degree γ (hU hγ), fun γ hγ => hw.hits γ (hU hγ)⟩
private def siteRatio (m : ℕ) : ℚ :=
  ((blockLength - m : ℕ) : ℚ) / ((agreement - m : ℕ) : ℚ)
private abbrev density : ℚ := (blockLength : ℚ) / agreement
private def persistentTotal (d B : ℕ) : ℚ := siteRatio d + 2 * density * d * (B-1 : ℕ)
private def persistentTop (d B J : ℕ) : ℚ :=
  min (persistentTotal d B) (density * d * (2*J-1 : ℕ))
private theorem persistentTotal_nonneg (d B : ℕ) : 0 ≤ persistentTotal d B := by
  unfold persistentTotal siteRatio
  positivity
private theorem caps_weighted {d m B J : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 164436)
    (hm : m ≤ d) (hJ : 0 < J) :
    let t := max 1 (d-m)
    siteRatio m * totalCap t B ≤ persistentTotal d B ∧
      siteRatio m * topCap t B J ≤ persistentTop d B J := by
  let t := max 1 (d-m)
  have hd : d < agreement := hh.trans_lt (by decide)
  obtain ⟨hMu, hLambda⟩ := weights hm hd (rho_at_endpoint hl hh)
  change siteRatio m ≤ siteRatio d at hMu
  change siteRatio m * t ≤ density * d at hLambda
  have hRatio : 0 ≤ siteRatio m := by unfold siteRatio; positivity
  have hp : (power t : ℚ) ≤ 2 * (t : ℚ) := by
    exact_mod_cast (Nat.sub_le (2 * t) 3)
  have hpow : siteRatio m * power t ≤ 2 * (density * d) := by
    have h := mul_le_mul_of_nonneg_left hp hRatio
    linarith only [h,hLambda]
  have htot : siteRatio m * totalCap t B ≤ persistentTotal d B := by
    unfold totalCap persistentTotal
    push_cast
    rw [mul_add, mul_one, ← mul_assoc, show 2 * density * (d : ℚ) = 2 * (density * d) from
      mul_assoc _ _ _]
    exact add_le_add hMu (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  refine ⟨htot, ?_⟩
  unfold persistentTop
  apply le_min
  · exact (mul_le_mul_of_nonneg_left (by exact_mod_cast
      (show topCap t B J ≤ totalCap t B from min_le_left _ _)) hRatio).trans htot
  · have hcap : topCap t B J ≤ t * (2*J-1) := by
      apply (min_le_right _ _).trans
      rw [show 2*J-1 = 2*(J-1)+1 by omega, Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right ((Nat.mul_le_mul_right _ (Nat.sub_le (2*t) 3)).trans_eq (by ring)) _
    calc
      _ ≤ siteRatio m * ((t * (2*J-1) : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcap) hRatio
      _ = (siteRatio m * t) * (2*J-1 : ℕ) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hLambda (Nat.cast_nonneg _)
private theorem persistent_regular {w T s d B J} (hw : FixedWord w T s d)
    (hl : 131071 ≤ d) (hh : d ≤ 164436) (hJ : 0 < J)
    (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hb : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) :
    (T.card : ℚ) ≤
      mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) + 1 := by
  have hpos : 0 ≤ mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) := by
    have ha : 0 ≤ persistentTotal d B := persistentTotal_nonneg d B
    have hv : 0 ≤ persistentTop d B J := le_min ha (by positivity)
    unfold mix
    positivity
  by_cases hsmall : T.card ≤ 1
  · exact (show (T.card : ℚ) ≤ 1 from by exact_mod_cast hsmall).trans (by linarith only [hpos])
  let sites := persistentNodes w T s
  let t := max 1 (d-sites.card)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : t ≤ d := max_le (by omega) (Nat.sub_le _ _)
  have htpos : 0 < t := (Nat.le_max_left _ _)
  have hsum : d ≤ sites.card + t := by
    have h := Nat.le_max_right 1 (d-sites.card)
    omega
  have hd : d < agreement := hh.trans_lt (by decide)
  have hdp := hd.trans (by decide : agreement < p)
  have ha : 0 < totalCap t B := by simp [totalCap]
  have hv : 0 < topCap t B J := lt_min ha ((Nat.le_add_left _ _).trans' htpos)
  let D := MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) (totalCap t B) (topCap t B J)
  have hcount := section_incidence hw D (fun i hi => by
    obtain ⟨cut, hc, he⟩ := short_cut f hdp ht hJ hb hj sites hsum w i
    exact section_bound hw f hf hfpos hreg ha hv i hi cut hc
      (fun γ hγ => he _ (hw.degree γ hγ) (hreg γ hγ) (fun _ hj => hits_persistent hγ hj)))
  have hgap : (0 : ℚ) < ((agreement-sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hratio : (T.card : ℚ) ≤ siteRatio sites.card * D := by
    unfold siteRatio
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hgap).mpr
    rw [mul_comm (T.card : ℚ)]
    exact_mod_cast hcount
  have hvle : topCap t B J ≤ totalCap t B := min_le_left _ _
  dsimp only [D] at hratio
  rw [cast_mixed (f.degreeOf_le_totalDegree 1) hvle] at hratio
  obtain ⟨hcapA, hcapV⟩ := caps_weighted (B := B) hl hh hs hJ
  refine hratio.trans ?_
  unfold mix
  calc
    _ = (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * (siteRatio sites.card * topCap t B J) +
        f.degreeOf 1 * (siteRatio sites.card * totalCap t B) := by ring
    _ ≤ (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * persistentTop d B J +
        f.degreeOf 1 * persistentTotal d B :=
      add_le_add (mul_le_mul_of_nonneg_left hcapV (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hcapA (Nat.cast_nonneg _))
    _ ≤ _ := le_add_of_nonneg_right (by decide)
theorem proof : HighCore82219_3.c2 := by
  classical
  intro b u del M Γ F hband B J guard G hG T hT hroot
  let d := degreeAt (finish b)
  have hdl : 131071 ≤ d := Nat.le_add_right _ _
  have hdu : d ≤ 164436 := Nat.add_le_add_left (HighCore82219.terminal_guards b).2.1 131071
  have hw : FixedWord M.word T F.scalar d := by
    refine ⟨F.distinct.mono hT, ?_, ?_⟩
    · intro γ hγ
      have hhi : M.overhead.toNat ≤ (finish b) := by
        simpa using Int.toNat_le_toNat hband.2
      exact (HighCore82219.degree_at_height M F γ (hT hγ)).trans (Nat.add_le_add_left hhi _)
    · intro γ hγ
      let mark := F.mark γ (hT hγ)
      exact ⟨mark.bad.support, mark.bad.agreement, mark.scalar_hits⟩
  let ap := persistentTotal d B
  let vp := persistentTop d B J
  have ha : 0 ≤ ap := persistentTotal_nonneg d B
  have hvp : 0 ≤ vp := le_min ha (by positivity)
  have h := fixed_bound hw guard G hG hroot ap vp hvp (min_le_left _ _)
    (fun U hU => persistent_regular (word_subset hw hU) hdl hdu guard.jpos)
  let r := mix B J ap vp
  have hceil : r ≤ (r.ceil.toNat : ℕ) := by
    have hz : r.ceil ≤ (r.ceil.toNat : ℤ) := Int.self_le_toNat _
    have hcast : (r.ceil : ℚ) ≤ (r.ceil.toNat : ℚ) := by exact_mod_cast hz
    exact Rat.le_ceil.trans hcast
  change T.card ≤ r.ceil.toNat + B^2
  have hfinal : (T.card : ℚ) ≤ (r.ceil.toNat : ℚ) + (B^2 : ℕ) :=
    h.trans (add_le_add hceil le_rfl)
  exact_mod_cast hfinal
end
end HighCore82219_3_2
end
