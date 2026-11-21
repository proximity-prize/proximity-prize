import ProximityPrize.SubmissionLower.Rect52PrefixScheduleData

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

set_option Elab.async false
set_option autoImplicit true
open Rect52Prefix (start finish prefixFee retainedCap)
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

section
namespace Rect52Prefix_3
noncomputable section
open Polynomial
open Rect52Prefix (Band K p agreement blockLength AnchorModel AnchoredFamily)
open Rect52Prefix (Stage stages terminal fullCutoff degreeAt gap fees curveUnit)
open K1_14 (Shape Jet Seeds FX Banks atX jetAt seedHasse graphEval)
open K1_14_2 (Ambient ODE OnJet)
open K1_14_2_2 (Active Fits FixedPart ODECaps fixedOn mass sectionDegree weight dot)
open K1_14_2_2_4 (pairCap residualShape highCap highScale)
open scoped BigOperators Classical
def OnParent {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (I : Ideal Ambient) (γ : K) : Prop := OnJet I (M.label γ) (F.scalar γ)
def BankPass (rows : Banks) (s : Shape) (I : Ideal Ambient) : Prop :=
  ∀ P ∈ rows s (fullCutoff s), K1_14_2.toJet P ∈ I
def PairPass {h rows s} (pair : Rect52Prefix.BufferedPair h rows s) (I : Ideal Ambient) : Prop :=
  BankPass rows s.free.shape I ∧ BankPass rows s.moving.shape I ∧
    K1_14_2_2R.chainCompatible pair.free pair.moving I
noncomputable section
open K1_14_2_2 (CutCover CurveGeometry RowCaps joinCuts joinCuts_cost sum_dot emptyCut)
open K1_14_2_2_3
open K1_14_2_2_7
open K1_14 (seedEmbedding)
open K1_14_2 (SeedField RootSeedSection jetMarkHom CoordinateRing)
open K1_14_2_3 (SeedSlice seedImage rootImage constantCoefficients DefinedOverConstants seedLength yLength)
open K1_14_2 (toJet)
open private seed_value_eq from ProximityPrize.SubmissionLower.Fast052
open private on_seed seed_graph_count from ProximityPrize.SubmissionLower.Fast062
theorem fixed_zero {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {I : Ideal Ambient} {G : ODE} {γ : K} (hm : OnParent F I γ) (hG : fixedOn G I) :
    K1_14_2.fixedAt G (F.scalar γ) = 0 := by
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (hm hG)
theorem proper_cut {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (s : Shape) {I : Ideal Ambient} {P : Jet} (hs : s.J ≤ s.B) (hI : Active I)
    (hcaps : RowCaps P s) (hprop : toJet P ∉ I) :
    ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight s fee) (sectionDegree I)) ∧
      ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0 →
        γ ∈ C.direct ∨ ∃ Q ∈ C.curves, OnParent F Q γ := by
  let marked (Q : Ideal Ambient) := Γ.filter (OnParent F Q)
  let direct := (constantComponents I P).biUnion marked
  have hcard : direct.card ≤ (constantComponents I P).card := by
    have hsingle (Q : Ideal Ambient) (hQ : Q ∈ constantComponents I P) :
        (marked Q).card ≤ 1 := by
      obtain ⟨hcomp, hconst⟩ := Finset.mem_filter.mp hQ
      let _ : Q.IsPrime := (cutComponent_curve hI hprop hcomp).1
      apply Finset.card_le_one.mpr
      intro γ hγ δ hδ
      apply sub_left_inj.mp
      apply seedEmbedding.injective
      apply (algebraMap K1_14.FX (CoordinateRing Q)).injective
      exact (seed_value_eq hconst (Finset.mem_filter.mp hγ).2).trans
        (seed_value_eq hconst (Finset.mem_filter.mp hδ).2).symm
    calc
      _ ≤ ∑ Q ∈ constantComponents I P, (marked Q).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ constantComponents I P, 1 := Finset.sum_le_sum hsingle
      _ = _ := by simp
  let C : CutCover :=
    ⟨direct, movingComponents I P, by
      intro Q hQ
      obtain ⟨hcomp, hmov⟩ := Finset.mem_filter.mp hQ
      obtain ⟨hp, hdim⟩ := cutComponent_curve hI hprop hcomp
      exact ⟨hp, hdim, K1_14_2_2_7_1.proof Q hp hdim hmov⟩⟩
  refine ⟨C, ?_, ?_⟩
  · intro fee
    fin_cases fee
    · exact P0_10R.Bridge.cut_seed_mass s I P hs hI hcaps hprop
    · exact P0_10R.Bridge.cut_ordinate_mass s I P hs hI hcaps hprop
    · exact hcard.trans (P0_10R.Bridge.cut_constant_count s I P hs hI hcaps hprop)
  · intro γ hγ hmark hzero
    let ev := K1_14_2.jetMarkHom (M.label γ) (F.scalar γ)
    change I ≤ RingHom.ker ev at hmark
    have hle : I ⊔ Ideal.span {toJet P} ≤ RingHom.ker ev := by
      apply sup_le hmark
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      exact RingHom.mem_ker.mpr ((K1_14_2.eval_toJet (M.label γ) (F.scalar γ) P).trans hzero)
    have : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
    obtain ⟨Q, hminimal, hQmark⟩ := Ideal.exists_minimalPrimes_le hle
    have hQ : Q ∈ cutComponents I P := Ideal.mem_minimalPrimesFinset.mpr hminimal
    have hmarked : OnParent F Q γ := by
      change Q ≤ RingHom.ker ev
      exact hQmark
    by_cases ht : ConstantSeed Q
    · exact Or.inl (Finset.mem_biUnion.mpr
        ⟨Q, Finset.mem_filter.mpr ⟨hQ, ht⟩, Finset.mem_filter.mpr ⟨hγ, hmarked⟩⟩)
    · exact Or.inr ⟨Q, Finset.mem_filter.mpr ⟨hQ, ht⟩, hmarked⟩
theorem combined_cuts {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    (A : Finset (Ideal Ambient)) (s : Shape) (hs : s.J ≤ s.B)
    (ha : ∀ I ∈ A, Active I)
    (hcut : ∀ I ∈ A, ∃ P : Jet, RowCaps P s ∧ toJet P ∉ I ∧
      ∀ γ ∈ Γ, OnParent F I γ → jetAt P (M.label γ) (F.scalar γ) = 0) :
    ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight s fee) (mass A)) ∧
      ∀ γ ∈ Γ, (∃ I ∈ A, OnParent F I γ) → γ ∈ C.direct ∨ ∃ I ∈ C.curves, OnParent F I γ := by
  have hex (I : Ideal Ambient) (hI : I ∈ A) :
      ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight s fee) (sectionDegree I)) ∧
        ∀ γ ∈ Γ, OnParent F I γ → γ ∈ C.direct ∨ ∃ Q ∈ C.curves, OnParent F Q γ := by
    obtain ⟨P, hp, hprop, hzero⟩ := hcut I hI
    obtain ⟨C, hc, hmarks⟩ := proper_cut F s hs (ha I hI) hp hprop
    exact ⟨C, hc, fun γ hγ hm => hmarks γ hγ hm (hzero γ hγ hm)⟩
  let C (I : Ideal Ambient) : CutCover :=
    if hI : I ∈ A then Classical.choose (hex I hI) else emptyCut
  have hC (I : Ideal Ambient) (hI : I ∈ A) :
      (∀ fee, (C I).cost fee ≤ dot (weight s fee) (sectionDegree I)) ∧
      ∀ γ ∈ Γ, OnParent F I γ → γ ∈ (C I).direct ∨ ∃ Q ∈ (C I).curves, OnParent F Q γ := by
    simpa only [C, dite_eq_left hI] using Classical.choose_spec (hex I hI)
  refine ⟨joinCuts A C, ?_, ?_⟩
  · intro fee
    calc
      _ ≤ ∑ I ∈ A, (C I).cost fee := joinCuts_cost A C fee
      _ ≤ ∑ I ∈ A, dot (weight s fee) (sectionDegree I) :=
        Finset.sum_le_sum (fun I hI => (hC I hI).1 fee)
      _ = _ := sum_dot _ _
  · rintro γ hγ ⟨I, hI, hmark⟩
    rcases (hC I hI).2 γ hγ hmark with hd | ⟨Q, hQ, hmark⟩
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨I, hI, hd⟩)
    · exact Or.inr ⟨Q, Finset.mem_biUnion.mpr ⟨I, hI, hQ⟩, hmark⟩
def curveMarks {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ) (C : CutCover) :
    Finset K := C.curves.biUnion fun I => Γ.filter (OnParent F I)
theorem mem_curveMarks {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {C : CutCover} {γ : K} (hγ : γ ∈ Γ) {I : Ideal Ambient} (hI : I ∈ C.curves)
    (hm : OnParent F I γ) : γ ∈ curveMarks F C :=
  Finset.mem_biUnion.mpr ⟨I, hI, Finset.mem_filter.mpr ⟨hγ, hm⟩⟩
private theorem prefix_seed_slice {I : Ideal Ambient} (h : CurveGeometry I) : SeedSlice I :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
private theorem prefix_mark_graph {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : seedImage I = Ideal.span {C}) :
    ∀ z ∈ (Γ.filter (OnParent F I)).image M.label, graphEval z C = 0 := by
  intro z hz
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
  apply on_seed (Finset.mem_filter.mp hγ).2
  rw [hC]
  exact Ideal.mem_span_singleton_self C
private theorem prefix_translated_card {u del} (M : AnchorModel u del) (T : Finset K) :
    (T.image M.label).card = T.card :=
  Finset.card_image_of_injective _ (fun _ _ hab => sub_left_inj.mp hab)
private theorem prefix_direct_count {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : C ≠ 0) (hI : seedImage I = Ideal.span {C})
    (hp : C.totalDegree < p) :
    (Γ.filter (OnParent F I)).card ≤ (p+1)*C.totalDegree := by
  have h := seed_graph_count C hC hp ((Γ.filter (OnParent F I)).image M.label) (prefix_mark_graph F hI)
  rwa [prefix_translated_card] at h
theorem direct_curve_count {u del} {M : AnchorModel u del} {Γ}
    (F : AnchoredFamily M Γ) (C : CutCover) (hp : C.cost 0 < p) :
    ((curveMarks F C).card : ℚ) ≤ ((p+1 : ℕ) : ℚ)*(C.cost 0 : ℚ) := by
  have hsum : ∑ I ∈ C.curves, seedLength I = C.cost 0 := rfl
  have hcount (I : Ideal Ambient) (hI : I ∈ C.curves) :
      (Γ.filter (OnParent F I)).card ≤ (p+1)*seedLength I := by
    obtain ⟨f, hf, he, _, hd⟩ := K1_14_2_3_1.proof I (prefix_seed_slice (C.geometric I hI))
    have hle : seedLength I ≤ C.cost 0 := hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hI
    exact (prefix_direct_count F hf.ne_zero he ((hd.trans hle).trans_lt hp)).trans
      (Nat.mul_le_mul_left _ hd)
  have h : (curveMarks F C).card ≤ (p+1)*C.cost 0 := calc
    _ ≤ ∑ I ∈ C.curves, (Γ.filter (OnParent F I)).card := Finset.card_biUnion_le
    _ ≤ ∑ I ∈ C.curves, (p+1)*seedLength I := Finset.sum_le_sum hcount
    _ = _ := by rw [← Finset.mul_sum, hsum]
  exact_mod_cast h

end
structure InitialCover {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (b : Rect52Prefix.Band) (freeFixed movingFixed : ODE) where
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
end Rect52Prefix_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
namespace Rect52Prefix_3
noncomputable section
open Polynomial
open Rect52Prefix (Band AnchorModel AnchoredFamily K p agreement)
open Rect52Prefix (Stage Listed Source InBand stages fullCutoff buffered window_nat)
open K1_14 (Shape Banks Jet Equation jetAt seedHasse seedEmbedding)
open K1_14_2 (Ambient OnJet jetMarkHom toJet eval_toJet CoordinateRing SeedField
  JetSeedSection JetYSection ODE)
open K1_14_2_2 (Active dual orderOn FixedPart ODECaps fixedOn RowCaps CutCover
  sectionDegree weight dot joinCuts joinCuts_cost sum_dot emptyCut mass)
open K1_14_2_2_3
open K1_14_2_2_7
open private specialize_shiftedWord shift_word from ProximityPrize.SubmissionLower.Fast052
open scoped BigOperators Classical
abbrev StageIndex (b : Rect52Prefix.Band) := Fin (stages b).length
def pairAt {b h rows} (pairs : Rect52Prefix.Pairs b h rows) (i : StageIndex b) :
    Rect52Prefix.BufferedPair h rows (stageAt b i) :=
  pairs _ (stage_mem i.isLt)
theorem free_listed {b : Rect52Prefix.Band} (i : StageIndex b) : Listed b (stageAt b i).free :=
  Or.inr (Or.inl ⟨_, stage_mem i.isLt, Or.inl rfl⟩)
theorem moving_listed {b : Rect52Prefix.Band} (i : StageIndex b) : Listed b (stageAt b i).moving :=
  Or.inr (Or.inl ⟨_, stage_mem i.isLt, Or.inr rfl⟩)
theorem bank_zero {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) {t : Rect52Prefix.Bank} (ht : Listed b t)
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
    {rows : Banks} (src : Source b M F rows) (hw : InBand b M.overhead) {t : Rect52Prefix.Bank}
    (ht : Listed b t) {r : ℕ} (guard : BankGuard (finish b) r t.shape)
    {P : Jet} (hP : P ∈ rows t.shape (buffered M.overhead.toNat r t.shape))
    (i : Fin 2) (a : ℕ) (ha : a ≤ r) :
    ∀ γ ∈ Γ, jetAt (seedHasse i a P) (M.label γ) (F.scalar γ) = 0 := by
  apply bank_zero src ht guard.pos _ (src.shift t ht _ _ hP i a)
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ ha) _).trans (buffer_spend hw guard)
structure FixedRows {b h rows} (pairs : Rect52Prefix.Pairs b h rows) (i : StageIndex b) where
  free : FixedPart (pairAt pairs i).free (stageAt b i).free.shape
  moving : FixedPart (pairAt pairs i).moving (stageAt b i).moving.shape
def fixedRows {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} (src : Source b M F rows) (pairs : Rect52Prefix.Pairs b M.overhead.toNat rows)
    (i : StageIndex b) : FixedRows pairs i :=
  let pair := pairAt pairs i
  ⟨Classical.choice (K1_14_2_2_1.proof _ _ pair.free_ne
      (src.shape _ (free_listed i) _ _ pair.free_mem)),
    Classical.choice (K1_14_2_2_1.proof _ _ pair.moving_ne
      (src.shape _ (moving_listed i) _ _ pair.moving_mem))⟩
theorem on_surface {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {I : Ideal Ambient} (hI : I.IsPrime) {γ : K} (hm : OnParent F I γ) :
    Rect52Prefix.MarkOn M F (P0_10R.Bridge.surfaceOf I hI) γ := by
  intro P hP
  apply RingHom.mem_ker.mpr
  change jetAt P (M.label γ) (F.scalar γ) = 0
  rw [← eval_toJet]
  exact RingHom.mem_ker.mp (hm hP)
theorem surface_pass {h rows s} {pair : Rect52Prefix.BufferedPair h rows s}
    {I : Ideal Ambient} (hI : I.IsPrime) (hp : PairPass pair I) :
    Rect52Prefix.PairPass pair (P0_10R.Bridge.surfaceOf I hI) :=
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
    {t : Rect52Prefix.Bank} (ht : Listed b t) {r : ℕ}
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
    {rows : Banks} (src : Source b M F rows) {t : Rect52Prefix.Bank} (ht : Listed b t)
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
    (pairs : Rect52Prefix.Pairs b M.overhead.toNat rows) (i : StageIndex b) {I : Ideal Ambient}
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

end
end Rect52Prefix_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1000000
namespace Rect52Prefix_3
noncomputable section
open Rect52Prefix (Band AnchorModel AnchoredFamily)
open Rect52Prefix (stages terminal Source InBand)
open P1_7_4 (massQ_mono)
open K1_14 (Banks)
open K1_14_2 (Ambient)
open K1_14_2_2 (Active Fits dual fixedOn mass)
open scoped Classical
def nextIndex {b : Rect52Prefix.Band} (i : ℕ) (hi : i < laterCount b) : StageIndex b :=
  ⟨i+1, by change i+1 < (stages b).length; unfold laterCount at hi; omega⟩
structure Process {b h rows} (pairs : Rect52Prefix.Pairs b h rows) where
  sched : ScheduleOK b
  parents : Finset (Ideal Ambient)
  fixed : ∀ i : StageIndex b, FixedRows pairs i
  geometry : ∀ I ∈ parents, Active I ∧ I.height = 2
  init_mass : Fits parents (initialCap b)
def Process.Clean {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs)
    (I : Ideal Ambient) : Prop :=
  ∀ i, ¬ fixedOn (R.fixed i).free.equation I ∧ ¬ fixedOn (R.fixed i).moving.equation I
def PassedThrough {b h rows} (pairs : Rect52Prefix.Pairs b h rows) (i : ℕ) (I : Ideal Ambient) : Prop :=
  ∀ j : StageIndex b, 0 < j.val → j.val ≤ i → PairPass (pairAt pairs j) I
def Process.tested {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  R.parents.filter fun I => R.Clean I ∧ PassedThrough pairs i I
def Process.kept {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  (R.tested i).filter fun I => stopIndex b ≤ i → dual I
def Process.rankExit {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs) :
    Finset (Ideal Ambient) :=
  (R.tested (stopIndex b)).filter fun I => ¬ dual I
def Process.final {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs) :
    Finset (Ideal Ambient) :=
  (R.kept (laterCount b)).filter (BankPass rows (terminal b).shape)
def Process.live {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  if i ≤ laterCount b then R.kept i else R.final
def Process.lost {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs) (i : ℕ) :
    Finset (Ideal Ambient) :=
  if hi : i < laterCount b then
    (R.kept i).filter fun I => ¬ PairPass (pairAt pairs (nextIndex i hi)) I
  else
    (R.kept i).filter fun I => ¬ BankPass rows (terminal b).shape I
theorem Process.tested_sub {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs)
    (i : ℕ) : R.tested i ⊆ R.parents :=
  Finset.filter_subset _ _
theorem Process.kept_sub {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs)
    (i : ℕ) : R.kept i ⊆ R.tested i :=
  Finset.filter_subset _ _
theorem Process.final_sub {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs) :
    R.final ⊆ R.kept (laterCount b) :=
  Finset.filter_subset _ _
theorem Process.lost_sub {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs)
    (i : ℕ) : R.lost i ⊆ R.kept i := by
  unfold Process.lost
  split <;> exact Finset.filter_subset _ _
private theorem Process.tested_anti {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs)
    {i j : ℕ} (hij : i ≤ j) : R.tested j ⊆ R.tested i := by
  intro I hI
  obtain ⟨hm, hc, hp⟩ := Finset.mem_filter.mp hI
  exact Finset.mem_filter.mpr ⟨hm, hc, fun k hpos hk => hp k hpos (hk.trans hij)⟩
private theorem Process.kept_anti {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs)
    {i j : ℕ} (hij : i ≤ j) : R.kept j ⊆ R.kept i := by
  intro I hI
  obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hI
  exact Finset.mem_filter.mpr ⟨R.tested_anti hij hm, fun h => hp (h.trans hij)⟩
theorem Process.next_sub {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs)
    {i : ℕ} (hi : i ≤ laterCount b) : R.live (i+1) ⊆ R.live i := by
  rcases hi.lt_or_eq with ht | he
  · simp only [Process.live, ite_eq_left hi, ite_eq_left (Nat.succ_le_of_lt ht)]
    exact R.kept_anti (Nat.le_succ _)
  · subst i
    simpa [Process.live] using R.final_sub
theorem Process.lost_diff {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs)
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
    {rows : Banks} {pairs : Rect52Prefix.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (estimate : PairedMass) (src : Source b M F rows) (hw : InBand b M.overhead)
    (i : StageIndex b) (hi : 0 < i.val) (square : Bool)
    {A : Finset (Ideal Ambient)} (hA : A ⊆ R.tested i)
    (hdual : square = true → ∀ I ∈ A, dual I) (k : Fin 4) :
    massQ A k ≤ stageCap b i square k := by
  let s := stageAt b i
  let pair := pairAt pairs i
  obtain ⟨ga, gb⟩ := R.sched.stage_guard i i.isLt
  have hr := R.sched.small_reserve _ i.isLt
  have hrpos := R.sched.later_pos (i.val-1) (by have hh : i.val < (stages b).length := i.isLt; unfold laterCount; omega)
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
    {rows : Banks} {pairs : Rect52Prefix.Pairs b M.overhead.toNat rows} (R : Process pairs)
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
    {rows : Banks} {pairs : Rect52Prefix.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (estimate : PairedMass) (src : Source b M F rows) (hw : InBand b M.overhead)
    {i : ℕ} (hi : i ≤ laterCount b) (k : Fin 4) : massQ (R.live i) k ≤ history b i k := by
  rw [Process.live, ite_eq_left hi]
  exact R.cap_kept estimate src hw hi k
theorem Process.rank_geometry {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs)
    {I : Ideal Ambient} (hI : I ∈ R.rankExit) : Active I ∧ ¬ dual I :=
  let hm := Finset.mem_filter.mp hI
  ⟨(R.geometry I (R.tested_sub _ hm.1)).1, hm.2⟩
private theorem stop_eq (b : Rect52Prefix.Band) : stopIndex b = 2 := by cases b <;> rfl

theorem Process.rank_enter {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs)
    {i : ℕ} (hi : i < stopIndex b) : R.tested (stopIndex b) ⊆ R.live i := by
  rw [Process.live, ite_eq_left (hi.le.trans R.sched.stop_le)]
  intro I hI
  exact Finset.mem_filter.mpr ⟨R.tested_anti hi.le hI, fun h => False.elim (by omega)⟩

theorem Process.rank_before_loss {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs)
    {i : ℕ} (hstop : i < stopIndex b) : R.lost i ⊆ R.live i \ R.tested (stopIndex b) := by
  have hi : i < laterCount b := hstop.trans_le R.sched.stop_le
  intro I hI
  have hf := (Finset.mem_filter.mp
    (show I ∈ (R.kept i).filter _ from by simpa only [Process.lost, dite_eq_left hi] using hI)).2
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · simpa only [Process.live, ite_eq_left hi.le] using R.lost_sub i hI
  · intro htest
    exact hf ((Finset.mem_filter.mp htest).2.2 (nextIndex i hi) (Nat.succ_pos i)
      (by change i+1 ≤ stopIndex b; omega))

theorem Process.rank_entry_cap {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : Rect52Prefix.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (estimate : PairedMass) (src : Source b M F rows) (hw : InBand b M.overhead)
    (k : Fin 4) : massQ (R.tested (stopIndex b)) k ≤ rankMass b k := by
  have h := R.sched.stop_le
  rw [stop_eq] at h
  have hi : 1 < laterCount b := by omega
  rw [rankMass, stop_eq]
  simp only [show (2 : ℕ) ≠ 0 by decide, ite_false, Nat.reduceSub]
  refine le_min ((massQ_mono ?_ k).trans (R.cap_kept estimate src hw hi.le k)) ?_
  · intro I hI
    exact Finset.mem_filter.mpr ⟨R.tested_anti (by decide : 1 ≤ 2) hI,
      fun hstop => False.elim (by rw [stop_eq] at hstop; omega)⟩
  · exact R.local_cap estimate src hw (nextIndex 1 hi) (Nat.succ_pos 1) false (fun _ h => h)
      (by intro h; contradiction) k

theorem Process.rank_cap {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : Rect52Prefix.Pairs b M.overhead.toNat rows} (R : Process pairs)
    (estimate : PairedMass) (src : Source b M F rows) (hw : InBand b M.overhead)
    (k : Fin 4) : massQ R.rankExit k ≤ rankMass b k :=
  (massQ_mono (Finset.filter_subset _ _) k).trans (R.rank_entry_cap estimate src hw k)
theorem Process.retains {b h rows} {pairs : Rect52Prefix.Pairs b h rows} (R : Process pairs)
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
end Rect52Prefix_3
end
