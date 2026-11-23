import ProximityPrize.SubmissionLower.H2429AffinePrefixBill
import ProximityPrize.SubmissionLower.HighCore82258BankProof
import ProximityPrize.SubmissionLower.HighCore82258Ledger

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000

namespace H2429AffineInventory
noncomputable section
open Finset Polynomial
open scoped BigOperators Classical
open FrontCore82258 (effectiveHeight)
open HighCore82258 (K p I node AnchorModel AnchoredFamily InBand Source BankPass Pairs MarkOn fees stages)
open HighCore82258_3
open K1_14 (Equation Jet Banks atX graphEval seedHasse jetAt)
open K1_14_2 (Ambient fixedAt)
open K1_14_2_2 (mass)
open K1_14_3 (Surface Parent ProjectedProduct SeedCover)
open P0_10R.Bridge (surfaceOf parent_of_dual seed_side_bounded)
open KoalaH2429PrefixNumbers (fullPrefix lowSeedSaving fixedBankFees)
open H2429AffinePrefixBill (gradeOf fixedPrice FixedPrice)
open private ceil_eq from ProximityPrize.SubmissionLower.H2429AffinePrefixBill
open private fixedMarks fixedBook mem_fixed_left mem_fixed_right
  from ProximityPrize.SubmissionLower.HighCore82258PrefixGeometry

private abbrev b : HighCore82258.Band := .h2429

def fee (e : ℕ) : ℕ := fullPrefix (gradeOf e) - lowSeedSaving

def Framed {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ) : Prop :=
  ∃ (G : Polynomial K) (R : Fin 2 → Polynomial K),
    (∀ i : I, G.eval (node i) ≠ 0) ∧
    ResidueSpace.space G 128643 R ≤ degreeLT K 133501 ∧
    ∀ γ ∈ Γ, F.scalar γ ∈ ResidueSpace.space G 128643 R

private theorem fixed_of_frame {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    (frame : Framed F) : FixedPrice F := by
  obtain ⟨G,R,off,hd,hframe⟩ := frame
  intro B J guard q hq T hT hroot
  have hw : HighCore82258.FixedWord M.word T F.scalar 133500 := by
    refine ⟨F.distinct.mono hT,?_,?_⟩
    · intro γ hg
      by_cases hz : F.scalar γ = 0
      · simp [hz]
      · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hz).mpr
          (mem_degreeLT.mp (hd (hframe γ (hT hg)))))
    · intro γ hg
      let mk := F.mark γ (hT hg)
      exact ⟨mk.bad.support,mk.bad.agreement,mk.scalar_hits⟩
  have h := H2429AffineFixedCount.count hw G R off hd (fun γ hγ => hframe γ (hT hγ)) guard q hq hroot
  obtain ⟨ha,hv⟩ := H2429AffineFixedCount.linearized_rates B J guard.jpos
  apply h.trans
  unfold fixedPrice
  apply Nat.add_le_add_right
  apply Int.toNat_le_toNat
  rw [← ceil_eq]
  apply Int.ceil_mono
  have hρ : H2429AffineRates.ratio 0 = H2429AffinePrefixBill.rho := by decide +kernel
  rw [hρ] at ha hv
  change H2429AffineFixedCount.totalRate B ≤
    H2429AffinePrefixBill.rho + 2*H2429AffinePrefixBill.lam*(B-1 : ℕ) at ha
  change H2429AffineFixedCount.topRate B J ≤
    min (H2429AffineFixedCount.totalRate B) (H2429AffinePrefixBill.lam*(2*J-1 : ℕ)) at hv
  unfold P1_7_4_3.mix
  exact add_le_add (mul_le_mul_of_nonneg_left (hv.trans (min_le_min ha le_rfl)) (Nat.cast_nonneg _))
    (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _))

private theorem stage_sum {α : Type} (stages : List α) (default : α) (f : α → ℕ) :
    (∑ i ∈ range stages.length, f (stages[i]?.getD default)) = (stages.map f).sum := by
  induction stages with
  | nil => simp
  | cons s ss ih => simp [Finset.sum_range_succ',ih,Nat.add_comm]

private theorem fixed_book_fee {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows : Banks} {pairs : Pairs b (effectiveHeight M).toNat rows} (R : Process pairs)
    (hcount : FixedPrice F) : (fixedBook F R).card ≤ fixedBankFees := by
  let price (s : HighCore82258.Stage) := fixedPrice s.free.shape.B s.free.shape.J +
    fixedPrice s.moving.shape.B s.moving.shape.J
  have hfee {B J : ℕ} (guard : ODEGuard B J) {G : K1_14_2.ODE}
      (cap : K1_14_2_2.ODECaps G B J) : (fixedMarks F G).card ≤ fixedPrice B J :=
    hcount B J guard G cap _ (filter_subset _ _) (fun _ hγ => (mem_filter.mp hγ).2)
  calc
    _ ≤ ∑ i : StageIndex b,
        (fixedMarks F (R.fixed i).free.equation ∪ fixedMarks F (R.fixed i).moving.equation).card :=
      card_biUnion_le
    _ ≤ ∑ i : StageIndex b, price (stageAt b i) := by
      apply sum_le_sum
      intro i _
      obtain ⟨g,h⟩ := R.sched.stage_guard i i.isLt
      exact (card_union_le _ _).trans (Nat.add_le_add
        (hfee g.ode (R.fixed i).free.equation_caps) (hfee h.ode (R.fixed i).moving.equation_caps))
    _ = fixedBankFees := by
      rw [Fin.sum_univ_eq_sum_range (fun i => price (stageAt b i)) (HighCore82258.stages b).length]
      exact stage_sum _ _ price

structure Inventory {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (rows : Banks) where
  parents : Finset Surface
  equation : Equation
  projected : parents.Nonempty → ProjectedProduct parents equation
  marks : Finset K
  marks_sub : marks ⊆ Γ
  covers : ∀ γ ∈ marks, ∃ q ∈ parents, MarkOn M F q γ
  geometric : ∀ q ∈ parents, Parent q
  terminal_pass : ∀ q ∈ parents, BankPass rows (HighCore82258.terminal b).shape q
  prefix_paid : (Γ \ marks).card + 1 ≤ fee equation.natDegree

theorem produce {u del Γ} (M : AnchorModel u del) (F : AnchoredFamily M Γ)
    (hw : InBand b (effectiveHeight M)) (frame : Framed F) (rows : Banks)
    (src : Source b M F rows) (pairs : Pairs b (effectiveHeight M).toNat rows) :
    Nonempty (Inventory M F rows) := by
  have tariff : H2429AffineCurve.Tariff M F := by
    obtain ⟨G,R,off,hd,hframe⟩ := frame
    exact H2429AffineCurve.of_frame M F G R off hd hframe
  have hfixed := fixed_of_frame frame
  let sched:=HighCore82258.schedule b
  let zero:StageIndex b:=⟨0,sched.stages_pos⟩
  let P:=pairAt pairs zero
  let fixed:=fixedRows src pairs
  obtain ⟨ga,gb⟩:=sched.stage_guard 0 sched.stages_pos
  have hfree:=src.shape _ (free_listed zero) _ _ P.free_mem
  have hg:=src.shape _ (moving_listed zero) _ _ P.moving_mem
  let later (i:ℕ):Jet:=if hi:i < (stages b).length then (pairAt pairs ⟨i,hi⟩).free else 0
  obtain ⟨initial⟩ := HighCore82258_3_1.proof b u del M Γ F sched P.free P.moving P.free_ne P.moving_ne
    P.no_moving hfree hg (fixed zero).free (fixed zero).moving (fun γ hγ =>
      ⟨bank_zero src (free_listed zero) ga.pos (Nat.sub_le _ _) P.free_mem γ hγ,
        bank_zero src (moving_listed zero) gb.pos (Nat.sub_le _ _) P.moving_mem γ hγ⟩) later (by
      intro i hi
      obtain ⟨_,hsize⟩:=sched.intro_pos i hi
      let j:StageIndex b:=⟨i,hsize⟩
      let pair:=pairAt pairs j
      simp only [later,dite_eq_left hsize]
      exact ⟨pair.free_ne, src.shape _ (free_listed j) _ _ pair.free_mem,
        fun k a ha => intro_zero src hw (free_listed j) (sched.stage_guard i hsize).1 pair.free_mem k a ha⟩)
  let R : Process pairs :=
    ⟨sched, initial.parents, fixed, fun I hI => ⟨initial.active I hI, initial.height_two I hI⟩,
      initial.mass_bound⟩
  have initial_mem (I : ↥R.final) : I.1 ∈ R.parents :=
    R.tested_sub _ (R.kept_sub _ (R.final_sub I.2))
  let toSurface (I : ↥R.final):Surface:=surfaceOf I.1 (R.geometry _ (initial_mem I)).1.prime
  let parents:=R.final.attach.image toSurface
  have hproduct : ∃ f : K1_14.Equation,
      (parents.Nonempty→K1_14_3.ProjectedProduct parents f) ∧ f.natDegree≤mass R.final 0:=by
    by_cases hm:R.final.Nonempty
    · obtain ⟨I, hI⟩ := hm
      have ha:R.final.attach.Nonempty:=⟨⟨I,hI⟩,Finset.mem_attach _ _⟩
      obtain ⟨f, hf, hdeg⟩ := K1_14_3_7.proof_indexed R.final.attach toSurface ha
        (fun i => K1_14_2_2.sectionDegree i.1 0)
        (fun i _ => seed_side_bounded (R.geometry i.1 (initial_mem i)).1)
      rw [Finset.sum_attach R.final (fun I => K1_14_2_2.sectionDegree I 0)] at hdeg
      exact ⟨f, fun _ => hf, hdeg⟩
    · refine ⟨0, ?_, by simp⟩
      exact fun ⟨q,hq⟩ => False.elim (by
        obtain ⟨i,_,_⟩:=Finset.mem_image.mp hq
        exact hm ⟨i.1,i.2⟩)
  obtain ⟨f,hf,hdeg⟩:=hproduct
  let seed := Γ.filter fun γ => initial.seed.Covers (M.label γ)
  have label_inj : Function.Injective M.label := fun _ _ h => sub_left_inj.mp h
  have hSeedFine : seed.card ≤ (p+1)*initial.seed.curve.totalDegree + initialE b := by
    have h := K1_14_3.seed_count (T := seed) label_inj.injOn initial.seed
      (initial.seed_le.trans_lt (sched.initial_small 2)) (fun _ hγ => (Finset.mem_filter.mp hγ).2)
    exact h.trans (Nat.add_le_add_left initial.seed_points _)
  obtain ⟨losses⟩ := H2429AffinePrefixBill.failure_books R src hw (gradeOf f.natDegree)
    ((H2429AffinePrefixBill.degree_gradeOf f.natDegree).trans hdeg)
    tariff hfixed seed initial.seed.curve.totalDegree initial.seed_parent hSeedFine
  let contents := Γ.filter fun γ => graphEval (M.label γ) initial.content = 0
  let ords := Γ.filter fun γ => atX (F.scalar γ) ∈ initial.ordinates
  have hcontents : contents.card ≤ (fees b).content := by
    let C : SeedCover := ⟨initial.content,initial.content_ne,∅⟩
    have h := K1_14_3.seed_count (T := contents) label_inj.injOn C
      (initial.content_le.trans_lt sched.content_small) (fun _ hγ => Or.inl (mem_filter.mp hγ).2)
    have h' : contents.card ≤ (p+1)*initial.content.totalDegree := by
      simpa only [C,card_empty,Nat.add_zero] using h
    exact (h'.trans (Nat.mul_le_mul_left _ initial.content_le)).trans sched.content
  have hords : ords.card ≤ (fees b).lowJet := by
    have he : ords.card ≤ initial.ordinates.card := card_le_card_of_injOn (fun γ => atX (F.scalar γ))
      (fun _ hγ => (mem_filter.mp hγ).2)
      (fun _ hγ _ hη h => F.distinct (mem_filter.mp hγ).1 (mem_filter.mp hη).1
        (K1_14_3.scalar_atX_injective h))
    exact (he.trans initial.ordinate_le).trans (by simpa only [jointRank,ite_true,Nat.add_zero] using sched.low_jet)
  let erased := losses.loss ∪ seed ∪ losses.point ∪ ords ∪ fixedBook F R ∪ contents
  let keep := Γ \ erased
  have hsize : (Γ \ keep).card ≤ erased.card :=
    card_le_card fun γ hγ => by
      obtain ⟨hΓ,h⟩ := mem_sdiff.mp hγ
      by_contra hm
      exact h (mem_sdiff.mpr ⟨hΓ,hm⟩)
  have htotal : erased.card ≤ losses.loss.card + seed.card + losses.point.card + ords.card +
      (fixedBook F R).card + contents.card := by
    unfold erased
    calc
      _ ≤ _ + contents.card := card_union_le _ _
      _ ≤ _ := by
        have h₁ := card_union_le losses.loss seed
        have h₂ := card_union_le (losses.loss ∪ seed) losses.point
        have h₃ := card_union_le (losses.loss ∪ seed ∪ losses.point) ords
        have h₄ := card_union_le (losses.loss ∪ seed ∪ losses.point ∪ ords) (fixedBook F R)
        omega
  have hpay : (Γ \ keep).card + 1 ≤ fee f.natDegree :=
    (Nat.add_le_add_right (hsize.trans htotal) 1).trans
      (KoalaH2429PrefixNumbers.seed_parent_prefix _ losses.loss_seed losses.point_paid hords
        (fixed_book_fee R hfixed) hcontents)
  refine ⟨⟨parents,f,hf,keep,sdiff_subset,?_,?_,?_,hpay⟩⟩
  · intro γ hγ
    obtain ⟨hΓ,hn⟩ := mem_sdiff.mp hγ
    simp only [erased,mem_union,not_or] at hn
    obtain ⟨⟨⟨⟨⟨noPaid,noSeed⟩,noPoint⟩,noOrd⟩,noFixed⟩,noContent⟩ := hn
    have noLoss (h : γ ∈ losses.point ∨ γ ∈ losses.loss) : False :=
      h.elim noPoint noPaid
    rcases initial.covers γ hΓ with hz | ho | hc | ha | hb | ⟨Q,hQ,hm⟩
    · exact (noSeed (mem_filter.mpr ⟨hΓ,hz⟩)).elim
    · exact (noOrd (mem_filter.mpr ⟨hΓ,ho⟩)).elim
    · exact (noContent (mem_filter.mpr ⟨hΓ,hc⟩)).elim
    · exact (noFixed (mem_fixed_left F R zero hΓ ha)).elim
    · exact (noFixed (mem_fixed_right F R zero hΓ hb)).elim
    · have clean : R.Clean Q := fun j =>
        ⟨fun hj => noFixed (mem_fixed_left F R j hΓ (fixed_zero hm hj)),
         fun hj => noFixed (mem_fixed_right F R j hΓ (fixed_zero hm hj))⟩
      have noRank : Q ∉ R.rankExit := fun h => noLoss (Or.inr (losses.rank_covers γ hΓ Q h hm))
      have noLost : ∀ i ≤ laterCount b, Q ∉ R.lost i := fun i hi h =>
        noLoss (losses.covers i hi γ hΓ Q h hm)
      let J : ↥R.final := ⟨Q,R.retains hQ clean noRank noLost⟩
      exact ⟨toSurface J,mem_image_of_mem _ (mem_attach _ _),on_surface _ hm⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩ := mem_image.mp hq
    have hx := R.geometry _ (initial_mem J)
    exact parent_of_dual hx.1 hx.2 ((mem_filter.mp (R.final_sub J.2)).2 sched.stop_le)
  · intro q hq
    obtain ⟨J,_,rfl⟩ := mem_image.mp hq
    exact (mem_filter.mp J.2).2

end
end H2429AffineInventory
