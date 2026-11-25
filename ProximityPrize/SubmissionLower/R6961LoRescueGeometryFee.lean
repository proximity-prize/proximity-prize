import ProximityPrize.SubmissionLower.R6961LoRescueGeometryInvoice
import ProximityPrize.SubmissionLower.TwoJetCaseBBridge

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6961.Lo.RescueGeometry
open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL evaluated)
open K1_14_2 (Ambient ODE)
open K1_14_2_2 (mass mass_mono ODECaps)
open K1_14_3 (Surface Parent)
open P1_7_4 (ODEGuard Mass massQ dotQ dotQ_mono_mass massQ_mono dotQ_scale_add)
open P1_7_4_3 (mix)
open HighCore82268JointRank (fixed_fee_linear)
open Lower6961.Lo.RescueGeometry (persistentTotal persistentTop siteRatio density)
open Lower6961.RescueGeometry (Model Family word OnMark OnSurface)
open scoped Classical BigOperators

def Initial.rankMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 10} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>∃ J∈ini.rankExit,OnMark F J γ)

theorem fixedFee_eq (B J : ℕ) :
    fixedFee B J = (mix B J (mu+2*lambda*(B-1 : ℕ))
      (min (mu+2*lambda*(B-1 : ℕ)) (lambda*(2*J-1 : ℕ)))).ceil.toNat+B^2 := by
  have he : 2*density*(endpointDegree : ℚ)=2*lambda := by unfold lambda density; ring
  have hl : density*(endpointDegree : ℚ)=lambda := rfl
  have hm : siteRatio endpointDegree=mu := rfl
  unfold fixedFee persistentTop persistentTotal
  rw [he,hl,hm]

/-- The actual rank-exit marks satisfy the linear ODE charge at the new
upper height. They share their initial mass with the dual parents. -/
theorem Initial.rank_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 10} (ini : Initial F G Q₀ rect) (hi : M.overhead.toNat≤2449) :
    (ini.rankMarks.card : ℚ)≤dotQ (rankWeight rect) (massQ ini.rankExit)+rankRound rect := by
  let S := ini.rankExit
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  obtain ⟨E,caps,roots⟩ := ini.rank_ode
  have mass_cap (k : Fin 4) : mass S k ≤ initialCap rect k :=
    (mass_mono (subset_union_left : S⊆ini.rankExit∪ini.parents) k).trans (ini.fits k)
  have hBm : B≤mass S 2+2 := max_le (by omega) (by omega)
  have hJm : J≤mass S 1+1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B≤rankB rect := hBm.trans (Nat.add_le_add_right (mass_cap 2) 2)
  have hJ : J≤rankJ rect := hJm.trans (Nat.add_le_add_right (mass_cap 1) 1)
  have hB2 : 2≤B := le_max_left _ _
  have hJ1 : 1≤J := le_max_left _ _
  have hJB : J≤B := max_le (by omega) (min_le_right _ _)
  have degree : E.natDegree≤B := by
    have top : E.coeff E.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree≠0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1,(le_min caps.2.1 degree).trans (le_max_right _ _),
    fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  obtain ⟨small,cJ,cB⟩ := rank_guard rect
  have guard : ODEGuard B J := ⟨hB2,hJ1,hJB,hB.trans_lt small⟩
  have count : ini.rankMarks.card≤fixedFee B J :=
    fixed_count F hi guard E ocaps (filter_subset _ _)
      (fun γ mem => roots γ (mem_filter.mp mem).1 (mem_filter.mp mem).2)
  have lin := fixed_fee_linear lambda mu tau (pivot rect) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤
      rankWeight rect 1 * J + rankWeight rect 2 * B + 2*lambda*pivot rect^2+1 := by
    rw [fixedFee_eq]
    exact lin
  have hJq : (J : ℚ)≤(mass S 1 : ℚ)+1 := by exact_mod_cast hJm
  have hBq : (B : ℚ)≤(mass S 2 : ℚ)+2 := by exact_mod_cast hBm
  have hjfee := mul_le_mul_of_nonneg_left hJq cJ
  have hbfee := mul_le_mul_of_nonneg_left hBq cB
  have hdot : dotQ (rankWeight rect) (massQ ini.rankExit) =
      rankWeight rect 1 * (mass S 1 : ℚ)+rankWeight rect 2 * (mass S 2 : ℚ) := by
    simp [dotQ,rankWeight,massQ,Fin.sum_univ_succ,S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [hdot,rankRound]
  linarith only [hjfee,hbfee]

private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ)≤q) : a≤q.ceil.toNat := by
  have ceil_cast : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact_mod_cast bound.trans (Rat.le_ceil.trans ceil_cast)

theorem CutBooks.curve_bin_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hiM : M.overhead.toNat≤2449) {i : ℕ} (hi : i<17) :
    ((curveMarks F (C.cover i)).card : ℚ)≤
      dotQ (lossWeight R.rect i) (massQ (R.lost i))+((C.cover i).cost 0 : ℚ) := by
  have global : ((C.cover i).cost 0 : ℚ)≤seedLimit R.rect :=
    (single_le_sum (fun j _=>Nat.cast_nonneg (α:=ℚ) ((C.cover j).cost 0))
      (mem_range.mpr hi)).trans C.seed_bill
  have localCap : ((C.cover i).cost 0 : ℚ)≤ dotQ (cutWeight R.rect 0 i) (history R.rect i) :=
    (C.costQ hi 0).trans (dotQ_mono_mass (fun _=>Nat.cast_nonneg _)
      (fun k=>(massQ_mono sdiff_subset k).trans (R.live_history hi k)))
  have prime : (C.cover i).cost 0 < p := by exact_mod_cast global.trans_lt (seed_limit_small R.rect)
  obtain ⟨ok,degree⟩ := rate_spec R.rect hi
  have count := rated_curve_count F (curve_tariff F hiM) ok (C.cover i)
    global ((min_le_min le_rfl localCap).trans degree) prime
  calc
    _ ≤ (degreeRate R.rect i : ℚ)*((C.cover i).cost 0 : ℚ) +
          (heightRate R.rect i : ℚ)*((C.cover i).cost 1 : ℚ)+((C.cover i).cost 0 : ℚ) := count
    _ ≤ (degreeRate R.rect i : ℚ)*dotQ (cutWeight R.rect 0 i) (massQ (R.lost i)) +
          (heightRate R.rect i : ℚ)*dotQ (cutWeight R.rect 1 i) (massQ (R.lost i)) +
          ((C.cover i).cost 0 : ℚ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (C.costQ hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (C.costQ hi 1) (Nat.cast_nonneg _))) le_rfl
    _ = _ := by rw [dotQ_scale_add]; rfl

def CutBooks.lossMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G} (C : CutBooks R) :
    Finset K := R.initial.rankMarks ∪ (range 17).biUnion (fun i=>curveMarks F (C.cover i))

theorem CutBooks.loss_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hi : M.overhead.toNat≤2449) : C.lossMarks.card ≤ (lossLimit R.rect).ceil.toNat := by
  apply card_round
  have cum : (C.lossMarks.card : ℚ) ≤ (R.initial.rankMarks.card : ℚ) +
      ∑ i∈range 17,((curveMarks F (C.cover i)).card : ℚ) := by
    exact_mod_cast (show C.lossMarks.card ≤ R.initial.rankMarks.card +
      ∑ i∈range 17,(curveMarks F (C.cover i)).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have sum_cuts := sum_le_sum (fun _ mem=>C.curve_bin_count hi (mem_range.mp mem))
    (s:=range 17)
  rw [sum_add_distrib] at sum_cuts
  have both := add_le_add (R.initial.rank_count hi) sum_cuts
  have joint := R.joint_bill (rankWeight R.rect) (lossWeight R.rect)
  have seed := C.seed_bill
  have total := cum.trans both
  unfold lossLimit
  linarith only [total,joint,seed]

def CutBooks.paid {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G} (C : CutBooks R) :
    Finset K := ((C.lossMarks ∪ C.pointMarks) ∪ R.initial.seedMarks) ∪ R.initial.ordinateMarks

theorem CutBooks.paid_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hi : M.overhead.toNat≤2449) : C.paid.card≤rescueFee R.rect := by
  have h1 := card_union_le ((C.lossMarks∪C.pointMarks)∪R.initial.seedMarks) R.initial.ordinateMarks
  have h2 := card_union_le (C.lossMarks∪C.pointMarks) R.initial.seedMarks
  have h3 := card_union_le C.lossMarks C.pointMarks
  have rate := C.loss_count hi
  have points := card_round C.point_bill
  have seeds := R.initial.seed_count
  have ordinates := R.initial.ordinate_count
  unfold rescueFee CutBooks.paid
  omega

private theorem small_stage0_shape (rect : Fin 10) (h : rect.val < 6) :
    (⟨59, 80 + 10 * (RescueSource.jetCap rect - 1), 24, 399 + 10 * RescueSource.seedCap rect⟩ : K1_14.Shape) =
      (RescueSource.bank rect 0).shape := by
  fin_cases rect <;> simp_all [RescueSource.jetCap, RescueSource.seedCap, RescueSource.bank] <;> decide

private theorem jetCap_pos (rect : Fin 10) : 1 ≤ RescueSource.jetCap rect := by
  fin_cases rect <;> decide

/-- Hybrid 2-Jet + 1-Jet exceptional prefix at `69.61` (`h ∈ [2346, 2449]`):
- Small rectangles (`rect < 6`): Case B (`jacDet = 0`) pays all marks on `G` directly (`≤ 37.71e15`);
  Case A (`jacDet ≠ 0`) constructs the Stage-0 avoiding prolongation row `Q₀` on `Γ_G` via `TwoJetCaseAFX`,
  then runs the 16 1-jet stages `1..16`.
- Large rectangles (`6 ≤ rect`): runs pure 1-jet stages `0..16`. -/
theorem exceptional_prefix {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2346≤M.overhead.toNat) (hi : M.overhead.toNat≤2449)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (common : Lower6960.PrefixRows.Common
      (evaluated Crt (word M) HelperSource.helperBank.shape (HelperSource.helperCutoff M.overhead.toNat)) G) :
    ∃ (paid : Finset K) (S : Finset Surface),
      paid.card ≤ 41008681981222112 ∧
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨rect, linear, jCap, uCap, hSmallIn, rows⟩ :=
    RescueSource.exceptional_rows Crt (word M) lo hi common.1 common.2.2.1 common.2.1 common.2.2.2
  have capsG : K1_14_2_2.RowCaps G (primeShape rect) :=
    (K1_14_2_2_2_1.rowCaps_iff G _).mpr ⟨jCap, linear.le, uCap⟩
  by_cases hsm : rect.val < 6
  · by_cases hdet : TwoJetCaseAKernel.jacDet TwoJetCaseADriver.fractionRingFieldDerivs
        (TwoJetCaseAFX.alpha1 G) (TwoJetCaseAFX.alpha2 G) = 0
    · -- Case B: direct 2-jet differential polynomial cap (`≤ 37.71e15 ≤ max_rescue_fee_lo`)!
      let ΓG := Γ.filter fun γ => jetAt G (M.label γ) (F.scalar γ) = 0
      have capsExact : K1_14_2_2.RowCaps G ⟨0, K1_14_2_2_2_1.jetDegree G, 1, K1_14_2_2_2_1.seedDegree G⟩ :=
        (K1_14_2_2_2_1.rowCaps_iff G _).mpr ⟨le_rfl, linear.le, le_rfl⟩
      have hB := (TwoJetCaseBBridge.caseB_small_rect_card_le_6961 F hi common.1 linear common.2.2.1
        (hSmallIn hsm) capsExact hdet).2
      refine ⟨ΓG, ∅, hB.trans (by decide), by simp, ?_⟩
      intro γ hγ hGz
      exact Or.inl (mem_filter.mpr ⟨hγ, hGz⟩)
    · -- Case A: Stage-0 2-jet prolongation avoidance on `ΓG`!
      let ΓG := Γ.filter fun γ => jetAt G (M.label γ) (F.scalar γ) = 0
      let FG : Family M ΓG := ⟨F.scalar, fun γ hγ => F.mark γ (mem_filter.mp hγ).1,
        F.distinct.mono (filter_subset _ _)⟩
      obtain ⟨W, hW, P₀, hP₀, hAvoid0⟩ :=
        TwoJetCaseAFX.caseA_avoidance_6961 lo hi Crt (word M) linear hdet
      let Q₀ := TwoJetRescueBridge.prolongSubst (TwoJetCaseAFX.prolongA G)
        (TwoJetCaseAFX.prolongB1 G) 10 (TwoJetRescueBridge.centerEval2 P₀)
      have capsQ0 : K1_14_2_2.RowCaps Q₀ (RescueSource.bank rect 0).shape := by
        rw [← small_stage0_shape rect hsm]
        exact TwoJetCaseAFX.rowCaps_mono
          (TwoJetCaseAFX.prolongSubst_rowCaps (jetCap_pos rect) capsG hP₀.1.1) le_rfl le_rfl le_rfl
      have zero0 : ∀ γ ∈ ΓG, jetAt Q₀ (M.label γ) (FG.scalar γ) = 0 := by
        intro γ hγ
        obtain ⟨hγΓ, hGz⟩ := mem_filter.mp hγ
        let B := F.mark γ hγΓ
        have hdeg : (K1_14.liftPoly (F.scalar γ)).natDegree ≤ 131071 + M.overhead.toNat := by
          rw [K1_14.liftPoly, Polynomial.natDegree_map]
          rcases B.scalar_degree with h0 | hd
          · simp [h0]
          · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at hd; omega
        have hhits : ∀ k ∈ B.bad.support, (K1_14.liftPoly (F.scalar γ)).eval (nodeL k) = word M k := by
          intro k hk
          rw [word, K1_14.liftPoly, nodeL, Polynomial.eval_map, Polynomial.eval₂_hom]
          exact congrArg (algebraMap K K1_14.L) (B.scalar_hits k hk)
        have hW' : W < (TwoJetCaseAFX.shape2_m59 399).m * 179808 := hW.trans_le (by decide)
        exact TwoJetCaseAFX.prolongSubst_vanish_at_mark (A := 179808) (s := TwoJetCaseAFX.shape2_m59 399)
          Crt (word M) noPole (M.label γ) (F.scalar γ)
          (residues γ hγΓ) hdeg B.bad.support B.bad.agreement hhits hW' hP₀ linear hGz
      obtain ⟨R, C, S, geom, cover⟩ := inventory_with_Q0 FG Crt lo hi noPole
        (fun γ hγ => residues γ (mem_filter.mp hγ).1) common.1 rect capsG Q₀ hAvoid0 capsQ0 zero0
        (fun i hi0 => rows i (Or.inr hi0))
      refine ⟨C.paid, S, (C.paid_count hi).trans (rescue_fee_bound R.rect), geom, ?_⟩
      intro γ hγ hGz
      have hγG : γ ∈ ΓG := mem_filter.mpr ⟨hγ, hGz⟩
      rcases cover γ hγG hGz with seed | ordinate | rank | point | ⟨i, hi', curve, mem, on⟩ | retained
      · exact Or.inl (mem_union_left _ (mem_union_right _ seed))
      · exact Or.inl (mem_union_right _ ordinate)
      · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _
          (mem_union_left _ (mem_filter.mpr ⟨hγG, rank⟩)))))
      · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ point)))
      · have cuts : γ ∈ (range 17).biUnion (fun i => curveMarks FG (C.cover i)) :=
          mem_biUnion.mpr ⟨i, mem_range.mpr hi', mem_curveMarks (F := FG) hγG mem on⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ cuts))))
      · exact Or.inr retained
  · -- Large rectangle (`6 ≤ rect.val`): pure 1-jet Stage 0!
    have hlg : 6 ≤ rect.val := by omega
    obtain ⟨Q₀, hQ₀_mem, hAvoid0⟩ := rows 0 (Or.inl hlg)
    have capsQ0 : K1_14_2_2.RowCaps Q₀ (RescueSource.bank rect 0).shape :=
      K1_14_1.evaluated_shape Crt (word M) hQ₀_mem
    have zero0 : ∀ γ ∈ Γ, jetAt Q₀ (M.label γ) (F.scalar γ) = 0 := fun γ hγ =>
      Lower6961.RescueGeometry.zero_of_contact
        (Lower6961.RescueGeometry.contact_at_mark F Crt noPole residues hQ₀_mem
          (RescueSource.cutoff_fit lo hi rect 0 (Or.inl hlg)) γ hγ)
    obtain ⟨R, C, S, geom, cover⟩ := inventory_with_Q0 F Crt lo hi noPole residues
      common.1 rect capsG Q₀ hAvoid0 capsQ0 zero0 (fun i hi0 => rows i (Or.inr hi0))
    refine ⟨C.paid, S, (C.paid_count hi).trans (rescue_fee_bound R.rect), geom, ?_⟩
    intro γ hγ hGz
    rcases cover γ hγ hGz with seed | ordinate | rank | point | ⟨i, hi', curve, mem, on⟩ | retained
    · exact Or.inl (mem_union_left _ (mem_union_right _ seed))
    · exact Or.inl (mem_union_right _ ordinate)
    · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _
        (mem_union_left _ (mem_filter.mpr ⟨hγ, rank⟩)))))
    · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ point)))
    · have cuts : γ ∈ (range 17).biUnion (fun i => curveMarks F (C.cover i)) :=
        mem_biUnion.mpr ⟨i, mem_range.mpr hi', mem_curveMarks (F := F) hγ mem on⟩
      exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ cuts))))
    · exact Or.inr retained

end Lower6961.Lo.RescueGeometry
