import ProximityPrize.SubmissionLower.HighCore82258JointRankCharge
import ProximityPrize.SubmissionLower.KoalaSeedParentBill
import ProximityPrize.SubmissionLower.KoalaSeedParentInventory

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000

open HighCore82258 (start finish)

open FrontCore82258 (effectiveHeight)

section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace HighCore82258_3
noncomputable section
open Polynomial
open HighCore82258 (AnchorModel AnchoredFamily K p)
open HighCore82258 (CurveTariff curveUnit)
open HighCore82258PrefixHelpers (curveMarks mem_curveMarks direct_curve_count)
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
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩
private theorem mark_graph {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {I:Ideal Ambient} {C:Seeds} (hC:seedImage I=Ideal.span {C}) :
    ∀ z ∈ (Γ.filter (OnParent F I)).image M.label,graphEval z C=0:=by
  intro z hz
  obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hz
  apply on_seed (Finset.mem_filter.mp hγ).2
  rw [hC]
  exact Ideal.mem_span_singleton_self C
private theorem translated_card {u del} (M : AnchorModel u del) (T : Finset K) :
    (T.image M.label).card=T.card :=
  Finset.card_image_of_injective _ (fun _ _ hab => sub_left_inj.mp hab)
private theorem direct_count {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {I:Ideal Ambient} {C:Seeds} (hC:C≠0) (hI:seedImage I=Ideal.span {C})
    (hp:C.totalDegree < p) :
    (Γ.filter (OnParent F I)).card≤(p+1)*C.totalDegree:=by
  have h:=seed_graph_count C hC hp ((Γ.filter (OnParent F I)).image M.label) (mark_graph F hI)
  rwa [translated_card] at h
def CurveTariffFor (unit : ℕ → ℚ) {u del} (M : AnchorModel u del) {Γ}
    (F : AnchoredFamily M Γ) : Prop :=
  ∀ T ⊆ Γ, ∀ J g H, 0 < g → g ≤ 80 → K1_14_2.SmallRootCurve J g H →
    Module.finrank SeedField (RootSeedSection J) < p →
    (∀ γ ∈ T, K1_14_2.OnRoot J (M.label γ) (F.scalar γ)) →
    (T.card : ℚ) ≤ unit g * H + g

structure DiscountRate (unit : ℕ → ℚ) (a h : ℚ) : Prop where
  degree : ((p+1 : ℕ) : ℚ)/81 ≤ a
  height : 0 ≤ h
  interpolation : ∀ g : ℕ, 0 < g → g ≤ 80 →
    max 0 (1 - a*g/((p+1 : ℕ) : ℚ))*unit g ≤ h

private theorem interpolate (unit : ℕ → ℚ) (g : ℕ) (a h d H T : ℚ) (hg : 0 < g)
    (hH:0≤H) (hd:0≤d) (hu:DiscountRate unit a h)
    (direct:T≤((p+1:ℕ):ℚ)*d)
    (tariff:g≤80→T≤ unit g*H+g) :
    T≤a*(d*g)+h*H+g:=by
  let q:ℚ:=(p+1:ℕ)
  have hq:0 < q:=Nat.cast_pos.mpr (Nat.succ_pos p)
  have ha:0≤a:=(show 0≤q/81 by positivity).trans hu.degree
  by_cases large:q≤a*g
  · calc
      T≤q*d:=direct
      _≤(a*g)*d:=mul_le_mul_of_nonneg_right large hd
      _=a*(d*g):=by ring
      _ ≤ _ := by
        have hn:=mul_nonneg hu.height hH
        have hgq:(0:ℚ)≤g:=Nat.cast_nonneg _
        linarith
  · have hgsmall : g ≤ 80 := by
      by_contra! h
      have hgQ:(81:ℚ)≤g:=by exact_mod_cast Nat.succ_le_of_lt h
      have he:q/81*81=q:=by ring
      apply large
      rw [← he]
      exact mul_le_mul hu.degree hgQ (by norm_num) ha
    let θ:=a*g/q
    have hθ:0≤θ:=div_nonneg (mul_nonneg ha (Nat.cast_nonneg _)) hq.le
    have hc:0≤1-θ:=sub_nonneg.mpr ((div_le_iff₀ hq).mpr (by simpa using (le_of_lt (lt_of_not_ge large))))
    have hh : (1-θ)*unit g ≤ h := by
      have hf:=hu.interpolation g hg hgsmall
      rw [max_eq_right hc] at hf
      exact hf
    calc
      T=θ*T+(1-θ)*T:=by ring
      _ ≤ θ*(q*d)+(1-θ)*(unit g*H+g) :=
        add_le_add (mul_le_mul_of_nonneg_left direct hθ)
          (mul_le_mul_of_nonneg_left (tariff hgsmall) hc)
      _ = a*(d*g)+((1-θ)*unit g)*H+(1-θ)*g := by
        dsimp only [θ]
        field_simp [hq.ne']; ring
      _ ≤ _ := by
        have hlast : (1-θ)*(g : ℚ) ≤ g := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (sub_le_self 1 hθ) (Nat.cast_nonneg (α:=ℚ) g)
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hh hH)) hlast
private theorem rated_component {unit : ℕ → ℚ} {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (tariff:CurveTariffFor unit M F) {a h globalCap localCap:ℚ} (hu:DiscountRate unit a h)
    (hmin:min globalCap localCap≤a) {I:Ideal Ambient} (geom:CurveGeometry I)
    (hglobal:(seedLength I:ℚ)≤globalCap) (hlocal:(seedLength I:ℚ)≤localCap)
    (hp:seedLength I < p) :
    ((Γ.filter (OnParent F I)).card : ℚ) ≤
      a*(seedLength I:ℚ)+h*(yLength I:ℚ)+seedLength I:=by
  let T:=Γ.filter (OnParent F I)
  let D:=seedLength I
  let H:=yLength I
  have hD:(0:ℚ)≤D:=Nat.cast_nonneg _
  have hH:(0:ℚ)≤H:=Nat.cast_nonneg _
  have ha:0≤a:=(show (0:ℚ)≤((p+1:ℕ):ℚ)/81 by positivity).trans hu.degree
  obtain ⟨f,hf,he,hpos,hd⟩:=K1_14_2_3_1.proof I (seed_slice geom)
  have hdq:(f.totalDegree:ℚ)≤D:=by exact_mod_cast hd
  by_cases hconst:DefinedOverConstants (seedImage I)
  · obtain ⟨Q, hQ, heQ⟩ := hconst
    have hdeg:f.totalDegree=Q.totalDegree:=equal_image_degree f hf.ne_zero Q (he.symm.trans heQ)
    obtain ⟨g,hg,hroot,hgD⟩:=projected_curve I Q (seed_slice geom) geom.2.2.2.2 hQ heQ
    have hgcap:g≤D:=(Nat.le_mul_of_pos_left g (hdeg ▸ hpos)).trans hgD
    have hp' : Module.finrank SeedField (RootSeedSection (rootImage I)) < p := by
      obtain ⟨_,Q', hQ', hQ'proj,_,hlen,_,_⟩:=hroot
      have heQ' : seedImage I=Ideal.span {MvPolynomial.map constantCoefficients Q'} := hQ'proj
      have hdeg' := equal_image_degree f hf.ne_zero Q' (he.symm.trans heQ')
      rw [hlen, ← hdeg', hdeg]
      exact hgD.trans_lt hp
    have hdir : (T.card : ℚ) ≤ ((p+1 : ℕ) : ℚ)*(Q.totalDegree : ℚ) := by
      have hcount:=direct_count F hf.ne_zero he (hd.trans_lt hp)
      rw [hdeg] at hcount
      exact_mod_cast hcount
    have htar (hgi : g ≤ 80) : (T.card : ℚ) ≤ unit g * H + g :=
      tariff T (Finset.filter_subset _ _) (rootImage I) g H hg hgi hroot hp'
        (fun _ hz => on_root (Finset.mem_filter.mp hz).2)
    have hfirst := interpolate unit g a h Q.totalDegree H T.card hg hH
      (Nat.cast_nonneg _) hu hdir htar
    have hgDq:(Q.totalDegree:ℚ)*g≤D:=by exact_mod_cast hgD
    have hgcapq:(g:ℚ)≤D:=by exact_mod_cast hgcap
    exact hfirst.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hgDq ha) le_rfl)
      hgcapq)
  · have hmov := moving_graph_count p f hf (he ▸ hconst)
      (T.image M.label) (mark_graph F he)
    rw [translated_card] at hmov
    have hcard:(T.card:ℚ)≤(f.totalDegree:ℚ)^2:=by exact_mod_cast hmov
    have hd0:(0:ℚ)≤f.totalDegree:=Nat.cast_nonneg _
    have har : (f.totalDegree : ℚ) ≤ a :=
      (le_min (hdq.trans hglobal) (hdq.trans hlocal)).trans hmin
    calc
      _≤(f.totalDegree:ℚ)^2:=hcard
      _≤a*D:=by rw [pow_two]; exact mul_le_mul har hdq hd0 ha
      _ ≤ _ := by
        have hn:=mul_nonneg hu.height hH
        linarith
theorem rated_curve_count_with {unit : ℕ → ℚ} {u del} {M : AnchorModel u del} {Γ}
    (F:AnchoredFamily M Γ) (tariff:CurveTariffFor unit M F)
    {a h globalCap:ℚ} (hu:DiscountRate unit a h) (C:CutCover)
    (hglobal:(C.cost 0:ℚ)≤globalCap)
    (hdegree:min globalCap (C.cost 0:ℚ)≤a) (hp:C.cost 0 < p) :
    ((curveMarks F C).card:ℚ)≤a*(C.cost 0:ℚ)+h*(C.cost 1:ℚ)+C.cost 0:=by
  have hsum : ∑ I ∈ C.curves,seedLength I=C.cost 0:=rfl
  have hsumH : ∑ I ∈ C.curves,yLength I=C.cost 1:=rfl
  have hcount (I : Ideal Ambient) (hI : I ∈ C.curves) :
      ((Γ.filter (OnParent F I)).card : ℚ) ≤
        a*(seedLength I:ℚ)+h*(yLength I:ℚ)+seedLength I:=by
    have hn:seedLength I≤C.cost 0:=hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hI
    have hq:(seedLength I:ℚ)≤(C.cost 0:ℚ):=by exact_mod_cast hn
    exact rated_component F tariff hu hdegree (C.geometric I hI) (hq.trans hglobal) hq (hn.trans_lt hp)
  calc
    _ ≤ ∑ I ∈ C.curves,((Γ.filter (OnParent F I)).card:ℚ):=union_card_le _ _
    _ ≤ ∑ I ∈ C.curves, (a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I) :=
      Finset.sum_le_sum hcount
    _=_:=by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum,hsum,hsumH]
theorem rated_curve_count {b u del} {M : AnchorModel u del} {Γ}
    (F : AnchoredFamily M Γ) (tariff : CurveTariff b M F)
    {a h globalCap : ℚ} (hu : RateOK (finish b) a h) (C : CutCover)
    (hglobal : (C.cost 0 : ℚ) ≤ globalCap)
    (hdegree : min globalCap (C.cost 0 : ℚ) ≤ a) (hp : C.cost 0 < p) :
    ((curveMarks F C).card : ℚ) ≤ a*(C.cost 0 : ℚ)+h*(C.cost 1 : ℚ)+C.cost 0 :=
  rated_curve_count_with (unit := curveUnit (finish b)) F tariff
    ⟨hu.degree,hu.height,hu.interpolation⟩ C hglobal hdegree hp

end
end HighCore82258_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace HighCore82258_3
noncomputable section
open HighCore82258 (AnchorModel AnchoredFamily K p)
open HighCore82258 (terminal Source InBand fees CurveTariff gradedLoss)
open HighCore82258PrefixHelpers (curveMarks mem_curveMarks direct_curve_count)
open P1_7_4 (Mass massQ_mono massQ_split massQ_nonneg dotQ_mono_mass dotQ_scale_add bill_bound flat_bill
  curveMarks direct_curve_count mem_curveMarks)
open K1_14 (Banks Jet jetAt)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (CutCover RowCaps mass)
open scoped Classical BigOperators
theorem cutWeight_nonneg (b : HighCore82258.Band) (fee : Fin 3) (i : ℕ) (k : Fin 4) :
    0≤ cutWeight b fee i k:=Nat.cast_nonneg _
theorem dot_cast (b : HighCore82258.Band) (fee : Fin 3) (i : ℕ) (S : Finset (Ideal Ambient)) :
    ((K1_14_2_2.dot (K1_14_2_2.weight (cutShape b i) fee) (mass S) : ℕ) : ℚ) =
      dotQ (cutWeight b fee i) (massQ S):=by
  simp only [dotQ,K1_14_2_2.dot,cutWeight,massQ,Nat.cast_sum,Nat.cast_mul]
theorem history_le_initial (b : HighCore82258.Band) (i : ℕ) (k : Fin 4) :
    history b i k≤ initialCap b k:=by
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact (min_le_left _ _).trans ih
open HighCore82258JointRank (rankMarks rank_and_loss_count_terminal)
structure FailureBooks {b u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {rows:Banks} {pairs:HighCore82258.Pairs b (effectiveHeight M).toNat rows} (R:Process pairs) (e:ℕ) (seedBook : Finset K) where
  loss:Finset K
  point:Finset K
  loss_le:loss.card≤gradedLoss b e
  loss_seed_le : loss.card + seedBook.card ≤ gradedLoss b e + initialE b
  point_le:point.card≤(fees b).point
  covers : ∀ i ≤ laterCount b, ∀ γ ∈ Γ, ∀ I ∈ R.lost i,
    OnParent F I γ→γ ∈ point ∨ γ ∈ loss
  rank_covers : jointRank b = true → ∀ γ ∈ Γ, ∀ I ∈ R.rankExit,
    OnParent F I γ→γ ∈ loss
private theorem properBin {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows:Banks} {pairs:HighCore82258.Pairs b (effectiveHeight M).toNat rows} (R:Process pairs)
    (src:Source b M F rows) (i:ℕ) :
    ∃ C : CutCover, (∀ fee, (C.cost fee : ℚ) ≤ dotQ (cutWeight b fee i) (massQ (R.lost i))) ∧
      ∀ γ ∈ Γ, (∃ I ∈ R.lost i, OnParent F I γ) →
        γ ∈ C.direct ∨ ∃ I ∈ C.curves,OnParent F I γ:=by
  have geom (I : Ideal Ambient) (hI : I ∈ R.lost i) :=
    (R.geometry I (R.tested_sub i (R.kept_sub i (R.lost_sub i hI)))).1
  have hj : (cutShape b i).J ≤ (cutShape b i).B := by
    by_cases hi:i < laterCount b
    · rw [cutShape, ite_eq_left hi]
      exact Nat.le_add_left _ _
    · rw [cutShape, ite_eq_right hi]
      exact R.sched.terminal_guard.ode.jb
  have cutter (I : Ideal Ambient) (hI : I ∈ R.lost i) :
      ∃ P : Jet, RowCaps P (cutShape b i) ∧ toJet P ∉ I ∧
        ∀ γ ∈ Γ,OnParent F I γ→jetAt P (M.label γ) (F.scalar γ)=0:=by
    by_cases hi:i < laterCount b
    · rw [cutShape, ite_eq_left hi]
      rw [Process.lost,dite_eq_left hi] at hI
      exact failed_pair src R.sched pairs (nextIndex i hi) (Finset.mem_filter.mp hI).2
    · rw [cutShape, ite_eq_right hi]
      rw [Process.lost,dite_eq_right hi] at hI
      obtain ⟨P, hP, hproper, hzero⟩ := failed_bank src (Or.inl rfl) R.sched.terminal_guard.pos
        (Finset.mem_filter.mp hI).2
      exact ⟨P,hP,hproper,fun γ hγ _ => hzero γ hγ⟩
  obtain ⟨C,hC,hcover⟩:=combined_cuts (R.lost i) (cutShape b i) hj geom cutter
  refine ⟨C,fun fee => ?_,hcover⟩
  rw [← dot_cast]
  exact (Nat.cast_le (α:=ℚ)).mpr (hC fee)
private theorem terminal_coordinate {S : Finset (Ideal Ambient)} {ed : ℕ}
    (hes:ed≤mass S 0) {w:Mass} (hw : ∀ k,0≤w k) :
    w 0*ed≤dotQ w (massQ S):=by
  have h : (ed : ℚ) ≤ massQ S 0 := by
    change (ed:ℚ)≤(mass S 0:ℚ)
    exact_mod_cast hes
  refine (mul_le_mul_of_nonneg_left h (hw 0)).trans ?_
  unfold dotQ
  exact Finset.single_le_sum (fun k _ => mul_nonneg (hw k) (massQ_nonneg S k)) (Finset.mem_univ 0)

theorem failure_books {b u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {rows:Banks} {pairs:HighCore82258.Pairs b (effectiveHeight M).toNat rows} (R:Process pairs)
    (src:Source b M F rows) (hw:InBand b (effectiveHeight M)) (est:PairedMass)
    (ledger:GradedLedger b) (e:ℕ)
    (hfinal:chargeDegree e≤mass R.final 0) (hcount:FixedCount) (tariff:(start b) < 7773→CurveTariff b M F)
    (seedBook : Finset K) (seedDegree : ℕ)
    (hparent : seedDegree + mass R.parents 2 ≤ initialCap b 2)
    (hseed : seedBook.card ≤ (p+1)*seedDegree + initialE b) :
    Nonempty (FailureBooks F R e seedBook):=by
  let n:=laterCount b+1
  choose C hcost hcover using properBin R src
  let points:=(Finset.range n).biUnion fun i => (C i).direct
  let lost:=(Finset.range n).biUnion fun i => curveMarks F (C i)
  have next : ∀ i < n, R.live (i+1) ⊆ R.live i :=
    fun _ hi => R.next_sub (Nat.le_of_lt_succ hi)
  have fail : ∀ i < n, R.lost i ⊆ R.live i \ R.live (i+1) :=
    fun _ hi => R.lost_diff (Nat.le_of_lt_succ hi)
  have caps : ∀ i < n, ∀ k, massQ (R.live i) k ≤ history b i k :=
    fun _ hi => R.cap_live est src hw (Nat.le_of_lt_succ hi)
  have sumD : (∑ i ∈ Finset.range n, ((C i).cost 0 : ℚ)) ≤ adjustedSeed b e := by
    have hb:=P1_7_4.bill_bound_terminal n (cutWeight b 0) (history b) R.live R.lost next fail caps
    have hh:R.live n=R.final:=by simp [n,Process.live]
    rw [hh] at hb
    have hx:=terminal_coordinate hfinal (P1_7_4.running_nonneg (cutWeight b 0) n)
    have hs:=Finset.sum_le_sum (fun i (_:i ∈ Finset.range n) => hcost i (0:Fin 3))
    unfold adjustedSeed seedCredit seedLimit
    dsimp only [n] at hb hx hs
    linarith only [hb,hx,hs]
  have hD (i : ℕ) (hi : i ≤ laterCount b) : ((C i).cost 0 : ℚ) ≤ adjustedSeed b e :=
    (Finset.single_le_sum (fun j _ => show 0 ≤ ((C j).cost 0 : ℚ) by positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).trans sumD
  have hp (i : ℕ) (hi : i ≤ laterCount b) : (C i).cost 0 < p :=
    (Nat.cast_lt (α:=ℚ)).mp ((hD i hi).trans_lt (ledger.seed_small e))
  have points_paid : (points.card : ℚ) ≤ (fees b).point := by
    let start : Mass :=
      ![(initialCap b 0:ℚ),(initialCap b 1:ℚ),(initialCap b 2:ℚ),(initialE b:ℚ)]
    have flat : ∀ i < n, ∀ k, massQ (R.live i) k ≤ start k := by
      intro i hi k
      have hc:=(caps i hi k).trans (history_le_initial b i k)
      fin_cases k
      · exact hc
      · exact hc
      · exact hc
      · exact hc.trans ((Nat.cast_le (α:=ℚ)).mpr R.sched.initial_e_ge)
    calc
      _ ≤ ∑ i ∈ Finset.range n, ((C i).cost 2 : ℚ) := by
        exact_mod_cast (Finset.card_biUnion_le : points.card ≤
          ∑ i ∈ Finset.range n,(C i).direct.card)
      _ ≤ ∑ i ∈ Finset.range n, dotQ (cutWeight b 2 i) (massQ (R.lost i)) :=
        Finset.sum_le_sum fun i _ => hcost i 2
      _ ≤ weightedBill n (cutWeight b 2) (fun _ => start) :=
        bill_bound n (cutWeight b 2) (fun _ => start) R.live R.lost next fail flat
      _=pointLimit b:=flat_bill _ _ _
      _≤_:=ledger.points
  have hsum : (lost.card : ℚ) ≤ ∑ i ∈ Finset.range n, ((curveMarks F (C i)).card : ℚ) := by
    exact_mod_cast (Finset.card_biUnion_le : lost.card ≤
      ∑ i ∈ Finset.range n,(curveMarks F (C i)).card)
  have per_bin (hd : start b < 7773) (a h : ℕ → ℚ)
    (hrate : ∀ i ≤ laterCount b, RateOK (finish b) (a i) (h i) ∧
      min (adjustedSeed b e) (adjustedLocal b e i)≤a i) (i:ℕ) (hi:i ∈ Finset.range n) :
      ((curveMarks F (C i)).card : ℚ) ≤
        dotQ (lossWeight b a h i) (massQ (R.lost i))+(C i).cost 0:=by
    have hi' : i≤laterCount b:=Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    obtain ⟨rate,ha⟩:=hrate i hi'
    have hsub : R.lost i ⊆ R.live i \ R.final := by
      intro I hI
      obtain ⟨hs,ht⟩:=Finset.mem_sdiff.mp (fail i (Finset.mem_range.mp hi) hI)
      exact Finset.mem_sdiff.mpr ⟨hs,fun hf => ht (R.final_live (i+1) hf)⟩
    have hsplit : dotQ (cutWeight b 0 i) (massQ (R.live i \ R.final)) +
        dotQ (cutWeight b 0 i) (massQ R.final) =
        dotQ (cutWeight b 0 i) (massQ (R.live i)):=by
      unfold dotQ
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [← mul_add,massQ_split (R.final_live i)]
    have hterm:=terminal_coordinate hfinal (cutWeight_nonneg b 0 i)
    have hcaps:=dotQ_mono_mass (cutWeight_nonneg b 0 i) (caps i (Finset.mem_range.mp hi))
    have hlost:=(hcost i 0).trans (dotQ_mono_mass (cutWeight_nonneg b 0 i) (massQ_mono hsub))
    have hloc : (C i).cost 0 ≤ adjustedLocal b e i := by
      unfold adjustedLocal
      linarith only [hsplit,hterm,hcaps,hlost]
    have hr := rated_curve_count F (tariff hd) rate (C i) (hD i hi')
      ((min_le_min le_rfl hloc).trans ha) (hp i hi')
    have a0:0≤a i:=(show (0:ℚ)≤((p+1:ℕ):ℚ)/81 by positivity).trans rate.degree
    calc
      _≤a i*((C i).cost 0:ℚ)+h i*((C i).cost 1:ℚ)+(C i).cost 0:=hr
      _ ≤ a i*dotQ (cutWeight b 0 i) (massQ (R.lost i)) +
            h i*dotQ (cutWeight b 1 i) (massQ (R.lost i))+(C i).cost 0 :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hcost i 0) a0)
          (mul_le_mul_of_nonneg_left (hcost i 1) rate.height)) le_rfl
      _=_:=by rw [dotQ_scale_add]; rfl
  let paid:=if jointRank b then lost ∪ rankMarks F R else lost
  have hj:jointRank b=true:=by cases b <;> rfl
  have loss_paid : (paid.card : ℚ) ≤ gradedLoss b e := by
    have hd:=jointRank_start b hj
    obtain ⟨a,h,hrate,hpay⟩:=ledger.discount e
    obtain ⟨ht0,ht1,hr,hs⟩:=ledger.rank_guard hj
    have hjoint := rank_and_loss_count_terminal F R est src hw hcount (rankTau b) (rankPivot b)
      ht0 ht1 hr hs (fun i => curveMarks F (C i)) (lossWeight b a h)
      (fun i => (C i).cost 0) (fun i hi => per_bin hd a h hrate i (Finset.mem_range.mpr hi))
    have hterm:=terminal_coordinate hfinal (P1_7_4.running_nonneg (lossWeights b a h) (lossCount b))
    simp only [paid,hj,ite_true]
    dsimp only at hjoint
    simp only [lossCount,lossWeights,lossHistory,lossOffset,hj,ite_true] at hpay hterm
    unfold mixedCredit at hpay
    simp only [lossCount,lossWeights,hj,ite_true] at hpay
    dsimp only [n] at sumD
    linarith only [hjoint,hpay,hterm,sumD]
  have loss_seed_paid : (paid.card : ℚ) + seedBook.card ≤ gradedLoss b e + initialE b := by
    have hd := jointRank_start b hj
    obtain ⟨a,h,hrate,hpay⟩ := ledger.discount e
    obtain ⟨ht0,ht1,hr,hs⟩ := ledger.rank_guard hj
    have hshare : ((p+1:ℕ):ℚ) ≤ HighCore82258JointRank.rankCharge b (rankTau b) (rankPivot b) 2 := by
      cases b <;> decide +kernel
    have hweights : ∀ k, 0 ≤ HighCore82258JointRank.rankCharge b (rankTau b) (rankPivot b) k := by
      intro k
      fin_cases k
      · exact le_rfl
      · exact hr
      · exact (by positivity : (0:ℚ) ≤ ((p+1:ℕ):ℚ)).trans hshare
      · exact le_rfl
    have hjoint := KoalaSeedParent.joint_rank_and_seed F R est src hw hcount (rankTau b) (rankPivot b)
      ht0 ht1 hr hs hweights hshare (fun i => curveMarks F (C i)) (lossWeight b a h)
      (fun i => (C i).cost 0) (fun i hi => per_bin hd a h hrate i (Finset.mem_range.mpr hi))
      seedDegree seedBook hparent hseed
    have hterm := terminal_coordinate hfinal (P1_7_4.running_nonneg (lossWeights b a h) (lossCount b))
    simp only [paid,hj,ite_true]
    dsimp only at hjoint
    simp only [lossCount,lossWeights,lossHistory,lossOffset,hj,ite_true] at hpay hterm
    unfold mixedCredit at hpay
    simp only [lossCount,lossWeights,hj,ite_true] at hpay
    dsimp only [n] at sumD
    simp only [stopIndex] at hpay hterm
    linarith only [hjoint,hpay,hterm,sumD]
  have hjoint_nat : paid.card + seedBook.card ≤ gradedLoss b e + initialE b := by
    exact_mod_cast loss_seed_paid
  refine ⟨⟨paid, points, (Nat.cast_le (α := ℚ)).mp loss_paid, hjoint_nat,
    (Nat.cast_le (α:=ℚ)).mp points_paid, ?_, ?_⟩⟩
  · intro i hi γ hγ I hI hm
    have hr:=Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
    rcases hcover i γ hγ ⟨I,hI,hm⟩ with hd | ⟨J,hJ,hj⟩
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨i,hr,hd⟩)
    · have hmem : γ ∈ lost :=
        Finset.mem_biUnion.mpr ⟨i,hr,mem_curveMarks (F:=F) hγ hJ hj⟩
      right
      by_cases h:jointRank b=true <;> simp only [paid,h,Bool.false_eq_true,ite_true,ite_false]
      · exact Finset.mem_union_left _ hmem
      · exact hmem
  · intro h γ hγ I hI hm
    simp only [paid,h,ite_true]
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ,I,hI,hm⟩)
end
end HighCore82258_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1500000
namespace HighCore82258_3
noncomputable section
open Polynomial
open HighCore82258 (K p AnchorModel AnchoredFamily)
open HighCore82258 (InBand stages terminal Source CurveTariff PrefixBooks PrefixInventory fees gradedLoss gradedLoss_le)
open K1_14 (Jet Banks seedHasse jetAt atX graphEval)
open K1_14_2 (Ambient ODE fixedAt)
open K1_14_2_2 (FixedPart ODECaps fixedOn dual mass)
open K1_14_3 (SeedCover Surface RowCaps NoMovingCommon)
open P0_10R.Bridge (surfaceOf parent_of_dual seed_side_bounded)
open scoped BigOperators Classical
def c1 : Prop :=
  ∀ (b : HighCore82258.Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    ScheduleOK b →
    ∀ P Q:Jet,P≠0→Q≠0→NoMovingCommon P Q →
    RowCaps P (stageAt b 0).free.shape→RowCaps Q (stageAt b 0).moving.shape →
    ∀ (A:FixedPart P (stageAt b 0).free.shape) (B:FixedPart Q (stageAt b 0).moving.shape),
    (∀ γ ∈ Γ,jetAt P (M.label γ) (F.scalar γ)=0 ∧ jetAt Q (M.label γ) (F.scalar γ)=0) →
    ∀ later:ℕ→Jet,
    (∀ i ∈ introIndices b, later i ≠ 0 ∧ RowCaps (later i) (stageAt b i).free.shape ∧
      ∀ j a, a ≤ (stageAt b i).reserve →
        ∀ γ ∈ Γ,jetAt (seedHasse j a (later i)) (M.label γ) (F.scalar γ)=0) →
    Nonempty (InitialCover M F b A.equation B.equation)
theorem paired_mass:PairedMass:=P1_7_4_2.proof
def c2 : Prop :=
  ∀ (b : HighCore82258.Band) u del (M : AnchorModel u del) Γ (F : AnchoredFamily M Γ),
    InBand b (effectiveHeight M) →
    ∀ B J:ℕ,ODEGuard B J →
    ∀ G:ODE,ODECaps G B J → ∀ T ⊆ Γ,
    (∀ γ ∈ T,fixedAt G (F.scalar γ)=0)→T.card≤fixedFee (finish b) B J
def c3:Prop := ∀ b:HighCore82258.Band,ScheduleOK b
def c4:Prop := ∀ b:HighCore82258.Band,GradedLedger b
private def fixedMarks {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (G:ODE):Finset K:=Γ.filter fun γ => fixedAt G (F.scalar γ)=0
private theorem fixed_paid (hcount : c2) {b u del} {M : AnchorModel u del} {Γ}
    (F:AnchoredFamily M Γ) (hw:InBand b (effectiveHeight M)) {B J:ℕ}
    (guard:ODEGuard B J) {G:ODE} (cap:ODECaps G B J) :
    (fixedMarks F G).card≤fixedFee (finish b) B J :=
  hcount b u del M Γ F hw B J guard G cap _ (Finset.filter_subset _ _)
    (fun _ hγ => (Finset.mem_filter.mp hγ).2)
private def fixedBook {b u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {rows:Banks} {pairs:HighCore82258.Pairs b (effectiveHeight M).toNat rows} (R:Process pairs):Finset K :=
  Finset.univ.biUnion fun i : StageIndex b =>
    fixedMarks F (R.fixed i).free.equation ∪ fixedMarks F (R.fixed i).moving.equation
private theorem fixed_book_paid (hcount : c2) {b u del} {M : AnchorModel u del} {Γ}
    (F:AnchoredFamily M Γ) (hw:InBand b (effectiveHeight M)) {rows:Banks}
    {pairs:HighCore82258.Pairs b (effectiveHeight M).toNat rows} (R:Process pairs) :
    (fixedBook F R).card≤(fees b).fixedODE:=by
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
      obtain ⟨ga,gb⟩:=R.sched.stage_guard i i.isLt
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add
        (fixed_paid hcount F hw ga.ode (R.fixed i).free.equation_caps)
        (fixed_paid hcount F hw gb.ode (R.fixed i).moving.equation_caps))
    _=fixedBudget b:=Fin.sum_univ_eq_sum_range price (stages b).length
    _≤_:=R.sched.fixed
private theorem mem_fixed_left {b u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {rows:Banks} {pairs:HighCore82258.Pairs b (effectiveHeight M).toNat rows} (R:Process pairs)
    (i:StageIndex b) {γ:K} (hγ:γ ∈ Γ) (hz:fixedAt (R.fixed i).free.equation (F.scalar γ)=0) :
    γ ∈ fixedBook F R :=
  Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ,hz⟩)⟩
private theorem mem_fixed_right {b u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    {rows:Banks} {pairs:HighCore82258.Pairs b (effectiveHeight M).toNat rows} (R:Process pairs)
    (i:StageIndex b) {γ:K} (hγ:γ ∈ Γ) (hz:fixedAt (R.fixed i).moving.equation (F.scalar γ)=0) :
    γ ∈ fixedBook F R :=
  Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ,hz⟩)⟩
private theorem floor_bound {n : ℕ} {r : ℚ} (h : (n : ℚ) ≤ r) : n ≤ r.floor.toNat := by
  have hi:(n:ℤ)≤ r.floor:=Rat.le_floor_iff.mpr (by exact_mod_cast h)
  simpa using Int.toNat_le_toNat hi
theorem of_children_seed_parent (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) : SeedParentC3 := by
  classical
  intro b u del M Γ F hw _ _ _ tariff rows src pairs
  let sched:=h3 b
  let zero:StageIndex b:=⟨0,sched.stages_pos⟩
  let P:=pairAt pairs zero
  let fixed:=fixedRows src pairs
  obtain ⟨ga,gb⟩:=sched.stage_guard 0 sched.stages_pos
  have hfree:=src.shape _ (free_listed zero) _ _ P.free_mem
  have hg:=src.shape _ (moving_listed zero) _ _ P.moving_mem
  let later (i:ℕ):Jet:=if hi:i < (stages b).length then (pairAt pairs ⟨i,hi⟩).free else 0
  obtain ⟨initial⟩ := h1 b u del M Γ F sched P.free P.moving P.free_ne P.moving_ne
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
  obtain ⟨losses⟩ := failure_books R src hw paired_mass (h4 b) f.natDegree
    ((chargeDegree_le f.natDegree).trans hdeg) h2 tariff seed initial.seed.curve.totalDegree
    initial.seed_parent hSeedFine
  obtain ⟨G, hgcap, hG⟩ := P1_7_4.rank_equation R.rankExit (fun _ hI => R.rank_geometry hI)
    (B:=rankB b) (J:=rankJ b) (floor_bound (R.rank_cap 1))
    (floor_bound (R.rank_cap 2))
  let contents:=Γ.filter fun γ => graphEval (M.label γ) initial.content=0
  let ords:=Γ.filter fun γ => atX (F.scalar γ) ∈ initial.ordinates
  let rank:=if jointRank b then ∅ else fixedMarks F G
  have hseed : seed.card ≤ (fees b).lowSeed := by
    have h := K1_14_3.seed_count (T := seed) label_inj.injOn initial.seed
      (initial.seed_le.trans_lt (sched.initial_small 2)) (fun _ hγ => (Finset.mem_filter.mp hγ).2)
    exact (h.trans (Nat.add_le_add (Nat.mul_le_mul_left _ initial.seed_le) initial.seed_points)).trans
      sched.low_seed
  have hcontents : contents.card ≤ (fees b).content := by
    let C:SeedCover:=⟨initial.content,initial.content_ne, ∅⟩
    have h := K1_14_3.seed_count (T := contents) label_inj.injOn C
      (initial.content_le.trans_lt sched.content_small)
      (fun _ hγ => Or.inl (Finset.mem_filter.mp hγ).2)
    have h' : contents.card ≤ (p+1)*initial.content.totalDegree := by
      simpa only [C,Finset.card_empty,Nat.add_zero] using h
    exact (h'.trans (Nat.mul_le_mul_left _ initial.content_le)).trans sched.content
  have hords : ords.card ≤ initialCap b 0 :=
    (Finset.card_le_card_of_injOn (fun γ => atX (F.scalar γ))
      (fun _ hγ => (Finset.mem_filter.mp hγ).2)
      (fun _ hγ _ hδ h => F.distinct (Finset.mem_filter.mp hγ).1 (Finset.mem_filter.mp hδ).1
        (K1_14_3.scalar_atX_injective h))).trans initial.ordinate_le
  have hlowJet : (ords ∪ rank).card ≤ (fees b).lowJet := by
    by_cases hj:jointRank b=true
    · have hfee := sched.low_jet
      simp only [hj,ite_true,Nat.add_zero] at hfee
      simpa only [rank,hj,ite_true,Finset.union_empty] using hords.trans hfee
    · have hfee := sched.low_jet
      simp only [hj,Bool.false_eq_true,ite_false] at hfee
      simpa only [rank, hj, Bool.false_eq_true, ite_false] using (Finset.card_union_le ords (fixedMarks F G)).trans
        ((Nat.add_le_add hords (fixed_paid h2 F hw sched.rank_guard hgcap)).trans hfee)
  have hLoss : losses.loss.card ≤ (fees b).loss :=
    losses.loss_le.trans (gradedLoss_le b f.natDegree)
  let books : PrefixBooks b :=
    ⟨losses.loss, losses.point, seed, ords ∪ rank, fixedBook F R, contents,
      hLoss,losses.point_le,hseed,hlowJet,fixed_book_paid h2 F hw R,hcontents⟩
  refine ⟨⟨⟨{
    books:=books
    parents:=parents
    geometric := ?_
    stage_pass := ?_
    terminal_pass := ?_
    covers := ?_ }, f,hf,losses.loss_le⟩,losses.loss_seed_le⟩⟩
  · intro q hq
    obtain ⟨I,_,rfl⟩:=Finset.mem_image.mp hq
    have hgeom:=R.geometry _ (initial_mem I)
    exact parent_of_dual hgeom.1 hgeom.2
      ((Finset.mem_filter.mp (R.final_sub I.2)).2 sched.stop_le)
  · intro q hq s hs hpositive
    obtain ⟨I,_,rfl⟩:=Finset.mem_image.mp hq
    obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp hs
    let j:StageIndex b:=⟨i,hi⟩
    have ht : stageAt b j = s := by
      simpa [j,stageAt,List.getElem?_eq_getElem hi] using he
    clear he
    subst s
    have htest:=(Finset.mem_filter.mp (R.kept_sub _ (R.final_sub I.2))).2.2
    have hj : 0 < j.val := by
      by_contra! hbad
      have hz:j.val=0:=Nat.eq_zero_of_le_zero hbad
      have hr:(stageAt b j).reserve=0:=by rw [hz,sched.zero]
      omega
    exact surface_pass (R.geometry _ (initial_mem I)).1.prime
      (htest j hj (by have hh:i < (HighCore82258.stages b).length:=hi; unfold laterCount; dsimp [j]; omega))
  · intro q hq
    obtain ⟨I,_,rfl⟩:=Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp I.2).2
  · intro γ hγ
    by_cases hpaid:γ ∈ books.union
    · exact Or.inl hpaid
    right
    have forbid_seed (h : γ ∈ seed) : False := hpaid (by
      simp only [PrefixBooks.union,books,Finset.mem_union]; tauto)
    have forbid_contents (h : γ ∈ contents) : False := hpaid (by
      simp only [PrefixBooks.union,books,Finset.mem_union]; tauto)
    have forbid_ords (h : γ ∈ ords) : False := hpaid (by
      simp only [PrefixBooks.union,books,Finset.mem_union]; tauto)
    have forbid_rank (h : γ ∈ rank) : False := hpaid (by
      simp only [PrefixBooks.union,books,Finset.mem_union]; tauto)
    have forbid_fixed (h : γ ∈ fixedBook F R) : False := hpaid (by
      simp only [PrefixBooks.union,books,Finset.mem_union]; tauto)
    have forbid_loss (h : γ ∈ losses.point ∨ γ ∈ losses.loss) : False := hpaid (by
      simp only [PrefixBooks.union,books,Finset.mem_union]; tauto)
    rcases initial.covers γ hγ with hz | ho | hc | ha | hb | ⟨I,hI,hm⟩
    · exact (forbid_seed (Finset.mem_filter.mpr ⟨hγ,hz⟩)).elim
    · exact (forbid_ords (Finset.mem_filter.mpr ⟨hγ,ho⟩)).elim
    · exact (forbid_contents (Finset.mem_filter.mpr ⟨hγ,hc⟩)).elim
    · exact (forbid_fixed (mem_fixed_left F R zero hγ ha)).elim
    · exact (forbid_fixed (mem_fixed_right F R zero hγ hb)).elim
    · have hclean : R.Clean I := fun j =>
        ⟨fun hj => forbid_fixed (mem_fixed_left F R j hγ (fixed_zero hm hj)),
          fun hj => forbid_fixed (mem_fixed_right F R j hγ (fixed_zero hm hj))⟩
      have hnotRank : I ∉ R.rankExit := by
        intro h
        by_cases hj:jointRank b=true
        · exact forbid_loss (Or.inr (losses.rank_covers hj γ hγ I h hm))
        · apply forbid_rank
          simp only [rank,hj,Bool.false_eq_true,ite_false]
          exact Finset.mem_filter.mpr ⟨hγ,fixed_zero hm (hG I h)⟩
      have hnotLost : ∀ i ≤ laterCount b, I ∉ R.lost i := fun i hi h =>
        forbid_loss (losses.covers i hi γ hγ I h hm)
      let J : ↥R.final:=⟨I,R.retains hI hclean hnotRank hnotLost⟩
      exact ⟨toSurface J,Finset.mem_image_of_mem _ (Finset.mem_attach _ _),on_surface _ hm⟩

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) : HighCore82258.GradedC3 := by
  intro b u del M Γ F hw hshift H hH tariff rows src pairs
  obtain ⟨J⟩ := of_children_seed_parent h1 h2 h3 h4 b u del M Γ F hw hshift H hH tariff rows src pairs
  exact ⟨J.toGradedInventory⟩

#print axioms SeedParentInventory.card_books
#print axioms of_children_seed_parent
end
end HighCore82258_3
end
section
namespace HighCore82258_3_1
noncomputable section
open HighCore82258 (AnchorModel AnchoredFamily)
open HighCore82258_3 (stageAt initialCap OnParent)
open P1_7_4_1 (SectionGeometry)
open K1_14 (Seeds graphEval)
open K1_14_2 (Ambient ODE fixedAt)
open K1_14_2_2 (Fits)
structure AffineCover {u del} {M : AnchorModel u del} {Γ} (F : AnchoredFamily M Γ)
    (b:HighCore82258.Band) (G H:ODE) where
  components:Finset (Ideal Ambient)
  geometry:SectionGeometry components
  fits:Fits components (initialCap b)
  content:Seeds
  content_ne:content≠0
  content_le:content.totalDegree≤(stageAt b 0).free.shape.U+(stageAt b 0).moving.shape.U
  covers : ∀ γ ∈ Γ, graphEval (M.label γ) content = 0 ∨
    fixedAt G (F.scalar γ) = 0 ∨ fixedAt H (F.scalar γ) = 0 ∨
      ∃ I ∈ components,OnParent F I γ
end
end HighCore82258_3_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
namespace HighCore82258_3_1
noncomputable section
open HighCore82258 (K p AnchorModel AnchoredFamily )
open HighCore82258_3 (ScheduleOK stageAt introIndices initialCap)
open P1_7_4 (sharedBound cornerBound)
open P1_7_4_1 (Stripped proper_cover collect ordinary_component_cover)
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open K1_14_3 (NoMovingCommon)
open K1_14_2_2_2_1 (extractOrdinary)
open scoped BigOperators Classical
open private gcd_caps multiset_prod_ne_zero distinct_le_degree seed_degree_mul
  atMark_prod_eq_zero jetAt_mul jetAt_ordinary from ProximityPrize.SubmissionLower.Fast051
open private sharedBound_zero P1_7_4_1_1.floor_bound from ProximityPrize.SubmissionLower.UpperBranch4
private theorem zero_ledger {b : HighCore82258.Band} (empty : (introIndices b).isEmpty = true)
    {x z:ℕ} (k:Fin 4)
    (hx:x≤ min (stageAt b 0).free.shape.U (stageAt b 0).moving.shape.U)
    (hz:z≤ min (stageAt b 0).free.shape.B (stageAt b 0).moving.shape.B)
    (hs:(stageAt b 0).free.shape.J≤(stageAt b 0).free.shape.B)
    (ht:(stageAt b 0).moving.shape.J≤(stageAt b 0).moving.shape.B) :
    residualBudget (afterGcd (stageAt b 0).free.shape x z)
      (afterGcd (stageAt b 0).moving.shape x z) k+ordinaryBudget x z k≤ initialCap b k:=by
  have h := P1_7_4_2.shared_le_corner (stageAt b 0).free.shape (stageAt b 0).moving.shape
    (r:=1) (m:=1) false k hx hz hs ht
  rw [sharedBound_zero] at h
  simpa only [initialCap,empty,ite_true] using P1_7_4_1_1.floor_bound h
theorem zero_cover {b : HighCore82258.Band} (sched : ScheduleOK b)
    (empty:(introIndices b).isEmpty=true)
    {u del} {M:AnchorModel u del} {Γ} (F:AnchoredFamily M Γ)
    {P Q:Jet} (hnc:NoMovingCommon P Q)
    {A:FixedPart P (stageAt b 0).free.shape} {B:FixedPart Q (stageAt b 0).moving.shape}
    (a:Stripped A) (b' : Stripped B)
    (hrows : ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 ∧
      jetAt Q (M.label γ) (F.scalar γ)=0) :
    Nonempty (AffineCover F b A.equation B.equation):=by
  classical
  let s:=(stageAt b 0).free.shape
  let t:=(stageAt b 0).moving.shape
  obtain ⟨gs,gt⟩:=sched.stage_guard 0 sched.stages_pos
  have hord (D : Jet) (hD : Irreducible D) (hda : D ∣ a.row) (hdb : D ∣ b'.row) :
      D.natDegree=0:=by
    by_contra hp
    obtain ⟨G, rfl⟩ := hnc D hD (hda.trans a.row_dvd) (hdb.trans b'.row_dvd)
      (Nat.pos_of_ne_zero hp)
    exact a.no_fixed G hD hda
  obtain ⟨N, L, T, hL, hT, hproper, hN⟩ :=
    extractOrdinary a.row b'.row a.row_ne b'.row_ne a.primitive hord
  let x:=ordinarySeedDegree N.prod
  let z:=N.prod.natDegree
  have hN0 : ∀ f ∈ N,f≠0:=fun f hf => (hN f hf).1.ne_zero
  have hF:=multiset_prod_ne_zero N hN0
  have hAc:RowCaps (C N.prod*L) s:=hL ▸ a.row_caps
  have hBc:RowCaps (C N.prod*T) t:=hT ▸ b'.row_caps
  obtain ⟨hx,hz,hcL⟩:=gcd_caps hF hproper.left_ne hAc
  obtain ⟨hx', hz', hcT⟩:=gcd_caps hF hproper.right_ne hBc
  obtain ⟨S, hgeom, hS, hcover⟩ :=
    proper_cover hproper (min_le_right _ _) (min_le_right _ _) hcL hcT
  have hs1 : ordinarySeedDegree (1 : Equation) = 0 := by
    rw [← K1_14_2_2_2_1.seedDegree_C]
    simpa only [C_1,MvPolynomial.totalDegree_one] using K1_14_2_2_2_1.seedDegree_seed (1:Seeds)
  have hseed : (∑ f ∈ N.toFinset, ordinarySeedDegree f) ≤ x :=
    distinct_le_degree ordinarySeedDegree hs1 (fun hf hg => seed_degree_mul hf hg) N hN0
  have hy : (∑ f ∈ N.toFinset, f.natDegree) ≤ z :=
    distinct_le_degree natDegree natDegree_one (fun hf hg => natDegree_mul hf hg) N hN0
  obtain ⟨U, hUgeom, hU, hUcover⟩ := collect N.toFinset
    (fun f => ordinaryBudget (ordinarySeedDegree f) f.natDegree) (fun f z R => atMark f z R=0)
    (fun f hf => ordinary_component_cover f (hN f (Multiset.mem_toFinset.mp hf)).1
      (hN f (Multiset.mem_toFinset.mp hf)).2
      (((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hf).trans hy).trans_lt
        (hz.trans_lt gs.ode.small)))
  refine ⟨{
    components:=S ∪ U
    geometry := ?_
    fits := ?_
    content:=a.content*b'.content
    content_ne:=mul_ne_zero a.content_ne b'.content_ne
    content_le:=(MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add a.content_le b'.content_le)
    covers := ?_ }⟩
  · intro I hI
    exact (Finset.mem_union.mp hI).elim (hgeom I) (hUgeom I)
  · intro k
    exact (sum_union_le (fun I => sectionDegree I k) _ _).trans
      ((Nat.add_le_add (hS k) ((hU k).trans (ordinary_sum _ _ _ hseed hy k))).trans
        (zero_ledger empty k (le_min hx hx') (le_min hz hz') gs.ode.jb gt.ode.jb))
  · intro γ hγ
    obtain ⟨hp,hq⟩:=hrows γ hγ
    rcases a.covers _ _ hp with h | h | ha
    · exact Or.inl (by rw [map_mul,h,zero_mul])
    · exact Or.inr (Or.inl h)
    rcases b'.covers _ _ hq with h | h | hb
    · exact Or.inl (by rw [map_mul,h,mul_zero])
    · exact Or.inr (Or.inr (Or.inl h))
    apply Or.inr ∘ Or.inr ∘ Or.inr
    by_cases hzero:atMark N.prod (M.label γ) (F.scalar γ)=0
    · obtain ⟨f, hf, hmark⟩ := atMark_prod_eq_zero hzero
      obtain ⟨I,hI,hon⟩:=hUcover f (Multiset.mem_toFinset.mpr hf) _ _ hmark
      exact ⟨I,Finset.mem_union_right _ hI,hon⟩
    · rw [hL, jetAt_mul, jetAt_ordinary, mul_eq_zero] at ha
      rw [hT,jetAt_mul,jetAt_ordinary,mul_eq_zero] at hb
      obtain ⟨I,hI,hon⟩:=hcover _ _ (ha.resolve_left hzero) (hb.resolve_left hzero)
      exact ⟨I,Finset.mem_union_left _ hI,hon⟩
end
end HighCore82258_3_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1400000
namespace HighCore82258_3_1
noncomputable section
open HighCore82258 (AnchorModel AnchoredFamily)
open HighCore82258_3 (stageAt introIndices initialCap ScheduleOK introAccount introJump introWeight degreeVector)
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
private theorem intro_components {b : HighCore82258.Band} (sched : ScheduleOK b)
    {P Q:Jet} (hQ:Q≠0) (hnc:NoMovingCommon P Q)
    (hQc:RowCaps Q (stageAt b 0).moving.shape) (later:ℕ→Jet)
    (rows : ∀ i ∈ introIndices b,later i≠0 ∧ RowCaps (later i) (stageAt b i).free.shape) :
    ∀ (is:List ℕ),(∀ i ∈ is,i ∈ introIndices b) →
    ∀ (D:Finset Jet) (cap:Fin 3→ℕ),IntroFactors P D→(∀ j,factorMass D j≤ cap j) →
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧
      (∀ k old,mass S k≤ introAccount b k is cap old+weightedDegree old D) ∧
      ∀ z R, (∀ i ∈ is, ∀ j a, a ≤ (stageAt b i).reserve →
        jetAt (seedHasse j a (later i)) z R=0) →
        jetAt Q z R=0→(∃ f ∈ D,jetAt f z R=0) → ∃ I ∈ S,OnJet I z R:=by
  classical
  intro is
  induction is with
  | nil =>
    intro _ D cap hD hcap
    let t:=(stageAt b 0).moving.shape
    have gt:=(sched.stage_guard 0 sched.stages_pos).2
    obtain ⟨S, hG, hS, hC⟩ := collect D
      (fun f k => factorTariff t k f+ordinaryBudget (factorDegree f 2) (factorDegree f 0) k)
      (fun f z R => jetAt f z R=0 ∧ jetAt Q z R=0)
      (terminal_piece hD hnc hQc gt.ode.jb gt.ode.small hQ)
    refine ⟨S,hG, ?_, ?_⟩
    · intro k old
      have hord : (![cap 0, cap 2, 2*cap 0*cap 2, cap 2*cap 2] : Fin 4 → ℕ) k =
          ordinaryBudget (cap 2) (cap 0) k:=by
        fin_cases k <;> try rfl
        change 2*cap 0*cap 2=2*cap 2*cap 0
        ring
      have hstep:=tariff_step (Finset.empty_subset D) cap old t k hcap
      simp only [Finset.sdiff_empty, weightedDegree, factorMass, Finset.sum_empty,
        mul_zero,Finset.sum_const_zero,Nat.add_zero] at hstep
      have hsum:=Nat.add_le_add hstep (ordinary_charge D cap hcap k)
      calc
        _ ≤ ∑ f ∈ D, (factorTariff t k f +
            ordinaryBudget (factorDegree f 2) (factorDegree f 0) k):=hS k
        _ ≤ (weightedDegree old D + introJump cap old t k) +
            ordinaryBudget (cap 2) (cap 0) k:=by
          rw [Finset.sum_add_distrib]
          exact hsum
        _ = _ := by
          simp only [introAccount,hord]
          ac_rfl
    · intro z R _ hq ⟨f, hf, hz⟩
      exact hC f hf z R ⟨hz,hq⟩
  | cons i is ih =>
    intro his D cap hD hcap
    have hi:=his i (List.mem_cons_self ..)
    have hrest : ∀ l ∈ is,l ∈ introIndices b:=fun l hl => his l (List.mem_cons_of_mem _ hl)
    let s:=(stageAt b i).free.shape
    let r:=(stageAt b i).reserve
    let T:=D.filter fun f => ∀ j a,a≤ r→f ∣ seedHasse j a (later i)
    have hT:T ⊆ D:=Finset.filter_subset _ _
    have gt:=(sched.stage_guard i (sched.intro_pos i hi).2).1
    obtain ⟨hrow,hc⟩:=rows i hi
    have hTcap (j : Fin 3) :
        factorMass T j≤ min (cap j) (degreeVector s j / (r+1)) :=
      le_min ((factorMass_mono hT j).trans (hcap j))
        (retained_mass (hD.mono hT) hrow hc gt.seed_small r
          (fun f hf => (Finset.mem_filter.mp hf).2) j)
    obtain ⟨laterCover, hLaterGeom, hLaterCap, hLater⟩ :=
      ih hrest T _ (hD.mono hT) hTcap
    obtain ⟨discard, hDiscardGeom, hDiscardCap, hDiscard⟩ :=
      collect (D \ T) (fun f k => factorTariff s k f)
        (fun f z R => jetAt f z R = 0 ∧
          ∀ j a,a≤ r→jetAt (seedHasse j a (later i)) z R=0) (by
        intro f hf
        obtain ⟨hfD,hfT⟩:=Finset.mem_sdiff.mp hf
        have hn : ¬ ∀ j a, a ≤ r → f ∣ seedHasse j a (later i) :=
          fun hall => hfT (Finset.mem_filter.mpr ⟨hfD,hall⟩)
        push Not at hn
        obtain ⟨j,a,ha,hd⟩:=hn
        have hirr:=(hD.factors f hfD).1
        obtain ⟨S, hG, hF, hC⟩ := proper_cover (irreducible_cut hirr hd)
          (own_J_le_B hirr.ne_zero) gt.ode.jb (own_caps f) (P1_7_4_1_2.proof s (later i) hc j a)
        exact ⟨S, hG, fun k => (hF k).trans_eq (residual_tariff f s gt.ode.jb k),
          fun z R hr => hC z R hr.1 (hr.2 j a ha)⟩)
    refine ⟨discard ∪ laterCover, ?_, ?_, ?_⟩
    · intro I hI
      exact (Finset.mem_union.mp hI).elim (hDiscardGeom I) (hLaterGeom I)
    · intro k old
      let w:=fun j => max (old j) (introWeight s k j)
      let newCap:=fun j => min (cap j) (degreeVector s j / (r+1))
      have hstep:=tariff_step hT cap old s k hcap
      calc
        _≤ mass discard k+mass laterCover k:=sum_union_le (fun I => sectionDegree I k) _ _
        _ ≤ (∑ f ∈ D \ T, factorTariff s k f) +
            (introAccount b k is newCap w+weightedDegree w T) :=
          Nat.add_le_add (hDiscardCap k) (hLaterCap k w)
        _ = introAccount b k is newCap w +
            ((∑ f ∈ D \ T,factorTariff s k f)+weightedDegree w T):=by ac_rfl
        _ ≤ introAccount b k is newCap w + (weightedDegree old D + introJump cap old s k) :=
          Nat.add_le_add_left hstep _
        _ = _ := by
          change _=(introJump cap old s k+introAccount b k is newCap w)+weightedDegree old D
          ac_rfl
    · intro z R hder hq ⟨f, hf, hz⟩
      by_cases h:f ∈ T
      · obtain ⟨I, hI, hMark⟩ := hLater z R
          (fun l hl => hder l (List.mem_cons_of_mem _ hl)) hq ⟨f,h,hz⟩
        exact ⟨I,Finset.mem_union_right _ hI,hMark⟩
      · obtain ⟨I, hI, hMark⟩ := hDiscard f (Finset.mem_sdiff.mpr ⟨hf, h⟩) z R
          ⟨hz,hder i (List.mem_cons_self ..)⟩
        exact ⟨I,Finset.mem_union_left _ hI,hMark⟩
theorem intro_cover {b : HighCore82258.Band} (sched : ScheduleOK b)
    (hne : ¬ (introIndices b).isEmpty=true)
    {u del} {M:AnchorModel u del} {Γ} (F:AnchoredFamily M Γ)
    {P Q:Jet} (hQ:Q≠0) (hnc:NoMovingCommon P Q)
    (hQc:RowCaps Q (stageAt b 0).moving.shape)
    {A:FixedPart P (stageAt b 0).free.shape} {B:FixedPart Q (stageAt b 0).moving.shape}
    (a:Stripped A)
    (hrows : ∀ γ ∈ Γ, jetAt P (M.label γ) (F.scalar γ) = 0 ∧
      jetAt Q (M.label γ) (F.scalar γ)=0)
    (later:ℕ→Jet)
    (hlater : ∀ i ∈ introIndices b, later i ≠ 0 ∧ RowCaps (later i) (stageAt b i).free.shape ∧
      ∀ j r, r ≤ (stageAt b i).reserve →
        ∀ γ ∈ Γ,jetAt (seedHasse j r (later i)) (M.label γ) (F.scalar γ)=0) :
    Nonempty (AffineCover F b A.equation B.equation):=by
  obtain ⟨D,hD,hcap,hroot⟩:=initial_factors a
  obtain ⟨S, hG, hFit, hC⟩ := intro_components sched hQ hnc hQc later
    (fun i hi => ⟨(hlater i hi).1,(hlater i hi).2.1⟩)
    (introIndices b) (fun _ hi => hi) D _ hD hcap
  refine ⟨{
    components:=S
    geometry:=hG
    fits:=fun k => ?_
    content:=a.content
    content_ne:=a.content_ne
    content_le:=a.content_le.trans (Nat.le_add_right _ _)
    covers := ?_ }⟩
  · rw [initialCap, ite_eq_right hne]
    simpa only [weightedDegree,zero_mul,Finset.sum_const_zero,Nat.add_zero] using hFit k (fun _ => 0)
  · intro γ hγ
    obtain ⟨hp,hq⟩:=hrows γ hγ
    rcases a.covers _ _ hp with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (hC _ _
        (fun i hi j r hr => (hlater i hi).2.2 j r hr γ hγ) hq (hroot _ _ h))))
end
end HighCore82258_3_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
namespace HighCore82258_3_1
noncomputable section
open HighCore82258 (K p AnchorModel AnchoredFamily)
open HighCore82258_3 (introIndices initialCap initialE ScheduleOK InitialCover OnParent)
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_2 K1_14_3_2 Polynomial
open K1_14_3 (SeedCover joinCovers joinCovers_degree joinCovers_points joinCovers_covers)
open scoped BigOperators Classical
open P1_7_4_1 (strip)
open private seed_projection from ProximityPrize.SubmissionLower.PortHighFinish
private theorem finish {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {b:HighCore82258.Band} {G H:ODE} (sched:ScheduleOK b) (C:AffineCover F b G H) :
    Nonempty (InitialCover M F b G H):=by
  classical
  let S:=C.components
  let noSeeds:=S.filter (fun I => sectionDegree I 0=0)
  let constY := S.filter (fun I => 0 < sectionDegree I 0 ∧
    ¬ Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl))
  let parents := S.filter (fun I => 0 < sectionDegree I 0 ∧
    Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl))
  have hparents (I : Ideal Ambient) (hi : I ∈ parents) : Active I := by
    obtain ⟨hI,ha,hy⟩:=Finset.mem_filter.mp hi
    obtain ⟨hprime,hdim,_,hf⟩:=C.geometry I hI
    have hsmall (k : Fin 4) : sectionDegree I k < p :=
      (length_le_mass hI k).trans_lt ((C.fits k).trans_lt (sched.initial_small k))
    exact ⟨hprime, hdim, hf.seeds, hf.ordinate, hf.mixed, hf.jets,
      ⟨ha,hsmall 0⟩,hsmall 2,hsmall 3,hy⟩
  have seed_exists (I : Ideal Ambient) (hi : I ∈ noSeeds) :
      ∃ D : SeedCover, D.curve.totalDegree ≤ sectionDegree I 2 ∧
        D.points.card≤ sectionDegree I 3 ∧ ∀ z R,OnJet I z R→D.Covers z:=by
    obtain ⟨hI,hz⟩:=Finset.mem_filter.mp hi
    obtain ⟨hprime,hdim,_,hf⟩:=C.geometry I hI
    exact seed_projection I hprime hdim hf hz
  let seedImage (I : Ideal Ambient) : SeedCover :=
    if hi:I ∈ noSeeds then Classical.choose (seed_exists I hi) else ⟨1,one_ne_zero, ∅⟩
  have hseedImage (I : Ideal Ambient) (hi : I ∈ noSeeds) :
      (seedImage I).curve.totalDegree≤ sectionDegree I 2 ∧
      (seedImage I).points.card≤ sectionDegree I 3 ∧
      ∀ z R,OnJet I z R→(seedImage I).Covers z:=by
    simpa only [seedImage,dite_eq_left hi] using Classical.choose_spec (seed_exists I hi)
  let imageCover:=joinCovers noSeeds seedImage
  let onY (I:Ideal Ambient):=(Γ.filter (OnParent F I)).image (fun γ => atX (F.scalar γ))
  let ordinates:=constY.biUnion onY
  have hy (I : Ideal Ambient) (hi : I ∈ constY) : (onY I).card ≤ sectionDegree I 0 := by
    obtain ⟨hI,ha,hy⟩:=Finset.mem_filter.mp hi
    apply le_trans (b:=1) _ ha
    apply Finset.card_le_one.mpr
    intro x hx y hy'
    obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨δ,hδ,rfl⟩:=Finset.mem_image.mp hy'
    exact ordinate_eq (C.geometry I hI).1 hy
      (Finset.mem_filter.mp hγ).2 (Finset.mem_filter.mp hδ).2
  refine ⟨{
    parents:=parents
    active:=hparents
    height_two:=fun I hi => (C.geometry I (Finset.mem_filter.mp hi).1).2.2.1
    mass_bound:=fits_mono (Finset.filter_subset _ _) C.fits
    seed:=imageCover
    seed_le := ?_
    seed_parent := ?_
    seed_points := ?_
    ordinates:=ordinates
    ordinate_le := ?_
    content:=C.content
    content_ne:=C.content_ne
    content_le:=C.content_le
    covers := ?_ }⟩
  · calc
      _ ≤ ∑ I ∈ noSeeds,(seedImage I).curve.totalDegree:=joinCovers_degree _ _
      _≤ mass noSeeds 2:=Finset.sum_le_sum fun I hi => (hseedImage I hi).1
      _≤ mass S 2:=mass_mono (Finset.filter_subset _ _) 2
      _≤_:=C.fits 2
  · have hseed : imageCover.curve.totalDegree ≤ mass noSeeds 2 :=
      (joinCovers_degree _ _).trans (Finset.sum_le_sum fun I hi => (hseedImage I hi).1)
    have hnp : Disjoint noSeeds parents := by
      rw [Finset.disjoint_left]
      intro I hn hp
      exact (Nat.ne_of_gt (Finset.mem_filter.mp hp).2.1) (Finset.mem_filter.mp hn).2
    exact ((Nat.add_le_add_right hseed _).trans
      (KoalaSeedParent.disjoint_mass (Finset.filter_subset _ _) (Finset.filter_subset _ _) hnp 2)).trans
      (C.fits 2)
  · calc
      _ ≤ ∑ I ∈ noSeeds,(seedImage I).points.card:=joinCovers_points _ _
      _≤ mass noSeeds 3:=Finset.sum_le_sum fun I hi => (hseedImage I hi).2.1
      _≤ mass S 3:=mass_mono (Finset.filter_subset _ _) 3
      _≤ initialCap b 3:=C.fits 3
      _≤_:=sched.initial_e_ge
  · calc
      _ ≤ ∑ I ∈ constY,(onY I).card:=Finset.card_biUnion_le
      _≤ mass constY 0:=Finset.sum_le_sum hy
      _≤ mass S 0:=mass_mono (Finset.filter_subset _ _) 0
      _≤_:=C.fits 0
  · intro γ hγ
    rcases C.covers γ hγ with h | h | h | ⟨I,hI,hon⟩
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · by_cases ha : sectionDegree I 0 = 0
      · have hmem : I ∈ noSeeds := Finset.mem_filter.mpr ⟨hI, ha⟩
        exact Or.inl (joinCovers_covers hmem ((hseedImage I hmem).2.2 _ _ hon))
      · have hpos := Nat.pos_of_ne_zero ha
        by_cases hy:Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨I,Finset.mem_filter.mpr ⟨hI,hpos,hy⟩,hon⟩))))
        · exact Or.inr (Or.inl (Finset.mem_biUnion.mpr
            ⟨I, Finset.mem_filter.mpr ⟨hI, hpos, hy⟩,
              Finset.mem_image.mpr ⟨γ,Finset.mem_filter.mpr ⟨hγ,hon⟩,rfl⟩⟩))
theorem proof : HighCore82258_3.c1 := by
  intro b u del M Γ F sched P Q hP hQ hnc hPc hQc A B hrows later hlater
  obtain ⟨a⟩:=strip hP hPc A
  by_cases hempty:(introIndices b).isEmpty=true
  · obtain ⟨tail⟩ := strip hQ hQc B
    obtain ⟨C⟩:=zero_cover sched hempty F hnc a tail hrows
    exact finish sched C
  · obtain ⟨C⟩ := intro_cover (B := B) sched hempty F hQ hnc hQc a hrows later hlater
    exact finish sched C
end
end HighCore82258_3_1
end
section
namespace HighCore82258_3_2
noncomputable section
open Polynomial Finset
open HighCore82258 (K agreement blockLength p)
open HighCore82258 (FixedWord degreeAt persistent_card_le section_incidence)
open HighCore82258_3 (fixedFee)
open P1_7_3 (persistentNodes hits_persistent)
open P1_7_4_3 (mix cast_mixed short_cut)
open K1_13 (Row extend)
open K1_13_5 (RegularAt)
open K1_14_3_6 (power totalCap topCap)
open private weights rho_at_endpoint from ProximityPrize.SubmissionLower.HighCore82258Family
open HighCore82258PrefixHelpers (section_bound fixed_bound)
private theorem word_subset {w T s d} (hw : FixedWord w T s d) {U : Finset K}
    (hU:U ⊆ T):FixedWord w U s d :=
  ⟨hw.distinct.mono hU,fun γ hγ => hw.degree γ (hU hγ),fun γ hγ => hw.hits γ (hU hγ)⟩
private def siteRatio (m : ℕ) : ℚ :=
  ((blockLength - m:ℕ):ℚ) / ((agreement - m:ℕ):ℚ)
private abbrev density:ℚ:=(blockLength:ℚ) / agreement
private def persistentTotal (d B:ℕ):ℚ:=siteRatio d+2*density*d*(B-1:ℕ)
private def persistentTop (d B J : ℕ) : ℚ :=
  min (persistentTotal d B) (density*d*(2*J-1:ℕ))
private theorem persistentTotal_nonneg (d B : ℕ) : 0 ≤ persistentTotal d B := by
  unfold persistentTotal siteRatio
  positivity
private theorem caps_weighted {d m B J : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 164514)
    (hm:m≤d) (hJ:0 < J) :
    let t:=max 1 (d-m)
    siteRatio m * totalCap t B ≤ persistentTotal d B ∧
      siteRatio m*topCap t B J≤persistentTop d B J:=by
  let t:=max 1 (d-m)
  have hd:d < agreement:=hh.trans_lt (by decide)
  obtain ⟨hMu,hLambda⟩:=weights hm hd (rho_at_endpoint hl hh)
  change siteRatio m≤ siteRatio d at hMu
  change siteRatio m*t≤density*d at hLambda
  have hRatio:0≤ siteRatio m:=by unfold siteRatio; positivity
  have hp : (power t : ℚ) ≤ 2 * (t : ℚ) := by
    exact_mod_cast (Nat.sub_le (2*t) 3)
  have hpow : siteRatio m * power t ≤ 2 * (density * d) := by
    have h:=mul_le_mul_of_nonneg_left hp hRatio
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
      (show topCap t B J≤totalCap t B from min_le_left _ _)) hRatio).trans htot
  · have hcap : topCap t B J ≤ t * (2*J-1) := by
      apply (min_le_right _ _).trans
      rw [show 2*J-1=2*(J-1)+1 by omega,Nat.mul_add,Nat.mul_one]
      exact Nat.add_le_add_right ((Nat.mul_le_mul_right _ (Nat.sub_le (2*t) 3)).trans_eq (by ring)) _
    calc
      _ ≤ siteRatio m * ((t * (2*J-1) : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcap) hRatio
      _=(siteRatio m*t)*(2*J-1:ℕ):=by push_cast; ring
      _≤_:=mul_le_mul_of_nonneg_right hLambda (Nat.cast_nonneg _)
private theorem persistent_regular {w T s d B J} (hw : FixedWord w T s d)
    (hl:131071≤d) (hh:d≤164514) (hJ:0 < J)
    (f:Row 2) (hf:Irreducible f) (hfpos:0 < f.degreeOf 1)
    (hb:f.totalDegree≤B) (hj:f.degreeOf 1≤J)
    (hreg : ∀ γ ∈ T,RegularAt 1 f (extend (s γ))) :
    (T.card : ℚ) ≤
      mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J)+1:=by
  have hpos : 0 ≤ mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) := by
    have ha:0≤persistentTotal d B:=persistentTotal_nonneg d B
    have hv:0≤persistentTop d B J:=le_min ha (by positivity)
    unfold mix
    positivity
  by_cases hsmall:T.card≤1
  · exact (show (T.card:ℚ)≤1 from by exact_mod_cast hsmall).trans (by linarith only [hpos])
  let sites:=persistentNodes w T s
  let t:=max 1 (d-sites.card)
  have hs:sites.card≤d:=persistent_card_le hw (by omega)
  have ht:t≤d:=max_le (by omega) (Nat.sub_le _ _)
  have htpos:0 < t:=(Nat.le_max_left _ _)
  have hsum : d ≤ sites.card + t := by
    have h:=Nat.le_max_right 1 (d-sites.card)
    omega
  have hd:d < agreement:=hh.trans_lt (by decide)
  have hdp:=hd.trans (by decide:agreement < p)
  have ha:0 < totalCap t B:=by simp [totalCap]
  have hv:0 < topCap t B J:=lt_min ha ((Nat.le_add_left _ _).trans' htpos)
  let D:=MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) (totalCap t B) (topCap t B J)
  have hcount := section_incidence hw D (fun i hi => by
    obtain ⟨cut,hc,he⟩:=short_cut f hdp ht hJ hb hj sites hsum w i
    exact section_bound hw f hf hfpos hreg ha hv i hi cut hc
      (fun γ hγ => he _ (hw.degree γ hγ) (hreg γ hγ) (fun _ hj => hits_persistent hγ hj)))
  have hgap : (0 : ℚ) < ((agreement-sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hratio : (T.card : ℚ) ≤ siteRatio sites.card * D := by
    unfold siteRatio
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hgap).mpr
    rw [mul_comm (T.card:ℚ)]
    exact_mod_cast hcount
  have hvle:topCap t B J≤totalCap t B:=min_le_left _ _
  dsimp only [D] at hratio
  rw [cast_mixed (f.degreeOf_le_totalDegree 1) hvle] at hratio
  obtain ⟨hcapA,hcapV⟩:=caps_weighted (B:=B) hl hh hs hJ
  refine hratio.trans ?_
  unfold mix
  calc
    _ = (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * (siteRatio sites.card * topCap t B J) +
        f.degreeOf 1*(siteRatio sites.card*totalCap t B):=by ring
    _ ≤ (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * persistentTop d B J +
        f.degreeOf 1*persistentTotal d B :=
      add_le_add (mul_le_mul_of_nonneg_left hcapV (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hcapA (Nat.cast_nonneg _))
    _≤_:=le_add_of_nonneg_right (by decide)
theorem proof : HighCore82258_3.c2 := by
  classical
  intro b u del M Γ F hband B J guard G hG T hT hroot
  let d:=degreeAt (finish b)
  have hdl:131071≤d:=Nat.le_add_right _ _
  have hdu:d≤164514:=Nat.add_le_add_left (HighCore82258.terminal_guards b).2.1 131071
  have hw : FixedWord M.word T F.scalar d := by
    refine ⟨F.distinct.mono hT, ?_, ?_⟩
    · intro γ hγ
      have hhi : (effectiveHeight M).toNat ≤ (finish b) := by
        simpa using Int.toNat_le_toNat hband.2
      exact (HighCore82258.degree_at_height M F γ (hT hγ)).trans (Nat.add_le_add_left hhi _)
    · intro γ hγ
      let mark:=F.mark γ (hT hγ)
      exact ⟨mark.bad.support,mark.bad.agreement,mark.scalar_hits⟩
  let ap:=persistentTotal d B
  let vp:=persistentTop d B J
  have ha:0≤ap:=persistentTotal_nonneg d B
  have hvp:0≤vp:=le_min ha (by positivity)
  have h := fixed_bound hw guard G hG hroot ap vp hvp (min_le_left _ _)
    (fun U hU => persistent_regular (word_subset hw hU) hdl hdu guard.jpos)
  let r:=mix B J ap vp
  have hceil : r ≤ (r.ceil.toNat : ℕ) := by
    have hz:r.ceil≤(r.ceil.toNat:ℤ):=Int.self_le_toNat _
    have hcast:(r.ceil:ℚ)≤(r.ceil.toNat:ℚ):=by exact_mod_cast hz
    exact Rat.le_ceil.trans hcast
  change T.card≤ r.ceil.toNat+B^2
  have hfinal : (T.card : ℚ) ≤ (r.ceil.toNat : ℚ) + (B^2 : ℕ) :=
    h.trans (add_le_add hceil le_rfl)
  exact_mod_cast hfinal
end
end HighCore82258_3_2
end
