import ProximityPrize.SubmissionLower.R6962B1RescueSource0
import ProximityPrize.SubmissionLower.R6962B1RescueSource1
import ProximityPrize.SubmissionLower.R6962B1RescueSource2
import ProximityPrize.SubmissionLower.R6962B1RescueSource3
import ProximityPrize.SubmissionLower.R6960RescueGeometryRates
import ProximityPrize.SubmissionLower.R6962B1TerminalReceipts

set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

-- ===================================================================
-- Section 1: Band 1 Rescue Source Assembly
-- ===================================================================
section B1RescueSourceAll
namespace Lower6962.B1.RescueSource
open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)
open Lower6962.B1 (helperBank helperCutoff helper_common_caps)

theorem checked (rect : Fin 4) (i : Fin 11) :
    B1Checked (bank rect i) (reserve i) (excess rect) (seed rect) := by
  fin_cases rect
  · exact rect0_checked i
  · exact rect1_checked i
  · exact rect2_checked i
  · exact rect3_checked i

theorem cutoff_fit {h : ℕ} (lo : 2360≤h) (hi : h≤2382) (rect : Fin 4) (i : Fin 11) :
    cutoff h rect i+2*h*(reserve i)<(bank rect i).shape.m*179808 :=
  (checked rect i).cutoff_fit lo hi

theorem rescue_row {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2360≤h) (hi : h≤2382) (rect : Fin 4) (i : Fin 11) {G : Jet}
    (irr : Irreducible G) (seeded : UsesSeed G) (slope : 1≤G.natDegree)
    (hs : seed rect≤seedDegree G) (hj : G.natDegree+excess rect≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word (bank rect i).shape (cutoff h rect i), ¬ G∣Q :=
  (checked rect i).avoids Crt word lo hi irr seeded slope hs hj

private theorem fits_rectangle {j u : ℕ} (loJ : 1≤j) (hiJ : j≤7)
    (loU : 1≤u) (hiU : u≤61) (mixed : 2≤j → u≤56) :
    ∃ rect : Fin 4, 1+excess rect≤j ∧ j≤jetCap rect ∧ seed rect≤u ∧ u≤seedCap rect := by
  by_cases hJ : 2≤j
  · refine ⟨3, ?_⟩
    change 2≤j ∧ j≤7 ∧ 1≤u ∧ u≤56
    exact ⟨hJ, hiJ, loU, mixed hJ⟩
  · by_cases hU : u≤1
    · refine ⟨0, ?_⟩
      change 1≤j ∧ j≤1 ∧ 1≤u ∧ u≤1
      omega
    · by_cases hU' : u≤6
      · refine ⟨1, ?_⟩
        change 1≤j ∧ j≤1 ∧ 2≤u ∧ u≤6
        omega
      · refine ⟨2, ?_⟩
        change 1≤j ∧ j≤1 ∧ 7≤u ∧ u≤61
        omega

theorem exceptional_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2360≤h) (hi : h≤2382) {G : Jet} (irr : Irreducible G) (seeded : UsesSeed G)
    (slope : 0<G.natDegree)
    (common : ∀ P ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣P) :
    ∃ rect : Fin 4, G.natDegree=1 ∧ jetDegree G≤jetCap rect ∧ seedDegree G≤seedCap rect ∧
      ∀ i : Fin 11, ∃ Q ∈ evaluated Crt word (bank rect i).shape (cutoff h rect i), ¬ G∣Q := by
  obtain ⟨linear,loJ,hiJ,loU,hiU,mixed⟩ := helper_common_caps Crt word lo hi irr seeded slope common
  obtain ⟨rect,lowJ,highJ,lowU,highU⟩ := fits_rectangle loJ hiJ loU hiU mixed
  refine ⟨rect,linear,highJ,highU,fun i => ?_⟩
  exact rescue_row Crt word lo hi rect i irr seeded (by omega) lowU (by rw [linear]; exact lowJ)

end Lower6962.B1.RescueSource
end B1RescueSourceAll

-- ===================================================================
-- Section 2: Band 1 Tariffs at endpointDegree = 133453
-- ===================================================================
section B1Tariffs
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Lower6962.B1.Tariffs
open Finset Polynomial ProximityPrize.Benchmark
open P1 (K I node p)
open K1_14 (Shape FX Seeds graphEval)
open K1_14_2 (Ambient OnJet ODE fixedAt RootSeedSection SeedField)
open K1_14_2_2 (ODECaps CutCover CurveGeometry)
open K1_14_2_3 (SeedSlice seedImage rootImage constantCoefficients DefinedOverConstants seedLength yLength
  on_root on_seed moving_graph_count seed_graph_count equal_image_degree union_card_le)
open K1_14_2_4 (taylorPower ordinateBound)
open P1_7_3 (persistentNodes hits_persistent section_bounds regular_chart persistent_taylor)
open P1_7_4 (ODEGuard)
open P1_7_4_3 (mix mix_eq cast_mixed short_cut)
open K1_13 (Row extend)
open K1_13_5 (RegularAt)
open K1_14_3_6 (power totalCap topCap)
open Lower6960.RescueGeometry (Model Family OnMark label_injective FixedWord persistent_card_le
  section_incidence section_bound fixed_bound siteRatio persistentTotal persistentTop density
  curveMarks mem_curveMarks)
open scoped Classical BigOperators

private abbrev agreement : ℕ := 179808
private abbrev blockLength : ℕ := 262144
abbrev b1EndpointDegree : ℕ := 133453

private theorem weights {s d : ℕ} (hs : s ≤ d) (hd : d < agreement)
    (haux : siteRatio d ≤ density * d) :
    siteRatio s ≤ siteRatio d ∧ siteRatio s * (max 1 (d-s) : ℕ) ≤ density * d := by
  have hAN : agreement ≤ blockLength := by decide
  have hsA := hs.trans_lt hd
  have hdN := hd.le.trans hAN
  have hsN := hs.trans hdN
  have hAs : (0 : ℚ) < (agreement : ℚ) - s := sub_pos.mpr (by exact_mod_cast hsA)
  have hAd : (0 : ℚ) < (agreement : ℚ) - d := sub_pos.mpr (by exact_mod_cast hd)
  have hmain : siteRatio s ≤ siteRatio d := by
    unfold siteRatio
    rw [Nat.cast_sub hsN, Nat.cast_sub hsA.le, Nat.cast_sub hdN, Nat.cast_sub hd.le]
    apply (div_le_div_iff₀ hAs hAd).mpr
    have h := mul_nonneg (sub_nonneg.mpr (show (s : ℚ) ≤ d by exact_mod_cast hs))
      (sub_nonneg.mpr (show (agreement : ℚ) ≤ blockLength by exact_mod_cast hAN))
    nlinarith only [h]
  refine ⟨hmain, ?_⟩
  by_cases heq : s = d
  · subst s; simpa using haux
  have hpos : 1 ≤ d - s := by omega
  rw [max_eq_right hpos]
  have hden : (0 : ℚ) < (agreement : ℚ) := by exact_mod_cast (by decide : 0 < agreement)
  have hfrac : ((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ) ≤ (d : ℚ) / agreement := by
    rw [Nat.cast_sub hs, Nat.cast_sub hsA.le]
    apply (div_le_div_iff₀ hAs hden).mpr
    have h := mul_nonneg (Nat.cast_nonneg s : (0 : ℚ) ≤ s) hAd.le
    nlinarith only [h]
  calc
    _ = ((blockLength-s : ℕ) : ℚ) * (((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ)) := by
      unfold siteRatio; ring
    _ ≤ (blockLength : ℚ) * ((d : ℚ) / agreement) :=
      mul_le_mul (by exact_mod_cast Nat.sub_le blockLength s) hfrac (by positivity) (by positivity)
    _ = density * d := by ring

private theorem rho_at_b1 : siteRatio b1EndpointDegree ≤ density * b1EndpointDegree := by
  decide +kernel

private theorem taylorPower_cast {g : ℕ} (hg : 0 < g) :
    (taylorPower g : ℚ) = 2 * (g : ℚ) - 1 := by
  unfold taylorPower
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl

private theorem regular_count {n g H : ℕ} {U : Finset K} {s : K → Polynomial K} {w}
    (A' : K1_14_2_4.RegularChart U s g H n) (hw : FixedWord w U s b1EndpointDegree) (hg : 0 < g) :
    (U.card : ℚ) ≤ (2 * density * b1EndpointDegree * (taylorPower g : ℚ) + siteRatio b1EndpointDegree) * H + 1 := by
  have hbound : 0 ≤ (2 * density * b1EndpointDegree * (taylorPower g : ℚ) + siteRatio b1EndpointDegree) * (H : ℚ) := by
    unfold siteRatio; positivity
  by_cases hc : U.card ≤ 1
  · have h : (U.card : ℚ) ≤ 1 := by exact_mod_cast hc
    linarith only [h, hbound]
  let sites := persistentNodes w U s
  let t := max 1 (b1EndpointDegree - sites.card)
  have hd : b1EndpointDegree < agreement := by decide
  have hs : sites.card ≤ b1EndpointDegree := persistent_card_le hw (by omega)
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left _ _)
  have htp : t < p := (max_le (by decide : 1 ≤ b1EndpointDegree) (Nat.sub_le _ _)).trans_lt (by decide)
  have hdt : b1EndpointDegree ≤ sites.card + t := by have h := le_max_right 1 (b1EndpointDegree - sites.card); omega
  obtain ⟨C, hreconstruct⟩ := persistent_taylor sites w hdt htp hg A'.equation A'.equation_degree
  let D := taylorPower t * (g * H) + ordinateBound t g * H
  have hsection := section_bounds (w := w) A' ht hw.distinct C fun γ hγ =>
    hreconstruct _ _ (hw.degree γ hγ) (fun _ hi => hits_persistent hγ hi) (A'.root γ hγ) (A'.simple γ hγ)
  have hinc : ((agreement - sites.card : ℕ) : ℚ) * U.card ≤ ((blockLength - sites.card : ℕ) : ℚ) * D := by
    exact_mod_cast section_incidence hw D hsection
  have hden : (0 : ℚ) < ((agreement - sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hcard : (U.card : ℚ) ≤ siteRatio sites.card * (D : ℚ) := by
    rw [siteRatio, div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    calc _ = ((agreement - sites.card : ℕ) : ℚ) * U.card := mul_comm _ _
         _ ≤ _ := hinc
  obtain ⟨hρ, hρt⟩ := weights hs hd rho_at_b1
  have hρb : siteRatio sites.card * (taylorPower t : ℚ) ≤ 2 * density * b1EndpointDegree := by
    have hb : (taylorPower t : ℚ) ≤ 2 * (t : ℚ) := by exact_mod_cast (Nat.sub_le (2*t) 1 : taylorPower t ≤ 2*t)
    have hρ0 : 0 ≤ siteRatio sites.card := by unfold siteRatio; positivity
    have h := mul_le_mul_of_nonneg_left hb hρ0
    nlinarith only [h, hρt]
  have hsum : g + (g - 1) = taylorPower g := by unfold taylorPower; omega
  have hD : D = (taylorPower t * taylorPower g + 1) * H := by rw [← hsum]; dsimp [D, ordinateBound]; ring
  refine hcard.trans (le_add_of_le_of_nonneg ?_ zero_le_one)
  calc
    _ = (siteRatio sites.card * (taylorPower t : ℚ) * (taylorPower g : ℚ) + siteRatio sites.card) * H := by
      rw [hD]; push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_right hρb (Nat.cast_nonneg _)) hρ) (Nat.cast_nonneg _)

theorem b1_fixed_word {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤2382) {T : Finset K} (hT : T⊆Γ) :
    FixedWord M.word T F.scalar b1EndpointDegree where
  distinct := F.distinct.mono hT
  degree := by
    intro γ hγ
    rcases (F.mark γ (hT hγ)).scalar_degree with zero | bound
    · simp [zero]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at bound
      change (F.scalar γ).natDegree≤133453
      omega
  hits := by
    intro γ hγ
    let A' := F.mark γ (hT hγ)
    exact ⟨A'.bad.support, A'.bad.agreement, A'.scalar_hits⟩

def curveUnit (g : ℕ) : ℚ :=
  (2*(g : ℚ)-1)*(1+2*density*b1EndpointDegree)+siteRatio b1EndpointDegree

def CurveTariff {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) : Prop :=
  ∀ T⊆Γ,∀ J g H,0<g → g≤80 →
    K1_14_2.SmallRootCurve J g H →
    Module.finrank SeedField (RootSeedSection J)<p →
    (∀ γ∈T,K1_14_2.OnRoot J (M.label γ) (F.scalar γ)) →
    (T.card : ℚ)≤curveUnit g*H+g

theorem curve_tariff {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤2382) : CurveTariff F := by
  intro T hT J g H hg hgLimit hcurve _ hmarks
  obtain ⟨U,hU,hexc,n,⟨A'⟩⟩ := regular_chart T M.label F.scalar J g H hg
    (hgLimit.trans_lt (by decide)) hcurve (label_injective M).injOn hmarks
  have hregular := regular_count A' (b1_fixed_word F hi (hU.trans hT)) hg
  have hgQ : (1 : ℚ)≤g := by exact_mod_cast hg
  have hexcQ : ((T \ U).card : ℚ)≤(taylorPower g : ℚ)*H := by exact_mod_cast hexc
  calc
    (T.card : ℚ) = ((T \ U).card : ℚ)+(U.card : ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _ ≤ (taylorPower g : ℚ)*H + ((2*density*b1EndpointDegree*(taylorPower g : ℚ)+siteRatio b1EndpointDegree)*H+1) :=
      add_le_add hexcQ hregular
    _ ≤ (taylorPower g : ℚ)*H + ((2*density*b1EndpointDegree*(taylorPower g : ℚ)+siteRatio b1EndpointDegree)*H+g) :=
      add_le_add le_rfl (add_le_add le_rfl hgQ)
    _ = curveUnit g*H+g := by rw [taylorPower_cast hg]; unfold curveUnit; ring

private theorem word_subset {w T s d} (hw : FixedWord w T s d) {U : Finset K}
    (hU : U ⊆ T) : FixedWord w U s d :=
  ⟨hw.distinct.mono hU, fun γ hγ => hw.degree γ (hU hγ), fun γ hγ => hw.hits γ (hU hγ)⟩

private theorem persistentTotal_nonneg (d B : ℕ) : 0 ≤ persistentTotal d B := by
  unfold persistentTotal siteRatio; positivity

private theorem caps_weighted {m B J : ℕ} (hm : m ≤ b1EndpointDegree) (hJ : 0 < J) :
    let t := max 1 (b1EndpointDegree - m)
    siteRatio m * totalCap t B ≤ persistentTotal b1EndpointDegree B ∧
      siteRatio m * topCap t B J ≤ persistentTop b1EndpointDegree B J := by
  let t := max 1 (b1EndpointDegree - m)
  obtain ⟨hMu, hLambda⟩ := weights hm (by decide : b1EndpointDegree < agreement) rho_at_b1
  have hRatio : 0 ≤ siteRatio m := by unfold siteRatio; positivity
  have hp : (power t : ℚ) ≤ 2 * (t : ℚ) := by exact_mod_cast (Nat.sub_le (2 * t) 3)
  have hpow : siteRatio m * power t ≤ 2 * (density * b1EndpointDegree) := by
    have h := mul_le_mul_of_nonneg_left hp hRatio
    linarith only [h, hLambda]
  have htot : siteRatio m * totalCap t B ≤ persistentTotal b1EndpointDegree B := by
    unfold totalCap persistentTotal
    push_cast
    have h2 : (2 * density * 133453 : ℚ) = 2 * (density * b1EndpointDegree) := by unfold b1EndpointDegree; push_cast; ring
    rw [mul_add, mul_one, ← mul_assoc, h2]
    exact add_le_add hMu (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  refine ⟨htot, ?_⟩
  unfold persistentTop
  apply le_min
  · exact (mul_le_mul_of_nonneg_left (by exact_mod_cast (show topCap t B J ≤ totalCap t B from min_le_left _ _)) hRatio).trans htot
  · have hcap : topCap t B J ≤ t * (2*J-1) := by
      apply (min_le_right _ _).trans
      rw [show 2*J-1 = 2*(J-1)+1 by omega, Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right ((Nat.mul_le_mul_right _ (Nat.sub_le (2*t) 3)).trans_eq (by ring)) _
    calc _ ≤ siteRatio m * ((t * (2*J-1) : ℕ) : ℚ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hcap) hRatio
         _ = (siteRatio m * t) * (2*J-1 : ℕ) := by push_cast; ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hLambda (Nat.cast_nonneg _)

private theorem persistent_regular {w T s B J} (hw : FixedWord w T s b1EndpointDegree)
    (hJ : 0 < J) (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hb : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) :
    (T.card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) (persistentTotal b1EndpointDegree B)
      (persistentTop b1EndpointDegree B J) + 1 := by
  have hpos : 0 ≤ mix f.totalDegree (f.degreeOf 1) (persistentTotal b1EndpointDegree B) (persistentTop b1EndpointDegree B J) := by
    have ha : 0 ≤ persistentTotal b1EndpointDegree B := persistentTotal_nonneg _ _
    have hv : 0 ≤ persistentTop b1EndpointDegree B J := le_min ha (by positivity)
    unfold mix; positivity
  by_cases hsmall : T.card ≤ 1
  · exact (show (T.card : ℚ) ≤ 1 from by exact_mod_cast hsmall).trans (by linarith only [hpos])
  let sites := persistentNodes w T s
  let t := max 1 (b1EndpointDegree - sites.card)
  have hs : sites.card ≤ b1EndpointDegree := persistent_card_le hw (by omega)
  have ht : t ≤ b1EndpointDegree := max_le (by decide) (Nat.sub_le _ _)
  have htpos : 0 < t := Nat.le_max_left _ _
  have hsum : b1EndpointDegree ≤ sites.card + t := by have h := Nat.le_max_right 1 (b1EndpointDegree - sites.card); omega
  have hd : b1EndpointDegree < agreement := by decide
  have hdp : b1EndpointDegree < p := by decide
  have ha : 0 < totalCap t B := by simp [totalCap]
  have hv : 0 < topCap t B J := lt_min ha ((Nat.le_add_left _ _).trans' htpos)
  let D := MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) (totalCap t B) (topCap t B J)
  have hcount := section_incidence hw D (fun i hi => by
    obtain ⟨cut, hc, he⟩ := short_cut f hdp ht hJ hb hj sites hsum w i
    exact section_bound hw f hf hfpos hreg ha hv i hi cut hc
      (fun γ hγ => he _ (hw.degree γ hγ) (hreg γ hγ) (fun _ hj => hits_persistent hγ hj)))
  have hgap : (0 : ℚ) < ((agreement - sites.card : ℕ) : ℚ) := by
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
  obtain ⟨hcapA, hcapV⟩ := caps_weighted (B := B) hs hJ
  refine hratio.trans ?_
  unfold mix
  calc
    _ = (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * (siteRatio sites.card * topCap t B J) +
        f.degreeOf 1 * (siteRatio sites.card * totalCap t B) := by ring
    _ ≤ (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * persistentTop b1EndpointDegree B J +
        f.degreeOf 1 * persistentTotal b1EndpointDegree B :=
      add_le_add (mul_le_mul_of_nonneg_left hcapV (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hcapA (Nat.cast_nonneg _))
    _ ≤ _ := le_add_of_nonneg_right (by decide)

def fixedFee (B J : ℕ) : ℕ :=
  (mix B J (persistentTotal b1EndpointDegree B) (persistentTop b1EndpointDegree B J)).ceil.toNat + B^2

theorem fixed_count {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤2382) {B J : ℕ} (guard : ODEGuard B J)
    (G : ODE) (caps : ODECaps G B J) {T : Finset K} (hT : T⊆Γ)
    (roots : ∀ γ∈T,fixedAt G (F.scalar γ)=0) :
    T.card≤fixedFee B J := by
  have hw := b1_fixed_word F hi hT
  let a := persistentTotal b1EndpointDegree B
  let v := persistentTop b1EndpointDegree B J
  have ha : 0≤a := persistentTotal_nonneg _ _
  have hv : 0≤v := le_min ha (by positivity)
  have h := fixed_bound hw guard G caps roots a v hv (min_le_left _ _)
    (fun U hU=>persistent_regular (word_subset hw hU) guard.jpos)
  let r := mix B J a v
  have hceil : r≤(r.ceil.toNat : ℕ) := by
    have hs : (r.ceil : ℚ)≤(r.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat r.ceil
    exact Rat.le_ceil.trans hs
  change T.card≤r.ceil.toNat+B^2
  have bound : (T.card : ℚ)≤(r.ceil.toNat : ℚ)+(B^2 : ℕ) := h.trans (add_le_add hceil le_rfl)
  exact_mod_cast bound

def lambda : ℚ := ((262144 : ℚ)/179808)*b1EndpointDegree
def mu : ℚ := ((262144-b1EndpointDegree : ℕ) : ℚ)/(179808-b1EndpointDegree : ℕ)
def tau : ℚ := 49/100

theorem fixedFee_eq (B J : ℕ) :
    fixedFee B J = (mix B J (mu+2*lambda*(B-1 : ℕ))
      (min (mu+2*lambda*(B-1 : ℕ)) (lambda*(2*J-1 : ℕ)))).ceil.toNat+B^2 := by
  have he : 2*density*(b1EndpointDegree : ℚ)=2*lambda := by unfold lambda density; ring
  have hl : density*(b1EndpointDegree : ℚ)=lambda := rfl
  have hm : siteRatio b1EndpointDegree=mu := rfl
  unfold fixedFee persistentTop persistentTotal
  rw [he,hl,hm]

structure RateOK (a h : ℚ) : Prop where
  degree : ((p+1 : ℕ) : ℚ)/81≤a
  height : 0≤h
  interpolation : ∀ g : ℕ,0<g → g≤80 →
    max 0 (1-a*g/((p+1 : ℕ) : ℚ))*curveUnit g≤h

private def heightTerms (a : ℕ) : List ℚ :=
  (List.range 80).map (fun i : ℕ =>
    let g := i+1
    max 0 (1-(a : ℚ)*(g : ℚ)/((p+1 : ℕ) : ℚ))*curveUnit g)

def heightBound (a : ℕ) : ℚ := (heightTerms a).foldr max 0

private theorem le_max_fold {q : ℚ} {terms : List ℚ} (mem : q∈terms) :
    q ≤ terms.foldr max 0 := by
  induction terms with
  | nil => simp at mem
  | cons a rest ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp mem with eq | h
    · exact eq.symm ▸ le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem height_spec (a g : ℕ) (pos : 0<g) (small : g≤80) :
    max 0 (1-(a : ℚ)*g/((p+1 : ℕ) : ℚ))*curveUnit g≤heightBound a := by
  apply le_max_fold
  unfold heightTerms
  apply List.mem_map.mpr
  refine ⟨g-1,List.mem_range.mpr (by omega),?_⟩
  dsimp only
  rw [Nat.sub_add_cancel (by omega : 1≤g)]

private theorem projected_curve : K1_14_2_3.c2 :=
  K1_14_2_3_2.of_children K1_14_2_3_2_1.proof K1_14_2_3_2_2.proof
private theorem seed_slice {I : Ideal Ambient} (h : CurveGeometry I) : SeedSlice I :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
private theorem mark_graph {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : seedImage I = Ideal.span {C}) :
    ∀ z ∈ (Γ.filter (OnMark F I)).image M.label, graphEval z C = 0 := by
  intro z hz
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
  apply on_seed (Finset.mem_filter.mp hγ).2
  rw [hC]
  exact Ideal.mem_span_singleton_self C
private theorem translated_card {u del} (M : Model u del) (T : Finset K) :
    (T.image M.label).card = T.card :=
  Finset.card_image_of_injective _ (fun _ _ hab => sub_left_inj.mp hab)
private theorem direct_count {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : C ≠ 0) (hI : seedImage I = Ideal.span {C})
    (hp : C.totalDegree < p) :
    (Γ.filter (OnMark F I)).card ≤ (p+1)*C.totalDegree := by
  have h := seed_graph_count C hC hp ((Γ.filter (OnMark F I)).image M.label) (mark_graph F hI)
  rwa [translated_card] at h
private theorem interpolate (g : ℕ) (a h d H T : ℚ) (hg : 0 < g)
    (hH : 0 ≤ H) (hd : 0 ≤ d) (hu : RateOK a h)
    (direct : T ≤ ((p+1 : ℕ) : ℚ)*d)
    (tariff : g ≤ 80 → T ≤ curveUnit g * H + g) :
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
      by_contra! h'
      have hgQ : (81 : ℚ) ≤ g := by exact_mod_cast Nat.succ_le_of_lt h'
      have he : q/81*81 = q := by ring
      apply large
      rw [← he]
      exact mul_le_mul hu.degree hgQ (by norm_num) ha
    let θ := a*g/q
    have hθ : 0 ≤ θ := div_nonneg (mul_nonneg ha (Nat.cast_nonneg _)) hq.le
    have hc : 0 ≤ 1-θ := sub_nonneg.mpr ((div_le_iff₀ hq).mpr (by simpa using (le_of_lt (lt_of_not_ge large))))
    have hh : (1-θ)*curveUnit g ≤ h := by
      have hf := hu.interpolation g hg hgsmall
      rw [max_eq_right hc] at hf
      exact hf
    calc
      T = θ*T+(1-θ)*T := by ring
      _ ≤ θ*(q*d)+(1-θ)*(curveUnit g*H+g) :=
        add_le_add (mul_le_mul_of_nonneg_left direct hθ)
          (mul_le_mul_of_nonneg_left (tariff hgsmall) hc)
      _ = a*(d*g)+((1-θ)*curveUnit g)*H+(1-θ)*g := by
        dsimp only [θ]; field_simp [hq.ne']; ring
      _ ≤ _ := by
        have hlast : (1-θ)*(g : ℚ) ≤ g := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (sub_le_self 1 hθ) (Nat.cast_nonneg (α := ℚ) g)
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hh hH)) hlast

private theorem rated_component {u del} {M : Model u del} {Γ} (F : Family M Γ)
    (tariff : CurveTariff F) {a h globalCap localCap : ℚ} (hu : RateOK a h)
    (hmin : min globalCap localCap ≤ a) {I : Ideal Ambient} (geom : CurveGeometry I)
    (hglobal : (seedLength I : ℚ) ≤ globalCap) (hlocal : (seedLength I : ℚ) ≤ localCap)
    (hp : seedLength I < p) :
    ((Γ.filter (OnMark F I)).card : ℚ) ≤
      a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
  let T := Γ.filter (OnMark F I)
  let D := seedLength I
  let H := yLength I
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
    have htar (hgi : g ≤ 80) : (T.card : ℚ) ≤ curveUnit g * H + g :=
      tariff T (Finset.filter_subset _ _) (rootImage I) g H hg hgi hroot hp'
        (fun _ hz => on_root (Finset.mem_filter.mp hz).2)
    have hfirst := interpolate g a h Q.totalDegree H T.card hg hH
      (Nat.cast_nonneg _) hu hdir htar
    have hgDq : (Q.totalDegree : ℚ)*g ≤ D := by exact_mod_cast hgD
    have hgcapq : (g : ℚ) ≤ D := by exact_mod_cast hgcap
    exact hfirst.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hgDq ha) le_rfl) hgcapq)
  · have hmov := moving_graph_count p f hf (he ▸ hconst) (T.image M.label) (mark_graph F he)
    rw [translated_card] at hmov
    have hcard : (T.card : ℚ) ≤ (f.totalDegree : ℚ)^2 := by exact_mod_cast hmov
    have hd0 : (0 : ℚ) ≤ f.totalDegree := Nat.cast_nonneg _
    have har : (f.totalDegree : ℚ) ≤ a := (le_min (hdq.trans hglobal) (hdq.trans hlocal)).trans hmin
    calc _ ≤ (f.totalDegree : ℚ)^2 := hcard
         _ ≤ a*D := by rw [pow_two]; exact mul_le_mul har hdq hd0 ha
         _ ≤ _ := by have hn := mul_nonneg hu.height hH; linarith

theorem rated_curve_count {u del} {M : Model u del} {Γ}
    (F : Family M Γ) (tariff : CurveTariff F)
    {a h globalCap : ℚ} (hu : RateOK a h) (C : CutCover)
    (hglobal : (C.cost 0 : ℚ) ≤ globalCap)
    (hdegree : min globalCap (C.cost 0 : ℚ) ≤ a) (hp : C.cost 0 < p) :
    ((curveMarks F C).card : ℚ) ≤ a*(C.cost 0 : ℚ)+h*(C.cost 1 : ℚ)+C.cost 0 := by
  have hsum : ∑ I ∈ C.curves, seedLength I = C.cost 0 := rfl
  have hsumH : ∑ I ∈ C.curves, yLength I = C.cost 1 := rfl
  have hcount (I : Ideal Ambient) (hI : I ∈ C.curves) :
      ((Γ.filter (OnMark F I)).card : ℚ) ≤ a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
    have hn : seedLength I ≤ C.cost 0 := hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hI
    have hq : (seedLength I : ℚ) ≤ (C.cost 0 : ℚ) := by exact_mod_cast hn
    exact rated_component F tariff hu hdegree (C.geometric I hI) (hq.trans hglobal) hq (hn.trans_lt hp)
  calc
    _ ≤ ∑ I ∈ C.curves, ((Γ.filter (OnMark F I)).card : ℚ) := union_card_le _ _
    _ ≤ ∑ I ∈ C.curves, (a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I) := Finset.sum_le_sum hcount
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum, hsum, hsumH]

end Lower6962.B1.Tariffs
end
end B1Tariffs

-- ===================================================================
-- Section 3: Band 1 Rescue Geometry (11 stages)
-- ===================================================================
section B1RescueGeom
noncomputable section
namespace Lower6962.B1.RescueGeometry
open Finset Polynomial
open K1 (I K p)
open K1_14 (L FX Shape Jet jetAt atX)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom ODE)
open K1_14_2_2 (RowCaps Active dual Fits mass mass_mono sectionDegree ordinateIncl ODECaps
  CutCover weight dot emptyCut joinCuts joinCuts_cost sum_dot)
open K1_14_2_2_2 (ordinate_eq length_le_mass)
open K1_14_2_2_2_1 (rowCaps_iff)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (Surface Parent SeedCover joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open P0_10R_1 (seed_projection section_bound component_height)
open P1_7_4 (ODEGuard Mass massQ dotQ dotQ_mono_mass massQ_mono dotQ_scale_add weightedBill bill_bound)
open P1_7_4_1 (irreducible_cut)
open HighCore82258_3 (envelope_caps)
open HighCore82268JointRank (fixed_fee_linear)
open Lower6960.DifferentialContact (Native)
open Lower6960.RescueGeometry (Model Family word OnMark label_injective contact_at_mark
  zero_of_contact proper_cut OnSurface beforeCuts curveMarks mem_curveMarks)
open Lower6962.B1 (helperBank helperCutoff)
open Lower6962.B1.RescueSource (jetCap seedCap)
private abbrev rBank := Lower6962.B1.RescueSource.bank
private abbrev rReserve := Lower6962.B1.RescueSource.reserve
private abbrev rCutoff := Lower6962.B1.RescueSource.cutoff
open Lower6962.B1.Tariffs (RateOK heightBound height_spec lambda mu tau fixedFee fixedFee_eq
  fixed_count curve_tariff rated_curve_count)
open scoped Classical BigOperators

def terminalShape : Shape := Lower6962.B1.TerminalReceipts.terminalBank.shape
def terminalCutoff : ℕ := terminalShape.m * 179808 - 1

def TerminalPass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (J : Ideal Ambient) : Prop :=
  ∀ P∈evaluated Crt w terminalShape terminalCutoff, toJet P∈J

def SurfacePass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (q : Surface) : Prop :=
  ∀ P∈evaluated Crt w terminalShape terminalCutoff, P∈q.asIdeal

def primeShape (rect : Fin 4) : Shape := ⟨0, jetCap rect, 1, seedCap rect⟩
def initialCap (rect : Fin 4) : Fin 4 → ℕ := pairCap (primeShape rect) (rBank rect 0).shape

theorem prime_shape_fit (rect : Fin 4) : (primeShape rect).J≤(primeShape rect).B := by
  fin_cases rect <;> decide
theorem initial_small (rect : Fin 4) (k : Fin 4) : initialCap rect k<K1.p := by
  fin_cases rect <;> fin_cases k <;> decide +kernel
theorem reserve_small (i : Fin 11) : rReserve i<K1.p := by
  fin_cases i <;> decide +kernel

private theorem initial_sections {G Q : Jet} {s t : Shape} (irr : Irreducible G)
    (avoid : ¬G∣Q) (gs : RowCaps G s) (qs : RowCaps Q t) (js : s.J≤s.B) (jt : t.J≤t.B) :
    ∃ A' : Finset (Ideal Ambient), P1_7_4_1.SectionGeometry A' ∧ Fits A' (pairCap s t) ∧
      (∀ J∈A',toJet G∈J ∧ toJet Q∈J) ∧
      ∀ z S,jetAt G z S=0 → jetAt Q z S=0 → ∃ J∈A',OnJet J z S := by
  have proper := irreducible_cut irr avoid
  obtain ⟨A',geom,cover⟩ := K1_14_2_2_2_3.proof _ _ proper
  obtain ⟨finite,fit⟩ := section_bound _ _ proper s t js jt gs qs A' geom
  refine ⟨A',?_,fit,fun J mem=>(geom J mem).2.2,cover⟩
  intro J mem
  obtain ⟨prime,dim,g,q⟩ := geom J mem
  exact ⟨prime,dim,component_height proper prime dim g q,finite J mem⟩

structure Initial {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (G Q₀ : Jet) (rect : Fin 4) where
  seeds : SeedCover
  seed_degree : seeds.curve.totalDegree ≤ initialCap rect 2
  seed_points : seeds.points.card ≤ initialCap rect 3
  ordinates : Finset FX
  ordinate_card : ordinates.card ≤ initialCap rect 0
  rankExit : Finset (Ideal Ambient)
  parents : Finset (Ideal Ambient)
  rank_geom : ∀ J∈rankExit,Active J ∧ ¬dual J
  parent_geom : ∀ J∈parents,Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet Q₀∈J
  disjoint : Disjoint rankExit parents
  fits : Fits (rankExit∪parents) (initialCap rect)
  covers : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 →
    seeds.Covers (M.label γ) ∨ atX (F.scalar γ)∈ordinates ∨
      (∃ J∈rankExit,OnMark F J γ) ∨ ∃ J∈parents,OnMark F J γ

private theorem classify {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {rect : Fin 4} {A' : Finset (Ideal Ambient)}
    (geom : P1_7_4_1.SectionGeometry A') (fit : Fits A' (initialCap rect))
    (rows : ∀ J∈A',toJet G∈J ∧ toJet Q₀∈J)
    (cover : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → ∃ J∈A',OnMark F J γ) :
    Nonempty (Initial F G Q₀ rect) := by
  let noSeeds := A'.filter (fun J=>sectionDegree J 0=0)
  let constY := A'.filter (fun J=>0<sectionDegree J 0 ∧ ¬Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let active := A'.filter (fun J=>0<sectionDegree J 0 ∧ Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let rank := active.filter (fun J=>¬dual J)
  let parents := active.filter dual
  have geomActive (J : Ideal Ambient) (mem : J∈active) : Active J ∧ J.height=2 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,height,finite⟩ := geom J hin
    have small (k : Fin 4) := (length_le_mass hin k).trans_lt ((fit k).trans_lt (initial_small rect k))
    exact ⟨⟨prime,dim,finite.seeds,finite.ordinate,finite.mixed,finite.jets,⟨seedPos,small 0⟩,small 2,small 3,ord⟩,height⟩
  have seed_exists (J : Ideal Ambient) (mem : J∈noSeeds) :
      ∃ C : SeedCover,C.curve.totalDegree≤sectionDegree J 2 ∧ C.points.card≤sectionDegree J 3 ∧
        ∀ z S,OnJet J z S → C.Covers z := by
    obtain ⟨hin,zero⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,_,finite⟩ := geom J hin
    exact seed_projection J prime dim finite zero
  let seedImage (J : Ideal Ambient) : SeedCover :=
    if mem : J∈noSeeds then Classical.choose (seed_exists J mem) else ⟨1,one_ne_zero,∅⟩
  have seed_spec (J : Ideal Ambient) (mem : J∈noSeeds) :
      (seedImage J).curve.totalDegree≤sectionDegree J 2 ∧ (seedImage J).points.card≤sectionDegree J 3 ∧
        ∀ z S,OnJet J z S → (seedImage J).Covers z := by
    simpa only [seedImage,dite_eq_left mem] using Classical.choose_spec (seed_exists J mem)
  let onY (J : Ideal Ambient) := (Γ.filter (OnMark F J)).image fun γ=>atX (F.scalar γ)
  have ordinate_bound (J : Ideal Ambient) (mem : J∈constY) : (onY J).card≤sectionDegree J 0 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    apply le_trans (b:=1) _ seedPos
    apply card_le_one.mpr
    intro y hy z hz
    obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hy
    obtain ⟨δ,hδ,rfl⟩ := mem_image.mp hz
    exact ordinate_eq (geom J hin).1 ord (mem_filter.mp hγ).2 (mem_filter.mp hδ).2
  refine ⟨⟨joinCovers noSeeds seedImage,?_,?_,constY.biUnion onY,?_,rank,parents,?_,?_,?_,?_,?_⟩⟩
  · exact (joinCovers_degree _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).1).trans ((mass_mono (filter_subset _ _) 2).trans (fit 2)))
  · exact (joinCovers_points _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).2.1).trans ((mass_mono (filter_subset _ _) 3).trans (fit 3)))
  · exact card_biUnion_le.trans ((sum_le_sum ordinate_bound).trans ((mass_mono (filter_subset _ _) 0).trans (fit 0)))
  · intro J mem; exact ⟨(geomActive J (mem_filter.mp mem).1).1,(mem_filter.mp mem).2⟩
  · intro J mem
    obtain ⟨hin,d⟩ := mem_filter.mp mem
    obtain ⟨act,ht⟩ := geomActive J hin
    exact ⟨act,d,ht,rows J (mem_filter.mp hin).1⟩
  · exact disjoint_left.mpr fun _ a b=>(mem_filter.mp a).2 (mem_filter.mp b).2
  · apply K1_14_2_2.fits_mono _ fit
    exact union_subset ((filter_subset _ _).trans (filter_subset _ _)) ((filter_subset _ _).trans (filter_subset _ _))
  · intro γ hγ zero
    obtain ⟨J,hin,on⟩ := cover γ hγ zero
    by_cases z : sectionDegree J 0=0
    · exact Or.inl (joinCovers_covers (mem_filter.mpr ⟨hin,z⟩) ((seed_spec J (mem_filter.mpr ⟨hin,z⟩)).2.2 _ _ on))
    · by_cases ord : Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl)
      · have mem : J∈active := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
        by_cases d : dual J
        · exact Or.inr (Or.inr (Or.inr ⟨J,mem_filter.mpr ⟨mem,d⟩,on⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨J,mem_filter.mpr ⟨mem,d⟩,on⟩))
      · exact Or.inr (Or.inl (mem_biUnion.mpr ⟨J,mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩,
          mem_image.mpr ⟨γ,mem_filter.mpr ⟨hγ,on⟩,rfl⟩⟩))

theorem initial_cover {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {rect : Fin 4} (irr : Irreducible G) (avoid : ¬G∣Q₀)
    (capsG : RowCaps G (primeShape rect)) (capsQ : RowCaps Q₀ (rBank rect 0).shape)
    (zero : ∀ γ∈Γ,jetAt Q₀ (M.label γ) (F.scalar γ)=0) : Nonempty (Initial F G Q₀ rect) := by
  obtain ⟨A',geom,fit,rows,cover⟩ := initial_sections irr avoid capsG capsQ (prime_shape_fit rect)
    (Lower6962.B1.RescueSource.shape_guards rect 0).2.1
  exact classify F geom fit rows (fun γ hγ hG => cover _ _ hG (zero γ hγ))

theorem Initial.rank_ode {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (initial : Initial F G Q₀ rect) :
    ∃ E : ODE, ODECaps E (mass initial.rankExit 2) (mass initial.rankExit 1) ∧
      ∀ γ∈Γ,(∃ J∈initial.rankExit,OnMark F J γ) → K1_14_2.fixedAt E (F.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation initial.rankExit initial.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩
  rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))

theorem history_from_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G : Jet} {rect : Fin 4} (irr : Irreducible G) (capsG : RowCaps G (primeShape rect))
    (Q : Fin 11→Jet) (init : Initial F G (Q 0) rect) (avoid : ∀ i,¬G∣Q i)
    (caps : ∀ i,RowCaps (Q i) (rBank rect i).shape)
    (contact : ∀ i γ,γ∈Γ → Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (rReserve i+1) (Q i)) :
    ∃ kept : ℕ→Finset (Ideal Ambient),
      kept 0=init.parents ∧ kept 1=init.parents ∧ Antitone kept ∧
      (∀ i : Fin 11,∀ n,i.val<n → ∀ J∈kept n,Native J (rReserve i+1) (Q i)) ∧
      (∀ i : Fin 11,∀ n,i.val<n → ∀ c : Fin 4,
        (rReserve i+1)*mass (kept n) c≤pairCap (primeShape rect) (rBank rect i).shape c) ∧
      ∀ i : Fin 11,∀ J∈kept i.val,J∉kept (i.val+1) →
        ∃ C : Jet,RowCaps C (rBank rect i).shape ∧ toJet C∉J ∧
          ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0 := by
  have on (J : Ideal Ambient) (mem : J∈init.parents) : Active J ∧ dual J ∧ toJet G∈J :=
    let h := init.parent_geom J mem; ⟨h.1,h.2.1,h.2.2.2.1⟩
  choose S sub pass bound cut using fun i =>
    Lower6960.ExceptionalStage.filter irr (avoid i) capsG (caps i) (prime_shape_fit rect)
      (Lower6962.B1.RescueSource.shape_guards rect i).2.1 init.parents on (rReserve i) (reserve_small i)
  let selected (i : Fin 11) := if i = 0 then init.parents else S i
  have first : selected 0=init.parents := by simp [selected]
  have rzero : rReserve 0=0 := by decide
  have contact_zero (J : Ideal Ambient) (mem : J∈init.parents) : Native J (rReserve 0+1) (Q 0) := by
    intro w hw; have hz : w.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp hz]; exact (init.parent_geom J mem).2.2.2.2
  have sel_pass (i : Fin 11) (J : Ideal Ambient) (mem : J∈selected i) : Native J (rReserve i+1) (Q i) := by
    by_cases zi : i = 0
    · subst i; exact contact_zero J (first ▸ mem)
    · exact pass i J (by simpa only [selected,ite_eq_right zi] using mem)
  have sel_bound (i : Fin 11) (c : Fin 4) :
      (rReserve i+1)*mass (selected i) c≤pairCap (primeShape rect) (rBank rect i).shape c := by
    by_cases zi : i = 0
    · subst i; rw [rzero, Nat.zero_add, first, one_mul]
      exact (mass_mono (subset_union_right (s₁:=init.rankExit) (s₂:=init.parents)) c).trans (init.fits c)
    · simpa only [selected,ite_eq_right zi] using bound i c
  let kept (n : ℕ) := init.parents.filter (fun J=>∀ i : Fin 11,i.val<n → J∈selected i)
  have spec {J n} : J∈kept n ↔ J∈init.parents ∧ ∀ i : Fin 11,i.val<n → J∈selected i := mem_filter
  refine ⟨kept,?_,?_,?_,?_,?_,?_⟩
  · ext J; simp [kept]
  · ext J; refine ⟨fun h=>(spec.mp h).1,fun h=>spec.mpr ⟨h,?_⟩⟩
    intro i hi; have zi : i = 0 := Fin.ext (by omega); subst i; exact first.symm ▸ h
  · intro n m h J mem; exact spec.mpr ⟨(spec.mp mem).1,fun i hi=>(spec.mp mem).2 i (hi.trans_le h)⟩
  · intro i n hi J mem; exact sel_pass i J ((spec.mp mem).2 i hi)
  · intro i n hi c
    exact (Nat.mul_le_mul_left _ (mass_mono (fun _ mem=>(spec.mp mem).2 i hi) c)).trans (sel_bound i c)
  · intro i J prev lost
    obtain ⟨root,prior⟩ := spec.mp prev
    have fail : J∉selected i := by
      intro pass; apply lost (spec.mpr ⟨root,?_⟩)
      intro j hj
      by_cases same : j=i
      · exact same ▸ pass
      · apply prior; have diff : j.val≠i.val := fun h=>same (Fin.ext h); omega
    have nz : i ≠ 0 := by intro z; subst i; exact fail (first.symm ▸ root)
    obtain ⟨C,cap,proper,zero⟩ := cut i J root (by simpa only [selected,ite_eq_right nz] using fail)
    exact ⟨C,cap,proper,fun γ hγ=>zero _ _ (contact i γ hγ)⟩

structure Run {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (G : Jet) where
  rect : Fin 4
  row : Fin 11→Jet
  row_mem : ∀ i,row i∈evaluated Crt (word M) (rBank rect i).shape (rCutoff M.overhead.toNat rect i)
  avoids : ∀ i,¬G∣row i
  initial : Initial F G (row 0) rect
  kept : ℕ→Finset (Ideal Ambient)
  start : kept 0=initial.parents
  intro_pass : kept 1=initial.parents
  antitone : Antitone kept
  passed : ∀ i : Fin 11,∀ n,i.val<n → ∀ J∈kept n,Native J (rReserve i+1) (row i)
  cap : ∀ i : Fin 11,∀ n,i.val<n → ∀ c : Fin 4,
    (rReserve i+1)*mass (kept n) c≤pairCap (primeShape rect) (rBank rect i).shape c
  cut : ∀ i : Fin 11,∀ J∈kept i.val,J∉kept (i.val+1) →
    ∃ C : Jet,RowCaps C (rBank rect i).shape ∧ toJet C∉J ∧
      ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0

theorem prepare {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2360≤M.overhead.toNat) (hi : M.overhead.toNat≤2382)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (common : Lower6960.PrefixRows.Common
      (evaluated Crt (word M) helperBank.shape (helperCutoff M.overhead.toNat)) G) :
    Nonempty (Run F Crt G) := by
  obtain ⟨rect,linear,jCap,uCap,rows⟩ := Lower6962.B1.RescueSource.exceptional_rows Crt (word M) lo hi
    common.1 common.2.2.1 common.2.1 common.2.2.2
  choose Q inside avoid using rows
  have capsG : RowCaps G (primeShape rect) := (rowCaps_iff G _).mpr ⟨jCap,linear.le,uCap⟩
  have caps (i : Fin 11) : RowCaps (Q i) (rBank rect i).shape := evaluated_shape Crt (word M) (inside i)
  have contact (i : Fin 11) (γ : K) (hγ : γ∈Γ) :
      Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (rReserve i+1) (Q i) :=
    contact_at_mark F Crt noPole residues (inside i) (Lower6962.B1.RescueSource.cutoff_fit lo hi rect i) γ hγ
  obtain ⟨ini⟩ := initial_cover F common.1 (avoid 0) capsG (caps 0) (fun γ hγ=>zero_of_contact (contact 0 γ hγ))
  obtain ⟨kept,start,intro_pass,anti,passed,cap,cut⟩ :=
    history_from_initial common.1 capsG Q ini avoid caps contact
  exact ⟨⟨rect,Q,inside,avoid,ini,kept,start,intro_pass,anti,passed,cap,cut⟩⟩

theorem Run.parent_geom {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {n : ℕ} {J : Ideal Ambient} (mem : J∈R.kept n) :
    Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet (R.row 0)∈J :=
  R.initial.parent_geom J (R.start ▸ R.antitone (Nat.zero_le n) mem)

def Run.final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    Finset (Ideal Ambient) := (R.kept 11).filter (TerminalPass Crt (word M))

def Run.live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) : Finset (Ideal Ambient) := if n<11 then R.kept (n+1) else R.final

def Run.lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) : Finset (Ideal Ambient) := R.live n \ R.live (n+1)

theorem Run.next_sub {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<11) : R.live (i+1)⊆R.live i := by
  by_cases hn : i+1<11
  · simp only [Run.live,ite_eq_left hi,ite_eq_left hn]; exact R.antitone (by omega)
  · have eq : i+1=11 := by omega
    rw [Run.live,Run.live,ite_eq_right hn,ite_eq_left hi,eq]; exact filter_subset _ _

theorem Run.live_active {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} {J : Ideal Ambient} (hi : i<11) (mem : J∈R.live i) : Active J := by
  rw [Run.live,ite_eq_left hi] at mem; exact (R.parent_geom mem).1

theorem Run.live_start {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    R.live 0=R.initial.parents := by
  rw [Run.live,ite_eq_left (by decide : 0<11)]; exact R.intro_pass

def rescueStage (rect : Fin 4) (i : Fin 11) : P1_7.Stage :=
  ⟨rReserve i,⟨Lower6960.HelperPrefix.timesShape (rReserve i+1) (primeShape rect),0,0⟩,rBank rect i⟩

def cutShape (rect : Fin 4) (i : ℕ) : Shape :=
  if hi : i+1<11 then HighCore82258_3.envelope (rescueStage rect ⟨i+1,hi⟩) else terminalShape

theorem cutShape_fit (rect : Fin 4) (i : ℕ) : (cutShape rect i).J≤(cutShape rect i).B := by
  unfold cutShape; split
  · exact Nat.le_add_left _ _
  · decide

theorem Run.marked_cutter {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} {J : Ideal Ambient} (hi : i<11) (mem : J∈R.lost i) :
    ∃ C : Jet, RowCaps C (cutShape R.rect i) ∧ toJet C∉J ∧
      ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0 := by
  obtain ⟨prev,lost⟩ := mem_sdiff.mp mem
  rw [Run.live,ite_eq_left hi] at prev
  by_cases hn : i+1<11
  · let j : Fin 11 := ⟨i+1,hn⟩
    rw [Run.live,ite_eq_left hn] at lost
    obtain ⟨C,cap,proper,zero⟩ := R.cut j J prev lost
    refine ⟨C,?_,proper,zero⟩
    rw [cutShape,dite_eq_left hn]
    apply envelope_caps (s:=rescueStage R.rect j)
    · exact Nat.mul_le_mul_left _ (prime_shape_fit R.rect)
    · exact (Lower6962.B1.RescueSource.shape_guards R.rect j).2.1
    · exact Or.inr cap
  · have eq : i+1=11 := by omega
    rw [Run.live,ite_eq_right hn] at lost
    have hf : ¬ TerminalPass Crt (word M) J := fun pass => lost (mem_filter.mpr ⟨eq ▸ prev,pass⟩)
    unfold TerminalPass at hf; push Not at hf
    obtain ⟨C,inside,proper⟩ := hf
    rw [cutShape,dite_eq_right hn]
    refine ⟨C,evaluated_shape Crt (word M) inside,proper,?_⟩
    intro γ hγ
    apply zero_of_contact (r:=0)
    exact contact_at_mark F Crt noPole residues inside (by simp only [Nat.mul_zero,Nat.add_zero]; decide +kernel) γ hγ

theorem Run.cutCover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} (hi : i<11) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape R.rect i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
  have oneCut (J : Ideal Ambient) (mem : J∈R.lost i) :
      ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape R.rect i) fee) (sectionDegree J)) ∧
        ∀ γ∈Γ,OnMark F J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
    obtain ⟨P,cap,proper,zero⟩ := R.marked_cutter noPole residues hi mem
    exact proper_cut F _ (cutShape_fit _ _) (R.live_active hi (mem_sdiff.mp mem).1) cap proper zero
  let C (J : Ideal Ambient) : CutCover := if mem : J∈R.lost i then Classical.choose (oneCut J mem) else emptyCut
  have spec (J : Ideal Ambient) (mem : J∈R.lost i) :
      (∀ fee,(C J).cost fee≤dot (weight (cutShape R.rect i) fee) (sectionDegree J)) ∧
        ∀ γ∈Γ,OnMark F J γ → γ∈(C J).direct ∨ ∃ Q∈(C J).curves,OnMark F Q γ := by
    simpa only [C,dite_eq_left mem] using Classical.choose_spec (oneCut J mem)
  refine ⟨joinCuts (R.lost i) C,?_,?_⟩
  · intro fee; exact (joinCuts_cost _ _ _).trans ((sum_le_sum fun J mem => (spec J mem).1 fee).trans_eq (sum_dot _ _))
  · rintro γ hγ ⟨J,mem,on⟩
    rcases (spec J mem).2 γ hγ on with point | ⟨Q,hQ,hmark⟩
    · exact Or.inl (mem_biUnion.mpr ⟨J,mem,point⟩)
    · exact Or.inr ⟨Q,mem_biUnion.mpr ⟨J,mem,hQ⟩,hmark⟩

theorem Run.retained_or_lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {J : Ideal Ambient} (mem : J∈R.initial.parents) :
    J∈R.final ∨ ∃ i<11,J∈R.lost i := by
  by_cases h : ∃ i<11,J∈R.lost i
  · exact Or.inr h
  · have live : ∀ n≤11,J∈R.live n := by
      intro n hn
      induction n with
      | zero => exact R.live_start.symm ▸ mem
      | succ n ih => by_contra absent; exact h ⟨n,by omega,mem_sdiff.mpr ⟨ih (by omega),absent⟩⟩
    exact Or.inl (by simpa [Run.live] using live 11 le_rfl)

theorem Run.terminal_surfaces {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,(∃ J∈R.final,OnMark F J γ) → ∃ q∈S,OnSurface F q γ := by
  let getGeom (J : R.final) := R.parent_geom (mem_filter.mp J.property).1
  let surface (J : R.final) := surfaceOf J.val (getGeom J).1.prime
  let S := R.final.attach.image surface
  refine ⟨S,?_,?_⟩
  · intro q hq; obtain ⟨J,_,rfl⟩ := mem_image.mp hq; have hJ := getGeom J
    exact ⟨parent_of_dual hJ.1 hJ.2.2.1 hJ.2.1,(mem_filter.mp J.property).2⟩
  · rintro γ _ ⟨J,hJ,on⟩; let q : R.final := ⟨J,hJ⟩
    refine ⟨surface q,mem_image.mpr ⟨q,mem_attach _ _,rfl⟩,?_⟩
    intro P mem; rw [←K1_14_2.eval_toJet]; exact RingHom.mem_ker.mp (on mem)

def initialMass (rect : Fin 4) : Mass := fun k => initialCap rect k

def history (rect : Fin 4) : ℕ → Mass
  | 0 => initialMass rect
  | n+1 => fun k =>
    if hn : n+1<11 then
      let i : Fin 11 := ⟨n+1,hn⟩
      min (history rect n k) ((pairCap (primeShape rect) (rBank rect i).shape k : ℚ)/(rReserve i+1))
    else history rect n k

theorem Run.initial_cap {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (n : ℕ) (k : Fin 4) : massQ (R.kept n) k ≤ initialMass R.rect k := by
  have sub : R.kept n ⊆ R.initial.parents := by simpa only [R.start] using (R.antitone (Nat.zero_le n) : R.kept n⊆R.kept 0)
  exact (Nat.cast_le (α:=ℚ)).mpr ((mass_mono (sub.trans subset_union_right) k).trans (R.initial.fits k))

theorem Run.history_cap {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i n : ℕ} (hi : i<11) (prior : i<n) (k : Fin 4) :
    massQ (R.kept n) k ≤ history R.rect i k := by
  induction i with
  | zero => exact R.initial_cap n k
  | succ i ih =>
    simp only [history,dite_eq_left hi]
    apply le_min (ih (by omega) (by omega))
    let j : Fin 11 := ⟨i+1,hi⟩
    change massQ (R.kept n) k ≤ (pairCap (primeShape R.rect) (rBank R.rect j).shape k : ℚ) / (rReserve j+1)
    have pos : (0 : ℚ)<rReserve j+1 := by positivity
    apply (le_div_iff₀ pos).mpr
    have bound := R.cap j n prior k
    rw [Nat.mul_comm] at bound; unfold massQ; exact_mod_cast bound

theorem Run.live_history {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<11) (k : Fin 4) : massQ (R.live i) k ≤ history R.rect i k := by
  rw [Run.live,ite_eq_left hi]; exact R.history_cap hi (Nat.lt_succ_self _) k

theorem Run.live_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    {i : ℕ} (hi : i<11) (k : Fin 4) : massQ (R.live i) k ≤ initialMass R.rect k := by
  rw [Run.live,ite_eq_left hi]; exact R.initial_cap _ k

def cutWeight (rect : Fin 4) (fee : Fin 3) (i : ℕ) : Mass := fun k => weight (cutShape rect i) fee k
def seedLimit (rect : Fin 4) : ℚ := weightedBill 11 (cutWeight rect 0) (history rect)
def pointLimit (rect : Fin 4) : ℚ := weightedBill 11 (cutWeight rect 2) (fun _ => initialMass rect)
def initialSeedLimit (rect : Fin 4) : ℕ := (K1.p+1)*initialCap rect 2+initialCap rect 3

theorem seed_limit_small (rect : Fin 4) : seedLimit rect < (K1.p : ℚ) := by
  fin_cases rect <;> decide +kernel

def Initial.seedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>ini.seeds.Covers (M.label γ))
def Initial.ordinateMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>atX (F.scalar γ)∈ini.ordinates)
def Initial.rankMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>∃ J∈ini.rankExit,OnMark F J γ)

theorem Initial.seed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) :
    ini.seedMarks.card ≤ initialSeedLimit rect := by
  have bound := K1_14_3.seed_count (T := ini.seedMarks) (label_injective M).injOn ini.seeds
    (ini.seed_degree.trans_lt (initial_small rect 2)) (fun _ hγ => (mem_filter.mp hγ).2)
  exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_left _ ini.seed_degree) ini.seed_points)

theorem Initial.ordinate_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) :
    ini.ordinateMarks.card ≤ initialCap rect 0 := by
  refine (card_le_card_of_injOn (fun γ=>atX (F.scalar γ)) (fun _ hγ=>(mem_filter.mp hγ).2) ?_).trans ini.ordinate_card
  intro γ hγ δ hδ eq; exact F.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1 (K1_14_3.scalar_atX_injective eq)

structure CutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) where
  cover : ℕ→CutCover
  cost : ∀ i<11,∀ fee,(cover i).cost fee ≤ dot (weight (cutShape R.rect i) fee) (mass (R.lost i))
  covers : ∀ i<11,∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) → γ∈(cover i).direct ∨ ∃ Q∈(cover i).curves,OnMark F Q γ

theorem Run.cutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (CutBooks R) := by
  have pick (i : ℕ) : ∃ C : CutCover,i<11 →
      (∀ fee,C.cost fee ≤ dot (weight (cutShape R.rect i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
    by_cases hi : i<11
    · obtain ⟨C,cap,cover⟩ := R.cutCover noPole residues hi; exact ⟨C,fun _=>⟨cap,cover⟩⟩
    · exact ⟨emptyCut,fun h=>(hi h).elim⟩
  choose C hC using pick; exact ⟨⟨C,fun i h=>(hC i h).1,fun i h=>(hC i h).2⟩⟩

theorem CutBooks.costQ {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) {i : ℕ} (hi : i<11) (fee : Fin 3) :
    ((C.cover i).cost fee : ℚ)≤dotQ (cutWeight R.rect fee i) (massQ (R.lost i)) := by
  have bound := (Nat.cast_le (α:=ℚ)).mpr (C.cost i hi fee)
  simpa only [cutWeight,dotQ,dot,massQ,Nat.cast_sum,Nat.cast_mul] using bound

theorem CutBooks.seed_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : (∑ i∈range 11,((C.cover i).cost 0 : ℚ))≤seedLimit R.rect :=
  (sum_le_sum fun _ h=>C.costQ (mem_range.mp h) 0).trans
    (bill_bound 11 _ _ R.live R.lost (fun _ hi=>R.next_sub hi) (fun _ _=>subset_rfl) (fun _ hi=>R.live_history hi))

def CutBooks.pointMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : Finset K := (range 11).biUnion fun i=>(C.cover i).direct

theorem CutBooks.point_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : (C.pointMarks.card : ℚ) ≤ pointLimit R.rect := by
  calc
    _ ≤ ∑ i∈range 11,((C.cover i).cost 2 : ℚ) := by
      exact_mod_cast (show C.pointMarks.card ≤ ∑ i∈range 11,(C.cover i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range 11,dotQ (cutWeight R.rect 2 i) (massQ (R.lost i)) :=
      sum_le_sum fun i h=>C.costQ (mem_range.mp h) 2
    _ ≤ _ := bill_bound 11 _ _ R.live R.lost (fun _ hi=>R.next_sub hi) (fun _ _=>subset_rfl) (fun _ hi=>R.live_initial hi)

private def Run.jointLive {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) : ℕ→Finset (Ideal Ambient)
  | 0 => R.initial.rankExit∪R.initial.parents
  | i+1 => R.live i
private def Run.jointLost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) : ℕ→Finset (Ideal Ambient)
  | 0 => R.initial.rankExit
  | i+1 => R.lost i

theorem Run.joint_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ R.initial.rankExit) + (∑ i∈range 11,dotQ (cut i) (massQ (R.lost i))) ≤
      weightedBill 12 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect)) := by
  have bill := bill_bound 12 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect))
    R.jointLive R.jointLost ?_ ?_ ?_
  · rw [show 12=11+1 by decide,sum_range_succ'] at bill
    simpa only [beforeCuts,Run.jointLost,add_comm] using bill
  · intro i hi; cases i with
    | zero => simpa only [Run.jointLive,R.live_start] using (subset_union_right : R.initial.parents⊆ R.initial.rankExit∪R.initial.parents)
    | succ i => exact R.next_sub (by omega)
  · intro i hi; cases i with
    | zero =>
      intro J mem; apply mem_sdiff.mpr; refine ⟨mem_union_left _ mem,?_⟩
      rw [Run.jointLive,R.live_start]; exact fun h=>(disjoint_left.mp R.initial.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k; cases i with
    | zero => exact (Nat.cast_le (α:=ℚ)).mpr (R.initial.fits k)
    | succ i => exact R.live_history (by omega) k

def degreeRates : List (List ℕ) :=
  [
    [257506322, 155594163, 122910301, 108995507, 108909283, 105574747, 106289737, 112744020, 125042751, 146870294, 134966668],
    [247842280, 148162364, 117387231, 105154536, 105182711, 103936843, 103936867, 108808377, 120450389, 141264273, 133453436],
    [217452578, 129961060, 115173004, 103937700, 103936843, 103936843, 103936922, 115173292, 115173292, 124258205, 129133767],
    [133865328, 81898553, 65560249, 65560205, 65560260, 65560184, 65560086, 65560238, 69859206, 75580878, 160033427]
  ]

def heightRates : List (List ℕ) :=
  [
    [1407106, 2472802, 3180780, 3611333, 3614325, 3730031, 3705221, 3481262, 3121195, 2618182, 2879054],
    [1465307, 2596312, 3335106, 3744612, 3743634, 3786865, 3786864, 3617826, 3249515, 2741040, 2912217],
    [1715057, 2988754, 3396978, 3786835, 3786865, 3786865, 3786862, 3396968, 3396968, 3143117, 3006884],
    [2903191, 4867146, 6124243, 6124247, 6124242, 6124249, 6124259, 6124244, 5734829, 5288810, 2399026]
  ]

def degreeRate (rect : Fin 4) (i : ℕ) : ℕ := (degreeRates.getD rect.val []).getD i 0
def heightRate (rect : Fin 4) (i : ℕ) : ℕ := (heightRates.getD rect.val []).getD i 0

private theorem checked_rates (rect : Fin 4) (i : Fin 11) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate rect i.val : ℚ) ∧
    min (seedLimit rect) (dotQ (cutWeight rect 0 i.val) (history rect i.val)) ≤ (degreeRate rect i.val : ℚ) ∧
    heightBound (degreeRate rect i.val) ≤ (heightRate rect i.val : ℚ) := by
  fin_cases rect <;> fin_cases i <;> decide +kernel

theorem rate_spec (rect : Fin 4) {i : ℕ} (hi : i<11) :
    RateOK (degreeRate rect i) (heightRate rect i) ∧
      min (seedLimit rect) (dotQ (cutWeight rect 0 i) (history rect i)) ≤ degreeRate rect i := by
  obtain ⟨base,degree,height⟩ := checked_rates rect ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def rankB (rect : Fin 4) : ℕ := initialCap rect 2+2
def rankJ (rect : Fin 4) : ℕ := initialCap rect 1+1
def pivot (rect : Fin 4) : ℚ := min (47843/5) (tau*rankB rect)
def rankWeight (rect : Fin 4) : Mass :=
  ![0,4*lambda*rankB rect*tau+mu-4*lambda*pivot rect,4*lambda*rankJ rect*(1-tau)+rankB rect,0]
def rankRound (rect : Fin 4) : ℚ :=
  rankWeight rect 1+2*rankWeight rect 2+2*lambda*pivot rect^2+1
def lossWeight (rect : Fin 4) (i : ℕ) : Mass :=
  fun k=>(degreeRate rect i : ℚ)*cutWeight rect 0 i k+(heightRate rect i : ℚ)*cutWeight rect 1 i k
def lossLimit (rect : Fin 4) : ℚ :=
  weightedBill 12 (beforeCuts (rankWeight rect) (lossWeight rect))
    (beforeCuts (initialMass rect) (history rect))+seedLimit rect+rankRound rect
def rescueFee (rect : Fin 4) : ℕ :=
  (lossLimit rect).ceil.toNat+(pointLimit rect).ceil.toNat+initialSeedLimit rect+initialCap rect 0

theorem rescue_fee_bound (rect : Fin 4) : rescueFee rect ≤ 112156563114883670 := by
  fin_cases rect <;> decide +kernel
theorem rank_guard (rect : Fin 4) :
    rankB rect < p ∧ 0≤rankWeight rect 1 ∧ 0≤rankWeight rect 2 := by
  fin_cases rect <;> decide +kernel

theorem Initial.rank_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) (hi : M.overhead.toNat≤2382) :
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
  have hJB : J≤B := max_le (by omega) (min_le_right _ _)
  have degree : E.natDegree≤B := by
    have top : E.coeff E.natDegree ≠ 0 := by rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree≠0 := by
      rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1,(le_min caps.2.1 degree).trans (le_max_right _ _),
    fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  obtain ⟨small,cJ,cB⟩ := rank_guard rect
  have guard : ODEGuard B J := ⟨le_max_left _ _, by omega, hJB, hB.trans_lt small⟩
  have count : ini.rankMarks.card≤fixedFee B J :=
    fixed_count F hi guard E ocaps (filter_subset _ _) (fun γ mem => roots γ (mem_filter.mp mem).1 (mem_filter.mp mem).2)
  have lin := fixed_fee_linear lambda mu tau (pivot rect) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤ rankWeight rect 1 * J + rankWeight rect 2 * B + 2*lambda*pivot rect^2+1 := by
    rw [fixedFee_eq]; exact lin
  have hJq : (J : ℚ)≤(mass S 1 : ℚ)+1 := by exact_mod_cast hJm
  have hBq : (B : ℚ)≤(mass S 2 : ℚ)+2 := by exact_mod_cast hBm
  have hjfee := mul_le_mul_of_nonneg_left hJq cJ
  have hbfee := mul_le_mul_of_nonneg_left hBq cB
  have hdot : dotQ (rankWeight rect) (massQ ini.rankExit) =
      rankWeight rect 1 * (mass S 1 : ℚ)+rankWeight rect 2 * (mass S 2 : ℚ) := by
    simp [dotQ,rankWeight,massQ,Fin.sum_univ_succ,S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [hdot,rankRound]; linarith only [hjfee,hbfee]

private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ)≤q) : a≤q.ceil.toNat := by
  have ceil_cast : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact_mod_cast bound.trans (Rat.le_ceil.trans ceil_cast)

theorem CutBooks.curve_bin_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hiM : M.overhead.toNat≤2382) {i : ℕ} (hi : i<11) :
    ((curveMarks F (C.cover i)).card : ℚ)≤
      dotQ (lossWeight R.rect i) (massQ (R.lost i))+((C.cover i).cost 0 : ℚ) := by
  have global : ((C.cover i).cost 0 : ℚ)≤seedLimit R.rect :=
    (single_le_sum (fun j _=>Nat.cast_nonneg (α:=ℚ) ((C.cover j).cost 0)) (mem_range.mpr hi)).trans C.seed_bill
  have localCap : ((C.cover i).cost 0 : ℚ)≤ dotQ (cutWeight R.rect 0 i) (history R.rect i) :=
    (C.costQ hi 0).trans (dotQ_mono_mass (fun _=>Nat.cast_nonneg _)
      (fun k=>(massQ_mono sdiff_subset k).trans (R.live_history hi k)))
  have prime : (C.cover i).cost 0 < p := by exact_mod_cast global.trans_lt (seed_limit_small R.rect)
  obtain ⟨ok,degree⟩ := rate_spec R.rect hi
  have count := rated_curve_count F (curve_tariff F hiM) ok (C.cover i)
    global ((min_le_min le_rfl localCap).trans degree) prime
  calc
    _ ≤ (degreeRate R.rect i : ℚ)*((C.cover i).cost 0 : ℚ) + (heightRate R.rect i : ℚ)*((C.cover i).cost 1 : ℚ)+((C.cover i).cost 0 : ℚ) := count
    _ ≤ (degreeRate R.rect i : ℚ)*dotQ (cutWeight R.rect 0 i) (massQ (R.lost i)) +
          (heightRate R.rect i : ℚ)*dotQ (cutWeight R.rect 1 i) (massQ (R.lost i)) + ((C.cover i).cost 0 : ℚ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (C.costQ hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (C.costQ hi 1) (Nat.cast_nonneg _))) le_rfl
    _ = _ := by rw [dotQ_scale_add]; rfl

def CutBooks.lossMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G} (C : CutBooks R) :
    Finset K := R.initial.rankMarks ∪ (range 11).biUnion (fun i=>curveMarks F (C.cover i))

theorem CutBooks.loss_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hi : M.overhead.toNat≤2382) : C.lossMarks.card ≤ (lossLimit R.rect).ceil.toNat := by
  apply card_round
  have cum : (C.lossMarks.card : ℚ) ≤ (R.initial.rankMarks.card : ℚ) +
      ∑ i∈range 11,((curveMarks F (C.cover i)).card : ℚ) := by
    exact_mod_cast (show C.lossMarks.card ≤ R.initial.rankMarks.card + ∑ i∈range 11,(curveMarks F (C.cover i)).card from
      (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have sum_cuts := sum_le_sum (fun _ mem=>C.curve_bin_count hi (mem_range.mp mem)) (s:=range 11)
  rw [sum_add_distrib] at sum_cuts
  have both := add_le_add (R.initial.rank_count hi) sum_cuts
  have joint := R.joint_bill (rankWeight R.rect) (lossWeight R.rect)
  have seed := C.seed_bill
  have total := cum.trans both
  unfold lossLimit; linarith only [total,joint,seed]

def CutBooks.paid {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G} (C : CutBooks R) :
    Finset K := ((C.lossMarks ∪ C.pointMarks) ∪ R.initial.seedMarks) ∪ R.initial.ordinateMarks

theorem CutBooks.paid_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hi : M.overhead.toNat≤2382) : C.paid.card≤rescueFee R.rect := by
  have h1 := card_union_le ((C.lossMarks∪C.pointMarks)∪R.initial.seedMarks) R.initial.ordinateMarks
  have h2 := card_union_le (C.lossMarks∪C.pointMarks) R.initial.seedMarks
  have h3 := card_union_le C.lossMarks C.pointMarks
  have rate := C.loss_count hi
  have points := card_round C.point_bill
  have seeds := R.initial.seed_count
  have ordinates := R.initial.ordinate_count
  unfold rescueFee CutBooks.paid; omega

theorem exceptional_prefix {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2360≤M.overhead.toNat) (hi : M.overhead.toNat≤2382)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (common : Lower6960.PrefixRows.Common
      (evaluated Crt (word M) helperBank.shape (helperCutoff M.overhead.toNat)) G) :
    ∃ (paid : Finset K) (S : Finset Surface),
      paid.card ≤ 112156563114883670 ∧
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨R⟩ := prepare F Crt lo hi noPole residues common
  obtain ⟨C⟩ := R.cutBooks noPole residues
  obtain ⟨S,geom,pass⟩ := R.terminal_surfaces
  refine ⟨C.paid,S,(C.paid_count hi).trans (rescue_fee_bound R.rect),geom,?_⟩
  intro γ hγ zero
  rcases R.initial.covers γ hγ zero with seed | ordinate | rank | ⟨J,mem,on⟩
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hγ,seed⟩)))
  · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨hγ,ordinate⟩))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hγ,rank⟩)))))
  · rcases R.retained_or_lost mem with final | ⟨i,hi',lost⟩
    · exact Or.inr (pass γ hγ ⟨J,final,on⟩)
    · rcases C.covers i hi' γ hγ ⟨J,lost,on⟩ with point | ⟨Q,hQ,hmark⟩
      · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨i,mem_range.mpr hi',point⟩))))
      · have cuts : γ∈(range 11).biUnion (fun i=>curveMarks F (C.cover i)) :=
          mem_biUnion.mpr ⟨i,mem_range.mpr hi',mem_curveMarks (F:=F) hγ hQ hmark⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ cuts))))

#print axioms exceptional_prefix
end Lower6962.B1.RescueGeometry
end
end B1RescueGeom

-- ===================================================================
-- Section 4: Band 1 Main Geometry (12 stages) + Combined Prefix
-- ===================================================================
section B1MainGeom
noncomputable section
namespace Lower6962.B1.MainGeometry
open Finset Polynomial
open K1 (I K p)
open K1_14 (L FX Shape Jet Seeds jetAt graphEval seedHasse atX)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet ODE fixedAt toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual Fits FixedPart fixedOn mass mass_mono sectionDegree sum_union_le
  ordinateIncl ODECaps orderOn CutCover weight dot emptyCut joinCuts joinCuts_cost sum_dot)
open K1_14_2_2_2 (ordinaryBudget ordinate_eq length_le_mass)
open K1_14_2_2R (chainCompatible)
open K1_14_3 (Surface Parent ProjectedProduct NoMovingCommon SeedCover joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open P0_10R_1 (seed_projection)
open P1_7_4 (ODEGuard Mass massQ dotQ dotQ_mono_mass massQ_mono dotQ_scale_add pairedCap weightedBill bill_bound
  degreeVector introJump introWeight)
open P1_7_4_1 (SectionGeometry IntroFactors factorDegree factorMass factorMass_mono factorTariff
  weightedDegree tariff_step ordinary_charge residual_tariff collect proper_cover own_J_le_B own_caps retained_mass
  initial_factors strip irreducible_cut terminal_piece)
open HighCore82258_3 (envelope_caps)
open HighCore82268JointRank (fixed_fee_linear)
open Lower6960.HelperPrefix (timesShape)
open Lower6960.MainPrefixSource (hasse_at_mark)
open Lower6960.DifferentialContact (Native)
open Lower6960.PrefixRows (Prepared)
open Lower6960.RescueGeometry (Model Family word OnMark label_injective contact_at_mark
  zero_of_contact proper_cut OnSurface beforeCuts curveMarks mem_curveMarks)
open Lower6962.B1 (helperBank helperCutoff bank reserve cutoff copies)
open Lower6962.B1.RescueGeometry (terminalShape terminalCutoff TerminalPass SurfacePass exceptional_prefix)
open Lower6962.B1.Tariffs (RateOK heightBound height_spec lambda mu tau fixedFee fixedFee_eq
  fixed_count curve_tariff rated_curve_count)
open scoped Classical BigOperators

def freeShape (i : Fin 12) : Shape := (bank i).shape
def movingShape (i : Fin 12) : Shape := timesShape (copies i) helperBank.shape
def stage (i : Fin 12) : P1_7.Stage := ⟨reserve i, bank i, ⟨movingShape i, 0, 0⟩⟩

def cutShape (i : ℕ) : Shape :=
  if hi : i+1<12 then HighCore82258_3.envelope (stage ⟨i+1,hi⟩) else terminalShape

theorem cutShape_fit (i : ℕ) : (cutShape i).J≤(cutShape i).B := by
  unfold cutShape; split
  · exact Nat.le_add_left _ _
  · decide

def introIndices : List (Fin 12) := [1, 2, 3, 4, 5, 6, 7]

def introAccount (k : Fin 4) : List (Fin 12) → (Fin 3→ℕ) → (Fin 3→ℕ) → ℕ
  | [], cap, old =>
      introJump cap old (movingShape 0) k + K1_14_2_2_2.ordinaryBudget (cap 2) (cap 0) k
  | i::rest, cap, old =>
      let s := freeShape i
      introJump cap old s k + introAccount k rest
        (fun j=>min (cap j) (degreeVector s j/(reserve i+1)))
        (fun j=>max (old j) (introWeight s k j))

def initialCap (k : Fin 4) : ℕ :=
  introAccount k introIndices (degreeVector (freeShape 0)) (fun _=>0)

theorem initial_small (k : Fin 4) : initialCap k < K1.p := by fin_cases k <;> decide +kernel
theorem free_ode_guard (i : Fin 12) : ODEGuard (freeShape i).B (freeShape i).J := by
  fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
theorem moving_ode_guard (i : Fin 12) : ODEGuard (movingShape i).B (movingShape i).J := by
  fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
theorem free_seed_small (i : Fin 12) : (freeShape i).U<K1.p := (Lower6962.B1.free_shape_guards i).2.2.2.1
theorem moving_seed_small (i : Fin 12) : (movingShape i).U<K1.p := by fin_cases i <;> decide +kernel
theorem reserve_small (i : Fin 12) : reserve i<K1.p := by fin_cases i <;> decide +kernel
theorem reserve_pos {i : Fin 12} (hi : 0 < i.val) : 0<reserve i := by
  have checks (j : Fin 12) : (j.val=0) ∨ 0<reserve j := by fin_cases j <;> decide +kernel
  exact (checks i).resolve_left (by omega)

structure Rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) where
  source : Fin 12→Jet
  out : Prepared source freeShape copies
    (evaluated Crt (word M) helperBank.shape (helperCutoff M.overhead.toNat)) helperBank.shape
  contact : ∀ i γ, γ∈Γ → jetAt out.exception (M.label γ) (F.scalar γ)≠0 →
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (out.helper^copies i)
  fixedFree : ∀ i, FixedPart (out.free i) (freeShape i)
  fixedMoving : ∀ i, FixedPart (out.helper^copies i) (movingShape i)

theorem rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2360≤M.overhead.toNat) (hi : M.overhead.toNat≤2382)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (Rows F Crt) := by
  obtain ⟨P,out,_,inside,_⟩ := Lower6962.B1.main_rows Crt (word M) lo hi
  refine ⟨⟨P,out,?_,?_,?_⟩⟩
  · intro i γ mem regular
    have fit : reserve i+1 ≤ copies i*11 := by unfold copies; omega
    refine out.contacts i _ (RingHom.ker_isPrime _) ?_ (reserve i+1) 11 fit ?_ ?_
    · intro van; apply regular; simpa only [K1_14_2.eval_toJet] using RingHom.mem_ker.mp van
    · exact contact_at_mark F Crt noPole residues (inside i) (Lower6962.B1.free_cutoff_fit lo hi i) γ mem
    · intro H hm
      have wh := Lower6962.B1.helper_width lo hi
      have width : helperCutoff M.overhead.toNat+2*M.overhead.toNat*10 < helperBank.shape.m*179808 :=
        Lower6960.FreeSource.buffered_fit helperBank 179808 _ 10 wh
      exact contact_at_mark F Crt noPole residues hm width γ mem
  · intro i; exact Classical.choice (K1_14_2_2_1.proof _ _ (out.free_ne i) (out.free_caps i))
  · intro i; exact Classical.choice (K1_14_2_2_1.proof _ _ (pow_ne_zero _ out.helper_ne) (out.moving_caps i))

def Rows.marks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Finset K :=
  Γ.filter (fun γ=>jetAt R.out.exception (M.label γ) (F.scalar γ)≠0)
def Rows.family {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Family M R.marks :=
  ⟨F.scalar,fun γ hγ=>F.mark γ (mem_filter.mp hγ).1,F.distinct.mono (filter_subset _ _)⟩
theorem Rows.main_contact {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 12) (γ : K) (mem : γ∈R.marks) :
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.helper^copies i) :=
  R.contact i γ (mem_filter.mp mem).1 (mem_filter.mp mem).2
theorem Rows.intro_tests {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 12) (j : Fin 2) (a : ℕ) (ha : a≤reserve i) (γ : K) (mem : γ∈R.marks) :
    jetAt (seedHasse j a (R.out.free i)) (M.label γ) (R.family.scalar γ)=0 :=
  hasse_at_mark (R.main_contact i γ mem).1 j a ha (ha.trans_lt (reserve_small i))
def Rows.Passes {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 12) (J : Ideal Ambient) : Prop :=
  orderOn J (R.out.free i) (reserve i+1) ∧
  orderOn J (R.out.helper^copies i) (reserve i+1) ∧ chainCompatible (R.out.free i) (R.out.helper^copies i) J
theorem Rows.failed_cut {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 12) {J : Ideal Ambient} (active : Active J) (dualJ : dual J) (fail : ¬R.Passes i J) :
    ∃ C : Jet,(RowCaps C (freeShape i) ∨ RowCaps C (movingShape i)) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  rcases Lower6960.PrefixStage.order_or_cut active dualJ (reserve_small i) (R.out.free_caps i) (R.out.moving_caps i)
    (pow_ne_zero _ R.out.helper_ne) (moving_ode_guard i).jpos with passes | ⟨C,cap,proper,zero⟩
  · exact (fail passes).elim
  · refine ⟨C,cap,proper,?_⟩
    intro γ hγ on; obtain ⟨free,moving⟩ := R.main_contact i γ hγ; exact zero _ _ on free moving

private theorem intro_components
    {P Q : Jet} (hQ : Q ≠ 0) (hnc : NoMovingCommon P Q)
    (hQc : RowCaps Q (movingShape 0)) (later : Fin 12 → Jet)
    (rows : ∀ i, later i ≠ 0 ∧ RowCaps (later i) (freeShape i)) :
    ∀ (is : List (Fin 12)),
    ∀ (D : Finset Jet) (cap : Fin 3 → ℕ), IntroFactors P D → (∀ j, factorMass D j ≤ cap j) →
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧
      (∀ k old, mass S k ≤ introAccount k is cap old + weightedDegree old D) ∧
      ∀ z R, (∀ i ∈ is, ∀ j a, a ≤ reserve i → jetAt (seedHasse j a (later i)) z R = 0) →
        jetAt Q z R = 0 → (∃ f ∈ D, jetAt f z R = 0) → ∃ I ∈ S, OnJet I z R := by
  intro is
  induction is with
  | nil =>
    intro D cap hD hcap
    let t := movingShape 0; have gt := moving_ode_guard 0
    obtain ⟨S, hG, hS, hC⟩ := collect D
      (fun f k => factorTariff t k f + ordinaryBudget (factorDegree f 2) (factorDegree f 0) k)
      (fun f z R => jetAt f z R = 0 ∧ jetAt Q z R = 0) (terminal_piece hD hnc hQc gt.jb gt.small hQ)
    refine ⟨S, hG, ?_, ?_⟩
    · intro k old
      have hstep := tariff_step (Finset.empty_subset D) cap old t k hcap
      simp only [Finset.sdiff_empty, weightedDegree, factorMass, Finset.sum_empty, mul_zero, Finset.sum_const_zero, Nat.add_zero] at hstep
      have hsum := Nat.add_le_add hstep (ordinary_charge D cap hcap k)
      calc _ ≤ ∑ f ∈ D, (factorTariff t k f + ordinaryBudget (factorDegree f 2) (factorDegree f 0) k) := hS k
           _ ≤ (weightedDegree old D + introJump cap old t k) + ordinaryBudget (cap 2) (cap 0) k := by rw [Finset.sum_add_distrib]; exact hsum
           _ = _ := by simp only [introAccount]; ac_rfl
    · intro z R _ hq ⟨f, hf, hz⟩; exact hC f hf z R ⟨hz, hq⟩
  | cons i is ih =>
    intro D cap hD hcap
    let s := freeShape i; let r := reserve i
    let T := D.filter fun f => ∀ j a, a ≤ r → f ∣ seedHasse j a (later i)
    have hT : T ⊆ D := Finset.filter_subset _ _
    have gt := free_ode_guard i
    obtain ⟨hrow, hc⟩ := rows i
    have hTcap (j : Fin 3) : factorMass T j ≤ min (cap j) (degreeVector s j / (r+1)) :=
      le_min ((factorMass_mono hT j).trans (hcap j))
        (retained_mass (hD.mono hT) hrow hc (free_seed_small i) r (fun f hf => (Finset.mem_filter.mp hf).2) j)
    obtain ⟨laterCover, hLaterGeom, hLaterCap, hLater⟩ := ih T _ (hD.mono hT) hTcap
    obtain ⟨discard, hDiscardGeom, hDiscardCap, hDiscard⟩ :=
      collect (D \ T) (fun f k => factorTariff s k f)
        (fun f z R => jetAt f z R = 0 ∧ ∀ j a, a ≤ r → jetAt (seedHasse j a (later i)) z R = 0) (by
        intro f hf; obtain ⟨hfD, hfT⟩ := Finset.mem_sdiff.mp hf
        have hn : ¬ ∀ j a, a ≤ r → f ∣ seedHasse j a (later i) := fun hall => hfT (Finset.mem_filter.mpr ⟨hfD, hall⟩)
        push Not at hn; obtain ⟨j, a, ha, hd⟩ := hn
        have hirr := (hD.factors f hfD).1
        obtain ⟨S, hG, hF, hC⟩ := proper_cover (irreducible_cut hirr hd)
          (own_J_le_B hirr.ne_zero) gt.jb (own_caps f) (P1_7_4_1_2.proof s (later i) hc j a)
        exact ⟨S, hG, fun k => (hF k).trans_eq (residual_tariff f s gt.jb k), fun z R hr => hC z R hr.1 (hr.2 j a ha)⟩)
    refine ⟨discard ∪ laterCover, fun I hI => (Finset.mem_union.mp hI).elim (hDiscardGeom I) (hLaterGeom I), ?_, ?_⟩
    · intro k old
      let w := fun j => max (old j) (introWeight s k j)
      let newCap := fun j => min (cap j) (degreeVector s j / (r+1))
      have hstep := tariff_step hT cap old s k hcap
      calc _ ≤ mass discard k + mass laterCover k := sum_union_le (fun I => sectionDegree I k) _ _
           _ ≤ (∑ f ∈ D \ T, factorTariff s k f) + (introAccount k is newCap w + weightedDegree w T) :=
             Nat.add_le_add (hDiscardCap k) (hLaterCap k w)
           _ = introAccount k is newCap w + ((∑ f ∈ D \ T, factorTariff s k f) + weightedDegree w T) := by ac_rfl
           _ ≤ introAccount k is newCap w + (weightedDegree old D + introJump cap old s k) := Nat.add_le_add_left hstep _
           _ = _ := by change _ = (introJump cap old s k + introAccount k is newCap w) + weightedDegree old D; ac_rfl
    · intro z R hder hq ⟨f, hf, hz⟩
      by_cases h : f ∈ T
      · obtain ⟨I, hI, hMark⟩ := hLater z R (fun l hl => hder l (List.mem_cons_of_mem _ hl)) hq ⟨f, h, hz⟩
        exact ⟨I, Finset.mem_union_right _ hI, hMark⟩
      · obtain ⟨I, hI, hMark⟩ := hDiscard f (Finset.mem_sdiff.mpr ⟨hf, h⟩) z R ⟨hz, hder i (List.mem_cons_self ..)⟩
        exact ⟨I, Finset.mem_union_left _ hI, hMark⟩

def Rows.fixedMarksOf {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (G : ODE) : Finset K :=
  R.marks.filter (fun γ=>fixedAt G (R.family.scalar γ)=0)
def Rows.fixedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Finset K :=
  (univ : Finset (Fin 12)).biUnion (fun i=>R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation)
theorem Rows.mem_fixed_free {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin 12) (root : fixedAt (R.fixedFree i).equation (R.family.scalar γ)=0) : γ∈R.fixedMarks :=
  mem_biUnion.mpr ⟨i,mem_univ _,mem_union_left _ (mem_filter.mpr ⟨mark,root⟩)⟩
theorem Rows.mem_fixed_moving {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin 12) (root : fixedAt (R.fixedMoving i).equation (R.family.scalar γ)=0) : γ∈R.fixedMarks :=
  mem_biUnion.mpr ⟨i,mem_univ _,mem_union_right _ (mem_filter.mpr ⟨mark,root⟩)⟩
def Rows.Clean {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (J : Ideal Ambient) : Prop :=
  ∀ i, ¬ fixedOn (R.fixedFree i).equation J ∧ ¬ fixedOn (R.fixedMoving i).equation J

private theorem Rows.fixed_of_not_clean {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {J : Ideal Ambient} {γ : K} (mark : γ∈R.marks) (on : OnMark R.family J γ) (bad : ¬R.Clean J) : γ∈R.fixedMarks := by
  by_contra absent; apply bad; intro i; constructor
  · intro h; apply absent (R.mem_fixed_free mark i ?_); simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on h)
  · intro h; apply absent (R.mem_fixed_moving mark i ?_); simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on h)

private theorem Rows.sections {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) :
    ∃ S : Finset (Ideal Ambient),SectionGeometry S ∧ Fits S initialCap ∧
      ∃ content : Seeds, content≠0 ∧ content.totalDegree≤(freeShape 0).U ∧
      ∀ γ∈R.marks,γ∈R.fixedMarks ∨ graphEval (M.label γ) content=0 ∨ ∃ J∈S,OnMark R.family J γ := by
  obtain ⟨a⟩ := strip (R.out.free_ne 0) (R.out.free_caps 0) (R.fixedFree 0)
  obtain ⟨A',hA,hcap,hroot⟩ := initial_factors a
  obtain ⟨S,geom,fit,cover⟩ := intro_components (pow_ne_zero _ R.out.helper_ne)
    (R.out.no_moving 0) (R.out.moving_caps 0) R.out.free
    (fun i=>⟨R.out.free_ne i,R.out.free_caps i⟩) introIndices A' _ hA hcap
  refine ⟨S,geom,?_,a.content,a.content_ne,a.content_le,?_⟩
  · intro k; simpa only [initialCap,weightedDegree,zero_mul,Finset.sum_const_zero,Nat.add_zero] using fit k (fun _=>0)
  · intro γ hγ; obtain ⟨p',q⟩ := R.main_contact 0 γ hγ
    rcases a.covers _ _ (zero_of_contact p') with hs | hf | hp
    · exact Or.inr (Or.inl hs)
    · exact Or.inl (R.mem_fixed_free hγ 0 hf)
    · exact Or.inr (Or.inr (cover _ _ (fun i _ j r hr=>R.intro_tests i j r hr γ hγ) (zero_of_contact q) (hroot _ _ hp)))

structure Initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) where
  seed : SeedCover
  seed_cap : seed.curve.totalDegree ≤ initialCap 2
  seed_points : seed.points.card ≤ initialCap 3
  ordinates : Finset FX
  ordinate_cap : ordinates.card ≤ initialCap 0
  content : Seeds
  content_ne : content≠0
  content_cap : content.totalDegree≤(freeShape 0).U
  rankExit : Finset (Ideal Ambient)
  parents : Finset (Ideal Ambient)
  fits : Fits (rankExit∪parents) initialCap
  disjoint : Disjoint rankExit parents
  rank_geom : ∀ J∈rankExit,Active J ∧ ¬dual J
  parent_geom : ∀ J∈parents,Active J ∧ dual J ∧ J.height=2 ∧ R.Clean J
  covers : ∀ γ∈R.marks,γ∈R.fixedMarks ∨ graphEval (M.label γ) content=0 ∨
    seed.Covers (M.label γ) ∨ atX (R.family.scalar γ)∈ordinates ∨
      (∃ J∈rankExit,OnMark R.family J γ) ∨ ∃ J∈parents,OnMark R.family J γ

theorem Rows.initial_cover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Nonempty (Initial R) := by
  obtain ⟨S,geom,fit,content,cn,cc,cover⟩ := R.sections
  let noSeeds := S.filter (fun J=>sectionDegree J 0=0)
  let constY := S.filter (fun J=>0<sectionDegree J 0 ∧ ¬Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let active := S.filter (fun J=>0<sectionDegree J 0 ∧ Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let rank := active.filter (fun J=>R.Clean J ∧ ¬dual J)
  let parents := active.filter (fun J=>R.Clean J ∧ dual J)
  have geomActive (J : Ideal Ambient) (mem : J∈active) : Active J ∧ J.height=2 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,height,finite⟩ := geom J hin
    have small (k : Fin 4) := (length_le_mass hin k).trans_lt ((fit k).trans_lt (initial_small k))
    exact ⟨⟨prime,dim,finite.seeds,finite.ordinate,finite.mixed,finite.jets,⟨seedPos,small 0⟩,small 2,small 3,ord⟩,height⟩
  have seed_exists (J : Ideal Ambient) (mem : J∈noSeeds) :
      ∃ C : SeedCover,C.curve.totalDegree≤sectionDegree J 2 ∧ C.points.card≤sectionDegree J 3 ∧
        ∀ z T,OnJet J z T → C.Covers z := by
    obtain ⟨hin,zero⟩ := mem_filter.mp mem; obtain ⟨prime,dim,_,finite⟩ := geom J hin
    exact seed_projection J prime dim finite zero
  let seedImage (J : Ideal Ambient) : SeedCover :=
    if mem : J∈noSeeds then Classical.choose (seed_exists J mem) else ⟨1,one_ne_zero,∅⟩
  have seed_spec (J : Ideal Ambient) (mem : J∈noSeeds) :
      (seedImage J).curve.totalDegree≤sectionDegree J 2 ∧ (seedImage J).points.card≤sectionDegree J 3 ∧
        ∀ z T,OnJet J z T → (seedImage J).Covers z := by
    simpa only [seedImage,dite_eq_left mem] using Classical.choose_spec (seed_exists J mem)
  let onY (J : Ideal Ambient) := (R.marks.filter (OnMark R.family J)).image fun γ=>atX (R.family.scalar γ)
  have ordinate_bound (J : Ideal Ambient) (mem : J∈constY) : (onY J).card≤sectionDegree J 0 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    apply le_trans (b:=1) _ seedPos; apply card_le_one.mpr
    intro y hy z hz; obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hy; obtain ⟨δ,hδ,rfl⟩ := mem_image.mp hz
    exact ordinate_eq (geom J hin).1 ord (mem_filter.mp hγ).2 (mem_filter.mp hδ).2
  refine ⟨⟨joinCovers noSeeds seedImage,?_,?_,constY.biUnion onY,?_,content,cn,cc,rank,parents,?_,?_,?_,?_,?_⟩⟩
  · exact (joinCovers_degree _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).1).trans ((mass_mono (filter_subset _ _) 2).trans (fit 2)))
  · exact (joinCovers_points _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).2.1).trans ((mass_mono (filter_subset _ _) 3).trans (fit 3)))
  · exact card_biUnion_le.trans ((sum_le_sum ordinate_bound).trans ((mass_mono (filter_subset _ _) 0).trans (fit 0)))
  · apply K1_14_2_2.fits_mono _ fit
    exact union_subset ((filter_subset _ _).trans (filter_subset _ _)) ((filter_subset _ _).trans (filter_subset _ _))
  · exact disjoint_left.mpr fun _ a b=>(mem_filter.mp a).2.2 (mem_filter.mp b).2.2
  · intro J mem; exact ⟨(geomActive J (mem_filter.mp mem).1).1,(mem_filter.mp mem).2.2⟩
  · intro J mem; obtain ⟨hin,c,d⟩ := mem_filter.mp mem; obtain ⟨act,ht⟩ := geomActive J hin; exact ⟨act,d,ht,c⟩
  · intro γ hγ
    rcases cover γ hγ with fixed | seed | ⟨J,hin,on⟩
    · exact Or.inl fixed
    · exact Or.inr (Or.inl seed)
    · by_cases z : sectionDegree J 0=0
      · exact Or.inr (Or.inr (Or.inl (joinCovers_covers (mem_filter.mpr ⟨hin,z⟩) ((seed_spec J (mem_filter.mpr ⟨hin,z⟩)).2.2 _ _ on))))
      · by_cases ord : Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl)
        · have mem : J∈active := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
          by_cases clean : R.Clean J
          · by_cases d : dual J
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨J,mem_filter.mpr ⟨mem,clean,d⟩,on⟩))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨J,mem_filter.mpr ⟨mem,clean,d⟩,on⟩))))
          · exact Or.inl (R.fixed_of_not_clean hγ on clean)
        · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_biUnion.mpr ⟨J,mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩,
            mem_image.mpr ⟨γ,mem_filter.mpr ⟨hγ,on⟩,rfl⟩⟩))))

theorem Initial.rank_ode {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ E : ODE, ODECaps E (mass ini.rankExit 2) (mass ini.rankExit 1) ∧
      ∀ γ∈R.marks,(∃ J∈ini.rankExit,OnMark R.family J γ) → fixedAt E (R.family.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation ini.rankExit ini.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩; rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))

def Initial.kept {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) :=
  ini.parents.filter (fun J=>∀ i : Fin 12,0 < i.val → i.val≤n → R.Passes i J)
theorem Initial.kept_zero {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.kept 0=ini.parents := by
  ext J; constructor
  · exact fun h=>(mem_filter.mp h).1
  · intro h; apply mem_filter.mpr; refine ⟨h,fun i pos zero=>?_⟩; omega
theorem Initial.kept_anti {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    Antitone ini.kept := by
  intro m n le J mem; obtain ⟨p',pass⟩ := mem_filter.mp mem
  exact mem_filter.mpr ⟨p',fun i hi hm=>pass i hi (hm.trans le)⟩
theorem Initial.kept_geom {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {n : ℕ} {J : Ideal Ambient} (mem : J∈ini.kept n) : Active J ∧ dual J ∧ J.height=2 ∧ R.Clean J :=
  ini.parent_geom J (mem_filter.mp mem).1
def Initial.final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    Finset (Ideal Ambient) := (ini.kept 11).filter (TerminalPass Crt (word M))
def Initial.live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := if n<12 then ini.kept n else ini.final
def Initial.lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := ini.live n \ ini.live (n+1)
theorem Initial.live_zero {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.live 0=ini.parents := by
  rw [Initial.live,ite_eq_left (by decide : 0<12),ini.kept_zero]
theorem Initial.next_sub {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<12) : ini.live (i+1)⊆ini.live i := by
  by_cases hn : i+1<12
  · simp only [Initial.live,ite_eq_left hi,ite_eq_left hn]; exact ini.kept_anti (Nat.le_succ _)
  · have eq : i=11 := by omega
    subst i; exact filter_subset _ _
theorem Initial.stage_mass {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (i : Fin 12) (hi : 0 < i.val) {n : ℕ} (step : i.val≤n) (k : Fin 4) :
    massQ (ini.kept n) k≤pairedCap (freeShape i) (movingShape i) (reserve i) true k := by
  have s := free_ode_guard i; have t := moving_ode_guard i
  apply P1_7_4_2.proof (freeShape i) (movingShape i) (reserve i) true (R.out.free i)
    (R.out.helper^copies i) (reserve_pos hi) (reserve_small i) s.small t.small
    (free_seed_small i) (moving_seed_small i) s.jb t.jb (R.out.free_ne i)
    (pow_ne_zero _ R.out.helper_ne) (R.out.free_caps i) (R.out.moving_caps i)
    (R.out.no_moving i) (R.fixedFree i) (R.fixedMoving i)
  · intro _ J mem; exact (ini.kept_geom mem).2.1
  · intro J mem; have geom := ini.kept_geom mem; have pass := (mem_filter.mp mem).2 i hi step
    have clean := geom.2.2.2 i; exact ⟨geom.1,pass.2.2,clean.1,clean.2,pass.1,pass.2.1⟩

theorem Initial.marked_cutter {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} {J : Ideal Ambient} (hi : i<12) (mem : J∈ini.lost i) :
    ∃ C : Jet,RowCaps C (cutShape i) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  obtain ⟨prev,lost⟩ := mem_sdiff.mp mem; rw [Initial.live,ite_eq_left hi] at prev
  by_cases hn : i+1<12
  · let j : Fin 12 := ⟨i+1,hn⟩
    have hf : ¬R.Passes j J := by
      intro p'; apply lost; rw [Initial.live,ite_eq_left hn]; apply mem_filter.mpr
      refine ⟨(mem_filter.mp prev).1,?_⟩; intro z hz ht
      by_cases same : z.val=i+1
      · exact (Fin.ext same : z=j) ▸ p'
      · exact (mem_filter.mp prev).2 z hz (by omega)
    have geom := ini.kept_geom prev
    obtain ⟨C,cap,proper,zero⟩ := R.failed_cut j geom.1 geom.2.1 hf
    refine ⟨C,?_,proper,zero⟩; rw [cutShape,dite_eq_left hn]
    exact envelope_caps (s:=stage j) (free_ode_guard j).jb (moving_ode_guard j).jb cap
  · have eq : i=11 := by omega
    subst i; have hf : ¬ TerminalPass Crt (word M) J := fun p' => lost (mem_filter.mpr ⟨prev,p'⟩)
    unfold TerminalPass at hf; push Not at hf; obtain ⟨C,inside,proper⟩ := hf
    refine ⟨C,evaluated_shape Crt (word M) inside,proper,?_⟩
    intro γ hγ _; apply zero_of_contact (r:=0)
    exact contact_at_mark R.family Crt noPole (fun δ hd=>residues δ (mem_filter.mp hd).1) inside
      (by simp only [Nat.mul_zero,Nat.add_zero]; decide +kernel) γ hγ

theorem Initial.cutCover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} (hi : i<12) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape i) fee) (mass (ini.lost i))) ∧
      ∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
  have oneCut (J : Ideal Ambient) (mem : J∈ini.lost i) :
      ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape i) fee) (sectionDegree J)) ∧
        ∀ γ∈R.marks,OnMark R.family J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
    obtain ⟨P,cap,proper,zero⟩ := ini.marked_cutter noPole residues hi mem
    have prev := (mem_sdiff.mp mem).1; rw [Initial.live,ite_eq_left hi] at prev
    let sub := R.marks.filter (OnMark R.family J)
    let G : Family M sub := ⟨R.family.scalar,fun γ hγ=>R.family.mark γ (mem_filter.mp hγ).1,R.family.distinct.mono (filter_subset _ _)⟩
    obtain ⟨C,cost,cover⟩ := proper_cut G (cutShape i) (cutShape_fit i) (ini.kept_geom prev).1 cap proper
      (fun γ hγ=>zero γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2)
    exact ⟨C,cost,fun γ hγ on=>cover γ (mem_filter.mpr ⟨hγ,on⟩) on⟩
  let C (J : Ideal Ambient) : CutCover := if mem : J∈ini.lost i then Classical.choose (oneCut J mem) else emptyCut
  have spec (J : Ideal Ambient) (mem : J∈ini.lost i) :
      (∀ fee,(C J).cost fee≤dot (weight (cutShape i) fee) (sectionDegree J)) ∧
        ∀ γ∈R.marks,OnMark R.family J γ → γ∈(C J).direct ∨ ∃ Q∈(C J).curves,OnMark R.family Q γ := by
    simpa only [C,dite_eq_left mem] using Classical.choose_spec (oneCut J mem)
  refine ⟨joinCuts (ini.lost i) C,?_,?_⟩
  · intro fee; exact (joinCuts_cost _ _ _).trans ((sum_le_sum fun J mem => (spec J mem).1 fee).trans_eq (sum_dot _ _))
  · rintro γ hγ ⟨J,mem,on⟩
    rcases (spec J mem).2 γ hγ on with point | ⟨Q,hQ,hmark⟩
    · exact Or.inl (mem_biUnion.mpr ⟨J,mem,point⟩)
    · exact Or.inr ⟨Q,mem_biUnion.mpr ⟨J,mem,hQ⟩,hmark⟩

theorem Initial.retained_or_lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {J : Ideal Ambient} (mem : J∈ini.parents) : J∈ini.final ∨ ∃ i<12,J∈ini.lost i := by
  by_cases h : ∃ i<12,J∈ini.lost i
  · exact Or.inr h
  · have alive : ∀ n≤12,J∈ini.live n := by
      intro n hn
      induction n with
      | zero => exact ini.live_zero.symm ▸ mem
      | succ n ih => by_contra absent; exact h ⟨n,by omega,mem_sdiff.mpr ⟨ih (by omega),absent⟩⟩
    exact Or.inl (by simpa [Initial.live] using alive 12 le_rfl)

theorem Initial.terminal_surfaces {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈R.marks,(∃ J∈ini.final,OnMark R.family J γ) → ∃ q∈S,OnSurface F q γ := by
  let geom (J : ini.final) := ini.kept_geom (mem_filter.mp J.property).1
  let surface (J : ini.final) := surfaceOf J.val (geom J).1.prime
  let S := ini.final.attach.image surface
  refine ⟨S,?_,?_⟩
  · intro q hq; obtain ⟨J,_,rfl⟩ := mem_image.mp hq; have hJ := geom J
    exact ⟨parent_of_dual hJ.1 hJ.2.2.1 hJ.2.1,(mem_filter.mp J.property).2⟩
  · rintro γ _ ⟨J,hJ,on⟩; let q : ini.final := ⟨J,hJ⟩
    refine ⟨surface q,mem_image.mpr ⟨q,mem_attach _ _,rfl⟩,?_⟩
    intro P mem; rw [←K1_14_2.eval_toJet]; exact RingHom.mem_ker.mp (on mem)

def initialMass : Mass := fun k=>initialCap k

private def historyTable : List Mass :=
  [
    ![10622, 103882, 482666, 2143787],
    ![26483/4, 158685/2, 1434455/4, 1827125],
    ![30013/9, 345112/9, 1434455/4, 1444804],
    ![2033, 187345/8, 188505, 901900],
    ![18673/18, 108647/9, 974565/8, 576081],
    ![537, 511942/81, 2309105/36, 2856535/9],
    ![537, 511942/81, 589573/10, 274302],
    ![142748/441, 1746256/441, 308471/8, 8230304/45],
    ![142748/441, 1746256/441, 308471/8, 136161],
    ![142748/441, 10903164/2809, 16305130/507, 136161],
    ![1525799/5547, 18906065/5547, 28100340/961, 136161],
    ![432628/2209, 18906065/5547, 28100340/961, 136161]
  ]

def history (i : ℕ) : Mass := historyTable.getD i initialMass

theorem history_zero (k : Fin 4) : history 0 k=initialMass k := by fin_cases k <;> decide +kernel
theorem history_step (i : Fin 11) (k : Fin 4) :
    let j : Fin 12 := ⟨i.val+1,by have := i.isLt; omega⟩
    history (i.val+1) k = min (history i.val k) (pairedCap (freeShape j) (movingShape j) (reserve j) true k) := by
  fin_cases i <;> fin_cases k <;> decide +kernel

theorem Initial.cap_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) (k : Fin 4) : massQ (ini.kept n) k ≤ initialMass k :=
  (Nat.cast_le (α:=ℚ)).mpr ((mass_mono ((filter_subset _ _).trans subset_union_right) k).trans (ini.fits k))

theorem Initial.cap_kept {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<12) (k : Fin 4) : massQ (ini.kept i) k≤history i k := by
  induction i with
  | zero => rw [history_zero]; exact ini.cap_initial _ _
  | succ i ih =>
    have hl : i<11 := by omega
    have hstep := history_step ⟨i,hl⟩ k; dsimp only at hstep; rw [hstep]
    exact le_min ((massQ_mono (ini.kept_anti (Nat.le_succ i)) k).trans (ih (by omega)))
      (ini.stage_mass ⟨i+1,hi⟩ (Nat.succ_pos _) le_rfl k)

theorem Initial.cap_live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<12) (k : Fin 4) : massQ (ini.live i) k≤history i k := by
  rw [Initial.live,ite_eq_left hi]; exact ini.cap_kept hi k
theorem Initial.live_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<12) (k : Fin 4) : massQ (ini.live i) k ≤ initialMass k := by
  rw [Initial.live,ite_eq_left hi]; exact ini.cap_initial _ k

def cutWeight (fee : Fin 3) (i : ℕ) : Mass := fun k=>weight (cutShape i) fee k
def seedLimit : ℚ := weightedBill 12 (cutWeight 0) history
def pointLimit : ℚ := weightedBill 12 (cutWeight 2) (fun _=>initialMass)
def initialSeedLimit : ℕ := (K1.p+1)*initialCap 2+initialCap 3
def contentLimit : ℕ := (K1.p+1)*(freeShape 0).U
def fixedLimit : ℕ := ∑ i : Fin 12, (fixedFee (freeShape i).B (freeShape i).J+fixedFee (movingShape i).B (movingShape i).J)

theorem seed_limit_small : seedLimit < (K1.p : ℚ) := by decide +kernel

def Initial.seedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))
def Initial.ordinateMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>atX (R.family.scalar γ)∈ini.ordinates)
def Initial.contentMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)
def Initial.rankMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>∃ J∈ini.rankExit,OnMark R.family J γ)

theorem Initial.ordinary_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.ordinateMarks.card ≤ initialCap 0 := by
  apply (card_le_card_of_injOn (fun γ=>atX (R.family.scalar γ)) (fun _ hγ=>(mem_filter.mp hγ).2) ?_).trans ini.ordinate_cap
  intro γ hγ δ hδ eq; exact R.family.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1 (K1_14_3.scalar_atX_injective eq)
theorem Initial.seed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.seedMarks.card ≤ initialSeedLimit := by
  have bound := K1_14_3.seed_count (T:=ini.seedMarks) (label_injective M).injOn ini.seed
    (ini.seed_cap.trans_lt (initial_small 2)) (fun _ hγ=>(mem_filter.mp hγ).2)
  exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_left _ ini.seed_cap) ini.seed_points)
theorem Initial.content_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.contentMarks.card≤contentLimit := by
  let C : K1_14_3.SeedCover := ⟨ini.content,ini.content_ne,∅⟩
  have bound := K1_14_3.seed_count (T:=ini.contentMarks) (label_injective M).injOn C
    (ini.content_cap.trans_lt (free_seed_small 0)) (fun _ hγ=>Or.inl (mem_filter.mp hγ).2)
  exact (by simpa only [C,card_empty,Nat.add_zero] using bound :
    ini.contentMarks.card≤(K1.p+1)*ini.content.totalDegree).trans (Nat.mul_le_mul_left _ ini.content_cap)
theorem Rows.fixed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (hi : M.overhead.toNat≤2382) :
    R.fixedMarks.card≤fixedLimit := by
  calc _ ≤ ∑ i : Fin 12, (R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation).card := card_biUnion_le
       _ ≤ _ := sum_le_sum fun i _=>(card_union_le _ _).trans (Nat.add_le_add
         (Lower6962.B1.Tariffs.fixed_count R.family hi (free_ode_guard i) _ (R.fixedFree i).equation_caps (filter_subset _ _) (fun _ hm=>(mem_filter.mp hm).2))
         (Lower6962.B1.Tariffs.fixed_count R.family hi (moving_ode_guard i) _ (R.fixedMoving i).equation_caps (filter_subset _ _) (fun _ hm=>(mem_filter.mp hm).2)))

structure CutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) where
  cover : ℕ→CutCover
  cost : ∀ i<12,∀ fee,(cover i).cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))
  covers : ∀ i<12,∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) → γ∈(cover i).direct ∨ ∃ Q∈(cover i).curves,OnMark R.family Q γ

theorem Initial.cutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0) (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (CutBooks ini) := by
  have pick (i : ℕ) : ∃ C : CutCover,i<12 →
      (∀ fee,C.cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))) ∧
      ∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
    by_cases hi : i<12
    · obtain ⟨C,cap,cover⟩ := ini.cutCover noPole residues hi; exact ⟨C,fun _=>⟨cap,cover⟩⟩
    · exact ⟨emptyCut,fun h=>(hi h).elim⟩
  choose C hC using pick; exact ⟨⟨C,fun i h=>(hC i h).1,fun i h=>(hC i h).2⟩⟩

theorem CutBooks.costQ {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) {i : ℕ} (hi : i<12) (fee : Fin 3) :
    ((C.cover i).cost fee : ℚ)≤dotQ (cutWeight fee i) (massQ (ini.lost i)) := by
  have bound := (Nat.cast_le (α:=ℚ)).mpr (C.cost i hi fee)
  simpa only [cutWeight,dotQ,dot,massQ,Nat.cast_sum,Nat.cast_mul] using bound
theorem CutBooks.seed_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : (∑ i∈range 12,((C.cover i).cost 0 : ℚ))≤seedLimit :=
  (sum_le_sum fun _ h=>C.costQ (mem_range.mp h) 0).trans
    (bill_bound 12 _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl) (fun _ hi=>ini.cap_live hi))
def CutBooks.pointMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : Finset K := (range 12).biUnion fun i=>(C.cover i).direct
theorem CutBooks.point_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : (C.pointMarks.card : ℚ) ≤ pointLimit := by
  calc _ ≤ ∑ i∈range 12,((C.cover i).cost 2 : ℚ) := by
         exact_mod_cast (show C.pointMarks.card ≤ ∑ i∈range 12,(C.cover i).direct.card from card_biUnion_le)
       _ ≤ ∑ i∈range 12,dotQ (cutWeight 2 i) (massQ (ini.lost i)) := sum_le_sum fun i h=>C.costQ (mem_range.mp h) 2
       _ ≤ _ := bill_bound 12 _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl) (fun _ hi=>ini.live_initial hi)

private def Initial.jointLive {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : ℕ→Finset (Ideal Ambient)
  | 0 => ini.rankExit∪ini.parents
  | i+1 => ini.live i
private def Initial.jointLost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : ℕ→Finset (Ideal Ambient)
  | 0 => ini.rankExit
  | i+1 => ini.lost i

theorem Initial.joint_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ ini.rankExit) + (∑ i∈range 12,dotQ (cut i) (massQ (ini.lost i))) ≤
      weightedBill 13 (beforeCuts rank cut) (beforeCuts initialMass history) := by
  have bill := bill_bound 13 (beforeCuts rank cut) (beforeCuts initialMass history) ini.jointLive ini.jointLost ?_ ?_ ?_
  · rw [show 13=12+1 by decide,sum_range_succ'] at bill
    simpa only [beforeCuts,Initial.jointLost,add_comm] using bill
  · intro i hi; cases i with
    | zero => simpa only [Initial.jointLive,ini.live_zero] using (subset_union_right : ini.parents⊆ ini.rankExit∪ini.parents)
    | succ i => exact ini.next_sub (by omega)
  · intro i hi; cases i with
    | zero =>
      intro J mem; apply mem_sdiff.mpr; refine ⟨mem_union_left _ mem,?_⟩
      rw [Initial.jointLive,ini.live_zero]; exact fun h=>(disjoint_left.mp ini.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k; cases i with
    | zero => exact (Nat.cast_le (α:=ℚ)).mpr (ini.fits k)
    | succ i => exact ini.cap_live (by omega) k

def degreeRates : List ℕ := [156602714, 109264930, 73288426, 50134209, 47881038, 50134238, 47881033, 50134064, 45821671, 62040749, 85430768, 146183885]
def heightRates : List ℕ := [2456041, 3601984, 5462401, 8070945, 8460216, 8070940, 8460217, 8070970, 8849477, 6484830, 4657495, 2633225]
def degreeRate (i : ℕ) : ℕ := degreeRates.getD i 0
def heightRate (i : ℕ) : ℕ := heightRates.getD i 0

private theorem checked_rates (i : Fin 12) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate i.val : ℚ) ∧
      min seedLimit (dotQ (cutWeight 0 i.val) (history i.val)) ≤ (degreeRate i.val : ℚ) ∧
      heightBound (degreeRate i.val) ≤ (heightRate i.val : ℚ) := by
  fin_cases i <;> decide +kernel

theorem rate_spec {i : ℕ} (hi : i<12) :
    RateOK (degreeRate i) (heightRate i) ∧
      min seedLimit (dotQ (cutWeight 0 i) (history i)) ≤ degreeRate i := by
  obtain ⟨base,degree,height⟩ := checked_rates ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def rankB : ℕ := initialCap 2+2
def rankJ : ℕ := initialCap 1+1
def pivot : ℚ := min (47843/5) (tau*rankB)
def rankWeight : Mass := ![0,4*lambda*rankB*tau+mu-4*lambda*pivot,4*lambda*rankJ*(1-tau)+rankB,0]
def rankRound : ℚ := rankWeight 1+2*rankWeight 2+2*lambda*pivot^2+1
def lossWeight (i : ℕ) : Mass := fun k=>(degreeRate i : ℚ)*cutWeight 0 i k+(heightRate i : ℚ)*cutWeight 1 i k
def lossLimit : ℚ := weightedBill 13 (beforeCuts rankWeight lossWeight) (beforeCuts initialMass history)+seedLimit+rankRound
def mainFee : ℕ := lossLimit.ceil.toNat+pointLimit.ceil.toNat+initialSeedLimit+initialCap 0+fixedLimit+contentLimit

theorem main_fee_bound : mainFee ≤ 76875204374024915 := by decide +kernel
theorem rank_guard : rankB<p ∧ 0≤rankWeight 1 ∧ 0≤rankWeight 2 := by decide +kernel

theorem Initial.rank_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) (hi : M.overhead.toNat≤2382) :
    (ini.rankMarks.card : ℚ)≤dotQ rankWeight (massQ ini.rankExit)+rankRound := by
  let S := ini.rankExit; let B := max 2 (mass S 2); let J := max 1 (min (mass S 1) B)
  obtain ⟨E,caps,roots⟩ := ini.rank_ode
  have mass_cap (k : Fin 4) : mass S k ≤ initialCap k := (mass_mono (subset_union_left : S⊆ini.rankExit∪ini.parents) k).trans (ini.fits k)
  have hBm : B≤mass S 2+2 := max_le (by omega) (by omega)
  have hJm : J≤mass S 1+1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B≤rankB := hBm.trans (Nat.add_le_add_right (mass_cap 2) 2)
  have hJ : J≤rankJ := hJm.trans (Nat.add_le_add_right (mass_cap 1) 1)
  have hJB : J≤B := max_le (by omega) (min_le_right _ _)
  have degree : E.natDegree≤B := by
    have top : E.coeff E.natDegree ≠ 0 := by rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree≠0 := by
      rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1,(le_min caps.2.1 degree).trans (le_max_right _ _),fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  obtain ⟨small,cJ,cB⟩ := rank_guard
  have guard : ODEGuard B J := ⟨le_max_left _ _, by omega, hJB, hB.trans_lt small⟩
  have count : ini.rankMarks.card≤fixedFee B J :=
    fixed_count R.family hi guard E ocaps (filter_subset _ _) (fun γ mem => roots γ (mem_filter.mp mem).1 (mem_filter.mp mem).2)
  have lin := fixed_fee_linear lambda mu tau pivot (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤ rankWeight 1 * J + rankWeight 2 * B + 2*lambda*pivot^2+1 := by rw [fixedFee_eq]; exact lin
  have hJq : (J : ℚ)≤(mass S 1 : ℚ)+1 := by exact_mod_cast hJm
  have hBq : (B : ℚ)≤(mass S 2 : ℚ)+2 := by exact_mod_cast hBm
  have hjfee := mul_le_mul_of_nonneg_left hJq cJ
  have hbfee := mul_le_mul_of_nonneg_left hBq cB
  have hdot : dotQ rankWeight (massQ ini.rankExit) = rankWeight 1 * (mass S 1 : ℚ)+rankWeight 2 * (mass S 2 : ℚ) := by
    simp [dotQ,rankWeight,massQ,Fin.sum_univ_succ,S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [hdot,rankRound]; linarith only [hjfee,hbfee]

private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ)≤q) : a≤q.ceil.toNat := by
  have ceil_cast : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact_mod_cast bound.trans (Rat.le_ceil.trans ceil_cast)

theorem CutBooks.curve_bin_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hiM : M.overhead.toNat≤2382) {i : ℕ} (hi : i<12) :
    ((curveMarks R.family (C.cover i)).card : ℚ)≤
      dotQ (lossWeight i) (massQ (ini.lost i))+((C.cover i).cost 0 : ℚ) := by
  have global : ((C.cover i).cost 0 : ℚ)≤seedLimit :=
    (single_le_sum (fun j _=>Nat.cast_nonneg (α:=ℚ) ((C.cover j).cost 0)) (mem_range.mpr hi)).trans C.seed_bill
  have localCap : ((C.cover i).cost 0 : ℚ)≤ dotQ (cutWeight 0 i) (history i) :=
    (C.costQ hi 0).trans (dotQ_mono_mass (fun _=>Nat.cast_nonneg _)
      (fun k=>(massQ_mono sdiff_subset k).trans (ini.cap_live hi k)))
  have prime : (C.cover i).cost 0 < p := by exact_mod_cast global.trans_lt seed_limit_small
  obtain ⟨ok,degree⟩ := rate_spec hi
  have count := rated_curve_count R.family (curve_tariff R.family hiM) ok (C.cover i)
    global ((min_le_min le_rfl localCap).trans degree) prime
  calc
    _ ≤ (degreeRate i : ℚ)*((C.cover i).cost 0 : ℚ) + (heightRate i : ℚ)*((C.cover i).cost 1 : ℚ)+((C.cover i).cost 0 : ℚ) := count
    _ ≤ (degreeRate i : ℚ)*dotQ (cutWeight 0 i) (massQ (ini.lost i)) +
          (heightRate i : ℚ)*dotQ (cutWeight 1 i) (massQ (ini.lost i)) + ((C.cover i).cost 0 : ℚ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (C.costQ hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (C.costQ hi 1) (Nat.cast_nonneg _))) le_rfl
    _ = _ := by rw [dotQ_scale_add]; rfl

def CutBooks.lossMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R} (C : CutBooks ini) :
    Finset K := ini.rankMarks ∪ (range 12).biUnion (fun i=>curveMarks R.family (C.cover i))

theorem CutBooks.loss_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hi : M.overhead.toNat≤2382) : C.lossMarks.card ≤ lossLimit.ceil.toNat := by
  apply card_round
  have cum : (C.lossMarks.card : ℚ) ≤ (ini.rankMarks.card : ℚ) + ∑ i∈range 12,((curveMarks R.family (C.cover i)).card : ℚ) := by
    exact_mod_cast (show C.lossMarks.card ≤ ini.rankMarks.card + ∑ i∈range 12,(curveMarks R.family (C.cover i)).card from
      (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have sum_cuts := sum_le_sum (fun _ mem=>C.curve_bin_count hi (mem_range.mp mem)) (s:=range 12)
  rw [sum_add_distrib] at sum_cuts
  have both := add_le_add (ini.rank_count hi) sum_cuts
  have joint := ini.joint_bill rankWeight lossWeight
  have seed := C.seed_bill
  have total := cum.trans both
  unfold lossLimit; linarith only [total,joint,seed]

def CutBooks.paid {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R} (C : CutBooks ini) :
    Finset K := (C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks) ∪ (R.fixedMarks ∪ ini.contentMarks)

theorem CutBooks.paid_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hi : M.overhead.toNat≤2382) : C.paid.card≤mainFee := by
  have combined := card_union_le ((C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks)) (R.fixedMarks ∪ ini.contentMarks)
  have left := card_union_le (C.lossMarks ∪ C.pointMarks) (ini.seedMarks ∪ ini.ordinateMarks)
  have cuts := card_union_le C.lossMarks C.pointMarks
  have low := card_union_le ini.seedMarks ini.ordinateMarks
  have fixed := card_union_le R.fixedMarks ini.contentMarks
  have loss := C.loss_count hi
  have points := card_round C.point_bill
  have seeds := ini.seed_count
  have ordinates := ini.ordinary_count
  have content := ini.content_count
  have fixedCard := R.fixed_count hi
  unfold mainFee CutBooks.paid; omega

theorem Rows.main_prefix {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (hi : M.overhead.toNat≤2382) (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (paid : Finset K) (S : Finset Surface),
      paid.card≤76875204374024915 ∧ (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈R.marks,γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨ini⟩ := R.initial_cover
  obtain ⟨C⟩ := ini.cutBooks noPole residues
  obtain ⟨S,geom,surface⟩ := ini.terminal_surfaces
  refine ⟨C.paid,S,(C.paid_count hi).trans main_fee_bound,geom,?_⟩
  intro γ hγ
  rcases ini.covers γ hγ with fixed | content | seed | ord | rank | ⟨J,mem,on⟩
  · exact Or.inl (mem_union_right _ (mem_union_left _ fixed))
  · exact Or.inl (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hγ,content⟩)))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hγ,seed⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hγ,ord⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hγ,rank⟩)))))
  · rcases ini.retained_or_lost mem with final | ⟨i,hi',lost⟩
    · exact Or.inr (surface γ hγ ⟨J,final,on⟩)
    · rcases C.covers i hi' γ hγ ⟨J,lost,on⟩ with point | ⟨Q,hQ,hmark⟩
      · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨i,mem_range.mpr hi',point⟩))))
      · have mark : γ∈(range 12).biUnion (fun i=>curveMarks R.family (C.cover i)) :=
          mem_biUnion.mpr ⟨i,mem_range.mpr hi',mem_curveMarks (F:=R.family) hγ hQ hmark⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ mark))))

def prefixCap : ℕ := 189031767488908585

theorem combined_prefix {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2360≤M.overhead.toNat) (hi : M.overhead.toNat≤2382)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (paid : Finset K) (S : Finset Surface), paid.card≤prefixCap ∧
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      (S.Nonempty → ∃ f,ProjectedProduct S f) ∧
      ∀ γ∈Γ,γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨R⟩ := rows F Crt lo hi noPole residues
  obtain ⟨main,left,fee,passing,cover⟩ := R.main_prefix hi noPole residues
  rcases R.out.kind with unit | common
  · refine ⟨main,left,fee.trans (by decide +kernel),passing,fun hs=>K1_14_3_7.proof left hs (fun q hq=>(passing q hq).1),?_⟩
    intro γ hγ; apply cover; exact mem_filter.mpr ⟨hγ,by simp [unit,jetAt]⟩
  · obtain ⟨rescue,right,cost,retains,rescue_cover⟩ := exceptional_prefix F Crt lo hi noPole residues common
    have geom : ∀ q∈left∪right, Parent q ∧ SurfacePass Crt (word M) q := fun q hq => (mem_union.mp hq).elim (passing q) (retains q)
    refine ⟨main∪rescue,left∪right,(card_union_le _ _).trans ((Nat.add_le_add fee cost).trans (by decide +kernel)),
      geom,fun hs=>K1_14_3_7.proof _ hs (fun q hq=>(geom q hq).1),?_⟩
    intro γ hγ
    by_cases e : jetAt R.out.exception (M.label γ) (F.scalar γ)=0
    · rcases rescue_cover γ hγ e with m | ⟨q,hq,hm⟩
      · exact Or.inl (subset_union_right m)
      · exact Or.inr ⟨q,subset_union_right hq,hm⟩
    · rcases cover γ (mem_filter.mpr ⟨hγ,e⟩) with m | ⟨q,hq,hm⟩
      · exact Or.inl (subset_union_left m)
      · exact Or.inr ⟨q,subset_union_left hq,hm⟩

#print axioms combined_prefix
end Lower6962.B1.MainGeometry
end
end B1MainGeom
