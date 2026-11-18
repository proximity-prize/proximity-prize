/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- 68.33 terminal specialization, derived from Lucieno PR 618, BitWonka PR 581 and Bome2017’s accepted 68.32 proof. Apache-2.0. -/
/- Retuned from Lucieno, Proximity Prize PR 618 (Apache-2.0). All moving derivative orders are allowed by the coefficient identity. -/
import ProximityPrize.SubmissionLower.K6833TerminalIncumbentGraph
import ProximityPrize.SubmissionLower.K6833TerminalIncumbentGraphPrice
import ProximityPrize.SubmissionLower.K6833TerminalIncumbentHelpers
import ProximityPrize.SubmissionLower.K6833TerminalIncumbentPrices

namespace ProximityPrize.SubmissionLower.K6833Residual

open scoped Classical BigOperators
open RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159 RCN174 RCN222 RCN234 RCN238 RCN243 RCN275 RCN286 RCN313 RCN319
open LocatorHybridCells LocatorFactorAggregate MovingFiberThreeSources6811
open K6833TerminalIncumbentGraph (axisPrice regular_graph_seed_card_mul_le)

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4500000
set_option maxRecDepth 6000

private def FlagLinear (q : FlagDegree → ℕ) : Prop :=
  ∀ left, q left = axisPrice (fun i => q (unit i)) left

private theorem unit_zero : unit 0 = unitZFlag := rfl
private theorem unit_one : unit 1 = unitYZFlag := rfl
private theorem unit_two : unit 2 = unitAllFlag := rfl

private theorem byAxis_zero (q : FlagDegree) : byAxis q 0 = q.zOnly := rfl
private theorem byAxis_one (q : FlagDegree) : byAxis q 1 = q.yz := rfl
private theorem byAxis_two (q : FlagDegree) : byAxis q 2 = q.all := rfl

private theorem flagLinear_mixed (g h : FlagDegree) : FlagLinear (fun left => flagMixed left g h) := by
  intro left
  simp only [axisPrice, unit_zero, unit_one, unit_two, flagMixed, unitZFlag, unitYZFlag, unitAllFlag]
  ring

private theorem flagLinear_add {q₁ q₂ : FlagDegree → ℕ} (h₁ : FlagLinear q₁)
    (h₂ : FlagLinear q₂) : FlagLinear (fun f => q₁ f + q₂ f) := by
  intro left
  change q₁ left + q₂ left = axisPrice (fun i => q₁ (unit i) + q₂ (unit i)) left
  rw [h₁ left, h₂ left]
  simp only [axisPrice]
  ring

private theorem flagLinear_mul {q : FlagDegree → ℕ} (a : ℕ) (hq : FlagLinear q) :
    FlagLinear (fun left => a * q left) := by
  intro left
  change a * q left = axisPrice (fun i => a * q (unit i)) left
  rw [hq left]
  simp only [axisPrice]
  ring

private theorem flagLinear_mul_right {q : FlagDegree → ℕ} (a : ℕ) (hq : FlagLinear q) :
    FlagLinear (fun left => q left * a) := by
  intro left
  change q left * a = axisPrice (fun i => q (unit i) * a) left
  rw [hq left]
  simp only [axisPrice]
  ring

private theorem flagLinear_sum {T : Type} (xs : List T) (q : T → FlagDegree → ℕ)
    (hq : ∀ j, FlagLinear (q j)) : FlagLinear (fun left => (xs.map (fun j => q j left)).sum) := by
  induction xs with
  | nil =>
    intro left
    simp [axisPrice]
  | cons j xs ih =>
    simpa only [List.map_cons, List.sum_cons] using flagLinear_add (hq j) ih

private theorem graph_linear (f : Envelope) (cfg : Fin 3 → JetProfile) :
    FlagLinear (jetGraphNumerator TailCorrections.original f cfg) := by
  unfold jetGraphNumerator graphFixed movingCharge
  apply flagLinear_add
  · apply flagLinear_mul_right
    exact flagLinear_sum _ _ (fun _ => flagLinear_mul _ (flagLinear_mixed _ _))
  · exact flagLinear_sum _ _ (fun _ => flagLinear_mul _ (flagLinear_mixed _ _))

private theorem leading_linear (f : Envelope) (cfg : Fin 3 → JetProfile) :
    FlagLinear (jetLeadingNumerator f cfg) := by
  intro left
  simp only [jetLeadingNumerator_eq_list]
  exact flagLinear_sum _ _ (fun j => flagLinear_mixed (cfg j).leading.flag _) left

private theorem graph_mono (f : Envelope) (cfg : Fin 3 → JetProfile) {a b : FlagDegree}
    (hab : Below a b) :
    jetGraphNumerator TailCorrections.original f cfg a ≤
      jetGraphNumerator TailCorrections.original f cfg b := by
  have hsum {T : Type} (xs : List T) (q₁ q₂ : T → ℕ) (hq : ∀ j, q₁ j ≤ q₂ j) :
      (xs.map q₁).sum ≤ (xs.map q₂).sum := by
    induction xs with
    | nil => exact le_rfl
    | cons j xs ih =>
      simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add (hq j) ih
  unfold jetGraphNumerator graphFixed movingCharge
  apply Nat.add_le_add
  · apply Nat.mul_le_mul_right
    exact hsum _ _ _ fun _ => Nat.mul_le_mul_left _ (mixed_mono_first hab _ _)
  · exact hsum _ _ _ fun _ => Nat.mul_le_mul_left _ (mixed_mono_first hab _ _)

private def identityWeight : ℕ := (residualPriceScale / 49997) * 131073 * 81077

def graphAxis (f : Envelope) (cfg : Fin 3 → JetProfile) (i : Fin 3) : ℕ :=
  max (jetGraphNumerator TailCorrections.original (f.pad 2) cfg (unit i))
    (identityWeight * byAxis (identityGraph (f.pad 2)) i)

private theorem identityAxis_mono (f : Envelope) :
    byAxis (identityGraph f) 0 ≤ byAxis (identityGraph f) 1 ∧
      byAxis (identityGraph f) 1 ≤ byAxis (identityGraph f) 2 := by
  simp only [byAxis_zero, byAxis_one, byAxis_two, identityGraph]
  constructor <;> omega

theorem graphAxis_mono (f : Envelope) (cfg : Fin 3 → JetProfile) :
    graphAxis f cfg 0 ≤ graphAxis f cfg 1 ∧ graphAxis f cfg 1 ≤ graphAxis f cfg 2 := by
  obtain ⟨h₁, h₂⟩ := identityAxis_mono (f.pad 2)
  have h01 : Below (unit 0) (unit 1) := by
    change (0 : ℕ) ≤ 0 ∧ 0 ≤ 1 ∧ 1 ≤ 1
    decide
  have h12 : Below (unit 1) (unit 2) := by
    change (0 : ℕ) ≤ 1 ∧ 1 ≤ 1 ∧ 1 ≤ 1
    decide
  exact ⟨max_le_max (graph_mono _ _ h01) (Nat.mul_le_mul_left _ h₁),
    max_le_max (graph_mono _ _ h12) (Nat.mul_le_mul_left _ h₂)⟩

private theorem axisPrice_mono {a b : Fin 3 → ℕ} (h : ∀ i, a i ≤ b i) (f : FlagDegree) :
    axisPrice a f ≤ axisPrice b f :=
  Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (h 0)) (Nat.mul_le_mul_left _ (h 1)))
    (Nat.mul_le_mul_left _ (h 2))

private theorem graph_le_axis (f : Envelope) (cfg : Fin 3 → JetProfile) (left : FlagDegree) :
    jetGraphNumerator TailCorrections.original (f.pad 2) cfg left ≤
      axisPrice (graphAxis f cfg) left := by
  rw [graph_linear (f.pad 2) cfg left]
  exact axisPrice_mono (fun _ => le_max_left _ _) left

private theorem identity_le_axis (f : Envelope) (cfg : Fin 3 → JetProfile) (left : FlagDegree)
    (hr : 3 ≤ (f.pad 2).slope) (hy : (f.pad 2).slope + 2 ≤ (f.pad 2).middle) :
    terminalScale * 131073 * 81077 *
        identityCurveDegree left (cellA (f.pad 2).total (f.pad 2).middle)
          (cellB (f.pad 2).middle (f.pad 2).slope) (cellS (f.pad 2).slope) RCN327.w ≤
      49997 * axisPrice (graphAxis f cfg) left := by
  rw [identityCurveDegree_eq_identityGraph _ _ hr hy]
  have hscale : terminalScale * 131073 * 81077 = 49997 * identityWeight := by decide +kernel
  rw [hscale]
  have haux (g : FlagDegree) (a b : ℕ) :
      (a * b) * (left.zOnly * g.zOnly + left.yz * g.yz + left.all * g.all) =
      a * axisPrice (fun i => b * byAxis g i) left := by
    simp only [axisPrice, byAxis_zero, byAxis_one, byAxis_two]
    ring
  rw [haux]
  exact Nat.mul_le_mul_left _ (axisPrice_mono (fun _ => le_max_right _ _) left)

private theorem axisPrice_add (p q : Fin 3 → ℕ) (left : FlagDegree) :
    axisPrice p left + axisPrice q left = axisPrice (fun i => p i + q i) left := by
  simp only [axisPrice]
  ring

private theorem jetFlagCharge_eq_axisPrice (cuts : TailCorrections) (f : Envelope)
    (cfg : Fin 3 → JetProfile) (left : FlagDegree) :
    jetFlagCharge cuts f cfg left = axisPrice (jetChargeAxisWithCorrections cuts f cfg) left :=
  jetFlagCharge_eq cuts f cfg left

theorem leading_add_axis_le (f : Envelope) (cfg : Fin 3 → JetProfile) (left : FlagDegree) :
    jetLeadingNumerator f cfg left + axisPrice (graphAxis f cfg) left ≤
      jetFlagCharge TailCorrections.original f cfg left := by
  rw [leading_linear f cfg left, axisPrice_add, jetFlagCharge_eq_axisPrice]
  apply axisPrice_mono
  intro i
  rw [jetLeadingNumerator_eq_list]
  unfold jetChargeAxisWithCorrections
  exact (le_max_left _ _).trans (le_max_right _ _)

private theorem profile_arithmetic (ids : Fin 6 × Fin 6 × Fin 6) (j : Fin 3) :
    3 * ((cellConfig ids j).derivativeOrder+1) ∣ terminalScale ∧
      (cellConfig ids j).derivativeOrder < 2130706433 := by
  let k : Fin 6 := (![ids.1, ids.2.1, ids.2.2] : Fin 3 → Fin 6) j
  have hk : cellConfig ids j = jetProfile k := by fin_cases j <;> rfl
  have all (k : Fin 6) : 3 * ((jetProfile k).derivativeOrder+1) ∣ terminalScale ∧
      (jetProfile k).derivativeOrder < 2130706433 := by
    fin_cases k <;> decide +kernel
  rw [hk]
  exact all k

private theorem cover_graph_and_leading {K : Type} (seeds : Finset K)
    (zero : Fin 3 → K → Prop) :
    seeds.card ≤ (seeds.filter (fun g => ∀ j, ¬ zero j g)).card +
      ∑ j : Fin 3, (seeds.filter (zero j)).card := by
  let good := seeds.filter (fun g => ∀ j, ¬ zero j g)
  let bad (j : Fin 3) := seeds.filter (zero j)
  have hcover : seeds ⊆ good ∪ Finset.univ.biUnion bad := by
    intro g hg
    by_cases h : ∀ j, ¬ zero j g
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hg, h⟩)
    · have h' : ∃ j, zero j g := by simpa only [not_forall, not_not] using h
      obtain ⟨j, hj⟩ := h'
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hg, hj⟩⟩)
  exact ((Finset.card_le_card hcover).trans (Finset.card_union_le _ _)).trans
    (Nat.add_le_add_left Finset.card_biUnion_le _)

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]

theorem incumbent_retained_profile_seed_card_mul_le
    (f : Envelope) (ids : Fin 6 × Fin 6 × Fin 6)
    (hmin : 1 ≤ f.slope ∧ 2 ≤ f.middle) (hshape : f.slope ≤ f.middle ∧ f.middle ≤ f.total)
    (hTotal : f.total < 2130706433)
    (hg : jetGatesWithCorrections TailCorrections.original f (cellConfig ids) = true)
    (D : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (ht : (f.pad 2).total ≤ 8870) (hy : (f.pad 2).middle ≤ 142) (hr : (f.pad 2).slope ≤ 31)
    (F : MvPolynomial (Fin 4) K) (hi : Irreducible F) (hpos : 0 < F.degreeOf (2 : Fin 4))
    (hbelow : Below (originalCumulativeFlag F) f.flag)
    (hbox : F ∈ globalCoefficientBox K D 131071 (f.pad 2).total (f.pad 2).slope)
    (hsupport : ResidualSupportData (f.paddedSupport 2) F)
    (hlarge : jetSourceCap (cellConfig ids) < wt residualTotalWeights F)
    (nodes : I ↪ K) (u₀ u₁ : I → K) (hI : Fintype.card I = 262144)
    (hsources : RetainedProfileSources ids F nodes u₀ u₁)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071)
    (hregular : ∀ g ∈ seeds, RegularSolution F (selected g) g)
    (hagreement : ∀ g ∈ seeds, 181068 ≤
      (Finset.univ.filter (fun i => (selected g).eval (nodes i) = u₀ i + g * u₁ i)).card)
    (hpencil : NoLargeSelectedPencil selected seeds 131071 81076) :
    seeds.card * terminalScale ≤
      jetFlagCharge TailCorrections.original f (cellConfig ids) (originalCumulativeFlag F) := by
  classical
  let _ : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
  let cfg := cellConfig ids
  let s := f.pad 2
  let left := originalCumulativeFlag F
  let supp := f.endpointSupport hmin hshape
  obtain ⟨source, hsources⟩ := hsources
  have hr3 : 3 ≤ s.slope := le_max_left _ _
  have hry : s.slope + 2 ≤ s.middle := le_max_right _ _
  have hyt : s.middle + 2 ≤ s.total := le_max_right _ _
  have hcellS : cellS s.slope + 2 = s.slope := by simp only [cellS]; omega
  have hcellYS : cellB s.middle s.slope + cellS s.slope + 3 = s.middle := by
    simp only [cellB, cellS]
    omega
  have hcellTotal : cellA s.total s.middle + cellB s.middle s.slope + cellS s.slope + 3 = s.total := by
    simp only [cellA, cellB, cellS]
    omega
  have hsupp : ResidualSupportData (cellSupport s.total s.middle s.slope) F := by
    constructor
    · simpa only [cellSupport, RCN198.support, hcellS] using (show wt residualSWeights F ≤ s.slope from hsupport.s_weight)
    · simpa only [cellSupport, RCN198.support, hcellYS] using (show wt residualYSWeights F ≤ s.middle from hsupport.ys_weight)
    · simpa only [cellSupport, RCN198.support, hcellTotal] using (show wt residualTotalWeights F ≤ s.total from hsupport.total_weight)
  have hfreeTotal : (cellSupport s.total s.middle s.slope).total ≤ 9678 := by
    simp only [cellSupport, RCN198.support, hcellTotal]
    exact ht.trans (by decide)
  have hderiv (j : Fin 3) : (source j).k = (cfg j).derivativeOrder := (hsources j).2.2.2.2.2.1
  have horder (j : Fin 3) : (cfg j).derivativeOrder + 1 = (source j).d := by
    simp only [Source.d, hderiv j]
  have hsourceFlag (j : Fin 3) : (source j).flag = (cfg j).moving := by
    obtain ⟨_, hB, hU, hT, _, hk, hn⟩ := hsources j
    simp only [Source.flag, Source.d, SecondJetRelaxedFlag.budgetFlag, JetProfile.moving,
      hB, hU, hT, hk, hn, Nat.sub_sub]
    rfl
  have hsourceDiv (j : Fin 3) : 3 * (source j).d ∣ terminalScale := by
    rw [←horder j]
    exact (profile_arithmetic ids j).1
  have hfact (j : Fin 3) : ((source j).k.factorial : GenericField K) ≠ 0 := by
    apply SecondJetOwnShape.factorial_ne
    rw [hderiv j]
    exact (profile_arithmetic ids j).2
  let zero (j : Fin 3) (g : K) := MvPolynomial.eval
    (selectedPoint (polynomialEmbedding K) selected g) ((source j).leading (polynomialEmbedding K)) = 0
  let good := seeds.filter (fun g => ∀ j, ¬ zero j g)
  let bad (j : Fin 3) := seeds.filter (zero j)
  have hGood := Finset.filter_subset (fun g => ∀ j, ¬ zero j g) seeds
  have hBad (j : Fin 3) := Finset.filter_subset (zero j) seeds
  have hgraph : good.card * terminalScale ≤ axisPrice (graphAxis f cfg) left := by
    have hc := regular_graph_seed_card_mul_le D s.total s.middle s.slope terminalScale hDlow hDchar
      ht hy hr hr3 hry hyt F hi hpos hbox hsupp selected good Finset.univ nodes u₀ u₁
      nodes.injective.injOn (by simpa only [Finset.card_univ] using hI)
      (fun _ hg => hdegree _ (hGood hg)) (fun _ hg => hagreement _ (hGood hg))
      (fun _ hg => (hregular _ (hGood hg)).1) (fun _ hg => (hregular _ (hGood hg)).2)
      (RCN243.noLargeSelectedPencil_mono selected seeds good 131071 81076 hGood hpencil)
      source (by decide) hsourceDiv (fun _ _ S _ => HFreeDir6813.hfree_stage_dir_of_gaps S hfreeTotal)
      SecondJetOwnShape.two_ne hfact (fun _ hg j => (Finset.mem_filter.mp hg).2 j)
      (graphAxis f cfg) (graphAxis_mono f cfg)
      (fun q => (originalGraphNumerator_eq_numeratorDir s hr3 hry cfg source hsourceFlag horder hsourceDiv q).symm.le.trans
        (graph_le_axis f cfg q))
      (fun q => identity_le_axis f cfg q hr3 hry)
    simpa only [Nat.mul_comm terminalScale] using hc
  have hlead : (∑ j : Fin 3, (bad j).card) * terminalScale ≤ jetLeadingNumerator f cfg left := by
    apply leading_counts_mul_le_jetLeadingNumerator (Fintype.card I) (fun j => (bad j).card)
      f cfg left supp rfl rfl rfl (by omega)
    intro j
    obtain ⟨h₁, h₂, hpair, _⟩ := incumbent_jet_pair_gates f cfg j hg
    have hc := profile_leading_seed_card_mul_le (cfg j) supp F (source j).P hi hpos
      (endpointSupport_of_flag_below F f hmin hshape hbelow) hTotal h₁ h₂ hpair
      nodes u₀ u₁ (by omega) (hsources j).1 ((profile_totalCap_le_jetSourceCap cfg j).trans_lt hlarge)
      selected (bad j) (fun g hg => hdegree g (hBad j hg))
      (fun g hg => hregular g (hBad j hg)) (fun g hg => (Finset.mem_filter.mp hg).2)
      (fun g hg => hagreement g (hBad j hg))
      (RCN243.noLargeSelectedPencil_mono selected seeds (bad j) 131071 81076 (hBad j) hpencil)
    exact hc
  calc
    _ ≤ (good.card + ∑ j : Fin 3, (bad j).card) * terminalScale :=
      Nat.mul_le_mul_right _ (cover_graph_and_leading seeds zero)
    _ = (∑ j : Fin 3, (bad j).card) * terminalScale + good.card * terminalScale := by
      rw [Nat.add_mul, Nat.add_comm]
    _ ≤ jetLeadingNumerator f cfg left + axisPrice (graphAxis f cfg) left := Nat.add_le_add hlead hgraph
    _ ≤ _ := leading_add_axis_le f cfg left

theorem individual_retained_profile_seed_card_mul_le
    (f : Envelope) (ids : Fin 6 × Fin 6 × Fin 6)
    (hmin : 1 ≤ f.slope ∧ 2 ≤ f.middle) (hshape : f.slope ≤ f.middle ∧ f.middle ≤ f.total)
    (hTotal : f.total < 2130706433)
    (hg : jetGatesWithCorrections TailCorrections.original f (cellConfig ids) = true)
    (D : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (ht : (f.pad 2).total ≤ 8870) (hy : (f.pad 2).middle ≤ 142) (hr : (f.pad 2).slope ≤ 31)
    (F : MvPolynomial (Fin 4) K) (hi : Irreducible F) (hpos : 0 < F.degreeOf (2 : Fin 4))
    (hbelow : Below (originalCumulativeFlag F) f.flag)
    (hbox : F ∈ globalCoefficientBox K D 131071 (f.pad 2).total (f.pad 2).slope)
    (hsupport : ResidualSupportData (f.paddedSupport 2) F)
    (hlarge : jetSourceCap (cellConfig ids) < wt residualTotalWeights F)
    (nodes : I ↪ K) (u₀ u₁ : I → K) (hI : Fintype.card I = 262144)
    (hsources : RetainedProfileSources ids F nodes u₀ u₁)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071)
    (hregular : ∀ g ∈ seeds, RegularSolution F (selected g) g)
    (hagreement : ∀ g ∈ seeds, 181068 ≤
      (Finset.univ.filter (fun i => (selected g).eval (nodes i) = u₀ i + g * u₁ i)).card)
    (hpencil : NoLargeSelectedPencil selected seeds 131071 81076) :
    seeds.card * terminalScale ≤
      jetLeadingNumerator f (cellConfig ids) (originalCumulativeFlag F) +
          axisPrice (graphAxis f (cellConfig ids)) (originalCumulativeFlag F) := by
  classical
  let _ : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
  let cfg := cellConfig ids
  let s := f.pad 2
  let left := originalCumulativeFlag F
  let supp := f.endpointSupport hmin hshape
  obtain ⟨source, hsources⟩ := hsources
  have hr3 : 3 ≤ s.slope := le_max_left _ _
  have hry : s.slope + 2 ≤ s.middle := le_max_right _ _
  have hyt : s.middle + 2 ≤ s.total := le_max_right _ _
  have hcellS : cellS s.slope + 2 = s.slope := by simp only [cellS]; omega
  have hcellYS : cellB s.middle s.slope + cellS s.slope + 3 = s.middle := by
    simp only [cellB, cellS]
    omega
  have hcellTotal : cellA s.total s.middle + cellB s.middle s.slope + cellS s.slope + 3 = s.total := by
    simp only [cellA, cellB, cellS]
    omega
  have hsupp : ResidualSupportData (cellSupport s.total s.middle s.slope) F := by
    constructor
    · simpa only [cellSupport, RCN198.support, hcellS] using (show wt residualSWeights F ≤ s.slope from hsupport.s_weight)
    · simpa only [cellSupport, RCN198.support, hcellYS] using (show wt residualYSWeights F ≤ s.middle from hsupport.ys_weight)
    · simpa only [cellSupport, RCN198.support, hcellTotal] using (show wt residualTotalWeights F ≤ s.total from hsupport.total_weight)
  have hfreeTotal : (cellSupport s.total s.middle s.slope).total ≤ 9678 := by
    simp only [cellSupport, RCN198.support, hcellTotal]
    exact ht.trans (by decide)
  have hderiv (j : Fin 3) : (source j).k = (cfg j).derivativeOrder := (hsources j).2.2.2.2.2.1
  have horder (j : Fin 3) : (cfg j).derivativeOrder + 1 = (source j).d := by
    simp only [Source.d, hderiv j]
  have hsourceFlag (j : Fin 3) : (source j).flag = (cfg j).moving := by
    obtain ⟨_, hB, hU, hT, _, hk, hn⟩ := hsources j
    simp only [Source.flag, Source.d, SecondJetRelaxedFlag.budgetFlag, JetProfile.moving,
      hB, hU, hT, hk, hn, Nat.sub_sub]
    rfl
  have hsourceDiv (j : Fin 3) : 3 * (source j).d ∣ terminalScale := by
    rw [←horder j]
    exact (profile_arithmetic ids j).1
  have hfact (j : Fin 3) : ((source j).k.factorial : GenericField K) ≠ 0 := by
    apply SecondJetOwnShape.factorial_ne
    rw [hderiv j]
    exact (profile_arithmetic ids j).2
  let zero (j : Fin 3) (g : K) := MvPolynomial.eval
    (selectedPoint (polynomialEmbedding K) selected g) ((source j).leading (polynomialEmbedding K)) = 0
  let good := seeds.filter (fun g => ∀ j, ¬ zero j g)
  let bad (j : Fin 3) := seeds.filter (zero j)
  have hGood := Finset.filter_subset (fun g => ∀ j, ¬ zero j g) seeds
  have hBad (j : Fin 3) := Finset.filter_subset (zero j) seeds
  have hgraph : good.card * terminalScale ≤ axisPrice (graphAxis f cfg) left := by
    have hc := regular_graph_seed_card_mul_le D s.total s.middle s.slope terminalScale hDlow hDchar
      ht hy hr hr3 hry hyt F hi hpos hbox hsupp selected good Finset.univ nodes u₀ u₁
      nodes.injective.injOn (by simpa only [Finset.card_univ] using hI)
      (fun _ hg => hdegree _ (hGood hg)) (fun _ hg => hagreement _ (hGood hg))
      (fun _ hg => (hregular _ (hGood hg)).1) (fun _ hg => (hregular _ (hGood hg)).2)
      (RCN243.noLargeSelectedPencil_mono selected seeds good 131071 81076 hGood hpencil)
      source (by decide) hsourceDiv (fun _ _ S _ => HFreeDir6813.hfree_stage_dir_of_gaps S hfreeTotal)
      SecondJetOwnShape.two_ne hfact (fun _ hg j => (Finset.mem_filter.mp hg).2 j)
      (graphAxis f cfg) (graphAxis_mono f cfg)
      (fun q => (originalGraphNumerator_eq_numeratorDir s hr3 hry cfg source hsourceFlag horder hsourceDiv q).symm.le.trans
        (graph_le_axis f cfg q))
      (fun q => identity_le_axis f cfg q hr3 hry)
    simpa only [Nat.mul_comm terminalScale] using hc
  have hlead : (∑ j : Fin 3, (bad j).card) * terminalScale ≤ jetLeadingNumerator f cfg left := by
    apply leading_counts_mul_le_jetLeadingNumerator (Fintype.card I) (fun j => (bad j).card)
      f cfg left supp rfl rfl rfl (by omega)
    intro j
    obtain ⟨h₁, h₂, hpair, _⟩ := incumbent_jet_pair_gates f cfg j hg
    have hc := profile_leading_seed_card_mul_le (cfg j) supp F (source j).P hi hpos
      (endpointSupport_of_flag_below F f hmin hshape hbelow) hTotal h₁ h₂ hpair
      nodes u₀ u₁ (by omega) (hsources j).1 ((profile_totalCap_le_jetSourceCap cfg j).trans_lt hlarge)
      selected (bad j) (fun g hg => hdegree g (hBad j hg))
      (fun g hg => hregular g (hBad j hg)) (fun g hg => (Finset.mem_filter.mp hg).2)
      (fun g hg => hagreement g (hBad j hg))
      (RCN243.noLargeSelectedPencil_mono selected seeds (bad j) 131071 81076 (hBad j) hpencil)
    exact hc
  calc
    _ ≤ (good.card + ∑ j : Fin 3, (bad j).card) * terminalScale :=
      Nat.mul_le_mul_right _ (cover_graph_and_leading seeds zero)
    _ = (∑ j : Fin 3, (bad j).card) * terminalScale + good.card * terminalScale := by
      rw [Nat.add_mul, Nat.add_comm]
    _ ≤ jetLeadingNumerator f cfg left + axisPrice (graphAxis f cfg) left := Nat.add_le_add hlead hgraph

end
end ProximityPrize.SubmissionLower.K6833Residual

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
