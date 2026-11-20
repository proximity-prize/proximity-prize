import ProximityPrize.SubmissionLower.Koala6844TerminalRegular
import ProximityPrize.SubmissionLower.Koala6844TerminalLongRates
import ProximityPrize.SubmissionLower.Koala6844VirtualShortCarrier


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open scoped Classical BigOperators
open RCN081 RCN095 RCN130 RCN135 RCN136 RCN138 RCN140 RCN156 RCN167 RCN174 RCN234 RCN238 RCN266 RCN275 RCN286 RCN319
open LocatorHybridCells MovingFiberThreeSources6811 Koala6844Receipts Koala6844VirtualShort
open SecondJetCoefficients SecondJetCoefficientSpecialization

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

variable {K I : Type} [Field K]

def leadValue {F : MvPolynomial (Fin 4) K} (S : Source F)
    (selected : K → Polynomial K) (z : K) : GenericField K :=
  MvPolynomial.eval (RCN238.selectedPoint (polynomialEmbedding K) selected z) (S.leading (polynomialEmbedding K))

theorem leadValue_zero {F : MvPolynomial (Fin 4) K} (S : Source F)
    (selected : K → Polynomial K) (z : K) :
    leadValue S selected z = 0 ↔ coefficientSpecialize (selected z) z (asS S.P).leadingCoeff = 0 := by
  change _ ↔ (coefficientSpecialize (selected z) z).toRingHom (asS S.P).leadingCoeff = 0
  rw [leadValue,Source.leading,SecondJetClearedHelper.coefficientSpecialize_eq]
  have h := actual_generic_initial_zero_iff K (selected z) z (asS S.P).leadingCoeff
  simp only [canonical_geometricSurfaceMap,RCN135.initialPoint,
    RCN135.coefficientEmbedding,RCN135.initialCoordinate] at h ⊢
  exact h

def Route (F : MvPolynomial (Fin 4) K) (g : Flag) (shape : SourceShape)
    (seeds : Finset K) (selected : K → Polynomial K) : Prop :=
  (∃ Q, ProperCut F Q (helperFlag g shape).r (helperFlag g shape).y (helperFlag g shape).t seeds selected) ∨
  ∃ S : Source F,
    S.d = shape.k+1 ∧ S.flag = geometryFlag shape.graphIncrement ∧
    S.B = shape.B ∧ S.U = shape.U ∧ S.T = shape.L+shape.q

theorem regular_pair_payment [CharP K 2130706433]
    (H : MvPolynomial (Fin 4) K) (F : RegularIndex H)
    (g right : Flag) (hr : 3 ≤ g.r) (hy : g.r+2 ≤ g.y) (ht : g.y ≤ g.t) (htchar : g.t < 2130706433)
    (hFfit : (physicalFlag F.1).cumulativeLE g) (hright : right.ordered) (hmixed : pairGate g right = true)
    (nodes : Finset I) (x u₀ u₁ : I → K) (selected : K → Polynomial K) (seeds Γ : Finset K)
    (data : TerminalSeedData nodes x u₀ u₁ selected seeds)
    (hΓ : Γ ⊆ regularSeeds H selected seeds F)
    (Q : MvPolynomial (Fin 4) K) (hQ : ProperCut F.1 Q right.r right.y right.t Γ selected) :
    graphScale * Γ.card ≤ dot (physicalFlag F.1).increments (graphPairRates right (graphDirection g)) := by
  obtain ⟨hirr,_,hpos⟩ := positiveRFactors_spec H F.1 F.2
  have hh := data.subset (hΓ.trans (regularSeeds_subset H selected seeds F))
  have hsol (z : K) (hz : z ∈ Γ) : RegularSolution F.1 (selected z) z := (Finset.mem_filter.mp (hΓ hz)).2
  have hcount := regular_terminal_pair_bound F.1 Q hirr hpos hQ.1 g.t g.y g.r hr hy ht htchar
    (physical_support F.1 g hr hy ht hFfit) (geometryFlag right.increments)
    (physical_cut_flag Q right hright hQ.2.1) (pair_gate_mixed g right hright hmixed).2
    selected Γ nodes x u₀ u₁ hh.injective hh.nodes_card hh.selected_degree hh.agreement
    (fun z hz => (hsol z hz).1) (fun z hz => (hsol z hz).2) hQ.2.2 hh.noPencil
  rw [physicalFlag_increments]
  exact scaled_pair_to_receipt g hr hy ht (originalCumulativeFlag F.1) right.increments Γ.card hcount

private theorem ordered_helper (g : Flag) (shape : SourceShape)
    (hg : g.ordered) (h : shape.carrierFlag.ordered) : (helperFlag g shape).ordered := by
  exact ⟨Nat.add_le_add h.1 (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hg.1 1)),
    Nat.add_le_add h.2 (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hg.2 1))⟩

private theorem card_graph_cover {F : MvPolynomial (Fin 4) K} (S : Fin 3 → Source F)
    (selected : K → Polynomial K) (Γ : Finset K) :
    Γ.card ≤ (Γ.filter (fun z => ∀ j, leadValue (S j) selected z ≠ 0)).card +
      (Γ.filter (fun z => leadValue (S 0) selected z = 0)).card +
      (Γ.filter (fun z => leadValue (S 1) selected z = 0)).card +
      (Γ.filter (fun z => leadValue (S 2) selected z = 0)).card := by
  let good := Γ.filter (fun z => ∀ j, leadValue (S j) selected z ≠ 0)
  let bad (j : Fin 3) := Γ.filter (fun z => leadValue (S j) selected z = 0)
  have h : Γ ⊆ ((good ∪ bad 0) ∪ bad 1) ∪ bad 2 := by
    intro z hz
    by_cases hgood : ∀ j, leadValue (S j) selected z ≠ 0
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz,hgood⟩)))
    · push Not at hgood
      obtain ⟨j,hj⟩ := hgood
      have hbad : z ∈ bad j := Finset.mem_filter.mpr ⟨hz,hj⟩
      fin_cases j
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hbad))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hbad)
      · exact Finset.mem_union_right _ hbad
  exact (Finset.card_le_card h).trans <| (Finset.card_union_le _ _).trans
    (Nat.add_le_add_right ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _)

private theorem graphScale_pos : 0 < graphScale := by decide
private theorem graphScale_gap : 49890 ∣ graphScale := by decide

attribute [local irreducible] graphScale

private theorem axis_cost_mono (a : FlagIncrements) (h : a.total ≤ a.middle ∧ a.middle ≤ a.slope) :
    a.axis (0 : Fin 3).val ≤ a.axis (1 : Fin 3).val ∧
      a.axis (1 : Fin 3).val ≤ a.axis (2 : Fin 3).val := by
  cases a
  exact h

private theorem regular_graph_payment [CharP K 2130706433]
    (H : MvPolynomial (Fin 4) K) (F : RegularIndex H) (D : Nat)
    (hD : 131072 ≤ D) (hDchar : D < 2130706433)
    (hcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071) F.1 ≤ D-1)
    (g : Flag) (hr : 3 ≤ g.r) (hy : g.r+2 ≤ g.y) (hyt : g.y+2 ≤ g.t)
    (gates : GraphGates g.t g.y g.r) (hfg : (physicalFlag F.1).cumulativeLE g)
    (src : Sources) (S : Fin 3 → Source F.1)
    (hd : ∀ j, (S j).d = (shapeAt src j).k+1)
    (hflag : ∀ j, (S j).flag = geometryFlag (shapeAt src j).graphIncrement)
    (hdiv : ∀ j : Fin 3, 3*(shapeAt src j).k+3 ∣ graphScale)
    (hk : ∀ j : Fin 3, (shapeAt src j).k < 2130706433)
    (nodes : Finset I) (x u₀ u₁ : I → K) (selected : K → Polynomial K) (seeds : Finset K)
    (data : TerminalSeedData nodes x u₀ u₁ selected seeds) :
    let good := (regularSeeds H selected seeds F).filter (fun z => ∀ j, leadValue (S j) selected z ≠ 0)
    graphScale * good.card ≤ dot (physicalFlag F.1).increments (graphCore g src) := by
  let Γ := regularSeeds H selected seeds F
  let left := (physicalFlag F.1).increments
  let good := Γ.filter (fun z => ∀ j, leadValue (S j) selected z ≠ 0)
  have ht : g.y ≤ g.t := (Nat.le_add_right g.y 2).trans hyt
  have hgood := data.subset ((Finset.filter_subset _ _).trans (regularSeeds_subset H selected seeds F))
    (sub := good)
  have hsol (z : K) (hz : z ∈ Γ) : RegularSolution F.1 (selected z) z := (Finset.mem_filter.mp hz).2
  have hGsol (z : K) (hz : z ∈ good) := hsol z (Finset.mem_filter.mp hz).1
  have hchar : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
  let _ : CharP (GenericField K) 2130706433 := hchar
  have htwo : (2 : GenericField K) ≠ 0 := by
    intro hz
    have hh := (CharP.cast_eq_zero_iff (GenericField K) 2130706433 2).1 (by exact hz)
    omega
  have hfact (j : Fin 3) : ((S j).k.factorial : GenericField K) ≠ 0 := by
    have hd' : (S j).k = (shapeAt src j).k := Nat.add_right_cancel (hd j)
    rw [hd']
    exact RCN347.factorial_cast_ne_zero_below_characteristic 2130706433 _ (hk j)
  have hscaleDiv (j : Fin 3) : 3*(S j).d ∣ graphScale := by
    rw [hd j,Nat.mul_add,Nat.mul_one]
    exact hdiv j
  obtain ⟨hirr,_,hpos⟩ := positiveRFactors_spec H F.1 F.2
  have hgraph := regular_graph_bound D g.t g.y g.r graphScale hD hDchar gates hr hy hyt
    F.1 hirr hpos (physical_box F.1 D (Nat.lt_of_lt_of_le (by decide : 0 < 131072) hD) hcontact g hfg)
    (physical_support F.1 g hr hy ht hfg) selected good nodes x u₀ u₁ hgood.injective hgood.nodes_card
    hgood.selected_degree hgood.agreement (fun z hz => (hGsol z hz).1) (fun z hz => (hGsol z hz).2)
    hgood.noPencil S graphScale_pos hscaleDiv htwo hfact (fun z hz j => (Finset.mem_filter.mp hz).2 j)
    graphScale_gap (fun j => (graphCore g src).axis j.val) (axis_cost_mono _ (long_graph_cost_mono g src))
    (long_graph_identity_le g src · hr hy ht)
    (long_graph_numerator_le S src g hr hy ht hd hflag hdiv)
  have hgraph' : graphScale * good.card ≤ dot left (graphCore g src) := by
    have hconv := charge_dot_eq (graphCore g src) (originalCumulativeFlag F.1)
    have hconv' := congrArg (fun f => dot f (graphCore g src)) (physicalFlag_increments F.1).symm
    exact hgraph.trans_eq (hconv.trans hconv')
  exact hgraph'

private theorem multiply_four (m a b c d : Nat) :
    m*(a+b+c+d) = m*a+m*b+m*c+m*d := by
  simp only [Nat.mul_add]

private theorem rotate_four (a b c d : Nat) : a+b+c+d = b+c+d+a := by
  ac_rfl

theorem long_regular_payment [CharP K 2130706433]
    (H : MvPolynomial (Fin 4) K) (F : RegularIndex H) (D : Nat)
    (hD : 131072 ≤ D) (hDchar : D < 2130706433)
    (hcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071) F.1 ≤ D-1)
    (scope : Flag) (src : Sources) (rate : Rates) (hp : LongRatesData scope src rate)
    (hfit : (physicalFlag F.1).cumulativeLE scope) (hlarge : src.totalCap < (physicalFlag F.1).t)
    (hshape : ∀ j : Fin 3, (shapeAt src j).carrierFlag.ordered)
    (hdiv : ∀ j : Fin 3, 3*(shapeAt src j).k+3 ∣ graphScale)
    (hk : ∀ j : Fin 3, (shapeAt src j).k < 2130706433)
    (nodes : Finset I) (x u₀ u₁ : I → K) (selected : K → Polynomial K) (seeds : Finset K)
    (data : TerminalSeedData nodes x u₀ u₁ selected seeds)
    (routes : ∀ j : Fin 3, Route F.1 (padFlag scope 2) (shapeAt src j) (regularSeeds H selected seeds F) selected) :
    rate.denominator * (regularSeeds H selected seeds F).card ≤
      dot (physicalFlag F.1).increments rate.numerator := by
  let g := padFlag scope 2
  let Γ := regularSeeds H selected seeds F
  let left := (physicalFlag F.1).increments
  obtain ⟨hr,hy,hyt⟩ := pad_shape scope 2
  have ht : g.y ≤ g.t := (Nat.le_add_right g.y 2).trans hyt
  have hg : g.ordered := ⟨(Nat.le_add_right g.r 2).trans hy,ht⟩
  have gates := hp.gates
  have htchar : g.t < 2130706433 := gates.total_le.trans_lt (by decide)
  have hfg : (physicalFlag F.1).cumulativeLE g :=
    ⟨hfit.1.trans (below_pad scope 2).1,hfit.2.1.trans (below_pad scope 2).2.1,
      hfit.2.2.trans (below_pad scope 2).2.2⟩
  have hden := congrArg (· * Γ.card) hp.denom
  apply hden.le.trans
  by_cases hcut : ∃ j : Fin 3, ∃ Q,
      ProperCut F.1 Q (helperFlag g (shapeAt src j)).r (helperFlag g (shapeAt src j)).y
        (helperFlag g (shapeAt src j)).t Γ selected
  · obtain ⟨j,Q,hQ⟩ := hcut
    exact (regular_pair_payment H F g _ hr hy ht htchar hfg (ordered_helper g _ hg (hshape j))
      (hp.helperGate j) nodes x u₀ u₁ selected seeds Γ data (fun _ hz => hz) Q hQ).trans (hp.helper_le left j)
  · have hroute (j : Fin 3) : ∃ S : Source F.1, S.d = (shapeAt src j).k+1 ∧
        S.flag = geometryFlag (shapeAt src j).graphIncrement ∧
        S.B = (shapeAt src j).B ∧ S.U = (shapeAt src j).U ∧ S.T = (shapeAt src j).L+(shapeAt src j).q :=
      (routes j).resolve_left (fun ⟨Q,hQ⟩ => hcut ⟨j,Q,hQ⟩)
    choose S hd hflag hB hU hT using hroute
    let good := Γ.filter (fun z => ∀ j, leadValue (S j) selected z ≠ 0)
    let bad (j : Fin 3) := Γ.filter (fun z => leadValue (S j) selected z = 0)
    have hgraph' : graphScale * good.card ≤ dot left (graphCore g src) :=
      regular_graph_payment H F D hD hDchar hcontact g hr hy hyt gates hfg src S hd hflag hdiv hk
        nodes x u₀ u₁ selected seeds data
    have hirr := (positiveRFactors_spec H F.1 F.2).1
    have hlead (j : Fin 3) : graphScale * (bad j).card ≤ dot left (leadRates g (shapeAt src j)) := by
      let p := shapeAt src j
      have hcap : p.L+p.q ≤ src.totalCap := by
        fin_cases j
        · exact le_max_left _ _
        · exact (le_max_left _ _).trans (le_max_right _ _)
        · exact (le_max_right _ _).trans (le_max_right _ _)
      have hP : (S j).P ≠ 0 := by
        intro hz
        have hn := (S j).hn
        have hd' := (S j).hdn
        simp only [hz,map_zero,Polynomial.natDegree_zero] at hn
        change (S j).k+1 ≤ (S j).n0 at hd'
        omega
      have hs := (S j).hshape
      rw [hB j,hU j,hT j] at hs
      have hQ := leading_properCut F.1 (S j).P p.B p.U (p.L+p.q) hirr hP (hcap.trans_lt hlarge)
        hs (bad j) selected
        (fun z hz => (leadValue_zero (S j) selected z).mp (Finset.mem_filter.mp hz).2)
      exact regular_pair_payment H F g p.carrierFlag hr hy ht htchar hfg (hshape j)
        (hp.leadGate j) nodes x u₀ u₁ selected seeds (bad j) data
        (Finset.filter_subset _ _) _ hQ
    have hm := Nat.mul_le_mul_left graphScale (card_graph_cover S selected Γ)
    have hs := multiply_four graphScale good.card (bad 0).card (bad 1).card (bad 2).card
    have hh := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hgraph' (hlead 0)) (hlead 1)) (hlead 2)
    have hrates := rotate_four (dot left (graphCore g src)) (dot left (leadRates g src.z))
      (dot left (leadRates g src.yz)) (dot left (leadRates g src.all))
    exact (hm.trans_eq hs).trans (hh.trans_eq hrates) |>.trans (hp.lead_graph_le left)

end
end ProximityPrize.SubmissionLower.Koala6844Terminal
