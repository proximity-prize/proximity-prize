import ProximityPrize.SubmissionLower.MovingFiberRegularData6811
import ProximityPrize.SubmissionLower.MovingFiberInterpolation6811
import ProximityPrize.SubmissionLower.MovingFiberTotalAvoidance6811

namespace ProximityPrize.SubmissionLower.MovingFiberProfile6811
open scoped Classical BigOperators
open MvPolynomial RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN174 RCN222 RCN234 RCN238 RCN243 RCN260 RCN319 RCN327
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider
open MovingFiberRegularData6811 MovingFiberThreeSources6811 MovingFiberInterpolation6811 MovingFiberTotalAvoidance6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

structure Params where
  m : ℕ
  B : ℕ
  s : ℕ
  U : ℕ
  L : ℕ
  k : ℕ
  n0 : ℕ
  deriving DecidableEq, Repr

def Params.d (P : Params) : ℕ := P.k+1
def Params.flag (P : Params) : FlagDegree := SecondJetRelaxedFlag.budgetFlag P.B P.U P.L P.d P.n0
def Params.WellFormed (P : Params) : Prop :=
  2*P.s ≤ P.B ∧ P.B ≤ P.U ∧ P.U ≤ P.L ∧ P.k ≤ P.s ∧ P.s < P.m ∧
    P.k+1 ≤ P.n0 ∧ 2*(P.n0-(P.k+1)) ≤ P.B ∧ P.s < 2130706433
def number (cfg : Fin 3 → Params) (scale t y r : ℕ) (f : FlagDegree) : ℕ :=
  scale/3*flagMixed f (MovingFiberRetainedStage6811.hfreeFirst t y r) (cellNormal t y r) +
    ∑ j : Fin 3, (4*(w+1)*weight (cellNormal t y r) j*(scale/(3*(cfg j).d))+
      65539*weight (MovingFiberRetainedStage6811.rawFirstFlag t y r) j*(scale/(cfg j).d))*
      flagMixed f (MovingFiberThreeSources6811.direction j) (cfg j).flag

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {nodes : I ↪ K} {u0 u1 : I → K}

def helperCap (S : Data nodes u0 u1) (P : Params) : ℕ :=
  AsymmetricHelper.leftRegularCountCap (S.pair (P.B+P.s*(S.r-1)) (P.U+P.s*(S.y-1)) (P.L+P.s*(S.t-1)))
def coefficientCap (S : Data nodes u0 u1) (P : Params) : ℕ :=
  AsymmetricHelper.leftRegularCountCap (S.pair P.B P.U P.L)
def bound (S : Data nodes u0 u1) (cfg : Fin 3 → Params) (scale : ℕ) : ℕ :=
  max (Finset.univ.sup (fun j : Fin 3 => helperCap S (cfg j)))
    (number cfg scale S.t S.y S.r (originalCumulativeFlag S.F)/scale +
      ∑ j : Fin 3, coefficientCap S (cfg j))

theorem count_of_interpolants
    (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (cfg : Fin 3 → Params) (hc : ∀ j, (cfg j).WellFormed)
    (scale : ℕ) (hscale : 0 < scale) (hscaleDiv : ∀ j, 3*(cfg j).d ∣ scale)
    (hfree : ∀ (G : Finset K) (fl : FlagDegree) (S' : RCN159.ResidualStage (polynomialEmbedding K) G
      ⇑nodes 2130706433 80869 fl w (cellSupport S.t S.y S.r)), S'.F = S.F →
      MovingFiberRetainedStage6811.HFreeStage S')
    (P : Fin 3 → SecondJetSupport.Poly (K := K))
    (hP : ∀ j, Interpolant (cfg j).m (cfg j).B (cfg j).s (cfg j).U (cfg j).L (cfg j).k (cfg j).n0 nodes u0 u1 (P j))
    (hL : ∀ j, (cfg j).L < wt residualTotalWeights S.F)
    (hHelperGates : ∀ j, S.PairGates ((cfg j).B+(cfg j).s*(S.r-1))
      ((cfg j).U+(cfg j).s*(S.y-1)) ((cfg j).L+(cfg j).s*(S.t-1)))
    (hCoefficientGates : ∀ j, S.PairGates (cfg j).B (cfg j).U (cfg j).L)
    (hidentity : ∀ f : FlagDegree, scale*131073*80870*
      identityCurveDegree f (cellA S.t S.y) (cellB S.y S.r) (cellS S.r) w ≤
        50204*number cfg scale S.t S.y S.r f) :
    S.seeds.card ≤ bound S cfg scale := by
  classical
  have hshape (j : Fin 3) : ∀ e ∈ (P j).support, 2*e 1+e 3 ≤ (cfg j).B ∧
      e 1+e 2+e 3 ≤ (cfg j).U ∧ e 1+e 2+e 3+e 4 ≤ (cfg j).L := by
    intro e he
    have h := (hP j).2.1 e he
    exact ⟨h.1,h.2.2.1,h.2.2.2.1⟩
  have hS (j : Fin 3) : ∀ e ∈ (P j).support, e 1 ≤ (cfg j).s := fun e he => ((hP j).2.1 e he).2.1
  have factorial (j : Fin 3) (d : ℕ) (hd : d ≤ (cfg j).s) : (d.factorial : K) ≠ 0 :=
    SecondJetOwnShape.factorial_ne d (hd.trans_lt (hc j).2.2.2.2.2.2.2)
  have alternatives (j : Fin 3) := helper_or_divisibility (P j) S.F
    (cfg j).m (cfg j).B (cfg j).s (cfg j).U (cfg j).L (cfg j).k (cfg j).n0 S.r S.y S.t
    nodes u0 u1 (hP j) S.irreducible (hL j) (hc j).1
    (by have := hc j; unfold Params.WellFormed at this; omega)
    (by have := hc j; unfold Params.WellFormed at this; omega)
    (hc j).2.2.2.1 (hc j).2.2.2.2.1
    (by have := S.rpos; omega) (by have := S.ry; omega) (by have := S.yt; omega)
    S.weights (factorial j)
  by_cases hall : ∀ j : Fin 3, (cfg j).n0 ≤ (SecondJetCoefficients.asS (P j)).natDegree ∧
      ∀ d ≤ (cfg j).k, S.F ∣ SecondJetClearedHelper.helper (P j) S.F ((cfg j).s-d) d
  · let source : Fin 3 → Source S.F := fun j => {
      P := P j, B := (cfg j).B, U := (cfg j).U, T := (cfg j).L,
      s := (cfg j).s, k := (cfg j).k, n0 := (cfg j).n0,
      hS := hS j, hshape := hshape j, hBU := (hc j).2.1,
      hUT := (hc j).2.2.1, hdn := (hc j).2.2.2.2.2.1,
      hB := (hc j).2.2.2.2.2.2.1, hn := (hall j).1, hdiv := (hall j).2 }
    let point := selectedPoint (polynomialEmbedding K) S.selected
    let LC := fun j : Fin 3 => surfaceMap (polynomialEmbedding K) (SecondJetCoefficients.asS (P j)).leadingCoeff
    let Good := S.seeds.filter (fun gamma => ∀ j : Fin 3, MvPolynomial.eval (point gamma) (LC j) ≠ 0)
    let Bad := fun j : Fin 3 => S.seeds.filter (fun gamma => MvPolynomial.eval (point gamma) (LC j) = 0)
    let SG := S.restrict Good (Finset.filter_subset _ _)
    have hnum (f : FlagDegree) : MovingFiberRetainedStage6811.numerator source scale S.t S.y S.r f =
        number cfg scale S.t S.y S.r f := rfl
    have h2 : (2 : GenericField K) ≠ 0 := SecondJetOwnShape.two_ne
    have hf (j : Fin 3) : ((source j).k.factorial : GenericField K) ≠ 0 :=
      SecondJetOwnShape.factorial_ne (cfg j).k (by
        have := hc j; unfold Params.WellFormed at this; omega)
    have hgood : ∀ gamma ∈ SG.seeds, ∀ j,
        MvPolynomial.eval (selectedPoint (polynomialEmbedding K) SG.selected gamma)
          ((source j).leading (polynomialEmbedding K)) ≠ 0 := by
      intro gamma hgamma j
      exact (Finset.mem_filter.mp hgamma).2 j
    have hid (f : FlagDegree) : scale*131073*80870*
        identityCurveDegree f (cellA S.t S.y) (cellB S.y S.r) (cellS S.r) w ≤
          50204*MovingFiberRetainedStage6811.numerator source scale S.t S.y S.r f := by
      rw [hnum]
      exact hidentity f
    have hg := MovingFiberRegularGeometry6811.regular_seed_bound
      SG.D SG.t SG.y SG.r scale SG.Dlow SG.Dchar SG.tbound SG.ybound SG.rbound SG.rpos SG.ry SG.yt
      SG.F SG.irreducible SG.rdegree SG.box SG.support SG.selected SG.seeds Finset.univ nodes u0 u1
      nodes.injective.injOn (by simpa only [Finset.card_univ] using hI)
      SG.degree SG.agreement SG.solution SG.regular SG.noPencil
      source hscale hscaleDiv hfree h2 hf hgood hid
    have hGood : Good.card ≤ number cfg scale S.t S.y S.r (originalCumulativeFlag S.F)/scale := by
      apply (Nat.le_div_iff_mul_le hscale).mpr
      rw [← hnum]
      dsimp only [SG,Data.restrict] at hg
      simpa only [Nat.mul_comm] using hg
    have hBad (j : Fin 3) : (Bad j).card ≤ coefficientCap S (cfg j) := by
      let SB := S.restrict (Bad j) (Finset.filter_subset _ _)
      have hnot := SecondJetTotalAvoidance.leading_not_dvd (P j) (hP j).1 S.F (cfg j).L
        (fun e he => (hshape j e he).2.2) (hL j)
      have hrel : IsRelPrime SB.F (SecondJetCoefficients.asS (P j)).leadingCoeff :=
        S.irreducible.isRelPrime_iff_not_dvd.mpr hnot.2
      apply SB.proper_count_left hI _ (cfg j).B (cfg j).U (cfg j).L hrel
        (SecondJetPairBounds.leading_degree_caps (P j) (cfg j).B (cfg j).U (cfg j).L (hshape j))
        (hCoefficientGates j)
      intro gamma hgamma
      have hz : MvPolynomial.eval (point gamma) (LC j) = 0 := (Finset.mem_filter.mp hgamma).2
      change MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (surfaceMap (polynomialEmbedding K) (SecondJetCoefficients.asS (P j)).leadingCoeff) = 0 at hz
      rw [selectedPoint_surface_evaluation] at hz
      dsimp only [SB,Data.restrict]
      exact (polynomialEmbedding_injective K) (by simpa only [map_zero] using hz)
    have hcover : S.seeds ⊆ Good ∪ Finset.univ.biUnion Bad := by
      intro gamma hgamma
      by_cases hg : ∀ j : Fin 3, MvPolynomial.eval (point gamma) (LC j) ≠ 0
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hgamma,hg⟩)
      · have hex : ∃ j : Fin 3, MvPolynomial.eval (point gamma) (LC j) = 0 := by simpa only [not_forall,not_not] using hg
        obtain ⟨j,hj⟩ := hex
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hgamma,hj⟩⟩)
    have hcard : S.seeds.card ≤ Good.card+∑ j : Fin 3, (Bad j).card :=
      ((Finset.card_le_card hcover).trans (Finset.card_union_le _ _)).trans
        (Nat.add_le_add_left Finset.card_biUnion_le _)
    exact (hcard.trans (Nat.add_le_add hGood (Finset.sum_le_sum (fun j _ => hBad j)))).trans (le_max_right _ _)
  · obtain ⟨j,hj⟩ := not_forall.mp hall
    rcases alternatives j with ⟨Q,hrel,hw,hzero⟩ | hret
    · have hb := S.proper_count_left hI Q ((cfg j).B+(cfg j).s*(S.r-1))
        ((cfg j).U+(cfg j).s*(S.y-1)) ((cfg j).L+(cfg j).s*(S.t-1)) hrel
        (SecondJetPairBounds.degree_caps_of_weights Q _ _ _ hw) (hHelperGates j) (by
          intro gamma hgamma
          apply hzero (S.selected gamma) (S.degree gamma hgamma) gamma
            (Finset.univ.filter (fun i => (S.selected gamma).eval (nodes i) = u0 i+gamma*u1 i))
            (S.agreement gamma hgamma) _ (S.solution gamma hgamma)
          intro i hi
          simpa only [mul_comm] using (Finset.mem_filter.mp hi).2)
      exact (hb.trans (Finset.le_sup (f := fun j : Fin 3 => helperCap S (cfg j)) (Finset.mem_univ j))).trans (le_max_left _ _)
    · exact (hj hret).elim

#print axioms count_of_interpolants
end
end ProximityPrize.SubmissionLower.MovingFiberProfile6811
