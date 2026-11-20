import ProximityPrize.SubmissionLower.Koala6844TerminalShortRates
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPhysicalPair


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open scoped Classical
open RCN081 RCN095 RCN130 RCN140 RCN156 RCN167 RCN174 RCN198 RCN234 RCN238 RCN243 RCN266 RCN275 RCN286 RCN319
open LocatorHybridCells Koala6844Receipts

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

variable {K I : Type} [Field K]

def physicalFlag (F : MvPolynomial (Fin 4) K) : Flag :=
  ⟨wt residualSWeights F,wt residualYSWeights F,wt residualTotalWeights F⟩

theorem physicalFlag_ordered (F : MvPolynomial (Fin 4) K) : (physicalFlag F).ordered :=
  residual_weight_nested F

theorem physicalFlag_increments (F : MvPolynomial (Fin 4) K) :
    (physicalFlag F).increments = increments (originalCumulativeFlag F) := by
  obtain ⟨hr,hy,ht⟩ := originalCumulativeFlag_cumulative F
  have h₀ : wt residualTotalWeights F - wt residualYSWeights F = (originalCumulativeFlag F).zOnly := by omega
  have h₁ : wt residualYSWeights F - wt residualSWeights F = (originalCumulativeFlag F).yz := by omega
  exact congrArg₂ (fun a b => FlagIncrements.mk a b (wt residualSWeights F)) h₀ h₁ |>.trans
    (congrArg (FlagIncrements.mk _ _) hr.symm)

theorem physicalFlag_positive (H : MvPolynomial (Fin 4) K) (F : RegularIndex H) :
    0 < (physicalFlag F.1).r := regularCumulativeFlag_positive H F

theorem pad_shape (f : Flag) (a : Nat) :
    3 ≤ (padFlag f a).r ∧ (padFlag f a).r+2 ≤ (padFlag f a).y ∧
      (padFlag f a).y+a ≤ (padFlag f a).t :=
  ⟨Nat.le_max_left _ _,Nat.le_max_right _ _,Nat.le_max_right _ _⟩

theorem below_pad (f : Flag) (a : Nat) : f.cumulativeLE (padFlag f a) :=
  ⟨Nat.le_max_right _ _,Nat.le_max_left _ _,Nat.le_max_left _ _⟩

theorem physical_support (F : MvPolynomial (Fin 4) K) (g : Flag)
    (hr : 3 ≤ g.r) (hy : g.r+2 ≤ g.y) (ht : g.y ≤ g.t)
    (h : (physicalFlag F).cumulativeLE g) :
    ResidualSupportData (cellSupport g.t g.y g.r) F := by
  obtain ⟨h₁,h₂,h₃⟩ := h
  change wt residualSWeights F ≤ g.r at h₁
  change wt residualYSWeights F ≤ g.y at h₂
  change wt residualTotalWeights F ≤ g.t at h₃
  constructor <;> simp only [cellSupport,RCN198.support,cellS,cellB,cellA] <;> omega

theorem physical_box (F : MvPolynomial (Fin 4) K) (D : Nat) (hD : 0 < D)
    (hcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071) F ≤ D-1)
    (g : Flag) (h : (physicalFlag F).cumulativeLE g) :
    F ∈ globalCoefficientBox K D 131071 g.t g.r := by
  apply (mem_globalCoefficientBox_iff F D 131071 g.t g.r hD).2
  refine ⟨?_,?_,hcontact⟩
  · apply (RCN081.weightedTotalDegree_le_iff seedWeights F g.t).2
    intro d hd
    have hh := (MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans h.2.2
    rw [RCN081.seed_weight]
    rw [RCN081.weight_fin4] at hh
    simp [residualTotalWeights] at hh
    omega
  · have he : slopeWeights = residualSWeights := rfl
    rw [he]
    exact h.1

theorem physical_cut_flag (Q : MvPolynomial (Fin 4) K) (right : Flag) (hshape : right.ordered)
    (h : (physicalFlag Q).cumulativeLE right) :
    PolynomialInFlag (geometryFlag right.increments) (RCN136.surfaceMap (RCN135.polynomialEmbedding K) Q) := by
  let T := RCN136.surfaceMap (RCN135.polynomialEmbedding K) Q
  have hmap := surfaceMap_nested_weights_le (RCN135.polynomialEmbedding K) Q
  obtain ⟨h₁,h₂,h₃⟩ := h
  have hsmall := polynomialIn_surfaceCumulativeFlag T
  obtain ⟨hr,hy,ht⟩ := surfaceCumulativeFlag_cumulative T
  have h₁' := hr.trans_le (hmap.1.trans h₁)
  have h₂' := hy.trans_le (hmap.2.1.trans h₂)
  have h₃' := ht.trans_le (hmap.2.2.trans h₃)
  obtain ⟨hor₁,hor₂⟩ := hshape
  intro d hd
  obtain ⟨hd₁,hd₂,hd₃⟩ := hsmall d hd
  change d 1 ≤ right.r ∧ d 0+d 1 ≤ right.y-right.r+right.r ∧
    d 0+d 1+d 2 ≤ right.t-right.y+(right.y-right.r)+right.r
  exact ⟨by omega,by omega,by omega⟩

theorem pair_gate_mixed (g f : Flag) (hshape : f.ordered) (h : pairGate g f = true) :
    (geometryFlag f.increments).yz + (geometryFlag f.increments).all = f.y ∧
    ((geometryFlag f.increments).yz + (geometryFlag f.increments).all)*g.r +
      g.y*(geometryFlag f.increments).all < 2130706433 := by
  have hg := (of_decide_eq_true h).2.2
  have e : (geometryFlag f.increments).yz + (geometryFlag f.increments).all = f.y :=
    Nat.sub_add_cancel hshape.1
  rw [e]
  refine ⟨rfl,?_⟩
  change f.y*g.r + g.y*f.r < prime
  rwa [Nat.mul_comm f.y g.r, Nat.add_comm]

structure TerminalSeedData (nodes : Finset I) (x u₀ u₁ : I → K)
    (selected : K → Polynomial K) (seeds : Finset K) : Prop where
  injective : Set.InjOn x nodes
  nodes_card : nodes.card = 262144
  selected_degree : ∀ gamma ∈ seeds, (selected gamma).natDegree ≤ 131071
  agreement : ∀ gamma ∈ seeds, 180960 ≤
    (nodes.filter (fun i => (selected gamma).eval (x i) = u₀ i+gamma*u₁ i)).card
  noPencil : NoLargeSelectedPencil selected seeds 131071 81184

theorem TerminalSeedData.subset {nodes : Finset I} {x u₀ u₁ : I → K}
    {selected : K → Polynomial K} {seeds sub : Finset K}
    (h : TerminalSeedData nodes x u₀ u₁ selected seeds) (hs : sub ⊆ seeds) :
    TerminalSeedData nodes x u₀ u₁ selected sub :=
  ⟨h.injective,h.nodes_card,fun g hg => h.selected_degree g (hs hg),
    fun g hg => h.agreement g (hs hg), noLargeSelectedPencil_mono selected seeds sub 131071 81184 hs h.noPencil⟩

theorem short_regular_payment [CharP K 2130706433]
    (H : MvPolynomial (Fin 4) K) (F : RegularIndex H) (D : Nat)
    (hD : 131072 ≤ D) (hDchar : D < 2130706433)
    (hcontact : MvPolynomial.weightedTotalDegree (contactWeights 131071) F.1 ≤ D-1)
    (f : Flag) (h1 : 1 ≤ f.r) (hf : f.ordered)
    (hR : f.r ≤ 20) (hY : f.y ≤ 84) (hT : f.t ≤ 3873)
    (hFf : (physicalFlag F.1).cumulativeLE f)
    (nodes : Finset I) (x u₀ u₁ : I → K) (selected : K → Polynomial K) (seeds : Finset K)
    (data : TerminalSeedData nodes x u₀ u₁ selected seeds) :
    let rate := shortRates f
    rate.denominator * (regularSeeds H selected seeds F).card ≤
      dot (physicalFlag F.1).increments rate.numerator := by
  let g := padFlag f
  let Γ := regularSeeds H selected seeds F
  have hfg : (physicalFlag F.1).cumulativeLE g :=
    ⟨hFf.1.trans (below_pad f 0).1,hFf.2.1.trans (below_pad f 0).2.1,hFf.2.2.trans (below_pad f 0).2.2⟩
  obtain ⟨hr,hy,ht⟩ := pad_shape f 0
  have ht' : g.y ≤ g.t := by simpa only [Nat.add_zero] using ht
  obtain ⟨hirr,_,hpos⟩ := positiveRFactors_spec H F.1 F.2
  have hΓ := data.subset (regularSeeds_subset H selected seeds F)
  have hsol (z : K) (hz : z ∈ Γ) : RegularSolution F.1 (selected z) z := (Finset.mem_filter.mp hz).2
  have hstage := (short_rates_raw f h1 hf.1 hf.2 hR hY hT).1
  have hbound := regular_raw_bound D g.t g.y g.r hD hDchar hstage hr hy ht' F.1 hirr hpos
    (physical_box F.1 D (by omega) hcontact g hfg) (physical_support F.1 g hr hy ht' hfg)
    selected Γ nodes x u₀ u₁ hΓ.injective hΓ.nodes_card hΓ.selected_degree hΓ.agreement
    (fun z hz => (hsol z hz).1) (fun z hz => (hsol z hz).2) hΓ.noPencil
  dsimp only
  rw [physicalFlag_increments]
  exact short_factor_payment f h1 hf.1 hf.2 hR hY hT (originalCumulativeFlag F.1) Γ.card hbound

end
end ProximityPrize.SubmissionLower.Koala6844Terminal
