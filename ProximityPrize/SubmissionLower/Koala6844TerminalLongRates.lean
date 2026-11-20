import ProximityPrize.SubmissionLower.Koala6844TerminalGraphRates
import ProximityPrize.SubmissionLower.Koala6844TerminalPairRates


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open scoped BigOperators
open RCN095
open Koala6844Receipts

set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] graphScale
set_option maxRecDepth 2048
set_option maxHeartbeats 420000

def shapeAt (s : Sources) (j : Fin 3) : SourceShape := ![s.z,s.yz,s.all] j

def graphCore (g : Flag) (sources : Sources) : FlagIncrements :=
  FlagIncrements.map fun i =>
    max ((graphIdentity g).axis i)
      ((graphBasis g).axis i + (graphMove g sources.z 0).axis i +
        (graphMove g sources.yz 1).axis i + (graphMove g sources.all 2).axis i)

def leadRates (g : Flag) (s : SourceShape) : FlagIncrements :=
  graphPairRates s.carrierFlag (graphDirection g)

def helperRates (g : Flag) (s : SourceShape) : FlagIncrements :=
  graphPairRates (helperFlag g s) (graphDirection g)

theorem axis_map (a : Nat → Nat) (j : Fin 3) :
    (FlagIncrements.map a).axis j.val = a j.val := by
  fin_cases j <;> rfl

private theorem dot_le_of_axes (left : FlagIncrements) {a b : FlagIncrements}
    (h : ∀ j : Fin 3, a.axis j.val ≤ b.axis j.val) : dot left a ≤ dot left b := by
  have h0 : a.total ≤ b.total := h 0
  have h1 : a.middle ≤ b.middle := h 1
  have h2 : a.slope ≤ b.slope := h 2
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ h0) (Nat.mul_le_mul_left _ h1))
    (Nat.mul_le_mul_left _ h2)

private theorem axis_add_dot (left a b c d : FlagIncrements) :
    dot left (FlagIncrements.map fun j => a.axis j + b.axis j + c.axis j + d.axis j) =
      dot left a + dot left b + dot left c + dot left d := by
  simp only [FlagIncrements.map,FlagIncrements.axis,dot,Nat.reduceEqDiff,ite_true,ite_false]
  ring

theorem graphCharge_eq {scope g : Flag} {src : SourceShape} {j : Fin 3}
    {c : GraphCharge} (h : graphCharge scope g src j.val = some c) :
    pairGate g src.carrierFlag = true ∧ pairGate g (helperFlag g src) = true ∧
      c = ⟨graphMove g src j,leadRates g src,helperRates g src⟩ := by
  unfold graphCharge at h
  dsimp only at h
  split at h
  · rename_i hg
    obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp hg
    exact ⟨h1,h2,(Option.some.inj h).symm⟩
  · contradiction

structure LongRatesData (scope : Flag) (src : Sources) (rate : Rates) : Prop where
  good : goodGraph (padFlag scope 2) = true
  leadGate : ∀ j : Fin 3, pairGate (padFlag scope 2) (shapeAt src j).carrierFlag = true
  helperGate : ∀ j : Fin 3, pairGate (padFlag scope 2) (helperFlag (padFlag scope 2) (shapeAt src j)) = true
  denom : rate.denominator = graphScale
  numer : ∀ j : Fin 3,
    let g := padFlag scope 2
    let i := j.val
    rate.numerator.axis i = max
      ((leadRates g src.z).axis i + (leadRates g src.yz).axis i +
        (leadRates g src.all).axis i + (graphCore g src).axis i)
      (max ((helperRates g src.z).axis i)
        (max ((helperRates g src.yz).axis i) ((helperRates g src.all).axis i)))

theorem LongRatesData.gates {scope : Flag} {src : Sources} {rate : Rates}
    (h : LongRatesData scope src rate) :
    GraphGates (padFlag scope 2).t (padFlag scope 2).y (padFlag scope 2).r :=
  graphGates_of_goodGraph _ (Nat.le_max_left _ _) (Nat.le_max_right _ _) h.good

private theorem core_axis (g : Flag) (src : Sources) (j : Fin 3) :
    (graphCore g src).axis j.val = max ((graphIdentity g).axis j.val)
      ((graphBasis g).axis j.val + (graphMove g src.z 0).axis j.val +
        (graphMove g src.yz 1).axis j.val + (graphMove g src.all 2).axis j.val) :=
  axis_map _ j

theorem charge_dot_eq (n : FlagIncrements) (f : FlagDegree) :
    charge (fun j => n.axis j.val) f = dot (increments f) n := by
  cases n
  rfl

theorem long_graph_identity_le (g : Flag) (src : Sources) (left : FlagDegree)
    (hr : 3 ≤ g.r) (hy : g.r+2 ≤ g.y) (ht : g.y ≤ g.t) :
    identityCharge graphScale g.t g.y g.r left ≤
      charge (fun j => (graphCore g src).axis j.val) left := by
  have hc (j : Fin 3) : (graphIdentity g).axis j.val ≤ (graphCore g src).axis j.val := by
    calc
      _ ≤ max ((graphIdentity g).axis j.val)
          ((graphBasis g).axis j.val + (graphMove g src.z 0).axis j.val +
            (graphMove g src.yz 1).axis j.val + (graphMove g src.all 2).axis j.val) := le_max_left _ _
      _ = _ := (core_axis g src j).symm
  calc
    _ = dot (increments left) (graphIdentity g) := graph_identity_eq g hr hy ht left
    _ ≤ dot (increments left) (graphCore g src) := dot_le_of_axes (increments left) hc
    _ = _ := (charge_dot_eq (graphCore g src) left).symm

theorem long_graph_numerator_le {K : Type} [Field K] {F : MvPolynomial (Fin 4) K}
    (source : Fin 3 → MovingFiberThreeSources6811.Source F) (src : Sources) (g : Flag)
    (hr : 3 ≤ g.r) (hy : g.r+2 ≤ g.y) (ht : g.y ≤ g.t)
    (hd : ∀ j, (source j).d = (shapeAt src j).k+1)
    (hf : ∀ j, (source j).flag = geometryFlag (shapeAt src j).graphIncrement)
    (hdiv : ∀ j, 3*(shapeAt src j).k+3 ∣ graphScale) (left : FlagDegree) :
    HFreeDir6813.numeratorDir source graphScale g.t g.y g.r left ≤
      charge (fun j => (graphCore g src).axis j.val) left := by
  let f := increments left
  let a := graphBasis g
  let b := graphMove g src.z 0
  let c := graphMove g src.yz 1
  let d := graphMove g src.all 2
  let summed := FlagIncrements.map fun i => a.axis i + b.axis i + c.axis i + d.axis i
  have hs : HFreeDir6813.numeratorDir source graphScale g.t g.y g.r left = dot f summed := by
    calc
      _ = dot f a + ∑ j : Fin 3, dot f (graphMove g (shapeAt src j) j) :=
        graph_numerator_eq source (shapeAt src) g hr hy ht hd hf hdiv left
      _ = dot f a + (dot f b + dot f c + dot f d) := congrArg (dot f a + ·) (Fin.sum_univ_three _)
      _ = dot f a + dot f b + dot f c + dot f d := by ac_rfl
      _ = _ := (axis_add_dot f a b c d).symm
  have haxes (j : Fin 3) : summed.axis j.val ≤ (graphCore g src).axis j.val := by
    calc
      _ = a.axis j.val + b.axis j.val + c.axis j.val + d.axis j.val := axis_map _ j
      _ ≤ max ((graphIdentity g).axis j.val) _ := le_max_right _ _
      _ = _ := (core_axis g src j).symm
  calc
    _ = dot f summed := hs
    _ ≤ dot f (graphCore g src) := dot_le_of_axes f haxes
    _ = _ := (charge_dot_eq (graphCore g src) left).symm

private theorem mixed_monotone (f g : FlagIncrements) :
    mixedRate 0 f g ≤ mixedRate 1 f g ∧ mixedRate 1 f g ≤ mixedRate 2 f g := by
  simp only [mixedRate,Nat.reduceEqDiff,ite_true,ite_false]
  constructor <;> omega

theorem long_graph_cost_mono (g : Flag) (src : Sources) :
    (graphCore g src).total ≤ (graphCore g src).middle ∧
      (graphCore g src).middle ≤ (graphCore g src).slope := by
  have hi : (graphIdentity g).total ≤ (graphIdentity g).middle ∧
      (graphIdentity g).middle ≤ (graphIdentity g).slope := by
    unfold graphIdentity
    constructor <;> apply Nat.mul_le_mul_left <;> omega
  have hb : (graphBasis g).total ≤ (graphBasis g).middle ∧
      (graphBasis g).middle ≤ (graphBasis g).slope := by
    unfold graphBasis
    let f := graphNormal g
    have h0 := mixed_monotone (graphFirstCut g 0) (axisFlag 0)
    have h1 := mixed_monotone (graphFirstCut g 1) (axisFlag 1)
    have h2 := mixed_monotone (graphFirstCut g 2) (axisFlag 2)
    constructor
    · exact Nat.mul_le_mul_right _ (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left f.total h0.1) (Nat.mul_le_mul_left f.middle h1.1))
        (Nat.mul_le_mul_left f.slope h2.1))
    · exact Nat.mul_le_mul_right _ (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left f.total h0.2) (Nat.mul_le_mul_left f.middle h1.2))
        (Nat.mul_le_mul_left f.slope h2.2))
  have hm (s : SourceShape) (j : Fin 3) :
      (graphMove g s j).total ≤ (graphMove g s j).middle ∧
        (graphMove g s j).middle ≤ (graphMove g s j).slope := by
    have h := mixed_monotone (axisFlag j.val) s.graphIncrement
    exact ⟨Nat.mul_le_mul_left _ h.1,Nat.mul_le_mul_left _ h.2⟩
  constructor
  · exact max_le_max hi.1 (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add hb.1 (hm src.z 0).1) (hm src.yz 1).1) (hm src.all 2).1)
  · exact max_le_max hi.2 (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add hb.2 (hm src.z 0).2) (hm src.yz 1).2) (hm src.all 2).2)

theorem LongRatesData.lead_graph_le {scope : Flag} {src : Sources} {rate : Rates}
    (h : LongRatesData scope src rate) (left : FlagIncrements) :
    let g := padFlag scope 2
    dot left (leadRates g src.z) + dot left (leadRates g src.yz) +
      dot left (leadRates g src.all) + dot left (graphCore g src) ≤ dot left rate.numerator := by
  dsimp only
  let g := padFlag scope 2
  let a := leadRates g src.z
  let b := leadRates g src.yz
  let c := leadRates g src.all
  let d := graphCore g src
  let summed := FlagIncrements.map fun j => a.axis j + b.axis j + c.axis j + d.axis j
  have hc (j : Fin 3) : summed.axis j.val ≤ rate.numerator.axis j.val := by
    calc
      _ = a.axis j.val + b.axis j.val + c.axis j.val + d.axis j.val := axis_map _ j
      _ ≤ max _ (max ((helperRates g src.z).axis j.val)
          (max ((helperRates g src.yz).axis j.val) ((helperRates g src.all).axis j.val))) := le_max_left _ _
      _ = _ := (h.numer j).symm
  exact (axis_add_dot left a b c d).symm.le.trans (dot_le_of_axes left hc)

theorem LongRatesData.helper_le {scope : Flag} {src : Sources} {rate : Rates}
    (h : LongRatesData scope src rate) (left : FlagIncrements) (j : Fin 3) :
    dot left (helperRates (padFlag scope 2) (shapeAt src j)) ≤ dot left rate.numerator := by
  apply dot_le_of_axes
  intro i
  let g := padFlag scope 2
  have hh : (helperRates g (shapeAt src j)).axis i.val ≤ max ((helperRates g src.z).axis i.val)
      (max ((helperRates g src.yz).axis i.val) ((helperRates g src.all).axis i.val)) := by
    fin_cases j
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  exact hh.trans ((le_max_right _ _).trans_eq (h.numer i).symm)

end ProximityPrize.SubmissionLower.Koala6844Terminal
