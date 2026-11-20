import ProximityPrize.SubmissionLower.Koala6844TerminalLongRates


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open Koala6844Receipts

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 420000
attribute [local irreducible] graphScale

private theorem choose_graph_charges (good : Bool) (a b c : Option GraphCharge)
    (finish : GraphCharge → GraphCharge → GraphCharge → Option Rates) (rate : Rates)
    (h : (if !good then none else do finish (← a) (← b) (← c)) = some rate) :
    good = true ∧ ∃ x y z, a = some x ∧ b = some y ∧ c = some z ∧ finish x y z = some rate := by
  cases good <;> cases a <;> cases b <;> cases c <;> simp_all

theorem longRates_data {scope : Flag} {src : Sources} {rate : Rates}
    (h : longRates scope src = some rate) : LongRatesData scope src rate := by
  let g := padFlag scope 2
  let numer (a b c : GraphCharge) := FlagIncrements.map fun i =>
    max (a.lead.axis i + b.lead.axis i + c.lead.axis i +
      max ((graphIdentity g).axis i) ((graphBasis g).axis i + a.move.axis i + b.move.axis i + c.move.axis i))
      (max (a.helper.axis i) (max (b.helper.axis i) (c.helper.axis i)))
  let finish (a b c : GraphCharge) : Option Rates :=
    let n := numer a b c
    if n.total ≤ n.middle ∧ n.middle ≤ n.slope then some ⟨n,graphScale⟩ else none
  obtain ⟨hg,a,b,c,ha,hb,hc,hfin⟩ := choose_graph_charges (goodGraph g)
    (graphCharge scope g src.z 0) (graphCharge scope g src.yz 1) (graphCharge scope g src.all 2)
    finish rate h
  obtain ⟨h0L,h0H,ha'⟩ := graphCharge_eq (j := 0) ha
  obtain ⟨h1L,h1H,hb'⟩ := graphCharge_eq (j := 1) hb
  obtain ⟨h2L,h2H,hc'⟩ := graphCharge_eq (j := 2) (by exact hc)
  have he : (Rates.mk (numer a b c) graphScale) = rate := by
    unfold finish at hfin
    dsimp only at hfin
    split at hfin
    · exact Option.some.inj hfin
    · contradiction
  refine ⟨hg,?_,?_,(congrArg Rates.denominator he).symm,?_⟩
  · intro j
    fin_cases j <;> assumption
  · intro j
    fin_cases j <;> assumption
  · intro j
    have hnum : rate.numerator = numer a b c := (congrArg Rates.numerator he).symm
    dsimp only
    rw [hnum,ha',hb',hc']
    unfold numer graphCore
    rw [axis_map,axis_map]

end ProximityPrize.SubmissionLower.Koala6844Terminal
