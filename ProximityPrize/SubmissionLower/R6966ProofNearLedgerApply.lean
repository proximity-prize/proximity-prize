import ProximityPrize.SubmissionLower.R6966ProofNearLedgerBudget
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowCatalogue

set_option Elab.async false

-- merged module R6966ProofNearLedgerQuote
section Merged_R6966ProofNearLedgerQuote

namespace Research6966.NearLedger

open HelperWindowCertificate (Witness)
open HelperWindowIntervals (box)
open HelperWindowNative (orient)

inductive Method where
  | degree | native | axis | surface | affine | single | fixed | large
  deriving DecidableEq, Repr

structure Pick where
  index : Fin 39
  narrow : Fin 2

def Pick.bank (p : Pick) : Witness := HelperWindowCatalogue.ordinary p.index

theorem Pick.verified (p : Pick) : HelperWindowCertificate.Verified p.bank :=
  HelperWindowCatalogue.ordinary_verified p.index

def binAt (i j : Fin 23) (z : Fin 2) : Fin 23 := if z=0 then i else j

def Pick.Valid (p : Pick) (a : ℕ) (i j : Fin 23) : Prop :=
  p.bank.degree=a ∧ p.bank.lower≤
    (if p.bank.rect then levels (binAt i j p.narrow) else max (levels i) (levels j))

instance (p : Pick) (a : ℕ) (i j : Fin 23) : Decidable (p.Valid a i j) := by
  unfold Pick.Valid
  infer_instance

def Pick.seedBudget (p : Pick) (z : Fin 2) : ℕ :=
  if p.bank.rect then orient p.narrow (box HelperWindowCertificate.seedCap p.bank.v) z else p.bank.v

structure Quote where
  method : Method
  degreePick : Option Pick
  axis0Pick : Option Pick
  axis1Pick : Option Pick

def Quote.axisPick (q : Quote) (z : Fin 2) : Option Pick := if z=0 then q.axis0Pick else q.axis1Pick

def Quote.degreeCap (q : Quote) (b : Band) (a : ℕ) : ℕ :=
  match q.degreePick with
  | none => b.high
  | some p => min b.high ((p.bank.B+(a-1)*p.bank.J)/(p.bank.reserve+1))

def Quote.axisCap (q : Quote) (i j : Fin 23) (z : Fin 2) : ℕ :=
  match q.axisPick z, upper (binAt i j z) with
  | some p, some u => min massCap ((p.seedBudget z+p.bank.J*u)/(p.bank.reserve+1))
  | _, _ => massCap

def inCap (i : Fin 23) : ℕ := (upper i).getD 0

def side (h : ℕ) : ℕ := (nodes-agreement)*h+(agreement-wordDegree)

def yHeight (a : ℕ) : ℕ := (2*wordDegree-1)*(a-1)+1

def seedHeight (a u : ℕ) : ℕ := max 1 ((if a=1 then wordDegree else 2*wordDegree-1)*u)

def singular (a : ℕ) (i j : Fin 23) : ℕ := (2*a-1)*(inCap i+prime*inCap j)

def Quote.wordPrice (q : Quote) (b : Band) (a : ℕ) (i j : Fin 23) : ℕ :=
  let d := agreement-wordDegree
  let numerator := nodes-wordDegree
  let y := yHeight a
  let x0 := seedHeight a (inCap i)
  let x1 := seedHeight a (inCap j)
  let fee := singular a i j
  match q.method with
  | .surface =>
    fee+2*(q.degreeCap b a*side x0*side x1+
      q.axisCap i j 0*side y*side x1+q.axisCap i j 1*side y*side x0)/d^2
  | .affine => fee+6*x0*x1*numerator^3/d^3
  | .single => fee+2*y*max x0 x1*numerator^2/d^2
  | .fixed => y*numerator/d+1
  | _ => 0

def Quote.axisPrice (q : Quote) (b : Band) (a : ℕ) (i j : Fin 23) : ℕ :=
  let g := q.degreeCap b a
  rate g*q.axisCap i j 0+(density g-credit)*q.axisCap i j 1

def repairFits (a : ℕ) (i j : Fin 23) : Prop :=
  i.val<22 ∧ j.val<22 ∧ (2*a-1)*inCap i<prime

instance (a : ℕ) (i j : Fin 23) : Decidable (repairFits a i j) := by
  unfold repairFits
  infer_instance

def allowedPick (o : Option Pick) (a : ℕ) (i j : Fin 23) : Prop :=
  o.elim True (fun p=>p.Valid a i j)

instance (o : Option Pick) (a : ℕ) (i j : Fin 23) : Decidable (allowedPick o a i j) := by
  cases o with
  | none => exact inferInstanceAs (Decidable True)
  | some p => exact inferInstanceAs (Decidable (p.Valid a i j))

def Quote.Paid (q : Quote) (b : Band) (a : ℕ) (i j : Fin 23) : Prop :=
  let g := q.degreeCap b a
  let off := b.off a
  let additive := b.additive
  let word := q.wordPrice b a i j
  match q.method with
  | .degree => g+off<b.low
  | .native => max g off<48 ∧ nativeCap (max g off)+additive≤core
  | .axis => g<48 ∧ density off≤credit ∧ q.axisPrice b a i j+additive≤free
  | .surface => repairFits a i j ∧ density off≤credit ∧ word+additive≤free
  | .affine => a=1 ∧ repairFits a i j ∧ density off≤credit ∧ word+additive≤free
  | .single => repairFits a i j ∧ min (inCap i) (inCap j)=0 ∧ 0<max (inCap i) (inCap j) ∧
      density off≤credit ∧ word+additive≤free
  | .fixed => upper i=some 0 ∧ upper j=some 0 ∧ density off≤credit ∧ word+additive≤free
  | .large => b.low=19 ∧ a=5 ∧ 1024≤levels j

instance (q : Quote) (b : Band) (a : ℕ) (i j : Fin 23) : Decidable (q.Paid b a i j) := by
  unfold Quote.Paid
  dsimp only
  split <;> infer_instance

def Quote.Valid (q : Quote) (b : Band) (a : ℕ) (i j : Fin 23) : Prop :=
  allowedPick q.degreePick a i j ∧ allowedPick q.axis0Pick a i j ∧
    allowedPick q.axis1Pick a i j ∧ q.Paid b a i j

instance (q : Quote) (b : Band) (a : ℕ) (i j : Fin 23) : Decidable (q.Valid b a i j) := by
  unfold Quote.Valid
  infer_instance

/-- The actual retained polynomial, its on/off graph split, and the
quotient estimates supplied by any admissible verified catalogue bank. -/
structure GraphEvidence (b : Band) (a : ℕ) (i j : Fin 23) where
  onDegree : ℕ
  offDegree : ℕ
  axes : Fin 2→ℕ
  onMass : ℕ
  offMass : ℕ
  degree_enough : b.low≤onDegree+offDegree
  on_high : onDegree≤b.high
  off_high : offDegree≤b.off a
  axes_mass : ∀ z, axes z≤onMass
  projected : ∀ w : Pick, w.Valid a i j →
    (w.bank.reserve+1)*onDegree≤w.bank.B+(a-1)*w.bank.J ∧
    ∀ z u, upper (binAt i j z)=some u →
      (w.bank.reserve+1)*axes z≤w.seedBudget z+w.bank.J*u

theorem Quote.bounds {b : Band} {a : ℕ} {i j : Fin 23} {q : Quote}
    (ok : q.Valid b a i j) (G : GraphEvidence b a i j) (small : G.onMass≤massCap) :
    G.onDegree≤q.degreeCap b a ∧ ∀ z, G.axes z≤q.axisCap i j z := by
  constructor
  · cases found : q.degreePick with
    | none => simpa only [Quote.degreeCap,found] using G.on_high
    | some p =>
      have good : p.Valid a i j := by
        have v := ok.1
        simpa only [allowedPick,found,Option.elim_some] using v
      simp only [Quote.degreeCap,found,le_min_iff]
      exact ⟨G.on_high,(Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (by
        rw [Nat.mul_comm]
        exact (G.projected p good).1)⟩
  · intro z
    have base := (G.axes_mass z).trans small
    cases found : q.axisPick z with
    | none => simpa only [Quote.axisCap,found] using base
    | some p =>
      cases width : upper (binAt i j z) with
      | none => simpa only [Quote.axisCap,found,width] using base
      | some u =>
        have avail : allowedPick (q.axisPick z) a i j := by
          by_cases zero : z=0
          · simpa only [Quote.axisPick,ite_eq_left zero] using ok.2.1
          · simpa only [Quote.axisPick,ite_eq_right zero] using ok.2.2.1
        have good : p.Valid a i j := by simpa only [found,allowedPick,Option.elim_some] using avail
        simp only [Quote.axisCap,found,width,le_min_iff]
        exact ⟨base,(Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr (by
          rw [Nat.mul_comm]
          exact (G.projected p good).2 z u width)⟩

end Research6966.NearLedger

end Merged_R6966ProofNearLedgerQuote

-- merged module R6966ProofNearLedgerApply
section Merged_R6966ProofNearLedgerApply

namespace Research6966.NearLedger
set_option maxHeartbeats 600000

theorem Invoice.mass_le {r : Fin 58} (I : Invoice (branch r)) : I.mass≤massCap :=
  (Nat.add_le_add I.primary_cap I.rescue_cap).trans (branch_base r).2.2.2.1

theorem Invoice.paid_credit {r : Fin 58} (I : Invoice (branch r)) :
    I.paid+credit*I.mass≤(branch r).base :=
  I.credit_le (branch_base r).2.1 (branch_base r).2.2.1

theorem small (r : Fin 58) (I : Invoice (branch r)) (e tail : ℕ) (he : e≤18)
    (count : tail≤density e*I.mass+(max 3 e-1)*e) : I.paid+tail≤core := by
  have d := Nat.mul_le_mul_right prime (rate_mono he)
  have deb := I.debit_le (density 18)
  have cap := branch_native r (show 18<48 by decide)
  have fixed : (max 3 e-1)*e≤17*18 :=
    Nat.mul_le_mul (Nat.sub_le_sub_right (max_le (by decide) he) 1) he
  have price := Nat.mul_le_mul_right I.mass d
  change density e*I.mass≤density 18*I.mass at price
  have final := small_cap
  omega

/-- Only the inequality corresponding to the selected pricing method is
required. Degree exclusion follows from the quotient bounds. The physical
large-seed exclusion must be supplied by the graph argument. -/
def Quote.Demand {r : Fin 58} (q : Quote) (b : Band) (a : ℕ) (i j : Fin 23)
    (I : Invoice (branch r)) (G : GraphEvidence b a i j) (tail : ℕ) : Prop :=
  let g := q.degreeCap b a
  let off := b.off a
  match q.method with
  | .degree => True
  | .large => False
  | .native => tail≤density (max g off)*I.mass+b.additive
  | .axis => tail≤rate g*(G.axes 0+prime*G.axes 1)+density off*G.offMass+b.additive
  | .surface | .affine | .single | .fixed =>
    tail≤q.wordPrice b a i j+density off*G.offMass+b.additive

private theorem credit_word {r : Fin 58} (I : Invoice (branch r)) {tail fee offMass additive off : ℕ}
    (fits : offMass≤I.mass) (offPrice : off≤credit) (budget : fee+additive≤free)
    (count : tail≤fee+off*offMass+additive) : I.paid+tail≤core := by
  have pay := I.paid_credit
  have price := Nat.mul_le_mul offPrice fits
  have left := (branch_base r).1
  omega

private theorem split_credit (d m : ℕ) : d*m≤credit*m+(d-credit)*m := by
  by_cases low : d≤credit
  · exact (Nat.mul_le_mul_right m low).trans (Nat.le_add_right _ _)
  · rw [← Nat.add_mul, Nat.add_sub_of_le (show credit≤d by omega)]

theorem Quote.finish {r : Fin 58} (I : Invoice (branch r)) {b : Band} {a : ℕ} {i j : Fin 23} {q : Quote}
    (ok : q.Valid b a i j) (G : GraphEvidence b a i j)
    (mass : G.onMass+G.offMass≤I.mass) (tail : ℕ) (count : q.Demand b a i j I G tail) :
    I.paid+tail≤core := by
  have budget := ok.2.2.2
  have on : G.onMass≤I.mass := (Nat.le_add_right _ _).trans mass
  have off : G.offMass≤I.mass := (Nat.le_add_left _ _).trans mass
  obtain ⟨grade,axes⟩ := q.bounds ok G (on.trans I.mass_le)
  cases kind : q.method
  · simp only [Quote.Paid,kind] at budget
    have need := G.degree_enough
    have split := G.off_high
    omega
  · simp only [Quote.Paid,Quote.Demand,kind] at budget count
    have debit := I.debit_le (density (max (q.degreeCap b a) (b.off a)))
    have limit := branch_native r budget.1
    have room := budget.2
    omega
  · simp only [Quote.Paid,Quote.Demand,kind] at budget count
    let g := q.degreeCap b a
    let y := G.axes 1
    have fit : y+G.offMass≤I.mass := (Nat.add_le_add_right (G.axes_mass 1) _).trans mass
    have collected : credit*y+density (b.off a)*G.offMass≤credit*I.mass := by
      calc
        _ ≤ credit*y+credit*G.offMass :=
          Nat.add_le_add_left (Nat.mul_le_mul_right G.offMass budget.2.1) _
        _ = credit*(y+G.offMass) := by rw [Nat.mul_add]
        _ ≤ _ := Nat.mul_le_mul_left credit fit
    have onFee := split_credit (density g) y
    have rest : rate g*G.axes 0+(density g-credit)*y≤q.axisPrice b a i j :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (axes 0)) (Nat.mul_le_mul_left _ (axes 1))
    have exact_count :
        tail≤rate g*G.axes 0+density g*y+density (b.off a)*G.offMass+b.additive := by
      dsimp only [g,y,density]
      rw [Nat.mul_add, ← Nat.mul_assoc] at count
      exact count
    have pay := I.paid_credit
    have left := (branch_base r).1
    have floor := budget.2.2
    omega
  · simp only [Quote.Paid,Quote.Demand,kind] at budget count
    exact credit_word I off budget.2.1 budget.2.2 count
  · simp only [Quote.Paid,Quote.Demand,kind] at budget count
    exact credit_word I off budget.2.2.1 budget.2.2.2 count
  · simp only [Quote.Paid,Quote.Demand,kind] at budget count
    exact credit_word I off budget.2.2.2.1 budget.2.2.2.2 count
  · simp only [Quote.Paid,Quote.Demand,kind] at budget count
    exact credit_word I off budget.2.2.1 budget.2.2.2 count
  · simp only [Quote.Demand,kind] at count

end Research6966.NearLedger

end Merged_R6966ProofNearLedgerApply
