import ProximityPrize.SubmissionLower.LocatorProtocol6803

/-!
# Coupled fixed/residual arithmetic target for 68.03

`scripts/check-locator-coupled-residual-6803.py` exhaustively scans every raw
state in the 6803 receipt box.  The residual quotient boxes subtract the raw
flag already retained by the fixed receipt.  Additional factors charged by
the receipt's initial-complement potential can only shrink those quotient
boxes, so ignoring that additional subtraction is conservative.

The old residual `B(m=111,L=12960,s=33)` has nonpositive kernel nullity at
agreement `181363`, so this ledger uses the viable replacement
`B(m=111,L=14261,s=34)`, whose derived middle cap is still `153`.  The wider
slope is reflected both in the receipt complement and in the grouped fixed-gcd
package below.  This module is an arithmetic handoff: the receipt and geometric
modules must still prove that the actual counts are bounded by its components.

The fixed ordinary term uses `initialAWidePotential`, whose coefficients are
valid on the full complementary box; the narrower historical potential is not
a majorant once middle/slope can reach `(153,34)`.
-/

namespace ProximityPrize.SubmissionLower.LocatorCoupledResidualLedger6803

set_option autoImplicit false

def witnessR : ℕ := 17
def witnessV : ℕ := 42
def witnessZ : ℕ := 6523

/-- Four-phase regular receipt plus its initial-factor potential. -/
def fixedOrdinaryAtWitness : ℕ := 274566473159888063

/-- Residual unequal-pair charge after subtracting the retained flag. -/
def residualPairAtWitness : ℕ := 114382255263114

/-- One grouped predecessor incidence for the residual `QB/H` chain. -/
def residualGroupedAtWitness : ℕ := 48644693864444

/-- Uniform proper-escape dot reserved by the grouped residual cardinality
adapter. -/
def residualEscapeCap : ℕ := 429140070

theorem residualEscapeCap_exact : residualEscapeCap = 429140070 := by
  rfl

/-- One aggregate slope-free residual tail. -/
def residualTailAtWitness : ℕ := 1479590622160

def residualAtWitness : ℕ :=
  residualPairAtWitness + residualGroupedAtWitness + residualEscapeCap +
    residualTailAtWitness

theorem residualAtWitness_exact : residualAtWitness = 164506968889788 := by
  norm_num [residualAtWitness, residualPairAtWitness,
    residualGroupedAtWitness, residualEscapeCap, residualTailAtWitness]

/-- The retuned mixed-volume calculation uses raw flags `(6523,119,34)` and
`(14108,119,34)`.  Its executable derivation lives in the companion script. -/
def viableProperExceptionalCap : ℕ := 18437737600

theorem viableProperExceptionalCap_exact :
    viableProperExceptionalCap = 18437737600 := rfl

/-- Exhaustive maximum before the fixed-gcd grouped package.  This already
includes `viableProperExceptionalCap`. -/
def coupledSubtotal : ℕ :=
  fixedOrdinaryAtWitness + residualAtWitness + viableProperExceptionalCap

theorem coupledSubtotal_exact : coupledSubtotal = 274730998566515451 := by
  norm_num [coupledSubtotal, fixedOrdinaryAtWitness, residualAtWitness,
    residualPairAtWitness, residualGroupedAtWitness, residualEscapeCap,
    residualTailAtWitness, viableProperExceptionalCap]

/-- Exact component caps supplied by the grouped-cardinality modules. -/
def mainGroupedRegularCap : ℕ := 105025484947256
def viableComplementGroupedRegularCap : ℕ := 139952655613867
def fixedHEscapeCap : ℕ := 200877080
def fixedAggregateTailCap : ℕ := 2093635209007

/-- Main grouped charge, viable complementary grouped charge, and aggregate
fixed tail.  The middle/total caps are unchanged, so the old tail applies. -/
def viableFixedGroupedCap : ℕ :=
  mainGroupedRegularCap + viableComplementGroupedRegularCap +
    fixedHEscapeCap + fixedAggregateTailCap

theorem viableFixedGroupedCap_exact :
    viableFixedGroupedCap = 247071976647210 := by
  rfl

/-- Full conservative target: fixed ordinary receipt, viable fixed grouped
charges, coupled residual charges, and the exceptional-cut allowance. -/
def fullConservativeTotal : ℕ := coupledSubtotal + viableFixedGroupedCap

theorem fullConservativeTotal_exact :
    fullConservativeTotal = 274978070543162661 := by
  rw [fullConservativeTotal, coupledSubtotal_exact,
    viableFixedGroupedCap_exact]

theorem fullConservativeTotal_lt_protocolBudget :
    fullConservativeTotal < LocatorProtocol6803.mcaBudget := by
  rw [fullConservativeTotal_exact]
  norm_num [LocatorProtocol6803.mcaBudget]

theorem protocolSlack_exact :
    LocatorProtocol6803.mcaBudget - fullConservativeTotal =
      2652343415671 := by
  rw [fullConservativeTotal_exact]
  norm_num [LocatorProtocol6803.mcaBudget]

theorem closes_of_coupled_bound {actual : ℕ}
    (hactual : actual ≤ fullConservativeTotal) :
    actual < LocatorProtocol6803.mcaBudget :=
  hactual.trans_lt fullConservativeTotal_lt_protocolBudget

/-- The all-positive-factor aggregation charges the entire retained factor
once, so the main and complementary fixed grouped charges are not additive.
The final assembly uses the all-H complement charge and aggregate tail. -/
def singleAllHGroupedCap : ℕ :=
  viableComplementGroupedRegularCap + fixedHEscapeCap +
    fixedAggregateTailCap

theorem singleAllHGroupedCap_exact :
    singleAllHGroupedCap = 142046491699954 := by
  rfl

def singleAllHFullTotal : ℕ := coupledSubtotal + singleAllHGroupedCap

theorem singleAllHFullTotal_exact :
    singleAllHFullTotal = 274873045058215405 := by
  rw [singleAllHFullTotal, coupledSubtotal_exact, singleAllHGroupedCap_exact]

theorem singleAllHFullTotal_lt_protocolBudget :
    singleAllHFullTotal < LocatorProtocol6803.mcaBudget := by
  rw [singleAllHFullTotal_exact]
  norm_num [LocatorProtocol6803.mcaBudget]

theorem singleAllHProtocolSlack_exact :
    LocatorProtocol6803.mcaBudget - singleAllHFullTotal =
      107677828362927 := by
  rw [singleAllHFullTotal_exact]
  norm_num [LocatorProtocol6803.mcaBudget]

/-- The empty retained-factor branch, checked separately because the generated
receipt enumerates only positive slope. -/
def zeroFixedComplement : ℕ := 1759867244112852
def zeroResidualPair : ℕ := 515423658925727
def zeroResidualGrouped : ℕ := 298968256359977
def zeroResidualTail : ℕ := 4472540779861

def zeroStateTotal : ℕ :=
  zeroFixedComplement + zeroResidualPair + zeroResidualGrouped +
    residualEscapeCap + zeroResidualTail + singleAllHGroupedCap +
      viableProperExceptionalCap

theorem zeroStateTotal_exact : zeroStateTotal = 2720797058756041 := by
  norm_num [zeroStateTotal, zeroFixedComplement, zeroResidualPair,
    zeroResidualGrouped, zeroResidualTail, singleAllHGroupedCap,
    residualEscapeCap, viableComplementGroupedRegularCap, fixedHEscapeCap,
    fixedAggregateTailCap, viableProperExceptionalCap]

theorem zeroStateTotal_lt_protocolBudget :
    zeroStateTotal < LocatorProtocol6803.mcaBudget := by
  rw [zeroStateTotal_exact]
  norm_num [LocatorProtocol6803.mcaBudget]

end ProximityPrize.SubmissionLower.LocatorCoupledResidualLedger6803
