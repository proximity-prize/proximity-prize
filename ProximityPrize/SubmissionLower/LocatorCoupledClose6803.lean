import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptSemantic
import ProximityPrize.SubmissionLower.LocatorCoupledResidualLedger6803

/-!
# Final correlated arithmetic join for 68.03

This module is deliberately independent of the geometric construction.  It
states exactly what that construction must provide at one retained flag and
then closes the protocol budget using the checked receipt.  Keeping this join
small makes the crucial "same state on both sides" condition explicit.
-/

namespace ProximityPrize.SubmissionLower.LocatorCoupledClose6803

open RCN095 LocatorFactorAggregate LocatorPhase6800Oracle
open LocatorPhase6803Composition LocatorPhase6803ReceiptCore
open LocatorPhase6803ReceiptSemantic

set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The phase cap appearing in the semantic checked receipt. -/
def phaseCap (p : FlagDegree) : ℕ :=
  afterPhase4 checkedBaseCap rPrefix cPrefix f500Prefix phase4Prefix p

/-- If the fixed and residual populations are charged at the same retained
flag, their partition is strictly below the 68.03 MCA budget.  The last
premise records the geometric fact that an aggregate flag with zero slope is
the empty aggregate flag. -/
theorem correlated_partition_lt
    (cert : CheckedRows) (p : FlagDegree)
    (hs : p.all ≤ 29) (hy : middle p ≤ 135) (ht : total p ≤ 6676)
    (fixed residual population : ℕ)
    (hpartition : fixed + residual = population)
    (hfixed : fixed ≤
      phaseCap p + LocatorPhase6803ReceiptCore.initialAComplement p +
        LocatorCoupledResidualLedger6803.singleAllHGroupedCap)
    (hresidual : residual ≤ residualCharge p.all p.yz p.zOnly)
    (hzero : p.all = 0 → p = rawFlag 0 0 0) :
    population < LocatorProtocol6803.mcaBudget := by
  rw [← hpartition]
  by_cases hp : 1 ≤ p.all
  · have hreceipt := LocatorPhase6803ReceiptSemantic.coupled_le cert p
      ⟨hp, hs, hy, ht⟩
    have hbound : fixed + residual ≤
        certifiedCoupledMaximum +
          LocatorCoupledResidualLedger6803.singleAllHGroupedCap := by
      simp only [phaseCap] at hfixed
      omega
    exact hbound.trans_lt (by
      norm_num [certifiedCoupledMaximum,
        LocatorCoupledResidualLedger6803.singleAllHGroupedCap,
        LocatorCoupledResidualLedger6803.viableComplementGroupedRegularCap,
        LocatorCoupledResidualLedger6803.fixedHEscapeCap,
        LocatorCoupledResidualLedger6803.fixedAggregateTailCap,
        LocatorProtocol6803.mcaBudget])
  · have hp0 : p.all = 0 := by omega
    have hpflag := hzero hp0
    rw [hpflag] at hfixed hresidual
    change residual ≤ residualCharge 0 0 0 at hresidual
    have hreceipt := zeroCoupled_exact
    have hbound : fixed + residual ≤
        2578750567056087 +
          LocatorCoupledResidualLedger6803.singleAllHGroupedCap := by
      simp only [phaseCap] at hfixed
      omega
    exact hbound.trans_lt (by
      norm_num [LocatorCoupledResidualLedger6803.singleAllHGroupedCap,
        LocatorCoupledResidualLedger6803.viableComplementGroupedRegularCap,
        LocatorCoupledResidualLedger6803.fixedHEscapeCap,
        LocatorCoupledResidualLedger6803.fixedAggregateTailCap,
        LocatorProtocol6803.mcaBudget])

end ProximityPrize.SubmissionLower.LocatorCoupledClose6803
