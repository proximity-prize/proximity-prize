import ProximityPrize.SubmissionLower.Shared50OrderDivision
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalRing.Module
import ProximityPrize.SubmissionLower.Low6966Monotone
import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCycleCaps
import ProximityPrize.SubmissionLower.Low49ActiveLattice
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.Low48BentCycle
import ProximityPrize.SubmissionLower.Low48BentCycleCap
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCyclePrice
import ProximityPrize.SubmissionLower.Low48BentCyclePrice
import Mathlib.Algebra.MvPolynomial.Coeff
import ProximityPrize.SubmissionLower.KoalaRetainedCut
import ProximityPrize.SubmissionLower.R6960Low6960SurfaceLinearFour
import ProximityPrize.SubmissionLower.GoldBranch6N8
import ProximityPrize.SubmissionLower.Final50Price
import ProximityPrize.SubmissionLower.R6960Anchor6966Local
import ProximityPrize.SubmissionLower.Low50Euler2367JetDegree
import ProximityPrize.SubmissionLower.Low6966Order
import ProximityPrize.SubmissionLower.Low6966Retained
import ProximityPrize.SubmissionLower.R6960Low6960SharedTallyNew
import ProximityPrize.SubmissionLower.Fast063
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Localization.Integer
import ProximityPrize.SubmissionLower.Shared50ShapeRankBase
import ProximityPrize.SubmissionLower.Wide50EulerPrimaryFamily
import ProximityPrize.SubmissionLower.Final50SurfaceLinearFive
import ProximityPrize.SubmissionLower.R6966ProofLowTierWeight
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option Elab.async false

-- merged module Gate6966Order
section Merged_Gate6966Order

set_option autoImplicit false

namespace Gate6966Order

open K1_13_6_1_2 (VanishesTo)













































































































end Gate6966Order

end Merged_Gate6966Order

-- merged module Gate6966Count
section Merged_Gate6966Count

set_option autoImplicit false
set_option Elab.async false

namespace Gate6966Count

open P3 (K)
open K1_13 (Row Shape shape InBox chart mixed32)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_1_2 (VanishesTo pair_height)




open scoped Polynomial BigOperators


variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ} {S : Set (Ideal GeoJets)}

























































































































end Gate6966Count

end Merged_Gate6966Count

-- merged module Gate6966TwoCut
section Merged_Gate6966TwoCut

set_option autoImplicit false
set_option Elab.async false

namespace Gate6966TwoCut

open P3 (K)
open K1_13 (Row Shape shape InBox mixed32)
open K1_13_6 (GeoJets toGeneric)
open K1_13_6_1_2 (VanishesTo)



open scoped Polynomial BigOperators















variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ} {S : Set (Ideal GeoJets)}













































































































































































end Gate6966TwoCut

end Merged_Gate6966TwoCut

-- merged module Gate6966Class
section Merged_Gate6966Class

set_option autoImplicit false

namespace Gate6966Class

open Gate6966TwoCut
























































































end Gate6966Class

end Merged_Gate6966Class

-- merged module Gate6966ClassTable
section Merged_Gate6966ClassTable

set_option autoImplicit false

namespace Gate6966ClassTable

open Gate6966TwoCut Gate6966Class

def okE (ρ a cn vn e : ℤ) : Bool :=
  let R := ρ - (e - 1) * a
  decide (0 ≤ 10000000 * (2 * ρ - cn) * R ^ 2 + 10000000 * cn * ρ * e * R + 2 * ρ * (vn * ρ ^ 2 * (e * (e - 1)) - 10000000 * ρ ^ 2)) &&
  decide (0 ≤ 10000000 * ρ * e * R + vn * ρ ^ 2 * (e * (e - 1)) - 10000000 * ρ ^ 2)

def pairOK (r a k vn : ℕ) : Bool :=
  decide (1 ≤ a ∧ a < r) &&
    (let ρ : ℕ := r - a
     let cn : ℤ := min (2 * (ρ : ℤ)) ((k : ℤ) * a)
     let e0 : ℕ := (ρ + a - 1) / a + 1
     ((List.range (e0 - 1)).all fun i => okE ρ a cn vn ((i : ℤ) + 1)) &&
       decide (10000000 * (ρ : ℤ) ^ 2 ≤ (vn : ℤ) * (ρ : ℤ) ^ 2 * ((e0 : ℤ) * ((e0 : ℤ) - 1))))





































































































def decode (w a : ℕ) : ℕ × ℕ :=
  let s := (w / 256 / 2 ^ (28 * (a - 1))) % 2 ^ 28
  (s % 16, s / 16)

def levelOK (r w : ℕ) : Bool :=
  (List.range (w % 256)).all fun i => pairOK r (i + 1) (decode w (i + 1)).1 (decode w (i + 1)).2

def tableOK : ℕ → List ℕ → Bool
  | _, [] => true
  | r, w :: ws => levelOK r w && tableOK (r + 1) ws

theorem tableOK_cons {r w : ℕ} {ws : List ℕ} (h1 : levelOK r w = true) (h2 : tableOK (r + 1) ws = true) :
    tableOK r (w :: ws) = true := by
  simp [tableOK, h1, h2]

















def lookup (r0 : ℕ) (ws : List ℕ) (r a : ℕ) : Option (ℕ × ℕ) :=
  if r0 ≤ r ∧ r - r0 < ws.length ∧ 1 ≤ a ∧ a ≤ ws.getD (r - r0) 0 % 256 then
    some (decode (ws.getD (r - r0) 0) a)
  else none



















end Gate6966ClassTable

end Merged_Gate6966ClassTable

-- merged module Gate6966CertCF
section Merged_Gate6966CertCF

set_option autoImplicit false

namespace Gate6966CertCF
open Gate6966TwoCut Gate6966Class






















































def cvOf (r0 : ℕ) (ws : List ℕ) (r a : ℕ) : ℕ × ℕ :=
  bif Nat.beq a 0 then (0, 0)
  else match Gate6966ClassTable.lookup r0 ws r a with
    | some (k, vn) => (min (2 * (r - a)) (k * a), vn)
    | none => (2 * (r - a), (10000000 * a * a + (r - a) * (r - a) - 1) / ((r - a) * (r - a)))


































































end Gate6966CertCF

end Merged_Gate6966CertCF
