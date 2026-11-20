import ProximityPrize.SubmissionLower.Low27Common
import ProximityPrize.SubmissionLower.Fast075
import ProximityPrize.SubmissionLower.Hi6921Fast023
import ProximityPrize.SubmissionLower.HighPrice6921Core
import ProximityPrize.SubmissionLower.Bridge6925Price
set_option Elab.async false
section PackSource_P0_10Defs
set_option autoImplicit true
namespace P0_10

noncomputable section

open Polynomial
open P0 (AnchorModel AnchoredFamily K k p node twist agreement t heightCap highPrefix)
open K1_14 (L FX Seeds Equation Jet Shape Band Banks liftPoly graphEval atX
  triangle slots shapeSum sourceDebit seedHasse SeedBound)
open K1_14_3 (Surface Parent NoMovingCommon Compatible RowCaps ProjectedProduct)
open scoped BigOperators

abbrev band := H21.band
abbrev terminalShape := H21.terminalShape
def freeShape (w : ℤ) (i : Fin 3) : Shape :=
  if w ≤ 3554 then ![⟨55, 76, 16, 1360⟩, ⟨91, 126, 27, 2072⟩, ⟨230,319,66,4045⟩] i
  else ![⟨34, 47, 10, 515⟩, ⟨77, 80, 16, 940⟩, ⟨230,319,66,4045⟩] i

def movingShape (w : ℤ) (i : Fin 3) : Shape :=
  if w ≤ 3554 then ![⟨160, 222, 46, 6927⟩, ⟨266, 369, 77, 10980⟩, ⟨600,837,168,25162⟩] i
  else ![⟨67, 93, 18, 1857⟩, ⟨124, 172, 35, 3138⟩, ⟨600,837,168,25162⟩] i

def reserve (i : Fin 3) : ℕ := ![0, 6, 25] i

def fullShape (w : ℤ) : Shape :=
  { terminalShape w with U := if w ≤ 3554 then 75000 else 59515 }

def scheduled (w : ℤ) : List Shape :=
  [freeShape w 0, movingShape w 0, freeShape w 1, movingShape w 1,
    freeShape w 2, movingShape w 2, fullShape w, terminalShape w]

def fullCutoff (s : Shape) : ℕ := s.m * agreement - 1

def reserveCutoff (w : ℤ) (s : Shape) (i : Fin 3) : ℕ :=
  fullCutoff s - 2 * w.toNat * reserve i

/-- Evaluated true-row spaces over the generic abscissa. The seed shifts
ignore nonzero abscissa factors because these are scalar units in FX. -/
structure JetSource {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (rows : Banks) : Prop where
  nested : ∀ s ∈ scheduled M.overhead, ∀ s' ∈ scheduled M.overhead,
    s.m = s'.m → s.B = s'.B → s.J = s'.J → s.U ≤ s'.U →
    ∀ W W', W ≤ W' → rows s W ≤ rows s' W'
  necessary : ∀ s ∈ scheduled M.overhead, ∀ W, W < s.m * agreement → ∀ P ∈ rows s W,
    ∀ γ ∈ Γ, K1_14.jetAt P (M.label γ) (F.scalar γ) = 0
  shape : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, RowCaps P s
  leading : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, P ≠ 0 →
    (P.leadingCoeff.natDegree + P.natDegree) * (131071 - M.overhead.toNat) ≤ W + P.natDegree
  shift : ∀ s ∈ scheduled M.overhead, ∀ W, ∀ P ∈ rows s W, ∀ i r,
    seedHasse i r P ∈ rows s (W + 2 * M.overhead.toNat * r)
  floor_bound : ∀ s ∈ scheduled M.overhead, ∀ W, W < s.m * agreement →
    (∀ q ≤ s.B, ∀ j ≤ min q s.J, q * (131071 - M.overhead.toNat) ≤ W + 1 + j) →
    triangle s.U * shapeSum s (fun q j => W + 1 + j - q * (131071 - M.overhead.toNat)) ≤
      sourceDebit M.overhead.toNat s + ∑ t ∈ Finset.range (W + 1), Module.finrank FX (rows s t)

/-- Both rows are selected at the stage's buffered cutoff. -/
structure BufferedPair (w : ℤ) (rows : Banks) (i : Fin 3) where
  free : Jet
  moving : Jet
  free_ne : free ≠ 0
  moving_ne : moving ≠ 0
  free_mem : free ∈ rows (freeShape w i) (reserveCutoff w (freeShape w i) i)
  moving_mem : moving ∈ rows (movingShape w i) (reserveCutoff w (movingShape w i) i)
  no_moving : NoMovingCommon free moving

def BankVanishes (rows : Banks) (s : Shape) (q : Surface) : Prop :=
  ∀ P ∈ rows s (fullCutoff s), P ∈ q.asIdeal

/-- Retention uses every row of both full spaces and the ordinary
compatibility test. At level five, each full cutoff exceeds its buffered
cutoff by ten times the overhead. -/
def PairPass {w : ℤ} {rows : Banks} {i : Fin 3} (pair : BufferedPair w rows i)
    (q : Surface) : Prop :=
  BankVanishes rows (freeShape w i) q ∧
  BankVanishes rows (movingShape w i) q ∧ Compatible pair.free pair.moving q

def MarkOn {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (q : Surface) (γ : K) : Prop :=
  q.asIdeal ≤ RingHom.ker
    (eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
      (atX (F.scalar γ).derivative))

abbrev forcedPower := H21.forcedPower
abbrev TerminalDivisibility := H21.TerminalDivisibility
export HighPrice6921 (FixedWord section_capacity)
end
end P0_10
end PackSource_P0_10Defs
namespace P0_10
def c2 : Prop :=
  ∀ u del (M : K21.AnchorModel u del) Γ (F : K21.AnchoredFamily M Γ),
    (2472 : ℤ) ≤ M.overhead → M.overhead ≤ 3554 → ∀ rows, JetSource M F rows →
    Nonempty (∀ i : Fin 3, BufferedPair M.overhead rows i)
end P0_10
