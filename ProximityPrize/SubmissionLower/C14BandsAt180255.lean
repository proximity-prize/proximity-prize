import ProximityPrize.SubmissionLower.Fast023
set_option Elab.async false

/-! New K1_14 band schedule for the 6916 radius (A = 180255, e = 81889). UNBUILT.

Only the seed degrees change (bands 1-3: 144→150, 98→100, 47→48) and the last band ends at
32700 (assumed new `AnchorModel.height_bound`). With the official seeds the dimension test
`subbankDebit w < seedGain w` is false at A = 180255 (w = 2601, 3555, 8250).
Exact margins (research/proximity-6916/c14_newbands.json, convex-in-w minimum):
band 1: 66036102716306196 at w = 2601; band 2: 14640149547992 at w = 3555;
band 3: 4589311425319900 at w = 8250; band 4: 1111114339368030 at w = 24000.
The universal test over each band is stated as `c5At` below and is NOT proved here. -/

section PackSource_K1_14_At180255
set_option autoImplicit true
namespace K1_14_At

open K1 K1_14 Polynomial
open scoped BigOperators

/-- Agreement-parametrised copy of `band` with the new seed degrees. -/
def bandNew (w : ℤ) : Band :=
  if w ≤ 3554 then ⟨3554, 5, 150, 836, 1164, 247, 19371⟩
  else if w ≤ 8249 then ⟨8249, 4, 100, 358, 500, 105, 6798⟩
  else if w ≤ 23999 then ⟨23999, 4, 48, 358, 500, 105, 4860⟩
  else ⟨32700, 4, 36, 358, 500, 105, 3913⟩

def simplePriceAt (A : ℕ) (bd : ℤ → Band) (w : ℤ) : ℕ :=
  let b := bd w
  let d := 131071 + b.endpoint
  let gap := A - d
  let T := 2*d-1
  let a := 1+T*(b.yBound-1)
  let B := T*b.seedBound
  let D := b.yBound*B^2 + 2*b.seedBound*a*B
  ((262144 - A)*((262144 - A)/gap+1)*D + (gap-1)) / gap + b.yBound

def singularDegreeAt (bd : ℤ → Band) (w : ℤ) : ℕ :=
  (2*(bd w).yBound-1)*(bd w).seedBound

theorem simplePriceAt_official (w : ℤ) : simplePriceAt 180265 band w = simplePrice w := rfl
theorem singularDegreeAt_official (w : ℤ) : singularDegreeAt band w = singularDegree w := rfl

def highRetainedNew (w : ℤ) : ℕ :=
  if w ≤ 3554 then 76112471485732532
  else if w ≤ 8249 then 46596151281738566
  else if w ≤ 23999 then 28823712025972031
  else 34536341193275597

theorem retained_price_new (w : ℤ) :
    (p+1)*singularDegreeAt bandNew w + simplePriceAt 180255 bandNew w = highRetainedNew w := by
  unfold singularDegreeAt simplePriceAt bandNew highRetainedNew
  split_ifs <;> decide

def rawWidthAt (A : ℕ) (w : ℤ) (q j : ℕ) : ℕ :=
  (bandNew w).multiplicity * A + j - q * (131071 - w.toNat)

def terminalShapeNew (w : ℤ) : Shape :=
  let b := bandNew w
  ⟨b.multiplicity, b.jetBound, b.vBound, b.subbankSeeds⟩

def seedGainAt (A : ℕ) (w : ℤ) : ℕ :=
  let b := bandNew w
  let U := b.subbankSeeds
  let v := b.seedBound + 1
  shapeSum (terminalShapeNew w) fun q j => ∑ r ∈ Finset.range (U / v + 1),
    (slots U (r*v) - slots U ((r+1)*v)) * (rawWidthAt A w q j - 2*w.toNat*(j+r))

def subbankDebitNew (w : ℤ) : ℕ := sourceDebit w.toNat (terminalShapeNew w)

/-- Remaining obligation (strict test at the 6916 radius); to be discharged like
`Fast063` `test_of_support` per band. -/
def c5At : Prop :=
  ∀ (w : ℤ), 2601 ≤ w → w ≤ 32700 → subbankDebitNew w < seedGainAt 180255 w

end K1_14_At
end PackSource_K1_14_At180255
