import ProximityPrize.SubmissionLower.BCHKSResultantMultiplicity6400

/-!
# Complementary two-axis resultant obstruction at score 64

If a bivariate factor specializes into the affine code component at every
owner slope and every source coordinate, multiplicity counting can be run in
both variable directions.  The two resulting inequalities are incompatible
with the production score-64 parameters unless at least one resultant is
zero.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoAxisResultant6400

open Polynomial
open Polynomial.Bivariate
open BCHKSResultantMultiplicity6400

set_option maxHeartbeats 1000000

def ownerFloor : Nat := 174972148031419761
def coordinateCount : Nat := 262144
def affineLocatorCap : Nat := 185362
def affineChallengeCap : Nat := 163597770632173
def homogeneousLocatorCap : Nat := 54291

/-- Eliminating the unknown transverse degree from the two multiplicity
inequalities.  This lemma also covers `t = 0`; positivity is required only
for the locator degree `d`, which is the degree we cancel. -/
theorem eliminate_transverse_degree
    (d t n u G I : Nat)
    (hd : 0 < d) (huG : u ≤ G) (hndI : n + d ≤ I)
    (howner : d * G ≤ n * t + d * u + d * t)
    (hcoord : t * I ≤ u * d + t * n + t * d) :
    (G - u) * (I - (n + d)) ≤ u * (n + d) := by
  have hownerNorm : d * G ≤ d * u + t * (n + d) := by
    calc
      d * G ≤ n * t + d * u + d * t := howner
      _ = d * u + t * (n + d) := by ring
  have hcoordNorm : t * I ≤ d * u + t * (n + d) := by
    calc
      t * I ≤ u * d + t * n + t * d := hcoord
      _ = d * u + t * (n + d) := by ring
  have hleft : d * (G - u) ≤ t * (n + d) := by
    have hdecomp : d * (G - u) + d * u ≤ d * u + t * (n + d) := by
      calc
        d * (G - u) + d * u = d * G := by
          rw [← Nat.mul_add, Nat.sub_add_cancel huG]
        _ ≤ d * u + t * (n + d) := hownerNorm
    omega
  have hright : t * (I - (n + d)) ≤ d * u := by
    have hdecomp : t * (I - (n + d)) + t * (n + d) ≤
        d * u + t * (n + d) := by
      calc
        t * (I - (n + d)) + t * (n + d) = t * I := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hndI]
        _ ≤ d * u + t * (n + d) := hcoordNorm
    omega
  apply Nat.le_of_mul_le_mul_left _ hd
  calc
    d * ((G - u) * (I - (n + d))) =
        (d * (G - u)) * (I - (n + d)) := by ring
    _ ≤ (t * (n + d)) * (I - (n + d)) :=
      Nat.mul_le_mul_right _ hleft
    _ = (n + d) * (t * (I - (n + d))) := by ring
    _ ≤ (n + d) * (d * u) := Nat.mul_le_mul_left _ hright
    _ = d * (u * (n + d)) := by ring

/-- The strict reverse of the eliminated inequality holds uniformly over the
entire possible locator-factor degree range. -/
theorem production_reverse_elimination
    (d : Nat) (hd : d ≤ homogeneousLocatorCap) :
    affineChallengeCap * (affineLocatorCap + d) <
      (ownerFloor - affineChallengeCap) *
        (coordinateCount - (affineLocatorCap + d)) := by
  norm_num [ownerFloor, coordinateCount, affineLocatorCap,
    affineChallengeCap, homogeneousLocatorCap] at hd ⊢
  omega

/-- At production scale, the owner-axis and coordinate-axis padded
resultants cannot both be nonzero.  All degree drops are already absorbed by
`twoAxis_multiplicity_bounds`; no genericity assumption on a specialization
is hidden here. -/
theorem production_resultant_zero_dichotomy
    {F ι κ : Type} [Field F]
    [DecidableEq F] [DecidableEq ι] [DecidableEq κ]
    (H C : F[X][X])
    (Owners : Finset ι) (owner : ι ↪ F)
    (Coords : Finset κ) (coord : κ ↪ F)
    (d t : Nat)
    (hH : H ≠ 0)
    (hHY : H.natDegree = d)
    (hHX : degreeX H = t)
    (hd : 0 < d)
    (hdcap : d ≤ homogeneousLocatorCap)
    (hCY : C.natDegree ≤ affineLocatorCap)
    (hCX : degreeX C ≤ affineChallengeCap)
    (hOwners : ownerFloor ≤ Owners.card)
    (hCoords : coordinateCount ≤ Coords.card)
    (howner : ∀ i ∈ Owners,
      H.map (Polynomial.evalRingHom (owner i)) ∣
        C.map (Polynomial.evalRingHom (owner i)))
    (hcoord : ∀ i ∈ Coords,
      (swap H).map (Polynomial.evalRingHom (coord i)) ∣
        (swap C).map (Polynomial.evalRingHom (coord i))) :
    Polynomial.resultant H C d affineLocatorCap = 0 ∨
      Polynomial.resultant (swap H) (swap C) t affineChallengeCap = 0 := by
  by_contra hboth
  push Not at hboth
  have hbounds := twoAxis_multiplicity_bounds
    H C Owners owner Coords coord
    d t affineLocatorCap affineChallengeCap
    hH hHY hHX hCY hCX howner hcoord hboth.1 hboth.2
  have hownerBound :
      d * ownerFloor ≤
        affineLocatorCap * t + d * affineChallengeCap + d * t :=
    (Nat.mul_le_mul_left d hOwners).trans hbounds.1
  have hcoordBound :
      t * coordinateCount ≤
        affineChallengeCap * d + t * affineLocatorCap + t * d :=
    (Nat.mul_le_mul_left t hCoords).trans hbounds.2
  have huG : affineChallengeCap ≤ ownerFloor := by
    norm_num [affineChallengeCap, ownerFloor]
  have hndI : affineLocatorCap + d ≤ coordinateCount := by
    norm_num [affineLocatorCap, coordinateCount, homogeneousLocatorCap] at hdcap ⊢
    omega
  have heliminated := eliminate_transverse_degree
    d t affineLocatorCap affineChallengeCap ownerFloor coordinateCount
    hd huG hndI hownerBound hcoordBound
  have hreverse := production_reverse_elimination d hdcap
  exact (Nat.not_lt_of_ge heliminated) hreverse

end BCHKSTwoAxisResultant6400
end ProximityPrize.SubmissionLower
