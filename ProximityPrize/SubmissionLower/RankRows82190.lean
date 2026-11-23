import ProximityPrize.SubmissionLower.AnchorPivotRank82180
import ProximityPrize.SubmissionLower.AnchorNinth82190
import ProximityPrize.SubmissionLower.AnchorBlock82190

set_option Elab.async false
set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

namespace RankRows82190
open AnchorPivot82180 (Data Sound E encode mon sound_monomial monoData sound_one)
open AnchorPivot82190 (allData allPoly all_ok)
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder orderCutoff bandCount bandSpace_finite finrank_bandSpace)
open MvPolynomial
open scoped BigOperators

abbrev Factor := Fin 9 × ℕ
def measure : List Factor → Data
  | [] => Data.unit
  | (i,k)::xs => ((allData i).times k).plus (measure xs)
noncomputable def product : List Factor → Form
  | [] => 1
  | (i,k)::xs => allPoly i^k * product xs
theorem product_ok (xs : List Factor) : Sound (measure xs) (product xs) := by
  induction xs with
  | nil => exact sound_one
  | cons t ts ih => exact ((all_ok t.1).pow t.2).mul ih

structure Row where
  tag : ℕ
  index : ℕ
  ord : ℕ
  e : E
  factors : List Factor
  deriving DecidableEq
def Row.bounds (r : Row) := (monoData r.e).plus (measure r.factors)
noncomputable def Row.form (r : Row) := mon r.e * product r.factors
theorem Row.sound (r : Row) : Sound r.bounds r.form :=
  (sound_monomial r.e).mul (product_ok r.factors)


private theorem band_mono {d a b : ℕ} {l h l' h' : ℤ} (hl : l' ≤ l) (hh : h ≤ h') (ht : a ≤ b) :
    bandSpace d l h a ≤ bandSpace d l' h' b := by
  intro p hp
  apply (MvPolynomial.mem_restrictSupport_iff Geom).mpr
  intro e he
  obtain ⟨hd,hlo,hhi,hf⟩ := (MvPolynomial.mem_restrictSupport_iff Geom).mp hp he
  exact ⟨hd,hl.trans hlo,hhi.trans hh,hf.trans ht⟩


open private independent from ProximityPrize.SubmissionLower.AnchorPivotRank82180


end RankRows82190
