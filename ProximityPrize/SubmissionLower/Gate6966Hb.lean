import ProximityPrize.SubmissionLower.Gate6966Amb
import ProximityPrize.SubmissionLower.Gate6966Shape
set_option Elab.async false

set_option autoImplicit false

namespace Gate6966Hb

open Gate6966Shape Gate6966Box MvPolynomial
open K1_13_2_2 (JetExp oldWeight gradeWeight)
open Low6966SharedShapeRank (ambient)

theorem weight_top (m : JetExp) : m.weight (Pi.single (3 : Fin 4) 1) = m 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Pi.single_apply]

theorem fitsBox_iff (b j t : ℕ) (m : JetExp) :
    fitsBox b j t m ↔ m.weight (wv 0) ≤ b ∧ m.weight (wv 1) ≤ j ∧ m.weight (wv 2) ≤ t := by
  unfold fitsBox
  have h0 : wv 0 = gradeWeight := rfl
  have h1 : wv 1 = oldWeight := rfl
  have h2 : m.weight (wv 2) = m 3 := weight_top m
  rw [h0, h1, h2]

theorem shp_le_of_mem_boxSpace (b j t : ℕ) (v : ↥ambient) (hv : v ∈ boxSpace b j t) (k : Fin 3) :
    shp k (v : Low6966SharedRational.FractionJet) ≤ ![b, j, t] k := by
  have hs := (mem_restrictSupport_iff _).mp hv
  unfold shp weightedTotalDegree
  apply Finset.sup_le
  intro m hm
  have hf := (Finset.mem_filter.mp (hs hm)).2
  have := (fitsBox_iff b j t m).mp hf
  fin_cases k
  · exact this.1
  · exact this.2.1
  · exact this.2.2

end Gate6966Hb
