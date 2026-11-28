import ProximityPrize.SubmissionLower.R6970SpreadWide6970
import ProximityPrize.SubmissionLower.Z6969Pack0632

set_option Elab.async false
set_option autoImplicit false

namespace Research6970.Height2313.Classification
noncomputable section
open Finset Polynomial
open K1_14 (L Equation)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (Surface Parent ProjectedProduct SeedField)
open Research6966
open Research6969
open Research6969.TransitionClassification (agreement grade content maxGraph band classify lower_bound)

theorem classify_from2313 {h:ℕ} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    (lo:2308≤h) (hi:h≤2557) (b:Fin 8) (S:Finset Surface) (live:S.Nonempty)
    (geo:∀q∈S,Parent q) (pass:∀q∈S,TerminalBanks.Pass Crt word agreement SpreadCatalogue.shape q)
    {f:Equation} (whole:ProjectedProduct S f) (large:grade b≤f.natDegree) :
    ∃ G:Pade.Row SeedField, G.primitive ∧ G.graphDegree≤maxGraph b ∧
      Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) (content b) := by
  by_cases inBand : h ≤ 2313
  · fin_cases b
    · exact SpreadWide6970.classify22 lo inBand Crt word S live geo pass whole (large.trans' (by decide))
    · exact SpreadWide6970.classify22 lo inBand Crt word S live geo pass whole (large.trans' (by decide))
    · exact SpreadWide6970.classify24 (lo.trans' (by decide)) inBand Crt word S live geo pass whole
        (large.trans' (by decide))
    · exact SpreadWide6970.classify28 lo inBand Crt word S live geo pass whole (large.trans' (by decide))
    · exact SpreadWide6970.classify28 lo inBand Crt word S live geo pass whole (large.trans' (by decide))
    · exact SpreadWide6970.classify37 lo inBand Crt word S live geo pass whole (large.trans' (by decide))
    · obtain ⟨G, prime, deg, control⟩ := SpreadWide6970.classify37 lo inBand Crt word S live geo pass whole
        (large.trans' (by decide))
      exact ⟨G, prime, deg, fun t v valid => (control t v valid).trans (by decide)⟩
    · obtain ⟨G, prime, deg, control⟩ := SpreadWide6970.classify64 lo inBand Crt word S live geo pass whole
        (large.trans' (by decide))
      exact ⟨G, prime, deg, fun t v valid => (control t v valid).trans (by decide)⟩
  exact classify Crt word (by omega) hi b S live geo pass whole large

theorem graph_above_twenty_one_from2313 {h:ℕ} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    (lo:2308≤h) (hi:h≤2557) (S:Finset Surface) (live:S.Nonempty)
    (geo:∀q∈S,Parent q) (pass:∀q∈S,TerminalBanks.Pass Crt word agreement SpreadCatalogue.shape q)
    {f:Equation} (whole:ProjectedProduct S f) (large:22≤f.natDegree) :
    ∃ G:Pade.Row SeedField,G.primitive ∧ G.graphDegree≤maxGraph (band f.natDegree) ∧
      Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) (content (band f.natDegree)) :=
  classify_from2313 Crt word lo hi (band f.natDegree) S live geo pass whole (lower_bound large)


end
end Research6970.Height2313.Classification
