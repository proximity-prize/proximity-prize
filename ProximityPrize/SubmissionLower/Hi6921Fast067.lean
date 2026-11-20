import ProximityPrize.SubmissionLower.Fast067
import ProximityPrize.SubmissionLower.Front6921
import ProximityPrize.SubmissionLower.Hi6921Fast007
import ProximityPrize.SubmissionLower.Hi6921Fast023
import ProximityPrize.SubmissionLower.Hi6921Fast029
import ProximityPrize.SubmissionLower.Hi6921Fast035
import ProximityPrize.SubmissionLower.Hi6921Fast048
import ProximityPrize.SubmissionLower.Hi6921Fast051
import ProximityPrize.SubmissionLower.Hi6921Fast057
import ProximityPrize.SubmissionLower.Hi6921Fast061
import ProximityPrize.SubmissionLower.Hi6921P32Split
import ProximityPrize.SubmissionLower.Hi6921P34Cutter
import ProximityPrize.SubmissionLower.Hi6921P3Split
set_option Elab.async false

/- 69.25 specialization of the high-overhead proof in PR 627. -/
section High_K1_14_3_2RCover
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

namespace H21_3_2R

noncomputable section

open K21 H21 H21_3 H21_3_2 Polynomial
open scoped BigOperators Classical
open private coeff_dx from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter
open private dx from ProximityPrize.SubmissionLower.Pack_K1_14_3_4Cutter
open private mass_mono from ProximityPrize.SubmissionLower.Pack_K1_14_3_2Split
open private mass_biUnion from ProximityPrize.SubmissionLower.Pack_K1_14_3_2Split
open private unionCaps from ProximityPrize.SubmissionLower.Pack_K1_14_3_2Split
open private section_le_total from ProximityPrize.SubmissionLower.Pack_K1_14_3_2Split
open private total_le from ProximityPrize.SubmissionLower.Pack_K1_14_3_2Split

export _root_.K1_14_3_2R (constant_ordinate_graph)

open private sum_branches from ProximityPrize.SubmissionLower.Fast067

export _root_.K1_14_3_2R (GraphSections)

open private ordCover from ProximityPrize.SubmissionLower.Fast067

open private allOrdinary from ProximityPrize.SubmissionLower.Fast067

open private allSurfaces from ProximityPrize.SubmissionLower.Fast067

theorem assemble (h1 : H21_3_2.c1) (h3 : H21_3_2.c3) (graphs : GraphSections)
    (h5 : H21_3_2.c5) (h6 : H21_3_2.c6) (h7 : H21_3_2.c7) : H21_3.c2 := by
  classical
  intro u del M Γ F P Q hP hQ hPc hQc hnc hmarks
  obtain ⟨B⟩ := h1 P Q hP hQ hPc hQc hnc
  obtain ⟨qs, hdim, hm, hcover⟩ := allSurfaces h3 graphs B
  obtain ⟨C, hCdeg, hCpoints, hCcover⟩ := h5 qs hdim
  obtain ⟨O, G, hG, hO, hGcaps, hGcover⟩ := h6 qs hdim
  have ha : totalSectionDegree qs .seed ≤ 2891 := total_le (by exact hm.seed)
  have hc : totalSectionDegree qs .ordinate ≤ 60998 := total_le (by exact hm.ordinate)
  have hz : totalSectionDegree qs .mixed ≤ 381269 := total_le (by exact hm.mixed)
  have he : totalSectionDegree qs .jets ≤ 3019828 := total_le (by exact hm.jets)
  let qs' := qs.filter (fun q => SeedDominant q ∧ JetDominant q)
  have hsub : qs' ⊆ qs := Finset.filter_subset _ _
  let seeds : SeedCover := ⟨B.seedContent * C.curve, mul_ne_zero B.seedContent_ne C.curve_ne, C.points⟩
  have hsdeg : C.curve.totalDegree ≤ 381269 := by
    have h := hCdeg.trans hm.mixed
    exact_mod_cast h
  have hspoints : C.points.card ≤ 3019828 := by
    have h := hCpoints.trans hm.jets
    exact_mod_cast h
  refine ⟨{
    parents := qs'
    geometric := ?_
    masses := ⟨(mass_mono hsub .seed).trans hm.seed, (mass_mono hsub .ordinate).trans hm.ordinate,
      (mass_mono hsub .mixed).trans hm.mixed⟩
    jetMass := (mass_mono hsub .jets).trans hm.jets
    seeds := seeds
    seedDegree := ?_
    seedPoints := hspoints
    ordinates := O
    ordinateCount := hO.trans ha
    lowJet := G
    fixedCheap := B.fixedCheap
    fixedLayered := B.fixedLayered
    lowJet_ne := hG
    fixedCheap_ne := B.fixedCheap_ne
    fixedLayered_ne := B.fixedLayered_ne
    lowJet_caps := ?_
    fixedCheap_caps := B.fixedCheap_caps
    fixedLayered_caps := B.fixedLayered_caps
    cover := ?_ }⟩
  · intro q hq
    obtain ⟨hq₀, ht, hj⟩ := Finset.mem_filter.mp hq
    exact h7 q (hdim q hq₀) ht hj
      (((section_le_total hq₀ .seed).trans ha).trans_lt (by decide))
      (((section_le_total hq₀ .jets).trans he).trans_lt (by decide))
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      (by linarith only [B.seedContent_degree, hsdeg])
  · intro v y h
    obtain ⟨hb, hj⟩ := hGcaps v y h
    exact ⟨hb.trans hz, hj.trans hc⟩
  · intro γ hγ
    let z := M.label γ
    let S := F.scalar γ
    obtain ⟨hPγ, hQγ⟩ := hmarks γ hγ
    rcases hcover z S hPγ hQγ with h | h | h | ⟨q, hq, hmark⟩
    · left
      left
      change graphEval z (B.seedContent * C.curve) = 0
      rw [map_mul, h, zero_mul]
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · by_cases ht : SeedDominant q
      · by_cases hj : JetDominant q
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨q, Finset.mem_filter.mpr ⟨hq, ht, hj⟩, hmark⟩))))
        · rcases hGcover q hq ht hj z S hmark with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
      · left
        rcases hCcover q hq ht z S hmark with h | h
        · left
          change graphEval z (B.seedContent * C.curve) = 0
          rw [map_mul, h, mul_zero]
        · exact Or.inr h

end
end H21_3_2R
end High_K1_14_3_2RCover
