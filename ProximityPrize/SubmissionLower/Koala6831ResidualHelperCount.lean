import ProximityPrize.SubmissionLower.Koala6831ResidualLocalTopAvoidance
import ProximityPrize.SubmissionLower.Koala6831MovingCarrierPairs

namespace ProximityPrize.SubmissionLower.Koala6831Residual

open scoped Classical BigOperators
open RCN095 RCN130 RCN135 RCN136 RCN156 RCN234 RCN238 RCN243 RCN275 RCN286 RCN313 RCN319
open LocatorFactorAggregate
open Koala6831MovingPairIncidence (scaledPairFlag)

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {K N : Type} [Field K] [Fintype N]

def helperEnvelope (profile : JetProfile) (support : ResidualSupportParameters) : Envelope :=
  ⟨profile.secondCap + profile.slopeCap * (support.s - 1),
    profile.middleCap + profile.slopeCap * (support.ys - 1),
    profile.totalCap + profile.slopeCap * (support.total - 1)⟩

theorem helperEnvelope_nested (profile : JetProfile) (support : ResidualSupportParameters)
    (h₁ : profile.secondCap ≤ profile.middleCap) (h₂ : profile.middleCap ≤ profile.totalCap) :
    (helperEnvelope profile support).slope ≤ (helperEnvelope profile support).middle ∧
      (helperEnvelope profile support).middle ≤ (helperEnvelope profile support).total := by
  exact ⟨Nat.add_le_add h₁ (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right support.s_le_ys _)),
    Nat.add_le_add h₂ (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right support.ys_le_total _))⟩

private theorem right_surface_flag (Q : MvPolynomial (Fin 4) K) (right : Envelope)
    (hshape : right.slope ≤ right.middle ∧ right.middle ≤ right.total)
    (hQ : wt residualSWeights Q ≤ right.slope ∧ wt residualYSWeights Q ≤ right.middle ∧
      wt residualTotalWeights Q ≤ right.total) :
    PolynomialInFlag right.flag (surfaceMap (polynomialEmbedding K) Q) := by
  let P := surfaceMap (polynomialEmbedding K) Q
  obtain ⟨hR, hM, hT⟩ := surfaceCumulativeFlag_cumulative P
  have h := surfaceMap_nested_weights_le (polynomialEmbedding K) Q
  have hs := hR.trans_le (h.1.trans hQ.1)
  have hm := hM.trans_le (h.2.1.trans hQ.2.1)
  have ht := hT.trans_le (h.2.2.trans hQ.2.2)
  intro d hd
  have hh := polynomialIn_surfaceCumulativeFlag P d hd
  unfold InFlag at hh ⊢
  simp only [Envelope.flag]
  omega

theorem proper_profile_helper_card_mul_le [CharP K 2130706433]
    (profile : JetProfile) (helperSupport support : ResidualSupportParameters)
    (F Q : MvPolynomial (Fin 4) K)
    (hirr : Irreducible F) (hpos : 0 < F.degreeOf (2 : Fin 4))
    (hSupport : ResidualSupportData support F) (hTotal : support.total < 2130706433)
    (hprofile₁ : profile.secondCap ≤ profile.middleCap)
    (hprofile₂ : profile.middleCap ≤ profile.totalCap)
    (hMixed : (helperEnvelope profile helperSupport).middle * support.s +
      support.ys * (helperEnvelope profile helperSupport).slope < 2130706433)
    (nodes : N ↪ K) (u₀ u₁ : N → K) (hn : 181078 ≤ Fintype.card N)
    (hQ : ProperProfileHelper F Q profile helperSupport.s helperSupport.ys helperSupport.total nodes u₀ u₁)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071)
    (hregular : ∀ g ∈ seeds, RegularSolution F (selected g) g)
    (hagreement : ∀ g ∈ seeds, 181078 ≤
      (Finset.univ.filter (fun i => (selected g).eval (nodes i) = u₀ i + g * u₁ i)).card)
    (hpencil : NoLargeSelectedPencil selected seeds 131071 81066) :
    seeds.card * (181078 * (181078 - 131071)) ≤ flagMixed (originalCumulativeFlag F)
      (helperEnvelope profile helperSupport).flag (scaledPairFlag support (Fintype.card N) 131071 181078 81066) := by
  let right := helperEnvelope profile helperSupport
  have hright := helperEnvelope_nested profile helperSupport hprofile₁ hprofile₂
  have hrightM : right.flag.yz + right.flag.all = right.middle := Nat.sub_add_cancel hright.1
  have hrightFlags := right_surface_flag Q right hright hQ.2.1
  have hchar : F.degreeOf (2 : Fin 4) < 2130706433 :=
    hSupport.coordinate_bounds.2.1.trans_lt ((support.s_le_ys.trans support.ys_le_total).trans_lt hTotal)
  have hproper : ¬ F ∣ Q := hirr.isRelPrime_iff_not_dvd.mp hQ.1
  have hpair : (right.flag.yz + right.flag.all) * support.s + support.ys * right.flag.all < 2130706433 := by
    rw [hrightM]
    exact hMixed
  have hQzero : ∀ g ∈ seeds, specialization K (selected g) g Q = 0 := by
    intro g hg
    let agree := Finset.univ.filter (fun i => (selected g).eval (nodes i) = u₀ i + g * u₁ i)
    have hvals : ∀ i ∈ agree, (selected g).eval (nodes i) = u₀ i + u₁ i * g := by
      intro i hi
      rw [mul_comm (u₁ i) g]
      exact (Finset.mem_filter.mp hi).2
    exact hQ.2.2 (selected g) (hdegree g hg) g agree (hagreement g hg) hvals (hregular g hg).1
  rw [← Finset.card_univ (α := N)]
  exact Koala6831MovingCarrierPairs.regular_carrier_seed_card_mul_le support F Q hirr hproper
    2130706433 hpos hchar hSupport right.flag hrightFlags selected seeds Finset.univ nodes u₀ u₁
    nodes.injective.injOn 131071 181078 81066 (by decide) (by decide) (by decide)
    (by simpa using hn) hTotal hpair hdegree (fun g hg => (hregular g hg).1) hQzero
    (fun g hg => (hregular g hg).2) hagreement hpencil

theorem profile_leading_seed_card_mul_le [CharP K 2130706433]
    (profile : JetProfile) (support : ResidualSupportParameters)
    (F : MvPolynomial (Fin 4) K) (P : SecondJetSupport.Poly (K := K))
    (hirr : Irreducible F) (hpos : 0 < F.degreeOf (2 : Fin 4))
    (hSupport : ResidualSupportData support F) (hTotal : support.total < 2130706433)
    (hprofile₁ : profile.secondCap ≤ profile.middleCap)
    (hprofile₂ : profile.middleCap ≤ profile.totalCap)
    (hMixed : profile.middleCap * support.s + support.ys * profile.secondCap < 2130706433)
    (nodes : N ↪ K) (u₀ u₁ : N → K) (hn : 181078 ≤ Fintype.card N)
    (hP : ProfileInterpolant profile nodes u₀ u₁ P)
    (hFT : profile.totalCap < wt residualTotalWeights F)
    (selected : K → Polynomial K) (seeds : Finset K)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071)
    (hregular : ∀ g ∈ seeds, RegularSolution F (selected g) g)
    (hleading : ∀ g ∈ seeds, MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected g)
      (surfaceMap (polynomialEmbedding K) (SecondJetCoefficients.asS P).leadingCoeff) = 0)
    (hagreement : ∀ g ∈ seeds, 181078 ≤
      (Finset.univ.filter (fun i => (selected g).eval (nodes i) = u₀ i + g * u₁ i)).card)
    (hpencil : NoLargeSelectedPencil selected seeds 131071 81066) :
    seeds.card * (181078 * (181078 - 131071)) ≤ flagMixed (originalCumulativeFlag F)
      (Envelope.flag ⟨profile.secondCap, profile.middleCap, profile.totalCap⟩)
      (scaledPairFlag support (Fintype.card N) 131071 181078 81066) := by
  let Q := (SecondJetCoefficients.asS P).leadingCoeff
  let right : Envelope := ⟨profile.secondCap, profile.middleCap, profile.totalCap⟩
  obtain ⟨hcop, hweights⟩ := profile_leading_coprime_and_weights profile P F nodes u₀ u₁ hP hirr hFT
  have hrightM : right.flag.yz + right.flag.all = right.middle := Nat.sub_add_cancel hprofile₁
  have hrightFlags := right_surface_flag Q right ⟨hprofile₁, hprofile₂⟩ hweights
  have hchar : F.degreeOf (2 : Fin 4) < 2130706433 :=
    hSupport.coordinate_bounds.2.1.trans_lt ((support.s_le_ys.trans support.ys_le_total).trans_lt hTotal)
  have hproper : ¬ F ∣ Q := hirr.isRelPrime_iff_not_dvd.mp hcop
  have hpair : (right.flag.yz + right.flag.all) * support.s + support.ys * right.flag.all < 2130706433 := by
    rw [hrightM]
    exact hMixed
  have hQzero : ∀ g ∈ seeds, specialization K (selected g) g Q = 0 := by
    intro g hg
    have he := hleading g hg
    change MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected g)
      (surfaceMap (polynomialEmbedding K) Q) = 0 at he
    rw [RCN222.selectedPoint_surface_evaluation] at he
    exact (polynomialEmbedding_injective K) (by simpa only [map_zero] using he)
  rw [← Finset.card_univ (α := N)]
  exact Koala6831MovingCarrierPairs.regular_carrier_seed_card_mul_le support F Q hirr hproper
    2130706433 hpos hchar hSupport right.flag hrightFlags selected seeds Finset.univ nodes u₀ u₁
    nodes.injective.injOn 131071 181078 81066 (by decide) (by decide) (by decide)
    (by simpa using hn) hTotal hpair hdegree (fun g hg => (hregular g hg).1) hQzero
    (fun g hg => (hregular g hg).2) hagreement hpencil

end

end ProximityPrize.SubmissionLower.Koala6831Residual

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
