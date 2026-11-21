import ProximityPrize.SubmissionLower.KoalaRuledComponents
import ProximityPrize.SubmissionLower.KoalaRuledTangent
import ProximityPrize.SubmissionLower.KoalaTwoSectionPrice
import ProximityPrize.SubmissionLower.KoalaRootSurface

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16000

namespace SplitCut.Rect
noncomputable section
open MvPolynomial
open K1_14 (FX)
open K1_14_6_1 (flatten)
open HighCore82219Upper (Input ResidueLift Factors)
open HighCore82219Upper_3 (JetRing tangentEquation rootIdeal)
open KoalaRectTaylor (jetToRect jetToRect_C)

def inRect (I : Ideal JetRing) : Ideal (Ring FX) := I.comap jetToRect.symm.toRingHom

theorem rectRoot_ideal {J : Input} {B : ResidueLift J} (D : Factors J B) :
    inRect (rootIdeal D) = Ideal.span {rectRoot D} := by
  calc
    inRect (rootIdeal D) = (rootIdeal D).map jetToRect.toRingEquiv :=
      Ideal.comap_symm jetToRect.toRingEquiv
    _ = _ := by rw [rootIdeal, Ideal.map_span, Set.image_singleton]; rfl

def graphCut {J : Input} {B : ResidueLift J} (D : Factors J B) : Ideal (Ring FX) :=
  Ideal.span {rectRoot D} ⊔ Ideal.span {jetToRect (tangentEquation J.f)}

private theorem rect_tangent_regular {J : Input} {B : ResidueLift J} (D : Factors J B)
    (hTangent : IsLeftRegular (Ideal.Quotient.mk (rootIdeal D) (tangentEquation J.f))) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {rectRoot D})
      (jetToRect (tangentEquation J.f))) := by
  rw [← rectRoot_ideal D]
  exact regular_comap jetToRect.symm.toRingHom (I := rootIdeal D)
    (jetToRect.symm_apply_apply (tangentEquation J.f)) hTangent

private theorem rectRoot_degrees {J : Input} {B : ResidueLift J} (D : Factors J B) {v w : ℕ}
    (haxis : ∀ i, (J.f.coeff i).degreeOf 0 ≤ v ∧ (J.f.coeff i).degreeOf 1 ≤ w) :
    (rectRoot D).degreeOf 1 = 0 ∧ ordinateWeight (rectRoot D) ≤ J.e ∧
      (rectRoot D).degreeOf 2 ≤ v ∧ (rectRoot D).degreeOf 3 ≤ w := by
  have hfit : flatten J.f ∈ SplitCut.BoxDegree.space FX J.e v w :=
    SplitCut.Raw.root (f := J.f) le_rfl haxis
  have hmem : rectRoot D ∈ space FX ⟨J.e, 0, v, w⟩ := by
    rw [rectRoot, jetToRect_C]
    exact embed_biform (SplitCut.RootSurface.proper_fit D hfit)
  obtain ⟨hVel, hOrd, hSeed₀, hSeed₁⟩ := (mem_space (d := ⟨J.e, 0, v, w⟩)).mp hmem
  exact ⟨Nat.eq_zero_of_le_zero hVel, by simpa only [Nat.mul_zero, Nat.add_zero] using hOrd,
    hSeed₀, hSeed₁⟩

private theorem mixedLead_root_mono (a b c h : ℕ) {y z s e v w : ℕ}
    (hy : y ≤ e) (hz : z ≤ v) (hs : s ≤ w) :
    2 * mixedLead a b c y z s h 1 v w ≤ 2 * mixedLead a b c e v w h 1 v w := by
  have hy' : (y : ℚ) ≤ (e : ℚ) := by exact_mod_cast hy
  have hz' : (z : ℚ) ≤ (v : ℚ) := by exact_mod_cast hz
  have hs' : (s : ℚ) ≤ (w : ℚ) := by exact_mod_cast hs
  unfold mixedLead
  gcongr

private theorem graphDegree_eq_mixed (e v w : ℕ) (he : 4 ≤ e) :
    (KoalaTwoSectionPrice.graphDegree e v w : ℚ) =
      2 * mixedLead (e - 3 : ℕ) (max 1 v : ℕ) (max 1 w : ℕ) e v w (e - 2 : ℕ) 1 v w := by
  unfold KoalaTwoSectionPrice.graphDegree mixedLead
  dsimp only
  push_cast [Nat.cast_sub (show 3 ≤ e by omega), Nat.cast_sub (show 2 ≤ e by omega),
    Nat.cast_sub (show 1 ≤ e by omega), Nat.cast_sub (show 2 ≤ 2 * e by omega),
    Nat.cast_sub (show 2 ≤ 2 * (e - 1) by omega)]
  ring

private theorem graphCut_mixed_bound (J : Input) {B : ResidueLift J} (D : Factors J B)
    {a b c v w : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (haxis : ∀ i, (J.f.coeff i).degreeOf 0 ≤ v ∧ (J.f.coeff i).degreeOf 1 ≤ w)
    (hg : rectRoot D ≠ 0)
    (hreg : IsLeftRegular (Ideal.Quotient.mk (Ideal.span {rectRoot D})
      (jetToRect (tangentEquation J.f))))
    (hdim : (affineHilbertPolynomial ((graphCut D).comap (project FX a b c))).natDegree = 2) :
    affineDegree ((graphCut D).comap (project FX a b c)) ≤
      2 * mixedLead a b c J.e v w (J.e - 2 : ℕ) 1 v w := by
  obtain ⟨hVel, hOrd, hSeed₀, hSeed₁⟩ := rectRoot_degrees D haxis
  obtain ⟨S, _, hS⟩ := tangent_section_rect J D haxis
  have hregS : IsLeftRegular (Ideal.Quotient.mk (Ideal.span {rectRoot D}) S.finite) := by
    rw [hS]
    exact hreg
  have hle : Ideal.span {rectRoot D} ≤ graphCut D := le_sup_left
  have hle' : Ideal.span {jetToRect (tangentEquation J.f)} ≤ graphCut D := le_sup_right
  have hmem : S.finite ∈ graphCut D := by
    rw [hS]
    exact hle' (Ideal.mem_span_singleton_self _)
  have hdeg := graph_degree (F := FX) (J := graphCut D) (k := tangentBox J v w)
    hg hVel hle S hmem hregS ha hb hc hdim
  exact hdeg.trans (mixedLead_root_mono a b c (J.e - 2) hOrd hSeed₀ hSeed₁)

theorem graph_budget (J : Input) {B : ResidueLift J} (D : Factors J B) {v w : ℕ}
    (hTangent : IsLeftRegular (Ideal.Quotient.mk (rootIdeal D) (tangentEquation J.f)))
    (he : 4 ≤ J.e) (haxis : ∀ i, (J.f.coeff i).degreeOf 0 ≤ v ∧ (J.f.coeff i).degreeOf 1 ≤ w) :
    let G := (graphCut D).comap (project FX (J.e-3) (max 1 v) (max 1 w))
    (affineHilbertPolynomial G).natDegree ≤ 2 ∧
      (∀ P ∈ G.minimalPrimes, (affineHilbertPolynomial P).natDegree = 2) ∧
      affineDegree G ≤ (KoalaTwoSectionPrice.graphDegree J.e v w : ℚ) := by
  classical
  let a := J.e - 3
  let b := max 1 v
  let c := max 1 w
  let G := (graphCut D).comap (project FX a b c)
  change (affineHilbertPolynomial G).natDegree ≤ 2 ∧
    (∀ P ∈ G.minimalPrimes, (affineHilbertPolynomial P).natDegree = 2) ∧
    affineDegree G ≤ (KoalaTwoSectionPrice.graphDegree J.e v w : ℚ)
  by_cases ht : graphCut D = ⊤
  · have htop : G = ⊤ := by
      dsimp only [G]
      rw [ht, Ideal.comap_top]
    rw [htop]
    refine ⟨?_, ?_, ?_⟩
    · simp only [affineHilbertPolynomial_top, Polynomial.natDegree_zero, Nat.zero_le]
    · intro P hP
      rw [Ideal.minimalPrimes_top] at hP
      exact False.elim hP
    · rw [affineDegree_top]
      exact Nat.cast_nonneg _
  have ha : 0 < a := by dsimp only [a]; omega
  have hb : 0 < b := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hc : 0 < c := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hg : rectRoot D ≠ 0 :=
    (map_ne_zero_iff jetToRect jetToRect.injective).mpr
      (Polynomial.C_ne_zero.mpr (HighCore82219Upper_3_2.proper_ne_zero D))
  have hreg := rect_tangent_regular D hTangent
  have hproj : Function.Surjective (project FX a b c) := project_surjective hb hc
  obtain ⟨hdim, hcomp⟩ := graph_pure (project FX a b c) hproj hg hreg ht
  have hdimG : (affineHilbertPolynomial G).natDegree = 2 := hdim
  refine ⟨hdimG.le, fun P hP => hcomp P (Ideal.mem_minimalPrimesFinset.mpr hP), ?_⟩
  rw [graphDegree_eq_mixed J.e v w he]
  exact graphCut_mixed_bound J D ha hb hc haxis hg hreg hdimG

#print axioms graph_budget
end
end SplitCut.Rect
