import ProximityPrize.SubmissionLower.KoalaRuledBudget
import ProximityPrize.SubmissionLower.KoalaRectTaylorCharts

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16000

namespace SplitCut.Rect
noncomputable section
open MvPolynomial
open K1_14 (FX)
open HighCore82219Upper (Input ResidueLift Factors)
open HighCore82219Upper_3 (JetRing tangentEquation rootIdeal graphIdeal openFactor)
open KoalaRectTaylor (jetToRect rectIdeal)

theorem graphCut_eq {J : Input} {B : ResidueLift J} (D : Factors J B) :
    rectIdeal (Ideal.span {Polynomial.C D.proper, tangentEquation J.f}) = graphCut D := by
  let I : Ideal JetRing := Ideal.span {Polynomial.C D.proper, tangentEquation J.f}
  have hmap : rectIdeal I = I.map jetToRect.toRingEquiv := Ideal.comap_symm jetToRect.toRingEquiv
  change rectIdeal I = graphCut D
  rw [hmap]
  dsimp only [I]
  rw [Ideal.map_span, Set.image_pair, ← Set.singleton_union, Ideal.span_union]
  rfl

theorem graph_saturation {J : Input} {B : ResidueLift J} (D : Factors J B) (p : Ring FX) :
    p ∈ rectIdeal (graphIdeal J B D) ↔
      ∃ n : ℕ, (jetToRect (openFactor J B))^n*p ∈ graphCut D := by
  let I : Ideal JetRing := Ideal.span {Polynomial.C D.proper, tangentEquation J.f}
  let s := openFactor J B
  have hcut : rectIdeal I = graphCut D := graphCut_eq D
  have hpow (n : ℕ) : jetToRect.symm ((jetToRect s)^n * p) = s^n * jetToRect.symm p := by
    rw [map_mul, map_pow, AlgEquiv.symm_apply_apply]
  rw [← hcut]
  change (∃ n : ℕ, s^n * jetToRect.symm p ∈ I) ↔
    ∃ n : ℕ, jetToRect.symm ((jetToRect s)^n * p) ∈ I
  simp only [hpow]

theorem saturation_surface_budget {F σ : Type*} [Field F] [Finite σ]
    {I G : Ideal (MvPolynomial σ F)} {u : MvPolynomial σ F} {price : ℚ}
    (hSat : ∀ p, p ∈ G ↔ ∃ n : ℕ, u^n * p ∈ I) (hG : G ≠ ⊤)
    (hbase : (affineHilbertPolynomial I).natDegree ≤ 2 ∧
      (∀ P ∈ I.minimalPrimes, (affineHilbertPolynomial P).natDegree = 2) ∧
      affineDegree I ≤ price) :
    (affineHilbertPolynomial G).natDegree = 2 ∧
      (∀ P ∈ G.minimalPrimes, (affineHilbertPolynomial P).natDegree = 2) ∧
      affineDegree G ≤ price := by
  obtain ⟨hI, hPure, hPrice⟩ := hbase
  have hIG : I ≤ G := by
    intro p hp
    exact (hSat p).mpr ⟨0, by simpa only [pow_zero, one_mul] using hp⟩
  have hSub := saturation_components hIG hSat
  have hPureG P (hP : P ∈ G.minimalPrimes) : (affineHilbertPolynomial P).natDegree = 2 :=
    hPure P (hSub hP)
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes hG
  have hmono := natDegree_affineHilbertPolynomial_le_of_le hIG
  have hGdim : (affineHilbertPolynomial G).natDegree = 2 := by
    refine le_antisymm (hmono.trans hI) ?_
    rw [← hPureG P hP]
    exact natDegree_affineHilbertPolynomial_le_of_le hP.le
  have hIdim : (affineHilbertPolynomial I).natDegree = 2 :=
    le_antisymm hI (hGdim.symm.le.trans hmono)
  have hcoeff := leadingCoeff_affineHilbertPolynomial_le_of_le hIG (hGdim.trans hIdim.symm)
  have hdegree : affineDegree G ≤ affineDegree I := by
    simp only [affineDegree, hGdim, hIdim]
    exact mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
  exact ⟨hGdim, hPureG, hdegree.trans hPrice⟩

theorem graph_sat_budget (J : Input) {B : ResidueLift J} (D : Factors J B) {v w : ℕ}
    (hTangent : IsLeftRegular (Ideal.Quotient.mk (rootIdeal D) (tangentEquation J.f)))
    (he : 4 ≤ J.e) (haxis : ∀ i, (J.f.coeff i).degreeOf 0 ≤ v ∧ (J.f.coeff i).degreeOf 1 ≤ w)
    (hProper : rectIdeal (graphIdeal J B D) ≠ ⊤) :
    let G := (rectIdeal (graphIdeal J B D)).comap (project FX (J.e-3) (max 1 v) (max 1 w))
    (affineHilbertPolynomial G).natDegree = 2 ∧
      (∀ P ∈ G.minimalPrimes, (affineHilbertPolynomial P).natDegree = 2) ∧
      affineDegree G ≤ (KoalaTwoSectionPrice.graphDegree J.e v w : ℚ) := by
  let a := J.e - 3
  let b := max 1 v
  let c := max 1 w
  let φ := project FX a b c
  let S := rectIdeal (graphIdeal J B D)
  let I := (graphCut D).comap φ.toRingHom
  let G := S.comap φ.toRingHom
  have hb : 0 < b := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hc : 0 < c := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hφ : Function.Surjective φ := project_surjective hb hc
  obtain ⟨u, hu⟩ := hφ (jetToRect (openFactor J B))
  have hSat (p) : p ∈ G ↔ ∃ n : ℕ, u^n * p ∈ I := by
    change φ p ∈ rectIdeal (graphIdeal J B D) ↔ ∃ n : ℕ, φ (u^n * p) ∈ graphCut D
    simpa only [map_mul, map_pow, hu] using graph_saturation D (φ p)
  have hG : G ≠ ⊤ := by
    intro h
    have hmap := congrArg (Ideal.map φ.toRingHom) h
    change (S.comap φ.toRingHom).map φ.toRingHom = Ideal.map φ.toRingHom ⊤ at hmap
    rw [Ideal.map_comap_of_surjective φ.toRingHom hφ, Ideal.map_top] at hmap
    exact hProper hmap
  exact saturation_surface_budget hSat hG (graph_budget J D hTangent he haxis)

#print axioms graph_saturation
#print axioms graph_sat_budget
end
end SplitCut.Rect
