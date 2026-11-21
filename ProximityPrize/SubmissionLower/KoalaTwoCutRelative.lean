import ProximityPrize.SubmissionLower.KoalaTwoCutMarks
import ProximityPrize.SubmissionLower.KoalaTwoCutCoverage
import ProximityPrize.SubmissionLower.KoalaTwoSectionPrice

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false

namespace SplitCut.TwoCut
noncomputable section
open MvPolynomial Finset
open K1_14 (FX seedEmbedding)
open P1 (K I node)
open HighCore82219 (FixedWord Band start finish degreeAt quotientOrder)
open HighCore82219Upper (Input ResidueLift Factors componentMarks mem_componentMarks)
open HighCore82219Upper_3 (JetRing graphIdeal markPoint openFactor)
open HighCore82219Upper_3_3 (curveValue wordAt)
open KoalaRectTaylor (Represented EquationAxis equationAxis_iff jetToRect rectIdeal)
open KoalaTwoSectionPrice (liftIndex liftIndex_spec liftIndex_le)
open P1_7_3 (persistentNodes hits_persistent)

abbrev box (J : Input) (v w q : ℕ) := Rect.diagonal (J.e-3) (max 1 v) (max 1 w) q
abbrev eIdeal (J : Input) (v w : ℕ) (P : Ideal JetRing) := P.comap (projectJet J v w)

theorem axes_of_bounds (J : Input) {v w : ℕ}
    (haxis : ∀ i, (J.f.coeff i).degreeOf 0 ≤ v ∧ (J.f.coeff i).degreeOf 1 ≤ w) :
    ∀ z : Fin 2, EquationAxis z J.f (![v,w] z) := by
  intro z
  fin_cases z
  · exact fun i => (haxis i).1
  · exact fun i => (haxis i).2

theorem widen_section {J : Input} {v w r m : ℕ} (he : 4 ≤ J.e) (hr : r ≤ m)
    {P : Ideal JetRing} {f : JetRing} (S : Represented P (KoalaRectTaylor.taylorBox J ![v,w] r) f) :
    Represented P (box J v w (m+liftIndex J.hi v w)) f := by
  let k := liftIndex J.hi v w
  have hrk : r+k ≤ m+k := Nat.add_le_add_right hr _
  obtain ⟨hk,hv,hw⟩ := liftIndex_spec J.hi v w
  have hwides (z : Fin 2) : 2*J.w ≤ k*max 1 (![v,w] z) := by
    apply (Nat.mul_le_mul_left 2 J.upper).trans
    fin_cases z
    · exact hv.trans_eq (Nat.mul_comm _ _)
    · exact hw.trans_eq (Nat.mul_comm _ _)
  have H := KoalaRectTaylor.represented_diagonal he hk hwides S
  have H' : Represented P (box J v w (r+k)) f := by
    simpa [KoalaRectTaylor.diagonalBox, box, Rect.diagonal, Nat.mul_comm] using H
  exact H'.widen hrk
    (Nat.add_le_add (Nat.mul_le_mul_left _ hrk) (Nat.mul_le_mul_left _ hrk))
    (Nat.mul_le_mul_left _ hrk) (Nat.mul_le_mul_left _ hrk)

/-- Apply a represented section as a proper cut on one irreducible marked curve. -/
theorem relative_count (J : Input) (v w : ℕ) (he : 4 ≤ J.e) (P : Ideal JetRing) [P.IsPrime]
    (hDim : (affineHilbertPolynomial (eIdeal J v w P)).natDegree = 1)
    {q : ℕ} {f : JetRing} (hS : Represented P (box J v w q) f) (hf : f ∉ P)
    (T : Finset K) (hOn : ∀ γ ∈ T, P ≤ RingHom.ker (markPoint J γ).toRingHom)
    (hzero : ∀ γ ∈ T, markPoint J γ f = 0) :
    (T.card : ℚ) ≤ q*affineDegree (eIdeal J v w P) := by
  obtain ⟨S,hS⟩ := hS
  let Q := rectIdeal P ⊔ Ideal.span {S.finite}
  have hsQ : S.finite ∈ Q := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hsP : S.finite ∉ rectIdeal P := by
    rw [hS, KoalaRectTaylor.jetToRect_mem_rectIdeal]
    exact hf
  haveI : (rectIdeal P).IsPrime := Ideal.comap_isPrime jetToRect.symm.toRingHom P
  have ha : 0 < J.e-3 := by omega
  refine Rect.relative_cut_points (show rectIdeal P ≤ Q from le_sup_left) ha S hsQ hsP hDim
    T (point J v w) (point_injective J v w).injOn ?_
  intro γ hγ
  have hmark : P ⊔ Ideal.span {f} ≤ RingHom.ker (markPoint J γ).toRingHom :=
    sup_le (hOn γ hγ) ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr (hzero γ hγ)))
  have hT := (mark_on_iff J v w γ (P ⊔ Ideal.span {f})).mpr hmark
  change point J v w γ ∈ zeroLocus FX (Rect.embedded (rectIdeal (P ⊔ Ideal.span {f})) _ _ _) at hT
  rw [rect_sup_span, ← hS] at hT
  exact hT

theorem repeated_count (J : Input) (B : ResidueLift J) (D : Factors J B) (v w : ℕ)
    (he : 4 ≤ J.e) (hlo : J.lo = start .h2367) (hhi : J.hi = finish .h2367)
    (haxis : ∀ z : Fin 2, EquationAxis z J.f (![v,w] z))
    (hword : FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi))
    (P : Ideal JetRing) [P.IsPrime] (hGraph : graphIdeal J B D ≤ P)
    (hDim : (affineHilbertPolynomial (eIdeal J v w P)).natDegree = 1)
    (U : Finset K) (hSub : U ⊆ J.marks)
    (hOn : ∀ γ ∈ U, P ≤ RingHom.ker (markPoint J γ).toRingHom) :
    (U.card : ℚ) ≤ (2*(quotientOrder J.lo+2+liftIndex J.hi v w):ℚ)*affineDegree (eIdeal J v w P) := by
  classical
  let k := liftIndex J.hi v w
  let L := quotientOrder J.lo
  let sites := persistentNodes J.model.word U J.family.scalar
  haveI : (eIdeal J v w P).IsPrime := Ideal.comap_isPrime (projectJet J v w).toRingHom P
  obtain ⟨δ,hδ,hval⟩ := PointCount.curve_degree_nat (‹(eIdeal J v w P).IsPrime›.ne_top) hDim
  have hword' : FixedWord J.model.word U J.family.scalar (degreeAt J.hi) :=
    ⟨hword.distinct.mono hSub, fun γ hγ => hword.degree γ (hSub hγ), fun γ hγ => hword.hits γ (hSub hγ)⟩
  have hD : degreeAt J.hi ≤ 133485 := by rw [hhi]; decide
  have hL : L ≤ 128729 := by dsimp [L]; rw [hlo]; decide
  have hmin : 128657 ≤ J.ell := by
    have hu : J.w ≤ 2414 := J.upper.trans_eq (hhi.trans (by decide))
    change 128657 ≤ 131071 - J.w
    omega
  have hk : k ≤ 4828 := liftIndex_le (hhi.le.trans (by decide)) _ _
  have h₀ : J.ell ≤ L := Nat.sub_le_sub_left J.lower _
  have hCuts (x : I) (hfail : ∃ γ ∈ U, (J.family.scalar γ).eval (node x) ≠ J.model.word x) :
      (U.filter fun γ => (J.family.scalar γ).eval (node x) = J.model.word x).card ≤
        (J.ell-sites.card+k)*δ := by
    obtain ⟨b,a,W⟩ := HighCore82219Upper_3_3_2.proof J sites x
    let f := KoalaRectTaylor.nodeNumerator J B sites x b a
    have hNode (γ : K) (hγ : γ ∈ U) :
        markPoint J γ f = 0 ↔ (J.family.scalar γ).eval (node x) = J.model.word x := by
      obtain ⟨ho,hcv⟩ := HighCore82219Upper_3_3_1.proof J B γ (hSub hγ)
      have hG p (hp : p ∈ graphIdeal J B D) : markPoint J γ p = 0 :=
        RingHom.mem_ker.mp (hOn γ hγ (hGraph hp))
      have hs i (hi : i ∈ sites) :
          curveValue (markPoint J γ) J B i = algebraMap FX FX (wordAt J i) := by
        rw [hcv i, Algebra.algebraMap_self, RingHom.id_apply, wordAt, hits_persistent hγ hi]
      rw [KoalaRectTaylor.node_zero_iff (markPoint J γ) ho hG W hs,
        hcv x, Algebra.algebraMap_self, RingHom.id_apply, wordAt]
      exact seedEmbedding.injective.eq_iff
    have hf : f ∉ P := by
      obtain ⟨γ,hγ,hn⟩ := hfail
      exact fun hf => hn ((hNode γ hγ).mp (RingHom.mem_ker.mp (hOn γ hγ hf)))
    have hsec := KoalaRectTaylor.node_section J B D haxis sites x b a
    have hbody := widen_section he le_rfl (hsec.restrict hGraph)
    let V := U.filter fun γ => (J.family.scalar γ).eval (node x) = J.model.word x
    have hBound := relative_count J v w he P hDim hbody hf V
      (fun γ hγ => hOn γ (mem_filter.mp hγ).1)
      (fun γ hγ => (hNode γ (mem_filter.mp hγ).1).mpr (mem_filter.mp hγ).2)
    rw [hval] at hBound
    exact_mod_cast hBound
  have hC := TwoCutCoverage.repeated_marks hword' hD hmin h₀ hL hk hδ hCuts
  rw [hval]
  exact_mod_cast hC

#print axioms relative_count
#print axioms repeated_count
end
end SplitCut.TwoCut
