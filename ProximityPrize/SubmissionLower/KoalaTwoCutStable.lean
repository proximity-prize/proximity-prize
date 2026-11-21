import ProximityPrize.SubmissionLower.KoalaTwoCutRelative
import ProximityPrize.SubmissionLower.KoalaCutoffCompat
import ProximityPrize.SubmissionLower.KoalaRuledTangent

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false

namespace SplitCut.TwoCut
noncomputable section
open MvPolynomial Finset
open K1_14 (FX)
open K1_14_6 (Biform)
open K1_14_6_1 (flatten)
open P1 (K I node)
open HighCore82219 (FixedWord Band start finish degreeAt quotientOrder p)
open HighCore82219Upper (Input ResidueLift Factors componentMarks)
open HighCore82219Upper_3 (JetRing graphIdeal markPoint openFactor rootInJet CurveMarks oldNumerator)
open KoalaRectTaylor (Represented EquationAxis jetToRect rectIdeal taylor_agrees)
open KoalaTwoSectionPrice (liftIndex)

def GoodNodes (J : Input) (v w : ℕ) (T : Finset K) : Prop :=
  ∀ (B : ResidueLift J) (D : Factors J B) (C : CurveMarks J B D), C.marks ⊆ T →
    (∀ q ∈ C.prime, StableFlow.action J.f q ∈ C.prime) →
    ∀ x : I, (∃ γ ∈ C.marks, (J.family.scalar γ).eval (node x) ≠ J.model.word x) →
      ∃ g : Biform, g ∈ BoxDegree.space FX J.e (v+128) (w+128) ∧
        rootInJet g ∉ C.prime ∧ ∀ γ ∈ C.marks,
          (J.family.scalar γ).eval (node x) = J.model.word x → markPoint J γ (rootInJet g) = 0

private theorem small_node_box (J : Input) (v w : ℕ) (he : 4 ≤ J.e) (P : Ideal JetRing)
    {g : Biform} (hg : g ∈ BoxDegree.space FX J.e (v+128) (w+128)) :
    Represented P (box J v w 129) (rootInJet g) := by
  apply KoalaRectTaylor.represented_of_mem
  have h : jetToRect (rootInJet g) = Rect.noVelocity g := by
    change jetToRect (Polynomial.C ((optionEquivLeft FX (Fin 2)) g)) = _
    rw [KoalaRectTaylor.jetToRect_C, flatten, AlgEquiv.symm_apply_apply]
  rw [h]
  apply restrictSupport_mono FX _ (Rect.embed_biform hg)
  intro m hm
  obtain ⟨h1,h0,h2,h3⟩ := hm
  change m 1 ≤ 0 at h1
  change m 0 + 2*m 1 ≤ J.e+2*0 at h0
  change m 2 ≤ v+128 at h2
  change m 3 ≤ w+128 at h3
  change m 1 ≤ 129 ∧ m 0+2*m 1 ≤ (J.e-3)*129+2*129 ∧
    m 2 ≤ max 1 v*129 ∧ m 3 ≤ max 1 w*129
  have hp (a : ℕ) : a+128 ≤ max 1 a*129 := by
    have ha := le_max_right 1 a
    have h128 := Nat.mul_le_mul_right 128 (le_max_left 1 a)
    rw [Nat.one_mul] at h128
    rw [show max 1 a*129 = max 1 a+max 1 a*128 by ring]
    exact Nat.add_le_add ha h128
  exact ⟨by omega, by omega, h2.trans (hp v), h3.trans (hp w)⟩

theorem stable_count (J : Input) (B : ResidueLift J) (D : Factors J B) (v w : ℕ)
    (he : 4 ≤ J.e) (hlo : J.lo = start .h2367) (hhi : J.hi = finish .h2367)
    (hword : FixedWord J.model.word J.marks J.family.scalar (degreeAt J.hi))
    (P : Ideal JetRing) [P.IsPrime] (hGraph : graphIdeal J B D ≤ P)
    (hOpen : openFactor J B ∉ P) (hfirst : first J B ∈ P) (hsecond : second J B ∈ P)
    (hSimple : ∀ x ∈ P, ∃ t ∉ P, t*x ∈ firstIdeal J B D)
    (hDim : (affineHilbertPolynomial (eIdeal J v w P)).natDegree = 1)
    (T U : Finset K) (hGood : GoodNodes J v w T) (hTU : U ⊆ T) (hSub : U ⊆ J.marks)
    (hOn : ∀ γ ∈ U, P ≤ RingHom.ker (markPoint J γ).toRingHom) :
    (U.card : ℚ) ≤ (quotientOrder J.lo+2+liftIndex J.hi v w : ℚ)*affineDegree (eIdeal J v w P) := by
  classical
  let L := quotientOrder J.lo
  let k := liftIndex J.hi v w
  let r := J.ell+1
  have hr : 0<r := by dsimp [r]; omega
  have hp : r+1 < p := by
    have hle : J.ell ≤ 131071 := Nat.sub_le _ _
    change J.ell+1+1 < 2130706433
    omega
  have rel₁ := taylor_agrees J B D (r:=r) (j:=r) le_rfl
  have rel₂ := taylor_agrees J B D (r:=r+1) (j:=r+1) le_rfl
  have hOld : oldNumerator J B r ∈ P :=
    (StableFlow.relative_cutoff_mem hGraph hOpen rel₁).mp hfirst
  have hs := StableFlow.relative_cutoff_stable hGraph hOpen hr hp rel₁ rel₂ hfirst hsecond hSimple
  let C : CurveMarks J B D := {
    prime := P
    isPrime := ‹P.IsPrime›
    onGraph := hGraph
    onCutoff := hOld
    regular := hOpen
    marks := U
    sub := hSub
    liesOn := hOn }
  haveI : (eIdeal J v w P).IsPrime := Ideal.comap_isPrime (projectJet J v w).toRingHom P
  obtain ⟨δ,hδ,hval⟩ := PointCount.curve_degree_nat (‹(eIdeal J v w P).IsPrime›.ne_top) hDim
  have hw : FixedWord J.model.word U J.family.scalar (degreeAt J.hi) :=
    ⟨hword.distinct.mono hSub, fun γ hγ => hword.degree γ (hSub hγ), fun γ hγ => hword.hits γ (hSub hγ)⟩
  have hD : degreeAt J.hi ≤ 133511 := by rw [hhi]; decide
  have hL : 128631 ≤ L := by dsimp [L]; rw [hlo]; decide
  have hCuts (x : I) (hFail : ∃ γ ∈ U, (J.family.scalar γ).eval (node x) ≠ J.model.word x) :
      (U.filter fun γ => (J.family.scalar γ).eval (node x) = J.model.word x).card ≤ 129*δ := by
    obtain ⟨g,hg,hn,hits⟩ := hGood B D C hTU hs x hFail
    let V := U.filter fun γ => (J.family.scalar γ).eval (node x) = J.model.word x
    have hR := relative_count J v w he P hDim (small_node_box J v w he P hg) hn V
      (fun γ hγ => hOn γ (mem_filter.mp hγ).1)
      (fun γ hγ => hits γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2)
    rw [hval] at hR
    exact_mod_cast hR
  have hC := TwoCutCoverage.stable_marks hw hD hL (k:=k) hδ hCuts
  rw [hval]
  exact_mod_cast hC

#print axioms stable_count
end
end SplitCut.TwoCut
