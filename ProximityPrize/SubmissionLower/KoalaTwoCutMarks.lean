import ProximityPrize.SubmissionLower.KoalaRectTaylorEval
import ProximityPrize.SubmissionLower.KoalaRelativeCut
import ProximityPrize.SubmissionLower.KoalaCutMultiplicity

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace SplitCut.TwoCut
noncomputable section
open MvPolynomial Finset
open K1_14 (FX)
open P1 (K I)
open HighCore82219Upper (Input ResidueLift Factors componentMarks mem_componentMarks)
open HighCore82219Upper_3 (JetRing graphIdeal markPoint openFactor seedVar rootIdeal tangentEquation)
open HighCore82219Upper_3_2 (mark_regular cutoff_le_mark graph_le_prime)
open KoalaRectTaylor (jetToRect rectIdeal taylorNumerator)
open scoped BigOperators
open private HighCore82219Upper_3.mark_seed from ProximityPrize.SubmissionLower.HighCore82219UpperGeometry

abbrev axis (J : Input) (v w : ℕ) := (Rect.diagonal (J.e-3) (max 1 v) (max 1 w) 1).support
abbrev projectRing (J : Input) (v w : ℕ) := Rect.project FX (J.e-3) (max 1 v) (max 1 w)
abbrev projectJet (J : Input) (v w : ℕ) := jetToRect.symm.toAlgHom.comp (projectRing J v w)

theorem projectJet_surjective (J : Input) (v w : ℕ) :
    Function.Surjective (projectJet J v w) :=
  jetToRect.symm.surjective.comp
    (Rect.project_surjective (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
      (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)))

def point (J : Input) (v w : ℕ) (γ : K) (i : axis J v w) : FX :=
  markPoint J γ (projectJet J v w (MvPolynomial.X i))

theorem aeval_point (J : Input) (v w : ℕ) (γ : K) :
    MvPolynomial.aeval (point J v w γ) = (markPoint J γ).comp (projectJet J v w) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [point]

theorem point_injective (J : Input) (v w : ℕ) : Function.Injective (point J v w) := by
  intro γ η he
  obtain ⟨q,hq⟩ := projectJet_surjective J v w (seedVar 0)
  have hh := congrArg (fun x : axis J v w → FX => MvPolynomial.aeval x q) he
  simp only [aeval_point, AlgHom.comp_apply, hq] at hh
  rw [HighCore82219Upper_3.mark_seed, HighCore82219Upper_3.mark_seed] at hh
  exact sub_left_inj.mp (K1_14.seedEmbedding.injective hh)

theorem mark_on_iff (J : Input) (v w : ℕ) (γ : K) (Q : Ideal JetRing) :
    point J v w γ ∈ zeroLocus FX (Q.comap (projectJet J v w)) ↔
      Q ≤ RingHom.ker (markPoint J γ).toRingHom := by
  constructor
  · intro h q hq
    obtain ⟨x,rfl⟩ := projectJet_surjective J v w q
    have hz := h x hq
    change (MvPolynomial.aeval (point J v w γ)) x = 0 at hz
    apply RingHom.mem_ker.mpr
    change markPoint J γ (projectJet J v w x) = 0
    simpa only [aeval_point, AlgHom.comp_apply] using hz
  · intro h x hx
    change (MvPolynomial.aeval (point J v w γ)) x = 0
    rw [aeval_point, AlgHom.comp_apply]
    exact RingHom.mem_ker.mp (h hx)

theorem rect_sup_span (Q : Ideal JetRing) (f : JetRing) :
    rectIdeal (Q ⊔ Ideal.span {f}) = rectIdeal Q ⊔ Ideal.span {jetToRect f} := by
  have h (I : Ideal JetRing) : rectIdeal I = I.map jetToRect.toRingEquiv :=
    Ideal.comap_symm jetToRect.toRingEquiv
  rw [h, h, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  rfl

theorem proper_graph_mark {J : Input} {B : ResidueLift J} (D : Factors J B) {γ : K}
    (hγ : γ ∈ componentMarks J D.proper) :
    graphIdeal J B D ≤ RingHom.ker (markPoint J γ).toRingHom := by
  obtain ⟨hm,hr⟩ := mem_componentMarks.mp hγ
  exact graph_le_prime (RingHom.ker_isPrime (markPoint J γ).toRingHom)
    (cutoff_le_mark J B D hm hr) (mark_regular J B hm)

abbrev first (J : Input) (B : ResidueLift J) :=
  taylorNumerator J B (J.ell+1) (J.ell+1)
abbrev second (J : Input) (B : ResidueLift J) :=
  taylorNumerator J B (J.ell+2) (J.ell+2)
abbrev firstIdeal (J : Input) (B : ResidueLift J) (D : Factors J B) :=
  graphIdeal J B D ⊔ Ideal.span {first J B}

structure MarkedCutoffs (J : Input) (B : ResidueLift J) (D : Factors J B) : Prop where
  tangent : IsLeftRegular (Ideal.Quotient.mk (rootIdeal D) (tangentEquation J.f))
  regular : IsLeftRegular (Ideal.Quotient.mk (graphIdeal J B D) (first J B))
  first_zero : ∀ γ ∈ componentMarks J D.proper, markPoint J γ (first J B) = 0
  second_zero : ∀ γ ∈ componentMarks J D.proper, markPoint J γ (second J B) = 0

theorem proper_first_mark {J : Input} {B : ResidueLift J} {D : Factors J B}
    (facts : MarkedCutoffs J B D) {γ : K} (hγ : γ ∈ componentMarks J D.proper) :
    firstIdeal J B D ≤ RingHom.ker (markPoint J γ).toRingHom :=
  sup_le (proper_graph_mark D hγ) ((Ideal.span_singleton_le_iff_mem _).mpr
    (RingHom.mem_ker.mpr (facts.first_zero γ hγ)))

theorem lift_simple {P Q : Ideal JetRing} [P.IsPrime]
    (J : Input) (v w : ℕ) (hP : (P.comap (projectJet J v w)) ∈ (Q.comap (projectJet J v w)).minimalPrimes)
    (hwt : K1_13_6_3_5.boundaryWeight (Q.comap (projectJet J v w))
        (P.comap (projectJet J v w)) = 1)
    (hDegree : (affineHilbertPolynomial (Q.comap (projectJet J v w))).natDegree ≤ 1) :
    ∀ q ∈ P, ∃ t ∉ P, t*q ∈ Q := by
  let φ := projectJet J v w
  have : (P.comap φ).IsPrime := Ideal.comap_isPrime φ.toRingHom P
  have hfin := (SplitCut.CutMultiplicity.coefficient_budget (Q.comap φ) 1 hDegree).1 (P.comap φ) hP
  have hs := SplitCut.CutMultiplicity.simple_saturation (P := P.comap φ) hfin hwt
  intro q hq
  obtain ⟨p,rfl⟩ := projectJet_surjective J v w q
  obtain ⟨r,hr,hrp⟩ := hs p hq
  exact ⟨φ r, hr, by simpa only [map_mul] using (show φ (r*p) ∈ Q from hrp)⟩

#print axioms point_injective
#print axioms lift_simple
end
end SplitCut.TwoCut
