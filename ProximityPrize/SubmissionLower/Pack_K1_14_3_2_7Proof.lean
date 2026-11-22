import ProximityPrize.SubmissionLower.Fast042
import ProximityPrize.SubmissionLower.Pack_K1_14_2_1Split
import ProximityPrize.SubmissionLower.Fast062
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 300000
namespace K1_14_3_2_7
noncomputable section
open K1 K1_14 K1_14_3 K1_14_3_2 Polynomial
private abbrev Parameters := MvPolynomial (Fin 4) FX
private def jetNodes : JetPlane →+* Parameters :=
  eval₂RingHom (eval₂RingHom MvPolynomial.C (MvPolynomial.X 2)) (MvPolynomial.X 3)
private theorem jetNodes_injective : Function.Injective jetNodes := by
  let r : Parameters →+* JetPlane :=
    MvPolynomial.eval₂Hom (C.comp C) ![0, 0, C Polynomial.X, Polynomial.X]
  have hr : r.comp jetNodes = RingHom.id _ := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext <;> simp [r, jetNodes]
    · simp [r, jetNodes]
  have hi : Function.LeftInverse r jetNodes := fun a => RingHom.congr_fun hr a
  exact hi.injective
private theorem pair_range {T : Type} (f : Fin 2 → T) : Set.range f = {f 0, f 1} := by
  ext a
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
private abbrev Chart (B : Type) [CommRing B] := Projection FX SectionField B
private def jetProjection : Chart JetPlane where
  intoJet := fixedEmbedding
  intoSection := (algebraMap Parameters SectionField).comp jetNodes
  injective := (IsFractionRing.injective Parameters SectionField).comp jetNodes_injective
  baseScalar := C.comp C
  baseVar := ![C Polynomial.X, Polynomial.X]
  ext := by
    intro T _ f g hc hxy
    apply Polynomial.ringHom_ext'
    · exact Polynomial.ringHom_ext hc (hxy 0)
    · exact hxy 1
  scalar_jet := by intro a; simp [fixedEmbedding, scalar]
  coeffMap := algebraMap FX SectionField
  scalar_section := by
    intro a
    simp only [RingHom.comp_apply, jetNodes, coe_eval₂RingHom, eval₂_C]
    exact (IsScalarTower.algebraMap_apply FX Parameters SectionField a).symm
  cutSet := sectionEquations .jets
  cuts := by
    rw [pair_range]
    simp [fixedEmbedding, jetNodes, sectionEquations, sectionScalar, extendScalars, scalar]
private theorem jet_generates :
    Function.Surjective (MvPolynomial.eval₂Hom jetProjection.intoJet seedVar) := by
  let r : Jet →+* MvPolynomial (Fin 2) JetPlane :=
    evaluate (MvPolynomial.C.comp (C.comp C)) MvPolynomial.X
      (MvPolynomial.C (C Polynomial.X)) (MvPolynomial.C Polynomial.X)
  have h : (MvPolynomial.eval₂Hom jetProjection.intoJet seedVar).comp r =
      RingHom.id _ := by
    apply four_ext
    · intro a
      simp only [RingHom.comp_apply, r, evaluate_scalar, MvPolynomial.eval₂Hom_C,
        RingHom.id_apply]
      exact jetProjection.scalar_jet a
    · intro i; simp [r]
    · simp only [RingHom.comp_apply, r, evaluate_y, MvPolynomial.eval₂Hom_C, RingHom.id_apply]
      simp [jetProjection, fixedEmbedding, yVar]
    · simp only [RingHom.comp_apply, r, evaluate_v, MvPolynomial.eval₂Hom_C, RingHom.id_apply]
      simp [jetProjection, fixedEmbedding, vVar]
  exact fun a => ⟨r a, RingHom.congr_fun h a⟩
end
end K1_14_3_2_7
end
