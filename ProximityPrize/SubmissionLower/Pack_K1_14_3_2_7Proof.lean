import ProximityPrize.SubmissionLower.Fast042
import ProximityPrize.SubmissionLower.Pack_K1_14_2_1Split
set_option Elab.async false
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
private def seedNodes : Seeds →+* Parameters :=
  (MvPolynomial.rename (R := FX) (Fin.natAdd 2 : Fin 2 → Fin 4)).toRingHom
private def jetNodes : JetPlane →+* Parameters :=
  eval₂RingHom (eval₂RingHom MvPolynomial.C (MvPolynomial.X 2)) (MvPolynomial.X 3)
private theorem seedNodes_injective : Function.Injective seedNodes := by
  exact MvPolynomial.rename_injective (R := FX) (Fin.natAdd 2) (Fin.natAdd_injective 2 2)
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
private def seedProjection : Chart Seeds where
  intoJet := C.comp C
  intoSection := (algebraMap Parameters SectionField).comp seedNodes
  injective := (IsFractionRing.injective Parameters SectionField).comp seedNodes_injective
  baseScalar := MvPolynomial.C
  baseVar := MvPolynomial.X
  ext := MvPolynomial.ringHom_ext
  scalar_jet := fun _ => rfl
  coeffMap := algebraMap FX SectionField
  scalar_section := by
    intro a
    change algebraMap Parameters SectionField
      (MvPolynomial.rename (Fin.natAdd 2 : Fin 2 → Fin 4) (MvPolynomial.C a)) = _
    rw [MvPolynomial.rename_C]
    exact (IsScalarTower.algebraMap_apply FX Parameters SectionField a).symm
  cutSet := sectionEquations .seed
  cuts := by
    rw [pair_range]
    simp [seedNodes, sectionEquations, sectionScalar, extendScalars, scalar, Fin.natAdd]
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
private theorem seed_generates :
    Function.Surjective (MvPolynomial.eval₂Hom seedProjection.intoJet ![yVar, vVar]) := by
  let r : Jet →+* MvPolynomial (Fin 2) Seeds :=
    evaluate (MvPolynomial.C.comp MvPolynomial.C)
      (fun i => MvPolynomial.C (MvPolynomial.X i)) (MvPolynomial.X 0) (MvPolynomial.X 1)
  have h : (MvPolynomial.eval₂Hom seedProjection.intoJet ![yVar, vVar]).comp r =
      RingHom.id _ := by
    apply four_ext
    · intro a
      simp only [RingHom.comp_apply, r, evaluate_scalar, MvPolynomial.eval₂Hom_C,
        RingHom.id_apply]
      rfl
    · intro i
      simp only [RingHom.comp_apply, r, evaluate_seed, MvPolynomial.eval₂Hom_C,
        RingHom.id_apply]
      rfl
    · simp [r]
    · simp [r]
  exact fun a => ⟨r a, RingHom.congr_fun h a⟩
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
private theorem separable_of_small {F E : Type} [Field F] [CharP F p] [Field E] [Algebra F E]
    [FiniteDimensional F E] (h : Module.finrank F E < p) : Algebra.IsSeparable F E := by
  let : Fact (Nat.Prime p) := ⟨(CharP.char_is_prime_or_zero F p).resolve_right (by decide)⟩
  obtain ⟨n, hn⟩ := finInsepDegree_eq_pow F E p
  apply (isSeparable_iff_finInsepDegree_eq_one F E).mpr
  cases n with
  | zero => simpa using hn
  | succ n =>
    have hle : p ≤ p ^ (n + 1) := by
      rw [pow_succ']
      exact Nat.le_mul_of_pos_right _ (pow_pos (by decide) _)
    have hdvd : p ^ (n + 1) ∣ Module.finrank F E := by
      rw [← hn, ← Field.finSepDegree_mul_finInsepDegree F E]
      exact dvd_mul_left _ _
    exact (not_lt_of_ge (hle.trans (Nat.le_of_dvd Module.finrank_pos hdvd)) h).elim
private theorem generic_point {R G B : Type} [CommRing R] [Field G] [CommRing B] [IsDomain B]
    [CharP (FractionRing B) p] (P : Projection R G B) (x : Fin 2 → Four R)
    (hgen : Function.Surjective (MvPolynomial.eval₂Hom P.intoJet x))
    (I : Ideal (Four R)) [I.IsPrime] (hh : I.height = 2) (hd : I.comap P.intoJet = ⊥)
    (hdeg : Module.finrank G (SectionQuotient P I) < p) :
    ∃ g : Four R →+* AlgebraicClosure (FractionRing B),
      g.comp P.intoJet = (algebraMap (FractionRing B) _).comp (algebraMap B (FractionRing B)) ∧
      RingHom.ker g = I ∧ ∀ a, IsSeparable (FractionRing B) (g a) := by
  let F := FractionRing B
  let E := GenericFibre P.intoJet I
  let : (localizedPrime P.intoJet I).IsMaximal :=
    fibre_maximal P.intoJet x hgen I hd hh
  let : Field E := fibreField P.intoJet I
  let : Module.Finite F E := fibre_finite P.intoJet x hgen I
  rw [section_finrank P I] at hdeg
  let : Algebra.IsSeparable F E := separable_of_small hdeg
  let j := toFibre P.intoJet I
  let e : E →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
  refine ⟨e.toRingHom.comp j, ?_, ?_, fun a =>
    IsSeparable.map e e.injective (Algebra.IsSeparable.isSeparable F (j a))⟩
  · apply RingHom.ext
    intro b
    change e (toFibre P.intoJet I (P.intoJet b)) = _
    rw [← fibre_base P.intoJet I b, e.commutes]
    rfl
  · change RingHom.ker (e.toRingHom.comp j) = _
    rw [RingHom.ker_comp_of_injective _ e.injective]
    exact ker_toFibre P.intoJet I hd
private theorem section_model {B : Type} [CommRing B]
    (P : Chart B) (q : Surface) (s : Slice) (hcoeff : P.coeffMap = algebraMap FX SectionField)
    (hcuts : sectionEquations s = P.cutSet) :
    sectionDegree q s = Module.finrank SectionField (SectionQuotient P q.asIdeal) := by
  have hmap : sectionMap = extendScalars P.coeffMap := by
    rw [hcoeff]
    rfl
  unfold sectionDegree
  rw [hcuts, hmap]
theorem proof : K1_14_3_2.c7 := by
  intro q hh hs hj hds hdj
  let : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  rw [section_model seedProjection q .seed rfl rfl] at hds
  rw [section_model jetProjection q .jets rfl rfl] at hdj
  obtain ⟨gs, hgs, hks, hsep⟩ :=
    generic_point seedProjection ![yVar, vVar] seed_generates q.asIdeal hh hs hds
  obtain ⟨gj, hgj, hkj, hjsep⟩ :=
    generic_point jetProjection seedVar jet_generates q.asIdeal hh hj hdj
  refine ⟨hh, ⟨gs yVar, gs vVar, ?_, hsep _, hsep _⟩, ⟨gj, hgj, hkj, fun i => hjsep _⟩⟩
  have hsEval : seedFibreEval (gs yVar) (gs vVar) = gs := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · apply RingHom.ext
        intro a
        simpa [seedFibreEval, seedGeneric, seedProjection] using
          (RingHom.congr_fun hgs a).symm
      · simp [seedFibreEval, yVar]
    · simp [seedFibreEval, vVar]
  rwa [OnSeedFibre, hsEval]
end
end K1_14_3_2_7
end
