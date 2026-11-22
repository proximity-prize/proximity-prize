import ProximityPrize.SubmissionLower.KoalaRectPhysical
import ProximityPrize.SubmissionLower.PortHighBase

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

namespace KoalaRect
noncomputable section
open K1_14 K1_14_1 K1_14_1_8
open K1 (I)
open scoped BigOperators Polynomial
open private Position boundaryMap sourceCoord boundaryDegree sourceCoord_degree jetCoords coords_center
  independent_at_fraction strict_of_ker trueWidth trueWidth_eq_add completeFinite
  from ProximityPrize.SubmissionLower.Fast065
open private zero_of_strict_cutoff from ProximityPrize.SubmissionLower.UpperBranch1

private def rectInclusion {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : rectComplete Crt word s W U →ₗ[L] complete Crt word s W :=
  Submodule.inclusion inf_le_left

private instance rectCompleteFinite {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : Module.Finite L (rectComplete Crt word s W U) := by
  let _ : Module.Finite L (complete Crt word s W) := completeFinite Crt word s W
  exact Module.Finite.of_injective (rectInclusion Crt word s W U)
    (Submodule.inclusion_injective inf_le_left)

private def rectBoundary {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) : rectComplete Crt word s W U →ₗ[L] (Position → L) :=
  (boundaryMap Crt word s W).comp (rectInclusion Crt word s W U)

private theorem rectBoundary_rank {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) :
    Module.finrank L (rectBoundary Crt word s W U).range ≤
      Module.finrank FX (rectEvaluated Crt word s W U) := by
  classical
  let R := rectEvaluated Crt word s W U
  have : Module.Finite FX R := by
    change Module.Finite FX (Submodule.span FX ((rectComplete Crt word s W U).map centerEval.toLinearMap : Set Jet))
    exact Module.Finite.of_fg ((Module.Finite.iff_fg.mp inferInstance).span (A := FX))
  let F := rectBoundary Crt word s W U
  let b := Module.finBasis L F.range
  have hex (k : Fin (Module.finrank L F.range)) :
      ∃ P : rectComplete Crt word s W U, F P = (b k : Position → L) := (b k).property
  choose P hP using hex
  have hli : LinearIndependent L (fun k t =>
      (sourceCoord (P k : Source) t).coeff (boundaryDegree h s W t)) := by
    change LinearIndependent L (F ∘ P)
    have heq : F ∘ P = fun k => ((b k : F.range) : Position → L) := funext hP
    rw [heq]
    exact b.linearIndependent.map' F.range.subtype F.range.ker_subtype
  have heval : LinearIndependent FX (fun k => centerEval (P k : Source)) := by
    apply LinearIndependent.of_comp jetCoords
    have hf : jetCoords ∘ (fun k => centerEval (P k : Source)) =
        fun k t => algebraMap L[X] FX (sourceCoord (P k : Source) t) :=
      funext fun k => funext fun t => coords_center (P k : Source) t
    rw [hf]
    exact independent_at_fraction (fun k => sourceCoord (P k : Source))
      (boundaryDegree h s W) (fun k => sourceCoord_degree (rectInclusion Crt word s W U (P k))) hli
  let u (k : Fin (Module.finrank L F.range)) : R :=
    ⟨centerEval (P k : Source), Submodule.subset_span ⟨_, (P k).property, rfl⟩⟩
  have hu : LinearIndependent FX u := LinearIndependent.of_comp R.subtype heval
  simpa [F, R] using hu.fintype_card_le_finrank

private theorem rectStrict {h : ℕ} {D : PoleData h} {Crt : CRTLift D} {word : I → L}
    {s : Shape} {W : ℕ} {U : Fin 2 → ℕ} (P : (rectBoundary Crt word s W U).ker)
    {j i a : ℕ} {e : Fin 2 →₀ ℕ} (hn : coeffAt (P.1 : Source) j i a e ≠ 0) :
    a + (i+j)*(131071+h) < W+(s.B+s.J)*(2*h)+j := by
  let q : (boundaryMap Crt word s W).ker :=
    ⟨rectInclusion Crt word s W U P.1, LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp P.property)⟩
  exact strict_of_ker q hn

theorem rectTelescope {h : ℕ} (hraw : h ≤ 131070) {D : PoleData h}
    (Crt : CRTLift D) (word : I → L) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ) :
    Module.finrank L (rectComplete Crt word s W U) ≤
      ∑ t ∈ Finset.range (W+1), Module.finrank FX (rectEvaluated Crt word s t U) := by
  induction W with
  | zero =>
    let F := rectBoundary Crt word s 0 U
    have hker : F.ker = ⊥ := by
      apply bot_unique
      intro P hP
      rw [Submodule.mem_bot]
      apply Subtype.ext
      apply zero_of_strict_cutoff hraw Crt s (P : Source) P.property.1.2
      intro j i a e hn
      simpa only [zero_add] using rectStrict (⟨P, hP⟩ : F.ker) hn
    have hr := F.finrank_range_add_finrank_ker
    rw [hker, finrank_bot, add_zero] at hr
    simpa [← hr, F] using rectBoundary_rank Crt word s 0 U
  | succ W ih =>
    rw [Finset.sum_range_succ]
    let F := rectBoundary Crt word s (W+1) U
    have hmem (P : F.ker) : (P.1 : Source) ∈ rectComplete Crt word s W U := by
      refine ⟨⟨⟨?_, P.1.property.1.1.2⟩, P.1.property.1.2⟩, P.1.property.2⟩
      intro j i a e hb
      by_contra hn
      have he : trueEligible h s (W+1) j i a e := by
        by_contra hh
        exact hn (P.1.property.1.1.1 j i a e hh)
      have hl := rectStrict P hn
      exact hb ⟨he.1, he.2.1, he.2.2.1, by omega⟩
    let f := ((rectComplete Crt word s (W+1) U).subtype.comp F.ker.subtype).codRestrict _ hmem
    have hfound : Function.Injective f := by
      intro P Q he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : rectComplete Crt word s W U => (x : Source)) he
    have hker := LinearMap.finrank_le_finrank_of_injective hfound
    have hr := F.finrank_range_add_finrank_ker
    have ha := rectBoundary_rank Crt word s (W+1) U
    change Module.finrank L F.range ≤ _ at ha
    omega

theorem rectAmbient_volume (h : ℕ) (s : Shape) (W : ℕ) (U : Fin 2 → ℕ)
    (hraw : h ≤ 131071) (hbox : U 0 + U 1 ≤ s.U) (hw : rawWidthCond h s W) :
    Module.finrank L (rectAmbient h s W U) =
      area U * shapeSum s (fun q j => W+1+j - q*(131071-h)) +
        2*h*area U*P1_7_1.poleRows s := by
  rw [rectAmbient_finrank _ _ _ _ hbox]
  have hsum : shapeSum s (trueWidth h s W) =
      shapeSum s (fun q j => W+1+j - q*(131071-h)) + 2*h*P1_7_1.poleRows s := by
    unfold P1_7_1.poleRows shapeSum
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro j hj
    exact trueWidth_eq_add hraw hw (by simpa using hq) (by simpa using hj)
  rw [hsum]
  ring

#print axioms rectTelescope
#print axioms rectAmbient_volume
end
end KoalaRect
