import ProximityPrize.SubmissionLower.UpperBranch1
import ProximityPrize.SubmissionLower.Rect51PoleWindowNode
import ProximityPrize.SubmissionLower.Rect51PoleWindowRank

/-! Square terminal bank. See the public kaankolcu 69.50 note,
submission f9161583-1b70-4048-8a65-bae6ee236fe4. -/
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
set_option maxSynthPendingDepth 32
namespace Rect51Bank
noncomputable section

open K1 (I)
open K1_14 (L FX Shape Jet Equation)
open K1_14_1
open Polynomial Finset
open scoped Polynomial BigOperators
open private Position sourceCoord jetCoords coords_center scalarPoly_coeff boundaryMap boundaryDegree
  sourceCoord_degree independent_at_fraction strict_of_ker completeFinite
  from ProximityPrize.SubmissionLower.Fast065
open private zero_of_strict_cutoff from ProximityPrize.SubmissionLower.UpperBranch1

variable {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : I→L) (s : Shape)
    (S : Submodule L Source)

def restricted (W : ℕ) : Submodule L Source := complete Crt word s W ⊓ S

instance (W : ℕ) : Module.Finite L (restricted Crt word s S W) :=
  by
  letI : Module.Finite L (complete Crt word s W) := completeFinite Crt word s W
  letI : IsNoetherian L (complete Crt word s W) := isNoetherian_of_isNoetherianRing_of_finite L (↥(complete Crt word s W))
  exact Module.Finite.of_injective
    (Submodule.inclusion (show restricted Crt word s S W≤complete Crt word s W from inf_le_left))
    (Submodule.inclusion_injective _)

def evaluated (W : ℕ) : Submodule FX Jet :=
  Submodule.span FX (centerEval '' (restricted Crt word s S W : Set Source))

instance (W : ℕ) : Module.Finite FX (evaluated Crt word s S W) := by
  change Module.Finite FX (Submodule.span FX
    ((restricted Crt word s S W).map centerEval.toLinearMap : Set Jet))
  exact Module.Finite.of_fg ((Module.Finite.iff_fg.mp inferInstance).span (A := FX))

theorem evaluated_le (W : ℕ) : evaluated Crt word s S W ≤ K1_14_1.evaluated Crt word s W := by
  apply Submodule.span_mono
  rintro _ ⟨P,hP,rfl⟩
  exact ⟨P,hP.1,rfl⟩

private def boundary (W : ℕ) : restricted Crt word s S W →ₗ[L] (Position→L) :=
  (boundaryMap Crt word s W).comp (Submodule.inclusion inf_le_left)

private theorem boundary_rank (W : ℕ) :
    Module.finrank L (boundary Crt word s S W).range ≤
      Module.finrank FX (evaluated Crt word s S W) := by
  classical
  let F := boundary Crt word s S W
  let b := Module.finBasis L F.range
  have hex (k : Fin (Module.finrank L F.range)) :
      ∃ P : restricted Crt word s S W, F P = (b k : Position→L) := (b k).property
  choose P hP using hex
  have hli : LinearIndependent L (fun k t =>
      (sourceCoord (P k : Source) t).coeff (boundaryDegree h s W t)) := by
    change LinearIndependent L (F ∘ P)
    have heq : F ∘ P = fun k => ((b k : F.range) : Position→L) := funext hP
    rw [heq]
    exact b.linearIndependent.map' F.range.subtype F.range.ker_subtype
  have heval : LinearIndependent FX (fun k=>centerEval (P k : Source)) := by
    apply LinearIndependent.of_comp jetCoords
    have heq : jetCoords ∘ (fun k=>centerEval (P k : Source)) =
        fun k t=>algebraMap L[X] FX (sourceCoord (P k : Source) t) :=
      funext fun k=>funext fun t=>coords_center (P k : Source) t
    rw [heq]
    exact independent_at_fraction (fun k=>sourceCoord (P k : Source)) (boundaryDegree h s W)
      (fun k=>sourceCoord_degree (⟨(P k).val,(P k).property.1⟩ : complete Crt word s W)) hli
  let u (k : Fin (Module.finrank L F.range)) : evaluated Crt word s S W :=
    ⟨centerEval (P k : Source),Submodule.subset_span ⟨_,(P k).property,rfl⟩⟩
  have hu : LinearIndependent FX u :=
    LinearIndependent.of_comp (evaluated Crt word s S W).subtype heval
  simpa only [F,Fintype.card_fin] using hu.fintype_card_le_finrank

private def restrict_ker (W : ℕ) (P : (boundary Crt word s S W).ker) :
    (boundaryMap Crt word s W).ker :=
  ⟨⟨P.1.val,P.1.property.1⟩,P.property⟩

private theorem ker_step (W : ℕ) :
    Module.finrank L (boundary Crt word s S (W+1)).ker ≤
      Module.finrank L (restricted Crt word s S W) := by
  let F := boundary Crt word s S (W+1)
  have hm (P : F.ker) : (P.1 : Source) ∈ restricted Crt word s S W := by
    refine ⟨⟨⟨?_,P.1.property.1.1.2⟩,P.1.property.1.2⟩,P.1.property.2⟩
    intro j i a e hb
    by_contra hn
    have he : trueEligible h s (W+1) j i a e := by
      by_contra hh
      exact hn (P.1.property.1.1.1 j i a e hh)
    have hl := strict_of_ker (restrict_ker Crt word s S (W+1) P) hn
    exact hb ⟨he.1,he.2.1,he.2.2.1,by omega⟩
  let f := ((restricted Crt word s S (W+1)).subtype.comp F.ker.subtype).codRestrict
    (restricted Crt word s S W) hm
  apply LinearMap.finrank_le_finrank_of_injective (f := f)
  intro P Q he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : restricted Crt word s S W => (x : Source)) he

private theorem ker_zero (hh : h≤131070) : (boundary Crt word s S 0).ker=⊥ := by
  apply bot_unique
  intro P hP
  rw [Submodule.mem_bot]
  apply Subtype.ext
  let z := restrict_ker Crt word s S 0 ⟨P,hP⟩
  have hz : (z.1 : Source) = P.val := by dsimp [z,restrict_ker]
  apply zero_of_strict_cutoff hh Crt s P.val P.property.1.2
  intro j i a e hn
  simpa only [Nat.zero_add] using strict_of_ker z (show coeffAt (z.1 : Source) j i a e ≠ 0 from hz.symm ▸ hn)

theorem telescope (hh : h≤131070) (W : ℕ) :
    Module.finrank L (restricted Crt word s S W)≤
      ∑ j∈range (W+1),Module.finrank FX (evaluated Crt word s S j) := by
  induction W with
  | zero =>
    have hr := LinearMap.finrank_range_add_finrank_ker (K := L) (V := ↥(restricted Crt word s S 0)) (V₂ := Position → L) (boundary Crt word s S 0)
    rw [ker_zero Crt word s S hh,finrank_bot,add_zero] at hr
    simpa [← hr] using boundary_rank Crt word s S 0
  | succ W ih =>
    rw [sum_range_succ]
    have hr := LinearMap.finrank_range_add_finrank_ker (K := L) (V := ↥(restricted Crt word s S (W+1))) (V₂ := Position → L) (boundary Crt word s S (W+1))
    have ha := boundary_rank Crt word s S (W+1)
    have hb := ker_step Crt word s S W
    omega


open K1_14_1_7 (PoleTest)
open Rect51PoleWindow (square rectAmbientVolume rectPoleCredit rectPhysicalDebit
  rectAmbient_finite rectAmbientBound rectPhysicalBound rectShaped_of_mem finrank_le_of_pole)
open P1_7_1 (poleRows groupedPoleMoment)

theorem rank_floor (hpos : 0<h) (hhi : h≤131070) (hchar : h<K1.p)
    (W U : ℕ) (hUs : 2*U≤s.U) (hw : rawWidthCond h s W) :
    rectAmbientVolume h s W U ≤ rectPhysicalDebit s U +
      2*h*(U+1)*groupedPoleMoment s.B s.J +
      ∑ j∈range (W+1),Module.finrank FX (evaluated Crt word s (square U) j) := by
  let A : Submodule L Source := contacted h word s W ⊓ square U
  let T := restricted Crt word s (square U) W
  have hAw : A≤ambient h s W ⊓ square U := le_inf
    (inf_le_left.trans (show contacted h word s W≤ambient h s W from inf_le_left)) inf_le_right
  letI : Module.Finite L (ambient h s W ⊓ square U : Submodule L Source) :=
    rectAmbient_finite h s W U hUs
  letI : Module.Finite L A :=
    Module.Finite.of_injective (Submodule.inclusion hAw) (Submodule.inclusion_injective _)
  letI : Module.Finite L T := inferInstanceAs (Module.Finite L (restricted Crt word s (square U) W))
  have hAmbient := rectAmbientBound (hhi.trans (Nat.le_succ _)) s W U hw hUs
  have hPhysical := rectPhysicalBound h word s W U
  have hPole := finrank_le_of_pole hpos hchar Crt s U A T
    (fun P hP=>rectShaped_of_mem (hAw hP).1 (hAw hP).2)
    (fun P hA htest=>⟨⟨hA.1,htest⟩,hA.2⟩)
  have hTelescope := telescope Crt word s (square U) hhi W
  have hDebit : Rect51PoleWindow.debit h s U =
      rectPoleCredit h s U+2*h*(U+1)*groupedPoleMoment s.B s.J := by
    unfold Rect51PoleWindow.debit rectPoleCredit poleRows
    ring
  rw [hDebit] at hPole
  change _ ≤ _ + Module.finrank L A at hPhysical
  change Module.finrank L T≤_ at hTelescope
  omega

#print axioms telescope
#print axioms rank_floor
end
end Rect51Bank
