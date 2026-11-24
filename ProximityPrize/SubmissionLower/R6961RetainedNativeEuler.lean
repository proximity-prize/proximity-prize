import ProximityPrize.SubmissionLower.R6961RetainedAxisTransition
import ProximityPrize.SubmissionLower.R6961RetainedAxisPoint
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace Lower6961.RetainedSurfaceClass
open K1_14 (L)
open Lower6961.MonicChart (ChartField)
open RetainedRestrictionTorus Module Submodule LinearMap Lower6960.LineEuler Polynomial
open scoped Lower6961.RetainedSurfaceClass Polynomial
variable (E:Type) [Field E] [Algebra ChartField E]

abbrev LineGlobals (j:Bool) (c:L) := ↥(chartImage E j c false⊓chartImage E j c true)
abbrev LineObstructions (j:Bool) (c:L) := (Axis E j c) ⧸ (chartImage E j c false⊔chartImage E j c true)

theorem native_frames [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]
    (j:Bool) (c:L) (nc:c≠0) :
    ∃ n : ℕ, Nonempty (Basis (Fin n) (Polynomial L) (chartImage E j c false)) ∧
      Nonempty (Basis (Fin n) (Polynomial L) (chartImage E j c true)) := by
  have fin (b:Bool) : Module.Finite (Polynomial L) (chartImage E j c b) := chart_finite E j c b
  have free (b:Bool) : Module.Free (Polynomial L) (chartImage E j c b) := chart_free E j c b
  let bf:=Module.finBasis (Polynomial L) (chartImage E j c false)
  let bi:=Module.finBasis (Polynomial L) (chartImage E j c true)
  let U:=localFreeBasis false bf (nativeMap E j c false) (native_localization E j c nc false)
  let V:=localFreeBasis true bi (nativeMap E j c true) (native_localization E j c nc true)
  have same : finrank (Polynomial L) (chartImage E j c true)=finrank (Polynomial L) (chartImage E j c false) := by
    simpa only [Fintype.card_fin] using (finrank_eq_card_basis V).symm.trans (finrank_eq_card_basis U)
  exact ⟨_,⟨bf⟩,⟨Module.finBasisOfFinrankEq (Polynomial L) _ same⟩⟩

/-- Euler's formula on the actual specialized surface order. The determinant is
computed from its finite and infinity bases, even if the fibre is a proper suborder. -/
theorem native_euler (j:Bool) (c:L) (nc:c≠0) {n : ℕ}
    (bf : Basis (Fin n) (Polynomial L) (chartImage E j c false))
    (bi : Basis (Fin n) (Polynomial L) (chartImage E j c true)) :
    let G:=freeTransition bf bi (nativeMap E j c false) (nativeMap E j c true)
      (native_localization E j c nc false) (native_localization E j c nc true)
    FiniteDimensional L (LineGlobals E j c) ∧ FiniteDimensional L (LineObstructions E j c) ∧
      ∃ d:ℤ,G.det.degree=(d:WithBot ℤ) ∧
        (finrank L (LineGlobals E j c):ℤ)-(finrank L (LineObstructions E j c):ℤ)=n+d := by
  let U:=chartImage E j c false
  let V:=chartImage E j c true
  let ff:=nativeMap E j c false
  let fi:=nativeMap E j c true
  let lf:=native_localization E j c nc false
  let li:=native_localization E j c nc true
  let G:=freeTransition bf bi ff fi lf li
  let tower:=laurent_scalar_tower E j c
  let e:Axis E j c≃ₗ[L](Fin n→Laurent L) := (localFreeBasis false bf ff lf).equivFun.restrictScalars L
  have h0 : (U⊓V).map e.toLinearMap=finiteLattice L (Fin n) ⊓ transitionLattice G := by
    ext w; obtain ⟨v,rfl⟩:=e.surjective w
    rw [Submodule.mem_map_equiv,LinearEquiv.symm_apply_apply]
    change (v∈U ∧ v∈V) ↔ _
    apply Iff.trans _ (free_global_iff bf bi ff fi lf li v).symm
    exact and_congr ⟨fun h=>⟨⟨v,h⟩,rfl⟩,fun ⟨x,eq⟩=>eq ▸ x.property⟩
      ⟨fun h=>⟨⟨v,h⟩,rfl⟩,fun ⟨x,eq⟩=>eq ▸ x.property⟩
  have h1 : (U⊔V).map e.toLinearMap=finiteLattice L (Fin n) ⊔ transitionLattice G := by
    ext w; obtain ⟨v,rfl⟩:=e.surjective w
    rw [Submodule.mem_map_equiv,LinearEquiv.symm_apply_apply,Submodule.mem_sup]
    apply Iff.trans _ (free_boundary_iff bf bi ff fi lf li v).symm
    exact ⟨fun ⟨u,hu,w,hw,s⟩=>⟨⟨u,hu⟩,⟨w,hw⟩,s⟩,fun ⟨u,w,s⟩=>⟨u,u.property,w,w.property,s⟩⟩
  let E0 : LineGlobals E j c≃ₗ[L]H0 G := (e.submoduleMap (U⊓V)).trans (LinearEquiv.ofEq _ _ h0)
  let E1 : LineObstructions E j c≃ₗ[L]H1 G := Submodule.Quotient.equiv _ _ e h1
  have good : IsUnit G := freeTransition_unit (M:=Axis E j c) bf bi ff fi lf li
  obtain ⟨f0,f1,d,ed,index⟩:=euler_index G good
  refine ⟨FiniteDimensional.of_injective E0.toLinearMap E0.injective,
    FiniteDimensional.of_injective E1.toLinearMap E1.injective,d,ed,?_⟩
  rw [E0.finrank_eq,E1.finrank_eq]
  simpa only [Fintype.card_fin] using index

#print axioms native_frames
#print axioms native_euler
end Lower6961.RetainedSurfaceClass
