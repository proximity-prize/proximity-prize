import ProximityPrize.SubmissionLower.LivePoles
import ProximityPrize.SubmissionLower.PoleGlobal
import ProximityPrize.SubmissionLower.HighSource6921Rank
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 24
namespace StructuredSource
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_7 Polynomial
open scoped Polynomial BigOperators

/-- The block bound charges the actual CRT source even when its special
primary blocks contain repeated roots. -/
theorem physical_to_complete (h : ℕ) (hh : 0<h) (hp : h<K1.p) (D : PoleData h)
    (Crt : CRTLift D) (word : I → L) (s : Shape) (W : ℕ) :
    Module.finrank L (contacted h word s W) ≤
      (2*h)*PoleGlobal.blockSum s + Module.finrank L (complete Crt word s W) := by
  classical
  obtain ⟨E,hnonzero⟩ := LivePoles.deformation h hh hp D Crt
  have h4 : K1_14_1_7.c4 := @K1_14_1_7_4.proof
  let A := contacted h word s W
  let _ : Module.Finite L A := contacted_finite h word s W
  let d := Module.finrank L A
  let basis := Module.finBasis L A
  let P : Fin d → Source := fun k => basis k
  have hP (k : Fin d) : Shaped s (P k) := contacted_shaped (basis k).property
  obtain ⟨n, M, hs, hg⟩ := h4 E s (Fin d) P hP
  have hgen := PoleGlobal.simple_rank_le E.genericPoles hnonzero s _
    (fun k => shaped_map (genericPoint.comp (Polynomial.C (R := L))) (hP k)) _ hg
  have hrank := (specialization_rank_le M).trans hgen
  let f := (M.map specialPoint).mulVecLin
  have hf : ∀ v : Fin d → L,
      Fintype.linearCombination L P v = ((basis.equivFun.symm v : A) : Source) := by
    intro v
    rw [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply]
    symm
    simpa only [map_smul, Submodule.subtype_apply, P] using
      map_sum A.subtype (fun k => v k • basis k) Finset.univ
  have hk (v : LinearMap.ker f) :
      ((basis.equivFun.symm (v : Fin d → L) : A) : Source) ∈ complete Crt word s W := by
    have hv := (hs v.val).mp (LinearMap.mem_ker.mp v.property)
    rw [hf] at hv
    exact ⟨(basis.equivFun.symm v.val).property, hv⟩
  let g : LinearMap.ker f →ₗ[L] complete Crt word s W :=
    LinearMap.codRestrict _ ((A.subtype.comp basis.equivFun.symm.toLinearMap).comp
      (LinearMap.ker f).subtype) hk
  let _ : Module.Finite L (complete Crt word s W) :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left)
      (Submodule.inclusion_injective _)
  have hginj : Function.Injective g := by
    intro v w hvw
    apply Subtype.ext
    apply basis.equivFun.symm.injective
    apply Subtype.ext
    exact congrArg (fun x : complete Crt word s W => (x : Source)) hvw
  have hkd := LinearMap.finrank_le_finrank_of_injective hginj
  have hdf := f.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, Fintype.card_fin] at hdf
  change Module.finrank L (LinearMap.range f) ≤ _ at hrank
  change d ≤ _
  omega


/-- A replacement source floor at the existing bank interface. The conservative
quantity subtracted here is the same raw-volume credit used by the old source. -/
theorem source_floor (h : ℕ) (lo : 2442 ≤ h) (hi : h ≤ 32970)
    (D : PoleData h) (Crt : CRTLift D) (word : I → L) (s : Shape) (W : ℕ)
    (hw : rawWidthCond h s W) :
    rawVolumeAt h s W ≤ physicalDebit s + (2*h*PoleGlobal.blockSum s - poleCredit h s) +
      ∑ t ∈ Finset.range (W+1), Module.finrank FX (evaluated Crt word s t) := by
  have a := HighSource6921.Ambient.proof h lo hi s W hw
  have b := HighSource6921.Physical.proof h lo hi word s W
  have c := physical_to_complete h (by omega) (by change h < 2130706433; omega) D Crt word s W
  have d := HighSource6921.Telescope.proof h lo hi D Crt word s W
  omega

end
end StructuredSource
