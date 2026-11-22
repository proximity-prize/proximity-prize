import ProximityPrize.SubmissionLower.AnchorTopFactor
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace AnchorBlock82190
open K1_13 K1_13_1_1 MvPolynomial
open SoundnessAnchor (Powers)
open private factor_band factor_order factor_ne from ProximityPrize.SubmissionLower.AnchorTopFactor
open private smallContact smallContact_order from ProximityPrize.SubmissionLower.Fast054
noncomputable section

/-- Truncate a homogeneous band after the change of jet coordinates. -/
def blockAt (d s : ℕ) (g : ℤ) : bandSpace d (-g) 48 12 →ₗ[Geom] Form :=
  ((weightedTruncation targetOrder (orderCutoff s g).toNat).comp
    backShift.toLinearMap).domRestrict _

def boundAt (d s : ℕ) (g : ℤ) (v : Powers) : ℕ :=
  let count := bandCount d (-g) 48 12
  if v.degree ≤ d ∧ v.maxIndex ≤ 48 ∧ v.maxTop ≤ 12 then
    let d' := d - v.degree
    let lo' := -g - (v.minIndex : ℤ)
    let hi' := 48 - (v.maxIndex : ℤ)
    let order' := orderCutoff s g - (v.minOrder : ℤ)
    count - (bandCount d' lo' hi' (12 - v.maxTop) - targetCount d' lo' order')
  else count

theorem rank_at (d s : ℕ) (g : ℤ) (v : Powers) :
    Module.finrank Geom (LinearMap.range (blockAt d s g)) ≤ boundAt d s g v := by
  let B := bandSpace d (-g) 48 12
  have hB : Module.Finite Geom B := bandSpace_finite _ _ _ _
  have hBdim : Module.finrank Geom B = bandCount d (-g) 48 12 := finrank_bandSpace _ _ _ _
  unfold boundAt
  dsimp only
  by_cases h : v.degree ≤ d ∧ v.maxIndex ≤ 48 ∧ v.maxTop ≤ 12
  · rw [ite_eq_left h]
    let d' := d - v.degree
    let lo' := -g - (v.minIndex : ℤ)
    let hi' := 48 - (v.maxIndex : ℤ)
    let top' := 12 - v.maxTop
    let order' := orderCutoff s g - (v.minOrder : ℤ)
    let W := bandSpace d' lo' hi' top'
    let Target := targetSpace d' lo' order'
    let small : W →ₗ[Geom] Target := smallContact d' lo' hi' top' order'
    let V := LinearMap.ker small
    have hW : Module.Finite Geom W := bandSpace_finite _ _ _ _
    have hTarget : Module.Finite Geom Target := targetSpace_finite _ _ _
    have hdim : Module.finrank Geom W = bandCount d' lo' hi' top' := finrank_bandSpace _ _ _ _
    have hTdim : Module.finrank Geom Target = targetCount d' lo' order' := finrank_targetSpace _ _ _
    have hsmall : Module.finrank Geom (LinearMap.range small) ≤ Module.finrank Geom Target :=
      Submodule.finrank_le _
    have hsum := small.finrank_range_add_finrank_ker
    have hK : bandCount d' lo' hi' top' - targetCount d' lo' order' ≤
        Module.finrank Geom V := by
      change Module.finrank Geom (LinearMap.range small) + Module.finrank Geom V =
        Module.finrank Geom W at hsum
      omega
    let multiply : W →ₗ[Geom] B :=
      ((LinearMap.mulLeft Geom (v.factor)).domRestrict W).codRestrict B (by
        intro Q
        have hm := bandSpace_mul (factor_band v) Q.property
        have hd : v.degree + d' = d := by dsimp [d']; omega
        have hl : (v.minIndex : ℤ) + lo' = -g := by dsimp [lo']; omega
        have hh : (v.maxIndex : ℤ) + hi' = 48 := by dsimp [hi']; omega
        have ht : v.maxTop + top' = 12 := by dsimp [top']; omega
        change v.factor * (Q : Form) ∈ bandSpace d (-g) 48 12
        simpa only [hd, hl, hh, ht] using hm)
    let embed : V →ₗ[Geom] LinearMap.ker (blockAt d s g) :=
      (multiply.domRestrict V).codRestrict (LinearMap.ker (blockAt d s g)) (by
        intro Q
        apply LinearMap.mem_ker.mpr
        change weightedTruncation targetOrder (orderCutoff s g).toNat
          (backShift (v.factor * (Q : Form))) = 0
        rw [map_mul]
        apply (weightedTruncation_eq_zero_iff _ _ _).mpr
        have hcut : (orderCutoff s g).toNat ≤ v.minOrder + order'.toNat := by
          dsimp [order']; omega
        exact restrictWeightedOrder_anti _ hcut
          (mul_mem_restrictWeightedOrder (factor_order v)
            (smallContact_order (d := d') (lo := lo') (hi := hi') (top := top') (order := order') Q)))
    have hinj : Function.Injective embed := by
      intro P Q he
      have he' : v.factor * (P : Form) = v.factor * (Q : Form) :=
        congrArg (fun P : LinearMap.ker (blockAt d s g) => (P : Form)) he
      exact Subtype.ext (Subtype.ext (mul_left_cancel₀ (factor_ne v) he'))
    have hr := LinearMap.finrank_range_le_sub_of_injective_ker (W := V) (blockAt d s g) embed hinj
    change _ ≤ bandCount d (-g) 48 12 - (bandCount d' lo' hi' top' - targetCount d' lo' order')
    change Module.finrank Geom (LinearMap.range (blockAt d s g)) ≤
      Module.finrank Geom B - Module.finrank Geom V at hr
    omega
  · rw [ite_eq_right h, ← hBdim]
    exact LinearMap.finrank_range_le (blockAt d s g)

#print axioms rank_at
end
end AnchorBlock82190
