import ProximityPrize.SubmissionLower.CurveListCoupledSlab

set_option autoImplicit false

namespace CurveListCoupledCap
noncomputable section
open MeasureTheory Set Filter
open scoped Pointwise Topology
open K1_13_5_4_2 (capBody)
open K1_13_5_4_2_5 (FirstBody)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport volumeQuotient)
open private K1_13_5_4_2_5_2_2.support support_attains form_fun form_apply
  from ProximityPrize.SubmissionLower.Fast070
local notation "faceSupport" => K1_13_5_4_2_5_2_2.support

theorem twice_top_le_index {P : Set Space} (hP : FirstBody P)
    (hsub : P ⊆ capBody (⟨80,24,12⟩ : K1_13.Shape) 0) :
    2 * topSupport P ≤ indexSupport P := by
  have hp : IsCompact P := by
    obtain ⟨v,hv,rfl⟩ := hP.polytope
    exact hv.isCompact_convexHull ℝ
  obtain ⟨x,hx,heq,_⟩ := support_attains hp hP.zero_mem (2 : Fin 6)
  obtain ⟨_,_,_,hmax⟩ := support_attains hp hP.zero_mem (1 : Fin 6)
  have hj := hmax x hx
  have hT : topSupport P = faceSupport P 2 := by simp [topSupport,K1_13_5_4_2_5_2_2.support,form_fun]
  have hJ : indexSupport P = faceSupport P 1 := by simp [indexSupport,K1_13_5_4_2_5_2_2.support,form_fun]
  rw [hT,hJ,← heq]
  simp [form_apply] at hj ⊢
  linarith [(hsub hx).1 1]

def prismVolume (b j c h : ℝ) : ℝ :=
  let u := j - c
  let v := b - j / 2
  c*u*v*h + (c*u/2 - c*v - 2*u*v)*h^2/2 +
    (2*v - c/2 - u)*h^3/3 + h^4/4

theorem real_volume_body {b j c h : ℝ} (hp : Chamber b j c h) :
    (volume (body b j c h)).toReal = prismVolume b j c h := by
  have heq (z : ℝ) : density b j c z =
      c*(j-c)*(b-j/2) + (c*(j-c)/2 - c*(b-j/2) - 2*(j-c)*(b-j/2))*z +
        (2*(b-j/2) - c/2 - (j-c))*z^2 + 1*z^3 := by
    unfold density
    ring
  rw [volume_body hp, ENNReal.toReal_ofReal]
  · simp only [heq]
    rw [K1_13_7_5_3_4.integral_cubic]
    simp [prismVolume]
  · apply intervalIntegral.integral_nonneg hp.1
    intro z hz
    obtain ⟨hc,hj,hb⟩ := chamber_at hp hz
    exact mul_nonneg (mul_nonneg hc (by linarith)) (by linarith)

/-- The linear term in a simultaneous displacement of the first three facets. -/
def firstVariation (b j c h B J C : ℝ) : ℝ :=
  let u := j - c
  let v := b - j / 2
  let U := J - C
  let V := B - J / 2
  (C*u*v + c*U*v + c*u*V)*h +
    ((C*u + c*U)/2 - (C*v + c*V) - 2*(U*v + u*V))*h^2/2 +
    (2*V - C/2 - U)*h^3/3

theorem deriv_volume (b j c h B J C : ℝ) :
    HasDerivAt (fun t : ℝ => prismVolume (b+t*B) (j+t*J) (c+t*C) h)
      (firstVariation b j c h B J C) 0 := by
  let u := j-c
  let v := b-j/2
  let U := J-C
  let V := B-J/2
  have line (a m : ℝ) : HasDerivAt (fun t : ℝ => a+t*m) m 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const m).const_add a
  have h1 := (((line c C).mul (line u U)).mul (line v V)).mul_const h
  have h2 := (((((line c C).mul (line u U)).div_const 2).sub
    ((line c C).mul (line v V))).sub (((line u U).mul (line v V)).const_mul 2)).mul_const (h^2/2)
  have h3 := ((((line v V).const_mul 2).sub ((line c C).div_const 2)).sub (line u U)).mul_const (h^3/3)
  convert (((h1.add h2).add h3).add_const (h^4/4)) using 1
  · funext t
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, prismVolume, u, v, U, V]
    ring
  · simp only [Pi.mul_apply,Pi.sub_apply,Pi.add_apply,zero_mul,add_zero,firstVariation,u,v,U,V]
    ring

theorem shifted_limit (P : Set Space) {b j c h : ℝ}
    (hsupport : 2 * topSupport P ≤ indexSupport P)
    (hc : 2*h < c) (hj : 2*c ≤ j) (hb : j < b) (hh : 0 ≤ h) :
    Tendsto (fun t : ℝ => ((volume (shifted P b j c h t)).toReal -
      (volume (body b j c h)).toReal) / t) (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝 (firstVariation b j c h (totalSupport P) (indexSupport P) (topSupport P))) := by
  let B := totalSupport P
  let J := indexSupport P
  let C := topSupport P
  have h₁ : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ), 2*h < c+t*C :=
    ((show ContinuousAt (fun _ : ℝ => 2*h) 0 from continuousAt_const).eventually_lt
      (show ContinuousAt (fun t : ℝ => c+t*C) 0 by fun_prop) (by simpa using hc)).filter_mono
      nhdsWithin_le_nhds
  have h₂ : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ), 2*(c+t*C) ≤ j+t*J := by
    filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with t ht
    have h := mul_le_mul_of_nonneg_left (show 2*C ≤ J from hsupport) (show 0 < t from ht).le
    linarith
  have h₃ : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ), j+t*J < b+t*B :=
    ((show ContinuousAt (fun t : ℝ => j+t*J) 0 by fun_prop).eventually_lt
      (show ContinuousAt (fun t : ℝ => b+t*B) 0 by fun_prop) (by simpa using hb)).filter_mono
      nhdsWithin_le_nhds
  apply (deriv_volume b j c h B J C).tendsto_slope_zero_right.congr'
  filter_upwards [h₁,h₂,h₃] with t hct hjt hbt
  change t⁻¹ • (prismVolume (b+(0+t)*B) (j+(0+t)*J) (c+(0+t)*C) h -
    prismVolume (b+0*B) (j+0*J) (c+0*C) h) =
    ((volume (body (b+t*B) (j+t*J) (c+t*C) h)).toReal - (volume (body b j c h)).toReal) / t
  rw [real_volume_body ⟨hh,hct.le,hjt,hbt.le⟩, real_volume_body ⟨hh,hc.le,hj,hb.le⟩]
  simp only [zero_add,zero_mul,add_zero,smul_eq_mul,div_eq_mul_inv]
  exact mul_comm _ _

theorem volume_variation (P : Set Space) (hP : FirstBody P)
    (hsub : P ⊆ capBody (⟨80,24,12⟩ : K1_13.Shape) 0) {b j c h : ℝ}
    (hc : 2*h < c) (hj : 2*c ≤ j) (hb : j < b) (hh : 0 ≤ h) :
    Tendsto (volumeQuotient P (body b j c h)) (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝 (firstVariation b j c h (totalSupport P) (indexSupport P) (topSupport P))) := by
  obtain ⟨K, hK⟩ := shifted_error hP hsub hc (by linarith) hh
  let f := fun t : ℝ => ((volume (shifted P b j c h t)).toReal -
    (volume (body b j c h)).toReal) / t
  have hupper := shifted_limit P (twice_top_le_index hP hsub) hc hj hb hh
  have hzero : Tendsto (fun t : ℝ => K*t) (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hid.const_mul K
  have hlower : Tendsto (fun t => f t - K*t) (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝 (firstVariation b j c h (totalSupport P) (indexSupport P) (topSupport P))) := by
    simpa using hupper.sub hzero
  apply hlower.squeeze' hupper
  · filter_upwards [hK,eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with t ht htpos
    have hpos : 0 < t := htpos
    have he := (div_le_iff₀ hpos).mpr (show _ ≤ K*t*t by
      simpa only [pow_two,mul_assoc] using ht.2)
    have hd : f t - volumeQuotient P (body b j c h) t =
        ((volume (shifted P b j c h t)).toReal - (volume (t • P + body b j c h)).toReal) / t := by
      unfold f volumeQuotient
      rw [← sub_div]
      congr 1
      ring
    linarith
  · filter_upwards [hK,eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with t ht htpos
    have hpos : 0 < t := htpos
    exact div_le_div_of_nonneg_right (by linarith [ht.1]) hpos.le

/-- Twelve times each facet coefficient, with no division in the integer receipt. -/
def scaledCoefficients (b j c h : ℕ) : ℤ × ℤ × ℤ :=
  let u := (j : ℤ) - c
  let v := 2 * (b : ℤ) - j
  (12*c*u*h - (6*c+12*u)*h^2 + 8*h^3,
   6*c*(v-u)*h + 6*(c-v+u)*h^2 - 8*h^3,
   6*(u-c)*v*h + 3*(u-c+v)*h^2 + 2*h^3)

theorem variation_scaled (b j c h : ℕ) (B J C : ℝ) :
    12 * firstVariation b j c h B J C =
      (scaledCoefficients b j c h).1 * B + (scaledCoefficients b j c h).2.1 * J +
        (scaledCoefficients b j c h).2.2 * C := by
  unfold firstVariation scaledCoefficients
  push_cast
  ring

end
end CurveListCoupledCap
