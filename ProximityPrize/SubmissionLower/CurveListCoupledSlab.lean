import ProximityPrize.SubmissionLower.CurveListCoupledCap
import ProximityPrize.SubmissionLower.Fast070
import ProximityPrize.SubmissionLower.CurveListCoupledShapes -- serialize candidate build

set_option autoImplicit false

namespace CurveListCoupledCap
noncomputable section
open K1_13_5_4_2 (ExponentSpace)
open K1_13_5_4_2_5 (FirstBody)
open MeasureTheory Set
open scoped Pointwise ENNReal
open private form form_apply Pair nonparallel remaining slabMatrix
  slabMatrix_invertible slabMap_apply from ProximityPrize.SubmissionLower.Fast070

abbrev charge : Fin 6 → ℝ := ![1,3,2,0,0,0]

def steep (i : Fin 6) : Space →ₗ[ℝ] ℝ := form i + charge i • LinearMap.proj 3

theorem steep_apply (i : Fin 6) (x : Space) : steep i x = form i x + charge i * x 3 := rfl

def caps (b j c : ℝ) : Fin 6 → ℝ := ![b,j,c,0,0,0]

theorem mem_body {b j c h : ℝ} {x : Space} :
    x ∈ body b j c h ↔ x 3 ∈ Icc 0 h ∧ ∀ i, steep i x ≤ caps b j c i := by
  simp [body, steep_apply, form_apply, charge, caps, Fin.forall_fin_succ]
  tauto

def shiftVector (p : Pair) : Space := ![charge p.1,charge p.2,0,0]

def steepMatrix (p : Pair) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i k => slabMatrix p i k + if k = (3 : Fin 4) then shiftVector p i else 0

theorem steepMatrix_det (p : Pair) : (steepMatrix p).det = (slabMatrix p).det := by
  have hsub : (steepMatrix p).submatrix Fin.castSucc Fin.castSucc =
      (slabMatrix p).submatrix Fin.castSucc Fin.castSucc := by
    ext i k
    have hk : Fin.castSucc k ≠ (3 : Fin 4) := Fin.castSucc_ne_last k
    simp [Matrix.submatrix_apply,steepMatrix,hk]
  rw [K1_13_5_4_2_5_2_2.slabMatrix_det p, Matrix.det_succ_row _ (Fin.last 3), Fin.sum_univ_four]
  have h0 : steepMatrix p (Fin.last 3) 0 = 0 := by change (0 : ℝ) + 0 = 0; ring
  have h1 : steepMatrix p (Fin.last 3) 1 = 0 := by change (0 : ℝ) + 0 = 0; ring
  have h2 : steepMatrix p (Fin.last 3) 2 = 0 := by change (0 : ℝ) + 0 = 0; ring
  have h3 : steepMatrix p (Fin.last 3) (Fin.last 3) = 1 := by change (1 : ℝ) + 0 = 1; ring
  simp only [h0,h1,h2,mul_zero,zero_mul,zero_add]
  change (-1 : ℝ)^6 * steepMatrix p (Fin.last 3) (Fin.last 3) *
      ((steepMatrix p).submatrix (Fin.last 3).succAbove (Fin.last 3).succAbove).det = _
  rw [h3,Fin.succAbove_last,hsub]
  norm_num

theorem steepMap_apply (p : Pair) (x : Space) :
    Matrix.toLin' (steepMatrix p) x = ![steep p.1 x, steep p.2 x, x (remaining p), x 3] := by
  have h : Matrix.toLin' (steepMatrix p) x = Matrix.toLin' (slabMatrix p) x + x 3 • shiftVector p := by
    ext i
    simp [Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_four,steepMatrix,Pi.smul_apply,smul_eq_mul]
    ring
  rw [h,slabMap_apply]
  ext i
  fin_cases i <;> simp [steep_apply,shiftVector,Pi.smul_apply,smul_eq_mul,mul_comm]

/-- Slab intersection bound; last-jet charges leave the determinant unchanged. -/
def steepSlab (a : Fin 6 → ℝ) (R e : ℝ) (p : Pair) : Set Space :=
  if nonparallel p then Matrix.toLin' (steepMatrix p) ⁻¹'
    Icc (![a p.1-e,a p.2-e,0,0] : Space) ![a p.1+e,a p.2+e,R,R]
  else ∅

theorem mem_steepSlab {a : Fin 6 → ℝ} {R e : ℝ} {p : Pair} {x : Space} (hp : nonparallel p) :
    x ∈ steepSlab a R e p ↔
      a p.1-e ≤ steep p.1 x ∧ steep p.1 x ≤ a p.1+e ∧
      a p.2-e ≤ steep p.2 x ∧ steep p.2 x ≤ a p.2+e ∧
      x (remaining p) ∈ Icc 0 R ∧ x 3 ∈ Icc 0 R := by
  simp only [steepSlab,hp,if_true,mem_preimage,steepMap_apply,mem_Icc,Pi.le_def,Fin.forall_fin_succ]
  simp [and_assoc,and_left_comm,and_comm]

theorem volume_steepSlab (a : Fin 6 → ℝ) {R e : ℝ} (hR : 0 ≤ R) (he : 0 ≤ e) (p : Pair) :
    volume (steepSlab a R e p) ≤ ENNReal.ofReal (|(slabMatrix p).det⁻¹| * 4 * R^2 * e^2) := by
  unfold steepSlab
  split_ifs with hp
  · rw [Measure.addHaar_preimage_linearMap volume (by
      rw [LinearMap.det_toLin',steepMatrix_det]; exact slabMatrix_invertible p hp),
      LinearMap.det_toLin',steepMatrix_det,Real.volume_Icc_pi,Fin.prod_univ_four]
    have hwidth (w : ℝ) : w+e-(w-e) = 2*e := by ring
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.head_cons,Matrix.tail_cons,hwidth,sub_zero]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*e), ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*e*(2*e)),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*e*(2*e)*R), ← ENNReal.ofReal_mul (abs_nonneg _)]
    apply le_of_eq
    congr 1
    ring
  · simp

open K1_13_5_4_2 (capBody)
open K1_13_5_4_2_5_2 (totalSupport indexSupport topSupport)
open Filter
open scoped Topology BigOperators
open private K1_13_5_4_2_5_2_2.support support_attains form_fun
  from ProximityPrize.SubmissionLower.Fast070
local notation "faceSupport" => K1_13_5_4_2_5_2_2.support

abbrev limitBox := (⟨80,24,12⟩ : K1_13.Shape)

def shifted (P : Set Space) (b j c h t : ℝ) : Set Space :=
  body (b+t*totalSupport P) (j+t*indexSupport P) (c+t*topSupport P) h

private theorem mem_shifted {P : Set Space} (h0 : 0 ∈ P) (hsub : P ⊆ capBody limitBox 0)
    {b j c h t : ℝ} {x : Space} : x ∈ shifted P b j c h t ↔
    x 3 ∈ Icc 0 h ∧ ∀ i, steep i x ≤ caps b j c i + t * faceSupport P i := by
  rw [shifted,mem_body]
  have hlow (i : Fin 6) (hi : 3 ≤ i.val) : faceSupport P i = 0 := by
    have hz : (0 : ℝ) ∈ form i '' P := ⟨0,h0,map_zero _⟩
    have hub : 0 ∈ upperBounds (form i '' P) := by
      rintro _ ⟨p,hp,rfl⟩
      have h := (hsub hp).1
      fin_cases i <;> norm_num at hi
      all_goals simpa [form_apply] using h _
    exact le_antisymm (csSup_le ⟨0,hz⟩ hub) (le_csSup ⟨0,hub⟩ hz)
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  fin_cases i
  · simp [caps,K1_13_5_4_2_5_2_2.support,totalSupport,form_fun]
  · simp [caps,K1_13_5_4_2_5_2_2.support,indexSupport,form_fun]
  · simp [caps,K1_13_5_4_2_5_2_2.support,topSupport,form_fun]
  all_goals rw [hlow _ (by decide)]; simp [caps]

private theorem form_bounded {P : Set Space} (hsub : P ⊆ capBody limitBox 0)
    {x : Space} (hx : x ∈ P) (i : Fin 6) : |form i x| ≤ 250 := by
  have hp := hsub hx
  have h0 := hp.1 0
  have h1 := hp.1 1
  have h2 := hp.1 2
  have hb := hp.2.1
  change x 0+x 1+x 2 ≤ (limitBox.b : ℝ) at hb
  norm_num [limitBox] at hb
  rw [abs_le,form_apply]
  fin_cases i <;> simp <;> constructor <;> linarith

/-- Replacing an infinitesimal Minkowski sum by shifted facet intercepts
only overcounts the intersections of two boundary slabs. -/
theorem shifted_error {P : Set Space} (hP : FirstBody P) (hsub : P ⊆ capBody limitBox 0)
    {b j c h : ℝ} (hc : 2*h < c) (hb : 0 ≤ b) (hh : 0 ≤ h) :
    ∃ K : ℝ, ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ),
      0 ≤ (volume (shifted P b j c h t)).toReal - (volume (t • P + body b j c h)).toReal ∧
      (volume (shifted P b j c h t)).toReal - (volume (t • P + body b j c h)).toReal ≤ K*t^2 := by
  have hp : IsCompact P := by
    obtain ⟨v,hv,rfl⟩ := hP.polytope
    exact hv.isCompact_convexHull ℝ
  choose pt hpt heq hmax using support_attains hp hP.zero_mem
  have hsup (i : Fin 6) : faceSupport P i ≤ 250 :=
    (heq i).symm.trans_le ((le_abs_self _).trans (form_bounded hsub (hpt i) i))
  let R : ℝ := b+h+250
  let coeff (p : Pair) : ℝ := |(slabMatrix p).det⁻¹| * 4 * R^2 * 250^2
  have hR : 0 ≤ R := by positivity
  refine ⟨∑ p, coeff p,?_⟩
  have hsmall : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ), t < (c-2*h)/250 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (div_pos (sub_pos.mpr hc) (by norm_num : (0 : ℝ) < 250)))
  have hone : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] (0 : ℝ), t < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0),hone,hsmall]
    with t ht ht1 hts
  have ht' : 0 < t := ht
  let e := t*250
  have he : 0 ≤ e := by positivity
  let S := shifted P b j c h t
  let C := t • P + body b j c h
  let E (p : Pair) := steepSlab (caps b j c) R e p
  have hform (i : Fin 6) (y : Space) (hy : y ∈ P) : steep i y = form i y := by
    rw [steep_apply,hP.zero_height y hy,mul_zero,add_zero]
  have hCS : C ⊆ S := by
    rintro x hx
    obtain ⟨w,hw,z,hz,rfl⟩ := mem_add.mp hx
    obtain ⟨y,hy,rfl⟩ := mem_smul_set.mp hw
    have hz' := mem_body.mp hz
    refine (mem_shifted hP.zero_mem hsub).mpr ⟨?_,fun i => ?_⟩
    · simpa [Pi.add_apply,Pi.smul_apply,hP.zero_height y hy] using hz'.1
    · rw [map_add,map_smul,smul_eq_mul,hform i y hy]
      exact (add_le_add (mul_le_mul_of_nonneg_left (hmax i y hy) ht'.le) (hz'.2 i)).trans_eq (add_comm _ _)
  have hcube : S ⊆ Icc (0 : Space) (fun _ => R) := by
    intro x hx
    obtain ⟨hn,hx',_,_,hx3⟩ := (show x ∈ body _ _ _ _ from hx)
    have heq' : totalSupport P = faceSupport P 0 := by simp [totalSupport,K1_13_5_4_2_5_2_2.support,form_fun]
    rw [heq'] at hx'
    have hbx := hx'.trans (add_le_add_right (mul_le_mul_of_nonneg_left (hsup 0) ht'.le) b)
    have h₀ := hn 0
    have h₁ := hn 1
    have h₂ := hn 2
    have h₃ := hn 3
    refine ⟨hn,fun i => ?_⟩
    fin_cases i <;> dsimp [R] <;> linarith
  have hcover : S ⊆ C ∪ ⋃ p,E p := by
    intro x hx
    by_cases hxc : x ∈ C
    · exact Or.inl hxc
    have hx' := (mem_shifted hP.zero_mem hsub).mp hx
    have hbase : x ∉ body b j c h := fun hm =>
      hxc (mem_add.mpr ⟨0,⟨0,hP.zero_mem,smul_zero _⟩,x,hm,zero_add _⟩)
    have hviol : ¬ ∀ i, steep i x ≤ caps b j c i := fun hi => hbase (mem_body.mpr ⟨hx'.1,hi⟩)
    push Not at hviol
    obtain ⟨i,hi⟩ := hviol
    let y := x-t • pt i
    have hyh : y 3 ∈ Icc 0 h := by
      simpa [y,Pi.sub_apply,Pi.smul_apply,hP.zero_height _ (hpt i)] using hx'.1
    have hy : y ∉ body b j c h := fun hm =>
      hxc (mem_add.mpr ⟨t • pt i,⟨pt i,hpt i,rfl⟩,y,hm,by dsimp [y]; abel⟩)
    have hother : ¬ ∀ k, steep k y ≤ caps b j c k := fun hk => hy (mem_body.mpr ⟨hyh,hk⟩)
    push Not at hother
    obtain ⟨k,hk⟩ := hother
    have hshift (l : Fin 6) : steep l y = steep l x-t*form l (pt i) := by
      dsimp only [y]
      rw [map_sub,map_smul,smul_eq_mul,hform l (pt i) (hpt i)]
    have hki : i ≠ k := by
      rintro rfl
      rw [hshift,heq] at hk
      linarith [hx'.2 i]
    have hlo : caps b j c k-e ≤ steep k x := by
      have H := (abs_le.mp (form_bounded hsub (hpt i) k)).1
      rw [hshift] at hk
      dsimp [e]
      linarith [mul_le_mul_of_nonneg_left H ht'.le]
    have hhi (l : Fin 6) : steep l x ≤ caps b j c l+e :=
      (hx'.2 l).trans (add_le_add_right (mul_le_mul_of_nonneg_left (hsup l) ht'.le) _)
    have hpar : nonparallel (i,k) := by
      refine ⟨?_,hki,?_⟩
      · have hn : ∀ l : Fin 4, 0 ≤ x l := (hcube hx).1
        fin_cases i <;> norm_num [caps,steep_apply,form_apply,charge] at hi ⊢
        · exact (not_lt_of_ge (hn 0)) hi
        · exact (not_lt_of_ge (hn 1)) hi
        · exact (not_lt_of_ge (hn 2)) hi
      · by_contra hn
        push Not at hn
        obtain ⟨rfl,rfl⟩ := hn
        simp [caps,steep_apply,form_apply,charge] at hi hlo
        linarith [hx'.1.2,show e<c-2*h from (lt_div_iff₀ (by norm_num : (0 : ℝ) < 250)).mp hts]
    refine Or.inr (mem_iUnion.mpr ⟨(i,k),(mem_steepSlab hpar).mpr ?_⟩)
    exact ⟨(sub_le_self _ he).trans hi.le,hhi i,hlo,hhi k,
      ⟨(hcube hx).1 _,(hcube hx).2 _⟩,⟨(hcube hx).1 _,(hcube hx).2 _⟩⟩
  have hevol : volume (⋃ p,E p) ≤ ENNReal.ofReal ((∑ p, coeff p)*t^2) := by
    calc
      _ ≤ ∑ p, volume (E p) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ p, ENNReal.ofReal (coeff p*t^2) := by
        apply Finset.sum_le_sum
        intro p _
        have H := volume_steepSlab (caps b j c) hR he p
        convert H using 2
        dsimp [coeff,e]
        ring
      _ = _ := by rw [Finset.sum_mul,ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
  have hS : volume S ≠ ∞ := measure_ne_top_of_subset hcube isCompact_Icc.measure_ne_top
  have hC : volume C ≠ ∞ := measure_ne_top_of_subset hCS hS
  have hevol' : volume S ≤ volume C+ENNReal.ofReal ((∑ p, coeff p)*t^2) :=
    (measure_mono hcover).trans ((measure_union_le _ _).trans (add_le_add_right hevol _))
  constructor
  · exact sub_nonneg.mpr (ENNReal.toReal_mono hS (measure_mono hCS))
  · have H := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hC,ENNReal.ofReal_ne_top⟩) hevol'
    rw [ENNReal.toReal_add hC ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal (by positivity)] at H
    exact sub_le_iff_le_add'.mpr H

end
end CurveListCoupledCap
