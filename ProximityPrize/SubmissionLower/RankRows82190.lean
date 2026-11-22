import ProximityPrize.SubmissionLower.AnchorPivotFactors82180
import ProximityPrize.SubmissionLower.AnchorTopFactor
import ProximityPrize.SubmissionLower.AnchorPivotRank82180

-- merged module AnchorNinth82190
section Merged_AnchorNinth82190
set_option Elab.async false
set_option maxHeartbeats 1500000
namespace AnchorPivot82190
open AnchorPivot82180
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder valueForm)
open MvPolynomial
open private poly_band poly_order encoded_degree from ProximityPrize.SubmissionLower.AnchorPivot82180

def src8 : List Term := [(1,⟨2,3,0,0⟩), (1,⟨0,5,0,0⟩), (-2,⟨1,4,0,0⟩), (-4,⟨2,1,1,1⟩), (-1,⟨0,4,1,0⟩), (1,⟨1,2,2,0⟩), (-2,⟨2,2,0,1⟩), (2,⟨1,3,0,1⟩), (1,⟨2,2,1,0⟩), (2,⟨3,0,1,1⟩), (1,⟨3,0,0,2⟩), (1,⟨3,0,2,0⟩), (1,⟨2,0,3,0⟩), (-1,⟨2,1,2,0⟩)]
private def dst8 : List Term := [(1,⟨2,3,0,0⟩), (-4,⟨0,1,1,3⟩), (-2,⟨1,1,1,2⟩), (1,⟨0,2,0,3⟩), (-1,⟨1,2,0,2⟩), (-2,⟨2,2,0,1⟩), (1,⟨2,2,1,0⟩), (1,⟨0,1,2,2⟩), (4,⟨1,2,1,1⟩), (-1,⟨0,0,4,1⟩), (3,⟨0,0,3,2⟩), (2,⟨1,0,3,1⟩), (-1,⟨0,0,1,4⟩), (-6,⟨1,0,2,2⟩), (-3,⟨2,0,2,1⟩), (2,⟨3,0,1,1⟩), (3,⟨0,1,0,4⟩), (6,⟨1,1,0,3⟩), (1,⟨0,0,0,5⟩), (3,⟨2,1,0,2⟩), (3,⟨1,0,0,4⟩), (3,⟨2,0,0,3⟩), (1,⟨3,0,0,2⟩), (-2,⟨1,1,3,0⟩), (-2,⟨0,0,2,3⟩), (2,⟨2,1,2,0⟩), (-2,⟨2,0,3,0⟩), (1,⟨3,0,2,0⟩), (2,⟨2,1,1,1⟩), (1,⟨1,0,4,0⟩), (3,⟨2,0,1,2⟩)]
def data8 : Data := ⟨5,3,6,2,6,120000⟩
theorem spec8 : Sound data8 (poly src8) := by
  refine ⟨poly_band _ (by decide +kernel), ?_, ?_⟩
  · have h : backShift (poly src8) = poly dst8 := by
      simp [src8,dst8,poly,mon,backShift,valueForm,map_ofNat, zsmul_eq_mul]
      ring
    rw [h]
    exact poly_order _ (by decide +kernel)
  · exact encoded_degree (b := 110002) ([(1,⟨0,5,0,0⟩), (-2,⟨1,4,0,0⟩), (-4,⟨2,1,1,1⟩), (-1,⟨0,4,1,0⟩), (1,⟨1,2,2,0⟩), (-2,⟨2,2,0,1⟩), (2,⟨1,3,0,1⟩), (1,⟨2,2,1,0⟩), (2,⟨3,0,1,1⟩), (1,⟨3,0,0,2⟩), (1,⟨3,0,2,0⟩), (1,⟨2,0,3,0⟩), (-1,⟨2,1,2,0⟩)]) (by decide) (by decide)

def allData : Fin 9 → Data := ![data0, data1, data2, data3, data4, data5, data6, data7, data8]
noncomputable def allPoly : Fin 9 → Form := ![poly src0, poly src1, poly src2, poly src3, poly src4, poly src5, poly src6, poly src7, poly src8]
theorem all_ok (i : Fin 9) : Sound (allData i) (allPoly i) := by
  fin_cases i
  · exact spec0
  · exact spec1
  · exact spec2
  · exact spec3
  · exact spec4
  · exact spec5
  · exact spec6
  · exact spec7
  · exact spec8

#print axioms all_ok
end AnchorPivot82190
end Merged_AnchorNinth82190

-- merged module AnchorBlock82190
section Merged_AnchorBlock82190
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
end Merged_AnchorBlock82190

set_option Elab.async false
set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

namespace RankRows82190
open AnchorPivot82180 (Data Sound E encode mon sound_monomial monoData sound_one)
open AnchorPivot82190 (allData allPoly all_ok)
open K1_13 (Geom)
open K1_13_1_1 (Form bandSpace backShift targetOrder orderCutoff bandCount bandSpace_finite finrank_bandSpace)
open AnchorBlock82190 (blockAt)
open MvPolynomial
open scoped BigOperators

abbrev Factor := Fin 9 × ℕ
def measure : List Factor → Data
  | [] => Data.unit
  | (i,k)::xs => ((allData i).times k).plus (measure xs)
noncomputable def product : List Factor → Form
  | [] => 1
  | (i,k)::xs => allPoly i^k * product xs
theorem product_ok (xs : List Factor) : Sound (measure xs) (product xs) := by
  induction xs with
  | nil => exact sound_one
  | cons t ts ih => exact ((all_ok t.1).pow t.2).mul ih

structure Row where
  tag : ℕ
  index : ℕ
  ord : ℕ
  e : E
  factors : List Factor
  deriving DecidableEq
def Row.bounds (r : Row) := (monoData r.e).plus (measure r.factors)
noncomputable def Row.form (r : Row) := mon r.e * product r.factors
theorem Row.sound (r : Row) : Sound r.bounds r.form :=
  (sound_monomial r.e).mul (product_ok r.factors)
def Row.good (r : Row) (d : ℕ) : Bool :=
  let x := r.bounds
  decide (x.deg = d ∧ r.index ≤ x.lo ∧ x.hi ≤ 48 ∧ x.top ≤ 12 ∧ r.ord ≤ x.ord ∧ x.tag = r.tag)

def accept (s : ℕ) (g : ℤ) (r : Row) : Bool :=
  decide (-g ≤ (r.index : ℤ) ∧ (orderCutoff s g).toNat ≤ r.ord)

private theorem band_mono {d a b : ℕ} {l h l' h' : ℤ} (hl : l' ≤ l) (hh : h ≤ h') (ht : a ≤ b) :
    bandSpace d l h a ≤ bandSpace d l' h' b := by
  intro p hp
  apply (MvPolynomial.mem_restrictSupport_iff Geom).mpr
  intro e he
  obtain ⟨hd,hlo,hhi,hf⟩ := (MvPolynomial.mem_restrictSupport_iff Geom).mp hp he
  exact ⟨hd,hl.trans hlo,hhi.trans hh,hf.trans ht⟩

private theorem row_kernel (d s : ℕ) (g : ℤ) (r : Row) (hv : r.good d = true)
    (ha : accept s g r = true) :
    ∃ w : LinearMap.ker (blockAt d s g), ((w.val : Form) = r.form) ∧
      (encode (w.val : Form)).degree = (r.tag : ℕ) := by
  obtain ⟨hd,hl,hh,ht,ho,hk⟩ := of_decide_eq_true hv
  obtain ⟨hl',ho'⟩ := of_decide_eq_true ha
  have hb := r.sound.band
  rw [hd] at hb
  let w : bandSpace d (-g) 48 12 := ⟨r.form,
    band_mono (hl'.trans (Int.ofNat_le.mpr hl)) (by exact_mod_cast hh) ht hb⟩
  have hw : w ∈ LinearMap.ker (blockAt d s g) := by
    apply (weightedTruncation_eq_zero_iff _ _ _).mpr
    exact restrictWeightedOrder_anti _ (ho'.trans ho) r.sound.contact
  exact ⟨⟨w,hw⟩,rfl,r.sound.degree.trans (congrArg (fun n : ℕ => (n : WithBot ℕ)) hk)⟩

open private independent from ProximityPrize.SubmissionLower.AnchorPivotRank82180

theorem count_bound (rows : List Row) (d s : ℕ) (g : ℤ)
    (good : ∀ r ∈ rows, r.good d = true)
    (sorted : rows.Pairwise fun a b => a.tag < b.tag) :
    Module.finrank Geom (LinearMap.range (blockAt d s g)) + (rows.filter (accept s g)).length ≤
      bandCount d (-g) 48 12 := by
  classical
  let use := rows.filter (accept s g)
  have memb (i : Fin use.length) : use.get i ∈ rows ∧ accept s g (use.get i) = true :=
    List.mem_filter.mp (List.get_mem use i)
  have hsort : use.Pairwise (fun a b => a.tag < b.tag) := sorted.sublist (List.filter_sublist ..)
  have hmono : StrictMono (fun i : Fin use.length => (use.get i).tag) :=
    fun _ _ h => hsort.rel_get_of_lt h
  have h (i : Fin use.length) := row_kernel d s g (use.get i) (good _ (memb i).1) (memb i).2
  let w (i : Fin use.length) := Classical.choose (h i)
  let embed : LinearMap.ker (blockAt d s g) →ₗ[Geom] Polynomial Geom :=
    encode.toLinearMap.comp ((bandSpace d (-g) 48 12).subtype.comp (LinearMap.ker (blockAt d s g)).subtype)
  have hw := independent embed w _ hmono.injective (fun i => (Classical.choose_spec (h i)).2)
  letI : Module.Finite Geom (bandSpace d (-g) 48 12) := bandSpace_finite _ _ _ _
  have hc := hw.fintype_card_le_finrank
  have hd := (blockAt d s g).finrank_range_add_finrank_ker
  rw [finrank_bandSpace] at hd
  simpa only [Fintype.card_fin] using
    ((Nat.add_le_add_left hc (Module.finrank Geom (LinearMap.range (blockAt d s g)))).trans_eq hd)

#print axioms count_bound
end RankRows82190