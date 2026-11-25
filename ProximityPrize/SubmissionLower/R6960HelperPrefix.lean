import ProximityPrize.SubmissionLower.UpperBranch1
import ProximityPrize.SubmissionLower.KoalaRectPoleBalance
import ProximityPrize.SubmissionLower.KoalaRectCutoff
import ProximityPrize.SubmissionLower.KoalaRectRank
import ProximityPrize.SubmissionLower.HighCore82258Source
import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic
import ProximityPrize.SubmissionLower.HighCore82258PrefixProcess

set_option Elab.async false

-- merged module KoalaRectPoleLocal
section Merged_KoalaRectPoleLocal

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

namespace KoalaRectPole
noncomputable section

open Polynomial
open K1_14 (Shape)
open K1_14_1 (jetConstant otherBlock)
open K1_14_1_7 K1_14_1_7_2
open P1_7_1 (columnCount groupedPoleMoment poleRows)
open P1_7_1_1 (Column Offset Pivot bounded_pole_minors firstJet input
  outputLength pascal_spans poleMatrix polynomialTest polynomialTests_to_poleMatrix rowIndex rowIndex_sum)
open scoped BigOperators Matrix Polynomial
open P1_7_1_1 (polynomialTest_apply side_degrees)

def RectSupport {F : Type} [CommSemiring F] (U : Fin 2 → ℕ) (P : TrueSource F) : Prop :=
  ∀ j i a e, sourceCoeff P j i a e ≠ 0 → ∀ z, e z ≤ U z

def rectWindow {F : Type} [Field F] (U : Fin 2 → ℕ) (d : ℕ) (side : Fin 2) (g : Seed F) : Prop :=
  ∀ z, g.degreeOf z ≤ U z + if z = side then d else 0

theorem rect_map {R S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    {U : Fin 2 → ℕ} {P : TrueSource R} (hP : RectSupport U P) :
    RectSupport U (mapSource f P) := by
  intro j i a e hne
  apply hP j i a e
  intro hz
  apply hne
  simpa [sourceCoeff, mapSource, Polynomial.coeff_map, MvPolynomial.coeff_map] using
    (congrArg f hz).trans (map_zero f)

theorem rect_combination {F ι : Type} [Field F] [Fintype ι]
    {U : Fin 2 → ℕ} {P : ι → TrueSource F} (hP : ∀ k, RectSupport U (P k)) (v : ι → F) :
    RectSupport U (Fintype.linearCombination F P v) := by
  intro j i a e hne z
  by_contra hbad
  apply hne
  change readCoeff j i a e (Fintype.linearCombination F P v) = 0
  rw [Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  have he : sourceCoeff (P k) j i a e = 0 := by
    by_contra hz
    exact hbad (hP k j i a e hz z)
  rw [map_smul]
  change v k • sourceCoeff (P k) j i a e = 0
  rw [he, smul_zero]

private theorem taylor_coordinate {F : Type} [Field F] (α : F) (P : TrueSource F)
    {U : Fin 2 → ℕ} (hP : RectSupport U P) (j i t : ℕ) (z : Fin 2) :
    (inputTaylorCoeff α j i t P).degreeOf z ≤ U z := by
  have hc (a : ℕ) : (((P.coeff j).coeff i).coeff a).degreeOf z ≤ U z := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact hP j i a e (MvPolynomial.mem_support_iff.mp he) z
  rw [inputTaylorCoeff_apply, inputTaylor, taylor_coeff, eval_eq_sum_range]
  refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun k _ => ?_)
  rw [hasseDeriv_coeff]
  have he :
      ((k + t).choose t : Seed F) * ((P.coeff j).coeff i).coeff (k + t) *
          (algebraMap F (Seed F) α) ^ k =
        MvPolynomial.C (((k + t).choose t : F) * α ^ k) *
          ((P.coeff j).coeff i).coeff (k + t) := by
    simp only [MvPolynomial.algebraMap_eq, map_mul, map_pow, map_natCast]
    ring
  rw [he]
  exact (MvPolynomial.degreeOf_mul_le _ _ _).trans
    (by simpa only [MvPolynomial.degreeOf_C, zero_add] using hc (k + t))

theorem polynomialTest_rect {F : Type} [Field F] {s : Shape} {t : Offset s}
    (α : F) (side : Fin 2) (v : Column s t → (Polynomial F)) {U : Fin 2 → ℕ} {d : ℕ}
    (hd : ∀ u, (v u).natDegree ≤ d) {P : TrueSource F} (hP : RectSupport U P) :
    rectWindow U d side (polynomialTest α side v P) := by
  intro z
  rw [polynomialTest_apply]
  refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le fun u _ => ?_)
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  have hg : (input α u P).degreeOf z ≤ U z := taylor_coordinate α P hP _ _ _ _
  have hf := side_degrees side (v u)
  by_cases hz : z = side
  · rw [ite_eq_left hz]
    have hv := (MvPolynomial.degreeOf_le_totalDegree ((v u).toMvPolynomial side) z).trans
      (hf.2.trans (hd u))
    exact (Nat.add_le_add hv hg).trans_eq (Nat.add_comm _ _)
  · have ho : z = otherBlock side := by fin_cases z <;> fin_cases side <;> simp_all [otherBlock]
    have hv : ((v u).toMvPolynomial side).degreeOf z ≤ 0 := ho.symm ▸ hf.1
    simpa only [ite_eq_right hz, zero_add, add_zero] using Nat.add_le_add hv hg

def LocalTests : Prop :=
  ∀ (F : Type) [Field F] [CharP F K1.p] (s : Shape),
    s.B < K1.p → ∀ (U : Fin 2 → ℕ) (H : (Polynomial F)) (lift : (Polynomial (SeedFrac F)))
      (α : F) (side : Fin 2) (a b c : F),
      H.eval α = 0 → H.derivative.eval α ≠ 0 → b ≠ 0 →
      lift.eval (algebraMap F (SeedFrac F) α) = residue side a b c →
      ∃ d : Fin (poleRows s) → ℕ,
        (∑ r, d r) ≤ groupedPoleMoment s.B s.J ∧
        ∃ tests : Fin (poleRows s) → TrueSource F →ₗ[F] Seed F,
          (∀ r P, RectSupport U P → rectWindow U (d r) side (tests r P)) ∧
          ∀ P, Shaped s P → (∀ r, tests r P = 0) →
            (jetConstant ((Polynomial.X (R := SeedFrac F) -
                Polynomial.C (algebraMap F (SeedFrac F) α)) ^ (s.B+s.J)) :
              JetPolys (SeedFrac F)) ∣ forward H lift P

theorem local_of_children (hLocal : P1_7_1_1.c1) (hBasis : P1_7_1_1.c2) : LocalTests := by
  classical
  intro F _ _ s _ U H lift α side a b c hH _ hb hz
  have hRows (t : Offset s) :=
    hBasis F (Pivot s t) (Column s t) _ _ (bounded_pole_minors F s t a b c hb)
  choose Q L d hL hdeg hsum using hRows
  let tests (t : Offset s) (r : Pivot s t) := polynomialTest α side (Q t r)
  let e := rowIndex s
  refine ⟨fun k => d (e k).1 (e k).2, rowIndex_sum s d hsum,
    fun k => tests (e k).1 (e k).2, ?_, ?_⟩
  · intro k P hP
    exact polynomialTest_rect α side _ (hdeg _ _) hP
  · intro P hP hzero
    have ht (t : Offset s) (r : Pivot s t) : tests t r P = 0 := by
      let testAt (k : Σ t : Offset s, Pivot s t) := tests k.1 k.2 P
      have hk : testAt (e (e.symm ⟨t, r⟩)) = 0 := hzero (e.symm ⟨t, r⟩)
      rw [e.apply_symm_apply] at hk
      exact hk
    let z := residue side a b c
    have hslots := hLocal F s α z
      (fun t q => pascal_spans (SeedFrac F) (firstJet s t) (columnCount s.B s.J t.val q.val)
        (outputLength s t q)) P hP
      (fun t => polynomialTests_to_poleMatrix t α side a b c P (Q t) (L t) (hL t) (ht t))
    have hd := K1_14_1_7_2_2.proof F s (localSlots s α z P) hslots
    rw [← K1_14_1_7_2_1.proof F s α z P hP] at hd
    exact transfer_dvd H lift α z (s.B+s.J) P hH hz
      (linear_pole_dvd α z (s.B+s.J) P hd)

theorem local_tests : LocalTests :=
  local_of_children P1_7_1_1_1.proof P1_7_1_1_2.proof

#print axioms local_tests

end
end KoalaRectPole

end Merged_KoalaRectPoleLocal

-- merged module KoalaRectPole
section Merged_KoalaRectPole

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

namespace KoalaRectPole
noncomputable section

open Polynomial
open K1_14 (L Shape)
open K1_14_1 K1_14_1_7 K1_14_1_7_3
open P1 (K I)
open P1_7_1 (groupedPoleMoment poleRows)
open scoped BigOperators Polynomial
open K1_14_1_7 (poleTest_of_local)

def poleDebit (h : ℕ) (s : Shape) (U : Fin 2 → ℕ) : ℕ :=
  2*h * poleRows s * ((U 0 + 1) * (U 1 + 1)) +
    h * (U 0 + U 1 + 2) * groupedPoleMoment s.B s.J

private abbrev Slots (U : Fin 2 → ℕ) (d : ℕ) (side : Fin 2) :=
  ∀ z : Fin 2, Fin (U z + (if z = side then d else 0) + 1)

private def slotExponent {U : Fin 2 → ℕ} {d : ℕ} {side : Fin 2} (k : Slots U d side) : Exponent :=
  Finsupp.equivFunOnFinite.symm (fun z => (k z).val)

private theorem read_rect_window (F : Type) [Field F] (U : Fin 2 → ℕ) (d : ℕ) (side : Fin 2) :
    ∃ read : Seed F →ₗ[F] (Slots U d side → F),
      ∀ g, rectWindow U d side g → read g = 0 → g = 0 := by
  let read : Seed F →ₗ[F] (Slots U d side → F) :=
    LinearMap.pi fun k => MvPolynomial.lcoeff F (slotExponent k)
  refine ⟨read, ?_⟩
  intro g hg hzero
  apply MvPolynomial.ext
  intro e
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hn
  have he (z : Fin 2) : e z ≤ U z + if z = side then d else 0 :=
    (MvPolynomial.le_degreeOf_of_mem_support z (MvPolynomial.mem_support_iff.mpr hn)).trans (hg z)
  let k : Slots U d side := fun z => ⟨e z, Nat.lt_succ_of_le (he z)⟩
  have hz := congrFun hzero k
  change g.coeff (Finsupp.equivFunOnFinite.symm (fun z => e z)) = 0 at hz
  exact hn ((Finsupp.equivFunOnFinite.symm_apply_apply e) ▸ hz)

private theorem slots_card (U : Fin 2 → ℕ) (d : ℕ) (side : Fin 2) :
    Fintype.card (Slots U d side) =
      (U 0 + 1) * (U 1 + 1) + (U (otherBlock side) + 1) * d := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin, Fin.prod_univ_two]
  fin_cases side <;> simp [otherBlock] <;> ring

private abbrev ScalarRows {h : ℕ} (s : Shape) (U : Fin 2 → ℕ)
    (side : Fin (2*h) → Fin 2) (d : Fin (2*h) → Fin (poleRows s) → ℕ) :=
  Σ t : Fin (2*h), Σ r : Fin (poleRows s), Slots U (d t r) (side t)

private theorem scalar_rows_card_le {h : ℕ} {F : Type} [Field F] {H : (Polynomial F)}
    {lift : (Polynomial (SeedFrac F))} (G : SimplePoles h H lift) (hG : Balanced G) (s : Shape)
    (U : Fin 2 → ℕ) (d : Fin (2*h) → Fin (poleRows s) → ℕ)
    (hd : ∀ t, (∑ r, d t r) ≤ groupedPoleMoment s.B s.J) :
    Fintype.card (ScalarRows s U G.side d) ≤ poleDebit h s U := by
  classical
  simp only [ScalarRows, Fintype.card_sigma, slots_card]
  let base := (U 0 + 1) * (U 1 + 1)
  let moment := groupedPoleMoment s.B s.J
  calc
    (∑ t : Fin (2*h), ∑ r : Fin (poleRows s), (base + (U (otherBlock (G.side t)) + 1) * d t r)) ≤
        ∑ t : Fin (2*h), (poleRows s * base + (U (otherBlock (G.side t)) + 1) * moment) := by
      apply Finset.sum_le_sum
      intro t _
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (hd t)) _
    _ = poleDebit h s U := by
      obtain ⟨e, he⟩ := hG
      simp_rw [he]
      rw [e.sum_comp (fun p => poleRows s * base + (U (otherBlock p.1) + 1) * moment),
        Fintype.sum_prod_type, Fin.sum_univ_two]
      simp only [show otherBlock (0 : Fin 2) = 1 by decide,
        show otherBlock (1 : Fin 2) = 0 by decide]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change h * (poleRows s * base + (U 1 + 1) * moment) +
        h * (poleRows s * base + (U 0 + 1) * moment) = poleDebit h s U
      dsimp [base, moment, poleDebit]
      ring

private theorem simple_rank_le {F ι : Type} [Field F] [CharP F K1.p] [Fintype ι] {h : ℕ}
    {H : (Polynomial F)} {lift : (Polynomial (SeedFrac F))} (G : SimplePoles h H lift) (hG : Balanced G)
    (s : Shape) (hs : s.B < K1.p) (U : Fin 2 → ℕ) (P : ι → TrueSource F)
    (hP : ∀ k, Shaped s (P k)) (hrect : ∀ k, RectSupport U (P k))
    {n : ℕ} (M : Matrix (Fin n) ι F)
    (hM : ∀ v, M.mulVec v = 0 ↔ PoleTest s H lift (Fintype.linearCombination F P v)) :
    M.rank ≤ poleDebit h s U := by
  classical
  have ht (t : Fin (2*h)) := local_tests F s hs U H lift (G.root t) (G.side t) (G.a t) (G.b t) (G.c t)
    (G.vanishes t) (G.simple t) (G.b_ne t) (G.centre t)
  choose d hd tests hwindow htest using ht
  have hread (t : Fin (2*h)) (r : Fin (poleRows s)) := read_rect_window F U (d t r) (G.side t)
  choose read hread using hread
  let f : (ι → F) →ₗ[F] (ScalarRows s U G.side d → F) :=
    LinearMap.pi fun r =>
      ((LinearMap.proj r.2.2).comp (read r.1 r.2.1)).comp
        ((tests r.1 r.2.1).comp (Fintype.linearCombination F P))
  have hker : LinearMap.ker f ≤ LinearMap.ker M.mulVecLin := by
    intro v hv
    apply LinearMap.mem_ker.mpr
    apply (hM v).mpr
    apply poleTest_of_local s G
    intro t
    apply htest t _ (shaped_combination hP v)
    intro r
    apply hread t r _ (hwindow t r _ (rect_combination hrect v))
    funext k
    exact congrFun (LinearMap.mem_ker.mp hv) ⟨t, r, k⟩
  have hn := Submodule.finrank_mono hker
  have hr : Module.finrank F (LinearMap.range f) ≤ poleDebit h s U := by
    refine (LinearMap.range f).finrank_le.trans ?_
    rw [Module.finrank_pi]
    exact scalar_rows_card_le G hG s U d hd
  have hf := f.finrank_range_add_finrank_ker
  have hm := M.mulVecLin.finrank_range_add_finrank_ker
  unfold Matrix.rank
  omega

/-- The pole debit for a seed rectangle inside the contacted source space. -/
theorem pole_bound {h : ℕ} (hpos : 0 < h) (hchar : h < K1.p) {D : PoleData h}
    (Crt : CRTLift D) (word : I → L) (s : Shape) (hs : s.B < K1.p) (W : ℕ)
    (U : Fin 2 → ℕ) (R : Submodule L Source) (hR : ∀ P ∈ R, RectSupport U P) :
    Module.finrank L (contacted h word s W ⊓ R : Submodule L Source) ≤ poleDebit h s U +
      Module.finrank L (complete Crt word s W ⊓ R : Submodule L Source) := by
  classical
  obtain ⟨E, hE⟩ := balanced_deformation hpos hchar D Crt
  let A : Submodule L Source := contacted h word s W ⊓ R
  let B : Submodule L Source := complete Crt word s W ⊓ R
  let _ : Module.Finite L (contacted h word s W) := contacted_finite h word s W
  let hA : A ≤ contacted h word s W := inf_le_left
  let _ : Module.Finite L A := Module.Finite.of_injective
    (Submodule.inclusion hA) (Submodule.inclusion_injective hA)
  let hBA : B ≤ A := inf_le_inf inf_le_left le_rfl
  let _ : Module.Finite L B := Module.Finite.of_injective
    (Submodule.inclusion hBA) (Submodule.inclusion_injective hBA)
  let d := Module.finrank L A
  let basis := Module.finBasis L A
  let P : Fin d → Source := fun k => basis k
  have hP (k : Fin d) : Shaped s (P k) := contacted_shaped (basis k).property.1
  have hrect (k : Fin d) : RectSupport U (P k) := hR _ (basis k).property.2
  obtain ⟨n, M, hspecial, hg⟩ := K1_14_1_7_4.proof E s (Fin d) P hP
  let embed := genericPoint.comp (Polynomial.C (R := L))
  let _ : CharP L K1.p := charP_of_injective_ringHom (algebraMap K L).injective K1.p
  let _ : CharP GenericField K1.p :=
    charP_of_injective_ringHom (f := embed) (generic_injective.comp Polynomial.C_injective) K1.p
  have hgen := simple_rank_le E.genericPoles hE s hs U _
    (fun k => shaped_map embed (hP k)) (fun k => rect_map embed (hrect k)) _ hg
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
      ((basis.equivFun.symm (v : Fin d → L) : A) : Source) ∈ B := by
    have hv := (hspecial v.val).mp (LinearMap.mem_ker.mp v.property)
    rw [hf] at hv
    exact ⟨⟨(basis.equivFun.symm v.val).property.1, hv⟩, (basis.equivFun.symm v.val).property.2⟩
  let g : LinearMap.ker f →ₗ[L] B :=
    LinearMap.codRestrict _ ((A.subtype.comp basis.equivFun.symm.toLinearMap).comp
      (LinearMap.ker f).subtype) hk
  have hginj : Function.Injective g := by
    intro v w hvw
    apply Subtype.ext
    apply basis.equivFun.symm.injective
    apply Subtype.ext
    exact congrArg (fun x : B => (x : Source)) hvw
  have hkd := LinearMap.finrank_le_finrank_of_injective hginj
  have hdf := f.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, Fintype.card_fin] at hdf
  change Module.finrank L (LinearMap.range f) ≤ _ at hrank
  change d ≤ poleDebit h s U + Module.finrank L B
  omega

#print axioms pole_bound

end
end KoalaRectPole

end Merged_KoalaRectPole

-- merged module KoalaRectPoleBridge
section Merged_KoalaRectPoleBridge

set_option Elab.async false
set_option autoImplicit false

namespace KoalaRect

open K1 (I)
open K1_14 (L Shape)
open K1_14_1 (CRTLift PoleData)
open P1_7_1 (groupedPoleMoment poleRows)

theorem rectPole_bound {h : ℕ} (hpos : 0 < h) (hchar : h < K1.p) {D : PoleData h}
    (Crt : CRTLift D) (word : I → L) (s : Shape) (hs : s.B < K1.p) (W : ℕ)
    (U : Fin 2 → ℕ) :
    Module.finrank L (rectContacted h word s W U) ≤
      2*h * poleRows s * area U + h * (U 0 + U 1 + 2) * groupedPoleMoment s.B s.J +
        Module.finrank L (rectComplete Crt word s W U) :=
  KoalaRectPole.pole_bound hpos hchar Crt word s hs W U (seedSupport U) (fun _ hp => hp)

#print axioms rectPole_bound

end KoalaRect

end Merged_KoalaRectPoleBridge

-- merged module KoalaRectBridgeCore
section Merged_KoalaRectBridgeCore

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace KoalaRect
noncomputable section
open Finset Polynomial
open K1 (I)
open K1_14 (L FX Jet Equation Shape shapeSum seedHasse)
open K1_14_1
open K1_14_3 (Surface Parent ProjectedProduct OrderAt)
open P1_7_1 (poleRows nodeRows groupedPoleMoment)
open scoped BigOperators

theorem rectRankFloor {h : ℕ} (hpos : 0 < h) (hraw : h ≤ 131070) (hchar : h < K1.p)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L) (s : Shape) (W : ℕ)
    (U : Fin 2 → ℕ) (hbox : U 0 + U 1 ≤ s.U) (hs : s.B < K1.p) (hw : rawWidthCond h s W)
    {nodes moment : ℕ} (hnodes : nodeRows s ≤ nodes) (hmoment : groupedPoleMoment s.B s.J ≤ moment) :
    area U * shapeSum s (fun q j => W+1+j-q*(131071-h)) ≤
      rectDebit h nodes moment U + ∑ t ∈ range (W+1), Module.finrank FX (rectEvaluated Crt word s t U) := by
  have hvol := rectAmbient_volume h s W U (hraw.trans (by decide)) hbox hw
  have hphys := rectPhysical_bound h word s W U
  have hpole := rectPole_bound hpos hchar Crt word s hs W U
  have hsum := rectTelescope hraw Crt word s W U
  have hm := Nat.mul_le_mul_left (h*(U 0+U 1+2)) hmoment
  have hn := Nat.mul_le_mul_left (area U) hnodes
  rw [show 2*h*poleRows s*area U = 2*h*area U*poleRows s by ring] at hpole
  unfold rectDebit
  omega

theorem rectDivides {h : ℕ} (hpos : 0 < h) {D : PoleData h} (Crt : CRTLift D) (word : I → L)
    (A : ℕ) (s : Shape) (U : Fin 2 → ℕ) (hsmall : s.m*A < K1.p)
    {qs : Finset Surface} (hgeo : ∀ q ∈ qs, Parent q)
    (hpass : ∀ q ∈ qs, ∀ P ∈ evaluated Crt word s (s.m*A-1), P ∈ q.asIdeal)
    {f : Equation} (hprod : ProjectedProduct qs f) {W : ℕ} (hW : W < s.m*A)
    {P : Jet} (hP : P ∈ rectEvaluated Crt word s W U) (hn : P ≠ 0) :
    f ^ (rectPower A h s W-P.natDegree) ∣ P.leadingCoeff := by
  have htri := rectEvaluated_le Crt word s W U hP
  apply hprod.divides_leading P _ hn
  intro q hq
  apply K1_14_3R_1.proof _ _ _ (hgeo q hq)
  · have hd := Nat.div_le_self (s.m*A-1-W) (2*h)
    unfold rectPower
    omega
  intro a c hac
  change a+c < 1+(s.m*A-1-W)/(2*h) at hac
  have hc := (Nat.le_div_iff_mul_le (by omega : 0 < 2*h)).mp
    (show a+c ≤ (s.m*A-1-W)/(2*h) by omega)
  rw [Nat.mul_comm (a+c), Nat.mul_add] at hc
  have hX : W+2*h*a+2*h*c ≤ s.m*A-1 := by omega
  have ha := P0_10_1.evaluated_shift Crt word htri 0 a
  have hb := P0_10_1.evaluated_shift Crt word ha 1 c
  exact hpass q hq _ (evaluated_mono Crt word rfl rfl rfl le_rfl hX hb)

theorem rectLoss {h : ℕ} (hpos : 0 < h) (hraw : h ≤ 131070) (hchar : h < K1.p)
    {D : PoleData h} (Crt : CRTLift D) (word : I → L) (A : ℕ) (s : Shape)
    (U d : Fin 2 → ℕ) (hA : 0 < s.m*A) (hsmall : s.m*A < K1.p) (hbox : U 0 + U 1 ≤ s.U)
    (hs : s.B < K1.p) (hwidth : s.B*(131071-h) ≤ s.m*A)
    {nodes moment E : ℕ} (hnodes : nodeRows s ≤ nodes) (hmoment : groupedPoleMoment s.B s.J ≤ moment)
    (he : 0 < E) {qs : Finset Surface} (hgeo : ∀ q ∈ qs, Parent q)
    (hpass : ∀ q ∈ qs, ∀ P ∈ evaluated Crt word s (s.m*A-1), P ∈ q.asIdeal)
    {f : Equation} (hf : f ≠ 0) (hE : E ≤ f.natDegree) (hprod : ProjectedProduct qs f)
    (hslots : ∀ r, rectSlots U (axisDegree f) r ≤ rectSlots U d r) :
    rectGain A h s E U d ≤ rectDebit h nodes moment U := by
  let top := s.m*A
  have htop : top-1+1 = top := by dsimp [top]; omega
  have hrawWidth : rawWidthCond h s (top-1) := by
    intro q hq j _
    rw [htop]
    exact (Nat.mul_le_mul_right _ hq).trans (hwidth.trans (by omega : top ≤ top+j))
  have hfloor := rectRankFloor hpos hraw hchar Crt word s (top-1) U hbox hs hrawWidth hnodes hmoment
  rw [htop] at hfloor
  have hcap (W : ℕ) (hW : W ∈ range top) :
      Module.finrank FX (rectEvaluated Crt word s W U) ≤ rectCapacity A h s E U d W := by
    apply rectCutoff_finrank_le _ _ _ _ _ _ _ _ hf hE (by omega) he
    · intro P hP j i hn
      exact evaluated_shape Crt word (rectEvaluated_le Crt word s W U hP) j i hn
    · intro P hP
      exact rectEvaluated_axis Crt word hP
    · intro P hP hn
      exact P0_10_1.leading_bound hpos hraw Crt word s W P (rectEvaluated_le Crt word s W U hP) hn
    · intro P hP hn
      exact rectDivides hpos Crt word A s U hsmall hgeo hpass hprod (mem_range.mp hW) hP hn
    · exact hslots
  have hsum := sum_le_sum (s := range top) hcap
  have htotal := rectCapacity_total A h s E U d (by omega) (by omega)
  change (∑ W ∈ range top, rectCapacity A h s E U d W) + rectGain A h s E U d =
    area U * shapeSum s (fun q j => top+j-q*(131071-h)) at htotal
  omega

#print axioms rectLoss
end
end KoalaRect

end Merged_KoalaRectBridgeCore

-- merged module R6960HelperPrefix
section Merged_R6960HelperPrefix
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1500000
namespace Lower6960.HelperPrefix
open Polynomial Finset
open K1_14 (Jet Shape Banks FX Seeds Equation)
open K1_14_2 (toJet Ambient)
open K1_14_2_2 (Active dual orderOn mass sectionDegree)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (Surface Parent ProjectedProduct)
open scoped Classical
open P1_7_4_2 (sections)
theorem product_power {R G H : Jet} {k : ℕ} (cop : IsRelPrime G H)
    (left : G^k∣R) (right : H^k∣R) : (G*H)^k∣R := by
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid (D:=Seeds)
  let : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D:=Equation)
  rw [mul_pow]
  exact (cop.pow_left.pow_right).mul_dvd left right
theorem powered_contact {R : Type*} [CommRing R] (I : Ideal R)
    {a : R} {s k n : ℕ} (h : a∈I^s) (fit : n≤s*k) : a^k∈I^n := by
  have p:=Ideal.pow_mem_pow h k
  rw [←pow_mul] at p
  exact Ideal.pow_le_pow_right fit p
theorem strip_contact {K : Type*} [Field K] (g a : (Polynomial K)) {n k : ℕ}
    (unit : g.eval 0≠0) (van : (Polynomial.X : (Polynomial K))^n∣g^k*a) :
    (Polynomial.X : (Polynomial K))^n∣a := by
  have nd : ¬ (Polynomial.X : (Polynomial K))∣g := fun h => unit ((coeff_zero_eq_eval_zero g).symm.trans (Polynomial.X_dvd_iff.mp h))
  have cop : IsCoprime (Polynomial.X : (Polynomial K)) g := Polynomial.irreducible_X.coprime_iff_not_dvd.mpr nd
  exact (cop.pow (m:=n) (n:=k)).dvd_of_dvd_mul_left van
theorem proper_power_mass (G Q : Jet) (s t : Shape) (S : Finset (Ideal Ambient))
    (k : ℕ) (pos : 0<k) (index : Fin 4) (ng : G≠0) (nq : Q≠0)
    (cop : IsRelPrime (toJet G) (toJet Q))
    (js : s.J≤s.B) (jt : t.J≤t.B)
    (capsG : K1_14_2_2.RowCaps (G^k) s) (capsQ : K1_14_2_2.RowCaps Q t)
    (on : ∀ I∈S, Active I ∧ dual I ∧ toJet G∈I ∧ orderOn I Q k) :
    (k*k)*mass S index≤pairCap s t index := by
  let : UniqueFactorizationMonoid Ambient := MvPolynomial.uniqueFactorizationMonoid (Fin 4)
  have hcop : IsRelPrime (toJet (G^k)) (toJet Q) := by rw [map_pow]; exact cop.pow_left
  apply sections (G^k) Q s t S index (k*k) (pow_ne_zero k ng) nq hcop js jt capsG capsQ (Nat.mul_pos pos pos)
  intro I hI
  obtain ⟨act,hd,hg,hq⟩ := on I hI
  have ho : orderOn I (G^k) k := by
    let _ := act.prime
    refine ⟨1,Ideal.one_notMem I,?_⟩
    rw [one_mul,map_pow]
    exact Ideal.mem_sup_left (Ideal.pow_mem_pow hg k)
  have len:=K1_14_2_2_4_4.proof (G^k) Q I act k pos ho hq
  rw [ite_eq_left hd,pow_two] at len
  exact ⟨act,fun _=>len⟩
theorem union_terminal (rows : Banks) (s : Shape) (left right : Finset Surface)
    (existsParent : (left∪right).Nonempty)
    (gl : ∀ q∈left,Parent q) (gr : ∀ q∈right,Parent q)
    (pl : ∀ q∈left,HighCore82258.BankPass rows s q)
    (pr : ∀ q∈right,HighCore82258.BankPass rows s q) :
    ∃ f, ProjectedProduct (left∪right) f ∧
      ∀ q∈left∪right, HighCore82258.BankPass rows s q := by
  classical
  obtain ⟨f,prod⟩:=K1_14_3_7.proof (left∪right) existsParent (by
    intro q mem; exact (mem_union.mp mem).elim (gl q) (gr q))
  exact ⟨f,prod,fun q mem=>(mem_union.mp mem).elim (pl q) (pr q)⟩
open K1_14_2_2_3
open K1_14_2_2_3 (shiftedWord specialize_shiftedWord)
theorem dual_order_of_tests {I : Ideal Ambient} (act : Active I) (dualI : dual I)
    (R : Jet) (r : ℕ) (small : r<K1.p)
    (tests : ∀ t : List (Fin 2), t.length≤r → toJet (shiftedWord R t)∈I) :
    orderOn I R (r+1) := by
  let a := algebraMap K1_14.Seeds K1_14_2.SeedField
  have hc : fibreContact (I.map (specializeJets a)) (specializeJets a (toJet R)) r := by
    intro t ht
    rw [←specialize_shiftedWord]
    exact Ideal.mem_map_of_mem _ (tests _ ht)
  rw [←mapGenericJets_eq] at hc
  exact clear_dual dualI (K1_14_2_2_3_1.proof I act.prime act.jet_finite dualI act.jet_lt _ r small hc)
theorem not_two_common (s : Shape) (h N : ℕ) (hh : 0<h)
    (rows : ℕ→Submodule FX Jet) (G H P : Jet) (g : Irreducible G) (h' : Irreducible H)
    (cop : IsRelPrime G H) (gs : 0<G.natDegree) (hs : 0<H.natDegree)
    (gu : K1_14_2.UsesSeed G) (hu : K1_14_2.UsesSeed H)
    (np : P≠0) (inside : P∈rows (N-1)) (small : s.U<K1.p)
    (pc : ∀ j i,((P.coeff j).coeff i).totalDegree≤s.U)
    (caps : ∀ W<N, ∀ R∈rows W,K1_14_3.RowCaps R s)
    (lead : ∀ W<N, ∀ R∈rows W,R≠0 →
      (R.leadingCoeff.natDegree+R.natDegree)*(131071-h)≤W+R.natDegree)
    (shift : ∀ W<N,∀ R∈rows W,∀ i a,W+2*h*a≤N-1 → K1_14.seedHasse i a R∈rows (N-1))
    (supply : (∑ W∈range N, Lower6960.PowerLayers.layerCost s h N W 2 0 1) <
      ∑ W∈range N,Module.finrank FX (rows W))
    (allG : ∀ Q∈rows (N-1),G∣Q) (allH : ∀ Q∈rows (N-1),H∣Q) : False := by
  let F:=G*H
  have fn : F≠0 := mul_ne_zero g.ne_zero h'.ne_zero
  have ds : 2≤F.natDegree := by dsimp only [F];rw [natDegree_mul g.ne_zero h'.ne_zero];omega
  have du : 1≤K1_14_2_2_2_1.seedDegree F := by
    obtain ⟨j,i,pos⟩:=gu
    have ge := (K1_14_2_2_2_1.seedDegree_le G _).1 le_rfl j i
    dsimp only [F]
    rw [K1_14_2_2_2_1.seedDegree_mul g.ne_zero h'.ne_zero]
    omega
  have dg : F.natDegree+0≤K1_14_2_2_2_1.jetDegree F := by
    have co : (F.coeff F.natDegree).coeff F.leadingCoeff.natDegree ≠ 0 := by
      rw [coeff_natDegree,coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr fn)
    have := (K1_14_2_2_2_1.jetDegree_le F _).1 le_rfl _ _ co
    omega
  apply Lower6960.PowerLayers.no_common_power s h N 2 0 1 rows F fn ds du dg caps lead supply
  intro W hw R hr
  apply product_power cop
  · exact Lower6960.PowerLayers.forced_power hh hw g gs gu np (allG P inside) small pc
      (fun i a ha=>allG _ (shift W hw R hr i a ha))
  · exact Lower6960.PowerLayers.forced_power hh hw h' hs hu np (allH P inside) small pc
      (fun i a ha=>allH _ (shift W hw R hr i a ha))
open K1_14_3R (fixed_of_no_seed)
theorem one_helper {ι : Type*} [Fintype ι] (P : ι→Jet) (ks : ι→ℕ)
    (V : Submodule FX Jet) (nonempty : ∃ H∈V,H≠0)
    (proper : ∀ i,P i≠0)
    (avoid : ∀ i G,Irreducible G → G∣P i → 0<G.natDegree → K1_14_2.UsesSeed G →
      ∃ H∈V, ¬ G∣H) :
    ∃ H∈V,H≠0 ∧ ∀ i,K1_14_3.NoMovingCommon (P i) (H^(ks i)) := by
  classical
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid (D:=Seeds)
  let : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D:=Equation)
  have prod : (∏ i,P i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>proper i)
  obtain ⟨H,inside,nh,all⟩:=K1_14_2_1.exists_layered (∏ i,P i) prod V nonempty (by
    intro G irr divides degree seeded
    obtain ⟨i,_,di⟩:=irr.prime.exists_mem_finset_dvd divides
    exact avoid i G irr di degree seeded)
  refine ⟨H,inside,nh,?_⟩
  intro i G irr left right degree
  apply fixed_of_no_seed
  intro seeded
  exact all G irr (left.trans (Finset.dvd_prod_of_mem P (Finset.mem_univ i))) degree seeded
    (irr.prime.dvd_of_dvd_pow right)
open P0_10R_1 (section_bound component_height)
open P1_7_4_1 (irreducible_cut)
theorem exceptional_initial (G Q : Jet) (s t : Shape) (irr : Irreducible G)
    (nd : ¬G∣Q) (js : s.J≤s.B) (jt : t.J≤t.B)
    (cg : K1_14_2_2.RowCaps G s) (cq : K1_14_2_2.RowCaps Q t) :
    ∃ S : Finset (Ideal Ambient), P1_7_4_1.SectionGeometry S ∧
      K1_14_2_2.Fits S (K1_14_2_2_2.residualBudget s t) ∧
      (∀ I∈S,toJet G∈I) ∧
      ∀ z R,K1_14.jetAt G z R=0 → K1_14.jetAt Q z R=0 →
        ∃ I∈S,K1_14_2.OnJet I z R := by
  have proper:=irreducible_cut irr nd
  obtain ⟨S,hs,cover⟩:=K1_14_2_2_2_3.proof _ _ proper
  obtain ⟨finite,fit⟩:=section_bound _ _ proper s t js jt cg cq S hs
  refine ⟨S,?_,fit,fun I hi=>(hs I hi).2.2.1,cover⟩
  intro I hi
  obtain ⟨prime,dim,row,cut⟩:=hs I hi
  exact ⟨prime,dim,component_height proper prime dim row cut,finite I hi⟩
def timesShape (k : ℕ) (s : Shape) : Shape := ⟨k*s.m,k*s.B,k*s.J,k*s.U⟩
theorem scaled_pair (k : ℕ) (s t : Shape) (i : Fin 4) :
    pairCap (timesShape k s) t i=k*pairCap s t i := by
  fin_cases i <;> simp [timesShape,pairCap,Nat.mul_sub,Nat.mul_add,
    Nat.mul_left_comm,Nat.mul_comm]
theorem exceptional_history (G Q : Jet) (s t : Shape) (S : Finset (Ideal Ambient))
    (k : ℕ) (hk : 0<k) (i : Fin 4) (ng : G≠0) (nq : Q≠0)
    (cop : IsRelPrime (toJet G) (toJet Q))
    (hs : s.J≤s.B) (ht : t.J≤t.B)
    (hc : K1_14_2_2.RowCaps (G^k) (timesShape k s)) (hq : K1_14_2_2.RowCaps Q t)
    (on : ∀ I∈S,Active I ∧ dual I ∧ toJet G∈I ∧ orderOn I Q k) :
    k*mass S i≤pairCap s t i := by
  have bound:=proper_power_mass G Q (timesShape k s) t S k hk i ng nq cop
    (Nat.mul_le_mul_left _ hs) ht hc hq on
  rw [scaled_pair,Nat.mul_assoc] at bound
  exact Nat.le_of_mul_le_mul_left bound hk
theorem high_ledger :
    116851670497542517 + 118687375614631597 + 27283109943102372 +
    143456202788540 + 48 + 3730105881391565 = 266695718139456639 := by decide +kernel
#print axioms exceptional_initial
#print axioms exceptional_history
#print axioms high_ledger
#print axioms one_helper
#print axioms not_two_common
#print axioms dual_order_of_tests
#print axioms product_power
#print axioms powered_contact
#print axioms strip_contact
#print axioms proper_power_mass
#print axioms union_terminal
end Lower6960.HelperPrefix

end
end Merged_R6960HelperPrefix
