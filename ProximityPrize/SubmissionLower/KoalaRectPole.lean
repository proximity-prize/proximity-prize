import ProximityPrize.SubmissionLower.KoalaRectPoleBalance
import ProximityPrize.SubmissionLower.KoalaRectPoleLocal

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
open private poleTest_of_local from ProximityPrize.SubmissionLower.Fast065

def poleDebit (h : ℕ) (s : Shape) (U : Fin 2 → ℕ) : ℕ :=
  2*h * poleRows s * ((U 0 + 1) * (U 1 + 1)) +
    h * (U 0 + U 1 + 2) * groupedPoleMoment s.B s.J

private abbrev Slots (U : Fin 2 → ℕ) (d : ℕ) (side : Fin 2) :=
  ∀ z : Fin 2, Fin (U z + (if z = side then d else 0) + 1)

private def slotExponent {U : Fin 2 → ℕ} {d : ℕ} {side : Fin 2} (k : Slots U d side) : Exponent :=
  Finsupp.equivFunOnFinite.symm (fun z => (k z).val)

theorem read_rect_window (F : Type) [Field F] (U : Fin 2 → ℕ) (d : ℕ) (side : Fin 2) :
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

abbrev ScalarRows {h : ℕ} (s : Shape) (U : Fin 2 → ℕ)
    (side : Fin (2*h) → Fin 2) (d : Fin (2*h) → Fin (poleRows s) → ℕ) :=
  Σ t : Fin (2*h), Σ r : Fin (poleRows s), Slots U (d t r) (side t)

theorem scalar_rows_card_le {h : ℕ} {F : Type} [Field F] {H : F[X]}
    {lift : (SeedFrac F)[X]} (G : SimplePoles h H lift) (hG : Balanced G) (s : Shape)
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
    {H : F[X]} {lift : (SeedFrac F)[X]} (G : SimplePoles h H lift) (hG : Balanced G)
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


end
end KoalaRectPole
