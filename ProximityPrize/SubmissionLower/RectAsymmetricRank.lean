import ProximityPrize.SubmissionLower.RectAsymmetricDeformation
import ProximityPrize.SubmissionLower.Rect51PoleWindowRank

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 16

namespace RectAsymmetric
noncomputable section

open Polynomial Matrix
open K1_14 (Shape L)
open K1_14_1 K1_14_1_7 K1_14_1_7_3
open P1_7_1 (poleRows groupedPoleMoment)
open Rect51PoleWindow (RectShaped Slots slots_card local_tests read read_eq_zero rect_map rect_combination)
open scoped BigOperators Polynomial
open private poleTest_of_local from ProximityPrize.SubmissionLower.Fast065

/-- The balanced pole debit for two independent seed caps. -/
def debit (h : ℕ) (s : Shape) (u v : ℕ) : ℕ :=
  2*h*poleRows s*(u+1)*(v+1) + h*(u+v+2)*groupedPoleMoment s.B s.J

theorem debit_equal (h : ℕ) (s : Shape) (u : ℕ) :
    debit h s u u = Rect51PoleWindow.debit h s u := by
  unfold debit Rect51PoleWindow.debit
  ring

private abbrev ScalarRow {h : ℕ} {F : Type} [Field F] {H : F[X]} {lift : (SeedFrac F)[X]}
    (G : SimplePoles h H lift) (s : Shape) (u v : ℕ)
    (d : Fin (2*h) → Fin (poleRows s) → ℕ) :=
  Σ t : Fin (2*h), Σ r : Fin (poleRows s), Slots ![u,v] (d t r) (G.side t)

private theorem scalarRow_card_le {h : ℕ} {F : Type} [Field F] {H : F[X]}
    {lift : (SeedFrac F)[X]} (G : SimplePoles h H lift) (balanced : Balanced G)
    (s : Shape) (u v : ℕ) (d : Fin (2*h) → Fin (poleRows s) → ℕ)
    (hd : ∀ t, (∑ r, d t r) ≤ groupedPoleMoment s.B s.J) :
    Fintype.card (ScalarRow G s u v d) ≤ debit h s u v := by
  classical
  let extra : Fin 2 → ℕ := fun k => (![u,v] : Fin 2 → ℕ) (otherBlock k) + 1
  let area := (u+1)*(v+1)
  let moment := groupedPoleMoment s.B s.J
  simp only [ScalarRow, Fintype.card_sigma, slots_card]
  change (∑ t, ∑ r, (area + extra (G.side t) * d t r)) ≤ _
  calc
    _ ≤ ∑ t, (poleRows s * area + extra (G.side t) * moment) := by
      apply Finset.sum_le_sum
      intro t _
      have hs : (∑ r : Fin (poleRows s), (area + extra (G.side t) * d t r)) =
          poleRows s * area + extra (G.side t) * (∑ r, d t r) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rfl
      rw [hs]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (hd t)) _
    _ = debit h s u v := by
      have hs : (∑ t : Fin (2*h), (poleRows s * area + extra (G.side t) * moment)) =
          (2*h)*(poleRows s*area) + (∑ t, extra (G.side t))*moment := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rfl
      rw [hs, balanced extra]
      change (2*h)*(poleRows s*area)+(h*(v+1)+h*(u+1))*moment = _
      unfold debit area moment
      ring

theorem simple_rank_le {F ι : Type} [Field F] [Fintype ι] {h : ℕ}
    {H : F[X]} {lift : (SeedFrac F)[X]}
    (G : SimplePoles h H lift) (balanced : Balanced G) (s : Shape) (u v : ℕ) (P : ι → TrueSource F)
    (hP : ∀ k, RectShaped s ![u,v] (P k)) {n : ℕ} (M : Matrix (Fin n) ι F)
    (hM : ∀ v, M.mulVec v = 0 ↔ PoleTest s H lift (Fintype.linearCombination F P v)) :
    M.rank ≤ debit h s u v := by
  classical
  have ht (t : Fin (2*h)) := local_tests F s ![u,v] H lift
    (G.root t) (G.side t) (G.a t) (G.b t) (G.c t) (G.vanishes t) (G.b_ne t) (G.centre t)
  choose d hd tests hwindow htest using ht
  let f : (ι → F) →ₗ[F] (ScalarRow G s u v d → F) :=
    LinearMap.pi fun r =>
      ((LinearMap.proj r.2.2).comp (read F ![u,v] (d r.1 r.2.1) (G.side r.1))).comp
        ((tests r.1 r.2.1).comp (Fintype.linearCombination F P))
  have hker : LinearMap.ker f ≤ LinearMap.ker M.mulVecLin := by
    intro v hv
    apply LinearMap.mem_ker.mpr
    apply (hM v).mpr
    apply poleTest_of_local s G
    intro t
    have hv' := rect_combination hP v
    apply htest t _ hv'
    intro r
    apply read_eq_zero (hwindow t r _ hv')
    funext k
    exact congrFun (LinearMap.mem_ker.mp hv) ⟨t, r, k⟩
  have hn := Submodule.finrank_mono hker
  have hr : Module.finrank F (LinearMap.range f) ≤ debit h s u v := by
    refine (LinearMap.range f).finrank_le.trans ?_
    rw [Module.finrank_pi]
    exact scalarRow_card_le G balanced s u v d hd
  have hf := f.finrank_range_add_finrank_ker
  have hm := M.mulVecLin.finrank_range_add_finrank_ker
  unfold Matrix.rank
  omega

/-- Specialize the rank estimate to the given CRT data on any finite rectangular source. -/
theorem finrank_le_of_pole {h : ℕ} (hpos : 0 < h) (hchar : h < K1.p)
    {D : PoleData h} (Crt : CRTLift D) (s : Shape) (u v : ℕ)
    (A T : Submodule L Source) [Module.Finite L A] [Module.Finite L T]
    (hA : ∀ P ∈ A, RectShaped s ![u,v] P)
    (hT : ∀ P ∈ A, PoleTest s (poleProduct D) (crtPolynomial Crt) P → P ∈ T) :
    Module.finrank L A ≤ debit h s u v + Module.finrank L T := by
  classical
  obtain ⟨E, hE⟩ := regular_deformation hpos hchar D Crt
  let d := Module.finrank L A
  let basis := Module.finBasis L A
  let P : Fin d → Source := fun k => basis k
  have hP (k : Fin d) : RectShaped s ![u,v] (P k) := hA _ (basis k).property
  obtain ⟨n, M, hspecial, hg⟩ := K1_14_1_7_4.proof E s (Fin d) P (fun k => (hP k).1)
  let embed := genericPoint.comp (Polynomial.C (R := L))
  have hgen := simple_rank_le E.genericPoles hE s u v _ (fun k => rect_map embed (hP k)) _ hg
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
      ((basis.equivFun.symm (v : Fin d → L) : A) : Source) ∈ T := by
    have hv := (hspecial v.val).mp (LinearMap.mem_ker.mp v.property)
    rw [hf] at hv
    exact hT _ (basis.equivFun.symm (v : Fin d → L) : A).property hv
  let g : LinearMap.ker f →ₗ[L] T :=
    LinearMap.codRestrict _ ((A.subtype.comp basis.equivFun.symm.toLinearMap).comp
      (LinearMap.ker f).subtype) hk
  have hginj : Function.Injective g := by
    intro v w hvw
    apply Subtype.ext
    apply basis.equivFun.symm.injective
    apply Subtype.ext
    exact congrArg (fun x : T => (x : Source)) hvw
  have hkd := LinearMap.finrank_le_finrank_of_injective hginj
  have hdf := f.finrank_range_add_finrank_ker
  rw [Module.finrank_pi, Fintype.card_fin] at hdf
  change Module.finrank L (LinearMap.range f) ≤ _ at hrank
  change d ≤ _
  omega

#print axioms finrank_le_of_pole
end
end RectAsymmetric
