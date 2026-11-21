import ProximityPrize.SubmissionLower.KoalaFreshRoot
import ProximityPrize.SubmissionLower.KoalaSeedBounds
import ProximityPrize.SubmissionLower.KoalaRawBounds

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace SplitCut.Compression
noncomputable section

open Polynomial HighCore82229Upper HighCore82229Upper_3
open K1_14 (L FX Equation liftPoly atX graphEval atMark seedEmbedding)
open K1_14_6 (Biform rootPoint)
open K1_14_6_1 (flatten markEval)
open P1 (K p)
open private HighCore82229Upper_3_2.seed_at_mark HighCore82229Upper_3_3_1.mark_biform
  HighCore82229Upper_2.seed_at_mark from ProximityPrize.SubmissionLower.HighCore82229UpperGeometry

structure MarkCompression (J : Input) (v w : ℕ) where
  G : FreshEquation L
  width : G.natDegree + J.e*P1_7.degreeAt J.hi < p
  yBound : ∀ i, (G.coeff i).natDegree ≤ J.e
  axes : ∀ i j, ((G.coeff i).coeff j).degreeOf 0 ≤ v+128 ∧
    ((G.coeff i).coeff j).degreeOf 1 ≤ w+128
  i : ℕ
  j : ℕ
  nonzero : (G.coeff i).coeff j ≠ 0
  atMarks : ∀ γ ∈ J.marks, atMark (centerEquation G) (J.model.label γ) (J.family.scalar γ) = 0

namespace MarkCompression

abbrev witness {J : Input} {v w : ℕ} (M : MarkCompression J v w) : SeedConstants :=
  (M.G.coeff M.i).coeff M.j

def good {J : Input} {v w : ℕ} (M : MarkCompression J v w) : Finset K := by
  classical
  exact J.marks.filter fun γ => evalSeedConstants (J.model.label γ) M.witness ≠ 0

theorem mem_good {J : Input} {v w : ℕ} (M : MarkCompression J v w) {γ : K} :
    γ ∈ M.good ↔ γ ∈ J.marks ∧ evalSeedConstants (J.model.label γ) M.witness ≠ 0 := by
  simp [good]

theorem bad_bound {J : Input} {v w : ℕ} (M : MarkCompression J v w) (hv : v ≤ 445) :
    (J.marks \ M.good).card ≤ (p+1)*(v+w+256) := by
  classical
  let B := J.marks \ M.good
  let a : K → L := fun γ => algebraMap K L (J.model.label γ)
  have ha : Set.InjOn a (B : Set K) := fun x _ y _ h => sub_left_inj.mp ((algebraMap K L).injective h)
  have hb : ∀ t ∈ B.image a, MvPolynomial.eval ![t,t^p] M.witness = 0 := by
    intro t ht
    obtain ⟨γ,hγ,rfl⟩ := Finset.mem_image.mp ht
    by_contra h
    exact (Finset.mem_sdiff.mp hγ).2 ((mem_good M).mpr ⟨(Finset.mem_sdiff.mp hγ).1,h⟩)
  have he := K1_14.frobenius_coefficient_exception_count p (v+128) (w+128) (by decide)
    M.witness M.nonzero (M.axes _ _).1 (show v+128<p by change v+128 < 2130706433; omega)
    (M.axes _ _).2 (B.image a) hb
  rw [Finset.card_image_of_injOn ha] at he
  refine he.trans ?_
  calc
    v+128+p*(w+128) ≤ (p+1)*(v+128)+(p+1)*(w+128) := by
      exact Nat.add_le_add (Nat.le_mul_of_pos_left _ (by omega)) (Nat.mul_le_mul_right _ (by omega))
    _ = _ := by ring

end MarkCompression

private theorem center_at_mark (J : Input) (G : FreshEquation L) (γ : K)
    (h : StableNode.substitute (liftPoly (J.family.scalar γ))
      (G.map (mapRingHom (evalSeedConstants (J.model.label γ)))) = 0) :
    atMark (centerEquation G) (J.model.label γ) (J.family.scalar γ) = 0 := by
  let z := J.model.label γ
  let s := J.family.scalar γ
  have hh := congrArg (Polynomial.map constantAbscissa) h
  rw [FreshRoot.map_substitute, Polynomial.map_zero, Polynomial.map_map] at hh
  have hseed : (mapRingHom constantAbscissa).comp (mapRingHom (evalSeedConstants z)) =
      mapRingHom ((graphEval z).comp liftSeeds) := by
    rw [HighCore82229Upper_3_2.seed_at_mark]
    apply RingHom.ext
    intro P
    exact Polynomial.map_map _ _ _
  have hA : ((liftPoly s).map constantAbscissa).eval center = atX s := by
    rw [eval_map]
    change (liftPoly s).eval₂ ((algebraMap L[X] FX).comp Polynomial.C)
      ((algebraMap L[X] FX) Polynomial.X) = _
    rw [← hom_eval₂, eval₂_C_X]
    rfl
  change (centerEquation G).eval₂ (graphEval z) (atX s) = 0
  rw [center_eval, show graphEval z (MvPolynomial.C center) = center from MvPolynomial.eval_C _,
    ← hseed, ← hA, ← FreshRoot.substitute_eval]
  rw [hh, eval_zero]

theorem compress_marks (J : Input) (v w : ℕ) (he : J.e ≤ 21) (hv : v ≤ 445) (hw : w ≤ 445)
    (hhi : J.hi ≤ 2439)
    (haxis : ∀ i, (J.f.coeff i).degreeOf 0 ≤ v ∧ (J.f.coeff i).degreeOf 1 ≤ w) :
    Nonempty (MarkCompression J v w) := by
  classical
  let α := {γ // γ ∈ J.marks}
  let S : α → L[X] := fun γ => liftPoly (J.family.scalar γ.val)
  let z : α → Fin 2 → L := fun γ =>
    ![algebraMap K L (J.model.label γ.val), (algebraMap K L (J.model.label γ.val))^p]
  have hf : flatten J.f ≠ 0 := by
    intro h
    have hz := (MvPolynomial.optionEquivLeft FX (Fin 2)).symm.injective (h.trans (map_zero _).symm)
    have hh := J.sheets
    change 3 ≤ J.f.natDegree at hh
    rw [hz, Polynomial.natDegree_zero] at hh
    omega
  have hfit := SplitCut.Raw.root (f:=J.f) le_rfl haxis
  have hS (g : α) : (S g).natDegree ≤ P1_7.degreeAt J.hi :=
    natDegree_map_le.trans ((HighCore82229Upper.fixed_word J (Finset.Subset.refl _)).degree _ g.property)
  have hroot (g : α) : MvPolynomial.eval (fun i : Option (Fin 2) => i.elim
      (algebraMap L[X] FX (S g)) (fun j => algebraMap L[X] FX (Polynomial.C (z g j))))
        (flatten J.f) = 0 := by
    have heq : (fun i : Option (Fin 2) => i.elim
      (algebraMap L[X] FX (S g)) (fun j => algebraMap L[X] FX (Polynomial.C (z g j)))) =
        rootPoint (J.model.label g.val) (J.family.scalar g.val) := by
      funext i
      cases i with
      | none => rfl
      | some j => fin_cases j <;> simp [z, rootPoint, seedEmbedding]
    rw [heq]
    exact (K1_14_6_1.eval_flatten _ _ _).trans (J.regular g.val g.property).1
  have hd : P1_7.degreeAt J.hi ≤ 133510 := by unfold P1_7.degreeAt; omega
  have hp : J.e*P1_7.degreeAt J.hi < p := by
    exact (Nat.mul_le_mul he hd).trans_lt (by decide)
  obtain ⟨G,hGn,hGx,hGy,hGz,hGmarks⟩ := compressed_polynomial S z hf hfit hS hroot
    (koala_guard he hv hw hd) hp
  have hsome : ∃ i j, (G.coeff i).coeff j ≠ 0 := by
    by_contra! h
    apply hGn
    apply Polynomial.ext
    intro i
    apply Polynomial.ext
    intro j
    simp [h i j]
  obtain ⟨i,j,hij⟩ := hsome
  refine ⟨⟨G,hGx,hGy,hGz,i,j,hij,fun γ hγ => ?_⟩⟩
  exact center_at_mark J G γ (hGmarks ⟨γ,hγ⟩)

end
end SplitCut.Compression

#print axioms SplitCut.Compression.compress_marks
#print axioms SplitCut.Compression.MarkCompression.bad_bound
