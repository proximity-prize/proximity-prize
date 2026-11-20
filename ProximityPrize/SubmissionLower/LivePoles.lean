import ProximityPrize.SubmissionLower.HighSource6921Rank

namespace LivePoles
noncomputable section
open K1 K1_14 K1_14_1 K1_14_1_7 K1_14_1_7_3 Polynomial
open scoped BigOperators Polynomial
open private fixed_eval_ne_zero from ProximityPrize.SubmissionLower.Fast065

theorem offset_ne {h : ℕ} (hh : 0 < h) (D : PoleData h) (i : Fin 2)
    {α : GenericField} (hr : (genericBlock D i).eval α = 0) :
    ((D.offset i).map constGeneric).eval α ≠ 0 := by
  apply fixed_eval_ne_zero D i hr
  intro he
  have hc := (D.determinant i).of_mul_left_left
  rw [he,isCoprime_zero_left] at hc
  exact not_isUnit_of_natDegree_pos _ (by simpa [D.degree] using hh) hc

theorem nonconstant {h : ℕ} (hlo : 0 < h) (hhi : h < K1.p) (D : PoleData h)
    (lift : (SeedFrac GenericField)[X])
    (hcentre : ∀ i α, (genericBlock D i).eval α = 0 →
      ((D.constant i).map constGeneric).eval α ≠ 0 →
      lift.eval (algebraMap GenericField (SeedFrac GenericField) α) =
        residue i (-((D.offset i).map constGeneric).eval α)
          (((D.constant i).map constGeneric).eval α) (((D.slope i).map constGeneric).eval α))
    (t : Fin (2*h)) : (simplePoles hlo hhi D lift hcentre).a t ≠ 0 := by
  let G := simplePoles hlo hhi D lift hcentre
  change -((D.offset (G.side t)).map constGeneric).eval (G.root t) ≠ 0
  apply neg_ne_zero.mpr
  apply offset_ne hlo D (G.side t)
  have hrs : ∃ i : Fin 2, (genericBlock D i).eval (G.root t) = 0 := by
    have he := G.vanishes t
    change ((movingProduct D).map genericPoint).eval (G.root t) = 0 at he
    simp only [movingProduct,Polynomial.map_mul,eval_mul] at he
    rcases mul_eq_zero.mp he with h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
  change (genericBlock D (Classical.choose hrs)).eval (G.root t) = 0
  exact Classical.choose_spec hrs

open private generic_den generic_centre from ProximityPrize.SubmissionLower.HighSource6921Rank

/-- A production deformation with an invertible projective seed change at every
generic simple pole, including when either special divisor has repeated roots. -/
theorem deformation (h : ℕ) (hh : 0 < h) (hp : h < K1.p) (D : PoleData h) (Crt : CRTLift D) :
    ∃ E : RegularDeformation D Crt, ∀ t, E.genericPoles.a t ≠ 0 := by
  let B : ∀ i, BlockLift D Crt i := blockLift hh D Crt
  let den := (B 0).den * (B 1).den
  let num := C (B 1).den * (B 0).num + C (B 0).den * (B 1).num
  have hd : specialSeed den ≠ 0 := by
    dsimp only [den]
    rw [map_mul]
    exact mul_ne_zero (B 0).specialDen (B 1).specialDen
  have hm := ((movingBlock_degree hh D 0).monic).mul (movingBlock_degree hh D 1).monic
  have centre : ∀ i α, (genericBlock D i).eval α = 0 →
      ((D.constant i).map constGeneric).eval α ≠ 0 →
      (liftAt genericPoint num den).eval (algebraMap GenericField (SeedFrac GenericField) α) =
        residue i (-((D.offset i).map constGeneric).eval α)
          (((D.constant i).map constGeneric).eval α) (((D.slope i).map constGeneric).eval α) := by
    intro i α hr hb
    dsimp only [num,den]
    rw [liftAt_add _ _ _ _ _ (generic_den (B 0).specialDen) (generic_den (B 1).specialDen)]
    simpa only [Fin.sum_univ_two] using generic_centre B i α hr hb
  refine ⟨⟨movingProduct D,num,den,hm,?_,hd,?_,generic_den hd,simplePoles hh hp D _ centre⟩,?_⟩
  · rw [movingProduct,Polynomial.map_mul,movingBlock_spec,movingBlock_spec,poleProduct]
  · dsimp only [num,den]
    rw [liftAt_add _ _ _ _ _ (B 0).specialDen (B 1).specialDen,
      (B 0).specialLift,(B 1).specialLift,crtPolynomial,Fin.sum_univ_two]
  · exact nonconstant hh hp D _ centre
end
end LivePoles
