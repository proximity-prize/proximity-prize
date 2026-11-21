import ProximityPrize.SubmissionLower.UpperBranch1

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

namespace KoalaRectPole
noncomputable section

open Polynomial
open K1_14_1 K1_14_1_7 K1_14_1_7_3
open scoped BigOperators Polynomial
open private deriv_eval_ne_zero other_eval_ne_zero constant_eval_ne_zero
  generic_den generic_centre from ProximityPrize.SubmissionLower.Fast065

/-- Each generic pole block can be indexed by its seed coordinate and one of `h` roots. -/
def Balanced {F : Type} [Field F] {h : ℕ} {H : F[X]} {lift : (SeedFrac F)[X]}
    (G : SimplePoles h H lift) : Prop :=
  ∃ e : Fin (2*h) ≃ Fin 2 × Fin h, ∀ t, G.side t = (e t).1

private theorem balanced_simple_poles {h : ℕ} (hlo : 0 < h) (hhi : h < K1.p) (D : PoleData h)
    (lift : (SeedFrac GenericField)[X])
    (hcentre : ∀ i α, (genericBlock D i).eval α = 0 →
      ((D.constant i).map constGeneric).eval α ≠ 0 →
      lift.eval (algebraMap GenericField (SeedFrac GenericField) α) =
        residue i (-((D.offset i).map constGeneric).eval α)
          (((D.constant i).map constGeneric).eval α) (((D.slope i).map constGeneric).eval α)) :
    ∃ G : SimplePoles h ((movingProduct D).map genericPoint) lift, Balanced G := by
  classical
  let H := (movingProduct D).map genericPoint
  have hblocks : H = genericBlock D 0 * genericBlock D 1 := by
    simp only [H, movingProduct, Polynomial.map_mul]
  have hmonic (i : Fin 2) : (genericBlock D i).Monic := (movingBlock_degree hlo D i).monic.map _
  have hdegree (i : Fin 2) : (genericBlock D i).natDegree = h :=
    ((movingBlock_degree hlo D i).monic.natDegree_map _).trans (movingBlock_degree hlo D i).natDegree_eq
  have hsep (i : Fin 2) : (genericBlock D i).Separable := by
    apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed GenericField GenericField _ _).mpr
    intro α
    by_cases he : (genericBlock D i).eval α = 0
    · exact Or.inr (by simpa using deriv_eval_ne_zero hlo hhi D i he)
    · exact Or.inl (by simpa using he)
  let roots (i : Fin 2) := (genericBlock D i).roots.toFinset
  have hcard (i : Fin 2) : Fintype.card (roots i) = h := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (nodup_roots (hsep i)),
      ← (IsAlgClosed.splits (genericBlock D i)).natDegree_eq_card_roots, hdegree]
  let e (i : Fin 2) : Fin h ≃ ↥(roots i) := (Fintype.equivFinOfCardEq (hcard i)).symm
  let α (i : Fin 2) (k : Fin h) : GenericField := (e i k).val
  have hroot (i : Fin 2) (k : Fin h) : (genericBlock D i).eval (α i k) = 0 :=
    (mem_roots (hmonic i).ne_zero).mp (Multiset.mem_toFinset.mp (e i k).property)
  let index : Fin (2*h) ≃ Fin 2 × Fin h := finProdFinEquiv.symm
  let side (t : Fin (2*h)) := (index t).1
  let root (t : Fin (2*h)) := α (side t) (index t).2
  have hinj : Function.Injective root := by
    intro t u htu
    apply index.injective
    have hs : side t = side u := by
      by_contra hne
      have he : side u = otherBlock (side t) := by
        generalize side t = i at hne ⊢
        generalize side u = j at hne ⊢
        fin_cases i <;> fin_cases j <;> simp_all [otherBlock]
      have ht := other_eval_ne_zero hlo D (side t) (hroot (side t) (index t).2)
      change (genericBlock D (otherBlock (side t))).eval (root t) ≠ 0 at ht
      rw [htu, ← he] at ht
      exact ht (hroot (side u) (index u).2)
    refine Prod.ext hs ?_
    apply (e (side t)).injective
    apply Subtype.ext
    change α (side t) (index t).2 = α (side t) (index u).2
    exact htu.trans (by change α (side u) (index u).2 = _; rw [hs])
  have hprod (i : Fin 2) : genericBlock D i = ∏ k, (Polynomial.X - C (α i k)) := by
    rw [(e i).prod_comp (fun x => Polynomial.X - C x.val)]
    rw [Finset.prod_coe_sort (roots i) (fun x => Polynomial.X - C x)]
    have he : (roots i).val = (genericBlock D i).roots :=
      (Multiset.toFinset_val _).trans (nodup_roots (hsep i)).dedup
    simpa only [Finset.prod, he] using (IsAlgClosed.splits (genericBlock D i)).eq_prod_roots_of_monic (hmonic i)
  have hvan (t : Fin (2*h)) : H.eval (root t) = 0 := by
    have he := hroot (side t) (index t).2
    change (genericBlock D (side t)).eval (root t) = 0 at he
    rw [hblocks, eval_mul]
    rcases (show ∀ i : Fin 2, i = 0 ∨ i = 1 by decide) (side t) with hz | hz
    · rw [hz] at he
      rw [he, zero_mul]
    · rw [hz] at he
      rw [he, mul_zero]
  have hsimple (t : Fin (2*h)) : H.derivative.eval (root t) ≠ 0 := by
    have he := hroot (side t) (index t).2
    change (genericBlock D (side t)).eval (root t) = 0 at he
    have hn := deriv_eval_ne_zero hlo hhi D (side t) he
    have ho := other_eval_ne_zero hlo D (side t) he
    rw [hblocks, derivative_mul, eval_add, eval_mul, eval_mul]
    rcases (show ∀ i : Fin 2, i = 0 ∨ i = 1 by decide) (side t) with hz | hz
    · rw [hz] at he hn ho
      change (genericBlock D 1).eval (root t) ≠ 0 at ho
      rw [he, zero_mul, add_zero]
      exact mul_ne_zero hn ho
    · rw [hz] at he hn ho
      change (genericBlock D 0).eval (root t) ≠ 0 at ho
      rw [he, mul_zero, zero_add]
      exact mul_ne_zero ho hn
  let G : SimplePoles h H lift := {
    root := root
    side := side
    a := fun t => -((D.offset (side t)).map constGeneric).eval (root t)
    b := fun t => ((D.constant (side t)).map constGeneric).eval (root t)
    c := fun t => ((D.slope (side t)).map constGeneric).eval (root t)
    distinct := hinj
    factorization := by
      change H = ∏ t, (Polynomial.X - C (α (index t).1 (index t).2))
      rw [index.prod_comp (fun p => Polynomial.X - C (α p.1 p.2)),
        Fintype.prod_prod_type, Fin.prod_univ_two, hblocks, ← hprod 0, ← hprod 1]
    vanishes := hvan
    simple := hsimple
    b_ne := fun t => constant_eval_ne_zero hlo D (side t) (hroot (side t) (index t).2)
    centre := fun t => hcentre _ _ (hroot (side t) (index t).2)
      (constant_eval_ne_zero hlo D (side t) (hroot (side t) (index t).2)) }
  exact ⟨G, index, fun _ => rfl⟩

theorem balanced_deformation {h : ℕ} (hh : 0 < h) (hp : h < K1.p)
    (D : PoleData h) (Crt : CRTLift D) :
    ∃ E : RegularDeformation D Crt, Balanced E.genericPoles := by
  let B : ∀ i, BlockLift D Crt i := blockLift hh D Crt
  let den := (B 0).den * (B 1).den
  let num := C (B 1).den * (B 0).num + C (B 0).den * (B 1).num
  have hden : specialSeed den ≠ 0 := by
    dsimp only [den]
    rw [map_mul]
    exact mul_ne_zero (B 0).specialDen (B 1).specialDen
  have hmonic : (movingProduct D).Monic :=
    (movingBlock_degree hh D 0).monic.mul (movingBlock_degree hh D 1).monic
  obtain ⟨G, hG⟩ := balanced_simple_poles hh hp D (liftAt genericPoint num den) (by
    intro i α hr hb
    dsimp only [num, den]
    rw [liftAt_add _ _ _ _ _ (generic_den (B 0).specialDen) (generic_den (B 1).specialDen)]
    simpa only [Fin.sum_univ_two] using generic_centre B i α hr hb)
  refine ⟨⟨movingProduct D, num, den, hmonic, ?_, hden, ?_, generic_den hden, G⟩, hG⟩
  · rw [movingProduct, Polynomial.map_mul, movingBlock_spec, movingBlock_spec, poleProduct]
  · dsimp only [num, den]
    rw [liftAt_add _ _ _ _ _ (B 0).specialDen (B 1).specialDen,
      (B 0).specialLift, (B 1).specialLift, crtPolynomial, Fin.sum_univ_two]

#print axioms balanced_deformation

end
end KoalaRectPole
