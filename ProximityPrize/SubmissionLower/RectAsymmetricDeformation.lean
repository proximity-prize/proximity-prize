import ProximityPrize.SubmissionLower.Rect51PoleWindowLocal

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 1000000

namespace RectAsymmetric
noncomputable section

open Polynomial
open K1_14 (L)
open K1_14_1 K1_14_1_7 K1_14_1_7_3
open scoped BigOperators Polynomial
open private other_eval_ne_zero deriv_eval_ne_zero constant_eval_ne_zero
  generic_den generic_centre from ProximityPrize.SubmissionLower.Fast065

/-- A pole enumeration with exactly the same number of roots in each seed. -/
def Balanced {F : Type} [Field F] {h : ℕ} {H : F[X]} {lift : (SeedFrac F)[X]}
    (G : SimplePoles h H lift) : Prop :=
  ∀ f : Fin 2 → ℕ, (∑ t, f (G.side t)) = h * f 0 + h * f 1

private theorem balanced_poles {h : ℕ} (hh : 0 < h) (hp : h < K1.p) (D : PoleData h)
    (lift : (SeedFrac GenericField)[X])
    (hcentre : ∀ i α, (genericBlock D i).eval α = 0 →
      ((D.constant i).map constGeneric).eval α ≠ 0 →
      lift.eval (algebraMap GenericField (SeedFrac GenericField) α) =
        residue i (-((D.offset i).map constGeneric).eval α)
          (((D.constant i).map constGeneric).eval α) (((D.slope i).map constGeneric).eval α)) :
    ∃ G : SimplePoles h ((movingProduct D).map genericPoint) lift, Balanced G := by
  classical
  let H := (movingProduct D).map genericPoint
  let P := genericBlock D
  have blocks : H = P 0 * P 1 := by simp only [H, P, movingProduct, Polynomial.map_mul]
  have hmonic (i : Fin 2) : (P i).Monic := (movingBlock_degree hh D i).monic.map _
  have hdegree (i : Fin 2) : (P i).natDegree = h :=
    ((movingBlock_degree hh D i).monic.natDegree_map _).trans (movingBlock_degree hh D i).natDegree_eq
  have sep (i : Fin 2) : (P i).Separable := by
    apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed GenericField GenericField (P i) (P i).derivative).mpr
    intro α
    by_cases he : (P i).eval α = 0
    · exact Or.inr (by
        change (P i).derivative.eval α ≠ 0
        exact deriv_eval_ne_zero hh hp D i he)
    · exact Or.inl (by simpa using he)
  let S (i : Fin 2) := (P i).roots.toFinset
  have hcard (i : Fin 2) : Fintype.card (S i) = h := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (nodup_roots (sep i)),
      ← (IsAlgClosed.splits (P i)).natDegree_eq_card_roots, hdegree]
  let e (i : Fin 2) : Fin h ≃ S i := (Fintype.equivFinOfCardEq (hcard i)).symm
  let pair : Fin (2*h) ≃ Fin 2 × Fin h := finProdFinEquiv.symm
  let side (t : Fin (2*h)) := (pair t).1
  let α (t : Fin (2*h)) : GenericField := (e (side t) (pair t).2).val
  have hroot (t : Fin (2*h)) : (P (side t)).eval (α t) = 0 :=
    (mem_roots (hmonic _).ne_zero).mp (Multiset.mem_toFinset.mp (e (side t) (pair t).2).property)
  have hdiff (t : Fin (2*h)) : (P (otherBlock (side t))).eval (α t) ≠ 0 :=
    other_eval_ne_zero hh D _ (hroot t)
  have inj : Function.Injective α := by
    intro t j hj
    by_cases hs : side t = side j
    · apply pair.injective
      apply Prod.ext hs
      apply (e (side t)).injective
      apply Subtype.ext
      change (e (side t) (pair t).2).val = (e (side j) (pair j).2).val at hj
      rw [← hs] at hj
      exact hj
    · have he : side j = otherBlock (side t) := by
        have aux (a b : Fin 2) (hn : a ≠ b) : b = otherBlock a := by
          fin_cases a <;> fin_cases b <;> simp_all [otherBlock]
        exact aux _ _ hs
      have h := hroot j
      rw [he, ← hj] at h
      exact False.elim (hdiff t h)
  have factor (i : Fin 2) : (∏ k : Fin h, (Polynomial.X - C (e i k).val)) = P i := by
    rw [(e i).prod_comp (fun x => Polynomial.X - C x.val),
      Finset.prod_coe_sort (S i) (fun x => Polynomial.X - C x)]
    have hS : (S i).val = (P i).roots :=
      (Multiset.toFinset_val _).trans (nodup_roots (sep i)).dedup
    simpa only [Finset.prod, hS] using ((IsAlgClosed.splits (P i)).eq_prod_roots_of_monic (hmonic i)).symm
  have side_cases (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have rootH (t : Fin (2*h)) : H.eval (α t) = 0 := by
    have hr := hroot t
    rw [blocks, eval_mul, mul_eq_zero]
    rcases side_cases (side t) with h | h
    · exact Or.inl (h ▸ hr)
    · exact Or.inr (h ▸ hr)
  have simpleH (t : Fin (2*h)) : H.derivative.eval (α t) ≠ 0 := by
    have hr := hroot t
    have hd := hdiff t
    have hn : (P (side t)).derivative.eval (α t) ≠ 0 := deriv_eval_ne_zero hh hp D _ hr
    rw [blocks, derivative_mul, eval_add, eval_mul, eval_mul]
    rcases side_cases (side t) with h | h
    · rw [h] at hr hd hn
      change (P 1).eval (α t) ≠ 0 at hd
      rw [hr, zero_mul, add_zero]
      exact mul_ne_zero hn hd
    · rw [h] at hr hd hn
      change (P 0).eval (α t) ≠ 0 at hd
      rw [hr, mul_zero, zero_add]
      exact mul_ne_zero hd hn
  refine ⟨⟨α, side, _, _, _, inj, ?_, rootH, simpleH,
    fun t => constant_eval_ne_zero hh D _ (hroot t),
    fun t => hcentre _ _ (hroot t) (constant_eval_ne_zero hh D _ (hroot t))⟩, ?_⟩
  · change H = ∏ t, (Polynomial.X - C (e (pair t).1 (pair t).2).val)
    rw [blocks, pair.prod_comp (fun k : Fin 2 × Fin h => Polynomial.X - C (e k.1 k.2).val),
      Fintype.prod_prod_type, Fin.prod_univ_two]
    change P 0 * P 1 = (∏ k : Fin h, (Polynomial.X - C (e 0 k).val)) *
      ∏ k : Fin h, (Polynomial.X - C (e 1 k).val)
    rw [factor, factor]
  · intro f
    change (∑ t, f (pair t).1) = _
    rw [pair.sum_comp (fun k : Fin 2 × Fin h => f k.1), Fintype.sum_prod_type, Fin.sum_univ_two]
    simp

/-- The original CRT deformation with an explicit balanced enumeration of its poles. -/
theorem regular_deformation {h : ℕ} (hh : 0 < h) (hp : h < K1.p)
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
  obtain ⟨G, hG⟩ := balanced_poles hh hp D (liftAt genericPoint num den) (by
    intro i α hr hb
    dsimp only [num, den]
    rw [liftAt_add _ _ _ _ _ (generic_den (B 0).specialDen) (generic_den (B 1).specialDen)]
    simpa only [Fin.sum_univ_two] using generic_centre B i α hr hb)
  refine ⟨⟨movingProduct D, num, den, hmonic, ?_, hden, ?_, generic_den hden, G⟩, hG⟩
  · rw [movingProduct, Polynomial.map_mul, movingBlock_spec, movingBlock_spec, poleProduct]
  · dsimp only [num, den]
    rw [liftAt_add _ _ _ _ _ (B 0).specialDen (B 1).specialDen,
      (B 0).specialLift, (B 1).specialLift, crtPolynomial, Fin.sum_univ_two]

#print axioms regular_deformation
end
end RectAsymmetric
