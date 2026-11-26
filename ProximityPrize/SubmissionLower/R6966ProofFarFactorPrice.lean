import ProximityPrize.SubmissionLower.R6966ProofFarNonlinear
import ProximityPrize.SubmissionLower.R6966ProofFarPure

set_option Elab.async false

namespace Research6966.FarFactorPrice
open Polynomial Finset
open K1 (K I p)
open K1_14 (L liftPoly)
open Lower6960
open RetainedShortening (Word)
open RetainedCompression (Curve ordinate parameter view view_y view_z
  MarkedFiber no_zero_degree constant_price specialize height heightCap evaluate_view evaluate
  escape proper_cut_price aggregate box_iff abscissa_le_height pure_node_price_far)
open RetainedLinear (GeometricallyLinear)
open CurvatureSquares (Ordinate zView xView ordEval)
open scoped Polynomial
set_option maxRecDepth 15000
set_option maxHeartbeats 2500000

abbrev agreement : ℕ := 179769
abbrev wordDegree : ℕ := 164748
abbrev rate := MarkedEvaluation.rate

theorem rate_mono : Monotone rate := by
  intro e n le
  unfold rate MarkedEvaluation.rate
  exact Nat.sub_le_sub_right (Nat.add_le_add
    (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 9 le) _) (Nat.sub_le_sub_right le 1))
    (Nat.mul_le_mul_left 2 le)) 1

private theorem vote_scale : CurvatureVotes.VoteScale agreement wordDegree 18 :=
  Or.inl (by decide +kernel)

private theorem word_roots {U : Finset K} (s : K → K[X]) (label : K → L) (Q : Ordinate)
    (H : ∀ γ∈U, MarkedFiber Q (label γ) (liftPoly (s γ))) :
    ∀ γ∈U, ordEval (label γ) ((s γ).map (algebraMap K L)) Q=0 := by
  intro γ hγ
  change Q.eval₂ (mapRingHom (evalRingHom (label γ))) (liftPoly (s γ))=0
  rw [← eval_map]
  exact (H γ hγ).root

theorem factor {w : I → K} {s : K → K[X]} {T : Finset K}
    (words : Word agreement wordDegree w s T) (label : K → L) (inject : Function.Injective label)
    {Q : Ordinate} (ir : Irreducible Q) (n : ℕ) (lo : 3≤n) (hi : n<48)
    (degree : Q.natDegree≤n) (mark : ∀ γ∈T, MarkedFiber Q (label γ) (liftPoly (s γ))) :
    T.card≤rate n*(zView Q).natDegree+(n-1)*Q.natDegree := by
  classical
  rcases T.eq_empty_or_nonempty with empty | ⟨γ,hγ⟩
  · simp [empty]
  let q := view.symm Q
  let e := Q.natDegree
  let v := (zView Q).natDegree
  have qp : Irreducible q := (MulEquiv.irreducible_iff view.symm).mpr ir
  have y : q.degreeOf ordinate=e := by rw [← view_y, RingEquiv.apply_symm_apply]
  have z : q.degreeOf parameter=v := by rw [← view_z, RingEquiv.apply_symm_apply]
  have pos : 0<e := no_zero_degree (mark γ hγ)
  have tRate : 24≤rate n := (by decide : 24≤rate 3).trans (rate_mono lo)
  have vRate : 18≤rate n := (by decide : 18≤24).trans tRate
  have budget : e≤(n-1)*e := Nat.le_mul_of_pos_left _ (by omega)
  have inj : Set.InjOn label (T : Set K) := inject.injOn
  by_cases hv : v=0
  · have Sinj : Set.InjOn (fun x=>liftPoly (s x)) (T:Set K) :=
      (Polynomial.map_injective _ (algebraMap K L).injective).comp_injOn words.distinct
    exact (constant_price Q T label (fun x=>liftPoly (s x)) Sinj hv mark).trans
      (budget.trans (Nat.le_add_left ..))
  have roots := word_roots s label Q mark
  by_cases linear : e=1
  · have count := CurvatureSquares.irreducible_linear_node words (algebraMap K L) label inj
      (by decide) vote_scale Q ir linear roots
    exact count.trans (Nat.add_le_add (Nat.mul_le_mul_right _ vRate) (pos.trans_le budget))
  have el : 2≤e := by omega
  by_cases tall : heightCap e wordDegree < height wordDegree q
  · let param (j : T) := label j.val
    let root (j : T) := liftPoly (s j.val)
    have deg (j : T) : (root j).natDegree≤wordDegree := by
      simpa only [root,liftPoly,natDegree_map_eq_of_injective (algebraMap K L).injective]
        using words.degree j.val j.property
    have rootsF (j : T) : evaluate (param j) (root j) q=0 := by
      rw [evaluate_view,RingEquiv.apply_symm_apply]
      exact (mark j.val j.property).root
    obtain ⟨G,_,nondiv,box,_,rootsG⟩ :=
      escape param root wordDegree (by decide) deg q qp.ne_zero el y z rootsF tall
    have ⟨gy,gz⟩ := (box_iff _ _ _).mp box
    have price := proper_cut_price T label (fun j=>liftPoly (s j))
      inj q G qp nondiv pos y z gy gz (fun j hj=>rootsF ⟨j,hj⟩)
      (fun j hj=>rootsG ⟨j,hj⟩)
    have ceiling : 12*e≤rate n := by
      by_cases two : e=2
      · simpa only [two] using tRate
      have three : 3≤e := by omega
      have ratio : 12*e≤rate e :=
        (by decide +kernel : ∀ i : Fin 48, 3 ≤ i.val → 12*i.val ≤ rate i.val)
          ⟨_,degree.trans_lt hi⟩ three
      exact ratio.trans (rate_mono degree)
    exact (price.trans (Nat.mul_le_mul_right _ ceiling)).trans (Nat.le_add_right ..)
  · have wt := Nat.le_of_not_gt tall
    by_cases two : e=2
    · have D : 2*(xView Q).natDegree<p := by
        have a := abscissa_le_height q wordDegree
        rw [RingEquiv.apply_symm_apply] at a
        exact (Nat.mul_le_mul_left 2 (a.trans wt)).trans_lt (by rw [two]; decide)
      have count := CurvatureSquares.degree_two_count words (algebraMap K L) label inj
        (by decide) vote_scale Q ir two D roots
      have add : 2≤(n-1)*e := el.trans budget
      exact count.trans (Nat.add_le_add
        (Nat.mul_le_mul_right _ (show max 8 18≤rate n from vRate)) add)
    have three : 3≤q.degreeOf ordinate := by rw [y]; omega
    have mark' (j : K) (hj : j ∈ T) : MarkedFiber (view q) (label j) (liftPoly (s j)) := by
      simpa only [q,RingEquiv.apply_symm_apply] using mark j hj
    have charge : T.card≤rate (q.degreeOf ordinate)*(q.degreeOf parameter)+
        (q.degreeOf ordinate-1)*q.degreeOf ordinate := by
      by_cases pure : GeometricallyLinear (view q)
      · have irr : Irreducible (view q) := (MulEquiv.irreducible_iff view).mpr qp
        have pos' : 0<(view q).natDegree := by rw [view_y];omega
        have nodes := RetainedLinear.pure_of_geometrically_linear w (view q) irr pos' pure
        have bound := pure_node_price_far words label inj (view q) irr pos' nodes mark'
        rw [view_z] at bound
        exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_right _ ((by decide : 18≤rate 3).trans (rate_mono three)))
          (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))))
      · exact MarkedEvaluation.nonlinear_far T label inject (fun j=>liftPoly (s j)) q qp three
          (y.symm ▸ degree.trans_lt hi) (Nat.pos_of_ne_zero (z.symm ▸ hv)) (y.symm ▸ wt) pure mark'
    rw [y,z] at charge
    exact charge.trans (Nat.add_le_add (Nat.mul_le_mul_right _ (rate_mono degree))
      (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right degree 1)))

/-- The factored tariff for any integral retained ordinate, with no
dependency on how the marks or the integral equation were produced. -/
theorem price {w : I → K} {s : K → K[X]} {T : Finset K}
    (words : Word agreement wordDegree w s T) (label : K → L) (inject : Function.Injective label)
    (P : Ordinate) (pn : P≠0) (n B : ℕ) (lo : 3≤n) (hi : n<48)
    (degree : P.natDegree≤n) (bound : (zView P).natDegree≤B)
    (marks : ∀ γ∈T, MarkedFiber P (label γ) (liftPoly (s γ))) :
    T.card≤rate n*B+(n-1)*P.natDegree := by
  have chosen := aggregate P T label (fun j=>liftPoly (s j)) (rate n) (n-1) pn marks (by
    intro Q ir dvd U sub mark
    have W : Word agreement wordDegree w s U :=
      ⟨words.distinct.mono sub,fun j hj=>words.degree j (sub hj),fun j hj=>words.hits j (sub hj)⟩
    exact factor W label inject ir n lo hi ((natDegree_le_of_dvd dvd pn).trans degree) mark)
  exact chosen.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ bound) _)

end Research6966.FarFactorPrice
