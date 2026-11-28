import ProximityPrize.SubmissionLower.R6960RetainedCompressionPureNodes

set_option Elab.async false

-- Source: Research6969.FarPure
set_option autoImplicit true
set_option Elab.async false
namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Finset
open K1 (K I node)
open K1_14 (L liftPoly)
open CurvatureSquares (Ordinate zView coeff_caps)
open RetainedShortening (Word)
open RescueGeometry (Model Family)
open scoped Polynomial

open CurvatureSquares (node_eval node_height node_ne root_count)
private abbrev embed := algebraMap K L
private theorem node_coefficient (P : Ordinate) (i : I) (j : ℕ) :
    ((atNode P i).coeff j).natDegree≤(zView P).natDegree := by
  rw [atNode,coeff_map,coe_evalRingHom]
  exact (CurvatureSquares.node_height ..).trans (coeff_caps P j).2
private theorem root_at_node {P : Ordinate} {z : L} {S : (Polynomial K)}
    (mark : MarkedFiber P z (liftPoly S)) (i : I) :
    ((atNode P i).map (evalRingHom z)).eval (embed (S.eval (node i)))=0 := by
  let x := embed (node i)
  have commute : (specialize P z).map (evalRingHom x)=(atNode P i).map (evalRingHom z) := by
    apply Polynomial.ext
    intro n
    simp only [specialize,atNode,x,coeff_map,coe_mapRingHom,coe_evalRingHom]
    exact (CurvatureSquares.node_eval (P.coeff n) (embed (node i)) z).symm
  have value : (liftPoly S).eval x=embed (S.eval (node i)) := by
    rw [liftPoly,show x=embed (node i) from rfl,Polynomial.eval_map_apply]
  have h := congrArg (Polynomial.eval x) mark.root
  have eq := Polynomial.eval_map_apply (f:=evalRingHom x)
    (p:=specialize P z) (x:=liftPoly S)
  rw [commute,coe_evalRingHom,value] at eq
  exact eq.trans (h.trans eval_zero)
theorem pure_node_price_6970 {w s T} (W : Word 179730 164826 w s T)
    (z : K → L) (inj : Set.InjOn z (T:Set K)) (P : Ordinate) (irr : Irreducible P)
    (pos : 0<P.natDegree) (pure : PureNodes w P)
    (marks : ∀ γ∈T, MarkedFiber P (z γ) (liftPoly (s γ))) :
    T.card≤18*(zView P).natDegree+1 := by
  classical
  apply CurvatureVotes.minority_count W (by decide) (Or.inl (by decide))
  intro i
  let Q := atNode P i
  let a := Q.leadingCoeff
  let g := Q.eval (C (embed (w i)))
  have cn (j : ℕ) : (Q.coeff j).natDegree≤(zView P).natDegree := node_coefficient P i j
  have fits : g.natDegree≤(zView P).natDegree := by
    dsimp only [g]
    rw [eval_eq_sum,Polynomial.sum_def]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    rw [← C_pow]
    exact (natDegree_mul_C_le ..).trans (cn j)
  by_cases nonzero : g≠0
  · left
    apply (CurvatureSquares.root_count (inj.mono (filter_subset _ _)) g nonzero _).trans fits
    intro γ hγ
    obtain ⟨active,hit⟩ := mem_filter.mp hγ
    have hz := root_at_node (marks γ active) i
    have eq := Polynomial.eval_map_apply (f:=evalRingHom (z γ))
      (p:=Q) (x:=C (embed (w i)))
    rw [coe_evalRingHom,eval_C] at eq
    rw [hit] at hz
    exact eq.symm.trans hz
  · right
    have qn : Q≠0 := CurvatureSquares.node_ne P irr pos _
    have an : a≠0 := leadingCoeff_ne_zero.mpr qn
    apply (CurvatureSquares.root_count (inj.mono (filter_subset _ _)) a an _).trans
      (by simpa only [a,coeff_natDegree] using cn Q.natDegree)
    intro γ hγ
    obtain ⟨active,miss⟩ := mem_filter.mp hγ
    have hz := root_at_node (marks γ active) i
    have packed := pure i (not_ne_iff.mp nonzero)
    change Q=C a*(Polynomial.X-C (C (embed (w i))))^P.natDegree at packed
    change (Q.map (evalRingHom (z γ))).eval (embed ((s γ).eval (node i)))=0 at hz
    rw [packed,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_sub,
      Polynomial.map_X,Polynomial.map_C,eval_mul,eval_pow,eval_sub,eval_X,eval_C,
      eval_C,coe_evalRingHom,eval_C] at hz
    exact (mul_eq_zero.mp hz).resolve_right (pow_ne_zero _ (sub_ne_zero.mpr (embed.injective.ne miss)))

end
end Lower6960.RetainedCompression
