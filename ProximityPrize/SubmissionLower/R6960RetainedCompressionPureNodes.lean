import ProximityPrize.SubmissionLower.R6960RetainedCompressionReduction

set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 2000000

namespace Lower6960.RetainedCompression
noncomputable section
open Polynomial Finset
open K1 (K I node)
open K1_14 (L liftPoly)
open CurvatureSquares (Ordinate zView coeff_caps)
open RetainedShortening (Word)
open RescueGeometry (Model Family)
open scoped Polynomial
open private rate_mono from ProximityPrize.SubmissionLower.R6960RetainedCompressionReduction
open private CurvatureSquares.node_eval CurvatureSquares.node_height CurvatureSquares.node_ne
  CurvatureSquares.root_count from ProximityPrize.SubmissionLower.R6960QuadraticProjection

private abbrev embed := algebraMap K L

def atNode (P : Ordinate) (i : I) : Polynomial (Polynomial L) :=
  P.map (evalRingHom (C (embed (node i))))

/-- A received value that is a generic root at a physical node is the only
generic ordinate there, counted with the full multiplicity. -/
def PureNodes (w : I → K) (P : Ordinate) : Prop :=
  ∀ i, (atNode P i).eval (C (embed (w i))) = 0 →
    atNode P i = C (atNode P i).leadingCoeff * (Polynomial.X-C (C (embed (w i))))^P.natDegree

private theorem node_coefficient (P : Ordinate) (i : I) (j : ℕ) :
    ((atNode P i).coeff j).natDegree≤(zView P).natDegree := by
  rw [atNode,coeff_map,coe_evalRingHom]
  exact (CurvatureSquares.node_height ..).trans (coeff_caps P j).2

private theorem root_at_node {P : Ordinate} {z : L} {S : K[X]}
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

theorem pure_node_price {w s T} (W : Word 179827 wordDegree w s T)
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

/-- Only factors with a physical received fibre that is not pure require the
remaining bounded-weight count. -/
def NonPureFactorPrice : Prop :=
  ∀ {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) (T : Finset K), T⊆Γ →
    Word 179827 wordDegree M.word F.scalar T →
    ∀ f : Curve L[X], Irreducible f →
      3≤f.degreeOf ordinate → f.degreeOf ordinate<48 → 0<f.degreeOf parameter →
      height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree →
      ¬PureNodes M.word (view f) →
      (∀ γ∈T, MarkedFiber (view f) (scalar M γ) (liftPoly (F.scalar γ))) →
      T.card≤MarkedSheet.rate (f.degreeOf ordinate)*(f.degreeOf parameter)+
        (f.degreeOf ordinate-1)*(f.degreeOf ordinate)

theorem bounded_of_nonpure (other : NonPureFactorPrice) : BoundedFactorPrice := by
  intro u deleted M Γ F T sub W f irr lo hi sv cap marks
  by_cases pure : PureNodes M.word (view f)
  · let P := view f
    have ir : Irreducible P := (MulEquiv.irreducible_iff view).mpr irr
    have positive : 0<P.natDegree := by change 0<(view f).natDegree; rw [view_y]; omega
    have fee := pure_node_price W (scalar M) (scalar_injective M).injOn P ir positive pure marks
    change _≤18*(zView (view f)).natDegree+1 at fee
    rw [view_z] at fee
    have rate : 18≤MarkedSheet.rate (f.degreeOf ordinate) := (by decide :
      18≤MarkedSheet.rate 3).trans (rate_mono lo)
    have additive : 1≤(f.degreeOf ordinate-1)*(f.degreeOf ordinate) :=
      Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
    exact fee.trans (Nat.add_le_add (Nat.mul_le_mul_right _ rate) additive)
  · exact other F T sub W f irr lo hi sv cap pure marks

theorem retained_of_nonpure (other : NonPureFactorPrice) : RetainedCount :=
  retained_of_bounded (bounded_of_nonpure other)

#print axioms pure_node_price
#print axioms retained_of_nonpure
end
end Lower6960.RetainedCompression
