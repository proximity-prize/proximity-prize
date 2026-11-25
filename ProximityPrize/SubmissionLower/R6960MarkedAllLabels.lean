import ProximityPrize.SubmissionLower.R6960MarkedEvaluationLedger
import ProximityPrize.SubmissionLower.R6960MonicChartActual
import ProximityPrize.SubmissionLower.R6960MarkedActualCount

-- merged module R6960MarkedEvaluationEndpoint
section Merged_R6960MarkedEvaluationEndpoint

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open K1 (K)
open K1_14 (L liftPoly)
open RescueGeometry (Model Family)
open RetainedShortening (Word)
open RetainedCompression
open RetainedLinear (GeometricallyLinear)
open scoped Polynomial

/-- Only the nonlinear marked factors of the actual high family need the
single-determinant estimate. Works uniformly for both high-side bands. -/
def NonlinearPrice : Prop :=
  ∀ (degD : ℕ), 0<degD → degD<179808 →
    ∀ {u deleted} {M:Model u deleted} {Γ} (F:Family M Γ) (T:Finset K), T⊆Γ →
      Word 179808 degD M.word F.scalar T →
      ∀ f:Curve (Polynomial L),Irreducible f → 3≤f.degreeOf ordinate →
        TameBand (f.degreeOf ordinate) degD →
        0<f.degreeOf parameter → height degD f≤heightCap (f.degreeOf ordinate) degD →
        ¬GeometricallyLinear (view f) →
        (∀ γ∈T,MarkedFiber (view f) (scalar M γ) (liftPoly (F.scalar γ))) →
        T.card≤rate (f.degreeOf ordinate)*f.degreeOf parameter+(f.degreeOf ordinate-1)*f.degreeOf ordinate

theorem rate_monotone : Monotone rate := by
  intro e n en
  exact Nat.sub_le_sub_right (Nat.add_le_add
    (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 9 en) _) (Nat.sub_le_sub_right en 1))
    (Nat.mul_le_mul_left 2 en)) 1

theorem rate_proper (e : ℕ) (he : 3 ≤ e) (hi : e < 64) : 14 * e ≤ rate e :=
  (by decide +kernel : ∀ i : Fin 64, 3 ≤ i.val → 14 * i.val ≤ rate i.val) ⟨e, hi⟩ he

theorem factor_price_of_nonlinear (price : NonlinearPrice) : FactorPriceAt rate := by
  intro degD hd0 hdA u deleted M Γ F T sub words f ir lo hi sv cap marks
  by_cases g : GeometricallyLinear (view f)
  · have irr : Irreducible (view f) := (MulEquiv.irreducible_iff view).mpr ir
    have pos : 0<(view f).natDegree := by rw [view_y]; omega
    have pure := RetainedLinear.pure_of_geometrically_linear M.word (view f) irr pos g
    have hvote : CurvatureVotes.VoteScale 179808 degD 18 := by
      apply Or.inl
      have hle : degD ≤ 164670 := by rcases hi with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
      omega
    have bound := pure_node_price words hdA hvote (scalar M) (scalar_injective M).injOn (view f) irr pos pure marks
    rw [view_z] at bound
    exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_right _ ((by decide : 18≤rate 3).trans (rate_monotone lo)))
      (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))))
  · exact price degD hd0 hdA F T sub words f ir lo hi sv cap g marks

theorem band2_high_count (price : NonlinearPrice)
    {u deleted} (M : Model u deleted) {Γ} (F : Family M Γ)
    (lo : 2383 ≤ M.overhead) (hi : M.overhead ≤ 33599) :
    Γ.card ≤ 265963255385514628 :=
  high_count_of_retained
    (retained_of_tariff rate rate_monotone (by decide) rate_proper budget (factor_price_of_nonlinear price))
    M F lo hi

#print axioms factor_price_of_nonlinear
#print axioms band2_high_count
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedEvaluationEndpoint

-- merged module R6960MarkedAllLabels
section Merged_R6960MarkedAllLabels
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open K1_14 (L)
open MonicChart (ChartField Scalar)
open RetainedTwistedRestriction RetainedSurfaceClass CollisionMarked NormalizedFiber Polynomial Finset Module Submodule
open scoped Polynomial BigOperators Lower6960.MarkedEvaluation Lower6960.RetainedSurfaceClass
variable {E:Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]

/-- Reinsert every marked parameter, including zero and all reciprocal
boundary exceptions. They are roots of a single polynomial of degree at
most 2t+1. -/
theorem all_labels [DecidableEq L] (p:ℕ) [CharP L p] [CharP Scalar p] (P:CurvatureSquares.Ordinate)
    (pn:projectedRaw P≠0) (lo:3≤P.natDegree) (hi:P.natDegree<p) (v:ℕ) (vp:0<v)
    (b:PowerBasis ChartField E) (dim:b.dim=P.natDegree)
    (root:let : Algebra (Plane L) E:=axisPlaneAlgebra false; aeval b.gen (projectedRaw P)=0)
    (s t:ℕ) (positive:0<s) (tame:2*s<p) (tariff:t≤(P.natDegree-1)*v) (surface:Budget E (s-1) (s+s*t))
    (δf δi:Plane L) (nf:δf≠0) (ni:δi≠0)
    (df:axisDiscriminant (E:=E) false=Ideal.span {δf}) (di:axisDiscriminant (E:=E) true=Ideal.span {δi})
    (xc:CurvatureSquares.height δf≤2*s) (zc:δf.natDegree≤2*t) (tail:((Bivariate.swap δi).trailingCoeff).natDegree≤2*t)
    (S:Finset L) (word:L → Polynomial L) (mark:∀z∈S,RetainedCompression.MarkedFiber P z (word z))
    (vertical:∀(U:Finset L)(m:ℕ)(v:Fin m→E),(∀j,controlled E (s-1) U (v j))→
      finrank Scalar (span Scalar (Set.range v))+s≤P.natDegree*s) :
    S.card≤rate P.natDegree*v+(P.natDegree-1)*P.natDegree := by
  classical
  let B:=(Bivariate.swap δi).trailingCoeff
  have bn:B≠0 := trailingCoeff_nonzero_iff_nonzero.mpr ((map_ne_zero_iff _ Bivariate.swap.injective).mpr ni)
  let D:=(Polynomial.X:(Polynomial L))*B
  have dn:D≠0:=mul_ne_zero Polynomial.X_ne_zero bn
  let bad:=D.roots.toFinset
  let U:=S\bad
  have valid (z:L) (hz:z∈U) : z≠0 ∧ B.eval z≠0 := by
    have no:= (Finset.mem_sdiff.mp hz).2
    have noeval:D.eval z≠0:=fun h=>no (Multiset.mem_toFinset.mpr ((mem_roots dn).mpr h))
    rw [show D=Polynomial.X*B from rfl,eval_mul,eval_X] at noeval
    exact mul_ne_zero_iff.mp noeval
  have good:=actual_good_count (E:=E) p P pn (by omega) hi b dim root s t positive tame surface δf δi nf ni df di xc zc U
    (fun z hz=>(valid z hz).1) word (fun z hz=>mark z (Finset.mem_sdiff.mp hz).1)
    (fun z hz=>(valid z hz).2) (vertical U)
  have exceptions:bad.card≤1+2*t :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans (by
      rw [show D=Polynomial.X*B from rfl,natDegree_mul Polynomial.X_ne_zero bn,natDegree_X]
      exact Nat.add_le_add_left tail 1))
  have combined : S.card≤9*P.natDegree*t+P.natDegree*(P.natDegree-1)+(1+2*t) :=
    Finset.card_le_card_sdiff_add_card.trans (Nat.add_le_add good exceptions)
  let e:=P.natDegree
  have base:1≤(2*e-1)*v:=Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by dsimp [e];omega) vp.ne')
  have rate_eq:rate e=(9*e+2)*(e-1)+(2*e-1) := by unfold rate;omega
  have charge:9*e*t+e*(e-1)+(1+2*t)=(9*e+2)*t+1+(e-1)*e := by ring
  change S.card≤rate e*v+(e-1)*e
  change S.card≤9*e*t+e*(e-1)+(1+2*t) at combined
  rw [charge] at combined
  rw [rate_eq,Nat.add_mul,Nat.mul_assoc]
  exact combined.trans (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left _ tariff) base) _)

#print axioms all_labels
end Lower6960.MarkedEvaluation

end
end Merged_R6960MarkedAllLabels
