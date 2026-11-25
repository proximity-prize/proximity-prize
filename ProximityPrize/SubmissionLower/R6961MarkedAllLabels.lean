import ProximityPrize.SubmissionLower.R6961MarkedScalarPlace
import ProximityPrize.SubmissionLower.R6961MonicChartProbes
import ProximityPrize.SubmissionLower.R6961MarkedActualCount

set_option Elab.async false

-- merged module R6961MarkedEvaluationEndpoint
section Merged_R6961MarkedEvaluationEndpoint

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open K1 (K p)
open K1_14 (L liftPoly Equation)
open Lower6961.RescueGeometry (Model Family)
open RetainedShortening (Word)
open KoalaRect (axisDegree)
open RetainedCompression
open RetainedLinear (GeometricallyLinear)
open scoped Polynomial

def NonlinearPrice (B : MarkedBand) : Prop :=
  ∀ {u deleted} {M:Model u deleted} {Γ} (F:Family M Γ) (T:Finset K), T⊆Γ →
    Word 179798 B.wordDegree M.word F.scalar T →
    ∀ f:Curve (Polynomial L), Irreducible f → 3≤f.degreeOf ordinate → f.degreeOf ordinate<B.maxOrd →
      0<f.degreeOf parameter → height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree →
      ¬GeometricallyLinear (view f) →
      (∀ γ∈T, MarkedFiber (view f) (scalar M γ) (liftPoly (F.scalar γ))) →
      T.card≤rate (f.degreeOf ordinate)*f.degreeOf parameter+(f.degreeOf ordinate-1)*f.degreeOf ordinate

theorem rate_monotone : Monotone rate := by
  intro e n en
  exact Nat.sub_le_sub_right (Nat.add_le_add
    (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 9 en) _) (Nat.sub_le_sub_right en 1))
    (Nat.mul_le_mul_left 2 en)) 1

theorem proper_rate (e : ℕ) (he : 3 ≤ e) : 12 * e ≤ rate e := by
  unfold rate
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
  have h1 : (9 * (3 + k) + 2) * (3 + k - 1) + 2 * (3 + k) = 9 * k ^ 2 + 49 * k + 64 := by
    have : 3 + k - 1 = 2 + k := by omega
    rw [this]; ring
  omega

theorem retained_of_nonlinear (B : MarkedBand) (price : NonlinearPrice B)
    (hMax axesCap retainedCap : ℕ) (witnessBound : ℕ → ℕ)
    (haxesSmall : axesCap < p) (hdegFit : 131071 + hMax ≤ B.wordDegree)
    (paid : ∀ e a b, 3≤e → e<B.maxOrd → a+b≤axesCap → b<witnessBound e →
      rate e*(a+p*b)+(e-1)*e≤retainedCap)
    {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat ≤ hMax) (T : Finset K) (f : Equation) (sub : T⊆Γ)
    (emin : 3≤f.natDegree) (emax : f.natDegree<B.maxOrd)
    (axes : axisDegree f 0+axisDegree f 1≤axesCap)
    (graded : ∀ j : Fin 2, axisDegree f j < witnessBound f.natDegree)
    (marks : ∀ γ∈T, simpleSheet f (M.label γ) (F.scalar γ)) :
    T.card ≤ retainedCap := by
  apply retained_of_tariff B hMax axesCap retainedCap witnessBound haxesSmall hdegFit
    rate rate_monotone (by decide) (fun e he _ => proper_rate e he) paid _ F hi T f sub emin emax axes graded marks
  intro u deleted M Γ F T sub words f ir lo hi sv cap marks'
  by_cases g : GeometricallyLinear (view f)
  · have irr : Irreducible (view f) := (MulEquiv.irreducible_iff view).mpr ir
    have pos : 0<(view f).natDegree := by rw [view_y]; omega
    have pure := RetainedLinear.pure_of_geometrically_linear M.word (view f) irr pos g
    have bound := pure_node_price B words (scalar M) (scalar_injective M).injOn (view f) irr pos pure marks'
    rw [view_z] at bound
    exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_right _ ((by decide : 18≤rate 3).trans (rate_monotone lo)))
      (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))))
  · exact price F T sub words f ir lo hi sv cap g marks'

end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedEvaluationEndpoint

-- merged module R6961MarkedAllLabels
section Merged_R6961MarkedAllLabels
set_option synthInstance.maxHeartbeats 200000

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open K1_14 (L)
open Lower6961.MonicChart (ChartField Scalar)
open RetainedTwistedRestriction RetainedSurfaceClass Lower6960.CollisionMarked Lower6961.CollisionMarked Lower6960.NormalizedFiber Polynomial Finset Module Submodule
open scoped Polynomial BigOperators Lower6961.MarkedEvaluation Lower6961.RetainedSurfaceClass
variable {E:Type} [Field E] [Algebra ChartField E] [FiniteDimensional ChartField E] [Algebra.IsSeparable ChartField E]

/-- Reinsert every marked parameter, including zero and all reciprocal
boundary exceptions. They are roots of a single polynomial of degree at
most 2t+1. -/
theorem all_labels [DecidableEq L] (p:ℕ) [CharP L p] [CharP Scalar p] (P:CurvatureSquares.Ordinate)
    (pn:Lower6961.CollisionMarked.projectedRaw P≠0) (lo:3≤P.natDegree) (hi:P.natDegree<p) (v:ℕ) (vp:0<v)
    (b:PowerBasis ChartField E) (dim:b.dim=P.natDegree)
    (root:let : Algebra (Plane L) E:=Lower6961.CollisionMarked.axisPlaneAlgebra false; aeval b.gen (Lower6961.CollisionMarked.projectedRaw P)=0)
    (s t:ℕ) (positive:0<s) (tame:2*s<p) (tariff:t≤(P.natDegree-1)*v) (surface:Budget E (s-1) (s+s*t))
    (δf δi:Plane L) (nf:δf≠0) (ni:δi≠0)
    (df:Lower6961.CollisionMarked.axisDiscriminant (E:=E) false=Ideal.span {δf}) (di:Lower6961.CollisionMarked.axisDiscriminant (E:=E) true=Ideal.span {δi})
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
end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedAllLabels
