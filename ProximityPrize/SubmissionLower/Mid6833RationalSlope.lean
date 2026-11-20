/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. New cancellation at good nodes and the leading-coefficient count.
The scalar price used below is the frozen 69.69 research estimate. -/
import ProximityPrize.SubmissionLower.Mid6833GenuineActual
import ProximityPrize.SubmissionLower.Mid6833PolynomialSlope
import ProximityPrize.SubmissionLower.Mid6833QuotientList
import ProximityPrize.SubmissionLower.Mid6833GenuineTypes
namespace ProximityPrize.SubmissionLower.Genuine6969
open Polynomial Finset K6969Global Koala6831Comparison Koala6831BenchmarkPrimitive
open Koala6831BenchmarkField (prime)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 30000
variable {K : Type} [Field K]

/-- Cancel a common factor even at a node where the common factor vanishes,
by using the other active row and Frobenius compatibility. -/
theorem cancel_slope_at_node (s : K →+* K) (x v : K) (hx : s x=x)
    (a b L R G D J : K[X]) (nz : G≠0)
    (aa : a=G*D) (ll : L=G*J) (eq : a.map s * R = b * L.map s)
    (active : a.eval x≠0 ∨ b.eval x≠0)
    (left : a.eval x*v=L.eval x) (right : b.eval x*s v=R.eval x) :
    D.eval x*v=J.eval x := by
  rcases active with first|second
  · rw [aa,eval_mul] at first
    rw [aa,ll,eval_mul,eval_mul,mul_assoc] at left
    exact mul_left_cancel₀ (left_ne_zero_of_mul first) left
  have compat : D.map s * R=b*J.map s := by
    apply mul_left_cancel₀ (map_ne_zero (f:=s) nz)
    rw [aa,ll,Polynomial.map_mul,Polynomial.map_mul] at eq
    linear_combination eq
  have atx := congrArg (Polynomial.eval x) compat
  have dn := eval_map_apply (p:=D) s x
  have jn := eval_map_apply (p:=J) s x
  rw [hx] at dn jn
  simp only [eval_mul,dn,jn,←right] at atx
  apply s.injective
  rw [map_mul]
  apply mul_left_cancel₀ second
  linear_combination atx

/-- A degree overflow above both row products exposes one nonzero affine
linearized seed polynomial, whose ordinary degree is at most p. -/
theorem overflow_count (s : K →+* K) (p w : ℕ) (hp : 1<p) (power : ∀ g, s g=g^p)
    (a b B L R : K[X]) (ha : a≠0) (hb : b≠0)
    (compatible : a.map s*R=b*L.map s) (high : w+a.natDegree<L.natDegree)
    (E : Finset K) (P : K → K[X]) (degree : ∀g∈E,(P g).natDegree≤w)
    (row : ∀g∈E,a*P g+b*(P g).map s=B+C g*L+C (s g)*R) : E.card≤p := by
  have ln : L≠0 := fun eq => by simp [eq] at high
  have rn : R≠0 := fun eq => by simpa [eq,hb,ln] using compatible
  have heights := congrArg natDegree compatible
  rw [natDegree_mul (Polynomial.map_ne_zero ha) rn,natDegree_mul hb (Polynomial.map_ne_zero ln),
    natDegree_map_eq_of_injective s.injective,natDegree_map_eq_of_injective s.injective] at heights
  let k := max L.natDegree R.natDegree
  have bounds : w+a.natDegree<k ∧ w+b.natDegree<k := by dsimp [k]; omega
  let f : K[X] := C (B.coeff k) + C (L.coeff k)*(Polynomial.X : K[X]) + C (R.coeff k)*(Polynomial.X : K[X])^p
  have nonzero : f≠0 := by
    intro z
    have e₁ := congrArg (fun t : K[X] => t.coeff 1) z
    have ep := congrArg (fun t : K[X] => t.coeff p) z
    have p1 : p≠1 := by omega
    have p0 : p≠0 := by omega
    simp [f,coeff_C,coeff_X,coeff_X_pow,Ne.symm p1,p1,p0] at e₁ ep
    rcases le_total R.natDegree L.natDegree with hr|hl
    · have Lc : L.coeff k≠0 := by
        rw [show k=L.natDegree from max_eq_left hr]
        exact leadingCoeff_ne_zero.mpr ln
      exact Lc e₁
    · have Rc : R.coeff k≠0 := by
        rw [show k=R.natDegree from max_eq_right hl]
        exact leadingCoeff_ne_zero.mpr rn
      exact Rc ep
  have cap : f.natDegree≤p := by
    dsimp only [f]
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · simp
      · exact (natDegree_C_mul_le ..).trans (by simpa using hp.le)
    · exact (natDegree_C_mul_le ..).trans_eq (natDegree_X_pow p)
  by_contra! excess
  apply nonzero
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' f E _ (cap.trans_lt excess)
  intro g hg
  have dg := degree g hg
  have dp := natDegree_map_le (p:=P g) (f:=s)
  have lo := natDegree_add_le (a*P g) (b*(P g).map s)
  have la := natDegree_mul_le (p:=a) (q:=P g)
  have lb := natDegree_mul_le (p:=b) (q:=(P g).map s)
  have cz := coeff_eq_zero_of_natDegree_lt
    (show (a*P g+b*(P g).map s).natDegree<k by omega)
  rw [row g hg] at cz
  simp only [coeff_add,coeff_C_mul,power] at cz
  simp only [f,eval_add,eval_mul,eval_X,eval_pow,eval_C]
  linear_combination cz

/-- Price the actual normalized numerator with the effective denominator
degree. A collision gives a code-degree polynomial slope. -/
theorem small_denominator_count (U : Received F ProximityPrize.Benchmark.IRSProfile.Index)
    (E : Finset F) (P : SelectionMap F) (sel : K6969Global.Selection Dmn U E P)
    (D J : F[X]) (hD : D.natDegree≤472) (hJ : J.natDegree≤131543)
    (slope : ∀g∈E,∀i∈agreementSet Dmn U P g, D.eval (Dmn i)*U 1 i=J.eval (Dmn i))
    (noPoly : ¬∃V : F[X], V.natDegree≤131071 ∧ D*V=J) : E.card≤214887237245589756 := by
  let T (g : E) := D*P g-C (g:F)*J
  have inj : Function.Injective T := by
    intro g h eq
    by_contra diff
    have ne : (g:F)-(h:F)≠0 := sub_ne_zero.mpr (fun z => diff (Subtype.ext z))
    have rel : D*(P g-P h)=C ((g:F)-(h:F))*J := by
      change D*P g-C (g:F)*J=D*P h-C (h:F)*J at eq
      rw [C_sub]
      linear_combination eq
    apply noPoly
    refine ⟨C ((g:F)-(h:F))⁻¹*(P g-P h),(natDegree_C_mul_le ..).trans
      ((natDegree_sub_le ..).trans (max_le (sel.degree_le g g.property) (sel.degree_le h h.property))),?_⟩
    rw [mul_left_comm D _ _,rel,←mul_assoc,←C_mul,inv_mul_cancel₀ ne,C_1,one_mul]
  apply Frontier.LinearKernel.high_cap Dmn E (agreementSet Dmn U P) sel.agreement ⟨T,inj⟩
    (fun i => D.eval (Dmn i)*U 0 i)
  intro g
  refine ⟨(natDegree_sub_le ..).trans (max_le (natDegree_mul_le.trans
    (Nat.add_le_add hD (sel.degree_le g g.property))) ((natDegree_C_mul_le ..).trans hJ)),?_⟩
  intro i hi
  change (D*P g-C (g:F)*J).eval (Dmn i)=_
  rw [eval_sub,eval_mul,eval_mul,eval_C,eval_eq_of_mem_agreementSet hi,←slope g g.property i hi]
  ring

#print axioms cancel_slope_at_node
#print axioms overflow_count
#print axioms small_denominator_count
end
end ProximityPrize.SubmissionLower.Genuine6969
