import ProximityPrize.SubmissionLower.R6966ProofTerminalProjection
import Mathlib.Algebra.Polynomial.Taylor

set_option Elab.async false

namespace Research6966.PadeJetOrder
open Polynomial Finset Ideal
open scoped Polynomial
noncomputable section
variable {R : Type*} [CommRing R]

/-- Powers of the ideal (p,V) have explicit divisibility conditions on
every slope coefficient, including those above the requested precision. -/
theorem origin_order (p:R) (Q:R[X]) (k:ℕ) :
    Q ∈ (Ideal.span ({C p,X}:Set R[X]))^k ↔ ∀ j,p^(k-j)∣Q.coeff j := by
  classical
  let I : Ideal R[X] := Ideal.span {C p}
  let J : Ideal R[X] := Ideal.span {X}
  have span : Ideal.span ({C p,X}:Set R[X])=I⊔J := by
    rw [←Ideal.span_union,Set.singleton_union]
  constructor
  · intro contact j
    by_cases small:k≤j
    · simp [Nat.sub_eq_zero_of_le small]
    have pair (n:ℕ) : (I⊔J)^(n+j)≤I^n ⊔ J^(j+1) := by
      rw [←Ideal.add_eq_sup,add_pow,Ideal.sum_eq_sup]
      apply Finset.sup_le
      intro i hi
      by_cases hn : n ≤ i
      · exact Ideal.mul_le_left.trans (Ideal.mul_le_left.trans ((Ideal.pow_le_pow_right hn).trans le_sup_left))
      · exact Ideal.mul_le_left.trans (Ideal.mul_le_right.trans
          ((Ideal.pow_le_pow_right (by omega : j+1≤n+j-i)).trans le_sup_right))
    have q:=pair (k-j)
    rw [Nat.sub_add_cancel (by omega : j≤k)] at q
    rw [span] at contact
    obtain ⟨a,ha,b,hb,ab⟩:= Submodule.mem_sup.mp (q contact)
    obtain ⟨u,hu⟩ : C (p^(k-j))∣a := Ideal.mem_span_singleton.mp (by simpa [I,Ideal.span_singleton_pow] using ha)
    obtain ⟨v,hv⟩ : X^(j+1)∣b := Ideal.mem_span_singleton.mp (by simpa [J,Ideal.span_singleton_pow] using hb)
    rw [←ab,hu,hv,coeff_add,coeff_C_mul,coeff_X_pow_mul']
    simp
  · intro coeff
    let H:=Ideal.span ({C p,X}:Set R[X])
    have pin:C p∈H := Ideal.subset_span (by simp)
    have xin:(X:R[X])∈H := Ideal.subset_span (by simp)
    rw [Q.as_sum_support_C_mul_X_pow]
    apply Ideal.sum_mem
    intro j hj
    obtain ⟨u,hu⟩ := coeff j
    have part:=Ideal.mul_mem_mul (Ideal.pow_mem_pow pin (k-j)) (Ideal.pow_mem_pow xin j)
    rw [←pow_add] at part
    have paid : C p^(k-j)*X^j∈H^k := Ideal.pow_le_pow_right (by omega) part
    rw [hu,map_mul,C_pow]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using (H^k).mul_mem_left (C u) paid

variable {K : Type*} [Field K]

private theorem translate_ideal (y v:K) :
    (TerminalProjection.fibrePoint y v).map (taylorEquiv (C v)).toRingEquiv =
      Ideal.span ({C (X-C y),X}:Set K[X][X]) := by
  rw [TerminalProjection.fibrePoint,Ideal.map_span]
  congr 1
  have hc (p:K[X]) : (taylorEquiv (C v)) (C p)=C p := taylor_C _ _
  have hx : (taylorEquiv (C v)) X = X+C (C v) := taylor_X _
  simp [Set.image_insert_eq,Set.image_singleton,hc,hx]

theorem point_order_iff (Q:K[X][X]) (y v:K) (k:ℕ) :
    Q∈(TerminalProjection.fibrePoint y v)^k ↔
      ∀ j,(X-C y)^(k-j)∣(taylor (C v) Q).coeff j := by
  rw [←origin_order]
  have eq := Ideal.map_pow (taylorEquiv (C v)).toRingEquiv (TerminalProjection.fibrePoint y v) k
  rw [translate_ideal] at eq
  rw [←eq]
  exact Ideal.apply_mem_of_equiv_iff.symm

/-- At a regular point of a primitive slope-linear graph, dividing by
the graph removes at most one order of contact. -/
theorem strip (A B : K[X]) (R:K[X][X]) (y v:K) (k:ℕ) (reg:A.eval y≠0)
    (onG:A.eval y*v=B.eval y)
    (order:(C A*X-C B)*R∈(TerminalProjection.fibrePoint y v)^(k+1)) :
    R∈(TerminalProjection.fibrePoint y v)^k := by
  classical
  let p : K[X]:=X-C y
  let D := A*C v-B
  have divD:p∣D := by apply dvd_iff_isRoot.mpr;simp [D,IsRoot,onG]
  have co:IsCoprime A p := by
    obtain ⟨q,hq⟩ : p∣A-C (A.eval y) := by apply dvd_iff_isRoot.mpr;simp [IsRoot]
    refine ⟨C (A.eval y)⁻¹,-C (A.eval y)⁻¹*q,?_⟩
    have inv:C (A.eval y)⁻¹*C (A.eval y)=(1:K[X]) := by rw [←C_mul,inv_mul_cancel₀ reg,C_1]
    linear_combination C (A.eval y)⁻¹*hq+inv
  let S:=taylor (C v) R
  have shifted : taylor (C v) ((C A*X-C B)*R) = C A*(X*S)+C D*S := by
    simp only [taylor_mul,map_sub,taylor_C,taylor_X,S,D,map_mul]
    ring
  have known := (point_order_iff _ y v (k+1)).mp order
  apply (point_order_iff _ y v k).mpr
  have all (l j:ℕ) (jl:k-j=l) : p^l∣S.coeff j := by
    induction l generalizing j with
    | zero => simp
    | succ l ih =>
      have next := ih (j+1) (by omega)
      have higher := known (j+1)
      rw [shifted,coeff_add,coeff_C_mul,coeff_C_mul,coeff_X_mul,
        show k+1-(j+1)=l+1 by omega] at higher
      have d : p^(l+1)∣D*S.coeff (j+1) := by
        rw [pow_succ']
        exact mul_dvd_mul divD next
      exact (co.symm.pow_left).dvd_of_dvd_mul_left ((dvd_add_left d).mp higher)
  exact fun j=>all (k-j) j rfl

#print axioms origin_order
#print axioms strip

/-- At a point off the graph its constant Taylor coefficient is a unit
modulo the ordinate factor. Division preserves the entire order. -/
theorem strip_off (A B:K[X]) (R:K[X][X]) (y v:K) (k:ℕ) (miss:A.eval y*v≠B.eval y)
    (order:(C A*X-C B)*R∈(TerminalProjection.fibrePoint y v)^k) :
    R∈(TerminalProjection.fibrePoint y v)^k := by
  classical
  let p:K[X]:=X-C y
  let D:=A*C v-B
  have nz:D.eval y≠0:=by simpa only [D,eval_sub,eval_mul,eval_C,sub_ne_zero] using miss
  have co:IsCoprime D p := by
    obtain ⟨q,hq⟩ : p∣D-C (D.eval y) := by apply dvd_iff_isRoot.mpr;simp [IsRoot]
    refine ⟨C (D.eval y)⁻¹,-C (D.eval y)⁻¹*q,?_⟩
    have inv:C (D.eval y)⁻¹*C (D.eval y)=(1:K[X]) := by rw [←C_mul,inv_mul_cancel₀ nz,C_1]
    linear_combination C (D.eval y)⁻¹*hq+inv
  let S:=taylor (C v) R
  have shifted : taylor (C v) ((C A*X-C B)*R)=C A*(X*S)+C D*S := by
    simp only [taylor_mul,map_sub,taylor_C,taylor_X,S,D,map_mul]
    ring
  have known:=(point_order_iff _ y v k).mp order
  apply (point_order_iff _ y v k).mpr
  intro j
  change p^(k-j)∣S.coeff j
  induction j with
  | zero =>
    have left:=known 0
    rw [shifted,coeff_add,coeff_C_mul,coeff_C_mul,coeff_X_mul_zero,mul_zero,zero_add] at left
    exact co.symm.pow_left.dvd_of_dvd_mul_left left
  | succ j ih =>
    have prev:p^(k-(j+1))∣A*S.coeff j :=
      dvd_mul_of_dvd_right ((pow_dvd_pow p (show k-(j+1)≤k-j by omega)).trans ih) _
    have left:=known (j+1)
    rw [shifted,coeff_add,coeff_C_mul,coeff_C_mul,coeff_X_mul] at left
    exact co.symm.pow_left.dvd_of_dvd_mul_left ((dvd_add_right prev).mp left)

#print axioms strip_off
end
end Research6966.PadeJetOrder
