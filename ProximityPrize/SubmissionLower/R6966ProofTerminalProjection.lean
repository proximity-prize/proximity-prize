import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

set_option Elab.async false

namespace Research6966.TerminalProjection
open Polynomial
open scoped Polynomial
noncomputable section

/-- Restrict a slope polynomial to A V = B, clearing the same denominator
for every coefficient. The index is the bank's slope cap. -/
def cleared {R : Type*} [CommRing R] (A B : R) (Q : R[X]) (J : ℕ) : R :=
  Q.sum (fun j c => c * B^j * A^(J-j))

theorem map_cleared {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B:R) (v:S) (hv:f A*v=f B) (Q:R[X]) (J:ℕ) (bound:Q.natDegree≤J) :
    f (cleared A B Q J) = (f A)^J * Q.eval₂ f v := by
  rw [cleared,Polynomial.sum_def,map_sum,eval₂_eq_sum,Polynomial.sum_def,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have le: i≤J := (le_natDegree_of_mem_supp i hi).trans bound
  rw [map_mul,map_mul,map_pow,map_pow,←hv,mul_pow]
  have full : (f A)^i*(f A)^(J-i)=(f A)^J := by rw [←pow_add];congr 1;omega
  linear_combination (f (Q.coeff i))*v^i*full

variable {K:Type*} [Field K]
private abbrev R := K[X]

/-- Avoiding the primitive graph makes the cleared projection nonzero. -/
theorem integral_nonzero_of_avoids {S:Type*} [CommRing S] [IsDomain S] [NormalizedGCDMonoid S]
    (A B:S) (Q:S[X]) (J:ℕ)
    (cap:Q.natDegree≤J) (nz:A≠0) (prim:(C A*X-C B).IsPrimitive)
    (avoid:¬ C A*X-C B ∣ Q) : cleared A B Q J ≠ 0 := by
  let F:=FractionRing S
  let f:=algebraMap S F
  have an : f A≠0 := (map_ne_zero_iff _ (IsFractionRing.injective _ F)).mpr nz
  let v:=f B/f A
  have av:f A*v=f B := by dsimp [v];field_simp
  intro z
  have eq:=map_cleared f A B v av Q J cap
  rw [z,map_zero] at eq
  have root : IsRoot (Q.map f) v := by
    rw [IsRoot,eval_map]
    exact (mul_eq_zero.mp eq.symm).resolve_left (pow_ne_zero _ an)
  obtain ⟨H,fac⟩ := dvd_iff_isRoot.mpr root
  apply avoid
  apply prim.dvd_of_fraction_map_dvd_fraction_map (K:=F)
  refine ⟨C (f A)⁻¹ * H,?_⟩
  rw [fac,Polynomial.map_sub,Polynomial.map_mul,map_C,map_X,map_C]
  have one : C (f A) * C (f A)⁻¹ = (1:F[X]) := by rw [←C_mul,mul_inv_cancel₀ an,C_1]
  have point : C (f B)*C (f A)⁻¹ = (C v:F[X]) := by rw [←C_mul];rfl
  linear_combination -(X*H)*one + H*point

theorem nonzero_of_avoids (A B:K[X]) (Q:K[X][X]) (J:ℕ)
    (cap:Q.natDegree≤J) (nz:A≠0) (prim:(C A*X-C B).IsPrimitive)
    (avoid:¬ C A*X-C B ∣ Q) : cleared A B Q J ≠ 0 := by
  classical
  exact integral_nonzero_of_avoids A B Q J cap nz prim avoid

def fibrePoint (y v:K) : Ideal K[X][X] :=
  Ideal.span {C (X-C y), X-C (C v)}

/-- Restriction along the graph preserves every order at a smooth graph
point. The quotient modulo (X-y)^k handles all powers at once. -/
theorem restriction_order (A B:K[X]) (Q:K[X][X]) (y v:K) (J k:ℕ)
    (cap:Q.natDegree≤J) (regular:A.eval y≠0) (onGraph:A.eval y*v=B.eval y)
    (order:Q∈(fibrePoint y v)^k) : (X-C y)^k ∣ cleared A B Q J := by
  classical
  cases k with
  | zero => simp
  | succ k =>
    let p:K[X]:=X-C y
    have atY : p ∣ A-C (A.eval y) := by apply dvd_iff_isRoot.mpr; simp [IsRoot]
    obtain ⟨d,hd⟩:=atY
    have cop : IsCoprime A p := by
      refine ⟨C (A.eval y)⁻¹,-C (A.eval y)⁻¹*d,?_⟩
      have inv : C (A.eval y)⁻¹*C (A.eval y)=(1:K[X]) := by rw [←C_mul,inv_mul_cancel₀ regular,C_1]
      linear_combination C (A.eval y)⁻¹*hd + inv
    obtain ⟨c,b,bez⟩:=cop.pow_right (n:=k+1)
    let W:=c*B
    have value : W.eval y=v := by
      have H:=congrArg (eval y) bez
      simp [p] at H
      dsimp [W];rw [eval_mul,←onGraph,←mul_assoc,H,one_mul]
    let ev:=evalRingHom W
    have mapped : (fibrePoint y v).map ev ≤ Ideal.span {p} := by
      apply Ideal.map_le_iff_le_comap.mpr
      apply Ideal.span_le.mpr
      intro F hF
      rcases hF with hF|hF
      · subst F;simp [ev,p]
      · have F_eq:F=X-C (C v):=Set.mem_singleton_iff.mp hF
        subst F;change (X-C (C v)).eval W∈Ideal.span {p}
        rw [eval_sub,eval_X,eval_C,Ideal.mem_span_singleton]
        apply dvd_iff_isRoot.mpr;simp [IsRoot,value]
    have orderW : Q.eval W ∈ Ideal.span {p^(k+1)} := by
      have h:=Ideal.mem_map_of_mem ev order
      rw [Ideal.map_pow] at h
      rw [← Ideal.span_singleton_pow]
      have incl : ((fibrePoint y v).map ev)^(k+1) ≤ (Ideal.span {p})^(k+1) := by gcongr
      exact incl h
    let I:Ideal K[X]:=Ideal.span {p^(k+1)}
    let f:=Ideal.Quotient.mk I
    have dead:f (p^(k+1))=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    have active : f A*f W=f B := by
      have H:=congrArg f bez
      simp only [map_add,map_mul,dead,mul_zero,add_zero,map_one] at H
      dsimp only [W];rw [map_mul]
      linear_combination f B*H
    have res:=map_cleared f A B (f W) active Q J cap
    have compat : f (Q.eval W)=Q.eval₂ f (f W) := by
      simp
    rw [←compat] at res
    have wz:f (Q.eval W)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr orderW
    rw [wz,mul_zero] at res
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp res)

#print axioms map_cleared
#print axioms nonzero_of_avoids
#print axioms restriction_order

/-- One avoiding row bounds the entire on-graph ordinate product, including
its order. A different row is allowed for each seed axis. -/
theorem all_sheets (A B : K[X]) (Q : K[X][X]) (ys : Finset K) (v : K → K) (J k : ℕ)
    (cap : Q.natDegree ≤ J)
    (sheets : ∀ y ∈ ys, A.eval y ≠ 0 ∧ A.eval y*v y = B.eval y ∧
      Q ∈ (fibrePoint y (v y))^k) :
    (∏ y ∈ ys, (X-C y : K[X]))^k ∣ cleared A B Q J := by
  classical
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj h
    exact ((isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr h).isUnit).pow_left).pow_right
  · intro y hy
    obtain ⟨reg,onG,van⟩ := sheets y hy
    exact restriction_order A B Q _ _ _ _ cap reg onG van

/-- Projection width in either seed, viewing the other variables as
coefficients. Physical differentiation is not needed for this estimate. -/
theorem seed_width (A B : K[X]) (Q : K[X][X]) (J u U : ℕ)
    (cap : Q.natDegree ≤ J) (a : A.natDegree ≤ u) (b : B.natDegree ≤ u)
    (coeff : ∀ i ∈ Q.support, (Q.coeff i).natDegree ≤ U) :
    (cleared A B Q J).natDegree ≤ U+J*u := by
  rw [cleared, Polynomial.sum_def]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have ij := (le_natDegree_of_mem_supp i hi).trans cap
  calc
    _ ≤ ((Q.coeff i).natDegree+i*u)+(J-i)*u := by
      apply natDegree_mul_le.trans;apply Nat.add_le_add
      · apply natDegree_mul_le.trans
        exact Nat.add_le_add_left (natDegree_pow_le.trans (Nat.mul_le_mul_left i b)) _
      · exact natDegree_pow_le.trans (Nat.mul_le_mul_left _ a)
    _ ≤ U+J*u := by
      rw [Nat.add_assoc,←Nat.add_mul, Nat.add_sub_of_le ij]
      exact Nat.add_le_add_right (coeff i hi) _

/-- A total-jet cap B₀ saves one ordinate degree per slope exponent. -/
theorem ordinate_width {F:Type*} [CommRing F] [Nontrivial F] (A B : F[X]) (Q : F[X][X]) (J a B₀ : ℕ)
    (cap : Q.natDegree ≤ J) (positive : 0<a)
    (degA : A.natDegree ≤ a-1) (degB : B.natDegree ≤ a)
    (coeff : ∀ i ∈ Q.support, (Q.coeff i).natDegree+i ≤ B₀) :
    (cleared A B Q J).natDegree ≤ B₀+(a-1)*J := by
  rw [cleared, Polynomial.sum_def]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have ij := (le_natDegree_of_mem_supp i hi).trans cap
  have ident : i*a + (J-i)*(a-1) = i + (a-1)*J := by
    have split : J = i+(J-i) := by omega
    have s : (a-1)+1=a := by omega
    calc
      _ = i*((a-1)+1)+(J-i)*(a-1) := by rw [s]
      _ = i+(a-1)*(i+(J-i)) := by ring
      _ = _ := by rw [←split]
  calc
    _ ≤ ((Q.coeff i).natDegree+i*a)+(J-i)*(a-1) := by
      apply natDegree_mul_le.trans;apply Nat.add_le_add
      · apply natDegree_mul_le.trans
        exact Nat.add_le_add_left (natDegree_pow_le.trans (Nat.mul_le_mul_left _ degB)) _
      · exact natDegree_pow_le.trans (Nat.mul_le_mul_left _ degA)
    _ ≤ B₀+(a-1)*J := by
      rw [Nat.add_assoc,ident,←Nat.add_assoc]
      exact Nat.add_le_add_right (coeff i hi) _

#print axioms all_sheets
#print axioms seed_width
#print axioms ordinate_width
end
end Research6966.TerminalProjection
