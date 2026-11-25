import ProximityPrize.SubmissionLower.R6966ProofNonlinearMarkRows

set_option Elab.async false

namespace Research6966.NonlinearMarkDegrees
open Polynomial Finset
open NonlinearMarkRows
open scoped Polynomial Differential
noncomputable section
set_option maxHeartbeats 600000
variable {σ F:Type*} [Field F] [Differential F]
attribute [local instance] GenericPhysicalCentre.seeds

/-- Degree across any chosen seed coordinates. Taking one indicator
measures one seed, while weight one measures total seed degree. -/
def cap (w:σ→ℕ) (u:ℕ) (P:Eqn σ F) : Prop :=
  ∀ i,P.coeff i∈MvPolynomial.restrictWeightAtMost w u

private theorem cap_add (w:σ→ℕ) {u:ℕ} {P Q:Eqn σ F} (p:cap w u P) (q:cap w u Q) :
    cap w u (P+Q) := fun i=>by rw [coeff_add];exact Submodule.add_mem _ (p i) (q i)

private theorem cap_sub (w:σ→ℕ) {u:ℕ} {P Q:Eqn σ F} (p:cap w u P) (q:cap w u Q) :
    cap w u (P-Q) := fun i=>by rw [coeff_sub];exact Submodule.sub_mem _ (p i) (q i)

private theorem cap_mul {w:σ→ℕ} {u v:ℕ} {P Q:Eqn σ F} (p:cap w u P) (q:cap w v Q) :
    cap w (u+v) (P*Q) := by
  intro i
  rw [coeff_mul]
  exact Submodule.sum_mem _ (fun ab _=>MvPolynomial.mul_mem_restrictWeightAtMost (p ab.1) (q ab.2))

private theorem cap_C (w:σ→ℕ) (c:F) : cap w 0 (C (MvPolynomial.C c)) := by
  intro i
  by_cases zero:i=0
  · subst i;rw [coeff_C_zero];exact MvPolynomial.C_mem_restrictWeightAtMost _ le_rfl _
  · rw [coeff_C,ite_eq_right zero];exact Submodule.zero_mem _

private theorem cap_X (w:σ→ℕ) : cap (F:=F) w 0 Polynomial.X := by
  intro i
  rw [coeff_X]
  split
  · exact MvPolynomial.C_mem_restrictWeightAtMost _ le_rfl (1:F)
  · exact Submodule.zero_mem _

private theorem cap_pow {w:σ→ℕ} {u:ℕ} {P:Eqn σ F} (p:cap w u P) (j:ℕ) :
    cap w (j*u) (P^j) := by
  induction j with
  | zero=>simpa only [pow_zero,zero_mul,map_one] using cap_C w (1:F)
  | succ j ih=>rw [pow_succ,Nat.succ_mul];exact cap_mul ih p

private theorem cap_deriv {w:σ→ℕ} {u:ℕ} {P:Eqn σ F} (p:cap w u P) :
    cap w u P.derivative := by
  intro i
  rw [coeff_derivative]
  rw [show (↑i+1:MvPolynomial σ F)=MvPolynomial.C (i+1:F) by simp,
    mul_comm,←MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (p _)

private theorem cap_dx {w:σ→ℕ} {u:ℕ} {P:Eqn σ F} (p:cap w u P) :
    cap w u (Differential.mapCoeffs P) := by
  intro i
  rw [Differential.coeff_mapCoeffs]
  apply MvPolynomial.mem_restrictWeightAtMost.mpr
  intro e he
  apply MvPolynomial.mem_restrictWeightAtMost.mp (p i) e
  apply MvPolynomial.mem_support_iff.mpr
  intro zero
  exact (MvPolynomial.mem_support_iff.mp he) (by rw [GenericPhysicalCentre.deriv_coeff,zero,map_zero])

theorem numerator_seeds {w:σ→ℕ} {u:ℕ} {A B:Eqn σ F} (ha:cap w u A) (hb:cap w u B) (j:ℕ) :
    cap w ((2*j+1)*u) (QuadraticWeight.numerator A B j) := by
  have dir {P:Eqn σ F} {l:ℕ} (p:cap w l P) :
      cap w (u+l) (A*Differential.mapCoeffs P+B*P.derivative) :=
    cap_add _ (cap_mul ha (cap_dx p)) (cap_mul hb (cap_deriv p))
  induction j with
  | zero=>simpa [QuadraticWeight.numerator] using hb
  | succ j ih=>
    rw [QuadraticWeight.numerator]
    apply cap_sub
    · convert cap_mul ha (dir ih) using 1 <;> ring
    · have constant:cap w 0 ((↑(2*j+1):Eqn σ F)):=by
        simpa only [map_natCast] using cap_C w (↑(2*j+1):F)
      convert cap_mul (cap_mul constant ih) (dir ha) using 1 <;> ring

private theorem dx_degree (P:Eqn σ F) : (Differential.mapCoeffs P).natDegree≤P.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n above
  rw [Differential.coeff_mapCoeffs,coeff_eq_zero_of_natDegree_lt above,map_zero]

theorem numerator_ordinate {r:ℕ} (rp:1≤r) {A B:Eqn σ F} (ha:A.natDegree≤r) (hb:B.natDegree≤r+1) (j:ℕ) :
    (QuadraticWeight.numerator A B j).natDegree≤(2*j+1)*r+1 := by
  have dir {P:Eqn σ F} {l:ℕ} (pos:0<l) (p:P.natDegree≤l) :
      (A*Differential.mapCoeffs P+B*P.derivative).natDegree≤r+l := by
    apply (natDegree_add_le ..).trans (max_le _ _)
    · exact natDegree_mul_le.trans (Nat.add_le_add ha ((dx_degree P).trans p))
    · exact (natDegree_mul_le.trans (Nat.add_le_add hb ((natDegree_derivative_le P).trans
        (Nat.sub_le_sub_right p 1)))).trans (by omega)
  induction j with
  | zero=>simpa [QuadraticWeight.numerator] using hb
  | succ j ih=>
    rw [QuadraticWeight.numerator]
    apply (natDegree_sub_le ..).trans (max_le _ _)
    · exact (natDegree_mul_le.trans (Nat.add_le_add ha (dir (Nat.succ_pos _) ih))).trans (by ring_nf;omega)
    · have num:((↑(2*j+1):Eqn σ F)).natDegree=0:=natDegree_natCast _
      have left:=natDegree_mul_le.trans (Nat.add_le_add num.le ih)
      exact (natDegree_mul_le.trans (Nat.add_le_add left (dir rp ha))).trans (by ring_nf;omega)

private theorem common_seed {w:σ→ℕ} {u:ℕ} {A B:Eqn σ F} (ha:cap w u A) (hb:cap w u B)
    (d j:ℕ) (le:j≤d) : cap w ((2*d-1)*u) (coeffRow A B d j) := by
  cases j with
  | zero=>simpa only [coeffRow,zero_add] using cap_mul (cap_X w) (cap_pow ha (2*d-1))
  | succ j=>
    have eq:(2*j+1)*u+(2*d-1-(2*j+1))*u=(2*d-1)*u:=by rw [←Nat.add_mul];congr 1;omega
    simpa only [coeffRow,eq] using cap_mul (numerator_seeds ha hb j) (cap_pow ha (2*d-1-(2*j+1)))

theorem node_seeds {w:σ→ℕ} {u:ℕ} {A B:Eqn σ F} (ha:cap w u A) (hb:cap w u B)
    (d:ℕ) (c x received:F) : cap w ((2*d-1)*u) (node A B d c x received) := by
  unfold node
  apply cap_sub
  · intro i
    rw [finsetSum_coeff]
    apply Submodule.sum_mem
    intro j hj
    exact (show cap w ((2*d-1)*u) _ from by
      simpa only [zero_add] using cap_mul (cap_C w ((x-c)^j/(j.factorial:F)))
        (common_seed ha hb d j (Nat.le_of_lt_succ (mem_range.mp hj)))) i
  · simpa only [zero_add] using cap_mul (cap_C w received) (cap_pow ha (2*d-1))

theorem node_ordinate {r:ℕ} (rp:1≤r) {A B:Eqn σ F} (ha:A.natDegree≤r) (hb:B.natDegree≤r+1)
    (d:ℕ) (c x received:F) : (node A B d c x received).natDegree≤(2*d-1)*r+1 := by
  have bound (j:ℕ) (le:j≤d) : (coeffRow A B d j).natDegree≤(2*d-1)*r+1 := by
    cases j with
    | zero=>exact (natDegree_mul_le.trans (Nat.add_le_add natDegree_X.le
        ((natDegree_pow_le ..).trans (Nat.mul_le_mul_left _ ha)))).trans (by omega)
    | succ j=>
      have add:2*j+1+(2*d-1-(2*j+1))=2*d-1:=by omega
      have cost:=natDegree_mul_le.trans (Nat.add_le_add (numerator_ordinate rp ha hb j)
        ((natDegree_pow_le ..).trans (Nat.mul_le_mul_left (2*d-1-(2*j+1)) ha)))
      simpa only [coeffRow] using cost.trans (show (2*j+1)*r+1+(2*d-1-(2*j+1))*r≤(2*d-1)*r+1 from
        by calc
          _ = ((2*j+1)+(2*d-1-(2*j+1)))*r+1 := by ring
          _ ≤ _ := by rw [add])
  unfold node
  apply (natDegree_sub_le ..).trans (max_le _ _)
  · apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_C_mul_le _ _).trans (bound j (Nat.le_of_lt_succ (mem_range.mp hj)))
  · exact (natDegree_C_mul_le _ _).trans ((natDegree_pow_le ..).trans ((Nat.mul_le_mul_left _ ha).trans (by omega)))

#print axioms node_seeds
#print axioms node_ordinate
end
end Research6966.NonlinearMarkDegrees
