import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_TrivSqZeroExt_Basic
import ProximityPrize.SubmissionLower.R6966ProofProtocolProfile

section Merged6967_R6966ProofGenericPhysicalCentre
set_option Elab.async false





set_option Elab.async false

namespace Research6966.GenericPhysicalCentre
open Polynomial
open scoped Polynomial nonZeroDivisors Differential
noncomputable section
variable {K:Type*} [Field K]

abbrev Frac (K:Type*) [Field K] := FractionRing K[X]
private abbrev Dual (R:Type*) := TrivSqZeroExt R R

private def jetPoly : K[X]→+*Dual (Frac K) where
  toFun P := (algebraMap K[X] (Frac K) P,algebraMap K[X] (Frac K) P.derivative)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' P Q := by
    apply TrivSqZeroExt.ext
    · exact map_add _ _ _
    · change algebraMap K[X] (Frac K) (P+Q).derivative=_
      rw [map_add,map_add];rfl
  map_mul' P Q := by
    apply TrivSqZeroExt.ext
    · exact map_mul _ _ _
    · change algebraMap K[X] (Frac K) (P*Q).derivative=
        algebraMap _ _ P*algebraMap _ _ Q.derivative+algebraMap _ _ P.derivative*algebraMap _ _ Q
      rw [derivative_mul,map_add,map_mul,map_mul,add_comm]

private def jetFrac : Frac K→+*Dual (Frac K) :=
  IsLocalization.lift (M:=nonZeroDivisors K[X]) (g:=jetPoly) (fun d=>
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (show IsUnit (algebraMap K[X] (Frac K) d.val) from
      ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (Frac K))).mpr (nonZeroDivisors.ne_zero d.property)).isUnit))
-- A rational function at the generic physical centre has its original value
-- in the first coordinate and its ordinary derivative in the second.
private theorem jet_poly (P:K[X]) : jetFrac (algebraMap K[X] (Frac K) P)=jetPoly P :=
  IsLocalization.lift_eq _ _

private theorem jet_value (x:Frac K) : (jetFrac x).fst=x := by
  let fst: Dual (Frac K)→+*Frac K:=(TrivSqZeroExt.fstHom (Frac K) (Frac K) (Frac K)).toRingHom
  have eq:fst.comp jetFrac=RingHom.id _ := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors K[X])
    apply RingHom.ext
    intro P
    change (jetFrac (algebraMap K[X] (Frac K) P)).fst=_
    rw [jet_poly];rfl
  exact RingHom.congr_fun eq x

private def ofJet {R:Type*} [CommRing R] (jet:R→+*Dual R) (fst:∀ x:R,(jet x).fst=x) : Differential R where
  deriv:=Derivation.mk' (((TrivSqZeroExt.sndHom (R:=R) (M:=R)).toAddMonoidHom.comp
    jet.toAddMonoidHom).toIntLinearMap) (by
      intro x y
      change (jet (x*y)).snd=x*(jet y).snd+y*(jet x).snd
      rw [map_mul]
      change (jet x).fst*(jet y).snd+(jet x).snd*(jet y).fst=_
      rw [fst,fst,mul_comm (jet x).snd y])

@[instance_reducible] def physical (K:Type*) [Field K] : Differential (Frac K) :=
  ofJet jetFrac jet_value

attribute [local instance] physical

theorem physical_poly (P:K[X]) : Differential.deriv (algebraMap K[X] (Frac K) P) =
    algebraMap K[X] (Frac K) P.derivative := by
  change (jetFrac (algebraMap K[X] (Frac K) P)).snd=_
  rw [jet_poly];rfl

theorem physical_iterate (P:K[X]) (j:ℕ) : Differential.deriv^[j] (algebraMap K[X] (Frac K) P)=
    algebraMap K[X] (Frac K) (Polynomial.derivative^[j] P) := by
  induction j with
  | zero=>rfl
  | succ j ih=>rw [Function.iterate_succ_apply',ih,physical_poly,Function.iterate_succ_apply']

section Coefficients
variable {F σ:Type*} [CommRing F] [Differential F]

private def onCoeffs (P:MvPolynomial σ F) : MvPolynomial σ F :=
  AddMonoidAlgebra.ofCoeff (P.coeff.mapRange Differential.deriv (map_zero _))

private theorem onCoeffs_coeff (P:MvPolynomial σ F) (e:σ→₀ℕ) :
    (onCoeffs P).coeff e = Differential.deriv (P.coeff e) := rfl

@[instance_reducible] def seeds (σ F:Type*) [CommRing F] [Differential F] : Differential (MvPolynomial σ F) where
  deriv:=Derivation.mk' (({
    toFun:=onCoeffs
    map_zero' := by ext e;simp only [onCoeffs_coeff,MvPolynomial.coeff_zero,Finsupp.zero_apply,map_zero]
    map_add' := by intro P Q;ext e;simp only [onCoeffs_coeff,MvPolynomial.coeff_add,map_add]
    } : MvPolynomial σ F →+ MvPolynomial σ F).toIntLinearMap) (by
      intro P Q
      classical
      ext e
      change (onCoeffs (P*Q)).coeff e=((P*onCoeffs Q)+(Q*onCoeffs P)).coeff e
      rw [mul_comm Q (onCoeffs P)]
      simp only [onCoeffs_coeff,MvPolynomial.coeff_add,MvPolynomial.coeff_mul,map_sum,Derivation.leibniz,
        smul_eq_mul,Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro ab _
      exact mul_comm _ _)

attribute [local instance] seeds

theorem deriv_coeff (P:MvPolynomial σ F) (e:σ→₀ℕ) :
    (Differential.deriv P).coeff e = Differential.deriv (P.coeff e) := rfl

private theorem deriv_C_seed (c:F) : Differential.deriv (MvPolynomial.C c : MvPolynomial σ F)=
    MvPolynomial.C (Differential.deriv c) := by
  classical
  ext e
  rw [deriv_coeff]
  by_cases eq:0=e <;> simp [MvPolynomial.coeff_C,eq]

private theorem deriv_X_seed (i:σ) : Differential.deriv (MvPolynomial.X i:MvPolynomial σ F)=0 := by
  classical
  ext e
  rw [deriv_coeff]
  by_cases eq:Finsupp.single i 1=e <;> simp [MvPolynomial.coeff_X,eq]

theorem deriv_eval (p:σ→F) (fixed:∀i,Differential.deriv (p i)=0) (P:MvPolynomial σ F) :
    Differential.deriv (MvPolynomial.eval p P)=MvPolynomial.eval p (Differential.deriv P) := by
  induction P using MvPolynomial.induction_on with
  | C c=>simp [deriv_C_seed]
  | add P Q hp hq=>simp [hp,hq]
  | mul_X P i hp=>simp [Derivation.leibniz,smul_eq_mul,hp,deriv_X_seed,fixed,mul_comm]

theorem deriv_axis (P:MvPolynomial σ F) (i:σ) :
    (Differential.deriv P).degreeOf i≤P.degreeOf i := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro e he
  apply MvPolynomial.le_degreeOf_of_mem_support
  apply MvPolynomial.mem_support_iff.mpr
  intro zero
  exact (MvPolynomial.mem_support_iff.mp he) (by rw [deriv_coeff,zero,map_zero])

#print axioms deriv_axis
#print axioms deriv_eval
end Coefficients
#print axioms physical_iterate
end
end Research6966.GenericPhysicalCentre

end Merged6967_R6966ProofGenericPhysicalCentre

section Merged6967_R6966ProofPadeJetOrder
set_option Elab.async false



set_option Elab.async false

namespace Research6966.PadeJetOrder
open Polynomial Finset Ideal
open scoped Polynomial
noncomputable section
variable {R : Type*} [CommRing R]

/-- Powers of the ideal (p,V) have explicit divisibility conditions on
every slope coefficient, including those above the requested precision. -/
theorem origin_order (p:R) (Q:R[X]) (k:ℕ) :
    Q ∈ (Ideal.span ({C p,«X»}:Set R[X]))^k ↔ ∀ j,p^(k-j)∣Q.coeff j := by
  classical
  let I : Ideal R[X] := Ideal.span {C p}
  let J : Ideal R[X] := Ideal.span {«X»}
  have span : Ideal.span ({C p,«X»}:Set R[X])=I⊔J := by
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
    obtain ⟨v,hv⟩ : «X»^(j+1)∣b := Ideal.mem_span_singleton.mp (by simpa [J,Ideal.span_singleton_pow] using hb)
    rw [←ab,hu,hv,coeff_add,coeff_C_mul,coeff_X_pow_mul']
    simp
  · intro coeff
    let H:=Ideal.span ({C p,«X»}:Set R[X])
    have pin:C p∈H := Ideal.subset_span (by simp)
    have xin:(«X»:R[X])∈H := Ideal.subset_span (by simp)
    rw [Q.as_sum_support_C_mul_X_pow]
    apply Ideal.sum_mem
    intro j hj
    obtain ⟨u,hu⟩ := coeff j
    have part:=Ideal.mul_mem_mul (Ideal.pow_mem_pow pin (k-j)) (Ideal.pow_mem_pow xin j)
    rw [←pow_add] at part
    have paid : C p^(k-j)*«X»^j∈H^k := Ideal.pow_le_pow_right (by omega) part
    rw [hu,map_mul,C_pow]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using (H^k).mul_mem_left (C u) paid

variable {K : Type*} [Field K]

private theorem translate_ideal (y v:K) :
    (TerminalProjection.fibrePoint y v).map (taylorEquiv (C v)).toRingEquiv =
      Ideal.span ({C («X»-C y),«X»}:Set K[X][X]) := by
  rw [TerminalProjection.fibrePoint,Ideal.map_span]
  congr 1
  have hc (p:K[X]) : (taylorEquiv (C v)) (C p)=C p := taylor_C _ _
  have hx : (taylorEquiv (C v)) «X» = «X»+C (C v) := taylor_X _
  simp [Set.image_insert_eq,Set.image_singleton,hc,hx]

theorem point_order_iff (Q:K[X][X]) (y v:K) (k:ℕ) :
    Q∈(TerminalProjection.fibrePoint y v)^k ↔
      ∀ j,(«X»-C y)^(k-j)∣(taylor (C v) Q).coeff j := by
  rw [←origin_order]
  have eq := Ideal.map_pow (taylorEquiv (C v)).toRingEquiv (TerminalProjection.fibrePoint y v) k
  rw [translate_ideal] at eq
  rw [←eq]
  exact Ideal.apply_mem_of_equiv_iff.symm

/-- At a regular point of a primitive slope-linear graph, dividing by
the graph removes at most one order of contact. -/
theorem strip (A B : K[X]) (R:K[X][X]) (y v:K) (k:ℕ) (reg:A.eval y≠0)
    (onG:A.eval y*v=B.eval y)
    (order:(C A*«X»-C B)*R∈(TerminalProjection.fibrePoint y v)^(k+1)) :
    R∈(TerminalProjection.fibrePoint y v)^k := by
  classical
  let p : K[X]:=«X»-C y
  let D := A*C v-B
  have divD:p∣D := by apply dvd_iff_isRoot.mpr;simp [D,IsRoot,onG]
  have co:IsCoprime A p := by
    obtain ⟨q,hq⟩ : p∣A-C (A.eval y) := by apply dvd_iff_isRoot.mpr;simp [IsRoot]
    refine ⟨C (A.eval y)⁻¹,-C (A.eval y)⁻¹*q,?_⟩
    have inv:C (A.eval y)⁻¹*C (A.eval y)=(1:K[X]) := by rw [←C_mul,inv_mul_cancel₀ reg,C_1]
    linear_combination C (A.eval y)⁻¹*hq+inv
  let S:=taylor (C v) R
  have shifted : taylor (C v) ((C A*«X»-C B)*R) = C A*(«X»*S)+C D*S := by
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
    (order:(C A*«X»-C B)*R∈(TerminalProjection.fibrePoint y v)^k) :
    R∈(TerminalProjection.fibrePoint y v)^k := by
  classical
  let p:K[X]:=«X»-C y
  let D:=A*C v-B
  have nz:D.eval y≠0:=by simpa only [D,eval_sub,eval_mul,eval_C,sub_ne_zero] using miss
  have co:IsCoprime D p := by
    obtain ⟨q,hq⟩ : p∣D-C (D.eval y) := by apply dvd_iff_isRoot.mpr;simp [IsRoot]
    refine ⟨C (D.eval y)⁻¹,-C (D.eval y)⁻¹*q,?_⟩
    have inv:C (D.eval y)⁻¹*C (D.eval y)=(1:K[X]) := by rw [←C_mul,inv_mul_cancel₀ nz,C_1]
    linear_combination C (D.eval y)⁻¹*hq+inv
  let S:=taylor (C v) R
  have shifted : taylor (C v) ((C A*«X»-C B)*R)=C A*(«X»*S)+C D*S := by
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

end Merged6967_R6966ProofPadeJetOrder
