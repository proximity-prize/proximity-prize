import ArkLib.Data.MvPolynomial.WeightedOrder
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.NumberTheory.FLT.MasonStothers
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import ProximityPrize.SubmissionLower.Fast004
import ProximityPrize.SubmissionLower.Fast005
set_option Elab.async false

section PackSource_K1_14Graph
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_14
noncomputable section
open MvPolynomial Finset
variable {F : Type*} [Field F]

def graphExponent (p : ℕ) (e : Fin 2 →₀ ℕ) : ℕ := e 0+p*e 1

def frobeniusGraph (p : ℕ) : MvPolynomial (Fin 2) F →ₐ[F] Polynomial F :=
  aeval ![Polynomial.X,Polynomial.X^p]

theorem graphExponent_injOn (p : ℕ) (hp : 0<p) :
    Set.InjOn (graphExponent p) {e : Fin 2 →₀ ℕ | e 0<p} := by
  intro e he f hf h
  have hm := congrArg (fun n : ℕ => n%p) h
  simp only [graphExponent,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt he,Nat.mod_eq_of_lt hf] at hm
  have hmul : p*e 1=p*f 1 := by unfold graphExponent at h; omega
  have h1 : e 1=f 1 := Nat.eq_of_mul_eq_mul_left hp hmul
  ext i
  fin_cases i <;> assumption

theorem frobeniusGraph_monomial (p : ℕ) (e : Fin 2 →₀ ℕ) (a : F) :
    frobeniusGraph p (monomial e a)=Polynomial.monomial (graphExponent p e) a := by
  rw [frobeniusGraph,aeval_monomial]
  simp [Finsupp.prod_fintype,Fin.prod_univ_succ,graphExponent,← pow_mul,← pow_add,Polynomial.C_mul_X_pow_eq_monomial]

theorem frobeniusGraph_coeff (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hdegree : Q.degreeOf 0<p) (e : Fin 2 →₀ ℕ) (he : e∈Q.support) :
    (frobeniusGraph p Q).coeff (graphExponent p e)=Q.coeff e := by
  classical
  have hex : frobeniusGraph p Q=∑ f∈Q.support,Polynomial.monomial (graphExponent p f) (Q.coeff f) := by
    conv_lhs => rw [Q.as_sum]
    simp only [map_sum,frobeniusGraph_monomial]
  rw [hex,Polynomial.finsetSum_coeff]
  trans ((Polynomial.monomial (graphExponent p e) (Q.coeff e)).coeff (graphExponent p e))
  · apply Finset.sum_eq_single_of_mem e he
    intro f hf hfe
    rw [Polynomial.coeff_monomial,ite_eq_right]
    intro h
    apply hfe
    apply graphExponent_injOn p hp
    · exact (le_degreeOf_of_mem_support 0 hf).trans_lt hdegree
    · exact (le_degreeOf_of_mem_support 0 he).trans_lt hdegree
    · exact h
  · simp

theorem frobeniusGraph_ne_zero (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hQ : Q≠0) (hdegree : Q.degreeOf 0<p) : frobeniusGraph p Q≠0 := by
  obtain ⟨e,he⟩ := support_nonempty.mpr hQ
  intro hz
  have hh := frobeniusGraph_coeff p hp Q hdegree e he
  rw [hz,Polynomial.coeff_zero] at hh
  exact (mem_support_iff.mp he) hh.symm

theorem frobeniusGraph_degree (p a b : ℕ) (Q : MvPolynomial (Fin 2) F)
    (hA : Q.degreeOf 0≤a) (hB : Q.degreeOf 1≤b) :
    (frobeniusGraph p Q).natDegree≤a+p*b := by
  apply (natDegree_aeval_le_weightedTotalDegree ![Polynomial.X,Polynomial.X^p] Q).trans
  apply Finset.sup_le
  intro e he
  have h0 := (le_degreeOf_of_mem_support 0 he).trans hA
  have h1 := (le_degreeOf_of_mem_support 1 he).trans hB
  simp [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul]
  nlinarith

/-- One nonzero parameter coefficient pays every zero specialization,
without primitive-content removal or a separate basepoint argument. -/
theorem frobenius_coefficient_exception_count (p a b : ℕ) (hp : 0<p)
    (Q : MvPolynomial (Fin 2) F) (hQ : Q≠0) (hA : Q.degreeOf 0≤a) (ha : a<p)
    (hB : Q.degreeOf 1≤b) (Γ : Finset F)
    (hΓ : ∀ γ∈Γ,MvPolynomial.eval ![γ,γ^p] Q=0) : Γ.card≤a+p*b := by
  have hn := frobeniusGraph_ne_zero p hp Q hQ (hA.trans_lt ha)
  have hcard : Γ.card≤(frobeniusGraph p Q).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro γ hγ
    apply (Polynomial.mem_roots hn).mpr
    have he : (frobeniusGraph p Q).eval γ=MvPolynomial.eval ![γ,γ^p] Q := by
      have hmap : (Polynomial.evalRingHom γ).comp (frobeniusGraph (F:=F) p).toRingHom=
          MvPolynomial.eval ![γ,γ^p] := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp [frobeniusGraph]
        · intro i
          fin_cases i <;> simp [frobeniusGraph]
      exact RingHom.congr_fun hmap Q
    change (frobeniusGraph p Q).eval γ=0
    rw [he]
    exact hΓ γ hγ
  exact hcard.trans (frobeniusGraph_degree p a b Q hA hB)

end
end K1_14
end PackSource_K1_14Graph

section PackSource_FinitePolynomialAvoidance
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Finset MvPolynomial
open scoped BigOperators
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem exists_nonzero_evaluation_of_totalDegree_lt_card {n : ℕ}
    (p : MvPolynomial (Fin n) F) (hp : p≠0) (hdeg : p.totalDegree<Fintype.card F) :
    ∃ x : Fin n → F, MvPolynomial.eval x p≠0 := by
  classical
  by_contra hn
  push Not at hn
  have hs := MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset F)
  have hgrid : (Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset F)))=Finset.univ := by
    ext x
    simp
  rw [hgrid] at hs
  simp only [hn,Finset.filter_true,Finset.card_univ,Fintype.card_fun,Fintype.card_fin] at hs
  have hpos : 0<(Fintype.card F : ℚ≥0) := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card F)
  have hpow : (Fintype.card F : ℚ≥0)^n≠0 := pow_ne_zero _ hpos.ne'
  rw [Nat.cast_pow,div_self hpow] at hs
  have hlt : (p.totalDegree : ℚ≥0)/(Fintype.card F : ℚ≥0)<1 :=
    (div_lt_one hpos).mpr (by exact_mod_cast hdeg)
  exact (not_lt_of_ge hs) hlt

/-- The same nonzero-evaluation theorem with any finite variable type. -/
theorem exists_nonzero_evaluation_finite_variables {ν : Type} [Fintype ν]
    (p : MvPolynomial ν F) (hp : p≠0) (hdeg : p.totalDegree<Fintype.card F) :
    ∃ x : ν → F, MvPolynomial.eval x p≠0 := by
  let e := Fintype.equivFin ν
  let q := MvPolynomial.rename e p
  have hq : q≠0 := by
    intro hz
    exact hp ((MvPolynomial.rename_eq_zero_iff_of_injective p e.injective).mp hz)
  have hqd : q.totalDegree<Fintype.card F := (MvPolynomial.totalDegree_rename_le e p).trans_lt hdeg
  obtain ⟨x,hx⟩ := exists_nonzero_evaluation_of_totalDegree_lt_card q hq hqd
  refine ⟨x ∘ e,?_⟩
  simpa only [q,MvPolynomial.eval,MvPolynomial.eval₂Hom_rename] using hx

end
end FrobeniusLocator.Strata
end PackSource_FinitePolynomialAvoidance

section PackSource_K1_10Graph
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace K1_10
noncomputable section
open MvPolynomial Finset
variable {F : Type*} [Field F]

def graphExponent (p : ℕ) (e : Fin 2 →₀ ℕ) : ℕ := e 0+p*e 1

def frobeniusGraph (p : ℕ) : MvPolynomial (Fin 2) F →ₐ[F] Polynomial F :=
  aeval ![Polynomial.X,Polynomial.X^p]

theorem graphExponent_injOn (p : ℕ) (hp : 0<p) :
    Set.InjOn (graphExponent p) {e : Fin 2 →₀ ℕ | e 0<p} := by
  intro e he f hf h
  have hm := congrArg (fun n : ℕ => n%p) h
  simp only [graphExponent,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt he,Nat.mod_eq_of_lt hf] at hm
  have hmul : p*e 1=p*f 1 := by unfold graphExponent at h; omega
  have h1 : e 1=f 1 := Nat.eq_of_mul_eq_mul_left hp hmul
  ext i
  fin_cases i <;> assumption

theorem frobeniusGraph_monomial (p : ℕ) (e : Fin 2 →₀ ℕ) (a : F) :
    frobeniusGraph p (monomial e a)=Polynomial.monomial (graphExponent p e) a := by
  rw [frobeniusGraph,aeval_monomial]
  simp [Finsupp.prod_fintype,Fin.prod_univ_succ,graphExponent,← pow_mul,← pow_add,Polynomial.C_mul_X_pow_eq_monomial]

theorem frobeniusGraph_coeff (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hdegree : Q.degreeOf 0<p) (e : Fin 2 →₀ ℕ) (he : e∈Q.support) :
    (frobeniusGraph p Q).coeff (graphExponent p e)=Q.coeff e := by
  classical
  have hex : frobeniusGraph p Q=∑ f∈Q.support,Polynomial.monomial (graphExponent p f) (Q.coeff f) := by
    conv_lhs => rw [Q.as_sum]
    simp only [map_sum,frobeniusGraph_monomial]
  rw [hex,Polynomial.finsetSum_coeff]
  trans ((Polynomial.monomial (graphExponent p e) (Q.coeff e)).coeff (graphExponent p e))
  · apply Finset.sum_eq_single_of_mem e he
    intro f hf hfe
    have hdistinct : graphExponent p f ≠ graphExponent p e := by
      intro h
      apply hfe
      apply graphExponent_injOn p hp
      · exact (le_degreeOf_of_mem_support 0 hf).trans_lt hdegree
      · exact (le_degreeOf_of_mem_support 0 he).trans_lt hdegree
      · exact h
    simp [Polynomial.coeff_monomial, hdistinct]
  · simp

theorem frobeniusGraph_ne_zero (p : ℕ) (hp : 0<p) (Q : MvPolynomial (Fin 2) F)
    (hQ : Q≠0) (hdegree : Q.degreeOf 0<p) : frobeniusGraph p Q≠0 := by
  obtain ⟨e,he⟩ := support_nonempty.mpr hQ
  intro hz
  have hh := frobeniusGraph_coeff p hp Q hdegree e he
  rw [hz,Polynomial.coeff_zero] at hh
  exact (mem_support_iff.mp he) hh.symm

theorem frobeniusGraph_degree (p a b : ℕ) (Q : MvPolynomial (Fin 2) F)
    (hA : Q.degreeOf 0≤a) (hB : Q.degreeOf 1≤b) :
    (frobeniusGraph p Q).natDegree≤a+p*b := by
  apply (natDegree_aeval_le_weightedTotalDegree ![Polynomial.X,Polynomial.X^p] Q).trans
  apply Finset.sup_le
  intro e he
  have h0 := (le_degreeOf_of_mem_support 0 he).trans hA
  have h1 := (le_degreeOf_of_mem_support 1 he).trans hB
  simp [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_succ,smul_eq_mul]
  nlinarith

/-- One nonzero parameter coefficient pays every zero specialization,
without primitive-content removal or a separate basepoint argument. -/
theorem frobenius_coefficient_exception_count (p a b : ℕ) (hp : 0<p)
    (Q : MvPolynomial (Fin 2) F) (hQ : Q≠0) (hA : Q.degreeOf 0≤a) (ha : a<p)
    (hB : Q.degreeOf 1≤b) (Γ : Finset F)
    (hΓ : ∀ γ∈Γ,MvPolynomial.eval ![γ,γ^p] Q=0) : Γ.card≤a+p*b := by
  have hn := frobeniusGraph_ne_zero p hp Q hQ (hA.trans_lt ha)
  have hcard : Γ.card≤(frobeniusGraph p Q).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro γ hγ
    apply (Polynomial.mem_roots hn).mpr
    have he : (frobeniusGraph p Q).eval γ=MvPolynomial.eval ![γ,γ^p] Q := by
      have hmap : (Polynomial.evalRingHom γ).comp (frobeniusGraph (F:=F) p).toRingHom=
          MvPolynomial.eval ![γ,γ^p] := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp [frobeniusGraph]
        · intro i
          fin_cases i <;> simp [frobeniusGraph]
      exact RingHom.congr_fun hmap Q
    change (frobeniusGraph p Q).eval γ=0
    rw [he]
    exact hΓ γ hγ
  exact hcard.trans (frobeniusGraph_degree p a b Q hA hB)

end
end K1_10
end PackSource_K1_10Graph

section PackSource_MultivariateMinorDegree
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Finset Matrix MvPolynomial
open scoped BigOperators
variable {F ν c : Type} [Field F] [Fintype c] [DecidableEq c]

theorem totalDegree_det_le_row_sum (M : Matrix c c (MvPolynomial ν F))
    (d : c → ℕ) (hM : ∀ i j, (M i j).totalDegree≤d i) :
    M.det.totalDegree≤∑ i, d i := by
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  have hs : (Equiv.Perm.sign σ • ∏ i, M (σ i) i).totalDegree≤
      (∏ i, M (σ i) i).totalDegree := MvPolynomial.totalDegree_smul_le _ _
  exact hs.trans ((MvPolynomial.totalDegree_finsetProd _ _).trans
    ((Finset.sum_le_sum (fun i _ => hM (σ i) i)).trans_eq (Equiv.sum_comp σ d)))

end
end FrobeniusLocator.Strata
end PackSource_MultivariateMinorDegree
