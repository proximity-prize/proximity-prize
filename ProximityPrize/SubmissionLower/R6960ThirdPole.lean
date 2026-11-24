import ProximityPrize.SubmissionLower.Fast012
import ArkLib.Data.Polynomial.ResultantDegree
import ArkLib.Data.Polynomial.ResultantSpecialization

set_option Elab.async false
set_option maxHeartbeats 800000
noncomputable section
namespace Lower6960.ThirdPole
open Polynomial
open scoped Polynomial BigOperators Classical

abbrev Seeds (F : Type*) [CommRing F] := MvPolynomial (Fin 2) F

private def view {F : Type*} [CommRing F] (i : Fin 2) :=
  (MvPolynomial.optionEquivLeft F {j : Fin 2 // j≠i}).toRingHom.comp
    (MvPolynomial.rename (R:=F) (Equiv.optionSubtypeNe i).symm).toRingHom

theorem resultant_axis {F : Type*} [Field F] (f g : (Polynomial (Seeds F))) (m n a b : ℕ)
    (i : Fin 2) (hf : ∀ j, (f.coeff j).degreeOf i≤a) (hg : ∀ j, (g.coeff j).degreeOf i≤b) :
    (f.resultant g m n).degreeOf i≤n*a+m*b := by
  have deg (Q : Seeds F) : ((view i) Q).natDegree=Q.degreeOf i :=
    (MvPolynomial.degreeOf_eq_natDegree i Q).symm
  rw [← deg, ← Polynomial.resultant_map_map]
  apply Polynomial.natDegree_resultant_le_of_coeff_natDegree_le
  · intro j; rw [coeff_map,deg]; exact hf j
  · intro j; rw [coeff_map,deg]; exact hg j

/-- Eliminate the exterior seed even at labels where either leading coefficient drops. -/
theorem count_common {F : Type*} [Field F] (p : ℕ) (hp : 0<p)
    (f g : (Polynomial (Seeds F))) (a b c d : ℕ)
    (fb : ∀ j, (f.coeff j).degreeOf 0≤a ∧ (f.coeff j).degreeOf 1≤b)
    (gb : ∀ j, (g.coeff j).degreeOf 0≤c ∧ (g.coeff j).degreeOf 1≤d)
    (pos : f.natDegree≠0 ∨ g.natDegree≠0) (proper : f.resultant g ≠ 0)
    (small : g.natDegree*a+f.natDegree*c<p) (T : Finset F)
    (roots : ∀ z∈T, ∃ u : F, (f.map (MvPolynomial.eval ![z,z^p])).eval u=0 ∧
      (g.map (MvPolynomial.eval ![z,z^p])).eval u=0) :
    T.card≤(g.natDegree*a+f.natDegree*c)+p*(g.natDegree*b+f.natDegree*d) := by
  apply K1_10.frobenius_coefficient_exception_count p _ _ hp _ proper
    (resultant_axis f g _ _ _ _ 0 (fun j => (fb j).1) (fun j => (gb j).1)) small
    (resultant_axis f g _ _ _ _ 1 (fun j => (fb j).2) (fun j => (gb j).2))
  intro z hz
  obtain ⟨u,hu,hv⟩:=roots z hz
  exact Polynomial.map_resultant_eq_zero_of_common_root _ f g le_rfl le_rfl pos u hu hv

/-- Coefficients of the equation in the ordinate, evaluated at a fixed abscissa.
The exterior seed is the polynomial variable of the result. -/
def pull {F : Type*} [Field F] (e : ℕ) (f : ℕ → Seeds F) (num den : (Polynomial F)) : (Polynomial (Seeds F)) :=
  ∑ j ∈ Finset.range (e+1), C (f j) * (num^j*den^(e-j)).map MvPolynomial.C

theorem pull_degree {F : Type*} [Field F] (e : ℕ) (f : ℕ → Seeds F)
    {num den : (Polynomial F)} (hn : num.natDegree≤1) (hd : den.natDegree≤1) :
    (pull e f num den).natDegree≤e := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  apply (natDegree_C_mul_le ..).trans (natDegree_map_le.trans (natDegree_mul_le.trans ?_))
  have jle : j≤e := by simpa using Finset.mem_range.mp hj
  have h₁ := natDegree_pow_le_of_le j hn
  have h₂ := natDegree_pow_le_of_le (e-j) hd
  simp only [Nat.mul_one] at h₁ h₂
  omega

theorem pull_axis {F : Type*} [Field F] (e : ℕ) (f : ℕ → Seeds F)
    (num den : (Polynomial F)) (i : Fin 2) {a : ℕ} (h : ∀ j, (f j).degreeOf i≤a) (k : ℕ) :
    ((pull e f num den).coeff k).degreeOf i≤a := by
  classical
  simp only [pull,finsetSum_coeff,coeff_C_mul,coeff_map]
  apply (MvPolynomial.degreeOf_sum_le ..).trans (Finset.sup_le ?_)
  intro j _
  exact (MvPolynomial.degreeOf_mul_le ..).trans (by simpa using h j)

theorem pull_root {F : Type*} [Field F] (e : ℕ) (f : ℕ → Seeds F)
    (ev : Seeds F →+* F) (const : ∀ a, ev (MvPolynomial.C a)=a) (num den : (Polynomial F)) (u y : F)
    (residue : den.eval u*y=num.eval u) (word : ∑ j ∈ Finset.range (e+1), ev (f j)*y^j=0) :
    ((pull e f num den).map ev).eval u=0 := by
  have comp : ev.comp MvPolynomial.C=RingHom.id F := RingHom.ext const
  simp only [pull,Polynomial.map_sum,Polynomial.map_mul,map_C,map_map,comp,map_id,
    eval_finsetSum,eval_mul,eval_C,eval_pow,←residue,mul_pow]
  calc
    _ = (∑ j ∈ Finset.range (e+1), ev (f j)*y^j) * den.eval u^e := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      have h : j+(e-j)=e := by have := Finset.mem_range.mp hj; omega
      rw [show den.eval u^e=den.eval u^j*den.eval u^(e-j) by rw [←pow_add,h]]
      ring
    _ = 0 := by rw [word,zero_mul]

/-- Two prescribed residues at exterior poles suffice if their equations are
coprime generically. The retained seed coordinates stay adjacent. -/
theorem two_probes {F : Type*} [Field F] (p : ℕ) (hp : 0<p) (e a b : ℕ)
    (f g : ℕ → Seeds F) (n₁ d₁ n₂ d₂ : (Polynomial F))
    (linear : n₁.natDegree≤1 ∧ d₁.natDegree≤1 ∧ n₂.natDegree≤1 ∧ d₂.natDegree≤1)
    (fit : ∀ j, (f j).degreeOf 0≤a ∧ (f j).degreeOf 1≤b ∧
      (g j).degreeOf 0≤a ∧ (g j).degreeOf 1≤b)
    (small : 2*e*a<p) (T : Finset F)
    (marks : ∀ z∈T, ∃ u y₁ y₂ : F, d₁.eval u*y₁=n₁.eval u ∧ d₂.eval u*y₂=n₂.eval u ∧
      (∑ j ∈ Finset.range (e+1), MvPolynomial.eval ![z,z^p] (f j)*y₁^j)=0 ∧
      (∑ j ∈ Finset.range (e+1), MvPolynomial.eval ![z,z^p] (g j)*y₂^j)=0)
    (pos : (pull e f n₁ d₁).natDegree≠0 ∨ (pull e g n₂ d₂).natDegree≠0)
    (proper : (pull e f n₁ d₁).resultant (pull e g n₂ d₂) ≠ 0) :
    T.card≤2*e*a+p*(2*e*b) := by
  let P:=pull e f n₁ d₁
  let Q:=pull e g n₂ d₂
  have pdeg : P.natDegree≤e := pull_degree _ _ linear.1 linear.2.1
  have qdeg : Q.natDegree≤e := pull_degree _ _ linear.2.2.1 linear.2.2.2
  have cap (c : ℕ) : Q.natDegree*c+P.natDegree*c≤2*e*c := by
    rw [←Nat.add_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  have bound:=count_common p hp P Q a b a b
    (fun j => ⟨pull_axis _ _ _ _ 0 (fun i => (fit i).1) j,
      pull_axis _ _ _ _ 1 (fun i => (fit i).2.1) j⟩)
    (fun j => ⟨pull_axis _ _ _ _ 0 (fun i => (fit i).2.2.1) j,
      pull_axis _ _ _ _ 1 (fun i => (fit i).2.2.2) j⟩) pos proper ((cap a).trans_lt small) T
    (fun z hz => by
      obtain ⟨u,y₁,y₂,r₁,r₂,h₁,h₂⟩:=marks z hz
      exact ⟨u,pull_root _ _ (MvPolynomial.eval ![z,z^p]) (fun x => MvPolynomial.eval_C x) _ _ _ _ r₁ h₁,
        pull_root _ _ (MvPolynomial.eval ![z,z^p]) (fun x => MvPolynomial.eval_C x) _ _ _ _ r₂ h₂⟩)
  exact bound.trans (Nat.add_le_add (cap a) (Nat.mul_le_mul_left _ (cap b)))

#print axioms two_probes
#print axioms pull_root

/-- The previous mixed-tangent control has just the zero word. Eval at the
full abscissa divisor detects this even before using a conjugate pole. -/
theorem mixed_stress {F : Type*} [Field F] (h₃ h₂ s : (Polynomial F)) (v w : F)
    (d₃ : h₃.natDegree=28000) (d₂ : h₂.natDegree=234144) (hs : s.natDegree≤133606)
    (root : s^2*(s-h₃)+h₃^3*h₂^2*(s-C v-X*C w)=0) : s=0 ∧ v=0 ∧ w=0 := by
  have nz₃ : h₃≠0 := by intro h; simp [h] at d₃
  have nz₂ : h₂≠0 := by intro h; simp [h] at d₂
  have nc := mul_ne_zero (pow_ne_zero 3 nz₃) (pow_ne_zero 2 nz₂)
  have degree : (h₃^3*h₂^2).natDegree=552288 := by
    rw [natDegree_mul (pow_ne_zero 3 nz₃) (pow_ne_zero 2 nz₂),natDegree_pow,natDegree_pow,d₃,d₂]
  have dvd : h₃^3*h₂^2 ∣ s^2*(s-h₃) :=
    ⟨-(s-C v-X*C w),by linear_combination root⟩
  have upper : (s^2*(s-h₃)).natDegree≤400818 := by
    apply natDegree_mul_le.trans
    rw [natDegree_pow]
    have := (natDegree_sub_le s h₃).trans (max_le hs (d₃.le.trans (by decide : 28000≤133606)))
    omega
  have zero : s^2*(s-h₃)=0 := by
    by_contra bad
    have := (natDegree_le_of_dvd dvd bad).trans upper
    omega
  rw [zero,zero_add] at root
  have low := (mul_eq_zero.mp root).resolve_left nc
  have affine : s=C v+X*C w := by linear_combination low
  have slope : s.natDegree≤1 := by
    rw [affine]
    exact (natDegree_add_le ..).trans (max_le (by simp) ((natDegree_mul_C_le ..).trans natDegree_X_le))
  have hzero : s=0 := by
    rcases mul_eq_zero.mp zero with h|h
    · exact (pow_eq_zero_iff (by decide : 2≠0)).mp h
    · rw [sub_eq_zero.mp h,d₃] at slope; omega
  rw [hzero] at affine
  have hv := congrArg (eval 0) affine
  have hw := congrArg (fun P : (Polynomial F) => P.coeff 1) affine
  exact ⟨hzero,by simpa using hv.symm,by simpa [coeff_X_mul] using hw.symm⟩

#print axioms mixed_stress
end Lower6960.ThirdPole
