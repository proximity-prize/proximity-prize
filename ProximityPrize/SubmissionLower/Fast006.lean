import ArkLib.Data.MvPolynomial.WeightedOrder
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.NumberTheory.FLT.MasonStothers
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import ProximityPrize.SubmissionLower.Fast004
import ProximityPrize.SubmissionLower.Fast005
set_option Elab.async false

section PackSource_PrincipalSpan
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F row : Type*} [Field F] [Fintype row]

theorem degreeLT_natDegree_le {q : ℕ} (Q : Polynomial.degreeLT F (q+1)) :
    (Q : F[X]).natDegree ≤ q := by
  by_cases hQ : (Q : F[X]) = 0
  · simp [hQ]
  · have h := (Polynomial.natDegree_lt_iff_degree_lt hQ).mpr
      (Polynomial.mem_degreeLT.mp Q.property)
    omega

/-- Truncated homogeneous multiplication, expressed in coefficient vectors.
The generator may drop ordinary degree; the map is still injective. -/
def multipleCoefficients (g : F[X]) (q t : ℕ) :
    Polynomial.degreeLT F (q+1) →ₗ[F] (Fin (t+1) → F) where
  toFun Q j := (g * (Q : F[X])).coeff j.val
  map_add' Q R := by ext j; simp [mul_add]
  map_smul' c Q := by ext j; simp [mul_smul_comm]

theorem coefficients_injective_bounded (t : ℕ) (P Q : F[X])
    (hP : P.natDegree ≤ t) (hQ : Q.natDegree ≤ t)
    (hcoeff : ∀ j : Fin (t+1), P.coeff j.val = Q.coeff j.val) : P = Q := by
  ext j
  by_cases hj : j < t+1
  · exact hcoeff ⟨j,hj⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

theorem multipleCoefficients_injective (g : F[X]) (a q t : ℕ)
    (hg : g ≠ 0) (hga : g.natDegree ≤ a) (hsize : a+q ≤ t) :
    Function.Injective (multipleCoefficients g q t) := by
  intro Q R hQR
  apply Subtype.ext
  apply mul_left_cancel₀ hg
  apply coefficients_injective_bounded t
  · exact Polynomial.natDegree_mul_le.trans (by have := degreeLT_natDegree_le Q; omega)
  · exact Polynomial.natDegree_mul_le.trans (by have := degreeLT_natDegree_le R; omega)
  · exact fun j => congrFun hQR j

/-- Normal nullity and the independent principal multiples force the whole
fiber to be principal. This is the specialization theorem, including
degree-drop/infinity cases, rather than a hypothesis about bad slopes. -/
theorem normal_kernel_factorization (a q t : ℕ) (M : Matrix row (Fin (t+1)) F)
    (g : F[X]) (hg : g ≠ 0) (hga : g.natDegree ≤ a)
    (hsize : a+q ≤ t)
    (hnull : Module.finrank F (LinearMap.ker M.mulVecLin) = q+1)
    (hshift : ∀ Q : Polynomial.degreeLT F (q+1),
      M.mulVec (multipleCoefficients g q t Q) = 0)
    (E : F[X]) (hE : E.natDegree ≤ t)
    (hker : M.mulVec (fun j : Fin (t+1) => E.coeff j.val) = 0) :
    ∃ Q : F[X], Q.natDegree ≤ q ∧ E = g*Q := by
  let f := multipleCoefficients g q t
  have hinj := multipleCoefficients_injective g a q t hg hga hsize
  have hdim : Module.finrank F (LinearMap.range f) = q+1 := by
    rw [LinearMap.finrank_range_of_inj hinj]
    exact ((Polynomial.degreeLTEquiv F (q+1)).finrank_eq).trans
      (by simp [Module.finrank_fintype_fun_eq_card])
  have hsub : LinearMap.range f ≤ LinearMap.ker M.mulVecLin := by
    rintro _ ⟨Q,rfl⟩
    exact hshift Q
  have heq : LinearMap.range f = LinearMap.ker M.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hsub (hdim.trans hnull.symm)
  have hmem : (fun j : Fin (t+1) => E.coeff j.val) ∈ LinearMap.range f := by
    rw [heq]
    exact hker
  obtain ⟨Q,hQ⟩ := hmem
  refine ⟨Q,degreeLT_natDegree_le Q,?_⟩
  symm
  apply coefficients_injective_bounded t
  · exact Polynomial.natDegree_mul_le.trans (by have := degreeLT_natDegree_le Q; omega)
  · exact hE
  · exact fun j => congrFun hQ j

end
end FrobeniusLocator.Principal
end PackSource_PrincipalSpan

section PackSource_PolynomialFamily
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators

def assemble {R : Type*} [Semiring R] {d : ℕ} (v : Fin (d+1) → R) : R[X] :=
  ∑ j, Polynomial.monomial j.val (v j)

theorem assemble_coeff {R : Type*} [Semiring R] {d : ℕ}
    (v : Fin (d+1) → R) (j : Fin (d+1)) : (assemble v).coeff j.val=v j := by
  classical
  simp only [assemble, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [show b.val ≠ j.val from fun h => hbj (Fin.ext h)]
  · simp

theorem assemble_natDegree_le {R : Type*} [Semiring R] {d : ℕ}
    (v : Fin (d+1) → R) : (assemble v).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_monomial_le (v j)).trans (by omega)

theorem map_assemble {R S : Type*} [Semiring R] [Semiring S] {d : ℕ}
    (φ : R →+* S) (v : Fin (d+1) → R) :
    (assemble v).map φ=assemble (fun j => φ (v j)) := by
  simp [assemble, Polynomial.map_sum]

theorem specialize_eq_assemble {F : Type*} [Field F] {d : ℕ}
    (v : Fin (d+1) → F[X]) (γ : F) :
    specialize v γ=assemble (fun j => (v j).eval γ) := by
  simp only [specialize,assemble,Polynomial.C_mul_X_pow_eq_monomial]

theorem assemble_map_eval {F : Type*} [Field F] {d : ℕ}
    (v : Fin (d+1) → F[X]) (γ : F) :
    (assemble v).map (Polynomial.evalRingHom γ)=specialize v γ := by
  rw [map_assemble,specialize_eq_assemble]
  rfl

theorem assemble_ne_zero {R : Type*} [Semiring R] {d : ℕ}
    (v : Fin (d+1) → R) (hv : v ≠ 0) : assemble v ≠ 0 := by
  intro hz
  apply hv
  funext j
  have h := congrArg (fun f : R[X] => f.coeff j.val) hz
  simpa only [assemble_coeff,coeff_zero,Pi.zero_apply] using h

theorem nodePolynomial_generic_eval {F K : Type*} [Field F] [Field K] {d : ℕ}
    (φ : F[X] →+* K) (v : Fin (d+1) → F[X]) (x : F) :
    φ (nodePolynomial v x) = (assemble (fun j => φ (v j))).eval (φ (C x)) := by
  simp only [nodePolynomial,map_sum,map_mul,assemble,Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro j _
  have hp : φ (C (x^j.val))=(φ (C x))^j.val := by rw [← map_pow,← Polynomial.C_pow]
  rw [hp,mul_comm]

variable {R S row col : Type*} [CommRing R] [CommRing S] [Fintype col]

/-- Polynomial kernel identities commute with arbitrary coefficient maps. -/
theorem family_kernel_map (φ : R →+* S) (M : Matrix row col R)
    (P : R[X]) (indices : col → ℕ)
    (hker : M.mulVec (fun j => P.coeff (indices j))=0) :
    (M.map φ).mulVec (fun j => (P.map φ).coeff (indices j))=0 := by
  funext i
  have hi := congrArg φ (congrFun hker i)
  simpa only [Matrix.mulVec,dotProduct,map_sum,map_mul,map_zero,
    Polynomial.coeff_map,Matrix.map_apply,Pi.zero_apply] using hi

/-- Injectivity reflects a generic family-kernel identity to the polynomial
coefficient ring, making it valid at every finite specialization. -/
theorem family_kernel_of_map (φ : R →+* S) (hφ : Function.Injective φ)
    (M : Matrix row col R) (P : R[X]) (indices : col → ℕ)
    (hker : (M.map φ).mulVec (fun j => (P.map φ).coeff (indices j))=0) :
    M.mulVec (fun j => P.coeff (indices j))=0 := by
  funext i
  apply hφ
  have hi := congrFun hker i
  simpa only [Matrix.mulVec,dotProduct,map_sum,map_mul,map_zero,
    Polynomial.coeff_map,Matrix.map_apply,Pi.zero_apply] using hi

end
end FrobeniusLocator.Principal
end PackSource_PolynomialFamily

section PackSource_PrincipalRecurrence
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset
open scoped BigOperators
variable {K : Type*} [Field K]

/-- A syndrome functional against a polynomial and a shifted sequence. -/
def recurrenceEval (s : ℕ → K) (j : ℕ) : K[X] →ₗ[K] K where
  toFun f := f.sum (fun i c => c*s (i+j))
  map_add' f g := Polynomial.sum_add_index f g _ (fun _ => by simp)
    (fun _ _ _ => by ring)
  map_smul' c f := by
    rw [Polynomial.sum_smul_index _ _ _ (fun _ => by simp)]
    simp only [RingHom.id_apply, smul_eq_mul, Polynomial.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem recurrenceEval_monomial (s : ℕ → K) (j i : ℕ) (c : K) :
    recurrenceEval s j (monomial i c) = c*s (i+j) := by
  change (monomial i c : K[X]).sum (fun n a => a*s (n+j)) = _
  exact Polynomial.sum_monomial_index c (fun n a => a*s (n+j)) (zero_mul _)

theorem recurrenceEval_shift (s : ℕ → K) (j l : ℕ) (f : K[X]) :
    recurrenceEval s j (f*X^l) = recurrenceEval s (j+l) f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [add_mul, map_add, hf, hg]
  | monomial i c =>
    rw [X_pow_eq_monomial, Polynomial.monomial_mul_monomial,
      mul_one, recurrenceEval_monomial, recurrenceEval_monomial]
    congr 2
    omega

/-- Homogeneous degree-t recurrence kernel, represented by ordinary
polynomials of degree at most t. Lower ordinary degree records infinity. -/
def InRecurrenceKernel (s : Fin 2 → ℕ → K) (m t : ℕ) (f : K[X]) : Prop :=
  f.natDegree ≤ t ∧ ∀ b j, j < m-t → recurrenceEval (s b) j f = 0

/-- Shift equations of the degree-t principal module recover every
degree-a recurrence equation. This is valid with roots at infinity. -/
theorem generator_in_small_kernel (s : Fin 2 → ℕ → K) (m a q : ℕ)
    (hL : a+q < m) (g : K[X]) (hga : g.natDegree ≤ a)
    (hshift : ∀ l ≤ q, InRecurrenceKernel s m (a+q) (g*X^l)) :
    InRecurrenceKernel s m a g := by
  refine ⟨hga,?_⟩
  intro b j hj
  let l := min j q
  let i := j-l
  have hl : l ≤ q := min_le_right _ _
  have hlj : l ≤ j := min_le_left _ _
  have hi : i < m-(a+q) := by dsimp [i,l]; omega
  have hij : i+l=j := by dsimp [i]; omega
  have h := (hshift l hl).2 b i hi
  rw [recurrenceEval_shift, hij] at h
  exact h

theorem small_kernel_shifts (s : Fin 2 → ℕ → K) (m a q : ℕ)
    (hsize : a+q ≤ m) (f : K[X]) (hf : InRecurrenceKernel s m a f)
    (l : ℕ) (hl : l ≤ q) : InRecurrenceKernel s m (a+q) (f*X^l) := by
  refine ⟨?_,?_⟩
  · have hdegree := hf.1
    exact Polynomial.natDegree_mul_le.trans (by simp only [natDegree_X_pow]; omega)
  · intro b j hj
    rw [recurrenceEval_shift]
    exact hf.2 b (j+l) (by omega)

/-- A principal degree-t homogeneous kernel has a one-dimensional
degree-a kernel. The highest-shift test prevents a hidden infinity gap. -/
theorem principal_small_kernel_line (s : Fin 2 → ℕ → K) (m a q : ℕ)
    (hsize : a+q ≤ m) (g : K[X]) (hg : g ≠ 0)
    (hprincipal : ∀ f : K[X], InRecurrenceKernel s m (a+q) f ↔
      ∃ Q : K[X], Q.natDegree ≤ q ∧ f=g*Q)
    (f : K[X]) (hf : InRecurrenceKernel s m a f) :
    ∃ c : K, f=c • g := by
  have hfirst := small_kernel_shifts s m a q hsize f hf 0 (by omega)
  simp only [pow_zero, mul_one] at hfirst
  obtain ⟨Q,hQ,hfQ⟩ := (hprincipal f).mp hfirst
  have hlast := small_kernel_shifts s m a q hsize f hf q (by omega)
  obtain ⟨R,hR,hfR⟩ := (hprincipal (f*X^q)).mp hlast
  have hQR : Q*X^q=R := by
    apply mul_left_cancel₀ hg
    rw [← mul_assoc, ← hfQ, hfR]
  by_cases hQ0 : Q=0
  · exact ⟨0,by simp [hfQ,hQ0]⟩
  have hQdegree : Q.natDegree=0 := by
    have hdeg := Polynomial.natDegree_mul hQ0 (pow_ne_zero q X_ne_zero)
    rw [hQR, natDegree_X_pow] at hdeg
    omega
  have hQC : Q=C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hQdegree
  refine ⟨Q.coeff 0,?_⟩
  rw [hfQ,hQC]
  simp only [Polynomial.smul_eq_C_mul, coeff_C_zero]
  ring

end
end FrobeniusLocator.Principal
end PackSource_PrincipalRecurrence

section PackSource_PolynomialRestriction
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators

variable {R row : Type*} [CommRing R]

def multiplicationMatrix (H : R[X]) (a d : ℕ) :
    Matrix (Fin (a+1)) (Fin (d+1)) R :=
  fun l j => (H*X^j.val).coeff l.val

def restrictByFamily (a d : ℕ) (M : Matrix row (Fin (a+1)) R) (H : R[X]) :
    Matrix row (Fin (d+1)) R := M*multiplicationMatrix H a d

theorem multiplicationMatrix_mulVec (H : R[X]) (a d : ℕ) (c : Fin (d+1) → R) :
    (multiplicationMatrix H a d).mulVec c =
      (fun l : Fin (a+1) => (H*assemble c).coeff l.val) := by
  funext l
  simp only [multiplicationMatrix,Matrix.mulVec,dotProduct,assemble]
  rw [Finset.mul_sum,Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  have heq : H*(C (c j)*X^j.val) = c j • (H*X^j.val) := by
    rw [Polynomial.smul_eq_C_mul]
    ring
  rw [heq,Polynomial.coeff_smul,smul_eq_mul,mul_comm]

theorem restrictByFamily_mulVec (a d : ℕ) (M : Matrix row (Fin (a+1)) R) (H : R[X])
    (c : Fin (d+1) → R) :
    (restrictByFamily a d M H).mulVec c =
      M.mulVec (fun l : Fin (a+1) => (H*assemble c).coeff l.val) := by
  rw [restrictByFamily,← Matrix.mulVec_mulVec,multiplicationMatrix_mulVec]

theorem restrictByFamily_map {S : Type*} [CommRing S]
    (a d : ℕ) (φ : R →+* S) (M : Matrix row (Fin (a+1)) R) (H : R[X]) :
    (restrictByFamily a d M H).map φ =
      restrictByFamily a d (M.map φ) (H.map φ) := by
  ext i j
  simp only [restrictByFamily,Matrix.mul_apply,Matrix.map_apply,map_sum,map_mul,
    multiplicationMatrix,Polynomial.coeff_map]
  apply Finset.sum_congr rfl
  intro l _
  have heq : φ ((H*X^j.val).coeff l.val) = (H.map φ*X^j.val).coeff l.val := by
    rw [← Polynomial.coeff_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
  rw [heq]

theorem assemble_coefficients {K : Type*} [Field K] (d : ℕ) (P : K[X])
    (hP : P.natDegree ≤ d) : assemble (fun j : Fin (d+1) => P.coeff j.val)=P := by
  apply coefficients_injective_bounded d
  · exact assemble_natDegree_le _
  · exact hP
  · intro j
    exact assemble_coeff _ j

theorem restricted_natDegree_le {F : Type*} [Field F] (a d : ℕ)
    (M : Matrix row (Fin (a+1)) F[X]) (H : F[X]) (cost : row → ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ cost i) (i : row) (j : Fin (d+1)) :
    (restrictByFamily a d M (H.map (Polynomial.C : F →+* F[X])) i j).natDegree ≤ cost i := by
  simp only [restrictByFamily,Matrix.mul_apply,multiplicationMatrix]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro l _
  have hcoeff : ((H.map (Polynomial.C : F →+* F[X]))*(Polynomial.X : F[X][X])^j.val).coeff l.val =
      (Polynomial.C : F →+* F[X]) ((H*(Polynomial.X : F[X])^j.val).coeff l.val) := by
    have heq : (H*(Polynomial.X : F[X])^j.val).map (Polynomial.C : F →+* F[X]) =
        H.map (Polynomial.C : F →+* F[X])*(Polynomial.X : F[X][X])^j.val := by
      rw [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
    have hc := congrArg (fun P : F[X][X] => P.coeff l.val) heq
    simpa only [Polynomial.coeff_map] using hc.symm
  change (M i l*((H.map (Polynomial.C : F →+* F[X]))*(Polynomial.X : F[X][X])^j.val).coeff l.val).natDegree ≤ _
  rw [hcoeff,mul_comm]
  exact (Polynomial.natDegree_C_mul_le _ _).trans (hM i l)

variable {K : Type*} [Field K]

/-- Removing a fixed polynomial factor from a one-dimensional homogeneous
kernel leaves a one-dimensional restricted kernel, even at infinity. -/
theorem restricted_kernel_line (a h d : ℕ) (hah : h+d=a)
    (M : Matrix row (Fin (a+1)) K) (H f : K[X])
    (hH : H ≠ 0) (hHd : H.natDegree ≤ h) (hfd : f.natDegree ≤ d)
    (hkernel : LinearMap.ker M.mulVecLin =
      K ∙ (fun j : Fin (a+1) => (H*f).coeff j.val)) :
    LinearMap.ker (restrictByFamily a d M H).mulVecLin =
      K ∙ (fun j : Fin (d+1) => f.coeff j.val) := by
  have hHf : (H*f).natDegree ≤ a := Polynomial.natDegree_mul_le.trans (by omega)
  apply le_antisymm
  · intro c hc
    have hc' : (restrictByFamily a d M H).mulVec c=0 := hc
    rw [restrictByFamily_mulVec] at hc'
    have hmem : (fun j : Fin (a+1) => (H*assemble c).coeff j.val) ∈
        K ∙ (fun j : Fin (a+1) => (H*f).coeff j.val) := by
      rw [← hkernel]
      exact hc'
    obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp hmem
    have heq : H*assemble c=b • (H*f) := by
      apply coefficients_injective_bounded a
      · exact Polynomial.natDegree_mul_le.trans (by have := assemble_natDegree_le c; omega)
      · exact (Polynomial.natDegree_smul_le _ _).trans hHf
      · intro j
        have hh := congrFun hb j
        simpa only [Polynomial.coeff_smul,Pi.smul_apply,smul_eq_mul] using hh.symm
    have hcancel : assemble c=b • f := by
      apply mul_left_cancel₀ hH
      simpa only [mul_smul_comm] using heq
    apply Submodule.mem_span_singleton.mpr
    refine ⟨b,?_⟩
    funext j
    have hh := congrArg (fun P : K[X] => P.coeff j.val) hcancel
    simpa only [assemble_coeff,Polynomial.coeff_smul,Pi.smul_apply,smul_eq_mul] using hh.symm
  · apply Submodule.span_le.mpr
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    subst c
    change (restrictByFamily a d M H).mulVec _=0
    rw [restrictByFamily_mulVec,assemble_coefficients d f hfd]
    have hmem : (fun j : Fin (a+1) => (H*f).coeff j.val) ∈
        K ∙ (fun j : Fin (a+1) => (H*f).coeff j.val) := Submodule.mem_span_singleton_self _
    rw [← hkernel] at hmem
    exact hmem

end
end FrobeniusLocator.Principal
end PackSource_PolynomialRestriction

section PackSource_RecurrenceMatrix
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {K : Type*} [Field K]

def recurrenceMatrix (s : Fin 2 → ℕ → K) (m t : ℕ) :
    Matrix (Fin 2 × Fin (m-t)) (Fin (t+1)) K :=
  fun i j => s i.1 (i.2.val+j.val)

theorem recurrenceEval_eq_sum (s : ℕ → K) (j t : ℕ) (f : K[X])
    (hf : f.natDegree ≤ t) :
    recurrenceEval s j f = ∑ i : Fin (t+1), f.coeff i.val*s (i.val+j) := by
  change f.sum (fun i c => c*s (i+j)) = _
  rw [Fin.sum_univ_eq_sum_range (fun i => f.coeff i*s (i+j)) (t+1)]
  apply Polynomial.sum_eq_of_subset _ (fun _ => by simp)
  intro i hi
  apply Finset.mem_range.mpr
  have := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi)
  omega

theorem recurrence_kernel_iff_matrix (s : Fin 2 → ℕ → K) (m t : ℕ) (f : K[X]) :
    InRecurrenceKernel s m t f ↔ f.natDegree ≤ t ∧
      (recurrenceMatrix s m t).mulVec (fun i => f.coeff i.val) = 0 := by
  constructor
  · rintro ⟨hf,hrec⟩
    refine ⟨hf,?_⟩
    funext i
    have hh := hrec i.1 i.2.val i.2.isLt
    rw [recurrenceEval_eq_sum _ _ t f hf] at hh
    simpa only [recurrenceMatrix, Matrix.mulVec, dotProduct, Nat.add_comm,
      mul_comm, Pi.zero_apply] using hh
  · rintro ⟨hf,hker⟩
    refine ⟨hf,?_⟩
    intro b j hj
    rw [recurrenceEval_eq_sum _ _ t f hf]
    have hh := congrFun hker (b,⟨j,hj⟩)
    simpa only [recurrenceMatrix, Matrix.mulVec, dotProduct, Nat.add_comm,
      mul_comm, Pi.zero_apply] using hh

/-- Exact generic principal homogeneous kernel hypothesis, with nominal
degree a rather than ordinary degree exactly a. -/
structure PrincipalAt (s : Fin 2 → ℕ → K) (m a q : ℕ) where
  generator : K[X]
  nonzero : generator ≠ 0
  degree_bound : generator.natDegree ≤ a
  kernel_eq : ∀ f : K[X], InRecurrenceKernel s m (a+q) f ↔
    ∃ Q : K[X], Q.natDegree ≤ q ∧ f=generator*Q

theorem PrincipalAt.generator_small {s : Fin 2 → ℕ → K} {m a q : ℕ}
    (P : PrincipalAt s m a q) (hL : a+q < m) :
    InRecurrenceKernel s m a P.generator := by
  apply generator_in_small_kernel s m a q hL P.generator P.degree_bound
  intro l hl
  apply (P.kernel_eq _).mpr
  exact ⟨X^l,by simpa using hl,rfl⟩

/-- The small locator matrix has exactly the generator line as kernel.
This is the algebraic step needed before selecting bounded cofactors. -/
theorem PrincipalAt.small_kernel_line {s : Fin 2 → ℕ → K} {m a q : ℕ}
    (P : PrincipalAt s m a q) (hL : a+q < m) :
    LinearMap.ker (recurrenceMatrix s m a).mulVecLin =
      K ∙ (fun i : Fin (a+1) => P.generator.coeff i.val) := by
  have hgen := (recurrence_kernel_iff_matrix s m a P.generator).mp (P.generator_small hL)
  apply le_antisymm
  · intro c hc
    let f := (Polynomial.degreeLTEquiv K (a+1)).symm c
    have hfdeg : (f : K[X]).natDegree ≤ a := degreeLT_natDegree_le f
    have hfcoeff : ∀ i : Fin (a+1), (f : K[X]).coeff i.val=c i := by
      intro i
      exact congrFun ((Polynomial.degreeLTEquiv K (a+1)).apply_symm_apply c) i
    have hrec : InRecurrenceKernel s m a (f : K[X]) := by
      apply (recurrence_kernel_iff_matrix s m a _).mpr
      refine ⟨hfdeg,?_⟩
      have hc' : (recurrenceMatrix s m a).mulVec c=0 := hc
      simpa only [hfcoeff] using hc'
    obtain ⟨b,hb⟩ := principal_small_kernel_line s m a q (by omega)
      P.generator P.nonzero P.kernel_eq f hrec
    apply Submodule.mem_span_singleton.mpr
    refine ⟨b,?_⟩
    funext i
    have hbi := congrArg (fun f : K[X] => f.coeff i.val) hb
    simpa only [hfcoeff, Polynomial.coeff_smul, Pi.smul_apply, smul_eq_mul] using hbi.symm
  · apply Submodule.span_le.mpr
    intro c hc
    rw [Set.mem_singleton_iff] at hc
    exact hc ▸ hgen.2

theorem PrincipalAt.small_nullity_one {s : Fin 2 → ℕ → K} {m a q : ℕ}
    (P : PrincipalAt s m a q) (hL : a+q < m) :
    Module.finrank K (LinearMap.ker (recurrenceMatrix s m a).mulVecLin) = 1 := by
  rw [P.small_kernel_line hL]
  apply finrank_span_singleton
  intro hzero
  have hcoeff : ∀ i : Fin (a+1), P.generator.coeff i.val=(0:K[X]).coeff i.val := by
    intro i
    simpa using congrFun hzero i
  exact P.nonzero (coefficients_injective_bounded a P.generator 0 P.degree_bound
    (by simp) hcoeff)

end
end FrobeniusLocator.Principal
end PackSource_RecurrenceMatrix

section PackSource_RecurrenceFamily
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {K : Type*} [Field K]

theorem small_kernel_multiples (s : Fin 2 → ℕ → K) (m a q : ℕ)
    (hsize : a+q ≤ m) (f Q : K[X]) (hf : InRecurrenceKernel s m a f)
    (hQ : Q.natDegree ≤ q) : InRecurrenceKernel s m (a+q) (f*Q) := by
  refine ⟨Polynomial.natDegree_mul_le.trans (Nat.add_le_add hf.1 hQ),?_⟩
  intro b i hi
  have hterm (j : Fin (q+1)) :
      recurrenceEval (s b) i (f*Polynomial.monomial j.val (Q.coeff j.val))=0 := by
    have hpoly : f*Polynomial.monomial j.val (Q.coeff j.val) =
        Q.coeff j.val • (f*X^j.val) := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial,Polynomial.smul_eq_C_mul]
      ring
    rw [hpoly,map_smul]
    have hz := (small_kernel_shifts s m a q hsize f hf j.val (by omega)).2 b i hi
    rw [hz,smul_zero]
  calc
    _ = ∑ j : Fin (q+1), recurrenceEval (s b) i
        (f*Polynomial.monomial j.val (Q.coeff j.val)) := by
      conv_lhs => rw [← assemble_coefficients q Q hQ,assemble,Finset.mul_sum,map_sum]
    _ = 0 := Finset.sum_eq_zero (fun j _ => hterm j)

theorem PrincipalAt.big_nullity {s : Fin 2 → ℕ → K} {m a q : ℕ}
    (P : PrincipalAt s m a q) :
    Module.finrank K (LinearMap.ker (recurrenceMatrix s m (a+q)).mulVecLin)=q+1 := by
  let M := recurrenceMatrix s m (a+q)
  let f := multipleCoefficients P.generator q (a+q)
  have hinj := multipleCoefficients_injective P.generator a q (a+q)
    P.nonzero P.degree_bound (by omega)
  have heq : LinearMap.range f=LinearMap.ker M.mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨Q,rfl⟩
      have hrec := (P.kernel_eq _).mpr ⟨Q,degreeLT_natDegree_le Q,rfl⟩
      exact ((recurrence_kernel_iff_matrix s m (a+q) _).mp hrec).2
    · intro c hc
      let E := assemble c
      have hE : InRecurrenceKernel s m (a+q) E := by
        apply (recurrence_kernel_iff_matrix s m (a+q) E).mpr
        refine ⟨assemble_natDegree_le _,?_⟩
        have hc' : M.mulVec c=0 := hc
        simpa only [E,assemble_coeff] using hc'
      obtain ⟨Q,hQ,hEQ⟩ := (P.kernel_eq E).mp hE
      refine ⟨⟨Q,Polynomial.mem_degreeLT.mpr
        (Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast (show Q.natDegree<q+1 by omega)))⟩,?_⟩
      funext j
      change (P.generator*Q).coeff j.val=c j
      rw [← hEQ]
      exact assemble_coeff c j
  rw [← heq,LinearMap.finrank_range_of_inj hinj]
  exact ((Polynomial.degreeLTEquiv K (q+1)).finrank_eq).trans (by simp)

variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]

def parameterSyndromes (p : ℕ) (x u v : ι → F) (b : Fin 2) (j : ℕ) : F[X] :=
  if b=0 then C (syndrome x u j)+X*C (syndrome x v j)
  else C (syndrome x u j ^ p)+X^p*C (syndrome x v j ^ p)

theorem recurrenceMatrix_parameter (φ : F[X] →+* K) (p : ℕ) (x u v : ι → F)
    (m t : ℕ) : recurrenceMatrix (fun b j => φ (parameterSyndromes p x u v b j)) m t =
      (stacked p x u v (m-t) t).map φ := by
  rfl

/-- A polynomial family in the small kernel supplies every homogeneous
multiple in the large specialized kernel, including rank-drop slopes. -/
theorem family_multiples_annihilate (p : ℕ) (x u v : ι → F) (m a q : ℕ)
    (hsize : a+q ≤ m) (P : F[X][X]) (hP : P.natDegree ≤ a)
    (hker : (stacked p x u v (m-a) a).mulVec
      (fun j : Fin (a+1) => P.coeff j.val)=0)
    (γ : F) (Q : Polynomial.degreeLT F (q+1)) :
    ((stacked p x u v (m-(a+q)) (a+q)).map (Polynomial.evalRingHom γ)).mulVec
      (multipleCoefficients (P.map (Polynomial.evalRingHom γ)) q (a+q) Q)=0 := by
  let s := fun b j => (parameterSyndromes p x u v b j).eval γ
  have hsmall : InRecurrenceKernel s m a (P.map (Polynomial.evalRingHom γ)) := by
    apply (recurrence_kernel_iff_matrix s m a _).mpr
    refine ⟨Polynomial.natDegree_map_le.trans hP,?_⟩
    change ((stacked p x u v (m-a) a).map (Polynomial.evalRingHom γ)).mulVec
      (fun i : Fin (a+1) => (P.map (Polynomial.evalRingHom γ)).coeff i.val)=0
    exact family_kernel_map (Polynomial.evalRingHom γ) _ P (fun j : Fin (a+1) => j.val) hker
  have hbig := small_kernel_multiples s m a q hsize _ Q hsmall (degreeLT_natDegree_le Q)
  have hbigM := ((recurrence_kernel_iff_matrix s m (a+q) _).mp hbig).2
  change ((stacked p x u v (m-(a+q)) (a+q)).map (Polynomial.evalRingHom γ)).mulVec
    (fun i : Fin (a+q+1) => ((P.map (Polynomial.evalRingHom γ))*(Q:F[X])).coeff i.val)=0 at hbigM
  exact hbigM

end
end FrobeniusLocator.Principal
end PackSource_RecurrenceFamily

section PackSource_RankDropCharge
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Strata
noncomputable section
open Polynomial Matrix Finset
open scoped BigOperators
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- Every rank exception is a zero of the SAME selected minor. Full
ordinary rank retains L cheap rows in its degree ledger. -/
theorem two_block_rank_exception_count (p : ℕ) [ExpChar F p]
    (x u v : ι → F) (L t r : ℕ)
    (hr : GenericLayer.genericRank (stacked p x u v L t)=t+1-r)
    (hfirst : GenericLayer.genericRank (hankel x u v L t)=L)
    (Γ : Finset F) (hΓ : ∀ γ∈Γ,
      ((stacked p x u v L t).map (evalRingHom γ)).rank ≠ t+1-r) :
    Γ.card ≤ L+p*(t+1-r-L) := by
  obtain ⟨B,hledger,hdeg⟩ :=
    GenericLayer.exists_frobenius_basis p x u v L t r hr hfirst
  apply (Polynomial.card_le_degree_of_subset_roots ?_).trans hdeg
  intro γ hγ
  apply (Polynomial.mem_roots B.minor_ne).mpr
  by_contra hn
  exact hΓ γ hγ (NormalFiber.rank_specializes _
    (IsFractionRing.injective F[X] (GenericLayer.GenericField F)) _ _ B γ hn)

/-- Exact first-cell bound, uniform in all r≥7. This counts every rank
exception, so applies in particular to its MCA-bad subset. -/
theorem native_rank_exception_count [ExpChar F 2130706433]
    (x u v : ι → F) (r : ℕ) (hr7 : 7≤r)
    (hr : GenericLayer.genericRank (stacked 2130706433 x u v 49164 81908)=81909-r)
    (hfirst : GenericLayer.genericRank (hankel x u v 49164 81908)=49164)
    (Γ : Finset F) (hΓ : ∀ γ∈Γ,
      ((stacked 2130706433 x u v 49164 81908).map (evalRingHom γ)).rank ≠ 81909-r) :
    Γ.card ≤ 69755067252718 := by
  have hb := two_block_rank_exception_count 2130706433 x u v 49164 81908 r hr hfirst Γ hΓ
  have hs : 81908+1-r-49164 ≤ 32738 := by omega
  have hm := Nat.mul_le_mul_left 2130706433 hs
  omega

end
end FrobeniusLocator.Strata
end PackSource_RankDropCharge

section PackSource_K1_6_2Aux1
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false

namespace K1_6_2

open Polynomial Matrix Finset
open FrobeniusLocator
open scoped BigOperators

private def unitColumns {R row col : Type*} [Zero R] [One R] [DecidableEq row]
    (rows : col → row) : Matrix row col R :=
  fun i j => (Pi.single (rows j) 1 : row → R) i

private theorem transpose_mul_unitColumns {R row col pick : Type*}
    [CommRing R] [Fintype row] [DecidableEq row]
    (W : Matrix row col R) (rows : pick → row) :
    W.transpose * unitColumns rows = (W.submatrix rows id).transpose := by
  ext i j
  change W.transpose.mulVec (Pi.single (rows j) 1) i = _
  rw [Matrix.mulVec_single_one]
  rfl

variable {E : Type*} [Field E] {r s : ℕ}

/-- With a nonzero kernel minor, adjoining the corresponding coordinate
columns gives a square matrix with trivial kernel. -/
private theorem augmentation_det_ne_zero
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) E)
    (W : Matrix (Fin r ⊕ Fin s) (Fin s) E)
    (hWC : W.transpose * C = 0)
    (hC : ∀ a, C.mulVec a = 0 → a = 0)
    (rows : Fin s → (Fin r ⊕ Fin s)) (hminor : (W.submatrix rows id).det ≠ 0) :
    (Matrix.fromCols C (unitColumns rows)).det ≠ 0 := by
  let A := Matrix.fromCols C (unitColumns rows)
  have hker : ∀ v, A.mulVec v = 0 → v = 0 := by
    intro v hv
    have hz := congrArg W.transpose.mulVec hv
    change W.transpose.mulVec ((Matrix.fromCols C (unitColumns rows)).mulVec v) =
      W.transpose.mulVec 0 at hz
    rw [Matrix.mulVec_zero, Matrix.fromCols_mulVec, Matrix.mulVec_add,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hWC, Matrix.zero_mulVec,
      zero_add, transpose_mul_unitColumns] at hz
    have hs : v ∘ Sum.inr = 0 :=
      Matrix.eq_zero_of_mulVec_eq_zero (by simpa only [Matrix.det_transpose] using hminor) hz
    change (Matrix.fromCols C (unitColumns rows)).mulVec v = 0 at hv
    rw [Matrix.fromCols_mulVec, hs, Matrix.mulVec_zero, add_zero] at hv
    have hr := hC _ hv
    funext i
    cases i with
    | inl i => exact congrFun hr i
    | inr i => exact congrFun hs i
  have hinj : Function.Injective A.mulVec := by
    intro u v huv
    exact sub_eq_zero.mp (hker (u - v) (by rw [Matrix.mulVec_sub, huv, sub_self]))
  exact ((Matrix.isUnit_iff_isUnit_det A).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)).ne_zero

/-- Unit-column augmentations encode signed complementary minors. Over
the field they are proportional to the minors of the annihilator. -/
private theorem augmented_minor_cross
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) E)
    (W : Matrix (Fin r ⊕ Fin s) (Fin s) E)
    (hWC : W.transpose * C = 0)
    (hC : ∀ a, C.mulVec a = 0 → a = 0)
    (rows : Fin s → (Fin r ⊕ Fin s)) (hminor : (W.submatrix rows id).det ≠ 0) :
    (Matrix.fromCols C (unitColumns rows)).det ≠ 0 ∧
    ∀ pick : Fin s → (Fin r ⊕ Fin s),
      (Matrix.fromCols C (unitColumns pick)).det * (W.submatrix rows id).det =
        (Matrix.fromCols C (unitColumns rows)).det * (W.submatrix pick id).det := by
  let A := Matrix.fromCols C (unitColumns rows)
  have hA := augmentation_det_ne_zero C W hWC hC rows hminor
  refine ⟨hA, ?_⟩
  intro pick
  let B := Matrix.fromCols C (unitColumns pick)
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  let T := A⁻¹ * B
  let J : Matrix (Fin r ⊕ Fin s) (Fin r) E := Matrix.fromRows 1 0
  have hAJ : A * J = C := by
    simp only [A, J, Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
  have hfirst : T.submatrix id Sum.inl = J := by
    change A⁻¹ * C = J
    rw [← hAJ, Matrix.nonsing_inv_mul_cancel_left A J hunit]
  let D := T.submatrix Sum.inr Sum.inr
  have hT : T = Matrix.fromBlocks 1 (T.submatrix Sum.inl Sum.inr) 0 D := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrFun (congrFun hfirst (Sum.inl i)) j
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j => exact congrFun (congrFun hfirst (Sum.inr i)) j
      | inr j => rfl
  have hAT : A * T = B := Matrix.mul_nonsing_inv_cancel_left A B hunit
  have hWaug (I : Fin s → (Fin r ⊕ Fin s)) :
      W.transpose * Matrix.fromCols C (unitColumns I) =
        Matrix.fromCols 0 (W.submatrix I id).transpose := by
    rw [Matrix.mul_fromCols, hWC, transpose_mul_unitColumns]
  have hbottom : (W.submatrix rows id).transpose * D = (W.submatrix pick id).transpose := by
    have hh : (W.transpose * A) * T = W.transpose * B := by rw [Matrix.mul_assoc, hAT]
    change (W.transpose * Matrix.fromCols C (unitColumns rows)) * T =
      W.transpose * Matrix.fromCols C (unitColumns pick) at hh
    rw [hWaug, hWaug, hT, Matrix.fromCols_mul_fromBlocks, Matrix.zero_mul,
      Matrix.mul_zero, zero_add, Matrix.zero_mul, zero_add] at hh
    exact congrArg (fun M : Matrix (Fin s) (Fin r ⊕ Fin s) E => M.submatrix id Sum.inr) hh
  have hdetD : (W.submatrix rows id).det * D.det = (W.submatrix pick id).det := by
    simpa only [Matrix.det_mul, Matrix.det_transpose] using congrArg Matrix.det hbottom
  have hdetT : T.det = D.det := by
    rw [hT, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  have hdetB : B.det = A.det * D.det := by
    rw [← hAT, Matrix.det_mul, hdetT]
  change B.det * (W.submatrix rows id).det = A.det * (W.submatrix pick id).det
  rw [hdetB, ← hdetD]
  ring

variable {F : Type*} [Field F]

/-- Each adjoined constant column saves one from the total row budget. -/
private theorem augmented_det_degree
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) F[X])
    (d : (Fin r ⊕ Fin s) → ℕ) (hpositive : ∀ i, 1 ≤ d i)
    (hdegree : ∀ i j, (C i j).natDegree ≤ d i)
    (rows : Fin s → (Fin r ⊕ Fin s)) :
    (Matrix.fromCols C (unitColumns rows)).det.natDegree ≤ (∑ i, d i) - s := by
  classical
  let A := Matrix.fromCols C (unitColumns rows : Matrix _ _ F[X])
  change A.det.natDegree ≤ _
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  have hsign : (Equiv.Perm.sign σ • ∏ j, A (σ j) j).natDegree =
      (∏ j, A (σ j) j).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, one_smul]
    · rw [h, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
  rw [hsign]
  let saving : (Fin r ⊕ Fin s) → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)
  have hpoint (j : Fin r ⊕ Fin s) : (A (σ j) j).natDegree + saving j ≤ d (σ j) := by
    cases j with
    | inl j => simpa [A, saving] using hdegree (σ (Sum.inl j)) j
    | inr j =>
      change ((Pi.single (rows j) 1 : Fin r ⊕ Fin s → F[X])
        (σ (Sum.inr j))).natDegree + 1 ≤
        d (σ (Sum.inr j))
      simp only [Pi.single_apply]
      split_ifs <;> simpa only [Polynomial.natDegree_one, Polynomial.natDegree_zero, zero_add]
        using hpositive (σ (Sum.inr j))
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint j)
  have hsaving : (∑ j, saving j) = s := by simp [saving, Fintype.sum_sum_type]
  rw [Finset.sum_add_distrib, hsaving, Equiv.sum_comp σ d] at hsum
  have hprod := Polynomial.natDegree_prod_le Finset.univ (fun j => A (σ j) j)
  omega

private theorem map_augmentation (φ : F[X] →+* E)
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) F[X]) (rows : Fin s → (Fin r ⊕ Fin s)) :
    φ (Matrix.fromCols C (unitColumns rows)).det =
      (Matrix.fromCols (C.map φ) (unitColumns rows)).det := by
  rw [φ.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j
  cases j with
  | inl j => rfl
  | inr j =>
    change φ ((Pi.single (rows j) 1 : Fin r ⊕ Fin s → F[X]) i) =
      (Pi.single (rows j) 1 : Fin r ⊕ Fin s → E) i
    simp only [Pi.single_apply]
    split_ifs <;> simp

/-- Bézout converts fraction-field proportionality into polynomial
divisibility by the primitive minor. -/
theorem primitive_minor_degree (φ : F[X] →+* E) (hφ : Function.Injective φ)
    (C : Matrix (Fin r ⊕ Fin s) (Fin r) F[X])
    (W : Matrix (Fin r ⊕ Fin s) (Fin s) F[X])
    (hWC : (W.map φ).transpose * (C.map φ) = 0)
    (hC : ∀ a, (C.map φ).mulVec a = 0 → a = 0)
    (hprim : PrimitiveVector.IsPrimitive
      (fun I : Fin s → (Fin r ⊕ Fin s) => (W.submatrix I id).det))
    (d : (Fin r ⊕ Fin s) → ℕ) (hpositive : ∀ i, 1 ≤ d i)
    (hdegree : ∀ i j, (C i j).natDegree ≤ d i)
    (rows : Fin s → (Fin r ⊕ Fin s)) :
    (W.submatrix rows id).det.natDegree ≤ (∑ i, d i) - s := by
  classical
  let P (I : Fin s → (Fin r ⊕ Fin s)) := (W.submatrix I id).det
  let A (I : Fin s → (Fin r ⊕ Fin s)) := (Matrix.fromCols C (unitColumns I)).det
  change (P rows).natDegree ≤ _
  by_cases hP : P rows = 0
  · simp [hP]
  have hmap (I : Fin s → (Fin r ⊕ Fin s)) : φ (P I) = ((W.map φ).submatrix I id).det :=
    φ.map_det (W.submatrix I id)
  have hW : ((W.map φ).submatrix rows id).det ≠ 0 := by
    rw [← hmap]
    exact fun hz => hP (hφ (hz.trans (map_zero φ).symm))
  obtain ⟨hAfield, hcrossField⟩ := augmented_minor_cross (C.map φ) (W.map φ) hWC hC rows hW
  have hA : A rows ≠ 0 := by
    intro hz
    apply hAfield
    rw [← map_augmentation φ C rows]
    exact (congrArg φ hz).trans (map_zero φ)
  have hcross (I : Fin s → (Fin r ⊕ Fin s)) : A I * P rows = A rows * P I := by
    apply hφ
    simpa only [map_mul, hmap, A, map_augmentation] using hcrossField I
  obtain ⟨a, ha⟩ := (PrimitiveVector.primitive_iff_bezout P).mp hprim
  let q := ∑ I, a I * A I
  have hfactor : A rows = q * P rows := by
    calc
      A rows = (∑ I, a I * P I) * A rows := by rw [ha, one_mul]
      _ = q * P rows := by
        dsimp only [q]
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro I _
        rw [mul_assoc, mul_comm (P I), ← hcross I, ← mul_assoc]
  have hq : q ≠ 0 := by
    intro hz
    exact hA (by rw [hfactor, hz, zero_mul])
  have hbound := augmented_det_degree C d hpositive hdegree rows
  change (A rows).natDegree ≤ _ at hbound
  rw [hfactor, Polynomial.natDegree_mul hq hP] at hbound
  omega

end K1_6_2
end PackSource_K1_6_2Aux1

section PackSource_PrincipalCofactor
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace FrobeniusLocator.Principal
noncomputable section
open Polynomial Finset Matrix
open scoped BigOperators
variable {F K row col : Type*} [Field F] [Field K] [Fintype col] [DecidableEq col]

/-- Extract the degree-bounded primitive kernel representative directly
from the shared arbitrary-nullity cofactors. No specializations can be zero. -/
theorem exists_primitive_kernel_vector (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (M : Matrix row col F[X]) (r : ℕ) (B : NormalFiber.RowBasis φ M r)
    (d : row → ℕ) (hdeg : ∀ i j, (M i j).natDegree ≤ d i)
    (E : col → K) (hE0 : E ≠ 0) (hE : (M.map φ).mulVec E = 0) :
    ∃ v : col → F[X], PrimitiveVector.IsPrimitive v ∧ M.mulVec v = 0 ∧
      (∀ j, (v j).natDegree ≤ ∑ i, d (B.rows i)) ∧
      (∀ γ, ∃ j, (v j).eval γ ≠ 0) := by
  classical
  have hcofactor : ∃ j, GenericCofactor.vector B j ≠ 0 := by
    by_contra h
    push_neg at h
    have hspan := GenericCofactor.generic_spans B hφ E hE
    have hz : ∀ j, (fun c => φ (GenericCofactor.vector B j c)) = 0 := by
      intro j
      funext c
      rw [h j]
      exact map_zero φ
    rw [show (∑ j, (E j / φ (NormalFiber.pivot B).det) •
      (fun c => φ (GenericCofactor.vector B j c))) = 0 by simp only [hz,smul_zero,
        Finset.sum_const_zero]] at hspan
    exact hE0 hspan
  obtain ⟨j,hj⟩ := hcofactor
  obtain ⟨g,v,hg,hgv,hprim⟩ := PrimitiveVector.exists_normalization
    (GenericCofactor.vector B j) hj
  refine ⟨v,hprim,?_,?_,PrimitiveVector.exists_eval_ne_zero v hprim⟩
  · exact PrimitiveVector.normalization_preserves_kernel M _ v g hg hgv
      (GenericCofactor.annihilates B hφ j)
  · intro c
    exact (PrimitiveVector.normalization_natDegree_le _ v g hg hgv c).trans
      (GenericCofactor.vector_natDegree_le B d hdeg j c)

end
end FrobeniusLocator.Principal
end PackSource_PrincipalCofactor
