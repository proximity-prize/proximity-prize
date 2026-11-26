import ProximityPrize.SubmissionBinaryLower.B6402ExceptionalFibres
import ProximityPrize.SubmissionBinaryLower.P64FoundSupp
import Mathlib.LinearAlgebra.Prod

/-! The actual linear recursion of quotient tests at an exceptional fibre.
The auxiliary at step i is a trivariate polynomial supported on a finite box. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402ExceptionalSystem
open Polynomial P64Found B6402ExceptionalFibres
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {K : Type*} [Field K]
abbrev Fibre (K : Type*) [Field K] := Polynomial (Polynomial (Polynomial K))
noncomputable local instance : CommRing (Polynomial K) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial K)) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing (Fibre K) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing ((Fibre K)[X]) := AddMonoidAlgebra.commRing

def box (r w z : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.range (r+1) ×ˢ (Finset.range (w+1) ×ˢ Finset.range (z+1))

def testBox (s J T H i : ℕ) := box (s+3*i) (J+5*i) (T+i*H)
def auxBox (s J T H d i : ℕ) := box (s+3*i) (J+5*i-d) (T+i*H-H)

theorem card_box (r w z : ℕ) : (box r w z).card=(r+1)*((w+1)*(z+1)) := by
  simp [box]

abbrev Aux (K : Type*) (b : ℕ) (B : ℕ → Finset (ℕ×ℕ×ℕ)) :=
  (i : Fin b) → (B i.val → K)

variable {U : Type*} [AddCommGroup U] [Module K U]

noncomputable def divMap : (Fibre K)[X] →ₗ[K] (Fibre K)[X] where
  toFun p := p.divX
  map_add' _ _ := divX_add
  map_smul' c p := by apply Polynomial.ext; intro n; simp only [coeff_divX,Polynomial.coeff_smul,RingHom.id_apply]

noncomputable def constMap : Fibre K →ₗ[K] (Fibre K)[X] where
  toFun p := C p
  map_add' _ _ := map_add _ _ _
  map_smul' c p := by exact (Polynomial.smul_C c p).symm

noncomputable def constantTerm : (Fibre K)[X] →ₗ[K] Fibre K where
  toFun p := p.coeff 0
  map_add' _ _ := coeff_add _ _ _
  map_smul' _ _ := Polynomial.coeff_smul _ _ _

noncomputable def layer (F : (Fibre K)[X]) (a : Fibre K)
    (g : U →ₗ[K] (Fibre K)[X]) (Q : ℕ → U →ₗ[K] Fibre K) : ℕ → U →ₗ[K] (Fibre K)[X]
  | 0 => g
  | i+1 => divMap.comp
      (((LinearMap.mulLeft K (C a)).comp (layer F a g Q i)) -
       ((LinearMap.mulLeft K F).comp (constMap.comp (Q i))))

noncomputable def errorTerm (F : (Fibre K)[X]) (a L : Fibre K)
    (g : U →ₗ[K] (Fibre K)[X]) (Q : ℕ → U →ₗ[K] Fibre K) (i : ℕ) : U →ₗ[K] Fibre K :=
  constantTerm.comp (layer F a g Q i) - (LinearMap.mulLeft K L).comp (Q i)

noncomputable def equations (F : (Fibre K)[X]) (a L : Fibre K)
    (g : U →ₗ[K] (Fibre K)[X]) (Q : ℕ → U →ₗ[K] Fibre K)
    (b : ℕ) (rows : ℕ → Finset (ℕ×ℕ×ℕ)) : U →ₗ[K] ((i : Fin b) → rows i.val → K) :=
  LinearMap.pi fun i => (extr3 (rows i.val)).comp (errorTerm F a L g Q i.val)

theorem kernel_error (F : (Fibre K)[X]) (a L : Fibre K)
    (g : U →ₗ[K] (Fibre K)[X]) (Q : ℕ → U →ₗ[K] Fibre K)
    (b : ℕ) (rows : ℕ → Finset (ℕ×ℕ×ℕ)) (u : U)
    (cover : ∀ i<b, errorTerm F a L g Q i u ∈ supp (rows i))
    (zero : equations F a L g Q b rows u=0) (i : ℕ) (hi : i<b) :
    ((layer F a g Q i) u).coeff 0 = L*(Q i u) := by
  have h : extr3 (rows i) (errorTerm F a L g Q i u)=0 := congrFun zero ⟨i,hi⟩
  have e := comb3_extr3 (cover i hi)
  rw [h,map_zero] at e
  exact sub_eq_zero.mp e.symm

theorem kernel_remainder (F : (Fibre K)[X]) (a L : Fibre K)
    (g : U →ₗ[K] (Fibre K)[X]) (Q : ℕ → U →ₗ[K] Fibre K)
    (b : ℕ) (rows : ℕ → Finset (ℕ×ℕ×ℕ)) (u : U)
    (cover : ∀ i<b, errorTerm F a L g Q i u ∈ supp (rows i))
    (zero : equations F a L g Q b rows u=0) :
    remainderConditions F a L b (g u) := by
  have go (n i : ℕ) (bound : i+n≤b) : remainderConditions F a L n (layer F a g Q i u) := by
    induction n generalizing i with
    | zero => trivial
    | succ n ih =>
      refine ⟨Q i u,kernel_error F a L g Q b rows u cover zero i (by omega),?_⟩
      exact ih (i+1) (by omega)
  exact go b 0 (by omega)

theorem zero_quotients (F : (Fibre K)[X]) (a L : Fibre K) (hn : L≠0)
    (g : U →ₗ[K] (Fibre K)[X]) (Q : ℕ → U →ₗ[K] Fibre K)
    (b : ℕ) (rows : ℕ → Finset (ℕ×ℕ×ℕ)) (u : U)
    (cover : ∀ i<b, errorTerm F a L g Q i u ∈ supp (rows i))
    (zero : equations F a L g Q b rows u=0) (hg : g u=0) :
    ∀ i<b, Q i u=0 := by
  have go (i : ℕ) (hi : i≤b) : layer F a g Q i u=0 := by
    induction i with
    | zero => exact hg
    | succ i ih =>
      have hprev := ih (by omega)
      have hq := kernel_error F a L g Q b rows u cover zero i (by omega)
      rw [hprev,coeff_zero] at hq
      have hq' := (mul_eq_zero.mp hq.symm).resolve_left hn
      change (C a * (layer F a g Q i u)-F*C (Q i u)).divX=0
      simp [hprev,hq']
  intro i hi
  have hq := kernel_error F a L g Q b rows u cover zero i hi
  rw [go i hi.le,coeff_zero] at hq
  exact (mul_eq_zero.mp hq.symm).resolve_left hn

#print axioms kernel_remainder
#print axioms zero_quotients
end ProximityPrize.SubmissionBinaryLower.B6402ExceptionalSystem
