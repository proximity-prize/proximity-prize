import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

set_option Elab.async false

namespace Research6966.QuadraticWeight
open Polynomial
open scoped Polynomial Differential
noncomputable section

/-- The cleared numerator for the (j+1)st derivative of an ODE solution. -/
def numerator {R : Type*} [CommRing R] [Differential R] (A B : R[X]) :
    ℕ → R[X]
  | 0 => B
  | j+1 =>
    let Q := numerator A B j
    let v := fun F : R[X] => A * Differential.mapCoeffs F + B * F.derivative
    A * v Q - ((2*j+1:ℕ):R[X]) * Q * v A

private theorem power_rule {S : Type*} [CommRing S] [Differential S] (a:S) (n:ℕ) :
    a * Differential.deriv (a^n) = n * a^n * Differential.deriv a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Differential.deriv.leibniz,Nat.cast_succ]
    simp only [smul_eq_mul] at *
    linear_combination a*ih

/-- Differential identity before specialization at a physical coordinate.
No divisions, including by a possibly vanishing separant, are performed. -/
theorem cleared {R S : Type*} [CommRing R] [Differential R] [CommRing S] [Differential S]
    [Algebra R S] [DifferentialAlgebra R S] (A B : R[X]) (y:S)
    (law : aeval y A * Differential.deriv y = aeval y B) (j:ℕ) :
    (aeval y A)^(2*j+1) * Differential.deriv^[j+1] y = aeval y (numerator A B j) := by
  let a := aeval y A
  let v (F : R[X]) := A*Differential.mapCoeffs F+B*F.derivative
  have chain (F:R[X]) : a*Differential.deriv (aeval y F) = aeval y (v F) := by
    rw [Differential.deriv_aeval_eq]
    dsimp [a,v]
    simp only [map_add,map_mul]
    linear_combination (aeval y F.derivative)*law
  induction j with
  | zero => simpa [numerator] using law
  | succ j ih =>
    let q := numerator A B j
    let z := Differential.deriv^[j+1] y
    let k := 2*j+1
    change a^k*z=aeval y q at ih
    have diff := congrArg (fun t:S => Differential.deriv t) ih
    simp only [Differential.deriv.leibniz,smul_eq_mul] at diff
    have target : 2*(j+1)+1=k+2 := by dsimp [k];omega
    rw [target, pow_add,Function.iterate_succ_apply' (n:=j+1),numerator]
    change a^k*a^2*Differential.deriv z=aeval y (A*v q-(k:R[X])*q*v A)
    simp only [map_sub,map_mul,map_natCast]
    change a^k*a^2*Differential.deriv z=a*aeval y (v q)-(k:S)*aeval y q*aeval y (v A)
    linear_combination a^2*diff + a*chain q - a*z*power_rule a k
      - (k:S)*z*a^k*chain A - (k:S)*aeval y (v A)*ih

/-- A word whose raw separant is nonzero has at most its physical degree
many singular agreements, irrespective of how many received nodes are base points. -/
theorem regular_hits {F I : Type*} [Field F] [DecidableEq F] [DecidableEq I]
    (nodes:I→F) (distinct:Function.Injective nodes) (T:Finset I)
    (separant:F[X]) (nz:separant≠0) :
    T.card ≤ (T.filter (fun i => separant.eval (nodes i) ≠ 0)).card + separant.natDegree := by
  let bad:=T.filter (fun i=>separant.eval (nodes i)=0)
  have sub : bad.image nodes ⊆ separant.roots.toFinset := by
    intro x hx
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    exact Multiset.mem_toFinset.mpr ((mem_roots nz).mpr (Finset.mem_filter.mp hi).2)
  have bound : bad.card ≤ separant.natDegree := by
    rw [←Finset.card_image_of_injective bad distinct]
    exact (Finset.card_le_card sub).trans
      ((Multiset.toFinset_card_le _).trans (card_roots' _))
  have split:=T.card_filter_add_card_filter_not (fun i=>separant.eval (nodes i)=0)
  change (T.filter (fun i=>separant.eval (nodes i)=0)).card ≤ _ at bound
  rw [← split, Nat.add_comm (T.filter (fun i=>separant.eval (nodes i)=0)).card]
  exact Nat.add_le_add_left bound _

#print axioms cleared
#print axioms regular_hits

/-- Applying the raw slope coefficient to a degree-w word charges just its
physical weight after removing the slope-variable weight. Zero coefficients
are allowed even if the budget contains no slot of their nominal weight. -/
theorem regular_hits_of_raw_line {F I : Type*} [Field F] [DecidableEq F] [DecidableEq I]
    (nodes:I→F) (distinct:Function.Injective nodes) (T:Finset I) (a b R:F[X]) (w cap:ℕ)
    (word:R.natDegree≤w) (hw:a=0 ∨ a.natDegree+w≤cap)
    (constant:b.natDegree≤cap) (nz:a*R+b≠0) :
    T.card ≤ (T.filter (fun i=>(a*R+b).eval (nodes i)≠0)).card + cap := by
  apply (regular_hits nodes distinct T _ nz).trans
  apply Nat.add_le_add_left
  apply (natDegree_add_le ..).trans
  apply max_le _ constant
  rcases hw with rfl|bound
  · simp
  · exact (natDegree_mul_le ..).trans ((Nat.add_le_add_left word _).trans bound)

/-- The determinant used to charge the identically singular words, valid
even at labels where the leading ordinate coefficient drops. -/
theorem exceptional_determinant {R : Type*} [CommRing R] (a c b₂ b₁ b₀ y:R)
    (singular:a*y+c=0) (root:b₂*y^2+b₁*y+b₀=0) :
    a^2*b₀-a*c*b₁+c^2*b₂=0 := by
  linear_combination a^2*root - (a*b₂*y+a*b₁-c*b₂)*singular

#print axioms regular_hits_of_raw_line
#print axioms exceptional_determinant

section SeedDegrees
variable {σ k : Type*} [CommRing k] [Nontrivial k]
abbrev Seeds := MvPolynomial σ k
private abbrev Row := (Seeds (σ:=σ) (k:=k))[X]
private def Bounded (Q : Row (σ:=σ) (k:=k)) (u:ℕ) := ∀ i, (Q.coeff i).totalDegree ≤ u

private theorem bound_add {F G : Row (σ:=σ) (k:=k)} {u : ℕ}
    (hf:Bounded F u) (hg:Bounded G u) : Bounded (F+G) u := by
  intro i
  rw [coeff_add]
  exact (MvPolynomial.totalDegree_add ..).trans (max_le (hf i) (hg i))

private theorem bound_sub {F G : Row (σ:=σ) (k:=k)} {u : ℕ}
    (hf:Bounded F u) (hg:Bounded G u) : Bounded (F-G) u := by
  intro i
  rw [coeff_sub]
  exact (MvPolynomial.totalDegree_sub ..).trans (max_le (hf i) (hg i))

private theorem bound_mul {F G : Row (σ:=σ) (k:=k)} {u v : ℕ}
    (hf:Bounded F u) (hg:Bounded G v) : Bounded (F*G) (u+v) := by
  intro i
  rw [coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro ij _
  exact (MvPolynomial.totalDegree_mul ..).trans (Nat.add_le_add (hf ij.1) (hg ij.2))

private theorem cast_degree (n:ℕ) : (n:Seeds (σ:=σ) (k:=k)).totalDegree=0 := by
  rw [← map_natCast (MvPolynomial.C : k →+* Seeds) n,MvPolynomial.totalDegree_C]

private theorem bound_dy {F : Row (σ:=σ) (k:=k)} {u:ℕ} (hf:Bounded F u) :
    Bounded F.derivative u := by
  intro i
  rw [coeff_derivative,← Nat.cast_succ]
  apply (MvPolynomial.totalDegree_mul ..).trans
  rw [cast_degree,Nat.add_zero]
  exact hf (i+1)

private theorem bound_const_mul (n:ℕ) {F : Row (σ:=σ) (k:=k)} {u:ℕ} (hf:Bounded F u) :
    Bounded ((n:Row)*F) u := by
  intro i
  rw [← map_natCast (C : Seeds →+* Row) n,coeff_C_mul]
  exact (MvPolynomial.totalDegree_mul ..).trans (by simpa [cast_degree] using hf i)

variable [Differential (Seeds (σ:=σ) (k:=k))]

/-- Degrees of all ordinate coefficients in the actual rational ODE numerator.
Physical coefficient differentiation fixes the two seeds. -/
theorem coefficient_degree (A B : Row (σ:=σ) (k:=k)) (u : ℕ)
    (dx:∀ f:Seeds (σ:=σ) (k:=k), (Differential.deriv f).totalDegree ≤ f.totalDegree)
    (ha:∀ i,(A.coeff i).totalDegree≤u) (hb:∀ i,(B.coeff i).totalDegree≤u)
    (j i:ℕ) : ((numerator A B j).coeff i).totalDegree≤(2*j+1)*u := by
  have direction {F : Row (σ:=σ) (k:=k)} {v:ℕ} (hf:Bounded F v) :
      Bounded (A*Differential.mapCoeffs F+B*F.derivative) (u+v) := by
    apply bound_add
    · apply bound_mul ha
      intro n
      simpa only [Differential.coeff_mapCoeffs] using (dx (F.coeff n)).trans (hf n)
    · exact bound_mul hb (bound_dy hf)
  suffices h:Bounded (numerator A B j) ((2*j+1)*u) from h i
  induction j with
  | zero => simpa [numerator,Bounded] using hb
  | succ j ih =>
    rw [numerator]
    apply bound_sub
    · convert bound_mul ha (direction ih) using 1
      ring
    · convert bound_mul (bound_const_mul (2*j+1) ih) (direction ha) using 1
      ring

#print axioms coefficient_degree
end SeedDegrees
end
end Research6966.QuadraticWeight
