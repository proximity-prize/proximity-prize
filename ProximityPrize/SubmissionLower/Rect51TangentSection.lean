import ProximityPrize.SubmissionLower.Rect51TangentSupport

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000

namespace Rect51Tangent
noncomputable section
open K1_14 (FX Equation)
open HighCore82706Tangent_3 (JetRing ordinate)
open HighCore82706Tangent_3_1 (velocity)
open scoped BigOperators

/-- The ordinate and velocity have weights one and two, respectively. -/
def Weighted (P : JetRing) (a : ℕ) : Prop :=
  ∀ j k, a < k+2*j → (P.coeff j).coeff k = 0

namespace Weighted
theorem mono {P : JetRing} {a b : ℕ} (h : Weighted P a) (e : a ≤ b) : Weighted P b :=
  fun j k hk => h j k (e.trans_lt hk)

theorem zero (a : ℕ) : Weighted 0 a := by intro j k _; simp

theorem monomial {P : Equation} {a j : ℕ} (h : P.natDegree+2*j ≤ a) :
    Weighted (Polynomial.monomial j P) a := by
  intro z k hk
  by_cases hz : z = j
  · subst z
    rw [Polynomial.coeff_monomial_same]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · rw [Polynomial.coeff_monomial_of_ne _ hz, Polynomial.coeff_zero]

theorem C {P : Equation} {a : ℕ} (h : P.natDegree ≤ a) : Weighted (Polynomial.C P) a := by
  rw [← Polynomial.monomial_zero_left]
  exact monomial (by simpa using h)

theorem ordinate : Weighted ordinate 1 := C Polynomial.natDegree_X.le

theorem velocity : Weighted velocity 2 := by
  rw [show HighCore82706Tangent_3_1.velocity = Polynomial.monomial 1 (1 : Equation) from
    Polynomial.monomial_one_one_eq_X.symm]
  exact monomial (by simp)

theorem scalar (x : FX) : Weighted (algebraMap FX JetRing x) 0 :=
  C (Polynomial.natDegree_C _).le

theorem add {P Q : JetRing} {a : ℕ} (hP : Weighted P a) (hQ : Weighted Q a) :
    Weighted (P+Q) a := by
  intro j k h
  rw [Polynomial.coeff_add, Polynomial.coeff_add, hP j k h, hQ j k h, add_zero]

theorem mul {P Q : JetRing} {a b : ℕ} (hP : Weighted P a) (hQ : Weighted Q b) :
    Weighted (P*Q) (a+b) := by
  intro j k h
  rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro uv huv
  have e₁ := Finset.mem_antidiagonal.mp huv
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro xy hxy
  have e₂ := Finset.mem_antidiagonal.mp hxy
  by_cases hp : a < xy.1+2*uv.1
  · rw [hP _ _ hp, zero_mul]
  · rw [hQ _ _ (by omega), mul_zero]

theorem neg {P : JetRing} {a : ℕ} (hP : Weighted P a) : Weighted (-P) a := by
  simpa only [map_neg, map_one, neg_one_mul, Nat.zero_add] using (scalar (-1 : FX)).mul hP

theorem sub {P Q : JetRing} {a : ℕ} (hP : Weighted P a) (hQ : Weighted Q a) :
    Weighted (P-Q) a := by
  rw [sub_eq_add_neg]
  exact hP.add hQ.neg

theorem pow {P : JetRing} {a : ℕ} (hP : Weighted P a) (n : ℕ) : Weighted (P^n) (n*a) := by
  induction n with
  | zero => simpa only [pow_zero, Nat.zero_mul, map_one] using scalar 1
  | succ n ih => simpa only [pow_succ, Nat.succ_mul] using ih.mul hP

theorem of_bounded {P : JetRing} {t : ℕ} {v : Axes} (hP : Bounded P t v) :
    ∃ a, Weighted P a := by
  classical
  let a := 2*t + P.support.sup (fun j => (P.coeff j).natDegree)
  refine ⟨a, fun j k h => ?_⟩
  by_cases hj : j ∈ P.support
  · have h₁ := (Polynomial.le_natDegree_of_mem_supp j hj).trans hP.1
    have h₂ := Finset.le_sup (f := fun j => (P.coeff j).natDegree) hj
    dsimp only [a] at h
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · rw [Polynomial.notMem_support_iff.mp hj, Polynomial.coeff_zero]

theorem sum {ι : Type*} {a : ℕ} {s : Finset ι} {f : ι → JetRing}
    (hf : ∀ i ∈ s, Weighted (f i) a) : Weighted (∑ i ∈ s, f i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact zero _
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
end Weighted

/-- Two representatives of a section with rectangular seed bounds. -/
structure Section (Q : Ideal JetRing) (h t : ℕ) (v : Axes) where
  order : ℕ
  affine : JetRing
  inverse : JetRing
  affine_bound : Bounded affine t v
  inverse_bound : Bounded inverse t v
  affine_weight : Weighted affine (h+2*t+order)
  inverse_weight : Weighted inverse (h+2*t+order)
  glue : ordinate^order * affine - inverse ∈ Q

def Represented (Q : Ideal JetRing) (h t : ℕ) (v : Axes) (P : JetRing) : Prop :=
  ∃ S : Section Q h t v, S.affine = P

namespace Section
def restrict {Q R : Ideal JetRing} {h t : ℕ} {v : Axes} (hQ : Q ≤ R)
    (S : Section Q h t v) : Section R h t v :=
  { S with glue := hQ S.glue }

def pad {Q : Ideal JetRing} {h t h' t' : ℕ} {v v' : Axes}
    (S : Section Q h t v) (hh : h+2*t ≤ h'+2*t') (ht : t ≤ t') (hv : ∀ i, v i ≤ v' i) :
    Section Q h' t' v' :=
  ⟨S.order,S.affine,S.inverse,S.affine_bound.mono ht hv,S.inverse_bound.mono ht hv,
    S.affine_weight.mono (by omega),S.inverse_weight.mono (by omega), S.glue⟩

def shift {Q : Ideal JetRing} {h t : ℕ} {v : Axes} (S : Section Q h t v) (n : ℕ) :
    Section Q h t v := by
  refine ⟨S.order+n,S.affine,ordinate^n*S.inverse,S.affine_bound,?_,?_,?_,?_⟩
  · simpa only [Nat.mul_zero, smul_zero, Nat.zero_add, zero_add] using
      (Bounded.ordinate.pow n).mul S.inverse_bound
  · exact S.affine_weight.mono (by omega)
  · have hW := (Weighted.ordinate.pow n).mul S.inverse_weight
    exact hW.mono (by omega)
  · rw [pow_add]
    convert Q.mul_mem_left (ordinate^n) S.glue using 1
    ring

def add {Q : Ideal JetRing} {h t : ℕ} {v : Axes}
    (S T : Section Q h t v) : Section Q h t v := by
  let A := S.shift T.order
  let B := T.shift S.order
  have e : A.order = B.order := Nat.add_comm _ _
  refine ⟨A.order,A.affine+B.affine,A.inverse+B.inverse,
    A.affine_bound.add B.affine_bound,A.inverse_bound.add B.inverse_bound,?_,?_,?_⟩
  · exact A.affine_weight.add (e.symm ▸ B.affine_weight)
  · exact A.inverse_weight.add (e.symm ▸ B.inverse_weight)
  · rw [mul_add, add_sub_add_comm]
    exact Q.add_mem A.glue (e.symm ▸ B.glue)
end Section

namespace Represented
theorem absolute {Q : Ideal JetRing} {h t : ℕ} {v : Axes} {P : JetRing}
    (hb : Bounded P t v) (hw : Weighted P (h+2*t)) : Represented Q h t v P := by
  exact ⟨⟨0,P,P,hb,hb,hw,hw,by simp⟩,rfl⟩

theorem of_inverse {Q : Ideal JetRing} {h t : ℕ} {v : Axes} {P R : JetRing} {n : ℕ}
    (ha : Bounded P t v) (hb : Bounded R t v)
    (hw : Weighted R (h+2*t+n)) (hg : ordinate^n*P-R ∈ Q) :
    Represented Q h t v P := by
  obtain ⟨m,hm⟩ := Weighted.of_bounded ha
  let R' := ordinate^m*R
  refine ⟨⟨n+m,P,R',ha,?_,hm.mono (by omega),?_,?_⟩,rfl⟩
  · simpa only [R', Nat.mul_zero, smul_zero, Nat.zero_add, zero_add] using (Bounded.ordinate.pow m).mul hb
  · exact ((Weighted.ordinate.pow m).mul hw).mono (by omega)
  · rw [pow_add]
    convert Q.mul_mem_left (ordinate^m) hg using 1
    dsimp only [R']
    ring

theorem pad {Q : Ideal JetRing} {h t h' t' : ℕ} {v v' : Axes} {P : JetRing}
    (S : Represented Q h t v P) (hh : h+2*t ≤ h'+2*t') (ht : t ≤ t') (hv : ∀ i, v i ≤ v' i) :
    Represented Q h' t' v' P := by
  obtain ⟨S,e⟩ := S
  exact ⟨S.pad hh ht hv,e⟩

theorem add {Q : Ideal JetRing} {h t : ℕ} {v : Axes} {P R : JetRing}
    (hP : Represented Q h t v P) (hR : Represented Q h t v R) :
    Represented Q h t v (P+R) := by
  obtain ⟨A,rfl⟩ := hP
  obtain ⟨B,rfl⟩ := hR
  exact ⟨A.add B,rfl⟩

theorem mul {Q : Ideal JetRing} {h t h' t' : ℕ} {v v' : Axes} {P R : JetRing}
    (hP : Represented Q h t v P) (hR : Represented Q h' t' v' R) :
    Represented Q (h+h') (t+t') (v+v') (P*R) := by
  obtain ⟨A,rfl⟩ := hP
  obtain ⟨B,rfl⟩ := hR
  refine ⟨⟨A.order+B.order,A.affine*B.affine,A.inverse*B.inverse,
    A.affine_bound.mul B.affine_bound,A.inverse_bound.mul B.inverse_bound,?_,?_,?_⟩,rfl⟩
  · exact (A.affine_weight.mul B.affine_weight).mono (by omega)
  · exact (A.inverse_weight.mul B.inverse_weight).mono (by omega)
  · rw [pow_add]
    convert Q.add_mem (Q.mul_mem_right (ordinate^B.order*B.affine) A.glue)
      (Q.mul_mem_left A.inverse B.glue) using 1
    ring

theorem scalar {Q : Ideal JetRing} (x : FX) : Represented Q 0 0 0 (algebraMap FX JetRing x) :=
  absolute (Bounded.scalar x) (Weighted.scalar x)

theorem zero {Q : Ideal JetRing} (h t : ℕ) (v : Axes) : Represented Q h t v (0 : JetRing) :=
  absolute (Bounded.zero _ _) (Weighted.zero _)

theorem smul {Q : Ideal JetRing} {h t : ℕ} {v : Axes} {P : JetRing} (x : FX)
    (hP : Represented Q h t v P) :
    Represented Q h t v (algebraMap FX JetRing x * P) := by
  simpa only [zero_add, Nat.zero_add] using (scalar x).mul hP

theorem neg {Q : Ideal JetRing} {h t : ℕ} {v : Axes} {P : JetRing}
    (hP : Represented Q h t v P) : Represented Q h t v (-P) := by
  simpa only [map_neg,map_one,neg_one_mul] using smul (-1 : FX) hP

theorem sub {Q : Ideal JetRing} {h t : ℕ} {v : Axes} {P R : JetRing}
    (hP : Represented Q h t v P) (hR : Represented Q h t v R) :
    Represented Q h t v (P-R) := by
  rw [sub_eq_add_neg]
  exact hP.add hR.neg

theorem pow {Q : Ideal JetRing} {h t : ℕ} {v : Axes} {P : JetRing}
    (hP : Represented Q h t v P) (n : ℕ) : Represented Q (n*h) (n*t) (n • v) (P^n) := by
  induction n with
  | zero => simpa only [pow_zero, Nat.zero_mul, zero_nsmul, map_one] using scalar (Q := Q) 1
  | succ n ih => simpa only [pow_succ, Nat.succ_mul, succ_nsmul] using ih.mul hP

theorem sum {ι : Type*} {Q : Ideal JetRing} {h t : ℕ} {v : Axes}
    {f : ι → JetRing} {s : Finset ι} (hf : ∀ i ∈ s, Represented Q h t v (f i)) :
    Represented Q h t v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact zero _ _ _
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
end Represented
end
end Rect51Tangent
