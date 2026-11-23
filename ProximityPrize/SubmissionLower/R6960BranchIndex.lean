import ProximityPrize.SubmissionLower.R6960BranchCollisions

noncomputable section
set_option Elab.async false
namespace Lower6960.BranchIndex
open Finset Polynomial Matrix
open scoped BigOperators Polynomial Matrix
open BranchCollisions
variable {K : Type} [Field K] [DecidableEq K]

private theorem mult_pow (p : K[X]) (a : K) (n : ℕ) :
    (p^n).rootMultiplicity a=n*p.rootMultiplicity a := by
  simp only [←Polynomial.count_roots,roots_pow,Multiset.count_nsmul]

private theorem mult_product {ι : Type*} (F : ι→K[X]) (w : ι→ℕ) (S : Finset ι)
    (nz : ∀ i∈S,F i≠0) (x : K) :
    (∏ i∈S,(F i)^w i).rootMultiplicity x=∑ i∈S,w i*(F i).rootMultiplicity x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S ni ih =>
    have rest (j) (hj : j∈S) := nz j (mem_insert_of_mem hj)
    rw [prod_insert ni,sum_insert ni,rootMultiplicity_mul (mul_ne_zero
      (pow_ne_zero _ (nz i (mem_insert_self ..))) (prod_ne_zero_iff.mpr (fun j hj=>pow_ne_zero _ (rest j hj)))),
      mult_pow,ih rest]

/-- A square determinant factor of the branch discriminant counts against the
actual weighted root collisions. A simple transverse root is excluded by the
stated support hypothesis on the change of order. -/
theorem index_degree [IsAlgClosed K] {ι : Type*} [Fintype ι]
    (F : ι→Polynomial K[X]) (w : ι→ℕ) (positive : ∀ i,0<w i)
    (B : Polynomial K[X]) (prod : B=∏i,F i)
    (sep : (B.map (algebraMap K[X] (FractionRing K[X]))).Separable)
    (T : Finset K) (good : ∀ z∈T,B.map (evalRingHom z)≠0)
    (idx : K→K[X]) (supported : ∀ z∈T, ∀ x∈(idx z).roots,2≤(B.map (evalRingHom z)).rootMultiplicity x)
    (disc : ∀ z∈T, idx z^2 ∣ ∏i, ((F i).map (evalRingHom z))^(w i))
    {s t : ℕ} (xcap : (∑ i,w i*(F i).natDegree)≤2*s)
    (zcap : (∑ i,w i*CurvatureSquares.height (F i))≤2*t) :
    (∑ z∈T,(idx z).natDegree)≤8*s*t := by
  classical
  let f (z) (i) := (F i).map (evalRingHom z)
  let xs (z : K) := (idx z).roots.toFinset
  have point (z : K) (hz : z∈T) :
      2*(idx z).natDegree≤∑ i,w i*collisionMass (f z i) (B.map (evalRingHom z)) (xs z) := by
    have nonzero : (∏i,f z i)≠0 := by
      simpa only [prod,Polynomial.map_prod,f] using good z hz
    have nz (i : ι) := prod_ne_zero_iff.mp nonzero i (mem_univ i)
    have big : (∏i,(f z i)^w i)≠0 := prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (nz i))
    have each (x : K) (hx : x∈xs z) : 2*(idx z).rootMultiplicity x≤
        ∑i,w i*(if 2≤(B.map (evalRingHom z)).rootMultiplicity x then (f z i).rootMultiplicity x else 0) := by
      have h := (le_rootMultiplicity_iff big).mpr
        ((((idx z)^2).pow_rootMultiplicity_dvd x).trans (disc z hz))
      rw [mult_pow,mult_product _ _ _ (fun i _=>nz i)] at h
      simpa only [ite_eq_left (supported z hz x (Multiset.mem_toFinset.mp hx))] using h
    have deg : (∑ x∈xs z,(idx z).rootMultiplicity x)=(idx z).natDegree := by
      simp only [xs,←Polynomial.count_roots,Multiset.toFinset_sum_count_eq]
      exact (IsAlgClosed.splits _).natDegree_eq_card_roots.symm
    calc 2*(idx z).natDegree = ∑ x∈xs z,2*(idx z).rootMultiplicity x := by rw [←deg,mul_sum]
         _ ≤ _ := sum_le_sum each
         _ = _ := by rw [sum_comm]; simp only [collisionMass,mul_sum]
  have upper := weighted F w positive B prod sep T xs good xcap zcap
  have total := sum_le_sum point
  rw [←mul_sum] at total
  have swap : (∑ z∈T,∑ i,w i*collisionMass (f z i) (B.map (evalRingHom z)) (xs z)) =
      ∑ i,w i*∑ z∈T,collisionMass (f z i) (B.map (evalRingHom z)) (xs z) := by
    rw [sum_comm]; simp only [mul_sum]
  rw [swap] at total
  have paid := total.trans upper
  calc (∑ z∈T,(idx z).natDegree) ≤ (16*s*t)/2 := (Nat.le_div_iff_mul_le (by decide)).mpr
         (by simpa only [Nat.mul_comm _ 2] using paid)
       _ = 8*s*t := by rw [show 16*s*t=8*s*t*2 by ring,Nat.mul_div_cancel _ (by decide)]

omit [DecidableEq K] in
/-- Changing the integral basis pairs the columns on both sides of the
trace form; this is the square factor used in the collision count. -/
theorem index_square {ι : Type*} [DecidableEq ι] [Fintype ι] (A D : Matrix ι ι K[X]) :
    D.det^2 ∣ (D.transpose*A*D).det := by
  refine ⟨A.det,?_⟩
  rw [det_mul,det_mul,det_transpose]; ring

omit [DecidableEq K] in
/-- Multiplying any normalized section, in particular the marked sheet
idempotent, by the index determinant puts it back in the original order. -/
theorem clear_section {ι : Type*} [DecidableEq ι] [Fintype ι] (D : Matrix ι ι K[X]) (v : ι→K[X]) :
    ∃ u : ι→K[X],D.mulVec u=D.det • v := by
  refine ⟨D.adjugate.mulVec v,?_⟩
  rw [Matrix.mulVec_mulVec,Matrix.mul_adjugate,Matrix.smul_mulVec,Matrix.one_mulVec]

#print axioms index_degree
#print axioms clear_section
end Lower6960.BranchIndex
