import ProximityPrize.SubmissionBinaryLower.B6402ExceptionalInterpolation

/-! Rectangular support of each shifted invariant basis element. A positive
spatial slice t^j allows at most two additional powers of the slope per t. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402LocalSupport
open Polynomial P64Found B6401ContactKerD B6401QuotInterp B6402SeedCoordinates B6402PrimarySystem
open B6402ExceptionalSystem B6402ExceptionalSupport B6402ExceptionalInterpolation
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {K : Type*} [Field K]
noncomputable local instance : CommRing (Polynomial K) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial K)) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing (Fibre K) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing ((Fibre K)[X]) := AddMonoidAlgebra.commRing

private theorem boxed_sum {α : Type*} (B : Finset α) {r w z : ℕ} (p : α → Fibre K)
    (h : ∀ i∈B, Bounds (p i) r w z) : Bounds (∑ i ∈ B,p i) r w z := by
  apply (in_box _ _ _ _).mp
  intro a b l ho
  rw [c3_sum]
  exact Finset.sum_eq_zero (fun i hi => (in_box _ _ _ _).mpr (h i hi) a b l ho)

def Series (p : (Fibre K)[X]) (r w z : ℕ) : Prop :=
    ∀ j, Bounds (p.coeff j) (r+2*j) w z

private theorem point {r w z : ℕ} {p : Fibre K}
    (h : ∀ a b l, c3 p a b l≠0 → a≤r ∧ b≤w ∧ l≤z) : Bounds p r w z :=
  ⟨fun a b l hn => by simpa using (h a b l hn).1,
   fun a b l hn => by simpa using (h a b l hn).2.1,
   fun a b l hn => by simpa using (h a b l hn).2.2⟩

theorem term (t w r : ℕ) (p : K[X]) (r0 : ℕ) (hr : r≤r0+2*t) :
    Series (monomial t (monomial w (monomial r p))) r0 w p.natDegree := by
  intro j; apply point
  intro a b l h
  by_cases ht : t=j <;> by_cases hw : w=b <;> by_cases hR : r=a <;>
    simp [c3,coeff_monomial,Finsupp.single_apply,ht,hw,hR] at h
  exact ⟨by omega,by omega,le_natDegree_of_ne_zero h⟩

theorem Series.mono {p : (Fibre K)[X]} {r w z r' w' z' : ℕ} (h : Series p r w z)
    (hr : r≤r') (hw : w≤w') (hz : z≤z') : Series p r' w' z' :=
  fun j => (h j).mono (by omega) hw hz

theorem Series.add {p h : (Fibre K)[X]} {r w z : ℕ} (hp : Series p r w z) (hh : Series h r w z) :
    Series (p+h) r w z := by
  intro j; rw [coeff_add]; apply (in_box _ _ _ _).mp
  intro a b l ho
  rw [c3_add,(in_box _ _ _ _).mpr (hp j) a b l ho,(in_box _ _ _ _).mpr (hh j) a b l ho,add_zero]

theorem Series.mul {p h : (Fibre K)[X]} {r w z r' w' z' : ℕ} (hp : Series p r w z) (hh : Series h r' w' z') :
    Series (p*h) (r+r') (w+w') (z+z') := by
  intro j; rw [coeff_mul]; apply boxed_sum
  intro u hu
  have eq := Finset.HasAntidiagonal.mem_antidiagonal.mp hu
  exact ((hp u.1).mul (hh u.2)).mono (by omega) le_rfl le_rfl

theorem const (p : K[X]) : Series (locC p) 0 0 p.natDegree := by
  simpa only [locC,monomial_zero_left] using term 0 0 0 p 0 (by omega)

theorem Series.pow {p : (Fibre K)[X]} {r w z : ℕ} (hp : Series p r w z) (i : ℕ) :
    Series (p^i) (i*r) (i*w) (i*z) := by
  induction i with
  | zero => simpa [locC] using const (1 : K[X])
  | succ i ih => simpa only [pow_succ,Nat.succ_mul] using ih.mul hp

theorem linearSlope : Series (locR : LocalPoly (Polynomial K)) 1 0 0 := by
  simpa [locR,monomial_zero_left,monomial_one_one_eq_X] using term 0 0 1 (1:K[X]) 1 (by decide)

theorem ordinate : Series (locW : LocalPoly (Polynomial K)) 0 1 0 := by
  simpa [locW,monomial_zero_left,monomial_one_one_eq_X] using term 0 1 0 (1:K[X]) 0 (by decide)

theorem spatial : Series (locT : LocalPoly (Polynomial K)) 0 0 0 := by
  simpa [locT,monomial_zero_left,monomial_one_one_eq_X] using term 1 0 0 (1:K[X]) 0 (by decide)

theorem invariant_pair : Series (localU : LocalPoly (Polynomial K)) 0 2 0 := by
  unfold localU
  apply Series.add (by simpa using (ordinate (K:=K)).pow 2)
  have ht := term 1 0 2 (1:K[X]) 0 (by decide)
  convert ht.mono le_rfl (by decide : 0≤2) (by simp) using 1
  simp only [locR,locT,←C_mul_X_pow_eq_monomial,map_one,one_mul,pow_zero,pow_one,mul_one,map_pow]
  exact mul_comm _ _

theorem basis (x : K) (y : K[X]) (q : ℕ) (hy : y.natDegree≤q) (k r b a : ℕ) :
    Series (kerDLocalPoly (C x) y (k,r,b,a)) (k+r) (2*b+r) (q*(2*b+r)) := by
  have x0 : Series (locC (C x)) 0 0 0 := by simpa using const (C x)
  have x2 : Series (locC ((C x)^2)) 0 0 0 := by simpa [←map_pow] using const (C (x^2))
  have y2 : (y^2).natDegree≤2*q := natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hy)
  have sy : Series (locC y + locC (C x)*locR + locW) 1 1 q :=
    (((const y).mono (by decide) (by decide) hy).add ((x0.mul linearSlope).mono (by decide) (by decide) (by omega))).add
      (ordinate.mono (by decide) le_rfl (by omega))
  have sb : Series (locC (y^2)+localU) 0 2 (2*q) :=
    ((const _).mono le_rfl (by decide) y2).add (invariant_pair.mono le_rfl le_rfl (by omega))
  have base := ((((linearSlope (K:=K)).pow k).mul (sy.pow r)).mul ((x2.add spatial).pow a)).mul (sb.pow b)
  unfold kerDLocalPoly
  convert base using 1 <;> simp <;> ring

theorem sum (x : K) (y : K[X]) (q : ℕ) (hy : y.natDegree≤q) {w W s J T : ℕ} (hw : 0<w)
    (fc : KerDIdx w W s → K[X])
    (weight : ∀ e, fc e≠0 → (fc e).natDegree+q*(2*e.1.2.2.1+e.1.2.1)≤T)
    (ordinate_cap : ∀ e, fc e≠0 → 2*e.1.2.2.1+e.1.2.1≤J) :
    Series (localized x y fc) s J T := by
  intro i
  unfold localized
  rw [finsetSum_coeff]
  apply boxed_sum
  intro e _
  by_cases hz : fc e=0
  · rw [hz]; simp only [locC,map_zero,zero_mul,coeff_zero]
    exact point (fun a b l hn => False.elim (hn (c3_zero a b l)))
  rcases e with ⟨⟨k,r,b,a⟩,he⟩
  have hcap := ((mem_kerDIdxFinset_iff w W s hw k r b a).mp he).2.1
  exact (((const _).mul (basis x y q hy k r b a) i).mono (by omega) (by simpa using ordinate_cap _ hz) (weight _ hz))

#print axioms basis
#print axioms sum
end ProximityPrize.SubmissionBinaryLower.B6402LocalSupport
