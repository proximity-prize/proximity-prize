import ProximityPrize.SubmissionLower.TransverseBudgetUse6814

/-! Multiplicity bookkeeping for a unique curvature-root owner.

This does not assume that a common factor owns all the root multiplicity.
The cofactor must explicitly be nonvanishing at the chosen root. The final
numeric bounds are conditional on the degree charges from two retained
sources; no packet-wide coverage or 68.14 submission is asserted here.
-/
namespace ProximityPrize.SubmissionLower.UniqueCurvatureOwner6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial

variable {E : Type*} [Field E]

theorem rootMultiplicity_power (j : Polynomial E) (t : E) (e : ℕ)
    (hj : j ≠ 0) : (j^e).rootMultiplicity t = e * j.rootMultiplicity t := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hj) hj), ih]
    ring

theorem unique_owner_order_le (j q : Polynomial E) (t : E) (d e : ℕ)
    (hj : j ≠ 0) (hq : q.eval t ≠ 0)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ j^e*q) :
    d ≤ e*j.rootMultiplicity t := by
  have hq0 : q ≠ 0 := by
    intro hz
    exact hq (by rw [hz]; simp)
  have hprod : j^e*q ≠ 0 := mul_ne_zero (pow_ne_zero _ hj) hq0
  have hm := (Polynomial.le_rootMultiplicity_iff hprod).mpr hd
  rw [Polynomial.rootMultiplicity_mul hprod,rootMultiplicity_power j t e hj,
    Polynomial.rootMultiplicity_eq_zero hq,add_zero] at hm
  exact hm

theorem simple_unique_owner_exponent (j q : Polynomial E) (t : E) (d e : ℕ)
    (hj : j ≠ 0) (hq : q.eval t ≠ 0) (hsimple : j.rootMultiplicity t = 1)
    (hd : (Polynomial.X-Polynomial.C t)^d ∣ j^e*q) : d ≤ e := by
  simpa only [hsimple,mul_one] using unique_owner_order_le j q t d e hj hq hd

theorem simple_owner_all_source_caps (b u t e31 e0 : ℕ)
    (he31 : 7 ≤ e31) (he0 : 6 ≤ e0)
    (hb : e31*b ≤ 53) (hu : e31*u ≤ 177) (ht : e0*t ≤ 1871) :
    b ≤ 7 ∧ u ≤ 25 ∧ t ≤ 311 := by
  have hb' := (Nat.mul_le_mul_right b he31).trans hb
  have hu' := (Nat.mul_le_mul_right u he31).trans hu
  have ht' := (Nat.mul_le_mul_right t he0).trans ht
  omega

open RCN095

theorem quadratic_native_price :
    flagMixed ⟨3504,45,12⟩ unitZFlag ⟨286,20,5⟩ = 525 ∧
    flagMixed ⟨3504,45,12⟩ unitYZFlag ⟨286,20,5⟩ = 21477 ∧
    flagMixed ⟨3504,45,12⟩ unitAllFlag ⟨286,20,5⟩ = 105327 := by
  norm_num [flagMixed,unitZFlag,unitYZFlag,unitAllFlag]

/-- Algebraic upper bound for a pair of nested degree flags. The lower
bound c on each factor matters; omitting it loses the useful price. -/
theorem nested_pair_bound (a b z v R T c : ℕ)
    (ha : c ≤ a) (hb : c ≤ b) (hR : a+b ≤ R)
    (hT : a+b+z+v ≤ T) (hwide : 2*R ≤ T) :
    a*b+z*b+v*a ≤ (R-c)*(T-(R-c)) := by
  suffices h : ∀ a b z v : ℕ, c ≤ a → c ≤ b → a+b ≤ R →
      a+b+z+v ≤ T → a ≤ b → a*b+z*b+v*a ≤ (R-c)*(T-(R-c)) by
    rcases le_total a b with hab | hba
    · exact h a b z v ha hb hR hT hab
    · have hh := h b a v z hb ha (by omega) (by omega) hba
      nlinarith
  intro a b z v ha hb hR hT hab
  have hk : b ≤ R-c := by omega
  have hwide' : R-c+b ≤ T := by omega
  have hm := Nat.mul_le_mul_left b hT
  have hv := Nat.mul_le_mul_left v hab
  have hfirst : a*b+z*b+v*a+b*b ≤ b*T := by nlinarith
  have he1 : R-c-b+b = R-c := Nat.sub_add_cancel hk
  have he2 : T-(R-c)-b+b+(R-c) = T := by omega
  have he3 : T-(R-c)+(R-c) = T := by omega
  have hprod : 0 ≤ (R-c-b)*(T-(R-c)-b) := Nat.zero_le _
  nlinarith

/-- Directional prices for two S-dependent factors within the small
source's ordinary clearing budget. These are degree inequalities only;
the proper-intersection/exception handoff is separate. -/
theorem small_source_pair_prices (p q : FlagDegree)
    (hp : 2 ≤ p.all) (hq : 2 ≤ q.all)
    (hr : p.all+q.all ≤ 31)
    (hy : p.yz+p.all+q.yz+q.all ≤ 112)
    (ht : p.zOnly+p.yz+p.all+q.zOnly+q.yz+q.all ≤ 1009) :
    flagMixed p q unitZFlag ≤ 2407 ∧
    flagMixed p q unitYZFlag ≤ 28420 ∧
    flagMixed p q unitAllFlag ≤ 98890 := by
  have hz := nested_pair_bound p.all q.all p.yz q.yz 31 112 2 hp hq hr
    (by omega) (by norm_num)
  have hm := nested_pair_bound p.all q.all (p.zOnly+p.yz) (q.zOnly+q.yz)
    31 1009 2 hp hq hr (by omega) (by norm_num)
  have ha := nested_pair_bound (p.yz+p.all) (q.yz+q.all) p.zOnly q.zOnly
    112 1009 2 (by omega) (by omega) (by omega) (by omega) (by norm_num)
  norm_num at hz hm ha
  simp only [flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Only the checked cell's main term, before new exception charges. -/
def checkedMain (z yz all : ℚ) : ℚ :=
    126275387074424400 +
    (4*131072/3*(131074*3504)+65539*(131073*3504))*z +
    (4*131072/3*(131074*45-131072)+65539*(131073*45))*yz +
    (4*131072/3*(131074*11)+65539*(131073*12-1))*all

theorem simple_quadratic_main_fits :
    checkedMain 525 21441 105156 = 251453192841101867 ∧
    checkedMain 525 21441 105156 < 272069082261391681 := by
  norm_num [checkedMain]

theorem two_owner_main_fits :
    checkedMain (4491/7) 28420 98890 = 1902781620765326954/7 ∧
    checkedMain (4491/7) 28420 98890 < 272069082261391681 := by
  norm_num [checkedMain]

#print axioms unique_owner_order_le
#print axioms simple_unique_owner_exponent
#print axioms simple_owner_all_source_caps
#print axioms quadratic_native_price
#print axioms small_source_pair_prices
#print axioms simple_quadratic_main_fits
#print axioms two_owner_main_fits
end
end ProximityPrize.SubmissionLower.UniqueCurvatureOwner6814
