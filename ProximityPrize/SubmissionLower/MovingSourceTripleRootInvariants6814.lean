import ProximityPrize.SubmissionLower.MovingSourceSameSourceCount6814

/-! Low-degree coefficient identities for the remaining triple-root
cubic/quartic band. These identities have coefficient degree two/three,
unlike the much larger discriminant itself. -/
namespace ProximityPrize.SubmissionLower.MovingSourceTripleRootInvariants6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000

def inv2 {R : Type*} [CommRing R] (a b c d e : R) : R := 12*a*e-3*b*d+c^2
def inv3 {R : Type*} [CommRing R] (a b c d e : R) : R :=
  72*a*c*e+9*b*c*d-27*a*d^2-27*b^2*e-2*c^3

theorem triple_factor_invariants {R : Type*} [CommRing R] (u v t : R) :
    inv2 u (v-3*u*t) (3*u*t^2-3*v*t) (3*v*t^2-u*t^3) (-v*t^3)=0 ∧
    inv3 u (v-3*u*t) (3*u*t^2-3*v*t) (3*v*t^2-u*t^3) (-v*t^3)=0 := by
  constructor <;> simp only [inv2,inv3] <;> ring

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

theorem depressed_root (h2 : (2 : K)≠0) (h3 : (3 : K)≠0)
    (p q r : K) (hI : p^2+12*r=0) (hJ : 8*p^3+27*q^2=0) :
    ∃ t : K, t^4+p*t^2+q*t+r=0 := by
  by_cases hp : p=0
  · have hr : r=0 := by
      have hh : (12 : K)*r=0 := by simpa only [hp,zero_pow (by decide : 2≠0),zero_add] using hI
      have h12 : (12 : K)≠0 := by
        have he : (12 : K)=3*2^2 := by ring
        rw [he]
        exact mul_ne_zero h3 (pow_ne_zero _ h2)
      exact (mul_eq_zero.mp hh).resolve_left h12
    exact ⟨0,by simp [hr]⟩
  · refine ⟨-3*q/(4*p),?_⟩
    have hnum : 81*q^4-48*p^3*q^2+256*p^4*r=0 := by
      apply (mul_eq_zero.mp (show (3 : K)*(81*q^4-48*p^3*q^2+256*p^4*r)=0 from ?_)).resolve_left h3
      linear_combination (9*q^2-8*p^3)*hJ+64*p^4*hI
    have h4 : (4 : K)≠0 := by
      have he : (4 : K)=2^2 := by ring
      rw [he]
      exact pow_ne_zero _ h2
    field_simp
    linear_combination hnum

theorem quartic_has_root_of_invariants
    (h2 : (2 : K)≠0) (h3 : (3 : K)≠0)
    (a b c d e : K) (ha : a≠0) (hI : inv2 a b c d e=0) (hJ : inv3 a b c d e=0) :
    ∃ t : K, a*t^4+b*t^3+c*t^2+d*t+e=0 := by
  let p := c/a-3*b^2/(8*a^2)
  let q := d/a-b*c/(2*a^2)+b^3/(8*a^3)
  let r := e/a-b*d/(4*a^2)+b^2*c/(16*a^3)-3*b^4/(256*a^4)
  have h4 : (4 : K)≠0 := by
    have he : (4 : K)=2^2 := by ring
    rw [he]; exact pow_ne_zero _ h2
  have h8 : (8 : K)≠0 := by
    have he : (8 : K)=2^3 := by ring
    rw [he]; exact pow_ne_zero _ h2
  have h16 : (16 : K)≠0 := by
    have he : (16 : K)=2^4 := by ring
    rw [he]; exact pow_ne_zero _ h2
  have h256 : (256 : K)≠0 := by
    have he : (256 : K)=2^8 := by ring
    rw [he]; exact pow_ne_zero _ h2
  have hIe : p^2+12*r=inv2 a b c d e/a^2 := by
    dsimp only [p,r,inv2]
    field_simp
    ring
  have hJe : 8*p^3+27*q^2=(6*a*p*inv2 a b c d e-inv3 a b c d e)/a^3 := by
    dsimp only [p,q,inv2,inv3]
    field_simp
    ring
  have hIp : p^2+12*r=0 := by rw [hIe,hI,zero_div]
  have hJp : 8*p^3+27*q^2=0 := by rw [hJe,hI,hJ,mul_zero,sub_self,zero_div]
  obtain ⟨t,ht⟩ := depressed_root h2 h3 p q r hIp hJp
  refine ⟨t-b/(4*a),?_⟩
  have he : a*(t-b/(4*a))^4+b*(t-b/(4*a))^3+c*(t-b/(4*a))^2+d*(t-b/(4*a))+e=
      a*(t^4+p*t^2+q*t+r) := by
    dsimp only [p,q,r]
    field_simp
    ring
  rw [he,ht,mul_zero]

theorem cubic_has_root_of_inv3
    (h3 : (3 : K)≠0) (b c d e : K) (hb : b≠0) (hJ : inv3 0 b c d e=0) :
    ∃ t : K, b*t^3+c*t^2+d*t+e=0 := by
  refine ⟨-c/(3*b),?_⟩
  field_simp
  dsimp only [inv3] at hJ
  linear_combination -hJ

#print axioms triple_factor_invariants
#print axioms quartic_has_root_of_invariants
#print axioms cubic_has_root_of_inv3
end
end ProximityPrize.SubmissionLower.MovingSourceTripleRootInvariants6814
