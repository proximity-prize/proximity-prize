import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionMarked
noncomputable section
open Polynomial
open scoped Polynomial

variable {k V Bf Bi : Type*} [Field k] [CommRing V] [CommRing Bf] [CommRing Bi]
  [Algebra (Polynomial k) Bi]

/-- A power of the boundary coordinate and a polynomial unit at the
boundary are relatively prime. Two clearings of this form in the same
original order recover the original section there. -/
theorem boundary_clearings (φ : Bi→+*V) (a : (Polynomial k)→+*V)
    (scalars : ∀ f,φ (algebraMap (Polynomial k) Bi f)=a f)
    (w : V) (n : ℕ) (D : (Polynomial k)) (unit : D.eval 0≠0)
    (p : ∃ u : Bi,φ u=a (Polynomial.X^n)*w)
    (d : ∃ u : Bi,φ u=a D*w) : ∃ u : Bi,φ u=w := by
  have nx : ¬ (Polynomial.X:(Polynomial k))∣D := by
    intro dv
    obtain ⟨g,hg⟩ := dv
    apply unit
    rw [hg,eval_mul,eval_X,zero_mul]
  have cp : IsCoprime ((Polynomial.X:(Polynomial k))^n) D :=
    (irreducible_X.coprime_iff_not_dvd.mpr nx).pow_left
  obtain ⟨x,y,xy⟩ := cp
  obtain ⟨u,hu⟩ := p
  obtain ⟨v,hv⟩ := d
  refine ⟨x • u+y • v,?_⟩
  simp only [Algebra.smul_def,map_add,map_mul,scalars,hu,hv]
  calc _ = a (x*Polynomial.X^n+y*D)*w := by rw [map_add,map_mul,map_mul]; ring
       _ = w := by rw [xy,map_one,one_mul]

/-- Actual chart images with a common localization agree on the
representatives of a regular marked multiple. The first chart can clear
an arbitrary polynomial denominator. The second chart only needs the
index to be a unit at its boundary point. -/
theorem marked_multiple_two_charts (ι : k→+*V) (X : Vˣ)
    (φf : Bf→+*V) (φi : Bi→+*V)
    (scalars : ∀ f,φi (algebraMap (Polynomial k) Bi f)=f.eval₂ ι (↑X⁻¹))
    (common : ∀ u : Bf,∃ n : ℕ,∃ v : Bi,φi v=((↑X⁻¹:V)^n)*φf u)
    (η : V) (D : (Polynomial k)) (unit : D.eval 0≠0)
    (clears : ∃ v : Bi,φi v=D.eval₂ ι (↑X⁻¹)*η)
    (h : (Polynomial k)) (a : ℕ) (deg : h.natDegree≤a)
    (finite : ∃ u : Bf,φf u=h.eval₂ ι (X:V)*η) :
    ∃ (u : Bf) (v : Bi),φf u=h.eval₂ ι (X:V)*η ∧
      φi v=((↑X⁻¹:V)^a)*φf u := by
  obtain ⟨u,hu⟩ := finite
  obtain ⟨n,y,hy⟩ := common u
  obtain ⟨z,hz⟩ := clears
  let w : V := ((↑X⁻¹:V)^a)*φf u
  let j := eval₂RingHom ι (↑X⁻¹:V)
  have jX : j Polynomial.X=(↑X⁻¹:V) := eval₂_X ι (↑X⁻¹:V)
  have power_clear : ∃ v : Bi,φi v=j (Polynomial.X^n)*w := by
    refine ⟨((Polynomial.X:(Polynomial k))^a) • y,?_⟩
    rw [Algebra.smul_def,map_mul,scalars,hy]
    change j (Polynomial.X^a)*_ = _
    rw [map_pow,map_pow,jX]
    unfold w
    ring
  let : Invertible (X:V) := invertibleOfLeftInverse (X:V) (↑X⁻¹:V) X.inv_mul
  have h_reflect : (h.reflect a).eval₂ ι (↑X⁻¹:V)=(↑X⁻¹:V)^a*h.eval₂ ι (X:V) := by
    have eq := eval₂_reflect_mul_pow ι (X:V) a h deg
    change (h.reflect a).eval₂ ι (↑X⁻¹:V)*(X:V)^a=h.eval₂ ι (X:V) at eq
    rw [←eq,mul_left_comm,←mul_pow,Units.inv_mul,one_pow,mul_one]
  have det_clear : ∃ v : Bi,φi v=j D*w := by
    refine ⟨(h.reflect a) • z,?_⟩
    rw [Algebra.smul_def,map_mul,scalars,hz,h_reflect]
    change _ = D.eval₂ ι (↑X⁻¹:V)*w
    unfold w
    rw [hu]
    ring
  obtain ⟨v,hv⟩ := boundary_clearings φi j scalars w n D unit power_clear det_clear
  exact ⟨u,v,hu,hv⟩

#print axioms marked_multiple_two_charts
end
end Lower6960.CollisionMarked
