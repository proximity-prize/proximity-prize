import ProximityPrize.SubmissionLower.R6960TraceSpecialization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
set_option Elab.async false
namespace Lower6960.TameTrace
open Algebra
variable {A B K C : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [UniqueFactorizationMonoid B] [Algebra A B] [Field K] [CommRing C]
    [Algebra K C] [FiniteDimensional K C]

/-- A nondivisible element of a normal semilocal Dedekind order can be
multiplied to exactly one base parameter, with a nonnilpotent residual
factor. The proof only uses unique factorization of the order. -/
private theorem first_layer (b : B) (bn : b≠0) (w : B) (nw : ¬b∣w)
    (red : B→+*C) (ker : ∀z,red z=0 ↔ b∣z) :
    ∃ m u:B,w*m=b*u ∧ ¬IsNilpotent (red u) := by
  obtain ⟨b',u,g,cop,gb,gu⟩ := UniqueFactorizationMonoid.exists_reduced_factors b bn w
  have nu : ¬IsUnit b' := by
    intro unit
    apply nw
    rw [←gb,←gu]
    exact mul_dvd_mul_left g unit.dvd
  refine ⟨b',u,by rw [←gb,←gu]; ring,?_⟩
  rintro ⟨n,hn⟩
  have dvd : b∣u^n := (ker _).mp (by rw [map_pow,hn])
  have part : b'∣b := gb ▸ dvd_mul_left ..
  have rel : IsRelPrime b' (u^n) := cop.pow_right
  exact nu (rel dvd_rfl (part.trans dvd))

/-- The trace of a primitive basis vector cannot be killed to second order
against every element of the order. This is the linear-algebra criterion
for a tame discriminant over a base DVR. -/
theorem no_second_layer (π : A) (πn : π≠0) (bn : algebraMap A B π≠0)
    (base : A→+*K) (red : B→+*C) (surj : Function.Surjective red)
    (kerA : ∀z,base z=0 ↔ π∣z) (kerB : ∀z,red z=0 ↔ algebraMap A B π∣z)
    (trace_comp : ∀z,base (Algebra.trace A B z)=Algebra.trace K C (red z))
    (p : ℕ) [CharP K p] (small : Module.finrank K C<p)
    (w : B) (deep : ∀s,π^2∣Algebra.trace A B (w*s)) :
    algebraMap A B π∣w := by
  by_contra nw
  obtain ⟨m,u,eq,nu⟩ := first_layer (algebraMap A B π) bn w nw red kerB
  apply nu
  apply (TraceSpecialization.trace_radical p small _).mp
  apply LinearMap.mem_ker.mpr
  ext y
  obtain ⟨s,rfl⟩ := surj y
  change Algebra.trace K C (red u*red s)=0
  rw [←map_mul,←trace_comp]
  apply (kerA _).mpr
  have multiple := deep (m*s)
  rw [←mul_assoc,eq,mul_assoc,←Algebra.smul_def,map_smul,smul_eq_mul,pow_two] at multiple
  exact (mul_dvd_mul_iff_left πn).mp multiple

#print axioms no_second_layer
end Lower6960.TameTrace
