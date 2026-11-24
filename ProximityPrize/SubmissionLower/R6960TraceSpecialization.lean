import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Projection

noncomputable section
set_option Elab.async false
namespace Lower6960.TraceSpecialization
open LinearMap
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]

/-- A nonnilpotent element of a finite algebra has a nonzero idempotent
multiple. Stabilize its powers before choosing the multiplier. -/
theorem idempotent_multiple [IsArtinianRing A] (x : A) (nx : ¬IsNilpotent x) :
    ∃ h : A,(x*h)^2=x*h ∧ x*h≠0 := by
  obtain ⟨n,y,hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1:A)
  let r:=x*y
  have stable {s t : A} (fix : s*t=s) (j : ℕ) : s*t^j=s := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ,←mul_assoc,ih,fix]
  have fixed : x^n*r=x^n := by simpa [r,pow_succ,mul_assoc] using hy
  have last : r^n*r=r^n := by
    have eq := congrArg (·*y^n) fixed
    simpa only [r,mul_pow,mul_assoc,mul_left_comm,mul_comm] using eq
  let h:=y*r^n
  have he : x*h=r^n := by dsimp [h]; rw [←mul_assoc,mul_comm (x*y)]; exact last
  refine ⟨h,?_,?_⟩
  · rw [he,pow_two]; exact stable last n
  · intro z
    have vanish:=stable fixed n
    rw [←he,z,mul_zero] at vanish
    exact nx ⟨n,vanish.symm⟩

/-- In characteristic exceeding the algebra dimension, the radical of the
trace pairing consists exactly of the nilpotents, including for nonreduced
specializations. No hypotheses about splitting of the fibre are required. -/
theorem trace_radical (p : ℕ) [CharP K p] (small : Module.finrank K A<p) (x : A) :
    x∈LinearMap.ker (Algebra.traceForm K A) ↔ IsNilpotent x := by
  constructor
  · intro hx
    by_contra nx
    have : IsArtinianRing A := isArtinian_of_tower K (inferInstance : IsArtinian K A)
    obtain ⟨y,idemp,ne⟩ := idempotent_multiple x nx
    let e:=Algebra.lmul K A (x*y)
    have proj : IsIdempotentElem e := by
      change e*e=e
      change Algebra.lmul K A (x*y)*Algebra.lmul K A (x*y)=_
      rw [←map_mul,←pow_two,idemp]
    have trace : LinearMap.trace K A e=0 := LinearMap.congr_fun (LinearMap.mem_ker.mp hx) y
    rw [proj.isProj_range.trace] at trace
    have low := (Submodule.finrank_le (LinearMap.range e)).trans_lt small
    have dim := Nat.eq_zero_of_dvd_of_lt ((CharP.cast_eq_zero_iff K p _).mp trace) low
    have bot : LinearMap.range e = ⊥ := Submodule.finrank_eq_zero.mp dim
    have zero := LinearMap.range_eq_bot.mp bot
    have bad := LinearMap.congr_fun zero (1:A)
    change (x*y)*1=0 at bad
    exact ne (by simpa only [mul_one] using bad)
  · intro nil
    apply LinearMap.mem_ker.mpr
    ext y
    change Algebra.trace K A (x*y)=0
    rw [Algebra.trace_apply]
    apply (LinearMap.isNilpotent_trace_of_isNilpotent _).eq_zero
    exact ((Commute.all x y).isNilpotent_mul_right nil).map (Algebra.lmul K A)

/-- A change of order cannot gain more trace radical than the corank of
its reduction. This saves one factor of the index in a trace discriminant. -/
theorem radical_specialization {B : Type*} [CommRing B] [Algebra K B] [FiniteDimensional K B]
    (p : ℕ) [CharP K p] (a : Module.finrank K A<p) (b : Module.finrank K B<p)
    (φ : A →ₐ[K] B) :
    Module.finrank K (LinearMap.ker (Algebra.traceForm K A)) ≤
      Module.finrank K (LinearMap.ker φ.toLinearMap) + Module.finrank K (LinearMap.ker (Algebra.traceForm K B)) := by
  let U:=LinearMap.ker (Algebra.traceForm K A)
  let V:=LinearMap.ker (Algebra.traceForm K B)
  let g : U→ₗ[K]V := (φ.toLinearMap.comp U.subtype).codRestrict V (fun x=>
    (trace_radical p b _).mpr (((trace_radical p a _).mp x.property).map φ))
  let lift : LinearMap.ker g →ₗ[K] LinearMap.ker φ.toLinearMap :=
    (U.subtype.comp (LinearMap.ker g).subtype).codRestrict _ (fun x=>by
      apply LinearMap.mem_ker.mpr
      exact congrArg Subtype.val (LinearMap.mem_ker.mp x.property))
  have inj : Function.Injective lift := by
    intro x y eq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : LinearMap.ker φ.toLinearMap=>(w:A)) eq
  have ker := LinearMap.finrank_le_finrank_of_injective (f:=lift) inj
  have ran := Submodule.finrank_le (LinearMap.range g)
  have both := g.finrank_range_add_finrank_ker
  change Module.finrank K U≤_+Module.finrank K V
  omega

#print axioms trace_radical
#print axioms radical_specialization
end Lower6960.TraceSpecialization
