import ProximityPrize.SubmissionLower.R6960RetainedGoodCrossing
import ProximityPrize.SubmissionLower.R6960TraceSpecialization

noncomputable section
set_option Elab.async false
namespace Lower6960.RetainedLineEvaluation
open Polynomial Algebra Module
open scoped Polynomial
open Lower6960.TraceSpecialization (idempotent_multiple)

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S] [Algebra (Polynomial k) S]

omit [Algebra k S] in
/-- A nonzero idempotent of a finite free line algebra survives on every point fibre.
If it vanished, its basis coordinates would be divisible by every power of X-a. -/
private theorem idempotent_survives [Module.Free (Polynomial k) S] {u : S} (id : u^2=u) (ne : u≠0)
    (a : k) : ¬algebraMap (Polynomial k) S (Polynomial.X-C a) ∣ u := by
  classical
  rintro ⟨w,eq⟩
  let b:=Module.Free.chooseBasis (Polynomial k) S
  obtain ⟨i,hi⟩ : ∃ i, b.repr u i≠0 := by
    by_contra! no
    apply ne
    apply b.repr.injective
    apply Finsupp.ext
    intro j
    simpa using no j
  let N:=(b.repr u i).natDegree
  have power (n:ℕ) : u^(n+1)=u := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,ih,←pow_two,id]
  have divides : (Polynomial.X-C a)^(N+1)∣b.repr u i := by
    refine ⟨b.repr (w^(N+1)) i,?_⟩
    have rel : u=(Polynomial.X-C a)^(N+1) • w^(N+1) := by
      calc u = u^(N+1) := (power N).symm
           _ = (algebraMap (Polynomial k) S (Polynomial.X-C a)*w)^(N+1) := congrArg (·^(N+1)) eq
           _ = _ := by rw [mul_pow,←map_pow,Algebra.smul_def]
    exact congrArg (fun p=>p i) ((congrArg b.repr rel).trans (b.repr.map_smul ..))
  have bound:=natDegree_le_of_dvd divides hi
  rw [natDegree_pow,natDegree_X_sub_C,mul_one] at bound
  omega

/-- A scalar-algebraic section on a reduced free line algebra is detected at a
single point. This allows the horizontal and vertical global sections to be charged
to the same crossing algebra even when the line fibres are reducible. -/
theorem detects_global [IsReduced S] [Module.Free (Polynomial k) S]
    (a : k) (u:S) (alg : IsIntegral k u) (vanish : algebraMap (Polynomial k) S (Polynomial.X-C a)∣u) : u=0 := by
  classical
  by_contra ne
  let B:=Algebra.adjoin k ({u}:Set S)
  let : Module.Finite k B := Algebra.finite_adjoin_simple_of_isIntegral alg
  let : IsArtinianRing B := isArtinian_of_tower k inferInstance
  let x : B:= ⟨u,Algebra.self_mem_adjoin_singleton k u⟩
  have nn : ¬IsNilpotent x := by
    intro nil
    exact ne (nil.map B.val.toRingHom).eq_zero
  obtain ⟨r,id,nz⟩:=Lower6960.TraceSpecialization.idempotent_multiple x nn
  have idem : (u*(r:S))^2=u*(r:S) := congrArg Subtype.val id
  have nonzero : u*(r:S)≠0 := fun eq=>nz (Subtype.ext eq)
  exact idempotent_survives idem nonzero a (vanish.trans (dvd_mul_right ..))

#print axioms detects_global

omit [Algebra k S] in
/-- A free polynomial algebra with one reduced point fibre is itself reduced. A
nilpotent can repeatedly be divided by the point equation, since that equation
is a nonzerodivisor and its image at the point vanishes. -/
theorem reduced_of_point [Module.Free (Polynomial k) S] {D : Type*} [CommRing D] [IsReduced D]
    (a : k) (atNode : S→+*D)
    (kernel : ∀ u, atNode u=0 → algebraMap (Polynomial k) S (Polynomial.X-C a)∣u) : IsReduced S := by
  classical
  constructor
  intro u nil
  let p : (Polynomial k):=Polynomial.X-C a
  have pn : p≠0 := X_sub_C_ne_zero _
  have div (n:ℕ) : ∃ w:S, IsNilpotent w ∧ u=p^n • w := by
    induction n with
    | zero => exact ⟨u,nil,by simp⟩
    | succ n ih =>
      obtain ⟨w,nw,eq⟩:=ih
      obtain ⟨v,rel⟩:=kernel w (nw.map atNode).eq_zero
      obtain ⟨m,hm⟩:=nw
      have van : p^m • v^m=0 := by
        rw [rel,mul_pow] at hm
        rw [Algebra.smul_def,map_pow]; exact hm
      refine ⟨v,⟨m,(smul_eq_zero_iff_right (pow_ne_zero _ pn)).mp van⟩,?_⟩
      rw [eq,rel,pow_succ,mul_smul,Algebra.smul_def p v]
  let b:=Module.Free.chooseBasis (Polynomial k) S
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  by_contra ne
  have nz : b.repr u i≠0 := by simpa using ne
  let n:=(b.repr u i).natDegree
  obtain ⟨v,_,eq⟩:=div (n+1)
  have large : p^(n+1)∣b.repr u i :=
    ⟨b.repr v i,congrArg (fun q=>q i) ((congrArg b.repr eq).trans (b.repr.map_smul ..))⟩
  have bad:=natDegree_le_of_dvd large nz
  rw [natDegree_pow,show p.natDegree=1 from natDegree_X_sub_C _,mul_one] at bad
  omega

#print axioms reduced_of_point
end Lower6960.RetainedLineEvaluation
