import ProximityPrize.SubmissionLower.R6966ProofHelperPhysicalModel
import Mathlib.RingTheory.Localization.Away.Basic

set_option Elab.async false

namespace Research6966.GlobalPrimitive
open Polynomial
open scoped Polynomial
noncomputable section

/-- Clearing denominators only needs units in the target. It therefore
applies to the physical chart localized away from its CRT denominators. -/
def Clears {R S:Type*} [CommRing R] [CommRing S] (f:R→+*S) : Prop :=
  ∀ y:S,∃ a d:R,IsUnit (f d) ∧ f a=f d*y

theorem clear_localization {R S:Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M:Submonoid R) [IsLocalization M S] : Clears (algebraMap R S) := by
  intro y
  obtain ⟨d,a,id⟩:=IsLocalization.exists_integer_multiple M y
  exact ⟨a,d.val,IsLocalization.map_units S d,by simpa only [Algebra.smul_def] using id⟩

theorem clear_poly {R S:Type*} [CommRing R] [CommRing S] (f:R→+*S) (base:Clears f) :
    ∀ P:S[X],∃ (A:R[X]) (d:R),IsUnit (f d) ∧ A.map f=C (f d)*P := by
  intro P
  induction P using Polynomial.induction_on' with
  | add P Q hp hq =>
    obtain ⟨A,a,au,hA⟩:=hp
    obtain ⟨B,b,bu,hB⟩:=hq
    refine ⟨C b*A+C a*B,a*b,(map_mul f a b) ▸ au.mul bu,?_⟩
    rw [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_C,hA,hB,map_mul f,map_mul]
    ring
  | monomial j c =>
    obtain ⟨a,d,du,eq⟩:=base c
    exact ⟨monomial j a,d,du,by rw [Polynomial.map_monomial,C_mul_monomial,eq]⟩

theorem lift_clear {R S:Type*} [CommRing R] [CommRing S] (f:R→+*S) (base:Clears f) :
    Clears (mapRingHom f) := by
  intro P
  obtain ⟨A,d,du,id⟩:=clear_poly f base P
  exact ⟨A,C d,by simpa only [coe_mapRingHom,Polynomial.map_C] using du.map (C:S→+*S[X]),
    by simpa only [coe_mapRingHom,Polynomial.map_C] using id⟩

private theorem right_unit {S:Type*} [CommRing S] [IsDomain S] {H A B:S} (hn:H≠0)
    (eq:H=A*B) (dv:H∣A) : IsUnit B := by
  obtain ⟨t,id⟩:=dv
  have an:=left_ne_zero_of_mul (eq ▸ hn)
  have cancel:A*1=A*(B*t):=by rw [mul_one,←mul_assoc,←eq];exact id
  exact IsUnit.of_mul_eq_one t (mul_left_cancel₀ an cancel).symm

theorem irreducible_image {R S:Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (f:R→+*S) (inj:Function.Injective f) (clear:Clears f) {p:R} (prime:Prime p)
    (nu:¬IsUnit (f p)) : Irreducible (f p) := by
  have nz:f p≠0:=(map_ne_zero_iff _ inj).mpr prime.ne_zero
  refine ⟨nu,?_⟩
  intro A B pair
  obtain ⟨a,d,du,eqA⟩:=clear A
  obtain ⟨b,e,eu,eqB⟩:=clear B
  have div:p∣a*b:=by
    use d*e
    apply inj
    rw [map_mul,map_mul,map_mul,eqA,eqB,pair];ring
  have descend {a d:R} {A:S} (dv:p∣a) (eq:f a=f d*A) (u:IsUnit (f d)) : f p∣A :=
    (associated_unit_mul_left _ _ u).dvd_iff_dvd_right.mp (eq ▸ map_dvd f dv)
  rcases prime.dvd_or_dvd div with left|right
  · exact Or.inr (right_unit nz pair (descend left eqA du))
  · exact Or.inl (right_unit nz (pair.trans (mul_comm ..)) (descend right eqB eu))

/-- A prime equation over the localized ring has one global prime
representative up to a unit of that ring. No denominator degree is charged. -/
theorem global_prime {R S:Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [CommRing S] [IsDomain S] (f:R→+*S) (inj:Function.Injective f) (clear:Clears f)
    {H:S} (hp:Prime H) : ∃ P:R,Prime P ∧ Associated (f P) H := by
  classical
  have extract (r:R):r≠0 → H∣f r → ∃ P:R,Prime P ∧ Associated (f P) H := by
    induction r using UniqueFactorizationMonoid.induction_on_prime with
    | h₁=>simp
    | h₂ e unit=>
      intro _ dv;exact False.elim (hp.not_unit (isUnit_of_dvd_unit dv (unit.map f)))
    | h₃ r p _ pr ih=>
      intro nz dv
      rw [map_mul] at dv
      rcases hp.dvd_or_dvd dv with yes|later
      · have ir:=irreducible_image f inj clear pr (fun un=>hp.not_unit (isUnit_of_dvd_unit yes un))
        exact ⟨p,pr,(hp.irreducible.associated_of_dvd ir yes).symm⟩
      · exact ih (right_ne_zero_of_mul nz) later
  obtain ⟨r,d,unit,eq⟩:=clear H
  have nz:r≠0:=by intro z;rw [z,map_zero] at eq;exact (mul_ne_zero unit.ne_zero hp.ne_zero) eq.symm
  exact extract r nz (eq ▸ dvd_mul_left _ _)

#print axioms global_prime

theorem clear_comp {R S T:Type*} [CommRing R] [CommRing S] [CommRing T] (f:R→+*S) (g:S→+*T)
    (a:Clears f) (b:Clears g) : Clears (g.comp f) := by
  intro z
  obtain ⟨p,q,qu,eq⟩:=b z
  obtain ⟨n,d,du,nv⟩:=a p
  obtain ⟨m,e,eu,mv⟩:=a q
  refine ⟨n*e,m*d,?_,?_⟩
  · simp only [RingHom.comp_apply,map_mul,mv]
    exact ((eu.map g).mul qu).mul (du.map g)
  · simp only [RingHom.comp_apply,map_mul,nv,mv,eq]
    ring

theorem prime_image {R S:Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (f:R→+*S) (inj:Function.Injective f) (clear:Clears f) {p:R} (prime:Prime p)
    (nu:¬IsUnit (f p)) : Prime (f p) := by
  refine ⟨(map_ne_zero_iff _ inj).mpr prime.ne_zero,nu,?_⟩
  rintro A B ⟨t,eq⟩
  obtain ⟨a,da,au,ac⟩:=clear A
  obtain ⟨b,db,bu,bc⟩:=clear B
  obtain ⟨c,dc,cu,cc⟩:=clear t
  have pay:p∣dc*(a*b):=by
    use da*db*c
    apply inj
    simp only [map_mul,ac,bc,cc]
    calc
      _ = (f dc)*(f da)*(f db)*(A*B) := by ring
      _ = _ := by rw [eq];ring
  rcases prime.dvd_or_dvd pay with unit|divide
  · exact False.elim (nu (isUnit_of_dvd_unit (map_dvd f unit) cu))
  rcases prime.dvd_or_dvd divide with l|r
  · exact Or.inl ((associated_unit_mul_left _ _ au).dvd_iff_dvd_right.mp (ac ▸ map_dvd f l))
  · exact Or.inr ((associated_unit_mul_left _ _ bu).dvd_iff_dvd_right.mp (bc ▸ map_dvd f r))

theorem clear_two {R S:Type*} [CommRing R] [CommRing S] (f:R→+*S) (base:Clears f) :
    ∀ P:S[X][X],∃ (N:R[X][X]) (d:R),IsUnit (f d) ∧ K1_14_1_4.doubleMap f N=K1_14_1.jetConstant (f d)*P := by
  intro P
  induction P using Polynomial.induction_on' with
  | add P Q hp hq=>
    obtain ⟨N,d,du,hN⟩:=hp
    obtain ⟨M,e,eu,hM⟩:=hq
    refine ⟨K1_14_1.jetConstant e*N+K1_14_1.jetConstant d*M,d*e,(map_mul f _ _) ▸ du.mul eu,?_⟩
    have const (r:R):K1_14_1_4.doubleMap f (K1_14_1.jetConstant r)=K1_14_1.jetConstant (f r):=by
      simp [K1_14_1_4.doubleMap,K1_14_1.jetConstant]
    rw [map_add,map_mul,map_mul,const,const,hN,hM,map_mul f,map_mul];ring
  | monomial j p=>
    obtain ⟨N,d,du,hN⟩:=clear_poly f base p
    refine ⟨monomial j N,d,du,?_⟩
    change (monomial j N).map (mapRingHom f)=C (C (f d))*monomial j p
    rw [map_monomial,coe_mapRingHom,hN,C_mul_monomial]

/-- A positive-slope prime cannot divide a nonzero scalar denominator.
This descends generic divisibility directly over the localized node chart. -/
theorem descend_jet {R S:Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (f:R→+*S) (inj:Function.Injective f) (clear:Clears f) {p q:R[X][X]}
    (pr:Prime p) (pos:0<p.natDegree) (div:K1_14_1_4.doubleMap f p∣K1_14_1_4.doubleMap f q) : p∣q := by
  obtain ⟨s,eq⟩:=div
  obtain ⟨n,d,du,id⟩:=clear_two f clear s
  have faithful:Function.Injective (K1_14_1_4.doubleMap f):=map_injective _ (map_injective _ inj)
  have c:K1_14_1_4.doubleMap f (K1_14_1.jetConstant d)=K1_14_1.jetConstant (f d):=by
    simp [K1_14_1_4.doubleMap,K1_14_1.jetConstant]
  have product:p∣K1_14_1.jetConstant d*q := by
    use n;apply faithful
    rw [map_mul,map_mul,c,eq,id];ring
  rcases pr.dvd_or_dvd product with bad|yes
  · have dn:d≠0:=fun zero=>du.ne_zero (zero ▸ map_zero f)
    have nz:(K1_14_1.jetConstant d:R[X][X])≠0:=C_ne_zero.mpr (C_ne_zero.mpr dn)
    have impossible:=natDegree_le_of_dvd bad nz
    simp [K1_14_1.jetConstant] at impossible;omega
  · exact yes

theorem unit_constant {R:Type*} [CommRing R] [IsDomain R] {p:R[X][X]} (unit:IsUnit p) :
    ∃ c:R,IsUnit c ∧ p=K1_14_1.jetConstant c := by
  obtain ⟨q,qu,id⟩:=Polynomial.isUnit_iff.mp unit
  obtain ⟨c,cu,cq⟩:=Polynomial.isUnit_iff.mp qu
  exact ⟨c,cu,id.symm.trans (congrArg C cq.symm)⟩

#print axioms descend_jet
end
end Research6966.GlobalPrimitive
