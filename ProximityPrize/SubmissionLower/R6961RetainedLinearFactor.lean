import ProximityPrize.SubmissionLower.R6961RetainedLinearBase
import Mathlib.RingTheory.Polynomial.GaussLemma

set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2300000

namespace Lower6961.RetainedLinear
noncomputable section
open Polynomial
open scoped Polynomial nonZeroDivisors

variable {F E : Type} [Field F] [Field E] [Algebra F E]

abbrev Plane (F : Type) [Field F] := Polynomial (Polynomial F)

def arithmetic (P : Plane F) : Polynomial (Fn F) := P.map (incl F)

def geometric (P : Plane F) : Polynomial (Fn E) := P.map (base (E:=E))

theorem geometric_map (P : Plane F) : geometric (E:=E) P=(arithmetic P).map rationalConstants := by
  unfold geometric arithmetic
  rw [Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro a
  simp [base]

theorem geometric_deg (P : Plane F) : (geometric (E:=E) P).natDegree=P.natDegree := by
  have injective : Function.Injective (base (F:=F) (E:=E)) :=
    (incl_injective E).comp (constants_injective (F:=F) (E:=E))
  exact natDegree_map_eq_of_injective injective P

theorem arithmetic_irred {P : Plane F} (ir : Irreducible P) (pos : 0<P.natDegree) :
    Irreducible (arithmetic P) :=
  (ir.isPrimitive (Nat.ne_of_gt pos)).irreducible_iff_irreducible_map_fraction_map.mp ir

/-- Content-freeness survives each physical abscissa because an identically
vanishing fibre would give a nonunit abscissa factor. -/
theorem node_not_zero {P : Plane F} (ir : Irreducible P) (pos : 0<P.natDegree) (x : F) :
    P.map (evalRingHom x)≠0 := by
  intro zero
  have prime := ir.isPrimitive (Nat.ne_of_gt pos)
  apply (irreducible_X_sub_C x).not_isUnit
  apply isPrimitive_iff_isUnit_of_C_dvd.mp prime
  apply (C_dvd_iff_dvd_coeff ..).mpr
  intro i
  apply dvd_iff_isRoot.mpr
  have gone := congrArg (fun Q : (Polynomial F) => Q.coeff i) zero
  simpa only [Polynomial.IsRoot,coeff_map,coe_evalRingHom,coeff_zero] using gone

abbrev numerator (r : Fn E) : (Polynomial E) := IsFractionRing.num (Polynomial E) r
abbrev denominator (r : Fn E) : (Polynomial E) := (IsFractionRing.den (Polynomial E) r).val

theorem denominator_ne (r : Fn E) : denominator r≠0 :=
  nonZeroDivisors.coe_ne_zero (IsFractionRing.den (Polynomial E) r)

theorem numerator_eq (r : Fn E) : r*incl E (denominator r)=incl E (numerator r) :=
  (IsFractionRing.num_mul_den_eq_num_iff_eq' (A:=(Polynomial E))).mpr rfl

private def line (r : Fn E) : Plane E := C (denominator r)*Polynomial.X+C (-numerator r)

private theorem line_primitive (r : Fn E) : (line r).IsPrimitive := by
  apply isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro b hb
  have coef := (C_dvd_iff_dvd_coeff ..).mp hb
  have first : b∣denominator r := by simpa [line] using coef 1
  have second : b∣numerator r := dvd_neg.mp (by simpa [line] using coef 0)
  exact IsFractionRing.num_den_reduced (Polynomial E) r second first

private theorem mapped_line (r : Fn E) :
    (line r).map (incl E)=C (incl E (denominator r))*(Polynomial.X-C r) := by
  simp only [line,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
    Polynomial.map_neg,map_neg]
  rw [← numerator_eq r]
  rw [mul_sub, mul_comm r, C_mul]
  ring

private theorem line_prod_primitive (s : Multiset (Fn E)) : ((s.map line).prod).IsPrimitive := by
  letI : NormalizedGCDMonoid (Polynomial E) := Classical.choice inferInstance
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    rw [Multiset.map_cons,Multiset.prod_cons]
    exact (line_primitive r).mul ih

private theorem mapped_lines (s : Multiset (Fn E)) :
    ((s.map line).prod).map (incl E)=C ((s.map (fun r=>incl E (denominator r))).prod) *
      (s.map (fun r=>Polynomial.X-C r)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    simp only [Multiset.map_cons,Multiset.prod_cons,Polynomial.map_mul,mapped_line,ih,C_mul]
    ring

/-- A received root in a nonzero physical fibre is carried by a
regular degree-one geometric branch. The denominator is obtained from
the primitive factor itself. -/
theorem exists_regular_root {P : Plane F} (ir : Irreducible P) (pos : 0<P.natDegree)
    (splits : (geometric (E:=E) P).Splits) (x t : F) (hit : (P.map (evalRingHom x)).eval t=0) :
    ∃ r ∈ (geometric (E:=E) P).roots,
      (denominator r).eval (algebraMap F E x)≠0 ∧
      (numerator r).eval (algebraMap F E x)=(denominator r).eval (algebraMap F E x)*algebraMap F E t := by
  classical
  let Qe := P.map (constants (F:=F) (E:=E))
  let L := geometric (E:=E) P
  let rs := L.roots
  let G := (rs.map line).prod
  let b := (rs.map (fun r=>incl E (denominator r))).prod
  have Pn := ir.ne_zero
  have geo : Qe.map (incl E)=L := by
    simp [Qe, L, geometric, base, Polynomial.map_map]
  have dn : b≠0 := by
    apply Multiset.prod_ne_zero
    intro mem
    obtain ⟨r,_,eq⟩ := Multiset.mem_map.mp mem
    exact ((map_ne_zero_iff _ (incl_injective E)).mpr (denominator_ne r)) eq
  have Gmap : G.map (incl E)=C b*(rs.map (fun r=>Polynomial.X-C r)).prod := mapped_lines rs
  have fac := splits.eq_prod_roots
  have mapped_dvd : G.map (incl E)∣Qe.map (incl E) := by
    refine ⟨C (L.leadingCoeff/b),?_⟩
    rw [geo,Gmap]
    change L=C b*(rs.map (fun r=>Polynomial.X-C r)).prod*C (L.leadingCoeff/b)
    calc
      _ = C L.leadingCoeff*(rs.map (fun r=>Polynomial.X-C r)).prod := fac
      _ = _ := by
        rw [mul_right_comm,← C_mul,← mul_div_assoc,mul_div_cancel_left₀ _ dn]
  obtain ⟨q,hq⟩ := (line_prod_primitive rs).dvd_of_fraction_map_dvd_fraction_map mapped_dvd
  have Gn : G≠0 := (line_prod_primitive rs).ne_zero
  have Yn : Qe≠0 := by
    have inj : Function.Injective (Polynomial.mapRingHom (constants (F:=F) (E:=E))) :=
      Polynomial.map_injective _ (constants_injective (F:=F) (E:=E))
    exact (map_ne_zero_iff _ inj).mpr Pn
  have qn : q≠0 := fun z=>Yn (by rw [hq,z,mul_zero])
  have degg : G.natDegree=P.natDegree := by
    rw [← natDegree_map_eq_of_injective (incl_injective E) G,Gmap,natDegree_C_mul dn,
      natDegree_multiset_prod_X_sub_C_eq_card,← splits.natDegree_eq_card_roots]
    exact geometric_deg P
  have degY : Qe.natDegree=P.natDegree := natDegree_map_eq_of_injective constants_injective _
  have size : q.natDegree=0 := by
    rw [hq,natDegree_mul Gn qn,degg] at degY
    omega
  let c := q.coeff 0
  have facY : Qe=G*C c := hq.trans (by rw [eq_C_of_natDegree_eq_zero size])
  let x' := algebraMap F E x
  let t' := algebraMap F E t
  let node := evalRingHom x'
  have compare : Qe.map node=(P.map (evalRingHom x)).map (algebraMap F E) := by
    apply Polynomial.ext
    intro i
    simp only [Qe,coeff_map,node,coe_evalRingHom,eval_constants,x']
  have Yn' : Qe.map node≠0 := by
    rw [compare]
    intro zero
    apply node_not_zero ir pos x
    apply Polynomial.map_injective _ (algebraMap F E).injective
    simpa only [Polynomial.map_zero] using zero
  have cn' : c.eval x'≠0 := by
    intro ch
    apply Yn'
    rw [facY,Polynomial.map_mul,Polynomial.map_C,coe_evalRingHom,ch,C_0,mul_zero]
  have hit' : (Qe.map node).eval t'=0 := by
    rw [compare,eval_map_apply,hit,map_zero]
  let select : Plane E →+* E := (evalRingHom t').comp (mapRingHom node)
  change select Qe=0 at hit'
  rw [facY,map_mul] at hit'
  have pc : select (C c)=c.eval x' := by
    simp only [select, RingHom.comp_apply,coe_mapRingHom,Polynomial.map_C,
      coe_evalRingHom,eval_C,node]
  rw [pc] at hit'
  have gone := (mul_eq_zero.mp hit').resolve_right cn'
  change select (rs.map line).prod=0 at gone
  rw [← Multiset.prod_hom, Multiset.map_map] at gone
  obtain ⟨r,hr,val⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp gone)
  have v : (denominator r).eval x'*t'+(-(numerator r)).eval x'=0 := by
    simpa [select,node,line] using val
  rw [eval_neg] at v
  have relation : (numerator r).eval x'=(denominator r).eval x'*t' := by
    linear_combination -v
  have den : (denominator r).eval x'≠0 := by
    intro collapse
    have num : (numerator r).eval x'=0 := by rw [relation,collapse,zero_mul]
    have d₀ : Polynomial.X-C x'∣numerator r := dvd_iff_isRoot.mpr num
    have d₁ : Polynomial.X-C x'∣denominator r := dvd_iff_isRoot.mpr collapse
    exact (irreducible_X_sub_C x').not_isUnit (IsFractionRing.num_den_reduced (Polynomial E) r d₀ d₁)
  exact ⟨r,hr,den,relation⟩

#print axioms node_not_zero
#print axioms exists_regular_root
end
end Lower6961.RetainedLinear
