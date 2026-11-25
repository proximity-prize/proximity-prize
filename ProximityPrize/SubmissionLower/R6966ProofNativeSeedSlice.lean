import ProximityPrize.SubmissionLower.R6966ProofNativeProjectedWitness

set_option Elab.async false

-- merged module R6966ProofNativeOrdinateMass
section Merged_R6966ProofNativeOrdinateMass

namespace Research6966.NativeOrdinateMass
open Finset Polynomial Module
open K1_14 (Jet Seeds Equation)
open K1_14_2 (Ambient toJet FibreRing OverSeeds mapGenericSeed)
open K1_14_2_2 (Active sectionDegree mass)
open K1_14_3 (Surface OnSeedFibre SeedField SeedClosure ProjectedProduct)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false

private def ordinate (J:Ideal Ambient) : OverSeeds J := Ideal.Quotient.mk _ (MvPolynomial.X 0)
private def relation (J:Ideal Ambient) : SeedField[X] := minpoly SeedField (ordinate J)

private theorem info {J:Ideal Ambient} (act:Active J) :
    relation J≠0 ∧ (relation J).natDegree≤sectionDegree J 0 := by
  letI : Module.Finite SeedField (OverSeeds J):=act.seed_finite
  exact ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R:=SeedField) (ordinate J)),minpoly.natDegree_le _⟩

private theorem kills {J:Ideal Ambient} {q:Surface} (src:q.asIdeal=J.comap toJet) {y v:SeedClosure}
    (point:OnSeedFibre q y v) (act:Active J) : aeval y (relation J)=0 := by
  letI:Module.Finite SeedField (OverSeeds J):=act.seed_finite
  let ev:FibreRing→ₐ[SeedField]SeedClosure:=MvPolynomial.aeval ![y,v]
  have same:ev.toRingHom.comp mapGenericSeed=K1_14_2_6.genericSeedPoint y v := by
    simpa only [ev,MvPolynomial.aeval_X,Matrix.cons_val_zero,Matrix.cons_val_one]
      using (K1_14_2_6_1.seedPoint ev).symm
  have sign:J≤RingHom.ker (K1_14_2_6.genericSeedPoint y v) := by
    intro x hx
    have onto:Function.Surjective toJet:=by
      rw [K1_14_2_2_4_1.toJet_equiv];exact K1_14_2_2_4_1.ambientToJet.symm.surjective
    obtain ⟨P,rfl⟩:=onto x
    have eq: (RingHom.ker (K1_14_2_6.genericSeedPoint y v)).comap toJet=J.comap toJet:=
      (K1_14_3R_1.seed_chart_ker point).trans src
    exact (show P∈(RingHom.ker (K1_14_2_6.genericSeedPoint y v)).comap toJet from eq ▸ hx)
  have passes:J.map mapGenericSeed ≤ RingHom.ker ev.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [RingHom.comap_ker,same];exact sign
  let use:OverSeeds J→ₐ[SeedField]SeedClosure:=
    Ideal.Quotient.liftₐ _ ev (fun x hx=>passes hx)
  have value:use (ordinate J)=y := by change ev (MvPolynomial.X 0)=y;simp [ev]
  rw [←value,aeval_algHom_apply]
  simp [relation,minpoly.aeval]

private theorem curve_at_root {F:Type*} [Field F] (D:F[X]) (y v:F) (zero:D.eval y=0) :
    (C D:F[X][X])∈TerminalProjection.fibrePoint y v := by
  obtain ⟨Q,eq⟩:=(dvd_iff_isRoot.mpr zero : Polynomial.X-C y∣D)
  rw [eq,map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))

private theorem order_of_root (D:Equation) {q:Surface}
    (root:∀ y v,OnSeedFibre q y v → (D.map K1_14_3.seedGeneric).eval y=0) : K1_14_3.OrderAt q (C D) 1 := by
  intro y v hv
  simp only [K1_14_3.fibreRow,Polynomial.map_C,coe_mapRingHom]
  have powered:=Ideal.pow_mem_pow (curve_at_root _ y v (root y v hv)) 1
  rw [pow_one (C (D.map K1_14_3.seedGeneric))] at powered
  exact powered

/-- The ordinate characterising polynomial on the union of the retained
surfaces has degree bounded by the already-budgeted seed-fibre dimension.
The argument works for every projected product and for any subset of the
retained parents. -/
theorem projected_degree {parents:Finset Surface} {H:Equation} (pr:ProjectedProduct parents H)
    (sources:Finset (Ideal Ambient)) (active:∀ J∈sources,Active J)
    (covered:∀ q∈parents,∃ J∈sources,q.asIdeal=J.comap toJet) : H.natDegree≤mass sources 0 := by
  let prod:SeedField[X]:=∏J∈sources,relation J
  have pn:prod≠0:=Finset.prod_ne_zero_iff.mpr (fun J hJ=>(info (active J hJ)).1)
  have degree:prod.natDegree≤mass sources 0 := by
    rw [show prod.natDegree=∑J∈sources,(relation J).natDegree from
      natDegree_prod _ _ (fun J hJ=>(info (active J hJ)).1)]
    exact sum_le_sum (fun J hJ=>(info (active J hJ)).2)
  let D:=IsLocalization.integerNormalization (nonZeroDivisors Seeds) prod
  obtain ⟨a,an,scaled⟩:=IsLocalization.integerNormalization_spec (nonZeroDivisors Seeds) prod
  have integral:D.map (algebraMap Seeds SeedField)=C (algebraMap Seeds SeedField a)*prod := by
    simpa only [Algebra.smul_def,Polynomial.algebraMap_apply] using scaled
  have dn:D≠0:=(IsFractionRing.integerNormalization_eq_zero_iff (A:=Seeds) (p:=prod)).not.mpr pn
  have an':algebraMap Seeds SeedField a≠0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Seeds SeedField)).mpr (nonZeroDivisors.ne_zero an)
  have dd:D.natDegree=prod.natDegree := by
    rw [←natDegree_map_eq_of_injective (IsFractionRing.injective Seeds SeedField) D,integral,natDegree_C_mul an']
  have div:=pr.divides_leading (C D) 1 (C_ne_zero.mpr dn) (fun q hq=>order_of_root D (by
    obtain ⟨J,mem,src⟩:=covered q hq
    intro y v point
    have zero:aeval y prod=0:=by
      rw [show aeval y prod=∏J∈sources,aeval y (relation J) from map_prod ..,prod_eq_zero_iff]
      exact ⟨J,mem,kills src point (active J mem)⟩
    change (D.map ((algebraMap SeedField SeedClosure).comp (algebraMap Seeds SeedField))).eval y=0
    rw [←Polynomial.map_map,integral,Polynomial.map_mul,Polynomial.map_C,eval_mul,eval_C,eval_map]
    change _*aeval y prod=0
    rw [zero,mul_zero]))
  have hd:H∣D:=by simpa only [natDegree_C,Nat.sub_zero,pow_one,leadingCoeff_C] using div
  exact (natDegree_le_of_dvd hd dn).trans (dd ▸ degree)

#print axioms projected_degree

/-- Every native ordinate relation on all selected parents contains their
squarefree projected product. -/
theorem divides_of_member {parents:Finset Surface} {H D:Equation} (pr:ProjectedProduct parents H)
    (vanish:∀ q∈parents,C D∈q.asIdeal) : H∣D := by
  by_cases z:D=0
  · simp [z]
  have hd:=pr.divides_leading (C D) 1 (C_ne_zero.mpr z) (fun q hq=>order_of_root D (by
    intro y v point
    have mem:=vanish q hq
    rw [←point,RingHom.mem_ker] at mem
    simpa only [K1_14_3.seedFibreEval,coe_eval₂RingHom,eval₂_C,eval_map] using mem))
  simpa only [natDegree_C,Nat.sub_zero,pow_one,leadingCoeff_C] using hd

#print axioms divides_of_member
end
end Research6966.NativeOrdinateMass

end Merged_R6966ProofNativeOrdinateMass

-- merged module R6966ProofNativeSeedSlice
section Merged_R6966ProofNativeSeedSlice

namespace Research6966.NativeSeedSlice
open Polynomial
open K1_14 (FX Seeds Equation)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (SectionField SectionAmbient OverOrdinate sectionBase sectionSeedLine sliceParameter Active sectionDegree)
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

abbrev B := MvPolynomial (Fin 4) FX
abbrev Lift := MvPolynomial (Fin 2) Equation
local instance (priority := 1100) quotientSemiring (J:Ideal Ambient) : CommSemiring (Ambient ⧸ J) :=
  (Ideal.Quotient.commRing J).toCommSemiring
abbrev Source (J:Ideal Ambient) := MvPolynomial (Fin 2) (Ambient ⧸ J)
def z (i:Fin 2) : Equation := C (MvPolynomial.X i)
def scalar : FX →+* Lift := MvPolynomial.C.comp (C.comp MvPolynomial.C)
def parameters : Fin 4 → Lift :=
  ![(MvPolynomial.X 0 : Lift), MvPolynomial.X 1,
    MvPolynomial.C (z 0)+MvPolynomial.X 0*MvPolynomial.C (z 1),MvPolynomial.C (Polynomial.X : Equation)]
def backBase : B →+* Lift := MvPolynomial.eval₂Hom scalar parameters
def back : B[X] →+* Lift := eval₂RingHom backBase (MvPolynomial.C (z 1))
def send (J:Ideal Ambient) : Lift →+* Source J :=
  MvPolynomial.map (((Ideal.Quotient.mk J).comp toJet).comp C)
def place (J:Ideal Ambient) : B →+* Source J := (send J).comp backBase
def denom (J:Ideal Ambient) : Submonoid (Source J) :=
  (nonZeroDivisors B).map (place J).toMonoidHom
abbrev Target (J:Ideal Ambient) := Localization (denom J)
def loc (J:Ideal Ambient) := algebraMap (Source J) (Target J)
private theorem units (J:Ideal Ambient) (s:nonZeroDivisors B) :
    IsUnit (((loc J).comp (place J)) s) :=
  IsLocalization.map_units (Target J) (⟨place J s,⟨s.val,s.property,rfl⟩⟩:denom J)
def fieldMap (J:Ideal Ambient) : SectionField →+* Target J :=
  IsLocalization.lift (M:=nonZeroDivisors B) (g:=(loc J).comp (place J)) (units J)
theorem field_base (J:Ideal Ambient) (s:B) :
    fieldMap J (algebraMap B SectionField s)=loc J (place J s) := IsLocalization.lift_eq (units J) s
def ambient (J:Ideal Ambient) : Ambient →+* Source J := MvPolynomial.C.comp (Ideal.Quotient.mk J)
def chart (J:Ideal Ambient) : SectionAmbient →+* Target J :=
  MvPolynomial.eval₂Hom (fieldMap J) (fun i => loc J (ambient J (MvPolynomial.X i)))
@[simp] private theorem chart_X (J:Ideal Ambient) (i:Fin 4) :
    chart J (MvPolynomial.X i)=loc J (ambient J (MvPolynomial.X i)) := by simp [chart]
@[simp] private theorem chart_C (J:Ideal Ambient) (a:SectionField) :
    chart J (MvPolynomial.C a)=fieldMap J a := by simp [chart]

private theorem place_C (J:Ideal Ambient) (c:FX) : place J (MvPolynomial.C c)=ambient J (MvPolynomial.C c) := by
  simp [place,backBase,send,scalar,ambient,K1_14_2.toJet,K1_14_2.toRoot,K1_14_2.rootIncl,K1_14_2.rootSeeds]
private theorem place_X (J:Ideal Ambient) (i:Fin 4) :
    place J (MvPolynomial.X i) = ![MvPolynomial.X 0,MvPolynomial.X 1,
      ambient J (MvPolynomial.X 0)+MvPolynomial.X 0*ambient J (MvPolynomial.X 1),
      ambient J (MvPolynomial.X 2)] i := by
  fin_cases i <;> simp [place,backBase,send,parameters,z,ambient,
    K1_14_2.toJet,K1_14_2.toRoot,K1_14_2.rootIncl,K1_14_2.rootSeeds]
private theorem chart_base (J:Ideal Ambient) : (chart J).comp sectionBase=(loc J).comp (ambient J) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply,sectionBase,MvPolynomial.map_C,chart_C]
    change fieldMap J (algebraMap B SectionField (MvPolynomial.C c))=_
    rw [field_base,place_C]
  · intro i
    simp [chart,sectionBase]
private theorem chart_parameter (J:Ideal Ambient) (i:Fin 4) :
    fieldMap J (sliceParameter i)=loc J (place J (MvPolynomial.X i)) := field_base J _
theorem quotient_map (J:Ideal Ambient) : ∃ φ:OverOrdinate J →+* Target J,
    (∀ c:SectionField,φ (algebraMap SectionField (OverOrdinate J) c)=fieldMap J c) ∧
    φ (Ideal.Quotient.mk _ (MvPolynomial.X 1))=loc J (ambient J (MvPolynomial.X 1)) := by
  classical
  let I:=J.map sectionBase ⊔ Ideal.span {sectionSeedLine, (MvPolynomial.X 2-MvPolynomial.C (sliceParameter 3))}
  have hI : I≤RingHom.ker (chart J) := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro q hq
      change chart J (sectionBase q)=0
      rw [←RingHom.comp_apply,chart_base,RingHom.comp_apply]
      simp [ambient,Ideal.Quotient.eq_zero_iff_mem.mpr hq]
    · apply Ideal.span_le.mpr
      intro p hp
      rcases hp with h|h
      · subst p
        change chart J sectionSeedLine=0
        unfold sectionSeedLine
        rw [map_sub,map_add,map_mul,chart_X,chart_X,chart_C,chart_C,chart_parameter,chart_parameter,place_X,place_X]
        simp
      · have eq:p=MvPolynomial.X 2-MvPolynomial.C (sliceParameter 3):=h
        subst p
        change chart J (MvPolynomial.X 2-MvPolynomial.C (sliceParameter 3))=0
        rw [map_sub,chart_X,chart_C,chart_parameter,place_X]
        simp
  refine ⟨Ideal.Quotient.lift I (chart J) hI,?_,?_⟩
  · intro c
    change chart J (MvPolynomial.C c)=_
    simp [chart]
  · change chart J (MvPolynomial.X 1)=_
    simp [chart]

#print axioms quotient_map

/-- Clearing the annihilator and the localization kernel costs no degree
in the moving seed. Both clearing factors are constants in that variable. -/
theorem annihilator (J:Ideal Ambient) (active:Active J) :
    ∃ p:B[X],p≠0 ∧ p.natDegree≤sectionDegree J 1 ∧ send J (back p)=0 := by
  classical
  letI : Module.Finite SectionField (OverOrdinate J):=active.ordinate_finite
  let y : OverOrdinate J:=Ideal.Quotient.mk _ (MvPolynomial.X 1)
  let m:=minpoly SectionField y
  have mn:m≠0:=minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R:=SectionField) y)
  have md:m.natDegree≤sectionDegree J 1:=minpoly.natDegree_le _
  let d:=IsLocalization.integerNormalization (nonZeroDivisors B) m
  obtain ⟨a,ha,scaled⟩:=IsLocalization.integerNormalization_spec (nonZeroDivisors B) m
  have integral:d.map (algebraMap B SectionField)=C (algebraMap B SectionField a)*m := by
    simpa only [Algebra.smul_def,Polynomial.algebraMap_apply] using scaled
  have dn:d≠0:=(IsFractionRing.integerNormalization_eq_zero_iff (A:=B) (p:=m)).not.mpr mn
  have an:algebraMap B SectionField a≠0:=(map_ne_zero_iff _ (IsFractionRing.injective B SectionField)).mpr (nonZeroDivisors.ne_zero ha)
  have degree:d.natDegree=m.natDegree:=by
    rw [←natDegree_map_eq_of_injective (IsFractionRing.injective B SectionField) d,integral,natDegree_C_mul an]
  obtain ⟨φ,hc,hy⟩:=quotient_map J
  have sy : send J (MvPolynomial.C (z 1))=ambient J (MvPolynomial.X 1) := by
    simp [send,z,ambient,K1_14_2.toJet,K1_14_2.toRoot,K1_14_2.rootIncl,K1_14_2.rootSeeds]
  have comm : (loc J).comp ((send J).comp back) =
      (φ.comp (aeval y).toRingHom).comp (mapRingHom (algebraMap B SectionField)) := by
    apply Polynomial.ringHom_ext'
    · apply RingHom.ext
      intro b
      change loc J (send J (back (C b)))=φ (aeval y ((C b).map (algebraMap B SectionField)))
      rw [Polynomial.map_C,aeval_C,hc,field_base]
      simp [place,back]
    · simp only [RingHom.comp_apply,coe_mapRingHom,Polynomial.map_X,AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe,aeval_X]
      calc
        _ = loc J (send J (MvPolynomial.C (z 1))) := by simp [back]
        _ = loc J (ambient J (MvPolynomial.X 1)) := congrArg _ sy
        _ = φ y := hy.symm
  have clear : loc J (send J (back d))=0 := by
    change ((loc J).comp ((send J).comp back)) d=0
    rw [comm]
    change φ (aeval y (d.map (algebraMap B SectionField)))=0
    rw [integral,map_mul,show aeval y m=0 from minpoly.aeval ..,mul_zero,map_zero]
  obtain ⟨s,hs⟩ := (IsLocalization.map_eq_zero_iff (denom J) (Target J) _).mp clear
  obtain ⟨c,hc,he⟩:=s.property
  have cn:c≠0:=nonZeroDivisors.ne_zero hc
  refine ⟨C c*d,mul_ne_zero (C_ne_zero.mpr cn) dn,?_,?_⟩
  · rwa [natDegree_C_mul cn,degree]
  · have hs' : (s:Source J)*send J (back d)=0 := hs
    have ef : (s:Source J)=send J (backBase c) := he.symm
    rw [ef] at hs'
    rw [map_mul,map_mul]
    simpa only [back,coe_eval₂RingHom,eval₂_C] using hs'

#print axioms annihilator

theorem common_relation {parents:Finset K1_14_3.Surface} {H:Equation}
    (proj:K1_14_3.ProjectedProduct parents H) (sources:Finset (Ideal Ambient))
    (active:∀ J∈sources,Active J) (origins:∀ q∈parents,∃ J∈sources,q.asIdeal=J.comap toJet) :
    ∃ D:B[X], D≠0 ∧ D.natDegree≤K1_14_2_2.mass sources 1 ∧ MvPolynomial.C H∣back D := by
  classical
  choose p pn pd vanish using fun J : sources => annihilator J.val (active J.val J.property)
  let D:B[X]:=∏ J:sources,p J
  have dn:D≠0:=Finset.prod_ne_zero_iff.mpr (fun J _=>pn J)
  refine ⟨D,dn,?_,?_⟩
  · calc
      _ = ∑ J:sources,(p J).natDegree := Polynomial.natDegree_prod _ _ (fun J _=>pn J)
      _ ≤ ∑ J:sources,sectionDegree J.val 1 := Finset.sum_le_sum fun J _=>pd J
      _ = _ := by
        simp [K1_14_2_2.mass]
        exact Finset.sum_attach sources (fun J=>sectionDegree J 1)
  · apply (MvPolynomial.C_dvd_iff_dvd_coeff ..).mpr
    intro m
    apply NativeOrdinateMass.divides_of_member proj
    intro q hq
    obtain ⟨J,hJ,eq⟩:=origins q hq
    have zero : send J (back D)=0 := by
      simp only [D,map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨J,hJ⟩:sources)) (vanish ⟨J,hJ⟩)
    rw [eq]
    change toJet (C ((back D).coeff m))∈J
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have zc:=congrArg (fun f:Source J=>f.coeff m) zero
    simpa only [send,MvPolynomial.coeff_map,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,RingHom.comp_apply] using zc

#print axioms common_relation
end
end Research6966.NativeSeedSlice

end Merged_R6966ProofNativeSeedSlice
