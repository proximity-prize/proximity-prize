import ProximityPrize.SubmissionLower.R6966ProofNativeGraphExceptional
import ProximityPrize.SubmissionLower.R6966ProofPadeRawField
import ProximityPrize.SubmissionLower.KoalaRectCutoff

set_option Elab.async false

-- merged module R6966ProofNativeProjectedWitness
section Merged_R6966ProofNativeProjectedWitness

set_option Elab.async false

namespace Research6966.NativeProjectedWitness
open Polynomial Finset
open K1_14 (Jet Equation Seeds)
open K1_14_3 (SeedField SeedClosure Surface Parent OrderAt ProjectedProduct OnSeedFibre fibreRow)
open K1_14_1_4 (doubleMap)
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open TerminalProjection (cleared)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16

private abbrev E:=SeedClosure
private abbrev φ:=K1_14_3.seedGeneric
private theorem inj:Function.Injective φ:=(algebraMap SeedField E).injective.comp (IsFractionRing.injective Seeds SeedField)

theorem graph_eq {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) :
    C (den N)*Polynomial.X-C (rhs N)=N.poly := by
  simpa only [den,rhs,map_neg,sub_neg_eq_add] using
    (Polynomial.eq_X_add_C_of_natDegree_le_one (NativeGraphMarks.slope_degree N gp).le).symm

private theorem map_clear (A B:Equation) (Q:Jet) (J:ℕ) (cap:Q.natDegree≤J) :
    (cleared A B Q J).map φ=cleared (A.map φ) (B.map φ) (fibreRow Q) J := by
  have top:(fibreRow Q).natDegree≤J:=by
    change (Q.map (mapRingHom φ)).natDegree≤J;exact natDegree_map_le.trans cap
  rw [cleared,cleared,Q.sum_over_range' (fun _=>by simp) (J+1) (by omega),
    (fibreRow Q).sum_over_range' (fun _=>by simp) (J+1) (by omega),Polynomial.map_sum]
  apply sum_congr rfl
  intro j _
  simp only [Polynomial.map_mul,Polynomial.map_pow,fibreRow,coeff_map,coe_mapRingHom]

/-- Fix the actual projected product once. Every avoiding row, including
one from a differently shaped bank, bounds this same native equation. -/
theorem projected_factor {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive)
    (parents:Finset Surface) (nonempty:parents.Nonempty) (geo:∀ q∈parents,Parent q)
    (onGraph:∀ q∈parents,N.poly∈q.asIdeal) :
    ∃ H:Equation,ProjectedProduct parents H ∧ ∀ (Q:Jet) (J k:ℕ),Q.natDegree≤J →
      (∀ q∈parents,OrderAt q Q k) → H^k ∣ cleared (den N) (rhs N) Q J := by
  obtain ⟨H,T,v,proj,card,sheets⟩:=Pade.Native.projected_sheets parents nonempty geo
  let emb:Pade.Native.Sep→+*E:=(separableClosure SeedField E).val.toRingHom
  let ys:=T.image emb
  let vel (y:E):=if eq:∃ x∈T,emb x=y then emb (v eq.choose) else 0
  have velocity x (mem:x∈T):vel (emb x)=emb (v x) := by
    have yes:∃ z∈T,emb z=emb x:=⟨x,mem,rfl⟩
    simp only [vel,dite_eq_left yes,emb.injective yes.choose_spec.2]
  have root (y:E) (hy:y∈ys):∃ q∈parents,OnSeedFibre q y (vel y) := by
    obtain ⟨x,hx,rfl⟩:=mem_image.mp hy
    rw [velocity x hx]
    exact (Pade.Native.sheets_iff ..).mp (sheets x hx)
  let D:E[X]:=∏y∈ys,(Polynomial.X-C y)
  have cardD:D.natDegree=H.natDegree := by
    dsimp only [D]
    rw [natDegree_prod ys (fun y=>Polynomial.X-C y) (fun y _=>X_sub_C_ne_zero y)]
    simpa only [natDegree_X_sub_C,sum_const,smul_eq_mul,mul_one,ys,card_image_of_injective _ emb.injective] using card
  have hn:H.map φ≠0:=(map_ne_zero_iff (mapRingHom φ) (map_injective φ inj)).mpr proj.primitive.ne_zero
  have divides:D∣H.map φ := by
    apply prod_dvd_of_coprime
    · intro x hx y hy ne;exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ne).isUnit
    · intro y hy
      obtain ⟨q,mem,onq⟩:=root y hy
      have zero:=proj.vanishes q mem
      rw [←onq,RingHom.mem_ker] at zero
      apply dvd_iff_isRoot.mpr
      change (H.map φ).eval y=0
      rw [eval_map]
      simpa only [K1_14_3.seedFibreEval,coe_eval₂RingHom,eval₂_C] using zero
  obtain ⟨a,eq⟩:=divides
  have da:D≠0:=left_ne_zero_of_mul (eq ▸ hn)
  have an:a≠0:=right_ne_zero_of_mul (eq ▸ hn)
  have total: (H.map φ).natDegree = D.natDegree+a.natDegree := by rw [eq,natDegree_mul da an]
  rw [natDegree_map_eq_of_injective inj,cardD] at total
  have const:a=C (a.coeff 0):=eq_C_of_natDegree_eq_zero (by omega)
  have cn:a.coeff 0≠0:=by intro z;apply an;rw [const,z,map_zero]
  have unit:IsUnit a:=const ▸ isUnit_C.mpr cn.isUnit
  have assoc:Associated (H.map φ) D:=eq ▸ associated_mul_unit_left _ _ unit
  refine ⟨H,proj,?_⟩
  intro Q J k cap order
  have projQ:=TerminalProjection.all_sheets ((den N).map φ) ((rhs N).map φ) (fibreRow Q) ys vel J k
    (natDegree_map_le.trans cap) (by
      intro y hy
      obtain ⟨q,mem,onq⟩:=root y hy
      have zero:=onGraph q mem
      rw [←onq,RingHom.mem_ker] at zero
      rw [←graph_eq N gp] at zero
      have hit:((den N).map φ).eval y*vel y=((rhs N).map φ).eval y := by
        simp only [K1_14_3.seedFibreEval,coe_eval₂RingHom,eval₂_sub,eval₂_mul,eval₂_C,eval₂_X] at zero
        simpa only [eval_map] using sub_eq_zero.mp zero
      have nz:((den N).map φ).eval y≠0:=by
        intro z
        obtain ⟨l,w,id⟩:=NativeGraphExceptional.coprime_generic N gp
        have bad:=congrArg (eval y) id
        simp [←hit,z] at bad
      exact ⟨nz,hit,order q mem y (vel y) onq⟩)
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α:=Seeds)
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid Seeds
  have prim (i:ℕ) : (H^i).IsPrimitive := by
    induction i with
    | zero=>simp
    | succ i ih=>rw [pow_succ];exact ih.mul proj.primitive
  apply PadeRawField.primitive_divides φ inj (prim k)
  rw [Polynomial.map_pow,map_clear _ _ _ _ cap]
  exact (pow_dvd_pow_of_dvd assoc.dvd k).trans projQ

theorem axis_clear {G:Pade.Row SeedField} (N:Native G) (Q:Jet) (z:Fin 2) (J U u:ℕ)
    (cap:Q.natDegree≤J) (Qaxis:∀ j i,((Q.coeff j).coeff i).degreeOf z≤U)
    (Naxis:∀ j i,((N.poly.coeff j).coeff i).degreeOf z≤u) :
    KoalaRect.axisDegree (cleared (den N) (rhs N) Q J) z ≤ U+J*u := by
  let view:=K1_14_4.seedView
  have a:KoalaRect.axisDegree (den N) z≤u:=(KoalaRect.axisDegree_le_iff ..).mpr (Naxis 1)
  have b:KoalaRect.axisDegree (rhs N) z≤u:=(KoalaRect.axisDegree_le_iff ..).mpr (fun i=>by simpa [rhs] using Naxis 0 i)
  change (view (cleared (den N) (rhs N) Q J)).degreeOf z≤_
  rw [cleared,Polynomial.sum_def,map_sum]
  apply (MvPolynomial.degreeOf_sum_le ..).trans (Finset.sup_le _)
  intro j hj
  have jJ: j≤J:=(le_natDegree_of_mem_supp j hj).trans cap
  have q:KoalaRect.axisDegree (Q.coeff j) z≤U:=(KoalaRect.axisDegree_le_iff ..).mpr (Qaxis j)
  rw [map_mul,map_mul,map_pow,map_pow]
  calc
    _ ≤ (U+j*u)+(J-j)*u := (MvPolynomial.degreeOf_mul_le ..).trans (Nat.add_le_add
      ((MvPolynomial.degreeOf_mul_le ..).trans (Nat.add_le_add q
        ((MvPolynomial.degreeOf_pow_le ..).trans (Nat.mul_le_mul_left j b))))
      ((MvPolynomial.degreeOf_pow_le ..).trans (Nat.mul_le_mul_left (J-j) a)))
    _ = _ := by rw [Nat.add_assoc,←Nat.add_mul,Nat.add_sub_of_le jJ]

theorem avoiding_widths {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive)
    {H:Equation} (hn:H≠0) (Q:Jet) (k J B:ℕ) (U u:Fin 2→ℕ)
    (notDiv:¬N.poly∣Q) (cap:Q.natDegree≤J) (joint:∀ j∈Q.support,(Q.coeff j).natDegree+j≤B)
    (Qa:∀ j i z,((Q.coeff j).coeff i).degreeOf z≤U z)
    (Na:∀ j i z,((N.poly.coeff j).coeff i).degreeOf z≤u z)
    (divides:H^k∣cleared (den N) (rhs N) Q J) :
    k*H.natDegree≤B+(G.graphDegree-1)*J ∧ ∀ z,k*KoalaRect.axisDegree H z≤U z+J*u z := by
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α:=Equation)
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid Equation
  have eq:=graph_eq N gp
  have nz:=TerminalProjection.integral_nonzero_of_avoids (den N) (rhs N) Q J cap
    (NativeGraphExceptional.den_ne N gp) (eq ▸ N.primitive) (eq ▸ notDiv)
  have deg:=NativeGraphMarks.equation_degrees N gp
  have y:=TerminalProjection.ordinate_width (den N) (rhs N) Q J G.graphDegree B cap
    (by unfold Pade.Row.graphDegree;omega) deg.1 deg.2 joint
  have lower:=natDegree_le_of_dvd divides nz
  rw [natDegree_pow] at lower
  refine ⟨lower.trans y,?_⟩
  intro z
  obtain ⟨D,eq⟩:=divides
  have dn:=right_ne_zero_of_mul (eq ▸ nz)
  have axis:=axis_clear N Q z J (U z) (u z) cap (fun j i=>Qa j i z) (fun j i=>Na j i z)
  rw [eq,KoalaRect.axisDegree_mul (pow_ne_zero _ hn) dn,KoalaRect.axisDegree_pow hn] at axis
  omega

end
end Research6966.NativeProjectedWitness

end Merged_R6966ProofNativeProjectedWitness

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

end
end Research6966.NativeSeedSlice

end Merged_R6966ProofNativeSeedSlice

-- merged module Z6969Pack0096
section Merged_Z6969Pack0096

-- Source: Research6969.JointOwnership
set_option autoImplicit true
namespace Research6969.JointOwnership
noncomputable section
open Polynomial Finset
open K1_14 (Equation Jet Seeds FX)
open K1_14_3 (Surface ProjectedProduct SeedField)
open Research6966.NativeOrdinateMass (divides_of_member)
open scoped Classical

/-- Assign every shared projected factor to the primary product. The
remaining polynomial divides the actual rescue product already over the
integral seed ring, and the two retained degrees sum to the union degree. -/
theorem exclusive {S T:Finset Surface} {p q h:Equation} (left:ProjectedProduct S p)
    (right:ProjectedProduct T q) (whole:ProjectedProduct (S∪T) h) :
    ∃ e:Equation, h=p*e ∧ e∣q ∧ e≠0 ∧ p.natDegree+e.natDegree=h.natDegree ∧
      (e.map (algebraMap Seeds SeedField)).Separable ∧
      ∀ Q∈T, C p∉Q.asIdeal → C e∈Q.asIdeal := by
  have div:p∣h:=divides_of_member left (fun Q hQ=>whole.vanishes Q (mem_union_left _ hQ))
  obtain ⟨e,he⟩:=div
  have product:h∣p*q:=divides_of_member whole (by
    intro Q hQ
    rw [map_mul]
    rcases mem_union.mp hQ with inS|inT
    · exact Q.asIdeal.mul_mem_right _ (left.vanishes Q inS)
    · exact Q.asIdeal.mul_mem_left _ (right.vanishes Q inT))
  have ne:e≠0:=fun zero=>whole.primitive.ne_zero (he.trans (by rw [zero,mul_zero]))
  obtain ⟨k,hk⟩:=product
  rw [he,mul_assoc] at hk
  have remainder:e∣q:=⟨k,mul_left_cancel₀ left.primitive.ne_zero hk⟩
  have sep:=whole.separable
  rw [he,Polynomial.map_mul] at sep
  refine ⟨e,he,remainder,ne,?_,sep.of_mul_right,?_⟩
  · rw [he,natDegree_mul left.primitive.ne_zero ne]
  · intro Q hQ absent
    have hzero:=whole.vanishes Q (mem_union_right _ hQ)
    rw [he,map_mul] at hzero
    exact (Q.isPrime.mem_or_mem hzero).resolve_left absent

/-- Specialization preserves ownership of all marks, even at a point
shared by two projected parents. -/
theorem mark_partition {α:Type*} {S T:Finset Surface} {p h e:Equation}
    (primary:ProjectedProduct S p) (whole:ProjectedProduct (S∪T) h) (factor:h=p*e)
    (z:α→Jet→+*FX) {j:α} (owner:∃Q∈S∪T,∀ f∈Q.asIdeal,z j f=0) :
    z j (C p)=0 ∨ (z j (C e)=0 ∧ ∃Q∈T,∀ f∈Q.asIdeal,z j f=0) := by
  by_cases hit:z j (C p)=0
  · exact Or.inl hit
  obtain ⟨Q,hQ,atQ⟩:=owner
  have zero:=atQ _ (whole.vanishes Q hQ)
  rw [factor,map_mul,map_mul] at zero
  refine Or.inr ⟨(mul_eq_zero.mp zero).resolve_left hit,Q,?_,atQ⟩
  exact (mem_union.mp hQ).resolve_left (fun inS=>hit (atQ _ (primary.vanishes Q inS)))


theorem rescue_caps {T:Finset Surface} {e q:Equation} (rescue:ProjectedProduct T q) (div:e∣q) :
    e.IsPrimitive ∧ K1_14_4.seedDegree e≤K1_14_4.seedDegree q ∧
    ∀ z,KoalaRect.axisDegree e z≤KoalaRect.axisDegree q z := by
  refine ⟨Polynomial.isPrimitive_of_dvd rescue.primitive div,?_⟩
  obtain ⟨k,eq⟩:=div
  have hn:e*k≠0:=eq ▸ rescue.primitive.ne_zero
  have en:e≠0:=left_ne_zero_of_mul hn
  have kn:k≠0:=right_ne_zero_of_mul hn
  constructor
  · rw [eq,K1_14_4.seedDegree_mul en kn]
    omega
  · intro z
    rw [eq,KoalaRect.axisDegree,KoalaRect.axisDegree,map_mul,
      MvPolynomial.degreeOf_mul_eq (by simpa using en) (by simpa using kn)]
    omega

/-- An empty exclusive degree cannot create a mark by specialization. -/
theorem zero_grade_unit {e:Equation} (prim:e.IsPrimitive) (zero:e.natDegree=0) : IsUnit e := by
  have eq:=eq_C_of_natDegree_eq_zero zero
  have u:=Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp prim (e.coeff 0) eq.symm.dvd
  rw [eq]
  exact u.map Polynomial.C

end
end Research6969.JointOwnership

end Merged_Z6969Pack0096
