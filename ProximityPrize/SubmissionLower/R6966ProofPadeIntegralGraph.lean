import ProximityPrize.SubmissionLower.R6966ProofPadeRawField

set_option Elab.async false

namespace Research6966.PadeIntegralGraph
open Polynomial Finset Module
open K1_14 (L FX Seeds)
open K1_14_1 (jetConstant)
open K1_14_1_4 (doubleMap evalRaw)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 16

private abbrev k:=K1_14_1.SeedField
private abbrev B:=K1_14_3.SeedField

def joint : FractionRing k[X] →+* B := IsFractionRing.lift PadeRawField.eval_injective

theorem joint_raw (x:k[X]) : joint (algebraMap k[X] (FractionRing k[X]) x)=evalRaw x :=
  IsFractionRing.lift_algebraMap PadeRawField.eval_injective x

private theorem restrict_joint : joint.comp (algebraMap k[X] (FractionRing k[X]))=evalRaw :=
  RingHom.ext joint_raw

/-- Both orders of adjoining the physical coordinate and the seeds give
the same rational function field, including in positive characteristic. -/
theorem joint_surjective : Function.Surjective joint := by
  let S:=joint.fieldRange
  have raw (p:k[X]) : evalRaw p∈S :=
    ⟨algebraMap k[X] (FractionRing k[X]) p,IsFractionRing.lift_algebraMap PadeRawField.eval_injective p⟩
  have physical (p:L[X]) : algebraMap FX B (algebraMap L[X] FX p)∈S :=
    RingHom.congr_fun K1_14_1_4.evalRaw_physical p ▸ raw (p.map (algebraMap L k))
  have scalar (p:FX) : algebraMap FX B p∈S := by
    obtain ⟨n,d,_,rfl⟩:=IsFractionRing.div_surjective L[X] p
    rw [map_div₀]
    exact S.div_mem (physical n) (physical d)
  have seed (p:Seeds) : algebraMap Seeds B p∈S := by
    induction p using MvPolynomial.induction_on with
    | C x =>
      change algebraMap Seeds B (algebraMap FX Seeds x)∈S
      rw [←IsScalarTower.algebraMap_apply]
      exact scalar x
    | add p q hp hq=>rw [map_add];exact S.add_mem hp hq
    | mul_X p i hp=>
      rw [map_mul]
      exact S.mul_mem hp (K1_14_1_4.evalRaw_seed i ▸ raw _)
  intro z
  obtain ⟨p,q,_,rfl⟩:=IsFractionRing.div_surjective Seeds z
  exact S.div_mem (seed p) (seed q)

private def jointEquiv : FractionRing k[X] ≃+* B :=
  RingEquiv.ofBijective joint ⟨joint.injective,joint_surjective⟩

private theorem double_comp {R A F:Type*} [CommSemiring R] [CommSemiring A] [CommSemiring F]
    (g:A→+*F) (f:R→+*A) (P:R[X][X]) :
    doubleMap g (doubleMap f P)=doubleMap (g.comp f) P := by
  ext j i;simp only [doubleMap,coe_mapRingHom,coeff_map,RingHom.comp_apply]

private theorem double_jet {R A:Type*} [CommSemiring R] [CommSemiring A] (f:R→+*A) (c:R) :
    doubleMap f (jetConstant c)=jetConstant (f c) := by
  simp only [doubleMap,jetConstant,coe_mapRingHom,RingHom.comp_apply,Polynomial.map_C]

theorem clear_two {R:Type*} [CommRing R] [IsDomain R] (P:(FractionRing R)[X][X]) :
    ∃ (D:R[X][X]) (d:R),d≠0 ∧ doubleMap (algebraMap R (FractionRing R)) D =
      jetConstant (algebraMap R (FractionRing R) d)*P := by
  classical
  let f:=algebraMap R (FractionRing R)
  induction P using Polynomial.induction_on' with
  | add P Q hp hq =>
    obtain ⟨A,a,anz,first⟩:=hp
    obtain ⟨B,b,bnz,second⟩:=hq
    exact ⟨jetConstant b*A+jetConstant a*B,a*b,mul_ne_zero anz bnz,by
      rw [map_add,map_mul,map_mul,double_jet,double_jet,first,second,map_mul,map_mul]
      ring⟩
  | monomial n q =>
    let N:=IsLocalization.integerNormalization (nonZeroDivisors R) q
    obtain ⟨d,hd,eq⟩:=IsLocalization.integerNormalization_spec (nonZeroDivisors R) q
    have cq:N.map f=C (f d)*q := by simpa only [Algebra.smul_def,Polynomial.algebraMap_apply] using eq
    refine ⟨monomial n N,d,nonZeroDivisors.ne_zero hd,?_⟩
    change (monomial n N).map (mapRingHom f)=C (C (f d))*monomial n q
    rw [map_monomial,coe_mapRingHom,cq,C_mul_monomial]

private theorem primitive_part {R F:Type*} [CommRing R] [IsDomain R] [Field F]
    [UniqueFactorizationMonoid R[X]] (f:R→+*F) (inj:Function.Injective f)
    (P:F[X][X]) (prim:P.IsPrimitive) (D:R[X][X]) (d:R) (nd:d≠0)
    (mapped:doubleMap f D=jetConstant (f d)*P) :
    ∃ (G:R[X][X]) (c:F),G.IsPrimitive ∧ c≠0 ∧ doubleMap f G=jetConstant c*P := by
  classical
  have dn:f d≠0 := (map_ne_zero_iff _ inj).mpr nd
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α:=R[X])
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid R[X]
  have content : C (D.content.map f)*doubleMap f D.primPart=jetConstant (f d)*P := by
    calc
      _ = doubleMap f (C D.content*D.primPart) := by
        simp only [map_mul,doubleMap,coe_mapRingHom,Polynomial.map_C]
      _ = _ := D.eq_C_content_mul_primPart ▸ mapped
  have unitScalar:IsUnit (jetConstant (f d):F[X][X]) :=
    isUnit_C.mpr (isUnit_C.mpr dn.isUnit)
  have cd:C (D.content.map f)∣P :=
    (associated_unit_mul_left _ _ unitScalar).dvd_iff_dvd_right.mp ⟨_,content.symm⟩
  obtain ⟨a,ua,coeff⟩:=Polynomial.isUnit_iff.mp (prim _ cd)
  rw [←coeff] at content
  refine ⟨D.primPart,f d/a,D.isPrimitive_primPart,div_ne_zero dn ua.ne_zero,?_⟩
  apply mul_left_cancel₀ (C_ne_zero.mpr (C_ne_zero.mpr ua.ne_zero) : (jetConstant a:F[X][X])≠0)
  change C (C a)*doubleMap f D.primPart = jetConstant a*(jetConstant (f d/a)*P)
  rw [content,←mul_assoc,←map_mul]
  congr 2
  field_simp [ua.ne_zero]

/-- Clear every coefficient into the raw polynomial ring with one scalar
and then divide out all common content in the ordinate and physical variables. -/
theorem raw_model (P:B[X][X]) (prim:P.IsPrimitive) :
    ∃ (G:K1_14_1.RawSource) (c:B),G.IsPrimitive ∧ c≠0 ∧ doubleMap evalRaw G=jetConstant c*P := by
  classical
  let H:=doubleMap jointEquiv.symm.toRingHom P
  obtain ⟨D,d,nd,eq⟩:=clear_two (R:=k[X]) H
  have back:doubleMap joint H=P := by
    ext j i
    simp only [H,doubleMap,coe_mapRingHom,coeff_map]
    exact jointEquiv.apply_symm_apply _
  have mapped:doubleMap evalRaw D=jetConstant (evalRaw d)*P := by
    have test:=congrArg (doubleMap joint) eq
    rw [double_comp,map_mul,double_jet,back] at test
    rwa [restrict_joint,joint_raw] at test
  exact primitive_part evalRaw PadeRawField.eval_injective P prim D d nd mapped

/-- A primitive representative with polynomial seed coefficients in the
native bank. Its two seed degrees are shared by all rows and cutoffs. -/
theorem native_model (P:B[X][X]) (prim:P.IsPrimitive) :
    ∃ (G:K1_14.Jet) (c:B),G.IsPrimitive ∧ c≠0 ∧
      doubleMap (algebraMap Seeds B) G=jetConstant c*P := by
  obtain ⟨D,d,nd,eq⟩:=clear_two (R:=Seeds) P
  exact primitive_part (algebraMap Seeds B) (IsFractionRing.injective Seeds B) P prim D d nd eq


end
end Research6966.PadeIntegralGraph
