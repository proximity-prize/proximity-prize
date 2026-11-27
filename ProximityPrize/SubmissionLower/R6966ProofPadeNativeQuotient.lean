import ProximityPrize.SubmissionLower.R6966ProofPadeConcentration

set_option Elab.async false

namespace Research6966.PadeNativeQuotient
open Polynomial Finset Module
open K1_14 (FX Jet Seeds L Shape)
open K1_14_1 (jetConstant PoleData CRTLift centerEval)
open K1_14_1_4 (doubleMap)
open K1_14_3 (SeedField SeedClosure fibreRow OrderAt Parent Surface)
open K1_14_2_2_2_1 (seedVariables coeff_seedVariables seedVariables_injective)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 18
set_option backward.isDefEq.respectTransparency false

private abbrev f:=algebraMap SeedField SeedClosure

def axis (P:Jet) (z:Fin 2) := (seedVariables P).degreeOf z

theorem axis_le (P:Jet) (z:Fin 2) (U:ℕ) :
    axis P z≤U ↔ ∀ j i,((P.coeff j).coeff i).degreeOf z≤U := by
  constructor
  · intro cap j i
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    apply MvPolynomial.degreeOf_le_iff.mp cap e (MvPolynomial.mem_support_iff.mpr ?_)
    intro zero
    let d:Fin 2→₀ℕ:=Finsupp.equivFunOnFinite.symm ![j,i]
    have gone:=congrArg (fun p:MvPolynomial (Fin 2) FX=>p.coeff d) zero
    rw [coeff_seedVariables,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] at gone
    exact (MvPolynomial.mem_support_iff.mp he) gone
  · intro cap
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    obtain ⟨d,hd⟩ : ∃ d,((seedVariables P).coeff e).coeff d≠0 := by
      by_contra! none
      exact (MvPolynomial.mem_support_iff.mp he) (MvPolynomial.ext _ _ (fun d=>by rw [none,AddMonoidAlgebra.coeff_zero];rfl))
    rw [coeff_seedVariables] at hd
    exact MvPolynomial.degreeOf_le_iff.mp (cap (d 0) (d 1)) e (MvPolynomial.mem_support_iff.mpr hd)

theorem axis_mul {A B:Jet} (an:A≠0) (bn:B≠0) (z:Fin 2) :
    axis (A*B) z=axis A z+axis B z := by
  unfold axis
  rw [map_mul,MvPolynomial.degreeOf_mul_eq ((map_ne_zero_iff _ seedVariables_injective).mpr an)
    ((map_ne_zero_iff _ seedVariables_injective).mpr bn)]

theorem axis_pow {A:Jet} (an:A≠0) (z:Fin 2) (t:ℕ) : axis (A^t) z=t*axis A z := by
  induction t with
  | zero=>simp [axis]
  | succ t ih=>rw [pow_succ,axis_mul (pow_ne_zero _ an) an,ih,Nat.succ_mul]

/-- Primitive native seed polynomial defining the descended graph. -/
structure Native (G:Pade.Row SeedField) where
  poly : Jet
  primitive : poly.IsPrimitive
  scalar : SeedClosure
  nonzero : scalar≠0
  eq : fibreRow poly=jetConstant scalar*(G.map f).polynomial

theorem exists_native {G:Pade.Row SeedField} (gp:G.primitive) : Nonempty (Native G) := by
  obtain ⟨H,c,prim,cn,eq⟩:=PadeIntegralGraph.native_model G.polynomial (G.polynomial_primitive gp)
  refine ⟨⟨H,prim,f c,(map_ne_zero f).mpr cn,?_⟩⟩
  have mapped:=congrArg (doubleMap f) eq
  have back:doubleMap f (doubleMap (algebraMap Seeds SeedField) H)=fibreRow H := by
    ext j i
    simp only [doubleMap,fibreRow,coe_mapRingHom,coeff_map,K1_14_3.seedGeneric,RingHom.comp_apply]
  rw [back,map_mul] at mapped
  simpa only [doubleMap,Pade.Row.polynomial,Pade.Row.map,jetConstant,coe_mapRingHom,
    Polynomial.map_C,Polynomial.map_X,map_mul,map_sub,RingHom.comp_apply] using mapped

theorem Native.divides {G:Pade.Row SeedField} (N:Native G) {P:Jet} {t:ℕ}
    (fieldPower:(G.map f).polynomial^t ∣ fibreRow P) : N.poly^t∣P := by
  have unit:IsUnit (jetConstant N.scalar:SeedClosure[X][X]) := isUnit_C.mpr (isUnit_C.mpr N.nonzero.isUnit)
  apply PadeRawField.integral_power K1_14_3.seedGeneric
    (f.injective.comp (IsFractionRing.injective Seeds SeedField)) N.primitive t
  change fibreRow N.poly^t ∣ fibreRow P
  rw [N.eq,mul_pow]
  exact (associated_unit_mul_left _ _ (unit.pow t)).dvd.trans fieldPower

theorem Native.remaining_axis {G:Pade.Row SeedField} (N:Native G) {P Q:Jet} (qn:Q≠0) (t:ℕ)
    (eq:P=N.poly^t*Q) (U:Fin 2→ℕ) (bound:∀ j i z,((P.coeff j).coeff i).degreeOf z≤U z) :
    ∀ j i z,((Q.coeff j).coeff i).degreeOf z≤U z-t*axis N.poly z := by
  intro j i z
  have cap:axis P z≤U z:=(axis_le ..).mpr (fun j i=>bound j i z)
  rw [eq,axis_mul (pow_ne_zero _ N.primitive.ne_zero) qn,axis_pow N.primitive.ne_zero] at cap
  exact (axis_le ..).mp (by omega : axis Q z≤U z-t*axis N.poly z) j i

private theorem strip_any (G:Pade.Row SeedClosure) (gp:G.primitive) (R:SeedClosure[X][X]) (y v:SeedClosure)
    (k:ℕ) (h:G.polynomial*R∈(K1_14_3.fibrePoint y v)^(k+1)) : R∈(K1_14_3.fibrePoint y v)^k := by
  by_cases onG:G.a.eval y*v=G.b.eval y
  · have regular:G.a.eval y≠0 := by
      intro nz
      obtain ⟨l,w,bez⟩:=gp.2
      have bad:=congrArg (eval y) bez
      simp [←onG,nz] at bad
    exact PadeJetOrder.strip G.a G.b R y v k regular onG h
  · exact Ideal.pow_le_pow_right (by omega : k≤k+1) (PadeJetOrder.strip_off G.a G.b R y v (k+1) onG h)

theorem Native.remaining_order {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive)
    {P Q:Jet} {q:Surface} (t k:ℕ) (eq:P=N.poly^t*Q) (ord:OrderAt q P k) : OrderAt q Q (k-t) := by
  intro y v fiber
  have whole:=ord y v fiber
  have mapped:fibreRow P=(jetConstant N.scalar)^t*((G.map f).polynomial^t*fibreRow Q) := by
    change doubleMap K1_14_3.seedGeneric P=_
    rw [eq,map_mul,map_pow]
    change (fibreRow N.poly)^t*fibreRow Q=_
    rw [N.eq,mul_pow,mul_assoc]
  rw [mapped] at whole
  have unit:IsUnit (jetConstant N.scalar:SeedClosure[X][X]) := isUnit_C.mpr (isUnit_C.mpr N.nonzero.isUnit)
  have bare:(G.map f).polynomial^t*fibreRow Q∈(K1_14_3.fibrePoint y v)^k := by
    obtain ⟨w,ew⟩:=unit.pow t
    rw [←ew] at whole
    have m:=((K1_14_3.fibrePoint y v)^k).mul_mem_left (↑w⁻¹) whole
    simpa only [←mul_assoc,Units.inv_mul,one_mul] using m
  clear whole mapped eq ord
  induction t generalizing k with
  | zero=>simpa using bare
  | succ t ih=>
    cases k with
    | zero=>simp
    | succ k=>
      rw [pow_succ' (G.map f).polynomial t,mul_assoc] at bare
      have next:=strip_any _ ((G.primitive_map f).mpr gp) _ y v k bare
      simpa only [Nat.add_sub_add_right] using ih k next

end
end Research6966.PadeNativeQuotient
