import ProximityPrize.SubmissionLower.R6966ProofPadeFiltered
import ProximityPrize.SubmissionLower.R6966ProofRawPhysicalDegree

set_option Elab.async false

namespace Research6966.PadeRawField
open Polynomial Finset Module
open K1_14 (L FX Seeds)
open K1_14_1 (SeedPoly Source RawSource centerEval jetConstant genericCoefficients)
open K1_14_1_4 (doubleMap centerBase evalRaw)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false

/-- Centering sends X to a transcendental and keeps the two seed
indeterminates. A vanishing image kills each physical coefficient. -/
theorem center_injective : Function.Injective centerBase := by
  apply (injective_iff_map_eq_zero centerBase).mpr
  intro g zero
  have z:centerEval (jetConstant g)=0 := by
    rw [K1_14_1_4.centerEval_apply]
    simp only [jetConstant,doubleMap,coe_mapRingHom,Polynomial.map_C,RingHom.comp_apply,zero,Polynomial.C_0]
  apply Polynomial.ext
  intro n
  apply MvPolynomial.ext
  intro e
  have co:=K1_14_1_8.coords_center (jetConstant g) (0,0,e)
  rw [z,map_zero] at co
  change 0=algebraMap L[X] FX (K1_14_1_8.sourceCoord (jetConstant g) (0,0,e)) at co
  have pzero : K1_14_1_8.sourceCoord (jetConstant g) (0,0,e)=0 :=
    (IsFractionRing.injective L[X] FX) (co.symm.trans (map_zero _).symm)
  have ns : ((((jetConstant g).coeff 0).coeff 0).coeff n).coeff e=0 :=
    (congrArg (fun q:L[X]=>q.coeff n) pzero).trans (coeff_zero n)
  change (g.coeff n).coeff e=0
  simpa only [jetConstant,RingHom.comp_apply,coeff_C_zero] using ns

/-- Injectivity on k(Z)[X] after moving X into the physical fraction field.
One common polynomial in the seeds reduces the assertion to the integral
source, for which all native coefficient positions remain visible. -/
theorem eval_injective : Function.Injective evalRaw := by
  apply (injective_iff_map_eq_zero evalRaw).mpr
  intro P zero
  let D:=IsLocalization.integerNormalization (nonZeroDivisors SeedPoly) P
  obtain ⟨b,hb,scaled⟩:=IsLocalization.integerNormalization_spec (nonZeroDivisors SeedPoly) P
  have eq:genericCoefficients D = C (algebraMap SeedPoly K1_14_1.SeedField b)*P := by
    change D.map (algebraMap SeedPoly K1_14_1.SeedField) = _
    simpa only [Algebra.smul_def,Polynomial.algebraMap_apply] using scaled
  have vanish:=RingHom.congr_fun K1_14_1_4.evalRaw_generic D
  change evalRaw (genericCoefficients D)=algebraMap Seeds (FractionRing Seeds) (centerBase D) at vanish
  rw [eq,map_mul,zero,mul_zero] at vanish
  have cent:centerBase D=0 := (IsFractionRing.injective Seeds (FractionRing Seeds))
    (vanish.symm.trans (map_zero _).symm)
  have dz:D=0 := center_injective (cent.trans (map_zero _).symm)
  exact (IsFractionRing.integerNormalization_eq_zero_iff (A:=SeedPoly) (p:=P)).mp dz

private abbrev k := K1_14_1.SeedField
private abbrev E := K1_14_3.SeedClosure

/-- Descend divisibility from any field extension through two polynomial
coordinates. Primitivity here is in the slope, over the full coefficient
UFD k[X,Y], so the quotient is integral also in physical X. -/
theorem primitive_divides {R F:Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    [Field F] (f:R→+*F) (inj:Function.Injective f) {G Q:R[X]} (primitive:G.IsPrimitive)
    (dv:G.map f ∣ Q.map f) : G∣Q := by
  let Rf:=FractionRing R
  let emb:Rf→+*F:=IsFractionRing.lift inj
  have factor:emb.comp (algebraMap R Rf)=f:=by ext x;simp [emb]
  apply primitive.dvd_of_fraction_map_dvd_fraction_map (K:=Rf)
  apply (Polynomial.map_dvd_map' emb).mp
  simpa only [Polynomial.map_map,factor] using dv

def rawField : k[X]→+*E := (algebraMap K1_14_3.SeedField E).comp evalRaw

theorem integral_power {R K:Type*} [CommRing R] [IsDomain R] [Field K] [UniqueFactorizationMonoid R[X]]
    (g:R→+*K) (inject:Function.Injective g) {G Q:R[X][X]} (gp:G.IsPrimitive) (t:ℕ)
    (dv:doubleMap g G^t ∣ doubleMap g Q) : G^t ∣ Q := by
  let F:=FractionRing K[X]
  let f:R[X]→+*F:=(algebraMap K[X] F).comp (mapRingHom g)
  have inj:Function.Injective f:=(IsFractionRing.injective K[X] F).comp (map_injective g inject)
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α:=R[X])
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid R[X]
  have prim:(G^t).IsPrimitive:=by
    clear dv
    induction t with
    | zero=>simp
    | succ t ih=>rw [pow_succ];exact ih.mul gp
  apply primitive_divides f inj prim
  obtain ⟨S,eq⟩:=dv
  refine ⟨S.map (algebraMap K[X] F),?_⟩
  have eq':=congrArg (fun p:K[X][X]=>p.map (algebraMap K[X] F)) eq
  simpa only [doubleMap,coe_mapRingHom,Polynomial.map_map,Polynomial.map_mul,Polynomial.map_pow] using eq'

theorem raw_divides {G Q:RawSource} (gp:G.IsPrimitive) (t:ℕ)
    (dv:doubleMap rawField G^t ∣ doubleMap rawField Q) : G^t ∣ Q :=
  integral_power rawField ((algebraMap K1_14_3.SeedField E).injective.comp eval_injective) gp t dv

/-- The normalized raw source pays t physical graph weights as soon as the
field-valued graph power is forced. The quotient is produced integrally. -/
theorem quotient_of_fibre_power {h:ℕ} (hp:0<h) (hl:h≤131070) {D:K1_14_1.PoleData h}
    (Crt:K1_14_1.CRTLift D) (word:K1.I→L) {s W P} (mem:P∈K1_14_1.complete Crt word s W)
    {G:RawSource} (gp:G.IsPrimitive) (t:ℕ)
    (dv:doubleMap rawField G^t ∣ doubleMap (algebraMap K1_14_3.SeedField E)
      (K1_14_1_4.specialized Crt (centerEval P))) :
    ∃ Q:RawSource, K1_14_1.forward Crt P=jetConstant ((K1_14_1.rawBlock D)^(s.B+s.J))*(G^t*Q) ∧
      K1_14_1_4.Bounded (131071-h) (131071-h-1) (W-t*RawPhysicalDegree.weight (131071-h) (131071-h-1) G) Q := by
  obtain ⟨S,eq,_⟩:=P0_10_1.complete_raw_bounded hp hl Crt word mem
  have compose (P:RawSource):doubleMap (algebraMap K1_14_3.SeedField E) (doubleMap evalRaw P)=
    doubleMap rawField P := by
      ext j i
      simp only [doubleMap,coe_mapRingHom,Polynomial.coeff_map,rawField,RingHom.comp_apply]
  rw [K1_14_1_4.specialized_center,compose,eq,map_mul] at dv
  let c:=rawField ((K1_14_1.rawBlock D)^(s.B+s.J))
  have nz:c≠0:=(map_ne_zero_iff rawField ((algebraMap K1_14_3.SeedField E).injective.comp eval_injective)).mpr
    (pow_ne_zero _ (K1_14_1_4.rawBlock_monic D).ne_zero)
  have unitC:IsUnit (jetConstant c : E[X][X]) := isUnit_C.mpr (isUnit_C.mpr nz.isUnit)
  have tr:doubleMap rawField (jetConstant ((K1_14_1.rawBlock D)^(s.B+s.J)))=jetConstant c := by
    simp only [jetConstant,doubleMap,RingHom.comp_apply,coe_mapRingHom,Polynomial.map_C];rfl
  rw [tr] at dv
  have divides:=raw_divides gp t ((associated_unit_mul_left _ _ unitC).dvd_iff_dvd_right.mp dv)
  obtain ⟨Q,id⟩:=divides
  exact ⟨Q,eq.trans (congrArg (_ * ·) id),RawPhysicalDegree.complete_graph_quotient hp hl Crt word mem G Q t
    gp.ne_zero (eq.trans (congrArg (_ * ·) id))⟩

end
end Research6966.PadeRawField
