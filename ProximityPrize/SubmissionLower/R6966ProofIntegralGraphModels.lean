import ProximityPrize.SubmissionLower.R6966ProofRegularPhysicalChart
import ProximityPrize.SubmissionLower.R6966ProofNativeWitnessBank

set_option Elab.async false

namespace Research6966.IntegralGraphModels
open Polynomial Finset
open K1_14 (Jet Seeds)
open K1_14_1 (PoleData CRTLift Source RawSource jetConstant)
open K1_14_1_4 (doubleMap evalRaw specialized)
open PhysicalPrimitiveCoeffs (R rawCoeff)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 750000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

private theorem deg_associated {S:Type*} [CommRing S] [IsDomain S] {A B:S[X]}
    (ab:Associated A B) (bn:B≠0) : A.natDegree=B.natDegree :=
  le_antisymm (natDegree_le_of_dvd ab.dvd bn) (natDegree_le_of_dvd ab.dvd' (ab.ne_zero_iff.mpr bn))

private theorem linear_prime {S:Type*} [CommRing S] [IsDomain S] [UniqueFactorizationMonoid S]
    {A:S[X]} (p:A.IsPrimitive) (deg:A.natDegree=1) : Prime A := by
  classical
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α:=S)
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid S
  let F:=FractionRing S
  have irr:Irreducible A := by
    apply (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map (R:=S) (K:=F) (p:=A) p).mpr
    apply irreducible_of_degree_eq_one
    let f:=algebraMap S F
    have inj:=IsFractionRing.injective S F
    have an:A.map f≠0:=(map_ne_zero_iff (mapRingHom f) (map_injective _ inj)).mpr p.ne_zero
    change (A.map f).degree=1
    rw [degree_eq_natDegree an,natDegree_map_eq_of_injective inj,deg];rfl
  exact irr.prime

/-- These two polynomial equations are chosen globally, before any label
or evaluation node. Each is prime in the ring with all variables integral. -/
structure Model {h} {D:PoleData h} {Crt:CRTLift D} {N:Jet} (M:HelperPhysicalModel.Model Crt N) where
  original : Source
  raw : Source
  original_prime : Prime original
  raw_prime : Prime raw
  original_slope : original.natDegree=1
  raw_slope : raw.natDegree=1
  original_eq : Associated (doubleMap K1_14_1_4.centerBase original) N
  raw_eq : Associated (doubleMap rawCoeff raw) M.raw

theorem exists_model {h} {D:PoleData h} {Crt:CRTLift D} {N:Jet} (M:HelperPhysicalModel.Model Crt N)
    (prime:Prime N) (slope:N.natDegree=1) : Nonempty (Model M) := by
  obtain ⟨P,pp,pa⟩:=PhysicalPrimitiveCoeffs.global_native prime
  have ps:P.natDegree=1:=by
    have eq:=deg_associated pa prime.ne_zero
    change (P.map (mapRingHom K1_14_1_4.centerBase)).natDegree=_ at eq
    rwa [natDegree_map_eq_of_injective (map_injective _ PadeRawField.center_injective),slope] at eq
  have rdeg:M.raw.natDegree=1:=by
    let f:=mapRingHom evalRaw
    have inj:Function.Injective f:=map_injective _ PadeRawField.eval_injective
    have ne: (jetConstant M.c:K1_14_3.SeedField[X][X])≠0:=C_ne_zero.mpr (C_ne_zero.mpr M.unit_c)
    have native:=K1_14_1_4.specialized_leading Crt prime.ne_zero
    have top:=(natDegree_map_eq_of_injective inj M.raw).symm
    change M.raw.natDegree=(doubleMap evalRaw M.raw).natDegree at top
    rw [top,M.eq,natDegree_mul ne native.2.2,native.1,slope]
    simp [jetConstant]
  obtain ⟨Q,qp,qa⟩:=PhysicalPrimitiveCoeffs.global_raw (linear_prime M.primitive rdeg)
  have qs:Q.natDegree=1:=by
    have eq:=deg_associated qa M.primitive.ne_zero
    change (Q.map (mapRingHom rawCoeff)).natDegree=_ at eq
    rw [natDegree_map_eq_of_injective (map_injective _ (map_injective _ (IsFractionRing.injective K1_14_1.SeedPoly K1_14_1.SeedField))),rdeg] at eq
    exact eq
  exact ⟨⟨P,Q,pp,qp,ps,qs,pa,qa⟩⟩

private theorem assoc_scalar {S:Type*} [CommRing S] [IsDomain S] {P Q:S[X][X]} (eq:Associated P Q) :
    ∃ c:S,IsUnit c ∧ P=jetConstant c*Q := by
  obtain ⟨v,id⟩:=eq.symm
  obtain ⟨c,unit,val⟩:=GlobalPrimitive.unit_constant v.isUnit
  exact ⟨c,unit,id.symm.trans (val ▸ mul_comm _ _)⟩

theorem Model.native_scalar {h} {D:PoleData h} {Crt:CRTLift D} {N:Jet} {M:HelperPhysicalModel.Model Crt N}
    (data:Model M) : ∃ c:Seeds,IsUnit c ∧ doubleMap K1_14_1_4.centerBase data.original=jetConstant c*N :=
  assoc_scalar data.original_eq

theorem Model.raw_weight {h} {D:PoleData h} {Crt:CRTLift D} {N:Jet} {M:HelperPhysicalModel.Model Crt N}
    (data:Model M) (w j i n:ℕ) (nz:(((data.raw.coeff j).coeff i).coeff n)≠0) :
    n+w*i+(w-1)*j≤RawPhysicalDegree.weight w (w-1) M.raw := by
  obtain ⟨d,unit,id⟩:=assoc_scalar data.raw_eq
  obtain ⟨c,cu,dc⟩:=Polynomial.isUnit_iff.mp unit
  rw [←dc] at id
  have eq:=congrArg (fun P:RawSource=>((P.coeff j).coeff i).coeff n) id
  simp only [doubleMap,PhysicalPrimitiveCoeffs.rawCoeff,coe_mapRingHom,coeff_map,jetConstant,
    RingHom.comp_apply,coeff_C_mul] at eq
  have alive:((M.raw.coeff j).coeff i).coeff n ≠ 0 := by
    intro z;rw [z,mul_zero] at eq
    exact nz ((map_eq_zero_iff _ (IsFractionRing.injective K1_14_1.SeedPoly K1_14_1.SeedField)).mp eq)
  exact (RawPhysicalDegree.bounded_iff ..).mpr le_rfl j i n alive

end
end Research6966.IntegralGraphModels
