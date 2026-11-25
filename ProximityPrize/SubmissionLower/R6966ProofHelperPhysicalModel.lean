import ProximityPrize.SubmissionLower.R6966ProofPadeIntegralGraph
import ProximityPrize.SubmissionLower.R6966ProofPadeChart

set_option Elab.async false

namespace Research6966.HelperPhysicalModel
open Polynomial
open K1_14 (Jet Seeds)
open K1_14_1 (PoleData CRTLift RawSource jetConstant centerEval)
open K1_14_1_4 (doubleMap specialized evalRaw)
open K1_14_3 (SeedField)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 750000
set_option maxSynthPendingDepth 16
set_option backward.isDefEq.respectTransparency false

private theorem other_unit {R:Type*} [CommRing R] [IsDomain R] {H P Q:R}
    (hn:H≠0) (eq:H=P*Q) (dv:H∣P) : IsUnit Q := by
  obtain ⟨t,id⟩:=dv
  have pn:=left_ne_zero_of_mul (eq ▸ hn)
  have cancel:P*1=P*(Q*t):=by rw [mul_one,←mul_assoc,←eq];exact id
  exact IsUnit.of_mul_eq_one t (mul_left_cancel₀ pn cancel).symm

/-- Localizing the seed coefficients of a positive-slope prime preserves
irreducibility. A factorization after localization would clear to two native
polynomial factors, one of which must contain the original prime. -/
theorem generic_prime {R:Type*} [CommRing R] [IsDomain R] {N:R[X][X]}
    (pr:Prime N) (slope:0<N.natDegree) :
    Irreducible (doubleMap (algebraMap R (FractionRing R)) N) := by
  classical
  let f:=algebraMap R (FractionRing R)
  let φ:=doubleMap f
  have fi:=IsFractionRing.injective R (FractionRing R)
  have inject:Function.Injective φ:=map_injective _ (map_injective _ fi)
  have hn:φ N≠0:=(map_ne_zero_iff φ inject).mpr pr.ne_zero
  have positive:0<(φ N).natDegree := by
    change 0<(N.map (mapRingHom f)).natDegree
    rwa [natDegree_map_eq_of_injective (map_injective f fi)]
  refine ⟨fun unit=>positive.ne' (natDegree_eq_zero_of_isUnit unit),?_⟩
  intro P Q eq
  change φ N=P*Q at eq
  obtain ⟨A,a,an,hA⟩:=PadeIntegralGraph.clear_two (R:=R) P
  obtain ⟨B,b,bn,hB⟩:=PadeIntegralGraph.clear_two (R:=R) Q
  have prod:A*B=jetConstant (a*b)*N := by
    apply inject
    have c (x:R):φ (jetConstant x)=jetConstant (f x) := by
      simp only [φ,doubleMap,jetConstant,coe_mapRingHom,RingHom.comp_apply,Polynomial.map_C]
    calc
      φ (A*B) = φ A*φ B := map_mul _ _ _
      _ = (jetConstant (f a)*P)*(jetConstant (f b)*Q) := by rw [←hA,←hB]
      _ = jetConstant (f (a*b))*φ N := by rw [map_mul f,map_mul jetConstant,eq];ring
      _ = φ (jetConstant (a*b)*N) := by rw [map_mul φ,c]
  have dv:N∣A*B:=prod ▸ dvd_mul_left _ _
  have descend {D:R[X][X]} {t:R} {T:(FractionRing R)[X][X]} (nz:t≠0)
      (cleared:φ D=jetConstant (f t)*T) (div:N∣D) : φ N∣T := by
    have h:=map_dvd φ div
    rw [cleared] at h
    have unit:IsUnit (jetConstant (f t):(FractionRing R)[X][X]):=
      isUnit_C.mpr (isUnit_C.mpr ((map_ne_zero_iff f fi).mpr nz).isUnit)
    exact (associated_unit_mul_left _ _ unit).dvd_iff_dvd_right.mp h
  rcases pr.dvd_or_dvd dv with left|right
  · exact Or.inr (other_unit hn eq (descend an hA left))
  · exact Or.inl (other_unit hn (eq.trans (mul_comm ..)) (descend bn hB right))

structure Model {h} {D:PoleData h} (Crt:CRTLift D) (N:Jet) where
  raw : RawSource
  primitive : raw.IsPrimitive
  c : SeedField
  unit_c : c≠0
  eq : doubleMap evalRaw raw=jetConstant c*specialized Crt N

theorem exists_model {h} {D:PoleData h} (Crt:CRTLift D) {N:Jet} (irr:Irreducible N)
    (slope:0<N.natDegree) : Nonempty (Model Crt N) := by
  let f:=algebraMap Seeds SeedField
  obtain ⟨a,b,u,d,an,form⟩:=K1_14_1_4.specialized_affine_form Crt
  let T:=PadeChart.chart a b u d
  let eqv:=AlgEquiv.ofBijective T (PadeChart.chart_equiv a b u d an)
  have chart:specialized Crt N=T (doubleMap f N) := by
    have id:=RingHom.congr_fun form N
    change specialized Crt N=_ at id
    rw [id]
    change _ = (K1_14_1_4.substitute (RingHom.id SeedField) _ _).comp (doubleMap f) N
    rw [K1_14_1_4.substitute_map,RingHom.id_comp]
  have generic:Irreducible (doubleMap f N):=generic_prime (R:=Seeds) (N:=N) irr.prime slope
  have image:Irreducible (specialized Crt N) := by rw [chart];exact (MulEquiv.irreducible_iff eqv).mpr generic
  have pos:(specialized Crt N).natDegree≠0:=by rw [(K1_14_1_4.specialized_leading Crt irr.ne_zero).1];exact slope.ne'
  obtain ⟨G,c,prim,unit,id⟩:=PadeIntegralGraph.raw_model _ (image.isPrimitive pos)
  exact ⟨⟨G,prim,c,unit,id⟩⟩

theorem Model.physical_support {h W t:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h} {Crt:CRTLift D}
    {N:Jet} (M:Model Crt N) (word:K1.I→K1_14.L) {s:K1_14.Shape} {P:K1_14_1.Source} {Q:Jet}
    (member:P∈K1_14_1.complete Crt word s W) (div:centerEval P=N^t*Q) (j i:ℕ)
    (nz:((specialized Crt Q).coeff j).coeff i≠0) :
    (131071-h)*i+(131071-h-1)*j+t*RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw≤W := by
  obtain ⟨R,rawEq,bounded⟩:=P0_10_1.complete_raw_bounded hp hl Crt word member
  let block:=evalRaw ((K1_14_1.rawBlock D)^(s.B+s.J))
  have blockUnit:IsUnit (jetConstant block:SeedField[X][X]) :=
    isUnit_C.mpr (isUnit_C.mpr (by
      dsimp only [block];rw [map_pow];exact (pow_ne_zero _ (K1_14_1_4.evalRaw_block_ne_zero D)).isUnit))
  have val:=K1_14_1_4.specialized_center Crt P
  rw [div,map_mul,map_pow,rawEq,map_mul] at val
  have pole:doubleMap evalRaw (jetConstant ((K1_14_1.rawBlock D)^(s.B+s.J)))=jetConstant block := by
    simp only [doubleMap,jetConstant,coe_mapRingHom,Polynomial.map_C,RingHom.comp_apply];rfl
  rw [pole] at val
  have unit:IsUnit (jetConstant M.c:SeedField[X][X]) := isUnit_C.mpr (isUnit_C.mpr M.unit_c.isUnit)
  have gv:(doubleMap evalRaw M.raw)^t∣doubleMap evalRaw R := by
    rw [M.eq,mul_pow]
    apply (associated_unit_mul_left _ _ blockUnit).dvd_iff_dvd_right.mp
    exact (associated_unit_mul_left _ _ (unit.pow t)).dvd.trans ⟨_,val.symm⟩
  obtain ⟨S,id⟩:=PadeRawField.integral_power evalRaw PadeRawField.eval_injective M.primitive t gv
  have mapped:doubleMap evalRaw M.raw≠0:=(map_ne_zero_iff (doubleMap evalRaw)
    (map_injective _ (map_injective _ PadeRawField.eval_injective))).mpr M.primitive.ne_zero
  have sn:specialized Crt N≠0:=by intro z;apply mapped;rw [M.eq,z,mul_zero]
  rw [id,map_mul,map_pow,M.eq,mul_pow] at val
  have same:specialized Crt Q=jetConstant (block*M.c^t)*doubleMap evalRaw S := by
    apply mul_left_cancel₀ (pow_ne_zero t sn)
    calc
      _ = _ := val
      _ = _ := by rw [map_mul jetConstant,map_pow jetConstant];ring
  have nonzero:(S.coeff j).coeff i≠0 := by
    intro z;apply nz
    rw [same]
    simp only [jetConstant,RingHom.comp_apply,coeff_C_mul,doubleMap,coe_mapRingHom,coeff_map,z,map_zero,mul_zero]
  have nonS:S≠0:=by intro z;exact nonzero (by simp [z])
  have paid:=(RawPhysicalDegree.bounded_iff ..).mp bounded
  rw [id,RawPhysicalDegree.weight_product _ _ (pow_ne_zero t M.primitive.ne_zero) nonS] at paid
  have pw:RawPhysicalDegree.weight (131071-h) (131071-h-1) (M.raw^t)=
      t*RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw := by simp [RawPhysicalDegree.weight,natDegree_pow]
  rw [pw] at paid
  have own:=(RawPhysicalDegree.bounded_iff (131071-h) (131071-h-1) _ S).mpr le_rfl
  have last:=own j i ((S.coeff j).coeff i).natDegree (leadingCoeff_ne_zero.mpr nonzero)
  omega

#print axioms generic_prime
#print axioms exists_model
#print axioms Model.physical_support

def Model.mul {h} {D:PoleData h} {Crt:CRTLift D} {A B:Jet} (left:Model Crt A) (right:Model Crt B) :
    Model Crt (A*B) where
  raw:=left.raw*right.raw
  primitive:=by
    let := UniqueFactorizationMonoid.strongNormalizationMonoid (α:=K1_14_1.SeedField[X][X])
    let := UniqueFactorizationMonoid.toNormalizedGCDMonoid K1_14_1.SeedField[X][X]
    exact left.primitive.mul right.primitive
  c:=left.c*right.c
  unit_c:=mul_ne_zero left.unit_c right.unit_c
  eq:=by rw [map_mul,left.eq,right.eq,map_mul jetConstant,map_mul];ring
end
end Research6966.HelperPhysicalModel
