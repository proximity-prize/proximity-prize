import ProximityPrize.SubmissionLower.R6966ProofPadeNativeQuotient

set_option Elab.async false

namespace Research6966.PadePhysicalQuotient
open Polynomial Finset
open K1_14 (Jet L Shape FX)
open K1_14_1 (PoleData CRTLift centerEval jetConstant RawSource)
open K1_14_1_4 (doubleMap specialized)
open K1_14_3 (SeedField SeedClosure Parent Surface fibreRow)
open PadeRank (Plane)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 18
set_option backward.isDefEq.respectTransparency false

private abbrev E:=SeedClosure
private abbrev f:=algebraMap SeedField E
private abbrev g:=PadeRawField.rawField

private theorem maps_raw (P:RawSource) : doubleMap f (doubleMap K1_14_1_4.evalRaw P)=doubleMap g P := by
  ext j i
  simp only [doubleMap,coe_mapRingHom,coeff_map,PadeRawField.rawField,RingHom.comp_apply]

private theorem maps_const {R K:Type*} [CommSemiring R] [CommSemiring K] (f:R→+*K) (c:R) :
    doubleMap f (jetConstant c)=jetConstant (f c) := by
  simp only [doubleMap,jetConstant,coe_mapRingHom,Polynomial.map_C,RingHom.comp_apply]

private theorem cancel_graph {K:Type*} [Field K] {G P Q:Plane K} (gn:G≠0)
    (a b c:K) (t:ℕ) (an:a≠0)
    (eq:(jetConstant a*G)^t*P=jetConstant c*((jetConstant b*G)^t*Q)) :
    P=jetConstant (c*b^t/a^t)*Q := by
  have bare:(jetConstant a)^t*P=jetConstant c*((jetConstant b)^t*Q) := by
    apply mul_left_cancel₀ (pow_ne_zero t gn)
    calc
      G^t*((jetConstant a)^t*P)=(jetConstant a*G)^t*P := by rw [mul_pow];ring
      _ = _ := eq
      _ = G^t*(jetConstant c*((jetConstant b)^t*Q)) := by rw [mul_pow];ring
  apply mul_left_cancel₀ (a:=jetConstant (a^t)) (C_ne_zero.mpr (C_ne_zero.mpr (pow_ne_zero _ an)))
  rw [←mul_assoc,←map_mul,show a^t*(c*b^t/a^t)=c*b^t by field_simp,map_mul,map_pow]
  rw [map_pow,mul_assoc]
  exact bare

/-- The native quotient and integral physical quotient represent exactly
the same transformed row up to a scalar. This comparison is valid before
discarding any physical positions. -/
theorem compare {h} {D:PoleData h} (Crt:CRTLift D) {G:Pade.Row SeedField}
    (raw:PadeConcentration.Model Crt G) (native:PadeNativeQuotient.Native G) (gp:G.primitive)
    {P:K1_14_1.Source} {Q:Jet} {R:RawSource} (t debit:ℕ)
    (nativeEq:centerEval P=native.poly^t*Q)
    (rawEq:K1_14_1.forward Crt P=jetConstant ((K1_14_1.rawBlock D)^debit)*(raw.raw^t*R)) :
    raw.transform (fibreRow Q)=jetConstant (g ((K1_14_1.rawBlock D)^debit)*raw.scalar^t/native.scalar^t)*
      doubleMap g R := by
  let G₁:Plane E:=(G.map f).polynomial
  have nativeMap: fibreRow (centerEval P)=(jetConstant native.scalar*G₁)^t*fibreRow Q := by
    change doubleMap K1_14_3.seedGeneric (centerEval P)=_
    rw [nativeEq,map_mul,map_pow]
    change (fibreRow native.poly)^t*fibreRow Q=_
    rw [native.eq]
  have scalar (c:E) : raw.transform (jetConstant c)=jetConstant c := raw.transform.commutes c
  have eq:(jetConstant native.scalar*raw.transform G₁)^t*raw.transform (fibreRow Q)=
      jetConstant (g ((K1_14_1.rawBlock D)^debit))*
        ((jetConstant raw.scalar*raw.transform G₁)^t*doubleMap g R) := by
    calc
      _ = raw.transform (fibreRow (centerEval P)) := by
        rw [nativeMap,map_mul raw.transform,map_pow raw.transform,map_mul raw.transform,scalar]
      _ = doubleMap f (specialized Crt (centerEval P)) := raw.onRows _
      _ = _ := by
        rw [K1_14_1_4.specialized_center,maps_raw,rawEq,map_mul (doubleMap g),maps_const,
          map_mul (doubleMap g),map_pow (doubleMap g),raw.equation]
  have nz:G₁≠0 := (G.map f).polynomial_ne ((G.primitive_map f).mpr gp)
  exact cancel_graph (raw.leading nz).2.2 _ _ _ _ native.nonzero eq

/-- Each nonzero physical coefficient in the native quotient pays the
full graph weight. This also excludes the entire row when the weight
spent on its forced graph already exceeds the cutoff. -/
theorem support {h W:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    {G:Pade.Row SeedField} (raw:PadeConcentration.Model Crt G) (native:PadeNativeQuotient.Native G)
    (gp:G.primitive) {s:Shape} {P:K1_14_1.Source} {Q:Jet} {R:RawSource} (t:ℕ)
    (mem:P∈K1_14_1.complete Crt word s W) (nEq:centerEval P=native.poly^t*Q)
    (rEq:K1_14_1.forward Crt P=jetConstant ((K1_14_1.rawBlock D)^(s.B+s.J))*(raw.raw^t*R))
    (j i:ℕ) (nonzero:((raw.transform (fibreRow Q)).coeff j).coeff i≠0) :
    (131071-h)*i+(131071-h-1)*j+t*RawPhysicalDegree.weight (131071-h) (131071-h-1) raw.raw≤W := by
  have eq:=compare Crt raw native gp t (s.B+s.J) nEq rEq
  have nz:(R.coeff j).coeff i≠0 := by
    intro zero
    apply nonzero
    rw [eq]
    simp only [jetConstant,RingHom.comp_apply,coeff_C_mul,doubleMap,coe_mapRingHom,coeff_map,zero,map_zero,mul_zero]
  have rn:R≠0:=fun zero=>nz (by simp [zero])
  obtain ⟨S,Sid,weight⟩:=P0_10_1.complete_raw_bounded hp hl Crt word mem
  have cn:(jetConstant ((K1_14_1.rawBlock D)^(s.B+s.J)):RawSource)≠0 :=
    C_ne_zero.mpr (C_ne_zero.mpr (pow_ne_zero _ (K1_14_1_4.rawBlock_monic D).ne_zero))
  have factor:=mul_left_cancel₀ cn (Sid.symm.trans rEq)
  have paid:=(RawPhysicalDegree.bounded_iff ..).mp weight
  rw [factor,RawPhysicalDegree.weight_product _ _ (pow_ne_zero _ raw.primitive.ne_zero) rn] at paid
  have pw:RawPhysicalDegree.weight (131071-h) (131071-h-1) (raw.raw^t)=
    t*RawPhysicalDegree.weight (131071-h) (131071-h-1) raw.raw := by
    simp [RawPhysicalDegree.weight,natDegree_pow]
  rw [pw] at paid
  have region:=(RawPhysicalDegree.bounded_iff (131071-h) (131071-h-1) _ R).mpr le_rfl
  have last:=region j i ((R.coeff j).coeff i).natDegree (leadingCoeff_ne_zero.mpr nz)
  omega

#print axioms compare
#print axioms support
end
end Research6966.PadePhysicalQuotient
