import ProximityPrize.SubmissionLower.R6966ProofPhysicalChartAtMark
import ProximityPrize.SubmissionLower.R6966ProofNativeGraphMarks

set_option Elab.async false

namespace Research6966.CRTChartSpecialization
open Finset Polynomial
open K1_14 (L FX Jet Seeds)
open K1_14_1 (SeedPoly PoleData CRTLift Source RawSource rawBlock crtPolynomial poleProduct jetConstant)
open K1_14_1_2 (RegularRing localLift includeGeneric specialize map_localLift specialize_localLift markedLift)
open K1_14_1_4 (evalRaw doubleMap specialized centerBase)
open PhysicalPrimitiveCoeffs (R rawCoeff)
open PhysicalChartAtMark (AtSeeds Chart H into genericMap direct atNode atLine atSeeds)
open RegularPhysicalChart (transform)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 850000
set_option maxSynthPendingDepth 24
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

private abbrev B:=K1_14_3.SeedField
private abbrev inc {h} (D:PoleData h) (t:Fin 2→L):=algebraMap (AtSeeds t) (Chart D t)
def diag {h} (D:PoleData h) (t:Fin 2→L) : (Chart D t)ˣ:=
  (IsLocalization.Away.algebraMap_isUnit (S:=Chart D t) (H D t)).unit
def crtMap {h} {D:PoleData h} (Crt:CRTLift D) (t:Fin 2→L)
    (ok:∀i,(Crt.denominator i).eval (t i)≠0) :=
  transform (↑(diag D t):Chart D t) (inc D t (localLift Crt t ok)) (inc D t (H D t).derivative)
    (inc D t (localLift Crt t ok).derivative)

private theorem model_coeffs {h} {D:PoleData h} (Crt:CRTLift D) (t:Fin 2→L)
    (ok:∀i,(Crt.denominator i).eval (t i)≠0) :
    genericMap D t (diag D t)=evalRaw (rawBlock D) ∧
    genericMap D t (inc D t (localLift Crt t ok))=evalRaw (crtPolynomial Crt) ∧
    genericMap D t (inc D t (H D t).derivative)=evalRaw (rawBlock D).derivative ∧
    genericMap D t (inc D t (localLift Crt t ok).derivative)=evalRaw (crtPolynomial Crt).derivative := by
  have header:(↑(diag D t):Chart D t)=inc D t (H D t):=IsUnit.unit_spec _
  have hmap:(H D t).map (includeGeneric t)=rawBlock D:=PhysicalChartAtMark.generic_H D t
  have lift:=map_localLift Crt t ok
  rw [header]
  simp only [inc,PhysicalChartAtMark.generic_atBase]
  change evalRaw ((H D t).map _) = _ ∧
    evalRaw ((localLift Crt t ok).map _) = _ ∧ evalRaw ((H D t).derivative.map _) = _ ∧
    evalRaw ((localLift Crt t ok).derivative.map _) = _
  rw [←derivative_map,←derivative_map,hmap,lift]
  exact ⟨rfl,rfl,rfl,rfl⟩

private theorem dcomp {U V W:Type*} [CommRing U] [CommRing V] [CommRing W]
    (f:U→+*V) (g:V→+*W) (N:U[X][X]) : doubleMap g (doubleMap f N)=doubleMap (g.comp f) N := by
  ext j i;simp [doubleMap]

private theorem send {U V:Type*} [CommRing U] [CommRing V] (f:U→+*V) (a b u d:U) (P:U[X][X]) :
    doubleMap f (transform a b u d P)=transform (f a) (f b) (f u) (f d) (doubleMap f P) :=
  RingHom.congr_fun (RegularPhysicalChart.maps f a b u d) P

private theorem from_native {U V:Type*} [CommRing U] [CommRing V] (f:U→+*V) (a b u d:V) (P:U[X][X]) :
    transform a b u d (doubleMap f P)=K1_14_1_4.substitute f (C (C a*Polynomial.X+C b))
      (C (C a)*Polynomial.X+C (C u*Polynomial.X+C d)) P := by
  change ((K1_14_1_4.substitute (RingHom.id V) _ _).comp (doubleMap f)) P=_
  rw [K1_14_1_4.substitute_map,RingHom.id_comp]
  simp [jetConstant,RegularPhysicalChart.yVar,RegularPhysicalChart.vVar,map_add,map_mul,add_assoc]

private theorem forward_eq {h} {D:PoleData h} (Crt:CRTLift D) (t:Fin 2→L)
    (ok:∀i,(Crt.denominator i).eval (t i)≠0) (P:Source) :
    doubleMap (genericMap D t) (crtMap Crt t ok (doubleMap (into D t) P))=
      specialized Crt (doubleMap K1_14_1_4.centerBase P) := by
  obtain ⟨a,b,u,d⟩:=model_coeffs Crt t ok
  unfold crtMap
  rw [send,dcomp,PhysicalChartAtMark.generic_atSource,a,b,u,d]
  let native:=doubleMap K1_14_1_4.centerBase P
  have lift:doubleMap direct P=doubleMap (algebraMap Seeds B) native:=
    (dcomp centerBase (algebraMap Seeds B) P).symm
  rw [lift,from_native]
  exact (RingHom.congr_fun (K1_14_1_4.specialized_formula Crt) native).symm

private theorem raw_at_generic {h} (D:PoleData h) (t:Fin 2→L) (Q:Source) :
    doubleMap (genericMap D t) (doubleMap (into D t) Q)=doubleMap evalRaw (doubleMap rawCoeff Q) := by
  calc
    _ = doubleMap ((genericMap D t).comp (into D t)) Q := dcomp (into D t) (genericMap D t) Q
    _ = doubleMap direct Q := congrArg (fun g:R→+*B=>doubleMap g Q) (PhysicalChartAtMark.generic_atSource D t)
    _ = doubleMap (evalRaw.comp rawCoeff) Q := congrArg (fun g:R→+*B=>doubleMap g Q) PhysicalChartAtMark.direct_eq.symm
    _ = _ := (dcomp rawCoeff evalRaw Q).symm

private theorem native_raw_associated {h} {D:PoleData h} {Crt:CRTLift D} {N:Jet}
    (M:HelperPhysicalModel.Model Crt N) : Associated (specialized Crt N) (doubleMap evalRaw M.raw) := by
  rw [M.eq]
  apply Associated.symm
  exact associated_unit_mul_left _ _ (isUnit_C.mpr (isUnit_C.mpr M.unit_c.isUnit))

private theorem generic_pair {h} {D:PoleData h} (Crt:CRTLift D) (t:Fin 2→L)
    (ok:∀i,(Crt.denominator i).eval (t i)≠0) {N:Jet} (M:HelperPhysicalModel.Model Crt N) {P Q:Source}
    (np:Associated (doubleMap centerBase P) N) (rq:Associated (doubleMap rawCoeff Q) M.raw) :
    Associated (doubleMap (genericMap D t) (crtMap Crt t ok (doubleMap (into D t) P)))
      (doubleMap (genericMap D t) (doubleMap (into D t) Q)) := by
  rw [forward_eq Crt t ok P,raw_at_generic D t Q]
  have hp:Associated (specialized Crt (doubleMap centerBase P)) (specialized Crt N):=np.map (specialized Crt).toRingHom
  have hq:Associated (doubleMap evalRaw (doubleMap rawCoeff Q)) (doubleMap evalRaw M.raw):=rq.map (doubleMap evalRaw)
  exact hp.trans ((native_raw_associated M).trans hq.symm)

set_option maxHeartbeats 1500000 in
/-- The two global integral models differ by a unit at each admissible
label after inverting the pole block. Consequently the same comparison
can be specialized at every allowed node and at the generic abscissa. -/
theorem chart_unit {h} {D:PoleData h} (Crt:CRTLift D) (t:Fin 2→L)
    (ok:∀i,(Crt.denominator i).eval (t i)≠0) {N:Jet} (M:HelperPhysicalModel.Model Crt N)
    {P Q:Source} (pp:Prime P) (qp:Prime Q) (ps:0<P.natDegree) (qs:0<Q.natDegree)
    (np:Associated (doubleMap K1_14_1_4.centerBase P) N) (rq:Associated (doubleMap rawCoeff Q) M.raw) :
    ∃ c:Chart D t,IsUnit c ∧ crtMap Crt t ok (doubleMap (into D t) P)=jetConstant c*doubleMap (into D t) Q := by
  exact RegularPhysicalChart.comparison (R:=R) (S:=Chart D t) (F:=B) (into D t) (PhysicalChartAtMark.into_injective D t)
    (PhysicalChartAtMark.into_clears D t) (genericMap D t) (PhysicalChartAtMark.generic_injective D t)
    (PhysicalChartAtMark.generic_clears D t) (diag D t) (inc D t (localLift Crt t ok))
    (inc D t (H D t).derivative) (inc D t (localLift Crt t ok).derivative) pp qp ps qs
    (generic_pair Crt t ok M np rq)

end
end Research6966.CRTChartSpecialization
