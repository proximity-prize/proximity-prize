import ProximityPrize.SubmissionLower.R6966ProofCRTChartSpecialization
import ProximityPrize.SubmissionLower.R6966ProofPhysicalSeparant
import ProximityPrize.SubmissionLower.R6966ProofPhysicalOriginal

set_option Elab.async false

namespace Research6966.PhysicalMonitor
open Polynomial Finset
open K1_14 (L FX Jet liftPoly graphEval atX)
open K1_14_1 (PoleData CRTLift Source seedPair poleProduct MarkResidues)
open K1_14_1_2 (markedLift markedLift_residue localLift)
open K1_14_1_4 (doubleMap)
open PhysicalChartAtMark (Chart AtSeeds H into atSeeds)
open PhysicalOriginal (atWord evalSeed)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

private abbrev inc {h} (D:PoleData h) (t:Fin 2→L):=algebraMap (AtSeeds t) (Chart D t)
private def sample {F:Type*} [Field F] {h} (D:PoleData h) (t:Fin 2→L) (e:L[X]→+*F)
    (nz:e (poleProduct D)≠0) : Chart D t→+*F :=
  IsLocalization.Away.lift (H D t) (g:=e.comp (atSeeds t)) (by
    change IsUnit (e (atSeeds t (H D t)));rw [PhysicalChartAtMark.actual_H];exact nz.isUnit)

private theorem sample_base {F:Type*} [Field F] {h} (D:PoleData h) (t:Fin 2→L) (e:L[X]→+*F)
    (nz:e (poleProduct D)≠0) (x:AtSeeds t) : sample D t e nz (inc D t x)=e (atSeeds t x) :=
  IsLocalization.Away.lift_eq _ _ _

private theorem sample_src {F:Type*} [Field F] {h} (D:PoleData h) (t:Fin 2→L) (e:L[X]→+*F)
    (nz:e (poleProduct D)≠0) : (sample D t e nz).comp (into D t)=e.comp (evalSeed t) := by
  apply RingHom.ext
  intro x
  change sample D t e nz (inc D t (PhysicalChartAtMark.embed t x))=_
  rw [sample_base]
  exact congrArg e (RingHom.congr_fun (PhysicalChartAtMark.actual_comp t) x)

private theorem read_slope {F:Type*} [Field F] {h} (D:PoleData h) (t:Fin 2→L) (e:L[X]→+*F)
    (nz:e (poleProduct D)≠0) (P:Source) (ord:L[X]) :
    ((doubleMap (into D t) P).coeff 1).eval₂ (sample D t e nz) (e ord)=e (atWord t ord (P.coeff 1)) := by
  simp only [doubleMap,coe_mapRingHom,coeff_map,eval₂_map,sample_src]
  exact (Polynomial.hom_eval₂ _ _ _ _).symm

/-- The global raw separant detects the native separant both at the
generic physical coordinate and at each regular code node. -/
theorem detects {F:Type*} [Field F] {h} {D:PoleData h} {Crt:CRTLift D} {N:Jet}
    {M:HelperPhysicalModel.Model Crt N} (data:IntegralGraphModels.Model M) (t:Fin 2→L)
    (ok:∀ i,(Crt.denominator i).eval (t i)≠0) (S T:L[X])
    (word:poleProduct D*T+markedLift Crt t=S) (e:L[X]→+*F) (nz:e (poleProduct D)≠0) :
    e (atWord t T (data.raw.coeff 1))≠0 ↔ e (atWord t S (data.original.coeff 1))≠0 := by
  let read:=sample D t e nz
  let a:=CRTChartSpecialization.diag D t
  let b:=inc D t (localLift Crt t ok)
  let u:=inc D t (H D t).derivative
  let d:=inc D t (localLift Crt t ok).derivative
  obtain ⟨c,unit,eq⟩:=CRTChartSpecialization.chart_unit Crt t ok M data.original_prime data.raw_prime
    (data.original_slope ▸ Nat.zero_lt_one) (data.raw_slope ▸ Nat.zero_lt_one) data.original_eq data.raw_eq
  have pcap:(doubleMap (into D t) data.original).natDegree≤1:=
    natDegree_map_le.trans data.original_slope.le
  have qcap:(doubleMap (into D t) data.raw).natDegree≤1:=natDegree_map_le.trans data.raw_slope.le
  have compare:=PhysicalSeparant.nonzero_iff read (a:Chart D t) b u d c a.isUnit unit
    (doubleMap (into D t) data.original) (doubleMap (into D t) data.raw) pcap qcap eq (e T)
  have diagonal:read (a:Chart D t)=e (poleProduct D):=by
    change sample D t e nz ((CRTChartSpecialization.diag D t):Chart D t)=_
    rw [show (↑(CRTChartSpecialization.diag D t):Chart D t)=inc D t (H D t) from IsUnit.unit_spec _,
      sample_base,PhysicalChartAtMark.actual_H]
  have shift:read b=e (markedLift Crt t):=by
    change sample D t e nz (inc D t (localLift Crt t ok))=_
    rw [sample_base];exact congrArg e (K1_14_1_2.specialize_localLift Crt t ok)
  have value:read (a:Chart D t)*e T+read b=e S:=by rw [diagonal,shift,←map_mul,←map_add,word]
  rw [value] at compare
  exact (read_slope D t e nz data.raw T) ▸ (read_slope D t e nz data.original S) ▸ compare

private theorem lift_degree {h} {D:PoleData h} (Crt:CRTLift D) (t:Fin 2→L) :
    (markedLift Crt t).natDegree≤2*h := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_le ..).trans (natDegree_map_le.trans
    (natDegree_le_iff_degree_le.mpr (Crt.numerator_degree i).le))

private theorem monitor_degree {h} {D:PoleData h} {Crt:CRTLift D} {N:Jet}
    {M:HelperPhysicalModel.Model Crt N} (data:IntegralGraphModels.Model M)
    (t:Fin 2→L) (w:ℕ) (T:L[X]) (degree:T.natDegree≤w) :
    (atWord t T (data.raw.coeff 1)).natDegree≤RawPhysicalDegree.weight w (w-1) M.raw-(w-1) := by
  change ((data.raw.coeff 1).eval₂ (evalSeed t) T).natDegree≤_
  rw [eval₂_eq_sum,Polynomial.sum_def]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have nz:((data.raw.coeff 1).coeff i)≠0:=mem_support_iff.mp hi
  have bound:=data.raw_weight w 1 i _ (by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr nz)
  have nat:((evalSeed t) ((data.raw.coeff 1).coeff i)).natDegree≤((data.raw.coeff 1).coeff i).natDegree:=natDegree_map_le
  have product:=natDegree_mul_le.trans (Nat.add_le_add nat ((natDegree_pow_le ..).trans (Nat.mul_le_mul_left i degree)))
  apply product.trans
  rw [Nat.mul_comm i w];simp only [mul_one] at bound;omega

/-- A low-weight quadratic on an actual marked word supplies one nonzero
physical polynomial of the priced degree, valid at every code node. -/
theorem witness {h} (hp:0<h) (hl:h≤131070) {D:PoleData h} {Crt:CRTLift D} {N:Jet}
    {M:HelperPhysicalModel.Model Crt N} (data:IntegralGraphModels.Model M)
    (z:K1.K) (S:K1.K[X]) (res:MarkResidues D z S) (degree:(liftPoly S).natDegree≤131071+h)
    (regular:(N.coeff 1).eval₂ (graphEval z) (atX S)≠0) :
    let w:=131071-h
    ∃ P:L[X],P≠0 ∧ P.natDegree≤RawPhysicalDegree.weight w (w-1) M.raw-(w-1) ∧
      ∀ x:L,(poleProduct D).eval x≠0 → P.eval x≠0 →
        (FixedNodeRows.evaluate (seedPair z) (liftPoly S) (PhysicalOriginal.integralA data.original)).eval x≠0 := by
  let t:=seedPair z
  let w:=131071-h
  have ok (i:Fin 2):(Crt.denominator i).eval (t i)≠0:=Crt.regular i _ (res i).1
  obtain ⟨T,divide⟩:=markedLift_residue Crt res
  have word:poleProduct D*T+markedLift Crt t=liftPoly S:=by rw [←divide];abel
  have hn:(poleProduct D)≠0:=((D.monic 0).mul (D.monic 1)).ne_zero
  have height:T.natDegree≤w := by
    by_cases zero:T=0
    · simp [zero]
    have top:=natDegree_sub_le (liftPoly S) (markedLift Crt t)
    rw [divide,natDegree_mul hn zero] at top
    have dh:(poleProduct D).natDegree=2*h:=by
      rw [poleProduct,natDegree_mul (D.monic 0).ne_zero (D.monic 1).ne_zero,D.degree,D.degree,two_mul]
    have fcap:=lift_degree Crt t
    rw [dh] at top;dsimp only [w];omega
  let P:=atWord t T (data.raw.coeff 1)
  have orig:=PhysicalOriginal.generically_regular data z S regular
  have embed:=IsFractionRing.injective L[X] FX
  have survives:=detects data t ok (liftPoly S) T word (algebraMap L[X] FX)
    ((map_ne_zero_iff _ embed).mpr hn)
  have nz:P≠0:=by
    have val:=survives.mpr ((map_ne_zero_iff _ embed).mpr orig)
    change algebraMap L[X] FX P≠0 at val
    exact (map_ne_zero_iff _ embed).mp val
  refine ⟨P,nz,monitor_degree data t w T height,?_⟩
  intro x good seen
  rw [PhysicalOriginal.integral_slope]
  exact (detects data t ok (liftPoly S) T word (evalRingHom x) good).mp seen

end
end Research6966.PhysicalMonitor
