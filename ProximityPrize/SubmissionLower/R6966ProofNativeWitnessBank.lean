import ProximityPrize.SubmissionLower.R6966ProofHelperWeightCap
import ProximityPrize.SubmissionLower.R6966ProofNativeProjectedWitness

set_option Elab.async false

namespace Research6966.NativeWitnessBank
open Polynomial Finset Module
open K1_14 (Jet Shape L Equation shapeSum)
open K1_14_1 (CRTLift PoleData)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Parent Surface ProjectedProduct OrderAt)
open KoalaRect (rectEvaluated area rectDebit)
open HelperAvoidance (debitAt rectSlots triSlots)
open PadeNativeQuotient (Native)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false

theorem irreducible {G:Pade.Row K1_14_3.SeedField} (N:Native G) (gp:G.primitive) : Irreducible N.poly := by
  classical
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α:=Equation)
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid Equation
  let F:=FractionRing Equation
  let f:=algebraMap Equation F
  refine (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map
    (R:=Equation) (K:=F) (p:=N.poly) N.primitive).mpr ?_
  apply irreducible_of_degree_eq_one
  have fi:=IsFractionRing.injective Equation F
  have nz:N.poly.map f≠0:=(map_ne_zero_iff (mapRingHom f) (map_injective _ fi)).mpr N.primitive.ne_zero
  change (N.poly.map f).degree=1
  rw [degree_eq_natDegree nz,natDegree_map_eq_of_injective fi,NativeGraphMarks.slope_degree N gp];rfl

def witnessed {G:Pade.Row K1_14_3.SeedField} (N:Native G) (parents:Finset Surface) (H:Equation) : Prop :=
  ProjectedProduct parents H ∧ ∀ Q:Jet,∀ J k:ℕ,Q.natDegree≤J →
    (∀ q∈parents,OrderAt q Q k) → H^k∣TerminalProjection.cleared
      (NativeGraphExceptional.den N) (NativeGraphExceptional.rhs N) Q J

theorem exists_witnessed {G:Pade.Row K1_14_3.SeedField} (N:Native G) (gp:G.primitive)
    {parents:Finset Surface} (nonempty:parents.Nonempty) (geo:∀ q∈parents,Parent q)
    (owner:∀ q∈parents,N.poly∈q.asIdeal) : ∃ H:Equation,witnessed N parents H :=
  NativeProjectedWitness.projected_factor N gp parents nonempty geo owner

private theorem consume {h agreement r:ℕ} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    {G:Pade.Row K1_14_3.SeedField} (N:Native G) (gp:G.primitive) {parents:Finset Surface} {H:Equation}
    (chosen:witnessed N parents H) {s envelope:Shape} {top:ℕ} (cut:top-1+2*h*r<s.m*agreement)
    (fits:TerminalBanks.inside s envelope) (small:r+1<K1.p) (U width:Fin 2→ℕ)
    (widthFit:∀ j i z,((N.poly.coeff j).coeff i).degreeOf z≤width z)
    (geo:∀ q∈parents,Parent q) (pass:∀ q∈parents,TerminalBanks.Pass Crt word agreement envelope q)
    (Q:Jet) (row:Q∈rectEvaluated Crt word s (top-1) U) (avoid:¬N.poly∣Q) :
    (r+1)*H.natDegree≤s.B+(G.graphDegree-1)*s.J ∧
      ∀ z,(r+1)*KoalaRect.axisDegree H z≤U z+s.J*width z := by
  have ev:=KoalaRect.rectEvaluated_le Crt word s (top-1) U row
  have nz:Q≠0:=by rintro rfl;exact avoid (dvd_zero _)
  have cap (j:ℕ) (mem:j∈Q.support) : (Q.coeff j).natDegree+j≤s.B ∧ j≤s.J := by
    have top: (Q.coeff j).coeff (Q.coeff j).natDegree≠0:=by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr (mem_support_iff.mp mem)
    exact ⟨(K1_14_1.evaluated_shape Crt word ev j _ top).1,(K1_14_1.evaluated_shape Crt word ev j _ top).2.1⟩
  have sj:Q.natDegree≤s.J:=(cap _ (natDegree_mem_support_of_nonzero nz)).2
  exact NativeProjectedWitness.avoiding_widths N gp chosen.1.primitive.ne_zero Q (r+1) s.J s.B U width
    avoid sj (fun j mem=>(cap j mem).1) (KoalaRect.rectEvaluated_axis Crt word row) widthFit
    (chosen.2 Q s.J (r+1) sj (fun q hq=>TerminalBanks.retained_order Crt word (geo q hq)
      (pass q hq) fits small cut ev))

/-- Every positive rectangle bounds the *same* fixed native projected
product in both seed axes and the ordinate, directly from terminal passes. -/
theorem rectangle {h agreement r top:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    {G:Pade.Row K1_14_3.SeedField} (N:Native G) (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} {H:Equation} (chosen:witnessed N parents H) {s envelope:Shape}
    (U lower width:Fin 2→ℕ) (isSeed:K1_14_2.UsesSeed N.poly) (char:s.U<K1.p) (charB:s.B<K1.p)
    {L0 nodes moment:ℕ} (lCap:L0≤RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw)
    (axisLow:∀ z,lower z≤PadeNativeQuotient.axis N.poly z)
    (axisHigh:∀ j i z,((N.poly.coeff j).coeff i).degreeOf z≤width z)
    (box:U 0+U 1≤s.U) (wide:s.B*(131071-h)≤top) (nt:0<top)
    (nodeCap:P1_7_1.nodeRows s≤nodes) (poleCap:P1_7_1.groupedPoleMoment s.B s.J≤moment)
    (positive:rectDebit h nodes moment U + ∑ W∈range top,debitAt s h top W G.graphDegree 1 L0 (rectSlots U lower) <
      area U*shapeSum s (fun q j=>top+j-q*(131071-h)))
    (cut:top-1+2*h*r<s.m*agreement) (fits:TerminalBanks.inside s envelope) (small:r+1<K1.p)
    (geo:∀ q∈parents,Parent q) (pass:∀ q∈parents,TerminalBanks.Pass Crt word agreement envelope q) :
    (r+1)*H.natDegree≤s.B+(G.graphDegree-1)*s.J ∧ ∀ z,(r+1)*KoalaRect.axisDegree H z≤U z+s.J*width z := by
  have nd:=NativeGraphMarks.slope_degree N gp
  obtain ⟨Q,mem,avoid⟩:=HelperAvoidance.rect_avoiding hp hl Crt word s U lower phys (irreducible N gp)
    (by omega) isSeed char (HelperWeightCap.native_degree N gp).ge nd.ge lCap axisLow box charB nt wide nodeCap poleCap positive
  exact consume Crt word N gp chosen cut fits small U width axisHigh geo pass Q mem avoid

theorem triangular {h agreement r top:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    {G:Pade.Row K1_14_3.SeedField} (N:Native G) (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} {H:Equation} (chosen:witnessed N parents H) (bank:P1_7.Bank) {envelope:Shape}
    (width:Fin 2→ℕ) (isSeed:K1_14_2.UsesSeed N.poly) (char:bank.shape.U<K1.p) (charB:bank.shape.B<K1.p)
    {L0 lower:ℕ} (lCap:L0≤RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw)
    (uLow:lower≤seedDegree N.poly) (axisHigh:∀ j i z,((N.poly.coeff j).coeff i).degreeOf z≤width z)
    (wide:bank.shape.B*(131071-h)≤top) (nt:0<top)
    (nodeCap:P1_7_1.nodeRows bank.shape=bank.nodeRows) (poleCap:P1_7_1.groupedPoleMoment bank.shape.B bank.shape.J≤bank.poleMoment)
    (positive:P1_7.debit h bank + ∑ W∈range top,debitAt bank.shape h top W G.graphDegree 1 L0 (triSlots bank.shape.U lower) <
      K1_14.triangle bank.shape.U*shapeSum bank.shape (fun q j=>top+j-q*(131071-h)))
    (cut:top-1+2*h*r<bank.shape.m*agreement) (fits:TerminalBanks.inside bank.shape envelope) (small:r+1<K1.p)
    (geo:∀ q∈parents,Parent q) (pass:∀ q∈parents,TerminalBanks.Pass Crt word agreement envelope q) :
    (r+1)*H.natDegree≤bank.shape.B+(G.graphDegree-1)*bank.shape.J ∧
      ∀ z,(r+1)*KoalaRect.axisDegree H z≤bank.shape.U+bank.shape.J*width z := by
  have nd:=NativeGraphMarks.slope_degree N gp
  obtain ⟨Q,mem,avoid⟩:=HelperAvoidance.triangle_avoiding hp hl Crt word bank phys (irreducible N gp)
    (by omega) isSeed char (HelperWeightCap.native_degree N gp).ge nd.ge lCap uLow charB nt wide nodeCap poleCap positive
  rw [←RectangularHelperShift.all_axes] at mem
  exact consume Crt word N gp chosen cut fits small _ width axisHigh geo pass Q mem avoid

#print axioms rectangle
#print axioms triangular
end
end Research6966.NativeWitnessBank
