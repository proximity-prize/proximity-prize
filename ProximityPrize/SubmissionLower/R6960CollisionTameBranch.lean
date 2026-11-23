import ProximityPrize.SubmissionLower.R6960CollisionTameOrder
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 4700000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionTame
noncomputable section
open Ideal IsLocalRing
open scoped Matrix

variable {R : Type*} [CommRing R] [IsDomain R]

private theorem primeCompl_le (P : Ideal R) [P.IsPrime] : P.primeCompl≤nonZeroDivisors R := by
  intro z hz
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  rintro rfl
  exact (Ideal.mem_primeCompl_iff.mp hz) (P.zero_mem)

theorem branch_algebraMap_injective (P : Ideal R) [P.IsPrime] :
    Function.Injective (algebraMap R (Localization.AtPrime P)) :=
  IsLocalization.injective _ (primeCompl_le P)

omit [IsDomain R] in
theorem branch_maximal (P : Ideal R) [P.IsPrime] (q : R) (span : P=Ideal.span {q}) :
    maximalIdeal (Localization.AtPrime P)=Ideal.span {algebraMap R (Localization.AtPrime P) q} := by
  let A := Localization.AtPrime P
  calc
    _ = P.map (algebraMap R A) := (IsLocalization.AtPrime.map_eq_maximalIdeal P A).symm
    _ = (Ideal.span {q}).map (algebraMap R A) := congrArg (Ideal.map (algebraMap R A)) span
    _ = _ := by rw [Ideal.map_span,Set.image_singleton]

/-- The local ring at a nonzero principal prime is a DVR. The image of
its original generator is a uniformizer in that actual local ring. -/
theorem principal_prime_dvr [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] (q : R) (nonzero : q≠0)
    (span : P=Ideal.span {q}) : IsDiscreteValuationRing (Localization.AtPrime P) := by
  let A := Localization.AtPrime P
  let : IsNoetherianRing A := IsLocalization.isNoetherianRing P.primeCompl A inferInstance
  have ideal := branch_maximal P q span
  have field : ¬IsField A := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq,ideal,Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff _ (branch_algebraMap_injective P)).mpr nonzero
  have principal : (maximalIdeal A).IsPrincipal := ⟨_,ideal⟩
  exact ((IsDiscreteValuationRing.TFAE A field).out 5 1).mp principal

theorem branch_uniformizer (P : Ideal R) [P.IsPrime] (q : R) (nonzero : q≠0)
    (span : P=Ideal.span {q}) : Irreducible (algebraMap R (Localization.AtPrime P) q) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    ((map_ne_zero_iff _ (branch_algebraMap_injective P)).mpr nonzero) (branch_maximal P q span)

omit [IsDomain R] in
private theorem residue_kernel (P : Ideal R) [P.IsPrime] (x : R) :
    residue (Localization.AtPrime P) (algebraMap R _ x)=0 ↔ x∈P := by
  change Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime P)) (algebraMap R _ x)=0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change x∈(maximalIdeal (Localization.AtPrime P)).under R ↔ x∈P
  rw [IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P]

/-- The quotient by the branch equation embeds into its actual generic
residue field. This is the map used for the generic rank on the divisor. -/
def branchResidue (P : Ideal R) [P.IsPrime] : R ⧸ P →+* ResidueField (Localization.AtPrime P) :=
  Ideal.Quotient.lift P ((residue (Localization.AtPrime P)).comp (algebraMap R _))
    (fun x h=>(residue_kernel P x).mpr h)

omit [IsDomain R] in
@[simp] theorem branchResidue_mk (P : Ideal R) [P.IsPrime] (x : R) :
    branchResidue P (Ideal.Quotient.mk P x)=residue (Localization.AtPrime P) (algebraMap R _ x) :=
  rfl

omit [IsDomain R] in
theorem branchResidue_injective (P : Ideal R) [P.IsPrime] : Function.Injective (branchResidue P) := by
  apply (injective_iff_map_eq_zero (branchResidue P)).mpr
  intro a hz
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective a
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ((residue_kernel P x).mp hz)

omit [IsDomain R] in
/-- Divisibility by powers of the branch generator is unchanged on the
original chart by passage to its height-one local ring. -/
theorem branch_power_dvd_iff [DecompositionMonoid R] (P : Ideal R) [P.IsPrime] (q : R) (pir : Irreducible q)
    (span : P=Ideal.span {q}) (n : ℕ) (a : R) :
    (algebraMap R (Localization.AtPrime P) q)^n∣algebraMap R (Localization.AtPrime P) a ↔ q^n∣a := by
  let A := Localization.AtPrime P
  let j := algebraMap R A
  constructor
  · intro hd
    have hP : (P^n).map j=Ideal.span {(j q)^n} := by
      rw [Ideal.map_pow,IsLocalization.AtPrime.map_eq_maximalIdeal P A,
        branch_maximal P q span,Ideal.span_singleton_pow]
    have hz : j a∈(P^n).map j := hP.symm ▸ Ideal.mem_span_singleton.mpr hd
    obtain ⟨m,hm,hma⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl A (P^n) a).mp hz
    have notdiv : ¬q∣m := by
      intro dv
      apply (Ideal.mem_primeCompl_iff.mp hm)
      rw [span]
      exact Ideal.mem_span_singleton.mpr dv
    have src : q^n∣m*a := by
      have eq : P^n=Ideal.span {q^n} := congrArg (fun I : Ideal R=>I^n) span |>.trans (Ideal.span_singleton_pow _ _)
      exact Ideal.mem_span_singleton.mp (eq ▸ hma)
    exact ((pir.isRelPrime_iff_not_dvd).mpr notdiv).pow_left.dvd_of_dvd_mul_left src
  · intro dv
    rw [←map_pow]
    exact map_dvd (algebraMap R A) dv

/-- The DVR order of any original chart element is exactly its extended
multiplicity along the branch equation. -/
theorem branch_order [IsNoetherianRing R] [DecompositionMonoid R] (P : Ideal R) [P.IsPrime] (q : R) (pir : Irreducible q)
    (span : P=Ideal.span {q}) (a : R) :
    let : IsDiscreteValuationRing (Localization.AtPrime P) := principal_prime_dvr P q pir.ne_zero span
    IsDiscreteValuationRing.addVal (Localization.AtPrime P) (algebraMap R (Localization.AtPrime P) a)=
      emultiplicity q a := by
  let A := Localization.AtPrime P
  let : IsDiscreteValuationRing A := principal_prime_dvr P q pir.ne_zero span
  let j := algebraMap R A
  change IsDiscreteValuationRing.addVal A (j a)=_
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  have val : IsDiscreteValuationRing.addVal A ((j q)^n)=(n:ℕ∞) := by
    rw [AddValuation.map_pow,IsDiscreteValuationRing.addVal_uniformizer (branch_uniformizer P q pir.ne_zero span),
      nsmul_eq_mul,mul_one]
  rw [←pow_dvd_iff_le_emultiplicity,←val,IsDiscreteValuationRing.addVal_le_iff_dvd]
  exact branch_power_dvd_iff P q pir span n a

variable {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- The local ring at the branch uses the same fraction field as the
original chart, with the unique localization map into that field. -/
def branchFractionHom (P : Ideal R) [P.IsPrime] : Localization.AtPrime P →+* F :=
  IsLocalization.lift (M:=P.primeCompl) (g:=algebraMap R F) fun r=>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp (primeCompl_le P r.property)))

@[simp] theorem branchFractionHom_apply (P : Ideal R) [P.IsPrime] (x : R) :
    branchFractionHom (F:=F) P (algebraMap R (Localization.AtPrime P) x)=algebraMap R F x :=
  IsLocalization.lift_eq _ _

theorem branchFraction_isFractionRing (P : Ideal R) [P.IsPrime] :
    let : Algebra (Localization.AtPrime P) F := (branchFractionHom (F:=F) P).toAlgebra
    IsFractionRing (Localization.AtPrime P) F := by
  let A := Localization.AtPrime P
  let : Algebra A F := (branchFractionHom (F:=F) P).toAlgebra
  let : IsScalarTower R A F := IsScalarTower.of_algebraMap_eq (R:=R) (S:=A) (A:=F)
    (branchFractionHom_apply (F:=F) P · |>.symm)
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl A F

/-- A chart trace matrix evaluated at the generic branch residue has
corank equal to the exponent of the branch equation in its determinant,
provided its localization is the trace matrix on the actual local order. -/
theorem trace_order_from_local_matrix [IsNoetherianRing R] [DecompositionMonoid R]
    (P : Ideal R) [P.IsPrime] (q : R) (pir : Irreducible q) (span : P=Ideal.span {q})
    {F E ι : Type*} [Field F] [Field E] [Fintype ι] [DecidableEq ι]
    [Algebra (Localization.AtPrime P) F] [IsFractionRing (Localization.AtPrime P) F]
    [Algebra (Localization.AtPrime P) E] [Algebra F E] [IsScalarTower (Localization.AtPrime P) F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (p : ℕ) [CharP (ResidueField (Localization.AtPrime P)) p] (small : Module.finrank F E<p)
    (b : Module.Basis ι (Localization.AtPrime P) (LocalOrder (Localization.AtPrime P) E))
    (M : Matrix ι ι R)
    (actual : M.map (algebraMap R (Localization.AtPrime P)) = Algebra.traceMatrix (Localization.AtPrime P) b) :
    emultiplicity q M.det=
      ((Fintype.card ι-((M.map (Ideal.Quotient.mk P)).map (branchResidue P)).rank : ℕ):ℕ∞) := by
  let A := Localization.AtPrime P
  let : IsDiscreteValuationRing A := principal_prime_dvr P q pir.ne_zero span
  let j := algebraMap R A
  have det : j M.det=(Algebra.traceMatrix A b).det := by
    have eq : (M.map j).det=j M.det := ((algebraMap R A).map_det M).symm
    exact eq.symm.trans (congrArg Matrix.det actual)
  have mapped : (Algebra.traceMatrix A b).map (residue A)=
      (M.map (Ideal.Quotient.mk P)).map (branchResidue P) := by rw [←actual]; rfl
  have ord := normalized_trace_order p small b (j q) (branch_uniformizer P q pir.ne_zero span)
  rw [←det,branch_order P q pir span,mapped] at ord
  exact ord

#print axioms principal_prime_dvr
#print axioms branchResidue_injective
#print axioms branchFraction_isFractionRing
#print axioms branch_order
#print axioms trace_order_from_local_matrix
end
end Lower6960.CollisionTame
