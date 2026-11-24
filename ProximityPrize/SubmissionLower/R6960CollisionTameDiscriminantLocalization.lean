import ProximityPrize.SubmissionLower.R6960CollisionTamePlaneDiscriminant
import Mathlib.RingTheory.Localization.Integral

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 5100000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.CollisionTame
noncomputable section
open Module Matrix
open scoped Matrix BigOperators

variable {A R F E : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [Field F] [Field E] [Algebra A R] [Algebra A F] [Algebra A E] [Algebra R F] [Algebra R E] [Algebra F E]
  [IsScalarTower A R F] [IsScalarTower A R E] [IsScalarTower A F E] [IsScalarTower R F E]
  [IsFractionRing A F] [IsFractionRing R F] [FiniteDimensional F E] [Algebra.IsSeparable F E]

def integralsIncl : integralClosure A E→+*integralClosure R E :=
  Subring.inclusion (show (integralClosure A E).toSubring≤(integralClosure R E).toSubring
    from fun _ h=>(show IsIntegral A _ from h).tower_top)

theorem gram_map {ι : Type*} (u : ι→integralClosure A E) :
    (tupleGram (integralTraceForm (A:=A) (E:=E) F) u).map (algebraMap A R) =
      tupleGram (integralTraceForm (A:=R) (E:=E) F) (fun i=>integralsIncl (R:=R) (u i)) := by
  apply Matrix.ext
  intro i j
  apply IsFractionRing.injective R F
  change algebraMap R F (algebraMap A R (integralTraceForm (A:=A) (E:=E) F (u i) (u j)))=
    algebraMap R F (integralTraceForm (A:=R) (E:=E) F (integralsIncl (u i)) (integralsIncl (u j)))
  rw [←IsScalarTower.algebraMap_apply,integralTraceForm_map,integralTraceForm_map]
  rfl

/-- The normalized discriminant ideal commutes with localization of the
base chart. Every full-size local tuple has one common denominator. -/
theorem normalizationDiscriminant_map (S : Submonoid A) [IsLocalization S R] :
    (normalizationDiscriminant (A:=A) (E:=E) F).map (algebraMap A R)=
      normalizationDiscriminant (A:=R) (E:=E) F := by
  let e := finrank F E
  let trA := integralTraceForm (A:=A) (E:=E) F
  let trR := integralTraceForm (A:=R) (E:=E) F
  let iR := (normalizationDiscriminant (A:=A) (E:=E) F).map (algebraMap A R)
  let j := algebraMap A R
  apply le_antisymm
  · apply (Ideal.map_le_iff_le_comap).mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨u,rfl⟩
    change j (tupleGram trA u).det∈gramIdeal (ι:=Fin e) trR
    have det : j (tupleGram trA u).det=(tupleGram trR (fun i=>integralsIncl (u i))).det :=
      (RingHom.map_det j _).trans (congrArg Matrix.det (gram_map u))
    rw [det]
    exact gramIdeal_mem trR _
  · change gramIdeal (ι:=Fin e) trR ≤ iR
    apply Ideal.span_le.mpr
    rintro _ ⟨v,rfl⟩
    classical
    choose a ha using fun i : Fin e=>IsIntegral.exists_multiple_integral_of_isLocalization S (v i:E) (v i).property
    let s : S := ∏ i,a i
    have clear (i : Fin e) : IsIntegral A ((s:A) • (v i:E)) := by
      obtain ⟨t,ht⟩ : a i∣s := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      have es : (s:A)=(t:A)*(a i:A) := by rw [ht]; exact mul_comm _ _
      rw [es,mul_smul]
      exact (ha i).smul (t:A)
    let u (i : Fin e) : integralClosure A E := ⟨_,clear i⟩
    have scale (i : Fin e) : integralsIncl (u i)=j (s:A) • v i := by
      apply Subtype.ext
      change (s:A) • (v i:E)=_
      rw [Subalgebra.coe_smul,←IsScalarTower.algebraMap_smul R]
    have mapped : (tupleGram trA u).map j=(j (s:A))^2 • tupleGram trR v := by
      rw [gram_map,show (fun i=>integralsIncl (u i))=(fun i=>j (s:A) • v i) from funext scale,
        tupleGram_smul]
    have det : j (tupleGram trA u).det=(j (s:A))^(2*e)*(tupleGram trR v).det := by
      rw [show j (tupleGram trA u).det=((tupleGram trA u).map j).det from RingHom.map_det j _,
        mapped,det_smul,←pow_mul,Fintype.card_fin]
    have mem : j (tupleGram trA u).det∈iR := Ideal.mem_map_of_mem j (gramIdeal_mem trA u)
    rw [det] at mem
    exact (Ideal.unit_mul_mem_iff_mem iR ((IsLocalization.map_units R s).pow (2*e))).mp mem

#print axioms normalizationDiscriminant_map
end
end Lower6960.CollisionTame
