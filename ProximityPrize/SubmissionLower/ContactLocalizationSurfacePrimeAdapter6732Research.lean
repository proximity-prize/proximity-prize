import ProximityPrize.SubmissionLower.ContactLocalizationQuotientAdapter6732Research
namespace ProximityPrize.SubmissionLower.ContactLocalizationSurfacePrimeAdapter6732Research
open ContactLocalizationQuotientAdapter6732Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {A B:Type*} [CommRing A] [CommRing B]
variable (M:Submonoid A) [Algebra A B] [IsLocalization M B]
def surfaceMap (I:Ideal A):
    (A ⧸ I) →+*(B ⧸ I.map (algebraMap A B)):=
  Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
    Ideal.le_comap_map
@[reducible] def surfaceAlgebra (I:Ideal A):
    Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B)):=
  quotientAlgebra I (I.map (algebraMap A B)) Ideal.le_comap_map
def sourcePrime (I P:Ideal A):Ideal (A ⧸ I):=
  P.map (Ideal.Quotient.mk I)
def targetPrime (I:Ideal A) (J:Ideal B):
    Ideal (B ⧸ I.map (algebraMap A B)):=
  J.map (Ideal.Quotient.mk (I.map (algebraMap A B)))
theorem sourcePrime_isPrime
    (I P:Ideal A) [P.IsPrime] (hIP:I ≤ P):
    (sourcePrime I P).IsPrime:=by
  apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
  simpa only [Ideal.mk_ker] using hIP
theorem map_ideal_le_relation
    (I P:Ideal A) (J:Ideal B)
    (hIP:I ≤ P) (hcontract:J.comap (algebraMap A B)=P):
    I.map (algebraMap A B) ≤ J:=by
  rw [Ideal.map_le_iff_le_comap,hcontract]
  exact hIP
theorem targetPrime_isPrime
    (I P:Ideal A) (J:Ideal B) [J.IsPrime]
    (hIP:I ≤ P) (hcontract:J.comap (algebraMap A B)=P):
    (targetPrime I J).IsPrime:=by
  apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
  simpa only [Ideal.mk_ker] using
    map_ideal_le_relation I P J hIP hcontract
theorem targetPrime_contract
    (I P:Ideal A) (J:Ideal B)
    (hIP:I ≤ P) (hcontract:J.comap (algebraMap A B)=P):
    (targetPrime I J).comap (surfaceMap I)=sourcePrime I P:=by
  let qA:A →+*A ⧸ I:=Ideal.Quotient.mk I
  let qB:B →+*B ⧸ I.map (algebraMap A B):=
    Ideal.Quotient.mk (I.map (algebraMap A B))
  apply Ideal.comap_injective_of_surjective qA Ideal.Quotient.mk_surjective
  change Ideal.comap qA
      (Ideal.comap (surfaceMap I) (Ideal.map qB J))=
    Ideal.comap qA (Ideal.map qA P)
  rw [Ideal.comap_comap]
  have hcomp:(surfaceMap I).comp qA=
      qB.comp (algebraMap A B):=by
    apply DFunLike.ext _ _
    intro a
    rfl
  rw [hcomp, ←Ideal.comap_comap,
    Ideal.comap_map_of_surjective' qB Ideal.Quotient.mk_surjective,
    Ideal.mk_ker,
    sup_eq_left.mpr (map_ideal_le_relation I P J hIP hcontract),
    hcontract,
    Ideal.comap_map_of_surjective' qA Ideal.Quotient.mk_surjective,
    Ideal.mk_ker,sup_eq_left.mpr hIP]
theorem surface_isLocalization (I:Ideal A):
    letI:=surfaceAlgebra (A:=A) (B:=B) I
    IsLocalization (M.map (Ideal.Quotient.mk I))
      (B ⧸ I.map (algebraMap A B)):=by
  letI:=surfaceAlgebra (A:=A) (B:=B) I
  exact quotient_isLocalization M I (I.map (algebraMap A B)) rfl
noncomputable abbrev SourceLocal
    (I P:Ideal A) [P.IsPrime] (hIP:I ≤ P):=
  @Localization.AtPrime (A ⧸ I) _ (sourcePrime I P)
    (sourcePrime_isPrime I P hIP)
noncomputable abbrev TargetLocal
    (I P:Ideal A) (J:Ideal B) [J.IsPrime]
    (hIP:I ≤ P) (hcontract:J.comap (algebraMap A B)=P):=
  @Localization.AtPrime (B ⧸ I.map (algebraMap A B)) _ (targetPrime I J)
    (targetPrime_isPrime I P J hIP hcontract)
noncomputable def surfaceLocalEquiv
    (I P:Ideal A) [P.IsPrime] (J:Ideal B) [J.IsPrime]
    (hIP:I ≤ P) (hcontract:J.comap (algebraMap A B)=P):
    SourceLocal I P hIP ≃+*TargetLocal I P J hIP hcontract:=by
  let p:=sourcePrime I P
  let q:=targetPrime I J
  letI:p.IsPrime:=sourcePrime_isPrime I P hIP
  letI:q.IsPrime:=targetPrime_isPrime I P J hIP hcontract
  let aSurface:=surfaceAlgebra (A:=A) (B:=B) I
  letI:Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B)):=aSurface
  letI:SMul (A ⧸ I) (B ⧸ I.map (algebraMap A B)):=aSurface.toSMul
  letI:IsLocalization (M.map (Ideal.Quotient.mk I))
      (B ⧸ I.map (algebraMap A B)):=surface_isLocalization M I
  let aLocal:Algebra (A ⧸ I) (Localization.AtPrime q):=
    ((algebraMap (B ⧸ I.map (algebraMap A B)) (Localization.AtPrime q)).comp
      (surfaceMap I)).toAlgebra' (fun _ _ => mul_comm _ _)
  letI:Algebra (A ⧸ I) (Localization.AtPrime q):=aLocal
  letI:SMul (A ⧸ I) (Localization.AtPrime q):=aLocal.toSMul
  let targetAlgebra:Algebra (B ⧸ I.map (algebraMap A B))
      (Localization.AtPrime q):=inferInstance
  letI:SMul (B ⧸ I.map (algebraMap A B)) (Localization.AtPrime q):=
    targetAlgebra.toSMul
  letI:IsScalarTower (A ⧸ I) (B ⧸ I.map (algebraMap A B))
      (Localization.AtPrime q):=IsScalarTower.of_algebraMap_eq' rfl
  have hloc:IsLocalization.AtPrime (Localization.AtPrime q) p:=by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M.map (Ideal.Quotient.mk I)) (Localization.AtPrime q) q
    exact (targetPrime_contract I P J hIP hcontract).symm
  letI:IsLocalization.AtPrime (Localization.AtPrime q) p:=hloc
  exact (IsLocalization.algEquiv p.primeCompl _ _).toRingEquiv
end
end ProximityPrize.SubmissionLower.ContactLocalizationSurfacePrimeAdapter6732Research
