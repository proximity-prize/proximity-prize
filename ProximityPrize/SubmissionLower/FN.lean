import ProximityPrize.SubmissionLower.S
import ProximityPrize.SubmissionLower.C9
namespace ProximityPrize.SubmissionLower.ContactPolynomialSurfaceNaturalResidue6733Research
open ContactPlaneLocalOrderPrimary6732Research
open ContactMaximalRelationMonicLift6733Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {R:Type} [CommRing R] [IsLocalRing R]
def polynomialRelationBar (surface:Polynomial R)
   (relation:Ideal (Polynomial R)):Ideal (SurfaceQuotient surface):=
 Ideal.map (Ideal.Quotient.mk (Ideal.span {surface})) relation
@[implicit_reducible] noncomputable def polynomialSurfaceAtPrimeAlgebra
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   Algebra R (Localization.AtPrime (polynomialRelationBar surface relation)):=
 (((algebraMap (SurfaceQuotient surface)
     (Localization.AtPrime (polynomialRelationBar surface relation))).comp
   (Ideal.Quotient.mk (Ideal.span {surface}))).comp
     (Polynomial.C:R →+*Polynomial R)).toAlgebra' (fun _ _ => mul_comm _ _)
theorem polynomialSurfaceAtPrimeAlgebra_eq_natural
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   (inferInstance:Algebra R
     (Localization.AtPrime (polynomialRelationBar surface relation)))=
       polynomialSurfaceAtPrimeAlgebra surface relation:=by
 apply Algebra.algebra_ext
 intro r
 rfl
theorem polynomialSurfaceAtPrimeAlgebra_isLocalHom
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hcontract:relation.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   letI:=polynomialSurfaceAtPrimeAlgebra surface relation
   IsLocalHom (algebraMap R
     (Localization.AtPrime (polynomialRelationBar surface relation))):=by
 let I:Ideal (Polynomial R):=Ideal.span {surface}
 let S:=SurfaceQuotient surface
 let bar:=polynomialRelationBar surface relation
 let L:=Localization.AtPrime bar
 let quotientMap:Polynomial R →+*S:=Ideal.Quotient.mk I
 letI:=polynomialSurfaceAtPrimeAlgebra surface relation
 refine ⟨fun r hrUnit => ?_⟩
 by_contra hrNonunit
 have hrMax:r∈IsLocalRing.maximalIdeal R:=
   (IsLocalRing.mem_maximalIdeal r).2 hrNonunit
 have hrRelation:Polynomial.C r∈relation:=by
   have:r∈relation.comap (Polynomial.C:R →+*Polynomial R):=
     hcontract.symm ▸ hrMax
   exact this
 have hrBar:quotientMap (Polynomial.C r)∈bar:=
   Ideal.mem_map_of_mem quotientMap hrRelation
 have hrTarget:algebraMap S L (quotientMap (Polynomial.C r))∈
     IsLocalRing.maximalIdeal L:=by
   rw [←IsLocalization.AtPrime.map_eq_maximalIdeal bar L]
   exact Ideal.mem_map_of_mem (algebraMap S L) hrBar
 have hscalar:algebraMap R L r=
     algebraMap S L (quotientMap (Polynomial.C r)):=rfl
 have:algebraMap R L r∈IsLocalRing.maximalIdeal L:=hscalar ▸ hrTarget
 exact (IsLocalRing.mem_maximalIdeal (algebraMap R L r)).mp this hrUnit
theorem polynomialSurfaceAtPrimeNatural_isLocalHom
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hcontract:relation.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   IsLocalHom (algebraMap R
     (Localization.AtPrime (polynomialRelationBar surface relation))):=by
 let L:=Localization.AtPrime (polynomialRelationBar surface relation)
 let natural:Algebra R L:=inferInstance
 let custom:Algebra R L:=polynomialSurfaceAtPrimeAlgebra surface relation
 have halg:natural=custom:=
   polynomialSurfaceAtPrimeAlgebra_eq_natural surface relation
 have hcustom:IsLocalHom (@algebraMap R L _ _ custom):=by
   letI:Algebra R L:=custom
   exact polynomialSurfaceAtPrimeAlgebra_isLocalHom surface relation hcontract
 change IsLocalHom (@algebraMap R L _ _ natural)
 have hmap:@algebraMap R L _ _ natural=@algebraMap R L _ _ custom:=
   congrArg (fun A:Algebra R L => @algebraMap R L _ _ A) halg
 rw [hmap]
 exact hcustom
noncomputable def polynomialSurfaceResidueEquiv
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hsurface:surface∈relation)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   (Polynomial R ⧸ relation) ≃+*
     IsLocalRing.ResidueField
       (Localization.AtPrime (polynomialRelationBar surface relation)):=by
 let I:Ideal (Polynomial R):=Ideal.span {surface}
 let bar:=polynomialRelationBar surface relation
 let L:=Localization.AtPrime bar
 have hIJ:I ≤ relation:=Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hsurface)
 exact (DoubleQuot.quotQuotEquivQuotOfLE hIJ).symm.trans
   (IsLocalization.AtPrime.equivQuotMaximalIdeal bar L)
theorem polynomialSurfaceResidueEquiv_compatible
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hcontract:relation.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   (hsurface:surface∈relation)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   let aRelation:=relationResidueAlgebra relation hcontract
   letI:Algebra (IsLocalRing.ResidueField R)
       (Polynomial R ⧸ relation):=aRelation
   letI:IsLocalHom (algebraMap R
       (Localization.AtPrime (polynomialRelationBar surface relation))):=
     polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
   (algebraMap (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField
       (Localization.AtPrime (polynomialRelationBar surface relation)))).comp
       (RingEquiv.refl (IsLocalRing.ResidueField R)).toRingHom=
     (polynomialSurfaceResidueEquiv surface relation hsurface).toRingHom.comp
       (algebraMap (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation)):=by
 let I:Ideal (Polynomial R):=Ideal.span {surface}
 let S:=SurfaceQuotient surface
 let bar:=polynomialRelationBar surface relation
 let L:=Localization.AtPrime bar
 letI:Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation):=
   relationResidueAlgebra relation hcontract
 letI:IsLocalHom (algebraMap R L):=
   polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
 apply RingHom.ext
 intro z
 obtain ⟨r,rfl⟩:=IsLocalRing.residue_surjective z
 change algebraMap (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField L) (IsLocalRing.residue R r)=
   polynomialSurfaceResidueEquiv surface relation hsurface
     (algebraMap (IsLocalRing.ResidueField R)
       (Polynomial R ⧸ relation) (IsLocalRing.residue R r))
 rw [IsLocalRing.ResidueField.algebraMap_residue]
 have hIJ:I ≤ relation:=
   Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hsurface)
 let eDouble:(S ⧸ bar) ≃+*(Polynomial R ⧸ relation):=
   DoubleQuot.quotQuotEquivQuotOfLE hIJ
 let eLocal:(S ⧸ bar) ≃+*IsLocalRing.ResidueField L:=
   IsLocalization.AtPrime.equivQuotMaximalIdeal bar L
 change IsLocalRing.residue L (algebraMap R L r)=
   eLocal (eDouble.symm (Ideal.Quotient.mk relation (Polynomial.C r)))
 have hpre:eDouble.symm (Ideal.Quotient.mk relation (Polynomial.C r))=
     Ideal.Quotient.mk bar (Ideal.Quotient.mk I (Polynomial.C r)):=by
   change (DoubleQuot.quotQuotEquivQuotOfLE hIJ).symm
     (Ideal.Quotient.mk relation (Polynomial.C r))=
       DoubleQuot.quotQuotMk I relation (Polynomial.C r)
   exact DoubleQuot.quotQuotEquivQuotOfLE_symm_mk _ hIJ
 rw [hpre]
 rfl
theorem polynomialSurfaceResidue_finite
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hcontract:relation.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   (hsurface:surface∈relation)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]
   (hfinite:
     letI:=relationResidueAlgebra relation hcontract
     FiniteDimensional (IsLocalRing.ResidueField R)
       (Polynomial R ⧸ relation)):
   letI:IsLocalHom (algebraMap R
       (Localization.AtPrime (polynomialRelationBar surface relation))):=
     polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
   FiniteDimensional (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField
       (Localization.AtPrime (polynomialRelationBar surface relation))):=by
 letI:Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation):=
   relationResidueAlgebra relation hcontract
 letI:FiniteDimensional (IsLocalRing.ResidueField R)
     (Polynomial R ⧸ relation):=hfinite
 letI:IsLocalHom (algebraMap R
     (Localization.AtPrime (polynomialRelationBar surface relation))):=
   polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
 exact Module.Finite.of_equiv_equiv (RingEquiv.refl _)
   (polynomialSurfaceResidueEquiv surface relation hsurface)
     (polynomialSurfaceResidueEquiv_compatible
       surface relation hcontract hsurface)
theorem polynomialSurfaceResidue_finrank_eq_relation
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hcontract:relation.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   (hsurface:surface∈relation)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   letI:Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation):=
     relationResidueAlgebra relation hcontract
   letI:IsLocalHom (algebraMap R
       (Localization.AtPrime (polynomialRelationBar surface relation))):=
     polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
   Module.finrank (IsLocalRing.ResidueField R)
       (IsLocalRing.ResidueField
         (Localization.AtPrime (polynomialRelationBar surface relation)))=
     Module.finrank (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation):=by
 letI:Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation):=
   relationResidueAlgebra relation hcontract
 letI:IsLocalHom (algebraMap R
     (Localization.AtPrime (polynomialRelationBar surface relation))):=
   polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
 exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
   (polynomialSurfaceResidueEquiv surface relation hsurface)
     (polynomialSurfaceResidueEquiv_compatible
       surface relation hcontract hsurface)).symm
end
end ProximityPrize.SubmissionLower.ContactPolynomialSurfaceNaturalResidue6733Research
