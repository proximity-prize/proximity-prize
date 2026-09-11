import ProximityPrize.SubmissionLower.PartF006_06
section Compact_PackedLegacy
section PackedLegacy_GB
namespace ProximityPrize.SubmissionLower.RCN297
open RCN307 RCN308
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {R:Type*} [CommRing R] [IsLocalRing R]

theorem exists_specialized_monic_reducer
   (P:Polynomial R)
   (hPbar:P.map (IsLocalRing.residue R)≠0):
   ∃ M:Polynomial R,
     M.Monic∧
     M∈Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R)∧
     M.natDegree ≤ P.natDegree:=by
 let k:=IsLocalRing.ResidueField R
 let q:R →+*k:=IsLocalRing.residue R
 let Pbar:Polynomial k:=P.map q
 let Mbar:Polynomial k:=Pbar*Polynomial.C Pbar.leadingCoeff⁻¹
 have hMbarMonic:Mbar.Monic:=
   Polynomial.monic_mul_leadingCoeff_inv hPbar
 have hMbarLift:Mbar∈Polynomial.lifts q:=
   Polynomial.mem_lifts_of_surjective (IsLocalRing.residue_surjective) Mbar
 obtain ⟨M,hMmap,hMdegree,hMMonic⟩:=
   Polynomial.lifts_and_natDegree_eq_and_monic hMbarLift hMbarMonic
 obtain ⟨c,hc⟩:=IsLocalRing.residue_surjective Pbar.leadingCoeff⁻¹
 change q c=Pbar.leadingCoeff⁻¹ at hc
 let D:Polynomial R:=M-Polynomial.C c*P
 have hDmap:D.map q=0:=by
   dsimp only [D]
   rw [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
     hMmap,hc]
   dsimp only [Mbar]
   ring
 have hDcoeff:D∈coefficientMaxIdeal (R:=R):=by
   have hker:D∈RingHom.ker (Polynomial.mapRingHom q):=hDmap
   rw [Polynomial.ker_mapRingHom,IsLocalRing.ker_residue] at hker
   exact hker
 have hMmem:M∈Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R):=by
   have hfirst:Polynomial.C c*P∈Ideal.span {P}:=
     (Ideal.span {P}).mul_mem_left _
       (Ideal.subset_span (Set.mem_singleton P))
   have hfirst':Polynomial.C c*P∈
       Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R):=
     (show Ideal.span {P} ≤
       Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R) from le_sup_left) hfirst
   have hDcoeff':D∈
       Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R):=
     (show coefficientMaxIdeal (R:=R) ≤
       Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R) from le_sup_right) hDcoeff
   have hadd:=(Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R)).add_mem
     hfirst' hDcoeff'
   convert hadd using 1 <;>
     simp only [D] <;> ring
 have hdegreeBar:Mbar.natDegree=Pbar.natDegree:=
   Polynomial.natDegree_mul_leadingCoeff_inv Pbar hPbar
 refine ⟨M,hMMonic,hMmem,?_⟩
 rw [hMdegree,hdegreeBar]
 exact Polynomial.natDegree_map_le
end
end ProximityPrize.SubmissionLower.RCN297
end PackedLegacy_GB

/-! Packed from ProximityPrize.SubmissionLower.EP. -/
section PackedLegacy_EP
namespace ProximityPrize.SubmissionLower.RCN143
open scoped Classical BigOperators
open RCN227 RCN307 RCN309 RCN308 RCN297
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Base:Type} [Field Base] [DecidableEq Base]
variable (primeIdeal:Ideal (Polynomial Base)) [primeIdeal.IsPrime]
 (factor:Polynomial Base)
abbrev LocalBase:=Localization.AtPrime primeIdeal
theorem grouped_resultant_power_dvd_of_primary_pieces_modMax
   {J:Type*} [Fintype J] (multiplicity:J → ℕ)
   (hprime:primeIdeal=Ideal.span {factor})
   (hfactor:Irreducible factor) (hfactorMonic:factor.Monic)
   (P₀ Q₀:Polynomial (Polynomial Base)) (m n:ℕ)
   (P Q:Polynomial (LocalBase primeIdeal))
   (hPmap:P=P₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hQmap:Q=Q₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P₀ Q₀ m n≠0)
   (C:PrimaryPiecesCertificate P Q multiplicity)
   [Module.Finite (LocalBase primeIdeal)
     (∀ j,Polynomial (LocalBase primeIdeal) ⧸ C.pieces j)]
   (hmod:Function.Surjective
     (((IsLocalRing.maximalIdeal (LocalBase primeIdeal) •
         (⊤:Submodule (LocalBase primeIdeal)
           (∀ j,Polynomial (LocalBase primeIdeal) ⧸ C.pieces j))).mkQ).comp
       (rawPiecesMap P Q m n C.pieces))):
   factor^(∑ j,multiplicity j)∣
     Polynomial.resultant P₀ Q₀ m n:=by
 have hp0:primeIdeal≠⊥:=by
   rw [hprime,ne_eq,Ideal.span_singleton_eq_bot]
   exact hfactor.ne_zero
 letI:IsDiscreteValuationRing (LocalBase primeIdeal):=
   IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
     (Polynomial Base) hp0 _
 have hmappedResultant:Polynomial.resultant P Q m n=
     algebraMap (Polynomial Base) (LocalBase primeIdeal)
       (Polynomial.resultant P₀ Q₀ m n):=by
   rw [hPmap,hQmap,Polynomial.resultant_map_map]
 have hmappedNe:Polynomial.resultant P Q m n≠0:=by
   rw [hmappedResultant]
   simpa only [map_zero] using
     (FaithfulSMul.algebraMap_injective
       (Polynomial Base) (LocalBase primeIdeal)).ne hresultant
 have hlocal:=
   sum_multiplicities_le_ord_resultant_of_primary_pieces_modMax
     P Q m n hPcap hQcap hmappedNe C.pieces C.contains hmod
       multiplicity C.length_le
 have hlocal':
     (((∑ j,multiplicity j:ℕ):ℕ∞)) ≤
       Ring.ord (LocalBase primeIdeal)
         (algebraMap (Polynomial Base) (LocalBase primeIdeal)
           (Polynomial.resultant P₀ Q₀ m n)):=by
   rw [←hmappedResultant]
   exact hlocal
 exact pow_sum_dvd_of_sum_le_localized_ord primeIdeal factor
   (Polynomial.resultant P₀ Q₀ m n) hprime hfactor hfactorMonic
     hresultant multiplicity hlocal'
theorem grouped_resultant_power_dvd_of_primary_pieces_of_surface_mod_ne_zero
   {J:Type*} [Fintype J] (multiplicity:J → ℕ)
   (hprime:primeIdeal=Ideal.span {factor})
   (hfactor:Irreducible factor) (hfactorMonic:factor.Monic)
   (P₀ Q₀:Polynomial (Polynomial Base)) (m n:ℕ)
   (P Q:Polynomial (LocalBase primeIdeal))
   (hPmap:P=P₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hQmap:Q=Q₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P₀ Q₀ m n≠0)
   (hPbar:P.map (IsLocalRing.residue (LocalBase primeIdeal))≠0)
   (C:PrimaryPiecesCertificate P Q multiplicity)
   [Module.Finite (LocalBase primeIdeal)
     (∀ j,Polynomial (LocalBase primeIdeal) ⧸ C.pieces j)]:
   factor^(∑ j,multiplicity j)∣
     Polynomial.resultant P₀ Q₀ m n:=by
 obtain ⟨M,hMMonic,hMmem,hMdegreeP⟩:=
   exists_specialized_monic_reducer P hPbar
 have hspan:Ideal.span {P} ≤ intersectionIdeal P Q:=by
   rw [Ideal.span_le]
   intro x hx
   rw [Set.mem_singleton_iff] at hx
   subst x
   exact Ideal.subset_span (Set.mem_insert P {Q})
 have hMmem':M∈intersectionIdeal P Q ⊔
     coefficientMaxIdeal (R:=LocalBase primeIdeal):=
   (sup_le_sup hspan le_rfl) hMmem
 have hMdegree:M.natDegree ≤ m+n:=
   hMdegreeP.trans (hPcap.trans (Nat.le_add_right m n))
 have hmod:=rawPieces_modMax_surjective_of_monic_mod
   P Q m n C.pieces C.coprime C.contains M hMMonic hMmem' hMdegree
 exact grouped_resultant_power_dvd_of_primary_pieces_modMax
   primeIdeal factor multiplicity hprime hfactor hfactorMonic
     P₀ Q₀ m n P Q hPmap hQmap hPcap hQcap hresultant C hmod
end
end ProximityPrize.SubmissionLower.RCN143
end PackedLegacy_EP

/-! Packed from ProximityPrize.SubmissionLower.FN. -/
section PackedLegacy_FN
namespace ProximityPrize.SubmissionLower.RCN232
open RCN225 RCN197
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
end ProximityPrize.SubmissionLower.RCN232
end PackedLegacy_FN

/-! Packed from ProximityPrize.SubmissionLower.EB. -/
section PackedLegacy_EB
namespace ProximityPrize.SubmissionLower.RCN110
open RCN011 RCN021 RCN002 RCN264 RCN093 RCN120 RCN102 RCN106 RCN107 RCN232 RCN197 RCN192 RCN111 RCN191
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A → RegularComponent Omega G T H)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
include hfinite in
theorem indexedNaturalSurfaceLocal_isLocalHom
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (a:IndexedFactorFiber component lam mu nu order ht q)
   [hbarMax:(indexedFiberRelationBar component lam mu nu order ht
     q hq surface a).IsMaximal]:
   IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=by
 letI:(polynomialRelationBar (indexedFiberSurface q hq surface)
     (indexedFiberRelation component lam mu nu order ht q hq a)).IsMaximal:=by
   change (indexedFiberRelationBar component lam mu nu order ht
     q hq surface a).IsMaximal
   exact hbarMax
 exact polynomialSurfaceAtPrimeNatural_isLocalHom
   (indexedFiberSurface q hq surface)
   (indexedFiberRelation component lam mu nu order ht q hq a)
   (indexedFiberRelation_comap_C_eq_maximalIdeal
     component lam mu nu order ht hfinite q hq a)
include hfinite hgen in
theorem indexedNaturalSurfaceResidue_finite
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (a:IndexedFactorFiber component lam mu nu order ht q)
   (hsurface:surface∈relationKernel Omega
     (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   [hbarMax:(indexedFiberRelationBar component lam mu nu order ht
     q hq surface a).IsMaximal]:
   letI:IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
     indexedNaturalSurfaceLocal_isLocalHom component lam mu nu order ht hfinite
       q hq surface a
   FiniteDimensional (IsLocalRing.ResidueField (FiberCoefficient q hq))
     (IsLocalRing.ResidueField (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=by
 cases a with
 | mk a hqeq =>
   subst q
   let L:=CoordinateField Omega (component a).1
   let e:=flagEvaluation Omega (component a).1 lam mu nu
   let P:=localizePlane Omega L order e (ht a) (hfinite a) surface
   let J:=localizedRelation Omega L order e (ht a) (hfinite a)
   have hcontract:=localizedRelation_comap_C_eq_maximalIdeal Omega L
     order e (ht a) (hfinite a)
   have hsurfaceJ:P∈J:=Ideal.mem_map_of_mem _ hsurface
   letI:(polynomialRelationBar P J).IsMaximal:=by
     change (indexedFiberRelationBar component lam mu nu order ht
       (indexedComponentFactor component lam mu nu order ht a) hq surface
         ⟨a,rfl⟩).IsMaximal
     exact hbarMax
   have hrelFinite:=localizedRelationResidue_finite Omega L order e
     (ht a) (hfinite a) (hgen a)
   exact polynomialSurfaceResidue_finite P J hcontract hsurfaceJ hrelFinite
include hfinite hgen in
theorem indexedNaturalSurfaceResidue_finrank_eq_plane
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (a:IndexedFactorFiber component lam mu nu order ht q)
   (hsurface:surface∈relationKernel Omega
     (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   [hbarMax:(indexedFiberRelationBar component lam mu nu order ht
     q hq surface a).IsMaximal]:
   letI:IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
     indexedNaturalSurfaceLocal_isLocalHom component lam mu nu order ht hfinite
       q hq surface a
   Module.finrank (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))=
     indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1:=by
 cases a with
 | mk a hqeq =>
   subst q
   let L:=CoordinateField Omega (component a).1
   let e:=flagEvaluation Omega (component a).1 lam mu nu
   let R:=LocalCoefficient Omega L order e (ht a) (hfinite a)
   let P:=localizePlane Omega L order e (ht a) (hfinite a) surface
   let J:=localizedRelation Omega L order e (ht a) (hfinite a)
   have hcontract:=localizedRelation_comap_C_eq_maximalIdeal Omega L
     order e (ht a) (hfinite a)
   have hsurfaceJ:P∈J:=Ideal.mem_map_of_mem _ hsurface
   letI:(polynomialRelationBar P J).IsMaximal:=by
     change (indexedFiberRelationBar component lam mu nu order ht
       (indexedComponentFactor component lam mu nu order ht a) hq surface
         ⟨a,rfl⟩).IsMaximal
     exact hbarMax
   letI:IsLocalHom (algebraMap R
       (Localization.AtPrime (polynomialRelationBar P J))):=
     polynomialSurfaceAtPrimeNatural_isLocalHom P J hcontract
   let aRelation:=relationResidueAlgebra J hcontract
   letI:Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=aRelation
   letI:SMul (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=aRelation.toSMul
   let targetSemiring:Semiring (Polynomial R ⧸ J):=inferInstance
   letI:AddCommMonoid (Polynomial R ⧸ J):=targetSemiring.toAddCommMonoid
   letI:Module (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=Algebra.toModule
   calc
     Module.finrank (IsLocalRing.ResidueField R)
         (IsLocalRing.ResidueField (Localization.AtPrime
           (polynomialRelationBar P J)))=
       Module.finrank (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=
         polynomialSurfaceResidue_finrank_eq_relation P J hcontract hsurfaceJ
     _=indexedPlaneResidueWeight component lam mu nu order ht hfinite a:=by
       simpa [indexedPlaneResidueWeight] using
         localizedRelationResidue_finrank_eq_unlocalized Omega L order e
           (ht a) (hfinite a) (hgen a)
end
end ProximityPrize.SubmissionLower.RCN110
end PackedLegacy_EB

/-! Packed from ProximityPrize.SubmissionLower.EA. -/
section PackedLegacy_EA
namespace ProximityPrize.SubmissionLower.RCN109
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN264 RCN093 RCN102 RCN106 RCN107 RCN143 RCN307 RCN014 RCN120 RCN236 RCN110 RCN111
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A → RegularComponent Omega G T H)
 (hcomponent:Function.Injective component)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
include hcomponent hfinite hgen in
theorem indexedFixedFactor_grouped_resultant_power_dvd
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q) (hqMonic:q.Monic)
   (surface tail:PlaneRing Omega) (m n:ℕ)
   [hSurfacePrime:(Ideal.span {indexedFiberSurface q hq surface}).IsPrime]
   [hbarMax:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal]
   [hlocal:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]
   [hresfinite:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     FiniteDimensional (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]
   (hbarne:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberRelationBar component lam mu nu order ht q hq surface a≠⊥)
   (multiplicity:IndexedFactorFiber component lam mu nu order ht q → ℕ)
   (htail:∀ a,indexedFiberTail q hq tail∈
     Ideal.span {indexedFiberSurface q hq surface} ⊔
       indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a)
   (hPcap:(indexedFiberSurface q hq surface).natDegree ≤ m)
   (hQcap:(indexedFiberTail q hq tail).natDegree ≤ n)
   (hresultant:Polynomial.resultant surface tail m n≠0)
   (hPbar:(indexedFiberSurface q hq surface).map
     (IsLocalRing.residue (FiberCoefficient q hq))≠0):
   q^(∑ a:IndexedFactorFiber component lam mu nu order ht q,
     multiplicity a*Module.finrank
       (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a))))∣
     Polynomial.resultant surface tail m n:=by
 letI:DecidableEq (RatFunc Omega):=Classical.decEq _
 letI:(Ideal.span {q}).IsPrime:=
   (PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 let weight:IndexedFactorFiber component lam mu nu order ht q → ℕ:=fun a =>
   Module.finrank (IsLocalRing.ResidueField (FiberCoefficient q hq))
     (IsLocalRing.ResidueField (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))
 let cert:=indexedWeightedFiberPrimaryPieces component hcomponent lam mu nu
   order ht hfinite hgen q hq surface tail hbarne multiplicity htail
     (hlocal:=hlocal) (hresfinite:=hresfinite)
 letI:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     Module.Finite (FiberCoefficient q hq)
       (Polynomial (FiberCoefficient q hq) ⧸ cert.pieces a):=fun a => by
   obtain ⟨M,hMmonic,hMmem⟩:=exists_monic_mem_indexedFiberRelation
     component lam mu nu order ht hfinite hgen q hq a
   apply RCN309.moduleFinite_quotient_of_monic_mem
     (cert.pieces a) (M^multiplicity a) (hMmonic.pow _)
   have hpow:M^multiplicity a∈
       Ideal.span {indexedFiberSurface q hq surface} ⊔
         indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a:=
     (show indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a ≤
         Ideal.span {indexedFiberSurface q hq surface} ⊔
           indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a
       from le_sup_right) (Ideal.pow_mem_pow hMmem (multiplicity a))
   simpa [cert,indexedWeightedFiberPrimaryPieces,
     primaryPiecesCertificateOfMembershipWeighted,mappedPrimaryPiece] using hpow
 letI:Module.Finite (FiberCoefficient q hq)
     (∀ a,Polynomial (FiberCoefficient q hq) ⧸ cert.pieces a):=inferInstance
 exact grouped_resultant_power_dvd_of_primary_pieces_of_surface_mod_ne_zero
   (Ideal.span {q}) q (fun a => multiplicity a*weight a)
     rfl hq hqMonic surface tail m n
     (indexedFiberSurface q hq surface) (indexedFiberTail q hq tail)
     rfl rfl hPcap hQcap hresultant hPbar cert
include hcomponent hfinite hgen in
theorem indexedFixedFactor_grouped_resultant_power_dvd_of_geometry
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q) (hqMonic:q.Monic)
   (surface tail:PlaneRing Omega) (m n:ℕ)
   [hSurfacePrime:(Ideal.span {indexedFiberSurface q hq surface}).IsPrime]
   (hsurface:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     surface∈relationKernel Omega (CoordinateField Omega (component a.1).1) order
       (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   (hbarne:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberRelationBar component lam mu nu order ht q hq surface a≠⊥)
   (multiplicity:IndexedFactorFiber component lam mu nu order ht q → ℕ)
   (htail:∀ a,indexedFiberTail q hq tail∈
     Ideal.span {indexedFiberSurface q hq surface} ⊔
       indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a)
   (hPcap:(indexedFiberSurface q hq surface).natDegree ≤ m)
   (hQcap:(indexedFiberTail q hq tail).natDegree ≤ n)
   (hresultant:Polynomial.resultant surface tail m n≠0)
   (hPbar:(indexedFiberSurface q hq surface).map
     (IsLocalRing.residue (FiberCoefficient q hq))≠0):
   q^(∑ a:IndexedFactorFiber component lam mu nu order ht q,
     multiplicity a*indexedPlaneResidueWeight component lam mu nu order
       ht hfinite a.1)∣Polynomial.resultant surface tail m n:=by
 letI:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal:=
   fun a => indexedFiberRelationBar_isMaximal component lam mu nu order ht
     hfinite hgen q hq surface hsurface a
 letI:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
   fun a => indexedNaturalSurfaceLocal_isLocalHom component lam mu nu order ht
     hfinite q hq surface a
 letI:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     FiniteDimensional (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
   fun a => indexedNaturalSurfaceResidue_finite component lam mu nu order ht
     hfinite hgen q hq surface a (hsurface a)
 have hpow:=indexedFixedFactor_grouped_resultant_power_dvd component hcomponent
   lam mu nu order ht hfinite hgen q hq hqMonic surface tail m n hbarne
     multiplicity htail hPcap hQcap hresultant hPbar
 have hweight:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     Module.finrank (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))=
       indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1:=
   fun a => indexedNaturalSurfaceResidue_finrank_eq_plane component lam mu nu
     order ht hfinite hgen q hq surface a (hsurface a)
 simpa only [hweight] using hpow
end
end ProximityPrize.SubmissionLower.RCN109
end PackedLegacy_EA

/-! Packed from ProximityPrize.SubmissionLower.M1. -/
section PackedLegacy_M1
namespace ProximityPrize.SubmissionLower.RCN195
open RCN011 RCN021 RCN022 RCN226 RCN191 RCN193
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
theorem localized_surface_residue_ne_zero
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (P₀:Polynomial (Polynomial (RatFunc K)))
   (hspecial:P₀.map
     (AdjoinRoot.mk (projectedFactor K L order e ht))≠0):
   (P₀.map (algebraMap (Polynomial (RatFunc K))
     (LocalCoefficient K L order e ht hfinite))).map
       (IsLocalRing.residue (LocalCoefficient K L order e ht hfinite))≠0:=by
 let q:=projectedFactor K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let E:=Rp ⧸ IsLocalRing.maximalIdeal Rp
 let eqv:=coefficientResidueEquiv K L order e ht hfinite
 let source:Polynomial (AdjoinRoot q):=P₀.map (AdjoinRoot.mk q)
 let target:Polynomial E:=
   (P₀.map (algebraMap (Polynomial (RatFunc K)) Rp)).map
     (IsLocalRing.residue Rp)
 have hmap:source.map eqv.toRingHom=target:=by
   apply Polynomial.ext
   intro n
   simp only [source,target,Polynomial.coeff_map,Function.comp_apply]
   exact coefficientResidueEquiv_mk K L order e ht hfinite (P₀.coeff n)
 intro hzero
 apply hspecial
 apply (Polynomial.map_injective eqv.toRingHom eqv.injective)
 have htargetZero:target=0:=hzero
 rw [hmap,htargetZero,Polynomial.map_zero]
end
end ProximityPrize.SubmissionLower.RCN195
end PackedLegacy_M1

/-! Packed from ProximityPrize.SubmissionLower.E2. -/
section PackedLegacy_E2
namespace ProximityPrize.SubmissionLower.RCN251
open scoped Classical BigOperators
open RCN135 RCN136 RCN086 RCN244 RCN074 RCN245 RCN246 RCN247 RCN249 RCN102 RCN103 RCN106 RCN107 RCN108 RCN109 RCN195 RCN120 RCN093 RCN095 RCN002 RCN011 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
 (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F)
theorem stageFamily_surfacePrime:
   (Ideal.span {indexedFiberSurface W.q W.irreducible
     (stageSurfacePlane S F.lam F.mu F.nu F.order)}).IsPrime:=by
 exact indexedFiberSurface_span_isPrime F.component F.lam F.mu F.nu F.order
   F.ht S.irreducible_G W.q W.irreducible W.witness
theorem stageFamily_surface_mem
   (a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht W.q):
   stageSurfacePlane S F.lam F.mu F.nu F.order∈
     relationKernel (GenericField K)
       (CoordinateField (GenericField K) (F.component a.1).1) F.order
       (flagEvaluation (GenericField K) (F.component a.1).1 F.lam F.mu F.nu)
       (F.ht a.1):=by
 exact indexedStageSurface_mem_relation S F.component F.lam F.mu F.nu
   F.order F.ht a.1
theorem stageFamily_bar_ne
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht W.q):
   indexedFiberRelationBar F.component F.lam F.mu F.nu F.order F.ht
     W.q W.irreducible (stageSurfacePlane S F.lam F.mu F.nu F.order) a≠⊥:=by
 have hproperLocal:indexedFiberTail W.q W.irreducible
     (stageTailPlane S F.lam F.mu F.nu F.order)∉
     Ideal.span {indexedFiberSurface W.q W.irreducible
       (stageSurfacePlane S F.lam F.mu F.nu F.order)}:=
   indexedFiberTail_not_mem_surface F.component F.lam F.mu F.nu F.order F.ht
     S.irreducible_G hfirstProper W.q W.irreducible W.witness
 exact indexedFiberRelationBar_ne_bot F.component F.lam F.mu F.nu F.order
   F.ht W.q W.irreducible
   (stageSurfacePlane S F.lam F.mu F.nu F.order)
   (stageTailPlane S F.lam F.mu F.nu F.order)
   (fun b↦indexedStageTail_mem_relation S F.component F.lam F.mu F.nu
     F.order F.ht b.1) hproperLocal a
theorem stageFamily_tail_mem
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht W.q):
   indexedFiberTail W.q W.irreducible
     (stageTailPlane S F.lam F.mu F.nu F.order)∈
     Ideal.span {indexedFiberSurface W.q W.irreducible
       (stageSurfacePlane S F.lam F.mu F.nu F.order)} ⊔
     indexedFiberRelation F.component F.lam F.mu F.nu F.order F.ht
       W.q W.irreducible a^
       localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
         (F.component a.1):=by
 exact indexedFiberTail_mem_primary S hfirstProper F.component F.lam F.mu
   F.nu F.order F.ht F.finite F.generates W.q W.irreducible a
end
end ProximityPrize.SubmissionLower.RCN251
end PackedLegacy_E2

/-! Packed from ProximityPrize.SubmissionLower.N3. -/
section PackedLegacy_N3
namespace ProximityPrize.SubmissionLower.RCN255
open RCN135 RCN136 RCN244 RCN249 RCN245 RCN106 RCN103 RCN093 RCN095 RCN125 RCN011 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {Omega:Type} [Field Omega]
theorem planeSurface_map_adjoinRoot_ne_zero
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega) (hirr:Irreducible surface)
   (hpositive:0 < surface.natDegree):
   surface.map (AdjoinRoot.mk q)≠0:=by
 letI:Fact (Irreducible q):=⟨hq⟩
 have hcoeff:Polynomial.eval₂RingHom
     (algebraMap (RatFunc Omega) (AdjoinRoot q))
       (AdjoinRoot.root q)=AdjoinRoot.mk q:=by
   apply Polynomial.ringHom_ext
   · intro c
     simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
       AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
   · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,AdjoinRoot.mk_X]
 have hs:=RCN360.bimap_specialization_ne_zero
   (algebraMap (RatFunc Omega) (AdjoinRoot q)) surface
   (hirr.isPrimitive (Nat.ne_of_gt hpositive)) (AdjoinRoot.root q)
 rw [RCN360.bimap_specialization,hcoeff] at hs
 exact hs
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
def StageFamilySurfaceSpecializationNonzero
   (F:StageIndexedFlagFamily S A)
   (q:Polynomial (RatFunc (GenericField K))):Prop:=
 (stageSurfacePlane S F.lam F.mu F.nu F.order).map (AdjoinRoot.mk q)≠0
theorem stageFamily_surface_specialization_ne
   (F:StageIndexedFlagFamily S A)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q):
   StageFamilySurfaceSpecializationNonzero S F q:=by
 change (planeMap (GenericField K) F.order
   (flagAlgHom F.lam F.mu F.nu S.G)).map (AdjoinRoot.mk q)≠0
 exact planeSurface_map_adjoinRoot_ne_zero q hq
   (planeMap (GenericField K) F.order (flagAlgHom F.lam F.mu F.nu S.G))
   (transformedSurface_irreducible F.lam F.mu F.nu F.order S.irreducible_G
     (F.component a.1) (F.ht a.1)) F.positive
end
end ProximityPrize.SubmissionLower.RCN255
end PackedLegacy_N3

/-! Packed from ProximityPrize.SubmissionLower.C4. -/
section PackedLegacy_C4
namespace ProximityPrize.SubmissionLower.RCN112
open RCN095 RCN125 RCN093 RCN123 RCN121 RCN103 RCN012 RCN011 RCN264
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega]
local instance:DecidableEq (RatFunc Omega):=Classical.decEq _
variable {G T H:MvPolynomial (Fin 3) Omega}
def flagPlaneResultant (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (G T:MvPolynomial (Fin 3) Omega):Polynomial (RatFunc Omega):=
 let P:=planeMap Omega order (flagAlgHom lam mu nu G)
 let Q:=planeMap Omega order (flagAlgHom lam mu nu T)
 Polynomial.resultant P Q P.natDegree Q.natDegree
theorem flagPlaneResultant_ne
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (C:RegularComponent Omega G T H)
   (ht:Transcendental Omega
     (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
   (hpositive:0 < (planeMap Omega order (flagAlgHom lam mu nu G)).natDegree):
   flagPlaneResultant lam mu nu order G T≠0:=by
 exact RCN362.irreducible_resultant_ne_zero_of_not_dvd
   (planeMap Omega order (flagAlgHom lam mu nu G))
   (planeMap Omega order (flagAlgHom lam mu nu T))
   (transformedSurface_irreducible lam mu nu order hG C ht) hpositive
   (transformedSurface_not_dvd_tail lam mu nu order hG hproper C ht)
theorem flagPlaneResultant_z_degree_le
   (surfaceFlag tailFlag:FlagDegree) (lam mu nu:Omega)
   (hGsupport:G.support ⊆ flagSupport surfaceFlag)
   (hTsupport:T.support ⊆ flagSupport tailFlag) (hTne:T≠0):
   (flagPlaneResultant lam mu nu zOrder G T).natDegree ≤
     flagMixed surfaceFlag tailFlag unitZFlag:=by
 let gCaps:=flagTrapezoidCaps_flagAlgHom surfaceFlag G lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom tailFlag T lam mu nu hTsupport
 change (Polynomial.resultant
   (planeMap Omega zOrder (flagAlgHom lam mu nu G))
   (planeMap Omega zOrder (flagAlgHom lam mu nu T))).natDegree ≤ _
 exact planeMap_trapezoid_resultant_natDegree_le Omega zOrder
   (flagAlgHom lam mu nu G) (flagAlgHom lam mu nu T)
   surfaceFlag.all tailFlag.all (surfaceFlag.yz+surfaceFlag.all)
   (tailFlag.yz+tailFlag.all) (flagMixed surfaceFlag tailFlag unitZFlag)
   (flag_ne_zero lam mu nu hTne) gCaps.zOuter tCaps.zOuter
   gCaps.zTotal tCaps.zTotal (z_flag_trapezoid_budget surfaceFlag tailFlag)
theorem flagPlaneResultant_u_degree_le
   (surfaceFlag tailFlag:FlagDegree) (lam mu nu:Omega)
   (hGsupport:G.support ⊆ flagSupport surfaceFlag)
   (hTsupport:T.support ⊆ flagSupport tailFlag) (hTne:T≠0):
   (flagPlaneResultant lam mu nu uOrder G T).natDegree ≤
     flagMixed surfaceFlag tailFlag unitYZFlag:=by
 let gCaps:=flagTrapezoidCaps_flagAlgHom surfaceFlag G lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom tailFlag T lam mu nu hTsupport
 change (Polynomial.resultant
   (planeMap Omega uOrder (flagAlgHom lam mu nu G))
   (planeMap Omega uOrder (flagAlgHom lam mu nu T))).natDegree ≤ _
 exact planeMap_trapezoid_resultant_natDegree_le Omega uOrder
   (flagAlgHom lam mu nu G) (flagAlgHom lam mu nu T)
   surfaceFlag.all tailFlag.all
   (surfaceFlag.zOnly+surfaceFlag.yz+surfaceFlag.all)
   (tailFlag.zOnly+tailFlag.yz+tailFlag.all)
   (flagMixed surfaceFlag tailFlag unitYZFlag)
   (flag_ne_zero lam mu nu hTne) gCaps.uOuter tCaps.uOuter
   gCaps.uTotal tCaps.uTotal (u_flag_trapezoid_budget surfaceFlag tailFlag)
theorem flagPlaneResultant_v_degree_le
   (surfaceFlag tailFlag:FlagDegree) (lam mu nu:Omega)
   (hGsupport:G.support ⊆ flagSupport surfaceFlag)
   (hTsupport:T.support ⊆ flagSupport tailFlag) (hTne:T≠0):
   (flagPlaneResultant lam mu nu vOrder G T).natDegree ≤
     flagMixed surfaceFlag tailFlag unitAllFlag:=by
 let gCaps:=flagTrapezoidCaps_flagAlgHom surfaceFlag G lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom tailFlag T lam mu nu hTsupport
 change (Polynomial.resultant
   (planeMap Omega vOrder (flagAlgHom lam mu nu G))
   (planeMap Omega vOrder (flagAlgHom lam mu nu T))).natDegree ≤ _
 exact planeMap_trapezoid_resultant_natDegree_le Omega vOrder
   (flagAlgHom lam mu nu G) (flagAlgHom lam mu nu T)
   (surfaceFlag.yz+surfaceFlag.all) (tailFlag.yz+tailFlag.all)
   (surfaceFlag.zOnly+surfaceFlag.yz+surfaceFlag.all)
   (tailFlag.zOnly+tailFlag.yz+tailFlag.all)
   (flagMixed surfaceFlag tailFlag unitAllFlag)
   (flag_ne_zero lam mu nu hTne) gCaps.vOuter tCaps.vOuter
   gCaps.vTotal tCaps.vTotal (v_flag_trapezoid_budget surfaceFlag tailFlag)
end
end ProximityPrize.SubmissionLower.RCN112
end PackedLegacy_C4

/-! Packed from ProximityPrize.SubmissionLower.N2. -/
section PackedLegacy_N2
namespace ProximityPrize.SubmissionLower.RCN254
open RCN135 RCN136 RCN086 RCN244 RCN245 RCN249 RCN112 RCN103 RCN113 RCN093 RCN095 RCN011
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
theorem stageFamily_resultant_ne
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
   stageFamilyResultant S A F≠0:=by
 change flagPlaneResultant F.lam F.mu F.nu F.order S.G
   (globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))≠0
 exact flagPlaneResultant_ne F.lam F.mu F.nu F.order S.irreducible_G hfirstProper
   (F.component W.witness.1) (F.ht W.witness.1) F.positive
end
end ProximityPrize.SubmissionLower.RCN254
end PackedLegacy_N2

/-! Packed from ProximityPrize.SubmissionLower.FZ. -/
section PackedLegacy_FZ
namespace ProximityPrize.SubmissionLower.RCN250
open scoped Classical BigOperators
open RCN135 RCN086 RCN244 RCN245 RCN249 RCN251 RCN254 RCN102 RCN106 RCN107 RCN109 RCN120 RCN095
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 {A:Type} [Fintype A]
def StageFamilySurfaceModNonzero
   (S:Stage K I Gamma x p flag errorCap stageSupport) (F:StageIndexedFlagFamily S A)
   (W:StageIndexedFactor S A F):Prop:=
 (indexedFiberSurface W.q W.irreducible
   (stageSurfacePlane S F.lam F.mu F.nu F.order)).map
     (IsLocalRing.residue (FiberCoefficient W.q W.irreducible))≠0
@[simp] theorem stageFamilySurfaceModNonzero_eq
   (S:Stage K I Gamma x p flag errorCap stageSupport) (F:StageIndexedFlagFamily S A)
   (W:StageIndexedFactor S A F):
   StageFamilySurfaceModNonzero S F W ↔
     (indexedFiberSurface W.q W.irreducible
       (stageSurfacePlane S F.lam F.mu F.nu F.order)).map
         (IsLocalRing.residue (FiberCoefficient W.q W.irreducible))≠0:=Iff.rfl
end
end ProximityPrize.SubmissionLower.RCN250
end PackedLegacy_FZ

/-! Packed from ProximityPrize.SubmissionLower.N0. -/
section PackedLegacy_N0
namespace ProximityPrize.SubmissionLower.RCN252
open RCN135 RCN136 RCN074 RCN244 RCN249 RCN245 RCN106 RCN107 RCN108 RCN103 RCN102 RCN195 RCN255 RCN250 RCN093 RCN095 RCN002 RCN011 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
theorem stageFamily_surface_mod_ne
   (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
   StageFamilySurfaceModNonzero S F W:=by
 rcases W with ⟨q,hq,_hqMonic,⟨a,hqeq⟩⟩
 let surface:=stageSurfacePlane S F.lam F.mu F.nu F.order
 have hspecial:=stageFamily_surface_specialization_ne S F q hq
   (⟨a,hqeq⟩:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q)
 change surface.map (AdjoinRoot.mk q)≠0 at hspecial
 change (indexedFiberSurface q hq surface).map
   (IsLocalRing.residue (FiberCoefficient q hq))≠0
 subst q
 exact localized_surface_residue_ne_zero (GenericField K)
   (CoordinateField (GenericField K) (F.component a).1) F.order
   (flagEvaluation (GenericField K) (F.component a).1 F.lam F.mu F.nu) (F.ht a)
   (F.finite a) surface hspecial
end
end ProximityPrize.SubmissionLower.RCN252
end PackedLegacy_N0

/-! Packed from ProximityPrize.SubmissionLower.N1. -/

/-! Packed from ProximityPrize.SubmissionLower.Q0. -/
section PackedLegacy_Q0
namespace ProximityPrize.SubmissionLower.RCN333
open scoped Classical BigOperators
open RCN135 RCN136 RCN086 RCN244 RCN074 RCN249 RCN251 RCN252 RCN255 RCN250 RCN247 RCN245 RCN106 RCN107 RCN108 RCN102 RCN103 RCN109 RCN112 RCN113 RCN264 RCN120 RCN243 RCN111 RCN093 RCN095 RCN125 RCN066 RCN336 RCN226 RCN002 RCN011 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 80000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
theorem finiteDimensional_coordinateField_congr
   {Omega:Type} [Field Omega]
   {P Q:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ:P = Q) (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (htP:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ:Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0))))
   (hfinite:letI:=flagBaseAlgebra Omega P lam mu nu order htP
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)) :
   letI:=flagBaseAlgebra Omega Q lam mu nu order htQ
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega Q):=by
 subst Q
 exact hfinite
theorem flagGenerators_congr
   {Omega:Type} [Field Omega]
   {P Q:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ:P = Q) (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (htP:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ:Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0))))
   (hgen:letI:=flagBaseAlgebra Omega P lam mu nu order htP
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 2)),
         flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 1))} :
         Set (CoordinateField Omega P)) = ⊤) :
   letI:=flagBaseAlgebra Omega Q lam mu nu order htQ
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 2)),
       flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 1))} :
       Set (CoordinateField Omega Q)) = ⊤:=by
 subst Q
 exact hgen
theorem indexedComponentFactor_congr
   {Omega:Type} [Field Omega]
   {P Q:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ:P = Q) (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (htP:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ:Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0)))) :
   projectedFactor Omega (CoordinateField Omega P) order
     (flagEvaluation Omega P lam mu nu) htP =
   projectedFactor Omega (CoordinateField Omega Q) order
     (flagEvaluation Omega Q lam mu nu) htQ:=by
 subst Q
 rfl
theorem relationKernel_congr
   {Omega:Type} [Field Omega]
   {P Q:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ:P = Q) (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (htP:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ:Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0)))) :
   relationKernel Omega (CoordinateField Omega P) order
     (flagEvaluation Omega P lam mu nu) htP =
   relationKernel Omega (CoordinateField Omega Q) order
     (flagEvaluation Omega Q lam mu nu) htQ:=by
 subst Q
 rfl
theorem flagPlaneMap_mem_relation
   {Omega:Type} [Field Omega]
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   {A:MvPolynomial (Fin 3) Omega} (hA:A ∈ P) :
   flagPlaneMap Omega lam mu nu order A ∈
     relationKernel Omega (CoordinateField Omega P) order
       (flagEvaluation Omega P lam mu nu) ht:=by
 change planeEvaluation Omega (CoordinateField Omega P) order
   (flagEvaluation Omega P lam mu nu) ht
     (planeMap Omega order (flagAlgHom lam mu nu A)) = 0
 rw [← RingHom.comp_apply,planeEvaluation_comp_planeMap]
 change flagEvaluation Omega P lam mu nu (flagAlgHom lam mu nu A) = 0
 rw [flagEvaluation_flag]
 change A ∈ RingHom.ker (coordinateEvaluation Omega P).toRingHom
 rw [coordinateEvaluation_ker]
 exact hA
theorem ideal_mem_right_of_sub_mem
   {R:Type} [CommRing R] (P:Ideal R) {A B:R}
   (hA:A ∈ P) (hAB:A - B ∈ P):B ∈ P:=by
 have h:=P.sub_mem hA hAB
 simpa only [sub_sub_cancel] using h
@[simp] theorem flagPlaneMap_apply
   {Omega:Type} [Field Omega] (lam mu nu:Omega)
   (order:Fin 3 ≃ Fin 3) (A:MvPolynomial (Fin 3) Omega) :
   flagPlaneMap Omega lam mu nu order A =
     planeMap Omega order (flagAlgHom lam mu nu A):=rfl
theorem reducedStage_indexedFixedFactor_groupedPowerDvd
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (Tred:MvPolynomial (Fin 3) (GenericField K))
   (hd:S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1) - Tred)
   {A:Type} [Fintype A]
   (component:A → RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F))
   (hcomponent:Function.Injective component)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (hfinite:∀ a,
     letI:=flagBaseAlgebra (GenericField K) (component a).1
       lam mu nu order (ht a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (component a).1))
   (hgen:∀ a,
     letI:=flagBaseAlgebra (GenericField K) (component a).1
       lam mu nu order (ht a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 1))} :
         Set (CoordinateField (GenericField K) (component a).1)) = ⊤)
   (positive:0 < (stageSurfacePlane S lam mu nu order).natDegree)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (hqMonic:q.Monic)
   (a0:IndexedFactorFiber component lam mu nu order ht q) :
   q^(∑ a:IndexedFactorFiber component lam mu nu order ht q,
     transportedMultiplicity hd
         (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
         (component a.1) *
       indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1) ∣
     flagPlaneResultant lam mu nu order S.G Tred:=by
 let e:=regularComponentEquiv
   (H:=regularitySurface (polynomialEmbedding K) S.F) hd
 let oldComponent:A → StageComponent S:=fun a => e.symm (component a)
 have oldComponent_val (a:A):(oldComponent a).1 = (component a).1 :=
   regularComponentEquiv_symm_val hd (component a)
 have holdInjective:Function.Injective oldComponent :=
   e.symm.injective.comp hcomponent
 have htold:∀ a,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (oldComponent a).1 lam mu nu
       (MvPolynomial.X (order 0))):=by
   intro a
   rw [oldComponent_val a]
   exact ht a
 have hfiniteold:∀ a,
     letI:=flagBaseAlgebra (GenericField K) (oldComponent a).1
       lam mu nu order (htold a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (oldComponent a).1):=by
   intro a
   exact finiteDimensional_coordinateField_congr
     (oldComponent_val a).symm lam mu nu order (ht a) (htold a) (hfinite a)
 have hgenold:∀ a,
     letI:=flagBaseAlgebra (GenericField K) (oldComponent a).1
       lam mu nu order (htold a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (oldComponent a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (oldComponent a).1 lam mu nu
           (MvPolynomial.X (order 1))} :
         Set (CoordinateField (GenericField K) (oldComponent a).1)) = ⊤:=by
   intro a
   exact flagGenerators_congr (oldComponent_val a).symm lam mu nu order
     (ht a) (htold a) (hgen a)
 let surface:=stageSurfacePlane S lam mu nu order
 let oldTail:=stageTailPlane S lam mu nu order
 let redTail:=flagPlaneMap (GenericField K) lam mu nu order Tred
 letI:(Ideal.span {indexedFiberSurface q hq surface}).IsPrime:=by
   exact indexedFiberSurface_span_isPrime component lam mu nu order ht
     S.irreducible_G q hq a0
 have hsurface:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     surface ∈ relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu) (ht a.1):=by
   intro a
   change flagPlaneMap (GenericField K) lam mu nu order S.G ∈ _
   exact flagPlaneMap_mem_relation (component a.1).1 lam mu nu order (ht a.1)
     (regularComponent_G_mem (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) (component a.1))
 have hproperRed:¬ S.G ∣ Tred:=by
   intro hr
   apply hfirstProper
   have hsum:=hd.add hr
   simpa only [sub_add_cancel] using hsum
 have hredTailRoot:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     redTail ∈ relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu) (ht a.1):=by
   intro a
   exact flagPlaneMap_mem_relation (component a.1).1 lam mu nu order (ht a.1)
     (regularComponent_T_mem (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) (component a.1))
 have hproperLocal:indexedFiberTail q hq redTail ∉
     Ideal.span {indexedFiberSurface q hq surface}:=by
   exact indexedFiberTail_not_mem_surface component lam mu nu order ht
     S.irreducible_G hproperRed q hq a0
 have hbar:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberRelationBar component lam mu nu order ht q hq surface a ≠ ⊥:=by
   intro a
   exact indexedFiberRelationBar_ne_bot component lam mu nu order ht q hq
     surface redTail hredTailRoot hproperLocal a
 have hplaneDvd:surface ∣ oldTail-redTail:=by
   simpa only [surface,oldTail,redTail,stageSurfacePlane,stageTailPlane,
     map_sub] using map_dvd (flagPlaneMap (GenericField K) lam mu nu order) hd
 have htail:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberTail q hq redTail ∈
       Ideal.span {indexedFiberSurface q hq surface} ⊔
         indexedFiberRelation component lam mu nu order ht q hq a ^
           transportedMultiplicity hd
             (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
             (component a.1):=by
   intro a
   let Q:=Ideal.span {indexedFiberSurface q hq surface} ⊔
     indexedFiberRelation component lam mu nu order ht q hq a ^
       transportedMultiplicity hd
         (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
         (component a.1)
   have hfactorOld:q =
       indexedComponentFactor oldComponent lam mu nu order htold a.1:=by
     calc
       q = indexedComponentFactor component lam mu nu order ht a.1:=a.2
       _ = indexedComponentFactor oldComponent lam mu nu order htold a.1:=by
         exact indexedComponentFactor_congr (oldComponent_val a.1).symm
           lam mu nu order (ht a.1) (htold a.1)
   let aold:IndexedFactorFiber oldComponent lam mu nu order htold q :=
     ⟨a.1,hfactorOld⟩
   have hold:=indexedFiberTail_mem_primary S hfirstProper oldComponent
     lam mu nu order htold hfiniteold hgenold q hq aold
   have aold_val:aold.1 = a.1:=rfl
   have hcomponentVal:(oldComponent aold.1).1 = (component a.1).1:=by
     rw [aold_val,oldComponent_val]
   have hrel:indexedFiberRelation oldComponent lam mu nu order htold q hq aold =
       indexedFiberRelation component lam mu nu order ht q hq a:=by
     unfold indexedFiberRelation
     exact congrArg (Ideal.map (fiberLocalizePlane q hq))
       (relationKernel_congr hcomponentVal lam mu nu order
         (htold aold.1) (ht a.1))
   have hmult:localMultiplicity S
       (canonicalLocalDVRFamily S hfirstProper) (oldComponent aold.1) =
       transportedMultiplicity hd
         (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
         (component a.1):=by
     change localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
         (e.symm (component aold.1)) =
       localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
         (e.symm (component a.1))
     rw [aold_val]
   rw [hrel,hmult] at hold
   have holdQ:indexedFiberTail q hq oldTail ∈ Q:=by
     simpa only [oldTail,surface,Q] using hold
   have hfiberDvd:indexedFiberSurface q hq surface ∣
       indexedFiberTail q hq oldTail-indexedFiberTail q hq redTail:=by
     simpa only [indexedFiberSurface,indexedFiberTail,map_sub] using
       map_dvd (fiberLocalizePlane q hq) hplaneDvd
   have hdiff:indexedFiberTail q hq oldTail-indexedFiberTail q hq redTail ∈ Q :=
     (show Ideal.span {indexedFiberSurface q hq surface} ≤ Q from le_sup_left)
       (Ideal.mem_span_singleton.mpr hfiberDvd)
   exact ideal_mem_right_of_sub_mem Q
     (A:=indexedFiberTail q hq oldTail)
     (B:=indexedFiberTail q hq redTail) holdQ hdiff
 have hresultant0:=flagPlaneResultant_ne lam mu nu order
   S.irreducible_G hproperRed (component a0.1) (ht a0.1) positive
 have hresultant:Polynomial.resultant surface redTail surface.natDegree
     redTail.natDegree ≠ 0:=by
   simpa only [flagPlaneResultant,surface,redTail,stageSurfacePlane,
     flagPlaneMap_apply] using hresultant0
 have hPbar:(indexedFiberSurface q hq surface).map
     (IsLocalRing.residue (FiberCoefficient q hq)) ≠ 0:=by
   have hfactorA0old:q =
       indexedComponentFactor oldComponent lam mu nu order htold a0.1:=by
     calc
       q = indexedComponentFactor component lam mu nu order ht a0.1:=a0.2
       _ = indexedComponentFactor oldComponent lam mu nu order htold a0.1:=by
         exact indexedComponentFactor_congr (oldComponent_val a0.1).symm
           lam mu nu order (ht a0.1) (htold a0.1)
   let F:StageIndexedFlagFamily S A:={
     component:=oldComponent
     injective:=holdInjective
     lam:=lam
     mu:=mu
     nu:=nu
     order:=order
     ht:=htold
     finite:=hfiniteold
     generates:=hgenold
     positive:=positive }
   let a0old:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q :=
     ⟨a0.1,hfactorA0old⟩
   let W:StageIndexedFactor S A F :=
     { q:=q, irreducible:=hq, monic:=hqMonic, witness:=a0old }
   have hPbar0:=stageFamily_surface_mod_ne S F W
   change (indexedFiberSurface q hq
     (stageSurfacePlane S lam mu nu order)).map
       (IsLocalRing.residue (FiberCoefficient q hq)) ≠ 0 at hPbar0
   simpa only [surface] using hPbar0
 have hpow:=indexedFixedFactor_grouped_resultant_power_dvd_of_geometry
   component hcomponent lam mu nu order ht hfinite hgen q hq hqMonic
   surface redTail surface.natDegree redTail.natDegree hsurface hbar
   (fun a => transportedMultiplicity hd
     (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
     (component a.1)) htail Polynomial.natDegree_map_le
       Polynomial.natDegree_map_le hresultant hPbar
 simpa only [flagPlaneResultant,surface,redTail,stageSurfacePlane,
   flagPlaneMap_apply] using hpow
end
end ProximityPrize.SubmissionLower.RCN333
end PackedLegacy_Q0

/-! Packed from ProximityPrize.SubmissionLower.A1. -/
section PackedLegacy_A1
namespace ProximityPrize.SubmissionLower.RCN031
open RCN002 RCN264 RCN341 RCN037 RCN038 RCN093 RCN125 RCN116 RCN120 RCN021 RCN022
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
abbrev ActiveNestedZIndex:={C:RegularComponent Omega G T H//
 Transcendental Omega (coordinate Omega C.1 2)}
def activeNestedZComponent:ActiveNestedZIndex (G:=G) (T:=T) (H:=H) →
   RegularComponent Omega G T H:=Subtype.val
theorem activeNestedZComponent_injective:Function.Injective
   (activeNestedZComponent (G:=G) (T:=T) (H:=H)):=
 Subtype.val_injective
def activeNestedZTranscendental
   (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)):
   Transcendental Omega
     (flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (zOrder 0))):=by
 simpa [zOrder,Equiv.swap_apply_def] using a.2
def activeNestedUTranscendental (C:RegularComponent Omega G T H):
   Transcendental Omega
     (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (uOrder 0))):=by
 simpa [uOrder] using D.uTranscendental C
def activeNestedVTranscendental (C:RegularComponent Omega G T H):
   Transcendental Omega
     (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (vOrder 0))):=by
 simpa [vOrder,Equiv.swap_apply_def] using D.allAffineTranscendental C
include hZ in
theorem activeNestedZGate
   (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H))
   (hx:Transcendental Omega
     (flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (zOrder 0)))):
   (letI:=flagBaseAlgebra Omega a.1.1 D.lam D.mu (D.mu*D.lam) zOrder hx
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega a.1.1))∧
   (letI:=flagBaseAlgebra Omega a.1.1 D.lam D.mu (D.mu*D.lam) zOrder hx
    Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega a.1.1)):=by
 have hx':Transcendental Omega (coordinate Omega a.1.1 2):=by
   simpa [zOrder,Equiv.swap_apply_def] using hx
 have hemb:=elementEmbedding_congr hx hx' (by simp [zOrder,flagEvaluation_X_two])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega a.1.1):=
     (elementEmbedding Omega (CoordinateField Omega a.1.1) _ hx).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega a.1.1))∧
   (letI:Algebra (RatFunc Omega) (CoordinateField Omega a.1.1):=
     (elementEmbedding Omega (CoordinateField Omega a.1.1) _ hx).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega a.1.1))
 rw [hemb]
 exact hZ a.1 hx'
theorem activeNestedUGate (C:RegularComponent Omega G T H)
   (hx:Transcendental Omega
     (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (uOrder 0)))):
   (letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) uOrder hx
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) uOrder hx
    Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)):=by
 have hx':Transcendental Omega (affineU Omega C.1 D.lam):=by
   simpa [uOrder] using hx
 have hemb:=elementEmbedding_congr hx hx' (by simp [uOrder,flagEvaluation_X_zero])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
 rw [hemb]
 exact D.uGate C hx'
theorem activeNestedVGate (C:RegularComponent Omega G T H)
   (hx:Transcendental Omega
     (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (vOrder 0)))):
   (letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) vOrder hx
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) vOrder hx
    Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)):=by
 have hemb:=elementEmbedding_congr hx (D.allAffineTranscendental C)
   (by simp [vOrder,flagEvaluation_X_one])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
 rw [hemb]
 exact ⟨D.allFinite C,D.allSeparable C⟩
def activeNestedZFinite (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)):=
 (activeNestedZGate base hactive hZ hSderiv D a
   (activeNestedZTranscendental base hactive hSderiv D a)).1
def activeNestedUFinite (C:RegularComponent Omega G T H):=
 (activeNestedUGate base hactive hSderiv D C
   (activeNestedUTranscendental base hactive hSderiv D C)).1
def activeNestedVFinite (C:RegularComponent Omega G T H):=
 (activeNestedVGate base hactive hSderiv D C
   (activeNestedVTranscendental base hactive hSderiv D C)).1
theorem activeNestedZGenerates
   (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)):
   letI:=flagBaseAlgebra Omega a.1.1 D.lam D.mu (D.mu*D.lam)
     zOrder (activeNestedZTranscendental base hactive hSderiv D a)
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (zOrder 2)),
       flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (zOrder 1))}:
       Set (CoordinateField Omega a.1.1))=⊤:=by
 have hemb:=elementEmbedding_congr
   (activeNestedZTranscendental base hactive hSderiv D a) a.2
   (by simp [zOrder,flagEvaluation_X_two])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega a.1.1):=
     (elementEmbedding Omega (CoordinateField Omega a.1.1)
       (flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (zOrder 0)))
       (activeNestedZTranscendental base hactive hSderiv D a)).toRingHom.toAlgebra;
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (zOrder 2)),
       flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (zOrder 1))}:Set (CoordinateField Omega a.1.1))=⊤)
 rw [hemb]
 simpa [zOrder,Equiv.swap_apply_def] using flag_generators_z Omega a.1.1 D.lam D.mu
   (D.mu*D.lam) a.2
theorem activeNestedUGenerates (C:RegularComponent Omega G T H):
   letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam)
     uOrder (activeNestedUTranscendental base hactive hSderiv D C)
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (uOrder 2)),
       flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (uOrder 1))}:
       Set (CoordinateField Omega C.1))=⊤:=by
 have hemb:=elementEmbedding_congr
   (activeNestedUTranscendental base hactive hSderiv D C)
   (D.uTranscendental C) (by simp [uOrder,flagEvaluation_X_zero])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (uOrder 0)))
       (activeNestedUTranscendental base hactive hSderiv D C)).toRingHom.toAlgebra;
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (uOrder 2)),
       flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (uOrder 1))}:Set (CoordinateField Omega C.1))=⊤)
 rw [hemb]
 simpa [uOrder] using flag_generators_u Omega C.1 D.lam D.mu
   (D.mu*D.lam) (D.uTranscendental C)
theorem activeNestedVGenerates (C:RegularComponent Omega G T H):
   letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam)
     vOrder (activeNestedVTranscendental base hactive hSderiv D C)
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (vOrder 2)),
       flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (vOrder 1))}:
       Set (CoordinateField Omega C.1))=⊤:=by
 have hemb:=elementEmbedding_congr
   (activeNestedVTranscendental base hactive hSderiv D C)
   (D.allAffineTranscendental C) (by simp [vOrder,flagEvaluation_X_one])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (vOrder 0)))
       (activeNestedVTranscendental base hactive hSderiv D C)).toRingHom.toAlgebra;
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (vOrder 2)),
       flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (vOrder 1))}:Set (CoordinateField Omega C.1))=⊤)
 rw [hemb]
 simpa [vOrder,Equiv.swap_apply_def] using flag_generators_v Omega C.1 D.lam D.mu
   (D.mu*D.lam) (D.allAffineTranscendental C)
end
end ProximityPrize.SubmissionLower.RCN031
end PackedLegacy_A1

/-! Packed from ProximityPrize.SubmissionLower.A0. -/
section PackedLegacy_A0
namespace ProximityPrize.SubmissionLower.RCN029
open scoped Classical BigOperators
open RCN264 RCN002 RCN341 RCN037 RCN038 RCN125 RCN031 RCN106 RCN111 RCN112
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
 (multiplicity:RegularComponent Omega G T H → ℕ)
end
end ProximityPrize.SubmissionLower.RCN029
end PackedLegacy_A0
end Compact_PackedLegacy
