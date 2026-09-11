import ProximityPrize.SubmissionLower.PartF006_02
section Compact_PackedLegacy
section PackedLegacy_C8
namespace ProximityPrize.SubmissionLower.RCN193
open RCN011 RCN021 RCN022 RCN226 RCN191 RCN120
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))

@[simp] theorem planeResidueEquiv_mk
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤)
   (x:PlaneRing K):
   planeResidueEquiv K L order e ht hfinite hgen
       (Ideal.Quotient.mk (relationKernel K L order e ht) x)=
     Ideal.Quotient.mk (localizedRelation K L order e ht hfinite)
       (localizePlane K L order e ht hfinite x):=rfl
theorem maximalIdeal_le_localizedRelation_comap_C
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite) ≤
     (localizedRelation K L order e ht hfinite).comap Polynomial.C:=by
 let C:=Polynomial (RatFunc K)
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let S:=PlaneRing K
 let Sp:=LocalizedPlane K L order e ht hfinite
 let J:=relationKernel K L order e ht
 let JP:=localizedRelation K L order e ht hfinite
 let a:C →+*Rp:=algebraMap C Rp
 let c:C →+*S:=Polynomial.C
 let cL:Rp →+*Sp:=Polynomial.C
 let f:S →+*Sp:=localizePlane K L order e ht hfinite
 have hpmax:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
 letI:p.IsPrime:=hpmax.isPrime
 letI:Algebra C Rp:=inferInstance
 letI:IsLocalization p.primeCompl Rp:=inferInstance
 have hcontract:J.comap c=p:=by
   simpa only [J,c,p] using relationKernel_comap_C K L order e ht
 have hsquare:cL.comp a=f.comp c:=by
   apply DFunLike.ext _ _
   intro x
   change Polynomial.C (a x)=Polynomial.map a (Polynomial.C x)
   rw [Polynomial.map_C]
 rw [←IsLocalization.AtPrime.map_eq_maximalIdeal p Rp,
   ←Ideal.map_le_iff_le_comap]
 calc
   Ideal.map cL (Ideal.map a p)=Ideal.map (cL.comp a) p:=
     Ideal.map_map a cL
   _=Ideal.map (f.comp c) p:=by
     rw [hsquare]
   _=Ideal.map f (Ideal.map c p):=(Ideal.map_map c f).symm
   _ ≤ Ideal.map f J:=Ideal.map_mono
     (Ideal.map_le_iff_le_comap.mpr hcontract.ge)
   _=JP:=rfl
@[reducible] def localizedResidueAlgebra
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Algebra
     (LocalCoefficient K L order e ht hfinite ⧸
       IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite))
     (LocalizedPlane K L order e ht hfinite ⧸
       localizedRelation K L order e ht hfinite):=
 Ideal.Quotient.algebraQuotientOfLEComap
   (maximalIdeal_le_localizedRelation_comap_C K L order e ht hfinite)
noncomputable def coefficientResidueEquiv
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   AdjoinRoot (projectedFactor K L order e ht) ≃+*
     (LocalCoefficient K L order e ht hfinite ⧸
       IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite)):=by
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 letI:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
 change (Polynomial (RatFunc K) ⧸ p) ≃+*
   (Rp ⧸ IsLocalRing.maximalIdeal Rp)
 exact IsLocalization.AtPrime.equivQuotMaximalIdeal p Rp
@[simp] theorem coefficientResidueEquiv_mk
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (x:Polynomial (RatFunc K)):
   coefficientResidueEquiv K L order e ht hfinite
       (AdjoinRoot.mk (projectedFactor K L order e ht) x)=
     Ideal.Quotient.mk
       (IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite))
       (algebraMap (Polynomial (RatFunc K))
         (LocalCoefficient K L order e ht hfinite) x):=rfl
end
end ProximityPrize.SubmissionLower.RCN193
end PackedLegacy_C8

/-! Packed from ProximityPrize.SubmissionLower.M0. -/

/- Library component D7 is loaded from Mathlib.RingTheory.OrderOfVanishing.Basic. -/

/-! Packed from ProximityPrize.SubmissionLower.M2. -/
section PackedLegacy_M2
namespace ProximityPrize.SubmissionLower.RCN196
open scoped Classical BigOperators
open Module
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {R M ι:Type*}
 [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
 [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
private theorem ord_finset_prod
   (a:ι → R) (ha:∀ i,a i≠0):
   Ring.ord R (∏ i,a i)=∑ i,Ring.ord R (a i):=by
 classical
 let s:Finset ι:=Finset.univ
 change Ring.ord R (∏ i∈s,a i)=∑ i∈s,Ring.ord R (a i)
 induction s using Finset.induction_on with
 | empty => simp
 | @insert i s hi ih =>
     rw [Finset.prod_insert hi,Finset.sum_insert hi,
       Ring.ord_mul' (R:=R)
         (mem_nonZeroDivisors_iff_ne_zero.mpr (ha i)),ih]
theorem associated_det_prod_smithRange
   (b:Basis ι R M) (f:M →ₗ[R] M) (hinj:Function.Injective f):
   Associated (LinearMap.det f)
     (∏ i,(LinearMap.range f).smithNormalFormCoeffs b
       (f.finrank_range_of_inj hinj) i):=by
 classical
 let N:Submodule R M:=LinearMap.range f
 let hrank:Module.finrank R N=Module.finrank R M:=
   f.finrank_range_of_inj hinj
 let bM:Basis ι R M:=N.smithNormalFormTopBasis b hrank
 let bN:Basis ι R N:=N.smithNormalFormBotBasis b hrank
 let a:ι → R:=N.smithNormalFormCoeffs b hrank
 let eActual:M ≃ₗ[R] N:=LinearEquiv.ofInjective f hinj
 let eSmith:M ≃ₗ[R] N:=bM.equiv bN (Equiv.refl ι)
 let g:M →ₗ[R] M:=N.subtype.comp eSmith.toLinearMap
 have hmatrix:LinearMap.toMatrix bM bM g=Matrix.diagonal a:=by
   ext i j
   simp only [LinearMap.toMatrix_apply,g,LinearMap.comp_apply,
     LinearEquiv.coe_coe,eSmith,Basis.equiv_apply,Equiv.refl_apply]
   have hsnf:((bN j:N):M)=a j • bM j:=by
     exact N.smithNormalFormBotBasis_def b hrank j
   change bM.repr ((bN j:N):M) i=
     if i=j then a i else 0
   rw [hsnf,map_smul,Basis.repr_self,Finsupp.smul_single]
   by_cases hij:i=j
   · subst j
     simp
   · simp [Finsupp.single_apply,hij]
 have hdetg:LinearMap.det g=∏ i,a i:=by
   calc
     LinearMap.det g=(LinearMap.toMatrix bM bM g).det:=
       (LinearMap.det_toMatrix bM g).symm
     _=(Matrix.diagonal a).det:=by rw [hmatrix]
     _=∏ i,a i:=Matrix.det_diagonal
 have hassoc:Associated (LinearMap.det f) (LinearMap.det g):=by
   have h:=LinearMap.associated_det_comp_equiv N.subtype eActual eSmith
   have heActual:N.subtype.comp eActual.toLinearMap=f:=by
     ext z
     exact LinearEquiv.ofInjective_apply (h:=hinj) f z
   rw [heActual] at h
   exact h
 simpa only [N,hrank,a,hdetg] using hassoc
theorem length_coker_eq_ord_det
   (b:Basis ι R M) (f:M →ₗ[R] M)
   (hinj:Function.Injective f):
   Module.length R (M ⧸ LinearMap.range f)=Ring.ord R (LinearMap.det f):=by
 classical
 let N:Submodule R M:=LinearMap.range f
 let hrank:Module.finrank R N=Module.finrank R M:=
   f.finrank_range_of_inj hinj
 let a:ι → R:=N.smithNormalFormCoeffs b hrank
 have ha:∀ i,a i≠0:=fun i => N.smithNormalFormCoeffs_ne_zero b hrank i
 have hdecomp:Module.length R (M ⧸ N)=
     ∑ i,Module.length R (R ⧸ Ideal.span ({a i}:Set R)):=by
   rw [(N.quotientEquivPiSpan b hrank).length_eq,
     Module.length_pi_of_fintype R]
 have hprod:Ring.ord R (∏ i,a i)=∑ i,Ring.ord R (a i):=
   ord_finset_prod a ha
 have hassoc:Associated (LinearMap.det f) (∏ i,a i):=by
   simpa only [N,hrank,a] using associated_det_prod_smithRange b f hinj
 change Module.length R (M ⧸ N)=_
 calc
   Module.length R (M ⧸ N)=
       ∑ i,Module.length R (R ⧸ Ideal.span ({a i}:Set R)):=hdecomp
   _=∑ i,Ring.ord R (a i):=rfl
   _=Ring.ord R (∏ i,a i):=hprod.symm
   _=Ring.ord R (LinearMap.det f):=
     (Ring.ord_eq_of_associated hassoc).symm
section TwoModules
variable {N:Type*} [AddCommGroup N] [Module R N]
theorem length_coker_eq_ord_toMatrix_det
   (bM:Basis ι R M) (bN:Basis ι R N)
   (f:M →ₗ[R] N) (hinj:Function.Injective f):
   Module.length R (N ⧸ LinearMap.range f)=
     Ring.ord R (LinearMap.toMatrix bM bN f).det:=by
 classical
 let e:N ≃ₗ[R] M:=bN.equiv bM (Equiv.refl ι)
 let g:N →ₗ[R] N:=f.comp e.toLinearMap
 have hginj:Function.Injective g:=hinj.comp e.injective
 have hrange:LinearMap.range g=LinearMap.range f:=by
   change LinearMap.range (f.comp e.toLinearMap)=LinearMap.range f
   rw [LinearMap.range_comp_of_range_eq_top f e.range]
 have hmatrix:LinearMap.toMatrix bN bN g=
     LinearMap.toMatrix bM bN f:=by
   change LinearMap.toMatrix bN bN (f.comp e.toLinearMap)=_
   rw [LinearMap.toMatrix_comp bN bM bN,
     LinearMap.toMatrix_basis_equiv,Matrix.mul_one]
 calc
   Module.length R (N ⧸ LinearMap.range f)=
       Module.length R (N ⧸ LinearMap.range g):=by rw [hrange]
   _=Ring.ord R (LinearMap.det g):=length_coker_eq_ord_det bN g hginj
   _=Ring.ord R (LinearMap.toMatrix bN bN g).det:=by
     rw [LinearMap.det_toMatrix]
   _=Ring.ord R (LinearMap.toMatrix bM bN f).det:=by rw [hmatrix]
theorem sum_multiplicities_le_ord_toMatrix_det_of_surjective
   {J:Type*} [Fintype J]
   (bM:Basis ι R M) (bN:Basis ι R N)
   (f:M →ₗ[R] N) (hinj:Function.Injective f)
   (pieces:J → Type*)
   [∀ j,AddCommGroup (pieces j)] [∀ j,Module R (pieces j)]
   (multiplicity:J → ℕ)
   (hlength:∀ j,(multiplicity j:ℕ∞) ≤ Module.length R (pieces j))
   (project:(N ⧸ LinearMap.range f) →ₗ[R] (∀ j,pieces j))
   (hsurj:Function.Surjective project):
   ((∑ j,multiplicity j:ℕ):ℕ∞) ≤
     Ring.ord R (LinearMap.toMatrix bM bN f).det:=by
 rw [←length_coker_eq_ord_toMatrix_det bM bN f hinj]
 calc
   ((∑ j,multiplicity j:ℕ):ℕ∞)=
       ∑ j,(multiplicity j:ℕ∞):=by simp
   _ ≤ ∑ j,Module.length R (pieces j):=
     Finset.sum_le_sum (fun j _ => hlength j)
   _=Module.length R (∀ j,pieces j):=
     (Module.length_pi_of_fintype R pieces).symm
   _ ≤ Module.length R (N ⧸ LinearMap.range f):=
     Module.length_le_of_surjective project hsurj
end TwoModules
end
end ProximityPrize.SubmissionLower.RCN196
end PackedLegacy_M2

/-! Packed from ProximityPrize.SubmissionLower.CE. -/
section PackedLegacy_CE
namespace ProximityPrize.SubmissionLower.RCN307
noncomputable section
set_option autoImplicit false
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
def intersectionIdeal (P Q:Polynomial R):Ideal (Polynomial R):=
 Ideal.span {P,Q}
structure PrimaryPiecesCertificate
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (multiplicity:J → ℕ) where
 pieces:J → Ideal (Polynomial R)
 coprime:Pairwise fun i j↦IsCoprime (pieces i) (pieces j)
 contains:∀ j,intersectionIdeal P Q ≤ pieces j
 length_le:∀ j,(multiplicity j:ℕ∞) ≤
   Module.length R (Polynomial R ⧸ pieces j)
end
end ProximityPrize.SubmissionLower.RCN307
end PackedLegacy_CE

/-! Packed from ProximityPrize.SubmissionLower.CF. -/
section PackedLegacy_CF
namespace ProximityPrize.SubmissionLower.RCN309
open scoped Classical BigOperators
open Module RCN196 RCN307
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
theorem moduleFinite_quotient_of_monic_mem
   (I:Ideal (Polynomial R)) (M:Polynomial R)
   (hMMonic:M.Monic) (hMmem:M∈I):
   Module.Finite R (Polynomial R ⧸ I):=by
 let hle:Ideal.span {M} ≤ I:=Ideal.span_le.mpr (by simpa)
 let f:(Polynomial R ⧸ Ideal.span {M}) →ₐ[R]
     (Polynomial R ⧸ I):=Ideal.Quotient.factorₐ R hle
 letI:Module.Finite R (Polynomial R ⧸ Ideal.span {M}):=
   hMMonic.finite_quotient
 exact Module.Finite.of_surjective f.toLinearMap
   (Ideal.Quotient.factor_surjective hle)
def rawPiecesMap
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (pieces:J → Ideal (Polynomial R)):
   Polynomial.degreeLT R (m+n) →ₗ[R]
     (∀ j,Polynomial R ⧸ pieces j):=
 LinearMap.pi fun j↦
   ((Submodule.mkQ (pieces j)).restrictScalars R).comp
     (Submodule.subtype (Polynomial.degreeLT R (m+n)))
theorem range_sylvesterMap_le_ker_rawPiecesMap
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (pieces:J → Ideal (Polynomial R))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j):
   LinearMap.range (Polynomial.sylvesterMap P Q hPcap hQcap) ≤
     LinearMap.ker (rawPiecesMap P Q m n pieces):=by
 rintro y ⟨v,rfl⟩
 rw [LinearMap.mem_ker]
 funext j
 apply Ideal.Quotient.eq_zero_iff_mem.mpr
 apply hcontains j
 change P*(v.2:Polynomial R)+Q*(v.1:Polynomial R)∈
   intersectionIdeal P Q
 exact Ideal.add_mem _
   (Ideal.mul_mem_right _ _
     (Ideal.subset_span (Set.mem_insert P {Q})))
   (Ideal.mul_mem_right _ _
     (Ideal.subset_span (Set.mem_insert_of_mem P (Set.mem_singleton Q))))
def cokerToPieces
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (pieces:J → Ideal (Polynomial R))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j):
   (Polynomial.degreeLT R (m+n) ⧸
     LinearMap.range (Polynomial.sylvesterMap P Q hPcap hQcap)) →ₗ[R]
       (∀ j,Polynomial R ⧸ pieces j):=
 (LinearMap.range (Polynomial.sylvesterMap P Q hPcap hQcap)).liftQ
   (rawPiecesMap P Q m n pieces)
   (range_sylvesterMap_le_ker_rawPiecesMap
     P Q m n hPcap hQcap pieces hcontains)
theorem cokerToPieces_surjective_of_modMax
   [IsLocalRing R]
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (pieces:J → Ideal (Polynomial R))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j)
   [Module.Finite R (∀ j,Polynomial R ⧸ pieces j)]
   (hmod:Function.Surjective
     (((IsLocalRing.maximalIdeal R •
         (⊤:Submodule R (∀ j,Polynomial R ⧸ pieces j))).mkQ).comp
       (rawPiecesMap P Q m n pieces))):
   Function.Surjective
     (cokerToPieces P Q m n hPcap hQcap pieces hcontains):=by
 let target:=∀ j,Polynomial R ⧸ pieces j
 let maxTarget:=IsLocalRing.maximalIdeal R •
   (⊤:Submodule R target)
 have hraw:Function.Surjective (rawPiecesMap P Q m n pieces):=by
   apply LinearMap.surjective_of_surjective_comp_mkQ
     (rawPiecesMap P Q m n pieces) (IsLocalRing.maximalIdeal R)
     (IsLocalRing.maximalIdeal_le_jacobson ⊥)
   exact hmod
 intro y
 obtain ⟨v,hv⟩:=hraw y
 refine ⟨Submodule.Quotient.mk v,?_⟩
 change rawPiecesMap P Q m n pieces v=y
 exact hv
end
end ProximityPrize.SubmissionLower.RCN309
end PackedLegacy_CF

/-! Packed from ProximityPrize.SubmissionLower.C9. -/
section PackedLegacy_C9
namespace ProximityPrize.SubmissionLower.RCN197
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
 [IsLocalRing R]
@[reducible] def relationResidueAlgebra
   (J:Ideal (Polynomial R))
   (hcontract:J.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R):
   Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=
 (Ideal.quotientMap J (Polynomial.C:R →+*Polynomial R) (by
   rw [hcontract])).toAlgebra' (fun _ _ => mul_comm _ _)
theorem exists_monic_mem_maximal_relation
   (J:Ideal (Polynomial R)) [J.IsMaximal]
   (hcontract:J.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   (hfinite:
     letI:=relationResidueAlgebra J hcontract
     FiniteDimensional (IsLocalRing.ResidueField R)
       (Polynomial R ⧸ J)):
   ∃ H:Polynomial R,H.Monic∧H∈J:=by
 let k:=IsLocalRing.ResidueField R
 let E:=Polynomial R ⧸ J
 let qR:R →+*k:=Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
 let qB:Polynomial R →+*E:=Ideal.Quotient.mk J
 let aResidue:=relationResidueAlgebra J hcontract
 letI:Algebra k E:=aResidue
 let phi:k →+*E:=algebraMap k E
 letI:FiniteDimensional k E:=hfinite
 let y:E:=qB Polynomial.X
 let hbar:Polynomial k:=minpoly k y
 have hbarMonic:hbar.Monic:=
   minpoly.monic (IsIntegral.of_finite k y)
 have hbarLift:hbar∈Polynomial.lifts qR:=
   Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective hbar
 obtain ⟨H,hmap,hdegree,hHMonic⟩:=
   Polynomial.lifts_and_natDegree_eq_and_monic hbarLift hbarMonic
 have hcomp:(Polynomial.eval₂RingHom phi y).comp
     (Polynomial.mapRingHom qR)=qB:=by
   apply Polynomial.ringHom_ext
   · intro r
     simp only [RingHom.comp_apply,Polynomial.coe_mapRingHom,
       Polynomial.map_C,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
     change Ideal.Quotient.mk J (Polynomial.C r)=qB (Polynomial.C r)
     rfl
   · simp only [RingHom.comp_apply,Polynomial.coe_mapRingHom,
       Polynomial.map_X,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
     rfl
 have hHmem:H∈J:=by
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   change qB H=0
   rw [←hcomp]
   change Polynomial.eval₂ phi y (H.map qR)=0
   rw [hmap]
   change Polynomial.aeval y hbar=0
   exact minpoly.aeval k y
 exact ⟨H,hHMonic,hHmem⟩
end
end ProximityPrize.SubmissionLower.RCN197
end PackedLegacy_C9

/-! Packed from ProximityPrize.SubmissionLower.L9. -/
section PackedLegacy_L9
namespace ProximityPrize.SubmissionLower.RCN192
open RCN011 RCN021 RCN022 RCN226 RCN191 RCN193 RCN120 RCN014 RCN197
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
theorem localizedRelation_comap_C_eq_maximalIdeal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   (localizedRelation K L order e ht hfinite).comap Polynomial.C=
     IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite):=by
 apply le_antisymm
 · apply IsLocalRing.le_maximalIdeal
   apply Ideal.comap_ne_top
   intro htop
   have hunder:=localizedRelation_under K L order e ht hfinite
   have hJne:relationKernel K L order e ht≠⊤:=RingHom.ker_ne_top _
   apply hJne
   rw [←hunder,htop,Ideal.comap_top]
 · exact maximalIdeal_le_localizedRelation_comap_C K L order e ht hfinite
theorem localizedRelationResidue_finite
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   let Rp:=LocalCoefficient K L order e ht hfinite
   let JP:=localizedRelation K L order e ht hfinite
   let hcontract:=localizedRelation_comap_C_eq_maximalIdeal
     K L order e ht hfinite
   let a:=relationResidueAlgebra JP hcontract
   letI:Algebra (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=a
   letI:SMul (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=a.toSMul
   let targetSemiring:Semiring
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=inferInstance
   letI:AddCommMonoid
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=
     targetSemiring.toAddCommMonoid
   letI:Module (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=Algebra.toModule
   FiniteDimensional (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=by
 let F:=RatFunc K
 let q:=projectedFactor K L order e ht
 let J:=relationKernel K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let JP:=localizedRelation K L order e ht hfinite
 letI:Algebra F L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 letI:FiniteDimensional F L:=hfinite
 letI:J.IsMaximal:=relationKernel_isMaximal K L order e ht hfinite hgen
 let a0:=residueAlgebra q J (relationKernel_comap_C K L order e ht)
 letI:Algebra (AdjoinRoot q) (PlaneRing K ⧸ J):=a0
 letI:SMul (AdjoinRoot q) (PlaneRing K ⧸ J):=a0.toSMul
 let quotientSemiring:Semiring (PlaneRing K ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing K ⧸ J):=quotientSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing K ⧸ J):=Algebra.toModule
 let phi:PlaneRing K →ₐ[F] L:={
   toRingHom:=planeEvaluation K L order e ht
   commutes':=fun a => by
     change planeEvaluation K L order e ht
       (Polynomial.C (Polynomial.C a))=algebraMap F L a
     rw [planeEvaluation_C_C]
     rfl}
 have hsurj:Function.Surjective phi:=by
   change Function.Surjective
     (RCN361.planeEval F L
       (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))))
   exact planeEvaluation_surjective_of_finite_generatingPair
     (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))) hgen
 let eqv0:(PlaneRing K ⧸ J) ≃ₐ[F] L:=by
   change (PlaneRing K ⧸ RingHom.ker phi) ≃ₐ[F] L
   exact Ideal.quotientKerAlgEquivOfSurjective hsurj
 letI:Module.Finite F (PlaneRing K ⧸ J):=
   Module.Finite.equiv eqv0.toLinearEquiv.symm
 letI:IsScalarTower F (AdjoinRoot q) (PlaneRing K ⧸ J):=
   IsScalarTower.of_algebraMap_eq fun c => by
     change Ideal.Quotient.mk J (Polynomial.C (Polynomial.C c))=
       Ideal.Quotient.mk J (Polynomial.C (Polynomial.C c))
     rfl
 letI:Module.Finite (AdjoinRoot q) (PlaneRing K ⧸ J):=
   Module.Finite.of_restrictScalars_finite F _ _
 have hcontract:=localizedRelation_comap_C_eq_maximalIdeal
   K L order e ht hfinite
 let a1:=relationResidueAlgebra JP hcontract
 letI:Algebra (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1
 letI:SMul (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1.toSMul
 let targetSemiring:Semiring
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=inferInstance
 letI:AddCommMonoid (LocalizedPlane K L order e ht hfinite ⧸ JP):=
   targetSemiring.toAddCommMonoid
 letI:Module (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=Algebra.toModule
 let e1:=coefficientResidueEquiv K L order e ht hfinite
 let e2:=planeResidueEquiv K L order e ht hfinite hgen
 refine Module.Finite.of_equiv_equiv
   (A₁:=AdjoinRoot q) (B₁:=PlaneRing K ⧸ J)
   (A₂:=IsLocalRing.ResidueField Rp)
   (B₂:=LocalizedPlane K L order e ht hfinite ⧸ JP) e1 e2 ?_
 apply RingHom.ext
 intro x
 obtain ⟨x,rfl⟩:=AdjoinRoot.mk_surjective x
 change Ideal.Quotient.mk JP
     (Polynomial.C (algebraMap (Polynomial (RatFunc K)) Rp x))=
   Ideal.Quotient.mk JP
     (localizePlane K L order e ht hfinite (Polynomial.C x))
 apply congrArg (Ideal.Quotient.mk JP)
 change Polynomial.C (algebraMap (Polynomial (RatFunc K)) Rp x)=
   Polynomial.map (algebraMap (Polynomial (RatFunc K)) Rp) (Polynomial.C x)
 rw [Polynomial.map_C]
theorem localizedRelationResidue_finrank_eq_unlocalized
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   let q:=projectedFactor K L order e ht
   let J:=relationKernel K L order e ht
   let Rp:=LocalCoefficient K L order e ht hfinite
   let JP:=localizedRelation K L order e ht hfinite
   let hcontract:=localizedRelation_comap_C_eq_maximalIdeal
     K L order e ht hfinite
   let a0:=residueAlgebra q J (relationKernel_comap_C K L order e ht)
   letI:Algebra (AdjoinRoot q) (PlaneRing K ⧸ J):=a0
   letI:SMul (AdjoinRoot q) (PlaneRing K ⧸ J):=a0.toSMul
   let sourceSemiring:Semiring (PlaneRing K ⧸ J):=inferInstance
   letI:AddCommMonoid (PlaneRing K ⧸ J):=sourceSemiring.toAddCommMonoid
   letI:Module (AdjoinRoot q) (PlaneRing K ⧸ J):=Algebra.toModule
   let a1:=relationResidueAlgebra JP hcontract
   letI:Algebra (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1
   letI:SMul (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1.toSMul
   let targetSemiring:Semiring
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=inferInstance
   letI:AddCommMonoid
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=targetSemiring.toAddCommMonoid
   letI:Module (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=Algebra.toModule
   Module.finrank (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP)=
     Module.finrank (AdjoinRoot q) (PlaneRing K ⧸ J):=by
 let q:=projectedFactor K L order e ht
 let J:=relationKernel K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let JP:=localizedRelation K L order e ht hfinite
 letI:J.IsMaximal:=relationKernel_isMaximal K L order e ht hfinite hgen
 let a0:=residueAlgebra q J (relationKernel_comap_C K L order e ht)
 letI:Algebra (AdjoinRoot q) (PlaneRing K ⧸ J):=a0
 letI:SMul (AdjoinRoot q) (PlaneRing K ⧸ J):=a0.toSMul
 let sourceSemiring:Semiring (PlaneRing K ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing K ⧸ J):=sourceSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing K ⧸ J):=Algebra.toModule
 have hcontract:=localizedRelation_comap_C_eq_maximalIdeal
   K L order e ht hfinite
 let a1:=relationResidueAlgebra JP hcontract
 letI:Algebra (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1
 letI:SMul (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1.toSMul
 let targetSemiring:Semiring
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=inferInstance
 letI:AddCommMonoid (LocalizedPlane K L order e ht hfinite ⧸ JP):=
   targetSemiring.toAddCommMonoid
 letI:Module (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=Algebra.toModule
 let e1:=coefficientResidueEquiv K L order e ht hfinite
 let e2:=planeResidueEquiv K L order e ht hfinite hgen
 have hcompat:(algebraMap (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP)).comp e1.toRingHom=
     e2.toRingHom.comp (algebraMap (AdjoinRoot q) (PlaneRing K ⧸ J)):=by
   apply RingHom.ext
   intro x
   obtain ⟨x,rfl⟩:=AdjoinRoot.mk_surjective x
   change Ideal.Quotient.mk JP
       (Polynomial.C (algebraMap (Polynomial (RatFunc K)) Rp x))=
     Ideal.Quotient.mk JP
       (localizePlane K L order e ht hfinite (Polynomial.C x))
   apply congrArg (Ideal.Quotient.mk JP)
   change Polynomial.C (algebraMap (Polynomial (RatFunc K)) Rp x)=
     Polynomial.map (algebraMap (Polynomial (RatFunc K)) Rp) (Polynomial.C x)
   rw [Polynomial.map_C]
 exact (Algebra.finrank_eq_of_equiv_equiv e1 e2 hcompat).symm
end
end ProximityPrize.SubmissionLower.RCN192
end PackedLegacy_L9

/-! Packed from ProximityPrize.SubmissionLower.FP. -/
section PackedLegacy_FP
namespace ProximityPrize.SubmissionLower.RCN236
open RCN014 RCN225 RCN307
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
 {J:Type*} [Fintype J]
noncomputable def primaryPiecesCertificateOfMembershipWeighted
   [IsLocalRing R]
   (surface tail:Polynomial R)
   [hSurfacePrime:(Ideal.span {surface}).IsPrime]
   (relation:J → Ideal (Polynomial R))
   (relationBar:J → Ideal (SurfaceQuotient surface))
   [∀ j,(relationBar j).IsMaximal]
   [IsNoetherianRing (SurfaceQuotient surface)]
   (hrelationBar:∀ j,relationBar j=
     Ideal.map (Ideal.Quotient.mk (Ideal.span {surface})) (relation j))
   (hrelationBarNe:∀ j,relationBar j≠⊥)
   [∀ j,IsLocalHom
     (algebraMap R (Localization.AtPrime (relationBar j)))]
   [∀ j,FiniteDimensional (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime (relationBar j)))]
   (mu:J → ℕ)
   (htail:∀ j,tail∈Ideal.span {surface} ⊔ relation j^mu j)
   (hcoprime:Pairwise fun i j↦IsCoprime (relation i) (relation j)):
   PrimaryPiecesCertificate surface tail (fun j↦
     mu j*Module.finrank (IsLocalRing.ResidueField R)
       (IsLocalRing.ResidueField (Localization.AtPrime (relationBar j)))) where
 pieces j:=mappedPrimaryPiece (RingHom.id (Polynomial R)) relation
   surface mu j
 coprime:=mappedPrimaryPiece_pairwise_coprime
   (RingHom.id (Polynomial R)) relation hcoprime surface mu
 contains j:=by
   apply span_pair_le_mappedPrimaryPiece
     (RingHom.id (Polynomial R)) relation surface tail mu j
   simpa only [mappedPrimaryPiece,Ideal.map_id] using htail j
 length_le j:=by
   have hmap:Ideal.map (RingHom.id (Polynomial R)) (relation j)=relation j:=
     Ideal.map_id (relation j)
   have hbound:=
     exponent_mul_residueDegree_le_length_span_surface_sup_relation_pow
       (R:=R) surface (relation j) (relationBar j)
         (hrelationBar j) (hrelationBarNe j) (mu j)
   change ((mu j*Module.finrank (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime (relationBar j))):ℕ):ℕ∞) ≤
       Module.length R (Polynomial R ⧸ (Ideal.span {surface} ⊔
         Ideal.map (RingHom.id (Polynomial R)) (relation j)^mu j))
   rw [hmap]
   exact hbound
end
end ProximityPrize.SubmissionLower.RCN236
end PackedLegacy_FP

/-! Packed from ProximityPrize.SubmissionLower.C3. -/
section PackedLegacy_C3
namespace ProximityPrize.SubmissionLower.RCN107
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN022 RCN264 RCN125 RCN093 RCN120 RCN102 RCN106 RCN192 RCN197 RCN236 RCN307 RCN225 RCN191
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
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
abbrev indexedFiberSurface
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega):Polynomial (FiberCoefficient q hq):=
 fiberLocalizePlane q hq surface
abbrev indexedFiberTail
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (tail:PlaneRing Omega):Polynomial (FiberCoefficient q hq):=
 fiberLocalizePlane q hq tail
include hfinite hgen in
theorem indexedFiberRelationBar_isMaximal
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (hsurface:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     surface∈relationKernel Omega (CoordinateField Omega (component a.1).1) order
       (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal:=by
 let J:=indexedFiberRelation component lam mu nu order ht q hq a
 let quotientMap:=Ideal.Quotient.mk
   (Ideal.span {indexedFiberSurface q hq surface})
 letI:J.IsMaximal:=indexedFiberRelation_isMaximal
   component lam mu nu order ht hfinite hgen q hq a
 apply Ideal.IsMaximal.map_of_surjective_of_ker_le
   (f:=quotientMap) Ideal.Quotient.mk_surjective
 rw [Ideal.mk_ker,Ideal.span_le]
 intro x hx
 rw [Set.mem_singleton_iff] at hx
 subst x
 exact Ideal.mem_map_of_mem (fiberLocalizePlane q hq) (hsurface a)
theorem indexedFiberRelationBar_ne_bot
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface tail:PlaneRing Omega)
   (htailRoot:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     tail∈relationKernel Omega (CoordinateField Omega (component a.1).1) order
       (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   (hproper:indexedFiberTail q hq tail∉
     Ideal.span {indexedFiberSurface q hq surface})
   (a:IndexedFactorFiber component lam mu nu order ht q):
   indexedFiberRelationBar component lam mu nu order ht q hq surface a≠⊥:=by
 let quotientMap:Polynomial (FiberCoefficient q hq) →+*
     SurfaceQuotient (indexedFiberSurface q hq surface):=
   Ideal.Quotient.mk (Ideal.span {indexedFiberSurface q hq surface})
 intro hbot
 have hmem:quotientMap (indexedFiberTail q hq tail)∈
     indexedFiberRelationBar component lam mu nu order ht q hq surface a:=
   Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (htailRoot a))
 have hzero:quotientMap (indexedFiberTail q hq tail)=0:=by
   apply Ideal.mem_bot.mp
   rw [←hbot]
   exact hmem
 exact hproper (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
include hfinite in
theorem indexedFiberRelation_comap_C_eq_maximalIdeal
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (indexedFiberRelation component lam mu nu order ht q hq a).comap
       Polynomial.C=IsLocalRing.maximalIdeal (FiberCoefficient q hq):=by
 cases a with
 | mk a hqeq =>
   subst q
   exact localizedRelation_comap_C_eq_maximalIdeal Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
include hfinite hgen in
theorem exists_monic_mem_indexedFiberRelation
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   ∃ M:Polynomial (FiberCoefficient q hq),M.Monic∧
     M∈indexedFiberRelation component lam mu nu order ht q hq a:=by
 cases a with
 | mk a hqeq =>
   subst q
   let J:=localizedRelation Omega (CoordinateField Omega (component a).1) order
     (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
   letI:J.IsMaximal:=localizedRelation_isMaximal Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a)
         (hfinite a) (hgen a)
   have hcontract:=localizedRelation_comap_C_eq_maximalIdeal Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
   have hfin:=localizedRelationResidue_finite Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a)
         (hfinite a) (hgen a)
   exact exists_monic_mem_maximal_relation J hcontract hfin
noncomputable def indexedWeightedFiberPrimaryPieces
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface tail:PlaneRing Omega)
   [hSurfacePrime:(Ideal.span {indexedFiberSurface q hq surface}).IsPrime]
   [hbarMax:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal]
   (hbarne:∀ a,indexedFiberRelationBar component lam mu nu order ht
     q hq surface a≠⊥)
   (multiplicity:IndexedFactorFiber component lam mu nu order ht q → ℕ)
   (htail:∀ a,indexedFiberTail q hq tail∈
     Ideal.span {indexedFiberSurface q hq surface} ⊔
       indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a)
   [hlocal:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]
   [hresfinite:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     FiniteDimensional (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]:
   PrimaryPiecesCertificate (indexedFiberSurface q hq surface)
     (indexedFiberTail q hq tail) (fun a => multiplicity a*
       Module.finrank (IsLocalRing.ResidueField (FiberCoefficient q hq))
         (IsLocalRing.ResidueField (Localization.AtPrime
           (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))):=by
 exact primaryPiecesCertificateOfMembershipWeighted
   (indexedFiberSurface q hq surface) (indexedFiberTail q hq tail)
   (indexedFiberRelation component lam mu nu order ht q hq)
   (indexedFiberRelationBar component lam mu nu order ht q hq surface)
   (fun _ => rfl) hbarne multiplicity htail
   (indexedFiberRelation_pairwise_coprime component hcomponent lam mu nu order
     ht hfinite hgen q hq)
end
end ProximityPrize.SubmissionLower.RCN107
end PackedLegacy_C3

/-! Packed from ProximityPrize.SubmissionLower.I6. -/
section PackedLegacy_I6
namespace ProximityPrize.SubmissionLower.RCN073
open RCN324
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {K R:Type} [Field K] [CommRing R] [IsDomain R]
 [Algebra K R] [IsDiscreteValuationRing R]
private theorem derivation_preserves_char_pow
   (D:Derivation K R R) (pi:R) (p:ℕ) [CharP R p]
   (_hp:1 ≤ p) (f:R) (hf:pi^p∣f):pi^p∣D f:=by
 obtain ⟨u,rfl⟩:=hf
 rw [D.leibniz,Derivation.leibniz_pow]
 simp only [nsmul_eq_mul,smul_eq_mul,CharP.cast_eq_zero R p,zero_mul,
   mul_zero,add_zero]
 exact ⟨D u,rfl⟩
private theorem recurrence_preserves_dvd
   (D:Derivation K R R) (H DH:R) (c:ℕ → R) (N:ℕ → R)
   (hrec:∀ j,N (j+1)=H*D (N j)-c j*N j*DH)
   (a:R) (j:ℕ) (hN:a∣N j) (hDN:a∣D (N j)):
   a∣N (j+1):=by
 obtain ⟨u,hu⟩:=hN
 obtain ⟨v,hv⟩:=hDN
 refine ⟨H*v-c j*u*DH,?_⟩
 rw [hrec j,hv,hu]
 ring
private theorem tangent_chain
   (D:Derivation K R R) (H DH:R) (c:ℕ → R) (N:ℕ → R)
   (hrec:∀ j,N (j+1)=H*D (N j)-c j*N j*DH)
   (pi a:R) (htangent:D pi=pi*a)
   (hN0:pi∣N 0):∀ j,pi∣N j:=by
 intro j
 induction j with
 | zero => exact hN0
 | succ j ih =>
     apply recurrence_preserves_dvd D H DH c N hrec pi j ih
     simpa only [pow_one] using
       tangent_preserves_divisibility D pi a 1 (by simp) htangent
         (N j) (by simpa only [pow_one] using ih)
private theorem char_pow_chain
   (D:Derivation K R R) (H DH:R) (c:ℕ → R) (N:ℕ → R)
   (hrec:∀ j,N (j+1)=H*D (N j)-c j*N j*DH)
   (pi:R) (p:ℕ) [CharP R p] (hp:1 ≤ p)
   (hN0:pi^p∣N 0):∀ j,pi^p∣N j:=by
 intro j
 induction j with
 | zero => exact hN0
 | succ j ih =>
     apply recurrence_preserves_dvd D H DH c N hrec (pi^p) j ih
     exact derivation_preserves_char_pow D pi p hp (N j) ih
private theorem addVal_derivation_eq_pred
   (D:Derivation K R R) (pi:R) (hpi:Irreducible pi)
   (htrans:IsUnit (D pi)) (p k:ℕ) [CharP R p]
   (hp:p.Prime) (hkpos:1 ≤ k) (hkp:k < p)
   (x:R) (u:Rˣ) (hx:x=(u:R)*pi^k):
   IsDiscreteValuationRing.addVal R (D x)=k-1:=by
 have h:=addVal_iterate_eq_sub_of_transverse D pi (u:R) k 1 p hp hkp
   hkpos hpi u.isUnit htrans
 rw [hx,mul_comm]
 simpa using h
private theorem transverse_recurrence_step
   (D:Derivation K R R) (H DH c x next pi:R)
   (hrec:next=H*D x-c*x*DH)
   (hH:IsUnit H) (hpi:Irreducible pi) (htrans:IsUnit (D pi))
   (p k:ℕ) [CharP R p] (hp:p.Prime) (hkpos:1 ≤ k) (hkp:k < p)
   (u:Rˣ) (hx:x=(u:R)*pi^k):
   IsDiscreteValuationRing.addVal R next=k-1:=by
 let v:=IsDiscreteValuationRing.addVal R
 have hDx:v (D x)=k-1:=
   addVal_derivation_eq_pred D pi hpi htrans p k hp hkpos hkp x u hx
 have hxv:v x=k:=IsDiscreteValuationRing.addVal_def x u hpi k hx
 have hfirst:v (H*D x)=k-1:=by
   rw [IsDiscreteValuationRing.addVal_mul,
     IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hH,zero_add,hDx]
 have hsecond:k ≤ v (c*x*DH):=by
   rw [IsDiscreteValuationRing.addVal_mul,
     IsDiscreteValuationRing.addVal_mul,hxv]
   exact le_add_right (le_add_left (le_refl (k:ℕ∞)))
 have hlt:v (H*D x) < v (c*x*DH):=by
   rw [hfirst]
   exact (ENat.coe_lt_coe.mpr (Nat.pred_lt (Nat.ne_zero_of_lt hkpos))).trans_le hsecond
 rw [hrec,v.map_sub_eq_of_lt_left hlt,hfirst]
theorem recurrence_unit_or_persistent
   (D:Derivation K R R) (H DH:R) (c:ℕ → R) (N:ℕ → R)
   (p:ℕ) [CharP R p] (hp:p.Prime)
   (hrec:∀ j,N (j+1)=H*D (N j)-c j*N j*DH)
   (hH:IsUnit H) (hN0ne:N 0≠0) (hN0nonunit:¬ IsUnit (N 0)):
   let mu:=(IsDiscreteValuationRing.addVal R (N 0)).toNat
   1 ≤ mu∧
     ((∃ delay,1 ≤ delay∧delay ≤ mu∧IsUnit (N delay))∨
       (∀ delay,¬ IsUnit (N delay))):=by
 classical
 let v:=IsDiscreteValuationRing.addVal R
 obtain ⟨pi,hpi⟩:=IsDiscreteValuationRing.exists_irreducible R
 obtain ⟨mu,u,hN0⟩:=
   IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hN0ne hpi
 have hv0:v (N 0)=mu:=IsDiscreteValuationRing.addVal_def (N 0) u hpi mu hN0
 have hmuDef:(v (N 0)).toNat=mu:=by rw [hv0];simp
 have hmuPos:1 ≤ mu:=by
   by_contra h
   have hz:mu=0:=Nat.eq_zero_of_not_pos h
   apply hN0nonunit
   apply IsDiscreteValuationRing.addVal_eq_zero_iff.mp
   change v (N 0)=0
   rw [hv0,hz]
   simp
 rw [hmuDef]
 refine ⟨hmuPos,?_⟩
 letI:Decidable (IsUnit (D pi)):=Classical.propDecidable _
 by_cases htrans:IsUnit (D pi)
 · by_cases hmup:mu < p
   · left
     refine ⟨mu,hmuPos,le_rfl,?_⟩
     have horders:∀ j ≤ mu,v (N j)=mu-j:=by
       intro j hj
       induction j with
       | zero => simpa using hv0
       | succ j ih =>
           have hjlt:j < mu:=by omega
           have hord:=ih hjlt.le
           have hNjNe:N j≠0:=by
             intro hz
             rw [hz,IsDiscreteValuationRing.addVal_zero] at hord
             exact ENat.top_ne_coe (mu-j) hord
           obtain ⟨k,uj,hNj⟩:=
             IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hNjNe hpi
           have hkv:v (N j)=k:=
             IsDiscreteValuationRing.addVal_def (N j) uj hpi k hNj
           have hk:k=mu-j:=by
             exact ENat.coe_inj.mp (hkv.symm.trans hord)
           have hkpos:1 ≤ k:=by omega
           have hkp:k < p:=by omega
           have hstep:=transverse_recurrence_step D H DH (c j) (N j)
             (N (j+1)) pi (hrec j) hH hpi htrans p k hp hkpos hkp uj hNj
           rw [hstep,hk]
           exact_mod_cast (show mu-j-1=mu-(j+1) by omega)
     exact IsDiscreteValuationRing.addVal_eq_zero_iff.mp (by
       simpa using horders mu le_rfl)
   · right
     have hpLe:p ≤ mu:=Nat.le_of_not_gt hmup
     have hpPos:1 ≤ p:=hp.one_le
     have hpow:pi^p∣N 0:=by
       rw [hN0]
       refine ⟨(u:R)*pi^(mu-p),?_⟩
       have hpowEq:pi^mu=pi^p*pi^(mu-p):=by
         rw [←pow_add,Nat.add_sub_of_le hpLe]
       rw [hpowEq]
       ring
     have hall:=char_pow_chain D H DH c N hrec pi p hpPos hpow
     intro j hunit
     apply hpi.not_isUnit
     apply isUnit_of_dvd_one
     exact (dvd_pow_self pi (Nat.ne_of_gt hpPos)).trans
       ((hall j).trans (isUnit_iff_dvd_one.mp hunit))
 · right
   have hDmem:D pi∈IsLocalRing.maximalIdeal R:=
     (IsLocalRing.mem_maximalIdeal (D pi)).2 htrans
   obtain ⟨a,ha⟩:∃ a,D pi=pi*a:=by
     have hmax:=(IsDiscreteValuationRing.irreducible_iff_uniformizer pi).mp hpi
     rw [hmax,Ideal.mem_span_singleton'] at hDmem
     obtain ⟨a,ha⟩:=hDmem
     exact ⟨a,by simpa [mul_comm] using ha.symm⟩
   have hpiDvd:pi∣N 0:=by
     rw [hN0]
     refine ⟨(u:R)*pi^(mu-1),?_⟩
     have hpowEq:pi^mu=pi*pi^(mu-1):=by
       calc
         pi^mu=pi^(1+(mu-1)):=by
           rw [Nat.add_sub_of_le hmuPos]
         _=pi^1*pi^(mu-1):=pow_add pi 1 (mu-1)
         _=pi*pi^(mu-1):=by rw [pow_one]
     rw [hpowEq]
     ring
   have hall:=tangent_chain D H DH c N hrec pi a ha hpiDvd
   intro j hunit
   exact hpi.not_isUnit (isUnit_of_dvd_one
     ((hall j).trans (isUnit_iff_dvd_one.mp hunit)))
end
end ProximityPrize.SubmissionLower.RCN073
end PackedLegacy_I6

/-! Packed from ProximityPrize.SubmissionLower.O2. -/
section PackedLegacy_O2
namespace ProximityPrize.SubmissionLower.RCN270
open IsLocalRing Ideal
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
variable {A:Type*} [CommRing A] [IsDomain A] [IsRegularLocalRing A]
private theorem exists_pair_generator_of_not_mem_sq
   (f:A) (hf:f∈maximalIdeal A) (hf2:f∉maximalIdeal A^2)
   (hdim:ringKrullDim A=2):
   ∃ g∈maximalIdeal A,maximalIdeal A=Ideal.span {f,g}:=by
 classical
 let m:=maximalIdeal A
 have hfg:m.FG:=m.fg_of_isNoetherianRing
 have hrank:m.spanFinrank=2:=by
   have hreg:=(isRegularLocalRing_iff A).mp (inferInstance:IsRegularLocalRing A)
   rw [hdim] at hreg
   exact_mod_cast hreg
 have hcard:m.generators.ncard=2:=by
   rw [Submodule.FG.generators_ncard hfg,hrank]
 obtain ⟨a,b,hab,hgen⟩:=Set.ncard_eq_two.mp hcard
 have hspan:Ideal.span {a,b}=m:=by
   simpa [hgen] using m.span_generators
 have ha:a∈m:=Submodule.FG.generators_mem m (by simp [hgen])
 have hb:b∈m:=Submodule.FG.generators_mem m (by simp [hgen])
 have hfm:f∈m:=by simpa [m] using hf
 have hfspan:f∈Ideal.span ({a,b}:Set A):=by rwa [hspan]
 obtain ⟨r,s,hrs⟩:=Ideal.mem_span_pair.mp hfspan
 have hunit:IsUnit r∨IsUnit s:=by
   letI:Decidable (IsUnit r):=Classical.propDecidable _
   letI:Decidable (IsUnit s):=Classical.propDecidable _
   by_cases hr:IsUnit r
   · exact Or.inl hr
   by_cases hs:IsUnit s
   · exact Or.inr hs
   · exfalso
     have hrm:r∈m:=(IsLocalRing.mem_maximalIdeal r).mpr hr
     have hsm:s∈m:=(IsLocalRing.mem_maximalIdeal s).mpr hs
     apply hf2
     rw [pow_two, ←hrs]
     exact (m*m).add_mem (Ideal.mul_mem_mul hrm ha) (Ideal.mul_mem_mul hsm hb)
 rcases hunit with hr | hs
 · refine ⟨b,hb,le_antisymm ?_ ?_⟩
   · change m ≤ Ideal.span {f,b}
     rw [←hspan]
     apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rw [hx]
       obtain ⟨u,rfl⟩:=hr
       have hfmem:f∈Ideal.span ({f,b}:Set A):=
         Ideal.subset_span (by simp)
       have hbmem:b∈Ideal.span ({f,b}:Set A):=
         Ideal.subset_span (by simp)
       have heq:a=(↑(u⁻¹):A)*f-(↑(u⁻¹):A)*s*b:=by
         rw [←hrs]
         have hu:(↑(u⁻¹):A)*(↑u:A)=1:=Units.inv_mul u
         calc
           a=((↑(u⁻¹):A)*(↑u:A))*a:=by rw [hu,one_mul]
           _=(↑(u⁻¹):A)*((↑u:A)*a+s*b)-
               (↑(u⁻¹):A)*s*b:=by ring
       rw [heq]
       exact (Ideal.span ({f,b}:Set A)).sub_mem
         ((Ideal.span ({f,b}:Set A)).mul_mem_left _ hfmem)
         ((Ideal.span ({f,b}:Set A)).mul_mem_left _ hbmem)
     · rw [hx]
       exact Ideal.subset_span (by simp)
   · apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rwa [hx]
     · rwa [hx]
 · refine ⟨a,ha,le_antisymm ?_ ?_⟩
   · change m ≤ Ideal.span {f,a}
     rw [←hspan]
     apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rw [hx]
       exact Ideal.subset_span (by simp)
     · rw [hx]
       obtain ⟨u,rfl⟩:=hs
       have hfmem:f∈Ideal.span ({f,a}:Set A):=
         Ideal.subset_span (by simp)
       have hamem:a∈Ideal.span ({f,a}:Set A):=
         Ideal.subset_span (by simp)
       have heq:b=(↑(u⁻¹):A)*f-(↑(u⁻¹):A)*r*a:=by
         rw [←hrs]
         have hu:(↑(u⁻¹):A)*(↑u:A)=1:=Units.inv_mul u
         calc
           b=((↑(u⁻¹):A)*(↑u:A))*b:=by rw [hu,one_mul]
           _=(↑(u⁻¹):A)*(r*a+(↑u:A)*b)-
               (↑(u⁻¹):A)*r*a:=by ring
       rw [heq]
       exact (Ideal.span ({f,a}:Set A)).sub_mem
         ((Ideal.span ({f,a}:Set A)).mul_mem_left _ hfmem)
         ((Ideal.span ({f,a}:Set A)).mul_mem_left _ hamem)
   · apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rwa [hx]
     · rwa [hx]
theorem quotient_span_singleton_isRegularLocalRing
   (f:A) (hf:f∈maximalIdeal A) (hf2:f∉maximalIdeal A^2)
   (hdim:ringKrullDim A=2)
   (hdimQ:ringKrullDim (A ⧸ Ideal.span {f})=1):
   IsRegularLocalRing (A ⧸ Ideal.span {f}):=by
 obtain ⟨g,hg,hmg⟩:=exists_pair_generator_of_not_mem_sq f hf hf2 hdim
 have hspanProper:Ideal.span ({f}:Set A)≠⊤:=by
   apply ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
   exact Ideal.span_le.2 (by simpa using hf)
 letI:Nontrivial (A ⧸ Ideal.span {f}):=
   Ideal.Quotient.nontrivial_iff.mpr hspanProper
 letI:IsLocalRing (A ⧸ Ideal.span {f}):=
   IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f}))
     Ideal.Quotient.mk_surjective
 apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
 rw [hdimQ]
 have hmax:maximalIdeal (A ⧸ Ideal.span {f})=
     Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g}:=by
   rw [←IsLocalRing.map_maximalIdeal_of_surjective
     (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective,hmg,
     Ideal.map_span]
   simp [Set.image_insert_eq,Set.image_singleton]
 rw [hmax]
 have hle:(Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g}:
     Ideal (A ⧸ Ideal.span {f})).spanFinrank ≤ 1:=by
   exact (Submodule.spanFinrank_span_le_ncard_of_finite
     (Set.finite_singleton _)).trans (by simp)
 exact_mod_cast hle
end ProximityPrize.SubmissionLower.RCN270
end PackedLegacy_O2

/-! Packed from ProximityPrize.SubmissionLower.L5. -/
section PackedLegacy_L5
namespace ProximityPrize.SubmissionLower.RCN186
variable {A:Type*} [CommRing A]
noncomputable def quotientPrime (I p:Ideal A):Ideal (A ⧸ I):=
 p.map (Ideal.Quotient.mk I)
theorem quotientPrime_isPrime (I p:Ideal A) [p.IsPrime]
   (hIp:I ≤ p):(quotientPrime I p).IsPrime:=by
 apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
 simpa only [Ideal.mk_ker] using hIp
noncomputable abbrev LocalizedQuotient (I p:Ideal A) [p.IsPrime]
   (hIp:I ≤ p):Type _:=
 @Localization.AtPrime (A ⧸ I) _ (quotientPrime I p)
   (quotientPrime_isPrime I p hIp)
theorem quotientPrime_comap_quotientMk (I p:Ideal A) [p.IsPrime]
   (hIp:I ≤ p):
   (quotientPrime I p).comap (Ideal.Quotient.mk I)=p:=by
 rw [quotientPrime,Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
 change p ⊔ RingHom.ker (Ideal.Quotient.mk I)=p
 rw [Ideal.mk_ker,sup_eq_left]
 exact hIp
theorem quotientMk_map_primeCompl (I p:Ideal A) [p.IsPrime]
   [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   Submonoid.map (Ideal.Quotient.mk I) p.primeCompl=
     (quotientPrime I p).primeCompl:=by
 apply SetLike.ext
 intro x
 constructor
 · rintro ⟨s,hs,rfl⟩
   intro hmem
   exact hs ((quotientPrime_comap_quotientMk I p hIp).symm ▸ hmem)
 · intro hx
   obtain ⟨s,rfl⟩:=Ideal.Quotient.mk_surjective x
   refine ⟨s,?_,rfl⟩
   intro hs
   apply hx
   change s∈(quotientPrime I p).comap (Ideal.Quotient.mk I)
   rw [quotientPrime_comap_quotientMk I p hIp]
   exact hs
noncomputable def ambientToLocalizedQuotient
   (I p:Ideal A) [p.IsPrime] [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   Localization.AtPrime p →+*LocalizedQuotient I p hIp:=by
 have hM:=quotientMk_map_primeCompl I p hIp
 letI:IsLocalization (Submonoid.map (Ideal.Quotient.mk I) p.primeCompl)
     (LocalizedQuotient I p hIp):=hM.symm ▸ inferInstance
 exact IsLocalization.map (LocalizedQuotient I p hIp) (Ideal.Quotient.mk I)
   p.primeCompl.le_comap_map
theorem ambientToLocalizedQuotient_surjective
   (I p:Ideal A) [p.IsPrime] [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   Function.Surjective (ambientToLocalizedQuotient I p hIp):=by
 have hM:=quotientMk_map_primeCompl I p hIp
 letI:IsLocalization (Submonoid.map (Ideal.Quotient.mk I) p.primeCompl)
     (LocalizedQuotient I p hIp):=hM.symm ▸ inferInstance
 simpa only [ambientToLocalizedQuotient] using
   (IsLocalization.map_surjective_of_surjective p.primeCompl (Localization.AtPrime p)
     (LocalizedQuotient I p hIp) Ideal.Quotient.mk_surjective)
theorem ambientToLocalizedQuotient_ker
   (I p:Ideal A) [p.IsPrime] [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   RingHom.ker (ambientToLocalizedQuotient I p hIp)=
     I.map (algebraMap A (Localization.AtPrime p)):=by
 have hM:=quotientMk_map_primeCompl I p hIp
 have hk:=IsLocalization.ker_map (S:=Localization.AtPrime p)
   (LocalizedQuotient I p hIp) (Ideal.Quotient.mk I) hM
 let canonicalMap:Localization.AtPrime p →+*LocalizedQuotient I p hIp:=
   IsLocalization.map (LocalizedQuotient I p hIp) (Ideal.Quotient.mk I)
     (hM.symm ▸ p.primeCompl.le_comap_map)
 have hmaps:ambientToLocalizedQuotient I p hIp=canonicalMap:=by
   apply IsLocalization.ringHom_ext p.primeCompl
   simp only [ambientToLocalizedQuotient,canonicalMap,IsLocalization.map_comp]
 rw [hmaps]
 change RingHom.ker canonicalMap=_
 calc
   RingHom.ker canonicalMap=RingHom.ker
       (IsLocalization.map (LocalizedQuotient I p hIp) (Ideal.Quotient.mk I)
         (hM.symm ▸ p.primeCompl.le_comap_map)):=by
     congr 1
   _=I.map (algebraMap A (Localization.AtPrime p)):=by
     simpa only [Ideal.mk_ker] using hk
noncomputable def quotientAmbientEquivLocalizedQuotient
   (I p:Ideal A) [p.IsPrime] [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))) ≃+*
     LocalizedQuotient I p hIp:=
 (Ideal.quotEquivOfEq (ambientToLocalizedQuotient_ker I p hIp).symm).trans
   (RingHom.quotientKerEquivOfSurjective
     (ambientToLocalizedQuotient_surjective I p hIp))
end ProximityPrize.SubmissionLower.RCN186
end PackedLegacy_L5

/-! Packed from ProximityPrize.SubmissionLower.I8. -/
section PackedLegacy_I8
namespace ProximityPrize.SubmissionLower.RCN078
def DualNumber (R:Type*):=R × R
namespace DualNumber
variable {K R:Type*}
instance [Zero R]:Zero (DualNumber R):=inferInstanceAs (Zero (R × R))
instance [Add R]:Add (DualNumber R):=inferInstanceAs (Add (R × R))
instance [Neg R]:Neg (DualNumber R):=inferInstanceAs (Neg (R × R))
instance [Sub R]:Sub (DualNumber R):=inferInstanceAs (Sub (R × R))
instance [AddCommMonoid R]:AddCommMonoid (DualNumber R):=
 inferInstanceAs (AddCommMonoid (R × R))
instance [AddCommGroup R]:AddCommGroup (DualNumber R):=
 inferInstanceAs (AddCommGroup (R × R))
instance [SMul K R]:SMul K (DualNumber R):=inferInstanceAs (SMul K (R × R))
instance {L:Type*} [SMul L K] [SMul L R] [SMul K R] [IsScalarTower L K R]:
   IsScalarTower L K (DualNumber R):=
 inferInstanceAs (IsScalarTower L K (R × R))
instance [Semiring K] [AddCommMonoid R] [Module K R]:Module K (DualNumber R):=
 inferInstanceAs (Module K (R × R))
instance [One R] [Zero R]:One (DualNumber R):=⟨(1,0)⟩
instance [Mul R] [Add R]:Mul (DualNumber R):=
 ⟨fun x y => (x.1*y.1,x.1*y.2+x.2*y.1)⟩
@[ext]
theorem ext {x y:DualNumber R} (h₁:x.1=y.1) (h₂:x.2=y.2):x=y:=
 Prod.ext h₁ h₂
@[simp] theorem fst_zero [Zero R]:(0:DualNumber R).1=0:=rfl
@[simp] theorem snd_zero [Zero R]:(0:DualNumber R).2=0:=rfl
@[simp] theorem fst_add [Add R] (x y:DualNumber R):(x+y).1=x.1+y.1:=rfl
@[simp] theorem snd_add [Add R] (x y:DualNumber R):(x+y).2=x.2+y.2:=rfl
@[simp] theorem fst_one [One R] [Zero R]:(1:DualNumber R).1=1:=rfl
@[simp] theorem snd_one [One R] [Zero R]:(1:DualNumber R).2=0:=rfl
@[simp] theorem fst_mul [Mul R] [Add R] (x y:DualNumber R):
   (x*y).1=x.1*y.1:=rfl
@[simp] theorem snd_mul [Mul R] [Add R] (x y:DualNumber R):
   (x*y).2=x.1*y.2+x.2*y.1:=rfl
instance [CommRing R]:CommRing (DualNumber R) where
 mul_assoc x y z:=by ext <;> simp [mul_assoc,mul_add,add_mul];ring
 one_mul x:=by ext <;> simp
 mul_one x:=by ext <;> simp
 left_distrib x y z:=by ext <;> simp [mul_add];ring
 right_distrib x y z:=by ext <;> simp [add_mul];ring
 zero_mul x:=by ext <;> simp
 mul_zero x:=by ext <;> simp
 mul_comm x y:=by ext <;> simp [mul_comm,add_comm]
def inlRingHom [CommRing R]:R →+*DualNumber R where
 toFun r:=(r,0)
 map_one':=rfl
 map_mul' _ _:=by ext <;> simp
 map_zero':=rfl
 map_add' _ _:=by ext <;> simp
instance [CommRing K] [CommRing R] [Algebra K R]:Algebra K (DualNumber R) where
 algebraMap:=inlRingHom.comp (algebraMap K R)
 commutes' k x:=by ext <;> simp [mul_comm]
 smul_def' k x:=by
   apply Prod.ext
   · change k • x.1=algebraMap K R k*x.1
     exact Algebra.smul_def k x.1
   · change k • x.2=algebraMap K R k*x.2+0*x.1
     simp [Algebra.smul_def]
@[simp]
theorem algebraMap_apply [CommRing K] [CommRing R] [Algebra K R] (k:K):
   algebraMap K (DualNumber R) k=(algebraMap K R k,0):=rfl
def fstHom [CommRing K] [CommRing R] [Algebra K R]:DualNumber R →ₐ[K] R where
 toFun x:=x.1
 map_one':=rfl
 map_mul' _ _:=rfl
 map_zero':=rfl
 map_add' _ _:=rfl
 commutes' _:=rfl
def sndHom [CommRing R]:DualNumber R →ₗ[R] R where
 toFun x:=x.2
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
theorem isUnit_of_isUnit_fst [CommRing R] {x:DualNumber R} (hx:IsUnit x.1):
   IsUnit x:=by
 rcases x with ⟨a,b⟩
 rcases hx with ⟨u,hu⟩
 change (u:R)=a at hu
 subst a
 refine ⟨{
   val:=((u:R),b)
   inv:=((↑u⁻¹:R), -((↑u⁻¹:R)*b*(↑u⁻¹:R)))
   val_inv:=?_
   inv_val:=?_},rfl⟩
 · ext <;> simp [mul_assoc]
 · ext <;> simp [mul_assoc]
end DualNumber
end ProximityPrize.SubmissionLower.RCN078
end PackedLegacy_I8

/-! Packed from ProximityPrize.SubmissionLower.L6. -/
section PackedLegacy_L6
namespace ProximityPrize.SubmissionLower.RCN188
open RCN078
variable {K R S:Type*} [CommRing K] [CommRing R] [CommRing S]
 [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
 (M:Submonoid R) [IsLocalization M S]
def derivationDualAlgHom (D:Derivation K R R):R →ₐ[K] DualNumber S where
 toFun r:=(algebraMap R S r,algebraMap R S (D r))
 map_one':=by
   apply DualNumber.ext <;> simp
 map_mul' x y:=by
   apply DualNumber.ext
   · simp
   · simp [D.leibniz]
     exact mul_comm _ _
 map_zero':=by
   apply DualNumber.ext <;> simp
 map_add' x y:=by
   apply DualNumber.ext <;> simp
 commutes' k:=by
   apply DualNumber.ext
   · exact (IsScalarTower.algebraMap_apply K R S k).symm
   · simp
theorem derivationDualAlgHom_isUnit (D:Derivation K R R) (y:M):
   IsUnit (derivationDualAlgHom (S:=S) D y):=by
 apply DualNumber.isUnit_of_isUnit_fst
 simpa [derivationDualAlgHom] using IsLocalization.map_units S y
noncomputable def localizedDualAlgHom (D:Derivation K R R):
   S →ₐ[K] DualNumber S:=
 IsLocalization.liftAlgHom (derivationDualAlgHom_isUnit M D)
@[simp]
theorem localizedDualAlgHom_algebraMap (D:Derivation K R R) (r:R):
   localizedDualAlgHom M D (algebraMap R S r)=
     (algebraMap R S r,algebraMap R S (D r)):=by
 simp [localizedDualAlgHom,derivationDualAlgHom]
theorem localizedDualAlgHom_fst (D:Derivation K R R) (x:S):
   (localizedDualAlgHom M D x).fst=x:=by
 have hhom:
     (DualNumber.fstHom (K:=K) (R:=S)).comp
       (localizedDualAlgHom M D)=AlgHom.id K S:=by
   have hr:
       ((DualNumber.fstHom (K:=K) (R:=S)).comp
         (localizedDualAlgHom M D)).toRingHom=
         (AlgHom.id K S).toRingHom:=by
     apply IsLocalization.ringHom_ext M
     ext r
     simp [DualNumber.fstHom]
   exact AlgHom.ext fun x => RingHom.congr_fun hr x
 exact AlgHom.congr_fun hhom x
noncomputable def localizationDerivation (D:Derivation K R R):Derivation K S S:=
 Derivation.mk'
   ((DualNumber.sndHom (R:=S)).restrictScalars K |>.comp
     (localizedDualAlgHom M D).toLinearMap)
   (by
     intro x y
     change (localizedDualAlgHom M D (x*y)).snd=
       x*(localizedDualAlgHom M D y).snd+
         y*(localizedDualAlgHom M D x).snd
     rw [map_mul,DualNumber.snd_mul,
       localizedDualAlgHom_fst M D x,localizedDualAlgHom_fst M D y]
     simp
     ring)
@[simp]
theorem localizationDerivation_algebraMap (D:Derivation K R R) (r:R):
   localizationDerivation M D (algebraMap R S r)=algebraMap R S (D r):=by
 change (localizedDualAlgHom M D (algebraMap R S r)).snd=_
 rw [localizedDualAlgHom_algebraMap]
end ProximityPrize.SubmissionLower.RCN188
end PackedLegacy_L6

/-! Packed from ProximityPrize.SubmissionLower.FM. -/
section PackedLegacy_FM
namespace ProximityPrize.SubmissionLower.RCN230
open IsLocalRing Polynomial Ideal
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option synthInstance.maxHeartbeats 300000
variable (R:Type*) [CommRing R]
theorem exists_monic_span_compat {k:Type*} [Field k]
   (I:Ideal k[X]) (hne:I≠⊥):
   ∃ f,f.Monic∧I=Ideal.span {f}:=by
 classical
 letI:DecidableEq k:=Classical.decEq k
 obtain ⟨x,h,spanx⟩:=Ideal.exists_normalized_span_of_isPrincipal I
 refine ⟨x,(Polynomial.normalize_eq_self_iff_monic ?_).mp h,spanx⟩
 by_contra eq0
 simp [eq0,spanx] at hne
theorem exists_monic_span_sup_map_eq_compat
   (p:Ideal R[X]) (hmax:(p.comap Polynomial.C).IsMaximal)
   (hne:p≠(p.comap Polynomial.C).map Polynomial.C):
   ∃ f:R[X],f.Monic∧
     p=(p.comap Polynomial.C).map Polynomial.C ⊔ Ideal.span {f}:=by
 let q:=p.comap Polynomial.C
 letI:Field (R ⧸ q):=Ideal.Quotient.field q
 have hne':Ideal.map (Polynomial.mapRingHom (Ideal.Quotient.mk q)) p≠⊥:=by
   simp only [ne_eq,Ideal.map_eq_bot_iff_le_ker,
     Polynomial.ker_mapRingHom,q,Ideal.mk_ker]
   exact not_le_of_gt (lt_of_le_of_ne Ideal.map_comap_le hne.symm)
 rcases exists_monic_span_compat
     (Ideal.map (Polynomial.mapRingHom (Ideal.Quotient.mk q)) p) hne' with
   ⟨y,mony,hy⟩
 have hyLift:y∈Polynomial.lifts (Ideal.Quotient.mk q):=
   Polynomial.map_surjective _ Ideal.Quotient.mk_surjective _
 rcases Polynomial.lifts_and_natDegree_eq_and_monic hyLift mony with
   ⟨f,hf,_deg,monf⟩
 refine ⟨f,monf,?_⟩
 trans Ideal.comap (Polynomial.mapRingHom (Ideal.Quotient.mk q))
   ((Ideal.span {f}).map (Polynomial.mapRingHom (Ideal.Quotient.mk q)))
 · rw [Ideal.map_span,Polynomial.coe_mapRingHom,Set.image_singleton,hf, ←hy,
     Ideal.comap_map_of_surjective' _
       (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective)]
   simpa [Polynomial.ker_mapRingHom,q] using Ideal.map_comap_le
 · rw [Ideal.comap_map_of_surjective' _
     (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective),
     sup_comm,Polynomial.ker_mapRingHom,Ideal.mk_ker]
theorem height_map_C_compat [IsNoetherianRing R]
   (p:Ideal R) [p.IsMaximal]:
   (p.map Polynomial.C).height=p.height:=by
 have:(p.map Polynomial.C).LiesOver p:=
   ⟨Ideal.IsMaximal.eq_of_le inferInstance Ideal.IsPrime.ne_top' Ideal.le_comap_map⟩
 simp [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p]
theorem polynomial_localization_isRegularLocalRing_compat
   [IsRegularLocalRing R] (p:Ideal R[X]) [p.IsPrime]
   (hcomap:p.comap Polynomial.C=maximalIdeal R):
   IsRegularLocalRing (Localization.AtPrime p):=by
 apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
 let q:=(maximalIdeal R).map Polynomial.C
 have qle:q ≤ p:=by simpa [q, ←hcomap] using Ideal.map_comap_le
 have hreg:=(isRegularLocalRing_iff R).mp (inferInstance:IsRegularLocalRing R)
 have hfg':=(maximalIdeal R).fg_of_isNoetherianRing
 have hfg:=Submodule.FG.finite_generators hfg'
 have ht:(maximalIdeal R).height ≤ q.height:=
   le_of_eq (height_map_C_compat R (maximalIdeal R)).symm
 by_cases heq:p=q
 · have ht1:(maximalIdeal R).height ≤ p.height:=by simpa [heq]
   have hspan:Ideal.span
       ((algebraMap R (Localization.AtPrime p)) ''
         (maximalIdeal R).generators)=maximalIdeal (Localization.AtPrime p):=by
     rw [IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime p),
       RingHom.coe_comp,Set.image_comp, ←Ideal.map_span, ←Ideal.map_span]
     simp only [Ideal.span,(maximalIdeal R).span_generators,algebraMap_eq,
       q, ←heq,Localization.AtPrime.map_eq_maximalIdeal]
   simp only [←maximalIdeal_height_eq_ringKrullDim,
     ←IsLocalization.height_under p.primeCompl,
     IsLocalization.AtPrime.under_maximalIdeal _ p,ge_iff_le]
   apply le_trans _ (WithBot.coe_le_coe.mpr ht1)
   simp only [maximalIdeal_height_eq_ringKrullDim, ←hreg,Nat.cast_le,
     ←hspan, ←Submodule.FG.generators_ncard hfg']
   exact (Submodule.spanFinrank_span_le_ncard_of_finite (hfg.image _)).trans
     (Set.ncard_image_le hfg)
 · have hlt:q < p:=lt_of_le_of_ne qle (Ne.symm heq)
   have hpmax:(p.comap Polynomial.C).IsMaximal:=by
     simpa [hcomap] using maximalIdeal.isMaximal R
   obtain ⟨y,_,hy⟩:=
     exists_monic_span_sup_map_eq_compat R p hpmax (by simpa [hcomap])
   have peq:p=Ideal.span
       (((algebraMap R R[X]) '' (maximalIdeal R).generators) ∪ {y}):=by
     simp only [Set.union_comm,Ideal.span_union, ←Ideal.map_span,
       algebraMap_eq,sup_comm]
     nth_rw 1 [hy,hcomap, ←(maximalIdeal R).span_generators]
   simp only [←Localization.AtPrime.map_eq_maximalIdeal,peq,Ideal.map_span]
   rw [←maximalIdeal_height_eq_ringKrullDim,
     ←IsLocalization.height_under p.primeCompl,
     IsLocalization.AtPrime.under_maximalIdeal _ p]
   apply le_trans _
     (WithBot.coe_le_coe.mpr (Ideal.height_add_one_le_of_lt_of_isPrime hlt))
   apply le_trans _ (WithBot.coe_le_coe.mpr (add_le_add_left ht 1))
   rw [WithBot.coe_add,maximalIdeal_height_eq_ringKrullDim,WithBot.coe_one,
     ←hreg, ←Nat.cast_one, ←Nat.cast_add,Nat.cast_le]
   have hfin:=(hfg.image (algebraMap R R[X])).union (Set.finite_singleton y)
   apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (hfin.image _))
   apply le_trans (Set.ncard_image_le hfin) (le_trans (Set.ncard_union_le _ _) _)
   rw [Set.ncard_singleton,add_le_add_iff_right,
     ←Submodule.FG.generators_ncard hfg']
   exact Set.ncard_image_le hfg
end
end ProximityPrize.SubmissionLower.RCN230
end PackedLegacy_FM
end Compact_PackedLegacy
