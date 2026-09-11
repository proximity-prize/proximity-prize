import ProximityPrize.SubmissionLower.Part.F005_06
section Compact_PackedLegacyCore2
namespace ProximityPrize.SubmissionLower

end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.ED. -/
section PackedLegacy_ED
namespace ProximityPrize.SubmissionLower.RCN115
open scoped Classical BigOperators
open IsDedekindDomain RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN075 RCN323 RCN118 RCN093 RCN125 RCN371 RCN011
 RCN022
noncomputable section
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
structure SeparablePrincipalProjection
   {G T H:MvPolynomial (Fin 3) Omega}
   (E:Finset (Fin 3 →₀ ℕ)) (separator:Fin 3)
   (hseparator:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (coordinate Omega C.1 separator))
   (hproj:∀ C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1)
   (B:GenericExactPolePolynomial G T H E separator hseparator hproj) where
 parameter:∀ C:RegularComponent Omega G T H,
   SeparableCoordinate Omega (CoordinateField Omega C.1)
 pole_eq:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Omega (CoordinateField Omega C.1))
     (coordinate Omega C.1) B.polynomial
   RCN346.poleOrder Omega (CoordinateField Omega C.1) v b=
     RCN346.poleOrder Omega (CoordinateField Omega C.1) v
       (SeparableCoordinate.value Omega (CoordinateField Omega C.1)
         (parameter C))
def SeparablePrincipalProjection.cost
   {G T H:MvPolynomial (Fin 3) Omega}
   {E:Finset (Fin 3 →₀ ℕ)} {separator:Fin 3}
   {hseparator:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (coordinate Omega C.1 separator)}
   {hproj:∀ C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1}
   {B:GenericExactPolePolynomial G T H E separator hseparator hproj}
   (P:SeparablePrincipalProjection E separator hseparator hproj B)
   (C:RegularComponent Omega G T H):ℕ:=
 SeparableCoordinate.degree Omega (CoordinateField Omega C.1) (P.parameter C)
def SeparablePrincipalProjection.toPrincipalCycleBudget
   {G T H:MvPolynomial (Fin 3) Omega}
   {E:Finset (Fin 3 →₀ ℕ)} {separator:Fin 3}
   {hseparator:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (coordinate Omega C.1 separator)}
   {hproj:∀ C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1}
   {B:GenericExactPolePolynomial G T H E separator hseparator hproj}
   (P:SeparablePrincipalProjection E separator hseparator hproj B)
   (wholeCap:ℕ)
   (hsum:(∑ C:RegularComponent Omega G T H,P.cost C) ≤ wholeCap):
   PrincipalCycleBudget E separator hseparator hproj B wholeCap where
 cost:=P.cost
 cycle_le:=by
   intro C
   dsimp only
   let htr:=hseparator C
   letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
     quotientPolynomialAlgebra Omega C.1 separator
   letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
     polynomialBaseAlgebra Omega C.1 separator
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     rationalBaseAlgebra Omega C.1 separator htr
   letI:=quotientBaseScalarTower Omega C.1 separator
   letI:=polynomialBaseScalarTower Omega C.1 separator
   letI:=quotientFractionScalarTower Omega C.1 separator
   letI:=polynomialRationalScalarTower Omega C.1 separator htr
   letI:=rationalBaseScalarTower Omega C.1 separator htr
   letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
     (hproj C separator htr).1
   letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
     (hproj C separator htr).2
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Omega (CoordinateField Omega C.1))
     (coordinate Omega C.1) B.polynomial
   let hb:b≠0:=coordinate_eval_ne_zero_of_not_mem
     C.1 B.polynomial (B.proper C)
   let W:=RCN026.placesFor Omega
     (CoordinateField Omega C.1) b hb
   calc
     (∑ v∈W,RCN346.poleOrder Omega
         (CoordinateField Omega C.1) v b)=
         ∑ v∈W,RCN346.poleOrder Omega
           (CoordinateField Omega C.1) v
           (SeparableCoordinate.value Omega (CoordinateField Omega C.1)
             (P.parameter C)):=by
       apply Finset.sum_congr rfl
       intro v _
       exact P.pole_eq C v
     _ ≤ (SeparableCoordinate.degree Omega (CoordinateField Omega C.1)
         (P.parameter C):ℤ):=
       SeparableCoordinate.finite_sum_pole_le_degree Omega
         (CoordinateField Omega C.1) (P.parameter C) W
     _=(P.cost C:ℤ):=rfl
 sum_cost_le:=hsum
def flagSeparableCoordinate
   {G T H:MvPolynomial (Fin 3) Omega}
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (ht:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
   (hfinite:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
         (ht C)).toRingHom.toAlgebra
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))
   (hsep:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
         (ht C)).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
   (C:RegularComponent Omega G T H):
   SeparableCoordinate Omega (CoordinateField Omega C.1) where
 embedding:=elementEmbedding Omega (CoordinateField Omega C.1)
   (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))) (ht C)
 finite:=hfinite C
 separable:=hsep C
@[simp] theorem flagSeparableCoordinate_value
   {G T H:MvPolynomial (Fin 3) Omega}
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (ht:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
   (hfinite:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
         (ht C)).toRingHom.toAlgebra
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))
   (hsep:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
         (ht C)).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
   (C:RegularComponent Omega G T H):
   SeparableCoordinate.value Omega (CoordinateField Omega C.1)
       (flagSeparableCoordinate lam mu nu order ht hfinite hsep C)=
     flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)):=by
 exact elementEmbedding_variable Omega (CoordinateField Omega C.1)
   (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))) (ht C)
def principalCycleBudget_of_flag_trapezoid
   {G T H:MvPolynomial (Fin 3) Omega}
   {E:Finset (Fin 3 →₀ ℕ)} {separator:Fin 3}
   {hseparator:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (coordinate Omega C.1 separator)}
   {hproj:∀ C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1}
   (B:GenericExactPolePolynomial G T H E separator hseparator hproj)
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (ht:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
   (hgen:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
         (ht C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 2)),
         flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 1))}:
         Set (CoordinateField Omega C.1))=⊤)
   (hsep:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))
         (ht C)).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
   (hpole:∀ (C:RegularComponent Omega G T H)
       (v:Place Omega (CoordinateField Omega C.1)),
     let b:=MvPolynomial.eval₂Hom
       (algebraMap Omega (CoordinateField Omega C.1))
       (coordinate Omega C.1) B.polynomial
     RCN346.poleOrder Omega (CoordinateField Omega C.1) v b=
       RCN346.poleOrder Omega (CoordinateField Omega C.1) v
         (flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (order 0))))
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hpositive:0 <
     (planeMap Omega order (flagAlgHom lam mu nu G)).natDegree)
   (n mCap totalG totalT cap:ℕ) (hTne:T≠0)
   (hGouter:(planeMap Omega order
     (flagAlgHom lam mu nu G)).natDegree ≤ n)
   (hTouter:(planeMap Omega order
     (flagAlgHom lam mu nu T)).natDegree ≤ mCap)
   (hGsupport:∀ d∈(rationalMap Omega order
     (flagAlgHom lam mu nu G)).support,d 0+d 1 ≤ totalG)
   (hTsupport:∀ d∈(rationalMap Omega order
     (flagAlgHom lam mu nu T)).support,d 0+d 1 ≤ totalT)
   (hbudget:∀ m,m ≤ mCap →
     m*totalG+n*totalT-m*n ≤ cap):
   PrincipalCycleBudget E separator hseparator hproj B cap:=by
 have hinj:Function.Injective
     (fun C:RegularComponent Omega G T H↦C.1):=by
   intro C D hCD
   exact Subtype.ext hCD
 have hfamily:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:RegularComponent Omega G T H↦C.1)
   hinj lam mu nu order ht hgen G T hG
   (fun C↦regularComponent_G_mem Omega G T H C)
   (fun C↦regularComponent_T_mem Omega G T H C)
   hproper hpositive n mCap totalG totalT cap hTne
   hGouter hTouter hGsupport hTsupport hbudget
 let hfinite:=hfamily.1
 let P:SeparablePrincipalProjection E separator hseparator hproj B:={
   parameter:=fun C↦
     flagSeparableCoordinate lam mu nu order ht hfinite hsep C
   pole_eq:=by
     intro C v
     simpa only [flagSeparableCoordinate_value] using hpole C v}
 apply P.toPrincipalCycleBudget cap
 change (∑ C:RegularComponent Omega G T H,
   SeparableCoordinate.degree Omega (CoordinateField Omega C.1)
     (flagSeparableCoordinate lam mu nu order ht hfinite hsep C)) ≤ cap
 convert hfamily.2 using 1
 apply Finset.sum_congr rfl
 intro C _
 rfl
end
end ProximityPrize.SubmissionLower.RCN115
end PackedLegacy_ED

/-! Packed from ProximityPrize.SubmissionLower.Z0. -/
section PackedLegacy_Z0
namespace ProximityPrize.SubmissionLower.RCN116
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN187 RCN075 RCN295 RCN095 RCN114 RCN125 RCN093 RCN097 RCN099 RCN115 RCN118 RCN123 RCN272 RCN371 RCN011
 RCN022
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 10000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
variable {hseparator:∀ C:RegularComponent Omega G T H,
 Transcendental Omega (coordinate Omega C.1 2)}
variable {hproj:∀ C:RegularComponent Omega G T H,
 ProjectionsFiniteSeparable Omega C.1}
def exactAgreementFlag6543:FlagDegree:=⟨91749700,5504983,1179639⟩
theorem elementEmbedding_congr
   {L:Type} [Field L] [Algebra Omega L]
   {s t:L} (hs:Transcendental Omega s)
   (ht:Transcendental Omega t) (h:s=t):
   elementEmbedding Omega L s hs=elementEmbedding Omega L t ht:=by
 subst t
 rfl
theorem elementEmbedding_coordinate_eq_rationalBaseEmbedding
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (i:Fin 3) (hs ht:Transcendental Omega (coordinate Omega P i)):
   elementEmbedding Omega (CoordinateField Omega P)
       (coordinate Omega P i) hs=
     rationalBaseEmbedding Omega P i ht:=by
 rfl
structure FlagProjectionPositivity
   (D:NestedFlagProjectionData hseparator hproj)
   (G:MvPolynomial (Fin 3) Omega):Prop where
 u:0 < (planeMap Omega uOrder
   (flagAlgHom D.lam D.mu (D.mu*D.lam) G)).natDegree
 v:0 < (planeMap Omega vOrder
   (flagAlgHom D.lam D.mu (D.mu*D.lam) G)).natDegree
 z:0 < (planeMap Omega zOrder
   (flagAlgHom D.lam D.mu (D.mu*D.lam) G)).natDegree
theorem unitZ_polynomial_pole
   (B:GenericExactPolePolynomial G T H (flagSupport unitZFlag) 2
     hseparator hproj)
   (C:RegularComponent Omega G T H)
   (v:Place Omega (CoordinateField Omega C.1)):
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Omega (CoordinateField Omega C.1))
     (coordinate Omega C.1) B.polynomial
   poleOrder v.val b=poleOrder v.val (coordinate Omega C.1 2):=by
 dsimp only
 calc
   poleOrder v.val
       (MvPolynomial.eval₂Hom
         (algebraMap Omega (CoordinateField Omega C.1))
         (coordinate Omega C.1) B.polynomial)=
       exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport unitZFlag):=B.exact_pole C v
   _=poleOrder v.val (coordinate Omega C.1 2):=
     exponentSetPoleWeight_unitZ v.val (coordinate Omega C.1)
theorem unitYZ_polynomial_pole
   (D:NestedFlagProjectionData hseparator hproj)
   (B:GenericExactPolePolynomial G T H (flagSupport unitYZFlag) 2
     hseparator hproj)
   (C:RegularComponent Omega G T H)
   (v:Place Omega (CoordinateField Omega C.1)):
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Omega (CoordinateField Omega C.1))
     (coordinate Omega C.1) B.polynomial
   poleOrder v.val b=poleOrder v.val (affineU Omega C.1 D.lam):=by
 dsimp only
 calc
   poleOrder v.val
       (MvPolynomial.eval₂Hom
         (algebraMap Omega (CoordinateField Omega C.1))
         (coordinate Omega C.1) B.polynomial)=
       exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport unitYZFlag):=B.exact_pole C v
   _=max (poleOrder v.val (coordinate Omega C.1 0))
         (poleOrder v.val (coordinate Omega C.1 2)):=
     exponentSetPoleWeight_unitYZ v.val (coordinate Omega C.1)
   _=poleOrder v.val (affineU Omega C.1 D.lam):=
     (nested_u_pole D C v).symm
theorem unitAll_polynomial_pole
   (D:NestedFlagProjectionData hseparator hproj)
   (B:GenericExactPolePolynomial G T H (flagSupport unitAllFlag) 2
     hseparator hproj)
   (C:RegularComponent Omega G T H)
   (v:Place Omega (CoordinateField Omega C.1)):
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Omega (CoordinateField Omega C.1))
     (coordinate Omega C.1) B.polynomial
   poleOrder v.val b=
     poleOrder v.val (affineV Omega C.1 D.mu (D.mu*D.lam)):=by
 dsimp only
 calc
   poleOrder v.val
       (MvPolynomial.eval₂Hom
         (algebraMap Omega (CoordinateField Omega C.1))
         (coordinate Omega C.1) B.polynomial)=
       exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport unitAllFlag):=B.exact_pole C v
   _=max (poleOrder v.val (coordinate Omega C.1 1))
         (max (poleOrder v.val (coordinate Omega C.1 0))
           (poleOrder v.val (coordinate Omega C.1 2))):=
     exponentSetPoleWeight_unitAll v.val (coordinate Omega C.1)
   _=poleOrder v.val
         (affineV Omega C.1 D.mu (D.mu*D.lam)):=
     (nested_v_pole D C v).symm
def flagProjectionCycleBudget6543_of_nested
   (D:NestedFlagProjectionData hseparator hproj)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport shearedSurfaceFlag)
   (hTsupport:T.support ⊆ flagSupport shearedAgreementFlag)
   (hpositive:FlagProjectionPositivity D G)
   (B:GenericExactPolePolynomial G T H
     (flagSupport shearedAgreementFlag) 2 hseparator hproj)
   (BZ:GenericExactPolePolynomial G T H
     (flagSupport unitZFlag) 2 hseparator hproj)
   (BYZ:GenericExactPolePolynomial G T H
     (flagSupport unitYZFlag) 2 hseparator hproj)
   (BAll:GenericExactPolePolynomial G T H
     (flagSupport unitAllFlag) 2 hseparator hproj):
   FlagProjectionCycleBudget shearedAgreementFlag 2 hseparator hproj B
     flagZMixedCap flagYZMixedCap flagAllMixedCap:=by
 let lam:=D.lam
 let mu:=D.mu
 let nu:=D.mu*D.lam
 let gCaps:=flagTrapezoidCaps_flagAlgHom shearedSurfaceFlag G
   lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom shearedAgreementFlag T
   lam mu nu hTsupport
 let htZ:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (zOrder 0))):=by
   intro C
   simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu] using hseparator C
 let htU:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (uOrder 0))):=by
   intro C
   simpa [uOrder,lam,mu,nu] using D.hU C
 let htV:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (vOrder 0))):=by
   intro C
   simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using hAffineV D C
 have hembZ (C:RegularComponent Omega G T H):
     elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (zOrder 0)))
         (htZ C)=
       elementEmbedding Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 2) (hseparator C):=
   elementEmbedding_congr (htZ C) (hseparator C)
     (by simp [zOrder,Equiv.swap_apply_def,lam,mu,nu])
 have hembU (C:RegularComponent Omega G T H):
     elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (uOrder 0)))
         (htU C)=
       elementEmbedding Omega (CoordinateField Omega C.1)
         (affineU Omega C.1 D.lam) (D.hU C):=
   elementEmbedding_congr (htU C) (D.hU C)
     (by simp [uOrder,lam,mu,nu])
 have hembV (C:RegularComponent Omega G T H):
     elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (vOrder 0)))
         (htV C)=
       elementEmbedding Omega (CoordinateField Omega C.1)
         (affineV Omega C.1 D.mu (D.mu*D.lam)) (hAffineV D C):=
   elementEmbedding_congr (htV C) (hAffineV D C)
     (by simp [vOrder,Equiv.swap_apply_def,lam,mu,nu])
 have hTne:T≠0:=by
   intro hzero
   apply hproper
   rw [hzero]
   exact dvd_zero G
 let zBudget:PrincipalCycleBudget (flagSupport unitZFlag) 2
     hseparator hproj BZ flagZMixedCap:=
   principalCycleBudget_of_flag_trapezoid BZ lam mu nu zOrder
     htZ
     (by
       intro C
       rw [hembZ C]
       simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu] using
         flag_generators_z Omega C.1 lam mu nu (hseparator C))
     (by
       intro C
       rw [hembZ C,
         elementEmbedding_coordinate_eq_rationalBaseEmbedding C.1 2
           (hseparator C) (hseparator C)]
       exact (hproj C 2 (hseparator C)).2)
     (by intro C v;simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu,
         RCN346.poleOrder] using
       unitZ_polynomial_pole BZ C v)
     hG hproper hpositive.z 5 1179639 26 6684622 flagZMixedCap hTne
     (by simpa [gCaps,shearedSurfaceFlag] using gCaps.zOuter)
     (by simpa [tCaps,shearedAgreementFlag_value] using tCaps.zOuter)
     (by simpa [gCaps,shearedSurfaceFlag] using gCaps.zTotal)
     (by simpa [tCaps,shearedAgreementFlag_value] using tCaps.zTotal)
     RCN123.z_trapezoid_budget6543
 let yzBudget:PrincipalCycleBudget (flagSupport unitYZFlag) 2
     hseparator hproj BYZ flagYZMixedCap:=
   principalCycleBudget_of_flag_trapezoid BYZ lam mu nu uOrder
     htU
     (by
       intro C
       rw [hembU C]
       simpa [uOrder,lam,mu,nu] using
         flag_generators_u Omega C.1 lam mu nu (D.hU C))
     (by
       intro C
       rw [hembU C]
       exact D.separableU C)
     (by intro C v;simpa [uOrder,lam,mu,nu,
         RCN346.poleOrder] using
       unitYZ_polynomial_pole D BYZ C v)
     hG hproper hpositive.u 5 1179639 376 98434322 flagYZMixedCap hTne
     (by simpa [gCaps,shearedSurfaceFlag] using gCaps.uOuter)
     (by simpa [tCaps,shearedAgreementFlag_value] using tCaps.uOuter)
     (by simpa [gCaps,shearedSurfaceFlag] using gCaps.uTotal)
     (by simpa [tCaps,shearedAgreementFlag_value] using tCaps.uTotal)
     RCN123.u_trapezoid_budget6543
 let allBudget:PrincipalCycleBudget (flagSupport unitAllFlag) 2
     hseparator hproj BAll flagAllMixedCap:=
   principalCycleBudget_of_flag_trapezoid BAll lam mu nu vOrder
     htV
     (by
       intro C
       rw [hembV C]
       simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using
         flag_generators_v Omega C.1 lam mu nu (hAffineV D C))
     (by
       intro C
       rw [hembV C]
       exact separableAffineV D C)
     (by intro C v;simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu,
         RCN346.poleOrder] using
       unitAll_polynomial_pole D BAll C v)
     hG hproper hpositive.v 26 6684622 376 98434322 flagAllMixedCap hTne
     (by simpa [gCaps,shearedSurfaceFlag] using gCaps.vOuter)
     (by simpa [tCaps,shearedAgreementFlag_value] using tCaps.vOuter)
     (by simpa [gCaps,shearedSurfaceFlag] using gCaps.vTotal)
     (by simpa [tCaps,shearedAgreementFlag_value] using tCaps.vTotal)
     RCN123.v_trapezoid_budget6543
 exact FlagProjectionCycleBudget.ofNestedProjectionBudgets B BZ BYZ BAll
   zBudget yzBudget allBudget
def residualComponentBudget6543_of_nested
   (D:NestedFlagProjectionData hseparator hproj)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport shearedSurfaceFlag)
   (hTsupport:T.support ⊆ flagSupport shearedAgreementFlag)
   (hpositive:FlagProjectionPositivity D G)
   (B:GenericExactPolePolynomial G T H
     (flagSupport shearedAgreementFlag) 2 hseparator hproj)
   (BZ:GenericExactPolePolynomial G T H
     (flagSupport unitZFlag) 2 hseparator hproj)
   (BYZ:GenericExactPolePolynomial G T H
     (flagSupport unitYZFlag) 2 hseparator hproj)
   (BAll:GenericExactPolePolynomial G T H
     (flagSupport unitAllFlag) 2 hseparator hproj):
   ResidualComponentBudget G T H
     (fun A↦A.support ⊆ flagSupport shearedAgreementFlag)
     flagWholeMixedCap:=
 (flagProjectionCycleBudget6543_of_nested D hG hproper hGsupport hTsupport
   hpositive B BZ BYZ BAll).toResidualComponentBudget6543
end
end ProximityPrize.SubmissionLower.RCN116
end PackedLegacy_Z0

/-! Packed from ProximityPrize.SubmissionLower.X9. -/
section PackedLegacy_X9
namespace ProximityPrize.SubmissionLower.RCN037
open scoped Classical WithZero TensorProduct
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN035 RCN044 RCN093 RCN099 RCN096 RCN114 RCN116 RCN295 RCN022 RCN369 RCN370
 RCN351
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def LiteralProjectionGate
   (C:RegularComponent Omega G T H) (j:Fin 3):Prop:=
 ∀ hj:Transcendental Omega (coordinate Omega C.1 j),
   (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 j) hj).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 j) hj).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
theorem base_differential_ne_zero
   {P:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime]
   (B:SeparableLiteralCoordinate P):
   D Omega (CoordinateField Omega P) (coordinate Omega P B.index)≠0:=by
 have h:=parameterDifferential_ne_zero_of_isSeparable Omega
   (CoordinateField Omega P)
   (rationalBaseEmbedding Omega P B.index B.transcendental)
   B.finite B.separable
 unfold RCN369.parameterDifferential at h
 have hvalue:rationalBaseEmbedding Omega P B.index B.transcendental
     (algebraMap (Polynomial Omega) (RatFunc Omega) Polynomial.X)=
       coordinate Omega P B.index:=
   (rationalBaseEmbedding_polynomial Omega P B.index B.transcendental
     Polynomial.X).trans (Polynomial.aeval_X _)
 rwa [hvalue] at h
theorem poleOrder_eq_zero_of_isAlgebraic
   {L:Type*} [Field L] [Algebra Omega L]
   (v:RCN346.Place Omega L) (x:L)
   (hx:IsAlgebraic Omega x):
   RCN187.poleOrder v.val x=0:=by
 obtain ⟨a,rfl⟩:=eq_algebraMap_of_isAlgebraic Omega L x hx
 exact RCN346.poleOrder_eq_zero_of_le_one Omega L v _
   (constant_value_le_one Omega L v a)
structure AdaptiveNestedProjectionData
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hY:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0) where
 lam:Omega
 lam_ne:lam≠0
 mu:Omega
 mu_ne:mu≠0
 uProjection:∀ C:RegularComponent Omega G T H,
   Coordinate Omega (CoordinateField Omega C.1)
 allProjection:∀ C:RegularComponent Omega G T H,
   Coordinate Omega (CoordinateField Omega C.1)
 uGate:∀ C:RegularComponent Omega G T H,
   ∀ htr:Transcendental Omega (affineU Omega C.1 lam),
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1)
           (affineU Omega C.1 lam) htr).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1)
           (affineU Omega C.1 lam) htr).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
 allAffineTranscendental:∀ C:RegularComponent Omega G T H,
   Transcendental Omega (affineV Omega C.1 mu (mu*lam))
 allFinite:∀ C:RegularComponent Omega G T H,
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 mu (mu*lam))
       (allAffineTranscendental C)).toRingHom.toAlgebra
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1)
 allSeparable:∀ C:RegularComponent Omega G T H,
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 mu (mu*lam))
       (allAffineTranscendental C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)
 uValue:∀ C:RegularComponent Omega G T H,
   coordinateValue Omega (CoordinateField Omega C.1) (uProjection C)=
     affineU Omega C.1 lam
 allValue:∀ C:RegularComponent Omega G T H,
   coordinateValue Omega (CoordinateField Omega C.1) (allProjection C)=
     affineV Omega C.1 mu (mu*lam)
 allTranscendental:∀ C:RegularComponent Omega G T H,
   Transcendental Omega
     (coordinateValue Omega (CoordinateField Omega C.1) (allProjection C))
 uPole:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
   RCN187.poleOrder v.val
       (coordinateValue Omega (CoordinateField Omega C.1) (uProjection C))=
     max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
       (RCN187.poleOrder v.val (coordinate Omega C.1 2))
 allPole:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
   RCN187.poleOrder v.val
       (coordinateValue Omega (CoordinateField Omega C.1) (allProjection C))=
     max (RCN187.poleOrder v.val (coordinate Omega C.1 1))
       (max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
         (RCN187.poleOrder v.val (coordinate Omega C.1 2)))
 directional:MvPolynomial.pderiv (0:Fin 3) G-
   MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) G≠0
theorem exists_adaptiveNestedProjectionData
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hY:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0):
   Nonempty (AdaptiveNestedProjectionData base hY hZ hSderiv):=by
 classical
 let ActiveU:={C:RegularComponent Omega G T H//
   D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0}
 let EU:ActiveU → Type:=fun C => CoordinateField Omega C.1.1
 let rY:∀ C:ActiveU,EU C:=fun C => coordinate Omega C.1.1 0
 let z:∀ C:ActiveU,EU C:=fun C => coordinate Omega C.1.1 2
 let WU:∀ C:ActiveU,Finset (Place Omega (EU C)):=
   fun C => literalRelevantPlaces (base C.1)
 let baseU:∀ C:ActiveU,SeparableCoordinate Omega (EU C):=
   fun C => literalToSeparableCoordinate (base C.1)
 obtain ⟨lam,hlam0,hlam⟩:=
   exists_common_exact_finite_separable_affine_adaptive EU rY z WU
     baseU (fun C => C.2)
 let U:∀ C:RegularComponent Omega G T H,
     CoordinateField Omega C.1:=
   fun C => affineU Omega C.1 lam
 have hUgate:∀ C:RegularComponent Omega G T H,
     ∀ htr:Transcendental Omega (U C),
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (U C) htr).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (U C) htr).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)):=by
   intro C htr
   by_cases hactive:
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
         D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0
   · let CU:ActiveU:=⟨C,hactive⟩
     obtain ⟨hs,hfinite,hsep,_⟩:=hlam CU
     have hp:htr=hs:=Subsingleton.elim _ _
     cases hp
     exact ⟨hfinite,hsep⟩
   · have hzero:=not_or.mp hactive
     have hYalg:IsAlgebraic Omega (coordinate Omega C.1 0):=by
       apply not_not.mp
       intro hy
       exact (differential_ne_zero_of_gate _ hy (hY C hy))
         (not_ne_iff.mp hzero.1)
     have hZalg:IsAlgebraic Omega (coordinate Omega C.1 2):=by
       apply not_not.mp
       intro hz
       exact (differential_ne_zero_of_gate _ hz (hZ C hz))
         (not_ne_iff.mp hzero.2)
     exact (htr (hYalg.add (hZalg.smul lam))).elim
 let uProjection:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=
   fun C => coordinateOfGate (U C) (hUgate C)
 have huValue:∀ C:RegularComponent Omega G T H,
     coordinateValue Omega (CoordinateField Omega C.1) (uProjection C)=U C:=
   fun C => coordinateOfGate_value (U C) (hUgate C)
 have huPole:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
     RCN187.poleOrder v.val (U C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
         (RCN187.poleOrder v.val (coordinate Omega C.1 2)):=by
   intro C v
   by_cases hactive:
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
         D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0
   · let CU:ActiveU:=⟨C,hactive⟩
     by_cases hv:v∈literalRelevantPlaces (base C)
     · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
         simpa only [WU,rY,z,U,affineU] using
           (hlam CU).choose_spec.2.2 v hv)
     · have h0:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
           (base C) v hv 0
       have h2:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
           (base C) v hv 2
       have h0le:=valuation_le_one_of_poleOrder_eq_zero v.val _ h0
       have h2le:=valuation_le_one_of_poleOrder_eq_zero v.val _ h2
       letI:v.val.IsTrivialOn Omega:=v.property.2
       have hscalar:v.val (lam • coordinate Omega C.1 2)=
           v.val (coordinate Omega C.1 2):=by
         rw [Algebra.smul_def,map_mul,
           Valuation.IsTrivialOn.eq_one lam hlam0,one_mul]
       have hUle:v.val (U C) ≤ 1:=by
         exact (v.val.map_add _ _).trans
           (by rw [hscalar];exact max_le h0le h2le)
       have hU0:RCN187.poleOrder v.val (U C)=0:=
         RCN346.poleOrder_eq_zero_of_le_one Omega
           (CoordinateField Omega C.1) v _ hUle
       rw [hU0,h0,h2]
       simp
   · have hzero:=not_or.mp hactive
     have hYalg:IsAlgebraic Omega (coordinate Omega C.1 0):=by
       apply not_not.mp
       intro hy
       exact (differential_ne_zero_of_gate _ hy (hY C hy))
         (not_ne_iff.mp hzero.1)
     have hZalg:IsAlgebraic Omega (coordinate Omega C.1 2):=by
       apply not_not.mp
       intro hz
       exact (differential_ne_zero_of_gate _ hz (hZ C hz))
         (not_ne_iff.mp hzero.2)
     have hUalg:IsAlgebraic Omega (U C):=hYalg.add (hZalg.smul lam)
     rw [poleOrder_eq_zero_of_isAlgebraic v _ hUalg,
       poleOrder_eq_zero_of_isAlgebraic v _ hYalg,
       poleOrder_eq_zero_of_isAlgebraic v _ hZalg]
     simp
 have hactiveV:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 1)≠0∨
       D Omega (CoordinateField Omega C.1) (U C)≠0:=by
   intro C
   by_cases hactive:
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
         D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0
   · let CU:ActiveU:=⟨C,hactive⟩
     obtain ⟨hs,hfinite,hsep,_⟩:=hlam CU
     exact Or.inr (differential_ne_zero_of_gate _ hs ⟨hfinite,hsep⟩)
   · have hzero:=not_or.mp hactive
     have hb:=base_differential_ne_zero (base C)
     generalize hidx:(base C).index=i at hb
     fin_cases i
     · exact (hb (not_ne_iff.mp hzero.1)).elim
     · exact Or.inl hb
     · exact (hb (not_ne_iff.mp hzero.2)).elim
 let EC:RegularComponent Omega G T H → Type:=
   fun C => CoordinateField Omega C.1
 let rS:∀ C,EC C:=fun C => coordinate Omega C.1 1
 let W:∀ C,Finset (Place Omega (EC C)):=
   fun C => literalRelevantPlaces (base C)
 let baseC:∀ C,SeparableCoordinate Omega (EC C):=
   fun C => literalToSeparableCoordinate (base C)
 let Extra:Omega → Prop:=fun mu =>
   MvPolynomial.pderiv (0:Fin 3) G-
     MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) G=0
 have hextra:∀ {a b},Extra a → Extra b → a=b:=by
   exact directional_bad_coefficient_subsingleton G hSderiv
 obtain ⟨mu,hmu0,hmudir,hmu⟩:=
   exists_common_exact_finite_separable_affine_adaptive_avoiding_one
     EC rS U W Extra hextra baseC hactiveV
 let V:∀ C:RegularComponent Omega G T H,
     CoordinateField Omega C.1:=
   fun C => coordinate Omega C.1 1+mu • U C
 let hV:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (V C):=fun C => (hmu C).choose
 let vProjection:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C => Sum.inr {
   embedding:=elementEmbedding Omega (CoordinateField Omega C.1) (V C) (hV C)
   finite:=(hmu C).choose_spec.1
   separable:=(hmu C).choose_spec.2.1}
 have hvValue:∀ C:RegularComponent Omega G T H,
     coordinateValue Omega (CoordinateField Omega C.1) (vProjection C)=V C:=by
   intro C
   exact elementEmbedding_variable Omega (CoordinateField Omega C.1) (V C) (hV C)
 have hvPole:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
     RCN187.poleOrder v.val (V C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.1 1))
         (RCN187.poleOrder v.val (U C)):=by
   intro C v
   by_cases hv:v∈literalRelevantPlaces (base C)
   · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
       simpa only [W,rS,V] using (hmu C).choose_spec.2.2 v hv)
   · have hS:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C) v hv 1
     have hY:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C) v hv 0
     have hZ:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C) v hv 2
     have hU:RCN187.poleOrder v.val (U C)=0:=by
       rw [huPole C v,hY,hZ]
       simp
     have hSle:=valuation_le_one_of_poleOrder_eq_zero v.val _ hS
     have hUle:=valuation_le_one_of_poleOrder_eq_zero v.val _ hU
     letI:v.val.IsTrivialOn Omega:=v.property.2
     have hscalar:v.val (mu • U C)=v.val (U C):=by
       rw [Algebra.smul_def,map_mul,
         Valuation.IsTrivialOn.eq_one mu hmu0,one_mul]
     have hVle:v.val (V C) ≤ 1:=
       (v.val.map_add _ _).trans
         (by rw [hscalar];exact max_le hSle hUle)
     have hV0:RCN187.poleOrder v.val (V C)=0:=
       RCN346.poleOrder_eq_zero_of_le_one Omega
         (CoordinateField Omega C.1) v _ hVle
     rw [hV0,hS,hU]
     simp
 let hVAff:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (affineV Omega C.1 mu (mu*lam)):=fun C => by
   rw [show affineV Omega C.1 mu (mu*lam)=V C by
     simp only [V,U,affineU,affineV]
     module]
   exact hV C
 have hembV (C:RegularComponent Omega G T H):
     elementEmbedding Omega (CoordinateField Omega C.1)
         (affineV Omega C.1 mu (mu*lam)) (hVAff C)=
       elementEmbedding Omega (CoordinateField Omega C.1) (V C) (hV C):=
   elementEmbedding_congr (hVAff C) (hV C) (by
     simp only [V,U,affineU,affineV]
     simp only [smul_add,smul_smul,add_assoc])
 refine ⟨{
   lam:=lam
   lam_ne:=hlam0
   mu:=mu
   mu_ne:=hmu0
   uProjection:=uProjection
   allProjection:=vProjection
   uGate:=hUgate
   allAffineTranscendental:=hVAff
   allFinite:=?_
   allSeparable:=?_
   uValue:=huValue
   allValue:=?_
   allTranscendental:=?_
   uPole:=?_
   allPole:=?_
   directional:=hmudir}⟩
 · intro C
   rw [hembV C]
   exact (hmu C).choose_spec.1
 · intro C
   rw [hembV C]
   exact (hmu C).choose_spec.2.1
 · intro C
   rw [hvValue C]
   simp only [V,U,affineU,affineV]
   simp only [smul_add,smul_smul,add_assoc]
 · intro C
   rw [hvValue C]
   exact hV C
 · intro C v
   rw [huValue C]
   exact huPole C v
 · intro C v
   rw [hvValue C,hvPole C v,huPole C v]
end
end ProximityPrize.SubmissionLower.RCN037
end PackedLegacy_X9

/-! Packed from ProximityPrize.SubmissionLower.C0. -/

/-! Packed from ProximityPrize.SubmissionLower.BA. -/
section PackedLegacy_BA
namespace ProximityPrize.SubmissionLower.RCN117
open scoped Classical
open RCN267 RCN125 RCN097 RCN116 RCN011
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
theorem derivative_planeMap (order:Equiv (Fin 3) (Fin 3)) (F:Poly3 K):
   Polynomial.derivative (planeMap K order F)=
     planeMap K order (MvPolynomial.pderiv (order 1) F):=by
 induction F using MvPolynomial.induction_on with
 | C a => simp
 | add P Q hP hQ => simp [hP,hQ]
 | mul_X P i hP =>
     obtain ⟨j,rfl⟩:=order.surjective i
     fin_cases j <;>
       simp [MvPolynomial.pderiv_mul,hP,Polynomial.derivative_mul,
         planeMap_X_first,planeMap_X_outer,planeMap_X_inner,
         Pi.single_apply] <;> ring
theorem planeMap_natDegree_pos_of_pderiv_ne_zero
   (order:Equiv (Fin 3) (Fin 3)) (F:Poly3 K)
   (hderiv:MvPolynomial.pderiv (order 1) F≠0):
   0 < (planeMap K order F).natDegree:=by
 apply Nat.pos_of_ne_zero
 intro hzero
 have hplanezero:Polynomial.derivative (planeMap K order F)=0:=
   Polynomial.derivative_of_natDegree_zero hzero
 rw [derivative_planeMap] at hplanezero
 apply hderiv
 apply planeMap_injective K order
 simpa only [map_zero] using hplanezero
theorem pderiv_one_flagAlgHom (lam mu nu:K) (F:Poly3 K):
   MvPolynomial.pderiv (1:Fin 3) (flagAlgHom lam mu nu F)=
     flagAlgHom lam mu nu (MvPolynomial.pderiv (1:Fin 3) F):=by
 induction F using MvPolynomial.induction_on with
 | C a => simp
 | add P Q hP hQ => simp [hP,hQ]
 | mul_X P i hP =>
     fin_cases i <;>
       simp [flagImage,hP,MvPolynomial.pderiv_mul,
         Derivation.leibniz] <;> ring
theorem pderiv_zero_flagAlgHom_nested (lam mu:K) (F:Poly3 K):
   MvPolynomial.pderiv (0:Fin 3)
       (flagAlgHom lam mu (mu*lam) F)=
     flagAlgHom lam mu (mu*lam)
       (MvPolynomial.pderiv (0:Fin 3) F-
         MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) F):=by
 induction F using MvPolynomial.induction_on with
 | C a => simp
 | add P Q hP hQ =>
     simp [hP,hQ,mul_add,sub_eq_add_neg] <;> ring
 | mul_X P i hP =>
     fin_cases i <;>
       simp [flagImage,hP,MvPolynomial.pderiv_mul,
         Derivation.leibniz] <;> ring
theorem flag_u_z_outer_positive_of_pderiv
   (lam mu:K) (G:Poly3 K)
   (hderiv:MvPolynomial.pderiv (1:Fin 3) G≠0):
   0 < (planeMap K uOrder
         (flagAlgHom lam mu (mu*lam) G)).natDegree∧
     0 < (planeMap K zOrder
         (flagAlgHom lam mu (mu*lam) G)).natDegree:=by
 have hflag:MvPolynomial.pderiv (1:Fin 3)
     (flagAlgHom lam mu (mu*lam) G)≠0:=by
   rw [pderiv_one_flagAlgHom]
   exact (flagEquiv lam mu (mu*lam)).injective.ne hderiv
 constructor
 · apply planeMap_natDegree_pos_of_pderiv_ne_zero uOrder
   simpa [uOrder] using hflag
 · apply planeMap_natDegree_pos_of_pderiv_ne_zero zOrder
   simpa [zOrder,Equiv.swap_apply_def] using hflag
section Characteristic
variable (p:ℕ) [CharP K p]
theorem flag_v_outer_positive_of_directional
   (lam mu:K) (G:Poly3 K)
   (hdirectional:MvPolynomial.pderiv (0:Fin 3) G-
     MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) G≠0):
   0 < (planeMap K vOrder
       (flagAlgHom lam mu (mu*lam) G)).natDegree:=by
 apply planeMap_natDegree_pos_of_pderiv_ne_zero vOrder
 simpa [vOrder,Equiv.swap_apply_def,
   pderiv_zero_flagAlgHom_nested] using
   (flagEquiv lam mu (mu*lam)).injective.ne hdirectional
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega p]
 {G T H:MvPolynomial (Fin 3) Omega}
variable
   {hseparator:∀ C:RCN264.RegularComponent
       Omega G T H,
     Transcendental Omega
       (RCN002.coordinate Omega C.1 2)}
   {hproj:∀ C:RCN264.RegularComponent
       Omega G T H,
     RCN007.ProjectionsFiniteSeparable Omega C.1}
end Characteristic
end
end ProximityPrize.SubmissionLower.RCN117
end PackedLegacy_BA

/-! Packed from ProximityPrize.SubmissionLower.Y0. -/
section PackedLegacy_Y0
namespace ProximityPrize.SubmissionLower.RCN039
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN046 RCN037 RCN095 RCN114 RCN093 RCN123 RCN121 RCN117 RCN116 RCN125 RCN022
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def adaptiveUnitProjectionFamily_of_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hY:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (D:AdaptiveNestedProjectionData base hY hZ hSderiv)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   AdaptiveUnitProjectionFamily base p q:=by
 classical
 let lam:=D.lam
 let mu:=D.mu
 let nu:=D.mu*D.lam
 let zProj:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C =>
   coordinateOfGate (coordinate Omega C.1 2) (hZ C)
 let uProj:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C =>
   coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C)
 let vProj:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C => Sum.inr {
   embedding:=elementEmbedding Omega (CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam))
     (D.allAffineTranscendental C)
   finite:=D.allFinite C
   separable:=D.allSeparable C}
 let gCaps:=flagTrapezoidCaps_flagAlgHom p G lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom q T lam mu nu hTsupport
 have hTne:T≠0:=by
   intro hzero
   apply hproper
   rw [hzero]
   exact dvd_zero G
 let sZ:={C:RegularComponent Omega G T H//
   Transcendental Omega (coordinate Omega C.1 2)}
 have hinjZ:Function.Injective (fun C:sZ => C.1.1):=by
   intro C E hCE
   apply Subtype.ext
   apply Subtype.ext
   exact hCE
 let htZ:∀ C:sZ,
     Transcendental Omega
       (flagEvaluation Omega C.1.1 lam mu nu
         (MvPolynomial.X (zOrder 0))):=by
   intro C
   simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu] using C.2
 have hembZ (C:sZ):
     elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 0))) (htZ C)=
       elementEmbedding Omega (CoordinateField Omega C.1.1)
         (coordinate Omega C.1.1 2) C.2:=
   elementEmbedding_congr (htZ C) C.2
     (by simp [zOrder,Equiv.swap_apply_def,lam,mu,nu])
 have hgenZ:∀ C:sZ,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 0))) (htZ C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 2)),
         flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 1))}:
         Set (CoordinateField Omega C.1.1))=⊤:=by
   intro C
   rw [hembZ C]
   simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu] using
     flag_generators_z Omega C.1.1 lam mu nu C.2
 have hfamilyZ:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:sZ => C.1.1) hinjZ lam mu nu zOrder
   htZ hgenZ G T hG
   (fun C => regularComponent_G_mem Omega G T H C.1)
   (fun C => regularComponent_T_mem Omega G T H C.1)
   hproper
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).2
   p.all q.all (p.yz+p.all) (q.yz+q.all)
   (flagMixed p q unitZFlag) hTne
   (by simpa only [gCaps] using gCaps.zOuter)
   (by simpa only [tCaps] using tCaps.zOuter)
   (by simpa only [gCaps] using gCaps.zTotal)
   (by simpa only [tCaps] using tCaps.zTotal)
   (z_flag_trapezoid_budget p q)
 have hsumZ:
     (∑ C:RegularComponent Omega G T H,
       coordinateDegree Omega (CoordinateField Omega C.1) (zProj C)) ≤
       flagMixed p q unitZFlag:=by
   have hsplit:=sum_coordinateOfGate_degree_eq
     (K:=Omega)
     (E:=fun C:RegularComponent Omega G T H => CoordinateField Omega C.1)
     (x:=fun C => coordinate Omega C.1 2) hZ
   change (∑ C:RegularComponent Omega G T H,
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate (coordinate Omega C.1 2) (hZ C))) ≤ _
   rw [hsplit]
   calc
     (∑ C:sZ,
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1.1)
           (coordinate Omega C.1.1 2) C.2).toRingHom.toAlgebra
        Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)))=
         ∑ C:sZ,
           (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
             (elementEmbedding Omega (CoordinateField Omega C.1.1)
               (flagEvaluation Omega C.1.1 lam mu nu
                 (MvPolynomial.X (zOrder 0))) (htZ C)).toRingHom.toAlgebra
            Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembZ C]
     _ ≤ _:=hfamilyZ.2
 let sU:={C:RegularComponent Omega G T H//
   Transcendental Omega (affineU Omega C.1 D.lam)}
 have hinjU:Function.Injective (fun C:sU => C.1.1):=by
   intro C E hCE
   apply Subtype.ext
   apply Subtype.ext
   exact hCE
 let htU:∀ C:sU,
     Transcendental Omega
       (flagEvaluation Omega C.1.1 lam mu nu
         (MvPolynomial.X (uOrder 0))):=by
   intro C
   simpa [uOrder,lam,mu,nu] using C.2
 have hembU (C:sU):
     elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 0))) (htU C)=
       elementEmbedding Omega (CoordinateField Omega C.1.1)
         (affineU Omega C.1.1 D.lam) C.2:=
   elementEmbedding_congr (htU C) C.2
     (by simp [uOrder,lam,mu,nu])
 have hgenU:∀ C:sU,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 0))) (htU C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 2)),
         flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 1))}:
         Set (CoordinateField Omega C.1.1))=⊤:=by
   intro C
   rw [hembU C]
   simpa [uOrder,lam,mu,nu] using
     flag_generators_u Omega C.1.1 lam mu nu C.2
 have hfamilyU:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:sU => C.1.1) hinjU lam mu nu uOrder
   htU hgenU G T hG
   (fun C => regularComponent_G_mem Omega G T H C.1)
   (fun C => regularComponent_T_mem Omega G T H C.1)
   hproper
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).1
   p.all q.all (p.zOnly+p.yz+p.all)
   (q.zOnly+q.yz+q.all) (flagMixed p q unitYZFlag) hTne
   (by simpa only [gCaps] using gCaps.uOuter)
   (by simpa only [tCaps] using tCaps.uOuter)
   (by simpa only [gCaps] using gCaps.uTotal)
   (by simpa only [tCaps] using tCaps.uTotal)
   (u_flag_trapezoid_budget p q)
 have hsumU:
     (∑ C:RegularComponent Omega G T H,
       coordinateDegree Omega (CoordinateField Omega C.1) (uProj C)) ≤
       flagMixed p q unitYZFlag:=by
   have hsplit:=sum_coordinateOfGate_degree_eq
     (K:=Omega)
     (E:=fun C:RegularComponent Omega G T H => CoordinateField Omega C.1)
     (x:=fun C => affineU Omega C.1 D.lam) D.uGate
   change (∑ C:RegularComponent Omega G T H,
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C))) ≤ _
   rw [hsplit]
   calc
     (∑ C:sU,
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1.1)
           (affineU Omega C.1.1 D.lam) C.2).toRingHom.toAlgebra
        Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)))=
         ∑ C:sU,
           (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
             (elementEmbedding Omega (CoordinateField Omega C.1.1)
               (flagEvaluation Omega C.1.1 lam mu nu
                 (MvPolynomial.X (uOrder 0))) (htU C)).toRingHom.toAlgebra
            Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembU C]
     _ ≤ _:=hfamilyU.2
 let htV:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu
         (MvPolynomial.X (vOrder 0))):=by
   intro C
   simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using
     D.allAffineTranscendental C
 have hembV (C:RegularComponent Omega G T H):
     elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 0))) (htV C)=
       elementEmbedding Omega (CoordinateField Omega C.1)
         (affineV Omega C.1 D.mu (D.mu*D.lam))
           (D.allAffineTranscendental C):=
   elementEmbedding_congr (htV C) (D.allAffineTranscendental C)
     (by simp [vOrder,Equiv.swap_apply_def,lam,mu,nu])
 have hgenV:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 0))) (htV C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 2)),
         flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 1))}:
         Set (CoordinateField Omega C.1))=⊤:=by
   intro C
   rw [hembV C]
   simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using
     flag_generators_v Omega C.1 lam mu nu (D.allAffineTranscendental C)
 have hinjV:Function.Injective
     (fun C:RegularComponent Omega G T H => C.1):=by
   intro C E hCE
   exact Subtype.ext hCE
 have hfamilyV:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:RegularComponent Omega G T H => C.1)
   hinjV lam mu nu vOrder htV hgenV G T hG
   (fun C => regularComponent_G_mem Omega G T H C)
   (fun C => regularComponent_T_mem Omega G T H C)
   hproper
   (flag_v_outer_positive_of_directional D.lam D.mu G D.directional)
   (p.yz+p.all) (q.yz+q.all)
   (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all)
   (flagMixed p q unitAllFlag) hTne
   (by simpa only [gCaps] using gCaps.vOuter)
   (by simpa only [tCaps] using tCaps.vOuter)
   (by simpa only [gCaps] using gCaps.vTotal)
   (by simpa only [tCaps] using tCaps.vTotal)
   (v_flag_trapezoid_budget p q)
 have hsumV:
     (∑ C:RegularComponent Omega G T H,
       coordinateDegree Omega (CoordinateField Omega C.1) (vProj C)) ≤
       flagMixed p q unitAllFlag:=by
   calc
     _=∑ C:RegularComponent Omega G T H,
         (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (affineV Omega C.1 D.mu (D.mu*D.lam))
               (D.allAffineTranscendental C)).toRingHom.toAlgebra
          Module.finrank (RatFunc Omega) (CoordinateField Omega C.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rfl
     _=∑ C:RegularComponent Omega G T H,
         (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (flagEvaluation Omega C.1 lam mu nu
               (MvPolynomial.X (vOrder 0))) (htV C)).toRingHom.toAlgebra
          Module.finrank (RatFunc Omega) (CoordinateField Omega C.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembV C]
     _ ≤ _:=hfamilyV.2
 have hvValue (C:RegularComponent Omega G T H):
     coordinateValue Omega (CoordinateField Omega C.1) (vProj C)=
       affineV Omega C.1 D.mu (D.mu*D.lam):=by
   dsimp only [vProj,coordinateValue,SeparableCoordinate.value,Sum.elim_inr]
   exact elementEmbedding_variable Omega (CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam))
     (D.allAffineTranscendental C)
 refine {
   zProjection:=zProj
   yzProjection:=uProj
   allProjection:=vProj
   zValue:=?_
   allTranscendental:=?_
   zPole_eq:=?_
   yzPole_eq:=?_
   allPole_eq:=?_
   sum_zDegree_le:=hsumZ
   sum_yzDegree_le:=hsumU
   sum_allDegree_le:=hsumV}
 · intro C
   exact coordinateOfGate_value _ _
 · intro C
   rw [hvValue C]
   exact D.allAffineTranscendental C
 · intro C v
   rw [exponentSetPoleWeight_unitZ]
   change _=RCN187.poleOrder v.val _
   rw [coordinateOfGate_value]
 · intro C v
   rw [exponentSetPoleWeight_unitYZ]
   change _=RCN187.poleOrder v.val _
   rw [coordinateOfGate_value]
   rw [←D.uValue C]
   exact (D.uPole C v).symm
 · intro C v
   rw [exponentSetPoleWeight_unitAll]
   change _=RCN187.poleOrder v.val _
   rw [hvValue C, ←D.allValue C]
   exact (D.allPole C v).symm
theorem exists_adaptiveUnitProjectionFamily_of_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hY:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   Nonempty (AdaptiveUnitProjectionFamily base p q):=by
 obtain ⟨D⟩:=exists_adaptiveNestedProjectionData base hY hZ hSderiv
 exact ⟨adaptiveUnitProjectionFamily_of_nested p q base hY hZ hSderiv D
   hG hproper hGsupport hTsupport⟩
end
end ProximityPrize.SubmissionLower.RCN039
end PackedLegacy_Y0

/-! Packed from ProximityPrize.SubmissionLower.E1. -/
section PackedLegacy_E1
namespace ProximityPrize.SubmissionLower.RCN240
open scoped Classical BigOperators
open RCN159 RCN164 RCN275 RCN276 RCN174 RCN286 RCN266 RCN238 RCN095
set_option maxHeartbeats 1500000
set_option maxRecDepth 50000
def factorPrimaryForDirection
   (p:Profile) (direction flag:FlagDegree):ℕ:=
 flagMixed flag direction direction*p.degreeIncidence^2+
   2*flagMixed flag direction unitYZFlag*
     p.degreeIncidence*p.unitIncidence+
   flagMixed flag unitYZFlag unitYZFlag*p.unitIncidence^2
def factorZTailForDirection
   (p:Profile) (direction flag:FlagDegree):ℕ:=
 (p.errors+1)*p.gap*
   (flagMixed flag direction unitZFlag*p.degreeIncidence+
     flagMixed flag unitYZFlag unitZFlag*p.unitIncidence)
def factorYZTailForDirection
   (p:Profile) (direction flag:FlagDegree):ℕ:=
 (p.errors+1)*p.gap*
   (flagMixed flag direction unitYZFlag*p.degreeIncidence+
     flagMixed flag unitYZFlag unitYZFlag*p.unitIncidence)
def factorRegularLedgerYZForDirection
   (p:Profile) (direction flag:FlagDegree):ℕ:=
 factorPrimaryForDirection p direction flag+
   factorZTailForDirection p direction flag+
   factorYZTailForDirection p direction flag
def factorYZTail (p:Profile) (flag:FlagDegree):ℕ:=
 factorYZTailForDirection p p.agreementDirection flag
def factorRegularLedgerYZ (p:Profile) (flag:FlagDegree):ℕ:=
 factorRegularLedgerYZForDirection p p.agreementDirection flag
def regularNumeratorYZ (p:Profile):ℕ:=
 factorRegularLedgerYZ p p.rectangularSurfaceFlag
noncomputable section
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
def factorDegreeCostYZ (p:Profile) (direction:FlagDegree)
   (flag:FlagDegree):ℕ:=
 (flagMixed flag direction direction*
     p.degreeIncidence+
   flagMixed flag direction unitYZFlag*p.unitIncidence)+
 (p.errors+1)*p.gap*
   (flagMixed flag direction unitZFlag+
     flagMixed flag direction unitYZFlag)
def factorUnitCostYZ (p:Profile) (direction:FlagDegree)
   (flag:FlagDegree):ℕ:=
 (flagMixed flag direction unitYZFlag*p.degreeIncidence+
   flagMixed flag unitYZFlag unitYZFlag*p.unitIncidence)+
 (p.errors+1)*p.gap*
   (flagMixed flag unitYZFlag unitZFlag+
     flagMixed flag unitYZFlag unitYZFlag)
theorem incidence_cost_eq_factorRegularLedgerYZ
   (p:Profile) (direction flag:FlagDegree)
   :
   p.degreeIncidence*factorDegreeCostYZ p direction flag+
     p.unitIncidence*factorUnitCostYZ p direction flag=
     factorRegularLedgerYZForDirection p direction flag:=by
 simp only [factorDegreeCostYZ,factorUnitCostYZ]
 simp only [factorRegularLedgerYZForDirection,factorPrimaryForDirection,
   factorZTailForDirection,factorYZTailForDirection]
 ring
end
end ProximityPrize.SubmissionLower.RCN240
end PackedLegacy_E1

/-! Packed from ProximityPrize.SubmissionLower.EI. -/
section PackedLegacy_EI
namespace ProximityPrize.SubmissionLower.RCN131
open scoped Classical BigOperators
open RCN095 RCN130 RCN240 RCN276 RCN266 RCN222 RCN275 RCN174 RCN319
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
theorem linear_cost_cumulative (cz cy ca:ℕ) (f:FlagDegree)
   (hzy:cz ≤ cy) (hya:cy ≤ ca):
   f.zOnly*cz+f.yz*cy+f.all*ca=
     cz*(f.zOnly+f.yz+f.all)+
       (cy-cz)*(f.yz+f.all)+(ca-cy)*f.all:=by
 have hy:cz+(cy-cz)=cy:=by omega
 have ha:cz+(cy-cz)+(ca-cy)=ca:=by omega
 calc
   f.zOnly*cz+f.yz*cy+f.all*ca=
       f.zOnly*cz+f.yz*(cz+(cy-cz))+
         f.all*(cz+(cy-cz)+(ca-cy)):=by rw [ha,hy]
   _=_:=by ring
variable {K:Type} [Field K]
end
end ProximityPrize.SubmissionLower.RCN131
end PackedLegacy_EI

/-! Packed from ProximityPrize.SubmissionLower.Y5. -/
section PackedLegacy_Y5
namespace ProximityPrize.SubmissionLower.RCN084
open scoped Classical BigOperators
open RCN095 RCN121 RCN071 RCN137 RCN264 RCN341 RCN037 RCN039 RCN046 RCN237 RCN002 RCN005 RCN003 RCN001
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 300000
variable {K:Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 3) K
def exactFlag (A:Poly):FlagDegree:=
 let s:=MvPolynomial.weightedTotalDegree flagSWeights A
 let m:=MvPolynomial.weightedTotalDegree flagYSWeights A
 let t:=MvPolynomial.weightedTotalDegree flagTotalWeights A
 ⟨t-m,m-s,s⟩
theorem flag_weights_nested (A:Poly):
   MvPolynomial.weightedTotalDegree flagSWeights A ≤
     MvPolynomial.weightedTotalDegree flagYSWeights A∧
   MvPolynomial.weightedTotalDegree flagYSWeights A ≤
     MvPolynomial.weightedTotalDegree flagTotalWeights A:=by
 constructor
 all_goals
   apply Finset.sup_le
   intro d hd
 · have h:=MvPolynomial.le_weightedTotalDegree flagYSWeights hd
   rw [flag_weight_fin3] at h ⊢
   change d 0*0+d 1*1+d 2*0 ≤ _
   change d 0*1+d 1*1+d 2*0 ≤ _ at h
   simpa using (show d 1 ≤ MvPolynomial.weightedTotalDegree flagYSWeights A by omega)
 · have h:=MvPolynomial.le_weightedTotalDegree flagTotalWeights hd
   rw [flag_weight_fin3] at h ⊢
   change d 0*1+d 1*1+d 2*0 ≤ _
   change d 0*1+d 1*1+d 2*1 ≤ _ at h
   omega
theorem exactFlag_cumulative (A:Poly):
   (exactFlag A).all=MvPolynomial.weightedTotalDegree flagSWeights A∧
   (exactFlag A).yz+(exactFlag A).all=MvPolynomial.weightedTotalDegree flagYSWeights A∧
   (exactFlag A).zOnly+(exactFlag A).yz+(exactFlag A).all=
     MvPolynomial.weightedTotalDegree flagTotalWeights A:=by
 have h:=flag_weights_nested A
 dsimp [exactFlag]
 omega
theorem polynomialIn_exactFlag (A:Poly):PolynomialInFlag (exactFlag A) A:=by
 intro d hd
 have hs:=MvPolynomial.le_weightedTotalDegree flagSWeights hd
 have hm:=MvPolynomial.le_weightedTotalDegree flagYSWeights hd
 have ht:=MvPolynomial.le_weightedTotalDegree flagTotalWeights hd
 rw [flag_weight_fin3] at hs hm ht
 have hc:=exactFlag_cumulative A
 change d 0*0+d 1*1+d 2*0 ≤ _ at hs
 change d 0*1+d 1*1+d 2*0 ≤ _ at hm
 change d 0*1+d 1*1+d 2*1 ≤ _ at ht
 unfold InFlag
 omega
theorem inFlag_weight_caps (A:Poly) (p:FlagDegree) (hA:PolynomialInFlag p A):
   MvPolynomial.weightedTotalDegree flagSWeights A ≤ p.all∧
   MvPolynomial.weightedTotalDegree flagYSWeights A ≤ p.yz+p.all∧
   MvPolynomial.weightedTotalDegree flagTotalWeights A ≤ p.zOnly+p.yz+p.all:=by
 refine ⟨?_,?_,?_⟩
 all_goals
   apply Finset.sup_le
   intro d hd
   have h:=hA d hd
   rw [flag_weight_fin3]
 · change d 0*0+d 1*1+d 2*0 ≤ _;exact by simpa using h.1
 · change d 0*1+d 1*1+d 2*0 ≤ _;exact by simpa using h.2.1
 · change d 0*1+d 1*1+d 2*1 ≤ _;exact by simpa using h.2.2
theorem sum_flagMixed_le_of_cumulative {I:Type*} [Fintype I]
   (f:I → FlagDegree) (p q r:FlagDegree)
   (hs:(∑ i,(f i).all) ≤ p.all)
   (hm:(∑ i,((f i).yz+(f i).all)) ≤ p.yz+p.all)
   (ht:(∑ i,((f i).zOnly+(f i).yz+(f i).all)) ≤ p.zOnly+p.yz+p.all):
   (∑ i,flagMixed (f i) q r) ≤ flagMixed p q r:=by
 let z:=flagMixed unitZFlag q r
 let y:=flagMixed unitYZFlag q r
 let a:=flagMixed unitAllFlag q r
 have hzy:z ≤ y:=by simp [z,y,flagMixed,unitZFlag,unitYZFlag];nlinarith
 have hya:y ≤ a:=by simp [y,a,flagMixed,unitYZFlag,unitAllFlag];nlinarith
 have heq (v:FlagDegree):flagMixed v q r=
     z*(v.zOnly+v.yz+v.all)+(y-z)*(v.yz+v.all)+(a-y)*v.all:=by
   calc
     flagMixed v q r=v.zOnly*z+v.yz*y+v.all*a:=by
       simp only [z,y,a,flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
       ring
     _=_:=RCN131.linear_cost_cumulative z y a v hzy hya
 rw [Finset.sum_congr rfl (fun i _↦heq (f i)),heq p]
 simp only [Finset.sum_add_distrib, ←Finset.mul_sum]
 simpa only [Finset.sum_add_distrib] using Nat.add_le_add
   (Nat.add_le_add (Nat.mul_le_mul_left z ht) (Nat.mul_le_mul_left (y-z) hm))
   (Nat.mul_le_mul_left (a-y) hs)
end
end ProximityPrize.SubmissionLower.RCN084
end PackedLegacy_Y5
end Compact_PackedLegacyCore2
