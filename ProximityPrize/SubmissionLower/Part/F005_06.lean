import ProximityPrize.SubmissionLower.Part.F005_05
section Compact_PackedLegacyCore2
section PackedLegacy_Y7
namespace ProximityPrize.SubmissionLower.RCN093
open scoped Classical BigOperators
open RCN002 RCN005
 RCN022 RCN011
 RCN371
open RCN125 RCN124
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable (K:Type) [Field K]
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]

theorem flagEvaluation_flag (lam μ ν:K)
   (F:MvPolynomial (Fin 3) K):
   flagEvaluation K P lam μ ν (flagAlgHom lam μ ν F)=
     coordinateEvaluation K P F:=by
 change MvPolynomial.eval₂Hom (algebraMap K (CoordinateField K P))
     ![coordinate K P 0+lam • coordinate K P 2,
       coordinate K P 1+μ • coordinate K P 0+ν • coordinate K P 2,
       coordinate K P 2] (flagAlgHom lam μ ν F)=_
 rw [show lam • coordinate K P 2=
     algebraMap K (CoordinateField K P) lam*coordinate K P 2 by
       simp [Algebra.smul_def],
   show μ • coordinate K P 0=
     algebraMap K (CoordinateField K P) μ*coordinate K P 0 by
       simp [Algebra.smul_def],
   show ν • coordinate K P 2=
     algebraMap K (CoordinateField K P) ν*coordinate K P 2 by
       simp [Algebra.smul_def],
   eval₂Hom_flag_at_affine]
 rw [coordinateEvaluation_eq_aeval]
 have hx:(![coordinate K P 0,coordinate K P 1,coordinate K P 2]:
     Fin 3 → CoordinateField K P)=coordinate K P:=by
   funext i
   fin_cases i <;> rfl
 rw [hx]
 exact (MvPolynomial.aeval_eq_eval₂Hom (coordinate K P) F).symm
theorem flagEvaluation_kernel_contract (lam μ ν:K):
   (RingHom.ker (flagEvaluation K P lam μ ν).toRingHom).comap
       (flagAlgHom lam μ ν).toRingHom=P:=by
 rw [RingHom.comap_ker]
 have hcomp:(flagEvaluation K P lam μ ν).comp (flagAlgHom lam μ ν)=
     coordinateEvaluation K P:=by
   apply AlgHom.ext
   intro F
   exact flagEvaluation_flag K P lam μ ν F
 have hring:=congrArg
   (fun f:MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K P↦
     f.toRingHom) hcomp
 rw [show (flagEvaluation K P lam μ ν).toRingHom.comp
     (flagAlgHom lam μ ν).toRingHom=
     (coordinateEvaluation K P).toRingHom from hring,
   coordinateEvaluation_ker]
private theorem top_of_affine_flag_mem
   [Algebra (RatFunc K) (CoordinateField K P)]
   [IsScalarTower K (RatFunc K) (CoordinateField K P)]
   (lam μ ν:K)
   (L:IntermediateField (RatFunc K) (CoordinateField K P))
   (hU:affineU K P lam∈L) (hV:affineV K P μ ν∈L)
   (hZ:coordinate K P 2∈L):L=⊤:=by
 have hlam:algebraMap K (CoordinateField K P) lam∈L:=by
   have h:=L.algebraMap_mem (algebraMap K (RatFunc K) lam)
   simpa only [IsScalarTower.algebraMap_apply K (RatFunc K)
     (CoordinateField K P)] using h
 have hμ:algebraMap K (CoordinateField K P) μ∈L:=by
   have h:=L.algebraMap_mem (algebraMap K (RatFunc K) μ)
   simpa only [IsScalarTower.algebraMap_apply K (RatFunc K)
     (CoordinateField K P)] using h
 have hν:algebraMap K (CoordinateField K P) ν∈L:=by
   have h:=L.algebraMap_mem (algebraMap K (RatFunc K) ν)
   simpa only [IsScalarTower.algebraMap_apply K (RatFunc K)
     (CoordinateField K P)] using h
 have hY:coordinate K P 0∈L:=by
   have h:=L.sub_mem hU (L.mul_mem hlam hZ)
   simpa only [affineU,Algebra.smul_def,add_sub_cancel_right] using h
 have hS:coordinate K P 1∈L:=by
   have h:=L.sub_mem hV
     (L.add_mem (L.mul_mem hμ hY) (L.mul_mem hν hZ))
   have heq:affineV K P μ ν-
       (algebraMap K (CoordinateField K P) μ*coordinate K P 0+
         algebraMap K (CoordinateField K P) ν*coordinate K P 2)=
       coordinate K P 1:=by
     simp only [affineV,Algebra.smul_def]
     ring
   rwa [heq] at h
 have hcoords:Set.range (coordinate K P) ⊆ L.restrictScalars K:=by
   rintro x ⟨i,rfl⟩
   fin_cases i
   · exact hY
   · exact hS
   · exact hZ
 have htop:L.restrictScalars K=⊤:=by
   apply top_unique
   rw [←adjoin_coordinates_eq_top K P]
   exact IntermediateField.adjoin_le_iff.mpr hcoords
 exact (IntermediateField.restrictScalars_eq_top_iff (K:=K)).mp htop
theorem flag_generators_u (lam μ ν:K)
   (hU:Transcendental K (affineU K P lam)):
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     (elementEmbedding K (CoordinateField K P) (affineU K P lam)
       hU).toRingHom.toAlgebra
   IntermediateField.adjoin (RatFunc K)
     ({coordinate K P 2,affineV K P μ ν}:
       Set (CoordinateField K P))=⊤:=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=
   (elementEmbedding K (CoordinateField K P) (affineU K P lam)
     hU).toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) (CoordinateField K P):=
   IsScalarTower.of_algebraMap_eq fun c↦
     ((elementEmbedding K (CoordinateField K P) (affineU K P lam)
       hU).commutes c).symm
 let L:IntermediateField (RatFunc K) (CoordinateField K P):=
   IntermediateField.adjoin (RatFunc K)
     {coordinate K P 2,affineV K P μ ν}
 have hZ:coordinate K P 2∈L:=
   IntermediateField.mem_adjoin_pair_left _ _ _
 have hV:affineV K P μ ν∈L:=
   IntermediateField.mem_adjoin_pair_right _ _ _
 have hbase:=L.algebraMap_mem
   (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
 have hUmem:affineU K P lam∈L:=by
   change elementEmbedding K (CoordinateField K P) (affineU K P lam) hU
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)∈L at hbase
   rwa [elementEmbedding_variable] at hbase
 exact top_of_affine_flag_mem K P lam μ ν L hUmem hV hZ
theorem flag_generators_v (lam μ ν:K)
   (hV:Transcendental K (affineV K P μ ν)):
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     (elementEmbedding K (CoordinateField K P) (affineV K P μ ν)
       hV).toRingHom.toAlgebra
   IntermediateField.adjoin (RatFunc K)
     ({coordinate K P 2,affineU K P lam}:
       Set (CoordinateField K P))=⊤:=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=
   (elementEmbedding K (CoordinateField K P) (affineV K P μ ν)
     hV).toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) (CoordinateField K P):=
   IsScalarTower.of_algebraMap_eq fun c↦
     ((elementEmbedding K (CoordinateField K P) (affineV K P μ ν)
       hV).commutes c).symm
 let L:IntermediateField (RatFunc K) (CoordinateField K P):=
   IntermediateField.adjoin (RatFunc K)
     {coordinate K P 2,affineU K P lam}
 have hZ:coordinate K P 2∈L:=
   IntermediateField.mem_adjoin_pair_left _ _ _
 have hU:affineU K P lam∈L:=
   IntermediateField.mem_adjoin_pair_right _ _ _
 have hbase:=L.algebraMap_mem
   (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
 have hVmem:affineV K P μ ν∈L:=by
   change elementEmbedding K (CoordinateField K P) (affineV K P μ ν) hV
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)∈L at hbase
   rwa [elementEmbedding_variable] at hbase
 exact top_of_affine_flag_mem K P lam μ ν L hU hVmem hZ
theorem flag_generators_z (lam μ ν:K)
   (hZ:Transcendental K (coordinate K P 2)):
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     (elementEmbedding K (CoordinateField K P) (coordinate K P 2)
       hZ).toRingHom.toAlgebra
   IntermediateField.adjoin (RatFunc K)
     ({affineU K P lam,affineV K P μ ν}:
       Set (CoordinateField K P))=⊤:=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=
   (elementEmbedding K (CoordinateField K P) (coordinate K P 2)
     hZ).toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) (CoordinateField K P):=
   IsScalarTower.of_algebraMap_eq fun c↦
     ((elementEmbedding K (CoordinateField K P) (coordinate K P 2)
       hZ).commutes c).symm
 let L:IntermediateField (RatFunc K) (CoordinateField K P):=
   IntermediateField.adjoin (RatFunc K)
     {affineU K P lam,affineV K P μ ν}
 have hU:affineU K P lam∈L:=
   IntermediateField.mem_adjoin_pair_left _ _ _
 have hV:affineV K P μ ν∈L:=
   IntermediateField.mem_adjoin_pair_right _ _ _
 have hbase:=L.algebraMap_mem
   (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
 have hZmem:coordinate K P 2∈L:=by
   change elementEmbedding K (CoordinateField K P) (coordinate K P 2) hZ
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)∈L at hbase
   rwa [elementEmbedding_variable] at hbase
 exact top_of_affine_flag_mem K P lam μ ν L hU hV hZmem
section Family
variable {I:Type} [Fintype I]
 (Q:I → Ideal (MvPolynomial (Fin 3) K)) [∀ i,(Q i).IsPrime]
theorem flagEvaluation_kernel_family_injective
   (hinj:Function.Injective Q) (lam μ ν:K):
   Function.Injective (fun i↦
     RingHom.ker (flagEvaluation K (Q i) lam μ ν).toRingHom):=by
 intro i j hij
 apply hinj
 have hc:=congrArg (Ideal.comap (flagAlgHom lam μ ν).toRingHom) hij
 simpa only [flagEvaluation_kernel_contract] using hc
theorem finite_sum_flag_finrank_trapezoid
   (hinj:Function.Injective Q) (lam μ ν:K)
   (order:Fin 3 ≃ Fin 3)
   (ht:∀ i,Transcendental K
     (flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 0))))
   (hgen:∀ i,
     letI:Algebra (RatFunc K) (CoordinateField K (Q i)):=
       (elementEmbedding K (CoordinateField K (Q i))
         (flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 0)))
         (ht i)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 2)),
         flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 1))}:
         Set (CoordinateField K (Q i)))=⊤)
   (G H:MvPolynomial (Fin 3) K) (hG:Irreducible G)
   (hGmem:∀ i,G∈Q i) (hHmem:∀ i,H∈Q i)
   (hproper:¬ G∣H)
   (hpositive:0 <
     (planeMap K order (flagAlgHom lam μ ν G)).natDegree)
   (n mCap totalG totalH cap:ℕ) (hHne:H≠0)
   (hGouter:(planeMap K order
     (flagAlgHom lam μ ν G)).natDegree ≤ n)
   (hHouter:(planeMap K order
     (flagAlgHom lam μ ν H)).natDegree ≤ mCap)
   (hGsupport:∀ d∈(rationalMap K order
     (flagAlgHom lam μ ν G)).support,d 0+d 1 ≤ totalG)
   (hHsupport:∀ d∈(rationalMap K order
     (flagAlgHom lam μ ν H)).support,d 0+d 1 ≤ totalH)
   (hbudget:∀ m,m ≤ mCap →
     m*totalG+n*totalH-m*n ≤ cap):
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (Q i)):=
     fun i↦(elementEmbedding K (CoordinateField K (Q i))
       (flagEvaluation K (Q i) lam μ ν (MvPolynomial.X (order 0)))
       (ht i)).toRingHom.toAlgebra
   (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (Q i)))∧
     (∑ i,Module.finrank (RatFunc K) (CoordinateField K (Q i))) ≤ cap:=by
 let e:∀ i,MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K (Q i):=
   fun i↦flagEvaluation K (Q i) lam μ ν
 have hGroot:∀ i,e i (flagAlgHom lam μ ν G)=0:=by
   intro i
   rw [show e i (flagAlgHom lam μ ν G)=coordinateEvaluation K (Q i) G
     from flagEvaluation_flag K (Q i) lam μ ν G]
   change G∈RingHom.ker (coordinateEvaluation K (Q i)).toRingHom
   rw [coordinateEvaluation_ker]
   exact hGmem i
 have hHroot:∀ i,e i (flagAlgHom lam μ ν H)=0:=by
   intro i
   rw [show e i (flagAlgHom lam μ ν H)=coordinateEvaluation K (Q i) H
     from flagEvaluation_flag K (Q i) lam μ ν H]
   change H∈RingHom.ker (coordinateEvaluation K (Q i)).toRingHom
   rw [coordinateEvaluation_ker]
   exact hHmem i
 exact finite_sum_finrank_bound_trapezoid K order
   (fun i↦CoordinateField K (Q i)) e ht hgen
   (flagEvaluation_kernel_family_injective K Q hinj lam μ ν)
   (flagAlgHom lam μ ν G) (flagAlgHom lam μ ν H)
   ((flag_irreducible_iff lam μ ν G).mpr hG)
   hGroot hHroot (by simpa only [flag_dvd_iff] using hproper) hpositive
   n mCap totalG totalH cap (flag_ne_zero lam μ ν hHne)
   hGouter hHouter hGsupport hHsupport hbudget
end Family
end
end ProximityPrize.SubmissionLower.RCN093
end PackedLegacy_Y7

/-! Packed from ProximityPrize.SubmissionLower.BB. -/
section PackedLegacy_BB
namespace ProximityPrize.SubmissionLower.RCN118
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN272
 RCN273
open RCN323 RCN075 RCN095 RCN114 RCN187 RCN295
noncomputable section
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
structure PrincipalCycleBudget
   {G T H:MvPolynomial (Fin 3) Ω}
   (E:Finset (Fin 3 →₀ ℕ)) (separator:Fin 3)
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (B:GenericExactPolePolynomial G T H E separator hseparator hproj)
   (wholeCap:ℕ) where
 cost:RegularComponent Ω G T H → ℕ
 cycle_le:∀ C:RegularComponent Ω G T H,
   let htr:=hseparator C
   letI:Algebra (Polynomial Ω) (CoordinateRing Ω C.1):=
     quotientPolynomialAlgebra Ω C.1 separator
   letI:Algebra (Polynomial Ω) (CoordinateField Ω C.1):=
     polynomialBaseAlgebra Ω C.1 separator
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     rationalBaseAlgebra Ω C.1 separator htr
   letI:=quotientBaseScalarTower Ω C.1 separator
   letI:=polynomialBaseScalarTower Ω C.1 separator
   letI:=quotientFractionScalarTower Ω C.1 separator
   letI:=polynomialRationalScalarTower Ω C.1 separator htr
   letI:=rationalBaseScalarTower Ω C.1 separator htr
   letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).1
   letI:Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).2
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) B.polynomial
   let hb:b≠0:=coordinate_eval_ne_zero_of_not_mem
     C.1 B.polynomial (B.proper C)
   (∑ v∈RCN026.placesFor Ω
       (CoordinateField Ω C.1) b hb,
     RCN346.poleOrder Ω (CoordinateField Ω C.1) v b) ≤
       (cost C:ℤ)
 sum_cost_le:(∑ C:RegularComponent Ω G T H,cost C) ≤ wholeCap
structure FlagProjectionCycleBudget
   {G T H:MvPolynomial (Fin 3) Ω}
   (p:FlagDegree) (separator:Fin 3)
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (B:GenericExactPolePolynomial G T H (flagSupport p) separator
     hseparator hproj)
   (zCap yzCap allCap:ℕ) where
 zCost:RegularComponent Ω G T H → ℕ
 yzCost:RegularComponent Ω G T H → ℕ
 allCost:RegularComponent Ω G T H → ℕ
 cycle_le:∀ C:RegularComponent Ω G T H,
   let htr:=hseparator C
   letI:Algebra (Polynomial Ω) (CoordinateRing Ω C.1):=
     quotientPolynomialAlgebra Ω C.1 separator
   letI:Algebra (Polynomial Ω) (CoordinateField Ω C.1):=
     polynomialBaseAlgebra Ω C.1 separator
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     rationalBaseAlgebra Ω C.1 separator htr
   letI:=quotientBaseScalarTower Ω C.1 separator
   letI:=polynomialBaseScalarTower Ω C.1 separator
   letI:=quotientFractionScalarTower Ω C.1 separator
   letI:=polynomialRationalScalarTower Ω C.1 separator htr
   letI:=rationalBaseScalarTower Ω C.1 separator htr
   letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).1
   letI:Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).2
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) B.polynomial
   let hb:b≠0:=coordinate_eval_ne_zero_of_not_mem
     C.1 B.polynomial (B.proper C)
   (∑ v∈RCN026.placesFor Ω
       (CoordinateField Ω C.1) b hb,
     RCN346.poleOrder Ω (CoordinateField Ω C.1) v b) ≤
       ((p.zOnly*zCost C+p.yz*yzCost C+
         p.all*allCost C:ℕ):ℤ)
 sum_zCost_le:(∑ C:RegularComponent Ω G T H,zCost C) ≤ zCap
 sum_yzCost_le:(∑ C:RegularComponent Ω G T H,yzCost C) ≤ yzCap
 sum_allCost_le:(∑ C:RegularComponent Ω G T H,allCost C) ≤ allCap
def FlagProjectionCycleBudget.ofNestedProjectionBudgets
   {G T H:MvPolynomial (Fin 3) Ω}
   {p:FlagDegree} {separator:Fin 3}
   {hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator)}
   {hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1}
   (B:GenericExactPolePolynomial G T H (flagSupport p) separator
     hseparator hproj)
   (BZ:GenericExactPolePolynomial G T H (flagSupport unitZFlag) separator
     hseparator hproj)
   (BYZ:GenericExactPolePolynomial G T H (flagSupport unitYZFlag) separator
     hseparator hproj)
   (BAll:GenericExactPolePolynomial G T H (flagSupport unitAllFlag) separator
     hseparator hproj)
   {zCap yzCap allCap:ℕ}
   (zBudget:PrincipalCycleBudget (flagSupport unitZFlag) separator
     hseparator hproj BZ zCap)
   (yzBudget:PrincipalCycleBudget (flagSupport unitYZFlag) separator
     hseparator hproj BYZ yzCap)
   (allBudget:PrincipalCycleBudget (flagSupport unitAllFlag) separator
     hseparator hproj BAll allCap):
   FlagProjectionCycleBudget p separator hseparator hproj B
     zCap yzCap allCap where
 zCost:=zBudget.cost
 yzCost:=yzBudget.cost
 allCost:=allBudget.cost
 sum_zCost_le:=zBudget.sum_cost_le
 sum_yzCost_le:=yzBudget.sum_cost_le
 sum_allCost_le:=allBudget.sum_cost_le
 cycle_le:=by
   intro C
   dsimp only
   let htr:=hseparator C
   letI:Algebra (Polynomial Ω) (CoordinateRing Ω C.1):=
     quotientPolynomialAlgebra Ω C.1 separator
   letI:Algebra (Polynomial Ω) (CoordinateField Ω C.1):=
     polynomialBaseAlgebra Ω C.1 separator
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     rationalBaseAlgebra Ω C.1 separator htr
   letI:=quotientBaseScalarTower Ω C.1 separator
   letI:=polynomialBaseScalarTower Ω C.1 separator
   letI:=quotientFractionScalarTower Ω C.1 separator
   letI:=polynomialRationalScalarTower Ω C.1 separator htr
   letI:=rationalBaseScalarTower Ω C.1 separator htr
   letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).1
   letI:Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1):=
     (hproj C separator htr).2
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) B.polynomial
   let hb:b≠0:=coordinate_eval_ne_zero_of_not_mem
     C.1 B.polynomial (B.proper C)
   let bZ:=MvPolynomial.eval₂Hom
     (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) BZ.polynomial
   let hbZ:bZ≠0:=coordinate_eval_ne_zero_of_not_mem
     C.1 BZ.polynomial (BZ.proper C)
   let bYZ:=MvPolynomial.eval₂Hom
     (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) BYZ.polynomial
   let hbYZ:bYZ≠0:=coordinate_eval_ne_zero_of_not_mem
     C.1 BYZ.polynomial (BYZ.proper C)
   let bAll:=MvPolynomial.eval₂Hom
     (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) BAll.polynomial
   let hbAll:bAll≠0:=coordinate_eval_ne_zero_of_not_mem
     C.1 BAll.polynomial (BAll.proper C)
   let W:=RCN026.placesFor Ω
     (CoordinateField Ω C.1) b hb
   have hZsupport:
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω C.1)
         (flagSupport unitZFlag)) ≤
       ∑ v∈RCN026.placesFor Ω
           (CoordinateField Ω C.1) bZ hbZ,
         RCN346.poleOrder Ω (CoordinateField Ω C.1) v bZ:=by
     exact support_sum_le_principal_poleMass_of_exact
       (coordinate Ω C.1) (flagSupport unitZFlag) bZ hbZ
       (BZ.exact_pole C) W
   have hYZsupport:
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω C.1)
         (flagSupport unitYZFlag)) ≤
       ∑ v∈RCN026.placesFor Ω
           (CoordinateField Ω C.1) bYZ hbYZ,
         RCN346.poleOrder Ω (CoordinateField Ω C.1) v bYZ:=by
     exact support_sum_le_principal_poleMass_of_exact
       (coordinate Ω C.1) (flagSupport unitYZFlag) bYZ hbYZ
       (BYZ.exact_pole C) W
   have hAllsupport:
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω C.1)
         (flagSupport unitAllFlag)) ≤
       ∑ v∈RCN026.placesFor Ω
           (CoordinateField Ω C.1) bAll hbAll,
         RCN346.poleOrder Ω (CoordinateField Ω C.1) v bAll:=by
     exact support_sum_le_principal_poleMass_of_exact
       (coordinate Ω C.1) (flagSupport unitAllFlag) bAll hbAll
       (BAll.exact_pole C) W
   have hZcycle:
       (∑ v∈RCN026.placesFor Ω
           (CoordinateField Ω C.1) bZ hbZ,
         RCN346.poleOrder Ω (CoordinateField Ω C.1) v bZ) ≤
       (zBudget.cost C:ℤ):=by
     simpa only using zBudget.cycle_le C
   have hYZcycle:
       (∑ v∈RCN026.placesFor Ω
           (CoordinateField Ω C.1) bYZ hbYZ,
         RCN346.poleOrder Ω (CoordinateField Ω C.1) v bYZ) ≤
       (yzBudget.cost C:ℤ):=by
     simpa only using yzBudget.cycle_le C
   have hAllcycle:
       (∑ v∈RCN026.placesFor Ω
           (CoordinateField Ω C.1) bAll hbAll,
         RCN346.poleOrder Ω (CoordinateField Ω C.1) v bAll) ≤
       (allBudget.cost C:ℤ):=by
     simpa only using allBudget.cycle_le C
   have hlocal:∀ v∈W,
       poleOrder v.val b ≤
         (p.zOnly:ℤ)*exponentSetPoleWeight v.val (coordinate Ω C.1)
             (flagSupport unitZFlag)+
         (p.yz:ℤ)*exponentSetPoleWeight v.val (coordinate Ω C.1)
             (flagSupport unitYZFlag)+
         (p.all:ℤ)*exponentSetPoleWeight v.val (coordinate Ω C.1)
             (flagSupport unitAllFlag):=by
     intro v _
     rw [B.exact_pole C v]
     exact exponentSetPoleWeight_flagSupport_le_three v.val
       (coordinate Ω C.1) p
   calc
     (∑ v∈W,RCN346.poleOrder Ω
         (CoordinateField Ω C.1) v b) ≤
         ∑ v∈W,
           ((p.zOnly:ℤ)*exponentSetPoleWeight v.val
               (coordinate Ω C.1) (flagSupport unitZFlag)+
            (p.yz:ℤ)*exponentSetPoleWeight v.val
               (coordinate Ω C.1) (flagSupport unitYZFlag)+
            (p.all:ℤ)*exponentSetPoleWeight v.val
               (coordinate Ω C.1) (flagSupport unitAllFlag)):=by
       apply Finset.sum_le_sum
       intro v hv
       exact hlocal v hv
     _=(p.zOnly:ℤ)*
           (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω C.1)
             (flagSupport unitZFlag))+
         (p.yz:ℤ)*
           (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω C.1)
             (flagSupport unitYZFlag))+
         (p.all:ℤ)*
           (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω C.1)
             (flagSupport unitAllFlag)):=by
       simp only [Finset.sum_add_distrib,Finset.mul_sum]
     _ ≤ (p.zOnly:ℤ)*(zBudget.cost C:ℤ)+
         (p.yz:ℤ)*(yzBudget.cost C:ℤ)+
         (p.all:ℤ)*(allBudget.cost C:ℤ):=by
       exact add_le_add
         (add_le_add
           (mul_le_mul_of_nonneg_left (hZsupport.trans hZcycle) (by positivity))
           (mul_le_mul_of_nonneg_left (hYZsupport.trans hYZcycle) (by positivity)))
         (mul_le_mul_of_nonneg_left (hAllsupport.trans hAllcycle) (by positivity))
     _=((p.zOnly*zBudget.cost C+p.yz*yzBudget.cost C+
         p.all*allBudget.cost C:ℕ):ℤ):=by
       push_cast
       ring
def FlagProjectionCycleBudget.combinedCost
   {G T H:MvPolynomial (Fin 3) Ω}
   {p:FlagDegree} {separator:Fin 3}
   {hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator)}
   {hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1}
   {B:GenericExactPolePolynomial G T H (flagSupport p) separator
     hseparator hproj}
   {zCap yzCap allCap:ℕ}
   (P:FlagProjectionCycleBudget p separator hseparator hproj B
     zCap yzCap allCap)
   (C:RegularComponent Ω G T H):ℕ:=
 p.zOnly*P.zCost C+p.yz*P.yzCost C+p.all*P.allCost C
theorem FlagProjectionCycleBudget.sum_combinedCost_le
   {G T H:MvPolynomial (Fin 3) Ω}
   {p:FlagDegree} {separator:Fin 3}
   {hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator)}
   {hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1}
   {B:GenericExactPolePolynomial G T H (flagSupport p) separator
     hseparator hproj}
   {zCap yzCap allCap:ℕ}
   (P:FlagProjectionCycleBudget p separator hseparator hproj B
     zCap yzCap allCap):
   (∑ C:RegularComponent Ω G T H,P.combinedCost C) ≤
     p.zOnly*zCap+p.yz*yzCap+p.all*allCap:=by
 rw [show (∑ C:RegularComponent Ω G T H,P.combinedCost C)=
     p.zOnly*(∑ C,P.zCost C)+
     p.yz*(∑ C,P.yzCost C)+
     p.all*(∑ C,P.allCost C) by
   simp only [FlagProjectionCycleBudget.combinedCost,
     Finset.sum_add_distrib,Finset.mul_sum]]
 exact Nat.add_le_add
   (Nat.add_le_add
     (Nat.mul_le_mul_left p.zOnly P.sum_zCost_le)
     (Nat.mul_le_mul_left p.yz P.sum_yzCost_le))
   (Nat.mul_le_mul_left p.all P.sum_allCost_le)
def FlagProjectionCycleBudget.toResidualComponentBudget
   {G T H:MvPolynomial (Fin 3) Ω}
   {p:FlagDegree} {separator:Fin 3}
   {hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator)}
   {hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1}
   {B:GenericExactPolePolynomial G T H (flagSupport p) separator
     hseparator hproj}
   {zCap yzCap allCap:ℕ}
   (P:FlagProjectionCycleBudget p separator hseparator hproj B
     zCap yzCap allCap):
   ResidualComponentBudget G T H
     (fun A↦A.support ⊆ flagSupport p)
     (p.zOnly*zCap+p.yz*yzCap+p.all*allCap):=
 (B.toGenericSparseBKKWitness P.combinedCost P.cycle_le
     P.sum_combinedCost_le).toResidualPoleComponentBudget
   |>.toResidualComponentBudget hproj
def FlagProjectionCycleBudget.toResidualComponentBudget6543
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   {hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator)}
   {hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1}
   {B:GenericExactPolePolynomial G T H
     (flagSupport shearedAgreementFlag) separator hseparator hproj}
   (P:FlagProjectionCycleBudget shearedAgreementFlag separator
     hseparator hproj B flagZMixedCap flagYZMixedCap flagAllMixedCap):
   ResidualComponentBudget G T H
     (fun A↦A.support ⊆ flagSupport shearedAgreementFlag)
     flagWholeMixedCap:=by
 rw [flag_projection_decomposition]
 exact P.toResidualComponentBudget
end
end ProximityPrize.SubmissionLower.RCN118
end PackedLegacy_BB

/-! Packed from ProximityPrize.SubmissionLower.Y8. -/
section PackedLegacy_Y8
namespace ProximityPrize.SubmissionLower.RCN097
open scoped Classical BigOperators WithZero TensorProduct
open Polynomial KaehlerDifferential IsDedekindDomain RCN022 RCN351 RCN344 RCN295 RCN075 RCN002 RCN005 RCN007 RCN264 RCN093
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
theorem exists_nonzero_avoiding_finite_subsingleton
   {K ι:Type*} [Field K] [Infinite K] [Finite ι]
   (Bad:ι → K → Prop)
   (hsingle:∀ i {a b},Bad i a → Bad i b → a=b):
   ∃ a:K,a≠0∧∀ i,¬ Bad i a:=by
 classical
 letI:DecidableEq K:=Classical.decEq K
 letI:DecidableEq ι:=Classical.decEq ι
 letI:Fintype ι:=Fintype.ofFinite ι
 let representative:ι → K:=fun i↦
   if h:∃ a,Bad i a then Classical.choose h else 0
 let forbidden:Finset K:=Finset.univ.image representative
 obtain ⟨a,ha⟩:=Infinite.exists_notMem_finset (insert 0 forbidden)
 refine ⟨a,?_,?_⟩
 · intro hzero
   exact ha (hzero ▸ Finset.mem_insert_self 0 forbidden)
 · intro i hbad
   have hex:∃ b,Bad i b:=⟨a,hbad⟩
   have hrepbad:Bad i (representative i):=by
     simp only [representative,dif_pos hex]
     exact Classical.choose_spec hex
   have hab:a=representative i:=hsingle i hbad hrepbad
   have hmem:representative i∈forbidden:=by
     exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
   exact ha (Finset.mem_insert_of_mem (hab ▸ hmem))
theorem valuation_shear_bad_coefficient_subsingleton
   {K L:Type*} [Field K] [Field L] [Algebra K L]
   (v:RCN345.NormalizedValuation K L)
   (r z:L):
   ∀ {a b:K},
     v.val (r+a • z) < max (v.val r) (v.val z) →
     v.val (r+b • z) < max (v.val r) (v.val z) → a=b:=by
 intro a b ha hb
 by_contra hab
 have hab0:a-b≠0:=sub_ne_zero.mpr hab
 letI:v.val.IsTrivialOn K:=v.property.2
 have hdiff:v.val ((r+a • z)-(r+b • z)) <
     max (v.val r) (v.val z):=v.val.map_sub_lt ha hb
 have hvaldiff:v.val ((r+a • z)-(r+b • z))=v.val z:=by
   rw [show (r+a • z)-(r+b • z)=(a-b) • z by module,
     Algebra.smul_def,map_mul,
     Valuation.IsTrivialOn.eq_one (a-b) hab0,one_mul]
 rw [hvaldiff] at hdiff
 have hzr:v.val z < v.val r:=by
   simpa only [lt_max_iff,lt_self_iff_false,or_false] using hdiff
 have hmax:max (v.val r) (v.val z)=v.val r:=max_eq_left hzr.le
 have ha0:a≠0:=by
   intro ha0
   rw [ha0,zero_smul,add_zero,hmax] at ha
   exact (lt_irrefl _ ha).elim
 have haz:v.val (a • z)=v.val z:=by
   rw [Algebra.smul_def,map_mul,
     Valuation.IsTrivialOn.eq_one a ha0,one_mul]
 have hsum:v.val (r+a • z)=v.val r:=by
   apply v.val.map_add_eq_of_lt_left
   rwa [haz]
 rw [hsum,hmax] at ha
 exact (lt_irrefl _ ha).elim
section FiniteFamily
variable {K:Type*} [Field K] [IsAlgClosed K]
 {I:Type*} [Fintype I]
 (E:I → Type*) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 (r z:∀ i,E i)
variable (W:∀ i,
 Finset (RCN345.NormalizedValuation K (E i)))
end FiniteFamily
section RegularComponents
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
 {G T H:MvPolynomial (Fin 3) Ω}
structure NestedFlagProjectionData
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 2))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1) where
 lam:Ω
 lam_ne:lam≠0
 hU:∀ C:RegularComponent Ω G T H,
   Transcendental Ω (affineU Ω C.1 lam)
 finiteU:∀ C:RegularComponent Ω G T H,
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     (elementEmbedding Ω (CoordinateField Ω C.1)
       (affineU Ω C.1 lam) (hU C)).toRingHom.toAlgebra
   FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1)
 separableU:∀ C:RegularComponent Ω G T H,
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     (elementEmbedding Ω (CoordinateField Ω C.1)
       (affineU Ω C.1 lam) (hU C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1)
 exactU:∀ C:RegularComponent Ω G T H,
   ∀ v∈componentRelevantPlaces hseparator hproj C,
     v.val (affineU Ω C.1 lam)=
       max (v.val (coordinate Ω C.1 0))
         (v.val (coordinate Ω C.1 2))
 mu:Ω
 mu_ne:mu≠0
 hV:∀ C:RegularComponent Ω G T H,
   Transcendental Ω
     (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)
 finiteV:∀ C:RegularComponent Ω G T H,
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     (elementEmbedding Ω (CoordinateField Ω C.1)
       (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)
       (hV C)).toRingHom.toAlgebra
   FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1)
 separableV:∀ C:RegularComponent Ω G T H,
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     (elementEmbedding Ω (CoordinateField Ω C.1)
       (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)
       (hV C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1)
 exactV:∀ C:RegularComponent Ω G T H,
   ∀ v∈componentRelevantPlaces hseparator hproj C,
     v.val (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)=
       max (v.val (coordinate Ω C.1 1))
         (v.val (affineU Ω C.1 lam))
theorem nestedV_eq_affineV
   {hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 2)}
   {hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1}
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Ω G T H):
   coordinate Ω C.1 1+D.mu • affineU Ω C.1 D.lam=
     affineV Ω C.1 D.mu (D.mu*D.lam):=by
 simp only [affineU,affineV]
 simp only [smul_add,smul_smul,add_assoc]
end RegularComponents
end
end ProximityPrize.SubmissionLower.RCN097
end PackedLegacy_Y8

/-! Packed from ProximityPrize.SubmissionLower.DN. -/
section PackedLegacy_DN
namespace ProximityPrize.SubmissionLower.RCN035
open scoped Classical BigOperators WithZero TensorProduct
open Polynomial KaehlerDifferential RCN344 RCN369 RCN370
 RCN351
open RCN022 RCN097
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
theorem element_transcendental_finite_separable_of_differential_ne_zero
   (K L:Type*) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
   (base:SeparableCoordinate K L) (t:L)
   (hdt:D K L t≠0):
   ∃ ht:Transcendental K t,
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L t ht).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) L)∧
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L t ht).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) L):=by
 have ht:Transcendental K t:=by
   show ¬ IsAlgebraic K t
   intro halg
   obtain ⟨c,hc⟩:=eq_algebraMap_of_isAlgebraic K L t halg
   apply hdt
   rw [←hc]
   exact (D K L).map_algebraMap c
 let embeddingT:=elementEmbedding K L t ht
 have hfiniteT:
     letI:Algebra (RatFunc K) L:=embeddingT.toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L:=
   finiteDimensional_elementEmbedding K L base.embedding base.finite t ht
 refine ⟨ht,hfiniteT,?_⟩
 have hcriterionBase:=
   isSeparable_iff_span_parameterDifferential K L base.embedding base.finite
 have hcriterionT:=
   isSeparable_iff_span_parameterDifferential K L embeddingT hfiniteT
 have hspanBase:Submodule.span L
     ({D K L (SeparableCoordinate.value K L base)}:Set Ω[L⁄K])=⊤:=by
   have h:=hcriterionBase.mp base.separable
   exact h
 apply hcriterionT.mpr
 have hparamT:parameterDifferential K L embeddingT=D K L t:=by
   unfold parameterDifferential embeddingT
   rw [elementEmbedding_variable]
 rw [hparamT]
 apply top_unique
 rw [←hspanBase]
 apply Submodule.span_le.mpr
 intro x hx
 rw [Set.mem_singleton_iff.mp hx]
 have htmem:D K L t∈Submodule.span L
     ({D K L (SeparableCoordinate.value K L base)}:Set Ω[L⁄K]):=by
   rw [hspanBase]
   trivial
 obtain ⟨b,hb⟩:=Submodule.mem_span_singleton.mp htmem
 have hb0:b≠0:=by
   intro hzero
   apply hdt
   rw [←hb,hzero,zero_smul]
 apply Submodule.mem_span_singleton.mpr
 refine ⟨b⁻¹,?_⟩
 rw [←hb,smul_smul,inv_mul_cancel₀ hb0,one_smul]
section FiniteFamily
variable {K:Type*} [Field K] [IsAlgClosed K]
 {I:Type*} [Fintype I]
 (E:I → Type*) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 (r z:∀ i,E i)
variable (W:∀ i,
 Finset (RCN345.NormalizedValuation K (E i)))
theorem exists_common_exact_finite_separable_affine_adaptive
   (base:∀ i,SeparableCoordinate K (E i))
   (hactive:∀ i,D K (E i) (r i)≠0∨D K (E i) (z i)≠0):
   ∃ a:K,a≠0∧∀ i,
     ∃ ht:Transcendental K (r i+a • z i),
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc K) (E i))∧
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc K) (E i))∧
       (∀ v∈W i,v.val (r i+a • z i)=
         max (v.val (r i)) (v.val (z i))):=by
 let J:=I ⊕ Sigma fun i:I => {v//v∈W i}
 let Bad:J → K → Prop
   | Sum.inl i,a => D K (E i) (r i)+a • D K (E i) (z i)=0
   | Sum.inr iv,a => iv.2.1.val (r iv.1+a • z iv.1) <
       max (iv.2.1.val (r iv.1)) (iv.2.1.val (z iv.1))
 have hsingle:∀ j {a b},Bad j a → Bad j b → a=b:=by
   intro j a b ha hb
   rcases j with i | ⟨i,v⟩
   · by_cases hdz:D K (E i) (z i)=0
     · have hdr:D K (E i) (r i)≠0:=
         (hactive i).resolve_right (fun hn => hn hdz)
       change D K (E i) (r i)+a • D K (E i) (z i)=0 at ha
       exfalso
       apply hdr
       simpa only [hdz,smul_zero,add_zero] using ha
     · exact shear_bad_coefficient_subsingleton K (E i) (r i) (z i)
         hdz ha hb
   · exact valuation_shear_bad_coefficient_subsingleton v.1 (r i) (z i) ha hb
 obtain ⟨a,ha0,havoid⟩:=
   exists_nonzero_avoiding_finite_subsingleton Bad hsingle
 refine ⟨a,ha0,fun i => ?_⟩
 have hdiff:D K (E i) (r i)+a • D K (E i) (z i)≠0:=by
   exact havoid (Sum.inl i)
 have hD:D K (E i) (r i+a • z i)≠0:=by
   rw [map_add,(D K (E i)).map_smul]
   exact hdiff
 obtain ⟨ht,hfinite,hsep⟩:=
   element_transcendental_finite_separable_of_differential_ne_zero
     K (E i) (base i) (r i+a • z i) hD
 refine ⟨ht,hfinite,hsep,?_⟩
 intro v hv
 have hnotlt:=havoid (Sum.inr ⟨i,⟨v,hv⟩⟩)
 have hupper:=v.val.map_add (r i) (a • z i)
 have haz:v.val (a • z i)=v.val (z i):=by
   letI:v.val.IsTrivialOn K:=v.property.2
   rw [Algebra.smul_def,map_mul,
     Valuation.IsTrivialOn.eq_one a ha0,one_mul]
 rw [haz] at hupper
 exact le_antisymm hupper (le_of_not_gt hnotlt)
theorem exists_common_exact_finite_separable_affine_adaptive_avoiding_one
   (Extra:K → Prop)
   (hextra:∀ {a b},Extra a → Extra b → a=b)
   (base:∀ i,SeparableCoordinate K (E i))
   (hactive:∀ i,D K (E i) (r i)≠0∨D K (E i) (z i)≠0):
   ∃ a:K,a≠0∧¬ Extra a∧∀ i,
     ∃ ht:Transcendental K (r i+a • z i),
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc K) (E i))∧
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) ht).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc K) (E i))∧
       (∀ v∈W i,v.val (r i+a • z i)=
         max (v.val (r i)) (v.val (z i))):=by
 let J:=Unit ⊕ (I ⊕ Sigma fun i:I => {v//v∈W i})
 let Bad:J → K → Prop
   | Sum.inl _,a => Extra a
   | Sum.inr (Sum.inl i),a =>
       D K (E i) (r i)+a • D K (E i) (z i)=0
   | Sum.inr (Sum.inr iv),a => iv.2.1.val (r iv.1+a • z iv.1) <
       max (iv.2.1.val (r iv.1)) (iv.2.1.val (z iv.1))
 have hsingle:∀ j {a b},Bad j a → Bad j b → a=b:=by
   intro j a b ha hb
   rcases j with _ | i | ⟨i,v⟩
   · exact hextra ha hb
   · by_cases hdz:D K (E i) (z i)=0
     · have hdr:D K (E i) (r i)≠0:=
         (hactive i).resolve_right (fun hn => hn hdz)
       change D K (E i) (r i)+a • D K (E i) (z i)=0 at ha
       exfalso
       apply hdr
       simpa only [hdz,smul_zero,add_zero] using ha
     · exact shear_bad_coefficient_subsingleton K (E i) (r i) (z i)
         hdz ha hb
   · exact valuation_shear_bad_coefficient_subsingleton v.1 (r i) (z i) ha hb
 obtain ⟨a,ha0,havoid⟩:=
   exists_nonzero_avoiding_finite_subsingleton Bad hsingle
 refine ⟨a,ha0,havoid (Sum.inl ()),fun i => ?_⟩
 have hdiff:D K (E i) (r i)+a • D K (E i) (z i)≠0:=by
   exact havoid (Sum.inr (Sum.inl i))
 have hD:D K (E i) (r i+a • z i)≠0:=by
   rw [map_add,(D K (E i)).map_smul]
   exact hdiff
 obtain ⟨ht,hfinite,hsep⟩:=
   element_transcendental_finite_separable_of_differential_ne_zero
     K (E i) (base i) (r i+a • z i) hD
 refine ⟨ht,hfinite,hsep,?_⟩
 intro v hv
 have hnotlt:=havoid (Sum.inr (Sum.inr ⟨i,⟨v,hv⟩⟩))
 have hupper:=v.val.map_add (r i) (a • z i)
 have haz:v.val (a • z i)=v.val (z i):=by
   letI:v.val.IsTrivialOn K:=v.property.2
   rw [Algebra.smul_def,map_mul,
     Valuation.IsTrivialOn.eq_one a ha0,one_mul]
 rw [haz] at hupper
 exact le_antisymm hupper (le_of_not_gt hnotlt)
end FiniteFamily
end
end ProximityPrize.SubmissionLower.RCN035
end PackedLegacy_DN

/-! Packed from ProximityPrize.SubmissionLower.Y1. -/
section PackedLegacy_Y1
namespace ProximityPrize.SubmissionLower.RCN042
open scoped Classical TensorProduct
open Polynomial KaehlerDifferential RCN344 RCN022 RCN369 RCN370
 RCN351
open RCN341
noncomputable section
variable {K:Type} {L:Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
def coordinateOfGate (x:L)
   (hgate:∀ hx:Transcendental K x,
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) L)∧
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) L)):Coordinate K L:=
 if hx:Transcendental K x then
   Sum.inr {
     embedding:=elementEmbedding K L x hx
     finite:=(hgate hx).1
     separable:=(hgate hx).2}
 else
   Sum.inl ((eq_algebraMap_of_isAlgebraic K L x (not_not.mp hx)).choose)
@[simp] theorem coordinateOfGate_value (x:L)
   (hgate:∀ hx:Transcendental K x,
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) L)∧
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) L)):
   coordinateValue K L (coordinateOfGate x hgate)=x:=by
 unfold coordinateOfGate
 split_ifs with hx
 · exact elementEmbedding_variable K L x hx
 · exact (eq_algebraMap_of_isAlgebraic K L x (not_not.mp hx)).choose_spec
@[simp] theorem coordinateOfGate_degree_of_transcendental (x:L)
   (hgate:∀ hx:Transcendental K x,
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) L)∧
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) L))
   (hx:Transcendental K x):
   coordinateDegree K L (coordinateOfGate x hgate)=
     (letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L x hx).toRingHom.toAlgebra
      Module.finrank (RatFunc K) L):=by
 unfold coordinateOfGate coordinateDegree SeparableCoordinate.degree
 rw [dif_pos hx]
 rfl
@[simp] theorem coordinateOfGate_degree_of_isAlgebraic (x:L)
   (hgate:∀ hx:Transcendental K x,
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) L)∧
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) L))
   (hx:IsAlgebraic K x):
   coordinateDegree K L (coordinateOfGate x hgate)=0:=by
 unfold coordinateOfGate coordinateDegree
 rw [dif_neg (fun htr => htr hx)]
 rfl
theorem one_le_coordinateDegree_of_transcendental_value
   (c:Coordinate K L)
   (hc:Transcendental K (coordinateValue K L c)):
   1 ≤ coordinateDegree K L c:=by
 rcases c with a | c
 · exact (hc (isAlgebraic_algebraMap a)).elim
 · letI:Algebra (RatFunc K) L:=c.embedding.toRingHom.toAlgebra
   letI:FiniteDimensional (RatFunc K) L:=c.finite
   exact Module.finrank_pos
section FiniteFamily
variable {I:Type*} [Fintype I]
 (E:I → Type) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
theorem sum_coordinateOfGate_degree_eq
   (x:∀ i,E i)
   (hgate:∀ i,∀ hx:Transcendental K (x i),
     (letI:Algebra (RatFunc K) (E i):=
         (elementEmbedding K (E i) (x i) hx).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) (E i))∧
     (letI:Algebra (RatFunc K) (E i):=
         (elementEmbedding K (E i) (x i) hx).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) (E i))):
   (∑ i,coordinateDegree K (E i) (coordinateOfGate (x i) (hgate i)))=
     ∑ i:{i:I//Transcendental K (x i)},
       (letI:Algebra (RatFunc K) (E i.1):=
         (elementEmbedding K (E i.1) (x i.1) i.2).toRingHom.toAlgebra
        Module.finrank (RatFunc K) (E i.1)):=by
 classical
 let s:Set I:={i | Transcendental K (x i)}
 let degree:s → ℕ:=fun i =>
   letI:Algebra (RatFunc K) (E i.1):=
     (elementEmbedding K (E i.1) (x i.1) i.2).toRingHom.toAlgebra
   Module.finrank (RatFunc K) (E i.1)
 apply Finset.sum_congr_set s
   (fun i => coordinateDegree K (E i) (coordinateOfGate (x i) (hgate i))) degree
 · intro i hi
   exact coordinateOfGate_degree_of_transcendental (x i) (hgate i) hi
 · intro i hi
   exact coordinateOfGate_degree_of_isAlgebraic (x i) (hgate i) (not_not.mp hi)
end FiniteFamily
def literalToSeparableCoordinate
   {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (D:SeparableLiteralCoordinate P):
   SeparableCoordinate K (RCN002.CoordinateField K P) where
 embedding:=RCN005.rationalBaseEmbedding
   K P D.index D.transcendental
 finite:=D.finite
 separable:=D.separable
@[simp] theorem literalToSeparableCoordinate_value
   {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (D:SeparableLiteralCoordinate P):
   coordinateValue K (RCN002.CoordinateField K P)
       (Sum.inr (literalToSeparableCoordinate D))=
     RCN002.coordinate K P D.index:=by
 exact RCN005.rational_variable_image
   K P D.index D.transcendental
theorem differential_ne_zero_of_gate (x:L)
   (hx:Transcendental K x)
   (hgate:
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) L)∧
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L x hx).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) L)):
   D K L x≠0:=by
 have h:=parameterDifferential_ne_zero_of_isSeparable K L
   (elementEmbedding K L x hx) hgate.1 hgate.2
 unfold parameterDifferential at h
 rwa [elementEmbedding_variable] at h
end
end ProximityPrize.SubmissionLower.RCN042
end PackedLegacy_Y1

/-! Packed from ProximityPrize.SubmissionLower.A3. -/
section PackedLegacy_A3
namespace ProximityPrize.SubmissionLower.RCN046
open scoped Classical BigOperators WithZero
open RCN002 RCN344 RCN264 RCN095 RCN341 RCN340 RCN237 RCN295 RCN042
noncomputable section
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
structure AdaptiveUnitProjectionFamily
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (p q:FlagDegree) where
 zProjection:∀ C:RegularComponent Omega G T H,
   Coordinate Omega (CoordinateField Omega C.1)
 yzProjection:∀ C:RegularComponent Omega G T H,
   Coordinate Omega (CoordinateField Omega C.1)
 allProjection:∀ C:RegularComponent Omega G T H,
   Coordinate Omega (CoordinateField Omega C.1)
 zValue:∀ C:RegularComponent Omega G T H,
   coordinateValue Omega (CoordinateField Omega C.1) (zProjection C)=
     coordinate Omega C.1 2
 allTranscendental:∀ C:RegularComponent Omega G T H,
   Transcendental Omega
     (coordinateValue Omega (CoordinateField Omega C.1) (allProjection C))
 zPole_eq:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
   exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitZFlag)=
     RCN346.poleOrder Omega (CoordinateField Omega C.1) v
       (coordinateValue Omega (CoordinateField Omega C.1) (zProjection C))
 yzPole_eq:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
   exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitYZFlag)=
     RCN346.poleOrder Omega (CoordinateField Omega C.1) v
       (coordinateValue Omega (CoordinateField Omega C.1) (yzProjection C))
 allPole_eq:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
   exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitAllFlag)=
     RCN346.poleOrder Omega (CoordinateField Omega C.1) v
       (coordinateValue Omega (CoordinateField Omega C.1) (allProjection C))
 sum_zDegree_le:
   (∑ C:RegularComponent Omega G T H,
     coordinateDegree Omega (CoordinateField Omega C.1) (zProjection C)) ≤
     flagMixed p q unitZFlag
 sum_yzDegree_le:
   (∑ C:RegularComponent Omega G T H,
     coordinateDegree Omega (CoordinateField Omega C.1) (yzProjection C)) ≤
     flagMixed p q unitYZFlag
 sum_allDegree_le:
   (∑ C:RegularComponent Omega G T H,
     coordinateDegree Omega (CoordinateField Omega C.1) (allProjection C)) ≤
     flagMixed p q unitAllFlag
def AdaptiveUnitProjectionFamily.toAdaptiveUnitPoleBudget
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (P:AdaptiveUnitProjectionFamily base p q):
   AdaptiveUnitPoleBudget base p q where
 zCost:=fun C => coordinateDegree Omega (CoordinateField Omega C.1)
   (P.zProjection C)
 yzCost:=fun C => coordinateDegree Omega (CoordinateField Omega C.1)
   (P.yzProjection C)
 allCost:=fun C => coordinateDegree Omega (CoordinateField Omega C.1)
   (P.allProjection C)
 sum_zCost_le:=P.sum_zDegree_le
 sum_yzCost_le:=P.sum_yzDegree_le
 sum_allCost_le:=P.sum_allDegree_le
 zPole:=by
   intro C
   unfold LiteralSupportPoleBound
   dsimp only
   intro W
   calc
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport unitZFlag))=
         ∑ v∈W,RCN346.poleOrder Omega
           (CoordinateField Omega C.1) v
           (coordinateValue Omega (CoordinateField Omega C.1)
             (P.zProjection C)):=by
       apply Finset.sum_congr rfl
       intro v _
       exact P.zPole_eq C v
     _ ≤ (coordinateDegree Omega (CoordinateField Omega C.1)
         (P.zProjection C):ℤ):=
       finite_sum_coordinate_pole_le_degree Omega
         (CoordinateField Omega C.1) (P.zProjection C) W
 yzPole:=by
   intro C
   unfold LiteralSupportPoleBound
   dsimp only
   intro W
   calc
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport unitYZFlag))=
         ∑ v∈W,RCN346.poleOrder Omega
           (CoordinateField Omega C.1) v
           (coordinateValue Omega (CoordinateField Omega C.1)
             (P.yzProjection C)):=by
       apply Finset.sum_congr rfl
       intro v _
       exact P.yzPole_eq C v
     _ ≤ (coordinateDegree Omega (CoordinateField Omega C.1)
         (P.yzProjection C):ℤ):=
       finite_sum_coordinate_pole_le_degree Omega
         (CoordinateField Omega C.1) (P.yzProjection C) W
 allPole:=by
   intro C
   unfold LiteralSupportPoleBound
   dsimp only
   intro W
   calc
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport unitAllFlag))=
         ∑ v∈W,RCN346.poleOrder Omega
           (CoordinateField Omega C.1) v
           (coordinateValue Omega (CoordinateField Omega C.1)
             (P.allProjection C)):=by
       apply Finset.sum_congr rfl
       intro v _
       exact P.allPole_eq C v
     _ ≤ (coordinateDegree Omega (CoordinateField Omega C.1)
         (P.allProjection C):ℤ):=
       finite_sum_coordinate_pole_le_degree Omega
         (CoordinateField Omega C.1) (P.allProjection C) W
def AdaptiveUnitProjectionFamily.toPrimeFlagBudgetFamily
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (P:AdaptiveUnitProjectionFamily base p q):
   PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q:=
 P.toAdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily
theorem AdaptiveUnitProjectionFamily.one_le_zDegree_of_transcendental
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (P:AdaptiveUnitProjectionFamily base p q)
   (C:RegularComponent Omega G T H)
   (hZ:Transcendental Omega (coordinate Omega C.1 2)):
   1 ≤ coordinateDegree Omega (CoordinateField Omega C.1)
     (P.zProjection C):=by
 apply one_le_coordinateDegree_of_transcendental_value
 rwa [P.zValue C]
theorem AdaptiveUnitProjectionFamily.one_le_toPrimeFlagBudgetFamily_zCost
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (P:AdaptiveUnitProjectionFamily base p q)
   (C:RegularComponent Omega G T H)
   (hZ:Transcendental Omega (coordinate Omega C.1 2)):
   1 ≤ P.toPrimeFlagBudgetFamily.zCost C:=
 P.one_le_zDegree_of_transcendental C hZ
end
end ProximityPrize.SubmissionLower.RCN046
end PackedLegacy_A3

/-! Packed from ProximityPrize.SubmissionLower.DS. -/
section PackedLegacy_DS
namespace ProximityPrize.SubmissionLower.RCN044
open scoped Classical WithZero
open IsDedekindDomain RCN187 RCN002 RCN005
 RCN006
open RCN344 RCN341
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
def literalRelevantPlaces
   {P:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime]
   (D:SeparableLiteralCoordinate P):
   Finset (Place Omega (CoordinateField Omega P)):=by
 classical
 let i0:=D.index
 let htr:=D.transcendental
 letI:Algebra (Polynomial Omega) (CoordinateRing Omega P):=
   quotientPolynomialAlgebra Omega P i0
 letI:Algebra (Polynomial Omega) (CoordinateField Omega P):=
   polynomialBaseAlgebra Omega P i0
 letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
   rationalBaseAlgebra Omega P i0 htr
 letI:=quotientBaseScalarTower Omega P i0
 letI:=polynomialBaseScalarTower Omega P i0
 letI:=quotientFractionScalarTower Omega P i0
 letI:=polynomialRationalScalarTower Omega P i0 htr
 letI:=rationalBaseScalarTower Omega P i0 htr
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega P):=D.finite
 letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=D.separable
 exact Finset.univ.biUnion (fun i:Fin 3 =>
   if hi:coordinate Omega P i≠0 then
     RCN026.placesFor Omega (CoordinateField Omega P)
       (coordinate Omega P i) hi
   else ∅)
theorem coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
   {P:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime]
   (D:SeparableLiteralCoordinate P)
   (v:Place Omega (CoordinateField Omega P))
   (hv:v∉literalRelevantPlaces D) (i:Fin 3):
   poleOrder v.val (coordinate Omega P i)=0:=by
 classical
 let i0:=D.index
 let htr:=D.transcendental
 letI:Algebra (Polynomial Omega) (CoordinateRing Omega P):=
   quotientPolynomialAlgebra Omega P i0
 letI:Algebra (Polynomial Omega) (CoordinateField Omega P):=
   polynomialBaseAlgebra Omega P i0
 letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
   rationalBaseAlgebra Omega P i0 htr
 letI:=quotientBaseScalarTower Omega P i0
 letI:=polynomialBaseScalarTower Omega P i0
 letI:=quotientFractionScalarTower Omega P i0
 letI:=polynomialRationalScalarTower Omega P i0 htr
 letI:=rationalBaseScalarTower Omega P i0 htr
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega P):=D.finite
 letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=D.separable
 by_cases hi:coordinate Omega P i=0
 · simp [hi,poleOrder]
 · have hnot:v∉RCN026.placesFor Omega
       (CoordinateField Omega P) (coordinate Omega P i) hi:=by
     intro hmem
     apply hv
     unfold literalRelevantPlaces
     apply Finset.mem_biUnion.mpr
     exact ⟨i,Finset.mem_univ _,by simp [hi,hmem]⟩
   have horder:RCN026.order Omega (CoordinateField Omega P) v
       (coordinate Omega P i)=0:=by
     by_contra hne
     exact hnot (RCN026.placesFor_covers Omega
       (CoordinateField Omega P) (coordinate Omega P i) hi v hne)
   unfold RCN026.order at horder
   unfold poleOrder
   have hlog:(v.val (coordinate Omega P i)).log=0:=by omega
   rw [hlog]
   simp
end
end ProximityPrize.SubmissionLower.RCN044
end PackedLegacy_DS

/-! Packed from ProximityPrize.SubmissionLower.J7. -/
section PackedLegacy_J7
namespace ProximityPrize.SubmissionLower.RCN096
open scoped Classical BigOperators WithZero TensorProduct
open Polynomial KaehlerDifferential IsDedekindDomain RCN022 RCN351 RCN344 RCN295 RCN075 RCN002 RCN005 RCN007 RCN264 RCN093 RCN097
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
theorem directional_bad_coefficient_subsingleton
   {K:Type*} [Field K] (G:MvPolynomial (Fin 3) K)
   (hS:MvPolynomial.pderiv (1:Fin 3) G≠0):
   ∀ {a b:K},
     MvPolynomial.pderiv (0:Fin 3) G-
         MvPolynomial.C a*MvPolynomial.pderiv (1:Fin 3) G=0 →
     MvPolynomial.pderiv (0:Fin 3) G-
         MvPolynomial.C b*MvPolynomial.pderiv (1:Fin 3) G=0 →
     a=b:=by
 intro a b ha hb
 have ha':MvPolynomial.pderiv (0:Fin 3) G=
     MvPolynomial.C a*MvPolynomial.pderiv (1:Fin 3) G:=
   sub_eq_zero.mp ha
 have hb':MvPolynomial.pderiv (0:Fin 3) G=
     MvPolynomial.C b*MvPolynomial.pderiv (1:Fin 3) G:=
   sub_eq_zero.mp hb
 have habmul:MvPolynomial.C a*MvPolynomial.pderiv (1:Fin 3) G=
     MvPolynomial.C b*MvPolynomial.pderiv (1:Fin 3) G:=
   ha'.symm.trans hb'
 have hfactor:(MvPolynomial.C a-MvPolynomial.C b)*
     MvPolynomial.pderiv (1:Fin 3) G=0:=by
   rw [sub_mul,habmul,sub_self]
 have hCsub:MvPolynomial.C a-MvPolynomial.C b=0:=
   (mul_eq_zero.mp hfactor).resolve_right hS
 apply MvPolynomial.C_injective
 exact sub_eq_zero.mp hCsub
section FiniteFamily
variable {K:Type*} [Field K] [IsAlgClosed K]
 {I:Type*} [Fintype I]
 (E:I → Type*) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 (r z:∀ i,E i)
variable (W:∀ i,
 Finset (RCN345.NormalizedValuation K (E i)))
end FiniteFamily
section RegularComponents
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
end RegularComponents
end
end ProximityPrize.SubmissionLower.RCN096
end PackedLegacy_J7

/-! Packed from ProximityPrize.SubmissionLower.J8. -/
section PackedLegacy_J8
namespace ProximityPrize.SubmissionLower.RCN099
open scoped Classical WithZero
open IsDedekindDomain RCN187 RCN344 RCN264 RCN075 RCN093 RCN097 RCN002 RCN005 RCN007 RCN022
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
theorem poleOrder_eq_max_of_valuation_eq_max
   {L:Type*} [Field L]
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x y z:L)
   (h:v x=max (v y) (v z)):
   poleOrder v x=max (poleOrder v y) (poleOrder v z):=by
 unfold poleOrder
 rw [h]
 by_cases hy:v y=0
 · rw [hy]
   simp
 by_cases hz:v z=0
 · rw [hz]
   simp
 rcases le_total (v y) (v z) with hyz | hzy
 · rw [max_eq_right hyz]
   rw [max_eq_right
     (max_le_max_left 0 ((WithZero.log_le_log hy hz).2 hyz))]
 · rw [max_eq_left hzy]
   rw [max_eq_left
     (max_le_max_left 0 ((WithZero.log_le_log hz hy).2 hzy))]
theorem valuation_le_one_of_poleOrder_eq_zero
   {L:Type*} [Field L]
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:L)
   (h:poleOrder v x=0):
   v x ≤ 1:=by
 by_cases hx:v x=0
 · simp [hx]
 by_contra hnot
 have hlt:(1:WithZero (Multiplicative ℤ)) < v x:=
   lt_of_not_ge hnot
 have hlog:0 < (v x).log:=by
   simpa only [WithZero.log_one] using
     ((WithZero.log_lt_log one_ne_zero hx).2 hlt)
 unfold poleOrder at h
 rw [max_eq_right hlog.le] at h
 omega
section RegularComponents
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
variable
   {hseparator:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (coordinate Omega C.1 2)}
   {hproj:∀ C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1}
theorem nested_u_pole
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H)
   (v:Place Omega (CoordinateField Omega C.1)):
   poleOrder v.val (affineU Omega C.1 D.lam)=
     max (poleOrder v.val (coordinate Omega C.1 0))
       (poleOrder v.val (coordinate Omega C.1 2)):=by
 by_cases hv:v∈componentRelevantPlaces hseparator hproj C
 · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _
     (D.exactU C v hv)
 · have hY:=coordinate_poleOrder_eq_zero_of_not_mem_relevant
       hseparator hproj C v hv 0
   have hZ:=coordinate_poleOrder_eq_zero_of_not_mem_relevant
       hseparator hproj C v hv 2
   have hYle:v.val (coordinate Omega C.1 0) ≤ 1:=
     valuation_le_one_of_poleOrder_eq_zero v.val _ hY
   have hZle:v.val (coordinate Omega C.1 2) ≤ 1:=
     valuation_le_one_of_poleOrder_eq_zero v.val _ hZ
   letI:v.val.IsTrivialOn Omega:=v.property.2
   have hscalar:
       v.val (D.lam • coordinate Omega C.1 2)=
         v.val (coordinate Omega C.1 2):=by
     rw [Algebra.smul_def,map_mul,
       Valuation.IsTrivialOn.eq_one D.lam D.lam_ne,one_mul]
   have hUle:v.val (affineU Omega C.1 D.lam) ≤ 1:=by
     unfold affineU
     exact (v.val.map_add _ _).trans
       (by rw [hscalar];exact max_le hYle hZle)
   have hU:poleOrder v.val (affineU Omega C.1 D.lam)=0:=
     RCN346.poleOrder_eq_zero_of_le_one
       Omega (CoordinateField Omega C.1) v _ hUle
   rw [hU,hY,hZ]
   simp
theorem nested_v_pole
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H)
   (v:Place Omega (CoordinateField Omega C.1)):
   poleOrder v.val (affineV Omega C.1 D.mu (D.mu*D.lam))=
     max (poleOrder v.val (coordinate Omega C.1 1))
       (max (poleOrder v.val (coordinate Omega C.1 0))
         (poleOrder v.val (coordinate Omega C.1 2))):=by
 rw [←nestedV_eq_affineV D C]
 by_cases hv:v∈componentRelevantPlaces hseparator hproj C
 · calc
     poleOrder v.val
         (coordinate Omega C.1 1+D.mu • affineU Omega C.1 D.lam)=
         max (poleOrder v.val (coordinate Omega C.1 1))
           (poleOrder v.val (affineU Omega C.1 D.lam)):=
       poleOrder_eq_max_of_valuation_eq_max v.val _ _ _
         (D.exactV C v hv)
     _=max (poleOrder v.val (coordinate Omega C.1 1))
         (max (poleOrder v.val (coordinate Omega C.1 0))
           (poleOrder v.val (coordinate Omega C.1 2))):=by
       rw [nested_u_pole D C v]
 · have hS:=coordinate_poleOrder_eq_zero_of_not_mem_relevant
       hseparator hproj C v hv 1
   have hY:=coordinate_poleOrder_eq_zero_of_not_mem_relevant
       hseparator hproj C v hv 0
   have hZ:=coordinate_poleOrder_eq_zero_of_not_mem_relevant
       hseparator hproj C v hv 2
   have hU:poleOrder v.val (affineU Omega C.1 D.lam)=0:=by
     rw [nested_u_pole D C v,hY,hZ]
     simp
   have hSle:v.val (coordinate Omega C.1 1) ≤ 1:=
     valuation_le_one_of_poleOrder_eq_zero v.val _ hS
   have hUle:v.val (affineU Omega C.1 D.lam) ≤ 1:=
     valuation_le_one_of_poleOrder_eq_zero v.val _ hU
   letI:v.val.IsTrivialOn Omega:=v.property.2
   have hscalar:v.val (D.mu • affineU Omega C.1 D.lam)=
       v.val (affineU Omega C.1 D.lam):=by
     rw [Algebra.smul_def,map_mul,
       Valuation.IsTrivialOn.eq_one D.mu D.mu_ne,one_mul]
   have hVle:v.val
       (coordinate Omega C.1 1+D.mu • affineU Omega C.1 D.lam) ≤ 1:=
     (v.val.map_add _ _).trans
       (by rw [hscalar];exact max_le hSle hUle)
   have hV:poleOrder v.val
       (coordinate Omega C.1 1+D.mu • affineU Omega C.1 D.lam)=0:=
     RCN346.poleOrder_eq_zero_of_le_one
       Omega (CoordinateField Omega C.1) v _ hVle
   rw [hV,hS,hY,hZ]
   simp
theorem hAffineV
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H):
   Transcendental Omega (affineV Omega C.1 D.mu (D.mu*D.lam)):=by
 rw [←nestedV_eq_affineV D C]
 exact D.hV C
theorem elementEmbedding_affineV_eq_nested
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H):
   elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 D.mu (D.mu*D.lam)) (hAffineV D C)=
     elementEmbedding Omega (CoordinateField Omega C.1)
       (coordinate Omega C.1 1+D.mu • affineU Omega C.1 D.lam)
       (D.hV C):=by
 apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial Omega))
 ext
 change elementEmbedding Omega (CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam)) (hAffineV D C)
       (algebraMap (Polynomial Omega) (RatFunc Omega) Polynomial.X)=
   elementEmbedding Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 1+D.mu • affineU Omega C.1 D.lam)
       (D.hV C)
       (algebraMap (Polynomial Omega) (RatFunc Omega) Polynomial.X)
 rw [elementEmbedding_variable,elementEmbedding_variable]
 exact (nestedV_eq_affineV D C).symm
theorem separableAffineV
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H):
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 D.mu (D.mu*D.lam))
       (hAffineV D C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=by
 rw [elementEmbedding_affineV_eq_nested D C]
 exact D.separableV C
end RegularComponents
end
end ProximityPrize.SubmissionLower.RCN099
end PackedLegacy_J8

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower
end Compact_PackedLegacyCore2
