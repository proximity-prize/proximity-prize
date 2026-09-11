import ProximityPrize.SubmissionLower.PartF003_08
section Compact_PackedLegacyCore1
section PackedLegacy_BQ
namespace ProximityPrize.SubmissionLower.RCN163
open scoped Classical
open RCN094 RCN157 RCN155 RCN160 RCN238 RCN125 RCN372
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K Omega:Type} [Field K] [Field Omega]
local instance:DecidableEq Omega:=Classical.decEq Omega

abbrev Poly3 (Omega:Type) [Field Omega]:=MvPolynomial (Fin 3) Omega
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
theorem originalAlgHom_eq_residualAlgHom_inverse
   (aY v bY aS bS cS:Omega):
   originalAlgHom aY v bY aS bS cS=
     residualAlgHom (-v⁻¹*aY) v⁻¹ (-v⁻¹*bY)
       (-v⁻¹*aS+v⁻¹*v⁻¹*bS*aY)
       (-v⁻¹*v⁻¹*bS)
       (v⁻¹*v⁻¹*bS*bY-v⁻¹*cS):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;>
   simp [originalAlgHom,originalImage,residualAlgHom,residualImage] <;>
   ring
theorem residual_degreeOf_one_le
   (aY v bY aS bS cS:Omega) (F:Poly3 Omega):
   (residualAlgHom aY v bY aS bS cS F).degreeOf 1 ≤ F.degreeOf 1:=by
 have h:=residualAlgHom_wt_le_pulled
   (Pi.single (1:Fin 3) 1) aY v bY aS bS cS F
 have hp:flagPullWeights (Pi.single (1:Fin 3) 1)=
     Pi.single (1:Fin 3) 1:=by
   funext i
   fin_cases i <;> simp [flagPullWeights]
 rw [hp] at h
 simpa [wt] using h
theorem original_degreeOf_one_le
   (aY v bY aS bS cS:Omega) (F:Poly3 Omega):
   (originalAlgHom aY v bY aS bS cS F).degreeOf 1 ≤ F.degreeOf 1:=by
 rw [originalAlgHom_eq_residualAlgHom_inverse]
 exact residual_degreeOf_one_le _ _ _ _ _ _ F
theorem residual_degreeOf_one_eq
   (aY v bY aS bS cS:Omega) (hv:v≠0) (F:Poly3 Omega):
   (residualAlgHom aY v bY aS bS cS F).degreeOf 1=F.degreeOf 1:=by
 apply Nat.le_antisymm
 · exact residual_degreeOf_one_le _ _ _ _ _ _ F
 · have h:=original_degreeOf_one_le aY v bY aS bS cS
     (residualAlgHom aY v bY aS bS cS F)
   have hback:
       originalAlgHom aY v bY aS bS cS
           (residualAlgHom aY v bY aS bS cS F)=F:=by
     have hc:=DFunLike.congr_fun
       (original_comp_residual aY v bY aS bS cS hv) F
     simpa [AlgHom.comp_apply] using hc
   simpa only [hback] using h
theorem residual_degreeOf_one_pos_iff
   (aY v bY aS bS cS:Omega) (hv:v≠0) (F:Poly3 Omega):
   0 < (residualAlgHom aY v bY aS bS cS F).degreeOf 1 ↔
     0 < F.degreeOf 1:=by
 rw [residual_degreeOf_one_eq aY v bY aS bS cS hv F]
theorem componentResidualHom_eq_residualAlgHom
   (aY v bY aS bS cS:Omega):
   componentResidualHom aY v bY aS bS cS=
     residualAlgHom aY v bY aS bS cS:=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;>
   simp [componentResidualHom,componentResidualImage,
     residualAlgHom,residualImage]
theorem surfaceMap_globalResidualHom_eq_residualAlgHom
   (phi:Polynomial K →+*Omega) (P0 P1 V:Polynomial K) (F:Poly4 K):
   RCN136.surfaceMap phi
       (globalResidualHom P0 P1 V F)=
     residualAlgHom (phi P0) (phi V) (phi P1)
       (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
       (RCN136.surfaceMap phi F):=by
 rw [surfaceMap_globalResidualHom]
 rw [componentResidualHom_eq_residualAlgHom]
theorem pderiv_globalResidualHom
   (P0 P1 V:Polynomial K) (F:Poly4 K):
   MvPolynomial.pderiv (2:Fin 4) (globalResidualHom P0 P1 V F)=
     embedX K V*globalResidualHom P0 P1 V
       (MvPolynomial.pderiv (2:Fin 4) F):=
 pderiv_globalResidualHom_R P0 P1 V F
theorem surfaceMap_pderiv_globalResidualHom
   (phi:Polynomial K →+*Omega) (P0 P1 V:Polynomial K) (F:Poly4 K):
   RCN136.surfaceMap phi
       (MvPolynomial.pderiv (2:Fin 4)
         (globalResidualHom P0 P1 V F))=
     MvPolynomial.C (phi V)*
       residualAlgHom (phi P0) (phi V) (phi P1)
         (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
         (RCN136.surfaceMap phi
           (MvPolynomial.pderiv (2:Fin 4) F)):=by
 rw [pderiv_globalResidualHom,map_mul,surfaceMap_embedX,
   surfaceMap_globalResidualHom_eq_residualAlgHom]
theorem residual_dvd_surfaceMap_globalResidualHom_iff
   (phi:Polynomial K →+*Omega) (hphi:Function.Injective phi)
   (P0 P1 V:Polynomial K) (hV:V≠0)
   (G:Poly3 Omega) (F:Poly4 K):
   residualAlgHom (phi P0) (phi V) (phi P1)
       (phi P0.derivative) (phi V.derivative) (phi P1.derivative) G∣
     RCN136.surfaceMap phi
       (globalResidualHom P0 P1 V F) ↔
     G∣RCN136.surfaceMap phi F:=by
 rw [surfaceMap_globalResidualHom_eq_residualAlgHom]
 exact residual_dvd_iff _ _ _ _ _ _
   ((map_ne_zero_iff phi hphi).mpr hV) _ _
theorem residual_dvd_pderiv_globalResidualHom_iff
   (phi:Polynomial K →+*Omega) (hphi:Function.Injective phi)
   (P0 P1 V:Polynomial K) (hV:V≠0)
   (G:Poly3 Omega) (F:Poly4 K):
   residualAlgHom (phi P0) (phi V) (phi P1)
       (phi P0.derivative) (phi V.derivative) (phi P1.derivative) G∣
     RCN136.surfaceMap phi
       (MvPolynomial.pderiv (2:Fin 4)
         (globalResidualHom P0 P1 V F)) ↔
     G∣RCN136.surfaceMap phi
       (MvPolynomial.pderiv (2:Fin 4) F):=by
 rw [surfaceMap_pderiv_globalResidualHom]
 have hv:phi V≠0:=(map_ne_zero_iff phi hphi).mpr hV
 have hu:IsUnit (MvPolynomial.C (phi V):Poly3 Omega):=
   (isUnit_iff_ne_zero.mpr hv).map MvPolynomial.C
 rw [hu.dvd_mul_left]
 exact residual_dvd_iff _ _ _ _ _ _ hv _ _
theorem residual_component_transport
   (phi:Polynomial K →+*Omega) (hphi:Function.Injective phi)
   (P0 P1 V:Polynomial K) (hV:V≠0)
   (F:Poly4 K) (G:Poly3 Omega)
   (hG:Irreducible G)
   (hdiv:G∣RCN136.surfaceMap phi F)
   (hr:0 < G.degreeOf 1)
   (hproper:¬ G∣RCN136.surfaceMap phi
     (MvPolynomial.pderiv (2:Fin 4) F))
   (p:RCN095.FlagDegree)
   (hflag:PolynomialInFlag p G):
   let Gres:=residualAlgHom (phi P0) (phi V) (phi P1)
     (phi P0.derivative) (phi V.derivative) (phi P1.derivative) G
   Irreducible Gres∧
     Gres∣RCN136.surfaceMap phi
       (globalResidualHom P0 P1 V F)∧
     0 < Gres.degreeOf 1∧
     ¬ Gres∣RCN136.surfaceMap phi
       (MvPolynomial.pderiv (2:Fin 4)
         (globalResidualHom P0 P1 V F))∧
     PolynomialInFlag p Gres:=by
 dsimp only
 have hv:phi V≠0:=(map_ne_zero_iff phi hphi).mpr hV
 refine ⟨(residual_irreducible_iff _ _ _ _ _ _ hv G).mpr hG,
   (residual_dvd_surfaceMap_globalResidualHom_iff
     phi hphi P0 P1 V hV G F).mpr hdiv,?_,?_,?_⟩
 · exact (residual_degreeOf_one_pos_iff _ _ _ _ _ _ hv G).mpr hr
 · exact (residual_dvd_pderiv_globalResidualHom_iff
     phi hphi P0 P1 V hV G F).not.mpr hproper
 · exact polynomialInFlag_residualAlgHom p G _ _ _ _ _ _ hflag
@[simp] theorem polynomial_eval₂_comp_C_X
   (phi:Polynomial K →+*Omega) (P:Polynomial K):
   P.eval₂ (phi.comp Polynomial.C) (phi Polynomial.X)=phi P:=by
 change (Polynomial.eval₂RingHom (phi.comp Polynomial.C)
   (phi Polynomial.X)) P=phi P
 congr 1
 apply Polynomial.ringHom_ext
 · intro a
   simp [RingHom.comp_apply]
 · simp
theorem eval_residualComponent_selectedPoint
   (phi:Polynomial K →+*Omega)
   (P0 P1 V C S:Polynomial K) (gamma:K) (G:Poly3 Omega)
   (hnormal:S=P0+Polynomial.C gamma*P1+V*C):
   MvPolynomial.eval (selectedPoint phi (fun _↦C) gamma)
       (residualAlgHom (phi P0) (phi V) (phi P1)
         (phi P0.derivative) (phi V.derivative) (phi P1.derivative) G)=
     MvPolynomial.eval (selectedPoint phi (fun _↦S) gamma) G:=by
 have hCpoint:selectedPoint phi (fun _↦C) gamma=
     ![phi C,phi C.derivative,(phi.comp Polynomial.C) gamma]:=by
   funext i
   fin_cases i <;>
     simp [selectedPoint,RCN231.polynomialPoint,
       RingHom.comp_apply]
 have hSpoint:selectedPoint phi (fun _↦S) gamma=
     ![phi S,phi S.derivative,(phi.comp Polynomial.C) gamma]:=by
   funext i
   fin_cases i <;>
     simp [selectedPoint,RCN231.polynomialPoint,
       RingHom.comp_apply]
 rw [hCpoint,hSpoint]
 change MvPolynomial.eval₂Hom (algebraMap Omega Omega)
     ![phi C,phi C.derivative,(phi.comp Polynomial.C) gamma]
       (residualAlgHom (phi P0) (phi V) (phi P1)
         (phi P0.derivative) (phi V.derivative) (phi P1.derivative) G)=
   MvPolynomial.eval₂Hom (algebraMap Omega Omega)
     ![phi S,phi S.derivative,(phi.comp Polynomial.C) gamma] G
 rw [eval₂Hom_residual]
 have hcoords:
     ![phi P0+phi V*phi C+phi P1*(phi.comp Polynomial.C) gamma,
       phi P0.derivative+phi V*phi C.derivative+
         phi V.derivative*phi C+
           phi P1.derivative*(phi.comp Polynomial.C) gamma,
       (phi.comp Polynomial.C) gamma]=
     ![phi S,phi S.derivative,(phi.comp Polynomial.C) gamma]:=by
   funext i
   fin_cases i <;>
     simp [hnormal,RingHom.comp_apply] <;> ring
 simpa using congrArg
   (fun q:Fin 3 → Omega↦
     MvPolynomial.eval₂Hom (algebraMap Omega Omega) q G) hcoords
theorem exists_residual_family_with_surface_data
   {iota:Type} [DecidableEq iota]
   (phi:Polynomial K →+*Omega) (hphi:Function.Injective phi)
   (I nodes:Finset iota) (x u0 u1:iota → K)
   (w e:ℕ) (hsub:I ⊆ nodes) (hIw:I.card ≤ w)
   (hinj:Set.InjOn x nodes)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hvalues:∀ gamma∈Gamma,∀ i∈I,
     (selected gamma).eval (x i)=u0 i+gamma*u1 i)
   (hno:NoLargeSelectedPencil selected Gamma w e)
   (F:Poly4 K)
   (hsolution:∀ gamma∈Gamma,
     RCN319.specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (RCN231.polynomialPoint
         (phi.comp Polynomial.C) (selected gamma) gamma (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0):
   ∃ P0 P1:Polynomial K,∃ residual:K → Polynomial K,
     P0.natDegree ≤ w∧P1.natDegree ≤ w∧
     (∀ gamma∈Gamma,
       (residual gamma).natDegree ≤ w-I.card)∧
     NoLargeSelectedPencil residual Gamma (w-I.card) e∧
     (∀ gamma∈Gamma,
       selected gamma=P0+Polynomial.C gamma*P1+
         Lagrange.nodal I x*residual gamma)∧
     (∀ gamma∈Gamma,∀ j∈nodes \ I,
       (selected gamma).eval (x j)=u0 j+gamma*u1 j →
         (residual gamma).eval (x j)=
           residualReceived I x u0 P0 j+
             gamma*residualReceived I x u1 P1 j)∧
     (∀ gamma∈Gamma,
       RCN319.specialization K (residual gamma) gamma
         (globalResidualHom P0 P1 (Lagrange.nodal I x) F)=0)∧
     ∀ gamma∈Gamma,
       MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
         (RCN231.polynomialPoint
           (phi.comp Polynomial.C) (residual gamma) gamma
             (phi Polynomial.X))
         (MvPolynomial.pderiv (2:Fin 4)
           (globalResidualHom P0 P1 (Lagrange.nodal I x) F))≠0:=by
 obtain ⟨P0,P1,residual,hP0,hP1,hresdeg,hnores,hnormal,
     hagree⟩:=exists_residual_family_with_incidence_data
   I nodes x u0 u1 w e hsub hIw hinj selected Gamma
     hdegree hvalues hno
 have hV:Lagrange.nodal I x≠0:=
   (Lagrange.nodal_monic (s:=I) (v:=x)).ne_zero
 have hVeval:(Lagrange.nodal I x).eval₂
     (phi.comp Polynomial.C) (phi Polynomial.X)≠0:=by
   rw [polynomial_eval₂_comp_C_X]
   exact (map_ne_zero_iff phi hphi).mpr hV
 refine ⟨P0,P1,residual,hP0,hP1,hresdeg,hnores,hnormal,
   ?_,?_,?_⟩
 · intro gamma hgamma j hj hagreement
   apply hagree gamma hgamma j
   · simpa only [Finset.mem_sdiff] using hj
   · exact hagreement
 · intro gamma hgamma
   apply globalResidual_solution
   rw [←hnormal gamma hgamma]
   exact hsolution gamma hgamma
 · intro gamma hgamma
   apply globalResidual_regular_at_polynomialPoint
     (phi.comp Polynomial.C) P0 P1 (Lagrange.nodal I x)
       (residual gamma) gamma (phi Polynomial.X) F hVeval
   rw [←hnormal gamma hgamma]
   exact hregular gamma hgamma
end
end ProximityPrize.SubmissionLower.RCN163
end PackedLegacy_BQ

/-! Packed from ProximityPrize.SubmissionLower.K5. -/
section PackedLegacy_K5
namespace ProximityPrize.SubmissionLower.RCN166
open RCN002 RCN136 RCN224 RCN139 RCN233 RCN231 RCN229 RCN313 RCN047 RCN147 RCN319 RCN065
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
 (phi:Polynomial K →+*Omega)
variable (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
 (F:MvPolynomial (Fin 4) K)
 (hF:surfaceMap phi F∈P)
 (hH:surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F)∉P)
theorem coordinate_y_affine_of_basefield_pencil
   (w:ℕ) (P0 P1:Polynomial K)
   (hp:truncatedPolynomial phi P F hF hH w=
     P0.map (componentCoefficients phi P)+
       Polynomial.C (coordinate Omega P 2)*
         P1.map (componentCoefficients phi P)):
   coordinate Omega P 0=algebraMap Omega (CoordinateField Omega P)
       ((P0.map (phi.comp Polynomial.C)).eval (phi Polynomial.X))+
     coordinate Omega P 2*algebraMap Omega (CoordinateField Omega P)
       ((P1.map (phi.comp Polynomial.C)).eval (phi Polynomial.X)):=by
 have hp':truncatedPolynomial phi P F hF hH w=
     (P0.map (phi.comp Polynomial.C)).map
         (algebraMap Omega (CoordinateField Omega P))+
       Polynomial.C (coordinate Omega P 2)*
         (P1.map (phi.comp Polynomial.C)).map
           (algebraMap Omega (CoordinateField Omega P)):=by
   simpa only [Polynomial.map_map,componentCoefficients] using hp
 rw [←truncatedPolynomial_initial_value phi P F hF hH w,hp']
 simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
   Polynomial.eval_map_apply]
include hF hH in
theorem identityNodes_card_le_of_r_dependent_principal_zero_safe
   {iota:Type} [DecidableEq iota]
   (nodes:Finset iota) (x u0 u1:iota → K) (w:ℕ)
   (hinj:Set.InjOn x nodes)
   (g:MvPolynomial (Fin 3) Omega) (hP:P=Ideal.span {g})
   (hr:0 < g.degreeOf 1):
   (identityNodes phi P F nodes x u0 u1 w).card ≤ w:=by
 by_contra h
 have hc:w < (identityNodes phi P F nodes x u0 u1 w).card:=
   Nat.lt_of_not_ge h
 obtain ⟨P0,P1,_,_,hp,_⟩:=
   exists_common_pencil_of_many_identities phi P F hF hH
     nodes x u0 u1 w hinj hc
     (fun t:Empty↦t.elim) (fun t:Empty↦t.elim)
     (fun t↦t.elim) (fun t↦t.elim)
 have hy:=coordinate_y_affine_of_basefield_pencil
   phi P F hF hH w P0 P1 hp
 exact not_y_affine_of_r_dependent_principal Omega P g hP hr _ _ hy
end
end ProximityPrize.SubmissionLower.RCN166
end PackedLegacy_K5

/-! Packed from ProximityPrize.SubmissionLower.E8. -/
section PackedLegacy_E8
namespace ProximityPrize.SubmissionLower.RCN275
open RCN136 RCN313 RCN174 RCN081 RCN234 RCN157 RCN156 RCN095
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
structure ResidualSupportParameters where
 s:ℕ
 ys:ℕ
 total:ℕ
 one_le_s:1 ≤ s
 s_le_ys:s ≤ ys
 ys_le_total:ys ≤ total
 two_le_ys:2 ≤ ys
 deriving DecidableEq
namespace ResidualSupportParameters
def agreementDirection (P:ResidualSupportParameters):FlagDegree:=
 ⟨2*(P.total-P.ys),2*(P.ys-P.s),2*P.s-1⟩
def residualAgreementFlag (P:ResidualSupportParameters) (d:ℕ):FlagDegree:=
 ⟨P.agreementDirection.zOnly*d,
   1+P.agreementDirection.yz*d,
   P.agreementDirection.all*d⟩
theorem residualAgreementFlag_ys (P:ResidualSupportParameters) (d:ℕ):
   (P.residualAgreementFlag d).yz+(P.residualAgreementFlag d).all=
     1+d*(2*P.ys-1):=by
 have hcoeff:2*(P.ys-P.s)+(2*P.s-1)=2*P.ys-1:=by
   rw [Nat.mul_sub_left_distrib]
   have hle:=Nat.mul_le_mul_left 2 P.s_le_ys
   have hpos:=P.one_le_s
   omega
 simp only [residualAgreementFlag,agreementDirection]
 rw [←hcoeff]
 ring
theorem residualAgreementFlag_total (P:ResidualSupportParameters) (d:ℕ):
   (P.residualAgreementFlag d).zOnly+
       (P.residualAgreementFlag d).yz+
       (P.residualAgreementFlag d).all=
     1+d*(2*P.total-1):=by
 have hcoeff:2*(P.total-P.ys)+2*(P.ys-P.s)+
     (2*P.s-1)=2*P.total-1:=by
   rw [Nat.mul_sub_left_distrib,Nat.mul_sub_left_distrib]
   have hle₁:=Nat.mul_le_mul_left 2 P.s_le_ys
   have hle₂:=Nat.mul_le_mul_left 2 P.ys_le_total
   have hpos:=P.one_le_s
   omega
 simp only [residualAgreementFlag,agreementDirection]
 rw [←hcoeff]
 ring
def acceptedSupport:ResidualSupportParameters where
 s:=8
 ys:=43
 total:=503
 one_le_s:=by norm_num
 s_le_ys:=by norm_num
 ys_le_total:=by norm_num
 two_le_ys:=by norm_num
def fixedMeetSupport:ResidualSupportParameters where
 s:=6
 ys:=34
 total:=604
 one_le_s:=by norm_num
 s_le_ys:=by norm_num
 ys_le_total:=by norm_num
 two_le_ys:=by norm_num
end ResidualSupportParameters
variable {K Omega:Type} [Field K] [Field Omega]
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
structure ResidualSupportData (P:ResidualSupportParameters) (F:Poly4 K):Prop where
 s_weight:wt residualSWeights F ≤ P.s
 ys_weight:wt residualYSWeights F ≤ P.ys
 total_weight:wt residualTotalWeights F ≤ P.total
namespace ResidualSupportData
theorem globalResidual
   {P:ResidualSupportParameters} {F:Poly4 K}
   (H:ResidualSupportData P F)
   (P0 P1 V:Polynomial K):
   ResidualSupportData P (globalResidualHom P0 P1 V F):=by
 refine ⟨?_,?_,?_⟩
 · exact (globalResidualHom_wt_le_pulled residualSWeights rfl
     P0 P1 V F).trans (by simpa [residualPullWeights_s] using H.s_weight)
 · exact (globalResidualHom_wt_le_pulled residualYSWeights rfl
     P0 P1 V F).trans (by simpa [residualPullWeights_ys] using H.ys_weight)
 · exact (globalResidualHom_wt_le_pulled residualTotalWeights rfl
     P0 P1 V F).trans (by
       simpa [residualPullWeights_total] using H.total_weight)
theorem coordinate_bounds
   {P:ResidualSupportParameters} {F:Poly4 K}
   (H:ResidualSupportData P F):
   F.degreeOf (1:Fin 4) ≤ P.ys∧
     F.degreeOf (2:Fin 4) ≤ P.s∧
     F.degreeOf (3:Fin 4) ≤ P.total:=by
 have hR:F.degreeOf (2:Fin 4) ≤ P.s:=by
   have hw:residualSWeights=Pi.single (2:Fin 4) 1:=by
     funext i
     fin_cases i <;> rfl
   have hs:=H.s_weight
   rw [hw,wt,MvPolynomial.weightedTotalDegree_piSingle] at hs
   exact hs
 have hY:F.degreeOf (1:Fin 4) ≤ P.ys:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   have hw:=(MvPolynomial.le_weightedTotalDegree residualYSWeights he).trans
     H.ys_weight
   rw [RCN081.weight_fin4] at hw
   change e 0*0+e 1*1+e 2*1+e 3*0 ≤ P.ys at hw
   norm_num at hw
   omega
 have hZ:F.degreeOf (3:Fin 4) ≤ P.total:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   have hw:=(MvPolynomial.le_weightedTotalDegree residualTotalWeights he).trans
     H.total_weight
   rw [RCN081.weight_fin4] at hw
   change e 0*0+e 1*1+e 2*1+e 3*1 ≤ P.total at hw
   norm_num at hw
   omega
 exact ⟨hY,hR,hZ⟩
theorem agreement_weight_bounds
   {P:ResidualSupportParameters} {F:Poly4 K}
   (H:ResidualSupportData P F)
   (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K):
   (agreementNumerator F d coeffs x u0 u1).degreeOf (2:Fin 4) ≤
       d*(2*P.s-1)∧
     wt residualYSWeights (agreementNumerator F d coeffs x u0 u1) ≤
       1+d*(2*P.ys-1)∧
     wt residualTotalWeights (agreementNumerator F d coeffs x u0 u1) ≤
       1+d*(2*P.total-1):=by
 obtain ⟨hY,hR,hZ⟩:=H.coordinate_bounds
 refine ⟨(agreementNumerator_degree_bounds F P.ys P.s P.total
   P.one_le_s hY hR hZ d coeffs x u0 u1).2.1,?_,?_⟩
 · have h:=agreementNumerator_wt_le_minkowski residualYSWeights rfl
     F P.ys (by change 1 ≤ P.ys;exact P.one_le_s.trans P.s_le_ys)
     (by change 2 ≤ P.ys;exact P.two_le_ys)
     (by change 1 ≤ 1;norm_num) H.ys_weight d coeffs x u0 u1
   have hcoeff:P.ys+(P.ys-1)=2*P.ys-1:=by omega
   apply h.trans_eq
   change max 1 0+d*(P.ys+(P.ys-1))=
     1+d*(2*P.ys-1)
   rw [hcoeff]
   norm_num
 · have htotalTwo:2 ≤ P.total:=P.two_le_ys.trans P.ys_le_total
   have honeTotal:1 ≤ P.total:=
     le_trans P.one_le_s (le_trans P.s_le_ys P.ys_le_total)
   have h:=agreementNumerator_wt_le_minkowski residualTotalWeights rfl
     F P.total (by change 1 ≤ P.total;exact honeTotal)
     (by change 2 ≤ P.total;exact htotalTwo)
     (by change 1 ≤ 1;norm_num) H.total_weight d coeffs x u0 u1
   have hcoeff:P.total+(P.total-1)=2*P.total-1:=by omega
   apply h.trans_eq
   change max 1 1+d*(P.total+(P.total-1))=
     1+d*(2*P.total-1)
   rw [hcoeff]
   norm_num
theorem surfaceMap_agreement_in_flag
   {P:ResidualSupportParameters}
   (phi:Polynomial K →+*Omega) {F:Poly4 K}
   (H:ResidualSupportData P F)
   (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K):
   PolynomialInFlag (P.residualAgreementFlag d)
     (surfaceMap phi (agreementNumerator F d coeffs x u0 u1)):=by
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp
   (support_surfaceMap_subset phi (agreementNumerator F d coeffs x u0 u1) he)
 obtain ⟨hR,hYS,hTotal⟩:=H.agreement_weight_bounds d coeffs x u0 u1
 have hqR:=(MvPolynomial.monomial_le_degreeOf (2:Fin 4) hq).trans hR
 have hqYS:=(MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hYS
 have hqTotal:=
   (MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hTotal
 rw [RCN081.weight_fin4] at hqYS hqTotal
 change q 0*0+q 1*1+q 2*1+q 3*0 ≤
   1+d*(2*P.ys-1) at hqYS
 change q 0*0+q 1*1+q 2*1+q 3*1 ≤
   1+d*(2*P.total-1) at hqTotal
 norm_num at hqYS hqTotal
 have hqR':q 2 ≤ (P.residualAgreementFlag d).all:=by
   change q 2 ≤ (2*P.s-1)*d
   rw [Nat.mul_comm]
   exact hqR
 change q 2 ≤ (P.residualAgreementFlag d).all∧
   q 1+q 2 ≤ (P.residualAgreementFlag d).yz+
     (P.residualAgreementFlag d).all∧
   q 1+q 2+q 3 ≤ (P.residualAgreementFlag d).zOnly+
     (P.residualAgreementFlag d).yz+
     (P.residualAgreementFlag d).all
 refine ⟨hqR',?_,?_⟩
 · rw [P.residualAgreementFlag_ys]
   exact hqYS
 · rw [P.residualAgreementFlag_total]
   exact hqTotal
end ResidualSupportData
end
end ProximityPrize.SubmissionLower.RCN275
end PackedLegacy_E8

/-! Packed from ProximityPrize.SubmissionLower.B. -/
section PackedLegacy_B
namespace ProximityPrize.SubmissionLower.RCN159
open scoped Classical
open RCN136 RCN231 RCN319 RCN313 RCN065 RCN238 RCN160 RCN157 RCN163 RCN166 RCN156 RCN275 RCN234 RCN094 RCN095 RCN125
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K Omega Iota:Type} [Field K] [Field Omega]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
abbrev Poly3 (Omega:Type) [Field Omega]:=MvPolynomial (Fin 3) Omega
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
structure ResidualStage
   (phi:Polynomial K →+*Omega) (Gamma:Finset K) (x:Iota → K)
   (p e:ℕ) [CharP Omega p] (flag:FlagDegree) (d:ℕ)
   (support:ResidualSupportParameters:=
     ResidualSupportParameters.acceptedSupport) where
 nodes:Finset Iota
 u0:Iota → K
 u1:Iota → K
 selected:K → Polynomial K
 F:Poly4 K
 G:Poly3 Omega
 irreducible_G:Irreducible G
 G_dvd_surface:G∣surfaceMap phi F
 y_dependent:0 < G.degreeOf 1
 regular_proper:¬ G∣surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F)
 flag_support:RCN095.PolynomialInFlag flag G
 surface_s_weight:wt residualSWeights F ≤ support.s
 surface_ys_weight:wt residualYSWeights F ≤ support.ys
 surface_total_weight:wt residualTotalWeights F ≤ support.total
 x_injective:Set.InjOn x nodes
 degree_le:∀ gamma∈Gamma,(selected gamma).natDegree ≤ d
 solution:∀ gamma∈Gamma,
   specialization K (selected gamma) gamma F=0
 regular:∀ gamma∈Gamma,
   MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
       (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0
 on_component:∀ gamma∈Gamma,
   MvPolynomial.eval (selectedPoint phi selected gamma) G=0
 no_large_pencil:NoLargeSelectedPencil selected Gamma d e
 characteristic_bound:d < p
namespace ResidualStage
variable {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {p e:ℕ} [CharP Omega p] {flag:FlagDegree} {d:ℕ}
 {support:ResidualSupportParameters}
def componentIdeal (S:ResidualStage phi Gamma x p e flag d support):
   Ideal (Poly3 Omega):=Ideal.span {S.G}
def identities (S:ResidualStage phi Gamma x p e flag d support):Finset Iota:=
 identityNodes phi S.componentIdeal S.F S.nodes x S.u0 S.u1 d
def Agrees (S:ResidualStage phi Gamma x p e flag d support)
   (gamma:K) (i:Iota):Prop:=
 (S.selected gamma).eval (x i)=S.u0 i+gamma*S.u1 i
local instance (S:ResidualStage phi Gamma x p e flag d support):
   ∀ gamma i,Decidable (S.Agrees gamma i):=fun _ _↦Classical.propDecidable _
def agreementFiber (S:ResidualStage phi Gamma x p e flag d support)
   (gamma:K):Finset Iota:=
 S.nodes.filter (S.Agrees gamma)
theorem componentIdeal_isPrime
   (S:ResidualStage phi Gamma x p e flag d support):S.componentIdeal.IsPrime:=by
 exact Ideal.isPrime_span_singleton_of_prime S.irreducible_G.prime
theorem surface_mem_componentIdeal
   (S:ResidualStage phi Gamma x p e flag d support):
   surfaceMap phi S.F∈S.componentIdeal:=by
 exact Ideal.mem_span_singleton.mpr S.G_dvd_surface
theorem regularity_not_mem_componentIdeal
   (S:ResidualStage phi Gamma x p e flag d support):
   surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) S.F)∉
     S.componentIdeal:=by
 intro h
 exact S.regular_proper (Ideal.mem_span_singleton.mp h)
theorem selected_point_ideal
   (S:ResidualStage phi Gamma x p e flag d support)
   {gamma:K} (hgamma:gamma∈Gamma):
   S.componentIdeal ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint phi S.selected gamma)).toRingHom:=by
 change Ideal.span {S.G} ≤
   RingHom.ker
     (MvPolynomial.aeval (selectedPoint phi S.selected gamma)).toRingHom
 rw [Ideal.span_le]
 intro Q hQ
 simp only [Set.mem_singleton_iff] at hQ
 subst Q
 exact S.on_component gamma hgamma
theorem agrees_on_identities
   (S:ResidualStage phi Gamma x p e flag d support):
   ∀ gamma∈Gamma,∀ i∈S.identities,S.Agrees gamma i:=by
 let P:=S.componentIdeal
 letI:P.IsPrime:=S.componentIdeal_isPrime
 intro gamma hgamma i hi
 exact selected_agrees_on_identity_nodes
   phi P S.F S.nodes x S.u0 S.u1 p d S.characteristic_bound
   (S.selected gamma) gamma (S.degree_le gamma hgamma)
   (S.solution gamma hgamma) (S.regular gamma hgamma)
   (S.selected_point_ideal hgamma) i hi
theorem identities_card_le
   (S:ResidualStage phi Gamma x p e flag d support):S.identities.card ≤ d:=by
 let P:=S.componentIdeal
 letI:P.IsPrime:=S.componentIdeal_isPrime
 exact identityNodes_card_le_of_r_dependent_principal_zero_safe
   phi P S.F S.surface_mem_componentIdeal S.regularity_not_mem_componentIdeal
   S.nodes x S.u0 S.u1 d S.x_injective S.G rfl S.y_dependent
theorem advance
   (hphi:Function.Injective phi)
   (S:ResidualStage phi Gamma x p e flag d support)
   (hne:S.identities≠∅):
   0 < S.identities.card∧
     ∃ Snext:ResidualStage phi Gamma x p e flag
         (d-S.identities.card) support,
       Snext.nodes=S.nodes \ S.identities∧
       (∀ gamma∈Gamma,∀ i∈S.identities,
         S.Agrees gamma i)∧
       ∀ gamma∈Gamma,∀ i∈Snext.nodes,
         S.Agrees gamma i → Snext.Agrees gamma i:=by
 classical
 let P:=S.componentIdeal
 letI:P.IsPrime:=S.componentIdeal_isPrime
 let J:=S.identities
 have hJsub:J ⊆ S.nodes:=identityNodes_subset
   phi P S.F S.nodes x S.u0 S.u1 d
 have hJcard:J.card ≤ d:=S.identities_card_le
 have hJpos:0 < J.card:=Finset.card_pos.mpr
   (Finset.nonempty_iff_ne_empty.mpr (by simpa only [J] using hne))
 have hvalues:∀ gamma∈Gamma,∀ i∈J,
     (S.selected gamma).eval (x i)=S.u0 i+gamma*S.u1 i:=by
   intro gamma hgamma i hi
   exact S.agrees_on_identities gamma hgamma i hi
 obtain ⟨P0,P1,residual,hP0,hP1,hresdeg,hnores,hnormal,
     hagree,hsolution,hregular⟩:=
   exists_residual_family_with_surface_data
     phi hphi J S.nodes x S.u0 S.u1 d e hJsub hJcard S.x_injective
     S.selected Gamma S.degree_le hvalues S.no_large_pencil S.F
     S.solution S.regular
 let V:Polynomial K:=Lagrange.nodal J x
 have hV:V≠0:=(Lagrange.nodal_monic (s:=J) (v:=x)).ne_zero
 let Fres:Poly4 K:=globalResidualHom P0 P1 V S.F
 let Gres:Poly3 Omega:=
   residualAlgHom (phi P0) (phi V) (phi P1)
     (phi P0.derivative) (phi V.derivative) (phi P1.derivative) S.G
 obtain ⟨hGirred,hGdiv,hGy,hGproper,hGflag⟩:=
   residual_component_transport phi hphi P0 P1 V hV S.F S.G
     S.irreducible_G S.G_dvd_surface S.y_dependent S.regular_proper
     flag S.flag_support
 let hsupport:ResidualSupportData support S.F:=
   ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
 have hsupportRes:=hsupport.globalResidual P0 P1 V
 let u0res:Iota → K:=fun i↦residualReceived J x S.u0 P0 i
 let u1res:Iota → K:=fun i↦residualReceived J x S.u1 P1 i
 let Snext:ResidualStage phi Gamma x p e flag (d-J.card) support:={
   nodes:=S.nodes \ J
   u0:=u0res
   u1:=u1res
   selected:=residual
   F:=Fres
   G:=Gres
   irreducible_G:=hGirred
   G_dvd_surface:=hGdiv
   y_dependent:=hGy
   regular_proper:=hGproper
   flag_support:=hGflag
   surface_s_weight:=hsupportRes.s_weight
   surface_ys_weight:=hsupportRes.ys_weight
   surface_total_weight:=hsupportRes.total_weight
   x_injective:=S.x_injective.mono (Finset.sdiff_subset)
   degree_le:=hresdeg
   solution:=hsolution
   regular:=hregular
   on_component:=by
     intro gamma hgamma
     have heval:=eval_residualComponent_selectedPoint
       phi P0 P1 V (residual gamma) (S.selected gamma) gamma S.G
         (hnormal gamma hgamma)
     change MvPolynomial.eval
       (selectedPoint phi (fun _↦residual gamma) gamma) Gres=0
     exact heval.trans (S.on_component gamma hgamma)
   no_large_pencil:=hnores
   characteristic_bound:=lt_of_le_of_lt (Nat.sub_le d J.card)
     S.characteristic_bound
 }
 refine ⟨?hpos,Snext,rfl,?_,?_⟩
 · simpa only [J] using hJpos
 · intro gamma hgamma i hi
   exact S.agrees_on_identities gamma hgamma i hi
 · intro gamma hgamma i hi hold
   exact hagree gamma hgamma i (by simpa [Snext,J] using hi) hold
theorem advance_card
   (hphi:Function.Injective phi)
   (S:ResidualStage phi Gamma x p e flag d support)
   (hne:S.identities≠∅):
   ∃ Snext:ResidualStage phi Gamma x p e flag
       (d-S.identities.card) support,
     Snext.nodes.card=S.nodes.card-S.identities.card∧
     ∀ gamma∈Gamma,
       (S.agreementFiber gamma).card-S.identities.card ≤
         (Snext.agreementFiber gamma).card:=by
 letI:S.componentIdeal.IsPrime:=S.componentIdeal_isPrime
 obtain ⟨_,Snext,hnodes,hidAgree,hdescend⟩:=S.advance hphi hne
 have hIdentityNodesSubset:S.identities ⊆ S.nodes:=by
   exact identityNodes_subset
     phi S.componentIdeal S.F S.nodes x S.u0 S.u1 d
 refine ⟨Snext,?_,?_⟩
 · rw [hnodes,Finset.card_sdiff_of_subset hIdentityNodesSubset]
 · intro gamma hgamma
   have hIdentitySubset:S.identities ⊆ S.agreementFiber gamma:=by
     intro i hi
     exact Finset.mem_filter.mpr ⟨
       (identityNodes_subset phi S.componentIdeal S.F
         S.nodes x S.u0 S.u1 d) hi,
       hidAgree gamma hgamma i hi⟩
   have hRemainingSubset:
       S.agreementFiber gamma \ S.identities ⊆
         Snext.agreementFiber gamma:=by
     intro i hi
     obtain ⟨holdFiber,hnotIdentity⟩:=Finset.mem_sdiff.mp hi
     obtain ⟨hinode,hold⟩:=Finset.mem_filter.mp holdFiber
     apply Finset.mem_filter.mpr
     refine ⟨?_,hdescend gamma hgamma i ?_ hold⟩
     · rw [hnodes]
       exact Finset.mem_sdiff.mpr ⟨hinode,hnotIdentity⟩
     · rw [hnodes]
       exact Finset.mem_sdiff.mpr ⟨hinode,hnotIdentity⟩
   calc
     (S.agreementFiber gamma).card-S.identities.card=
         (S.agreementFiber gamma \ S.identities).card:=by
       rw [Finset.card_sdiff_of_subset hIdentitySubset]
     _ ≤ (Snext.agreementFiber gamma).card:=
       Finset.card_le_card hRemainingSubset
structure TerminalDescendant
   (S:ResidualStage phi Gamma x p e flag d support) where
 degree:ℕ
 degree_le:degree ≤ d
 stage:ResidualStage phi Gamma x p e flag degree support
 terminal:stage.identities=∅
 nodes_card:stage.nodes.card=S.nodes.card-(d-degree)
 agreement_card:∀ gamma∈Gamma,
   (S.agreementFiber gamma).card-(d-degree) ≤
     (stage.agreementFiber gamma).card
theorem proper_agreement_of_terminal
   (S:ResidualStage phi Gamma x p e flag d support)
   (hterminal:S.identities=∅) {i:Iota} (hi:i∈S.nodes):
   ¬ S.G∣agreementPolynomial phi S.F d (x i) (S.u0 i) (S.u1 i):=by
 intro hdvd
 have hmem:i∈S.identities:=by
   apply Finset.mem_filter.mpr
   exact ⟨hi,Ideal.mem_span_singleton.mpr hdvd⟩
 rw [hterminal] at hmem
 simpa using hmem
theorem exists_terminal_descendant
   (hphi:Function.Injective phi)
   (S:ResidualStage phi Gamma x p e flag d support):
   Nonempty S.TerminalDescendant:=by
 induction d using Nat.strong_induction_on with
 | h d ih =>
     by_cases hterminal:S.identities=∅
     · exact ⟨{
         degree:=d
         degree_le:=le_rfl
         stage:=S
         terminal:=hterminal
         nodes_card:=by simp
         agreement_card:=by simp
       }⟩
     · have hk:S.identities.card ≤ d:=S.identities_card_le
       have hkpos:0 < S.identities.card:=Finset.card_pos.mpr
         (Finset.nonempty_iff_ne_empty.mpr hterminal)
       obtain ⟨Snext,hnodes,hagreements⟩:=
         S.advance_card hphi hterminal
       have hdegree_lt:d-S.identities.card < d:=by omega
       obtain ⟨Dnext⟩:=ih (d-S.identities.card) hdegree_lt Snext
       have hDle:Dnext.degree ≤ d-S.identities.card:=
         Dnext.degree_le
       have hdegree_split:d-Dnext.degree=
           S.identities.card+
             ((d-S.identities.card)-Dnext.degree):=by
         omega
       refine ⟨{
         degree:=Dnext.degree
         degree_le:=Dnext.degree_le.trans (Nat.sub_le d S.identities.card)
         stage:=Dnext.stage
         terminal:=Dnext.terminal
         nodes_card:=?_
         agreement_card:=?_
       }⟩
       · rw [Dnext.nodes_card,hnodes]
         rw [hdegree_split]
         exact Nat.sub_sub _ _ _
       · intro gamma hgamma
         have hstep:=hagreements gamma hgamma
         have htail:=Dnext.agreement_card gamma hgamma
         have hmono:
             ((S.agreementFiber gamma).card-S.identities.card)-
                 ((d-S.identities.card)-Dnext.degree) ≤
               (Snext.agreementFiber gamma).card-
                 ((d-S.identities.card)-Dnext.degree):=
           Nat.sub_le_sub_right hstep _
         calc
           (S.agreementFiber gamma).card-(d-Dnext.degree)=
               ((S.agreementFiber gamma).card-S.identities.card)-
                 ((d-S.identities.card)-Dnext.degree):=by
             rw [hdegree_split]
             exact (Nat.sub_sub _ _ _).symm
           _ ≤ (Snext.agreementFiber gamma).card-
                 ((d-S.identities.card)-Dnext.degree):=hmono
           _ ≤ (Dnext.stage.agreementFiber gamma).card:=htail
end ResidualStage
end
end ProximityPrize.SubmissionLower.RCN159
end PackedLegacy_B

/-! Packed from ProximityPrize.SubmissionLower.D8. -/
section PackedLegacy_D8
namespace ProximityPrize.SubmissionLower.RCN221
open scoped Classical BigOperators
open RCN223 RCN135 RCN136 RCN138 RCN137 RCN267 RCN081 RCN238 RCN231 RCN174 RCN319 RCN243 RCN222 RCN266 RCN159 RCN156 RCN275 RCN234 RCN095 RCN214
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
variable (K:Type) [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)
def geometricFlag {F:MvPolynomial (Fin 4) K}
   (g:GeometricFactor K F):FlagDegree:=
 ⟨g.1.degreeOf (2:Fin 3),g.1.degreeOf (0:Fin 3),
   g.1.degreeOf (1:Fin 3)⟩
theorem polynomialIn_geometricFlag {F:MvPolynomial (Fin 4) K}
   (g:GeometricFactor K F):PolynomialInFlag (geometricFlag K g) g.1:=by
 intro d hd
 have h0:=MvPolynomial.monomial_le_degreeOf (0:Fin 3) hd
 have h1:=MvPolynomial.monomial_le_degreeOf (1:Fin 3) hd
 have h2:=MvPolynomial.monomial_le_degreeOf (2:Fin 3) hd
 change d 1 ≤ g.1.degreeOf 1∧
   d 0+d 1 ≤ g.1.degreeOf 0+g.1.degreeOf 1∧
   d 0+d 1+d 2 ≤
     g.1.degreeOf 2+g.1.degreeOf 0+g.1.degreeOf 1
 omega
theorem residual_surface_weights_of_box
   (F:MvPolynomial (Fin 4) K)
   (hbox:F∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap):
   wt residualSWeights F ≤ 8∧
     wt residualYSWeights F ≤ 43∧
     wt residualTotalWeights F ≤ 503:=by
 constructor
 · apply (weightedTotalDegree_le_iff residualSWeights F 8).mpr
   intro d hd
   have hb:d 1+d 3 ≤ seedTotalCap∧d 2 ≤ slopeCap∧
       d 0+w*d 1+(w-1)*d 2 < weightedCap:=hbox hd
   rw [weight_fin4]
   rw [show residualSWeights 0=0 by rfl,
     show residualSWeights 1=0 by rfl,
     show residualSWeights 2=1 by rfl,
     show residualSWeights 3=0 by rfl]
   simp only [Nat.mul_zero,Nat.mul_one,Nat.zero_add,Nat.add_zero]
   simpa only [slopeCap] using hb.2.1
 · constructor
   · apply (weightedTotalDegree_le_iff residualYSWeights F 43).mpr
     intro d hd
     have hb:d 1+d 3 ≤ seedTotalCap∧d 2 ≤ slopeCap∧
         d 0+w*d 1+(w-1)*d 2 < weightedCap:=hbox hd
     rw [weight_fin4]
     rw [show residualYSWeights 0=0 by rfl,
       show residualYSWeights 1=1 by rfl,
       show residualYSWeights 2=1 by rfl,
       show residualYSWeights 3=0 by rfl]
     simp only [Nat.mul_zero,Nat.mul_one,Nat.zero_add,Nat.add_zero]
     norm_num [weightedCap,RCN223.multiplicity,
       agreements,n,errors,w] at hb
     omega
   · apply (weightedTotalDegree_le_iff residualTotalWeights F 503).mpr
     intro d hd
     have hb:d 1+d 3 ≤ seedTotalCap∧d 2 ≤ slopeCap∧
         d 0+w*d 1+(w-1)*d 2 < weightedCap:=hbox hd
     rw [weight_fin4]
     rw [show residualTotalWeights 0=0 by rfl,
       show residualTotalWeights 1=1 by rfl,
       show residualTotalWeights 2=1 by rfl,
       show residualTotalWeights 3=1 by rfl]
     simp only [Nat.mul_zero,Nat.mul_one,Nat.zero_add,Nat.add_zero]
     norm_num [seedTotalCap,slopeCap] at hb
     omega
variable {Iota:Type}
local instance:DecidableEq Iota:=Classical.decEq Iota
def geometricResidualStageOfSupport
   (support:ResidualSupportParameters)
   {pchar errorCap degree:ℕ} [CharP K pchar]
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hRpos:0 < F.degreeOf (2:Fin 4))
   (hRsmall:F.degreeOf (2:Fin 4) < pchar)
   (hsupport:ResidualSupportData support F)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ degree)
   (hsolutions:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hnoPencil:NoLargeSelectedPencil selected Gamma degree errorCap)
   (hdegreeChar:degree < pchar)
   (g:GeometricFactor K F):
   letI:CharP (GenericField K) pchar:=genericField_charP K pchar
   ResidualStage (polynomialEmbedding K)
     (geometricSeeds K F selected Gamma g) x pchar errorCap
     (geometricFlag K g) degree support:=by
 classical
 letI:CharP (GenericField K) pchar:=genericField_charP K pchar
 have hgspec:=surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2
 have hgirred:=hgspec.1
 have hgdiv:=hgspec.2
 have hgate:=geometric_factor_regular_gate K (GenericField K) F hF pchar
   hRpos hRsmall g.1 hgirred
   (by simpa only [canonical_geometricSurfaceMap] using hgdiv)
 have hsub:=geometricSeeds_subset K F selected Gamma g
 exact {
   nodes:=nodes
   u0:=u0
   u1:=u1
   selected:=selected
   F:=F
   G:=g.1
   irreducible_G:=hgirred
   G_dvd_surface:=hgdiv
   y_dependent:=hgate.1
   regular_proper:=by
     simpa only [canonical_geometricSurfaceMap] using hgate.2.2.2.2
   flag_support:=polynomialIn_geometricFlag K g
   surface_s_weight:=hsupport.s_weight
   surface_ys_weight:=hsupport.ys_weight
   surface_total_weight:=hsupport.total_weight
   x_injective:=hinj
   degree_le:=fun gamma hgamma↦hdegree gamma (hsub hgamma)
   solution:=fun gamma hgamma↦hsolutions gamma (hsub hgamma)
   regular:=fun gamma hgamma↦
     selectedPoint_regular_of_specialization K F selected gamma
       (hregular gamma (hsub hgamma))
   on_component:=fun gamma hgamma↦(Finset.mem_filter.mp hgamma).2
   no_large_pencil:=noLargeSelectedPencil_mono selected Gamma _ degree errorCap
     hsub hnoPencil
   characteristic_bound:=hdegreeChar
 }
def geometricResidualStage
   [CharP K prime]
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hRpos:0 < F.degreeOf (2:Fin 4))
   (hbox:F∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hsolutions:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w errors)
   (g:GeometricFactor K F):
   letI:CharP (GenericField K) prime:=genericField_charP K prime
   ResidualStage (polynomialEmbedding K)
     (geometricSeeds K F selected Gamma g) x prime errors
     (geometricFlag K g) w:=by
 have hRsmall:F.degreeOf (2:Fin 4) < prime:=
   (degreeOf_R_le_of_mem_box F weightedCap w seedTotalCap slopeCap hbox).trans_lt
     (by norm_num [slopeCap,prime])
 have hsupport:=residual_surface_weights_of_box K F hbox
 exact geometricResidualStageOfSupport K
   ResidualSupportParameters.acceptedSupport F hF hRpos hRsmall
   ⟨hsupport.1,hsupport.2.1,hsupport.2.2⟩ selected Gamma nodes x u0 u1
   hinj hdegree hsolutions hregular hnoPencil
   (by norm_num [w,prime]) g
end
end ProximityPrize.SubmissionLower.RCN221
end PackedLegacy_D8

end Compact_PackedLegacyCore1

