import ProximityPrize.SubmissionLower.Part.F005_07
section Compact_PackedLegacyCore2
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

def activeFactors (F N:Poly):Finset Poly:=
 (normalizedFactorSet F).filter fun g↦¬ g∣N∧MvPolynomial.pderiv (1:Fin 3) g≠0
theorem activeFactors_spec (F N:Poly) (g:↥(activeFactors F N)):
   Irreducible g.1∧g.1∣F∧¬ g.1∣N∧MvPolynomial.pderiv (1:Fin 3) g.1≠0:=by
 have h:=Finset.mem_filter.mp g.2
 exact ⟨(normalizedFactorSet_spec F g.1 h.1).1,
   (normalizedFactorSet_spec F g.1 h.1).2,h.2⟩
theorem activeFactors_mixed_sum_le (F N:Poly) (hF:F≠0)
   (p q r:FlagDegree) (hsupport:PolynomialInFlag p F):
   (∑ g:↥(activeFactors F N),flagMixed (exactFlag g.1) q r) ≤ flagMixed p q r:=by
 have hc:=inFlag_weight_caps F p hsupport
 have hw (w:Fin 3 → ℕ):
     (∑ g:↥(activeFactors F N),MvPolynomial.weightedTotalDegree w g.1) ≤
       MvPolynomial.weightedTotalDegree w F:=by
   rw [Finset.sum_coe_sort]
   exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans
     (sum_weightedTotalDegree_le_of_prod_dvd_fin3 w (normalizedFactorSet F) id F hF
       (normalizedFactorSet_product_dvd F hF))
 apply sum_flagMixed_le_of_cumulative
 · simpa only [(exactFlag_cumulative _).1] using (hw flagSWeights).trans hc.1
 · calc
     _=∑ g:↥(activeFactors F N),MvPolynomial.weightedTotalDegree flagYSWeights g.1:=
       Finset.sum_congr rfl (fun g _↦(exactFlag_cumulative g.1).2.1)
     _ ≤ _:=(hw flagYSWeights).trans hc.2.1
 · calc
     _=∑ g:↥(activeFactors F N),MvPolynomial.weightedTotalDegree flagTotalWeights g.1:=
       Finset.sum_congr rfl (fun g _↦(exactFlag_cumulative g.1).2.2)
     _ ≤ _:=(hw flagTotalWeights).trans hc.2.2
variable [IsAlgClosed K]
def IsolatedPoint (F N A:Poly) (v:Fin 3 → K):Prop:=
 ∀ D:Ideal Poly,D.IsPrime →
   (∀ w:Fin 3 → K,D≠RingHom.ker (MvPolynomial.aeval w).toRingHom) →
   D ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom → F∈D → N∈D → A∉D
theorem exists_active_factor_of_isolated (F N A R:Poly) (hF:F≠0)
   (v:Fin 3 → K) (hvF:MvPolynomial.eval v F=0)
   (hvA:MvPolynomial.eval v A=0) (hvR:MvPolynomial.eval v R≠0)
   (hvD:MvPolynomial.eval v (MvPolynomial.pderiv (1:Fin 3) F)≠0)
   (hi:IsolatedPoint F N A v):
   ∃ g:↥(activeFactors F N),MvPolynomial.eval v g.1=0:=by
 obtain ⟨g,hg,hgv⟩:=exists_normalizedFactorSet_zero (MvPolynomial.eval v) F hF hvF
 have hs:=normalizedFactorSet_spec F g hg
 have hproper:¬ g∣N:=by
   intro hgN
   obtain ⟨D,hD⟩:=exists_regular_component K g A R v hgv hvA hvR
   have hmem:=regularComponent_G_mem K g A R D
   exact hi D.1 inferInstance (regularComponent_ne_point K g A R D) hD
     (D.1.mem_of_dvd hs.2 hmem) (D.1.mem_of_dvd hgN hmem)
     (regularComponent_T_mem K g A R D)
 have hderiv:MvPolynomial.pderiv (1:Fin 3) g≠0:=by
   intro hz
   obtain ⟨b,hb⟩:=hs.2
   apply hvD
   rw [hb,MvPolynomial.pderiv_mul,map_add,map_mul,map_mul,hz,map_zero,hgv]
   ring
 exact ⟨⟨g,Finset.mem_filter.mpr ⟨hg,hproper,hderiv⟩⟩,hgv⟩
theorem isolated_points_card_le (F N A R:Poly) (p q r:FlagDegree)
   (hF:F≠0) (hFp:PolynomialInFlag p F)
   (hNq:PolynomialInFlag q N) (hAr:PolynomialInFlag r A)
   (base:∀ g:↥(activeFactors F N),∀ C:RegularComponent K g.1 N R,
     SeparableLiteralCoordinate C.1)
   (hY:∀ g:↥(activeFactors F N),∀ C:RegularComponent K g.1 N R,
     LiteralProjectionGate C 0)
   (hZ:∀ g:↥(activeFactors F N),∀ C:RegularComponent K g.1 N R,
     LiteralProjectionGate C 2)
   (points:Finset (Fin 3 → K))
   (hcover:∀ v∈points,∃ g:↥(activeFactors F N),MvPolynomial.eval v g.1=0)
   (hN:∀ v∈points,MvPolynomial.eval v N=0)
   (hA:∀ v∈points,MvPolynomial.aeval v A=0)
   (hR:∀ v∈points,MvPolynomial.eval v R≠0)
   (hisolated:∀ g:↥(activeFactors F N),∀ C:RegularComponent K g.1 N R,
     ∀ v∈points,C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom → A∉C.1):
   points.card ≤ flagMixed p q r:=by
 classical
 letI:DecidableEq K:=Classical.decEq K
 let S (g:↥(activeFactors F N)):Finset (Fin 3 → K):=
   points.filter fun (v:Fin 3 → K)↦MvPolynomial.eval v g.1=(0:K)
 have hcoverage:points ⊆ Finset.univ.biUnion S:=by
   intro v hv
   obtain ⟨g,hg⟩:=hcover v hv
   exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hv,hg⟩⟩
 have hcount (g:↥(activeFactors F N)):(S g).card ≤ flagMixed (exactFlag g.1) q r:=by
   have hg:=activeFactors_spec F N g
   obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamily_of_nested (exactFlag g.1) q
     (base g) (hY g) (hZ g) hg.2.2.2 hg.1 hg.2.2.1
     ((support_subset_flagSupport_iff _ _).mpr (polynomialIn_exactFlag g.1))
     ((support_subset_flagSupport_iff _ _).mpr hNq)
   let B:=P.toPrimeFlagBudgetFamily
   calc
     (S g).card ≤ ∑ C:RegularComponent K g.1 N R,
         (componentSeeds K g.1 N R (S g) id C).card:=
       card_le_sum_componentSeeds K g.1 N R (S g) id
         (fun v hv↦(Finset.mem_filter.mp hv).2)
         (fun v hv↦hN v (Finset.mem_filter.mp hv).1)
         (fun v hv↦hR v (Finset.mem_filter.mp hv).1)
     _ ≤ ∑ C:RegularComponent K g.1 N R,B.weightedCost r C:=by
       apply Finset.sum_le_sum
       intro C _
       by_cases hempty:(componentSeeds K g.1 N R (S g) id C).Nonempty
       · obtain ⟨v,hv⟩:=hempty
         have hvP:=componentSeeds_on_prime K g.1 N R (S g) id C v hv
         have hvS:=componentSeeds_subset K g.1 N R (S g) id C hv
         apply (B.primeBudget C).zero_le r A hAr
           (hisolated g C v (Finset.mem_filter.mp hvS).1 hvP)
         · intro w hw
           exact componentSeeds_on_prime K g.1 N R (S g) id C w hw
         · intro w hw
           exact hA w (Finset.mem_filter.mp
             (componentSeeds_subset K g.1 N R (S g) id C hw)).1
       · simp only [Finset.not_nonempty_iff_eq_empty.mp hempty,Finset.card_empty,Nat.zero_le]
     _ ≤ flagMixed (exactFlag g.1) q r:=B.sum_weightedCost_le r
 exact ((Finset.card_le_card hcoverage).trans Finset.card_biUnion_le).trans
   ((Finset.sum_le_sum (fun g _↦hcount g)).trans (activeFactors_mixed_sum_le F N hF p q r hFp))
theorem degreeOf_le_flag_total (F:Poly) (p:FlagDegree) (hF:PolynomialInFlag p F)
   (i:Fin 3):F.degreeOf i ≤ p.zOnly+p.yz+p.all:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have h:=(hF d hd).2.2
 have hi:i=0∨i=1∨i=2:=by omega
 rcases hi with rfl | rfl | rfl <;> omega
theorem exists_small_projection_data (F N R:Poly) (hF:F≠0)
   (p q:FlagDegree) (hFp:PolynomialInFlag p F) (hNq:PolynomialInFlag q N)
   (c:ℕ) [CharP K c] (hdeg:p.zOnly+p.yz+p.all < c)
   (hmix:2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c):
   ∃ base:∀ g:↥(activeFactors F N),∀ C:RegularComponent K g.1 N R,
       SeparableLiteralCoordinate C.1,
     (∀ g:↥(activeFactors F N),∀ C:RegularComponent K g.1 N R,LiteralProjectionGate C 0)∧
     (∀ g:↥(activeFactors F N),∀ C:RegularComponent K g.1 N R,LiteralProjectionGate C 2):=by
 have hgate (g:↥(activeFactors F N)) (C:RegularComponent K g.1 N R)
     (i:Fin 3) (hi:Transcendental K (coordinate K C.1 i)):
     letI:Algebra (RatFunc K) (CoordinateField K C.1):=rationalBaseAlgebra K C.1 i hi
     FiniteDimensional (RatFunc K) (CoordinateField K C.1)∧
       Algebra.IsSeparable (RatFunc K) (CoordinateField K C.1):=by
   have hg:=activeFactors_spec F N g
   have hgdeg (j:Fin 3):g.1.degreeOf j ≤ p.zOnly+p.yz+p.all:=
     (coordinate_degree_le_of_dvd j g.1 F hg.2.1 hF).trans (degreeOf_le_flag_total F p hFp j)
   have hNdeg (j:Fin 3):=degreeOf_le_flag_total N q hNq j
   apply finite_separable_at_of_original_coordinate_gate K C.1 i hi c g.1 N
     hg.1 (regularComponent_G_mem K _ _ _ C) (regularComponent_T_mem K _ _ _ C)
     hg.2.2.1 (fun j↦(hgdeg j).trans_lt hdeg)
   have hprod (u v:Fin 3):N.degreeOf u*g.1.degreeOf v+g.1.degreeOf u*N.degreeOf v ≤
       2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all):=by
     calc
       _ ≤ (q.zOnly+q.yz+q.all)*(p.zOnly+p.yz+p.all)+
           (p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all):=
         Nat.add_le_add (Nat.mul_le_mul (hNdeg u) (hgdeg v))
           (Nat.mul_le_mul (hgdeg u) (hNdeg v))
       _=_:=by ring
   have hi3:i=0∨i=1∨i=2:=by omega
   rcases hi3 with rfl | rfl | rfl
   · rw [coordinateMixedDegree_zero];exact (hprod 1 2).trans_lt hmix
   · rw [coordinateMixedDegree_one];exact (hprod 0 2).trans_lt hmix
   · rw [coordinateMixedDegree_two];exact (hprod 0 1).trans_lt hmix
 refine ⟨fun g C↦Classical.choice (exists_separableLiteralCoordinate_of_YZ_gates C.1
   (regularComponent_ne_point K _ _ _ C) (hgate g C 0) (hgate g C 2)),?_,?_⟩
 · exact fun g C↦hgate g C 0
 · exact fun g C↦hgate g C 2
end
end ProximityPrize.SubmissionLower.RCN084
end PackedLegacy_Y5

/-! Packed from ProximityPrize.SubmissionLower.D1. -/
section PackedLegacy_D1
namespace ProximityPrize.SubmissionLower.RCN206
open scoped Classical BigOperators
open RCN095 RCN084
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
def surfaceFlag (a b s:ℕ):FlagDegree:=⟨a,b+1,s+2⟩
def denominatorFlag (a b s:ℕ):FlagDegree:=⟨a,b+1,s+1⟩
def numeratorFlag (a b s:ℕ):FlagDegree:=⟨a,b,s+3⟩
def fiberFlag (a b s:ℕ):FlagDegree:=⟨a,b+1,s+3⟩
def normalFlag (a b s:ℕ):FlagDegree:=⟨a,b,s⟩
def directionFlag (a b s:ℕ):FlagDegree:=⟨2*a,2*b+1,2*s+3⟩
def centreFlag (a b s:ℕ):FlagDegree:=unitYZFlag+directionFlag a b s
def qeff (a b s:ℕ) (p:FlagDegree):ℕ:=
 flagMixed p (directionFlag a b s) (normalFlag a b s)+
   flagMixed p (fiberFlag a b s) (surfaceFlag a b s)
def quad (a b s:ℕ) (p:FlagDegree):ℕ:=flagMixed p (directionFlag a b s) (directionFlag a b s)
def ell (a b s:ℕ) (p:FlagDegree):ℕ:=flagMixed p (directionFlag a b s) unitYZFlag
def unitBase (p:FlagDegree):ℕ:=flagMixed p unitYZFlag unitYZFlag
def lin (a b s:ℕ) (p:FlagDegree):ℕ:=flagMixed p (centreFlag a b s) (directionFlag a b s)
def unit (a b s:ℕ) (p:FlagDegree):ℕ:=flagMixed p (centreFlag a b s) (centreFlag a b s)
def zSlope (a b s:ℕ) (p:FlagDegree):ℕ:=flagMixed p (directionFlag a b s) unitZFlag
def zBase (a b s:ℕ) (p:FlagDegree):ℕ:=flagMixed p (centreFlag a b s) unitZFlag
def yzSlope (a b s:ℕ) (p:FlagDegree):ℕ:=flagMixed p (directionFlag a b s) unitYZFlag
def yzBase (a b s:ℕ) (p:FlagDegree):ℕ:=flagMixed p (centreFlag a b s) unitYZFlag
def weightedMixed (p q r:FlagDegree):ℕ:=
 r.zOnly*flagMixed p q unitZFlag+r.yz*flagMixed p q unitYZFlag+r.all*flagMixed p q unitAllFlag
section Cumulative
variable {I:Type*} [Fintype I] (flags:I → FlagDegree) (p:FlagDegree)
 (hs:(∑ i,(flags i).all) ≤ p.all)
 (hm:(∑ i,((flags i).yz+(flags i).all)) ≤ p.yz+p.all)
 (ht:(∑ i,((flags i).zOnly+(flags i).yz+(flags i).all)) ≤ p.zOnly+p.yz+p.all)
include hs hm ht
end Cumulative
end
end ProximityPrize.SubmissionLower.RCN206
end PackedLegacy_D1

/-! Packed from ProximityPrize.SubmissionLower.CommonShearDegreePrototype. -/

/-! Packed from ProximityPrize.SubmissionLower.DD. -/
section PackedLegacy_DD
namespace ProximityPrize.SubmissionLower.RCN023
open scoped Classical BigOperators
open Field RCN002 RCN005 RCN007
noncomputable section
variable (K:Type) [Field K]
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
def ProjectionsFinite:Prop:=
 ∀ (i:Fin 3) (hi:Transcendental K (coordinate K P i)),
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   FiniteDimensional (RatFunc K) (CoordinateField K P)
variable [IsAlgClosed K]
end
end ProximityPrize.SubmissionLower.RCN023
end PackedLegacy_DD

/-! Packed from ProximityPrize.SubmissionLower.X0. -/
section PackedLegacy_X0
namespace ProximityPrize.SubmissionLower.RCN368
open scoped Classical
noncomputable section
end
end ProximityPrize.SubmissionLower.RCN368
end PackedLegacy_X0

/-! Packed from ProximityPrize.SubmissionLower.I2. -/
section PackedLegacy_I2
namespace ProximityPrize.SubmissionLower.RCN067
open scoped Classical
open RCN002 RCN007
 RCN238
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
variable (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
theorem point_coordinate_eq_scalar
   (i:Fin 3) (c:Ω)
   (hc:algebraMap Ω (CoordinateField Ω P) c=coordinate Ω P i)
   (v:Fin 3 → Ω)
   (hv:P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom):
   v i=c:=by
 let Q:MvPolynomial (Fin 3) Ω:=MvPolynomial.X i-MvPolynomial.C c
 have hQ:Q∈P:=by
   rw [←aeval_coordinate_ker Ω P]
   change MvPolynomial.aeval (coordinate Ω P) Q=0
   simp only [Q,map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C]
   exact sub_eq_zero.mpr hc.symm
 have hz:=hv hQ
 change MvPolynomial.aeval v Q=0 at hz
 simpa only [Q,map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C,
   sub_eq_zero,Algebra.algebraMap_self_apply] using hz
theorem selected_seed_set_card_le_one_of_seedCoordinate_isAlgebraic
   (selected:K → Polynomial K) (Γ:Finset K)
   (hpoint:∀ γ∈Γ,
     P ≤ RingHom.ker
       (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (hZ:IsAlgebraic Ω (coordinate Ω P 2)):
   Γ.card ≤ 1:=by
 obtain ⟨c,hc⟩:=coordinate_eq_scalar_of_isAlgebraic Ω P 2 hZ
 apply Finset.card_le_one.mpr
 intro γ hγ η hη
 have hcγ:=point_coordinate_eq_scalar P 2 c hc
   (selectedPoint φ selected γ) (hpoint γ hγ)
 have hcη:=point_coordinate_eq_scalar P 2 c hc
   (selectedPoint φ selected η) (hpoint η hη)
 have hc:(φ.comp Polynomial.C) γ=(φ.comp Polynomial.C) η:=by
   simpa only [selectedPoint_seed] using hcγ.trans hcη.symm
 exact (φ.comp Polynomial.C).injective hc
end
end ProximityPrize.SubmissionLower.RCN067
end PackedLegacy_I2

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.DT. -/
section PackedLegacy_DT
namespace ProximityPrize.SubmissionLower.RCN045
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
open RCN002 RCN005 RCN006
 RCN007
open RCN136 RCN231 RCN229 RCN313 RCN065 RCN319 RCN238 RCN264 RCN243 RCN306 RCN023 RCN001 RCN008 RCN369 RCN344 RCN368 RCN022 RCN067
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
 (φ:Polynomial K →+*Ω)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
variable [IsAlgClosed Ω]
variable (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
private def adaptiveFamilyFiniteSummary {I:Type} [Fintype I]
   (Q:I → Ideal (MvPolynomial (Fin 3) Ω)) [∀ i,(Q i).IsPrime]
   (A:∀ i,Algebra (RatFunc Ω) (CoordinateField Ω (Q i)))
   (B:ℕ):Prop:=
 letI:=A
 (∀ i,FiniteDimensional (RatFunc Ω) (CoordinateField Ω (Q i)))∧
   (∑ i,Module.finrank (RatFunc Ω) (CoordinateField Ω (Q i))) ≤ B
def adaptiveShearCap (cap:Fin 3 → ℕ):Fin 3 → ℕ:=
 ![cap 0,cap 1,cap 2+2*cap 1]
def shearedPolynomialCap (cap:Fin 3 → ℕ):Fin 3 → ℕ:=
 ![cap 0,cap 1,cap 2+cap 1]
def adaptiveShearCost (cap:Fin 3 → ℕ):ℕ:=
 componentCost P (adaptiveShearCap cap)
def AdaptiveShearFiberCertificate
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (Γ:Finset K) (w:ℕ) (cap:Fin 3 → ℕ):Prop:=
 ∀ (x u₀ u₁:K),agreementPolynomial φ F w x u₀ u₁∉P →
   (∀ j,(agreementPolynomial φ F w x u₀ u₁).degreeOf j ≤ cap j) →
     (Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)).card ≤
       adaptiveShearCost P cap
def globalShearDegree (dS:ℕ):Fin 3 → ℕ:=
 ![actualCoordinateDegree Ω P 0,dS,actualCoordinateDegree Ω P 2]
def globalShearCost (dS:ℕ) (cap:Fin 3 → ℕ):ℕ:=
 ∑ i,shearedPolynomialCap cap i*globalShearDegree P dS i
theorem globalShearCost_eq (dS:ℕ) (cap:Fin 3 → ℕ):
   globalShearCost P dS cap=
     cap 0*actualCoordinateDegree Ω P 0+cap 1*dS+
       (cap 2+cap 1)*actualCoordinateDegree Ω P 2:=by
 simp [globalShearCost,globalShearDegree,shearedPolynomialCap,
   Fin.sum_univ_three]
def GlobalShearFiberCertificate
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (Γ:Finset K) (w dS:ℕ) (cap:Fin 3 → ℕ):Prop:=
 ∀ (x u₀ u₁:K),agreementPolynomial φ F w x u₀ u₁∉P →
   (∀ j,(agreementPolynomial φ F w x u₀ u₁).degreeOf j ≤ cap j) →
     (Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)).card ≤
       globalShearCost P dS cap
theorem globalShearFiberCertificate_of_card_le_one
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (Γ:Finset K) (w dS:ℕ) (cap:Fin 3 → ℕ)
   (hcard:Γ.card ≤ 1) (hcost:1 ≤ globalShearCost P dS cap):
   GlobalShearFiberCertificate φ P F selected Γ w dS cap:=by
 intro x u₀ u₁ _ _
 exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
   (hcard.trans hcost)
theorem coordinateDegree_pos_of_transcendental_finite
   (hfinite:ProjectionsFinite Ω P) (j:Fin 3)
   (hj:Transcendental Ω (coordinate Ω P j)):
   1 ≤ actualCoordinateDegree Ω P j:=by
 letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
   rationalBaseAlgebra Ω P j hj
 letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω P):=hfinite j hj
 rw [actualCoordinateDegree_of_transcendental Ω P j hj]
 exact Module.finrank_pos
abbrev rationalElementEmbedding
   (k L:Type*) [Field k] [Field L] [Algebra k L]
   (s:L) (hs:Transcendental k s):RatFunc k →ₐ[k] L:=
 elementEmbedding k L s hs
def BadRShearCoordinateCertificate (hfinite:ProjectionsFinite Ω P):Prop:=
 ∀ (hR:Transcendental Ω (coordinate Ω P 1))
   (hZ:Transcendental Ω (coordinate Ω P 2)),
   (letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
     rationalBaseAlgebra Ω P 1 hR;
     ¬ Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)) →
   (letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
     rationalBaseAlgebra Ω P 2 hZ;
     Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)) →
   ∃ hS:Transcendental Ω (coordinate Ω P 1+coordinate Ω P 2),
     letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
       (rationalElementEmbedding Ω (CoordinateField Ω P)
         (coordinate Ω P 1+coordinate Ω P 2) hS).toRingHom.toAlgebra;
     Module.finrank (RatFunc Ω) (CoordinateField Ω P) ≤
       actualCoordinateDegree Ω P 1+actualCoordinateDegree Ω P 2
def shearedRingCoordinates:Fin 3 → CoordinateRing Ω P:=
 ![quotientCoordinate Ω P 0,
   quotientCoordinate Ω P 1+quotientCoordinate Ω P 2,
   quotientCoordinate Ω P 2]
def ShearedPolynomialTransport
   (A:MvPolynomial (Fin 3) Ω) (cap:Fin 3 → ℕ):Prop:=
 ∃ B:MvPolynomial (Fin 3) Ω,
   (∀ i,B.degreeOf i ≤ shearedPolynomialCap cap i)∧
     MvPolynomial.eval₂Hom (algebraMap Ω (CoordinateRing Ω P))
       (shearedRingCoordinates P) B=Ideal.Quotient.mk P A
def ShearedAgreementTransportCertificate
   (F:MvPolynomial (Fin 4) K) (w:ℕ) (cap:Fin 3 → ℕ):Prop:=
 ∀ (x u₀ u₁:K),
   (∀ i,(agreementPolynomial φ F w x u₀ u₁).degreeOf i ≤ cap i) →
     ShearedPolynomialTransport P (agreementPolynomial φ F w x u₀ u₁) cap
def actualCoordinateDataAt
   (hfinite:ProjectionsFinite Ω P) (i:Fin 3)
   (hsep:∀ hi:Transcendental Ω (coordinate Ω P i),
     letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
       rationalBaseAlgebra Ω P i hi
     Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)):
   Coordinate Ω (CoordinateField Ω P):=
 if hi:Transcendental Ω (coordinate Ω P i) then
   Sum.inr {
     embedding:=rationalBaseEmbedding Ω P i hi
     finite:=hfinite i hi
     separable:=hsep hi}
 else
   Sum.inl ((coordinate_eq_scalar_of_isAlgebraic Ω P i (not_not.mp hi)).choose)
def shearCoordinateData
   (hS:Transcendental Ω (coordinate Ω P 1+coordinate Ω P 2))
   (hfiniteS:
     letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
       (rationalElementEmbedding Ω (CoordinateField Ω P)
         (coordinate Ω P 1+coordinate Ω P 2) hS).toRingHom.toAlgebra
     FiniteDimensional (RatFunc Ω) (CoordinateField Ω P))
   (hsepS:
     letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
       (rationalElementEmbedding Ω (CoordinateField Ω P)
         (coordinate Ω P 1+coordinate Ω P 2) hS).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)):
   Coordinate Ω (CoordinateField Ω P):=
 Sum.inr {
   embedding:=rationalElementEmbedding Ω (CoordinateField Ω P)
     (coordinate Ω P 1+coordinate Ω P 2) hS
   finite:=hfiniteS
   separable:=hsepS}
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem prime_seed_incidence_sharp_global_shear
   (hfinite:ProjectionsFinite Ω P)
   (hnonpoint:∀ v:Fin 3 → Ω,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K)
   (hF:surfaceMap φ F∈P)
   (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
   (dS:ℕ)
   (hfiber:GlobalShearFiberCertificate φ P F selected Γ w dS cap):
   Γ.card*(a-w) ≤ (nodes.card-w)*globalShearCost P dS cap+
     (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
 classical
 let I:=identityNodes φ P F nodes x u₀ u₁ w
 let relation:K → ι → Prop:=
   fun γ i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i
 by_cases hI:I.card ≤ w
 · have hproperFiber:∀ i∈nodes \ I,
       (Γ.filter (fun γ↦relation γ i)).card ≤ globalShearCost P dS cap:=by
     intro i hi
     obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
     have hproper:agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)∉P:=by
       intro hmem
       apply hnotI
       exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
     exact hfiber (x i) (u₀ i) (u₁ i) hproper (hcap i hinodes)
   have hcount:=RCN173.sharp_incidence_bound relation Γ nodes I a w
     (globalShearCost P dS cap) (identityNodes_subset φ P F nodes x u₀ u₁ w)
     hI hwa han hagreement hproperFiber
   omega
 · have hc:w < I.card:=Nat.lt_of_not_ge hI
   have hvalues:∀ (t:{γ:K//γ∈Γ}) i,i∈I →
       (selected t.1).eval (x i)=u₀ i+t.1*u₁ i:=by
     intro t
     exact selected_agrees_on_identity_nodes φ P F nodes x u₀ u₁ p w hchar
       (selected t.1) t.1 (hdegree t.1 t.2) (hsolution t.1 t.2)
       (hregular t.1 t.2) (hpoint t.1 t.2)
   obtain ⟨P₀,P₁,h₀,h₁,_,hpencil⟩:=
     exists_common_pencil_of_many_identities φ P F hF hH nodes x u₀ u₁ w hinj hc
       (fun t:{γ:K//γ∈Γ}↦t.1) (fun t↦selected t.1)
       (fun t↦hdegree t.1 t.2) hvalues
   have hfilter:Γ.filter
       (fun γ↦selected γ=P₀+Polynomial.C γ*P₁)=Γ:=
     Finset.filter_eq_self.mpr (fun γ hγ↦hpencil ⟨γ,hγ⟩)
   have hΓ:Γ.card ≤ e+1:=by
     have h:=hnoPencil P₀ P₁ h₀ h₁
     rwa [hfilter] at h
   have hZ:=seed_transcendental_of_many_identities φ P F hF hH
     nodes x u₀ u₁ w hw hinj hc hnonpoint
   have hδ:=coordinateDegree_pos_of_transcendental_finite P hfinite (2:Fin 3) hZ
   have hcharge:Γ.card*(a-w) ≤
       (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
     calc
       _ ≤ (e+1)*(a-w):=Nat.mul_le_mul_right _ hΓ
       _ ≤ _:=by
         simpa only [Nat.mul_one] using
           Nat.mul_le_mul_left ((e+1)*(a-w)) hδ
   omega
theorem family_finite_and_sum_actualCoordinateDegree_at_le
   {I:Type} [Fintype I]
   (Q:I → Ideal (MvPolynomial (Fin 3) Ω)) [∀ i,(Q i).IsPrime]
   (hinjQ:Function.Injective Q) (j:Fin 3)
   (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hGmem:∀ i,G∈Q i)
   (hTmem:∀ i,T∈Q i) (hproper:¬ G∣T):
   (∀ i (hi:Transcendental Ω (coordinate Ω (Q i) j)),
     letI:Algebra (RatFunc Ω) (CoordinateField Ω (Q i)):=
       rationalBaseAlgebra Ω (Q i) j hi
     FiniteDimensional (RatFunc Ω) (CoordinateField Ω (Q i)))∧
     (∑ i,actualCoordinateDegree Ω (Q i) j) ≤
       coordinateMixedDegree Ω G T j:=by
 classical
 let s:Set I:={i | Transcendental Ω (coordinate Ω (Q i) j)}
 let D:s → ℕ:=fun i↦
   letI:Algebra (RatFunc Ω) (CoordinateField Ω (Q i)):=
     rationalBaseAlgebra Ω (Q i) j i.2
   Module.finrank (RatFunc Ω) (CoordinateField Ω (Q i))
 letI:∀ i:s,Algebra (RatFunc Ω) (CoordinateField Ω (Q i)):=
   fun i↦rationalBaseAlgebra Ω (Q i) j i.2
 have hinj':Function.Injective (fun i:s↦Q i):=by
   intro i k h
   apply Subtype.ext
   exact hinjQ h
 have hresult:=original_finite_sum_finrank_bound_without_separability
   Ω (Equiv.swap 0 j) (fun i:s↦Q i) (fun i↦i.2) hinj'
   G T hG (fun i↦hGmem i) (fun i↦hTmem i) hproper
 change adaptiveFamilyFiniteSummary (fun i:s↦Q i)
   (fun i↦rationalBaseAlgebra Ω (Q i) j i.2)
   (coordinateMixedDegree Ω G T j) at hresult
 constructor
 · intro i hi
   exact hresult.1 ⟨i,hi⟩
 · calc
     (∑ i,actualCoordinateDegree Ω (Q i) j)=∑ i:s,D i:=by
       apply Finset.sum_congr_set s
         (fun i↦actualCoordinateDegree Ω (Q i) j) D
       · intro i hi
         exact actualCoordinateDegree_of_transcendental Ω (Q i) j hi
       · intro i hi
         change ¬ Transcendental Ω (coordinate Ω (Q i) j) at hi
         exact dif_neg hi
     _ ≤ coordinateMixedDegree Ω G T j:=by
       exact hresult.2
end
end ProximityPrize.SubmissionLower.RCN045
end PackedLegacy_DT

/-! Packed from ProximityPrize.SubmissionLower.EO. -/
section PackedLegacy_EO
namespace ProximityPrize.SubmissionLower.RCN142
open RCN002 RCN007 RCN045 RCN023
noncomputable section
variable (K:Type) [Field K] [IsAlgClosed K]
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
theorem transcendental_add_smul_of_transcendental_isAlgebraic
   (r z:CoordinateField K P) (a:K)
   (hr:Transcendental K r) (hz:IsAlgebraic K z):
   Transcendental K (r+a • z):=by
 intro hs
 apply hr
 have hscaled:IsAlgebraic K (a • z):=hz.smul a
 have hsub:IsAlgebraic K ((r+a • z)-a • z):=hs.sub hscaled
 simpa using hsub
end
end ProximityPrize.SubmissionLower.RCN142
end PackedLegacy_EO

/-! Packed from ProximityPrize.SubmissionLower.CommonShearFiberPrototype. -/

/-! Packed from ProximityPrize.SubmissionLower.CommonShearFamilyPrototype. -/

/-! Packed from ProximityPrize.SubmissionLower.CommonShearConsumerPrototype. -/

/-! Packed from ProximityPrize.SubmissionLower.CommonShearTightPrototype. -/

/-! Packed from ProximityPrize.SubmissionLower.L2. -/
section PackedLegacy_L2
namespace ProximityPrize.SubmissionLower.RCN181
open scoped BigOperators
open Set UniqueFactorizationMonoid RCN100 RCN180 RCN137
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
local instance:StrongNormalizationMonoid (Poly4 K) :=
 UniqueFactorizationMonoid.strongNormalizationMonoid
local instance:NormalizedGCDMonoid (Poly4 K) :=
 UniqueFactorizationMonoid.toNormalizedGCDMonoid (Poly4 K)
def submoduleReconstructLinear {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K)) :
   V →ₗ[K] Poly4 K :=
 (reconstructLinear (K:=K) D w L s).comp V.subtype
theorem submoduleReconstructLinear_injective {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K)) :
   Function.Injective (submoduleReconstructLinear V):=by
 intro x y h
 apply Subtype.ext
 exact reconstructLinear_injective (K:=K) D w L s h
def commonDivisorProof {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] (b:Module.Basis ι K V) :
   ∀ v:V,commonGCD V b ∣ submoduleReconstructLinear V v:=by
 intro v
 exact commonGCD_dvd V b v
def commonQuotientLinear {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] (b:Module.Basis ι K V)
   (hH:commonGCD V b ≠ 0):V →ₗ[K] Poly4 K :=
 quotientLinear (submoduleReconstructLinear V) (commonGCD V b) hH
   (commonDivisorProof V b)
def quotientDvdSubmodule {V:Type*} [AddCommGroup V] [Module K V]
   (q:V →ₗ[K] Poly4 K) (F:Poly4 K):Submodule K V where
 carrier:={v | F ∣ q v}
 zero_mem':=by simp
 add_mem':=by
   intro x y hx hy
   change F ∣ q x at hx
   change F ∣ q y at hy
   change F ∣ q (x + y)
   rw [map_add]
   exact dvd_add hx hy
 smul_mem':=by
   intro a x hx
   change F ∣ q x at hx
   change F ∣ q (a • x)
   rw [map_smul,MvPolynomial.smul_eq_C_mul]
   exact dvd_mul_of_dvd_right hx _
theorem quotientDvdSubmodule_ne_top {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] (b:Module.Basis ι K V)
   (hH:commonGCD V b ≠ 0) (F:Poly4 K) (hF:Irreducible F) :
   quotientDvdSubmodule (commonQuotientLinear V b hH) F ≠ ⊤:=by
 intro htop
 have hall:∀ v:V,F ∣ commonQuotientLinear V b hH v:=by
   intro v
   have hv:v ∈ quotientDvdSubmodule (commonQuotientLinear V b hH) F:=by
     rw [htop]
     trivial
   exact hv
 have hmul:commonGCD V b * F ∣ commonGCD V b:=by
   apply (dvd_commonGCD_iff V b (commonGCD V b * F)).2
   intro v
   have hq:=hall v
   have heq:=recon_eq_mul_quotientPolynomial
     (submoduleReconstructLinear V) (commonGCD V b)
     (commonDivisorProof V b) v
   change commonGCD V b * F ∣ submoduleReconstructLinear V v
   rw [heq]
   exact mul_dvd_mul_left (commonGCD V b) hq
 have hFone:F ∣ (1:Poly4 K):=by
   apply (mul_dvd_mul_iff_left hH).mp
   simpa using hmul
 exact hF.not_isUnit (isUnit_iff_dvd_one.mpr hFone)
theorem exists_common_quotient_isRelPrime {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] [Nonempty ι] (b:Module.Basis ι K V)
   (hH:commonGCD V b ≠ 0) (P:Poly4 K) (hP:P ≠ 0)
   (hcard:(normalizedFactorSet P).card < ENat.card K) :
   ∃ v:V,v ≠ 0 ∧ IsRelPrime (commonQuotientLinear V b hH v) P:=by
 classical
 letI:DecidableEq (Fin 4):=Classical.decEq _
 by_cases hunit:IsUnit P
 · let i:ι:=Classical.choice inferInstance
   refine ⟨b i,b.ne_zero i,hunit.isRelPrime_right⟩
 · let S:=normalizedFactorSet P
   have hSne:S.Nonempty:=by
     obtain ⟨F,hF⟩:=exists_mem_normalizedFactors hP hunit
     exact ⟨F,Multiset.mem_toFinset.mpr hF⟩
   let bad:S → Submodule K V:=fun F ↦
     quotientDvdSubmodule (commonQuotientLinear V b hH) F.1
   have hproper:∀ F:S,bad F ≠ ⊤:=by
     intro F
     exact quotientDvdSubmodule_ne_top V b hH F.1
       (normalizedFactorSet_spec P F.1 F.2).1
   have hsmall:(Finset.univ:Finset S).card < ENat.card K:=by
     simpa [S] using hcard
   have hss:=RCN133.finite_iUnion_ssubset
     (Finset.univ:Finset S) bad hproper hsmall
   obtain ⟨v,hv⟩:=Set.ssubset_univ_iff_nonempty_compl.mp hss
   have havoid:∀ F:S,v ∉ bad F:=by
     intro F hmem
     apply hv
     simp only [Set.mem_iUnion,Finset.mem_univ,true_and]
     exact ⟨F,trivial,hmem⟩
   have hv0:v ≠ 0:=by
     intro hz
     obtain ⟨F,hF⟩:=hSne
     have hnot:=havoid ⟨F,hF⟩
     apply hnot
     subst v
     change F ∣ commonQuotientLinear V b hH 0
     simp
   refine ⟨v,hv0,?_⟩
   apply WfDvdMonoid.isRelPrime_of_no_irreducible_factors
   · intro hzero
     exact hP hzero.2
   · intro z hz hzq hzPdiv
     obtain ⟨F,hFnorm,hassoc⟩ :=
       exists_mem_normalizedFactors_of_dvd hP hz hzPdiv
     have hnot:=havoid
       (⟨F,Multiset.mem_toFinset.mpr hFnorm⟩:S)
     apply hnot
     change F ∣ commonQuotientLinear V b hH v
     exact hassoc.dvd_iff_dvd_left.mp hzq
theorem irreducible_positive_degree_sum_fin4
   (F:Poly4 K) (hF:Irreducible F) :
   0 < F.degreeOf 0 + F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3:=by
 by_contra hn
 have hsum:F.degreeOf 0 + F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3 = 0 :=
   Nat.eq_zero_of_not_pos hn
 have h0:F.degreeOf (0:Fin 4) = 0:=by omega
 have h1:F.degreeOf (1:Fin 4) = 0:=by omega
 have h2:F.degreeOf (2:Fin 4) = 0:=by omega
 have h3:F.degreeOf (3:Fin 4) = 0:=by omega
 have hdeg (i:Fin 4):F.degreeOf i = 0:=by
   fin_cases i
   · simpa using h0
   · simpa using h1
   · simpa using h2
   · simpa using h3
 have heq:F = MvPolynomial.C (F.coeff 0):=by
   apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
   apply Nat.eq_zero_of_le_zero
   rw [MvPolynomial.totalDegree,Finset.sup_le_iff]
   intro d hd
   have hd0:d = 0:=by
     ext i
     have hi:=MvPolynomial.monomial_le_degreeOf i hd
     rw [hdeg i] at hi
     exact Nat.eq_zero_of_le_zero hi
   simp [hd0]
 have hc:F.coeff 0 ≠ 0:=by
   intro hz
   apply hF.ne_zero
   rw [heq,hz,map_zero]
 apply hF.not_isUnit
 rw [heq]
 exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
theorem normalizedFactorSet_card_le_degree_sum_fin4
   (P:Poly4 K) (hP:P ≠ 0) :
   (normalizedFactorSet P).card ≤
     P.degreeOf 0 + P.degreeOf 1 + P.degreeOf 2 + P.degreeOf 3:=by
 classical
 calc
   (normalizedFactorSet P).card =
       ∑ _F ∈ normalizedFactorSet P,(1:ℕ):=by simp
   _ ≤ ∑ F ∈ normalizedFactorSet P,
       (F.degreeOf 0 + F.degreeOf 1 + F.degreeOf 2 + F.degreeOf 3):=by
     apply Finset.sum_le_sum
     intro F hF
     exact irreducible_positive_degree_sum_fin4 F
       (normalizedFactorSet_spec P F hF).1
   _ = (∑ F ∈ normalizedFactorSet P,F.degreeOf 0) +
         (∑ F ∈ normalizedFactorSet P,F.degreeOf 1) +
         (∑ F ∈ normalizedFactorSet P,F.degreeOf 2) +
         (∑ F ∈ normalizedFactorSet P,F.degreeOf 3):=by
     simp only [Finset.sum_add_distrib]
   _ ≤ P.degreeOf 0 + P.degreeOf 1 + P.degreeOf 2 + P.degreeOf 3:=by
     gcongr <;> exact normalizedFactorSet_degree_budget P hP _
theorem degreeOf_X_le_of_mem_flagBox (P:Poly4 K)
   (D w L s:ℕ) (hbox:P ∈ globalCoefficientBox K D w L s) :
   P.degreeOf (0:Fin 4) ≤ D - 1:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have hc:=(hbox hd).2.2
 omega
theorem normalizedFactorSet_card_le_of_mem_flagBox
   (P:Poly4 K) (D w L s:ℕ) (hw:0 < w) (hP:P ≠ 0)
   (hbox:P ∈ globalCoefficientBox K D w L s) :
   (normalizedFactorSet P).card ≤
     (D - 1) + (D - 1) / w + s + L:=by
 have hsum:=normalizedFactorSet_card_le_degree_sum_fin4 P hP
 have hX:=degreeOf_X_le_of_mem_flagBox P D w L s hbox
 have hY:P.degreeOf (1:Fin 4) ≤ (D - 1) / w:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   apply (Nat.le_div_iff_mul_le hw).mpr
   have hc:=(hbox hd).2.2
   have hm:d 1 * w = w * d 1:=Nat.mul_comm _ _
   omega
 have hR:P.degreeOf (2:Fin 4) ≤ s:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.1
 have hZ:P.degreeOf (3:Fin 4) ≤ L:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   have hL:=(hbox hd).1
   omega
 omega
end
end ProximityPrize.SubmissionLower.RCN181
end PackedLegacy_L2

/-! Packed from ProximityPrize.SubmissionLower.L4. -/
section PackedLegacy_L4
namespace ProximityPrize.SubmissionLower.RCN183
open scoped BigOperators
open ProximityPrize.Benchmark RCN100 RCN119 RCN101 RCN180 RCN181 RCN137 RCN130 RCN234 RCN156 RCN081
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance:StrongNormalizationMonoid GlobalPoly :=
 UniqueFactorizationMonoid.strongNormalizationMonoid
local instance:NormalizedGCDMonoid GlobalPoly :=
 UniqueFactorizationMonoid.toNormalizedGCDMonoid GlobalPoly
def agreements6733:ℕ:=182042
abbrev AKernel (u₀ u₁:IRSProfile.Index → IRSProfile.Field) :=
 ConstraintKernel (K:=IRSProfile.Field)
   7645764 131071 84439 12 42 IRSProfile.domain u₀ u₁
abbrev BKernel (u₀ u₁:IRSProfile.Index → IRSProfile.Field) :=
 ConstraintKernel (K:=IRSProfile.Field)
   14745402 131071 1262 25 81 IRSProfile.domain u₀ u₁
abbrev CKernel (u₀ u₁:IRSProfile.Index → IRSProfile.Field) :=
 ConstraintKernel (K:=IRSProfile.Field)
   7463722 131071 41787 12 41 IRSProfile.domain u₀ u₁
theorem gateA :
   Fintype.card IRSProfile.Index * localRankBound 42 84439 12 <
     coefficientCount 7645764 131071 84439 12:=by
 rw [show Fintype.card IRSProfile.Index = 262144 by
   norm_num [IRSProfile.Index]]
 rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
   7645764 131071 84439 12 59 (by decide) (by decide)]
 decide
theorem gateB :
   Fintype.card IRSProfile.Index * localRankBound 81 1262 25 <
     coefficientCount 14745402 131071 1262 25:=by
 rw [show Fintype.card IRSProfile.Index = 262144 by
   norm_num [IRSProfile.Index]]
 rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
   14745402 131071 1262 25 113 (by decide) (by decide)]
 decide
theorem field_cardinality :
   Fintype.card IRSProfile.Field = (2130706433:ℕ) ^ 6:=by
 norm_num [IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize]
theorem normalizedFactorSet_card_lt_field_of_mem_flagBox
   (P:GlobalPoly) (D L s:ℕ) (hP:P ≠ 0)
   (hbox:P ∈ globalCoefficientBox IRSProfile.Field D 131071 L s)
   (hsmall:(D - 1) + (D - 1) / 131071 + s + L <
     (2130706433:ℕ) ^ 6) :
   (normalizedFactorSet P).card < ENat.card IRSProfile.Field:=by
 have hle:=normalizedFactorSet_card_le_of_mem_flagBox
   P D 131071 L s (by decide) hP hbox
 rw [ENat.card_eq_coe_fintype_card,field_cardinality]
 exact_mod_cast hle.trans_lt hsmall
theorem commonGCD_mem_flagBox
   {D L s:ℕ}
   (V:Submodule IRSProfile.Field (CoefficientIndex D 131071 L s → IRSProfile.Field))
   {ι:Type*} [Fintype ι] [Nonempty ι]
   (b:Module.Basis ι IRSProfile.Field V) :
   commonGCD V b ∈ globalCoefficientBox IRSProfile.Field D 131071 L s:=by
 let i:ι:=Classical.choice inferInstance
 let Q:=reconstruct IRSProfile.Field D 131071 L s (b i).1
 have hQ:Q ≠ 0:=by
   apply reconstruct_ne_zero IRSProfile.Field D 131071 L s
   intro hb
   apply b.ne_zero i
   exact Subtype.ext hb
 exact mem_flagGlobalCoefficientBox_of_dvd (commonGCD V b) Q
   D 131071 L s hQ (commonGCD_dvd_basis V b i)
   (reconstruct_mem_globalCoefficientBox IRSProfile.Field D 131071 L s (b i).1)
local instance:GCDMonoid GlobalPoly :=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
private theorem gcd_mul_right_plain_associated
   (P H q:GlobalPoly) (hc:IsRelPrime q P) :
   Associated (gcd P (H * q)) (gcd P H):=by
 apply associated_of_dvd_dvd
 · have hleft:gcd P (H * q) ∣ P:=gcd_dvd_left P (H * q)
   have hright:gcd P (H * q) ∣ H * q:=gcd_dvd_right P (H * q)
   have hcop:IsRelPrime (gcd P (H * q)) q :=
     hc.symm.of_dvd_left hleft
   exact dvd_gcd hleft (hcop.dvd_of_dvd_mul_right hright)
 · exact dvd_gcd (gcd_dvd_left P H)
     ((gcd_dvd_right P H).trans (dvd_mul_right H q))
private theorem gcd_mul_left_plain_associated
   (H q P:GlobalPoly) (hc:IsRelPrime q P) :
   Associated (gcd (H * q) P) (gcd H P):=by
 apply associated_of_dvd_dvd
 · have hleft:gcd (H * q) P ∣ H * q:=gcd_dvd_left (H * q) P
   have hright:gcd (H * q) P ∣ P:=gcd_dvd_right (H * q) P
   have hcop:IsRelPrime (gcd (H * q) P) q :=
     hc.symm.of_dvd_left hright
   exact dvd_gcd (hcop.dvd_of_dvd_mul_right hleft) hright
 · exact dvd_gcd ((gcd_dvd_left H P).trans (dvd_mul_right H q))
     (gcd_dvd_right H P)
@[simp] theorem submoduleReconstructLinear_apply
   {D L s:ℕ}
   (V:Submodule IRSProfile.Field
     (CoefficientIndex D 131071 L s → IRSProfile.Field)) (v:V) :
   submoduleReconstructLinear V v =
     reconstruct IRSProfile.Field D 131071 L s v.1:=rfl
end
end ProximityPrize.SubmissionLower.RCN183
end PackedLegacy_L4

/-! Packed from ProximityPrize.SubmissionLower.Y6. -/
section PackedLegacy_Y6
namespace ProximityPrize.SubmissionLower.RCN086
open scoped Classical BigOperators
open RCN313 RCN136 RCN238 RCN053 RCN054 RCN095 RCN207 RCN234 RCN198
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 35000
variable {K Ω:Type} [Field K] [Field Ω]
def tailSelector (d j:ℕ):K:=if j=d then 1 else 0
theorem selected_term_identity (F:MvPolynomial (Fin 4) K) (d:ℕ):
   agreementNumerator F d (tailSelector d) 0 0 0=
     numerator K F d*(-MvPolynomial.X (0:Fin 4))^d:=by
 classical
 unfold agreementNumerator clearedTaylorNumerator
 rw [Finset.sum_eq_single d]
 · simp [commonNumeratorTerm,tailSelector,affineSeedPolynomial]
 · intro j _ hj
   simp [commonNumeratorTerm,tailSelector,hj]
 · intro hd
   exact (hd (Finset.mem_range.mpr (Nat.lt_succ_self d))).elim
def globalTailCut (φ:Polynomial K →+*Ω)
   (F:MvPolynomial (Fin 4) K) (d:ℕ):MvPolynomial (Fin 3) Ω:=
 surfaceMap φ (agreementNumerator F d (tailSelector d) 0 0 0)
theorem globalTailCut_eq (φ:Polynomial K →+*Ω)
   (F:MvPolynomial (Fin 4) K) (d:ℕ):
   globalTailCut φ F d=
     surfaceMap φ (numerator K F d)*MvPolynomial.C ((-φ Polynomial.X)^d):=by
 simp [globalTailCut,selected_term_identity,map_mul,map_pow,map_neg]
theorem tail_scalar_ne_zero (φ:Polynomial K →+*Ω)
   (hφ:Function.Injective φ) (d:ℕ):(-φ Polynomial.X)^d≠0:=by
 apply pow_ne_zero
 apply neg_ne_zero.mpr
 intro h
 have hX:(Polynomial.X:Polynomial K)=0:=hφ (by simpa using h)
 exact Polynomial.X_ne_zero hX
theorem globalTailCut_dvd_iff (φ:Polynomial K →+*Ω)
   (hφ:Function.Injective φ) (F:MvPolynomial (Fin 4) K) (d:ℕ)
   (G:MvPolynomial (Fin 3) Ω):
   G∣globalTailCut φ F d ↔ G∣surfaceMap φ (numerator K F d):=by
 rw [globalTailCut_eq]
 let c:Ω:=(-φ Polynomial.X)^d
 have hc:c≠0:=tail_scalar_ne_zero φ hφ d
 constructor
 · intro h
   have hh:=h.mul_right (MvPolynomial.C c⁻¹)
   simpa only [c,mul_assoc, ←map_mul,mul_inv_cancel₀ hc,map_one,mul_one] using hh
 · intro h
   exact h.mul_right _
theorem selected_globalTailCut_zero (φ:Polynomial K →+*Ω)
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (γ:K) (w:ℕ) (hdegree:(selected γ).natDegree ≤ w)
   (hsolution:RCN319.specialization K (selected γ) γ F=0):
   MvPolynomial.aeval (selectedPoint φ selected γ) (globalTailCut φ F (w+1))=0:=by
 rw [globalTailCut_eq,map_mul]
 have hzero:=RCN068.selected_firstTail_zero φ F selected γ w hdegree hsolution
 change MvPolynomial.aeval _ (surfaceMap φ (numerator K F (w+1)))=0 at hzero
 rw [hzero,zero_mul]
theorem exists_filtered_certificate (φ:Polynomial K →+*Ω)
   (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
   (hR:F.degreeOf 2 ≤ s+2)
   (hYR:wt ![0,1,1,0] F ≤ b+s+3)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s+3)
   (d:ℕ) (hd:2 ≤ d) (coeffs:ℕ → K) (x u0 u1:K):
   ∃ (B:Fin (d-1+1) → MvPolynomial (Fin 3) Ω)
     (c:Fin (d-1+1) → FlagDegree),
     surfaceMap φ (agreementNumerator F d coeffs x u0 u1)=
       filteredCut (d-1) B (surfaceMap φ (polyH K F)) (surfaceMap φ (polyG K F))∧
     (∀ j,PolynomialInFlag (c j) (B j))∧
     (∀ j,c j+(d-1-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
       j.val • (⟨a,b,s+3⟩:FlagDegree)=center a b s+(d-1) • direction a b s):=by
 classical
 let B0:=fun j => surfaceMap φ (agreementCoefficients F d coeffs x u0 u1 j)
 refine ⟨(fun j => B0 j.val),(fun j => coefficientFlag a (b+1) (s+2) d j.val),?_,?_,?_⟩
 · rw [surfaceMap_agreementNumerator_eq_coefficient_sum φ F d hd]
   have hk:d-1+1=d:=by omega
   calc
     _=∑ j:Fin (d-1+1),surfaceMap φ (polyH K F)^(d-1-j.val)*
         surfaceMap φ (polyG K F)^j.val*B0 j.val:=by
       let f:=fun j:ℕ => surfaceMap φ (polyH K F)^(d-1-j)*
         surfaceMap φ (polyG K F)^j*B0 j
       change (∑ j∈Finset.range d,f j)=∑ j:Fin (d-1+1),f j.val
       rw [Finset.sum_range]
       let E:Fin d ≃ Fin (d-1+1):={
         toFun:=fun j => ⟨j.val,by have:=j.isLt;omega⟩
         invFun:=fun j => ⟨j.val,by have:=j.isLt;omega⟩
         left_inv:=fun j => rfl
         right_inv:=fun j => rfl}
       exact Fintype.sum_equiv E _ _ (fun _ => rfl)
     _=_:=by
       unfold filteredCut
       apply Finset.sum_congr rfl
       intro j _
       ring
 · intro j
   apply surfaceMap_agreementCoefficients_in_flag φ F a (b+1) (s+2)
     (by omega) (by omega) hR (by omega) (by omega) d hd coeffs x u0 u1 j.val
   have:=j.isLt
   omega
 · intro j
   have hj:j.val<d:=by have:=j.isLt;omega
   have h:=coefficientFlag_add_baseMonomial a (b+1) (s+2) d j.val
     (by omega) (by omega) hj
   rw [(shifted_flags a b s).1,(shifted_flags a b s).2.1,
     (shifted_flags a b s).2.2] at h
   refine h.trans ?_
   have hk:d-1+1=d:=by omega
   simpa only [hk] using class_total a b s (d-1)
theorem globalTailCut_certificate (φ:Polynomial K →+*Ω)
   (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
   (hR:F.degreeOf 2 ≤ s+2)
   (hYR:wt ![0,1,1,0] F ≤ b+s+3)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s+3)
   (w:ℕ) (hw:1 ≤ w):
   ∃ (B:Fin (w+1) → MvPolynomial (Fin 3) Ω)
     (c:Fin (w+1) → FlagDegree),
     globalTailCut φ F (w+1)=
       filteredCut w B (surfaceMap φ (polyH K F)) (surfaceMap φ (polyG K F))∧
     (∀ j,PolynomialInFlag (c j) (B j))∧
     (∀ j,c j+(w-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
       j.val • (⟨a,b,s+3⟩:FlagDegree)=center a b s+w • direction a b s):=by
 have h:=exists_filtered_certificate φ a b s F hR hYR hAll (w+1) (by omega)
   (tailSelector (w+1)) 0 0 0
 rw [show w+1-1=w by omega] at h
 exact h
end
end ProximityPrize.SubmissionLower.RCN086
end PackedLegacy_Y6

/-! Packed from ProximityPrize.SubmissionLower.FD. -/
section PackedLegacy_FD
namespace ProximityPrize.SubmissionLower.RCN212
open scoped Classical BigOperators WithZero
open RCN133 RCN184 RCN295 RCN095 RCN187
noncomputable section
set_option maxHeartbeats 1000000
def liftExponent (d:Fin 3 →₀ ℕ):Fin 4 →₀ ℕ:=
 Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+Finsupp.single 2 (d 2)
def shiftExponent (d:Fin 3 →₀ ℕ):Fin 4 →₀ ℕ:=
 liftExponent d+Finsupp.single 3 1
abbrev quadraticSupport:=flagSupport (2 • unitAllFlag)
abbrev linearSupport:=flagSupport unitYZFlag
def movingSupport:Finset (Fin 4 →₀ ℕ):=
 quadraticSupport.image liftExponent ∪ linearSupport.image shiftExponent
theorem liftExponent_injective:Function.Injective liftExponent:=by
 intro d e h
 ext i
 have hh:=DFunLike.congr_fun h i.castSucc
 fin_cases i <;> simpa [liftExponent] using hh
theorem shiftExponent_injective:Function.Injective shiftExponent:=by
 intro d e h
 exact liftExponent_injective (add_right_cancel h)
theorem mem_movingSupport (d:Fin 4 →₀ ℕ):
   d∈movingSupport ↔ d 0+d 1+d 2+d 3 ≤ 2∧d 3 ≤ 1∧d 1+2*d 3 ≤ 2:=by
 classical
 constructor
 · intro hd
   rcases Finset.mem_union.mp hd with hd | hd
   · obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp hd
     have he:=(mem_flagSupport_iff _ _).mp he
     simp only [InFlag,nsmul_zOnly,nsmul_yz,nsmul_all,unitAllFlag] at he
     simp [liftExponent]
     omega
   · obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp hd
     have he:=(mem_flagSupport_iff _ _).mp he
     simp only [InFlag,unitYZFlag] at he
     simp [shiftExponent,liftExponent]
     omega
 · rintro ⟨ht,hw,hr⟩
   let e:=exponentOfTriple (d 0,d 1,d 2)
   have heq0:e 0=d 0∧e 1=d 1∧e 2=d 2:=by simp [e,exponentOfTriple]
   have hdw:d 3=0∨d 3=1:=by omega
   rcases hdw with hdw | hdw
   · apply Finset.mem_union_left
     refine Finset.mem_image.mpr ⟨e,?_,?_⟩
     · rw [mem_flagSupport_iff]
       simp [InFlag,unitAllFlag,heq0.1,heq0.2.1,heq0.2.2]
       omega
     · ext i;fin_cases i <;> simp [liftExponent,heq0.1,heq0.2.1,heq0.2.2,hdw]
   · apply Finset.mem_union_right
     refine Finset.mem_image.mpr ⟨e,?_,?_⟩
     · rw [mem_flagSupport_iff]
       simp [InFlag,unitYZFlag,heq0.1,heq0.2.1,heq0.2.2]
       omega
     · ext i;fin_cases i <;> simp [shiftExponent,liftExponent,heq0.1,heq0.2.1,heq0.2.2,hdw]
theorem movingSupport_downwardClosed:ExponentSetDownwardClosed movingSupport:=by
 intro d hd e he
 rw [mem_movingSupport] at hd ⊢
 have h0:=he 0;have h1:=he 1;have h2:=he 2;have h3:=he 3
 omega
theorem zero_mem_movingSupport:(0:Fin 4 →₀ ℕ)∈movingSupport:=by
 simp [mem_movingSupport]
def quadraticIndex (d:quadraticSupport):movingSupport:=
 ⟨liftExponent d.1,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d.1,d.2,rfl⟩)⟩
def linearIndex (d:linearSupport):movingSupport:=
 ⟨shiftExponent d.1,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d.1,d.2,rfl⟩)⟩
theorem quadraticIndex_injective:Function.Injective quadraticIndex:=
 fun _ _ h↦Subtype.ext (liftExponent_injective (congrArg Subtype.val h))
theorem linearIndex_injective:Function.Injective linearIndex:=
 fun _ _ h↦Subtype.ext (shiftExponent_injective (congrArg Subtype.val h))
def supportIndex:quadraticSupport ⊕ linearSupport → movingSupport:=
 Sum.elim quadraticIndex linearIndex
theorem supportIndex_bijective:Function.Bijective supportIndex:=by
 constructor
 · intro d e h
   cases d with
   | inl d =>
     cases e with
     | inl e => exact congrArg Sum.inl (quadraticIndex_injective h)
     | inr e => have hh:=DFunLike.congr_fun (congrArg Subtype.val h) 3
                simp [supportIndex,quadraticIndex,linearIndex,liftExponent,shiftExponent] at hh
   | inr d =>
     cases e with
     | inl e => have hh:=DFunLike.congr_fun (congrArg Subtype.val h) 3
                simp [supportIndex,quadraticIndex,linearIndex,liftExponent,shiftExponent] at hh
     | inr e => exact congrArg Sum.inr (linearIndex_injective h)
 · intro d
   rcases Finset.mem_union.mp d.2 with hd | hd
   · obtain ⟨e,he,h⟩:=Finset.mem_image.mp hd
     exact ⟨Sum.inl ⟨e,he⟩,Subtype.ext h⟩
   · obtain ⟨e,he,h⟩:=Finset.mem_image.mp hd
     exact ⟨Sum.inr ⟨e,he⟩,Subtype.ext h⟩
variable {K L:Type*} [Field K] [Field L] [Algebra K L]
def restrictQ:(movingSupport → K) →ₗ[K] (quadraticSupport → K):=
 LinearMap.funLeft K K quadraticIndex
def restrictU:(movingSupport → K) →ₗ[K] (linearSupport → K):=
 LinearMap.funLeft K K linearIndex
theorem restrictU_surjective:Function.Surjective (restrictU (K:=K)):=
 LinearMap.funLeft_surjective_of_injective K K _ linearIndex_injective
def quadraticPolynomial (c:movingSupport → K):=polynomialOfSupport quadraticSupport (restrictQ c)
def linearPolynomial (c:movingSupport → K):=polynomialOfSupport linearSupport (restrictU c)
theorem quadraticPolynomial_inFlag (c:movingSupport → K):
   PolynomialInFlag (2 • unitAllFlag) (quadraticPolynomial c):=
 (support_subset_flagSupport_iff _ _).mp (support_polynomialOfSupport_subset _ _)
theorem linearPolynomial_inFlag (c:movingSupport → K):
   PolynomialInFlag unitYZFlag (linearPolynomial c):=
 (support_subset_flagSupport_iff _ _).mp (support_polynomialOfSupport_subset _ _)
def movingCoordinates (x:Fin 3 → L) (w:L):Fin 4 → L:=![x 0,x 1,x 2,w]
theorem evaluation_lift (x:Fin 3 → L) (w:L) (d:Fin 3 →₀ ℕ) (a:K):
   MvPolynomial.eval₂Hom (algebraMap K L) (movingCoordinates x w)
     (MvPolynomial.monomial (liftExponent d) a)=
   MvPolynomial.eval₂Hom (algebraMap K L) x (MvPolynomial.monomial d a):=by
 simp [MvPolynomial.eval₂Hom_monomial,Finsupp.prod_fintype,Fin.prod_univ_four,
   Fin.prod_univ_three,liftExponent,movingCoordinates]
theorem evaluation_shift (x:Fin 3 → L) (w:L) (d:Fin 3 →₀ ℕ) (a:K):
   MvPolynomial.eval₂Hom (algebraMap K L) (movingCoordinates x w)
     (MvPolynomial.monomial (shiftExponent d) a)=
   MvPolynomial.eval₂Hom (algebraMap K L) x (MvPolynomial.monomial d a)*w:=by
 simp [MvPolynomial.eval₂Hom_monomial,Finsupp.prod_fintype,Fin.prod_univ_four,
   Fin.prod_univ_three,shiftExponent,liftExponent,movingCoordinates,mul_assoc]
theorem coefficientEvaluation_eq (x:Fin 3 → L) (w:L) (c:movingSupport → K):
   coefficientEvaluation (movingCoordinates x w) movingSupport c=
     MvPolynomial.eval₂Hom (algebraMap K L) x (quadraticPolynomial c)+
     MvPolynomial.eval₂Hom (algebraMap K L) x (linearPolynomial c)*w:=by
 let e:=Equiv.ofBijective supportIndex supportIndex_bijective
 change MvPolynomial.eval₂Hom _ _ (polynomialOfSupport _ _)=_
 simp only [polynomialOfSupport,map_sum]
 rw [←e.sum_comp]
 simp only [Fintype.sum_sum_type,e,Equiv.ofBijective_apply,supportIndex,Sum.elim_inl,
   Sum.elim_inr,quadraticIndex,linearIndex]
 simp only [evaluation_lift,evaluation_shift]
 simp [quadraticPolynomial,linearPolynomial,polynomialOfSupport,map_sum,
   Finset.sum_mul,restrictQ,restrictU,LinearMap.funLeft,quadraticIndex,linearIndex]
theorem coordinate_mem (i:Fin 3):Finsupp.single i.castSucc 1∈movingSupport:=by
 fin_cases i <;> simp [mem_movingSupport]
theorem exists_coordinate_evaluation (x:Fin 3 → L) (w:L) (i:Fin 3):
   ∃ c:movingSupport → K,
     coefficientEvaluation (movingCoordinates x w) movingSupport c=x i:=by
 refine ⟨deltaCoefficient movingSupport ⟨Finsupp.single i.castSucc 1,coordinate_mem i⟩,?_⟩
 change MvPolynomial.eval₂Hom _ _ (polynomialOfSupport _ _)=_
 rw [polynomialOfSupport_deltaCoefficient]
 fin_cases i <;> simp [MvPolynomial.eval₂Hom_monomial,movingCoordinates]
theorem exponentSetPoleWeight_moving (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (w:L):
   exponentSetPoleWeight v (movingCoordinates x w) movingSupport=
     max (2*max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2))))
       (max (poleOrder v (x 0)) (poleOrder v (x 2))+poleOrder v w):=by
 let q:Fin 4 → ℤ:=fun i↦poleOrder v (movingCoordinates x w i)
 let a:=max (q 1) (max (q 0) (q 2))
 let b:=max (q 0) (q 2)
 have hq:∀ i,0 ≤ q i:=fun i↦le_max_left _ _
 have ha0:q 0 ≤ a:=(le_max_left _ _).trans (le_max_right _ _)
 have ha1:q 1 ≤ a:=le_max_left _ _
 have ha2:q 2 ≤ a:=(le_max_right _ _).trans (le_max_right _ _)
 have hb0:q 0 ≤ b:=le_max_left _ _
 have hb2:q 2 ≤ b:=le_max_right _ _
 have ha:0 ≤ a:=(hq 1).trans ha1
 change exponentSetPoleWeight v (movingCoordinates x w) movingSupport=max (2*a) (b+q 3)
 have hweight (d:Fin 4 →₀ ℕ):exponentPoleWeight v (movingCoordinates x w) d=
     (d 0:ℤ)*q 0+(d 1:ℤ)*q 1+(d 2:ℤ)*q 2+(d 3:ℤ)*q 3:=by
   simp [exponentPoleWeight,Fin.sum_univ_four,q]
 apply le_antisymm
 · unfold exponentSetPoleWeight
   apply Finset.max'_le
   intro z hz
   rcases Finset.mem_insert.mp hz with rfl | hz
   · exact (by omega:0 ≤ 2*a).trans (le_max_left _ _)
   obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp hz
   rcases (mem_movingSupport d).mp hd with ⟨ht,hw,hr⟩
   rw [hweight]
   have hdw:d 3=0∨d 3=1:=by omega
   rcases hdw with hdw | hdw
   · have ht':(d 0:ℤ)+d 1+d 2 ≤ 2:=by exact_mod_cast (by omega:d 0+d 1+d 2 ≤ 2)
     have h0:=mul_le_mul_of_nonneg_left ha0 (Int.natCast_nonneg (d 0))
     have h1:=mul_le_mul_of_nonneg_left ha1 (Int.natCast_nonneg (d 1))
     have h2:=mul_le_mul_of_nonneg_left ha2 (Int.natCast_nonneg (d 2))
     simp only [hdw,Nat.cast_zero,zero_mul,add_zero]
     apply le_trans _ (le_max_left _ _)
     nlinarith
   · have hd1:d 1=0:=by omega
     have ht':(d 0:ℤ)+d 2 ≤ 1:=by exact_mod_cast (by omega:d 0+d 2 ≤ 1)
     have hb:0 ≤ b:=(hq 0).trans hb0
     have h0:=mul_le_mul_of_nonneg_left hb0 (Int.natCast_nonneg (d 0))
     have h2:=mul_le_mul_of_nonneg_left hb2 (Int.natCast_nonneg (d 2))
     simp only [hdw,hd1,Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,add_zero]
     apply le_trans _ (le_max_right _ _)
     nlinarith
 · have hmem (d:Fin 4 →₀ ℕ) (hd:d∈movingSupport):
       exponentPoleWeight v (movingCoordinates x w) d ≤
         exponentSetPoleWeight v (movingCoordinates x w) movingSupport:=by
     apply Finset.le_max'
     exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨d,hd,rfl⟩)
   have hs (i:Fin 3):2*q i.castSucc ≤ exponentSetPoleWeight v (movingCoordinates x w) movingSupport:=by
     have hm:Finsupp.single i.castSucc 2∈movingSupport:=by fin_cases i <;> simp [mem_movingSupport]
     have hh:=hmem _ hm
     fin_cases i <;> simpa [hweight] using hh
   have hw (i:Fin 3) (hi:i=0∨i=2):q i.castSucc+q 3 ≤
       exponentSetPoleWeight v (movingCoordinates x w) movingSupport:=by
     have hm:Finsupp.single i.castSucc 1+Finsupp.single 3 1∈movingSupport:=by
       rcases hi with rfl | rfl <;> simp [mem_movingSupport]
     have hh:=hmem _ hm
     rcases hi with rfl | rfl <;> simpa [hweight] using hh
   have hs0:=hs 0;have hs1:=hs 1;have hs2:=hs 2
   have hw0:=hw 0 (Or.inl rfl);have hw2:=hw 2 (Or.inr rfl)
   dsimp [a,b] at*
   omega
end
end ProximityPrize.SubmissionLower.RCN212
end PackedLegacy_FD

/-! Packed from ProximityPrize.SubmissionLower.EJ. -/
section PackedLegacy_EJ
namespace ProximityPrize.SubmissionLower.RCN134
open scoped BigOperators
open RCN002
noncomputable section
variable {K L:Type} [Field K] [Field L] [Algebra K L]
def embeddingPoint (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (f:CoordinateField K P →ₐ[K] L):Fin 3 → L:=
 fun i => f (coordinate K P i)
theorem embeddingPoint_aeval (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (f:CoordinateField K P →ₐ[K] L):
   MvPolynomial.aeval (embeddingPoint P f)=
     f.comp (coordinateEvaluation K P):=by
 apply MvPolynomial.algHom_ext
 intro i
 simp only [MvPolynomial.aeval_X,AlgHom.comp_apply,embeddingPoint,coordinate]
theorem embeddingPoint_kernel (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (f:CoordinateField K P →ₐ[K] L):
   RingHom.ker (MvPolynomial.aeval (embeddingPoint P f)).toRingHom=P:=by
 rw [embeddingPoint_aeval]
 change RingHom.ker (f.toRingHom.comp
   (coordinateEvaluation K P).toRingHom)=P
 rw [RingHom.ker_comp_of_injective _ f.injective,coordinateEvaluation_ker]
theorem embeddingPoint_injective (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]:
   Function.Injective (embeddingPoint (L:=L) P):=by
 intro f g hfg
 have he:f.comp (coordinateEvaluation K P)=
     g.comp (coordinateEvaluation K P):=by
   rw [←embeddingPoint_aeval, ←embeddingPoint_aeval,hfg]
 apply IsLocalization.algHom_ext (nonZeroDivisors (CoordinateRing K P))
 apply AlgHom.ext
 intro a
 obtain ⟨A,rfl⟩:=Ideal.Quotient.mk_surjective a
 exact AlgHom.congr_fun he A
variable {I:Type} (P:I → Ideal (MvPolynomial (Fin 3) K))
 [∀ i,(P i).IsPrime]
def familyEmbeddingPoint
   (z:Σ i,CoordinateField K (P i) →ₐ[K] L):Fin 3 → L:=
 embeddingPoint (P z.1) z.2
section CommonBase
variable {B:Type} [Field B] [Algebra K B] [Algebra B L]
 [IsScalarTower K B L]
 [∀ i,Algebra B (CoordinateField K (P i))]
 [∀ i,IsScalarTower K B (CoordinateField K (P i))]
def commonBaseEmbeddingPoint
   (z:Σ i,CoordinateField K (P i) →ₐ[B] L):Fin 3 → L:=
 embeddingPoint (P z.1) (z.2.restrictScalars K)
theorem commonBaseEmbeddingPoint_injective (hP:Function.Injective P):
   Function.Injective (commonBaseEmbeddingPoint (B:=B) (L:=L) P):=by
 rintro ⟨i,f⟩ ⟨j,g⟩ hfg
 have hij:P i=P j:=by
   rw [←embeddingPoint_kernel (P i) (f.restrictScalars K),
     ←embeddingPoint_kernel (P j) (g.restrictScalars K)]
   exact congrArg (fun v:Fin 3 → L =>
     RingHom.ker (MvPolynomial.aeval v).toRingHom) hfg
 obtain rfl:=hP hij
 have hr:f.restrictScalars K=g.restrictScalars K:=
   embeddingPoint_injective (P i) hfg
 have hf:f=g:=by
   apply AlgHom.ext
   intro a
   exact AlgHom.congr_fun hr a
 cases hf
 rfl
variable [Fintype I] [IsAlgClosed L]
 [∀ i,FiniteDimensional B (CoordinateField K (P i))]
 [∀ i,Algebra.IsSeparable B (CoordinateField K (P i))]
end CommonBase
end
end ProximityPrize.SubmissionLower.RCN134
end PackedLegacy_EJ
end Compact_PackedLegacyCore2
