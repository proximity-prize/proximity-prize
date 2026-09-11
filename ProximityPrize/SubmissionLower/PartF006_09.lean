import ProximityPrize.SubmissionLower.PartF006_08
section Compact_PackedLegacy
section PackedLegacy_EQ
namespace ProximityPrize.SubmissionLower.RCN146
open scoped Classical BigOperators
open RCN135 RCN136 RCN231 RCN319 RCN313 RCN174 RCN238 RCN065 RCN243 RCN264 RCN159 RCN095 RCN275 RCN198 RCN203 RCN287 RCN049 RCN144 RCN063 RCN145 RCN087 RCN046 RCN265 RCN295 RCN344 RCN002
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 45000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

abbrev Ω (K:Type) [Field K]:=GenericField K
def identityCurveDegree (flag:FlagDegree) (a b s w:ℕ):ℕ:=
 flagMixed flag (paddedCut a b s (w+1)) unitZFlag+
   flagMixed flag (paddedCut a b s (w+1)) unitYZFlag
theorem mixed_padded_le_succ (flag:FlagDegree) (a b s d:ℕ) (r:FlagDegree):
   flagMixed flag (paddedCut a b s d) r ≤
     flagMixed flag (paddedCut a b s (d+1)) r:=by
 have he:paddedCut a b s (d+1)=paddedCut a b s d+
     RCN206.directionFlag a b s:=by
   change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
   congr 1 <;> simp only [paddedCut,
     RCN206.centreFlag,
     RCN206.directionFlag,
     add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all] <;> ring
 rw [he,mixed_add_second]
 exact Nat.le_add_right _ _
variable {Γ:Finset K} {x:I → K} {p e a b s:ℕ} [CharP (Ω K) p]
 {flag:FlagDegree} {w:ℕ}
theorem actual_identityCurveCountProvider
   (S:ResidualStage (polynomialEmbedding K) Γ x p e flag w (support a b s))
   (agreements:ℕ) (hnodes:S.nodes.card=agreements+e)
   (hagreement:∀ γ∈Γ,agreements≤(S.agreementFiber γ).card)
   (hwa:w<agreements)
   (hTail:S.G∣surfaceMap (polynomialEmbedding K) (numerator K S.F (w+1)))
   (bound seedCap slopeCap:ℕ) (hw:1≤w)
   (hshort:w+1≤bound) (hchar:bound<p)
   (hbox:S.F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:(1+w*(2*(b+s+3)-2))*flag.all+
     (flag.yz+flag.all)*((2*(s+2)-1)*w)<p):
   IdentityCurveCountProvider S (identityCurveDegree flag a b s w):=by
 classical
 unfold IdentityCurveCountProvider
 intro i hi
 dsimp only
 intro hproper
 let T:=agreementPolynomial (polynomialEmbedding K) S.F w
   (x i) (S.u0 i) (S.u1 i)
 let Gi:=Γ.filter (fun γ => S.Agrees γ i)
 obtain ⟨base,⟨U⟩⟩:=exists_agreement_projection_of_caps S
   (x i) (S.u0 i) (S.u1 i) hproper hflagChar hmixed
 let cost:RegularComponent (Ω K) S.G T (regularitySurface (polynomialEmbedding K) S.F)→ℕ:=
   fun C => U.family.toPrimeFlagBudgetFamily.zCost C+
     U.family.toPrimeFlagBudgetFamily.yzCost C
 refine ⟨cost,?_,?_⟩
 · intro C
   let Gc:=componentSeeds (Ω K) S.G T
     (regularitySurface (polynomialEmbedding K) S.F) Gi
     (selectedPoint (polynomialEmbedding K) S.selected) C
   have hGcGi:Gc⊆Gi:=componentSeeds_subset (Ω K) S.G T _ Gi _ C
   have hGiΓ:Gi⊆Γ:=Finset.filter_subset _ _
   have hGcΓ:Gc⊆Γ:=hGcGi.trans hGiΓ
   have hyzC:∀ W:Finset (RCN346.Place (Ω K)
       (CoordinateField (Ω K) C.1)),
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate (Ω K) C.1)
         (flagSupport unitYZFlag))≤
         (U.family.toPrimeFlagBudgetFamily.yzCost C:ℤ):=by
     intro W
     change (∑ v∈W,exponentSetPoleWeight v.val (coordinate (Ω K) C.1)
       (flagSupport unitYZFlag))≤
       (coordinateDegree (Ω K) (CoordinateField (Ω K) C.1)
         (U.family.yzProjection C):ℤ)
     calc
       _=∑ v∈W,RCN346.poleOrder (Ω K)
           (CoordinateField (Ω K) C.1) v
           (coordinateValue (Ω K) (CoordinateField (Ω K) C.1)
             (U.family.yzProjection C)):=by
         apply Finset.sum_congr rfl
         intro v _
         exact U.family.yzPole_eq C v
       _ ≤ _:=finite_sum_coordinate_pole_le_degree (Ω K)
         (CoordinateField (Ω K) C.1) (U.family.yzProjection C) W
   have hprofileYZ:=coefficientPoleProfile_of_regular_agreement_curve
     S hTail (x i) (S.u0 i) (S.u1 i) hproper C
     bound seedCap slopeCap (U.family.toPrimeFlagBudgetFamily.yzCost C)
     hw hshort hchar hbox hyzC
   have hprofile:CoefficientPoleProfile (polynomialEmbedding K) C.1 S.F
       (stage_surface_mem S (x i) (S.u0 i) (S.u1 i) C)
       (stage_regularity_not_mem S (x i) (S.u0 i) (S.u1 i) C) w (cost C):=by
     intro W
     exact (hprofileYZ W).trans (by
       change (U.family.toPrimeFlagBudgetFamily.yzCost C:ℤ) ≤
         ((U.family.toPrimeFlagBudgetFamily.zCost C+
           U.family.toPrimeFlagBudgetFamily.yzCost C:ℕ):ℤ)
       norm_cast
       omega)
   have hcost:1≤cost C:=
     U.one_le_zCost_add_yzCost (polynomialEmbedding K) S.F rfl S.G_dvd_surface C
   apply prime_curve_card_le_of_coefficientPoleProfile
     (polynomialEmbedding K) C.1 S.F
     (stage_surface_mem S (x i) (S.u0 i) (S.u1 i) C)
     (stage_regularity_not_mem S (x i) (S.u0 i) (S.u1 i) C)
     (base C) p w agreements e (cost C) S.characteristic_bound hwa hcost hprofile
     S.selected Gc S.nodes x S.u0 S.u1 S.x_injective hnodes
   · intro γ hγ
     exact S.degree_le γ (hGcΓ hγ)
   · intro γ hγ
     exact S.solution γ (hGcΓ hγ)
   · intro γ hγ
     exact S.regular γ (hGcΓ hγ)
   · intro γ hγ
     exact componentSeeds_on_prime (Ω K) S.G T
       (regularitySurface (polynomialEmbedding K) S.F) Gi
       (selectedPoint (polynomialEmbedding K) S.selected) C γ hγ
   · intro γ hγ
     have hΓ:=hGcΓ hγ
     simpa only [ResidualStage.agreementFiber,ResidualStage.Agrees] using
       hagreement γ hΓ
   · exact noLargeSelectedPencil_mono S.selected Γ Gc w e hGcΓ S.no_large_pencil
 · have hz:=U.family.sum_zDegree_le
   have hyz:=U.family.sum_yzDegree_le
   change (∑ C,U.family.toPrimeFlagBudgetFamily.zCost C)≤
     flagMixed flag (sharpResidualAgreementFlag (support a b s) w) unitZFlag at hz
   change (∑ C,U.family.toPrimeFlagBudgetFamily.yzCost C)≤
     flagMixed flag (sharpResidualAgreementFlag (support a b s) w) unitYZFlag at hyz
   have hz':=hz.trans (mixed_sharp_le_padded a b s w flag unitZFlag)
   have hyz':=hyz.trans (mixed_sharp_le_padded a b s w flag unitYZFlag)
   have hz'':=hz'.trans (mixed_padded_le_succ flag a b s w unitZFlag)
   have hyz'':=hyz'.trans (mixed_padded_le_succ flag a b s w unitYZFlag)
   change (∑ C,(U.family.toPrimeFlagBudgetFamily.zCost C+
     U.family.toPrimeFlagBudgetFamily.yzCost C)) ≤ identityCurveDegree flag a b s w
   rw [Finset.sum_add_distrib]
   exact Nat.add_le_add hz'' hyz''
end
end ProximityPrize.SubmissionLower.RCN146
end PackedLegacy_EQ

/-! Packed from ProximityPrize.SubmissionLower.O0. -/
section PackedLegacy_O0
namespace ProximityPrize.SubmissionLower.RCN268
open scoped Classical
open RCN223 RCN286 RCN174 RCN319 RCN135 RCN238 RCN243 RCN081 RCN222 RCN221 RCN266 RCN140 RCN159 RCN095 RCN275 RCN214
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)
def regularGeometricResidualStageOfSupport
   (support:ResidualSupportParameters)
   {pchar errorCap degree:ℕ} [CharP K pchar]
   (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ degree)
   (hnoPencil:NoLargeSelectedPencil selected Gamma degree errorCap)
   (R:RCN266.RegularIndex Q)
   (hRirred:Irreducible R.1)
   (hRpos:0 < R.1.degreeOf (2:Fin 4))
   (hRsmall:R.1.degreeOf (2:Fin 4) < pchar)
   (hRsupport:ResidualSupportData support R.1)
   (hdegreeChar:degree < pchar)
   (g:GeometricFactor K R.1):
   letI:CharP (GenericField K) pchar:=genericField_charP K pchar
   ResidualStage (polynomialEmbedding K)
     (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g)
     x pchar errorCap (geometricFlag K g) degree support:=by
 have hsub:=regularSeeds_subset Q selected Gamma R
 exact geometricResidualStageOfSupport K support R.1 hRirred hRpos
   hRsmall hRsupport selected
   (regularSeeds Q selected Gamma R) nodes x u0 u1 hinj
   (fun gamma hgamma↦hdegree gamma (hsub hgamma))
   (fun gamma hgamma↦(Finset.mem_filter.mp hgamma).2.1)
   (fun gamma hgamma↦(Finset.mem_filter.mp hgamma).2.2)
   (noLargeSelectedPencil_mono selected Gamma _ degree errorCap hsub hnoPencil)
   hdegreeChar g
def regularGeometricResidualStage
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime]
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w errors)
   (R:RCN266.RegularIndex Q)
   (g:GeometricFactor K R.1):
   letI:CharP (GenericField K) prime:=genericField_charP K prime
   ResidualStage (polynomialEmbedding K)
     (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g)
     x prime errors (geometricFlag K g) w:=by
 have hRdata:=
   directFactor_data Q R.1 hQ weightedCap w seedTotalCap slopeCap hbox R.2
 have hRsmall:R.1.degreeOf (2:Fin 4) < prime:=
   (degreeOf_R_le_of_mem_box R.1 weightedCap w seedTotalCap slopeCap
     hRdata.2.2).trans_lt (by norm_num [slopeCap,prime])
 have hsupport:=residual_surface_weights_of_box K R.1 hRdata.2.2
 exact regularGeometricResidualStageOfSupport
   ResidualSupportParameters.acceptedSupport Q selected Gamma nodes x u0 u1
   hinj hdegree hnoPencil R hRdata.1 hRdata.2.1 hRsmall
   ⟨hsupport.1,hsupport.2.1,hsupport.2.2⟩
   (by norm_num [w,prime]) g
end
end ProximityPrize.SubmissionLower.RCN268
end PackedLegacy_O0

/-! Packed from ProximityPrize.SubmissionLower.FQ. -/

/-! Packed from ProximityPrize.SubmissionLower.AB. -/
section PackedLegacy_AB
namespace ProximityPrize.SubmissionLower.RCN259
noncomputable section
section Quotients
variable {A:Type*} [CommMonoidWithZero A] [GCDMonoid A]
def leftGCDQuotient (a b:A):A:=Classical.choose (gcd_dvd_left a b)
def rightGCDQuotient (a b:A):A:=Classical.choose (gcd_dvd_right a b)
theorem left_eq_gcd_mul_leftGCDQuotient (a b:A):
   a=gcd a b*leftGCDQuotient a b:=
 Classical.choose_spec (gcd_dvd_left a b)
theorem right_eq_gcd_mul_rightGCDQuotient (a b:A):
   b=gcd a b*rightGCDQuotient a b:=
 Classical.choose_spec (gcd_dvd_right a b)
theorem gcdQuotients_isRelPrime {a b:A} (ha:a≠0):
   IsRelPrime (leftGCDQuotient a b) (rightGCDQuotient a b):=by
 intro d hdleft hdright
 have hg:gcd a b≠0:=gcd_ne_zero_of_left ha
 have hda:gcd a b*d∣a:=by
   calc
     gcd a b*d∣gcd a b*leftGCDQuotient a b:=
       mul_dvd_mul_left (gcd a b) hdleft
     _=a:=(left_eq_gcd_mul_leftGCDQuotient a b).symm
 have hdb:gcd a b*d∣b:=by
   calc
     gcd a b*d∣gcd a b*rightGCDQuotient a b:=
       mul_dvd_mul_left (gcd a b) hdright
     _=b:=(right_eq_gcd_mul_rightGCDQuotient a b).symm
 have hdg:gcd a b*d∣gcd a b:=dvd_gcd hda hdb
 apply isUnit_iff_dvd_one.mpr
 apply (mul_dvd_mul_iff_left hg).mp
 simpa only [mul_one] using hdg
end Quotients
section RecursiveDefinitions
variable {A:Type*} [CommMonoidWithZero A] [GCDMonoid A]
def gcd12 (a b:A):A:=gcd a b
def gcd123 (a b c:A):A:=gcd (gcd12 a b) c
def quotientA (a b:A):A:=leftGCDQuotient a b
def quotientB (a b:A):A:=rightGCDQuotient a b
def middleQuotient (a b c:A):A:=leftGCDQuotient (gcd12 a b) c
def quotientC (a b c:A):A:=rightGCDQuotient (gcd12 a b) c
theorem a_eq_gcd12_mul_quotientA (a b:A):
   a=gcd12 a b*quotientA a b:=
 left_eq_gcd_mul_leftGCDQuotient a b
theorem b_eq_gcd12_mul_quotientB (a b:A):
   b=gcd12 a b*quotientB a b:=
 right_eq_gcd_mul_rightGCDQuotient a b
theorem firstQuotients_isRelPrime {a b:A} (ha:a≠0):
   IsRelPrime (quotientA a b) (quotientB a b):=
 gcdQuotients_isRelPrime ha
end RecursiveDefinitions
section Normalization
variable {A:Type*} [CommMonoidWithZero A] [NormalizedGCDMonoid A]
end Normalization
section ThreeBranchCover
variable {A B:Type*} [CommRing A] [GCDMonoid A]
 [CommRing B] [IsDomain B]
end ThreeBranchCover
end
end ProximityPrize.SubmissionLower.RCN259
end PackedLegacy_AB

/-! Packed from ProximityPrize.SubmissionLower.L3. -/
section PackedLegacy_L3
namespace ProximityPrize.SubmissionLower.RCN182
open ProximityPrize.Benchmark RCN174 RCN256 RCN319
noncomputable section
variable (K:Type*) [Field K]
theorem block_equations_of_mem_ker
   {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1)):
   ∀ (i:I) (r:Fin m),
     contactJet K (m-r.val)
       ((extractBlock K D w L s (nodes i) (u0 i) (u1 i) r.val theta):
         Poly K)=0:=by
 intro i r
 have hzero:constraintMap K D w L s m nodes u0 u1 theta=0:=
   LinearMap.mem_ker.mp htheta
 have happ:=congrArg
   (fun target:GlobalTarget K I m L s => ((target i r):Poly K)) hzero
 change contactJet K (m-r.val)
   ((extractBlock K D w L s (nodes i) (u0 i) (u1 i) r.val theta):
     Poly K)=0 at happ
 exact happ
theorem translated_contact_of_mem_ker
   {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1)):
   ∀ (i:I) (r:ℕ),
     slopeDifference K^(m-r)∣
       (homogenizedTranslation K (nodes i) (u0 i) (u1 i)
         (reconstruct K D w L s theta)).coeff r:=by
 intro i r
 rw [translation_reconstruct_coeff]
 exact all_blocks_divisible_of_equations K D w L s m
   (nodes i) (u0 i) (u1 i) theta
   (block_equations_of_mem_ker K D w L s m nodes u0 u1 theta htheta i) r
theorem specialization_eq_zero_of_mem_ker
   [DecidableEq K] {I:Type*} [Fintype I] [DecidableEq I]
   (D w L s m:ℕ) (nodes:I ↪ K) (u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1))
   (P:Polynomial K) (gamma:K) (support:Finset I)
   (hD:0 < D) (hP:P.natDegree ≤ w)
   (hcapacity:D ≤ m*support.card)
   (hvalues:∀ i∈support,
     P.eval (nodes i)=u0 i+gamma*u1 i):
   specialization K P gamma (reconstruct K D w L s theta)=0:=by
 apply specialization_eq_zero_of_contact_and_degree K
   (reconstruct K D w L s theta) P gamma nodes u0 u1 support m
 · intro i hi r
   exact translated_contact_of_mem_ker K D w L s m nodes u0 u1 theta
     htheta i r
 · exact hvalues
 · have hdegree:=specialization_natDegree_lt K D w L s
     (reconstruct K D w L s theta) P gamma hD
     (reconstruct_mem_globalCoefficientBox K D w L s theta) hP
   exact hdegree.trans_le hcapacity
theorem specialization_eq_zero_of_agreements
   [DecidableEq K] {I:Type*} [Fintype I] [DecidableEq I]
   (D w L s m a:ℕ) (nodes:I ↪ K) (u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1))
   (hD:0 < D) (hDa:D=m*a)
   (P:Polynomial K) (gamma:K) (support:Finset I)
   (hP:P.natDegree ≤ w) (hcard:a ≤ support.card)
   (hvalues:∀ i∈support,
     P.eval (nodes i)=u0 i+gamma*u1 i):
   specialization K P gamma (reconstruct K D w L s theta)=0:=by
 apply specialization_eq_zero_of_mem_ker K D w L s m nodes u0 u1 theta
   htheta P gamma support hD hP
 · rw [hDa]
   exact Nat.mul_le_mul_left m hcard
 · exact hvalues
theorem nonzero_kernel_member_universal
   [DecidableEq K] {I:Type*} [Fintype I] [DecidableEq I]
   (D w L s m a:ℕ) (nodes:I ↪ K) (u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta0:theta≠0)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1))
   (hD:0 < D) (hDa:D=m*a):
   reconstruct K D w L s theta≠0∧
     reconstruct K D w L s theta∈globalCoefficientBox K D w L s∧
     ∀ (gamma:K) (P:Polynomial K) (support:Finset I),
       P.natDegree ≤ w → a ≤ support.card →
       (∀ i∈support,
         P.eval (nodes i)=u0 i+gamma*u1 i) →
       specialization K P gamma (reconstruct K D w L s theta)=0:=by
 refine ⟨reconstruct_ne_zero K D w L s theta htheta0,
   reconstruct_mem_globalCoefficientBox K D w L s theta,?_⟩
 intro gamma P support hP hcard hvalues
 exact specialization_eq_zero_of_agreements K D w L s m a nodes u0 u1
   theta htheta hD hDa P gamma support hP hcard hvalues
end
end ProximityPrize.SubmissionLower.RCN182
end PackedLegacy_L3

/-! Packed from ProximityPrize.SubmissionLower.GF. -/
section PackedLegacy_GF
namespace ProximityPrize.SubmissionLower.RCN300
open ProximityPrize.Benchmark RCN174 RCN256 RCN319 RCN182 RCN301
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
end
end ProximityPrize.SubmissionLower.RCN300
end PackedLegacy_GF

/-! Packed from ProximityPrize.SubmissionLower.GD. -/
section PackedLegacy_GD
namespace ProximityPrize.SubmissionLower.RCN299
open ProximityPrize.Benchmark RCN174 RCN319 RCN259 RCN301 RCN300
noncomputable section
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
local instance:GCDMonoid GlobalPoly:=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
def RecursiveSpecializationBranch
   (P:Polynomial IRSProfile.Field) (gamma:IRSProfile.Field)
   (QA QB QC:GlobalPoly):Prop:=
 let phi:=(specialization IRSProfile.Field P gamma).toRingHom
 (phi (gcd12 QA QB)≠0∧
     phi (quotientA QA QB)=0∧phi (quotientB QA QB)=0)∨
   (phi (gcd12 QA QB)=0∧phi (gcd123 QA QB QC)≠0∧
     phi (middleQuotient QA QB QC)=0∧
     phi (quotientC QA QB QC)=0)∨
   (phi (gcd123 QA QB QC)=0∧phi (gcd12 QA QB)=0)
end
end ProximityPrize.SubmissionLower.RCN299
end PackedLegacy_GD

/-! Packed from ProximityPrize.SubmissionLower.CC. -/
section PackedLegacy_CC
namespace ProximityPrize.SubmissionLower.RCN304
open ProximityPrize.Benchmark RCN319 RCN259 RCN299
noncomputable section
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq (Polynomial IRSProfile.Field):=Classical.decEq _
local instance:GCDMonoid GlobalPoly:=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
def gcd12Vanishes
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (QA QB:GlobalPoly) (gamma:IRSProfile.Field):Prop:=
 specialization IRSProfile.Field (selected gamma) gamma (gcd12 QA QB)=0
def gcd123Vanishes
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (QA QB QC:GlobalPoly) (gamma:IRSProfile.Field):Prop:=
 specialization IRSProfile.Field (selected gamma) gamma (gcd123 QA QB QC)=0
def firstResidualSeeds
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB:GlobalPoly):
   Finset IRSProfile.Field:=by
 classical
 exact Gamma.filter (fun gamma↦¬ gcd12Vanishes selected QA QB gamma)
def secondResidualSeeds
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
   Finset IRSProfile.Field:=by
 classical
 exact (Gamma.filter (gcd12Vanishes selected QA QB)).filter
   (fun gamma↦¬ gcd123Vanishes selected QA QB QC gamma)
def fixedSeeds
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
   Finset IRSProfile.Field:=by
 classical
 exact (Gamma.filter (gcd12Vanishes selected QA QB)).filter
   (gcd123Vanishes selected QA QB QC)
theorem partition_card
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
   (firstResidualSeeds selected Gamma QA QB).card+
     (secondResidualSeeds selected Gamma QA QB QC).card+
     (fixedSeeds selected Gamma QA QB QC).card=Gamma.card:=by
 classical
 have houter:=Finset.card_filter_add_card_filter_not
   (s:=Gamma) (gcd12Vanishes selected QA QB)
 have hinner:=Finset.card_filter_add_card_filter_not
   (s:=Gamma.filter (gcd12Vanishes selected QA QB))
   (gcd123Vanishes selected QA QB QC)
 simp only [firstResidualSeeds,secondResidualSeeds,fixedSeeds]
 change
   (Gamma.filter (fun gamma↦¬ gcd12Vanishes selected QA QB gamma)).card+
     ((Gamma.filter (gcd12Vanishes selected QA QB)).filter
       (fun gamma↦¬ gcd123Vanishes selected QA QB QC gamma)).card+
     ((Gamma.filter (gcd12Vanishes selected QA QB)).filter
       (gcd123Vanishes selected QA QB QC)).card=Gamma.card
 omega
end
end ProximityPrize.SubmissionLower.RCN304
end PackedLegacy_CC

/-! Packed from ProximityPrize.SubmissionLower.GC. -/
section PackedLegacy_GC
namespace ProximityPrize.SubmissionLower.RCN298
open ProximityPrize.Benchmark RCN174 RCN081 RCN259 RCN301
noncomputable section
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance:GCDMonoid GlobalPoly:=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
end
end ProximityPrize.SubmissionLower.RCN298
end PackedLegacy_GC

/-! Packed from ProximityPrize.SubmissionLower.GH. -/
section PackedLegacy_GH
namespace ProximityPrize.SubmissionLower.RCN303
open scoped Classical BigOperators
open ProximityPrize.Benchmark RCN174 RCN319 RCN081 RCN238 RCN243 RCN259 RCN301 RCN299 RCN304 RCN298 RCN260 RCN318 RCN294 RCN291 RCN292 RCN052
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 35000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
abbrev StackedPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance:GCDMonoid StackedPoly:=
 UniqueFactorizationMonoid.toGCDMonoid StackedPoly
local instance:CharP IRSProfile.Field prime:=by
 simpa [prime,RCN223.prime] using
   RCN128.challenge_field_characteristic6600
def firstResidualQ2Stage:UnequalParameters:=
 ⟨262144,131071,182807,65,14,598,34,7,5263⟩
def firstResidualQ2Ceiling:ℕ:=66773536747163
def secondResidualGcd12Ceiling:ℕ:=370003897865012
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
end
end ProximityPrize.SubmissionLower.RCN303
end PackedLegacy_GH

/-! Packed from ProximityPrize.SubmissionLower.P2. -/
section PackedLegacy_P2
namespace ProximityPrize.SubmissionLower.RCN285
open scoped BigOperators Pointwise
open RCN119
noncomputable section
variable (K:Type*) [Field K]
abbrev Poly:=MvPolynomial (Fin 3) K
def seedlessExponents (M L s:ℕ):Set (Fin 3 →₀ ℕ):=
 {d | d 0 ≤ M∧d 0+d 1 ≤ L∧d 1 ≤ s∧d 2=0}
def seedlessBox (M L s:ℕ):Submodule K (Poly K):=
 MvPolynomial.restrictSupport K (seedlessExponents M L s)
theorem seedlessBox_mul
   {M L s M' L' s':ℕ} {f g:Poly K}
   (hf:f∈seedlessBox K M L s)
   (hg:g∈seedlessBox K M' L' s'):
   f*g∈seedlessBox K (M+M') (L+L') (s+s'):=by
 have hset:seedlessExponents M L s+seedlessExponents M' L' s' ⊆
     seedlessExponents (M+M') (L+L') (s+s'):=by
   rintro _ ⟨d,hd,e,he,rfl⟩
   rcases hd with ⟨hd0,hd01,hd1,hd2⟩
   rcases he with ⟨he0,he01,he1,he2⟩
   simp only [seedlessExponents,Set.mem_setOf_eq,Finsupp.add_apply]
   exact ⟨by omega,by omega,by omega,by omega⟩
 apply MvPolynomial.restrictSupport_mono (R:=K) hset
 rw [MvPolynomial.restrictSupport_add]
 exact Submodule.mul_mem_mul hf hg
theorem slopeDifference_mem_seedlessBox:
   slopeDifference K∈seedlessBox K 1 1 1:=by
 apply (seedlessBox K 1 1 1).sub_mem
 · change MvPolynomial.monomial (Finsupp.single 0 1) (1:K)∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [seedlessExponents]
 · change MvPolynomial.monomial (Finsupp.single 1 1) (1:K)∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [seedlessExponents]
theorem slopeDifference_pow_mem_seedlessBox (h:ℕ):
   slopeDifference K^h∈seedlessBox K h h h:=by
 induction h with
 | zero =>
     simp only [pow_zero]
     change MvPolynomial.monomial 0 (1:K)∈_
     apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
     left
     simp [seedlessExponents]
 | succ h ih =>
     simpa only [pow_succ] using
       seedlessBox_mul K ih (slopeDifference_mem_seedlessBox K)
theorem slopeDifference_mul_mem_seedlessBox
   {M L s h:ℕ} (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s)
   {q:Poly K} (hq:q∈seedlessBox K (M-h) (L-h) (s-h)):
   slopeDifference K^h*q∈seedlessBox K M L s:=by
 have hh:=seedlessBox_mul K (slopeDifference_pow_mem_seedlessBox K h) hq
 simpa only [Nat.add_sub_of_le hM,Nat.add_sub_of_le hL,
   Nat.add_sub_of_le hs] using hh
private def exponentPair (i j:ℕ):Fin 3 →₀ ℕ:=
 Finsupp.single 0 i+Finsupp.single 1 j
@[simp] private theorem exponentPair_zero (i j:ℕ):
   exponentPair i j 0=i:=by simp [exponentPair]
@[simp] private theorem exponentPair_one (i j:ℕ):
   exponentPair i j 1=j:=by simp [exponentPair]
@[simp] private theorem exponentPair_two (i j:ℕ):
   exponentPair i j 2=0:=by simp [exponentPair]
private theorem exponentPair_eta (d:Fin 3 →₀ ℕ) (hd:d 2=0):
   exponentPair (d 0) (d 1)=d:=by
 ext i
 fin_cases i <;> simp [hd]
abbrev SeedlessBoxIndex (M L s:ℕ):=
 (i:Fin (M+1)) × Fin (min (s+1) (L+1-i.val))
private theorem fin_heq_of_val_eq
   {a b:ℕ} {u:Fin a} {v:Fin b}
   (hab:a=b) (huv:u.val=v.val):HEq u v:=by
 subst b
 exact heq_of_eq (Fin.ext huv)
def seedlessExponentsEquivIndex (M L s:ℕ):
   seedlessExponents M L s ≃ SeedlessBoxIndex M L s where
 toFun d:=
   ⟨⟨d.val 0,Nat.lt_succ_of_le d.property.1⟩,
     ⟨d.val 1,by
       rcases d.property with ⟨_,h01,h1,_⟩
       rw [lt_min_iff]
       constructor
       · omega
       · change d.val 1 < L+1-d.val 0
         omega⟩⟩
 invFun q:=
   ⟨exponentPair q.1.val q.2.val,by
     have hi:=q.1.isLt
     have hj:=q.2.isLt
     rw [lt_min_iff] at hj
     simp only [seedlessExponents,Set.mem_setOf_eq,exponentPair_zero,
       exponentPair_one,exponentPair_two]
     exact ⟨by omega,by omega,by omega,by simp⟩⟩
 left_inv d:=Subtype.ext (exponentPair_eta d.val d.property.2.2.2)
 right_inv q:=by
   rcases q with ⟨⟨i,hi⟩,⟨j,hj⟩⟩
   apply Sigma.ext
   · apply Fin.ext
     exact exponentPair_zero i j
   · apply fin_heq_of_val_eq
     · simp only [exponentPair_zero]
     · exact exponentPair_one i j
instance seedlessExponentsFintype (M L s:ℕ):
   Fintype (seedlessExponents M L s):=
 Fintype.ofEquiv (SeedlessBoxIndex M L s)
   (seedlessExponentsEquivIndex M L s).symm
instance seedlessBoxFinite (M L s:ℕ):
   Module.Finite K (seedlessBox K M L s):=
 Module.Finite.of_basis
   (MvPolynomial.basisRestrictSupport K (seedlessExponents M L s))
def seedlessInputCount (M L s:ℕ):ℕ:=
 ∑ i∈Finset.range (M+1),min (s+1) (L+1-i)
theorem seedlessBox_finrank (M L s:ℕ):
   Module.finrank K (seedlessBox K M L s)=seedlessInputCount M L s:=by
 change Module.finrank K
     (MvPolynomial.restrictSupport K (seedlessExponents M L s))=_
 rw [Module.finrank_eq_card_basis
   (MvPolynomial.basisRestrictSupport K (seedlessExponents M L s))]
 rw [Fintype.card_congr (seedlessExponentsEquivIndex M L s)]
 simp [SeedlessBoxIndex,seedlessInputCount,Fintype.card_sigma,
   Finset.sum_range]
def seedlessBlockJet (M L s h:ℕ):
   seedlessBox K M L s →ₗ[K] Poly K:=
 (contactJet K h).comp (seedlessBox K M L s).subtype
def multiplyIntoSeedlessBox {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   seedlessBox K (M-h) (L-h) (s-h) →ₗ[K]
     seedlessBox K M L s where
 toFun q:=⟨slopeDifference K^h*q.val,
   slopeDifference_mul_mem_seedlessBox K hM hL hs q.property⟩
 map_add' q r:=by apply Subtype.ext;simp [mul_add]
 map_smul' c q:=by apply Subtype.ext;simp [mul_smul_comm]
theorem multiplyIntoSeedlessBox_injective {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (multiplyIntoSeedlessBox K hM hL hs):=by
 intro q r heq
 apply Subtype.ext
 have hh:slopeDifference K^h*q.val=
     slopeDifference K^h*r.val:=congrArg Subtype.val heq
 exact mul_left_cancel₀ (pow_ne_zero h (slopeDifference_ne_zero K)) hh
def seedlessKernelEmbedding {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   seedlessBox K (M-h) (L-h) (s-h) →ₗ[K]
     LinearMap.ker (seedlessBlockJet K M L s h):=
 LinearMap.codRestrict (LinearMap.ker (seedlessBlockJet K M L s h))
   (multiplyIntoSeedlessBox K hM hL hs) (fun q => by
     change contactJet K h (slopeDifference K^h*q.val)=0
     exact contactJet_mul_slopeDifference K h q.val)
theorem seedlessKernelEmbedding_injective {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (seedlessKernelEmbedding K hM hL hs):=by
 intro q r heq
 apply multiplyIntoSeedlessBox_injective K hM hL hs
 exact congrArg Subtype.val heq
def seedlessKernelLowerBound (M L s h:ℕ):ℕ:=
 if h ≤ M∧h ≤ L∧h ≤ s then
   seedlessInputCount (M-h) (L-h) (s-h)
 else 0
def seedlessContactRankBound (M L s h:ℕ):ℕ:=
 seedlessInputCount M L s-seedlessKernelLowerBound M L s h
theorem seedlessBlockJet_rank_le_contactRankBound
   (M L s h:ℕ) (hML:M ≤ L):
   Module.finrank K (LinearMap.range (seedlessBlockJet K M L s h)) ≤
     seedlessContactRankBound M L s h:=by
 by_cases hM:h ≤ M
 · by_cases hs:h ≤ s
   · have hL:h ≤ L:=hM.trans hML
     have hker:=LinearMap.finrank_le_finrank_of_injective
       (seedlessKernelEmbedding_injective K hM hL hs)
     have hsum:=(seedlessBlockJet K M L s h).finrank_range_add_finrank_ker
     rw [seedlessBox_finrank K] at hker
     rw [seedlessBox_finrank K] at hsum
     unfold seedlessContactRankBound seedlessKernelLowerBound
     rw [if_pos ⟨hM,hL,hs⟩]
     omega
   · have hbad:¬ (h ≤ M∧h ≤ L∧h ≤ s):=by
       intro hh
       exact hs hh.2.2
     have hinput:=(seedlessBlockJet K M L s h).finrank_range_add_finrank_ker
     rw [seedlessBox_finrank K] at hinput
     unfold seedlessContactRankBound seedlessKernelLowerBound
     rw [if_neg hbad,Nat.sub_zero]
     omega
 · have hbad:¬ (h ≤ M∧h ≤ L∧h ≤ s):=by
     intro hh
     exact hM hh.1
   have hinput:=(seedlessBlockJet K M L s h).finrank_range_add_finrank_ker
   rw [seedlessBox_finrank K] at hinput
   unfold seedlessContactRankBound seedlessKernelLowerBound
   rw [if_neg hbad,Nat.sub_zero]
   omega
end
end ProximityPrize.SubmissionLower.RCN285
end PackedLegacy_P2

/-! Packed from ProximityPrize.SubmissionLower.E9. -/
section PackedLegacy_E9
namespace ProximityPrize.SubmissionLower.RCN279
open scoped BigOperators
open ProximityPrize.Benchmark RCN285 RCN119
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
variable (K:Type*) [Field K]
abbrev LocalPoly:=MvPolynomial (Fin 3) K
abbrev Poly4:=MvPolynomial (Fin 4) K
abbrev CoefficientIndex (D w L s:ℕ):=
 (i:Fin (L+1)) × (j:Fin (s+1)) ×
   (Fin (min 1 (L+1-i.val-j.val)) ×
     Fin (D-w*i.val-(w-1)*j.val))
def columnExponent {D w L s:ℕ}
   (c:CoefficientIndex D w L s):Fin 4 →₀ ℕ:=
 Finsupp.single 0 c.2.2.2.val+Finsupp.single 1 c.1.val+
   Finsupp.single 2 c.2.1.val
@[simp] theorem columnExponent_x {D w L s:ℕ}
   (c:CoefficientIndex D w L s):columnExponent c 0=c.2.2.2.val:=by
 simp [columnExponent]
@[simp] theorem columnExponent_y {D w L s:ℕ}
   (c:CoefficientIndex D w L s):columnExponent c 1=c.1.val:=by
 simp [columnExponent]
@[simp] theorem columnExponent_r {D w L s:ℕ}
   (c:CoefficientIndex D w L s):columnExponent c 2=c.2.1.val:=by
 simp [columnExponent]
@[simp] theorem columnExponent_z {D w L s:ℕ}
   (c:CoefficientIndex D w L s):columnExponent c 3=0:=by
 simp [columnExponent]
theorem columnExponent_injective (D w L s:ℕ):
   Function.Injective
     (columnExponent (D:=D) (w:=w) (L:=L) (s:=s)):=by
 intro c d h
 have hx:=congrArg (fun e:Fin 4 →₀ ℕ => e 0) h
 have hy:=congrArg (fun e:Fin 4 →₀ ℕ => e 1) h
 have hr:=congrArg (fun e:Fin 4 →₀ ℕ => e 2) h
 rcases c with ⟨⟨ci,hci⟩,⟨⟨cj,hcj⟩,⟨⟨cz,hcz⟩,⟨ce,hce⟩⟩⟩⟩
 rcases d with ⟨⟨di,hdi⟩,⟨⟨dj,hdj⟩,⟨⟨dz,hdz⟩,⟨de,hde⟩⟩⟩⟩
 simp only [columnExponent_x] at hx
 simp only [columnExponent_y] at hy
 simp only [columnExponent_r] at hr
 subst di
 subst dj
 subst de
 have hcz0:cz=0:=by omega
 have hdz0:dz=0:=by omega
 subst cz
 subst dz
 rfl
def globalExponents (D w L s:ℕ):Set (Fin 4 →₀ ℕ):=
 {d | d 1+d 2 ≤ L∧d 2 ≤ s∧d 3=0∧
   d 0+w*d 1+(w-1)*d 2 < D}
def globalCoefficientBox (D w L s:ℕ):Submodule K (Poly4 K):=
 MvPolynomial.restrictSupport K (globalExponents D w L s)
theorem columnMonomial_mem (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a∈
     globalCoefficientBox K D w L s:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 have hi:=c.1.isLt
 have hj:=c.2.1.isLt
 have ht:=c.2.2.1.isLt
 have he:=c.2.2.2.isLt
 have htri:c.1.val+c.2.1.val ≤ L:=by
   have hminpos:0 < min 1 (L+1-c.1.val-c.2.1.val):=by
     omega
   have hpos:0 < L+1-c.1.val-c.2.1.val:=
     hminpos.trans_le (min_le_right _ _)
   omega
 unfold globalExponents
 simp only [Set.mem_setOf_eq,columnExponent_x,columnExponent_y,
   columnExponent_r,columnExponent_z]
 exact ⟨htri,by omega,by simp,by omega⟩
def reconstruct (D w L s:ℕ) (theta:CoefficientIndex D w L s → K):
   Poly4 K:=
 ∑ c:CoefficientIndex D w L s,
   MvPolynomial.monomial (columnExponent c) (theta c)
theorem reconstruct_coeff (D w L s:ℕ)
   (theta:CoefficientIndex D w L s → K) (c:CoefficientIndex D w L s):
   MvPolynomial.coeff (columnExponent c) (reconstruct K D w L s theta)=
     theta c:=by
 classical
 simp [reconstruct,MvPolynomial.coeff_sum,
   (columnExponent_injective D w L s).eq_iff]
@[simp] theorem reconstruct_zero (D w L s:ℕ):
   reconstruct K D w L s (0:CoefficientIndex D w L s → K)=0:=by
 simp [reconstruct]
theorem reconstruct_injective (D w L s:ℕ):
   Function.Injective (reconstruct K D w L s):=by
 intro theta eta h
 funext c
 have hh:=congrArg (MvPolynomial.coeff (columnExponent c)) h
 simpa only [reconstruct_coeff] using hh
theorem reconstruct_ne_zero (D w L s:ℕ)
   (theta:CoefficientIndex D w L s → K) (htheta:theta≠0):
   reconstruct K D w L s theta≠0:=by
 intro hz
 apply htheta
 apply reconstruct_injective K D w L s
 simpa only [reconstruct_zero] using hz
theorem reconstruct_mem_box (D w L s:ℕ)
   (theta:CoefficientIndex D w L s → K):
   reconstruct K D w L s theta∈globalCoefficientBox K D w L s:=by
 classical
 unfold reconstruct
 apply Submodule.sum_mem
 intro c hc
 exact columnMonomial_mem K D w L s c (theta c)
def coefficientCount (D w L s:ℕ):ℕ:=
 ∑ i∈Finset.range (L+1),
   ∑ j∈Finset.range (s+1),
     min 1 (L+1-i-j)*(D-w*i-(w-1)*j)
theorem coefficient_index_card (D w L s:ℕ):
   Fintype.card (CoefficientIndex D w L s)=coefficientCount D w L s:=by
 simp [CoefficientIndex,coefficientCount,Fintype.card_sigma,
   Finset.sum_range]
def localMonomial (f j:ℕ):LocalPoly K:=
 MvPolynomial.monomial (Finsupp.single 0 f+Finsupp.single 1 j) 1
theorem localMonomial_mem (f j:ℕ):
   localMonomial K f j∈seedlessBox K f (f+j) j:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 simp [localMonomial,seedlessExponents]
def blockEntry (D w L s:ℕ) (x u:K)
   (c:CoefficientIndex D w L s) (r:ℕ):LocalPoly K:=
 ∑ f:Fin (c.1.val+1),
   if f.val ≤ r then
     ((((c.2.2.2.val.choose (r-f.val):ℕ):K)*
       x^(c.2.2.2.val-(r-f.val))*
       ((c.1.val.choose f.val:ℕ):K)*u^(c.1.val-f.val))) •
         localMonomial K f.val c.2.1.val
   else 0
theorem blockEntry_mem (D w L s:ℕ) (x u:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   blockEntry K D w L s x u c r∈
     seedlessBox K (min r L) L s:=by
 classical
 unfold blockEntry
 apply Submodule.sum_mem
 intro f hf
 split_ifs with hfr
 · apply (seedlessBox K (min r L) L s).smul_mem
   apply MvPolynomial.restrictSupport_mono (R:=K) ?_
     (localMonomial_mem K f.val c.2.1.val)
   intro d hd
   rcases hd with ⟨hd0,hd01,hd1,hd2⟩
   have hi:=c.1.isLt
   have hj:=c.2.1.isLt
   have ht:=c.2.2.1.isLt
   have hfi:=f.isLt
   have htri:c.1.val+c.2.1.val ≤ L:=by
     have hminpos:0 < min 1 (L+1-c.1.val-c.2.1.val):=by
       omega
     have hpos:0 < L+1-c.1.val-c.2.1.val:=
       hminpos.trans_le (min_le_right _ _)
     omega
   exact ⟨hd0.trans (by omega),by omega,hd1.trans (by omega),hd2⟩
 · exact (seedlessBox K (min r L) L s).zero_mem
def boundedBlockEntry (D w L s:ℕ) (x u:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   seedlessBox K (min r L) L s:=
 ⟨blockEntry K D w L s x u c r,blockEntry_mem K D w L s x u c r⟩
def extractBlock (D w L s:ℕ) (x u:K) (r:ℕ):
   (CoefficientIndex D w L s → K) →ₗ[K]
     seedlessBox K (min r L) L s where
 toFun theta:=∑ c:CoefficientIndex D w L s,
   theta c • boundedBlockEntry K D w L s x u c r
 map_add' theta eta:=by
   simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
 map_smul' a theta:=by
   simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul,
     RingHom.id_apply]
def localRankBound (m L s:ℕ):ℕ:=
 ∑ r∈Finset.range m,
   seedlessContactRankBound (min r L) L s (m-r)
abbrev LocalTarget (m L s:ℕ):=
 (r:Fin m) → LinearMap.range
   (seedlessBlockJet K (min r.val L) L s (m-r.val))
theorem localTarget_finrank_le (m L s:ℕ):
   Module.finrank K (LocalTarget K m L s) ≤ localRankBound m L s:=by
 change Module.finrank K ((r:Fin m) → LinearMap.range
   (seedlessBlockJet K (min r.val L) L s (m-r.val))) ≤ _
 rw [Module.finrank_pi_fintype]
 unfold localRankBound
 rw [Finset.sum_range]
 apply Finset.sum_le_sum
 intro r hr
 exact seedlessBlockJet_rank_le_contactRankBound K (min r.val L) L s
   (m-r.val) (min_le_right r.val L)
abbrev GlobalTarget (I:Type*) (m L s:ℕ):=I → LocalTarget K m L s
def constraintMap {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes received:I → K):
   (CoefficientIndex D w L s → K) →ₗ[K] GlobalTarget K I m L s:=
 LinearMap.pi fun i => LinearMap.pi fun r =>
   (seedlessBlockJet K (min r.val L) L s (m-r.val)).rangeRestrict.comp
     (extractBlock K D w L s (nodes i) (received i) r.val)
theorem exists_nonzero_kernel_array {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes received:I → K)
   (hgate:Fintype.card I*localRankBound m L s <
     coefficientCount D w L s):
   ∃ theta:CoefficientIndex D w L s → K,theta≠0∧
     constraintMap K D w L s m nodes received theta=0:=by
 classical
 by_contra hnone
 have hinj:Function.Injective
     (constraintMap K D w L s m nodes received):=by
   intro theta eta heq
   by_contra hne
   apply hnone
   refine ⟨theta-eta,sub_ne_zero.mpr hne,?_⟩
   rw [map_sub,heq,sub_self]
 have hdim:=LinearMap.finrank_le_finrank_of_injective hinj
 rw [Module.finrank_fintype_fun_eq_card,coefficient_index_card] at hdim
 have htarget:Module.finrank K (GlobalTarget K I m L s) ≤
     Fintype.card I*localRankBound m L s:=by
   change Module.finrank K (I → LocalTarget K m L s) ≤ _
   rw [Module.finrank_pi_fintype]
   calc
     (∑ _i:I,Module.finrank K (LocalTarget K m L s)) ≤
         ∑ _i:I,localRankBound m L s:=by
       apply Finset.sum_le_sum
       intro i hi
       exact localTarget_finrank_le K m L s
     _=Fintype.card I*localRankBound m L s:=by simp
 exact (Nat.not_le_of_gt hgate) (hdim.trans htarget)
theorem all_blocks_divisible_of_kernel {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes received:I → K)
   (theta:CoefficientIndex D w L s → K)
   (hzero:constraintMap K D w L s m nodes received theta=0):
   ∀ i:I,∀ r:ℕ,slopeDifference K^(m-r)∣
     ((extractBlock K D w L s (nodes i) (received i) r theta):LocalPoly K):=by
 intro i r
 by_cases hr:r < m
 · have hh:=congrArg
     (fun t:GlobalTarget K I m L s => ((t i ⟨r,hr⟩):LocalPoly K)) hzero
   change contactJet K (m-r)
     ((extractBlock K D w L s (nodes i) (received i) r theta):LocalPoly K)=0 at hh
   exact (contactJet_eq_zero_iff K (m-r) _).mp hh
 · have hm:m-r=0:=by omega
   simp only [hm,pow_zero,one_dvd]
def homogenizedTranslation (x u:K):
   Poly4 K →ₐ[K] Polynomial (LocalPoly K):=
 RCN122.homogenizedTranslation K x u 0
theorem columnMonomial_eq (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a=
     MvPolynomial.C a*MvPolynomial.X 0^c.2.2.2.val*
       MvPolynomial.X 1^c.1.val*MvPolynomial.X 2^c.2.1.val:=by
 rw [columnExponent,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single,
   ←MvPolynomial.C_mul_X_pow_eq_monomial]
theorem localMonomial_eq (f j:ℕ):
   localMonomial K f j=MvPolynomial.X 0^f*MvPolynomial.X 1^j:=by
 rw [localMonomial,MvPolynomial.monomial_add_single,
   ←MvPolynomial.X_pow_eq_monomial]
theorem translation_column_coeff (D w L s:ℕ) (x u:K)
   (c:CoefficientIndex D w L s) (a:K) (r:ℕ):
   (homogenizedTranslation K x u
     (MvPolynomial.monomial (columnExponent c) a)).coeff r=
       a • blockEntry K D w L s x u c r:=by
 have hfactor:
     homogenizedTranslation K x u
         (MvPolynomial.monomial (columnExponent c) a)=
       Polynomial.C (MvPolynomial.C a)*
         (((Polynomial.X+Polynomial.C (MvPolynomial.C x))^c.2.2.2.val*
           (Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
             Polynomial.C (MvPolynomial.C u))^c.1.val*
           Polynomial.C (MvPolynomial.X 1^c.2.1.val))):=by
   rw [columnMonomial_eq K D w L s]
   simp [homogenizedTranslation,
     RCN122.homogenizedTranslation,
     RCN122.translationVariables,
     RCN100.seedAffine,
     Polynomial.algebraMap_apply,MvPolynomial.algebraMap_eq]
   ring
 rw [hfactor,Polynomial.coeff_C_mul,
   RCN122.coeff_shifted_affine_product]
 unfold blockEntry
 rw [Finset.mul_sum,Finset.smul_sum]
 apply Finset.sum_congr rfl
 intro f hf
 split_ifs with hfr
 · simp only [localMonomial_eq,MvPolynomial.smul_eq_C_mul,map_mul,
     map_pow,map_natCast]
   ring
 · simp
theorem translation_reconstruct_coeff (D w L s:ℕ) (x u:K)
   (theta:CoefficientIndex D w L s → K) (r:ℕ):
   (homogenizedTranslation K x u (reconstruct K D w L s theta)).coeff r=
     ((extractBlock K D w L s x u r theta):LocalPoly K):=by
 rw [reconstruct,map_sum,Polynomial.finsetSum_coeff]
 simp only [translation_column_coeff]
 change (∑ c:CoefficientIndex D w L s,
     theta c • blockEntry K D w L s x u c r)=
   (((∑ c:CoefficientIndex D w L s,
     theta c • boundedBlockEntry K D w L s x u c r):
       seedlessBox K (min r L) L s):LocalPoly K)
 simp [boundedBlockEntry]
def n:ℕ:=262144
def errors:ℕ:=79866
def agreements:ℕ:=n-errors
def w:ℕ:=131071
def multiplicity:ℕ:=37
def yTotalCap:ℕ:=51
def slopeCap:ℕ:=9
def weightedCap:ℕ:=multiplicity*agreements
theorem parameter_values:
   agreements=182278∧weightedCap=6744286:=by
 norm_num [agreements,weightedCap,multiplicity,n,errors]
theorem coefficient_count_exact:
   coefficientCount weightedCap w yTotalCap slopeCap=1481264965:=by
 decide
theorem local_rank_exact:
   localRankBound multiplicity yTotalCap slopeCap=5650:=by
 decide
theorem nullity_exact:
   coefficientCount weightedCap w yTotalCap slopeCap-
     n*localRankBound multiplicity yTotalCap slopeCap=151365:=by
 rw [coefficient_count_exact,local_rank_exact]
 norm_num [n]
theorem interpolation_gate:
   n*localRankBound multiplicity yTotalCap slopeCap <
     coefficientCount weightedCap w yTotalCap slopeCap:=by
 rw [coefficient_count_exact,local_rank_exact]
 norm_num [n]
theorem exists_frozen_seedless_interpolant
   (received:IRSProfile.Index → IRSProfile.Field):
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q≠0∧
     Q∈globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap∧
     ∀ (i:IRSProfile.Index) (r:ℕ),
       slopeDifference IRSProfile.Field^(multiplicity-r)∣
         (RCN319.homogenizedTranslation IRSProfile.Field
           (IRSProfile.domain i) (received i) 0 Q).coeff r:=by
 obtain ⟨theta,htheta,hzero⟩:=exists_nonzero_kernel_array
   IRSProfile.Field weightedCap w yTotalCap slopeCap multiplicity
   IRSProfile.domain received (by
     rw [show Fintype.card IRSProfile.Index=n by
       norm_num [IRSProfile.Index,n]]
     exact interpolation_gate)
 refine ⟨reconstruct IRSProfile.Field weightedCap w yTotalCap slopeCap theta,
   reconstruct_ne_zero IRSProfile.Field _ _ _ _ theta htheta,
   reconstruct_mem_box IRSProfile.Field _ _ _ _ theta,?_⟩
 intro i r
 have hdiv:=all_blocks_divisible_of_kernel IRSProfile.Field
   weightedCap w yTotalCap slopeCap multiplicity IRSProfile.domain received
   theta hzero i r
 rw [←translation_reconstruct_coeff IRSProfile.Field weightedCap w
   yTotalCap slopeCap (IRSProfile.domain i) (received i) theta r] at hdiv
 exact hdiv
theorem seedlessBox_le_legacy:
   globalCoefficientBox IRSProfile.Field weightedCap w yTotalCap slopeCap ≤
     RCN174.globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap:=by
 apply MvPolynomial.restrictSupport_mono
 intro d hd
 rcases hd with ⟨hYR,hR,hZ,hweighted⟩
 exact ⟨by omega,hR,hweighted⟩
theorem exists_frozen_seedless_vanishing_interpolant
   (received:IRSProfile.Index → IRSProfile.Field):
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q≠0∧
     Q∈globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap∧
     Q∈RCN174.globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap∧
     ∀ (P:Polynomial IRSProfile.Field)
       (support:Finset IRSProfile.Index),
       P.natDegree ≤ w → agreements ≤ support.card →
       (∀ i∈support,P.eval (IRSProfile.domain i)=received i) →
       RCN319.specialization IRSProfile.Field P 0 Q=0:=by
 classical
 obtain ⟨Q,hQ,hbox,hcontact⟩:=
   exists_frozen_seedless_interpolant received
 have hlegacy:=seedlessBox_le_legacy hbox
 refine ⟨Q,hQ,hbox,hlegacy,?_⟩
 intro P support hdegree hcard hvalues
 apply RCN319.specialization_eq_zero_of_contact_and_degree
   IRSProfile.Field Q P 0 IRSProfile.domain received (fun _ => 0)
     support multiplicity
 · intro i hi r
   exact hcontact i r
 · intro i hi
   simpa only [mul_zero,add_zero] using hvalues i hi
 · have hdeg:=RCN319.specialization_natDegree_lt
     IRSProfile.Field weightedCap w yTotalCap slopeCap Q P 0
     (by norm_num [weightedCap,multiplicity,agreements,n,errors])
     hlegacy hdegree
   have hbound:weightedCap ≤ multiplicity*support.card:=by
     rw [weightedCap]
     exact Nat.mul_le_mul_left multiplicity hcard
   exact hdeg.trans_le hbound
end
end ProximityPrize.SubmissionLower.RCN279
end PackedLegacy_E9

/-! Packed from ProximityPrize.SubmissionLower.O9. -/
section PackedLegacy_O9
namespace ProximityPrize.SubmissionLower.RCN282
open scoped Classical BigOperators
open RCN002 RCN007 RCN004 RCN001 RCN013 RCN136 RCN231 RCN229 RCN065 RCN238 RCN173 RCN264 RCN243 RCN319 RCN163
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
variable {K Omega:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 (phi:Polynomial K →+*Omega)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
def seedlessPoint (S:Polynomial K):Fin 3 → Omega:=
 fun i => polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X) i.succ
theorem seedlessPoint_value (S:Polynomial K):
   seedlessPoint phi S=![phi S,phi S.derivative,0]:=by
 funext i
 fin_cases i <;>
   simp [seedlessPoint,polynomialPoint,polynomial_eval₂_comp_C_X]
theorem seedlessPoint_injective (hphi:Function.Injective phi):
   Function.Injective (seedlessPoint phi):=by
 intro S T h
 apply hphi
 have h0:=congrFun h (0:Fin 3)
 simpa only [seedlessPoint_value,Matrix.cons_val_zero] using h0
theorem seedlessPoint_surface_evaluation (S:Polynomial K)
   (Q:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (seedlessPoint phi S) (surfaceMap phi Q)=
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X)) Q:=by
 rw [eval_surfaceMap]
 have hv:Fin.cases (phi Polynomial.X) (seedlessPoint phi S)=
     polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X):=by
   funext i
   fin_cases i <;> rfl
 rw [hv]
theorem seedless_agreement_zero_iff
   (F:MvPolynomial (Fin 4) K) (S:Polynomial K)
   (p w:ℕ) [CharP Omega p] (hchar:w < p)
   (hdegree:S.natDegree ≤ w)
   (hsolution:specialization K S 0 F=0)
   (hregular:MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (x u:K):
   MvPolynomial.aeval (seedlessPoint phi S)
     (agreementPolynomial phi F w x u 0)=0 ↔ S.eval x=u:=by
 have hpoint:seedlessPoint phi S=selectedPoint phi (fun _:K => S) 0:=rfl
 rw [hpoint]
 simpa only [zero_mul,add_zero] using
   (selected_agreement_zero_iff phi F (fun _:K => S) p w hchar 0
     hdegree hsolution hregular x u 0)
variable (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
theorem seedless_agreement_fiber_card_le
   (hphi:Function.Injective phi)
   (hproj:ProjectionsFiniteSeparable Omega P)
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K) (Gamma:Finset (Polynomial K))
   (p w:ℕ) [CharP Omega p] (hchar:w < p)
   (hdegree:∀ S∈Gamma,S.natDegree ≤ w)
   (hsolution:∀ S∈Gamma,specialization K S 0 F=0)
   (hregular:∀ S∈Gamma,MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ S∈Gamma,P ≤ RingHom.ker
     (MvPolynomial.aeval (seedlessPoint phi S)).toRingHom)
   (x u:K) (hproper:agreementPolynomial phi F w x u 0∉P)
   (cap:Fin 3 → ℕ)
   (hcap:∀ j,(agreementPolynomial phi F w x u 0).degreeOf j ≤ cap j):
   (Gamma.filter (fun S => S.eval x=u)).card ≤ componentCost P cap:=by
 classical
 let fiber:=Gamma.filter (fun S => S.eval x=u)
 let points:=fiber.image (seedlessPoint phi)
 have hpointsP:∀ v∈points,
     P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨S,hS,rfl⟩:=Finset.mem_image.mp hv
   exact hpoint S (Finset.mem_filter.mp hS).1
 have hpointsF:∀ v∈points,
     MvPolynomial.aeval v (agreementPolynomial phi F w x u 0)=0:=by
   intro v hv
   obtain ⟨S,hS,rfl⟩:=Finset.mem_image.mp hv
   obtain ⟨hGamma,hagree⟩:=Finset.mem_filter.mp hS
   exact (seedless_agreement_zero_iff phi F S p w hchar
     (hdegree S hGamma) (hsolution S hGamma) (hregular S hGamma) x u).mpr hagree
 have hcount:=RCN007.finite_zero_points_le_box Omega P hproj
   hnonpoint (agreementPolynomial phi F w x u 0) hproper cap hcap
   points hpointsP hpointsF
 have hcard:points.card=fiber.card:=
   Finset.card_image_of_injective _ (seedlessPoint_injective phi hphi)
 rw [hcard] at hcount
 unfold componentCost
 exact_mod_cast hcount
theorem coordinate_two_eq_zero (hZ:MvPolynomial.X (2:Fin 3)∈P):
   coordinate Omega P 2=0:=by
 change coordinateEvaluation Omega P (MvPolynomial.X (2:Fin 3))=0
 change MvPolynomial.X (2:Fin 3)∈
   RingHom.ker (coordinateEvaluation Omega P).toRingHom
 rwa [coordinateEvaluation_ker]
theorem identityNodes_card_le_of_seedless_cut
   (F:MvPolynomial (Fin 4) K)
   (hF:surfaceMap phi F∈P)
   (hH:surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F)∉P)
   (hZ:MvPolynomial.X (2:Fin 3)∈P)
   {Iota:Type} (nodes:Finset Iota) (x u:Iota → K)
   (w:ℕ) (hw:1 ≤ w) (hinj:Set.InjOn x nodes)
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom):
   (identityNodes phi P F nodes x u (fun _ => 0) w).card ≤ w:=by
 classical
 by_contra hnot
 have hmany:w < (identityNodes phi P F nodes x u (fun _ => 0) w).card:=
   Nat.lt_of_not_ge hnot
 have htrans:=seed_transcendental_of_many_identities phi P F hF hH
   nodes x u (fun _ => 0) w hw hinj hmany hnonpoint
 have hz0:=coordinate_two_eq_zero P hZ
 rw [hz0] at htrans
 exact htrans isAlgebraic_zero
variable {Iota:Type}
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem seedless_prime_incidence
   (hphi:Function.Injective phi)
   (hproj:ProjectionsFiniteSeparable Omega P)
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K)
   (hF:surfaceMap phi F∈P)
   (hH:surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F)∉P)
   (hZ:MvPolynomial.X (2:Fin 3)∈P)
   (Gamma:Finset (Polynomial K))
   (nodes:Finset Iota) (x u:Iota → K) (hinj:Set.InjOn x nodes)
   (p w a:ℕ) [CharP Omega p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegree:∀ S∈Gamma,S.natDegree ≤ w)
   (hsolution:∀ S∈Gamma,specialization K S 0 F=0)
   (hregular:∀ S∈Gamma,MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ S∈Gamma,P ≤ RingHom.ker
     (MvPolynomial.aeval (seedlessPoint phi S)).toRingHom)
   (hagreement:∀ S∈Gamma,
     a ≤ (nodes.filter (fun i => S.eval (x i)=u i)).card)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial phi F w (x i) (u i) 0).degreeOf j ≤ cap j):
   Gamma.card*(a-w) ≤ (nodes.card-w)*componentCost P cap:=by
 classical
 let I:=identityNodes phi P F nodes x u (fun _ => 0) w
 let relation:Polynomial K → Iota → Prop:=fun S i => S.eval (x i)=u i
 have hI:I.card ≤ w:=identityNodes_card_le_of_seedless_cut phi P F hF hH
   hZ nodes x u w hw hinj hnonpoint
 have hfiber:∀ i∈nodes \ I,
     (Gamma.filter (fun S => relation S i)).card ≤ componentCost P cap:=by
   intro i hi
   obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
   have hproper:agreementPolynomial phi F w (x i) (u i) 0∉P:=by
     intro hmem
     apply hnotI
     exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
   exact seedless_agreement_fiber_card_le phi P hphi hproj hnonpoint F Gamma
     p w hchar hdegree hsolution hregular hpoint (x i) (u i) hproper cap
     (hcap i hinodes)
 exact sharp_incidence_bound relation Gamma nodes I a w (componentCost P cap)
   (identityNodes_subset phi P F nodes x u (fun _ => 0) w) hI hwa han
   hagreement hfiber
end
end ProximityPrize.SubmissionLower.RCN282
end PackedLegacy_O9

/-! Packed from ProximityPrize.SubmissionLower.P0. -/
section PackedLegacy_P0
namespace ProximityPrize.SubmissionLower.RCN283
open scoped Classical BigOperators
open RCN002 RCN007 RCN004 RCN001 RCN013 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN282
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 (phi:Polynomial K →+*Omega)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
def seedlessCut:MvPolynomial (Fin 3) Omega:=MvPolynomial.X 2
theorem seedless_proper_cut_bound
   (hphi:Function.Injective phi)
   (F:MvPolynomial (Fin 4) K) (G:MvPolynomial (Fin 3) Omega)
   (hG:Irreducible G) (hdiv:G∣surfaceMap phi F)
   (hproper:¬ G∣seedlessCut)
   (Gamma:Finset (Polynomial K))
   (nodes:Finset Iota) (x u:Iota → K) (hinj:Set.InjOn x nodes)
   (p w a:ℕ) [CharP Omega p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hcutDegree:∀ j k:Fin 3,j≠k →
     (seedlessCut (Omega:=Omega)).degreeOf j*G.degreeOf k+
       G.degreeOf j*(seedlessCut (Omega:=Omega)).degreeOf k < p)
   (hdegree:∀ S∈Gamma,S.natDegree ≤ w)
   (hsolution:∀ S∈Gamma,specialization K S 0 F=0)
   (hregular:∀ S∈Gamma,MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ S∈Gamma,
     MvPolynomial.eval (seedlessPoint phi S) G=0)
   (hagreement:∀ S∈Gamma,
     a ≤ (nodes.filter (fun i => S.eval (x i)=u i)).card)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial phi F w (x i) (u i) 0).degreeOf j ≤ cap j):
   Gamma.card*(a-w) ≤
     (nodes.card-w)*
       (∑ i,cap i*coordinateMixedDegree Omega G seedlessCut i):=by
 classical
 let T:MvPolynomial (Fin 3) Omega:=seedlessCut
 let H:=regularitySurface phi F
 have hTpoint:∀ S∈Gamma,
     MvPolynomial.eval (seedlessPoint phi S) T=0:=by
   intro S hS
   simp [T,seedlessCut,seedlessPoint_value]
 have hHp:∀ S∈Gamma,
     MvPolynomial.eval (seedlessPoint phi S) H≠0:=by
   intro S hS
   change MvPolynomial.eval (seedlessPoint phi S)
     (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [seedlessPoint_surface_evaluation]
   exact hregular S hS
 let degree:RegularComponent Omega G T H → Fin 3 → ℕ:=
   fun C i => actualCoordinateDegree Omega C.1 i
 have hcomponent:∀ C:RegularComponent Omega G T H,
     (componentSeeds Omega G T H Gamma (seedlessPoint phi) C).card*
         (a-w) ≤
       (nodes.card-w)*(∑ i,cap i*degree C i):=by
   intro C
   have hsub:=componentSeeds_subset Omega G T H Gamma (seedlessPoint phi) C
   have hgmem:=regularComponent_G_mem Omega G T H C
   have htmem:=regularComponent_T_mem Omega G T H C
   have hFmem:surfaceMap phi F∈C.1:=
     ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
       (Ideal.mem_span_singleton.mpr hdiv)
   have hproj:ProjectionsFiniteSeparable Omega C.1:=
     all_transcendental_coordinates_finite_separable Omega C.1 p G T
       hG hgmem htmem hproper hGdegree hcutDegree
   exact seedless_prime_incidence phi C.1 hphi hproj
     (regularComponent_ne_point Omega G T H C) F hFmem
     (regularComponent_H_not_mem Omega G T H C) htmem
     (componentSeeds Omega G T H Gamma (seedlessPoint phi) C)
     nodes x u hinj p w a hw hchar hwa han
     (fun S hS => hdegree S (hsub hS))
     (fun S hS => hsolution S (hsub hS))
     (fun S hS => hregular S (hsub hS))
     (fun S hS => componentSeeds_on_prime Omega G T H Gamma
       (seedlessPoint phi) C S hS)
     (fun S hS => hagreement S (hsub hS)) cap hcap
 have hbudget:∀ i,
     (∑ C:RegularComponent Omega G T H,
       actualCoordinateDegree Omega C.1 i) ≤
         coordinateMixedDegree Omega G T i:=
   regularComponents_degree_budget phi F G T p hG hproper hGdegree hcutDegree
 have hagg:=aggregate_component_incidence Omega G T H Gamma
   (seedlessPoint phi) hGpoint hTpoint hHp (a-w) (nodes.card-w) 0
   cap (coordinateMixedDegree Omega G T) degree
   (fun C => by simpa only [Nat.zero_mul,Nat.add_zero] using hcomponent C)
   hbudget
 simpa only [T,Nat.zero_mul,Nat.add_zero] using hagg
end
end ProximityPrize.SubmissionLower.RCN283
end PackedLegacy_P0

/-! Packed from ProximityPrize.SubmissionLower.O8. -/
section PackedLegacy_O8
namespace ProximityPrize.SubmissionLower.RCN281
open scoped Classical BigOperators
open ProximityPrize.Benchmark RCN319 RCN174 RCN231 RCN081 RCN167 RCN313 RCN136 RCN135 RCN138 RCN137 RCN267 RCN238 RCN243 RCN222 RCN290 RCN293 RCN286 RCN279 RCN282 RCN283 RCN001
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
def prime:ℕ:=2130706433
def gap:ℕ:=agreements-w
def capY:ℕ:=1+2*w*yTotalCap
def capR:ℕ:=w*(2*slopeCap-1)
def agreementCap:Fin 3 → ℕ:=![capY,capR,1]
def regularListNumerator:ℕ:=
 (n-w)*(capY*slopeCap+capR*yTotalCap)
def singularListCap:ℕ:=(2*slopeCap-1)*yTotalCap
def listNumerator:ℕ:=regularListNumerator+singularListCap*gap
def listBudget:ℕ:=600000000
theorem list_numerator_fits:listNumerator < listBudget*gap:=by
 norm_num [listNumerator,regularListNumerator,singularListCap,listBudget,
   gap,capY,capR,agreements,n,errors,w,yTotalCap,slopeCap]
variable (K:Type) [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)
theorem seedless_degree_caps
   (Q:MvPolynomial (Fin 4) K)
   (hbox:Q∈RCN279.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap):
   Q.degreeOf 1 ≤ yTotalCap∧Q.degreeOf 2 ≤ slopeCap∧
     Q.degreeOf 3=0:=by
 refine ⟨MvPolynomial.degreeOf_le_iff.mpr ?_,
   MvPolynomial.degreeOf_le_iff.mpr ?_,?_⟩
 · intro d hd
   exact (Nat.le_add_right (d 1) (d 2)).trans (hbox hd).1
 · intro d hd
   exact (hbox hd).2.1
 · apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.2.1.le
theorem agreement_cap
   (phi:Polynomial K →+*GenericField K)
   (F:MvPolynomial (Fin 4) K)
   (hY:F.degreeOf 1 ≤ yTotalCap)
   (hR:F.degreeOf 2 ≤ slopeCap)
   (hZ:F.degreeOf 3=0) (x u:K):
   ∀ j,(agreementPolynomial phi F w x u 0).degreeOf j ≤ agreementCap j:=by
 have hb:=agreementNumerator_degree_bounds F yTotalCap slopeCap 0
   (by norm_num [slopeCap]) hY hR hZ.le w
     (fun j => (j.factorial:K)⁻¹) x u 0
 intro j
 fin_cases j
 · exact (surfaceMap_degreeOf_le phi _ 0).trans
     (hb.1.trans (by simp [agreementCap,capY]))
 · exact (surfaceMap_degreeOf_le phi _ 1).trans
     (hb.2.1.trans (by simp [agreementCap,capR]))
 · exact (surfaceMap_degreeOf_le phi _ 2).trans
     (hb.2.2.trans (by simp [agreementCap]))
abbrev GeometricFactor (F:MvPolynomial (Fin 4) K):=
 RCN222.GeometricFactor K F
def geometricPolynomials (F:MvPolynomial (Fin 4) K)
   (Gamma:Finset (Polynomial K)) (g:GeometricFactor K F):
   Finset (Polynomial K):=by
 classical
 exact Gamma.filter (fun S =>
   MvPolynomial.eval (seedlessPoint (polynomialEmbedding K) S) g.1=0)
theorem geometricPolynomials_subset
   (F:MvPolynomial (Fin 4) K) (Gamma:Finset (Polynomial K))
   (g:GeometricFactor K F):geometricPolynomials K F Gamma g ⊆ Gamma:=by
 classical
 exact Finset.filter_subset _ _
theorem card_le_sum_geometricPolynomials
   (F:MvPolynomial (Fin 4) K) (hF:F≠0)
   (Gamma:Finset (Polynomial K))
   (hsolutions:∀ S∈Gamma,specialization K S 0 F=0):
   Gamma.card ≤ ∑ g:GeometricFactor K F,
     (geometricPolynomials K F Gamma g).card:=by
 classical
 have hcover:Gamma ⊆ Finset.univ.biUnion (geometricPolynomials K F Gamma):=by
   intro S hS
   have hz:MvPolynomial.eval (seedlessPoint (polynomialEmbedding K) S)
       (surfaceMap (polynomialEmbedding K) F)=0:=by
     rw [seedlessPoint_surface_evaluation,
       eval_polynomialPoint_eq_specialization,hsolutions S hS]
     simp
   obtain ⟨g,hg,hzg⟩:=exists_surfaceFactor_zero (polynomialEmbedding K)
     (polynomialEmbedding_injective K) F hF
     (seedlessPoint (polynomialEmbedding K) S) hz
   exact Finset.mem_biUnion.mpr ⟨⟨g,hg⟩,Finset.mem_univ _,
     Finset.mem_filter.mpr ⟨hS,hzg⟩⟩
 exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le
theorem geometric_seedless_cut_proper
   (g:MvPolynomial (Fin 3) (GenericField K))
   (hR:0 < g.degreeOf 1):
   ¬ g∣(seedlessCut:MvPolynomial (Fin 3) (GenericField K)):=by
 intro hdvd
 have hle:=coordinate_degree_le_of_dvd 1 g seedlessCut hdvd
   (by simp [seedlessCut])
 have hx:(seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 1=0:=by
   simp [seedlessCut,MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3)≠2)]
 rw [hx] at hle
 omega
theorem original_regular_seedless_bound
   [CharP K prime]
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hRpos:0 < F.degreeOf 2)
   (hbox:F∈RCN174.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (hY:F.degreeOf 1 ≤ yTotalCap)
   (hR:F.degreeOf 2 ≤ slopeCap)
   (hZ:F.degreeOf 3=0)
   (Gamma:Finset (Polynomial K))
   (hdegree:∀ S∈Gamma,S.natDegree ≤ w)
   (hsolutions:∀ S∈Gamma,specialization K S 0 F=0)
   (hregular:∀ S∈Gamma,
     specialization K S 0 (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   {Iota:Type} [Fintype Iota] [DecidableEq Iota]
   (nodes:Finset Iota) (x received:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
   (hagreement:∀ S∈Gamma,agreements ≤
     (nodes.filter (fun i => S.eval (x i)=received i)).card):
   Gamma.card*gap ≤
     (n-w)*(capY*F.degreeOf 2+capR*F.degreeOf 1):=by
 classical
 letI:CharP (GenericField K) prime:=genericField_charP K prime
 have hsmall:F.degreeOf 2 < prime:=hR.trans_lt (by
   norm_num [slopeCap,prime])
 have hcount (g:GeometricFactor K F):
     (geometricPolynomials K F Gamma g).card*gap ≤
       (n-w)*(capY*g.1.degreeOf 1+capR*g.1.degreeOf 0):=by
   obtain ⟨hgirred,hgdiv⟩:=
     surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2
   have hgate:=geometric_factor_regular_gate K (GenericField K) F hF
     prime hRpos hsmall g.1 hgirred
     (by simpa only [canonical_geometricSurfaceMap] using hgdiv)
   have hproper:=geometric_seedless_cut_proper K g.1 hgate.1
   have hgY:=(geometricFactor_degree_le K F hF.ne_zero g 0).trans hY
   have hgR:=(geometricFactor_degree_le K F hF.ne_zero g 1).trans hR
   have hgZ:g.1.degreeOf 2=0:=Nat.eq_zero_of_le_zero
     ((geometricFactor_degree_le K F hF.ne_zero g 2).trans_eq hZ)
   have hGdegree:∀ j:Fin 3,g.1.degreeOf j < prime:=by
     intro j
     fin_cases j
     · exact hgY.trans_lt (by norm_num [yTotalCap,prime])
     · exact hgR.trans_lt (by norm_num [slopeCap,prime])
     · simp [hgZ,prime]
   have hcutDegree:∀ j k:Fin 3,j≠k →
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf j*
           g.1.degreeOf k+
         g.1.degreeOf j*
           (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf k < prime:=by
     intro j k hjk
     have h0:=hGdegree 0
     have h1:=hGdegree 1
     have h2:=hGdegree 2
     fin_cases j <;> fin_cases k <;>
       simp [seedlessCut,MvPolynomial.degreeOf_X_of_ne] at hjk ⊢ <;>
       omega
   have hsub:=geometricPolynomials_subset K F Gamma g
   have hraw:=seedless_proper_cut_bound (polynomialEmbedding K)
     (polynomialEmbedding_injective K) F g.1 hgirred hgdiv hproper
     (geometricPolynomials K F Gamma g) nodes x received hinj prime w agreements
     (by norm_num [w])
     (by norm_num [w,prime])
     (by norm_num [agreements,w,n,errors])
     (by rw [hnodes];norm_num [agreements,n,errors])
     hGdegree hcutDegree
     (fun S hS => hdegree S (hsub hS))
     (fun S hS => hsolutions S (hsub hS))
     (fun S hS => selectedPoint_regular_of_specialization K F
       (fun _:K => S) 0 (hregular S (hsub hS)))
     (fun S hS => (Finset.mem_filter.mp hS).2)
     (fun S hS => hagreement S (hsub hS)) agreementCap
     (fun i hi => agreement_cap K (polynomialEmbedding K) F hY hR hZ
       (x i) (received i))
   have hx0:
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 0=0:=by
     simp [seedlessCut,MvPolynomial.degreeOf_X_of_ne (by decide:(0:Fin 3)≠2)]
   have hx1:
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 1=0:=by
     simp [seedlessCut,MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3)≠2)]
   have hx2:
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 2=1:=by
     simp [seedlessCut]
   have hm0:coordinateMixedDegree (GenericField K) g.1 seedlessCut 0=
       g.1.degreeOf 1:=by
     rw [RCN001.coordinateMixedDegree_zero,hx1,hx2]
     omega
   have hm1:coordinateMixedDegree (GenericField K) g.1 seedlessCut 1=
       g.1.degreeOf 0:=by
     rw [RCN001.coordinateMixedDegree_one,hx0,hx2]
     omega
   have hm2:coordinateMixedDegree (GenericField K) g.1 seedlessCut 2=0:=by
     rw [RCN001.coordinateMixedDegree_two,hx0,hx1]
     omega
   have hcost:
       (∑ i:Fin 3,agreementCap i*
         coordinateMixedDegree (GenericField K) g.1 seedlessCut i)=
       capY*g.1.degreeOf 1+capR*g.1.degreeOf 0:=by
     simp [Fin.sum_univ_succ,agreementCap,hm0,hm1,hm2]
   rw [hnodes,hcost] at hraw
   change (geometricPolynomials K F Gamma g).card*(agreements-w) ≤
     (n-w)*(capY*g.1.degreeOf 1+capR*g.1.degreeOf 0)
   exact hraw
 calc
   Gamma.card*gap ≤
       (∑ g:GeometricFactor K F,
         (geometricPolynomials K F Gamma g).card)*gap:=
     Nat.mul_le_mul_right _
       (card_le_sum_geometricPolynomials K F hF.ne_zero Gamma hsolutions)
   _=∑ g:GeometricFactor K F,
       (geometricPolynomials K F Gamma g).card*gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g:GeometricFactor K F,
       (n-w)*(capY*g.1.degreeOf 1+capR*g.1.degreeOf 0):=
     Finset.sum_le_sum (fun g _ => hcount g)
   _=(n-w)*(capY*(∑ g:GeometricFactor K F,g.1.degreeOf 1)+
       capR*(∑ g:GeometricFactor K F,g.1.degreeOf 0)):=by
     rw [←Finset.mul_sum,Finset.sum_add_distrib,
       ←Finset.mul_sum, ←Finset.mul_sum]
   _ ≤ (n-w)*(capY*F.degreeOf 2+capR*F.degreeOf 1):=by
     apply Nat.mul_le_mul_left
     exact Nat.add_le_add
       (Nat.mul_le_mul_left capY (geometricFactor_sum_degree_le K F hF.ne_zero 1))
       (Nat.mul_le_mul_left capR (geometricFactor_sum_degree_le K F hF.ne_zero 0))
end
end ProximityPrize.SubmissionLower.RCN281
end PackedLegacy_O8
end Compact_PackedLegacy
