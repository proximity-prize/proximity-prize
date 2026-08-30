import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Z9
import ProximityPrize.SubmissionLower.AC
import ProximityPrize.SubmissionLower.B
namespace ProximityPrize.SubmissionLower.RCN221
open scoped Classical BigOperators
open RCN223
open RCN135 RCN136 RCN138
open RCN137 RCN267 RCN081
open RCN238 RCN231 RCN174
open RCN319 RCN243
open RCN222
open RCN266
open RCN159
open RCN156
open RCN275
open RCN234
open RCN095
open RCN214
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
theorem geometricFlag_budgets
   (F:MvPolynomial (Fin 4) K) (hF:F≠0):
   (∑ g:GeometricFactor K F,(geometricFlag K g).zOnly) ≤
       F.degreeOf (3:Fin 4)∧
     (∑ g:GeometricFactor K F,(geometricFlag K g).yz) ≤
       F.degreeOf (1:Fin 4)∧
     (∑ g:GeometricFactor K F,(geometricFlag K g).all) ≤
       F.degreeOf (2:Fin 4):=by
 exact ⟨geometricFactor_sum_degree_le K F hF 2,
   geometricFactor_sum_degree_le K F hF 0,
   geometricFactor_sum_degree_le K F hF 1⟩
theorem original_regular_seed_bound_of_geometric_factor_counts
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hsolutions:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hcount:∀ g:GeometricFactor K F,
     (geometricSeeds K F selected Gamma g).card*gap^2 ≤
       factorRegularLedger (geometricFlag K g)):
   Gamma.card*gap^2 ≤
     factorRegularLedger
       ⟨F.degreeOf (3:Fin 4),F.degreeOf (1:Fin 4),
         F.degreeOf (2:Fin 4)⟩:=by
 have hcover:=card_le_sum_geometricSeeds K F hF.ne_zero selected Gamma
   hsolutions
 have hcaps:=geometricFlag_budgets K F hF.ne_zero
 calc
   Gamma.card*gap^2 ≤
       (∑ g:GeometricFactor K F,
         (geometricSeeds K F selected Gamma g).card)*gap^2:=
     Nat.mul_le_mul_right _ hcover
   _=∑ g:GeometricFactor K F,
       (geometricSeeds K F selected Gamma g).card*gap^2:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g:GeometricFactor K F,
       factorRegularLedger (geometricFlag K g):=
     Finset.sum_le_sum (fun g _↦hcount g)
   _ ≤ factorRegularLedger
       ⟨F.degreeOf (3:Fin 4),F.degreeOf (1:Fin 4),
         F.degreeOf (2:Fin 4)⟩:=
     sum_factorRegularLedger_le_flag (geometricFlag K)
       ⟨F.degreeOf (3:Fin 4),F.degreeOf (1:Fin 4),
         F.degreeOf (2:Fin 4)⟩ hcaps.1 hcaps.2.1 hcaps.2.2
end
end ProximityPrize.SubmissionLower.RCN221
