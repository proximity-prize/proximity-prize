import ProximityPrize.SubmissionLower.PackedLegacyCore1

/-! Packed from ProximityPrize.SubmissionLower.BG. -/
section PackedLegacy_BG
namespace ProximityPrize.SubmissionLower.RCN130
open scoped Classical BigOperators
open RCN081 RCN136 RCN135 RCN137 RCN222 RCN266 RCN167 RCN156 RCN095
open RCN125 (sWeight ysWeight totalWeight)
open RCN071 RCN234 RCN275 RCN159
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
variable {K L:Type} [Field K] [Field L]
def flagFromCaps (total middle inner:ℕ):FlagDegree:=
 ⟨total-middle,middle-inner,inner⟩
theorem flagFromCaps_cumulative (total middle inner:ℕ)
   (hi:inner ≤ middle) (hm:middle ≤ total):
   (flagFromCaps total middle inner).all=inner∧
     (flagFromCaps total middle inner).yz+
       (flagFromCaps total middle inner).all=middle∧
     (flagFromCaps total middle inner).zOnly+
       (flagFromCaps total middle inner).yz+
       (flagFromCaps total middle inner).all=total:=by
 dsimp [flagFromCaps]
 omega
theorem residual_weight_nested (F:MvPolynomial (Fin 4) K):
   wt residualSWeights F ≤ wt residualYSWeights F∧
     wt residualYSWeights F ≤ wt residualTotalWeights F:=by
 constructor
 · apply (weightedTotalDegree_le_iff residualSWeights F _).mpr
   intro d hd
   have h:=MvPolynomial.le_weightedTotalDegree residualYSWeights hd
   rw [weight_fin4] at h ⊢
   simp [wt,residualSWeights,residualYSWeights] at h ⊢
   omega
 · apply (weightedTotalDegree_le_iff residualYSWeights F _).mpr
   intro d hd
   have h:=MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
   rw [weight_fin4] at h ⊢
   simp [wt,residualYSWeights,residualTotalWeights] at h ⊢
   omega
theorem surface_weight_nested (G:MvPolynomial (Fin 3) L):
   MvPolynomial.weightedTotalDegree sWeight G ≤
       MvPolynomial.weightedTotalDegree ysWeight G∧
     MvPolynomial.weightedTotalDegree ysWeight G ≤
       MvPolynomial.weightedTotalDegree totalWeight G:=by
 constructor
 · unfold MvPolynomial.weightedTotalDegree
   apply Finset.sup_le
   intro d hd
   exact (show Finsupp.weight sWeight d ≤ Finsupp.weight ysWeight d by
     rw [RCN372.weight_fin3,RCN372.weight_fin3]
     simp [sWeight,ysWeight]).trans (Finset.le_sup hd)
 · unfold MvPolynomial.weightedTotalDegree
   apply Finset.sup_le
   intro d hd
   exact (show Finsupp.weight ysWeight d ≤ Finsupp.weight totalWeight d by
     rw [RCN372.weight_fin3,RCN372.weight_fin3]
     simp [ysWeight,totalWeight]).trans (Finset.le_sup hd)
def originalCumulativeFlag (F:MvPolynomial (Fin 4) K):FlagDegree:=
 flagFromCaps (wt residualTotalWeights F) (wt residualYSWeights F)
   (wt residualSWeights F)
def surfaceCumulativeFlag (G:MvPolynomial (Fin 3) L):FlagDegree:=
 flagFromCaps (MvPolynomial.weightedTotalDegree totalWeight G)
   (MvPolynomial.weightedTotalDegree ysWeight G)
   (MvPolynomial.weightedTotalDegree sWeight G)
abbrev regularCumulativeFlag (Q:MvPolynomial (Fin 4) K) (R:RegularIndex Q):=
 originalCumulativeFlag R.1
abbrev geometricCumulativeFlag (K:Type) [Field K]
   {F:MvPolynomial (Fin 4) K} (g:GeometricFactor K F):=
 surfaceCumulativeFlag g.1
def supportCumulativeFlag (P:ResidualSupportParameters):FlagDegree:=
 flagFromCaps P.total P.ys P.s
theorem originalCumulativeFlag_cumulative (F:MvPolynomial (Fin 4) K):
   (originalCumulativeFlag F).all=wt residualSWeights F∧
     (originalCumulativeFlag F).yz+(originalCumulativeFlag F).all=
       wt residualYSWeights F∧
     (originalCumulativeFlag F).zOnly+(originalCumulativeFlag F).yz+
       (originalCumulativeFlag F).all=wt residualTotalWeights F:=
 flagFromCaps_cumulative _ _ _ (residual_weight_nested F).1
   (residual_weight_nested F).2
theorem surfaceCumulativeFlag_cumulative (G:MvPolynomial (Fin 3) L):
   (surfaceCumulativeFlag G).all=MvPolynomial.weightedTotalDegree sWeight G∧
     (surfaceCumulativeFlag G).yz+(surfaceCumulativeFlag G).all=
       MvPolynomial.weightedTotalDegree ysWeight G∧
     (surfaceCumulativeFlag G).zOnly+(surfaceCumulativeFlag G).yz+
       (surfaceCumulativeFlag G).all=MvPolynomial.weightedTotalDegree totalWeight G:=
 flagFromCaps_cumulative _ _ _ (surface_weight_nested G).1
   (surface_weight_nested G).2
theorem polynomialIn_surfaceCumulativeFlag (G:MvPolynomial (Fin 3) L):
   PolynomialInFlag (surfaceCumulativeFlag G) G:=by
 intro d hd
 have hs:=MvPolynomial.le_weightedTotalDegree sWeight hd
 have hm:=MvPolynomial.le_weightedTotalDegree ysWeight hd
 have ht:=MvPolynomial.le_weightedTotalDegree totalWeight hd
 rw [RCN372.weight_fin3] at hs hm ht
 simp [sWeight,ysWeight,totalWeight] at hs hm ht
 have hc:=surfaceCumulativeFlag_cumulative G
 change d 1 ≤ (surfaceCumulativeFlag G).all∧
   d 0+d 1 ≤ (surfaceCumulativeFlag G).yz+(surfaceCumulativeFlag G).all∧
   d 0+d 1+d 2 ≤ (surfaceCumulativeFlag G).zOnly+
     (surfaceCumulativeFlag G).yz+(surfaceCumulativeFlag G).all
 rw [hc.2.2,hc.2.1,hc.1]
 exact ⟨hs,hm,ht⟩
theorem surfaceMap_nested_weights_le (phi:Polynomial K →+*L)
   (F:MvPolynomial (Fin 4) K):
   MvPolynomial.weightedTotalDegree sWeight (surfaceMap phi F) ≤
       wt residualSWeights F∧
     MvPolynomial.weightedTotalDegree ysWeight (surfaceMap phi F) ≤
       wt residualYSWeights F∧
     MvPolynomial.weightedTotalDegree totalWeight (surfaceMap phi F) ≤
       wt residualTotalWeights F:=by
 refine ⟨?_,?_,?_⟩
 all_goals
   unfold MvPolynomial.weightedTotalDegree
   apply Finset.sup_le
   intro e he
   obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp (support_surfaceMap_subset phi F he)
   rw [RCN372.weight_fin3]
 · have h:=MvPolynomial.le_weightedTotalDegree residualSWeights hd
   rw [weight_fin4] at h
   simpa [wt,sWeight,residualSWeights,Finsupp.tail_apply] using h
 · have h:=MvPolynomial.le_weightedTotalDegree residualYSWeights hd
   rw [weight_fin4] at h
   simpa [wt,ysWeight,residualYSWeights,Finsupp.tail_apply] using h
 · have h:=MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
   rw [weight_fin4] at h
   simpa [wt,totalWeight,residualTotalWeights,Finsupp.tail_apply] using h
theorem surfaceMap_in_originalCumulativeFlag (phi:Polynomial K →+*L)
   (F:MvPolynomial (Fin 4) K):
   PolynomialInFlag (originalCumulativeFlag F) (surfaceMap phi F):=by
 have hm:=surfaceMap_nested_weights_le phi F
 have hc:=originalCumulativeFlag_cumulative F
 apply (support_subset_flagSupport_iff _ _).mp
 apply support_subset_flagSupport_of_weighted_degrees
 · rw [hc.1];exact hm.1
 · rw [hc.2.1];exact hm.2.1
 · rw [hc.2.2];exact hm.2.2
theorem regularCumulativeFlag_budgets
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {P:ResidualSupportParameters} (H:ResidualSupportData P Q):
   (∑ R:RegularIndex Q,(regularCumulativeFlag Q R).all) ≤ P.s∧
     (∑ R:RegularIndex Q,((regularCumulativeFlag Q R).yz+
       (regularCumulativeFlag Q R).all)) ≤ P.ys∧
     (∑ R:RegularIndex Q,((regularCumulativeFlag Q R).zOnly+
       (regularCumulativeFlag Q R).yz+(regularCumulativeFlag Q R).all)) ≤ P.total:=by
 have hp:=positiveRFactors_product_dvd Q hQ
 have hs:=sum_weightedTotalDegree_le_of_prod_dvd residualSWeights
   (positiveRFactors Q) id Q hQ hp
 have hm:=sum_weightedTotalDegree_le_of_prod_dvd residualYSWeights
   (positiveRFactors Q) id Q hQ hp
 have ht:=sum_weightedTotalDegree_le_of_prod_dvd residualTotalWeights
   (positiveRFactors Q) id Q hQ hp
 refine ⟨?_,?_,?_⟩
 · rw [Finset.sum_congr rfl (fun R _↦(originalCumulativeFlag_cumulative R.1).1),
     Finset.sum_coe_sort]
   exact hs.trans H.s_weight
 · rw [Finset.sum_congr rfl (fun R _↦(originalCumulativeFlag_cumulative R.1).2.1),
     Finset.sum_coe_sort]
   exact hm.trans H.ys_weight
 · rw [Finset.sum_congr rfl (fun R _↦(originalCumulativeFlag_cumulative R.1).2.2),
     Finset.sum_coe_sort]
   exact ht.trans H.total_weight
theorem geometricCumulativeFlag_budgets (F:MvPolynomial (Fin 4) K) (hF:F≠0):
   (∑ g:GeometricFactor K F,(geometricCumulativeFlag K g).all) ≤
       (originalCumulativeFlag F).all∧
     (∑ g:GeometricFactor K F,((geometricCumulativeFlag K g).yz+
       (geometricCumulativeFlag K g).all)) ≤
       (originalCumulativeFlag F).yz+(originalCumulativeFlag F).all∧
     (∑ g:GeometricFactor K F,((geometricCumulativeFlag K g).zOnly+
       (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all)) ≤
       (originalCumulativeFlag F).zOnly+(originalCumulativeFlag F).yz+
         (originalCumulativeFlag F).all:=by
 let phi:=polynomialEmbedding K
 have hSF:=surfaceMap_ne_zero phi (polynomialEmbedding_injective K) F hF
 have hp:=normalizedFactorSet_product_dvd (surfaceMap phi F) hSF
 have hs:=sum_weightedTotalDegree_le_of_prod_dvd_fin3 sWeight
   (surfaceFactors phi F) id (surfaceMap phi F) hSF hp
 have hm:=sum_weightedTotalDegree_le_of_prod_dvd_fin3 ysWeight
   (surfaceFactors phi F) id (surfaceMap phi F) hSF hp
 have ht:=sum_weightedTotalDegree_le_of_prod_dvd_fin3 totalWeight
   (surfaceFactors phi F) id (surfaceMap phi F) hSF hp
 have hmap:=surfaceMap_nested_weights_le phi F
 have hc:=originalCumulativeFlag_cumulative F
 refine ⟨?_,?_,?_⟩
 · rw [Finset.sum_congr rfl (fun g _↦(surfaceCumulativeFlag_cumulative g.1).1),
     Finset.sum_coe_sort,hc.1]
   exact hs.trans hmap.1
 · rw [Finset.sum_congr rfl (fun g _↦(surfaceCumulativeFlag_cumulative g.1).2.1),
     Finset.sum_coe_sort,hc.2.1]
   exact hm.trans hmap.2.1
 · rw [Finset.sum_congr rfl (fun g _↦(surfaceCumulativeFlag_cumulative g.1).2.2),
     Finset.sum_coe_sort,hc.2.2]
   exact ht.trans hmap.2.2
theorem geometricCumulativeFlag_le_support
   (F:MvPolynomial (Fin 4) K) (hF:F≠0)
   {P:ResidualSupportParameters} (H:ResidualSupportData P F)
   (g:GeometricFactor K F):
   (geometricCumulativeFlag K g).all ≤ P.s∧
     (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ P.ys∧
     (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+
       (geometricCumulativeFlag K g).all ≤ P.total:=by
 have hb:=geometricCumulativeFlag_budgets F hF
 have hc:=originalCumulativeFlag_cumulative F
 rw [hc.2.2,hc.2.1,hc.1] at hb
 refine ⟨?_,?_,?_⟩
 · exact (Finset.single_le_sum (fun _ _↦Nat.zero_le _)
     (Finset.mem_univ g)).trans (hb.1.trans H.s_weight)
 · exact (Finset.single_le_sum (fun _ _↦Nat.zero_le _)
     (Finset.mem_univ g)).trans (hb.2.1.trans H.ys_weight)
 · exact (Finset.single_le_sum (fun _ _↦Nat.zero_le _)
     (Finset.mem_univ g)).trans (hb.2.2.trans H.total_weight)
theorem originalCumulativeFlag_all (F:MvPolynomial (Fin 4) K):
   (originalCumulativeFlag F).all=F.degreeOf 2:=by
 change MvPolynomial.weightedTotalDegree residualSWeights F=_
 have hw:residualSWeights=Pi.single (2:Fin 4) 1:=by
   funext i
   fin_cases i <;> simp [residualSWeights]
 rw [hw,MvPolynomial.weightedTotalDegree_piSingle]
theorem regularCumulativeFlag_positive
   (Q:MvPolynomial (Fin 4) K) (R:RegularIndex Q):
   0 < (regularCumulativeFlag Q R).all:=by
 rw [originalCumulativeFlag_all]
 exact (positiveRFactors_spec Q R.1 R.2).2.2
theorem surfaceCumulativeFlag_all (G:MvPolynomial (Fin 3) L):
   (surfaceCumulativeFlag G).all=G.degreeOf 1:=by
 change MvPolynomial.weightedTotalDegree sWeight G=_
 have hw:sWeight=Pi.single (1:Fin 3) 1:=by
   funext i
   fin_cases i <;> simp [sWeight]
 rw [hw,MvPolynomial.weightedTotalDegree_piSingle]
def reflagResidualStage {Iota:Type} {phi:Polynomial K →+*L}
   {Gamma:Finset K} {x:Iota → K} {p e d:ℕ} [CharP L p]
   {oldFlag newFlag:FlagDegree} {support:ResidualSupportParameters}
   (S:ResidualStage phi Gamma x p e oldFlag d support)
   (hflag:PolynomialInFlag newFlag S.G):
   ResidualStage phi Gamma x p e newFlag d support:=
 { S with flag_support:=hflag}
end
end ProximityPrize.SubmissionLower.RCN130
end PackedLegacy_BG

/-! Packed from ProximityPrize.SubmissionLower.AJ. -/
section PackedLegacy_AJ
namespace ProximityPrize.SubmissionLower.RCN302
open RCN100 RCN119
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def prime:ℕ:=2130706433
def agreements:ℕ:=182278
def errors:ℕ:=n-agreements
def gap:ℕ:=agreements-w
structure Profile where
 multiplicity:ℕ
 seedCap:ℕ
 slopeCap:ℕ
 deriving DecidableEq
def profileA:Profile:=⟨34,20000,10⟩
def profileB:Profile:=⟨68,900,21⟩
def profileC:Profile:=⟨37,42000,9⟩
namespace Profile
def weightedCap (P:Profile):ℕ:=P.multiplicity*agreements
def totalCap (P:Profile):ℕ:=P.seedCap
def yCap (P:Profile):ℕ:=(P.weightedCap-1)/w
def characteristicCap (P:Profile):ℕ:=
 (2*P.slopeCap-1)*P.weightedCap
def coefficients (P:Profile):ℕ:=
 coefficientCount P.weightedCap w P.seedCap P.slopeCap
def localRank (P:Profile):ℕ:=
 localRankBound P.multiplicity P.seedCap P.slopeCap
def totalRank (P:Profile):ℕ:=n*P.localRank
def nullity (P:Profile):ℕ:=P.coefficients-P.totalRank
end Profile
theorem coefficientCount_eq_sum_range_of_weighted_cutoff
   (D w L s t:ℕ) (ht:t ≤ L+1) (hD:D ≤ w*t):
   coefficientCount D w L s=
     ∑ i∈Finset.range t,
       ∑ j∈Finset.range (s+1),
         (L+1-i-j)*(D-w*i-(w-1)*j):=by
 have hsplit:L+1=t+(L+1-t):=by omega
 unfold coefficientCount
 rw [hsplit,Finset.sum_range_add]
 have htail:
     (∑ x∈Finset.range (L+1-t),
       ∑ j∈Finset.range (s+1),
         (t+(L+1-t)-(t+x)-j)*
           (D-w*(t+x)-(w-1)*j))=0:=by
   apply Finset.sum_eq_zero
   intro i hi
   apply Finset.sum_eq_zero
   intro j hj
   have hti:t ≤ t+i:=by omega
   have hzero:D-w*(t+i)=0:=
     Nat.sub_eq_zero_of_le (hD.trans (Nat.mul_le_mul_left w hti))
   simp [hzero]
 rw [htail,add_zero]
theorem base_values:
   errors=79866∧gap=51207:=by
 norm_num [errors,gap,n,agreements,w]
theorem profileA_coefficients_exact:
   profileA.coefficients=26510739472987:=by
 change coefficientCount (34*182278) 131071 20000 10=26510739472987
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   (34*182278) 131071 20000 10 48 (by norm_num) (by norm_num)]
 decide
theorem profileA_localRank_exact:profileA.localRank=101130370:=by
 change localRankBound 34 20000 10=101130370
 decide
theorem profileA_values:
   profileA.weightedCap=6197452∧profileA.yCap=47∧
     profileA.localRank=101130370∧
     profileA.coefficients=26510739472987∧
     profileA.nullity=19759707:=by
 refine ⟨by norm_num [Profile.weightedCap,profileA,agreements],
   by norm_num [Profile.yCap,Profile.weightedCap,profileA,agreements,w],
   profileA_localRank_exact,profileA_coefficients_exact,?_⟩
 rw [Profile.nullity,Profile.totalRank,profileA_coefficients_exact,
   profileA_localRank_exact]
 norm_num [n]
theorem profileB_coefficients_exact:
   profileB.coefficients=8952917932750:=by
 change coefficientCount (68*182278) 131071 900 21=8952917932750
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   (68*182278) 131071 900 21 95 (by norm_num) (by norm_num)]
 decide
theorem profileB_localRank_exact:profileB.localRank=34148169:=by
 change localRankBound 68 900 21=34148169
 decide
theorem profileB_values:
   profileB.weightedCap=12394904∧profileB.yCap=94∧
     profileB.localRank=34148169∧
     profileB.coefficients=8952917932750∧
     profileB.nullity=1180318414:=by
 refine ⟨by norm_num [Profile.weightedCap,profileB,agreements],
   by norm_num [Profile.yCap,Profile.weightedCap,profileB,agreements,w],
   profileB_localRank_exact,profileB_coefficients_exact,?_⟩
 rw [Profile.nullity,Profile.totalRank,profileB_coefficients_exact,
   profileB_localRank_exact]
 norm_num [n]
theorem profileC_coefficients_exact:
   profileC.coefficients=62185590423245:=by
 change coefficientCount (37*182278) 131071 42000 9=62185590423245
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   (37*182278) 131071 42000 9 52 (by norm_num) (by norm_num)]
 decide
theorem profileC_localRank_exact:profileC.localRank=237219085:=by
 change localRankBound 37 42000 9=237219085
 decide
theorem profileC_values:
   profileC.weightedCap=6744286∧profileC.yCap=51∧
     profileC.localRank=237219085∧
     profileC.coefficients=62185590423245∧
     profileC.nullity=30605005:=by
 refine ⟨by norm_num [Profile.weightedCap,profileC,agreements],
   by norm_num [Profile.yCap,Profile.weightedCap,profileC,agreements,w],
   profileC_localRank_exact,profileC_coefficients_exact,?_⟩
 rw [Profile.nullity,Profile.totalRank,profileC_coefficients_exact,
   profileC_localRank_exact]
 norm_num [n]
theorem interpolation_gates:
     profileA.totalRank < profileA.coefficients∧
     profileB.totalRank < profileB.coefficients∧
     profileC.totalRank < profileC.coefficients:=by
 simp only [Profile.totalRank]
 rw [profileA_coefficients_exact,profileA_localRank_exact,
   profileB_coefficients_exact,profileB_localRank_exact,
   profileC_coefficients_exact,profileC_localRank_exact]
 norm_num [n]
theorem characteristic_gates:
   profileA.characteristicCap < prime∧
     (2*profileA.slopeCap-1)*profileA.seedCap < prime∧
     profileA.slopeCap < prime∧
   profileB.characteristicCap < prime∧
     (2*profileB.slopeCap-1)*profileB.seedCap < prime∧
     profileB.slopeCap < prime∧
   profileC.characteristicCap < prime∧
     (2*profileC.slopeCap-1)*profileC.seedCap < prime∧
     profileC.slopeCap < prime:=by
 norm_num [Profile.characteristicCap,Profile.weightedCap,profileA,profileB,
   profileC,agreements,prime]
theorem meet_caps:
   (min profileA.multiplicity profileB.multiplicity,
       min profileA.seedCap profileB.seedCap,
       min profileA.slopeCap profileB.slopeCap)=(34,900,10)∧
     (min (min profileA.multiplicity profileB.multiplicity) profileC.multiplicity,
       min (min profileA.seedCap profileB.seedCap) profileC.seedCap,
       min (min profileA.slopeCap profileB.slopeCap) profileC.slopeCap)=
         (34,900,9):=by
 norm_num [profileA,profileB,profileC]
theorem middle_support_gates:
   profileA.weightedCap+profileA.slopeCap ≤ w*(profileA.yCap+1)∧
     profileB.weightedCap+profileB.slopeCap ≤ w*(profileB.yCap+1)∧
     profileC.weightedCap+profileC.slopeCap ≤ w*(profileC.yCap+1):=by
 norm_num [Profile.weightedCap,Profile.yCap,profileA,profileB,profileC,
   agreements,w]
end ProximityPrize.SubmissionLower.RCN302
end PackedLegacy_AJ

/-! Packed from ProximityPrize.SubmissionLower.L1. -/
section PackedLegacy_L1
namespace ProximityPrize.SubmissionLower.RCN180
open scoped BigOperators
open RCN100 RCN081 RCN234 RCN156
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
def reconstructLinear (D w L s:ℕ) :
   (CoefficientIndex D w L s → K) →ₗ[K] Poly4 K where
 toFun:=reconstruct K D w L s
 map_add' θ η:=by
   classical
   simp [reconstruct,Finset.sum_add_distrib]
 map_smul' a θ:=by
   classical
   rw [show reconstruct K D w L s (a • θ) =
       ∑ c:CoefficientIndex D w L s,
         MvPolynomial.monomial (columnExponent c) (a * θ c) by
     simp [reconstruct]]
   change (∑ c:CoefficientIndex D w L s,
     MvPolynomial.monomial (columnExponent c) (a * θ c)) =
     a • (∑ c:CoefficientIndex D w L s,
       MvPolynomial.monomial (columnExponent c) (θ c))
   rw [Finset.smul_sum]
   apply Finset.sum_congr rfl
   intro c hc
   rw [MvPolynomial.smul_monomial]
   simp [smul_eq_mul]
theorem reconstructLinear_injective (D w L s:ℕ) :
   Function.Injective (reconstructLinear (K:=K) D w L s) :=
 reconstruct_injective K D w L s
def reconstructIntoBox (D w L s:ℕ) :
   (CoefficientIndex D w L s → K) →ₗ[K]
     globalCoefficientBox K D w L s :=
 LinearMap.codRestrict (globalCoefficientBox K D w L s)
   (reconstructLinear (K:=K) D w L s)
   (reconstruct_mem_globalCoefficientBox K D w L s)
theorem reconstructIntoBox_injective (D w L s:ℕ) :
   Function.Injective (reconstructIntoBox (K:=K) D w L s):=by
 intro θ η h
 apply reconstructLinear_injective (K:=K) D w L s
 exact congrArg Subtype.val h
def columnIndexOfExponent {D w L s:ℕ} (d:Fin 4 →₀ ℕ)
   (hd:d ∈ globalExponents D w L s):CoefficientIndex D w L s:=by
 rcases hd with ⟨hL,hs,hD⟩
 have hi:d 1 < L + 1:=by omega
 have hj:d 2 < s + 1:=by omega
 have hz:d 3 < L + 1 - d 1 - d 2:=by omega
 have hx:d 0 < D - w * d 1 - (w - 1) * d 2:=by omega
 exact ⟨⟨d 1,hi⟩,⟨⟨d 2,hj⟩,⟨⟨d 3,hz⟩,⟨d 0,hx⟩⟩⟩⟩
theorem columnExponent_columnIndexOfExponent {D w L s:ℕ}
   (d:Fin 4 →₀ ℕ) (hd:d ∈ globalExponents D w L s) :
   columnExponent (columnIndexOfExponent d hd) = d:=by
 rcases hd with ⟨hL,hs,hD⟩
 ext i
 fin_cases i <;> simp [columnIndexOfExponent]
def encodeBox {D w L s:ℕ} (Q:globalCoefficientBox K D w L s) :
   CoefficientIndex D w L s → K :=
 fun c ↦ MvPolynomial.coeff (columnExponent c) Q.1
theorem reconstruct_encodeBox {D w L s:ℕ}
   (Q:globalCoefficientBox K D w L s) :
   reconstruct K D w L s (encodeBox Q) = Q.1:=by
 classical
 ext d
 by_cases hd:d ∈ globalExponents D w L s
 · let c:=columnIndexOfExponent d hd
   have hc:columnExponent c = d :=
     columnExponent_columnIndexOfExponent d hd
   rw [← hc,reconstruct_coeff]
   rfl
 · have hQ:MvPolynomial.coeff d Q.1 = 0:=by
     by_contra hn
     exact hd (Q.2 (MvPolynomial.mem_support_iff.mpr hn))
   have hRmem:=reconstruct_mem_globalCoefficientBox K D w L s (encodeBox Q)
   have hR:MvPolynomial.coeff d
       (reconstruct K D w L s (encodeBox Q)) = 0:=by
     by_contra hn
     exact hd (hRmem (MvPolynomial.mem_support_iff.mpr hn))
   rw [hQ,hR]
theorem reconstructIntoBox_surjective (D w L s:ℕ) :
   Function.Surjective (reconstructIntoBox (K:=K) D w L s):=by
 intro Q
 refine ⟨encodeBox Q,?_⟩
 apply Subtype.ext
 exact reconstruct_encodeBox Q
def reconstructBoxEquiv (D w L s:ℕ) :
   (CoefficientIndex D w L s → K) ≃ₗ[K]
     globalCoefficientBox K D w L s :=
 LinearEquiv.ofBijective (reconstructIntoBox (K:=K) D w L s)
   ⟨reconstructIntoBox_injective (K:=K) D w L s,
     reconstructIntoBox_surjective (K:=K) D w L s⟩
instance globalCoefficientBoxFinite (D w L s:ℕ) :
   Module.Finite K (globalCoefficientBox K D w L s) :=
 Module.Finite.of_surjective (reconstructIntoBox (K:=K) D w L s)
   (reconstructIntoBox_surjective (K:=K) D w L s)
theorem globalCoefficientBox_finrank (D w L s:ℕ) :
   Module.finrank K (globalCoefficientBox K D w L s) =
     coefficientCount D w L s:=by
 rw [← coefficient_index_card D w L s,
   ← Module.finrank_fintype_fun_eq_card K]
 exact LinearEquiv.finrank_eq (reconstructBoxEquiv (K:=K) D w L s).symm
theorem mem_flagGlobalCoefficientBox_iff (Q:Poly4 K)
   (D w L s:ℕ) (hD:0 < D) :
   Q ∈ globalCoefficientBox K D w L s ↔
     wt residualTotalWeights Q ≤ L ∧
     wt residualSWeights Q ≤ s ∧
     wt (contactWeights w) Q ≤ D - 1:=by
 constructor
 · intro h
   refine ⟨?_,?_,?_⟩
   · apply (weightedTotalDegree_le_iff residualTotalWeights Q L).mpr
     intro d hd
     have hq:=h hd
     rw [weight_fin4]
     simp [residualTotalWeights]
     exact hq.1
   · apply (weightedTotalDegree_le_iff residualSWeights Q s).mpr
     intro d hd
     have hq:=h hd
     rw [weight_fin4]
     simp [residualSWeights]
     exact hq.2.1
   · apply (weightedTotalDegree_le_iff (contactWeights w) Q (D - 1)).mpr
     intro d hd
     rw [contact_weight]
     have hq:=(h hd).2.2
     omega
 · rintro ⟨ht,hs,hc⟩ d hd
   have hdt:=(MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans ht
   have hds:=(MvPolynomial.le_weightedTotalDegree residualSWeights hd).trans hs
   have hdc:=(MvPolynomial.le_weightedTotalDegree (contactWeights w) hd).trans hc
   rw [weight_fin4] at hdt hds
   rw [contact_weight] at hdc
   simp [residualTotalWeights] at hdt
   simp [residualSWeights] at hds
   exact ⟨hdt,hds,by omega⟩
theorem residualYS_mul_le_contact_add_slope (Q:Poly4 K)
   (w:ℕ) (hw:1 ≤ w) :
   w * wt residualYSWeights Q ≤
     wt (contactWeights w) Q + wt residualSWeights Q:=by
 by_cases hQ:Q = 0
 · subst Q
   simp [wt,MvPolynomial.weightedTotalDegree]
 obtain ⟨d,hd,heq⟩:=Finset.exists_mem_eq_sup Q.support
   (MvPolynomial.support_nonempty.mpr hQ)
   (Finsupp.weight residualYSWeights)
 have hc:=MvPolynomial.le_weightedTotalDegree (contactWeights w) hd
 have hs:=MvPolynomial.le_weightedTotalDegree residualSWeights hd
 change wt residualYSWeights Q = Finsupp.weight residualYSWeights d at heq
 rw [weight_fin4] at heq hs
 rw [contact_weight] at hc
 simp [residualYSWeights] at heq
 simp [residualSWeights] at hs
 simp only [residualYSWeights,residualSWeights]
 rw [heq]
 have hwsub:w - 1 + 1 = w:=by omega
 have hwmul:w * d 2 = (w - 1) * d 2 + d 2:=by
   calc
     w * d 2 = ((w - 1) + 1) * d 2:=by rw [hwsub]
     _ = (w - 1) * d 2 + d 2:=by ring
 calc
   w * (d 1 + d 2) ≤
       (d 0 + w * d 1 + (w - 1) * d 2) + d 2:=by
     rw [Nat.mul_add,hwmul]
     omega
   _ ≤ wt (contactWeights w) Q + wt residualSWeights Q :=
     Nat.add_le_add hc hs
theorem quotient_mem_flagGlobalCoefficientBox_of_mul_eq
   (Q H R:Poly4 K) (D w L s contactLower totalLower slopeLower:ℕ)
   (hQ:Q ≠ 0) (hH:H ≠ 0) (hR:R ≠ 0)
   (hbox:Q ∈ globalCoefficientBox K D w L s)
   (heq:Q = H * R)
   (hcontact:contactLower ≤ wt (contactWeights w) H)
   (htotal:totalLower ≤ wt residualTotalWeights H)
   (hslope:slopeLower ≤ wt residualSWeights H) :
   R ∈ globalCoefficientBox K (D - contactLower) w
     (L - totalLower) (s - slopeLower):=by
 have hD:0 < D:=by
   rcases MvPolynomial.support_nonempty.mpr hQ with ⟨d,hd⟩
   have:=(hbox hd).2.2
   omega
 have hc:=(mem_flagGlobalCoefficientBox_iff Q D w L s hD).mp hbox
 simp only [wt] at hc hcontact htotal hslope
 have hmulT:=weightedTotalDegree_mul residualTotalWeights H R hH hR
 have hmulS:=weightedTotalDegree_mul residualSWeights H R hH hR
 have hmulC:=weightedTotalDegree_mul (contactWeights w) H R hH hR
 rw [← heq] at hmulT hmulS hmulC
 have hDq:0 < D - contactLower:=by omega
 apply (mem_flagGlobalCoefficientBox_iff R (D - contactLower) w
   (L - totalLower) (s - slopeLower) hDq).mpr
 simp only [wt]
 omega
theorem mem_flagGlobalCoefficientBox_of_dvd
   (F Q:Poly4 K) (D w L s:ℕ)
   (hQ:Q ≠ 0) (hdiv:F ∣ Q)
   (hbox:Q ∈ globalCoefficientBox K D w L s) :
   F ∈ globalCoefficientBox K D w L s:=by
 have hD:0 < D:=by
   rcases MvPolynomial.support_nonempty.mpr hQ with ⟨d,hd⟩
   have:=(hbox hd).2.2
   omega
 have hc:=(mem_flagGlobalCoefficientBox_iff Q D w L s hD).mp hbox
 apply (mem_flagGlobalCoefficientBox_iff F D w L s hD).mpr
 exact ⟨(weightedTotalDegree_le_of_dvd residualTotalWeights F Q hdiv hQ).trans hc.1,
   (weightedTotalDegree_le_of_dvd residualSWeights F Q hdiv hQ).trans hc.2.1,
   (weightedTotalDegree_le_of_dvd (contactWeights w) F Q hdiv hQ).trans hc.2.2⟩
section CommonGCD
local instance:StrongNormalizationMonoid (Poly4 K) :=
 UniqueFactorizationMonoid.strongNormalizationMonoid
local instance:NormalizedGCDMonoid (Poly4 K) :=
 UniqueFactorizationMonoid.toNormalizedGCDMonoid (Poly4 K)
def commonGCD {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] (b:Module.Basis ι K V):Poly4 K :=
 Finset.univ.gcd (fun i ↦ reconstruct K D w L s (b i).1)
theorem commonGCD_dvd_basis {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] (b:Module.Basis ι K V) (i:ι) :
   commonGCD V b ∣ reconstruct K D w L s (b i).1:=by
 exact Finset.gcd_dvd (Finset.mem_univ i)
theorem commonGCD_ne_zero {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] [Nonempty ι] (b:Module.Basis ι K V) :
   commonGCD V b ≠ 0:=by
 rw [commonGCD,Finset.gcd_ne_zero_iff]
 let i:ι:=Classical.choice inferInstance
 refine ⟨i,Finset.mem_univ i,?_⟩
 apply reconstruct_ne_zero K D w L s
 intro hi
 apply b.ne_zero i
 exact Subtype.ext hi
theorem commonGCD_dvd {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] (b:Module.Basis ι K V) (v:V) :
   commonGCD V b ∣ reconstruct K D w L s v.1:=by
 rw [← b.sum_repr v]
 simp only [Submodule.coe_sum,Submodule.coe_smul]
 change commonGCD V b ∣
   reconstructLinear (K:=K) D w L s
     (∑ i,(b.repr v) i • (b i).1)
 rw [map_sum]
 apply Finset.dvd_sum
 intro i hi
 rw [map_smul,MvPolynomial.smul_eq_C_mul]
 exact dvd_mul_of_dvd_right (commonGCD_dvd_basis V b i) _
theorem dvd_commonGCD_iff {D w L s:ℕ}
   (V:Submodule K (CoefficientIndex D w L s → K))
   {ι:Type*} [Fintype ι] (b:Module.Basis ι K V) (F:Poly4 K) :
   F ∣ commonGCD V b ↔
     ∀ v:V,F ∣ reconstruct K D w L s v.1:=by
 constructor
 · intro hF v
   exact hF.trans (commonGCD_dvd V b v)
 · intro hF
   apply Finset.dvd_gcd_iff.mpr
   intro i hi
   exact hF (b i)
end CommonGCD
section LinearQuotient
variable {V:Type*} [AddCommGroup V] [Module K V]
def quotientPolynomial (recon:V →ₗ[K] Poly4 K) (H:Poly4 K)
   (hdiv:∀ v,H ∣ recon v) (v:V):Poly4 K :=
 Classical.choose (hdiv v)
theorem recon_eq_mul_quotientPolynomial
   (recon:V →ₗ[K] Poly4 K) (H:Poly4 K)
   (hdiv:∀ v,H ∣ recon v) (v:V) :
   recon v = H * quotientPolynomial recon H hdiv v :=
 Classical.choose_spec (hdiv v)
def quotientLinear (recon:V →ₗ[K] Poly4 K) (H:Poly4 K)
   (hH:H ≠ 0) (hdiv:∀ v,H ∣ recon v):V →ₗ[K] Poly4 K where
 toFun:=quotientPolynomial recon H hdiv
 map_add' v z:=by
   apply mul_left_cancel₀ hH
   rw [← recon_eq_mul_quotientPolynomial recon H hdiv (v + z),map_add,
     recon_eq_mul_quotientPolynomial recon H hdiv v,
     recon_eq_mul_quotientPolynomial recon H hdiv z,mul_add]
 map_smul' a v:=by
   apply mul_left_cancel₀ hH
   rw [← recon_eq_mul_quotientPolynomial recon H hdiv (a • v),map_smul,
     recon_eq_mul_quotientPolynomial recon H hdiv v]
   simp only [MvPolynomial.smul_eq_C_mul]
   ac_rfl
theorem quotientLinear_injective
   (recon:V →ₗ[K] Poly4 K) (hrecon:Function.Injective recon)
   (H:Poly4 K) (hH:H ≠ 0) (hdiv:∀ v,H ∣ recon v) :
   Function.Injective (quotientLinear recon H hH hdiv):=by
 intro v z hvz
 apply hrecon
 rw [recon_eq_mul_quotientPolynomial recon H hdiv v,
   recon_eq_mul_quotientPolynomial recon H hdiv z]
 exact congrArg (fun Q:Poly4 K ↦ H * Q) hvz
theorem finrank_le_quotient_box
   (recon:V →ₗ[K] Poly4 K) (hrecon:Function.Injective recon)
   (H:Poly4 K) (hH:H ≠ 0) (hdiv:∀ v,H ∣ recon v)
   (W:Submodule K (Poly4 K)) [Module.Finite K W]
   (hmem:∀ v,quotientPolynomial recon H hdiv v ∈ W) :
   Module.finrank K V ≤ Module.finrank K W:=by
 let q:V →ₗ[K] W:=LinearMap.codRestrict W
   (quotientLinear recon H hH hdiv) hmem
 apply LinearMap.finrank_le_finrank_of_injective (f:=q)
 intro v z hvz
 apply quotientLinear_injective recon hrecon H hH hdiv
 exact congrArg Subtype.val hvz
end LinearQuotient
section ConstraintKernel
open RCN119
variable {I:Type*} [Fintype I]
abbrev ConstraintKernel (D w L s m:ℕ)
   (nodes u₀ u₁:I → K) :=
 LinearMap.ker (constraintMap K D w L s m nodes u₀ u₁)
def kernelReconstructLinear (D w L s m:ℕ)
   (nodes u₀ u₁:I → K) :
   ConstraintKernel (K:=K) D w L s m nodes u₀ u₁ →ₗ[K] Poly4 K :=
 (reconstructLinear (K:=K) D w L s).comp
   (ConstraintKernel (K:=K) D w L s m nodes u₀ u₁).subtype
@[simp] theorem kernelReconstructLinear_apply (D w L s m:ℕ)
   (nodes u₀ u₁:I → K)
   (v:ConstraintKernel (K:=K) D w L s m nodes u₀ u₁) :
   kernelReconstructLinear (K:=K) D w L s m nodes u₀ u₁ v =
     reconstruct K D w L s v.1:=rfl
theorem kernelReconstructLinear_injective (D w L s m:ℕ)
   (nodes u₀ u₁:I → K) :
   Function.Injective
     (kernelReconstructLinear (K:=K) D w L s m nodes u₀ u₁):=by
 intro v z hvz
 apply Subtype.ext
 apply reconstructLinear_injective (K:=K) D w L s
 exact hvz
private theorem nat_sub_le_of_add_eq_of_le {R K C B:ℕ}
   (hsum:R + K = C) (hr:R ≤ B):C - B ≤ K:=by
 apply Nat.sub_le_of_le_add
 rw [← hsum]
 simpa [Nat.add_comm] using Nat.add_le_add_right hr K
theorem constraintKernel_finrank_lower_bound (D w L s m:ℕ)
   (nodes u₀ u₁:I → K) :
   coefficientCount D w L s - Fintype.card I * localRankBound m L s ≤
     Module.finrank K
       (ConstraintKernel (K:=K) D w L s m nodes u₀ u₁):=by
 let f:=constraintMap K D w L s m nodes u₀ u₁
 have hsum:=f.finrank_range_add_finrank_ker
 have hrange:Module.finrank K f.range ≤
     Fintype.card I * localRankBound m L s :=
   f.range.finrank_le.trans (globalTarget_finrank_le K m L s)
 have hdom:Module.finrank K (CoefficientIndex D w L s → K) =
     coefficientCount D w L s:=by
   rw [Module.finrank_fintype_fun_eq_card K,coefficient_index_card]
 dsimp [f] at hsum hrange
 rw [hdom] at hsum
 dsimp [ConstraintKernel] at hsum ⊢
 exact nat_sub_le_of_add_eq_of_le hsum hrange
theorem common_divisor_dimension_obstruction
   (D w L s m Dq Lq sq:ℕ) (nodes u₀ u₁:I → K)
   (H:Poly4 K) (hH:H ≠ 0)
   (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m nodes u₀ u₁,
     H ∣ kernelReconstructLinear (K:=K) D w L s m nodes u₀ u₁ v)
   (hqbox:∀ v:ConstraintKernel (K:=K) D w L s m nodes u₀ u₁,
     quotientPolynomial
       (kernelReconstructLinear (K:=K) D w L s m nodes u₀ u₁)
       H hdiv v ∈ globalCoefficientBox K Dq w Lq sq) :
   coefficientCount D w L s - Fintype.card I * localRankBound m L s ≤
     coefficientCount Dq w Lq sq:=by
 have hlo:=constraintKernel_finrank_lower_bound
   (K:=K) D w L s m nodes u₀ u₁
 have hhi:=finrank_le_quotient_box
   (kernelReconstructLinear (K:=K) D w L s m nodes u₀ u₁)
   (kernelReconstructLinear_injective (K:=K) D w L s m nodes u₀ u₁)
   H hH hdiv (globalCoefficientBox K Dq w Lq sq) hqbox
 rw [globalCoefficientBox_finrank] at hhi
 exact hlo.trans hhi
end ConstraintKernel
namespace Numeric6733
open RCN119 RCN100 RCN302
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
theorem profileA_localRank_exact :
   localRankBound 41 1003041 12 = 8671143936:=by
 decide
theorem profileB_localRank_exact :
   localRankBound 81 1242 25 = 79112293:=by
 decide
theorem profileB_smallCoefficient_exact :
   coefficientCount 14746212 131071 1 25 = 58722707:=by
 decide
theorem coefficientCount_mono_D_s
   {D D' w L s s':ℕ} (hD:D ≤ D') (hs:s ≤ s') :
   coefficientCount D w L s ≤ coefficientCount D' w L s':=by
 unfold coefficientCount
 apply Finset.sum_le_sum
 intro i hi
 calc
   (∑ j ∈ Finset.range (s + 1),
     (L + 1 - i - j) * (D - w * i - (w - 1) * j)) ≤
     ∑ j ∈ Finset.range (s + 1),
       (L + 1 - i - j) * (D' - w * i - (w - 1) * j):=by
         apply Finset.sum_le_sum
         intro j hj
         gcongr
   _ ≤ ∑ j ∈ Finset.range (s' + 1),
       (L + 1 - i - j) * (D' - w * i - (w - 1) * j) :=
     Finset.sum_le_sum_of_subset_of_nonneg
       (Finset.range_mono (Nat.succ_le_succ hs)) (by simp)
theorem profileA_full_nullity_exact :
   coefficientCount 7464132 131071 1003041 12 -
       262144 * localRankBound 41 1003041 12 = 505079935113:=by
 rw [profileA_localRank_exact]
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   7464132 131071 1003041 12 57 (by decide) (by decide)]
 decide
theorem profileA_quotient_cap_exact :
   coefficientCount 255239 131071 1002986 12 = 505079933175:=by
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   255239 131071 1002986 12 2 (by decide) (by decide)]
 decide
theorem profileA_dimension_strata (r:ℕ) (hr:r ≤ 12) :
   coefficientCount 7464132 131071 1003041 12 -
       262144 * localRankBound 41 1003041 12 >
     coefficientCount (7464132 - (55 * 131071 - r)) 131071
       (1003041 - 55) (12 - r):=by
 rw [profileA_full_nullity_exact]
 have hmono:=coefficientCount_mono_D_s
   (D:=7464132 - (55 * 131071 - r)) (D':=255239)
   (w:=131071) (L:=1002986) (s:=12 - r) (s':=12)
   (by omega) (by omega)
 rw [profileA_quotient_cap_exact] at hmono
 norm_num at hmono ⊢
 omega
theorem profileB_full_nullity_exact :
   coefficientCount 14746212 131071 1242 25 -
       262144 * localRankBound 81 1242 25 = 82451746:=by
 rw [profileB_localRank_exact]
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   14746212 131071 1242 25 113 (by decide) (by decide)]
 decide
theorem profileB_dimension_stratum :
   coefficientCount 14746212 131071 1242 25 -
       262144 * localRankBound 81 1242 25 >
     coefficientCount 14746212 131071 1 25:=by
 rw [profileB_full_nullity_exact,profileB_smallCoefficient_exact]
 decide
end Numeric6733
namespace Caps6733
open ProximityPrize.Benchmark RCN119 RCN100 RCN130 Numeric6733
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev AKernel (u₀ u₁:IRSProfile.Index → IRSProfile.Field) :=
 ConstraintKernel (K:=IRSProfile.Field)
   7464132 131071 1003041 12 41 IRSProfile.domain u₀ u₁
theorem profileA_commonGCD_ys_le
   (u₀ u₁:IRSProfile.Index → IRSProfile.Field)
   {ι:Type*} [Fintype ι] [Nonempty ι]
   (b:Module.Basis ι IRSProfile.Field (AKernel u₀ u₁)) :
   wt residualYSWeights
     (commonGCD (D:=7464132) (w:=131071) (L:=1003041) (s:=12)
       (AKernel u₀ u₁) b) ≤ 54:=by
 let H:Poly4 IRSProfile.Field :=
   commonGCD (D:=7464132) (w:=131071) (L:=1003041) (s:=12)
     (AKernel u₀ u₁) b
 have hH:H ≠ 0:=commonGCD_ne_zero
   (D:=7464132) (w:=131071) (L:=1003041) (s:=12)
   (AKernel u₀ u₁) b
 have hdiv:∀ v:AKernel u₀ u₁,
     H ∣ kernelReconstructLinear (K:=IRSProfile.Field)
       7464132 131071 1003041 12 41 IRSProfile.domain u₀ u₁ v:=by
   intro v
   rw [kernelReconstructLinear_apply]
   exact
     (commonGCD_dvd (D:=7464132) (w:=131071)
       (L:=1003041) (s:=12) (AKernel u₀ u₁) b v)
 let i:ι:=Classical.choice inferInstance
 let Qi:=reconstruct IRSProfile.Field
   7464132 131071 1003041 12 (b i).1
 have hQi:Qi ≠ 0:=by
   change reconstruct IRSProfile.Field 7464132 131071 1003041 12 (b i).1 ≠ 0
   apply reconstruct_ne_zero IRSProfile.Field 7464132 131071 1003041 12
   intro hbzero
   apply b.ne_zero i
   exact Subtype.ext hbzero
 have hQibox:Qi ∈ globalCoefficientBox IRSProfile.Field
     7464132 131071 1003041 12:=by
   change reconstruct IRSProfile.Field 7464132 131071 1003041 12 (b i).1 ∈ _
   exact reconstruct_mem_globalCoefficientBox IRSProfile.Field _ _ _ _ _
 have hHbox:H ∈ globalCoefficientBox IRSProfile.Field
     7464132 131071 1003041 12 :=
   mem_flagGlobalCoefficientBox_of_dvd H Qi
     7464132 131071 1003041 12 hQi
     (commonGCD_dvd_basis (D:=7464132) (w:=131071)
       (L:=1003041) (s:=12) (AKernel u₀ u₁) b i) hQibox
 have hHcaps:=(mem_flagGlobalCoefficientBox_iff H
   7464132 131071 1003041 12 (by decide)).mp hHbox
 by_contra hnot
 change ¬ wt residualYSWeights H ≤ 54 at hnot
 have hys:55 ≤ wt residualYSWeights H:=by omega
 let r:=wt residualSWeights H
 have hr:r ≤ 12:=hHcaps.2.1
 have htotal:55 ≤ wt residualTotalWeights H :=
   hys.trans (residual_weight_nested H).2
 have hrel:=residualYS_mul_le_contact_add_slope H 131071 (by decide)
 have hcontact:55 * 131071 - r ≤ wt (contactWeights 131071) H:=by
   dsimp [r]
   omega
 have hqbox:∀ v:AKernel u₀ u₁,
     quotientPolynomial
       (kernelReconstructLinear (K:=IRSProfile.Field)
         7464132 131071 1003041 12 41 IRSProfile.domain u₀ u₁)
       H hdiv v ∈ globalCoefficientBox IRSProfile.Field
         (7464132 - (55 * 131071 - r)) 131071
         (1003041 - 55) (12 - r):=by
   intro v
   by_cases hv:v = 0
   · subst v
     have hqzero:quotientPolynomial
         (kernelReconstructLinear (K:=IRSProfile.Field)
           7464132 131071 1003041 12 41 IRSProfile.domain u₀ u₁)
         H hdiv 0 = 0:=by
       apply mul_left_cancel₀ hH
       rw [← recon_eq_mul_quotientPolynomial
         (kernelReconstructLinear (K:=IRSProfile.Field)
           7464132 131071 1003041 12 41 IRSProfile.domain u₀ u₁)
         H hdiv 0]
       simp
     rw [hqzero]
     exact (globalCoefficientBox IRSProfile.Field _ _ _ _).zero_mem
   · let recon:=kernelReconstructLinear (K:=IRSProfile.Field)
         7464132 131071 1003041 12 41 IRSProfile.domain u₀ u₁
     let R:=quotientPolynomial recon H hdiv v
     have hQv:recon v ≠ 0:=by
       intro hz
       apply hv
       apply kernelReconstructLinear_injective (K:=IRSProfile.Field)
         7464132 131071 1003041 12 41 IRSProfile.domain u₀ u₁
       simpa only [map_zero] using hz
     have hR:R ≠ 0:=by
       intro hz
       apply hQv
       rw [recon_eq_mul_quotientPolynomial recon H hdiv v]
       change H * R = 0
       rw [hz,mul_zero]
     have hReconBox:recon v ∈ globalCoefficientBox IRSProfile.Field
         7464132 131071 1003041 12:=by
       rw [kernelReconstructLinear_apply]
       exact reconstruct_mem_globalCoefficientBox IRSProfile.Field
         7464132 131071 1003041 12 v.1
     exact quotient_mem_flagGlobalCoefficientBox_of_mul_eq
       (recon v) H R 7464132 131071 1003041 12
       (55 * 131071 - r) 55 r hQv hH hR hReconBox
       (recon_eq_mul_quotientPolynomial recon H hdiv v)
       hcontact htotal (le_refl r)
 have hobs:=common_divisor_dimension_obstruction
   (K:=IRSProfile.Field) 7464132 131071 1003041 12 41
   (7464132 - (55 * 131071 - r)) (1003041 - 55) (12 - r)
   IRSProfile.domain u₀ u₁ H hH hdiv hqbox
 rw [show Fintype.card IRSProfile.Index = 262144 by
   norm_num [IRSProfile.Index]] at hobs
 exact (Nat.not_le_of_gt (profileA_dimension_strata r hr)) hobs
abbrev BKernel (u₀ u₁:IRSProfile.Index → IRSProfile.Field) :=
 ConstraintKernel (K:=IRSProfile.Field)
   14746212 131071 1242 25 81 IRSProfile.domain u₀ u₁
theorem profileB_commonGCD_total_le
   (u₀ u₁:IRSProfile.Index → IRSProfile.Field)
   {ι:Type*} [Fintype ι] [Nonempty ι]
   (b:Module.Basis ι IRSProfile.Field (BKernel u₀ u₁)) :
   wt residualTotalWeights
     (commonGCD (D:=14746212) (w:=131071) (L:=1242) (s:=25)
       (BKernel u₀ u₁) b) ≤ 1240:=by
 let H:Poly4 IRSProfile.Field :=
   commonGCD (D:=14746212) (w:=131071) (L:=1242) (s:=25)
     (BKernel u₀ u₁) b
 have hH:H ≠ 0:=commonGCD_ne_zero
   (D:=14746212) (w:=131071) (L:=1242) (s:=25)
   (BKernel u₀ u₁) b
 have hdiv:∀ v:BKernel u₀ u₁,
     H ∣ kernelReconstructLinear (K:=IRSProfile.Field)
       14746212 131071 1242 25 81 IRSProfile.domain u₀ u₁ v:=by
   intro v
   rw [kernelReconstructLinear_apply]
   exact commonGCD_dvd (D:=14746212) (w:=131071)
     (L:=1242) (s:=25) (BKernel u₀ u₁) b v
 by_contra hnot
 change ¬ wt residualTotalWeights H ≤ 1240 at hnot
 have htotal:1241 ≤ wt residualTotalWeights H:=by omega
 have hqbox:∀ v:BKernel u₀ u₁,
     quotientPolynomial
       (kernelReconstructLinear (K:=IRSProfile.Field)
         14746212 131071 1242 25 81 IRSProfile.domain u₀ u₁)
       H hdiv v ∈ globalCoefficientBox IRSProfile.Field
         14746212 131071 1 25:=by
   intro v
   by_cases hv:v = 0
   · subst v
     have hqzero:quotientPolynomial
         (kernelReconstructLinear (K:=IRSProfile.Field)
           14746212 131071 1242 25 81 IRSProfile.domain u₀ u₁)
         H hdiv 0 = 0:=by
       apply mul_left_cancel₀ hH
       rw [← recon_eq_mul_quotientPolynomial
         (kernelReconstructLinear (K:=IRSProfile.Field)
           14746212 131071 1242 25 81 IRSProfile.domain u₀ u₁)
         H hdiv 0]
       simp
     rw [hqzero]
     exact (globalCoefficientBox IRSProfile.Field _ _ _ _).zero_mem
   · let recon:=kernelReconstructLinear (K:=IRSProfile.Field)
         14746212 131071 1242 25 81 IRSProfile.domain u₀ u₁
     let R:=quotientPolynomial recon H hdiv v
     have hQv:recon v ≠ 0:=by
       intro hz
       apply hv
       apply kernelReconstructLinear_injective (K:=IRSProfile.Field)
         14746212 131071 1242 25 81 IRSProfile.domain u₀ u₁
       simpa only [map_zero] using hz
     have hR:R ≠ 0:=by
       intro hz
       apply hQv
       rw [recon_eq_mul_quotientPolynomial recon H hdiv v]
       change H * R = 0
       rw [hz,mul_zero]
     have hReconBox:recon v ∈ globalCoefficientBox IRSProfile.Field
         14746212 131071 1242 25:=by
       rw [kernelReconstructLinear_apply]
       exact reconstruct_mem_globalCoefficientBox IRSProfile.Field
         14746212 131071 1242 25 v.1
     exact quotient_mem_flagGlobalCoefficientBox_of_mul_eq
       (recon v) H R 14746212 131071 1242 25
       0 1241 0 hQv hH hR hReconBox
       (recon_eq_mul_quotientPolynomial recon H hdiv v)
       (Nat.zero_le _) htotal (Nat.zero_le _)
 have hobs:=common_divisor_dimension_obstruction
   (K:=IRSProfile.Field) 14746212 131071 1242 25 81
   14746212 1 25 IRSProfile.domain u₀ u₁ H hH hdiv hqbox
 rw [show Fintype.card IRSProfile.Index = 262144 by
   norm_num [IRSProfile.Index]] at hobs
 exact (Nat.not_le_of_gt profileB_dimension_stratum) hobs
end Caps6733
namespace Numeric6734
open RCN119 RCN100 RCN302
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
theorem profileA_localRank_exact :
   localRankBound 42 84439 12 = 769336295:=by
 decide
theorem profileB_localRank_exact :
   localRankBound 81 1262 25 = 80423213:=by
 decide
theorem profileA_full_nullity_exact :
   coefficientCount 7645764 131071 84439 12 -
       262144 * localRankBound 42 84439 12 = 81098093102:=by
 rw [profileA_localRank_exact]
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   7645764 131071 84439 12 59 (by decide) (by decide)]
 decide
theorem profileA_ys_quotient_cap_exact :
   coefficientCount 305800 131071 84383 12 = 66345127211:=by
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   305800 131071 84383 12 3 (by decide) (by decide)]
 decide
theorem profileA_corner_quotient_exact :
   coefficientCount 436871 131071 84384 0 = 81098093098:=by
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   436871 131071 84384 0 4 (by decide) (by decide)]
 decide
theorem profileB_full_nullity_exact :
   coefficientCount 14745402 131071 1262 25 -
       262144 * localRankBound 81 1262 25 = 46988916:=by
 rw [profileB_localRank_exact]
 rw [coefficientCount_eq_sum_range_of_weighted_cutoff
   14745402 131071 1262 25 113 (by decide) (by decide)]
 decide
theorem profileB_quotient_exact :
   coefficientCount 14745402 131071 0 25 = 14745402:=by
 decide
theorem profileA_ys_dimension_strata (r:ℕ) (hr:r ≤ 12) :
   coefficientCount 7645764 131071 84439 12 -
       262144 * localRankBound 42 84439 12 >
     coefficientCount (7645764 - (56 * 131071 - r)) 131071
       (84439 - 56) (12 - r):=by
 rw [profileA_full_nullity_exact]
 have hmono:=Numeric6733.coefficientCount_mono_D_s
   (D:=7645764 - (56 * 131071 - r)) (D':=305800)
   (w:=131071) (L:=84383) (s:=12 - r) (s':=12)
   (by omega) (by omega)
 rw [profileA_ys_quotient_cap_exact] at hmono
 norm_num at hmono ⊢
 omega
theorem profileA_corner_dimension :
   coefficientCount 7645764 131071 84439 12 -
       262144 * localRankBound 42 84439 12 >
     coefficientCount (7645764 - (55 * 131071 - 12)) 131071
       (84439 - 55) (12 - 12):=by
 rw [profileA_full_nullity_exact]
 norm_num
 rw [profileA_corner_quotient_exact]
 decide
theorem profileB_dimension :
   coefficientCount 14745402 131071 1262 25 -
       262144 * localRankBound 81 1262 25 >
     coefficientCount 14745402 131071 (1262 - 1262) 25:=by
 rw [profileB_full_nullity_exact]
 norm_num
 rw [profileB_quotient_exact]
 decide
end Numeric6734
namespace Caps6734
open ProximityPrize.Benchmark RCN119 RCN100 RCN130 Numeric6734
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev AKernel (u₀ u₁:IRSProfile.Index → IRSProfile.Field) :=
 ConstraintKernel (K:=IRSProfile.Field)
   7645764 131071 84439 12 42 IRSProfile.domain u₀ u₁
abbrev BKernel (u₀ u₁:IRSProfile.Index → IRSProfile.Field) :=
 ConstraintKernel (K:=IRSProfile.Field)
   14745402 131071 1262 25 81 IRSProfile.domain u₀ u₁
private theorem commonGCD_data
   (D L s m:ℕ) (u₀ u₁:IRSProfile.Index → IRSProfile.Field)
   {ι:Type*} [Fintype ι] [Nonempty ι]
   (b:Module.Basis ι IRSProfile.Field
     (ConstraintKernel (K:=IRSProfile.Field)
       D 131071 L s m IRSProfile.domain u₀ u₁)) :
   let V:=ConstraintKernel (K:=IRSProfile.Field)
     D 131071 L s m IRSProfile.domain u₀ u₁
   let H:=commonGCD (D:=D) (w:=131071) (L:=L) (s:=s) V b
   H ≠ 0 ∧
     (∀ v:V,H ∣ kernelReconstructLinear (K:=IRSProfile.Field)
       D 131071 L s m IRSProfile.domain u₀ u₁ v) ∧
     H ∈ globalCoefficientBox IRSProfile.Field D 131071 L s:=by
 dsimp only
 let V:=ConstraintKernel (K:=IRSProfile.Field)
   D 131071 L s m IRSProfile.domain u₀ u₁
 let H:=commonGCD (D:=D) (w:=131071) (L:=L) (s:=s) V b
 have hH:H ≠ 0:=commonGCD_ne_zero V b
 have hdiv:∀ v:V,H ∣ kernelReconstructLinear (K:=IRSProfile.Field)
     D 131071 L s m IRSProfile.domain u₀ u₁ v:=by
   intro v
   rw [kernelReconstructLinear_apply]
   exact commonGCD_dvd V b v
 let i:ι:=Classical.choice inferInstance
 let Qi:=reconstruct IRSProfile.Field D 131071 L s (b i).1
 have hQi:Qi ≠ 0:=by
   apply reconstruct_ne_zero IRSProfile.Field D 131071 L s
   intro hbzero
   apply b.ne_zero i
   exact Subtype.ext hbzero
 have hQibox:Qi ∈ globalCoefficientBox IRSProfile.Field D 131071 L s :=
   reconstruct_mem_globalCoefficientBox IRSProfile.Field D 131071 L s (b i).1
 have hHbox:H ∈ globalCoefficientBox IRSProfile.Field D 131071 L s :=
   mem_flagGlobalCoefficientBox_of_dvd H Qi D 131071 L s hQi
     (commonGCD_dvd_basis V b i) hQibox
 exact ⟨hH,hdiv,hHbox⟩
private theorem quotient_box_of_commonGCD
   (D L s m contactLower totalLower slopeLower:ℕ)
   (u₀ u₁:IRSProfile.Index → IRSProfile.Field)
   {ι:Type*} [Fintype ι] [Nonempty ι]
   (b:Module.Basis ι IRSProfile.Field
     (ConstraintKernel (K:=IRSProfile.Field)
       D 131071 L s m IRSProfile.domain u₀ u₁))
   (hcontact:contactLower ≤ wt (contactWeights 131071)
     (commonGCD (D:=D) (w:=131071) (L:=L) (s:=s)
       (ConstraintKernel (K:=IRSProfile.Field)
         D 131071 L s m IRSProfile.domain u₀ u₁) b))
   (htotal:totalLower ≤ wt residualTotalWeights
     (commonGCD (D:=D) (w:=131071) (L:=L) (s:=s)
       (ConstraintKernel (K:=IRSProfile.Field)
         D 131071 L s m IRSProfile.domain u₀ u₁) b))
   (hslope:slopeLower ≤ wt residualSWeights
     (commonGCD (D:=D) (w:=131071) (L:=L) (s:=s)
       (ConstraintKernel (K:=IRSProfile.Field)
         D 131071 L s m IRSProfile.domain u₀ u₁) b)) :
   let V:=ConstraintKernel (K:=IRSProfile.Field)
     D 131071 L s m IRSProfile.domain u₀ u₁
   let H:=commonGCD (D:=D) (w:=131071) (L:=L) (s:=s) V b
   ∀ v:V,quotientPolynomial
     (kernelReconstructLinear (K:=IRSProfile.Field)
       D 131071 L s m IRSProfile.domain u₀ u₁) H
     (fun v ↦ commonGCD_dvd V b v) v ∈
       globalCoefficientBox IRSProfile.Field (D - contactLower) 131071
         (L - totalLower) (s - slopeLower):=by
 dsimp only
 intro v
 let V:=ConstraintKernel (K:=IRSProfile.Field)
   D 131071 L s m IRSProfile.domain u₀ u₁
 let H:=commonGCD (D:=D) (w:=131071) (L:=L) (s:=s) V b
 let recon:=kernelReconstructLinear (K:=IRSProfile.Field)
   D 131071 L s m IRSProfile.domain u₀ u₁
 let hdiv:∀ z:V,H ∣ recon z:=by
   intro z
   rw [kernelReconstructLinear_apply]
   exact commonGCD_dvd V b z
 have hH:H ≠ 0:=commonGCD_ne_zero V b
 by_cases hv:v = 0
 · subst v
   have hqzero:quotientPolynomial recon H hdiv 0 = 0:=by
     apply mul_left_cancel₀ hH
     rw [← recon_eq_mul_quotientPolynomial recon H hdiv 0]
     simp
   rw [hqzero]
   exact (globalCoefficientBox IRSProfile.Field _ _ _ _).zero_mem
 · let R:=quotientPolynomial recon H hdiv v
   have hQv:recon v ≠ 0:=by
     intro hz
     apply hv
     apply kernelReconstructLinear_injective (K:=IRSProfile.Field)
       D 131071 L s m IRSProfile.domain u₀ u₁
     simpa only [map_zero] using hz
   have hR:R ≠ 0:=by
     intro hz
     apply hQv
     rw [recon_eq_mul_quotientPolynomial recon H hdiv v]
     change H * R = 0
     rw [hz,mul_zero]
   have hReconBox:recon v ∈ globalCoefficientBox IRSProfile.Field
       D 131071 L s:=by
     rw [kernelReconstructLinear_apply]
     exact reconstruct_mem_globalCoefficientBox IRSProfile.Field D 131071 L s v.1
   exact quotient_mem_flagGlobalCoefficientBox_of_mul_eq
     (recon v) H R D 131071 L s contactLower totalLower slopeLower
     hQv hH hR hReconBox (recon_eq_mul_quotientPolynomial recon H hdiv v)
     hcontact htotal hslope
theorem profileA_commonGCD_ys_le
   (u₀ u₁:IRSProfile.Index → IRSProfile.Field)
   {ι:Type*} [Fintype ι] [Nonempty ι]
   (b:Module.Basis ι IRSProfile.Field (AKernel u₀ u₁)) :
   wt residualYSWeights
     (commonGCD (D:=7645764) (w:=131071) (L:=84439) (s:=12)
       (AKernel u₀ u₁) b) ≤ 55:=by
 let H:=commonGCD (D:=7645764) (w:=131071) (L:=84439) (s:=12)
   (AKernel u₀ u₁) b
 obtain ⟨hH,hdiv,hHbox⟩:=commonGCD_data 7645764 84439 12 42 u₀ u₁ b
 have hHcaps:=(mem_flagGlobalCoefficientBox_iff H
   7645764 131071 84439 12 (by decide)).mp hHbox
 by_contra hnot
 change ¬ wt residualYSWeights H ≤ 55 at hnot
 have hys:56 ≤ wt residualYSWeights H:=by omega
 let r:=wt residualSWeights H
 have hr:r ≤ 12:=hHcaps.2.1
 have htotal:56 ≤ wt residualTotalWeights H :=
   hys.trans (residual_weight_nested H).2
 have hrel:=residualYS_mul_le_contact_add_slope H 131071 (by decide)
 have hcontact:56 * 131071 - r ≤ wt (contactWeights 131071) H:=by
   dsimp [r]
   omega
 have hqbox:=quotient_box_of_commonGCD 7645764 84439 12 42
   (56 * 131071 - r) 56 r u₀ u₁ b hcontact htotal (le_refl r)
 have hobs:=common_divisor_dimension_obstruction
   (K:=IRSProfile.Field) 7645764 131071 84439 12 42
   (7645764 - (56 * 131071 - r)) (84439 - 56) (12 - r)
   IRSProfile.domain u₀ u₁ H hH hdiv hqbox
 rw [show Fintype.card IRSProfile.Index = 262144 by
   norm_num [IRSProfile.Index]] at hobs
 exact (Nat.not_le_of_gt (profileA_ys_dimension_strata r hr)) hobs
theorem profileA_commonGCD_corner
   (u₀ u₁:IRSProfile.Index → IRSProfile.Field)
   {ι:Type*} [Fintype ι] [Nonempty ι]
   (b:Module.Basis ι IRSProfile.Field (AKernel u₀ u₁)) :
   wt residualYSWeights
       (commonGCD (D:=7645764) (w:=131071) (L:=84439) (s:=12)
         (AKernel u₀ u₁) b) ≤ 54 ∨
     wt residualSWeights
       (commonGCD (D:=7645764) (w:=131071) (L:=84439) (s:=12)
         (AKernel u₀ u₁) b) ≤ 11:=by
 let H:=commonGCD (D:=7645764) (w:=131071) (L:=84439) (s:=12)
   (AKernel u₀ u₁) b
 obtain ⟨hH,hdiv,hHbox⟩:=commonGCD_data 7645764 84439 12 42 u₀ u₁ b
 have hHcaps:=(mem_flagGlobalCoefficientBox_iff H
   7645764 131071 84439 12 (by decide)).mp hHbox
 by_contra hnot
 change ¬ (wt residualYSWeights H ≤ 54 ∨
   wt residualSWeights H ≤ 11) at hnot
 push_neg at hnot
 have hys:55 ≤ wt residualYSWeights H:=by omega
 have hslope:12 ≤ wt residualSWeights H:=by omega
 have htotal:55 ≤ wt residualTotalWeights H :=
   hys.trans (residual_weight_nested H).2
 have hrel:=residualYS_mul_le_contact_add_slope H 131071 (by decide)
 have hcontact:55 * 131071 - 12 ≤ wt (contactWeights 131071) H:=by
   omega
 have hqbox:=quotient_box_of_commonGCD 7645764 84439 12 42
   (55 * 131071 - 12) 55 12 u₀ u₁ b hcontact htotal hslope
 have hobs:=common_divisor_dimension_obstruction
   (K:=IRSProfile.Field) 7645764 131071 84439 12 42
   (7645764 - (55 * 131071 - 12)) (84439 - 55) (12 - 12)
   IRSProfile.domain u₀ u₁ H hH hdiv hqbox
 rw [show Fintype.card IRSProfile.Index = 262144 by
   norm_num [IRSProfile.Index]] at hobs
 exact (Nat.not_le_of_gt profileA_corner_dimension) hobs
theorem profileB_commonGCD_total_le
   (u₀ u₁:IRSProfile.Index → IRSProfile.Field)
   {ι:Type*} [Fintype ι] [Nonempty ι]
   (b:Module.Basis ι IRSProfile.Field (BKernel u₀ u₁)) :
   wt residualTotalWeights
     (commonGCD (D:=14745402) (w:=131071) (L:=1262) (s:=25)
       (BKernel u₀ u₁) b) ≤ 1261:=by
 let H:=commonGCD (D:=14745402) (w:=131071) (L:=1262) (s:=25)
   (BKernel u₀ u₁) b
 obtain ⟨hH,hdiv,_hHbox⟩:=commonGCD_data 14745402 1262 25 81 u₀ u₁ b
 by_contra hnot
 change ¬ wt residualTotalWeights H ≤ 1261 at hnot
 have htotal:1262 ≤ wt residualTotalWeights H:=by omega
 have hqbox:=quotient_box_of_commonGCD 14745402 1262 25 81
   0 1262 0 u₀ u₁ b (Nat.zero_le _) htotal (Nat.zero_le _)
 have hobs:=common_divisor_dimension_obstruction
   (K:=IRSProfile.Field) 14745402 131071 1262 25 81
   14745402 (1262 - 1262) 25 IRSProfile.domain u₀ u₁ H hH hdiv hqbox
 rw [show Fintype.card IRSProfile.Index = 262144 by
   norm_num [IRSProfile.Index]] at hobs
 exact (Nat.not_le_of_gt profileB_dimension) hobs
end Caps6734
end
end ProximityPrize.SubmissionLower.RCN180
end PackedLegacy_L1

/-! Packed from ProximityPrize.SubmissionLower.ContactOrderBridge. -/
section PackedLegacy_ContactOrderBridge
namespace ProximityPrize.SubmissionLower.ContactOrderBridge
open scoped BigOperators Pointwise
open RCN081 RCN119 RCN100 RCN122
noncomputable section
section MinimumWeight
variable {K σ:Type*} [Field K]
def AtLeast (w:σ → ℕ) (n:ℕ) (P:MvPolynomial σ K):Prop :=
  ∀ d ∈ P.support, n ≤ Finsupp.weight w d
theorem atLeast_zero (w:σ → ℕ) (P:MvPolynomial σ K):AtLeast w 0 P:=by
  intro d hd
  exact Nat.zero_le _
theorem zero_atLeast (w:σ → ℕ) (n:ℕ):AtLeast w n (0:MvPolynomial σ K):=by
  intro d hd
  simp at hd
theorem atLeast_mono (w:σ → ℕ) {m n:ℕ} {P:MvPolynomial σ K}
    (hmn:m ≤ n) (hP:AtLeast w n P):AtLeast w m P:=by
  intro d hd
  exact hmn.trans (hP d hd)
theorem atLeast_add (w:σ → ℕ) {n:ℕ} {P Q:MvPolynomial σ K}
    (hP:AtLeast w n P) (hQ:AtLeast w n Q):AtLeast w n (P + Q):=by
  change P ∈ MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d} at hP
  change Q ∈ MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d} at hQ
  exact (MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d}).add_mem hP hQ
theorem atLeast_sub (w:σ → ℕ) {n:ℕ} {P Q:MvPolynomial σ K}
    (hP:AtLeast w n P) (hQ:AtLeast w n Q):AtLeast w n (P - Q):=by
  change P ∈ MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d} at hP
  change Q ∈ MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d} at hQ
  exact (MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d}).sub_mem hP hQ
theorem atLeast_mul (w:σ → ℕ) {m n:ℕ} {P Q:MvPolynomial σ K}
    (hP:AtLeast w m P) (hQ:AtLeast w n Q):AtLeast w (m + n) (P * Q):=by
  have hset:{d:σ →₀ ℕ | m ≤ Finsupp.weight w d} +
      {d:σ →₀ ℕ | n ≤ Finsupp.weight w d} ⊆
      {d:σ →₀ ℕ | m + n ≤ Finsupp.weight w d}:=by
    rintro _ ⟨d, hd, e, he, rfl⟩
    simpa only [Set.mem_setOf_eq, map_add] using Nat.add_le_add hd he
  change P ∈ MvPolynomial.restrictSupport K {d | m ≤ Finsupp.weight w d} at hP
  change Q ∈ MvPolynomial.restrictSupport K {d | n ≤ Finsupp.weight w d} at hQ
  apply MvPolynomial.restrictSupport_mono (R:=K) hset
  rw [MvPolynomial.restrictSupport_add]
  exact Submodule.mul_mem_mul hP hQ
theorem atLeast_X (w:σ → ℕ) (i:σ) :
    AtLeast w (w i) (MvPolynomial.X i:MvPolynomial σ K):=by
  classical
  intro d hd
  have he:d = Finsupp.single i 1 :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst d
  simp only [Finsupp.weight_single, one_nsmul, le_refl]
theorem atLeast_pderiv (w:σ → ℕ) (i:σ) {n:ℕ} {P:MvPolynomial σ K}
    (hP:AtLeast w n P):AtLeast w (n - w i) (MvPolynomial.pderiv i P):=by
  classical
  intro d hd
  have hbefore:d + Finsupp.single i 1 ∈ P.support:=by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    have hne:=MvPolynomial.mem_support_iff.mp hd
    apply hne
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
  have h:=hP _ hbefore
  simp only [map_add, Finsupp.weight_single, one_nsmul] at h
  omega
theorem component_ne_zero_iff (w:σ → ℕ) (n:ℕ) (P:MvPolynomial σ K) :
    MvPolynomial.weightedHomogeneousComponent w n P ≠ 0 ↔
      ∃ d ∈ P.support, Finsupp.weight w d = n:=by
  classical
  constructor
  · intro h
    obtain ⟨d, hd⟩:=MvPolynomial.exists_coeff_ne_zero h
    rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hd
    split_ifs at hd with hw
    · exact ⟨d, MvPolynomial.mem_support_iff.mpr hd, hw⟩
    · exact False.elim (hd rfl)
  · rintro ⟨d, hd, hw⟩ hz
    have hc:=congrArg (MvPolynomial.coeff d) hz
    rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos hw,
      MvPolynomial.coeff_zero] at hc
    exact MvPolynomial.mem_support_iff.mp hd hc
theorem initial_mul (w:σ → ℕ) {m n:ℕ} {P Q:MvPolynomial σ K}
    (hP:AtLeast w m P) (hQ:AtLeast w n Q) :
    MvPolynomial.weightedHomogeneousComponent w (m + n) (P * Q) =
      MvPolynomial.weightedHomogeneousComponent w m P *
        MvPolynomial.weightedHomogeneousComponent w n Q:=by
  classical
  letI:DecidableEq σ:=Classical.decEq σ
  letI:DecidableEq K:=Classical.decEq K
  letI:DecidableEq (σ →₀ ℕ):=Classical.decEq (σ →₀ ℕ)
  ext d
  rw [MvPolynomial.coeff_weightedHomogeneousComponent,
    MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  split_ifs with hd
  · apply Finset.sum_congr rfl
    rintro ⟨e, f⟩ hef
    simp only [MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases he:MvPolynomial.coeff e P = 0
    · simp [he]
    by_cases hf:MvPolynomial.coeff f Q = 0
    · simp [hf]
    have hew:=hP e (MvPolynomial.mem_support_iff.mpr he)
    have hfw:=hQ f (MvPolynomial.mem_support_iff.mpr hf)
    have hef':e + f = d:=Finset.mem_antidiagonal.mp hef
    have hsum:Finsupp.weight w e + Finsupp.weight w f = m + n:=by
      rw [← map_add, hef', hd]
    have hem:Finsupp.weight w e = m:=by omega
    have hfn:Finsupp.weight w f = n:=by omega
    simp [hem, hfn]
  · symm
    apply Finset.sum_eq_zero
    rintro ⟨e, f⟩ hef
    simp only [MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases he:Finsupp.weight w e = m
    · by_cases hf:Finsupp.weight w f = n
      · exfalso
        apply hd
        have hef':e + f = d:=Finset.mem_antidiagonal.mp hef
        rw [← hef', map_add, he, hf]
      · simp [he, hf]
    · simp [he]
def ExactOrder (w:σ → ℕ) (n:ℕ) (P:MvPolynomial σ K):Prop :=
  AtLeast w n P ∧ MvPolynomial.weightedHomogeneousComponent w n P ≠ 0
theorem exists_exactOrder (w:σ → ℕ) (P:MvPolynomial σ K) (hP:P ≠ 0) :
    ∃ n, ExactOrder w n P:=by
  classical
  have hex:∃ n, ∃ d ∈ P.support, Finsupp.weight w d = n:=by
    obtain ⟨d, hd⟩:=MvPolynomial.support_nonempty.mpr hP
    exact ⟨_, d, hd, rfl⟩
  refine ⟨Nat.find hex, ?_, (component_ne_zero_iff w _ P).mpr (Nat.find_spec hex)⟩
  intro d hd
  exact Nat.find_min' hex ⟨d, hd, rfl⟩
theorem exactOrder_unique (w:σ → ℕ) {m n:ℕ} {P:MvPolynomial σ K}
    (hm:ExactOrder w m P) (hn:ExactOrder w n P):m = n:=by
  obtain ⟨d, hd, hdm⟩:=(component_ne_zero_iff w m P).mp hm.2
  obtain ⟨e, he, hen⟩:=(component_ne_zero_iff w n P).mp hn.2
  have hnm:=hn.1 d hd
  have hmn:=hm.1 e he
  omega
def order (w:σ → ℕ) (P:MvPolynomial σ K):ℕ:=by
  classical
  exact if hP:P = 0 then 0 else Classical.choose (exists_exactOrder w P hP)
theorem exactOrder_order (w:σ → ℕ) (P:MvPolynomial σ K) (hP:P ≠ 0) :
    ExactOrder w (order w P) P:=by
  simp only [order, dif_neg hP]
  exact Classical.choose_spec (exists_exactOrder w P hP)
theorem atLeast_iff_le_order (w:σ → ℕ) (n:ℕ) (P:MvPolynomial σ K)
    (hP:P ≠ 0):AtLeast w n P ↔ n ≤ order w P:=by
  have ho:=exactOrder_order w P hP
  constructor
  · intro hn
    obtain ⟨d, hd, hw⟩:=(component_ne_zero_iff w _ P).mp ho.2
    simpa only [hw] using hn d hd
  · intro hn
    exact atLeast_mono w hn ho.1
theorem exactOrder_mul (w:σ → ℕ) {m n:ℕ} {P Q:MvPolynomial σ K}
    (hP:ExactOrder w m P) (hQ:ExactOrder w n Q) :
    ExactOrder w (m + n) (P * Q):=by
  refine ⟨atLeast_mul w hP.1 hQ.1, ?_⟩
  rw [initial_mul w hP.1 hQ.1]
  exact mul_ne_zero hP.2 hQ.2
theorem order_mul (w:σ → ℕ) (P Q:MvPolynomial σ K) (hP:P ≠ 0) (hQ:Q ≠ 0) :
    order w (P * Q) = order w P + order w Q:=by
  exact exactOrder_unique w (exactOrder_order w (P * Q) (mul_ne_zero hP hQ))
    (exactOrder_mul w (exactOrder_order w P hP) (exactOrder_order w Q hQ))
theorem colon_iff (w:σ → ℕ) (m:ℕ) (F P:MvPolynomial σ K) (hF:F ≠ 0) :
    AtLeast w m (F * P) ↔ AtLeast w (m - order w F) P:=by
  by_cases hP:P = 0
  · subst P
    simp only [mul_zero]
    exact iff_of_true (zero_atLeast w m) (zero_atLeast w _)
  · rw [atLeast_iff_le_order w m (F * P) (mul_ne_zero hF hP),
      atLeast_iff_le_order w _ P hP, order_mul w F P hF hP]
    omega
end MinimumWeight
section LocalCoordinates
variable (K:Type*) [Field K]
abbrev Poly4:=MvPolynomial (Fin 4) K
def localWeights:Fin 4 → ℕ:=![1, 2, 0, 0]
def localVariables (x u₀ u₁:K):Fin 4 → Poly4 K :=
  ![MvPolynomial.X 0 + MvPolynomial.C x,
    MvPolynomial.C u₀ + MvPolynomial.X 3 * MvPolynomial.C u₁ +
      MvPolynomial.X 2 * MvPolynomial.X 0 + MvPolynomial.X 1,
    MvPolynomial.X 2, MvPolynomial.X 3]
def inverseVariables (x u₀ u₁:K):Fin 4 → Poly4 K :=
  ![MvPolynomial.X 0 - MvPolynomial.C x,
    MvPolynomial.X 1 - (MvPolynomial.C u₀ + MvPolynomial.X 3 * MvPolynomial.C u₁) -
      MvPolynomial.X 2 * (MvPolynomial.X 0 - MvPolynomial.C x),
    MvPolynomial.X 2, MvPolynomial.X 3]
def localize (x u₀ u₁:K):Poly4 K →ₐ[K] Poly4 K :=
  MvPolynomial.aeval (localVariables K x u₀ u₁)
def unlocalize (x u₀ u₁:K):Poly4 K →ₐ[K] Poly4 K :=
  MvPolynomial.aeval (inverseVariables K x u₀ u₁)
theorem unlocalize_comp_localize (x u₀ u₁:K) :
    (unlocalize K x u₀ u₁).comp (localize K x u₀ u₁) = AlgHom.id K (Poly4 K):=by
  ext i
  fin_cases i <;> simp [localize, unlocalize, localVariables, inverseVariables] <;> ring
theorem localize_injective (x u₀ u₁:K):Function.Injective (localize K x u₀ u₁):=by
  intro P Q h
  have hinv (P:Poly4 K):unlocalize K x u₀ u₁ (localize K x u₀ u₁ P) = P :=
    DFunLike.congr_fun (unlocalize_comp_localize K x u₀ u₁) P
  simpa only [hinv] using congrArg (unlocalize K x u₀ u₁) h
theorem localize_ne_zero (x u₀ u₁:K) (P:Poly4 K) (hP:P ≠ 0) :
    localize K x u₀ u₁ P ≠ 0:=by
  intro h
  apply hP
  apply localize_injective K x u₀ u₁
  simpa only [map_zero] using h
def ContactAtLeast (x u₀ u₁:K) (m:ℕ) (P:Poly4 K):Prop :=
  AtLeast localWeights m (localize K x u₀ u₁ P)
def contactOrder (x u₀ u₁:K) (P:Poly4 K):ℕ :=
  order localWeights (localize K x u₀ u₁ P)
theorem contactOrder_mul (x u₀ u₁:K) (F P:Poly4 K) (hF:F ≠ 0) (hP:P ≠ 0) :
    contactOrder K x u₀ u₁ (F * P) =
      contactOrder K x u₀ u₁ F + contactOrder K x u₀ u₁ P:=by
  unfold contactOrder
  rw [map_mul]
  exact order_mul localWeights _ _ (localize_ne_zero K x u₀ u₁ F hF)
    (localize_ne_zero K x u₀ u₁ P hP)
theorem contact_colon_iff (x u₀ u₁:K) (m:ℕ) (F P:Poly4 K) (hF:F ≠ 0) :
    ContactAtLeast K x u₀ u₁ m (F * P) ↔
      ContactAtLeast K x u₀ u₁ (m - contactOrder K x u₀ u₁ F) P:=by
  unfold ContactAtLeast contactOrder
  rw [map_mul]
  exact colon_iff localWeights m _ _ (localize_ne_zero K x u₀ u₁ F hF)
theorem localize_pderiv_R (x u₀ u₁:K) (P:Poly4 K) :
    localize K x u₀ u₁ (MvPolynomial.pderiv (2:Fin 4) P) =
      MvPolynomial.pderiv (2:Fin 4) (localize K x u₀ u₁ P) -
        MvPolynomial.X 0 * MvPolynomial.pderiv (1:Fin 4) (localize K x u₀ u₁ P):=by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp [localize]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
      ring
  | mul_X P i hP =>
      simp only [MvPolynomial.pderiv_mul, map_add, map_mul, hP]
      fin_cases i <;> simp [localize, localVariables, MvPolynomial.pderiv_mul] <;> ring
theorem contactAtLeast_pderiv_R (x u₀ u₁:K) (m:ℕ) (P:Poly4 K)
    (hP:ContactAtLeast K x u₀ u₁ m P) :
    ContactAtLeast K x u₀ u₁ (m - 1) (MvPolynomial.pderiv (2:Fin 4) P):=by
  change AtLeast localWeights (m - 1) (localize K x u₀ u₁ (MvPolynomial.pderiv 2 P))
  rw [localize_pderiv_R]
  have hR:=atLeast_pderiv localWeights (2:Fin 4) hP
  have hv:=atLeast_pderiv localWeights (1:Fin 4) hP
  have ht:=atLeast_X (K:=K) localWeights (0:Fin 4)
  have htv:=atLeast_mul localWeights ht hv
  apply atLeast_sub localWeights
  · apply atLeast_mono localWeights (show m - 1 ≤ m - localWeights 2 by
      change m - 1 ≤ m - 0
      omega) hR
  · apply atLeast_mono localWeights (show m - 1 ≤ localWeights 0 + (m - localWeights 1) by
      change m - 1 ≤ 1 + (m - 2)
      omega) htv
def localEvaluation (P:Polynomial K) (x γ:K):Poly4 K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X, RCN185.contactResidual P x,
    Polynomial.taylor x P.derivative, Polynomial.C γ]
theorem localEvaluation_localize (Q:Poly4 K) (P:Polynomial K)
    (x u₀ u₁ γ:K) (hvalue:P.eval x = u₀ + γ * u₁) :
    localEvaluation K P x γ (localize K x u₀ u₁ Q) =
      Polynomial.taylor x (specialization K P γ Q):=by
  have hhom:(localEvaluation K P x γ).comp (localize K x u₀ u₁) =
      (Polynomial.taylorAlgHom x).comp (specialization K P γ):=by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [localEvaluation, localize, localVariables, specialization,
        RCN185.contactResidual, hvalue,
        Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq] <;> ring
  exact DFunLike.congr_fun hhom Q
theorem localEvaluation_dvd (Q:Poly4 K) (P:Polynomial K) (x γ:K) (m:ℕ)
    (hQ:AtLeast localWeights m Q) :
    (Polynomial.X:Polynomial K) ^ m ∣ localEvaluation K P x γ Q:=by
  classical
  rw [MvPolynomial.as_sum Q, map_sum]
  apply Finset.dvd_sum
  intro d hd
  have hweight:m ≤ d 0 + 2 * d 1:=by
    have h:=hQ d hd
    rw [weight_fin4] at h
    simpa [localWeights, Nat.mul_comm] using h
  have hterm:=RCN185.contact_monomial_dvd
    (Polynomial.C (MvPolynomial.coeff d Q))
    (RCN185.contactResidual P x)
    (Polynomial.taylor x P.derivative) m (d 0) (d 1) (d 2)
    (RCN185.X_sq_dvd_contactResidual P x) hweight
  have hlast:=dvd_mul_of_dvd_left hterm ((Polynomial.C γ) ^ d 3)
  simpa [RCN122.monomial_eq, localEvaluation,
    Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq] using hlast
theorem contactAtLeast_specialization_dvd (Q:Poly4 K) (P:Polynomial K)
    (x u₀ u₁ γ:K) (m:ℕ) (hvalue:P.eval x = u₀ + γ * u₁)
    (hQ:ContactAtLeast K x u₀ u₁ m Q) :
    (Polynomial.X - Polynomial.C x) ^ m ∣ specialization K P γ Q:=by
  have hlocal:=localEvaluation_dvd K (localize K x u₀ u₁ Q) P x γ m hQ
  rw [localEvaluation_localize K Q P x u₀ u₁ γ hvalue] at hlocal
  exact (RCN185.shifted_power_dvd_iff_taylor_coeff_zero
    (specialization K P γ Q) x m).mpr (Polynomial.X_pow_dvd_iff.mp hlocal)
theorem specialized_R_derivative_dvd (F:Poly4 K) (hF:F ≠ 0)
    (P:Polynomial K) (x u₀ u₁ γ:K) (hvalue:P.eval x = u₀ + γ * u₁) :
    (Polynomial.X - Polynomial.C x) ^ (contactOrder K x u₀ u₁ F - 1) ∣
      specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F):=by
  apply contactAtLeast_specialization_dvd K _ P x u₀ u₁ γ _ hvalue
  apply contactAtLeast_pderiv_R K x u₀ u₁ (contactOrder K x u₀ u₁ F) F
  exact (exactOrder_order localWeights (localize K x u₀ u₁ F)
    (localize_ne_zero K x u₀ u₁ F hF)).1
theorem specialized_R_rootMultiplicity [DecidableEq K] (F:Poly4 K) (hF:F ≠ 0)
    (P:Polynomial K) (x u₀ u₁ γ:K) (hvalue:P.eval x = u₀ + γ * u₁)
    (hregular:specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F) ≠ 0) :
    contactOrder K x u₀ u₁ F - 1 ≤
      (specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F)).rootMultiplicity x:=by
  exact (Polynomial.le_rootMultiplicity_iff hregular).mpr
    (specialized_R_derivative_dvd K F hF P x u₀ u₁ γ hvalue)
theorem specialized_R_derivative_degree (F:Poly4 K) (P:Polynomial K) (γ:K)
    (w d:ℕ) (hP:P.natDegree ≤ w)
    (hF:MvPolynomial.weightedTotalDegree (contactWeights w) F ≤ d)
    (hregular:specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F) ≠ 0) :
    (specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F)).natDegree + w ≤ d + 1:=by
  classical
  let H:Poly4 K:=MvPolynomial.pderiv (2:Fin 4) F
  have hsupport (e:Fin 4 →₀ ℕ) (he:e ∈ H.support) :
      Finsupp.weight (contactWeights w) e + (w - 1) ≤ d:=by
    have hbefore:e + Finsupp.single (2:Fin 4) 1 ∈ F.support:=by
      apply MvPolynomial.mem_support_iff.mpr
      intro hz
      have hne:=MvPolynomial.mem_support_iff.mp he
      apply hne
      change MvPolynomial.coeff e (MvPolynomial.pderiv (2:Fin 4) F) = 0
      rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
    have hh:=(MvPolynomial.le_weightedTotalDegree (contactWeights w) hbefore).trans hF
    simpa [map_add, Finsupp.weight_single, contactWeights] using hh
  have hH:H ≠ 0:=by
    intro hz
    apply hregular
    change specialization K P γ H = 0
    rw [hz, map_zero]
  obtain ⟨e, he⟩:=MvPolynomial.support_nonempty.mpr hH
  have hdrop:w - 1 ≤ d:=by
    have hh:=hsupport e he
    omega
  have hterms:∀ e ∈ H.support,
      (specialization K P γ (MvPolynomial.monomial e (MvPolynomial.coeff e H))).natDegree ≤
        d - (w - 1):=by
    intro e he
    have hw:=hsupport e he
    rw [contact_weight] at hw
    have ht:=specialization_monomial_natDegree_le K P γ w hP e (MvPolynomial.coeff e H)
    omega
  have hdegree:(specialization K P γ H).natDegree ≤ d - (w - 1):=by
    rw [MvPolynomial.as_sum H, map_sum]
    exact Polynomial.natDegree_sum_le_of_forall_le H.support
      (fun e => specialization K P γ (MvPolynomial.monomial e (MvPolynomial.coeff e H))) hterms
  change (specialization K P γ H).natDegree + w ≤ d + 1
  omega
end LocalCoordinates
section KernelBridge
variable (K:Type*) [Field K]
def diagonalWeights:Fin 4 → ℕ:=![1, 1, 0, 0]
def blowupExponent:(Fin 4 →₀ ℕ) →+ (Fin 4 →₀ ℕ) where
  toFun d:=Finsupp.single 0 (d 0 + d 1) + Finsupp.single 1 (d 1) +
    Finsupp.single 2 (d 2) + Finsupp.single 3 (d 3)
  map_zero':=by simp
  map_add' d e:=by
    ext i
    fin_cases i <;> simp [Finsupp.add_apply] <;> omega
theorem blowupExponent_injective:Function.Injective blowupExponent:=by
  intro d e h
  have hsum:d 0 + d 1 = e 0 + e 1:=by
    simpa [blowupExponent] using congrArg (fun q:Fin 4 →₀ ℕ => q 0) h
  have h1:d 1 = e 1:=by
    simpa [blowupExponent] using congrArg (fun q:Fin 4 →₀ ℕ => q 1) h
  have h2:d 2 = e 2:=by
    simpa [blowupExponent] using congrArg (fun q:Fin 4 →₀ ℕ => q 2) h
  have h3:d 3 = e 3:=by
    simpa [blowupExponent] using congrArg (fun q:Fin 4 →₀ ℕ => q 3) h
  have h0:d 0 = e 0:=by omega
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
def contactBlowup:Poly4 K →+* Poly4 K :=
  AddMonoidAlgebra.mapDomainRingHom K blowupExponent
theorem contactBlowup_monomial (d:Fin 4 →₀ ℕ) (a:K) :
    contactBlowup K (MvPolynomial.monomial d a) = MvPolynomial.monomial (blowupExponent d) a:=by
  change AddMonoidAlgebra.mapDomain blowupExponent (AddMonoidAlgebra.single d a) =
    AddMonoidAlgebra.single (blowupExponent d) a
  exact AddMonoidAlgebra.mapDomain_single
@[simp] theorem contactBlowup_C (a:K) :
    contactBlowup K (MvPolynomial.C a) = MvPolynomial.C a:=by
  change contactBlowup K (MvPolynomial.monomial 0 a) = MvPolynomial.monomial 0 a
  rw [contactBlowup_monomial, map_zero]
@[simp] theorem contactBlowup_X (i:Fin 4) :
    contactBlowup K (MvPolynomial.X i) =
      ![MvPolynomial.X 0, MvPolynomial.X 0 * MvPolynomial.X 1,
        MvPolynomial.X 2, MvPolynomial.X 3] i:=by
  change contactBlowup K (MvPolynomial.monomial (Finsupp.single i 1) 1) = _
  rw [contactBlowup_monomial]
  fin_cases i <;> simp [blowupExponent, MvPolynomial.monomial_add_single,
    ← MvPolynomial.X_pow_eq_monomial]
theorem support_contactBlowup (P:Poly4 K) :
    (contactBlowup K P).support = P.support.image blowupExponent:=by
  change (Finsupp.mapDomain blowupExponent (AddMonoidAlgebra.coeff P)).support =
    Finset.image blowupExponent (AddMonoidAlgebra.coeff P).support
  exact Finsupp.mapDomain_support_of_injective blowupExponent_injective _
theorem weight_blowupExponent (d:Fin 4 →₀ ℕ) :
    Finsupp.weight diagonalWeights (blowupExponent d) = Finsupp.weight localWeights d:=by
  rw [weight_fin4, weight_fin4]
  simp [diagonalWeights, localWeights, blowupExponent] <;> omega
theorem atLeast_contactBlowup_iff (m:ℕ) (P:Poly4 K) :
    AtLeast diagonalWeights m (contactBlowup K P) ↔ AtLeast localWeights m P:=by
  classical
  constructor
  · intro h d hd
    have hmem:blowupExponent d ∈ (contactBlowup K P).support:=by
      rw [support_contactBlowup]
      exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
    simpa only [weight_blowupExponent] using h _ hmem
  · intro h d hd
    rw [support_contactBlowup] at hd
    obtain ⟨e, he, rfl⟩:=Finset.mem_image.mp hd
    simpa only [weight_blowupExponent] using h e he
@[simp] theorem shiftPlus_C_bridge (a:K) :
    shiftPlus K (MvPolynomial.C a) = MvPolynomial.C a:=by
  simp [shiftPlus]
@[simp] theorem shiftPlus_X_bridge (i:Fin 3) :
    shiftPlus K (MvPolynomial.X i) =
      ![MvPolynomial.X 0 + MvPolynomial.X 1, MvPolynomial.X 1, MvPolynomial.X 2] i:=by
  fin_cases i <;> simp [shiftPlus] <;> rfl
@[simp] theorem shiftPlus_seedAffine_bridge (u₀ u₁:K) :
    shiftPlus K (seedAffine K u₀ u₁) = seedAffine K u₀ u₁:=by
  simp [seedAffine, ← MvPolynomial.C_mul_X_eq_monomial]
theorem collected_contactBlowup_localize (x u₀ u₁:K) (Q:Poly4 K) :
    MvPolynomial.finSuccEquiv K 3 (contactBlowup K (localize K x u₀ u₁ Q)) =
      Polynomial.map (shiftPlus K).toRingHom (homogenizedTranslation K x u₀ u₁ Q):=by
  classical
  have hC (a:K):MvPolynomial.finSuccEquiv K 3 (MvPolynomial.C a) =
      Polynomial.C (MvPolynomial.C a):=by
    simp [MvPolynomial.finSuccEquiv_apply]
  have hX0:MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (0:Fin 4)) =
      Polynomial.X:=MvPolynomial.finSuccEquiv_X_zero
  have hX1:MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (1:Fin 4)) =
      Polynomial.C (MvPolynomial.X (0:Fin 3)) :=
    MvPolynomial.finSuccEquiv_X_succ (j:=(0:Fin 3))
  have hX2:MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (2:Fin 4)) =
      Polynomial.C (MvPolynomial.X (1:Fin 3)) :=
    MvPolynomial.finSuccEquiv_X_succ (j:=(1:Fin 3))
  have hX3:MvPolynomial.finSuccEquiv K 3 (MvPolynomial.X (3:Fin 4)) =
      Polynomial.C (MvPolynomial.X (2:Fin 3)) :=
    MvPolynomial.finSuccEquiv_X_succ (j:=(2:Fin 3))
  have hgen (i:Fin 4) :
      MvPolynomial.finSuccEquiv K 3
          (contactBlowup K (localize K x u₀ u₁ (MvPolynomial.X i))) =
        Polynomial.map (shiftPlus K).toRingHom
          (homogenizedTranslation K x u₀ u₁ (MvPolynomial.X i)):=by
    fin_cases i <;>
      simp [localize, localVariables, homogenizedTranslation, translationVariables,
        hC, hX0, hX1, hX2, hX3, seedAffine,
        ← MvPolynomial.C_mul_X_eq_monomial, Polynomial.algebraMap_apply,
        MvPolynomial.algebraMap_eq] <;> ring
  induction Q using MvPolynomial.induction_on with
  | C a =>
      simp [localize, homogenizedTranslation, MvPolynomial.finSuccEquiv_apply,
        Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  | add P Q hP hQ =>
      simp only [map_add, Polynomial.map_add, hP, hQ]
  | mul_X P i hP =>
      simpa only [map_mul, Polynomial.map_mul] using congrArg₂ (· * ·) hP (hgen i)
theorem diagonalAtLeast_iff_coeff (m:ℕ) (Q:Poly4 K) :
    AtLeast diagonalWeights m Q ↔
      ∀ (r:ℕ) (d:Fin 3 →₀ ℕ), r + d 0 < m →
        MvPolynomial.coeff d ((MvPolynomial.finSuccEquiv K 3 Q).coeff r) = 0:=by
  classical
  constructor
  · intro h r d hsmall
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]
    by_contra hc
    have hw:=h (Finsupp.cons r d) (MvPolynomial.mem_support_iff.mpr hc)
    have hcons:(Finsupp.cons r d) (1:Fin 4) = d 0:=rfl
    rw [weight_fin4] at hw
    simp [diagonalWeights, hcons] at hw
    omega
  · intro h d hd
    have hweight:Finsupp.weight diagonalWeights d = d 0 + d 1:=by
      rw [weight_fin4]
      simp [diagonalWeights]
    by_contra hsmall
    have hlt:d 0 + d.tail 0 < m:=by
      simp only [Finsupp.tail_apply]
      change d 0 + d 1 < m
      omega
    have hz:=h (d 0) d.tail hlt
    rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hz
    have he:Finsupp.cons (d 0) d.tail = d:=by
      ext i
      fin_cases i <;> simp [Finsupp.tail_apply]
    rw [he] at hz
    exact MvPolynomial.mem_support_iff.mp hd hz
theorem contactAtLeast_iff_block_divisibility (x u₀ u₁:K) (m:ℕ) (Q:Poly4 K) :
    ContactAtLeast K x u₀ u₁ m Q ↔
      ∀ r:ℕ, slopeDifference K ^ (m - r) ∣
        (homogenizedTranslation K x u₀ u₁ Q).coeff r:=by
  change AtLeast localWeights m (localize K x u₀ u₁ Q) ↔ _
  rw [← atLeast_contactBlowup_iff K m (localize K x u₀ u₁ Q), diagonalAtLeast_iff_coeff]
  simp only [collected_contactBlowup_localize, Polynomial.coeff_map]
  constructor
  · intro h r
    apply (contactJet_eq_zero_iff K (m - r) _).mp
    apply (contactJet_eq_zero_iff_coeff K (m - r) _).mpr
    intro d hd
    exact h r d (by omega)
  · intro h r d hd
    have hjet:=(contactJet_eq_zero_iff K (m - r) _).mpr (h r)
    exact (contactJet_eq_zero_iff_coeff K (m - r) _).mp hjet d (by omega)
theorem contactAtLeast_of_mem_kernel {I:Type*} [Fintype I]
    (D w L s m:ℕ) (nodes u₀ u₁:I → K)
    (a:CoefficientIndex D w L s → K)
    (ha:a ∈ LinearMap.ker (constraintMap K D w L s m nodes u₀ u₁)) (i:I) :
    ContactAtLeast K (nodes i) (u₀ i) (u₁ i) m (reconstruct K D w L s a):=by
  apply (contactAtLeast_iff_block_divisibility K (nodes i) (u₀ i) (u₁ i) m _).mpr
  exact RCN101.translated_contact_of_mem_ker
    K D w L s m nodes u₀ u₁ a ha i
def slopeDiagonal:Poly K →ₐ[K] Poly K :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 0, MvPolynomial.X 2]
theorem monomial_fin3 (d:Fin 3 →₀ ℕ) (a:K) :
    MvPolynomial.monomial d a =
      MvPolynomial.C a * MvPolynomial.X 0 ^ d 0 * MvPolynomial.X 1 ^ d 1 *
        MvPolynomial.X 2 ^ d 2:=by
  have hd:d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
      Finsupp.single 2 (d 2):=by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hd]
  rw [MvPolynomial.monomial_add_single, MvPolynomial.monomial_add_single,
    ← MvPolynomial.C_mul_X_pow_eq_monomial]
theorem slopeDiagonal_fixed (P:Poly K) (hP:∀ d ∈ P.support, d 1 = 0) :
    slopeDiagonal K P = P:=by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P, map_sum]
  conv_rhs => rw [MvPolynomial.as_sum P]
  apply Finset.sum_congr rfl
  intro d hd
  rw [monomial_fin3]
  simp [slopeDiagonal, hP d hd]
@[simp] theorem slopeDiagonal_slopeDifference :
    slopeDiagonal K (slopeDifference K) = 0:=by
  simp [slopeDiagonal, slopeDifference]
theorem slopeFree_blocks_zero_of_contactAtLeast
    (D w L m:ℕ) (x u₀ u₁:K) (a:CoefficientIndex D w L 0 → K)
    (ha:ContactAtLeast K x u₀ u₁ m (reconstruct K D w L 0 a)) :
    ∀ r:ℕ, r < m → ((extractBlock K D w L 0 x u₀ u₁ r a):Poly K) = 0:=by
  intro r hr
  have hdiv:=(contactAtLeast_iff_block_divisibility K x u₀ u₁ m _).mp ha r
  rw [translation_reconstruct_coeff] at hdiv
  let B:Poly K:=extractBlock K D w L 0 x u₀ u₁ r a
  have hfree:∀ d ∈ B.support, d 1 = 0:=by
    intro d hd
    have hbox:=(extractBlock K D w L 0 x u₀ u₁ r a).property
    have hs:=(mem_coefficientBox_iff K (min r L) L 0 B).mp hbox d hd
    omega
  obtain ⟨q, hq⟩:=hdiv
  have hdiag:=congrArg (slopeDiagonal K) hq
  change slopeDiagonal K B = slopeDiagonal K (slopeDifference K ^ (m - r) * q) at hdiag
  rw [slopeDiagonal_fixed K B hfree, map_mul, map_pow, slopeDiagonal_slopeDifference] at hdiag
  have hpos:m - r ≠ 0:=by omega
  simpa only [zero_pow hpos, zero_mul] using hdiag
end KernelBridge
end
end ProximityPrize.SubmissionLower.ContactOrderBridge
end PackedLegacy_ContactOrderBridge

/-! Packed from ProximityPrize.SubmissionLower.CH. -/
section PackedLegacy_CH
namespace ProximityPrize.SubmissionLower.RCN324
open IsLocalRing
variable {K R:Type*} [CommRing K] [CommRing R] [Algebra K R]
private theorem prime_dvd_factorial:∀ {n p:ℕ},p.Prime → (p∣n.factorial ↔ p ≤ n)
 | 0,_,hp => iff_of_false hp.not_dvd_one (not_le_of_gt hp.pos)
 | n+1,p,hp => by
     rw [Nat.factorial_succ,hp.dvd_mul,prime_dvd_factorial hp]
     exact ⟨fun h => h.elim (Nat.le_of_dvd (Nat.succ_pos _)) Nat.le_succ_of_le,
       fun h => (_root_.lt_or_eq_of_le h).elim
         (Or.inr ∘ Nat.le_of_lt_succ) fun h => Or.inl <| by rw [h]⟩
theorem derivation_pow_mul (D:Derivation K R R) (pi u:R) (mu:ℕ)
   (hmu:1 ≤ mu):
   D (pi^mu*u)=
     pi^(mu-1)*((mu:R)*u*D pi+pi*D u):=by
 rw [D.leibniz,Derivation.leibniz_pow]
 simp only [nsmul_eq_mul,smul_eq_mul]
 have hpow:pi^mu=pi^(mu-1)*pi:=by
   obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hmu
   simp [Nat.add_comm,pow_succ]
 rw [hpow]
 ring
theorem tangent_pow_mul (D:Derivation K R R) (pi u a:R) (mu:ℕ)
   (hmu:1 ≤ mu) (htangent:D pi=pi*a):
   D (pi^mu*u)=pi^mu*((mu:R)*a*u+D u):=by
 rw [derivation_pow_mul D pi u mu hmu,htangent]
 have hpow:pi^mu=pi^(mu-1)*pi:=by
   obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hmu
   simp [Nat.add_comm,pow_succ]
 rw [hpow]
 ring
theorem tangent_preserves_divisibility (D:Derivation K R R) (pi a:R) (mu:ℕ)
   (hmu:1 ≤ mu) (htangent:D pi=pi*a) (f:R) (hf:pi^mu∣f):
   pi^mu∣D f:=by
 obtain ⟨u,rfl⟩:=hf
 rw [tangent_pow_mul D pi u a mu hmu htangent]
 exact dvd_mul_right _ _
theorem tangent_iterate_preserves_divisibility
   (D:Derivation K R R) (pi a:R) (mu:ℕ)
   (hmu:1 ≤ mu) (htangent:D pi=pi*a) (f:R) (hf:pi^mu∣f):
   ∀ r,pi^mu∣(D:R → R)^[r] f:=by
 intro r
 induction r with
 | zero => simpa using hf
 | succ r ih =>
     rw [Function.iterate_succ_apply']
     exact tangent_preserves_divisibility D pi a mu hmu htangent _ ih
theorem iterate_pow_mul_expansion (D:Derivation K R R) (pi u:R)
   (mu r:ℕ) (hr:r ≤ mu):
   ∃ error:R,
     (D:R → R)^[r] (pi^mu*u)=
       (mu.descFactorial r:R)*pi^(mu-r)*u*(D pi)^r+
         pi^(mu-r+1)*error:=by
 induction r with
 | zero =>
     refine ⟨0,?_⟩
     simp
 | succ r ih =>
     have hr0:r ≤ mu:=le_trans (Nat.le_succ r) hr
     obtain ⟨error,herror⟩:=ih hr0
     obtain ⟨k,hk⟩:∃ k,mu-r=k+1:=by
       have hpos:0 < mu-r:=Nat.sub_pos_of_lt (Nat.lt_of_succ_le hr)
       exact Nat.exists_eq_succ_of_ne_zero hpos.ne'
     have hnext:mu-(r+1)=k:=by omega
     let q:=D pi
     let nextError:R:=
       (mu.descFactorial r:R)*D u*q^r+
       (mu.descFactorial r:R)*u*(r:R)*q^(r-1)*D q+
       (k+2:R)*q*error+pi*D error
     refine ⟨nextError,?_⟩
     rw [Function.iterate_succ_apply',herror,map_add]
     simp only [D.leibniz,Derivation.leibniz_pow,D.map_natCast,
       nsmul_eq_mul,smul_eq_mul]
     rw [hk,hnext,Nat.descFactorial_succ]
     have hmur:mu-r=k+1:=hk
     push_cast [hmur]
     dsimp only [q,nextError]
     ring
theorem isUnit_add_of_isUnit_of_not_isUnit [IsLocalRing R]
   {a b:R} (ha:IsUnit a) (hb:¬ IsUnit b):IsUnit (a+b):=by
 by_contra hab
 have hnb:¬ IsUnit (-b):=by simpa using hb
 have hs:=IsLocalRing.nonunits_add hab hnb
 apply hs
 simpa [add_assoc] using ha
section DVR
variable [IsDomain R] [IsDiscreteValuationRing R]
theorem addVal_iterate_eq_sub_of_transverse
   (D:Derivation K R R) (pi u:R) (mu r p:ℕ)
   [CharP R p] (hp:p.Prime) (hmu:mu < p) (hr:r ≤ mu)
   (hpi:Irreducible pi) (hu:IsUnit u) (htrans:IsUnit (D pi)):
   IsDiscreteValuationRing.addVal R ((D:R → R)^[r] (pi^mu*u))=mu-r:=by
 obtain ⟨error,herror⟩:=iterate_pow_mul_expansion D pi u mu r hr
 have hdescDvd:mu.descFactorial r∣mu.factorial:=by
   refine ⟨(mu-r).factorial,?_⟩
   rw [mul_comm,Nat.factorial_mul_descFactorial hr]
 have hnot:¬p∣mu.descFactorial r:=by
   intro hd
   have hpf:p∣mu.factorial:=hd.trans hdescDvd
   rw [prime_dvd_factorial hp] at hpf
   omega
 have hc:IsUnit (mu.descFactorial r:R):=
   (CharP.isUnit_natCast_iff hp).2 hnot
 have hlead:IsUnit ((mu.descFactorial r:R)*u*(D pi)^r):=
   (hc.mul hu).mul (htrans.pow r)
 let lead:R:=(mu.descFactorial r:R)*u*(D pi)^r
 have hpiError:¬IsUnit (pi*error):=
   not_isUnit_of_not_isUnit_dvd hpi.not_isUnit (dvd_mul_right pi error)
 have hbracket:IsUnit (lead+pi*error):=
   isUnit_add_of_isUnit_of_not_isUnit hlead hpiError
 have hfactor:
     (D:R → R)^[r] (pi^mu*u)=pi^(mu-r)*(lead+pi*error):=by
   rw [herror]
   simp only [lead]
   ring
 rw [hfactor,IsDiscreteValuationRing.addVal_mul,
   IsDiscreteValuationRing.addVal_pow,
   IsDiscreteValuationRing.addVal_uniformizer hpi,
   IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hbracket]
 simp
end DVR
theorem isDiscreteValuationRing_of_isRegularLocalRing_of_dimension_one
   [IsDomain R] [IsRegularLocalRing R] (hdim:ringKrullDim R=1):
   IsDiscreteValuationRing R:=by
 have hfin':=(IsRegularLocalRing.iff_finrank_cotangentSpace R).mp
   (inferInstance:IsRegularLocalRing R)
 rw [hdim] at hfin'
 have hfin:Module.finrank (ResidueField R) (CotangentSpace R)=1:=by
   exact_mod_cast hfin'
 exact IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp hfin
end ProximityPrize.SubmissionLower.RCN324
end PackedLegacy_CH

/-! Packed from ProximityPrize.SubmissionLower.BI. -/
section PackedLegacy_BI
namespace ProximityPrize.SubmissionLower.RCN133
open Function Set
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {ι K M:Type*} [Field K] [AddCommGroup M] [Module K M]
theorem finite_iUnion_ssubset
   (s:Finset ι) (p:ι → Submodule K M)
   (h₁:∀ i,p i≠⊤) (h₂:s.card < ENat.card K):
   ⋃ i∈s,(p i:Set M) ⊂ univ:=by
 letI:DecidableEq ι:=Classical.decEq ι
 letI:DecidableEq K:=Classical.decEq K
 induction s using Finset.induction_on with
 | empty => simp
 | insert j s hj hj' =>
   simp only [ssubset_univ_iff] at hj' ⊢
   rcases s.eq_empty_or_nonempty with rfl | hs
   · simpa using! h₁ j
   replace h₂:s.card+1 < ENat.card K:=by simpa [Finset.card_insert_of_notMem hj] using! h₂
   specialize hj' (lt_trans ENat.natCast_lt_succ h₂)
   contrapose hj'
   replace hj':(p j:Set M) ∪ (⋃ i∈s,p i)=univ:=by
     simpa [Finset.mem_insert] using! hj'
   suffices (p j:Set M) ⊆ ⋃ i∈s,p i by rwa [union_eq_right.mpr this] at hj'
   intro x (hx:x∈p j)
   rcases eq_or_ne x 0 with rfl | hx₀
   · simpa using! hs
   obtain ⟨y,hy⟩:∃ y,y∉p j:=by specialize h₁ j;contrapose! h₁;ext;simp [h₁]
   have hy₀:y≠0:=by aesop
   let sxy:={x+t • y | (t:K) (ht:t≠0)}
   have hsxy:sxy ⊆ ⋃ i∈s,p i:=by
     suffices Disjoint sxy (p j) from this.subset_right_of_subset_union <| hj' ▸ sxy.subset_univ
     rw [Set.disjoint_iff]
     rintro-⟨⟨t,ht₀,rfl⟩,ht:x+t • y∈p j⟩
     rw [(p j).add_mem_iff_right hx,(p j).smul_mem_iff ht₀] at ht
     contradiction
   obtain ⟨k,hk,t₁,t₂,ht,ht₁,ht₂⟩:∃ᵉ (k∈s) (t₁:K) (t₂:K),
       t₁≠t₂∧x+t₁ • y∈p k∧x+t₂ • y∈p k:=by
     suffices ∃ᵉ (k∈s) (z₁∈sxy) (z₂∈sxy),z₁≠z₂∧z₁∈p k∧z₂∈p k by
       obtain ⟨k,hk, -,⟨t₁, -,rfl⟩, -,⟨t₂, -,rfl⟩,htne,ht₁,ht₂⟩:=this
       exact ⟨k,hk,t₁,t₂,by aesop,ht₁,ht₂⟩
     choose f hf using fun z:sxy↦mem_iUnion.mp (hsxy z.property)
     have hf':MapsTo f univ s:=fun z _↦by specialize hf z;aesop
     suffices ∃ z₁ z₂,z₁≠z₂∧f z₁=f z₂ by
       obtain ⟨z₁,z₂,hne,heq⟩:=this
       exact ⟨f z₁,hf' (mem_univ _),z₁,z₁.property,z₂,z₂.property,
         Subtype.coe_ne_coe.mpr hne,by specialize hf z₁;simp_all,by specialize hf z₂;aesop⟩
     have key:s.card < sxy.encard:=by
       refine lt_of_add_lt_add_right <| lt_of_lt_of_le h₂ ?_
       have:Injective (fun t:K↦x+t • y):=
         fun t₁ t₂ ht↦smul_left_injective K hy₀ <| by simpa using! ht
       have aux:sxy=((fun t:K↦x+t • y) '' {t | t≠0}):=by ext;simp [sxy]
       rw [aux,this.encard_image,encard_ne_add_one]
     obtain ⟨z₁, -,z₂, -,h⟩:=exists_ne_map_eq_of_encard_lt_of_maps_to (by simpa) hf'
     exact ⟨z₁,z₂,h⟩
   replace ht:y∈p k:=by
     have:(t₁-t₂) • y∈p k:=by convert sub_mem ht₁ ht₂;module
     refine ((p k).smul_mem_iff ?_).mp this
     rwa [sub_ne_zero]
   replace ht:x∈p k:=by convert sub_mem ht₁ ((p k).smul_mem t₁ ht);simp
   simpa using! ⟨k,hk,ht⟩
theorem exists_avoiding_finite_proper_submodules
   [Finite ι] [Infinite K]
   (p:ι → Submodule K M) (hproper:∀ i,p i≠⊤):
   ∃ x,∀ i,x∉p i:=by
 let _i:Fintype ι:=Fintype.ofFinite ι
 suffices ⋃ i,(p i:Set M) ⊂ univ by
   simpa [ssubset_univ_iff,iUnion_eq_univ_iff] using this
 simpa using finite_iUnion_ssubset Finset.univ p hproper (by simp)
variable {N:Type*} [AddCommGroup N] [Module K N]
theorem exists_simultaneous_noncancellation
   [Finite ι] [Infinite K]
   (lead:ι → M →ₗ[K] N) (hlead:∀ i,lead i≠0):
   ∃ x:M,∀ i,lead i x≠0:=by
 let bad:ι → Submodule K M:=fun i↦LinearMap.ker (lead i)
 have hproper:∀ i,bad i≠⊤:=by
   intro i htop
   apply hlead i
   rw [←LinearMap.ker_eq_top]
   exact htop
 obtain ⟨x,hx⟩:=
   exists_avoiding_finite_proper_submodules bad hproper
 refine ⟨x,fun i hi↦?_⟩
 exact hx i (by simpa [bad,LinearMap.mem_ker] using hi)
variable {σ:Type*} [DecidableEq σ]
def polynomialOfSupport (E:Finset (σ →₀ ℕ)) (c:E → K):
   MvPolynomial σ K:=
 ∑ d:E,MvPolynomial.monomial d.1 (c d)
@[simp] theorem coeff_polynomialOfSupport
   (E:Finset (σ →₀ ℕ)) (c:E → K) (d:σ →₀ ℕ):
   MvPolynomial.coeff d (polynomialOfSupport E c)=
     if hd:d∈E then c ⟨d,hd⟩ else 0:=by
 classical
 rw [show polynomialOfSupport E c=
     ∑ e∈(Finset.univ:Finset E),
       MvPolynomial.monomial e.1 (c e) by simp [polynomialOfSupport]]
 rw [MvPolynomial.coeff_sum]
 simp only [MvPolynomial.coeff_monomial]
 by_cases hd:d∈E
 · simp only [hd,dite_true]
   rw [Finset.sum_eq_single ⟨d,hd⟩]
   · simp
   · intro e _ hne
     have hval:e.1≠d:=by
       intro heq
       apply hne
       exact Subtype.ext heq
     rw [if_neg hval]
   · simp
 · simp only [hd,dite_false]
   apply Finset.sum_eq_zero
   intro e _
   have hval:e.1≠d:=by
     intro heq
     apply hd
     rw [←heq]
     exact e.2
   rw [if_neg hval]
theorem support_polynomialOfSupport_subset
   (E:Finset (σ →₀ ℕ)) (c:E → K):
   (polynomialOfSupport E c).support ⊆ E:=by
 intro d hd
 by_contra hnot
 have hcoeff:=MvPolynomial.mem_support_iff.mp hd
 rw [coeff_polynomialOfSupport,dif_neg hnot] at hcoeff
 exact hcoeff rfl
theorem exists_supportedPolynomial_simultaneous_noncancellation
   {τ:Type*} [Finite τ] [Infinite K]
   (E:Finset (σ →₀ ℕ))
   (lead:τ → (E → K) →ₗ[K] K) (hlead:∀ t,lead t≠0):
   ∃ c:E → K,
     (polynomialOfSupport E c).support ⊆ E∧
       ∀ t,lead t c≠0:=by
 obtain ⟨c,hc⟩:=exists_simultaneous_noncancellation lead hlead
 exact ⟨c,support_polynomialOfSupport_subset E c,hc⟩
end
end ProximityPrize.SubmissionLower.RCN133
end PackedLegacy_BI

/-! Packed from ProximityPrize.SubmissionLower.AZ. -/
section PackedLegacy_AZ
namespace ProximityPrize.SubmissionLower
open scoped NNReal ProbabilityTheory
open CoreDefinitions ProximityGap
def AffineLineGivenSetsBound
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   (C:LinearCode ι F) (δ:ℝ) (a:ℕ):Prop:=
 ∀ (U:Fin 2 → ι → F) (S:Finset F) (T:F → Finset ι),
   a < S.card →
   (∀ z∈S,(T z).card ≥ (Fintype.card ι:ℝ)*(1-δ)) →
   (∀ z∈S,
     LinearCode.projectedWord (fun i => U 0 i+z*U 1 i) (T z)∈
       LinearCode.projectedCodeSubmod C (T z)) →
   ∃ z∈S,∀ j:Fin 2,
     LinearCode.projectedWord (U j) (T z)∈LinearCode.projectedCodeSubmod C (T z)
theorem mcaError_affineLine_le_of_givenSetsBound
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   (C:LinearCode ι F) (δ:ℝ) (a:ℕ)
   (hgiven:AffineLineGivenSetsBound C δ a):
   mcaError (AffineLineGenerator F) C δ ≤
     ENNReal.ofReal ((a:ℝ)/Fintype.card F):=by
 classical
 unfold mcaError
 refine iSup_le fun U => ?_
 rw [Probability.prob_uniform_eq_ofReal]
 apply ENNReal.ofReal_le_ofReal
 apply div_le_div_of_nonneg_right
 · exact_mod_cast (show
     (Finset.univ.filter (fun z:F =>
       IsMCA (AffineLineGenerator F) C z U δ)).card ≤ a by
     by_contra hnot
     have hlarge:a < (Finset.univ.filter (fun z:F =>
         IsMCA (AffineLineGenerator F) C z U δ)).card:=by omega
     let S:Finset F:=Finset.univ.filter (fun z:F =>
       IsMCA (AffineLineGenerator F) C z U δ)
     have hmem (z:F) (hz:z∈S):
         IsMCA (AffineLineGenerator F) C z U δ:=by
       simpa [S] using hz
     let T:F → Finset ι:=fun z =>
       if hz:z∈S then Classical.choose (hmem z hz) else ∅
     have hTspec (z:F) (hz:z∈S):
         (T z).card ≥ (Fintype.card ι:ℝ)*(1-δ)∧
         LinearCode.projectedWord (fun i => U 0 i+z*U 1 i) (T z)∈
           LinearCode.projectedCodeSubmod C (T z)∧
         ∃ j:Fin 2,LinearCode.projectedWord (U j) (T z)∉
           LinearCode.projectedCodeSubmod C (T z):=by
       rcases Classical.choose_spec (hmem z hz) with ⟨hcard,hcomb,hbad⟩
       have hTz:T z=Classical.choose (hmem z hz):=by
         simp only [T,dif_pos hz]
       rw [hTz]
       refine ⟨hcard,?_,hbad⟩
       simpa [AffineLineGenerator,Fin.sum_univ_two] using hcomb
     obtain ⟨z,hzS,hall⟩:=hgiven U S T (by simpa [S] using hlarge)
       (fun z hz => (hTspec z hz).1) (fun z hz => (hTspec z hz).2.1)
     obtain ⟨j,hj⟩:=(hTspec z hzS).2.2
     exact hj (hall j))
 · positivity
open Finset
variable {ι F:Type} [Fintype ι] [DecidableEq ι]
 [Field F] [DecidableEq F]
theorem exists_common_affine_set
   (U p:Fin 2 → ι → F) (T:Finset F) (A:F → Finset ι) (e:ℕ)
   (hT:e+1 < T.card)
   (hAcard:∀ z∈T,Fintype.card ι-e ≤ (A z).card)
   (hEq:∀ z∈T,∀ x∈A z,
     U 0 x+z*U 1 x=p 0 x+z*p 1 x):
   ∃ z∈T,∀ x∈A z,U 0 x=p 0 x∧U 1 x=p 1 x:=by
 classical
 let B:Finset ι:=Finset.univ.filter fun x =>
   U 0 x≠p 0 x∨U 1 x≠p 1 x
 let R:F → Finset ι:=fun z => A z ∩ B
 have hRsub (z:F):R z ⊆ B:=by
   intro x hx
   exact (Finset.mem_inter.mp hx).2
 have hRpair:(↑T:Set F).PairwiseDisjoint R:=by
   rintro z hz w hw hzw
   change Disjoint (R z) (R w)
   rw [Finset.disjoint_left]
   intro x hxz hxw
   have hxAz:x∈A z:=(Finset.mem_inter.mp hxz).1
   have hxAw:x∈A w:=(Finset.mem_inter.mp hxw).1
   have hzEq:=hEq z hz x hxAz
   have hwEq:=hEq w hw x hxAw
   have hmul:(z-w)*(U 1 x-p 1 x)=0:=by
     linear_combination hzEq-hwEq
   have hzw0:z-w≠0:=sub_ne_zero.mpr hzw
   have hrow1:U 1 x=p 1 x:=by
     exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hzw0)
   have hrow0:U 0 x=p 0 x:=by
     rw [hrow1] at hzEq
     exact add_right_cancel hzEq
   have hxB:x∈B:=(Finset.mem_inter.mp hxz).2
   simp only [B,Finset.mem_filter,Finset.mem_univ,true_and] at hxB
   exact hxB.elim (fun h => h hrow0) (fun h => h hrow1)
 have hRlower (z:F) (hz:z∈T):B.card ≤ (R z).card+e:=by
   have hsplit:=Finset.card_inter_add_card_sdiff (A z) B
   have hsdiff:(A z \ B).card ≤ Bᶜ.card:=by
     apply Finset.card_le_card
     intro x hx
     rw [Finset.mem_compl]
     exact (Finset.mem_sdiff.mp hx).2
   rw [Finset.card_compl] at hsdiff
   have ha:=hAcard z hz
   have hbcard:B.card ≤ Fintype.card ι:=Finset.card_le_univ B
   dsimp only [R]
   omega
 have hB:B.card ≤ e:=by
   by_contra hnot
   have heB:e < B.card:=Nat.lt_of_not_ge hnot
   have hsumLower:T.card*(B.card-e) ≤ ∑ z∈T,(R z).card:=by
     calc
       T.card*(B.card-e)=∑ z∈T,(B.card-e):=by
         exact (Finset.sum_const_nat (fun _ _ => rfl)).symm
       _ ≤ ∑ z∈T,(R z).card:=by
         exact Finset.sum_le_sum fun z hz => by
           have:=hRlower z hz
           omega
   have hunionSub:(T.biUnion R).card ≤ B.card:=by
     apply Finset.card_le_card
     intro x hx
     obtain ⟨z,hzT,hxR⟩:=Finset.mem_biUnion.mp hx
     exact hRsub z hxR
   have hunionCard:(T.biUnion R).card=∑ z∈T,(R z).card:=
     Finset.card_biUnion hRpair
   rw [hunionCard] at hunionSub
   have hprod:T.card*(B.card-e) ≤ B.card:=hsumLower.trans hunionSub
   have hdpos:0 < B.card-e:=Nat.sub_pos_of_lt heB
   have htlo:e+2 ≤ T.card:=by omega
   have he_mul:e ≤ e*(B.card-e):=
     Nat.le_mul_of_pos_right e hdpos
   have hstrict:B.card < (e+2)*(B.card-e):=by
     calc
       B.card=e+(B.card-e):=(Nat.add_sub_of_le heB.le).symm
       _ ≤ e*(B.card-e)+(B.card-e):=Nat.add_le_add_right he_mul _
       _ < e*(B.card-e)+2*(B.card-e):=by omega
       _=(e+2)*(B.card-e):=by ring
   have hprodLower:(e+2)*(B.card-e) ≤
       T.card*(B.card-e):=Nat.mul_le_mul_right _ htlo
   omega
 by_contra hno
 push Not at hno
 have hRpos:∀ z∈T,1 ≤ (R z).card:=by
   intro z hz
   obtain ⟨x,hxA,hxnot⟩:=hno z hz
   apply Finset.card_pos.mpr
   refine ⟨x,Finset.mem_inter.mpr ⟨hxA,?_⟩⟩
   simp only [B,Finset.mem_filter,Finset.mem_univ,true_and]
   by_cases h0:U 0 x=p 0 x
   · exact Or.inr (hxnot h0)
   · exact Or.inl h0
 have hTsum:T.card ≤ ∑ z∈T,(R z).card:=by
   calc
     T.card=∑ z∈T,1:=by simp
     _ ≤ ∑ z∈T,(R z).card:=Finset.sum_le_sum hRpos
 have hunionSub:(T.biUnion R).card ≤ B.card:=by
   apply Finset.card_le_card
   intro x hx
   obtain ⟨z,hzT,hxR⟩:=Finset.mem_biUnion.mp hx
   exact hRsub z hxR
 rw [Finset.card_biUnion hRpair] at hunionSub
 have hTB:T.card ≤ B.card:=hTsum.trans hunionSub
 omega
def AffineLineAlignmentBound
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   (C:LinearCode ι F) (e a:ℕ):Prop:=
 ∀ (U:Fin 2 → ι → F) (S:Finset F) (A:F → Finset ι),
   a < S.card →
   (∀ z∈S,Fintype.card ι-e ≤ (A z).card) →
   (∀ z∈S,
     LinearCode.projectedWord (fun i => U 0 i+z*U 1 i) (A z)∈
       LinearCode.projectedCodeSubmod C (A z)) →
   ∃ p:Fin 2 → ι → F,
     (∀ j,p j∈C)∧
     ∃ T:Finset F,T ⊆ S∧e+1 < T.card∧
       ∀ z∈T,∀ x∈A z,
         U 0 x+z*U 1 x=p 0 x+z*p 1 x
theorem givenSetsBound_of_alignmentBound
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   (C:LinearCode ι F) (δ:ℝ) (e a:ℕ)
   (hsize:∀ A:Finset ι,
     (A.card:ℝ) ≥ (Fintype.card ι:ℝ)*(1-δ) →
     Fintype.card ι-e ≤ A.card)
   (halign:AffineLineAlignmentBound C e a):
   AffineLineGivenSetsBound C δ a:=by
 classical
 intro U S A hS hAcard hcomb
 obtain ⟨p,hpC,T,hTS,hTcard,hEq⟩:=
   halign U S A hS (fun z hz => hsize (A z) (hAcard z hz)) hcomb
 obtain ⟨z,hzT,hz⟩:=
   exists_common_affine_set U p T A e hTcard
     (fun z hz => hsize (A z) (hAcard z (hTS hz))) hEq
 refine ⟨z,hTS hzT,fun j => ?_⟩
 rw [LinearCode.mem_projectedCodeSubmod_iff]
 refine ⟨p j,hpC j,?_⟩
 funext x
 simp only [LinearCode.projectedWord]
 rcases hz x.1 x.2 with ⟨h0,h1⟩
 fin_cases j
 · exact h0
 · exact h1
end ProximityPrize.SubmissionLower
end PackedLegacy_AZ

/-! Packed from ProximityPrize.SubmissionLower.DV. -/
section PackedLegacy_DV
namespace ProximityPrize.SubmissionLower.RCN050
open ProximityPrize.Benchmark
noncomputable section
variable {ι K:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
 [Field K] [Fintype K] [DecidableEq K]
def pencilSeeds (seeds:Finset K) (selected:K → Polynomial K)
   (P₀ P₁:Polynomial K):Finset K:=by
 classical
 exact seeds.filter (fun γ => selected γ=P₀+Polynomial.C γ*P₁)
def SelectedNoLargePencilBound (domain:ι ↪ K) (w e B:ℕ):Prop:=
 ∀ (U:Fin 2 → ι → K) (seeds:Finset K) (A:K → Finset ι)
   (selected:K → Polynomial K),
   (∀ γ∈seeds,(selected γ).natDegree ≤ w) →
   (∀ γ∈seeds,Fintype.card ι-e ≤ (A γ).card) →
   (∀ γ∈seeds,∀ i∈A γ,
     (selected γ).eval (domain i)=U 0 i+γ*U 1 i) →
   (∀ P₀ P₁:Polynomial K,P₀.natDegree ≤ w → P₁.natDegree ≤ w →
     (pencilSeeds seeds selected P₀ P₁).card ≤ e+1) →
   seeds.card ≤ B
theorem degree_lt_succ_of_natDegree_le (P:Polynomial K) (w:ℕ)
   (hdegree:P.natDegree ≤ w):P.degree < ((w+1:ℕ):WithBot ℕ):=by
 rcases eq_or_ne P 0 with hzero | hnonzero
 · simp [hzero]
 · rw [←Polynomial.natDegree_lt_iff_degree_lt hnonzero]
   omega
theorem exists_selected_polynomials
   (domain:ι ↪ K) (w:ℕ) (U:Fin 2 → ι → K)
   (seeds:Finset K) (A:K → Finset ι)
   (hprojected:∀ γ∈seeds,
     LinearCode.projectedWord (fun i => U 0 i+γ*U 1 i) (A γ)∈
       LinearCode.projectedCodeSubmod (ReedSolomon.code domain (w+1)) (A γ)):
   ∃ selected:K → Polynomial K,
     (∀ γ∈seeds,(selected γ).natDegree ≤ w)∧
     (∀ γ∈seeds,∀ i∈A γ,
       (selected γ).eval (domain i)=U 0 i+γ*U 1 i):=by
 classical
 have hexists (γ:K) (hγ:γ∈seeds):∃ P:Polynomial K,
     P.natDegree ≤ w∧∀ i∈A γ,P.eval (domain i)=U 0 i+γ*U 1 i:=by
   have hc:=hprojected γ hγ
   rw [LinearCode.mem_projectedCodeSubmod_iff] at hc
   obtain ⟨c,hcode,hvalue⟩:=hc
   change c∈ReedSolomon.code domain (w+1) at hcode
   rw [ReedSolomon.mem_code_iff_exists_polynomial] at hcode
   obtain ⟨P,hdegree,rfl⟩:=hcode
   refine ⟨P,?_,?_⟩
   · rcases eq_or_ne P 0 with hzero | hnonzero
     · simp [hzero]
     · have hd:P.natDegree < w+1:=
         (Polynomial.natDegree_lt_iff_degree_lt hnonzero).mpr hdegree
       omega
   · intro i hi
     have hh:=congrFun hvalue ⟨i,hi⟩
     simpa [LinearCode.projectedWord,ReedSolomon.evalOnPoints] using hh.symm
 let selected:K → Polynomial K:=fun γ =>
   if hγ:γ∈seeds then Classical.choose (hexists γ hγ) else 0
 have hspec (γ:K) (hγ:γ∈seeds):
     (selected γ).natDegree ≤ w∧
       ∀ i∈A γ,(selected γ).eval (domain i)=U 0 i+γ*U 1 i:=by
   simpa only [selected,dif_pos hγ] using Classical.choose_spec (hexists γ hγ)
 exact ⟨selected,fun γ hγ => (hspec γ hγ).1,fun γ hγ => (hspec γ hγ).2⟩
theorem exists_large_pencil_of_selected_count
   (domain:ι ↪ K) (w e B:ℕ)
   (hcount:SelectedNoLargePencilBound domain w e B)
   (U:Fin 2 → ι → K) (seeds:Finset K) (A:K → Finset ι)
   (selected:K → Polynomial K) (hlarge:B < seeds.card)
   (hdegree:∀ γ∈seeds,(selected γ).natDegree ≤ w)
   (hcard:∀ γ∈seeds,Fintype.card ι-e ≤ (A γ).card)
   (hagreement:∀ γ∈seeds,∀ i∈A γ,
     (selected γ).eval (domain i)=U 0 i+γ*U 1 i):
   ∃ P₀ P₁:Polynomial K,P₀.natDegree ≤ w∧P₁.natDegree ≤ w∧
     e+1 < (pencilSeeds seeds selected P₀ P₁).card:=by
 by_contra hno
 have hsmall:∀ P₀ P₁:Polynomial K,P₀.natDegree ≤ w → P₁.natDegree ≤ w →
     (pencilSeeds seeds selected P₀ P₁).card ≤ e+1:=by
   intro P₀ P₁ h₀ h₁
   apply Nat.le_of_not_gt
   intro hh
   exact hno ⟨P₀,P₁,h₀,h₁,hh⟩
 have hh:=hcount U seeds A selected hdegree hcard hagreement hsmall
 omega
theorem alignmentBound_of_selected_count
   (domain:ι ↪ K) (w e B:ℕ)
   (hcount:SelectedNoLargePencilBound domain w e B):
   AffineLineAlignmentBound (ReedSolomon.code domain (w+1)) e B:=by
 classical
 intro U seeds A hlarge hcard hprojected
 obtain ⟨selected,hdegree,hagreement⟩:=exists_selected_polynomials domain w U seeds A hprojected
 obtain ⟨P₀,P₁,h₀,h₁,hTcard⟩:=exists_large_pencil_of_selected_count
   domain w e B hcount U seeds A selected hlarge hdegree hcard hagreement
 let T:=pencilSeeds seeds selected P₀ P₁
 have hTsub:T ⊆ seeds:=Finset.filter_subset _ _
 let rows:Fin 2 → ι → K:=
   ![ReedSolomon.evalOnPoints domain P₀,ReedSolomon.evalOnPoints domain P₁]
 refine ⟨rows,?_,T,hTsub,hTcard,?_⟩
 · intro j
   fin_cases j
   · change ReedSolomon.evalOnPoints domain P₀∈ReedSolomon.code domain (w+1)
     exact ReedSolomon.evalOnPoints_mem_code_of_degree_lt
       (degree_lt_succ_of_natDegree_le P₀ w h₀)
   · change ReedSolomon.evalOnPoints domain P₁∈ReedSolomon.code domain (w+1)
     exact ReedSolomon.evalOnPoints_mem_code_of_degree_lt
       (degree_lt_succ_of_natDegree_le P₁ w h₁)
 · intro γ hγ i hi
   have hpoly:selected γ=P₀+Polynomial.C γ*P₁:=(Finset.mem_filter.mp hγ).2
   have heval:=congrArg (Polynomial.eval (domain i)) hpoly
   have hword:=hagreement γ (hTsub hγ) i hi
   simpa [rows,ReedSolomon.evalOnPoints] using hword.symm.trans heval
theorem exists_original_support_of_selected_count
   (domain:ι ↪ K) (w e B:ℕ)
   (hcount:SelectedNoLargePencilBound domain w e B)
   (U:Fin 2 → ι → K) (seeds:Finset K) (A:K → Finset ι)
   (hlarge:B < seeds.card)
   (hcard:∀ γ∈seeds,Fintype.card ι-e ≤ (A γ).card)
   (hprojected:∀ γ∈seeds,
     LinearCode.projectedWord (fun i => U 0 i+γ*U 1 i) (A γ)∈
       LinearCode.projectedCodeSubmod (ReedSolomon.code domain (w+1)) (A γ)):
   ∃ γ∈seeds,∀ j:Fin 2,
     LinearCode.projectedWord (U j) (A γ)∈
       LinearCode.projectedCodeSubmod (ReedSolomon.code domain (w+1)) (A γ):=by
 classical
 obtain ⟨rows,hrows,T,hTsub,hTcard,hEq⟩:=
   alignmentBound_of_selected_count domain w e B hcount U seeds A hlarge hcard hprojected
 obtain ⟨γ,hγ,hcommon⟩:=ProximityPrize.SubmissionLower.exists_common_affine_set
   U rows T A e hTcard (fun z hz => hcard z (hTsub hz)) hEq
 refine ⟨γ,hTsub hγ,fun j => ?_⟩
 rw [LinearCode.mem_projectedCodeSubmod_iff]
 refine ⟨rows j,hrows j,?_⟩
 funext i
 simp only [LinearCode.projectedWord]
 obtain ⟨h₀,h₁⟩:=hcommon i.1 i.2
 fin_cases j
 · exact h₀
 · exact h₁
def SelectedNoLargePencilBound6400:Prop:=
 SelectedNoLargePencilBound IRSProfile.domain 131071 76780 274980728111352763
theorem alignmentBound6400_of_selected_count
   (hcount:SelectedNoLargePencilBound6400):
   AffineLineAlignmentBound IRSProfile.baseCode 76780 274980728111352763:=by
 change AffineLineAlignmentBound (ReedSolomon.code IRSProfile.domain (131071+1))
   76780 274980728111352763
 exact alignmentBound_of_selected_count IRSProfile.domain 131071 76780
   274980728111352763 hcount
end
end ProximityPrize.SubmissionLower.RCN050
end PackedLegacy_DV

/-! Packed from ProximityPrize.SubmissionLower.K7. -/
section PackedLegacy_K7
namespace ProximityPrize.SubmissionLower.RCN175
open RCN174 RCN256 RCN223 ProximityPrize.Benchmark
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
abbrev FrozenCoefficientIndex6600:=
 CoefficientIndex weightedCap w seedTotalCap slopeCap
theorem exists_frozen_nonzero_contact_array6600
   (u0 u1:IRSProfile.Index → IRSProfile.Field):
   ∃ theta:FrozenCoefficientIndex6600 → IRSProfile.Field,theta≠0∧
     ∀ (i:IRSProfile.Index) (r:Fin multiplicity),
       contactJet IRSProfile.Field (multiplicity-r.val)
         ((extractBlock IRSProfile.Field weightedCap w seedTotalCap slopeCap
           (IRSProfile.domain i) (u0 i) (u1 i) r.val theta):
             Poly IRSProfile.Field)=0:=by
 apply exists_nonzero_block_equations IRSProfile.Field
   weightedCap w seedTotalCap slopeCap multiplicity
   (fun i:IRSProfile.Index↦IRSProfile.domain i) u0 u1
 rw [show Fintype.card IRSProfile.Index=n by
   norm_num [IRSProfile.Index,n]]
 simpa only [totalContactRank,RCN223.localContactRank,
   RCN256.localRankBound,
   RCN223.contactExponent,
   RCN223.coefficientCount,
   RCN174.coefficientCount,RCN256.contactRankBound,
   RCN256.blockInputCount,
   RCN256.blockKernelLowerBound] using interpolation_gate
theorem exists_frozen_nonzero_polynomial_and_equations6600
   (u0 u1:IRSProfile.Index → IRSProfile.Field):
   ∃ (Q:MvPolynomial (Fin 4) IRSProfile.Field)
     (theta:FrozenCoefficientIndex6600 → IRSProfile.Field),
     Q≠0∧
     Q∈globalCoefficientBox IRSProfile.Field
       weightedCap w seedTotalCap slopeCap∧
     Q=reconstruct IRSProfile.Field weightedCap w seedTotalCap slopeCap theta∧
     ∀ (i:IRSProfile.Index) (r:Fin multiplicity),
       contactJet IRSProfile.Field (multiplicity-r.val)
         ((extractBlock IRSProfile.Field weightedCap w seedTotalCap slopeCap
           (IRSProfile.domain i) (u0 i) (u1 i) r.val theta):
             Poly IRSProfile.Field)=0:=by
 obtain ⟨theta,htheta,hconstraints⟩:=
   exists_frozen_nonzero_contact_array6600 u0 u1
 exact ⟨reconstruct IRSProfile.Field weightedCap w seedTotalCap slopeCap theta,
   theta,
   reconstruct_ne_zero IRSProfile.Field weightedCap w seedTotalCap slopeCap
     theta htheta,
   reconstruct_mem_globalCoefficientBox IRSProfile.Field
     weightedCap w seedTotalCap slopeCap theta,
   rfl,hconstraints⟩
end
end ProximityPrize.SubmissionLower.RCN175
end PackedLegacy_K7

/-! Packed from ProximityPrize.SubmissionLower.GR. -/
section PackedLegacy_GR
namespace ProximityPrize.SubmissionLower.RCN320
open ProximityPrize.Benchmark RCN174 RCN175 RCN256 RCN223 RCN319
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
theorem exists_frozen_translated_contact_interpolant6600
   (u0 u1:IRSProfile.Index → IRSProfile.Field):
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q≠0∧
     Q∈globalCoefficientBox IRSProfile.Field
       weightedCap w seedTotalCap slopeCap∧
     ∀ (i:IRSProfile.Index) (r:ℕ),
       slopeDifference IRSProfile.Field^(multiplicity-r)∣
         (homogenizedTranslation IRSProfile.Field
           (IRSProfile.domain i) (u0 i) (u1 i) Q).coeff r:=by
 obtain ⟨Q,theta,hQ,hcaps,hreconstruct,hequations⟩:=
   exists_frozen_nonzero_polynomial_and_equations6600 u0 u1
 refine ⟨Q,hQ,hcaps,?_⟩
 intro i r
 rw [hreconstruct,
   translation_reconstruct_coeff IRSProfile.Field
     weightedCap w seedTotalCap slopeCap]
 exact all_blocks_divisible_of_equations IRSProfile.Field
   weightedCap w seedTotalCap slopeCap multiplicity
   (IRSProfile.domain i) (u0 i) (u1 i) theta (hequations i) r
theorem exists_frozen_universal_vanishing_interpolant6600
   (u0 u1:IRSProfile.Index → IRSProfile.Field):
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q≠0∧
     Q∈globalCoefficientBox IRSProfile.Field
       weightedCap w seedTotalCap slopeCap∧
     ∀ (gamma:IRSProfile.Field) (P:Polynomial IRSProfile.Field)
       (support:Finset IRSProfile.Index),
       P.natDegree ≤ w → agreements ≤ support.card →
       (∀ i∈support,
         P.eval (IRSProfile.domain i)=u0 i+gamma*u1 i) →
       specialization IRSProfile.Field P gamma Q=0:=by
 classical
 obtain ⟨Q,hQ,hcaps,hcontact⟩:=
   exists_frozen_translated_contact_interpolant6600 u0 u1
 refine ⟨Q,hQ,hcaps,?_⟩
 intro gamma P support hP hcard hvalues
 apply specialization_eq_zero_of_contact_and_degree IRSProfile.Field Q P gamma
   IRSProfile.domain u0 u1 support multiplicity
 · intro i hi r
   exact hcontact i r
 · exact hvalues
 · have hdegree:=specialization_natDegree_lt IRSProfile.Field
     weightedCap w seedTotalCap slopeCap Q P gamma
     (by norm_num [RCN223.weightedCap,
       RCN223.multiplicity,
       RCN223.agreements,
       RCN223.n,
       RCN223.errors])
     hcaps hP
   have hbound:weightedCap ≤
       RCN223.multiplicity*support.card:=by
     rw [RCN223.weightedCap]
     exact Nat.mul_le_mul_left
       RCN223.multiplicity hcard
   exact hdegree.trans_le hbound
end
end ProximityPrize.SubmissionLower.RCN320
end PackedLegacy_GR

/-! Packed from ProximityPrize.SubmissionLower.BF. -/
section PackedLegacy_BF
namespace ProximityPrize.SubmissionLower.RCN128
open ProximityPrize.Benchmark RCN050 RCN174 RCN319 RCN320 RCN238 RCN223
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
def SelectedNoLargePencilBound6600:Prop:=
 SelectedNoLargePencilBound IRSProfile.domain w errors alignmentBudget
def GlobalCountLtAlignment6600:Prop:=
 ∀ (Q:MvPolynomial (Fin 4) IRSProfile.Field),
   Q≠0 →
   Q∈globalCoefficientBox IRSProfile.Field
     weightedCap w seedTotalCap slopeCap →
   ∀ (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
     (seeds:Finset IRSProfile.Field)
     (u0 u1:IRSProfile.Index → IRSProfile.Field),
     (∀ gamma∈seeds,(selected gamma).natDegree ≤ w) →
     (∀ gamma∈seeds,
       specialization IRSProfile.Field (selected gamma) gamma Q=0) →
     (∀ gamma∈seeds,agreements ≤
       (Finset.univ.filter (fun i:IRSProfile.Index↦
         (selected gamma).eval (IRSProfile.domain i)=
           u0 i+gamma*u1 i)).card) →
     NoLargeSelectedPencil selected seeds w errors →
     seeds.card < alignmentBudget
abbrev InterpolantSelectedCount6600:=GlobalCountLtAlignment6600
theorem challenge_field_characteristic6600:
   CharP IRSProfile.Field prime:=by
 change CharP KoalaBear.Ext6 2130706433
 exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433
theorem original_support_card6600
   (A:IRSProfile.Field → Finset IRSProfile.Index)
   (seeds:Finset IRSProfile.Field)
   (hcard:∀ gamma∈seeds,
     Fintype.card IRSProfile.Index-errors ≤ (A gamma).card):
   ∀ gamma∈seeds,agreements ≤ (A gamma).card:=by
 intro gamma hgamma
 have h:=hcard gamma hgamma
 simpa [IRSProfile.Index,agreements,n,errors] using h
theorem selected_count_of_global_count_lt_alignment6600
   (hcount:GlobalCountLtAlignment6600):
   SelectedNoLargePencilBound6600:=by
 classical
 intro U seeds A selected hdegree hcard hvalues hno
 have hcard':=original_support_card6600 A seeds hcard
 obtain ⟨Q,hQ,hbox,hvanish⟩:=
   exists_frozen_universal_vanishing_interpolant6600 (U 0) (U 1)
 have hsolution:∀ gamma∈seeds,
     specialization IRSProfile.Field (selected gamma) gamma Q=0:=by
   intro gamma hgamma
   exact hvanish gamma (selected gamma) (A gamma)
     (hdegree gamma hgamma) (hcard' gamma hgamma) (hvalues gamma hgamma)
 have hagreement:∀ gamma∈seeds,agreements ≤
     (Finset.univ.filter (fun i:IRSProfile.Index↦
       (selected gamma).eval (IRSProfile.domain i)=
         U 0 i+gamma*U 1 i)).card:=by
   intro gamma hgamma
   apply le_trans (hcard' gamma hgamma)
   apply Finset.card_le_card
   intro i hi
   exact Finset.mem_filter.mpr
     ⟨Finset.mem_univ i,hvalues gamma hgamma i hi⟩
 have hno':NoLargeSelectedPencil selected seeds w errors:=by
   intro P0 P1 h0 h1
   have hp:=hno P0 P1 h0 h1
   refine le_trans ?_ hp
   apply Finset.card_le_card
   intro gamma hgamma
   simpa only [pencilSeeds,Finset.mem_filter] using
     (Finset.mem_filter.mp hgamma)
 exact Nat.le_of_lt
   (hcount Q hQ hbox selected seeds (U 0) (U 1)
     hdegree hsolution hagreement hno')
theorem alignment_of_global_count_lt_alignment6600
   (hcount:GlobalCountLtAlignment6600):
   AffineLineAlignmentBound IRSProfile.baseCode errors alignmentBudget:=by
 change AffineLineAlignmentBound
   (ReedSolomon.code IRSProfile.domain (w+1)) errors alignmentBudget
 exact alignmentBound_of_selected_count IRSProfile.domain w errors
   alignmentBudget (selected_count_of_global_count_lt_alignment6600 hcount)
end
end ProximityPrize.SubmissionLower.RCN128
end PackedLegacy_BF

/-! Packed from ProximityPrize.SubmissionLower.BY. -/
section PackedLegacy_BY
namespace ProximityPrize.SubmissionLower.RCN179
open scoped BigOperators
open RCN081 RCN167 RCN313 RCN234
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
theorem wt_polyG_le_of_R_le_Y
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hRY:weights 2 ≤ weights 1)
   (hYC:weights 1 ≤ C) (hF:wt weights F ≤ C):
   wt weights (polyG K F) ≤ C:=by
 have hx:=wt_pderiv_le weights F 0 C hF
 have hy:=wt_pderiv_le weights F 1 C hF
 have hR:wt weights (MvPolynomial.X (2:Fin 4):Poly4 K)=weights 2:=
   weighted_X weights 2
 have hm:=wt_mul_le weights (MvPolynomial.X (2:Fin 4):Poly4 K)
   (MvPolynomial.pderiv 1 F)
 have hsum:=wt_add_le weights (MvPolynomial.pderiv 0 F)
   (MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv 1 F)
 unfold polyG
 rw [wt_neg]
 exact hsum.trans (max_le (by omega) (by omega))
theorem numeratorStep_wt_le_equal_weight
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F M:Poly4 K) (b A C:ℕ)
   (hRY:weights 2 ≤ weights 1) (hYC:weights 1 ≤ C)
   (hRR:2*weights 2 ≤ C) (hA:weights 2 ≤ A)
   (hF:wt weights F ≤ C) (hM:wt weights M ≤ A):
   wt weights (numeratorStep K F b M) ≤
     A+2*(C-weights 2):=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly4 K:=MvPolynomial.X (2:Fin 4)
 let Hcap:=C-weights 2
 have hRC:weights 2 ≤ C:=by omega
 have hH:wt weights H ≤ Hcap:=wt_polyH_le weights F C hF
 have hG:wt weights G ≤ C:=
   wt_polyG_le_of_R_le_Y weights hX F C hRY hYC hF
 have hRwt:wt weights R=weights 2:=weighted_X weights 2
 have hRH:weights 2+Hcap=C:=by
   dsimp [Hcap]
   omega
 have hRH2:weights 2 ≤ Hcap:=by
   dsimp [Hcap]
   omega
 have hMX:wt weights (MvPolynomial.pderiv 0 M) ≤ A:=by
   have h:=wt_pderiv_le weights M 0 A hM
   rw [hX,Nat.sub_zero] at h
   exact h
 have hMY:wt weights (MvPolynomial.pderiv 1 M) ≤ A-weights 1:=
   wt_pderiv_le weights M 1 A hM
 have hMR:wt weights (MvPolynomial.pderiv 2 M) ≤ A-weights 2:=
   wt_pderiv_le weights M 2 A hM
 have hHX:wt weights (MvPolynomial.pderiv 0 H) ≤ Hcap:=by
   have h:=wt_pderiv_le weights H 0 Hcap hH
   rw [hX,Nat.sub_zero] at h
   exact h
 have hHY:wt weights (MvPolynomial.pderiv 1 H) ≤ Hcap-weights 1:=
   wt_pderiv_le weights H 1 Hcap hH
 have hHR:wt weights (MvPolynomial.pderiv 2 H) ≤ Hcap-weights 2:=
   wt_pderiv_le weights H 2 Hcap hH
 have hH2:wt weights (H^2) ≤ 2*Hcap:=
   (wt_pow_le weights H 2).trans (Nat.mul_le_mul_left 2 hH)
 have htermX:wt weights (H^2*MvPolynomial.pderiv 0 M) ≤
     A+2*Hcap:=by
   have h:=wt_mul_le weights (H^2) (MvPolynomial.pderiv 0 M)
   omega
 have htermY:wt weights (R*H^2*MvPolynomial.pderiv 1 M) ≤
     A+2*Hcap:=by
   have h1:=wt_mul_le weights R (H^2)
   have h2:=wt_mul_le weights (R*H^2) (MvPolynomial.pderiv 1 M)
   omega
 have htermR:wt weights (G*H*MvPolynomial.pderiv 2 M) ≤
     A+2*Hcap:=by
   have h1:=wt_mul_le weights G H
   have h2:=wt_mul_le weights (G*H) (MvPolynomial.pderiv 2 M)
   omega
 have hinnerX:wt weights (H*MvPolynomial.pderiv 0 H) ≤ 2*Hcap:=by
   have h:=wt_mul_le weights H (MvPolynomial.pderiv 0 H)
   omega
 have hinnerY:wt weights (R*H*MvPolynomial.pderiv 1 H) ≤
     2*Hcap:=by
   have h1:=wt_mul_le weights R H
   have h2:=wt_mul_le weights (R*H) (MvPolynomial.pderiv 1 H)
   omega
 have hinnerR:wt weights (G*MvPolynomial.pderiv 2 H) ≤ 2*Hcap:=by
   have h:=wt_mul_le weights G (MvPolynomial.pderiv 2 H)
   omega
 have hinner:wt weights
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H) ≤ 2*Hcap:=by
   exact (wt_add_le weights _ _).trans
     (max_le ((wt_add_le weights _ _).trans (max_le hinnerX hinnerY)) hinnerR)
 have hn:wt weights (((2*b:ℕ):Poly4 K))=0:=wt_natCast weights (2*b)
 have hnM:wt weights (((2*b:ℕ):Poly4 K)*M) ≤ A:=by
   have h:=wt_mul_le weights (((2*b:ℕ):Poly4 K)) M
   omega
 have hlast:wt weights (((2*b:ℕ):Poly4 K)*M*
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H)) ≤ A+2*Hcap:=by
   have h:=wt_mul_le weights (((2*b:ℕ):Poly4 K)*M)
     (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
       G*MvPolynomial.pderiv 2 H)
   omega
 change wt weights
     (H^2*MvPolynomial.pderiv 0 M+
       R*H^2*MvPolynomial.pderiv 1 M+
       G*H*MvPolynomial.pderiv 2 M-
       ((2*b:ℕ):Poly4 K)*M*
         (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
           G*MvPolynomial.pderiv 2 H)) ≤ A+2*Hcap
 exact (wt_sub_le weights _ _).trans
   (max_le ((wt_add_le weights _ _).trans
     (max_le ((wt_add_le weights _ _).trans (max_le htermX htermY)) htermR)) hlast)
theorem numerator_wt_le_equal_weight
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hRY:weights 2 ≤ weights 1)
   (hYC:weights 1 ≤ C) (hRR:2*weights 2 ≤ C)
   (hbase:weights 2 ≤ weights 1) (hF:wt weights F ≤ C) (b:ℕ):
   wt weights (numerator K F b) ≤
     weights 1+b*(2*(C-weights 2)):=by
 induction b with
 | zero =>
     rw [numerator_zero]
     unfold wt
     rw [weighted_X]
     simp
 | succ b ih =>
     rw [numerator_succ]
     have h:=numeratorStep_wt_le_equal_weight weights hX F
       (numerator K F b) b
       (weights 1+b*(2*(C-weights 2))) C hRY hYC hRR
       (hbase.trans (Nat.le_add_right _ _)) hF ih
     convert h using 1 <;> ring
theorem clearedTaylorNumerator_wt_le_equal_weight
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hRY:weights 2 ≤ weights 1)
   (hYC:weights 1 ≤ C) (hRR:2*weights 2 ≤ C)
   (hbase:weights 2 ≤ weights 1) (hF:wt weights F ≤ C)
   (w:ℕ) (coeffs:ℕ → K) (x:K):
   wt weights (clearedTaylorNumerator F w coeffs x) ≤
     weights 1+w*(2*(C-weights 2)):=by
 unfold clearedTaylorNumerator
 apply wt_sum_le
 intro j hj
 have hjw:j ≤ w:=by
   have:=Finset.mem_range.mp hj
   omega
 have hM:=numerator_wt_le_equal_weight weights hX F C hRY hYC hRR
   hbase hF j
 have hCM:wt weights (MvPolynomial.C (coeffs j)*numerator K F j) ≤
     weights 1+j*(2*(C-weights 2)):=by
   have hm:=wt_mul_le weights (MvPolynomial.C (coeffs j)) (numerator K F j)
   rw [wt_C,Nat.zero_add] at hm
   exact hm.trans hM
 have hH:wt weights (polyH K F) ≤ C-weights 2:=
   wt_polyH_le weights F C hF
 have hHP:wt weights (polyH K F^(2*(w-j))) ≤
     2*(w-j)*(C-weights 2):=
   (wt_pow_le weights (polyH K F) (2*(w-j))).trans
     (Nat.mul_le_mul_left _ hH)
 have hSX:=shiftedX_wt_eq_zero weights hX x
 have hSXP:wt weights
     ((MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)^j) ≤ 0:=by
   have hp:=wt_pow_le weights
     (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K) j
   rw [hSX,Nat.mul_zero] at hp
   exact hp
 have h1:=wt_mul_le weights
   (MvPolynomial.C (coeffs j)*numerator K F j)
   (polyH K F^(2*(w-j)))
 have h2:=wt_mul_le weights
   (MvPolynomial.C (coeffs j)*numerator K F j*
     polyH K F^(2*(w-j)))
   ((MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^j)
 simp only [commonNumeratorTerm]
 apply h2.trans
 calc
   wt weights (MvPolynomial.C (coeffs j)*numerator K F j*
       polyH K F^(2*(w-j)))+
       wt weights ((MvPolynomial.C x-MvPolynomial.X 0:Poly4 K)^j) ≤
       (weights 1+j*(2*(C-weights 2))+
         2*(w-j)*(C-weights 2))+0:=
     Nat.add_le_add (h1.trans (Nat.add_le_add hCM hHP)) hSXP
   _=weights 1+w*(2*(C-weights 2)):=by
     have hjw':j+(w-j)=w:=by omega
     calc
       (weights 1+j*(2*(C-weights 2))+
           2*(w-j)*(C-weights 2))+0=
           weights 1+(j+(w-j))*(2*(C-weights 2)):=by ring
       _=weights 1+w*(2*(C-weights 2)):=by rw [hjw']
theorem agreementNumerator_wt_le_equal_weight
   (weights:Fin 4 → ℕ) (hX:weights 0=0)
   (F:Poly4 K) (C:ℕ) (hRY:weights 2 ≤ weights 1)
   (hYC:weights 1 ≤ C) (hRR:2*weights 2 ≤ C)
   (hbase:weights 2 ≤ weights 1) (hF:wt weights F ≤ C)
   (w:ℕ) (coeffs:ℕ → K) (x u₀ u₁:K):
   wt weights (agreementNumerator F w coeffs x u₀ u₁) ≤
     max (weights 1) (weights 3)+w*(2*(C-weights 2)):=by
 have hTaylor:=clearedTaylorNumerator_wt_le_equal_weight weights hX F C hRY
   hYC hRR hbase hF w coeffs x
 have hA:=affineSeedPolynomial_wt_le weights u₀ u₁
 have hH:wt weights (polyH K F) ≤ C-weights 2:=
   wt_polyH_le weights F C hF
 have hHP:wt weights (polyH K F^(2*w)) ≤
     2*w*(C-weights 2):=
   (wt_pow_le weights (polyH K F) (2*w)).trans
     (Nat.mul_le_mul_left _ hH)
 have hprod:=wt_mul_le weights (affineSeedPolynomial u₀ u₁)
   (polyH K F^(2*w))
 unfold agreementNumerator
 apply (wt_sub_le weights _ _).trans
 apply max_le
 · exact hTaylor.trans (Nat.add_le_add_right (Nat.le_max_left _ _) _)
 · apply hprod.trans
   calc
     wt weights (affineSeedPolynomial u₀ u₁)+
         wt weights (polyH K F^(2*w)) ≤
         weights 3+2*w*(C-weights 2):=Nat.add_le_add hA hHP
     _ ≤ max (weights 1) (weights 3)+w*(2*(C-weights 2)):=by
       have hz:=Nat.le_max_right (weights 1) (weights 3)
       calc
         weights 3+2*w*(C-weights 2)=
             weights 3+w*(2*(C-weights 2)):=by ring
         _ ≤ max (weights 1) (weights 3)+w*(2*(C-weights 2)):=
           Nat.add_le_add_right hz _
end
end ProximityPrize.SubmissionLower.RCN179
end PackedLegacy_BY

/-! Packed from ProximityPrize.SubmissionLower.Z6. -/
section PackedLegacy_Z6
namespace ProximityPrize.SubmissionLower.RCN164
open scoped Classical
open RCN159 RCN159.ResidualStage RCN213 RCN173 RCN238 RCN095 RCN275
noncomputable section
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {p e:ℕ} [CharP Omega p] {flag:FlagDegree}
 {support:ResidualSupportParameters}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem recursive_stratified_incidence_bound
   (hphi:Function.Injective phi) {w a:ℕ}
   (S:ResidualStage phi Gamma x p e flag w support)
   (degreeCost unitCost U V:ℕ)
   (hwa:w < a)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (S.agreementFiber gamma).card)
   (hfiber:∀ D:S.TerminalDescendant,∀ i∈D.stage.nodes,
     ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i) →
     (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card ≤
       D.degree*degreeCost+unitCost)
   (hdegree:∀ k ≤ w,
     (S.nodes.card-k)*(a-w)*(w-k) ≤ U*(a-k))
   (hunit:∀ k ≤ w,
     (S.nodes.card-k)*(a-w) ≤ V*(a-k)):
   Gamma.card*(a-w) ≤ U*degreeCost+V*unitCost:=by
 classical
 obtain ⟨D⟩:=S.exists_terminal_descendant hphi
 let k:=w-D.degree
 have hk:k ≤ w:=Nat.sub_le w D.degree
 have hDle:D.degree ≤ w:=D.degree_le
 have hdegreeEq:D.degree=w-k:=by
   dsimp only [k]
   omega
 have hnodeEq:D.stage.nodes.card=S.nodes.card-k:=by
   simpa only [k] using D.nodes_card
 have hterminalAgreement:∀ gamma∈Gamma,
     a-k ≤ (D.stage.agreementFiber gamma).card:=by
   intro gamma hgamma
   exact (Nat.sub_le_sub_right (hagreement gamma hgamma) k).trans
     (by simpa only [k] using D.agreement_card gamma hgamma)
 have hterminalFiber:∀ i∈D.stage.nodes,
     (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card ≤
       D.degree*degreeCost+unitCost:=by
   intro i hi
   exact hfiber D i hi
     (D.stage.proper_agreement_of_terminal D.terminal hi)
 have hrawTerminal:=incidence_after_exempt_nodes
   (fun gamma i↦D.stage.Agrees gamma i)
   Gamma D.stage.nodes ∅ (a-k)
     (D.degree*degreeCost+unitCost)
   (by simp) hterminalAgreement (by
     intro i hi
     exact hterminalFiber i (by simpa using hi))
 have hraw:Gamma.card*(a-k) ≤
     (S.nodes.card-k)*((w-k)*degreeCost+unitCost):=by
   simpa only [Finset.card_empty,Nat.sub_zero,hnodeEq,hdegreeEq] using
     hrawTerminal
 exact stratified_incidence_linear Gamma.card S.nodes.card a w k
   degreeCost unitCost U V hk hwa hraw (hdegree k hk) (hunit k hk)
theorem recursive_scaled_stratified_incidence_bound
   (hphi:Function.Injective phi) {w a:ℕ}
   (S:ResidualStage phi Gamma x p e flag w support)
   (degreeCost unitCost U V:ℕ)
   (hwa:w < a)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (S.agreementFiber gamma).card)
   (hfiber:∀ D:S.TerminalDescendant,∀ i∈D.stage.nodes,
     ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i) →
     (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*(a-w) ≤
       D.degree*degreeCost+unitCost)
   (hdegree:∀ k ≤ w,
     (S.nodes.card-k)*(a-w)*(w-k) ≤ U*(a-k))
   (hunit:∀ k ≤ w,
     (S.nodes.card-k)*(a-w) ≤ V*(a-k)):
   Gamma.card*(a-w)^2 ≤ U*degreeCost+V*unitCost:=by
 classical
 obtain ⟨D⟩:=S.exists_terminal_descendant hphi
 let k:=w-D.degree
 have hk:k ≤ w:=Nat.sub_le w D.degree
 have hDle:D.degree ≤ w:=D.degree_le
 have hdegreeEq:D.degree=w-k:=by
   dsimp only [k]
   omega
 have hnodeEq:D.stage.nodes.card=S.nodes.card-k:=by
   simpa only [k] using D.nodes_card
 have hterminalAgreement:∀ gamma∈Gamma,
     a-k ≤ (D.stage.agreementFiber gamma).card:=by
   intro gamma hgamma
   exact (Nat.sub_le_sub_right (hagreement gamma hgamma) k).trans
     (by simpa only [k] using D.agreement_card gamma hgamma)
 let geometricCost:=D.degree*degreeCost+unitCost
 have hgap:0 < a-w:=Nat.sub_pos_of_lt hwa
 have hterminalFiberDiv:∀ i∈D.stage.nodes,
     (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card ≤
       geometricCost/(a-w):=by
   intro i hi
   apply (Nat.le_div_iff_mul_le hgap).mpr
   exact hfiber D i hi
     (D.stage.proper_agreement_of_terminal D.terminal hi)
 have hrawTerminal:=incidence_after_exempt_nodes
   (fun gamma i↦D.stage.Agrees gamma i)
   Gamma D.stage.nodes ∅ (a-k) (geometricCost/(a-w))
   (by simp) hterminalAgreement (by
     intro i hi
     exact hterminalFiberDiv i (by simpa using hi))
 have hrawScaled:(Gamma.card*(a-w))*(a-k) ≤
     (S.nodes.card-k)*((w-k)*degreeCost+unitCost):=by
   calc
     (Gamma.card*(a-w))*(a-k)=
         (Gamma.card*(a-k))*(a-w):=by ring
     _ ≤ ((D.stage.nodes.card*(geometricCost/(a-w)))*
         (a-w)):=Nat.mul_le_mul_right (a-w) (by
           simpa only [Finset.card_empty,Nat.sub_zero] using hrawTerminal)
     _=D.stage.nodes.card*
         ((geometricCost/(a-w))*(a-w)):=by ring
     _ ≤ D.stage.nodes.card*geometricCost:=
       Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
     _=(S.nodes.card-k)*
         ((w-k)*degreeCost+unitCost):=by
       simp only [hnodeEq,geometricCost,hdegreeEq]
 have hlinear:=stratified_incidence_linear
   (Gamma.card*(a-w)) S.nodes.card a w k
   degreeCost unitCost U V hk hwa hrawScaled
   (hdegree k hk) (hunit k hk)
 calc
   Gamma.card*(a-w)^2=(Gamma.card*(a-w))*(a-w):=by ring
   _ ≤ U*degreeCost+V*unitCost:=hlinear
end
end ProximityPrize.SubmissionLower.RCN164
end PackedLegacy_Z6

/-! Packed from ProximityPrize.SubmissionLower.U. -/
section PackedLegacy_U
namespace ProximityPrize.SubmissionLower.RCN276
open scoped BigOperators
open RCN174 RCN286 RCN095 RCN266
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
structure Profile where
 n:ℕ
 w:ℕ
 agreements:ℕ
 weightedCap:ℕ
 seedTotalCap:ℕ
 slopeCap:ℕ
 deriving DecidableEq,Repr
namespace Profile
def errors (p:Profile):ℕ:=p.n-p.agreements
def gap (p:Profile):ℕ:=p.agreements-p.w
def yCap (p:Profile):ℕ:=(p.weightedCap-1)/p.w
def degreeIncidence (p:Profile):ℕ:=
 (p.n*p.gap*p.w+p.agreements-1)/p.agreements
def unitIncidence (p:Profile):ℕ:=p.n-p.w
def surfaceFlag (p:Profile):FlagDegree:=
 ⟨p.seedTotalCap+p.slopeCap-p.yCap,
   p.yCap-p.slopeCap,p.slopeCap⟩
def derivativeFlag (p:Profile):FlagDegree:=
 ⟨p.surfaceFlag.zOnly,p.surfaceFlag.yz,p.surfaceFlag.all-1⟩
def agreementDirection (p:Profile):FlagDegree:=
 p.surfaceFlag+p.derivativeFlag
def rectangularSurfaceFlag (p:Profile):FlagDegree:=
 ⟨p.seedTotalCap,p.yCap,p.slopeCap⟩
def factorPrimary (p:Profile) (flag:FlagDegree):ℕ:=
 flagMixed flag p.agreementDirection p.agreementDirection*p.degreeIncidence^2+
   2*flagMixed flag p.agreementDirection unitYZFlag*
     p.degreeIncidence*p.unitIncidence+
   flagMixed flag unitYZFlag unitYZFlag*p.unitIncidence^2
def factorZTail (p:Profile) (flag:FlagDegree):ℕ:=
 (p.errors+1)*p.gap*
   (flagMixed flag p.agreementDirection unitZFlag*p.degreeIncidence+
     flagMixed flag unitYZFlag unitZFlag*p.unitIncidence)
def factorAllTail (p:Profile) (flag:FlagDegree):ℕ:=
 (p.errors+1)*p.gap*
   (flagMixed flag p.agreementDirection unitAllFlag*p.degreeIncidence+
     flagMixed flag unitYZFlag unitAllFlag*p.unitIncidence)
def factorRegularLedger (p:Profile) (flag:FlagDegree):ℕ:=
 p.factorPrimary flag+p.factorZTail flag+p.factorAllTail flag
def regularNumerator (p:Profile):ℕ:=
 p.factorRegularLedger p.rectangularSurfaceFlag
structure DegreeVector where
 y:ℕ
 r:ℕ
 z:ℕ
 deriving DecidableEq,Repr
def mixed (a b c:DegreeVector):ℕ:=
 a.y*b.r*c.z+a.y*b.z*c.r+
   a.r*b.y*c.z+a.r*b.z*c.y+
   a.z*b.y*c.r+a.z*b.r*c.y
def algebraicCap (p:Profile):ℕ:=
 (2*p.slopeCap-1)*p.seedTotalCap
def implicitWeightedCap (p:Profile):ℕ:=
 (2*p.slopeCap-1)*p.weightedCap
def implicitYCap (p:Profile):ℕ:=
 (p.implicitWeightedCap-1)/p.w
def liftedSurface (p:Profile):DegreeVector:=
 ⟨p.implicitYCap,1,p.algebraicCap⟩
def implicitCut (p:Profile):DegreeVector:=
 ⟨p.implicitYCap,0,p.algebraicCap⟩
def liftedLast (p:Profile):DegreeVector:=
 ⟨1+2*p.implicitWeightedCap*p.implicitYCap,
   p.implicitWeightedCap,
   2*p.implicitWeightedCap*p.algebraicCap⟩
def liftedAgreement (p:Profile):DegreeVector:=
 ⟨1+2*p.w*p.implicitYCap,
   p.w,2*p.w*p.algebraicCap+1⟩
def unitZ:DegreeVector:=⟨0,0,1⟩
def retainedSingularContribution (p:Profile):ℕ:=
 p.gap*
   (p.gap*
     (p.algebraicCap+2*p.algebraicCap^2+
       mixed p.liftedSurface p.implicitCut p.liftedLast+
       (p.errors+1)*mixed p.liftedSurface p.implicitCut unitZ)+
     (p.n-p.w)*
       mixed p.liftedSurface p.implicitCut p.liftedAgreement)
def totalNumerator (p:Profile):ℕ:=
 p.regularNumerator+p.retainedSingularContribution
def fixedCost (p:Profile):ℕ:=
 (p.totalNumerator+p.gap^2-1)/p.gap^2
end Profile
theorem factorRegularLedger_projection_decomposition
   (p:Profile) (flag:FlagDegree):
   p.factorRegularLedger flag=
     flag.zOnly*p.factorRegularLedger unitZFlag+
     flag.yz*p.factorRegularLedger unitYZFlag+
     flag.all*p.factorRegularLedger unitAllFlag:=by
 cases flag
 simp [Profile.factorRegularLedger,Profile.factorPrimary,
   Profile.factorZTail,Profile.factorAllTail,flagMixed,
   unitZFlag,unitYZFlag,unitAllFlag]
 ring
theorem sum_factorRegularLedger_le_flag
   {I:Type} [Fintype I] (p:Profile)
   (flag:I → FlagDegree) (cap:FlagDegree)
   (hz:(∑ i,(flag i).zOnly) ≤ cap.zOnly)
   (hyz:(∑ i,(flag i).yz) ≤ cap.yz)
   (hall:(∑ i,(flag i).all) ≤ cap.all):
   (∑ i,p.factorRegularLedger (flag i)) ≤
     p.factorRegularLedger cap:=by
 classical
 calc
   (∑ i,p.factorRegularLedger (flag i))=
       ∑ i,((flag i).zOnly*p.factorRegularLedger unitZFlag+
         (flag i).yz*p.factorRegularLedger unitYZFlag+
         (flag i).all*p.factorRegularLedger unitAllFlag):=by
     apply Finset.sum_congr rfl
     intro i _
     exact factorRegularLedger_projection_decomposition p (flag i)
   _=(∑ i,(flag i).zOnly)*p.factorRegularLedger unitZFlag+
       (∑ i,(flag i).yz)*p.factorRegularLedger unitYZFlag+
       (∑ i,(flag i).all)*p.factorRegularLedger unitAllFlag:=by
     simp only [Finset.sum_add_distrib,Finset.sum_mul]
   _ ≤ cap.zOnly*p.factorRegularLedger unitZFlag+
       cap.yz*p.factorRegularLedger unitYZFlag+
       cap.all*p.factorRegularLedger unitAllFlag:=
     Nat.add_le_add
       (Nat.add_le_add (Nat.mul_le_mul_right _ hz)
         (Nat.mul_le_mul_right _ hyz))
       (Nat.mul_le_mul_right _ hall)
   _=p.factorRegularLedger cap:=
     (factorRegularLedger_projection_decomposition p cap).symm
noncomputable section
variable {K:Type} [Field K]
theorem regularFlag_budgets
   (p:Profile) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (hw:0 < p.w)
   (hbox:Q∈globalCoefficientBox K p.weightedCap p.w
     p.seedTotalCap p.slopeCap):
   (∑ F:RegularIndex Q,(regularFlag Q F).zOnly) ≤ p.seedTotalCap∧
     (∑ F:RegularIndex Q,(regularFlag Q F).yz) ≤ p.yCap∧
     (∑ F:RegularIndex Q,(regularFlag Q F).all) ≤ p.slopeCap:=by
 classical
 have hb:=directFactor_input_budgets Q hQ p.weightedCap p.w
   p.seedTotalCap p.slopeCap hw hbox
 simp only [regularFlag,Finset.sum_coe_sort]
 exact ⟨hb.2.2,hb.1,hb.2.1⟩
theorem sum_factor_counts_rectangular_le
   (p:Profile) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (hw:0 < p.w)
   (hbox:Q∈globalCoefficientBox K p.weightedCap p.w
     p.seedTotalCap p.slopeCap)
   (count:RegularIndex Q → ℕ)
   (hcount:∀ F,count F*p.gap^2 ≤
     p.factorRegularLedger (regularFlag Q F)):
   (∑ F,count F)*p.gap^2 ≤ p.regularNumerator:=by
 have hcaps:=regularFlag_budgets p Q hQ hw hbox
 calc
   (∑ F,count F)*p.gap^2=∑ F,count F*p.gap^2:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ F,p.factorRegularLedger (regularFlag Q F):=
     Finset.sum_le_sum (fun F _↦hcount F)
   _ ≤ p.factorRegularLedger p.rectangularSurfaceFlag:=
     sum_factorRegularLedger_le_flag p (regularFlag Q)
       p.rectangularSurfaceFlag hcaps.1 hcaps.2.1 hcaps.2.2
   _=p.regularNumerator:=rfl
end
theorem combined_fixed_scaled_bound
   (p:Profile) (regularCount singularCount:ℕ)
   (hregular:regularCount*p.gap^2 ≤ p.regularNumerator)
   (hsingular:singularCount*p.gap^2 ≤
     p.retainedSingularContribution):
   (regularCount+singularCount)*p.gap^2 ≤ p.totalNumerator:=by
 calc
   (regularCount+singularCount)*p.gap^2=
       regularCount*p.gap^2+singularCount*p.gap^2:=by ring
   _ ≤ p.regularNumerator+p.retainedSingularContribution:=
     Nat.add_le_add hregular hsingular
   _=p.totalNumerator:=rfl
def meetProfile:Profile where
 n:=262144
 w:=131071
 agreements:=182807
 weightedCap:=4570175
 seedTotalCap:=598
 slopeCap:=6
theorem meet_parameter_values:
   meetProfile.errors=79337∧meetProfile.gap=51736∧
     meetProfile.yCap=34∧meetProfile.degreeIncidence=9724036071∧
     meetProfile.unitIncidence=131073∧
     meetProfile.surfaceFlag=⟨570,28,6⟩∧
     meetProfile.agreementDirection=⟨1140,56,11⟩∧
     meetProfile.rectangularSurfaceFlag=⟨598,34,6⟩:=by
 norm_num [meetProfile,Profile.errors,Profile.gap,Profile.yCap,
   Profile.degreeIncidence,Profile.unitIncidence,Profile.surfaceFlag,
   Profile.derivativeFlag,Profile.agreementDirection,
   Profile.rectangularSurfaceFlag] <;> rfl
theorem meet_regular_numerator_exact:
   meetProfile.regularNumerator=254256809306954333411326320:=by
 norm_num [Profile.regularNumerator,Profile.factorRegularLedger,
   Profile.factorPrimary,Profile.factorZTail,Profile.factorAllTail,
   Profile.rectangularSurfaceFlag,Profile.agreementDirection,
   Profile.derivativeFlag,Profile.surfaceFlag,Profile.degreeIncidence,
   Profile.unitIncidence,Profile.errors,Profile.gap,Profile.yCap,
   meetProfile,flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
theorem meet_singular_contribution_exact:
   meetProfile.retainedSingularContribution=
     2047455364091186323290168:=by
 norm_num [Profile.retainedSingularContribution,Profile.mixed,
   Profile.liftedSurface,Profile.implicitCut,Profile.liftedLast,
   Profile.liftedAgreement,Profile.unitZ,Profile.algebraicCap,
   Profile.implicitWeightedCap,Profile.implicitYCap,
   Profile.errors,Profile.gap,meetProfile]
theorem meet_total_numerator_exact:
   meetProfile.totalNumerator=256304264671045519734616488:=by
 rw [show meetProfile.totalNumerator=meetProfile.regularNumerator+
     meetProfile.retainedSingularContribution by rfl,
   meet_regular_numerator_exact,meet_singular_contribution_exact]
theorem meet_fixed_cost_exact:
   meetProfile.fixedCost=95756912943422943:=by
 rw [show meetProfile.fixedCost=
     (meetProfile.totalNumerator+meetProfile.gap^2-1)/
       meetProfile.gap^2 by rfl,
   meet_total_numerator_exact]
 norm_num [Profile.gap,meetProfile]
theorem meet_fixed_cost_lt_budget:
   meetProfile.fixedCost < 100000000000000000:=by
 rw [meet_fixed_cost_exact]
 norm_num
end ProximityPrize.SubmissionLower.RCN276
end PackedLegacy_U

/-! Packed from ProximityPrize.SubmissionLower.B8. -/
section PackedLegacy_B8
namespace ProximityPrize.SubmissionLower.RCN091
open scoped Classical
open RCN159 RCN164 RCN213 RCN275 RCN276 RCN238 RCN095
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 50000
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem fixedMeet_agreementDirection_eq:
   ResidualSupportParameters.fixedMeetSupport.agreementDirection=
     meetProfile.agreementDirection:=by
 rw [ResidualSupportParameters.fixedMeet_agreement_direction]
 exact meet_parameter_values.2.2.2.2.2.2.1.symm
theorem meet_incidence_values:
   meetProfile.degreeIncidence=9724036071∧
     meetProfile.unitIncidence=131073:=by
 exact ⟨meet_parameter_values.2.2.2.1,
   meet_parameter_values.2.2.2.2.1⟩
theorem meet_degree_incidence_ceiling:
   meetProfile.n*meetProfile.gap*meetProfile.w ≤
     meetProfile.degreeIncidence*meetProfile.agreements:=by
 norm_num [meetProfile,Profile.gap,Profile.degreeIncidence]
theorem meet_degree_part_bound (k:ℕ) (hk:k ≤ meetProfile.w):
   (meetProfile.n-k)*meetProfile.gap*(meetProfile.w-k) ≤
     meetProfile.degreeIncidence*(meetProfile.agreements-k):=by
 have hcross:=identity_degree_weight_cross_le meetProfile.n
   meetProfile.agreements meetProfile.w k hk
     (by norm_num [meetProfile]) (by norm_num [meetProfile])
 have hmul:=Nat.mul_le_mul_right (meetProfile.agreements-k)
   meet_degree_incidence_ceiling
 have htotal:
     ((meetProfile.n-k)*meetProfile.gap*(meetProfile.w-k))*
         meetProfile.agreements ≤
       (meetProfile.degreeIncidence*(meetProfile.agreements-k))*
         meetProfile.agreements:=by
   calc
     ((meetProfile.n-k)*meetProfile.gap*(meetProfile.w-k))*
           meetProfile.agreements=
         (meetProfile.n-k)*
           (meetProfile.agreements-meetProfile.w)*
           (meetProfile.w-k)*meetProfile.agreements:=by
             rfl
     _ ≤ meetProfile.n*(meetProfile.agreements-meetProfile.w)*
         meetProfile.w*(meetProfile.agreements-k):=hcross
     _ ≤ (meetProfile.degreeIncidence*meetProfile.agreements)*
         (meetProfile.agreements-k):=by
           simpa only [Profile.gap] using hmul
     _=(meetProfile.degreeIncidence*(meetProfile.agreements-k))*
         meetProfile.agreements:=by ring
 exact Nat.le_of_mul_le_mul_right htotal (by norm_num [meetProfile])
theorem meet_unit_part_bound (k:ℕ) (hk:k ≤ meetProfile.w):
   (meetProfile.n-k)*meetProfile.gap ≤
     meetProfile.unitIncidence*(meetProfile.agreements-k):=by
 simpa only [Profile.gap,Profile.unitIncidence] using
   identity_unit_weight_le meetProfile.n meetProfile.agreements
     meetProfile.w k hk (by norm_num [meetProfile]) (by norm_num [meetProfile])
def meetFactorDegreeCost (p:FlagDegree):ℕ:=
 (flagMixed p ResidualSupportParameters.fixedMeetSupport.agreementDirection
       ResidualSupportParameters.fixedMeetSupport.agreementDirection*
     meetProfile.degreeIncidence+
   flagMixed p ResidualSupportParameters.fixedMeetSupport.agreementDirection
       unitYZFlag*meetProfile.unitIncidence)+
 (meetProfile.errors+1)*meetProfile.gap*
   (flagMixed p ResidualSupportParameters.fixedMeetSupport.agreementDirection
       unitZFlag+
     flagMixed p ResidualSupportParameters.fixedMeetSupport.agreementDirection
       unitAllFlag)
def meetFactorUnitCost (p:FlagDegree):ℕ:=
 (flagMixed p ResidualSupportParameters.fixedMeetSupport.agreementDirection
       unitYZFlag*meetProfile.degreeIncidence+
   flagMixed p unitYZFlag unitYZFlag*meetProfile.unitIncidence)+
 (meetProfile.errors+1)*meetProfile.gap*
   (flagMixed p unitYZFlag unitZFlag+
     flagMixed p unitYZFlag unitAllFlag)
theorem meet_incidence_cost_eq_factorRegularLedger (p:FlagDegree):
   meetProfile.degreeIncidence*meetFactorDegreeCost p+
     meetProfile.unitIncidence*meetFactorUnitCost p=
     meetProfile.factorRegularLedger p:=by
 simp only [meetFactorDegreeCost,meetFactorUnitCost]
 rw [fixedMeet_agreementDirection_eq]
 simp only [Profile.factorRegularLedger,Profile.factorPrimary,
   Profile.factorZTail,Profile.factorAllTail]
 ring
theorem recursive_scaled_factor_6656
   (hphi:Function.Injective phi)
   (S:ResidualStage phi Gamma x pchar meetProfile.errors flag meetProfile.w
     ResidualSupportParameters.fixedMeetSupport)
   (p:FlagDegree)
   (hnodes:S.nodes.card=meetProfile.n)
   (hagreement:∀ gamma∈Gamma,
     meetProfile.agreements ≤ (S.agreementFiber gamma).card)
   (hfiber:∀ D:S.TerminalDescendant,∀ i∈D.stage.nodes,
     ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i) →
     (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*
         meetProfile.gap ≤
       D.degree*meetFactorDegreeCost p+meetFactorUnitCost p):
   Gamma.card*meetProfile.gap^2 ≤
     meetProfile.factorRegularLedger p:=by
 have h:=recursive_scaled_stratified_incidence_bound
   hphi S (meetFactorDegreeCost p) (meetFactorUnitCost p)
     meetProfile.degreeIncidence meetProfile.unitIncidence
     (by norm_num [meetProfile]) hagreement hfiber
     (by
       intro k hk
       rw [hnodes]
       exact meet_degree_part_bound k hk)
     (by
       intro k hk
       rw [hnodes]
       exact meet_unit_part_bound k hk)
 calc
   Gamma.card*meetProfile.gap^2 ≤
       meetProfile.degreeIncidence*meetFactorDegreeCost p+
         meetProfile.unitIncidence*meetFactorUnitCost p:=by
           simpa only [Profile.gap] using h
   _=meetProfile.factorRegularLedger p:=
     meet_incidence_cost_eq_factorRegularLedger p
end
end ProximityPrize.SubmissionLower.RCN091
end PackedLegacy_B8

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier13 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.EN. -/
section PackedLegacy_EN
namespace ProximityPrize.SubmissionLower.RCN141
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN167 RCN169 RCN290 RCN238 RCN266 RCN140 RCN291 RCN294 RCN318 RCN276
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 35000
def prime6656:ℕ:=2130706433
def meetTightProfile:TightParameters where
 n:=meetProfile.n
 w:=meetProfile.w
 a:=meetProfile.agreements
 D:=meetProfile.weightedCap
 L:=meetProfile.seedTotalCap
 s:=meetProfile.slopeCap
theorem meet_tight_parameter_values:
   meetTightProfile.errors=meetProfile.errors∧
     meetTightProfile.gap=meetProfile.gap∧
     meetTightProfile.implicitYCap=meetProfile.implicitYCap∧
     meetTightProfile.algebraicCap=meetProfile.algebraicCap:=by
 norm_num [meetTightProfile,meetProfile,TightParameters.errors,
   TightParameters.gap,TightParameters.implicitYCap,
   TightParameters.algebraicCap,TightParameters.kappa,
   Profile.errors,Profile.gap,Profile.implicitYCap,
   Profile.implicitWeightedCap,Profile.algebraicCap]
theorem meet_characteristic_gates:
   meetProfile.slopeCap < prime6656∧
     meetProfile.algebraicCap < prime6656∧
     meetProfile.implicitWeightedCap < prime6656:=by
 norm_num [meetProfile,prime6656,Profile.algebraicCap,
   Profile.implicitWeightedCap]
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem meet_card_le_regular_sum_add_singular
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime6656]
   (hbox:Q∈globalCoefficientBox K meetProfile.weightedCap meetProfile.w
     meetProfile.seedTotalCap meetProfile.slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0):
   Gamma.card ≤
     (∑ F:RegularIndex Q,(regularSeeds Q selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=by
 classical
 have hdecomp:=selected_seed_decomposition Q hQ
   meetProfile.weightedCap meetProfile.w meetProfile.seedTotalCap
   meetProfile.slopeCap prime6656
   (by norm_num [meetProfile])
   meet_characteristic_gates.1
   (by norm_num [meetProfile])
   (by norm_num [meetProfile])
   (by norm_num [meetProfile,Profile.algebraicCap])
   meet_characteristic_gates.2.1 hbox Gamma selected hsolution
 let regularUnion:=Finset.univ.biUnion (regularSeeds Q selected Gamma)
 have hsub:Gamma ⊆ regularUnion ∪ singularSeeds Q selected Gamma:=by
   intro gamma hgamma
   by_cases hexc:gamma∈
       exceptionalSeeds (singularAuxiliary Q) Gamma selected
   · apply Finset.mem_union.mpr
     right
     apply Finset.mem_union.mpr
     right
     exact hexc
   · obtain ⟨F,hF,hreg⟩ | ⟨q,hq,himp⟩:=
       hdecomp.2.1 gamma hgamma hexc
     · apply Finset.mem_union.mpr
       left
       apply Finset.mem_biUnion.mpr
       exact ⟨⟨F,hF⟩,Finset.mem_univ _,
         Finset.mem_filter.mpr ⟨hgamma,hreg⟩⟩
     · apply Finset.mem_union.mpr
       right
       apply Finset.mem_union.mpr
       left
       apply Finset.mem_biUnion.mpr
       exact ⟨⟨q,hq⟩,Finset.mem_univ _,
         Finset.mem_filter.mpr ⟨hgamma,himp⟩⟩
 calc
   Gamma.card ≤ (regularUnion ∪ singularSeeds Q selected Gamma).card:=
     Finset.card_le_card hsub
   _ ≤ regularUnion.card+(singularSeeds Q selected Gamma).card:=
     Finset.card_union_le _ _
   _ ≤ (∑ F:RegularIndex Q,(regularSeeds Q selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=
     Nat.add_le_add_right Finset.card_biUnion_le _
def meetImplicitCost (Q:MvPolynomial (Fin 4) K)
   (q:ImplicitIndex Q):RCN223.DegreeVector:=
 ⟨pairYCost q.1,pairRCost q.1,pairZCost q.1⟩
theorem meet_singularSeeds_scaled_bound_of_implicit_pairs
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime6656]
   (hbox:Q∈globalCoefficientBox K meetProfile.weightedCap meetProfile.w
     meetProfile.seedTotalCap meetProfile.slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hpair:∀ q:ImplicitIndex Q,
     (implicitSeeds Q selected Gamma q).card*meetProfile.gap ≤
       (meetProfile.n-meetProfile.w)*
           dot meetTightProfile.agreement (meetImplicitCost Q q)+
         (meetProfile.errors+1)*meetProfile.gap*
           (meetImplicitCost Q q).z):
   (singularSeeds Q selected Gamma).card*meetProfile.gap^2 ≤
     meetProfile.retainedSingularContribution:=by
 classical
 have hdecomp:=selected_seed_decomposition Q hQ
   meetProfile.weightedCap meetProfile.w meetProfile.seedTotalCap
   meetProfile.slopeCap prime6656
   (by norm_num [meetProfile])
   meet_characteristic_gates.1
   (by norm_num [meetProfile])
   (by norm_num [meetProfile])
   (by norm_num [meetProfile,Profile.algebraicCap])
   meet_characteristic_gates.2.1 hbox Gamma selected hsolution
 have hy:(∑ q:ImplicitIndex Q,(meetImplicitCost Q q).y) ≤
     meetTightProfile.algebraicCap:=by
   simpa only [meetImplicitCost,Finset.sum_coe_sort,
     meet_tight_parameter_values.2.2.2,Profile.algebraicCap] using
       hdecomp.2.2.2.1
 have hr:(∑ q:ImplicitIndex Q,(meetImplicitCost Q q).r) ≤
     2*meetTightProfile.implicitYCap*meetTightProfile.algebraicCap:=by
   simpa only [meetImplicitCost,Finset.sum_coe_sort,
     meet_tight_parameter_values.2.2.1,
     meet_tight_parameter_values.2.2.2,Profile.implicitYCap,
     Profile.implicitWeightedCap,Profile.algebraicCap] using
       hdecomp.2.2.2.2.1
 have hz:(∑ q:ImplicitIndex Q,(meetImplicitCost Q q).z) ≤
     meetTightProfile.implicitYCap:=by
   simpa only [meetImplicitCost,Finset.sum_coe_sort,
     meet_tight_parameter_values.2.2.1,Profile.implicitYCap,
     Profile.implicitWeightedCap] using hdecomp.2.2.2.2.2
 have hexc:
     (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card ≤
       2*meetTightProfile.algebraicCap^2:=by
   simpa only [meet_tight_parameter_values.2.2.2,
     Profile.algebraicCap] using hdecomp.1
 have hpair':∀ q:ImplicitIndex Q,
     (implicitSeeds Q selected Gamma q).card*meetTightProfile.gap ≤
       (meetTightProfile.n-meetTightProfile.w)*
           dot meetTightProfile.agreement (meetImplicitCost Q q)+
         (meetTightProfile.errors+1)*meetTightProfile.gap*
           (meetImplicitCost Q q).z:=by
   intro q
   simpa only [meetTightProfile,TightParameters.errors,
     TightParameters.gap,Profile.errors,Profile.gap] using hpair q
 have hsum:=meetTightProfile.with_exceptions_bound
   (fun q:ImplicitIndex Q↦(implicitSeeds Q selected Gamma q).card)
   (meetImplicitCost Q)
   (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card
   hy hr hz hpair' hexc
 have hunion:=singularSeeds_card_le_sum Q selected Gamma
 have hgap:meetTightProfile.gap=meetProfile.gap:=
   meet_tight_parameter_values.2.1
 have htight:meetTightProfile.tightNumerator*meetProfile.gap ≤
     meetProfile.retainedSingularContribution:=by
   norm_num [meetTightProfile,meetProfile,TightParameters.tightNumerator,
     TightParameters.coreNumerator,TightParameters.aggregateCost,
     TightParameters.agreement,TightParameters.implicitYCap,
     TightParameters.algebraicCap,TightParameters.kappa,
     TightParameters.errors,TightParameters.gap,Profile.errors,
     Profile.gap,Profile.retainedSingularContribution,Profile.mixed,
     Profile.liftedSurface,Profile.implicitCut,Profile.liftedLast,
     Profile.liftedAgreement,Profile.unitZ,Profile.algebraicCap,
     Profile.implicitWeightedCap,Profile.implicitYCap,dot]
 calc
   (singularSeeds Q selected Gamma).card*meetProfile.gap^2 ≤
       (((∑ q:ImplicitIndex Q,
         (implicitSeeds Q selected Gamma q).card)+
         (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card)*
           meetProfile.gap)*meetProfile.gap:=by
     calc
       _ ≤ ((∑ q:ImplicitIndex Q,
             (implicitSeeds Q selected Gamma q).card)+
             (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card)*
             meetProfile.gap^2:=
         Nat.mul_le_mul_right _ hunion
       _=(((∑ q:ImplicitIndex Q,
             (implicitSeeds Q selected Gamma q).card)+
             (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card)*
               meetProfile.gap)*meetProfile.gap:=by ring
   _ ≤ meetTightProfile.tightNumerator*meetProfile.gap:=by
     rw [←hgap]
     exact Nat.mul_le_mul_right meetTightProfile.gap hsum
   _ ≤ meetProfile.retainedSingularContribution:=htight
theorem meet_global_count_lt_fixed_cost_of_local_counts
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime6656]
   (hbox:Q∈globalCoefficientBox K meetProfile.weightedCap meetProfile.w
     meetProfile.seedTotalCap meetProfile.slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hregular:∀ F:RegularIndex Q,
     (regularSeeds Q selected Gamma F).card*meetProfile.gap^2 ≤
       meetProfile.factorRegularLedger (regularFlag Q F))
   (hpair:∀ q:ImplicitIndex Q,
     (implicitSeeds Q selected Gamma q).card*meetProfile.gap ≤
       (meetProfile.n-meetProfile.w)*
           dot meetTightProfile.agreement (meetImplicitCost Q q)+
         (meetProfile.errors+1)*meetProfile.gap*
           (meetImplicitCost Q q).z):
   Gamma.card < 95756912943422943:=by
 have hcover:=meet_card_le_regular_sum_add_singular Q hQ hbox selected
   Gamma hsolution
 have hreg:=sum_factor_counts_rectangular_le meetProfile Q hQ
   (by norm_num [meetProfile]) hbox
   (fun F:RegularIndex Q↦(regularSeeds Q selected Gamma F).card)
   hregular
 have hsing:=meet_singularSeeds_scaled_bound_of_implicit_pairs Q hQ hbox
   selected Gamma hsolution hpair
 have hscaled:Gamma.card*meetProfile.gap^2 ≤
     meetProfile.totalNumerator:=by
   calc
     Gamma.card*meetProfile.gap^2 ≤
         ((∑ F:RegularIndex Q,
           (regularSeeds Q selected Gamma F).card)+
           (singularSeeds Q selected Gamma).card)*meetProfile.gap^2:=
       Nat.mul_le_mul_right _ hcover
     _=(∑ F:RegularIndex Q,
           (regularSeeds Q selected Gamma F).card)*meetProfile.gap^2+
         (singularSeeds Q selected Gamma).card*meetProfile.gap^2:=by ring
     _ ≤ meetProfile.regularNumerator+
         meetProfile.retainedSingularContribution:=Nat.add_le_add hreg hsing
     _=meetProfile.totalNumerator:=rfl
 have hstrict:meetProfile.totalNumerator <
     95756912943422943*meetProfile.gap^2:=by
   rw [meet_total_numerator_exact]
   norm_num [meetProfile,Profile.gap]
 exact Nat.lt_of_mul_lt_mul_right (hscaled.trans_lt hstrict)
end
end ProximityPrize.SubmissionLower.RCN141
end PackedLegacy_EN

/-! Packed from ProximityPrize.SubmissionLower.AG. -/
section PackedLegacy_AG
namespace ProximityPrize.SubmissionLower.RCN292
open scoped Classical BigOperators
open RCN286 RCN169 RCN167 RCN290 RCN293 RCN174 RCN319 RCN081 RCN238 RCN243 RCN291 RCN318 RCN172 RCN294
noncomputable section
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev TightParameters:=RCN318.TightParameters
namespace TightParameters
theorem implicitVector_budgets_of_profile
   (P:TightParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {p:ℕ} [CharP K p]
   (hbox:Q∈globalCoefficientBox K P.D P.w P.L P.s)
   (hs:1 ≤ P.s) (hsSmall:P.s < p) (hw:1 ≤ P.w):
   (∑ q:ImplicitIndex Q,(implicitVector Q q).y) ≤ P.algebraicCap∧
     (∑ q:ImplicitIndex Q,(implicitVector Q q).r) ≤
       2*P.implicitYCap*P.algebraicCap∧
     (∑ q:ImplicitIndex Q,(implicitVector Q q).z) ≤ P.implicitYCap:=by
 classical
 obtain ⟨hJ,hJboxRaw⟩:=singularAuxiliary_nonzero_mem_box Q
   P.D P.w P.L P.s p hQ hs hsSmall hbox
 have hJbox:singularAuxiliary Q∈
     globalCoefficientBox K (P.kappa*P.D) P.w P.algebraicCap 0:=by
   simpa [RCN318.TightParameters.kappa,
     RCN318.TightParameters.algebraicCap] using hJboxRaw
 have hb:=implicitPair_input_budgets (singularAuxiliary Q) hJ
   (P.kappa*P.D) P.w P.algebraicCap (by omega) hJbox
 simpa only [implicitVector,Finset.sum_coe_sort,
   RCN318.TightParameters.implicitYCap] using hb
theorem exceptionalSeeds_bound_of_profile
   (P:TightParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {p:ℕ} [CharP K p]
   (hbox:Q∈globalCoefficientBox K P.D P.w P.L P.s)
   (hs:1 ≤ P.s) (hsSmall:P.s < p)
   (hj:1 ≤ P.algebraicCap)
   (hjSmall:P.algebraicCap < p)
   (selected:K → Polynomial K) (Gamma:Finset K):
   (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card ≤
     2*P.algebraicCap^2:=by
 classical
 obtain ⟨hJ,hJboxRaw⟩:=singularAuxiliary_nonzero_mem_box Q
   P.D P.w P.L P.s p hQ hs hsSmall hbox
 have hJbox:singularAuxiliary Q∈
     globalCoefficientBox K (P.kappa*P.D) P.w P.algebraicCap 0:=by
   simpa [RCN318.TightParameters.kappa,
     RCN318.TightParameters.algebraicCap] using hJboxRaw
 have hJR:(singularAuxiliary Q).degreeOf 2=0:=
   Nat.eq_zero_of_le_zero
     (degreeOf_R_le_of_mem_box _ _ _ _ _ hJbox)
 have hJY:(singularAuxiliary Q).degreeOf 1 ≤ P.algebraicCap:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   have hh:=(hJbox hd).1
   omega
 have hJZ:(singularAuxiliary Q).degreeOf 3 ≤ P.algebraicCap:=
   degreeOf_Z_le_of_mem_box _ _ _ _ _ hJbox
 exact exceptionalSeeds_card_le (singularAuxiliary Q) hJ hJR
   P.algebraicCap p hj hjSmall hJY hJZ Gamma selected
variable {Iota:Type}
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem implicitSeeds_pair_bound_of_profile
   (P:TightParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {p:ℕ} [CharP K p]
   (hbox:Q∈globalCoefficientBox K P.D P.w P.L P.s)
   (hs:1 ≤ P.s) (hsSmall:P.s < p)
   (hw:1 ≤ P.w) (hchar:P.w < p)
   (hDw:P.w < P.kappa*P.D)
   (hjYSmall:P.implicitYCap < p)
   (hjZSmall:P.algebraicCap < p)
   (hmixedSmall:2*P.implicitYCap*P.algebraicCap < p)
   (hwa:P.w < P.a) (han:P.a ≤ P.n)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors)
   (q:ImplicitIndex Q):
   (implicitSeeds Q selected Gamma q).card*P.gap ≤
     (P.n-P.w)*dot P.agreement (implicitVector Q q)+
       (P.errors+1)*P.gap*(implicitVector Q q).z:=by
 classical
 obtain ⟨hJ,hJboxRaw⟩:=singularAuxiliary_nonzero_mem_box Q
   P.D P.w P.L P.s p hQ hs hsSmall hbox
 have hJbox:singularAuxiliary Q∈
     globalCoefficientBox K (P.kappa*P.D) P.w P.algebraicCap 0:=by
   simpa [RCN318.TightParameters.kappa,
     RCN318.TightParameters.algebraicCap] using hJboxRaw
 obtain ⟨_hA,hG,hGR,hAbox,hGbox,hproper⟩:=
   implicitPair_data (singularAuxiliary Q) hJ
     (P.kappa*P.D) P.w P.algebraicCap hw hDw hJbox q.1 q.2
 have hsub:=implicitSeeds_subset Q selected Gamma q
 have hpair:=implicit_pair_seed_bound q.1.1 q.1.2 hG hGR hproper
   (P.kappa*P.D) P.w P.implicitYCap P.algebraicCap
   p P.n P.a P.errors hAbox hGbox rfl selected
   (implicitSeeds Q selected Gamma q) nodes x u0 u1 hinj hnodes
   hw hchar hwa han hjYSmall hjZSmall hmixedSmall
   (fun gamma hgamma => hdegree gamma (hsub hgamma))
   (fun gamma hgamma =>
     (implicitSeeds_solution Q selected Gamma q gamma hgamma).1)
   (fun gamma hgamma =>
     (implicitSeeds_solution Q selected Gamma q gamma hgamma).2.2.1)
   (fun gamma hgamma =>
     (implicitSeeds_solution Q selected Gamma q gamma hgamma).2.2.2)
   (fun gamma hgamma => hagreement gamma (hsub hgamma))
   (noLargeSelectedPencil_mono selected Gamma _ P.w P.errors hsub hnoPencil)
 simpa [implicitVector,
   RCN318.TightParameters.agreement,
   RCN318.TightParameters.errors,
   RCN318.TightParameters.gap,dot] using hpair
theorem singularSeeds_tight_gap_bound
   (P:TightParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {p:ℕ} [CharP K p]
   (hbox:Q∈globalCoefficientBox K P.D P.w P.L P.s)
   (hs:1 ≤ P.s) (hsSmall:P.s < p)
   (hw:1 ≤ P.w) (hchar:P.w < p)
   (hDw:P.w < P.kappa*P.D)
   (hj:1 ≤ P.algebraicCap)
   (hjYSmall:P.implicitYCap < p)
   (hjZSmall:P.algebraicCap < p)
   (hmixedSmall:2*P.implicitYCap*P.algebraicCap < p)
   (hwa:P.w < P.a) (han:P.a ≤ P.n)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors):
   (singularSeeds Q selected Gamma).card*P.gap ≤ P.tightNumerator:=by
 have hcaps:=P.implicitVector_budgets_of_profile Q hQ hbox hs hsSmall hw
 have hexc:=P.exceptionalSeeds_bound_of_profile Q hQ hbox hs hsSmall
   hj hjZSmall selected Gamma
 have hsum:=P.with_exceptions_bound
   (fun q:ImplicitIndex Q => (implicitSeeds Q selected Gamma q).card)
   (implicitVector Q)
   (exceptionalSeeds (singularAuxiliary Q) Gamma selected).card
   hcaps.1 hcaps.2.1 hcaps.2.2
   (P.implicitSeeds_pair_bound_of_profile Q hQ hbox hs hsSmall hw hchar
     hDw hjYSmall hjZSmall hmixedSmall hwa han selected Gamma nodes x u0 u1
     hinj hnodes hdegree hagreement hnoPencil)
   hexc
 exact (Nat.mul_le_mul_right P.gap
   (singularSeeds_card_le_sum Q selected Gamma)).trans hsum
theorem singularSeeds_count_le_countCap
   (P:TightParameters) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {p:ℕ} [CharP K p]
   (hbox:Q∈globalCoefficientBox K P.D P.w P.L P.s)
   (hs:1 ≤ P.s) (hsSmall:P.s < p)
   (hw:1 ≤ P.w) (hchar:P.w < p)
   (hDw:P.w < P.kappa*P.D)
   (hj:1 ≤ P.algebraicCap)
   (hjYSmall:P.implicitYCap < p)
   (hjZSmall:P.algebraicCap < p)
   (hmixedSmall:2*P.implicitYCap*P.algebraicCap < p)
   (hwa:P.w < P.a) (han:P.a ≤ P.n)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=P.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ P.w)
   (hagreement:∀ gamma∈Gamma,
     P.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma P.w P.errors):
   (singularSeeds Q selected Gamma).card ≤ P.countCap:=by
 apply P.count_le_countCap _ (by
   simpa [RCN318.TightParameters.gap] using
     Nat.sub_pos_of_lt hwa)
 exact P.singularSeeds_tight_gap_bound Q hQ hbox hs hsSmall hw hchar hDw
   hj hjYSmall hjZSmall hmixedSmall hwa han selected Gamma nodes x u0 u1
   hinj hnodes hdegree hagreement hnoPencil
end TightParameters
def firstResidualQ2:TightParameters:=
 ⟨262144,131071,182807,8591929,598,14⟩
def secondResidualGcd12:TightParameters:=
 ⟨262144,131071,182807,4570175,598,7⟩
theorem optimized_pivot_values:
   firstResidualQ2.implicitYCap=1769∧
     firstResidualQ2.algebraicCap=16146∧
     firstResidualQ2.tightNumerator=2944211023232807391∧
     firstResidualQ2.countCap=56908362131452∧
     secondResidualGcd12.implicitYCap=453∧
     secondResidualGcd12.algebraicCap=7774∧
     secondResidualGcd12.tightNumerator=363014145446108303∧
     secondResidualGcd12.countCap=7016664323606:=by
 norm_num [firstResidualQ2,secondResidualGcd12,
   TightParameters.countCap,TightParameters.tightNumerator,
   TightParameters.coreNumerator,TightParameters.aggregateCost,
   TightParameters.agreement,TightParameters.implicitYCap,
   TightParameters.algebraicCap,TightParameters.kappa,
   TightParameters.errors,TightParameters.gap,dot]
theorem optimized_pivot_characteristic_gates:
   firstResidualQ2.s < 2130706433∧
     firstResidualQ2.w < 2130706433∧
     firstResidualQ2.implicitYCap < 2130706433∧
     firstResidualQ2.algebraicCap < 2130706433∧
     2*firstResidualQ2.implicitYCap*firstResidualQ2.algebraicCap < 2130706433∧
     secondResidualGcd12.s < 2130706433∧
     secondResidualGcd12.w < 2130706433∧
     secondResidualGcd12.implicitYCap < 2130706433∧
     secondResidualGcd12.algebraicCap < 2130706433∧
     2*secondResidualGcd12.implicitYCap*secondResidualGcd12.algebraicCap < 2130706433:=by
 norm_num [firstResidualQ2,secondResidualGcd12,
   TightParameters.implicitYCap,TightParameters.algebraicCap,
   TightParameters.kappa]
end
end ProximityPrize.SubmissionLower.RCN292
end PackedLegacy_AG

/-! Packed from ProximityPrize.SubmissionLower.J6. -/
section PackedLegacy_J6
namespace ProximityPrize.SubmissionLower.RCN092
open scoped Classical BigOperators
open RCN174 RCN319 RCN238 RCN266 RCN140 RCN291 RCN294 RCN318 RCN276 RCN141 RCN292
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 35000
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem meet_tight_scaled_le_retained:
   meetTightProfile.tightNumerator*meetProfile.gap ≤
     meetProfile.retainedSingularContribution:=by
 norm_num [meetTightProfile,meetProfile,TightParameters.tightNumerator,
   TightParameters.coreNumerator,TightParameters.aggregateCost,
   TightParameters.agreement,TightParameters.implicitYCap,
   TightParameters.algebraicCap,TightParameters.kappa,
   TightParameters.errors,TightParameters.gap,Profile.errors,
   Profile.gap,Profile.retainedSingularContribution,Profile.mixed,
   Profile.liftedSurface,Profile.implicitCut,Profile.liftedLast,
   Profile.liftedAgreement,Profile.unitZ,Profile.algebraicCap,
   Profile.implicitWeightedCap,Profile.implicitYCap,dot]
theorem meet_singularSeeds_tight_gap_bound
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   [CharP K prime6656]
   (hbox:Q∈globalCoefficientBox K meetProfile.weightedCap meetProfile.w
     meetProfile.seedTotalCap meetProfile.slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=meetProfile.n)
   (hdegree:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ meetProfile.w)
   (hagreement:∀ gamma∈Gamma,
     meetProfile.agreements ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma meetProfile.w
     meetProfile.errors):
   (singularSeeds Q selected Gamma).card*meetTightProfile.gap ≤
     meetTightProfile.tightNumerator:=by
 exact
   RCN292.TightParameters.singularSeeds_tight_gap_bound
     meetTightProfile Q hQ hbox
     (by norm_num [meetTightProfile,meetProfile])
     (by norm_num [meetTightProfile,meetProfile,prime6656])
     (by norm_num [meetTightProfile,meetProfile])
     (by norm_num [meetTightProfile,meetProfile,prime6656])
     (by norm_num [meetTightProfile,meetProfile,TightParameters.kappa])
     (by norm_num [meetTightProfile,meetProfile,
       TightParameters.algebraicCap,TightParameters.kappa])
     (by norm_num [meetTightProfile,meetProfile,prime6656,
       TightParameters.implicitYCap,TightParameters.kappa])
     (by norm_num [meetTightProfile,meetProfile,prime6656,
       TightParameters.algebraicCap,TightParameters.kappa])
     (by norm_num [meetTightProfile,meetProfile,prime6656,
       TightParameters.implicitYCap,TightParameters.algebraicCap,
       TightParameters.kappa])
     (by norm_num [meetTightProfile,meetProfile])
     (by norm_num [meetTightProfile,meetProfile])
     selected Gamma nodes x u0 u1 hinj
     (by simpa [meetTightProfile] using hnodes)
     (by simpa [meetTightProfile] using hdegree)
     (by simpa [meetTightProfile] using hagreement)
     (by simpa [meetTightProfile,TightParameters.errors,
       Profile.errors] using hnoPencil)
theorem meet_singularSeeds_scaled_bound
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   [CharP K prime6656]
   (hbox:Q∈globalCoefficientBox K meetProfile.weightedCap meetProfile.w
     meetProfile.seedTotalCap meetProfile.slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=meetProfile.n)
   (hdegree:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ meetProfile.w)
   (hagreement:∀ gamma∈Gamma,
     meetProfile.agreements ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma meetProfile.w
     meetProfile.errors):
   (singularSeeds Q selected Gamma).card*meetProfile.gap^2 ≤
     meetProfile.retainedSingularContribution:=by
 have hbase:=meet_singularSeeds_tight_gap_bound Q hQ hbox selected Gamma
   nodes x u0 u1 hinj hnodes hdegree hagreement hnoPencil
 have hgap:meetTightProfile.gap=meetProfile.gap:=
   meet_tight_parameter_values.2.1
 have hscaled:
     (singularSeeds Q selected Gamma).card*meetProfile.gap^2 ≤
       meetTightProfile.tightNumerator*meetProfile.gap:=by
   rw [←hgap]
   calc
     (singularSeeds Q selected Gamma).card*meetTightProfile.gap^2=
         ((singularSeeds Q selected Gamma).card*meetTightProfile.gap)*
           meetTightProfile.gap:=by ring
     _ ≤ meetTightProfile.tightNumerator*meetTightProfile.gap:=
       Nat.mul_le_mul_right meetTightProfile.gap hbase
 exact hscaled.trans meet_tight_scaled_le_retained
theorem meet_global_count_lt_fixedCost_of_regular_factors
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   [CharP K prime6656]
   (hbox:Q∈globalCoefficientBox K meetProfile.weightedCap meetProfile.w
     meetProfile.seedTotalCap meetProfile.slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=meetProfile.n)
   (hdegree:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ meetProfile.w)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hagreement:∀ gamma∈Gamma,
     meetProfile.agreements ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma meetProfile.w
     meetProfile.errors)
   (hregular:∀ F:RegularIndex Q,
     (regularSeeds Q selected Gamma F).card*meetProfile.gap^2 ≤
       meetProfile.factorRegularLedger (regularFlag Q F)):
   Gamma.card < meetProfile.fixedCost:=by
 have hcover:=meet_card_le_regular_sum_add_singular Q hQ hbox selected
   Gamma hsolution
 have hreg:=sum_factor_counts_rectangular_le meetProfile Q hQ
   (by norm_num [meetProfile]) hbox
   (fun F:RegularIndex Q => (regularSeeds Q selected Gamma F).card)
   hregular
 have hsing:=meet_singularSeeds_scaled_bound Q hQ hbox selected Gamma
   nodes x u0 u1 hinj hnodes hdegree hagreement hnoPencil
 have hscaled:Gamma.card*meetProfile.gap^2 ≤
     meetProfile.totalNumerator:=by
   calc
     Gamma.card*meetProfile.gap^2 ≤
         ((∑ F:RegularIndex Q,
           (regularSeeds Q selected Gamma F).card)+
           (singularSeeds Q selected Gamma).card)*meetProfile.gap^2:=
       Nat.mul_le_mul_right _ hcover
     _=(∑ F:RegularIndex Q,
           (regularSeeds Q selected Gamma F).card)*meetProfile.gap^2+
         (singularSeeds Q selected Gamma).card*meetProfile.gap^2:=by ring
     _ ≤ meetProfile.regularNumerator+
         meetProfile.retainedSingularContribution:=Nat.add_le_add hreg hsing
     _=meetProfile.totalNumerator:=rfl
 have hstrict:meetProfile.totalNumerator <
     meetProfile.fixedCost*meetProfile.gap^2:=by
   rw [meet_total_numerator_exact,meet_fixed_cost_exact]
   norm_num [meetProfile,Profile.gap]
 exact Nat.lt_of_mul_lt_mul_right (hscaled.trans_lt hstrict)
end
end ProximityPrize.SubmissionLower.RCN092
end PackedLegacy_J6

/-! Packed from ProximityPrize.SubmissionLower.GQ. -/
section PackedLegacy_GQ
namespace ProximityPrize.SubmissionLower.RCN317
open scoped Classical BigOperators
open RCN174 RCN319 RCN238 RCN266 RCN140 RCN291 RCN294 RCN318 RCN276 RCN141 RCN092
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 35000
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
def tightRegularCountCap (p:Profile):ℕ:=
 p.regularNumerator/p.gap^2
def tightFixedCountCap (p:Profile) (t:TightParameters):ℕ:=
 tightRegularCountCap p+t.countCap
theorem combined_tight_count_bound
   (p:Profile) (t:TightParameters) (regularCount singularCount:ℕ)
   (hpgap:0 < p.gap) (htgap:0 < t.gap)
   (hregular:regularCount*p.gap^2 ≤ p.regularNumerator)
   (hsingular:singularCount*t.gap ≤ t.tightNumerator):
   regularCount+singularCount ≤ tightFixedCountCap p t:=by
 apply Nat.add_le_add
 · exact (Nat.le_div_iff_mul_le (pow_pos hpgap 2)).2 hregular
 · exact t.count_le_countCap singularCount htgap hsingular
def meetTightFixedCountCap:ℕ:=
 tightFixedCountCap meetProfile meetTightProfile
def meetTightFixedCost:ℕ:=meetTightFixedCountCap+1
theorem meet_tight_regular_count_cap_exact:
   tightRegularCountCap meetProfile=94991970521155972:=by
 rw [show tightRegularCountCap meetProfile=
     meetProfile.regularNumerator/meetProfile.gap^2 by rfl,
   meet_regular_numerator_exact]
 norm_num [meetProfile,Profile.gap]
theorem meet_tight_singular_count_cap_exact:
   meetTightProfile.countCap=5019737604113:=by
 norm_num [meetTightProfile,meetProfile,TightParameters.countCap,
   TightParameters.tightNumerator,TightParameters.coreNumerator,
   TightParameters.aggregateCost,TightParameters.agreement,
   TightParameters.implicitYCap,TightParameters.algebraicCap,
   TightParameters.kappa,TightParameters.errors,TightParameters.gap,dot]
theorem meet_tight_fixed_costs_exact:
   meetTightFixedCountCap=94996990258760085∧
     meetTightFixedCost=94996990258760086:=by
 have hcap:meetTightFixedCountCap=94996990258760085:=by
   rw [show meetTightFixedCountCap=
       tightRegularCountCap meetProfile+meetTightProfile.countCap by rfl,
     meet_tight_regular_count_cap_exact,meet_tight_singular_count_cap_exact]
 exact ⟨hcap,by rw [meetTightFixedCost,hcap]⟩
theorem meet_tight_fixed_strict_saving_exact:
   meetProfile.fixedCost-meetTightFixedCost=759922684662857:=by
 rw [meet_fixed_cost_exact,meet_tight_fixed_costs_exact.2]
theorem meet_global_count_le_tightFixedCountCap_of_regular_factors
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   [CharP K prime6656]
   (hbox:Q∈globalCoefficientBox K meetProfile.weightedCap meetProfile.w
     meetProfile.seedTotalCap meetProfile.slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=meetProfile.n)
   (hdegree:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ meetProfile.w)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hagreement:∀ gamma∈Gamma,
     meetProfile.agreements ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma meetProfile.w
     meetProfile.errors)
   (hregular:∀ F:RegularIndex Q,
     (regularSeeds Q selected Gamma F).card*meetProfile.gap^2 ≤
       meetProfile.factorRegularLedger (regularFlag Q F)):
   Gamma.card ≤ meetTightFixedCountCap:=by
 have hcover:=meet_card_le_regular_sum_add_singular Q hQ hbox selected
   Gamma hsolution
 have hreg:=sum_factor_counts_rectangular_le meetProfile Q hQ
   (by norm_num [meetProfile]) hbox
   (fun F:RegularIndex Q => (regularSeeds Q selected Gamma F).card)
   hregular
 have hsing:=meet_singularSeeds_tight_gap_bound Q hQ hbox selected Gamma
   nodes x u0 u1 hinj hnodes hdegree hagreement hnoPencil
 exact hcover.trans (combined_tight_count_bound meetProfile meetTightProfile
   (∑ F:RegularIndex Q,(regularSeeds Q selected Gamma F).card)
   (singularSeeds Q selected Gamma).card
   (by norm_num [meetProfile,Profile.gap])
   (by norm_num [meetTightProfile,meetProfile,TightParameters.gap])
   hreg hsing)
theorem meet_global_count_lt_tightFixedCost_of_regular_factors
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   [CharP K prime6656]
   (hbox:Q∈globalCoefficientBox K meetProfile.weightedCap meetProfile.w
     meetProfile.seedTotalCap meetProfile.slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=meetProfile.n)
   (hdegree:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ meetProfile.w)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hagreement:∀ gamma∈Gamma,
     meetProfile.agreements ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma meetProfile.w
     meetProfile.errors)
   (hregular:∀ F:RegularIndex Q,
     (regularSeeds Q selected Gamma F).card*meetProfile.gap^2 ≤
       meetProfile.factorRegularLedger (regularFlag Q F)):
   Gamma.card < meetTightFixedCost:=by
 exact (meet_global_count_le_tightFixedCountCap_of_regular_factors Q hQ hbox
   selected Gamma nodes x u0 u1 hinj hnodes hdegree hsolution hagreement
   hnoPencil hregular).trans_lt (Nat.lt_succ_self _)
end
end ProximityPrize.SubmissionLower.RCN317
end PackedLegacy_GQ

/-! Packed from ProximityPrize.SubmissionLower.AF. -/
section PackedLegacy_AF
namespace ProximityPrize.SubmissionLower.RCN287
open scoped Classical BigOperators
open RCN081 RCN313 RCN136 RCN234 RCN179 RCN095 RCN275 RCN275.ResidualSupportParameters RCN156 RCN174 RCN238 RCN266 RCN159 RCN164 RCN091 RCN276 RCN318 RCN141 RCN317
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 35000
def sharpAgreementDirection (P:ResidualSupportParameters):FlagDegree:=
 ⟨2*(P.total-P.ys),2*(P.ys-P.s)-1,2*P.s-1⟩
def sharpResidualAgreementFlag
   (P:ResidualSupportParameters) (d:ℕ):FlagDegree:=
 ⟨(sharpAgreementDirection P).zOnly*d,
   1+(sharpAgreementDirection P).yz*d,
   (sharpAgreementDirection P).all*d⟩
theorem sharpResidualAgreementFlag_ys
   (P:ResidualSupportParameters) (hsy:P.s < P.ys) (d:ℕ):
   (sharpResidualAgreementFlag P d).yz+
       (sharpResidualAgreementFlag P d).all=
     1+d*(2*P.ys-2):=by
 have hcoeff:
     (2*(P.ys-P.s)-1)+(2*P.s-1)=2*P.ys-2:=by
   have hleft:1 ≤ 2*(P.ys-P.s):=by
     have:1 ≤ P.ys-P.s:=Nat.sub_pos_of_lt hsy
     omega
   have hright:1 ≤ 2*P.s:=by
     have:1 ≤ P.s:=P.one_le_s
     omega
   rw [tsub_add_tsub_comm hleft hright]
   have hsum:2*(P.ys-P.s)+2*P.s=2*P.ys:=by
     calc
       2*(P.ys-P.s)+2*P.s=2*((P.ys-P.s)+P.s):=by ring
       _=2*P.ys:=by rw [Nat.sub_add_cancel (Nat.le_of_lt hsy)]
   rw [hsum]
 simp only [sharpResidualAgreementFlag,sharpAgreementDirection]
 rw [←hcoeff]
 ring
theorem sharpResidualAgreementFlag_total
   (P:ResidualSupportParameters) (hsy:P.s < P.ys) (d:ℕ):
   (sharpResidualAgreementFlag P d).zOnly+
       (sharpResidualAgreementFlag P d).yz+
       (sharpResidualAgreementFlag P d).all=
     1+d*(2*P.total-2):=by
 have hcoeff:
     2*(P.total-P.ys)+(2*(P.ys-P.s)-1)+
         (2*P.s-1)=2*P.total-2:=by
   have hmiddle:
       (2*(P.ys-P.s)-1)+(2*P.s-1)=
         2*P.ys-2:=by
     have hleft:1 ≤ 2*(P.ys-P.s):=by
       have:1 ≤ P.ys-P.s:=Nat.sub_pos_of_lt hsy
       omega
     have hright:1 ≤ 2*P.s:=by
       have:1 ≤ P.s:=P.one_le_s
       omega
     rw [tsub_add_tsub_comm hleft hright]
     have hsum:2*(P.ys-P.s)+2*P.s=2*P.ys:=by
       calc
         2*(P.ys-P.s)+2*P.s=
             2*((P.ys-P.s)+P.s):=by ring
         _=2*P.ys:=by rw [Nat.sub_add_cancel (Nat.le_of_lt hsy)]
     rw [hsum]
   rw [Nat.add_assoc,hmiddle]
   have htwo:2 ≤ 2*P.ys:=by
     have:1 ≤ P.ys:=P.one_le_s.trans P.s_le_ys
     omega
   rw [←Nat.add_sub_assoc htwo]
   have hsum:2*(P.total-P.ys)+2*P.ys=2*P.total:=by
     calc
       2*(P.total-P.ys)+2*P.ys=
           2*((P.total-P.ys)+P.ys):=by ring
       _=2*P.total:=by rw [Nat.sub_add_cancel P.ys_le_total]
   rw [hsum]
 simp only [sharpResidualAgreementFlag,sharpAgreementDirection]
 rw [←hcoeff]
 ring
theorem fixedMeet_sharp_agreement_direction:
   sharpAgreementDirection fixedMeetSupport=⟨1140,55,11⟩:=by
 norm_num [fixedMeetSupport,sharpAgreementDirection]
theorem fixedMeet_sharp_agreement_flag (d:ℕ):
   sharpResidualAgreementFlag fixedMeetSupport d=
     ⟨1140*d,1+55*d,11*d⟩:=by
 rw [show sharpResidualAgreementFlag fixedMeetSupport d=
     ⟨(sharpAgreementDirection fixedMeetSupport).zOnly*d,
       1+(sharpAgreementDirection fixedMeetSupport).yz*d,
       (sharpAgreementDirection fixedMeetSupport).all*d⟩ by rfl,
   fixedMeet_sharp_agreement_direction]
variable {K Omega:Type} [Field K] [Field Omega]
theorem sharp_agreement_weight_bounds
   {P:ResidualSupportParameters} {F:MvPolynomial (Fin 4) K}
   (H:ResidualSupportData P F)
   (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K):
   (agreementNumerator F d coeffs x u0 u1).degreeOf (2:Fin 4) ≤
       d*(2*P.s-1)∧
     wt residualYSWeights (agreementNumerator F d coeffs x u0 u1) ≤
       1+d*(2*P.ys-2)∧
     wt residualTotalWeights (agreementNumerator F d coeffs x u0 u1) ≤
       1+d*(2*P.total-2):=by
 obtain ⟨hY,hR,hZ⟩:=H.coordinate_bounds
 refine ⟨(agreementNumerator_degree_bounds F P.ys P.s P.total
   P.one_le_s hY hR hZ d coeffs x u0 u1).2.1,?_,?_⟩
 · have h:=agreementNumerator_wt_le_equal_weight residualYSWeights rfl
     F P.ys (by change 1 ≤ 1;norm_num)
     (by change 1 ≤ P.ys;exact P.one_le_s.trans P.s_le_ys)
     (by change 2*1 ≤ P.ys;simpa using P.two_le_ys)
     (by change 1 ≤ 1;norm_num) H.ys_weight d coeffs x u0 u1
   have hcoeff:2*(P.ys-1)=2*P.ys-2:=by omega
   apply h.trans_eq
   change max 1 0+d*(2*(P.ys-1))=
     1+d*(2*P.ys-2)
   rw [hcoeff]
   norm_num
 · have htotalTwo:2 ≤ P.total:=P.two_le_ys.trans P.ys_le_total
   have honeTotal:1 ≤ P.total:=
     P.one_le_s.trans (P.s_le_ys.trans P.ys_le_total)
   have h:=agreementNumerator_wt_le_equal_weight residualTotalWeights rfl
     F P.total (by change 1 ≤ 1;norm_num)
     (by change 1 ≤ P.total;exact honeTotal)
     (by change 2*1 ≤ P.total;simpa using htotalTwo)
     (by change 1 ≤ 1;norm_num) H.total_weight d coeffs x u0 u1
   have hcoeff:2*(P.total-1)=2*P.total-2:=by omega
   apply h.trans_eq
   change max 1 1+d*(2*(P.total-1))=
     1+d*(2*P.total-2)
   rw [hcoeff]
   norm_num
theorem surfaceMap_agreement_in_sharp_flag
   {P:ResidualSupportParameters} (hsy:P.s < P.ys)
   (phi:Polynomial K →+*Omega) {F:MvPolynomial (Fin 4) K}
   (H:ResidualSupportData P F)
   (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K):
   PolynomialInFlag (sharpResidualAgreementFlag P d)
     (surfaceMap phi (agreementNumerator F d coeffs x u0 u1)):=by
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp
   (support_surfaceMap_subset phi (agreementNumerator F d coeffs x u0 u1) he)
 obtain ⟨hR,hYS,hTotal⟩:=sharp_agreement_weight_bounds H
   d coeffs x u0 u1
 have hqR:=(MvPolynomial.monomial_le_degreeOf (2:Fin 4) hq).trans hR
 have hqYS:=
   (MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hYS
 have hqTotal:=
   (MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hTotal
 rw [RCN081.weight_fin4] at hqYS hqTotal
 change q 0*0+q 1*1+q 2*1+q 3*0 ≤
   1+d*(2*P.ys-2) at hqYS
 change q 0*0+q 1*1+q 2*1+q 3*1 ≤
   1+d*(2*P.total-2) at hqTotal
 norm_num at hqYS hqTotal
 have hqR':q 2 ≤ (sharpResidualAgreementFlag P d).all:=by
   change q 2 ≤ (2*P.s-1)*d
   rw [Nat.mul_comm]
   exact hqR
 change q 2 ≤ (sharpResidualAgreementFlag P d).all∧
   q 1+q 2 ≤ (sharpResidualAgreementFlag P d).yz+
     (sharpResidualAgreementFlag P d).all∧
   q 1+q 2+q 3 ≤ (sharpResidualAgreementFlag P d).zOnly+
     (sharpResidualAgreementFlag P d).yz+
     (sharpResidualAgreementFlag P d).all
 refine ⟨hqR',?_,?_⟩
 · rw [sharpResidualAgreementFlag_ys P hsy]
   exact hqYS
 · rw [sharpResidualAgreementFlag_total P hsy]
   exact hqTotal
def factorRegularLedgerForDirection
   (p:Profile) (direction flag:FlagDegree):ℕ:=
 (flagMixed flag direction direction*p.degreeIncidence^2+
     2*flagMixed flag direction unitYZFlag*
       p.degreeIncidence*p.unitIncidence+
     flagMixed flag unitYZFlag unitYZFlag*p.unitIncidence^2)+
   (p.errors+1)*p.gap*
     (flagMixed flag direction unitZFlag*p.degreeIncidence+
       flagMixed flag unitYZFlag unitZFlag*p.unitIncidence)+
   (p.errors+1)*p.gap*
     (flagMixed flag direction unitAllFlag*p.degreeIncidence+
       flagMixed flag unitYZFlag unitAllFlag*p.unitIncidence)
def sharpRegularNumerator
   (p:Profile) (support:ResidualSupportParameters):ℕ:=
 factorRegularLedgerForDirection p (sharpAgreementDirection support)
   p.rectangularSurfaceFlag
theorem factorRegularLedgerForDirection_projection_decomposition
   (p:Profile) (direction flag:FlagDegree):
   factorRegularLedgerForDirection p direction flag=
     flag.zOnly*factorRegularLedgerForDirection p direction unitZFlag+
     flag.yz*factorRegularLedgerForDirection p direction unitYZFlag+
     flag.all*factorRegularLedgerForDirection p direction unitAllFlag:=by
 cases flag
 simp [factorRegularLedgerForDirection,flagMixed,unitZFlag,unitYZFlag,
   unitAllFlag]
 ring
theorem sum_factorRegularLedgerForDirection_le_flag
   {I:Type} [Fintype I] (p:Profile) (direction:FlagDegree)
   (flag:I → FlagDegree) (cap:FlagDegree)
   (hz:(∑ i,(flag i).zOnly) ≤ cap.zOnly)
   (hyz:(∑ i,(flag i).yz) ≤ cap.yz)
   (hall:(∑ i,(flag i).all) ≤ cap.all):
   (∑ i,factorRegularLedgerForDirection p direction (flag i)) ≤
     factorRegularLedgerForDirection p direction cap:=by
 classical
 calc
   (∑ i,factorRegularLedgerForDirection p direction (flag i))=
       ∑ i,((flag i).zOnly*
           factorRegularLedgerForDirection p direction unitZFlag+
         (flag i).yz*
           factorRegularLedgerForDirection p direction unitYZFlag+
         (flag i).all*
           factorRegularLedgerForDirection p direction unitAllFlag):=by
     apply Finset.sum_congr rfl
     intro i _
     exact factorRegularLedgerForDirection_projection_decomposition
       p direction (flag i)
   _=(∑ i,(flag i).zOnly)*
         factorRegularLedgerForDirection p direction unitZFlag+
       (∑ i,(flag i).yz)*
         factorRegularLedgerForDirection p direction unitYZFlag+
       (∑ i,(flag i).all)*
         factorRegularLedgerForDirection p direction unitAllFlag:=by
     simp only [Finset.sum_add_distrib,Finset.sum_mul]
   _ ≤ cap.zOnly*factorRegularLedgerForDirection p direction unitZFlag+
       cap.yz*factorRegularLedgerForDirection p direction unitYZFlag+
       cap.all*factorRegularLedgerForDirection p direction unitAllFlag:=
     Nat.add_le_add
       (Nat.add_le_add (Nat.mul_le_mul_right _ hz)
         (Nat.mul_le_mul_right _ hyz))
       (Nat.mul_le_mul_right _ hall)
   _=factorRegularLedgerForDirection p direction cap:=
     (factorRegularLedgerForDirection_projection_decomposition
       p direction cap).symm
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem sum_factor_counts_rectangular_sharp_le
   (p:Profile) (support:ResidualSupportParameters)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (hw:0 < p.w)
   (hbox:Q∈globalCoefficientBox K p.weightedCap p.w
     p.seedTotalCap p.slopeCap)
   (count:RegularIndex Q → ℕ)
   (hcount:∀ F,count F*p.gap^2 ≤
     factorRegularLedgerForDirection p (sharpAgreementDirection support)
       (regularFlag Q F)):
   (∑ F,count F)*p.gap^2 ≤ sharpRegularNumerator p support:=by
 have hcaps:=regularFlag_budgets p Q hQ hw hbox
 calc
   (∑ F,count F)*p.gap^2=∑ F,count F*p.gap^2:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ F,factorRegularLedgerForDirection p
       (sharpAgreementDirection support) (regularFlag Q F):=
     Finset.sum_le_sum (fun F _↦hcount F)
   _ ≤ factorRegularLedgerForDirection p (sharpAgreementDirection support)
       p.rectangularSurfaceFlag:=
     sum_factorRegularLedgerForDirection_le_flag p
       (sharpAgreementDirection support) (regularFlag Q)
       p.rectangularSurfaceFlag hcaps.1 hcaps.2.1 hcaps.2.2
   _=sharpRegularNumerator p support:=rfl
def meetSharpFactorDegreeCost (flag:FlagDegree):ℕ:=
 (flagMixed flag (sharpAgreementDirection fixedMeetSupport)
       (sharpAgreementDirection fixedMeetSupport)*
     meetProfile.degreeIncidence+
   flagMixed flag (sharpAgreementDirection fixedMeetSupport) unitYZFlag*
     meetProfile.unitIncidence)+
 (meetProfile.errors+1)*meetProfile.gap*
   (flagMixed flag (sharpAgreementDirection fixedMeetSupport) unitZFlag+
     flagMixed flag (sharpAgreementDirection fixedMeetSupport) unitAllFlag)
def meetSharpFactorUnitCost (flag:FlagDegree):ℕ:=
 (flagMixed flag (sharpAgreementDirection fixedMeetSupport) unitYZFlag*
     meetProfile.degreeIncidence+
   flagMixed flag unitYZFlag unitYZFlag*meetProfile.unitIncidence)+
 (meetProfile.errors+1)*meetProfile.gap*
   (flagMixed flag unitYZFlag unitZFlag+
     flagMixed flag unitYZFlag unitAllFlag)
theorem meet_sharp_incidence_cost_eq_ledger (flag:FlagDegree):
   meetProfile.degreeIncidence*meetSharpFactorDegreeCost flag+
     meetProfile.unitIncidence*meetSharpFactorUnitCost flag=
   factorRegularLedgerForDirection meetProfile
     (sharpAgreementDirection fixedMeetSupport) flag:=by
 simp [meetSharpFactorDegreeCost,meetSharpFactorUnitCost,
   factorRegularLedgerForDirection]
 ring
theorem recursive_scaled_factor_sharp_6656
   {flag:FlagDegree}
   (hphi:Function.Injective phi)
   (S:ResidualStage phi Gamma x pchar meetProfile.errors flag meetProfile.w
     fixedMeetSupport)
   (hnodes:S.nodes.card=meetProfile.n)
   (hagreement:∀ gamma∈Gamma,
     meetProfile.agreements ≤ (S.agreementFiber gamma).card)
   (hfiber:∀ D:S.TerminalDescendant,∀ i∈D.stage.nodes,
     ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i) →
     (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*
         meetProfile.gap ≤
       D.degree*meetSharpFactorDegreeCost flag+
         meetSharpFactorUnitCost flag):
   Gamma.card*meetProfile.gap^2 ≤
     factorRegularLedgerForDirection meetProfile
       (sharpAgreementDirection fixedMeetSupport) flag:=by
 have h:=recursive_scaled_stratified_incidence_bound
   hphi S (meetSharpFactorDegreeCost flag) (meetSharpFactorUnitCost flag)
     meetProfile.degreeIncidence meetProfile.unitIncidence
     (by norm_num [meetProfile]) hagreement hfiber
     (by
       intro k hk
       rw [hnodes]
       exact meet_degree_part_bound k hk)
     (by
       intro k hk
       rw [hnodes]
       exact meet_unit_part_bound k hk)
 calc
   Gamma.card*meetProfile.gap^2 ≤
       meetProfile.degreeIncidence*meetSharpFactorDegreeCost flag+
         meetProfile.unitIncidence*meetSharpFactorUnitCost flag:=by
     simpa only [Profile.gap] using h
   _=factorRegularLedgerForDirection meetProfile
       (sharpAgreementDirection fixedMeetSupport) flag:=
     meet_sharp_incidence_cost_eq_ledger flag
def meetSharpRegularNumerator:ℕ:=
 sharpRegularNumerator meetProfile fixedMeetSupport
def meetSharpTightFixedCountCap:ℕ:=
 meetSharpRegularNumerator/meetProfile.gap^2+
   meetTightProfile.countCap
def meetSharpTightFixedCost:ℕ:=meetSharpTightFixedCountCap+1
theorem meet_sharp_regular_numerator_exact:
   meetSharpRegularNumerator=251547391650163581021710430:=by
 norm_num [meetSharpRegularNumerator,sharpRegularNumerator,
   factorRegularLedgerForDirection,fixedMeetSupport,
   sharpAgreementDirection,
   meetProfile,Profile.rectangularSurfaceFlag,Profile.yCap,
   Profile.degreeIncidence,Profile.unitIncidence,Profile.errors,
   Profile.gap,flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
theorem meet_sharp_tight_fixed_costs_exact:
   meetSharpTightFixedCountCap=93984734489150979∧
     meetSharpTightFixedCost=93984734489150980:=by
 have hcap:meetSharpTightFixedCountCap=93984734489150979:=by
   rw [show meetSharpTightFixedCountCap=
       meetSharpRegularNumerator/meetProfile.gap^2+
         meetTightProfile.countCap by rfl,
     meet_sharp_regular_numerator_exact,
     meet_tight_singular_count_cap_exact]
   norm_num [meetProfile,Profile.gap]
 exact ⟨hcap,by rw [meetSharpTightFixedCost,hcap]⟩
theorem meet_sharp_saving_over_tight_fixed_exact:
   meetTightFixedCost-meetSharpTightFixedCost=1012255769609106:=by
 rw [meet_tight_fixed_costs_exact.2,meet_sharp_tight_fixed_costs_exact.2]
end
end ProximityPrize.SubmissionLower.RCN287
end PackedLegacy_AF

/-! Packed from ProximityPrize.SubmissionLower.N7. -/
section PackedLegacy_N7
namespace ProximityPrize.SubmissionLower.RCN262
open scoped BigOperators
open RCN077 RCN313 RCN293 RCN234 RCN179
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
def vectorNumerator (F P:Poly K):Poly K :=
 polyH K F * MvPolynomial.pderiv (0:Fin 4) P +
   MvPolynomial.X (2:Fin 4) * polyH K F * MvPolynomial.pderiv (1:Fin 4) P +
   polyG K F * MvPolynomial.pderiv (2:Fin 4) P
theorem vectorNumerator_surface (F:Poly K):vectorNumerator F F = 0:=by
 unfold vectorNumerator polyG polyH
 ring
theorem vectorNumerator_mul (F P Q:Poly K) :
   vectorNumerator F (P * Q) = P * vectorNumerator F Q + Q * vectorNumerator F P:=by
 simp only [vectorNumerator,MvPolynomial.pderiv_mul]
 ring
theorem vectorNumerator_sub (F P Q:Poly K) :
   vectorNumerator F (P - Q) = vectorNumerator F P - vectorNumerator F Q:=by
 simp only [vectorNumerator,map_sub]
 ring
theorem numeratorStep_eq_vector (F P:Poly K) (b:ℕ) :
   numeratorStep K F b P =
     polyH K F * vectorNumerator F P -
       ((2 * b:ℕ):Poly K) * P * vectorNumerator F (polyH K F):=by
 unfold numeratorStep clearedStep vectorNumerator
 ring
theorem numeratorStep_sub (F P Q:Poly K) (b:ℕ) :
   numeratorStep K F b (P - Q) = numeratorStep K F b P - numeratorStep K F b Q:=by
 simp only [numeratorStep_eq_vector,vectorNumerator_sub]
 ring
theorem numeratorStep_mul_surface (F Q:Poly K) (b:ℕ) :
   numeratorStep K F b (F * Q) = F * numeratorStep K F b Q:=by
 simp only [numeratorStep_eq_vector,vectorNumerator_mul,vectorNumerator_surface,
   mul_zero,add_zero]
 ring
theorem numeratorStep_congr (F P Q:Poly K) (b:ℕ) (h:F ∣ P - Q) :
   F ∣ numeratorStep K F b P - numeratorStep K F b Q:=by
 obtain ⟨T,hT⟩:=h
 refine ⟨numeratorStep K F b T,?_⟩
 rw [← numeratorStep_sub,hT,numeratorStep_mul_surface]
theorem vectorNumerator_R_degree_bound (F P:Poly K) (a s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (hP:P.degreeOf (2:Fin 4) ≤ a) :
   (vectorNumerator F P).degreeOf (2:Fin 4) ≤ a + s:=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly K:=MvPolynomial.X (2:Fin 4)
 have hR:R.degreeOf (2:Fin 4) ≤ 1:=by simp [R]
 have hH:H.degreeOf (2:Fin 4) ≤ s - 1 :=
   pderiv_same_degree_bound (2:Fin 4) F s hF
 have hG:G.degreeOf (2:Fin 4) ≤ s + 1 :=
   polyG_degree_bound (2:Fin 4) F s 1 hF hR
 have hPX:=pderiv_degree_bound (0:Fin 4) (2:Fin 4) P a hP
 have hPY:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) P a hP
 have hPR:=pderiv_same_degree_bound (2:Fin 4) P a hP
 have hx:(H * MvPolynomial.pderiv (0:Fin 4) P).degreeOf (2:Fin 4) ≤ a + s:=by
   have h:=degree_mul_bound (2:Fin 4) hH hPX
   omega
 have hy:(R * H * MvPolynomial.pderiv (1:Fin 4) P).degreeOf (2:Fin 4) ≤ a + s:=by
   have h:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hR hH) hPY
   omega
 have hr:(G * MvPolynomial.pderiv (2:Fin 4) P).degreeOf (2:Fin 4) ≤ a + s:=by
   by_cases ha:a = 0
   · have hz:=pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) P (by simpa [ha] using hP)
     simp [hz]
   · have h:=degree_mul_bound (2:Fin 4) hG hPR
     omega
 exact degree_add_bound (2:Fin 4) (degree_add_bound (2:Fin 4) hx hy) hr
theorem pderiv_eq_zero_of_wt_lt (weights:Fin 4 → ℕ) (P:Poly K) (i:Fin 4)
   (hP:wt weights P < weights i):MvPolynomial.pderiv i P = 0:=by
 apply MvPolynomial.support_eq_empty.mp
 apply Finset.eq_empty_iff_forall_notMem.mpr
 intro d hd
 have hh:=MvPolynomial.le_weightedTotalDegree weights (support_before_pderiv i P d hd)
 simp only [map_add,Finsupp.weight_single,one_nsmul] at hh
 change Finsupp.weight weights d + weights i ≤ wt weights P at hh
 omega
def excessFactor (F P:Poly K) (s b:ℕ):Poly K :=
 (s:Poly K) *
   ((s:Poly K) * liftedCoefficient F s *
       MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient P (2 * b * (s - 1))) -
     ((2 * b * (s - 1) + 2 * b:ℕ):Poly K) *
       MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s) *
         liftedCoefficient P (2 * b * (s - 1)))
def reductionMultiplier (F P:Poly K) (s b:ℕ):Poly K :=
 excessFactor F P s b * MvPolynomial.X (2:Fin 4) ^ ((2 * b + 1) * (s - 1))
def reducedStep (F P:Poly K) (s b:ℕ):Poly K :=
 numeratorStep K F b P - reductionMultiplier F P s b * F
def reducedNumerator (F:Poly K) (s:ℕ):ℕ → Poly K
 | 0 => MvPolynomial.X (1:Fin 4)
 | b + 1 => reducedStep F (reducedNumerator F s b) s b
@[simp] theorem reducedNumerator_zero (F:Poly K) (s:ℕ) :
   reducedNumerator F s 0 = MvPolynomial.X (1:Fin 4):=rfl
@[simp] theorem reducedNumerator_succ (F:Poly K) (s b:ℕ) :
   reducedNumerator F s (b + 1) = reducedStep F (reducedNumerator F s b) s b:=rfl
theorem numerator_sub_reduced_dvd (F:Poly K) (s b:ℕ) :
   F ∣ numerator K F b - reducedNumerator F s b:=by
 induction b with
 | zero => simp
 | succ b ih =>
     have hstep:=numeratorStep_congr F (numerator K F b) (reducedNumerator F s b) b ih
     obtain ⟨T,hT⟩:=hstep
     refine ⟨T + reductionMultiplier F (reducedNumerator F s b) s b,?_⟩
     rw [numerator_succ,reducedNumerator_succ,reducedStep]
     linear_combination hT
def reducedCommonNumeratorTerm (F:Poly K) (s w:ℕ) (c:ℕ → K) (x:K)
   (j:ℕ):Poly K :=
 MvPolynomial.C (c j) * reducedNumerator F s j *
   polyH K F ^ (2 * (w - j)) *
     (MvPolynomial.C x - MvPolynomial.X (0:Fin 4)) ^ j
def reducedClearedTaylorNumerator (F:Poly K) (s w:ℕ) (c:ℕ → K) (x:K) :
   Poly K :=
 ∑ j ∈ Finset.range (w + 1),reducedCommonNumeratorTerm F s w c x j
def reducedAgreementNumerator (F:Poly K) (s w:ℕ) (c:ℕ → K) (x u₀ u₁:K) :
   Poly K :=
 reducedClearedTaylorNumerator F s w c x -
   affineSeedPolynomial u₀ u₁ * polyH K F ^ (2 * w)
theorem commonNumeratorTerm_sub_reduced_dvd (F:Poly K) (s w j:ℕ)
   (c:ℕ → K) (x:K) :
   F ∣ commonNumeratorTerm F w c x j - reducedCommonNumeratorTerm F s w c x j:=by
 obtain ⟨T,hT⟩:=numerator_sub_reduced_dvd F s j
 refine ⟨MvPolynomial.C (c j) * T * polyH K F ^ (2 * (w - j)) *
   (MvPolynomial.C x - MvPolynomial.X (0:Fin 4)) ^ j,?_⟩
 unfold commonNumeratorTerm reducedCommonNumeratorTerm
 linear_combination MvPolynomial.C (c j) * polyH K F ^ (2 * (w - j)) *
   (MvPolynomial.C x - MvPolynomial.X (0:Fin 4)) ^ j * hT
theorem clearedTaylorNumerator_sub_reduced_dvd (F:Poly K) (s w:ℕ)
   (c:ℕ → K) (x:K) :
   F ∣ clearedTaylorNumerator F w c x - reducedClearedTaylorNumerator F s w c x:=by
 unfold clearedTaylorNumerator reducedClearedTaylorNumerator
 rw [← Finset.sum_sub_distrib]
 exact Finset.dvd_sum fun j _ => commonNumeratorTerm_sub_reduced_dvd F s w j c x
theorem agreementNumerator_sub_reduced_dvd (F:Poly K) (s w:ℕ)
   (c:ℕ → K) (x u₀ u₁:K) :
   F ∣ agreementNumerator F w c x u₀ u₁ -
     reducedAgreementNumerator F s w c x u₀ u₁:=by
 unfold agreementNumerator reducedAgreementNumerator
 simpa only [sub_sub_sub_cancel_right] using
   clearedTaylorNumerator_sub_reduced_dvd F s w c x
end
end ProximityPrize.SubmissionLower.RCN262
end PackedLegacy_N7

/-! Packed from ProximityPrize.SubmissionLower.N6. -/
section PackedLegacy_N6
namespace ProximityPrize.SubmissionLower.RCN261
open RCN290 RCN293 RCN081
noncomputable section
variable {K:Type*} [Field K]
theorem embedCoefficients_injective:Function.Injective (embedCoefficients K):=by
 intro P Q h
 exact Polynomial.C_injective ((collectR K).symm.injective h)
@[simp] theorem liftedCoefficient_zero (n:ℕ) :
   liftedCoefficient (0:MvPolynomial (Fin 4) K) n = 0:=by
 simp [liftedCoefficient]
@[simp] theorem liftedCoefficient_add (P Q:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient (P + Q) n = liftedCoefficient P n + liftedCoefficient Q n:=by
 simp [liftedCoefficient]
@[simp] theorem liftedCoefficient_sub (P Q:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient (P - Q) n = liftedCoefficient P n - liftedCoefficient Q n:=by
 simp [liftedCoefficient]
@[simp] theorem liftedCoefficient_neg (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient (-P) n = -liftedCoefficient P n:=by
 simp [liftedCoefficient]
theorem liftedCoefficient_eq_zero_iff (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient P n = 0 ↔ (collectR K P).coeff n = 0:=by
 change embedCoefficients K ((collectR K P).coeff n) = 0 ↔ _
 rw [← map_zero (embedCoefficients K),embedCoefficients_injective.eq_iff]
theorem liftedCoefficient_eq_zero_of_degree_lt (P:MvPolynomial (Fin 4) K)
   (n:ℕ) (hP:P.degreeOf 2 < n):liftedCoefficient P n = 0:=by
 apply (liftedCoefficient_eq_zero_iff P n).mpr
 exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [collectR_natDegree])
theorem collectR_X_R :
   collectR K (MvPolynomial.X (2:Fin 4)) = Polynomial.X:=by
 simp [collectR,MvPolynomial.renameEquiv_apply,
   Equiv.optionSubtypeNe_symm_apply]
theorem collectR_pderiv_R (P:MvPolynomial (Fin 4) K) :
   collectR K (MvPolynomial.pderiv (2:Fin 4) P) = (collectR K P).derivative:=by
 classical
 induction P using MvPolynomial.induction_on with
 | C c =>
     simp [collectR,MvPolynomial.renameEquiv_apply]
 | add P Q hP hQ => simp only [map_add,hP,hQ]
 | mul_X P i hP =>
     by_cases hi:i = 2
     · subst i
       simp [map_mul,collectR_X_R,Polynomial.derivative_mul,hP]
       ring
     · have hX:=collectR_X_other (K:=K) (⟨i,hi⟩:RemainingCoordinates)
       simp only [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X_of_ne hi,
         mul_zero,add_zero,map_mul,hX,Polynomial.derivative_mul,
         Polynomial.derivative_C,mul_zero,add_zero,hP]
theorem liftedCoefficient_pderiv_R (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient (MvPolynomial.pderiv (2:Fin 4) P) n =
     MvPolynomial.C ((n + 1:ℕ):K) * liftedCoefficient P (n + 1):=by
 unfold liftedCoefficient
 rw [collectR_pderiv_R,Polynomial.coeff_derivative,map_mul]
 simp only [map_add,map_natCast,map_one,Nat.cast_add,Nat.cast_one]
 ring
private theorem optionCoefficient_pderiv_some {σ:Type*}
   (P:MvPolynomial (Option σ) K) (i:σ) (n:ℕ) :
   (MvPolynomial.optionEquivLeft K σ (MvPolynomial.pderiv (some i) P)).coeff n =
     MvPolynomial.pderiv i ((MvPolynomial.optionEquivLeft K σ P).coeff n):=by
 classical
 ext e
 rw [MvPolynomial.optionEquivLeft_coeff_coeff,MvPolynomial.coeff_pderiv,
   MvPolynomial.coeff_pderiv,MvPolynomial.optionEquivLeft_coeff_coeff]
 have he:e.optionElim n + Finsupp.single (some i) 1 =
     (e + Finsupp.single i 1).optionElim n:=by
   ext j
   cases j with
   | none => simp
   | some j =>
       simp only [Finsupp.add_apply,Finsupp.optionElim_apply_some]
       rw [Finsupp.single_apply_left
         (show Function.Injective (some:σ → Option σ) from fun _ _ h => Option.some.inj h)]
 rw [he,Finsupp.optionElim_apply_some]
theorem liftedCoefficient_pderiv_other (P:MvPolynomial (Fin 4) K)
   (i:Fin 4) (hi:i ≠ 2) (n:ℕ) :
   liftedCoefficient (MvPolynomial.pderiv i P) n =
     MvPolynomial.pderiv i (liftedCoefficient P n):=by
 have hindex:(Equiv.optionSubtypeNe (2:Fin 4)).symm i = some ⟨i,hi⟩:=by
   simp [Equiv.optionSubtypeNe_symm_apply,hi]
 have hrename :
     MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm
       (MvPolynomial.pderiv i P) =
     MvPolynomial.pderiv (some (⟨i,hi⟩:RemainingCoordinates))
       (MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm P):=by
   rw [← MvPolynomial.pderiv_rename
     (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective i P,hindex]
 have hc:(collectR K (MvPolynomial.pderiv i P)).coeff n =
     MvPolynomial.pderiv (⟨i,hi⟩:RemainingCoordinates) ((collectR K P).coeff n):=by
   change (MvPolynomial.optionEquivLeft K RemainingCoordinates
     (MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm
       (MvPolynomial.pderiv i P))).coeff n = _
   rw [hrename,optionCoefficient_pderiv_some]
   rfl
 unfold liftedCoefficient
 rw [hc,embedCoefficients_eq_rename,embedCoefficients_eq_rename]
 exact (MvPolynomial.pderiv_rename Subtype.val_injective
   (⟨i,hi⟩:RemainingCoordinates) ((collectR K P).coeff n)).symm
theorem liftedCoefficient_pderiv_R_top (P:MvPolynomial (Fin 4) K) (a:ℕ)
   (ha:0 < a) :
   liftedCoefficient (MvPolynomial.pderiv (2:Fin 4) P) (a - 1) =
     MvPolynomial.C (a:K) * liftedCoefficient P a:=by
 simpa only [Nat.sub_add_cancel ha] using liftedCoefficient_pderiv_R P (a - 1)
theorem liftedCoefficient_mul_top (P Q:MvPolynomial (Fin 4) K) (a b:ℕ)
   (hP:P.degreeOf 2 ≤ a) (hQ:Q.degreeOf 2 ≤ b) :
   liftedCoefficient (P * Q) (a + b) =
     liftedCoefficient P a * liftedCoefficient Q b:=by
 unfold liftedCoefficient
 rw [map_mul,Polynomial.coeff_mul_add_eq_of_natDegree_le
   (by rwa [collectR_natDegree]) (by rwa [collectR_natDegree]),map_mul]
theorem liftedCoefficient_zero_degree (P:MvPolynomial (Fin 4) K)
   (hP:P.degreeOf 2 = 0):liftedCoefficient P 0 = P:=by
 have hC:collectR K P = Polynomial.C ((collectR K P).coeff 0) :=
   Polynomial.eq_C_of_natDegree_eq_zero (by rwa [collectR_natDegree])
 change (collectR K).symm (Polynomial.C ((collectR K P).coeff 0)) = P
 rw [← hC,AlgEquiv.symm_apply_apply]
theorem liftedCoefficient_mul_degree_zero_left (P Q:MvPolynomial (Fin 4) K)
   (n:ℕ) (hP:P.degreeOf 2 = 0) :
   liftedCoefficient (P * Q) n = P * liftedCoefficient Q n:=by
 have hC:collectR K P = Polynomial.C ((collectR K P).coeff 0) :=
   Polynomial.eq_C_of_natDegree_eq_zero (by rwa [collectR_natDegree])
 unfold liftedCoefficient
 rw [map_mul,hC,Polynomial.coeff_C_mul,map_mul]
 change liftedCoefficient P 0 * _ = _
 rw [liftedCoefficient_zero_degree P hP]
@[simp] theorem liftedCoefficient_C_mul (c:K) (P:MvPolynomial (Fin 4) K)
   (n:ℕ):liftedCoefficient (MvPolynomial.C c * P) n =
     MvPolynomial.C c * liftedCoefficient P n :=
 liftedCoefficient_mul_degree_zero_left _ P n (MvPolynomial.degreeOf_C c 2)
@[simp] theorem liftedCoefficient_natCast_mul (c:ℕ)
   (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient ((c:MvPolynomial (Fin 4) K) * P) n =
     (c:MvPolynomial (Fin 4) K) * liftedCoefficient P n:=by
 simpa only [map_natCast] using liftedCoefficient_C_mul (c:K) P n
theorem liftedCoefficient_X_R_pow (n:ℕ) :
   liftedCoefficient ((MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K) ^ n) n =
     1:=by
 simp [liftedCoefficient,map_pow,collectR_X_R]
theorem liftedCoefficient_X_R_mul (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   liftedCoefficient (MvPolynomial.X (2:Fin 4) * P) (n + 1) =
     liftedCoefficient P n:=by
 unfold liftedCoefficient
 rw [map_mul,collectR_X_R,Polynomial.coeff_X_mul]
theorem liftedCoefficient_support_exact
   (P:MvPolynomial (Fin 4) K) (n:ℕ) (e:Fin 4 →₀ ℕ)
   (he:e ∈ (liftedCoefficient P n).support) :
   ∃ d ∈ P.support,d 2 = n ∧ e 2 = 0 ∧ ∀ i,i ≠ 2 → e i = d i:=by
 classical
 have heR:e 2 = 0:=by
   have hh:=MvPolynomial.monomial_le_degreeOf (2:Fin 4) he
   rw [liftedCoefficient_R_degree] at hh
   omega
 change e ∈ (embedCoefficients K ((collectR K P).coeff n)).support at he
 rw [embedCoefficients_eq_rename,
   MvPolynomial.support_rename_of_injective Subtype.val_injective] at he
 obtain ⟨u,hu,heu⟩:=Finset.mem_image.mp he
 have hopt:u.optionElim n ∈
     (MvPolynomial.rename (Equiv.optionSubtypeNe (2:Fin 4)).symm P).support :=
   (MvPolynomial.mem_support_coeff_optionEquivLeft (R:=K)).mp hu
 rw [MvPolynomial.support_rename_of_injective
   (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective] at hopt
 obtain ⟨d,hd,hdu⟩:=Finset.mem_image.mp hopt
 refine ⟨d,hd,?_,heR,?_⟩
 · have huv:=congrArg
     (fun f:Option RemainingCoordinates →₀ ℕ =>
       f ((Equiv.optionSubtypeNe (2:Fin 4)).symm 2)) hdu
   rw [Finsupp.mapDomain_apply (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective] at huv
   simpa [Equiv.optionSubtypeNe_symm_apply] using huv
 · intro i hi
   have hev:e i = u ⟨i,hi⟩:=by
     rw [← heu]
     exact Finsupp.mapDomain_apply Subtype.val_injective u ⟨i,hi⟩
   have huv:=congrArg
     (fun f:Option RemainingCoordinates →₀ ℕ =>
       f ((Equiv.optionSubtypeNe (2:Fin 4)).symm i)) hdu
   rw [Finsupp.mapDomain_apply (Equiv.optionSubtypeNe (2:Fin 4)).symm.injective] at huv
   have hindex:(Equiv.optionSubtypeNe (2:Fin 4)).symm i = some ⟨i,hi⟩:=by
     simp [Equiv.optionSubtypeNe_symm_apply,hi]
   rw [hindex,Finsupp.optionElim_apply_some] at huv
   exact hev.trans huv.symm
theorem liftedCoefficient_weight_add_le (weights:Fin 4 → ℕ)
   (P:MvPolynomial (Fin 4) K) (n:ℕ) (hn:liftedCoefficient P n ≠ 0) :
   MvPolynomial.weightedTotalDegree weights (liftedCoefficient P n) + n * weights 2 ≤
     MvPolynomial.weightedTotalDegree weights P:=by
 classical
 obtain ⟨e,he,hmax⟩:=Finset.exists_mem_eq_sup
   (liftedCoefficient P n).support (MvPolynomial.support_nonempty.mpr hn)
   (Finsupp.weight weights)
 obtain ⟨d,hd,hdR,heR,heq⟩:=liftedCoefficient_support_exact P n e he
 have hw:Finsupp.weight weights e + n * weights 2 = Finsupp.weight weights d:=by
   rw [weight_fin4,weight_fin4,hdR,heR,
     heq 0 (by decide),heq 1 (by decide),heq 3 (by decide)]
   omega
 change (liftedCoefficient P n).support.sup (Finsupp.weight weights) + _ ≤ _
 rw [hmax,hw]
 exact MvPolynomial.le_weightedTotalDegree weights hd
theorem liftedCoefficient_weight_le_sub (weights:Fin 4 → ℕ)
   (P:MvPolynomial (Fin 4) K) (n:ℕ) :
   MvPolynomial.weightedTotalDegree weights (liftedCoefficient P n) ≤
     MvPolynomial.weightedTotalDegree weights P - n * weights 2:=by
 by_cases hn:liftedCoefficient P n = 0
 · simp [hn,MvPolynomial.weightedTotalDegree]
 · have h:=liftedCoefficient_weight_add_le weights P n hn
   omega
theorem liftedCoefficient_eq_zero_of_weight_lt (weights:Fin 4 → ℕ)
   (P:MvPolynomial (Fin 4) K) (n:ℕ)
   (hP:MvPolynomial.weightedTotalDegree weights P < n * weights 2) :
   liftedCoefficient P n = 0:=by
 by_contra hn
 have h:=liftedCoefficient_weight_add_le weights P n hn
 omega
theorem degreeR_le_sub_one_of_top_zero (P:MvPolynomial (Fin 4) K) (t:ℕ)
   (ht:0 < t) (hP:P.degreeOf 2 ≤ t) (hzero:liftedCoefficient P t = 0) :
   P.degreeOf 2 ≤ t - 1:=by
 rw [← collectR_natDegree]
 apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
 intro n hn
 by_cases heq:n = t
 · subst n
   exact (liftedCoefficient_eq_zero_iff P t).mp hzero
 · exact Polynomial.coeff_eq_zero_of_natDegree_lt
     (by rw [collectR_natDegree]; omega)
theorem degreeR_sub_cancel_top (W F q:MvPolynomial (Fin 4) K) (t s k:ℕ)
   (ht:0 < t) (hW:W.degreeOf 2 ≤ t) (hF:F.degreeOf 2 ≤ s)
   (hq:q.degreeOf 2 = 0) (hks:k + s = t)
   (hcoeff:liftedCoefficient W t = q * liftedCoefficient F s) :
   (W - q * MvPolynomial.X (2:Fin 4) ^ k * F).degreeOf 2 ≤ t - 1:=by
 have hR:((MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K) ^ k).degreeOf 2 ≤ k:=by
   simpa using MvPolynomial.degreeOf_pow_le (2:Fin 4)
     (MvPolynomial.X (2:Fin 4):MvPolynomial (Fin 4) K) k
 have hqR:(q * MvPolynomial.X (2:Fin 4) ^ k).degreeOf 2 ≤ k:=by
   have h:=MvPolynomial.degreeOf_mul_le (2:Fin 4) q
     ((MvPolynomial.X (2:Fin 4)) ^ k)
   omega
 have hprod:(q * MvPolynomial.X (2:Fin 4) ^ k * F).degreeOf 2 ≤ t:=by
   have h:=RCN313.degree_mul_bound (2:Fin 4) hqR hF
   omega
 apply degreeR_le_sub_one_of_top_zero _ t ht
   (RCN313.degree_sub_bound (2:Fin 4) hW hprod)
 rw [liftedCoefficient_sub,← hks,
   liftedCoefficient_mul_top _ F k s hqR hF,
   liftedCoefficient_mul_degree_zero_left _ _ k hq,
   liftedCoefficient_X_R_pow,mul_one,hks,hcoeff,sub_self]
end
end ProximityPrize.SubmissionLower.RCN261
end PackedLegacy_N6

/-! Packed from ProximityPrize.SubmissionLower.N8. -/
section PackedLegacy_N8
namespace ProximityPrize.SubmissionLower.RCN262
open scoped BigOperators
open RCN077 RCN313 RCN293 RCN261
noncomputable section
set_option maxHeartbeats 800000
variable {K:Type*} [Field K]
theorem liftedCoefficient_polyH_top (F:Poly K) (s:ℕ) (hs:1 ≤ s) :
   liftedCoefficient (polyH K F) (s - 1) = (s:Poly K) * liftedCoefficient F s:=by
 simpa only [polyH,map_natCast] using liftedCoefficient_pderiv_R_top F s hs
theorem liftedCoefficient_polyG_top (F:Poly K) (s:ℕ)
   (hF:F.degreeOf (2:Fin 4) ≤ s) :
   liftedCoefficient (polyG K F) (s + 1) =
     -MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s):=by
 have hPX:=pderiv_degree_bound (0:Fin 4) (2:Fin 4) F s hF
 have hx:liftedCoefficient (MvPolynomial.pderiv (0:Fin 4) F) (s + 1) = 0 :=
   liftedCoefficient_eq_zero_of_degree_lt _ _ (by omega)
 simp only [polyG,liftedCoefficient_neg,liftedCoefficient_add,hx,zero_add,
   liftedCoefficient_X_R_mul,liftedCoefficient_pderiv_other F 1 (by decide) s]
theorem vectorNumerator_top_coefficient (F P:Poly K) (a s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (hP:P.degreeOf (2:Fin 4) ≤ a) :
   liftedCoefficient (vectorNumerator F P) (a + s) =
     (s:Poly K) * liftedCoefficient F s *
         MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient P a) -
       (a:Poly K) * MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s) *
         liftedCoefficient P a:=by
 let H:=polyH K F
 let G:=polyG K F
 let R:Poly K:=MvPolynomial.X (2:Fin 4)
 have hR:R.degreeOf (2:Fin 4) ≤ 1:=by simp [R]
 have hH:H.degreeOf (2:Fin 4) ≤ s - 1 :=
   pderiv_same_degree_bound (2:Fin 4) F s hF
 have hG:G.degreeOf (2:Fin 4) ≤ s + 1 :=
   polyG_degree_bound (2:Fin 4) F s 1 hF hR
 have hPX:=pderiv_degree_bound (0:Fin 4) (2:Fin 4) P a hP
 have hPY:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) P a hP
 have hPR:=pderiv_same_degree_bound (2:Fin 4) P a hP
 have hcR:liftedCoefficient R 1 = 1:=by
   simpa only [R,pow_one] using liftedCoefficient_X_R_pow (K:=K) 1
 have hcH:liftedCoefficient H (s - 1) = (s:Poly K) * liftedCoefficient F s :=
   liftedCoefficient_polyH_top F s hs
 have hRH:(R * H).degreeOf (2:Fin 4) ≤ s:=by
   have h:=degree_mul_bound (2:Fin 4) hR hH
   omega
 have hcRH:liftedCoefficient (R * H) s = (s:Poly K) * liftedCoefficient F s:=by
   have h:=liftedCoefficient_mul_top R H 1 (s - 1) hR hH
   rw [show 1 + (s - 1) = s by omega,hcR,hcH,one_mul] at h
   exact h
 have hx:liftedCoefficient (H * MvPolynomial.pderiv (0:Fin 4) P) (a + s) = 0:=by
   apply liftedCoefficient_eq_zero_of_degree_lt
   have h:=degree_mul_bound (2:Fin 4) hH hPX
   omega
 have hy:liftedCoefficient (R * H * MvPolynomial.pderiv (1:Fin 4) P) (a + s) =
     (s:Poly K) * liftedCoefficient F s *
       MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient P a):=by
   have h:=liftedCoefficient_mul_top (R * H) (MvPolynomial.pderiv (1:Fin 4) P)
     s a hRH hPY
   rw [hcRH,liftedCoefficient_pderiv_other P 1 (by decide) a] at h
   simpa only [Nat.add_comm] using h
 have hr:liftedCoefficient (G * MvPolynomial.pderiv (2:Fin 4) P) (a + s) =
     -(a:Poly K) * MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s) *
       liftedCoefficient P a:=by
   by_cases ha:a = 0
   · have hz:=pderiv_eq_zero_of_degree_bound_zero (2:Fin 4) P (by simpa [ha] using hP)
     simp [ha,hz]
   · have hapos:0 < a:=Nat.pos_of_ne_zero ha
     have h:=liftedCoefficient_mul_top G (MvPolynomial.pderiv (2:Fin 4) P)
       (s + 1) (a - 1) hG hPR
     rw [show s + 1 + (a - 1) = a + s by omega,
       liftedCoefficient_polyG_top F s hF,
       liftedCoefficient_pderiv_R_top P a hapos,map_natCast] at h
     rw [h]
     ring
 change liftedCoefficient (H * MvPolynomial.pderiv (0:Fin 4) P +
   R * H * MvPolynomial.pderiv (1:Fin 4) P +
     G * MvPolynomial.pderiv (2:Fin 4) P) (a + s) = _
 rw [liftedCoefficient_add,liftedCoefficient_add,hx,hy,hr]
 ring
theorem vectorNumerator_H_top_coefficient (F:Poly K) (s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s) :
   liftedCoefficient (vectorNumerator F (polyH K F)) (2 * s - 1) =
     (s:Poly K) * liftedCoefficient F s *
       MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s):=by
 have hH:=pderiv_same_degree_bound (2:Fin 4) F s hF
 have h:=vectorNumerator_top_coefficient F (polyH K F) (s - 1) s hs hF hH
 rw [show s - 1 + s = 2 * s - 1 by omega,
   liftedCoefficient_polyH_top F s hs] at h
 rw [h,MvPolynomial.pderiv_mul]
 simp only [Derivation.map_natCast,zero_mul,mul_zero,add_zero,zero_add]
 rw [Nat.cast_sub hs]
 simp only [Nat.cast_one]
 ring
theorem numeratorStep_top_coefficient (F P:Poly K) (a s b:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (hP:P.degreeOf (2:Fin 4) ≤ a) :
   liftedCoefficient (numeratorStep K F b P) (a + (2 * s - 1)) =
     liftedCoefficient F s * ((s:Poly K) *
       ((s:Poly K) * liftedCoefficient F s *
           MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient P a) -
         ((a + 2 * b:ℕ):Poly K) *
           MvPolynomial.pderiv (1:Fin 4) (liftedCoefficient F s) *
             liftedCoefficient P a)):=by
 have hH:=pderiv_same_degree_bound (2:Fin 4) F s hF
 have hV:=vectorNumerator_R_degree_bound F P a s hs hF hP
 have hVH:(vectorNumerator F (polyH K F)).degreeOf (2:Fin 4) ≤ 2 * s - 1:=by
   have h:=vectorNumerator_R_degree_bound F (polyH K F) (s - 1) s hs hF hH
   omega
 have hfirst:=liftedCoefficient_mul_top (polyH K F) (vectorNumerator F P)
   (s - 1) (a + s) hH hV
 rw [show s - 1 + (a + s) = a + (2 * s - 1) by omega,
   liftedCoefficient_polyH_top F s hs,
   vectorNumerator_top_coefficient F P a s hs hF hP] at hfirst
 have hlast:=liftedCoefficient_mul_top P (vectorNumerator F (polyH K F))
   a (2 * s - 1) hP hVH
 rw [vectorNumerator_H_top_coefficient F s hs hF] at hlast
 rw [numeratorStep_eq_vector,liftedCoefficient_sub,hfirst]
 rw [show ((2 * b:ℕ):Poly K) * P * vectorNumerator F (polyH K F) =
   ((2 * b:ℕ):Poly K) * (P * vectorNumerator F (polyH K F)) by ring,
   liftedCoefficient_natCast_mul,hlast]
 push_cast
 ring
theorem excessFactor_R_degree (F P:Poly K) (s b:ℕ) :
   (excessFactor F P s b).degreeOf (2:Fin 4) = 0:=by
 have hf:(liftedCoefficient F s).degreeOf (2:Fin 4) ≤ 0 :=
   (liftedCoefficient_R_degree F s).le
 have hc:(liftedCoefficient P (2 * b * (s - 1))).degreeOf (2:Fin 4) ≤ 0 :=
   (liftedCoefficient_R_degree P _).le
 have hdf:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) _ 0 hf
 have hdc:=pderiv_degree_bound (1:Fin 4) (2:Fin 4) _ 0 hc
 have hs:(s:Poly K).degreeOf (2:Fin 4) ≤ 0:=(degree_natCast_eq_zero 2 s).le
 have hn:((2 * b * (s - 1) + 2 * b:ℕ):Poly K).degreeOf (2:Fin 4) ≤ 0 :=
   (degree_natCast_eq_zero 2 _).le
 have hleft:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hs hf) hdc
 have hright:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hn hdf) hc
 have hinner:=degree_sub_bound (2:Fin 4) hleft hright
 have h:=degree_mul_bound (2:Fin 4) hs hinner
 exact Nat.eq_zero_of_le_zero (by simpa only [excessFactor,Nat.zero_add] using h)
theorem reducedStep_R_degree_bound (F P:Poly K) (s b:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (hP:P.degreeOf (2:Fin 4) ≤ 2 * b * (s - 1)) :
   (reducedStep F P s b).degreeOf (2:Fin 4) ≤ 2 * (b + 1) * (s - 1):=by
 let a:=2 * b * (s - 1)
 let t:=a + (2 * s - 1)
 have ht:0 < t:=by dsimp [t]; omega
 have hW:=numeratorStep_R_degree_bound F P b a s hs hF hP
 have hcoeff:liftedCoefficient (numeratorStep K F b P) t =
     excessFactor F P s b * liftedCoefficient F s:=by
   rw [numeratorStep_top_coefficient F P a s b hs hF hP]
   dsimp [excessFactor,a]
   ring
 have hks:(2 * b + 1) * (s - 1) + s = t:=by
   dsimp [t,a]
   have hsi:s = (s - 1) + 1:=by omega
   conv_lhs => rhs; rw [hsi]
   have ht':2 * s - 1 = 2 * (s - 1) + 1:=by omega
   rw [ht']
   ring
 have h:=degreeR_sub_cancel_top (numeratorStep K F b P) F (excessFactor F P s b)
   t s ((2 * b + 1) * (s - 1)) ht hW hF (excessFactor_R_degree F P s b) hks hcoeff
 have heq:t - 1 = 2 * (b + 1) * (s - 1):=by
   dsimp [t,a]
   have ht':2 * s - 1 = 2 * (s - 1) + 1:=by omega
   rw [ht',← Nat.add_assoc,Nat.add_sub_cancel]
   ring
 simpa only [reducedStep,reductionMultiplier,heq] using h
theorem reducedNumerator_R_degree_bound (F:Poly K) (s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s) (b:ℕ) :
   (reducedNumerator F s b).degreeOf (2:Fin 4) ≤ 2 * b * (s - 1):=by
 induction b with
 | zero => simp [MvPolynomial.degreeOf_X_of_ne (by decide:(2:Fin 4) ≠ 1)]
 | succ b ih => exact reducedStep_R_degree_bound F (reducedNumerator F s b) s b hs hF ih
theorem reducedCommonNumeratorTerm_R_degree_bound (F:Poly K) (s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (w j:ℕ) (hj:j ≤ w) (c:ℕ → K) (x:K) :
   (reducedCommonNumeratorTerm F s w c x j).degreeOf (2:Fin 4) ≤ 2 * w * (s - 1):=by
 have hN:=reducedNumerator_R_degree_bound F s hs hF j
 have hCN:(MvPolynomial.C (c j) * reducedNumerator F s j).degreeOf (2:Fin 4) ≤
     2 * j * (s - 1) :=
   (MvPolynomial.degreeOf_C_mul_le (reducedNumerator F s j) (2:Fin 4) (c j)).trans hN
 have hH:=pderiv_same_degree_bound (2:Fin 4) F s hF
 have hHP:=degree_pow_bound (2:Fin 4) (2 * (w - j)) hH
 have hXP:((MvPolynomial.C x - MvPolynomial.X (0:Fin 4):Poly K) ^ j).degreeOf
     (2:Fin 4) ≤ 0:=by
   simpa only [Nat.mul_zero] using
     degree_pow_bound (2:Fin 4) j (shiftedX_degree_bound (2:Fin 4) (by decide) x)
 have h:=degree_mul_bound (2:Fin 4) (degree_mul_bound (2:Fin 4) hCN hHP) hXP
 apply h.trans
 have hw:j + (w - j) = w:=by omega
 calc
   2 * j * (s - 1) + 2 * (w - j) * (s - 1) + 0 =
       2 * (j + (w - j)) * (s - 1):=by ring
   _ ≤ 2 * w * (s - 1):=by simp only [hw,le_refl]
theorem reducedClearedTaylorNumerator_R_degree_bound (F:Poly K) (s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (w:ℕ) (c:ℕ → K) (x:K) :
   (reducedClearedTaylorNumerator F s w c x).degreeOf (2:Fin 4) ≤ 2 * w * (s - 1):=by
 apply degree_sum_bound (2:Fin 4)
 intro j hj
 exact reducedCommonNumeratorTerm_R_degree_bound F s hs hF w j
   (by have h:=Finset.mem_range.mp hj; omega) c x
theorem reducedAgreementNumerator_R_degree_bound (F:Poly K) (s:ℕ)
   (hs:1 ≤ s) (hF:F.degreeOf (2:Fin 4) ≤ s)
   (w:ℕ) (c:ℕ → K) (x u₀ u₁:K) :
   (reducedAgreementNumerator F s w c x u₀ u₁).degreeOf (2:Fin 4) ≤ 2 * w * (s - 1):=by
 apply degree_sub_bound (2:Fin 4)
 · exact reducedClearedTaylorNumerator_R_degree_bound F s hs hF w c x
 · have hA:=affineSeedPolynomial_degree_bound (2:Fin 4) 0
     (by simp [MvPolynomial.degreeOf_X_of_ne (by decide:(2:Fin 4) ≠ 3)]) u₀ u₁
   have hH:=pderiv_same_degree_bound (2:Fin 4) F s hF
   simpa only [polyH,Nat.zero_add] using
     degree_mul_bound (2:Fin 4) hA (degree_pow_bound (2:Fin 4) (2 * w) hH)
end
end ProximityPrize.SubmissionLower.RCN262
end PackedLegacy_N8

/-! Packed from ProximityPrize.SubmissionLower.N9. -/
section PackedLegacy_N9
namespace ProximityPrize.SubmissionLower.RCN262
open scoped BigOperators
open RCN077 RCN313 RCN293 RCN261 RCN234 RCN179
noncomputable section
variable {K:Type*} [Field K]
theorem excessFactor_wt_le (weights:Fin 4 → ℕ)
   (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F P:Poly K) (s b C:ℕ) (hs:1 ≤ s)
   (hF:wt weights F ≤ C) (hP:wt weights P ≤ 1 + 2 * b * (C - 1)) :
   wt weights (excessFactor F P s b) ≤ (2 * b + 1) * (C - s):=by
 by_cases hfzero:liftedCoefficient F s = 0
 · simp [excessFactor,hfzero,wt,MvPolynomial.weightedTotalDegree]
 let f:=liftedCoefficient F s
 let c:=liftedCoefficient P (2 * b * (s - 1))
 let D:=C - s
 have hfadd:=liftedCoefficient_weight_add_le weights F s hfzero
 change wt weights f + s * weights 2 ≤ wt weights F at hfadd
 rw [hR,Nat.mul_one] at hfadd
 have hsC:s ≤ C:=by omega
 have hf:wt weights f ≤ D:=by dsimp [D]; omega
 have hc:wt weights c ≤ 1 + 2 * b * D:=by
   have h:=liftedCoefficient_weight_le_sub weights P (2 * b * (s - 1))
   change wt weights c ≤ wt weights P - 2 * b * (s - 1) * weights 2 at h
   rw [hR,Nat.mul_one] at h
   have h':=h.trans (Nat.sub_le_sub_right hP (2 * b * (s - 1)))
   have hdecomp:C - 1 = D + (s - 1):=by dsimp [D]; omega
   have heq:1 + 2 * b * (C - 1) = (1 + 2 * b * D) + 2 * b * (s - 1):=by
     rw [hdecomp]
     ring
   rwa [heq,Nat.add_sub_cancel] at h'
 have hdc:wt weights (MvPolynomial.pderiv (1:Fin 4) c) ≤ 2 * b * D:=by
   have h:=wt_pderiv_le weights c 1 (1 + 2 * b * D) hc
   rw [hY] at h
   omega
 have hdf:wt weights (MvPolynomial.pderiv (1:Fin 4) f) ≤ D - 1:=by
   simpa only [hY] using wt_pderiv_le weights f 1 D hf
 have hsf:wt weights ((s:Poly K) * f) ≤ D:=by
   have h:=wt_mul_le weights (s:Poly K) f
   rw [wt_natCast,Nat.zero_add] at h
   exact h.trans hf
 have hleft:wt weights ((s:Poly K) * f * MvPolynomial.pderiv (1:Fin 4) c) ≤
     (2 * b + 1) * D:=by
   have h:=(wt_mul_le weights ((s:Poly K) * f) (MvPolynomial.pderiv (1:Fin 4) c)).trans
     (Nat.add_le_add hsf hdc)
   apply h.trans
   apply le_of_eq
   ring
 have hright:wt weights (((2 * b * (s - 1) + 2 * b:ℕ):Poly K) *
     MvPolynomial.pderiv (1:Fin 4) f * c) ≤ (2 * b + 1) * D:=by
   by_cases hD:D = 0
   · have hz:MvPolynomial.pderiv (1:Fin 4) f = 0 :=
       pderiv_eq_zero_of_wt_lt weights f 1 (by rw [hY]; omega)
     simp [hz,wt,MvPolynomial.weightedTotalDegree]
   · have hn:wt weights (((2 * b * (s - 1) + 2 * b:ℕ):Poly K) *
         MvPolynomial.pderiv (1:Fin 4) f) ≤ D - 1:=by
       have h:=wt_mul_le weights (((2 * b * (s - 1) + 2 * b:ℕ):Poly K))
         (MvPolynomial.pderiv (1:Fin 4) f)
       rw [wt_natCast,Nat.zero_add] at h
       exact h.trans hdf
     have h:=(wt_mul_le weights
       (((2 * b * (s - 1) + 2 * b:ℕ):Poly K) * MvPolynomial.pderiv (1:Fin 4) f)
       c).trans (Nat.add_le_add hn hc)
     apply h.trans
     rw [Nat.add_mul,Nat.one_mul]
     omega
 have hinner:=(wt_sub_le weights
   ((s:Poly K) * f * MvPolynomial.pderiv (1:Fin 4) c)
   (((2 * b * (s - 1) + 2 * b:ℕ):Poly K) * MvPolynomial.pderiv (1:Fin 4) f * c)).trans
   (max_le hleft hright)
 have h:=wt_mul_le weights (s:Poly K)
   ((s:Poly K) * f * MvPolynomial.pderiv (1:Fin 4) c -
     ((2 * b * (s - 1) + 2 * b:ℕ):Poly K) * MvPolynomial.pderiv (1:Fin 4) f * c)
 rw [wt_natCast,Nat.zero_add] at h
 exact h.trans hinner
theorem reductionCorrection_wt_le (weights:Fin 4 → ℕ)
   (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F P:Poly K) (s b C:ℕ) (hs:1 ≤ s)
   (hF:wt weights F ≤ C) (hP:wt weights P ≤ 1 + 2 * b * (C - 1)) :
   wt weights (reductionMultiplier F P s b * F) ≤ 1 + 2 * (b + 1) * (C - 1):=by
 by_cases hfzero:liftedCoefficient F s = 0
 · simp [reductionMultiplier,excessFactor,hfzero,wt,MvPolynomial.weightedTotalDegree]
 have hfadd:=liftedCoefficient_weight_add_le weights F s hfzero
 change wt weights (liftedCoefficient F s) + s * weights 2 ≤ wt weights F at hfadd
 rw [hR,Nat.mul_one] at hfadd
 have hsC:s ≤ C:=by omega
 have hCpos:1 ≤ C:=hs.trans hsC
 have hq:=excessFactor_wt_le weights hY hR F P s b C hs hF hP
 have hpow:wt weights ((MvPolynomial.X (2:Fin 4):Poly K) ^ ((2 * b + 1) * (s - 1))) ≤
     (2 * b + 1) * (s - 1):=by
   have h:=wt_pow_le weights (MvPolynomial.X (2:Fin 4):Poly K) ((2 * b + 1) * (s - 1))
   simpa only [wt_X,hR,Nat.mul_one] using h
 have hqR:=(wt_mul_le weights (excessFactor F P s b)
   ((MvPolynomial.X (2:Fin 4)) ^ ((2 * b + 1) * (s - 1)))).trans
   (Nat.add_le_add hq hpow)
 have h:=(wt_mul_le weights (reductionMultiplier F P s b) F).trans
   (Nat.add_le_add hqR hF)
 apply h.trans
 have hdecomp:(C - s) + (s - 1) = C - 1:=by omega
 apply le_of_eq
 calc
   (2 * b + 1) * (C - s) + (2 * b + 1) * (s - 1) + C =
       (2 * b + 1) * ((C - s) + (s - 1)) + C:=by ring
   _ = (2 * b + 1) * (C - 1) + C:=by rw [hdecomp]
   _ = (2 * b + 1) * (C - 1) + ((C - 1) + 1) :=
     congrArg (fun n => (2 * b + 1) * (C - 1) + n) (Nat.sub_add_cancel hCpos).symm
   _ = 1 + 2 * (b + 1) * (C - 1):=by ring
theorem reducedStep_wt_le (weights:Fin 4 → ℕ)
   (hX:weights 0 = 0) (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F P:Poly K) (s b C:ℕ) (hs:1 ≤ s) (hC:2 ≤ C)
   (hF:wt weights F ≤ C) (hP:wt weights P ≤ 1 + 2 * b * (C - 1)) :
   wt weights (reducedStep F P s b) ≤ 1 + 2 * (b + 1) * (C - 1):=by
 have hstep:=numeratorStep_wt_le_equal_weight weights hX F P b
   (1 + 2 * b * (C - 1)) C (by omega) (by omega) (by omega) (by omega) hF hP
 rw [hR] at hstep
 have hstep':wt weights (numeratorStep K F b P) ≤ 1 + 2 * (b + 1) * (C - 1):=by
   convert hstep using 1 <;> ring
 exact (wt_sub_le weights _ _).trans
   (max_le hstep' (reductionCorrection_wt_le weights hY hR F P s b C hs hF hP))
theorem reducedNumerator_wt_le (weights:Fin 4 → ℕ)
   (hX:weights 0 = 0) (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F:Poly K) (s C:ℕ) (hs:1 ≤ s) (hC:2 ≤ C)
   (hF:wt weights F ≤ C) (b:ℕ) :
   wt weights (reducedNumerator F s b) ≤ 1 + 2 * b * (C - 1):=by
 induction b with
 | zero => simp only [reducedNumerator_zero,wt_X,hY,Nat.mul_zero,Nat.zero_mul,Nat.add_zero,le_refl]
 | succ b ih => exact reducedStep_wt_le weights hX hY hR F (reducedNumerator F s b) s b C hs hC hF ih
theorem reducedCommonNumeratorTerm_wt_le (weights:Fin 4 → ℕ)
   (hX:weights 0 = 0) (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F:Poly K) (s C:ℕ) (hs:1 ≤ s) (hC:2 ≤ C)
   (hF:wt weights F ≤ C) (w j:ℕ) (hj:j ≤ w)
   (c:ℕ → K) (x:K) :
   wt weights (reducedCommonNumeratorTerm F s w c x j) ≤ 1 + 2 * w * (C - 1):=by
 have hN:=reducedNumerator_wt_le weights hX hY hR F s C hs hC hF j
 have hCN:wt weights (MvPolynomial.C (c j) * reducedNumerator F s j) ≤
     1 + 2 * j * (C - 1):=by
   have h:=wt_mul_le weights (MvPolynomial.C (c j)) (reducedNumerator F s j)
   rw [wt_C,Nat.zero_add] at h
   exact h.trans hN
 have hH:wt weights (polyH K F) ≤ C - 1:=by
   simpa only [hR] using wt_polyH_le weights F C hF
 have hHP:=(wt_pow_le weights (polyH K F) (2 * (w - j))).trans
   (Nat.mul_le_mul_left _ hH)
 have hXP:wt weights ((MvPolynomial.C x - MvPolynomial.X (0:Fin 4):Poly K) ^ j) ≤ 0:=by
   have h:=wt_pow_le weights
     (MvPolynomial.C x - MvPolynomial.X (0:Fin 4):Poly K) j
   simpa only [shiftedX_wt_eq_zero weights hX x,Nat.mul_zero] using h
 have h1:=(wt_mul_le weights (MvPolynomial.C (c j) * reducedNumerator F s j)
   (polyH K F ^ (2 * (w - j)))).trans (Nat.add_le_add hCN hHP)
 have h2:=(wt_mul_le weights
   (MvPolynomial.C (c j) * reducedNumerator F s j * polyH K F ^ (2 * (w - j)))
   ((MvPolynomial.C x - MvPolynomial.X (0:Fin 4)) ^ j)).trans (Nat.add_le_add h1 hXP)
 apply h2.trans
 have hw:j + (w - j) = w:=by omega
 apply le_of_eq
 calc
   (1 + 2 * j * (C - 1) + 2 * (w - j) * (C - 1)) + 0 =
       1 + 2 * (j + (w - j)) * (C - 1):=by ring
   _ = 1 + 2 * w * (C - 1):=by rw [hw]
theorem reducedClearedTaylorNumerator_wt_le (weights:Fin 4 → ℕ)
   (hX:weights 0 = 0) (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F:Poly K) (s C:ℕ) (hs:1 ≤ s) (hC:2 ≤ C)
   (hF:wt weights F ≤ C) (w:ℕ) (c:ℕ → K) (x:K) :
   wt weights (reducedClearedTaylorNumerator F s w c x) ≤ 1 + 2 * w * (C - 1):=by
 apply wt_sum_le
 intro j hj
 exact reducedCommonNumeratorTerm_wt_le weights hX hY hR F s C hs hC hF w j
   (by have h:=Finset.mem_range.mp hj; omega) c x
theorem reducedAgreementNumerator_wt_le (weights:Fin 4 → ℕ)
   (hX:weights 0 = 0) (hY:weights 1 = 1) (hR:weights 2 = 1)
   (F:Poly K) (s C:ℕ) (hs:1 ≤ s) (hC:2 ≤ C)
   (hF:wt weights F ≤ C) (w:ℕ) (c:ℕ → K) (x u₀ u₁:K) :
   wt weights (reducedAgreementNumerator F s w c x u₀ u₁) ≤
     max 1 (weights 3) + 2 * w * (C - 1):=by
 have hTaylor:=reducedClearedTaylorNumerator_wt_le weights hX hY hR F s C hs hC hF w c x
 have hA:=affineSeedPolynomial_wt_le weights u₀ u₁
 have hH:wt weights (polyH K F) ≤ C - 1:=by
   simpa only [hR] using wt_polyH_le weights F C hF
 have hHP:=(wt_pow_le weights (polyH K F) (2 * w)).trans
   (Nat.mul_le_mul_left _ hH)
 have hprod:=(wt_mul_le weights (affineSeedPolynomial u₀ u₁) (polyH K F ^ (2 * w))).trans
   (Nat.add_le_add hA hHP)
 exact (wt_sub_le weights _ _).trans (max_le
   (hTaylor.trans (Nat.add_le_add_right (Nat.le_max_left _ _) _))
   (hprod.trans (Nat.add_le_add_right (Nat.le_max_right _ _) _)))
end
end ProximityPrize.SubmissionLower.RCN262
end PackedLegacy_N9

/-! Packed from ProximityPrize.SubmissionLower.Z5. -/
section PackedLegacy_Z5
namespace ProximityPrize.SubmissionLower.RCN162
open scoped Classical
open RCN094
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
def forwardResidualPoint
   (aY v bY aS bS cS:K) (q:Fin 3 → K):Fin 3 → K:=
 ![aY+v*q 0+bY*q 2,
   aS+v*q 1+bS*q 0+cS*q 2,
   q 2]
theorem eval_residualEquiv
   (aY v bY aS bS cS:K) (hv:v≠0)
   (q:Fin 3 → K) (F:Poly3 K):
   MvPolynomial.eval q
       (residualEquiv aY v bY aS bS cS hv F)=
     MvPolynomial.eval (forwardResidualPoint aY v bY aS bS cS q) F:=by
 change MvPolynomial.eval₂Hom (RingHom.id K) q
     (residualAlgHom aY v bY aS bS cS F)=
   MvPolynomial.eval₂Hom (RingHom.id K)
     (forwardResidualPoint aY v bY aS bS cS q) F
 have hq:q=![q 0,q 1,q 2]:=by
   funext i
   fin_cases i <;> rfl
 have hforward:
     forwardResidualPoint aY v bY aS bS cS q=
       ![aY+v*q 0+bY*q 2,
         aS+v*q 1+bS*q 0+cS*q 2,
         q 2]:=by
   funext i
   fin_cases i <;> simp [forwardResidualPoint]
 calc
   _=MvPolynomial.eval₂Hom (RingHom.id K) ![q 0,q 1,q 2]
         (residualAlgHom aY v bY aS bS cS F):=by rw [←hq]
   _=MvPolynomial.eval₂Hom (RingHom.id K)
         ![aY+v*q 0+bY*q 2,
           aS+v*q 1+bS*q 0+cS*q 2,
           q 2] F:=by
     simpa only [Algebra.algebraMap_self,RingHom.id_apply] using
       (eval₂Hom_residual F (q 0) (q 1) (q 2) aY v bY aS bS cS)
   _=_:=by rw [hforward]
theorem comap_pointKernel_residualEquiv
   (aY v bY aS bS cS:K) (hv:v≠0)
   (q:Fin 3 → K):
   (RingHom.ker (MvPolynomial.aeval q).toRingHom).comap
       (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom=
     RingHom.ker
       (MvPolynomial.aeval
         (forwardResidualPoint aY v bY aS bS cS q)).toRingHom:=by
 ext F
 simp only [Ideal.mem_comap,RingHom.mem_ker]
 change MvPolynomial.eval q
     (residualEquiv aY v bY aS bS cS hv F)=0 ↔
   MvPolynomial.eval (forwardResidualPoint aY v bY aS bS cS q) F=0
 rw [eval_residualEquiv]
theorem map_le_pointKernel_iff
   (aY v bY aS bS cS:K) (hv:v≠0)
   (P:Ideal (Poly3 K)) (q:Fin 3 → K):
   P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom ≤
       RingHom.ker (MvPolynomial.aeval q).toRingHom ↔
     P ≤ RingHom.ker
       (MvPolynomial.aeval
         (forwardResidualPoint aY v bY aS bS cS q)).toRingHom:=by
 rw [Ideal.map_le_iff_le_comap,
   comap_pointKernel_residualEquiv aY v bY aS bS cS hv q]
theorem map_le_pointKernel_of_forward_eq
   (aY v bY aS bS cS:K) (hv:v≠0)
   (P:Ideal (Poly3 K)) (q qOld:Fin 3 → K)
   (hforward:forwardResidualPoint aY v bY aS bS cS q=qOld)
   (hold:P ≤ RingHom.ker (MvPolynomial.aeval qOld).toRingHom):
   P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom ≤
     RingHom.ker (MvPolynomial.aeval q).toRingHom:=by
 rw [map_le_pointKernel_iff,hforward]
 exact hold
structure RegularPrimeData (G T H:Poly3 K) where
 ideal:Ideal (Poly3 K)
 isPrime:ideal.IsPrime
 G_mem:G∈ideal
 T_mem:T∈ideal
 H_not_mem:H∉ideal
 ne_point:∀ q:Fin 3 → K,
   ideal≠RingHom.ker (MvPolynomial.aeval q).toRingHom
def RegularPrimeData.mulRegularityUnit
   {G T H:Poly3 K} (D:RegularPrimeData G T H)
   (c:K) (hc:c≠0):
   RegularPrimeData G T (MvPolynomial.C c*H):=by
 have hu:IsUnit (MvPolynomial.C c:Poly3 K):=
   (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
 refine {
   ideal:=D.ideal
   isPrime:=D.isPrime
   G_mem:=D.G_mem
   T_mem:=D.T_mem
   H_not_mem:=?_
   ne_point:=D.ne_point
 }
 intro hmem
 exact D.H_not_mem ((D.ideal.unit_mul_mem_iff_mem hu).mp hmem)
@[simp] theorem RegularPrimeData.mulRegularityUnit_ideal
   {G T H:Poly3 K} (D:RegularPrimeData G T H)
   (c:K) (hc:c≠0):
   (D.mulRegularityUnit c hc).ideal=D.ideal:=rfl
def RegularPrimeData.mapResidual
   {G T H:Poly3 K} (D:RegularPrimeData G T H)
   (aY v bY aS bS cS:K) (hv:v≠0):
   RegularPrimeData
     (residualAlgHom aY v bY aS bS cS G)
     (residualAlgHom aY v bY aS bS cS T)
     (residualAlgHom aY v bY aS bS cS H):=by
 let E:=residualEquiv aY v bY aS bS cS hv
 let Pnext:Ideal (Poly3 K):=D.ideal.map E.toRingEquiv.toRingHom
 letI:D.ideal.IsPrime:=D.isPrime
 haveI:Pnext.IsPrime:=Ideal.map_isPrime_of_equiv E.toRingEquiv
 refine {
   ideal:=Pnext
   isPrime:=inferInstance
   G_mem:=?_
   T_mem:=?_
   H_not_mem:=?_
   ne_point:=?_
 }
 · exact Ideal.mem_map_of_mem E.toRingEquiv.toRingHom D.G_mem
 · exact Ideal.mem_map_of_mem E.toRingEquiv.toRingHom D.T_mem
 · intro hmem
   exact D.H_not_mem
     ((Ideal.apply_mem_of_equiv_iff (f:=E.toRingEquiv)
       (I:=D.ideal) (x:=H)).mp hmem)
 · intro q heq
   apply D.ne_point (forwardResidualPoint aY v bY aS bS cS q)
   have hback:Pnext.comap E.toRingEquiv.toRingHom=D.ideal:=by
     ext F
     exact Ideal.apply_mem_of_equiv_iff (f:=E.toRingEquiv)
       (I:=D.ideal) (x:=F)
   rw [←hback,heq,
     comap_pointKernel_residualEquiv aY v bY aS bS cS hv q]
@[simp] theorem RegularPrimeData.mapResidual_ideal
   {G T H:Poly3 K} (D:RegularPrimeData G T H)
   (aY v bY aS bS cS:K) (hv:v≠0):
   (D.mapResidual aY v bY aS bS cS hv).ideal=
     D.ideal.map
       (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom:=rfl
theorem mem_mapResidual_iff
   {G T H:Poly3 K} (D:RegularPrimeData G T H)
   (aY v bY aS bS cS:K) (hv:v≠0) (F:Poly3 K):
   residualAlgHom aY v bY aS bS cS F∈
       (D.mapResidual aY v bY aS bS cS hv).ideal ↔
     F∈D.ideal:=by
 exact Ideal.apply_mem_of_equiv_iff
   (f:=(residualEquiv aY v bY aS bS cS hv).toRingEquiv)
     (I:=D.ideal) (x:=F)
end
end ProximityPrize.SubmissionLower.RCN162
end PackedLegacy_Z5

/-! Packed from ProximityPrize.SubmissionLower.AE. -/
section PackedLegacy_AE
namespace ProximityPrize.SubmissionLower.RCN272
open scoped Classical BigOperators
open RCN002 RCN007 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def FiniteZeroSetBound
   (P:Ideal (MvPolynomial (Fin 3) Ω))
   (A:MvPolynomial (Fin 3) Ω) (cost:ℕ):Prop:=
 ∀ points:Finset (Fin 3 → Ω),
   (∀ v∈points,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom) →
   (∀ v∈points,MvPolynomial.aeval v A=0) →
   points.card ≤ cost
structure ResidualComponentBudget
   (G T H:MvPolynomial (Fin 3) Ω)
   (Admissible:MvPolynomial (Fin 3) Ω → Prop) (wholeCost:ℕ) where
 cost:RegularComponent Ω G T H → ℕ
 zero_le:∀ (C:RegularComponent Ω G T H)
     (A:MvPolynomial (Fin 3) Ω),
   Admissible A → A∉C.1 → FiniteZeroSetBound C.1 A (cost C)
 sum_cost_le:(∑ C:RegularComponent Ω G T H,cost C) ≤ wholeCost
theorem agreement_fiber_card_le_of_zero_bound
   (P:Ideal (MvPolynomial (Fin 3) Ω))
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (Γ:Finset K)
   (p w:ℕ) [CharP Ω p] (hchar:w < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (x u₀ u₁:K) (cost:ℕ)
   (hzero:FiniteZeroSetBound P
     (agreementPolynomial φ F w x u₀ u₁) cost):
   (Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)).card ≤ cost:=by
 classical
 let fiber:=Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)
 let points:=fiber.image (selectedPoint φ selected)
 have hpointsP:∀ v∈points,
     P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hv
   exact hpoint γ (Finset.mem_filter.mp hγ).1
 have hpointsA:∀ v∈points,
     MvPolynomial.aeval v (agreementPolynomial φ F w x u₀ u₁)=0:=by
   intro v hv
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hv
   obtain ⟨hΓ,hagree⟩:=Finset.mem_filter.mp hγ
   exact (selected_agreement_zero_iff φ F selected p w hchar γ
     (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) x u₀ u₁).mpr hagree
 have hcount:=hzero points hpointsP hpointsA
 have hcard:points.card=fiber.card:=
   Finset.card_image_of_injective _ (selectedPoint_injective φ selected)
 rwa [hcard] at hcount
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem prime_seed_incidence_sharp_of_residual_cost
   (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
   (hproj:ProjectionsFiniteSeparable Ω P)
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
     a ≤ (nodes.filter (fun i↦
       (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cost:ℕ)
   (hzero:∀ i∈nodes,
     agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)∉P →
     FiniteZeroSetBound P
       (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) cost):
   Γ.card*(a-w) ≤ (nodes.card-w)*cost+
     (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
 classical
 let I:=identityNodes φ P F nodes x u₀ u₁ w
 let relation:K → ι → Prop:=fun γ i↦
   (selected γ).eval (x i)=u₀ i+γ*u₁ i
 by_cases hI:I.card ≤ w
 · have hfiber:∀ i∈nodes \ I,
       (Γ.filter (fun γ↦relation γ i)).card ≤ cost:=by
     intro i hi
     obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
     have hproper:agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)∉P:=by
       intro hmem
       apply hnotI
       exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
     exact agreement_fiber_card_le_of_zero_bound φ P F selected Γ p w hchar
       hdegree hsolution hregular hpoint (x i) (u₀ i) (u₁ i) cost
       (hzero i hinodes hproper)
   have hcount:=RCN173.sharp_incidence_bound relation Γ nodes I a w
     cost (identityNodes_subset φ P F nodes x u₀ u₁ w) hI hwa han
     hagreement hfiber
   omega
 · have hc:w < I.card:=Nat.lt_of_not_ge hI
   have hvalues:∀ (t:{γ:K//γ∈Γ}) i,i∈I →
       (selected t.1).eval (x i)=u₀ i+t.1*u₁ i:=by
     intro t
     exact selected_agrees_on_identity_nodes φ P F nodes x u₀ u₁ p w hchar
       (selected t.1) t.1 (hdegree t.1 t.2) (hsolution t.1 t.2)
       (hregular t.1 t.2) (hpoint t.1 t.2)
   obtain ⟨P₀,P₁,h₀,h₁,_,hpencil⟩:=
     exists_common_pencil_of_many_identities φ P F hF hH nodes x u₀ u₁ w
       hinj hc (fun t:{γ:K//γ∈Γ}↦t.1)
       (fun t↦selected t.1) (fun t↦hdegree t.1 t.2) hvalues
   have hfilter:Γ.filter
       (fun γ↦selected γ=P₀+Polynomial.C γ*P₁)=Γ:=
     Finset.filter_eq_self.mpr (fun γ hγ↦hpencil ⟨γ,hγ⟩)
   have hΓ:Γ.card ≤ e+1:=by
     have h:=hnoPencil P₀ P₁ h₀ h₁
     rwa [hfilter] at h
   have hZ:=seed_transcendental_of_many_identities φ P F hF hH
     nodes x u₀ u₁ w hw hinj hc hnonpoint
   have hδ:=coordinateDegree_pos_of_transcendental P hproj (2:Fin 3) hZ
   have hcharge:Γ.card*(a-w) ≤
       (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
     calc
       _ ≤ (e+1)*(a-w):=Nat.mul_le_mul_right _ hΓ
       _ ≤ _:=by
         simpa only [Nat.mul_one] using
           Nat.mul_le_mul_left ((e+1)*(a-w)) hδ
   omega
theorem aggregate_component_residual_incidence
   (G T H:MvPolynomial (Fin 3) Ω)
   {Seed:Type*} (S:Finset Seed) (v:Seed → Fin 3 → Ω)
   (hG:∀ γ∈S,MvPolynomial.eval (v γ) G=0)
   (hT:∀ γ∈S,MvPolynomial.eval (v γ) T=0)
   (hH:∀ γ∈S,MvPolynomial.eval (v γ) H≠0)
   (gap nodes pencil wholeCost zBudget:ℕ)
   (cost zDegree:RegularComponent Ω G T H → ℕ)
   (hcomponent:∀ C,
     (componentSeeds Ω G T H S v C).card*gap ≤
       nodes*cost C+pencil*gap*zDegree C)
   (hcost:(∑ C,cost C) ≤ wholeCost)
   (hz:(∑ C,zDegree C) ≤ zBudget):
   S.card*gap ≤ nodes*wholeCost+pencil*gap*zBudget:=by
 classical
 calc
   S.card*gap ≤ (∑ C:RegularComponent Ω G T H,
       (componentSeeds Ω G T H S v C).card)*gap:=
     Nat.mul_le_mul_right gap
       (card_le_sum_componentSeeds Ω G T H S v hG hT hH)
   _=∑ C:RegularComponent Ω G T H,
       (componentSeeds Ω G T H S v C).card*gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ C:RegularComponent Ω G T H,
       (nodes*cost C+pencil*gap*zDegree C):=
     Finset.sum_le_sum (fun C _↦hcomponent C)
   _=nodes*(∑ C:RegularComponent Ω G T H,cost C)+
       pencil*gap*(∑ C:RegularComponent Ω G T H,zDegree C):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum]
   _ ≤ nodes*wholeCost+pencil*gap*zBudget:=
     Nat.add_le_add (Nat.mul_le_mul_left nodes hcost)
       (Nat.mul_le_mul_left (pencil*gap) hz)
theorem proper_cut_seed_bound_of_residual_component_budget
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hdiv:G∣surfaceMap φ F)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hTpoint:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) T=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i↦
       (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (Admissible:MvPolynomial (Fin 3) Ω → Prop)
   (wholeCost zBudget:ℕ)
   (hsparse:ResidualComponentBudget G T (regularitySurface φ F)
     Admissible wholeCost)
   (hadmissible:∀ i∈nodes,
     Admissible (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)))
   (hproj:∀ C:RegularComponent Ω G T (regularitySurface φ F),
     ProjectionsFiniteSeparable Ω C.1)
   (hzbudget:(∑ C:RegularComponent Ω G T (regularitySurface φ F),
     actualCoordinateDegree Ω C.1 2) ≤ zBudget):
   Γ.card*(a-w) ≤ (nodes.card-w)*wholeCost+
     (e+1)*(a-w)*zBudget:=by
 classical
 let H:=regularitySurface φ F
 have hHp:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) H≠0:=by
   intro γ hγ
   change MvPolynomial.eval (selectedPoint φ selected γ)
     (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [selectedPoint_evaluation]
   exact hregular γ hγ
 let zDegree:RegularComponent Ω G T H → ℕ:=
   fun C↦actualCoordinateDegree Ω C.1 2
 have hcomponent:∀ C:RegularComponent Ω G T H,
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C).card*
         (a-w) ≤
       (nodes.card-w)*hsparse.cost C+
         (e+1)*(a-w)*zDegree C:=by
   intro C
   have hsub:=componentSeeds_subset Ω G T H Γ
     (selectedPoint φ selected) C
   have hgmem:=regularComponent_G_mem Ω G T H C
   have hFmem:surfaceMap φ F∈C.1:=
     ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
       (Ideal.mem_span_singleton.mpr hdiv)
   apply prime_seed_incidence_sharp_of_residual_cost φ C.1 (hproj C)
     (regularComponent_ne_point Ω G T H C) F hFmem
     (regularComponent_H_not_mem Ω G T H C) selected
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C)
     nodes x u₀ u₁ hinj p w a e hw hchar hwa han
     (fun γ hγ↦hdegree γ (hsub hγ))
     (fun γ hγ↦hsolution γ (hsub hγ))
     (fun γ hγ↦hregular γ (hsub hγ))
     (fun γ hγ↦componentSeeds_on_prime Ω G T H Γ
       (selectedPoint φ selected) C γ hγ)
     (fun γ hγ↦hagreement γ (hsub hγ))
     (noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil)
     (hsparse.cost C)
   intro i hi hproper
   exact hsparse.zero_le C _ (hadmissible i hi) hproper
 exact aggregate_component_residual_incidence G T H Γ
   (selectedPoint φ selected) hGpoint hTpoint hHp (a-w)
   (nodes.card-w) (e+1) wholeCost zBudget hsparse.cost zDegree
   hcomponent hsparse.sum_cost_le hzbudget
end
end ProximityPrize.SubmissionLower.RCN272
end PackedLegacy_AE

/-! Packed from ProximityPrize.SubmissionLower.BR. -/
section PackedLegacy_BR
namespace ProximityPrize.SubmissionLower.RCN165
open scoped Classical
open RCN095 RCN094 RCN162 RCN272
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
theorem originalAlgHom_eq_residualAlgHom
   (aY v bY aS bS cS:K):
   originalAlgHom aY v bY aS bS cS=
     residualAlgHom
       (-v⁻¹*aY) v⁻¹ (-v⁻¹*bY)
       (-v⁻¹*aS+v⁻¹*bS*v⁻¹*aY)
       (-v⁻¹*bS*v⁻¹)
       (v⁻¹*bS*v⁻¹*bY-v⁻¹*cS):=by
 apply MvPolynomial.algHom_ext
 intro i
 fin_cases i <;>
   simp [originalAlgHom,residualAlgHom,originalImage,residualImage] <;>
   ring
theorem polynomialInFlag_originalAlgHom
   (r:FlagDegree) (A:Poly3 K) (aY v bY aS bS cS:K)
   (hA:PolynomialInFlag r A):
   PolynomialInFlag r (originalAlgHom aY v bY aS bS cS A):=by
 rw [originalAlgHom_eq_residualAlgHom]
 exact RCN094.polynomialInFlag_residualAlgHom
   r A _ _ _ _ _ _ hA
@[simp] theorem residual_original_apply
   (aY v bY aS bS cS:K) (hv:v≠0) (A:Poly3 K):
   residualAlgHom aY v bY aS bS cS
       (originalAlgHom aY v bY aS bS cS A)=A:=by
 have h:=AlgHom.congr_fun
   (residual_comp_original aY v bY aS bS cS hv) A
 simpa only [AlgHom.comp_apply,AlgHom.id_apply] using h
theorem forwardResidualPoint_injective
   (aY v bY aS bS cS:K) (hv:v≠0):
   Function.Injective (forwardResidualPoint aY v bY aS bS cS):=by
 intro q r hqr
 have h0:=congrFun hqr 0
 have h1:=congrFun hqr 1
 have h2:=congrFun hqr 2
 simp only [forwardResidualPoint,Matrix.cons_val_zero,
   Matrix.cons_val_one,Matrix.cons_val_two] at h0 h1 h2
 change q 2=r 2 at h2
 have hy:q 0=r 0:=by
   apply (mul_left_cancel₀ hv)
   rw [h2] at h0
   linear_combination h0
 have hs:q 1=r 1:=by
   apply (mul_left_cancel₀ hv)
   rw [hy,h2] at h1
   linear_combination h1
 funext i
 fin_cases i
 · exact hy
 · exact hs
 · exact h2
theorem finiteZeroSetBound_map_residual
   (aY v bY aS bS cS:K) (hv:v≠0)
   (P:Ideal (Poly3 K)) (A:Poly3 K) (cost:ℕ)
   (hzero:FiniteZeroSetBound P A cost):
   FiniteZeroSetBound
     (P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom)
     (residualAlgHom aY v bY aS bS cS A) cost:=by
 classical
 intro points hpointsP hpointsA
 let forward:=forwardResidualPoint aY v bY aS bS cS
 let oldPoints:=points.image forward
 have hcard:oldPoints.card=points.card:=by
   exact Finset.card_image_of_injective points
     (forwardResidualPoint_injective aY v bY aS bS cS hv)
 rw [←hcard]
 apply hzero oldPoints
 · intro qOld hqOld
   obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hqOld
   exact (map_le_pointKernel_iff aY v bY aS bS cS hv P q).mp
     (hpointsP q hq)
 · intro qOld hqOld
   obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hqOld
   have hz:=hpointsA q hq
   change MvPolynomial.eval q
     (residualAlgHom aY v bY aS bS cS A)=0 at hz
   change MvPolynomial.eval
     (forwardResidualPoint aY v bY aS bS cS q) A=0
   change MvPolynomial.eval q
     (residualEquiv aY v bY aS bS cS hv A)=0 at hz
   rwa [eval_residualEquiv] at hz
theorem finiteZeroSetBound_map_residual_of_inverse
   (aY v bY aS bS cS:K) (hv:v≠0)
   (P:Ideal (Poly3 K)) (A:Poly3 K) (cost:ℕ)
   (hzero:FiniteZeroSetBound P
     (originalAlgHom aY v bY aS bS cS A) cost):
   FiniteZeroSetBound
     (P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom)
     A cost:=by
 have h:=finiteZeroSetBound_map_residual aY v bY aS bS cS hv P
   (originalAlgHom aY v bY aS bS cS A) cost hzero
 change FiniteZeroSetBound
   (P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom)
   (residualAlgHom aY v bY aS bS cS
     (originalAlgHom aY v bY aS bS cS A)) cost at h
 rw [residual_original_apply aY v bY aS bS cS hv] at h
 exact h
structure PrimeFlagZeroBudget
   (P:Ideal (Poly3 K)) (cost:FlagDegree → ℕ) where
 zero_le:∀ (r:FlagDegree) (A:Poly3 K),
   PolynomialInFlag r A → A∉P → FiniteZeroSetBound P A (cost r)
def PrimeFlagZeroBudget.mapResidual
   {P:Ideal (Poly3 K)} {cost:FlagDegree → ℕ}
   (B:PrimeFlagZeroBudget P cost)
   (aY v bY aS bS cS:K) (hv:v≠0):
   PrimeFlagZeroBudget
     (P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom)
     cost where
 zero_le:=by
   intro r A hA hproper
   have hAold:PolynomialInFlag r
       (originalAlgHom aY v bY aS bS cS A):=
     polynomialInFlag_originalAlgHom r A aY v bY aS bS cS hA
   have hproperOld:originalAlgHom aY v bY aS bS cS A∉P:=by
     intro hmem
     apply hproper
     have hmapped:=Ideal.mem_map_of_mem
       (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom hmem
     change residualAlgHom aY v bY aS bS cS
       (originalAlgHom aY v bY aS bS cS A)∈
         P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom
       at hmapped
     rwa [residual_original_apply aY v bY aS bS cS hv] at hmapped
   exact finiteZeroSetBound_map_residual_of_inverse
     aY v bY aS bS cS hv P A (cost r)
     (B.zero_le r _ hAold hproperOld)
end
end ProximityPrize.SubmissionLower.RCN165
end PackedLegacy_BR

/-! Packed from ProximityPrize.SubmissionLower.BE. -/
section PackedLegacy_BE
namespace ProximityPrize.SubmissionLower.RCN123
open scoped Classical
open RCN095 RCN125 RCN371 RCN011
 RCN009 RCN012
noncomputable section
variable {K:Type} [Field K]
abbrev Poly3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
structure FlagTrapezoidCaps (p:FlagDegree) (F:Poly3 K):Prop where
 uOuter:(planeMap K uOrder F).natDegree ≤ p.all
 uTotal:∀ d∈(rationalMap K uOrder F).support,
   d 0+d 1 ≤ p.zOnly+p.yz+p.all
 vOuter:(planeMap K vOrder F).natDegree ≤ p.yz+p.all
 vTotal:∀ d∈(rationalMap K vOrder F).support,
   d 0+d 1 ≤ p.zOnly+p.yz+p.all
 zOuter:(planeMap K zOrder F).natDegree ≤ p.all
 zTotal:∀ d∈(rationalMap K zOrder F).support,
   d 0+d 1 ≤ p.yz+p.all
private theorem degreeOf_s_le
   {p:FlagDegree} {F:Poly3 K}
   (hF:RCN125.PolynomialInFlag p F):
   F.degreeOf 1 ≤ p.all:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 exact (hF d hd).1
private theorem degreeOf_y_le
   {p:FlagDegree} {F:Poly3 K}
   (hF:RCN125.PolynomialInFlag p F):
   F.degreeOf 0 ≤ p.yz+p.all:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 exact (Nat.le_add_right (d 0) (d 1)).trans (hF d hd).2.1
theorem flagTrapezoidCaps_of_inFlag
   (p:FlagDegree) (F:Poly3 K)
   (hF:RCN125.PolynomialInFlag p F):
   FlagTrapezoidCaps p F:=by
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 · exact (planeMap_natDegree_le K uOrder F).trans
     (by simpa [uOrder] using degreeOf_s_le hF)
 · apply rationalMap_joint_support_of_original K uOrder F _
   intro d hd
   have h:=(hF d hd).2.2
   have h':d 1+d 2 ≤ p.zOnly+p.yz+p.all:=by omega
   simpa [uOrder] using h'
 · exact (planeMap_natDegree_le K vOrder F).trans
     (by simpa [vOrder,Equiv.swap_apply_def] using degreeOf_y_le hF)
 · apply rationalMap_joint_support_of_original K vOrder F _
   intro d hd
   have h:=(hF d hd).2.2
   have h':d 0+d 2 ≤ p.zOnly+p.yz+p.all:=by omega
   simpa [vOrder,Equiv.swap_apply_def] using h'
 · exact (planeMap_natDegree_le K zOrder F).trans
     (by simpa [zOrder,Equiv.swap_apply_def] using degreeOf_s_le hF)
 · apply rationalMap_joint_support_of_original K zOrder F _
   intro d hd
   have h:=(hF d hd).2.1
   simpa [zOrder,Equiv.swap_apply_def,Nat.add_comm] using h
theorem flagTrapezoidCaps_flagAlgHom
   (p:FlagDegree) (F:Poly3 K) (lam mu nu:K)
   (hF:F.support ⊆ flagSupport p):
   FlagTrapezoidCaps p (flagAlgHom lam mu nu F):=by
 apply flagTrapezoidCaps_of_inFlag
 apply polynomialInFlag_flagAlgHom p F lam mu nu
 intro d hd
 exact (mem_flagSupport_iff p d).mp (hF hd)
theorem u_trapezoid_budget6543 (m:ℕ) (hm:m ≤ 1179639):
   m*376+5*98434322-m*5 ≤ flagYZMixedCap:=by
 rw [flag_mixed_values.2.2.1]
 omega
theorem v_trapezoid_budget6543 (m:ℕ) (hm:m ≤ 6684622):
   m*376+26*98434322-m*26 ≤ flagAllMixedCap:=by
 rw [flag_mixed_values.2.2.2]
 omega
theorem z_trapezoid_budget6543 (m:ℕ) (hm:m ≤ 1179639):
   m*26+5*6684622-m*5 ≤ flagZMixedCap:=by
 rw [flag_mixed_values.2.1]
 omega
end
end ProximityPrize.SubmissionLower.RCN123
end PackedLegacy_BE

/-! Packed from ProximityPrize.SubmissionLower.Z2. -/
section PackedLegacy_Z2
namespace ProximityPrize.SubmissionLower.RCN121
open RCN095
theorem flagMixed_projection_decomposition
   (p q r:FlagDegree):
   flagMixed p q r=
     r.zOnly*flagMixed p q unitZFlag+
     r.yz*flagMixed p q unitYZFlag+
     r.all*flagMixed p q unitAllFlag:=by
 cases p
 cases q
 cases r
 simp [flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
 ring
theorem trapezoid_budget_mono
   (n mCap totalG totalT m:ℕ)
   (hn:n ≤ totalG) (hm:m ≤ mCap):
   m*totalG+n*totalT-m*n ≤
     mCap*totalG+n*totalT-mCap*n:=by
 let delta:=totalG-n
 have hsplit:totalG=n+delta:=by
   dsimp only [delta]
   omega
 have hdecomp (a:ℕ):
     a*totalG=a*n+a*delta:=by
   rw [hsplit,Nat.mul_add]
 have hdelta:m*delta ≤ mCap*delta:=
   Nat.mul_le_mul_right delta hm
 rw [hdecomp m,hdecomp mCap]
 omega
theorem u_flag_trapezoid_budget
   (p q:FlagDegree) (m:ℕ) (hm:m ≤ q.all):
   m*(p.zOnly+p.yz+p.all)+
         p.all*(q.zOnly+q.yz+q.all)-m*p.all ≤
     flagMixed p q unitYZFlag:=by
 calc
   m*(p.zOnly+p.yz+p.all)+
         p.all*(q.zOnly+q.yz+q.all)-m*p.all ≤
       q.all*(p.zOnly+p.yz+p.all)+
         p.all*(q.zOnly+q.yz+q.all)-q.all*p.all:=
     trapezoid_budget_mono p.all q.all
       (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all) m
       (by omega) hm
   _=flagMixed p q unitYZFlag:=by
     have hsum:
         q.all*(p.zOnly+p.yz+p.all)+
             p.all*(q.zOnly+q.yz+q.all)=
           q.all*p.all+flagMixed p q unitYZFlag:=by
       simp [flagMixed,unitYZFlag]
       ring
     rw [hsum,Nat.add_sub_cancel_left]
theorem v_flag_trapezoid_budget
   (p q:FlagDegree) (m:ℕ) (hm:m ≤ q.yz+q.all):
   m*(p.zOnly+p.yz+p.all)+
         (p.yz+p.all)*(q.zOnly+q.yz+q.all)-
           m*(p.yz+p.all) ≤
     flagMixed p q unitAllFlag:=by
 calc
   m*(p.zOnly+p.yz+p.all)+
         (p.yz+p.all)*(q.zOnly+q.yz+q.all)-
           m*(p.yz+p.all) ≤
       (q.yz+q.all)*(p.zOnly+p.yz+p.all)+
         (p.yz+p.all)*(q.zOnly+q.yz+q.all)-
           (q.yz+q.all)*(p.yz+p.all):=
     trapezoid_budget_mono (p.yz+p.all) (q.yz+q.all)
       (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all) m
       (by omega) hm
   _=flagMixed p q unitAllFlag:=by
     have hsum:
         (q.yz+q.all)*(p.zOnly+p.yz+p.all)+
             (p.yz+p.all)*(q.zOnly+q.yz+q.all)=
           (q.yz+q.all)*(p.yz+p.all)+
             flagMixed p q unitAllFlag:=by
       simp [flagMixed,unitAllFlag]
       ring
     rw [hsum,Nat.add_sub_cancel_left]
theorem z_flag_trapezoid_budget
   (p q:FlagDegree) (m:ℕ) (hm:m ≤ q.all):
   m*(p.yz+p.all)+p.all*(q.yz+q.all)-m*p.all ≤
     flagMixed p q unitZFlag:=by
 calc
   m*(p.yz+p.all)+p.all*(q.yz+q.all)-m*p.all ≤
       q.all*(p.yz+p.all)+p.all*(q.yz+q.all)-
         q.all*p.all:=
     trapezoid_budget_mono p.all q.all (p.yz+p.all)
       (q.yz+q.all) m (by omega) hm
   _=flagMixed p q unitZFlag:=by
     have hsum:
         q.all*(p.yz+p.all)+p.all*(q.yz+q.all)=
           q.all*p.all+flagMixed p q unitZFlag:=by
       simp [flagMixed,unitZFlag]
       ring
     rw [hsum,Nat.add_sub_cancel_left]
end ProximityPrize.SubmissionLower.RCN121
end PackedLegacy_Z2

/-! Packed from ProximityPrize.SubmissionLower.I. -/
section PackedLegacy_I
namespace ProximityPrize.SubmissionLower.RCN237
open scoped Classical BigOperators
open RCN264 RCN095 RCN121 RCN165 RCN156 RCN213 RCN215 RCN275
noncomputable section
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
structure PrimeFlagBudgetFamily (p q:FlagDegree) where
 zCost:RegularComponent Omega G T H → ℕ
 yzCost:RegularComponent Omega G T H → ℕ
 allCost:RegularComponent Omega G T H → ℕ
 primeBudget:∀ C:RegularComponent Omega G T H,
   PrimeFlagZeroBudget C.1 (fun r↦
     r.zOnly*zCost C+r.yz*yzCost C+r.all*allCost C)
 sum_zCost_le:(∑ C:RegularComponent Omega G T H,zCost C) ≤
   flagMixed p q unitZFlag
 sum_yzCost_le:(∑ C:RegularComponent Omega G T H,yzCost C) ≤
   flagMixed p q unitYZFlag
 sum_allCost_le:(∑ C:RegularComponent Omega G T H,allCost C) ≤
   flagMixed p q unitAllFlag
def PrimeFlagBudgetFamily.weightedCost
   {p q:FlagDegree} (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q)
   (r:FlagDegree) (C:RegularComponent Omega G T H):ℕ:=
 r.zOnly*B.zCost C+r.yz*B.yzCost C+r.all*B.allCost C
theorem PrimeFlagBudgetFamily.sum_weightedCost_le
   {p q:FlagDegree} (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q)
   (r:FlagDegree):
   (∑ C:RegularComponent Omega G T H,B.weightedCost r C) ≤
     flagMixed p q r:=by
 calc
   (∑ C:RegularComponent Omega G T H,B.weightedCost r C)=
       r.zOnly*(∑ C:RegularComponent Omega G T H,B.zCost C)+
       r.yz*(∑ C:RegularComponent Omega G T H,B.yzCost C)+
       r.all*(∑ C:RegularComponent Omega G T H,B.allCost C):=by
     simp only [PrimeFlagBudgetFamily.weightedCost,
       Finset.sum_add_distrib,Finset.mul_sum]
   _ ≤ r.zOnly*flagMixed p q unitZFlag+
       r.yz*flagMixed p q unitYZFlag+
       r.all*flagMixed p q unitAllFlag:=
     Nat.add_le_add
       (Nat.add_le_add
         (Nat.mul_le_mul_left r.zOnly B.sum_zCost_le)
         (Nat.mul_le_mul_left r.yz B.sum_yzCost_le))
       (Nat.mul_le_mul_left r.all B.sum_allCost_le)
   _=flagMixed p q r:=(flagMixed_projection_decomposition p q r).symm
theorem PrimeFlagBudgetFamily.weightedCost_residualAgreementFlag
   {p q:FlagDegree} (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q)
   (C:RegularComponent Omega G T H) (d:ℕ):
   B.weightedCost (residualAgreementFlag d) C=
     d*B.weightedCost agreementDirection6600 C+
       B.weightedCost unitYZFlag C:=by
 rw [residualAgreementFlag_eq_affine]
 simp only [PrimeFlagBudgetFamily.weightedCost,add_zOnly,add_yz,add_all,
   nsmul_zOnly,nsmul_yz,nsmul_all]
 ring
theorem PrimeFlagBudgetFamily.weightedCost_supportResidualAgreementFlag
   {p q:FlagDegree} (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q)
   (support:ResidualSupportParameters)
   (C:RegularComponent Omega G T H) (d:ℕ):
   B.weightedCost (support.residualAgreementFlag d) C=
     d*B.weightedCost support.agreementDirection C+
       B.weightedCost unitYZFlag C:=by
 simp only [ResidualSupportParameters.residualAgreementFlag,
   ResidualSupportParameters.agreementDirection,
   PrimeFlagBudgetFamily.weightedCost,unitYZFlag]
 ring
theorem flagMixed_supportResidualAgreement_direction
   (p:FlagDegree) (support:ResidualSupportParameters) (d:ℕ):
   flagMixed p (support.residualAgreementFlag d) support.agreementDirection=
     d*flagMixed p support.agreementDirection support.agreementDirection+
       flagMixed p support.agreementDirection unitYZFlag:=by
 simp [flagMixed,ResidualSupportParameters.residualAgreementFlag,
   ResidualSupportParameters.agreementDirection,unitYZFlag]
 ring
theorem flagMixed_supportResidualAgreement_unit
   (p:FlagDegree) (support:ResidualSupportParameters) (d:ℕ):
   flagMixed p (support.residualAgreementFlag d) unitYZFlag=
     d*flagMixed p support.agreementDirection unitYZFlag+
       flagMixed p unitYZFlag unitYZFlag:=by
 simp [flagMixed,ResidualSupportParameters.residualAgreementFlag,
   ResidualSupportParameters.agreementDirection,unitYZFlag]
 ring
theorem flagMixed_supportResidualAgreement_z
   (p:FlagDegree) (support:ResidualSupportParameters) (d:ℕ):
   flagMixed p (support.residualAgreementFlag d) unitZFlag=
     d*flagMixed p support.agreementDirection unitZFlag+
       flagMixed p unitYZFlag unitZFlag:=by
 simp [flagMixed,ResidualSupportParameters.residualAgreementFlag,
   ResidualSupportParameters.agreementDirection,unitYZFlag,unitZFlag]
 ring
theorem flagMixed_supportResidualAgreement_all
   (p:FlagDegree) (support:ResidualSupportParameters) (d:ℕ):
   flagMixed p (support.residualAgreementFlag d) unitAllFlag=
     d*flagMixed p support.agreementDirection unitAllFlag+
       flagMixed p unitYZFlag unitAllFlag:=by
 simp [flagMixed,ResidualSupportParameters.residualAgreementFlag,
   ResidualSupportParameters.agreementDirection,unitYZFlag,unitAllFlag]
 ring
theorem flagMixed_residualAgreement_direction
   (p:FlagDegree) (d:ℕ):
   flagMixed p (residualAgreementFlag d) agreementDirection6600=
     d*flagMixed p agreementDirection6600 agreementDirection6600+
       flagMixed p agreementDirection6600 unitYZFlag:=by
 rw [residualAgreementFlag_eq_affine]
 simp [flagMixed,unitYZFlag,agreementDirection6600]
 ring
theorem flagMixed_residualAgreement_unit
   (p:FlagDegree) (d:ℕ):
   flagMixed p (residualAgreementFlag d) unitYZFlag=
     d*flagMixed p agreementDirection6600 unitYZFlag+
       flagMixed p unitYZFlag unitYZFlag:=by
 rw [residualAgreementFlag_eq_affine]
 simp [flagMixed,unitYZFlag,agreementDirection6600]
 ring
theorem flagMixed_residualAgreement_z
   (p:FlagDegree) (d:ℕ):
   flagMixed p (residualAgreementFlag d) unitZFlag=
     d*flagMixed p agreementDirection6600 unitZFlag+
       flagMixed p unitYZFlag unitZFlag:=by
 rw [residualAgreementFlag_eq_affine]
 simp [flagMixed,unitYZFlag,unitZFlag,agreementDirection6600]
 ring
theorem flagMixed_residualAgreement_all
   (p:FlagDegree) (d:ℕ):
   flagMixed p (residualAgreementFlag d) unitAllFlag=
     d*flagMixed p agreementDirection6600 unitAllFlag+
       flagMixed p unitYZFlag unitAllFlag:=by
 rw [residualAgreementFlag_eq_affine]
 simp [flagMixed,unitYZFlag,unitAllFlag,agreementDirection6600]
 ring
end
end ProximityPrize.SubmissionLower.RCN237
end PackedLegacy_I

/-! Packed from ProximityPrize.SubmissionLower.B1. -/
section PackedLegacy_B1
namespace ProximityPrize.SubmissionLower.RCN066
open scoped Classical BigOperators
open RCN072 RCN264 RCN095 RCN272 RCN165 RCN237
noncomputable section
variable {K:Type} [Field K]
abbrev Poly3:=MvPolynomial (Fin 3) K
theorem mem_iff_of_sub_mem (P:Ideal (Poly3 (K:=K)))
   {A B:Poly3 (K:=K)} (h:A - B ∈ P):A ∈ P ↔ B ∈ P:=by
 constructor
 · intro hA
   simpa only [sub_sub_cancel] using P.sub_mem hA h
 · intro hB
   simpa only [sub_add_cancel] using P.add_mem h hB
theorem sub_mem_of_dvd (P:Ideal (Poly3 (K:=K)))
   {G A B:Poly3 (K:=K)} (hG:G ∈ P) (h:G ∣ A - B) :
   A - B ∈ P:=by
 obtain ⟨Q,hQ⟩:=h
 rw [hQ]
 exact P.mul_mem_right Q hG
theorem cutIdeal_eq_of_dvd_sub {G T T':Poly3 (K:=K)}
   (h:G ∣ T - T'):cutIdeal K G T = cutIdeal K G T':=by
 have hG:G ∈ cutIdeal K G T:=Ideal.subset_span (by simp)
 have hG':G ∈ cutIdeal K G T':=Ideal.subset_span (by simp)
 have hT:T ∈ cutIdeal K G T:=Ideal.subset_span (by simp)
 have hT':T' ∈ cutIdeal K G T':=Ideal.subset_span (by simp)
 have hd:=sub_mem_of_dvd (cutIdeal K G T) hG h
 have hd':=sub_mem_of_dvd (cutIdeal K G T') hG' h
 apply le_antisymm
 · apply Ideal.span_le.mpr
   intro A hA
   simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
   rcases hA with rfl | rfl
   · exact hG'
   · exact (mem_iff_of_sub_mem _ hd').mpr hT'
 · apply Ideal.span_le.mpr
   intro A hA
   simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA
   rcases hA with rfl | rfl
   · exact hG
   · exact (mem_iff_of_sub_mem _ hd).mp hT
theorem regularComponents_eq_of_dvd_sub {G T T' H:Poly3 (K:=K)}
   (h:G ∣ T - T') :
   regularComponents K G T H = regularComponents K G T' H:=by
 classical
 ext P
 simp only [regularComponents,Finset.mem_filter,mem_componentFamily,
   cutIdeal_eq_of_dvd_sub h]
def regularComponentEquiv {G T T' H:Poly3 (K:=K)}
   (h:G ∣ T - T') :
   RegularComponent K G T H ≃ RegularComponent K G T' H where
 toFun C:=⟨C.1,(regularComponents_eq_of_dvd_sub h) ▸ C.2⟩
 invFun C:=⟨C.1,(regularComponents_eq_of_dvd_sub h).symm ▸ C.2⟩
 left_inv C:=by rfl
 right_inv C:=by rfl
@[simp] theorem regularComponentEquiv_val {G T T' H:Poly3 (K:=K)}
   (h:G ∣ T - T') (C:RegularComponent K G T H) :
   (regularComponentEquiv h C).1 = C.1:=rfl
@[simp] theorem regularComponentEquiv_symm_val {G T T' H:Poly3 (K:=K)}
   (h:G ∣ T - T') (C:RegularComponent K G T' H) :
   ((regularComponentEquiv h).symm C).1 = C.1:=rfl
theorem eval_eq_of_sub_mem (P:Ideal (Poly3 (K:=K)))
   {A B:Poly3 (K:=K)} (h:A - B ∈ P) (v:Fin 3 → K)
   (hv:P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom) :
   MvPolynomial.aeval v A = MvPolynomial.aeval v B:=by
 have hz:=hv h
 change MvPolynomial.aeval v (A - B) = 0 at hz
 rw [map_sub] at hz
 exact sub_eq_zero.mp hz
theorem finiteZeroSetBound_of_sub_mem (P:Ideal (Poly3 (K:=K)))
   {A B:Poly3 (K:=K)} {cost:ℕ}
   (h:A - B ∈ P) (hB:FiniteZeroSetBound P B cost) :
   FiniteZeroSetBound P A cost:=by
 intro points hpointsP hpointsA
 apply hB points hpointsP
 intro v hv
 rw [← eval_eq_of_sub_mem P h v (hpointsP v hv)]
 exact hpointsA v hv
def PolynomialInFlagMod (P:Ideal (Poly3 (K:=K)))
   (r:FlagDegree) (A:Poly3 (K:=K)):Prop :=
 ∃ B,PolynomialInFlag r B ∧ A - B ∈ P
theorem PolynomialInFlagMod.mono {P Q:Ideal (Poly3 (K:=K))}
   {r:FlagDegree} {A:Poly3 (K:=K)} (hPQ:P ≤ Q)
   (h:PolynomialInFlagMod P r A):PolynomialInFlagMod Q r A:=by
 obtain ⟨B,hB,hAB⟩:=h
 exact ⟨B,hB,hPQ hAB⟩
theorem PolynomialInFlagMod.of_surface_mem
   {P:Ideal (Poly3 (K:=K))} {G A:Poly3 (K:=K)}
   {r:FlagDegree} (hG:G ∈ P)
   (h:PolynomialInFlagMod (Ideal.span {G}) r A) :
   PolynomialInFlagMod P r A:=by
 apply PolynomialInFlagMod.mono (P:=Ideal.span {G}) (Q:=P) _ h
 apply Ideal.span_le.mpr
 intro B hB
 change B ∈ P
 rcases Set.mem_singleton_iff.mp hB with rfl
 exact hG
theorem PrimeFlagZeroBudget.zero_le_congr
   {P:Ideal (Poly3 (K:=K))} {cost:FlagDegree → ℕ}
   (B:PrimeFlagZeroBudget P cost) (r:FlagDegree)
   (A:Poly3 (K:=K)) (hA:PolynomialInFlagMod P r A)
   (hproper:A ∉ P):FiniteZeroSetBound P A (cost r):=by
 obtain ⟨A',hflag,hcongr⟩:=hA
 have hproper':A' ∉ P:=by
   intro hmem
   exact hproper ((mem_iff_of_sub_mem P hcongr).mpr hmem)
 exact finiteZeroSetBound_of_sub_mem P hcongr (B.zero_le r A' hflag hproper')
def PrimeFlagBudgetFamily.ofCongruentCut
   {G T T' H:Poly3 (K:=K)} {p q:FlagDegree}
   (h:G ∣ T - T')
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T') (H:=H) p q) :
   PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q where
 zCost C:=B.zCost (regularComponentEquiv h C)
 yzCost C:=B.yzCost (regularComponentEquiv h C)
 allCost C:=B.allCost (regularComponentEquiv h C)
 primeBudget C:=B.primeBudget (regularComponentEquiv h C)
 sum_zCost_le:=by
   simpa only [(regularComponentEquiv h).sum_comp B.zCost] using B.sum_zCost_le
 sum_yzCost_le:=by
   simpa only [(regularComponentEquiv h).sum_comp B.yzCost] using B.sum_yzCost_le
 sum_allCost_le:=by
   simpa only [(regularComponentEquiv h).sum_comp B.allCost] using B.sum_allCost_le
theorem PrimeFlagBudgetFamily.ofCongruentCut_positive
   {G T T' H:Poly3 (K:=K)} {p q:FlagDegree}
   (h:G ∣ T - T')
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T') (H:=H) p q)
   (hpos:∀ C,1 ≤ B.zCost C + B.yzCost C) :
   ∀ C,1 ≤ (PrimeFlagBudgetFamily.ofCongruentCut h B).zCost C +
     (PrimeFlagBudgetFamily.ofCongruentCut h B).yzCost C:=by
 intro C
 exact hpos (regularComponentEquiv h C)
theorem PrimeFlagBudgetFamily.ofCongruentCut_z_positive
   {G T T' H:Poly3 (K:=K)} {p q:FlagDegree}
   (h:G ∣ T - T')
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T') (H:=H) p q)
   (i:Fin 3)
   (hpos:∀ C,Transcendental K
     (RCN002.coordinate K C.1 i) → 1 ≤ B.zCost C) :
   ∀ C,Transcendental K
     (RCN002.coordinate K C.1 i) →
     1 ≤ (PrimeFlagBudgetFamily.ofCongruentCut h B).zCost C:=by
 intro C htr
 exact hpos (regularComponentEquiv h C) htr
theorem PrimeFlagBudgetFamily.ofCongruentCut_yz_positive
   {G T T' H:Poly3 (K:=K)} {p q:FlagDegree}
   (h:G ∣ T - T')
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T') (H:=H) p q)
   (i:Fin 3)
   (hpos:∀ C,¬ Transcendental K
     (RCN002.coordinate K C.1 i) → 1 ≤ B.yzCost C) :
   ∀ C,¬ Transcendental K
     (RCN002.coordinate K C.1 i) →
     1 ≤ (PrimeFlagBudgetFamily.ofCongruentCut h B).yzCost C:=by
 intro C htr
 exact hpos (regularComponentEquiv h C) htr
end
end ProximityPrize.SubmissionLower.RCN066
end PackedLegacy_B1

/-! Packed from ProximityPrize.SubmissionLower.E5. -/
section PackedLegacy_E5
namespace ProximityPrize.SubmissionLower.RCN263
open RCN136 RCN231 RCN313 RCN238 RCN156 RCN234 RCN095 RCN275 RCN262 RCN066
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
def reducedAgreementDirection (P:ResidualSupportParameters):FlagDegree :=
 ⟨2 * (P.total - P.ys),2 * (P.ys - P.s),2 * P.s - 2⟩
def reducedResidualAgreementFlag
   (P:ResidualSupportParameters) (d:ℕ):FlagDegree :=
 ⟨(reducedAgreementDirection P).zOnly * d,
   1 + (reducedAgreementDirection P).yz * d,
   (reducedAgreementDirection P).all * d⟩
theorem reducedResidualAgreementFlag_ys
   (P:ResidualSupportParameters) (d:ℕ) :
   (reducedResidualAgreementFlag P d).yz +
       (reducedResidualAgreementFlag P d).all =
     1 + d * (2 * P.ys - 2):=by
 have hs:=P.s_le_ys
 have h1:=P.one_le_s
 have hcoeff :
     2 * (P.ys - P.s) + (2 * P.s - 2) = 2 * P.ys - 2:=by
   rw [Nat.mul_sub_left_distrib]
   omega
 simp only [reducedResidualAgreementFlag,reducedAgreementDirection]
 rw [← hcoeff]
 ring
theorem reducedResidualAgreementFlag_total
   (P:ResidualSupportParameters) (d:ℕ) :
   (reducedResidualAgreementFlag P d).zOnly +
       (reducedResidualAgreementFlag P d).yz +
       (reducedResidualAgreementFlag P d).all =
     1 + d * (2 * P.total - 2):=by
 have hs:=P.s_le_ys
 have ht:=P.ys_le_total
 have h1:=P.one_le_s
 have hcoeff:2 * (P.total - P.ys) + 2 * (P.ys - P.s) +
     (2 * P.s - 2) = 2 * P.total - 2:=by
   rw [Nat.mul_sub_left_distrib,Nat.mul_sub_left_distrib]
   omega
 simp only [reducedResidualAgreementFlag,reducedAgreementDirection]
 rw [← hcoeff]
 ring
def reducedAgreementPolynomial (phi:Polynomial K →+* Omega)
   (P:ResidualSupportParameters) (F:MvPolynomial (Fin 4) K)
   (d:ℕ) (x u0 u1:K):MvPolynomial (Fin 3) Omega :=
 surfaceMap phi (reducedAgreementNumerator F P.s d
   (fun j ↦ (j.factorial:K)⁻¹) x u0 u1)
theorem agreementPolynomial_sub_reduced_dvd
   (phi:Polynomial K →+* Omega) (P:ResidualSupportParameters)
   (F:MvPolynomial (Fin 4) K) (d:ℕ) (x u0 u1:K) :
   surfaceMap phi F ∣ agreementPolynomial phi F d x u0 u1 -
     reducedAgreementPolynomial phi P F d x u0 u1:=by
 change surfaceMap phi F ∣
   surfaceMap phi (agreementNumerator F d
     (fun j ↦ (j.factorial:K)⁻¹) x u0 u1) -
   surfaceMap phi (reducedAgreementNumerator F P.s d
     (fun j ↦ (j.factorial:K)⁻¹) x u0 u1)
 rw [← map_sub]
 exact map_dvd (surfaceMap phi)
   (agreementNumerator_sub_reduced_dvd F P.s d
     (fun j ↦ (j.factorial:K)⁻¹) x u0 u1)
theorem surfaceMap_reducedAgreement_in_flag
   (phi:Polynomial K →+* Omega) (P:ResidualSupportParameters)
   {F:MvPolynomial (Fin 4) K} (H:ResidualSupportData P F)
   (d:ℕ) (coeffs:ℕ → K) (x u0 u1:K) :
   PolynomialInFlag (reducedResidualAgreementFlag P d)
     (surfaceMap phi
       (reducedAgreementNumerator F P.s d coeffs x u0 u1)):=by
 have hR:=reducedAgreementNumerator_R_degree_bound F P.s P.one_le_s
   H.coordinate_bounds.2.1 d coeffs x u0 u1
 have hYS:=reducedAgreementNumerator_wt_le residualYSWeights rfl rfl rfl
   F P.s P.ys P.one_le_s P.two_le_ys H.ys_weight d coeffs x u0 u1
 have hTotal:=reducedAgreementNumerator_wt_le residualTotalWeights rfl rfl rfl
   F P.s P.total P.one_le_s (P.two_le_ys.trans P.ys_le_total)
   H.total_weight d coeffs x u0 u1
 rw [show residualYSWeights 3 = 0 from rfl] at hYS
 rw [show residualTotalWeights 3 = 1 from rfl] at hTotal
 norm_num at hYS hTotal
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp
   (support_surfaceMap_subset phi
     (reducedAgreementNumerator F P.s d coeffs x u0 u1) he)
 have hqR:=(MvPolynomial.monomial_le_degreeOf (2:Fin 4) hq).trans hR
 have hqYS :=
   (MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hYS
 have hqTotal :=
   (MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hTotal
 rw [RCN081.weight_fin4] at hqYS hqTotal
 change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 0 ≤ _ at hqYS
 change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 1 ≤ _ at hqTotal
 norm_num at hqYS hqTotal
 change q 2 ≤ (reducedResidualAgreementFlag P d).all ∧
   q 1 + q 2 ≤ (reducedResidualAgreementFlag P d).yz +
     (reducedResidualAgreementFlag P d).all ∧
   q 1 + q 2 + q 3 ≤ (reducedResidualAgreementFlag P d).zOnly +
     (reducedResidualAgreementFlag P d).yz +
     (reducedResidualAgreementFlag P d).all
 refine ⟨?_,?_,?_⟩
 · change q 2 ≤ (2 * P.s - 2) * d
   have hs:2 * (P.s - 1) = 2 * P.s - 2:=by omega
   have heq:2 * d * (P.s - 1) = (2 * P.s - 2) * d:=by
     rw [← hs]
     ring
   rw [heq] at hqR
   exact hqR
 · rw [reducedResidualAgreementFlag_ys]
   have hs:2 * (P.ys - 1) = 2 * P.ys - 2:=by omega
   have heq:2 * d * (P.ys - 1) = d * (2 * P.ys - 2):=by
     rw [← hs]
     ring
   rw [heq] at hqYS
   exact hqYS
 · rw [reducedResidualAgreementFlag_total]
   have hs:2 * (P.total - 1) = 2 * P.total - 2:=by
     have:=P.one_le_s.trans (P.s_le_ys.trans P.ys_le_total)
     omega
   have heq:2 * d * (P.total - 1) = d * (2 * P.total - 2):=by
     rw [← hs]
     ring
   rw [heq] at hqTotal
   exact hqTotal
theorem agreement_in_flag_mod_factor
   (phi:Polynomial K →+* Omega) (P:ResidualSupportParameters)
   {F:MvPolynomial (Fin 4) K} (H:ResidualSupportData P F)
   (G:MvPolynomial (Fin 3) Omega) (hG:G ∣ surfaceMap phi F)
   (d:ℕ) (x u0 u1:K) :
   PolynomialInFlagMod (Ideal.span {G}) (reducedResidualAgreementFlag P d)
     (agreementPolynomial phi F d x u0 u1):=by
 refine ⟨reducedAgreementPolynomial phi P F d x u0 u1,
   surfaceMap_reducedAgreement_in_flag phi P H d
     (fun j ↦ (j.factorial:K)⁻¹) x u0 u1,?_⟩
 exact Ideal.mem_span_singleton.mpr
   (hG.trans (agreementPolynomial_sub_reduced_dvd phi P F d x u0 u1))
theorem agreement_in_flag_mod_ideal
   (phi:Polynomial K →+* Omega) (P:ResidualSupportParameters)
   {F:MvPolynomial (Fin 4) K} (H:ResidualSupportData P F)
   (I:Ideal (MvPolynomial (Fin 3) Omega)) (hF:surfaceMap phi F ∈ I)
   (d:ℕ) (x u0 u1:K) :
   PolynomialInFlagMod I (reducedResidualAgreementFlag P d)
     (agreementPolynomial phi F d x u0 u1):=by
 refine ⟨reducedAgreementPolynomial phi P F d x u0 u1,
   surfaceMap_reducedAgreement_in_flag phi P H d
     (fun j ↦ (j.factorial:K)⁻¹) x u0 u1,?_⟩
 exact sub_mem_of_dvd I hF
   (agreementPolynomial_sub_reduced_dvd phi P F d x u0 u1)
end
end ProximityPrize.SubmissionLower.RCN263
end PackedLegacy_E5

/-! Packed from ProximityPrize.SubmissionLower.Y3. -/
section PackedLegacy_Y3
namespace ProximityPrize.SubmissionLower.RCN055
open RCN077 RCN313 RCN347
noncomputable section
section Algebra
variable {K:Type*} [CommRing K]
def horizontalDerivation:Derivation K (Poly4 K) (Poly4 K):=
 MvPolynomial.pderiv (0:Fin 4)+
   (MvPolynomial.X (2:Fin 4):Poly4 K) • MvPolynomial.pderiv (1:Fin 4)
def baseDerivation (F:Poly4 K):Derivation K (Poly4 K) (Poly4 K):=
 polyH K F • horizontalDerivation+polyG K F • MvPolynomial.pderiv (2:Fin 4)
theorem baseDerivation_apply (F P:Poly4 K):
   baseDerivation F P=polyH K F*
     (MvPolynomial.pderiv (0:Fin 4) P+
       MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) P)+
     polyG K F*MvPolynomial.pderiv (2:Fin 4) P:=by
 simp only [baseDerivation,horizontalDerivation,Derivation.add_apply,
   Derivation.smul_apply,smul_eq_mul]
def baseIdeal (F:Poly4 K):Ideal (Poly4 K):=
 Ideal.span {polyH K F,polyG K F}
theorem H_mem_baseIdeal (F:Poly4 K):polyH K F∈baseIdeal F:=
 Ideal.subset_span (by simp)
theorem G_mem_baseIdeal (F:Poly4 K):polyG K F∈baseIdeal F:=
 Ideal.subset_span (by simp)
theorem baseDerivation_mem (F P:Poly4 K):baseDerivation F P∈baseIdeal F:=by
 rw [baseDerivation_apply]
 exact (baseIdeal F).add_mem
   ((baseIdeal F).mul_mem_right _ (H_mem_baseIdeal F))
   ((baseIdeal F).mul_mem_right _ (G_mem_baseIdeal F))
theorem derivation_preserves_ideal_pow {A:Type*} [CommRing A] [Algebra K A]
   (D:Derivation K A A) (I:Ideal A)
   (hI:∀ P∈I,D P∈I) (n:ℕ):∀ P∈I^n,D P∈I^n:=by
 induction n with
 | zero => simp
 | succ n ih =>
   rw [pow_succ]
   intro P hP
   refine Submodule.mul_induction_on hP ?_ ?_
   · intro P hP Q hQ
     rw [leibniz_product]
     exact (I^n*I).add_mem
       (Ideal.mul_mem_mul (ih P hP) hQ) (Ideal.mul_mem_mul hP (hI Q hQ))
   · intro P Q hP hQ
     simpa only [map_add] using (I^n*I).add_mem hP hQ
theorem baseDerivation_preserves_pow (F:Poly4 K) (n:ℕ)
   (P:Poly4 K) (hP:P∈baseIdeal F^n):
   baseDerivation F P∈baseIdeal F^n:=
 derivation_preserves_ideal_pow (baseDerivation F) (baseIdeal F)
   (fun P _ => baseDerivation_mem F P) n P hP
theorem numeratorStep_eq (F P:Poly4 K) (b:ℕ):
   numeratorStep K F b P=polyH K F*baseDerivation F P-
     (2*b:ℕ)*P*baseDerivation F (polyH K F):=by
 simp only [numeratorStep,clearedStep,baseDerivation_apply]
 ring
theorem numerator_one (F:Poly4 K):
   numerator K F 1=MvPolynomial.X (2:Fin 4)*polyH K F^2:=by
 simp [numerator,numeratorStep,clearedStep,MvPolynomial.pderiv_X]
theorem baseDerivation_R (F:Poly4 K):
   baseDerivation F (MvPolynomial.X (2:Fin 4))=polyG K F:=by
 simp [baseDerivation_apply,MvPolynomial.pderiv_X]
theorem numerator_two (F:Poly4 K):
   numerator K F 2=polyH K F^3*polyG K F:=by
 rw [numerator_succ,numerator_one,numeratorStep_eq,leibniz_product,
   baseDerivation_R,Derivation.leibniz_pow]
 simp only [smul_eq_mul,nsmul_eq_mul,Nat.reduceSub,Nat.cast_ofNat]
 ring
def baseNumerator (F:Poly4 K):ℕ → Poly4 K
 | 0 => polyG K F
 | n+1 => polyH K F*baseDerivation F (baseNumerator F n)-
     (2*n+1:ℕ)*baseNumerator F n*baseDerivation F (polyH K F)
theorem numeratorStep_H_cube (F P:Poly4 K) (n:ℕ):
   numeratorStep K F (n+2) (polyH K F^3*P)=
     polyH K F^3*(polyH K F*baseDerivation F P-
       (2*n+1:ℕ)*P*baseDerivation F (polyH K F)):=by
 rw [numeratorStep_eq,leibniz_product,Derivation.leibniz_pow]
 simp only [smul_eq_mul,nsmul_eq_mul,Nat.reduceSub,Nat.cast_add,
   Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
 ring
theorem numerator_eq_H_cube (F:Poly4 K) (n:ℕ):
   numerator K F (n+2)=polyH K F^3*baseNumerator F n:=by
 induction n with
 | zero => exact numerator_two F
 | succ n ih =>
   rw [show n+1+2=(n+2)+1 by omega,numerator_succ,ih,
     numeratorStep_H_cube]
   rfl
theorem baseNumerator_mem_pow (F:Poly4 K) (n:ℕ):
   baseNumerator F n∈baseIdeal F^(n+1):=by
 induction n with
 | zero => simpa only [baseNumerator,Nat.zero_add,pow_one] using G_mem_baseIdeal F
 | succ n ih =>
   rw [baseNumerator,pow_succ]
   apply (baseIdeal F^(n+1)*baseIdeal F).sub_mem
   · simpa only [mul_comm (baseDerivation F (baseNumerator F n))] using
       Ideal.mul_mem_mul (baseDerivation_preserves_pow F (n+1) _ ih)
         (H_mem_baseIdeal F)
   · simpa only [mul_assoc] using
       (baseIdeal F^(n+1)*baseIdeal F).mul_mem_left (2*n+1:ℕ)
         (Ideal.mul_mem_mul ih (baseDerivation_mem F (polyH K F)))
theorem numerator_mem_pow (F:Poly4 K) (b:ℕ) (hb:2 ≤ b):
   numerator K F b∈baseIdeal F^(b+2):=by
 obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le hb
 rw [Nat.add_comm 2 n,numerator_eq_H_cube]
 have h:=Ideal.mul_mem_mul (Ideal.pow_mem_pow (H_mem_baseIdeal F) 3)
   (baseNumerator_mem_pow F n)
 rw [←pow_add] at h
 simpa only [show 3+(n+1)=n+2+2 by omega] using h
end Algebra
section Agreement
variable {K:Type*} [Field K]
theorem commonNumeratorTerm_mem_pow (F:Poly4 K) (d j:ℕ)
   (hd:2 ≤ d) (hj:j ≤ d) (c:ℕ → K) (x:K):
   commonNumeratorTerm F d c x j∈baseIdeal F^(d+2):=by
 unfold commonNumeratorTerm
 apply (baseIdeal F^(d+2)).mul_mem_right
 by_cases hj2:2 ≤ j
 · have h:=Ideal.mul_mem_mul (numerator_mem_pow F j hj2)
     (Ideal.pow_mem_pow (H_mem_baseIdeal F) (2*(d-j)))
   rw [←pow_add] at h
   have h':numerator K F j*polyH K F^(2*(d-j))∈
       baseIdeal F^(d+2):=Ideal.pow_le_pow_right (by omega) h
   simpa only [mul_assoc] using (baseIdeal F^(d+2)).mul_mem_left
     (MvPolynomial.C (c j)) h'
 · have hj01:j=0∨j=1:=by omega
   rcases hj01 with rfl | rfl
   · exact (baseIdeal F^(d+2)).mul_mem_left _
       (Ideal.pow_le_pow_right (by omega)
         (Ideal.pow_mem_pow (H_mem_baseIdeal F) (2*(d-0))))
   · rw [numerator_one]
     have hpow:2+2*(d-1)=2*d:=by omega
     have hmem:polyH K F^(2*d)∈baseIdeal F^(d+2):=
       Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow (H_mem_baseIdeal F) _)
     convert (baseIdeal F^(d+2)).mul_mem_left
       (MvPolynomial.C (c 1)*MvPolynomial.X (2:Fin 4)) hmem using 1
     rw [←hpow,pow_add]
     ring
theorem agreementNumerator_mem_pow (F:Poly4 K) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K):
   agreementNumerator F d c x u₀ u₁∈baseIdeal F^(d+2):=by
 unfold agreementNumerator clearedTaylorNumerator
 apply (baseIdeal F^(d+2)).sub_mem
 · exact (baseIdeal F^(d+2)).sum_mem fun j hj =>
     commonNumeratorTerm_mem_pow F d j hd (by simpa using Finset.mem_range.mp hj) c x
 · exact (baseIdeal F^(d+2)).mul_mem_left _
     (Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow (H_mem_baseIdeal F) (2*d)))
end Agreement
end
end ProximityPrize.SubmissionLower.RCN055
end PackedLegacy_Y3

/-! Packed from ProximityPrize.SubmissionLower.A6. -/
section PackedLegacy_A6
namespace ProximityPrize.SubmissionLower.RCN056
open RCN077 RCN313 RCN347 RCN055
noncomputable section
variable {K:Type*} [CommRing K]
def sameContribution (F:Poly4 K) (n j:ℕ) (P:Poly4 K):Poly4 K:=
 polyH K F*horizontalDerivation P-
   (n+j:ℕ)*P*horizontalDerivation (polyH K F)+
     (j:ℕ)*P*MvPolynomial.pderiv (2:Fin 4) (polyG K F)
def downContribution (F:Poly4 K) (j:ℕ) (P:Poly4 K):Poly4 K:=
 (j:ℕ)*P*horizontalDerivation (polyG K F)
def upContribution (F:Poly4 K) (n j:ℕ) (P:Poly4 K):Poly4 K:=
 polyH K F*MvPolynomial.pderiv (2:Fin 4) P-
   (n+j:ℕ)*P*MvPolynomial.pderiv (2:Fin 4) (polyH K F)
def baseMonomial (F:Poly4 K) (k j:ℕ) (P:Poly4 K):Poly4 K:=
 polyH K F^(k-j)*polyG K F^j*P
def baseStep (F:Poly4 K) (n:ℕ) (P:Poly4 K):Poly4 K:=
 polyH K F*baseDerivation F P-
   (2*n+1:ℕ)*P*baseDerivation F (polyH K F)
theorem baseStep_monomial (F P:Poly4 K) (n j:ℕ) (hj:j ≤ n+1):
   baseStep F n (baseMonomial F (n+1) j P)=
     baseMonomial F (n+2) j (sameContribution F n j P)+
     baseMonomial F (n+2) (j-1) (downContribution F j P)+
     baseMonomial F (n+2) (j+1) (upContribution F n j P):=by
 cases j with
 | zero =>
   have he:n+2-1=n+1:=by omega
   simp only [baseStep,baseMonomial,sameContribution,downContribution,
     upContribution,baseDerivation,Derivation.add_apply,Derivation.smul_apply,
     smul_eq_mul,Nat.sub_zero,Nat.zero_sub,Nat.cast_zero,zero_mul,mul_zero,
     pow_zero,mul_one,Nat.zero_add,he,add_zero,leibniz_product,
     Derivation.leibniz_pow,nsmul_eq_mul,Nat.add_sub_cancel]
   simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,pow_succ]
   ring
 | succ j =>
   by_cases ht:j=n
   · subst j
     simp only [baseStep,baseMonomial,sameContribution,downContribution,
       upContribution,baseDerivation,Derivation.add_apply,Derivation.smul_apply,
       smul_eq_mul,Nat.add_sub_add_left,Nat.add_sub_cancel,Nat.sub_self,
       Nat.reduceSub,Nat.add_sub_cancel_left,pow_zero,one_mul,
       leibniz_product,Derivation.leibniz_pow,nsmul_eq_mul]
     simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,pow_succ]
     ring
   · have hjn:j+1 ≤ n:=by omega
     obtain ⟨u,hu⟩:=Nat.exists_eq_add_of_le hjn
     subst n
     have e₁:j+1+u+1-(j+1)=u+1:=by omega
     have e₂:j+1+u+2-(j+1)=u+2:=by omega
     have e₃:j+1+u+2-j=u+3:=by omega
     have e₄:j+1+u+2-(j+1+1)=u+1:=by omega
     simp only [baseStep,baseMonomial,sameContribution,downContribution,
       upContribution,baseDerivation,Derivation.add_apply,Derivation.smul_apply,
       smul_eq_mul,Nat.add_sub_cancel,e₁,e₂,e₃,e₄,
       leibniz_product,Derivation.leibniz_pow,nsmul_eq_mul]
     simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,pow_succ]
     ring
def coefficientStep (F:Poly4 K) (n:ℕ) (C:ℕ → Poly4 K) (j:ℕ):Poly4 K:=
 sameContribution F n j (C j)+downContribution F (j+1) (C (j+1))+
   if j=0 then 0 else upContribution F n (j-1) (C (j-1))
def baseCoefficients (F:Poly4 K):ℕ → ℕ → Poly4 K
 | 0,j => if j=1 then 1 else 0
 | n+1,j => coefficientStep F n (baseCoefficients F n) j
theorem baseCoefficients_zero (F:Poly4 K) (n j:ℕ) (hj:n+1 < j):
   baseCoefficients F n j=0:=by
 induction n generalizing j with
 | zero => simp [baseCoefficients,show j≠1 by omega]
 | succ n ih =>
   simp [baseCoefficients,coefficientStep,ih j (by omega),
     ih (j+1) (by omega),ih (j-1) (by omega),
     sameContribution,downContribution,upContribution]
theorem baseStep_sum (F:Poly4 K) (n:ℕ) (s:Finset ℕ) (P:ℕ → Poly4 K):
   baseStep F n (∑ j∈s,P j)=∑ j∈s,baseStep F n (P j):=by
 simp only [baseStep,map_sum,Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib]
theorem coefficientStep_represents (F:Poly4 K) (n:ℕ) (C:ℕ → Poly4 K)
   (hC:∀ j,n+1 < j → C j=0):
   baseStep F n (∑ j∈Finset.range (n+2),baseMonomial F (n+1) j (C j))=
     ∑ j∈Finset.range (n+3),baseMonomial F (n+2) j (coefficientStep F n C j):=by
 let a j:=baseMonomial F (n+2) j (sameContribution F n j (C j))
 let b j:=baseMonomial F (n+2) (j-1) (downContribution F j (C j))
 let c j:=baseMonomial F (n+2) (j+1) (upContribution F n j (C j))
 have ha:(∑ j∈Finset.range (n+2),a j)=∑ j∈Finset.range (n+3),a j:=by
   conv_rhs => rw [Finset.sum_range_succ]
   simp [a,hC (n+2) (by omega),sameContribution,baseMonomial]
 have hb0:b 0=0:=by simp [b,downContribution,baseMonomial]
 have hb2:b (n+2)=0:=by
   simp [b,hC (n+2) (by omega),downContribution,baseMonomial]
 have hb3:b (n+3)=0:=by
   simp [b,hC (n+3) (by omega),downContribution,baseMonomial]
 have hb:(∑ j∈Finset.range (n+2),b j)=
     ∑ j∈Finset.range (n+3),b (j+1):=by
   calc
     _=∑ j∈Finset.range (n+1),b (j+1):=by
       rw [Finset.sum_range_succ']
       simp only [hb0,add_zero]
     _=_:=by
       symm
       rw [Finset.sum_range_succ,Finset.sum_range_succ]
       simp only [show n+1+1=n+2 by omega,show n+2+1=n+3 by omega,
         hb2,hb3,add_zero]
 have hc:(∑ j∈Finset.range (n+2),c j)=
     ∑ j∈Finset.range (n+3),baseMonomial F (n+2) j
       (if j=0 then 0 else upContribution F n (j-1) (C (j-1))):=by
   conv_rhs => rw [Finset.sum_range_succ']
   simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte,
     Nat.add_sub_cancel,baseMonomial,mul_zero,add_zero]
   rfl
 rw [baseStep_sum]
 calc
   _=∑ j∈Finset.range (n+2),(a j+b j+c j):=by
     apply Finset.sum_congr rfl
     intro j hj
     exact baseStep_monomial F (C j) n j (by have:=Finset.mem_range.mp hj;omega)
   _=(∑ j∈Finset.range (n+2),a j)+
       (∑ j∈Finset.range (n+2),b j)+(∑ j∈Finset.range (n+2),c j):=by
     simp only [Finset.sum_add_distrib]
   _=_:=by
     rw [ha,hb,hc]
     simp only [a,b,coefficientStep,baseMonomial,mul_add,
       Finset.sum_add_distrib,Nat.add_sub_cancel]
theorem baseNumerator_eq_sum (F:Poly4 K) (n:ℕ):
   baseNumerator F n=
     ∑ j∈Finset.range (n+2),baseMonomial F (n+1) j (baseCoefficients F n j):=by
 induction n with
 | zero => simp [baseNumerator,baseCoefficients,baseMonomial]
 | succ n ih =>
   change baseStep F n (baseNumerator F n)=_
   rw [ih,coefficientStep_represents F n _ (baseCoefficients_zero F n)]
   rfl
theorem numerator_eq_coefficient_sum (F:Poly4 K) (n:ℕ):
   numerator K F (n+2)=polyH K F^3*
     ∑ j∈Finset.range (n+2),
       polyH K F^(n+1-j)*polyG K F^j*baseCoefficients F n j:=by
 rw [numerator_eq_H_cube,baseNumerator_eq_sum]
 rfl
end
end ProximityPrize.SubmissionLower.RCN056
end PackedLegacy_A6

/-! Packed from ProximityPrize.SubmissionLower.DX. -/
section PackedLegacy_DX
namespace ProximityPrize.SubmissionLower.RCN053
open RCN077 RCN313 RCN055 RCN056
noncomputable section
variable {K:Type*} [Field K]
def agreementLow (c:ℕ → K) (x u₀ u₁:K):Poly4 K:=
 MvPolynomial.C (c 0)*MvPolynomial.X (1:Fin 4)+
   MvPolynomial.C (c 1)*MvPolynomial.X (2:Fin 4)*
     (MvPolynomial.C x-MvPolynomial.X (0:Fin 4))-affineSeedPolynomial u₀ u₁
def agreementHighCoefficient (F:Poly4 K) (d:ℕ) (c:ℕ → K) (x:K)
   (n j:ℕ):Poly4 K:=
 MvPolynomial.C (c (n+2))*polyH K F^(d-(n+2)+3)*
   baseCoefficients F n j*(MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^(n+2)
def agreementCoefficients (F:Poly4 K) (d:ℕ) (c:ℕ → K) (x u₀ u₁:K)
   (j:ℕ):Poly4 K:=
 (if j=0 then polyH K F^(d+1)*agreementLow c x u₀ u₁ else 0)+
   ∑ n∈Finset.range (d-1),agreementHighCoefficient F d c x n j
theorem agreementNumerator_eq_low_add_sum (F:Poly4 K) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K):
   agreementNumerator F d c x u₀ u₁=polyH K F^(2*d)*agreementLow c x u₀ u₁+
     ∑ n∈Finset.range (d-1),commonNumeratorTerm F d c x (n+2):=by
 have hpow:polyH K F^2*polyH K F^(2*(d-1))=polyH K F^(2*d):=by
   rw [←pow_add,show 2+2*(d-1)=2*d by omega]
 unfold agreementNumerator clearedTaylorNumerator
 rw [show d+1=2+(d-1) by omega,Finset.sum_range_add]
 simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,zero_add,
   show ∀ n:ℕ,2+n=n+2 from fun n => Nat.add_comm 2 n]
 simp only [commonNumeratorTerm,numerator_one,numerator_zero,Nat.sub_zero,
   pow_zero,mul_one,pow_one]
 unfold agreementLow
 linear_combination (MvPolynomial.C (c 1)*MvPolynomial.X (2:Fin 4)*
   (MvPolynomial.C x-MvPolynomial.X (0:Fin 4)))*hpow
theorem highCoefficient_monomial (F:Poly4 K) (d n j:ℕ)
   (hn:n+2 ≤ d) (hj:j ≤ n+1) (c:ℕ → K) (x:K):
   baseMonomial F (d-1) j (agreementHighCoefficient F d c x n j)=
     MvPolynomial.C (c (n+2))*polyH K F^3*
       (polyH K F^(n+1-j)*polyG K F^j*baseCoefficients F n j)*
         polyH K F^(2*(d-(n+2)))*
           (MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^(n+2):=by
 have hp:polyH K F^(d-1-j)*polyH K F^(d-(n+2)+3)=
     polyH K F^3*polyH K F^(n+1-j)*polyH K F^(2*(d-(n+2))):=by
   simp only [←pow_add]
   congr 1
   omega
 unfold baseMonomial agreementHighCoefficient
 linear_combination (MvPolynomial.C (c (n+2))*polyG K F^j*
   baseCoefficients F n j*(MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^(n+2))*hp
theorem commonNumeratorTerm_eq_coefficient_sum (F:Poly4 K) (d n:ℕ)
   (hn:n+2 ≤ d) (c:ℕ → K) (x:K):
   commonNumeratorTerm F d c x (n+2)=
     ∑ j∈Finset.range d,baseMonomial F (d-1) j
       (agreementHighCoefficient F d c x n j):=by
 have hs:(∑ j∈Finset.range (n+2),baseMonomial F (d-1) j
     (agreementHighCoefficient F d c x n j))=
     ∑ j∈Finset.range d,baseMonomial F (d-1) j
       (agreementHighCoefficient F d c x n j):=by
   apply Finset.sum_subset (Finset.range_mono hn)
   intro j _ hj
   have hz:=baseCoefficients_zero F n j (by simp only [Finset.mem_range] at hj;omega)
   simp only [baseMonomial,agreementHighCoefficient,hz,mul_zero,zero_mul]
 rw [←hs]
 unfold commonNumeratorTerm
 rw [numerator_eq_coefficient_sum]
 simp only [Finset.mul_sum,Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro j hj
 simpa only [mul_assoc] using (highCoefficient_monomial F d n j hn
   (by have:=Finset.mem_range.mp hj;omega) c x).symm
theorem agreementNumerator_eq_coefficient_sum (F:Poly4 K) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K):
   agreementNumerator F d c x u₀ u₁=
     ∑ j∈Finset.range d,polyH K F^(d-1-j)*polyG K F^j*
       agreementCoefficients F d c x u₀ u₁ j:=by
 rw [agreementNumerator_eq_low_add_sum F d hd c x u₀ u₁]
 have hlo:(∑ j∈Finset.range d,polyH K F^(d-1-j)*polyG K F^j*
     (if j=0 then polyH K F^(d+1)*agreementLow c x u₀ u₁ else 0))=
     polyH K F^(2*d)*agreementLow c x u₀ u₁:=by
   rw [Finset.sum_eq_single 0]
   · simp only [Nat.sub_zero,pow_zero,mul_one,if_true]
     rw [←mul_assoc, ←pow_add,show d-1+(d+1)=2*d by omega]
   · intro j _ hj
     simp only [if_neg hj,mul_zero]
   · intro hj
     exact (hj (Finset.mem_range.mpr (by omega))).elim
 simp only [agreementCoefficients,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
 rw [hlo,Finset.sum_comm]
 apply congrArg (fun P:Poly4 K => polyH K F^(2*d)*agreementLow c x u₀ u₁+P)
 apply Finset.sum_congr rfl
 intro n hn
 exact commonNumeratorTerm_eq_coefficient_sum F d n
   (by have:=Finset.mem_range.mp hn;omega) c x
end
end ProximityPrize.SubmissionLower.RCN053
end PackedLegacy_DX

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier14 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.DZ. -/
section PackedLegacy_DZ
namespace ProximityPrize.SubmissionLower.RCN057
open RCN313 RCN055 RCN056 RCN234
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
private theorem pderiv_eq_zero_of_wt_lt (weights:Fin 4 → ℕ) (P:Poly K) (i:Fin 4)
   (hP:wt weights P < weights i):MvPolynomial.pderiv i P=0:=by
 apply MvPolynomial.support_eq_empty.mp
 apply Finset.eq_empty_iff_forall_notMem.mpr
 intro d hd
 have hh:=MvPolynomial.le_weightedTotalDegree weights (support_before_pderiv i P d hd)
 simp only [map_add,Finsupp.weight_single,one_nsmul] at hh
 change Finsupp.weight weights d+weights i ≤ wt weights P at hh
 omega
def WeightBound (w:Fin 4 → ℕ) (P:Poly K) (c:ℤ):Prop:=
 P=0∨(wt w P:ℤ) ≤ c
namespace WeightBound
variable {w:Fin 4 → ℕ} {P Q:Poly K} {a b:ℤ}
theorem mono (h:WeightBound w P a) (hab:a ≤ b):WeightBound w P b:=
 h.imp_right (fun hp => hp.trans hab)
theorem add (hP:WeightBound w P a) (hQ:WeightBound w Q a):
   WeightBound w (P+Q) a:=by
 rcases hP with rfl | hp
 · simpa only [zero_add] using hQ
 rcases hQ with rfl | hq
 · rw [add_zero]
   exact Or.inr hp
 right
 have h:(wt w (P+Q):ℤ) ≤ max (wt w P:ℤ) (wt w Q:ℤ):=by
   exact_mod_cast wt_add_le w P Q
 exact h.trans (max_le hp hq)
theorem neg (hP:WeightBound w P a):WeightBound w (-P) a:=by
 rcases hP with rfl | hp
 · exact Or.inl neg_zero
 exact Or.inr (by simpa only [wt_neg] using hp)
theorem sub (hP:WeightBound w P a) (hQ:WeightBound w Q a):
   WeightBound w (P-Q) a:=by
 simpa only [sub_eq_add_neg] using hP.add hQ.neg
theorem mul (hP:WeightBound w P a) (hQ:WeightBound w Q b):
   WeightBound w (P*Q) (a+b):=by
 rcases hP with rfl | hp
 · exact Or.inl (zero_mul _)
 rcases hQ with rfl | hq
 · exact Or.inl (mul_zero _)
 right
 have h:(wt w (P*Q):ℤ) ≤ (wt w P:ℤ)+(wt w Q:ℤ):=by
   exact_mod_cast wt_mul_le w P Q
 linarith
theorem natCast (n:ℕ):WeightBound w (n:Poly K) 0:=
 Or.inr (by simp only [wt_natCast,Nat.cast_zero,le_refl])
theorem scale (n:ℕ) (hP:WeightBound w P a):WeightBound w ((n:Poly K)*P) a:=by
 simpa only [zero_add] using (natCast n).mul hP
theorem pderiv (hP:WeightBound w P a) (i:Fin 4):
   WeightBound w (MvPolynomial.pderiv i P) (a-w i):=by
 by_cases hz:MvPolynomial.pderiv i P=0
 · exact Or.inl hz
 rcases hP with rfl | hp
 · exact (hz (map_zero _)).elim
 right
 have hi:w i ≤ wt w P:=by
   by_contra hh
   exact hz (pderiv_eq_zero_of_wt_lt w P i (by omega))
 have hd:=wt_pderiv_le w P i (wt w P) le_rfl
 have hsum:wt w (MvPolynomial.pderiv i P)+w i ≤ wt w P:=by omega
 have hsum':(wt w (MvPolynomial.pderiv i P):ℤ)+w i ≤ wt w P:=by
   exact_mod_cast hsum
 linarith
theorem horizontal (hP:WeightBound w P a) (t:ℕ)
   (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (ht:t ≤ 1):
   WeightBound w (horizontalDerivation P) (a+1-t):=by
 have hx:=hP.pderiv (0:Fin 4)
 have hy:=hP.pderiv (1:Fin 4)
 have hr:WeightBound w (MvPolynomial.X (2:Fin 4):Poly K) 1:=
   Or.inr (by simp only [wt_X,hR,Nat.cast_one,le_refl])
 simp only [hX,Nat.cast_zero,sub_zero] at hx
 rw [hY] at hy
 have hxy:WeightBound w (MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv (1:Fin 4) P)
     (a+1-t):=by convert hr.mul hy using 1;ring
 have ht':(t:ℤ) ≤ 1:=by exact_mod_cast ht
 simpa only [horizontalDerivation,Derivation.add_apply,Derivation.smul_apply,
   smul_eq_mul] using (hx.mono (by linarith)).add hxy
end WeightBound
theorem contribution_bounds (w:Fin 4 → ℕ) (t:ℕ)
   (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (ht:t ≤ 1)
   (F P:Poly K) (C a:ℤ) (hF:WeightBound w F C) (hP:WeightBound w P a)
   (n j:ℕ):
   WeightBound w (sameContribution F n j P) (a+C-t)∧
   WeightBound w (downContribution F j P) (a+C+2-2*t)∧
   WeightBound w (upContribution F n j P) (a+C-2):=by
 have hH:WeightBound w (polyH K F) (C-1):=by
   simpa only [polyH,hR,Nat.cast_one] using hF.pderiv (2:Fin 4)
 have hG:WeightBound w (polyG K F) (C+1-t):=by
   simpa only [polyG,horizontalDerivation,Derivation.add_apply,
     Derivation.smul_apply,smul_eq_mul] using (hF.horizontal t hX hY hR ht).neg
 have hDH:=hH.horizontal t hX hY hR ht
 have hDG:=hG.horizontal t hX hY hR ht
 have hDP:=hP.horizontal t hX hY hR ht
 have hGR:=hG.pderiv (2:Fin 4)
 have hHR:=hH.pderiv (2:Fin 4)
 have hPR:=hP.pderiv (2:Fin 4)
 simp only [hR,Nat.cast_one] at hGR hHR hPR
 refine ⟨?_,?_,?_⟩
 · unfold sameContribution
   apply WeightBound.add
   · apply WeightBound.sub
     · convert hH.mul hDP using 1;ring
     · convert (hP.scale (n+j)).mul hDH using 1;ring
   · convert (hP.scale j).mul hGR using 1;ring
 · unfold downContribution
   convert (hP.scale j).mul hDG using 1;ring
 · unfold upContribution
   apply WeightBound.sub
   · convert hH.mul hPR using 1;ring
   · convert (hP.scale (n+j)).mul hHR using 1;ring
theorem baseCoefficients_weightBound (w:Fin 4 → ℕ) (t:ℕ)
   (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (ht:t ≤ 1)
   (F:Poly K) (C:ℤ) (hF:WeightBound w F C) (n j:ℕ):
   WeightBound w (baseCoefficients F n j)
     (2-t+n*(C-t)-j*(2-t)):=by
 induction n generalizing j with
 | zero =>
   by_cases hj:j=1
   · subst j
     simp only [baseCoefficients,↓reduceIte]
     convert WeightBound.natCast (w:=w) (K:=K) 1 using 1 <;> push_cast <;> ring
   · exact Or.inl (by simp [baseCoefficients,hj])
 | succ n ih =>
   rw [baseCoefficients,coefficientStep]
   apply WeightBound.add
   · apply WeightBound.add
     · convert (contribution_bounds w t hX hY hR ht F _ C _ hF (ih j) n j).1 using 1
       push_cast
       ring
     · convert (contribution_bounds w t hX hY hR ht F _ C _ hF (ih (j+1)) n (j+1)).2.1
         using 1
       push_cast
       ring
   · by_cases hj:j=0
     · rw [if_pos hj]
       exact Or.inl rfl
     · rw [if_neg hj]
       have hj1:1 ≤ j:=by omega
       convert (contribution_bounds w t hX hY hR ht F _ C _ hF (ih (j-1)) n (j-1)).2.2
         using 1
       simp only [Nat.cast_sub hj1,Nat.cast_one,Nat.cast_add]
       ring
theorem baseCoefficients_cumulative_wt_le (w:Fin 4 → ℕ)
   (hX:w 0=0) (hY:w 1=1) (hR:w 2=1)
   (F:Poly K) (C:ℕ) (hC:1 ≤ C) (hF:wt w F ≤ C) (n j:ℕ):
   wt w (baseCoefficients F n j) ≤ 1+n*(C-1)-j:=by
 have h:=baseCoefficients_weightBound w 1 hX hY hR le_rfl F C
   (Or.inr (by exact_mod_cast hF)) n j
 rcases h with hz | hb
 · simp [hz,wt,MvPolynomial.weightedTotalDegree]
 · have hi:(wt w (baseCoefficients F n j):ℤ)+j ≤ 1+n*((C-1:ℕ):ℤ):=by
     rw [Nat.cast_sub hC,Nat.cast_one]
     norm_num at hb ⊢
     linarith
   have hn:wt w (baseCoefficients F n j)+j ≤ 1+n*(C-1):=by exact_mod_cast hi
   omega
theorem baseCoefficients_R_wt_le (w:Fin 4 → ℕ)
   (hX:w 0=0) (hY:w 1=0) (hR:w 2=1)
   (F:Poly K) (s:ℕ) (hF:wt w F ≤ s) (n j:ℕ):
   wt w (baseCoefficients F n j) ≤ n*s+2-2*j:=by
 have h:=baseCoefficients_weightBound w 0 hX hY hR (by omega) F s
   (Or.inr (by exact_mod_cast hF)) n j
 rcases h with hz | hb
 · simp [hz,wt,MvPolynomial.weightedTotalDegree]
 · have hi:(wt w (baseCoefficients F n j):ℤ)+2*j ≤ n*s+2:=by
     norm_num at hb ⊢
     linarith
   have hn:wt w (baseCoefficients F n j)+2*j ≤ n*s+2:=by exact_mod_cast hi
   omega
private theorem wt_coordinate (P:Poly K) (i:Fin 4):
   wt (Pi.single i 1) P=P.degreeOf i:=by
 rw [wt,MvPolynomial.weightedTotalDegree,MvPolynomial.degreeOf_eq_sup]
 apply congrArg (fun f:(Fin 4 →₀ ℕ) → ℕ => P.support.sup f)
 funext d
 exact Finsupp.weight_single_one_apply i d
theorem baseCoefficients_R_degree_le (F:Poly K) (s:ℕ)
   (hF:F.degreeOf (2:Fin 4) ≤ s) (n j:ℕ):
   (baseCoefficients F n j).degreeOf (2:Fin 4) ≤ n*s+2-2*j:=by
 simpa only [wt_coordinate] using baseCoefficients_R_wt_le (Pi.single (2:Fin 4) 1)
   (by simp) (by simp) (by simp) F s (by simpa only [wt_coordinate] using hF) n j
theorem baseCoefficients_support_bounds (F:Poly K) (s M L:ℕ)
   (hM:1 ≤ M) (hL:1 ≤ L) (hR:F.degreeOf (2:Fin 4) ≤ s)
   (hYR:wt ![0,1,1,0] F ≤ M) (hAll:wt ![0,1,1,1] F ≤ L) (n j:ℕ):
   (baseCoefficients F n j).degreeOf (2:Fin 4) ≤ n*s+2-2*j∧
   wt ![0,1,1,0] (baseCoefficients F n j) ≤ 1+n*(M-1)-j∧
   wt ![0,1,1,1] (baseCoefficients F n j) ≤ 1+n*(L-1)-j:=by
 exact ⟨baseCoefficients_R_degree_le F s hR n j,
   baseCoefficients_cumulative_wt_le _ rfl rfl rfl F M hM hYR n j,
   baseCoefficients_cumulative_wt_le _ rfl rfl rfl F L hL hAll n j⟩
end
end ProximityPrize.SubmissionLower.RCN057
end PackedLegacy_DZ

/-! Packed from ProximityPrize.SubmissionLower.DY. -/
section PackedLegacy_DY
namespace ProximityPrize.SubmissionLower.RCN054
open RCN313 RCN055 RCN056 RCN057 RCN053 RCN234 RCN095
noncomputable section
variable {K:Type*} [Field K]
theorem weightBound_C (w:Fin 4 → ℕ) (c:K):
   WeightBound w (MvPolynomial.C c:Poly K) 0:=
 Or.inr (by simp only [wt_C,Nat.cast_zero,le_refl])
theorem weightBound_pow {w:Fin 4 → ℕ} {P:Poly K} {a:ℤ}
   (hP:WeightBound w P a) (n:ℕ):WeightBound w (P^n) (n*a):=by
 induction n with
 | zero => simpa only [pow_zero,Nat.cast_zero,zero_mul,Nat.cast_one] using
     (WeightBound.natCast (w:=w) (K:=K) 1)
 | succ n ih =>
   rw [pow_succ]
   convert ih.mul hP using 1
   push_cast
   ring
theorem weightBound_sum {w:Fin 4 → ℕ} {a:ℤ} (I:Finset ℕ) (P:ℕ → Poly K)
   (hP:∀ i∈I,WeightBound w (P i) a):WeightBound w (∑ i∈I,P i) a:=by
 classical
 induction I using Finset.induction_on with
 | empty => exact Or.inl (by simp)
 | @insert i I hi ih =>
   rw [Finset.sum_insert hi]
   exact (hP i (Finset.mem_insert_self _ _)).add
     (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)))
theorem weightBound_shift (w:Fin 4 → ℕ) (hX:w 0=0) (x:K):
   WeightBound w (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly K) 0:=
 (weightBound_C w x).sub (Or.inr (by simp only [wt_X,hX,Nat.cast_zero,le_refl]))
theorem agreementLow_weightBound (w:Fin 4 → ℕ) (hX:w 0=0)
   (hY:w 1 ≤ 1) (hR:w 2=1) (hZ:w 3 ≤ 1)
   (c:ℕ → K) (x u₀ u₁:K):WeightBound w (agreementLow c x u₀ u₁) 1:=by
 have hvar (i:Fin 4) (hi:w i ≤ 1):
     WeightBound w (MvPolynomial.X i:Poly K) 1:=by
   right
   rw [wt_X]
   exact_mod_cast hi
 have h₀:=(weightBound_C w (c 0)).mul (hvar 1 hY)
 have h₁:=((weightBound_C w (c 1)).mul (hvar 2 (by omega))).mul (weightBound_shift w hX x)
 have hseed:=((weightBound_C w u₀).mono (by norm_num:(0:ℤ) ≤ 1)).add
   (by simpa only [add_zero] using (hvar 3 hZ).mul (weightBound_C w u₁))
 simpa only [agreementLow,affineSeedPolynomial,zero_add,add_zero] using (h₀.add h₁).sub hseed
theorem agreementCoefficients_weightBound (w:Fin 4 → ℕ) (t:ℕ)
   (hX:w 0=0) (hY:w 1=t) (hR:w 2=1) (hZ:w 3 ≤ 1) (ht:t ≤ 1)
   (F:Poly K) (C:ℤ) (hF:WeightBound w F C) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K) (j:ℕ):
   WeightBound w (agreementCoefficients F d c x u₀ u₁ j)
     ((d+1:ℕ)*(C-1)+1+(d-1:ℕ)*(1-(t:ℤ))-j*(2-(t:ℤ))):=by
 have ht':(t:ℤ) ≤ 1:=by exact_mod_cast ht
 have hH:WeightBound w (polyH K F) (C-1):=by
   simpa only [polyH,hR,Nat.cast_one] using hF.pderiv (2:Fin 4)
 unfold agreementCoefficients
 apply WeightBound.add
 · by_cases hj:j=0
   · subst j
     rw [if_pos rfl]
     apply ((weightBound_pow hH (d+1)).mul
       (agreementLow_weightBound w hX (by omega) hR hZ c x u₀ u₁)).mono
     simp only [Nat.cast_zero,zero_mul,sub_zero]
     have hn:(0:ℤ) ≤ (d-1:ℕ):=Nat.cast_nonneg _
     nlinarith
   · rw [if_neg hj]
     exact Or.inl rfl
 · apply weightBound_sum
   intro n hn
   have hn':n+2 ≤ d:=by have:=Finset.mem_range.mp hn;omega
   have he:((d-(n+2)+3:ℕ):ℤ)=(d:ℤ)-n+1:=by
     push_cast [Nat.cast_sub hn']
     ring
   have hn'':(n:ℤ)+2 ≤ d:=by exact_mod_cast hn'
   have hd':((d-1:ℕ):ℤ)=(d:ℤ)-1:=by omega
   have hterm:=(((weightBound_C w (c (n+2))).mul
     (weightBound_pow hH (d-(n+2)+3))).mul
       (baseCoefficients_weightBound w t hX hY hR ht F C hF n j)).mul
         (weightBound_pow (weightBound_shift w hX x) (n+2))
   apply hterm.mono
   rw [he,hd']
   push_cast
   nlinarith
theorem agreementCoefficients_support_bounds (F:Poly K) (s M L:ℕ)
   (hR:F.degreeOf (2:Fin 4) ≤ s) (hYR:wt ![0,1,1,0] F ≤ M)
   (hAll:wt ![0,1,1,1] F ≤ L) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K) (j:ℕ):
   (agreementCoefficients F d c x u₀ u₁ j).degreeOf (2:Fin 4) ≤ (d+1)*s-1-2*j∧
   wt ![0,1,1,0] (agreementCoefficients F d c x u₀ u₁ j) ≤ (d+1)*M-d-j∧
   wt ![0,1,1,1] (agreementCoefficients F d c x u₀ u₁ j) ≤ (d+1)*L-d-j:=by
 have hcoord (P:Poly K):wt (Pi.single (2:Fin 4) 1) P=P.degreeOf (2:Fin 4):=by
   rw [wt,MvPolynomial.weightedTotalDegree,MvPolynomial.degreeOf_eq_sup]
   apply congrArg (fun f:(Fin 4 →₀ ℕ) → ℕ => P.support.sup f)
   funext e
   exact Finsupp.weight_single_one_apply _ e
 have hbound (w:Fin 4 → ℕ) (t:ℕ) (hX:w 0=0) (hY:w 1=t)
     (hR':w 2=1) (hZ:w 3 ≤ 1) (ht:t ≤ 1) (N:ℕ) (hF:wt w F ≤ N):=
   agreementCoefficients_weightBound w t hX hY hR' hZ ht F N
     (Or.inr (by exact_mod_cast hF)) d hd c x u₀ u₁ j
 constructor
 · have h:=hbound (Pi.single (2:Fin 4) 1) 0 (by simp) (by simp) (by simp)
     (by simp) (by omega) s (by simpa only [hcoord] using hR)
   rcases h with hz | hb
   · simp [hz]
   · rw [hcoord] at hb
     have he:((d-1:ℕ):ℤ)=(d:ℤ)-1:=by omega
     rw [he] at hb
     push_cast at hb
     have hh:((agreementCoefficients F d c x u₀ u₁ j).degreeOf (2:Fin 4):ℤ)+1+
         2*j ≤ (d+1:ℕ)*s:=by push_cast;nlinarith
     have hn:(agreementCoefficients F d c x u₀ u₁ j).degreeOf (2:Fin 4)+1+
         2*j ≤ (d+1)*s:=by exact_mod_cast hh
     omega
 · have cumulative (w:Fin 4 → ℕ) (hX:w 0=0) (hY:w 1=1)
       (hR':w 2=1) (hZ:w 3 ≤ 1) (N:ℕ) (hF:wt w F ≤ N):
       wt w (agreementCoefficients F d c x u₀ u₁ j) ≤ (d+1)*N-d-j:=by
     rcases hbound w 1 hX hY hR' hZ le_rfl N hF with hz | hb
     · simp [hz,wt,MvPolynomial.weightedTotalDegree]
     · have hh:(wt w (agreementCoefficients F d c x u₀ u₁ j):ℤ)+d+j ≤
           (d+1:ℕ)*N:=by push_cast at hb ⊢;nlinarith
       have hn:wt w (agreementCoefficients F d c x u₀ u₁ j)+d+j ≤
           (d+1)*N:=by exact_mod_cast hh
       omega
   exact ⟨cumulative _ rfl rfl rfl (by decide) M hYR,
     cumulative _ rfl rfl rfl (by decide) L hAll⟩
def coefficientFlag (a b s d j:ℕ):FlagDegree:=
 ⟨(d+1)*a,1+(d+1)*b-d+j,(d+1)*s-1-2*j⟩
def hFlag (a b s:ℕ):FlagDegree:=⟨a,b,s-1⟩
def gFlag (a b s:ℕ):FlagDegree:=⟨a,b-1,s+1⟩
def directionFlag (a b s:ℕ):FlagDegree:=⟨2*a,2*b-1,2*s-1⟩
theorem coefficientFlag_cumulative (a b s d j:ℕ) (hb:1 ≤ b) (hs:2 ≤ s)
   (hj:j < d):
   (coefficientFlag a b s d j).all=(d+1)*s-1-2*j∧
   (coefficientFlag a b s d j).yz+(coefficientFlag a b s d j).all=
     (d+1)*(b+s)-d-j∧
   (coefficientFlag a b s d j).zOnly+(coefficientFlag a b s d j).yz+
     (coefficientFlag a b s d j).all=(d+1)*(a+b+s)-d-j:=by
 obtain ⟨b,rfl⟩:=Nat.exists_eq_add_of_le hb
 obtain ⟨s,rfl⟩:=Nat.exists_eq_add_of_le hs
 obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
 simp only [coefficientFlag,Nat.succ_eq_add_one,Nat.mul_add,Nat.add_mul,
   Nat.mul_one,Nat.one_mul]
 exact ⟨trivial,by omega,by omega⟩
theorem coefficientFlag_nonnegative_form (a b s d j:ℕ) (hb:1 ≤ b) (hs:2 ≤ s)
   (hj:j < d):coefficientFlag a b s d j=
     ⟨(d+1)*a,(d+1)*(b-1)+2+j,
       (d+1)*(s-2)+3+2*(d-1-j)⟩:=by
 obtain ⟨b,rfl⟩:=Nat.exists_eq_add_of_le hb
 obtain ⟨s,rfl⟩:=Nat.exists_eq_add_of_le hs
 obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
 dsimp only [coefficientFlag]
 congr 1 <;> simp only [Nat.succ_eq_add_one,Nat.mul_add,Nat.add_mul,Nat.mul_one,
   Nat.one_mul,Nat.add_sub_cancel_left] <;> omega
theorem coefficientFlag_add_baseMonomial (a b s d j:ℕ) (hb:1 ≤ b) (hs:2 ≤ s)
   (hj:j < d):
   coefficientFlag a b s d j+(d-1-j) • hFlag a b s+j • gFlag a b s=
     unitYZFlag+d • directionFlag a b s:=by
 rw [coefficientFlag_nonnegative_form a b s d j hb hs hj]
 obtain ⟨b,rfl⟩:=Nat.exists_eq_add_of_le hb
 obtain ⟨s,rfl⟩:=Nat.exists_eq_add_of_le hs
 obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
 have hk:j+1+k-1-j=k:=by omega
 have hs':2+s-1=1+s:=by omega
 have hb':2*(1+b)-1=1+2*b:=by omega
 have hs'':2*(2+s)-1=3+2*s:=by omega
 simp only [hk,hFlag,gFlag,directionFlag,unitYZFlag,Nat.add_sub_cancel_left,
   hs',hb',hs'']
 change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
 congr 1 <;> simp only [add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
   <;> dsimp <;> ring
theorem agreementCoefficients_in_flag (F:Poly K) (a b s:ℕ) (hb:1 ≤ b) (hs:2 ≤ s)
   (hR:F.degreeOf (2:Fin 4) ≤ s) (hYR:wt ![0,1,1,0] F ≤ b+s)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K) (j:ℕ) (hj:j < d):
   ∀ e∈(agreementCoefficients F d c x u₀ u₁ j).support,
     e 2 ≤ (coefficientFlag a b s d j).all∧
     e 1+e 2 ≤ (coefficientFlag a b s d j).yz+(coefficientFlag a b s d j).all∧
     e 1+e 2+e 3 ≤ (coefficientFlag a b s d j).zOnly+
       (coefficientFlag a b s d j).yz+(coefficientFlag a b s d j).all:=by
 intro e he
 obtain ⟨hr,hyr,ht⟩:=agreementCoefficients_support_bounds F s (b+s) (a+b+s)
   hR hYR hAll d hd c x u₀ u₁ j
 obtain ⟨fr,fyr,ft⟩:=coefficientFlag_cumulative a b s d j hb hs hj
 rw [ft,fyr,fr]
 have heR:=(MvPolynomial.le_degreeOf_of_mem_support (2:Fin 4) he).trans hr
 have heYR:=(MvPolynomial.le_weightedTotalDegree ![0,1,1,0] he).trans hyr
 have heT:=(MvPolynomial.le_weightedTotalDegree ![0,1,1,1] he).trans ht
 rw [RCN081.weight_fin4] at heYR heT
 change e 0*0+e 1*1+e 2*1+e 3*0 ≤ _ at heYR
 change e 0*0+e 1*1+e 2*1+e 3*1 ≤ _ at heT
 simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero,Nat.zero_add] at heYR heT
 exact ⟨heR,heYR,heT⟩
theorem surfaceMap_agreementCoefficients_in_flag {Ω:Type*} [Field Ω]
   (φ:Polynomial K →+*Ω) (F:Poly K) (a b s:ℕ) (hb:1 ≤ b) (hs:2 ≤ s)
   (hR:F.degreeOf (2:Fin 4) ≤ s) (hYR:wt ![0,1,1,0] F ≤ b+s)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K) (j:ℕ) (hj:j < d):
   PolynomialInFlag (coefficientFlag a b s d j)
     (RCN136.surfaceMap φ (agreementCoefficients F d c x u₀ u₁ j)):=by
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp
   (RCN136.support_surfaceMap_subset φ _ he)
 exact agreementCoefficients_in_flag F a b s hb hs hR hYR hAll d hd c x u₀ u₁ j hj q hq
theorem surfaceMap_agreementNumerator_eq_coefficient_sum {Ω:Type*} [Field Ω]
   (φ:Polynomial K →+*Ω) (F:Poly K) (d:ℕ) (hd:2 ≤ d)
   (c:ℕ → K) (x u₀ u₁:K):
   RCN136.surfaceMap φ (agreementNumerator F d c x u₀ u₁)=
     ∑ j∈Finset.range d,RCN136.surfaceMap φ (polyH K F)^(d-1-j)*
       RCN136.surfaceMap φ (polyG K F)^j*
         RCN136.surfaceMap φ (agreementCoefficients F d c x u₀ u₁ j):=by
 rw [agreementNumerator_eq_coefficient_sum F d hd c x u₀ u₁]
 simp only [map_sum,map_mul,map_pow]
end
end ProximityPrize.SubmissionLower.RCN054
end PackedLegacy_DY

/-! Packed from ProximityPrize.SubmissionLower.D2. -/
section PackedLegacy_D2
namespace ProximityPrize.SubmissionLower.RCN207
open scoped Classical BigOperators Pointwise
open RCN095
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
variable {K:Type*} [Field K]
local notation "Poly" => MvPolynomial (Fin 3) K
def filteredCut {R:Type*} [CommRing R] (k:ℕ) (B:Fin (k+1) → R)
   (H G:R):R:=∑ j,B j*H^(k-j.val)*G^j.val
def movingEquation (H G Q U:Poly) (t:K):Poly:=
 H*(MvPolynomial.C t-Q)-U*G
def eliminatedCut (k:ℕ) (B:Fin (k+1) → Poly) (Q U:Poly) (t:K):Poly:=
 filteredCut k B U (MvPolynomial.C t-Q)
theorem map_filteredCut {R S:Type*} [CommRing R] [CommRing S]
   (ev:R →+*S) (k:ℕ) (B:Fin (k+1) → R) (H G:R):
   ev (filteredCut k B H G)=filteredCut k (fun j↦ev (B j)) (ev H) (ev G):=by
 simp [filteredCut]
theorem binary_clearing {R:Type*} [CommRing R] (k:ℕ) (B:Fin (k+1) → R)
   (H G U V:R) (hrel:H*V=U*G):
   H^k*filteredCut k B U V=U^k*filteredCut k B H G:=by
 unfold filteredCut
 rw [Finset.mul_sum,Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro j _
 have hj:k-j.val+j.val=k:=Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)
 have hh:H^k=H^(k-j.val)*H^j.val:=by rw [←pow_add,hj]
 have hu:U^k=U^(k-j.val)*U^j.val:=by rw [←pow_add,hj]
 calc
   _=B j*H^(k-j.val)*U^(k-j.val)*(H*V)^j.val:=by
     rw [hh,mul_pow];ring
   _=B j*H^(k-j.val)*U^(k-j.val)*(U*G)^j.val:=by rw [hrel]
   _=_:=by rw [hu,mul_pow];ring
theorem clearing_at_equation {R:Type*} [CommRing R] (ev:Poly →+*R)
   (k:ℕ) (B:Fin (k+1) → Poly) (H G Q U:Poly) (t:K)
   (hN:ev (movingEquation H G Q U t)=0):
   ev H^k*ev (eliminatedCut k B Q U t)=
     ev U^k*ev (filteredCut k B H G):=by
 have hrel:ev H*ev (MvPolynomial.C t-Q)=ev U*ev G:=by
   simpa [movingEquation,sub_eq_zero] using hN
 simp only [eliminatedCut,map_filteredCut]
 exact binary_clearing k _ _ _ _ _ hrel
theorem eliminatedCut_zero_iff {L:Type*} [Field L] (ev:Poly →+*L)
   (k:ℕ) (B:Fin (k+1) → Poly) (H G Q U:Poly) (t:K)
   (hN:ev (movingEquation H G Q U t)=0) (hH:ev H≠0) (hU:ev U≠0):
   ev (eliminatedCut k B Q U t)=0 ↔ ev (filteredCut k B H G)=0:=by
 have heq:=clearing_at_equation ev k B H G Q U t hN
 constructor
 · intro hz
   rw [hz,mul_zero] at heq
   exact (mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero _ hU)
 · intro hz
   rw [hz,mul_zero] at heq
   exact (mul_eq_zero.mp heq).resolve_left (pow_ne_zero _ hH)
theorem original_mem_of_eliminated_mem (P:Ideal Poly) [P.IsPrime]
   (k:ℕ) (B:Fin (k+1) → Poly) (H G Q U:Poly) (t:K)
   (hN:movingEquation H G Q U t∈P)
   (hT:eliminatedCut k B Q U t∈P) (hU:U∉P):
   filteredCut k B H G∈P:=by
 let ev:=Ideal.Quotient.mk P
 have heq:=clearing_at_equation ev k B H G Q U t
   (Ideal.Quotient.eq_zero_iff_mem.mpr hN)
 have hzero:ev (eliminatedCut k B Q U t)=0:=
   Ideal.Quotient.eq_zero_iff_mem.mpr hT
 have hUne:ev U≠0:=fun h↦hU (Ideal.Quotient.eq_zero_iff_mem.mp h)
 rw [hzero,mul_zero] at heq
 exact Ideal.Quotient.eq_zero_iff_mem.mp
   ((mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero _ hUne))
theorem inFlag_const (p:FlagDegree) (c:K):PolynomialInFlag p (MvPolynomial.C c):=by
 intro d hd
 have hd0:d=0:=by
   by_contra h
   exact (MvPolynomial.mem_support_iff.mp hd) (MvPolynomial.coeff_C_of_ne_zero h _)
 subst d
 exact inFlag_zero p
private theorem flag_eq {p q:FlagDegree} (hx:p.zOnly=q.zOnly)
   (hy:p.yz=q.yz) (hz:p.all=q.all):p=q:=by
 cases p;cases q;simp_all
theorem inFlag_map {E:Type*} [Field E] (f:K →+*E)
   {p:FlagDegree} {A:Poly} (hA:PolynomialInFlag p A):
   PolynomialInFlag p (MvPolynomial.map f A):=by
 intro d hd
 exact hA d (MvPolynomial.support_map_subset f A hd)
theorem inFlag_add_poly {p:FlagDegree} {A B:Poly}
   (hA:PolynomialInFlag p A) (hB:PolynomialInFlag p B):
   PolynomialInFlag p (A+B):=by
 intro d hd
 rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
 · exact hA d h
 · exact hB d h
theorem inFlag_sub_poly {p:FlagDegree} {A B:Poly}
   (hA:PolynomialInFlag p A) (hB:PolynomialInFlag p B):
   PolynomialInFlag p (A-B):=by
 intro d hd
 rcases Finset.mem_union.mp (MvPolynomial.support_sub (Fin 3) A B hd) with h | h
 · exact hA d h
 · exact hB d h
theorem inFlag_mul_poly {p q:FlagDegree} {A B:Poly}
   (hA:PolynomialInFlag p A) (hB:PolynomialInFlag q B):
   PolynomialInFlag (p+q) (A*B):=by
 intro d hd
 obtain ⟨a,ha,b,hb,rfl⟩:=Finset.mem_add.mp (MvPolynomial.support_mul A B hd)
 exact inFlag_add (hA a ha) (hB b hb)
theorem inFlag_pow_poly {p:FlagDegree} {A:Poly} (hA:PolynomialInFlag p A) (k:ℕ):
   PolynomialInFlag (k • p) (A^k):=by
 induction k with
 | zero => simpa using inFlag_const (0 • p) (1:K)
 | succ k ih =>
   have heq:(k+1) • p=k • p+p:=by
     apply flag_eq <;> simp only [nsmul_zOnly,nsmul_yz,nsmul_all,
       add_zOnly,add_yz,add_all] <;> ring
   rw [pow_succ,heq]
   exact inFlag_mul_poly ih hA
theorem inFlag_sum_poly {ι:Type*} (s:Finset ι) (p:FlagDegree) (A:ι → Poly)
   (hA:∀ i∈s,PolynomialInFlag p (A i)):PolynomialInFlag p (∑ i∈s,A i):=by
 intro d hd
 obtain ⟨i,hi,hdi⟩:=Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
 exact hA i hi d hdi
theorem eliminatedCut_inFlag (k:ℕ) (B:Fin (k+1) → Poly) (Q U:Poly) (t:K)
   (c:Fin (k+1) → FlagDegree) (P:FlagDegree)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hQ:PolynomialInFlag (2 • unitAllFlag) Q)
   (hU:PolynomialInFlag unitYZFlag U)
   (hc:∀ j,c j+(k-j.val) • unitYZFlag+j.val • (2 • unitAllFlag)=P):
   PolynomialInFlag P (eliminatedCut k B Q U t):=by
 unfold eliminatedCut filteredCut
 apply inFlag_sum_poly
 intro j _
 rw [←hc j]
 exact inFlag_mul_poly (inFlag_mul_poly (hB j) (inFlag_pow_poly hU _))
   (inFlag_pow_poly (inFlag_sub_poly (inFlag_const _ _) hQ) _)
theorem eliminatedCut_small_flag (a b s k:ℕ) (C:FlagDegree)
   (B:Fin (k+1) → Poly) (Q U:Poly) (t:K)
   (c:Fin (k+1) → FlagDegree)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hQ:PolynomialInFlag (2 • unitAllFlag) Q)
   (hU:PolynomialInFlag unitYZFlag U)
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree)):
   PolynomialInFlag (C+k • (⟨a,b+1,s+2⟩:FlagDegree)) (eliminatedCut k B Q U t):=by
 apply eliminatedCut_inFlag k B Q U t c _ hB hQ hU
 intro j
 have hx:=congrArg FlagDegree.zOnly (hc j)
 have hy:=congrArg FlagDegree.yz (hc j)
 have hz:=congrArg FlagDegree.all (hc j)
 have hj:k-j.val+j.val=k:=Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)
 apply flag_eq
 all_goals simp only [add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,
   nsmul_all,unitYZFlag,unitAllFlag] at*
 all_goals nlinarith
theorem movingEquation_inFlag (a b s:ℕ) (H G Q U:Poly) (t:K)
   (hH:PolynomialInFlag ⟨a,b+1,s+1⟩ H)
   (hG:PolynomialInFlag ⟨a,b,s+3⟩ G)
   (hQ:PolynomialInFlag (2 • unitAllFlag) Q)
   (hU:PolynomialInFlag unitYZFlag U):
   PolynomialInFlag ⟨a,b+1,s+3⟩ (movingEquation H G Q U t):=by
 apply inFlag_sub_poly
 · have hc:(⟨a,b+1,s+1⟩:FlagDegree)+2 • unitAllFlag=⟨a,b+1,s+3⟩:=by
     apply flag_eq
     all_goals simp only [add_zOnly,add_yz,add_all,nsmul_zOnly,
       nsmul_yz,nsmul_all,unitAllFlag]
     omega
   rw [←hc]
   exact inFlag_mul_poly hH (inFlag_sub_poly (inFlag_const _ _) hQ)
 · have hc:unitYZFlag+(⟨a,b,s+3⟩:FlagDegree)=⟨a,b+1,s+3⟩:=by
     apply flag_eq <;> simp only [add_zOnly,add_yz,add_all,unitYZFlag] <;> omega
   rw [←hc]
   exact inFlag_mul_poly hU hG
theorem small_projection_cap_identity (a b s k:ℕ) (C:FlagDegree):
   let f:FlagDegree:=⟨a,b+1,s+2⟩
   let h:FlagDegree:=⟨a,b+1,s+1⟩
   let g:FlagDegree:=⟨a,b,s+3⟩
   let D:FlagDegree:=⟨2*a,2*b+1,2*s+3⟩
   let E:FlagDegree:=⟨a,b+1,s+3⟩
   let P:=C+k • D
   a*flagMixed f P unitZFlag+b*flagMixed f P unitYZFlag+
     s*flagMixed f P unitAllFlag+flagMixed f E (C+k • f)+k*flagMixed f h g=
     flagMixed f P D+2*k*flagMixed f unitAllFlag unitYZFlag:=by
 dsimp only
 simp only [flagMixed,add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,
   nsmul_all,unitZFlag,unitYZFlag,unitAllFlag]
 ring
end
end ProximityPrize.SubmissionLower.RCN207
end PackedLegacy_D2

/-! Packed from ProximityPrize.SubmissionLower.Z8. -/
section PackedLegacy_Z8
namespace ProximityPrize.SubmissionLower.RCN198
open scoped Classical BigOperators
open RCN313 RCN136 RCN238 RCN053 RCN054 RCN095 RCN207 RCN234 RCN156 RCN275 RCN287
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 35000
variable {K Ω:Type} [Field K] [Field Ω]
def direction (a b s:ℕ):FlagDegree:=⟨2*a,2*b+1,2*s+3⟩
def center (a b s:ℕ):FlagDegree:=unitYZFlag+direction a b s
def support (a b s:ℕ):ResidualSupportParameters:=
 ⟨s+2,b+s+3,a+b+s+3,by omega,by omega,by omega,by omega⟩
theorem shifted_flags (a b s:ℕ):
   hFlag a (b+1) (s+2)=⟨a,b+1,s+1⟩∧
   gFlag a (b+1) (s+2)=⟨a,b,s+3⟩∧
   directionFlag a (b+1) (s+2)=direction a b s:=by
 refine ⟨?_,?_,?_⟩ <;>
   simp only [hFlag,gFlag,directionFlag,direction] <;> congr 1 <;> omega
theorem class_total (a b s k:ℕ):
   unitYZFlag+(k+1) • direction a b s=
     center a b s+k • direction a b s:=by
 change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
 congr 1 <;> simp only [center,direction,unitYZFlag,
   add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all] <;> ring
theorem support_data (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
   (hR:F.degreeOf 2 ≤ s+2)
   (hYR:wt ![0,1,1,0] F ≤ b+s+3)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s+3):
   ResidualSupportData (support a b s) F:=by
 refine ⟨?_,hYR,hAll⟩
 have hw:residualSWeights=Pi.single (2:Fin 4) 1:=by
   funext i;fin_cases i <;> rfl
 simpa only [hw,wt,support,MvPolynomial.weightedTotalDegree_piSingle] using hR
theorem sharp_flag_eq (a b s d:ℕ):
   sharpResidualAgreementFlag (support a b s) d=
     unitYZFlag+d • direction a b s:=by
 have hdir:sharpAgreementDirection (support a b s)=direction a b s:=by
   simp only [sharpAgreementDirection,support,direction]
   congr 1 <;> omega
 simp only [sharpResidualAgreementFlag,hdir,direction,unitYZFlag]
 change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
 congr 1 <;> simp only [add_zOnly,add_yz,add_all,
   nsmul_zOnly,nsmul_yz,nsmul_all] <;> ring
theorem low_agreement_in_center (φ:Polynomial K →+*Ω)
   (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
   (hR:F.degreeOf 2 ≤ s+2)
   (hYR:wt ![0,1,1,0] F ≤ b+s+3)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s+3)
   (d:ℕ) (hd:d ≤ 1) (x u0 u1:K):
   PolynomialInFlag (center a b s) (agreementPolynomial φ F d x u0 u1):=by
 have hh:=surfaceMap_agreement_in_sharp_flag
   (P:=support a b s) (by dsimp [support];omega) φ
   (support_data a b s F hR hYR hAll) d (fun j:ℕ => (j.factorial:K)⁻¹) x u0 u1
 rw [sharp_flag_eq] at hh
 intro q hq
 have h:=hh q hq
 change InFlag (center a b s) q
 rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with rfl | rfl
 · simp [InFlag,center,direction,unitYZFlag] at h ⊢
   omega
 · simpa [center,InFlag,direction,unitYZFlag] using h
theorem exists_actual_agreement_certificate (φ:Polynomial K →+*Ω)
   (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
   (hR:F.degreeOf 2 ≤ s+2)
   (hYR:wt ![0,1,1,0] F ≤ b+s+3)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s+3)
   (d:ℕ) (x u0 u1:K):
   ∃ (B:Fin (d-1+1) → MvPolynomial (Fin 3) Ω)
     (c:Fin (d-1+1) → FlagDegree),
     agreementPolynomial φ F d x u0 u1=
       filteredCut (d-1) B (surfaceMap φ (polyH K F)) (surfaceMap φ (polyG K F))∧
     (∀ j,PolynomialInFlag (c j) (B j))∧
     (∀ j,c j+(d-1-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
       j.val • (⟨a,b,s+3⟩:FlagDegree)=
         center a b s+(d-1) • direction a b s)∧d-1 ≤ d:=by
 classical
 by_cases hd:2 ≤ d
 · let coeffs:ℕ → K:=fun j => (j.factorial:K)⁻¹
   let B0:=fun j => surfaceMap φ (agreementCoefficients F d coeffs x u0 u1 j)
   refine ⟨(fun j => B0 j.val),(fun j => coefficientFlag a (b+1) (s+2) d j.val),?_,?_,?_,Nat.sub_le _ _⟩
   · change surfaceMap φ (agreementNumerator F d coeffs x u0 u1)=_
     rw [surfaceMap_agreementNumerator_eq_coefficient_sum φ F d hd]
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
         intro j hj
         ring
   · intro j
     apply surfaceMap_agreementCoefficients_in_flag φ F a (b+1) (s+2)
       (by omega) (by omega) hR (by omega)
       (by omega) d hd coeffs x u0 u1 j.val
     have:=j.isLt
     omega
   · intro j
     have hj:j.val < d:=by have:=j.isLt;omega
     have h:=coefficientFlag_add_baseMonomial a (b+1) (s+2) d j.val
       (by omega) (by omega) hj
     rw [(shifted_flags a b s).1,(shifted_flags a b s).2.1,
       (shifted_flags a b s).2.2] at h
     refine h.trans ?_
     have hk:d-1+1=d:=by omega
     simpa only [hk] using class_total a b s (d-1)
 · have hd':d ≤ 1:=by omega
   have hk:d-1=0:=by omega
   refine ⟨(fun _ => agreementPolynomial φ F d x u0 u1),(fun _ => center a b s),?_,?_,?_,Nat.sub_le _ _⟩
   · rw [hk]
     unfold filteredCut
     rw [Fin.sum_univ_one]
     simp
   · intro j
     exact low_agreement_in_center φ a b s F hR hYR hAll d hd' x u0 u1
   · intro j
     have hj:j.val=0:=by have:=j.isLt;omega
     simp only [hk,hj,Nat.sub_zero]
     change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
     congr 1 <;> simp [center,direction,unitYZFlag]
end
end ProximityPrize.SubmissionLower.RCN198
end PackedLegacy_Z8

/-! Packed from ProximityPrize.SubmissionLower.BZ. -/
section PackedLegacy_BZ
namespace ProximityPrize.SubmissionLower.RCN184
open scoped Classical BigOperators WithZero
open RCN187 RCN133 RCN295
noncomputable section
variable {K L σ:Type*} [Field K] [Field L] [Fintype σ]
 [DecidableEq σ] [Algebra K L]
def coefficientEvaluation (x:σ → L) (E:Finset (σ →₀ ℕ)):
   (E → K) →ₗ[K] L where
 toFun c:=MvPolynomial.eval₂Hom (algebraMap K L) x
   (polynomialOfSupport E c)
 map_add' c d:=by
   rw [show polynomialOfSupport E (c+d)=
       polynomialOfSupport E c+polynomialOfSupport E d by
     ext m
     by_cases hm:m∈E <;>
       simp [coeff_polynomialOfSupport,hm]]
   exact map_add (MvPolynomial.eval₂Hom (algebraMap K L) x)
     (polynomialOfSupport E c) (polynomialOfSupport E d)
 map_smul' a c:=by
   rw [show polynomialOfSupport E (a • c)=
       a • polynomialOfSupport E c by
     ext m
     by_cases hm:m∈E <;>
       simp [coeff_polynomialOfSupport,hm]]
   simpa [Algebra.smul_def] using
     MvPolynomial.eval₂Hom_smul (algebraMap K L) x a
       (polynomialOfSupport E c)
def livePoleTruncation
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):σ →₀ ℕ:=
 d.filter (fun i↦x i≠0∧0 ≤ (v (x i)).log)
theorem livePoleTruncation_le
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):
   livePoleTruncation v x d ≤ d:=by
 intro i
 simp only [livePoleTruncation,Finsupp.filter_apply]
 split_ifs
 · exact le_rfl
 · exact Nat.zero_le _
theorem exponentValuationWeight_livePoleTruncation
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ):
   exponentValuationWeight v x (livePoleTruncation v x d)=
     exponentPoleWeight v x d:=by
 classical
 unfold exponentValuationWeight exponentPoleWeight poleOrder
 apply Finset.sum_congr rfl
 intro i _
 simp only [livePoleTruncation,Finsupp.filter_apply]
 by_cases hx:x i=0
 · simp [hx]
 · by_cases hlog:0 ≤ (v (x i)).log
   · rw [if_pos ⟨hx,hlog⟩,max_eq_right hlog]
   · have hle:(v (x i)).log ≤ 0:=le_of_not_ge hlog
     rw [if_neg (fun h↦hlog h.2),max_eq_left hle]
     simp
theorem livePoleTruncation_coordinate_ne_zero
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ) (i:σ)
   (hi:livePoleTruncation v x d i≠0):x i≠0:=by
 classical
 simp only [livePoleTruncation,Finsupp.filter_apply] at hi
 split at hi
 · exact ‹x i≠0∧0 ≤ (v (x i)).log›.1
 · exact (hi rfl).elim
private theorem exp_sum (s:Finset σ) (z:σ → ℤ):
   WithZero.exp (∑ i∈s,z i)=∏ i∈s,WithZero.exp (z i):=by
 classical
 induction s using Finset.induction_on with
 | empty => simp
 | @insert i s hi ih => simp [hi,ih,WithZero.exp_add]
theorem valuation_eval_monomial_one_eq_exp
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (d:σ →₀ ℕ)
   (hlive:∀ i,d i≠0 → x i≠0):
   v (MvPolynomial.eval₂Hom (algebraMap K L) x
       (MvPolynomial.monomial d (1:K)))=
     WithZero.exp (exponentValuationWeight v x d):=by
 classical
 rw [MvPolynomial.eval₂Hom_monomial,
   Finsupp.prod_fintype _ _ (fun _↦pow_zero _),map_mul,map_prod]
 simp only [map_one,one_mul,map_pow]
 rw [show WithZero.exp (exponentValuationWeight v x d)=
     ∏ i,WithZero.exp ((d i:ℤ)*(v (x i)).log) by
   unfold exponentValuationWeight
   simpa only using exp_sum (Finset.univ:Finset σ)
     (fun i↦(d i:ℤ)*(v (x i)).log)]
 apply Finset.prod_congr rfl
 intro i _
 by_cases hd:d i=0
 · simp [hd]
 · have hvx:v (x i)≠0:=
     (Valuation.ne_zero_iff v).mpr (hlive i hd)
   rw [show ((d i:ℤ)*(v (x i)).log)=
       d i • (v (x i)).log by simp,
     WithZero.exp_nsmul,WithZero.exp_log hvx]
theorem exists_mem_exponentPoleWeight_eq
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ)) (hzero:0∈E):
   ∃ d∈E,exponentPoleWeight v x d=exponentSetPoleWeight v x E:=by
 classical
 let S:=insert (0:ℤ) (E.image (exponentPoleWeight v x))
 have hS:S.Nonempty:=⟨0,Finset.mem_insert_self 0 _⟩
 have hmem:S.max' hS∈S:=Finset.max'_mem S hS
 change S.max' hS∈insert (0:ℤ) (E.image (exponentPoleWeight v x)) at hmem
 rcases Finset.mem_insert.mp hmem with hmax | hmax
 · refine ⟨0,hzero,?_⟩
   unfold exponentSetPoleWeight
   change exponentPoleWeight v x 0=S.max' hS
   simp only [exponentPoleWeight,Finsupp.zero_apply,Nat.cast_zero,
     zero_mul,Finset.sum_const_zero]
   exact hmax.symm
 · obtain ⟨d,hd,heq⟩:=Finset.mem_image.mp hmax
   refine ⟨d,hd,?_⟩
   unfold exponentSetPoleWeight
   change exponentPoleWeight v x d=S.max' hS
   exact heq
def deltaCoefficient (E:Finset (σ →₀ ℕ)) (e:E):E → K:=
 fun d↦if d=e then 1 else 0
theorem polynomialOfSupport_deltaCoefficient
   (E:Finset (σ →₀ ℕ)) (e:E):
   polynomialOfSupport E (deltaCoefficient E e:E → K)=
     MvPolynomial.monomial e.1 1:=by
 classical
 unfold polynomialOfSupport deltaCoefficient
 rw [Finset.sum_eq_single e]
 · simp
 · intro d _ hd
   simp [hd]
 · simp
theorem exists_exact_support_evaluation_of_downwardClosed
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ))
   (hdown:ExponentSetDownwardClosed E) (hzero:0∈E):
   ∃ c:E → K,
     v (coefficientEvaluation x E c)=
       WithZero.exp (exponentSetPoleWeight v x E):=by
 obtain ⟨d,hd,hmax⟩:=exists_mem_exponentPoleWeight_eq v x E hzero
 let e:σ →₀ ℕ:=livePoleTruncation v x d
 have he:e∈E:=hdown d hd e (livePoleTruncation_le v x d)
 let esub:E:=⟨e,he⟩
 refine ⟨deltaCoefficient E esub,?_⟩
 rw [coefficientEvaluation,LinearMap.coe_mk,AddHom.coe_mk,
   polynomialOfSupport_deltaCoefficient]
 rw [valuation_eval_monomial_one_eq_exp v x e
   (livePoleTruncation_coordinate_ne_zero v x d)]
 rw [exponentValuationWeight_livePoleTruncation,hmax]
theorem exponentSetPoleWeight_nonneg
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ)):
   0 ≤ exponentSetPoleWeight v x E:=by
 unfold exponentSetPoleWeight
 exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
theorem poleOrder_eq_of_valuation_eq_exp
   (v:Valuation L (WithZero (Multiplicative ℤ))) (b:L) (q:ℤ)
   (hq:0 ≤ q) (hexact:v b=WithZero.exp q):
   poleOrder v b=q:=by
 unfold poleOrder
 rw [hexact,WithZero.log_exp,max_eq_right hq]
def cancellationSubmodule
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (hcoeff:∀ a:K,v (algebraMap K L a) ≤ 1)
   (x:σ → L) (E:Finset (σ →₀ ℕ)):
   Submodule K (E → K) where
 carrier:={c | v (coefficientEvaluation x E c) <
   WithZero.exp (exponentSetPoleWeight v x E)}
 zero_mem':=by
   change v (coefficientEvaluation x E 0) <
     WithZero.exp (exponentSetPoleWeight v x E)
   rw [map_zero,map_zero]
   exact WithZero.exp_pos
 add_mem':=by
   intro c d hc hd
   change v (coefficientEvaluation x E (c+d)) <
     WithZero.exp (exponentSetPoleWeight v x E)
   change v (coefficientEvaluation x E c) <
     WithZero.exp (exponentSetPoleWeight v x E) at hc
   change v (coefficientEvaluation x E d) <
     WithZero.exp (exponentSetPoleWeight v x E) at hd
   rw [map_add]
   exact (v.map_add _ _).trans_lt (max_lt hc hd)
 smul_mem':=by
   intro a c hc
   change v (coefficientEvaluation x E (a • c)) <
     WithZero.exp (exponentSetPoleWeight v x E)
   change v (coefficientEvaluation x E c) <
     WithZero.exp (exponentSetPoleWeight v x E) at hc
   rw [map_smul,Algebra.smul_def,map_mul]
   calc
     v (algebraMap K L a)*v (coefficientEvaluation x E c) ≤
         1*v (coefficientEvaluation x E c):=
       mul_le_mul' (hcoeff a) le_rfl
     _ < WithZero.exp (exponentSetPoleWeight v x E):=by
       simpa using hc
theorem cancellationSubmodule_ne_top_of_exact
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (hcoeff:∀ a:K,v (algebraMap K L a) ≤ 1)
   (x:σ → L) (E:Finset (σ →₀ ℕ))
   (c:E → K)
   (hc:v (coefficientEvaluation x E c)=
     WithZero.exp (exponentSetPoleWeight v x E)):
   cancellationSubmodule v hcoeff x E≠⊤:=by
 intro htop
 have hmem:c∈cancellationSubmodule v hcoeff x E:=by
   rw [htop]
   trivial
 change v (coefficientEvaluation x E c) <
   WithZero.exp (exponentSetPoleWeight v x E) at hmem
 rw [hc] at hmem
 exact (lt_irrefl _ hmem)
theorem exists_simultaneous_exact_support_evaluation
   {τ:Type*} [Finite τ] [Infinite K]
   (v:τ → Valuation L (WithZero (Multiplicative ℤ)))
   (hcoeff:∀ t,∀ a:K,v t (algebraMap K L a) ≤ 1)
   (x:σ → L) (E:Finset (σ →₀ ℕ))
   (hwitness:∀ t,∃ c:E → K,
     v t (coefficientEvaluation x E c)=
       WithZero.exp (exponentSetPoleWeight (v t) x E)):
   ∃ c:E → K,
     (polynomialOfSupport E c).support ⊆ E∧
     ∀ t,v t (MvPolynomial.eval₂Hom (algebraMap K L) x
         (polynomialOfSupport E c))=
       WithZero.exp (exponentSetPoleWeight (v t) x E):=by
 let bad:τ → Submodule K (E → K):=
   fun t↦cancellationSubmodule (v t) (hcoeff t) x E
 have hproper:∀ t,bad t≠⊤:=by
   intro t
   obtain ⟨c,hc⟩:=hwitness t
   exact cancellationSubmodule_ne_top_of_exact
     (v t) (hcoeff t) x E c hc
 obtain ⟨c,hc⟩:=
   exists_avoiding_finite_proper_submodules bad hproper
 refine ⟨c,support_polynomialOfSupport_subset E c,?_⟩
 intro t
 have hlower:WithZero.exp (exponentSetPoleWeight (v t) x E) ≤
     v t (coefficientEvaluation x E c):=by
   apply le_of_not_gt
   intro hlt
   exact hc t hlt
 have hupper:v t (coefficientEvaluation x E c) ≤
     WithZero.exp (exponentSetPoleWeight (v t) x E):=by
   exact valuation_eval_le_exp_exponentSet (v t) (algebraMap K L)
     (hcoeff t) x E (polynomialOfSupport E c)
     (support_polynomialOfSupport_subset E c)
 exact le_antisymm hupper hlower
theorem exists_simultaneous_exact_support_evaluation_of_downwardClosed
   {τ:Type*} [Finite τ] [Infinite K]
   (v:τ → Valuation L (WithZero (Multiplicative ℤ)))
   (hcoeff:∀ t,∀ a:K,v t (algebraMap K L a) ≤ 1)
   (x:σ → L) (E:Finset (σ →₀ ℕ))
   (hdown:ExponentSetDownwardClosed E) (hzero:0∈E):
   ∃ c:E → K,
     (polynomialOfSupport E c).support ⊆ E∧
     ∀ t,v t (MvPolynomial.eval₂Hom (algebraMap K L) x
         (polynomialOfSupport E c))=
       WithZero.exp (exponentSetPoleWeight (v t) x E):=by
 exact exists_simultaneous_exact_support_evaluation v hcoeff x E
   (fun t↦exists_exact_support_evaluation_of_downwardClosed
     (v t) x E hdown hzero)
theorem exists_simultaneous_exact_poleOrder_of_downwardClosed
   {τ:Type*} [Finite τ] [Infinite K]
   (v:τ → Valuation L (WithZero (Multiplicative ℤ)))
   (hcoeff:∀ t,∀ a:K,v t (algebraMap K L a) ≤ 1)
   (x:σ → L) (E:Finset (σ →₀ ℕ))
   (hdown:ExponentSetDownwardClosed E) (hzero:0∈E):
   ∃ c:E → K,
     (polynomialOfSupport E c).support ⊆ E∧
     ∀ t,poleOrder (v t)
         (MvPolynomial.eval₂Hom (algebraMap K L) x
           (polynomialOfSupport E c))=
       exponentSetPoleWeight (v t) x E:=by
 obtain ⟨c,hsupport,hexact⟩:=
   exists_simultaneous_exact_support_evaluation_of_downwardClosed
     v hcoeff x E hdown hzero
 refine ⟨c,hsupport,fun t↦?_⟩
 exact poleOrder_eq_of_valuation_eq_exp (v t) _ _
   (exponentSetPoleWeight_nonneg (v t) x E) (hexact t)
end
end ProximityPrize.SubmissionLower.RCN184
end PackedLegacy_BZ

/-! Packed from ProximityPrize.SubmissionLower.GA. -/
section PackedLegacy_GA
namespace ProximityPrize.SubmissionLower.RCN296
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN295 RCN344 RCN002 RCN005 RCN006 RCN007
noncomputable section
variable {K L σ:Type} [Field K] [Field L] [Fintype σ]
 [Algebra K L] [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L]
 [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L]
 [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (Place K L):=Classical.decEq _
variable (A:Type) [CommRing A] [IsDomain A]
 [Algebra K A] [Algebra A L] [IsFractionRing A L]
 [Algebra (Polynomial K) A]
 [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
 [IsScalarTower (Polynomial K) A L]
theorem finite_model_zero_points_le_exponentSet
   (x:σ → A) (E:Finset (σ →₀ ℕ))
   (F:MvPolynomial σ K) (hFE:F.support ⊆ E)
   (hF:MvPolynomial.eval₂Hom (algebraMap K A) x F≠0)
   (q:ℕ)
   (hpole:∀ W:Finset (Place K L),
     (∑ v∈W,exponentSetPoleWeight v.val
       (fun i↦algebraMap A L (x i)) E) ≤ (q:ℤ))
   (S:Finset (A →ₐ[K] K))
   (hS:∀ ψ∈S,ψ (MvPolynomial.eval₂Hom (algebraMap K A) x F)=0):
   S.card ≤ q:=by
 classical
 have heval:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦algebraMap A L (x i)) F=
       algebraMap A L (MvPolynomial.eval₂Hom (algebraMap K A) x F):=
   (map_model_eval K L A x F).symm
 have hnonzero:MvPolynomial.eval₂Hom (algebraMap K L)
     (fun i↦algebraMap A L (x i)) F≠0:=by
   rw [heval]
   intro hz
   apply hF
   apply IsFractionRing.injective A L
   simpa only [map_zero] using hz
 let U:=S.image (modelPlace K L A)
 have hU:∀ v∈U,1 ≤ RCN026.order K L v
     (MvPolynomial.eval₂Hom (algebraMap K L)
       (fun i↦algebraMap A L (x i)) F):=by
   intro v hv
   obtain ⟨ψ,hψ,rfl⟩:=Finset.mem_image.mp hv
   rw [heval]
   exact RCN000.actual_model_zero_order_ge_one
     K A L ψ _ hF (hS ψ hψ)
 let W:=RCN026.placesFor K L _ hnonzero
 have hcount:=RCN026.finite_zero_places_le_poleMass
   K L _ hnonzero U hU
 have hsupport:=weighted_poleOrder_eval_le_exponentSet W
   (fun _↦1) (fun v↦v.val) (algebraMap K L)
   (fun v _ c↦constant_value_le_one K L v c)
   (fun i↦algebraMap A L (x i)) E F hFE
 have hcard:U.card=S.card:=
   Finset.card_image_of_injective _ (modelPlace_injective K L A)
 have hq:(S.card:ℤ) ≤ q:=by
   calc
     (S.card:ℤ)=(U.card:ℤ):=by rw [hcard]
     _ ≤ ∑ v∈W,RCN346.poleOrder K L v
         (MvPolynomial.eval₂Hom (algebraMap K L)
           (fun i↦algebraMap A L (x i)) F):=hcount
     _ ≤ ∑ v∈W,exponentSetPoleWeight v.val
         (fun i↦algebraMap A L (x i)) E:=by
       simpa only [RCN346.poleOrder,Nat.cast_one,one_mul] using hsupport
     _ ≤ (q:ℤ):=hpole W
 exact_mod_cast hq
section ActualCurve
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
theorem finite_zero_points_le_exponentSet_of_separator
   (hproj:ProjectionsFiniteSeparable K P)
   (i₀:Fin 3) (hi₀:Transcendental K (coordinate K P i₀))
   (E:Finset (Fin 3 →₀ ℕ)) (q:ℕ)
   (hpole:
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       rationalBaseAlgebra K P i₀ hi₀
     ∀ W:Finset (Place K (CoordinateField K P)),
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate K P) E) ≤ (q:ℤ))
   (F:MvPolynomial (Fin 3) K) (hFE:F.support ⊆ E) (hF:F∉P)
   (S:Finset (Fin 3 → K))
   (hSP:∀ v∈S,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hSF:∀ v∈S,MvPolynomial.aeval v F=0):
   S.card ≤ q:=by
 classical
 letI:Algebra (Polynomial K) (CoordinateRing K P):=
   quotientPolynomialAlgebra K P i₀
 letI:Algebra (Polynomial K) (CoordinateField K P):=
   polynomialBaseAlgebra K P i₀
 letI:Algebra (RatFunc K) (CoordinateField K P):=
   rationalBaseAlgebra K P i₀ hi₀
 letI:=quotientBaseScalarTower K P i₀
 letI:=polynomialBaseScalarTower K P i₀
 letI:=quotientFractionScalarTower K P i₀
 letI:=polynomialRationalScalarTower K P i₀ hi₀
 letI:=rationalBaseScalarTower K P i₀ hi₀
 letI:FiniteDimensional (RatFunc K) (CoordinateField K P):=
   (hproj i₀ hi₀).1
 letI:Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=
   (hproj i₀ hi₀).2
 let liftPoint:{v:Fin 3 → K//v∈S} →
     (CoordinateRing K P →ₐ[K] K):=
   fun v↦pointHom K P ⟨v.1,hSP v.1 v.2⟩
 have hinj:Function.Injective liftPoint:=by
   intro v w hvw
   have h:=pointHom_injective K P hvw
   apply Subtype.ext
   exact congrArg (fun z:PointOn K P↦z.val) h
 let points:=S.attach.image liftPoint
 have hpoints:∀ ψ∈points,ψ (MvPolynomial.eval₂Hom
     (algebraMap K (CoordinateRing K P)) (quotientCoordinate K P) F)=0:=by
   intro ψ hψ
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hψ
   rw [quotient_eval_eq_mk]
   exact hSF v.1 v.2
 have hpole':∀ W:Finset (Place K (CoordinateField K P)),
     (∑ v∈W,exponentSetPoleWeight v.val
       (fun i↦algebraMap (CoordinateRing K P) (CoordinateField K P)
         (quotientCoordinate K P i)) E) ≤ (q:ℤ):=by
   intro W
   simpa only [quotientCoordinate_fraction] using hpole W
 have hcount:=finite_model_zero_points_le_exponentSet
   (K:=K) (L:=CoordinateField K P) (σ:=Fin 3)
   (CoordinateRing K P) (quotientCoordinate K P) E F hFE
   (quotient_eval_ne_zero_of_not_mem K P F hF) q hpole' points hpoints
 have hcard:points.card=S.card:=by
   change (S.attach.image liftPoint).card=S.card
   rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
 rwa [hcard] at hcount
end ActualCurve
end
end ProximityPrize.SubmissionLower.RCN296
end PackedLegacy_GA

/-! Packed from ProximityPrize.SubmissionLower.O4. -/
section PackedLegacy_O4
namespace ProximityPrize.SubmissionLower.RCN273
open scoped Classical BigOperators WithZero
open RCN002 RCN007 RCN264 RCN243 RCN295 RCN296 RCN272 RCN344
noncomputable section
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
structure ResidualPoleComponentBudget
   (G T H:MvPolynomial (Fin 3) Ω)
   (E:Finset (Fin 3 →₀ ℕ)) (separator:Fin 3) (wholeCost:ℕ) where
 cost:RegularComponent Ω G T H → ℕ
 separator_transcendental:∀ C:RegularComponent Ω G T H,
   Transcendental Ω (coordinate Ω C.1 separator)
 pole_le:∀ C:RegularComponent Ω G T H,
   let htr:=separator_transcendental C
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     RCN005.rationalBaseAlgebra Ω C.1 separator htr
   ∀ W:Finset (Place Ω (CoordinateField Ω C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω C.1) E) ≤
       (cost C:ℤ)
 sum_cost_le:(∑ C:RegularComponent Ω G T H,cost C) ≤ wholeCost
def ResidualPoleComponentBudget.toResidualComponentBudget
   {G T H:MvPolynomial (Fin 3) Ω}
   {E:Finset (Fin 3 →₀ ℕ)} {separator:Fin 3} {wholeCost:ℕ}
   (B:ResidualPoleComponentBudget G T H E separator wholeCost)
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1):
   ResidualComponentBudget G T H (fun A↦A.support ⊆ E) wholeCost where
 cost:=B.cost
 zero_le:=by
   intro C A hAE hproper points hpointsP hpointsA
   exact finite_zero_points_le_exponentSet_of_separator C.1 (hproj C)
     separator (B.separator_transcendental C) E (B.cost C) (B.pole_le C)
     A hAE hproper points hpointsP hpointsA
 sum_cost_le:=B.sum_cost_le
end
end ProximityPrize.SubmissionLower.RCN273
end PackedLegacy_O4

/-! Packed from ProximityPrize.SubmissionLower.GU. -/
section PackedLegacy_GU
namespace ProximityPrize.SubmissionLower.RCN323
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN295 RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN273
noncomputable section
variable {K L σ:Type} [Field K] [Field L] [Fintype σ]
 [Algebra K L] [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L]
 [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L]
 [Algebra.IsSeparable (RatFunc K) L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (Place K L):=Classical.decEq _
theorem exponentSetPoleWeight_nonneg
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:σ → L) (E:Finset (σ →₀ ℕ)):
   0 ≤ exponentSetPoleWeight v x E:=by
 unfold exponentSetPoleWeight
 exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
theorem support_sum_le_principal_poleMass_of_exact
   (x:σ → L) (E:Finset (σ →₀ ℕ)) (b:L) (hb:b≠0)
   (hexact:∀ v:Place K L,
     RCN187.poleOrder v.val b=
       exponentSetPoleWeight v.val x E)
   (W:Finset (Place K L)):
   (∑ v∈W,exponentSetPoleWeight v.val x E) ≤
     ∑ v∈RCN026.placesFor K L b hb,
       RCN346.poleOrder K L v b:=by
 classical
 let P:=RCN026.placesFor K L b hb
 have hout:∀ v∈W,v∉P →
     exponentSetPoleWeight v.val x E=0:=by
   intro v hvW hvP
   have hpole:RCN187.poleOrder v.val b=0:=by
     by_contra hpole
     apply hvP
     apply RCN026.placesFor_covers K L b hb v
     unfold RCN026.order RCN187.poleOrder at*
     omega
   rw [←hexact v,hpole]
 calc
   (∑ v∈W,exponentSetPoleWeight v.val x E)=
       ∑ v∈W ∩ P,exponentSetPoleWeight v.val x E:=by
     symm
     apply Finset.sum_subset Finset.inter_subset_left
     intro v hvW hvnot
     apply hout v hvW
     intro hvP
     exact hvnot (Finset.mem_inter.mpr ⟨hvW,hvP⟩)
   _ ≤ ∑ v∈P,exponentSetPoleWeight v.val x E:=by
     apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
     intro v _ _
     exact exponentSetPoleWeight_nonneg v.val x E
   _=∑ v∈P,RCN346.poleOrder K L v b:=by
     apply Finset.sum_congr rfl
     intro v _
     exact (hexact v).symm
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
theorem coordinate_eval_ne_zero_of_not_mem
   (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
   (F:MvPolynomial (Fin 3) Ω) (hF:F∉P):
   MvPolynomial.eval₂Hom (algebraMap Ω (CoordinateField Ω P))
     (coordinate Ω P) F≠0:=by
 intro hz
 apply hF
 rw [←aeval_coordinate_ker Ω P]
 exact hz
structure GenericSparseBKKWitness
   (G T H:MvPolynomial (Fin 3) Ω)
   (E:Finset (Fin 3 →₀ ℕ)) (separator:Fin 3) (wholeCost:ℕ)
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1) where
 polynomial:MvPolynomial (Fin 3) Ω
 support_subset:polynomial.support ⊆ E
 proper:∀ C:RegularComponent Ω G T H,polynomial∉C.1
 cost:RegularComponent Ω G T H → ℕ
 exact_pole:∀ C:RegularComponent Ω G T H,
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
   ∀ v:Place Ω (CoordinateField Ω C.1),
     RCN187.poleOrder v.val
         (MvPolynomial.eval₂Hom
           (algebraMap Ω (CoordinateField Ω C.1))
           (coordinate Ω C.1) polynomial)=
       exponentSetPoleWeight v.val (coordinate Ω C.1) E
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
     (coordinate Ω C.1) polynomial
   let hb:b≠0:=coordinate_eval_ne_zero_of_not_mem C.1 polynomial (proper C)
   (∑ v∈RCN026.placesFor Ω (CoordinateField Ω C.1) b hb,
     RCN346.poleOrder Ω (CoordinateField Ω C.1) v b) ≤
       (cost C:ℤ)
 sum_cost_le:(∑ C:RegularComponent Ω G T H,cost C) ≤ wholeCost
def GenericSparseBKKWitness.toResidualPoleComponentBudget
   {G T H:MvPolynomial (Fin 3) Ω}
   {E:Finset (Fin 3 →₀ ℕ)} {separator:Fin 3} {wholeCost:ℕ}
   {hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator)}
   {hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1}
   (B:GenericSparseBKKWitness G T H E separator wholeCost
     hseparator hproj):
   ResidualPoleComponentBudget G T H E separator wholeCost where
 cost:=B.cost
 separator_transcendental:=hseparator
 pole_le:=by
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
   intro W
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) B.polynomial
   have hb:b≠0:=
     coordinate_eval_ne_zero_of_not_mem C.1 B.polynomial (B.proper C)
   exact (support_sum_le_principal_poleMass_of_exact
     (K:=Ω) (L:=CoordinateField Ω C.1)
     (coordinate Ω C.1) E b hb (B.exact_pole C) W).trans
       (B.cycle_le C)
 sum_cost_le:=B.sum_cost_le
end
end ProximityPrize.SubmissionLower.RCN323
end PackedLegacy_GU

/-! Packed from ProximityPrize.SubmissionLower.B4. -/
section PackedLegacy_B4
namespace ProximityPrize.SubmissionLower.RCN075
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN187 RCN133 RCN184 RCN295 RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN273 RCN323
noncomputable section
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
def componentRelevantPlaces
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (C:RegularComponent Ω G T H):
   Finset (Place Ω (CoordinateField Ω C.1)):=by
 classical
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
 exact Finset.univ.biUnion (fun i:Fin 3↦
   if hi:coordinate Ω C.1 i≠0 then
     RCN026.placesFor Ω (CoordinateField Ω C.1)
       (coordinate Ω C.1 i) hi
   else ∅)
theorem coordinate_poleOrder_eq_zero_of_not_mem_relevant
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (C:RegularComponent Ω G T H)
   (v:Place Ω (CoordinateField Ω C.1))
   (hv:v∉componentRelevantPlaces hseparator hproj C) (i:Fin 3):
   poleOrder v.val (coordinate Ω C.1 i)=0:=by
 classical
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
 by_cases hi:coordinate Ω C.1 i=0
 · simp [hi,poleOrder]
 · have hnot:v∉RCN026.placesFor Ω
       (CoordinateField Ω C.1) (coordinate Ω C.1 i) hi:=by
     intro hmem
     apply hv
     unfold componentRelevantPlaces
     apply Finset.mem_biUnion.mpr
     exact ⟨i,Finset.mem_univ _,by simp [hi,hmem]⟩
   have horder:RCN026.order Ω (CoordinateField Ω C.1) v
       (coordinate Ω C.1 i)=0:=by
     by_contra hne
     exact hnot (RCN026.placesFor_covers Ω
       (CoordinateField Ω C.1) (coordinate Ω C.1 i) hi v hne)
   unfold RCN026.order at horder
   unfold poleOrder
   have hlog:(v.val (coordinate Ω C.1 i)).log=0:=by omega
   rw [hlog]
   simp
theorem exponentSetPoleWeight_eq_zero_of_not_mem_relevant
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (E:Finset (Fin 3 →₀ ℕ))
   (C:RegularComponent Ω G T H)
   (v:Place Ω (CoordinateField Ω C.1))
   (hv:v∉componentRelevantPlaces hseparator hproj C):
   exponentSetPoleWeight v.val (coordinate Ω C.1) E=0:=by
 classical
 have hcoord:∀ i:Fin 3,
     poleOrder v.val (coordinate Ω C.1 i)=0:=
   coordinate_poleOrder_eq_zero_of_not_mem_relevant
     hseparator hproj C v hv
 unfold exponentSetPoleWeight exponentPoleWeight
 apply le_antisymm
 · apply Finset.max'_le
   intro z hz
   obtain rfl | hz:=Finset.mem_insert.mp hz
   · exact le_rfl
   · obtain ⟨d,_,rfl⟩:=Finset.mem_image.mp hz
     simp [hcoord]
 · exact Finset.le_max' _ _ (Finset.mem_insert_self (0:ℤ) _)
abbrev RelevantPlaceIndex
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1):=
 Σ C:RegularComponent Ω G T H,
   {v:Place Ω (CoordinateField Ω C.1)//
     v∈componentRelevantPlaces hseparator hproj C}
abbrev DependentGenericityIndex
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1):=
 RegularComponent Ω G T H ⊕ RelevantPlaceIndex hseparator hproj
def dependentBadSubmodule
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (E:Finset (Fin 3 →₀ ℕ)):
   DependentGenericityIndex hseparator hproj → Submodule Ω (E → Ω)
 | Sum.inl C => LinearMap.ker (coefficientEvaluation (coordinate Ω C.1) E)
 | Sum.inr ⟨C,v⟩ => cancellationSubmodule v.1.val
     (fun a↦constant_value_le_one Ω (CoordinateField Ω C.1) v.1 a)
     (coordinate Ω C.1) E
theorem dependentBadSubmodule_ne_top
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (E:Finset (Fin 3 →₀ ℕ))
   (hdown:ExponentSetDownwardClosed E) (hzero:0∈E):
   ∀ j:DependentGenericityIndex hseparator hproj,
     dependentBadSubmodule hseparator hproj E j≠⊤:=by
 classical
 intro j
 rcases j with C | ⟨C,v⟩
 · intro htop
   let e0:E:=⟨0,hzero⟩
   let c0:E → Ω:=deltaCoefficient E e0
   have hc0:c0∈dependentBadSubmodule hseparator hproj E (Sum.inl C):=by
     rw [htop]
     trivial
   have hzeroeval:coefficientEvaluation (coordinate Ω C.1) E c0=0:=by
     exact LinearMap.mem_ker.mp hc0
   have honeeval:coefficientEvaluation (coordinate Ω C.1) E c0=1:=by
     rw [coefficientEvaluation,LinearMap.coe_mk,AddHom.coe_mk,
       polynomialOfSupport_deltaCoefficient]
     simp [e0]
   rw [honeeval] at hzeroeval
   exact one_ne_zero hzeroeval
 · obtain ⟨c,hc⟩:=
     exists_exact_support_evaluation_of_downwardClosed
       (K:=Ω) (L:=CoordinateField Ω C.1) (σ:=Fin 3)
       v.1.val (coordinate Ω C.1) E hdown hzero
   exact cancellationSubmodule_ne_top_of_exact v.1.val
     (fun a↦constant_value_le_one Ω (CoordinateField Ω C.1) v.1 a)
     (coordinate Ω C.1) E c hc
structure GenericExactPolePolynomial
   (G T H:MvPolynomial (Fin 3) Ω)
   (E:Finset (Fin 3 →₀ ℕ)) (separator:Fin 3)
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1) where
 polynomial:MvPolynomial (Fin 3) Ω
 support_subset:polynomial.support ⊆ E
 proper:∀ C:RegularComponent Ω G T H,polynomial∉C.1
 exact_pole:∀ C:RegularComponent Ω G T H,
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
   ∀ v:Place Ω (CoordinateField Ω C.1),
     poleOrder v.val
         (MvPolynomial.eval₂Hom
           (algebraMap Ω (CoordinateField Ω C.1))
           (coordinate Ω C.1) polynomial)=
       exponentSetPoleWeight v.val (coordinate Ω C.1) E
theorem exists_genericExactPolePolynomial
   {G T H:MvPolynomial (Fin 3) Ω} {separator:Fin 3}
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1)
   (E:Finset (Fin 3 →₀ ℕ))
   (hdown:ExponentSetDownwardClosed E) (hzero:0∈E):
   Nonempty (GenericExactPolePolynomial G T H E separator
     hseparator hproj):=by
 classical
 let bad:=dependentBadSubmodule hseparator hproj E
 obtain ⟨c,hc⟩:=exists_avoiding_finite_proper_submodules bad
   (dependentBadSubmodule_ne_top hseparator hproj E hdown hzero)
 let B:=polynomialOfSupport E c
 have hsupport:B.support ⊆ E:=support_polynomialOfSupport_subset E c
 have hproper:∀ C:RegularComponent Ω G T H,B∉C.1:=by
   intro C hmem
   apply hc (Sum.inl C)
   change c∈LinearMap.ker
     (coefficientEvaluation (coordinate Ω C.1) E)
   rw [LinearMap.mem_ker]
   have hker:B∈RingHom.ker
       (MvPolynomial.aeval (coordinate Ω C.1)).toRingHom:=by
     rw [aeval_coordinate_ker]
     exact hmem
   have hz:=RingHom.mem_ker.mp hker
   change MvPolynomial.aeval (coordinate Ω C.1) B=0 at hz
   rw [MvPolynomial.aeval_eq_eval₂Hom] at hz
   change MvPolynomial.eval₂Hom (algebraMap Ω (CoordinateField Ω C.1))
     (coordinate Ω C.1) B=0
   exact hz
 refine ⟨⟨B,hsupport,hproper,?_⟩⟩
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
 intro v
 by_cases hv:v∈componentRelevantPlaces hseparator hproj C
 · have havoid:=hc (Sum.inr ⟨C,⟨v,hv⟩⟩)
   change ¬v.val (coefficientEvaluation (coordinate Ω C.1) E c) <
     WithZero.exp (exponentSetPoleWeight v.val (coordinate Ω C.1) E) at havoid
   have hlower:WithZero.exp
       (exponentSetPoleWeight v.val (coordinate Ω C.1) E) ≤
       v.val (coefficientEvaluation (coordinate Ω C.1) E c):=
     le_of_not_gt havoid
   have hupper:v.val (coefficientEvaluation (coordinate Ω C.1) E c) ≤
       WithZero.exp
         (exponentSetPoleWeight v.val (coordinate Ω C.1) E):=
     valuation_eval_le_exp_exponentSet v.val (algebraMap Ω _)
       (fun a↦constant_value_le_one Ω (CoordinateField Ω C.1) v a)
       (coordinate Ω C.1) E B hsupport
   exact poleOrder_eq_of_valuation_eq_exp v.val _ _
     (RCN184.exponentSetPoleWeight_nonneg
       v.val (coordinate Ω C.1) E)
     (le_antisymm hupper hlower)
 · have hweight:exponentSetPoleWeight v.val (coordinate Ω C.1) E=0:=
     exponentSetPoleWeight_eq_zero_of_not_mem_relevant
       hseparator hproj E C v hv
   have hle:poleOrder v.val
       (MvPolynomial.eval₂Hom
         (algebraMap Ω (CoordinateField Ω C.1))
         (coordinate Ω C.1) B) ≤
       exponentSetPoleWeight v.val (coordinate Ω C.1) E:=
     (poleOrder_eval_le_support v.val (algebraMap Ω _)
       (fun a↦constant_value_le_one Ω (CoordinateField Ω C.1) v a)
       (coordinate Ω C.1) B).trans
     (supportPoleWeight_le_exponentSetPoleWeight v.val
       (coordinate Ω C.1) B E hsupport)
   rw [hweight] at hle ⊢
   exact le_antisymm hle (by unfold poleOrder;exact le_max_left _ _)
def GenericExactPolePolynomial.toGenericSparseBKKWitness
   {G T H:MvPolynomial (Fin 3) Ω}
   {E:Finset (Fin 3 →₀ ℕ)} {separator:Fin 3} {wholeCost:ℕ}
   {hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 separator)}
   {hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1}
   (B:GenericExactPolePolynomial G T H E separator hseparator hproj)
   (cost:RegularComponent Ω G T H → ℕ)
   (cycle_le:∀ C:RegularComponent Ω G T H,
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
         (cost C:ℤ))
   (sum_cost_le:(∑ C:RegularComponent Ω G T H,cost C) ≤ wholeCost):
   GenericSparseBKKWitness G T H E separator wholeCost hseparator hproj where
 polynomial:=B.polynomial
 support_subset:=B.support_subset
 proper:=B.proper
 cost:=cost
 exact_pole:=B.exact_pole
 cycle_le:=cycle_le
 sum_cost_le:=sum_cost_le
end
end ProximityPrize.SubmissionLower.RCN075
end PackedLegacy_B4

/-! Packed from ProximityPrize.SubmissionLower.DO. -/
section PackedLegacy_DO
namespace ProximityPrize.SubmissionLower.RCN036
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN187 RCN184
 RCN133 RCN295
open RCN323 RCN272 RCN296
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 20000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
noncomputable def componentSeparator
   (C:RegularComponent Omega G T H):Fin 3:=
 Classical.choose
   (exists_transcendental_coordinate_of_ne_point_kernel Omega C.1
     (regularComponent_ne_point Omega G T H C))
theorem componentSeparator_transcendental
   (C:RegularComponent Omega G T H):
   Transcendental Omega
     (coordinate Omega C.1 (componentSeparator C)):=
 Classical.choose_spec
   (exists_transcendental_coordinate_of_ne_point_kernel Omega C.1
     (regularComponent_ne_point Omega G T H C))
def componentRelevantPlacesAdaptive
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1)
   (C:RegularComponent Omega G T H):
   Finset (Place Omega (CoordinateField Omega C.1)):=by
 classical
 let i0:=componentSeparator C
 let htr:=componentSeparator_transcendental C
 letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
   quotientPolynomialAlgebra Omega C.1 i0
 letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
   polynomialBaseAlgebra Omega C.1 i0
 letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
   rationalBaseAlgebra Omega C.1 i0 htr
 letI:=quotientBaseScalarTower Omega C.1 i0
 letI:=polynomialBaseScalarTower Omega C.1 i0
 letI:=quotientFractionScalarTower Omega C.1 i0
 letI:=polynomialRationalScalarTower Omega C.1 i0 htr
 letI:=rationalBaseScalarTower Omega C.1 i0 htr
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
   (hproj C i0 htr).1
 letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
   (hproj C i0 htr).2
 exact Finset.univ.biUnion (fun i:Fin 3 =>
   if hi:coordinate Omega C.1 i≠0 then
     RCN026.placesFor Omega (CoordinateField Omega C.1)
       (coordinate Omega C.1 i) hi
   else ∅)
theorem coordinate_poleOrder_eq_zero_of_not_mem_adaptive
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1)
   (C:RegularComponent Omega G T H)
   (v:Place Omega (CoordinateField Omega C.1))
   (hv:v∉componentRelevantPlacesAdaptive hproj C) (i:Fin 3):
   poleOrder v.val (coordinate Omega C.1 i)=0:=by
 classical
 let i0:=componentSeparator C
 let htr:=componentSeparator_transcendental C
 letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
   quotientPolynomialAlgebra Omega C.1 i0
 letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
   polynomialBaseAlgebra Omega C.1 i0
 letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
   rationalBaseAlgebra Omega C.1 i0 htr
 letI:=quotientBaseScalarTower Omega C.1 i0
 letI:=polynomialBaseScalarTower Omega C.1 i0
 letI:=quotientFractionScalarTower Omega C.1 i0
 letI:=polynomialRationalScalarTower Omega C.1 i0 htr
 letI:=rationalBaseScalarTower Omega C.1 i0 htr
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
   (hproj C i0 htr).1
 letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
   (hproj C i0 htr).2
 by_cases hi:coordinate Omega C.1 i=0
 · simp [hi,poleOrder]
 · have hnot:v∉RCN026.placesFor Omega
       (CoordinateField Omega C.1) (coordinate Omega C.1 i) hi:=by
     intro hmem
     apply hv
     unfold componentRelevantPlacesAdaptive
     apply Finset.mem_biUnion.mpr
     exact ⟨i,Finset.mem_univ _,by simp [hi,hmem]⟩
   have horder:RCN026.order Omega (CoordinateField Omega C.1) v
       (coordinate Omega C.1 i)=0:=by
     by_contra hne
     exact hnot (RCN026.placesFor_covers Omega
       (CoordinateField Omega C.1) (coordinate Omega C.1 i) hi v hne)
   unfold RCN026.order at horder
   unfold poleOrder
   have hlog:(v.val (coordinate Omega C.1 i)).log=0:=by omega
   rw [hlog]
   simp
theorem exponentSetPoleWeight_eq_zero_of_not_mem_adaptive
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1)
   (E:Finset (Fin 3 →₀ ℕ))
   (C:RegularComponent Omega G T H)
   (v:Place Omega (CoordinateField Omega C.1))
   (hv:v∉componentRelevantPlacesAdaptive hproj C):
   exponentSetPoleWeight v.val (coordinate Omega C.1) E=0:=by
 classical
 have hcoord:forall i:Fin 3,
     poleOrder v.val (coordinate Omega C.1 i)=0:=
   coordinate_poleOrder_eq_zero_of_not_mem_adaptive hproj C v hv
 unfold exponentSetPoleWeight exponentPoleWeight
 apply le_antisymm
 · apply Finset.max'_le
   intro z hz
   obtain rfl | hz:=Finset.mem_insert.mp hz
   · exact le_rfl
   · obtain ⟨d,_,rfl⟩:=Finset.mem_image.mp hz
     simp [hcoord]
 · exact Finset.le_max' _ _ (Finset.mem_insert_self (0:Int) _)
abbrev AdaptiveRelevantPlaceIndex
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1):=
 Sigma fun C:RegularComponent Omega G T H =>
   {v:Place Omega (CoordinateField Omega C.1)//
     v∈componentRelevantPlacesAdaptive hproj C}
abbrev AdaptiveGenericityIndex
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1):=
 RegularComponent Omega G T H ⊕ AdaptiveRelevantPlaceIndex hproj
def adaptiveBadSubmodule
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1)
   (E:Finset (Fin 3 →₀ ℕ)):
   AdaptiveGenericityIndex hproj → Submodule Omega (E → Omega)
 | Sum.inl C => LinearMap.ker (coefficientEvaluation (coordinate Omega C.1) E)
 | Sum.inr ⟨C,v⟩ => cancellationSubmodule v.1.val
     (fun a => constant_value_le_one Omega (CoordinateField Omega C.1) v.1 a)
     (coordinate Omega C.1) E
theorem adaptiveBadSubmodule_ne_top
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1)
   (E:Finset (Fin 3 →₀ ℕ))
   (hdown:ExponentSetDownwardClosed E) (hzero:0∈E):
   forall j:AdaptiveGenericityIndex hproj,
     adaptiveBadSubmodule hproj E j≠⊤:=by
 classical
 intro j
 rcases j with C | ⟨C,v⟩
 · intro htop
   let e0:E:=⟨0,hzero⟩
   let c0:E → Omega:=deltaCoefficient E e0
   have hc0:c0∈adaptiveBadSubmodule hproj E (Sum.inl C):=by
     rw [htop]
     trivial
   have hzeroeval:coefficientEvaluation (coordinate Omega C.1) E c0=0:=
     LinearMap.mem_ker.mp hc0
   have honeeval:coefficientEvaluation (coordinate Omega C.1) E c0=1:=by
     rw [coefficientEvaluation,LinearMap.coe_mk,AddHom.coe_mk,
       polynomialOfSupport_deltaCoefficient]
     simp [e0]
   rw [honeeval] at hzeroeval
   exact one_ne_zero hzeroeval
 · obtain ⟨c,hc⟩:=
     exists_exact_support_evaluation_of_downwardClosed
       (K:=Omega) (L:=CoordinateField Omega C.1) (σ:=Fin 3)
       v.1.val (coordinate Omega C.1) E hdown hzero
   exact cancellationSubmodule_ne_top_of_exact v.1.val
     (fun a => constant_value_le_one Omega (CoordinateField Omega C.1) v.1 a)
     (coordinate Omega C.1) E c hc
structure AdaptiveGenericExactPolePolynomial
   (G T H:MvPolynomial (Fin 3) Omega)
   (E:Finset (Fin 3 →₀ ℕ))
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1) where
 polynomial:MvPolynomial (Fin 3) Omega
 support_subset:polynomial.support ⊆ E
 proper:forall C:RegularComponent Omega G T H,polynomial∉C.1
 exact_pole:forall C:RegularComponent Omega G T H,
   let i0:=componentSeparator C
   let htr:=componentSeparator_transcendental C
   letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
     quotientPolynomialAlgebra Omega C.1 i0
   letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
     polynomialBaseAlgebra Omega C.1 i0
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     rationalBaseAlgebra Omega C.1 i0 htr
   letI:=quotientBaseScalarTower Omega C.1 i0
   letI:=polynomialBaseScalarTower Omega C.1 i0
   letI:=quotientFractionScalarTower Omega C.1 i0
   letI:=polynomialRationalScalarTower Omega C.1 i0 htr
   letI:=rationalBaseScalarTower Omega C.1 i0 htr
   letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
     (hproj C i0 htr).1
   letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
     (hproj C i0 htr).2
   forall v:Place Omega (CoordinateField Omega C.1),
     poleOrder v.val
         (MvPolynomial.eval₂Hom
           (algebraMap Omega (CoordinateField Omega C.1))
           (coordinate Omega C.1) polynomial)=
       exponentSetPoleWeight v.val (coordinate Omega C.1) E
theorem exists_adaptiveGenericExactPolePolynomial
   (hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1)
   (E:Finset (Fin 3 →₀ ℕ))
   (hdown:ExponentSetDownwardClosed E) (hzero:0∈E):
   Nonempty (AdaptiveGenericExactPolePolynomial G T H E hproj):=by
 classical
 let bad:=adaptiveBadSubmodule hproj E
 obtain ⟨c,hc⟩:=exists_avoiding_finite_proper_submodules bad
   (adaptiveBadSubmodule_ne_top hproj E hdown hzero)
 let B:=polynomialOfSupport E c
 have hsupport:B.support ⊆ E:=support_polynomialOfSupport_subset E c
 have hproper:forall C:RegularComponent Omega G T H,B∉C.1:=by
   intro C hmem
   apply hc (Sum.inl C)
   change c∈LinearMap.ker (coefficientEvaluation (coordinate Omega C.1) E)
   rw [LinearMap.mem_ker]
   have hker:B∈RingHom.ker
       (MvPolynomial.aeval (coordinate Omega C.1)).toRingHom:=by
     rw [aeval_coordinate_ker]
     exact hmem
   have hz:=RingHom.mem_ker.mp hker
   change MvPolynomial.aeval (coordinate Omega C.1) B=0 at hz
   rw [MvPolynomial.aeval_eq_eval₂Hom] at hz
   exact hz
 refine ⟨⟨B,hsupport,hproper,?_⟩⟩
 intro C
 dsimp only
 let i0:=componentSeparator C
 let htr:=componentSeparator_transcendental C
 letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
   quotientPolynomialAlgebra Omega C.1 i0
 letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
   polynomialBaseAlgebra Omega C.1 i0
 letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
   rationalBaseAlgebra Omega C.1 i0 htr
 letI:=quotientBaseScalarTower Omega C.1 i0
 letI:=polynomialBaseScalarTower Omega C.1 i0
 letI:=quotientFractionScalarTower Omega C.1 i0
 letI:=polynomialRationalScalarTower Omega C.1 i0 htr
 letI:=rationalBaseScalarTower Omega C.1 i0 htr
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
   (hproj C i0 htr).1
 letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
   (hproj C i0 htr).2
 intro v
 by_cases hv:v∈componentRelevantPlacesAdaptive hproj C
 · have havoid:=hc (Sum.inr ⟨C,⟨v,hv⟩⟩)
   change ¬(v.val (coefficientEvaluation (coordinate Omega C.1) E c) <
     WithZero.exp (exponentSetPoleWeight v.val (coordinate Omega C.1) E)) at havoid
   have hlower:WithZero.exp
       (exponentSetPoleWeight v.val (coordinate Omega C.1) E) ≤
       v.val (coefficientEvaluation (coordinate Omega C.1) E c):=
     le_of_not_gt havoid
   have hupper:v.val (coefficientEvaluation (coordinate Omega C.1) E c) ≤
       WithZero.exp (exponentSetPoleWeight v.val (coordinate Omega C.1) E):=
     valuation_eval_le_exp_exponentSet v.val (algebraMap Omega _)
       (fun a => constant_value_le_one Omega (CoordinateField Omega C.1) v a)
       (coordinate Omega C.1) E B hsupport
   exact poleOrder_eq_of_valuation_eq_exp v.val _ _
     (RCN184.exponentSetPoleWeight_nonneg
       v.val (coordinate Omega C.1) E)
     (le_antisymm hupper hlower)
 · have hweight:exponentSetPoleWeight v.val (coordinate Omega C.1) E=0:=
     exponentSetPoleWeight_eq_zero_of_not_mem_adaptive hproj E C v hv
   have hle:poleOrder v.val
       (MvPolynomial.eval₂Hom
         (algebraMap Omega (CoordinateField Omega C.1))
         (coordinate Omega C.1) B) ≤
       exponentSetPoleWeight v.val (coordinate Omega C.1) E:=
     (poleOrder_eval_le_support v.val (algebraMap Omega _)
       (fun a => constant_value_le_one Omega (CoordinateField Omega C.1) v a)
       (coordinate Omega C.1) B).trans
     (supportPoleWeight_le_exponentSetPoleWeight v.val
       (coordinate Omega C.1) B E hsupport)
   rw [hweight] at hle ⊢
   exact le_antisymm hle (by unfold poleOrder;exact le_max_left _ _)
def AdaptiveGenericExactPolePolynomial.toResidualComponentBudget
   {E:Finset (Fin 3 →₀ ℕ)} {wholeCost:ℕ}
   {hproj:forall C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1}
   (B:AdaptiveGenericExactPolePolynomial G T H E hproj)
   (cost:RegularComponent Omega G T H → ℕ)
   (cycle_le:forall C:RegularComponent Omega G T H,
     let i0:=componentSeparator C
     let htr:=componentSeparator_transcendental C
     letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
       quotientPolynomialAlgebra Omega C.1 i0
     letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
       polynomialBaseAlgebra Omega C.1 i0
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       rationalBaseAlgebra Omega C.1 i0 htr
     letI:=quotientBaseScalarTower Omega C.1 i0
     letI:=polynomialBaseScalarTower Omega C.1 i0
     letI:=quotientFractionScalarTower Omega C.1 i0
     letI:=polynomialRationalScalarTower Omega C.1 i0 htr
     letI:=rationalBaseScalarTower Omega C.1 i0 htr
     letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
       (hproj C i0 htr).1
     letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
       (hproj C i0 htr).2
     let b:=MvPolynomial.eval₂Hom
       (algebraMap Omega (CoordinateField Omega C.1))
       (coordinate Omega C.1) B.polynomial
     let hb:b≠0:=coordinate_eval_ne_zero_of_not_mem
       C.1 B.polynomial (B.proper C)
     (∑ v∈RCN026.placesFor Omega
         (CoordinateField Omega C.1) b hb,
       RCN346.poleOrder Omega (CoordinateField Omega C.1) v b) ≤
         (cost C:ℤ))
   (sum_cost_le:(∑ C:RegularComponent Omega G T H,cost C) ≤ wholeCost):
   ResidualComponentBudget G T H (fun A => A.support ⊆ E) wholeCost where
 cost:=cost
 sum_cost_le:=sum_cost_le
 zero_le:=by
   intro C A hAE hproper points hpointsP hpointsA
   let i0:=componentSeparator C
   let htr:=componentSeparator_transcendental C
   letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
     quotientPolynomialAlgebra Omega C.1 i0
   letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
     polynomialBaseAlgebra Omega C.1 i0
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     rationalBaseAlgebra Omega C.1 i0 htr
   letI:=quotientBaseScalarTower Omega C.1 i0
   letI:=polynomialBaseScalarTower Omega C.1 i0
   letI:=quotientFractionScalarTower Omega C.1 i0
   letI:=polynomialRationalScalarTower Omega C.1 i0 htr
   letI:=rationalBaseScalarTower Omega C.1 i0 htr
   letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
     (hproj C i0 htr).1
   letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
     (hproj C i0 htr).2
   let b:=MvPolynomial.eval₂Hom
     (algebraMap Omega (CoordinateField Omega C.1))
     (coordinate Omega C.1) B.polynomial
   have hb:b≠0:=coordinate_eval_ne_zero_of_not_mem
     C.1 B.polynomial (B.proper C)
   have hpole:forall W:Finset (Place Omega (CoordinateField Omega C.1)),
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1) E) ≤
         (cost C:ℤ):=fun W =>
     (support_sum_le_principal_poleMass_of_exact
       (K:=Omega) (L:=CoordinateField Omega C.1)
       (coordinate Omega C.1) E b hb (B.exact_pole C) W).trans
         (cycle_le C)
   exact finite_zero_points_le_exponentSet_of_separator C.1 (hproj C)
     i0 htr E (cost C) hpole A hAE hproper points hpointsP hpointsA
end
end ProximityPrize.SubmissionLower.RCN036
end PackedLegacy_DO

/-! Packed from ProximityPrize.SubmissionLower.X. -/
section PackedLegacy_X
namespace ProximityPrize.SubmissionLower.RCN341
open scoped Classical
open RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN295 RCN296
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
structure SeparableLiteralCoordinate
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime] where
 index:Fin 3
 transcendental:Transcendental Omega (coordinate Omega P index)
 finite:
   letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
     rationalBaseAlgebra Omega P index transcendental
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)
 separable:
   letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
     rationalBaseAlgebra Omega P index transcendental
   Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P)
theorem rationalBaseEmbedding_surjective_of_other_coordinates_algebraic
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (hS:Transcendental Omega (coordinate Omega P 1))
   (hY:IsAlgebraic Omega (coordinate Omega P 0))
   (hZ:IsAlgebraic Omega (coordinate Omega P 2)):
   Function.Surjective (rationalBaseEmbedding Omega P 1 hS):=by
 letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
   rationalBaseAlgebra Omega P 1 hS
 letI:IsScalarTower Omega (RatFunc Omega) (CoordinateField Omega P):=
   rationalBaseScalarTower Omega P 1 hS
 obtain ⟨y,hy⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P 0 hY
 obtain ⟨z,hz⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P 2 hZ
 have hYbot:coordinate Omega P 0∈
     (⊥:IntermediateField (RatFunc Omega) (CoordinateField Omega P)):=by
   rw [IntermediateField.mem_bot]
   refine ⟨algebraMap Omega (RatFunc Omega) y,?_⟩
   rw [←IsScalarTower.algebraMap_apply Omega (RatFunc Omega)
     (CoordinateField Omega P)]
   exact hy
 have hZbot:coordinate Omega P 2∈
     (⊥:IntermediateField (RatFunc Omega) (CoordinateField Omega P)):=by
   rw [IntermediateField.mem_bot]
   refine ⟨algebraMap Omega (RatFunc Omega) z,?_⟩
   rw [←IsScalarTower.algebraMap_apply Omega (RatFunc Omega)
     (CoordinateField Omega P)]
   exact hz
 have hadjoinBot:IntermediateField.adjoin (RatFunc Omega)
     ({coordinate Omega P 2,coordinate Omega P 0}:
       Set (CoordinateField Omega P))=⊥:=by
   rw [IntermediateField.adjoin_eq_bot_iff]
   intro x hx
   rcases hx with (rfl | hx)
   · exact hZbot
   · simpa using hx ▸ hYbot
 have hadjoinTop:IntermediateField.adjoin (RatFunc Omega)
     ({coordinate Omega P 2,coordinate Omega P 0}:
       Set (CoordinateField Omega P))=⊤:=
   adjoin_two_coordinates_over_ratFunc_eq_top Omega P 1 2 0 hS
     (by intro i;fin_cases i <;> simp)
 have htopbot:
     (⊤:IntermediateField (RatFunc Omega) (CoordinateField Omega P))=⊥:=
   hadjoinTop.symm.trans hadjoinBot
 intro x
 obtain ⟨a,ha⟩:=
   IntermediateField.mem_bot.mp (by rw [←htopbot];trivial:
     x∈(⊥:IntermediateField (RatFunc Omega) (CoordinateField Omega P)))
 refine ⟨a,?_⟩
 exact ha
theorem finite_separable_at_S_of_other_coordinates_algebraic
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (hS:Transcendental Omega (coordinate Omega P 1))
   (hY:IsAlgebraic Omega (coordinate Omega P 0))
   (hZ:IsAlgebraic Omega (coordinate Omega P 2)):
   letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
     rationalBaseAlgebra Omega P 1 hS
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)∧
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=by
 letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
   rationalBaseAlgebra Omega P 1 hS
 have hsurj:Function.Surjective
     (algebraMap (RatFunc Omega) (CoordinateField Omega P)):=by
   have hs:=
     rationalBaseEmbedding_surjective_of_other_coordinates_algebraic P hS hY hZ
   exact hs
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega P):=
   FiniteDimensional.of_surjective
     (Algebra.linearMap (RatFunc Omega) (CoordinateField Omega P)) hsurj
 have hsep:Algebra.IsSeparable
     (RatFunc Omega) (CoordinateField Omega P):=by
   constructor
   intro x
   obtain ⟨a,rfl⟩:=hsurj x
   exact isSeparable_algebraMap a
 exact ⟨inferInstance,hsep⟩
theorem finite_zero_points_le_exponentSet_of_literalCoordinate
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (D:SeparableLiteralCoordinate P)
   (E:Finset (Fin 3 →₀ ℕ)) (q:ℕ)
   (hpole:
     letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
       rationalBaseAlgebra Omega P D.index D.transcendental
     ∀ W:Finset (Place Omega (CoordinateField Omega P)),
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega P) E) ≤
         (q:ℤ))
   (F:MvPolynomial (Fin 3) Omega) (hFE:F.support ⊆ E) (hF:F∉P)
   (S:Finset (Fin 3 → Omega))
   (hSP:∀ v∈S,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hSF:∀ v∈S,MvPolynomial.aeval v F=0):
   S.card ≤ q:=by
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
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega P):=
   D.finite
 letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=
   D.separable
 let liftPoint:{v:Fin 3 → Omega//v∈S} →
     (CoordinateRing Omega P →ₐ[Omega] Omega):=
   fun v↦pointHom Omega P ⟨v.1,hSP v.1 v.2⟩
 have hinj:Function.Injective liftPoint:=by
   intro v w hvw
   have h:=pointHom_injective Omega P hvw
   apply Subtype.ext
   exact congrArg (fun z:PointOn Omega P↦z.val) h
 let points:=S.attach.image liftPoint
 have hpoints:∀ psi∈points,psi (MvPolynomial.eval₂Hom
     (algebraMap Omega (CoordinateRing Omega P))
     (quotientCoordinate Omega P) F)=0:=by
   intro psi hpsi
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hpsi
   rw [quotient_eval_eq_mk]
   exact hSF v.1 v.2
 have hpole':∀ W:Finset (Place Omega (CoordinateField Omega P)),
     (∑ v∈W,exponentSetPoleWeight v.val
       (fun i↦algebraMap (CoordinateRing Omega P) (CoordinateField Omega P)
         (quotientCoordinate Omega P i)) E) ≤ (q:ℤ):=by
   intro W
   simpa only [quotientCoordinate_fraction] using hpole W
 have hcount:=finite_model_zero_points_le_exponentSet
   (K:=Omega) (L:=CoordinateField Omega P) (σ:=Fin 3)
   (CoordinateRing Omega P) (quotientCoordinate Omega P) E F hFE
   (quotient_eval_ne_zero_of_not_mem Omega P F hF) q hpole' points hpoints
 have hcard:points.card=S.card:=by
   change (S.attach.image liftPoint).card=S.card
   rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
 rwa [hcard] at hcount
theorem exists_separableLiteralCoordinate_of_YZ_gates
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hY:∀ h:Transcendental Omega (coordinate Omega P 0),
     letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
       rationalBaseAlgebra Omega P 0 h
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)∧
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P))
   (hZ:∀ h:Transcendental Omega (coordinate Omega P 2),
     letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
       rationalBaseAlgebra Omega P 2 h
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)∧
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P)):
   Nonempty (SeparableLiteralCoordinate P):=by
 by_cases hy:Transcendental Omega (coordinate Omega P 0)
 · exact ⟨⟨0,hy,(hY hy).1,(hY hy).2⟩⟩
 by_cases hz:Transcendental Omega (coordinate Omega P 2)
 · exact ⟨⟨2,hz,(hZ hz).1,(hZ hz).2⟩⟩
 have hyalg:IsAlgebraic Omega (coordinate Omega P 0):=not_not.mp hy
 have hzalg:IsAlgebraic Omega (coordinate Omega P 2):=not_not.mp hz
 obtain ⟨i,hi⟩:=
   exists_transcendental_coordinate_of_ne_point_kernel Omega P hnonpoint
 have hi1:i=(1:Fin 3):=by
   fin_cases i <;> simp_all
 subst i
 have hs:=finite_separable_at_S_of_other_coordinates_algebraic
   P hi hyalg hzalg
 exact ⟨⟨1,hi,hs.1,hs.2⟩⟩
end
end ProximityPrize.SubmissionLower.RCN341
end PackedLegacy_X

/-! Packed from ProximityPrize.SubmissionLower.P. -/
section PackedLegacy_P
namespace ProximityPrize.SubmissionLower.RCN114
open scoped Classical BigOperators WithZero
open RCN187 RCN295 RCN095
noncomputable section
theorem exponent_weight_le_flag_bound
   (p:FlagDegree) (d:Fin 3 →₀ ℕ) (q:Fin 3 → ℤ)
   (hd:InFlag p d) (hq:∀ i,0 ≤ q i):
   (∑ i,(d i:ℤ)*q i) ≤
     (p.zOnly:ℤ)*q 2+
       (p.yz:ℤ)*max (q 0) (q 2)+
       (p.all:ℤ)*max (q 1) (max (q 0) (q 2)):=by
 let m₁:ℤ:=max (q 0) (q 2)
 let m₂:ℤ:=max (q 1) m₁
 have hq0m₁:q 0 ≤ m₁:=le_max_left _ _
 have hq2m₁:q 2 ≤ m₁:=le_max_right _ _
 have hq1m₂:q 1 ≤ m₂:=le_max_left _ _
 have hm₁m₂:m₁ ≤ m₂:=le_max_right _ _
 have hreplace0:(d 0:ℤ)*q 0 ≤ (d 0:ℤ)*m₁:=
   mul_le_mul_of_nonneg_left hq0m₁ (by positivity)
 have hreplace1:(d 1:ℤ)*q 1 ≤ (d 1:ℤ)*m₂:=
   mul_le_mul_of_nonneg_left hq1m₂ (by positivity)
 have htotal:((d 0+d 1+d 2:ℕ):ℤ) ≤
     ((p.zOnly+p.yz+p.all:ℕ):ℤ):=by
   exact_mod_cast hd.2.2
 have hys:((d 0+d 1:ℕ):ℤ) ≤
     ((p.yz+p.all:ℕ):ℤ):=by
   exact_mod_cast hd.2.1
 have hs:(d 1:ℤ) ≤ (p.all:ℤ):=by
   exact_mod_cast hd.1
 have hdiff₁:0 ≤ m₁-q 2:=sub_nonneg.mpr hq2m₁
 have hdiff₂:0 ≤ m₂-m₁:=sub_nonneg.mpr hm₁m₂
 have hcap:
     ((d 0+d 1+d 2:ℕ):ℤ)*q 2+
         ((d 0+d 1:ℕ):ℤ)*(m₁-q 2)+
         (d 1:ℤ)*(m₂-m₁) ≤
       ((p.zOnly+p.yz+p.all:ℕ):ℤ)*q 2+
         ((p.yz+p.all:ℕ):ℤ)*(m₁-q 2)+
         (p.all:ℤ)*(m₂-m₁):=by
   exact add_le_add
     (add_le_add (mul_le_mul_of_nonneg_right htotal (hq 2))
       (mul_le_mul_of_nonneg_right hys hdiff₁))
     (mul_le_mul_of_nonneg_right hs hdiff₂)
 calc
   (∑ i,(d i:ℤ)*q i)=
       (d 0:ℤ)*q 0+(d 1:ℤ)*q 1+(d 2:ℤ)*q 2:=by
     simp [Fin.sum_univ_three]
   _ ≤ (d 0:ℤ)*m₁+(d 1:ℤ)*m₂+(d 2:ℤ)*q 2:=
     add_le_add (add_le_add hreplace0 hreplace1) le_rfl
   _=((d 0+d 1+d 2:ℕ):ℤ)*q 2+
         ((d 0+d 1:ℕ):ℤ)*(m₁-q 2)+
         (d 1:ℤ)*(m₂-m₁):=by
     push_cast
     ring
   _ ≤ ((p.zOnly+p.yz+p.all:ℕ):ℤ)*q 2+
         ((p.yz+p.all:ℕ):ℤ)*(m₁-q 2)+
         (p.all:ℤ)*(m₂-m₁):=hcap
   _=(p.zOnly:ℤ)*q 2+(p.yz:ℤ)*m₁+
         (p.all:ℤ)*m₂:=by
     push_cast
     ring
   _=_:=rfl
variable {L:Type*} [Field L]
theorem exponentSetPoleWeight_flagSupport_le
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L)
   (p:FlagDegree):
   exponentSetPoleWeight v x (flagSupport p) ≤
     (p.zOnly:ℤ)*poleOrder v (x 2)+
       (p.yz:ℤ)*max (poleOrder v (x 0)) (poleOrder v (x 2))+
       (p.all:ℤ)*max (poleOrder v (x 1))
         (max (poleOrder v (x 0)) (poleOrder v (x 2))):=by
 classical
 unfold exponentSetPoleWeight
 apply Finset.max'_le
 intro z hz
 obtain rfl | hz:=Finset.mem_insert.mp hz
 · have h0:∀ i:Fin 3,0 ≤ poleOrder v (x i):=fun i↦by
     unfold poleOrder
     exact le_max_left _ _
   exact add_nonneg
     (add_nonneg (mul_nonneg (by positivity) (h0 2))
       (mul_nonneg (by positivity)
         ((h0 0).trans (le_max_left _ _))))
     (mul_nonneg (by positivity)
       ((h0 1).trans (le_max_left _ _)))
 · obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp hz
   exact exponent_weight_le_flag_bound p d (fun i↦poleOrder v (x i))
     ((mem_flagSupport_iff p d).mp hd)
     (fun i↦by unfold poleOrder;exact le_max_left _ _)
theorem exponentPoleWeight_single
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L)
   (i:Fin 3):
   exponentPoleWeight v x (Finsupp.single i 1)=poleOrder v (x i):=by
 classical
 fin_cases i <;> simp [exponentPoleWeight,Fin.sum_univ_three]
private theorem poleOrder_le_support_of_mem
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L)
   (p:FlagDegree) (i:Fin 3)
   (hi:Finsupp.single i 1∈flagSupport p):
   poleOrder v (x i) ≤ exponentSetPoleWeight v x (flagSupport p):=by
 rw [←exponentPoleWeight_single v x i]
 unfold exponentSetPoleWeight
 apply Finset.le_max'
 exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
   ⟨Finsupp.single i 1,hi,rfl⟩)
theorem exponentSetPoleWeight_unitZ
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L):
   exponentSetPoleWeight v x (flagSupport unitZFlag)=poleOrder v (x 2):=by
 apply le_antisymm
 · simpa [unitZFlag] using exponentSetPoleWeight_flagSupport_le v x unitZFlag
 · apply poleOrder_le_support_of_mem v x unitZFlag 2
   rw [mem_flagSupport_iff]
   simp [InFlag,unitZFlag]
theorem exponentSetPoleWeight_unitYZ
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L):
   exponentSetPoleWeight v x (flagSupport unitYZFlag)=
     max (poleOrder v (x 0)) (poleOrder v (x 2)):=by
 apply le_antisymm
 · simpa [unitYZFlag] using exponentSetPoleWeight_flagSupport_le v x unitYZFlag
 · apply max_le
   · apply poleOrder_le_support_of_mem v x unitYZFlag 0
     rw [mem_flagSupport_iff]
     simp [InFlag,unitYZFlag]
   · apply poleOrder_le_support_of_mem v x unitYZFlag 2
     rw [mem_flagSupport_iff]
     simp [InFlag,unitYZFlag]
theorem exponentSetPoleWeight_unitAll
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L):
   exponentSetPoleWeight v x (flagSupport unitAllFlag)=
     max (poleOrder v (x 1))
       (max (poleOrder v (x 0)) (poleOrder v (x 2))):=by
 apply le_antisymm
 · simpa [unitAllFlag] using exponentSetPoleWeight_flagSupport_le v x unitAllFlag
 · apply max_le
   · apply poleOrder_le_support_of_mem v x unitAllFlag 1
     rw [mem_flagSupport_iff]
     simp [InFlag,unitAllFlag]
   · apply max_le
     · apply poleOrder_le_support_of_mem v x unitAllFlag 0
       rw [mem_flagSupport_iff]
       simp [InFlag,unitAllFlag]
     · apply poleOrder_le_support_of_mem v x unitAllFlag 2
       rw [mem_flagSupport_iff]
       simp [InFlag,unitAllFlag]
theorem exponentSetPoleWeight_flagSupport_le_three
   (v:Valuation L (WithZero (Multiplicative ℤ))) (x:Fin 3 → L)
   (p:FlagDegree):
   exponentSetPoleWeight v x (flagSupport p) ≤
     (p.zOnly:ℤ)*exponentSetPoleWeight v x (flagSupport unitZFlag)+
     (p.yz:ℤ)*exponentSetPoleWeight v x (flagSupport unitYZFlag)+
     (p.all:ℤ)*exponentSetPoleWeight v x (flagSupport unitAllFlag):=by
 rw [exponentSetPoleWeight_unitZ,exponentSetPoleWeight_unitYZ,
   exponentSetPoleWeight_unitAll]
 exact exponentSetPoleWeight_flagSupport_le v x p
end
end ProximityPrize.SubmissionLower.RCN114
end PackedLegacy_P

/-! Packed from ProximityPrize.SubmissionLower.Q8. -/
section PackedLegacy_Q8
namespace ProximityPrize.SubmissionLower.RCN340
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN002 RCN005
 RCN006
open RCN344 RCN264 RCN095 RCN114 RCN295 RCN341 RCN237 RCN165
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 20000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def LiteralSupportPoleBound
   {P:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime]
   (D:SeparableLiteralCoordinate P)
   (E:Finset (Fin 3 →₀ ℕ)) (cost:ℕ):Prop:=
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
 letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega P):=
   D.finite
 letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=
   D.separable
 ∀ W:Finset (Place Omega (CoordinateField Omega P)),
   (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega P) E) ≤
     (cost:ℤ)
structure AdaptiveUnitPoleBudget
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (p q:FlagDegree) where
 zCost:RegularComponent Omega G T H → ℕ
 yzCost:RegularComponent Omega G T H → ℕ
 allCost:RegularComponent Omega G T H → ℕ
 zPole:∀ C:RegularComponent Omega G T H,
   LiteralSupportPoleBound (base C) (flagSupport unitZFlag) (zCost C)
 yzPole:∀ C:RegularComponent Omega G T H,
   LiteralSupportPoleBound (base C) (flagSupport unitYZFlag) (yzCost C)
 allPole:∀ C:RegularComponent Omega G T H,
   LiteralSupportPoleBound (base C) (flagSupport unitAllFlag) (allCost C)
 sum_zCost_le:(∑ C:RegularComponent Omega G T H,zCost C) ≤
   flagMixed p q unitZFlag
 sum_yzCost_le:(∑ C:RegularComponent Omega G T H,yzCost C) ≤
   flagMixed p q unitYZFlag
 sum_allCost_le:(∑ C:RegularComponent Omega G T H,allCost C) ≤
   flagMixed p q unitAllFlag
def AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (U:AdaptiveUnitPoleBudget base p q):
   PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q where
 zCost:=U.zCost
 yzCost:=U.yzCost
 allCost:=U.allCost
 sum_zCost_le:=U.sum_zCost_le
 sum_yzCost_le:=U.sum_yzCost_le
 sum_allCost_le:=U.sum_allCost_le
 primeBudget:=by
   intro C
   refine ⟨?_⟩
   intro r A hA hproper points hpointsP hpointsA
   let D:=base C
   let i0:=D.index
   let htr:=D.transcendental
   letI:Algebra (Polynomial Omega) (CoordinateRing Omega C.1):=
     quotientPolynomialAlgebra Omega C.1 i0
   letI:Algebra (Polynomial Omega) (CoordinateField Omega C.1):=
     polynomialBaseAlgebra Omega C.1 i0
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     rationalBaseAlgebra Omega C.1 i0 htr
   letI:=quotientBaseScalarTower Omega C.1 i0
   letI:=polynomialBaseScalarTower Omega C.1 i0
   letI:=quotientFractionScalarTower Omega C.1 i0
   letI:=polynomialRationalScalarTower Omega C.1 i0 htr
   letI:=rationalBaseScalarTower Omega C.1 i0 htr
   letI:FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=
     D.finite
   letI:Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1):=
     D.separable
   have hz:=U.zPole C
   have hyz:=U.yzPole C
   have hall:=U.allPole C
   change ∀ W:Finset (Place Omega (CoordinateField Omega C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitZFlag)) ≤ (U.zCost C:ℤ) at hz
   change ∀ W:Finset (Place Omega (CoordinateField Omega C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitYZFlag)) ≤ (U.yzCost C:ℤ) at hyz
   change ∀ W:Finset (Place Omega (CoordinateField Omega C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
       (flagSupport unitAllFlag)) ≤ (U.allCost C:ℤ) at hall
   have hpole:∀ W:Finset (Place Omega (CoordinateField Omega C.1)),
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
         (flagSupport r)) ≤
       ((r.zOnly*U.zCost C+r.yz*U.yzCost C+
         r.all*U.allCost C:ℕ):ℤ):=by
     intro W
     calc
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
           (flagSupport r)) ≤
           ∑ v∈W,
             ((r.zOnly:ℤ)*exponentSetPoleWeight v.val
                 (coordinate Omega C.1) (flagSupport unitZFlag)+
              (r.yz:ℤ)*exponentSetPoleWeight v.val
                 (coordinate Omega C.1) (flagSupport unitYZFlag)+
              (r.all:ℤ)*exponentSetPoleWeight v.val
                 (coordinate Omega C.1) (flagSupport unitAllFlag)):=by
         apply Finset.sum_le_sum
         intro v _
         exact exponentSetPoleWeight_flagSupport_le_three v.val
           (coordinate Omega C.1) r
       _=(r.zOnly:ℤ)*
             (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
               (flagSupport unitZFlag))+
           (r.yz:ℤ)*
             (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
               (flagSupport unitYZFlag))+
           (r.all:ℤ)*
             (∑ v∈W,exponentSetPoleWeight v.val (coordinate Omega C.1)
               (flagSupport unitAllFlag)):=by
         simp only [Finset.sum_add_distrib,Finset.mul_sum]
       _ ≤ (r.zOnly:ℤ)*(U.zCost C:ℤ)+
           (r.yz:ℤ)*(U.yzCost C:ℤ)+
           (r.all:ℤ)*(U.allCost C:ℤ):=by
         exact add_le_add
           (add_le_add
             (mul_le_mul_of_nonneg_left (hz W) (by positivity))
             (mul_le_mul_of_nonneg_left (hyz W) (by positivity)))
           (mul_le_mul_of_nonneg_left (hall W) (by positivity))
       _=((r.zOnly*U.zCost C+r.yz*U.yzCost C+
           r.all*U.allCost C:ℕ):ℤ):=by
         push_cast
         ring
   exact finite_zero_points_le_exponentSet_of_literalCoordinate C.1 D
     (flagSupport r)
     (r.zOnly*U.zCost C+r.yz*U.yzCost C+r.all*U.allCost C)
     hpole A ((support_subset_flagSupport_iff r A).2 hA) hproper
     points hpointsP hpointsA
end
end ProximityPrize.SubmissionLower.RCN340
end PackedLegacy_Q8

/-! Packed from ProximityPrize.SubmissionLower.G. -/
section PackedLegacy_G
namespace ProximityPrize.SubmissionLower.RCN022
open scoped Classical
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
def elementEmbedding (s:L) (hs:Transcendental K s):RatFunc K →ₐ[K] L:=
 RatFunc.liftAlgHom (Polynomial.aeval s)
   (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
     (Polynomial.aeval s).toRingHom (transcendental_iff_injective.mp hs))
theorem elementEmbedding_variable (s:L) (hs:Transcendental K s):
   elementEmbedding K L s hs
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=s:=by
 change RatFunc.liftAlgHom (Polynomial.aeval s) _
   (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=s
 calc
   _=Polynomial.aeval s Polynomial.X:=
     RatFunc.liftRingHom_algebraMap _ _ Polynomial.X
   _=s:=Polynomial.aeval_X s
theorem elementEmbedding_eq_adjoin_comp (s:L) (hs:Transcendental K s):
   elementEmbedding K L s hs=
     (IntermediateField.adjoin K ({s}:Set L)).val.comp
       (RatFunc.algEquivOfTranscendental s hs).toAlgHom:=by
 apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
 ext
 change elementEmbedding K L s hs
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=
   ((RatFunc.algEquivOfTranscendental s hs
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X):
       IntermediateField.adjoin K ({s}:Set L)):L)
 rw [elementEmbedding_variable]
 simp
theorem finiteDimensional_elementEmbedding
   (base:RatFunc K →ₐ[K] L)
   (hfinite:
     letI:Algebra (RatFunc K) L:=base.toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (s:L) (hs:Transcendental K s):
   letI:Algebra (RatFunc K) L:=
     (elementEmbedding K L s hs).toRingHom.toAlgebra
   FiniteDimensional (RatFunc K) L:=by
 letI:Algebra (RatFunc K) L:=base.toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun c↦(base.commutes c).symm
 letI:FiniteDimensional (RatFunc K) L:=hfinite
 have hadjoin:FiniteDimensional (IntermediateField.adjoin K ({s}:Set L)) L:=
   FunctionField.finiteDimensional_of_adjoin_transcendental hs
 let e:RatFunc K ≃ₐ[K] (IntermediateField.adjoin K ({s}:Set L)):=
   RatFunc.algEquivOfTranscendental s hs
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L s hs).toRingHom.toAlgebra
 have hsmul:∀ (c:IntermediateField.adjoin K ({s}:Set L)) (x:L),
     e.symm c • x=c • x:=by
   intro c x
   rw [Algebra.smul_def,Algebra.smul_def]
   change elementEmbedding K L s hs (e.symm c)*x=(c:L)*x
   rw [elementEmbedding_eq_adjoin_comp]
   simp [e]
 let b:=Module.finBasis (IntermediateField.adjoin K ({s}:Set L)) L
 exact (b.mapCoeffs e.symm hsmul).finiteDimensional_of_finite
end
end ProximityPrize.SubmissionLower.RCN022
end PackedLegacy_G

/-! Packed from ProximityPrize.SubmissionLower.G7. -/
section PackedLegacy_G7
namespace ProximityPrize.SubmissionLower.RCN369
open scoped Classical
open KaehlerDifferential
noncomputable section
set_option maxHeartbeats 2000000
section RatFuncDifferential
variable (K:Type*) [Field K]
theorem span_singleton_D_ratFunc_X:
   Submodule.span (RatFunc K)
       ({D K (RatFunc K)
         (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)}:
         Set Ω[RatFunc K⁄K])=⊤:=by
 have hall:=span_range_map_derivation_of_isLocalization
   K (Polynomial K) (RatFunc K) (nonZeroDivisors (Polynomial K))
 apply top_unique
 rw [←hall]
 apply Submodule.span_le.mpr
 rintro x ⟨P,rfl⟩
 change map K K (Polynomial K) (RatFunc K) (D K (Polynomial K) P)∈_
 rw [polynomial_D_apply,LinearMap.map_smul_of_tower,map_D]
 exact Submodule.smul_of_tower_mem _ _
   (Submodule.subset_span (Set.mem_singleton _))
end RatFuncDifferential
section ProjectionCriterion
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
def parameterDifferential (embedding:RatFunc K →ₐ[K] L):Ω[L⁄K]:=
 D K L (embedding (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))
theorem isSeparable_iff_span_parameterDifferential
   (embedding:RatFunc K →ₐ[K] L):
   letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
   FiniteDimensional (RatFunc K) L →
     (Algebra.IsSeparable (RatFunc K) L ↔
       Submodule.span L ({parameterDifferential K L embedding}:Set Ω[L⁄K])=⊤):=by
 letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun c↦(embedding.commutes c).symm
 intro hfinite
 letI:FiniteDimensional (RatFunc K) L:=hfinite
 constructor
 · intro hsep
   letI:Algebra.IsSeparable (RatFunc K) L:=hsep
   letI:Algebra.FormallyUnramified (RatFunc K) L:=
     Algebra.FormallyUnramified.of_isSeparable (RatFunc K) L
   have htarget:Subsingleton Ω[L⁄RatFunc K]:=inferInstance
   have hsurj:Function.Surjective (mapBaseChange K (RatFunc K) L):=by
     rw [←LinearMap.range_eq_top,range_mapBaseChange]
     apply top_unique
     intro x _
     change map K (RatFunc K) L L x=0
     exact Subsingleton.elim _ _
   have hsource:=span_singleton_D_ratFunc_X K
   rw [←LinearMap.range_eq_top] at hsurj
   apply top_unique
   rw [←hsurj]
   rintro x ⟨x,rfl⟩
   induction x with
   | zero => simp
   | add x y hx hy =>
       rw [map_add]
       exact Submodule.add_mem _ hx hy
   | tmul l ω =>
       have hω:ω∈Submodule.span (RatFunc K)
           ({D K (RatFunc K)
             (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)}:
             Set Ω[RatFunc K⁄K]):=by
         rw [hsource]
         trivial
       obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hω
       rw [TensorProduct.tmul_smul]
       change mapBaseChange K (RatFunc K) L
         ((algebraMap (RatFunc K) L a*l) ⊗ₜ
           D K (RatFunc K)
             (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))∈_
       rw [mapBaseChange_tmul,map_D]
       change (algebraMap (RatFunc K) L a*l) •
         parameterDifferential K L embedding∈
           Submodule.span L
             ({parameterDifferential K L embedding}:Set Ω[L⁄K])
       exact Submodule.smul_mem _ _
         (Submodule.subset_span (Set.mem_singleton _))
 · intro hspan
   have hrange:LinearMap.range (mapBaseChange K (RatFunc K) L)=⊤:=by
     apply top_unique
     rw [←hspan]
     apply Submodule.span_le.mpr
     intro η hη
     rw [Set.mem_singleton_iff.mp hη]
     refine ⟨1 ⊗ₜ D K (RatFunc K)
         (algebraMap (Polynomial K) (RatFunc K) Polynomial.X),?_⟩
     rw [mapBaseChange_tmul,one_smul,map_D]
     rfl
   have hker:LinearMap.ker (map K (RatFunc K) L L)=⊤:=by
     rw [←range_mapBaseChange]
     exact hrange
   have hzero:map K (RatFunc K) L L=0:=by
     apply LinearMap.ker_eq_top.mp hker
   have hsub:Subsingleton Ω[L⁄RatFunc K]:=by
     constructor
     intro x y
     obtain ⟨x,rfl⟩:=map_surjective K (RatFunc K) L x
     obtain ⟨y,rfl⟩:=map_surjective K (RatFunc K) L y
     rw [hzero,LinearMap.zero_apply,LinearMap.zero_apply]
   letI:Subsingleton Ω[L⁄RatFunc K]:=hsub
   letI:Algebra.FormallyUnramified (RatFunc K) L:=⟨inferInstance⟩
   exact Algebra.FormallyUnramified.isSeparable (RatFunc K) L
theorem isSeparable_shear_of_not_isSeparable
   (embeddingR embeddingZ embeddingS:RatFunc K →ₐ[K] L)
   (hfiniteR:
     letI:Algebra (RatFunc K) L:=embeddingR.toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hfiniteZ:
     letI:Algebra (RatFunc K) L:=embeddingZ.toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hfiniteS:
     letI:Algebra (RatFunc K) L:=embeddingS.toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hnotsepR:
     letI:Algebra (RatFunc K) L:=embeddingR.toRingHom.toAlgebra
     ¬ Algebra.IsSeparable (RatFunc K) L)
   (hsepZ:
     letI:Algebra (RatFunc K) L:=embeddingZ.toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc K) L)
   (hshear:
     embeddingS (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=
       embeddingR (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)+
         embeddingZ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)):
   letI:Algebra (RatFunc K) L:=embeddingS.toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc K) L:=by
 let dR:=parameterDifferential K L embeddingR
 let dZ:=parameterDifferential K L embeddingZ
 let dS:=parameterDifferential K L embeddingS
 have hcriterionR:=
   isSeparable_iff_span_parameterDifferential K L embeddingR hfiniteR
 have hcriterionZ:=
   isSeparable_iff_span_parameterDifferential K L embeddingZ hfiniteZ
 have hcriterionS:=
   isSeparable_iff_span_parameterDifferential K L embeddingS hfiniteS
 have hspanZ:Submodule.span L ({dZ}:Set Ω[L⁄K])=⊤:=
   hcriterionZ.mp hsepZ
 have hspanR_ne:Submodule.span L ({dR}:Set Ω[L⁄K])≠⊤:=by
   intro htop
   exact hnotsepR (hcriterionR.mpr htop)
 have hdR:dR=0:=by
   by_contra hdR0
   apply hspanR_ne
   apply top_unique
   rw [←hspanZ]
   apply Submodule.span_le.mpr
   intro x hx
   rw [Set.mem_singleton_iff.mp hx]
   have hdR_mem:dR∈Submodule.span L ({dZ}:Set Ω[L⁄K]):=by
     rw [hspanZ]
     trivial
   obtain ⟨b,hb⟩:=Submodule.mem_span_singleton.mp hdR_mem
   have hb0:b≠0:=by
     intro hzero
     apply hdR0
     rw [←hb,hzero,zero_smul]
   apply Submodule.mem_span_singleton.mpr
   refine ⟨b⁻¹,?_⟩
   rw [←hb,smul_smul,inv_mul_cancel₀ hb0,one_smul]
 apply hcriterionS.mpr
 have hdS:dS=dR+dZ:=by
   unfold dS dR dZ parameterDifferential
   rw [hshear,map_add]
 change Submodule.span L ({dS}:Set Ω[L⁄K])=⊤
 rw [hdS,hdR,zero_add]
 exact hspanZ
end ProjectionCriterion
end
end ProximityPrize.SubmissionLower.RCN369
end PackedLegacy_G7

/-! Packed from ProximityPrize.SubmissionLower.X1. -/
section PackedLegacy_X1
namespace ProximityPrize.SubmissionLower.RCN370
open scoped Classical
open KaehlerDifferential RCN369
noncomputable section
set_option maxHeartbeats 2000000
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
theorem eq_algebraMap_of_isAlgebraic [IsAlgClosed K]
   (s:L) (hs:IsAlgebraic K s):
   ∃ c:K,algebraMap K L c=s:=by
 let S:IntermediateField K L:=IntermediateField.adjoin K {s}
 letI:Algebra.IsAlgebraic K S:=
   IntermediateField.isAlgebraic_adjoin_simple hs.isIntegral
 obtain ⟨c,hc⟩:=
   (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=K) (K:=S)).2
     (⟨s,IntermediateField.mem_adjoin_simple_self K s⟩:S)
 refine ⟨c,?_⟩
 have hcast:=congrArg (algebraMap S L) hc
 simpa only [IntermediateField.algebraMap_apply,
   IntermediateField.coe_algebraMap_apply] using hcast
theorem transcendental_add_of_not_isSeparable_isSeparable [IsAlgClosed K]
   (embeddingR embeddingZ:RatFunc K →ₐ[K] L)
   (hfiniteR:
     letI:Algebra (RatFunc K) L:=embeddingR.toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hfiniteZ:
     letI:Algebra (RatFunc K) L:=embeddingZ.toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hnotsepR:
     letI:Algebra (RatFunc K) L:=embeddingR.toRingHom.toAlgebra
     ¬ Algebra.IsSeparable (RatFunc K) L)
   (hsepZ:
     letI:Algebra (RatFunc K) L:=embeddingZ.toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc K) L):
   Transcendental K
     (embeddingR (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)+
       embeddingZ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)):=by
 let dR:=parameterDifferential K L embeddingR
 let dZ:=parameterDifferential K L embeddingZ
 have hcriterionR:=
   isSeparable_iff_span_parameterDifferential K L embeddingR hfiniteR
 have hcriterionZ:=
   isSeparable_iff_span_parameterDifferential K L embeddingZ hfiniteZ
 have hspanR_ne:Submodule.span L ({dR}:Set Ω[L⁄K])≠⊤:=by
   intro htop
   exact hnotsepR (hcriterionR.mpr htop)
 have hspanZ:Submodule.span L ({dZ}:Set Ω[L⁄K])=⊤:=
   hcriterionZ.mp hsepZ
 have hdR:dR=0:=by
   by_contra hdR0
   apply hspanR_ne
   apply top_unique
   rw [←hspanZ]
   apply Submodule.span_le.mpr
   intro x hx
   rw [Set.mem_singleton_iff.mp hx]
   have hdR_mem:dR∈Submodule.span L ({dZ}:Set Ω[L⁄K]):=by
     rw [hspanZ]
     trivial
   obtain ⟨b,hb⟩:=Submodule.mem_span_singleton.mp hdR_mem
   have hb0:b≠0:=by
     intro hzero
     apply hdR0
     rw [←hb,hzero,zero_smul]
   apply Submodule.mem_span_singleton.mpr
   refine ⟨b⁻¹,?_⟩
   rw [←hb,smul_smul,inv_mul_cancel₀ hb0,one_smul]
 have hdZ:dZ≠0:=by
   intro hdZ
   apply hspanR_ne
   simpa only [hdR,hdZ] using hspanZ
 show ¬ IsAlgebraic K _
 intro halg
 obtain ⟨c,hc⟩:=eq_algebraMap_of_isAlgebraic K L _ halg
 apply hdZ
 have hD:D K L
     (embeddingR (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)+
       embeddingZ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))=0:=by
   rw [←hc]
   exact (D K L).map_algebraMap c
 have hD':parameterDifferential K L embeddingR+
     parameterDifferential K L embeddingZ=0:=by
   change D K L
       (embeddingR (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))+
     D K L
       (embeddingZ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))=0
   simpa only [map_add] using hD
 unfold dR at hdR
 unfold dZ
 rw [hdR,zero_add] at hD'
 exact hD'
end
end ProximityPrize.SubmissionLower.RCN370
end PackedLegacy_X1

/-! Packed from ProximityPrize.SubmissionLower.R7. -/
section PackedLegacy_R7
namespace ProximityPrize.SubmissionLower.RCN351
open scoped Classical TensorProduct
open Polynomial KaehlerDifferential RCN369 RCN370 RCN022
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
theorem formallyEtale_of_finite_isSeparable
   (F E:Type*) [Field F] [Field E] [Algebra F E]
   [FiniteDimensional F E] [Algebra.IsSeparable F E]:
   Algebra.FormallyEtale F E:=by
 have:=Algebra.FormallyUnramified.of_isSeparable F E
 have:=Algebra.FormallyUnramified.finite_of_free (R:=F) (S:=E)
 refine Algebra.FormallyEtale.iff_comp_bijective.mpr fun B _ _ I h↦?_
 refine ⟨Algebra.FormallyUnramified.iff_comp_injective_of_small.mp
   (Algebra.FormallyUnramified.of_isSeparable F E) I h,?_⟩
 intro f
 let pb:=Field.powerBasisOfFiniteOfSeparable F E
 obtain ⟨x,hx⟩:=Ideal.Quotient.mk_surjective (f pb.gen)
 have helper:∀ x,IsScalarTower.toAlgHom F B
     (HasQuotient.Quotient B I) x=
     Ideal.Quotient.mk I x:=fun _↦rfl
 have hx':Ideal.Quotient.mk I (aeval x (minpoly F pb.gen))=0:=by
   rw [←helper, ←aeval_algHom_apply,helper,hx,aeval_algHom_apply,
     minpoly.aeval,map_zero]
 obtain ⟨u,hu⟩:∃ u,
     (aeval x) (derivative (minpoly F pb.gen))*u+1∈I:=by
   have hunit:=(isUnit_iff_ne_zero.mpr
     ((Algebra.IsSeparable.isSeparable F pb.gen).aeval_derivative_ne_zero
       (minpoly.aeval F _))).map f
   rw [←aeval_algHom_apply, ←hx, ←helper,aeval_algHom_apply,
     helper] at hunit
   obtain ⟨u,hu⟩:=Ideal.Quotient.mk_surjective
     (-hunit.unit⁻¹:HasQuotient.Quotient B I)
   use u
   rw [←Ideal.Quotient.eq_zero_iff_mem,map_add,map_mul,map_one,hu,
     mul_neg,IsUnit.mul_val_inv,neg_add_cancel]
 use pb.liftEquiv.symm ⟨x+u*aeval x (minpoly F pb.gen),?_⟩
 · apply pb.algHom_ext
   simp [hx,hx']
 · rw [←eval_map_algebraMap,Polynomial.eval_add_of_sq_eq_zero,
     derivative_map, ←one_mul (eval x _),eval_map_algebraMap,
     eval_map_algebraMap, ←mul_assoc, ←add_mul, ←Ideal.mem_bot,
     ←h,pow_two,add_comm]
   · exact Ideal.mul_mem_mul hu (Ideal.Quotient.eq_zero_iff_mem.mp hx')
   rw [←Ideal.mem_bot, ←h]
   apply Ideal.pow_mem_pow
   rw [←Ideal.Quotient.eq_zero_iff_mem,map_mul,hx',mul_zero]
theorem ratFunc_variableDifferential_ne_zero (K:Type*) [Field K]:
   D K (RatFunc K)
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)≠0:=by
 letI:Algebra.FormallyEtale (Polynomial K) (RatFunc K):=
   Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (Polynomial K))
 intro hzero
 have htensor:=congrArg
   (tensorKaehlerEquivOfFormallyEtale
     K (Polynomial K) (RatFunc K)).symm hzero
 have htensor':(1:RatFunc K) ⊗ₜ[Polynomial K]
     D K (Polynomial K) Polynomial.X=0:=by
   simpa only [map_zero,
     tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap] using htensor
 let l:Ω[Polynomial K⁄K] →ₗ[Polynomial K] RatFunc K:=
   (Algebra.linearMap (Polynomial K) (RatFunc K)).comp
     (polynomialEquiv K).toLinearMap
 have himage:=congrArg (l.liftBaseChange (RatFunc K)) htensor'
 have hone:(1:RatFunc K)=0:=by
   rw [LinearMap.liftBaseChange_tmul,one_smul,map_zero] at himage
   change algebraMap (Polynomial K) (RatFunc K)
     (polynomialEquiv K (D K (Polynomial K) Polynomial.X))=0 at himage
   simpa only [polynomialEquiv_D,derivative_X,map_one] using himage
 exact one_ne_zero hone
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
theorem parameterDifferential_ne_zero_of_isSeparable
   (embedding:RatFunc K →ₐ[K] L)
   (hfinite:
     letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hsep:
     letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc K) L):
   parameterDifferential K L embedding≠0:=by
 letI:Algebra (RatFunc K) L:=embedding.toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun c↦(embedding.commutes c).symm
 letI:FiniteDimensional (RatFunc K) L:=hfinite
 letI:Algebra.IsSeparable (RatFunc K) L:=hsep
 letI:Algebra.FormallyEtale (RatFunc K) L:=
   formallyEtale_of_finite_isSeparable (RatFunc K) L
 intro hzero
 change D K L
   (algebraMap (RatFunc K) L
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))=0 at hzero
 have htensor:=congrArg
   (tensorKaehlerEquivOfFormallyEtale K (RatFunc K) L).symm hzero
 have htensor':(1:L) ⊗ₜ[RatFunc K]
     D K (RatFunc K)
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=0:=by
   simpa only [map_zero,
     tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap] using htensor
 have hsource:D K (RatFunc K)
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=0:=by
   rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at htensor'
   exact htensor'
 exact ratFunc_variableDifferential_ne_zero K hsource
theorem shear_bad_coefficient_subsingleton
   (r z:L) (hdz:D K L z≠0):
   ∀ {a b:K},
     D K L r+a • D K L z=0 →
     D K L r+b • D K L z=0 → a=b:=by
 intro a b ha hb
 apply smul_left_injective K hdz
 exact (eq_neg_of_add_eq_zero_right ha).trans
   (eq_neg_of_add_eq_zero_right hb).symm
theorem shear_transcendental_finite_separable_of_differential_ne_zero
   [IsAlgClosed K]
   (embeddingZ:RatFunc K →ₐ[K] L) (r z:L) (a:K)
   (hvalueZ:embeddingZ
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=z)
   (hfiniteZ:
     letI:Algebra (RatFunc K) L:=embeddingZ.toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hsepZ:
     letI:Algebra (RatFunc K) L:=embeddingZ.toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc K) L)
   (hdiff:D K L r+a • D K L z≠0):
   ∃ hs:Transcendental K (r+a • z),
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L (r+a • z) hs).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) L)∧
     (letI:Algebra (RatFunc K) L:=
         (elementEmbedding K L (r+a • z) hs).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) L):=by
 have hDs:D K L (r+a • z)=D K L r+a • D K L z:=by
   rw [map_add,(D K L).map_smul]
 have hs:Transcendental K (r+a • z):=by
   show ¬ IsAlgebraic K _
   intro halg
   obtain ⟨c,hc⟩:=eq_algebraMap_of_isAlgebraic K L _ halg
   apply hdiff
   rw [←hDs, ←hc]
   exact (D K L).map_algebraMap c
 refine ⟨hs,?_,?_⟩
 · exact finiteDimensional_elementEmbedding K L embeddingZ hfiniteZ
     (r+a • z) hs
 · let embeddingS:=elementEmbedding K L (r+a • z) hs
   have hfiniteS:=finiteDimensional_elementEmbedding K L embeddingZ hfiniteZ
     (r+a • z) hs
   have hcriterionZ:=
     isSeparable_iff_span_parameterDifferential K L embeddingZ hfiniteZ
   have hcriterionS:=
     isSeparable_iff_span_parameterDifferential K L embeddingS hfiniteS
   have hspanZ:Submodule.span L ({D K L z}:Set Ω[L⁄K])=⊤:=by
     have hz:=hcriterionZ.mp hsepZ
     unfold parameterDifferential at hz
     rw [hvalueZ] at hz
     exact hz
   apply hcriterionS.mpr
   have hparamS:parameterDifferential K L embeddingS=
       D K L (r+a • z):=by
     unfold parameterDifferential embeddingS
     rw [elementEmbedding_variable]
   rw [hparamS,hDs]
   apply top_unique
   rw [←hspanZ]
   apply Submodule.span_le.mpr
   intro x hx
   rw [Set.mem_singleton_iff.mp hx]
   have hS_mem:D K L r+a • D K L z∈
       Submodule.span L ({D K L z}:Set Ω[L⁄K]):=by
     rw [hspanZ]
     trivial
   obtain ⟨b,hb⟩:=Submodule.mem_span_singleton.mp hS_mem
   have hb0:b≠0:=by
     intro hzero
     apply hdiff
     rw [←hb,hzero,zero_smul]
   apply Submodule.mem_span_singleton.mpr
   refine ⟨b⁻¹,?_⟩
   rw [←hb,smul_smul,inv_mul_cancel₀ hb0,one_smul]
section FiniteFamily
variable {I:Type*} [Fintype I]
 (E:I → Type*) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 (r z:∀ i,E i)
theorem exists_common_nonzero_shear_coefficient
   [Infinite K] (hdz:∀ i,D K (E i) (z i)≠0):
   ∃ a:K,a≠0∧∀ i,
     D K (E i) (r i)+a • D K (E i) (z i)≠0:=by
 classical
 letI:DecidableEq K:=Classical.decEq K
 letI:DecidableEq I:=Classical.decEq I
 let Bad:I → K → Prop:=fun i a↦
   D K (E i) (r i)+a • D K (E i) (z i)=0
 have hsingle:∀ i {a b},Bad i a → Bad i b → a=b:=by
   intro i a b ha hb
   exact shear_bad_coefficient_subsingleton K (E i) (r i) (z i)
     (hdz i) ha hb
 let forbidden:Finset K:=Finset.univ.biUnion fun i↦
   if h:∃ a,Bad i a then {Classical.choose h} else ∅
 obtain ⟨a,ha⟩:=Infinite.exists_notMem_finset (insert 0 forbidden)
 refine ⟨a,?_,?_⟩
 · intro hzero
   exact ha (hzero ▸ Finset.mem_insert_self 0 forbidden)
 · intro i hbad
   have hex:∃ b,Bad i b:=⟨a,hbad⟩
   let b:=Classical.choose hex
   have hbbad:Bad i b:=Classical.choose_spec hex
   have heq:a=b:=hsingle i hbad hbbad
   have hbmem:b∈forbidden:=by
     change b∈Finset.univ.biUnion (fun i↦
       if h:∃ a,Bad i a then {Classical.choose h} else ∅)
     apply Finset.mem_biUnion.mpr
     refine ⟨i,Finset.mem_univ i,?_⟩
     simpa only [dif_pos hex,Finset.mem_singleton,b]
   exact ha (Finset.mem_insert_of_mem (heq ▸ hbmem))
theorem exists_common_finite_separable_shear
   [IsAlgClosed K]
   (embeddingZ:∀ i,RatFunc K →ₐ[K] E i)
   (hvalueZ:∀ i,embeddingZ i
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=z i)
   (hfiniteZ:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (embeddingZ i).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) (E i))
   (hsepZ:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (embeddingZ i).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc K) (E i)):
   ∃ a:K,a≠0∧∀ i,
     ∃ hs:Transcendental K (r i+a • z i),
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) hs).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc K) (E i))∧
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) hs).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc K) (E i)):=by
 have hdz:∀ i,D K (E i) (z i)≠0:=by
   intro i
   have h:=parameterDifferential_ne_zero_of_isSeparable
     K (E i) (embeddingZ i) (hfiniteZ i) (hsepZ i)
   unfold parameterDifferential at h
   rw [hvalueZ i] at h
   exact h
 obtain ⟨a,ha0,hdiff⟩:=
   exists_common_nonzero_shear_coefficient K E r z hdz
 refine ⟨a,ha0,fun i↦?_⟩
 exact shear_transcendental_finite_separable_of_differential_ne_zero
   K (E i) (embeddingZ i) (r i) (z i) a
     (hvalueZ i) (hfiniteZ i) (hsepZ i) (hdiff i)
end FiniteFamily
end
end ProximityPrize.SubmissionLower.RCN351
end PackedLegacy_R7

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier15 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.DE. -/
section PackedLegacy_DE
namespace ProximityPrize.SubmissionLower.RCN024
open scoped BigOperators
noncomputable section
variable {K:Type*} [Field K] [DecidableEq K]
 {ι:Type*} [Fintype ι] [DecidableEq ι]
theorem pow_card_dvd_det_of_dvd_columns
   (M:Matrix ι ι (Polynomial K)) (a:Polynomial K) (columns:Finset ι)
   (hdiv:∀ j∈columns,∀ i,a∣M i j):
   a^columns.card∣M.det:=by
 classical
 rw [Matrix.det_apply']
 apply Finset.dvd_sum
 intro permutation _
 have hpart:
     (∏ _j∈columns,a)∣∏ j∈columns,M (permutation j) j:=by
   apply Finset.prod_dvd_prod_of_dvd
   intro j hj
   exact hdiv j hj (permutation j)
 have hfull:
     (∏ j∈columns,M (permutation j) j)∣
       ∏ j:ι,M (permutation j) j:=
   Finset.prod_dvd_prod_of_subset columns Finset.univ
     (fun j => M (permutation j) j) (Finset.subset_univ columns)
 have hproduct:a^columns.card∣∏ j:ι,M (permutation j) j:=by
   simpa using hpart.trans hfull
 exact dvd_mul_of_dvd_right hproduct _
theorem irreducible_pow_corank_dvd_det
   (M:Matrix ι ι (Polynomial K)) (mu:Polynomial K)
   (hmu:Irreducible mu):
   mu^(Fintype.card ι-((AdjoinRoot.mk mu).mapMatrix M).rank)∣M.det:=by
 classical
 letI:Fact (Irreducible mu):=⟨hmu⟩
 let reduceMatrix:Matrix ι ι (Polynomial K) →+*
     Matrix ι ι (AdjoinRoot mu):=(AdjoinRoot.mk mu).mapMatrix
 let reduced:Matrix ι ι (AdjoinRoot mu):=reduceMatrix M
 obtain ⟨V,U,e,hV,hU,hnormal⟩:=Matrix.exists_rank_normal_form reduced
 let liftEntry:AdjoinRoot mu → Polynomial K:=
   Function.surjInv (AdjoinRoot.mk_surjective (g:=mu))
 have hliftEntry (x:AdjoinRoot mu):AdjoinRoot.mk mu (liftEntry x)=x:=by
   exact Function.surjInv_eq (AdjoinRoot.mk_surjective (g:=mu)) x
 let Vlift:Matrix ι ι (Polynomial K):=fun i j => liftEntry (V i j)
 let Ulift:Matrix ι ι (Polynomial K):=fun i j => liftEntry (U i j)
 have hmapV:reduceMatrix Vlift=V:=by
   ext i j
   exact hliftEntry (V i j)
 have hmapU:reduceMatrix Ulift=U:=by
   ext i j
   exact hliftEntry (U i j)
 let transformed:Matrix ι ι (Polynomial K):=Vlift*M*Ulift
 have hmapTransformed:reduceMatrix transformed=
     (Matrix.fromBlocks 1 0 0 0).submatrix e e:=by
   change reduceMatrix (Vlift*M*Ulift)=_
   rw [map_mul,map_mul,hmapV,hmapU]
   exact hnormal
 let zeroEmbedding:Fin (Fintype.card ι-reduced.rank) ↪ ι:={
   toFun:=fun j => e.symm (Sum.inr j)
   inj':=by
     intro i j hij
     exact Sum.inr.inj (e.symm.injective hij)
 }
 let zeroColumns:Finset ι:=Finset.univ.map zeroEmbedding
 have hcard:zeroColumns.card=Fintype.card ι-reduced.rank:=by
   simp [zeroColumns]
 have hcolumns:∀ j∈zeroColumns,∀ i,mu∣transformed i j:=by
   intro j hj i
   obtain ⟨j0,_,rfl⟩:=Finset.mem_map.mp hj
   apply AdjoinRoot.mk_eq_zero.mp
   change reduceMatrix transformed i (e.symm (Sum.inr j0))=0
   rw [hmapTransformed]
   simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply]
   cases e i <;> rfl
 have hVdet:¬mu∣Vlift.det:=by
   intro hdiv
   have hzero:AdjoinRoot.mk mu Vlift.det=0:=AdjoinRoot.mk_eq_zero.mpr hdiv
   have hdetmap:AdjoinRoot.mk mu Vlift.det=V.det:=by
     rw [(AdjoinRoot.mk mu).map_det,hmapV]
   have hVdetUnit:IsUnit V.det:=(Matrix.isUnit_iff_isUnit_det _).mp hV
   exact hVdetUnit.ne_zero (hdetmap ▸ hzero)
 have hUdet:¬mu∣Ulift.det:=by
   intro hdiv
   have hzero:AdjoinRoot.mk mu Ulift.det=0:=AdjoinRoot.mk_eq_zero.mpr hdiv
   have hdetmap:AdjoinRoot.mk mu Ulift.det=U.det:=by
     rw [(AdjoinRoot.mk mu).map_det,hmapU]
   have hUdetUnit:IsUnit U.det:=(Matrix.isUnit_iff_isUnit_det _).mp hU
   exact hUdetUnit.ne_zero (hdetmap ▸ hzero)
 have hdetdiv:=pow_card_dvd_det_of_dvd_columns
   transformed mu zeroColumns hcolumns
 rw [hcard] at hdetdiv
 change mu^(Fintype.card ι-reduced.rank)∣
     (Vlift*M*Ulift).det at hdetdiv
 rw [Matrix.det_mul,Matrix.det_mul] at hdetdiv
 have hprime:Prime mu:=hmu.prime
 have hafterV:mu^(Fintype.card ι-reduced.rank)∣M.det*Ulift.det:=
   hprime.pow_dvd_of_dvd_mul_left _ hVdet (by simpa [mul_assoc] using hdetdiv)
 have hafterU:mu^(Fintype.card ι-reduced.rank)∣M.det:=
   hprime.pow_dvd_of_dvd_mul_right _ hUdet hafterV
 simpa [reduced,reduceMatrix] using hafterU
section SylvesterCorank
variable {F:Type*} [Field F] [DecidableEq F]
def remainderOn (D:Polynomial F) (N:ℕ) (hD:D.Monic):
   Polynomial.degreeLT F N →ₗ[F] Polynomial.degreeLT F D.natDegree where
 toFun p:=⟨(p:Polynomial F) %ₘ D,
   Polynomial.mem_degreeLT.mpr (by
     simpa only [Polynomial.degree_eq_natDegree hD.ne_zero] using
       Polynomial.degree_modByMonic_lt (p:Polynomial F) hD)⟩
 map_add' p q:=Subtype.ext (Polynomial.add_modByMonic _ _)
 map_smul' c p:=Subtype.ext (Polynomial.smul_modByMonic c (p:Polynomial F))
theorem remainderOn_surjective (D:Polynomial F) (N:ℕ) (hD:D.Monic)
   (hdegree:D.natDegree ≤ N):Function.Surjective (remainderOn D N hD):=by
 intro q
 have hqN:(q:Polynomial F).degree < (N:WithBot ℕ):=
   (Polynomial.mem_degreeLT.mp q.property).trans_le (by exact_mod_cast hdegree)
 refine ⟨⟨q,Polynomial.mem_degreeLT.mpr hqN⟩,?_⟩
 apply Subtype.ext
 exact (Polynomial.modByMonic_eq_self_iff hD).mpr (by
   rw [Polynomial.degree_eq_natDegree hD.ne_zero]
   exact Polynomial.mem_degreeLT.mp q.property)
theorem sylvester_rank_eq_finrank_range
   (p q:Polynomial F) (m n:ℕ)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n):
   (Polynomial.sylvester p q m n).rank=
     Module.finrank F (LinearMap.range (Polynomial.sylvesterMap p q hp hq)):=by
 have hmatrix:LinearMap.toMatrix
     (Polynomial.degreeLT.basisProd F m n)
     (Polynomial.degreeLT.basis F (m+n))
     (Polynomial.sylvesterMap p q hp hq)=Polynomial.sylvester p q m n:=
   Polynomial.toMatrix_sylvesterMap' p q hp hq
 rw [Matrix.rank_eq_finrank_range_toLin _
   (Polynomial.degreeLT.basis F (m+n)) (Polynomial.degreeLT.basisProd F m n)]
 rw [←hmatrix,Matrix.toLin_toMatrix]
theorem common_divisor_natDegree_le_sylvester_corank
   (p q D:Polynomial F) (m n:ℕ)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n)
   (hD:D.Monic) (hDdegree:D.natDegree ≤ m+n)
   (hDp:D∣p) (hDq:D∣q):
   D.natDegree ≤ m+n-(Polynomial.sylvester p q m n).rank:=by
 let R:=remainderOn D (m+n) hD
 let L:=Polynomial.sylvesterMap p q hp hq
 have hsurj:Function.Surjective R:=
   remainderOn_surjective D (m+n) hD hDdegree
 have hcontain:LinearMap.range L ≤ LinearMap.ker R:=by
   rintro output ⟨input,rfl⟩
   rw [LinearMap.mem_ker]
   apply Subtype.ext
   change ((R (L input):Polynomial F))=0
   simp only [R,L,remainderOn,Polynomial.sylvesterMap,LinearMap.coe_mk,
     AddHom.coe_mk]
   apply (Polynomial.modByMonic_eq_zero_iff_dvd hD).mpr
   exact dvd_add (dvd_mul_of_dvd_left hDp _) (dvd_mul_of_dvd_left hDq _)
 have hremainderRank:Module.finrank F (LinearMap.range R)=D.natDegree:=by
   rw [LinearMap.range_eq_top.mpr hsurj,finrank_top]
   simpa using Module.finrank_eq_card_basis
     (Polynomial.degreeLT.basis F D.natDegree)
 have hnull:=LinearMap.finrank_range_add_finrank_ker R
 rw [hremainderRank] at hnull
 have hdomain:Module.finrank F (Polynomial.degreeLT F (m+n))=m+n:=by
   simpa using Module.finrank_eq_card_basis (Polynomial.degreeLT.basis F (m+n))
 rw [hdomain] at hnull
 have hmono:=Submodule.finrank_mono hcontain
 have hmatrix:=sylvester_rank_eq_finrank_range p q m n hp hq
 change (Polynomial.sylvester p q m n).rank=
   Module.finrank F (LinearMap.range L) at hmatrix
 omega
theorem sum_common_divisor_natDegrees_le_sylvester_corank
   {I:Type*} [Fintype I]
   (p q:Polynomial F) (D:I → Polynomial F) (m n:ℕ)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n) (hpne:p≠0)
   (hmonic:∀ i,(D i).Monic)
   (hcoprime:Pairwise fun i j => IsCoprime (D i) (D j))
   (hDp:∀ i,D i∣p) (hDq:∀ i,D i∣q):
   (∑ i,(D i).natDegree) ≤
     m+n-(Polynomial.sylvester p q m n).rank:=by
 classical
 let Dprod:Polynomial F:=∏ i,D i
 have hDprodMonic:Dprod.Monic:=by
   dsimp [Dprod]
   simpa using Polynomial.monic_prod_of_monic Finset.univ D
     (fun i _ => hmonic i)
 have hDprodP:Dprod∣p:=by
   dsimp [Dprod]
   exact Fintype.prod_dvd_of_coprime hcoprime hDp
 have hDprodQ:Dprod∣q:=by
   dsimp [Dprod]
   exact Fintype.prod_dvd_of_coprime hcoprime hDq
 have hDprodDegree:Dprod.natDegree=∑ i,(D i).natDegree:=by
   dsimp [Dprod]
   simpa using Polynomial.natDegree_prod_of_monic
     (s:=Finset.univ) (f:=D) (fun i _ => hmonic i)
 have hDdegree:Dprod.natDegree ≤ m+n:=by
   have hle:=Polynomial.natDegree_le_of_dvd hDprodP hpne
   omega
 rw [←hDprodDegree]
 exact common_divisor_natDegree_le_sylvester_corank p q Dprod m n
   hp hq hDprodMonic hDdegree hDprodP hDprodQ
end SylvesterCorank
section IrreducibleAggregation
theorem sum_irreducible_coranks_le_det_natDegree
   {I:Type*} [Fintype I]
   (M:Matrix ι ι (Polynomial K)) (mu:I → Polynomial K) (c:I → ℕ)
   (hmonic:∀ i,(mu i).Monic)
   (hirreducible:∀ i,Irreducible (mu i))
   (hcoprime:Pairwise fun i j => IsCoprime (mu i) (mu j))
   (hcorank:∀ i,
     c i ≤ Fintype.card ι-((AdjoinRoot.mk (mu i)).mapMatrix M).rank)
   (hdet:M.det≠0):
   (∑ i,c i*(mu i).natDegree) ≤ M.det.natDegree:=by
 classical
 have hfactor (i:I):(mu i)^c i∣M.det:=
   (pow_dvd_pow (mu i) (hcorank i)).trans
     (irreducible_pow_corank_dvd_det M (mu i) (hirreducible i))
 have hpowersCoprime:Pairwise fun i j =>
     IsCoprime ((mu i)^c i) ((mu j)^c j):=by
   intro i j hij
   exact (hcoprime hij).pow
 have hprodDvd:(∏ i,(mu i)^c i)∣M.det:=
   Fintype.prod_dvd_of_coprime hpowersCoprime hfactor
 have hprodMonic:(∏ i,(mu i)^c i).Monic:=by
   simpa using Polynomial.monic_prod_of_monic Finset.univ
     (fun i => (mu i)^c i) (fun i _ => (hmonic i).pow _)
 have hdegree:(∏ i,(mu i)^c i).natDegree=
     ∑ i,c i*(mu i).natDegree:=by
   rw [Polynomial.natDegree_prod_of_monic
     (s:=Finset.univ) (f:=fun i => (mu i)^c i)
     (fun i _ => (hmonic i).pow _)]
   apply Finset.sum_congr rfl
   intro i _
   exact Polynomial.natDegree_pow (mu i) (c i)
 rw [←hdegree]
 exact Polynomial.natDegree_le_of_dvd hprodDvd hdet
end IrreducibleAggregation
section RelationKernel
variable {K₀ E₁ E₂:Type} [Field K₀] [DecidableEq K₀]
 [Field E₁] [Field E₂] [Algebra K₀ E₁] [Algebra K₀ E₂]
theorem planeEval_quotientRoot_eq_aeval_map
   (mu:Polynomial K₀) [Fact (Irreducible mu)]
   [Algebra (AdjoinRoot mu) E₁] [IsScalarTower K₀ (AdjoinRoot mu) E₁]
   (r:E₁) (P:Polynomial (Polynomial K₀)):
   RCN361.planeEval K₀ E₁
     (algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)) r P=
     Polynomial.aeval r (P.map (AdjoinRoot.mk mu)):=by
 let y:E₁:=algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)
 have hcoeff:
     (algebraMap (AdjoinRoot mu) E₁).comp (AdjoinRoot.mk mu)=
       Polynomial.eval₂RingHom (algebraMap K₀ E₁) y:=by
   apply Polynomial.ringHom_ext
   · intro c
     simpa only [RingHom.comp_apply,AdjoinRoot.mk_C,
       Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
       AdjoinRoot.algebraMap_eq] using
       (IsScalarTower.algebraMap_apply K₀ (AdjoinRoot mu) E₁ c).symm
   · simp only [RingHom.comp_apply,AdjoinRoot.mk_X,
       Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,y]
 let rhs:Polynomial (Polynomial K₀) →+*E₁:=
   (Polynomial.aeval r).toRingHom.comp
     (Polynomial.mapRingHom (AdjoinRoot.mk mu))
 have heq:RCN361.planeEval K₀ E₁ y r=rhs:=by
   apply Polynomial.ringHom_ext
   · intro c
     simpa only [RCN361.planeEval,RingHom.comp_apply,
       Polynomial.coe_mapRingHom,Polynomial.map_C,
       Polynomial.coe_evalRingHom,Polynomial.eval_C,Polynomial.aeval_C,
       rhs,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using
       (congrFun (congrArg DFunLike.coe hcoeff) c).symm
   · simp only [RCN361.planeEval,RingHom.comp_apply,
       Polynomial.coe_mapRingHom,Polynomial.map_X,
       Polynomial.coe_evalRingHom,Polynomial.eval_X,Polynomial.aeval_X,
       rhs,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom]
 exact DFunLike.congr_fun heq P
theorem mem_relationIdeal_quotientRoot_iff_minpoly_dvd_map
   (mu:Polynomial K₀) [Fact (Irreducible mu)]
   [Algebra (AdjoinRoot mu) E₁] [IsScalarTower K₀ (AdjoinRoot mu) E₁]
   (r:E₁) (P:Polynomial (Polynomial K₀)):
   P∈RCN361.relationIdeal K₀ E₁
       (algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)) r ↔
     minpoly (AdjoinRoot mu) r∣P.map (AdjoinRoot.mk mu):=by
 change RCN361.planeEval K₀ E₁
     (algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)) r P=0 ↔ _
 rw [planeEval_quotientRoot_eq_aeval_map]
 exact minpoly.dvd_iff.symm
theorem relationIdeal_eq_of_adjoinRoot_minpoly_eq
   (mu:Polynomial K₀) [Fact (Irreducible mu)]
   [Algebra (AdjoinRoot mu) E₁] [IsScalarTower K₀ (AdjoinRoot mu) E₁]
   [Algebra (AdjoinRoot mu) E₂] [IsScalarTower K₀ (AdjoinRoot mu) E₂]
   (r₁:E₁) (r₂:E₂)
   (hmin:minpoly (AdjoinRoot mu) r₁=minpoly (AdjoinRoot mu) r₂):
   RCN361.relationIdeal K₀ E₁
       (algebraMap (AdjoinRoot mu) E₁ (AdjoinRoot.root mu)) r₁=
     RCN361.relationIdeal K₀ E₂
       (algebraMap (AdjoinRoot mu) E₂ (AdjoinRoot.root mu)) r₂:=by
 apply Ideal.ext
 intro P
 rw [mem_relationIdeal_quotientRoot_iff_minpoly_dvd_map,
   mem_relationIdeal_quotientRoot_iff_minpoly_dvd_map,hmin]
theorem relative_minpolys_pairwise_coprime_of_relationIdeal_injective
   {I:Type*} [Fintype I]
   (mu:Polynomial K₀) [Fact (Irreducible mu)]
   (E:I → Type) [∀ i,Field (E i)]
   [∀ i,Algebra K₀ (E i)]
   [∀ i,Algebra (AdjoinRoot mu) (E i)]
   [∀ i,IsScalarTower K₀ (AdjoinRoot mu) (E i)]
   [∀ i,FiniteDimensional (AdjoinRoot mu) (E i)]
   (r:∀ i,E i)
   (hkernels:Function.Injective (fun i =>
     RCN361.relationIdeal K₀ (E i)
       (algebraMap (AdjoinRoot mu) (E i) (AdjoinRoot.root mu)) (r i))):
   Pairwise fun i j => IsCoprime
     (minpoly (AdjoinRoot mu) (r i)) (minpoly (AdjoinRoot mu) (r j)):=by
 intro i j hij
 have hiIntegral:IsIntegral (AdjoinRoot mu) (r i):=
   IsIntegral.of_finite (AdjoinRoot mu) (r i)
 have hjIntegral:IsIntegral (AdjoinRoot mu) (r j):=
   IsIntegral.of_finite (AdjoinRoot mu) (r j)
 have hiIrreducible:=minpoly.irreducible hiIntegral
 have hjIrreducible:=minpoly.irreducible hjIntegral
 apply hiIrreducible.coprime_iff_not_dvd.mpr
 intro hdvd
 have hassociated:=hiIrreducible.associated_of_dvd hjIrreducible hdvd
 have hmin:minpoly (AdjoinRoot mu) (r i)=
     minpoly (AdjoinRoot mu) (r j):=
   Polynomial.eq_of_monic_of_associated
     (minpoly.monic hiIntegral) (minpoly.monic hjIntegral) hassociated
 have hk:=relationIdeal_eq_of_adjoinRoot_minpoly_eq
   (K₀:=K₀) (E₁:=E i) (E₂:=E j) mu (r i) (r j) hmin
 exact hij (hkernels hk)
end RelationKernel
section SingleComponent
variable {E:Type*} [Field E] [Algebra K E]
theorem finrank_le_resultant_natDegree_of_adjoinRoot_component
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (mu:Polynomial K)
   [Fact (Irreducible mu)]
   [Algebra (AdjoinRoot mu) E] [IsScalarTower K (AdjoinRoot mu) E]
   [FiniteDimensional (AdjoinRoot mu) E]
   (r:E)
   (hgen:IntermediateField.adjoin (AdjoinRoot mu) ({r}:Set E)=⊤)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (hPne:P.map (AdjoinRoot.mk mu)≠0)
   (hProot:Polynomial.aeval r (P.map (AdjoinRoot.mk mu))=0)
   (hQroot:Polynomial.aeval r (Q.map (AdjoinRoot.mk mu))=0)
   (hresultant:Polynomial.resultant P Q m n≠0):
   Module.finrank K E ≤ (Polynomial.resultant P Q m n).natDegree:=by
 have hmu:Irreducible mu:=Fact.out
 letI:FiniteDimensional K (AdjoinRoot mu):=
   (AdjoinRoot.powerBasis hmu.ne_zero).finite
 let p:Polynomial (AdjoinRoot mu):=P.map (AdjoinRoot.mk mu)
 let q:Polynomial (AdjoinRoot mu):=Q.map (AdjoinRoot.mk mu)
 let D:Polynomial (AdjoinRoot mu):=minpoly (AdjoinRoot mu) r
 have hDmonic:D.Monic:=minpoly.monic (IsIntegral.of_finite (AdjoinRoot mu) r)
 have hDp:D∣p:=minpoly.dvd (AdjoinRoot mu) r hProot
 have hDq:D∣q:=minpoly.dvd (AdjoinRoot mu) r hQroot
 have hpCap:p.natDegree ≤ m:=Polynomial.natDegree_map_le.trans hPcap
 have hqCap:q.natDegree ≤ n:=Polynomial.natDegree_map_le.trans hQcap
 have hDdegree:D.natDegree ≤ m+n:=by
   have hle:D.natDegree ≤ p.natDegree:=
     Polynomial.natDegree_le_of_dvd hDp hPne
   omega
 have hcorank:D.natDegree ≤ m+n-(Polynomial.sylvester p q m n).rank:=
   common_divisor_natDegree_le_sylvester_corank p q D m n
     hpCap hqCap hDmonic hDdegree hDp hDq
 have hpow:
     mu^(m+n-(Polynomial.sylvester p q m n).rank)∣
       Polynomial.resultant P Q m n:=by
   simpa only [Polynomial.resultant,Fintype.card_fin,
     ←Polynomial.sylvester_map_map] using
     (irreducible_pow_corank_dvd_det
       (M:=Polynomial.sylvester P Q m n) mu Fact.out)
 have hpowDegree:
     (mu^(m+n-(Polynomial.sylvester p q m n).rank)).natDegree ≤
       (Polynomial.resultant P Q m n).natDegree:=
   Polynomial.natDegree_le_of_dvd hpow hresultant
 have hrelative:D.natDegree=Module.finrank (AdjoinRoot mu) E:=
   (Field.primitive_element_iff_minpoly_natDegree_eq (AdjoinRoot mu) r).mp hgen
 have hbase:Module.finrank K (AdjoinRoot mu)=mu.natDegree:=by
   change Module.finrank K (Polynomial K ⧸ Ideal.span {mu})=mu.natDegree
   exact finrank_quotient_span_eq_natDegree
 have htotal:Module.finrank K E=mu.natDegree*D.natDegree:=by
   rw [←Module.finrank_mul_finrank K (AdjoinRoot mu) E,hbase, ←hrelative]
 rw [htotal]
 calc
   mu.natDegree*D.natDegree ≤
       mu.natDegree*(m+n-(Polynomial.sylvester p q m n).rank):=
     Nat.mul_le_mul_left _ hcorank
   _=(mu^(m+n-(Polynomial.sylvester p q m n).rank)).natDegree:=by
     rw [Polynomial.natDegree_pow,Nat.mul_comm]
   _ ≤ (Polynomial.resultant P Q m n).natDegree:=hpowDegree
end SingleComponent
section SingleComponentBidegree
variable {K₀ E₀:Type} [Field K₀] [DecidableEq K₀]
 [Field E₀] [Algebra K₀ E₀]
theorem finrank_le_bidegree_of_adjoinRoot_component
   (P Q:Polynomial (Polynomial K₀)) (m n:ℕ) (mu:Polynomial K₀)
   [Fact (Irreducible mu)]
   [Algebra (AdjoinRoot mu) E₀] [IsScalarTower K₀ (AdjoinRoot mu) E₀]
   [FiniteDimensional (AdjoinRoot mu) E₀]
   (r:E₀)
   (hgen:IntermediateField.adjoin (AdjoinRoot mu) ({r}:Set E₀)=⊤)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (hPne:P.map (AdjoinRoot.mk mu)≠0)
   (hProot:Polynomial.aeval r (P.map (AdjoinRoot.mk mu))=0)
   (hQroot:Polynomial.aeval r (Q.map (AdjoinRoot.mk mu))=0)
   (hresultant:Polynomial.resultant P Q m n≠0):
   Module.finrank K₀ E₀ ≤
     n*Polynomial.Bivariate.degreeX P+m*Polynomial.Bivariate.degreeX Q:=by
 exact (finrank_le_resultant_natDegree_of_adjoinRoot_component P Q m n mu r
   hgen hPcap hQcap hPne hProot hQroot hresultant).trans
     (bivariate_resultant_natDegree_le (F:=K₀) P Q m n)
end SingleComponentBidegree
section ExistingGeneratingPair
variable {K₀ E₀:Type} [Field K₀] [DecidableEq K₀]
 [Field E₀] [Algebra K₀ E₀] [FiniteDimensional K₀ E₀]
theorem finrank_le_planar_bound_without_separability
   (P Q:Polynomial (Polynomial K₀))
   (hP:Irreducible P) (hpositive:0 < P.natDegree) (hproper:¬P∣Q)
   (y r:E₀)
   (hgen:IntermediateField.adjoin K₀ ({y,r}:Set E₀)=⊤)
   (hPy:RCN361.planeEval K₀ E₀ y r P=0)
   (hQy:RCN361.planeEval K₀ E₀ y r Q=0):
   Module.finrank K₀ E₀ ≤
     Q.natDegree*Polynomial.Bivariate.degreeX P+
       P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 have hyIntegral:IsIntegral K₀ y:=IsIntegral.of_finite K₀ y
 let mu:Polynomial K₀:=minpoly K₀ y
 have hmuIrreducible:Irreducible mu:=minpoly.irreducible hyIntegral
 letI:Fact (Irreducible mu):=⟨hmuIrreducible⟩
 let S:IntermediateField K₀ E₀:=IntermediateField.adjoin K₀ {y}
 let baseEquiv:AdjoinRoot mu ≃ₐ[K₀] S:=
   IntermediateField.adjoinRootEquivAdjoin K₀ hyIntegral
 let baseHom:AdjoinRoot mu →ₐ[K₀] E₀:=S.val.comp baseEquiv.toAlgHom
 letI:Algebra (AdjoinRoot mu) E₀:=baseHom.toRingHom.toAlgebra
 haveI:IsScalarTower K₀ (AdjoinRoot mu) E₀:=
   IsScalarTower.of_algebraMap_eq fun c => (baseHom.commutes c).symm
 letI:Module.Finite (AdjoinRoot mu) E₀:=
   Module.Finite.of_restrictScalars_finite K₀ (AdjoinRoot mu) E₀
 have hroot:algebraMap (AdjoinRoot mu) E₀ (AdjoinRoot.root mu)=y:=by
   change baseHom (AdjoinRoot.root mu)=y
   change ((S.val.comp baseEquiv.toAlgHom) (AdjoinRoot.root mu):E₀)=y
   rw [AlgHom.comp_apply]
   change ((baseEquiv (AdjoinRoot.root mu):S):E₀)=y
   rw [show baseEquiv=IntermediateField.adjoinRootEquivAdjoin K₀ hyIntegral from rfl,
     IntermediateField.adjoinRootEquivAdjoin_apply_root]
   rfl
 have hgenAll:IntermediateField.adjoin (AdjoinRoot mu)
     ({y,r}:Set E₀)=⊤:=
   IntermediateField.adjoin_eq_top_of_adjoin_eq_top
     (F:=K₀) (E:=AdjoinRoot mu) (K:=E₀) hgen
 have hgenRelative:IntermediateField.adjoin (AdjoinRoot mu)
     ({r}:Set E₀)=⊤:=by
   apply le_antisymm le_top
   rw [←hgenAll]
   apply IntermediateField.adjoin_le_iff.mpr
   intro x hx
   rcases Set.mem_insert_iff.mp hx with hxy | hxr
   · subst x
     rw [←hroot]
     exact IntermediateField.adjoin.algebraMap_mem (AdjoinRoot mu) {r}
       (AdjoinRoot.root mu)
   · have:x=r:=Set.mem_singleton_iff.mp hxr
     subst x
     exact IntermediateField.subset_adjoin (AdjoinRoot mu) {r}
       (Set.mem_singleton r)
 have hcoeff:Polynomial.eval₂RingHom
     (algebraMap K₀ (AdjoinRoot mu)) (AdjoinRoot.root mu)=
     AdjoinRoot.mk mu:=by
   apply Polynomial.ringHom_ext
   · intro c
     simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
       AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
   · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,
       AdjoinRoot.mk_X]
 have hPne:P.map (AdjoinRoot.mk mu)≠0:=by
   have hspecial:=RCN360.bimap_specialization_ne_zero
     (algebraMap K₀ (AdjoinRoot mu)) P
     (hP.isPrimitive (Nat.ne_of_gt hpositive)) (AdjoinRoot.root mu)
   rw [RCN360.bimap_specialization,hcoeff] at hspecial
   exact hspecial
 have hProot:Polynomial.aeval r (P.map (AdjoinRoot.mk mu))=0:=by
   rw [←planeEval_quotientRoot_eq_aeval_map,hroot]
   exact hPy
 have hQroot:Polynomial.aeval r (Q.map (AdjoinRoot.mk mu))=0:=by
   rw [←planeEval_quotientRoot_eq_aeval_map,hroot]
   exact hQy
 have hresultant:Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=
   RCN362.irreducible_resultant_ne_zero_of_not_dvd
     P Q hP hpositive hproper
 exact finrank_le_bidegree_of_adjoinRoot_component
   P Q P.natDegree Q.natDegree mu r hgenRelative le_rfl le_rfl
     hPne hProot hQroot hresultant
end ExistingGeneratingPair
section FiniteWithoutSeparability
variable {K₀ E₀:Type} [Field K₀] [DecidableEq K₀]
 [Field E₀] [Algebra K₀ E₀]
theorem finiteDimensional_of_integral_generating_pair
   (y r:E₀) (hy:IsIntegral K₀ y) (hr:IsIntegral K₀ r)
   (hgen:IntermediateField.adjoin K₀ ({y,r}:Set E₀)=⊤):
   FiniteDimensional K₀ E₀:=by
 letI:FiniteDimensional K₀
     (IntermediateField.adjoin K₀ ({y,r}:Set E₀)):=
   IntermediateField.finiteDimensional_adjoin_pair hy hr
 letI:FiniteDimensional K₀ (⊤:IntermediateField K₀ E₀):=by
   rw [←hgen]
   infer_instance
 exact Module.Finite.of_surjective
   (IntermediateField.topEquiv (F:=K₀) (E:=E₀)).toLinearMap
   (IntermediateField.topEquiv (F:=K₀) (E:=E₀)).surjective
theorem finite_of_proper_plane_roots
   (P Q:Polynomial (Polynomial K₀))
   (hirreducible:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬P∣Q) (y r:E₀)
   (hP:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ E₀) y) r P=0)
   (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ E₀) y) r Q=0)
   (hgen:IntermediateField.adjoin K₀ ({y,r}:Set E₀)=⊤):
   FiniteDimensional K₀ E₀:=by
 classical
 have hresne:=RCN362.irreducible_resultant_ne_zero_of_not_dvd
   P Q hirreducible hpositive hproper
 have hresroot:=RCN364.resultant_aeval_eq_zero_of_common_root P Q
   P.natDegree Q.natDegree le_rfl le_rfl (Or.inl (Nat.ne_of_gt hpositive))
     y r hP hQ
 have hyIntegral:IsIntegral K₀ y:=
   IsAlgebraic.isIntegral ⟨Polynomial.resultant P Q P.natDegree Q.natDegree,
     hresne,hresroot⟩
 let S:IntermediateField K₀ E₀:=IntermediateField.adjoin K₀ {y}
 let yS:S:=⟨y,IntermediateField.mem_adjoin_simple_self K₀ y⟩
 let g:Polynomial K₀ →+*S:=Polynomial.eval₂RingHom (algebraMap K₀ S) yS
 let Py:Polynomial S:=P.map g
 have hPyne:Py≠0:=by
   have h:=RCN360.bimap_specialization_ne_zero
     (algebraMap K₀ S) P
     (hirreducible.isPrimitive (Nat.ne_of_gt hpositive)) yS
   rw [RCN360.bimap_specialization] at h
   exact h
 have hcoefficient:(algebraMap S E₀).comp g=
     Polynomial.eval₂RingHom (algebraMap K₀ E₀) y:=by
   apply Polynomial.ringHom_ext
   · intro c
     change algebraMap S E₀
         (Polynomial.eval₂ (algebraMap K₀ S) yS (Polynomial.C c))=
       Polynomial.eval₂ (algebraMap K₀ E₀) y (Polynomial.C c)
     rw [Polynomial.eval₂_C,Polynomial.eval₂_C]
     exact (IsScalarTower.algebraMap_apply K₀ S E₀ c).symm
   · change algebraMap S E₀
         (Polynomial.eval₂ (algebraMap K₀ S) yS Polynomial.X)=
       Polynomial.eval₂ (algebraMap K₀ E₀) y Polynomial.X
     rw [Polynomial.eval₂_X,Polynomial.eval₂_X]
     rfl
 have hPyroot:Polynomial.aeval r Py=0:=by
   change Polynomial.eval₂ (algebraMap S E₀) r (P.map g)=0
   rw [Polynomial.eval₂_map,hcoefficient]
   exact hP
 have hrIntegralS:IsIntegral S r:=
   IsAlgebraic.isIntegral ⟨Py,hPyne,hPyroot⟩
 letI:FiniteDimensional K₀ S:=
   IntermediateField.adjoin.finiteDimensional hyIntegral
 letI:Algebra.IsIntegral K₀ S:=Algebra.IsIntegral.of_finite K₀ S
 have hrIntegral:IsIntegral K₀ r:=isIntegral_trans r hrIntegralS
 exact finiteDimensional_of_integral_generating_pair y r hyIntegral hrIntegral hgen
theorem finrank_le_planar_bound_from_proper_roots
   (P Q:Polynomial (Polynomial K₀))
   (hirreducible:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬P∣Q) (y r:E₀)
   (hP:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ E₀) y) r P=0)
   (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ E₀) y) r Q=0)
   (hgen:IntermediateField.adjoin K₀ ({y,r}:Set E₀)=⊤):
   Module.finrank K₀ E₀ ≤
     Q.natDegree*Polynomial.Bivariate.degreeX P+
       P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 letI:FiniteDimensional K₀ E₀:=
   finite_of_proper_plane_roots P Q hirreducible hpositive hproper y r hP hQ hgen
 apply finrank_le_planar_bound_without_separability P Q
   hirreducible hpositive hproper y r hgen
 · change (P.map (Polynomial.eval₂RingHom (algebraMap K₀ E₀) y)).eval r=0
   simpa only [Polynomial.eval₂_eq_eval_map] using hP
 · change (Q.map (Polynomial.eval₂RingHom (algebraMap K₀ E₀) y)).eval r=0
   simpa only [Polynomial.eval₂_eq_eval_map] using hQ
end FiniteWithoutSeparability
end
end ProximityPrize.SubmissionLower.RCN024
end PackedLegacy_DE

/-! Packed from ProximityPrize.SubmissionLower.DF. -/
section PackedLegacy_DF
namespace ProximityPrize.SubmissionLower.RCN025
open scoped Classical BigOperators
open RCN024
noncomputable section
section ScalarBridge
variable {K B E:Type} [Field K] [Field B] [Field E]
 [Algebra K B] [Algebra K E] [Algebra B E] [IsScalarTower K B E]
theorem adjoin_singleton_eq_top_of_pair_eq_top
   (y r:E)
   (hgen:IntermediateField.adjoin K ({y,r}:Set E)=⊤)
   (hy:∃ b:B,algebraMap B E b=y):
   IntermediateField.adjoin B ({r}:Set E)=⊤:=by
 have hgenAll:IntermediateField.adjoin B ({y,r}:Set E)=⊤:=
   IntermediateField.adjoin_eq_top_of_adjoin_eq_top
     (F:=K) (E:=B) (K:=E) hgen
 apply le_antisymm le_top
 rw [←hgenAll]
 apply IntermediateField.adjoin_le_iff.mpr
 intro x hx
 rcases Set.mem_insert_iff.mp hx with hxy | hxr
 · subst x
   obtain ⟨b,rfl⟩:=hy
   exact IntermediateField.adjoin.algebraMap_mem B {r} b
 · have:x=r:=Set.mem_singleton_iff.mp hxr
   subst x
   exact IntermediateField.subset_adjoin B {r} (Set.mem_singleton r)
end ScalarBridge
section MinpolyTower
variable {K E:Type} [Field K] [DecidableEq K] [Field E] [Algebra K E]
 [FiniteDimensional K E]
theorem minpoly_natDegree_dvd_finrank (y:E):
   (minpoly K y).natDegree∣Module.finrank K E:=by
 classical
 have hyIntegral:IsIntegral K y:=IsIntegral.of_finite K y
 let mu:Polynomial K:=minpoly K y
 have hmuIrreducible:Irreducible mu:=minpoly.irreducible hyIntegral
 letI:Fact (Irreducible mu):=⟨hmuIrreducible⟩
 let baseHom:AdjoinRoot mu →ₐ[K] E:=
   AdjoinRoot.liftAlgHom mu (Algebra.ofId K E) y (by
     change Polynomial.aeval y mu=0
     exact minpoly.aeval K y)
 letI:Algebra (AdjoinRoot mu) E:=baseHom.toRingHom.toAlgebra
 haveI:IsScalarTower K (AdjoinRoot mu) E:=
   IsScalarTower.of_algebraMap_eq fun c => (baseHom.commutes c).symm
 letI:Module.Finite (AdjoinRoot mu) E:=
   Module.Finite.of_restrictScalars_finite K (AdjoinRoot mu) E
 letI:FiniteDimensional K (AdjoinRoot mu):=
   (AdjoinRoot.powerBasis hmuIrreducible.ne_zero).finite
 have hbase:Module.finrank K (AdjoinRoot mu)=mu.natDegree:=by
   change Module.finrank K (Polynomial K ⧸ Ideal.span {mu})=mu.natDegree
   exact finrank_quotient_span_eq_natDegree
 refine ⟨Module.finrank (AdjoinRoot mu) E,?_⟩
 rw [←Module.finrank_mul_finrank K (AdjoinRoot mu) E,hbase]
end MinpolyTower
section FixedResiduePolynomial
variable {K:Type} [Field K] [DecidableEq K]
 {I:Type*} [Fintype I]
theorem sum_relative_finrank_le_sylvester_corank
   (mu:Polynomial K) [Fact (Irreducible mu)]
   (E:I → Type) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
   [∀ i,Algebra (AdjoinRoot mu) (E i)]
   [∀ i,IsScalarTower K (AdjoinRoot mu) (E i)]
   [∀ i,FiniteDimensional (AdjoinRoot mu) (E i)]
   (r:∀ i,E i)
   (hgen:∀ i,IntermediateField.adjoin (AdjoinRoot mu)
     ({r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i =>
     RCN361.relationIdeal K (E i)
       (algebraMap (AdjoinRoot mu) (E i) (AdjoinRoot.root mu)) (r i)))
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (hPne:P.map (AdjoinRoot.mk mu)≠0)
   (hProot:∀ i,Polynomial.aeval (r i) (P.map (AdjoinRoot.mk mu))=0)
   (hQroot:∀ i,Polynomial.aeval (r i) (Q.map (AdjoinRoot.mk mu))=0):
   (∑ i,Module.finrank (AdjoinRoot mu) (E i)) ≤
     m+n-(Polynomial.sylvester
       (P.map (AdjoinRoot.mk mu)) (Q.map (AdjoinRoot.mk mu)) m n).rank:=by
 classical
 let D:I → Polynomial (AdjoinRoot mu):=
   fun i => minpoly (AdjoinRoot mu) (r i)
 have hmonic:∀ i,(D i).Monic:=fun i =>
   minpoly.monic (IsIntegral.of_finite (AdjoinRoot mu) (r i))
 have hcoprime:Pairwise fun i j => IsCoprime (D i) (D j):=by
   exact relative_minpolys_pairwise_coprime_of_relationIdeal_injective
     mu E r hkernels
 have hDp:∀ i,D i∣P.map (AdjoinRoot.mk mu):=fun i =>
   minpoly.dvd (AdjoinRoot mu) (r i) (hProot i)
 have hDq:∀ i,D i∣Q.map (AdjoinRoot.mk mu):=fun i =>
   minpoly.dvd (AdjoinRoot mu) (r i) (hQroot i)
 have hdegree:∀ i,(D i).natDegree=
     Module.finrank (AdjoinRoot mu) (E i):=fun i =>
   (Field.primitive_element_iff_minpoly_natDegree_eq
     (AdjoinRoot mu) (r i)).mp (hgen i)
 have hbound:=sum_common_divisor_natDegrees_le_sylvester_corank
   (P.map (AdjoinRoot.mk mu)) (Q.map (AdjoinRoot.mk mu)) D m n
   (Polynomial.natDegree_map_le.trans hPcap)
   (Polynomial.natDegree_map_le.trans hQcap) hPne
   hmonic hcoprime hDp hDq
 simpa only [hdegree] using hbound
end FixedResiduePolynomial
section MinpolyGrouping
variable {K:Type} [Field K] [DecidableEq K]
 {ι:Type*} [Fintype ι] [DecidableEq ι]
 {I:Type*} [Fintype I]
theorem sum_grouped_weights_le_det_natDegree
   (M:Matrix ι ι (Polynomial K))
   (mu:I → Polynomial K) (relativeDegree:I → ℕ)
   (hmonic:∀ i,(mu i).Monic)
   (hirreducible:∀ i,Irreducible (mu i))
   (fiberCorank:∀ f∈(Finset.univ.image mu),
     (∑ i with mu i=f,relativeDegree i) ≤
       Fintype.card ι-((AdjoinRoot.mk f).mapMatrix M).rank)
   (hdet:M.det≠0):
   (∑ i,relativeDegree i*(mu i).natDegree) ≤ M.det.natDegree:=by
 classical
 let roots:Finset (Polynomial K):=Finset.univ.image mu
 let c:roots → ℕ:=fun f => ∑ i with mu i=f.1,relativeDegree i
 have hrootsMonic:∀ f:roots,(f.1).Monic:=by
   intro f
   obtain ⟨i,_,hi⟩:=Finset.mem_image.mp f.2
   simpa only [hi] using hmonic i
 have hrootsIrreducible:∀ f:roots,Irreducible f.1:=by
   intro f
   obtain ⟨i,_,hi⟩:=Finset.mem_image.mp f.2
   simpa only [hi] using hirreducible i
 have hrootsCoprime:Pairwise fun f g:roots => IsCoprime f.1 g.1:=by
   intro f g hfg
   apply (hrootsIrreducible f).coprime_iff_not_dvd.mpr
   intro hdvd
   have hassociated:=
     (hrootsIrreducible f).associated_of_dvd (hrootsIrreducible g) hdvd
   have heq:f.1=g.1:=Polynomial.eq_of_monic_of_associated
     (hrootsMonic f) (hrootsMonic g) hassociated
   exact hfg (Subtype.ext heq)
 have hc:∀ f:roots,
     c f ≤ Fintype.card ι-((AdjoinRoot.mk f.1).mapMatrix M).rank:=by
   intro f
   exact fiberCorank f.1 f.2
 have houter:=sum_irreducible_coranks_le_det_natDegree
   (K:=K) (I:=roots) M (fun f:roots => f.1) c
     hrootsMonic hrootsIrreducible hrootsCoprime hc hdet
 have hregroup:
     (∑ f:roots,c f*f.1.natDegree)=
       ∑ i,relativeDegree i*(mu i).natDegree:=by
   change (∑ f:roots,
     (∑ i with mu i=f.1,relativeDegree i)*f.1.natDegree)=_
   have hattach:
       (∑ f:roots,
         (∑ i with mu i=f.1,relativeDegree i)*f.1.natDegree)=
       ∑ f∈roots,
         (∑ i with mu i=f,relativeDegree i)*f.natDegree:=by
     rw [show (Finset.univ:Finset roots)=roots.attach from
       Finset.univ_eq_attach roots]
     exact Finset.sum_attach roots (fun f:Polynomial K =>
       (∑ i with mu i=f,relativeDegree i)*f.natDegree)
   rw [hattach]
   simp_rw [Finset.sum_mul]
   calc
     (∑ f∈roots,∑ i with mu i=f,
         relativeDegree i*f.natDegree)=
         ∑ f∈roots,∑ i with mu i=f,
           relativeDegree i*(mu i).natDegree:=by
       apply Finset.sum_congr rfl
       intro f hf
       apply Finset.sum_congr rfl
       intro i hi
       rw [(Finset.mem_filter.mp hi).2]
     _=∑ i∈(Finset.univ:Finset I),
         relativeDegree i*(mu i).natDegree:=
       Finset.sum_fiberwise_of_maps_to
         (s:=Finset.univ) (t:=roots) (g:=mu)
         (fun i _ => Finset.mem_image_of_mem mu (Finset.mem_univ i)) _
     _=∑ i,relativeDegree i*(mu i).natDegree:=by rfl
 rwa [hregroup] at houter
end MinpolyGrouping
section FinitePlaneFamily
variable {K:Type} [Field K] [DecidableEq K]
 {I:Type*} [Fintype I]
 (E:I → Type) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 [∀ i,FiniteDimensional K (E i)]
theorem sum_finrank_le_resultant_of_relationIdeal_injective
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (y r:∀ i,E i)
   (hgen:∀ i,IntermediateField.adjoin K
     ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i =>
     RCN361.relationIdeal K (E i) (y i) (r i)))
   (hProot:∀ i,RCN361.planeEval K (E i)
     (y i) (r i) P=0)
   (hQroot:∀ i,RCN361.planeEval K (E i)
     (y i) (r i) Q=0)
   (hPspecial:∀ f∈
     (Finset.univ.image (fun i => minpoly K (y i))),
       P.map (AdjoinRoot.mk f)≠0)
   (hresultant:Polynomial.resultant P Q m n≠0):
   (∑ i,Module.finrank K (E i)) ≤
     (Polynomial.resultant P Q m n).natDegree:=by
 classical
 let mu:I → Polynomial K:=fun i => minpoly K (y i)
 let relativeDegree:I → ℕ:=fun i =>
   Module.finrank K (E i)/(mu i).natDegree
 have hmuMonic:∀ i,(mu i).Monic:=fun i =>
   minpoly.monic (IsIntegral.of_finite K (y i))
 have hmuIrreducible:∀ i,Irreducible (mu i):=fun i =>
   minpoly.irreducible (IsIntegral.of_finite K (y i))
 have htotal:∀ i,relativeDegree i*(mu i).natDegree=
     Module.finrank K (E i):=by
   intro i
   exact Nat.div_mul_cancel (minpoly_natDegree_dvd_finrank (K:=K) (y i))
 have hfiber:∀ f∈(Finset.univ.image mu),
     (∑ i with mu i=f,relativeDegree i) ≤
       m+n-((AdjoinRoot.mk f).mapMatrix
         (Polynomial.sylvester P Q m n)).rank:=by
   intro f hf
   let J:={i:I//mu i=f}
   have hJnonempty:Nonempty J:=by
     obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hf
     exact ⟨⟨i,hi⟩⟩
   let j₀:J:=Classical.choice hJnonempty
   have hfIrreducible:Irreducible f:=by
     simpa only [←j₀.property] using hmuIrreducible j₀.1
   letI:Fact (Irreducible f):=⟨hfIrreducible⟩
   let fiberBaseHom:∀ j:J,AdjoinRoot f →ₐ[K] E j.1:=fun j =>
     AdjoinRoot.liftAlgHom f (Algebra.ofId K (E j.1)) (y j.1) (by
       change Polynomial.aeval (y j.1) f=0
       calc
         _=Polynomial.aeval (y j.1) (mu j.1):=
           congrArg (Polynomial.aeval (y j.1)) j.property.symm
         _=0:=minpoly.aeval K (y j.1))
   letI:∀ j:J,Algebra (AdjoinRoot f) (E j.1):=
     fun j => (fiberBaseHom j).toRingHom.toAlgebra
   letI:∀ j:J,IsScalarTower K (AdjoinRoot f) (E j.1):=
     fun j => IsScalarTower.of_algebraMap_eq
       (fun c => ((fiberBaseHom j).commutes c).symm)
   letI:∀ j:J,Module.Finite (AdjoinRoot f) (E j.1):=
     fun j => Module.Finite.of_restrictScalars_finite K (AdjoinRoot f) (E j.1)
   letI:FiniteDimensional K (AdjoinRoot f):=
     (AdjoinRoot.powerBasis hfIrreducible.ne_zero).finite
   have hroot (j:J):
       algebraMap (AdjoinRoot f) (E j.1) (AdjoinRoot.root f)=y j.1:=by
     change fiberBaseHom j (AdjoinRoot.root f)=y j.1
     exact AdjoinRoot.liftAlgHom_root f (Algebra.ofId K (E j.1))
       (y j.1) _
   have hgenRelative:∀ j:J,
       IntermediateField.adjoin (AdjoinRoot f)
         ({r j.1}:Set (E j.1))=⊤:=by
     intro j
     exact adjoin_singleton_eq_top_of_pair_eq_top
       (y j.1) (r j.1) (hgen j.1)
         ⟨AdjoinRoot.root f,hroot j⟩
   have hkernelFiber:Function.Injective (fun j:J =>
       RCN361.relationIdeal K (E j.1)
         (algebraMap (AdjoinRoot f) (E j.1) (AdjoinRoot.root f)) (r j.1)):=by
     intro a b hab
     apply Subtype.ext
     apply hkernels
     simpa only [hroot] using hab
   have hProotFiber:∀ j:J,
       Polynomial.aeval (r j.1) (P.map (AdjoinRoot.mk f))=0:=by
     intro j
     rw [←planeEval_quotientRoot_eq_aeval_map,hroot]
     exact hProot j.1
   have hQrootFiber:∀ j:J,
       Polynomial.aeval (r j.1) (Q.map (AdjoinRoot.mk f))=0:=by
     intro j
     rw [←planeEval_quotientRoot_eq_aeval_map,hroot]
     exact hQroot j.1
   have hfixed:=sum_relative_finrank_le_sylvester_corank
     (K:=K) (I:=J) f (fun j:J => E j.1) (fun j => r j.1)
     hgenRelative hkernelFiber P Q m n hPcap hQcap
     (hPspecial f (by simpa only [mu] using hf)) hProotFiber hQrootFiber
   have hbase:Module.finrank K (AdjoinRoot f)=f.natDegree:=by
     change Module.finrank K (Polynomial K ⧸ Ideal.span {f})=f.natDegree
     exact finrank_quotient_span_eq_natDegree
   have hrelative (j:J):relativeDegree j.1=
       Module.finrank (AdjoinRoot f) (E j.1):=by
     change Module.finrank K (E j.1)/(mu j.1).natDegree=_
     rw [j.property, ←Module.finrank_mul_finrank K (AdjoinRoot f) (E j.1),
       hbase]
     exact Nat.mul_div_cancel_left _ hfIrreducible.natDegree_pos
   have hsum:(∑ i with mu i=f,relativeDegree i)=
       ∑ j:J,Module.finrank (AdjoinRoot f) (E j.1):=by
     calc
       _=∑ j:J,relativeDegree j.1:=by
         simpa only [J,Finset.subtype_univ] using
           (Finset.sum_subtype_eq_sum_filter
             (s:=(Finset.univ:Finset I)) relativeDegree
             (p:=fun i => mu i=f)).symm
       _=_:=by
         apply Finset.sum_congr rfl
         intro j _
         exact hrelative j
   rw [hsum]
   simpa only [Fintype.card_fin, ←Polynomial.sylvester_map_map] using hfixed
 have hdet:(Polynomial.sylvester P Q m n).det≠0:=by
   simpa only [Polynomial.resultant] using hresultant
 have hfiber':∀ f∈(Finset.univ.image mu),
     (∑ i with mu i=f,relativeDegree i) ≤
       Fintype.card (Fin (m+n))-((AdjoinRoot.mk f).mapMatrix
         (Polynomial.sylvester P Q m n)).rank:=by
   simpa only [Fintype.card_fin] using hfiber
 have houter:=sum_grouped_weights_le_det_natDegree
   (K:=K) (I:=I) (M:=Polynomial.sylvester P Q m n)
   mu relativeDegree hmuMonic hmuIrreducible hfiber' hdet
 simpa only [Polynomial.resultant,htotal] using houter
theorem sum_finrank_le_planar_bound_without_separability
   (P Q:Polynomial (Polynomial K))
   (hP:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬ P∣Q)
   (y r:∀ i,E i)
   (hgen:∀ i,IntermediateField.adjoin K
     ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i =>
     RCN361.relationIdeal K (E i) (y i) (r i)))
   (hProot:∀ i,RCN361.planeEval K (E i)
     (y i) (r i) P=0)
   (hQroot:∀ i,RCN361.planeEval K (E i)
     (y i) (r i) Q=0):
   (∑ i,Module.finrank K (E i)) ≤
     Q.natDegree*Polynomial.Bivariate.degreeX P+
       P.natDegree*Polynomial.Bivariate.degreeX Q:=by
 classical
 have hspecial:∀ f∈
     (Finset.univ.image (fun i => minpoly K (y i))),
       P.map (AdjoinRoot.mk f)≠0:=by
   intro f hf
   obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hf
   letI:Fact (Irreducible (minpoly K (y i))):=
     ⟨minpoly.irreducible (IsIntegral.of_finite K (y i))⟩
   have hcoeff:Polynomial.eval₂RingHom
       (algebraMap K (AdjoinRoot (minpoly K (y i))))
         (AdjoinRoot.root (minpoly K (y i)))=
       AdjoinRoot.mk (minpoly K (y i)):=by
     apply Polynomial.ringHom_ext
     · intro c
       simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
         AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
     · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,
         AdjoinRoot.mk_X]
   have h:=RCN360.bimap_specialization_ne_zero
     (algebraMap K (AdjoinRoot (minpoly K (y i)))) P
     (hP.isPrimitive (Nat.ne_of_gt hpositive))
     (AdjoinRoot.root (minpoly K (y i)))
   rw [RCN360.bimap_specialization,hcoeff] at h
   exact h
 have hresultant:Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=
   RCN362.irreducible_resultant_ne_zero_of_not_dvd
     P Q hP hpositive hproper
 exact (sum_finrank_le_resultant_of_relationIdeal_injective
   (K:=K) E P Q P.natDegree Q.natDegree le_rfl le_rfl y r hgen
     hkernels hProot hQroot hspecial hresultant).trans
       (bivariate_resultant_natDegree_le
         (F:=K) P Q P.natDegree Q.natDegree)
end FinitePlaneFamily
end
end ProximityPrize.SubmissionLower.RCN025
end PackedLegacy_DF

/-! Packed from ProximityPrize.SubmissionLower.AW. -/
section PackedLegacy_AW
namespace ProximityPrize.SubmissionLower.RCN008
open scoped Classical BigOperators
open RCN002 RCN005
 RCN371 RCN011
 RCN009 RCN013 RCN010
 RCN024
 RCN025
noncomputable section
variable (K:Type) [Field K]
private def familyFiniteSummary {I:Type} [Fintype I]
   (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
   (A:∀ i,Algebra (RatFunc K) (CoordinateField K (P i))) (B:ℕ):Prop:=
 letI:=A
 (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i)))∧
   (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤ B
theorem rationalBaseAlgebra_congr
   (P:Ideal (Original K)) [P.IsPrime]
   (i j:Fin 3) (hij:i=j)
   (hi:Transcendental K (coordinate K P i))
   (hj:Transcendental K (coordinate K P j)):
   rationalBaseAlgebra K P i hi=rationalBaseAlgebra K P j hj:=by
 subst j
 rfl
theorem plane_budget_le_original (order:Fin 3 ≃ Fin 3) (G H:Original K):
   (planeMap K order H).natDegree*
         Polynomial.Bivariate.degreeX (planeMap K order G)+
       (planeMap K order G).natDegree*
         Polynomial.Bivariate.degreeX (planeMap K order H) ≤
     originalMixedDegree K order G H:=
 Nat.add_le_add
   (Nat.mul_le_mul (planeMap_natDegree_le K order H)
     (planeMap_degreeX_le K order G))
   (Nat.mul_le_mul (planeMap_natDegree_le K order G)
     (planeMap_degreeX_le K order H))
section FixedOrder
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
theorem actual_finite_sum_finrank_bound_without_separability
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P) (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i)
   (hHmem:∀ i,H∈P i) (hproper:¬ G∣H)
   (hpositive:0 < (planeMap K order G).natDegree):
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
     fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
   (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i)))∧
     (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
       (planeMap K order H).natDegree*
           Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*
           Polynomial.Bivariate.degreeX (planeMap K order H):=by
 classical
 letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
   fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   have hirr:Irreducible (planeMap K order G):=
     planeMap_irreducible_of_component
       (K:=K) (order:=order) (P:=P i₀) (ht:=ht i₀)
         G hG (hGmem i₀)
   have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
     intro hdiv
     exact hproper ((planeMap_dvd_iff_of_component
       (K:=K) (order:=order) (P:=P i₀) (ht:=ht i₀)
         G H hG (hGmem i₀)).mp hdiv)
   have hGroots:∀ i,
       RCN361.planeEval (RatFunc K)
         (CoordinateField K (P i))
         (coordinate K (P i) (order 2))
         (coordinate K (P i) (order 1)) (planeMap K order G)=0:=by
     intro i
     change actualPlaneEvaluation K order (P i) (ht i)
       (planeMap K order G)=0
     exact (actualPlane_root_iff K order (P i) (ht i) G).mpr (hGmem i)
   have hHroots:∀ i,
       RCN361.planeEval (RatFunc K)
         (CoordinateField K (P i))
         (coordinate K (P i) (order 2))
         (coordinate K (P i) (order 1)) (planeMap K order H)=0:=by
     intro i
     change actualPlaneEvaluation K order (P i) (ht i)
       (planeMap K order H)=0
     exact (actualPlane_root_iff K order (P i) (ht i) H).mpr (hHmem i)
   have hfinite:∀ i,
       FiniteDimensional (RatFunc K) (CoordinateField K (P i)):=by
     intro i
     have hGeval:Polynomial.eval₂
         (Polynomial.eval₂RingHom
           (algebraMap (RatFunc K) (CoordinateField K (P i)))
           (coordinate K (P i) (order 2)))
         (coordinate K (P i) (order 1)) (planeMap K order G)=0:=by
       rw [←RCN365.planeEval_eq_eval₂]
       exact hGroots i
     have hHeval:Polynomial.eval₂
         (Polynomial.eval₂RingHom
           (algebraMap (RatFunc K) (CoordinateField K (P i)))
           (coordinate K (P i) (order 2)))
         (coordinate K (P i) (order 1)) (planeMap K order H)=0:=by
       rw [←RCN365.planeEval_eq_eval₂]
       exact hHroots i
     exact finite_of_proper_plane_roots
       (planeMap K order G) (planeMap K order H)
       hirr hpositive hproperPlane
       (coordinate K (P i) (order 2))
       (coordinate K (P i) (order 1))
       hGeval hHeval (actual_generators K order (P i) (ht i))
   letI:∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i)):=
     hfinite
   have hkernels:Function.Injective (fun i =>
       RCN361.relationIdeal (RatFunc K)
         (CoordinateField K (P i))
         (coordinate K (P i) (order 2))
         (coordinate K (P i) (order 1))):=by
     change Function.Injective (fun i =>
       actualRelationKernel K order (P i) (ht i))
     exact actualRelationKernel_family_injective K order P ht hinj
   constructor
   · exact hfinite
   · exact sum_finrank_le_planar_bound_without_separability
       (K:=RatFunc K) (I:=I)
       (fun i => CoordinateField K (P i))
       (planeMap K order G) (planeMap K order H)
       hirr hpositive hproperPlane
       (fun i => coordinate K (P i) (order 2))
       (fun i => coordinate K (P i) (order 1))
       (fun i => actual_generators K order (P i) (ht i))
       hkernels hGroots hHroots
 · letI:IsEmpty I:=⟨fun i => hI ⟨i⟩⟩
   constructor
   · intro i
     exact isEmptyElim i
   · simp
end FixedOrder
section OriginalOrder
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (P:I → Ideal (Original K)) [∀ i,(P i).IsPrime]
theorem original_finite_sum_finrank_bound_without_separability
   (ht:∀ i,Transcendental K (coordinate K (P i) (order 0)))
   (hinj:Function.Injective P) (G H:Original K)
   (hG:Irreducible G) (hGmem:∀ i,G∈P i)
   (hHmem:∀ i,H∈P i) (hproper:¬ G∣H):
   letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
     fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
   (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i)))∧
     (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
       originalMixedDegree K order G H:=by
 classical
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   obtain ⟨order',hor,hbase,hpositive⟩:=
     exists_positive_outer_order K order (P i₀) G hG (hGmem i₀) (ht i₀)
   have hbudget:originalMixedDegree K order' G H=
       originalMixedDegree K order G H:=by
     rcases hor with rfl | rfl
     · rfl
     · exact originalMixedDegree_swap K order G H
   have ht':∀ i,
       Transcendental K (coordinate K (P i) (order' 0)):=by
     intro i
     simpa only [hbase] using ht i
   have hresult:
       letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
         fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
       (∀ i,FiniteDimensional (RatFunc K) (CoordinateField K (P i)))∧
         (∑ i,Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
           originalMixedDegree K order' G H:=by
     letI:∀ i,Algebra (RatFunc K) (CoordinateField K (P i)):=
       fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
     obtain ⟨hfinite,hbound⟩:=
       actual_finite_sum_finrank_bound_without_separability
         K order' P ht' hinj G H hG hGmem hHmem hproper hpositive
     exact ⟨hfinite,hbound.trans (plane_budget_le_original K order' G H)⟩
   have halg:
       (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))=
         (fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)):=by
     funext i
     exact rationalBaseAlgebra_congr K (P i) (order' 0) (order 0)
       hbase (ht' i) (ht i)
   change familyFiniteSummary K P
     (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))
       (originalMixedDegree K order' G H) at hresult
   rw [halg,hbudget] at hresult
   exact hresult
 · letI:IsEmpty I:=⟨fun i => hI ⟨i⟩⟩
   constructor
   · intro i
     exact isEmptyElim i
   · simp
end OriginalOrder
end
end ProximityPrize.SubmissionLower.RCN008
end PackedLegacy_AW

/-! Packed from ProximityPrize.SubmissionLower.X7. -/
section PackedLegacy_X7
namespace ProximityPrize.SubmissionLower.RCN021
open scoped Classical BigOperators
open RCN371 RCN011
 RCN009 RCN013
 RCN008
 RCN024
 RCN025 RCN022
noncomputable section
set_option maxHeartbeats 1000000
variable (K:Type) [Field K]
attribute [local instance] MvPolynomial.algebraMvPolynomial
local instance:IsLocalization (coefficientDenominators K)
   (RationalPolynomials K):=
 MvPolynomial.isLocalization (nonZeroDivisors (Polynomial K)) (RatFunc K)
section OneEvaluation
variable (L:Type) [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3) (e:Original K →ₐ[K] L)
def collectedEvaluation:Collected K →+*L:=
 e.toRingHom.comp (collect K order).symm.toRingHom
@[simp] theorem collectedEvaluation_collect (F:Original K):
   collectedEvaluation K L order e (collect K order F)=e F:=by
 simp [collectedEvaluation]
@[simp] theorem collectedEvaluation_C (H:Polynomial K):
   collectedEvaluation K L order e (MvPolynomial.C H)=
     Polynomial.aeval (e (MvPolynomial.X (order 0))) H:=by
 have hhom:e.toRingHom.comp (coefficientLift K order)=
     (Polynomial.aeval (e (MvPolynomial.X (order 0)))).toRingHom:=by
   apply Polynomial.ringHom_ext
   · intro a
     change e (coefficientLift K order (Polynomial.C a))=
       Polynomial.aeval (e (MvPolynomial.X (order 0))) (Polynomial.C a)
     rw [coefficientLift_C,Polynomial.aeval_C]
     exact e.commutes a
   · change e (coefficientLift K order Polynomial.X)=
       Polynomial.aeval (e (MvPolynomial.X (order 0))) Polynomial.X
     rw [coefficientLift_X,Polynomial.aeval_X]
 exact RingHom.congr_fun hhom H
theorem coefficientDenominators_disjoint_of_evaluation
   (G:Original K) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   Disjoint (coefficientDenominators K:Set (Collected K))
     (Ideal.span ({collect K order G}:Set (Collected K)):Set (Collected K)):=by
 rw [Set.disjoint_left]
 intro a ha hI
 obtain ⟨H,hH,rfl⟩:=Submonoid.mem_map.mp ha
 have hH0:H≠0:=mem_nonZeroDivisors_iff_ne_zero.mp hH
 obtain ⟨U,hU⟩:=Ideal.mem_span_singleton.mp hI
 have hzero:Polynomial.aeval (e (MvPolynomial.X (order 0))) H=0:=by
   have heval:=congrArg (collectedEvaluation K L order e) hU
   simpa only [map_mul,collectedEvaluation_collect,collectedEvaluation_C,
     hroot,zero_mul] using heval
 exact hH0 (transcendental_iff.mp ht H hzero)
theorem rationalMap_irreducible_of_evaluation
   (G:Original K) (hG:Irreducible G) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   Irreducible (rationalMap K order G):=by
 have hp:=IsLocalization.isPrime_of_isPrime_disjoint
   (coefficientDenominators K) (RationalPolynomials K)
   (Ideal.span ({collect K order G}:Set (Collected K)))
   (collected_principal_isPrime K order G hG)
   (coefficientDenominators_disjoint_of_evaluation K L order e G hroot ht)
 have hp':
     (Ideal.span ({rationalMap K order G}:Set (RationalPolynomials K))).IsPrime:=by
   simpa only [Ideal.map_span,Set.image_singleton, ←rationalMap_eq] using hp
 exact ((Ideal.span_singleton_prime
   (rationalMap_ne_zero K order G hG.ne_zero)).mp hp').irreducible
theorem rationalMap_dvd_iff_of_evaluation
   (G H:Original K) (hG:Irreducible G) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   rationalMap K order G∣rationalMap K order H ↔ G∣H:=by
 constructor
 · intro hdiv
   have hm:algebraMap (Collected K) (RationalPolynomials K) (collect K order H)∈
       Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
         (Ideal.span ({collect K order G}:Set (Collected K))):=by
     simpa only [Ideal.map_span,Set.image_singleton,Ideal.mem_span_singleton,
       ←rationalMap_eq] using hdiv
   have hu:collect K order H∈
       (Ideal.map (algebraMap (Collected K) (RationalPolynomials K))
         (Ideal.span ({collect K order G}:Set (Collected K)))).under (Collected K):=hm
   rw [IsLocalization.under_map_of_isPrime_disjoint (coefficientDenominators K)
     (RationalPolynomials K) (collected_principal_isPrime K order G hG)
     (coefficientDenominators_disjoint_of_evaluation K L order e G hroot ht)] at hu
   obtain ⟨U,hU⟩:=Ideal.mem_span_singleton.mp hu
   refine ⟨(collect K order).symm U,?_⟩
   apply (collect K order).injective
   simpa only [map_mul,AlgEquiv.apply_symm_apply] using hU
 · exact fun hdiv↦map_dvd (rationalMap K order) hdiv
theorem planeMap_irreducible_of_evaluation
   (G:Original K) (hG:Irreducible G) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   Irreducible (planeMap K order G):=
 (MulEquiv.irreducible_iff (bivariateEquiv (RatFunc K))).mpr
   (rationalMap_irreducible_of_evaluation K L order e G hG hroot ht)
theorem planeMap_dvd_iff_of_evaluation
   (G H:Original K) (hG:Irreducible G) (hroot:e G=0)
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   planeMap K order G∣planeMap K order H ↔ G∣H:=by
 constructor
 · rintro ⟨U,hU⟩
   have hrat:rationalMap K order G∣rationalMap K order H:=by
     refine ⟨(bivariateEquiv (RatFunc K)).symm U,?_⟩
     apply (bivariateEquiv (RatFunc K)).injective
     change bivariateEquiv (RatFunc K) (rationalMap K order H)=
       bivariateEquiv (RatFunc K) (rationalMap K order G)*U at hU
     simpa only [map_mul,AlgEquiv.apply_symm_apply] using hU
   exact (rationalMap_dvd_iff_of_evaluation K L order e G H hG hroot ht).mp hrat
 · exact fun hdiv↦map_dvd (planeMap K order) hdiv
def planeEvaluation
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   PlaneRing K →+*L:=
 (Polynomial.evalRingHom (e (MvPolynomial.X (order 1)))).comp
   (Polynomial.mapRingHom
     (Polynomial.eval₂RingHom
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom
       (e (MvPolynomial.X (order 2)))))
@[simp] theorem planeEvaluation_C_C
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))) (a:RatFunc K):
   planeEvaluation K L order e ht (Polynomial.C (Polynomial.C a))=
     elementEmbedding K L (e (MvPolynomial.X (order 0))) ht a:=by
 simp [planeEvaluation]
@[simp] theorem planeEvaluation_X
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   planeEvaluation K L order e ht Polynomial.X=
     e (MvPolynomial.X (order 1)):=by
 simp [planeEvaluation]
@[simp] theorem planeEvaluation_C_X
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   planeEvaluation K L order e ht (Polynomial.C Polynomial.X)=
     e (MvPolynomial.X (order 2)):=by
 simp [planeEvaluation]
theorem elementEmbedding_polynomial (s:L) (hs:Transcendental K s)
   (f:Polynomial K):
   elementEmbedding K L s hs (algebraMap (Polynomial K) (RatFunc K) f)=
     Polynomial.aeval s f:=
 RatFunc.liftRingHom_algebraMap _ _ f
theorem planeEvaluation_comp_planeMap
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   (planeEvaluation K L order e ht).comp (planeMap K order)=e.toRingHom:=by
 apply MvPolynomial.ringHom_ext
 · intro a
   simp only [RingHom.comp_apply]
   rw [planeMap_C,planeEvaluation_C_C,
     elementEmbedding_polynomial,Polynomial.aeval_C]
   exact (e.commutes a).symm
 · intro i
   obtain ⟨j,rfl⟩:=order.surjective i
   by_cases hj:j=0
   · subst j
     simp only [RingHom.comp_apply]
     rw [planeMap_X_first,planeEvaluation_C_C,
       elementEmbedding_variable]
     rfl
   by_cases hj':j=1
   · subst j
     simp only [RingHom.comp_apply]
     rw [planeMap_X_outer,planeEvaluation_X]
     rfl
   have hjtwo:j=2:=by
     apply Fin.ext
     have hjlt:=j.isLt
     have hjzero:j.val≠0:=fun h↦hj (Fin.ext h)
     have hjone:j.val≠1:=fun h↦hj' (Fin.ext h)
     omega
   subst j
   simp only [RingHom.comp_apply]
   rw [planeMap_X_inner,planeEvaluation_C_X]
   rfl
def relationKernel
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   Ideal (PlaneRing K):=RingHom.ker (planeEvaluation K L order e ht)
theorem relationKernel_contract
   (ht:Transcendental K (e (MvPolynomial.X (order 0)))):
   (relationKernel K L order e ht).comap (planeMap K order)=
     RingHom.ker e.toRingHom:=by
 rw [relationKernel,RingHom.comap_ker,planeEvaluation_comp_planeMap]
end OneEvaluation
section FixedFamily
variable (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
 (E:I → Type)
 [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
 (e:∀ i,Original K →ₐ[K] E i)
theorem finite_sum_finrank_bound
   (ht:∀ i,Transcendental K (e i (MvPolynomial.X (order 0))))
   (hgen:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e i (MvPolynomial.X (order 2)),e i (MvPolynomial.X (order 1))}:
         Set (E i))=⊤)
   (hkernels:Function.Injective (fun i↦RingHom.ker (e i).toRingHom))
   (G H:Original K) (hG:Irreducible G)
   (hGroot:∀ i,e i G=0) (hHroot:∀ i,e i H=0)
   (hproper:¬ G∣H) (hpositive:0 < (planeMap K order G).natDegree):
   letI:∀ i,Algebra (RatFunc K) (E i):=fun i↦
     (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
   (∀ i,FiniteDimensional (RatFunc K) (E i))∧
     (∑ i,Module.finrank (RatFunc K) (E i)) ≤
       (planeMap K order H).natDegree*
           Polynomial.Bivariate.degreeX (planeMap K order G)+
         (planeMap K order G).natDegree*
           Polynomial.Bivariate.degreeX (planeMap K order H):=by
 classical
 letI:∀ i,Algebra (RatFunc K) (E i):=fun i↦
   (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   have hirr:Irreducible (planeMap K order G):=
     planeMap_irreducible_of_evaluation K (E i₀) order (e i₀)
       G hG (hGroot i₀) (ht i₀)
   have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
     intro hdiv
     exact hproper ((planeMap_dvd_iff_of_evaluation K (E i₀) order (e i₀)
       G H hG (hGroot i₀) (ht i₀)).mp hdiv)
   have hGroots:∀ i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
     intro i
     change planeEvaluation K (E i) order (e i) (ht i) (planeMap K order G)=0
     rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
     exact hGroot i
   have hHroots:∀ i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order H)=0:=by
     intro i
     change planeEvaluation K (E i) order (e i) (ht i) (planeMap K order H)=0
     rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
     exact hHroot i
   have hfinite:∀ i,FiniteDimensional (RatFunc K) (E i):=by
     intro i
     have hGeval:Polynomial.eval₂
         (Polynomial.eval₂RingHom (algebraMap (RatFunc K) (E i))
           (e i (MvPolynomial.X (order 2))))
         (e i (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
       rw [←RCN365.planeEval_eq_eval₂]
       exact hGroots i
     have hHeval:Polynomial.eval₂
         (Polynomial.eval₂RingHom (algebraMap (RatFunc K) (E i))
           (e i (MvPolynomial.X (order 2))))
         (e i (MvPolynomial.X (order 1))) (planeMap K order H)=0:=by
       rw [←RCN365.planeEval_eq_eval₂]
       exact hHroots i
     exact finite_of_proper_plane_roots (planeMap K order G) (planeMap K order H)
       hirr hpositive hproperPlane
       (e i (MvPolynomial.X (order 2))) (e i (MvPolynomial.X (order 1)))
       hGeval hHeval (hgen i)
   letI:∀ i,FiniteDimensional (RatFunc K) (E i):=hfinite
   have hrelation:Function.Injective (fun i↦
       RCN361.relationIdeal (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1)))):=by
     intro i j hij
     apply hkernels
     change relationKernel K (E i) order (e i) (ht i)=
       relationKernel K (E j) order (e j) (ht j) at hij
     have hc:=congrArg (Ideal.comap (planeMap K order)) hij
     simpa only [relationKernel_contract] using hc
   exact ⟨hfinite,
     sum_finrank_le_planar_bound_without_separability
       (K:=RatFunc K) (I:=I) E
       (planeMap K order G) (planeMap K order H)
       hirr hpositive hproperPlane
       (fun i↦e i (MvPolynomial.X (order 2)))
       (fun i↦e i (MvPolynomial.X (order 1))) hgen
       hrelation hGroots hHroots⟩
 · letI:IsEmpty I:=⟨fun i↦hI ⟨i⟩⟩
   exact ⟨fun i↦isEmptyElim i,by simp⟩
end FixedFamily
end
end ProximityPrize.SubmissionLower.RCN021
end PackedLegacy_X7

/-! Packed from ProximityPrize.SubmissionLower.EE. -/
section PackedLegacy_EE
namespace ProximityPrize.SubmissionLower.RCN124
open scoped Classical BigOperators
open RCN371 RCN011
 RCN009 RCN013
 RCN008
 RCN024
 RCN025 RCN022
 RCN021 RCN012
noncomputable section
theorem sum_finrank_le_ordinary_resultant_without_separability
   {F:Type} [Field F] {I:Type*} [Fintype I]
   (E:I → Type) [∀ i,Field (E i)] [∀ i,Algebra F (E i)]
   [∀ i,FiniteDimensional F (E i)]
   (P Q:Polynomial (Polynomial F))
   (hP:Irreducible P) (hpositive:0 < P.natDegree)
   (hproper:¬ P∣Q)
   (y r:∀ i,E i)
   (hgen:∀ i,IntermediateField.adjoin F
     ({y i,r i}:Set (E i))=⊤)
   (hkernels:Function.Injective (fun i↦
     RCN361.relationIdeal F (E i) (y i) (r i)))
   (hProot:∀ i,RCN361.planeEval F (E i)
     (y i) (r i) P=0)
   (hQroot:∀ i,RCN361.planeEval F (E i)
     (y i) (r i) Q=0):
   (∑ i,Module.finrank F (E i)) ≤
     (Polynomial.resultant P Q).natDegree:=by
 classical
 letI:DecidableEq F:=Classical.decEq F
 have hspecial:∀ f∈
     (Finset.univ.image (fun i↦minpoly F (y i))),
       P.map (AdjoinRoot.mk f)≠0:=by
   intro f hf
   obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hf
   letI:Fact (Irreducible (minpoly F (y i))):=
     ⟨minpoly.irreducible (IsIntegral.of_finite F (y i))⟩
   have hcoeff:Polynomial.eval₂RingHom
       (algebraMap F (AdjoinRoot (minpoly F (y i))))
         (AdjoinRoot.root (minpoly F (y i)))=
       AdjoinRoot.mk (minpoly F (y i)):=by
     apply Polynomial.ringHom_ext
     · intro c
       simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
         AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
     · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,
         AdjoinRoot.mk_X]
   have h:=RCN360.bimap_specialization_ne_zero
     (algebraMap F (AdjoinRoot (minpoly F (y i)))) P
     (hP.isPrimitive (Nat.ne_of_gt hpositive))
     (AdjoinRoot.root (minpoly F (y i)))
   rw [RCN360.bimap_specialization,hcoeff] at h
   exact h
 have hresultant:Polynomial.resultant P Q P.natDegree Q.natDegree≠0:=
   RCN362.irreducible_resultant_ne_zero_of_not_dvd
     P Q hP hpositive hproper
 simpa only using
   (sum_finrank_le_resultant_of_relationIdeal_injective
     (K:=F) E P Q P.natDegree Q.natDegree le_rfl le_rfl y r hgen
       hkernels hProot hQroot hspecial hresultant)
variable (K:Type) [Field K]
theorem finite_sum_finrank_bound_trapezoid
   (order:Fin 3 ≃ Fin 3) {I:Type} [Fintype I]
   (E:I → Type)
   [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
   (e:∀ i,Original K →ₐ[K] E i)
   (ht:∀ i,Transcendental K (e i (MvPolynomial.X (order 0))))
   (hgen:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
         (ht i)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e i (MvPolynomial.X (order 2)),e i (MvPolynomial.X (order 1))}:
         Set (E i))=⊤)
   (hkernels:Function.Injective (fun i↦RingHom.ker (e i).toRingHom))
   (G H:Original K) (hG:Irreducible G)
   (hGroot:∀ i,e i G=0) (hHroot:∀ i,e i H=0)
   (hproper:¬ G∣H) (hpositive:0 < (planeMap K order G).natDegree)
   (n mCap totalG totalH cap:ℕ) (hHne:H≠0)
   (hGouter:(planeMap K order G).natDegree ≤ n)
   (hHouter:(planeMap K order H).natDegree ≤ mCap)
   (hGsupport:∀ d∈(rationalMap K order G).support,
     d 0+d 1 ≤ totalG)
   (hHsupport:∀ d∈(rationalMap K order H).support,
     d 0+d 1 ≤ totalH)
   (hbudget:∀ m,m ≤ mCap →
     m*totalG+n*totalH-m*n ≤ cap):
   letI:∀ i,Algebra (RatFunc K) (E i):=fun i↦
     (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
       (ht i)).toRingHom.toAlgebra
   (∀ i,FiniteDimensional (RatFunc K) (E i))∧
     (∑ i,Module.finrank (RatFunc K) (E i)) ≤ cap:=by
 classical
 letI:∀ i,Algebra (RatFunc K) (E i):=fun i↦
   (elementEmbedding K (E i) (e i (MvPolynomial.X (order 0)))
     (ht i)).toRingHom.toAlgebra
 by_cases hI:Nonempty I
 · let i₀:I:=Classical.choice hI
   have hirr:Irreducible (planeMap K order G):=
     planeMap_irreducible_of_evaluation K (E i₀) order (e i₀)
       G hG (hGroot i₀) (ht i₀)
   have hproperPlane:¬ planeMap K order G∣planeMap K order H:=by
     intro hdiv
     exact hproper ((planeMap_dvd_iff_of_evaluation K (E i₀) order (e i₀)
       G H hG (hGroot i₀) (ht i₀)).mp hdiv)
   have hbase:=finite_sum_finrank_bound K order E e ht hgen hkernels
     G H hG hGroot hHroot hproper hpositive
   have hfinite:∀ i,FiniteDimensional (RatFunc K) (E i):=hbase.1
   letI:∀ i,FiniteDimensional (RatFunc K) (E i):=hfinite
   have hGroots:∀ i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
     intro i
     change planeEvaluation K (E i) order (e i) (ht i)
       (planeMap K order G)=0
     rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
     exact hGroot i
   have hHroots:∀ i,
       RCN361.planeEval (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1))) (planeMap K order H)=0:=by
     intro i
     change planeEvaluation K (E i) order (e i) (ht i)
       (planeMap K order H)=0
     rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
     exact hHroot i
   have hrelation:Function.Injective (fun i↦
       RCN361.relationIdeal (RatFunc K) (E i)
         (e i (MvPolynomial.X (order 2)))
         (e i (MvPolynomial.X (order 1)))):=by
     intro i j hij
     apply hkernels
     change relationKernel K (E i) order (e i) (ht i)=
       relationKernel K (E j) order (e j) (ht j) at hij
     have hc:=congrArg (Ideal.comap (planeMap K order)) hij
     simpa only [relationKernel_contract] using hc
   refine ⟨hfinite,?_⟩
   exact (sum_finrank_le_ordinary_resultant_without_separability E
     (planeMap K order G) (planeMap K order H) hirr hpositive hproperPlane
     (fun i↦e i (MvPolynomial.X (order 2)))
     (fun i↦e i (MvPolynomial.X (order 1))) hgen hrelation
     hGroots hHroots).trans
       (planeMap_trapezoid_resultant_natDegree_le K order G H
         n mCap totalG totalH cap hHne hGouter hHouter
         hGsupport hHsupport hbudget)
 · letI:IsEmpty I:=⟨fun i↦hI ⟨i⟩⟩
   exact ⟨fun i↦isEmptyElim i,by simp⟩
end
end ProximityPrize.SubmissionLower.RCN124
end PackedLegacy_EE

/-! Packed from ProximityPrize.SubmissionLower.Y7. -/
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
def affineU (lam:K):CoordinateField K P:=
 coordinate K P 0+lam • coordinate K P 2
def affineV (μ ν:K):CoordinateField K P:=
 coordinate K P 1+μ • coordinate K P 0+ν • coordinate K P 2
def flagEvaluation (lam μ ν:K):
   MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K P:=
 MvPolynomial.aeval ![affineU K P lam,affineV K P μ ν,
   coordinate K P 2]
@[simp] theorem flagEvaluation_X_zero (lam μ ν:K):
   flagEvaluation K P lam μ ν (MvPolynomial.X 0)=affineU K P lam:=by
 simp [flagEvaluation]
@[simp] theorem flagEvaluation_X_one (lam μ ν:K):
   flagEvaluation K P lam μ ν (MvPolynomial.X 1)=affineV K P μ ν:=by
 simp [flagEvaluation]
@[simp] theorem flagEvaluation_X_two (lam μ ν:K):
   flagEvaluation K P lam μ ν (MvPolynomial.X 2)=coordinate K P 2:=by
 simp [flagEvaluation]
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
theorem exists_common_exact_finite_separable_shear
   (embeddingZ:∀ i,RatFunc K →ₐ[K] E i)
   (hvalueZ:∀ i,embeddingZ i
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=z i)
   (hfiniteZ:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (embeddingZ i).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) (E i))
   (hsepZ:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (embeddingZ i).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc K) (E i)):
   ∃ a:K,a≠0∧∀ i,
     ∃ hs:Transcendental K (r i+a • z i),
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) hs).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc K) (E i))∧
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) hs).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc K) (E i))∧
       (∀ v∈W i,v.val (r i+a • z i)=
         max (v.val (r i)) (v.val (z i))):=by
 have hdz:∀ i,D K (E i) (z i)≠0:=by
   intro i
   have h:=parameterDifferential_ne_zero_of_isSeparable
     K (E i) (embeddingZ i) (hfiniteZ i) (hsepZ i)
   unfold RCN369.parameterDifferential at h
   rwa [hvalueZ i] at h
 let J:=I ⊕ Σ i:I,{v//v∈W i}
 let Bad:J → K → Prop
   | Sum.inl i,a => D K (E i) (r i)+a • D K (E i) (z i)=0
   | Sum.inr iv,a => iv.2.1.val (r iv.1+a • z iv.1) <
       max (iv.2.1.val (r iv.1)) (iv.2.1.val (z iv.1))
 have hsingle:∀ j {a b},Bad j a → Bad j b → a=b:=by
   intro j a b ha hb
   rcases j with i | ⟨i,v⟩
   · exact shear_bad_coefficient_subsingleton K (E i) (r i) (z i)
       (hdz i) ha hb
   · exact valuation_shear_bad_coefficient_subsingleton v.1 (r i) (z i) ha hb
 obtain ⟨a,ha0,havoid⟩:=
   exists_nonzero_avoiding_finite_subsingleton Bad hsingle
 refine ⟨a,ha0,fun i↦?_⟩
 have hdiff:D K (E i) (r i)+a • D K (E i) (z i)≠0:=by
   exact havoid (Sum.inl i)
 obtain ⟨hs,hfinite,hsep⟩:=
   shear_transcendental_finite_separable_of_differential_ne_zero
     K (E i) (embeddingZ i) (r i) (z i) a
       (hvalueZ i) (hfiniteZ i) (hsepZ i) hdiff
 refine ⟨hs,hfinite,hsep,?_⟩
 intro v hv
 have hnotlt:=havoid (Sum.inr ⟨i,⟨v,hv⟩⟩)
 have hupper:=v.val.map_add (r i) (a • z i)
 have haz:v.val (a • z i)=v.val (z i):=by
   letI:v.val.IsTrivialOn K:=v.property.2
   rw [Algebra.smul_def,map_mul,
     Valuation.IsTrivialOn.eq_one a ha0,one_mul]
 rw [haz] at hupper
 exact le_antisymm hupper (le_of_not_gt hnotlt)
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
theorem exists_nestedFlagProjectionData
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 2))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1):
   Nonempty (NestedFlagProjectionData hseparator hproj):=by
 classical
 let E:RegularComponent Ω G T H → Type:=
   fun C↦CoordinateField Ω C.1
 let rY:∀ C,E C:=fun C↦coordinate Ω C.1 0
 let z:∀ C,E C:=fun C↦coordinate Ω C.1 2
 let W:∀ C,Finset
     (RCN345.NormalizedValuation Ω (E C)):=
   fun C↦componentRelevantPlaces hseparator hproj C
 let embeddingZ:∀ C,RatFunc Ω →ₐ[Ω] E C:=
   fun C↦rationalBaseEmbedding Ω C.1 2 (hseparator C)
 have hvalueZ:∀ C,embeddingZ C
     (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X)=z C:=by
   intro C
   exact rationalBaseEmbedding_polynomial Ω C.1 2 (hseparator C) Polynomial.X
     |>.trans (Polynomial.aeval_X _)
 have hfiniteZ:∀ C,
     letI:Algebra (RatFunc Ω) (E C):=
       (embeddingZ C).toRingHom.toAlgebra
     FiniteDimensional (RatFunc Ω) (E C):=by
   intro C
   exact (hproj C 2 (hseparator C)).1
 have hsepZ:∀ C,
     letI:Algebra (RatFunc Ω) (E C):=
       (embeddingZ C).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc Ω) (E C):=by
   intro C
   exact (hproj C 2 (hseparator C)).2
 obtain ⟨lam,hlam0,hlam⟩:=
   exists_common_exact_finite_separable_shear E rY z W
     embeddingZ hvalueZ hfiniteZ hsepZ
 let hU:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (affineU Ω C.1 lam):=
   fun C↦Classical.choose (hlam C)
 have hUdata:∀ C,
     (letI:Algebra (RatFunc Ω) (E C):=
         (elementEmbedding Ω (E C) (affineU Ω C.1 lam)
           (hU C)).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc Ω) (E C))∧
     (letI:Algebra (RatFunc Ω) (E C):=
         (elementEmbedding Ω (E C) (affineU Ω C.1 lam)
           (hU C)).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc Ω) (E C))∧
     ∀ v∈W C,v.val (affineU Ω C.1 lam)=
       max (v.val (coordinate Ω C.1 0))
         (v.val (coordinate Ω C.1 2)):=by
   intro C
   have hp:hU C=Classical.choose (hlam C):=Subsingleton.elim _ _
   cases hp
   simpa only [E,rY,z,affineU,hU] using! Classical.choose_spec (hlam C)
 let rS:∀ C,E C:=fun C↦coordinate Ω C.1 1
 let u:∀ C,E C:=fun C↦affineU Ω C.1 lam
 let embeddingU:∀ C,RatFunc Ω →ₐ[Ω] E C:=fun C↦
   elementEmbedding Ω (E C) (u C) (hU C)
 have hvalueU:∀ C,embeddingU C
     (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X)=u C:=by
   intro C
   exact elementEmbedding_variable Ω (E C) (u C) (hU C)
 have hfiniteU:∀ C,
     letI:Algebra (RatFunc Ω) (E C):=
       (embeddingU C).toRingHom.toAlgebra
     FiniteDimensional (RatFunc Ω) (E C):=fun C↦(hUdata C).1
 have hsepU:∀ C,
     letI:Algebra (RatFunc Ω) (E C):=
       (embeddingU C).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc Ω) (E C):=fun C↦(hUdata C).2.1
 obtain ⟨mu,hmu0,hmu⟩:=
   exists_common_exact_finite_separable_shear E rS u W
     embeddingU hvalueU hfiniteU hsepU
 let hV:∀ C:RegularComponent Ω G T H,Transcendental Ω
     (coordinate Ω C.1 1+mu • affineU Ω C.1 lam):=
   fun C↦Classical.choose (hmu C)
 have hVdata:∀ C,
     (letI:Algebra (RatFunc Ω) (E C):=
         (elementEmbedding Ω (E C)
           (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)
           (hV C)).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc Ω) (E C))∧
     (letI:Algebra (RatFunc Ω) (E C):=
         (elementEmbedding Ω (E C)
           (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)
           (hV C)).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc Ω) (E C))∧
     ∀ v∈W C,
       v.val (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)=
         max (v.val (coordinate Ω C.1 1))
           (v.val (affineU Ω C.1 lam)):=by
   intro C
   have hp:hV C=Classical.choose (hmu C):=Subsingleton.elim _ _
   cases hp
   simpa only [E,rS,u,hV] using! Classical.choose_spec (hmu C)
 exact ⟨⟨lam,hlam0,hU,
   (fun C↦(hUdata C).1),(fun C↦(hUdata C).2.1),
   (fun C↦(hUdata C).2.2),
   mu,hmu0,hV,
   (fun C↦(hVdata C).1),(fun C↦(hVdata C).2.1),
   (fun C↦(hVdata C).2.2)⟩⟩
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
theorem AdaptiveUnitProjectionFamily.one_le_allDegree
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (P:AdaptiveUnitProjectionFamily base p q)
   (C:RegularComponent Omega G T H):
   1 ≤ coordinateDegree Omega (CoordinateField Omega C.1)
     (P.allProjection C):=
 one_le_coordinateDegree_of_transcendental_value
   (P.allProjection C) (P.allTranscendental C)
theorem AdaptiveUnitProjectionFamily.one_le_toPrimeFlagBudgetFamily_allCost
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (P:AdaptiveUnitProjectionFamily base p q)
   (C:RegularComponent Omega G T H):
   1 ≤ P.toPrimeFlagBudgetFamily.allCost C:=
 P.one_le_allDegree C
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
theorem exists_common_exact_finite_separable_shear_avoiding
   {J:Type*} [Finite J]
   (Extra:J → K → Prop)
   (hextra:∀ j {a b},Extra j a → Extra j b → a=b)
   (embeddingZ:∀ i,RatFunc K →ₐ[K] E i)
   (hvalueZ:∀ i,embeddingZ i
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=z i)
   (hfiniteZ:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (embeddingZ i).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) (E i))
   (hsepZ:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (embeddingZ i).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc K) (E i)):
   ∃ a:K,a≠0∧(∀ j,¬ Extra j a)∧∀ i,
     ∃ hs:Transcendental K (r i+a • z i),
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) hs).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc K) (E i))∧
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) hs).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc K) (E i))∧
       (∀ v∈W i,v.val (r i+a • z i)=
         max (v.val (r i)) (v.val (z i))):=by
 have hdz:∀ i,D K (E i) (z i)≠0:=by
   intro i
   have h:=parameterDifferential_ne_zero_of_isSeparable
     K (E i) (embeddingZ i) (hfiniteZ i) (hsepZ i)
   unfold RCN369.parameterDifferential at h
   rwa [hvalueZ i] at h
 let Q:=J ⊕ (I ⊕ Σ i:I,{v//v∈W i})
 let Bad:Q → K → Prop
   | Sum.inl j,a => Extra j a
   | Sum.inr (Sum.inl i),a =>
       D K (E i) (r i)+a • D K (E i) (z i)=0
   | Sum.inr (Sum.inr iv),a =>
       iv.2.1.val (r iv.1+a • z iv.1) <
         max (iv.2.1.val (r iv.1)) (iv.2.1.val (z iv.1))
 have hsingle:∀ q {a b},Bad q a → Bad q b → a=b:=by
   intro q a b ha hb
   rcases q with j | i | ⟨i,v⟩
   · exact hextra j ha hb
   · exact shear_bad_coefficient_subsingleton K (E i) (r i) (z i)
       (hdz i) ha hb
   · exact valuation_shear_bad_coefficient_subsingleton v.1 (r i) (z i) ha hb
 obtain ⟨a,ha0,havoid⟩:=
   exists_nonzero_avoiding_finite_subsingleton Bad hsingle
 refine ⟨a,ha0,?_,fun i↦?_⟩
 · intro j
   exact havoid (Sum.inl j)
 · have hdiff:D K (E i) (r i)+a • D K (E i) (z i)≠0:=by
     exact havoid (Sum.inr (Sum.inl i))
   obtain ⟨hs,hfinite,hsep⟩:=
     shear_transcendental_finite_separable_of_differential_ne_zero
       K (E i) (embeddingZ i) (r i) (z i) a
         (hvalueZ i) (hfiniteZ i) (hsepZ i) hdiff
   refine ⟨hs,hfinite,hsep,?_⟩
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
section RegularComponents
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
theorem exists_nestedFlagProjectionData_directional
   (hseparator:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (coordinate Omega C.1 2))
   (hproj:∀ C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0):
   ∃ D:NestedFlagProjectionData hseparator hproj,
     MvPolynomial.pderiv (0:Fin 3) G-
       MvPolynomial.C D.mu*MvPolynomial.pderiv (1:Fin 3) G≠0:=by
 classical
 let E:RegularComponent Omega G T H → Type:=
   fun C↦CoordinateField Omega C.1
 let rY:∀ C,E C:=fun C↦coordinate Omega C.1 0
 let z:∀ C,E C:=fun C↦coordinate Omega C.1 2
 let W:∀ C,Finset
     (RCN345.NormalizedValuation Omega (E C)):=
   fun C↦componentRelevantPlaces hseparator hproj C
 let embeddingZ:∀ C,RatFunc Omega →ₐ[Omega] E C:=
   fun C↦rationalBaseEmbedding Omega C.1 2 (hseparator C)
 have hvalueZ:∀ C,embeddingZ C
     (algebraMap (Polynomial Omega) (RatFunc Omega) Polynomial.X)=z C:=by
   intro C
   exact rationalBaseEmbedding_polynomial Omega C.1 2 (hseparator C) Polynomial.X
     |>.trans (Polynomial.aeval_X _)
 have hfiniteZ:∀ C,
     letI:Algebra (RatFunc Omega) (E C):=
       (embeddingZ C).toRingHom.toAlgebra
     FiniteDimensional (RatFunc Omega) (E C):=by
   intro C
   exact (hproj C 2 (hseparator C)).1
 have hsepZ:∀ C,
     letI:Algebra (RatFunc Omega) (E C):=
       (embeddingZ C).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc Omega) (E C):=by
   intro C
   exact (hproj C 2 (hseparator C)).2
 obtain ⟨lam,hlam0,hlam⟩:=
   exists_common_exact_finite_separable_shear E rY z W
     embeddingZ hvalueZ hfiniteZ hsepZ
 let hU:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (affineU Omega C.1 lam):=
   fun C↦Classical.choose (hlam C)
 have hUdata:∀ C,
     (letI:Algebra (RatFunc Omega) (E C):=
         (elementEmbedding Omega (E C) (affineU Omega C.1 lam)
           (hU C)).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc Omega) (E C))∧
     (letI:Algebra (RatFunc Omega) (E C):=
         (elementEmbedding Omega (E C) (affineU Omega C.1 lam)
           (hU C)).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc Omega) (E C))∧
     ∀ v∈W C,v.val (affineU Omega C.1 lam)=
       max (v.val (coordinate Omega C.1 0))
         (v.val (coordinate Omega C.1 2)):=by
   intro C
   have hp:hU C=Classical.choose (hlam C):=Subsingleton.elim _ _
   cases hp
   simpa only [E,rY,z,affineU,hU] using! Classical.choose_spec (hlam C)
 let rS:∀ C,E C:=fun C↦coordinate Omega C.1 1
 let u:∀ C,E C:=fun C↦affineU Omega C.1 lam
 let embeddingU:∀ C,RatFunc Omega →ₐ[Omega] E C:=fun C↦
   elementEmbedding Omega (E C) (u C) (hU C)
 have hvalueU:∀ C,embeddingU C
     (algebraMap (Polynomial Omega) (RatFunc Omega) Polynomial.X)=u C:=by
   intro C
   exact elementEmbedding_variable Omega (E C) (u C) (hU C)
 have hfiniteU:∀ C,
     letI:Algebra (RatFunc Omega) (E C):=
       (embeddingU C).toRingHom.toAlgebra
     FiniteDimensional (RatFunc Omega) (E C):=fun C↦(hUdata C).1
 have hsepU:∀ C,
     letI:Algebra (RatFunc Omega) (E C):=
       (embeddingU C).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc Omega) (E C):=fun C↦(hUdata C).2.1
 let Extra:PUnit → Omega → Prop:=fun _ mu↦
   MvPolynomial.pderiv (0:Fin 3) G-
     MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) G=0
 have hextra:∀ j {a b},Extra j a → Extra j b → a=b:=by
   intro j a b ha hb
   exact directional_bad_coefficient_subsingleton G hSderiv ha hb
 obtain ⟨mu,hmu0,hmudir,hmu⟩:=
   exists_common_exact_finite_separable_shear_avoiding E rS u W
     Extra hextra embeddingU hvalueU hfiniteU hsepU
 let hV:∀ C:RegularComponent Omega G T H,Transcendental Omega
     (coordinate Omega C.1 1+mu • affineU Omega C.1 lam):=
   fun C↦Classical.choose (hmu C)
 have hVdata:∀ C,
     (letI:Algebra (RatFunc Omega) (E C):=
         (elementEmbedding Omega (E C)
           (coordinate Omega C.1 1+mu • affineU Omega C.1 lam)
           (hV C)).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc Omega) (E C))∧
     (letI:Algebra (RatFunc Omega) (E C):=
         (elementEmbedding Omega (E C)
           (coordinate Omega C.1 1+mu • affineU Omega C.1 lam)
           (hV C)).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc Omega) (E C))∧
     ∀ v∈W C,
       v.val (coordinate Omega C.1 1+mu • affineU Omega C.1 lam)=
         max (v.val (coordinate Omega C.1 1))
           (v.val (affineU Omega C.1 lam)):=by
   intro C
   have hp:hV C=Classical.choose (hmu C):=Subsingleton.elim _ _
   cases hp
   simpa only [E,rS,u,hV] using! Classical.choose_spec (hmu C)
 let D:NestedFlagProjectionData hseparator hproj:=
   ⟨lam,hlam0,hU,
     (fun C↦(hUdata C).1),(fun C↦(hUdata C).2.1),
     (fun C↦(hUdata C).2.2),
     mu,hmu0,hV,
     (fun C↦(hVdata C).1),(fun C↦(hVdata C).2.1),
     (fun C↦(hVdata C).2.2)⟩
 refine ⟨D,?_⟩
 exact hmudir PUnit.unit
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
theorem finiteAffineV
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Omega G T H):
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 D.mu (D.mu*D.lam))
       (hAffineV D C)).toRingHom.toAlgebra
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1):=by
 rw [elementEmbedding_affineV_eq_nested D C]
 exact D.finiteV C
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
set_option Elab.async false in
theorem PackedLegacyBarrier16 : True := by trivial
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
theorem exactAgreementFlag6543_eq:
   exactAgreementFlag6543=shearedAgreementFlag:=by
 rw [shearedAgreementFlag_value]
 rfl
theorem exists_genericExactPolePolynomial_flagSupport
   (hseparator:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (coordinate Omega C.1 2))
   (hproj:∀ C:RegularComponent Omega G T H,
     ProjectionsFiniteSeparable Omega C.1)
   (p:FlagDegree):
   Nonempty (GenericExactPolePolynomial G T H (flagSupport p) 2
     hseparator hproj):=
 exists_genericExactPolePolynomial hseparator hproj (flagSupport p)
   (flagSupport_downwardClosed p) (zero_mem_flagSupport p)
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
theorem exists_residualComponentBudget6543_of_projectionPositivity
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport shearedSurfaceFlag)
   (hTsupport:T.support ⊆ flagSupport shearedAgreementFlag)
   (hpositive:∃ D:NestedFlagProjectionData hseparator hproj,
     FlagProjectionPositivity D G):
   Nonempty (ResidualComponentBudget G T H
     (fun A↦A.support ⊆ flagSupport shearedAgreementFlag)
     flagWholeMixedCap):=by
 obtain ⟨D,hD⟩:=hpositive
 obtain ⟨B⟩:=exists_genericExactPolePolynomial_flagSupport
   hseparator hproj exactAgreementFlag6543
 rw [exactAgreementFlag6543_eq] at B
 obtain ⟨BZ⟩:=exists_genericExactPolePolynomial_flagSupport
   hseparator hproj unitZFlag
 obtain ⟨BYZ⟩:=exists_genericExactPolePolynomial_flagSupport
   hseparator hproj unitYZFlag
 obtain ⟨BAll⟩:=exists_genericExactPolePolynomial_flagSupport
   hseparator hproj unitAllFlag
 exact ⟨residualComponentBudget6543_of_nested D hG hproper hGsupport
   hTsupport hD B BZ BYZ BAll⟩
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
section PackedLegacy_C0
namespace ProximityPrize.SubmissionLower.RCN098
open scoped Classical BigOperators WithZero
open IsDedekindDomain RCN002 RCN005
 RCN006 RCN007
open RCN344 RCN264 RCN187 RCN075 RCN095 RCN114 RCN125 RCN093 RCN097 RCN099 RCN115 RCN118 RCN123 RCN116 RCN121 RCN272 RCN371 RCN011
 RCN022
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 20000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
variable {hseparator:∀ C:RegularComponent Omega G T H,
 Transcendental Omega (coordinate Omega C.1 2)}
variable {hproj:∀ C:RegularComponent Omega G T H,
 ProjectionsFiniteSeparable Omega C.1}
def flagProjectionCycleBudget_of_nested_general
   (p q r:FlagDegree)
   (D:NestedFlagProjectionData hseparator hproj)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q)
   (hpositive:FlagProjectionPositivity D G)
   (B:GenericExactPolePolynomial G T H (flagSupport r) 2
     hseparator hproj)
   (BZ:GenericExactPolePolynomial G T H (flagSupport unitZFlag) 2
     hseparator hproj)
   (BYZ:GenericExactPolePolynomial G T H (flagSupport unitYZFlag) 2
     hseparator hproj)
   (BAll:GenericExactPolePolynomial G T H (flagSupport unitAllFlag) 2
     hseparator hproj):
   FlagProjectionCycleBudget r 2 hseparator hproj B
     (flagMixed p q unitZFlag)
     (flagMixed p q unitYZFlag)
     (flagMixed p q unitAllFlag):=by
 let lam:=D.lam
 let mu:=D.mu
 let nu:=D.mu*D.lam
 let gCaps:=flagTrapezoidCaps_flagAlgHom p G lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom q T lam mu nu hTsupport
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
     hseparator hproj BZ (flagMixed p q unitZFlag):=
   principalCycleBudget_of_flag_trapezoid BZ lam mu nu zOrder htZ
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
     (by
       intro C v
       simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu,
         RCN346.poleOrder] using
         unitZ_polynomial_pole BZ C v)
     hG hproper hpositive.z p.all q.all (p.yz+p.all)
     (q.yz+q.all) (flagMixed p q unitZFlag) hTne
     (by simpa only [gCaps] using gCaps.zOuter)
     (by simpa only [tCaps] using tCaps.zOuter)
     (by simpa only [gCaps] using gCaps.zTotal)
     (by simpa only [tCaps] using tCaps.zTotal)
     (z_flag_trapezoid_budget p q)
 let yzBudget:PrincipalCycleBudget (flagSupport unitYZFlag) 2
     hseparator hproj BYZ (flagMixed p q unitYZFlag):=
   principalCycleBudget_of_flag_trapezoid BYZ lam mu nu uOrder htU
     (by
       intro C
       rw [hembU C]
       simpa [uOrder,lam,mu,nu] using
         flag_generators_u Omega C.1 lam mu nu (D.hU C))
     (by
       intro C
       rw [hembU C]
       exact D.separableU C)
     (by
       intro C v
       simpa [uOrder,lam,mu,nu,RCN346.poleOrder] using
         unitYZ_polynomial_pole D BYZ C v)
     hG hproper hpositive.u p.all q.all
     (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all)
     (flagMixed p q unitYZFlag) hTne
     (by simpa only [gCaps] using gCaps.uOuter)
     (by simpa only [tCaps] using tCaps.uOuter)
     (by simpa only [gCaps] using gCaps.uTotal)
     (by simpa only [tCaps] using tCaps.uTotal)
     (u_flag_trapezoid_budget p q)
 let allBudget:PrincipalCycleBudget (flagSupport unitAllFlag) 2
     hseparator hproj BAll (flagMixed p q unitAllFlag):=
   principalCycleBudget_of_flag_trapezoid BAll lam mu nu vOrder htV
     (by
       intro C
       rw [hembV C]
       simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using
         flag_generators_v Omega C.1 lam mu nu (hAffineV D C))
     (by
       intro C
       rw [hembV C]
       exact separableAffineV D C)
     (by
       intro C v
       simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu,
         RCN346.poleOrder] using
         unitAll_polynomial_pole D BAll C v)
     hG hproper hpositive.v (p.yz+p.all) (q.yz+q.all)
     (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all)
     (flagMixed p q unitAllFlag) hTne
     (by simpa only [gCaps] using gCaps.vOuter)
     (by simpa only [tCaps] using tCaps.vOuter)
     (by simpa only [gCaps] using gCaps.vTotal)
     (by simpa only [tCaps] using tCaps.vTotal)
     (v_flag_trapezoid_budget p q)
 exact FlagProjectionCycleBudget.ofNestedProjectionBudgets
   B BZ BYZ BAll zBudget yzBudget allBudget
def residualComponentBudget_flagMixed_of_nested
   (p q r:FlagDegree)
   (D:NestedFlagProjectionData hseparator hproj)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q)
   (hpositive:FlagProjectionPositivity D G)
   (B:GenericExactPolePolynomial G T H (flagSupport r) 2
     hseparator hproj)
   (BZ:GenericExactPolePolynomial G T H (flagSupport unitZFlag) 2
     hseparator hproj)
   (BYZ:GenericExactPolePolynomial G T H (flagSupport unitYZFlag) 2
     hseparator hproj)
   (BAll:GenericExactPolePolynomial G T H (flagSupport unitAllFlag) 2
     hseparator hproj):
   ResidualComponentBudget G T H
     (fun A↦A.support ⊆ flagSupport r) (flagMixed p q r):=by
 rw [flagMixed_projection_decomposition]
 exact (flagProjectionCycleBudget_of_nested_general p q r D hG hproper
   hGsupport hTsupport hpositive B BZ BYZ BAll).toResidualComponentBudget
theorem exists_residualComponentBudget_flagMixed_of_projectionPositivity
   (p q r:FlagDegree)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q)
   (hpositive:∃ D:NestedFlagProjectionData hseparator hproj,
     FlagProjectionPositivity D G):
   Nonempty (ResidualComponentBudget G T H
     (fun A↦A.support ⊆ flagSupport r) (flagMixed p q r)):=by
 obtain ⟨D,hD⟩:=hpositive
 obtain ⟨B⟩:=exists_genericExactPolePolynomial_flagSupport
   hseparator hproj r
 obtain ⟨BZ⟩:=exists_genericExactPolePolynomial_flagSupport
   hseparator hproj unitZFlag
 obtain ⟨BYZ⟩:=exists_genericExactPolePolynomial_flagSupport
   hseparator hproj unitYZFlag
 obtain ⟨BAll⟩:=exists_genericExactPolePolynomial_flagSupport
   hseparator hproj unitAllFlag
 exact ⟨residualComponentBudget_flagMixed_of_nested p q r D hG hproper
   hGsupport hTsupport hD B BZ BYZ BAll⟩
end
end ProximityPrize.SubmissionLower.RCN098
end PackedLegacy_C0

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
theorem flag_u_z_outer_positive
   (lam mu:K) (G:Poly3 K)
   (hSpos:0 < G.degreeOf 1) (hSchar:G.degreeOf 1 < p):
   0 < (planeMap K uOrder
         (flagAlgHom lam mu (mu*lam) G)).natDegree∧
     0 < (planeMap K zOrder
         (flagAlgHom lam mu (mu*lam) G)).natDegree:=by
 have hderiv:MvPolynomial.pderiv (1:Fin 3) G≠0:=by
   intro hzero
   have hz:=(pderiv_zero_iff_degree_zero_below_char
     (1:Fin 3) G p hSchar).mp hzero
   omega
 exact flag_u_z_outer_positive_of_pderiv lam mu G hderiv
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
theorem flagProjectionPositivity_of_degree_directional
   (D:NestedFlagProjectionData hseparator hproj)
   (hSpos:0 < G.degreeOf 1) (hSchar:G.degreeOf 1 < p)
   (hdirectional:MvPolynomial.pderiv (0:Fin 3) G-
     MvPolynomial.C D.mu*MvPolynomial.pderiv (1:Fin 3) G≠0):
   FlagProjectionPositivity D G:=by
 have huz:=flag_u_z_outer_positive p D.lam D.mu G hSpos hSchar
 exact ⟨huz.1,
   flag_v_outer_positive_of_directional D.lam D.mu G hdirectional,
   huz.2⟩
theorem flagProjectionPositivity_of_derivatives
   (D:NestedFlagProjectionData hseparator hproj)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (hdirectional:MvPolynomial.pderiv (0:Fin 3) G-
     MvPolynomial.C D.mu*MvPolynomial.pderiv (1:Fin 3) G≠0):
   FlagProjectionPositivity D G:=by
 have huz:=flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv
 exact ⟨huz.1,
   flag_v_outer_positive_of_directional D.lam D.mu G hdirectional,
   huz.2⟩
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
theorem factorRegularLedgerYZForDirection_projection_decomposition
   (p:Profile) (direction flag:FlagDegree):
   factorRegularLedgerYZForDirection p direction flag=
     flag.zOnly*factorRegularLedgerYZForDirection p direction unitZFlag+
     flag.yz*factorRegularLedgerYZForDirection p direction unitYZFlag+
     flag.all*factorRegularLedgerYZForDirection p direction unitAllFlag:=by
 cases flag
 simp [factorRegularLedgerYZForDirection,factorPrimaryForDirection,
   factorZTailForDirection,factorYZTailForDirection,flagMixed,
   unitZFlag,unitYZFlag,unitAllFlag]
 ring
theorem sum_factorRegularLedgerYZForDirection_le_flag
   {I:Type} [Fintype I] (p:Profile) (direction:FlagDegree)
   (flag:I → FlagDegree) (cap:FlagDegree)
   (hz:(∑ i,(flag i).zOnly) ≤ cap.zOnly)
   (hyz:(∑ i,(flag i).yz) ≤ cap.yz)
   (hall:(∑ i,(flag i).all) ≤ cap.all):
   (∑ i,factorRegularLedgerYZForDirection p direction (flag i)) ≤
     factorRegularLedgerYZForDirection p direction cap:=by
 classical
 calc
   (∑ i,factorRegularLedgerYZForDirection p direction (flag i))=
       ∑ i,((flag i).zOnly*factorRegularLedgerYZForDirection p direction unitZFlag+
         (flag i).yz*factorRegularLedgerYZForDirection p direction unitYZFlag+
         (flag i).all*factorRegularLedgerYZForDirection p direction unitAllFlag):=by
     apply Finset.sum_congr rfl
     intro i _
     exact factorRegularLedgerYZForDirection_projection_decomposition p direction (flag i)
   _=(∑ i,(flag i).zOnly)*factorRegularLedgerYZForDirection p direction unitZFlag+
       (∑ i,(flag i).yz)*factorRegularLedgerYZForDirection p direction unitYZFlag+
       (∑ i,(flag i).all)*factorRegularLedgerYZForDirection p direction unitAllFlag:=by
     simp only [Finset.sum_add_distrib,Finset.sum_mul]
   _ ≤ cap.zOnly*factorRegularLedgerYZForDirection p direction unitZFlag+
       cap.yz*factorRegularLedgerYZForDirection p direction unitYZFlag+
       cap.all*factorRegularLedgerYZForDirection p direction unitAllFlag:=
     Nat.add_le_add
       (Nat.add_le_add (Nat.mul_le_mul_right _ hz)
         (Nat.mul_le_mul_right _ hyz))
       (Nat.mul_le_mul_right _ hall)
   _=factorRegularLedgerYZForDirection p direction cap:=
     (factorRegularLedgerYZForDirection_projection_decomposition p direction cap).symm
theorem factorRegularLedgerYZ_projection_decomposition
   (p:Profile) (flag:FlagDegree):
   factorRegularLedgerYZ p flag=
     flag.zOnly*factorRegularLedgerYZ p unitZFlag+
     flag.yz*factorRegularLedgerYZ p unitYZFlag+
     flag.all*factorRegularLedgerYZ p unitAllFlag:=
 factorRegularLedgerYZForDirection_projection_decomposition
   p p.agreementDirection flag
theorem sum_factorRegularLedgerYZ_le_flag
   {I:Type} [Fintype I] (p:Profile)
   (flag:I → FlagDegree) (cap:FlagDegree)
   (hz:(∑ i,(flag i).zOnly) ≤ cap.zOnly)
   (hyz:(∑ i,(flag i).yz) ≤ cap.yz)
   (hall:(∑ i,(flag i).all) ≤ cap.all):
   (∑ i,factorRegularLedgerYZ p (flag i)) ≤
     factorRegularLedgerYZ p cap:=
 sum_factorRegularLedgerYZForDirection_le_flag p p.agreementDirection
   flag cap hz hyz hall
noncomputable section
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem sum_factor_counts_rectangularYZ_le
   (p:Profile) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (hw:0 < p.w)
   (hbox:Q∈globalCoefficientBox K p.weightedCap p.w
     p.seedTotalCap p.slopeCap)
   (count:RegularIndex Q → ℕ)
   (hcount:∀ F,count F*p.gap^2 ≤
     factorRegularLedgerYZ p (regularFlag Q F)):
   (∑ F,count F)*p.gap^2 ≤ regularNumeratorYZ p:=by
 have hcaps:=regularFlag_budgets p Q hQ hw hbox
 calc
   (∑ F,count F)*p.gap^2=∑ F,count F*p.gap^2:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ F,factorRegularLedgerYZ p (regularFlag Q F):=
     Finset.sum_le_sum (fun F _↦hcount F)
   _ ≤ factorRegularLedgerYZ p p.rectangularSurfaceFlag:=
     sum_factorRegularLedgerYZ_le_flag p (regularFlag Q)
       p.rectangularSurfaceFlag hcaps.1 hcaps.2.1 hcaps.2.2
   _=regularNumeratorYZ p:=rfl
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
theorem recursive_scaled_factorYZ
   (hphi:Function.Injective phi)
   (p:Profile) (support:ResidualSupportParameters)
   (direction:FlagDegree)
   (S:ResidualStage phi Gamma x pchar p.errors flag p.w support)
   (hwa:p.w < p.agreements)
   (hagreement:∀ gamma∈Gamma,
     p.agreements ≤ (S.agreementFiber gamma).card)
   (hfiber:∀ D:S.TerminalDescendant,∀ i∈D.stage.nodes,
     ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i) →
     (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*p.gap ≤
       D.degree*factorDegreeCostYZ p direction flag+
         factorUnitCostYZ p direction flag)
   (hdegree:∀ k ≤ p.w,
     (S.nodes.card-k)*p.gap*(p.w-k) ≤
       p.degreeIncidence*(p.agreements-k))
   (hunit:∀ k ≤ p.w,
     (S.nodes.card-k)*p.gap ≤
       p.unitIncidence*(p.agreements-k)):
   Gamma.card*p.gap^2 ≤
     factorRegularLedgerYZForDirection p direction flag:=by
 have h:=recursive_scaled_stratified_incidence_bound
   hphi S (factorDegreeCostYZ p direction flag)
     (factorUnitCostYZ p direction flag)
     p.degreeIncidence p.unitIncidence hwa hagreement
     (by simpa only [Profile.gap] using hfiber)
     (by simpa only [Profile.gap] using hdegree)
     (by simpa only [Profile.gap] using hunit)
 calc
   Gamma.card*p.gap^2 ≤
       p.degreeIncidence*factorDegreeCostYZ p direction flag+
         p.unitIncidence*factorUnitCostYZ p direction flag:=by
     simpa only [Profile.gap] using h
   _=factorRegularLedgerYZForDirection p direction flag:=
     incidence_cost_eq_factorRegularLedgerYZ p direction flag
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
theorem flagMixed_unit_mono (q r:FlagDegree):
   flagMixed unitZFlag q r ≤ flagMixed unitYZFlag q r∧
     flagMixed unitYZFlag q r ≤ flagMixed unitAllFlag q r:=by
 constructor
 · calc
     flagMixed unitZFlag q r ≤ flagMixed unitZFlag q r+
         (q.zOnly*r.all+r.zOnly*q.all):=Nat.le_add_right _ _
     _=flagMixed unitYZFlag q r:=by
       simp [flagMixed,unitZFlag,unitYZFlag]
       ring
 · calc
     flagMixed unitYZFlag q r ≤ flagMixed unitYZFlag q r+
         (q.yz*r.yz+q.zOnly*r.yz+r.zOnly*q.yz):=Nat.le_add_right _ _
     _=flagMixed unitAllFlag q r:=by
       simp [flagMixed,unitYZFlag,unitAllFlag]
       ring
theorem ledger_unit_mono (p:Profile) (direction:FlagDegree):
   factorRegularLedgerYZForDirection p direction unitZFlag ≤
       factorRegularLedgerYZForDirection p direction unitYZFlag∧
     factorRegularLedgerYZForDirection p direction unitYZFlag ≤
       factorRegularLedgerYZForDirection p direction unitAllFlag:=by
 have hm (a b:FlagDegree)
     (h:∀ q r,flagMixed a q r ≤ flagMixed b q r):
     factorRegularLedgerYZForDirection p direction a ≤
       factorRegularLedgerYZForDirection p direction b:=by
   unfold factorRegularLedgerYZForDirection factorPrimaryForDirection
     factorZTailForDirection factorYZTailForDirection
   gcongr <;> exact h _ _
 exact ⟨hm _ _ (fun q r↦(flagMixed_unit_mono q r).1),
   hm _ _ (fun q r↦(flagMixed_unit_mono q r).2)⟩
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
theorem sum_linear_cost_cumulative_le
   {I:Type} [Fintype I] (cost:FlagDegree → ℕ)
   (hlinear:∀ f,cost f=f.zOnly*cost unitZFlag+
     f.yz*cost unitYZFlag+f.all*cost unitAllFlag)
   (hzy:cost unitZFlag ≤ cost unitYZFlag)
   (hya:cost unitYZFlag ≤ cost unitAllFlag)
   (flag:I → FlagDegree) (cap:FlagDegree)
   (hi:(∑ i,(flag i).all) ≤ cap.all)
   (hm:(∑ i,((flag i).yz+(flag i).all)) ≤ cap.yz+cap.all)
   (ht:(∑ i,((flag i).zOnly+(flag i).yz+(flag i).all)) ≤
     cap.zOnly+cap.yz+cap.all):
   (∑ i,cost (flag i)) ≤ cost cap:=by
 have heq (f:FlagDegree):cost f=
     cost unitZFlag*(f.zOnly+f.yz+f.all)+
       (cost unitYZFlag-cost unitZFlag)*(f.yz+f.all)+
       (cost unitAllFlag-cost unitYZFlag)*f.all:=by
   rw [hlinear f]
   exact linear_cost_cumulative _ _ _ f hzy hya
 rw [Finset.sum_congr rfl (fun i _↦heq (flag i)),heq cap]
 simp only [Finset.sum_add_distrib, ←Finset.mul_sum]
 simpa only [Finset.sum_add_distrib] using Nat.add_le_add
   (Nat.add_le_add (Nat.mul_le_mul_left _ ht) (Nat.mul_le_mul_left _ hm))
   (Nat.mul_le_mul_left _ hi)
theorem sum_ledger_cumulative_le
   {I:Type} [Fintype I] (p:Profile) (direction:FlagDegree)
   (flag:I → FlagDegree) (cap:FlagDegree)
   (hi:(∑ i,(flag i).all) ≤ cap.all)
   (hm:(∑ i,((flag i).yz+(flag i).all)) ≤ cap.yz+cap.all)
   (ht:(∑ i,((flag i).zOnly+(flag i).yz+(flag i).all)) ≤
     cap.zOnly+cap.yz+cap.all):
   (∑ i,factorRegularLedgerYZForDirection p direction (flag i)) ≤
     factorRegularLedgerYZForDirection p direction cap:=
 sum_linear_cost_cumulative_le (factorRegularLedgerYZForDirection p direction)
   (factorRegularLedgerYZForDirection_projection_decomposition p direction)
   (ledger_unit_mono p direction).1 (ledger_unit_mono p direction).2
   flag cap hi hm ht
variable {K:Type} [Field K]
theorem sum_regular_counts_cumulative_le
   (p:Profile) (direction:FlagDegree)
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   {P:ResidualSupportParameters} (H:ResidualSupportData P Q)
   (count:RegularIndex Q → ℕ)
   (hcount:∀ R,count R*p.gap^2 ≤
     factorRegularLedgerYZForDirection p direction (regularCumulativeFlag Q R)):
   (∑ R,count R)*p.gap^2 ≤
     factorRegularLedgerYZForDirection p direction (supportCumulativeFlag P):=by
 have hc:=regularCumulativeFlag_budgets Q hQ H
 have hp:=flagFromCaps_cumulative P.total P.ys P.s P.s_le_ys P.ys_le_total
 calc
   (∑ R,count R)*p.gap^2=∑ R,count R*p.gap^2:=by rw [Finset.sum_mul]
   _ ≤ ∑ R,factorRegularLedgerYZForDirection p direction
       (regularCumulativeFlag Q R):=Finset.sum_le_sum (fun R _↦hcount R)
   _ ≤ factorRegularLedgerYZForDirection p direction (supportCumulativeFlag P):=
     sum_ledger_cumulative_le p direction (regularCumulativeFlag Q)
       (supportCumulativeFlag P)
       (by simpa only [supportCumulativeFlag,hp.1] using hc.1)
       (by simpa only [supportCumulativeFlag,hp.2.1] using hc.2.1)
       (by simpa only [supportCumulativeFlag,hp.2.2] using hc.2.2)
theorem geometric_seed_counts_cumulative_le
   (p:Profile) (direction:FlagDegree)
   (F:MvPolynomial (Fin 4) K) (hF:F≠0)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hsolutions:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hcount:∀ g:GeometricFactor K F,
     (geometricSeeds K F selected Gamma g).card*p.gap^2 ≤
       factorRegularLedgerYZForDirection p direction (geometricCumulativeFlag K g)):
   Gamma.card*p.gap^2 ≤
     factorRegularLedgerYZForDirection p direction (originalCumulativeFlag F):=by
 have hc:=geometricCumulativeFlag_budgets F hF
 calc
   Gamma.card*p.gap^2 ≤
       (∑ g:GeometricFactor K F,(geometricSeeds K F selected Gamma g).card)*
         p.gap^2:=Nat.mul_le_mul_right _
           (card_le_sum_geometricSeeds K F hF selected Gamma hsolutions)
   _=∑ g:GeometricFactor K F,
       (geometricSeeds K F selected Gamma g).card*p.gap^2:=by rw [Finset.sum_mul]
   _ ≤ ∑ g:GeometricFactor K F,
       factorRegularLedgerYZForDirection p direction (geometricCumulativeFlag K g):=
     Finset.sum_le_sum (fun g _↦hcount g)
   _ ≤ factorRegularLedgerYZForDirection p direction (originalCumulativeFlag F):=
     sum_ledger_cumulative_le p direction (geometricCumulativeFlag K)
       (originalCumulativeFlag F) hc.1 hc.2.1 hc.2.2
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
theorem weightedMixed_eq (p q r:FlagDegree):weightedMixed p q r=flagMixed p q r:=by
 simp only [weightedMixed,flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
 ring
theorem qeff_add_base (a b s:ℕ) (p:FlagDegree):
   qeff a b s p+flagMixed p (denominatorFlag a b s) (numeratorFlag a b s)=
     quad a b s p+2*flagMixed p unitAllFlag unitYZFlag:=by
 simp only [qeff,quad,directionFlag,normalFlag,fiberFlag,surfaceFlag,
   denominatorFlag,numeratorFlag,flagMixed,unitAllFlag,unitYZFlag]
 ring
theorem lin_eq (a b s:ℕ) (p:FlagDegree):lin a b s p=quad a b s p+ell a b s p:=by
 simp only [lin,quad,ell,centreFlag,flagMixed,add_zOnly,add_yz,add_all,unitYZFlag]
 ring
theorem unit_eq (a b s:ℕ) (p:FlagDegree):
   unit a b s p=quad a b s p+2*ell a b s p+unitBase p:=by
 simp only [unit,quad,ell,unitBase,centreFlag,flagMixed,add_zOnly,add_yz,add_all,unitYZFlag]
 ring
theorem envelope_identity (a b s d:ℕ) (p:FlagDegree):
   weightedMixed p (centreFlag a b s+d • directionFlag a b s) (normalFlag a b s)+
     flagMixed p (fiberFlag a b s) (centreFlag a b s+d • surfaceFlag a b s)=
       d*qeff a b s p+lin a b s p:=by
 simp only [weightedMixed,qeff,lin,centreFlag,directionFlag,normalFlag,fiberFlag,surfaceFlag,
   flagMixed,add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all,unitZFlag,unitYZFlag,unitAllFlag]
 ring
theorem centre_identity (a b s d:ℕ) (p:FlagDegree):
   weightedMixed p (centreFlag a b s+d • directionFlag a b s) (centreFlag a b s)=
     d*lin a b s p+unit a b s p:=by
 simp only [weightedMixed,lin,unit,flagMixed,add_zOnly,add_yz,add_all,
   nsmul_zOnly,nsmul_yz,nsmul_all,unitZFlag,unitYZFlag,unitAllFlag]
 ring
theorem z_affine (a b s d:ℕ) (p:FlagDegree):
   flagMixed p (centreFlag a b s+d • directionFlag a b s) unitZFlag=
     d*zSlope a b s p+zBase a b s p:=by
 simp only [zSlope,zBase,flagMixed,add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
 ring
theorem yz_affine (a b s d:ℕ) (p:FlagDegree):
   flagMixed p (centreFlag a b s+d • directionFlag a b s) unitYZFlag=
     d*yzSlope a b s p+yzBase a b s p:=by
 simp only [yzSlope,yzBase,flagMixed,add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
 ring
section Cumulative
variable {I:Type*} [Fintype I] (flags:I → FlagDegree) (p:FlagDegree)
 (hs:(∑ i,(flags i).all) ≤ p.all)
 (hm:(∑ i,((flags i).yz+(flags i).all)) ≤ p.yz+p.all)
 (ht:(∑ i,((flags i).zOnly+(flags i).yz+(flags i).all)) ≤ p.zOnly+p.yz+p.all)
include hs hm ht
theorem sum_qeff_le (a b s:ℕ):(∑ i,qeff a b s (flags i)) ≤ qeff a b s p:=by
 simp only [qeff,Finset.sum_add_distrib]
 exact add_le_add
   (sum_flagMixed_le_of_cumulative flags p (directionFlag a b s) (normalFlag a b s) hs hm ht)
   (sum_flagMixed_le_of_cumulative flags p (fiberFlag a b s) (surfaceFlag a b s) hs hm ht)
theorem sum_lin_le (a b s:ℕ):(∑ i,lin a b s (flags i)) ≤ lin a b s p:=
 sum_flagMixed_le_of_cumulative flags p (centreFlag a b s) (directionFlag a b s) hs hm ht
theorem sum_unit_le (a b s:ℕ):(∑ i,unit a b s (flags i)) ≤ unit a b s p:=
 sum_flagMixed_le_of_cumulative flags p (centreFlag a b s) (centreFlag a b s) hs hm ht
theorem sum_zSlope_le (a b s:ℕ):(∑ i,zSlope a b s (flags i)) ≤ zSlope a b s p:=
 sum_flagMixed_le_of_cumulative flags p (directionFlag a b s) unitZFlag hs hm ht
theorem sum_zBase_le (a b s:ℕ):(∑ i,zBase a b s (flags i)) ≤ zBase a b s p:=
 sum_flagMixed_le_of_cumulative flags p (centreFlag a b s) unitZFlag hs hm ht
theorem sum_yzSlope_le (a b s:ℕ):(∑ i,yzSlope a b s (flags i)) ≤ yzSlope a b s p:=
 sum_flagMixed_le_of_cumulative flags p (directionFlag a b s) unitYZFlag hs hm ht
theorem sum_yzBase_le (a b s:ℕ):(∑ i,yzBase a b s (flags i)) ≤ yzBase a b s p:=
 sum_flagMixed_le_of_cumulative flags p (centreFlag a b s) unitYZFlag hs hm ht
theorem sum_envelope_le (a b s d:ℕ):
   (∑ i,(weightedMixed (flags i) (centreFlag a b s+d • directionFlag a b s) (normalFlag a b s)+
     flagMixed (flags i) (fiberFlag a b s) (centreFlag a b s+d • surfaceFlag a b s))) ≤
       d*qeff a b s p+lin a b s p:=by
 simp_rw [envelope_identity]
 rw [Finset.sum_add_distrib,←Finset.mul_sum]
 exact add_le_add (Nat.mul_le_mul_left d (sum_qeff_le flags p hs hm ht a b s))
   (sum_lin_le flags p hs hm ht a b s)
theorem sum_centre_le (a b s d:ℕ):
   (∑ i,weightedMixed (flags i) (centreFlag a b s+d • directionFlag a b s) (centreFlag a b s)) ≤
     d*lin a b s p+unit a b s p:=by
 simp_rw [centre_identity]
 rw [Finset.sum_add_distrib,←Finset.mul_sum]
 exact add_le_add (Nat.mul_le_mul_left d (sum_lin_le flags p hs hm ht a b s))
   (sum_unit_le flags p hs hm ht a b s)
theorem sum_z_tail_le (a b s d:ℕ):
   (∑ i,flagMixed (flags i) (centreFlag a b s+d • directionFlag a b s) unitZFlag) ≤
     d*zSlope a b s p+zBase a b s p:=by
 rw [←z_affine]
 exact sum_flagMixed_le_of_cumulative flags p _ _ hs hm ht
theorem sum_yz_tail_le (a b s d:ℕ):
   (∑ i,flagMixed (flags i) (centreFlag a b s+d • directionFlag a b s) unitYZFlag) ≤
     d*yzSlope a b s p+yzBase a b s p:=by
 rw [←yz_affine]
 exact sum_flagMixed_le_of_cumulative flags p _ _ hs hm ht
end Cumulative
theorem qeff_row:qeff 955 40 8 (surfaceFlag 955 40 8)=7643526:=by
 norm_num [qeff,surfaceFlag,directionFlag,normalFlag,fiberFlag,flagMixed]
theorem correction_row:2*flagMixed (surfaceFlag 955 40 8) unitAllFlag unitYZFlag=2012:=by
 norm_num [surfaceFlag,flagMixed,unitAllFlag,unitYZFlag]
end
end ProximityPrize.SubmissionLower.RCN206
end PackedLegacy_D1

/-! Packed from ProximityPrize.SubmissionLower.CommonShearDegreePrototype. -/
section PackedLegacy_CommonShearDegreePrototype

namespace ProximityPrize.SubmissionLower.RCN988

open scoped Classical BigOperators
open RCN001 RCN002 RCN005 RCN008 RCN009 RCN011 RCN013 RCN021 RCN022 RCN093 RCN125 RCN351
  RCN371 RCN372

noncomputable section

variable {K : Type} [Field K]

private def familyFiniteSummary {I : Type} [Fintype I]
    (Q : I → Ideal (MvPolynomial (Fin 3) K)) [∀ i, (Q i).IsPrime]
    (A : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)))
    (bound : ℕ) : Prop :=
  letI := A
  (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
    (∑ i, Module.finrank (RatFunc K) (CoordinateField K (Q i))) ≤ bound

private theorem elementEmbedding_congr_local
    {L : Type} [Field L] [Algebra K L] {s t : L}
    (hs : Transcendental K s) (ht : Transcendental K t) (h : s = t) :
    elementEmbedding K L s hs = elementEmbedding K L t ht := by
  subst t
  rfl

theorem flagAlgHom_zero_zero_eq_shearAlgHom (a : K) :
    RCN125.flagAlgHom (0 : K) 0 a = RCN372.shearAlgHom a := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [RCN125.flagImage, RCN125.flagAlgHom,
      RCN372.shearImage, RCN372.shearAlgHom]

theorem flag_shear_degreeOf_zero_le (a : K)
    (F : MvPolynomial (Fin 3) K) :
    (RCN125.flagAlgHom (0 : K) 0 a F).degreeOf 0 ≤ F.degreeOf 0 := by
  rw [flagAlgHom_zero_zero_eq_shearAlgHom]
  exact RCN372.shear_degreeOf_zero_le a F

theorem flag_shear_degreeOf_two_le (a : K)
    (F : MvPolynomial (Fin 3) K) :
    (RCN125.flagAlgHom (0 : K) 0 a F).degreeOf 2 ≤
      F.degreeOf 2 + F.degreeOf 1 := by
  rw [flagAlgHom_zero_zero_eq_shearAlgHom]
  exact RCN372.shear_degreeOf_two_le a F

theorem coordinateMixedDegree_flag_shear_one_le (a : K)
    (G T : MvPolynomial (Fin 3) K) :
    RCN001.coordinateMixedDegree K
        (RCN125.flagAlgHom (0 : K) 0 a G)
        (RCN125.flagAlgHom (0 : K) 0 a T) 1 ≤
      RCN001.coordinateMixedDegree K G T 1 +
        RCN001.coordinateMixedDegree K G T 2 := by
  rw [RCN001.coordinateMixedDegree_one,
    RCN001.coordinateMixedDegree_one,
    RCN001.coordinateMixedDegree_two]
  have hG0 := flag_shear_degreeOf_zero_le a G
  have hG2 := flag_shear_degreeOf_two_le a G
  have hT0 := flag_shear_degreeOf_zero_le a T
  have hT2 := flag_shear_degreeOf_two_le a T
  calc
    _ ≤ T.degreeOf 0 * (G.degreeOf 2 + G.degreeOf 1) +
        G.degreeOf 0 * (T.degreeOf 2 + T.degreeOf 1) :=
      Nat.add_le_add (Nat.mul_le_mul hT0 hG2)
        (Nat.mul_le_mul hG0 hT2)
    _ = T.degreeOf 0 * G.degreeOf 2 + G.degreeOf 0 * T.degreeOf 2 +
        (T.degreeOf 0 * G.degreeOf 1 + G.degreeOf 0 * T.degreeOf 1) := by
      simp only [Nat.mul_add]
      omega

section Family

variable {I : Type} [Fintype I]
  (Q : I → Ideal (MvPolynomial (Fin 3) K)) [∀ i, (Q i).IsPrime]

theorem exists_common_component_shear
    [IsAlgClosed K]
    (hZ : ∀ i, Transcendental K (coordinate K (Q i) 2))
    (hfiniteZ : ∀ i,
      letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
        rationalBaseAlgebra K (Q i) 2 (hZ i)
      FiniteDimensional (RatFunc K) (CoordinateField K (Q i)))
    (hsepZ : ∀ i,
      letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
        rationalBaseAlgebra K (Q i) 2 (hZ i)
      Algebra.IsSeparable (RatFunc K) (CoordinateField K (Q i))) :
    ∃ a : K, a ≠ 0 ∧ ∀ i,
      ∃ hS : Transcendental K
          (coordinate K (Q i) 1 + a • coordinate K (Q i) 2),
        (letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
            (elementEmbedding K (CoordinateField K (Q i))
              (coordinate K (Q i) 1 + a • coordinate K (Q i) 2)
              hS).toRingHom.toAlgebra;
          FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
        (letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
            (elementEmbedding K (CoordinateField K (Q i))
              (coordinate K (Q i) 1 + a • coordinate K (Q i) 2)
              hS).toRingHom.toAlgebra;
          Algebra.IsSeparable (RatFunc K) (CoordinateField K (Q i))) := by
  let embeddingZ : ∀ i, RatFunc K →ₐ[K] CoordinateField K (Q i) :=
    fun i => rationalBaseEmbedding K (Q i) 2 (hZ i)
  have hvalueZ : ∀ i, embeddingZ i
      (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) =
        coordinate K (Q i) 2 := by
    intro i
    dsimp only [embeddingZ]
    rw [rationalBaseEmbedding_polynomial, Polynomial.aeval_X]
  exact RCN351.exists_common_finite_separable_shear K
    (fun i => CoordinateField K (Q i))
    (fun i => coordinate K (Q i) 1)
    (fun i => coordinate K (Q i) 2)
    embeddingZ hvalueZ hfiniteZ hsepZ

/-- Once one common shear makes `R + a Z` transcendental on a finite family,
the separability-free family resultant bounds the *sum* of all resulting
extension degrees by the old `R` and `Z` mixed-degree budgets together.  This
is the aggregate substitute for the unavailable componentwise inequality
`[L : K(R+Z)] ≤ [L : K(R)] + [L : K(Z)]`. -/
theorem finite_sum_flag_shear_finrank_le_two_budgets_of_order
    (order : Fin 3 ≃ Fin 3)
    (horder : order = Equiv.swap 0 1 ∨
      order = RCN013.swapOtherOrder (Equiv.swap 0 1))
    (hinj : Function.Injective Q) (a : K)
    (hS : ∀ i, Transcendental K (RCN093.affineV K (Q i) 0 a))
    (G T : MvPolynomial (Fin 3) K) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ Q i) (hTmem : ∀ i, T ∈ Q i)
    (hproper : ¬ G ∣ T)
    (hpositive : 0 <
      (planeMap K order
        (RCN125.flagAlgHom (0 : K) 0 a G)).natDegree) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) :=
      fun i => (elementEmbedding K (CoordinateField K (Q i))
        (RCN093.affineV K (Q i) 0 a) (hS i)).toRingHom.toAlgebra
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (Q i))) ≤
        RCN001.coordinateMixedDegree K G T 1 +
          RCN001.coordinateMixedDegree K G T 2 := by
  let e : ∀ i, MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K (Q i) :=
    fun i => RCN093.flagEvaluation K (Q i) 0 0 a
  have hbase : order 0 = 1 := by
    rcases horder with hsame | hswap
    · subst order
      decide
    · subst order
      simp
  have ht : ∀ i, Transcendental K (e i (MvPolynomial.X (order 0))) := by
    intro i
    simpa [e, hbase] using hS i
  have hemb (i : I) :
      elementEmbedding K (CoordinateField K (Q i))
          (e i (MvPolynomial.X (order 0))) (ht i) =
        elementEmbedding K (CoordinateField K (Q i))
          (RCN093.affineV K (Q i) 0 a) (hS i) :=
    elementEmbedding_congr_local (ht i) (hS i)
      (by simp [e, hbase])
  have hgen : ∀ i,
      letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
        (elementEmbedding K (CoordinateField K (Q i))
          (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc K)
        ({e i (MvPolynomial.X (order 2)), e i (MvPolynomial.X (order 1))} :
          Set (CoordinateField K (Q i))) = ⊤ := by
    intro i
    rw [hemb i]
    rcases horder with hsame | hswap
    · subst order
      simpa [e, Equiv.swap_apply_def] using
        (RCN093.flag_generators_v K (Q i) 0 0 a (hS i))
    · subst order
      simpa [e, RCN013.swapOtherOrder, Equiv.swap_apply_def, Set.pair_comm]
        using (RCN093.flag_generators_v K (Q i) 0 0 a (hS i))
  have hGroot : ∀ i, e i (RCN125.flagAlgHom (0 : K) 0 a G) = 0 := by
    intro i
    rw [show e i (RCN125.flagAlgHom (0 : K) 0 a G) =
        coordinateEvaluation K (Q i) G from
      RCN093.flagEvaluation_flag K (Q i) 0 0 a G]
    change G ∈ RingHom.ker (coordinateEvaluation K (Q i)).toRingHom
    rw [coordinateEvaluation_ker]
    exact hGmem i
  have hTroot : ∀ i, e i (RCN125.flagAlgHom (0 : K) 0 a T) = 0 := by
    intro i
    rw [show e i (RCN125.flagAlgHom (0 : K) 0 a T) =
        coordinateEvaluation K (Q i) T from
      RCN093.flagEvaluation_flag K (Q i) 0 0 a T]
    change T ∈ RingHom.ker (coordinateEvaluation K (Q i)).toRingHom
    rw [coordinateEvaluation_ker]
    exact hTmem i
  have hresult := RCN021.finite_sum_finrank_bound K order
    (fun i => CoordinateField K (Q i)) e ht hgen
    (RCN093.flagEvaluation_kernel_family_injective K Q hinj 0 0 a)
    (RCN125.flagAlgHom (0 : K) 0 a G)
    (RCN125.flagAlgHom (0 : K) 0 a T)
    ((RCN125.flag_irreducible_iff 0 0 a G).mpr hG)
    hGroot hTroot (by simpa only [RCN125.flag_dvd_iff] using hproper)
    hpositive
  have htransformed : RCN013.originalMixedDegree K order
      (RCN125.flagAlgHom (0 : K) 0 a G)
      (RCN125.flagAlgHom (0 : K) 0 a T) ≤
      RCN001.coordinateMixedDegree K G T 1 +
        RCN001.coordinateMixedDegree K G T 2 := by
    rcases horder with hsame | hswap
    · subst order
      change RCN001.coordinateMixedDegree K
          (RCN125.flagAlgHom (0 : K) 0 a G)
          (RCN125.flagAlgHom (0 : K) 0 a T) 1 ≤ _
      exact coordinateMixedDegree_flag_shear_one_le a G T
    · subst order
      rw [RCN013.originalMixedDegree_swap]
      change RCN001.coordinateMixedDegree K
          (RCN125.flagAlgHom (0 : K) 0 a G)
          (RCN125.flagAlgHom (0 : K) 0 a T) 1 ≤ _
      exact coordinateMixedDegree_flag_shear_one_le a G T
  have hbound := hresult.2 |>.trans
    (RCN008.plane_budget_le_original K order
      (RCN125.flagAlgHom (0 : K) 0 a G)
      (RCN125.flagAlgHom (0 : K) 0 a T)) |>.trans htransformed
  have hpack := And.intro hresult.1 hbound
  let A : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) :=
    fun i => (elementEmbedding K (CoordinateField K (Q i))
      (e i (MvPolynomial.X (order 0))) (ht i)).toRingHom.toAlgebra
  let B : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) :=
    fun i => (elementEmbedding K (CoordinateField K (Q i))
      (RCN093.affineV K (Q i) 0 a) (hS i)).toRingHom.toAlgebra
  have hAB : A = B := by
    funext i
    exact congrArg (fun f => f.toRingHom.toAlgebra) (hemb i)
  change familyFiniteSummary Q A
    (RCN001.coordinateMixedDegree K G T 1 +
      RCN001.coordinateMixedDegree K G T 2) at hpack
  change familyFiniteSummary Q B
    (RCN001.coordinateMixedDegree K G T 1 +
      RCN001.coordinateMixedDegree K G T 2)
  rw [← hAB]
  exact hpack

/-- The outer-variable positivity required by the planar resultant is not an
extra source hypothesis: on a nonempty component family irreducibility chooses
one of the two non-base variables.  Swapping those two variables preserves the
mixed-degree budget.  The empty family is immediate. -/
theorem finite_sum_flag_shear_finrank_le_two_budgets_auto
    (hinj : Function.Injective Q) (a : K)
    (hS : ∀ i, Transcendental K (RCN093.affineV K (Q i) 0 a))
    (G T : MvPolynomial (Fin 3) K) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ Q i) (hTmem : ∀ i, T ∈ Q i)
    (hproper : ¬ G ∣ T) :
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (Q i)) :=
      fun i => (elementEmbedding K (CoordinateField K (Q i))
        (RCN093.affineV K (Q i) 0 a) (hS i)).toRingHom.toAlgebra
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (Q i))) ≤
        RCN001.coordinateMixedDegree K G T 1 +
          RCN001.coordinateMixedDegree K G T 2 := by
  classical
  by_cases hI : Nonempty I
  · let i0 : I := Classical.choice hI
    let order0 : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
    let e0 : MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K (Q i0) :=
      RCN093.flagEvaluation K (Q i0) 0 0 a
    have ht0 : Transcendental K (e0 (MvPolynomial.X (order0 0))) := by
      simpa [e0, order0, Equiv.swap_apply_def] using hS i0
    have hGroot0 : e0 (RCN125.flagAlgHom (0 : K) 0 a G) = 0 := by
      rw [show e0 (RCN125.flagAlgHom (0 : K) 0 a G) =
          coordinateEvaluation K (Q i0) G from
        RCN093.flagEvaluation_flag K (Q i0) 0 0 a G]
      change G ∈ RingHom.ker (coordinateEvaluation K (Q i0)).toRingHom
      rw [coordinateEvaluation_ker]
      exact hGmem i0
    have hirr := RCN021.rationalMap_irreducible_of_evaluation K
      (CoordinateField K (Q i0)) order0 e0
      (RCN125.flagAlgHom (0 : K) 0 a G)
      ((RCN125.flag_irreducible_iff 0 0 a G).mpr hG) hGroot0 ht0
    rcases RCN013.positive_degree_of_irreducible
        (rationalMap K order0 (RCN125.flagAlgHom (0 : K) 0 a G)) hirr with
      houter | hinner
    · apply finite_sum_flag_shear_finrank_le_two_budgets_of_order Q
        order0 (Or.inl rfl) hinj a hS G T hG hGmem hTmem hproper
      change 0 < (bivariateEquiv (RatFunc K)
        (rationalMap K order0
          (RCN125.flagAlgHom (0 : K) 0 a G))).natDegree
      rwa [bivariateEquiv_natDegree]
    · apply finite_sum_flag_shear_finrank_le_two_budgets_of_order Q
        (RCN013.swapOtherOrder order0) (Or.inr rfl)
        hinj a hS G T hG hGmem hTmem hproper
      rwa [RCN013.swapped_outer_degree]
  · letI : IsEmpty I := ⟨fun i => hI ⟨i⟩⟩
    constructor
    · intro i
      exact isEmptyElim i
    · simp

/-- Choose the coefficient using only the `Z`-transcendental components, but
charge *every* component on which the resulting `R + a Z` is transcendental
in one resultant family.  This includes the `Z`-algebraic/`R`-transcendental
case and is the form needed for the algebraic-`Z` fiber split. -/
theorem exists_common_shear_with_full_transcendental_sum_bound
    [IsAlgClosed K]
    (hinj : Function.Injective Q)
    (hfiniteZ : ∀ i (hZ : Transcendental K (coordinate K (Q i) 2)),
      letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
        rationalBaseAlgebra K (Q i) 2 hZ
      FiniteDimensional (RatFunc K) (CoordinateField K (Q i)))
    (hsepZ : ∀ i (hZ : Transcendental K (coordinate K (Q i) 2)),
      letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
        rationalBaseAlgebra K (Q i) 2 hZ
      Algebra.IsSeparable (RatFunc K) (CoordinateField K (Q i)))
    (G T : MvPolynomial (Fin 3) K) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ Q i) (hTmem : ∀ i, T ∈ Q i)
    (hproper : ¬ G ∣ T) :
    ∃ a : K, a ≠ 0 ∧
      (∀ i (hZ : Transcendental K (coordinate K (Q i) 2)),
        ∃ hS : Transcendental K
            (coordinate K (Q i) 1 + a • coordinate K (Q i) 2),
          (letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
              (elementEmbedding K (CoordinateField K (Q i))
                (coordinate K (Q i) 1 + a • coordinate K (Q i) 2)
                hS).toRingHom.toAlgebra;
            FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
          (letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
              (elementEmbedding K (CoordinateField K (Q i))
                (coordinate K (Q i) 1 + a • coordinate K (Q i) 2)
                hS).toRingHom.toAlgebra;
            Algebra.IsSeparable (RatFunc K) (CoordinateField K (Q i)))) ∧
      (let sS : Set I := {i | Transcendental K
          (RCN093.affineV K (Q i) 0 a)}
       let hS : ∀ i : sS,
          Transcendental K (RCN093.affineV K (Q i) 0 a) := fun i => i.2
       letI : ∀ i : sS,
          Algebra (RatFunc K) (CoordinateField K (Q i)) :=
         fun i => (elementEmbedding K (CoordinateField K (Q i))
           (RCN093.affineV K (Q i) 0 a) (hS i)).toRingHom.toAlgebra
       (∀ i : sS,
          FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
         (∑ i : sS,
            Module.finrank (RatFunc K) (CoordinateField K (Q i))) ≤
           RCN001.coordinateMixedDegree K G T 1 +
             RCN001.coordinateMixedDegree K G T 2) := by
  classical
  let sZ : Set I := {i | Transcendental K (coordinate K (Q i) 2)}
  obtain ⟨a, ha0, hzdata⟩ := exists_common_component_shear
    (Q := fun i : sZ => Q i)
    (fun i => i.2)
    (fun i => hfiniteZ i.1 i.2)
    (fun i => hsepZ i.1 i.2)
  have hzdata' : ∀ i (hZi : Transcendental K (coordinate K (Q i) 2)),
      ∃ hS : Transcendental K
          (coordinate K (Q i) 1 + a • coordinate K (Q i) 2),
        (letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
            (elementEmbedding K (CoordinateField K (Q i))
              (coordinate K (Q i) 1 + a • coordinate K (Q i) 2)
              hS).toRingHom.toAlgebra;
          FiniteDimensional (RatFunc K) (CoordinateField K (Q i))) ∧
        (letI : Algebra (RatFunc K) (CoordinateField K (Q i)) :=
            (elementEmbedding K (CoordinateField K (Q i))
              (coordinate K (Q i) 1 + a • coordinate K (Q i) 2)
              hS).toRingHom.toAlgebra;
          Algebra.IsSeparable (RatFunc K) (CoordinateField K (Q i))) := by
    intro i hZi
    exact hzdata ⟨i, hZi⟩
  refine ⟨a, ha0, hzdata', ?_⟩
  let sS : Set I := {i | Transcendental K
    (RCN093.affineV K (Q i) 0 a)}
  let hS : ∀ i : sS,
      Transcendental K (RCN093.affineV K (Q i) 0 a) := fun i => i.2
  exact finite_sum_flag_shear_finrank_le_two_budgets_auto
    (Q := fun i : sS => Q i) (fun _ _ h => Subtype.ext (hinj h))
    a hS G T hG (fun i => hGmem i) (fun i => hTmem i) hproper

end Family

end

end ProximityPrize.SubmissionLower.RCN988
end PackedLegacy_CommonShearDegreePrototype

/-! Packed from ProximityPrize.SubmissionLower.DD. -/
section PackedLegacy_DD
namespace ProximityPrize.SubmissionLower.RCN023
open scoped Classical BigOperators
open Field RCN002 RCN005 RCN007
noncomputable section
theorem char_le_finrank_of_not_isSeparable
   (F E:Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
   (p:ℕ) [CharP F p] (hp:p≠0)
   (hsep:¬ Algebra.IsSeparable F E):
   p ≤ Module.finrank F E:=by
 letI:Fact p.Prime:=⟨CharP.char_prime_of_ne_zero F hp⟩
 obtain ⟨n,hn⟩:=finInsepDegree_eq_pow (F:=F) (E:=E) p
 have hinsep_ne_one:finInsepDegree F E≠1:=by
   intro h
   apply hsep
   rw [←separableClosure.eq_top_iff,
     ←IntermediateField.finrank_eq_one_iff_eq_top]
   exact h
 have hn_ne_zero:n≠0:=by
   intro hn0
   subst n
   exact hinsep_ne_one (by simpa using hn)
 have hp_le_insep:p ≤ finInsepDegree F E:=by
   rw [hn]
   simpa only [pow_one] using
     Nat.pow_le_pow_right (CharP.char_prime_of_ne_zero F hp).pos
       (Nat.one_le_iff_ne_zero.mpr hn_ne_zero)
 have hinsep_le_finrank:finInsepDegree F E ≤ Module.finrank F E:=by
   rw [←Field.finSepDegree_mul_finInsepDegree]
   exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne _))
 exact hp_le_insep.trans hinsep_le_finrank
theorem isPurelyInseparable_of_finrank_eq_prime_of_not_isSeparable
   (F E:Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
   (p:ℕ) (hp:p.Prime)
   (hdegree:Module.finrank F E=p)
   (hsep:¬ Algebra.IsSeparable F E):
   IsPurelyInseparable F E:=by
 have hinsep_ne_one:Field.finInsepDegree F E≠1:=by
   intro hinsep
   exact hsep ((isSeparable_iff_finInsepDegree_eq_one F E).mpr hinsep)
 have hproduct:Field.finSepDegree F E*Field.finInsepDegree F E=p:=by
   rw [Field.finSepDegree_mul_finInsepDegree,hdegree]
 have hinsep_dvd:Field.finInsepDegree F E∣p:=
   ⟨Field.finSepDegree F E,by simpa only [Nat.mul_comm] using hproduct.symm⟩
 have hinsep_eq:Field.finInsepDegree F E=p:=
   (hp.eq_one_or_self_of_dvd _ hinsep_dvd).resolve_left hinsep_ne_one
 have hsepDegree:Field.finSepDegree F E=1:=by
   apply Nat.mul_right_cancel hp.pos
   simpa only [hinsep_eq,one_mul] using hproduct
 exact isPurelyInseparable_of_finSepDegree_eq_one hsepDegree
variable (K:Type) [Field K]
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
def ProjectionsFinite:Prop:=
 ∀ (i:Fin 3) (hi:Transcendental K (coordinate K P i)),
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   FiniteDimensional (RatFunc K) (CoordinateField K P)
theorem projectionsFinite_of_finiteSeparable
   (hproj:ProjectionsFiniteSeparable K P):ProjectionsFinite K P:=
 fun i hi↦(hproj i hi).1
variable [IsAlgClosed K]
theorem char_le_actualCoordinateDegree_of_not_isSeparable
   (hfinite:ProjectionsFinite K P) (p:ℕ) [CharP K p] (hp:p≠0)
   (i:Fin 3) (hi:Transcendental K (coordinate K P i))
   (hsep:
     letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
     ¬ Algebra.IsSeparable (RatFunc K) (CoordinateField K P)):
   p ≤ actualCoordinateDegree K P i:=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
 letI:FiniteDimensional (RatFunc K) (CoordinateField K P):=hfinite i hi
 rw [actualCoordinateDegree_of_transcendental K P i hi]
 apply char_le_finrank_of_not_isSeparable (RatFunc K) (CoordinateField K P) p
 · exact hp
 · exact hsep
theorem isSeparable_of_actualCoordinateDegree_lt_char
   (hfinite:ProjectionsFinite K P) (p:ℕ) [CharP K p] (hp:p≠0)
   (i:Fin 3) (hi:Transcendental K (coordinate K P i))
   (hdegree:actualCoordinateDegree K P i < p):
   letI:Algebra (RatFunc K) (CoordinateField K P):=
     rationalBaseAlgebra K P i hi
   Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=
   rationalBaseAlgebra K P i hi
 by_contra hsep
 exact (Nat.not_lt_of_ge
   (char_le_actualCoordinateDegree_of_not_isSeparable
     K P hfinite p hp i hi hsep)) hdegree
theorem family_coordinate_isSeparable_of_sum_degree_lt_char
   {I:Type} [Fintype I]
   (Q:I → Ideal (MvPolynomial (Fin 3) K)) [∀ i,(Q i).IsPrime]
   (hfinite:∀ i,ProjectionsFinite K (Q i))
   (p:ℕ) [CharP K p] (hp:p≠0) (j:Fin 3)
   (hsum:(∑ i,actualCoordinateDegree K (Q i) j) < p)
   (i:I) (hi:Transcendental K (coordinate K (Q i) j)):
   letI:Algebra (RatFunc K) (CoordinateField K (Q i)):=
     rationalBaseAlgebra K (Q i) j hi
   Algebra.IsSeparable (RatFunc K) (CoordinateField K (Q i)):=by
 apply isSeparable_of_actualCoordinateDegree_lt_char
   K (Q i) (hfinite i) p hp j hi
 exact (Finset.single_le_sum
   (s:=Finset.univ)
   (f:=fun k:I↦actualCoordinateDegree K (Q k) j)
   (fun _ _↦Nat.zero_le _) (Finset.mem_univ i)).trans_lt hsum
theorem finite_zero_points_le_box_of_finite_or_inseparable
   (hfinite:ProjectionsFinite K P)
   (p:ℕ) [CharP K p] (hp:p≠0)
   (hnonpoint:∀ v:Fin 3 → K,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 3) K) (hF:F∉P)
   (cap:Fin 3 → ℕ) (hcap:∀ i,F.degreeOf i ≤ cap i)
   (hcap_pos:∀ i,1 ≤ cap i)
   (S:Finset (Fin 3 → K)) (hS_card:S.card ≤ p)
   (hSP:∀ v∈S,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hSF:∀ v∈S,MvPolynomial.aeval v F=0):
   S.card ≤ ∑ i,cap i*actualCoordinateDegree K P i:=by
 classical
 by_cases hsep:∀ (i:Fin 3) (hi:Transcendental K (coordinate K P i)),
     letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P)
 · have hproj:ProjectionsFiniteSeparable K P:=fun i hi↦⟨hfinite i hi,hsep i hi⟩
   have hcount:=finite_zero_points_le_box K P hproj hnonpoint F hF cap hcap S hSP hSF
   exact_mod_cast hcount
 · push_neg at hsep
   obtain ⟨i,hi,hnotsep⟩:=hsep
   have hp_degree:p ≤ actualCoordinateDegree K P i:=
     char_le_actualCoordinateDegree_of_not_isSeparable K P hfinite p hp i hi hnotsep
   have hdegree_term:actualCoordinateDegree K P i ≤
       cap i*actualCoordinateDegree K P i:=
     Nat.le_mul_of_pos_left _ (hcap_pos i)
   have hterm_sum:cap i*actualCoordinateDegree K P i ≤
       ∑ j,cap j*actualCoordinateDegree K P j:=
     Finset.single_le_sum
       (s:=Finset.univ)
       (f:=fun j:Fin 3↦cap j*actualCoordinateDegree K P j)
       (fun _ _↦Nat.zero_le _) (Finset.mem_univ i)
   exact hS_card.trans (hp_degree.trans (hdegree_term.trans hterm_sum))
end
end ProximityPrize.SubmissionLower.RCN023
end PackedLegacy_DD

/-! Packed from ProximityPrize.SubmissionLower.X0. -/
section PackedLegacy_X0
namespace ProximityPrize.SubmissionLower.RCN368
open scoped Classical
noncomputable section
theorem add_not_mem_frobenius_range_of_mem_not_mem
   (L:Type*) [Field L] (p:ℕ) [ExpChar L p]
   {r z:L} (hr:r∈(frobenius L p).range)
   (hz:z∉(frobenius L p).range):
   r+z∉(frobenius L p).range:=by
 intro hrs
 apply hz
 have hsub:(r+z)-r∈(frobenius L p).range:=
   Subring.sub_mem (frobenius L p).range hrs hr
 simpa only [add_sub_cancel_left] using hsub
theorem pow_prime_mem_base_of_pure_degree_prime
   (F E:Type*) [Field F] [Field E] [Algebra F E]
   [FiniteDimensional F E] [IsPurelyInseparable F E]
   (p:ℕ) [ExpChar F p] (hp:p.Prime)
   (hdegree:Module.finrank F E=p) (x:E):
   x^p∈(algebraMap F E).range:=by
 obtain ⟨n,y,hmin⟩:=
   IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p x
 have hmin_degree:(minpoly F x).natDegree=p^n:=by
   rw [hmin,Polynomial.natDegree_sub_C,Polynomial.natDegree_X_pow]
 have hpow_le:p^n ≤ p:=by
   calc
     p^n=(minpoly F x).natDegree:=hmin_degree.symm
     _ ≤ Module.finrank F E:=minpoly.natDegree_le x
     _=p:=hdegree
 have hn_le:n ≤ 1:=by
   apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
   simpa only [pow_one] using hpow_le
 have hrel:x^p^n=algebraMap F E y:=by
   have hroot:=minpoly.aeval F x
   rw [hmin,map_sub,Polynomial.aeval_X_pow,Polynomial.aeval_C,
     sub_eq_zero] at hroot
   exact hroot
 rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn_le with rfl | rfl
 · have hx:x∈(algebraMap F E).range:=by
     refine ⟨y,?_⟩
     simpa only [pow_zero,pow_one] using hrel.symm
   exact Subring.pow_mem (algebraMap F E).range hx p
 · exact ⟨y,by simpa only [pow_one] using hrel.symm⟩
theorem separating_add_of_differential_criterion
   (K L:Type*) [Field K] [Field L] [Algebra K L]
   (D:Derivation K L L) (Separating:L → Prop)
   (hcriterion:∀ f,Separating f ↔ D f≠0)
   {r z:L} (hr:¬ Separating r) (hz:Separating z):
   Separating (r+z):=by
 rw [hcriterion]
 have hDr:D r=0:=by
   by_contra hne
   exact hr ((hcriterion r).mpr hne)
 have hDz:D z≠0:=(hcriterion z).mp hz
 rw [map_add,hDr,zero_add]
 exact hDz
theorem sheared_box_cost_le_old_add_two_penalty
   (cY cR cZ dY dR dZ dS:ℕ) (hS:dS ≤ dR+dZ):
   cY*dY+cR*dS+(cZ+cR)*dZ ≤
     (cY*dY+cR*dR+cZ*dZ)+2*cR*dZ:=by
 calc
   cY*dY+cR*dS+(cZ+cR)*dZ ≤
       cY*dY+cR*(dR+dZ)+(cZ+cR)*dZ:=by
         exact Nat.add_le_add_right
           (Nat.add_le_add_left (Nat.mul_le_mul_left cR hS) (cY*dY))
           ((cZ+cR)*dZ)
   _=(cY*dY+cR*dR+cZ*dZ)+2*cR*dZ:=by
     ring
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
set_option Elab.async false in
theorem PackedLegacyBarrier17 : True := by trivial
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
theorem adaptiveShearCost_eq (cap:Fin 3 → ℕ):
   adaptiveShearCost P cap=componentCost P cap+
     2*cap 1*actualCoordinateDegree Ω P 2:=by
 simp [adaptiveShearCost,adaptiveShearCap,componentCost,Fin.sum_univ_three]
 ring
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
theorem globalShearFiberCertificate_of_seedCoordinate_isAlgebraic
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (Γ:Finset K) (w dS:ℕ) (cap:Fin 3 → ℕ)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (hZ:IsAlgebraic Ω (coordinate Ω P 2))
   (hcost:1 ≤ globalShearCost P dS cap):
   GlobalShearFiberCertificate φ P F selected Γ w dS cap:=by
 apply globalShearFiberCertificate_of_card_le_one φ P F selected Γ w dS cap
 · exact selected_seed_set_card_le_one_of_seedCoordinate_isAlgebraic
     φ P selected Γ hpoint hZ
 · exact hcost
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
theorem rationalElementEmbedding_variable
   (k L:Type*) [Field k] [Field L] [Algebra k L]
   (s:L) (hs:Transcendental k s):
   rationalElementEmbedding k L s hs
       (algebraMap (Polynomial k) (RatFunc k) Polynomial.X)=s:=by
 exact elementEmbedding_variable k L s hs
theorem actual_shear_isSeparable
   (hR:Transcendental Ω (coordinate Ω P 1))
   (hZ:Transcendental Ω (coordinate Ω P 2))
   (hS:Transcendental Ω (coordinate Ω P 1+coordinate Ω P 2))
   (hfinite:ProjectionsFinite Ω P)
   (hnotsepR:
     letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
       rationalBaseAlgebra Ω P 1 hR
     ¬ Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
   (hsepZ:
     letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
       rationalBaseAlgebra Ω P 2 hZ
     Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)):
   letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
     (rationalElementEmbedding Ω (CoordinateField Ω P)
       (coordinate Ω P 1+coordinate Ω P 2) hS).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P):=by
 let embeddingR:=rationalBaseEmbedding Ω P 1 hR
 let embeddingZ:=rationalBaseEmbedding Ω P 2 hZ
 let embeddingS:=rationalElementEmbedding Ω (CoordinateField Ω P)
   (coordinate Ω P 1+coordinate Ω P 2) hS
 have hfiniteS:=finiteDimensional_elementEmbedding Ω (CoordinateField Ω P)
   embeddingZ (hfinite 2 hZ)
   (coordinate Ω P 1+coordinate Ω P 2) hS
 apply isSeparable_shear_of_not_isSeparable Ω (CoordinateField Ω P)
   embeddingR embeddingZ embeddingS (hfinite 1 hR) (hfinite 2 hZ)
   hfiniteS hnotsepR hsepZ
 dsimp only [embeddingR,embeddingZ,embeddingS]
 rw [rationalElementEmbedding_variable,
   rationalBaseEmbedding_polynomial,rationalBaseEmbedding_polynomial,
   Polynomial.aeval_X,Polynomial.aeval_X]
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
theorem actualCoordinateDataAt_value
   (hfinite:ProjectionsFinite Ω P) (i:Fin 3)
   (hsep:∀ hi:Transcendental Ω (coordinate Ω P i),
     letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
       rationalBaseAlgebra Ω P i hi
     Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)):
   coordinateValue Ω (CoordinateField Ω P)
     (actualCoordinateDataAt P hfinite i hsep)=coordinate Ω P i:=by
 unfold actualCoordinateDataAt
 split_ifs with hi
 · exact rational_variable_image Ω P i hi
 · exact (coordinate_eq_scalar_of_isAlgebraic Ω P i
     (not_not.mp hi)).choose_spec
theorem actualCoordinateDataAt_degree
   (hfinite:ProjectionsFinite Ω P) (i:Fin 3)
   (hsep:∀ hi:Transcendental Ω (coordinate Ω P i),
     letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=
       rationalBaseAlgebra Ω P i hi
     Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)):
   coordinateDegree Ω (CoordinateField Ω P)
     (actualCoordinateDataAt P hfinite i hsep)=actualCoordinateDegree Ω P i:=by
 unfold actualCoordinateDataAt actualCoordinateDegree
 split_ifs <;> rfl
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
theorem shearCoordinateData_value
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
   coordinateValue Ω (CoordinateField Ω P)
     (shearCoordinateData P hS hfiniteS hsepS)=
       coordinate Ω P 1+coordinate Ω P 2:=
 rationalElementEmbedding_variable Ω (CoordinateField Ω P)
   (coordinate Ω P 1+coordinate Ω P 2) hS
theorem sheared_degree_cost_le_adaptive
   (cap:Fin 3 → ℕ) (dS:ℕ)
   (hdegreeS:dS ≤ actualCoordinateDegree Ω P 1+
     actualCoordinateDegree Ω P 2):
   cap 0*actualCoordinateDegree Ω P 0+cap 1*dS+
       (cap 2+cap 1)*actualCoordinateDegree Ω P 2 ≤
     adaptiveShearCost P cap:=by
 have h:=sheared_box_cost_le_old_add_two_penalty
   (cap 0) (cap 1) (cap 2)
   (actualCoordinateDegree Ω P 0) (actualCoordinateDegree Ω P 1)
   (actualCoordinateDegree Ω P 2) dS hdegreeS
 simpa only [adaptiveShearCost_eq,componentCost,Fin.sum_univ_three] using h
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem prime_seed_incidence_sharp_adaptive_shear
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
   (hfiber:AdaptiveShearFiberCertificate φ P F selected Γ w cap):
   Γ.card*(a-w) ≤ (nodes.card-w)*adaptiveShearCost P cap+
     (e+1)*(a-w)*actualCoordinateDegree Ω P 2:=by
 classical
 let I:=identityNodes φ P F nodes x u₀ u₁ w
 let relation:K → ι → Prop:=
   fun γ i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i
 by_cases hI:I.card ≤ w
 · have hproperFiber:∀ i∈nodes \ I,
       (Γ.filter (fun γ↦relation γ i)).card ≤ adaptiveShearCost P cap:=by
     intro i hi
     obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
     have hproper:agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)∉P:=by
       intro hmem
       apply hnotI
       exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
     exact hfiber (x i) (u₀ i) (u₁ i) hproper (hcap i hinodes)
   have hcount:=RCN173.sharp_incidence_bound relation Γ nodes I a w
     (adaptiveShearCost P cap) (identityNodes_subset φ P F nodes x u₀ u₁ w)
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
theorem regularComponents_finite_and_degree_budget_charfree
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hproper:¬ G∣T):
   (∀ C:RegularComponent Ω G T (regularitySurface φ F),
     ProjectionsFinite Ω C.1)∧
     ∀ i,(∑ C:RegularComponent Ω G T (regularitySurface φ F),
       actualCoordinateDegree Ω C.1 i) ≤ coordinateMixedDegree Ω G T i:=by
 classical
 let H:=regularitySurface φ F
 letI:∀ C:RegularComponent Ω G T H,C.1.IsPrime:=
   fun C↦regularComponent_isPrime Ω G T H C
 have hfamily (i:Fin 3):=
   family_finite_and_sum_actualCoordinateDegree_at_le
     (Q:=fun C:RegularComponent Ω G T H↦C.1)
     Subtype.val_injective i G T hG
     (regularComponent_G_mem Ω G T H)
     (regularComponent_T_mem Ω G T H) hproper
 constructor
 · intro C i hi
   exact (hfamily i).1 C hi
 · intro i
   exact (hfamily i).2
theorem proper_cut_seed_bound_of_global_shear_sum
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F) (hproper:¬ G∣T)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hTpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) T=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap budget:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
   (hfinite:∀ C:RegularComponent Ω G T (regularitySurface φ F),
     ProjectionsFinite Ω C.1)
   (hbudget:∀ i,
     (∑ C:RegularComponent Ω G T (regularitySurface φ F),
       actualCoordinateDegree Ω C.1 i) ≤ budget i)
   (dS:RegularComponent Ω G T (regularitySurface φ F) → ℕ)
   (hSbudget:(∑ C,dS C) ≤ budget 1+budget 2)
   (hfiber:∀ C:RegularComponent Ω G T (regularitySurface φ F),
     GlobalShearFiberCertificate φ C.1 F selected
       (componentSeeds Ω G T (regularitySurface φ F) Γ
         (selectedPoint φ selected) C) w (dS C) cap):
   Γ.card*(a-w) ≤
     (nodes.card-w)*(∑ i,adaptiveShearCap cap i*budget i)+
       (e+1)*(a-w)*budget 2:=by
 classical
 let shearBudget:Fin 3 → ℕ:=![budget 0,budget 1+budget 2,budget 2]
 let degree:RegularComponent Ω G T (regularitySurface φ F) → Fin 3 → ℕ:=
   fun C↦globalShearDegree C.1 (dS C)
 have degree_zero (C:RegularComponent Ω G T (regularitySurface φ F)):
     degree C 0=actualCoordinateDegree Ω C.1 0:=by rfl
 have degree_one (C:RegularComponent Ω G T (regularitySurface φ F)):
     degree C 1=dS C:=by rfl
 have degree_two (C:RegularComponent Ω G T (regularitySurface φ F)):
     degree C 2=actualCoordinateDegree Ω C.1 2:=by rfl
 have shearBudget_zero:shearBudget 0=budget 0:=by rfl
 have shearBudget_one:shearBudget 1=budget 1+budget 2:=by rfl
 have shearBudget_two:shearBudget 2=budget 2:=by rfl
 have hHp:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ)
     (regularitySurface φ F)≠0:=by
   intro γ hγ
   change MvPolynomial.eval (selectedPoint φ selected γ)
     (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [selectedPoint_evaluation]
   exact hregular γ hγ
 have hcomponent:∀ C:RegularComponent Ω G T (regularitySurface φ F),
     (componentSeeds Ω G T (regularitySurface φ F) Γ
       (selectedPoint φ selected) C).card*(a-w) ≤
       (nodes.card-w)*(∑ i,shearedPolynomialCap cap i*degree C i)+
         (e+1)*(a-w)*degree C 2:=by
   intro C
   have hsub:=componentSeeds_subset Ω G T (regularitySurface φ F) Γ
     (selectedPoint φ selected) C
   have hgmem:=regularComponent_G_mem Ω G T (regularitySurface φ F) C
   have hFmem:surfaceMap φ F∈C.1:=
     ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
       (Ideal.mem_span_singleton.mpr hdiv)
   have hcount:=prime_seed_incidence_sharp_global_shear φ C.1 (hfinite C)
     (regularComponent_ne_point Ω G T (regularitySurface φ F) C) F hFmem
     (regularComponent_H_not_mem Ω G T (regularitySurface φ F) C) selected
     (componentSeeds Ω G T (regularitySurface φ F) Γ
       (selectedPoint φ selected) C)
     nodes x u₀ u₁ hinj p w a e hw hchar hwa han
     (fun γ hγ↦hdegree γ (hsub hγ))
     (fun γ hγ↦hsolution γ (hsub hγ))
     (fun γ hγ↦hregular γ (hsub hγ))
     (fun γ hγ↦componentSeeds_on_prime Ω G T (regularitySurface φ F) Γ
       (selectedPoint φ selected) C γ hγ)
     (fun γ hγ↦hagreement γ (hsub hγ))
     (noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil)
     cap hcap (dS C) (hfiber C)
   simpa only [globalShearCost,degree_two] using hcount
 have hdegreeBudget0:(∑ C,degree C 0) ≤ shearBudget 0:=by
   rw [shearBudget_zero]
   exact le_trans
     (Finset.sum_le_sum (fun C _↦le_of_eq (degree_zero C))) (hbudget 0)
 have hdegreeBudget1:(∑ C,degree C 1) ≤ shearBudget 1:=by
   rw [shearBudget_one]
   calc
     _=∑ C,dS C:=by
       apply Finset.sum_congr rfl
       intro C _
       exact degree_one C
     _ ≤ budget 1+budget 2:=hSbudget
 have hdegreeBudget2:(∑ C,degree C 2) ≤ shearBudget 2:=by
   rw [shearBudget_two]
   exact le_trans
     (Finset.sum_le_sum (fun C _↦le_of_eq (degree_two C))) (hbudget 2)
 have hdegreeBudget:∀ i,(∑ C,degree C i) ≤ shearBudget i:=by
   intro i
   fin_cases i
   · exact hdegreeBudget0
   · exact hdegreeBudget1
   · exact hdegreeBudget2
 have haggregate:=aggregate_component_incidence Ω G T (regularitySurface φ F) Γ
   (selectedPoint φ selected) hGpoint hTpoint hHp
   (a-w) (nodes.card-w) (e+1)
   (shearedPolynomialCap cap) shearBudget degree hcomponent hdegreeBudget
 have hcost:
     (∑ i,shearedPolynomialCap cap i*shearBudget i)=
       ∑ i,adaptiveShearCap cap i*budget i:=by
   simp [shearedPolynomialCap,adaptiveShearCap,shearBudget,Fin.sum_univ_three]
   ring
 rw [hcost] at haggregate
 simpa only [shearBudget_two] using haggregate
theorem proper_cut_seed_bound_of_projection_sum_adaptive_shear
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F) (hproper:¬ G∣T)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hTpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) T=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap budget:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
   (hfinite:∀ C:RegularComponent Ω G T (regularitySurface φ F),
     ProjectionsFinite Ω C.1)
   (hbudget:∀ i,
     (∑ C:RegularComponent Ω G T (regularitySurface φ F),
       actualCoordinateDegree Ω C.1 i) ≤ budget i)
   (hfiber:∀ C:RegularComponent Ω G T (regularitySurface φ F),
     AdaptiveShearFiberCertificate φ C.1 F selected
       (componentSeeds Ω G T (regularitySurface φ F) Γ
         (selectedPoint φ selected) C) w cap):
   Γ.card*(a-w) ≤
     (nodes.card-w)*(∑ i,adaptiveShearCap cap i*budget i)+
       (e+1)*(a-w)*budget 2:=by
 classical
 let H:=regularitySurface φ F
 have hHp:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) H≠0:=by
   intro γ hγ
   change MvPolynomial.eval (selectedPoint φ selected γ)
     (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [selectedPoint_evaluation]
   exact hregular γ hγ
 let degree:RegularComponent Ω G T H → Fin 3 → ℕ:=
   fun C i↦actualCoordinateDegree Ω C.1 i
 have hcomponent:∀ C:RegularComponent Ω G T H,
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C).card*(a-w) ≤
       (nodes.card-w)*(∑ i,adaptiveShearCap cap i*degree C i)+
         (e+1)*(a-w)*degree C 2:=by
   intro C
   have hsub:=componentSeeds_subset Ω G T H Γ (selectedPoint φ selected) C
   have hgmem:=regularComponent_G_mem Ω G T H C
   have hFmem:surfaceMap φ F∈C.1:=
     ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
       (Ideal.mem_span_singleton.mpr hdiv)
   have hcount:=prime_seed_incidence_sharp_adaptive_shear φ C.1 (hfinite C)
     (regularComponent_ne_point Ω G T H C) F hFmem
     (regularComponent_H_not_mem Ω G T H C) selected
     (componentSeeds Ω G T H Γ (selectedPoint φ selected) C)
     nodes x u₀ u₁ hinj p w a e hw hchar hwa han
     (fun γ hγ↦hdegree γ (hsub hγ))
     (fun γ hγ↦hsolution γ (hsub hγ))
     (fun γ hγ↦hregular γ (hsub hγ))
     (fun γ hγ↦componentSeeds_on_prime Ω G T H Γ
       (selectedPoint φ selected) C γ hγ)
     (fun γ hγ↦hagreement γ (hsub hγ))
     (noLargeSelectedPencil_mono selected Γ _ w e hsub hnoPencil)
     cap hcap (hfiber C)
   simpa only [adaptiveShearCost,componentCost,degree] using hcount
 exact aggregate_component_incidence Ω G T H Γ (selectedPoint φ selected)
   hGpoint hTpoint hHp (a-w) (nodes.card-w) (e+1)
   (adaptiveShearCap cap) budget degree hcomponent hbudget
theorem proper_cut_seed_bound_adaptive_shear
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F) (hproper:¬ G∣T)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hTpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) T=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i↦(selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
   (hfiber:∀ C:RegularComponent Ω G T (regularitySurface φ F),
     AdaptiveShearFiberCertificate φ C.1 F selected
       (componentSeeds Ω G T (regularitySurface φ F) Γ
         (selectedPoint φ selected) C) w cap):
   Γ.card*(a-w) ≤
     (nodes.card-w)*
         (∑ i,adaptiveShearCap cap i*coordinateMixedDegree Ω G T i)+
       (e+1)*(a-w)*coordinateMixedDegree Ω G T 2:=by
 have hgeom:=regularComponents_finite_and_degree_budget_charfree φ F G T hG hproper
 exact proper_cut_seed_bound_of_projection_sum_adaptive_shear
   φ F G T hG hdiv hproper selected Γ nodes x u₀ u₁ hinj
   p w a e hw hchar hwa han hdegree hsolution hregular hGpoint hTpoint
   hagreement hnoPencil cap (coordinateMixedDegree Ω G T) hcap
   hgeom.1 hgeom.2 hfiber
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
theorem globalShearCost_pos_of_seedCoordinate_isAlgebraic
   (hfinite:ProjectionsFinite K P)
   (hnonpoint:∀ v:Fin 3 → K,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hZ:IsAlgebraic K (coordinate K P 2))
   (a:K) (dS:ℕ) (cap:Fin 3 → ℕ)
   (hSdegree:Transcendental K
       (coordinate K P 1+a • coordinate K P 2) → 1 ≤ dS)
   (hcapY:1 ≤ cap 0) (hcapS:1 ≤ cap 1):
   1 ≤ globalShearCost P dS cap:=by
 obtain ⟨j,hj⟩:=
   exists_transcendental_coordinate_of_ne_point_kernel K P hnonpoint
 rw [globalShearCost_eq]
 fin_cases j
 · have hdY:1 ≤ actualCoordinateDegree K P 0:=
     coordinateDegree_pos_of_transcendental_finite P hfinite 0 hj
   calc
     1=1*1:=by norm_num
     _ ≤ cap 0*actualCoordinateDegree K P 0:=
       Nat.mul_le_mul hcapY hdY
     _ ≤ cap 0*actualCoordinateDegree K P 0+cap 1*dS+
         (cap 2+cap 1)*actualCoordinateDegree K P 2:=by omega
 · have hS:Transcendental K
       (coordinate K P 1+a • coordinate K P 2):=
     transcendental_add_smul_of_transcendental_isAlgebraic
       K P _ _ a hj hZ
   have hdS:1 ≤ dS:=hSdegree hS
   calc
     1=1*1:=by norm_num
     _ ≤ cap 1*dS:=Nat.mul_le_mul hcapS hdS
     _ ≤ cap 0*actualCoordinateDegree K P 0+cap 1*dS+
         (cap 2+cap 1)*actualCoordinateDegree K P 2:=by omega
 · exact (hj hZ).elim
end
end ProximityPrize.SubmissionLower.RCN142
end PackedLegacy_EO

/-! Packed from ProximityPrize.SubmissionLower.CommonShearFiberPrototype. -/
section PackedLegacy_CommonShearFiberPrototype

namespace ProximityPrize.SubmissionLower.CommonShearFiberPrototype

open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN007 RCN022 RCN023 RCN045 RCN067 RCN142 RCN231
  RCN238 RCN319 RCN344 RCN370 RCN372

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
variable (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]

theorem eval₂Hom_shear_at_add
    {A : Type} [CommRing A] [Algebra Ω A]
    (F : MvPolynomial (Fin 3) Ω) (y r z : A) (a : Ω) :
    MvPolynomial.eval₂Hom (algebraMap Ω A)
        ![y, r + algebraMap Ω A a * z, z] (shearAlgHom a F) =
      MvPolynomial.eval₂Hom (algebraMap Ω A) ![y, r, z] F := by
  have hhom :
      (MvPolynomial.eval₂Hom (algebraMap Ω A)
          ![y, r + algebraMap Ω A a * z, z]).comp
          (shearAlgHom a).toRingHom =
        MvPolynomial.eval₂Hom (algebraMap Ω A) ![y, r, z] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [RingHom.comp_apply, shearAlgHom]
    · intro i
      fin_cases i <;>
        simp [RingHom.comp_apply, shearAlgHom, shearImage] <;> ring
  exact RingHom.congr_fun hhom F

def shearedRingCoordinatesAt (a : Ω) : Fin 3 → CoordinateRing Ω P :=
  ![quotientCoordinate Ω P 0,
    quotientCoordinate Ω P 1 +
      algebraMap Ω (CoordinateRing Ω P) a * quotientCoordinate Ω P 2,
    quotientCoordinate Ω P 2]

theorem shearedPolynomialTransportAt_of_degree
    (a : Ω) (A : MvPolynomial (Fin 3) Ω) (cap : Fin 3 → ℕ)
    (hcap : ∀ i, A.degreeOf i ≤ cap i) :
    ∃ B : MvPolynomial (Fin 3) Ω,
      (∀ i, B.degreeOf i ≤ shearedPolynomialCap cap i) ∧
        MvPolynomial.eval₂Hom (algebraMap Ω (CoordinateRing Ω P))
          (shearedRingCoordinatesAt P a) B = Ideal.Quotient.mk P A := by
  refine ⟨shearAlgHom a A, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact (shear_degreeOf_zero_le a A).trans (hcap 0)
    · exact (shear_degreeOf_one_le a A).trans (hcap 1)
    · exact (shear_degreeOf_two_le a A).trans
        (Nat.add_le_add (hcap 2) (hcap 1))
  · rw [← quotient_eval_eq_mk]
    have h := eval₂Hom_shear_at_add
        (A := CoordinateRing Ω P) A
        (quotientCoordinate Ω P 0) (quotientCoordinate Ω P 1)
        (quotientCoordinate Ω P 2) a
    change MvPolynomial.eval₂Hom (algebraMap Ω (CoordinateRing Ω P))
      (shearedRingCoordinatesAt P a) (shearAlgHom a A) = _
    rw [show shearedRingCoordinatesAt P a =
        ![quotientCoordinate Ω P 0,
          quotientCoordinate Ω P 1 +
            algebraMap Ω (CoordinateRing Ω P) a * quotientCoordinate Ω P 2,
          quotientCoordinate Ω P 2] by rfl]
    rw [h]
    congr 2
    funext i
    fin_cases i <;> rfl

def shearCoordinateDataAt (a : Ω)
    (hS : Transcendental Ω
      (coordinate Ω P 1 + a • coordinate Ω P 2))
    (hfiniteS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra;
      FiniteDimensional (RatFunc Ω) (CoordinateField Ω P))
    (hsepS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)) :
    Coordinate Ω (CoordinateField Ω P) :=
  Sum.inr {
    embedding := elementEmbedding Ω (CoordinateField Ω P)
      (coordinate Ω P 1 + a • coordinate Ω P 2) hS
    finite := hfiniteS
    separable := hsepS }

theorem shearCoordinateDataAt_value (a : Ω)
    (hS : Transcendental Ω
      (coordinate Ω P 1 + a • coordinate Ω P 2))
    (hfiniteS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Ω) (CoordinateField Ω P))
    (hsepS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)) :
    coordinateValue Ω (CoordinateField Ω P)
      (shearCoordinateDataAt P a hS hfiniteS hsepS) =
        coordinate Ω P 1 + a • coordinate Ω P 2 := by
  exact elementEmbedding_variable Ω (CoordinateField Ω P)
    (coordinate Ω P 1 + a • coordinate Ω P 2) hS

theorem shearCoordinateDataAt_degree (a : Ω)
    (hS : Transcendental Ω
      (coordinate Ω P 1 + a • coordinate Ω P 2))
    (hfiniteS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Ω) (CoordinateField Ω P))
    (hsepS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P)) :
    coordinateDegree Ω (CoordinateField Ω P)
      (shearCoordinateDataAt P a hS hfiniteS hsepS) =
        (letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
          (elementEmbedding Ω (CoordinateField Ω P)
            (coordinate Ω P 1 + a • coordinate Ω P 2)
            hS).toRingHom.toAlgebra;
          Module.finrank (RatFunc Ω) (CoordinateField Ω P)) := by
  rfl

theorem finite_zero_points_le_global_of_common_shear
    (hfinite : ProjectionsFinite Ω P)
    (hnonpoint : ∀ v : Fin 3 → Ω,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hZ : Transcendental Ω (coordinate Ω P 2))
    (hsepY : ∀ hY : Transcendental Ω (coordinate Ω P 0),
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        rationalBaseAlgebra Ω P 0 hY
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (hsepZ : ∀ hZ' : Transcendental Ω (coordinate Ω P 2),
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        rationalBaseAlgebra Ω P 2 hZ'
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (a : Ω)
    (hS : Transcendental Ω
      (coordinate Ω P 1 + a • coordinate Ω P 2))
    (hfiniteS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Ω) (CoordinateField Ω P))
    (hsepS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (A : MvPolynomial (Fin 3) Ω) (hA : A ∉ P)
    (cap : Fin 3 → ℕ) (hcap : ∀ i, A.degreeOf i ≤ cap i)
    (points : Finset (Fin 3 → Ω))
    (hpointsP : ∀ v ∈ points,
      P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hpointsA : ∀ v ∈ points, MvPolynomial.aeval v A = 0) :
    points.card ≤ globalShearCost P
      (letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra;
        Module.finrank (RatFunc Ω) (CoordinateField Ω P)) cap := by
  classical
  let embeddingS := elementEmbedding Ω (CoordinateField Ω P)
    (coordinate Ω P 1 + a • coordinate Ω P 2) hS
  let dS : ℕ :=
    letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
      embeddingS.toRingHom.toAlgebra
    Module.finrank (RatFunc Ω) (CoordinateField Ω P)
  obtain ⟨B, hBcap, hBquot⟩ :=
    shearedPolynomialTransportAt_of_degree P a A cap hcap

  letI : Algebra (Polynomial Ω) (CoordinateRing Ω P) :=
    quotientPolynomialAlgebra Ω P 2
  letI : Algebra (Polynomial Ω) (CoordinateField Ω P) :=
    polynomialBaseAlgebra Ω P 2
  letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
    rationalBaseAlgebra Ω P 2 hZ
  letI := quotientBaseScalarTower Ω P 2
  letI := polynomialBaseScalarTower Ω P 2
  letI := quotientFractionScalarTower Ω P 2
  letI := polynomialRationalScalarTower Ω P 2 hZ
  letI := rationalBaseScalarTower Ω P 2 hZ
  letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω P) :=
    hfinite 2 hZ
  letI : Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P) :=
    hsepZ hZ

  let c : Fin 3 → Coordinate Ω (CoordinateField Ω P) :=
    ![actualCoordinateDataAt P hfinite 0 hsepY,
      shearCoordinateDataAt P a hS hfiniteS hsepS,
      actualCoordinateDataAt P hfinite 2 hsepZ]
  have hc : ∀ j,
      coordinateValue Ω (CoordinateField Ω P) (c j) =
        algebraMap (CoordinateRing Ω P) (CoordinateField Ω P)
          (shearedRingCoordinatesAt P a j) := by
    intro j
    fin_cases j
    · change coordinateValue Ω (CoordinateField Ω P)
          (actualCoordinateDataAt P hfinite 0 hsepY) =
        algebraMap (CoordinateRing Ω P) (CoordinateField Ω P)
          (quotientCoordinate Ω P 0)
      rw [quotientCoordinate_fraction]
      exact actualCoordinateDataAt_value P hfinite 0 hsepY
    · change coordinateValue Ω (CoordinateField Ω P)
          (shearCoordinateDataAt P a hS hfiniteS hsepS) =
        algebraMap (CoordinateRing Ω P) (CoordinateField Ω P)
          (quotientCoordinate Ω P 1 +
            algebraMap Ω (CoordinateRing Ω P) a * quotientCoordinate Ω P 2)
      rw [map_add, map_mul, quotientCoordinate_fraction,
        quotientCoordinate_fraction]
      rw [← IsScalarTower.algebraMap_apply Ω (CoordinateRing Ω P)
        (CoordinateField Ω P)]
      simpa only [Algebra.smul_def] using
        shearCoordinateDataAt_value P a hS hfiniteS hsepS
    · change coordinateValue Ω (CoordinateField Ω P)
          (actualCoordinateDataAt P hfinite 2 hsepZ) =
        algebraMap (CoordinateRing Ω P) (CoordinateField Ω P)
          (quotientCoordinate Ω P 2)
      rw [quotientCoordinate_fraction]
      exact actualCoordinateDataAt_value P hfinite 2 hsepZ
  have hcdegree : ∀ j,
      coordinateDegree Ω (CoordinateField Ω P) (c j) =
        globalShearDegree P dS j := by
    intro j
    fin_cases j
    · exact actualCoordinateDataAt_degree P hfinite 0 hsepY
    · exact shearCoordinateDataAt_degree P a hS hfiniteS hsepS
    · exact actualCoordinateDataAt_degree P hfinite 2 hsepZ
  have hBnonzero :
      MvPolynomial.eval₂Hom
        (algebraMap Ω (CoordinateRing Ω P))
        (shearedRingCoordinatesAt P a) B ≠ 0 := by
    rw [hBquot]
    intro hzero
    exact hA (Ideal.Quotient.eq_zero_iff_mem.mp hzero)

  let liftPoint : {v : Fin 3 → Ω // v ∈ points} →
      (CoordinateRing Ω P →ₐ[Ω] Ω) :=
    fun v => pointHom Ω P ⟨v.1, hpointsP v.1 v.2⟩
  have hlift_injective : Function.Injective liftPoint := by
    intro v w hvw
    have hpoint := pointHom_injective Ω P hvw
    apply Subtype.ext
    exact congrArg (fun z : PointOn Ω P => z.val) hpoint
  let modelPoints := points.attach.image liftPoint
  have hmodelPoints : ∀ ψ ∈ modelPoints,
      ψ (MvPolynomial.eval₂Hom
        (algebraMap Ω (CoordinateRing Ω P))
        (shearedRingCoordinatesAt P a) B) = 0 := by
    intro ψ hψ
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hψ
    calc
      liftPoint v (MvPolynomial.eval₂Hom
          (algebraMap Ω (CoordinateRing Ω P))
          (shearedRingCoordinatesAt P a) B) =
          liftPoint v (Ideal.Quotient.mk P A) :=
            congrArg (fun q => liftPoint v q) hBquot
      _ = MvPolynomial.aeval v.1 A := pointHom_mk Ω P _ A
      _ = 0 := hpointsA v.1 v.2
  have hcount := finite_model_zero_points_le_box
    Ω (CoordinateField Ω P) (CoordinateRing Ω P)
    (shearedRingCoordinatesAt P a) c hc (shearedPolynomialCap cap)
    B hBcap hBnonzero modelPoints hmodelPoints
  have hcountNat : modelPoints.card ≤
      ∑ j, shearedPolynomialCap cap j *
        coordinateDegree Ω (CoordinateField Ω P) (c j) := by
    exact_mod_cast hcount
  have hsum :
      (∑ j, shearedPolynomialCap cap j *
        coordinateDegree Ω (CoordinateField Ω P) (c j)) =
        globalShearCost P dS cap := by
    unfold globalShearCost
    apply Finset.sum_congr rfl
    intro j _
    rw [hcdegree j]
  rw [hsum] at hcountNat
  have hcard : modelPoints.card = points.card := by
    change (points.attach.image liftPoint).card = points.card
    rw [Finset.card_image_of_injective _ hlift_injective,
      Finset.card_attach]
  rw [hcard] at hcountNat
  exact hcountNat

variable {K : Type} [Field K]
variable (φ : Polynomial K →+* Ω)
local instance : DecidableEq K := Classical.decEq K

theorem globalShearFiberCertificate_of_common_shear
    (hfinite : ProjectionsFinite Ω P)
    (hnonpoint : ∀ v : Fin 3 → Ω,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hZ : Transcendental Ω (coordinate Ω P 2))
    (hsepY : ∀ hY : Transcendental Ω (coordinate Ω P 0),
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        rationalBaseAlgebra Ω P 0 hY
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (hsepZ : ∀ hZ' : Transcendental Ω (coordinate Ω P 2),
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        rationalBaseAlgebra Ω P 2 hZ'
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (a : Ω)
    (hS : Transcendental Ω
      (coordinate Ω P 1 + a • coordinate Ω P 2))
    (hfiniteS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      FiniteDimensional (RatFunc Ω) (CoordinateField Ω P))
    (hsepS :
      letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω P))
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Γ : Finset K) (p w : ℕ) [CharP Ω p] (hchar : w < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom
      (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ
        (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : ∀ γ ∈ Γ, P ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
    (cap : Fin 3 → ℕ) :
    GlobalShearFiberCertificate φ P F selected Γ w
      (letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra;
        Module.finrank (RatFunc Ω) (CoordinateField Ω P)) cap := by
  classical
  intro x u₀ u₁ hproper hcap
  let fiber := Γ.filter (fun γ => (selected γ).eval x = u₀ + γ * u₁)
  let points := fiber.image (selectedPoint φ selected)
  have hpointsP : ∀ v ∈ points,
      P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hv
    have hγ' : γ ∈ Γ.filter
        (fun η => (selected η).eval x = u₀ + η * u₁) := by
      simpa only [fiber] using hγ
    exact hpoint γ (Finset.mem_filter.mp hγ').1
  have hpointsA : ∀ v ∈ points,
      MvPolynomial.aeval v (agreementPolynomial φ F w x u₀ u₁) = 0 := by
    intro v hv
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hv
    have hγ' : γ ∈ Γ.filter
        (fun η => (selected η).eval x = u₀ + η * u₁) := by
      simpa only [fiber] using hγ
    obtain ⟨hγΓ, hagree⟩ := Finset.mem_filter.mp hγ'
    exact (selected_agreement_zero_iff φ F selected p w hchar γ
      (hdegree γ hγΓ) (hsolution γ hγΓ) (hregular γ hγΓ)
      x u₀ u₁).mpr hagree
  have hcount := finite_zero_points_le_global_of_common_shear P
    hfinite hnonpoint hZ hsepY hsepZ a hS hfiniteS hsepS
    (agreementPolynomial φ F w x u₀ u₁) hproper cap hcap
    points hpointsP hpointsA
  have hcard : points.card = fiber.card :=
    Finset.card_image_of_injective _ (selectedPoint_injective φ selected)
  have hfiber : fiber.card ≤ globalShearCost P
      (letI : Algebra (RatFunc Ω) (CoordinateField Ω P) :=
        (elementEmbedding Ω (CoordinateField Ω P)
          (coordinate Ω P 1 + a • coordinate Ω P 2)
          hS).toRingHom.toAlgebra;
        Module.finrank (RatFunc Ω) (CoordinateField Ω P)) cap := by
    rwa [← hcard]
  simpa only [fiber] using hfiber

theorem globalShearFiberCertificate_of_algebraic_z
    (hfinite : ProjectionsFinite Ω P)
    (hnonpoint : ∀ v : Fin 3 → Ω,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hZalg : IsAlgebraic Ω (coordinate Ω P 2))
    (a : Ω) (dS : ℕ)
    (hSdegree : Transcendental Ω
      (coordinate Ω P 1 + a • coordinate Ω P 2) → 1 ≤ dS)
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Γ : Finset K) (w : ℕ)
    (hpoint : ∀ γ ∈ Γ, P ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
    (cap : Fin 3 → ℕ) (hcapY : 1 ≤ cap 0) (hcapS : 1 ≤ cap 1) :
    GlobalShearFiberCertificate φ P F selected Γ w dS cap := by
  apply globalShearFiberCertificate_of_seedCoordinate_isAlgebraic
    φ P F selected Γ w dS cap hpoint hZalg
  exact globalShearCost_pos_of_seedCoordinate_isAlgebraic
    Ω P hfinite hnonpoint hZalg a dS cap hSdegree hcapY hcapS

end

end ProximityPrize.SubmissionLower.CommonShearFiberPrototype
end PackedLegacy_CommonShearFiberPrototype

/-! Packed from ProximityPrize.SubmissionLower.CommonShearFamilyPrototype. -/
section PackedLegacy_CommonShearFamilyPrototype

namespace ProximityPrize.SubmissionLower.CommonShearFamilyPrototype

open scoped Classical BigOperators
open RCN001 RCN002 RCN005 RCN006 RCN007 RCN022 RCN023 RCN045 RCN067 RCN093
  RCN231 RCN238 RCN319 RCN344 RCN370 RCN372
open CommonShearFiberPrototype RCN988

noncomputable section

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 2000000

variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable (φ : Polynomial K →+* Ω)
local instance : DecidableEq K := Classical.decEq K

variable {I : Type} [Fintype I]
  (Q : I → Ideal (MvPolynomial (Fin 3) Ω)) [∀ i, (Q i).IsPrime]

private theorem elementEmbedding_congr_local
    {L : Type} [Field L] [Algebra Ω L] {s t : L}
    (hs : Transcendental Ω s) (ht : Transcendental Ω t) (h : s = t) :
    elementEmbedding Ω L s hs = elementEmbedding Ω L t ht := by
  subst t
  rfl

/-- Complete input package for `proper_cut_seed_bound_of_global_shear_sum`:
one common nonzero shear, one degree per component, the aggregate degree
budget, and a `GlobalShearFiberCertificate` for every component.  Components
with algebraic `Z` use the cardinality-one route; all transcendental sheared
coordinates (including algebraic-`Z`/transcendental-`R`) are charged together
by the family resultant. -/
theorem exists_common_global_shear_family
    (hinj : Function.Injective Q)
    (hfinite : ∀ i, ProjectionsFinite Ω (Q i))
    (hnonpoint : ∀ i (v : Fin 3 → Ω),
      Q i ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hsepY : ∀ i (hY : Transcendental Ω (coordinate Ω (Q i) 0)),
      letI : Algebra (RatFunc Ω) (CoordinateField Ω (Q i)) :=
        rationalBaseAlgebra Ω (Q i) 0 hY
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (Q i)))
    (hsepZ : ∀ i (hZ : Transcendental Ω (coordinate Ω (Q i) 2)),
      letI : Algebra (RatFunc Ω) (CoordinateField Ω (Q i)) :=
        rationalBaseAlgebra Ω (Q i) 2 hZ
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (Q i)))
    (G T : MvPolynomial (Fin 3) Ω) (hG : Irreducible G)
    (hGmem : ∀ i, G ∈ Q i) (hTmem : ∀ i, T ∈ Q i)
    (hproper : ¬ G ∣ T)
    (F : MvPolynomial (Fin 4) K) (selected : K → Polynomial K)
    (Γ : I → Finset K) (p w : ℕ) [CharP Ω p] (hchar : w < p)
    (hdegree : ∀ i γ, γ ∈ Γ i → (selected γ).natDegree ≤ w)
    (hsolution : ∀ i γ, γ ∈ Γ i →
      specialization K (selected γ) γ F = 0)
    (hregular : ∀ i γ, γ ∈ Γ i → MvPolynomial.eval₂Hom
      (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ
        (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hpoint : ∀ i γ, γ ∈ Γ i → Q i ≤ RingHom.ker
      (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
    (cap : Fin 3 → ℕ) (hcapY : 1 ≤ cap 0) (hcapS : 1 ≤ cap 1) :
    ∃ a : Ω, a ≠ 0 ∧ ∃ dS : I → ℕ,
      (∑ i, dS i) ≤ coordinateMixedDegree Ω G T 1 +
          coordinateMixedDegree Ω G T 2 ∧
      ∀ i, GlobalShearFiberCertificate φ (Q i) F selected (Γ i) w
        (dS i) cap := by
  classical
  obtain ⟨a, ha0, hzdata, hall⟩ :=
    exists_common_shear_with_full_transcendental_sum_bound Q hinj
      (fun i hZ => hfinite i 2 hZ) hsepZ
      G T hG hGmem hTmem hproper
  let sS : Set I := {i | Transcendental Ω (affineV Ω (Q i) 0 a)}
  let hSsub : ∀ i : sS, Transcendental Ω (affineV Ω (Q i) 0 a) :=
    fun i => i.2
  let D : sS → ℕ := fun i =>
    letI : Algebra (RatFunc Ω) (CoordinateField Ω (Q i)) :=
      (elementEmbedding Ω (CoordinateField Ω (Q i))
        (affineV Ω (Q i) 0 a) (hSsub i)).toRingHom.toAlgebra
    Module.finrank (RatFunc Ω) (CoordinateField Ω (Q i))
  let dS : I → ℕ := fun i =>
    if hSi : Transcendental Ω (affineV Ω (Q i) 0 a) then
      letI : Algebra (RatFunc Ω) (CoordinateField Ω (Q i)) :=
        (elementEmbedding Ω (CoordinateField Ω (Q i))
          (affineV Ω (Q i) 0 a) hSi).toRingHom.toAlgebra
      Module.finrank (RatFunc Ω) (CoordinateField Ω (Q i))
    else 0
  have hall' :
      letI : ∀ i : sS,
          Algebra (RatFunc Ω) (CoordinateField Ω (Q i)) :=
        fun i => (elementEmbedding Ω (CoordinateField Ω (Q i))
          (affineV Ω (Q i) 0 a) (hSsub i)).toRingHom.toAlgebra
      (∀ i : sS,
        FiniteDimensional (RatFunc Ω) (CoordinateField Ω (Q i))) ∧
        (∑ i : sS,
          Module.finrank (RatFunc Ω) (CoordinateField Ω (Q i))) ≤
            coordinateMixedDegree Ω G T 1 +
              coordinateMixedDegree Ω G T 2 := by
    simpa only [sS, hSsub] using hall
  have hsum : (∑ i, dS i) ≤ coordinateMixedDegree Ω G T 1 +
      coordinateMixedDegree Ω G T 2 := by
    calc
      (∑ i, dS i) = ∑ i : sS, D i := by
        apply Finset.sum_congr_set sS dS D
        · intro i hi
          change Transcendental Ω (affineV Ω (Q i) 0 a) at hi
          simp only [dS, dif_pos hi, D, hSsub]
        · intro i hi
          change ¬ Transcendental Ω (affineV Ω (Q i) 0 a) at hi
          simp only [dS, dif_neg hi]
      _ ≤ _ := by
        exact hall'.2
  refine ⟨a, ha0, dS, hsum, ?_⟩
  intro i
  by_cases hZi : Transcendental Ω (coordinate Ω (Q i) 2)
  · obtain ⟨hSi, hfiniteSi, hsepSi⟩ := hzdata i hZi
    have hSaffine : Transcendental Ω (affineV Ω (Q i) 0 a) := by
      simpa [affineV] using hSi
    have hfiber := globalShearFiberCertificate_of_common_shear
      (Q i) φ (hfinite i) (hnonpoint i) hZi (hsepY i) (hsepZ i)
      a hSi hfiniteSi hsepSi F selected (Γ i) p w hchar
      (fun γ hγ => hdegree i γ hγ)
      (fun γ hγ => hsolution i γ hγ)
      (fun γ hγ => hregular i γ hγ)
      (fun γ hγ => hpoint i γ hγ) cap
    have hemb :
        elementEmbedding Ω (CoordinateField Ω (Q i))
            (affineV Ω (Q i) 0 a) hSaffine =
          elementEmbedding Ω (CoordinateField Ω (Q i))
            (coordinate Ω (Q i) 1 + a • coordinate Ω (Q i) 2) hSi :=
      elementEmbedding_congr_local hSaffine hSi (by simp [affineV])
    have hdS : dS i =
        (letI : Algebra (RatFunc Ω) (CoordinateField Ω (Q i)) :=
          (elementEmbedding Ω (CoordinateField Ω (Q i))
            (coordinate Ω (Q i) 1 + a • coordinate Ω (Q i) 2)
            hSi).toRingHom.toAlgebra;
          Module.finrank (RatFunc Ω) (CoordinateField Ω (Q i))) := by
      rw [show dS i =
          (letI : Algebra (RatFunc Ω) (CoordinateField Ω (Q i)) :=
            (elementEmbedding Ω (CoordinateField Ω (Q i))
              (affineV Ω (Q i) 0 a) hSaffine).toRingHom.toAlgebra;
            Module.finrank (RatFunc Ω) (CoordinateField Ω (Q i))) by
        simp only [dS, dif_pos hSaffine]]
      rw [hemb]
    rw [hdS]
    exact hfiber
  · have hZalg : IsAlgebraic Ω (coordinate Ω (Q i) 2) := not_not.mp hZi
    have hSdegree : Transcendental Ω
        (coordinate Ω (Q i) 1 + a • coordinate Ω (Q i) 2) →
        1 ≤ dS i := by
      intro hSi
      have hSaffine : Transcendental Ω (affineV Ω (Q i) 0 a) := by
        simpa [affineV] using hSi
      let j : sS := ⟨i, hSaffine⟩
      letI : Algebra (RatFunc Ω) (CoordinateField Ω (Q i)) :=
        (elementEmbedding Ω (CoordinateField Ω (Q i))
          (affineV Ω (Q i) 0 a) hSaffine).toRingHom.toAlgebra
      have hfd : FiniteDimensional (RatFunc Ω)
          (CoordinateField Ω (Q i)) := by
        simpa only [j, sS, hSsub] using hall'.1 j
      letI : FiniteDimensional (RatFunc Ω) (CoordinateField Ω (Q i)) := hfd
      have hpos : 1 ≤ Module.finrank (RatFunc Ω)
          (CoordinateField Ω (Q i)) := Module.finrank_pos
      simpa only [dS, dif_pos hSaffine] using hpos
    exact globalShearFiberCertificate_of_algebraic_z
      (Q i) φ (hfinite i) (hnonpoint i) hZalg a (dS i) hSdegree
      F selected (Γ i) w (fun γ hγ => hpoint i γ hγ)
      cap hcapY hcapS

end

end ProximityPrize.SubmissionLower.CommonShearFamilyPrototype
end PackedLegacy_CommonShearFamilyPrototype

/-! Packed from ProximityPrize.SubmissionLower.CommonShearConsumerPrototype. -/
section PackedLegacy_CommonShearConsumerPrototype

namespace ProximityPrize.SubmissionLower.CommonShearConsumerPrototype

open scoped Classical BigOperators
open RCN001 RCN002 RCN003 RCN005 RCN006 RCN007 RCN022 RCN023 RCN045 RCN051
  RCN067 RCN068 RCN081 RCN093 RCN135 RCN136 RCN137 RCN138 RCN169 RCN170
  RCN172 RCN174 RCN231 RCN238 RCN243 RCN264 RCN319 RCN344 RCN370 RCN372
open CommonShearFamilyPrototype

noncomputable section

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 2000000

variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable (φ : Polynomial K →+* Ω)
variable {ι : Type*}
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Ω := Classical.decEq Ω
local instance : DecidableEq ι := Classical.decEq ι

/-- A proper-cut seed bound obtained from one common shear across all regular
components.  Only the original `Y` and `Z` characteristic gates are needed:
the `R` projection is replaced by the common `R + a Z` coordinate. -/
theorem proper_cut_seed_bound_of_common_global_shear
    (F : MvPolynomial (Fin 4) K) (G T : MvPolynomial (Fin 3) Ω)
    (hG : Irreducible G) (hdiv : G ∣ surfaceMap φ F) (hproper : ¬ G ∣ T)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (p w a e : ℕ) [CharP Ω p] (hw : 1 ≤ w) (hchar : w < p)
    (hwa : w < a) (han : a ≤ nodes.card)
    (hGdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixedY : coordinateMixedDegree Ω G T 0 < p)
    (hmixedZ : coordinateMixedDegree Ω G T 2 < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolution : ∀ γ ∈ Γ, specialization K (selected γ) γ F = 0)
    (hregular : ∀ γ ∈ Γ, MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
      (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ
        (φ Polynomial.X))
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hGpoint : ∀ γ ∈ Γ,
      MvPolynomial.eval (selectedPoint φ selected γ) G = 0)
    (hTpoint : ∀ γ ∈ Γ,
      MvPolynomial.eval (selectedPoint φ selected γ) T = 0)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i =>
        (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e)
    (cap : Fin 3 → ℕ)
    (hcap : ∀ i ∈ nodes, ∀ j,
      (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)).degreeOf j ≤ cap j)
    (hcapY : 1 ≤ cap 0) (hcapR : 1 ≤ cap 1) :
    Γ.card * (a - w) ≤
      (nodes.card - w) *
        (∑ i, adaptiveShearCap cap i * coordinateMixedDegree Ω G T i) +
      (e + 1) * (a - w) * coordinateMixedDegree Ω G T 2 := by
  classical
  let H := regularitySurface φ F
  let Component := RegularComponent Ω G T H
  have hgeom :=
    regularComponents_finite_and_degree_budget_charfree φ F G T hG hproper
  have hsepY : ∀ C : Component,
      ∀ hY : Transcendental Ω (coordinate Ω C.1 0),
        letI : Algebra (RatFunc Ω) (CoordinateField Ω C.1) :=
          rationalBaseAlgebra Ω C.1 0 hY
        Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1) := by
    intro C hY
    exact (finite_separable_at_of_original_coordinate_gate Ω C.1 0 hY p G T
      hG (regularComponent_G_mem Ω G T H C)
      (regularComponent_T_mem Ω G T H C) hproper hGdegree hmixedY).2
  have hsepZ : ∀ C : Component,
      ∀ hZ : Transcendental Ω (coordinate Ω C.1 2),
        letI : Algebra (RatFunc Ω) (CoordinateField Ω C.1) :=
          rationalBaseAlgebra Ω C.1 2 hZ
        Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1) := by
    intro C hZ
    exact (finite_separable_at_of_original_coordinate_gate Ω C.1 2 hZ p G T
      hG (regularComponent_G_mem Ω G T H C)
      (regularComponent_T_mem Ω G T H C) hproper hGdegree hmixedZ).2
  obtain ⟨shear, hshear, dS, hSbudget, hfiber⟩ :=
    exists_common_global_shear_family φ
      (Q := fun C : Component => C.1) Subtype.val_injective hgeom.1
      (fun C => regularComponent_ne_point Ω G T H C)
      hsepY hsepZ G T hG
      (regularComponent_G_mem Ω G T H)
      (regularComponent_T_mem Ω G T H) hproper F selected
      (fun C : Component =>
        componentSeeds Ω G T H Γ (selectedPoint φ selected) C)
      p w hchar
      (fun C γ hγ => hdegree γ
        (componentSeeds_subset Ω G T H Γ (selectedPoint φ selected) C hγ))
      (fun C γ hγ => hsolution γ
        (componentSeeds_subset Ω G T H Γ (selectedPoint φ selected) C hγ))
      (fun C γ hγ => hregular γ
        (componentSeeds_subset Ω G T H Γ (selectedPoint φ selected) C hγ))
      (fun C γ hγ => componentSeeds_on_prime Ω G T H Γ
        (selectedPoint φ selected) C γ hγ)
      cap hcapY hcapR
  exact proper_cut_seed_bound_of_global_shear_sum φ F G T hG hdiv hproper
    selected Γ nodes x u₀ u₁ hinj p w a e hw hchar hwa han hdegree
    hsolution hregular hGpoint hTpoint hagreement hnoPencil cap
    (coordinateMixedDegree Ω G T) hcap hgeom.1 hgeom.2 dS hSbudget hfiber

/-- Generic implicit-pair incidence bound using the common global shear.  It
removes the old mixed `R` characteristic premise `2 * jY * jZ < p`; the exact
price is the `2 * w` contribution to the `Z` coefficient below. -/
theorem implicit_pair_seed_bound_common_global_shear
    (A G : MvPolynomial (Fin 4) K) (hG : Irreducible G)
    (hGR : G.degreeOf 2 = 1) (hproper : ¬ G ∣ A)
    (implicitD w jY jZ p n a e : ℕ)
    (hAbox : A ∈ globalCoefficientBox K implicitD w jZ 0)
    (hGbox : G ∈ globalCoefficientBox K implicitD w jZ 1)
    (hjY : (implicitD - 1) / w = jY)
    (selected : K → Polynomial K) (Γ : Finset K)
    (nodes : Finset ι) (x u₀ u₁ : ι → K) (hinj : Set.InjOn x nodes)
    (hnodes : nodes.card = n) [CharP K p]
    (hw : 1 ≤ w) (hchar : w < p) (hwa : w < a) (han : a ≤ n)
    (hjYsmall : jY < p) (hjZsmall : jZ < p)
    (hdegree : ∀ γ ∈ Γ, (selected γ).natDegree ≤ w)
    (hsolutionA : ∀ γ ∈ Γ, specialization K (selected γ) γ A = 0)
    (hsolutionG : ∀ γ ∈ Γ, specialization K (selected γ) γ G = 0)
    (hregular : ∀ γ ∈ Γ,
      specialization K (selected γ) γ (MvPolynomial.pderiv (2 : Fin 4) G) ≠ 0)
    (hagreement : ∀ γ ∈ Γ,
      a ≤ (nodes.filter (fun i =>
        (selected γ).eval (x i) = u₀ i + γ * u₁ i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Γ w e) :
    Γ.card * (a - w) ≤
      (n - w) *
        ((1 + 2 * w * jY) * pairYCost ⟨A, G⟩ +
          w * pairRCost ⟨A, G⟩ +
          (2 * w * jZ + 1 + 2 * w) * pairZCost ⟨A, G⟩) +
      (e + 1) * (a - w) * pairZCost ⟨A, G⟩ := by
  classical
  let φ := polynomialEmbedding K
  let factors := surfaceFactors φ G
  let seedsFor := fun g : MvPolynomial (Fin 3) (GenericField K) =>
    Γ.filter (fun γ => MvPolynomial.eval (selectedPoint φ selected γ) g = 0)
  let surfaceCap : RCN051.DegreeVector := ⟨jY, 1, jZ⟩
  let cutCap : RCN051.DegreeVector := ⟨jY, 0, jZ⟩
  let agreementCap : RCN051.DegreeVector :=
    ⟨1 + 2 * w * jY, w, 2 * w * jZ + 1⟩
  have hsub (g) : seedsFor g ⊆ Γ := Finset.filter_subset _ _
  have hAGcaps := degree_bounds_of_mem_box A implicitD w jZ 0 hw hAbox
  have hGGcaps := degree_bounds_of_mem_box G implicitD w jZ 1 hw hGbox
  have hAY : A.degreeOf 1 ≤ jY := hAGcaps.1.trans_eq hjY
  have hGY : G.degreeOf 1 ≤ jY := hGGcaps.1.trans_eq hjY
  have hAR : A.degreeOf 2 = 0 := Nat.eq_zero_of_le_zero hAGcaps.2.1
  have hAcaps : HasCaps (surfaceMap φ A) cutCap := by
    intro i
    fin_cases i
    · exact (surfaceMap_degreeOf_le φ A 0).trans hAY
    · exact (surfaceMap_degreeOf_le φ A 1).trans hAGcaps.2.1
    · exact (surfaceMap_degreeOf_le φ A 2).trans hAGcaps.2.2
  have hFzero : ∀ γ ∈ Γ,
      MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ G) = 0 := by
    intro γ hγ
    rw [RCN170.canonical_selectedPoint_surface_evaluation,
      hsolutionG γ hγ, map_zero]
  have hAzero : ∀ γ ∈ Γ,
      MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ A) = 0 := by
    intro γ hγ
    rw [RCN170.canonical_selectedPoint_surface_evaluation,
      hsolutionA γ hγ, map_zero]
  have hcover : Γ ⊆ factors.biUnion seedsFor := by
    intro γ hγ
    obtain ⟨g, hg, hz⟩ := exists_surfaceFactor_zero φ
      (polynomialEmbedding_injective K) G hG.ne_zero
      (selectedPoint φ selected γ) (hFzero γ hγ)
    exact Finset.mem_biUnion.mpr
      ⟨g, hg, Finset.mem_filter.mpr ⟨hγ, hz⟩⟩
  have hcard : Γ.card ≤ ∑ g ∈ factors, (seedsFor g).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hsingle (g : MvPolynomial (Fin 3) (GenericField K)) (hg : g ∈ factors) :
      (seedsFor g).card * (a - w) ≤
        (n - w) * (∑ i : Fin 3,
          adaptiveShearCap (capAt agreementCap) i *
            capAt (RCN170.geometricPairCost A g) i) +
        (e + 1) * (a - w) *
          capAt (RCN170.geometricPairCost A g) 2 := by
    obtain ⟨hgi, hdiv⟩ := surfaceFactors_spec φ G g hg
    have hfacdegree (i : Fin 3) : g.degreeOf i ≤ G.degreeOf i.succ :=
      (coordinate_degree_le_of_dvd i g (surfaceMap φ G) hdiv
        (surfaceMap_ne_zero φ (polynomialEmbedding_injective K) G
          hG.ne_zero)).trans (surfaceMap_degreeOf_le φ G i)
    have hgcaps : HasCaps g surfaceCap := by
      intro i
      fin_cases i
      · exact (hfacdegree 0).trans hGY
      · exact (hfacdegree 1).trans hGGcaps.2.1
      · exact (hfacdegree 2).trans hGGcaps.2.2
    have hsurfaceSmall : ∀ j, capAt surfaceCap j < p := by
      intro j
      fin_cases j
      · simpa [surfaceCap, capAt] using hjYsmall
      · simpa [surfaceCap, capAt] using lt_of_le_of_lt hw hchar
      · simpa [surfaceCap, capAt] using hjZsmall
    have hGdegree : ∀ j : Fin 3, g.degreeOf j < p :=
      fun j => (hgcaps j).trans_lt (hsurfaceSmall j)
    have hmixedYactual : coordinateMixedDegree (GenericField K) g
        (surfaceMap φ A) 0 < p := by
      have hpair := actual_pair_degree_le g (surfaceMap φ A)
        surfaceCap cutCap hgcaps hAcaps 1 2
      have hcapbound :
          capAt cutCap 1 * capAt surfaceCap 2 +
            capAt surfaceCap 1 * capAt cutCap 2 ≤ jZ := by
        simp [surfaceCap, cutCap, capAt]
      exact (hpair.trans hcapbound).trans_lt hjZsmall
    have hmixedZactual : coordinateMixedDegree (GenericField K) g
        (surfaceMap φ A) 2 < p := by
      have hpair := actual_pair_degree_le g (surfaceMap φ A)
        surfaceCap cutCap hgcaps hAcaps 0 1
      have hcapbound :
          capAt cutCap 0 * capAt surfaceCap 1 +
            capAt surfaceCap 0 * capAt cutCap 1 ≤ jY := by
        simp [surfaceCap, cutCap, capAt]
      simpa [coordinateMixedDegree_two] using
        (hpair.trans hcapbound).trans_lt hjYsmall
    have hreg : ∀ γ ∈ seedsFor g,
        MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
          (RCN231.polynomialPoint (φ.comp Polynomial.C)
            (selected γ) γ (φ Polynomial.X))
          (MvPolynomial.pderiv (2 : Fin 4) G) ≠ 0 := by
      intro γ hγ
      exact (initialPoint_regular_iff K G (selected γ) γ).mpr
        (hregular γ (hsub g hγ))
    have hcap (i : ι) : HasCaps
        (agreementPolynomial φ G w (x i) (u₀ i) (u₁ i)) agreementCap := by
      have h := surface_agreement_caps φ G jY 1 jZ (by decide)
        hGY hGGcaps.2.1 hGGcaps.2.2 w
        (fun j => (j.factorial : K)⁻¹) (x i) (u₀ i) (u₁ i)
      simpa [agreementPolynomial, agreementCaps, agreementCap] using h
    have hcount := proper_cut_seed_bound_of_common_global_shear φ G g
      (surfaceMap φ A) hgi hdiv
      (RCN170.geometric_factor_proper_cut A G hG hGR hproper g hg)
      selected (seedsFor g) nodes x u₀ u₁ hinj p w a e hw hchar hwa
      (by simpa [hnodes] using han) hGdegree hmixedYactual hmixedZactual
      (fun γ hγ => hdegree γ (hsub g hγ))
      (fun γ hγ => hsolutionG γ (hsub g hγ)) hreg
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
      (fun γ hγ => hAzero γ (hsub g hγ))
      (fun γ hγ => hagreement γ (hsub g hγ))
      (noLargeSelectedPencil_mono selected Γ _ w e (hsub g) hnoPencil)
      (capAt agreementCap) (fun i _ => hcap i)
      (by simp [agreementCap, capAt]) (by simpa [agreementCap, capAt] using hw)
    rw [hnodes] at hcount
    have hδ (i : Fin 3) :=
      RCN170.coordinateMixedDegree_le_geometricPairCost φ A hAR g i
    exact hcount.trans (Nat.add_le_add
      (Nat.mul_le_mul_left (n - w) (Finset.sum_le_sum
        (fun i _ => Nat.mul_le_mul_left
          (adaptiveShearCap (capAt agreementCap) i) (hδ i))))
      (Nat.mul_le_mul_left ((e + 1) * (a - w)) (hδ 2)))
  have hbudget (i : Fin 3) :
      (∑ g ∈ factors, capAt (RCN170.geometricPairCost A g) i) ≤
        capAt (RCN170.pairCost A G) i :=
    RCN170.sum_geometricPairCost_le φ
      (polynomialEmbedding_injective K) A G hG.ne_zero i
  have hfubini :
      (∑ g ∈ factors, ∑ i : Fin 3,
        adaptiveShearCap (capAt agreementCap) i *
          capAt (RCN170.geometricPairCost A g) i) =
      ∑ i : Fin 3, adaptiveShearCap (capAt agreementCap) i *
        (∑ g ∈ factors, capAt (RCN170.geometricPairCost A g) i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  calc
    Γ.card * (a - w) ≤ (∑ g ∈ factors, (seedsFor g).card) * (a - w) :=
      Nat.mul_le_mul_right (a - w) hcard
    _ = ∑ g ∈ factors, (seedsFor g).card * (a - w) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ g ∈ factors,
        ((n - w) * (∑ i : Fin 3,
          adaptiveShearCap (capAt agreementCap) i *
            capAt (RCN170.geometricPairCost A g) i) +
          (e + 1) * (a - w) *
            capAt (RCN170.geometricPairCost A g) 2) :=
      Finset.sum_le_sum (fun g hg => hsingle g hg)
    _ = (n - w) * (∑ i : Fin 3,
          adaptiveShearCap (capAt agreementCap) i *
            (∑ g ∈ factors, capAt (RCN170.geometricPairCost A g) i)) +
        (e + 1) * (a - w) *
          (∑ g ∈ factors, capAt (RCN170.geometricPairCost A g) 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hfubini]
    _ ≤ (n - w) * (∑ i : Fin 3,
          adaptiveShearCap (capAt agreementCap) i *
            capAt (RCN170.pairCost A G) i) +
        (e + 1) * (a - w) * capAt (RCN170.pairCost A G) 2 :=
      Nat.add_le_add
        (Nat.mul_le_mul_left (n - w) (Finset.sum_le_sum
          (fun i _ => Nat.mul_le_mul_left
            (adaptiveShearCap (capAt agreementCap) i) (hbudget i))))
        (Nat.mul_le_mul_left ((e + 1) * (a - w)) (hbudget 2))
    _ = (n - w) *
        ((1 + 2 * w * jY) * pairYCost ⟨A, G⟩ +
          w * pairRCost ⟨A, G⟩ +
          (2 * w * jZ + 1 + 2 * w) * pairZCost ⟨A, G⟩) +
        (e + 1) * (a - w) * pairZCost ⟨A, G⟩ := by
      simp [Fin.sum_univ_three, adaptiveShearCap, capAt, agreementCap,
        RCN170.pairCost]

end

end ProximityPrize.SubmissionLower.CommonShearConsumerPrototype
end PackedLegacy_CommonShearConsumerPrototype

/-! Packed from ProximityPrize.SubmissionLower.CommonShearTightPrototype. -/
section PackedLegacy_CommonShearTightPrototype

namespace ProximityPrize.SubmissionLower.CommonShearTightPrototype

open scoped Classical BigOperators
open RCN169 RCN167 RCN174 RCN238 RCN243 RCN291 RCN294 RCN318 RCN319

noncomputable section

set_option maxHeartbeats 3000000

variable {K : Type} [Field K]
variable {Iota : Type}
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota

abbrev TightParameters := RCN318.TightParameters

/-- The only numerical change caused by the common-shear incidence theorem is
the extra `2 * w` coefficient on the aggregate Z cost. -/
def agreement (P : TightParameters) : RCN223.DegreeVector :=
  ⟨1 + 2 * P.w * P.implicitYCap,
    P.w,
    2 * P.w * P.algebraicCap + 1 + 2 * P.w⟩

def coefficients (P : TightParameters) : RCN223.DegreeVector :=
  ⟨(P.n - P.w) * (agreement P).y,
    (P.n - P.w) * (agreement P).r,
    (P.n - P.w) * (agreement P).z + (P.errors + 1) * P.gap⟩

def coreNumerator (P : TightParameters) : ℕ :=
  (P.n - P.w) * RCN294.dot (agreement P) P.aggregateCost +
    (P.errors + 1) * P.gap * P.implicitYCap

def tightNumerator (P : TightParameters) : ℕ :=
  coreNumerator P + 2 * P.algebraicCap ^ 2 * P.gap

def countCap (P : TightParameters) : ℕ := tightNumerator P / P.gap

theorem bound_eq_dot (P : TightParameters) (v : RCN223.DegreeVector) :
    (P.n - P.w) * RCN294.dot (agreement P) v +
        (P.errors + 1) * P.gap * v.z =
      RCN294.dot v (coefficients P) := by
  simp only [agreement, coefficients, RCN318.TightParameters.errors,
    RCN318.TightParameters.gap, RCN294.dot]
  ring

theorem aggregate_eq_core (P : TightParameters) :
    RCN294.dot P.aggregateCost (coefficients P) = coreNumerator P := by
  simp only [agreement, coefficients, coreNumerator,
    RCN318.TightParameters.aggregateCost, RCN318.TightParameters.errors,
    RCN318.TightParameters.gap, RCN294.dot]
  ring

theorem sum_counts_bound (P : TightParameters) {I : Type} [Fintype I]
    (count : I → ℕ) (cost : I → RCN223.DegreeVector)
    (hy : (∑ i, (cost i).y) ≤ P.algebraicCap)
    (hr : (∑ i, (cost i).r) ≤
      2 * P.implicitYCap * P.algebraicCap)
    (hz : (∑ i, (cost i).z) ≤ P.implicitYCap)
    (hcount : ∀ i, count i * P.gap ≤
      (P.n - P.w) * RCN294.dot (agreement P) (cost i) +
        (P.errors + 1) * P.gap * (cost i).z) :
    (∑ i, count i) * P.gap ≤ coreNumerator P := by
  calc
    (∑ i, count i) * P.gap = ∑ i, count i * P.gap :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ i, RCN294.dot (cost i) (coefficients P) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← bound_eq_dot]
      exact hcount i
    _ = RCN294.dot (RCN294.sumVector cost) (coefficients P) :=
      (RCN294.dot_sum_left cost (coefficients P)).symm
    _ ≤ RCN294.dot P.aggregateCost (coefficients P) :=
      RCN294.dot_mono_left (coefficients P) ⟨hy, hr, hz⟩
    _ = coreNumerator P := aggregate_eq_core P

theorem with_exceptions_bound (P : TightParameters)
    {I : Type} [Fintype I]
    (count : I → ℕ) (cost : I → RCN223.DegreeVector)
    (exceptions : ℕ)
    (hy : (∑ i, (cost i).y) ≤ P.algebraicCap)
    (hr : (∑ i, (cost i).r) ≤
      2 * P.implicitYCap * P.algebraicCap)
    (hz : (∑ i, (cost i).z) ≤ P.implicitYCap)
    (hcount : ∀ i, count i * P.gap ≤
      (P.n - P.w) * RCN294.dot (agreement P) (cost i) +
        (P.errors + 1) * P.gap * (cost i).z)
    (hexceptions : exceptions ≤ 2 * P.algebraicCap ^ 2) :
    ((∑ i, count i) + exceptions) * P.gap ≤ tightNumerator P := by
  have hmain := sum_counts_bound P count cost hy hr hz hcount
  calc
    ((∑ i, count i) + exceptions) * P.gap =
        (∑ i, count i) * P.gap + exceptions * P.gap := Nat.add_mul _ _ _
    _ ≤ coreNumerator P + 2 * P.algebraicCap ^ 2 * P.gap :=
      Nat.add_le_add hmain (Nat.mul_le_mul_right P.gap hexceptions)
    _ = tightNumerator P := rfl

theorem count_le_countCap (P : TightParameters) (count : ℕ)
    (hgap : 0 < P.gap) (hcount : count * P.gap ≤ tightNumerator P) :
    count ≤ countCap P := by
  exact (Nat.le_div_iff_mul_le hgap).mpr hcount

theorem implicitSeeds_pair_bound_of_profile
    (P : TightParameters) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    {p : ℕ} [CharP K p]
    (hbox : Q ∈ globalCoefficientBox K P.D P.w P.L P.s)
    (hs : 1 ≤ P.s) (hsSmall : P.s < p)
    (hw : 1 ≤ P.w) (hchar : P.w < p)
    (hDw : P.w < P.kappa * P.D)
    (hjYSmall : P.implicitYCap < p)
    (hjZSmall : P.algebraicCap < p)
    (hwa : P.w < P.a) (han : P.a ≤ P.n)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma,
      P.a ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma P.w P.errors)
    (q : RCN291.ImplicitIndex Q) :
    (RCN291.implicitSeeds Q selected Gamma q).card * P.gap ≤
      (P.n - P.w) * RCN294.dot (agreement P) (RCN291.implicitVector Q q) +
        (P.errors + 1) * P.gap * (RCN291.implicitVector Q q).z := by
  classical
  obtain ⟨hJ, hJboxRaw⟩ := RCN293.singularAuxiliary_nonzero_mem_box Q
    P.D P.w P.L P.s p hQ hs hsSmall hbox
  have hJbox : RCN290.singularAuxiliary Q ∈
      globalCoefficientBox K (P.kappa * P.D) P.w P.algebraicCap 0 := by
    simpa [RCN318.TightParameters.kappa,
      RCN318.TightParameters.algebraicCap] using hJboxRaw
  obtain ⟨_hA, hG, hGR, hAbox, hGbox, hproper⟩ :=
    RCN286.implicitPair_data (RCN290.singularAuxiliary Q) hJ
      (P.kappa * P.D) P.w P.algebraicCap hw hDw hJbox q.1 q.2
  have hsub := RCN291.implicitSeeds_subset Q selected Gamma q
  have hpair :=
    CommonShearConsumerPrototype.implicit_pair_seed_bound_common_global_shear
      q.1.1 q.1.2 hG hGR hproper
      (P.kappa * P.D) P.w P.implicitYCap P.algebraicCap
      p P.n P.a P.errors hAbox hGbox rfl selected
      (RCN291.implicitSeeds Q selected Gamma q) nodes x u0 u1 hinj hnodes
      hw hchar hwa han hjYSmall hjZSmall
      (fun gamma hgamma => hdegree gamma (hsub hgamma))
      (fun gamma hgamma =>
        (RCN291.implicitSeeds_solution Q selected Gamma q gamma hgamma).1)
      (fun gamma hgamma =>
        (RCN291.implicitSeeds_solution Q selected Gamma q gamma hgamma).2.2.1)
      (fun gamma hgamma =>
        (RCN291.implicitSeeds_solution Q selected Gamma q gamma hgamma).2.2.2)
      (fun gamma hgamma => hagreement gamma (hsub hgamma))
      (noLargeSelectedPencil_mono selected Gamma _ P.w P.errors hsub hnoPencil)
  simpa [RCN291.implicitVector, agreement,
    RCN318.TightParameters.errors, RCN318.TightParameters.gap,
    RCN294.dot] using hpair

theorem singularSeeds_tight_gap_bound
    (P : TightParameters) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    {p : ℕ} [CharP K p]
    (hbox : Q ∈ globalCoefficientBox K P.D P.w P.L P.s)
    (hs : 1 ≤ P.s) (hsSmall : P.s < p)
    (hw : 1 ≤ P.w) (hchar : P.w < p)
    (hDw : P.w < P.kappa * P.D)
    (hj : 1 ≤ P.algebraicCap)
    (hjYSmall : P.implicitYCap < p)
    (hjZSmall : P.algebraicCap < p)
    (hwa : P.w < P.a) (han : P.a ≤ P.n)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma,
      P.a ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma P.w P.errors) :
    (RCN291.singularSeeds Q selected Gamma).card * P.gap ≤
      tightNumerator P := by
  have hcaps := RCN292.TightParameters.implicitVector_budgets_of_profile
    P Q hQ hbox hs hsSmall hw
  have hexc := RCN292.TightParameters.exceptionalSeeds_bound_of_profile
    P Q hQ hbox hs hsSmall hj hjZSmall selected Gamma
  have hsum := with_exceptions_bound P
    (fun q : RCN291.ImplicitIndex Q =>
      (RCN291.implicitSeeds Q selected Gamma q).card)
    (RCN291.implicitVector Q)
    (RCN286.exceptionalSeeds (RCN290.singularAuxiliary Q) Gamma selected).card
    hcaps.1 hcaps.2.1 hcaps.2.2
    (implicitSeeds_pair_bound_of_profile P Q hQ hbox hs hsSmall hw hchar
      hDw hjYSmall hjZSmall hwa han selected Gamma nodes x u0 u1 hinj
      hnodes hdegree hagreement hnoPencil)
    hexc
  exact (Nat.mul_le_mul_right P.gap
    (RCN291.singularSeeds_card_le_sum Q selected Gamma)).trans hsum

theorem singularSeeds_count_le_countCap
    (P : TightParameters) (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    {p : ℕ} [CharP K p]
    (hbox : Q ∈ globalCoefficientBox K P.D P.w P.L P.s)
    (hs : 1 ≤ P.s) (hsSmall : P.s < p)
    (hw : 1 ≤ P.w) (hchar : P.w < p)
    (hDw : P.w < P.kappa * P.D)
    (hj : 1 ≤ P.algebraicCap)
    (hjYSmall : P.implicitYCap < p)
    (hjZSmall : P.algebraicCap < p)
    (hwa : P.w < P.a) (han : P.a ≤ P.n)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = P.n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ P.w)
    (hagreement : ∀ gamma ∈ Gamma,
      P.a ≤ (nodes.filter (fun i =>
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma P.w P.errors) :
    (RCN291.singularSeeds Q selected Gamma).card ≤ countCap P := by
  apply count_le_countCap P _ (by
    simpa [RCN318.TightParameters.gap] using Nat.sub_pos_of_lt hwa)
  exact singularSeeds_tight_gap_bound P Q hQ hbox hs hsSmall hw hchar hDw
    hj hjYSmall hjZSmall hwa han selected Gamma nodes x u0 u1 hinj hnodes
    hdegree hagreement hnoPencil

end

end ProximityPrize.SubmissionLower.CommonShearTightPrototype
end PackedLegacy_CommonShearTightPrototype

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
theorem gcd_mul_right_of_isRelPrime_associated
   (P H q:Poly4 K) (hc:IsRelPrime q P) :
   Associated (gcd P (H * q)) (gcd P H):=by
 apply associated_of_dvd_dvd
 · have hleft:gcd P (H * q) ∣ P:=gcd_dvd_left P (H * q)
   have hright:gcd P (H * q) ∣ H * q:=gcd_dvd_right P (H * q)
   have hcop:IsRelPrime (gcd P (H * q)) q :=
     hc.symm.of_dvd_left hleft
   exact dvd_gcd hleft (hcop.dvd_of_dvd_mul_right hright)
 · exact dvd_gcd (gcd_dvd_left P H)
     ((gcd_dvd_right P H).trans (dvd_mul_right H q))
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
theorem gateC :
   Fintype.card IRSProfile.Index * localRankBound 41 41787 12 <
     coefficientCount 7463722 131071 41787 12:=by
 rw [show Fintype.card IRSProfile.Index = 262144 by
   norm_num [IRSProfile.Index]]
 rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
   7463722 131071 41787 12 57 (by decide) (by decide)]
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
theorem globalTailCut_in_sharp_flag (φ:Polynomial K →+*Ω)
   (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
   (hR:F.degreeOf 2 ≤ s+2)
   (hYR:wt ![0,1,1,0] F ≤ b+s+3)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s+3) (d:ℕ):
   PolynomialInFlag
     (RCN287.sharpResidualAgreementFlag (support a b s) d)
     (globalTailCut φ F d):=by
 exact RCN287.surfaceMap_agreement_in_sharp_flag
   (P:=support a b s) (by change s+2 < b+s+3;omega) φ
   (support_data a b s F hR hYR hAll) d (tailSelector d) 0 0 0
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
theorem restrictQ_surjective:Function.Surjective (restrictQ (K:=K)):=
 LinearMap.funLeft_surjective_of_injective K K _ quadraticIndex_injective
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
theorem quadratic_max_signed_eq_truncated (a b w:ℤ) (ha:0 ≤ a) (hb:b ≤ a):
   max (2*a) (b+w)=max (2*a) (b+max 0 w):=by omega
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
theorem familyEmbeddingPoint_injective (hP:Function.Injective P):
   Function.Injective (familyEmbeddingPoint (L:=L) P):=by
 rintro ⟨i,f⟩ ⟨j,g⟩ hfg
 have hij:P i=P j:=by
   rw [←embeddingPoint_kernel (P i) f,
     ←embeddingPoint_kernel (P j) g]
   exact congrArg (fun v:Fin 3 → L =>
     RingHom.ker (MvPolynomial.aeval v).toRingHom) hfg
 obtain rfl:=hP hij
 have hf:f=g:=embeddingPoint_injective (P i) hfg
 cases hf
 rfl
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
def genericFiberPoints:Finset (Fin 3 → L):=by
 classical
 exact Finset.univ.image (commonBaseEmbeddingPoint (B:=B) (L:=L) P)
theorem genericFiberPoints_card (hP:Function.Injective P):
   (genericFiberPoints (B:=B) (L:=L) P).card=
     ∑ i,Module.finrank B (CoordinateField K (P i)):=by
 classical
 rw [genericFiberPoints,
   Finset.card_image_of_injective _ (commonBaseEmbeddingPoint_injective P hP)]
 simp only [Finset.card_univ,Fintype.card_sigma,AlgHom.card]
end CommonBase
end
end ProximityPrize.SubmissionLower.RCN134
end PackedLegacy_EJ

/-! Packed from ProximityPrize.SubmissionLower.D3. -/
section PackedLegacy_D3
namespace ProximityPrize.SubmissionLower.RCN208
open scoped Classical
open RCN002 RCN072 RCN264 RCN022 RCN207 RCN134
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
variable {K L:Type} [Field K] [Field L]
def coordinateFieldMap (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (ev:MvPolynomial (Fin 3) K →+*L) (hker:RingHom.ker ev=P):
   CoordinateField K P →+*L:=
 let hz:∀ A,A∈P → ev A=0:=fun A hA↦by
   exact RingHom.mem_ker.mp (hker.symm ▸ hA)
 IsFractionRing.lift (K:=CoordinateField K P)
   (RingHom.lift_injective_of_ker_le_ideal P hz hker.le)
theorem coordinateFieldMap_eval (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (ev:MvPolynomial (Fin 3) K →+*L) (hker:RingHom.ker ev=P)
   (A:MvPolynomial (Fin 3) K):
   coordinateFieldMap P ev hker (coordinateEvaluation K P A)=ev A:=by
 unfold coordinateFieldMap
 change IsFractionRing.lift _
   (algebraMap (CoordinateRing K P) (CoordinateField K P) (Ideal.Quotient.mk P A))=ev A
 rw [IsFractionRing.lift_algebraMap,Ideal.Quotient.lift_mk]
def movingValue (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (H G Q U:MvPolynomial (Fin 3) K):CoordinateField K P:=
 coordinateEvaluation K P Q+
   coordinateEvaluation K P U*coordinateEvaluation K P G/
     coordinateEvaluation K P H
def scalarPolynomialMap (K E:Type) [Field K] [Field E] [Algebra K E]:
   MvPolynomial (Fin 3) K →+*MvPolynomial (Fin 3) E:=
 MvPolynomial.map (algebraMap K E)
theorem comap_le_of_embedding_point {E:Type} [Field E] [Algebra K E]
   (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (f:CoordinateField K P →ₐ[K] E) (D:Ideal (MvPolynomial (Fin 3) E))
   (hD:D ≤ RingHom.ker
     (MvPolynomial.aeval (embeddingPoint P f):MvPolynomial (Fin 3) E →ₐ[E] E).toRingHom):
   D.comap (scalarPolynomialMap K E) ≤ P:=by
 intro A hA
 rw [←embeddingPoint_kernel P f]
 apply RingHom.mem_ker.mpr
 have hv:=RingHom.mem_ker.mp (hD hA)
 simpa only [MvPolynomial.aeval_eq_eval₂Hom,scalarPolynomialMap,
   MvPolynomial.eval₂Hom_map_hom,Algebra.algebraMap_self,RingHom.id_comp,
   AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hv
private theorem rational_base_diagram {E M:Type} [Field E] [Field M]
   [Algebra K E] [Algebra K L] [Algebra E M]
   (j:L) (hj:Transcendental K j) (t:E) (ht:Transcendental K t)
   (phi:L →+*M)
   (hc:∀ c:K,phi (algebraMap K L c)=algebraMap E M (algebraMap K E c))
   (hjmap:phi j=algebraMap E M t):
   (algebraMap E M).comp (elementEmbedding K E t ht).toRingHom=
     phi.comp (elementEmbedding K L j hj).toRingHom:=by
 apply IsFractionRing.ringHom_ext (A:=Polynomial K)
 intro p
 have hpoly:
     ((algebraMap E M).comp (elementEmbedding K E t ht).toRingHom).comp
         (algebraMap (Polynomial K) (RatFunc K))=
       (phi.comp (elementEmbedding K L j hj).toRingHom).comp
         (algebraMap (Polynomial K) (RatFunc K)):=by
   apply Polynomial.ringHom_ext
   · intro c
     change algebraMap E M (elementEmbedding K E t ht (algebraMap K (RatFunc K) c))=
       phi (elementEmbedding K L j hj (algebraMap K (RatFunc K) c))
     rw [AlgHom.commutes,AlgHom.commutes,hc]
   · simpa only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
       AlgHom.coe_toRingHom,elementEmbedding_variable] using hjmap.symm
 exact RingHom.congr_fun hpoly p
theorem eliminatedCut_not_mem_of_contraction
   {E:Type} [Field E] [IsAlgClosed E] [Algebra K E]
   (F H G Q U:MvPolynomial (Fin 3) K)
   (k:ℕ) (B:Fin (k+1) → MvPolynomial (Fin 3) K)
   (C:RegularComponent K F (filteredCut k B H G) H)
   (hj:Transcendental K (movingValue C.1 H G Q U))
   (hfinite:
     letI:Algebra (RatFunc K) (CoordinateField K C.1):=
       (elementEmbedding K (CoordinateField K C.1) (movingValue C.1 H G Q U) hj).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) (CoordinateField K C.1))
   (t:E) (ht:Transcendental K t)
   (D:RegularComponent E (scalarPolynomialMap K E F)
     (movingEquation (scalarPolynomialMap K E H) (scalarPolynomialMap K E G)
       (scalarPolynomialMap K E Q) (scalarPolynomialMap K E U) t)
     (scalarPolynomialMap K E H*scalarPolynomialMap K E U))
   (hbelow:D.1.comap (scalarPolynomialMap K E) ≤ C.1):
   eliminatedCut k (fun j↦scalarPolynomialMap K E (B j))
     (scalarPolynomialMap K E Q) (scalarPolynomialMap K E U) t∉D.1:=by
 intro hT
 let mu:=scalarPolynomialMap K E
 let N:=movingEquation (mu H) (mu G) (mu Q) (mu U) t
 let evD:=coordinateEvaluation E D.1
 let ev:=evD.toRingHom.comp mu
 have hN:N∈D.1:=regularComponent_T_mem E _ _ _ D
 have hprod:mu H*mu U∉D.1:=regularComponent_H_not_mem E _ _ _ D
 have hH:mu H∉D.1:=fun h↦hprod (D.1.mul_mem_right (mu U) h)
 have hU:mu U∉D.1:=fun h↦hprod (D.1.mul_mem_left (mu H) h)
 have hTor:mu (filteredCut k B H G)∈D.1:=by
   rw [map_filteredCut]
   exact original_mem_of_eliminated_mem D.1 k (fun j↦mu (B j))
     (mu H) (mu G) (mu Q) (mu U) t hN hT hU
 have hcut:cutIdeal K F (filteredCut k B H G) ≤ D.1.comap mu:=by
   apply Ideal.span_le.mpr
   intro A hA
   rcases (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hA) with rfl | rfl
   · exact regularComponent_G_mem E _ _ _ D
   · exact hTor
 have hmin:=(mem_componentFamily K F (filteredCut k B H G) C.1).mp
   (regularComponent_mem K _ _ _ C)
 have hcontract:D.1.comap mu=C.1:=
   le_antisymm hbelow (hmin.2 ⟨inferInstance,hcut⟩ hbelow)
 have hker:RingHom.ker ev=C.1:=by
   rw [show RingHom.ker ev=(RingHom.ker evD.toRingHom).comap mu from rfl,
     coordinateEvaluation_ker E D.1]
   exact hcontract
 let phi:=coordinateFieldMap C.1 ev hker
 have hphi (A:MvPolynomial (Fin 3) K):
     phi (coordinateEvaluation K C.1 A)=ev A:=coordinateFieldMap_eval _ _ _ A
 have hscalar (c:K):
     phi (algebraMap K (CoordinateField K C.1) c)=
       algebraMap E (CoordinateField E D.1) (algebraMap K E c):=by
   have h:=hphi (MvPolynomial.C c)
   simpa [ev,mu,scalarPolynomialMap] using h
 have hHne:ev H≠0:=by
   intro hz
   have:mu H∈RingHom.ker evD.toRingHom:=hz
   rw [coordinateEvaluation_ker E D.1] at this
   exact hH this
 have hNzero:evD N=0:=by
   apply RingHom.mem_ker.mp
   change N∈RingHom.ker (coordinateEvaluation E D.1).toRingHom
   rw [coordinateEvaluation_ker E D.1]
   exact hN
 have hconst:evD (MvPolynomial.C t)=algebraMap E (CoordinateField E D.1) t:=
   evD.commutes t
 have hrel:ev H*(algebraMap E (CoordinateField E D.1) t-ev Q)=ev U*ev G:=by
   apply sub_eq_zero.mp
   simpa only [N,movingEquation,map_sub,map_mul,hconst,
     ev,RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hNzero
 have hjmap:phi (movingValue C.1 H G Q U)=
     algebraMap E (CoordinateField E D.1) t:=by
   unfold movingValue
   rw [map_add,map_div₀,map_mul,hphi Q,hphi U,hphi G,hphi H]
   have hd:ev U*ev G/ev H=algebraMap E (CoordinateField E D.1) t-ev Q:=by
     apply (div_eq_iff hHne).mpr
     simpa only [mul_comm] using hrel.symm
   rw [hd]
   ring
 letI:Algebra (RatFunc K) (CoordinateField K C.1):=
   (elementEmbedding K (CoordinateField K C.1) (movingValue C.1 H G Q U) hj).toRingHom.toAlgebra
 letI:FiniteDimensional (RatFunc K) (CoordinateField K C.1):=hfinite
 have hdiag:
     (algebraMap E (CoordinateField E D.1)).comp (elementEmbedding K E t ht).toRingHom=
       phi.comp (algebraMap (RatFunc K) (CoordinateField K C.1)):=
   rational_base_diagram (movingValue C.1 H G Q U) hj t ht phi hscalar hjmap
 have halg:∀ i,IsAlgebraic E (coordinate E D.1 i):=by
   intro i
   have hint:=IsIntegral.map_of_comp_eq (elementEmbedding K E t ht).toRingHom
     phi hdiag (IsIntegral.of_finite (RatFunc K) (coordinate K C.1 i))
   have hcoord:phi (coordinate K C.1 i)=coordinate E D.1 i:=by
     simpa only [coordinate,ev,evD,RingHom.comp_apply,mu,scalarPolynomialMap,
       MvPolynomial.map_X,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hphi (MvPolynomial.X i)
   rw [hcoord] at hint
   exact hint.isAlgebraic
 obtain ⟨point,hpoint⟩:=eq_point_kernel_of_coordinates_algebraic E D.1 halg
 exact regularComponent_ne_point E _ _ _ D point hpoint
end
end ProximityPrize.SubmissionLower.RCN208
end PackedLegacy_D3

/-! Packed from ProximityPrize.SubmissionLower.A9. -/
section PackedLegacy_A9
namespace ProximityPrize.SubmissionLower.RCN064
open scoped Classical BigOperators WithZero
open RCN212 RCN184 RCN133 RCN295 RCN095 RCN114 RCN187 RCN344 RCN002 RCN005 RCN006 RCN341 RCN044 RCN037 RCN207 RCN208 RCN264 RCN042 RCN035 RCN022
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
private theorem exact_of_avoids {K L σ:Type*} [Field K] [Field L]
   [Algebra K L] [Fintype σ] [DecidableEq σ]
   (v:RCN345.NormalizedValuation K L) (x:σ → L)
   (E:Finset (σ →₀ ℕ)) (c:E → K)
   (hc:c∉cancellationSubmodule v.val (constant_value_le_one K L v) x E):
   v.val (coefficientEvaluation x E c)=WithZero.exp (exponentSetPoleWeight v.val x E):=by
 apply le_antisymm
 · exact valuation_eval_le_exp_exponentSet v.val (algebraMap K L)
     (constant_value_le_one K L v) x E _ (support_polynomialOfSupport_subset _ _)
 · exact le_of_not_gt hc
theorem exists_common_coefficients {K I:Type*} [Field K] [Infinite K] [Finite I]
   (L:I → Type*) [∀ i,Field (L i)] [∀ i,Algebra K (L i)]
   (x:∀ i,Fin 3 → L i) (w:∀ i,L i) (index:I → Fin 3)
   (hd:∀ i,KaehlerDifferential.D K (L i) (x i (index i))≠0)
   (V:∀ i,Finset (RCN345.NormalizedValuation K (L i))):
   ∃ c:movingSupport → K,∀ i,
     coefficientEvaluation (x i) linearSupport (restrictU c)≠0∧
     KaehlerDifferential.D K (L i)
       (coefficientEvaluation (movingCoordinates (x i) (w i)) movingSupport c)≠0∧
     ∀ v∈V i,
       v.val (coefficientEvaluation (movingCoordinates (x i) (w i)) movingSupport c)=
         WithZero.exp (max (2*max (poleOrder v.val (x i 1))
           (max (poleOrder v.val (x i 0)) (poleOrder v.val (x i 2))))
           (max (poleOrder v.val (x i 0)) (poleOrder v.val (x i 2))+poleOrder v.val (w i)))∧
       v.val (coefficientEvaluation (x i) linearSupport (restrictU c))=
         WithZero.exp (max (poleOrder v.val (x i 0)) (poleOrder v.val (x i 2))):=by
 classical
 let evJ i:=coefficientEvaluation (K:=K) (movingCoordinates (x i) (w i)) movingSupport
 let evU i:=(coefficientEvaluation (K:=K) (x i) linearSupport).comp restrictU
 let Extra:=I × Bool
 let Pole:=Sigma fun i:I↦{v//v∈V i} × Bool
 let bad:Extra ⊕ Pole → Submodule K (movingSupport → K)
   | Sum.inl (i,false) => LinearMap.ker (evU i)
   | Sum.inl (i,true) => LinearMap.ker ((KaehlerDifferential.D K (L i)).toLinearMap.comp (evJ i))
   | Sum.inr ⟨i,v,false⟩ => (cancellationSubmodule v.1.val
       (constant_value_le_one K (L i) v.1) (x i) linearSupport).comap restrictU
   | Sum.inr ⟨i,v,true⟩ => cancellationSubmodule v.1.val
       (constant_value_le_one K (L i) v.1) (movingCoordinates (x i) (w i)) movingSupport
 have hbad:∀ j,bad j≠⊤:=by
   rintro (⟨i,b⟩ | ⟨i,v,b⟩)
   · cases b
     · obtain ⟨c,hc⟩:=restrictU_surjective (K:=K)
         (deltaCoefficient linearSupport ⟨0,zero_mem_flagSupport _⟩)
       have hone:evU i c=1:=by
         change coefficientEvaluation (x i) linearSupport (restrictU c)=1
         rw [hc]
         change MvPolynomial.eval₂Hom _ _ (polynomialOfSupport _ _)=_
         rw [polynomialOfSupport_deltaCoefficient]
         simp
       intro ht
       have hz:evU i c=0:=LinearMap.mem_ker.mp (by change c∈bad (Sum.inl (i,false));rw [ht];trivial)
       exact one_ne_zero (hone.symm.trans hz)
     · obtain ⟨c,hc⟩:=exists_coordinate_evaluation (K:=K) (x i) (w i) (index i)
       intro ht
       have hz:KaehlerDifferential.D K (L i) (evJ i c)=0:=
         LinearMap.mem_ker.mp (by change c∈bad (Sum.inl (i,true));rw [ht];trivial)
       exact hd i (hc ▸ hz)
   · cases b
     · obtain ⟨d,hd⟩:=exists_exact_support_evaluation_of_downwardClosed (K:=K)
         v.1.val (x i) linearSupport (flagSupport_downwardClosed _) (zero_mem_flagSupport _)
       obtain ⟨c,hc⟩:=restrictU_surjective (K:=K) d
       intro ht
       have hm:c∈bad (Sum.inr ⟨i,v,false⟩):=by rw [ht];trivial
       change v.1.val (coefficientEvaluation (x i) linearSupport (restrictU c)) < _ at hm
       rw [hc,hd] at hm
       exact lt_irrefl _ hm
     · obtain ⟨c,hc⟩:=exists_exact_support_evaluation_of_downwardClosed (K:=K)
         v.1.val (movingCoordinates (x i) (w i)) movingSupport
         movingSupport_downwardClosed zero_mem_movingSupport
       exact cancellationSubmodule_ne_top_of_exact _ _ _ _ c hc
 obtain ⟨c,hc⟩:=exists_avoiding_finite_proper_submodules bad hbad
 refine ⟨c,fun i↦⟨?_,?_,?_⟩⟩
 · exact hc (Sum.inl (i,false))
 · exact hc (Sum.inl (i,true))
 · intro v hv
   have hj:=exact_of_avoids v (movingCoordinates (x i) (w i)) movingSupport c
     (hc (Sum.inr ⟨i,⟨v,hv⟩,true⟩))
   have hu:=exact_of_avoids v (x i) linearSupport (restrictU c)
     (hc (Sum.inr ⟨i,⟨v,hv⟩,false⟩))
   rw [exponentSetPoleWeight_moving] at hj
   rw [exponentSetPoleWeight_unitYZ] at hu
   exact ⟨hj,hu⟩
variable {K:Type} [Field K] [IsAlgClosed K]
def movingRelevantPlaces {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (D:SeparableLiteralCoordinate P) (w:CoordinateField K P):
   Finset (Place K (CoordinateField K P)):=by
 letI:=polynomialBaseAlgebra K P D.index
 letI:=rationalBaseAlgebra K P D.index D.transcendental
 letI:=polynomialBaseScalarTower K P D.index
 letI:=polynomialRationalScalarTower K P D.index D.transcendental
 letI:=rationalBaseScalarTower K P D.index D.transcendental
 letI:FiniteDimensional (RatFunc K) (CoordinateField K P):=D.finite
 letI:Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=D.separable
 exact literalRelevantPlaces D ∪ if hw:w≠0 then
   RCN026.placesFor K (CoordinateField K P) w hw else ∅
theorem outside_movingRelevantPlaces {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (D:SeparableLiteralCoordinate P) (w:CoordinateField K P)
   (v:Place K (CoordinateField K P)) (hv:v∉movingRelevantPlaces D w):
   (∀ i,poleOrder v.val (coordinate K P i)=0)∧poleOrder v.val w=0:=by
 letI:=polynomialBaseAlgebra K P D.index
 letI:=rationalBaseAlgebra K P D.index D.transcendental
 letI:=polynomialBaseScalarTower K P D.index
 letI:=polynomialRationalScalarTower K P D.index D.transcendental
 letI:=rationalBaseScalarTower K P D.index D.transcendental
 letI:FiniteDimensional (RatFunc K) (CoordinateField K P):=D.finite
 letI:Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=D.separable
 constructor
 · exact coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant D v
     (fun h↦hv (Finset.mem_union_left _ h))
 · by_cases hw:w=0
   · simp [hw,poleOrder]
   have horder:RCN026.order K (CoordinateField K P) v w=0:=by
     by_contra hn
     apply hv
     apply Finset.mem_union_right
     simp only [dif_pos hw]
     exact RCN026.placesFor_covers K (CoordinateField K P) w hw v hn
   simp only [RCN026.order] at horder
   simp [poleOrder,show (v.val w).log=0 by omega]
def movingRatio (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (H G:MvPolynomial (Fin 3) K):CoordinateField K P:=
 coordinateEvaluation K P G/coordinateEvaluation K P H
def movingPoleTarget (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (H G:MvPolynomial (Fin 3) K) (v:Place K (CoordinateField K P)):ℤ:=
 max (2*max (poleOrder v.val (coordinate K P 1))
   (max (poleOrder v.val (coordinate K P 0)) (poleOrder v.val (coordinate K P 2))))
   (max (poleOrder v.val (coordinate K P 0)) (poleOrder v.val (coordinate K P 2))+
     poleOrder v.val (movingRatio P H G))
private theorem field_eval (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (A:MvPolynomial (Fin 3) K):
   MvPolynomial.eval₂Hom (algebraMap K (CoordinateField K P)) (coordinate K P) A=
     coordinateEvaluation K P A:=by
 rw [coordinateEvaluation_eq_aeval]
 exact (MvPolynomial.aeval_eq_eval₂Hom _ _).symm
theorem exists_common_original_projection (F A H G:MvPolynomial (Fin 3) K)
   (base:∀ C:RegularComponent K F A H,SeparableLiteralCoordinate C.1):
   ∃ Q U:MvPolynomial (Fin 3) K,
     PolynomialInFlag (2 • unitAllFlag) Q∧PolynomialInFlag unitYZFlag U∧
     ∀ C:RegularComponent K F A H,
       U∉C.1∧KaehlerDifferential.D K (CoordinateField K C.1)
         (movingValue C.1 H G Q U)≠0∧
       (∀ v:Place K (CoordinateField K C.1),
         poleOrder v.val (movingValue C.1 H G Q U)=movingPoleTarget C.1 H G v)∧
       (∀ v∈movingRelevantPlaces (base C) (movingRatio C.1 H G),
         v.val (coordinateEvaluation K C.1 U)=
           WithZero.exp (max (poleOrder v.val (coordinate K C.1 0))
             (poleOrder v.val (coordinate K C.1 2)))):=by
 classical
 obtain ⟨c,hc⟩:=exists_common_coefficients (K:=K)
   (fun C:RegularComponent K F A H↦CoordinateField K C.1)
   (fun C↦coordinate K C.1) (fun C↦movingRatio C.1 H G)
   (fun C↦(base C).index) (fun C↦base_differential_ne_zero (base C))
   (fun C↦movingRelevantPlaces (base C) (movingRatio C.1 H G))
 let Q:=quadraticPolynomial c
 let U:=linearPolynomial c
 have hJ (C:RegularComponent K F A H):
     coefficientEvaluation (movingCoordinates (coordinate K C.1) (movingRatio C.1 H G))
       movingSupport c=movingValue C.1 H G Q U:=by
   rw [coefficientEvaluation_eq,field_eval,field_eval]
   simp only [movingValue,movingRatio,Q,U,mul_div_assoc]
 have hU (C:RegularComponent K F A H):
     coefficientEvaluation (coordinate K C.1) linearSupport (restrictU c)=
       coordinateEvaluation K C.1 U:=field_eval C.1 U
 refine ⟨Q,U,quadraticPolynomial_inFlag c,linearPolynomial_inFlag c,fun C↦?_⟩
 have h:=hc C
 rw [hU C,hJ C] at h
 refine ⟨?_,h.2.1,?_,fun v hv↦(h.2.2 v hv).2⟩
 · intro hmem
   apply h.1
   apply RingHom.mem_ker.mp
   change U∈RingHom.ker (coordinateEvaluation K C.1).toRingHom
   rwa [coordinateEvaluation_ker]
 · intro v
   by_cases hv:v∈movingRelevantPlaces (base C) (movingRatio C.1 H G)
   · exact poleOrder_eq_of_valuation_eq_exp v.val _ _
       (by dsimp [movingPoleTarget,poleOrder];positivity) (h.2.2 v hv).1
   · obtain ⟨hcoord,hw⟩:=outside_movingRelevantPlaces (base C) (movingRatio C.1 H G) v hv
     have hz:exponentSetPoleWeight v.val
         (movingCoordinates (coordinate K C.1) (movingRatio C.1 H G)) movingSupport=0:=by
       rw [exponentSetPoleWeight_moving]
       simp [hcoord,hw]
     have hp:=(poleOrder_eval_le_support v.val (algebraMap K (CoordinateField K C.1))
       (constant_value_le_one K (CoordinateField K C.1) v)
       (movingCoordinates (coordinate K C.1) (movingRatio C.1 H G))
       (polynomialOfSupport movingSupport c)).trans
       (supportPoleWeight_le_exponentSetPoleWeight _ _ _ movingSupport
         (support_polynomialOfSupport_subset _ _))
     change poleOrder v.val (coefficientEvaluation _ _ c) ≤ _ at hp
     rw [hJ C,hz] at hp
     have hp0:=le_antisymm hp (le_max_left _ _)
     simpa [movingPoleTarget,hcoord,hw] using hp0
theorem moving_projection_gate {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (base:SeparableLiteralCoordinate P) (H G Q U:MvPolynomial (Fin 3) K)
   (hd:KaehlerDifferential.D K (CoordinateField K P) (movingValue P H G Q U)≠0):
   ∃ ht:Transcendental K (movingValue P H G Q U),
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       (elementEmbedding K (CoordinateField K P) (movingValue P H G Q U) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
     IsScalarTower K (RatFunc K) (CoordinateField K P)∧
     algebraMap (RatFunc K) (CoordinateField K P)
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=movingValue P H G Q U:=by
 obtain ⟨ht,hf,hs⟩:=element_transcendental_finite_separable_of_differential_ne_zero
   K (CoordinateField K P) (literalToSeparableCoordinate base) (movingValue P H G Q U) hd
 letI:Algebra (RatFunc K) (CoordinateField K P):=
   (elementEmbedding K (CoordinateField K P) (movingValue P H G Q U) ht).toRingHom.toAlgebra
 refine ⟨ht,hf,hs,?_,elementEmbedding_variable K (CoordinateField K P) _ ht⟩
 exact IsScalarTower.of_algebraMap_eq fun c↦
   ((elementEmbedding K (CoordinateField K P) _ ht).commutes c).symm
theorem moving_pole_mem_relevant {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (base:SeparableLiteralCoordinate P) (w:CoordinateField K P)
   (v:Place K (CoordinateField K P)) (hw:poleOrder v.val w≠0):
   v∈movingRelevantPlaces base w:=by
 by_contra hv
 exact hw (outside_movingRelevantPlaces base w v hv).2
theorem value_one_at_finite_moving_pole {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (base:SeparableLiteralCoordinate P) (w u:CoordinateField K P)
   (hu:∀ v∈movingRelevantPlaces base w,
     v.val u=WithZero.exp (max (poleOrder v.val (coordinate K P 0))
       (poleOrder v.val (coordinate K P 2))))
   (v:Place K (CoordinateField K P)) (hw:poleOrder v.val w≠0)
   (h0:poleOrder v.val (coordinate K P 0)=0)
   (h2:poleOrder v.val (coordinate K P 2)=0):v.val u=1:=by
 rw [hu v (moving_pole_mem_relevant base w v hw),h0,h2]
 simp
end
end ProximityPrize.SubmissionLower.RCN064
end PackedLegacy_A9

/-! Packed from ProximityPrize.SubmissionLower.M8. -/
section PackedLegacy_M8
namespace ProximityPrize.SubmissionLower.RCN204
open scoped Classical BigOperators WithZero
open RCN095 RCN114 RCN207 RCN212 RCN295 RCN187 RCN002 RCN344 RCN064
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
private theorem flag_eq {p q:FlagDegree} (hx:p.zOnly=q.zOnly)
   (hy:p.yz=q.yz) (hz:p.all=q.all):p=q:=by
 cases p;cases q;simp_all
theorem coefficient_flag_eq (a b s k:ℕ) (C:FlagDegree)
   (c:Fin (k+1) → FlagDegree)
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree))
   (j:Fin (k+1)):
   c j=C+k • (⟨a,b,s⟩:FlagDegree)+(k-j.val) • (2 • unitAllFlag)+j.val • unitYZFlag:=by
 have hx:=congrArg FlagDegree.zOnly (hc j)
 have hy:=congrArg FlagDegree.yz (hc j)
 have hz:=congrArg FlagDegree.all (hc j)
 have hj:k-j.val+j.val=k:=Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)
 apply flag_eq
 all_goals simp only [add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all,
   unitAllFlag,unitYZFlag] at*
 all_goals nlinarith
variable {K L:Type*} [Field K] [Field L]
theorem filteredCut_div_pow (k:ℕ) (B:Fin (k+1) → L) (H G:L) (hH:H≠0):
   filteredCut k B H G/H^k=∑ j,B j*(G/H)^j.val:=by
 apply (div_eq_iff (pow_ne_zero k hH)).mpr
 have hrel:H*(G/H)=(1:L)*G:=by field_simp
 have h:=binary_clearing k B H G 1 (G/H) hrel
 simpa [filteredCut,mul_comm,mul_left_comm,mul_assoc] using h.symm
def flagPole (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (p:FlagDegree):ℤ:=
 (p.zOnly:ℤ)*poleOrder v (x 2)+
 (p.yz:ℤ)*max (poleOrder v (x 0)) (poleOrder v (x 2))+
 (p.all:ℤ)*max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2)))
theorem flagPole_nonneg (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (p:FlagDegree):0 ≤ flagPole v x p:=by
 unfold flagPole poleOrder
 positivity
@[simp] theorem flagPole_add (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (p q:FlagDegree):
   flagPole v x (p+q)=flagPole v x p+flagPole v x q:=by
 simp only [flagPole,add_zOnly,add_yz,add_all,Nat.cast_add]
 ring
@[simp] theorem flagPole_nsmul (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (k:ℕ) (p:FlagDegree):
   flagPole v x (k • p)=(k:ℤ)*flagPole v x p:=by
 simp only [flagPole,nsmul_zOnly,nsmul_yz,nsmul_all,Nat.cast_mul]
 ring
@[simp] theorem flagPole_unitAll (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L):flagPole v x unitAllFlag=
     max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2))):=by
 simp [flagPole,unitAllFlag]
@[simp] theorem flagPole_unitYZ (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L):flagPole v x unitYZFlag=
     max (poleOrder v (x 0)) (poleOrder v (x 2)):=by
 simp [flagPole,unitYZFlag]
theorem valuation_eval_le_flag (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ a,v (coeff a) ≤ 1) (x:Fin 3 → L)
   (p:FlagDegree) (B:MvPolynomial (Fin 3) K) (hB:PolynomialInFlag p B):
   v (MvPolynomial.eval₂Hom coeff x B) ≤ WithZero.exp (flagPole v x p):=
 (valuation_eval_le_exp_exponentSet v coeff hcoeff x (flagSupport p) B
   ((support_subset_flagSupport_iff _ _).mpr hB)).trans
   (WithZero.exp_le_exp.mpr (exponentSetPoleWeight_flagSupport_le v x p))
private theorem mixed_weight_le (r j k:ℕ) (h:r+j=k) (A B:ℤ):
   (r:ℤ)*A+(j:ℤ)*B ≤ (k:ℤ)*max A B:=by
 calc
   _ ≤ (r:ℤ)*max A B+(j:ℤ)*max A B:=add_le_add
     (mul_le_mul_of_nonneg_left (le_max_left _ _) (Int.natCast_nonneg _))
     (mul_le_mul_of_nonneg_left (le_max_right _ _) (Int.natCast_nonneg _))
   _=((r+j:ℕ):ℤ)*max A B:=by push_cast;ring
   _=_:=by rw [h]
theorem valuation_polynomialInW_le (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ a,v (coeff a) ≤ 1) (x:Fin 3 → L)
   (w:L) (k:ℕ) (C N:FlagDegree) (B:Fin (k+1) → MvPolynomial (Fin 3) K)
   (hB:∀ j,PolynomialInFlag
     (C+k • N+(k-j.val) • (2 • unitAllFlag)+j.val • unitYZFlag) (B j)):
   v (∑ j,MvPolynomial.eval₂Hom coeff x (B j)*w^j.val) ≤
     WithZero.exp (flagPole v x C+(k:ℤ)*(flagPole v x N+
       max (2*flagPole v x unitAllFlag) (flagPole v x unitYZFlag+poleOrder v w))):=by
 apply v.map_sum_le
 intro j _
 let p:=C+k • N+(k-j.val) • (2 • unitAllFlag)+j.val • unitYZFlag
 have hBj:=valuation_eval_le_flag v coeff hcoeff x p (B j) (hB j)
 have hw:v w ≤ WithZero.exp (poleOrder v w):=
   WithZero.le_exp_of_log_le (le_max_right _ _)
 have hpow:v (w^j.val) ≤ WithZero.exp ((j.val:ℤ)*poleOrder v w):=by
   rw [map_pow]
   simpa only [←WithZero.exp_nsmul,nsmul_eq_mul] using
     pow_le_pow_left₀ (show (0:WithZero (Multiplicative ℤ)) ≤ v w from zero_le) hw j.val
 calc
   v (MvPolynomial.eval₂Hom coeff x (B j)*w^j.val) ≤
       WithZero.exp (flagPole v x p)*WithZero.exp ((j.val:ℤ)*poleOrder v w):=by
     rw [map_mul]
     exact mul_le_mul' hBj hpow
   _=WithZero.exp (flagPole v x p+(j.val:ℤ)*poleOrder v w):=by rw [WithZero.exp_add]
   _ ≤ _:=by
     apply WithZero.exp_le_exp.mpr
     have hm:=mixed_weight_le (k-j.val) j.val k
       (Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt))
       (2*flagPole v x unitAllFlag) (flagPole v x unitYZFlag+poleOrder v w)
     simp only [p,flagPole_add,flagPole_nsmul,Nat.cast_ofNat]
     nlinarith
private theorem poleOrder_le_of_value_le_exp (v:Valuation L (WithZero (Multiplicative ℤ)))
   (z:L) (q:ℤ) (hq:0 ≤ q) (hz:v z ≤ WithZero.exp q):poleOrder v z ≤ q:=by
 apply max_le hq
 by_cases hv:v z=0
 · simpa [hv] using hq
 · simpa only [WithZero.log_exp] using (WithZero.log_le_log hv WithZero.exp_ne_zero).mpr hz
theorem poleOrder_filteredCut_div_le (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ a,v (coeff a) ≤ 1) (x:Fin 3 → L)
   (a b s k:ℕ) (C:FlagDegree) (B:Fin (k+1) → MvPolynomial (Fin 3) K)
   (H G:MvPolynomial (Fin 3) K) (c:Fin (k+1) → FlagDegree)
   (hH:MvPolynomial.eval₂Hom coeff x H≠0)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree)):
   poleOrder v (MvPolynomial.eval₂Hom coeff x (filteredCut k B H G)/
     (MvPolynomial.eval₂Hom coeff x H)^k) ≤
   flagPole v x C+(k:ℤ)*(flagPole v x (⟨a,b,s⟩:FlagDegree)+
     max (2*max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2))))
       (max (poleOrder v (x 0)) (poleOrder v (x 2))+
         poleOrder v (MvPolynomial.eval₂Hom coeff x G/MvPolynomial.eval₂Hom coeff x H))):=by
 rw [map_filteredCut,filteredCut_div_pow k _ _ _ hH]
 apply poleOrder_le_of_value_le_exp
 · have hC:=flagPole_nonneg v x C
   have hN:=flagPole_nonneg v x (⟨a,b,s⟩:FlagDegree)
   dsimp [poleOrder]
   positivity
 · simpa only [flagPole_unitAll,flagPole_unitYZ] using
     valuation_polynomialInW_le v coeff hcoeff x
       (MvPolynomial.eval₂Hom coeff x G/MvPolynomial.eval₂Hom coeff x H)
       k C (⟨a,b,s⟩:FlagDegree) B (fun j↦by
         rw [←coefficient_flag_eq a b s k C c hc j]
         exact hB j)
theorem coordinate_filteredCut_pole_le {Ω:Type} [Field Ω]
   (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
   (v:Place Ω (CoordinateField Ω P)) (a b s k:ℕ) (C:FlagDegree)
   (B:Fin (k+1) → MvPolynomial (Fin 3) Ω) (H G:MvPolynomial (Fin 3) Ω)
   (c:Fin (k+1) → FlagDegree) (hH:coordinateEvaluation Ω P H≠0)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree)):
   poleOrder v.val (coordinateEvaluation Ω P (filteredCut k B H G)/
     (coordinateEvaluation Ω P H)^k) ≤
     flagPole v.val (coordinate Ω P) C+(k:ℤ)*
       (flagPole v.val (coordinate Ω P) (⟨a,b,s⟩:FlagDegree)+movingPoleTarget P H G v):=by
 have h:=poleOrder_filteredCut_div_le v.val (algebraMap Ω (CoordinateField Ω P))
   (constant_value_le_one Ω (CoordinateField Ω P) v) (coordinate Ω P)
   a b s k C B H G c (by
     simpa only [coordinateEvaluation_eq_aeval,MvPolynomial.aeval_eq_eval₂Hom] using hH) hB hc
 simpa only [coordinateEvaluation_eq_aeval,MvPolynomial.aeval_eq_eval₂Hom,
   movingPoleTarget,movingRatio] using h
end
end ProximityPrize.SubmissionLower.RCN204
end PackedLegacy_M8

/-! Packed from ProximityPrize.SubmissionLower.O3. -/
section PackedLegacy_O3
namespace ProximityPrize.SubmissionLower.RCN271
open scoped Classical
open RCN272 RCN094 RCN162 RCN165
noncomputable section
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Ring3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
private theorem eval_eq_of_sub_mem (P:Ideal (Ring3 K))
   {A B:Ring3 K} (h:A-B∈P) (v:Fin 3 → K)
   (hv:P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom):
   MvPolynomial.aeval v A=MvPolynomial.aeval v B:=by
 have hz:=hv h
 change MvPolynomial.aeval v (A-B)=0 at hz
 rw [map_sub] at hz
 exact sub_eq_zero.mp hz
def FiniteRegularZeroSetBound (P:Ideal (Ring3 K)) (H A:Ring3 K)
   (cost:ℕ):Prop:=
 ∀ points:Finset (Fin 3 → K),
   (∀ v∈points,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom) →
   (∀ v∈points,MvPolynomial.aeval v H≠0) →
   (∀ v∈points,MvPolynomial.aeval v A=0) → points.card ≤ cost
theorem FiniteRegularZeroSetBound.of_all_points
   {P:Ideal (Ring3 K)} {H A:Ring3 K} {cost:ℕ}
   (h:FiniteZeroSetBound P A cost):FiniteRegularZeroSetBound P H A cost:=by
 intro points hP _ hA
 exact h points hP hA
theorem FiniteRegularZeroSetBound.mono
   {P:Ideal (Ring3 K)} {H A:Ring3 K} {cost cost':ℕ}
   (h:FiniteRegularZeroSetBound P H A cost) (hle:cost ≤ cost'):
   FiniteRegularZeroSetBound P H A cost':=by
 intro points hP hH hA
 exact (h points hP hH hA).trans hle
theorem FiniteRegularZeroSetBound.of_sub_mem
   {P:Ideal (Ring3 K)} {H A B:Ring3 K} {cost:ℕ}
   (hAB:A-B∈P) (h:FiniteRegularZeroSetBound P H B cost):
   FiniteRegularZeroSetBound P H A cost:=by
 intro points hP hH hA
 apply h points hP hH
 intro v hv
 rw [←eval_eq_of_sub_mem P hAB v (hP v hv)]
 exact hA v hv
theorem FiniteRegularZeroSetBound.regularity_congr
   {P:Ideal (Ring3 K)} {H H' A:Ring3 K} {cost:ℕ}
   (hHH':H-H'∈P) (h:FiniteRegularZeroSetBound P H A cost):
   FiniteRegularZeroSetBound P H' A cost:=by
 intro points hP hH' hA
 apply h points hP _ hA
 intro v hv
 rw [eval_eq_of_sub_mem P hHH' v (hP v hv)]
 exact hH' v hv
theorem FiniteRegularZeroSetBound.regularity_dvd
   {P:Ideal (Ring3 K)} {H H' A:Ring3 K} {cost:ℕ}
   (hdiv:H∣H') (h:FiniteRegularZeroSetBound P H A cost):
   FiniteRegularZeroSetBound P H' A cost:=by
 obtain ⟨B,rfl⟩:=hdiv
 intro points hP hHB hA
 apply h points hP _ hA
 intro v hv hzero
 apply hHB v hv
 simp only [map_mul,hzero,zero_mul]
theorem FiniteRegularZeroSetBound.map_residual
   (aY v bY aS bS cS:K) (hv:v≠0)
   {P:Ideal (Ring3 K)} {H A:Ring3 K} {cost:ℕ}
   (h:FiniteRegularZeroSetBound P H A cost):
   FiniteRegularZeroSetBound
     (P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom)
     (residualAlgHom aY v bY aS bS cS H)
     (residualAlgHom aY v bY aS bS cS A) cost:=by
 classical
 intro points hP hH hA
 let forward:=forwardResidualPoint aY v bY aS bS cS
 let oldPoints:=points.image forward
 have hcard:oldPoints.card=points.card:=
   Finset.card_image_of_injective points
     (forwardResidualPoint_injective aY v bY aS bS cS hv)
 rw [←hcard]
 apply h oldPoints
 · intro qOld hqOld
   obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hqOld
   exact (map_le_pointKernel_iff aY v bY aS bS cS hv P q).mp (hP q hq)
 · intro qOld hqOld
   obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hqOld
   have hn:=hH q hq
   change MvPolynomial.eval q (residualEquiv aY v bY aS bS cS hv H)≠0 at hn
   change MvPolynomial.eval (forwardResidualPoint aY v bY aS bS cS q) H≠0
   rwa [eval_residualEquiv] at hn
 · intro qOld hqOld
   obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hqOld
   have hz:=hA q hq
   change MvPolynomial.eval q (residualEquiv aY v bY aS bS cS hv A)=0 at hz
   change MvPolynomial.eval (forwardResidualPoint aY v bY aS bS cS q) A=0
   rwa [eval_residualEquiv] at hz
theorem FiniteRegularZeroSetBound.map_residual_of_inverse
   (aY v bY aS bS cS:K) (hv:v≠0)
   {P:Ideal (Ring3 K)} {H A:Ring3 K} {cost:ℕ}
   (h:FiniteRegularZeroSetBound P
     (originalAlgHom aY v bY aS bS cS H)
     (originalAlgHom aY v bY aS bS cS A) cost):
   FiniteRegularZeroSetBound
     (P.map (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom)
     H A cost:=by
 have ht:=h.map_residual aY v bY aS bS cS hv
 simpa only [residual_original_apply aY v bY aS bS cS hv] using ht
section Selected
open RCN136 RCN231 RCN319 RCN238 RCN243
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
local instance:DecidableEq Ω:=Classical.decEq Ω
theorem agreement_fiber_card_le_of_regular_zero_bound
   (φ:Polynomial K →+*Ω) (P:Ideal (Ring3 Ω))
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (Γ:Finset K)
   (p w:ℕ) [CharP Ω p] (hchar:w < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (x u₀ u₁:K) (cost:ℕ)
   (hzero:FiniteRegularZeroSetBound P (regularitySurface φ F)
     (agreementPolynomial φ F w x u₀ u₁) cost):
   (Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)).card ≤ cost:=by
 classical
 let fiber:=Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)
 let points:=fiber.image (selectedPoint φ selected)
 have hcount:points.card ≤ cost:=by
   apply hzero points
   · intro q hq
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hq
     exact hpoint γ (Finset.mem_filter.mp hγ).1
   · intro q hq
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hq
     change MvPolynomial.eval (selectedPoint φ selected γ)
       (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0
     rw [selectedPoint_evaluation]
     exact hregular γ (Finset.mem_filter.mp hγ).1
   · intro q hq
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hq
     obtain ⟨hΓ,hagree⟩:=Finset.mem_filter.mp hγ
     exact (selected_agreement_zero_iff φ F selected p w hchar γ
       (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) x u₀ u₁).mpr hagree
 have hcard:points.card=fiber.card:=
   Finset.card_image_of_injective _ (selectedPoint_injective φ selected)
 rwa [hcard] at hcount
end Selected
end
end ProximityPrize.SubmissionLower.RCN271
end PackedLegacy_O3

/-! Packed from ProximityPrize.SubmissionLower.E3. -/
section PackedLegacy_E3
namespace ProximityPrize.SubmissionLower.RCN257
open scoped Classical BigOperators WithZero
open RCN344 RCN000 RCN002 RCN005 RCN006 RCN007 RCN271 RCN341
noncomputable section
variable (K L:Type) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
 (A:Type) [CommRing A] [IsDomain A]
 [Algebra K A] [Algebra A L] [IsFractionRing A L]
 [Algebra (Polynomial K) A]
 [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
 [IsScalarTower (Polynomial K) A L]
local instance:DecidableEq K:=Classical.decEq K
theorem model_regular_value_eq_one (ψ:A →ₐ[K] K) (h:A) (hψ:ψ h≠0):
   (modelPlace K L A ψ).val (algebraMap A L h)=1:=by
 apply le_antisymm
 · exact actual_model_value_le_one K A L ψ h
 · apply le_of_not_gt
   intro hlt
   exact hψ ((actual_model_value_lt_one_iff K A L ψ h).mp hlt)
theorem model_regular_quotient_zero_order
   (ψ:A →ₐ[K] K) (a h:A) (k:ℕ) (ha:a≠0)
   (hzero:ψ a=0) (hregular:ψ h≠0):
   1 ≤ RCN026.order K L (modelPlace K L A ψ)
     (algebraMap A L a/(algebraMap A L h)^k):=by
 have hv:=model_regular_value_eq_one K L A ψ h hregular
 change 1 ≤-((modelPlace K L A ψ).val
   (algebraMap A L a/(algebraMap A L h)^k)).log
 simp only [map_div₀,map_pow,hv,one_pow,div_one]
 exact actual_model_zero_order_ge_one K A L ψ a ha hzero
theorem finite_model_regular_zeros_le_poleMass
   (a h:A) (k cost:ℕ) (ha:a≠0) (hh:h≠0)
   (hpole:∀ W:Finset (Place K L),
     (∑ v∈W,RCN346.poleOrder K L v
       (algebraMap A L a/(algebraMap A L h)^k)) ≤ (cost:ℤ))
   (S:Finset (A →ₐ[K] K))
   (hzero:∀ ψ∈S,ψ a=0) (hregular:∀ ψ∈S,ψ h≠0):
   S.card ≤ cost:=by
 classical
 let f:L:=algebraMap A L a/(algebraMap A L h)^k
 have hfa:algebraMap A L a≠0:=by
   simpa only [map_zero] using (IsFractionRing.injective A L).ne ha
 have hfh:algebraMap A L h≠0:=by
   simpa only [map_zero] using (IsFractionRing.injective A L).ne hh
 have hf:f≠0:=div_ne_zero hfa (pow_ne_zero k hfh)
 let U:=S.image (modelPlace K L A)
 have hU:∀ v∈U,1 ≤ RCN026.order K L v f:=by
   intro v hv
   obtain ⟨ψ,hψ,rfl⟩:=Finset.mem_image.mp hv
   exact model_regular_quotient_zero_order K L A ψ a h k ha
     (hzero ψ hψ) (hregular ψ hψ)
 have hcount:=RCN026.finite_zero_places_le_poleMass K L f hf U hU
 have hcard:U.card=S.card:=
   Finset.card_image_of_injective _ (modelPlace_injective K L A)
 have hb:(S.card:ℤ) ≤ cost:=by
   rw [←hcard]
   exact hcount.trans (hpole _)
 exact_mod_cast hb
section ActualCurve
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
theorem quotient_fraction_eq_field_eval (T:MvPolynomial (Fin 3) K):
   algebraMap (CoordinateRing K P) (CoordinateField K P) (Ideal.Quotient.mk P T)=
     MvPolynomial.aeval (coordinate K P) T:=by
 exact (aeval_coordinate_eq_quotient K P T).symm
theorem finite_regular_zero_bound_of_separator
   (base:SeparableLiteralCoordinate P)
   (H F:MvPolynomial (Fin 3) K) (k cost:ℕ) (hF:F∉P) (hH:H∉P)
   (hpole:
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       rationalBaseAlgebra K P base.index base.transcendental
     ∀ W:Finset (Place K (CoordinateField K P)),
       (∑ v∈W,RCN346.poleOrder K (CoordinateField K P) v
         (MvPolynomial.aeval (coordinate K P) F/
           (MvPolynomial.aeval (coordinate K P) H)^k)) ≤ (cost:ℤ)):
   FiniteRegularZeroSetBound P H F cost:=by
 classical
 let i₀:=base.index
 let hi₀:=base.transcendental
 letI:Algebra (Polynomial K) (CoordinateRing K P):=
   quotientPolynomialAlgebra K P i₀
 letI:Algebra (Polynomial K) (CoordinateField K P):=
   polynomialBaseAlgebra K P i₀
 letI:Algebra (RatFunc K) (CoordinateField K P):=
   rationalBaseAlgebra K P i₀ hi₀
 letI:=quotientBaseScalarTower K P i₀
 letI:=polynomialBaseScalarTower K P i₀
 letI:=quotientFractionScalarTower K P i₀
 letI:=polynomialRationalScalarTower K P i₀ hi₀
 letI:=rationalBaseScalarTower K P i₀ hi₀
 letI:FiniteDimensional (RatFunc K) (CoordinateField K P):=base.finite
 letI:Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=base.separable
 intro S hSP hSH hSF
 let liftPoint:{v:Fin 3 → K//v∈S} → (CoordinateRing K P →ₐ[K] K):=
   fun v↦pointHom K P ⟨v.1,hSP v.1 v.2⟩
 have hinj:Function.Injective liftPoint:=by
   intro v w hvw
   apply Subtype.ext
   exact congrArg (fun z:PointOn K P↦z.val) (pointHom_injective K P hvw)
 let points:=S.attach.image liftPoint
 have hzero:∀ ψ∈points,ψ (Ideal.Quotient.mk P F)=0:=by
   intro ψ hψ
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hψ
   exact hSF v.1 v.2
 have hregular:∀ ψ∈points,ψ (Ideal.Quotient.mk P H)≠0:=by
   intro ψ hψ
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hψ
   exact hSH v.1 v.2
 have hFq:Ideal.Quotient.mk P F≠0:=
   fun hz↦hF (Ideal.Quotient.eq_zero_iff_mem.mp hz)
 have hHq:Ideal.Quotient.mk P H≠0:=
   fun hz↦hH (Ideal.Quotient.eq_zero_iff_mem.mp hz)
 have hcount:=finite_model_regular_zeros_le_poleMass K (CoordinateField K P)
   (CoordinateRing K P) (Ideal.Quotient.mk P F) (Ideal.Quotient.mk P H)
   k cost hFq hHq (by simpa only [quotient_fraction_eq_field_eval] using hpole)
   points hzero hregular
 have hcard:points.card=S.card:=by
   change (S.attach.image liftPoint).card=S.card
   rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
 rwa [hcard] at hcount
end ActualCurve
end
end ProximityPrize.SubmissionLower.RCN257
end PackedLegacy_E3
