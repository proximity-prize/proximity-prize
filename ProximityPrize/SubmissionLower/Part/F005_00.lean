import ProximityPrize.SubmissionLower.Part.F004

section Compact_PackedLegacyCore2
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
theorem atLeast_mono (w:σ → ℕ) {m n:ℕ} {P:MvPolynomial σ K}
    (hmn:m ≤ n) (hP:AtLeast w n P):AtLeast w m P:=by
  intro d hd
  exact hmn.trans (hP d hd)
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
def order (w:σ → ℕ) (P:MvPolynomial σ K):ℕ:=by
  classical
  exact if hP:P = 0 then 0 else Classical.choose (exists_exactOrder w P hP)
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
def ContactAtLeast (x u₀ u₁:K) (m:ℕ) (P:Poly4 K):Prop :=
  AtLeast localWeights m (localize K x u₀ u₁ P)
def contactOrder (x u₀ u₁:K) (P:Poly4 K):ℕ :=
  order localWeights (localize K x u₀ u₁ P)
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
end KernelBridge
end
end ProximityPrize.SubmissionLower.ContactOrderBridge
end PackedLegacy_ContactOrderBridge
end Compact_PackedLegacyCore2
