import ProximityPrize.SubmissionLower.Q1
namespace ProximityPrize.SubmissionLower.RCN332
open scoped Classical BigOperators
open RCN135 RCN136
open RCN159 RCN264
open RCN074
open RCN086 RCN243
open RCN238 RCN095
open RCN237
open RCN198
open RCN275
open RCN244
open RCN327
open RCN263 RCN089
open RCN066
open RCN334
open RCN331
open RCN336
open RCN027
open RCN030
open RCN029
open RCN338
open RCN042 RCN341
open RCN002 RCN344
open RCN340
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}
def reducedFirstCut
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)) : MvPolynomial (Fin 3) (GenericField K) :=
 reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1)
theorem ordinary_sub_reducedFirstCut_dvd
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)) :
   S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1) -
     reducedFirstCut S :=
 S.G_dvd_surface.trans
   (globalTailCut_sub_reduced_dvd (polynomialEmbedding K) (support a b s)
     S.F (w + 1))
theorem reducedFirstCut_proper
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   ¬ S.G ∣ reducedFirstCut S := by
 intro hr
 apply hfirstProper
 have h := (ordinary_sub_reducedFirstCut_dvd S).add hr
 simpa only [reducedFirstCut, sub_add_cancel] using h
theorem reducedFirstCut_in_flag
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)) :
   PolynomialInFlag (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S) := by
 exact reducedGlobalTailCut_in_flag (polynomialEmbedding K) (support a b s)
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩ (w + 1)
noncomputable def reducedUnitFamily
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :=
 let A := reducedActiveGeometry S hfirstProper hflagChar hmixed
 activeNestedUnitFamily A.base A.hactive A.hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
   S.irreducible_G (reducedFirstCut_proper S hfirstProper)
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))
noncomputable def reducedMultiplicity
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hs : (support a b s).s ≤ fixedSupport.s)
   (hys : (support a b s).ys ≤ fixedSupport.ys)
   (htotal : (support a b s).total ≤ fixedSupport.total)
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   FirstTailComponent S → ℕ :=
 localMultiplicity (loosenStage S hs hys htotal)
   (canonicalLocalDVRFamily (loosenStage S hs hys htotal) hfirstProper)
theorem reducedFixedPowers
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hs : (support a b s).s ≤ fixedSupport.s)
   (hys : (support a b s).ys ≤ fixedSupport.ys)
   (htotal : (support a b s).total ≤ fixedSupport.total)
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   let A := reducedActiveGeometry S hfirstProper hflagChar hmixed
   ActiveNestedFixedPowers A.base A.hactive A.hZ
     (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicity S hs hys htotal hfirstProper)) := by
 dsimp only
 exact reducedStage_activeFixedPowers (loosenStage S hs hys htotal)
   hfirstProper (reducedFirstCut S) (ordinary_sub_reducedFirstCut_dvd S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).base
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hactive
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).data
theorem reducedWeightedResultants
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hs : (support a b s).s ≤ fixedSupport.s)
   (hys : (support a b s).ys ≤ fixedSupport.ys)
   (htotal : (support a b s).total ≤ fixedSupport.total)
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicity S hs hys htotal hfirstProper)) := by
 let A := reducedActiveGeometry S hfirstProper hflagChar hmixed
 exact activeNestedWeightedCertificate A.base A.hactive A.hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
   S.irreducible_G (reducedFirstCut_proper S hfirstProper)
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))
   (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
     (reducedMultiplicity S hs hys htotal hfirstProper))
   (reducedFixedPowers S hs hys htotal hfirstProper hflagChar hmixed)
noncomputable def reducedBudgetFamily
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :=
 PrimeFlagBudgetFamily.ofCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
theorem transportedWeightedResultants
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hs : (support a b s).s ≤ fixedSupport.s)
   (hys : (support a b s).ys ≤ fixedSupport.ys)
   (htotal : (support a b s).total ≤ fixedSupport.total)
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedBudgetFamily S hfirstProper hflagChar hmixed)
     (reducedMultiplicity S hs hys htotal hfirstProper) := by
 exact weightedCertificate_of_congruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
   (reducedMultiplicity S hs hys htotal hfirstProper)
   (reducedWeightedResultants S hs hys htotal hfirstProper hflagChar hmixed)
noncomputable def reducedBaseOrd
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (C : FirstTailComponent S) : SeparableLiteralCoordinate C.1 := by
 let C' : RegularComponent (GenericField K) S.G (reducedFirstCut S)
     (regularitySurface (polynomialEmbedding K) S.F) :=
   ⟨C.1, by
     rw [← regularComponents_eq_of_dvd_sub (ordinary_sub_reducedFirstCut_dvd S)]
     exact C.2⟩
 exact (reducedActiveGeometry S hfirstProper hflagChar hmixed).base C'
theorem reducedBudgetFamily_yzPositive
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (C : FirstTailComponent S) :
   1 ≤ (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C := by
 let hd := ordinary_sub_reducedFirstCut_dvd S
 let C' := regularComponentEquiv hd C
 let A := reducedActiveGeometry S hfirstProper hflagChar hmixed
 let U := reducedUnitFamily S hfirstProper hflagChar hmixed
 change 1 ≤ U.toPrimeFlagBudgetFamily.yzCost C'
 change 1 ≤ coordinateDegree (GenericField K)
   (CoordinateField (GenericField K) C'.1) (U.yzProjection C')
 apply one_le_coordinateDegree_of_transcendental_value
 have hproj : U.yzProjection C' = coordinateOfGate
     (RCN093.affineU
       (GenericField K) C'.1 A.data.lam) (A.data.uGate C') := rfl
 rw [hproj, coordinateOfGate_value]
 exact A.data.uTranscendental C'
theorem reducedBudgetFamily_yzPole
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (C : FirstTailComponent S) :
   LiteralSupportPoleBound
     (reducedBaseOrd S hfirstProper hflagChar hmixed C)
     (flagSupport unitYZFlag)
     ((reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C) := by
 let C' : RegularComponent (GenericField K) S.G (reducedFirstCut S)
     (regularitySurface (polynomialEmbedding K) S.F) :=
   ⟨C.1, by
     rw [← regularComponents_eq_of_dvd_sub (ordinary_sub_reducedFirstCut_dvd S)]
     exact C.2⟩
 have heq : regularComponentEquiv (ordinary_sub_reducedFirstCut_dvd S) C = C' := by
   apply Subtype.ext
   rfl
 rw [show (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C =
     (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily.yzCost C' by
   simp only [reducedBudgetFamily, PrimeFlagBudgetFamily.ofCongruentCut, heq]]
 change LiteralSupportPoleBound
   ((reducedActiveGeometry S hfirstProper hflagChar hmixed).base C')
   (flagSupport unitYZFlag)
   ((reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily.yzCost C')
 exact (reducedUnitFamily S hfirstProper hflagChar hmixed).toAdaptiveUnitPoleBudget.yzPole C'
/- Support-generic counterparts. The legacy functions above are retained. -/
noncomputable def reducedMultiplicityGeneral
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   FirstTailComponent S → ℕ :=
 localMultiplicity (loosenStageGeneral S)
   (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper)

theorem reducedFixedPowersGeneral
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   let A := reducedActiveGeometry S hfirstProper hflagChar hmixed
   ActiveNestedFixedPowers A.base A.hactive A.hZ
     (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicityGeneral S hfirstProper)) := by
 dsimp only
 exact reducedStage_activeFixedPowers (loosenStageGeneral S)
   hfirstProper (reducedFirstCut S) (ordinary_sub_reducedFirstCut_dvd S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).base
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hactive
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).data

theorem reducedWeightedResultantsGeneral
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicityGeneral S hfirstProper)) := by
 let A := reducedActiveGeometry S hfirstProper hflagChar hmixed
 exact activeNestedWeightedCertificate A.base A.hactive A.hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
   S.irreducible_G (reducedFirstCut_proper S hfirstProper)
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))
   (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
     (reducedMultiplicityGeneral S hfirstProper))
   (reducedFixedPowersGeneral S hfirstProper hflagChar hmixed)

theorem transportedWeightedResultantsGeneral
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedBudgetFamily S hfirstProper hflagChar hmixed)
     (reducedMultiplicityGeneral S hfirstProper) := by
 exact weightedCertificate_of_congruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
   (reducedMultiplicityGeneral S hfirstProper)
   (reducedWeightedResultantsGeneral S hfirstProper hflagChar hmixed)

end
end ProximityPrize.SubmissionLower.RCN332
