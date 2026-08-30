import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.GN
namespace ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6656Research
open scoped Classical
open ActualCurveCoordinateField ActualCurveRationalProjection
open ActualCurveJointProjectionBounds ActualCoordinateDegreeSum
open ContactParameters6600Research ContactPrimeSeedIncidence
open ContactGenericSurface ContactProperCutSeedCount ContactRegularComponentCover
open ContactRegularFactorGate
open ContactFlagBezout6543Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualIncidenceResearch
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedUnitFamily6600Research
open ContactAdaptiveUnitPoleFamilyResearch
open ContactWeakSeparableSeparatorResearch
open ContactResidualStageDerivative6600Research
open ContactResidualSupportParametersResearch
open ContactRobustFixedMeet6656Research
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem residualStage_pderiv_one_ne_zero_of_support
   {p e d:ℕ} [CharP Omega p] {flag:FlagDegree}
   {support:ResidualSupportParameters}
   (S:ResidualStage phi Gamma x p e flag d support):
   MvPolynomial.pderiv (1:Fin 3) S.G≠0:=by
 intro hzero
 apply S.regular_proper
 rw [←surfaceMap_pderiv_R]
 obtain ⟨Q,hQ⟩:=S.G_dvd_surface
 refine ⟨MvPolynomial.pderiv (1:Fin 3) Q,?_⟩
 rw [hQ,MvPolynomial.pderiv_mul,hzero,zero_mul,zero_add]
def FixedMeetTerminalAdaptiveProjectionFamilies
   [CharP Omega prime]
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x prime meetProfile.errors flag meetProfile.w
     ResidualSupportParameters.fixedMeetSupport):Prop:=
 ∀ (D:S.TerminalDescendant) (i:Iota),
   i∈D.stage.nodes →
   ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i) →
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamily base flag
       (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag
         D.degree))
theorem fixedMeet_cut_coordinate_caps {d:ℕ} (hd:d ≤ 131071):
   (1+56*d)+11*d ≤ 1+67*131071∧
     11*d ≤ 11*131071∧
     1140*d+(1+56*d)+11*d ≤ 1+1207*131071:=by
 refine ⟨?_,Nat.mul_le_mul_left 11 hd,?_⟩
 · calc
     (1+56*d)+11*d=1+67*d:=by ring
     _ ≤ 1+67*131071:=Nat.add_le_add_left
       (Nat.mul_le_mul_left 67 hd) 1
 · calc
     1140*d+(1+56*d)+11*d=1+1207*d:=by ring
     _ ≤ 1+1207*131071:=Nat.add_le_add_left
       (Nat.mul_le_mul_left 1207 hd) 1
theorem fixedMeet_terminal_mixed_gates:
   (11*131071)*638+6*(1+1207*131071)=1869072466∧
     (1+67*131071)*6+40*(11*131071)=110361788∧
     1869072466 < prime:=by
 norm_num [prime]
theorem literalProjectionGates_of_fixedMeet_caps
   [CharP Omega prime]
   {G T H:MvPolynomial (Fin 3) Omega}
   (hGirreducible:Irreducible G)
   (hproper:¬ G∣T)
   (hGY:G.degreeOf 0 ≤ 40)
   (hGS:G.degreeOf 1 ≤ 6)
   (hGZ:G.degreeOf 2 ≤ 638)
   (hTY:T.degreeOf 0 ≤ 1+67*131071)
   (hTS:T.degreeOf 1 ≤ 11*131071)
   (hTZ:T.degreeOf 2 ≤ 1+1207*131071):
   (∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 0)∧
     (∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2):=by
 have hGdegree:∀ j:Fin 3,G.degreeOf j < prime:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt (by norm_num [prime])
   · exact hGS.trans_lt (by norm_num [prime])
   · exact hGZ.trans_lt (by norm_num [prime])
 have hmixedY:coordinateMixedDegree Omega G T 0 < prime:=by
   rw [coordinateMixedDegree_zero]
   apply (Nat.add_le_add
     (Nat.mul_le_mul hTS hGZ)
     (Nat.mul_le_mul hGS hTZ)).trans_lt
   norm_num [prime]
 have hmixedZ:coordinateMixedDegree Omega G T 2 < prime:=by
   rw [coordinateMixedDegree_two]
   apply (Nat.add_le_add
     (Nat.mul_le_mul hTY hGS)
     (Nat.mul_le_mul hGY hTS)).trans_lt
   norm_num [prime]
 constructor
 · intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 0 htr
     prime G T hGirreducible
     (regularComponent_G_mem Omega G T H C)
     (regularComponent_T_mem Omega G T H C)
     hproper hGdegree hmixedY
 · intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
     prime G T hGirreducible
     (regularComponent_G_mem Omega G T H C)
     (regularComponent_T_mem Omega G T H C)
     hproper hGdegree hmixedZ
theorem exists_adaptiveUnitProjectionFamily_of_literal_gates
   {G T H:MvPolynomial (Fin 3) Omega} {p q:FlagDegree}
   (hY:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGflag:PolynomialInFlag p G) (hTflag:PolynomialInFlag q T):
   ∃ base:∀ C:RegularComponent Omega G T H,
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamily base p q):=by
 have hbase:∀ C:RegularComponent Omega G T H,
     Nonempty (SeparableLiteralCoordinate C.1):=by
   intro C
   exact exists_separableLiteralCoordinate_of_YZ_gates C.1
     (regularComponent_ne_point Omega G T H C) (hY C) (hZ C)
 let base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1:=fun C↦Classical.choice (hbase C)
 refine ⟨base,?_⟩
 exact exists_adaptiveUnitProjectionFamily_of_nested p q base hY hZ
   hSderiv hG hproper
   ((support_subset_flagSupport_iff p G).2 hGflag)
   ((support_subset_flagSupport_iff q T).2 hTflag)
theorem literalProjectionGates_of_fixedMeet_flags
   [CharP Omega prime]
   {G T H:MvPolynomial (Fin 3) Omega} {flag:FlagDegree} {d:ℕ}
   (hGirreducible:Irreducible G) (hproper:¬ G∣T)
   (hGflag:PolynomialInFlag flag G)
   (hTflag:PolynomialInFlag
     (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag d) T)
   (hd:d ≤ 131071)
   (hflagZ:flag.zOnly ≤ 598)
   (hflagY:flag.yz ≤ 34)
   (hflagS:flag.all ≤ 6):
   (∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 0)∧
     (∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2):=by
 obtain ⟨hGY,hGS,hGZ⟩:=
   _root_.ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6600Research.degree_bounds_of_polynomialInFlag hGflag
 obtain ⟨hTY,hTS,hTZ⟩:=
   _root_.ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6600Research.degree_bounds_of_polynomialInFlag hTflag
 have hGY':G.degreeOf 0 ≤ 40:=
   hGY.trans (Nat.add_le_add hflagY hflagS)
 have hGS':G.degreeOf 1 ≤ 6:=hGS.trans hflagS
 have hGZ':G.degreeOf 2 ≤ 638:=
   hGZ.trans (Nat.add_le_add (Nat.add_le_add hflagZ hflagY) hflagS)
 have hTY':T.degreeOf 0 ≤ 1+67*131071:=by
   apply hTY.trans
   change (1+56*d)+11*d ≤ 1+67*131071
   exact (fixedMeet_cut_coordinate_caps hd).1
 have hTS':T.degreeOf 1 ≤ 11*131071:=by
   apply hTS.trans
   change 11*d ≤ 11*131071
   exact (fixedMeet_cut_coordinate_caps hd).2.1
 have hTZ':T.degreeOf 2 ≤ 1+1207*131071:=by
   apply hTZ.trans
   change 1140*d+(1+56*d)+11*d ≤ 1+1207*131071
   exact (fixedMeet_cut_coordinate_caps hd).2.2
 exact literalProjectionGates_of_fixedMeet_caps hGirreducible hproper
   hGY' hGS' hGZ' hTY' hTS' hTZ'
theorem fixedMeetTerminalAdaptiveProjection_at_cut_of_gates
   [CharP Omega prime]
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x prime meetProfile.errors flag meetProfile.w
     ResidualSupportParameters.fixedMeetSupport)
   (D:S.TerminalDescendant) (i:Iota)
   (hproper:¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
     (x i) (D.stage.u0 i) (D.stage.u1 i))
   (hGflag:PolynomialInFlag flag D.stage.G)
   (hTflag:PolynomialInFlag
     (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag D.degree)
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i)))
   (hY:∀ C:RegularComponent Omega D.stage.G
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (regularitySurface phi D.stage.F),LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega D.stage.G
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (regularitySurface phi D.stage.F),LiteralProjectionGate C 2):
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamily base flag
       (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag
         D.degree)):=by
 exact exists_adaptiveUnitProjectionFamily_of_literal_gates
   (G:=D.stage.G)
   (T:=agreementPolynomial phi D.stage.F D.degree
     (x i) (D.stage.u0 i) (D.stage.u1 i))
   (H:=regularitySurface phi D.stage.F)
   (p:=flag)
   (q:=ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag
     D.degree)
   hY hZ
   (residualStage_pderiv_one_ne_zero_of_support D.stage)
   D.stage.irreducible_G hproper
   hGflag hTflag
theorem fixedMeetTerminalAdaptiveProjection_at_cut
   [CharP Omega prime]
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x prime meetProfile.errors flag meetProfile.w
     ResidualSupportParameters.fixedMeetSupport)
   (hflagZ:flag.zOnly ≤ 598)
   (hflagY:flag.yz ≤ 34)
   (hflagS:flag.all ≤ 6)
   (D:S.TerminalDescendant) (i:Iota)
   (hi:i∈D.stage.nodes)
   (hproper:¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
     (x i) (D.stage.u0 i) (D.stage.u1 i)):
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamily base flag
       (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag
         D.degree)):=by
 classical
 let T:=agreementPolynomial phi D.stage.F D.degree
   (x i) (D.stage.u0 i) (D.stage.u1 i)
 let H:=regularitySurface phi D.stage.F
 change ¬ D.stage.G∣T at hproper
 change ∃ base:∀ C:RegularComponent Omega D.stage.G T H,
     SeparableLiteralCoordinate C.1,
   Nonempty (AdaptiveUnitProjectionFamily base flag
     (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag
       D.degree))
 have hGflag:PolynomialInFlag flag D.stage.G:=D.stage.flag_support
 have hTflag:PolynomialInFlag
     (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag D.degree) T:=by
   exact (terminal_proper_cuts_in_residual_flag D.stage D.terminal i hi).2
 have hD:D.degree ≤ meetProfile.w:=
   D.degree_le.trans (Nat.le_refl meetProfile.w)
 change D.degree ≤ 131071 at hD
 obtain ⟨hY,hZ⟩:=literalProjectionGates_of_fixedMeet_flags
   D.stage.irreducible_G hproper hGflag hTflag hD hflagZ hflagY hflagS
 exact fixedMeetTerminalAdaptiveProjection_at_cut_of_gates S D i hproper
   hGflag hTflag hY hZ
theorem fixedMeetTerminalAdaptiveProjectionFamilies_of_rectangular_caps
   [CharP Omega prime]
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x prime meetProfile.errors flag meetProfile.w
     ResidualSupportParameters.fixedMeetSupport)
   (hflagZ:flag.zOnly ≤ 598)
   (hflagY:flag.yz ≤ 34)
   (hflagS:flag.all ≤ 6):
   FixedMeetTerminalAdaptiveProjectionFamilies S:=by
 intro D i hi hproper
 exact fixedMeetTerminalAdaptiveProjection_at_cut S hflagZ hflagY hflagS
   D i hi hproper
end
end ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6656Research
