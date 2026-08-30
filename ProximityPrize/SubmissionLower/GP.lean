import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DQ
import ProximityPrize.SubmissionLower.O6
import ProximityPrize.SubmissionLower.GO
namespace ProximityPrize.SubmissionLower.RCN316
open scoped Classical
open Polynomial KaehlerDifferential
open RCN002 RCN005
open RCN003 RCN001
open RCN223 RCN238
open RCN136 RCN243 RCN264
open RCN095
open RCN159
open RCN158
open RCN037
open RCN038
open RCN040
open RCN041
open RCN046
open RCN265
open RCN341
open RCN277
open RCN274
open RCN275
open RCN276
open RCN315
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
def TerminalAdaptiveProjectionFamiliesOfSupport
   {pchar e w:ℕ} [CharP Omega pchar]
   {flag:FlagDegree}
   (support:ResidualSupportParameters)
   (S:ResidualStage phi Gamma x pchar e flag w support):Prop:=
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
       (support.residualAgreementFlag D.degree))
def TerminalAdaptiveProjectionFamiliesYZOfSupport
   {pchar e w:ℕ} [CharP Omega pchar]
   {flag:FlagDegree}
   (support:ResidualSupportParameters)
   (S:ResidualStage phi Gamma x pchar e flag w support):Prop:=
 ∀ (D:S.TerminalDescendant) (i:Iota),
   i∈D.stage.nodes →
   ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i) →
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (support.residualAgreementFlag D.degree))
theorem terminalAdaptiveProjectionAtCutYZ_of_active_yz_gates
   {pchar e w:ℕ} [CharP Omega pchar]
   {support:ResidualSupportParameters} {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar e flag w support)
   (D:S.TerminalDescendant) (i:Iota)
   (hproper:¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
     (x i) (D.stage.u0 i) (D.stage.u1 i))
   (hGdegree:∀ j:Fin 3,D.stage.G.degreeOf j < pchar)
   (hmixedZ:coordinateMixedDegree Omega D.stage.G
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i)) 2 < pchar)
   (hGflag:PolynomialInFlag flag D.stage.G)
   (hTflag:PolynomialInFlag (support.residualAgreementFlag D.degree)
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))):
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (support.residualAgreementFlag D.degree)):=by
 classical
 let T:=agreementPolynomial phi D.stage.F D.degree
   (x i) (D.stage.u0 i) (D.stage.u1 i)
 let H:=regularitySurface phi D.stage.F
 let choiceData:∀ C:RegularComponent Omega D.stage.G T H,
     ∃ B:SeparableLiteralCoordinate C.1,B.index=0∨B.index=2:=
   fun C↦regularComponent_exists_separableLiteralCoordinate6630
     phi D.stage.F D.stage.G T pchar D.stage.G_dvd_surface
     D.stage.irreducible_G hproper D.stage.y_dependent hGdegree hmixedZ C
 let base:∀ C:RegularComponent Omega D.stage.G T H,
     SeparableLiteralCoordinate C.1:=fun C↦(choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Omega D.stage.G T H,
     (base C).index=0∨(base C).index=2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Omega D.stage.G T H,
     KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 0)≠0∨
       KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 2)≠0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left
     simpa only [hidx] using hb
   · right
     simpa only [hidx] using hb
 let hZ:∀ C:RegularComponent Omega D.stage.G T H,
     LiteralProjectionGate C 2:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
     pchar D.stage.G T D.stage.irreducible_G
     (regularComponent_G_mem Omega D.stage.G T H C)
     (regularComponent_T_mem Omega D.stage.G T H C)
     hproper hGdegree hmixedZ
 obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
   flag (support.residualAgreementFlag D.degree)
   base hactive hZ (residualStage_pderiv_one_ne_zero_of_support D.stage)
   D.stage.irreducible_G hproper
   ((support_subset_flagSupport_iff flag D.stage.G).2 hGflag)
   ((support_subset_flagSupport_iff (support.residualAgreementFlag D.degree)
     T).2 hTflag)
 exact ⟨base,⟨P⟩⟩
theorem terminalAdaptiveProjectionAtCut_of_active_yz_gates
   {pchar e w:ℕ} [CharP Omega pchar]
   {support:ResidualSupportParameters} {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar e flag w support)
   (D:S.TerminalDescendant) (i:Iota)
   (hproper:¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
     (x i) (D.stage.u0 i) (D.stage.u1 i))
   (hGdegree:∀ j:Fin 3,D.stage.G.degreeOf j < pchar)
   (hmixedZ:coordinateMixedDegree Omega D.stage.G
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i)) 2 < pchar)
   (hGflag:PolynomialInFlag flag D.stage.G)
   (hTflag:PolynomialInFlag (support.residualAgreementFlag D.degree)
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))):
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamily base flag
       (support.residualAgreementFlag D.degree)):=by
 obtain ⟨base,⟨P⟩⟩:=terminalAdaptiveProjectionAtCutYZ_of_active_yz_gates
   S D i hproper hGdegree hmixedZ hGflag hTflag
 exact ⟨base,⟨P.family⟩⟩
theorem terminalAdaptiveProjectionFamiliesYZOfSupport_of_active_yz_caps
   {pchar e w:ℕ} [CharP Omega pchar]
   {flag:FlagDegree}
   (support:ResidualSupportParameters)
   (S:ResidualStage phi Gamma x pchar e flag w support)
   (surfaceY surfaceS surfaceZ cutY cutS:ℕ)
   (hflagY:flag.yz+flag.all ≤ surfaceY)
   (hflagS:flag.all ≤ surfaceS)
   (hflagZ:flag.zOnly+flag.yz+flag.all ≤ surfaceZ)
   (hcutY:1+w*(2*support.ys-1) ≤ cutY)
   (hcutS:(2*support.s-1)*w ≤ cutS)
   (hsurfaceChar:surfaceY < pchar∧surfaceS < pchar∧
     surfaceZ < pchar)
   (hmixedZ:cutY*surfaceS+surfaceY*cutS < pchar):
   TerminalAdaptiveProjectionFamiliesYZOfSupport support S:=by
 intro D i hi hproper
 let T:=agreementPolynomial phi D.stage.F D.degree
   (x i) (D.stage.u0 i) (D.stage.u1 i)
 have hGflag:PolynomialInFlag flag D.stage.G:=D.stage.flag_support
 have hTflag:PolynomialInFlag (support.residualAgreementFlag D.degree) T:=
   (terminal_proper_cuts_in_residual_flag D.stage D.terminal i hi).2
 obtain ⟨hGY,hGS,hGZ⟩:=
   RCN314.degree_bounds_of_polynomialInFlag
     hGflag
 obtain ⟨hTY,hTS,_hTZ⟩:=
   RCN314.degree_bounds_of_polynomialInFlag
     hTflag
 have hD:D.degree ≤ w:=D.degree_le.trans (Nat.le_refl w)
 have hGY':D.stage.G.degreeOf 0 ≤ surfaceY:=hGY.trans hflagY
 have hGS':D.stage.G.degreeOf 1 ≤ surfaceS:=hGS.trans hflagS
 have hGZ':D.stage.G.degreeOf 2 ≤ surfaceZ:=hGZ.trans hflagZ
 have hTY':T.degreeOf 0 ≤ cutY:=by
   calc
     T.degreeOf 0 ≤
         (support.residualAgreementFlag D.degree).yz+
           (support.residualAgreementFlag D.degree).all:=hTY
     _=1+D.degree*(2*support.ys-1):=
       support.residualAgreementFlag_ys D.degree
     _ ≤ 1+w*(2*support.ys-1):=
       Nat.add_le_add_left
         (Nat.mul_le_mul_right (2*support.ys-1) hD) 1
     _ ≤ cutY:=hcutY
 have hTS':T.degreeOf 1 ≤ cutS:=by
   calc
     T.degreeOf 1 ≤ (support.residualAgreementFlag D.degree).all:=hTS
     _=(2*support.s-1)*D.degree:=by
       simp only [ResidualSupportParameters.residualAgreementFlag,
         ResidualSupportParameters.agreementDirection]
     _ ≤ (2*support.s-1)*w:=
       Nat.mul_le_mul_left (2*support.s-1) hD
     _ ≤ cutS:=hcutS
 have hGdegree:∀ j:Fin 3,D.stage.G.degreeOf j < pchar:=by
   intro j
   fin_cases j
   · exact hGY'.trans_lt hsurfaceChar.1
   · exact hGS'.trans_lt hsurfaceChar.2.1
   · exact hGZ'.trans_lt hsurfaceChar.2.2
 have hmixedZ':coordinateMixedDegree Omega D.stage.G T 2 < pchar:=by
   rw [coordinateMixedDegree_two]
   exact (Nat.add_le_add
     (Nat.mul_le_mul hTY' hGS')
     (Nat.mul_le_mul hGY' hTS')).trans_lt hmixedZ
 exact terminalAdaptiveProjectionAtCutYZ_of_active_yz_gates S D i hproper
   hGdegree hmixedZ' hGflag hTflag
theorem terminalAdaptiveProjectionFamiliesOfSupport_of_active_yz_caps
   {pchar e w:ℕ} [CharP Omega pchar]
   {flag:FlagDegree}
   (support:ResidualSupportParameters)
   (S:ResidualStage phi Gamma x pchar e flag w support)
   (surfaceY surfaceS surfaceZ cutY cutS:ℕ)
   (hflagY:flag.yz+flag.all ≤ surfaceY)
   (hflagS:flag.all ≤ surfaceS)
   (hflagZ:flag.zOnly+flag.yz+flag.all ≤ surfaceZ)
   (hcutY:1+w*(2*support.ys-1) ≤ cutY)
   (hcutS:(2*support.s-1)*w ≤ cutS)
   (hsurfaceChar:surfaceY < pchar∧surfaceS < pchar∧
     surfaceZ < pchar)
   (hmixedZ:cutY*surfaceS+surfaceY*cutS < pchar):
   TerminalAdaptiveProjectionFamiliesOfSupport support S:=by
 intro D i hi hproper
 obtain ⟨base,⟨P⟩⟩:=
   terminalAdaptiveProjectionFamiliesYZOfSupport_of_active_yz_caps
     support S surfaceY surfaceS surfaceZ cutY cutS hflagY hflagS hflagZ
     hcutY hcutS hsurfaceChar hmixedZ D i hi hproper
 exact ⟨base,⟨P.family⟩⟩
theorem fixedMeetTerminalAdaptiveProjectionFamilies_of_active_yz
   [CharP Omega prime]
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x prime meetProfile.errors flag meetProfile.w
     ResidualSupportParameters.fixedMeetSupport)
   (hflagZ:flag.zOnly ≤ 598)
   (hflagY:flag.yz ≤ 34)
   (hflagS:flag.all ≤ 6):
   FixedMeetTerminalAdaptiveProjectionFamilies S:=by
 intro D i hi hproper
 apply (terminalAdaptiveProjectionFamiliesOfSupport_of_active_yz_caps
   ResidualSupportParameters.fixedMeetSupport S
   40 6 638 (1+67*131071) (11*131071)
   (by omega) hflagS (by omega)
   (by norm_num [meetProfile,ResidualSupportParameters.fixedMeetSupport])
   (by norm_num [meetProfile,ResidualSupportParameters.fixedMeetSupport])
   (by norm_num [prime]) (by norm_num [prime])) D i hi hproper
def frontierMeetSupport182688:ResidualSupportParameters where
 s:=7
 ys:=36
 total:=683
 one_le_s:=by norm_num
 s_le_ys:=by norm_num
 ys_le_total:=by norm_num
 two_le_ys:=by norm_num
theorem frontierMeet182688_parameters:
   26*182688=4749888∧(4749888-1)/131071=36∧
     frontierMeetSupport182688.agreementDirection=⟨1294,58,13⟩:=by
 norm_num [frontierMeetSupport182688,
   ResidualSupportParameters.agreementDirection]
theorem frontierMeet182688TerminalAdaptiveProjectionFamilies_of_active_yz
   [CharP Omega prime]
   {e:ℕ} {flag:FlagDegree}
   (S:ResidualStage phi Gamma x prime e flag 131071
     frontierMeetSupport182688)
   (hflagZ:flag.zOnly ≤ 676)
   (hflagY:flag.yz ≤ 36)
   (hflagS:flag.all ≤ 7):
   TerminalAdaptiveProjectionFamiliesOfSupport frontierMeetSupport182688 S:=by
 apply terminalAdaptiveProjectionFamiliesOfSupport_of_active_yz_caps
   frontierMeetSupport182688 S
   43 7 719 (1+71*131071) (13*131071)
 · omega
 · exact hflagS
 · omega
 · norm_num [frontierMeetSupport182688]
 · norm_num [frontierMeetSupport182688]
 · norm_num [prime]
 · norm_num [prime]
theorem frontierMeet182688TerminalAdaptiveProjectionFamiliesYZ_of_active_yz
   [CharP Omega prime]
   {e:ℕ} {flag:FlagDegree}
   (S:ResidualStage phi Gamma x prime e flag 131071
     frontierMeetSupport182688)
   (hflagZ:flag.zOnly ≤ 676)
   (hflagY:flag.yz ≤ 36)
   (hflagS:flag.all ≤ 7):
   TerminalAdaptiveProjectionFamiliesYZOfSupport frontierMeetSupport182688 S:=by
 apply terminalAdaptiveProjectionFamiliesYZOfSupport_of_active_yz_caps
   frontierMeetSupport182688 S
   43 7 719 (1+71*131071) (13*131071)
 · omega
 · exact hflagS
 · omega
 · norm_num [frontierMeetSupport182688]
 · norm_num [frontierMeetSupport182688]
 · norm_num [prime]
 · norm_num [prime]
end
end ProximityPrize.SubmissionLower.RCN316
