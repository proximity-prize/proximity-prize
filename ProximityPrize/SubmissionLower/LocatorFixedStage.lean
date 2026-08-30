import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BF
import ProximityPrize.SubmissionLower.Q2
import ProximityPrize.SubmissionLower.EQ
import ProximityPrize.SubmissionLower.J3
import ProximityPrize.SubmissionLower.LocatorFactorAggregate
import ProximityPrize.SubmissionLower.LocatorMovingTransport
namespace ProximityPrize.SubmissionLower.LocatorFixedStage
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN174
open RCN159 RCN086
open RCN095 RCN275
open RCN198 RCN263
open RCN146 RCN087
open RCN203 RCN084
open RCN313 RCN074
open RCN335
open RCN066 RCN085 RCN088
open RCN199 RCN332 RCN338
open RCN287
open RCN046 RCN206 RCN237 RCN264 RCN330
open RCN238 RCN243 RCN341
open RCN207
open RCN271
open RCN244 RCN312 RCN328 RCN334
open LocatorMovingTransport
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80201
def agreements:ℕ:=181943
def gap:ℕ:=50872
def prime:ℕ:=2130706433
def weightedCap:ℕ:=8551321
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K prime:=by
 simpa [prime, RCN223.prime] using
   RCN128.challenge_field_characteristic6600
def firstTail (a b s:ℕ):FlagDegree :=
 reducedResidualAgreementFlag (RCN198.support a b s) (w + 1)
def secondTail (a b s:ℕ):FlagDegree :=
 reducedResidualAgreementFlag (RCN198.support a b s) (w + 2)
def rationalFlag (a b s:ℕ):FlagDegree :=
 ⟨2 * a + (w + 1) * a,
   2 * b + 2 + (w + 1) * (b + 1),
   2 * s + 3 + (w + 1) * s⟩
def movingFiberFlag (a b s:ℕ):FlagDegree:=⟨a, b + 1, s + 3⟩
def movingCutFlag (a b s:ℕ):FlagDegree :=
 ⟨2 * a + (w + 1) * a,
   2 * b + 2 + (w + 1) * (b + 1),
   2 * s + 3 + (w + 1) * (s + 2)⟩
def hybridStageCost (flag:FlagDegree) (a b s:ℕ):ℕ :=
 flagMixed flag (firstTail a b s) (rationalFlag a b s) +
   (w + 2) * flagMixed flag (movingFiberFlag a b s) (movingCutFlag a b s)
theorem row_values :
   agreements + errors = n ∧ agreements - w = gap ∧
   weightedCap = 47 * agreements ∧ w < agreements ∧
   w + 1 ≤ weightedCap ∧ weightedCap < prime:=by
 norm_num [agreements, errors, n, w, gap, weightedCap, prime]
theorem tail_support_formula (a b s d:ℕ) :
   reducedResidualAgreementFlag (RCN198.support a b s) d =
     ⟨2 * a * d, 1 + 2 * (b + 1) * d, 2 * (s + 1) * d⟩:=by
 have ht:a + b + s + 3 - (b + s + 3) = a:=by omega
 have hy:b + s + 3 - (s + 2) = b + 1:=by omega
 have hs:2 * (s + 2) - 2 = 2 * (s + 1):=by omega
 simp only [reducedResidualAgreementFlag, reducedAgreementDirection, RCN198.support]
 rw [ht, hy, hs]
theorem identityDegree_linear (flag:FlagDegree) (a b s:ℕ) :
   identityCurveDegree flag a b s w =
     flag.zOnly * (393219 + 262146 * s) +
     flag.yz * (786438 + 524292 * s) +
     flag.all * (1048586 + 262146 * a + 524292 * b + 524292 * s):=by
 simp only [identityCurveDegree, paddedCut,
   RCN206.centreFlag,
   RCN206.directionFlag,
   flagMixed, unitZFlag, unitYZFlag, add_zOnly, add_yz, add_all,
   nsmul_zOnly, nsmul_yz, nsmul_all, w]
 ring
def identitySlackZ (b s:ℕ):ℕ :=
 6354155669414290 + 6991847784185856 * b + 11227960454355676 * s +
   3495923892092928 * s ^ 2 + 6991847784185856 * b * s
def identitySlackYZ (a b s:ℕ):ℕ :=
 2220512990868916 + 6991847784185856 * a + 6991847784185856 * b +
   8472198668658760 * s + 3495923892092928 * s ^ 2 +
   6991847784185856 * a * s + 6991847784185856 * b * s
def identitySlackAll (a b s:ℕ):ℕ :=
 2960680744363188 + 11227960454355676 * a + 8472198668658760 * b +
   3495923892092928 * b ^ 2 + 8472198668658760 * s +
   3495923892092928 * s ^ 2 + 6991847784185856 * a * b +
   6991847784185856 * a * s + 6991847784185856 * b * s
def identitySlack (flag:FlagDegree) (a b s:ℕ):ℕ :=
 flag.zOnly * identitySlackZ b s + flag.yz * identitySlackYZ a b s +
   flag.all * identitySlackAll a b s
theorem identity_budget_exact (flag:FlagDegree) (a b s:ℕ) :
   gap * flagMixed flag (firstTail a b s) (secondTail a b s) =
     (n - w) * (errors + 1) * identityCurveDegree flag a b s w +
       identitySlack flag a b s:=by
 rw [identityDegree_linear]
 norm_num [firstTail, secondTail, tail_support_formula, w, n, errors, gap,
   identitySlack, identitySlackZ, identitySlackYZ, identitySlackAll, flagMixed] <;>
   ring
theorem identity_budget (flag:FlagDegree) (a b s:ℕ) :
   (n - w) * (errors + 1) * identityCurveDegree flag a b s w ≤
     gap * flagMixed flag (firstTail a b s) (secondTail a b s):=by
 rw [identity_budget_exact]
 exact Nat.le_add_right _ _
def hybridIdentitySlackZ (b s:ℕ):ℕ :=
 7228323344458042 + 6117980165831800 * b + 8606164229632564 * s +
   2621969590750576 * s ^ 2 + 5243939181501152 * b * s
def hybridIdentitySlackYZ (a b s:ℕ):ℕ :=
 3094680665912668 + 6117980165831800 * a + 6117980165831800 * b +
   5850402443935648 * s + 2621969590750576 * s ^ 2 +
   5243939181501152 * a * s + 5243939181501152 * b * s
def hybridIdentitySlackAll (a b s:ℕ):ℕ :=
 2960874114329364 + 8606164229632564 * a + 5850402443935648 * b +
   2621969590750576 * b ^ 2 + 5850402443935648 * s +
   2621969590750576 * s ^ 2 + 5243939181501152 * a * b +
   5243939181501152 * a * s + 5243939181501152 * b * s
def hybridIdentitySlack (flag:FlagDegree) (a b s:ℕ):ℕ :=
 flag.zOnly * hybridIdentitySlackZ b s +
   flag.yz * hybridIdentitySlackYZ a b s +
   flag.all * hybridIdentitySlackAll a b s
theorem identity_budget_hybrid_exact (flag:FlagDegree) (a b s:ℕ) :
   gap * hybridStageCost flag a b s =
     (n - w) * (errors + 1) * identityCurveDegree flag a b s w +
       hybridIdentitySlack flag a b s:=by
 rw [identityDegree_linear]
 norm_num [hybridStageCost, firstTail, tail_support_formula, rationalFlag,
   movingFiberFlag, movingCutFlag, w, n, errors, gap,
   hybridIdentitySlack, hybridIdentitySlackZ, hybridIdentitySlackYZ,
   hybridIdentitySlackAll, flagMixed] <;>
   ring
theorem identity_budget_hybrid (flag:FlagDegree) (a b s:ℕ) :
   (n - w) * (errors + 1) * identityCurveDegree flag a b s w ≤
     gap * hybridStageCost flag a b s:=by
 rw [identity_budget_hybrid_exact]
 exact Nat.le_add_right _ _
theorem identity_positive (flag:FlagDegree) (a b s:ℕ)
   (hpos:0 < flag.zOnly + flag.yz + flag.all) :
   1 ≤ identityCurveDegree flag a b s w:=by
 rw [identityDegree_linear]
 have hz:=Nat.mul_le_mul_left flag.zOnly
   (show 1 ≤ 393219 + 262146 * s by omega)
 have hy:=Nat.mul_le_mul_left flag.yz
   (show 1 ≤ 786438 + 524292 * s by omega)
 have ha:=Nat.mul_le_mul_left flag.all
   (show 1 ≤ 1048586 + 262146 * a + 524292 * b + 524292 * s by omega)
 simp only [Nat.mul_one] at hz hy ha
 omega
theorem tangent_gate (a b s:ℕ) :
   errors + 1 ≤ (secondTail a b s).yz:=by
 rw [secondTail, tail_support_formula]
 change errors + 1 ≤ 1 + 2 * (b + 1) * (w + 2)
 have hb:2 * (w + 2) ≤ 2 * (b + 1) * (w + 2):=by
   have h:=Nat.mul_le_mul_right (w + 2)
     (Nat.mul_le_mul_left 2 (show 1 ≤ b + 1 by omega))
   simpa only [Nat.mul_one] using h
 exact (by norm_num [errors, w]:errors + 1 ≤ 1 + 2 * (w + 2)).trans
   (Nat.add_le_add_left hb 1)
private theorem delayed_sharp_below_rational
   (a b s delay multiplicity:ℕ) (hs:7 ≤ s)
   (hdelay:delay ≤ multiplicity) (hmu:3 ≤ multiplicity) :
   LocatorFactorAggregate.Below
     (sharpResidualAgreementFlag (RCN198.support a b s) (w + 1 + delay))
     (multiplicity • rationalFlag a b s):=by
 have ha:a + b + s + 3 - (b + s + 3) = a:=by omega
 have hb:b + s + 3 - (s + 2) = b + 1:=by omega
 have hall:2 * (s + 2) - 1 = 2 * s + 3:=by omega
 have hby:2 * (b + 1) - 1 = 2 * b + 1:=by omega
 have hmiddle :
     1 + (2 * (b + 1) - 1) * (w + 1 + delay) +
         (2 * s + 3) * (w + 1 + delay) ≤
       multiplicity *
         ((2 * b + 2 + (w + 1) * (b + 1)) +
           (2 * s + 3 + (w + 1) * s)):=by
   norm_num [w]
   rw [hby]
   nlinarith
 have htotal :
     2 * a * (w + 1 + delay) +
         (1 + (2 * (b + 1) - 1) * (w + 1 + delay)) +
         (2 * s + 3) * (w + 1 + delay) ≤
       multiplicity *
         ((2 * a + (w + 1) * a) +
           (2 * b + 2 + (w + 1) * (b + 1)) +
           (2 * s + 3 + (w + 1) * s)):=by
   norm_num [w]
   rw [hby]
   nlinarith
 unfold LocatorFactorAggregate.Below LocatorFactorAggregate.middle
   LocatorFactorAggregate.total
 simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
   RCN198.support, rationalFlag, nsmul_zOnly, nsmul_yz, nsmul_all,
   ha, hb, hall]
 constructor
 · norm_num [w]
   nlinarith
 constructor
 · simpa only [Nat.mul_add] using hmiddle
 · simpa only [Nat.mul_add] using htotal
theorem laterTail_in_rationalFlag
   {Gamma:Finset K} {flag:FlagDegree} {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
     prime errors flag w (RCN198.support a b s))
   (delay multiplicity:ℕ) (hs:7 ≤ s) (hdelay:1 ≤ delay)
   (hdelayMu:delay ≤ multiplicity) (hmu:3 ≤ multiplicity) :
   PolynomialInFlag (multiplicity • rationalFlag a b s)
     (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)):=by
 have hsharp:PolynomialInFlag
     (sharpResidualAgreementFlag (RCN198.support a b s) (w + 1 + delay))
     (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)):=by
   exact RCN287.surfaceMap_agreement_in_sharp_flag
     (P:=RCN198.support a b s)
     (by change s + 2 < b + s + 3; omega) (polynomialEmbedding K)
     ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
     (w + 1 + delay) (tailSelector (w + 1 + delay)) 0 0 0
 have hbelow:=delayed_sharp_below_rational a b s delay multiplicity hs hdelayMu hmu
 intro exponent hexponent
 have h:=hsharp exponent hexponent
 exact ⟨h.1.trans hbelow.1, h.2.1.trans hbelow.2.1,
   h.2.2.trans hbelow.2.2⟩
theorem reducedTail_below_sharp (a b s d:ℕ) :
   LocatorFactorAggregate.Below
     (reducedResidualAgreementFlag (RCN198.support a b s) d)
     (sharpResidualAgreementFlag (RCN198.support a b s) d):=by
 have ha:a + b + s + 3 - (b + s + 3) = a:=by omega
 have hb:b + s + 3 - (s + 2) = b + 1:=by omega
 have hall:2 * (s + 2) - 1 = 2 * s + 3:=by omega
 have hby:2 * (b + 1) - 1 = 2 * b + 1:=by omega
 rw [tail_support_formula]
 unfold LocatorFactorAggregate.Below LocatorFactorAggregate.middle
   LocatorFactorAggregate.total
 simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
   RCN198.support, ha, hb, hall, hby]
 refine ⟨Nat.mul_le_mul_right d (by omega), ?_, ?_⟩
 · ring_nf
   exact le_rfl
 · ring_nf
   exact le_rfl
def movingSharpFlag (a b s d:ℕ):FlagDegree :=
 ⟨2 * a * d, 1 + (2 * (b + 1) - 1) * d, (2 * s + 3) * d⟩
theorem movingSharpFlag_eq_sharp (a b s d:ℕ) :
   movingSharpFlag a b s d =
     sharpResidualAgreementFlag (RCN198.support a b s) d:=by
 have ha:a + b + s + 3 - (b + s + 3) = a:=by omega
 have hb:b + s + 3 - (s + 2) = b + 1:=by omega
 have hall:2 * (s + 2) - 1 = 2 * s + 3:=by omega
 simp only [movingSharpFlag, sharpResidualAgreementFlag,
   sharpAgreementDirection, RCN198.support, ha, hb, hall]
noncomputable def movingUnitFamily
   {F I0:Type} [Field F] {Gamma:Finset F} {x:I0 → F}
   {p e:ℕ} [CharP (GenericField F) p]
   {flag:FlagDegree} {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding F) Gamma x
     p e flag RCN327.w (RCN198.support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding F) S.F (RCN327.w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (RCN327.w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (RCN327.w + 1)) < p)
   (Q:FlagDegree)
   (hbelow:LocatorFactorAggregate.Below
     (reducedResidualAgreementFlag (RCN198.support a b s) (RCN327.w + 1)) Q) :
   UnitFamilyBundle (F:=F) (I0:=I0) (Gamma:=Gamma)
     (x:=x) (p:=p) (e:=e) (w0:=RCN327.w)
     (flag:=flag) (P:=RCN198.support a b s) S Q:=by
 classical
 let base:∀ C:FirstTailComponent S, SeparableLiteralCoordinate C.1 :=
   reducedBaseOrd (K:=F) (I:=I0) (Gamma:=Gamma) (x:=x)
     (p:=p) (stageErrorCap:=e) (flag:=flag)
     (a:=a) (b:=b) (s:=s) S hfirstProper hflagChar hmixed
 let h:=ordinary_sub_reducedFirstCut_dvd S
 let U:=reducedUnitFamily S hfirstProper hflagChar hmixed
 exact ⟨base, unitFamily_ofCongruentCut h base U hbelow⟩
theorem exists_movingBudgets
   {Gamma:Finset K} {flag:FlagDegree} {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
     prime errors flag w (RCN198.support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < prime ∧ flag.all < prime ∧
     flag.zOnly + flag.yz + flag.all < prime)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < prime)
   (hmix:2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) < prime) :
   ∃ (base:∀ C:FirstTailComponent S, SeparableLiteralCoordinate C.1)
     (M:∀ C:FirstTailComponent S,
       MovingPoleBudget C.1
         (regularitySurface (polynomialEmbedding K) S.F)
         (surfaceMap (polynomialEmbedding K) (polyG K S.F))),
     (∀ C,
       (M C).zCost = (reducedBudgetFamily S hfirstProper hflagChar hmixed).zCost C ∧
       (M C).yzCost = (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C ∧
       (M C).allCost = (reducedBudgetFamily S hfirstProper hflagChar hmixed).allCost C) ∧
     (∑ C, (M C).movingCost) ≤
       flagMixed flag (movingFiberFlag a b s) (movingCutFlag a b s):=by
 classical
 let base:∀ C:FirstTailComponent S, SeparableLiteralCoordinate C.1 :=
   reducedBaseOrd S hfirstProper hflagChar hmixed
 let h:=ordinary_sub_reducedFirstCut_dvd S
 let Ured:=reducedUnitFamily S hfirstProper hflagChar hmixed
 let hbelow:=reducedTail_below_sharp a b s (w + 1)
 let U:=unitFamily_ofCongruentCut h base Ured hbelow
 let E:=AlgebraicClosure (RatFunc (GenericField K))
 letI:IsScalarTower (GenericField K) (RatFunc (GenericField K)) E:=by
   infer_instance
 letI:CharP E prime:=by infer_instance
 let Hsupport:ResidualSupportData (RCN198.support a b s) S.F :=
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
 obtain ⟨M, hcost, _hz, _hyz, _hall, hmove⟩ :=
   exists_firstTail_cut_budgets (E:=E)
     (polynomialEmbedding K) S.F S.G
     (globalTailCut (polynomialEmbedding K) S.F (w + 1))
     a b s w (by norm_num [w]) rfl Hsupport flag
     S.irreducible_G.ne_zero S.G_dvd_surface S.flag_support
     base U prime hmix
 refine ⟨base, M, ?_, ?_⟩
 · intro C
   have hc:=hcost C
   have ht:=unitFamily_ofCongruentCut_costs h base Ured hbelow C
   have hz:U.toPrimeFlagBudgetFamily.zCost C =
       (reducedBudgetFamily S hfirstProper hflagChar hmixed).zCost C:=by
     change U.toPrimeFlagBudgetFamily.zCost C =
       (PrimeFlagBudgetFamily.ofCongruentCut h
         Ured.toPrimeFlagBudgetFamily).zCost C
     exact ht.1
   have hyz:U.toPrimeFlagBudgetFamily.yzCost C =
       (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C:=by
     change U.toPrimeFlagBudgetFamily.yzCost C =
       (PrimeFlagBudgetFamily.ofCongruentCut h
         Ured.toPrimeFlagBudgetFamily).yzCost C
     exact ht.2.1
   have hall:U.toPrimeFlagBudgetFamily.allCost C =
       (reducedBudgetFamily S hfirstProper hflagChar hmixed).allCost C:=by
     change U.toPrimeFlagBudgetFamily.allCost C =
       (PrimeFlagBudgetFamily.ofCongruentCut h
         Ured.toPrimeFlagBudgetFamily).allCost C
     exact ht.2.2
   exact ⟨hc.1.trans hz, hc.2.1.trans hyz, hc.2.2.trans hall⟩
 · have hfiber:RCN206.fiberFlag a b s = movingFiberFlag a b s:=rfl
   have hcut:RCN198.center a b s +
       (w + 1) • RCN206.surfaceFlag a b s = movingCutFlag a b s:=by
     change FlagDegree.mk
       ((0 + 2 * a) + (w + 1) * a)
       ((1 + (2 * b + 1)) + (w + 1) * (b + 1))
       ((0 + (2 * s + 3)) + (w + 1) * (s + 2)) =
       FlagDegree.mk
         (2 * a + (w + 1) * a)
         (2 * b + 2 + (w + 1) * (b + 1))
         (2 * s + 3 + (w + 1) * (s + 2))
     have hz:(0 + 2 * a) + (w + 1) * a =
         2 * a + (w + 1) * a:=by ring
     have hy:(1 + (2 * b + 1)) + (w + 1) * (b + 1) =
         2 * b + 2 + (w + 1) * (b + 1):=by ring
     have hall:(0 + (2 * s + 3)) + (w + 1) * (s + 2) =
         2 * s + 3 + (w + 1) * (s + 2):=by ring
     rw [hz, hy, hall]
   simpa only [hfiber, hcut] using hmove
theorem component_smallTail_moving_card_le
   {Gamma:Finset K} {flag:FlagDegree} {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
     prime errors flag w (RCN198.support a b s))
   (base:∀ C:FirstTailComponent S, SeparableLiteralCoordinate C.1)
   (M:∀ C:FirstTailComponent S,
     MovingPoleBudget C.1
       (regularitySurface (polynomialEmbedding K) S.F)
       (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
   (C:FirstTailComponent S) (delay multiplicity:ℕ)
   (hdelay:1 ≤ delay) (hdelayMu:delay ≤ multiplicity)
   (hmu:multiplicity ≤ 2)
   (hproper:globalTailCut (polynomialEmbedding K) S.F
     (w + 1 + delay) ∉ C.1) :
   (componentSeeds (GenericField K) S.G
     (globalTailCut (polynomialEmbedding K) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F) Gamma
     (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
       multiplicity * (M C).weightedCost (rationalFlag a b s) +
         (w + 2) * (M C).movingCost:=by
 let phi:=polynomialEmbedding K
 let T1:=globalTailCut phi S.F (w + 1)
 let H:=surfaceMap phi (polyH K S.F)
 let G0:=surfaceMap phi (polyG K S.F)
 let Hsupport:ResidualSupportData (RCN198.support a b s) S.F :=
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
 obtain ⟨coeffs, cflags, hcut, hcoeff, hclass⟩:=globalTailCut_certificate
   phi a b s S.F Hsupport.coordinate_bounds.2.1 Hsupport.ys_weight
     Hsupport.total_weight (w + delay) (by omega)
 have hd:w + 1 + delay = w + delay + 1:=by omega
 have hfiltered:filteredCut (w + delay) coeffs H G0 ∉ C.1:=by
   intro hmem
   apply hproper
   rw [hd, hcut]
   exact hmem
 have hzeroBudget:FiniteRegularZeroSetBound C.1 H
     (filteredCut (w + delay) coeffs H G0)
     ((M C).weightedCost (RCN206.centreFlag a b s) +
       (w + delay) * ((M C).weightedCost (RCN206.normalFlag a b s) +
         (M C).movingCost)):=by
   exact (M C).zero_le (base C) a b s (w + delay)
     (RCN206.centreFlag a b s) coeffs cflags
     (regularComponent_H_not_mem (GenericField K) S.G T1 H C)
     hfiltered hcoeff hclass
 let seeds:=componentSeeds (GenericField K) S.G T1 H Gamma
   (selectedPoint phi S.selected) C
 let points:=seeds.image (selectedPoint phi S.selected)
 have hpointsPrime:∀ v ∈ points,
     C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨gamma, hgamma, rfl⟩:=Finset.mem_image.mp hv
   exact componentSeeds_on_prime (GenericField K) S.G T1 H Gamma
     (selectedPoint phi S.selected) C gamma hgamma
 have hpointsRegular:∀ v ∈ points, MvPolynomial.aeval v H ≠ 0:=by
   intro v hv
   obtain ⟨gamma, hgamma, rfl⟩:=Finset.mem_image.mp hv
   have hGamma:=componentSeeds_subset (GenericField K) S.G T1 H Gamma
     (selectedPoint phi S.selected) C hgamma
   change MvPolynomial.eval (selectedPoint phi S.selected gamma)
     (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) S.F)) ≠ 0
   rw [selectedPoint_evaluation]
   exact S.regular gamma hGamma
 have hpointsZero:∀ v ∈ points,
     MvPolynomial.aeval v (filteredCut (w + delay) coeffs H G0) = 0:=by
   intro v hv
   obtain ⟨gamma, hgamma, rfl⟩:=Finset.mem_image.mp hv
   have hGamma:=componentSeeds_subset (GenericField K) S.G T1 H Gamma
     (selectedPoint phi S.selected) C hgamma
   rw [← hcut]
   exact selected_globalTailCut_zero_of_lt phi S.F S.selected gamma w
     (w + delay + 1) (S.degree_le gamma hGamma) (S.solution gamma hGamma)
     (by omega)
 have hbound:=hzeroBudget points hpointsPrime hpointsRegular hpointsZero
 have hcard:points.card = seeds.card :=
   Finset.card_image_of_injective _ (selectedPoint_injective phi S.selected)
 have hcost :
     (M C).weightedCost (RCN206.centreFlag a b s) +
         (w + delay) * ((M C).weightedCost (RCN206.normalFlag a b s) +
           (M C).movingCost) ≤
       multiplicity * (M C).weightedCost (rationalFlag a b s) +
         (w + 2) * (M C).movingCost:=by
   have hrational :
       (M C).weightedCost (rationalFlag a b s) =
         (M C).weightedCost (RCN206.centreFlag a b s) +
           (w + 1) * (M C).weightedCost (RCN206.normalFlag a b s) +
           (w + 1) * (M C).yzCost:=by
     simp only [MovingPoleBudget.weightedCost, RCN206.centreFlag,
       RCN206.directionFlag, RCN206.normalFlag, rationalFlag,
       add_zOnly, add_yz, add_all, unitYZFlag]
     ring
   rw [hrational]
   have hdelayTwo:delay ≤ 2:=hdelayMu.trans hmu
   interval_cases delay <;> interval_cases multiplicity <;>
     simp only [Nat.mul_add] <;> nlinarith
 simpa only [seeds, hcard, H, regularitySurface, polyH, phi] using
   hbound.trans hcost
theorem stage_card_le_hybrid
   {Gamma:Finset K} {flag:FlagDegree} {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
     prime errors flag w (RCN198.support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < prime ∧ flag.all < prime ∧
     flag.zOnly + flag.yz + flag.all < prime)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < prime)
   (hs:7 ≤ s)
   (base:∀ C:FirstTailComponent S, SeparableLiteralCoordinate C.1)
   (M:∀ C:FirstTailComponent S,
     MovingPoleBudget C.1
       (regularitySurface (polynomialEmbedding K) S.F)
       (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
   (hcost:∀ C,
     (M C).zCost = (reducedBudgetFamily S hfirstProper hflagChar hmixed).zCost C ∧
     (M C).yzCost = (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C ∧
     (M C).allCost = (reducedBudgetFamily S hfirstProper hflagChar hmixed).allCost C)
   (hmoving:(∑ C, (M C).movingCost) ≤
     flagMixed flag (movingFiberFlag a b s) (movingCutFlag a b s))
   (resultants:RegularComponentWeightedInertiaResultantCertificate
     (reducedBudgetFamily S hfirstProper hflagChar hmixed)
     (reducedMultiplicityGeneral S hfirstProper))
   (hnodes:S.nodes.card = agreements + errors)
   (hagreement:∀ gamma ∈ Gamma,
     agreements ≤ (S.agreementFiber gamma).card)
   (hbox:S.F ∈ RCN174.globalCoefficientBox K weightedCap w
     (a + b + s + 3) (s + 2)) :
   Gamma.card ≤ hybridStageCost flag a b s:=by
 let multiplicity:FirstTailComponent S → ℕ :=
   reducedMultiplicityGeneral S hfirstProper
 let B:=reducedBudgetFamily S hfirstProper hflagChar hmixed
 let T1:=globalTailCut (polynomialEmbedding K) S.F (w + 1)
 let H:=regularitySurface (polynomialEmbedding K) S.F
 let point:=selectedPoint (polynomialEmbedding K) S.selected
 let cost:FirstTailComponent S → ℕ:=fun C =>
   multiplicity C * B.weightedCost (rationalFlag a b s) C +
     if multiplicity C ≤ 2 then (w + 2) * (M C).movingCost else 0
 have hone:∀ C, 1 ≤ multiplicity C:=by
   exact loosenStageGeneral_one_le_localMultiplicity S hfirstProper
 have tangentCount (C:FirstTailComponent S)
     (hall:∀ delay, globalTailCut (polynomialEmbedding K) S.F
       (w + 1 + delay) ∈ C.1) :
     (componentSeeds (GenericField K) S.G T1 H Gamma point C).card ≤
       (errors + 1) * B.yzCost C:=by
   exact tangent_component_card_le S C hfirstProper (base C)
     agreements weightedCap (a + b + s + 3) (s + 2)
     hnodes hagreement (by norm_num [agreements, w]) (by norm_num [w])
     (by norm_num [w, weightedCap]) (by norm_num [weightedCap, prime])
     hbox B
     (reducedBudgetFamily_yzPositive S hfirstProper hflagChar hmixed C)
     hall (reducedBudgetFamily_yzPole S hfirstProper hflagChar hmixed C)
 have componentBound (C:FirstTailComponent S) :
     (componentSeeds (GenericField K) S.G T1 H Gamma point C).card ≤ cost C:=by
   have hd:=local_order_tail_dichotomy (loosenStageGeneral S)
     (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C hfirstProper
   rcases hd.2 with hproper | htangent
   · obtain ⟨delay, hdelay, hdelayMu, hproperTail⟩:=hproper
     change delay ≤ multiplicity C at hdelayMu
     by_cases hmu:multiplicity C ≤ 2
     · have hm:=component_smallTail_moving_card_le S base M C delay
         (multiplicity C) hdelay hdelayMu hmu hproperTail
       have hcoordinate :
           (M C).weightedCost (rationalFlag a b s) =
             B.weightedCost (rationalFlag a b s) C:=by
         simp only [MovingPoleBudget.weightedCost,
           PrimeFlagBudgetFamily.weightedCost, B,
           (hcost C).1, (hcost C).2.1, (hcost C).2.2]
       rw [hcoordinate] at hm
       rw [show cost C =
           multiplicity C * B.weightedCost (rationalFlag a b s) C +
             (w + 2) * (M C).movingCost by simp [cost, hmu]]
       simpa only [T1, H, point] using hm
     · have hmuThree:3 ≤ multiplicity C:=by omega
       have hflag:=laterTail_in_rationalFlag S delay (multiplicity C)
         hs hdelay hdelayMu hmuThree
       have hzero:∀ gamma ∈
           componentSeeds (GenericField K) S.G T1 H Gamma point C,
           MvPolynomial.aeval (point gamma)
             (globalTailCut (polynomialEmbedding K) S.F
               (w + 1 + delay)) = 0:=by
         intro gamma hgamma
         have hGamma:=componentSeeds_subset (GenericField K) S.G T1 H
           Gamma point C hgamma
         exact selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F
           S.selected gamma w (w + 1 + delay) (S.degree_le gamma hGamma)
             (S.solution gamma hGamma) (by omega)
       have hc:=component_secondTail_card_le B C Gamma point
         (selectedPoint_injective (polynomialEmbedding K) S.selected)
         hflag hproperTail hzero
       have hscale:B.weightedCost
           (multiplicity C • rationalFlag a b s) C =
             multiplicity C * B.weightedCost (rationalFlag a b s) C:=by
         simp only [PrimeFlagBudgetFamily.weightedCost, nsmul_zOnly,
           nsmul_yz, nsmul_all]
         ring
       rw [hscale] at hc
       rw [show cost C =
           multiplicity C * B.weightedCost (rationalFlag a b s) C by
         simp [cost, hmu]]
       simpa only [T1, H, point, w, RCN327.w] using hc
   · have ht:=tangentCount C htangent
     have hrat:errors + 1 ≤ (rationalFlag a b s).yz:=by
       dsimp [rationalFlag, errors, w]
       omega
     have hfactor:errors + 1 ≤
         multiplicity C * (rationalFlag a b s).yz:=by
       calc
         errors + 1 ≤ 1 * (rationalFlag a b s).yz:=by simpa using hrat
         _ ≤ multiplicity C * (rationalFlag a b s).yz :=
           Nat.mul_le_mul_right _ (hone C)
     have hscaled:(errors + 1) * B.yzCost C ≤
         (multiplicity C * (rationalFlag a b s).yz) * B.yzCost C :=
       Nat.mul_le_mul_right _ hfactor
     have hinside:(rationalFlag a b s).yz * B.yzCost C ≤
         B.weightedCost (rationalFlag a b s) C:=by
       simp only [PrimeFlagBudgetFamily.weightedCost]
       omega
     have hfinal :
         (multiplicity C * (rationalFlag a b s).yz) * B.yzCost C ≤
           multiplicity C * B.weightedCost (rationalFlag a b s) C:=by
       calc
         _ = multiplicity C *
             ((rationalFlag a b s).yz * B.yzCost C):=by ring
         _ ≤ _:=Nat.mul_le_mul_left _ hinside
     exact (ht.trans (hscaled.trans hfinal)).trans (Nat.le_add_right _ _)
 have hG:∀ gamma ∈ Gamma, MvPolynomial.eval (point gamma) S.G = 0 :=
   S.on_component
 have hT1:∀ gamma ∈ Gamma, MvPolynomial.eval (point gamma) T1 = 0:=by
   intro gamma hgamma
   exact selected_globalTailCut_zero (polynomialEmbedding K) S.F S.selected
     gamma w (S.degree_le gamma hgamma) (S.solution gamma hgamma)
 have hH:∀ gamma ∈ Gamma, MvPolynomial.eval (point gamma) H ≠ 0:=by
   intro gamma hgamma
   change MvPolynomial.eval (point gamma)
     (surfaceMap (polynomialEmbedding K)
       (MvPolynomial.pderiv (2:Fin 4) S.F)) ≠ 0
   rw [selectedPoint_evaluation]
   exact S.regular gamma hgamma
 have hcover:=card_le_sum_componentSeeds (GenericField K) S.G T1 H
   Gamma point hG hT1 hH
 have hcoordinate :
     (∑ C, multiplicity C * B.weightedCost (rationalFlag a b s) C) ≤
       flagMixed flag (firstTail a b s) (rationalFlag a b s):=by
   exact resultants.divisor_le B multiplicity
 have hmovingPart :
     (∑ C, if multiplicity C ≤ 2 then
         (w + 2) * (M C).movingCost else 0) ≤
       (w + 2) * flagMixed flag
         (movingFiberFlag a b s) (movingCutFlag a b s):=by
   calc
     _ ≤ ∑ C, (w + 2) * (M C).movingCost:=by
       apply Finset.sum_le_sum
       intro C _
       split_ifs <;> omega
     _ = (w + 2) * (∑ C, (M C).movingCost):=by
       rw [Finset.mul_sum]
     _ ≤ _:=Nat.mul_le_mul_left _ hmoving
 calc
   Gamma.card ≤ ∑ C:FirstTailComponent S,
       (componentSeeds (GenericField K) S.G T1 H Gamma point C).card:=hcover
   _ ≤ ∑ C:FirstTailComponent S, cost C :=
     Finset.sum_le_sum (fun C _ ↦ componentBound C)
   _ = (∑ C, multiplicity C * B.weightedCost (rationalFlag a b s) C) +
       ∑ C, if multiplicity C ≤ 2 then
         (w + 2) * (M C).movingCost else 0:=by
     simp only [cost, Finset.sum_add_distrib]
   _ ≤ flagMixed flag (firstTail a b s) (rationalFlag a b s) +
       (w + 2) * flagMixed flag
         (movingFiberFlag a b s) (movingCutFlag a b s) :=
     Nat.add_le_add hcoordinate hmovingPart
   _ = hybridStageCost flag a b s:=rfl
theorem flag_characteristic (a b s:ℕ) (flag:FlagDegree)
   (hS:s + 2 ≤ 13) (hY:b + s + 3 ≤ 62) (hT:a + b + s + 3 ≤ 1495)
   (hflag:flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
     flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
   flag.yz + flag.all < prime ∧ flag.all < prime ∧
     flag.zOnly + flag.yz + flag.all < prime:=by
 dsimp [prime]
 omega
theorem identity_mixed_gate (b s:ℕ) (flag:FlagDegree)
   (hS:s + 2 ≤ 13) (hY:b + s + 3 ≤ 62)
   (hfs:flag.all ≤ s + 2) (hfy:flag.yz + flag.all ≤ b + s + 3) :
   (1 + w * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 1) * w) < prime:=by
 have hy:2 * (b + s + 3) - 2 ≤ 122:=by omega
 have hs:2 * (s + 2) - 1 ≤ 25:=by omega
 have hfS:flag.all ≤ 13:=hfs.trans hS
 have hfY:flag.yz + flag.all ≤ 62:=hfy.trans hY
 calc
   _ ≤ (1 + w * 122) * 13 + 62 * (25 * w) :=
     Nat.add_le_add
       (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left w hy) 1) hfS)
       (Nat.mul_le_mul hfY (Nat.mul_le_mul_right w hs))
   _ < prime:=by norm_num [w, prime]
theorem provider_mixed_gate (b s:ℕ) (flag:FlagDegree)
   (hS:s + 2 ≤ 13) (hY:b + s + 3 ≤ 62)
   (hfs:flag.all ≤ s + 2) (hfy:flag.yz + flag.all ≤ b + s + 3) :
   (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < prime:=by
 have hy:2 * (b + s + 3) - 2 ≤ 122:=by omega
 have hs:2 * (s + 2) - 2 ≤ 24:=by omega
 have hfS:flag.all ≤ 13:=hfs.trans hS
 have hfY:flag.yz + flag.all ≤ 62:=hfy.trans hY
 calc
   _ ≤ (1 + (w + 1) * 122) * 13 + 62 * (24 * (w + 1)) :=
     Nat.add_le_add
       (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left (w + 1) hy) 1) hfS)
       (Nat.mul_le_mul hfY (Nat.mul_le_mul_right (w + 1) hs))
   _ < prime:=by norm_num [w, prime]
def FixedStageBound (a b s:ℕ):Prop :=
 ∀ {Gamma:Finset K} {flag:FlagDegree},
   (S:ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
     prime errors flag w (RCN198.support a b s)) →
   S.nodes.card = agreements + errors →
   (∀ gamma ∈ Gamma, agreements ≤ (S.agreementFiber gamma).card) →
   S.F ∈ RCN174.globalCoefficientBox K weightedCap w (a + b + s + 3) (s + 2) →
   (flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
     flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) →
   Gamma.card ≤ flagMixed flag (firstTail a b s) (secondTail a b s)
theorem fixedStageBound (a b s:ℕ)
   (hS:s + 2 ≤ 13) (hY:b + s + 3 ≤ 62) (hT:a + b + s + 3 ≤ 1495) :
   FixedStageBound a b s:=by
 intro Gamma flag S hnodes hagreement hbox hflag
 have hflagChar:=flag_characteristic a b s flag hS hY hT hflag
 by_cases hTail:S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)
 · have hTailNumerator:S.G ∣ surfaceMap (polynomialEmbedding K)
       (numerator K S.F (w + 1)) :=
     (globalTailCut_dvd_iff (polynomialEmbedding K)
       (polynomialEmbedding_injective K) S.F (w + 1) S.G).mp hTail
   have hprovider:=actual_identityCurveCountProvider S agreements hnodes
     hagreement (by norm_num [agreements, w]) hTailNumerator
     weightedCap (a + b + s + 3) (s + 2)
     (by norm_num [w]) (by norm_num [w, weightedCap])
     (by norm_num [weightedCap, prime]) hbox hflagChar
     (identity_mixed_gate b s flag hS hY hflag.1 hflag.2.1)
   have hpositive:1 ≤ identityCurveDegree flag a b s w:=by
     apply identity_positive
     have hy:0 < S.G.degreeOf 1:=S.y_dependent
     have hdeg:=degreeOf_le_flag_total S.G flag S.flag_support 1
     omega
   have hinc:=identity_surface_seed_bound S agreements
     (identityCurveDegree flag a b s w) hprovider hagreement
     (by norm_num [agreements, w])
     (by rw [hnodes] <;> norm_num [agreements, errors]) hpositive
   have hscaled:Gamma.card * gap ≤
       gap * flagMixed flag (firstTail a b s) (secondTail a b s):=by
     calc
       Gamma.card * gap = Gamma.card * (agreements - w):=rfl
       _ ≤ (S.nodes.card - w) * (errors + 1) *
           identityCurveDegree flag a b s w:=hinc
       _ = (n - w) * (errors + 1) * identityCurveDegree flag a b s w:=by
         rw [hnodes] <;> norm_num [n, agreements, errors]
       _ ≤ gap * flagMixed flag (firstTail a b s) (secondTail a b s) :=
         identity_budget flag a b s
   apply Nat.le_of_mul_le_mul_right ?_ (by norm_num [gap]:0 < gap)
   simpa only [Nat.mul_comm] using hscaled
 · have hprovider:=exists_delayedTailMultiplicityProvider_of_reducedGeneral
     (stageErrorCap:=errors) agreements S hTail hflagChar
     (provider_mixed_gate b s flag hS hY hflag.1 hflag.2.1)
     weightedCap (a + b + s + 3) (s + 2) hnodes hagreement
     (by norm_num [RCN327.w, agreements]) (by norm_num [RCN327.w, weightedCap])
     (by norm_num [weightedCap, prime]) hbox (tangent_gate a b s)
   exact stage_card_le_flagMixed S hprovider.some
def HybridStageBound (a b s:ℕ):Prop :=
 ∀ {Gamma:Finset K} {flag:FlagDegree},
   (S:ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
     prime errors flag w (RCN198.support a b s)) →
   S.nodes.card = agreements + errors →
   (∀ gamma ∈ Gamma, agreements ≤ (S.agreementFiber gamma).card) →
   S.F ∈ RCN174.globalCoefficientBox K weightedCap w
     (a + b + s + 3) (s + 2) →
   (flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
     flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) →
   Gamma.card ≤ hybridStageCost flag a b s
theorem hybridStageBound (a b s:ℕ) (hs:7 ≤ s)
   (hS:s + 2 ≤ 13) (hY:b + s + 3 ≤ 62)
   (hT:a + b + s + 3 ≤ 1495):HybridStageBound a b s:=by
 intro Gamma flag S hnodes hagreement hbox hflag
 have hflagChar:=flag_characteristic a b s flag hS hY hT hflag
 by_cases hTail:S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)
 · have hTailNumerator:S.G ∣ surfaceMap (polynomialEmbedding K)
       (numerator K S.F (w + 1)) :=
     (globalTailCut_dvd_iff (polynomialEmbedding K)
       (polynomialEmbedding_injective K) S.F (w + 1) S.G).mp hTail
   have hprovider:=actual_identityCurveCountProvider S agreements hnodes
     hagreement (by norm_num [agreements, w]) hTailNumerator
     weightedCap (a + b + s + 3) (s + 2)
     (by norm_num [w]) (by norm_num [w, weightedCap])
     (by norm_num [weightedCap, prime]) hbox hflagChar
     (identity_mixed_gate b s flag hS hY hflag.1 hflag.2.1)
   have hpositive:1 ≤ identityCurveDegree flag a b s w:=by
     apply identity_positive
     have hy:0 < S.G.degreeOf 1:=S.y_dependent
     have hdeg:=degreeOf_le_flag_total S.G flag S.flag_support 1
     omega
   have hinc:=identity_surface_seed_bound S agreements
     (identityCurveDegree flag a b s w) hprovider hagreement
     (by norm_num [agreements, w])
     (by rw [hnodes] <;> norm_num [agreements, errors]) hpositive
   have hscaled:Gamma.card * gap ≤
       gap * hybridStageCost flag a b s:=by
     calc
       Gamma.card * gap = Gamma.card * (agreements - w):=rfl
       _ ≤ (S.nodes.card - w) * (errors + 1) *
           identityCurveDegree flag a b s w:=hinc
       _ = (n - w) * (errors + 1) * identityCurveDegree flag a b s w:=by
         rw [hnodes] <;> norm_num [n, agreements, errors]
       _ ≤ gap * hybridStageCost flag a b s :=
         identity_budget_hybrid flag a b s
   apply Nat.le_of_mul_le_mul_right ?_ (by norm_num [gap]:0 < gap)
   simpa only [Nat.mul_comm] using hscaled
 · have hmixed:=provider_mixed_gate b s flag hS hY hflag.1 hflag.2.1
   have hmix :
       2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) < prime:=by
     calc
       _ ≤ 2 * 1495 * 1496:=by
         exact Nat.mul_le_mul
           (Nat.mul_le_mul_left 2 (hflag.2.2.trans hT))
           (by omega)
       _ < prime:=by norm_num [prime]
   obtain ⟨base, M, hcost, hmoving⟩ :=
     exists_movingBudgets S hTail hflagChar hmixed hmix
   exact stage_card_le_hybrid S hTail hflagChar hmixed hs base M hcost hmoving
     (transportedWeightedResultantsGeneral S hTail hflagChar hmixed)
     hnodes hagreement hbox
end
end ProximityPrize.SubmissionLower.LocatorFixedStage
