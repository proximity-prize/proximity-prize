import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BF
import ProximityPrize.SubmissionLower.Q2
import ProximityPrize.SubmissionLower.EQ
import ProximityPrize.SubmissionLower.J3
import ProximityPrize.SubmissionLower.LocatorFactorAggregate

/- Factor-adapted stage count for the 80201-error row.
   Both counting branches below use existing counting theorems; no independent
   seed-count assumption or ProtocolClaim is introduced. -/
namespace ProximityPrize.SubmissionLower.LocatorFixedStage
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open Polynomial KaehlerDifferential
open RCN135 RCN136 RCN174
open RCN159 RCN086
open RCN095 RCN275
open RCN198 RCN263
open RCN146 RCN087
open RCN203 RCN084
open RCN313 RCN074
open RCN335
open RCN287 RCN199 RCN206
open RCN001 RCN002 RCN003 RCN005
open RCN037 RCN038 RCN040 RCN041 RCN042
open RCN088 RCN314 RCN315
open RCN231 RCN238 RCN243 RCN265 RCN274 RCN277 RCN319 RCN341
open RCN237 RCN295
open RCN244 RCN264 RCN312 RCN328 RCN330 RCN336
open RCN027 RCN031 RCN046 RCN207 RCN271 RCN331 RCN338 RCN344
open RCN029 RCN030 RCN085 RCN093

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000

def n : ℕ := 262144
def w : ℕ := 131071
def errors : ℕ := 80201
def agreements : ℕ := 181943
def gap : ℕ := 50872
def prime : ℕ := 2130706433
def weightedCap : ℕ := 8187435

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (GenericField K) := Classical.decEq _
local instance : CharP K prime := by
  simpa [prime, RCN223.prime] using
    RCN128.challenge_field_characteristic6600

def firstTail (a b s : ℕ) : FlagDegree :=
  reducedResidualAgreementFlag (RCN198.support a b s) (w + 1)
def secondTail (a b s : ℕ) : FlagDegree :=
  reducedResidualAgreementFlag (RCN198.support a b s) (w + 2)

def exactFirstTail (a b s : ℕ) : FlagDegree :=
  ⟨2 * a * (w + 1), 1 + (2 * b + 1) * (w + 1),
    (2 * s + 3) * (w + 1)⟩
def coreHybridSecondTail (a b s : ℕ) : FlagDegree :=
  ⟨a * 131074, 1 + (2 * b + 1) * 65537, (2 * s + 3) * 65537⟩
def hybridSecondTail (a b s : ℕ) : FlagDegree :=
  ⟨a * 131074, errors + 1 + 2 * b * 65537, (2 * s + 3) * 65537⟩
def rationalCoordinate (a b s : ℕ) : FlagDegree :=
  RCN206.centreFlag a b s + (w + 1) • RCN206.normalFlag a b s
def movingFiber (a b s : ℕ) : FlagDegree := RCN206.fiberFlag a b s
def movingCut (a b s : ℕ) : FlagDegree :=
  RCN198.center a b s + (w + 1) • RCN206.surfaceFlag a b s
def hybridStageCost (flag : FlagDegree) (a b s : ℕ) : ℕ :=
  flagMixed flag (exactFirstTail a b s) (hybridSecondTail a b s) +
    (w + 1) * flagMixed flag (movingFiber a b s) (movingCut a b s)
def coreHybridStageCost (flag : FlagDegree) (a b s : ℕ) : ℕ :=
  flagMixed flag (exactFirstTail a b s) (coreHybridSecondTail a b s) +
    (w + 1) * flagMixed flag (movingFiber a b s) (movingCut a b s)

theorem row_values :
    agreements + errors = n ∧ agreements - w = gap ∧
    weightedCap = 45 * agreements ∧ w < agreements ∧
    w + 1 ≤ weightedCap ∧ weightedCap < prime := by
  norm_num [agreements, errors, n, w, gap, weightedCap, prime]

theorem tail_support_formula (a b s d : ℕ) :
    reducedResidualAgreementFlag (RCN198.support a b s) d =
      ⟨2 * a * d, 1 + 2 * (b + 1) * d, 2 * (s + 1) * d⟩ := by
  have ht : a + b + s + 3 - (b + s + 3) = a := by omega
  have hy : b + s + 3 - (s + 2) = b + 1 := by omega
  have hs : 2 * (s + 2) - 2 = 2 * (s + 1) := by omega
  simp only [reducedResidualAgreementFlag, reducedAgreementDirection, RCN198.support]
  rw [ht, hy, hs]

/- The identity degree is linear in the actual first flag. -/
theorem identityDegree_linear (flag : FlagDegree) (a b s : ℕ) :
    identityCurveDegree flag a b s w =
      flag.zOnly * (393219 + 262146 * s) +
      flag.yz * (786438 + 524292 * s) +
      flag.all * (1048586 + 262146 * a + 524292 * b + 524292 * s) := by
  simp only [identityCurveDegree, paddedCut,
    RCN206.centreFlag,
    RCN206.directionFlag,
    flagMixed, unitZFlag, unitYZFlag, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all, w]
  ring

def hybridSlackZ (b s : ℕ) : ℕ :=
  12035132012537930 + 9613857382203392 * b +
    10354066163964636 * s + 2621962922754048 * s ^ 2 +
    5243925845508096 * b * s
def hybridSlackYZ (a b s : ℕ) : ℕ :=
  7901489333992556 + 9613857382203392 * a +
    9613857382203392 * b + 7598304378267720 * s +
    2621962922754048 * s ^ 2 + 5243925845508096 * a * s +
    5243925845508096 * b * s
def hybridSlackAll (a b s : ℕ) : ℕ :=
  6456697986983092 + 10354066163964636 * a +
    7598304378267720 * b + 2621962922754048 * b ^ 2 +
    7598304378267720 * s + 2621962922754048 * s ^ 2 +
    5243925845508096 * a * b + 5243925845508096 * a * s +
    5243925845508096 * b * s
def hybridSlack (flag : FlagDegree) (a b s : ℕ) : ℕ :=
  flag.zOnly * hybridSlackZ b s + flag.yz * hybridSlackYZ a b s +
    flag.all * hybridSlackAll a b s

theorem identity_hybrid_budget_exact (flag : FlagDegree) (a b s : ℕ) :
    gap * coreHybridStageCost flag a b s =
      (n - w) * (errors + 1) * identityCurveDegree flag a b s w +
        hybridSlack flag a b s := by
  rw [identityDegree_linear]
  norm_num [coreHybridStageCost, exactFirstTail, coreHybridSecondTail,
    rationalCoordinate, movingFiber, movingCut, hybridSlack, hybridSlackZ,
    hybridSlackYZ, hybridSlackAll, RCN198.center, RCN198.direction,
    RCN206.centreFlag, RCN206.normalFlag,
    RCN206.fiberFlag, RCN206.surfaceFlag, RCN206.directionFlag,
    w, n, errors, gap, flagMixed, unitYZFlag, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all]
  ring

theorem identity_hybrid_budget (flag : FlagDegree) (a b s : ℕ) :
    (n - w) * (errors + 1) * identityCurveDegree flag a b s w ≤
      gap * hybridStageCost flag a b s := by
  have hcore : (n - w) * (errors + 1) * identityCurveDegree flag a b s w ≤
      gap * coreHybridStageCost flag a b s := by
    rw [identity_hybrid_budget_exact]
    exact Nat.le_add_right _ _
  apply hcore.trans
  apply Nat.mul_le_mul_left
  unfold coreHybridStageCost hybridStageCost
  apply Nat.add_le_add_right
  apply LocatorFactorAggregate.mixed_mono_third
  constructor <;> dsimp [LocatorFactorAggregate.middle,
    LocatorFactorAggregate.total, coreHybridSecondTail, hybridSecondTail,
    errors] <;> omega

theorem identity_positive (flag : FlagDegree) (a b s : ℕ)
    (hpos : 0 < flag.zOnly + flag.yz + flag.all) :
    1 ≤ identityCurveDegree flag a b s w := by
  rw [identityDegree_linear]
  have hz := Nat.mul_le_mul_left flag.zOnly
    (show 1 ≤ 393219 + 262146 * s by omega)
  have hy := Nat.mul_le_mul_left flag.yz
    (show 1 ≤ 786438 + 524292 * s by omega)
  have ha := Nat.mul_le_mul_left flag.all
    (show 1 ≤ 1048586 + 262146 * a + 524292 * b + 524292 * s by omega)
  simp only [Nat.mul_one] at hz hy ha
  omega

theorem tangent_gate (a b s : ℕ) :
    errors + 1 ≤ (secondTail a b s).yz := by
  rw [secondTail, tail_support_formula]
  change errors + 1 ≤ 1 + 2 * (b + 1) * (w + 2)
  have hb : 2 * (w + 2) ≤ 2 * (b + 1) * (w + 2) := by
    have h := Nat.mul_le_mul_right (w + 2)
      (Nat.mul_le_mul_left 2 (show 1 ≤ b + 1 by omega))
    simpa only [Nat.mul_one] using h
  exact (by norm_num [errors, w] : errors + 1 ≤ 1 + 2 * (w + 2)).trans
    (Nat.add_le_add_left hb 1)

theorem flag_characteristic (a b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 13) (hY : b + s + 3 ≤ 62) (hT : a + b + s + 3 ≤ 1510)
    (hflag : flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) :
    flag.yz + flag.all < prime ∧ flag.all < prime ∧
      flag.zOnly + flag.yz + flag.all < prime := by
  dsimp [prime]
  omega

theorem identity_mixed_gate (b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 13) (hY : b + s + 3 ≤ 62)
    (hfs : flag.all ≤ s + 2) (hfy : flag.yz + flag.all ≤ b + s + 3) :
    (1 + w * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * w) < prime := by
  have hy : 2 * (b + s + 3) - 2 ≤ 122 := by omega
  have hs : 2 * (s + 2) - 1 ≤ 25 := by omega
  have hfS : flag.all ≤ 13 := hfs.trans hS
  have hfY : flag.yz + flag.all ≤ 62 := hfy.trans hY
  calc
    _ ≤ (1 + w * 122) * 13 + 62 * (25 * w) :=
      Nat.add_le_add
        (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left w hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right w hs))
    _ < prime := by norm_num [w, prime]

theorem provider_mixed_gate (b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 13) (hY : b + s + 3 ≤ 62)
    (hfs : flag.all ≤ s + 2) (hfy : flag.yz + flag.all ≤ b + s + 3) :
    (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < prime := by
  have hy : 2 * (b + s + 3) - 2 ≤ 122 := by omega
  have hs : 2 * (s + 2) - 2 ≤ 24 := by omega
  have hfS : flag.all ≤ 13 := hfs.trans hS
  have hfY : flag.yz + flag.all ≤ 62 := hfy.trans hY
  calc
    _ ≤ (1 + (w + 1) * 122) * 13 + 62 * (24 * (w + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul (Nat.add_le_add_left (Nat.mul_le_mul_left (w + 1) hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right (w + 1) hs))
    _ < prime := by norm_num [w, prime]

theorem active_mixed_gate (b s : ℕ) (flag : FlagDegree)
    (hS : s + 2 ≤ 13) (hY : b + s + 3 ≤ 62)
    (hfs : flag.all ≤ s + 2) (hfy : flag.yz + flag.all ≤ b + s + 3) :
    (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * (w + 1)) < prime := by
  have hy : 2 * (b + s + 3) - 2 ≤ 122 := by omega
  have hs : 2 * (s + 2) - 1 ≤ 25 := by omega
  have hfS : flag.all ≤ 13 := hfs.trans hS
  have hfY : flag.yz + flag.all ≤ 62 := hfy.trans hY
  calc
    _ ≤ (1 + (w + 1) * 122) * 13 + 62 * (25 * (w + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul
          (Nat.add_le_add_left (Nat.mul_le_mul_left (w + 1) hy) 1) hfS)
        (Nat.mul_le_mul hfY (Nat.mul_le_mul_right (w + 1) hs))
    _ < prime := by norm_num [w, prime]

theorem exists_firstTail_activeData
    {Gamma : Finset K} {flag : FlagDegree} {a b s : ℕ}
    (S : ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
      prime errors flag w (RCN198.support a b s))
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
    (hflagChar : flag.yz + flag.all < prime ∧ flag.all < prime ∧
      flag.zOnly + flag.yz + flag.all < prime)
    (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 1) * (w + 1)) < prime) :
    ∃ (base : ∀ C : FirstTailComponent S, SeparableLiteralCoordinate C.1),
      ∃ (hactive : ∀ C : FirstTailComponent S,
          D (GenericField K) (CoordinateField (GenericField K) C.1)
              (coordinate (GenericField K) C.1 0) ≠ 0 ∨
            D (GenericField K) (CoordinateField (GenericField K) C.1)
              (coordinate (GenericField K) C.1 2) ≠ 0),
        ∃ (hZ : ∀ C : FirstTailComponent S, LiteralProjectionGate C 2),
          Nonempty (AdaptiveNestedProjectionDataActive base hactive
            (RCN315.residualStage_pderiv_one_ne_zero_of_support S)) := by
  classical
  let T := globalTailCut (polynomialEmbedding K) S.F (w + 1)
  let H := regularitySurface (polynomialEmbedding K) S.F
  let supp := RCN198.support a b s
  have hsy : supp.s < supp.ys := by
    change s + 2 < b + s + 3
    omega
  have hTflag : PolynomialInFlag
      (sharpResidualAgreementFlag supp (w + 1)) T :=
    RCN088.firstTail_in_sharp_flag S
  obtain ⟨hGY, hGS, hGZ⟩ := degree_bounds_of_polynomialInFlag S.flag_support
  obtain ⟨hTY, hTS, _⟩ := degree_bounds_of_polynomialInFlag hTflag
  have hTY' : T.degreeOf 0 ≤ 1 + (w + 1) * (2 * (b + s + 3) - 2) := by
    apply hTY.trans_eq
    exact sharpResidualAgreementFlag_ys supp hsy (w + 1)
  have hTS' : T.degreeOf 1 ≤ (2 * (s + 2) - 1) * (w + 1) := by
    apply hTS.trans_eq
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection, supp,
      RCN198.support]
  have hGdegree : ∀ j : Fin 3, S.G.degreeOf j < prime := by
    intro j
    fin_cases j
    · exact hGY.trans_lt hflagChar.1
    · exact hGS.trans_lt hflagChar.2.1
    · exact hGZ.trans_lt hflagChar.2.2
  have hmixedZ : coordinateMixedDegree (GenericField K) S.G T 2 < prime := by
    rw [coordinateMixedDegree_two]
    exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
      (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
  let choiceData : ∀ C : FirstTailComponent S,
      ∃ B : SeparableLiteralCoordinate C.1, B.index = 0 ∨ B.index = 2 :=
    fun C ↦ regularComponent_exists_separableLiteralCoordinate6630
      (polynomialEmbedding K) S.F S.G T prime S.G_dvd_surface S.irreducible_G
      hproper S.y_dependent hGdegree hmixedZ C
  let base : ∀ C : FirstTailComponent S, SeparableLiteralCoordinate C.1 :=
    fun C ↦ (choiceData C).choose
  have hbaseIndex : ∀ C : FirstTailComponent S,
      (base C).index = 0 ∨ (base C).index = 2 := by
    intro C
    exact (choiceData C).choose_spec
  have hactive : ∀ C : FirstTailComponent S,
      D (GenericField K) (CoordinateField (GenericField K) C.1)
          (coordinate (GenericField K) C.1 0) ≠ 0 ∨
        D (GenericField K) (CoordinateField (GenericField K) C.1)
          (coordinate (GenericField K) C.1 2) ≠ 0 := by
    intro C
    have hb := base_differential_ne_zero (base C)
    rcases hbaseIndex C with hidx | hidx
    · left
      simpa only [hidx] using hb
    · right
      simpa only [hidx] using hb
  have hZ : ∀ C : FirstTailComponent S, LiteralProjectionGate C 2 := by
    intro C htr
    exact finite_separable_at_of_original_coordinate_gate (GenericField K) C.1 2 htr
      prime S.G T S.irreducible_G
      (regularComponent_G_mem (GenericField K) S.G T H C)
      (regularComponent_T_mem (GenericField K) S.G T H C)
      hproper hGdegree hmixedZ
  exact ⟨base, hactive, hZ,
    exists_adaptiveNestedProjectionDataActive base hactive
      (RCN315.residualStage_pderiv_one_ne_zero_of_support S)⟩

theorem sharp_formula (a b s d : ℕ) :
    sharpResidualAgreementFlag (RCN198.support a b s) d =
      ⟨2 * a * d, 1 + (2 * b + 1) * d, (2 * s + 3) * d⟩ := by
  have ha : a + b + s + 3 - (b + s + 3) = a := by omega
  have hb : b + s + 3 - (s + 2) = b + 1 := by omega
  have hb2 : 2 * (b + 1) = 2 * b + 2 := by omega
  have hs : 2 * (s + 2) - 1 = 2 * s + 3 := by omega
  simp [sharpResidualAgreementFlag, sharpAgreementDirection,
    RCN198.support, ha, hb, hb2, hs]

theorem exactFirstTail_eq_sharp (a b s : ℕ) :
    exactFirstTail a b s =
      sharpResidualAgreementFlag (RCN198.support a b s) (w + 1) := by
  simpa only [exactFirstTail] using (sharp_formula a b s (w + 1)).symm

theorem firstTail_in_exact
    {Gamma : Finset K} {flag : FlagDegree} {a b s : ℕ}
    (S : Stage K I Gamma IRSProfile.domain prime flag errors
      (RCN198.support a b s)) :
    PolynomialInFlag (exactFirstTail a b s)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1)) := by
  rw [exactFirstTail_eq_sharp]
  exact surfaceMap_agreement_in_sharp_flag
    (P := RCN198.support a b s)
    (by change s + 2 < b + s + 3; omega) (polynomialEmbedding K)
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
    (w + 1) (tailSelector (w + 1)) 0 0 0

theorem laterTail_in_hybrid
    {Gamma : Finset K} {flag : FlagDegree} {a b s : ℕ}
    (S : Stage K I Gamma IRSProfile.domain prime flag errors
      (RCN198.support a b s))
    (delay multiplicity : ℕ) (hdelay : 1 ≤ delay)
    (hdelayMu : delay ≤ multiplicity) (hmu : 2 ≤ multiplicity) :
    PolynomialInFlag (multiplicity • hybridSecondTail a b s)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
  let d := w + 1 + delay
  have hsharp : PolynomialInFlag
      (sharpResidualAgreementFlag (RCN198.support a b s) d)
      (globalTailCut (polynomialEmbedding K) S.F d) := by
    exact surfaceMap_agreement_in_sharp_flag
      (P := RCN198.support a b s)
      (by change s + 2 < b + s + 3; omega) (polynomialEmbedding K)
      ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
      d (tailSelector d) 0 0 0
  intro exponent hexponent
  have hs := hsharp exponent hexponent
  change InFlag (multiplicity • hybridSecondTail a b s) exponent
  rw [sharp_formula] at hs
  dsimp [d] at hs
  norm_num [InFlag, w] at hs
  simp only [InFlag, hybridSecondTail, nsmul_zOnly, nsmul_yz, nsmul_all] at ⊢
  have hdscale : 131072 + delay ≤ multiplicity * 65537 := by omega
  have hsa : (2 * s + 3) * (131072 + delay) ≤
      multiplicity * ((2 * s + 3) * 65537) := by
    calc
      _ ≤ (2 * s + 3) * (multiplicity * 65537) :=
        Nat.mul_le_mul_left _ hdscale
      _ = _ := by ring
  have hy : (2 * b + 1) * (131072 + delay) ≤
      multiplicity * ((2 * b + 1) * 65537) := by
    calc
      _ ≤ (2 * b + 1) * (multiplicity * 65537) :=
        Nat.mul_le_mul_left _ hdscale
      _ = _ := by ring
  have hz : (2 * a) * (131072 + delay) ≤
      multiplicity * ((2 * a) * 65537) := by
    calc
      _ ≤ (2 * a) * (multiplicity * 65537) :=
        Nat.mul_le_mul_left _ hdscale
      _ = _ := by ring
  have hymu : multiplicity * (1 + (2 * b + 1) * 65537) ≤
      multiplicity * (errors + 1 + 2 * b * 65537) := by
    apply Nat.mul_le_mul_left
    norm_num [errors]
    omega
  have hyaug : 1 + (2 * b + 1) * (131072 + delay) ≤
      multiplicity * (errors + 1 + 2 * b * 65537) := by
    apply (show 1 + (2 * b + 1) * (131072 + delay) ≤
        multiplicity * (1 + (2 * b + 1) * 65537) by
      calc
        _ ≤ multiplicity + multiplicity * ((2 * b + 1) * 65537) :=
          Nat.add_le_add (by omega) hy
        _ = _ := by ring).trans
    exact hymu
  have hz' : 2 * a * (131072 + delay) ≤
      multiplicity * (a * 131074) := by
    calc
      _ ≤ multiplicity * (2 * a * 65537) := hz
      _ = _ := by ring
  omega

theorem component_secondTail_moving_card_le
    {Gamma : Finset K} {flag : FlagDegree} {a b s : ℕ}
    (S : Stage K I Gamma IRSProfile.domain prime flag errors
      (RCN198.support a b s))
    (base : ∀ C : FirstTailComponent S, SeparableLiteralCoordinate C.1)
    (M : ∀ C : FirstTailComponent S,
      MovingPoleBudget C.1
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (C : FirstTailComponent S)
    (hproper : globalTailCut (polynomialEmbedding K) S.F (w + 2) ∉ C.1) :
    (componentSeeds (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
        (M C).weightedCost (rationalCoordinate a b s) +
          (w + 1) * (M C).movingCost := by
  let phi := polynomialEmbedding K
  let T1 := globalTailCut phi S.F (w + 1)
  let T2 := globalTailCut phi S.F (w + 2)
  let H := regularitySurface phi S.F
  let G0 := surfaceMap phi (polyG K S.F)
  let Hsupport : ResidualSupportData (RCN198.support a b s) S.F :=
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
  obtain ⟨coeffs, cflags, hcut, hcoeff, hclass⟩ := globalTailCut_certificate
    phi a b s S.F Hsupport.coordinate_bounds.2.1 Hsupport.ys_weight
      Hsupport.total_weight (w + 1) (by decide)
  have hcutT : T2 = filteredCut (w + 1) coeffs H G0 := by
    simpa [T2, H, G0, regularitySurface, polyH,
      show w + 1 + 1 = w + 2 by omega] using hcut
  have hfiltered : filteredCut (w + 1) coeffs H G0 ∉ C.1 := by
    rwa [← hcutT]
  have hzeroBudget : FiniteRegularZeroSetBound C.1 H
      (filteredCut (w + 1) coeffs H G0)
      ((M C).weightedCost (RCN206.centreFlag a b s) +
        (w + 1) * ((M C).weightedCost (RCN206.normalFlag a b s) +
          (M C).movingCost)) := by
    exact (M C).zero_le (base C) a b s (w + 1)
      (RCN206.centreFlag a b s) coeffs cflags
      (regularComponent_H_not_mem (GenericField K) S.G T1 H C)
      hfiltered hcoeff hclass
  let seeds := componentSeeds (GenericField K) S.G T1 H Gamma
    (selectedPoint phi S.selected) C
  let points := seeds.image (selectedPoint phi S.selected)
  have hpointsPrime : ∀ v ∈ points,
      C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    exact componentSeeds_on_prime (GenericField K) S.G T1 H Gamma
      (selectedPoint phi S.selected) C gamma hgamma
  have hpointsRegular : ∀ v ∈ points, MvPolynomial.aeval v H ≠ 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    have hGamma := componentSeeds_subset (GenericField K) S.G T1 H Gamma
      (selectedPoint phi S.selected) C hgamma
    change MvPolynomial.eval (selectedPoint phi S.selected gamma)
      (surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) S.F)) ≠ 0
    rw [selectedPoint_evaluation]
    exact S.regular gamma hGamma
  have hpointsZero : ∀ v ∈ points,
      MvPolynomial.aeval v (filteredCut (w + 1) coeffs H G0) = 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    have hGamma := componentSeeds_subset (GenericField K) S.G T1 H Gamma
      (selectedPoint phi S.selected) C hgamma
    rw [← hcutT]
    exact selected_globalTailCut_zero_of_lt phi S.F S.selected gamma w (w + 2)
      (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
  have hbound := hzeroBudget points hpointsPrime hpointsRegular hpointsZero
  have hcard : points.card = seeds.card :=
    Finset.card_image_of_injective _ (selectedPoint_injective phi S.selected)
  have hcost :
      (M C).weightedCost (RCN206.centreFlag a b s) +
          (w + 1) * ((M C).weightedCost (RCN206.normalFlag a b s) +
            (M C).movingCost) =
        (M C).weightedCost (rationalCoordinate a b s) +
          (w + 1) * (M C).movingCost := by
    simp only [MovingPoleBudget.weightedCost, RCN206.centreFlag,
      RCN206.directionFlag, RCN206.normalFlag, rationalCoordinate,
      add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all,
      unitYZFlag, w]
    ring
  simpa only [seeds, hcard, hcost] using hbound

theorem stage_card_le_hybrid
    {Gamma : Finset K} {flag : FlagDegree} {a b s : ℕ}
    (S : Stage K I Gamma IRSProfile.domain prime flag errors
      (RCN198.support a b s))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
    (base : ∀ C : FirstTailComponent S, SeparableLiteralCoordinate C.1)
    (U : AdaptiveUnitProjectionFamily base flag
      (sharpResidualAgreementFlag (RCN198.support a b s) (w + 1)))
    (hyzTranscendental : ∀ C : FirstTailComponent S,
      Transcendental (GenericField K)
        (coordinateValue (GenericField K) (CoordinateField (GenericField K) C.1)
          (U.yzProjection C)))
    (M : ∀ C : FirstTailComponent S,
      MovingPoleBudget C.1
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (hcost : ∀ C, (M C).zCost = U.toPrimeFlagBudgetFamily.zCost C ∧
      (M C).yzCost = U.toPrimeFlagBudgetFamily.yzCost C ∧
      (M C).allCost = U.toPrimeFlagBudgetFamily.allCost C)
    (hmoving : (∑ C, (M C).movingCost) ≤
      flagMixed flag (movingFiber a b s) (movingCut a b s))
    (resultants : RegularComponentWeightedInertiaResultantCertificate
      U.toPrimeFlagBudgetFamily
        (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)))
    (hnodes : S.nodes.card = agreements + errors)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤ (S.agreementFiber gamma).card)
    (hbox : S.F ∈ globalCoefficientBox K weightedCap w
      (a + b + s + 3) (s + 2)) :
    Gamma.card ≤ hybridStageCost flag a b s := by
  let multiplicity : FirstTailComponent S → ℕ :=
    localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
  have hone : ∀ C, 1 ≤ multiplicity C := by
    exact one_le_localMultiplicity S hfirstProper
  let B := U.toPrimeFlagBudgetFamily
  let T1 := globalTailCut (polynomialEmbedding K) S.F (w + 1)
  let H := regularitySurface (polynomialEmbedding K) S.F
  let point := selectedPoint (polynomialEmbedding K) S.selected
  let cost : FirstTailComponent S → ℕ := fun C ↦
    multiplicity C * B.weightedCost (hybridSecondTail a b s) C +
      if multiplicity C = 1 then (w + 1) * (M C).movingCost else 0
  have hyzPositive (C : FirstTailComponent S) : 1 ≤ B.yzCost C := by
    change 1 ≤ coordinateDegree (GenericField K)
      (CoordinateField (GenericField K) C.1) (U.yzProjection C)
    exact one_le_coordinateDegree_of_transcendental_value
      (U.yzProjection C) (hyzTranscendental C)
  have hyzPole (C : FirstTailComponent S) : ∀ W : Finset
      (RCN346.Place (GenericField K) (CoordinateField (GenericField K) C.1)),
      (∑ v ∈ W, exponentSetPoleWeight v.val
        (coordinate (GenericField K) C.1) (flagSupport unitYZFlag)) ≤
          (B.yzCost C : ℤ) := by
    exact U.toAdaptiveUnitPoleBudget.yzPole C
  have tangentCount (C : FirstTailComponent S)
      (hall : ∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (w + 1 + delay) ∈ C.1) :
      (componentSeeds (GenericField K) S.G T1 H Gamma point C).card ≤
        (errors + 1) * B.yzCost C := by
    exact tangent_component_card_le S C hfirstProper (base C)
      agreements weightedCap (a + b + s + 3) (s + 2) hnodes hagreement
      (by norm_num [RCN326.w, agreements]) (by norm_num [RCN326.w])
      (by norm_num [RCN326.w, weightedCap]) (by norm_num [weightedCap, prime])
      hbox B (hyzPositive C) hall (hyzPole C)
  have componentBound (C : FirstTailComponent S) :
      (componentSeeds (GenericField K) S.G T1 H Gamma point C).card ≤ cost C := by
    have hd := local_order_tail_dichotomy S
      (canonicalLocalDVRFamily S hfirstProper) C hfirstProper
    rcases hd.2 with hproper | htangent
    · obtain ⟨delay, hdelay, hdelayMu, hproperTail⟩ := hproper
      have hproperTail' : globalTailCut (polynomialEmbedding K) S.F
          (w + 1 + delay) ∉ C.1 := by
        simpa [w, RCN326.w] using hproperTail
      change delay ≤ multiplicity C at hdelayMu
      by_cases hmu : multiplicity C = 1
      · have hdelayOne : delay = 1 := by omega
        subst delay
        have hm := component_secondTail_moving_card_le S base M C
          (by simpa [w] using hproperTail')
        have hcoordinate : (M C).weightedCost (rationalCoordinate a b s) ≤
            B.weightedCost (hybridSecondTail a b s) C := by
          have hzcoord : (rationalCoordinate a b s).zOnly ≤
              (hybridSecondTail a b s).zOnly := by
            simp [rationalCoordinate, hybridSecondTail, RCN206.centreFlag,
              RCN206.directionFlag, RCN206.normalFlag, unitYZFlag, w]
            omega
          have hycoord : (rationalCoordinate a b s).yz ≤
              (hybridSecondTail a b s).yz := by
            simp [rationalCoordinate, hybridSecondTail, RCN206.centreFlag,
              RCN206.directionFlag, RCN206.normalFlag, unitYZFlag, w, errors]
            omega
          have hacoord : (rationalCoordinate a b s).all ≤
              (hybridSecondTail a b s).all := by
            simp [rationalCoordinate, hybridSecondTail, RCN206.centreFlag,
              RCN206.directionFlag, RCN206.normalFlag, unitYZFlag, w]
            omega
          simp only [MovingPoleBudget.weightedCost,
            RCN237.PrimeFlagBudgetFamily.weightedCost,
            (hcost C).1, (hcost C).2.1, (hcost C).2.2]
          exact Nat.add_le_add
            (Nat.add_le_add (Nat.mul_le_mul_right _ hzcoord)
              (Nat.mul_le_mul_right _ hycoord))
            (Nat.mul_le_mul_right _ hacoord)
        have hm2 := hm.trans (Nat.add_le_add_right hcoordinate _)
        rw [show cost C = B.weightedCost (hybridSecondTail a b s) C +
            (w + 1) * (M C).movingCost by simp [cost, hmu]]
        simpa [T1, H, point] using hm2
      · have hmuTwo : 2 ≤ multiplicity C := by omega
        have hflag := laterTail_in_hybrid S delay (multiplicity C)
          hdelay hdelayMu hmuTwo
        have hzero : ∀ gamma ∈ componentSeeds (GenericField K) S.G T1 H Gamma point C,
            MvPolynomial.aeval (point gamma)
              (globalTailCut (polynomialEmbedding K) S.F
                (w + 1 + delay)) = 0 := by
          intro gamma hgamma
          have hGamma := componentSeeds_subset (GenericField K) S.G T1 H Gamma
            point C hgamma
          exact selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F
            S.selected gamma w (w + 1 + delay) (S.degree_le gamma hGamma)
              (S.solution gamma hGamma) (by omega)
        have hc := component_secondTail_card_le B C Gamma point
          (selectedPoint_injective (polynomialEmbedding K) S.selected)
          hflag hproperTail' hzero
        have hscale : B.weightedCost
            (multiplicity C • hybridSecondTail a b s) C =
              multiplicity C * B.weightedCost (hybridSecondTail a b s) C := by
          simp only [RCN237.PrimeFlagBudgetFamily.weightedCost, nsmul_zOnly,
            nsmul_yz, nsmul_all]
          ring
        rw [hscale] at hc
        rw [show cost C = multiplicity C *
            B.weightedCost (hybridSecondTail a b s) C by simp [cost, hmu]]
        simpa [T1, H, point, w, RCN326.w] using hc
    · have htangent' : ∀ delay, globalTailCut (polynomialEmbedding K) S.F
          (w + 1 + delay) ∈ C.1 := by
        intro delay
        simpa [w, RCN326.w] using htangent delay
      have ht := tangentCount C htangent'
      have hfactor : errors + 1 ≤
          multiplicity C * (hybridSecondTail a b s).yz := by
        have hgate : errors + 1 ≤ (hybridSecondTail a b s).yz := by
          simp only [hybridSecondTail]
          omega
        exact hgate.trans (by
          calc
            (hybridSecondTail a b s).yz =
                1 * (hybridSecondTail a b s).yz := by simp
            _ ≤ multiplicity C * (hybridSecondTail a b s).yz :=
              Nat.mul_le_mul_right _ (hone C))
      have hscaled : (errors + 1) * B.yzCost C ≤
          (multiplicity C * (hybridSecondTail a b s).yz) * B.yzCost C :=
        Nat.mul_le_mul_right _ hfactor
      have hinside : (hybridSecondTail a b s).yz * B.yzCost C ≤
          B.weightedCost (hybridSecondTail a b s) C := by
        simp only [RCN237.PrimeFlagBudgetFamily.weightedCost]
        omega
      have hfinal :
          (multiplicity C * (hybridSecondTail a b s).yz) * B.yzCost C ≤
            multiplicity C * B.weightedCost (hybridSecondTail a b s) C := by
        calc
          _ = multiplicity C *
              ((hybridSecondTail a b s).yz * B.yzCost C) := by ring
          _ ≤ _ := Nat.mul_le_mul_left _ hinside
      exact (ht.trans (hscaled.trans hfinal)).trans (Nat.le_add_right _ _)
  have hG : ∀ gamma ∈ Gamma, MvPolynomial.eval (point gamma) S.G = 0 :=
    S.on_component
  have hT1 : ∀ gamma ∈ Gamma, MvPolynomial.eval (point gamma) T1 = 0 := by
    intro gamma hgamma
    exact selected_globalTailCut_zero (polynomialEmbedding K) S.F S.selected gamma w
      (S.degree_le gamma hgamma) (S.solution gamma hgamma)
  have hH : ∀ gamma ∈ Gamma, MvPolynomial.eval (point gamma) H ≠ 0 := by
    intro gamma hgamma
    change MvPolynomial.eval (point gamma)
      (surfaceMap (polynomialEmbedding K)
        (MvPolynomial.pderiv (2 : Fin 4) S.F)) ≠ 0
    rw [selectedPoint_evaluation]
    exact S.regular gamma hgamma
  have hcover := card_le_sum_componentSeeds (GenericField K) S.G T1 H Gamma point
    hG hT1 hH
  have hcoordinate :
      (∑ C, multiplicity C * B.weightedCost (hybridSecondTail a b s) C) ≤
        flagMixed flag (exactFirstTail a b s) (hybridSecondTail a b s) :=
    by
      simpa only [exactFirstTail_eq_sharp] using resultants.divisor_le B multiplicity
  have hmovingPart :
      (∑ C, if multiplicity C = 1 then (w + 1) * (M C).movingCost else 0) ≤
        (w + 1) * flagMixed flag (movingFiber a b s) (movingCut a b s) := by
    calc
      _ ≤ ∑ C, (w + 1) * (M C).movingCost := by
        apply Finset.sum_le_sum
        intro C _
        split_ifs <;> omega
      _ = (w + 1) * (∑ C, (M C).movingCost) := by rw [Finset.mul_sum]
      _ ≤ _ := Nat.mul_le_mul_left _ hmoving
  calc
    Gamma.card ≤ ∑ C : FirstTailComponent S,
        (componentSeeds (GenericField K) S.G T1 H Gamma point C).card := hcover
    _ ≤ ∑ C : FirstTailComponent S, cost C :=
      Finset.sum_le_sum (fun C _ ↦ componentBound C)
    _ = (∑ C, multiplicity C * B.weightedCost (hybridSecondTail a b s) C) +
        ∑ C, if multiplicity C = 1 then
          (w + 1) * (M C).movingCost else 0 := by
      simp only [cost, Finset.sum_add_distrib]
    _ ≤ flagMixed flag (exactFirstTail a b s) (hybridSecondTail a b s) +
        (w + 1) * flagMixed flag (movingFiber a b s) (movingCut a b s) :=
      Nat.add_le_add hcoordinate hmovingPart
    _ = hybridStageCost flag a b s := rfl

def FixedStageBound (a b s : ℕ) : Prop :=
  ∀ {Gamma : Finset K} {flag : FlagDegree},
    (S : ResidualStage (polynomialEmbedding K) Gamma IRSProfile.domain
      prime errors flag w (RCN198.support a b s)) →
    S.nodes.card = agreements + errors →
    (∀ gamma ∈ Gamma, agreements ≤ (S.agreementFiber gamma).card) →
    S.F ∈ globalCoefficientBox K weightedCap w (a + b + s + 3) (s + 2) →
    (flag.all ≤ s + 2 ∧ flag.yz + flag.all ≤ b + s + 3 ∧
      flag.zOnly + flag.yz + flag.all ≤ a + b + s + 3) →
    Gamma.card ≤ hybridStageCost flag a b s

theorem fixedStageBound (a b s : ℕ)
    (hS : s + 2 ≤ 13) (hY : b + s + 3 ≤ 62) (hT : a + b + s + 3 ≤ 1510) :
    FixedStageBound a b s := by
  intro Gamma flag S hnodes hagreement hbox hflag
  have hflagChar := flag_characteristic a b s flag hS hY hT hflag
  by_cases hTail : S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)
  · have hTailNumerator : S.G ∣ surfaceMap (polynomialEmbedding K)
        (numerator K S.F (w + 1)) :=
      (globalTailCut_dvd_iff (polynomialEmbedding K)
        (polynomialEmbedding_injective K) S.F (w + 1) S.G).mp hTail
    have hprovider := actual_identityCurveCountProvider S agreements hnodes
      hagreement (by norm_num [agreements, w]) hTailNumerator
      weightedCap (a + b + s + 3) (s + 2)
      (by norm_num [w]) (by norm_num [w, weightedCap])
      (by norm_num [weightedCap, prime]) hbox hflagChar
      (identity_mixed_gate b s flag hS hY hflag.1 hflag.2.1)
    have hpositive : 1 ≤ identityCurveDegree flag a b s w := by
      apply identity_positive
      have hy : 0 < S.G.degreeOf 1 := S.y_dependent
      have hdeg := degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc := identity_surface_seed_bound S agreements
      (identityCurveDegree flag a b s w) hprovider hagreement
      (by norm_num [agreements, w])
      (by rw [hnodes] <;> norm_num [agreements, errors]) hpositive
    have hscaled : Gamma.card * gap ≤ gap * hybridStageCost flag a b s := by
      calc
        Gamma.card * gap = Gamma.card * (agreements - w) := rfl
        _ ≤ (S.nodes.card - w) * (errors + 1) *
            identityCurveDegree flag a b s w := hinc
        _ = (n - w) * (errors + 1) * identityCurveDegree flag a b s w := by
          rw [hnodes] <;> norm_num [n, agreements, errors]
        _ ≤ gap * hybridStageCost flag a b s :=
          identity_hybrid_budget flag a b s
    apply Nat.le_of_mul_le_mul_right ?_ (by norm_num [gap] : 0 < gap)
    simpa only [Nat.mul_comm] using hscaled
  · let S0 := RCN334.loosenStageGeneral S
    have hTail0 : ¬ S0.G ∣ globalTailCut (polynomialEmbedding K) S0.F
        (RCN326.w + 1) := by
      simpa only [S0, RCN334.loosenStageGeneral, w, RCN326.w] using hTail
    have hTailLocal : ¬ S0.G ∣ globalTailCut (polynomialEmbedding K) S0.F
        (w + 1) := by
      simpa only [w, RCN326.w] using hTail0
    have hactiveMixed := active_mixed_gate b s flag hS hY hflag.1 hflag.2.1
    obtain ⟨base, hactive, hZ, ⟨D⟩⟩ :=
      exists_firstTail_activeData S0 hTailLocal hflagChar hactiveMixed
    let hSderiv := RCN315.residualStage_pderiv_one_ne_zero_of_support S0
    let T1 := globalTailCut (polynomialEmbedding K) S0.F (w + 1)
    have hGsupport : S0.G.support ⊆ flagSupport flag :=
      (support_subset_flagSupport_iff flag S0.G).2 S0.flag_support
    have hTsupport : T1.support ⊆ flagSupport
        (sharpResidualAgreementFlag (RCN198.support a b s) (w + 1)) := by
      apply (support_subset_flagSupport_iff
        (sharpResidualAgreementFlag (RCN198.support a b s) (w + 1)) T1).2
      exact RCN088.firstTail_in_sharp_flag S0
    let U : AdaptiveUnitProjectionFamily base flag
        (sharpResidualAgreementFlag (RCN198.support a b s) (w + 1)) :=
      activeNestedUnitFamily base hactive hZ hSderiv D S0.irreducible_G
        hTailLocal hGsupport hTsupport
    have hyzTranscendental : ∀ C : FirstTailComponent S0,
        Transcendental (GenericField K)
          (coordinateValue (GenericField K)
            (CoordinateField (GenericField K) C.1) (U.yzProjection C)) := by
      intro C
      have hproj : U.yzProjection C = coordinateOfGate
          (affineU (GenericField K) C.1 D.lam) (D.uGate C) := rfl
      rw [hproj, coordinateOfGate_value]
      exact D.uTranscendental C
    let multiplicity : FirstTailComponent S0 → ℕ :=
      localMultiplicity S0 (canonicalLocalDVRFamily S0 hTail0)
    have hd : S0.G ∣ globalTailCut (polynomialEmbedding K) S0.F
        (RCN326.w + 1) - T1 := by
      simp [T1, w, RCN326.w]
    let powers0 := RCN331.reducedStage_activeFixedPowers S0 hTail0 T1 hd
      base hactive hZ hSderiv D
    have htransport : transportedMultiplicity hd multiplicity = multiplicity := by
      funext C
      apply congrArg multiplicity
      apply Subtype.ext
      rfl
    have powers : ActiveNestedFixedPowers base hactive hZ hSderiv D multiplicity := by
      change ActiveNestedFixedPowers base hactive hZ hSderiv D
        (transportedMultiplicity hd multiplicity) at powers0
      rw [htransport] at powers0
      exact powers0
    let resultants : RegularComponentWeightedInertiaResultantCertificate
        U.toPrimeFlagBudgetFamily multiplicity :=
      activeNestedWeightedCertificate base hactive hZ hSderiv D S0.irreducible_G
        hTailLocal hGsupport hTsupport multiplicity powers
    let E := AlgebraicClosure (RatFunc (GenericField K))
    let Hsupport : ResidualSupportData (RCN198.support a b s) S0.F :=
      ⟨S0.surface_s_weight, S0.surface_ys_weight, S0.surface_total_weight⟩
    have hmix : 2 * (flag.zOnly + flag.yz + flag.all) * (a + b + s + 4) < prime := by
      calc
        _ ≤ 2 * 1510 * 1511 := Nat.mul_le_mul
          (Nat.mul_le_mul_left 2 (hflag.2.2.trans hT)) (by omega)
        _ < prime := by norm_num [prime]
    obtain ⟨M, hcost, _, _, _, hmoving⟩ :=
      exists_firstTail_cut_budgets (E := E) (polynomialEmbedding K)
        S0.F S0.G T1 a b s w (by norm_num [w]) rfl Hsupport flag
        S0.irreducible_G.ne_zero S0.G_dvd_surface S0.flag_support base U prime hmix
    have hmoving' : (∑ C, (M C).movingCost) ≤
        flagMixed flag (movingFiber a b s) (movingCut a b s) := by
      simpa only [movingFiber, movingCut, T1] using hmoving
    have hnodes0 : S0.nodes.card = agreements + errors := by
      simpa only [S0, RCN334.loosenStageGeneral] using hnodes
    have hagreement0 : ∀ gamma ∈ Gamma,
        agreements ≤ (S0.agreementFiber gamma).card := by
      intro gamma hgamma
      change agreements ≤ (S.agreementFiber gamma).card
      exact hagreement gamma hgamma
    have hbox0 : S0.F ∈ globalCoefficientBox K weightedCap w
        (a + b + s + 3) (s + 2) := by
      simpa only [S0, RCN334.loosenStageGeneral] using hbox
    exact stage_card_le_hybrid S0 hTailLocal base U hyzTranscendental M hcost
      hmoving' resultants hnodes0 hagreement0 hbox0

end
end ProximityPrize.SubmissionLower.LocatorFixedStage
