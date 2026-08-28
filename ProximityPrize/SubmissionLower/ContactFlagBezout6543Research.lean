import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactPost6464ExactShear6543Research
import ProximityPrize.SubmissionLower.ContactSparsePoleSupportResearch
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_MvPolynomial_WeightedHomogeneous

/-!
# A flag-degree outer polytope that still reaches score 65.43

The exact post-6464 sheared Newton polytopes admit a particularly small
three-step flag outer bound.  Write

`Flag(a,b,c) = a * conv(0,Z) + b * conv(0,Y,Z) +
  c * conv(0,Y,S,Z)`.

Membership is equivalently described by the nested degree inequalities

* `deg_S <= c`;
* `deg_{Y,S} <= b+c`;
* `deg_{Y,S,Z} <= a+b+c`.

For the 65.43 row the sheared surface and its `S` derivative are contained
in `Flag(350,21,5)` and `Flag(350,21,4)`.  Consequently the agreement
polytope is contained in

`Flag(700*w, 1+42*w, 9*w)`.

This outer approximation is slightly larger than the exact Newton polytope,
but its normalized mixed cost is still small enough for score 65.43.  The
remaining geometry can therefore be stated as a flag-Bezout theorem rather
than a full arbitrary-polytope BKK theorem.
-/

namespace ProximityPrize.SubmissionLower.ContactFlagBezout6543Research

open scoped BigOperators
open ProximityPrize.SubmissionLower.ContactPost6464ExactShear6543Research
open ProximityPrize.SubmissionLower.ContactSparsePoleSupportResearch

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Coefficients of the nested simplex sum
`a*[0,Z] + b*conv(0,Y,Z) + c*conv(0,Y,S,Z)`. -/
structure FlagDegree where
  zOnly : ℕ
  yz : ℕ
  all : ℕ
  deriving DecidableEq, Repr

instance : Add FlagDegree := ⟨fun p q ↦
  ⟨p.zOnly + q.zOnly, p.yz + q.yz, p.all + q.all⟩⟩

instance : SMul ℕ FlagDegree := ⟨fun n p ↦
  ⟨n * p.zOnly, n * p.yz, n * p.all⟩⟩

@[simp] theorem add_zOnly (p q : FlagDegree) :
    (p + q).zOnly = p.zOnly + q.zOnly := rfl

@[simp] theorem add_yz (p q : FlagDegree) :
    (p + q).yz = p.yz + q.yz := rfl

@[simp] theorem add_all (p q : FlagDegree) :
    (p + q).all = p.all + q.all := rfl

@[simp] theorem nsmul_zOnly (n : ℕ) (p : FlagDegree) :
    (n • p).zOnly = n * p.zOnly := rfl

@[simp] theorem nsmul_yz (n : ℕ) (p : FlagDegree) :
    (n • p).yz = n * p.yz := rfl

@[simp] theorem nsmul_all (n : ℕ) (p : FlagDegree) :
    (n • p).all = n * p.all := rfl

/-- The three nested degree inequalities for an exponent in coordinates
`(Y,S,Z)`. -/
def InFlag (p : FlagDegree) (d : Fin 3 →₀ ℕ) : Prop :=
  d 1 ≤ p.all ∧
    d 0 + d 1 ≤ p.yz + p.all ∧
    d 0 + d 1 + d 2 ≤ p.zOnly + p.yz + p.all

theorem inFlag_zero (p : FlagDegree) : InFlag p 0 := by
  simp [InFlag]

theorem inFlag_add {p q : FlagDegree} {d e : Fin 3 →₀ ℕ}
    (hd : InFlag p d) (he : InFlag q e) : InFlag (p + q) (d + e) := by
  rcases hd with ⟨hdS, hdYS, hdTot⟩
  rcases he with ⟨heS, heYS, heTot⟩
  simp only [InFlag, Finsupp.add_apply, add_zOnly, add_yz, add_all]
  omega

/-- Exponent with coordinates `(Y,S,Z)`. -/
noncomputable def exponentOfTriple (t : ℕ × ℕ × ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 t.1 + Finsupp.single 1 t.2.1 +
    Finsupp.single 2 t.2.2

/-- All lattice points of a flag polytope.  The explicit bounding box makes
this a computable finite support while the filter retains the sharp nested
inequalities. -/
noncomputable def flagSupport (p : FlagDegree) : Finset (Fin 3 →₀ ℕ) :=
  by
    classical
    exact (((((Finset.range (p.zOnly + p.yz + p.all + 1)).product
        (Finset.range (p.all + 1))).product
        (Finset.range (p.zOnly + p.yz + p.all + 1))).image
          (fun t ↦ exponentOfTriple (t.1.1, t.1.2, t.2))).filter (InFlag p))

theorem exponentOfTriple_coordinates (y s z : ℕ) :
    exponentOfTriple (y, s, z) 0 = y ∧
      exponentOfTriple (y, s, z) 1 = s ∧
      exponentOfTriple (y, s, z) 2 = z := by
  simp [exponentOfTriple]

/-- The concrete finite support is extensionally the flag inequalities. -/
theorem mem_flagSupport_iff (p : FlagDegree) (d : Fin 3 →₀ ℕ) :
    d ∈ flagSupport p ↔ InFlag p d := by
  classical
  constructor
  · intro hd
    unfold flagSupport at hd
    exact (Finset.mem_filter.mp hd).2
  · intro hd
    unfold flagSupport
    rw [Finset.mem_filter]
    refine ⟨?_, hd⟩
    apply Finset.mem_image.mpr
    rcases hd with ⟨hS, hYS, htotal⟩
    refine ⟨((d 0, d 1), d 2), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by simp only [Prod.fst, Prod.snd]; omega),
          Finset.mem_range.mpr (by simp only [Prod.fst, Prod.snd]; omega)⟩,
        Finset.mem_range.mpr (by simp only [Prod.fst, Prod.snd]; omega)⟩
    · ext i
      fin_cases i <;> simp [exponentOfTriple]

theorem zero_mem_flagSupport (p : FlagDegree) :
    (0 : Fin 3 →₀ ℕ) ∈ flagSupport p := by
  rw [mem_flagSupport_iff]
  exact inFlag_zero p

/-- Flag lattice supports are anti-blocking, as required by the generic
leading-coefficient avoidance theorem. -/
theorem flagSupport_downwardClosed (p : FlagDegree) :
    ExponentSetDownwardClosed (flagSupport p) := by
  intro d hd e he
  rw [mem_flagSupport_iff] at hd ⊢
  rcases hd with ⟨hdS, hdYS, hdtotal⟩
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  exact ⟨h1.trans hdS, by omega, by omega⟩

/-- Polynomial support containment in the flag polytope. -/
def PolynomialInFlag {K : Type*} [Field K]
    (p : FlagDegree) (A : MvPolynomial (Fin 3) K) : Prop :=
  ∀ d ∈ A.support, InFlag p d

theorem support_subset_flagSupport_iff {K : Type*} [Field K]
    (p : FlagDegree) (A : MvPolynomial (Fin 3) K) :
    A.support ⊆ flagSupport p ↔ PolynomialInFlag p A := by
  simp only [PolynomialInFlag, Finset.subset_iff, mem_flagSupport_iff]

def flagSWeights : Fin 3 → ℕ := ![0, 1, 0]
def flagYSWeights : Fin 3 → ℕ := ![1, 1, 0]
def flagTotalWeights : Fin 3 → ℕ := ![1, 1, 1]

theorem flag_weight_fin3 (weights : Fin 3 → ℕ) (d : Fin 3 →₀ ℕ) :
    Finsupp.weight weights d =
      d 0 * weights 0 + d 1 * weights 1 + d 2 * weights 2 := by
  have hd : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
      Finsupp.single 2 (d 2) := by
    ext i
    fin_cases i <;> simp
  rw [hd, map_add, map_add]
  simp [Finsupp.weight_single, Nat.mul_comm]

/-- Three scalar weighted-degree bounds imply the exact support inclusion
in a flag polytope.  This is the intended adapter from the existing shear
support-function lemmas. -/
theorem support_subset_flagSupport_of_weighted_degrees
    {K : Type*} [Field K] (p : FlagDegree)
    (A : MvPolynomial (Fin 3) K)
    (hS : MvPolynomial.weightedTotalDegree flagSWeights A ≤ p.all)
    (hYS : MvPolynomial.weightedTotalDegree flagYSWeights A ≤ p.yz + p.all)
    (hTotal : MvPolynomial.weightedTotalDegree flagTotalWeights A ≤
      p.zOnly + p.yz + p.all) :
    A.support ⊆ flagSupport p := by
  rw [support_subset_flagSupport_iff]
  intro d hd
  have hs := (MvPolynomial.le_weightedTotalDegree flagSWeights hd).trans hS
  have hys := (MvPolynomial.le_weightedTotalDegree flagYSWeights hd).trans hYS
  have htotal :=
    (MvPolynomial.le_weightedTotalDegree flagTotalWeights hd).trans hTotal
  rw [flag_weight_fin3] at hs hys htotal
  change d 0 * 0 + d 1 * 1 + d 2 * 0 ≤ p.all at hs
  change d 0 * 1 + d 1 * 1 + d 2 * 0 ≤ p.yz + p.all at hys
  change d 0 * 1 + d 1 * 1 + d 2 * 1 ≤
    p.zOnly + p.yz + p.all at htotal
  simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add] at hs hys htotal
  exact ⟨hs, hys, htotal⟩

/-- Polarization of the normalized volume polynomial

`Vol(Flag(a,b,c)) = c^3 + 3*a*c^2 + 3*b*c^2 + 3*b^2*c + 6*a*b*c`.

Thus `flagMixed p q r` is the normalized mixed volume of three flag
polytopes.  The formula is kept purely integral for the benchmark ledger. -/
def flagMixed (p q r : FlagDegree) : ℕ :=
  p.all * q.all * r.all +
  (p.zOnly * q.all * r.all + q.zOnly * p.all * r.all +
    r.zOnly * p.all * q.all) +
  (p.yz * q.all * r.all + q.yz * p.all * r.all +
    r.yz * p.all * q.all) +
  (p.all * q.yz * r.yz + q.all * p.yz * r.yz +
    r.all * p.yz * q.yz) +
  (p.zOnly * q.yz * r.all + p.zOnly * r.yz * q.all +
    q.zOnly * p.yz * r.all + q.zOnly * r.yz * p.all +
    r.zOnly * p.yz * q.all + r.zOnly * q.yz * p.all)

def unitZFlag : FlagDegree := ⟨1, 0, 0⟩
def unitYZFlag : FlagDegree := ⟨0, 1, 0⟩
def unitAllFlag : FlagDegree := ⟨0, 0, 1⟩
def seedFlag : FlagDegree := unitYZFlag

/-- Tight flag outer bound for the sheared surface support. -/
def shearedSurfaceFlag : FlagDegree := ⟨350, 21, 5⟩

/-- Tight flag outer bound for the sheared `S`-derivative support. -/
def shearedDerivativeFlag : FlagDegree := ⟨350, 21, 4⟩

/-- The agreement support is `seed + w*(surface+derivative)`. -/
def shearedAgreementFlag : FlagDegree :=
  seedFlag + w • (shearedSurfaceFlag + shearedDerivativeFlag)

theorem shearedAgreementFlag_value :
    shearedAgreementFlag = ⟨91749700, 5504983, 1179639⟩ := by
  change (⟨0 + 131071 * (350 + 350),
      1 + 131071 * (21 + 21),
      0 + 131071 * (5 + 4)⟩ : FlagDegree) = _
  norm_num

/-- Exact normalized flag-Bezout cost for `(surface,agreement,agreement)`. -/
def flagWholeMixedCap : ℕ :=
  flagMixed shearedSurfaceFlag shearedAgreementFlag shearedAgreementFlag

/-- The `Z`-segment mixed cost is unchanged by the flag outer bound. -/
def flagZMixedCap : ℕ :=
  flagMixed shearedSurfaceFlag shearedAgreementFlag unitZFlag

/-- Mixed cost of a generic affine projection in the `(Y,Z)` plane. -/
def flagYZMixedCap : ℕ :=
  flagMixed shearedSurfaceFlag shearedAgreementFlag unitYZFlag

/-- Mixed cost of a generic affine projection in `(S,Y,Z)`. -/
def flagAllMixedCap : ℕ :=
  flagMixed shearedSurfaceFlag shearedAgreementFlag unitAllFlag

theorem flag_mixed_values :
    flagWholeMixedCap = 16236998221509765 ∧
      flagZMixedCap = 58195529 ∧
      flagYZMixedCap = 929817679 ∧
      flagAllMixedCap = 4898910072 := by
  norm_num [flagWholeMixedCap, flagZMixedCap, flagMixed,
    flagYZMixedCap, flagAllMixedCap,
    shearedSurfaceFlag, shearedAgreementFlag, shearedDerivativeFlag,
    seedFlag, unitZFlag, unitYZFlag, unitAllFlag, w]

/-- The whole flag mixed cost is exactly the weighted sum of the three
projection costs.  This is the algebraic reason the flag route can use
ordinary resultants for `Z`, `Y + lambda*Z`, and
`S + mu*Y + nu*Z` instead of a general toric BKK theorem. -/
theorem flag_projection_decomposition :
    flagWholeMixedCap =
      shearedAgreementFlag.zOnly * flagZMixedCap +
      shearedAgreementFlag.yz * flagYZMixedCap +
      shearedAgreementFlag.all * flagAllMixedCap := by
  norm_num [flagWholeMixedCap, flagZMixedCap, flagYZMixedCap,
    flagAllMixedCap, flagMixed, shearedSurfaceFlag,
    shearedAgreementFlag, shearedDerivativeFlag, seedFlag,
    unitZFlag, unitYZFlag, unitAllFlag, w]

/-- The flag outer approximation costs only this much beyond the exact
mixed-volume computation. -/
theorem flag_excess_exact :
    flagWholeMixedCap - shearedWholeMixedCap = 6957740851605 := by
  rw [flag_mixed_values.1]
  norm_num [shearedWholeMixedCap]

/-- Regular whole-surface numerator with the flag-Bezout cost. -/
def flagWholeNumerator : ℕ :=
  (n - w) ^ 2 * flagWholeMixedCap +
    (errors + 1) * (n - w) * gap * flagZMixedCap

/-- The implicit/singular branch is unchanged. -/
def flagTotalNumerator : ℕ :=
  flagWholeNumerator + gap * singularNumerator

def flagLedgerCeiling : ℕ :=
  (flagTotalNumerator + gapSquared - 1) / gapSquared

theorem flag_whole_numerator_exact :
    flagWholeNumerator = 278985298988701469237937066 := by
  norm_num [flagWholeNumerator, flag_mixed_values.1, flag_mixed_values.2.1,
    n, w, errors, gap, agreements]

theorem flag_total_numerator_exact :
    flagTotalNumerator = 279410497558140516468138639 := by
  rw [show flagTotalNumerator =
      flagWholeNumerator + gap * singularNumerator by rfl,
    flag_whole_numerator_exact, singular_numerator_exact]
  norm_num [gap, agreements, n, errors, w]

theorem flag_ledger_ceiling_exact :
    flagLedgerCeiling = 99985979822093871 := by
  norm_num [flagLedgerCeiling, flag_total_numerator_exact, gap_squared_exact]

theorem flag_budget_slack :
    alignmentBudget - flagLedgerCeiling = 14020177906129 := by
  rw [flag_ledger_ceiling_exact]
  norm_num [alignmentBudget]

/-- The simpler flag outer polytope, not the exact BKK polytope, still gives
the strict ledger inequality required by the 65.43 protocol row. -/
theorem flag_strict_budget :
    flagTotalNumerator < alignmentBudget * gapSquared := by
  rw [flag_total_numerator_exact, gap_squared_exact]
  norm_num [alignmentBudget]

end ProximityPrize.SubmissionLower.ContactFlagBezout6543Research

#print axioms ProximityPrize.SubmissionLower.ContactFlagBezout6543Research.inFlag_add
#print axioms ProximityPrize.SubmissionLower.ContactFlagBezout6543Research.flag_mixed_values
#print axioms ProximityPrize.SubmissionLower.ContactFlagBezout6543Research.flag_projection_decomposition
#print axioms ProximityPrize.SubmissionLower.ContactFlagBezout6543Research.flag_strict_budget
