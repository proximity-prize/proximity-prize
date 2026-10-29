import ProximityPrize.SubmissionBinaryLower.P64List
import ProximityPrize.SubmissionBinaryLower.P64Interp

/-!
# The 64.00 claim, conditional on the class bounds (formal-plan.md section 1)

`protocolClaim6400_of_classBounds` proves `ProtocolClaim 6400 78622925 268435456` from one
hypothesis, `ClassBounds K1 K2 K3`, together with the surface side condition on `K1, K2, K3`.
`ClassBounds` is the per-factor charge of PROOF.md 3.2 and 4: for every interpolant of Lemma E and
every family of bad slopes with witnesses, each factor's single-factor slopes are at most
`factorBound`. Everything else (Lemma E, GS, the cover, Theorem D, Lemma R and the pair case, the
(Y0) case, the budgets, Lemma J, the MCA bridge, the score) is proved.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64Final

open Polynomial ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open CoreDefinitions ProximityGap ToyProblem
open BCHKSSubstitutionVanish P64LineOrder P64Charging P64Ledger P64Interp P64List
open scoped NNReal

local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
local notation "Tri" => Polynomial (Polynomial (Polynomial Fld))

/-- The pair `(u0, u1)` restricted to `A` is not a pair of codewords. -/
def BadOn (U : Fin 2 → Idx → Fld) (A : Finset Idx) : Prop :=
  ¬ ∃ p₀ p₁ : Fld[X], p₀.natDegree ≤ 1048575 ∧ p₁.natDegree ≤ 1048575 ∧
    ∀ i ∈ A, p₀.eval (BinaryIRSProfile.domain i) = U 0 i ∧
      p₁.eval (BinaryIRSProfile.domain i) = U 1 i

/-- **The remaining assumption**: per-factor class bounds (PROOF.md 3.2 and 4, classes 1 to 7).
Classes 6 and 7 are to be derived from `P64Surf.SurfaceInterface K1 K2 K3`. -/
def ClassBounds (K1 K2 K3 : ℚ) : Prop :=
  ∀ (U : Fin 2 → Idx → Fld) (Q : Tri) (S : Finset Fld) (P : Fld → Fld[X])
    (Az : Fld → Finset Idx),
    GSCaps Q →
    (∀ i, OrdGE Q (BinaryIRSProfile.domain i)
      ((Polynomial.C (U 0 i) : Polynomial Fld) + Polynomial.X * Polynomial.C (U 1 i)) 249292) →
    (∀ z ∈ S, (P z).natDegree ≤ 1048575 ∧ 1482911 ≤ (Az z).card ∧
      (∀ i ∈ Az z, (P z).eval (BinaryIRSProfile.domain i) = U 0 i + z * U 1 i) ∧
      BadOn U (Az z)) →
    ∀ R ∈ factors Q, ((caseSingle Q S P R).card : ℚ) ≤
      factorBound K1 K2 K3 R.natDegree (P64Caps.YZ.yzSupportDegree R 1)
        (P64Caps.Weighted.weightedSupportDegree R 1048575)

/-- Agreement with a polynomial of degree at most `D` on `A` puts the word in the projected
base code. -/
lemma mem_projected_of_poly (w : Idx → Fld) (A : Finset Idx) (p : Fld[X])
    (hp : p.natDegree ≤ 1048575) (hagree : ∀ i ∈ A, p.eval (BinaryIRSProfile.domain i) = w i) :
    LinearCode.projectedWord w A ∈ LinearCode.projectedCodeSubmod BinaryIRSProfile.baseCode A := by
  rw [LinearCode.mem_projectedCodeSubmod_iff]
  refine ⟨ReedSolomon.evalOnPoints BinaryIRSProfile.domain p, ?_, ?_⟩
  · change _ ∈ ReedSolomon.code BinaryIRSProfile.domain BinaryIRSProfile.baseDimension
    rw [ReedSolomon.mem_code_iff_exists_polynomial]
    refine ⟨p, ?_, rfl⟩
    by_cases hp0 : p = 0
    · simp [hp0]
    · rw [Polynomial.degree_eq_natDegree hp0]
      norm_num [BinaryIRSProfile.baseDimension]
      exact_mod_cast Nat.lt_succ_of_le hp
  · funext i
    simp [LinearCode.projectedWord, ReedSolomon.evalOnPoints, hagree i.1 i.2]

/-- A word in the projected base code is a polynomial of degree at most `D` on `A`. -/
lemma exists_poly_of_mem_projected (w : Idx → Fld) (A : Finset Idx)
    (hw : LinearCode.projectedWord w A ∈
      LinearCode.projectedCodeSubmod BinaryIRSProfile.baseCode A) :
    ∃ p : Fld[X], p.natDegree ≤ 1048575 ∧
      ∀ i ∈ A, p.eval (BinaryIRSProfile.domain i) = w i := by
  rw [LinearCode.mem_projectedCodeSubmod_iff] at hw
  obtain ⟨c, hc, hceq⟩ := hw
  change c ∈ ReedSolomon.code BinaryIRSProfile.domain BinaryIRSProfile.baseDimension at hc
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hc
  obtain ⟨p, hpdeg, rfl⟩ := hc
  refine ⟨p, ?_, ?_⟩
  · by_cases hp : p = 0
    · simp [hp]
    · have hlt : p.natDegree < BinaryIRSProfile.baseDimension :=
        (Polynomial.natDegree_lt_iff_degree_lt hp).2 hpdeg
      norm_num [BinaryIRSProfile.baseDimension] at hlt ⊢
      omega
  · intro i hi
    have heq := congrFun hceq ⟨i, hi⟩
    simpa [LinearCode.projectedWord, ReedSolomon.evalOnPoints] using heq.symm

/-- **(T)**: the chosen-agreement-set bound with numerator `2^64 - 235031`. -/
theorem givenSets_of_classBounds {K1 K2 K3 : ℚ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3)
    (hK : K1 * 2097152 * 58589180685 + K2 * 352552 * 58589180685 +
      K3 * 2097152 * (58589180685 + 352552) ≤ 17864703000000000000)
    (hcl : ClassBounds K1 K2 K3) :
    AffineLineGivenSetsBound BinaryIRSProfile.baseCode (radius : ℝ) numerator := by
  classical
  intro U S T hS hTcard hcomb
  by_contra hall
  push Not at hall
  have hw : ∀ z ∈ S, ∃ p : Fld[X], p.natDegree ≤ 1048575 ∧
      ∀ i ∈ T z, p.eval (BinaryIRSProfile.domain i) = U 0 i + z * U 1 i := fun z hz =>
    exists_poly_of_mem_projected _ _ (hcomb z hz)
  let P : Fld → Fld[X] := fun z => if hz : z ∈ S then Classical.choose (hw z hz) else 0
  have hPspec : ∀ z ∈ S, (P z).natDegree ≤ 1048575 ∧
      ∀ i ∈ T z, (P z).eval (BinaryIRSProfile.domain i) = U 0 i + z * U 1 i := by
    intro z hz
    simp only [P, dif_pos hz]
    exact Classical.choose_spec (hw z hz)
  let Az : Fld → Finset Idx := fun z =>
    Finset.univ.filter fun i => (P z).eval (BinaryIRSProfile.domain i) = U 0 i + z * U 1 i
  have hTA : ∀ z ∈ S, T z ⊆ Az z := fun z hz i hi => by
    simp only [Az, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hPspec z hz).2 i hi
  have hTge : ∀ z ∈ S, 1482911 ≤ (T z).card := by
    intro z hz
    have h := hTcard z hz
    rw [BinaryIRSProfile.card_index] at h
    have hrad : ((radius : ℝ≥0) : ℝ) = 78622925 / 268435456 := by simp [radius]
    rw [hrad] at h
    have : (1482910 : ℝ) < (T z).card := by
      have := h
      norm_num at this
      linarith
    exact_mod_cast this
  have hdata : ∀ z ∈ S, (P z).natDegree ≤ 1048575 ∧ 1482911 ≤ (Az z).card ∧
      (∀ i ∈ Az z, (P z).eval (BinaryIRSProfile.domain i) = U 0 i + z * U 1 i) ∧
      BadOn U (Az z) := by
    intro z hz
    refine ⟨(hPspec z hz).1, (hTge z hz).trans (Finset.card_le_card (hTA z hz)), ?_, ?_⟩
    · intro i hi
      simpa [Az] using hi
    · rintro ⟨p₀, p₁, h₀, h₁, hag⟩
      obtain ⟨j, hj⟩ := hall z hz
      apply hj
      fin_cases j
      · exact mem_projected_of_poly _ _ p₀ h₀ fun i hi => (hag i (hTA z hz hi)).1
      · exact mem_projected_of_poly _ _ p₁ h₁ fun i hi => (hag i (hTA z hz hi)).2
  obtain ⟨Q, hQ, hGS⟩ := exists_interpolant BinaryIRSProfile.domain (U 0) (U 1)
  have hbad : ∀ z ∈ S, triEval Q z (P z) = 0 := by
    intro z hz
    obtain ⟨hdeg, hcard, hag, _⟩ := hdata z hz
    exact triEval_eq_zero BinaryIRSProfile.domain _ Q hQ hGS z (P z) hdeg (Az z) hcard
      (fun i hi => by rw [hag i hi]; simp; ring)
  have hpair : (casePair Q S P).card ≤ 352552 * 58589180685 := by
    have hF : 2 * Q.natDegree * P64Caps.Weighted.weightedSupportDegree Q 1048575 <
        Fintype.card Fld := by
      rw [show Fintype.card Fld = 2 ^ (192 : ℕ) from BF64.card_ext3]
      have h1 := hQ.natDegree_le
      have h2 := hQ.weighted_lt
      calc 2 * Q.natDegree * P64Caps.Weighted.weightedSupportDegree Q 1048575 ≤
            2 * 352552 * (249292 * 1482911) := by gcongr; omega
        _ < 2 ^ 192 := by norm_num
    exact (P64Resultant.card_casePair_le Q hQ.ne_zero 1048575 hF S P).trans
      (Nat.mul_le_mul hQ.natDegree_le hQ.yz_le)
  have hwle : P64Caps.Weighted.weightedSupportDegree Q 1048575 ≤ 249292 * 1482911 - 1 := by
    have := hQ.weighted_lt
    omega
  have hcls := hcl U Q S P Az hQ hGS hdata
  have hcard := card_bad_le hK1 hK2 hK3 hK Q hQ.ne_zero hQ.natDegree_le hQ.yz_le
    hwle S P hbad hpair hcls
  have hnum : numerator = 2 ^ 64 - 235031 := rfl
  rw [hnum] at hS
  exact absurd hcard (not_le.mpr hS)

lemma nat_div_le_inv_pow {m q t : ℕ} (hm : 0 < m) (hq : m * 2 ^ t ≤ q) :
    (m : ENNReal) / (q : ENNReal) ≤ 1 / 2 ^ t := by
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
  have hmtop : (m : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hqE : ((m * 2 ^ t : ℕ) : ENNReal) ≤ (q : ENNReal) := by exact_mod_cast hq
  have hcast : ((m * 2 ^ t : ℕ) : ENNReal) = (m : ENNReal) * 2 ^ t := by
    push_cast
    ring
  calc
    (m : ENNReal) / (q : ENNReal) ≤ (m : ENNReal) / ((m * 2 ^ t : ℕ) : ENNReal) :=
      ENNReal.div_le_div_left hqE _
    _ = (m : ENNReal) / ((m : ENNReal) * 2 ^ t) := by rw [hcast]
    _ = (m : ENNReal) * 1 / ((m : ENNReal) * 2 ^ t) := by rw [mul_one]
    _ = 1 / 2 ^ t := ENNReal.mul_div_mul_left 1 (2 ^ t) hm0 hmtop

theorem certifiedGammaError_le_of_givenSets
    (hgiven : AffineLineGivenSetsBound BinaryIRSProfile.baseCode (radius : ℝ) numerator) :
    certifiedGammaError BinaryIRSProfile.code radius ≤ (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hmca : mcaError (AffineLineGenerator Fld) BinaryIRSProfile.code (radius : ℝ) ≤
      (numerator : ENNReal) / (Fintype.card Fld : ENNReal) := by
    calc
      _ ≤ mcaError (AffineLineGenerator Fld) BinaryIRSProfile.baseCode (radius : ℝ) := by
        simpa [BinaryIRSProfile.code, BinaryIRSProfile.baseCode,
          ReedSolomon.Interleaved.irsCode,
          BinaryIRSProfile.totalDimension_div_interleaving] using
          (ProximityGap.mcaError_interleaved_le BinaryIRSProfile.baseCode
            BinaryIRSProfile.interleaving radius
            (by norm_num [BinaryIRSProfile.interleaving])
            (by norm_num [radius]) (by norm_num [radius]))
      _ ≤ ENNReal.ofReal ((numerator : ℝ) / Fintype.card Fld) :=
          mcaError_affineLine_le_of_givenSetsBound _ _ _ hgiven
      _ = (numerator : ENNReal) / (Fintype.card Fld : ENNReal) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_natCast]
  have hLambdaNat : (Code.Lambda SquaredCode (radius : ℝ)).toNat ≤ listBound :=
    ENat.toNat_le_of_le_natCast lambda_le
  have hList :
      ((Code.Lambda SquaredCode (radius : ℝ)).toNat : ENNReal) / (Fintype.card Fld : ENNReal) ≤
        (listBound : ENNReal) / (Fintype.card Fld : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    mcaError (AffineLineGenerator Fld) BinaryIRSProfile.code (radius : ℝ) +
        ((Code.Lambda
          ((BinaryIRSProfile.code ^⋈ (Fin 2) :
            ModuleCode Idx Fld (Fin 2 → Fin BinaryIRSProfile.interleaving → Fld)) :
            Set (Idx → Fin 2 → Fin BinaryIRSProfile.interleaving → Fld))
          (radius : ℝ)).toNat : ENNReal) / (Fintype.card Fld : ENNReal) ≤
      (numerator : ENNReal) / (Fintype.card Fld : ENNReal) +
        (listBound : ENNReal) / (Fintype.card Fld : ENNReal) := by
      apply add_le_add hmca
      simpa [SquaredCode] using hList
    _ = ((numerator + listBound : ℕ) : ENNReal) / (Fintype.card Fld : ENNReal) := by
      rw [← ENNReal.add_div]
      norm_num
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply nat_div_le_inv_pow
      · norm_num [numerator, listBound]
      · rw [show Fintype.card Fld = 2 ^ (192 : ℕ) from BF64.card_ext3]
        norm_num [numerator, listBound]

end P64Final
end ProximityPrize.SubmissionBinaryLower

namespace ProximityPrize.Benchmark.Binary

open ToyProblem
open scoped NNReal
open ProximityPrize.SubmissionBinaryLower

/-- The 64.00 claim, conditional only on the per-factor class bounds. -/
theorem protocolClaim6400_of_classBounds {K1 K2 K3 : ℚ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hK3 : 0 ≤ K3)
    (hK : K1 * 2097152 * 58589180685 + K2 * 352552 * 58589180685 +
      K3 * 2097152 * (58589180685 + 352552) ≤ 17864703000000000000)
    (hcl : P64Final.ClassBounds K1 K2 K3) :
    ProtocolClaim 6400 78622925 268435456 where
  admissible := by
    constructor <;> norm_num [claimedRadius, BinaryIRSProfile.minRelativeDistance]
  reduction := by
    have h : ToyProblem.certifiedGammaError BinaryIRSProfile.code P64List.radius ≤
        reductionTarget :=
      (P64Final.certifiedGammaError_le_of_givenSets
        (P64Final.givenSets_of_classBounds hK1 hK2 hK3 hK hcl)).trans (by
          norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
    have hr : claimedRadius 78622925 268435456 = P64List.radius := by
      norm_num [claimedRadius, P64List.radius]
    have hc : ReedSolomon.Interleaved.irsCode BinaryIRSProfile.domain
        BinaryIRSProfile.totalDimension BinaryIRSProfile.interleaving = BinaryIRSProfile.code :=
      rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hr, hc]
    exact h
  score := by
    have hr : claimedRadius 78622925 268435456 = P64List.radius := by
      norm_num [claimedRadius, P64List.radius]
    rw [hr]
    exact P64List.radius_score

end ProximityPrize.Benchmark.Binary
