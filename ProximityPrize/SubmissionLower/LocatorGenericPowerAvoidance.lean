/-
Ported verbatim from the public proximity-prize repository, PR #471,
commit db5c259 (submission 8aab1b73-c3cb-4cd9-a382-f1ed2c2dadc2, score 6784),
authored by jieyilong.  Row-independent: no constants of that row appear here.
-/
import ProximityPrize.SubmissionLower.LocatorIteratedPowerProduct

namespace ProximityPrize.SubmissionLower.LocatorGenericPowerAvoidance

open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN156 RCN180 RCN234 RCN260
open LocatorLowQuotient LocatorCoprimeQuotient LocatorDoubleSquareAvoidance
open LocatorIteratedPowerProduct

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

variable {K V : Type*} [Field K]

/-- The total codimension paid by `n` consecutive high-band projections.

This recursive presentation is deliberately aligned with the proof: after one
projection and one quotient by `F`, the tail is definitionally the same budget
with all three residual caps reduced by the corresponding weight of `F`.
Consequently it scales to arbitrary depth without expanding a long sum. -/
def sourcePowerBudget (delta T YS S : ℕ)
    (F : MvPolynomial (Fin 4) K) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      delta * channelCount T YS S +
        sourcePowerBudget delta
          (T - wt residualTotalWeights F)
          (YS - wt residualYSWeights F)
          (S - wt residualSWeights F) F n

/-- A small kernel-friendly consecutive sum.  Unlike a `Finset.range`
expression it unfolds one stage at a time, which is useful both to the proof
and to generated arithmetic receipts. -/
def forwardSum (f : ℕ → ℕ) (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => f start + forwardSum f (start + 1) n

theorem forwardSum_mono (f g : ℕ → ℕ)
    (h : ∀ j, f j ≤ g j) (start n : ℕ) :
    forwardSum f start n ≤ forwardSum g start n := by
  induction n generalizing start with
  | zero => simp [forwardSum]
  | succ n ih =>
      simp only [forwardSum]
      exact Nat.add_le_add (h start) (ih (start + 1))

/-- Closed-stage view of the recursive source budget.  In particular, calling
this at `start = 1` after the outer quotient produces exactly the band costs
for powers `1, ..., n`, without ever materializing an n-way addition tree. -/
theorem sourcePowerBudget_shift_eq_forwardSum
    (delta T YS S : ℕ) (F : MvPolynomial (Fin 4) K)
    (start n : ℕ) :
    sourcePowerBudget delta
        (T - start * wt residualTotalWeights F)
        (YS - start * wt residualYSWeights F)
        (S - start * wt residualSWeights F) F n =
      forwardSum (fun j => delta * channelCount
        (T - j * wt residualTotalWeights F)
        (YS - j * wt residualYSWeights F)
        (S - j * wt residualSWeights F)) start n := by
  induction n generalizing start with
  | zero => simp [sourcePowerBudget, forwardSum]
  | succ n ih =>
      simp only [sourcePowerBudget, forwardSum]
      have hT :
          T - start * wt residualTotalWeights F -
              wt residualTotalWeights F =
            T - (start + 1) * wt residualTotalWeights F := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have hY :
          YS - start * wt residualYSWeights F - wt residualYSWeights F =
            YS - (start + 1) * wt residualYSWeights F := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have hS :
          S - start * wt residualSWeights F - wt residualSWeights F =
            S - (start + 1) * wt residualSWeights F := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      rw [hT, hY, hS, ih]

/-- A compact witness for one branch of the repeated quotient extraction.
`depth = n - 1` is the terminal branch, on which no non-divisibility conclusion
is required.  Every earlier branch exposes a quotient not divisible by `F`. -/
structure PowerExtractionWitness [AddCommGroup V] [Module K V]
    (Dlow w delta T YS S n : ℕ)
    (q : V →ₗ[K] MvPolynomial (Fin 4) K)
    (F : MvPolynomial (Fin 4) K) where
  depth : ℕ
  depth_lt : depth < n
  vector : V
  quotient : MvPolynomial (Fin 4) K
  vector_ne : vector ≠ 0
  quotient_ne : quotient ≠ 0
  factorization : F ^ depth * quotient = q vector
  quotient_box : quotient ∈ nestedCoefficientBox K
    (Dlow - depth * delta - depth * wt (contactWeights w) F) w
    (T - depth * wt residualTotalWeights F)
    (YS - depth * wt residualYSWeights F)
    (S - depth * wt residualSWeights F)
  terminal_or_not_dvd : depth + 1 = n ∨ ¬ F ∣ quotient

section LinearDichotomy

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Arbitrary-depth repeated quotient/power avoidance.

At each level we spend one high-band codimension.  If the resulting low
subspace contains a polynomial not divisible by `F`, that polynomial is the
desired branch.  Otherwise division by `F` gives an injective linear map on the
low subspace and the construction recurses.  The theorem is stated for `n+1`
levels so the terminal branch is always meaningful. -/
theorem exists_powerExtractionWitness
    (n Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] MvPolynomial (Fin 4) K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hsource : sourcePowerBudget delta T YS S F (n + 1) <
      Module.finrank K V) :
    Nonempty (PowerExtractionWitness Dlow w delta T YS S (n + 1) q F) := by
  classical
  induction n generalizing V Dhigh Dlow T YS S with
  | zero =>
      let bandOne := (highBandMap (K := K) w Dlow delta T YS S).comp q
      let lowOne := LinearMap.ker bandOne
      have hrangeOne : Module.finrank K bandOne.range ≤
          delta * channelCount T YS S := by
        calc
          Module.finrank K bandOne.range ≤
              Module.finrank K (HighBandIndex delta T YS S → K) :=
            bandOne.range.finrank_le
          _ = delta * channelCount T YS S := by
            rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
      have hlowOneRank : 0 < Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        change delta * channelCount T YS S + 0 < Module.finrank K V at hsource
        omega
      let qOne : lowOne →ₗ[K] MvPolynomial (Fin 4) K := q.comp lowOne.subtype
      have hqOne : Function.Injective qOne := by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
      have hqOneBox : ∀ v : lowOne,
          qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
        intro v
        have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
          have hv := v.2
          change bandOne v.1 = 0 at hv
          simpa only [bandOne, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
            (q v.1) (hmem v.1) hzero
      letI : Nontrivial lowOne := Module.finrank_pos_iff.mp hlowOneRank
      obtain ⟨v, hv⟩ := exists_ne (0 : lowOne)
      have hqv : qOne v ≠ 0 := by
        intro hz
        apply hv
        apply hqOne
        simpa only [map_zero] using hz
      exact ⟨{
        depth := 0
        depth_lt := by omega
        vector := v.1
        quotient := qOne v
        vector_ne := by
          intro hz
          apply hv
          exact Subtype.ext hz
        quotient_ne := hqv
        factorization := by
          simp only [pow_zero, one_mul, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype]
        quotient_box := by simpa using hqOneBox v
        terminal_or_not_dvd := Or.inl rfl }⟩
  | succ n ih =>
      let bandOne := (highBandMap (K := K) w Dlow delta T YS S).comp q
      let lowOne := LinearMap.ker bandOne
      have hrangeOne : Module.finrank K bandOne.range ≤
          delta * channelCount T YS S := by
        calc
          Module.finrank K bandOne.range ≤
              Module.finrank K (HighBandIndex delta T YS S → K) :=
            bandOne.range.finrank_le
          _ = delta * channelCount T YS S := by
            rw [Module.finrank_fintype_fun_eq_card, highBandIndex_card]
      have hlowOneRank :
          sourcePowerBudget delta
              (T - wt residualTotalWeights F)
              (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) F (n + 1) <
            Module.finrank K lowOne := by
        have hsum := bandOne.finrank_range_add_finrank_ker
        change Module.finrank K bandOne.range + Module.finrank K lowOne =
          Module.finrank K V at hsum
        change delta * channelCount T YS S +
          sourcePowerBudget delta
            (T - wt residualTotalWeights F)
            (YS - wt residualYSWeights F)
            (S - wt residualSWeights F) F (n + 1) <
          Module.finrank K V at hsource
        omega
      let qOne : lowOne →ₗ[K] MvPolynomial (Fin 4) K := q.comp lowOne.subtype
      have hqOne : Function.Injective qOne := by
        intro a b hab
        apply Subtype.ext
        apply hq
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using hab
      have hqOneBox : ∀ v : lowOne,
          qOne v ∈ nestedCoefficientBox K Dlow w T YS S := by
        intro v
        have hzero : highBandMap w Dlow delta T YS S (q v.1) = 0 := by
          have hv := v.2
          change bandOne v.1 = 0 at hv
          simpa only [bandOne, qOne, LinearMap.comp_apply,
            Submodule.coe_subtype] using hv
        simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype] using
          mem_low_of_highBandMap_eq_zero Dhigh Dlow w delta T YS S hwidth
            (q v.1) (hmem v.1) hzero
      by_cases hdivOne : ∀ v : lowOne, F ∣ qOne v
      · let qTwo := quotientLinear qOne F hF hdivOne
        have hqTwo : Function.Injective qTwo :=
          quotientLinear_injective qOne hqOne F hF hdivOne
        have hqTwoBox : ∀ v : lowOne,
            qTwo v ∈ nestedCoefficientBox K
              (Dlow - wt (contactWeights w) F) w
              (T - wt residualTotalWeights F)
              (YS - wt residualYSWeights F)
              (S - wt residualSWeights F) := by
          intro v
          by_cases hv : v = 0
          · subst v
            rw [map_zero]
            exact (nestedCoefficientBox K _ _ _ _ _).zero_mem
          · have hqOneV : qOne v ≠ 0 := by
              intro hz
              apply hv
              apply hqOne
              simpa only [map_zero] using hz
            have hqTwoV : qTwo v ≠ 0 := by
              intro hz
              apply hqOneV
              rw [recon_eq_mul_quotientPolynomial qOne F hdivOne v]
              change F * qTwo v = 0
              rw [hz, mul_zero]
            exact quotient_mem_nestedCoefficientBox_of_mul_eq
              (qOne v) F (qTwo v) Dlow w T YS S hqOneV hF hqTwoV
                (hqOneBox v)
                (recon_eq_mul_quotientPolynomial qOne F hdivOne v)
        let DOneHigh := Dlow - wt (contactWeights w) F
        let DOneLow := Dlow - delta - wt (contactWeights w) F
        let TOne := T - wt residualTotalWeights F
        let YOne := YS - wt residualYSWeights F
        let SOne := S - wt residualSWeights F
        have hwidthRest : DOneHigh ≤ DOneLow + delta := by
          simp only [DOneHigh, DOneLow]
          omega
        obtain ⟨htail⟩ := ih DOneHigh DOneLow TOne YOne SOne
          hwidthRest qTwo hqTwo (by simpa [DOneHigh, TOne, YOne, SOne]
            using hqTwoBox) (by
              simpa only [TOne, YOne, SOne] using hlowOneRank)
        refine ⟨{
          depth := htail.depth + 1
          depth_lt := by
            have h := htail.depth_lt
            omega
          vector := htail.vector.1
          quotient := htail.quotient
          vector_ne := by
            intro hz
            apply htail.vector_ne
            exact Subtype.ext hz
          quotient_ne := htail.quotient_ne
          factorization := ?_
          quotient_box := ?_
          terminal_or_not_dvd := ?_ }⟩
        · calc
            F ^ (htail.depth + 1) * htail.quotient =
                F * (F ^ htail.depth * htail.quotient) := by
              rw [pow_succ]
              ring
            _ = F * qTwo htail.vector := by rw [htail.factorization]
            _ = qOne htail.vector :=
              (recon_eq_mul_quotientPolynomial qOne F hdivOne
                htail.vector).symm
            _ = q htail.vector.1 := rfl
        · have hD :
              DOneLow - htail.depth * delta -
                    htail.depth * wt (contactWeights w) F =
                Dlow - (htail.depth + 1) * delta -
                    (htail.depth + 1) * wt (contactWeights w) F := by
              simp only [DOneLow]
              rw [Nat.add_mul, Nat.one_mul, Nat.add_mul, Nat.one_mul]
              omega
          have hT : TOne - htail.depth * wt residualTotalWeights F =
              T - (htail.depth + 1) * wt residualTotalWeights F := by
            simp only [TOne]
            rw [Nat.add_mul, Nat.one_mul]
            omega
          have hY : YOne - htail.depth * wt residualYSWeights F =
              YS - (htail.depth + 1) * wt residualYSWeights F := by
            simp only [YOne]
            rw [Nat.add_mul, Nat.one_mul]
            omega
          have hS : SOne - htail.depth * wt residualSWeights F =
              S - (htail.depth + 1) * wt residualSWeights F := by
            simp only [SOne]
            rw [Nat.add_mul, Nat.one_mul]
            omega
          simpa only [hD, hT, hY, hS] using htail.quotient_box
        · rcases htail.terminal_or_not_dvd with hterminal | hnot
          · left
            omega
          · exact Or.inr hnot
      · push Not at hdivOne
        obtain ⟨v, hvdiv⟩ := hdivOne
        have hv : v.1 ≠ 0 := by
          intro hz
          apply hvdiv
          have hvzero : v = 0 := Subtype.ext hz
          rw [hvzero]
          simp only [map_zero]
          exact dvd_zero F
        have hqv : qOne v ≠ 0 := by
          intro hz
          apply hv
          apply hq
          simpa only [qOne, LinearMap.comp_apply, Submodule.coe_subtype,
            map_zero] using hz
        exact ⟨{
          depth := 0
          depth_lt := by omega
          vector := v.1
          quotient := qOne v
          vector_ne := hv
          quotient_ne := hqv
          factorization := by
            simp only [pow_zero, one_mul, qOne, LinearMap.comp_apply,
              Submodule.coe_subtype]
          quotient_box := by simpa using hqOneBox v
          terminal_or_not_dvd := Or.inr hvdiv }⟩

end LinearDichotomy

section GenericPowerSpecialization

variable {I : Type*} [Fintype I]
local instance : DecidableEq I := Classical.decEq I

/-- Generic replacement for the separate square/cube/.../ninth-power
specialization lemmas.  The two reusable iterated-derivative theorems reduce
every power to the same short argument. -/
theorem specialization_eq_zero_of_kernel_power
    (D Dlow w L s m n : ℕ) (hn : 1 ≤ n)
    (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈
      globalCoefficientBox K Dlow w L s)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hw : 1 ≤ w) (hP : P.natDegree ≤ w)
    (hcapacity : Dlow ≤ (m - n) * support.card + n * (w - 1))
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i)
    (F Q : MvPolynomial (Fin 4) K)
    (heq : reconstruct K D w L s v.1 = F ^ n * Q)
    (hfactorial : (n.factorial : K) ≠ 0)
    (hFzero : RCN319.specialization K P gamma F = 0)
    (hregular : RCN319.specialization K P gamma
      (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) :
    RCN319.specialization K P gamma Q = 0 := by
  have hiter := specialization_pderivRIter_eq_zero_of_kernel_low_box
    D Dlow w L s m n hn nodes u0 u1 v hlow P gamma support hw hP
      hcapacity hvalues
  rw [heq] at hiter
  exact specialization_eq_zero_of_pderivRIter_power
    P gamma F Q n hfactorial hFzero hregular hiter

/-- Family form used by source-count arguments: one invocation supplies the
vanishing hypothesis for every selected regular seed, independently of the
requested power depth. -/
theorem source_power_specialization_zero
    (D Dlow w L s m n : ℕ) (hn : 1 ≤ n) (hw : 1 ≤ w)
    (nodes : I ↪ K) (u0 u1 : I → K)
    (v : ConstraintKernel (K := K) D w L s m nodes u0 u1)
    (hlow : reconstruct K D w L s v.1 ∈
      globalCoefficientBox K Dlow w L s)
    (selected : K → Polynomial K) (Gamma seeds : Finset K)
    (support : K → Finset I)
    (hseed : seeds ⊆ Gamma)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hcapacity : ∀ gamma ∈ seeds,
      Dlow ≤ (m - n) * (support gamma).card + n * (w - 1))
    (hvalues : ∀ gamma ∈ seeds, ∀ i ∈ support gamma,
      (selected gamma).eval (nodes i) = u0 i + gamma * u1 i)
    (F Q : MvPolynomial (Fin 4) K)
    (heq : reconstruct K D w L s v.1 = F ^ n * Q)
    (hfactorial : (n.factorial : K) ≠ 0)
    (hFzero : ∀ gamma ∈ seeds,
      RCN319.specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ seeds,
      RCN319.specialization K (selected gamma) gamma
        (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0) :
    ∀ gamma ∈ seeds,
      RCN319.specialization K (selected gamma) gamma Q = 0 := by
  intro gamma hgamma
  apply specialization_eq_zero_of_kernel_power
    D Dlow w L s m n hn nodes u0 u1 v hlow
      (selected gamma) gamma (support gamma) hw
      (hdegree gamma (hseed hgamma)) (hcapacity gamma hgamma)
      (hvalues gamma hgamma) F Q heq hfactorial
      (hFzero gamma hgamma) (hregular gamma hgamma)

end GenericPowerSpecialization

/-- The generic extractor instantiated at the requested maximum helper depth.
The proof term remains the same size as for every other depth. -/
theorem source_power_count_depth30
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Dhigh Dlow w delta T YS S : ℕ)
    (hwidth : Dhigh ≤ Dlow + delta)
    (q : V →ₗ[K] MvPolynomial (Fin 4) K) (hq : Function.Injective q)
    (hmem : ∀ v, q v ∈ nestedCoefficientBox K Dhigh w T YS S)
    (F : MvPolynomial (Fin 4) K) (hF : F ≠ 0)
    (hsource : sourcePowerBudget delta T YS S F 30 <
      Module.finrank K V) :
    Nonempty (PowerExtractionWitness Dlow w delta T YS S 30 q F) := by
  simpa using exists_powerExtractionWitness 29 Dhigh Dlow w delta T YS S
    hwidth q hq hmem F hF hsource

end

end ProximityPrize.SubmissionLower.LocatorGenericPowerAvoidance
