import ArkLib.Data.CodingTheory.ProximityGenerator.AffineGenerator
import ArkLib.Data.CodingTheory.ProximityGenerator.Interleaving
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CurveCertificate
import ArkLib.Data.Polynomial.Differential.OrderZeroPresentation
import ProximityPrize.SubmissionLower.Fast002
import ProximityPrize.SubmissionLower.Fast003
import ProximityPrize.SubmissionLower.Fast009
import ProximityPrize.SubmissionLower.Fast010
import ProximityPrize.SubmissionLower.Fast011
set_option Elab.async false

section PackSource_WeightedChart
set_option autoImplicit true
namespace Astra7
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4000

variable {F : Type*} [Field F]

theorem initialEquation_weight {r : ℕ} (a b : ℕ) (center : F)
    (Q : DifferentialPolynomial F r) :
    (initialJetEquation center Q).weightedTotalDegree (coeffWeight a b (r+1)) ≤
      Q.weightedTotalDegree (jetWeight a b (r+1)) := by
  apply weightedTotalDegree_aeval_le_of_le
  intro i
  cases i with
  | none => simp [jetWeight]
  | some j =>
    change (MvPolynomial.X j : MvPolynomial (Fin (r+1)) F).weightedTotalDegree
      (coeffWeight a b (r+1)) ≤ a+b*j.val
    rw [MvPolynomial.X,weightedTotalDegree_monomial _ _ 1 one_ne_zero]
    simp [Finsupp.weight_single,coeffWeight]

def chartBound (r a b V K τ : ℕ) : ℕ := τ*(V-(a+b*r))+a+b*(K-1)

theorem agreementEquation_weight {r : ℕ} (a b V K τ : ℕ) (center : F)
    (Q : DifferentialPolynomial F r) (hτ : TaylorExponentSufficient r K τ)
    (hV : a+b*r ≤ V)
    (hQ : Q.weightedTotalDegree (jetWeight a b (r+1)) ≤ V) (x y : F) :
    (taylorAgreementEquation center Q K τ x y).weightedTotalDegree
      (coeffWeight a b (r+1)) ≤ chartBound r a b V K τ := by
  unfold taylorAgreementEquation
  apply (AddMonoidAlgebra.supDegree_sub_le).trans
  apply max_le
  · apply AddMonoidAlgebra.supDegree_sum_le.trans
    apply Finset.sup_le
    intro l _
    apply (weightedTotalDegree_mul_le _ _ _).trans
    rw [weightedTotalDegree_C,zero_add]
    apply (commonTaylor_weight a b V K τ center Q hτ hV hQ l).trans
    dsimp [chartBound]
    have hl : l.val ≤ K-1 := by omega
    gcongr
  · apply (weightedTotalDegree_mul_le _ _ _).trans
    rw [weightedTotalDegree_C,zero_add]
    apply (weightedTotalDegree_pow_le _ _ _).trans
    have hs := (initialSeparant_weight a b center Q).trans
      (Nat.sub_le_sub_right hQ (a+b*r))
    exact (Nat.mul_le_mul_left τ hs).trans (by dsimp [chartBound]; omega)

theorem weighted_regular_jets_card [IsAlgClosed F] {r n k A : ℕ}
    (a b V : ℕ) (ha : 0 < a) (hV : a+b*r ≤ V)
    (hchar : ∀ j : Fin (r+1), ((a+b*j.val : ℕ) : F) ≠ 0)
    (center : F) (Q : DifferentialPolynomial F r)
    (hQ : Q.weightedTotalDegree (jetWeight a b (r+1)) ≤ V)
    (hrk : r < k) (hkA : k ≤ A)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (S : Finset (Fin (r+1) → F))
    (hS : ∀ jet ∈ S, aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0)
    (hA : ∀ jet ∈ S, A ≤ {i | aeval jet
      (taylorAgreementEquation center Q k (2*k) (domain i) (received i)) = 0}.ncard) :
    ((S.card * ∏ j : Fin (r+1), (a+b*j.val) : ℕ) : ℚ) ≤ V *
      ((((n-k+1)*chartBound r a b V k (2*k) : ℕ) : ℚ) / ((A-k+1 : ℕ) : ℚ)) ^ r := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨jet,hjet⟩
  · simp only [Finset.card_empty,zero_mul,Nat.cast_zero]
    positivity
  have hsep : initialJetSeparant center Q ≠ 0 := by
    intro hz
    exact (hS jet hjet).2 (by simp [hz])
  have hinit := initialJetEquation_ne_zero_of_initialJetSeparant_ne_zero center Q hsep
  have hτ := taylorExponentSufficient_two_mul r k
  have hw : ∀ j : Fin (r+1), 0 < coeffWeight a b (r+1) j := by
    intro j
    dsimp [coeffWeight]
    omega
  have hfinite : ∀ T : Finset (Fin n), T.card = k →
      {jet : Fin (r+1) → F | aeval jet (initialJetEquation center Q) = 0 ∧
        aeval jet (initialJetSeparant center Q) ≠ 0 ∧
        ∀ i ∈ T, aeval jet (taylorAgreementEquation center Q k (2*k)
          (domain i) (received i)) = 0}.Finite := by
    intro T hT
    apply Set.Subsingleton.finite
    intro x hx y hy
    apply eq_of_highTaylorCuts_of_agreement center Q (k := k) hτ hrk domain received T
      domain.injective.injOn (by omega) hx.2.1 hy.2.1
      (by intro l hl hl'; omega) (by intro l hl hl'; omega) hx.2.2 hy.2.2
  have hh := weighted_hypersurface_count (coeffWeight a b (r+1)) hw hchar hinit
    (initialJetSeparant center Q) ((initialEquation_weight a b center Q).trans hQ)
    (fun i => taylorAgreementEquation center Q k (2*k) (domain i) (received i))
    (fun i => agreementEquation_weight a b V k (2*k) center Q hτ hV hQ (domain i) (received i))
    (by dsimp [chartBound]; omega) hkA hfinite S hS hA
  simpa [coeffWeight,Nat.card_eq_fintype_card] using hh

end
end Astra7
end PackSource_WeightedChart

section PackSource_WeightedRegularList
set_option autoImplicit true
namespace Astra7
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4000
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F]

/-- Weighted regular-list bound over the original field, with the entire
algebraic-closure chart construction and finite covering degree discharged. -/
theorem weighted_regular_polynomial_card {r n k A : ℕ}
    (a b V : ℕ) (ha : 0 < a) (hV : a+b*r ≤ V)
    (hchar : ∀ j : Fin (r+1), ((a+b*j.val : ℕ) : F) ≠ 0)
    (Q : DifferentialPolynomial F r)
    (hQ : Q.weightedTotalDegree (jetWeight a b (r+1)) ≤ V)
    (hrk : r < k) (hkA : k ≤ A)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hbin : ∀ i, r < i → i < k → (i.choose r : F) ≠ 0)
    (S : Finset (Polynomial F))
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P=0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter fun i => P.eval (domain i)=received i).card) :
    ((S.card * ∏ j : Fin (r+1), (a+b*j.val) : ℕ) : ℚ) ≤ V *
      ((((n-k+1)*chartBound r a b V k (2*k) : ℕ) : ℚ) / ((A-k+1 : ℕ) : ℚ)) ^ r := by
  classical
  let E := AlgebraicClosure F
  let f : F →+* E := algebraMap F E
  have hbinE : ∀ i, r < i → i < k → (i.choose r : E) ≠ 0 := by
    intro i hir hik hz
    apply hbin i hir hik
    exact f.injective (by simpa using hz)
  have hcharE : ∀ j : Fin (r+1), ((a+b*j.val : ℕ) : E) ≠ 0 := by
    intro j hz
    apply hchar j
    apply f.injective
    rw [map_natCast,map_zero]
    exact hz
  obtain ⟨center,J,hcard,hJ⟩ := exists_regular_solution_jet_family_of_exponent f Q k k (2*k)
    (taylorExponentSufficient_two_mul r k) le_rfl S domain received hdegree hsol hsep hbinE hagree
  let QE := MvPolynomial.map f Q
  have hQE : QE.weightedTotalDegree (jetWeight a b (r+1)) ≤ V := by
    apply Finset.sup_le
    intro m hm
    exact (le_weightedTotalDegree _ (MvPolynomial.support_map_subset f Q hm)).trans hQ
  let domainE : Fin n ↪ E := domain.trans ⟨f,f.injective⟩
  have hA : ∀ jet ∈ J, A ≤ {i | aeval jet
      (taylorAgreementEquation center QE k (2*k) (domainE i) (f (received i)))=0}.ncard := by
    intro jet hjet
    have heq : {i | aeval jet (taylorAgreementEquation center QE k (2*k)
        (domainE i) (f (received i)))=0} =
        ((Finset.univ.filter fun i => aeval jet (taylorAgreementEquation center QE k (2*k)
          (f (domain i)) (f (received i)))=0 : Finset (Fin n)) : Set (Fin n)) := by
      ext i
      simp only [Set.mem_setOf_eq,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and]
      rfl
    rw [heq,Set.ncard_coe_finset]
    exact (hJ jet hjet).2.2.2
  have hh := weighted_regular_jets_card a b V ha hV hcharE center QE hQE hrk hkA domainE
    (fun i => f (received i)) J (fun jet hjet => ⟨(hJ jet hjet).1,(hJ jet hjet).2.1⟩) hA
  rwa [hcard] at hh

theorem native_choose_two [CharP F 2130706433] (i : ℕ) (hi : 2 < i) (hik : i < 131073) :
    (i.choose 2 : F) ≠ 0 := by
  have hh := natCast_choose_ne_zero_of_ringChar (F := F) (D := 131072) (s := 2)
    (Or.inr (by rw [ringChar.eq F 2130706433]; norm_num)) (i-2) (by omega) (by omega)
  simpa only [Nat.sub_add_cancel (by omega : 2 ≤ i)] using hh

def weightedRegularCap : ℚ := (148 : ℚ) / 45 *
  (((131072 : ℚ)*36962583)/49164)^2

theorem regular64_card [CharP F 2130706433]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F)
    (Q : DifferentialPolynomial F 2)
    (hQ : Q.weightedTotalDegree (jetWeight 1 4 3) ≤ 148)
    (S : Finset (Polynomial F))
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last 2)) P ≠ 0)
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180236) :
    (S.card : ℚ) ≤ weightedRegularCap := by
  classical
  have hchar : ∀ j : Fin 3, ((1+4*j.val : ℕ) : F) ≠ 0 := by
    intro j hz
    have hdvd := (CharP.cast_eq_zero_iff F 2130706433 (1+4*j.val)).mp hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd
  have hh := weighted_regular_polynomial_card (r := 2) (n := 262144) (k := 131073) (A := 180236)
    1 4 148 (by decide) (by decide) hchar Q hQ
    (by decide) (by decide) domain received native_choose_two S
    (fun P hP => (hS P hP).2.1) (fun P hP => (hS P hP).1) hsep
    (fun P hP => by
      simpa [ReedSolomon.closePolynomialSet,ReedSolomon.polynomialAgreementSet] using
        (hS P hP).2.2)
  norm_num [chartBound,Fin.prod_univ_succ] at hh
  dsimp [weightedRegularCap]
  linarith

end
end Astra7
end PackSource_WeightedRegularList

section PackSource_CapSensitiveListCore
set_option autoImplicit true
/-!
Cap-sensitive order-two list consumer.

This file constructs no interpolation source and asserts no protocol claim.
The complete-list corollary explicitly requires the individual Y2-degree cap
of the specialized certificate equation; total jet degree alone is insufficient.

The intended native instantiation uses n=262144, A=177505, and k=131073
(polynomial degree at most 131072), so max k 3 is also 131073.
Exact source-surplus and protocol-budget arithmetic are separate obligations.
-/

noncomputable section

open Polynomial PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} [Field F]

/-- Safe order-two envelope: at most S top-order stages and at most nu stages
charged at order one. The latter deliberately overcounts top-order stages. -/
def capSensitiveOrderTwoBound (n A k K nu S : ℕ) : ℚ :=
  (S : ℚ) * dimensionSensitiveIncidenceProduct n A k 1 2 * (nu : ℚ) *
      ((1 + 2 * K * (nu - 1) : ℕ) : ℚ) ^ 2 +
    (nu : ℚ) ^ 2 * dimensionSensitiveIncidenceProduct n A k 1 1 *
      ((1 + 2 * K * (nu - 1) : ℕ) : ℚ)

private theorem sum_map_ite_add_const {α : Type*} (xs : List α)
    (p : α → Prop) [DecidablePred p] (hi lo : ℚ) :
    (xs.map fun x ↦ (if p x then hi else 0) + lo).sum =
      ((xs.filter fun x ↦ decide (p x)).length : ℚ) * hi + (xs.length : ℚ) * lo := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : p x
      · simp [hx, ih, Nat.cast_add, Nat.cast_one]
        ring
      · simp [hx, ih, Nat.cast_add, Nat.cast_one]
        ring

/-- A stage with bounded weight and order is bounded by the uniform charge
at those bounds. -/
theorem directJetStageCharge_le_weight_order
    {d : ℕ} (stage : SeparantStage F d)
    (n A k K nu r : ℕ) (hAn : A ≤ n)
    (hweight : jetTotalDegree stage.1 ≤ nu) (horder : stage.2.val ≤ r) :
    directJetStageCharge n A k K stage ≤
      dimensionSensitiveIncidenceProduct n A k 1 r * (nu : ℚ) *
        ((1 + 2 * K * (nu - 1) : ℕ) : ℚ) ^ r := by
  have hp := dimensionSensitiveIncidenceProduct_mono_dimension
    (n := n) (A := A) (k := k) (b := 1) hAn Nat.zero_lt_one horder
  have hbase :
      (1 + 2 * K * (jetTotalDegree stage.1 - 1) : ℕ) ≤
        1 + 2 * K * (nu - 1) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left (2 * K)
      (Nat.sub_le_sub_right hweight 1)) 1
  have hb : (1 : ℚ) ≤
      ((1 + 2 * K * (nu - 1) : ℕ) : ℚ) := by
    exact_mod_cast (Nat.le_add_right 1 _)
  unfold directJetStageCharge
  calc
    dimensionSensitiveIncidenceProduct n A k 1 stage.2.val *
        (jetTotalDegree stage.1 : ℚ) *
        (1 + 2 * K * (jetTotalDegree stage.1 - 1) : ℕ) ^ stage.2.val ≤
      dimensionSensitiveIncidenceProduct n A k 1 r * (nu : ℚ) *
        ((1 + 2 * K * (nu - 1) : ℕ) : ℚ) ^ stage.2.val := by
          gcongr
          · exact mul_nonneg (dimensionSensitiveIncidenceProduct_nonneg n A k 1 r)
              (Nat.cast_nonneg _)
          · exact dimensionSensitiveIncidenceProduct_nonneg n A k 1 r
    _ ≤ dimensionSensitiveIncidenceProduct n A k 1 r * (nu : ℚ) *
        ((1 + 2 * K * (nu - 1) : ℕ) : ℚ) ^ r := by
          gcongr
          exact mul_nonneg (dimensionSensitiveIncidenceProduct_nonneg n A k 1 r)
            (Nat.cast_nonneg _)

/-- Actual separant charges for an order-two equation obey the safe cap-sensitive
envelope when its initial Y2 degree is at most S. -/
theorem directJetStageCharge_sum_le_capSensitiveOrderTwo
    {Q terminal : DifferentialPolynomial F 2}
    {stages : List (SeparantStage F 2)}
    (hchain : SeparantChain Q stages terminal)
    (n A k K nu S : ℕ) (hAn : A ≤ n)
    (hweight : jetTotalDegree Q ≤ nu)
    (htop : jetDegree Q (Fin.last 2) ≤ S) :
    (stages.map (directJetStageCharge n A k K)).sum ≤
      capSensitiveOrderTwoBound n A k K nu S := by
  classical
  let hi : ℚ := dimensionSensitiveIncidenceProduct n A k 1 2 * (nu : ℚ) *
    ((1 + 2 * K * (nu - 1) : ℕ) : ℚ) ^ 2
  let lo : ℚ := dimensionSensitiveIncidenceProduct n A k 1 1 * (nu : ℚ) *
    ((1 + 2 * K * (nu - 1) : ℕ) : ℚ)
  have hhi : 0 ≤ hi := by
    dsimp [hi]
    exact mul_nonneg
      (mul_nonneg (dimensionSensitiveIncidenceProduct_nonneg n A k 1 2)
        (Nat.cast_nonneg _)) (sq_nonneg _)
  have hlo : 0 ≤ lo := by
    dsimp [lo]
    exact mul_nonneg
      (mul_nonneg (dimensionSensitiveIncidenceProduct_nonneg n A k 1 1)
        (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hpoint : ∀ stage ∈ stages,
      directJetStageCharge n A k K stage ≤
        (if stage.2 = Fin.last 2 then hi else 0) + lo := by
    intro stage hstage
    have hw := (hchain.jetTotalDegree_le_of_mem hstage).trans hweight
    by_cases ht : stage.2 = Fin.last 2
    · have hs := directJetStageCharge_le_weight_order stage n A k K nu 2 hAn hw
        (by have := stage.2.isLt; omega : stage.2.val ≤ 2)
      simp only [ht, ↓reduceIte]
      exact hs.trans (le_add_of_nonneg_right hlo)
    · have hr : stage.2.val ≤ 1 := by
        have htval : stage.2.val ≠ 2 := by
          intro heq
          apply ht
          apply Fin.ext
          exact heq
        omega
      have hs := directJetStageCharge_le_weight_order stage n A k K nu 1 hAn hw hr
      rw [ite_eq_right ht, zero_add]
      simpa only [lo, pow_one] using hs
  have hfiltered : (stages.filter fun stage ↦ stage.2 = Fin.last 2).length ≤ S :=
    (hchain.length_filter_le_jetDegree (Fin.last 2)).trans htop
  have hlength : stages.length ≤ nu := hchain.length_le.trans hweight
  calc
    (stages.map (directJetStageCharge n A k K)).sum ≤
        (stages.map fun stage ↦
          (if stage.2 = Fin.last 2 then hi else 0) + lo).sum := List.sum_le_sum hpoint
    _ = ((stages.filter fun stage ↦ stage.2 = Fin.last 2).length : ℚ) * hi +
        (stages.length : ℚ) * lo :=
      sum_map_ite_add_const stages (fun stage ↦ stage.2 = Fin.last 2) hi lo
    _ ≤ (S : ℚ) * hi + (nu : ℚ) * lo := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hfiltered) hhi)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hlength) hlo)
    _ = capSensitiveOrderTwoBound n A k K nu S := by
      unfold capSensitiveOrderTwoBound
      dsimp [hi, lo]
      ring

end ReedSolomon.HiddenDerivative

namespace ReedSolomon

open HiddenDerivative

universe u
variable {F : Type u} [Field F]

open Classical in
/-- A complete fixed-word list bound from an order-two constant-received-curve
certificate, with an explicit cap on the specialized equation's Y2 degree. -/
theorem close_list_bound_of_curve_certificate_capSensitiveOrderTwo
    {n k A nu H S : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (cert : SymbolicReceivedCurve.Certificate.{0, u} A k 0 nu 2 H domain
      (fun i ↦ Polynomial.C (received i)))
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (k - 1) (max 2 nu) < ringChar F)
    (htop : jetDegree
      (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id F) 0) cert.Q)
      (Fin.last 2) ≤ S) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℚ) ≤
        capSensitiveOrderTwoBound n A k (max k 3) nu S := by
  classical
  obtain ⟨stages, terminal, list, hchain, hlist, _hmem, hactual⟩ :=
    exists_closePolynomial_list_of_curve_certificate_actualStages
      domain received cert hkA hAn hchar
  have hweight : jetTotalDegree
      (MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id F) 0) cert.Q) ≤ nu :=
    (cert.specialization_sound (RingHom.id F) (0 : F)).2.1
  have hcap := directJetStageCharge_sum_le_capSensitiveOrderTwo
    hchain n A k (max k 3) nu S hAn hweight htop
  constructor
  · rw [← hlist]
    exact list.finite_toSet
  · rw [← hlist]
    simpa only [Set.ncard_coe_finset] using hactual.trans hcap

end ReedSolomon
end
end PackSource_CapSensitiveListCore

section PackSource_C40ResultantPrimitives
set_option autoImplicit true
/-! Proved leaves of the written C40 consumer. Full multivariate resultant
degree, irreducible-factor coverage and whole-list assembly remain separate. -/
namespace Sol1.C40Primitives

open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- Sylvester Bezout specialization works even if degrees or leading
coefficients drop after the coefficient map. -/
theorem map_resultant_eq_zero_of_common_root
    {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (f g : R[X]) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (hsize : m ≠ 0 ∨ n ≠ 0)
    (z : S) (hfroot : f.eval₂ phi z = 0) (hgroot : g.eval₂ phi z = 0) :
    phi (f.resultant g m n) = 0 := by
  obtain ⟨p, q, _hp, _hq, hbezout⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg hsize
  have he := congrArg (fun t : R[X] ↦ t.eval₂ phi z) hbezout
  simpa only [eval₂_add, eval₂_mul, eval₂_C, hfroot, hgroot, zero_mul, zero_add] using he.symm

/-- The irreducible derivative resultant is nonzero over a coefficient field
when its positive highest-variable degree is below the characteristic. -/
theorem irreducible_derivative_resultant_ne_zero
    {E : Type*} [Field E] (p : ℕ) [CharP E p]
    (f : E[X]) (hirr : Irreducible f) (hpos : 0 < f.natDegree) (hlt : f.natDegree < p) :
    f.resultant f.derivative ≠ 0 := by
  have hder := Sol1.MasonSparsePlace.derivative_ne_zero_of_natDegree_pos_lt_char p f hpos hlt
  apply Polynomial.resultant_ne_zero
  apply hirr.coprime_iff_not_dvd.mpr
  intro hdvd
  have hle := Polynomial.natDegree_le_of_dvd hdvd hder
  have hltder := Polynomial.natDegree_derivative_lt (Nat.ne_of_gt hpos)
  omega

/-- The final Sylvester degree-accounting inequality, independent of the
still-missing multivariate polynomial degree transport. -/
theorem sylvester_degree_identity (v s : ℤ) :
    v * (v - 1) - ((2 * s - 1) * v - s * s) = (v - s) ^ 2 := by ring

theorem sylvester_degree_le (v s : ℤ) : (2 * s - 1) * v - s * s ≤ v * (v - 1) := by
  nlinarith [sq_nonneg (v - s)]

/-- Native characteristic supplies every binomial nonvanishing premise of
the pinned regular-stage theorem, over every field of this characteristic. -/
theorem native_binomial_guard {E : Type*} [Field E] [CharP E 2130706433]
    (r : ℕ) (_hr : r ≤ 2) (i : ℕ) (hri : r < i) (hi : i < 131073) :
    (i.choose r : E) ≠ 0 := by
  have h := natCast_choose_ne_zero_of_ringChar (D := 131072) (s := r)
    (Or.inr (by rw [ringChar.eq E 2130706433]; norm_num)) (i - r)
    (by omega) (by omega)
  simpa only [Nat.sub_add_cancel (Nat.le_of_lt hri)] using h

open Classical in
/-- Complete pinned regular-order-two branch, with the uniform total-jet cap.
This does not count singular roots or lower-order factors. -/
theorem regular_order_two_card_le
    {E : Type*} [Field E] [CharP E 2130706433]
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (Q : DifferentialPolynomial E 2) (nu : ℕ)
    (hhighest : highestActiveJet Q = some (Fin.last 2))
    (hweight : jetTotalDegree Q ≤ nu)
    (S : Finset E[X])
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last 2)) P ≠ 0)
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180236) :
    (S.card : ℚ) ≤ dimensionSensitiveIncidenceProduct 262144 180236 131073 1 2 * nu *
      ((1 + 2 * 131073 * (nu - 1) : ℕ) : ℚ) ^ 2 := by
  have hactual := finite_actualStage_regularSolutions_card_le_dimensionSensitive Q (Fin.last 2)
    hhighest 131073 131073 (by norm_num) le_rfl domain received (by norm_num) (by norm_num)
    native_binomial_guard S hsep hS
  exact hactual.trans (directJetStageCharge_le_weight_order (Q, Fin.last 2)
    262144 180236 131073 131073 nu 2 (by norm_num) hweight (by norm_num))


end Sol1.C40Primitives
end PackSource_C40ResultantPrimitives

section PackSource_C57SingularCoverage
set_option autoImplicit true
namespace Sol1.C57
open Polynomial PolynomialDifferential MvPolynomial
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {E : Type*} [Field E]

/-- The derivative resultant has the sharp remaining-jet degree v(v-1). -/
theorem singular_weight (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    jetTotalDegree (singularEquation d Q) ≤
      jetTotalDegree (regularPart d Q) * (jetTotalDegree (regularPart d Q) - 1) := by
  unfold singularEquation jetTotalDegree
  apply Sol1.C58.weighted_derivative_resultant_le
  intro i hi
  have hi' : i ≤ degreeOf none (radicalPrimPart none (topReindex d Q)) := by
    simpa only [ordinaryRootPolynomial, natDegree_optionEquivLeft] using hi
  have h := coeff_weight_add_le jetDegreeWeight
    (radicalPrimPart none (topReindex d Q)) i hi'
  change i + ((optionEquivLeft E (JetVariable d)
    (radicalPrimPart none (topReindex d Q))).coeff i).weightedTotalDegree jetDegreeWeight ≤ _
  exact h.trans_eq (regular_weight d Q)

/-- Common-root specialization uses Bezout, so it also covers leading-degree drops. -/
theorem singular_root (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) (P : E[X])
    (hpos : 0 < jetDegree (regularPart d Q) (Fin.last (d + 1)))
    (hroot : differentialSpecialization (regularPart d Q) P = 0)
    (hsep : differentialSpecialization (separant (regularPart d Q) (Fin.last (d + 1))) P = 0) :
    differentialSpecialization (singularEquation d Q) P = 0 := by
  let f := ordinaryRootPolynomial (topReindex d Q)
  have hb : f.natDegree = jetDegree (regularPart d Q) (Fin.last (d + 1)) := by
    change (ordinaryRootPolynomial (topReindex d Q)).natDegree = _
    rw [← regular_presentation d Q, topPresentation_degree]
  change (differentialSpecializationHom P).toRingHom
    (Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1)) = 0
  apply Sol1.C40Primitives.map_resultant_eq_zero_of_common_root
    (differentialSpecializationHom P).toRingHom f f.derivative f.natDegree (f.natDegree - 1)
    le_rfl (Polynomial.natDegree_derivative_le f) (Or.inl (by omega))
    (Polynomial.hasseDeriv (d + 1) P)
  · change f.eval₂ _ _ = 0
    rw [show f = topPresentation d (regularPart d Q) from (regular_presentation d Q).symm,
      topPresentation_eval]
    exact hroot
  · change f.derivative.eval₂ _ _ = 0
    rw [show f = topPresentation d (regularPart d Q) from (regular_presentation d Q).symm,
      topPresentation_derivative, topPresentation_eval]
    exact hsep

def exceptionalEquation (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    DifferentialPolynomial E d := lowerPart d Q * singularEquation d Q

theorem exceptional_ne_zero (d : ℕ) (Q : DifferentialPolynomial E (d + 1))
    (hchar : ringChar E = 0 ∨ jetDegree Q (Fin.last (d + 1)) < ringChar E) :
    exceptionalEquation d Q ≠ 0 :=
  mul_ne_zero (lower_ne_zero d Q) (singularEquation_ne_zero d Q hchar)

/-- Full singular/lower-order coverage for an arbitrary input equation. -/
theorem root_regular_or_exceptional (d : ℕ) (Q : DifferentialPolynomial E (d + 1))
    (hQ : Q ≠ 0) (P : E[X]) (hroot : differentialSpecialization Q P = 0)
    (hpos : 0 < jetDegree (regularPart d Q) (Fin.last (d + 1))) :
    (differentialSpecialization (regularPart d Q) P = 0 ∧
      differentialSpecialization (separant (regularPart d Q) (Fin.last (d + 1))) P ≠ 0) ∨
    differentialSpecialization (exceptionalEquation d Q) P = 0 := by
  rcases root_split d Q hQ P hroot with hc | hr
  · right
    simp only [exceptionalEquation, differentialSpecialization, map_mul]
    change differentialSpecialization (lowerPart d Q) P * _ = 0
    rw [hc, zero_mul]
  · by_cases hs : differentialSpecialization
        (separant (regularPart d Q) (Fin.last (d + 1))) P = 0
    · right
      have hz := singular_root d Q P hpos hr hs
      simp only [exceptionalEquation, differentialSpecialization, map_mul]
      change _ * differentialSpecialization (singularEquation d Q) P = 0
      rw [hz, mul_zero]
    · exact Or.inl ⟨hr,hs⟩

theorem exceptional_weight (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) :
    jetTotalDegree (exceptionalEquation d Q) ≤ jetTotalDegree (lowerPart d Q) +
      jetTotalDegree (regularPart d Q) * (jetTotalDegree (regularPart d Q) - 1) := by
  apply (weightedTotalDegree_mul_le jetDegreeWeight _ _).trans
  exact Nat.add_le_add_left (singular_weight d Q) _

theorem degree_budget_sharp (c v h : ℕ) (hv : 0 < v) (hb : c + v ≤ h) :
    c + v * (v - 1) ≤ h * (h - 1) := by
  have hvh : v ≤ h := by omega
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hvh
  have hct : c ≤ t := by omega
  cases v with
  | zero => omega
  | succ v =>
    have hs : v + 1 + t - 1 = v + t := by omega
    simp only [Nat.succ_sub_one, hs]
    nlinarith [Nat.zero_le (v*t), Nat.zero_le (t*t)]

/-- Shared content/regular degree budget gives the sharp first-order exceptional charge. -/
theorem exceptional_weight_sharp (d : ℕ) (Q : DifferentialPolynomial E (d + 1)) (h : ℕ)
    (hweight : jetTotalDegree Q ≤ h) (hpos : 0 < jetTotalDegree (regularPart d Q)) :
    jetTotalDegree (exceptionalEquation d Q) ≤ h * (h - 1) :=
  (exceptional_weight d Q).trans (degree_budget_sharp _ _ _ hpos ((split_weight d Q).trans hweight))

end
end Sol1.C57
end PackSource_C57SingularCoverage

section PackSource_C57CountingPrimitives
set_option autoImplicit true
namespace Sol1.C57
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {E : Type*} [Field E]

/-- The pinned order-zero conversion is injective. -/
theorem orderZeroAsPolynomial_injective :
    Function.Injective (orderZeroAsPolynomial (F := E)) := by
  intro Q R h
  apply (MvPolynomial.renameEquiv E orderZeroVariableEquiv).injective
  apply (MvPolynomial.finSuccEquiv E 1).injective
  apply Polynomial.map_injective (MvPolynomial.uniqueAlgEquiv E (Fin 1)).toRingHom
    (MvPolynomial.uniqueAlgEquiv E (Fin 1)).injective
  exact h

theorem orderZeroAsPolynomial_degree (Q : DifferentialPolynomial E 0) :
    (orderZeroAsPolynomial Q).natDegree = jetTotalDegree Q := by
  have hleft : orderZeroOfPolynomial (orderZeroAsPolynomial Q) = Q := by
    apply orderZeroAsPolynomial_injective
    exact orderZeroAsPolynomial_orderZeroOfPolynomial _
  simpa only [hleft] using (orderZeroOfPolynomial_jetTotalDegree (orderZeroAsPolynomial Q)).symm

/-- The entire ordinary polynomial root family of a nonzero order-zero equation. -/
theorem order_zero_card_le (Q : DifferentialPolynomial E 0) (hQ : Q ≠ 0)
    (S : Finset E[X]) (hroot : ∀ P ∈ S, differentialSpecialization Q P = 0) :
    S.card ≤ jetTotalDegree Q := by
  have hP : orderZeroAsPolynomial Q ≠ 0 := by
    intro hz
    apply hQ
    apply orderZeroAsPolynomial_injective
    simpa only [orderZeroAsPolynomial, map_zero, Polynomial.map_zero] using hz
  have h := Polynomial.card_le_natDegree_of_injOn_of_eval_eq_zero hP
    (x := id) (s := S) Function.injective_id.injOn
    (fun P hP ↦ (orderZeroAsPolynomial_eval Q P).trans (hroot P hP))
  exact h.trans_eq (orderZeroAsPolynomial_degree Q)

section Native
variable [CharP E 2130706433]

/-- Native dimension-sensitive regular branch, uniformly at any order d<=2. -/
theorem regular_top_card_le (d : ℕ) (hd : d ≤ 2)
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (Q : DifferentialPolynomial E d) (nu : ℕ)
    (hhighest : highestActiveJet Q = some (Fin.last d)) (hweight : jetTotalDegree Q ≤ nu)
    (S : Finset E[X])
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last d)) P ≠ 0)
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180236) :
    (S.card : ℚ) ≤ dimensionSensitiveIncidenceProduct 262144 180236 131073 1 d * nu *
      ((1 + 2 * 131073 * (nu - 1) : ℕ) : ℚ) ^ d := by
  have hactual := finite_actualStage_regularSolutions_card_le_dimensionSensitive Q (Fin.last d)
    hhighest 131073 131073 (by omega) le_rfl domain received (by norm_num) (by norm_num)
    (fun r hr ↦ Sol1.C40Primitives.native_binomial_guard r (hr.trans hd)) S hsep hS
  exact hactual.trans (directJetStageCharge_le_weight_order (Q, Fin.last d)
    262144 180236 131073 131073 nu d (by norm_num) hweight (by simp))

end Native

/-- A positive top degree makes the top variable the computed highest active jet. -/
theorem highestActiveJet_last_of_pos {d : ℕ} (Q : DifferentialPolynomial E d)
    (hpos : 0 < jetDegree Q (Fin.last d)) : highestActiveJet Q = some (Fin.last d) := by
  cases hh : highestActiveJet Q with
  | none =>
    exact False.elim (((highestActiveJet_eq_none_iff Q).mp hh) _ hpos)
  | some j =>
    have hj := isHighestActiveJet_of_highestActiveJet_eq_some hh
    have heq : j = Fin.last d := by
      by_contra hne
      have hlt : j < Fin.last d := lt_of_le_of_ne (Fin.le_last j) hne
      exact hj.2 _ hlt hpos
    exact congrArg some heq

end
end Sol1.C57
end PackSource_C57CountingPrimitives

section PackSource_C57FirstOrderConsumer
set_option autoImplicit true
namespace Sol1.C57
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open Sol1.C42
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {E : Type*} [Field E] [CharP E 2130706433]

theorem incidence_one : dimensionSensitiveIncidenceProduct 262144 180236 131073 1 1 = I1 := by
  norm_num [dimensionSensitiveIncidenceProduct, I1]
theorem incidence_two : dimensionSensitiveIncidenceProduct 262144 180236 131073 1 2 = I2 := by
  norm_num [dimensionSensitiveIncidenceProduct, I2, I1]

theorem cast_mul_pred (h : ℕ) : ((h * (h - 1) : ℕ) : ℚ) = (h : ℚ) * (h - 1) := by
  cases h with
  | zero => norm_num
  | succ h => simp [Nat.cast_add, Nat.cast_mul]

theorem firstOrderCharge_ge (h : ℕ) : (h : ℚ) ≤ firstOrderCharge h := by
  have hi : (1 : ℚ) ≤ I1 := by norm_num [I1]
  have hI : 0 ≤ I1 := by norm_num [I1]
  have hb : (1 : ℚ) ≤ (b h : ℚ) := by
    exact_mod_cast (by unfold b; omega : 1 ≤ b h)
  have hprod : 0 ≤ (h : ℚ) * (h - 1) := by
    rw [← cast_mul_pred]
    positivity
  have h1 : (h : ℚ) ≤ I1 * h := by nlinarith [Nat.cast_nonneg (α := ℚ) h]
  have h2 : I1 * h ≤ I1 * h * b h :=
    le_mul_of_one_le_right (mul_nonneg hI (Nat.cast_nonneg _)) hb
  exact (h1.trans h2).trans (le_add_of_nonneg_right hprod)

/-- Sharp whole first-order fixed-word consumer, including every singular/lower-order root. -/
theorem first_order_card_le
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (Q : DifferentialPolynomial E 1) (hQ : Q ≠ 0) (h : ℕ) (hbound : h ≤ 4096)
    (hweight : jetTotalDegree Q ≤ h) (S : Finset E[X])
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180236) :
    (S.card : ℚ) ≤ firstOrderCharge h := by
  classical
  let G := regularPart 0 Q
  have hsplit := split_weight 0 Q
  have hGweight : jetTotalDegree G ≤ h := by dsimp [G]; omega
  have hchar : ringChar E = 0 ∨ jetDegree Q (Fin.last 1) < ringChar E := by
    right
    rw [ringChar.eq E 2130706433]
    have hh := jetDegree_le_total Q (Fin.last 1)
    omega
  by_cases hb : jetDegree G (Fin.last 1) = 0
  · have hGone : G = 1 := regular_eq_one_of_degree_zero 0 Q hb
    have hlow : ∀ P ∈ S, differentialSpecialization (lowerPart 0 Q) P = 0 := by
      intro P hP
      rcases root_split 0 Q hQ P (hS P hP).1 with hc | hr
      · exact hc
      · change differentialSpecialization G P = 0 at hr
        rw [hGone] at hr
        have hz : (1 : E[X]) = 0 := by
          simpa only [differentialSpecialization, map_one] using hr
        exact (one_ne_zero hz).elim
    have hc := order_zero_card_le (lowerPart 0 Q) (lower_ne_zero 0 Q) S hlow
    have hch : S.card ≤ h := by omega
    exact (by exact_mod_cast hch : (S.card : ℚ) ≤ h).trans (firstOrderCharge_ge h)
  · have hbpos : 0 < jetDegree G (Fin.last 1) := by omega
    let good : E[X] → Prop := fun P ↦ differentialSpecialization G P = 0 ∧
      differentialSpecialization (separant G (Fin.last 1)) P ≠ 0
    let regular := S.filter good
    let exceptional := S.filter fun P ↦ ¬ good P
    have hreg : (regular.card : ℚ) ≤ I1 * h * b h := by
      have hx := regular_top_card_le 1 (by norm_num) domain received G h
        (highestActiveJet_last_of_pos G hbpos) hGweight regular
        (by intro P hP; exact ((Finset.mem_filter.mp hP).2).2)
        (by
          intro P hP
          have hp := Finset.mem_filter.mp hP
          exact ⟨hp.2.1,(hS P hp.1).2⟩)
      simpa only [incidence_one, pow_one, b] using hx
    let R := exceptionalEquation 0 Q
    have hR : R ≠ 0 := exceptional_ne_zero 0 Q hchar
    have hRweight : jetTotalDegree R ≤ h * (h - 1) :=
      exceptional_weight_sharp 0 Q h hweight
        (hbpos.trans_le (jetDegree_le_total G (Fin.last 1)))
    have hexc : exceptional.card ≤ h * (h - 1) := by
      apply (order_zero_card_le R hR exceptional ?_).trans hRweight
      intro P hP
      have hp := Finset.mem_filter.mp hP
      rcases root_regular_or_exceptional 0 Q hQ P (hS P hp.1).1 hbpos with hg | he
      · exact (hp.2 hg).elim
      · exact he
    have hcard : regular.card + exceptional.card = S.card :=
      Finset.card_filter_add_card_filter_not (s := S) (p := good)
    calc
      (S.card : ℚ) = (regular.card : ℚ) + exceptional.card := by exact_mod_cast hcard.symm
      _ ≤ I1 * h * b h + ((h * (h - 1) : ℕ) : ℚ) :=
        add_le_add hreg (by exact_mod_cast hexc)
      _ = firstOrderCharge h := by rw [cast_mul_pred]; rfl

end
end Sol1.C57
end PackSource_C57FirstOrderConsumer

section PackSource_ReciprocalIRSAdapter
set_option autoImplicit true
/-! Actual IsMCA inclusion for the repeated-row reciprocal family. -/

namespace Sol1.Reciprocal

noncomputable section
open Polynomial Code LinearCode CoreDefinitions

variable {F K I : Type} [Field F] [Field K] [Fintype K] [Fintype I]

def liftedDomain (phi : F →+* K) (nodes : I ↪ F) : I ↪ K :=
  nodes.trans ⟨phi, phi.injective⟩

open Classical in
def baseNodeSet (nodes : I ↪ F) : Finset F := Finset.univ.image nodes

omit [Field F] in
theorem baseNodeSet_card (nodes : I ↪ F) : (baseNodeSet nodes).card = Fintype.card I := by
  classical
  unfold baseNodeSet
  rw [Finset.card_image_of_injective _ nodes.injective, Finset.card_univ]

open Classical in
omit [Field F] in
theorem mem_baseNodeSet (nodes : I ↪ F) (x : F) :
    x ∈ baseNodeSet nodes ↔ ∃ i, nodes i = x := by
  simp [baseNodeSet]

def repeatPoleInputs (phi : F →+* K) (nodes : I ↪ F) (w : F → F) (alpha : K) :
    Fin 2 → I → Fin 8 → K :=
  fun j i _ ↦ if j = 0 then phi (w (nodes i)) / (phi (nodes i) - alpha)
    else -1 / (phi (nodes i) - alpha)

noncomputable def repeatedRS (phi : F →+* K) (nodes : I ↪ F) (k : ℕ) :
    ModuleCode I K (Fin 8 → K) :=
  Code.ModuleCode.moduleInterleavedCode K K (Fin 8) I
    (ReedSolomon.code (liftedDomain phi nodes) k)

open Classical in
/-- Every scalar pole-MCA seed is an actual affine-line MCA seed for the
eight identical rows, on the same support and at the stated real radius. -/
theorem pole_mca_isMCA_repeat
    (phi : F →+* K) (nodes : I ↪ F) (w : F → F)
    (alpha gamma : K) (k A : ℕ) (delta : ℝ)
    (hk : 0 < k) (hkA : k < A)
    (hthreshold : (Fintype.card I : ℝ) * (1 - delta) ≤ A)
    (halpha : ∀ x ∈ baseNodeSet nodes, phi x ≠ alpha)
    (hgamma : gamma ∈ poleMCASet phi (baseNodeSet nodes) w alpha k A) :
    IsMCA (AffineLineGenerator K) (repeatedRS phi nodes k) gamma
      (repeatPoleInputs phi nodes w alpha) delta := by
  classical
  have : NeZero k := ⟨by omega⟩
  obtain ⟨S, hSD, hAS, hdecode, _⟩ := hgamma
  obtain ⟨h, hh, heval⟩ := hdecode
  let T : Finset I := Finset.univ.filter fun i ↦ nodes i ∈ S
  have himage : T.image nodes = S := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
    · intro hx
      obtain ⟨i, _hi, heq⟩ := Finset.mem_image.mp (hSD hx)
      exact Finset.mem_image.mpr ⟨i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [heq] using hx⟩, heq⟩
  have hTcard : T.card = S.card := by
    calc
      T.card = (T.image nodes).card :=
        (Finset.card_image_of_injective T nodes.injective).symm
      _ = S.card := congrArg Finset.card himage
  have hnode : ∀ i ∈ T, nodes i ∈ S := fun i hi ↦ (Finset.mem_filter.mp hi).2
  change ∃ T : Finset I, (T.card : ℝ) ≥ Fintype.card I * (1 - delta) ∧ _
  refine ⟨T, hthreshold.trans ?_, ?_, (1 : Fin 2), ?_⟩
  · exact_mod_cast (show A ≤ T.card by omega)
  · apply Submodule.mem_map.mpr
    refine ⟨(fun i (_ : Fin 8) ↦ h.eval (phi (nodes i))), ?_, ?_⟩
    · change ∀ _row : Fin 8,
        (fun i ↦ h.eval (phi (nodes i))) ∈ ReedSolomon.code (liftedDomain phi nodes) k
      intro row
      exact ReedSolomon.evalOnPoints_mem_code_of_natDegree_lt hh
    · ext i row
      change h.eval (phi (nodes i.val)) =
        ∑ j, AffineLineGenerator K gamma j • repeatPoleInputs phi nodes w alpha j i.val row
      rw [heval (nodes i.val) (hnode i.val i.property)]
      simp [Fin.sum_univ_two, AffineLineGenerator, repeatPoleInputs, smul_eq_mul]
      ring
  · intro hbad
    obtain ⟨c, hc, hcT⟩ :=
      (mem_projectedCodeSubmod_iff (repeatedRS phi nodes k) T _).mp hbad
    have hrow : (fun i ↦ c i (0 : Fin 8)) ∈
        ReedSolomon.code (liftedDomain phi nodes) k := hc (0 : Fin 8)
    obtain ⟨g, hg, hgeval⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hrow
    apply pole_direction_never_extends phi S alpha k (hkA.trans_le hAS)
      (fun x hx ↦ halpha x (hSD hx))
    refine ⟨g, hg, ?_⟩
    intro x hx
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (himage.symm ▸ hx)
    have he := congrFun (congrFun hcT ⟨i, hi⟩) (0 : Fin 8)
    change repeatPoleInputs phi nodes w alpha 1 i 0 = c i 0 at he
    rw [← heq]
    exact (hgeval i).trans (by simpa [repeatPoleInputs] using he.symm)

open Classical in
/-- A uniform actual repeated-IRS MCA cap supplies the scalar pole cap. -/
theorem pole_cap_of_actual_cap
    (phi : F →+* K) (nodes : I ↪ F) (w : F → F) (k A B : ℕ) (delta : ℝ)
    (hk : 0 < k) (hkA : k < A)
    (hthreshold : (Fintype.card I : ℝ) * (1 - delta) ≤ A)
    (hcap : ∀ U : Fin 2 → I → Fin 8 → K,
      {gamma | IsMCA (AffineLineGenerator K) (repeatedRS phi nodes k) gamma U delta}.ncard ≤ B)
    (alpha : K) (halpha : ∀ x ∈ baseNodeSet nodes, phi x ≠ alpha) :
    (poleMCASet phi (baseNodeSet nodes) w alpha k A).ncard ≤ B := by
  apply (Set.ncard_le_ncard (t := {gamma | IsMCA (AffineLineGenerator K)
    (repeatedRS phi nodes k) gamma (repeatPoleInputs phi nodes w alpha) delta}) ?_).trans
      (hcap (repeatPoleInputs phi nodes w alpha))
  intro gamma hgamma
  exact pole_mca_isMCA_repeat phi nodes w alpha gamma k A delta hk hkA
    hthreshold halpha hgamma

open Classical in
/-- Necessary ordinary base-list bound conditional on a universal actual MCA cap. -/
theorem base_list_bound_of_actual_repeated_cap
    (phi : F →+* K) (nodes : I ↪ F) (w : F → F) (k A B : ℕ) (delta : ℝ)
    (hk : 0 < k) (hkA : k < A)
    (hthreshold : (Fintype.card I : ℝ) * (1 - delta) ≤ A)
    (hroom : (baseNodeSet nodes).card + k * (B + 1) ^ 2 < Fintype.card K)
    (hcap : ∀ U : Fin 2 → I → Fin 8 → K,
      {gamma | IsMCA (AffineLineGenerator K) (repeatedRS phi nodes k) gamma U delta}.ncard ≤ B) :
    (baseCloseSet (baseNodeSet nodes) w k A).Finite ∧
      (baseCloseSet (baseNodeSet nodes) w k A).ncard ≤ B := by
  apply base_list_finite_ncard_le_of_pole_cap phi (baseNodeSet nodes) w k A B hk hkA hroom
  exact pole_cap_of_actual_cap phi nodes w k A B delta hk hkA hthreshold hcap


end
end Sol1.Reciprocal
end PackSource_ReciprocalIRSAdapter

section PackSource_C64InterleavingTransfer
set_option autoImplicit true
/-! Restricted-input MCA interleaving transfer. One common row functional
preserves every selected ACTUAL same-support witness and the input subcode. -/
namespace Sol1.C64
open Code LinearCode CoreDefinitions
noncomputable section
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 0
variable {K I R : Type} [Field K] [Fintype K] [Fintype I] [Fintype R]

theorem exists_projected_bad_family (C D : ModuleCode I K K) (delta : ℝ)
    (U : Fin 2 → I → R → K) (hU : ∀ j r, (fun i ↦ U j i r) ∈ D)
    (S : Finset K) (hs : (S.card : ℕ∞) ≤ ENat.card K)
    (hbad : ∀ gamma ∈ S, IsMCA (AffineLineGenerator K) (C^⋈R) gamma U delta) :
    ∃ V : Fin 2 → I → K, (∀ j, V j ∈ D) ∧
      ∀ gamma ∈ S, IsMCA (AffineLineGenerator K) C gamma V delta := by
  classical
  choose! T hT using hbad
  obtain ⟨lambda,hlambda⟩ := Code.exists_rowFunctional_forall_notMem C U S T hs
    (fun gamma hg ↦ (hT gamma hg).2.2)
  let V : Fin 2 → I → K := fun j i ↦ ∑ r, lambda r • U j i r
  refine ⟨V,?_,?_⟩
  · intro j
    have heq : V j = ∑ r, lambda r • (fun i ↦ U j i r) := by
      ext i
      simp [V]
    rw [heq]
    exact D.sum_mem (fun r _ ↦ D.smul_mem (lambda r) (hU j r))
  · intro gamma hg
    refine ⟨T gamma,(hT gamma hg).1,?_,hlambda gamma hg⟩
    have hcomb := Code.projectedWord_rowCombination_mem C _ (T gamma) lambda (hT gamma hg).2.1
    have hfun : (fun i ↦ ∑ r, lambda r • (∑ j, (AffineLineGenerator K gamma j) • U j i) r) =
        fun i ↦ ∑ j, (AffineLineGenerator K gamma j) • V j i := by
      funext i
      simp only [V,Finset.sum_apply,Pi.smul_apply,Finset.smul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun r _ ↦ smul_comm _ _ _
    rwa [hfun] at hcomb

/-- A scalar input-subcode MCA cap transfers with the SAME count to full row-wise input subcodes.
Only a B+1 counterexample is projected; its field-room hypothesis is explicit. -/
theorem restricted_interleaved_card_le (C D : ModuleCode I K K) (delta : ℝ) (B : ℕ)
    (hroom : B+1 ≤ Fintype.card K)
    (hscalar : ∀ V : Fin 2 → I → K, (∀ j, V j ∈ D) → ∀ S : Finset K,
      (∀ gamma ∈ S, IsMCA (AffineLineGenerator K) C gamma V delta) → S.card ≤ B)
    (U : Fin 2 → I → R → K) (hU : ∀ j r, (fun i ↦ U j i r) ∈ D)
    (S : Finset K) (hbad : ∀ gamma ∈ S, IsMCA (AffineLineGenerator K) (C^⋈R) gamma U delta) :
    S.card ≤ B := by
  classical
  by_contra hlarge
  have hsize : B+1 ≤ S.card := by omega
  obtain ⟨Q,hQS,hQcard⟩ := Finset.exists_subset_card_eq hsize
  have hroom' : (Q.card : ℕ∞) ≤ ENat.card K := by
    rw [hQcard,ENat.card_eq_coe_fintype_card]
    exact_mod_cast hroom
  obtain ⟨V,hV,hbadV⟩ := exists_projected_bad_family C D delta U hU Q hroom'
    (fun gamma hg ↦ hbad gamma (hQS hg))
  have hcount := hscalar V hV Q hbadV
  rw [hQcard] at hcount
  omega

end
end Sol1.C64
end PackSource_C64InterleavingTransfer
