import ProximityPrize.SubmissionBinaryLower.B6401Params
import ProximityPrize.SubmissionBinaryLower.B6401FarkasVerifier
import ProximityPrize.SubmissionBinaryLower.B6401ContactKerD
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Equation
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
import Mathlib.Tactic

set_option Elab.async false

/-!
# ArkLib ordinary-equation bridge, `ScalarList → Lambda(SquaredCode)`, and `ProtocolClaim 6401`

Bridges our eliminated 3-variable polynomials `Φ ∈ F[Z][X][Y]` directly into ArkLib's
`ReedSolomon.exists_baseExceptional_ordinaryPowerEquation` and `ReedSolomon.mcaError_affineLine_le_of_exactAgreement`,
proves the 15-line random-linear-combination reduction `ScalarList ≤ L → Lambda(SquaredCode, δ) ≤ L`,
and assembles `ProtocolClaim 6401 78633206 268435456`!
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6401ListAndMCA

open Polynomial MvPolynomial PolynomialDifferential ReedSolomon
open CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open B6401Params B6401FarkasVerifier B6401ContactKerD
open scoped BigOperators NNReal Polynomial

local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index

/-! ### Part 1: Bridge `BiPoly (Polynomial F)` → `DifferentialPolynomial F[X] 0` → ArkLib -/

/-- Specialize `Z ↦ z` on `BiPoly (Polynomial F) = F[Z][X][Y]`. -/
noncomputable def evalZBiPoly {F : Type*} [CommRing F] (Φ : BiPoly (Polynomial F)) (z : F) :
    BiPoly F :=
  Φ.map (Polynomial.mapRingHom (evalRingHom z))

/-- Canonical ring homomorphism `F[Z][X][Y] →+* DifferentialPolynomial F[X] 0`:
`Z ↦ C`, `X ↦ X none`, `Y ↦ X (some 0)`. -/
noncomputable def biPolyToDiffPoly {F : Type*} [CommRing F] :
    BiPoly (Polynomial F) →+* DifferentialPolynomial (Polynomial F) 0 :=
  eval₂RingHom
    (eval₂RingHom MvPolynomial.C (MvPolynomial.X none))
    (MvPolynomial.X (some 0))

lemma coeff_biPolyToDiffPoly {F : Type*} [CommRing F] (Φ : BiPoly (Polynomial F))
    (m : Option (Fin 1) →₀ ℕ) :
    (biPolyToDiffPoly Φ).coeff m = (Φ.coeff (m (some 0))).coeff (m none) := by
  classical
  -- Prove by expanding Φ = ∑ j, ∑ i, C(C(a_{j,i})) * X^i * Y^j!
  let a := m none
  let b := m (some 0)
  have hm_eq : m = Finsupp.single none a + Finsupp.single (some 0) b := by
    ext x
    rcases x with _ | x
    · simp [a]
    · fin_cases x; simp [b]
  -- Evaluate biPolyToDiffPoly via double sum over j ∈ Φ.support, i ∈ (Φ.coeff j).support
  have hsum : biPolyToDiffPoly Φ =
      ∑ j ∈ Φ.support, ∑ i ∈ (Φ.coeff j).support,
        MvPolynomial.monomial (Finsupp.single none i + Finsupp.single (some 0) j)
          ((Φ.coeff j).coeff i) := by
    unfold biPolyToDiffPoly
    change Polynomial.eval₂ _ _ Φ = _
    rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    apply Finset.sum_congr rfl; intro j _
    change Polynomial.eval₂ _ _ (Φ.coeff j) * _ = _
    rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    rw [MvPolynomial.monomial_eq, Finsupp.prod_add_index']
    · simp [Finsupp.prod_single_index, mul_assoc]
    · intro _; simp
    · intro _ _ _; rw [pow_add]
  rw [hsum, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  have hfin_eq : ∀ j i,
      (Finsupp.single (none : Option (Fin 1)) i + Finsupp.single (some 0) j = m) ↔ (j = b ∧ i = a) := by
    intro j i
    constructor
    · intro h
      have h1 := congrArg (fun f : Option (Fin 1) →₀ ℕ => f (some 0)) h
      have h2 := congrArg (fun f : Option (Fin 1) →₀ ℕ => f none) h
      simp only [Finsupp.add_apply, Finsupp.single_apply, reduceCtorEq, ↓reduceIte, zero_add, add_zero] at h1 h2
      exact ⟨h1, h2⟩
    · rintro ⟨rfl, rfl⟩; exact hm_eq.symm
  simp_rw [hfin_eq]
  by_cases hb : b ∈ Φ.support
  · rw [Finset.sum_eq_single b]
    · by_cases ha : a ∈ (Φ.coeff b).support
      · rw [Finset.sum_eq_single a]
        · simp [a, b]
        · intro i _ hne; simp [hne]
        · intro h; exact absurd ha h
      · have h0 : (Φ.coeff b).coeff a = 0 := by simpa [Polynomial.mem_support_iff] using ha
        rw [h0]
        apply Finset.sum_eq_zero; intro i hi
        have hne : i ≠ a := fun h => ha (h ▸ hi)
        simp [hne]
    · intro j _ hne
      apply Finset.sum_eq_zero; intro i _; simp [hne]
    · intro h; exact absurd hb h
  · have h0 : Φ.coeff b = 0 := by simpa [Polynomial.mem_support_iff] using hb
    rw [h0, Polynomial.coeff_zero]
    apply Finset.sum_eq_zero; intro j hj
    apply Finset.sum_eq_zero; intro i _
    have hne : j ≠ b := fun h => hb (h ▸ hj)
    simp [hne]

lemma biPolyToDiffPoly_ne_zero {F : Type*} [CommRing F] {Φ : BiPoly (Polynomial F)} (hΦ : Φ ≠ 0) :
    biPolyToDiffPoly Φ ≠ 0 := by
  intro h0
  apply hΦ
  apply Polynomial.ext; intro j
  apply Polynomial.ext; intro i
  have hm := congrArg (fun p : DifferentialPolynomial (Polynomial F) 0 =>
    p.coeff (Finsupp.single none i + Finsupp.single (some 0) j)) h0
  rw [coeff_biPolyToDiffPoly] at hm
  simpa using hm

lemma degreeOf_biPolyToDiffPoly_le {F : Type*} [CommRing F] (Φ : BiPoly (Polynomial F)) :
    (biPolyToDiffPoly Φ).degreeOf (some 0) ≤ Φ.natDegree := by
  rw [MvPolynomial.degreeOf_eq_sup]
  apply Finset.sup_le
  intro m hm
  have hne : (biPolyToDiffPoly Φ).coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  rw [coeff_biPolyToDiffPoly] at hne
  have hne_j : Φ.coeff (m (some 0)) ≠ 0 := fun h => hne (by simp [h])
  exact le_natDegree_of_ne_zero hne_j

lemma coeffNatDegreeLE_biPolyToDiffPoly {F : Type*} [CommRing F] (Φ : BiPoly (Polynomial F))
    {H : ℕ} (hH : ∀ j i, ((Φ.coeff j).coeff i).natDegree ≤ H) :
    MvPolynomial.CoeffNatDegreeLE (biPolyToDiffPoly Φ) H := by
  intro m
  rw [coeff_biPolyToDiffPoly]
  exact hH (m (some 0)) (m none)

/-- Specialization compatibility: `differentialSpecialization (challengeSpecialization (biPolyToDiffPoly Φ) z) P`
equals `(evalZBiPoly Φ z).eval P`! -/
theorem differentialSpecialization_biPolyToDiffPoly {F : Type*} [CommRing F]
    (Φ : BiPoly (Polynomial F)) (z : F) (P : Polynomial F) :
    differentialSpecialization (challengeSpecialization (biPolyToDiffPoly Φ) z) P =
      (evalZBiPoly Φ z).eval P := by
  induction Φ using Polynomial.induction_on' with
  | add p q hp hq =>
      have h1 : biPolyToDiffPoly (p + q) = biPolyToDiffPoly p + biPolyToDiffPoly q := map_add _ _ _
      have h2 : evalZBiPoly (p + q) z = evalZBiPoly p z + evalZBiPoly q z := by
        unfold evalZBiPoly; simp [Polynomial.map_add]
      rw [h1, h2, Polynomial.eval_add]
      change differentialSpecializationHom P
        (MvPolynomial.map (Polynomial.aeval z).toRingHom (biPolyToDiffPoly p + biPolyToDiffPoly q)) = _
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) hp hq
  | monomial j a =>
      induction a using Polynomial.induction_on' with
      | add r s hr hs =>
          have h1 : Polynomial.monomial j (r + s) = Polynomial.monomial j r + Polynomial.monomial j s :=
            map_add (Polynomial.monomial j) r s
          rw [h1]
          have hm1 : biPolyToDiffPoly (Polynomial.monomial j r + Polynomial.monomial j s) =
              biPolyToDiffPoly (Polynomial.monomial j r) + biPolyToDiffPoly (Polynomial.monomial j s) := map_add _ _ _
          have hm2 : evalZBiPoly (Polynomial.monomial j r + Polynomial.monomial j s) z =
              evalZBiPoly (Polynomial.monomial j r) z + evalZBiPoly (Polynomial.monomial j s) z := by
            unfold evalZBiPoly; simp [Polynomial.map_add]
          rw [hm1, hm2, Polynomial.eval_add]
          change differentialSpecializationHom P
            (MvPolynomial.map (Polynomial.aeval z).toRingHom
              (biPolyToDiffPoly (Polynomial.monomial j r) + biPolyToDiffPoly (Polynomial.monomial j s))) = _
          rw [map_add, map_add]
          exact congrArg₂ (· + ·) hr hs
      | monomial i c =>
          have hLHS : biPolyToDiffPoly (Polynomial.monomial j (Polynomial.monomial i c)) =
              MvPolynomial.C c * MvPolynomial.X none ^ i * MvPolynomial.X (some 0) ^ j := by
            unfold biPolyToDiffPoly
            change Polynomial.eval₂ _ _ (Polynomial.monomial j (Polynomial.monomial i c)) = _
            rw [Polynomial.eval₂_monomial]
            change Polynomial.eval₂ _ _ (Polynomial.monomial i c) * _ = _
            rw [Polynomial.eval₂_monomial]
          have hRHS : (evalZBiPoly (Polynomial.monomial j (Polynomial.monomial i c)) z).eval P =
              (Polynomial.C (c.eval z) * Polynomial.X ^ i) * P ^ j := by
            unfold evalZBiPoly
            rw [Polynomial.map_monomial]
            change (Polynomial.monomial j (Polynomial.map (Polynomial.evalRingHom z) (Polynomial.monomial i c))).eval P = _
            rw [Polynomial.map_monomial, Polynomial.eval_monomial,
              Polynomial.coe_evalRingHom, ← Polynomial.C_mul_X_pow_eq_monomial]
          rw [hLHS, hRHS]
          simp [challengeSpecialization, differentialSpecialization, differentialSpecializationHom]

/-- Equivalence between `arklibBoundQ B H` and ArkLib's `ordinaryUnifiedPowerFactorAtOrHeight`! -/
theorem ordinaryUnifiedPowerFactorAtOrHeight_eq_arklibBoundQ (B H : ℕ) :
    ordinaryUnifiedPowerFactorAtOrHeight N wY 1 B H A (wY + 1) ≤ max (H : ℚ) (arklibBoundQ B H) := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · rw [ordinaryUnifiedPowerFactorAtOrHeight_zero]
    exact le_max_left _ _
  · rw [ordinaryUnifiedPowerFactorAtOrHeight_of_pos N wY 1 B H A (wY + 1) hB]
    rw [ordinaryUnifiedPowerFactorAt_succ_eq N wY 1 B H A (by norm_num [wY, A]) (by norm_num [N, A])]
    have heq : ordinaryUnifiedPowerFactorRaw (((N - wY : ℕ) : ℚ) / ((A - wY : ℕ) : ℚ)) N wY 1 B H =
        arklibBoundQ B H := by
      unfold ordinaryUnifiedPowerFactorRaw arklibBoundQ ordinaryPsi
      have hsub : B - 2 * wY - 1 = B - (2 * wY + 1) := by omega
      rw [hsub]
      push_cast
      ring
    rw [heq]
    exact le_max_right _ _

/-- **Main single-factor ArkLib bridge:**
For ANY nonzero `Φ ∈ Fld[Z][X][Y]` of `deg_Y ≤ B` and `deg_Z ≤ H`, there exists `exceptional : Finset Fld`
with `(exceptional.card : ℚ) ≤ max H (arklibBoundQ B H)` outside which every degree-`≤ wY` root `P`
of `(evalZBiPoly Φ z).eval P = 0` with `≥ A` agreements with `f + z • g` has exact correlated pair agreement! -/
theorem exists_exceptional_of_biPoly
    (f g : Idx → Fld) (Φ : BiPoly (Polynomial Fld)) (B H : ℕ)
    (hΦ : Φ ≠ 0) (hB : Φ.natDegree ≤ B) (hH : ∀ j i, ((Φ.coeff j).coeff i).natDegree ≤ H) :
    ∃ exceptional : Finset Fld,
      (exceptional.card : ℚ) ≤ max (H : ℚ) (arklibBoundQ B H) ∧
      ∀ z ∉ exceptional, ∀ P : Polynomial Fld, P.degree < (wY + 1 : ℕ) →
        (evalZBiPoly Φ z).eval P = 0 →
        A ≤ (polynomialAgreementSet BinaryIRSProfile.domain (fun i => f i + z * g i) P).card →
        HasExactCorrelatedPair BinaryIRSProfile.domain f g (RingHom.id Fld) (wY + 1) z P := by
  have hQne : biPolyToDiffPoly Φ ≠ 0 := biPolyToDiffPoly_ne_zero hΦ
  have hdeg : (biPolyToDiffPoly Φ).degreeOf (some 0) ≤ B :=
    (degreeOf_biPolyToDiffPoly_le Φ).trans hB
  have hht : MvPolynomial.CoeffNatDegreeLE (biPolyToDiffPoly Φ) H :=
    coeffNatDegreeLE_biPolyToDiffPoly Φ hH
  let dom : Fin BinaryIRSProfile.domainSize ↪ Fld := BinaryIRSProfile.domain
  let f' : Fin BinaryIRSProfile.domainSize → Fld := f
  let g' : Fin BinaryIRSProfile.domainSize → Fld := g
  obtain ⟨ex, hcard, hgood⟩ := ReedSolomon.exists_baseExceptional_ordinaryPowerEquation
    (n := BinaryIRSProfile.domainSize) (ℓ := 1) dom ![f', g'] (biPolyToDiffPoly Φ) wY H B (wY + 1) A
    hQne (by norm_num [wY]) (by norm_num [wY]) (by norm_num [wY, A]) hht hdeg
  have hcard' : (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorAtOrHeight N wY 1 B H A (wY + 1) := by
    simpa only [show BinaryIRSProfile.domainSize = N from rfl] using hcard
  refine ⟨ex, hcard'.trans (ordinaryUnifiedPowerFactorAtOrHeight_eq_arklibBoundQ B H), ?_⟩
  intro z hz P hPdeg hroot hagree
  have hword : powerBatchedWord (ℓ := 1) ![f', g'] z = (fun i => f' i + z * g' i) := by
    funext i; simp [powerBatchedWord, Fin.sum_univ_two]
  have hdiff : differentialSpecialization (challengeSpecialization (biPolyToDiffPoly Φ) z) P = 0 := by
    rw [differentialSpecialization_biPolyToDiffPoly]; exact hroot
  have hagree' : A ≤ (polynomialAgreementSet dom (fun i => f' i + z * g' i) P).card := hagree
  have hpow := hgood z hz P hPdeg hdiff (by rwa [hword])
  exact exactCorrelatedPair_of_powerAgreement_one dom ![f', g'] (RingHom.id Fld) z P hpow

/-! ### Part 2: 15-line random-linear-combination reduction `ScalarList → Lambda(SquaredCode)` -/

/-- The code interleaved twice (`baseCode ^⋈ 64 ^⋈ 2`). -/
noncomputable abbrev SquaredCode :
    Set (Idx → Fin 2 → Fin BinaryIRSProfile.interleaving → Fld) :=
  Code.interleavedCodeSet (κ := Fin 2)
    (BinaryIRSProfile.code : Set (Idx → Fin BinaryIRSProfile.interleaving → Fld))

/-- Scalar list-size bound at agreement threshold `A`: for every received word `u : Idx → Fld`,
at most `L` distinct polynomials of degree `≤ wY` agree with `u` on `≥ A` points. -/
def ScalarListBound (L : ℕ) : Prop :=
  ∀ (u : Idx → Fld) (T : Finset (Polynomial Fld)),
    (∀ p ∈ T, p.natDegree ≤ wY ∧
      A ≤ (Finset.univ.filter fun i : Idx => p.eval (BinaryIRSProfile.domain i) = u i).card) →
    T.card ≤ L

/-- Polymorphic Schwartz-Zippel separating-weights lemma:
if `T'` has `T'.card * (T'.card - 1) < |F|` elements separated by polynomial tuples `P c : ι → F[X]`,
then there exists `w : ι → F` making `c ↦ ∑ ab, C (w ab) * P c ab` injective on `T'`. -/
private lemma exists_separating_weights {F ι α : Type*} [Field F] [Fintype F]
    [Fintype ι] [Nonempty ι] (T' : Finset α) (P : α → ι → Polynomial F)
    (hsep : ∀ c1 ∈ T', ∀ c2 ∈ T', c1 ≠ c2 → ∃ ab : ι, P c1 ab ≠ P c2 ab)
    (hsmall : T'.card * (T'.card - 1) < Fintype.card F) :
    ∃ w : ι → F, Set.InjOn (fun c => ∑ ab : ι, Polynomial.C (w ab) * P c ab) (T' : Set α) := by
  classical
  let W := ι → F
  let badPair (c1 c2 : α) : Finset W :=
    Finset.univ.filter fun w : W =>
      (∑ ab : ι, Polynomial.C (w ab) * P c1 ab) = (∑ ab : ι, Polynomial.C (w ab) * P c2 ab)
  have hbad_card : ∀ c1 ∈ T', ∀ c2 ∈ T', c1 ≠ c2 →
      (badPair c1 c2).card * Fintype.card F ≤ Fintype.card W := by
    intro c1 hc1 c2 hc2 hne
    obtain ⟨ab0, hab0⟩ := hsep c1 hc1 c2 hc2 hne
    let proj : W → ({ ab : ι // ab ≠ ab0 } → F) := fun w x => w x.1
    have hinj : Set.InjOn proj (badPair c1 c2 : Set W) := by
      intro w1 hw1 w2 hw2 hproj
      have h1 : (∑ ab : ι, Polynomial.C (w1 ab) * (P c1 ab - P c2 ab)) = 0 := by
        have hm := (Finset.mem_filter.mp (Finset.mem_coe.mp hw1)).2
        simp_rw [mul_sub]; rw [Finset.sum_sub_distrib, sub_eq_zero]; exact hm
      have h2 : (∑ ab : ι, Polynomial.C (w2 ab) * (P c1 ab - P c2 ab)) = 0 := by
        have hm := (Finset.mem_filter.mp (Finset.mem_coe.mp hw2)).2
        simp_rw [mul_sub]; rw [Finset.sum_sub_distrib, sub_eq_zero]; exact hm
      have hdiff : (∑ ab : ι, Polynomial.C (w1 ab - w2 ab) * (P c1 ab - P c2 ab)) = 0 := by
        simp_rw [map_sub, sub_mul]; rw [Finset.sum_sub_distrib, h1, h2, sub_self]
      rw [Finset.sum_eq_single ab0] at hdiff
      · have hzero := (mul_eq_zero.mp hdiff).resolve_right (sub_ne_zero.mpr hab0)
        have hw0 : w1 ab0 = w2 ab0 := sub_eq_zero.mp (Polynomial.C_eq_zero.mp hzero)
        funext ab
        by_cases h : ab = ab0
        · rw [h, hw0]
        · exact congrFun hproj ⟨ab, h⟩
      · intro ab _ hne_ab
        have heq : w1 ab = w2 ab := congrFun hproj ⟨ab, hne_ab⟩
        rw [heq, sub_self, map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hle := Finset.card_le_card_of_injOn proj (fun _ _ => Finset.mem_univ _) hinj
    have hcardW : Fintype.card W = Fintype.card ({ ab : ι // ab ≠ ab0 } → F) * Fintype.card F := by
      simp only [W, Fintype.card_fun, Fintype.card_subtype_compl, Fintype.card_unique]
      have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos
      rw [← pow_succ, Nat.sub_add_cancel hpos]
    rw [hcardW]
    exact Nat.mul_le_mul_right _ (by simpa only [Finset.card_univ] using hle)
  let pairs := (T' ×ˢ T').filter fun p => p.1 ≠ p.2
  have hpairs_card : pairs.card ≤ T'.card * (T'.card - 1) := by
    have h1 : pairs.card + T'.card = (T' ×ˢ T').card := by
      have hdisj : Disjoint pairs ((T' ×ˢ T').filter fun p => p.1 = p.2) := by
        rw [Finset.disjoint_left]; intro p h1 h2
        exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
      have hunion : pairs ∪ ((T' ×ˢ T').filter fun p => p.1 = p.2) = T' ×ˢ T' := by
        ext p; simp only [pairs, Finset.mem_union, Finset.mem_filter]
        by_cases he : p.1 = p.2 <;> simp [he]
      have hdiag : ((T' ×ˢ T').filter fun p => p.1 = p.2).card = T'.card := by
        rw [show ((T' ×ˢ T').filter fun p => p.1 = p.2) = T'.image (fun c => (c, c)) from by
          ext ⟨a, b⟩; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.mk.injEq]
          constructor
          · rintro ⟨⟨ha, _⟩, rfl⟩; exact ⟨a, ha, rfl, rfl⟩
          · rintro ⟨c, hc, rfl, rfl⟩; exact ⟨⟨hc, hc⟩, rfl⟩]
        exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)
      rw [← hdiag, ← Finset.card_union_of_disjoint hdisj, hunion]
    rw [Finset.card_product] at h1
    cases hT : T'.card with
    | zero => rw [hT] at h1; omega
    | succ k => rw [hT] at h1; simp only [Nat.add_sub_cancel]; nlinarith
  let allBad := pairs.biUnion fun p => badPair p.1 p.2
  have hallBad_lt : allBad.card < Fintype.card W := by
    have h1 : allBad.card * Fintype.card F ≤ pairs.card * Fintype.card W := by
      calc allBad.card * Fintype.card F
          ≤ (∑ p ∈ pairs, (badPair p.1 p.2).card) * Fintype.card F :=
            Nat.mul_le_mul_right _ Finset.card_biUnion_le
        _ = ∑ p ∈ pairs, (badPair p.1 p.2).card * Fintype.card F := Finset.sum_mul _ _ _
        _ ≤ ∑ _p ∈ pairs, Fintype.card W := Finset.sum_le_sum fun p hp => by
            have hmem := Finset.mem_filter.mp hp
            have hprod := Finset.mem_product.mp hmem.1
            exact hbad_card p.1 hprod.1 p.2 hprod.2 hmem.2
        _ = pairs.card * Fintype.card W := by simp
    have hWpos : 0 < Fintype.card W := Fintype.card_pos
    have h2 : pairs.card * Fintype.card W < Fintype.card F * Fintype.card W :=
      Nat.mul_lt_mul_of_pos_right (lt_of_le_of_lt hpairs_card hsmall) hWpos
    have h3 : allBad.card * Fintype.card F < Fintype.card W * Fintype.card F := by linarith
    exact Nat.lt_of_mul_lt_mul_right h3
  have hex_w : ∃ w : W, w ∉ allBad := by
    by_contra hall; push Not at hall
    have hsub : (Finset.univ : Finset W) ⊆ allBad := fun w _ => hall w
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    omega
  obtain ⟨w, hw⟩ := hex_w
  refine ⟨w, fun c1 hc1 c2 hc2 heq => ?_⟩
  by_contra hne
  apply hw
  exact Finset.mem_biUnion.mpr ⟨(c1, c2), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc1, hc2⟩, hne⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩⟩

/-- **15-line random-linear-combination reduction:**
Any scalar list-size bound `L` at threshold `A` with `(L + 1) * L < 2^192` immediately gives
`Code.Lambda SquaredCode (radius : ℝ) ≤ L`! -/
theorem lambda_squaredCode_le_of_scalarList {L : ℕ} (hScalar : ScalarListBound L)
    (hLsmall : (L + 1) * L < Fintype.card Fld) :
    Code.Lambda SquaredCode (radius : ℝ) ≤ (L : ℕ∞) := by
  classical
  apply Code.Lambda_le_of_forall_finset_card_le
  intro received T hT
  by_contra hgt
  push Not at hgt
  obtain ⟨T', hT'sub, hT'card⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hgt)
  have hpoly : ∀ c ∈ T', ∀ (a : Fin 2) (b : Fin BinaryIRSProfile.interleaving),
      ∃ p : Polynomial Fld, p.natDegree ≤ wY ∧ ∀ i : Idx, p.eval (BinaryIRSProfile.domain i) = c i a b := by
    intro c hc a b
    have hmem : c ∈ SquaredCode := (Code.mem_closeCodewordsRel_iff.mp (hT c (hT'sub hc))).1
    have hrow : (fun i => c i a) ∈ (BinaryIRSProfile.code : Set _) := hmem a
    change (fun i => c i a) ∈ ReedSolomon.Interleaved.irsCode BinaryIRSProfile.domain
      BinaryIRSProfile.totalDimension BinaryIRSProfile.interleaving at hrow
    have hbase : (fun i => c i a b) ∈ ReedSolomon.code BinaryIRSProfile.domain BinaryIRSProfile.baseDimension := by
      rw [← BinaryIRSProfile.totalDimension_div_interleaving]
      exact hrow b
    rw [ReedSolomon.mem_code_iff_exists_polynomial] at hbase
    obtain ⟨p, hpdeg, hpeq⟩ := hbase
    refine ⟨p, ?_, ?_⟩
    · by_cases hp0 : p = 0
      · simp [hp0]
      · have hlt : p.natDegree < BinaryIRSProfile.baseDimension :=
          (Polynomial.natDegree_lt_iff_degree_lt hp0).2 hpdeg
        norm_num [BinaryIRSProfile.baseDimension, wY] at hlt ⊢; omega
    · intro i
      have := congrFun hpeq i
      simpa [ReedSolomon.evalOnPoints] using this.symm
  let P (c : Idx → Fin 2 → Fin BinaryIRSProfile.interleaving → Fld)
      (ab : Fin 2 × Fin BinaryIRSProfile.interleaving) : Polynomial Fld :=
    if hc : c ∈ T' then Classical.choose (hpoly c hc ab.1 ab.2) else 0
  have hPspec : ∀ c ∈ T', ∀ (ab : Fin 2 × Fin BinaryIRSProfile.interleaving), (P c ab).natDegree ≤ wY ∧
      ∀ i : Idx, (P c ab).eval (BinaryIRSProfile.domain i) = c i ab.1 ab.2 := by
    intro c hc ab; simp only [P, dite_eq_left, hc]; exact Classical.choose_spec (hpoly c hc ab.1 ab.2)
  have hsep : ∀ c1 ∈ T', ∀ c2 ∈ T', c1 ≠ c2 →
      ∃ ab : Fin 2 × Fin BinaryIRSProfile.interleaving, P c1 ab ≠ P c2 ab := by
    intro c1 hc1 c2 hc2 hne
    by_contra hall; push Not at hall
    apply hne; funext i a b
    rw [← (hPspec c1 hc1 (a, b)).2 i, ← (hPspec c2 hc2 (a, b)).2 i, hall (a, b)]
  have hsmall : T'.card * (T'.card - 1) < Fintype.card Fld := by
    rw [hT'card, Nat.succ_eq_add_one, Nat.add_sub_cancel]; exact hLsmall
  have : Nonempty (Fin 2 × Fin BinaryIRSProfile.interleaving) := ⟨(0, ⟨0, by norm_num [BinaryIRSProfile.interleaving]⟩)⟩
  obtain ⟨w, hinj_comb⟩ := exists_separating_weights T' P hsep hsmall
  let u_w : Idx → Fld := fun i => ∑ ab : Fin 2 × Fin BinaryIRSProfile.interleaving, w ab * received i ab.1 ab.2
  let comb (c : Idx → Fin 2 → Fin BinaryIRSProfile.interleaving → Fld) : Polynomial Fld :=
    ∑ ab : Fin 2 × Fin BinaryIRSProfile.interleaving, Polynomial.C (w ab) * P c ab
  let Qset : Finset (Polynomial Fld) := T'.image comb
  have hQcard : Qset.card = L + 1 := by
    rw [Finset.card_image_of_injOn hinj_comb, hT'card]
  have hQok : ∀ q ∈ Qset, q.natDegree ≤ wY ∧
      A ≤ (Finset.univ.filter fun i : Idx => q.eval (BinaryIRSProfile.domain i) = u_w i).card := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨c, hcT', rfl⟩
    refine ⟨?_, ?_⟩
    · refine (natDegree_sum_le _ _).trans (Finset.sup_le fun ab _ => ?_)
      exact (natDegree_C_mul_le _ _).trans (hPspec c hcT' ab).1
    · have hdist := (Code.mem_closeCodewordsRel_iff.mp (hT c (hT'sub hcT'))).2
      rw [Code.relHammingDist_coe, BinaryIRSProfile.card_index] at hdist
      have hge_agree : A ≤ (Finset.univ.filter fun i : Idx => c i = received i).card := by
        have hsum := Code.agree_add_hammingDist (u := received) (v := c)
        rw [BinaryIRSProfile.card_index] at hsum
        have hrad : ((radius : ℝ≥0) : ℝ) = (radNum : ℝ) / (radDen : ℝ) := by
          simp [radius, claimedRadius, radNum, radDen]
        rw [hrad] at hdist
        have hd_le : (hammingDist received c : ℝ) ≤ (N : ℝ) * ((radNum : ℝ) / (radDen : ℝ)) := by
          rw [div_le_iff₀ (by norm_num)] at hdist
          rw [show ((2097152 : ℕ) : ℝ) = (N : ℝ) by norm_num [N], mul_comm] at hdist
          exact hdist
        have hd_nat : hammingDist received c ≤ 614321 := by
          have : (N : ℝ) * ((radNum : ℝ) / (radDen : ℝ)) < 614322 := by
            norm_num [N, radNum, radDen]
          have : hammingDist received c < 614322 := by exact_mod_cast (lt_of_le_of_lt hd_le this)
          omega
        have hcard_ag : (Finset.univ.filter fun i : Idx => c i = received i).card =
            2097152 - hammingDist received c := by
          have : (Finset.univ.filter fun i : Idx => received i = c i).card + hammingDist received c = 2097152 := by
            simpa [Code.agree] using hsum
          have heq : (Finset.univ.filter fun i : Idx => c i = received i) =
              (Finset.univ.filter fun i : Idx => received i = c i) := by
            ext i; simp [eq_comm]
          rw [heq]; omega
        rw [hcard_ag]; norm_num [A]; omega
      refine hge_agree.trans (Finset.card_le_card fun i hi => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      dsimp [comb, u_w]
      change (evalRingHom (BinaryIRSProfile.domain i))
        (∑ ab : Fin 2 × Fin BinaryIRSProfile.interleaving, Polynomial.C (w ab) * P c ab) = _
      rw [map_sum]
      apply Finset.sum_congr rfl; intro ab _
      change (Polynomial.C (w ab) * P c ab).eval (BinaryIRSProfile.domain i) = _
      rw [Polynomial.eval_mul, Polynomial.eval_C, (hPspec c hcT' ab).2 i, hi]
  have hle := hScalar u_w Qset hQok
  omega

/-! ### Part 3: Final `ProtocolClaim 6401 78633206 268435456` assembly! -/

lemma nat_div_le_inv_pow {m q t : ℕ} (hm : 0 < m) (hq : m * 2 ^ t ≤ q) :
    (m : ENNReal) / (q : ENNReal) ≤ 1 / 2 ^ t := by
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
  have hmtop : (m : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hqE : ((m * 2 ^ t : ℕ) : ENNReal) ≤ (q : ENNReal) := by exact_mod_cast hq
  have hcast : ((m * 2 ^ t : ℕ) : ENNReal) = (m : ENNReal) * 2 ^ t := by push_cast; ring
  calc (m : ENNReal) / (q : ENNReal)
      ≤ (m : ENNReal) / ((m * 2 ^ t : ℕ) : ENNReal) := ENNReal.div_le_div_left hqE _
    _ = (m : ENNReal) / ((m : ENNReal) * 2 ^ t) := by rw [hcast]
    _ = (m : ENNReal) * 1 / ((m : ENNReal) * 2 ^ t) := by rw [mul_one]
    _ = 1 / 2 ^ t := ENNReal.mul_div_mul_left 1 (2 ^ t) hm0 hmtop

/-- **Master assembly theorem:**
From a `LineExactAgreementBound` of size `mcaCap` and a `ScalarListBound` of size `listCap`
at agreement threshold `A = 1482831` with `mcaCap + listCap ≤ 2^64`, we obtain
`ProtocolClaim 6401 78633206 268435456`! -/
theorem protocolClaim6401_of_lineAndList {mcaCap listCap : ℕ}
    (hpos : 0 < mcaCap + listCap)
    (hbudget : mcaCap + listCap ≤ 2 ^ 64)
    (hLine : LineExactAgreementBound BinaryIRSProfile.domain (wY + 1) A (mcaCap : ℝ))
    (hList : ScalarListBound listCap) :
    ProtocolClaim 6401 radNum radDen where
  admissible := radius_admissible
  reduction := by
    have hLsmall : (listCap + 1) * listCap < Fintype.card Fld := by
      rw [show Fintype.card Fld = 2 ^ (192 : ℕ) from BF64.card_ext3]
      have hle : listCap ≤ 2 ^ 64 := by omega
      nlinarith
    have hthresh : A ≤ ⌈(Fintype.card Idx : ℝ) * (1 - (radius : ℝ))⌉₊ := by
      rw [BinaryIRSProfile.card_index]
      have hceil : (A : ℝ) ≤ (⌈(2097152 : ℝ) * (1 - (radius : ℝ))⌉₊ : ℝ) := by
        have h1 : (2097152 : ℝ) * (1 - (radius : ℝ)) ≤ (⌈(2097152 : ℝ) * (1 - (radius : ℝ))⌉₊ : ℝ) :=
          Nat.le_ceil _
        -- Wait: 2097152 * (1 - radius) = 1482830.078125 > 1482830, so ceil ≥ 1482831 = A!
        have hgt : (1482830 : ℝ) < (2097152 : ℝ) * (1 - (radius : ℝ)) := by
          have hrad : ((radius : ℝ≥0) : ℝ) = (radNum : ℝ) / (radDen : ℝ) := by
            simp [radius, claimedRadius, radNum, radDen]
          rw [hrad]; norm_num [radNum, radDen]
        have hlt_nat : 1482830 < ⌈(2097152 : ℝ) * (1 - (radius : ℝ))⌉₊ := by
          exact_mod_cast lt_of_lt_of_le hgt h1
        norm_num [A]; exact_mod_cast Nat.succ_le_of_lt hlt_nat
      exact_mod_cast hceil
    have hmca : mcaError (AffineLineGenerator Fld) BinaryIRSProfile.code (radius : ℝ) ≤
        (mcaCap : ENNReal) / (Fintype.card Fld : ENNReal) := by
      calc _ ≤ mcaError (AffineLineGenerator Fld) BinaryIRSProfile.baseCode (radius : ℝ) := by
            simpa [BinaryIRSProfile.code, BinaryIRSProfile.baseCode,
              ReedSolomon.Interleaved.irsCode, BinaryIRSProfile.totalDimension_div_interleaving] using
              (ProximityGap.mcaError_interleaved_le BinaryIRSProfile.baseCode
                BinaryIRSProfile.interleaving radius (by norm_num [BinaryIRSProfile.interleaving]))
        _ ≤ ENNReal.ofReal ((mcaCap : ℝ) / (Fintype.card Fld : ℝ)) := by
            have hk : BinaryIRSProfile.baseDimension = wY + 1 := by norm_num [BinaryIRSProfile.baseDimension, wY]
            simpa [BinaryIRSProfile.baseCode, hk] using
              mcaError_affineLine_le_of_exactAgreement BinaryIRSProfile.domain (mcaCap : ℝ) hLine (radius : ℝ) hthresh
        _ = (mcaCap : ENNReal) / (Fintype.card Fld : ENNReal) := by
            rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos),
              ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    have hLambdaNat : (Code.Lambda SquaredCode (radius : ℝ)).toNat ≤ listCap :=
      ENat.toNat_le_of_le_natCast (lambda_squaredCode_le_of_scalarList hList hLsmall)
    have hListE :
        ((Code.Lambda SquaredCode (radius : ℝ)).toNat : ENNReal) / (Fintype.card Fld : ENNReal) ≤
          (listCap : ENNReal) / (Fintype.card Fld : ENNReal) :=
      ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
    have hcert : ToyProblem.certifiedGammaError BinaryIRSProfile.code radius ≤
        (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
      rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
      push_cast
      calc mcaError (AffineLineGenerator Fld) BinaryIRSProfile.code (radius : ℝ) +
            ((Code.Lambda
              ((BinaryIRSProfile.code ^⋈ (Fin 2) :
                ModuleCode Idx Fld (Fin 2 → Fin BinaryIRSProfile.interleaving → Fld)) :
                Set (Idx → Fin 2 → Fin BinaryIRSProfile.interleaving → Fld))
              (radius : ℝ)).toNat : ENNReal) / (Fintype.card Fld : ENNReal)
          ≤ (mcaCap : ENNReal) / (Fintype.card Fld : ENNReal) +
            (listCap : ENNReal) / (Fintype.card Fld : ENNReal) := by
              apply add_le_add hmca; simpa [SquaredCode] using hListE
        _ = ((mcaCap + listCap : ℕ) : ENNReal) / (Fintype.card Fld : ENNReal) := by
              rw [← ENNReal.add_div]; push_cast; rfl
        _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
              apply nat_div_le_inv_pow hpos
              rw [show Fintype.card Fld = 2 ^ (192 : ℕ) from BF64.card_ext3]
              calc (mcaCap + listCap) * 2 ^ 128 ≤ 2 ^ 64 * 2 ^ 128 := Nat.mul_le_mul_right _ hbudget
                _ = 2 ^ 192 := by norm_num
    have hred : ToyProblem.certifiedGammaError BinaryIRSProfile.code radius ≤ reductionTarget :=
      hcert.trans (by norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
    have hr : claimedRadius radNum radDen = radius := rfl
    have hc : ReedSolomon.Interleaved.irsCode BinaryIRSProfile.domain
        BinaryIRSProfile.totalDimension BinaryIRSProfile.interleaving = BinaryIRSProfile.code := rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hr, hc]
    exact hred
  score := radius_score

end B6401ListAndMCA
end ProximityPrize.SubmissionBinaryLower
