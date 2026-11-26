import ProximityPrize.SubmissionBinaryLower.B6401Main
import ProximityPrize.SubmissionBinaryLower.Binary6402Hybrid12
import ProximityPrize.SubmissionBinaryLower.B6402FilteredJets
import ProximityPrize.SubmissionBinaryLower.B6402ProtocolBridge

/-! The 6402 label partition over the native protocol. The remaining
positive-slope counting theorem is explicit and is not assumed as an axiom. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402FactorAssembly
open Polynomial ReedSolomon ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open B6401Params hiding A
open B6402HybridP64 (A BadOn6402 linePow linePow_natDegree_le eval_linePow)
open B6401ContactKerD B6401QuotInterp B6401ResLineOrd B6401Main P64Cofactor
open B6401SmallAlg (wdegBiDom)
open B6401FactorBound (wdegBiDom_le_of_wdeg_coeff wdegBiDom_ge_natDegree_mul)
open scoped BigOperators

local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
local notation "Poly" => ContactPoly (Polynomial Fld)

abbrev factorCap : ℕ := 8167616324360948337+700000000000000000+100000000000000

def PositiveFactorCount : Prop :=
  ∀ (u₀ u₁ : Idx → Fld) (Q F : Poly), Q ≠ 0 → contactDeriv Q=0 →
    Q.natDegree≤2 → wdeg wY Q ≤ 26689499 → wYZ 1 Q ≤ 1811 →
    F ∣ Q → Irreducible F → 1 ≤ F.natDegree →
    ∀ (S : Finset Fld) (P : Fld → Polynomial Fld) (Az : Fld → Finset Idx),
      (∀ z∈S, (P z).natDegree≤wY ∧ A≤(Az z).card ∧ BadOn6402 u₀ u₁ (Az z)) →
      (∀ z∈S, ∀ i : Idx, i∈Az z ↔ (P z).eval (BinaryIRSProfile.domain i)=u₀ i+z*u₁ i) →
      (∀ z∈S, evalContact (evalZContact F z) (P z)=0) →
      S.card ≤ F.natDegree*factorCap

private theorem union_degree (m : Multiset Poly) (f : Poly → Finset Fld)
    (hn : ∀ x∈m, x≠0) (hc : ∀ x∈m, (f x).card≤x.natDegree*factorCap) :
    (m.toFinset.biUnion f).card≤m.prod.natDegree*factorCap := by
  classical
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x l ih =>
    have hx := hn x (Multiset.mem_cons_self _ _)
    have hl := fun a ha => hn a (Multiset.mem_cons_of_mem ha)
    have nonzero : ∀ z : Multiset Poly, (∀ g∈z, g≠0) → z.prod≠0 := by
      intro z
      induction z using Multiset.induction_on with
      | empty => simp
      | cons f z hz =>
        intro h
        rw [Multiset.prod_cons]
        exact mul_ne_zero (h f (Multiset.mem_cons_self _ _)) (hz (fun g hg => h g (Multiset.mem_cons_of_mem hg)))
    have h0 := nonzero l hl
    have h1 := hc x (Multiset.mem_cons_self _ _)
    have h2 := ih hl (fun a ha => hc a (Multiset.mem_cons_of_mem ha))
    rw [Multiset.toFinset_cons,Finset.biUnion_insert,Multiset.prod_cons,natDegree_mul hx h0,Nat.add_mul]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add h1 h2)

theorem line_bound_of_factors (count : PositiveFactorCount) :
    LineExactAgreementBound BinaryIRSProfile.domain (wY+1) A (18400000000000000000 : ℝ) := by
  intro u₀ u₁
  let agr (z : Fld) (Q : Polynomial Fld) : Finset Idx :=
    polynomialAgreementSet BinaryIRSProfile.domain (fun i => u₀ i + z * u₁ i) Q
  let pred (z : Fld) : Prop :=
    ∃ P : Polynomial Fld, P.natDegree ≤ wY ∧
      A ≤ (agr z P).card ∧ BadOn6402 u₀ u₁ (agr z P)
  classical
  let S : Finset Fld := Set.toFinset {z : Fld | pred z}
  have hS_mem : ∀ z : Fld, z ∈ S ↔ pred z := fun z => by
    simp only [S, Set.mem_toFinset, Set.mem_ofPred_eq]
  have hS_card : (S.card : ℚ) ≤ (18400000000000000000 : ℚ) := by
    -- Pick one bad witness `P z` for each `z ∈ S`!
    let P (z : Fld) : Polynomial Fld :=
      if hz : z ∈ S then Classical.choose ((hS_mem z).mp hz) else 0
    let Az (z : Fld) : Finset Idx := agr z (P z)
    have hPspec : ∀ z ∈ S, (P z).natDegree ≤ wY ∧ A ≤ (Az z).card ∧ BadOn6402 u₀ u₁ (Az z) := by
      intro z hz; simp only [P, Az, dite_eq_left hz]
      exact Classical.choose_spec ((hS_mem z).mp hz)
    have hmatch : ∀ z ∈ S, ∀ i : Idx, i ∈ Az z ↔ (P z).eval (BinaryIRSProfile.domain i) = u₀ i + z * u₁ i :=
      fun z _ i => by simp only [Az, agr, mem_polynomialAgreementSet]
    let W0 : ℕ := 2*A*9-1
    obtain ⟨Q,hQ_ne,hQ_D,hQ_deg,hQ_wdeg,hQ_wYZ,van⟩ :=
      B6402FilteredJets.initial_interpolant_6402 BinaryIRSProfile.card_index
        BinaryIRSProfile.domain (linePow u₀ u₁ 1) (fun i => linePow_natDegree_le u₀ u₁ 1 i)
    change wdeg wY Q ≤ W0 at hQ_wdeg
    have hQ_eval : ∀ z∈S, evalContact (evalZContact Q z) (P z)=0 := by
      intro z hz
      refine van z (P z) (Az z) (hPspec z hz).1 (hPspec z hz).2.1 ?_
      intro i hi; rw [eval_linePow,pow_one]; exact (hmatch z hz i).mp hi
    -- UFD factorization of `Q` in `ContactPoly (Polynomial Fld)`!
    let facs := UniqueFactorizationMonoid.normalizedFactors Q
    let facs0 := facs.filter fun F => F.natDegree = 0
    let facs1 := facs.filter fun F => 1 ≤ F.natDegree
    have hfacs_split : facs = facs0 + facs1 := by
      ext F; simp only [facs0, facs1, Multiset.count_add, Multiset.count_filter]
      by_cases h0 : F.natDegree = 0
      · simp [h0]
      · simp [h0, show 1 ≤ F.natDegree by omega]
    obtain ⟨uQ, huQ⟩ := UniqueFactorizationMonoid.prod_normalizedFactors (a := Q) hQ_ne
    have hQ_fac : facs0.prod * facs1.prod * (uQ : ContactPoly (Polynomial Fld)) = Q := by
      rw [← Multiset.prod_add, ← hfacs_split]; exact huQ
    have hfacs0_deg0 : facs0.prod.natDegree = 0 := by
      have hgen : ∀ m : Multiset (ContactPoly (Polynomial Fld)), (∀ F ∈ m, F.natDegree = 0) → m.prod.natDegree = 0 := by
        intro m; induction m using Multiset.induction_on with
        | empty => intro _; simp
        | cons a s ih =>
            intro h; rw [Multiset.prod_cons]
            exact Nat.eq_zero_of_le_zero (Polynomial.natDegree_mul_le.trans
              (by rw [h a (Multiset.mem_cons_self a s), ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))]))
      exact hgen facs0 fun F hF => (Multiset.mem_filter.mp hF).2
    let G0 : BiPoly (Polynomial Fld) := facs0.prod.coeff 0
    have hfacs0_eq : facs0.prod = Polynomial.C G0 := Polynomial.eq_C_of_natDegree_eq_zero hfacs0_deg0
    have hG0_ne : G0 ≠ 0 := fun h0 => hQ_ne (by rw [← hQ_fac, hfacs0_eq, h0, map_zero, zero_mul, zero_mul])
    have hf1p_ne : facs1.prod ≠ 0 := fun h0 => hQ_ne (by rw [← hQ_fac, h0, mul_zero, zero_mul])
    have hG0_wdeg : wdeg wY (Polynomial.C G0) ≤ W0 := by
      have h1 := wdeg_mul wY (Polynomial.C_ne_zero.mpr hG0_ne) (mul_ne_zero hf1p_ne uQ.ne_zero)
      rw [← mul_assoc, show Polynomial.C G0 * facs1.prod * (uQ : ContactPoly (Polynomial Fld)) = Q by
        rw [← hfacs0_eq, hQ_fac]] at h1; omega
    have hG0_deg : G0.natDegree ≤ 25 := by
      have h1 : wdegBiDom wY G0 ≤ W0 := by simpa using wdegBiDom_le_of_wdeg_coeff hG0_wdeg 0
      have h2 := wdegBiDom_ge_natDegree_mul wY G0 hG0_ne
      have hle := h2.trans h1
      have hW0 : W0 = 26689499 := by norm_num [W0, A]
      have hw : wY = 1048575 := rfl
      rw [hw] at hle; omega
    have hG0_wYZ : wYZ 1 (Polynomial.C G0) ≤ 1811 := by
      have h1 := wYZ_mul 1 (Polynomial.C_ne_zero.mpr hG0_ne) (mul_ne_zero hf1p_ne uQ.ne_zero)
      rw [← mul_assoc, show Polynomial.C G0 * facs1.prod * (uQ : ContactPoly (Polynomial Fld)) = Q by
        rw [← hfacs0_eq, hQ_fac]] at h1; omega
    -- Bound `S0` (roots of `G0`): `≤ 10^12`!
    let S0 := S.filter fun z => triEval G0 z (P z) = 0
    have hS0_card : (S0.card : ℚ) ≤ (1000000000000 : ℚ) := by
      have hark := B6402HybridP64.card_le_of_biPoly_pow u₀ u₁ 1 le_rfl G0 25 1811 hG0_ne hG0_deg
        (fun j a => by simpa only [Polynomial.coeff_C_zero] using natDegree_Z_le_of_wYZ hG0_wYZ 0 j a) S0 P Az
        (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).1)
        (fun z hz => (Finset.mem_filter.mp hz).2)
        (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).2.1)
        (fun z hz i hi => by simpa only [pow_one] using (hmatch z (Finset.mem_filter.mp hz).1 i).mp hi)
        (fun z hz => (hPspec z (Finset.mem_filter.mp hz).1).2.2)
      refine hark.trans (max_le (by norm_num) ?_)
      unfold B6402HybridP64.arklibBoundPowQ; norm_num [N,wY,B6402HybridP64.A]
    -- Every `z ∈ S` lies in `S0` or `SF F` for some `F ∈ facs1`!
    let SF (F : ContactPoly (Polynomial Fld)) : Finset Fld := S.filter fun z => evalContact (evalZContact F z) (P z) = 0
    have hS_cover : ∀ z ∈ S, z ∈ S0 ∨ ∃ F ∈ facs1, z ∈ SF F := by
      intro z hz
      have h0 := hQ_eval z hz
      rw [← hQ_fac] at h0
      have hmulZ : ∀ A B : ContactPoly (Polynomial Fld), evalZContact (A * B) z = evalZContact A z * evalZContact B z :=
        fun A B => by unfold evalZContact; exact Polynomial.map_mul _
      rw [hmulZ, hmulZ, evalContact_mul, evalContact_mul, hfacs0_eq] at h0
      have hu_ne : evalContact (evalZContact (uQ : ContactPoly (Polynomial Fld)) z) (P z) ≠ 0 := by
        rcases uQ.isUnit with ⟨v, hv⟩; intro h0'
        have h1 := congrArg (fun q => evalContact (evalZContact q z) (P z)) v.mul_inv
        rw [hmulZ, evalContact_mul, hv, h0', zero_mul] at h1
        have : evalContact (evalZContact (1 : ContactPoly (Polynomial Fld)) z) (P z) = 1 := by
          unfold evalZContact evalContact; simp
        rw [this] at h1; exact one_ne_zero h1.symm
      rcases mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hu_ne) with hG | hFprod
      · left; exact Finset.mem_filter.mpr ⟨hz, by simpa [evalZContact, evalContact, triEval] using hG⟩
      · right
        have hgen : ∀ m : Multiset (ContactPoly (Polynomial Fld)),
            evalContact (evalZContact m.prod z) (P z) = 0 → ∃ F ∈ m, evalContact (evalZContact F z) (P z) = 0 := by
          intro m; induction m using Multiset.induction_on with
          | empty => intro h; unfold evalZContact evalContact at h; simp at h
          | cons a s ih =>
              intro h; rw [Multiset.prod_cons, hmulZ, evalContact_mul] at h
              rcases mul_eq_zero.mp h with ha | hs
              · exact ⟨a, Multiset.mem_cons_self a s, ha⟩
              · obtain ⟨F, hF, hv⟩ := ih hs; exact ⟨F, Multiset.mem_cons_of_mem hF, hv⟩
        obtain ⟨F, hF, hv⟩ := hgen facs1 hFprod
        exact ⟨F, hF, Finset.mem_filter.mpr ⟨hz, hv⟩⟩
    have hc : ∀ F∈facs1, (SF F).card ≤ F.natDegree*factorCap := by
      intro F hF
      have mem := (Multiset.mem_filter.mp hF).1
      have irr := UniqueFactorizationMonoid.irreducible_of_normalized_factor F mem
      have dvd : F∣Q := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors mem
      apply count u₀ u₁ Q F hQ_ne hQ_D hQ_deg hQ_wdeg hQ_wYZ dvd irr (Multiset.mem_filter.mp hF).2 (SF F) P Az
      · exact fun z hz => hPspec z (Finset.mem_filter.mp hz).1
      · exact fun z hz => hmatch z (Finset.mem_filter.mp hz).1
      · exact fun z hz => (Finset.mem_filter.mp hz).2
    have hn : ∀ F∈facs1, F≠0 := fun F hf =>
      (UniqueFactorizationMonoid.irreducible_of_normalized_factor F (Multiset.mem_filter.mp hf).1).ne_zero
    have hpos := union_degree facs1 SF hn hc
    have hdeg : facs1.prod.natDegree ≤ 2 := by
      have hmul := congrArg Polynomial.natDegree hQ_fac
      rw [Polynomial.natDegree_mul (mul_ne_zero (hfacs0_eq ▸ Polynomial.C_ne_zero.mpr hG0_ne) hf1p_ne) uQ.ne_zero,
          Polynomial.natDegree_mul (hfacs0_eq ▸ Polynomial.C_ne_zero.mpr hG0_ne) hf1p_ne] at hmul
      omega
    have hsub : S ⊆ S0 ∪ facs1.toFinset.biUnion SF := by
      intro z hz
      rcases hS_cover z hz with h|⟨F,hF,hzF⟩
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨F,Multiset.mem_toFinset.mpr hF,hzF⟩)
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hs0 : S0.card ≤ 1000000000000 := by exact_mod_cast hS0_card
    have hpos2 := hpos.trans (Nat.mul_le_mul_right factorCap hdeg)
    exact_mod_cast (show S.card ≤ 18400000000000000000 by dsimp [factorCap] at hpos2; omega)
  -- Convert `S` into `LineExactAgreementBound`!
  have hS_nat : S.card ≤ 18400000000000000000 := by exact_mod_cast hS_card
  refine ⟨S, by exact_mod_cast hS_nat, ?_⟩
  intro z hz P hPdeg hA
  have hPnat : P.natDegree ≤ wY := by
    by_cases hP0 : P = 0
    · simp [hP0]
    · have := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg; omega
  have hnot_bad : ¬ BadOn6402 u₀ u₁ (agr z P) := by
    intro hbad
    exact hz ((hS_mem z).mpr ⟨P, hPnat, hA, hbad⟩)
  unfold BadOn6402 at hnot_bad; push Not at hnot_bad
  obtain ⟨P₀, P₁, hP₀_deg, hP₁_deg, hagree⟩ := hnot_bad
  have hP₀_lt : P₀.degree < (wY + 1 : ℕ) := by
    by_cases h0 : P₀ = 0
    · simp [h0]
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mp (by omega)
  have hP₁_lt : P₁.degree < (wY + 1 : ℕ) := by
    by_cases h0 : P₁ = 0
    · simp [h0]
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mp (by omega)
  have hP_eq : P = P₀ + Polynomial.C z * P₁ := by
    let D := P - (P₀ + Polynomial.C z * P₁)
    have hD_deg : D.natDegree ≤ wY := by
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le hPnat ?_)
      exact (Polynomial.natDegree_add_le _ _).trans (max_le hP₀_deg ((Polynomial.natDegree_C_mul_le _ _).trans hP₁_deg))
    have hD_zero : D = 0 := by
      by_contra hDne
      let roots_im := (agr z P).image BinaryIRSProfile.domain
      have hsub : roots_im ⊆ D.roots.toFinset := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hDne, Polynomial.IsRoot.def]
        have hPi : P.eval (BinaryIRSProfile.domain i) = u₀ i + z * u₁ i :=
          (mem_polynomialAgreementSet _ _ _ _).mp hi
        have ⟨h0i, h1i⟩ := hagree i hi
        simp [D, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hPi, h0i, h1i]
      have hcard_r : A ≤ D.natDegree := by
        calc A ≤ (agr z P).card := hA
          _ = roots_im.card := (Finset.card_image_of_injective _ BinaryIRSProfile.domain.injective).symm
          _ ≤ D.roots.toFinset.card := Finset.card_le_card hsub
          _ ≤ D.roots.card := Multiset.toFinset_card_le _
          _ ≤ D.natDegree := Polynomial.card_roots' D
      norm_num [A, wY] at hcard_r hD_deg; omega
    exact sub_eq_zero.mp hD_zero
  refine ⟨P₀, P₁, hP₀_lt, hP₁_lt, hP_eq, ?_⟩
  ext i
  rw [mem_polynomialAgreementSet, mem_commonPolynomialAgreementSet]
  constructor
  · intro hi; exact hagree i ((mem_polynomialAgreementSet _ _ _ _).mpr hi)
  · rintro ⟨h0i, h1i⟩; rw [hP_eq]; simp [h0i, h1i]

theorem protocol_from_factor_and_scalar (factors : PositiveFactorCount)
    (scalar : B6402Protocol.ScalarListBound 10000000) :
    ProtocolClaim 6402 78643482 268435456 :=
  B6402Protocol.protocolClaim6402_of_lineAndList (mcaCap:=18400000000000000000) (listCap:=10000000)
    (by decide) (by decide) (line_bound_of_factors factors) scalar

#print axioms protocol_from_factor_and_scalar
end ProximityPrize.SubmissionBinaryLower.B6402FactorAssembly
