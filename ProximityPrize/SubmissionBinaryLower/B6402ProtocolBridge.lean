import ProximityPrize.SubmissionBinaryLower.B6401ListAndMCA
import ProximityPrize.SubmissionBinaryLower.B6402Radius

/-! The final protocol bridge at the new radius, following PR 694's scalar
projection argument. The two hypotheses are the line and scalar-list bounds. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402Protocol
open Polynomial MvPolynomial PolynomialDifferential ReedSolomon CoreDefinitions ProximityGap ToyProblem
open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open B6401Params hiding A radius radNum radDen
open B6401ListAndMCA hiding ScalarListBound lambda_squaredCode_le_of_scalarList
open scoped BigOperators NNReal Polynomial
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
local notation "Fld" => BinaryIRSProfile.Field
local notation "Idx" => BinaryIRSProfile.Index
private abbrev A : ℕ := B6402Radius.agreement
private abbrev radNum : ℕ := B6402Radius.numerator
private abbrev radDen : ℕ := B6402Radius.denominator
private noncomputable abbrev radius : ℝ≥0 := B6402Radius.radius

def ScalarListBound (L : ℕ) : Prop :=
  ∀ (u : Idx → Fld) (T : Finset (Polynomial Fld)),
    (∀ p ∈ T, p.natDegree ≤ wY ∧
      A ≤ (Finset.univ.filter fun i : Idx => p.eval (BinaryIRSProfile.domain i) = u i).card) →
    T.card ≤ L

/-- Polymorphic Schwartz-Zippel separating-weights lemma:
if `T'` has `T'.card * (T'.card - 1) < |F|` elements separated by polynomial tuples `P c : ι → F[X]`,
then there exists `w : ι → F` making `c ↦ ∑ ab, C (w ab) * P c ab` injective on `T'`. -/
private lemma separate_polynomials {F ι α : Type*} [Field F] [Fintype F]
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
  obtain ⟨w, hinj_comb⟩ := separate_polynomials T' P hsep hsmall
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
          simp [radius, B6402Radius.radius, claimedRadius, radNum, radDen]
        rw [hrad] at hdist
        have hd_le : (hammingDist received c : ℝ) ≤ (N : ℝ) * ((radNum : ℝ) / (radDen : ℝ)) := by
          rw [div_le_iff₀ (by norm_num)] at hdist
          rw [show ((2097152 : ℕ) : ℝ) = (N : ℝ) by norm_num [N], mul_comm] at hdist
          exact hdist
        have hd_nat : hammingDist received c ≤ 614402 := by
          have : (N : ℝ) * ((radNum : ℝ) / (radDen : ℝ)) < 614403 := by
            norm_num [N, radNum, radDen]
          have : hammingDist received c < 614403 := by exact_mod_cast (lt_of_le_of_lt hd_le this)
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


theorem protocolClaim6402_of_lineAndList {mcaCap listCap : ℕ}
    (hpos : 0 < mcaCap + listCap)
    (hbudget : mcaCap + listCap ≤ 2 ^ 64)
    (hLine : LineExactAgreementBound BinaryIRSProfile.domain (wY + 1) A (mcaCap : ℝ))
    (hList : ScalarListBound listCap) :
    ProtocolClaim 6402 radNum radDen where
  admissible := B6402Radius.admissible
  reduction := by
    have hLsmall : (listCap + 1) * listCap < Fintype.card Fld := by
      rw [show Fintype.card Fld = 2 ^ (192 : ℕ) from BF64.card_ext3]
      have hle : listCap ≤ 2 ^ 64 := by omega
      nlinarith
    have hthresh : A ≤ ⌈(Fintype.card Idx : ℝ) * (1 - (radius : ℝ))⌉₊ := B6402Radius.agreement_ge (Nat.le_ceil _)
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
  score := B6402Radius.score


#print axioms protocolClaim6402_of_lineAndList
end ProximityPrize.SubmissionBinaryLower.B6402Protocol
