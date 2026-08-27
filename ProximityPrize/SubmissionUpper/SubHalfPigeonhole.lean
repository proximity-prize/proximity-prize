/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.HalfRadiusCollision

namespace ProximityPrize.SubmissionUpper.SubHalfPigeonhole

open Polynomial
open ToyProblem ToyProblem.Impl.IRS
open scoped BigOperators NNReal

abbrev F := ProximityPrize.Benchmark.IRSProfile.Field
abbrev I := ProximityPrize.Benchmark.IRSProfile.Index
abbrev k := ProximityPrize.Benchmark.IRSProfile.totalDimension
abbrev s := ProximityPrize.Benchmark.IRSProfile.interleaving
abbrev rowK := 131072
abbrev extra := 8
abbrev agreement := 131080
abbrev signatureWidth := 9
abbrev unsafeIndex := 131064

namespace IRSProfile

open ProximityPrize.Benchmark

local instance : NeZero s := ⟨by
  norm_num [s, Benchmark.IRSProfile.interleaving]⟩

theorem rowDimension_eq : k / s = rowK :=
  Benchmark.IRSProfile.totalDimension_div_interleaving.trans (by
    norm_num [rowK, Benchmark.IRSProfile.baseDimension])

abbrev CandidateSets := Set.powersetCard I agreement

noncomputable instance : Fintype CandidateSets := Fintype.ofFinite _

noncomputable def nodes (T : CandidateSets) : Finset F :=
  (T : Finset I).image Benchmark.IRSProfile.domain

theorem card_nodes (T : CandidateSets) : (nodes T).card = agreement := by
  rw [nodes, Finset.card_image_of_injective _ Benchmark.IRSProfile.domain.injective]
  exact T.prop

noncomputable def rootPoly (T : CandidateSets) : Polynomial F :=
  (nodes T).prod fun a => Polynomial.X - Polynomial.C a

theorem rootPoly_monic (T : CandidateSets) : (rootPoly T).Monic := by
  simpa only [rootPoly] using
    (Polynomial.monic_prod_X_sub_C (fun x : F => x) (nodes T))

theorem rootPoly_natDegree (T : CandidateSets) :
    (rootPoly T).natDegree = agreement := by
  rw [rootPoly, Polynomial.natDegree_finsetProd_X_sub_C_eq_card, card_nodes]

noncomputable def signature (T : CandidateSets) : Fin signatureWidth → F :=
  fun i => (rootPoly T).coeff (rowK + i)

theorem field_card_lt_two_pow_186 : Fintype.card F < 2 ^ 186 := by
  change Fintype.card _root_.KoalaBear.Ext6 < 2 ^ 186
  rw [_root_.KoalaBear.card_ext6]
  norm_num [_root_.KoalaBear.fieldSize]

theorem field_pow_11_lt_two_pow_2046 :
    (Fintype.card F) ^ 11 < 2 ^ 2046 := by
  have hpow : ∀ q : Nat, q < 2 ^ 186 → q ^ 11 < 2 ^ 2046 := by
    intro q hq
    calc
      q ^ 11 < (2 ^ 186) ^ 11 :=
        Nat.pow_lt_pow_left hq (by norm_num)
      _ = 2 ^ (186 * 11) := (pow_mul 2 186 11).symm
      _ = 2 ^ 2046 := by norm_num
  exact hpow (Fintype.card F) field_card_lt_two_pow_186

theorem two_pow_2046_lt_small_central_choose :
    2 ^ 2046 < Nat.choose 2060 1030 := by
  have hcentral := Nat.four_pow_lt_mul_centralBinom 1030 (by norm_num)
  rw [Nat.centralBinom_eq_two_mul_choose] at hcentral
  norm_num only [Nat.reduceMul] at hcentral
  by_contra hnot
  have hle : Nat.choose 2060 1030 ≤ 2 ^ 2046 := Nat.le_of_not_gt hnot
  have hbad : 4 ^ 1030 < 1030 * 2 ^ 2046 :=
    lt_of_lt_of_le hcentral (Nat.mul_le_mul_left 1030 hle)
  have hreverse : 1030 * 2 ^ 2046 < 4 ^ 1030 := by
    calc
      1030 * 2 ^ 2046 < 2 ^ 11 * 2 ^ 2046 := by gcongr <;> norm_num
      _ = 2 ^ (11 + 2046) := (pow_add 2 11 2046).symm
      _ < 2 ^ (2 * 1030) := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      _ = (2 ^ 2) ^ 1030 := pow_mul 2 2 1030
      _ = 4 ^ 1030 := by norm_num
  exact (Nat.not_lt_of_ge hreverse.le) hbad

theorem two_pow_2046_lt_card_candidateSets :
    2 ^ 2046 < Fintype.card CandidateSets := by
  have hconcrete : 2 ^ 2046 < Nat.choose 262144 131080 := by
    calc
      2 ^ 2046 < Nat.choose 2060 1030 := two_pow_2046_lt_small_central_choose
      _ = Nat.centralBinom 1030 := by
        rw [Nat.centralBinom_eq_two_mul_choose]
      _ < Nat.centralBinom 131064 := Nat.centralBinom_strictMono (by norm_num)
      _ = Nat.choose 262128 131064 := by
        rw [Nat.centralBinom_eq_two_mul_choose]
      _ ≤ Nat.choose 262144 131064 := Nat.choose_le_choose 131064 (by norm_num)
      _ = Nat.choose 262144 131080 :=
        Nat.choose_symm_of_eq_add (by norm_num)
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
  have hcardI : Nat.card I = 262144 := by
    rw [I, Benchmark.IRSProfile.Index, Nat.card_fin]
    norm_num
  rw [hcardI]
  exact hconcrete

theorem signature_card_mul_field_sq_lt :
    Fintype.card (Fin signatureWidth → F) * (Fintype.card F - 1) ^ 2 <
      Fintype.card CandidateSets := by
  have hfun : ∀ w : Nat, Fintype.card (Fin w → F) =
      (Fintype.card F) ^ w := fun w => by
    simpa only [Fintype.card_fin] using
      (Fintype.card_fun : Fintype.card (Fin w → F) =
        Fintype.card F ^ Fintype.card (Fin w))
  have hsig : Fintype.card (Fin signatureWidth → F) =
      (Fintype.card F) ^ signatureWidth := hfun signatureWidth
  have hmul : ∀ q w : Nat, q ^ w * (q - 1) ^ 2 ≤ q ^ w * q ^ 2 := by
    intro q w
    exact Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (Nat.sub_le q 1) 2)
  calc
    Fintype.card (Fin signatureWidth → F) * (Fintype.card F - 1) ^ 2 ≤
        (Fintype.card F) ^ signatureWidth * (Fintype.card F) ^ 2 := by
      rw [hsig]
      exact hmul (Fintype.card F) signatureWidth
    _ = (Fintype.card F) ^ 11 := by
      norm_num [signatureWidth, ← pow_add]
    _ < 2 ^ 2046 := field_pow_11_lt_two_pow_2046
    _ < Fintype.card CandidateSets := two_pow_2046_lt_card_candidateSets

lemma exists_large_fiber {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (sieve : Nat)
    (hlarge : Fintype.card β * sieve < Fintype.card α) :
    ∃ y : β, sieve < (Finset.univ.filter fun x : α => f x = y).card := by
  classical
  by_contra! hall
  have hsum : Fintype.card α =
      ∑ y : β, (Finset.univ.filter fun x : α => f x = y).card := by
    rw [← Finset.card_univ]
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset α))
      (t := (Finset.univ : Finset β)) (f := f)
      (fun _ _ => Finset.mem_univ _))
  have hle : Fintype.card α ≤ Fintype.card β * sieve := by
    rw [hsum]
    calc
      (∑ y : β, (Finset.univ.filter fun x : α => f x = y).card) ≤
          ∑ _y : β, sieve := by
        exact Finset.sum_le_sum fun y _ => hall y
      _ = Fintype.card β * sieve := by simp
  omega

theorem exists_signature_fiber :
    ∃ y : Fin signatureWidth → F,
      (Fintype.card F - 1) ^ 2 <
        (Finset.univ.filter fun T : CandidateSets => signature T = y).card := by
  exact exists_large_fiber signature ((Fintype.card F - 1) ^ 2)
    signature_card_mul_field_sq_lt

noncomputable def chosenSignature : Fin signatureWidth → F :=
  Classical.choose exists_signature_fiber

noncomputable def fiberSets : Finset CandidateSets :=
  Finset.univ.filter fun T => signature T = chosenSignature

abbrev FiberSets := ↥fiberSets

theorem card_fiberSets_large :
    (Fintype.card F - 1) ^ 2 < Fintype.card FiberSets := by
  rw [Fintype.card_coe]
  exact Classical.choose_spec exists_signature_fiber

theorem fiberSets_nonempty : fiberSets.Nonempty := by
  apply Finset.card_pos.mp
  rw [← Fintype.card_coe]
  exact lt_of_le_of_lt (Nat.zero_le _) card_fiberSets_large

noncomputable def anchor : FiberSets :=
  ⟨Classical.choose fiberSets_nonempty, Classical.choose_spec fiberSets_nonempty⟩

theorem member_signature (T : FiberSets) :
    signature T.1 = chosenSignature := by
  exact (Finset.mem_filter.mp T.2).2

noncomputable def diffPoly (T : FiberSets) : Polynomial F :=
  rootPoly anchor.1 - rootPoly T.1

theorem diffPoly_degree_lt (T : FiberSets) :
    (diffPoly T).degree < (rowK : Nat) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [diffPoly, Polynomial.coeff_sub]
  by_cases hna : n ≤ agreement
  · have hi : n - rowK < signatureWidth := by
      norm_num [agreement, rowK, signatureWidth] at hna hn ⊢
      omega
    let i : Fin signatureWidth := ⟨n - rowK, hi⟩
    have hs := congrFun
      ((member_signature anchor).trans (member_signature T).symm) i
    have hadd : rowK + (n - rowK) = n := Nat.add_sub_of_le hn
    rw [signature, signature, show rowK + i.1 = n by simpa [i] using hadd] at hs
    exact sub_eq_zero.mpr hs
  · have hgt : agreement < n := Nat.lt_of_not_ge hna
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (rootPoly_natDegree anchor.1 ▸ hgt),
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (rootPoly_natDegree T.1 ▸ hgt), sub_zero]

noncomputable def coeff (T : FiberSets) : Fin (k / s) → F :=
  Polynomial.degreeLTEquiv F (k / s) ⟨diffPoly T, by
    rw [Polynomial.mem_degreeLT]
    simpa only [rowDimension_eq] using diffPoly_degree_lt T⟩

noncomputable def rows (T : FiberSets) : Fin s → Fin (k / s) → F :=
  fun row => if row = 0 then coeff T else 0

noncomputable def message (T : FiberSets) : Fin k → F :=
  flatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension (rows T)

theorem rsPolynomial_coeff (T : FiberSets) :
    ToyProblem.Spec.rsPolynomial (k / s) (coeff T) = diffPoly T := by
  exact congrArg Subtype.val
    ((Polynomial.degreeLTEquiv F (k / s)).symm_apply_apply
      ⟨diffPoly T, by
        rw [Polynomial.mem_degreeLT]
        simpa only [rowDimension_eq] using diffPoly_degree_lt T⟩)

noncomputable def fixedWord : I → Fin s → F :=
  fun j row => if row = 0 then (rootPoly anchor.1).eval
    (Benchmark.IRSProfile.domain j) else 0

theorem rootPoly_eval_eq_zero (T : CandidateSets) (j : I)
    (hj : j ∈ (T : Finset I)) :
    (rootPoly T).eval (Benchmark.IRSProfile.domain j) = 0 := by
  classical
  rw [rootPoly, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := Benchmark.IRSProfile.domain j)
  · simp [nodes, hj]
  · simp

theorem fixedWord_agrees (T : FiberSets) :
    ∀ j ∈ (T.1 : Finset I),
      fixedWord j = Benchmark.IRSProfile.encoder (message T) j := by
  intro j hj
  funext row
  rw [Benchmark.IRSProfile.encoder, encoder_apply]
  change fixedWord j row = ToyProblem.Spec.rsEncoder (k / s)
    Benchmark.IRSProfile.domain
      (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension
        (flatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension
          (rows T)) row) j
  rw [unflatten_flatten]
  by_cases hrow : row = 0
  · subst row
    rw [show rows T 0 = coeff T by simp [rows],
      ToyProblem.Spec.rsEncoder_apply, rsPolynomial_coeff]
    simp only [fixedWord, if_pos, diffPoly, Polynomial.eval_sub]
    rw [rootPoly_eval_eq_zero T.1 j hj, sub_zero]
  · have hz := congrFun
      (map_zero (ToyProblem.Spec.rsEncoder (k / s) Benchmark.IRSProfile.domain)) j
    simpa [fixedWord, rows, hrow] using hz.symm

theorem no_message_agrees_on_more_than_agreement
    (u : Fin k → F) (S : Finset I) (hcard : agreement < S.card)
    (hagree : ∀ j ∈ S, fixedWord j = Benchmark.IRSProfile.encoder u j) : False := by
  let q : Polynomial F := ToyProblem.Spec.rsPolynomial (k / s)
    (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension u 0)
  have hqdeg : q.degree < (rowK : Nat) := by
    have h := ToyProblem.Spec.rsPolynomial_degree_lt (k / s)
      (unflatten k s Benchmark.IRSProfile.interleaving_dvd_totalDimension u 0)
    simpa only [rowDimension_eq] using h
  have hrootdeg : (rootPoly anchor.1).degree < (S.card : Nat) := by
    rw [Polynomial.degree_eq_natDegree (rootPoly_monic anchor.1).ne_zero,
      rootPoly_natDegree]
    exact_mod_cast hcard
  have hqdegS : q.degree < (S.card : Nat) := by
    have hrS : rowK < S.card :=
      (show rowK < agreement by norm_num [rowK, agreement]).trans hcard
    exact hqdeg.trans (by exact_mod_cast hrS)
  have heval : ∀ j ∈ S,
      (rootPoly anchor.1).eval (Benchmark.IRSProfile.domain j) =
        q.eval (Benchmark.IRSProfile.domain j) := by
    intro j hj
    have h := congrFun (hagree j hj) (0 : Fin s)
    rw [Benchmark.IRSProfile.encoder, encoder_apply,
      ToyProblem.Spec.rsEncoder_apply] at h
    simpa [fixedWord, q] using h
  have heq : rootPoly anchor.1 = q :=
    Polynomial.eq_of_degrees_lt_of_eval_index_eq
      S Benchmark.IRSProfile.domain.injective.injOn hrootdeg hqdegS heval
  have hqnat : q.natDegree < rowK := by
    by_cases hqzero : q = 0
    · simp [hqzero, rowK]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hqzero).mpr hqdeg
  have hnat := congrArg Polynomial.natDegree heq
  rw [rootPoly_natDegree] at hnat
  norm_num [agreement, rowK] at hnat hqnat
  omega

theorem message_eq_zero_of_zero_on_many (u : Fin k → F) (S : Finset I)
    (hcard : rowK ≤ S.card)
    (hzero : ∀ j ∈ S, Benchmark.IRSProfile.encoder u j = 0) : u = 0 := by
  have hu := erasureDecodeOrZero_eq k s
    Benchmark.IRSProfile.interleaving_dvd_totalDimension Benchmark.IRSProfile.domain
    (nodes := S) (w := 0) (m := u) (by simpa only [rowDimension_eq] using hcard) hzero
  have hz := erasureDecodeOrZero_eq k s
    Benchmark.IRSProfile.interleaving_dvd_totalDimension Benchmark.IRSProfile.domain
    (nodes := S) (w := 0) (m := (0 : Fin k → F))
    (by simpa only [rowDimension_eq] using hcard) (by
      intro j hj
      exact congrFun (map_zero Benchmark.IRSProfile.encoder) j)
  rw [← hu, hz]

theorem message_injective : Function.Injective message := by
  intro A B hAB
  by_contra hne
  have hval : A.1 ≠ B.1 := by
    intro h
    exact hne (Subtype.ext h)
  have hcardUnion : agreement <
      ((A.1 : Finset I) ∪ (B.1 : Finset I)).card := by
    obtain ⟨i, hiA, hiB⟩ :=
      (Set.powersetCard.exists_mem_notMem_iff_ne A.1 B.1).mp hval
    have hBsub : (B.1 : Finset I) ⊆
        (A.1 : Finset I) ∪ (B.1 : Finset I) := Finset.subset_union_right
    have hBstrict : (B.1 : Finset I) ⊂
        (A.1 : Finset I) ∪ (B.1 : Finset I) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hBsub, ?_⟩
      intro heq
      have hiUnion : i ∈ (A.1 : Finset I) ∪ (B.1 : Finset I) :=
        Finset.mem_union_left _ hiA
      have : i ∈ (B.1 : Finset I) := by rwa [← heq] at hiUnion
      exact hiB this
    have hlt := Finset.card_lt_card hBstrict
    simpa only [Set.powersetCard.card_eq B.1] using hlt
  apply no_message_agrees_on_more_than_agreement
    (message A) ((A.1 : Finset I) ∪ (B.1 : Finset I)) hcardUnion
  intro j hj
  rcases Finset.mem_union.mp hj with hjA | hjB
  · exact fixedWord_agrees A j hjA
  · rw [hAB]
    exact fixedWord_agrees B j hjB

theorem winningSetSoundness_eq_one
    (δ : ℝ≥0)
    (hδ : δ ∈ Set.Ico
      (ProximityGap.gridPt (ι := I) unsafeIndex)
      Benchmark.IRSProfile.minRelativeDistance) :
    winningSetDensity Benchmark.IRSProfile.encoder δ = 1 := by
  apply HalfRadiusCollision.winningSetSoundness_eq_one_of_large_fixed_word_list
    (F := F) Benchmark.IRSProfile.encoder δ
    (m := agreement) (z := rowK) (J := FiberSets)
    (p := message) (T := fun T => (T.1 : Finset I)) (f := fixedWord)
  · have hlt : (δ : ℝ) < 131073 / 262144 := by
      exact_mod_cast hδ.2
    norm_num [rowK, I, Benchmark.IRSProfile.Index,
      Benchmark.IRSProfile.minRelativeDistance] at hlt ⊢
    linarith
  · have hgeGrid :
        ((ProximityGap.gridPt (ι := I) unsafeIndex : ℝ≥0) : ℝ) ≤ (δ : ℝ) :=
      NNReal.coe_le_coe.mpr hδ.1
    have hge : (unsafeIndex : ℝ) / 262144 ≤ δ := by
      norm_num [ProximityGap.gridPt, unsafeIndex, I,
        Benchmark.IRSProfile.Index] at hgeGrid ⊢
      exact hgeGrid
    norm_num [agreement, unsafeIndex, I, Benchmark.IRSProfile.Index] at hge ⊢
    linarith
  · exact message_injective
  · exact card_fiberSets_large
  · intro T
    exact T.1.prop
  · exact fixedWord_agrees
  · exact message_eq_zero_of_zero_on_many

end IRSProfile
end ProximityPrize.SubmissionUpper.SubHalfPigeonhole
