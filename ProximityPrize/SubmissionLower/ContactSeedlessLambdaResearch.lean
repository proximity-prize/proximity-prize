import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSeedlessListBoundResearch
import ProximityPrize.SubmissionLower.AlignmentInterleavedLambda

/-! . -/

namespace ProximityPrize.SubmissionLower.ContactSeedlessLambdaResearch

open scoped Classical NNReal
open ProximityPrize.Benchmark
open ContactSeedlessInterpolationResearch ContactSeedlessListBoundResearch
open AlignmentMomentCurveProjection AlignmentInterleavedLambda
open ContactTranslation

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
local instance : CharP IRSProfile.Field prime := by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

/-- .

 -/
theorem irs_scalar_finite_list_card_le
    (received : IRSProfile.Index → IRSProfile.Field)
    (L : Finset (IRSProfile.Index → IRSProfile.Field))
    (hcode : ∀ c ∈ L, c ∈ IRSProfile.baseCode)
    (hclose : ∀ c ∈ L, agreements ≤
      (Finset.univ.filter (fun i => c i = received i)).card) :
    L.card ≤ listBudget := by
  classical
  let D := ↥L
  let codeword : D → IRSProfile.baseCode := fun c => ⟨c.1, hcode c.1 c.2⟩
  let selected : D → Polynomial IRSProfile.Field := fun c => ReedSolomon.toPolynomial (codeword c)
  let Gamma : Finset (Polynomial IRSProfile.Field) := Finset.univ.image selected
  have hselected : Function.Injective selected := by
    intro c d h
    apply Subtype.ext
    funext i
    have hh := congrArg (fun P : Polynomial IRSProfile.Field =>
      P.eval (IRSProfile.domain i)) h
    simpa only [selected, ReedSolomon.toPolynomial_eval_at_domain] using hh
  have hcard : Gamma.card = L.card := by
    rw [show Gamma = Finset.univ.image selected by rfl,
      Finset.card_image_of_injective _ hselected, Finset.card_univ,
      Fintype.card_coe]
  obtain ⟨Q, hQ, hbox, hlegacy, hvanish⟩ :=
    exists_frozen_seedless_vanishing_interpolant received
  have hdegree : ∀ P ∈ Gamma, P.natDegree ≤ w := by
    intro P hP
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hP
    have hp := ReedSolomon.toPolynomial_mem_lt_deg (codeword c)
    have hdeg : (selected c).degree < ((w + 1 : ℕ) : WithBot ℕ) := by
      have hh := Polynomial.mem_degreeLT.mp hp
      change (selected c).degree <
        ((IRSProfile.baseDimension : ℕ) : WithBot ℕ) at hh
      rw [show IRSProfile.baseDimension = w + 1 by
        norm_num [IRSProfile.baseDimension, w]] at hh
      exact hh
    by_cases hz : selected c = 0
    · simp [hz]
    · rw [← Polynomial.natDegree_lt_iff_degree_lt hz] at hdeg
      omega
  have hsolution : ∀ P ∈ Gamma, specialization IRSProfile.Field P 0 Q = 0 := by
    intro P hP
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hP
    let A := Finset.univ.filter (fun i => c.1 i = received i)
    apply hvanish (selected c) A (hdegree (selected c)
      (Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩))
      (hclose c.1 c.2)
    intro i hi
    have hcval := ReedSolomon.toPolynomial_eval_at_domain (c := codeword c) (i := i)
    exact hcval.trans (Finset.mem_filter.mp hi).2
  have hagreement : ∀ P ∈ Gamma, agreements ≤
      (Finset.univ.filter (fun i => P.eval (IRSProfile.domain i) = received i)).card := by
    intro P hP
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hP
    have heq : Finset.univ.filter
        (fun i => (selected c).eval (IRSProfile.domain i) = received i) =
        Finset.univ.filter (fun i => c.1 i = received i) := by
      apply Finset.filter_congr
      intro i hi
      rw [ReedSolomon.toPolynomial_eval_at_domain]
    rw [heq]
    exact hclose c.1 c.2
  have hbound := seedless_list_card_le IRSProfile.Field Q hQ hbox hlegacy Gamma
    (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain received
    IRSProfile.domain.injective.injOn
    (by norm_num [IRSProfile.Index, n]) hdegree hsolution hagreement
  rwa [hcard] at hbound

/-- .
 -/
theorem irs_interleaved_finite_list_card_le
    {r : ℕ}
    (received : IRSProfile.Index → Fin r → IRSProfile.Field)
    (L : Finset (IRSProfile.Index → Fin r → IRSProfile.Field))
    (hrows : ∀ v ∈ L, ∀ j : Fin r,
      (fun i => v i j) ∈ IRSProfile.baseCode)
    (hclose : ∀ v ∈ L, agreements ≤
      (Finset.univ.filter (fun i => v i = received i)).card)
    (hseparation : (r - 1) * (listBudget + 1).choose 2 <
      Fintype.card IRSProfile.Field) :
    L.card ≤ listBudget := by
  classical
  letI : DecidableEq (IRSProfile.Index → Fin r → IRSProfile.Field) := Classical.decEq _
  letI : DecidableEq (IRSProfile.Index → IRSProfile.Field) := Classical.decEq _
  by_contra hnot
  obtain ⟨D, hDL, hDcard⟩ :=
    Finset.exists_subset_card_eq (show listBudget + 1 ≤ L.card by omega)
  have hsepD : (r - 1) * D.card.choose 2 < Fintype.card IRSProfile.Field := by
    rw [hDcard]
    exact hseparation
  obtain ⟨t, ht⟩ := exists_separating_moment_parameter D hsepD
  let projected : Finset (IRSProfile.Index → IRSProfile.Field) :=
    D.image (momentProjection (ι := IRSProfile.Index) (r := r) t)
  have hprojcard : projected.card = D.card := Finset.card_image_of_injOn ht
  have hcode : ∀ c ∈ projected, c ∈ IRSProfile.baseCode := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    exact momentProjection_mem_code IRSProfile.baseCode t v (hrows v (hDL hv))
  have hnear : ∀ c ∈ projected, agreements ≤
      (Finset.univ.filter (fun i => c i = momentProjection t received i)).card := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    exact (hclose v (hDL hv)).trans
      (Finset.card_le_card (momentProjection_preserves_agreements t v received))
  have hbound := irs_scalar_finite_list_card_le (momentProjection t received)
    projected hcode hnear
  rw [hprojcard, hDcard] at hbound
  omega

theorem sixteen_row_separation :
    15 * (listBudget + 1).choose 2 < Fintype.card IRSProfile.Field := by
  rw [show Fintype.card IRSProfile.Field = (2130706433 : ℕ) ^ 6 by
    norm_num [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize],
    Nat.choose_eq_descFactorial_div_factorial]
  norm_num [listBudget, Nat.descFactorial_succ, Nat.factorial_succ]

/-- .
 -/
theorem squared_eight_lambda_le_of_interleaved_list
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (C : LinearCode ι F) (e B : ℕ)
    (hfinite : ∀ (received : ι → Fin 16 → F)
        (L : Finset (ι → Fin 16 → F)),
      (∀ v ∈ L, ∀ j : Fin 16, (fun i => v i j) ∈ C) →
      (∀ v ∈ L, Fintype.card ι - e ≤
        (Finset.univ.filter (fun i => v i = received i)).card) →
      L.card ≤ B)
    (delta : ℝ)
    (hcell : delta * (Fintype.card ι : ℝ) < ((e + 1 : ℕ) : ℝ)) :
    Code.Lambda
      (((C ^⋈ (Fin 8)) ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → Fin 8 → F)) :
        Set (ι → Fin 2 → Fin 8 → F)) delta ≤ (B : ℕ∞) := by
  classical
  letI : DecidableEq (ι → Fin 2 → Fin 8 → F) := Classical.decEq _
  letI : DecidableEq (ι → Fin 16 → F) := Classical.decEq _
  apply Code.Lambda_le_of_forall_finset_card_le
  intro received L hL
  let projected : Finset (ι → Fin 16 → F) := L.image flattenWord
  have hinj : Set.InjOn flattenWord (L : Set (ι → Fin 2 → Fin 8 → F)) :=
    fun _ _ _ _ hh => flattenWord_injective hh
  have hcard : projected.card = L.card := Finset.card_image_of_injOn hinj
  have hrows : ∀ v ∈ projected, ∀ j : Fin 16, (fun i => v i j) ∈ C := by
    intro v hv j
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
    have hcode := (Code.mem_closeCodewordsRel_iff.mp (hL c hc)).1
    change (fun i => c i (sixteenIndexEquiv.symm j).1
      (sixteenIndexEquiv.symm j).2) ∈ C
    exact squared_eight_rows C c hcode _ _
  have hclose : ∀ v ∈ projected, Fintype.card ι - e ≤
      (Finset.univ.filter (fun i => v i = flattenWord received i)).card := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
    rw [flattenWord_agreement_card]
    exact agreement_card_ge_of_closeCodewordsRel _ received c delta e hcell (hL c hc)
  have hbound := hfinite (flattenWord received) projected hrows hclose
  rwa [hcard] at hbound

/-- . -/
theorem squared_eight_lambda_seedless
    (delta : ℝ)
    (hcell : (delta : ℝ) * (Fintype.card IRSProfile.Index : ℝ) <
      ((errors + 1 : ℕ) : ℝ)) :
    Code.Lambda
      (((IRSProfile.baseCode ^⋈ (Fin 8)) ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin 8 → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field))
      delta ≤ (listBudget : ℕ∞) := by
  apply squared_eight_lambda_le_of_interleaved_list
    IRSProfile.baseCode errors listBudget ?_ delta hcell
  intro received L hrows hclose
  have hclose' : ∀ v ∈ L, agreements ≤
      (Finset.univ.filter (fun i => v i = received i)).card := by
    intro v hv
    simpa [agreements, n, errors, IRSProfile.Index] using hclose v hv
  classical
  letI : DecidableEq (IRSProfile.Index → Fin 16 → IRSProfile.Field) := Classical.decEq _
  letI : DecidableEq (IRSProfile.Index → IRSProfile.Field) := Classical.decEq _
  by_contra hnot
  obtain ⟨D, hDL, hDcard⟩ :=
    Finset.exists_subset_card_eq (show listBudget + 1 ≤ L.card by omega)
  have hsepD : 15 * D.card.choose 2 < Fintype.card IRSProfile.Field := by
    rw [hDcard]
    exact sixteen_row_separation
  obtain ⟨t, ht⟩ := exists_separating_moment_parameter D hsepD
  let projected : Finset (IRSProfile.Index → IRSProfile.Field) :=
    D.image (momentProjection (ι := IRSProfile.Index) (r := 16) t)
  have hprojcard : projected.card = D.card := Finset.card_image_of_injOn ht
  have hcode : ∀ c ∈ projected, c ∈ IRSProfile.baseCode := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    exact momentProjection_mem_code IRSProfile.baseCode t v (hrows v (hDL hv))
  have hnear : ∀ c ∈ projected, agreements ≤
      (Finset.univ.filter (fun i => c i = momentProjection t received i)).card := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    exact (hclose' v (hDL hv)).trans
      (Finset.card_le_card (momentProjection_preserves_agreements t v received))
  have hbound := irs_scalar_finite_list_card_le
    (momentProjection t received) projected hcode hnear
  rw [hprojcard, hDcard] at hbound
  omega

/-- . -/
theorem irs_squared_lambda_seedless
    (delta : ℝ≥0)
    (hcell : (delta : ℝ) * (Fintype.card IRSProfile.Index : ℝ) <
      ((errors + 1 : ℕ) : ℝ)) :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
      (delta : ℝ) ≤ (listBudget : ℕ∞) := by
  rw [irs_squared_carrier_eq]
  exact squared_eight_lambda_seedless (delta : ℝ) hcell

end

end ProximityPrize.SubmissionLower.ContactSeedlessLambdaResearch
