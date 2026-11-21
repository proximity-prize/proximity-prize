import ProximityPrize.SubmissionLower.Scalar50LeadingList
import ProximityPrize.SubmissionLower.Cell82219
import ProximityPrize.SubmissionLower.FrontRank282219
import ProximityPrize.SubmissionLower.FrontRank382219
import ProximityPrize.SubmissionLower.FrontRank482219
import ProximityPrize.SubmissionLower.FrontRank582219
import ProximityPrize.SubmissionLower.HighCore82219Finish

set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
namespace Protocol50Direct
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem FrobeniusLocator ProximityPrize.Benchmark
open Sol1.OneCount (squaredCode A16)
open ProtocolTarget82219 (I K Words node k agreement queryRadius radius BadFamily
  radiusNumerator radiusDenominator query_admissible query_score close_agreement_ge nativeBadSlopes)
open scoped NNReal
abbrev listCap : ℕ := 2302614105857199
abbrev scalarCap : ℕ := 272678114005537888
theorem scalar_projection_room : scalarCap + 1 < (0x7f000001 : ℕ) ^ 6 := by decide
theorem list_projection_room : (listCap + 1) ^ 2 < (0x7f000001 : ℕ) ^ 6 := by decide
theorem squared_lambda_le (hlist : CJ0.ScalarList agreement listCap) :
    Code.Lambda (squaredCode : Set (I → A16)) radius ≤ (listCap : ℕ∞) :=
  CJ0.squared_lambda_le hlist (Sol1.C64.native_field_card ▸ list_projection_room.le)
    radius close_agreement_ge
set_option linter.constructorNameAsVariable false in
theorem native_cap_of_scalar_cap
    (hscalar : ∀ u Γ, BadFamily u Γ → Γ.card ≤ scalarCap) (U : Sol1.C64.NativePair) :
    (nativeBadSlopes U).card ≤ scalarCap := by
  classical
  apply Sol1.C64.restricted_interleaved_card_le IRSProfile.baseCode
    (⊤ : ModuleCode I K K) radius scalarCap
    (by rw [Sol1.C64.native_field_card]; exact scalar_projection_room.le)
    (fun u _ Γ hΓ => hscalar u Γ hΓ) U (by simp) (nativeBadSlopes U)
  intro γ hγ
  change γ ∈ Finset.univ.filter (fun z => IsMCA (AffineLineGenerator K)
    IRSProfile.code z U radius) at hγ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
  rw [Sol1.C64.native_code_eq] at hγ
  exact hγ
theorem mca_error_le_of_scalar_cap (hscalar : ∀ u Γ, BadFamily u Γ → Γ.card ≤ scalarCap) :
    mcaError (AffineLineGenerator K) IRSProfile.code radius ≤
      (scalarCap : ENNReal) / (Fintype.card K : ENNReal) := by
  classical
  refine iSup_le fun U => ?_
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  change ENNReal.ofReal (((nativeBadSlopes U).card : ℝ) / Fintype.card K) ≤ _
  calc
    _ ≤ ENNReal.ofReal ((scalarCap : ℝ) / Fintype.card K) := by
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right (by exact_mod_cast native_cap_of_scalar_cap hscalar U)
        (by positivity)
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]
theorem error_budget :
    (scalarCap + listCap) * 2 ^ 128 ≤ (0x7f000001 : ℕ) ^ 6 := by decide
theorem gamma_error_le_of_scalar_cap (hlist : CJ0.ScalarList agreement listCap)
    (hscalar : ∀ u Γ, BadFamily u Γ → Γ.card ≤ scalarCap) :
    ToyProblem.certifiedGammaError IRSProfile.code queryRadius ≤ reductionTarget := by
  have hNat := ENat.toNat_le_of_le_natCast (squared_lambda_le hlist)
  have hList :
      ((Code.Lambda (squaredCode : Set (I → A16)) radius).toNat : ENNReal) /
        (Fintype.card K : ENNReal) ≤ (listCap : ENNReal) / Fintype.card K :=
    ENNReal.div_le_div_right (by exact_mod_cast hNat) _
  have hreal : ((scalarCap + listCap : ℕ) : ℝ) / Fintype.card K ≤ (1 : ℝ) / 2 ^ 128 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    norm_num only [one_mul]
    exact_mod_cast (Sol1.C64.native_field_card ▸ error_budget :
      (scalarCap + listCap) * 2 ^ 128 ≤ Fintype.card K)
  have hENN : ((scalarCap + listCap : ℕ) : ENNReal) / Fintype.card K ≤
      (1 : ENNReal) / 2 ^ 128 := by
    have h := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast, ENNReal.ofReal_div_of_pos (by positivity)] at h
    simpa using h
  rw [← ENNReal.coe_le_coe, ToyProblem.coe_certifiedGammaError]
  calc
    _ ≤ (scalarCap : ENNReal) / Fintype.card K + (listCap : ENNReal) / Fintype.card K :=
      add_le_add (mca_error_le_of_scalar_cap hscalar) hList
    _ = ((scalarCap + listCap : ℕ) : ENNReal) / Fintype.card K := by
      rw [← ENNReal.add_div, Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ 128 := hENN
    _ = (reductionTarget : ENNReal) := by
      norm_num [reductionTarget, ProximityGap.prizeThreshold]
theorem protocol_claim_of_scalar_cap (hlist : CJ0.ScalarList agreement listCap)
    (hscalar : ∀ u Γ, BadFamily u Γ → Γ.card ≤ scalarCap) :
    ProtocolClaim 6950 radiusNumerator radiusDenominator where
  admissible := query_admissible
  reduction := gamma_error_le_of_scalar_cap hlist hscalar
  score := query_score


end
end Protocol50Direct

namespace Front50Direct
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark Front82219
abbrev slopeBudget : ℕ := Protocol50Direct.scalarCap
abbrev coreBudget : ℕ := 272535931964886069
def CoreCount : Prop := ∀ u deleted (M : AnchorModel u deleted) Γ, AnchoredFamily M Γ →
    1 ≤ M.overhead → M.overhead ≤ (heightCap : ℤ) → Γ.card ≤ coreBudget

private theorem coherent_count (h5 : c5) (hc : CoreCount)
    (u : Words) (hu : FrontRemainder u) (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D) (hsat : NormalSaturation R)
    (hp : Parallel B) (hn : UnitNorm B) (Γ : Finset K) (hΓ : BadFamily u Γ) :
    Γ.card ≤ slopeBudget := by
  classical
  let N := normalSlopes u Γ
  rcases h5 u hu T R D B hsat hp hn N (normal_badFamily hΓ) normal_on_normalSlopes with
    hcheap | ⟨book, hs, hb, M, ⟨F⟩⟩
  · exact (add_rank_exceptions u hu Γ _ hcheap).trans (by decide)
  · have htotal : Γ.card ≤ (N \ book).card + book.card + rankFee :=
      add_rank_exceptions u hu Γ _ (Finset.card_sdiff_add_card_eq_card hs).ge
    have hreserve (b : ℕ) (h : (N \ book).card ≤ b) : Γ.card ≤ b + anchorFee + rankFee :=
      htotal.trans (Nat.add_le_add_right (Nat.add_le_add h hb) rankFee)
    have hwmax : M.overhead ≤ (heightCap : ℤ) := by
      have hh : M.E.natDegree + amplitudeDegree M.A₀ M.A₁ ≤ heightCap := M.height_bound
      change (M.E.natDegree : ℤ) - M.factor.natDegree - amplitudeDegree M.A₀ M.A₁ ≤ heightCap
      omega
    by_cases hw₀ : M.overhead ≤ 0
    · exact (hreserve _ (P1.anchored_list_count Scalar50LeadingList.scalar_list M _ F hw₀)).trans (by decide)
    · exact (hreserve _ (hc u _ M _ F (by omega) hwmax)).trans (by decide)
private theorem scalar_count (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4)
    (h5 : c5) (hc : CoreCount)
    (u : Words) (Γ : Finset K) (hΓ : BadFamily u Γ) : Γ.card ≤ slopeBudget := by
  classical
  by_cases hdef : firstRank u < L
  · exact (deficient_count u Γ hdef hΓ).trans (by decide)
  have hfirst := Nat.le_antisymm (firstRank_le u) (Nat.le_of_not_gt hdef)
  by_cases hz : nullity u = 0
  · exact (full_column_count u Γ hfirst hz hΓ).trans (by decide)
  by_cases htype : TypeAtMostOne u
  · exact (type_one_count u htype Γ hΓ).trans (by decide)
  by_cases hprincipal : HomogeneousPrincipal u
  · exact (principal_count u Γ hprincipal hΓ).trans (by decide)
  by_cases hconstant : ConstantKernel u
  · exact (constant_count u Γ hconstant hΓ).trans (by decide)
  obtain ⟨T⟩ := two_active_of_positive u (Nat.pos_of_ne_zero hz) htype hprincipal
  have hu : FrontRemainder u := ⟨two_active_nullity T, hfirst, htype, hprincipal, hconstant⟩
  let R := relation_of_two_active hu T
  have hsat := h1 u hu T R
  let N := normalSlopes u Γ
  have hN := normal_badFamily hΓ
  have hnormal := @normal_on_normalSlopes u Γ
  by_cases hmoving : MovingGCD R
  · exact (add_rank_exceptions u hu Γ _ (moving_count u hu T R hmoving hsat N hN hnormal)).trans
      (by decide)
  have hnone (he : N = ∅) : Γ.card ≤ slopeBudget :=
    (add_rank_exceptions u hu Γ 0 (by rw [show normalSlopes u Γ = ∅ from he]; simp)).trans
      (by decide)
  by_cases hinvalid : InvalidLeft R
  · apply hnone
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro γ hγ
    obtain ⟨hγΓ, hnγ⟩ := mem_normalSlopes.mp hγ
    obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγΓ
    exact (hsat γ hnγ M).valid hinvalid
  by_cases hne : N.Nonempty
  · obtain ⟨γ, hγ⟩ := hne
    obtain ⟨hγΓ, hnγ⟩ := mem_normalSlopes.mp hγ
    obtain ⟨D, hfour | ⟨B, hnp | hpar⟩⟩ := classify_fixed hu T R hmoving hinvalid hsat
      ⟨γ, hnγ, bad_mark u Γ hΓ γ hγΓ⟩
    · exact (add_rank_exceptions u hu Γ _ (h4 u hu T R D hsat hfour N hN hnormal)).trans
        (by decide)
    · exact (add_rank_exceptions u hu Γ _ (h3 u hu T R D B hsat hnp N hN hnormal)).trans
        (by decide)
    · by_cases hn : UnitNorm B
      · exact coherent_count h5 hc u hu T R D B hsat hpar hn Γ hΓ
      · exact (add_rank_exceptions u hu Γ _ (h2 u hu T R D B hsat hpar hn N hN hnormal)).trans
          (by decide)
  · exact hnone (Finset.not_nonempty_iff_eq_empty.mp hne)


/-- A bound through 2,404 joins the checked high range at 2,405. -/
theorem of_low (low : ∀ u del (M : AnchorModel u del) Γ, AnchoredFamily M Γ →
    1 ≤ M.overhead → M.overhead ≤ 2404 → Γ.card ≤ coreBudget) :
    ProtocolClaim 6950 ProximityPrize.SubmissionLower.Cell82219.p
      ProximityPrize.SubmissionLower.Cell82219.q := by
  apply ProximityPrize.SubmissionLower.Cell82219.extend
  apply Protocol50Direct.protocol_claim_of_scalar_cap Scalar50LeadingList.scalar_list
  apply scalar_count Front82219_1.proof Front82219_2.proof
    (Front82219_3.of_children Front82219_3_1.proof Front82219_3_2.proof)
    (Front82219_4.of_children Front82219_4_1.proof Front82219_4_2.proof) Front82219_5.proof
  intro u del M Γ F lo hi
  by_cases high : 2405 ≤ M.overhead
  · exact (HighCore82219.ordinary_high M F high hi).trans (by decide)
  · exact low u del M Γ F lo (by omega)

#print axioms of_low
end
end Front50Direct
