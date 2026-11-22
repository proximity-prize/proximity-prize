import ProximityPrize.SubmissionLower.FrontBranch12

-- merged module ProtocolTarget82200
section Merged_ProtocolTarget82200
set_option Elab.async false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace ProtocolTarget82200
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem
open FrobeniusLocator ProximityPrize.Benchmark
open Sol1.OneCount Sol1.FiniteRowProjection
abbrev I := P3.I
abbrev K := P3.K
abbrev Words := P3.Words
abbrev node := P3.node
abbrev k := P3.k
open scoped NNReal

abbrev agreement : ℕ := 179886
abbrev radiusNumerator : ℕ := 336932863
abbrev radiusDenominator : ℕ := 1073741824
abbrev listCap : ℕ := 6965751486339445
abbrev scalarCap : ℕ := 268014976625055642
def queryRadius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator
def radius : ℝ := queryRadius
def BadFamily (u : Words) (Γ : Finset K) : Prop :=
  ∀ γ ∈ Γ, IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius

theorem agreement_of_threshold {s : ℕ}
    (hs : (Fintype.card I : ℝ) * (1-radius) ≤ s) : agreement ≤ s := by
  rw [IRSProfile.card_index] at hs
  have p : (179885 : ℝ) < 262144*(1-radius) := by norm_num [radius, queryRadius, claimedRadius]
  exact (show 179885 < s by exact_mod_cast p.trans_le hs)
theorem query_score : (1 - queryRadius) ^ IRSProfile.repetitions ≤ claimedError 6954 := by
  have hcomplement : (1 - queryRadius : ℝ≥0) = 736808961 / 0x40000000 := by
    apply NNReal.coe_injective
    have hr : queryRadius ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [queryRadius, claimedRadius]
    rw [NNReal.coe_sub hr]
    norm_num [queryRadius, claimedRadius]
  change (1 - queryRadius) ^ 128 ≤ claimedError 6954
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (100 : ℕ) ≠ 0)).mp
  rw [← pow_mul, Sol1.C42.claimedError_pow_100, hcomplement]
  change ((736808961 : ℝ≥0) / 0x40000000) ^ 12800 ≤ 1 / (2 : ℝ≥0) ^ 6954
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast (show (736808961 : ℕ)^12800 * 2^6954 ≤ 1073741824^12800 by decide +kernel)
theorem query_admissible : queryRadius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;> norm_num [queryRadius, claimedRadius, IRSProfile.minRelativeDistance]
theorem scalar_projection_room : scalarCap + 1 < (0x7f000001 : ℕ) ^ 6 := by decide
theorem list_projection_room : (listCap + 1) ^ 2 < (0x7f000001 : ℕ) ^ 6 := by decide
theorem close_agreement_ge (f w : I → A16)
    (hd : (δᵣ(w,f) : ℝ) ≤ radius) : agreement ≤ agreementCard f w := by
  classical
  have hpos : 0 < Fintype.card I := by rw [IRSProfile.card_index]; decide
  have hposR : (0 : ℝ) < Fintype.card I := by exact_mod_cast hpos
  have hradius : radius =
      1 - ((Fintype.card I : ℝ) * (1 - radius)) / Fintype.card I := by
    rw [mul_comm, mul_div_cancel_right₀ _ hposR.ne']
    ring
  have hagree := (Code.relHammingDist_le_one_sub_div_iff hpos).mp
    (show (δᵣ(w,f) : ℝ) ≤ 1 - ((Fintype.card I : ℝ) * (1 - radius)) / Fintype.card I by
      rwa [← hradius])
  have hcard : Code.agree f w ≤ agreementCard f w := by
    unfold Code.agree agreementCard
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi
  exact (agreement_of_threshold hagree).trans hcard
theorem squared_lambda_le (hlist : CJ0.ScalarList agreement listCap) :
    Code.Lambda (squaredCode : Set (I → A16)) radius ≤ (listCap : ℕ∞) :=
  CJ0.squared_lambda_le hlist (Sol1.C64.native_field_card ▸ list_projection_room.le)
    radius close_agreement_ge
def nativeBadSlopes (U : Sol1.C64.NativePair) : Finset K := by
  classical
  exact Finset.univ.filter fun γ => IsMCA (AffineLineGenerator K) IRSProfile.code γ U radius
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
    ProtocolClaim 6954 radiusNumerator radiusDenominator where
  admissible := query_admissible
  reduction := gamma_error_le_of_scalar_cap hlist hscalar
  score := query_score

/-- The list bound and the uniform bound on bad slopes suffice for the soundness claim. -/
theorem of_bad_slopes (hlist : CJ0.ScalarList agreement listCap)
    (bound : ∀ (u : Words) (Γ : Finset K),
    (∀ γ ∈ Γ, Principal.BadSlope node (u 0) (u 1) k agreement γ) → Γ.card ≤ scalarCap) :
    ProtocolClaim 6954 336932863 1073741824 := by
  apply protocol_claim_of_scalar_cap hlist
  intro u Γ hΓ
  apply bound u Γ
  intro γ hγ
  let : NeZero k := ⟨by decide⟩
  exact Principal.isMCA_implies_badSlope node u k agreement radius
    (fun _ h => agreement_of_threshold h) γ (hΓ γ hγ)

#print axioms of_bad_slopes
end
end ProtocolTarget82200
end Merged_ProtocolTarget82200

-- merged module FrontParams82200
section Merged_FrontParams82200
set_option Elab.async false
set_option autoImplicit true
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace Front82200
noncomputable section
open Polynomial Matrix CoreDefinitions Code FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators NNReal
export P0 (K I Words node p blockLength k Frac Bivar TypeAtMostOne coefficientBlocks
  extendSeed IsCommonGCD atSlope seed liftX twist amplitudeDegree sixNorm columnRank
  threeU threeV sameDirection relationOn)
abbrev Rung := P1.Rung
abbrev target : Rung := ⟨179886, 336932863, 1073741824, 2413, 268014976625055642, 6965751486339445⟩
abbrev agreement := target.agreement
abbrev radiusNumerator := target.numerator
abbrev radiusDenominator := target.denominator
abbrev lowCutoff : ℤ := target.lowEnd
abbrev scalarCap := target.mcaBound
abbrev listCap := target.listBound
abbrev t : ℕ := blockLength - agreement
abbrev L : ℕ := agreement - k
abbrev heightCap : ℕ := t + 1 - L - 2
abbrev rankFee : ℕ := 71257215287633
abbrev anchorFee : ℕ := 71257215567851
def queryRadius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator
def radius : ℝ := queryRadius
def BadFamily (u : Words) (Γ : Finset K) : Prop :=
  ∀ γ ∈ Γ, IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius
abbrev BadMarkAt := P1.BadMarkAt
abbrev BadMark := BadMarkAt agreement
def ordinary (u : Words) := hankel node (u 0) (u 1) L t
def twoBlock (u : Words) := stacked p node (u 0) (u 1) L t
def firstRank (u : Words) := GenericLayer.genericRank (ordinary u)
def stackRank (u : Words) := GenericLayer.genericRank (twoBlock u)
def nullity (u : Words) := GenericLayer.genericNullity (twoBlock u)
def Normal (u : Words) (γ : K) : Prop :=
  ((twoBlock u).map (evalRingHom γ)).rank = stackRank u
def normalSlopes (u : Words) (Γ : Finset K) : Finset K := by
  classical exact Γ.filter (Normal u)
def abnormalSlopes (u : Words) (Γ : Finset K) : Finset K := by
  classical exact Γ.filter (fun γ => ¬ Normal u γ)
def HomogeneousPrincipal (u : Words) : Prop :=
  ∃ (a : ℕ) (g : Frac[X]), g ≠ 0 ∧ g.natDegree ≤ a ∧ a ≤ t ∧
    ∀ P : Frac[X], P.natDegree ≤ t →
      (((twoBlock u).map (algebraMap K[X] Frac)).mulVec (fun i => P.coeff i.val) = 0 ↔
        ∃ Q : Frac[X], Q.natDegree ≤ t - a ∧ P = g * Q)
abbrev coefficientStack (u : Words) := coefficientBlocks p node (u 0) (u 1) L t
def ConstantKernel (u : Words) : Prop :=
  stackRank u = (coefficientStack u).rank
def FrontRemainder (u : Words) : Prop :=
  2 ≤ nullity u ∧ firstRank u = L ∧ ¬ TypeAtMostOne u ∧
    ¬ HomogeneousPrincipal u ∧ ¬ ConstantKernel u
structure TwoActive (u : Words) where
  a : ℕ
  b : ℕ
  c : ℕ
  ab : a ≤ b
  active : b ≤ t
  inactive : t < c
  top : c ≤ k
  degreeSum : a + b + c = 2 * k + 2
  nullitySum : nullity u + a + b = 2 * (t + 1)
  level : Strata.HasLevelHilbertFunction
    (fun s j => algebraMap K[X] Frac (Principal.parameterSyndromes p node (u 0) (u 1) s j))
    k a b c
def TwoActive.height {u : Words} (T : TwoActive u) := (k + 1) - T.c
abbrev Relation {u : Words} (T : TwoActive u) :=
  Strata.PolynomialRelationCertificate p node (u 0) (u 1) k T.height
def leftU {u : Words} {T : TwoActive u} (R : Relation T) : Bivar :=
  Principal.assemble (fun j => R.coefficients (0, j))
def leftV {u : Words} {T : TwoActive u} (R : Relation T) : Bivar :=
  Principal.assemble (fun j => R.coefficients (1, j))
def fixedNodes {u : Words} {T : TwoActive u} (R : Relation T) : Finset I := by
  classical
  exact Finset.univ.filter fun i =>
    (leftU R).eval (C (node i)) = 0 ∧ (leftV R).eval (C (node i)) = 0
def FixedLeftGCD {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  ∃ G : K[X], IsCommonGCD (G.map (algebraMap K Frac))
    (extendSeed (leftU R)) (extendSeed (leftV R))
def MovingGCD {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  ¬ FixedLeftGCD R ∧ ∃ G : Frac[X], G ≠ 0 ∧ G ∣ extendSeed (leftU R) ∧
    G ∣ extendSeed (leftV R) ∧ (fixedNodes R).card < G.natDegree
def InvalidLeft {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  max (leftU R).natDegree (leftV R).natDegree < T.height ∨
    ∃ G : K[X], G ≠ 0 ∧ G.map Polynomial.C ∣ leftU R ∧ G.map Polynomial.C ∣ leftV R ∧
      ¬ G ∣ locator node Finset.univ
structure SaturatedAt {u : Words} {T : TwoActive u} (R : Relation T)
    {γ : K} (M : BadMark u γ) : Prop where
  U_ne : atSlope (leftU R) γ ≠ 0
  V_ne : atSlope (leftV R) γ ≠ 0
  degree_eq : max (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree =
    T.height
  gcd_errors : ∃ errors : Finset I,
    (∀ i ∈ errors, M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i) ∧
    IsCommonGCD (locator node errors) (atSlope (leftU R) γ) (atSlope (leftV R) γ)
  fixed_errors : ∀ i ∈ fixedNodes R, M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i
  valid : ¬ InvalidLeft R
def NormalSaturation {u : Words} {T : TwoActive u} (R : Relation T) : Prop :=
  ∀ γ, Normal u γ → ∀ M : BadMark u γ, SaturatedAt R M
structure Reduction (u : Words) (T : TwoActive u) (R : Relation T) where
  U : Bivar
  V : Bivar
  output : Bivar
  height : ℕ
  height_eq : height + (fixedNodes R).card = T.height
  max_degree : max U.natDegree V.natDegree = height
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  coprime : IsCoprime (extendSeed U) (extendSeed V)
  U_factor : leftU R = liftX (locator node (fixedNodes R)) * U
  V_factor : leftV R = liftX (locator node (fixedNodes R)) * V
  output_factor : R.output = liftX (locator node (fixedNodes R)) * output
  output_degree : output.degree < (k + height : ℕ)
  deleted_error : ∀ γ, Normal u γ → ∀ M : BadMark u γ, ∀ i ∈ fixedNodes R,
    M.decoder.eval (node i) ≠ u 0 i + γ * u 1 i
structure RankThree (u : Words) (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) where
  rank_eq : columnRank D.U D.V = 3
  α : Fin 2 → K[X]
  β : Fin 2 → K[X]
  a : K[X]
  b : K[X]
  a_ne : a ≠ 0
  b_ne : b ≠ 0
  α_primitive : IsCoprime (α 0) (α 1)
  β_primitive : IsCoprime (β 0) (β 1)
  first_degree : a.natDegree + amplitudeDegree (β 0) (β 1) ≤ D.height
  second_degree : b.natDegree + amplitudeDegree (α 0) (α 1) ≤ D.height
  same_direction : sameDirection D.U D.V (threeU a β) (threeV b α)
  output : Bivar
  output_degree : output.degree < (k + D.height : ℕ)
  nodes : relationOn u (fixedNodes R) (threeU a β) (threeV b α) output
def Parallel {u T R D} (B : RankThree u T R D) : Prop :=
  B.α = B.β
def Nonparallel {u T R D} (B : RankThree u T R D) : Prop :=
  B.α 0 * B.β 1 - B.α 1 * B.β 0 ≠ 0
def UnitNorm {u T R D} (B : RankThree u T R D) : Prop :=
  sixNorm B.a = sixNorm B.b
abbrev ModelAt := P1.ModelAt
abbrev MarkAt := @P1.MarkAt
abbrev FamilyAt := @P1.FamilyAt
abbrev ModelAt.overhead := @P1.ModelAt.overhead
abbrev AnchorModel := ModelAt heightCap
abbrev AnchorMark {u deleted} (M : AnchorModel u deleted) := MarkAt (A := agreement) M
abbrev AnchoredFamily {u deleted} (M : AnchorModel u deleted) := FamilyAt agreement M
abbrev AnchorModel.overhead {u deleted} (M : AnchorModel u deleted) := ModelAt.overhead M
abbrev lowCap : ℕ := 267872462194200158
abbrev highCap : ℕ := 267872462194200158
end
end Front82200
end
end Merged_FrontParams82200

set_option Elab.async false

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
namespace Front82200
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open K1_8 (seedInclusion seedInclusion_injective extendSeed_injective
  lift_locator_dvd coprime_after_factor)
open private certificate_output_zero from ProximityPrize.SubmissionLower.Fast068
open private eval_liftX constantsInFrac extend_liftX from ProximityPrize.SubmissionLower.RungFront
private theorem mem_fixed_iff {u : Words} {T : TwoActive u} (R : Relation T) (i : I) :
    i ∈ fixedNodes R ↔ (leftU R).eval (C (node i)) = 0 ∧ (leftV R).eval (C (node i)) = 0 := by
  classical
  simp [fixedNodes]
private theorem fixed_case_maximal {u : Words} {T : TwoActive u} (R : Relation T)
    (hi : ¬ InvalidLeft R) (hf : FixedLeftGCD R) :
    ∀ H : Frac[X], H ∣ extendSeed (leftU R) → H ∣ extendSeed (leftV R) →
      H ∣ extendSeed (liftX (locator node (fixedNodes R))) := by
  classical
  obtain ⟨g, hg, hgu, hgv, hgmax⟩ := hf
  change g.map constantsInFrac ≠ 0 at hg
  change g.map constantsInFrac ∣ _ at hgu hgv
  change ∀ H : Frac[X], H ∣ extendSeed (leftU R) → H ∣ extendSeed (leftV R) →
    H ∣ g.map constantsInFrac at hgmax
  have hg0 : g ≠ 0 := by
    intro hz
    exact hg (by rw [hz, Polynomial.map_zero])
  let g₀ := g * C g.leadingCoeff⁻¹
  have hm : g₀.Monic := monic_mul_leadingCoeff_inv hg0
  have hnorm (P : Frac[X]) (hd : g.map constantsInFrac ∣ P) :
      g₀.map constantsInFrac ∣ P := by
    apply ((Polynomial.map_dvd_map' constantsInFrac).mpr ?_).trans hd
    exact (dvd_mul_leadingCoeff_inv hg0).mp dvd_rfl
  have hlift (P : Bivar) (hd : g.map constantsInFrac ∣ extendSeed P) :
      liftX g₀ ∣ P := by
    apply (Polynomial.map_dvd_map seedInclusion seedInclusion_injective (hm.map Polynomial.C)).mp
    change extendSeed (liftX g₀) ∣ extendSeed P
    rw [extend_liftX]
    exact hnorm _ hd
  have hu := hlift _ hgu
  have hv := hlift _ hgv
  have hdom : g₀ ∣ locator node Finset.univ := by
    by_contra h
    exact hi (Or.inr ⟨g₀, hm.ne_zero, hu, hv, h⟩)
  obtain ⟨S, _, _, t, ht, hS⟩ :=
    Strata.split_divisor_locator_factor node IRSProfile.domain.injective Finset.univ g₀ hm.ne_zero hdom
  have hsub : S ⊆ fixedNodes R := by
    intro i his
    have hz : g₀.eval (node i) = 0 := by
      rw [hS, eval_smul, locator_eval_zero node S i his, smul_zero]
    have hlzero : (liftX g₀).eval (C (node i)) = 0 := by
      rw [eval_liftX, hz, C_0]
    obtain ⟨U, hU⟩ := hu
    obtain ⟨V, hV⟩ := hv
    exact (mem_fixed_iff R i).mpr ⟨by rw [hU, eval_mul, hlzero, zero_mul],
      by rw [hV, eval_mul, hlzero, zero_mul]⟩
  have hg₀dvd : g₀ ∣ locator node (fixedNodes R) := by
    rw [hS, Polynomial.smul_eq_C_mul, (isUnit_C.mpr (isUnit_iff_ne_zero.mpr ht)).mul_left_dvd]
    exact Strata.locator_dvd_of_eval_zero node IRSProfile.domain.injective S _
      (fun i his => locator_eval_zero node _ i (hsub his))
  intro H hU hV
  rw [extend_liftX]
  exact (hgmax H hU hV).trans
    ((Polynomial.map_dvd_map' constantsInFrac).mpr
      ((dvd_mul_right g (C g.leadingCoeff⁻¹)).trans hg₀dvd))
theorem fixed_gcd {u : Words} {T : TwoActive u} (R : Relation T)
    (hu : leftU R ≠ 0) (hm : ¬ MovingGCD R) (hi : ¬ InvalidLeft R) :
    IsCommonGCD (extendSeed (liftX (locator node (fixedNodes R))))
      (extendSeed (leftU R)) (extendSeed (leftV R)) := by
  classical
  let S := fixedNodes R
  let Δ := liftX (locator node S)
  let A := extendSeed (leftU R)
  let B := extendSeed (leftV R)
  have hΔ : Δ.Monic := (locator_monic node S).map Polynomial.C
  have hΔ0 : extendSeed Δ ≠ 0 := (hΔ.map seedInclusion).ne_zero
  have hA0 : A ≠ 0 :=
    fun h => hu (extendSeed_injective (h.trans (Polynomial.map_zero _).symm))
  have hΔA : extendSeed Δ ∣ A := by
    exact _root_.map_dvd (Polynomial.mapRingHom seedInclusion)
      (lift_locator_dvd S (leftU R) (fun i h => ((mem_fixed_iff R i).mp h).1))
  have hΔB : extendSeed Δ ∣ B := by
    exact _root_.map_dvd (Polynomial.mapRingHom seedInclusion)
      (lift_locator_dvd S (leftV R) (fun i h => ((mem_fixed_iff R i).mp h).2))
  refine ⟨hΔ0, hΔA, hΔB, ?_⟩
  by_cases hf : FixedLeftGCD R
  · exact fixed_case_maximal R hi hf
  let G := EuclideanDomain.gcd A B
  have hGA : G ∣ A := EuclideanDomain.gcd_dvd_left _ _
  have hGB : G ∣ B := EuclideanDomain.gcd_dvd_right _ _
  have hG : G ≠ 0 := fun hz => hA0 (zero_dvd_iff.mp (hz ▸ hGA))
  have hGd : G.natDegree ≤ S.card := by
    apply Nat.le_of_not_gt
    exact fun h => hm ⟨hf, G, hG, hGA, hGB, h⟩
  have hΔd : (extendSeed Δ).natDegree = S.card := by
    rw [extend_liftX, natDegree_map_eq_of_injective constantsInFrac.injective, locator_natDegree]
  obtain ⟨q, hq⟩ := EuclideanDomain.dvd_gcd hΔA hΔB
  change G = extendSeed Δ * q at hq
  have hq0 : q ≠ 0 := by intro h; exact hG (by rw [hq, h, mul_zero])
  have hd := congrArg Polynomial.natDegree hq
  rw [natDegree_mul hΔ0 hq0, hΔd] at hd
  have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
  have hqU : IsUnit q := by
    rw [hqC, isUnit_C, isUnit_iff_ne_zero]
    intro hz
    exact hq0 (by rwa [hz, C_0] at hqC)
  intro H hHA hHB
  have hHG : H ∣ G := EuclideanDomain.dvd_gcd hHA hHB
  rwa [hq, hqU.dvd_mul_right] at hHG
theorem puncture {u : Words} {T : TwoActive u} (R : Relation T)
    (hs : NormalSaturation R) (hw : ∃ γ, Normal u γ ∧ Nonempty (BadMark u γ))
    (hgcd : IsCommonGCD (extendSeed (liftX (locator node (fixedNodes R))))
      (extendSeed (leftU R)) (extendSeed (leftV R))) : Nonempty (Reduction u T R) := by
  classical
  obtain ⟨γ, hγ, ⟨M⟩⟩ := hw
  have h := hs γ hγ M
  let B := fixedNodes R
  let G := liftX (locator node B)
  have hG : G.Monic := (locator_monic node B).map Polynomial.C
  have hGd : G.natDegree = B.card := by
    change ((locator node B).map Polynomial.C).natDegree = _
    rw [Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective, locator_natDegree]
  obtain ⟨U, hU⟩ := lift_locator_dvd B (leftU R)
    (fun i hi => (mem_fixed_iff R i |>.mp hi).1)
  obtain ⟨V, hV⟩ := lift_locator_dvd B (leftV R)
    (fun i hi => (mem_fixed_iff R i |>.mp hi).2)
  obtain ⟨W, hW⟩ := lift_locator_dvd B R.output (fun i hi => by
    have hroot := (mem_fixed_iff R i).mp hi
    exact certificate_output_zero R i hroot.1 hroot.2)
  have hu : U ≠ 0 := by
    intro hz
    apply h.U_ne
    rw [hU, hz, mul_zero, atSlope, Polynomial.map_zero]
  have hv : V ≠ 0 := by
    intro hz
    apply h.V_ne
    rw [hV, hz, mul_zero, atSlope, Polynomial.map_zero]
  have hdeg : max (leftU R).natDegree (leftV R).natDegree = T.height := by
    apply le_antisymm (max_le (R.x_degree 0) (R.x_degree 1))
    exact Nat.le_of_not_gt fun hlt => h.valid (Or.inl hlt)
  have hdu := congrArg Polynomial.natDegree hU
  have hdv := congrArg Polynomial.natDegree hV
  change (leftU R).natDegree = (G * U).natDegree at hdu
  change (leftV R).natDegree = (G * V).natDegree at hdv
  rw [natDegree_mul hG.ne_zero hu, hGd] at hdu
  rw [natDegree_mul hG.ne_zero hv, hGd] at hdv
  let H := max U.natDegree V.natDegree
  have hH : H + B.card = T.height := by
    dsimp [H]
    omega
  have hout : W.degree < (k + H : ℕ) := by
    by_cases hzero : W = 0
    · rw [hzero, degree_zero]
      exact WithBot.bot_lt_coe _
    have hRout : R.output ≠ 0 := by rw [hW]; exact mul_ne_zero hG.ne_zero hzero
    have hd := (natDegree_lt_iff_degree_lt hRout).mpr R.output_degree
    rw [hW] at hd
    change (G * W).natDegree < _ at hd
    rw [natDegree_mul hG.ne_zero hzero, hGd] at hd
    exact (natDegree_lt_iff_degree_lt hzero).mp (by omega)
  have hcop : IsCoprime (extendSeed U) (extendSeed V) := by
    apply coprime_after_factor (extendSeed G) _ _ hgcd.1
      (fun hz => hu (extendSeed_injective (hz.trans (Polynomial.map_zero _).symm)))
    intro Q hqu hqv
    apply hgcd.2.2.2 Q
    · rw [hU, extendSeed, Polynomial.map_mul]
      exact hqu
    · rw [hV, extendSeed, Polynomial.map_mul]
      exact hqv
  exact ⟨⟨U, V, W, H, hH, rfl, hu, hv, hcop, hU, hV, hW, hout,
    fun γ hn M => (hs γ hn M).fixed_errors⟩⟩
end
end Front82200
end
section
set_option maxRecDepth 12000
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
namespace Front82200
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem
open FrobeniusLocator ProximityPrize.Benchmark
open Sol1.OneCount Sol1.FiniteRowProjection
open scoped NNReal
abbrev agreement_of_threshold := @ProtocolTarget82200.agreement_of_threshold
theorem bad_slope (u : Words) (γ : K)
    (hγ : IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u radius) :
    Principal.BadSlope node (u 0) (u 1) k agreement γ := by
  let : NeZero k := ⟨by decide⟩
  exact Principal.isMCA_implies_badSlope node u k agreement radius
    (fun _ hT => agreement_of_threshold hT) γ hγ
theorem bad_mark (u : Words) (Γ : Finset K) (hΓ : BadFamily u Γ) (γ : K) (hγ : γ ∈ Γ) :
    Nonempty (BadMark u γ) := by
  obtain ⟨S, hS, ⟨P, hP, he⟩, hn⟩ := bad_slope u γ (hΓ γ hγ)
  exact ⟨⟨S, P, hS, hP, he, hn⟩⟩
end
end Front82200
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace Front82200
noncomputable section
open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open scoped BigOperators
theorem firstRank_le (u : Words) : firstRank u ≤ L := by
  simpa only [firstRank, GenericLayer.genericRank, Fintype.card_fin] using
    Matrix.rank_le_card_height ((ordinary u).map (algebraMap K[X] Frac))
theorem actual_stackRank (u : Words) : stackRank u = t + 1 - nullity u := by
  have h := GenericLayer.rank_add_nullity (twoBlock u)
  simp only [Fintype.card_fin] at h
  change stackRank u + nullity u = t + 1 at h
  omega
theorem relation_height_balance {u : Words} (T : TwoActive u) :
    L + T.height + nullity u = t + 1 := by
  exact Strata.relation_degree_nullity_balance k L t (nullity u) T.a T.b T.c
    (by decide) T.top T.degreeSum (by have := T.nullitySum; omega)
theorem relation_height_le {u : Words} (hu : FrontRemainder u) (T : TwoActive u) :
    T.height ≤ heightCap := by
  have h := relation_height_balance T
  have hr := hu.1
  change 48814 + T.height + nullity u = 82259 at h
  change T.height ≤ 33443
  omega
def relation_of_two_active {u : Words} (hu : FrontRemainder u) (T : TwoActive u) :
    Relation T := by
  have hline := Strata.generic_relation_line_of_level p node (u 0) (u 1)
    k T.a T.b T.c T.top T.degreeSum T.ab (T.active.trans_lt T.inactive)
    ((show 1 ≤ t by decide).trans_lt T.inactive) T.level
  have hH := relation_height_le hu T
  apply Strata.polynomialRelationCertificate_of_nullity_one p (by decide)
    node (u 0) (u 1) node.injective Native.native_domain_fixed
    k k T.height (by rw [IRSProfile.card_index]; decide)
    (hH.trans (by decide)) _ hline
  rw [Sol1.C64.native_field_card]
  exact (Nat.mul_le_mul_right p (show 2 * T.height + 2 ≤ 2 * heightCap + 2 by omega)).trans_lt
    (by decide)
theorem rank_fee_exact : L + p * heightCap = rankFee := by decide
theorem anchor_fee_exact : p * heightCap + 2 * heightCap + blockLength + 2 = anchorFee := by
  decide
theorem rank_exceptions (u : Words) (hu : FrontRemainder u) (Γ : Finset K) :
    (abnormalSlopes u Γ).card ≤ rankFee := by
  classical
  have h := Strata.two_block_rank_exception_count p node (u 0) (u 1) L t (nullity u)
    (actual_stackRank u) hu.2.1 (abnormalSlopes u Γ) (fun γ hγ => by
      rw [← actual_stackRank u]
      exact (Finset.mem_filter.mp hγ).2)
  have hs : t + 1 - nullity u - L ≤ heightCap := by
    have hr := hu.1
    change 82259 - nullity u - 48814 ≤ 33443
    omega
  exact h.trans ((Nat.add_le_add_left (Nat.mul_le_mul_left p hs) L).trans_eq rank_fee_exact)
open private type_one_bad_count_of_syndromes from ProximityPrize.SubmissionLower.PortBase
theorem type_one_count (u : Words) (htype : TypeAtMostOne u)
    (Γ : Finset K) (hΓ : BadFamily u Γ) : Γ.card ≤ 1 := by
  have hk : k ≤ Fintype.card I := by rw [IRSProfile.card_index]; decide
  exact type_one_bad_count_of_syndromes node (u 0) (u 1) node.injective
    k agreement p hk (by decide) htype Γ (fun γ hγ => bad_slope u γ (hΓ γ hγ))
theorem deficient_count (u : Words) (Γ : Finset K) (hrank : firstRank u < L)
    (hΓ : BadFamily u Γ) : Γ.card ≤ 310957 := by
  have h := K1_3.deficient_hankel_count node (u 0) (u 1) node.injective
    k L t (firstRank u) (by rw [IRSProfile.card_index]; decide) hrank rfl Γ
    (fun γ hγ => bad_slope u γ (hΓ γ hγ))
  rw [IRSProfile.card_index] at h
  exact h.trans (Nat.add_le_add_left (Nat.le_of_lt_succ hrank) blockLength)
theorem principal_count (u : Words) (Γ : Finset K) (hprincipal : HomogeneousPrincipal u)
    (hΓ : BadFamily u Γ) : Γ.card ≤ 733819556938066 := by
  obtain ⟨a, g, hg, hga, ha, hkernel⟩ := hprincipal
  have hsum : a + (t - a) = t := by omega
  let φ := algebraMap K[X] Frac
  have hcertificate : Principal.PrincipalAt
      (fun b j => φ (Principal.parameterSyndromes p node (u 0) (u 1) b j)) k a (t - a) := by
    refine { generator := g, nonzero := hg, degree_bound := hga, kernel_eq := ?_ }
    intro f
    rw [hsum, Principal.recurrence_kernel_iff_matrix, Principal.recurrenceMatrix_parameter]
    change (f.natDegree ≤ t ∧ ((twoBlock u).map φ).mulVec (fun i => f.coeff i.val) = 0) ↔
      ∃ Q : Frac[X], Q.natDegree ≤ t - a ∧ f = g * Q
    constructor
    · rintro ⟨hf, hker⟩
      exact (hkernel f hf).mp hker
    · rintro ⟨Q, hQ, rfl⟩
      have hdegree : (g * Q).natDegree ≤ t :=
        natDegree_mul_le.trans ((Nat.add_le_add hga hQ).trans_eq hsum)
      exact ⟨hdegree, (hkernel _ hdegree).mpr ⟨Q, hQ, rfl⟩⟩
  have h := Principal.generic_principal_bad_count_coarse φ
    (IsFractionRing.injective K[X] Frac) p (by decide) node node.injective
    Native.native_domain_fixed (u 0) (u 1) k k a (t - a)
    (by rw [IRSProfile.card_index]; decide)
    (hsum.trans_lt (show t < k by decide)) hcertificate Γ (fun γ hγ => by
      rw [hsum]
      exact bad_slope u γ (hΓ γ hγ))
  rw [IRSProfile.card_index] at h
  exact h.trans ((Nat.mul_le_mul_left p (Nat.add_le_add_left ha blockLength)).trans (by decide))
open private constantRankCount nativeMoments independent_nativeMoments from ProximityPrize.SubmissionLower.PortBase
theorem constant_count (u : Words) (Γ : Finset K) (hu : ConstantKernel u)
    (hΓ : BadFamily u Γ) : Γ.card ≤ 175269780472147 := by
  let φ := algebraMap K[X] Frac
  have hrank : ((twoBlock u).map φ).rank = stackRank u := rfl
  have hconstant : (coefficientBlocks p node (u 0) (u 1) L t).rank = stackRank u := hu.symm
  have hcount := constantRankCount φ (IsFractionRing.injective K[X] Frac)
    p (by decide) node node.injective Native.native_domain_fixed
    (u 0) (u 1) k agreement L t (by decide) (by decide)
    (by rw [IRSProfile.card_index]; decide) (stackRank u) hrank hconstant
    Γ (fun γ hγ => bad_slope u γ (hΓ γ hγ))
  have hr : stackRank u ≤ t + 1 := by
    rw [actual_stackRank]
    exact Nat.sub_le _ _
  exact hcount.trans ((Nat.mul_le_mul_left p hr).trans_eq (by decide))
open K1_1
private theorem locator_matrix (u : Words) :
    Principal.recurrenceMatrix (nativeMoments u) k t =
      (twoBlock u).map (algebraMap K[X] Frac) :=
  Principal.recurrenceMatrix_parameter (algebraMap K[X] Frac)
    p node (u 0) (u 1) k t
private theorem locator_nullity (u : Words) :
    sliceDim (nativeMoments u) k (t + 1) = nullity u := by
  rw [sliceDim_succ (nativeMoments u) k t, locator_matrix]
  rfl
private theorem principal_of_one_active (u : Words) (a : ℕ) (ha : a ≤ t)
    (hone : sliceDim (nativeMoments u) k (a+1) = 1)
    (hnull : nullity u = (t + 1)-a) : HomogeneousPrincipal u := by
  have hpos : 0 < sliceDim (nativeMoments u) k (a+1) := by omega
  have hdim : sliceDim (nativeMoments u) k (t + 1) = (t-a)+1 := by
    rw [locator_nullity]
    omega
  obtain ⟨g, hg, hdeg, hfac⟩ := principal_of_slice (nativeMoments u) k a t
    ha (by decide) hpos hdim
  refine ⟨a, g, hg, hdeg, ha, fun P hP => ?_⟩
  rw [← locator_matrix]
  exact hfac P hP
theorem two_active_of_positive (u : Words) (hpos : 0 < nullity u)
    (hind : ¬ TypeAtMostOne u) (hnp : ¬ HomogeneousPrincipal u) : Nonempty (TwoActive u) := by
  obtain ⟨a, b, c, hab, hbc, hc, hsum, hdim⟩ := level_profile
    (nativeMoments u) k (independent_nativeMoments u hind)
  have hloc := hdim (t + 1) (by decide)
  rw [locator_nullity] at hloc
  have hthree : 3 * t < 2 * k + 2 := by decide
  have hinactive : t < c := by omega
  have ha : a ≤ t := by omega
  have hb : b ≤ t := by
    by_contra hb
    have hsmall := hdim (a+1) (by omega)
    exact hnp (principal_of_one_active u a ha (by omega) (by omega))
  refine ⟨⟨a, b, c, hab, hb, hinactive, hc, hsum, by omega, ?_⟩⟩
  exact level_of_profile _ _ _ _ _ hdim
theorem two_active_nullity {u : Words} (T : TwoActive u) : 2 ≤ nullity u := by
  have := T.ab
  have := T.active
  have := T.nullitySum
  omega
open private excludes_full_rank from ProximityPrize.SubmissionLower.RungFront
private theorem bad_excludes_full_rank (u : Words) (γ : K) (M : BadMark u γ) :
    ((twoBlock u).map (evalRingHom γ)).rank ≠ t + 1 := by
  classical
  let S := Finset.univ \ M.support
  have hs : S.card ≤ t := by
    dsimp [S]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, IRSProfile.card_index]
    have := M.agreement
    change 179886 ≤ _ at this
    change 262144 - _ ≤ 82258
    omega
  exact excludes_full_rank p node node.injective Native.native_domain_fixed (u 0) (u 1) γ k L t
    (by rw [IRSProfile.card_index]; decide) M.decoder M.degree S hs
    (fun i hi => (M.hits i (by simpa [S] using hi)).symm)
theorem full_column_count (u : Words) (Γ : Finset K) (hfirst : firstRank u = L)
    (hz : nullity u = 0) (hΓ : BadFamily u Γ) : Γ.card ≤ 71261476700499 := by
  have hr := actual_stackRank u
  rw [hz] at hr
  apply (Strata.two_block_rank_exception_count p node (u 0) (u 1) L t 0 hr hfirst Γ ?_).trans_eq
  · decide
  · intro γ hγ
    obtain ⟨M⟩ := bad_mark u Γ hΓ γ hγ
    exact bad_excludes_full_rank u γ M
theorem shortened_guards {u T R} (D : Reduction u T R) (hu : FrontRemainder u) :
    k + 3 * D.height ≤ blockLength - (fixedNodes R).card ∧
    k + D.height ≤ agreement ∧ D.height < p - 1 := by
  have hb := relation_height_le hu T
  have he := D.height_eq
  change T.height ≤ 33443 at hb
  change 131072 + 3 * D.height ≤ 262144 - _ ∧ 131072 + D.height ≤ 179886 ∧ D.height < 0x7f000000
  omega
end
end Front82200
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace Front82200
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open K1_8 (seedInclusion seedInclusion_injective extendSeed_injective extendSeedHom AmplitudeDirection)
open private transfer_at from ProximityPrize.SubmissionLower.Fast068
open private threeU_height threeV_height common_multiplier multiplier_degree_zero
  seed_scalar_coeff descend_scalar proportional_amplitudes rescale_threeU from ProximityPrize.SubmissionLower.Fast068
open P0_4 (threeU_eq relationOn_eq columnRank_eq)
open private sameDirection_eq threeV_eq from ProximityPrize.SubmissionLower.PortFrontA
private theorem reduced_scaled_relation {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (e : K[X]) :
    relationOn u (fixedNodes R) (C e * D.U) (C e * D.V) (C e * D.output) := by
  let G := liftX (locator node (fixedNodes R))
  have hG : ∀ i ∉ fixedNodes R, G.eval (C (node i)) ≠ 0 := by
    intro i hi
    change (K1.liftX (locator node (fixedNodes R))).eval (C (node i)) ≠ 0
    rw [K1_8.eval_liftX, C_ne_zero]
    exact fun hz => hi ((Principal.locator_eval_zero_iff node
      ProximityPrize.Benchmark.IRSProfile.domain.injective _ i).mp hz)
  rw [relationOn_eq]
  exact @transfer_at u K1.p k T.height R (fixedNodes R) G D.U D.V D.output
    hG D.U_factor D.V_factor D.output_factor e
private theorem seed_multiplier {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (P Q : Bivar) (hcross : sameDirection D.U D.V P Q)
    (hp : P.natDegree ≤ D.height) (hq : Q.natDegree ≤ D.height) :
    ∃ e : K[X], P = C e * D.U ∧ Q = C e * D.V := by
  have hext (F : Bivar) : (extendSeedHom F).natDegree = F.natDegree :=
    natDegree_map_eq_of_injective seedInclusion_injective F
  have hne (F : Bivar) (hF : F ≠ 0) : extendSeedHom F ≠ 0 :=
    fun hz => hF (extendSeed_injective (hz.trans (Polynomial.map_zero _).symm))
  have hxy : extendSeedHom D.U * extendSeedHom Q = extendSeedHom D.V * extendSeedHom P := by
    have h := congrArg extendSeedHom hcross
    simpa only [map_mul] using h
  have hcop : IsCoprime (extendSeedHom D.U) (extendSeedHom D.V) := D.coprime
  obtain ⟨E, heP, heQ⟩ := common_multiplier hcop hxy
  have hEd := multiplier_degree_zero (hne _ D.U_ne) (hne _ D.V_ne) heP heQ
    (by simpa only [hext] using D.max_degree)
    (by simpa only [hext] using hp) (by simpa only [hext] using hq)
  let s := E.coeff 0
  have hE : E = C s := eq_C_of_natDegree_eq_zero hEd
  rw [hE] at heP heQ
  let G := liftX (locator node (fixedNodes R))
  have hLeftU : extendSeedHom (G * P) = C s * extendSeedHom (leftU R) := by
    rw [D.U_factor]
    change extendSeedHom (G * P) = C s * extendSeedHom (G * D.U)
    rw [map_mul, map_mul, heP]
    ac_rfl
  have hLeftV : extendSeedHom (G * Q) = C s * extendSeedHom (leftV R) := by
    rw [D.V_factor]
    change extendSeedHom (G * Q) = C s * extendSeedHom (G * D.V)
    rw [map_mul, map_mul, heQ]
    ac_rfl
  let F : Fin 2 → Bivar := ![G * P, G * Q]
  let A : Fin 2 × Fin (T.height + 1) → K[X] :=
    fun j => (F j.1).coeff j.2.val
  have hA : ∀ j, seedInclusion (A j) = s * seedInclusion (R.coefficients j) := by
    rintro ⟨i, j⟩
    fin_cases i
    · have hc := seed_scalar_coeff j.val hLeftU
      rw [leftU, Principal.assemble_coeff] at hc
      exact hc
    · have hc := seed_scalar_coeff j.val hLeftV
      rw [leftV, Principal.assemble_coeff] at hc
      exact hc
  obtain ⟨e, he⟩ := descend_scalar R.coefficients A R.primitive s hA
  have hmapC : extendSeedHom (C e) = C s := by
    change (C e).map seedInclusion = C s
    rw [Polynomial.map_C, he]
  refine ⟨e, extendSeed_injective ?_, extendSeed_injective ?_⟩
  · change extendSeedHom P = extendSeedHom (C e * D.U)
    rw [map_mul, hmapC, heP]
  · change extendSeedHom Q = extendSeedHom (C e * D.V)
    rw [map_mul, hmapC, heQ]
private theorem canonical_output {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (P Q : Bivar) (hcross : sameDirection D.U D.V P Q)
    (hp : P.natDegree ≤ D.height) (hq : Q.natDegree ≤ D.height) :
    ∃ W : Bivar, W.degree < (k + D.height : ℕ) ∧ relationOn u (fixedNodes R) P Q W := by
  obtain ⟨e, rfl, rfl⟩ := seed_multiplier D P Q hcross hp hq
  refine ⟨C e * D.output, ?_, ?_⟩
  · have hdeg : (C e * D.output).degree ≤ D.output.degree := by
      simpa only [smul_eq_C_mul] using degree_smul_le e D.output
    exact hdeg.trans_lt D.output_degree
  · exact reduced_scaled_relation D e
theorem rank_three_branch {u : Words} {T : TwoActive u} {R : Relation T}
    (D : Reduction u T R) (hr : columnRank D.U D.V = 3) (S : AmplitudeDirection D.U D.V)
    (ha : S.a.natDegree + amplitudeDegree (S.β 0) (S.β 1) ≤ D.height)
    (hb : S.b.natDegree + amplitudeDegree (S.α 0) (S.α 1) ≤ D.height) :
    ∃ B : RankThree u T R D, Nonparallel B ∨ Parallel B := by
  have hdir : sameDirection D.U D.V (threeU S.a S.β) (threeV S.b S.α) := by
    rw [threeU_eq, threeV_eq, sameDirection_eq]
    exact S.direction
  have hUdeg : (threeU S.a S.β).natDegree ≤ D.height := by
    rw [threeU_eq]
    exact (threeU_height _ _).trans ha
  have hVdeg : (threeV S.b S.α).natDegree ≤ D.height := by
    rw [threeV_eq]
    exact (threeV_height _ _).trans hb
  obtain ⟨W, hW, hnodes⟩ := canonical_output D _ _ hdir hUdeg hVdeg
  by_cases hd : S.α 0 * S.β 1 - S.α 1 * S.β 0 = 0
  · obtain ⟨t, ht, htβ⟩ := proportional_amplitudes S.α_primitive S.β_primitive (sub_eq_zero.mp hd)
    have htσ : twist t ≠ 0 := fun hz => ht (twist.injective (hz.trans (map_zero twist).symm))
    let a := S.a * C (twist t)
    have heq (i : Fin 2) : (S.β i).map twist = C (twist t) * (S.α i).map twist := by
      rw [htβ i, Polynomial.map_mul, Polynomial.map_C]
    have hU : threeU a S.α = threeU S.a S.β :=
      (threeU_eq _ _).trans ((rescale_threeU S.a S.α S.β (twist t) heq).trans (threeU_eq _ _).symm)
    have hdeg (i : Fin 2) : (S.β i).natDegree = (S.α i).natDegree := by
      rw [htβ i, natDegree_C_mul ht]
    have ha' : a.natDegree + amplitudeDegree (S.α 0) (S.α 1) ≤ D.height := by
      simpa only [a, natDegree_mul_C htσ, amplitudeDegree, hdeg] using ha
    have hdir' : sameDirection D.U D.V (threeU a S.α) (threeV S.b S.α) := by
      rw [hU]
      exact hdir
    have hn : relationOn u (fixedNodes R) (threeU a S.α) (threeV S.b S.α) W := by
      rw [hU]
      exact hnodes
    exact ⟨⟨hr, S.α, S.α, a, S.b, mul_ne_zero S.a_ne (C_ne_zero.mpr htσ), S.b_ne,
      S.α_primitive, S.α_primitive, ha', hb, hdir', W, hW, hn⟩, Or.inr rfl⟩
  · exact ⟨⟨hr, S.α, S.β, S.a, S.b, S.a_ne, S.b_ne,
      S.α_primitive, S.β_primitive, ha, hb, hdir, W, hW, hnodes⟩, Or.inl hd⟩
theorem classify_fixed {u : Words} (hfront : FrontRemainder u) (T : TwoActive u)
    (R : Relation T) (hmove : ¬ MovingGCD R) (hinvalid : ¬ InvalidLeft R)
    (hsat : NormalSaturation R) (hw : ∃ γ, Normal u γ ∧ Nonempty (BadMark u γ)) :
    ∃ D : Reduction u T R, columnRank D.U D.V = 4 ∨
      ∃ B : RankThree u T R D, Nonparallel B ∨ Parallel B := by
  have hu : leftU R ≠ 0 := by
    obtain ⟨γ, hγ, ⟨M⟩⟩ := hw
    intro hz
    exact (hsat γ hγ M).U_ne (by rw [atSlope, hz, Polynomial.map_zero])
  obtain ⟨D⟩ := puncture R hsat hw (fixed_gcd R hu hmove hinvalid)
  refine ⟨D, ?_⟩
  rcases K1_8.rank_cases D.U D.V D.U_ne D.V_ne with hfour | hthree
  · exact Or.inl ((columnRank_eq _ _).trans hfour)
  · obtain ⟨S⟩ := K1_8_1.proof D.U D.V D.U_ne D.V_ne hthree
    have hsmall := (shortened_guards D hfront).2.2
    obtain ⟨ha, hb⟩ := K1_8_2.proof D.U D.V D.height D.U_ne D.V_ne D.coprime D.max_degree hsmall S
    exact Or.inr (rank_three_branch D ((columnRank_eq _ _).trans hthree) S ha hb)
end
end Front82200
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace Front82200
open Polynomial Matrix FrobeniusLocator ProximityPrize.Benchmark
open private certificate_shifts_annihilate_generic from ProximityPrize.SubmissionLower.Fast050
open private lift_common_divisor specialize_factor eval_atSlope root_outside_of_dvd_locator
  common_node_count from ProximityPrize.SubmissionLower.Fast051
private theorem certificate_shifts_annihilate {u : Words} {T : TwoActive u} (R : Relation T)
    (s : ℕ) (hL : T.height + s = L) :
    (K1_6.shifts (fun b => Principal.assemble (fun j => R.coefficients (b, j))) L s).transpose *
      twoBlock u = 0 := by
  have hsize : k + (48813 + 1) + t ≤ Fintype.card I := by
    rw [IRSProfile.card_index]
    decide
  exact certificate_shifts_annihilate_generic p node (u 0) (u 1) IRSProfile.domain.injective
    Native.native_domain_fixed (algebraMap K[X] Frac) (IsFractionRing.injective K[X] Frac)
    k T.height 48813 t s hL hsize R _ (fun _ => rfl)
private theorem moving_has_new_node {u : Words} {T : TwoActive u} (R : Relation T)
    (hMoving : MovingGCD R) {γ : K} {M : BadMark u γ} (hSat : SaturatedAt R M) :
    ∃ i ∉ fixedNodes R,
      (atSlope (leftU R) γ).eval (node i) = 0 ∧ (atSlope (leftV R) γ).eval (node i) = 0 := by
  classical
  obtain ⟨G, hG, hGU, hGV, hg⟩ := hMoving.2
  obtain ⟨D, hD, hd, hDU, hDV⟩ := lift_common_divisor hG hGU hGV
  obtain ⟨A, hA⟩ := hDU
  obtain ⟨B, hB⟩ := hDV
  obtain ⟨hAU, hAUdeg⟩ := specialize_factor hD hA hSat.U_ne
  obtain ⟨hBV, hBVdeg⟩ := specialize_factor hD hB hSat.V_ne
  change atSlope (leftU R) γ = atSlope D γ * atSlope A γ at hAU
  change atSlope (leftV R) γ = atSlope D γ * atSlope B γ at hBV
  change (atSlope (leftU R) γ).natDegree + D.natDegree ≤
    (leftU R).natDegree + (atSlope D γ).natDegree at hAUdeg
  change (atSlope (leftV R) γ).natDegree + D.natDegree ≤
    (leftV R).natDegree + (atSlope D γ).natDegree at hBVdeg
  have hdeg : D.natDegree ≤ (atSlope D γ).natDegree := by
    have hU := R.x_degree 0
    have hV := R.x_degree 1
    change (leftU R).natDegree ≤ T.height at hU
    change (leftV R).natDegree ≤ T.height at hV
    have hMax := hSat.degree_eq
    rcases le_total (atSlope (leftU R) γ).natDegree (atSlope (leftV R) γ).natDegree with h | h
    · rw [max_eq_right h] at hMax
      omega
    · rw [max_eq_left h] at hMax
      omega
  obtain ⟨errors, _, hGCD⟩ := hSat.gcd_errors
  have hDvd := hGCD.2.2.2 (atSlope D γ) ⟨atSlope A γ, hAU⟩ ⟨atSlope B γ, hBV⟩
  have hCard : (fixedNodes R).card < (atSlope D γ).natDegree := by omega
  obtain ⟨i, hiFixed, hi⟩ := root_outside_of_dvd_locator (F := K) (ι := I)
    node IRSProfile.domain.injective errors (fixedNodes R) (atSlope D γ) hDvd hCard
  exact ⟨i, hiFixed, by rw [hAU, eval_mul, hi, zero_mul], by rw [hBV, eval_mul, hi, zero_mul]⟩
open private count_bound from ProximityPrize.SubmissionLower.RungFront
private theorem normal_growth_count {u : Words} {T : TwoActive u} (R : Relation T)
    (hHeight : ∀ i, (R.coefficients i).natDegree ≤ 6766528128)
    (hMoving : MovingGCD R) (hSat : NormalSaturation R) (Γ : Finset K)
    (hBad : BadFamily u Γ) (hNormal : ∀ γ ∈ Γ, Normal u γ) :
    Γ.card ≤ 1773804749586432 := by
  classical
  let U (i : I) := (leftU R).eval (C (node i))
  let V (i : I) := (leftV R).eval (C (node i))
  have hU (i) : (U i).natDegree ≤ 6766528128 := by
    dsimp only [U, leftU]
    rw [Strata.assemble_nodePolynomial]
    exact Principal.nodePolynomial_natDegree_le _ (fun j => hHeight (0, j)) _
  have hV (i) : (V i).natDegree ≤ 6766528128 := by
    dsimp only [V, leftV]
    rw [Strata.assemble_nodePolynomial]
    exact Principal.nodePolynomial_natDegree_le _ (fun j => hHeight (1, j)) _
  have hNew (γ : K) (hγ : γ ∈ Γ) :
      ∃ i, ¬ (U i = 0 ∧ V i = 0) ∧ (U i).eval γ = 0 ∧ (V i).eval γ = 0 := by
    refine (Front82200.bad_mark u Γ hBad γ hγ).elim (fun M => ?_)
    obtain ⟨i, hi, hu, hv⟩ := moving_has_new_node R hMoving (hSat γ (hNormal γ hγ) M)
    have hNZ : ¬ (U i = 0 ∧ V i = 0) := by
      simpa only [fixedNodes, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact ⟨i, hNZ, (eval_atSlope (leftU R) γ (node i)).symm.trans hu,
      (eval_atSlope (leftV R) γ (node i)).symm.trans hv⟩
  exact count_bound (c := Γ.card) (n := Fintype.card I) (n' := 262144)
    (H := 6766528128) (b := 1773804749586432) IRSProfile.card_index
    (common_node_count U V 6766528128 Γ hU hV hNew) rfl
theorem moving_count (u : Words) (front : FrontRemainder u) (T : TwoActive u)
    (R : Relation T) (moving : MovingGCD R) (saturated : NormalSaturation R)
    (Γ : Finset K) (bad : BadFamily u Γ) (normal : ∀ γ ∈ Γ, Normal u γ) :
    Γ.card ≤ 1773804749586432 := by
  let P (b : Fin 2) : Bivar := Principal.assemble (fun j => R.coefficients (b, j))
  let s := L - T.height
  have hP : ∀ b, (P b).natDegree ≤ T.height := R.x_degree
  have hBalance := relation_height_balance T
  have hHeight := relation_height_le front T
  change T.height ≤ 33443 at hHeight
  have hsDef : s = 48814 - T.height := rfl
  have hSum : T.height + s = L := by change T.height + s = 48814; omega
  have hs : 15371 ≤ s := by omega
  have hRank : GenericLayer.genericRank (twoBlock u) + s = 2 * L := by
    change stackRank u + s = _
    rw [actual_stackRank u]
    change 48814 + T.height + nullity u = 82259 at hBalance
    change 82259 - nullity u + s = 97628
    omega
  have hCoordinates : K1_6.pairCoordinates P T.height = R.coefficients := by
    funext i
    exact Principal.assemble_coeff (fun j => R.coefficients (i.1, j)) i.2
  have hPrim : PrimitiveVector.IsPrimitive (K1_6.pairCoordinates P T.height) := by
    rw [hCoordinates]
    exact R.primitive
  have hKernel := certificate_shifts_annihilate R s hSum
  obtain ⟨hMinors, H, hH, rows, hRows⟩ :=
    K1_6_1.proof K T.height L s P hSum (by omega) hP hPrim
  have hBound := K1_6_2.proof K L (t + 1) s p (twoBlock u) (K1_6.shifts P L s)
    (by decide) hRank hKernel (stacked_entry_natDegree p node (u 0) (u 1) L t) hMinors rows
  rw [hRows] at hBound
  have hProduct : 15371 * H ≤ s * H := Nat.mul_le_mul_right H hs
  have hCeiling : L * (p + 1) = 104008303869276 := rfl
  rw [hCeiling] at hBound
  have hCap : H ≤ 6766528128 := by omega
  apply normal_growth_count R _ moving saturated Γ bad normal
  intro i
  rw [← hCoordinates]
  exact (hH i.1 i.2.val).trans hCap
end Front82200
end
set_option backward.isDefEq.respectTransparency false
namespace Front82200
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
def c1 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T), NormalSaturation R
def c2 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D),
    NormalSaturation R → Parallel B → ¬ UnitNorm B →
    ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) → Γ.card ≤ t + 1
def c3 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D),
    NormalSaturation R → Nonparallel B →
    ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) → Γ.card ≤ 250000000000000000
def c4 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T) (D : Reduction u T R),
    NormalSaturation R → columnRank D.U D.V = 4 →
    ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) → Γ.card ≤ 250000000000000000
def c5 : Prop :=
  ∀ u, FrontRemainder u → ∀ (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D),
    NormalSaturation R → Parallel B → UnitNorm B →
    ∀ Γ, BadFamily u Γ → (∀ γ ∈ Γ, Normal u γ) →
    Γ.card ≤ anchorFee ∨
      ∃ book : Finset K, book ⊆ Γ ∧ book.card ≤ anchorFee ∧
        ∃ M : AnchorModel u (fixedNodes R), Nonempty (AnchoredFamily M (Γ \ book))
def c6 : Prop :=
  ∀ u deleted (M : AnchorModel u deleted) Γ, AnchoredFamily M Γ →
    1 ≤ M.overhead → M.overhead ≤ lowCutoff →
    Γ.card ≤ lowCap
def c7 : Prop :=
  ∀ u deleted (M : AnchorModel u deleted) Γ, AnchoredFamily M Γ →
    lowCutoff + 1 ≤ M.overhead → M.overhead ≤ (heightCap : ℤ) →
    Γ.card ≤ highCap
theorem mem_normalSlopes {u : Words} {Γ : Finset K} {γ : K} :
    γ ∈ normalSlopes u Γ ↔ γ ∈ Γ ∧ Normal u γ := by
  classical exact Finset.mem_filter
theorem normal_badFamily {u : Words} {Γ : Finset K} (hΓ : BadFamily u Γ) :
    BadFamily u (normalSlopes u Γ) :=
  fun γ hγ => hΓ γ (mem_normalSlopes.mp hγ).1
theorem normal_on_normalSlopes {u : Words} {Γ : Finset K} :
    ∀ γ ∈ normalSlopes u Γ, Normal u γ :=
  fun _ hγ => (mem_normalSlopes.mp hγ).2
theorem add_rank_exceptions (u : Words) (hu : FrontRemainder u) (Γ : Finset K)
    (b : ℕ) (hb : (normalSlopes u Γ).card ≤ b) :
    Γ.card ≤ b + rankFee := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (s := Γ) (p := Normal u)]
  exact Nat.add_le_add hb (rank_exceptions u hu Γ)
theorem low_with_reserve : lowCap + anchorFee + rankFee = 268014976625055642 := by decide
theorem nonpositive_with_reserve : listCap + anchorFee + rankFee = 7108265917194929 := by decide
private theorem coherent_count (h5 : c5) (h6 : c6) (h7 : c7) (hlist : CJ0.ScalarList agreement listCap)
    (u : Words) (hu : FrontRemainder u) (T : TwoActive u) (R : Relation T)
    (D : Reduction u T R) (B : RankThree u T R D) (hsat : NormalSaturation R)
    (hp : Parallel B) (hn : UnitNorm B) (Γ : Finset K) (hΓ : BadFamily u Γ) :
    Γ.card ≤ scalarCap := by
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
      have hh := M.height_bound
      change (M.E.natDegree : ℤ) - M.factor.natDegree - amplitudeDegree M.A₀ M.A₁ ≤ heightCap
      omega
    by_cases hw₀ : M.overhead ≤ 0
    · exact (hreserve _ (P1.anchored_list_count hlist M _ F hw₀)).trans
        (nonpositive_with_reserve.le.trans (by decide))
    by_cases hwL : M.overhead ≤ lowCutoff
    · exact (hreserve _ (h6 u _ M _ F (by omega) hwL)).trans
        (low_with_reserve.le.trans (by decide))
    · exact (hreserve _ (h7 u _ M _ F (by omega) hwmax)).trans (by decide)
private theorem scalar_count (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4)
    (h5 : c5) (h6 : c6) (h7 : c7) (hlist : CJ0.ScalarList agreement listCap)
    (u : Words) (Γ : Finset K) (hΓ : BadFamily u Γ) : Γ.card ≤ scalarCap := by
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
  have hnone (he : N = ∅) : Γ.card ≤ scalarCap :=
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
      · exact coherent_count h5 h6 h7 hlist u hu T R D B hsat hpar hn Γ hΓ
      · exact (add_rank_exceptions u hu Γ _ (h2 u hu T R D B hsat hpar hn N hN hnormal)).trans
          (by decide)
  · exact hnone (Finset.not_nonempty_iff_eq_empty.mp hne)

/-- The seven rank and height cases suffice for the protocol at 82,200 errors. -/
theorem of_children (hlist : CJ0.ScalarList agreement listCap) (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) (h6 : c6) (h7 : c7) :
    ProtocolClaim 6954 336932863 1073741824 :=
  ProtocolTarget82200.protocol_claim_of_scalar_cap hlist
    (scalar_count h1 h2 h3 h4 h5 h6 h7 hlist)
end
end Front82200