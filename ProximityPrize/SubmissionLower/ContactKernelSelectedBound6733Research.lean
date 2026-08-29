import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAlignmentBridge
import ProximityPrize.SubmissionLower.ContactKernelSelectedInterpolation6733Research
import ProximityPrize.SubmissionLower.ContactKernelResidualCells6733Research
import ProximityPrize.SubmissionLower.ContactKernelFixedSelected6733Research
import ProximityPrize.SubmissionLower.ContactStackedSeedPartition6670Research
namespace ProximityPrize.SubmissionLower.ContactKernelSelectedBound6733Research
open ProximityPrize.Benchmark
open ContactAlignmentBridge ContactInterpolation ContactTranslation
open ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactFactorCaps ContactGCDCumulativeFlagsResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactRecursiveGCDResearch ContactStackedGCDCover6670Research
open ContactStackedSeedPartition6670Research
open ContactKernelSelectedInterpolation6733Research
open ContactKernelResidualCells6733Research
open ContactKernelFixedSelected6733Research
open ContactKernelArithmetic6733Research
open ContactPost6464MinkowskiRecurrenceResearch
open ContactRecursiveResidualStages6656Research
open ContactTightSingularLedgerResearch
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
local instance : DecidableEq IRSProfile.Field := Classical.decEq _
local instance : DecidableEq IRSProfile.Index := Classical.decEq _
abbrev Poly := MvPolynomial (Fin 4) IRSProfile.Field
local instance : GCDMonoid Poly :=
  UniqueFactorizationMonoid.toGCDMonoid Poly
local instance : CharP IRSProfile.Field 2130706433 := by
  simpa [ContactParameters6600Research.prime] using
    ContactFrozenAlignment6600Research.challenge_field_characteristic6600
private theorem selected_recursive_cover
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (seeds : Finset IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (S : SelectedInterpolants (U 0) (U 1))
    (hdegree : ∀ γ ∈ seeds,(selected γ).natDegree ≤ 131071)
    (hcard : ∀ γ ∈ seeds,182052 ≤ (A γ).card)
    (hvalues : ∀ γ ∈ seeds,∀ i ∈ A γ,
      (selected γ).eval (IRSProfile.domain i) = U 0 i + γ * U 1 i) :
    ∀ γ ∈ seeds,
      RecursiveSpecializationBranch (selected γ) γ S.QA S.QB S.QC := by
  intro γ hγ
  obtain ⟨hA,hB,hC⟩ := S.universal_vanishing γ (selected γ) (A γ)
    (hdegree γ hγ) (hcard γ hγ) (hvalues γ hγ)
  exact recursive_branch_of_three_vanishings (selected γ) γ S.QA S.QB S.QC
    hA hB hC
private theorem full_domain_agreement
    (U : Fin 2 → IRSProfile.Index → IRSProfile.Field)
    (seeds : Finset IRSProfile.Field)
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (hcard : ∀ γ ∈ seeds,182052 ≤ (A γ).card)
    (hvalues : ∀ γ ∈ seeds,∀ i ∈ A γ,
      (selected γ).eval (IRSProfile.domain i) = U 0 i + γ * U 1 i) :
    ∀ γ ∈ seeds,182052 ≤
      ((Finset.univ : Finset IRSProfile.Index).filter (fun i ↦
        (selected γ).eval (IRSProfile.domain i) = U 0 i + γ * U 1 i)).card := by
  intro γ hγ
  apply (hcard γ hγ).trans
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvalues γ hγ i hi⟩
private theorem weighted_quotient_add_factor_le
    (weights : Fin 4 → ℕ) (F H G Q : Poly)
    (hF : F ≠ 0) (hH : H ≠ 0) (hG : G ≠ 0) (hQ : Q ≠ 0)
    (heq : F = H * Q) (hGH : G ∣ H) :
    wt weights Q + wt weights G ≤ wt weights F := by
  have hGleH := weightedTotalDegree_le_of_dvd weights G H hGH hH
  have hmul := weightedTotalDegree_mul weights H Q hH hQ
  rw [← heq] at hmul
  simp only [wt] at hGleH hmul ⊢
  omega
private theorem ys_cap_of_flag
    (Q : Poly) (D L s yCap : ℕ) (hD : 0 < D)
    (hbox : Q ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field D 131071 L s)
    (hnum : D - 1 + s < 131071 * (yCap + 1)) :
    wt residualYSWeights Q ≤ yCap := by
  have hc := (ContactKernelCommonGCDResearch.mem_flagGlobalCoefficientBox_iff
    Q D 131071 L s hD).mp hbox
  have hrel := ContactKernelCommonGCDResearch.residualYS_mul_le_contact_add_slope
    Q 131071 (by decide)
  simp only [wt] at hc hrel ⊢
  omega
private theorem cap_nested (Q : Poly) :
    (ContactKernelFixedSelected6733Research.capOf Q).middle ≤
        (ContactKernelFixedSelected6733Research.capOf Q).total ∧
      (ContactKernelFixedSelected6733Research.capOf Q).inner ≤
        (ContactKernelFixedSelected6733Research.capOf Q).middle := by
  have h := residual_weight_nested Q
  exact ⟨h.2,h.1⟩
private def rawComplement (p g : Cap) (middle : ℕ) : Cap :=
  ⟨p.total-g.total,middle,p.inner-g.inner⟩
private def paddedLeftComplement (p g : Cap) (middle : ℕ) : Cap :=
  ⟨p.total-g.total,middle,max 1 (p.inner-g.inner)⟩
private def stage1Safe (g : Cap) : ℕ :=
  residualPadded (paddedLeftComplement parentB g 112)
      (rawComplement parentA g 56) 112+
    singularPadded (paddedLeftComplement parentB g 112) (81*agreements)
private def stage2Safe (g : Cap) : ℕ :=
  residualPadded (paddedLeftComplement hmax g 56)
      (rawComplement parentC g 59) 56+
    singularPadded (paddedLeftComplement hmax g 56) (41*agreements)
private def coupledSafe (g : Cap) : ℕ :=
  stage1Safe g+stage2Safe g+fixed g+singularPadded g (41*agreements)
private theorem stagesSafe_antitone {g h : Cap} (hgh : CapLE g h) :
    stage1Safe h+stage2Safe h ≤ stage1Safe g+stage2Safe g := by
  rcases hgh with ⟨hL,_hY,hS⟩
  have haL := Nat.sub_le_sub_left hL parentA.total
  have haS := Nat.sub_le_sub_left hS parentA.inner
  have hbL := Nat.sub_le_sub_left hL parentB.total
  have hbS := Nat.sub_le_sub_left hS parentB.inner
  have hbSp := max_le_max (le_refl 1) hbS
  have hhL := Nat.sub_le_sub_left hL hmax.total
  have hhS := Nat.sub_le_sub_left hS hmax.inner
  have hhSp := max_le_max (le_refl 1) hhS
  have hcL := Nat.sub_le_sub_left hL parentC.total
  have hcS := Nat.sub_le_sub_left hS parentC.inner
  exact Nat.add_le_add
    (Nat.add_le_add
      (residualPadded_mono hbL hbSp haL (le_refl 56) haS)
      (singularPadded_mono hbL (le_refl 112) hbSp))
    (Nat.add_le_add
      (residualPadded_mono hhL hhSp hcL (le_refl 59) hcS)
      (singularPadded_mono hhL (le_refl 56) hhSp))
private theorem stage1Safe_antitone {g h : Cap} (hgh : CapLE g h) :
    stage1Safe h ≤ stage1Safe g := by
  rcases hgh with ⟨hL,_hY,hS⟩
  have haL := Nat.sub_le_sub_left hL parentA.total
  have haS := Nat.sub_le_sub_left hS parentA.inner
  have hbL := Nat.sub_le_sub_left hL parentB.total
  have hbS := Nat.sub_le_sub_left hS parentB.inner
  have hbSp := max_le_max (le_refl 1) hbS
  exact Nat.add_le_add
    (residualPadded_mono hbL hbSp haL (le_refl 56) haS)
    (singularPadded_mono hbL (le_refl 112) hbSp)
private theorem stage2Safe_of_caps {g h : Cap}
    (hL : h.total ≤ hmax.total) (hS : h.inner ≤ hmax.inner) :
    residualPadded (paddedLeftComplement h g 56)
        (rawComplement parentC g 59) 56+
      singularPadded (paddedLeftComplement h g 56) (41*agreements) ≤
      stage2Safe g := by
  have hsubL := Nat.sub_le_sub_right hL g.total
  have hsubS := Nat.sub_le_sub_right hS g.inner
  have hsubSp := max_le_max (le_refl 1) hsubS
  exact Nat.add_le_add
    (residualPadded_mono hsubL hsubSp (le_refl _)
      (le_refl 59) (le_refl _))
    (singularPadded_mono hsubL (le_refl 56) hsubSp)
private theorem coupledSafe_box {lo g hi : Cap}
    (hlo : CapLE lo g) (hhi : CapLE g hi) :
    coupledSafe g ≤ stage1Safe lo+stage2Safe lo+fixed hi+
      singularPadded hi (41*agreements) := by
  rcases hhi with ⟨hL,hY,hS⟩
  have hst := stagesSafe_antitone hlo
  have hf := fixed_mono hL hY hS
  have hs := singularPadded_mono hL hY hS (D := 41*agreements)
  unfold coupledSafe
  omega
private theorem stagesSafe_le_max (g : Cap) :
    stage1Safe g+stage2Safe g ≤ 7486606599893923 := by
  calc
    stage1Safe g+stage2Safe g ≤
        (residualPadded (paddedLeftComplement parentB ⟨0,0,0⟩ 112)
            (rawComplement parentA ⟨0,0,0⟩ 56) 112+
          singularPadded (paddedLeftComplement parentB ⟨0,0,0⟩ 112) (81*agreements))+
        (residualPadded (paddedLeftComplement hmax ⟨0,0,0⟩ 56)
            (rawComplement parentC ⟨0,0,0⟩ 59) 56+
          singularPadded (paddedLeftComplement hmax ⟨0,0,0⟩ 56) (41*agreements)) := by
      exact Nat.add_le_add
        (Nat.add_le_add
          (residualPadded_mono (Nat.sub_le _ _)
            (max_le_max (le_refl 1) (Nat.sub_le _ _))
            (Nat.sub_le _ _) (le_refl 56) (Nat.sub_le _ _))
          (singularPadded_mono (Nat.sub_le _ _) (le_refl 112)
            (max_le_max (le_refl 1) (Nat.sub_le _ _))))
        (Nat.add_le_add
          (residualPadded_mono (Nat.sub_le _ _)
            (max_le_max (le_refl 1) (Nat.sub_le _ _))
            (Nat.sub_le _ _) (le_refl 59) (Nat.sub_le _ _))
          (singularPadded_mono (Nat.sub_le _ _) (le_refl 56)
            (max_le_max (le_refl 1) (Nat.sub_le _ _))))
    _ = 7486606599893923 := by
      norm_num [rawComplement,paddedLeftComplement,residualPadded,
        singularPadded,ensurePositiveSlope,
        singular,parentA,parentB,parentC,hmax,agreements,
        ContactKernelArithmetic6733Research.errors,
        ContactKernelArithmetic6733Research.gap,u,
        ContactKernelArithmetic6733Research.w,
        ContactKernelArithmetic6733Research.n]
private theorem safe_case_s10 {g : Cap}
    (hL : g.total ≤ 1240) (hy : g.middle ≤ 54) (hs : g.inner ≤ 10) :
    coupledSafe g+1240 ≤ 270601956763892927 := by
  have hf := fixed_mono (p := g) (q := ⟨1240,54,10⟩) hL hy hs
  have hsing := singularPadded_mono (p := g) (q := ⟨1240,54,10⟩)
    hL hy hs (D := 41*agreements)
  have hstage := stagesSafe_le_max g
  calc
    coupledSafe g+1240 ≤
        (7486606599893923+fixed ⟨1240,54,10⟩+
          singularPadded ⟨1240,54,10⟩ (41*agreements))+1240 := by
      unfold coupledSafe
      omega
    _ = 270601956763892927 := by
      norm_num [fixed,singularPadded,ensurePositiveSlope,singular,
        agreements,ContactKernelArithmetic6733Research.errors,
        ContactKernelArithmetic6733Research.gap,u,
        ContactKernelArithmetic6733Research.w,
        ContactKernelArithmetic6733Research.n]
private theorem safe_case_y53 {g : Cap}
    (hL : g.total ≤ 1240) (hy : g.middle ≤ 53)
    (hs11 : g.inner = 11)
    (hn1 : g.middle ≤ g.total) (hn2 : g.inner ≤ g.middle) :
    coupledSafe g ≤ 271963885755256005 := by
  have hlo : CapLE ⟨11,11,11⟩ g := by simp only [CapLE]; omega
  have hhi : CapLE g ⟨1240,53,11⟩ := by simp only [CapLE]; omega
  have h := coupledSafe_box hlo hhi
  norm_num [stage1Safe,stage2Safe,rawComplement,paddedLeftComplement,
    residualPadded,parentA,parentB,
    parentC,hmax,fixed,singularPadded,
    ensurePositiveSlope,singular,agreements,
    ContactKernelArithmetic6733Research.errors,
    ContactKernelArithmetic6733Research.gap,u,
    ContactKernelArithmetic6733Research.w,
    ContactKernelArithmetic6733Research.n] at h ⊢
  exact h
private theorem safe_case_y54_low {g : Cap}
    (hloL : 54 ≤ g.total) (hhiL : g.total ≤ 1206)
    (hy54 : g.middle = 54) (hs11 : g.inner = 11) :
    coupledSafe g+1186 ≤ 271285853370013836 := by
  have hlo : CapLE ⟨54,54,11⟩ g := by simp only [CapLE]; omega
  have hhi : CapLE g ⟨1206,54,11⟩ := by simp only [CapLE]; omega
  have h := coupledSafe_box hlo hhi
  norm_num [stage1Safe,stage2Safe,rawComplement,paddedLeftComplement,
    residualPadded,parentA,parentB,
    parentC,hmax,fixed,singularPadded,
    ensurePositiveSlope,singular,agreements,
    ContactKernelArithmetic6733Research.errors,
    ContactKernelArithmetic6733Research.gap,u,
    ContactKernelArithmetic6733Research.w,
    ContactKernelArithmetic6733Research.n] at h ⊢
  omega
private theorem safe_case_y54_high {g : Cap}
    (hloL : 1207 ≤ g.total) (hhiL : g.total ≤ 1240)
    (hy54 : g.middle = 54) (hs11 : g.inner = 11) :
    coupledSafe g+33 ≤ 273551344698042877 := by
  have hlo : CapLE ⟨1207,54,11⟩ g := by simp only [CapLE]; omega
  have hhi : CapLE g ⟨1240,54,11⟩ := by simp only [CapLE]; omega
  have h := coupledSafe_box hlo hhi
  norm_num [stage1Safe,stage2Safe,rawComplement,paddedLeftComplement,
    residualPadded,parentA,parentB,
    parentC,hmax,fixed,singularPadded,
    ensurePositiveSlope,singular,agreements,
    ContactKernelArithmetic6733Research.errors,
    ContactKernelArithmetic6733Research.gap,u,
    ContactKernelArithmetic6733Research.w,
    ContactKernelArithmetic6733Research.n] at h ⊢
  omega
private theorem coupledSafe_lt_budget (g : Cap)
    (hL : g.total ≤ 1240) (hy : g.middle ≤ 54) (hs : g.inner ≤ 11)
    (hn1 : g.middle ≤ g.total) (hn2 : g.inner ≤ g.middle) :
    coupledSafe g < budget := by
  by_cases hs10 : g.inner ≤ 10
  · have h := safe_case_s10 hL hy hs10
    exact (Nat.le_add_right _ 1240).trans_lt
      (h.trans_lt (by norm_num [budget,ContactKernelArithmetic6733Research.prime]))
  have hs11 : g.inner = 11 := by omega
  by_cases hy53 : g.middle ≤ 53
  · exact (safe_case_y53 hL hy53 hs11 hn1 hn2).trans_lt
      (by norm_num [budget,ContactKernelArithmetic6733Research.prime])
  have hy54 : g.middle = 54 := by omega
  by_cases hL1206 : g.total ≤ 1206
  · have h := safe_case_y54_low (by omega) hL1206 hy54 hs11
    exact (Nat.le_add_right _ 1186).trans_lt
      (h.trans_lt (by norm_num [budget,ContactKernelArithmetic6733Research.prime]))
  · have h := safe_case_y54_high (by omega) hL hy54 hs11
    exact (Nat.le_add_right _ 33).trans_lt
      (h.trans_lt (by norm_num [budget,ContactKernelArithmetic6733Research.prime]))
private theorem firstStageGates_of_caps
    (rightY hTotal hSlope tTotal tSlope : ℕ)
    (rightY_le : rightY ≤ 56) (hTotal_ne : hTotal ≠ 0)
    (hTotal_le : hTotal ≤ 1242) (hSlope_le : hSlope ≤ 25)
    (tTotal_le : tTotal ≤ 1003041) (tSlope_le : tSlope ≤ 12) :
    StageGates
      (residualParameters 112 rightY hTotal hSlope tTotal tSlope)
      (singularParameters 14746212 hTotal hSlope) := by
  have hpad_le : paddedSlope hSlope ≤ 25 := by simp [paddedSlope]; omega
  have hkappa_one : 1 ≤ 2*paddedSlope hSlope-1 := by simp [paddedSlope]; omega
  have hkappa_le : 2*paddedSlope hSlope-1 ≤ 49 := by omega
  have hweighted : 131071 < (2*paddedSlope hSlope-1)*14746212 := by
    have hmul := Nat.mul_le_mul_right 14746212 hkappa_one
    norm_num at hmul ⊢
    omega
  have halg_pos : 1 ≤ (2*paddedSlope hSlope-1)*hTotal :=
    Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hTotal_ne)
  have halg_le : (2*paddedSlope hSlope-1)*hTotal ≤ 49*1242 :=
    Nat.mul_le_mul hkappa_le hTotal_le
  have himp_le :
      ((2*paddedSlope hSlope-1)*14746212-1)/131071 ≤ 5512 := by
    calc
      _ ≤ (49*14746212)/131071 := by
        apply Nat.div_le_div_right
        exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_right 14746212 hkappa_le)
      _ = 5512 := by norm_num
  have hsing_mixed :
      2*(((2*paddedSlope hSlope-1)*14746212-1)/131071)*
        ((2*paddedSlope hSlope-1)*hTotal) < 2130706433 := by
    have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left 2 himp_le) halg_le
    norm_num at hmul ⊢
    omega
  have hmixY1 : paddedSlope hSlope*tTotal ≤ 25*1003041 :=
    Nat.mul_le_mul hpad_le tTotal_le
  have hmixY2 : hTotal*tSlope ≤ 1242*12 :=
    Nat.mul_le_mul hTotal_le tSlope_le
  have hmixR1 : 112*tTotal ≤ 112*1003041 := Nat.mul_le_mul_left 112 tTotal_le
  have hmixR2 : hTotal*rightY ≤ 1242*56 := Nat.mul_le_mul hTotal_le rightY_le
  have hmixZ1 : 112*tSlope ≤ 112*12 := Nat.mul_le_mul_left 112 tSlope_le
  have hmixZ2 : paddedSlope hSlope*rightY ≤ 25*56 :=
    Nat.mul_le_mul hpad_le rightY_le
  constructor <;>
    norm_num [residualParameters,singularParameters,paddedSlope,
      ContactKernelResidualCells6733Research.n,
      ContactKernelResidualCells6733Research.w,
      ContactKernelResidualCells6733Research.a,
      ContactKernelResidualCells6733Research.prime,
      TightParameters.kappa,TightParameters.implicitYCap,
      TightParameters.algebraicCap,UnequalParameters.mixedCost] at * <;>
    omega
private theorem secondStageGates_of_caps
    (rightY hTotal hSlope tTotal tSlope : ℕ)
    (rightY_le : rightY ≤ 59) (hTotal_ne : hTotal ≠ 0)
    (hTotal_le : hTotal ≤ 1240) (hSlope_le : hSlope ≤ 12)
    (tTotal_le : tTotal ≤ 624668) (tSlope_le : tSlope ≤ 11) :
    StageGates
      (residualParameters 56 rightY hTotal hSlope tTotal tSlope)
      (singularParameters 7464132 hTotal hSlope) := by
  have hpad_le : paddedSlope hSlope ≤ 12 := by simp [paddedSlope]; omega
  have hkappa_one : 1 ≤ 2*paddedSlope hSlope-1 := by simp [paddedSlope]; omega
  have hkappa_le : 2*paddedSlope hSlope-1 ≤ 23 := by omega
  have hweighted : 131071 < (2*paddedSlope hSlope-1)*7464132 := by
    have hmul := Nat.mul_le_mul_right 7464132 hkappa_one
    norm_num at hmul ⊢
    omega
  have halg_pos : 1 ≤ (2*paddedSlope hSlope-1)*hTotal :=
    Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hTotal_ne)
  have halg_le : (2*paddedSlope hSlope-1)*hTotal ≤ 23*1240 :=
    Nat.mul_le_mul hkappa_le hTotal_le
  have himp_le :
      ((2*paddedSlope hSlope-1)*7464132-1)/131071 ≤ 1309 := by
    calc
      _ ≤ (23*7464132)/131071 := by
        apply Nat.div_le_div_right
        exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_right 7464132 hkappa_le)
      _ = 1309 := by norm_num
  have hsing_mixed :
      2*(((2*paddedSlope hSlope-1)*7464132-1)/131071)*
        ((2*paddedSlope hSlope-1)*hTotal) < 2130706433 := by
    have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left 2 himp_le) halg_le
    norm_num at hmul ⊢
    omega
  have hmixY1 : paddedSlope hSlope*tTotal ≤ 12*624668 :=
    Nat.mul_le_mul hpad_le tTotal_le
  have hmixY2 : hTotal*tSlope ≤ 1240*11 := Nat.mul_le_mul hTotal_le tSlope_le
  have hmixR1 : 56*tTotal ≤ 56*624668 := Nat.mul_le_mul_left 56 tTotal_le
  have hmixR2 : hTotal*rightY ≤ 1240*59 := Nat.mul_le_mul hTotal_le rightY_le
  have hmixZ1 : 56*tSlope ≤ 56*11 := Nat.mul_le_mul_left 56 tSlope_le
  have hmixZ2 : paddedSlope hSlope*rightY ≤ 12*59 :=
    Nat.mul_le_mul hpad_le rightY_le
  constructor <;>
    norm_num [residualParameters,singularParameters,paddedSlope,
      ContactKernelResidualCells6733Research.n,
      ContactKernelResidualCells6733Research.w,
      ContactKernelResidualCells6733Research.a,
      ContactKernelResidualCells6733Research.prime,
      TightParameters.kappa,TightParameters.implicitYCap,
      TightParameters.algebraicCap,UnequalParameters.mixedCost] at * <;>
    omega
private theorem firstGates (QA QB : Poly)
    (hTotal_ne : firstQTotal QA QB ≠ 0) :
    StageGates (firstStage QA QB) (firstSingular QA QB) := by
  change StageGates
    (residualParameters 112 56 (firstQTotal QA QB) (firstQSlope QA QB)
      (firstTTotal QA QB) (firstTSlope QA QB))
    (singularParameters 14746212 (firstQTotal QA QB) (firstQSlope QA QB))
  exact firstStageGates_of_caps 56 (firstQTotal QA QB) (firstQSlope QA QB)
    (firstTTotal QA QB) (firstTSlope QA QB) (le_refl 56) hTotal_ne
    (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _)
private theorem secondGates (QA QB QC : Poly)
    (hTotal_le : secondQTotal QA QB QC ≤ 1240)
    (hSlope_le : secondQSlope QA QB QC ≤ 12)
    (hTotal_ne : secondQTotal QA QB QC ≠ 0) :
    StageGates (secondStage QA QB QC) (secondSingular QA QB QC) := by
  change StageGates
    (residualParameters 56 59 (secondQTotal QA QB QC) (secondQSlope QA QB QC)
      (secondTTotal QA QB QC) (secondTSlope QA QB QC))
    (singularParameters 7464132 (secondQTotal QA QB QC)
      (secondQSlope QA QB QC))
  exact secondStageGates_of_caps 59 (secondQTotal QA QB QC)
    (secondQSlope QA QB QC) (secondTTotal QA QB QC) (secondTSlope QA QB QC)
    (le_refl 59) hTotal_ne hTotal_le hSlope_le
    (Nat.sub_le _ _) (Nat.sub_le _ _)
private def firstLeftCap (QA QB : Poly) : Cap :=
  ⟨firstQTotal QA QB,112,paddedSlope (firstQSlope QA QB)⟩
private def firstRightCap (QA QB : Poly) : Cap :=
  ⟨firstTTotal QA QB,56,firstTSlope QA QB⟩
private def secondLeftCap (QA QB QC : Poly) : Cap :=
  ⟨secondQTotal QA QB QC,56,paddedSlope (secondQSlope QA QB QC)⟩
private def secondRightCap (QA QB QC : Poly) : Cap :=
  ⟨secondTTotal QA QB QC,59,secondTSlope QA QB QC⟩
private theorem first_regular_eq (QA QB : Poly) :
    (firstStage QA QB).regularCountCap =
      residualPadded (firstLeftCap QA QB) (firstRightCap QA QB) 112 := by
  simp only [firstStage,residualParameters,firstLeftCap,firstRightCap,
    residualPadded,UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator,UnequalParameters.agreement,
    UnequalParameters.leftAgreement,UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost,UnequalParameters.errors,
    UnequalParameters.gap,ContactSingularLedger6600Research.dot,
    ContactKernelResidualCells6733Research.n,
    ContactKernelResidualCells6733Research.w,
    ContactKernelResidualCells6733Research.a,
    ContactKernelArithmetic6733Research.n,
    ContactKernelArithmetic6733Research.w,
    ContactKernelArithmetic6733Research.errors,
    ContactKernelArithmetic6733Research.agreements,
    ContactKernelArithmetic6733Research.gap,u]
private theorem second_regular_eq (QA QB QC : Poly) :
    (secondStage QA QB QC).regularCountCap =
      residualPadded (secondLeftCap QA QB QC) (secondRightCap QA QB QC) 56 := by
  simp only [secondStage,residualParameters,secondLeftCap,secondRightCap,
    residualPadded,UnequalParameters.regularCountCap,
    UnequalParameters.regularNumerator,UnequalParameters.agreement,
    UnequalParameters.leftAgreement,UnequalParameters.rightAgreement,
    UnequalParameters.mixedCost,UnequalParameters.errors,
    UnequalParameters.gap,ContactSingularLedger6600Research.dot,
    ContactKernelResidualCells6733Research.n,
    ContactKernelResidualCells6733Research.w,
    ContactKernelResidualCells6733Research.a,
    ContactKernelArithmetic6733Research.n,
    ContactKernelArithmetic6733Research.w,
    ContactKernelArithmetic6733Research.errors,
    ContactKernelArithmetic6733Research.agreements,
    ContactKernelArithmetic6733Research.gap,u]
private theorem first_singular_succ_eq (QA QB : Poly)
    (h : firstQTotal QA QB ≠ 0) :
    (firstSingular QA QB).countCap+1 =
      singularPadded (firstLeftCap QA QB) (81*agreements) := by
  have hpad : max 1 (max 1 (firstQSlope QA QB)) =
      max 1 (firstQSlope QA QB) := by omega
  simp only [firstSingular,firstLeftCap,singularParameters,singularPadded,
    ensurePositiveSlope,singular,TightParameters.countCap,
    TightParameters.tightNumerator,TightParameters.coreNumerator,
    TightParameters.aggregateCost,TightParameters.agreement,
    TightParameters.implicitYCap,TightParameters.algebraicCap,
    TightParameters.kappa,TightParameters.errors,TightParameters.gap,
    paddedSlope,hpad,agreements,
    ContactKernelArithmetic6733Research.n,
    ContactKernelArithmetic6733Research.w,
    ContactKernelArithmetic6733Research.errors,
    ContactKernelArithmetic6733Research.gap,
    ContactKernelArithmetic6733Research.u,
    ContactKernelResidualCells6733Research.n,
    ContactKernelResidualCells6733Research.w,
    ContactKernelResidualCells6733Research.a,
    ContactSingularLedger6600Research.dot]
  rw [if_neg]
  · norm_num only [pow_two,Nat.mul_assoc]
  · simp only [not_or]
    exact ⟨Nat.one_le_iff_ne_zero.mp (le_max_left 1 _),h,
      Nat.one_le_iff_ne_zero.mp (le_max_left 1 112)⟩
private theorem second_singular_succ_eq (QA QB QC : Poly)
    (h : secondQTotal QA QB QC ≠ 0) :
    (secondSingular QA QB QC).countCap+1 =
      singularPadded (secondLeftCap QA QB QC) (41*agreements) := by
  have hpad : max 1 (max 1 (secondQSlope QA QB QC)) =
      max 1 (secondQSlope QA QB QC) := by omega
  simp only [secondSingular,secondLeftCap,singularParameters,singularPadded,
    ensurePositiveSlope,singular,TightParameters.countCap,
    TightParameters.tightNumerator,TightParameters.coreNumerator,
    TightParameters.aggregateCost,TightParameters.agreement,
    TightParameters.implicitYCap,TightParameters.algebraicCap,
    TightParameters.kappa,TightParameters.errors,TightParameters.gap,
    paddedSlope,hpad,agreements,
    ContactKernelArithmetic6733Research.n,
    ContactKernelArithmetic6733Research.w,
    ContactKernelArithmetic6733Research.errors,
    ContactKernelArithmetic6733Research.gap,
    ContactKernelArithmetic6733Research.u,
    ContactKernelResidualCells6733Research.n,
    ContactKernelResidualCells6733Research.w,
    ContactKernelResidualCells6733Research.a,
    ContactSingularLedger6600Research.dot]
  rw [if_neg]
  · norm_num only [pow_two,Nat.mul_assoc]
  · simp only [not_or]
    exact ⟨Nat.one_le_iff_ne_zero.mp (le_max_left 1 _),h,
      Nat.one_le_iff_ne_zero.mp (le_max_left 1 56)⟩
theorem selectedNoLargePencilBound6733 :
    SelectedNoLargePencilBound IRSProfile.domain 131071 80092 budget := by
  intro U seeds A selected hdegree hcardRaw hvalues hnoRaw
  have hcard : ∀ γ ∈ seeds,182052 ≤ (A γ).card := by
    intro γ hγ
    have h := hcardRaw γ hγ
    norm_num [IRSProfile.Index] at h ⊢
    exact h
  have hagreement := full_domain_agreement U seeds A selected hcard hvalues
  have hno : NoLargeSelectedPencil selected seeds 131071 80092 := by
    intro P0 P1 hP0 hP1
    have hh := hnoRaw P0 P1 hP0 hP1
    convert hh using 1
    · apply congrArg Finset.card
      ext γ
      simp [pencilSeeds]
  obtain ⟨S⟩ := exists_selected_interpolants (U 0) (U 1)
  have hH12 : gcd12 S.QA S.QB = S.H := by
    simpa only [gcd12] using S.H_eq.symm
  have hG123 : gcd123 S.QA S.QB S.QC = S.G := by
    simp only [gcd123,gcd12]
    rw [← S.H_eq]
    exact S.G_eq.symm
  have hGdvdH : S.G ∣ S.H := by
    rw [S.G_eq]
    exact gcd_dvd_left S.H S.QC
  have hHcapsA :=
    (ContactKernelCommonGCDResearch.mem_flagGlobalCoefficientBox_iff
      S.H 7464132 131071 1003041 12 (by decide)).mp S.H_flagA
  have hGcapsA :=
    (ContactKernelCommonGCDResearch.mem_flagGlobalCoefficientBox_iff
      S.G 7464132 131071 1003041 12 (by decide)).mp S.G_flagA
  have hGcapsC :=
    (ContactKernelCommonGCDResearch.mem_flagGlobalCoefficientBox_iff
      S.G 7828236 131071 624668 11 (by decide)).mp S.G_flagC
  let hcap := ContactKernelFixedSelected6733Research.capOf S.H
  let gcap := ContactKernelFixedSelected6733Research.capOf S.G
  have hgh : CapLE gcap hcap := by
    simp only [CapLE,gcap,hcap,
      ContactKernelFixedSelected6733Research.capOf]
    exact ⟨
      weightedTotalDegree_le_of_dvd residualTotalWeights S.G S.H hGdvdH S.H_ne,
      weightedTotalDegree_le_of_dvd residualYSWeights S.G S.H hGdvdH S.H_ne,
      weightedTotalDegree_le_of_dvd residualSWeights S.G S.H hGdvdH S.H_ne⟩
  have hhmax : CapLE hcap hmax := by
    exact ⟨S.H_total_le,S.H_ys_le,hHcapsA.2.1⟩
  have hgNested := cap_nested S.G
  have hgTotal : gcap.total ≤ 1240 := S.G_total_le
  have hgMiddle : gcap.middle ≤ 54 := S.G_ys_le
  have hgInner : gcap.inner ≤ 11 := hGcapsC.2.1
  have hfirstTotal : firstQTotal S.QA S.QB ≠ 0 := by
    rw [firstQTotal,hH12]
    have ht := S.H_total_le
    omega
  have hsecondTotalLe : secondQTotal S.QA S.QB S.QC ≤ 1240 := by
    rw [secondQTotal,hH12,hG123]
    exact (Nat.sub_le _ _).trans S.H_total_le
  have hsecondSlopeLe : secondQSlope S.QA S.QB S.QC ≤ 12 := by
    rw [secondQSlope,hH12,hG123]
    exact (Nat.sub_le _ _).trans hHcapsA.2.1
  have hcover := selected_recursive_cover U seeds A selected S hdegree hcard hvalues
  have hfirstRaw := firstResidualCell_count_lt S.QA S.QB S.QC
    S.QA_ne S.QB_ne S.QA_flag S.QB_flag selected seeds (U 0) (U 1)
    hcover hdegree hagreement hno (fun _ ↦ firstGates S.QA S.QB hfirstTotal)
  have hsecondRaw := secondResidualCell_count_lt S.QA S.QB S.QC
    S.QA_ne S.QC_ne S.QA_flag S.QC_flag selected seeds (U 0) (U 1)
    hcover hdegree hagreement hno
    (fun hz ↦ secondGates S.QA S.QB S.QC hsecondTotalLe hsecondSlopeLe hz)
  have hfirstBase :
      (firstResidualSeeds selected seeds S.QA S.QB).card ≤
        (firstStage S.QA S.QB).regularCountCap+
          (firstSingular S.QA S.QB).countCap := by
    rw [firstCeiling,if_neg hfirstTotal] at hfirstRaw
    omega
  have hfirstCaps :
      firstLeftCap S.QA S.QB = paddedLeftComplement parentB hcap 112 ∧
        firstRightCap S.QA S.QB = rawComplement parentA hcap 56 := by
    constructor
    · simp only [firstLeftCap,paddedLeftComplement,firstQTotal,firstQSlope,
        hcap,ContactKernelFixedSelected6733Research.capOf,parentB]
      rw [hH12]
      rfl
    · simp only [firstRightCap,rawComplement,firstTTotal,firstTSlope,
        hcap,ContactKernelFixedSelected6733Research.capOf,parentA]
      rw [hH12]
  have hfirstCost :
      (firstResidualSeeds selected seeds S.QA S.QB).card ≤ stage1Safe gcap := by
    calc
      _ ≤ (firstStage S.QA S.QB).regularCountCap+
          (firstSingular S.QA S.QB).countCap := hfirstBase
      _ ≤ (firstStage S.QA S.QB).regularCountCap+
          ((firstSingular S.QA S.QB).countCap+1) := by omega
      _ = stage1Safe hcap := by
        rw [first_regular_eq,first_singular_succ_eq S.QA S.QB hfirstTotal,
          hfirstCaps.1,hfirstCaps.2]
        rfl
      _ ≤ stage1Safe gcap := stage1Safe_antitone hgh
  have hsecondCost :
      (secondResidualSeeds selected seeds S.QA S.QB S.QC).card ≤
        stage2Safe gcap := by
    by_cases hz : secondQTotal S.QA S.QB S.QC = 0
    · rw [secondCeiling,if_pos hz] at hsecondRaw
      omega
    · have hbase :
          (secondResidualSeeds selected seeds S.QA S.QB S.QC).card ≤
            (secondStage S.QA S.QB S.QC).regularCountCap+
              (secondSingular S.QA S.QB S.QC).countCap := by
        rw [secondCeiling,if_neg hz] at hsecondRaw
        omega
      have hsecondCaps :
          secondLeftCap S.QA S.QB S.QC =
              paddedLeftComplement hcap gcap 56 ∧
            secondRightCap S.QA S.QB S.QC =
              rawComplement parentC gcap 59 := by
        constructor
        · simp only [secondLeftCap,paddedLeftComplement,secondQTotal,
            secondQSlope,hcap,gcap,
            ContactKernelFixedSelected6733Research.capOf]
          rw [hH12,hG123]
          rfl
        · simp only [secondRightCap,rawComplement,secondTTotal,
            secondTSlope,gcap,
            ContactKernelFixedSelected6733Research.capOf,parentC]
          rw [hG123]
      calc
        _ ≤ (secondStage S.QA S.QB S.QC).regularCountCap+
            (secondSingular S.QA S.QB S.QC).countCap := hbase
        _ ≤ (secondStage S.QA S.QB S.QC).regularCountCap+
            ((secondSingular S.QA S.QB S.QC).countCap+1) := by omega
        _ = residualPadded (paddedLeftComplement hcap gcap 56)
              (rawComplement parentC gcap 59) 56+
            singularPadded (paddedLeftComplement hcap gcap 56)
              (41*agreements) := by
          rw [second_regular_eq,
            second_singular_succ_eq S.QA S.QB S.QC hz,
            hsecondCaps.1,hsecondCaps.2]
        _ ≤ stage2Safe gcap := stage2Safe_of_caps hhmax.1 hhmax.2.2
  let Delta := fixedSeeds selected seeds S.QA S.QB S.QC
  have hGflag : S.G ∈
      ContactFlagInterpolation6641Research.globalCoefficientBox
        IRSProfile.Field 7464132 131071 1240 11 := by
    apply (ContactKernelCommonGCDResearch.mem_flagGlobalCoefficientBox_iff
      S.G 7464132 131071 1240 11 (by decide)).mpr
    exact ⟨S.G_total_le,hGcapsC.2.1,hGcapsA.2.2⟩
  have hsub : Delta ⊆ seeds := by
    simpa only [Delta] using fixedSeeds_subset selected seeds S.QA S.QB S.QC
  have hfixedSolution : ∀ γ ∈ Delta,
      specialization IRSProfile.Field (selected γ) γ S.G = 0 := by
    intro γ hγ
    have hv := fixedSeeds_vanish selected seeds S.QA S.QB S.QC γ
      (by simpa only [Delta] using hγ)
    rw [hG123] at hv
    exact hv
  have hfixedDegree : ∀ γ ∈ Delta,(selected γ).natDegree ≤ 131071 :=
    fun γ hγ ↦ hdegree γ (hsub hγ)
  have hfixedAgreement : ∀ γ ∈ Delta,182052 ≤
      ((Finset.univ : Finset IRSProfile.Index).filter (fun i ↦
        (selected γ).eval (IRSProfile.domain i) = U 0 i+γ*U 1 i)).card :=
    fun γ hγ ↦ hagreement γ (hsub hγ)
  have hfixedNoPencil : NoLargeSelectedPencil selected Delta 131071 80092 :=
    noLargeSelectedPencil_mono selected seeds Delta 131071 80092 hsub hno
  have hfixed := fixed_selected_count_le S.G S.G_ne hGflag S.G_ys_le
    selected Delta (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain
    (U 0) (U 1) IRSProfile.domain.injective.injOn
    (by norm_num [IRSProfile.Index]) hfixedDegree hfixedSolution
    hfixedAgreement hfixedNoPencil
  have hpartition := partition_card selected seeds S.QA S.QB S.QC
  have htotal : seeds.card ≤ coupledSafe gcap := by
    rw [← hpartition]
    unfold coupledSafe
    have hs := Nat.add_le_add (Nat.add_le_add hfirstCost hsecondCost) hfixed
    simp only [Delta,gcap,ContactKernelArithmetic6733Research.agreements,
      ContactKernelArithmetic6733Research.n,
      ContactKernelArithmetic6733Research.errors] at hs ⊢
    norm_num at hs ⊢
    omega
  have hbudget := coupledSafe_lt_budget gcap hgTotal hgMiddle hgInner
    hgNested.1 hgNested.2
  omega
end
end ProximityPrize.SubmissionLower.ContactKernelSelectedBound6733Research
