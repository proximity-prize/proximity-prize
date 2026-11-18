import ProximityPrize.SubmissionLower.Koala6831MovingSources

namespace ProximityPrize.SubmissionLower.Koala6831Moving

open scoped BigOperators
open Koala6831MovingSources LocatorDerivativeChain LocatorLowQuotient
open RCN081 RCN156 RCN234

noncomputable section

variable {K : Type} [Field K]
local instance rfreeDecidableEq : DecidableEq K := Classical.decEq _

abbrev ExceptionPoly (K : Type) [Field K] := MvPolynomial (Fin 4) K

def freeAndTailCarrier (H : ExceptionPoly K) : ExceptionPoly K :=
  ∏ F ∈ RCN082.activeFactors H, dR (chainLength F) F

private theorem dR_weight_le (weights : Fin 4 → ℕ) (j : ℕ) (F : ExceptionPoly K) :
    wt weights (dR j F) ≤ wt weights F := by
  induction j with
  | zero => simp only [dR_zero, le_refl]
  | succ j ih =>
    rw [dR_succ]
    exact (wt_pderiv_le weights (dR j F) 2 _ ih).trans (Nat.sub_le _ _)

theorem freeAndTailCarrier_weight_le (H : ExceptionPoly K) (hH : H ≠ 0)
    (weights : Fin 4 → ℕ) : wt weights (freeAndTailCarrier H) ≤ wt weights H := by
  classical
  calc
    _ ≤ ∑ F ∈ RCN082.activeFactors H, wt weights (dR (chainLength F) F) :=
      RCN293.weightedTotalDegree_prod_le weights _ _
    _ ≤ ∑ F ∈ RCN082.activeFactors H, wt weights F :=
      Finset.sum_le_sum fun F _ => dR_weight_le weights _ F
    _ ≤ wt weights H := RCN293.sum_weighted_degrees_le_of_prod_dvd weights _ id H hH
      (RCN082.activeFactors_product_dvd H hH)

theorem freeAndTailCarrier_ne_zero (H : ExceptionPoly K) (hH : H ≠ 0)
    (p : ℕ) [CharP K p] (hsmall : H.degreeOf 2 < p) : freeAndTailCarrier H ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro F hF
  have hspec := RCN082.activeFactors_spec H F hF
  have hdeg := degreeOf_le_of_dvd (2 : Fin 4) F H hspec.2.1 hH
  exact dR_ne_zero F hspec.1.ne_zero p (hdeg.trans_lt hsmall) _ le_rfl

theorem freeAndTailCarrier_R_degree (H : ExceptionPoly K) : (freeAndTailCarrier H).degreeOf 2 = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  refine (MvPolynomial.degreeOf_prod_le _ _ _).trans ?_
  exact (Finset.sum_eq_zero fun F _ => chainLength_spec F).le

theorem freeAndTailCarrier_vanishes_of_tail (H F : ExceptionPoly K)
    (hF : F ∈ RCN082.activeFactors H) (P : Polynomial K) (g : K)
    (hvanish : RCN319.specialization K P g (dR (chainLength F) F) = 0) :
    RCN319.specialization K P g (freeAndTailCarrier H) = 0 := by
  classical
  have hdvd : dR (chainLength F) F ∣ freeAndTailCarrier H := Finset.dvd_prod_of_mem _ hF
  obtain ⟨Q, hQ⟩ := hdvd
  rw [hQ, map_mul, hvanish, zero_mul]

theorem primary_regular_fold_or_free (H : ExceptionPoly K) (hH : H ≠ 0)
    (P : Polynomial K) (g : K) (hzero : RCN319.specialization K P g H = 0) :
    RCN319.specialization K P g (freeAndTailCarrier H) = 0 ∨
    ∃ F : RCN266.RegularIndex H, RCN319.specialization K P g F.1 = 0 ∧
      (RCN319.specialization K P g (dR 1 F.1) ≠ 0 ∨
       RCN319.specialization K P g (dR 1 F.1) = 0 ∧
       RCN319.specialization K P g (dR (chainLength F.1) F.1) ≠ 0) := by
  classical
  obtain ⟨F, hF, hzeroF⟩ := exists_active_factor_of_solution H hH P g hzero
  by_cases htail : RCN319.specialization K P g (dR (chainLength F) F) = 0
  · exact .inl (freeAndTailCarrier_vanishes_of_tail H F hF P g htail)
  have hpos : 0 < F.degreeOf 2 := by
    by_contra! hfree
    have hlength : chainLength F = 0 := Nat.eq_zero_of_le_zero ((chainLength_le F).trans hfree)
    exact htail (by simpa only [hlength, dR_zero] using hzeroF)
  let factor : RCN266.RegularIndex H := ⟨F, by
    simpa only [RCN167.positiveRFactors, Finset.mem_filter] using And.intro hF hpos⟩
  refine .inr ⟨factor, hzeroF, ?_⟩
  by_cases hfirst : RCN319.specialization K P g (dR 1 F) = 0
  · exact .inr ⟨hfirst, htail⟩
  · exact .inl hfirst

theorem dR_cumulative_drop (F : ExceptionPoly K) (j : ℕ) (h : dR j F ≠ 0) :
    wt residualSWeights (dR j F) + j ≤ wt residualSWeights F ∧
    wt residualYSWeights (dR j F) + j ≤ wt residualYSWeights F ∧
    wt residualTotalWeights (dR j F) + j ≤ wt residualTotalWeights F := by
  have step (weights : Fin 4 → ℕ) (hweight : weights 2 = 1) :
      wt weights (dR j F) + j ≤ wt weights F := by
    have hstep := LocatorArbitraryPowerContact.iteratePderivR_weight_add_le weights F j h
    simpa only [show LocatorArbitraryPowerContact.iteratePderivR j F = dR j F by rfl,
      hweight, Nat.mul_one] using hstep
  exact ⟨step residualSWeights rfl, step residualYSWeights rfl, step residualTotalWeights rfl⟩

theorem fold_exists_first_proper_cut {R : Type*} [CommRing R]
    (ψ : ExceptionPoly K →+* R) (component : Ideal R) (F : ExceptionPoly K)
    (h₀ : ψ F ∈ component) (h₁ : ψ (dR 1 F) ∈ component)
    (htop : ψ (dR (chainLength F) F) ∉ component) :
    ∃ j : ℕ, 1 ≤ j ∧ j + 1 ≤ chainLength F ∧
      ψ (dR j F) ∈ component ∧ ψ (dR (j + 1) F) ∉ component ∧
      (∀ k ≤ j, ψ (dR k F) ∈ component) ∧
      (wt residualSWeights (dR j F) + 1 ≤ wt residualSWeights F ∧
       wt residualYSWeights (dR j F) + 1 ≤ wt residualYSWeights F ∧
       wt residualTotalWeights (dR j F) + 1 ≤ wt residualTotalWeights F) ∧
      (wt residualSWeights (dR (j + 1) F) + 2 ≤ wt residualSWeights F ∧
       wt residualYSWeights (dR (j + 1) F) + 2 ≤ wt residualYSWeights F ∧
       wt residualTotalWeights (dR (j + 1) F) + 2 ≤ wt residualTotalWeights F) := by
  classical
  have hex : ∃ m, ψ (dR m F) ∉ component := ⟨chainLength F, htop⟩
  let m := Nat.find hex
  have hm : ψ (dR m F) ∉ component := Nat.find_spec hex
  have hle : m ≤ chainLength F := Nat.find_min' hex htop
  have hm2 : 2 ≤ m := by
    by_contra! h
    interval_cases m
    · exact hm (by simpa only [dR_zero] using h₀)
    · exact hm h₁
  let j := m - 1
  have hnext : j + 1 = m := by dsimp [j]; omega
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hprior (k : ℕ) (hk : k ≤ j) : ψ (dR k F) ∈ component := by
    by_contra! hn
    exact Nat.find_min hex (by omega : k < m) hn
  have hproper : ψ (dR (j + 1) F) ∉ component := by rw [hnext]; exact hm
  have hn : dR (j + 1) F ≠ 0 := by
    intro hz
    apply hproper
    rw [hz, map_zero]
    exact component.zero_mem
  have hcarrier_ne : dR j F ≠ 0 := by
    intro hz
    exact hn (by rw [dR_succ, hz, map_zero])
  obtain ⟨hs₁, hy₁, ht₁⟩ := dR_cumulative_drop F j hcarrier_ne
  obtain ⟨hs₂, hy₂, ht₂⟩ := dR_cumulative_drop F (j + 1) hn
  exact ⟨j, hj, by rw [hnext]; exact hle, hprior _ le_rfl, hproper, hprior,
    ⟨by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega⟩⟩

section FixedProfile

open RCN318

def freeAndTailParameters : TightParameters := ⟨262144, weight, agreement, Stage.primary.cutoff, 41882, 1⟩

set_option maxRecDepth 80000 in

theorem freeAndTailCarrier_seed_count [CharP K 2130706433] {I : Type}
    (H : ExceptionPoly K) (hH : H ≠ 0)
    (hbox : H ∈ nestedCoefficientBox K Stage.primary.cutoff weight 41882 418 93)
    (seeds : Finset K) (selected : K → Polynomial K) (nodes : Finset I)
    (x u₀ u₁ : I → K) (hinj : Set.InjOn x nodes) (hnodes : nodes.card = 262144)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ weight)
    (hsol : ∀ g ∈ seeds, RCN319.specialization K (selected g) g (freeAndTailCarrier H) = 0)
    (hagree : ∀ g ∈ seeds, agreement ≤
      (nodes.filter fun i => (selected g).eval (x i) = u₀ i + g * u₁ i).card)
    (hpencil : RCN238.NoLargeSelectedPencil selected seeds weight 81066) :
    seeds.card ≤ 36089978520741 := by
  let J := freeAndTailCarrier H
  let params := freeAndTailParameters
  have hweights := nested_mem_weights hbox hH
  have hsmall : H.degreeOf 2 < 2130706433 := by
    apply lt_of_le_of_lt (b := 93) ?_ (by decide +kernel)
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    exact (hbox hd).2.2.1
  have hJ : J ≠ 0 := freeAndTailCarrier_ne_zero H hH _ hsmall
  have hJR : J.degreeOf 2 = 0 := freeAndTailCarrier_R_degree H
  have hJBox : J ∈ RCN174.globalCoefficientBox K params.D params.w params.L params.s := by
    intro d hd
    have ht := (MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans
      ((freeAndTailCarrier_weight_le H hH residualTotalWeights).trans hweights.1)
    have hr := (MvPolynomial.monomial_le_degreeOf (2 : Fin 4) hd).trans_eq hJR
    have hx := (MvPolynomial.le_weightedTotalDegree (contactWeights weight) hd).trans_lt
      ((freeAndTailCarrier_weight_le H hH (contactWeights weight)).trans_lt hweights.2.2.2)
    have ht' : d 1 + d 2 + d 3 ≤ 41882 := by
      simpa [weight_fin4, residualTotalWeights] using ht
    exact ⟨by change d 1 + d 3 ≤ 41882; omega,
      hr.trans (by decide +kernel),
      by simpa [weight_fin4, contactWeights, Nat.mul_comm, params, freeAndTailParameters] using hx⟩
  have herrors : params.errors = 81066 := by decide +kernel
  have hpencil' : RCN238.NoLargeSelectedPencil selected seeds params.w params.errors := by
    rw [herrors]
    exact hpencil
  have hcount := rfree_seed_count_le params J hJ 2130706433 hJBox hJR rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) selected seeds nodes x u₀ u₁ hinj hnodes
    hdegree hsol hagree hpencil'
  exact hcount.trans (by decide +kernel)

end FixedProfile

end

end ProximityPrize.SubmissionLower.Koala6831Moving

/- Retuned for the full 68.32 domain and the m=303 primary, November 2026. -/

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
