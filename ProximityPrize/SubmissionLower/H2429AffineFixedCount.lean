import ProximityPrize.SubmissionLower.HighCore82258PrefixHelpers
import ProximityPrize.SubmissionLower.H2429AffineRates
import ProximityPrize.SubmissionLower.PeriodTwoPrefixReconstruction

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace P1_7_4_3
noncomputable section
open Polynomial Finset PolynomialDifferential
open P1 (K I node p)
open K1_13 (Row extend)
open K1_13_5 (RegularAt)
open K1_13_5_3
open K1_14 (seedEmbedding)
open K1_14_3_6 (power totalCap topCap)
open private solution_taylor short_numerator_bound short_denominator_bound
  from ProximityPrize.SubmissionLower.UpperBranch4
open scoped BigOperators

/-- Construct a short cut from weights for the specified scalar family.
The true scalar degree still controls the derivative specialization. -/
theorem short_cut_with_weights (f : Row 2) {d t B J : ℕ} (hd : d < p) (ht : t ≤ d)
    (hJ:0 < J) (hB:f.totalDegree≤B) (hj:f.degreeOf 1≤J)
    (w:I→K) (i:I) (Eligible : K[X] → Prop)
    (c : CenterField) (a : Fin (t+1) → CenterField)
    (ha : ∀ S : K[X], S.natDegree ≤ d → Eligible S →
      seedEmbedding (S.eval (node i)) =
        c + ∑ j,a j*(Polynomial.taylor center (S.map seedEmbedding)).coeff j) :
    ∃ cut : MvPolynomial (Fin 2) CenterField,
      cut ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 (totalCap t B) (topCap t B J) ∧
      ∀ S : K[X], S.natDegree ≤ d → RegularAt 1 f (extend S) → Eligible S →
        (MvPolynomial.aeval (marked (extend S)) cut=0↔S.eval (node i)=w i):=by
  classical
  let Q:=chart f
  let D:=initialJetSeparant center Q ^ power t
  let N (j:Fin (t+1)):=commonTaylorNumerator center Q (power t) j
  let cut:=MvPolynomial.C (c - seedEmbedding (w i))*D + ∑ j,MvPolynomial.C (a j)*N j
  have hτ : TaylorExponentSufficient 1 (t+1) (power t) :=
    taylorExponentSufficient_firstOrder_tight t
  refine ⟨cut, ?_, ?_⟩
  · dsimp only [cut]
    apply Submodule.add_mem
    · rw [← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (short_denominator_bound f hB hj)
    · apply Submodule.sum_mem
      intro j _
      rw [← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (short_numerator_bound f hJ hB hj j)
  · intro S hS hreg hEligible
    obtain ⟨hsep,hcoef⟩:=solution_taylor hd hreg
    have hval := ha S hS hEligible
    let x:=marked (extend S)
    have he (j : Fin (t+1)) : MvPolynomial.aeval x (N j) =
        MvPolynomial.aeval x D*(Polynomial.taylor center (S.map seedEmbedding)).coeff j:=by
      dsimp only [N,D]
      rw [aeval_commonTaylorNumerator center Q x (hτ j) hsep, map_pow,
        hcoef _ ((Nat.le_of_lt_succ j.isLt).trans ht)]
    have hdne : MvPolynomial.aeval x D ≠ 0 := by
      dsimp only [D]
      rw [map_pow]
      exact pow_ne_zero _ hsep
    have hc : MvPolynomial.aeval x cut =
        MvPolynomial.aeval x D*(seedEmbedding (S.eval (node i)) - seedEmbedding (w i)):=by
      dsimp only [cut]
      rw [hval, map_add, map_mul, map_sum, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply,
        mul_sub,mul_add,Finset.mul_sum]
      simp only [map_mul,MvPolynomial.aeval_C,Algebra.algebraMap_self_apply,he]
      have hsum : (∑ j : Fin (t+1), a j *
          (MvPolynomial.aeval x D*(Polynomial.taylor center (S.map seedEmbedding)).coeff j)) =
          ∑ j : Fin (t+1), MvPolynomial.aeval x D *
            (a j*(Polynomial.taylor center (S.map seedEmbedding)).coeff j) :=
        Finset.sum_congr rfl fun _ _ => by ring
      rw [hsum]
      ring
    change MvPolynomial.aeval x cut=0↔_
    rw [hc,mul_eq_zero,or_iff_right hdne,sub_eq_zero,seedEmbedding.injective.eq_iff]

end
end P1_7_4_3

namespace H2429AffineFixedCount

open Polynomial Finset
open P1 (I node p)
open HighCore82258 (K agreement blockLength FixedWord persistent_card_le section_incidence)
open P1_7_3 (persistentNodes hits_persistent)
open P1_7_4 (ODEGuard)
open P1_7_4_3 (mix cast_mixed short_cut_with_weights)
open K1_13 (Row extend embed)
open K1_13_5 (RegularAt)
open K1_13_5_3 (center toCenter)
open K1_14 (seedEmbedding)
open K1_14_2 (ODE fixedAt)
open K1_14_2_2 (ODECaps)
open K1_14_3_6 (power totalCap topCap)
open HighCore82258PrefixHelpers (section_bound fixed_bound)
open H2429AffineRates (ratio order)
open scoped Polynomial

def totalRate (B : ℕ) : ℚ := ratio 0 * (1 + 257285 * ((B - 1 : ℕ) : ℚ))

def topRate (B J : ℕ) : ℚ :=
  min (totalRate B) (ratio 0 * (128644 + 257285 * ((J - 1 : ℕ) : ℚ)))

theorem totalRate_nonneg (B : ℕ) : 0 ≤ totalRate B := by
  unfold totalRate ratio
  positivity

theorem topRate_nonneg (B J : ℕ) : 0 ≤ topRate B J := by
  apply le_min (totalRate_nonneg B)
  unfold ratio
  positivity

theorem caps_weighted {s B J : ℕ} (hs : s ≤ 133500) (hB : 2 ≤ B) :
    ratio s * totalCap (order s) B ≤ totalRate B ∧
      ratio s * topCap (order s) B J ≤ topRate B J := by
  have hr : 0 ≤ ratio s := by
    have h : (s : ℚ) ≤ 133500 := by exact_mod_cast hs
    unfold ratio
    exact div_nonneg (by linarith) (by linarith)
  have hb : (1 : ℚ) ≤ ((B-1 : ℕ) : ℚ) := by
    exact_mod_cast (show 1 ≤ B-1 by omega)
  have hj : (0 : ℚ) ≤ ((J-1 : ℕ) : ℚ) := Nat.cast_nonneg _
  have hcore :
      ratio s * totalCap (order s) B ≤ totalRate B ∧
      ratio s * (power (order s) * (J-1) + order s : ℕ) ≤
        ratio 0 * (128644 + 257285 * ((J-1 : ℕ) : ℚ)) := by
    by_cases h : s < 128643
    · have ht : order s = 128644-s := max_eq_right (by omega)
      have ht2 : 3 ≤ 2 * order s := by rw [ht]; omega
      have htQ : (order s : ℚ) = 128644 - (s : ℚ) := by
        rw [ht,Nat.cast_sub (by omega)]
        norm_num
      have hpQ : (power (order s) : ℚ) = 257285 - 2*(s : ℚ) := by
        unfold power
        rw [Nat.cast_sub ht2]
        push_cast
        rw [htQ]
        ring
      have htotal : (totalCap (order s) B : ℚ) =
          1 + 257285*((B-1 : ℕ) : ℚ) - (2*((B-1 : ℕ) : ℚ))*s := by
        unfold totalCap
        push_cast
        rw [hpQ]
        ring
      have htop : ((power (order s) * (J-1) + order s : ℕ) : ℚ) =
          128644 + 257285*((J-1 : ℕ) : ℚ) - (1 + 2*((J-1 : ℕ) : ℚ))*s := by
        push_cast
        rw [hpQ,htQ]
        ring
      constructor
      · rw [htotal,totalRate]
        apply H2429AffineRates.affine hs
        · linarith only [hb]
        · rw [← htotal]
          positivity
      · rw [htop]
        apply H2429AffineRates.affine hs
        · linarith only [hj]
        · rw [← htop]
          positivity
    · have ht : order s = 1 := by
        unfold order
        apply max_eq_left
        omega
      have hratio := H2429AffineRates.ratio_le_three hs
      have hdensity : (1 : ℚ) ≤ ratio 0 := by norm_num [ratio]
      have htotal : (3 : ℚ) ≤ 1 + 257285*((B-1 : ℕ) : ℚ) := by linarith only [hb]
      have htop : (3 : ℚ) ≤ 128644 + 257285*((J-1 : ℕ) : ℚ) := by linarith only [hj]
      have hA : totalCap (order s) B = 1 := by simp [ht,totalCap,power]
      have hV : power (order s) * (J-1) + order s = 1 := by simp [ht,power]
      rw [hA,hV,Nat.cast_one,mul_one,totalRate]
      exact ⟨hratio.trans (htotal.trans (le_mul_of_one_le_left (by positivity) hdensity)),
        hratio.trans (htop.trans (le_mul_of_one_le_left (by positivity) hdensity))⟩
  refine ⟨hcore.1, le_min ?_ ?_⟩
  · exact (mul_le_mul_of_nonneg_left (by exact_mod_cast
      (show topCap (order s) B J ≤ totalCap (order s) B from min_le_left _ _)) hr).trans hcore.1
  · exact (mul_le_mul_of_nonneg_left (by exact_mod_cast
      (show topCap (order s) B J ≤ power (order s) * (J-1) + order s from
        min_le_right _ _)) hr).trans hcore.2

/-- Compare the exact rates with the standard linearized rank ledger. -/
theorem linearized_rates (B J : ℕ) (hJ : 0 < J) :
    totalRate B ≤ ratio 0 + 2 * (ratio 0 * 128644) * ((B-1 : ℕ) : ℚ) ∧
    topRate B J ≤ min (totalRate B) ((ratio 0 * 128644) * ((2*J-1 : ℕ) : ℚ)) := by
  have hd : 0 ≤ ratio 0 := by unfold ratio; positivity
  have hb : (0 : ℚ) ≤ ((B-1 : ℕ) : ℚ) := Nat.cast_nonneg _
  have hj : (0 : ℚ) ≤ ((J-1 : ℕ) : ℚ) := Nat.cast_nonneg _
  constructor
  · unfold totalRate
    rw [mul_add,mul_one]
    refine add_le_add le_rfl ?_
    rw [show 2*(ratio 0*128644)*((B-1 : ℕ) : ℚ) =
      ratio 0*(257288*((B-1 : ℕ) : ℚ)) by ring]
    apply mul_le_mul_of_nonneg_left _ hd
    linarith only [hb]
  · apply le_min (min_le_left _ _)
    apply (min_le_right _ _).trans
    have hform : 2*J-1 = 2*(J-1)+1 := by omega
    rw [hform]
    push_cast
    rw [show ratio 0 * 128644 * (2 * ((J-1 : ℕ) : ℚ) + 1) =
      ratio 0*(128644+257288*((J-1 : ℕ) : ℚ)) by ring]
    apply mul_le_mul_of_nonneg_left _ hd
    linarith only [hj]

private theorem count_regular {w : I → K} {T : Finset K} {S : K → K[X]} {B J : ℕ}
    (hw : FixedWord w T S 133500)
    (G : K[X]) (R : Fin 2 → K[X]) (off : ∀ i : I, G.eval (node i) ≠ 0)
    (hdegree : ResidueSpace.space G 128643 R ≤ degreeLT K 133501)
    (hframe : ∀ γ ∈ T, S γ ∈ ResidueSpace.space G 128643 R) (hB : 2 ≤ B) (hJ : 0 < J)
    (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hb : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (S γ))) :
    (T.card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) (totalRate B) (topRate B J) + 1 := by
  by_cases hsmall : T.card ≤ 1
  · have hnonneg :
        0 ≤ mix f.totalDegree (f.degreeOf 1) (totalRate B) (topRate B J) := by
      unfold mix
      have ha := totalRate_nonneg B
      have hv := topRate_nonneg B J
      positivity
    exact (show (T.card : ℚ) ≤ 1 from by exact_mod_cast hsmall).trans (by linarith)
  let sites := persistentNodes w T S
  let t := order sites.card
  have hs : sites.card ≤ 133500 := persistent_card_le hw (by omega)
  have ht : t ≤ 133500 := max_le (by decide) ((Nat.sub_le _ _).trans (by decide))
  have htpos : 0 < t := Nat.le_max_left _ _
  have hindex : Function.Injective (Polynomial.eval₂RingHom seedEmbedding center) :=
    PeriodTwoPrefixReconstruction.eval₂_symbol_injective embed toCenter
      (IsFractionRing.injective _ _)
  obtain ⟨c,A,hweights⟩ := PeriodTwoPrefixReconstruction.indexed_interpolation_weights_2429
    G R ⟨node,ProximityPrize.Benchmark.IRSProfile.domain.injective⟩ sites w (fun i _ => off i) hdegree (by decide : 133501 ≤ p)
    seedEmbedding center hindex
  have ha : 0 < totalCap t B := by simp [totalCap]
  have hv : 0 < topCap t B J := lt_min ha ((Nat.le_add_left _ _).trans' htpos)
  let D := MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1)
    (totalCap t B) (topCap t B J)
  have hcount := section_incidence hw D (fun i hi => by
    obtain ⟨cut,hcut,he⟩ := short_cut_with_weights f
      (by decide : 133500 < p) ht hJ hb hj w i
      (fun Q => Q ∈ ResidueSpace.space G 128643 R ∧
        ∀ j ∈ sites, Q.eval (node j) = w j)
      (c (node i)) (A (node i)) (fun Q _ hQ => hweights (node i) Q hQ.1 hQ.2)
    exact section_bound hw f hf hfpos hreg ha hv i hi cut hcut
      (fun γ hγ => he _ (hw.degree γ hγ) (hreg γ hγ)
        ⟨hframe γ hγ, fun j hj => hits_persistent hγ hj⟩))
  have hgap : (0 : ℚ) < ((agreement-sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt (by decide : 133500 < agreement))
  have hratio : (T.card : ℚ) ≤ ratio sites.card * D := by
    have hA : sites.card ≤ agreement := hs.trans (by decide)
    have hN : sites.card ≤ blockLength := hs.trans (by decide)
    have heq : ratio sites.card =
        ((blockLength-sites.card : ℕ) : ℚ) / ((agreement-sites.card : ℕ) : ℚ) := by
      unfold ratio
      rw [Nat.cast_sub hN,Nat.cast_sub hA] <;> rfl
    rw [heq,div_mul_eq_mul_div]
    apply (le_div_iff₀ hgap).mpr
    rw [mul_comm (T.card : ℚ)]
    exact_mod_cast hcount
  have hvle : topCap t B J ≤ totalCap t B := min_le_left _ _
  dsimp only [D] at hratio
  rw [cast_mixed (f.degreeOf_le_totalDegree 1) hvle] at hratio
  obtain ⟨hcapA,hcapV⟩ := caps_weighted (J := J) hs hB
  refine hratio.trans ?_
  unfold mix
  calc
    _ = (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) *
          (ratio sites.card * topCap t B J) +
        f.degreeOf 1 * (ratio sites.card * totalCap t B) := by ring
    _ ≤ (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * topRate B J +
        f.degreeOf 1 * totalRate B :=
      add_le_add (mul_le_mul_of_nonneg_left hcapV (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hcapA (Nat.cast_nonneg _))
    _ ≤ _ := le_add_of_nonneg_right (by decide)

theorem count {w : I → K} {T : Finset K} {S : K → K[X]} {B J : ℕ}
    (hw : FixedWord w T S 133500)
    (G : K[X]) (R : Fin 2 → K[X]) (off : ∀ i : I, G.eval (node i) ≠ 0)
    (hdegree : ResidueSpace.space G 128643 R ≤ degreeLT K 133501)
    (hframe : ∀ γ ∈ T, S γ ∈ ResidueSpace.space G 128643 R)
    (guard : ODEGuard B J) (q : ODE) (hq : ODECaps q B J)
    (hroot : ∀ γ ∈ T, fixedAt q (S γ) = 0) :
    T.card ≤ (mix B J (totalRate B) (topRate B J)).ceil.toNat + B^2 := by
  have h := fixed_bound hw guard q hq hroot (totalRate B) (topRate B J)
    (topRate_nonneg B J) (min_le_left _ _) (fun U hU =>
      count_regular
        ⟨hw.distinct.mono hU,fun γ hγ => hw.degree γ (hU hγ),fun γ hγ => hw.hits γ (hU hγ)⟩
        G R off hdegree (fun γ hγ => hframe γ (hU hγ)) guard.bmin guard.jpos)
  let r := mix B J (totalRate B) (topRate B J)
  have hceil : r ≤ (r.ceil.toNat : ℕ) := by
    have hz : r.ceil ≤ (r.ceil.toNat : ℤ) := Int.self_le_toNat _
    have hc : (r.ceil : ℚ) ≤ (r.ceil.toNat : ℚ) := by exact_mod_cast hz
    exact Rat.le_ceil.trans hc
  change T.card ≤ r.ceil.toNat + B^2
  have hfinal : (T.card : ℚ) ≤ (r.ceil.toNat : ℚ) + (B^2 : ℕ) :=
    h.trans (add_le_add hceil le_rfl)
  exact_mod_cast hfinal

#print axioms caps_weighted
#print axioms count
end H2429AffineFixedCount
