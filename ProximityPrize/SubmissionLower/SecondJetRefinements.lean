import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.SecondJetTotalAvoidance
open MvPolynomial SecondJetSupport SecondJetCoefficients RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {K : Type*} [Field K]

/-- A coefficient loses one unit of residual total weight per S power. -/
theorem coefficient_total_weight (P : Poly (K := K)) (L j : ℕ)
    (hP : ∀ e ∈ P.support, e 1+e 2+e 3+e 4 ≤ L) :
    wt residualTotalWeights ((asS P).coeff j) ≤ L-j := by
  apply (RCN081.weightedTotalDegree_le_iff _ _ _).mpr
  intro e he
  have hh := hP _ (coefficient_support P j e he)
  obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates j e
  rw [h1,h2,h3,h4] at hh
  simp [residualTotalWeights, RCN081.weight_fin4]
  omega

theorem coefficient_not_dvd (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (L j : ℕ) (hP : ∀ e ∈ P.support, e 1+e 2+e 3+e 4 ≤ L)
    (hF : L < wt residualTotalWeights F) (hC : (asS P).coeff j ≠ 0) :
    ¬ F ∣ (asS P).coeff j := by
  intro hdiv
  have hh := RCN081.weightedTotalDegree_le_of_dvd residualTotalWeights F
    ((asS P).coeff j) hdiv hC
  have hc := coefficient_total_weight P L j hP
  change wt residualTotalWeights F ≤ wt residualTotalWeights ((asS P).coeff j) at hh
  omega

theorem leading_not_dvd (P : Poly (K := K)) (hP : P ≠ 0)
    (F : MvPolynomial (Fin 4) K) (L : ℕ)
    (hPL : ∀ e ∈ P.support, e 1+e 2+e 3+e 4 ≤ L)
    (hF : L < wt residualTotalWeights F) :
    (asS P).leadingCoeff ≠ 0 ∧ ¬ F ∣ (asS P).leadingCoeff := by
  have hn : asS P ≠ 0 := by
    intro hz
    apply hP
    apply (asS (K := K)).injective
    simpa only [map_zero] using hz
  have hc := Polynomial.leadingCoeff_ne_zero.mpr hn
  exact ⟨hc,coefficient_not_dvd P F L (asS P).natDegree hPL hF hc⟩

open SecondJetCoefficientSpecialization SecondJetClearedHelper SecondJetHelperWeights
open SecondJetRelaxedInterpolation SecondJetRelaxedCoefficientsReceipt SecondJetProperAlternatives
variable {N : Type*} [Fintype N]

theorem helper_or_divisibility (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (m B s U L k n0 capR capY capT : ℕ)
    (nodes : N ↪ K) (u0 u1 : N → K)
    (hP : Interpolant m B s U L k n0 nodes u0 u1 P)
    (hFi : Irreducible F) (hFT : L < wt residualTotalWeights F)
    (hsB : 2*s ≤ B) (hsU : s ≤ U) (hsL : s ≤ L) (hks : k ≤ s) (hsm : s < m)
    (hR : 1 ≤ capR) (hY : 1 ≤ capY) (hT : 1 ≤ capT)
    (hF : wt residualSWeights F ≤ capR ∧ wt residualYSWeights F ≤ capY ∧
      wt residualTotalWeights F ≤ capT)
    (hfact : ∀ d ≤ s, (d.factorial : K) ≠ 0) :
    (∃ Q, ProperHelper F Q B U L s capR capY capT nodes u0 u1) ∨
      (n0 ≤ (asS P).natDegree ∧ ∀ d ≤ k, F ∣ helper P F (s-d) d) := by
  classical
  have hflags : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L := by
    intro e he
    have h := hP.2.1 e he
    exact ⟨h.1,h.2.2.1,h.2.2.2.1⟩
  have hS : ∀ e ∈ P.support, e 1 ≤ s := fun e he => (hP.2.1 e he).2.1
  have hdegree : (asS P).natDegree ≤ s := by
    simpa using asS_derivative_degree P s 0 hS
  by_cases hn : (asS P).natDegree < n0
  · left
    let n := (asS P).natDegree
    let Q := (asS P).leadingCoeff
    have hQ := SecondJetTotalAvoidance.leading_not_dvd P hP.1 F L
      (fun e he => (hflags e he).2.2) hFT
    refine ⟨Q,hFi.isRelPrime_iff_not_dvd.mpr hQ.2,?_,?_⟩
    · have hw := derivative_coefficient_weights P B U L 0 n hflags
      simp only [Function.iterate_zero, id_eq, Nat.mul_zero, Nat.sub_zero] at hw
      change wt residualSWeights ((asS P).coeff n) ≤ B+s*(capR-1) ∧
        wt residualYSWeights ((asS P).coeff n) ≤ U+s*(capY-1) ∧
        wt residualTotalWeights ((asS P).coeff n) ≤ L+s*(capT-1)
      omega
    · intro f hf z S hSc hvalues _hFzero
      have hweight : ∀ e ∈ P.support,
          e 0+131071*e 2+131070*e 3+131069*e 1+
            SecondJetRelaxedDifferentiation.reserve k n0 (e 1)*50284 < m*181353 := by
        intro e he
        have hw := (hP.2.1 e he).2.2.2.2
        dsimp [cutoff] at hw
        omega
      apply SecondJetLeadingCoefficient.low_coefficient_vanish P m k n0 n
        (by dsimp [n]; omega) hn (hfact n hdegree) hweight nodes u0 u1 hP.2.2.1
        f hf z S hSc hvalues
      intro j hj
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj,map_zero]
  · by_cases hdiv : ∀ d ≤ k, F ∣ helper P F (s-d) d
    · exact Or.inr ⟨Nat.le_of_not_gt hn,hdiv⟩
    · left
      push_neg at hdiv
      obtain ⟨d,hd,hproper⟩ := hdiv
      refine ⟨helper P F (s-d) d,hFi.isRelPrime_iff_not_dvd.mpr hproper,?_,?_⟩
      · have hw := helper_weights P F B U L s d capT capY capR hsB hsU hsL
          (hd.trans hks) hR hY hT hflags hF
        have hr := Nat.mul_le_mul_right (capR-1) (Nat.sub_le s d)
        have hy := Nat.mul_le_mul_right (capY-1) (Nat.sub_le s d)
        have ht := Nat.mul_le_mul_right (capT-1) (Nat.sub_le s d)
        omega
      · intro f hf z S hSc hvalues hFzero
        exact helper_vanish P F (s-d) d (asS_derivative_degree P s d hS) f z hFzero
          (hP.2.2.2 d hd f hf z S hSc hvalues)


end
end ProximityPrize.SubmissionLower.SecondJetTotalAvoidance

namespace ProximityPrize.SubmissionLower.SecondJetPairBounds
open RCN260 RCN052 RCN294

/-- The regular-seed inequality only needs the carrier's agreement vector. -/
theorem count_le_left_cap {K : Type} [Field K]
    (P : UnequalParameters) (F : MvPolynomial (Fin 4) K)
    (hY : F.degreeOf 1 ≤ P.leftY) (hR : F.degreeOf 2 ≤ P.leftR)
    (hZ : F.degreeOf 3 ≤ P.leftZ) (count : ℕ) (hgap : 0 < P.gap)
    (hc : count*P.gap ≤ (P.n-P.w)*dot P.leftAgreement (regularVector P F)+
      (P.errors+1)*P.gap*(regularVector P F).z) :
    count ≤ AsymmetricHelper.leftRegularCountCap P := by
  have hv := LocatorCoprimeQuotient.regularVector_le_mixedCost P F hY hR hZ
  have hdot : dot P.leftAgreement (regularVector P F) ≤ dot P.leftAgreement P.mixedCost :=
    Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left P.leftAgreement.y hv.1)
        (Nat.mul_le_mul_left P.leftAgreement.r hv.2.1))
      (Nat.mul_le_mul_left P.leftAgreement.z hv.2.2)
  apply (Nat.le_div_iff_mul_le hgap).mpr
  exact hc.trans (Nat.add_le_add (Nat.mul_le_mul_left (P.n-P.w) hdot)
    (Nat.mul_le_mul_left ((P.errors+1)*P.gap) hv.2.2))

end ProximityPrize.SubmissionLower.SecondJetPairBounds

namespace ProximityPrize.SubmissionLower.SecondJetRegularData.Data
open MvPolynomial RCN319 RCN260 RCN327
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {nodes : I ↪ K} {u0 u1 : I → K}

theorem proper_count_left (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (Q : MvPolynomial (Fin 4) K) (R capY T : ℕ) (hrel : IsRelPrime S.F Q)
    (hQ : Q.degreeOf 1 ≤ capY ∧ Q.degreeOf 2 ≤ R ∧ Q.degreeOf 3 ≤ T)
    (hgates : S.PairGates R capY T)
    (hzero : ∀ gamma ∈ S.seeds, specialization K (S.selected gamma) gamma Q=0) :
    S.seeds.card ≤ AsymmetricHelper.leftRegularCountCap (S.pair R capY T) := by
  have hF := SecondJetPairBounds.degree_caps_of_weights S.F S.r S.y S.t S.weights
  have hcount := SecondJetProperCounting.regular_seed_bound_left
    (S.pair R capY T) S.F Q S.irreducible S.rdegree hrel 2130706433
    hF.1 hF.2.1 hF.2.2 hQ.1 hQ.2.1 hQ.2.2 (by have := S.rpos; dsimp [pair]; omega)
    (by have := S.ybound; dsimp [pair]; omega)
    (by have := S.rbound; dsimp [pair]; omega)
    (by have := S.tbound; dsimp [pair]; omega)
    hgates.1 hgates.2.1 hgates.2.2 S.selected S.seeds Finset.univ nodes u0 u1
    nodes.injective.injOn (by simpa only [Finset.card_univ,pair] using hI)
    (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair])
    S.degree S.agreement (by simpa only [pair,UnequalParameters.errors,
      (show (262144 - 181353 : ℕ) = 80791 by decide),RCN327.w] using S.noPencil)
    S.solution S.regular hzero
  exact SecondJetPairBounds.count_le_left_cap (S.pair R capY T) S.F hF.1 hF.2.1 hF.2.2
    S.seeds.card (by change 0 < (181353 - 131071 : ℕ); decide) hcount

end
end ProximityPrize.SubmissionLower.SecondJetRegularData.Data

namespace ProximityPrize.SubmissionLower.SecondJetAsymmetric
open scoped Classical
open MvPolynomial RCN135 RCN136 RCN319 RCN327 RCN238 RCN222 RCN234 RCN156
open SecondJetRegularData SecondJetRegularData.Data SecondJetCoefficients
open SecondJetRelaxedInterpolation SecondJetProperAlternatives SecondJetExceptionalComponents
open AsymmetricHelper
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {nodes : I ↪ K} {u0 u1 : I → K}

def bound (S : Data nodes u0 u1) (B U L s k n0 : ℕ) : ℕ :=
  max (leftRegularCountCap (S.pair (B+s*(S.r-1)) (U+s*(S.y-1)) (L+s*(S.t-1))))
    (S.normal+131076*((S.moving B U L k n0+k)/(k+1))+leftRegularCountCap (S.pair B U L))

omit [CharP K 2130706433] in
theorem bound_le_symmetric (S : Data nodes u0 u1) (B U L s k n0 : ℕ) :
    bound S B U L s k n0 ≤ SecondJetCombinedCount.bound S B U L s k n0 := by
  apply max_le_max
  · exact Nat.div_le_div_right (leftRegularNumerator_le _)
  · exact Nat.add_le_add_left (Nat.div_le_div_right (leftRegularNumerator_le _)) _

theorem count_of_interpolant_total (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (P : SecondJetSupport.Poly (K := K)) (m B s U L k n0 : ℕ)
    (hP : Interpolant m B s U L k n0 nodes u0 u1 P)
    (hL : L < wt residualTotalWeights S.F)
    (hsB : 2*s ≤ B) (hsU : s ≤ U) (hsL : s ≤ L) (hks : k ≤ s) (hsm : s < m)
    (hBU : B ≤ U) (hUL : U ≤ L) (hdn : k+1 ≤ n0) (hB : 2*(n0-(k+1)) ≤ B)
    (hfact : ∀ d ≤ s, (d.factorial : K) ≠ 0)
    (h2 : (2 : GenericField K) ≠ 0) (hfactG : (k.factorial : GenericField K) ≠ 0)
    (hhelperGates : S.PairGates (B+s*(S.r-1)) (U+s*(S.y-1)) (L+s*(S.t-1)))
    (hcoefficientGates : S.PairGates B U L) :
    S.seeds.card ≤ bound S B U L s k n0 := by
  have hflags : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L := fun e he =>
    ⟨(hP.2.1 e he).1,(hP.2.1 e he).2.2.1,(hP.2.1 e he).2.2.2.1⟩
  have hS : ∀ e ∈ P.support, e 1 ≤ s := fun e he => (hP.2.1 e he).2.1
  have halt := SecondJetTotalAvoidance.helper_or_divisibility P S.F m B s U L k n0 S.r S.y S.t nodes u0 u1 hP
    S.irreducible hL hsB hsU hsL hks hsm
    (by have := S.rpos; omega) (by have := S.ry; omega) (by have := S.yt; omega)
    S.weights hfact
  rcases halt with ⟨Q,hQ⟩ | ⟨hn,hdiv⟩
  · have hzero : ∀ gamma ∈ S.seeds, specialization K (S.selected gamma) gamma Q = 0 := by
      intro gamma hgamma
      apply hQ.2.2 (S.selected gamma) (S.degree gamma hgamma) gamma
        (Finset.univ.filter (fun i => (S.selected gamma).eval (nodes i)=u0 i+gamma*u1 i))
        (S.agreement gamma hgamma) ?_ (S.solution gamma hgamma)
      intro i hi
      simpa only [mul_comm] using (Finset.mem_filter.mp hi).2
    have hc := S.proper_count_left hI Q (B+s*(S.r-1)) (U+s*(S.y-1)) (L+s*(S.t-1))
      hQ.1 (SecondJetPairBounds.degree_caps_of_weights Q _ _ _ hQ.2.1) hhelperGates hzero
    exact hc.trans (le_max_left _ _)
  · let C := (asS P).leadingCoeff
    let point := RCN238.selectedPoint (polynomialEmbedding K) S.selected
    let T := surfaceMap (polynomialEmbedding K) C
    let Good := goodSeeds S.seeds point T
    let Bad := exceptionalSeeds S.seeds point T
    have hgoodSub : Good ⊆ S.seeds := Finset.filter_subset _ _
    have hbadSub : Bad ⊆ S.seeds := Finset.filter_subset _ _
    let SG := S.restrict Good hgoodSub
    let SB := S.restrict Bad hbadSub
    have hgood : ∀ gamma ∈ SG.seeds,
        MvPolynomial.eval (RCN238.selectedPoint (polynomialEmbedding K) SG.selected gamma)
          (surfaceMap (polynomialEmbedding K) (asS P).leadingCoeff) ≠ 0 := by
      intro gamma hgamma
      exact (Finset.mem_filter.mp hgamma).2
    have hscaled := SG.retained_scaled hI P B U L s k n0 hS hflags hBU hUL hdn hB hn hdiv h2 hfactG hgood
    have hGcount := SecondJetRounding.count_le Good.card S.normal (S.moving B U L k n0) 131076 k hscaled
    have hproper := SecondJetTotalAvoidance.leading_not_dvd P hP.1 S.F L
      (fun e he => (hflags e he).2.2) hL
    have hrel : IsRelPrime SB.F C := S.irreducible.isRelPrime_iff_not_dvd.mpr hproper.2
    have hzero : ∀ gamma ∈ SB.seeds, specialization K (SB.selected gamma) gamma C = 0 := by
      intro gamma hgamma
      have hz : MvPolynomial.eval (point gamma) T = 0 := (Finset.mem_filter.mp hgamma).2
      change MvPolynomial.eval (RCN238.selectedPoint (polynomialEmbedding K) S.selected gamma)
        (surfaceMap (polynomialEmbedding K) C)=0 at hz
      rw [selectedPoint_surface_evaluation] at hz
      change specialization K (S.selected gamma) gamma C = 0
      exact (polynomialEmbedding_injective K) (by simpa only [map_zero] using hz)
    have hBcount := SB.proper_count_left hI C B U L hrel
      (SecondJetPairBounds.leading_degree_caps P B U L hflags) hcoefficientGates hzero
    have hpartition := card_partition S.seeds point T
    have hc : S.seeds.card ≤ S.normal+131076*((S.moving B U L k n0+k)/(k+1))+
        leftRegularCountCap (S.pair B U L) := by
      rw [hpartition]
      exact Nat.add_le_add hGcount hBcount
    exact hc.trans (le_max_right _ _)

def numericBound (r v z B U L s k n0 : ℕ) : ℕ :=
  max (leftRegularCountCap (SecondJetNumericGeometry.properParameters r v z B U L s))
    (SecondJetNumericGeometry.normal r v z+
      131076*((SecondJetAffineCeiling.moving r v z
        (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0)+k)/(k+1))+
      leftRegularCountCap (SecondJetNumericGeometry.parameters r (r+v) (r+v+z) B U L))

theorem bound_eq_numeric (S : Data nodes u0 u1) (hown : SecondJetOwnShape.Own S)
    (B U L s k n0 : ℕ) :
    bound S B U L s k n0 = numericBound S.r (S.y-S.r) (S.t-S.y) B U L s k n0 := by
  have hy : S.r+(S.y-S.r) = S.y := by have := S.ry; omega
  have ht : S.y+(S.t-S.y) = S.t := by have := S.yt; omega
  unfold bound numericBound
  rw [SecondJetOwnShape.normal_eq S hown, SecondJetSingleCap.moving_eq S hown]
  simp only [SecondJetNumericGeometry.properParameters, SecondJetNumericGeometry.parameters,
    Data.pair, hy, ht]

theorem profile114_binding_value :
    numericBound 10 37 2276 47 155 2255 21 5 7 = 268923679246212987 := by
  decide

end
end ProximityPrize.SubmissionLower.SecondJetAsymmetric


namespace ProximityPrize.SubmissionLower.SecondJetOwnShape
open MvPolynomial RCN130 RCN234 RCN156 RCN095 RCN347 RCN135
open SecondJetRegularData SecondJetRegularData.Data
noncomputable section
set_option autoImplicit false
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

theorem total_weight_eq (S : Data nodes u0 u1) (hown : Own S) :
    wt residualTotalWeights S.F = S.t := by
  have h := (originalCumulativeFlag_cumulative S.F).2.2
  rw [hown] at h
  dsimp only at h
  have := S.ry
  have := S.yt
  omega

theorem avoidance_total (S : Data nodes u0 u1) (hown : Own S) (L : ℕ) (hL : L < S.t) :
    L < wt residualTotalWeights S.F := by
  rwa [total_weight_eq S hown]

end
end ProximityPrize.SubmissionLower.SecondJetOwnShape

namespace ProximityPrize.SubmissionLower.SecondJetProfile114
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts SecondJetRelaxedCounts
open SecondJetRelaxedCoefficientsReceipt SecondJetRelaxedInterpolation
open SecondJetNumericGeometry RCN260 RCN294 RCN135
open SecondJetRegularData SecondJetRegularData.Data SecondJetOwnShape
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem coefficient_count :
    coefficientCount (cutoff 114 5 7) 131071 2255 47 21 155 = 1521555139747342 := by
  decide

theorem local_rank : rankBound 114 2255 47 21 155 = 5804271999 := by
  decide

theorem cutoff_caps : ∀ h : Fin 22, 155 ≤ (cutoff 114 5 7 h.val+47-1)/131071 := by
  decide

theorem source_card :
    Fintype.card (Index (cutoff 114 5 7) 131071 2255 47 21 155) = 1521555139747342 := by
  rw [card_index_closed _ _ _ _ _ _ (by decide), coefficient_count]

theorem exact_rank :
    SecondJetRelaxedGlobalMap.rankBound 114 2255 47 21 155
      (fun h => (cutoff 114 5 7 h+47-1)/131071) = 5804271999 := by
  rw [rankBound_eq_closed _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
    (fun h hh => cutoff_caps ⟨h,by omega⟩), local_rank]

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433

theorem exists_interpolant (hI : Fintype.card I = 262144) :
    ∃ P, Interpolant 114 47 21 155 2255 5 7 nodes u0 u1 P := by
  apply exists_of_dimension _ _ _ _ _ _ _ (by decide) (by decide) hI nodes u0 u1
  rw [exact_rank, source_card]
  decide

theorem uniform_gates (r y t R U T : ℕ)
    (hr : r ≤ 30) (hy : y ≤ 136) (ht : t ≤ 6917)
    (hR : R ≤ 656) (hU : U ≤ 2990) (hT : T ≤ 147491) :
    (parameters r y t R U T).mixedCost.y < 2130706433 ∧
    (parameters r y t R U T).mixedCost.r < 2130706433 ∧
    (parameters r y t R U T).mixedCost.z < 2130706433 := by
  have h := mixed_mono hr hy ht hR hU hT
  exact ⟨h.1.trans_lt (by norm_num [parameters,UnequalParameters.mixedCost]),
    h.2.1.trans_lt (by norm_num [parameters,UnequalParameters.mixedCost]),
    h.2.2.trans_lt (by norm_num [parameters,UnequalParameters.mixedCost])⟩

theorem helper_gates (S : Data nodes u0 u1) :
    S.PairGates (47+21*(S.r-1)) (155+21*(S.y-1)) (2255+21*(S.t-1)) := by
  apply uniform_gates _ _ _ _ _ _ S.rbound S.ybound S.tbound
  · have := S.rbound
    omega
  · have := S.ybound
    omega
  · have := S.tbound
    omega

theorem coefficient_gates (S : Data nodes u0 u1) : S.PairGates 47 155 2255 :=
  uniform_gates _ _ _ _ _ _ S.rbound S.ybound S.tbound (by decide) (by decide) (by decide)

theorem count_114 (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (hown : Own S) (hL : 2255 < S.t) :
    S.seeds.card ≤ SecondJetAsymmetric.numericBound S.r (S.y-S.r) (S.t-S.y)
      47 155 2255 21 5 7 := by
  obtain ⟨P,hP⟩ := exists_interpolant (nodes := nodes) (u0 := u0) (u1 := u1) hI
  have hc := SecondJetAsymmetric.count_of_interpolant_total S hI P 114 47 21 155 2255 5 7 hP
    (avoidance_total S hown _ hL)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun d hd => factorial_ne (K := K) d (by omega))
    (two_ne (K := GenericField K)) (factorial_ne (K := GenericField K) 5 (by decide))
    (helper_gates S) (coefficient_gates S)
  rwa [SecondJetAsymmetric.bound_eq_numeric S hown] at hc

end
end ProximityPrize.SubmissionLower.SecondJetProfile114

namespace ProximityPrize.SubmissionLower.SecondJetRefinedCap
open RCN095 RCN260 RCN294 AsymmetricHelper SecondJetNumericGeometry
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def pairNumerator (r v z B U L s : ℕ) : ℕ :=
  leftRegularNumerator (properParameters r v z B U L s)

def pairSlope (r v B U s : ℕ) : ℕ :=
  let rightR := B+s*(r-1)
  let rightY := U+s*(r+v-1)
  131073*((1+262142*(r+v))*(r*s+rightR)+131071*(2*r-1)*((r+v)*s+rightY)+
    262142*((r+v)*rightR+r*rightY))

theorem pairNumerator_add (r v z h B U L s : ℕ) (hr : 1 ≤ r) :
    pairNumerator r v (z+h) B U L s = pairNumerator r v z B U L s+
      h*pairSlope r v B U s := by
  have hs : r+v+(z+h)-1 = (r+v+z-1)+h := by omega
  simp only [pairNumerator,pairSlope,properParameters,leftRegularNumerator,
    UnequalParameters.leftAgreement,UnequalParameters.mixedCost,UnequalParameters.errors,
    UnequalParameters.gap,dot]
  rw [hs]
  ring

def start (r v : ℕ) : ℕ := 2256-(r+v)

def properValue (r v : ℕ) : ℕ :=
  (pairNumerator r v (start r v) 47 155 2255 21+50281)/50282

def properSlope (r v : ℕ) : ℕ := (pairSlope r v 47 155 21+50281)/50282

def coefficientValue (r v : ℕ) : ℕ :=
  (pairNumerator r v (start r v) 47 155 2255 0+50281)/50282

def coefficientSlope (r v : ℕ) : ℕ := (pairSlope r v 47 155 0+50281)/50282

def retainedValue (r v : ℕ) : ℕ :=
  normal r v (start r v)+
    131076*((SecondJetAffineCeiling.moving r v (start r v)
      (SecondJetRelaxedFlag.budgetFlag 47 155 2255 6 7)+5)/6)+coefficientValue r v

def retainedSlope (r v : ℕ) : ℕ :=
  (normal r v 1-normal r v 0)+
    131076*((SecondJetAffineCeiling.movingSlope r v
      (SecondJetRelaxedFlag.budgetFlag 47 155 2255 6 7)+5)/6)+coefficientSlope r v

def properLine (r v z : ℕ) : ℕ := properValue r v+properSlope r v*(z-start r v)

def retainedLine (r v z : ℕ) : ℕ := retainedValue r v+retainedSlope r v*(z-start r v)

/-- Both possible geometric branches remain explicitly charged. -/
def profile (r v z : ℕ) : ℕ := max (properLine r v z) (retainedLine r v z)

def activated (p : FlagDegree) : ℕ :=
  if 3 ≤ p.all ∧ 2 ≤ p.yz ∧ 2 ≤ p.zOnly ∧ 2255 < p.all+p.yz+p.zOnly then
    profile p.all p.yz p.zOnly
  else SecondJetSingleCap.cap p

def cap (p : FlagDegree) : ℕ := min (SecondJetSingleCap.cap p) (activated p)

theorem cap_le_old (p : FlagDegree) : cap p ≤ SecondJetSingleCap.cap p := min_le_left _ _

theorem pairCount_le_line (r v z B U L s : ℕ) (hr : 1 ≤ r)
    (hz : start r v ≤ z) :
    leftRegularCountCap (properParameters r v z B U L s) ≤
      (pairNumerator r v (start r v) B U L s+50281)/50282+
      ((pairSlope r v B U s+50281)/50282)*(z-start r v) := by
  have he : z = start r v+(z-start r v) := by omega
  unfold leftRegularCountCap
  rw [show (properParameters r v z B U L s).gap = 50282 by
    norm_num [properParameters,UnequalParameters.gap]]
  change pairNumerator r v z B U L s / 50282 ≤ _
  have hp := pairNumerator_add r v (start r v) (z-start r v) B U L s hr
  rw [←he] at hp
  rw [hp]
  have h := SecondJetAffineCeiling.ceil_add_mul_le
    (pairNumerator r v (start r v) B U L s) (pairSlope r v B U s)
    (z-start r v) 50281
  have hl := Nat.div_le_div_right (c := 50282)
    (Nat.le_add_right (pairNumerator r v (start r v) B U L s+
      (z-start r v)*pairSlope r v B U s) 50281)
  simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel, Nat.mul_comm] using hl.trans h

theorem numericBound_le_profile (r v z : ℕ) (hr : 1 ≤ r) (hz : start r v ≤ z) :
    SecondJetAsymmetric.numericBound r v z 47 155 2255 21 5 7 ≤ profile r v z := by
  apply max_le_max
  · exact pairCount_le_line r v z 47 155 2255 21 hr hz
  · have hc := pairCount_le_line r v z 47 155 2255 0 hr hz
    have he : z = start r v+(z-start r v) := by omega
    have hm := SecondJetAffineCeiling.moving_ceil_add_le r v (start r v)
      (z-start r v) 5 (SecondJetRelaxedFlag.budgetFlag 47 155 2255 6 7)
    have hn := SecondJetSingleCap.normal_add r v (start r v) (z-start r v)
    rw [←he] at hm hn
    simp only [properParameters,Nat.zero_mul,Nat.add_zero] at hc
    change leftRegularCountCap (parameters r (r+v) (r+v+z) 47 155 2255) ≤
      coefficientValue r v+coefficientSlope r v*(z-start r v) at hc
    change normal r v z+131076*((SecondJetAffineCeiling.moving r v z
      (SecondJetRelaxedFlag.budgetFlag 47 155 2255 6 7)+5)/6)+
      leftRegularCountCap (parameters r (r+v) (r+v+z) 47 155 2255) ≤ retainedLine r v z
    rw [hn]
    have h := Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 131076 hm)
      (normal r v (start r v)+(z-start r v)*(normal r v 1-normal r v 0))) hc
    apply h.trans_eq
    simp only [retainedLine,retainedValue,retainedSlope]
    ring

theorem properLine_affine (r v lo z : ℕ) (hlo : start r v ≤ lo) (hz : lo ≤ z) :
    properLine r v z = properLine r v lo+properSlope r v*(z-lo) := by
  have h : z-start r v = (lo-start r v)+(z-lo) := by omega
  simp only [properLine,h]
  ring

theorem retainedLine_affine (r v lo z : ℕ) (hlo : start r v ≤ lo) (hz : lo ≤ z) :
    retainedLine r v z = retainedLine r v lo+retainedSlope r v*(z-lo) := by
  have h : z-start r v = (lo-start r v)+(z-lo) := by omega
  simp only [retainedLine,h]
  ring

theorem profile_le_between (r v lo hi z : ℕ) (g : ℕ → ℕ) (slope : ℕ)
    (hstart : start r v ≤ lo) (hz : lo ≤ z) (hzi : z ≤ hi)
    (hg : ∀ zz, lo ≤ zz → zz ≤ hi → g zz = g lo+slope*(zz-lo))
    (h0 : profile r v lo ≤ g lo) (h1 : profile r v hi ≤ g hi) :
    profile r v z ≤ g z := by
  have hlo : lo ≤ hi := hz.trans hzi
  rw [hg z hz hzi]
  apply max_le
  · rw [properLine_affine r v lo z hstart hz]
    have hlast := (le_max_left (properLine r v hi) (retainedLine r v hi)).trans h1
    rw [properLine_affine r v lo hi hstart hlo, hg hi hlo le_rfl] at hlast
    exact Lower80791.PhaseRows.affine_le_between _ _ _ _ _ _
      (Nat.sub_le_sub_right hzi lo) ((le_max_left _ _).trans h0) hlast
  · rw [retainedLine_affine r v lo z hstart hz]
    have hlast := (le_max_right (properLine r v hi) (retainedLine r v hi)).trans h1
    rw [retainedLine_affine r v lo hi hstart hlo, hg hi hlo le_rfl] at hlast
    exact Lower80791.PhaseRows.affine_le_between _ _ _ _ _ _
      (Nat.sub_le_sub_right hzi lo) ((le_max_right _ _).trans h0) hlast

end ProximityPrize.SubmissionLower.SecondJetRefinedCap

namespace ProximityPrize.SubmissionLower.SecondJetRefinedCap
open RCN130 RCN234 RCN156 RCN347 SecondJetRegularData SecondJetRegularData.Data SecondJetOwnShape
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

theorem count_114 (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (hown : Own S) (hL : 2255 < S.t) :
    S.seeds.card ≤ profile S.r (S.y-S.r) (S.t-S.y) := by
  have hs : start S.r (S.y-S.r) ≤ S.t-S.y := by
    have := S.ry
    have := S.yt
    unfold start
    omega
  exact (SecondJetProfile114.count_114 S hI hown hL).trans
    (numericBound_le_profile _ _ _ (by have := S.rpos; omega) hs)

theorem count_le_cap (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (hown : Own S)
    (hold : S.seeds.card ≤ SecondJetSingleCap.cap (originalCumulativeFlag S.F)) :
    S.seeds.card ≤ cap (originalCumulativeFlag S.F) := by
  apply le_min hold
  unfold activated
  rw [hown]
  dsimp only
  have ht : S.r+(S.y-S.r)+(S.t-S.y) = S.t := by
    have := S.ry
    have := S.yt
    omega
  rw [ht]
  split
  · rename_i ha
    exact count_114 S hI hown ha.2.2.2
  · rw [hown] at hold
    exact hold

end
end ProximityPrize.SubmissionLower.SecondJetRefinedCap
