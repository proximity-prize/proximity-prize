import ProximityPrize.SubmissionLower.HigherRootOwnShape6810P2
import ProximityPrize.SubmissionLower.HigherRootRegularData6810P2
import ProximityPrize.SubmissionLower.HigherRootTotalAvoidance6810
import ProximityPrize.SubmissionLower.HigherRootInterpolation6810
import ProximityPrize.SubmissionLower.HigherRootLeadingCoefficient6810

namespace ProximityPrize.SubmissionLower.HigherRootRegularData6810P2.Data
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
      (show (262144 - 181294 : ℕ) = 80850 by decide),RCN327.w] using S.noPencil)
    S.solution S.regular hzero
  exact SecondJetPairBounds.count_le_left_cap (S.pair R capY T) S.F hF.1 hF.2.1 hF.2.2
    S.seeds.card (by change 0 < (181294 - 131071 : ℕ); decide) hcount

end
end ProximityPrize.SubmissionLower.HigherRootRegularData6810P2.Data



namespace ProximityPrize.SubmissionLower.HigherRootAsymmetric6810P2
open scoped Classical
open MvPolynomial RCN135 RCN136 RCN319 RCN327 RCN238 RCN222 RCN234 RCN156
open HigherRootRegularData6810P2 HigherRootRegularData6810P2.Data SecondJetCoefficients
open HigherRootInterpolation6810 HigherRootTotalAvoidance6810 SecondJetExceptionalComponents
open AsymmetricHelper
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {nodes : I ↪ K} {u0 u1 : I → K}

def bound (S : Data nodes u0 u1) : ℕ :=
  max (leftRegularCountCap (S.pair (56+25*(S.r-1)) (185+25*(S.y-1)) (2526+25*(S.t-1))))
    (S.dual / 49 + leftRegularCountCap (S.pair 56 185 2526))

theorem count_of_interpolant_total (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (P : SecondJetSupport.Poly (K := K))
    (hP : Interpolant 136 56 25 185 2526 6 8 nodes u0 u1 P)
    (hL : 2526 < wt residualTotalWeights S.F)
    (hfact : ∀ d ≤ 25, (d.factorial : K) ≠ 0)
    (h2 : (2 : GenericField K) ≠ 0) (hfactG : ((6).factorial : GenericField K) ≠ 0)
    (hhelperGates : S.PairGates (56+25*(S.r-1)) (185+25*(S.y-1)) (2526+25*(S.t-1)))
    (hcoefficientGates : S.PairGates 56 185 2526) :
    S.seeds.card ≤ bound S := by
  have hflags : ∀ e ∈ P.support, 2*e 1+e 3 ≤ 56 ∧ e 1+e 2+e 3 ≤ 185 ∧
      e 1+e 2+e 3+e 4 ≤ 2526 := fun e he =>
    ⟨(hP.2.1 e he).1,(hP.2.1 e he).2.2.1,(hP.2.1 e he).2.2.2.1⟩
  have hS : ∀ e ∈ P.support, e 1 ≤ 25 := fun e he => (hP.2.1 e he).2.1
  have halt := HigherRootTotalAvoidance6810.helper_or_divisibility P S.F 136 56 25 185 2526 6 8 S.r S.y S.t nodes u0 u1 hP
    S.irreducible hL (by decide) (by decide) (by decide) (by decide) (by decide)
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
    have hc := S.proper_count_left hI Q (56+25*(S.r-1)) (185+25*(S.y-1)) (2526+25*(S.t-1))
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
    have hscaled := SG.retained_dual hI P hS hflags hn hdiv h2 hfactG hgood
    have hGcount : Good.card ≤ S.dual / 49 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 49)).mpr
      simpa only [SG, Data.dual, Data.restrict, Nat.mul_comm] using hscaled
    have hproper := SecondJetTotalAvoidance.leading_not_dvd P hP.1 S.F 2526
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
    have hBcount := SB.proper_count_left hI C 56 185 2526 hrel
      (SecondJetPairBounds.leading_degree_caps P 56 185 2526 hflags) hcoefficientGates hzero
    have hpartition := card_partition S.seeds point T
    have hc : S.seeds.card ≤ S.dual / 49+
        leftRegularCountCap (S.pair 56 185 2526) := by
      rw [hpartition]
      exact Nat.add_le_add hGcount hBcount
    exact hc.trans (le_max_right _ _)


end
end ProximityPrize.SubmissionLower.HigherRootAsymmetric6810P2
