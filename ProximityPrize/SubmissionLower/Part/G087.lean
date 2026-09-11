import ProximityPrize.SubmissionLower.Part.G086


section Compact_SecondJetCombinedCount
/-! The full second-jet count for a regular irreducible carrier. All geometric
cases are included; the remaining profile-specific inequalities are numeric. -/
namespace ProximityPrize.SubmissionLower.SecondJetCombinedCount
open scoped Classical
open MvPolynomial RCN135 RCN136 RCN319 RCN327 RCN238 RCN222
open SecondJetRegularData SecondJetRegularData.Data SecondJetCoefficients
open SecondJetRelaxedInterpolation SecondJetProperAlternatives SecondJetExceptionalComponents
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {nodes : I ↪ K} {u0 u1 : I → K}

def bound (S : Data nodes u0 u1) (B U L s k n0 : ℕ) : ℕ :=
  max (S.pair (B+s*(S.r-1)) (U+s*(S.y-1)) (L+s*(S.t-1))).regularCountCap
    (S.normal+131076*((S.moving B U L k n0+k)/(k+1))+(S.pair B U L).regularCountCap)

theorem count_of_interpolant (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (P : SecondJetSupport.Poly (K := K)) (m B s U L k n0 : ℕ)
    (hP : Interpolant m B s U L k n0 nodes u0 u1 P)
    (hL : L < S.F.degreeOf 3)
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
  have halt := helper_or_divisibility P S.F m B s U L k n0 S.r S.y S.t nodes u0 u1 hP
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
    have hc := S.proper_count hI Q (B+s*(S.r-1)) (U+s*(S.y-1)) (L+s*(S.t-1))
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
    have hproper := SecondJetCoefficientAvoidance.leading_not_dvd P hP.1 S.F L
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
    have hBcount := SB.proper_count hI C B U L hrel
      (SecondJetPairBounds.leading_degree_caps P B U L hflags) hcoefficientGates hzero
    have hpartition := card_partition S.seeds point T
    have hc : S.seeds.card ≤ S.normal+131076*((S.moving B U L k n0+k)/(k+1))+
        (S.pair B U L).regularCountCap := by
      rw [hpartition]
      exact Nat.add_le_add hGcount hBcount
    exact hc.trans (le_max_right _ _)

end
end ProximityPrize.SubmissionLower.SecondJetCombinedCount

end Compact_SecondJetCombinedCount
