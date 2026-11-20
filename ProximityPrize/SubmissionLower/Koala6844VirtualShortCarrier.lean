import ProximityPrize.SubmissionLower.Koala6844VirtualShortSource
import ProximityPrize.SubmissionLower.MergedInfra6815_10
import ProximityPrize.SubmissionLower.MergedInfra6815_12
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetSupport SecondJetSpecialize SecondJetCoefficients SecondJetCoefficientSpecialization
open SecondJetClearedHelper SecondJetHelperWeights
open RCN095 RCN156 RCN234
open MovingFiberThreeSources6811 Koala6844Receipts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

variable {K : Type} [Field K]

def ProperCut (F Q : MvPolynomial (Fin 4) K) (r y t : ℕ)
    (seeds : Finset K) (selected : K → Polynomial K) : Prop :=
  IsRelPrime F Q ∧
  (wt residualSWeights Q ≤ r ∧ wt residualYSWeights Q ≤ y ∧ wt residualTotalWeights Q ≤ t) ∧
  ∀ g ∈ seeds, RCN319.specialization K (selected g) g Q = 0

theorem leading_properCut (F : MvPolynomial (Fin 4) K) (P : Poly (K := K)) (B U L : ℕ)
    (hF : Irreducible F) (hP : P ≠ 0) (hFT : L < wt residualTotalWeights F)
    (hPflag : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧ e 1+e 2+e 3+e 4 ≤ L)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hzero : ∀ g ∈ seeds, coefficientSpecialize (selected g) g (asS P).leadingCoeff = 0) :
    ProperCut F (asS P).leadingCoeff B U L seeds selected := by
  refine ⟨hF.isRelPrime_iff_not_dvd.mpr (SecondJetTotalAvoidance.leading_not_dvd P hP F L
    (fun e he => (hPflag e he).2.2) hFT).2, ?_, ?_⟩
  · have hh := derivative_coefficient_weights P B U L 0 (asS P).natDegree hPflag
    simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero,Polynomial.coeff_natDegree] at hh
    omega
  · intro g hg
    exact hzero g hg

theorem proper_cut_or_graph_source
    (F : MvPolynomial (Fin 4) K) (P : Poly (K := K)) (src : SourceShape) (r y t : ℕ)
    (hF : Irreducible F) (hP : P ≠ 0) (hFT : src.L+src.q < wt residualTotalWeights F)
    (hsB : 2*src.s ≤ src.B) (hBU : src.B ≤ src.U) (hUL : src.U ≤ src.L)
    (hks : src.k ≤ src.s) (hdn : src.k+1 ≤ src.n0) (hnB : 2*(src.n0-(src.k+1)) ≤ src.B)
    (hr : 1 ≤ r) (hy : 1 ≤ y) (ht : 1 ≤ t)
    (hFflag : wt residualSWeights F ≤ r ∧ wt residualYSWeights F ≤ y ∧ wt residualTotalWeights F ≤ t)
    (hPflag : ∀ e ∈ P.support, 2*e 1+e 3 ≤ src.B ∧ e 1 ≤ src.s ∧ e 1+e 2+e 3 ≤ src.U ∧
      e 1+e 2+e 3+e 4 ≤ src.L+src.q)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hFzero : ∀ g ∈ seeds, RCN319.specialization K (selected g) g F = 0)
    (hpartial : ∀ g ∈ seeds, ∀ d ≤ src.k,
      specialize (selected g) g ((MvPolynomial.pderiv 1)^[d] P) = 0)
    (hleading : (asS P).natDegree < src.n0 → ∀ g ∈ seeds,
      coefficientSpecialize (selected g) g (asS P).leadingCoeff = 0) :
    (∃ Q, ProperCut F Q (src.B+src.s*(r-1)) (src.U+src.s*(y-1))
      (src.L+src.q+src.s*(t-1)) seeds selected) ∨
    ∃ source : Source F, source.P = P ∧ source.d = src.k+1 ∧
      source.flag = ⟨src.graphIncrement.total,src.graphIncrement.middle,src.graphIncrement.slope⟩ ∧
      source.B = src.B ∧ source.U = src.U ∧ source.T = src.L+src.q := by
  classical
  have hflags (e : Fin 5 →₀ ℕ) (he : e ∈ P.support) :
      2*e 1+e 3 ≤ src.B ∧ e 1+e 2+e 3 ≤ src.U ∧ e 1+e 2+e 3+e 4 ≤ src.L+src.q :=
    ⟨(hPflag e he).1,(hPflag e he).2.2.1,(hPflag e he).2.2.2⟩
  have hS (e : Fin 5 →₀ ℕ) (he : e ∈ P.support) : e 1 ≤ src.s := (hPflag e he).2.1
  by_cases hn : (asS P).natDegree < src.n0
  · left
    obtain ⟨hrel,hc,hzero⟩ := leading_properCut F P src.B src.U (src.L+src.q) hF hP hFT hflags
      seeds selected (hleading hn)
    exact ⟨(asS P).leadingCoeff,hrel,⟨by omega,by omega,by omega⟩,hzero⟩
  · by_cases hdiv : ∀ j ≤ src.k, F ∣ helper P F (src.s-j) j
    · right
      let S : Source F := ⟨P,src.B,src.U,src.L+src.q,src.s,src.k,src.n0,
        hS,hflags,hBU,by omega,hdn,hnB,Nat.le_of_not_gt hn,hdiv⟩
      exact ⟨S,rfl,rfl,rfl,rfl,rfl,rfl⟩
    · left
      push Not at hdiv
      obtain ⟨j,hj,hproper⟩ := hdiv
      refine ⟨helper P F (src.s-j) j,hF.isRelPrime_iff_not_dvd.mpr hproper,?_,?_⟩
      · have hw := helper_weights P F src.B src.U (src.L+src.q) src.s j t y r hsB
          (by omega) (by omega) (hj.trans hks) hr hy ht hflags hFflag
        have h₁ := Nat.mul_le_mul_right (r-1) (Nat.sub_le src.s j)
        have h₂ := Nat.mul_le_mul_right (y-1) (Nat.sub_le src.s j)
        have h₃ := Nat.mul_le_mul_right (t-1) (Nat.sub_le src.s j)
        exact ⟨by omega,by omega,by omega⟩
      · intro g hg
        exact helper_vanish P F (src.s-j) j (asS_derivative_degree P src.s j hS)
          (selected g) g (hFzero g hg) (hpartial g hg j hj)

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
