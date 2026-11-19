/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- 68.33 terminal specialization, derived from Lucieno PR 618, BitWonka PR 581 and Bome2017’s accepted 68.32 proof. Apache-2.0. -/
import ProximityPrize.SubmissionLower.K6833TerminalInterpolants
import ProximityPrize.SubmissionLower.MergedInfra6815_12
import ProximityPrize.SubmissionLower.MergedInfra6815_18

set_option Elab.async false

namespace ProximityPrize.SubmissionLower.K6833Residual

open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetSpecialize
open SecondJetCoefficients SecondJetCoefficientSpecialization SecondJetDifferentiation
open SecondJetRelaxedDifferentiation SecondJetClearedHelper SecondJetHelperWeights
open MovingFiberLeadingCoefficient6815 RCN234 RCN156

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {K N : Type*} [Field K]

theorem low_coefficient_vanish_of_agreement (P : Poly (K := K)) (m a w k n0 d : ℕ)
    (ha : 0 < a) (hwa : w-2 ≤ a) (hdm : d < m) (hdn : d < n0)
    (hfact : (d.factorial : K) ≠ 0)
    (hP : ∀ e ∈ P.support,
      e 0+w*e 2+(w-1)*e 3+(w-2)*e 1+reserve k n0 (e 1)*(a-(w-2)) < m*a)
    (nodes : N ↪ K) (u0 u1 : N → K)
    (hcontact : ∀ i, MvPolynomial.X 0^m ∣ substitute (K := K)
      (localize (nodes i) (u0 i) (u1 i) P))
    (f : Polynomial K) (hf : f.natDegree ≤ w) (z : K) (S : Finset N)
    (hS : a ≤ S.card) (hvalues : ∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z)
    (hh : ∀ j, d < j → coefficientSpecialize f z ((asS P).coeff j) = 0) :
    coefficientSpecialize f z ((asS P).coeff d) = 0 := by
  have hreserve : (w-2)*d+d*(a-(w-2)) = d*a := by
    rw [Nat.mul_comm (w-2) d, ← Nat.mul_add, Nat.add_sub_of_le hwa]
  have horder : (m-d)*a+d*a = m*a := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hdm.le]
  have hweight : ∀ e ∈ ((asS P).coeff d).support,
      e 0+w*e 1+(w-1)*e 2 < (m-d)*a := by
    intro e he
    have hb := hP _ (coefficient_support P d e he)
    obtain ⟨h0,h1,h2,h3,_⟩ := lift_coordinates d e
    rw [h0,h1,h2,h3] at hb
    simp only [reserve, hdn, ite_true, add_assoc, hreserve] at hb
    omega
  have hdeg := coefficient_degree ((asS P).coeff d) f z w ((m-d)*a)
    hf (Nat.mul_pos (Nat.sub_pos_of_lt hdm) ha) hweight
  have htop := specialize_top P f z d hh
  have hv : specialize f z ((pderiv 1)^[d] P) = 0 := by
    refine SecondJetVanish.eq_zero_of_contact_degree _ f z nodes u0 u1 S (m-d) ?_ hvalues ?_
    · intro i _
      apply SecondJetGlobalDifferentiation.local_derivative_contact
      simpa only [Nat.sub_add_cancel hdm.le] using hcontact i
    · rw [htop]
      have hs := Polynomial.natDegree_smul_le d.factorial
        (coefficientSpecialize f z ((asS P).coeff d))
      exact (hs.trans_lt hdeg).trans_le (Nat.mul_le_mul_left (m-d) hS)
  rw [htop, nsmul_eq_mul] at hv
  apply (mul_eq_zero.mp hv).resolve_left
  simpa only [map_natCast] using (Polynomial.C_ne_zero.mpr hfact)

def ProperProfileHelper (F Q : MvPolynomial (Fin 4) K) (p : JetProfile)
    (capR capY capT : ℕ) (nodes : N ↪ K) (u0 u1 : N → K) : Prop :=
  IsRelPrime F Q ∧
    (wt residualSWeights Q ≤ p.secondCap+p.slopeCap*(capR-1) ∧
      wt residualYSWeights Q ≤ p.middleCap+p.slopeCap*(capY-1) ∧
      wt residualTotalWeights Q ≤ p.totalCap+p.slopeCap*(capT-1)) ∧
    ∀ f : Polynomial K, f.natDegree ≤ 131071 → ∀ z : K, ∀ S : Finset N,
      181049 ≤ S.card → (∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z) →
      RCN319.specialization K f z F = 0 → RCN319.specialization K f z Q = 0

theorem profile_leading_coprime_and_weights [Fintype N]
    (p : JetProfile) (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (nodes : N ↪ K) (u0 u1 : N → K) (hP : ProfileInterpolant p nodes u0 u1 P)
    (hFi : Irreducible F) (hFT : p.totalCap < wt residualTotalWeights F) :
    let Q := (asS P).leadingCoeff
    IsRelPrime F Q ∧ wt residualSWeights Q ≤ p.secondCap ∧
      wt residualYSWeights Q ≤ p.middleCap ∧ wt residualTotalWeights Q ≤ p.totalCap := by
  have hflags : ∀ e ∈ P.support, 2*e 1+e 3 ≤ p.secondCap ∧
      e 1+e 2+e 3 ≤ p.middleCap ∧ e 1+e 2+e 3+e 4 ≤ p.totalCap := by
    intro e he
    have h := hP.2.1 e he
    exact ⟨h.1,h.2.2.1,h.2.2.2.1⟩
  have hQ := SecondJetTotalAvoidance.leading_not_dvd P hP.1 F p.totalCap
    (fun e he => (hflags e he).2.2) hFT
  refine ⟨hFi.isRelPrime_iff_not_dvd.mpr hQ.2, ?_⟩
  have hw := derivative_coefficient_weights P p.secondCap p.middleCap p.totalCap 0
    (asS P).natDegree hflags
  simp only [Function.iterate_zero, id_eq, Nat.mul_zero, Nat.sub_zero] at hw
  exact ⟨hw.1.trans (Nat.sub_le _ _), hw.2.1.trans (Nat.sub_le _ _),
    hw.2.2.trans (Nat.sub_le _ _)⟩

theorem profile_helper_or_divisibility [CharP K 2130706433] [Fintype N]
    (j : Fin 6) (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (capR capY capT : ℕ) (nodes : N ↪ K) (u0 u1 : N → K)
    (hP : ProfileInterpolant (jetProfile j) nodes u0 u1 P)
    (hFi : Irreducible F) (hFT : (jetProfile j).totalCap < wt residualTotalWeights F)
    (hR : 1 ≤ capR) (hY : 1 ≤ capY) (hT : 1 ≤ capT)
    (hF : wt residualSWeights F ≤ capR ∧ wt residualYSWeights F ≤ capY ∧
      wt residualTotalWeights F ≤ capT) :
    let p := jetProfile j
    (∃ Q, ProperProfileHelper F Q p capR capY capT nodes u0 u1) ∨
      (p.minimumOrder ≤ (asS P).natDegree ∧
        ∀ d ≤ p.derivativeOrder, F ∣ helper P F (p.slopeCap-d) d) := by
  classical
  let p := jetProfile j
  have hsB : 2*p.slopeCap ≤ p.secondCap := by fin_cases j <;> decide
  have hsU : p.slopeCap ≤ p.middleCap := by fin_cases j <;> decide
  have hsL : p.slopeCap ≤ p.totalCap := by fin_cases j <;> decide
  have hks : p.derivativeOrder ≤ p.slopeCap := by fin_cases j <;> decide
  have hsm : p.slopeCap < p.order := by fin_cases j <;> decide
  have hchar : p.slopeCap < 2130706433 := by fin_cases j <;> decide
  have hflags : ∀ e ∈ P.support, 2*e 1+e 3 ≤ p.secondCap ∧
      e 1+e 2+e 3 ≤ p.middleCap ∧ e 1+e 2+e 3+e 4 ≤ p.totalCap := by
    intro e he
    have h := hP.2.1 e he
    exact ⟨h.1,h.2.2.1,h.2.2.2.1⟩
  have hS : ∀ e ∈ P.support, e 1 ≤ p.slopeCap := fun e he => (hP.2.1 e he).2.1
  have hdegree : (asS P).natDegree ≤ p.slopeCap := by
    simpa using asS_derivative_degree P p.slopeCap 0 hS
  change (∃ Q, ProperProfileHelper F Q p capR capY capT nodes u0 u1) ∨
    (p.minimumOrder ≤ (asS P).natDegree ∧
      ∀ d ≤ p.derivativeOrder, F ∣ helper P F (p.slopeCap-d) d)
  by_cases hn : (asS P).natDegree < p.minimumOrder
  · left
    let n := (asS P).natDegree
    let Q := (asS P).leadingCoeff
    obtain ⟨hcop,hwR,hwY,hwT⟩ := profile_leading_coprime_and_weights p P F nodes u0 u1 hP hFi hFT
    refine ⟨Q,hcop,⟨by dsimp [Q]; omega, by dsimp [Q]; omega, by dsimp [Q]; omega⟩,?_⟩
    · intro f hf z S hSc hvalues _
      have hweight : ∀ e ∈ P.support,
          e 0+131071*e 2+131070*e 3+131069*e 1+
            reserve p.derivativeOrder p.minimumOrder (e 1)*49980 < p.order*181049 := by
        intro e he
        have hcut := (hP.2.1 e he).2.2.2.2
        change e 0+131071*e 2+131070*e 3+131069*e 1 < profileCutoff p (e 1) at hcut
        dsimp [profileCutoff] at hcut
        omega
      apply low_coefficient_vanish_of_agreement P p.order 181049 131071
        p.derivativeOrder p.minimumOrder n (by decide) (by decide)
        (hdegree.trans_lt hsm) hn
        (RCN347.factorial_cast_ne_zero_below_characteristic 2130706433 n (hdegree.trans_lt hchar))
        hweight nodes u0 u1 hP.2.2.1 f hf z S hSc hvalues
      intro i hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, map_zero]
  · by_cases hdiv : ∀ d ≤ p.derivativeOrder, F ∣ helper P F (p.slopeCap-d) d
    · exact Or.inr ⟨Nat.le_of_not_gt hn,hdiv⟩
    · left
      push Not at hdiv
      obtain ⟨d,hd,hproper⟩ := hdiv
      refine ⟨helper P F (p.slopeCap-d) d,hFi.isRelPrime_iff_not_dvd.mpr hproper,?_,?_⟩
      · have hw := helper_weights P F p.secondCap p.middleCap p.totalCap p.slopeCap
          d capT capY capR hsB hsU hsL (hd.trans hks) hR hY hT hflags hF
        have hr := Nat.mul_le_mul_right (capR-1) (Nat.sub_le p.slopeCap d)
        have hy := Nat.mul_le_mul_right (capY-1) (Nat.sub_le p.slopeCap d)
        have ht := Nat.mul_le_mul_right (capT-1) (Nat.sub_le p.slopeCap d)
        omega
      · intro f hf z S hSc hvalues hFzero
        exact helper_vanish P F (p.slopeCap-d) d
          (asS_derivative_degree P p.slopeCap d hS) f z hFzero
          (hP.2.2.2 d hd f hf z S hSc hvalues)

section RetainedSources

variable {E : Type} [Field E] [CharP E 2130706433] [Fintype N]

theorem exists_cell_helper_or_sources (ids : Fin 6 × Fin 6 × Fin 6)
    (hN : Fintype.card N ≤ 262144) (F : MvPolynomial (Fin 4) E)
    (capR capY capT : ℕ) (nodes : N ↪ E) (u0 u1 : N → E)
    (hFi : Irreducible F) (hFT : ∀ j, (cellConfig ids j).totalCap < wt residualTotalWeights F)
    (hR : 1 ≤ capR) (hY : 1 ≤ capY) (hT : 1 ≤ capT)
    (hF : wt residualSWeights F ≤ capR ∧ wt residualYSWeights F ≤ capY ∧
      wt residualTotalWeights F ≤ capT) :
    (∃ j : Fin 3, ∃ Q, ProperProfileHelper F Q (cellConfig ids j) capR capY capT nodes u0 u1) ∨
      ∃ source : Fin 3 → MovingFiberThreeSources6811.Source F,
        ∀ j, let p := cellConfig ids j
          ProfileInterpolant p nodes u0 u1 (source j).P ∧
            (source j).B = p.secondCap ∧ (source j).U = p.middleCap ∧
            (source j).T = p.totalCap ∧ (source j).s = p.slopeCap ∧
            (source j).k = p.derivativeOrder ∧ (source j).n0 = p.minimumOrder := by
  classical
  obtain ⟨P,hP⟩ := exists_cell_interpolants ids hN nodes u0 u1
  let profileId : Fin 3 → Fin 6 := ![ids.1, ids.2.1, ids.2.2]
  have hconfig (j : Fin 3) : cellConfig ids j = jetProfile (profileId j) := by
    fin_cases j <;> rfl
  have halternative (j : Fin 3) := profile_helper_or_divisibility (profileId j) (P j) F
    capR capY capT nodes u0 u1 (hconfig j ▸ hP j) hFi (hconfig j ▸ hFT j) hR hY hT hF
  by_cases hproper : ∃ j : Fin 3, ∃ Q, ProperProfileHelper F Q
      (cellConfig ids j) capR capY capT nodes u0 u1
  · exact Or.inl hproper
  · have hretain (j : Fin 3) :
        let p := cellConfig ids j
        p.minimumOrder ≤ (asS (P j)).natDegree ∧
          ∀ d ≤ p.derivativeOrder, F ∣ helper (P j) F (p.slopeCap-d) d := by
      rw [hconfig j]
      exact (halternative j).resolve_left (fun ⟨Q,hQ⟩ => hproper ⟨j,Q,(hconfig j).symm ▸ hQ⟩)
    have hprofile (i : Fin 6) :
        let p := jetProfile i
        p.secondCap ≤ p.middleCap ∧ p.middleCap ≤ p.totalCap ∧
          p.derivativeOrder+1 ≤ p.minimumOrder ∧
          2*(p.minimumOrder-(p.derivativeOrder+1)) ≤ p.secondCap := by
      fin_cases i <;> decide
    have hshape (j : Fin 3) :
        let p := cellConfig ids j
        p.secondCap ≤ p.middleCap ∧ p.middleCap ≤ p.totalCap ∧
          p.derivativeOrder+1 ≤ p.minimumOrder ∧
          2*(p.minimumOrder-(p.derivativeOrder+1)) ≤ p.secondCap := by
      rw [hconfig]
      exact hprofile (profileId j)
    let source (j : Fin 3) : MovingFiberThreeSources6811.Source F :=
      { P := P j
        B := (cellConfig ids j).secondCap
        U := (cellConfig ids j).middleCap
        T := (cellConfig ids j).totalCap
        s := (cellConfig ids j).slopeCap
        k := (cellConfig ids j).derivativeOrder
        n0 := (cellConfig ids j).minimumOrder
        hS := fun e he => ((hP j).2.1 e he).2.1
        hshape := fun e he => by
          have h := (hP j).2.1 e he
          exact ⟨h.1, h.2.2.1, h.2.2.2.1⟩
        hBU := (hshape j).1
        hUT := (hshape j).2.1
        hdn := (hshape j).2.2.1
        hB := (hshape j).2.2.2
        hn := (hretain j).1
        hdiv := (hretain j).2 }
    exact Or.inr ⟨source, fun j => ⟨hP j,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩

end RetainedSources

end

end ProximityPrize.SubmissionLower.K6833Residual

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
