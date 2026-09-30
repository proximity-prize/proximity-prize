import ProximityPrize.SubmissionLower.MovingSourceZCounts6814
namespace ProximityPrize.SubmissionLower.MovingSourceZSupplier6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetSpecialize
open SecondJetCoefficients SecondJetCoefficientSpecialization SecondJetClearedHelper SecondJetHelperWeights
open SecondJetRelaxedDifferentiation MovingSourceZCounts6814 MovingFiberThreeSources6811
open RCN234 RCN156

variable {K N : Type} [Field K] [Fintype N]

def Bounds (P : Poly (K:=K)) : Prop := ∀ e ∈ P.support,
  2*e 1+e 3≤53 ∧ e 1≤24 ∧ e 1+e 2+e 3≤177 ∧ e 1+e 2+e 3+e 4≤3429 ∧
    e 0+131071*e 2+131070*e 3+131069*e 1<cutoff (e 1)

def Interpolant (nodes : N ↪ K) (u0 u1 : N → K) (P : Poly (K:=K)) : Prop :=
  P≠0 ∧ Bounds P ∧ ∀ i, MvPolynomial.X 0^130 ∣ SecondJetDifferentiation.substitute (K:=K)
    (localize (nodes i) (u0 i) (u1 i) P)

theorem derivative_vanish (nodes : N ↪ K) (u0 u1 : N → K)
    (P : Poly (K:=K)) (hP : Interpolant nodes u0 u1 P)
    (d : ℕ) (hd : d≤6) (f : Polynomial K) (hf : f.natDegree≤131071)
    (z : K) (S : Finset N) (hS : 181255≤S.card)
    (hvalues : ∀ i ∈ S, f.eval (nodes i)=u0 i+u1 i*z) :
    specialize f z ((pderiv 1)^[d] P)=0 := by
  apply SecondJetRelaxedDifferentiation.derivative_vanish P 130 181255 131071 6 8 d
    (by omega) (by omega) (by omega) hd ?_ nodes u0 u1 hP.2.2 f hf z S hS hvalues
  intro e he
  have hh := (hP.2.1 e he).2.2.2.2
  dsimp [cutoff] at hh
  norm_num
  omega

theorem low_coefficient_vanish (nodes : N ↪ K) (u0 u1 : N → K)
    (P : Poly (K:=K)) (hP : Interpolant nodes u0 u1 P)
    (d : ℕ) (hd : d<8) (hfact : (d.factorial : K)≠0)
    (f : Polynomial K) (hf : f.natDegree≤131071) (z : K) (S : Finset N)
    (hS : 181255≤S.card) (hvalues : ∀ i ∈ S, f.eval (nodes i)=u0 i+u1 i*z)
    (hh : ∀ j, d<j → coefficientSpecialize f z ((asS P).coeff j)=0) :
    coefficientSpecialize f z ((asS P).coeff d)=0 := by
  have hweight : ∀ e ∈ ((asS P).coeff d).support,
      e 0+131071*e 1+131070*e 2<(130-d)*181255 := by
    intro e he
    have hb := (hP.2.1 _ (coefficient_support P d e he)).2.2.2.2
    obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates d e
    rw [h0,h1,h2,h3] at hb
    simp only [cutoff,reserve,if_pos hd] at hb
    omega
  have hdeg := MovingFiberLeadingCoefficient6811.coefficient_degree ((asS P).coeff d)
    f z 131071 ((130-d)*181255) hf (by omega) hweight
  have htop := MovingFiberLeadingCoefficient6811.specialize_top P f z d hh
  have hv : specialize f z ((pderiv 1)^[d] P)=0 := by
    refine SecondJetVanish.eq_zero_of_contact_degree _ f z nodes u0 u1 S (130-d) ?_ hvalues ?_
    · intro i _
      apply SecondJetGlobalDifferentiation.local_derivative_contact
      simpa only [Nat.sub_add_cancel (show d≤130 by omega)] using hP.2.2 i
    · rw [htop]
      exact ((Polynomial.natDegree_smul_le d.factorial _).trans_lt hdeg).trans_le
        (Nat.mul_le_mul_left (130-d) hS)
  rw [htop,nsmul_eq_mul] at hv
  exact (mul_eq_zero.mp hv).resolve_left (by
    simpa only [map_natCast] using Polynomial.C_ne_zero.mpr hfact)

end
end ProximityPrize.SubmissionLower.MovingSourceZSupplier6814
