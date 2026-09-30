import ProximityPrize.SubmissionLower.PacketExactIndex6815
import ProximityPrize.SubmissionLower.WholeSpacePowerSupplier6814
namespace ProximityPrize.SubmissionLower.PacketFourRetention6815
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open SecondJetRelaxedGlobalIndex SecondJetRelaxedGlobalCounts
open SecondJetCoefficients SecondJetGlobalSupport SecondJetCoefficientSpecialization
open SecondJetClearedHelper SecondJetHelperWeights RCN234 RCN156

def cutoff (h : ℕ) : ℕ :=
  87*181245-SecondJetRelaxedDifferentiation.reserve 3 4 h*50176

theorem coefficients :
    coefficientCount cutoff 131071 1430 38 17 119=366765095606388 := by decide +kernel

theorem rank : SecondJetRelaxedCounts.rankBound 87 1430 38 17 119=1399093086 := by
  decide +kernel

theorem middle_cap (h : ℕ) : 119≤(cutoff h+38-1)/131071 := by
  unfold cutoff SecondJetRelaxedDifferentiation.reserve
  split_ifs <;> omega

theorem dimension :
    262144*SecondJetRelaxedGlobalMap.rankBound 87 1430 38 17 119
      (fun h => (cutoff h+38-1)/131071)<
      Fintype.card (Index cutoff 131071 1430 38 17 119) := by
  rw [SecondJetRelaxedCounts.rankBound_eq_closed 87 1430 38 17 119 _
    (by omega) (by omega) (by omega) (by omega) (fun h _ => middle_cap h),
    card_index_closed _ _ _ _ _ _ (by omega),rank,coefficients]
  decide +kernel

variable {K N E : Type} [Field K] [Fintype N] [Field E]

def Bounds (P : Poly (K:=K)) : Prop :=
  ∀ e∈P.support, 2*e 1+e 3≤38 ∧ e 1≤17 ∧
    e 1+e 2+e 3≤119 ∧ e 1+e 2+e 3+e 4≤1430 ∧
    e 0+131071*e 2+131070*e 3+131069*e 1<cutoff (e 1)

omit [Fintype N] in
theorem derivative_vanish (nodes : N ↪ K) (u0 u1 : N → K)
    (P : Poly (K:=K)) (hb : Bounds P)
    (hc : ∀ i, MvPolynomial.X 0^87 ∣ SecondJetDifferentiation.substitute (K:=K)
      (localize (nodes i) (u0 i) (u1 i) P))
    (d : ℕ) (hd : d≤3) (f : Polynomial K) (hf : f.natDegree≤131071)
    (z : K) (S : Finset N) (hS : 181245≤S.card)
    (hvalues : ∀ i∈S, f.eval (nodes i)=u0 i+u1 i*z) :
    SecondJetSpecialize.specialize f z ((pderiv 1)^[d] P)=0 := by
  apply SecondJetRelaxedDifferentiation.derivative_vanish P 87 181245 131071 3 4 d
    (by omega) (by omega) (by omega) hd ?_ nodes u0 u1 hc f hf z S hS hvalues
  intro e he
  have hh := (hb e he).2.2.2.2
  dsimp [cutoff] at hh
  norm_num
  omega

theorem cofactor_root_power
    (phi : Poly (K:=K) →+* Polynomial E) (z : E)
    (J P Q : Poly (K:=K)) (e m d : ℕ) (hEq : P=J^e*Q)
    (hJ : phi J≠0) (hm : (phi J).rootMultiplicity z=m)
    (hp : (Polynomial.X-Polynomial.C z)^d∣phi P) :
    (Polynomial.X-Polynomial.C z)^(d-e*m)∣phi Q := by
  by_cases hQ : phi Q=0
  · rw [hQ]; exact dvd_zero _
  rw [hEq,map_mul,map_pow] at hp
  have hn := mul_ne_zero (pow_ne_zero e hJ) hQ
  have horder := (Polynomial.le_rootMultiplicity_iff hn).mpr hp
  rw [Polynomial.rootMultiplicity_mul hn,
    UniqueCurvatureOwner6814.rootMultiplicity_power (phi J) z e hJ,hm] at horder
  exact (Polynomial.le_rootMultiplicity_iff hQ).mp (by omega)

theorem residual_order_pos (d m e : ℕ) (hm : 0<m)
    (he : e<(d+m-1)/m) : 0<d-e*m := by
  have hh : (e+1)*m≤d+m-1 := (Nat.le_div_iff_mul_le hm).mp (by omega)
  have hp : e*m+m≤d+m-1 := by simpa only [Nat.add_mul,one_mul] using hh
  omega

theorem retained_pair_extract
    (phi : Poly (K:=K) →+* Polynomial E) (z : E)
    (J P : Poly (K:=K)) (hJ : Irreducible J) (d m : ℕ) (hmpos : 0<m)
    (hnot : ¬J^((d+m-1)/m)∣P) (hne : phi J≠0)
    (hm : (phi J).rootMultiplicity z=m)
    (hpow : (Polynomial.X-Polynomial.C z)^d∣phi P) :
    ∃ e<(d+m-1)/m, ∃ Q : Poly (K:=K), P=J^e*Q ∧ Q≠0 ∧ IsRelPrime J Q ∧
      0<min m (d-e*m) ∧ (Polynomial.X-Polynomial.C z)^(d-e*m)∣phi Q := by
  obtain ⟨e,he,Q,hEq,hQ,hcop⟩ :=
    WholeSpacePowerSupplier6814.cofactor_of_not_power J P hJ ((d+m-1)/m) hnot
  exact ⟨e,he,Q,hEq,hQ,hcop,lt_min hmpos (residual_order_pos d m e hmpos he),
    cofactor_root_power phi z J P Q e m d hEq hne hm hpow⟩

end
end ProximityPrize.SubmissionLower.PacketFourRetention6815
