import ProximityPrize.SubmissionLower.MergedInfra6815_23
import ProximityPrize.SubmissionLower.MergedInfra6815_29
import ProximityPrize.SubmissionLower.MergedInfra6815_17
import ProximityPrize.SubmissionLower.MergedInfra6815_30
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.WholeSpacePowerCover6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
open WholeSpacePowerBox6814 MovingSourceNativeEnvelope6814 RCN095 SecondJetRelaxedFlag

def native (m s b u t : ℕ) : ℕ :=
  3*126275387074424400*m+
    coefficientZ3*flagMixed parentFlag unitZFlag (budgetFlag b u t m s)+
    coefficientU3*flagMixed parentFlag unitYZFlag (budgetFlag b u t m s)+
    coefficientA3*flagMixed parentFlag unitAllFlag (budgetFlag b u t m s)

end
end ProximityPrize.SubmissionLower.WholeSpacePowerCover6814
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.WholeSpacePowerSupplier6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open WholeSpacePowerBox6814 WholeSpacePowerCover6814 WholeSpaceSourceKernel6814
open WholeSpaceSourceCounts6814 SecondJetGlobalSupport

variable {K N I : Type*} [Field K] [Fintype N] [Fintype I]

theorem cofactor_of_not_power (J P : Poly (K := K)) (hJ : Irreducible J) (q : ℕ)
    (hnot : ¬J^q∣P) :
    ∃ e<q, ∃ Q : Poly (K := K), P=J^e*Q ∧ Q≠0 ∧ IsRelPrime J Q := by
  have hP : P≠0 := by intro hz; exact hnot (by rw [hz]; exact dvd_zero _)
  obtain ⟨e,Q,hnd,hEq⟩ := WfDvdMonoid.max_power_factor hP hJ
  have hQ : Q≠0 := by intro hz; apply hP; rw [hEq,hz,mul_zero]
  have he : e<q := by
    by_contra h
    exact hnot ((pow_dvd_pow J (by omega : q≤e)).trans ⟨Q,hEq⟩)
  exact ⟨e,he,Q,hEq,hQ,hJ.isRelPrime_iff_not_dvd.mpr hnd⟩

end
end ProximityPrize.SubmissionLower.WholeSpacePowerSupplier6814
end MergedPart1
section MergedPart2
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
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.PortfolioSource6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 40000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open SecondJetCoefficients SecondJetCoefficientSpecialization SecondJetClearedHelper SecondJetHelperWeights
open SecondJetGlobalSupport SecondJetSpecialize SecondJetRelaxedGlobalIndex
open RCN234 RCN156 MovingFiberThreeSources6811

structure Parameters where
  m : ℕ
  L : ℕ
  B : ℕ
  s : ℕ
  U : ℕ
  k : ℕ
  n0 : ℕ
  deriving DecidableEq

def Parameters.cutoff (p : Parameters) (h : ℕ) : ℕ :=
  p.m*181245-SecondJetRelaxedDifferentiation.reserve p.k p.n0 h*50176

structure Shape (p : Parameters) : Prop where
  slope : 2*p.s≤p.B
  middle : p.B≤p.U
  total : p.U≤p.L
  contact : p.s<p.m
  retention : p.k+1≤p.n0
  degree : p.n0≤p.s
  characteristic : p.s<2130706433

def Dimension (p : Parameters) (Kdim : ℕ) : Prop :=
  Kdim+262144*SecondJetRelaxedGlobalMap.rankBound p.m p.L p.B p.s p.U
    (fun h => (p.cutoff h+p.B-1)/131071)≤
    Fintype.card (Index p.cutoff 131071 p.L p.B p.s p.U)

variable {K N : Type} [Field K] [Fintype N]

def Bounds (p : Parameters) (P : Poly (K:=K)) : Prop :=
  ∀ e∈P.support, 2*e 1+e 3≤p.B ∧ e 1≤p.s ∧ e 1+e 2+e 3≤p.U ∧
    e 1+e 2+e 3+e 4≤p.L ∧
    e 0+131071*e 2+131070*e 3+131069*e 1<p.cutoff (e 1)

def Interpolant (p : Parameters) (nodes : N ↪ K) (u0 u1 : N → K) (P : Poly (K:=K)) : Prop :=
  P≠0 ∧ Bounds p P ∧ ∀ i, MvPolynomial.X 0^p.m ∣ SecondJetDifferentiation.substitute (K:=K)
    (localize (nodes i) (u0 i) (u1 i) P)

theorem exists_kernel (p : Parameters) (hp : Shape p) (Kdim : ℕ) (hd : Dimension p Kdim)
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144) :
    ∃ V : Submodule K (Poly (K:=K)), Module.Finite K V ∧ Kdim≤Module.finrank K V ∧
      (∀ P∈V, Bounds p P) ∧ (∀ P∈V, ∀ i, MvPolynomial.X 0^p.m ∣
        SecondJetDifferentiation.substitute (K:=K) (localize (nodes i) (u0 i) (u1 i) P)) := by
  let e := SecondJetRelaxedGlobalIndex.exponent (D:=p.cutoff) (w:=131071)
    (L:=p.L) (B:=p.B) (s:=p.s) (U:=p.U)
  have he := SecondJetRelaxedGlobalIndex.exponent_injective p.cutoff 131071 p.L p.B p.s p.U
  have hb := SecondJetRelaxedGlobalIndex.exponent_bounds p.cutoff 131071 p.L p.B p.s p.U hp.slope
  obtain ⟨V,hf,hv,hs,hc⟩ := WholeSpaceSourceKernel6814.exists_contact_kernel e he
    p.m p.L p.B p.s p.U 131071 p.cutoff (by decide)
    (fun i => (hb i).1) (fun i => (hb i).2.1) (fun i => (hb i).2.2.1)
    (fun i => (hb i).2.2.2.1) (fun i => (hb i).2.2.2.2) nodes u0 u1 Kdim
    (by simpa only [hN,Dimension] using hd)
  refine ⟨V,hf,hv,?_,hc⟩
  intro P hP d hdP
  obtain ⟨i,rfl⟩ := hs P hP d hdP
  exact hb i

theorem exists_interpolant (p : Parameters) (hp : Shape p) (Kdim : ℕ)
    (hpos : 0<Kdim) (hd : Dimension p Kdim)
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144) :
    ∃ P, Interpolant p nodes u0 u1 P := by
  obtain ⟨V,hf,hv,hb,hc⟩ := exists_kernel p hp Kdim hd nodes u0 u1 hN
  letI : Module.Finite K V := hf
  have hn : ∃ P∈V, P≠0 := by
    by_contra h
    have hz : ∀ P∈V, P=0 := by simpa using h
    have hcard := finrank_le_coefficients (fun i : Fin 0 => Fin.elim0 i)
      V.subtype Subtype.val_injective (by
        intro v e he
        simp [show (v : Poly (K:=K))=0 from hz v.val v.property] at he)
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨P,hP,hne⟩ := hn
  exact ⟨P,hne,hb P hP,hc P hP⟩

theorem derivative_vanish (p : Parameters) (hp : Shape p)
    (nodes : N ↪ K) (u0 u1 : N → K) (P : Poly (K:=K))
    (hP : Interpolant p nodes u0 u1 P) (d : ℕ) (hd : d≤p.k)
    (f : Polynomial K) (hf : f.natDegree≤131071) (z : K) (A : Finset N)
    (hA : 181245≤A.card) (hvalues : ∀ i∈A, f.eval (nodes i)=u0 i+u1 i*z) :
    specialize f z ((pderiv 1)^[d] P)=0 := by
  have hs := hp.contact
  have hk := hp.retention
  have hn := hp.degree
  apply SecondJetRelaxedDifferentiation.derivative_vanish P p.m 181245 131071 p.k p.n0 d
    (by decide) (by decide) (by omega) hd ?_ nodes u0 u1 hP.2.2 f hf z A hA hvalues
  intro e he
  have hh := (hP.2.1 e he).2.2.2.2
  dsimp [Parameters.cutoff] at hh
  norm_num
  omega

theorem low_coefficient_vanish (p : Parameters) (hp : Shape p)
    (nodes : N ↪ K) (u0 u1 : N → K) (P : Poly (K:=K))
    (hP : Interpolant p nodes u0 u1 P) (d : ℕ) (hd : d<p.n0)
    (hfact : (d.factorial : K)≠0)
    (f : Polynomial K) (hf : f.natDegree≤131071) (z : K) (A : Finset N)
    (hA : 181245≤A.card) (hvalues : ∀ i∈A, f.eval (nodes i)=u0 i+u1 i*z)
    (hh : ∀ j, d<j → coefficientSpecialize f z ((asS P).coeff j)=0) :
    coefficientSpecialize f z ((asS P).coeff d)=0 := by
  have hdm : d<p.m := lt_trans (lt_of_lt_of_le hd hp.degree) hp.contact
  have hweight : ∀ e∈((asS P).coeff d).support,
      e 0+131071*e 1+131070*e 2<(p.m-d)*181245 := by
    intro e he
    have hb := (hP.2.1 _ (coefficient_support P d e he)).2.2.2.2
    obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates d e
    rw [h0,h1,h2,h3] at hb
    simp only [Parameters.cutoff,SecondJetRelaxedDifferentiation.reserve,if_pos hd] at hb
    omega
  have hdeg := MovingFiberLeadingCoefficient6811.coefficient_degree ((asS P).coeff d)
    f z 131071 ((p.m-d)*181245) hf (by omega) hweight
  have htop := MovingFiberLeadingCoefficient6811.specialize_top P f z d hh
  have hv : specialize f z ((pderiv 1)^[d] P)=0 := by
    refine SecondJetVanish.eq_zero_of_contact_degree _ f z nodes u0 u1 A (p.m-d) ?_ hvalues ?_
    · intro i _
      apply SecondJetGlobalDifferentiation.local_derivative_contact
      simpa only [Nat.sub_add_cancel (Nat.le_of_lt hdm)] using hP.2.2 i
    · rw [htop]
      exact ((Polynomial.natDegree_smul_le d.factorial _).trans_lt hdeg).trans_le
        (Nat.mul_le_mul_left (p.m-d) hA)
  rw [htop,nsmul_eq_mul] at hv
  exact (mul_eq_zero.mp hv).resolve_left (by
    simpa only [map_natCast] using Polynomial.C_ne_zero.mpr hfact)

def ProperHelper (p : Parameters) (F Q : MvPolynomial (Fin 4) K) (r y t : ℕ)
    (nodes : N ↪ K) (u0 u1 : N → K) : Prop :=
  IsRelPrime F Q ∧
  (wt residualSWeights Q≤p.B+p.s*(r-1) ∧ wt residualYSWeights Q≤p.U+p.s*(y-1) ∧
    wt residualTotalWeights Q≤p.L+p.s*(t-1)) ∧
  ∀ f : Polynomial K, f.natDegree≤131071 → ∀ z : K, ∀ A : Finset N,
    181245≤A.card → (∀ i∈A, f.eval (nodes i)=u0 i+u1 i*z) →
      RCN319.specialization K f z F=0 → RCN319.specialization K f z Q=0

theorem helper_or_retained [CharP K 2130706433]
    (p : Parameters) (hp : Shape p) (nodes : N ↪ K) (u0 u1 : N → K)
    (P : Poly (K:=K)) (hP : Interpolant p nodes u0 u1 P)
    (F : MvPolynomial (Fin 4) K) (hFi : Irreducible F) (hFT : p.L<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t) :
    (∃ Q, ProperHelper p F Q r y t nodes u0 u1) ∨
      (p.n0≤(asS P).natDegree ∧ ∀ d≤p.k, F∣helper P F (p.s-d) d) := by
  have hflags : ∀ e∈P.support, 2*e 1+e 3≤p.B ∧ e 1+e 2+e 3≤p.U ∧
      e 1+e 2+e 3+e 4≤p.L :=
    fun e he => ⟨(hP.2.1 e he).1,(hP.2.1 e he).2.2.1,(hP.2.1 e he).2.2.2.1⟩
  have hS : ∀ e∈P.support, e 1≤p.s := fun e he => (hP.2.1 e he).2.1
  have hdegree : (asS P).natDegree≤p.s := by simpa using asS_derivative_degree P p.s 0 hS
  by_cases hn : (asS P).natDegree<p.n0
  · left
    let n := (asS P).natDegree
    let Q := (asS P).leadingCoeff
    have hQ := SecondJetTotalAvoidance.leading_not_dvd P hP.1 F p.L (fun e he => (hflags e he).2.2) hFT
    refine ⟨Q,hFi.isRelPrime_iff_not_dvd.mpr hQ.2,?_,?_⟩
    · have hw := derivative_coefficient_weights P p.B p.U p.L 0 n hflags
      simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at hw
      change wt residualSWeights ((asS P).coeff n)≤p.B+p.s*(r-1) ∧
        wt residualYSWeights ((asS P).coeff n)≤p.U+p.s*(y-1) ∧
        wt residualTotalWeights ((asS P).coeff n)≤p.L+p.s*(t-1)
      omega
    · intro f hf z A hA hvalues _
      apply low_coefficient_vanish p hp nodes u0 u1 P hP n hn
        (SecondJetOwnShape.factorial_ne n (hdegree.trans_lt hp.characteristic)) f hf z A hA hvalues
      intro j hj
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj,map_zero]
  · by_cases hdiv : ∀ d≤p.k, F∣helper P F (p.s-d) d
    · exact Or.inr ⟨by omega,hdiv⟩
    · left
      push Not at hdiv
      obtain ⟨d,hd,hproper⟩ := hdiv
      refine ⟨helper P F (p.s-d) d,hFi.isRelPrime_iff_not_dvd.mpr hproper,?_,?_⟩
      · have hshape := hp.slope
        have hmid := hp.middle
        have htot := hp.total
        have hret := hp.retention
        have hdeg := hp.degree
        have hw := helper_weights P F p.B p.U p.L p.s d t y r
          (by omega) (by omega) (by omega) (by omega) hr hy ht hflags hF
        have hrr := Nat.mul_le_mul_right (r-1) (Nat.sub_le p.s d)
        have hyy := Nat.mul_le_mul_right (y-1) (Nat.sub_le p.s d)
        have htt := Nat.mul_le_mul_right (t-1) (Nat.sub_le p.s d)
        omega
      · intro f hf z A hA hvalues hFzero
        exact helper_vanish P F (p.s-d) d (asS_derivative_degree P p.s d hS) f z hFzero
          (derivative_vanish p hp nodes u0 u1 P hP d hd f hf z A hA hvalues)

theorem exists_helper_or_source [CharP K 2130706433]
    (p : Parameters) (hp : Shape p) (Kdim : ℕ) (hpos : 0<Kdim) (hd : Dimension p Kdim)
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (F : MvPolynomial (Fin 4) K) (hFi : Irreducible F) (hFT : p.L<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t) :
    (∃ Q, ProperHelper p F Q r y t nodes u0 u1) ∨
      ∃ S : Source F, MovingSourceTwoProfiles6814.Profile S p.B p.U p.L p.s p.k p.n0 := by
  obtain ⟨P,hP⟩ := exists_interpolant p hp Kdim hpos hd nodes u0 u1 hN
  rcases helper_or_retained p hp nodes u0 u1 P hP F hFi hFT r y t hr hy ht hF with hh | hret
  · exact Or.inl hh
  let S : Source F := {
    P:=P, B:=p.B, U:=p.U, T:=p.L, s:=p.s, k:=p.k, n0:=p.n0
    hS:=fun e he => (hP.2.1 e he).2.1
    hshape:=fun e he => ⟨(hP.2.1 e he).1,(hP.2.1 e he).2.2.1,(hP.2.1 e he).2.2.2.1⟩
    hBU:=hp.middle, hUT:=hp.total, hdn:=hp.retention
    hB:=by have := hp.slope; have := hp.degree; omega
    hn:=hret.1, hdiv:=hret.2 }
  exact Or.inr ⟨S,by repeat' constructor⟩

end
end ProximityPrize.SubmissionLower.PortfolioSource6815
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.PortfolioSource6815
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem dimension_of_counts (p : Parameters) (Kdim C R : ℕ)
    (hsB : 2*p.s≤p.B) (hBm : p.B≤p.m) (hU : p.m+p.s≤p.U)
    (hL : p.m+p.B+p.s≤p.L) (hUT : p.U≤p.L)
    (hcaps : ∀ h, h≤p.s → p.U≤(p.cutoff h+p.B-1)/131071)
    (hC : SecondJetRelaxedGlobalCounts.coefficientCount p.cutoff 131071 p.L p.B p.s p.U=C)
    (hR : SecondJetRelaxedCounts.rankBound p.m p.L p.B p.s p.U=R)
    (hfit : Kdim+262144*R≤C) : Dimension p Kdim := by
  unfold Dimension
  rw [SecondJetRelaxedCounts.rankBound_eq_closed _ _ _ _ _ _ hsB hBm hU hL hcaps,
    SecondJetRelaxedGlobalCounts.card_index_closed _ _ _ _ _ _ hUT,hR,hC]
  exact hfit

end ProximityPrize.SubmissionLower.PortfolioSource6815
end MergedPart4
