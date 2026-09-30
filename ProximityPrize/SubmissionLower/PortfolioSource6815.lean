import ProximityPrize.SubmissionLower.PacketPortfolioAvoidance6815
import ProximityPrize.SubmissionLower.MovingSourceZSupplier6814
import ProximityPrize.SubmissionLower.MovingSourceTwoProfiles6814
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
