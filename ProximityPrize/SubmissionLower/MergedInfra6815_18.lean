import ProximityPrize.SubmissionLower.MergedInfra6815_10
import ProximityPrize.SubmissionLower.MergedInfra6815_15
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.MovingFiberLeadingCoefficient6815
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetSpecialize
open SecondJetCoefficients SecondJetCoefficientSpecialization SecondJetDifferentiation
open SecondJetRelaxedDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K N : Type*} [Field K]

theorem coefficient_monomial_degree (f : Polynomial K) (z : K) (w : ℕ)
    (hf : f.natDegree ≤ w) (e : Fin 4 →₀ ℕ) (c : K) :
    (coefficientSpecialize f z (MvPolynomial.monomial e c)).natDegree ≤
      e 0+w*e 1+(w-1)*e 2 := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, map_mul, map_pow]
    have hc : (coefficientSpecialize f z (MvPolynomial.C c)).natDegree ≤ 0 := by
      simp [coefficientSpecialize]
    have h0 : (coefficientSpecialize f z (MvPolynomial.X 0)^e 0).natDegree ≤ e 0 := by
      simp [coefficientSpecialize]
    have h1 : (coefficientSpecialize f z (MvPolynomial.X 1)^e 1).natDegree ≤ e 1*w := by
      simpa [coefficientSpecialize] using Polynomial.natDegree_pow_le_of_le (e 1) hf
    have h2 : (coefficientSpecialize f z (MvPolynomial.X 2)^e 2).natDegree ≤ e 2*(w-1) := by
      simpa [coefficientSpecialize] using Polynomial.natDegree_pow_le_of_le (e 2)
        ((Polynomial.natDegree_derivative_le f).trans (Nat.sub_le_sub_right hf 1))
    have h3 : (coefficientSpecialize f z (MvPolynomial.X 3)^e 3).natDegree ≤ 0 := by
      simp [coefficientSpecialize]
    have hh := Polynomial.natDegree_mul_le_of_le hc (Polynomial.natDegree_mul_le_of_le h0
      (Polynomial.natDegree_mul_le_of_le h1 (Polynomial.natDegree_mul_le_of_le h2 h3)))
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,Nat.mul_comm] using hh
  · intro i
    simp

theorem coefficient_degree (P : MvPolynomial (Fin 4) K) (f : Polynomial K)
    (z : K) (w D : ℕ) (hf : f.natDegree ≤ w) (hD : 0 < D)
    (hP : ∀ e ∈ P.support, e 0+w*e 1+(w-1)*e 2 < D) :
    (coefficientSpecialize f z P).natDegree < D := by
  classical
  have ht : ∀ e ∈ P.support,
      (coefficientSpecialize f z (MvPolynomial.monomial e (AddMonoidAlgebra.coeff P e))).natDegree ≤ D-1 := by
    intro e he
    have hh := coefficient_monomial_degree f z w hf e (AddMonoidAlgebra.coeff P e)
    have hb := hP e he
    omega
  rw [MvPolynomial.as_sum P, map_sum]
  have hh := Polynomial.natDegree_sum_le_of_forall_le P.support
    (fun e => coefficientSpecialize f z (MvPolynomial.monomial e (AddMonoidAlgebra.coeff P e))) ht
  omega

theorem iterate_derivative_top {R : Type*} [CommRing R] (P : Polynomial R) (d : ℕ)
    (hh : ∀ j, d < j → P.coeff j = 0) :
    (Polynomial.derivative)^[d] P = Polynomial.C (d.factorial • P.coeff d) := by
  ext j
  rw [Polynomial.coeff_iterate_derivative]
  by_cases hj : j = 0
  · subst j
    simp [Nat.descFactorial_self]
  · rw [hh (j+d) (by omega)]
    simp [hj]

theorem specialize_top (P : Poly (K := K)) (f : Polynomial K) (z : K) (d : ℕ)
    (hh : ∀ j, d < j → coefficientSpecialize f z ((asS P).coeff j) = 0) :
    specialize f z ((pderiv 1)^[d] P) =
      d.factorial • coefficientSpecialize f z ((asS P).coeff d) := by
  rw [specialize_eq, asS_iterate, ← Polynomial.eval_map, ← Polynomial.iterate_derivative_map]
  rw [iterate_derivative_top _ d (by intro j hj; simpa using hh j hj)]
  simp

theorem low_coefficient_vanish (P : Poly (K := K)) (m k n0 d : ℕ)
    (hdm : d < m) (hdn : d < n0) (hfact : (d.factorial : K) ≠ 0)
    (hP : ∀ e ∈ P.support,
      e 0+131071*e 2+131070*e 3+131069*e 1+
        reserve k n0 (e 1)*50176 < m*181245)
    (nodes : N ↪ K) (u0 u1 : N → K)
    (hcontact : ∀ i, MvPolynomial.X 0^m ∣ substitute (K := K)
      (localize (nodes i) (u0 i) (u1 i) P))
    (f : Polynomial K) (hf : f.natDegree ≤ 131071) (z : K) (S : Finset N)
    (hS : 181245 ≤ S.card) (hvalues : ∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z)
    (hh : ∀ j, d < j → coefficientSpecialize f z ((asS P).coeff j) = 0) :
    coefficientSpecialize f z ((asS P).coeff d) = 0 := by
  have hweight : ∀ e ∈ ((asS P).coeff d).support,
      e 0+131071*e 1+131070*e 2 < (m-d)*181245 := by
    intro e he
    have hb := hP _ (coefficient_support P d e he)
    obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates d e
    rw [h0,h1,h2,h3] at hb
    simp only [reserve,if_pos hdn] at hb
    omega
  have hdeg := coefficient_degree ((asS P).coeff d) f z 131071 ((m-d)*181245)
    hf (by omega) hweight
  have htop := specialize_top P f z d hh
  have hv : specialize f z ((pderiv 1)^[d] P) = 0 := by
    refine SecondJetVanish.eq_zero_of_contact_degree _ f z nodes u0 u1 S (m-d) ?_ hvalues ?_
    · intro i _
      apply SecondJetGlobalDifferentiation.local_derivative_contact
      simpa only [Nat.sub_add_cancel (Nat.le_of_lt hdm)] using hcontact i
    · rw [htop]
      have hs := Polynomial.natDegree_smul_le d.factorial
        (coefficientSpecialize f z ((asS P).coeff d))
      exact (hs.trans_lt hdeg).trans_le (Nat.mul_le_mul_left (m-d) hS)
  rw [htop,nsmul_eq_mul] at hv
  apply (mul_eq_zero.mp hv).resolve_left
  simpa only [map_natCast] using (Polynomial.C_ne_zero.mpr hfact)

end
end ProximityPrize.SubmissionLower.MovingFiberLeadingCoefficient6815
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.MovingFiberTotalAvoidance6815
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetCoefficientSpecialization
open SecondJetClearedHelper SecondJetHelperWeights MovingFiberInterpolation6815
open SecondJetRelaxedCoefficientsReceipt RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option maxRecDepth 100000
variable {K N : Type*} [Field K] [Fintype N]

def ProperHelper (F Q : MvPolynomial (Fin 4) K) (B U L s capR capY capT : ℕ)
    (nodes : N ↪ K) (u0 u1 : N → K) : Prop :=
  IsRelPrime F Q ∧
  (wt residualSWeights Q ≤ B+s*(capR-1) ∧
    wt residualYSWeights Q ≤ U+s*(capY-1) ∧
    wt residualTotalWeights Q ≤ L+s*(capT-1)) ∧
  ∀ f : Polynomial K, f.natDegree ≤ 131071 → ∀ z : K, ∀ S : Finset N,
    181245 ≤ S.card → (∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z) →
    RCN319.specialization K f z F = 0 → RCN319.specialization K f z Q = 0

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
            SecondJetRelaxedDifferentiation.reserve k n0 (e 1)*50176 < m*181245 := by
        intro e he
        have hw := (hP.2.1 e he).2.2.2.2
        dsimp [MovingFiberInterpolation6815.cutoff] at hw
        omega
      apply MovingFiberLeadingCoefficient6815.low_coefficient_vanish P m k n0 n
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
end ProximityPrize.SubmissionLower.MovingFiberTotalAvoidance6815
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.Lower80899.Selection
open ProximityPrize.Benchmark RCN100 RCN119 RCN101 RCN180 RCN181 RCN137 RCN183
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq _
local instance:DecidableEq I:=Classical.decEq _
local instance:StrongNormalizationMonoid P4:=
  UniqueFactorizationMonoid.strongNormalizationMonoid
local instance:NormalizedGCDMonoid P4:=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid P4
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
abbrev TCapKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 45673740 131071 11193 78 252 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 30086670 131071 15421 50 166 IRSProfile.domain u0 u1
theorem gateTCap : Fintype.card I * localRankBound 252 11193 78 < coefficientCount 45673740 131071 11193 78 := by
  rw [MovingFiberKernels6815.TCap.rank_exact, MovingFiberKernels6815.TCap.coefficient_exact]
  norm_num [I, IRSProfile.Index]
theorem gateB : Fintype.card I * localRankBound 166 15421 50 < coefficientCount 30086670 131071 15421 50 := by
  rw [MovingFiberKernels6815.B.rank_exact, MovingFiberKernels6815.B.coefficient_exact]
  norm_num [I, IRSProfile.Index]
private theorem gcd_mul_right_plain_associated
    (P H q:P4) (hc:IsRelPrime q P) :
    Associated (gcd P (H * q)) (gcd P H):=by
  apply associated_of_dvd_dvd
  · have hleft:gcd P (H * q) ∣ P:=gcd_dvd_left P (H * q)
    have hright:gcd P (H * q) ∣ H * q:=gcd_dvd_right P (H * q)
    have hcop:IsRelPrime (gcd P (H * q)) q:=hc.symm.of_dvd_left hleft
    exact dvd_gcd hleft (hcop.dvd_of_dvd_mul_right hright)
  · exact dvd_gcd (gcd_dvd_left P H)
      ((gcd_dvd_right P H).trans (dvd_mul_right H q))
private theorem gcd_mul_left_plain_associated
    (H q P:P4) (hc:IsRelPrime q P) :
    Associated (gcd (H * q) P) (gcd H P):=by
  apply associated_of_dvd_dvd
  · have hleft:gcd (H * q) P ∣ H * q:=gcd_dvd_left (H * q) P
    have hright:gcd (H * q) P ∣ P:=gcd_dvd_right (H * q) P
    have hcop:IsRelPrime (gcd (H * q) P) q:=hc.symm.of_dvd_left hright
    exact dvd_gcd (hcop.dvd_of_dvd_mul_right hleft) hright
  · exact dvd_gcd ((gcd_dvd_left H P).trans (dvd_mul_right H q))
      (gcd_dvd_right H P)
structure SelectedPair (u0 u1:I → K) where
  QA:P4
  QB:P4
  QA_ne:QA ≠ 0
  QB_ne:QB ≠ 0
  QA_flag:QA ∈ globalCoefficientBox K 45673740 131071 11193 78
  QB_flag:QB ∈ globalCoefficientBox K 30086670 131071 15421 50
  common_divides_TCap:∀ v:TCapKernel u0 u1,
    gcd QA QB ∣ reconstruct K 45673740 131071 11193 78 v.1
  common_divides_B:∀ v:BKernel u0 u1,
    gcd QA QB ∣ reconstruct K 30086670 131071 15421 50 v.1
  universal_vanishing:
    ∀ (gamma:K) (P:Polynomial K) (points:Finset I),
      P.natDegree ≤ 131071 → 181245 ≤ points.card →
      (∀ i ∈ points,P.eval (IRSProfile.domain i) =u0 i + gamma * u1 i) →
      RCN319.specialization K P gamma QA=0 ∧
        RCN319.specialization K P gamma QB=0
theorem exists_selected_pair (u0 u1:I → K):Nonempty (SelectedPair u0 u1):=by
  classical
  obtain ⟨thetaT,htT,hkT⟩:=exists_nonzero_kernel_array (I:=I)
    K 45673740 131071 11193 78 252 IRSProfile.domain u0 u1 gateTCap
  obtain ⟨thetaB,htB,hkB⟩:=exists_nonzero_kernel_array (I:=I)
    K 30086670 131071 15421 50 166 IRSProfile.domain u0 u1 gateB
  let vT0:TCapKernel u0 u1:=⟨thetaT,LinearMap.mem_ker.mpr hkT⟩
  let vB0:BKernel u0 u1:=⟨thetaB,LinearMap.mem_ker.mpr hkB⟩
  letI:Nontrivial (TCapKernel u0 u1):=⟨⟨vT0,0,by
    intro h
    exact htT (congrArg Subtype.val h)⟩⟩
  letI:Nontrivial (BKernel u0 u1):=⟨⟨vB0,0,by
    intro h
    exact htB (congrArg Subtype.val h)⟩⟩
  let bT:=Module.Free.chooseBasis K (TCapKernel u0 u1)
  let bB:=Module.Free.chooseBasis K (BKernel u0 u1)
  letI:Finite (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)) :=
    Module.Finite.finite_basis bT
  letI:Finite (Module.Free.ChooseBasisIndex K (BKernel u0 u1)) :=
    Module.Finite.finite_basis bB
  letI:Fintype (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)):=Fintype.ofFinite _
  letI:Fintype (Module.Free.ChooseBasisIndex K (BKernel u0 u1)):=Fintype.ofFinite _
  letI:Nonempty (Module.Free.ChooseBasisIndex K (TCapKernel u0 u1)):=bT.index_nonempty
  letI:Nonempty (Module.Free.ChooseBasisIndex K (BKernel u0 u1)):=bB.index_nonempty
  let HT:=commonGCD (TCapKernel u0 u1) bT
  let HB:=commonGCD (BKernel u0 u1) bB
  have hHT:HT ≠ 0:=commonGCD_ne_zero (TCapKernel u0 u1) bT
  have hHB:HB ≠ 0:=commonGCD_ne_zero (BKernel u0 u1) bB
  have hHBbox:HB ∈ globalCoefficientBox K 30086670 131071 15421 50:=
    commonGCD_mem_flagBox (BKernel u0 u1) bB
  have hcardHB:(normalizedFactorSet HB).card < ENat.card K:=
    normalizedFactorSet_card_lt_field_of_mem_flagBox HB 30086670 15421 50
      hHB hHBbox (by norm_num)
  obtain ⟨vA,hvA,hcopA⟩:=exists_common_quotient_isRelPrime
    (TCapKernel u0 u1) bT hHT HB hHB hcardHB
  let qA:=commonQuotientLinear (TCapKernel u0 u1) bT hHT vA
  let QA:=submoduleReconstructLinear (TCapKernel u0 u1) vA
  have hQAeq:QA=HT * qA:=recon_eq_mul_quotientPolynomial
    (submoduleReconstructLinear (TCapKernel u0 u1)) HT
    (commonDivisorProof (TCapKernel u0 u1) bT) vA
  have hQA:QA ≠ 0:=by
    intro hz
    apply hvA
    apply submoduleReconstructLinear_injective (TCapKernel u0 u1)
    simpa only [map_zero,QA] using hz
  have hQAbox:QA ∈ globalCoefficientBox K 45673740 131071 11193 78:=by
    dsimp only [QA]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 45673740 131071 11193 78 vA.1
  have hcardQA:(normalizedFactorSet QA).card < ENat.card K:=
    normalizedFactorSet_card_lt_field_of_mem_flagBox QA 45673740 11193 78
      hQA hQAbox (by norm_num)
  obtain ⟨vB,hvB,hcopB⟩:=exists_common_quotient_isRelPrime
    (BKernel u0 u1) bB hHB QA hQA hcardQA
  let qB:=commonQuotientLinear (BKernel u0 u1) bB hHB vB
  let QB:=submoduleReconstructLinear (BKernel u0 u1) vB
  have hQBeq:QB=HB * qB:=recon_eq_mul_quotientPolynomial
    (submoduleReconstructLinear (BKernel u0 u1)) HB
    (commonDivisorProof (BKernel u0 u1) bB) vB
  have hQB:QB ≠ 0:=by
    intro hz
    apply hvB
    apply submoduleReconstructLinear_injective (BKernel u0 u1)
    simpa only [map_zero,QB] using hz
  have hQBbox:QB ∈ globalCoefficientBox K 30086670 131071 15421 50:=by
    dsimp only [QB]
    rw [submoduleReconstructLinear_apply]
    exact reconstruct_mem_globalCoefficientBox K 30086670 131071 15421 50 vB.1
  have hAssocA:Associated (gcd QA HB) (gcd HT HB):=by
    rw [hQAeq]
    exact gcd_mul_left_plain_associated HT qA HB hcopA
  have hAssocB:Associated (gcd QA QB) (gcd QA HB):=by
    rw [hQBeq]
    exact gcd_mul_right_plain_associated QA HB qB hcopB
  have hAssoc:=hAssocB.trans hAssocA
  have hHHT:gcd QA QB ∣ HT:=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_left HT HB)
  have hHHB:gcd QA QB ∣ HB:=
    hAssoc.dvd_iff_dvd_left.mpr (gcd_dvd_right HT HB)
  refine ⟨{
    QA:=QA,QB:=QB,QA_ne:=hQA,QB_ne:=hQB
    QA_flag:=hQAbox,QB_flag:=hQBbox
    common_divides_TCap:=?_,common_divides_B:=?_
    universal_vanishing:=?_}⟩
  · intro v
    exact hHHT.trans (commonGCD_dvd (TCapKernel u0 u1) bT v)
  · intro v
    exact hHHB.trans (commonGCD_dvd (BKernel u0 u1) bB v)
  · intro gamma P points hP hcard hvalues
    constructor
    · dsimp only [QA]
      rw [submoduleReconstructLinear_apply]
      exact specialization_eq_zero_of_agreements K
        45673740 131071 11193 78 252 181245 IRSProfile.domain u0 u1
        vA.1 vA.2 (by decide +kernel) (by decide +kernel) P gamma points hP hcard hvalues
    · dsimp only [QB]
      rw [submoduleReconstructLinear_apply]
      exact specialization_eq_zero_of_agreements K
        30086670 131071 15421 50 166 181245 IRSProfile.domain u0 u1
        vB.1 vB.2 (by decide +kernel) (by decide +kernel) P gamma points hP hcard hvalues
end
end ProximityPrize.SubmissionLower.Lower80899.Selection

namespace ProximityPrize.SubmissionLower.Lower80899.Caps
open ProximityPrize.Benchmark RCN100 RCN119 RCN180 RCN081 RCN234 RCN156 RCN130
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
abbrev K:=IRSProfile.Field
abbrev I:=IRSProfile.Index
abbrev P4:=MvPolynomial (Fin 4) K
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev AKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 23924340 131071 76330 39 132 IRSProfile.domain u0 u1
abbrev TCapKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 45673740 131071 11193 78 252 IRSProfile.domain u0 u1
abbrev BKernel (u0 u1:I → K) :=
  ConstraintKernel (K:=K) 30086670 131071 15421 50 166 IRSProfile.domain u0 u1
theorem gateA : Fintype.card I * localRankBound 132 76330 39 < coefficientCount 23924340 131071 76330 39 := by
  rw [MovingFiberKernels6815.A.rank_exact, MovingFiberKernels6815.A.coefficient_exact]
  norm_num [I, IRSProfile.Index]
theorem gateB : Fintype.card I * localRankBound 166 15421 50 < coefficientCount 30086670 131071 15421 50 := by
  rw [MovingFiberKernels6815.B.rank_exact, MovingFiberKernels6815.B.coefficient_exact]
  norm_num [I, IRSProfile.Index]
theorem full_divisor_mem_box (D w L s m:ℕ)
    (gate:Fintype.card I * localRankBound m L s < coefficientCount D w L s)
    (u0 u1:I → K) (F:P4)
    (hdiv:∀ v:ConstraintKernel (K:=K) D w L s m IRSProfile.domain u0 u1,
      F ∣ reconstruct K D w L s v.1) :
    F ∈ globalCoefficientBox K D w L s:=by
  classical
  obtain ⟨a,ha,hk⟩:=exists_nonzero_kernel_array (I:=I)
    K D w L s m IRSProfile.domain u0 u1 gate
  let v:ConstraintKernel (K:=K) D w L s m IRSProfile.domain u0 u1:=
    ⟨a,LinearMap.mem_ker.mpr hk⟩
  have hQ:reconstruct K D w L s a ≠ 0:=reconstruct_ne_zero K D w L s a ha
  exact mem_flagGlobalCoefficientBox_of_dvd F (reconstruct K D w L s a)
    D w L s hQ (hdiv v) (reconstruct_mem_globalCoefficientBox K D w L s a)
theorem full_A_divisor_mem_box (u0 u1:I → K) (F:P4) (_hF:F ≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 23924340 131071 76330 39 v.1) :
    F ∈ globalCoefficientBox K 23924340 131071 76330 39:=
  full_divisor_mem_box 23924340 131071 76330 39 132 gateA u0 u1 F hdiv
theorem full_B_divisor_mem_box (u0 u1:I → K) (F:P4) (_hF:F ≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 30086670 131071 15421 50 v.1) :
    F ∈ globalCoefficientBox K 30086670 131071 15421 50:=
  full_divisor_mem_box 30086670 131071 15421 50 166 gateB u0 u1 F hdiv
theorem common_A_ys_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 23924340 131071 76330 39 v.1) :
    wt residualYSWeights F ≤ 182:=by
  have hbox:=full_A_divisor_mem_box u0 u1 F hF hdiv
  have hcaps:=(mem_flagGlobalCoefficientBox_iff F
    23924340 131071 76330 39 (by decide +kernel)).mp hbox
  have hr:wt residualSWeights F ≤ 39:=hcaps.2.1
  have hw:=residualYS_mul_le_contact_add_slope F 131071 (by decide +kernel)
  have hc:wt (contactWeights 131071) F ≤ 23924340:=by omega
  omega
theorem common_A_slope_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:AKernel u0 u1,F ∣ reconstruct K 23924340 131071 76330 39 v.1) :
    wt residualSWeights F ≤ 39:=
  ((mem_flagGlobalCoefficientBox_iff F 23924340 131071 76330 39 (by decide +kernel)).mp
    (full_A_divisor_mem_box u0 u1 F hF hdiv)).2.1
theorem common_B_slope_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 30086670 131071 15421 50 v.1) :
    wt residualSWeights F ≤ 50:=
  ((mem_flagGlobalCoefficientBox_iff F 30086670 131071 15421 50 (by decide +kernel)).mp
    (full_B_divisor_mem_box u0 u1 F hF hdiv)).2.1
theorem common_B_ys_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:BKernel u0 u1,F ∣ reconstruct K 30086670 131071 15421 50 v.1) :
    wt residualYSWeights F ≤ 229:=by
  have hcaps:=(mem_flagGlobalCoefficientBox_iff F
    30086670 131071 15421 50 (by decide +kernel)).mp
    (full_B_divisor_mem_box u0 u1 F hF hdiv)
  have hr:wt residualSWeights F ≤ 50:=hcaps.2.1
  have hc:wt (contactWeights 131071) F ≤ 30086670 - 1:=hcaps.2.2
  have hw:=residualYS_mul_le_contact_add_slope F 131071 (by decide +kernel)
  omega
theorem common_TCap_total_le (u0 u1:I → K) (F:P4) (hF:F ≠ 0)
    (hdiv:∀ v:TCapKernel u0 u1,F ∣ reconstruct K 45673740 131071 11193 78 v.1) :
    wt residualTotalWeights F ≤ 11192:=by
  by_contra hnot
  have ht:11193 ≤ wt residualTotalWeights F:=by omega
  have hdivK:∀ v:TCapKernel u0 u1,
      F ∣ kernelReconstructLinear (K:=K)
        45673740 131071 11193 78 252 IRSProfile.domain u0 u1 v:=by
    intro v
    simpa only [kernelReconstructLinear_apply] using hdiv v
  have hq:∀ v:TCapKernel u0 u1,
      quotientPolynomial
        (kernelReconstructLinear (K:=K) (I:=I)
          45673740 131071 11193 78 252 IRSProfile.domain u0 u1)
        F hdivK v ∈ globalCoefficientBox K 45673740 131071 0 78:=by
    have h:=LocatorLowQuotient.quotient_box_of_full_divisor (K:=K) (I:=I)
      45673740 131071 11193 78 252 0 11193 0
      IRSProfile.domain u0 u1 F hF hdivK (Nat.zero_le _) ht (Nat.zero_le _)
    intro v
    simpa only [Nat.sub_zero,show 11193 - 11193=0 by decide] using h v
  have hobs:=common_divisor_dimension_obstruction (K:=K) (I:=I)
    45673740 131071 11193 78 252 45673740 0 78
    IRSProfile.domain u0 u1 F hF hdivK hq
  rw [show Fintype.card I=262144 by norm_num [I,IRSProfile.Index]] at hobs
  rw [MovingFiberKernels6815.TCap.nullity_exact] at hobs
  exact (not_lt_of_ge hobs) MovingFiberKernels6815.TCap.quotient_count_lt
end
end Caps
end ProximityPrize.SubmissionLower.Lower80899

namespace ProximityPrize.SubmissionLower.Lower80899.Selection.SelectedPair
open RCN100 RCN180 RCN234 RCN156
noncomputable section
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
theorem common_total_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualTotalWeights (gcd S.QA S.QB) ≤ 11192:=
  Caps.common_TCap_total_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_TCap
theorem common_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualYSWeights (gcd S.QA S.QB) ≤ 229:=
  Caps.common_B_ys_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B
theorem common_slope_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualSWeights (gcd S.QA S.QB) ≤ 50:=
  Caps.common_B_slope_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B
end
end ProximityPrize.SubmissionLower.Lower80899.Selection.SelectedPair
end MergedPart2
