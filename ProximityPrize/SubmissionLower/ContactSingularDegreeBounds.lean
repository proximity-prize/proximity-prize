import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSingularAuxiliary

/-! .











 -/

namespace ProximityPrize.SubmissionLower.ContactSingularDegreeBounds

open ContactSingularAuxiliary ContactFactorCaps ContactFactorCover

noncomputable section

variable {K : Type*} [Field K]

def embedCoefficients (K : Type*) [Field K] :
    CoefficientRing K →+* MvPolynomial (Fin 4) K :=
  (collectR K).symm.toRingHom.comp Polynomial.C

theorem collectR_X_other (i : RemainingCoordinates) :
    collectR K (MvPolynomial.X (i : Fin 4)) = Polynomial.C (MvPolynomial.X i) := by
  simp [collectR, MvPolynomial.renameEquiv_apply,
    Equiv.optionSubtypeNe_symm_apply, i.property]

theorem collectR_rename_remaining (P : CoefficientRing K) :
    collectR K (MvPolynomial.rename Subtype.val P) = Polynomial.C P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [collectR, MvPolynomial.renameEquiv_apply]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, MvPolynomial.rename_X, hP, collectR_X_other]

theorem embedCoefficients_eq_rename (P : CoefficientRing K) :
    embedCoefficients K P = MvPolynomial.rename Subtype.val P := by
  apply (collectR K).injective
  rw [collectR_rename_remaining]
  exact (collectR K).apply_symm_apply (Polynomial.C P)

def liftedCoefficient (F : MvPolynomial (Fin 4) K) (n : ℕ) :
    MvPolynomial (Fin 4) K := embedCoefficients K ((collectR K F).coeff n)

theorem liftedCoefficient_R_degree (F : MvPolynomial (Fin 4) K) (n : ℕ) :
    (liftedCoefficient F n).degreeOf 2 = 0 := by
  rw [← collectR_natDegree]
  change ((collectR K) ((collectR K).symm (Polynomial.C ((collectR K F).coeff n)))).natDegree = 0
  rw [AlgEquiv.apply_symm_apply, Polynomial.natDegree_C]

/-- .
 -/
theorem liftedCoefficient_support
    (F : MvPolynomial (Fin 4) K) (n : ℕ) (e : Fin 4 →₀ ℕ)
    (he : e ∈ (liftedCoefficient F n).support) :
    ∃ d ∈ F.support, ∀ i, e i ≤ d i := by
  classical
  have heR : e 2 = 0 := by
    have hh := MvPolynomial.monomial_le_degreeOf (2 : Fin 4) he
    rw [liftedCoefficient_R_degree] at hh
    omega
  change e ∈ (embedCoefficients K ((collectR K F).coeff n)).support at he
  rw [embedCoefficients_eq_rename,
    MvPolynomial.support_rename_of_injective Subtype.val_injective] at he
  obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp he
  have hopt : u.optionElim n ∈
      (MvPolynomial.rename (Equiv.optionSubtypeNe (2 : Fin 4)).symm F).support :=
    (MvPolynomial.mem_support_coeff_optionEquivLeft (R := K)).mp hu
  rw [MvPolynomial.support_rename_of_injective
    (Equiv.optionSubtypeNe (2 : Fin 4)).symm.injective] at hopt
  obtain ⟨d, hd, hdu⟩ := Finset.mem_image.mp hopt
  refine ⟨d, hd, ?_⟩
  intro i
  by_cases hi : i = 2
  · subst i
    rw [heR]
    exact Nat.zero_le _
  · have hev : e i = u ⟨i, hi⟩ := by
      rw [← heu]
      exact Finsupp.mapDomain_apply Subtype.val_injective u ⟨i, hi⟩
    have huv := congrArg
      (fun f : Option RemainingCoordinates →₀ ℕ =>
        f ((Equiv.optionSubtypeNe (2 : Fin 4)).symm i)) hdu
    rw [Finsupp.mapDomain_apply (Equiv.optionSubtypeNe (2 : Fin 4)).symm.injective] at huv
    have hindex : (Equiv.optionSubtypeNe (2 : Fin 4)).symm i = some ⟨i, hi⟩ := by
      simp [Equiv.optionSubtypeNe_symm_apply, hi]
    rw [hindex, Finsupp.optionElim_apply_some] at huv
    exact le_of_eq (hev.trans huv.symm)

theorem weight_mono_fin4 (weights : Fin 4 → ℕ) (e d : Fin 4 →₀ ℕ)
    (h : ∀ i, e i ≤ d i) : Finsupp.weight weights e ≤ Finsupp.weight weights d := by
  rw [weight_fin4, weight_fin4]
  gcongr <;> exact h _

theorem liftedCoefficient_weight_le (weights : Fin 4 → ℕ)
    (F : MvPolynomial (Fin 4) K) (n : ℕ) :
    MvPolynomial.weightedTotalDegree weights (liftedCoefficient F n) ≤
      MvPolynomial.weightedTotalDegree weights F := by
  apply (weightedTotalDegree_le_iff weights _ _).mpr
  intro e he
  obtain ⟨d, hd, hed⟩ := liftedCoefficient_support F n e he
  exact (weight_mono_fin4 weights e d hed).trans (MvPolynomial.le_weightedTotalDegree weights hd)

theorem pderiv_weight_le (weights : Fin 4 → ℕ)
    (F : MvPolynomial (Fin 4) K) (i : Fin 4) :
    MvPolynomial.weightedTotalDegree weights (MvPolynomial.pderiv i F) ≤
      MvPolynomial.weightedTotalDegree weights F := by
  apply (weightedTotalDegree_le_iff weights _ _).mpr
  intro e he
  have hd := ContactTaylorNumerators.support_before_pderiv i F e he
  have hle : Finsupp.weight weights e ≤
      Finsupp.weight weights (e + Finsupp.single i 1) := by
    rw [map_add]
    exact Nat.le_add_right _ _
  exact hle.trans (MvPolynomial.le_weightedTotalDegree weights hd)

/-- . -/
theorem degreeOf_det_le_uniform (N a : ℕ)
    (M : Matrix (Fin N) (Fin N) (MvPolynomial (Fin 5) K))
    (hM : ∀ i j, (M i j).degreeOf 4 ≤ a) : M.det.degreeOf 4 ≤ N * a := by
  classical
  rw [Matrix.det_apply']
  apply (MvPolynomial.degreeOf_sum_le (4 : Fin 5) Finset.univ _).trans
  apply Finset.sup_le_iff.mpr
  intro σ _
  have hprod : (∏ i, M (σ i) i).degreeOf (4 : Fin 5) ≤ N * a := by
    calc
      _ ≤ ∑ i : Fin N, (M (σ i) i).degreeOf (4 : Fin 5) :=
        MvPolynomial.degreeOf_prod_le (4 : Fin 5) Finset.univ _
      _ ≤ ∑ _i : Fin N, a := Finset.sum_le_sum fun i _ => hM (σ i) i
      _ = N * a := by simp
  have hsign : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 5) K)).degreeOf 4 ≤ 0 := by
    simpa only [map_intCast] using
      (MvPolynomial.degreeOf_C (((Equiv.Perm.sign σ : ℤ) : K)) (4 : Fin 5)).le
  exact (MvPolynomial.degreeOf_mul_le (4 : Fin 5) _ _).trans
    ((Nat.add_le_add hsign hprod).trans_eq (zero_add _))

/-- .
 -/
def weightedCoefficientEmbedding (K : Type*) [Field K] (weights : Fin 4 → ℕ) :
    CoefficientRing K →+* MvPolynomial (Fin 5) K :=
  (weightedLift K weights).comp (embedCoefficients K)

theorem degree_weightedCoefficient (weights : Fin 4 → ℕ)
    (F : MvPolynomial (Fin 4) K) (n : ℕ) :
    (weightedCoefficientEmbedding K weights ((collectR K F).coeff n)).degreeOf 4 ≤
      MvPolynomial.weightedTotalDegree weights F := by
  change (weightedLift K weights (liftedCoefficient F n)).degreeOf 4 ≤ _
  rw [degree_weightedLift]
  exact liftedCoefficient_weight_le weights F n

/-- . -/
theorem eliminateR_weight_le (weights : Fin 4 → ℕ)
    (F G : MvPolynomial (Fin 4) K) (a : ℕ)
    (hF : MvPolynomial.weightedTotalDegree weights F ≤ a)
    (hG : MvPolynomial.weightedTotalDegree weights G ≤ a) :
    MvPolynomial.weightedTotalDegree weights (eliminateR F G) ≤
      (F.degreeOf 2 + G.degreeOf 2) * a := by
  let ψ := weightedCoefficientEmbedding K weights
  let M := Polynomial.sylvester (collectR K F) (collectR K G)
    (collectR K F).natDegree (collectR K G).natDegree
  have hentry : ∀ i j, ((ψ.mapMatrix M) i j).degreeOf (4 : Fin 5) ≤ a := by
    intro i j
    induction j using Fin.addCases with
    | «left» j =>
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, M, Polynomial.sylvester,
          Matrix.of_apply, Fin.addCases_left]
        split_ifs
        · exact (degree_weightedCoefficient weights G _).trans hG
        · simp
    | «right» j =>
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, M, Polynomial.sylvester,
          Matrix.of_apply, Fin.addCases_right]
        split_ifs
        · exact (degree_weightedCoefficient weights F _).trans hF
        · simp
  have hdet := degreeOf_det_le_uniform
    ((collectR K F).natDegree + (collectR K G).natDegree) a (ψ.mapMatrix M) hentry
  rw [← ψ.map_det] at hdet
  change (weightedLift K weights (eliminateR F G)).degreeOf 4 ≤ _ at hdet
  rw [degree_weightedLift, collectR_natDegree, collectR_natDegree] at hdet
  exact hdet

theorem weightedTotalDegree_prod_le {ι : Type*} (weights : Fin 4 → ℕ)
    (I : Finset ι) (f : ι → MvPolynomial (Fin 4) K) :
    MvPolynomial.weightedTotalDegree weights (∏ i ∈ I, f i) ≤
      ∑ i ∈ I, MvPolynomial.weightedTotalDegree weights (f i) := by
  rw [← degree_weightedLift, map_prod]
  simpa only [degree_weightedLift] using
    (MvPolynomial.degreeOf_prod_le (4 : Fin 5) I (fun i => weightedLift K weights (f i)))

/-- . -/
theorem sum_weighted_degrees_le_of_prod_dvd {ι : Type*} (weights : Fin 4 → ℕ)
    (I : Finset ι) (f : ι → MvPolynomial (Fin 4) K) (Q : MvPolynomial (Fin 4) K)
    (hQ : Q ≠ 0) (hdiv : (∏ i ∈ I, f i) ∣ Q) :
    (∑ i ∈ I, MvPolynomial.weightedTotalDegree weights (f i)) ≤
      MvPolynomial.weightedTotalDegree weights Q := by
  classical
  have hprod : (∏ i ∈ I, f i) ≠ 0 := by
    intro hz
    obtain ⟨T, hT⟩ := hdiv
    exact hQ (by rw [hT, hz, zero_mul])
  have hf : ∀ i ∈ I, f i ≠ 0 := Finset.prod_ne_zero_iff.mp hprod
  have hmap : (∏ i ∈ I, weightedLift K weights (f i)) ∣ weightedLift K weights Q := by
    obtain ⟨T, hT⟩ := hdiv
    refine ⟨weightedLift K weights T, ?_⟩
    rw [hT, map_mul, map_prod]
  calc
    (∑ i ∈ I, MvPolynomial.weightedTotalDegree weights (f i)) =
        ∑ i ∈ I, (weightedLift K weights (f i)).degreeOf (4 : Fin 5) := by
      simp only [degree_weightedLift]
    _ = (∏ i ∈ I, weightedLift K weights (f i)).degreeOf (4 : Fin 5) :=
      (MvPolynomial.degreeOf_prod_eq I _
        (fun i hi => weightedLift_ne_zero weights (f i) (hf i hi))).symm
    _ ≤ (weightedLift K weights Q).degreeOf (4 : Fin 5) :=
      ContactGeometricFactorCover.coordinate_degree_le_of_dvd (4 : Fin 5) _ _ hmap
        (weightedLift_ne_zero weights Q hQ)
    _ = MvPolynomial.weightedTotalDegree weights Q := degree_weightedLift weights Q

theorem singularContribution_weight_le (weights : Fin 4 → ℕ)
    (F : MvPolynomial (Fin 4) K) (s : ℕ) (hs : 1 ≤ s) (hR : F.degreeOf 2 ≤ s) :
    MvPolynomial.weightedTotalDegree weights (singularContribution F) ≤
      (2 * s - 1) * MvPolynomial.weightedTotalDegree weights F := by
  unfold singularContribution
  split_ifs with h
  · have hfactor : 1 ≤ 2 * s - 1 := by omega
    simpa only [one_mul] using
      (Nat.mul_le_mul_right (MvPolynomial.weightedTotalDegree weights F) hfactor)
  · have hpos : 0 < F.degreeOf 2 := Nat.pos_of_ne_zero h
    have hder := ContactRegularFactorGate.R_derivative_degree_lt F hpos
    have hfactor : F.degreeOf 2 + (MvPolynomial.pderiv (2 : Fin 4) F).degreeOf 2 ≤
        2 * s - 1 := by omega
    exact (eliminateR_weight_le weights F (MvPolynomial.pderiv (2 : Fin 4) F)
      (MvPolynomial.weightedTotalDegree weights F) le_rfl (pderiv_weight_le weights F 2)).trans
      (Nat.mul_le_mul_right _ hfactor)

/-- .
 -/
theorem singularAuxiliary_weight_le (weights : Fin 4 → ℕ)
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (s : ℕ) (hs : 1 ≤ s) (hR : Q.degreeOf 2 ≤ s) :
    MvPolynomial.weightedTotalDegree weights (singularAuxiliary Q) ≤
      (2 * s - 1) * MvPolynomial.weightedTotalDegree weights Q := by
  classical
  calc
    _ ≤ ∑ F ∈ activeFactors Q,
        MvPolynomial.weightedTotalDegree weights (singularContribution F) :=
      weightedTotalDegree_prod_le weights (activeFactors Q) singularContribution
    _ ≤ ∑ F ∈ activeFactors Q,
        (2 * s - 1) * MvPolynomial.weightedTotalDegree weights F := by
      apply Finset.sum_le_sum
      intro F hF
      exact singularContribution_weight_le weights F s hs
        ((ContactFactorCaps.degreeOf_le_of_dvd (2 : Fin 4) F Q
          (activeFactors_spec Q F hF).2.1 hQ).trans hR)
    _ = (2 * s - 1) * ∑ F ∈ activeFactors Q, MvPolynomial.weightedTotalDegree weights F := by
      rw [Finset.mul_sum]
    _ ≤ (2 * s - 1) * MvPolynomial.weightedTotalDegree weights Q :=
      Nat.mul_le_mul_left _ (sum_weighted_degrees_le_of_prod_dvd weights
        (activeFactors Q) id Q hQ (activeFactors_product_dvd Q hQ))

/-- .
 -/
theorem singularAuxiliary_input_caps
    (Q : MvPolynomial (Fin 4) K) (D w L s : ℕ)
    (hQ : Q ≠ 0) (hs : 1 ≤ s)
    (hbox : Q ∈ ContactInterpolation.globalCoefficientBox K D w L s) :
    MvPolynomial.weightedTotalDegree seedWeights (singularAuxiliary Q) ≤ (2 * s - 1) * L ∧
      MvPolynomial.weightedTotalDegree (contactWeights w) (singularAuxiliary Q) <
        (2 * s - 1) * D := by
  have hD : 0 < D := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hQ
    have hh := (hbox hd).2.2
    omega
  have hcaps := (mem_globalCoefficientBox_iff Q D w L s hD).mp hbox
  have hR : Q.degreeOf 2 ≤ s := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    exact (hbox hd).2.1
  have hpositive : 0 < 2 * s - 1 := by omega
  refine ⟨(singularAuxiliary_weight_le seedWeights Q hQ s hs hR).trans
    (Nat.mul_le_mul_left _ hcaps.1), ?_⟩
  have hle := (singularAuxiliary_weight_le (contactWeights w) Q hQ s hs hR).trans
    (Nat.mul_le_mul_left _ hcaps.2.2)
  exact hle.trans_lt (Nat.mul_lt_mul_of_pos_left (by omega : D - 1 < D) hpositive)

/-- .
 -/
theorem singularAuxiliary_nonzero_mem_box
    (Q : MvPolynomial (Fin 4) K) (D w L s p : ℕ) [CharP K p]
    (hQ : Q ≠ 0) (hs : 1 ≤ s) (hsmall : s < p)
    (hbox : Q ∈ ContactInterpolation.globalCoefficientBox K D w L s) :
    singularAuxiliary Q ≠ 0 ∧
      singularAuxiliary Q ∈ ContactInterpolation.globalCoefficientBox K
        ((2 * s - 1) * D) w ((2 * s - 1) * L) 0 := by
  have hR : Q.degreeOf 2 ≤ s := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro d hd
    exact (hbox hd).2.1
  have hjR := singularAuxiliary_R_degree Q hQ p (hR.trans_lt hsmall)
  have hc := singularAuxiliary_input_caps Q D w L s hQ hs hbox
  refine ⟨singularAuxiliary_nonzero Q hQ p (hR.trans_lt hsmall), ?_⟩
  intro d hd
  have hseed := (MvPolynomial.le_weightedTotalDegree seedWeights hd).trans hc.1
  have hcontact := (MvPolynomial.le_weightedTotalDegree (contactWeights w) hd).trans_lt hc.2
  have hslope := MvPolynomial.monomial_le_degreeOf (f := singularAuxiliary Q) (2 : Fin 4) hd
  rw [hjR] at hslope
  rw [seed_weight] at hseed
  rw [contact_weight] at hcontact
  exact ⟨hseed, hslope, hcontact⟩


end
end ProximityPrize.SubmissionLower.ContactSingularDegreeBounds
