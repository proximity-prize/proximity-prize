import ProximityPrize.SubmissionLower.Koala6844VirtualShortSylvester


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open RCN081 RCN156 RCN234 RCN261 RCN290 RCN293

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000

variable {K : Type*} [Field K]

theorem eliminateR_weight_sharp (w : Fin 4 → ℕ) (hw : w 2 = 1)
    (F G : MvPolynomial (Fin 4) K) (a b : ℕ)
    (hF : F.weightedTotalDegree w ≤ a) (hG : G.weightedTotalDegree w ≤ b) :
    (eliminateR F G).weightedTotalDegree w ≤ F.degreeOf 2*b+G.degreeOf 2*a-F.degreeOf 2*G.degreeOf 2 := by
  let m := F.degreeOf 2
  let n := G.degreeOf 2
  let φ := embedCoefficients K
  have hm : (collectR K F).natDegree = m := collectR_natDegree F
  have hn : (collectR K G).natDegree = n := collectR_natDegree G
  have heq : eliminateR F G = Polynomial.resultant ((collectR K F).map φ) ((collectR K G).map φ) m n := by
    rw [Polynomial.resultant_map_map]
    change φ (Polynomial.resultant (collectR K F) (collectR K G)) = _
    rw [hm,hn]
  rw [heq]
  apply resultant_weighted_sharp _ _ m n a b w
  · intro j hj
    change ((collectR K F).map φ).coeff j ≠ 0 at hj
    rw [Polynomial.coeff_map] at hj ⊢
    change (liftedCoefficient F j).weightedTotalDegree w+j ≤ a
    have h := liftedCoefficient_weight_add_le w F j hj
    simpa only [hw,Nat.mul_one] using h.trans hF
  · intro j hj
    rw [Polynomial.coeff_map] at hj ⊢
    change (liftedCoefficient G j).weightedTotalDegree w+j ≤ b
    have h := liftedCoefficient_weight_add_le w G j hj
    simpa only [hw,Nat.mul_one] using h.trans hG

private def keepCoordinates : Fin 3 ≃ RemainingCoordinates :=
  Equiv.ofBijective (fun i : Fin 3 => ⟨(![0,1,3] : Fin 3 → Fin 4) i, by fin_cases i <;> decide⟩)
    (by decide)

private theorem compose_eval_resultant (f : Polynomial K) (g : K) (P : CoefficientRing K) :
    MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X,f,Polynomial.C g]
        (MvPolynomial.rename keepCoordinates.symm P) =
      RCN319.specialization K f g (MvPolynomial.rename Subtype.val P) := by
  let e := MvPolynomial.eval₂Hom (Polynomial.C : K →+* Polynomial K) ![Polynomial.X,f,Polynomial.C g]
  have h : e.comp (MvPolynomial.rename keepCoordinates.symm).toRingHom =
      (RCN319.specialization K f g).toRingHom.comp (MvPolynomial.rename Subtype.val).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [e,RCN319.specialization]
    · intro i
      obtain ⟨j,rfl⟩ := keepCoordinates.surjective i
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,RingHom.coe_coe,
        MvPolynomial.rename_X,Equiv.symm_apply_apply]
      fin_cases j <;> simp [e,keepCoordinates,RCN319.specialization]
  exact DFunLike.congr_fun h P

theorem exists_weighted_R_resultant
    (F G : MvPolynomial (Fin 4) K) (hF : Irreducible F) (hr : 0 < F.degreeOf 2) (hG : ¬F ∣ G)
    (y u t v : ℕ)
    (hFY : wt residualYSWeights F ≤ y) (hGY : wt residualYSWeights G ≤ u)
    (hFT : wt residualTotalWeights F ≤ t) (hGT : wt residualTotalWeights G ≤ v) :
    let r := F.degreeOf 2
    let s := G.degreeOf 2
    ∃ J : MvPolynomial (Fin 3) K, J ≠ 0 ∧
      J.degreeOf 1 ≤ s*y+r*u-r*s ∧
      J.weightedTotalDegree ![0,1,1] ≤ s*t+r*v-r*s ∧
      ∀ f : Polynomial K, ∀ g : K,
        RCN319.specialization K f g F = 0 → RCN319.specialization K f g G = 0 →
          MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X,f,Polynomial.C g] J = 0 := by
  classical
  let P := Polynomial.resultant (collectR K F) (collectR K G)
  let E := eliminateR F G
  let J := MvPolynomial.rename keepCoordinates.symm P
  have hE : E ≠ 0 := eliminateR_nonzero F G hF hr hG
  have heq : E = MvPolynomial.rename Subtype.val P := embedCoefficients_eq_rename P
  have hP : P ≠ 0 := by
    intro hz
    exact hE (by rw [heq,hz,map_zero])
  have hJ : J ≠ 0 := by
    intro hz
    apply hP
    apply MvPolynomial.rename_injective _ keepCoordinates.symm.injective
    simpa only [map_zero] using hz
  have hY := eliminateR_weight_sharp residualYSWeights rfl F G y u hFY hGY
  have hT := eliminateR_weight_sharp residualTotalWeights rfl F G t v hFT hGT
  have hsupport (e : Fin 3 →₀ ℕ) (he : e ∈ J.support) :
      ∃ d ∈ E.support, e 1 = d 1 ∧ e 2 = d 3 ∧ d 2 = 0 := by
    change e ∈ (MvPolynomial.rename keepCoordinates.symm P).support at he
    rw [MvPolynomial.support_rename_of_injective keepCoordinates.symm.injective] at he
    obtain ⟨z,hz,heq'⟩ := Finset.mem_image.mp he
    let d := Finsupp.mapDomain Subtype.val z
    have hd : d ∈ E.support := by
      rw [heq,MvPolynomial.support_rename_of_injective Subtype.val_injective]
      exact Finset.mem_image.mpr ⟨z,hz,rfl⟩
    refine ⟨d,hd,?_,?_,?_⟩
    · rw [←heq']
      have h1 := Finsupp.mapDomain_apply_of_injective keepCoordinates.symm.injective z (keepCoordinates 1)
      have h2 := Finsupp.mapDomain_apply_of_injective Subtype.val_injective z (keepCoordinates 1)
      rw [Equiv.symm_apply_apply] at h1
      exact h1.trans h2.symm
    · rw [←heq']
      have h1 := Finsupp.mapDomain_apply_of_injective keepCoordinates.symm.injective z (keepCoordinates 2)
      have h2 := Finsupp.mapDomain_apply_of_injective Subtype.val_injective z (keepCoordinates 2)
      rw [Equiv.symm_apply_apply] at h1
      exact h1.trans h2.symm
    · have h := MvPolynomial.monomial_le_degreeOf (2 : Fin 4) hd
      rw [eliminateR_R_degree] at h
      exact Nat.eq_zero_of_le_zero h
  refine ⟨J,hJ,?_,?_,?_⟩
  · rw [MvPolynomial.degreeOf_eq_sup]
    apply Finset.sup_le
    intro e he
    obtain ⟨d,hd,h1,_,h2⟩ := hsupport e he
    have hh := (MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans hY
    rw [weight_fin4] at hh
    change d 0*0+d 1*1+d 2*1+d 3*0 ≤ _ at hh
    simpa [h1,h2,Nat.add_comm] using hh
  · unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro e he
    obtain ⟨d,hd,h1,h2,hr0⟩ := hsupport e he
    have hh := (MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans hT
    rw [weight_fin4] at hh
    have heq'' : Finsupp.weight (![0,1,1] : Fin 3 → ℕ) e = d 1+d 3 := by
      rw [Finsupp.weight_apply,Finsupp.sum_fintype _ _ (fun _ => by simp),Fin.sum_univ_three]
      change e 0*0+e 1*1+e 2*1 = _
      omega
    rw [heq'']
    simpa [residualTotalWeights,hr0,Nat.add_comm] using hh
  · intro f g hf hg
    rw [compose_eval_resultant f g P,←heq]
    exact eliminateR_map_zero (RCN319.specialization K f g).toRingHom F G hr hf hg


private theorem reduced_resultant_cap (r s y u : ℕ) (hs : s ≤ u) :
    s*y+r*u-r*s = s*y+r*(u-s) := by
  rw [Nat.mul_sub_left_distrib, Nat.add_sub_assoc (Nat.mul_le_mul_left r hs)]

theorem resultant_cap_mono (r s R S y u : ℕ)
    (hr : r ≤ R) (hs : s ≤ S) (hR : R ≤ y) (hS : S ≤ u) :
    s*y+r*u-r*s ≤ S*y+R*u-R*S := by
  rw [reduced_resultant_cap _ _ _ _ (hs.trans hS), reduced_resultant_cap _ _ _ _ hS]
  have hstep (k : ℕ) (hk : k ≤ u) : k*y+R*(u-k) = k*(y-R)+R*u := by
    conv_lhs => rw [← Nat.sub_add_cancel hR, Nat.mul_add]
    rw [Nat.add_assoc,Nat.mul_comm k R,←Nat.mul_add, Nat.add_sub_of_le hk]
  calc
    _ ≤ s*y+R*(u-s) := Nat.add_le_add_left (Nat.mul_le_mul_right (u-s) hr) _
    _ ≤ S*y+R*(u-S) := by
      rw [hstep s (hs.trans hS),hstep S hS]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right (y-R) hs) _

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
