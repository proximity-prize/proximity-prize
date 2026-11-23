import ProximityPrize.SubmissionLower.RungSplit

set_option Elab.async false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

namespace CurveListPairResultant
open CJ0 Polynomial PolynomialDifferential MvPolynomial Sol1.C57 ReedSolomon.HiddenDerivative
open scoped Polynomial
open private row row_weight rowWeight rowWeight_last lowerMap lowerMap_injective lower_weight
  view_row input_total input_index output_index
  from ProximityPrize.SubmissionLower.RungSplit
open private resultant_weight from ProximityPrize.SubmissionLower.Fast076

noncomputable section

theorem coprime_fraction {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {F G:R[X]} (hF:F≠0) (hrel:IsRelPrime F G) :
    IsCoprime (F.map (algebraMap R (FractionRing R))) (G.map (algebraMap R (FractionRing R))):=by
  classical
  let φ:=algebraMap R (FractionRing R)
  have hinj:=IsFractionRing.injective R (FractionRing R)
  have hunit (f : (FractionRing R)[X]) (hf : IsUnit f) : IsCoprime f (G.map φ) := by
    obtain ⟨u,rfl⟩:=hf
    exact ⟨↑u⁻¹,0,by simp⟩
  letI:NormalizationMonoid R:=Classical.choice inferInstance
  letI:=UniqueFactorizationMonoid.toNormalizedGCDMonoid R
  refine UniqueFactorizationMonoid.induction_on_prime
    (P:=fun f:R[X] => f≠0→IsRelPrime f G→IsCoprime (f.map φ) (G.map φ)) F
    (fun h _ => (h rfl).elim) (fun f hu _ _ => hunit _ (hu.map (Polynomial.mapRingHom φ))) ?_ hF hrel
  intro a b ha hb ih _ hba
  have hbG : ¬ b ∣ G:=fun hd => hb.not_isUnit (hba (dvd_mul_right b a) hd)
  have hc : IsCoprime (b.map φ) (G.map φ) := by
    by_cases hd:b.natDegree=0
    · apply hunit
      have hl:b.coeff b.natDegree≠0:=leadingCoeff_ne_zero.mpr hb.ne_zero
      rw [hd] at hl
      rw [eq_C_of_natDegree_eq_zero hd,Polynomial.map_C]
      have hφ:φ (b.coeff 0)≠0:=by simpa only [map_zero] using hinj.ne hl
      exact (isUnit_iff_ne_zero.mpr hφ).map Polynomial.C
    · have hp := hb.irreducible.isPrimitive hd
      have hi:Irreducible (b.map φ):=hp.irreducible_iff_irreducible_map_fraction_map.mp hb.irreducible
      exact hi.coprime_iff_not_dvd.mpr (fun h => hbG (hp.dvd_of_fraction_map_dvd_fraction_map h))
  have haG : IsRelPrime a G := by
    intro z hd hg
    exact hba (hd.trans (dvd_mul_left a b)) hg
  rw [Polynomial.map_mul]
  exact hc.mul_left (ih ha haG)

private def eliminate (U W : DifferentialPolynomial K 2) : DifferentialPolynomial K 1 :=
  let P:=topPresentation 1 U
  let Q:=topPresentation 1 W
  if P.natDegree=0 then P.coeff 0 else P.resultant Q P.natDegree Q.natDegree

private theorem eliminate_ne_zero {U W : DifferentialPolynomial K 2}
    (hU:U≠0) (hrel:IsRelPrime U W):eliminate U W≠0:=by
  let E:=topPresentation (E:=K) 1
  let P:=E U
  let Q:=E W
  have hn:P≠0:=fun h => hU (E.injective (h.trans E.map_zero.symm))
  change (if P.natDegree=0 then P.coeff 0 else P.resultant Q P.natDegree Q.natDegree)≠0
  split_ifs with h
  · have hl : P.coeff P.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hn
    rwa [h] at hl
  · have hrel' : IsRelPrime P Q := by
      intro d hP hQ
      obtain ⟨a,ha⟩:=hP
      obtain ⟨b,hb⟩:=hQ
      have ha' : E.symm d ∣ U := ⟨E.symm a,by
        simpa only [P,AlgEquiv.symm_apply_apply,map_mul] using congrArg E.symm ha⟩
      have hb' : E.symm d ∣ W := ⟨E.symm b,by
        simpa only [Q,AlgEquiv.symm_apply_apply,map_mul] using congrArg E.symm hb⟩
      have hu:=(hrel ha' hb').map E.toRingHom
      change IsUnit (E (E.symm d)) at hu
      rwa [AlgEquiv.apply_symm_apply] at hu
    let φ:=algebraMap (DifferentialPolynomial K 1) (FractionRing (DifferentialPolynomial K 1))
    have hinj:=IsFractionRing.injective (DifferentialPolynomial K 1) (FractionRing (DifferentialPolynomial K 1))
    have hres:=Polynomial.resultant_ne_zero (P.map φ) (Q.map φ) (coprime_fraction hn hrel')
    rw [Polynomial.natDegree_map_eq_of_injective hinj, Polynomial.natDegree_map_eq_of_injective hinj,
      Polynomial.resultant_map_map] at hres
    exact fun hz => hres (by rw [hz,map_zero])

private theorem eliminate_root {U W : DifferentialPolynomial K 2} (f : K[X])
    (hU:differentialSpecialization U f=0) (hW:differentialSpecialization W f=0) :
    differentialSpecialization (eliminate U W) f=0:=by
  let P:=topPresentation 1 U
  let Q:=topPresentation 1 W
  let ψ:=(differentialSpecializationHom (d:=1) f).toRingHom
  have he:P.eval₂ ψ (hasseDeriv 2 f)=0:=(topPresentation_eval 1 U f).trans hU
  have hg:Q.eval₂ ψ (hasseDeriv 2 f)=0:=(topPresentation_eval 1 W f).trans hW
  change ψ (if P.natDegree=0 then P.coeff 0 else P.resultant Q P.natDegree Q.natDegree)=0
  split_ifs with hz
  · have hh := congrArg (fun R : Polynomial (DifferentialPolynomial K 1) =>
      R.eval₂ ψ (hasseDeriv 2 f)) (eq_C_of_natDegree_eq_zero hz)
    change P.eval₂ ψ (hasseDeriv 2 f)=_ at hh
    rw [Polynomial.eval₂_C] at hh
    exact hh.symm.trans he
  · exact map_resultant_eq_zero_of_common_root ψ P Q le_rfl le_rfl (Or.inl hz) (hasseDeriv 2 f)
      ((Polynomial.eval₂_eq_eval_map ψ).symm.trans he) ((Polynomial.eval₂_eq_eval_map ψ).symm.trans hg)

private theorem eliminate_weight (a B C : ℕ) (w : JetVariable 1 → ℕ)
    {U W:DifferentialPolynomial K 2}
    (hU:U.weightedTotalDegree (CJ0_5.inputWeight a w)≤B)
    (hW:W.weightedTotalDegree (CJ0_5.inputWeight a w)≤B)
    (hUc:jetDegree U (Fin.last 2)≤C) (hWc:jetDegree W (Fin.last 2)≤C) (hC:0 < C) :
    (eliminate U W).weightedTotalDegree w≤2*C*B:=by
  let P:=topPresentation 1 U
  let Q:=topPresentation 1 W
  let v:Fin 3→ℕ:=fun j => rowWeight a w j.castSucc
  let P' := K1_13_5_1.view (row U)
  let Q' := K1_13_5_1.view (row W)
  have hpmap:P' = P.map lowerMap:=view_row U
  have hqmap:Q' = Q.map lowerMap:=view_row W
  have hm:P'.natDegree=P.natDegree:=hpmap ▸ natDegree_map_eq_of_injective lowerMap_injective P
  have hn:Q'.natDegree=Q.natDegree:=hqmap ▸ natDegree_map_eq_of_injective lowerMap_injective Q
  have hC₁:P.natDegree≤C:=(topPresentation_degree 1 U).trans_le hUc
  have hC₂:Q.natDegree≤C:=(topPresentation_degree 1 W).trans_le hWc
  have hpw (i : ℕ) (hi : i ≤ P.natDegree) : (P'.coeff i).weightedTotalDegree v+a*i ≤ B := by
    have h:=K1_13_5_1.view_coeff_weight (rowWeight a w) (row U) i (by rwa [hm])
    rw [rowWeight_last,row_weight] at h
    exact h.trans hU
  have hqw (i : ℕ) (hi : i ≤ Q.natDegree) : (Q'.coeff i).weightedTotalDegree v+a*i ≤ B := by
    have h:=K1_13_5_1.view_coeff_weight (rowWeight a w) (row W) i (by rwa [hn])
    rw [rowWeight_last,row_weight] at h
    exact h.trans hW
  have happ:C*B+C*B=2*C*B:=by ring
  change (if P.natDegree=0 then P.coeff 0 else P.resultant Q P.natDegree Q.natDegree).weightedTotalDegree w≤_
  split_ifs with hz
  · have h := hpw 0 (Nat.zero_le _)
    rw [hpmap,Polynomial.coeff_map,lower_weight,Nat.mul_zero,Nat.add_zero] at h
    exact h.trans (by calc
      B=1*B:=by simp
      _≤C*B:=Nat.mul_le_mul_right B hC
      _≤2*C*B:=by omega)
  · have h := resultant_weight v a P' Q' P.natDegree Q.natDegree B B hpw hqw
    rw [hpmap,hqmap,Polynomial.resultant_map_map,lower_weight] at h
    exact (Nat.le_add_right ..).trans (h.trans ((Nat.add_le_add
      (Nat.mul_le_mul_right B hC₂) (Nat.mul_le_mul_right B hC₁)).trans_eq happ))

end
end CurveListPairResultant
