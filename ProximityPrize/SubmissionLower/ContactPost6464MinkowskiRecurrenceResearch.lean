import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactImplicitContactLift
import ProximityPrize.SubmissionLower.ContactTaylorNumerators
namespace ProximityPrize.SubmissionLower.ContactPost6464MinkowskiRecurrenceResearch
open scoped BigOperators
open ContactFactorCaps ContactImplicitContactLift ContactTaylorNumerators
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
def wt (weights:Fin 4 → ℕ) (P:Poly4 K):ℕ:=
  MvPolynomial.weightedTotalDegree weights P
theorem wt_mul_le (weights:Fin 4 → ℕ) (P Q:Poly4 K):
    wt weights (P*Q) ≤ wt weights P+wt weights Q:=
  weighted_mul_le weights P Q
theorem wt_add_le (weights:Fin 4 → ℕ) (P Q:Poly4 K):
    wt weights (P+Q) ≤ max (wt weights P) (wt weights Q):=
  weighted_add_le weights P Q
theorem wt_sub_le (weights:Fin 4 → ℕ) (P Q:Poly4 K):
    wt weights (P-Q) ≤ max (wt weights P) (wt weights Q):=by
  unfold wt
  rw [←degree_weightedLift,map_sub]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_sub_le (4:Fin 5)
      (weightedLift K weights P) (weightedLift K weights Q)
theorem wt_neg (weights:Fin 4 → ℕ) (P:Poly4 K):
    wt weights (-P)=wt weights P:=by
  unfold wt
  rw [←degree_weightedLift,map_neg,MvPolynomial.degreeOf_neg,
    degree_weightedLift]
theorem wt_pow_le (weights:Fin 4 → ℕ) (P:Poly4 K) (n:ℕ):
    wt weights (P^n) ≤ n*wt weights P:=by
  unfold wt
  rw [←degree_weightedLift,map_pow]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_pow_le (4:Fin 5) (weightedLift K weights P) n
theorem wt_C (weights:Fin 4 → ℕ) (c:K):
    wt weights (MvPolynomial.C c:Poly4 K)=0:=by
  unfold wt MvPolynomial.weightedTotalDegree
  simp
theorem wt_X (weights:Fin 4 → ℕ) (i:Fin 4):
    wt weights (MvPolynomial.X i:Poly4 K)=weights i:=by
  unfold wt
  exact weighted_X weights i
theorem wt_natCast (weights:Fin 4 → ℕ) (n:ℕ):
    wt weights (n:Poly4 K)=0:=by
  rw [←map_natCast (MvPolynomial.C:K →+*Poly4 K),wt_C]
theorem wt_sum_le (weights:Fin 4 → ℕ) (I:Finset ℕ)
    (f:ℕ → Poly4 K) (a:ℕ) (hf:∀ i∈I,wt weights (f i) ≤ a):
    wt weights (∑ i∈I,f i) ≤ a:=by
  unfold wt
  rw [←degree_weightedLift,map_sum]
  apply (MvPolynomial.degreeOf_sum_le (4:Fin 5) I
    (fun i => weightedLift K weights (f i))).trans
  apply Finset.sup_le
  intro i hi
  rw [degree_weightedLift]
  exact hf i hi
theorem wt_pderiv_le (weights:Fin 4 → ℕ) (P:Poly4 K)
    (i:Fin 4) (A:ℕ) (hP:wt weights P ≤ A):
    wt weights (MvPolynomial.pderiv i P) ≤ A-weights i:=
  pderiv_weight_sub_bound weights P i A hP
theorem wt_polyH_le (weights:Fin 4 → ℕ) (F:Poly4 K)
    (C:ℕ) (hF:wt weights F ≤ C):
    wt weights (polyH K F) ≤ C-weights 2:=
  wt_pderiv_le weights F 2 C hF
theorem wt_polyG_le (weights:Fin 4 → ℕ) (hX:weights 0=0)
    (F:Poly4 K) (C:ℕ) (hF:wt weights F ≤ C):
    wt weights (polyG K F) ≤ C+weights 2:=by
  have hx:=wt_pderiv_le weights F 0 C hF
  have hy:=wt_pderiv_le weights F 1 C hF
  have hR:wt weights (MvPolynomial.X (2:Fin 4):Poly4 K)=weights 2:=
    weighted_X weights 2
  have hm:=wt_mul_le weights (MvPolynomial.X (2:Fin 4):Poly4 K)
    (MvPolynomial.pderiv 1 F)
  have hsum:=wt_add_le weights (MvPolynomial.pderiv 0 F)
    (MvPolynomial.X (2:Fin 4)*MvPolynomial.pderiv 1 F)
  unfold polyG
  rw [wt_neg]
  exact hsum.trans (max_le (by omega) (by omega))
theorem numeratorStep_wt_le_minkowski
    (weights:Fin 4 → ℕ) (hX:weights 0=0)
    (F M:Poly4 K) (b A C:ℕ) (hR:weights 2 ≤ C)
    (hRR:2*weights 2 ≤ C) (hA:weights 2 ≤ A)
    (hF:wt weights F ≤ C) (hM:wt weights M ≤ A):
    wt weights (numeratorStep K F b M) ≤
      A+C+(C-weights 2):=by
  let H:=polyH K F
  let G:=polyG K F
  let R:Poly4 K:=MvPolynomial.X (2:Fin 4)
  let Hcap:=C-weights 2
  have hH:wt weights H ≤ Hcap:=wt_polyH_le weights F C hF
  have hG:wt weights G ≤ C+weights 2:=wt_polyG_le weights hX F C hF
  have hRwt:wt weights R=weights 2:=weighted_X weights 2
  have hHC:Hcap ≤ C:=Nat.sub_le C (weights 2)
  have hRH:weights 2+Hcap=C:=by
    dsimp [Hcap]
    omega
  have hRH2:weights 2 ≤ Hcap:=by
    dsimp [Hcap]
    omega
  have hMX:wt weights (MvPolynomial.pderiv 0 M) ≤ A:=by
    have h:=wt_pderiv_le weights M 0 A hM
    rw [hX,Nat.sub_zero] at h
    exact h
  have hMY:wt weights (MvPolynomial.pderiv 1 M) ≤ A:=
    (wt_pderiv_le weights M 1 A hM).trans (Nat.sub_le A (weights 1))
  have hMR:wt weights (MvPolynomial.pderiv 2 M) ≤ A-weights 2:=
    wt_pderiv_le weights M 2 A hM
  have hHX:wt weights (MvPolynomial.pderiv 0 H) ≤ Hcap:=by
    have h:=wt_pderiv_le weights H 0 Hcap hH
    rw [hX,Nat.sub_zero] at h
    exact h
  have hHY:wt weights (MvPolynomial.pderiv 1 H) ≤ Hcap:=
    (wt_pderiv_le weights H 1 Hcap hH).trans
      (Nat.sub_le Hcap (weights 1))
  have hHR:wt weights (MvPolynomial.pderiv 2 H) ≤ Hcap-weights 2:=
    wt_pderiv_le weights H 2 Hcap hH
  have hH2:wt weights (H^2) ≤ 2*Hcap:=
    (wt_pow_le weights H 2).trans (Nat.mul_le_mul_left 2 hH)
  have htermX:wt weights (H^2*MvPolynomial.pderiv 0 M) ≤
      A+C+Hcap:=by
    have h:=wt_mul_le weights (H^2) (MvPolynomial.pderiv 0 M)
    omega
  have htermY:wt weights (R*H^2*MvPolynomial.pderiv 1 M) ≤
      A+C+Hcap:=by
    have h1:=wt_mul_le weights R (H^2)
    have h2:=wt_mul_le weights (R*H^2) (MvPolynomial.pderiv 1 M)
    omega
  have htermR:wt weights (G*H*MvPolynomial.pderiv 2 M) ≤
      A+C+Hcap:=by
    have h1:=wt_mul_le weights G H
    have h2:=wt_mul_le weights (G*H) (MvPolynomial.pderiv 2 M)
    omega
  have hinnerX:wt weights (H*MvPolynomial.pderiv 0 H) ≤ C+Hcap:=by
    have h:=wt_mul_le weights H (MvPolynomial.pderiv 0 H)
    omega
  have hinnerY:wt weights (R*H*MvPolynomial.pderiv 1 H) ≤ C+Hcap:=by
    have h1:=wt_mul_le weights R H
    have h2:=wt_mul_le weights (R*H) (MvPolynomial.pderiv 1 H)
    omega
  have hinnerR:wt weights (G*MvPolynomial.pderiv 2 H) ≤ C+Hcap:=by
    have h:=wt_mul_le weights G (MvPolynomial.pderiv 2 H)
    omega
  have hinner:wt weights
      (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
        G*MvPolynomial.pderiv 2 H) ≤ C+Hcap:=by
    exact (wt_add_le weights _ _).trans
      (max_le ((wt_add_le weights _ _).trans (max_le hinnerX hinnerY)) hinnerR)
  have hn:wt weights (((2*b:ℕ):Poly4 K))=0:=wt_natCast weights (2*b)
  have hnM:wt weights (((2*b:ℕ):Poly4 K)*M) ≤ A:=by
    have h:=wt_mul_le weights (((2*b:ℕ):Poly4 K)) M
    omega
  have hlast:wt weights (((2*b:ℕ):Poly4 K)*M*
      (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
        G*MvPolynomial.pderiv 2 H)) ≤ A+C+Hcap:=by
    have h:=wt_mul_le weights (((2*b:ℕ):Poly4 K)*M)
      (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
        G*MvPolynomial.pderiv 2 H)
    omega
  change wt weights
      (H^2*MvPolynomial.pderiv 0 M+
        R*H^2*MvPolynomial.pderiv 1 M+
        G*H*MvPolynomial.pderiv 2 M-
        ((2*b:ℕ):Poly4 K)*M*
          (H*MvPolynomial.pderiv 0 H+R*H*MvPolynomial.pderiv 1 H+
            G*MvPolynomial.pderiv 2 H)) ≤ A+C+Hcap
  exact (wt_sub_le weights _ _).trans
    (max_le ((wt_add_le weights _ _).trans
      (max_le ((wt_add_le weights _ _).trans (max_le htermX htermY)) htermR)) hlast)
theorem numerator_wt_le_minkowski
    (weights:Fin 4 → ℕ) (hX:weights 0=0)
    (F:Poly4 K) (C:ℕ) (hR:weights 2 ≤ C)
    (hRR:2*weights 2 ≤ C) (hbase:weights 2 ≤ weights 1)
    (hF:wt weights F ≤ C) (b:ℕ):
    wt weights (numerator K F b) ≤
      weights 1+b*(C+(C-weights 2)):=by
  induction b with
  | zero =>
      rw [numerator_zero]
      unfold wt
      rw [weighted_X]
      simp
  | succ b ih =>
      rw [numerator_succ]
      have h:=numeratorStep_wt_le_minkowski weights hX F (numerator K F b) b
        (weights 1+b*(C+(C-weights 2))) C hR hRR
        (hbase.trans (Nat.le_add_right _ _)) hF ih
      convert h using 1 <;> ring
theorem shiftedX_wt_eq_zero (weights:Fin 4 → ℕ) (hX:weights 0=0)
    (x:K):
    wt weights (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)=0:=by
  apply Nat.eq_zero_of_le_zero
  apply (wt_sub_le weights _ _).trans
  rw [wt_C,wt_X,hX]
  simp
theorem affineSeedPolynomial_wt_le (weights:Fin 4 → ℕ) (u₀ u₁:K):
    wt weights (affineSeedPolynomial u₀ u₁) ≤ weights 3:=by
  unfold affineSeedPolynomial
  apply (wt_add_le weights _ _).trans
  apply max_le
  · rw [wt_C]
    exact Nat.zero_le _
  · have hm:=wt_mul_le weights (MvPolynomial.X (3:Fin 4):Poly4 K)
      (MvPolynomial.C u₁)
    rw [wt_X,wt_C,Nat.add_zero] at hm
    exact hm
theorem commonNumeratorTerm_wt_le_minkowski
    (weights:Fin 4 → ℕ) (hX:weights 0=0)
    (F:Poly4 K) (C:ℕ) (hR:weights 2 ≤ C)
    (hRR:2*weights 2 ≤ C) (hbase:weights 2 ≤ weights 1)
    (hF:wt weights F ≤ C) (w j:ℕ) (hj:j ≤ w)
    (coeffs:ℕ → K) (x:K):
    wt weights (commonNumeratorTerm F w coeffs x j) ≤
      weights 1+w*(C+(C-weights 2)):=by
  let Hcap:=C-weights 2
  let Qcap:=C+Hcap
  have hHC:Hcap ≤ C:=Nat.sub_le _ _
  have hM:wt weights (numerator K F j) ≤ weights 1+j*Qcap:=by
    simpa only [Hcap,Qcap] using
      numerator_wt_le_minkowski weights hX F C hR hRR hbase hF j
  have hCM:wt weights (MvPolynomial.C (coeffs j)*numerator K F j) ≤
      weights 1+j*Qcap:=by
    have hm:=wt_mul_le weights (MvPolynomial.C (coeffs j)) (numerator K F j)
    rw [wt_C,Nat.zero_add] at hm
    exact hm.trans hM
  have hH:wt weights (polyH K F) ≤ Hcap:=wt_polyH_le weights F C hF
  have hHP:wt weights (polyH K F^(2*(w-j))) ≤
      2*(w-j)*Hcap:=by
    exact (wt_pow_le weights (polyH K F) (2*(w-j))).trans
      (Nat.mul_le_mul_left _ hH)
  have hSX:=shiftedX_wt_eq_zero weights hX x
  have h1:=wt_mul_le weights
    (MvPolynomial.C (coeffs j)*numerator K F j)
    (polyH K F^(2*(w-j)))
  have h2:=wt_mul_le weights
    (MvPolynomial.C (coeffs j)*numerator K F j*
      polyH K F^(2*(w-j)))
    ((MvPolynomial.C x-MvPolynomial.X (0:Fin 4))^j)
  have hSXP:wt weights
      ((MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K)^j) ≤ 0:=by
    have hp:=wt_pow_le weights
      (MvPolynomial.C x-MvPolynomial.X (0:Fin 4):Poly4 K) j
    rw [hSX,Nat.mul_zero] at hp
    exact hp
  have hraw:wt weights (commonNumeratorTerm F w coeffs x j) ≤
      (weights 1+j*Qcap)+2*(w-j)*Hcap:=by
    simpa only [commonNumeratorTerm,Nat.add_zero] using
      h2.trans (Nat.add_le_add (h1.trans (Nat.add_le_add hCM hHP)) hSXP)
  have hunit:2*Hcap ≤ Qcap:=by
    dsimp [Qcap]
    omega
  have hmul:=Nat.mul_le_mul_left (w-j) hunit
  have hwj:j+(w-j)=w:=by omega
  apply hraw.trans
  calc
    (weights 1+j*Qcap)+2*(w-j)*Hcap=
        weights 1+j*Qcap+(w-j)*(2*Hcap):=by ring
    _ ≤ weights 1+j*Qcap+(w-j)*Qcap:=
      Nat.add_le_add_left hmul _
    _=weights 1+(j+(w-j))*Qcap:=by ring
    _=weights 1+w*Qcap:=by rw [hwj]
theorem clearedTaylorNumerator_wt_le_minkowski
    (weights:Fin 4 → ℕ) (hX:weights 0=0)
    (F:Poly4 K) (C:ℕ) (hR:weights 2 ≤ C)
    (hRR:2*weights 2 ≤ C) (hbase:weights 2 ≤ weights 1)
    (hF:wt weights F ≤ C) (w:ℕ) (coeffs:ℕ → K) (x:K):
    wt weights (clearedTaylorNumerator F w coeffs x) ≤
      weights 1+w*(C+(C-weights 2)):=by
  unfold clearedTaylorNumerator
  apply wt_sum_le
  intro j hj
  apply commonNumeratorTerm_wt_le_minkowski weights hX F C hR hRR hbase hF
  have:=Finset.mem_range.mp hj
  omega
theorem agreementNumerator_wt_le_minkowski
    (weights:Fin 4 → ℕ) (hX:weights 0=0)
    (F:Poly4 K) (C:ℕ) (hR:weights 2 ≤ C)
    (hRR:2*weights 2 ≤ C) (hbase:weights 2 ≤ weights 1)
    (hF:wt weights F ≤ C) (w:ℕ) (coeffs:ℕ → K)
    (x u₀ u₁:K):
    wt weights (agreementNumerator F w coeffs x u₀ u₁) ≤
      max (weights 1) (weights 3)+w*(C+(C-weights 2)):=by
  let Hcap:=C-weights 2
  let Qcap:=C+Hcap
  have hHC:Hcap ≤ C:=Nat.sub_le _ _
  have hTaylor:=clearedTaylorNumerator_wt_le_minkowski weights hX F C hR hRR
    hbase hF w coeffs x
  have hA:=affineSeedPolynomial_wt_le weights u₀ u₁
  have hH:wt weights (polyH K F) ≤ Hcap:=wt_polyH_le weights F C hF
  have hHP:wt weights (polyH K F^(2*w)) ≤ 2*w*Hcap:=
    (wt_pow_le weights (polyH K F) (2*w)).trans
      (Nat.mul_le_mul_left _ hH)
  have hprod:=wt_mul_le weights (affineSeedPolynomial u₀ u₁)
    (polyH K F^(2*w))
  have hunit:2*Hcap ≤ Qcap:=by
    dsimp [Qcap]
    omega
  have hmul:=Nat.mul_le_mul_left w hunit
  have hright:wt weights
      (affineSeedPolynomial u₀ u₁*polyH K F^(2*w)) ≤
      max (weights 1) (weights 3)+w*Qcap:=by
    apply hprod.trans
    calc
      wt weights (affineSeedPolynomial u₀ u₁)+
          wt weights (polyH K F^(2*w)) ≤ weights 3+2*w*Hcap:=
        Nat.add_le_add hA hHP
      _=weights 3+w*(2*Hcap):=by ring
      _ ≤ max (weights 1) (weights 3)+w*Qcap:=
        Nat.add_le_add (Nat.le_max_right _ _) hmul
  unfold agreementNumerator
  apply (wt_sub_le weights _ _).trans
  apply max_le
  · simpa only [Hcap,Qcap] using
      hTaylor.trans (Nat.add_le_add_right (Nat.le_max_left _ _) _)
  · simpa only [Hcap,Qcap] using hright
end
end ProximityPrize.SubmissionLower.ContactPost6464MinkowskiRecurrenceResearch
