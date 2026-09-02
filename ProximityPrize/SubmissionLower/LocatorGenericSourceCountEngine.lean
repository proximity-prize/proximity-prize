import ProximityPrize.SubmissionLower.LocatorGenericSourceCount
import ProximityPrize.SubmissionLower.LocatorHelperArithmetic6784
import ProximityPrize.SubmissionLower.LocatorQuotientMonotone
namespace ProximityPrize.SubmissionLower.LocatorGenericSourceCountEngine
open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient LocatorGenericPowerAvoidance LocatorGenericSourceCount LocatorReplacementGridData
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600
abbrev SourceKernel (D L s m : ℕ) (u0 u1 : I → K) := ConstraintKernel (K := K) D 131071 L s m IRSProfile.domain u0 u1
private theorem source_quotient_nested
    (D L s m Ysrc : ℕ) (hshape : D + s ≤ 131071 * (Ysrc + 1))
    (u0 u1 : I → K) (H : P4) (F : RegularIndex H) (hF : F.1 ≠ 0)
    (q : SourceKernel D L s m u0 u1 →ₗ[K] P4)
    (hqinj : Function.Injective q)
    (hprod : ∀ v, reconstruct K D 131071 L s v.1 = F.1 * q v)
    (hqbox : ∀ v, q v ∈ globalCoefficientBox K
      (D - wt (contactWeights 131071) F.1) 131071
      (L - wt residualTotalWeights F.1)
      (s - wt residualSWeights F.1)) :
    ∀ v, q v ∈ nestedCoefficientBox K
      (D - wt (contactWeights 131071) F.1) 131071
      (L - wt residualTotalWeights F.1)
      (Ysrc - wt residualYSWeights F.1)
      (s - wt residualSWeights F.1) := by
  intro v
  have hqYS : wt residualYSWeights (q v) ≤
      Ysrc - wt residualYSWeights F.1 := by
    by_cases hv : v = 0
    · subst v
      simp [wt, MvPolynomial.weightedTotalDegree]
    · have hqv : q v ≠ 0 := by
        intro hz
        apply hv
        apply hqinj
        simpa only [map_zero] using hz
      have hsrc : wt residualYSWeights
          (reconstruct K D 131071 L s v.1) ≤ Ysrc := by
        apply flag_box_ys_bound D 131071 L s Ysrc (by decide) hshape
        exact reconstruct_mem_globalCoefficientBox K D 131071 L s v.1
      have hmul := weightedTotalDegree_mul residualYSWeights F.1 (q v) hF hqv
      rw [← hprod v] at hmul
      simp only [wt] at hsrc ⊢
      omega
  intro d hd
  have hb := hqbox v hd
  have hy := (MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans hqYS
  rw [weight_fin4] at hy
  simp only [residualYSWeights] at hy
  refine ⟨hb.1, ?_, hb.2.1, hb.2.2⟩
  simpa [residualYSWeights] using hy
theorem exists_source_quotient
    (D L s m Ysrc : ℕ) (hshape : D + s ≤ 131071 * (Ysrc + 1))
    (u0 u1 : I → K) (H : P4) (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : SourceKernel D L s m u0 u1,
      F.1 ∣ reconstruct K D 131071 L s v.1) :
    ∃ q : SourceKernel D L s m u0 u1 →ₗ[K] P4,
      Function.Injective q ∧
      (∀ v, reconstruct K D 131071 L s v.1 = F.1 * q v) ∧
      (∀ v, q v ∈ nestedCoefficientBox K
        (D - wt (contactWeights 131071) F.1) 131071
        (L - wt residualTotalWeights F.1)
        (Ysrc - wt residualYSWeights F.1)
        (s - wt residualSWeights F.1)) := by
  let recon := kernelReconstructLinear (K := K) D 131071 L s m
    IRSProfile.domain u0 u1
  have hdivK : ∀ v : SourceKernel D L s m u0 u1, F.1 ∣ recon v := by
    intro v
    simpa only [recon, kernelReconstructLinear_apply] using hdiv v
  let q := quotientLinear recon F.1 hF hdivK
  have hqinj : Function.Injective q := quotientLinear_injective recon
    (kernelReconstructLinear_injective (K := K) D 131071 L s m
      IRSProfile.domain u0 u1) F.1 hF hdivK
  have hprod (v : SourceKernel D L s m u0 u1) : recon v = F.1 * q v :=
    recon_eq_mul_quotientPolynomial recon F.1 hdivK v
  have hproduct : ∀ v : SourceKernel D L s m u0 u1,
      reconstruct K D 131071 L s v.1 = F.1 * q v := by
    intro v
    simpa only [recon, kernelReconstructLinear_apply] using hprod v
  have hqbox : ∀ v : SourceKernel D L s m u0 u1,
      q v ∈ globalCoefficientBox K
        (D - wt (contactWeights 131071) F.1) 131071
        (L - wt residualTotalWeights F.1)
        (s - wt residualSWeights F.1) :=
    quotient_box_of_full_divisor D 131071 L s m
      (wt (contactWeights 131071) F.1) (wt residualTotalWeights F.1)
      (wt residualSWeights F.1) IRSProfile.domain u0 u1 F.1 hF hdivK
      le_rfl le_rfl le_rfl
  exact ⟨q, hqinj, hproduct,
    source_quotient_nested D L s m Ysrc hshape
      u0 u1 H F hF q hqinj hproduct hqbox⟩
theorem source_count_of_divisor
    (D L s m Ysrc delta k : ℕ) (src : Source)
    (hsrcLength : src.length = L) (hsrcY : src.y = Ysrc)
    (hsrcR : src.r = s) (hdelta : delta = 50480)
    (hD : 0 < D) (hshape : D + s ≤ 131071 * (Ysrc + 1))
    (hcapacity : ∀ j, 1 ≤ j → j ≤ k →
      D - j * delta ≤ (m - j) * 181550 + j * (131071 - 1))
    (hlowpos : ∀ j, 1 ≤ j → j ≤ k → 0 < D - j * delta)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181550 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80594)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : SourceKernel D L s m u0 u1,
      F.1 ∣ reconstruct K D 131071 L s v.1)
    (hgap : src.gap ≤ Module.finrank K (SourceKernel D L s m u0 u1))
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : RouteFits src k (box c)) :
    (regularSeeds H selected Gamma F).card ≤ routeCost src (box c) k := by
  classical
  obtain ⟨hkpos, hk30, _hyroom, _hrroom, _hshapeRoute, hband,
    hterminal, hgates, _hrate⟩ := hfit
  obtain ⟨hr, hylo, _hyhi, htlo, _hthi⟩ :=
    factor_bounds_of_cell H F c hcell
  have hTstage (j : ℕ) : L - j * wt residualTotalWeights F.1 ≤
      stageT src (box c) j := by
    rw [stageT, hsrcLength]
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_left j htlo) L
  have hYstage (j : ℕ) : Ysrc - j * wt residualYSWeights F.1 ≤
      stageY src (box c) j := by
    rw [stageY, hsrcY]
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_left j hylo) Ysrc
  have hRstage (j : ℕ) : s - j * wt residualSWeights F.1 ≤
      stageR src (box c) j := by
    rw [stageR, hsrcR, hr]
  have hbandLe (j : ℕ) :
      delta * channelCount
        (L - j * wt residualTotalWeights F.1)
        (Ysrc - j * wt residualYSWeights F.1)
        (s - j * wt residualSWeights F.1) ≤ stageBand src (box c) j := by
    rw [stageBand_eq]; change delta * channelCount _ _ _ ≤ 50480 * channelCount _ _ _
    rw [hdelta]
    exact Nat.mul_le_mul_left 50480
      (channelCount_mono (hTstage j) (hYstage j) (hRstage j))
  have hbudget : sourcePowerBudget delta
      (L - wt residualTotalWeights F.1)
      (Ysrc - wt residualYSWeights F.1)
      (s - wt residualSWeights F.1) F.1 k <
      Module.finrank K (SourceKernel D L s m u0 u1) := by
    have hrewrite := sourcePowerBudget_shift_eq_forwardSum
      delta L Ysrc s F.1 1 k
    simp only [Nat.one_mul] at hrewrite
    rw [hrewrite]
    exact (forwardSum_mono _ _ hbandLe 1 k).trans_lt
      ((forwardSum_stageBand_eq_bandSum src (box c) k).trans_lt
        (hband.trans_le hgap))
  obtain ⟨q, hqinj, hprod, hqNested⟩ :=
    exists_source_quotient D L s m Ysrc hshape u0 u1 H F hF hdiv
  have hwidth : D - wt (contactWeights 131071) F.1 ≤
      (D - delta - wt (contactWeights 131071) F.1) + delta := by
    have := hlowpos 1 (by omega) hkpos
    omega
  have hex : Nonempty (PowerExtractionWitness
      (D - delta - wt (contactWeights 131071) F.1) 131071 delta
      (L - wt residualTotalWeights F.1)
      (Ysrc - wt residualYSWeights F.1)
      (s - wt residualSWeights F.1) k q F.1) := by
    have hbudget' : sourcePowerBudget delta
        (L - wt residualTotalWeights F.1)
        (Ysrc - wt residualYSWeights F.1)
        (s - wt residualSWeights F.1) F.1 (k - 1 + 1) <
        Module.finrank K (SourceKernel D L s m u0 u1) := by
      rw [Nat.sub_add_cancel hkpos]
      exact hbudget
    simpa [Nat.sub_add_cancel hkpos] using
      exists_powerExtractionWitness (k - 1)
        (D - wt (contactWeights 131071) F.1)
        (D - delta - wt (contactWeights 131071) F.1)
        131071 delta (L - wt residualTotalWeights F.1)
        (Ysrc - wt residualYSWeights F.1)
        (s - wt residualSWeights F.1) hwidth q hqinj hqNested F.1 hF hbudget'
  obtain ⟨e⟩ := hex
  let j := e.depth + 1
  have hjpos : 1 ≤ j := by simp [j]
  have hjle : j ≤ k := by simpa [j] using e.depth_lt
  have hwQ := nested_mem_weights e.quotient_box e.quotient_ne
  have hTeq :
      (L - wt residualTotalWeights F.1) -
          e.depth * wt residualTotalWeights F.1 =
        L - j * wt residualTotalWeights F.1 := by
    dsimp only [j]
    rw [Nat.add_mul, Nat.one_mul, Nat.sub_sub]
    congr 1
    omega
  have hYeq :
      (Ysrc - wt residualYSWeights F.1) -
          e.depth * wt residualYSWeights F.1 =
        Ysrc - j * wt residualYSWeights F.1 := by
    dsimp only [j]
    rw [Nat.add_mul, Nat.one_mul, Nat.sub_sub]
    congr 1
    omega
  have hReq :
      (s - wt residualSWeights F.1) -
          e.depth * wt residualSWeights F.1 =
        s - j * wt residualSWeights F.1 := by
    dsimp only [j]
    rw [Nat.add_mul, Nat.one_mul, Nat.sub_sub]
    congr 1
    omega
  have hCeq :
      (D - delta - wt (contactWeights 131071) F.1) -
          e.depth * delta - e.depth * wt (contactWeights 131071) F.1 =
        D - j * delta - j * wt (contactWeights 131071) F.1 := by
    dsimp only [j]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_mul, Nat.one_mul]
    simp only [Nat.sub_sub]
    congr 1
    omega
  have hQTraw : wt residualTotalWeights e.quotient ≤
      L - j * wt residualTotalWeights F.1 := by
    have := hwQ.1
    change wt residualTotalWeights e.quotient ≤
      (L - wt residualTotalWeights F.1) -
        e.depth * wt residualTotalWeights F.1 at this
    exact this.trans_eq hTeq
  have hQYraw : wt residualYSWeights e.quotient ≤
      Ysrc - j * wt residualYSWeights F.1 := by
    have := hwQ.2.1
    change wt residualYSWeights e.quotient ≤
      (Ysrc - wt residualYSWeights F.1) -
        e.depth * wt residualYSWeights F.1 at this
    exact this.trans_eq hYeq
  have hQRraw : wt residualSWeights e.quotient ≤
      s - j * wt residualSWeights F.1 := by
    have := hwQ.2.2.1
    change wt residualSWeights e.quotient ≤
      (s - wt residualSWeights F.1) -
        e.depth * wt residualSWeights F.1 at this
    exact this.trans_eq hReq
  have hcQ : wt (contactWeights 131071) e.quotient <
      D - j * delta - j * wt (contactWeights 131071) F.1 := by
    have := hwQ.2.2.2
    change wt (contactWeights 131071) e.quotient <
      (D - delta - wt (contactWeights 131071) F.1) -
        e.depth * delta - e.depth * wt (contactWeights 131071) F.1 at this
    exact this.trans_le hCeq.le
  have heq : reconstruct K D 131071 L s e.vector = F.1 ^ j * e.quotient := by
    rw [hprod, ← e.factorization]
    dsimp only [j]
    rw [pow_succ]
    ring
  have hlow : reconstruct K D 131071 L s e.vector ∈
      globalCoefficientBox K (D - j * delta) 131071 L s :=
    reconstruct_mem_low_of_power IRSProfile.domain u0 u1 e.vector
      F.1 e.quotient heq hD (hlowpos j hjpos hjle) hcQ
  have hQT := hQTraw.trans (hTstage j)
  have hQY := hQYraw.trans (hYstage j)
  have hQR := hQRraw.trans (hRstage j)
  have hrel : IsRelPrime F.1 e.quotient := by
    rcases e.terminal_or_not_dvd with hlast | hnot
    · have hjlast : j = k := by simpa [j] using hlast
      apply terminal_relPrime H F c src j e.quotient e.quotient_ne hcell
        hQT hQY hQR
      simpa [hjlast] using hterminal
    · exact (RCN167.positiveRFactors_spec H F.1 F.2).1
        |>.isRelPrime_iff_not_dvd.mpr hnot
  let supports : K → Finset I := fun gamma ↦
    (Finset.univ : Finset I).filter (fun i ↦
      (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)
  have hQzero : ∀ gamma ∈ regularSeeds H selected Gamma F,
      RCN319.specialization K (selected gamma) gamma e.quotient = 0 := by
    apply source_power_specialization_zero D (D - j * delta) 131071 L s m j
      hjpos (by decide) IRSProfile.domain u0 u1 e.vector hlow
      selected Gamma (regularSeeds H selected Gamma F) supports
      (regularSeeds_subset H selected Gamma F) hdegree
    · intro gamma hgamma
      have hcard := hagreement gamma
        (regularSeeds_subset H selected Gamma F hgamma)
      exact (hcapacity j hjpos hjle).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left (m - j) hcard) _)
    · intro gamma _ i hi
      exact (Finset.mem_filter.mp hi).2
    · exact heq
    · exact LocatorHelperArithmetic6784.factorial_cast_ne_zero_of_le_thirty
        j (hjle.trans hk30)
    · intro gamma hgamma
      exact (Finset.mem_filter.mp hgamma).2.1
    · intro gamma hgamma
      exact (Finset.mem_filter.mp hgamma).2.2
  have hgate := pairGatesThrough_get src (box c) hjpos hjle hgates
  exact (count_le_stageCost u0 u1 H selected Gamma hdegree hagreement hno
    F c hcell src j e.quotient e.quotient_ne hQT hQY hQR hrel hgate hQzero).trans
      (stageCost_le_routeCost src (box c) hjpos hjle)
end
end ProximityPrize.SubmissionLower.LocatorGenericSourceCountEngine
