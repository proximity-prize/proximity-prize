import ProximityPrize.SubmissionLower.Z6970H2307SlopeShape
import ProximityPrize.SubmissionLower.Shared50OrderDivision
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalRing.Module
import ProximityPrize.SubmissionLower.Z6969Pack0853
import ProximityPrize.SubmissionLower.Z6969Pack0851
import ProximityPrize.SubmissionLower.Z6969Pack0850
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969GateCertCF
section Z6969Source2417
set_option autoImplicit true
set_option Elab.async false

-- merged module Low6969GateOrder
section Merged_Low6969GateOrder

set_option autoImplicit false

namespace Low6969GateOrder

open K1_13_6_1_2 (VanishesTo)


theorem vanishesTo_zero {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] (f : R) :
    VanishesTo P f 0 := by
  unfold VanishesTo
  simp

theorem exists_exact_order {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (P : Ideal R) [P.IsPrime] {f : R} (hf : f ≠ 0) :
    ∃ e : ℕ, VanishesTo P f e ∧ ¬ VanishesTo P f (e + 1) := by
  classical
  let L := Localization.AtPrime P
  have hinj : Function.Injective (algebraMap R L) :=
    IsLocalization.injective L (by
      intro x hx
      exact mem_nonZeroDivisors_of_ne_zero (fun h => (Ideal.mem_primeCompl_iff.mp hx) (h ▸ P.zero_mem)))
  have hne : algebraMap R L f ≠ 0 := fun h => hf (hinj (h.trans (map_zero _).symm))
  have hex : ∃ n, ¬ VanishesTo P f n := by
    by_contra hall
    push_neg at hall
    apply hne
    have hmem : algebraMap R L f ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal L ^ n := by
      rw [Submodule.mem_iInf]
      exact fun n => hall n
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal L)
      (IsLocalRing.maximalIdeal.isMaximal L).ne_top, Submodule.mem_bot] at hmem
  let n := Nat.find hex
  have hn : ¬ VanishesTo P f n := Nat.find_spec hex
  have hpos : n ≠ 0 := fun h0 => hn (h0 ▸ vanishesTo_zero P f)
  refine ⟨n - 1, ?_, ?_⟩
  · by_contra hc
    exact Nat.find_min hex (by omega : n - 1 < n) hc
  · rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hpos)]

theorem cofactor_order {n : ℕ} {K : Type*} [Field K] [PerfectField K]
    (P : Ideal (MvPolynomial (Fin n) K)) [P.IsPrime] {f h G : MvPolynomial (Fin n) K} {a e m r : ℕ}
    (hf : ¬ VanishesTo P f (e + 1)) (hh : ¬ VanishesTo P h (m + 1))
    (hQ : VanishesTo P (f ^ a * (h * G)) r) : VanishesTo P G (r - e * a - m) := by
  have h1 := Shared50OrderDivision.vanishesTo_of_pow_mul P hf hQ
  have h2 : VanishesTo P (h ^ 1 * G) (r - e * a) := by simpa using h1
  have h3 := Shared50OrderDivision.vanishesTo_of_pow_mul P hh h2
  simpa [Nat.mul_one] using h3



private theorem deriv_ideal_pow {k : Type*} [Field k] {n : ℕ}
    (P : Ideal (MvPolynomial (Fin n) k)) (i : Fin n) (e : ℕ)
    {F : MvPolynomial (Fin n) k} (h : F ∈ P^(e+1)) : MvPolynomial.pderiv i F ∈ P^e := by
  induction e generalizing F with
  | zero => simp
  | succ e ih =>
    rw [pow_succ] at h
    refine Submodule.mul_induction_on h ?_ ?_
    · intro x hx y hy
      rw [MvPolynomial.pderiv_mul]
      have h₁ : MvPolynomial.pderiv i x * y ∈ P^(e+1) := by
        rw [pow_succ]
        exact Ideal.mul_mem_mul (ih hx) hy
      have h₂ : x * MvPolynomial.pderiv i y ∈ P^(e+1) := (P^(e+1)).mul_mem_right _ hx
      simpa only [mul_comm, add_comm] using (P^(e+1)).add_mem h₁ h₂
    · intro x y hx hy
      rw [map_add]
      exact (P^(e+1)).add_mem hx hy

theorem deriv_order {k : Type*} [Field k] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) k))
    [P.IsPrime] {F : MvPolynomial (Fin n) k} (i : Fin n) {e : ℕ}
    (h : VanishesTo P F e) : VanishesTo P (MvPolynomial.pderiv i F) (e-1) := by
  cases e with
  | zero => simp [VanishesTo]
  | succ e =>
    let L := Localization.AtPrime P
    change algebraMap _ L F ∈ IsLocalRing.maximalIdeal L ^ (e+1) at h
    change algebraMap _ L (MvPolynomial.pderiv i F) ∈ IsLocalRing.maximalIdeal L ^ e
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P L, ← Ideal.map_pow,
      IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl L] at h ⊢
    obtain ⟨u, hu, hF⟩ := h
    refine ⟨u*u, P.primeCompl.mul_mem hu hu, ?_⟩
    have hD := deriv_ideal_pow P i e hF
    have hE : u*F ∈ P^e := Ideal.pow_le_pow_right (by omega) hF
    have hM := (P^e).sub_mem ((P^e).mul_mem_left u hD) ((P^e).mul_mem_left (MvPolynomial.pderiv i u) hE)
    convert hM using 1
    rw [MvPolynomial.pderiv_mul]
    ring

theorem separant_order (P : Ideal K1_13_6.GeoJets) [P.IsPrime] {f : K1_13.Row 4} {e : ℕ}
    (hl : VanishesTo P (K1_13_6.toGeneric f) e) :
    VanishesTo P (K1_13_6.toGeneric (K1_13_6.separant f)) (e - 1) := by
  simpa only [K1_13_6.toGeneric, K1_13_6.separant, MvPolynomial.pderiv_map] using
    deriv_order P (3 : Fin 4) hl

end Low6969GateOrder

end Merged_Low6969GateOrder

-- merged module Low6969GateCount
section Merged_Low6969GateCount

set_option autoImplicit false
set_option Elab.async false

namespace Low6969GateCount

open P3 (K)
open K1_13 (Row Shape shape InBox chart mixed32)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_1_2 (VanishesTo pair_height)
open Low6969GeometryCut (CutInput)
open Low6969GeometryCut_2 (Branch)
open Low6969Prices (taylorLength)
open Low6969SharedTally (Data)
open scoped Polynomial BigOperators
open Low6969SharedChooseCut (mem_of_order)

variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ} {S : Set (Ideal GeoJets)}

theorem minimal_of_height_two {R1 R2 : Row 4} {P : Ideal GeoJets} [P.IsPrime] (hP : P.height = 2)
    (hR1 : toGeneric R1 ≠ 0) (hrel : IsRelPrime (toGeneric R1) (toGeneric R2))
    (hR1P : toGeneric R1 ∈ P) (hYP : toGeneric R2 ∈ P) : (intersectionIdeal R1 R2).IsMinimalPrime P := by
  have hsub : intersectionIdeal R1 R2 ≤ P := by
    unfold intersectionIdeal
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hR1P
    · exact hYP
  obtain ⟨P', hmin, hle⟩ := Ideal.exists_minimalPrimes_le hsub
  have hht : P'.height = 2 := pair_height hR1 hrel hmin
  letI : P'.IsPrime := hmin.isPrime
  have heq : P' = P := by
    by_contra hne
    have hs := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
    rw [hht, hP] at hs
    exact (by decide : ¬(2 : ℕ∞) + 1 ≤ 2) hs
  exact heq ▸ hmin

theorem branch_height (input : CutInput Γ s f Q l) (b : Branch f Q l) : b.surface.height = 2 :=
  pair_height (K1_13_6_3_6.toGeneric_ne_zero input.small.1.ne_zero)
    (K1_13_7_1.proper_generic f Q input.small.1 input.proper) b.base

theorem branch_pair_weight (input : CutInput Γ s f Q l) (b : Branch f Q l) {R1 R2 : Row 4}
    (hR1 : toGeneric R1 ≠ 0) (hrel : IsRelPrime (toGeneric R1) (toGeneric R2)) {α β : ℕ}
    (hα : @VanishesTo _ _ b.surface b.base.isPrime (toGeneric R1) α)
    (hβ : @VanishesTo _ _ b.surface b.base.isPrime (toGeneric R2) β) (hαp : 0 < α) (hβp : 0 < β) :
    ∃ h : (intersectionIdeal R1 R2).IsMinimalPrime b.surface,
      ((α * β : ℕ) : ℕ∞) ≤ cycleLength (intersectionIdeal R1 R2) b.surface h.isPrime := by
  letI := b.base.isPrime
  have hmin := minimal_of_height_two (branch_height input b) hR1 hrel (mem_of_order hαp hα)
    (mem_of_order hβp hβ)
  exact ⟨hmin, Shared50Multiplicity.cycleLength_ge_product_of_minimal hmin hR1 hrel hα hβ⟩

theorem pair_sum_tilted (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F ⊆ D.branches) (R1 R2 : Row 4) (hR1 : toGeneric R1 ≠ 0)
    (hR1' : R1 ≠ 0) (hrel : IsRelPrime (toGeneric R1) (toGeneric R2))
    (htilt : Low6969Prices.tiltedFits (shape f)) (q₁ q₂ : Shape) (hQ₁ : InBox (shape R1) q₁)
    (hQ₂ : InBox (shape R2) q₂) (hq₁ : Low48BentLattice.Chamber (q₁, 0))
    (hq₂ : Low48BentLattice.Chamber (q₂, 0)) (α β : Ideal GeoJets → ℕ)
    (hα : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric R1) (α b.surface))
    (hβ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric R2) (β b.surface)) :
    1920 * (∑ b ∈ F, α b.surface * β b.surface * (b.weight * (D.points b).card)) ≤
      Low6969Gate.tiltedPair (shape f).chamber q₁ q₂ := by
  classical
  let F' := F.filter (fun b => 0 < α b.surface * β b.surface)
  have hsum : ∑ b ∈ F, α b.surface * β b.surface * (b.weight * (D.points b).card) =
      ∑ b ∈ F', α b.surface * β b.surface * (b.weight * (D.points b).card) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : 0 < α b.surface * β b.surface
    · simp [h]
    · have : α b.surface * β b.surface = 0 := by omega
      simp [this]
  rw [hsum]
  exact Low6969Gate.tilted_pair_tally D input F' (fun b hb => hF (Finset.mem_filter.mp hb).1) R1 R2 hR1' hrel
    (fun P => α P * β P) htilt q₁ q₂ hQ₁ hQ₂ hq₁ hq₂ (fun b hb => by
      obtain ⟨hbF, hpos⟩ := Finset.mem_filter.mp hb
      have hαp : 0 < α b.surface := Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
      have hβp : 0 < β b.surface := Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
      exact branch_pair_weight input b hR1 hrel (hα b hbF) (hβ b hbF) hαp hβp)

theorem pair_sum_tilted_rat (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F ⊆ D.branches) (R1 R2 : Row 4) (hR1 : toGeneric R1 ≠ 0)
    (hR1' : R1 ≠ 0) (hrel : IsRelPrime (toGeneric R1) (toGeneric R2))
    (htilt : Low6969Prices.tiltedFits (shape f)) (q₁ q₂ : Shape) (hQ₁ : InBox (shape R1) q₁)
    (hQ₂ : InBox (shape R2) q₂) (hq₁ : Low48BentLattice.Chamber (q₁, 0))
    (hq₂ : Low48BentLattice.Chamber (q₂, 0)) (α β : Ideal GeoJets → ℕ)
    (hα : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric R1) (α b.surface))
    (hβ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric R2) (β b.surface)) :
    ∑ b ∈ F, ((α b.surface : ℚ) * β b.surface) * ((b.weight * (D.points b).card : ℕ) : ℚ) ≤
      (Low6969Gate.tiltedPair (shape f).chamber q₁ q₂ : ℚ) / 1920 := by
  have h := pair_sum_tilted D input F hF R1 R2 hR1 hR1' hrel htilt q₁ q₂ hQ₁ hQ₂ hq₁ hq₂ α β hα hβ
  have h' : ((1920 * (∑ b ∈ F, α b.surface * β b.surface * (b.weight * (D.points b).card)) : ℕ) : ℚ) ≤
      (Low6969Gate.tiltedPair (shape f).chamber q₁ q₂ : ℚ) := by exact_mod_cast h
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 1920)]
  push_cast at h' ⊢
  nlinarith [h']

theorem pair_sum_ordinary_rat (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F ⊆ D.branches) (R1 R2 : Row 4) (hR1 : toGeneric R1 ≠ 0)
    (hR1' : R1 ≠ 0) (hrel : IsRelPrime (toGeneric R1) (toGeneric R2))
    (q₁ q₂ : Shape) (hq₁ : K1_13_6_2_3.ChamberBox q₁) (hq₂ : K1_13_6_2_3.ChamberBox q₂)
    (hQ₁ : InBox (shape R1) q₁) (hQ₂ : InBox (shape R2) q₂) (α β : Ideal GeoJets → ℕ)
    (hα : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric R1) (α b.surface))
    (hβ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric R2) (β b.surface)) :
    ∑ b ∈ F, ((α b.surface : ℚ) * β b.surface) * ((b.weight * (D.points b).card : ℕ) : ℚ) ≤
      (mixed32 q₁ q₂ (chart (taylorLength + 1) (shape f).chamber)
        (chart (taylorLength + 2) (shape f).chamber) : ℚ) / 32 := by
  classical
  let F' := F.filter (fun b => 0 < α b.surface * β b.surface)
  have hsum : ∑ b ∈ F, α b.surface * β b.surface * (b.weight * (D.points b).card) =
      ∑ b ∈ F', α b.surface * β b.surface * (b.weight * (D.points b).card) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : 0 < α b.surface * β b.surface
    · simp [h]
    · have : α b.surface * β b.surface = 0 := by omega
      simp [this]
  have h := Low6969Gate.ordinary_pair_tally D input F' (fun b hb => hF (Finset.mem_filter.mp hb).1) R1 R2
    hR1' hrel q₁ q₂ hq₁ hq₂ hQ₁ hQ₂ (fun P => α P * β P) (fun b hb => by
      obtain ⟨hbF, hpos⟩ := Finset.mem_filter.mp hb
      have hαp : 0 < α b.surface := Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
      have hβp : 0 < β b.surface := Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
      exact branch_pair_weight input b hR1 hrel (hα b hbF) (hβ b hbF) hαp hβp)
  rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 32)]
  have h' : ((32 * (∑ b ∈ F', α b.surface * β b.surface * (b.weight * (D.points b).card)) : ℕ) : ℚ) ≤
      (mixed32 q₁ q₂ (chart (taylorLength + 1) (shape f).chamber)
        (chart (taylorLength + 2) (shape f).chamber) : ℚ) := by exact_mod_cast h
  have hs : ∑ b ∈ F, ((α b.surface : ℚ) * β b.surface) * ((b.weight * (D.points b).card : ℕ) : ℚ) =
      ((∑ b ∈ F', α b.surface * β b.surface * (b.weight * (D.points b).card) : ℕ) : ℚ) := by
    rw [← hsum]; push_cast; rfl
  rw [hs]
  push_cast at h' ⊢
  nlinarith [h']

end Low6969GateCount

end Merged_Low6969GateCount

-- merged module Low6969GateTwoCut
section Merged_Low6969GateTwoCut

set_option autoImplicit false
set_option Elab.async false

namespace Low6969GateTwoCut

open P3 (K)
open K1_13 (Row Shape shape InBox mixed32)
open K1_13_6 (GeoJets toGeneric)
open K1_13_6_1_2 (VanishesTo)
open Low6969GeometryCut (CutInput)
open Low6969GeometryCut_2 (Branch)
open Low6969SharedTally (Data)
open scoped Polynomial BigOperators

def ClassCert (r a : ℕ) (cc v : ℚ) : Prop :=
  ∀ e m : ℕ, 1 ≤ e →
    ((r - a : ℕ) : ℚ) ^ 2 ≤ (1 - cc) * (((r - e * a - m : ℕ) : ℚ) * ((r - e * a - m : ℕ) : ℚ)) +
      (m : ℚ) * ((r - e * a - m : ℕ) : ℚ) + ((r - a : ℕ) : ℚ) * ((e : ℚ) * m) +
      cc * ((r - a : ℕ) : ℚ) * ((e : ℚ) * ((r - e * a - m : ℕ) : ℚ)) +
      v * ((r - a : ℕ) : ℚ) ^ 2 * ((e : ℚ) * ((e : ℚ) - 1))

theorem classCert_zero (r : ℕ) : ClassCert r 0 0 0 := by
  intro e m he
  have h := Low6969GateCombine.class_zero r e m (r - 0 * e - m) he (by omega)
  simp only [Nat.zero_mul, Nat.zero_sub, Nat.sub_zero, Nat.cast_zero, sub_zero, zero_mul, one_mul, mul_zero,
    add_zero] at h ⊢
  nlinarith [h]

variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ} {S : Set (Ideal GeoJets)}

theorem two_cut_count_tilted (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F ⊆ D.branches) (H G₁ G₂ sf : Row 4)
    (htilt : Low6969Prices.tiltedFits (shape f))
    (qf qH q₁ q₂ qs : Shape) (hbf : InBox (shape f) qf) (hbH : InBox (shape H) qH)
    (hb₁ : InBox (shape G₁) q₁) (hb₂ : InBox (shape G₂) q₂) (hbs : InBox (shape sf) qs)
    (hcf : Low48BentLattice.Chamber (qf, 0)) (hcH : Low48BentLattice.Chamber (qH, 0))
    (hc₁ : Low48BentLattice.Chamber (q₁, 0)) (hc₂ : Low48BentLattice.Chamber (q₂, 0))
    (hcs : Low48BentLattice.Chamber (qs, 0)) (r a : ℕ) (cc v : ℚ) (hc0 : 0 ≤ cc) (hc1 : cc ≤ 1)
    (hv : 0 ≤ v) (hcert : ClassCert r a cc v)
    (e m : Ideal GeoJets → ℕ)
    (hf0 : f ≠ 0) (hH0 : H ≠ 0) (hG0 : G₁ ≠ 0) (hf0' : toGeneric f ≠ 0) (hH0' : toGeneric H ≠ 0)
    (hG0' : toGeneric G₁ ≠ 0) (hsf : sf ≠ 0) (hsf' : toGeneric sf ≠ 0)
    (hfH : IsRelPrime (toGeneric f) (toGeneric H)) (hfG : IsRelPrime (toGeneric f) (toGeneric G₁))
    (hHG : IsRelPrime (toGeneric H) (toGeneric G₁)) (hGG : IsRelPrime (toGeneric G₁) (toGeneric G₂))
    (hfs : IsRelPrime (toGeneric f) (toGeneric sf))
    (hef : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric f) (e b.surface) ∧
      ¬ @VanishesTo _ _ b.surface b.base.isPrime (toGeneric f) (e b.surface + 1))
    (hmH : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric H) (m b.surface) ∧
      ¬ @VanishesTo _ _ b.surface b.base.isPrime (toGeneric H) (m b.surface + 1))
    (hsfdef : sf = K1_13_6.separant f)
    (hQ₁ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime
      ((toGeneric f) ^ a * (toGeneric H * toGeneric G₁)) r)
    (hQ₂ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime
      ((toGeneric f) ^ a * (toGeneric H * toGeneric G₂)) r)
    (hρ : a ≤ r) :
    ((r - a : ℕ) : ℚ) ^ 2 * (∑ b ∈ F, ((b.weight * (D.points b).card : ℕ) : ℚ)) ≤
      (1 - cc) * ((Low6969Gate.tiltedPair (shape f).chamber q₁ q₂ : ℚ) / 1920) +
      (Low6969Gate.tiltedPair (shape f).chamber qH q₁ : ℚ) / 1920 +
      ((r - a : ℕ) : ℚ) * ((Low6969Gate.tiltedPair (shape f).chamber qf qH : ℚ) / 1920) +
      cc * ((r - a : ℕ) : ℚ) *
        ((Low6969Gate.tiltedPair (shape f).chamber qf q₁ : ℚ) / 1920) +
      v * ((r - a : ℕ) : ℚ) ^ 2 *
        ((Low6969Gate.tiltedPair (shape f).chamber qf qs : ℚ) / 1920) := by
  classical
  have hsep : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric sf) (e b.surface - 1) := by
    intro b hb
    letI := b.base.isPrime
    rw [hsfdef]
    exact Low6969GateOrder.separant_order b.surface (hef b hb).1
  let g : Ideal GeoJets → ℕ := fun P => r - e P * a - m P
  have hg₁ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric G₁) (g b.surface) := by
    intro b hb
    letI := b.base.isPrime
    exact Low6969GateOrder.cofactor_order b.surface (hef b hb).2 (hmH b hb).2 (hQ₁ b hb)
  have hg₂ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric G₂) (g b.surface) := by
    intro b hb
    letI := b.base.isPrime
    exact Low6969GateOrder.cofactor_order b.surface (hef b hb).2 (hmH b hb).2 (hQ₂ b hb)
  have he1 : ∀ b ∈ F, 1 ≤ e b.surface := by
    intro b hb
    by_contra h0
    have h0' : e b.surface = 0 := by omega
    apply (hef b hb).2
    letI := b.base.isPrime
    rw [h0']
    unfold VanishesTo
    simp only [zero_add, pow_one]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ b.surface _).mpr
      (b.base.le (Ideal.subset_span (by simp)))
  have hgg := Low6969GateCount.pair_sum_tilted_rat D input F hF G₁ G₂ hG0' hG0 hGG htilt q₁ q₂ hb₁ hb₂ hc₁ hc₂ g g hg₁ hg₂
  have hmg := Low6969GateCount.pair_sum_tilted_rat D input F hF H G₁ hH0' hH0 hHG htilt qH q₁ hbH hb₁ hcH hc₁ m g
    (fun b hb => (hmH b hb).1) hg₁
  have hem := Low6969GateCount.pair_sum_tilted_rat D input F hF f H hf0' hf0 hfH htilt qf qH hbf hbH hcf hcH e m
    (fun b hb => (hef b hb).1) (fun b hb => (hmH b hb).1)
  have heg := Low6969GateCount.pair_sum_tilted_rat D input F hF f G₁ hf0' hf0 hfG htilt qf q₁ hbf hb₁ hcf hc₁ e g
    (fun b hb => (hef b hb).1) hg₁
  have hee := Low6969GateCount.pair_sum_tilted_rat D input F hF f sf hf0' hf0 hfs htilt qf qs hbf hbs hcf hcs e (fun P => e P - 1)
    (fun b hb => (hef b hb).1) hsep
  have hee' : ∑ b ∈ F, ((e b.surface : ℚ) * ((e b.surface : ℚ) - 1)) *
      ((b.weight * (D.points b).card : ℕ) : ℚ) ≤
      (Low6969Gate.tiltedPair (shape f).chamber qf qs : ℚ) / 1920 := by
    refine le_trans (le_of_eq ?_) hee
    apply Finset.sum_congr rfl
    intro b hb
    rw [Nat.cast_sub (he1 b hb)]; simp
  have h := Low6969GateAssembly.combine_branches F Branch.surface
    (fun b => b.weight * (D.points b).card) e m g ((r - a : ℕ) : ℚ) cc v _ _ _ _ _ hc0 hc1 hv
    (Nat.cast_nonneg _)
    (fun b hb => by
      have := hcert (e b.surface) (m b.surface) (he1 b hb)
      simpa only [g] using this)
    hgg hmg hem heg hee'
  exact h

theorem two_cut_count_ordinary (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F ⊆ D.branches) (H G₁ G₂ sf : Row 4)
    (qf qH q₁ q₂ qs : Shape) (hbf : InBox (shape f) qf) (hbH : InBox (shape H) qH)
    (hb₁ : InBox (shape G₁) q₁) (hb₂ : InBox (shape G₂) q₂) (hbs : InBox (shape sf) qs)
    (hcf : K1_13_6_2_3.ChamberBox qf) (hcH : K1_13_6_2_3.ChamberBox qH)
    (hc₁ : K1_13_6_2_3.ChamberBox q₁) (hc₂ : K1_13_6_2_3.ChamberBox q₂)
    (hcs : K1_13_6_2_3.ChamberBox qs) (r a : ℕ) (cc v : ℚ) (hc0 : 0 ≤ cc) (hc1 : cc ≤ 1)
    (hv : 0 ≤ v) (hcert : ClassCert r a cc v)
    (e m : Ideal GeoJets → ℕ)
    (hf0 : f ≠ 0) (hH0 : H ≠ 0) (hG0 : G₁ ≠ 0) (hf0' : toGeneric f ≠ 0) (hH0' : toGeneric H ≠ 0)
    (hG0' : toGeneric G₁ ≠ 0) (hsf : sf ≠ 0) (hsf' : toGeneric sf ≠ 0)
    (hfH : IsRelPrime (toGeneric f) (toGeneric H)) (hfG : IsRelPrime (toGeneric f) (toGeneric G₁))
    (hHG : IsRelPrime (toGeneric H) (toGeneric G₁)) (hGG : IsRelPrime (toGeneric G₁) (toGeneric G₂))
    (hfs : IsRelPrime (toGeneric f) (toGeneric sf))
    (hef : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric f) (e b.surface) ∧
      ¬ @VanishesTo _ _ b.surface b.base.isPrime (toGeneric f) (e b.surface + 1))
    (hmH : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric H) (m b.surface) ∧
      ¬ @VanishesTo _ _ b.surface b.base.isPrime (toGeneric H) (m b.surface + 1))
    (hsfdef : sf = K1_13_6.separant f)
    (hQ₁ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime
      ((toGeneric f) ^ a * (toGeneric H * toGeneric G₁)) r)
    (hQ₂ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime
      ((toGeneric f) ^ a * (toGeneric H * toGeneric G₂)) r)
    (hρ : a ≤ r) :
    ((r - a : ℕ) : ℚ) ^ 2 * (∑ b ∈ F, ((b.weight * (D.points b).card : ℕ) : ℚ)) ≤
      (1 - cc) * ((mixed32 q₁ q₂ (K1_13.chart (Low6969Prices.taylorLength + 1) (shape f).chamber) (K1_13.chart (Low6969Prices.taylorLength + 2) (shape f).chamber) : ℚ) / 32) +
      (mixed32 qH q₁ (K1_13.chart (Low6969Prices.taylorLength + 1) (shape f).chamber) (K1_13.chart (Low6969Prices.taylorLength + 2) (shape f).chamber) : ℚ) / 32 +
      ((r - a : ℕ) : ℚ) * ((mixed32 qf qH (K1_13.chart (Low6969Prices.taylorLength + 1) (shape f).chamber) (K1_13.chart (Low6969Prices.taylorLength + 2) (shape f).chamber) : ℚ) / 32) +
      cc * ((r - a : ℕ) : ℚ) *
        ((mixed32 qf q₁ (K1_13.chart (Low6969Prices.taylorLength + 1) (shape f).chamber) (K1_13.chart (Low6969Prices.taylorLength + 2) (shape f).chamber) : ℚ) / 32) +
      v * ((r - a : ℕ) : ℚ) ^ 2 *
        ((mixed32 qf qs (K1_13.chart (Low6969Prices.taylorLength + 1) (shape f).chamber) (K1_13.chart (Low6969Prices.taylorLength + 2) (shape f).chamber) : ℚ) / 32) := by
  classical
  have hsep : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric sf) (e b.surface - 1) := by
    intro b hb
    letI := b.base.isPrime
    rw [hsfdef]
    exact Low6969GateOrder.separant_order b.surface (hef b hb).1
  let g : Ideal GeoJets → ℕ := fun P => r - e P * a - m P
  have hg₁ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric G₁) (g b.surface) := by
    intro b hb
    letI := b.base.isPrime
    exact Low6969GateOrder.cofactor_order b.surface (hef b hb).2 (hmH b hb).2 (hQ₁ b hb)
  have hg₂ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric G₂) (g b.surface) := by
    intro b hb
    letI := b.base.isPrime
    exact Low6969GateOrder.cofactor_order b.surface (hef b hb).2 (hmH b hb).2 (hQ₂ b hb)
  have he1 : ∀ b ∈ F, 1 ≤ e b.surface := by
    intro b hb
    by_contra h0
    have h0' : e b.surface = 0 := by omega
    apply (hef b hb).2
    letI := b.base.isPrime
    rw [h0']
    unfold VanishesTo
    simp only [zero_add, pow_one]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ b.surface _).mpr
      (b.base.le (Ideal.subset_span (by simp)))
  have hgg := Low6969GateCount.pair_sum_ordinary_rat D input F hF G₁ G₂ hG0' hG0 hGG q₁ q₂ hc₁ hc₂ hb₁ hb₂ g g hg₁ hg₂
  have hmg := Low6969GateCount.pair_sum_ordinary_rat D input F hF H G₁ hH0' hH0 hHG qH q₁ hcH hc₁ hbH hb₁ m g
    (fun b hb => (hmH b hb).1) hg₁
  have hem := Low6969GateCount.pair_sum_ordinary_rat D input F hF f H hf0' hf0 hfH qf qH hcf hcH hbf hbH e m
    (fun b hb => (hef b hb).1) (fun b hb => (hmH b hb).1)
  have heg := Low6969GateCount.pair_sum_ordinary_rat D input F hF f G₁ hf0' hf0 hfG qf q₁ hcf hc₁ hbf hb₁ e g
    (fun b hb => (hef b hb).1) hg₁
  have hee := Low6969GateCount.pair_sum_ordinary_rat D input F hF f sf hf0' hf0 hfs qf qs hcf hcs hbf hbs e (fun P => e P - 1)
    (fun b hb => (hef b hb).1) hsep
  have hee' : ∑ b ∈ F, ((e b.surface : ℚ) * ((e b.surface : ℚ) - 1)) *
      ((b.weight * (D.points b).card : ℕ) : ℚ) ≤
      (mixed32 qf qs (K1_13.chart (Low6969Prices.taylorLength + 1) (shape f).chamber) (K1_13.chart (Low6969Prices.taylorLength + 2) (shape f).chamber) : ℚ) / 32 := by
    refine le_trans (le_of_eq ?_) hee
    apply Finset.sum_congr rfl
    intro b hb
    rw [Nat.cast_sub (he1 b hb)]; simp
  have h := Low6969GateAssembly.combine_branches F Branch.surface
    (fun b => b.weight * (D.points b).card) e m g ((r - a : ℕ) : ℚ) cc v _ _ _ _ _ hc0 hc1 hv
    (Nat.cast_nonneg _)
    (fun b hb => by
      have := hcert (e b.surface) (m b.surface) (he1 b hb)
      simpa only [g] using this)
    hgg hmg hem heg hee'
  exact h

theorem mark_bound_of_good {ρ N A R : ℚ} (hρ : 0 < ρ) (h : ρ ^ 2 * N ≤ R) (hgood : R ≤ A * ρ ^ 2) :
    N ≤ A := by
  have h2 : ρ ^ 2 * N ≤ ρ ^ 2 * A := by nlinarith [h, hgood]
  exact le_of_mul_le_mul_left h2 (by positivity)

end Low6969GateTwoCut

end Merged_Low6969GateTwoCut

-- merged module Low6969GateClass
section Merged_Low6969GateClass

set_option autoImplicit false

namespace Low6969GateClass

open Low6969GateTwoCut

def P0 (ρ a cc v : ℚ) (e : ℚ) : ℚ :=
  (1 - cc) * (ρ - (e - 1) * a) ^ 2 + cc * ρ * e * (ρ - (e - 1) * a) + v * ρ ^ 2 * (e * (e - 1)) - ρ ^ 2

def P1 (ρ a v : ℚ) (e : ℚ) : ℚ :=
  ρ * e * (ρ - (e - 1) * a) + v * ρ ^ 2 * (e * (e - 1)) - ρ ^ 2

theorem classCert_of_checks (r a : ℕ) (ha : a ≤ r) (cc v : ℚ) (hc0 : 0 ≤ cc) (hv : 0 ≤ v)
    (H1 : ∀ e : ℕ, 1 ≤ e → ((e : ℚ) - 1) * a < ((r - a : ℕ) : ℚ) →
      0 ≤ P0 ((r - a : ℕ) : ℚ) a cc v e ∧ 0 ≤ P1 ((r - a : ℕ) : ℚ) a v e)
    (H2 : ∀ e : ℕ, 1 ≤ e → ((r - a : ℕ) : ℚ) ≤ ((e : ℚ) - 1) * a →
      ((r - a : ℕ) : ℚ) ^ 2 ≤ v * ((r - a : ℕ) : ℚ) ^ 2 * ((e : ℚ) * ((e : ℚ) - 1))) :
    ClassCert r a cc v := by
  intro e m he
  set ρ : ℚ := ((r - a : ℕ) : ℚ) with hρ
  have hρnn : 0 ≤ ρ := Nat.cast_nonneg _
  have heq : (1 : ℚ) ≤ e := by exact_mod_cast he
  have hρr : ρ = (r : ℚ) - a := by rw [hρ, Nat.cast_sub ha]
  set R : ℚ := ρ - ((e : ℚ) - 1) * a with hR
  have hee : 0 ≤ (e : ℚ) * ((e : ℚ) - 1) := mul_nonneg (by linarith) (by linarith)
  have hm0 : (0 : ℚ) ≤ m := Nat.cast_nonneg _
  have hv' : 0 ≤ v * ρ ^ 2 * ((e : ℚ) * ((e : ℚ) - 1)) :=
    mul_nonneg (mul_nonneg hv (sq_nonneg _)) hee
  by_cases hRpos : ((e : ℚ) - 1) * a < ρ
  · -- R > 0
    have hR0 : 0 < R := by rw [hR]; linarith
    obtain ⟨h0, h1⟩ := H1 e he hRpos
    by_cases hmR : (m : ℚ) < R
    · -- g = R - m > 0
      have hg : ((r - e * a - m : ℕ) : ℚ) = R - m := by
        have hle : e * a + m ≤ r := by
          have : (e : ℚ) * a + m ≤ r := by
            have h' := hmR; rw [hR, hρr] at h'; linarith
          exact_mod_cast this
        rw [Nat.sub_sub, Nat.cast_sub hle]; push_cast; rw [hR, hρr]; ring
      rw [hg]
      set g : ℚ := R - m with hgdef
      have hg0 : 0 < g := by rw [hgdef]; linarith
      have hmg : (m : ℚ) = R - g := by rw [hgdef]; ring
      have hgR : g ≤ R := by rw [hgdef]; linarith
      have key : R * (((1 - cc) * (g * g) + (m : ℚ) * g + ρ * ((e : ℚ) * m) + cc * ρ * ((e : ℚ) * g) +
          v * ρ ^ 2 * ((e : ℚ) * ((e : ℚ) - 1))) - ρ ^ 2) =
          (R - g) * P1 ρ a v e + g * P0 ρ a cc v e + R * cc * g * (R - g) := by
        unfold P0 P1
        rw [hmg, ← hR]
        ring
      have hpos : 0 ≤ (R - g) * P1 ρ a v e + g * P0 ρ a cc v e + R * cc * g * (R - g) := by
        have := mul_nonneg (sub_nonneg.mpr hgR) h1
        have := mul_nonneg hg0.le h0
        have := mul_nonneg (mul_nonneg (mul_nonneg hR0.le hc0) hg0.le) (sub_nonneg.mpr hgR)
        linarith
      have hF : 0 ≤ ((1 - cc) * (g * g) + (m : ℚ) * g + ρ * ((e : ℚ) * m) + cc * ρ * ((e : ℚ) * g) +
          v * ρ ^ 2 * ((e : ℚ) * ((e : ℚ) - 1))) - ρ ^ 2 := by
        by_contra hneg
        push_neg at hneg
        have := mul_neg_of_pos_of_neg hR0 hneg
        linarith
      show ρ ^ 2 ≤ _
      linarith
    · -- m ≥ R, g = 0
      have hg : r - e * a - m = 0 := by
        have : (r : ℚ) ≤ e * a + m := by
          have h' := hmR; push_neg at h'; rw [hR, hρr] at h'; linarith
        have h' : r ≤ e * a + m := by exact_mod_cast this
        omega
      rw [hg]
      push_neg at hmR
      show ρ ^ 2 ≤ _
      simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, zero_add, sub_zero]
      have h1' := h1
      unfold P1 at h1'
      have hm' : ρ * (e : ℚ) * R ≤ ρ * e * m := by
        exact mul_le_mul_of_nonneg_left hmR (mul_nonneg hρnn (by linarith))
      rw [← hR] at h1'
      nlinarith [hm', h1']
  · -- R ≤ 0
    push_neg at hRpos
    have h2 := H2 e he hRpos
    have hg : r - e * a - m = 0 := by
      have : (r : ℚ) ≤ e * a + m := by rw [hρr] at hRpos; linarith
      have h' : r ≤ e * a + m := by exact_mod_cast this
      omega
    rw [hg]
    show ρ ^ 2 ≤ _
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, zero_add, sub_zero]
    have hmn : 0 ≤ ρ * ((e : ℚ) * m) := mul_nonneg hρnn (mul_nonneg (by linarith) hm0)
    linarith

end Low6969GateClass

end Merged_Low6969GateClass

-- merged module Low6969GateClassTable
section Merged_Low6969GateClassTable

set_option autoImplicit false

namespace Low6969GateClassTable

open Low6969GateTwoCut Low6969GateClass

def okE (ρ a cn vn e : ℤ) : Bool :=
  let R := ρ - (e - 1) * a
  decide (0 ≤ 10000000 * (2 * ρ - cn) * R ^ 2 + 10000000 * cn * ρ * e * R + 2 * ρ * (vn * ρ ^ 2 * (e * (e - 1)) - 10000000 * ρ ^ 2)) &&
  decide (0 ≤ 10000000 * ρ * e * R + vn * ρ ^ 2 * (e * (e - 1)) - 10000000 * ρ ^ 2)

def pairOK (r a k vn : ℕ) : Bool :=
  decide (1 ≤ a ∧ a < r) &&
    (let ρ : ℕ := r - a
     let cn : ℤ := min (2 * (ρ : ℤ)) ((k : ℤ) * a)
     let e0 : ℕ := (ρ + a - 1) / a + 1
     ((List.range (e0 - 1)).all fun i => okE ρ a cn vn ((i : ℤ) + 1)) &&
       decide (10000000 * (ρ : ℤ) ^ 2 ≤ (vn : ℤ) * (ρ : ℤ) ^ 2 * ((e0 : ℤ) * ((e0 : ℤ) - 1))))

theorem P0_scaled (ρ a cn vn : ℚ) (hρ : ρ ≠ 0) (e : ℚ) :
    P0 ρ a (cn / (2 * ρ)) (vn / 10000000) e =
      (10000000 * (2 * ρ - cn) * (ρ - (e - 1) * a) ^ 2 + 10000000 * cn * ρ * e * (ρ - (e - 1) * a) +
        2 * ρ * (vn * ρ ^ 2 * (e * (e - 1)) - 10000000 * ρ ^ 2)) / (2 * ρ * 10000000) := by
  unfold P0
  field_simp
  ring

theorem P1_scaled (ρ a vn : ℚ) (e : ℚ) :
    P1 ρ a (vn / 10000000) e =
      (10000000 * ρ * e * (ρ - (e - 1) * a) + vn * ρ ^ 2 * (e * (e - 1)) - 10000000 * ρ ^ 2) / 10000000 := by
  unfold P1
  field_simp

theorem okE_P (ρ a e : ℕ) (cn : ℤ) (vn : ℕ) (hρ : 0 < ρ) (h : okE ρ a cn vn e = true) :
    0 ≤ P0 (ρ : ℚ) a ((cn : ℚ) / (2 * ρ)) ((vn : ℚ) / 10000000) e ∧
      0 ≤ P1 (ρ : ℚ) a ((vn : ℚ) / 10000000) e := by
  unfold okE at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1⟩ := h
  have hρq : (ρ : ℚ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hρpos : (0 : ℚ) < ρ := by exact_mod_cast hρ
  constructor
  · rw [P0_scaled _ _ _ _ hρq]
    apply div_nonneg
    · have := Int.cast_nonneg (R := ℚ) h0
      push_cast at this
      linarith
    · positivity
  · rw [P1_scaled]
    apply div_nonneg
    · have := Int.cast_nonneg (R := ℚ) h1
      push_cast at this
      linarith
    · positivity

theorem pairOK_sound {r a k vn : ℕ} (h : pairOK r a k vn = true) :
    ClassCert r a (((min (2 * ((r - a : ℕ) : ℤ)) ((k : ℤ) * a) : ℤ) : ℚ) / (2 * ((r - a : ℕ) : ℚ)))
      ((vn : ℚ) / 10000000) := by
  unfold pairOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨ha1, har⟩, hall, htail⟩ := h
  set ρ : ℕ := r - a with hρdef
  have hρ : 0 < ρ := by omega
  set cn : ℤ := min (2 * (ρ : ℤ)) ((k : ℤ) * a) with hcn
  set e0 : ℕ := (ρ + a - 1) / a + 1 with he0
  have hρq : (0 : ℚ) < ρ := by exact_mod_cast hρ
  have hcn0 : 0 ≤ cn := by rw [hcn]; positivity
  apply Low6969GateClass.classCert_of_checks r a (by omega)
  · apply div_nonneg
    · exact_mod_cast hcn0
    · positivity
  · positivity
  · -- H1
    intro e he hlt
    have hlt' : (e - 1) * a < ρ := by
      have : (((e - 1 : ℕ) : ℚ)) * a < ρ := by
        rw [Nat.cast_sub he]; push_cast; exact hlt
      exact_mod_cast this
    have hea : e * a ≤ ρ + a - 1 := by
      have : e * a = (e - 1) * a + a := by
        obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
        simp [Nat.succ_mul]
      omega
    have hel : e ≤ (ρ + a - 1) / a := (Nat.le_div_iff_mul_le (by omega)).mpr hea
    have hmem : e - 1 < e0 - 1 := by omega
    have hok := List.all_eq_true.mp hall (e - 1) (List.mem_range.mpr hmem)
    have hcast : (((e - 1 : ℕ) : ℤ) + 1) = (e : ℤ) := by omega
    rw [hcast] at hok
    have := okE_P ρ a e cn vn hρ (by simpa using hok)
    simpa using this
  · -- H2
    intro e he hge
    have hge' : ρ ≤ (e - 1) * a := by
      have : (ρ : ℚ) ≤ (((e - 1 : ℕ) : ℚ)) * a := by
        rw [Nat.cast_sub he]; push_cast; exact hge
      exact_mod_cast this
    have he0le : e0 ≤ e := by
      have : (ρ + a - 1) / a ≤ e - 1 := by
        rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
        have : (e - 1) * a + (a - 1) ≥ ρ + a - 1 := by omega
        nlinarith [this]
      omega
    have hs : (10000000 : ℤ) * (ρ : ℤ) ^ 2 ≤ (vn : ℤ) * (ρ : ℤ) ^ 2 * ((e : ℤ) * ((e : ℤ) - 1)) := by
      have h0 : (e0 : ℤ) * ((e0 : ℤ) - 1) ≤ (e : ℤ) * ((e : ℤ) - 1) := by
        have : (e0 : ℤ) ≤ e := by exact_mod_cast he0le
        have h1 : 1 ≤ e0 := by rw [he0]; exact Nat.le_add_left _ _
        have : (1 : ℤ) ≤ e0 := by exact_mod_cast h1
        nlinarith
      have hv0 : 0 ≤ (vn : ℤ) * (ρ : ℤ) ^ 2 := by positivity
      calc (10000000 : ℤ) * (ρ : ℤ) ^ 2 ≤ (vn : ℤ) * (ρ : ℤ) ^ 2 * ((e0 : ℤ) * ((e0 : ℤ) - 1)) := htail
        _ ≤ _ := mul_le_mul_of_nonneg_left h0 hv0
    have hq : (10000000 : ℚ) * (ρ : ℚ) ^ 2 ≤ (vn : ℚ) * (ρ : ℚ) ^ 2 * ((e : ℚ) * ((e : ℚ) - 1)) := by
      exact_mod_cast hs
    show (ρ : ℚ) ^ 2 ≤ (vn : ℚ) / 10000000 * (ρ : ℚ) ^ 2 * ((e : ℚ) * ((e : ℚ) - 1))
    have : (vn : ℚ) / 10000000 * (ρ : ℚ) ^ 2 * ((e : ℚ) * ((e : ℚ) - 1)) =
        (vn : ℚ) * (ρ : ℚ) ^ 2 * ((e : ℚ) * ((e : ℚ) - 1)) / 10000000 := by ring
    rw [this, le_div_iff₀ (by norm_num)]
    linarith

def decode (w a : ℕ) : ℕ × ℕ :=
  let s := (w / 256 / 2 ^ (28 * (a - 1))) % 2 ^ 28
  (s % 16, s / 16)

def levelOK (r w : ℕ) : Bool :=
  (List.range (w % 256)).all fun i => pairOK r (i + 1) (decode w (i + 1)).1 (decode w (i + 1)).2

def tableOK : ℕ → List ℕ → Bool
  | _, [] => true
  | r, w :: ws => levelOK r w && tableOK (r + 1) ws



theorem tableOK_level : ∀ {ws : List ℕ} {r0 : ℕ}, tableOK r0 ws = true → ∀ j, j < ws.length →
    levelOK (r0 + j) (ws.getD j 0) = true := by
  intro ws
  induction ws with
  | nil => intro r0 _ j hj; simp at hj
  | cons w ws ih =>
    intro r0 h j hj
    simp only [tableOK, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := ih h.2 j (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

def lookup (r0 : ℕ) (ws : List ℕ) (r a : ℕ) : Option (ℕ × ℕ) :=
  if r0 ≤ r ∧ r - r0 < ws.length ∧ 1 ≤ a ∧ a ≤ ws.getD (r - r0) 0 % 256 then
    some (decode (ws.getD (r - r0) 0) a)
  else none

theorem table_sound {r0 : ℕ} {ws : List ℕ} (h : tableOK r0 ws = true) {r a k vn : ℕ}
    (hl : lookup r0 ws r a = some (k, vn)) :
    ClassCert r a (((min (2 * ((r - a : ℕ) : ℤ)) ((k : ℤ) * a) : ℤ) : ℚ) / (2 * ((r - a : ℕ) : ℚ)))
      ((vn : ℚ) / 10000000) := by
  unfold lookup at hl
  split_ifs at hl with hc
  obtain ⟨hr0, hrl, ha1, hamax⟩ := hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, rfl⟩ := hl
  have hj := tableOK_level h (r - r0) hrl
  unfold levelOK at hj
  have hmem : a - 1 ∈ List.range (ws.getD (r - r0) 0 % 256) := List.mem_range.mpr (by omega)
  have hp := List.all_eq_true.mp hj (a - 1) hmem
  have hr : r0 + (r - r0) = r := by omega
  have hae : a - 1 + 1 = a := by omega
  rw [hr, hae] at hp
  exact pairOK_sound hp

end Low6969GateClassTable

end Merged_Low6969GateClassTable

-- merged module Low6969GateCertCF
section Merged_Low6969GateCertCF

set_option autoImplicit false

namespace Low6969GateCertCF
open Low6969GateTwoCut Low6969GateClass

theorem cf_sound (r a : ℕ) (ha : a < r) (v : ℚ) (hv : (a : ℚ) ^ 2 ≤ v * ((r - a : ℕ) : ℚ) ^ 2) :
    ClassCert r a 1 v := by
  have hρ : (0 : ℚ) < ((r - a : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt ha
  set ρ : ℚ := ((r - a : ℕ) : ℚ) with hρd
  have hρr : ρ = (r : ℚ) - a := by rw [hρd, Nat.cast_sub ha.le]
  have hv0 : 0 ≤ v := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (a : ℚ), mul_pos hρ hρ, mul_neg_of_neg_of_pos h (mul_pos hρ hρ)]
  apply Low6969GateClass.classCert_of_checks r a ha.le 1 v (by norm_num) hv0
  · intro e he hlt
    have he' : (1 : ℚ) ≤ e := by exact_mod_cast he
    set u : ℚ := (e : ℚ) - 1 with hu
    have hu0 : 0 ≤ u := by rw [hu]; linarith
    have hlt' : u * (a : ℚ) < ρ := hlt
    have hR : 0 < ρ - u * a := sub_pos.mpr hlt'
    have key : 0 ≤ ρ * (u + 1) * (ρ - u * a) + v * ρ ^ 2 * ((u + 1) * u) - ρ ^ 2 := by
      have h1 : ρ * (u + 1) * (ρ - u * a) + v * ρ ^ 2 * ((u + 1) * u) - ρ ^ 2 =
          ρ * u * (ρ - (u + 1) * a + v * ρ * (u + 1)) := by ring
      rw [h1]
      have h2 : 0 ≤ ρ - (u + 1) * a + v * ρ * (u + 1) := by
        have h3 : (u + 1) * a * (ρ - a) ≤ ρ * ρ := by
          have : (u + 1) * a < ρ + a := by nlinarith [hlt']
          have ha0 : (0 : ℚ) ≤ a := Nat.cast_nonneg _
          by_cases hρa : (a : ℚ) ≤ ρ
          · nlinarith [mul_le_mul_of_nonneg_right this.le (sub_nonneg.mpr hρa)]
          · push_neg at hρa
            have : (u + 1) * a * (ρ - a) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) ha0) (by linarith)
            nlinarith [mul_pos hρ hρ]
        have h4 : (a : ℚ) ^ 2 * (u + 1) ≤ v * ρ * (u + 1) * ρ := by nlinarith [mul_le_mul_of_nonneg_right hv (by linarith : (0 : ℚ) ≤ u + 1)]
        have h5 : 0 ≤ (ρ - (u + 1) * a + v * ρ * (u + 1)) * ρ := by nlinarith
        exact nonneg_of_mul_nonneg_left h5 hρ
      positivity
    constructor
    · unfold P0; simp only [hu] at key ⊢; nlinarith [key]
    · unfold P1; simp only [hu] at key ⊢; nlinarith [key]
  · intro e he hge
    have he' : (1 : ℚ) ≤ e := by exact_mod_cast he
    have hu0 : (1 : ℚ) ≤ e := he'
    have hge' : ρ ≤ ((e : ℚ) - 1) * a := hge
    have : ρ ^ 2 ≤ v * ρ ^ 2 * ((e : ℚ) * ((e : ℚ) - 1)) := by
      have hea : ρ ≤ ((e : ℚ) - 1) * a := hge'
      have ha0 : (0 : ℚ) < a := by
        by_contra h; push_neg at h
        have : (a : ℚ) = 0 := le_antisymm h (Nat.cast_nonneg _)
        rw [this] at hea; simp at hea; linarith
      have hee : ρ ^ 2 ≤ ((e : ℚ) - 1) ^ 2 * a ^ 2 := by nlinarith
      have hee2 : ((e : ℚ) - 1) ^ 2 ≤ (e : ℚ) * ((e : ℚ) - 1) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hv (mul_nonneg (by linarith : (0 : ℚ) ≤ e) (by linarith : (0 : ℚ) ≤ (e : ℚ) - 1)),
        mul_nonneg hρ.le hρ.le]
    exact this

def cvOf (r0 : ℕ) (ws : List ℕ) (r a : ℕ) : ℕ × ℕ :=
  bif Nat.beq a 0 then (0, 0)
  else match Low6969GateClassTable.lookup r0 ws r a with
    | some (k, vn) => (min (2 * (r - a)) (k * a), vn)
    | none => (2 * (r - a), (10000000 * a * a + (r - a) * (r - a) - 1) / ((r - a) * (r - a)))

theorem ceil_mul (N D : ℕ) (hD : 0 < D) : N ≤ ((N + D - 1) / D) * D := by
  have h1 := Nat.div_add_mod (N + D - 1) D
  have h2 := Nat.mod_lt (N + D - 1) hD
  rw [Nat.mul_comm] at h1
  omega

noncomputable def certF (r0 : ℕ) (ws : List ℕ) (r a : ℕ) : ℚ × ℚ :=
  (((cvOf r0 ws r a).1 : ℚ) / (2 * ((r - a : ℕ) : ℚ)), ((cvOf r0 ws r a).2 : ℚ) / 10000000)

theorem cvOf_le (r0 : ℕ) (ws : List ℕ) (r a : ℕ) : (cvOf r0 ws r a).1 ≤ 2 * (r - a) := by
  unfold cvOf
  cases h : Nat.beq a 0
  · simp only [Bool.cond_false]
    split <;> simp
  · simp

theorem certF_bounds (r0 : ℕ) (ws : List ℕ) (r a : ℕ) :
    0 ≤ (certF r0 ws r a).1 ∧ (certF r0 ws r a).1 ≤ 1 ∧ 0 ≤ (certF r0 ws r a).2 := by
  unfold certF
  refine ⟨by positivity, ?_, by positivity⟩
  by_cases hρ : r - a = 0
  · simp [hρ]
  · have hρq : (0 : ℚ) < ((r - a : ℕ) : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hρ
    rw [div_le_one (by positivity)]
    exact_mod_cast cvOf_le r0 ws r a

theorem certF_class {r0 : ℕ} {ws : List ℕ} (ht : Low6969GateClassTable.tableOK r0 ws = true) {r a : ℕ} (ha : a < r) :
    ClassCert r a (certF r0 ws r a).1 (certF r0 ws r a).2 := by
  unfold certF cvOf
  by_cases h0 : a = 0
  · subst h0
    simpa using classCert_zero r
  · have hb : Nat.beq a 0 = false := by
      rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨n, hn⟩
      rw [hn]; rfl
    simp only [hb, Bool.cond_false]
    split
    · rename_i k vn hl
      have e : (((min (2 * (r - a)) (k * a) : ℕ)) : ℚ) =
          (((min (2 * ((r - a : ℕ) : ℤ)) ((k : ℤ) * a) : ℤ)) : ℚ) := by
        have : ((min (2 * (r - a)) (k * a) : ℕ) : ℤ) = min (2 * ((r - a : ℕ) : ℤ)) ((k : ℤ) * a) := by
          push_cast; rfl
        exact_mod_cast this
      show ClassCert r a (((min (2 * (r - a)) (k * a) : ℕ) : ℚ) / (2 * ((r - a : ℕ) : ℚ))) ((vn : ℚ) / 10000000)
      rw [e]
      exact Low6969GateClassTable.table_sound ht hl
    · rename_i hl
      simp only
      have hρ : 0 < r - a := Nat.sub_pos_of_lt ha
      have hρq : (0 : ℚ) < ((r - a : ℕ) : ℚ) := by exact_mod_cast hρ
      have e1 : ((2 * (r - a) : ℕ) : ℚ) / (2 * ((r - a : ℕ) : ℚ)) = 1 := by
        push_cast; field_simp
      rw [e1]
      apply cf_sound r a ha
      have hq : (a : ℚ) ^ 2 * 10000000 ≤ (((10000000 * a * a + (r - a) * (r - a) - 1) / ((r - a) * (r - a)) : ℕ) : ℚ) *
          ((r - a : ℕ) : ℚ) ^ 2 := by
        have h2 := ceil_mul (10000000 * a * a) ((r - a) * (r - a)) (Nat.mul_pos hρ hρ)
        have h3 : ((10000000 * a * a : ℕ) : ℚ) ≤ ((((10000000 * a * a + (r - a) * (r - a) - 1) / ((r - a) * (r - a))) * ((r - a) * (r - a)) : ℕ) : ℚ) := by
          exact_mod_cast h2
        push_cast at h3 ⊢
        nlinarith [h3]
      push_cast
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℚ) < 10000000)]
      linarith

end Low6969GateCertCF

end Merged_Low6969GateCertCF
end Z6969Source2417

-- Source: ProximityPrize.SubmissionLower.Low6969GateRows
section Z6969Source2418
set_option autoImplicit true
set_option Elab.async false

-- merged module Low6969GateFlat
section Merged_Low6969GateFlat

set_option autoImplicit false
set_option Elab.async false

namespace Low6969GateFlat

open Low6969SharedRational (toGeometric FractionJet)
open K1_13_6 (GenericField GeoField GeoJets)
open K1_13_5_4_4 (regular_cut_of_flat_map)
open K1_13_6_2_4_4 (relPrime_of_regular)

theorem pair_regular_fraction {F G : FractionJet} (hrel : IsRelPrime F G) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {F}) G) := by
  apply (isLeftRegular_iff_right_eq_zero_of_mul).mpr
  intro x hx
  obtain ⟨D, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr (hrel.dvd_of_dvd_mul_left hx))

theorem isRelPrime_toGeometric {G₁ G₂ : FractionJet} (h₁ : G₁ ≠ 0)
    (hrel : IsRelPrime G₁ G₂) : IsRelPrime (toGeometric G₁) (toGeometric G₂) := by
  have hreg := pair_regular_fraction hrel
  have hf : IsSMulRegular (FractionJet) G₁ := by
    intro x y hxy
    exact mul_left_cancel₀ h₁ hxy
  have hflat : (algebraMap GenericField GeoField).Flat := by
    letI : Algebra GenericField GeoField := (algebraMap GenericField GeoField).toAlgebra
    have h : Module.Flat GenericField GeoField := inferInstance
    exact h
  have h2 := regular_cut_of_flat_map (algebraMap GenericField GeoField) hflat hf hreg
  have hne : toGeometric G₁ ≠ 0 := by
    intro h
    apply h₁
    exact MvPolynomial.map_injective _ (algebraMap GenericField GeoField).injective
      (h.trans (map_zero _).symm)
  exact relPrime_of_regular hne h2

end Low6969GateFlat

end Merged_Low6969GateFlat

-- merged module Low6969GateClear
section Merged_Low6969GateClear

set_option autoImplicit false
set_option Elab.async false

namespace Low6969GateClear

open Low6969SharedRational (FractionJet toGeometric toFraction clear_denominators fraction_geometric)
open K1_13 (Row shape Geom)
open scoped Polynomial
open K1_13_6 (GeoJets GeoField toGeneric)
open K1_13_6_1_2 (VanishesTo)
open Low6969SharedPrice (coord)
open Low6969SharedChooseCut (weight_coord)


theorem coord_eq_shp (A0' : Row 4) (A0 : FractionJet) (h : A0'.support = A0.support) (i : Fin 3) :
    coord (shape A0') i = Low6969GateShape.shp i A0 := by
  rw [weight_coord]
  unfold Low6969GateShape.shp MvPolynomial.weightedTotalDegree
  rw [h]
  fin_cases i <;> rfl

theorem vanishesTo_C_mul (P : Ideal GeoJets) [P.IsPrime] {u : GeoField} (hu : u ≠ 0) {B0 : GeoJets} {n : ℕ} :
    VanishesTo P (MvPolynomial.C u * B0) n ↔ VanishesTo P B0 n := by
  constructor
  · intro h
    have hu' : MvPolynomial.C u⁻¹ * (MvPolynomial.C u * B0) = B0 := by
      rw [← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hu, MvPolynomial.C_1, one_mul]
    rw [← hu']
    unfold VanishesTo at *
    change algebraMap GeoJets (Localization.AtPrime P) _ ∈ _ at h ⊢
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ h
  · intro h
    unfold VanishesTo at *
    change algebraMap GeoJets (Localization.AtPrime P) _ ∈ _ at h ⊢
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ h

theorem isRelPrime_C_mul_right {u : GeoField} (hu : u ≠ 0) {A0 B0 : GeoJets} (h : IsRelPrime A0 B0) :
    IsRelPrime A0 (MvPolynomial.C u * B0) := by
  intro d hd1 hd2
  have hc : IsUnit (MvPolynomial.C u : GeoJets) := (Ne.isUnit hu).map MvPolynomial.C
  exact h hd1 ((hc.dvd_mul_left).mp hd2)

theorem isRelPrime_C_mul_left {u : GeoField} (hu : u ≠ 0) {A0 B0 : GeoJets} (h : IsRelPrime A0 B0) :
    IsRelPrime (MvPolynomial.C u * A0) B0 := by
  intro d hd1 hd2
  have hc : IsUnit (MvPolynomial.C u : GeoJets) := (Ne.isUnit hu).map MvPolynomial.C
  exact h ((hc.dvd_mul_left).mp hd1) hd2

end Low6969GateClear

end Merged_Low6969GateClear

-- merged module Low6969GateRows
section Merged_Low6969GateRows

set_option autoImplicit false
set_option Elab.async false

namespace Low6969GateRows

open Low6969SharedRational (FractionJet toGeometric toFraction fraction_geometric)
open K1_13 (Row shape Geom)
open K1_13_6 (GeoJets GeoField GenericField toGeneric)
open K1_13_6_1_2 (VanishesTo)
open Low6969SharedPrice (coord)
open scoped Polynomial

theorem shp_pow {F : Type*} [Field F] {p : MvPolynomial (Fin 4) F} (hp : p ≠ 0) (a : ℕ) (i : Fin 3) :
    Low6969GateShape.shp i (p ^ a) = a * Low6969GateShape.shp i p := by
  induction a with
  | zero =>
    simp [Low6969GateShape.shp, MvPolynomial.weightedTotalDegree]
  | succ a ih =>
    rw [pow_succ, Low6969GateShape.shp_mul (pow_ne_zero _ hp) hp, ih]; ring

theorem support_toFraction (f : Row 4) : (toFraction f).support = f.support :=
  MvPolynomial.support_map_of_injective f (IsFractionRing.injective (Polynomial Geom) GenericField)

theorem shp_toFraction (f : Row 4) (i : Fin 3) :
    Low6969GateShape.shp i (toFraction f) = coord (shape f) i :=
  (Low6969GateClear.coord_eq_shp f (toFraction f) (support_toFraction f).symm i).symm

theorem toFraction_ne_zero {f : Row 4} (hf : f ≠ 0) : toFraction f ≠ 0 := by
  intro h
  apply hf
  exact MvPolynomial.map_injective _ (IsFractionRing.injective (Polynomial Geom) GenericField)
    (h.trans (map_zero _).symm)

theorem toFraction_not_unit {f : Row 4} (hdeg : 0 < f.totalDegree) : ¬ IsUnit (toFraction f) := by
  rw [MvPolynomial.isUnit_iff_totalDegree_of_isReduced]
  have : (toFraction f).totalDegree = f.totalDegree := by
    unfold MvPolynomial.totalDegree
    rw [support_toFraction]
  omega

theorem isRelPrime_scaled {a b : FractionJet} (ha : a ≠ 0) (hrel : IsRelPrime a b) {a' b' : Row 4} {ua ub : GeoField}
    (hua : ua ≠ 0) (hub : ub ≠ 0) (ha' : toGeneric a' = MvPolynomial.C ua * toGeometric a)
    (hb' : toGeneric b' = MvPolynomial.C ub * toGeometric b) :
    IsRelPrime (toGeneric a') (toGeneric b') := by
  have h := Low6969GateFlat.isRelPrime_toGeometric ha hrel
  rw [ha', hb']
  exact Low6969GateClear.isRelPrime_C_mul_left hua (Low6969GateClear.isRelPrime_C_mul_right hub h)

theorem clear_frac (X0 : FractionJet) :
    ∃ X' : Row 4, X'.support = X0.support ∧ ∃ c : GenericField, c ≠ 0 ∧
      toFraction X' = MvPolynomial.C c * X0 := by
  obtain ⟨d, Q, hd, hS, hQ⟩ := Low6969SharedRational.clear_denominators X0
  refine ⟨Q, hS, algebraMap (Polynomial Geom) GenericField d, ?_, hQ⟩
  intro h
  exact hd ((IsFractionRing.injective (Polynomial Geom) GenericField) (h.trans (map_zero _).symm))

theorem toGeneric_clear {X' : Row 4} {X0 : FractionJet} {c : GenericField}
    (h : toFraction X' = MvPolynomial.C c * X0) :
    toGeneric X' = MvPolynomial.C (algebraMap GenericField GeoField c) * toGeometric X0 := by
  rw [← fraction_geometric, h, map_mul]
  simp [toGeometric]

theorem algebraMap_ne_zero {c : GenericField} (hc : c ≠ 0) : algebraMap GenericField GeoField c ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap GenericField GeoField).injective).mpr hc

set_option maxHeartbeats 1600000 in
theorem rows_from_subspace [Infinite GenericField] (f : Row 4) (hfirr : Irreducible f)
    (hdeg : 0 < f.totalDegree) (U : Submodule GenericField FractionJet) (hU : U ≠ ⊥) (r : ℕ)
    (S : Finset (Ideal GeoJets)) (hS : ∀ P ∈ S, P.IsPrime)
    (hcontact : ∀ Q ∈ U, ∀ (P : Ideal GeoJets) (hP : P ∈ S),
      @VanishesTo _ _ P (hS P hP) (toGeometric Q) r)
    (B : Fin 3 → ℕ) (hB : ∀ Q ∈ U, ∀ i, Low6969GateShape.shp i Q ≤ B i) :
    ∃ (a : ℕ) (H G₁ G₂ : Row 4), H ≠ 0 ∧ G₁ ≠ 0 ∧
      IsRelPrime (toGeneric f) (toGeneric H) ∧ IsRelPrime (toGeneric f) (toGeneric G₁) ∧
      IsRelPrime (toGeneric H) (toGeneric G₁) ∧ IsRelPrime (toGeneric G₁) (toGeneric G₂) ∧
      (∀ (P : Ideal GeoJets) (hP : P ∈ S), @VanishesTo _ _ P (hS P hP)
        ((toGeneric f) ^ a * (toGeneric H * toGeneric G₁)) r) ∧
      (∀ (P : Ideal GeoJets) (hP : P ∈ S), @VanishesTo _ _ P (hS P hP)
        ((toGeneric f) ^ a * (toGeneric H * toGeneric G₂)) r) ∧
      (∀ i, coord (shape G₁) i ≤ B i - (a * coord (shape f) i + coord (shape H) i)) ∧
      (∀ i, coord (shape G₂) i ≤ B i - (a * coord (shape f) i + coord (shape H) i)) ∧
      Module.finrank GenericField U ≤
        Low6969GateShape.free (fun i => B i - (a * coord (shape f) i + coord (shape H) i)) ∧
      (∀ i, a * coord (shape f) i + coord (shape H) i ≤ B i) ∧
      (coord (shape H) 2 ≤ coord (shape H) 0 ∧ 3 * coord (shape H) 2 ≤ coord (shape H) 1 ∧
        coord (shape H) 1 ≤ 2 * coord (shape H) 0 + coord (shape H) 2) := by
  classical
  have hf0 : f ≠ 0 := hfirr.ne_zero
  have hfF0 := toFraction_ne_zero hf0
  have hfFn := toFraction_not_unit hdeg
  obtain ⟨g0, hg0, V', hV', hdiv, hno⟩ := Low6969GateGcd.gcd_split U hU
  obtain ⟨a, h', hgh, hnd⟩ := Low6969GateGcd.split_power_nonunit (toFraction f) g0 hfFn hg0
  have hh0 : h' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hgh
    exact hg0 hgh
  have hT0 : toFraction f * h' ≠ 0 := mul_ne_zero hfF0 hh0
  have hTn : ¬ IsUnit (toFraction f * h') := fun h => hfFn (isUnit_of_mul_isUnit_left h)
  obtain ⟨G1, hG1, G2, hG2, hG10, hrelT1, hrel12⟩ := Low6969GateGcd.two_general V' hno hT0 hTn
  have hmem : ∀ G, G ∈ V' → g0 * G ∈ U := fun G hG => by rw [hV'] at hG; exact hG
  obtain ⟨H, hHs, cH, hcH, hHf⟩ := clear_frac h'
  obtain ⟨K1, hK1s, c1, hc1, hK1f⟩ := clear_frac G1
  obtain ⟨K2, hK2s, c2, hc2, hK2f⟩ := clear_frac G2
  have hH0 : H ≠ 0 := by
    intro h; apply hh0
    have := congrArg MvPolynomial.support h
    rw [hHs, MvPolynomial.support_zero] at this
    exact MvPolynomial.support_eq_empty.mp this
  have hK10 : K1 ≠ 0 := by
    intro h; apply hG10
    have := congrArg MvPolynomial.support h
    rw [hK1s, MvPolynomial.support_zero] at this
    exact MvPolynomial.support_eq_empty.mp this
  have eH := toGeneric_clear hHf
  have e1 := toGeneric_clear hK1f
  have e2 := toGeneric_clear hK2f
  have ef : toGeneric f = MvPolynomial.C (1 : GeoField) * toGeometric (toFraction f) := by
    rw [fraction_geometric]; simp
  have hfG1 : IsRelPrime (toFraction f) G1 := hrelT1.of_mul_left_left
  have hhG1 : IsRelPrime h' G1 := hrelT1.of_mul_left_right
  have hnotdvd : ¬ f ∣ H := by
    intro ⟨w, hw⟩
    apply hnd
    have h1 : toFraction f ∣ MvPolynomial.C cH * h' := by
      rw [← hHf]
      exact ⟨toFraction w, by rw [hw]; simp [toFraction, map_mul]⟩
    have hu : IsUnit (MvPolynomial.C cH : FractionJet) := (Ne.isUnit hcH).map MvPolynomial.C
    exact (hu.dvd_mul_left).mp h1
  have hgfrac : toGeometric g0 = (toGeneric f) ^ a * toGeometric h' := by
    rw [hgh, map_mul, map_pow, fraction_geometric]
  have shp_g0 : ∀ i, Low6969GateShape.shp i g0 = a * coord (shape f) i + coord (shape H) i := by
    intro i
    rw [hgh, Low6969GateShape.shp_mul (pow_ne_zero a hfF0) hh0, shp_pow hfF0, shp_toFraction,
      ← Low6969GateClear.coord_eq_shp H h' hHs i]
  have contact_of : ∀ (G : FractionJet) (K : Row 4) (c : GenericField), G ∈ V' →
      toFraction K = MvPolynomial.C c * G → c ≠ 0 →
      ∀ (P : Ideal GeoJets) (hP : P ∈ S), @VanishesTo _ _ P (hS P hP)
        ((toGeneric f) ^ a * (toGeneric H * toGeneric K)) r := by
    intro G K c hG hKf hc P hP
    haveI := hS P hP
    have hq := hcontact (g0 * G) (hmem G hG) P hP
    have eK := toGeneric_clear hKf
    have hrew : (toGeneric f) ^ a * (toGeneric H * toGeneric K) =
        MvPolynomial.C (algebraMap GenericField GeoField cH * algebraMap GenericField GeoField c) *
          toGeometric (g0 * G) := by
      rw [eH, eK, show toGeometric (g0 * G) = toGeometric g0 * toGeometric G from map_mul _ _ _, hgfrac,
        MvPolynomial.C_mul]; ring
    rw [hrew]
    exact (Low6969GateClear.vanishesTo_C_mul P
      (mul_ne_zero (algebraMap_ne_zero hcH) (algebraMap_ne_zero hc))).mpr hq
  have shape_of : ∀ (G : FractionJet) (K : Row 4), G ∈ V' → K.support = G.support → ∀ i,
      coord (shape K) i ≤ B i - (a * coord (shape f) i + coord (shape H) i) := by
    intro G K hG hKs i
    rw [Low6969GateClear.coord_eq_shp K G hKs i]
    by_cases hG0 : G = 0
    · subst hG0; simp [Low6969GateShape.shp, MvPolynomial.weightedTotalDegree]
    · have h1 := hB (g0 * G) (hmem G hG) i
      rw [Low6969GateShape.shp_mul hg0 hG0, shp_g0] at h1
      omega
  have fitsx : ∀ i, a * coord (shape f) i + coord (shape H) i ≤ B i := by
    intro i
    have h1 := hB (g0 * G1) (hmem G1 hG1) i
    rw [Low6969GateShape.shp_mul hg0 hG10, shp_g0] at h1
    omega
  have validH : coord (shape H) 2 ≤ coord (shape H) 0 ∧ 3 * coord (shape H) 2 ≤ coord (shape H) 1 ∧
      coord (shape H) 1 ≤ 2 * coord (shape H) 0 + coord (shape H) 2 := by
    have := Low6969GateShape.shp_valid hh0
    rw [Low6969GateClear.coord_eq_shp H h' hHs 0, Low6969GateClear.coord_eq_shp H h' hHs 1,
      Low6969GateClear.coord_eq_shp H h' hHs 2]
    exact this
  refine ⟨a, H, K1, K2, hH0, hK10, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fitsx, validH⟩
  · exact K1_13_7_1.proper_generic f H hfirr hnotdvd
  · exact isRelPrime_scaled hfF0 hfG1 one_ne_zero (algebraMap_ne_zero hc1) ef e1
  · exact isRelPrime_scaled hh0 hhG1 (algebraMap_ne_zero hcH) (algebraMap_ne_zero hc1) eH e1
  · exact isRelPrime_scaled hG10 hrel12 (algebraMap_ne_zero hc1) (algebraMap_ne_zero hc2) e1 e2
  · exact contact_of G1 K1 c1 hG1 hK1f hc1
  · exact contact_of G2 K2 c2 hG2 hK2f hc2
  · exact shape_of G1 K1 hG1 hK1s
  · exact shape_of G2 K2 hG2 hK2s
  · have := Low6969GateShape.dim_le_free U g0 hg0 hdiv B hB
    simpa only [shp_g0] using this

end Low6969GateRows

end Merged_Low6969GateRows
end Z6969Source2418

-- Source: ProximityPrize.SubmissionLower.Low6969GateGate
section Z6969Source2419
set_option autoImplicit true
set_option Elab.async false

set_option autoImplicit false

namespace Low6969GateGate

open Module

section Overlap

variable {𝕜 E ι : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]

theorem threshold_overlap (s : Finset ι) (V M : ι → Submodule 𝕜 E) (W : ι → ℕ)
    (h : (∑ i ∈ s, (finrank 𝕜 E - finrank 𝕜 (M i) + W i)) < ∑ i ∈ s, finrank 𝕜 (V i)) :
    ∃ i ∈ s, W i < finrank 𝕜 ↥(V i ⊓ M i) := by
  classical
  by_contra! hn
  apply Nat.not_lt_of_ge ?_ h
  refine Finset.sum_le_sum fun i hi => ?_
  have he := Submodule.finrank_sup_add_finrank_inf_eq (V i) (M i)
  have hsup := (V i ⊔ M i).finrank_le
  have hi' := hn i hi
  omega

end Overlap

section Gate

variable {𝕜 E ι : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable {G : Type*}

theorem gate₂ (Target : Prop) (s : Finset ι) (V M : ι → Submodule 𝕜 E) (W : ι → ℕ)
    (Good : ι → G → Prop) (free : ι → G → ℕ)
    (hdich : ∀ i ∈ s, ∀ U : Submodule 𝕜 E, U ≤ V i ⊓ M i → U ≠ ⊥ →
      ∃ g : G, finrank 𝕜 U ≤ free i g ∧ (Good i g → Target))
    (hW : ∀ i ∈ s, ∀ g : G, ¬ Good i g → free i g ≤ W i)
    (hsum : (∑ i ∈ s, (finrank 𝕜 E - finrank 𝕜 (M i) + W i)) < ∑ i ∈ s, finrank 𝕜 (V i)) :
    Target := by
  obtain ⟨i, hi, hlt⟩ := threshold_overlap s V M W hsum
  have hne : (V i ⊓ M i) ≠ ⊥ := by
    intro hb
    rw [hb, _root_.finrank_bot] at hlt
    exact Nat.not_lt_zero _ hlt
  obtain ⟨g, hfin, hgood⟩ := hdich i hi (V i ⊓ M i) le_rfl hne
  by_cases hG : Good i g
  · exact hgood hG
  · exact absurd (hfin.trans (hW i hi g hG)) (Nat.not_le_of_lt hlt)

theorem gate₂_of_need (Target : Prop) (s : Finset ι) (V M : ι → Submodule 𝕜 E) (W : ι → ℕ)
    (Good : ι → G → Prop) (free : ι → G → ℕ) (need : ℕ)
    (hdich : ∀ i ∈ s, ∀ U : Submodule 𝕜 E, U ≤ V i ⊓ M i → U ≠ ⊥ →
      ∃ g : G, finrank 𝕜 U ≤ free i g ∧ (Good i g → Target))
    (hW : ∀ i ∈ s, ∀ g : G, ¬ Good i g → free i g ≤ W i)
    (hneed : need ≤ ∑ i ∈ s, finrank 𝕜 (V i))
    (hsum : (∑ i ∈ s, (finrank 𝕜 E - finrank 𝕜 (M i) + W i)) < need) :
    Target :=
  gate₂ Target s V M W Good free hdich hW (hsum.trans_le hneed)

end Gate

end Low6969GateGate
end Z6969Source2419

-- Source: ProximityPrize.SubmissionLower.Low6969GateAmb
section Z6969Source2420
set_option autoImplicit true
set_option Elab.async false

-- merged module Low6969GateBox
section Merged_Low6969GateBox

set_option autoImplicit false
set_option Elab.async false

namespace Low6969GateBox

open K1_13_6 (GenericField)
open K1_13_2_2 (JetExp oldWeight gradeWeight)
open ExpandedColumns6970 (jetColumns jetExponents)
open MvPolynomial Finset
open Low6969SharedShapeRank (ambient)

def fitsBox (b j t : ℕ) (m : JetExp) : Prop :=
  m.weight gradeWeight ≤ b ∧ m.weight oldWeight ≤ j ∧ m 3 ≤ t

noncomputable instance (b j t : ℕ) (m : JetExp) : Decidable (fitsBox b j t m) := by
  unfold fitsBox; infer_instance


noncomputable def ambCount (b j t : ℕ) : ℕ := (jetColumns.filter (fitsBox b j t)).card

noncomputable def boxSpace (b j t : ℕ) : Submodule GenericField ambient :=
  (restrictSupport GenericField (↑(jetColumns.filter (fitsBox b j t)))).comap ambient.subtype

theorem boxSpace_dim (b j t : ℕ) : Module.finrank GenericField (boxSpace b j t) = ambCount b j t := by
  have hle : restrictSupport GenericField (↑(jetColumns.filter (fitsBox b j t))) ≤ ambient := by
    intro Q hQ m hm
    have hw := Finset.mem_filter.mp ((mem_restrictSupport_iff GenericField).mp hQ hm)
    exact ExpandedColumns6970.jetExponents_finite.mem_toFinset.mp hw.1
  change Module.finrank GenericField
    ((restrictSupport GenericField (↑(jetColumns.filter (fitsBox b j t)))).comap ambient.subtype) = _
  rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq, finrank_restrictSupport_finset]
  rfl





end Low6969GateBox

end Merged_Low6969GateBox

-- merged module Low6969GateAmb
section Merged_Low6969GateAmb

set_option autoImplicit false

namespace Low6969GateAmb
open K1_13_2 (cappedCount)
open K1_13_2_2 (JetExp oldWeight gradeWeight cumulativeExponents mem_cumulativeColumns)
open ExpandedColumns6970 (jetColumns jetExponents)
open ExpandedColumns6970 (gradeCap)
open scoped BigOperators
open Finset
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open K1_13_2_2_3 (cappedColumns mem_cappedColumns capped_card)
open ExpandedColumns6970 (sumGrade sumOld)

def bound (b : ℕ) : ℕ := min 4025 (b + 1)
def start (k : ℕ) : ℕ := k
def stop (b k : ℕ) : ℕ := min (bound b) (start (k + 1))
def chunks (b : ℕ) : ℕ := bound b
def padGrade (b k : ℕ) : ℕ := min (gradeCap (start k)) (gradeCap (stop b k - 1))
def index (j : ℕ) : ℕ := min 1679 j

private theorem grade_le {b k q : ℕ} (hlo : start k ≤ q) (hhi : q < stop b k) :
    padGrade b k ≤ gradeCap q := by
  unfold padGrade gradeCap
  have hcap := ExpandedShape6970.cap_antitone (show q ≤ stop b k-1 by omega)
  exact le_min ((min_le_left _ _).trans ((min_le_left _ _).trans hlo))
    ((min_le_right _ _).trans ((min_le_right _ _).trans hcap))

noncomputable def grid (b j t : ℕ) : Finset (Σ _ : ℕ, ℕ × JetExp) :=
  (range (chunks b)).sigma fun k => (Ico (start k) (stop b k)).product
    (cappedColumns (padGrade b k) (index j) (min 500 t))

noncomputable def pad (b : ℕ) (x : Σ _ : ℕ, ℕ × JetExp) : JetExp :=
  x.2.2 + Finsupp.single 0 (x.2.1 - padGrade b x.1)

private theorem pad_spec {b j t : ℕ} {x : Σ _ : ℕ, ℕ × JetExp} (hx : x ∈ grid b j t) :
    (pad b x).weight gradeWeight = x.2.1 ∧
    (pad b x).weight oldWeight = x.2.2.weight oldWeight ∧
    (∀ i : Fin 4, i ≠ 0 → pad b x i = x.2.2 i) := by
  obtain ⟨k,q,m⟩ := x
  have hm := (mem_cappedColumns.mp (mem_product.mp (mem_sigma.mp hx).2).2).1
  have hm' := (mem_cumulativeColumns.mp hm).1
  have hg : m.weight gradeWeight = padGrade b k := by exact_mod_cast hm'
  obtain ⟨hl,hh⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hx).2).1
  change start k ≤ q at hl
  change q < stop b k at hh
  have hq := (grade_le hl hh).trans (min_le_left _ _ : gradeCap q ≤ q)
  have h0 : pad b ⟨k,q,m⟩ 0 = m 0 + (q-padGrade b k) := by simp [pad]
  have hsucc (i : Fin 4) (hi : i ≠ 0) : pad b ⟨k,q,m⟩ i = m i := by
    simp [pad,Finsupp.single_eq_of_ne hi]
  refine ⟨?_, ?_, hsucc⟩
  · change (pad b ⟨k,q,m⟩).weight gradeWeight = q
    rw [sumGrade, h0, hsucc 1 (by decide), hsucc 2 (by decide), hsucc 3 (by decide)]
    rw [sumGrade] at hg
    omega
  · rw [sumOld,sumOld,hsucc 1 (by decide),hsucc 2 (by decide),hsucc 3 (by decide)]

private theorem map_mem {b j t : ℕ} {x : Σ _ : ℕ, ℕ × JetExp} (hx : x ∈ grid b j t) :
    pad b x ∈ jetColumns.filter (Low6969GateBox.fitsBox b j t) := by
  obtain ⟨k,q,m⟩ := x
  obtain ⟨hl,hh⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hx).2).1
  obtain ⟨hj,ht⟩ := mem_cappedColumns.mp (mem_product.mp (mem_sigma.mp hx).2).2
  obtain ⟨hg,hi⟩ := mem_cumulativeColumns.mp hj
  obtain ⟨eB,eJ,eOther⟩ := pad_spec hx
  dsimp only at eB eJ eOther hl hh
  have hgrade : m.weight gradeWeight = padGrade b k := by exact_mod_cast hg
  have hindex : m.weight oldWeight ≤ index j := by exact_mod_cast hi
  have htop : m 3 ≤ min 500 t := by exact_mod_cast ht
  have hD := (grade_le hl hh).trans (min_le_right _ _ : gradeCap q ≤ ExpandedTaper6970.cap q)
  have hb : q ≤ 4024 ∧ q ≤ b := by
    unfold stop bound at hh
    omega
  apply Finset.mem_filter.mpr
  refine ⟨?_,⟨eB.trans_le hb.2,eJ.trans_le (hindex.trans (min_le_right _ _)),?_⟩⟩
  · apply ExpandedColumns6970.jetExponents_finite.mem_toFinset.mpr
    change (pad b ⟨k,q,m⟩).weight gradeWeight ≤ 4024 ∧
      (pad b ⟨k,q,m⟩).weight oldWeight ≤ 1679 ∧ _
    refine ⟨eB.trans_le hb.1,eJ.trans_le (hindex.trans (min_le_left _ _)),?_,?_⟩
    · rw [eOther 3 (by decide)]
      exact htop.trans (min_le_left _ _)
    rw [eB,eOther 1 (by decide),eOther 2 (by decide),eOther 3 (by decide)]
    rw [sumGrade] at hgrade
    omega
  · rw [eOther 3 (by decide)]
    exact htop.trans (min_le_right _ _)

private theorem pad_injective (b j t : ℕ) : Set.InjOn (pad b) (grid b j t : Set (Σ _ : ℕ, ℕ × JetExp)) := by
  intro x hx y hy hxy
  obtain ⟨k,q,m⟩ := x
  obtain ⟨k',q',m'⟩ := y
  obtain ⟨hlo,hhi⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hx).2).1
  obtain ⟨hlo',hhi'⟩ := mem_Ico.mp (mem_product.mp (mem_sigma.mp hy).2).1
  have eQ : q = q' := (pad_spec hx).1.symm.trans ((congrArg (fun e : JetExp => e.weight gradeWeight) hxy).trans (pad_spec hy).1)
  subst q'
  have eK : k = k' := by
    change q < stop b k at hhi
    change q < stop b k' at hhi'
    change start k ≤ q at hlo
    change start k' ≤ q at hlo'
    simp only [stop, start] at hhi hhi' hlo hlo'
    omega
  subst k'
  have em : m = m' := by
    apply add_right_cancel (b := Finsupp.single (0 : Fin 4) (q-padGrade b k))
    exact hxy
  subst m'
  rfl

def block (b j t k : ℕ) : ℤ :=
  ((stop b k-start k : ℕ) : ℤ) * cappedCount (padGrade b k) (index j) (min 500 t)

def compute (b j t : ℕ) : ℤ := ∑ k ∈ range (chunks b), block b j t k

private theorem grid_eq (b j t : ℕ) : ((grid b j t).card : ℤ) = compute b j t := by
  unfold grid compute
  rw [card_sigma,Nat.cast_sum]
  apply sum_congr rfl
  intro k _
  change (((Ico (start k) (stop b k)).product
    (cappedColumns (padGrade b k) (index j) (min 500 t))).card : ℤ) = block b j t k
  have hcard := Finset.card_product (Ico (start k) (stop b k))
    (cappedColumns (padGrade b k) (index j) (min 500 t))
  change ((Ico (start k) (stop b k)).product
    (cappedColumns (padGrade b k) (index j) (min 500 t))).card = _ at hcard
  rw [hcard, Nat.card_Ico, Nat.cast_mul, capped_card K1_13_2_2_2.proof]
  rfl

theorem amb_ge (b j t : ℕ) : compute b j t ≤ (Low6969GateBox.ambCount b j t : ℤ) := by
  rw [← grid_eq]
  unfold Low6969GateBox.ambCount
  exact_mod_cast Finset.card_le_card_of_injOn (pad b) (fun _ h => map_mem h) (pad_injective b j t)

theorem amb_full (b j t : ℕ) (hb : 4024 ≤ b) (hj : 1679 ≤ j) (htt : 500 ≤ t) :
    Low6969GateBox.ambCount b j t = Low6969Prices.symbolCount := by
  unfold Low6969GateBox.ambCount
  have jc : jetColumns.card = Low6969Prices.symbolCount := by
    exact ExpandedShape6970.jet_count
  rw [filter_true_of_mem, jc]
  intro m hm
  have h : m ∈ jetExponents := ExpandedColumns6970.jetExponents_finite.mem_toFinset.mp hm
  unfold Low6969GateBox.fitsBox
  have ht : 3 * m 3 ≤ m.weight oldWeight := by rw [sumOld]; omega
  exact ⟨h.1.trans hb, h.2.1.trans hj, h.2.2.1.trans htt⟩

theorem amb_le (b j t : ℕ) : Low6969GateBox.ambCount b j t ≤ Low6969Prices.symbolCount := by
  unfold Low6969GateBox.ambCount
  have jc : jetColumns.card = Low6969Prices.symbolCount := by
    exact ExpandedShape6970.jet_count
  rw [← jc]
  exact Finset.card_filter_le _ _

end Low6969GateAmb

end Merged_Low6969GateAmb
end Z6969Source2420

-- Source: ProximityPrize.SubmissionLower.Low6969GateHb
section Z6969Source2421
set_option autoImplicit true
set_option Elab.async false

set_option autoImplicit false

namespace Low6969GateHb

open Low6969GateShape Low6969GateBox MvPolynomial
open K1_13_2_2 (JetExp oldWeight gradeWeight)
open Low6969SharedShapeRank (ambient)

theorem weight_top (m : JetExp) : m.weight (Pi.single (3 : Fin 4) 1) = m 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Pi.single_apply]

theorem fitsBox_iff (b j t : ℕ) (m : JetExp) :
    fitsBox b j t m ↔ m.weight (wv 0) ≤ b ∧ m.weight (wv 1) ≤ j ∧ m.weight (wv 2) ≤ t := by
  unfold fitsBox
  have h0 : wv 0 = gradeWeight := rfl
  have h1 : wv 1 = oldWeight := rfl
  have h2 : m.weight (wv 2) = m 3 := weight_top m
  rw [h0, h1, h2]

theorem shp_le_of_mem_boxSpace (b j t : ℕ) (v : ↥ambient) (hv : v ∈ boxSpace b j t) (k : Fin 3) :
    shp k (v : Low6969SharedRational.FractionJet) ≤ ![b, j, t] k := by
  have hs := (mem_restrictSupport_iff _).mp hv
  unfold shp weightedTotalDegree
  apply Finset.sup_le
  intro m hm
  have hf := (Finset.mem_filter.mp (hs hm)).2
  have := (fitsBox_iff b j t m).mp hf
  fin_cases k
  · exact this.1
  · exact this.2.1
  · exact this.2.2

end Low6969GateHb
end Z6969Source2421
