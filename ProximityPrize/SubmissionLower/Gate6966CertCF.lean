import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DdZ1iXjHc
import ProximityPrize.SubmissionLower.Gate6966Hb
import ProximityPrize.SubmissionLower.Gate6966Assembly
import ProximityPrize.SubmissionLower.Low6966RetainedCount
set_option Elab.async false







set_option Elab.async false

-- merged module Gate6966Order
section Merged_Gate6966Order

set_option autoImplicit false

namespace Gate6966Order

open K1_13_6_1_2 (VanishesTo)

theorem vanishesTo_mono {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] {f : R} {m n : ℕ}
    (h : m ≤ n) (hn : VanishesTo P f n) : VanishesTo P f m := by
  unfold VanishesTo at *
  exact Ideal.pow_le_pow_right h hn

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

theorem vanishesTo_cofactor_of_not_mem {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] {g u : R}
    (hg : g ∉ P) {n : ℕ} (h : VanishesTo P (g * u) n) : VanishesTo P u n := by
  unfold VanishesTo at *
  change algebraMap R (Localization.AtPrime P) (g * u) ∈ _ at h
  show algebraMap R (Localization.AtPrime P) u ∈ _
  let L := Localization.AtPrime P
  have hu : IsUnit (algebraMap R L g) := IsLocalization.map_units L (⟨g, hg⟩ : P.primeCompl)
  obtain ⟨v, hv⟩ := hu
  have h' : algebraMap R L u = (↑v⁻¹ : L) * algebraMap R L (g * u) := by
    rw [map_mul, ← hv, ← mul_assoc]; simp
  rw [h']
  exact Ideal.mul_mem_left _ _ h

theorem vanishesTo_cofactor_pow {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] {g u : R}
    (hg : g ∉ P) (k : ℕ) {n : ℕ} (h : VanishesTo P (g ^ k * u) n) : VanishesTo P u n :=
  vanishesTo_cofactor_of_not_mem P (fun hm => hg (‹P.IsPrime›.mem_of_pow_mem k hm)) h

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

end Gate6966Order

end Merged_Gate6966Order

-- merged module Gate6966Count
section Merged_Gate6966Count

set_option autoImplicit false
set_option Elab.async false

namespace Gate6966Count

open P3 (K)
open K1_13 (Row Shape shape InBox chart mixed32)
open K1_13_6 (GeoJets toGeneric cycleLength intersectionIdeal)
open K1_13_6_1_2 (VanishesTo pair_height)
open Low6966GeometryCut (CutInput)
open Low6966GeometryCut_2 (Branch)
open Low6966Prices (taylorLength)
open Low6966SharedTally (Data)
open scoped Polynomial BigOperators
open Low6966SharedChooseCut (mem_of_order)

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
    (htilt : Low6966Prices.tiltedFits (shape f)) (q₁ q₂ : Shape) (hQ₁ : InBox (shape R1) q₁)
    (hQ₂ : InBox (shape R2) q₂) (hq₁ : Low48BentLattice.Chamber (q₁, 0))
    (hq₂ : Low48BentLattice.Chamber (q₂, 0)) (α β : Ideal GeoJets → ℕ)
    (hα : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric R1) (α b.surface))
    (hβ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric R2) (β b.surface)) :
    1920 * (∑ b ∈ F, α b.surface * β b.surface * (b.weight * (D.points b).card)) ≤
      Gate6966.tiltedPair (shape f).chamber q₁ q₂ := by
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
  exact Gate6966.tilted_pair_tally D input F' (fun b hb => hF (Finset.mem_filter.mp hb).1) R1 R2 hR1' hrel
    (fun P => α P * β P) htilt q₁ q₂ hQ₁ hQ₂ hq₁ hq₂ (fun b hb => by
      obtain ⟨hbF, hpos⟩ := Finset.mem_filter.mp hb
      have hαp : 0 < α b.surface := Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
      have hβp : 0 < β b.surface := Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
      exact branch_pair_weight input b hR1 hrel (hα b hbF) (hβ b hbF) hαp hβp)

theorem pair_sum_tilted_rat (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F ⊆ D.branches) (R1 R2 : Row 4) (hR1 : toGeneric R1 ≠ 0)
    (hR1' : R1 ≠ 0) (hrel : IsRelPrime (toGeneric R1) (toGeneric R2))
    (htilt : Low6966Prices.tiltedFits (shape f)) (q₁ q₂ : Shape) (hQ₁ : InBox (shape R1) q₁)
    (hQ₂ : InBox (shape R2) q₂) (hq₁ : Low48BentLattice.Chamber (q₁, 0))
    (hq₂ : Low48BentLattice.Chamber (q₂, 0)) (α β : Ideal GeoJets → ℕ)
    (hα : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric R1) (α b.surface))
    (hβ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric R2) (β b.surface)) :
    ∑ b ∈ F, ((α b.surface : ℚ) * β b.surface) * ((b.weight * (D.points b).card : ℕ) : ℚ) ≤
      (Gate6966.tiltedPair (shape f).chamber q₁ q₂ : ℚ) / 1920 := by
  have h := pair_sum_tilted D input F hF R1 R2 hR1 hR1' hrel htilt q₁ q₂ hQ₁ hQ₂ hq₁ hq₂ α β hα hβ
  have h' : ((1920 * (∑ b ∈ F, α b.surface * β b.surface * (b.weight * (D.points b).card)) : ℕ) : ℚ) ≤
      (Gate6966.tiltedPair (shape f).chamber q₁ q₂ : ℚ) := by exact_mod_cast h
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
  have h := Gate6966.ordinary_pair_tally D input F' (fun b hb => hF (Finset.mem_filter.mp hb).1) R1 R2
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

end Gate6966Count

end Merged_Gate6966Count

-- merged module Gate6966TwoCut
section Merged_Gate6966TwoCut

set_option autoImplicit false
set_option Elab.async false

namespace Gate6966TwoCut

open P3 (K)
open K1_13 (Row Shape shape InBox mixed32)
open K1_13_6 (GeoJets toGeneric)
open K1_13_6_1_2 (VanishesTo)
open Low6966GeometryCut (CutInput)
open Low6966GeometryCut_2 (Branch)
open Low6966SharedTally (Data)
open scoped Polynomial BigOperators

def ClassCert (r a : ℕ) (cc v : ℚ) : Prop :=
  ∀ e m : ℕ, 1 ≤ e →
    ((r - a : ℕ) : ℚ) ^ 2 ≤ (1 - cc) * (((r - e * a - m : ℕ) : ℚ) * ((r - e * a - m : ℕ) : ℚ)) +
      (m : ℚ) * ((r - e * a - m : ℕ) : ℚ) + ((r - a : ℕ) : ℚ) * ((e : ℚ) * m) +
      cc * ((r - a : ℕ) : ℚ) * ((e : ℚ) * ((r - e * a - m : ℕ) : ℚ)) +
      v * ((r - a : ℕ) : ℚ) ^ 2 * ((e : ℚ) * ((e : ℚ) - 1))

theorem classCert_zero (r : ℕ) : ClassCert r 0 0 0 := by
  intro e m he
  have h := Gate6966Combine.class_zero r e m (r - 0 * e - m) he (by omega)
  simp only [Nat.zero_mul, Nat.zero_sub, Nat.sub_zero, Nat.cast_zero, sub_zero, zero_mul, one_mul, mul_zero,
    add_zero] at h ⊢
  nlinarith [h]

variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ} {S : Set (Ideal GeoJets)}

theorem two_cut_count_tilted (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (F : Finset (Branch f Q l)) (hF : F ⊆ D.branches) (H G₁ G₂ sf : Row 4)
    (htilt : Low6966Prices.tiltedFits (shape f))
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
      (1 - cc) * ((Gate6966.tiltedPair (shape f).chamber q₁ q₂ : ℚ) / 1920) +
      (Gate6966.tiltedPair (shape f).chamber qH q₁ : ℚ) / 1920 +
      ((r - a : ℕ) : ℚ) * ((Gate6966.tiltedPair (shape f).chamber qf qH : ℚ) / 1920) +
      cc * ((r - a : ℕ) : ℚ) *
        ((Gate6966.tiltedPair (shape f).chamber qf q₁ : ℚ) / 1920) +
      v * ((r - a : ℕ) : ℚ) ^ 2 *
        ((Gate6966.tiltedPair (shape f).chamber qf qs : ℚ) / 1920) := by
  classical
  have hsep : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric sf) (e b.surface - 1) := by
    intro b hb
    letI := b.base.isPrime
    rw [hsfdef]
    exact Gate6966Order.separant_order b.surface (hef b hb).1
  let g : Ideal GeoJets → ℕ := fun P => r - e P * a - m P
  have hg₁ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric G₁) (g b.surface) := by
    intro b hb
    letI := b.base.isPrime
    exact Gate6966Order.cofactor_order b.surface (hef b hb).2 (hmH b hb).2 (hQ₁ b hb)
  have hg₂ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric G₂) (g b.surface) := by
    intro b hb
    letI := b.base.isPrime
    exact Gate6966Order.cofactor_order b.surface (hef b hb).2 (hmH b hb).2 (hQ₂ b hb)
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
  have hgg := Gate6966Count.pair_sum_tilted_rat D input F hF G₁ G₂ hG0' hG0 hGG htilt q₁ q₂ hb₁ hb₂ hc₁ hc₂ g g hg₁ hg₂
  have hmg := Gate6966Count.pair_sum_tilted_rat D input F hF H G₁ hH0' hH0 hHG htilt qH q₁ hbH hb₁ hcH hc₁ m g
    (fun b hb => (hmH b hb).1) hg₁
  have hem := Gate6966Count.pair_sum_tilted_rat D input F hF f H hf0' hf0 hfH htilt qf qH hbf hbH hcf hcH e m
    (fun b hb => (hef b hb).1) (fun b hb => (hmH b hb).1)
  have heg := Gate6966Count.pair_sum_tilted_rat D input F hF f G₁ hf0' hf0 hfG htilt qf q₁ hbf hb₁ hcf hc₁ e g
    (fun b hb => (hef b hb).1) hg₁
  have hee := Gate6966Count.pair_sum_tilted_rat D input F hF f sf hf0' hf0 hfs htilt qf qs hbf hbs hcf hcs e (fun P => e P - 1)
    (fun b hb => (hef b hb).1) hsep
  have hee' : ∑ b ∈ F, ((e b.surface : ℚ) * ((e b.surface : ℚ) - 1)) *
      ((b.weight * (D.points b).card : ℕ) : ℚ) ≤
      (Gate6966.tiltedPair (shape f).chamber qf qs : ℚ) / 1920 := by
    refine le_trans (le_of_eq ?_) hee
    apply Finset.sum_congr rfl
    intro b hb
    rw [Nat.cast_sub (he1 b hb)]; simp
  have h := Gate6966Assembly.combine_branches F Branch.surface
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
      (1 - cc) * ((mixed32 q₁ q₂ (K1_13.chart (Low6966Prices.taylorLength + 1) (shape f).chamber) (K1_13.chart (Low6966Prices.taylorLength + 2) (shape f).chamber) : ℚ) / 32) +
      (mixed32 qH q₁ (K1_13.chart (Low6966Prices.taylorLength + 1) (shape f).chamber) (K1_13.chart (Low6966Prices.taylorLength + 2) (shape f).chamber) : ℚ) / 32 +
      ((r - a : ℕ) : ℚ) * ((mixed32 qf qH (K1_13.chart (Low6966Prices.taylorLength + 1) (shape f).chamber) (K1_13.chart (Low6966Prices.taylorLength + 2) (shape f).chamber) : ℚ) / 32) +
      cc * ((r - a : ℕ) : ℚ) *
        ((mixed32 qf q₁ (K1_13.chart (Low6966Prices.taylorLength + 1) (shape f).chamber) (K1_13.chart (Low6966Prices.taylorLength + 2) (shape f).chamber) : ℚ) / 32) +
      v * ((r - a : ℕ) : ℚ) ^ 2 *
        ((mixed32 qf qs (K1_13.chart (Low6966Prices.taylorLength + 1) (shape f).chamber) (K1_13.chart (Low6966Prices.taylorLength + 2) (shape f).chamber) : ℚ) / 32) := by
  classical
  have hsep : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric sf) (e b.surface - 1) := by
    intro b hb
    letI := b.base.isPrime
    rw [hsfdef]
    exact Gate6966Order.separant_order b.surface (hef b hb).1
  let g : Ideal GeoJets → ℕ := fun P => r - e P * a - m P
  have hg₁ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric G₁) (g b.surface) := by
    intro b hb
    letI := b.base.isPrime
    exact Gate6966Order.cofactor_order b.surface (hef b hb).2 (hmH b hb).2 (hQ₁ b hb)
  have hg₂ : ∀ b ∈ F, @VanishesTo _ _ b.surface b.base.isPrime (toGeneric G₂) (g b.surface) := by
    intro b hb
    letI := b.base.isPrime
    exact Gate6966Order.cofactor_order b.surface (hef b hb).2 (hmH b hb).2 (hQ₂ b hb)
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
  have hgg := Gate6966Count.pair_sum_ordinary_rat D input F hF G₁ G₂ hG0' hG0 hGG q₁ q₂ hc₁ hc₂ hb₁ hb₂ g g hg₁ hg₂
  have hmg := Gate6966Count.pair_sum_ordinary_rat D input F hF H G₁ hH0' hH0 hHG qH q₁ hcH hc₁ hbH hb₁ m g
    (fun b hb => (hmH b hb).1) hg₁
  have hem := Gate6966Count.pair_sum_ordinary_rat D input F hF f H hf0' hf0 hfH qf qH hcf hcH hbf hbH e m
    (fun b hb => (hef b hb).1) (fun b hb => (hmH b hb).1)
  have heg := Gate6966Count.pair_sum_ordinary_rat D input F hF f G₁ hf0' hf0 hfG qf q₁ hcf hc₁ hbf hb₁ e g
    (fun b hb => (hef b hb).1) hg₁
  have hee := Gate6966Count.pair_sum_ordinary_rat D input F hF f sf hf0' hf0 hfs qf qs hcf hcs hbf hbs e (fun P => e P - 1)
    (fun b hb => (hef b hb).1) hsep
  have hee' : ∑ b ∈ F, ((e b.surface : ℚ) * ((e b.surface : ℚ) - 1)) *
      ((b.weight * (D.points b).card : ℕ) : ℚ) ≤
      (mixed32 qf qs (K1_13.chart (Low6966Prices.taylorLength + 1) (shape f).chamber) (K1_13.chart (Low6966Prices.taylorLength + 2) (shape f).chamber) : ℚ) / 32 := by
    refine le_trans (le_of_eq ?_) hee
    apply Finset.sum_congr rfl
    intro b hb
    rw [Nat.cast_sub (he1 b hb)]; simp
  have h := Gate6966Assembly.combine_branches F Branch.surface
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

end Gate6966TwoCut

end Merged_Gate6966TwoCut

-- merged module Gate6966Class
section Merged_Gate6966Class

set_option autoImplicit false

namespace Gate6966Class

open Gate6966TwoCut

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

end Gate6966Class

end Merged_Gate6966Class

-- merged module Gate6966ClassTable
section Merged_Gate6966ClassTable

set_option autoImplicit false

namespace Gate6966ClassTable

open Gate6966TwoCut Gate6966Class

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
  apply Gate6966Class.classCert_of_checks r a (by omega)
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

theorem tableOK_cons {r w : ℕ} {ws : List ℕ} (h1 : levelOK r w = true) (h2 : tableOK (r + 1) ws = true) :
    tableOK r (w :: ws) = true := by
  simp [tableOK, h1, h2]

theorem tableOK_nil (r : ℕ) : tableOK r [] = true := rfl

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

end Gate6966ClassTable

end Merged_Gate6966ClassTable

-- merged module Gate6966CertCF
section Merged_Gate6966CertCF

set_option autoImplicit false

namespace Gate6966CertCF
open Gate6966TwoCut Gate6966Class

theorem cf_sound (r a : ℕ) (ha : a < r) (v : ℚ) (hv : (a : ℚ) ^ 2 ≤ v * ((r - a : ℕ) : ℚ) ^ 2) :
    ClassCert r a 1 v := by
  have hρ : (0 : ℚ) < ((r - a : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt ha
  set ρ : ℚ := ((r - a : ℕ) : ℚ) with hρd
  have hρr : ρ = (r : ℚ) - a := by rw [hρd, Nat.cast_sub ha.le]
  have hv0 : 0 ≤ v := by
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (a : ℚ), mul_pos hρ hρ, mul_neg_of_neg_of_pos h (mul_pos hρ hρ)]
  apply Gate6966Class.classCert_of_checks r a ha.le 1 v (by norm_num) hv0
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
  else match Gate6966ClassTable.lookup r0 ws r a with
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

theorem certF_class {r0 : ℕ} {ws : List ℕ} (ht : Gate6966ClassTable.tableOK r0 ws = true) {r a : ℕ} (ha : a < r) :
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
      exact Gate6966ClassTable.table_sound ht hl
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

end Gate6966CertCF

end Merged_Gate6966CertCF
