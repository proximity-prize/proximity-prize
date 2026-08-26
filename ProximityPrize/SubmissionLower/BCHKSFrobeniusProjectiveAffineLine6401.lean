import ProximityPrize.SubmissionLower.BCHKSFrobeniusKeyEquationFork6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSFrobeniusProjectiveAffineLine6401
open Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
def frobeniusFixedScalars
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (sigma : F →+* F) : Finset F :=
  Finset.univ.filter fun x => sigma x = x
theorem mem_frobeniusFixedScalars
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (sigma : F →+* F) (x : F) :
    x ∈ frobeniusFixedScalars sigma ↔ sigma x = x := by
  simp [frobeniusFixedScalars]
theorem fractionalLinear_injective_of_cross_ne_zero
    {F : Type*} [Field F]
    (ai aj bi bj z w : F)
    (hcross : ai * bj - aj * bi ≠ 0)
    (hz : aj + z * bj ≠ 0) (hw : aj + w * bj ≠ 0)
    (hratio : (ai + z * bi) / (aj + z * bj) =
      (ai + w * bi) / (aj + w * bj)) :
    z = w := by
  have hmul : (ai + z * bi) * (aj + w * bj) =
      (ai + w * bi) * (aj + z * bj) := by
    exact (div_eq_div_iff hz hw).mp hratio
  have hfactor : (z - w) * (aj * bi - ai * bj) = 0 := by
    linear_combination hmul
  rcases mul_eq_zero.mp hfactor with hzw | hdet
  · exact sub_eq_zero.mp hzw
  · exfalso
    apply hcross
    linear_combination -hdet
theorem fractionalLinear_poles_card_le_one
    {F : Type*} [Field F] [DecidableEq F]
    (S : Finset F) (ai aj bi bj : F)
    (hcross : ai * bj - aj * bi ≠ 0) :
    (S.filter fun z => aj + z * bj = 0).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro z hz w hw
  simp only [Finset.mem_filter] at hz hw
  have hbj : bj ≠ 0 := by
    intro h
    subst bj
    simp only [mul_zero, zero_mul, sub_zero] at hcross
    have haj : aj = 0 := by simpa using hz.2
    simp [haj] at hcross
  have hsub : (z - w) * bj = 0 := by
    linear_combination hz.2 - hw.2
  exact sub_eq_zero.mp (mul_eq_zero.mp hsub |>.resolve_right hbj)
theorem projectiveFrobenius_affineLine_card_le_fixed_add_one
    {F iota : Type*} [Field F] [Fintype F] [DecidableEq F]
    [DecidableEq iota]
    (sigma : F →+* F) (S : Finset F) (a b : iota → F)
    (i j : iota)
    (hcross : a i * b j - a j * b i ≠ 0)
    (heigen : ∀ z ∈ S, ∃ c : F, c ≠ 0 ∧
      ∀ r, sigma (a r + z * b r) = c * (a r + z * b r)) :
    S.card ≤ (frobeniusFixedScalars sigma).card + 1 := by
  classical
  let good := S.filter fun z => a j + z * b j ≠ 0
  let bad := S.filter fun z => a j + z * b j = 0
  let ratio : F → F := fun z => (a i + z * b i) / (a j + z * b j)
  have hfixed : good.image ratio ⊆ frobeniusFixedScalars sigma := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨z, hzgood, rfl⟩ := hx
    have hzS : z ∈ S := (Finset.mem_filter.mp hzgood).1
    have hzden : a j + z * b j ≠ 0 :=
      (Finset.mem_filter.mp hzgood).2
    obtain ⟨c, hc, heig⟩ := heigen z hzS
    rw [mem_frobeniusFixedScalars]
    dsimp [ratio]
    rw [map_div₀, heig i, heig j]
    field_simp
  have hinj : (good.image ratio).card = good.card := by
    apply Finset.card_image_iff.mpr
    intro z hz w hw hratio
    exact fractionalLinear_injective_of_cross_ne_zero
      (a i) (a j) (b i) (b j) z w hcross
      (Finset.mem_filter.mp hz).2 (Finset.mem_filter.mp hw).2 hratio
  have hgood : good.card ≤ (frobeniusFixedScalars sigma).card := by
    rw [← hinj]
    exact Finset.card_le_card hfixed
  have hbad : bad.card ≤ 1 := by
    exact fractionalLinear_poles_card_le_one S
      (a i) (a j) (b i) (b j) hcross
  have hpartition : good.card + bad.card = S.card := by
    simpa [good, bad, not_not] using
      (Finset.card_filter_add_card_filter_not
        (s := S) (fun z => a j + z * b j ≠ 0))
  omega
theorem benchmark_projectiveFrobenius_forces_cross_zero6401
    {F iota : Type*} [Field F] [Fintype F] [DecidableEq F]
    [DecidableEq iota]
    (sigma : F →+* F) (S : Finset F) (a b : iota → F)
    (hfixedCard : (frobeniusFixedScalars sigma).card ≤
      BCHKSTwoFrobeniusModuleAudit6401.q6401)
    (hlarge : BCHKSTwoFrobeniusWeakCurveSeed6401.weakCurveSeedInput6401 ≤
      S.card)
    (heigen : ∀ z ∈ S, ∃ c : F, c ≠ 0 ∧
      ∀ r, sigma (a r + z * b r) = c * (a r + z * b r)) :
    ∀ i j, a i * b j - a j * b i = 0 := by
  intro i j
  by_contra hcross
  have hcap := projectiveFrobenius_affineLine_card_le_fixed_add_one
    sigma S a b i j hcross heigen
  have hnum :
      BCHKSTwoFrobeniusModuleAudit6401.q6401 + 1 <
        BCHKSTwoFrobeniusWeakCurveSeed6401.weakCurveSeedInput6401 := by
    native_decide
  omega
end BCHKSFrobeniusProjectiveAffineLine6401
end ProximityPrize.SubmissionLower
