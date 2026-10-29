import ProximityPrize.SubmissionBinaryLower.P64C6Boxes

/-!
# Support and line-shift bounds for the flat interpolation boxes
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Weights

open Polynomial P64Found P64C6Flow P64C6Coordinates P64C6Boxes

variable {F : Type*} [Field F]

local notation "Tri" => Polynomial (Polynomial (Polynomial F))

lemma weight_of_supp {T : Finset (ℕ × ℕ × ℕ)} {R : Tri} {α β γ k : ℕ}
    (hR : R ∈ supp T) (hT : ∀ p ∈ T, α * p.1 + β * p.2.1 + γ * p.2.2 ≤ k) :
    WtLE α β γ k R := by
  intro a b l hn
  apply hT (a, b, l)
  by_contra ht
  exact hn (hR a b l ht)

lemma weight_add {R H : Tri} {α β γ k : ℕ}
    (hR : WtLE α β γ k R) (hH : WtLE α β γ k H) : WtLE α β γ k (R + H) := by
  intro a b l hn
  by_cases hr : c3 R a b l = 0
  · apply hH a b l
    simpa [c3_add, hr] using hn
  · exact hR a b l hr

lemma parameter_weight_iff (R : Tri) (q e : ℕ) :
    WtLE 0 q 1 e R ↔ (((degGrading F).poly 0).poly q).mem e R := by
  constructor
  · intro h b a
    by_cases hz : (R.coeff b).coeff a = 0
    · exact Or.inl hz
    right
    have hl : c3 R a b ((R.coeff b).coeff a).natDegree ≠ 0 := by
      simpa [c3] using Polynomial.leadingCoeff_ne_zero.mpr hz
    have hb := h a b _ hl
    have hbi : (q : ℤ) * b + ((R.coeff b).coeff a).natDegree ≤ e := by
      exact_mod_cast (by simpa using hb : q * b + ((R.coeff b).coeff a).natDegree ≤ e)
    change (((R.coeff b).coeff a).natDegree : ℤ) ≤ (e : ℤ) - b * q - a * 0
    nlinarith
  · intro h a b l hn
    have hz : (R.coeff b).coeff a ≠ 0 := by
      intro hz
      simp [c3, hz] at hn
    have hb := (h b a).resolve_left hz
    have hl : l ≤ ((R.coeff b).coeff a).natDegree := Polynomial.le_natDegree_of_ne_zero hn
    have hli : (l : ℤ) ≤ ((R.coeff b).coeff a).natDegree := by exact_mod_cast hl
    have he : (q : ℤ) * b + l ≤ e := by
      change (((R.coeff b).coeff a).natDegree : ℤ) ≤ (e : ℤ) - b * q - a * 0 at hb
      nlinarith
    simpa using (show q * b + l ≤ e by exact_mod_cast he)

/-- A line with parameter degree at most `q` preserves the weighted parameter cap. -/
lemma lineShift_weight (R : Tri) (x : F) (y : F[X]) (q e : ℕ)
    (hR : WtLE 0 q 1 e R) (hy : y.natDegree ≤ q) :
    WtLE 0 q 1 e (P64LineOrder.lineShift R x y) := by
  apply (parameter_weight_iff _ q e).mpr
  change (((degGrading F).poly 0).poly q).mem e (shiftHom (Polynomial.C x) y R)
  apply shift_mem ((parameter_weight_iff R q e).mp hR)
  · exact Or.inr (by simp)
  · exact Or.inr (by exact_mod_cast hy)

lemma spatial_weight (R : Tri) (D W : ℕ) (hR : WtLE 1 D 0 W R) :
    P64Caps.Weighted.weightedSupportDegree R D ≤ W := by
  classical
  unfold P64Caps.Weighted.weightedSupportDegree
  apply Finset.sup_le
  intro b hb
  have hb0 : R.coeff b ≠ 0 := Polynomial.mem_support_iff.mp hb
  have ha0 : (R.coeff b).coeff (R.coeff b).natDegree ≠ 0 := by
    simpa using Polynomial.leadingCoeff_ne_zero.mpr hb0
  obtain ⟨l, hl⟩ := Polynomial.nonempty_support_iff.mpr ha0
  have h := hR (R.coeff b).natDegree b l (Polynomial.mem_support_iff.mp hl)
  simpa using h

lemma outer_degree_of_supp {T : Finset (ℕ × ℕ × ℕ)} {R : Tri} {h : ℕ}
    (hne : R ≠ 0) (hR : R ∈ supp T) (hT : ∀ p ∈ T, p.2.1 < h) : R.natDegree < h := by
  have hb0 : R.coeff R.natDegree ≠ 0 := by simpa using Polynomial.leadingCoeff_ne_zero.mpr hne
  obtain ⟨a, ha⟩ := Polynomial.nonempty_support_iff.mpr hb0
  obtain ⟨l, hl⟩ := Polynomial.nonempty_support_iff.mpr (Polynomial.mem_support_iff.mp ha)
  apply hT (a, R.natDegree, l)
  by_contra ht
  exact (Polynomial.mem_support_iff.mp hl) (hR a R.natDegree l ht)

lemma auxiliary_caps {R : Tri} (D W q e h : ℕ) (hne : R ≠ 0)
    (hR : R ∈ supp (auxiliary D W q e h)) :
    P64Caps.Weighted.weightedSupportDegree R D ≤ W ∧ R.natDegree < h ∧ WtLE 0 q 1 e R := by
  refine ⟨spatial_weight R D W (weight_of_supp hR ?_), outer_degree_of_supp hne hR ?_,
    weight_of_supp hR ?_⟩
  · rintro ⟨a, b, l⟩ hp
    simpa using ((mem_auxiliary D W q e h a b l).mp hp).2.1
  · rintro ⟨a, b, l⟩ hp
    exact ((mem_auxiliary D W q e h a b l).mp hp).1
  · rintro ⟨a, b, l⟩ hp
    simpa using ((mem_auxiliary D W q e h a b l).mp hp).2.2

/-- All coefficients of normal order below `s` are among the selected constraints. -/
lemma order_of_constraints (R : Tri) (s q e : ℕ) (hR : WtLE 0 q 1 e R)
    (hc : extr3 (conditions s q e) R = 0) :
    ∀ a b, a + b < s → (R.coeff b).coeff a = 0 := by
  intro a b hab
  ext l
  change c3 R a b l = 0
  by_contra hn
  have hwt := hR a b l hn
  have hp : (a, b, l) ∈ conditions s q e :=
    (mem_conditions s q e a b l).mpr ⟨hab, by simpa using hwt⟩
  exact hn (congrFun hc ⟨(a, b, l), hp⟩)

section Inverse

variable {B : Type*} [CommRing B]

lemma shiftHom_inverse (u v : B) (R : Polynomial (Polynomial B)) :
    shiftHom u v (shiftHom (-u) (-v) R) = R := by
  have hh : (shiftHom u v).comp (shiftHom (-u) (-v)) = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro p
      simp [shiftHom, Polynomial.taylor_taylor]
    · simp [shiftHom, Polynomial.taylor_apply]
  exact RingHom.congr_fun hh R

end Inverse

end P64C6Weights
end ProximityPrize.SubmissionBinaryLower
