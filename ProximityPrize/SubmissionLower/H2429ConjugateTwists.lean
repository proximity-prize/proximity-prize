import ProximityPrize.SubmissionLower.H2429ConstantSlopes
import ProximityPrize.SubmissionLower.H2429ConjugateResidues

set_option autoImplicit false
set_option maxRecDepth 12000
set_option Elab.async false
set_option maxHeartbeats 300000

namespace H2429ConjugateTwists

open Polynomial P1
open scoped Polynomial

/-- Native Frobenius to the indicated power. -/
@[irreducible] def σ (r : ℕ) : K →+* K := iterateFrobenius K p r

theorem sigma_one : σ 1 = twist := by
  rw [σ, iterateFrobenius_one] <;> rfl

theorem sigma_six : σ 6 = RingHom.id K := by
  apply RingHom.ext
  intro x
  rw [σ, iterateFrobenius_def]
  change x ^ p ^ 6 = x
  have hcard : Fintype.card K = p ^ 6 := Sol1.C64.native_field_card
  rw [← hcard]
  exact FiniteField.pow_card x

theorem sigma_apply_add (r s : ℕ) (x : K) :
    σ (r + s) x = σ r (σ s x) := by
  simp only [σ, iterateFrobenius_add, RingHom.comp_apply]

theorem map_shift (P : K[X]) (r s : ℕ) :
    (P.map (σ r)).map (σ s) = P.map (σ (s + r)) := by
  simp only [σ, Polynomial.map_map, iterateFrobenius_add]

theorem map_fixed {P : K[X]} (h : P.map twist = P) (r : ℕ) : P.map (σ r) = P := by
  induction r with
  | zero => simp [σ]
  | succ r ih =>
    rw [← map_shift P 1 r, sigma_one, h, ih]

theorem node_fixed (r : ℕ) (i : I) : σ r (node i) = node i := by
  induction r with
  | zero => simp [σ]
  | succ r ih =>
    have one : twist (node i) = node i := FrobeniusLocator.Native.native_domain_fixed i
    rw [sigma_apply_add, sigma_one, one, ih]

theorem off_nodes {E : K[X]} (h : ∀ i : I, E.eval (node i) ≠ 0) (r : ℕ) (i : I) :
    (E.map (σ r)).eval (node i) ≠ 0 := by
  have eq : (E.map (σ r)).eval (node i) = σ r (E.eval (node i)) :=
    FrobeniusLocator.Strata.eval_coefficient_map (σ r) E (node i) (node_fixed r i)
  rw [eq]
  exact (map_ne_zero (σ r)).mpr (h i)

theorem family_fixed {cap A : ℕ} {u : Words} {del : Finset I} {Γ : Finset K}
    {M : ModelAt cap u del} (F : FamilyAt A M Γ) (r : ℕ) :
    ∀ γ ∈ Γ, (F.scalar γ).map (σ r) = F.scalar γ :=
  fun γ hγ => map_fixed (F.mark γ hγ).scalar_fixed r

private theorem shift_pair {E : K[X]} {r : ℕ} (s : ℕ)
    (hc : IsCoprime E (E.map (σ r))) :
    IsCoprime (E.map (σ s)) (E.map (σ (s + r))) := by
  rw [← map_shift E r s]
  exact hc.map (mapRingHom (σ s))

/-- Absence of overlap with the third conjugate makes the second union adjacent-coprime. -/
theorem adjacent_two {E : K[X]} (adjacent : IsCoprime E (E.map twist))
    (away : IsCoprime E (E.map (σ 3))) :
    IsCoprime (E * E.map (σ 2)) ((E * E.map (σ 2)).map twist) := by
  have h01 : IsCoprime E (E.map (σ 1)) :=
    (congrArg (fun f : K →+* K => IsCoprime E (E.map f)) sigma_one).mpr adjacent
  have h12 : IsCoprime (E.map (σ 1)) (E.map (σ 2)) := shift_pair (r := 1) 1 h01
  have h23 : IsCoprime (E.map (σ 2)) (E.map (σ 3)) := shift_pair (r := 1) 2 h01
  rw [Polynomial.map_mul, ← sigma_one, map_shift E 2 1]
  exact (h01.mul_left h12.symm).mul_right (away.mul_left h23)

/-- Absence of overlap with the second conjugate makes the third union adjacent-coprime. -/
theorem adjacent_three {E : K[X]} (adjacent : IsCoprime E (E.map twist))
    (away : IsCoprime E (E.map (σ 2))) :
    IsCoprime (E * E.map (σ 3)) ((E * E.map (σ 3)).map twist) := by
  have h01 : IsCoprime E (E.map (σ 1)) :=
    (congrArg (fun f : K →+* K => IsCoprime E (E.map f)) sigma_one).mpr adjacent
  have h13 : IsCoprime (E.map (σ 1)) (E.map (σ 3)) := shift_pair (r := 2) 1 away
  have h34 : IsCoprime (E.map (σ 3)) (E.map (σ 4)) := shift_pair (r := 1) 3 h01
  have h46 : IsCoprime (E.map (σ 4)) (E.map (σ 6)) := shift_pair (r := 2) 4 away
  have h04 : IsCoprime E (E.map (σ 4)) := by
    rw [sigma_six, Polynomial.map_id] at h46
    exact h46.symm
  rw [Polynomial.map_mul, ← sigma_one, map_shift E 3 1]
  exact (h01.mul_left h13.symm).mul_right (h04.mul_left h34)

private theorem ratio_fixed {x y : K} (hy : y ≠ 0)
    (h₂ : σ 2 x * y = x * σ 2 y) (h₃ : σ 3 x * y = x * σ 3 y) :
    σ 1 (x / y) = x / y := by
  have h (r : ℕ) (hr : σ r x * y = x * σ r y) : σ r (x / y) = x / y := by
    rw [map_div₀ (σ r)]
    exact (div_eq_div_iff ((map_ne_zero (σ r)).mpr hy) hy).mpr hr
  apply (σ 2).injective
  rw [← sigma_apply_add 2 1, h 3 h₃, h 2 h₂]

/-- Overlap with both conjugates forces every marked slope ratio into the prime field. -/
theorem both_overlap_card {cap : ℕ} {u : Words} {del : Finset I} {Γ : Finset K}
    (M : ModelAt cap u del) (F : FamilyAt 179876 M Γ) (factor : M.factor = 1)
    (constant : amplitudeDegree M.A₀ M.A₁ = 0) {G₂ G₃ : K[X]}
    (pos₂ : 0 < G₂.natDegree) (left₂ : G₂ ∣ M.E) (right₂ : G₂ ∣ M.E.map (σ 2))
    (pos₃ : 0 < G₃.natDegree) (left₃ : G₃ ∣ M.E) (right₃ : G₃ ∣ M.E.map (σ 3)) :
    Γ.card ≤ p := by
  classical
  by_cases many : 1 < Γ.card
  · have positive : 0 < M.E.natDegree :=
      pos₂.trans_le (natDegree_le_of_dvd left₂ M.E_monic.ne_zero)
    obtain ⟨D⟩ := H2429ConstantSlopes.exists_coordinate M F constant positive
    obtain ⟨γ₀, hγ₀, nonzero⟩ := D.has_nonzero many
    have residues (γ : K) (hγ : γ ∈ Γ) : M.E ∣ F.scalar γ - C (D.slope γ) * M.Q :=
      D.residue F factor hγ
    have prop₂ := H2429ConjugateResidues.proportional pos₂ left₂ right₂
      M.offset_reduced residues (family_fixed F 2) hγ₀
    have prop₃ := H2429ConjugateResidues.proportional pos₃ left₃ right₃
      M.offset_reduced residues (family_fixed F 3) hγ₀
    let f (γ : K) := D.slope γ / D.slope γ₀
    have hf : Set.InjOn f (Γ : Set K) := by
      intro a ha b hb hab
      apply D.slope_injective ha hb
      have h := congrArg (fun x : K => x * D.slope γ₀) hab
      simpa only [f, div_mul_cancel₀ _ nonzero] using h
    let X₀ : K[X] := Polynomial.X
    let R : K[X] := X₀ ^ p - X₀
    have hne : R ≠ 0 := by
      intro hz
      have heq : X₀ ^ p = X₀ := sub_eq_zero.mp hz
      have hd := congrArg Polynomial.natDegree heq
      rw [natDegree_X_pow, natDegree_X] at hd
      exact (by decide : p ≠ 1) hd
    have hdeg : R.natDegree ≤ p := by
      refine (natDegree_sub_le (X₀ ^ p) X₀).trans ?_
      rw [show X₀ = (Polynomial.X : K[X]) from rfl, natDegree_X_pow, natDegree_X]
      exact max_eq_left (by decide : 1 ≤ p) |>.le
    have hcard : (Γ.image f).card ≤ R.natDegree := by
      apply card_le_degree_of_subset_roots
      intro x hx
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp (Finset.mem_def.mpr hx)
      apply (mem_roots hne).mpr
      have h := ratio_fixed nonzero (prop₂ γ hγ) (prop₃ γ hγ)
      have hp : f γ ^ p = f γ := by
        simpa only [σ, iterateFrobenius_def, pow_one] using h
      change R.eval (f γ) = 0
      rw [show R = X₀ ^ p - X₀ from rfl, eval_sub, eval_pow,
        show X₀ = (Polynomial.X : K[X]) from rfl, eval_X]
      exact sub_eq_zero.mpr hp
    rw [Finset.card_image_of_injOn hf] at hcard
    exact hcard.trans hdeg
  · exact (Nat.le_of_not_gt many).trans (by decide)

end H2429ConjugateTwists
