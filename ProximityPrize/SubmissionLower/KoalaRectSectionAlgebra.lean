import ProximityPrize.SubmissionLower.KoalaRectSections
import ProximityPrize.SubmissionLower.KoalaRectTaylorAxes

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace SplitCut.Rect
noncomputable section

open MvPolynomial
open scoped Pointwise BigOperators

variable {F : Type*} [Field F]

theorem space_mono_weight {d k : Box}
    (hv : d.velocity ≤ k.velocity) (hy : d.base+2*d.velocity ≤ k.base+2*k.velocity)
    (h₀ : d.seed₀ ≤ k.seed₀) (h₁ : d.seed₁ ≤ k.seed₁) :
    space F d ≤ space F k := by
  intro p hp m hm
  obtain ⟨a,b,c,d'⟩ := hp hm
  exact ⟨a.trans hv,b.trans hy,c.trans h₀,d'.trans h₁⟩

theorem space_pad_mono {d : Box} {a b : ℕ} (h : a ≤ b) :
    space F (d.pad a) ≤ space F (d.pad b) :=
  space_mono_weight le_rfl (by dsimp [Box.pad]; omega) le_rfl le_rfl

theorem space_mul {p q : Ring F} {d k : Box}
    (hp : p ∈ space F d) (hq : q ∈ space F k) : p*q ∈ space F (d.add k) := by
  classical
  intro m hm
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp (support_mul _ _ hm)
  obtain ⟨a₀,a₁,a₂,a₃⟩ := hp ha
  obtain ⟨b₀,b₁,b₂,b₃⟩ := hq hb
  change (a+b) 1 ≤ _ ∧ (a+b) 0 + 2*(a+b) 1 ≤ _ ∧ (a+b) 2 ≤ _ ∧ (a+b) 3 ≤ _
  simp only [Finsupp.add_apply, Box.add]
  omega

theorem space_C (c : F) (d : Box) : MvPolynomial.C c ∈ space F d := by
  classical
  intro m hm
  have h : m = 0 := Finset.mem_singleton.mp (support_monomial_subset hm)
  subst m
  exact ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩

theorem space_Y_pow (n : ℕ) : (MvPolynomial.X (0 : Fin 4) ^ n : Ring F) ∈
    space F ⟨n,0,0,0⟩ := by
  classical
  rw [MvPolynomial.X_pow_eq_monomial]
  intro m hm
  have h : m = Finsupp.single (0 : Fin 4) n := Finset.mem_singleton.mp (support_monomial_subset hm)
  subst m
  change _ ≤ 0 ∧ _ + 2*_ ≤ n+2*0 ∧ _ ≤ 0 ∧ _ ≤ 0
  simp

theorem space_shift_ordinate {d : Box} {o : ℕ} {p : Ring F}
    (hp : p ∈ space F (d.pad o)) (n : ℕ) :
    MvPolynomial.X (0 : Fin 4)^n*p ∈ space F (d.pad (o+n)) := by
  have h := space_mul (space_Y_pow (F := F) n) hp
  simpa [Box.add, Box.pad, Nat.add_comm, Nat.add_left_comm] using h

namespace Section

variable {I J : Ideal (Ring F)} {d k : Box}

def restrict (S : Section I d) (h : I ≤ J) : Section J d :=
  { S with glue := h S.glue }

def widen (S : Section I d)
    (hv : d.velocity ≤ k.velocity) (hy : d.base+2*d.velocity ≤ k.base+2*k.velocity)
    (h₀ : d.seed₀ ≤ k.seed₀) (h₁ : d.seed₁ ≤ k.seed₁) : Section I k :=
  { S with
    finite_bound := space_mono_weight (d := d.pad S.order) (k := k.pad S.order)
      hv (by dsimp [Box.pad]; omega) h₀ h₁ S.finite_bound
    inverse_bound := space_mono_weight (d := d.pad S.order) (k := k.pad S.order)
      hv (by dsimp [Box.pad]; omega) h₀ h₁ S.inverse_bound }

def raiseOrder (S : Section I d) (n : ℕ) (h : S.order ≤ n) : Section I d where
  order := n
  finite := S.finite
  inverse := MvPolynomial.X (0 : Fin 4)^(n-S.order)*S.inverse
  finite_bound := space_pad_mono h S.finite_bound
  inverse_bound := by
    simpa only [Nat.add_sub_of_le h] using space_shift_ordinate S.inverse_bound (n-S.order)
  glue := by
    have hm := I.mul_mem_left (MvPolynomial.X (0 : Fin 4)^(n-S.order)) S.glue
    rw [mul_sub, ← mul_assoc, ← pow_add, Nat.sub_add_cancel h] at hm
    exact hm

def mul (S : Section I d) (T : Section I k) : Section I (d.add k) where
  order := S.order+T.order
  finite := S.finite*T.finite
  inverse := S.inverse*T.inverse
  finite_bound := by
    have h := space_mul S.finite_bound T.finite_bound
    simpa [Box.add, Box.pad, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  inverse_bound := by
    have h := space_mul S.inverse_bound T.inverse_bound
    simpa [Box.add, Box.pad, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  glue := by
    let φ := Ideal.Quotient.mk I
    have hs := Ideal.Quotient.eq_zero_iff_mem.mpr S.glue
    have ht := Ideal.Quotient.eq_zero_iff_mem.mpr T.glue
    simp only [map_sub, map_mul, map_pow, sub_eq_zero] at hs ht
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp only [map_sub, map_mul, map_pow, pow_add, sub_eq_zero]
    rw [mul_mul_mul_comm, hs, ht]

def add (S T : Section I d) : Section I d := by
  let n := max S.order T.order
  let A := S.raiseOrder n (le_max_left _ _)
  let B := T.raiseOrder n (le_max_right _ _)
  refine ⟨n, S.finite+T.finite, A.inverse+B.inverse, ?_, ?_, ?_⟩
  · exact (space F _).add_mem A.finite_bound B.finite_bound
  · exact (space F _).add_mem A.inverse_bound B.inverse_bound
  · have h := I.add_mem A.glue B.glue
    change (MvPolynomial.X (0 : Fin 4)^n*S.finite-A.inverse) + (MvPolynomial.X (0 : Fin 4)^n*T.finite-B.inverse) ∈ I at h
    convert h using 1
    ring

def smul (S : Section I d) (c : F) : Section I d where
  order := S.order
  finite := c • S.finite
  inverse := c • S.inverse
  finite_bound := (space F _).smul_mem c S.finite_bound
  inverse_bound := (space F _).smul_mem c S.inverse_bound
  glue := by
    have h := I.mul_mem_left (MvPolynomial.C c) S.glue
    convert h using 1
    simp only [MvPolynomial.smul_eq_C_mul]
    ring

/-- A polynomial already contained in its box has the same two chart representatives. -/
def of_mem {p : Ring F} (hp : p ∈ space F d) : Section I d where
  order := 0
  finite := p
  inverse := p
  finite_bound := by simpa [Box.pad] using hp
  inverse_bound := by simpa [Box.pad] using hp
  glue := by simp

end Section
end
end SplitCut.Rect

#print axioms SplitCut.Rect.Section.mul
#print axioms SplitCut.Rect.Section.add
