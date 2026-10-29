import ProximityPrize.SubmissionBinaryLower.P64C6Theta

/-!
# Polynomial substitutions preserving coefficient profiles

These lemmas lift the flow's grading to polynomial coefficients. They are used
with the degree grading for a curve shift and with the order grading for a
line shift.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64C6Flow.Grading

variable {B : Type*} [CommRing B]

open Polynomial

/-- Give the polynomial variable weight `w` in a coefficient grading. -/
def poly (G : Grading B) (w : ℤ) : Grading (Polynomial B) where
  mem n p := ∀ a : ℕ, G.mem (n - a * w) (p.coeff a)
  zero_mem _ a := by simpa using G.zero_mem _
  add_mem hp hq a := by simpa using G.add_mem (hp a) (hq a)
  neg_mem hp a := by simpa using G.neg_mem (hp a)
  mul_mem {n m p q} hp hq a := by
    rw [Polynomial.coeff_mul]
    refine G.sum_mem _ _ fun ij hij => ?_
    have heq := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    refine G.congr_mem ?_ (G.mul_mem (hp ij.1) (hq ij.2))
    rw [← heq]
    push_cast
    ring
  one_mem a := by
    rw [Polynomial.coeff_one]
    split_ifs with ha
    · subst a; simpa using G.one_mem
    · exact G.zero_mem _

lemma poly_C {G : Grading B} {w n : ℤ} {c : B} (hc : G.mem n c) :
    (G.poly w).mem n (Polynomial.C c) := by
  intro a
  rw [Polynomial.coeff_C]
  split_ifs with ha
  · subst a; simpa using hc
  · exact G.zero_mem _

lemma poly_X (G : Grading B) (w : ℤ) : (G.poly w).mem w Polynomial.X := by
  intro a
  rw [Polynomial.coeff_X]
  split_ifs with ha
  · subst a; simpa using G.one_mem
  · exact G.zero_mem _

/-- Evaluate a polynomial whose coefficient profiles account for the weight of the input. -/
lemma eval₂_mem {A : Type*} [CommRing A] (G : Grading B) (f : A →+* B)
    (p : Polynomial A) {w n : ℤ} {x : B} (hx : G.mem w x)
    (hp : ∀ a : ℕ, G.mem (n - a * w) (f (p.coeff a))) :
    G.mem n (Polynomial.eval₂ f x p) := by
  rw [Polynomial.eval₂_eq_sum_range]
  refine G.sum_mem _ _ fun a _ => ?_
  exact G.congr_mem (by ring) (G.mul_mem (hp a) (G.pow_mem hx a))

lemma comp_mem {G : Grading B} {w n : ℤ} {p q : Polynomial B}
    (hp : (G.poly w).mem n p) (hq : (G.poly w).mem w q) :
    (G.poly w).mem n (p.comp q) := by
  exact eval₂_mem (G.poly w) Polynomial.C p hq (fun a => poly_C (hp a))

lemma taylor_mem {G : Grading B} {w n : ℤ} {p : Polynomial B} {c : B}
    (hp : (G.poly w).mem n p) (hc : G.mem w c) :
    (G.poly w).mem n (Polynomial.taylor c p) :=
  comp_mem hp ((G.poly w).add_mem (poly_X G w) (poly_C hc))

lemma map_mem {A : Type*} [CommRing A] {G : Grading A} {H : Grading B}
    (f : A →+* B) (hf : ∀ n x, G.mem n x → H.mem n (f x)) {w n : ℤ}
    {p : Polynomial A} (hp : (G.poly w).mem n p) :
    (H.poly w).mem n (p.map f) := by
  intro a
  rw [Polynomial.coeff_map]
  exact hf _ _ (hp a)

end P64C6Flow.Grading
end ProximityPrize.SubmissionBinaryLower
