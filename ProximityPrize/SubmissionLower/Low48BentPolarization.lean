import ProximityPrize.SubmissionLower.Low48BentVolumePrice

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace Low48BentPolarization
open Finset MvPolynomial
open Low48BentLattice
open K1_13 (Shape)
open K1_13_6_2_4_1
  (Grade Form line line_coeff squarefree squarefree_apply squarefree_degree
   cube_extract positiveDiagonal positiveDiagonal_apply)
open scoped BigOperators
noncomputable section

def zeroDiagonal (s : Finset (Fin 5)) (i : Fin 5) : ℚ := if i ∈ s then 1 else 0

theorem zero_cube_prod (a : Grade) :
    (∑ J ∈ (univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      ∏ j ∈ (univ : Finset (Fin 5)) \ J, (0 : ℚ) ^ a j) =
      ∏ j : Fin 5, ((1 : ℚ) - (0 : ℚ) ^ a j) := by
  classical
  rw [Finset.prod_sub (fun _ => (1 : ℚ)) (fun j => (0 : ℚ) ^ a j)]
  refine Finset.sum_bij (fun J _ => univ \ J) ?_ ?_ ?_ ?_
  · intro J _
    simp
  · intro J _ K _ h
    simpa using congrArg (fun U : Finset (Fin 5) => univ \ U) h
  · intro J _
    exact ⟨univ \ J, by simp, by simp⟩
  · intro J _
    simp [Finset.card_sdiff_of_subset (Finset.subset_univ J)]

theorem zero_cube_monomial (a : Grade) (r : ℚ) :
    (∑ J ∈ (univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      eval (zeroDiagonal J) (monomial a r)) =
      r * ∏ j : Fin 5, ((1 : ℚ) - (0 : ℚ) ^ a j) := by
  rw [← zero_cube_prod, Finset.mul_sum]
  refine sum_congr rfl fun J _ => ?_
  rw [eval_monomial, Finsupp.prod_pow]
  have hv (j : Fin 5) : zeroDiagonal J j ^ a j =
      if j ∈ (univ : Finset (Fin 5)) \ J then (0 : ℚ) ^ a j else 1 := by
    by_cases hj : j ∈ J <;> simp [zeroDiagonal, hj]
  simp_rw [hv]
  rw [Finset.prod_ite_mem, Finset.univ_inter]
  ring

theorem zero_cube_monomial_top {a : Grade} (ha : a.degree = 5) (r : ℚ) :
    (∑ J ∈ (univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      eval (zeroDiagonal J) (monomial a r)) =
      (monomial a r).coeff (squarefree univ) := by
  classical
  rw [zero_cube_monomial]
  by_cases h : squarefree (univ : Finset (Fin 5)) ≤ a
  · have he : squarefree (univ : Finset (Fin 5)) = a := by
      obtain ⟨b, hab⟩ := le_iff_exists_add.mp h
      have hd := congrArg Finsupp.degree hab
      rw [ha, map_add, squarefree_degree, card_univ, Fintype.card_fin] at hd
      have hb : b.degree = 0 := by omega
      rw [hab, (Finsupp.degree_eq_zero_iff _).mp hb, add_zero]
    subst a
    simp [squarefree_apply]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    have hm : a j = 0 := by simpa [squarefree_apply] using hj
    rw [Finset.prod_eq_zero (mem_univ j) (by simp [hm]), mul_zero, coeff_monomial]
    exact (ite_eq_right (fun he => h he.ge)).symm

theorem zero_cube (p : Form) :
    (∑ J ∈ (univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      eval (zeroDiagonal J) (homogeneousComponent 5 p)) =
      p.coeff (squarefree univ) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a r =>
    simp only [homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
    by_cases h : 5 = a.degree
    · simpa only [ite_eq_left h] using zero_cube_monomial_top h.symm r
    · have hne : a ≠ squarefree univ := fun h' => h (by rw [h', squarefree_degree]; simp)
      simp [h, coeff_monomial, hne]
  | add p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) hp hq

def bend {R : Type*} [CommRing R] (b j t h : R) : R :=
  -576 * h ^ 5 + 160 * t ^ 2 * h ^ 3 - 480 * t ^ 3 * h ^ 2 + 540 * t ^ 4 * h
  + 960 * j * h ^ 4 - 320 * j * t * h ^ 3 + 960 * j * t ^ 2 * h ^ 2 - 1200 * j * t ^ 3 * h
  - 480 * j ^ 2 * h ^ 3 - 480 * j ^ 2 * t * h ^ 2 + 840 * j ^ 2 * t ^ 2 * h
  + 240 * j ^ 3 * h ^ 2 - 240 * j ^ 3 * t * h - 960 * b * h ^ 4 + 640 * b * t * h ^ 3
  - 1440 * b * t ^ 2 * h ^ 2 + 1440 * b * t ^ 3 * h + 640 * b * j * h ^ 3
  + 960 * b * j * t * h ^ 2 - 1440 * b * j * t ^ 2 * h - 480 * b * j ^ 2 * h ^ 2
  + 480 * b * j ^ 2 * t * h

private def linear (caps : Fin 5 → Cap) (f : Cap → ℕ) : Form :=
  ∑ i : Fin 5, MvPolynomial.C (f (caps i) : ℚ) * MvPolynomial.X i

theorem linear_homogeneous (caps : Fin 5 → Cap) (f : Cap → ℕ) :
    (linear caps f).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

private def form (caps : Fin 5 → Cap) : Form :=
  bend (linear caps fun p => p.1.b) (linear caps fun p => p.1.j)
    (linear caps fun p => p.1.t) (linear caps Prod.snd)

theorem nat_homogeneous (n : ℕ) : IsHomogeneous (n : Form) 0 := by
  simpa using (isHomogeneous_C (σ:=Fin 5) (n : ℚ))

theorem form_homogeneous (caps : Fin 5 → Cap) : (form caps).IsHomogeneous 5 := by
  unfold form bend
  generalize hb : linear caps (fun a => a.1.b) = b
  generalize hj : linear caps (fun a => a.1.j) = j
  generalize ht : linear caps (fun a => a.1.t) = t
  generalize hh : linear caps Prod.snd = h
  have hb' : b.IsHomogeneous 1 := hb ▸ linear_homogeneous caps _
  have hj' : j.IsHomogeneous 1 := hj ▸ linear_homogeneous caps _
  have ht' : t.IsHomogeneous 1 := ht ▸ linear_homogeneous caps _
  have hh' : h.IsHomogeneous 1 := hh ▸ linear_homogeneous caps _
  have m0 := ((nat_homogeneous 576).neg).mul (hh'.pow 5)
  have m1 := (((nat_homogeneous 160)).mul (ht'.pow 2)).mul (hh'.pow 3)
  have m2 := (((nat_homogeneous 480)).mul (ht'.pow 3)).mul (hh'.pow 2)
  have m3 := (((nat_homogeneous 540)).mul (ht'.pow 4)).mul hh'
  have m4 := (((nat_homogeneous 960)).mul hj').mul (hh'.pow 4)
  have m5 := ((((nat_homogeneous 320)).mul hj').mul ht').mul (hh'.pow 3)
  have m6 := ((((nat_homogeneous 960)).mul hj').mul (ht'.pow 2)).mul (hh'.pow 2)
  have m7 := ((((nat_homogeneous 1200)).mul hj').mul (ht'.pow 3)).mul hh'
  have m8 := (((nat_homogeneous 480)).mul (hj'.pow 2)).mul (hh'.pow 3)
  have m9 := ((((nat_homogeneous 480)).mul (hj'.pow 2)).mul ht').mul (hh'.pow 2)
  have m10 := ((((nat_homogeneous 840)).mul (hj'.pow 2)).mul (ht'.pow 2)).mul hh'
  have m11 := (((nat_homogeneous 240)).mul (hj'.pow 3)).mul (hh'.pow 2)
  have m12 := ((((nat_homogeneous 240)).mul (hj'.pow 3)).mul ht').mul hh'
  have m13 := (((nat_homogeneous 960)).mul hb').mul (hh'.pow 4)
  have m14 := ((((nat_homogeneous 640)).mul hb').mul ht').mul (hh'.pow 3)
  have m15 := ((((nat_homogeneous 1440)).mul hb').mul (ht'.pow 2)).mul (hh'.pow 2)
  have m16 := ((((nat_homogeneous 1440)).mul hb').mul (ht'.pow 3)).mul hh'
  have m17 := ((((nat_homogeneous 640)).mul hb').mul hj').mul (hh'.pow 3)
  have m18 := (((((nat_homogeneous 960)).mul hb').mul hj').mul ht').mul (hh'.pow 2)
  have m19 := (((((nat_homogeneous 1440)).mul hb').mul hj').mul (ht'.pow 2)).mul hh'
  have m20 := ((((nat_homogeneous 480)).mul hb').mul (hj'.pow 2)).mul (hh'.pow 2)
  have m21 := (((((nat_homogeneous 480)).mul hb').mul (hj'.pow 2)).mul ht').mul hh'
  have partial0 := ((((m0).add m1).sub m2).add m3).add m4
  have partial1 := ((((partial0).sub m5).add m6).sub m7).sub m8
  have partial2 := ((((partial1).sub m9).add m10).add m11).sub m12
  have partial3 := ((((partial2).sub m13).add m14).sub m15).add m16
  have partial4 := ((((partial3).add m17).add m18).sub m19).sub m20
  exact (partial4).add m21

theorem evaluate_form (caps : Fin 5 → Cap) (w : Fin 5 → ℚ) :
    eval w (form caps) =
      bend (∑ i : Fin 5, ((caps i).1.b : ℚ) * w i) (∑ i : Fin 5, ((caps i).1.j : ℚ) * w i)
        (∑ i : Fin 5, ((caps i).1.t : ℚ) * w i) (∑ i : Fin 5, ((caps i).2 : ℚ) * w i) := by
  simp only [form, bend, linear, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_sum, eval_C, eval_X]

theorem eval_zero_diagonal (caps : Fin 5 → Cap) (J : Finset (Fin 5)) :
    eval (zeroDiagonal J) (form caps) =
      (Low48Price.bentIntegral (Low48BentLattice.Sum J caps).1.b (Low48BentLattice.Sum J caps).1.j (Low48BentLattice.Sum J caps).1.t (Low48BentLattice.Sum J caps).2 : ℚ) := by
  classical
  rw [evaluate_form]
  simp only [zeroDiagonal, mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter,
    Low48BentLattice.Sum, Nat.cast_sum, Low48Price.bentIntegral, bend]
  push_cast
  rfl

theorem eval_positive_diagonal (caps : Fin 5 → Cap) (J : Finset (Fin 5)) :
    let p := Low48BentLattice.Sum univ (fun i => Scale (positiveDiagonal J i) (caps i))
    eval (fun i => (positiveDiagonal J i : ℚ)) (form caps) =
      (Low48Price.bentIntegral p.1.b p.1.j p.1.t p.2 : ℚ) := by
  rw [evaluate_form]
  simp only [Low48BentLattice.Sum, Scale, Shape.scale, Nat.cast_sum, Nat.cast_mul, Low48Price.bentIntegral, bend]
  push_cast
  simp only [mul_comm]

theorem remove_baseline (caps : Fin 5 → Cap) :
    (∑ J ∈ (univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      (let p := Low48BentLattice.Sum univ (fun i => Scale (positiveDiagonal J i) (caps i))
       (Low48Price.bentIntegral p.1.b p.1.j p.1.t p.2 : ℚ))) =
      ∑ J ∈ (univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        (Low48Price.bentIntegral (Low48BentLattice.Sum J caps).1.b (Low48BentLattice.Sum J caps).1.j (Low48BentLattice.Sum J caps).1.t (Low48BentLattice.Sum J caps).2 : ℚ) := by
  simp_rw [← eval_positive_diagonal, ← eval_zero_diagonal]
  have hhom := homogeneousComponent_eq_self (form_homogeneous caps)
  have h5 : 5 = (univ : Finset (Fin 5)).card := by simp
  calc
    _ = (form caps).coeff (squarefree univ) := by
      have hs := cube_extract univ (form caps)
      simp_rw [line_coeff, ← h5, hhom] at hs
      exact hs
    _ = _ := by
      rw [← zero_cube (form caps), hhom]

end
end Low48BentPolarization
