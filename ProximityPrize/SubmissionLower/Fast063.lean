import ProximityPrize.SubmissionLower.Fast004
import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast054
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast051
import ProximityPrize.SubmissionLower.Fast060
import ProximityPrize.SubmissionLower.Fast049
import ProximityPrize.SubmissionLower.Fast048
import ProximityPrize.SubmissionLower.Fast018
import ProximityPrize.SubmissionLower.Fast019
import ProximityPrize.SubmissionLower.Fast020
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast053
import ProximityPrize.SubmissionLower.Fast040
import ProximityPrize.SubmissionLower.Fast058
import ProximityPrize.SubmissionLower.Fast059
import ProximityPrize.SubmissionLower.Fast056
set_option Elab.async false

section PackSource_K1_13_6_1_4_3_3Packing
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_4_3_3

open K1_13 K1_13_7_1 K1_13_7_1_1
open scoped Pointwise

theorem zero_mem_lattice (p : Shape) : 0 ∈ lattice p := by
  simp [lattice]

theorem mem_lattice_iff {p : Shape} {e : Exponent} :
    e ∈ lattice p ↔ (fun i => (e i : ℝ)) ∈ cap p := by
  change (_ ∧ _ ∧ _) ↔
    (∀ i, 0 ≤ (e i : ℝ)) ∧ ((e 0 : ℝ) + e 1 + e 2 + e 3 ≤ p.b) ∧
      ((e 1 : ℝ) + 2 * e 2 + 3 * e 3 ≤ p.j) ∧ (e 3 : ℝ) ≤ p.t
  simp only [Nat.cast_nonneg, implies_true, true_and]
  exact_mod_cast Iff.rfl

theorem lattice_zero : lattice ⟨0, 0, 0⟩ = 0 := by
  ext e
  rw [mem_lattice_iff, cap_zero, Set.mem_zero, Set.mem_zero]
  constructor
  · intro he
    ext i
    change e i = 0
    have hi : (e i : ℝ) = 0 := congrFun he i
    exact_mod_cast hi
  · rintro rfl
    funext i
    simp

/-- When at least one index budget is even, allocate weight two first,
then use the remaining slots for the weight-one coordinate. -/
private theorem split_weighted {x y A B : ℕ} (h : x + 2 * y ≤ A + B)
    (he : Even A ∨ Even B) :
    ∃ u ≤ x, ∃ v ≤ y, u + 2 * v ≤ A ∧ (x - u) + 2 * (y - v) ≤ B := by
  have hab : (A + B) / 2 = A / 2 + B / 2 := by
    rcases he with ⟨s, hs⟩ | ⟨s, hs⟩ <;> omega
  let v := min y (A / 2)
  have hvy : v ≤ y := min_le_left _ _
  have hvA : v ≤ A / 2 := min_le_right _ _
  have hvB : y - v ≤ B / 2 := by
    dsimp [v]
    omega
  let u := min x (A - 2 * v)
  have hux : u ≤ x := min_le_left _ _
  have huA : u ≤ A - 2 * v := min_le_right _ _
  refine ⟨u, hux, v, hvy, by omega, ?_⟩
  dsimp [u]
  omega

/-- An integral exponent in the sum cap can be allocated between the two
summands when both index and top budgets are even. -/
theorem lattice_add {p q : Shape} (hp : Chamber p) (hq : Chamber q)
    (hpj : Even p.j) (hpt : Even p.t) (hqj : Even q.j) :
    lattice (p.plus q) = lattice p + lattice q := by
  apply Set.Subset.antisymm
  · intro e he
    have hb : e 0 + e 1 + e 2 + e 3 ≤ p.b + q.b := he.1
    have hj : e 1 + 2 * e 2 + 3 * e 3 ≤ p.j + q.j := he.2.1
    have ht : e 3 ≤ p.t + q.t := he.2.2
    let z := min (e 3) p.t
    have hze : z ≤ e 3 := min_le_left _ _
    have hzp : z ≤ p.t := min_le_right _ _
    have hzq : e 3 - z ≤ q.t := by dsimp [z]; omega
    have hpz : 3 * z ≤ p.j := by have := hp.2; omega
    have hqz : 3 * (e 3 - z) ≤ q.j := by have := hq.2; omega
    let A := p.j - 3 * z
    let B := q.j - 3 * (e 3 - z)
    have heven : Even A ∨ Even B := by
      rcases le_total (e 3) p.t with h | h
      · have hz : z = e 3 := min_eq_left h
        exact Or.inr (by simpa [B, hz] using hqj)
      · have hz : z = p.t := min_eq_right h
        apply Or.inl
        obtain ⟨a, ha⟩ := hpj
        obtain ⟨b, hb'⟩ := hpt
        refine ⟨a - 3 * b, ?_⟩
        dsimp [A]
        omega
    obtain ⟨u, hu, v, hv, huvA, huvB⟩ :=
      split_weighted (x := e 1) (y := e 2) (A := A) (B := B)
        (by dsimp [A, B]; omega) heven
    change u + 2 * v ≤ p.j - 3 * z at huvA
    change (e 1 - u) + 2 * (e 2 - v) ≤ q.j - 3 * (e 3 - z) at huvB
    have hsumP : u + v + z ≤ p.b := by have := hp.1; omega
    have hsumQ : (e 1 - u) + (e 2 - v) + (e 3 - z) ≤ q.b := by have := hq.1; omega
    let x := min (e 0) (p.b - u - v - z)
    have hxe : x ≤ e 0 := min_le_left _ _
    have hxp : x ≤ p.b - u - v - z := min_le_right _ _
    have hxq : (e 0 - x) + (e 1 - u) + (e 2 - v) + (e 3 - z) ≤ q.b := by
      dsimp [x]
      omega
    let a : Exponent := Finsupp.equivFunOnFinite.symm ![x, u, v, z]
    have ha (i : Fin 4) : a i = (![x, u, v, z] : Fin 4 → ℕ) i := rfl
    have haP : a ∈ lattice p := by
      change a 0 + a 1 + a 2 + a 3 ≤ p.b ∧ a 1 + 2 * a 2 + 3 * a 3 ≤ p.j ∧ a 3 ≤ p.t
      rw [ha 0, ha 1, ha 2, ha 3]
      change x + u + v + z ≤ p.b ∧ u + 2 * v + 3 * z ≤ p.j ∧ z ≤ p.t
      omega
    have hae : a ≤ e := by
      intro i
      fin_cases i <;> rw [ha] <;> assumption
    have haQ : e - a ∈ lattice q := by
      change (e - a) 0 + (e - a) 1 + (e - a) 2 + (e - a) 3 ≤ q.b ∧
        (e - a) 1 + 2 * (e - a) 2 + 3 * (e - a) 3 ≤ q.j ∧ (e - a) 3 ≤ q.t
      simp only [Finsupp.tsub_apply, ha]
      change (e 0 - x) + (e 1 - u) + (e 2 - v) + (e 3 - z) ≤ q.b ∧
        (e 1 - u) + 2 * (e 2 - v) + 3 * (e 3 - z) ≤ q.j ∧ e 3 - z ≤ q.t
      omega
    exact Set.mem_add.mpr ⟨a, haP, e - a, haQ, add_tsub_cancel_of_le hae⟩
  · rintro e ⟨a, ha, b, hb, rfl⟩
    rw [mem_lattice_iff] at ha hb ⊢
    rw [cap_add hp hq]
    exact Set.mem_add.mpr ⟨_, ha, _, hb, by ext i; simp [Finsupp.add_apply]⟩

theorem chamber_scale {p : Shape} (hp : Chamber p) (n : ℕ) : Chamber (p.scale n) := by
  refine ⟨Nat.mul_le_mul_left n hp.1, ?_⟩
  change 3 * (n * p.t) ≤ n * p.j
  simpa only [Nat.mul_left_comm] using Nat.mul_le_mul_left n hp.2

theorem lattice_scale {p : Shape} (hp : Chamber p) (hj : Even p.j) (ht : Even p.t)
    (n : ℕ) : lattice (p.scale n) = n • lattice p := by
  induction n with
  | zero =>
    simpa [Shape.scale] using lattice_zero
  | succ n ih =>
    have he : Even (p.scale n).j := by
      change Even (n * p.j)
      exact hj.mul_left n
    have hs : p.scale (n + 1) = p.plus (p.scale n) := by
      cases p
      simp [Shape.scale, Shape.plus, Nat.add_mul, Nat.add_comm]
    rw [hs, lattice_add hp (chamber_scale hp n) hj ht he, ih, succ_nsmul']

end K1_13_6_1_4_3_3
end PackSource_K1_13_6_1_4_3_3Packing

section PackSource_K1_13_6_1_4_3_3Volume
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_4_3_3

noncomputable section

open K1_13 K1_13_7_1 K1_13_7_1_1 MeasureTheory Filter Set
open scoped ENNReal Topology

private def unitCell (e : Exponent) : Set RealPoint :=
  univ.pi fun i => Ico (e i : ℝ) ((e i : ℝ) + 1)

private theorem unitCell_disjoint {e f : Exponent} (h : e ≠ f) :
    Disjoint (unitCell e) (unitCell f) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply h
  ext i
  have hxe := hx i (mem_univ i)
  have hxf := hy i (mem_univ i)
  change (e i : ℝ) ≤ x i ∧ x i < (e i : ℝ) + 1 at hxe
  change (f i : ℝ) ≤ x i ∧ x i < (f i : ℝ) + 1 at hxf
  have hef : (e i : ℝ) < (f i : ℝ) + 1 := hxe.1.trans_lt hxf.2
  have hfe : (f i : ℝ) < (e i : ℝ) + 1 := hxf.1.trans_lt hxe.2
  exact le_antisymm (Nat.lt_succ_iff.mp (by exact_mod_cast hef))
    (Nat.lt_succ_iff.mp (by exact_mod_cast hfe))

private def cells (p : Shape) : Set RealPoint :=
  ⋃ e ∈ (lattice_finite p).toFinset, unitCell e

private theorem volume_cells (p : Shape) : volume (cells p) = ((lattice p).ncard : ℝ≥0∞) := by
  rw [cells, measure_biUnion_finset
    (fun _ _ _ _ h => unitCell_disjoint h)
    (fun _ _ => MeasurableSet.univ_pi fun _ => measurableSet_Ico)]
  have hvol (e : Exponent) : volume (unitCell e) = 1 := by
    unfold unitCell
    rw [Real.volume_pi_Ico]
    simp
  simp only [hvol, Finset.sum_const, nsmul_one, Set.ncard_eq_toFinset_card _ (lattice_finite p)]

private theorem cap_subset_cells (p : Shape) : cap p ⊆ cells p := by
  intro x hx
  obtain ⟨hx, hb, hj, ht⟩ := hx
  let e : Exponent := Finsupp.equivFunOnFinite.symm (fun i => ⌊x i⌋₊)
  have he (i : Fin 4) : e i = ⌊x i⌋₊ := rfl
  have hlo (i : Fin 4) : (e i : ℝ) ≤ x i := by rw [he]; exact Nat.floor_le (hx i)
  have hhi (i : Fin 4) : x i < (e i : ℝ) + 1 := by rw [he]; exact Nat.lt_floor_add_one _
  have hm : e ∈ lattice p := by
    apply mem_lattice_iff.mpr
    exact ⟨fun _ => Nat.cast_nonneg _, by linarith [hlo 0, hlo 1, hlo 2, hlo 3],
      by linarith [hlo 1, hlo 2, hlo 3], (hlo 3).trans ht⟩
  exact mem_iUnion₂.mpr ⟨e, (lattice_finite p).mem_toFinset.mpr hm, fun i _ => ⟨hlo i, hhi i⟩⟩

private def padding : Shape := ⟨6, 6, 1⟩

private theorem cells_subset_cap (p : Shape) : cells p ⊆ cap (p.plus padding) := by
  intro x hx
  obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
  have he' := mem_lattice_iff.mp ((lattice_finite p).mem_toFinset.mp he)
  obtain ⟨hn, hb, hj, ht⟩ := he'
  have hlo (i : Fin 4) : (e i : ℝ) ≤ x i := (hxe i (mem_univ i)).1
  have hhi (i : Fin 4) : x i < (e i : ℝ) + 1 := (hxe i (mem_univ i)).2
  refine ⟨fun i => (hn i).trans (hlo i), ?_, ?_, ?_⟩ <;>
    simp only [Shape.plus, padding, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] <;>
    linarith [hhi 0, hhi 1, hhi 2, hhi 3]

private theorem volume_cap_ne_top (p : Shape) : volume (cap p) ≠ ∞ := by
  let box : Set RealPoint := Icc 0 fun _ => (p.b : ℝ)
  have hs : cap p ⊆ box := by
    intro x hx
    obtain ⟨hx, hb, _, _⟩ := hx
    refine ⟨hx, ?_⟩
    intro i
    change x i ≤ (p.b : ℝ)
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    have h3 := hx 3
    fin_cases i
    · change x 0 ≤ (p.b : ℝ)
      linarith
    · change x 1 ≤ (p.b : ℝ)
      linarith
    · change x 2 ≤ (p.b : ℝ)
      linarith
    · change x 3 ≤ (p.b : ℝ)
      linarith
  have hfin : volume box ≠ ∞ := by
    change volume (Icc (0 : RealPoint) fun _ => (p.b : ℝ)) ≠ ∞
    rw [Real.volume_Icc_pi]
    exact ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top
  exact (measure_lt_top_of_subset hs hfin).ne

private theorem lattice_volume_bounds (p : Shape) :
    (volume (cap p)).toReal ≤ ((lattice p).ncard : ℝ) ∧
      ((lattice p).ncard : ℝ) ≤ (volume (cap (p.plus padding))).toReal := by
  have hlo := measure_mono (μ := volume) (cap_subset_cells p)
  have hhi := measure_mono (μ := volume) (cells_subset_cap p)
  rw [volume_cells] at hlo hhi
  exact ⟨by simpa using ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hlo,
    by simpa using ENNReal.toReal_mono (volume_cap_ne_top _) hhi⟩

private def volumeFormula (b j t : ℝ) : ℝ :=
  (8*b*j^2*t - 24*b*j*t^2 + 24*b*t^3 - 4*j^3*t + 14*j^2*t^2 - 20*j*t^3 + 9*t^4) / 32

private theorem volume_eq_formula (p : Shape) (hp : Chamber p) :
    (volume (cap p)).toReal = volumeFormula p.b p.j p.t := by
  have h := K1_13_6_1_4_3.cap_volume32 p hp
  unfold volume32 at h
  push_cast at h
  unfold volumeFormula
  linarith

private theorem ratio_volume (R p : Shape) (hR : Chamber R) (hp : Chamber p) :
    Tendsto (fun n : ℕ => (volume (cap (R.plus (p.scale n)))).toReal / (n : ℝ)^4)
      atTop (𝓝 (volume (cap p)).toReal) := by
  have hcoord (r s : ℕ) :
      Tendsto (fun n : ℕ => (s : ℝ) + (r : ℝ) / n) atTop (𝓝 (s : ℝ)) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (r : ℝ)).const_add (s : ℝ)
  let f : ℝ × ℝ × ℝ → ℝ := fun y => volumeFormula y.1 y.2.1 y.2.2
  have hc : Continuous f := by unfold f volumeFormula; fun_prop
  have h := hc.continuousAt.tendsto.comp
    ((hcoord R.b p.b).prodMk_nhds ((hcoord R.j p.j).prodMk_nhds (hcoord R.t p.t)))
  rw [volume_eq_formula p hp]
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
  rw [volume_eq_formula _ (chamber_plus hR (chamber_scale hp n))]
  simp only [f, Function.comp_apply, Shape.plus, Shape.scale, Nat.cast_add, Nat.cast_mul]
  unfold volumeFormula
  field_simp
  ring

/-- The normalized count has the cap's volume as its limit, even along a
lower-dimensional direction and with a fixed baseline. -/
theorem lattice_ratio (R p : Shape) (hR : Chamber R) (hp : Chamber p) :
    Tendsto (fun n : ℕ => ((lattice (R.plus (p.scale n))).ncard : ℝ) / (n : ℝ)^4)
      atTop (𝓝 (volume (cap p)).toReal) := by
  have hpad : Chamber padding := ⟨by decide, by decide⟩
  have hassoc (n : ℕ) : (R.plus (p.scale n)).plus padding = (R.plus padding).plus (p.scale n) := by
    cases R
    cases p
    simp [Shape.plus, Shape.scale, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (ratio_volume R p hR hp)
    (ratio_volume (R.plus padding) p (chamber_plus hR hpad) hp)
  · intro n
    exact div_le_div_of_nonneg_right (lattice_volume_bounds _).1 (by positivity)
  · intro n
    have hb := div_le_div_of_nonneg_right (lattice_volume_bounds (R.plus (p.scale n))).2
      (by positivity : 0 ≤ (n : ℝ)^4)
    simpa only [hassoc] using hb

end

end K1_13_6_1_4_3_3
end PackSource_K1_13_6_1_4_3_3Volume

section PackSource_K1_13_6_1_4_3_3_3Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_4_3_3_3

noncomputable section

open K1_13 K1_13_6_1_4_3_3 MvPolynomial

abbrev Degree := Fin 4 → ℕ
abbrev GenericJets (k : Type) [Field k] (P : Fin 4 → Shape) :=
  Jets (CoefficientField k P)

/-- The fifth factor supplies the four coordinate monomials on the affine chart. -/
def auxiliary : Shape := ⟨6, 6, 2⟩

/-- The cap for a graded piece, with the auxiliary degree kept separate. -/
def shapeAt (P : Fin 4 → Shape) (b : ℕ) (d : Degree) : Shape :=
  (((((auxiliary.scale b).plus ((P 0).scale (d 0))).plus
    ((P 1).scale (d 1))).plus ((P 2).scale (d 2))).plus ((P 3).scale (d 3)))

def shift (d : Degree) (i : Fin 4) (n : ℕ) : Degree := d + Pi.single i n

/-- The polynomials in one dehomogenized multidegree. -/
def piece (k : Type) [Field k] (P : Fin 4 → Shape) (b : ℕ) (d : Degree) :
    Submodule (CoefficientField k P) (GenericJets k P) :=
  restrictSupport (CoefficientField k P) (lattice (shapeAt P b d))

/-- The first `r` affine cuts, with the full independent coefficient field. -/
def prefixIdeal (k : Type) [Field k] (P : Fin 4 → Shape) (r : ℕ) :
    Ideal (GenericJets k P) :=
  Ideal.span (genericEquation k P '' {i : Fin 4 | i.val < r})

end

end K1_13_6_1_4_3_3_3
end PackSource_K1_13_6_1_4_3_3_3Defs

section PackSource_K1_13_6_1_4_3_3_3Pieces
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_4_3_3_3

noncomputable section

open K1_13 K1_13_7_1 K1_13_7_1_1 K1_13_6_1_4_3_3 MvPolynomial
open scoped Pointwise

private theorem auxiliary_admissible : Chamber auxiliary ∧ Even auxiliary.j ∧ Even auxiliary.t :=
  ⟨⟨by decide, by decide⟩, ⟨3, rfl⟩, ⟨1, rfl⟩⟩

theorem auxiliary_contains_coordinate (i : Fin 4) : Finsupp.single i 1 ∈ lattice auxiliary := by
  fin_cases i <;> norm_num [lattice, auxiliary, Finsupp.single_apply]

private theorem scale_admissible {p : Shape} (hp : Chamber p ∧ Even p.j ∧ Even p.t)
    (n : ℕ) : Chamber (p.scale n) ∧ Even (p.scale n).j ∧ Even (p.scale n).t :=
  ⟨chamber_scale hp.1 n, hp.2.1.mul_left n, hp.2.2.mul_left n⟩

private theorem plus_admissible {p q : Shape} (hp : Chamber p ∧ Even p.j ∧ Even p.t)
    (hq : Chamber q ∧ Even q.j ∧ Even q.t) :
    Chamber (p.plus q) ∧ Even (p.plus q).j ∧ Even (p.plus q).t :=
  ⟨chamber_plus hp.1 hq.1, hp.2.1.add hq.2.1, hp.2.2.add hq.2.2⟩

private theorem shapePlus_comm (p q : Shape) : p.plus q = q.plus p := by
  cases p
  cases q
  simp [Shape.plus, Nat.add_comm]

theorem shapeAt_admissible {P : Fin 4 → Shape}
    (hP : ∀ i, Chamber (P i) ∧ Even (P i).j ∧ Even (P i).t) (b : ℕ) (d : Degree) :
    Chamber (shapeAt P b d) ∧ Even (shapeAt P b d).j ∧ Even (shapeAt P b d).t :=
  plus_admissible (plus_admissible (plus_admissible (plus_admissible
    (scale_admissible auxiliary_admissible b) (scale_admissible (hP 0) (d 0)))
    (scale_admissible (hP 1) (d 1))) (scale_admissible (hP 2) (d 2)))
    (scale_admissible (hP 3) (d 3))

/-- Every lattice exponent of the cap is a sum of the prescribed numbers of
monomials from the five factors. -/
theorem lattice_shapeAt {P : Fin 4 → Shape}
    (hP : ∀ i, Chamber (P i) ∧ Even (P i).j ∧ Even (P i).t) (b : ℕ) (d : Degree) :
    lattice (shapeAt P b d) = ((((b • lattice auxiliary + d 0 • lattice (P 0)) +
      d 1 • lattice (P 1)) + d 2 • lattice (P 2)) + d 3 • lattice (P 3)) := by
  have hA := scale_admissible auxiliary_admissible b
  have hS (i : Fin 4) := scale_admissible (hP i) (d i)
  have h0 := plus_admissible hA (hS 0)
  have h1 := plus_admissible h0 (hS 1)
  have h2 := plus_admissible h1 (hS 2)
  have hadd {p q : Shape} (hp : Chamber p ∧ Even p.j ∧ Even p.t)
      (hq : Chamber q ∧ Even q.j ∧ Even q.t) : lattice (p.plus q) = lattice p + lattice q :=
    lattice_add hp.1 hq.1 hp.2.1 hp.2.2 hq.2.1
  have hscale (i : Fin 4) := lattice_scale (hP i).1 (hP i).2.1 (hP i).2.2 (d i)
  unfold shapeAt
  rw [hadd h2 (hS 3), hadd h1 (hS 2), hadd h0 (hS 1), hadd hA (hS 0),
    lattice_scale auxiliary_admissible.1 auxiliary_admissible.2.1 auxiliary_admissible.2.2 b,
    hscale 0, hscale 1, hscale 2, hscale 3]

theorem shapeAt_shift (P : Fin 4 → Shape) (b : ℕ) (d : Degree) (i : Fin 4) (n : ℕ) :
    shapeAt P b (shift d i n) = (shapeAt P b d).plus ((P i).scale n) := by
  fin_cases i <;>
    simp [shapeAt, shift, Shape.plus, Shape.scale, Pi.single_eq_of_ne, Nat.add_mul] <;>
    omega

variable {k : Type} [Field k] {P : Fin 4 → Shape}

instance piece_finite (b : ℕ) (d : Degree) : Module.Finite (CoefficientField k P) (piece k P b d) :=
  FiniteDimensional.of_finite_basis (basisRestrictSupport _ _) (lattice_finite _)

private theorem generic_supported (i : Fin 4) :
    genericEquation k P i ∈ restrictSupport (CoefficientField k P) (lattice (P i)) := by
  classical
  unfold genericEquation
  apply Submodule.sum_mem
  intro e _
  exact (monomial_mem_restrictSupport _).mpr (Or.inl e.property)

theorem equation_mul_mem_piece (hP : ∀ i, Chamber (P i) ∧ Even (P i).j ∧ Even (P i).t)
    (b : ℕ) (d : Degree) (i : Fin 4) {p : GenericJets k P} (hp : p ∈ piece k P b d) :
    genericEquation k P i * p ∈ piece k P b (shift d i 1) := by
  have hd := shapeAt_admissible hP b d
  have h := Submodule.mul_mem_mul (generic_supported (k := k) (P := P) i) hp
  change genericEquation k P i * p ∈ restrictSupport _ _ * restrictSupport _ _ at h
  rw [← restrictSupport_add, ← lattice_add (hP i).1 hd.1 (hP i).2.1 (hP i).2.2 hd.2.1] at h
  unfold piece
  rw [shapeAt_shift, show (P i).scale 1 = P i from by cases P i; simp [Shape.scale]]
  rwa [shapePlus_comm] at h

private theorem lattice_mono {p q : Shape} (hb : p.b ≤ q.b) (hj : p.j ≤ q.j) (ht : p.t ≤ q.t) :
    lattice p ⊆ lattice q := fun _ h => ⟨h.1.trans hb, h.2.1.trans hj, h.2.2.trans ht⟩

theorem piece_mono {b c : ℕ} {d e : Degree} (hbc : b ≤ c) (hde : d ≤ e) :
    piece k P b d ≤ piece k P c e := by
  unfold piece
  apply restrictSupport_mono
  have h0 := hde 0
  have h1 := hde 1
  have h2 := hde 2
  have h3 := hde 3
  apply lattice_mono <;> simp only [shapeAt, Shape.plus, Shape.scale] <;> gcongr

/-- The auxiliary cap alone contains any fixed affine polynomial for sufficiently large degree. -/
theorem piece_exhaustive (p : GenericJets k P) : ∃ b : ℕ, p ∈ piece k P b (fun _ => 0) := by
  refine ⟨p.totalDegree, ?_⟩
  apply (mem_restrictSupport_iff _).mpr
  intro e he
  have hd := le_totalDegree (show e ∈ p.support from he)
  rw [Finsupp.sum_fintype e (fun _ m => m) (fun _ => rfl), Fin.sum_univ_four] at hd
  simp only [lattice, Set.mem_ofPred_eq, shapeAt, Shape.plus, Shape.scale, auxiliary,
    Nat.zero_mul, Nat.add_zero]
  omega

theorem finrank_piece (b : ℕ) (d : Degree) :
    Module.finrank (CoefficientField k P) (piece k P b d) = (lattice (shapeAt P b d)).ncard := by
  rw [piece, Module.finrank_eq_nat_card_basis (basisRestrictSupport _ _), Nat.card_coe_set_eq]

end
end K1_13_6_1_4_3_3_3
end PackSource_K1_13_6_1_4_3_3_3Pieces

section PackSource_K1_13_6_1_4_3_3_3Finite
set_option autoImplicit true
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace K1_13_6_1_4_3_3_3

noncomputable section

open K1_13 K1_13_6_1_4_3_3 MvPolynomial

/-- If a polynomial parametrization with as many variables as the coefficient
field captures all its coefficient variables, its image is algebraic over that field. -/
private theorem image_algebraic {k σ D : Type} [Field k] [Fintype σ]
    [CommRing D] [Algebra k D] [Algebra (FractionRing (MvPolynomial σ k)) D]
    [IsScalarTower k (FractionRing (MvPolynomial σ k)) D]
    (f : MvPolynomial σ k →ₐ[k] D)
    (c : σ → MvPolynomial σ k)
    (hc : ∀ i, f (c i) = algebraMap (FractionRing (MvPolynomial σ k)) D
      (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k)) (MvPolynomial.X i)))
    (x : MvPolynomial σ k) : IsAlgebraic (FractionRing (MvPolynomial σ k)) (f x) := by
  let B := MvPolynomial σ k
  let F := FractionRing B
  by_contra hx
  have hX : AlgebraicIndependent k (fun i : σ => algebraMap B F (MvPolynomial.X i)) :=
    (algebraicIndependent_X σ k).map'
      (f := IsScalarTower.toAlgHom k B F) (IsFractionRing.injective B F)
  have hx' : AlgebraicIndependent F (fun _ : Unit => f x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have h := hX.sumElim_comp hx'
  have h' : AlgebraicIndependent k (f ∘ Sum.elim (fun _ : Unit => x) c) := by
    convert h using 1
    funext i
    cases i with
    | inl _ => rfl
    | inr i => exact hc i
  have hle := (AlgebraicIndependent.of_comp f h').cardinalMk_le_trdeg
  rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype (Unit ⊕ σ),
    Cardinal.mk_fintype σ, Fintype.card_sum, Fintype.card_unit] at hle
  have : 1 + Fintype.card σ ≤ Fintype.card σ := by exact_mod_cast hle
  omega

/-- Eliminate the four constant coefficients using the affine equations.
The four spatial coordinates replace them in the polynomial parametrization. -/
theorem generic_finite (k : Type) [Field k] (P : Fin 4 → Shape) :
    Module.Finite (CoefficientField k P) (GenericAlgebra k P) := by
  classical
  let (i : Fin 4) : Fintype (lattice (P i)) := (lattice_finite (P i)).fintype
  let σ := Σ i : Fin 4, lattice (P i)
  let : Fintype σ := inferInstanceAs (Fintype (Σ i : Fin 4, lattice (P i)))
  let B := CoefficientRing k P
  let F := CoefficientField k P
  let J := CutIdeal (genericEquation k P)
  let D := GenericAlgebra k P
  let q : GenericJets k P →ₐ[F] D := Ideal.Quotient.mkₐ F J
  let p (i : Fin 4) : lattice (P i) := ⟨0, zero_mem_lattice _⟩
  let coord (i : Fin 4) : D := q (MvPolynomial.X i)
  let coeff (v : σ) : D := algebraMap F D (algebraMap B F (MvPolynomial.X v))
  let f : B →ₐ[k] D := aeval (fun v : σ => if v.2.val = 0 then coord v.1 else coeff v)
  let S := f.toRingHom.range
  have hcoord (i : Fin 4) : coord i ∈ S := by
    refine ⟨MvPolynomial.X ⟨i, p i⟩, ?_⟩
    change f (MvPolynomial.X ⟨i, p i⟩) = coord i
    dsimp only [f]
    rw [aeval_X, ite_eq_left (show (p i).val = 0 from rfl)]
  have hfree (i : Fin 4) (a : lattice (P i)) (ha : a.val ≠ 0) : coeff ⟨i, a⟩ ∈ S := by
    refine ⟨MvPolynomial.X ⟨i, a⟩, ?_⟩
    change f (MvPolynomial.X ⟨i, a⟩) = coeff ⟨i, a⟩
    dsimp only [f]
    rw [aeval_X, ite_eq_right ha]
  have hcoeff (v : σ) : coeff v ∈ S := by
    rcases v with ⟨i, a⟩
    by_cases ha : a.val = 0
    · have hap : a = p i := Subtype.ext ha
      subst a
      let term (e : lattice (P i)) : D :=
        coeff ⟨i, e⟩ * e.val.prod (fun j n => coord j ^ n)
      have ht (e : lattice (P i)) :
          q (monomial e.val (algebraMap B F (MvPolynomial.X ⟨i, e⟩))) = term e := by
        rw [monomial_eq, map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
          map_finsuppProd]
        simp only [term, coeff, coord, map_pow]
      have hz : q (genericEquation k P i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
      have hsum : q (genericEquation k P i) = ∑ e : lattice (P i), term e := by
        rw [genericEquation, map_sum]
        exact Finset.sum_congr rfl fun e _ => ht e
      rw [hsum, ← Finset.sum_erase_add _ _ (Finset.mem_univ (p i)),
        show term (p i) = coeff ⟨i, p i⟩ by simp [term, p]] at hz
      rw [eq_neg_of_add_eq_zero_right hz]
      apply S.neg_mem (S.sum_mem fun e he => ?_)
      have hne : e.val ≠ 0 := fun he0 => (Finset.mem_erase.mp he).1 (Subtype.ext he0)
      exact S.mul_mem (hfree i e hne)
        (S.prod_mem fun j _ => S.pow_mem (hcoord j) _)
    · exact hfree i a ha
  choose liftCoeff hliftCoeff using hcoeff
  have halg (i : Fin 4) : IsAlgebraic F (coord i) := by
    obtain ⟨x, hx⟩ := hcoord i
    change f x = coord i at hx
    rw [← hx]
    exact image_algebraic f liftCoeff hliftCoeff x
  have hadj : Algebra.adjoin F (Set.range coord) = ⊤ := by
    rw [show coord = q ∘ MvPolynomial.X from rfl, Set.range_comp, Algebra.adjoin_image,
      MvPolynomial.adjoin_range_X, Algebra.map_top,
      (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective F J)]
  have h := Algebra.isAlgebraic_adjoin_iff.mpr (Set.forall_mem_range.mpr halg)
  rw [hadj] at h
  let : Algebra.IsIntegral F D :=
    Algebra.isAlgebraic_iff_isIntegral.mp (Algebra.isAlgebraic_iff.mpr h)
  exact Algebra.IsIntegral.finite

end
end K1_13_6_1_4_3_3_3
end PackSource_K1_13_6_1_4_3_3_3Finite

section PackSource_K1_13_6_1_4_3_3_3Box
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_4_3_3_3

noncomputable section

open K1_13 K1_13_6_1_4_3_3

def degreeDifference (F : Degree → ℝ) (i : Fin 4) (n : ℕ) (d : Degree) : ℝ :=
  F (shift d i n) - F d

def degreeDifferences (n : ℕ) (F : Degree → ℝ) (is : List (Fin 4)) : Degree → ℝ :=
  is.foldl (fun H i => degreeDifference H i n) F

private theorem le_shift (d : Degree) (i : Fin 4) (n : ℕ) : d ≤ shift d i n :=
  fun _ => Nat.le_add_right _ _

private theorem shift_succ (d : Degree) (i : Fin 4) (n : ℕ) :
    shift d i (n + 1) = shift (shift d i n) i 1 := by
  funext j
  by_cases h : j = i <;> simp [shift, h, Pi.single_eq_of_ne, add_assoc]

private theorem shift_comm (d : Degree) (i j : Fin 4) (t n : ℕ) :
    shift (shift d j n) i t = shift (shift d i t) j n := by
  unfold shift
  ac_rfl

private theorem line_sum {F G : Degree → ℝ} {q : ℕ} {i : Fin 4}
    (h : ∀ d : Degree, (∀ j, q ≤ d j) → F (shift d i 1) - F d = G (shift d i 1))
    (n : ℕ) (d : Degree) (hd : ∀ j, q ≤ d j) :
    degreeDifference F i n d = ∑ t ∈ Finset.range n, G (shift d i (t + 1)) := by
  induction n with
  | zero => simp [degreeDifference, shift]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, degreeDifference, degreeDifference, shift_succ d i n,
      ← h (shift d i n) (fun j => (hd j).trans (le_shift d i n j))]
    ring

private theorem differences_sum {q : ℕ} {i : Fin 4} {U G : Degree → ℝ}
    (n : ℕ) (is : List (Fin 4))
    (h : ∀ d : Degree, (∀ j, q ≤ d j) → U d = ∑ t ∈ Finset.range n, G (shift d i (t + 1)))
    (d : Degree) (hd : ∀ j, q ≤ d j) :
    degreeDifferences n U is d =
      ∑ t ∈ Finset.range n, degreeDifferences n G is (shift d i (t + 1)) := by
  induction is generalizing U G d with
  | nil => exact h d hd
  | cons j is ih =>
    apply ih (U := degreeDifference U j n) (G := degreeDifference G j n) _ d hd
    intro e he
    simp only [degreeDifference, h (shift e j n) (fun l => (he l).trans (le_shift e j n l)),
      h e he, ← Finset.sum_sub_distrib, shift_comm e i j]

private theorem box_step {F G : Degree → ℝ} {q : ℕ} {i : Fin 4}
    (h : ∀ d : Degree, (∀ j, q ≤ d j) → F (shift d i 1) - F d = G (shift d i 1))
    (n : ℕ) (is : List (Fin 4)) (d : Degree) (hd : ∀ j, q ≤ d j) :
    degreeDifferences n F (i :: is) d =
      ∑ t ∈ Finset.range n, degreeDifferences n G is (shift d i (t + 1)) :=
  differences_sum n is (line_sum h n) d hd

/-- Each point of the four-dimensional box contributes its terminal rank. -/
theorem fourfold_telescoping (H : ℕ → Degree → ℝ) (C : ℝ) (q : ℕ)
    (hstep : ∀ (i : Fin 4) (d : Degree), (∀ j, q ≤ d j) →
      H i.val (shift d i 1) - H i.val d = H (i.val + 1) (shift d i 1))
    (htop : ∀ d : Degree, (∀ j, q ≤ d j) → H 4 d = C)
    (n : ℕ) (d : Degree) (hd : ∀ j, q ≤ d j) :
    degreeDifferences n (H 0) [0, 1, 2, 3] d = C * (n : ℝ)^4 := by
  let tail := List.finRange 4
  have htail (i : Fin 4) : tail.drop i.val = i :: tail.drop (i.val + 1) := by
    fin_cases i <;> decide
  have hbox (r : ℕ) (hr : r ≤ 4) : ∀ e : Degree, (∀ j, q ≤ e j) →
      degreeDifferences n (H r) (tail.drop r) e = C * (n : ℝ)^(4 - r) := by
    refine Nat.decreasingInduction' (m := r) (n := 4)
      (P := fun l => ∀ e : Degree, (∀ j, q ≤ e j) →
        degreeDifferences n (H l) (tail.drop l) e = C * (n : ℝ)^(4 - l)) ?_ hr ?_
    · intro l hl _ ih e he
      let i : Fin 4 := ⟨l, hl⟩
      have ht : tail.drop l = i :: tail.drop (l + 1) := htail i
      rw [ht, box_step (hstep i) _ _ _ he]
      calc
        _ = ∑ _t ∈ Finset.range n, C * (n : ℝ)^(4 - (l + 1)) :=
          Finset.sum_congr rfl fun t _ =>
            ih (shift e i (t + 1)) (fun j => (he j).trans (le_shift e i (t + 1) j))
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [show 4 - l = (4 - (l + 1)) + 1 by omega, pow_succ]
          ring
    · intro e he
      simpa [degreeDifferences, tail, show (List.finRange 4).drop 4 = [] by decide] using htop e he
  exact hbox 0 (by decide) d hd

/-- A shift in a single multidegree is the matching shift of the cap. -/
theorem shape_differences (P : Fin 4 → Shape) (b n : ℕ) (F : Shape → ℝ)
    (d : Degree) (is : List (Fin 4)) :
    degreeDifferences n (fun e => F (shapeAt P b e)) is d =
      is.foldl (fun G i => shapeDifference G ((P i).scale n)) F (shapeAt P b d) := by
  induction is generalizing F with
  | nil => rfl
  | cons i is ih =>
    have he : degreeDifference (fun e => F (shapeAt P b e)) i n =
        fun e => shapeDifference F ((P i).scale n) (shapeAt P b e) := by
      funext e
      simp only [degreeDifference, shapeAt_shift, shapeDifference]
    change degreeDifferences n (degreeDifference (fun e => F (shapeAt P b e)) i n) is d = _
    rw [he]
    exact ih _

end

end K1_13_6_1_4_3_3_3
end PackSource_K1_13_6_1_4_3_3_3Box

section PackSource_K1_13_6_1_3Defs
set_option autoImplicit true
namespace K1_13_6_1_3
noncomputable section
open Polynomial K1_13 K1_13_6

abbrev RationalJets := MvPolynomial (Fin 4) GenericField

def toRational : Row 4 →+* RationalJets :=
  MvPolynomial.map (algebraMap Geom[X] GenericField)

/-- The contraction before geometric scalar extension. -/
abbrev contractedPrime (surface : Ideal GeoJets) : Ideal RationalJets :=
  surface.comap (MvPolynomial.map (algebraMap GenericField GeoField))

/-- Length on the rational chart, before geometric scalar extension,
expressed as the coheight of the localized intersection ideal. -/
def contractedLength (g P : Row 4) (surface : Ideal GeoJets) (hp : surface.IsPrime) : ℕ∞ := by
  letI := hp
  let L := Localization.AtPrime (contractedPrime surface)
  let J : Ideal L := (Ideal.span {toRational g, toRational P}).map (algebraMap RationalJets L)
  exact Order.coheight J

/-- A uniformizer on the rational chart, and a cutter of exact order v,
expressed in the source polynomial ring by clearing denominators. -/
def NormalForm (g P : Row 4) (surface : Ideal GeoJets) (v : ℕ) : Prop :=
  ∃ t d u B : Row 4,
    toGeneric t ∈ surface ∧ toGeneric d ∉ surface ∧ toGeneric u ∉ surface ∧
    d * P = B * g + u * t ^ v ∧
    ∀ a : Row 4, toGeneric a ∈ surface →
      ∃ e C W : Row 4, toGeneric e ∉ surface ∧ e * a = C * g + W * t

end
end K1_13_6_1_3
end PackSource_K1_13_6_1_3Defs

section PackSource_K1_13_6_1_3Boxes
set_option autoImplicit true
namespace K1_13_6_1_3
noncomputable section
open Polynomial MvPolynomial K1_13 K1_13_1 K1_13_6 K1_13_6_1 K1_13_7_1

local notation "W" => MvPolynomial.weightedTotalDegree

private theorem pderiv_zero_of_weight_lt (w : Fin 4 → ℕ) (i : Fin 4) (P : Row 4)
    (h : W w P < w i) : pderiv i P = 0 := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_pderiv]
  have hz : P.coeff (m + Finsupp.single i 1) = 0 := by
    by_contra hn
    have hm := le_weightedTotalDegree w (MvPolynomial.mem_support_iff.mpr hn)
    rw [map_add, Finsupp.weight_single, one_smul] at hm
    omega
  simp [hz]

private theorem weight_coeff_deriv (w : Fin 4 → ℕ) (P : Row 4) :
    W w (coefficientDerivative P) ≤ W w P := by
  classical
  apply weight_le_of_support_subset
  intro m hm
  obtain ⟨j, hj, hmj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  have h : j = m := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hmj) (by rw [MvPolynomial.coeff_monomial, ite_eq_right hne])
  exact h ▸ hj

private theorem partialFlow_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    (P : Row 4) {d : ℕ} (hP : W w P ≤ d) : W w (partialFlow P) ≤ d + Δ := by
  classical
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.add_mem
  · exact mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
      ((weight_coeff_deriv w P).trans (hP.trans (Nat.le_add_right _ _)))
  · apply Submodule.sum_mem
    intro i _
    apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    rw [mul_assoc]
    apply (weight_const_mul_le w _ _).trans
    by_cases h : w i.castSucc ≤ d
    · have hp := (weightedTotalDegree_pderiv_le_sub w i.castSucc P).trans
        (Nat.sub_le_sub_right hP (w i.castSucc))
      have he := hshift i
      exact (weightedTotalDegree_mul_le _ _ _).trans
        ((Nat.add_le_add (weight_X_le w _) hp).trans (by omega))
    · rw [pderiv_zero_of_weight_lt w _ P (hP.trans_lt (Nat.lt_of_not_ge h)), mul_zero,
        weightedTotalDegree_zero]
      exact Nat.zero_le _

private theorem flow_bound (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g P : Row 4} {B d : ℕ} (hΔ : Δ ≤ B)
    (hg : W w g ≤ B) (hP : W w P ≤ d) :
    W w (flowNumerator g P) ≤ d + 2 * B := by
  have hsep (F : Row 4) : W w (separant F) ≤ W w F :=
    weightedTotalDegree_pderiv_le w 3 F
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  apply Submodule.sub_mem
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    have h := Nat.add_le_add ((hsep g).trans hg) (partialFlow_bound w Δ hshift P hP)
    exact (weightedTotalDegree_mul_le _ _ _).trans (h.trans (by omega))
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    have h := Nat.add_le_add (partialFlow_bound w Δ hshift g hg) ((hsep P).trans hP)
    exact (weightedTotalDegree_mul_le _ _ _).trans (h.trans (by omega))

private theorem tangent_weight (w : Fin 4 → ℕ) (Δ : ℕ)
    (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ)
    {g P : Row 4} {B d : ℕ} (hΔ : Δ ≤ B)
    (hg : W w g ≤ B) (hP : W w P ≤ d) (n : ℕ) :
    W w (tangentCut g P n) ≤ d + (2 * n) * B := by
  induction n with
  | zero => simpa [tangentCut] using hP
  | succ n ih =>
    rw [tangentCut, Function.iterate_succ_apply']
    change W w (flowNumerator g (tangentCut g P n)) ≤ _
    simpa only [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.add_assoc] using
      flow_bound w Δ hshift hΔ hg ih

theorem tangent_box {g P : Row 4} {a b : Shape} (hb : 0 < b.t) (hj : 0 < b.j)
    (hg : InBox (shape g) b) (hP : InBox (shape P) a) (n : ℕ) :
    InBox (shape (tangentCut g P n)) (a.plus (b.scale (2 * n))) := by
  have h₁ : W 1 g ≤ b.b := by simpa only [shape, weightedTotalDegree_one] using hg.1
  have h₂ : W Fin.val g ≤ b.j := by simpa only [shape, indexDegree_eq] using hg.2.1
  let w : Fin 4 → ℕ := Pi.single 3 1
  have h₃ : W w g ≤ b.t := by simpa only [w, shape, weightedTotalDegree_piSingle] using hg.2.2
  have hp₁ : W 1 P ≤ a.b := by simpa only [shape, weightedTotalDegree_one] using hP.1
  have hp₂ : W Fin.val P ≤ a.j := by simpa only [shape, indexDegree_eq] using hP.2.1
  have hp₃ : W w P ≤ a.t := by simpa only [w, shape, weightedTotalDegree_piSingle] using hP.2.2
  have hs₁ : ∀ i : Fin 3, (1 : Fin 4 → ℕ) i.succ ≤ (1 : Fin 4 → ℕ) i.castSucc + 0 := by
    intro i
    change (1 : ℕ) ≤ 1
    exact le_rfl
  have hs₂ : ∀ i : Fin 3, i.succ.val ≤ i.castSucc.val + 1 := fun _ => le_rfl
  have hs₃ : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + 1 := by
    intro i
    fin_cases i <;> decide
  refine ⟨?_, ?_, ?_⟩
  · simpa only [shape, Shape.plus, Shape.scale, weightedTotalDegree_one, Nat.mul_comm] using
      tangent_weight 1 0 hs₁ (Nat.zero_le _) h₁ hp₁ n
  · simpa only [shape, Shape.plus, Shape.scale, indexDegree_eq, Nat.mul_comm] using
      tangent_weight Fin.val 1 hs₂ hj h₂ hp₂ n
  · simpa only [w, shape, Shape.plus, Shape.scale, weightedTotalDegree_piSingle, Nat.mul_comm] using
      tangent_weight w 1 hs₃ hb h₃ hp₃ n

theorem anchor_fits (f : Row 4) : InBox (shape f) (anchorBox f) :=
  ⟨le_max_left _ _, le_rfl, le_rfl⟩

theorem derivative_fits (f : Row 4) (r : ℕ) :
    InBox (shape ((separant^[r]) f)) (anchorBox f) := by
  have d := derivative_in_box f r
  have a := anchor_fits f
  exact ⟨d.1.trans a.1, d.2.1.trans a.2.1, d.2.2.trans a.2.2⟩

theorem derivative_proper {f : Row 4} (hf : SmallFactor f) (j : ℕ)
    (hj : 0 < j) (hg : (separant^[j]) f ≠ 0) : ¬ f ∣ (separant^[j]) f := by
  rintro ⟨q, hq⟩
  have hq0 : q ≠ 0 := by
    intro hz
    exact hg (by rw [hq, hz, mul_zero])
  have hd := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.1.ne_zero hq0
  have h := derivative_degree f j
  have ht : 0 < f.degreeOf 3 := hf.2.1
  change ((separant^[j]) f).degreeOf 3 ≤ f.degreeOf 3 - j at h
  rw [hq, hd] at h
  omega

end
end K1_13_6_1_3
end PackSource_K1_13_6_1_3Boxes

section PackSource_K1_13_6_1_3Leibniz
set_option autoImplicit true
namespace K1_13_6_1_3
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_6_1
open scoped BigOperators

@[simp] private theorem coeff_coefficientDerivative (P : Row 4) (m : Fin 4 →₀ ℕ) :
    (coefficientDerivative P).coeff m = derivative (P.coeff m) := by
  classical
  rw [coefficientDerivative, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]

private theorem coefficientDerivative_add (P Q : Row 4) :
    coefficientDerivative (P + Q) = coefficientDerivative P + coefficientDerivative Q := by
  ext m
  simp

private theorem coefficientDerivative_mul (P Q : Row 4) :
    coefficientDerivative (P * Q) = coefficientDerivative P * Q + P * coefficientDerivative Q := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_coefficientDerivative]
  change derivative ((P * Q).coeff m) =
    (coefficientDerivative P * Q).coeff m + (P * coefficientDerivative Q).coeff m
  simp only [coeff_coefficientDerivative, MvPolynomial.coeff_mul, map_sum, derivative_mul,
    Finset.sum_add_distrib]

private theorem partialFlow_add (P Q : Row 4) :
    partialFlow (P + Q) = partialFlow P + partialFlow Q := by
  simp only [partialFlow, coefficientDerivative_add, map_add, mul_add, Finset.sum_add_distrib]
  abel

private theorem partialFlow_mul (P Q : Row 4) :
    partialFlow (P * Q) = partialFlow P * Q + P * partialFlow Q := by
  let a : Fin 3 → Row 4 := fun i =>
    MvPolynomial.C (C ((i.val + 1 : ℕ) : Geom)) * MvPolynomial.X i.succ
  change coefficientDerivative (P * Q) +
      (∑ i : Fin 3, a i * MvPolynomial.pderiv i.castSucc (P * Q)) =
    partialFlow P * Q + P * partialFlow Q
  have hs : (∑ i : Fin 3, a i * MvPolynomial.pderiv i.castSucc (P * Q)) =
      (∑ i : Fin 3, a i * MvPolynomial.pderiv i.castSucc P) * Q +
        P * (∑ i : Fin 3, a i * MvPolynomial.pderiv i.castSucc Q) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [MvPolynomial.pderiv_mul]
    ring
  rw [coefficientDerivative_mul, hs]
  change _ = (coefficientDerivative P + (∑ i : Fin 3, a i * MvPolynomial.pderiv i.castSucc P)) * Q +
    P * (coefficientDerivative Q + (∑ i : Fin 3, a i * MvPolynomial.pderiv i.castSucc Q))
  ring

private def delta (g : Row 4) : Row 4 →+ Row 4 where
  toFun := flowNumerator g
  map_add' P Q := by
    simp only [flowNumerator, partialFlow_add, separant, map_add]
    ring
  map_zero' := by
    simp [flowNumerator, separant, partialFlow, coefficientDerivative]

private theorem delta_mul (g x y : Row 4) :
    delta g (x * y) = delta g x * y + x * delta g y := by
  change flowNumerator g (x * y) = flowNumerator g x * y + x * flowNumerator g y
  simp only [flowNumerator, partialFlow_mul, separant, MvPolynomial.pderiv_mul]
  ring

section Iterates
variable {R S : Type*} [CommRing R] [CommRing S]
variable (D : R →+ R) (ρ : R →+* S)
variable (hD : ∀ x y, D (x * y) = D x * y + x * D y)

private theorem iterate_map_add (n : ℕ) (x y : R) :
    (D^[n]) (x + y) = (D^[n]) x + (D^[n]) y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_add]

include hD

/-- Through order n, only the undifferentiated left factor contributes if
all lower derivatives of the right factor vanish in the residue ring. -/
private theorem iterate_mul_residue (n : ℕ) (x y : R)
    (hy : ∀ k < n, ρ ((D^[k]) y) = 0) :
    ρ ((D^[n]) (x * y)) = ρ x * ρ ((D^[n]) y) := by
  induction n generalizing x y with
  | zero => exact map_mul ρ _ _
  | succ n ih =>
    rw [Function.iterate_succ_apply _ _ (x * y), hD, iterate_map_add D, map_add]
    rw [ih (D x) y (fun k hk => hy k (Nat.lt_succ_of_lt hk)), hy n (Nat.lt_succ_self n), mul_zero, zero_add]
    have hy' : ∀ k < n, ρ ((D^[k]) (D y)) = 0 := by
      intro k hk
      exact hy (k + 1) (Nat.succ_lt_succ hk)
    simpa only [Function.iterate_succ_apply] using ih x (D y) hy'

private theorem derivative_pow_succ (t : R) (n : ℕ) :
    D (t ^ (n + 1)) = ((n + 1 : ℕ) : R) * D t * t ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ t (n + 1), hD, ih, pow_succ t n]
    push_cast
    ring

private theorem iterate_power_order (t : R) (ht : ρ t = 0) (n : ℕ) :
    (∀ k < n, ∀ a : R, ρ ((D^[k]) (a * t ^ n)) = 0) ∧
    ∀ a : R, ρ ((D^[n]) (a * t ^ n)) = ρ a * (n.factorial : S) * (ρ (D t)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep (a : R) :
        D (a * t ^ (n + 1)) =
          (D a * t + a * ((n + 1 : ℕ) : R) * D t) * t ^ n := by
      rw [hD, derivative_pow_succ D hD, pow_succ' t n]
      ring
    constructor
    · intro k hk a
      cases k with
      | zero => simp [map_mul, ht]
      | succ k =>
        rw [Function.iterate_succ_apply, hstep]
        exact ih.1 k (Nat.lt_of_succ_lt_succ hk) _
    · intro a
      rw [Function.iterate_succ_apply, hstep, ih.2]
      simp only [map_add, map_mul, ht, mul_zero, zero_add, map_natCast, Nat.factorial_succ,
        Nat.cast_mul, pow_succ]
      ring

end Iterates

/-- The polynomial normal form suffices for the DVR tangent test. No
derivation of the algebraic closure of the abscissa field is required. -/
theorem tangent_proper {g P : Row 4} {surface : Ideal GeoJets} (hp : surface.IsPrime) {v : ℕ}
    (hg : toGeneric g ∈ surface) (hi : ¬ Invariant g surface) (hv : v < K1.p)
    (hn : NormalForm g P surface v) :
    toGeneric (tangentCut g P v) ∉ surface := by
  classical
  let _ : surface.IsPrime := hp
  let ρ : Row 4 →+* GeoJets ⧸ surface := (Ideal.Quotient.mk surface).comp (MvPolynomial.map genericCoeffs)
  have hρ (x : Row 4) : ρ x = 0 ↔ toGeneric x ∈ surface := Ideal.Quotient.eq_zero_iff_mem
  let D := delta g
  have hD (x y : Row 4) : D (x * y) = D x * y + x * D y := delta_mul g x y
  have hDg : D g = 0 := by
    change flowNumerator g g = 0
    unfold flowNumerator
    ring
  obtain ⟨t, d, u, B, ht, hd, hu, hP, hgen⟩ := hn
  have ht0 := (hρ t).mpr ht
  have hg0 := (hρ g).mpr hg
  have hd0 := fun h => hd ((hρ d).mp h)
  have hu0 := fun h => hu ((hρ u).mp h)
  have hDt : ρ (D t) ≠ 0 := by
    intro htD
    apply hi
    intro a ha
    obtain ⟨e, C, W, he, hEq⟩ := hgen a ha
    have h := congrArg (fun x => ρ (D x)) hEq
    simp only [map_add, hD, map_mul, hDg, hg0, ht0, htD, (hρ a).mpr ha,
      mul_zero, zero_add, add_zero] at h
    exact (hρ _).mp ((mul_eq_zero.mp h).resolve_left (fun h => he ((hρ e).mp h)))
  have iter_g (k : ℕ) : ∀ b : Row 4, ρ ((D^[k]) (b * g)) = 0 := by
    induction k with
    | zero => intro b; simp only [Function.iterate_zero_apply, map_mul, hg0, mul_zero]
    | succ k ih =>
      intro b
      rw [Function.iterate_succ_apply, hD, hDg, mul_zero, add_zero]
      exact ih _
  have iter_eq (k : ℕ) : ρ ((D^[k]) (d * P)) = ρ ((D^[k]) (u * t ^ v)) := by
    have h := congrArg (fun x => ρ ((D^[k]) x)) hP
    simpa only [iterate_map_add D, map_add, iter_g, zero_add] using h
  have hpow := iterate_power_order D ρ hD t ht0 v
  have hlower : ∀ k < v, ρ ((D^[k]) P) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have h := iterate_mul_residue D ρ hD k d P (fun j hj => ih j hj (hj.trans hk))
      rw [iter_eq, hpow.1 k hk u] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hd0
  have htop := iterate_mul_residue D ρ hD v d P hlower
  rw [iter_eq, hpow.2 u] at htop
  let ψ : Geom →+* GeoJets ⧸ surface := ρ.comp (MvPolynomial.C.comp Polynomial.C)
  have hfact : (v.factorial : GeoJets ⧸ surface) ≠ 0 := by
    intro h
    apply K1_13_7_1.factorial_cast_ne_zero hv
    apply ψ.injective
    simpa only [map_natCast, map_zero] using h
  intro hz
  have hzero : ρ ((D^[v]) P) = 0 := (hρ _).mpr hz
  rw [hzero, mul_zero] at htop
  exact (mul_ne_zero (mul_ne_zero hu0 hfact) (pow_ne_zero _ hDt)) htop

end
end K1_13_6_1_3
end PackSource_K1_13_6_1_3Leibniz

section PackSource_K1_13_6_1_3Split
set_option autoImplicit true
namespace K1_13_6_1_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_1

/-- A proper auxiliary pair vanishing on an original surface component
has that same component, with its ordinary Bézout local-length bound. -/
def c1 : Prop :=
  ∀ f P Q surface, IsRelPrime (toGeneric f) (toGeneric P) →
    (intersectionIdeal f Q).IsMinimalPrime surface → toGeneric P ∈ surface →
    ∃ (hZ : (intersectionIdeal f P).IsMinimalPrime surface) (w : ℕ),
      0 < w ∧ w ≤ (shape f).b * (shape P).b ∧
        cycleLength (intersectionIdeal f P) surface hZ.isPrime = (w : ℕ∞)

/-- The contracted smooth hypersurface chart is a DVR at the surface
prime. Its local quotient length determines the exact order. -/
def c2 : Prop :=
  ∀ g P surface (hZ : (intersectionIdeal g P).IsMinimalPrime surface) (v : ℕ),
    IsRelPrime (toGeneric g) (toGeneric P) → toGeneric (separant g) ∉ surface →
    0 < v → contractedLength g P surface hZ.isPrime = (v : ℕ∞) →
    NormalForm g P surface v

/-- Below the characteristic the geometric local length agrees with
the contracted local length over the rational abscissa field. -/
def c3 : Prop :=
  ∀ g P surface (hZ : (intersectionIdeal g P).IsMinimalPrime surface) (v : ℕ),
    cycleLength (intersectionIdeal g P) surface hZ.isPrime = (v : ℕ∞) →
    v < K1.p → contractedLength g P surface hZ.isPrime = (v : ℕ∞)

private theorem intersection_comm (g P : Row 4) : intersectionIdeal g P = intersectionIdeal P g := by
  unfold intersectionIdeal
  rw [Set.pair_comm]

private theorem chart_cut (h2 : c2) (h3 : c3)
    {g P : Row 4} {surface : Ideal GeoJets} (hZ : (intersectionIdeal g P).IsMinimalPrime surface)
    (hrel : IsRelPrime (toGeneric g) (toGeneric P)) (hsep : toGeneric (separant g) ∉ surface)
    (hi : ¬ Invariant g surface) {v : ℕ} (hv : 0 < v) (hchar : v < K1.p)
    (hlen : cycleLength (intersectionIdeal g P) surface hZ.isPrime = (v : ℕ∞)) :
    toGeneric (tangentCut g P v) ∉ surface := by
  have hg : toGeneric g ∈ surface := hZ.le (Ideal.subset_span (Set.mem_insert _ _))
  have hlen' := h3 g P surface hZ v hlen hchar
  have hn := h2 g P surface hZ v hrel hsep hv hlen'
  exact tangent_proper hZ.isPrime hg hi hchar hn

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13_6_1.c3 := by
  intro f Q surface hZ v r hf hproper hQbox hv hvmax hlen hr hi
  let g := (separant^[r]) f
  have hsep : toGeneric (separant g) ∉ surface := hr.2.2
  have hgt : toGeneric g ∈ surface := hr.2.1 r le_rfl
  have hAnchor := anchor_fits f
  have hGbox := derivative_fits f r
  have ht : 0 < (anchorBox f).t := hf.2.1
  have hj : 0 < (anchorBox f).j :=
    (by omega : 0 < 3 * (anchorBox f).t).trans_le (K1_13_7_1.shape_chamber f).2
  have hfb : (shape f).b ≤ 120 := hf.2.2.1.1
  by_cases hr0 : r = 0
  · subst r
    have hvChar : v < K1.p :=
      (hvmax.trans (Nat.mul_le_mul_right _ hfb)).trans_lt (by decide)
    exact Or.inl ⟨rfl, chart_cut h2 h3 hZ
        (K1_13_7_1.proper_generic f Q hf.1 hproper) hsep hi hv hvChar hlen,
      tangent_box ht hj hAnchor hQbox v⟩
  · have hrPos : 0 < r := Nat.pos_of_ne_zero hr0
    have hg0 : g ≠ 0 := by
      intro he
      exact hsep (by simp [he, separant, toGeneric])
    have hgProper := derivative_proper hf r hrPos hg0
    have hgRel := K1_13_7_1.proper_generic f g hf.1 hgProper
    obtain ⟨hfg, w, hw, hwmax, hwlen⟩ := h1 f g Q surface hgRel hZ hgt
    have hgb : (shape g).b ≤ 120 := (K1_13_7_1.derivative_in_box f r).1.trans hfb
    have hwChar : w < K1.p :=
      (hwmax.trans (Nat.mul_le_mul hfb hgb)).trans_lt (by decide)
    have hgf : (intersectionIdeal g f).IsMinimalPrime surface := by
      rwa [intersection_comm g f]
    have hwlen' : cycleLength (intersectionIdeal g f) surface hgf.isPrime = (w : ℕ∞) := by
      simpa only [intersection_comm g f] using hwlen
    exact Or.inr ⟨hrPos, w, ⟨hgProper, hGbox, hw, hfg, hwlen⟩,
      chart_cut h2 h3 hgf hgRel.symm hsep hi hw hwChar hwlen',
      tangent_box ht hj hGbox hAnchor w⟩

end
end K1_13_6_1_3
end PackSource_K1_13_6_1_3Split

section PackSource_K1_13_6_1_3_3Aux1
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_3_3

noncomputable section

open IsLocalRing

/-- Colength at a prime of an ambient ring. -/
abbrev localLength {R : Type*} [CommRing R] (q : Ideal R) [q.IsPrime] (J : Ideal R) : ℕ∞ :=
  Module.length (Localization.AtPrime q)
    (Localization.AtPrime q ⧸ J.map (algebraMap R (Localization.AtPrime q)))

section Length

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (Q : Ideal S) [Q.IsPrime]

theorem localLength_pos {J : Ideal S} (hJ : J ≤ Q) : 0 < localLength Q J := by
  apply Module.length_pos_iff.mpr
  apply Ideal.Quotient.nontrivial_iff.mpr
  exact ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top
    ((Ideal.map_mono hJ).trans_eq Localization.AtPrime.map_eq_maximalIdeal)

theorem localLength_eq_one_iff {J : Ideal S} :
    localLength Q J = 1 ↔
      J.map (algebraMap S (Localization.AtPrime Q)) = maximalIdeal (Localization.AtPrime Q) := by
  rw [localLength, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff]

theorem localLength_mono {I J : Ideal S} (h : I ≤ J) :
    localLength Q J ≤ localLength Q I := by
  simp only [localLength, Module.length_quotient]
  exact Order.coheight_anti (Ideal.map_mono h)

/-- Flat base change multiplies the local colength by the colength of the local residue fibre. -/
theorem localLength_map [Module.Flat R S] (J : Ideal R) :
    localLength Q (J.map (algebraMap R S)) =
      localLength (Q.comap (algebraMap R S)) J *
        localLength Q ((Q.comap (algebraMap R S)).map (algebraMap R S)) := by
  let q := Q.comap (algebraMap R S)
  let : q.IsPrime := Ideal.comap_isPrime _ _
  let : Q.LiesOver q := ⟨rfl⟩
  let A := Localization.AtPrime q
  let B := Localization.AtPrime Q
  let : Algebra A B := Localization.AtPrime.algebraOfLiesOver q Q
  have : IsLocalHom (algebraMap A B) := by
    change IsLocalHom (Localization.localRingHom q Q (algebraMap R S) rfl)
    infer_instance
  have hmap (I : Ideal R) :
      (I.map (algebraMap R A)).map (algebraMap A B) =
        (I.map (algebraMap R S)).map (algebraMap S B) := by
    rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq R A B,
      ← IsScalarTower.algebraMap_eq R S B]
  let I := J.map (algebraMap R A)
  change Module.length B (B ⧸ (J.map (algebraMap R S)).map (algebraMap S B)) =
    Module.length A (A ⧸ I) *
      Module.length B (B ⧸ (q.map (algebraMap R S)).map (algebraMap S B))
  rw [← hmap, ← hmap, Localization.AtPrime.map_eq_maximalIdeal]
  exact ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq).trans
    (IsLocalRing.length_baseChange A B (A ⧸ I))

end Length

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem polynomial_flat {k l σ : Type*} [Field k] [Field l] [Algebra k l] :
    Module.Flat (MvPolynomial σ k) (MvPolynomial σ l) := by
  have h : Algebra.IsPushout k (MvPolynomial σ k) l (MvPolynomial σ l) := inferInstance
  exact Module.Flat.isBaseChange k (MvPolynomial σ k) l (MvPolynomial σ l) h.out

/-- A flat local base change cannot decrease the colength. -/
theorem localLength_le_map {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (Q : Ideal S) [Q.IsPrime] (J : Ideal R) :
    localLength (Q.comap (algebraMap R S)) J ≤ localLength Q (J.map (algebraMap R S)) := by
  rw [localLength_map]
  exact ENat.self_le_mul_right _ (localLength_pos Q (Ideal.map_le_iff_le_comap.mpr le_rfl)).ne'

end

end K1_13_6_1_3_3
end PackSource_K1_13_6_1_3_3Aux1

section PackSource_K1_13_6_1_3_3Aux2
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_3_3

noncomputable section

open IsLocalRing Algebra
open scoped TensorProduct

attribute [local instance] MvPolynomial.algebraMvPolynomial

section FiniteScalarExtension

variable {k l σ : Type*} [Field k] [Field l] [Algebra k l] [FiniteDimensional k l]
variable (Q : Ideal (MvPolynomial σ l)) [Q.IsPrime]

/-- The local fibre of a finite separable change of coefficients has length one. -/
theorem separable_fibre [Algebra.IsSeparable k l] :
    localLength Q ((Q.comap (algebraMap (MvPolynomial σ k) _)).map
      (algebraMap (MvPolynomial σ k) _)) = 1 := by
  let R := MvPolynomial σ k
  let S := MvPolynomial σ l
  let q := Q.comap (algebraMap R S)
  let : q.IsPrime := Ideal.comap_isPrime _ _
  let : Q.LiesOver q := ⟨rfl⟩
  let A := Localization.AtPrime q
  let B := Localization.AtPrime Q
  let : Algebra A B := Localization.AtPrime.algebraOfLiesOver q Q
  let : IsLocalHom (algebraMap A B) := by
    change IsLocalHom (Localization.localRingHom q Q (algebraMap R S) rfl)
    infer_instance
  let e := IsPushout.equiv k R l S
  have : Module.Finite R S := Module.Finite.of_surjective e.toLinearMap e.surjective
  have : FormallyUnramified k l := FormallyUnramified.of_isSeparable k l
  have : FormallyUnramified R S := FormallyUnramified.of_equiv e
  have : FormallyUnramified R B := by
    change FormallyUnramified R (Localization Q.primeCompl)
    infer_instance
  have : FormallyUnramified A B := FormallyUnramified.of_restrictScalars R A B
  have : EssFiniteType R B := by
    change EssFiniteType R (Localization Q.primeCompl)
    infer_instance
  have : EssFiniteType A B := EssFiniteType.of_comp R A B
  apply (localLength_eq_one_iff Q).mpr
  change (q.map (algebraMap R S)).map (algebraMap S B) = maximalIdeal B
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S B,
    IsScalarTower.algebraMap_eq R A B, ← Ideal.map_map,
    Localization.AtPrime.map_eq_maximalIdeal]
  exact FormallyUnramified.map_maximalIdeal

end FiniteScalarExtension

private theorem selfLength_congr {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  rw [Module.length_eq_coheight, Module.length_eq_coheight]
  change Order.coheight (⊥ : Ideal R) = Order.coheight (⊥ : Ideal S)
  simpa using Order.coheight_orderIso e.idealComapOrderIso (⊥ : Ideal S)

section PurelyInseparable

variable {k l F : Type*} [Field k] [Field l] [Field F] [Algebra k l] [Algebra k F]
variable [IsPurelyInseparable k l]

private theorem tensor_selfLength_eq_one [FiniteDimensional k l]
    (p : ℕ) [ExpChar k p] (hp : p.Prime)
    (h : Module.length (F ⊗[k] l) (F ⊗[k] l) < (p : ℕ∞)) :
    Module.length (F ⊗[k] l) (F ⊗[k] l) = 1 := by
  let T := F ⊗[k] l
  have : Subsingleton (PrimeSpectrum T) :=
    (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k l F).injective.subsingleton
  have : Subsingleton (MaximalSpectrum T) := MaximalSpectrum.toPrimeSpectrum_injective.subsingleton
  have : IsLocalRing T := IsLocalRing.of_singleton_maximalSpectrum
  have : IsLocalHom (algebraMap F T) := ⟨fun x hx ↦ isUnit_iff_ne_zero.mpr fun hz ↦
    by simp [hz] at hx⟩
  obtain ⟨a, ha⟩ := IsPurelyInseparable.finrank_eq_pow k l p
  have hd := IsLocalRing.length_restrictScalars F T T
  rw [Module.length_eq_finrank F T, Module.finrank_baseChange, ha] at hd
  have hdvd : (Module.length T T).toNat ∣ p ^ a := by
    refine ⟨(Module.length (ResidueField F) (ResidueField T)).toNat, ?_⟩
    simpa only [ENat.toNat_mul, ENat.toNat_natCast] using congrArg ENat.toNat hd
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  cases n with
  | zero => exact (ENat.toNat_eq_iff (by decide : (1 : ℕ) ≠ 0)).mp (by simpa using hn)
  | succ n =>
    have hle : p ≤ p ^ (n + 1) := Nat.le_pow (Nat.succ_pos n)
    have hlt : (Module.length T T).toNat < p := by
      exact ENat.natCast_lt_natCast.mp ((ENat.natCast_toNat_le_self _).trans_lt h)
    omega

end PurelyInseparable

section PolynomialFibre

variable {k l σ : Type*} [Field k] [Field l] [Algebra k l]
variable [IsPurelyInseparable k l]
variable (q : Ideal (MvPolynomial σ k)) [q.IsPrime]
variable (Q : Ideal (MvPolynomial σ l)) [Q.IsPrime] [Q.LiesOver q]

private abbrev fibreInclusion {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal R) [q.IsPrime] : S →+* q.Fiber S :=
  (Algebra.TensorProduct.includeRight (R := R) (A := q.ResidueField) (B := S)).toRingHom

set_option backward.isDefEq.respectTransparency false in
private theorem fibre_at_length {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal R) [q.IsPrime] (r : Ideal (q.Fiber S)) [r.IsPrime] :
    localLength (r.comap (fibreInclusion (S := S) q)) (q.map (algebraMap R S)) =
      Module.length (Localization.AtPrime r) (Localization.AtPrime r) := by
  let Q := r.comap (fibreInclusion (S := S) q)
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  let B := Localization.AtPrime Q
  let I := (q.map (algebraMap R S)).map (algebraMap S B)
  change Module.length B (B ⧸ I) = _
  have hsurj : Function.Surjective (algebraMap B (B ⧸ I)) :=
    Ideal.Quotient.mk_surjective
  have hquot := Module.length_eq_of_surjective (S := B) (R := B ⧸ I) (M := B ⧸ I) hsurj
  let e : Localization.AtPrime r ≃+* (B ⧸ I) :=
    (Ideal.Fiber.algEquivAux₂ (S := S) q r).toRingEquiv
  have he := selfLength_congr (R := B ⧸ I) (S := Localization.AtPrime r) e.symm
  exact hquot.trans he

set_option backward.isDefEq.respectTransparency false in
/-- A purely inseparable residue fibre is already local. -/
private theorem purely_inseparable_fibre_length :
    localLength Q (q.map (algebraMap (MvPolynomial σ k) (MvPolynomial σ l))) =
      Module.length (q.ResidueField ⊗[k] l) (q.ResidueField ⊗[k] l) := by
  let R := MvPolynomial σ k
  let S := MvPolynomial σ l
  let F := q.ResidueField
  let T := F ⊗[k] l
  let e₁ : q.Fiber S ≃ₐ[F] T :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F)
      ((IsPushout.equiv k R l S).symm)).trans
        (Algebra.TensorProduct.cancelBaseChange k R F F l)
  obtain ⟨z, hz⟩ := (PrimeSpectrum.primesOverOrderIsoFiber R S q).symm.surjective
    ⟨Q, inferInstance, inferInstance⟩
  let r := z.asIdeal
  have : r.IsPrime := z.isPrime
  have hQ : r.comap (fibreInclusion (S := S) q) = Q :=
    congrArg (fun w : q.primesOver S ↦ w.1) hz
  have hu : r.primeCompl ≤ IsUnit.submonoid (q.Fiber S) := by
    intro x hx
    obtain ⟨n, hn, y, hy⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct (e₁ x)
    have hxy : x ^ n = algebraMap F (q.Fiber S) y := by
      apply e₁.injective
      rw [map_pow, e₁.commutes, hy]
    have hy0 : y ≠ 0 := by
      intro hz
      apply hx
      exact (‹r.IsPrime›.pow_mem_iff_mem _ hn).mp (by simp [hxy, hz])
    change IsUnit x
    rw [← isUnit_pow_iff hn.ne', hxy]
    exact (isUnit_iff_ne_zero.mpr hy0).map (algebraMap F (q.Fiber S))
  let e₂ := IsLocalization.atUnits (q.Fiber S) r.primeCompl (S := Localization.AtPrime r) hu
  subst Q
  have h₁ := fibre_at_length (R := R) (S := S) q r
  let e : Localization.AtPrime r ≃+* T := e₂.symm.toRingEquiv.trans e₁.toRingEquiv
  have h₂ := selfLength_congr (R := Localization.AtPrime r) (S := T) e
  exact h₁.trans h₂

/-- A finite purely inseparable fibre of length less than the characteristic has length one. -/
theorem purely_inseparable_fibre [FiniteDimensional k l] (p : ℕ) [ExpChar k p] (hp : p.Prime)
    (h : localLength Q (q.map (algebraMap (MvPolynomial σ k) _)) < (p : ℕ∞)) :
    localLength Q (q.map (algebraMap (MvPolynomial σ k) _)) = 1 := by
  rw [purely_inseparable_fibre_length q Q] at h ⊢
  exact tensor_selfLength_eq_one p hp h

end PolynomialFibre

end

end K1_13_6_1_3_3
end PackSource_K1_13_6_1_3_3Aux2

section PackSource_K1_13_6_1_3_3Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_3_3

noncomputable section

open IsLocalRing
open K1_13 K1_13_6 K1_13_6_1_3

attribute [local instance] MvPolynomial.algebraMvPolynomial

private theorem polynomial_tower {k E l σ : Type*} [Field k] [Field E] [Field l]
    [Algebra k E] [Algebra k l] [Algebra E l] [IsScalarTower k E l] :
    IsScalarTower (MvPolynomial σ k) (MvPolynomial σ E) (MvPolynomial σ l) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  simp only [MvPolynomial.algebraMap_def]
  change MvPolynomial.map (algebraMap k l) x =
    MvPolynomial.map (algebraMap E l) (MvPolynomial.map (algebraMap k E) x)
  rw [MvPolynomial.map_map, IsScalarTower.algebraMap_eq k E l]

private theorem finite_fibre {k l σ : Type*} [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] (Q : Ideal (MvPolynomial σ l)) [Q.IsPrime]
    (p : ℕ) [ExpChar k p] (hp : p.Prime)
    (h : localLength Q ((Q.comap (algebraMap (MvPolynomial σ k) _)).map
      (algebraMap (MvPolynomial σ k) _)) < (p : ℕ∞)) :
    localLength Q ((Q.comap (algebraMap (MvPolynomial σ k) _)).map
      (algebraMap (MvPolynomial σ k) _)) = 1 := by
  let E := separableClosure k l
  let R := MvPolynomial σ k
  let T := MvPolynomial σ E
  let S := MvPolynomial σ l
  let q := Q.comap (algebraMap T S)
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : Q.LiesOver q := ⟨rfl⟩
  have : Module.Flat T S := polynomial_flat
  have : IsScalarTower R T S := polynomial_tower
  have hmap : ((q.comap (algebraMap R T)).map (algebraMap R T)).map (algebraMap T S) =
      (Q.comap (algebraMap R S)).map (algebraMap R S) := by
    simp only [q, Ideal.map_map, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq R T S]
  rw [← hmap, localLength_map, separable_fibre (k := k) q, one_mul] at h ⊢
  exact purely_inseparable_fibre q Q p hp h

private theorem lift_polynomial {k l σ : Type*} [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] (x : MvPolynomial σ l) :
    ∃ (E : IntermediateField k l), FiniteDimensional k E ∧
      ∃ y : MvPolynomial σ E, algebraMap (MvPolynomial σ E) (MvPolynomial σ l) y = x := by
  classical
  let s := x.support.image x.coeff
  let E := IntermediateField.adjoin k (s : Set l)
  have : FiniteDimensional k E := IntermediateField.finiteDimensional_adjoin
    (fun z _ ↦ Algebra.IsIntegral.isIntegral (R := k) z)
  have hcoeff (m : σ →₀ ℕ) (hm : m ∈ x.support) : x.coeff m ∈ E :=
    IntermediateField.subset_adjoin k _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  let y : MvPolynomial σ E :=
    ∑ m ∈ x.support.attach, MvPolynomial.monomial m.1 ⟨x.coeff m.1, hcoeff m.1 m.2⟩
  refine ⟨E, inferInstance, y, ?_⟩
  simp only [y, map_sum, MvPolynomial.algebraMap_def, MvPolynomial.map_monomial,
    IntermediateField.algebraMap_apply]
  rw [Finset.sum_attach x.support (fun m ↦ MvPolynomial.monomial m (x.coeff m))]
  exact (MvPolynomial.as_sum x).symm

/-- A local residue fibre of algebraic scalar extension has length one when
its length is below the positive characteristic. Each element of the geometric
prime is represented over a finite coefficient extension. -/
theorem algebraic_fibre {k l σ : Type*} [Field k] [Field l] [Algebra k l]
    [Algebra.IsAlgebraic k l] (Q : Ideal (MvPolynomial σ l)) [Q.IsPrime]
    (p : ℕ) [ExpChar k p] (hp : p.Prime)
    (h : localLength Q ((Q.comap (algebraMap (MvPolynomial σ k) _)).map
      (algebraMap (MvPolynomial σ k) _)) < (p : ℕ∞)) :
    localLength Q ((Q.comap (algebraMap (MvPolynomial σ k) _)).map
      (algebraMap (MvPolynomial σ k) _)) = 1 := by
  let R := MvPolynomial σ k
  let S := MvPolynomial σ l
  let J := (Q.comap (algebraMap R S)).map (algebraMap R S)
  let B := Localization.AtPrime Q
  apply (localLength_eq_one_iff Q).mpr
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  change J.map (algebraMap S B) = Q.map (algebraMap S B)
  refine le_antisymm (Ideal.map_mono Ideal.map_comap_le) ?_
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  obtain ⟨E, hE, y, hy⟩ := lift_polynomial (k := k) x
  let T := MvPolynomial σ E
  let q := Q.comap (algebraMap T S)
  let J₀ := (q.comap (algebraMap R T)).map (algebraMap R T)
  let A := Localization.AtPrime q
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : Q.LiesOver q := ⟨rfl⟩
  let : Algebra A B := Localization.AtPrime.algebraOfLiesOver q Q
  have : IsScalarTower R T S := polynomial_tower
  have : Module.Flat T S := polynomial_flat
  have hmap : J₀.map (algebraMap T S) = J := by
    simp only [J₀, J, q, Ideal.map_map, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq R T S]
  have h₀ : localLength q J₀ < (p : ℕ∞) := (localLength_le_map Q J₀).trans_lt (hmap ▸ h)
  have h₁ := (localLength_eq_one_iff q).mp (finite_fibre (k := k) q p hp h₀)
  have hyq : y ∈ q := by
    change algebraMap T S y ∈ Q
    exact hy.symm ▸ hx
  have hymem : algebraMap T A y ∈ J₀.map (algebraMap T A) := by
    rw [h₁, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hyq
  have hmem := Ideal.mem_map_of_mem (algebraMap A B) hymem
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq T A B,
    IsScalarTower.algebraMap_eq T S B, ← Ideal.map_map, hmap] at hmem
  change algebraMap S B x ∈ J.map (algebraMap S B)
  rw [← hy]
  change (algebraMap S B) ((algebraMap T S) y) ∈ J.map (algebraMap S B)
  rw [← IsScalarTower.algebraMap_apply T S B]
  rwa [← IsScalarTower.algebraMap_apply T A B] at hmem

/-- Below the characteristic, the rational and geometric local lengths coincide. -/
theorem proof : K1_13_6_1_3.c3 := by
  intro g P surface hZ v hlen hv
  have : surface.IsPrime := hZ.isPrime
  change localLength surface (intersectionIdeal g P) = (v : ℕ∞) at hlen
  let q := contractedPrime surface
  have : q.IsPrime := Ideal.comap_isPrime _ _
  let J : Ideal RationalJets := Ideal.span {toRational g, toRational P}
  let f := algebraMap RationalJets GeoJets
  have hfg (U : Row 4) : f (toRational U) = toGeneric U := by
    change MvPolynomial.map (algebraMap GenericField GeoField) (toRational U) = _
    simp only [toRational, toGeneric, genericCoeffs, MvPolynomial.map_map]
  have hJ : J.map f = intersectionIdeal g P := by
    simp only [J, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hfg, intersectionIdeal]
  have hsmall : localLength surface (q.map f) < (K1.p : ℕ∞) := by
    have hle : (intersectionIdeal g P) ≤ q.map f := by
      rw [← hJ]
      apply Ideal.map_mono
      exact Ideal.map_le_iff_le_comap.mp (hJ.symm ▸ hZ.le)
    refine (localLength_mono surface hle).trans_lt ?_
    rw [hlen]
    exact ENat.natCast_lt_natCast.mpr hv
  have hp := CharP.char_is_prime_of_two_le K1.K K1.p (by decide)
  have : CharP Geom K1.p := charP_of_injective_ringHom embed.injective K1.p
  have : CharP (Polynomial Geom) K1.p :=
    charP_of_injective_ringHom Polynomial.C_injective K1.p
  have : CharP GenericField K1.p :=
    charP_of_injective_ringHom (IsFractionRing.injective (K := GenericField) (Polynomial Geom)) K1.p
  have : ExpChar GenericField K1.p := ExpChar.prime hp
  have hfib : localLength surface (q.map f) = 1 :=
    algebraic_fibre (k := GenericField) surface K1.p hp hsmall
  have : Module.Flat RationalJets GeoJets := polynomial_flat
  have hbase := localLength_map surface J
  change localLength surface (J.map f) = localLength q J * localLength surface (q.map f) at hbase
  rw [hJ, hfib, mul_one] at hbase
  change Order.coheight (J.map (algebraMap RationalJets (Localization.AtPrime q))) = _
  simpa only [localLength, Module.length_quotient] using hbase.symm.trans hlen

end

end K1_13_6_1_3_3
end PackSource_K1_13_6_1_3_3Proof

section PackSource_K1_13_6_1_3_2Proof
set_option autoImplicit true
namespace K1_13_6_1_3_2

noncomputable section

open K1_13 K1_13_6 K1_13_6_1_3 IsLocalRing

attribute [local instance] MvPolynomial.algebraMvPolynomial

private theorem toGeneric_eq (a : Row 4) :
    MvPolynomial.map (algebraMap GenericField GeoField) (toRational a) = toGeneric a := by
  rw [toRational, toGeneric, genericCoeffs, MvPolynomial.map_map]

section Chart

variable (surface : Ideal GeoJets) [surface.IsPrime]

private abbrev A := Localization.AtPrime (contractedPrime surface)
private abbrev sourcePrime := (contractedPrime surface).comap (algebraMap (Row 4) RationalJets)

/-- The chart is also the localization of the source rows at the contracted prime. -/
local instance : IsLocalization.AtPrime (A surface) (sourcePrime surface) :=
  IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    ((nonZeroDivisors (Polynomial Geom)).map (MvPolynomial.C (σ := Fin 4))) (A surface)
    (contractedPrime surface)

private abbrev loc := algebraMap (Row 4) (A surface)

private theorem loc_eq_rational (a : Row 4) :
    loc surface a = algebraMap RationalJets (A surface) (toRational a) := rfl

omit [surface.IsPrime] in
private theorem source_mem (a : Row 4) : a ∈ sourcePrime surface ↔ toGeneric a ∈ surface := by
  change (MvPolynomial.map (algebraMap GenericField GeoField) (toRational a) ∈ surface) ↔ _
  rw [toGeneric_eq]

private theorem loc_mem (a : Row 4) : loc surface a ∈ maximalIdeal (A surface) ↔ toGeneric a ∈ surface :=
  (IsLocalization.AtPrime.to_map_mem_maximal_iff (A surface) (sourcePrime surface) a).trans (source_mem surface a)

private theorem loc_unit (a : Row 4) : IsUnit (loc surface a) ↔ toGeneric a ∉ surface :=
  (IsLocalization.AtPrime.isUnit_to_map_iff (A surface) (sourcePrime surface) a).trans (not_congr (source_mem surface a))

private theorem loc_numerator (x : A surface) :
    ∃ a d : Row 4, toGeneric d ∉ surface ∧ x * loc surface d = loc surface a := by
  obtain ⟨⟨a, d⟩, h⟩ := IsLocalization.surj (sourcePrime surface).primeCompl x
  exact ⟨a, d, (not_congr (source_mem surface d)).mp d.2, h⟩

private theorem clear_mem {J : Ideal (Row 4)} {a : Row 4} (ha : loc surface a ∈ J.map (loc surface)) :
    ∃ d : Row 4, toGeneric d ∉ surface ∧ d * a ∈ J := by
  obtain ⟨d, hd, hda⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (sourcePrime surface).primeCompl (A surface) J a).mp ha
  exact ⟨d, (not_congr (source_mem surface d)).mp hd, hda⟩

omit [surface.IsPrime] in
private theorem separant_mem_of_sq {a : Row 4} (ha : a ∈ sourcePrime surface ^ 2) :
    separant a ∈ sourcePrime surface := by
  rw [pow_two] at ha
  refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · rw [separant, MvPolynomial.pderiv_mul]
    exact (sourcePrime surface).add_mem ((sourcePrime surface).mul_mem_left _ hy)
      ((sourcePrime surface).mul_mem_right _ hx)
  · simpa only [separant, map_add] using (sourcePrime surface).add_mem hx hy

private theorem loc_not_sq {g : Row 4} (hg : toGeneric g ∈ surface)
    (hs : toGeneric (separant g) ∉ surface) :
    loc surface g ∉ maximalIdeal (A surface) ^ 2 := by
  intro h
  have hmap : (sourcePrime surface).map (loc surface) = maximalIdeal (A surface) := by
    rw [← IsLocalization.map_under (sourcePrime surface).primeCompl (A surface) (maximalIdeal (A surface)),
      IsLocalization.AtPrime.under_maximalIdeal (A surface) (sourcePrime surface)]
  rw [← hmap, ← Ideal.map_pow] at h
  obtain ⟨d, hd, hdg⟩ := clear_mem surface h
  have hder := separant_mem_of_sq surface hdg
  rw [separant, MvPolynomial.pderiv_mul] at hder
  have hother : MvPolynomial.pderiv 3 d * g ∈ sourcePrime surface :=
    (sourcePrime surface).mul_mem_left _ ((source_mem surface g).mpr hg)
  have hmul := ((sourcePrime surface).add_mem_iff_right hother).mp hder
  have hp : (sourcePrime surface).IsPrime := inferInstance
  exact (hp.mem_or_mem hmul).elim
    (fun h => hd ((source_mem surface d).mp h))
    (fun h => hs ((source_mem surface (separant g)).mp h))

private theorem loc_proper {g P : Row 4} (hg : toGeneric g ∈ surface)
    (hrel : IsRelPrime (toGeneric g) (toGeneric P)) :
    loc surface P ∉ Ideal.span {loc surface g} := by
  intro h
  have hm : (Ideal.span {g}).map (loc surface) = Ideal.span {loc surface g} := by
    rw [Ideal.map_span, Set.image_singleton]
  obtain ⟨d, hd, hdp⟩ := clear_mem surface (hm.symm ▸ h)
  have hdvd := map_dvd (MvPolynomial.map genericCoeffs) (Ideal.mem_span_singleton.mp hdp)
  rw [map_mul] at hdvd
  exact hd (surface.mem_of_dvd (hrel.dvd_of_dvd_mul_right hdvd) hg)

private theorem clear_order {g P : Row 4} {v : ℕ} {t' u' : A surface}
    (ht' : maximalIdeal (A surface) = Ideal.span {loc surface g, t'})
    (hu' : IsUnit u') (hP : loc surface P - u' * t' ^ v ∈ Ideal.span {loc surface g}) :
    NormalForm g P surface v := by
  obtain ⟨t, dt, hdt, ht⟩ := loc_numerator surface t'
  obtain ⟨u, du, hdu, hu⟩ := loc_numerator surface u'
  have ht_mem : t' ∈ maximalIdeal (A surface) := ht'.symm ▸ Ideal.subset_span (by simp)
  have htZ : toGeneric t ∈ surface := (loc_mem surface t).mp
    (ht ▸ (maximalIdeal (A surface)).mul_mem_right _ ht_mem)
  have huZ : toGeneric u ∉ surface := (loc_unit surface u).mp
    (hu ▸ hu'.mul ((loc_unit surface du).mpr hdu))
  let d := du * dt ^ v
  have hd : toGeneric d ∉ surface := (loc_unit surface d).mp (by
    change IsUnit (loc surface (du * dt ^ v))
    rw [map_mul, map_pow]
    exact ((loc_unit surface du).mpr hdu).mul (((loc_unit surface dt).mpr hdt).pow _))
  have hEq : loc surface (d * P - u * t ^ v) = loc surface d * (loc surface P - u' * t' ^ v) := by
    simp only [d, map_sub, map_mul, map_pow, ← ht, ← hu, mul_pow]
    ring
  have hmem : loc surface (d * P - u * t ^ v) ∈ (Ideal.span {g}).map (loc surface) := by
    rw [Ideal.map_span, Set.image_singleton, hEq]
    exact Ideal.mul_mem_left _ _ hP
  obtain ⟨s, hs, hsg⟩ := clear_mem surface hmem
  obtain ⟨B, hB⟩ := Ideal.mem_span_singleton'.mp hsg
  refine ⟨t, s * d, s * u, B, htZ, ?_, ?_, ?_, ?_⟩
  · exact (loc_unit surface _).mp (by rw [map_mul]; exact ((loc_unit surface s).mpr hs).mul ((loc_unit surface d).mpr hd))
  · exact (loc_unit surface _).mp (by rw [map_mul]; exact ((loc_unit surface s).mpr hs).mul ((loc_unit surface u).mpr huZ))
  · calc
      (s * d) * P = s * (d * P - u * t ^ v) + (s * u) * t ^ v := by ring
      _ = B * g + (s * u) * t ^ v := by rw [hB]
  · intro a ha
    have htm : maximalIdeal (A surface) = (Ideal.span {g, t}).map (loc surface) := by
      rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, ← ht, ht']
      simp only [Ideal.span_insert, Ideal.span_singleton_mul_right_unit ((loc_unit surface dt).mpr hdt)]
    obtain ⟨e, he, hea⟩ := clear_mem surface (htm ▸ (loc_mem surface a).mpr ha)
    obtain ⟨C, W, heq⟩ := Ideal.mem_span_pair.mp hea
    exact ⟨e, C, W, he, heq.symm⟩

end Chart

theorem proof : K1_13_6_1_3.c2 := by
  intro g P surface hZ v hrel hsep _ hlen
  have := hZ.isPrime
  have hg : toGeneric g ∈ surface := hZ.le (Ideal.subset_span (by simp))
  have hq : toGeneric P ∈ surface := hZ.le (Ideal.subset_span (by simp))
  have hlen' : Order.coheight (Ideal.span ({loc surface g, loc surface P} : Set (A surface))) = (v : ℕ∞) := by
    unfold contractedLength at hlen
    simpa only [loc_eq_rational, Ideal.map_span, Set.image_insert_eq, Set.image_singleton] using hlen
  have hreg : IsRegularLocalRing (A surface) :=
    IsRegularRing.isRegularLocalRing_localization (contractedPrime surface)
  have hufd : UniqueFactorizationMonoid (A surface) :=
    UniqueFactorizationMonoid.of_isLocalization (contractedPrime surface).primeCompl (A surface)
  have hdom : IsDomain (A surface) := inferInstance
  have hg' := (loc_mem surface g).mpr hg
  have hq' := (loc_mem surface P).mpr hq
  have hgsq := loc_not_sq surface (g := g) hg hsep
  have hqf := loc_proper surface (g := g) (P := P) hg hrel
  obtain ⟨t, u, ht, hu, hP⟩ := @local_order (A surface) inferInstance hdom hreg hufd
    (loc surface g) (loc surface P) v hg' hq' hgsq hqf hlen'
  exact clear_order surface (g := g) (P := P) (v := v) (t' := t) (u' := u) ht hu hP

end
end K1_13_6_1_3_2
end PackSource_K1_13_6_1_3_2Proof

section PackSource_K1_13_6_3_1_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_3_1_1

noncomputable section

open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_1 K1_13_6_1_3_3

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem proof : K1_13_6_3_1.c1 := by
  intro f Q P hz hlen
  have : P.IsPrime := hz.isPrime
  change localLength P (intersectionIdeal f Q) < (K1.p : ℕ∞) at hlen
  let J : Ideal SepJets := Ideal.span {rowToSep f, rowToSep Q}
  have hJ : J.map sepToGeo = intersectionIdeal f Q := by
    simp only [J, intersectionIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      sepToGeo_rowToSep]
  let const : K1.K →+* SepField :=
    (algebraMap GenericField SepField).comp
      ((algebraMap (Polynomial Geom) GenericField).comp (Polynomial.C.comp embed))
  have : CharP SepField K1.p := charP_of_injective_ringHom const.injective K1.p
  have hp := CharP.char_is_prime_of_two_le K1.K K1.p (by decide)
  have : ExpChar SepField K1.p := .prime hp
  have hle : intersectionIdeal f Q ≤ (P.comap sepToGeo).map sepToGeo := by
    rw [← hJ]
    exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mp (hJ.symm ▸ hz.le))
  have hsmall : localLength P ((P.comap sepToGeo).map sepToGeo) < (K1.p : ℕ∞) :=
    (localLength_mono P hle).trans_lt hlen
  have hone : localLength P ((P.comap sepToGeo).map sepToGeo) = 1 :=
    algebraic_fibre (k := SepField) P K1.p hp hsmall
  exact descent_of_local_equality (k := SepField) (E := GeoField) (R := SepJets) P
    ((localLength_eq_one_iff P).mp hone)

end
end K1_13_6_3_1_1
end PackSource_K1_13_6_3_1_1Proof

section PackSource_K1_13_6_1_5Aux1
set_option autoImplicit true
namespace K1_13_6_1_5
noncomputable section

open Polynomial K1 K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
open scoped BigOperators

private abbrev constants : Geom →+* GeoField := genericCoeffs.comp Polynomial.C
private abbrev center : GeoField := genericCoeffs Polynomial.X

def valueForm (x a : K) : AffineForm :=
  (-constants (embed a), fun i => (constants (embed x) - center) ^ i.val)

private theorem eval_at_center (S : Geom[X]) : (S.map constants).eval center = genericCoeffs S := by
  rw [Polynomial.eval_map]
  change Polynomial.eval₂RingHom constants center S = genericCoeffs S
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp [constants]
  · simp [center]

private theorem taylor_value (S : Geom[X]) (hS : S.natDegree < taylorLength) (x : Geom) :
    (∑ i : TaylorIndex, genericCoeffs (hasseDeriv i.val S) * (constants x - center) ^ i.val) =
      constants (S.eval x) := by
  let P := S.map constants
  have hdeg : (taylor center P).natDegree < taylorLength := by
    rw [natDegree_taylor]
    exact natDegree_map_le.trans_lt hS
  have hcoeff (i : ℕ) :
      (taylor center P).coeff i = genericCoeffs (hasseDeriv i S) := by
    rw [taylor_coeff]
    change (hasseDeriv i (S.map constants)).eval center = _
    rw [hasseDeriv_map, eval_at_center]
  have heval := (taylor center P).eval_eq_sum_range' hdeg (constants x - center)
  rw [← Fin.sum_univ_eq_sum_range] at heval
  simp only [hcoeff] at heval
  rw [taylor_eval_sub, show P.eval (constants x) = constants (S.eval x) from
    Polynomial.eval_map_apply constants x] at heval
  exact heval.symm

theorem value_cut_eval (T : TaylorChart) {S : K[X]}
    (hS : S.natDegree ≤ 133634) (hT : T.Recovers (extend S)) (x a : K) :
    evalGeneric (extend S) (T.pullback (valueForm x a)) = 0 ↔ S.eval x = a := by
  have hdeg : (extend S).natDegree < taylorLength :=
    natDegree_map_le.trans_lt (Nat.lt_succ_of_le hS)
  have hval := taylor_value (extend S) hdeg (embed x)
  rw [Polynomial.eval_map_apply] at hval
  have hsum :
      (∑ i : TaylorIndex, (constants (embed x) - center) ^ i.val *
        (evalGeneric (extend S) T.denom * genericCoeffs (hasseDeriv i.val (extend S)))) =
        evalGeneric (extend S) T.denom * constants (embed (S.eval x)) := by
    rw [← hval, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  unfold TaylorChart.pullback valueForm
  simp only [map_add, map_sum, map_mul, evalGeneric, MvPolynomial.eval_C]
  change (-constants (embed a)) * evalGeneric (extend S) T.denom +
      (∑ i : TaylorIndex, (constants (embed x) - center) ^ i.val *
        evalGeneric (extend S) (T.numerator i)) = 0 ↔ _
  simp only [hT.2, hsum]
  rw [show -constants (embed a) * evalGeneric (extend S) T.denom +
      evalGeneric (extend S) T.denom * constants (embed (S.eval x)) =
      evalGeneric (extend S) T.denom * (constants (embed (S.eval x)) - constants (embed a)) by ring,
    mul_eq_zero, or_iff_right hT.1, sub_eq_zero]
  exact (genericCoeffs_injective.comp Polynomial.C_injective).eq_iff.trans embed.injective.eq_iff

def markPoint (S : Geom[X]) : GeoPoint := fun i => genericCoeffs (jet S i)

theorem markPoint_injective : Function.Injective markPoint := by
  intro S T h
  have hzero := congrFun h (0 : Fin 4)
  simpa only [markPoint, jet, Fin.val_zero, hasseDeriv_zero', genericCoeffs_injective.eq_iff]
    using hzero

theorem coordinate_cut {C : Ideal GeoJets} (hp : C.IsPrime)
    (hdim : ringKrullDim (GeoJets ⧸ C) = 1) :
    ∃ (x : GeoPoint) (D : GeoJets), C ≤ RingHom.ker (MvPolynomial.eval x) ∧
      GeoFits D ⟨1, 3, 1⟩ ∧ D ∉ C ∧ MvPolynomial.eval x D = 0 := by
  classical
  obtain ⟨J, hJ, hCJ⟩ := Ideal.exists_le_maximal C hp.ne_top
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal GeoField hJ
  have hon : C ≤ RingHom.ker (MvPolynomial.eval x) := by
    intro P hP
    have h := hCJ hP
    rw [hx, MvPolynomial.mem_vanishingIdeal_singleton_iff, MvPolynomial.aeval_eq_eval] at h
    exact h
  have hcut : ∃ i : Fin 4, MvPolynomial.X i - MvPolynomial.C (x i) ∉ C := by
    by_contra! hall
    let q := Ideal.Quotient.mk C
    have hq : q = q.comp (MvPolynomial.C.comp (MvPolynomial.eval x)) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp
      · intro i
        simp only [RingHom.comp_apply, MvPolynomial.eval_X]
        exact sub_eq_zero.mp (by
          rw [← map_sub]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (hall i))
    have hsurj : Function.Surjective (q.comp MvPolynomial.C) := by
      intro b
      obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact ⟨MvPolynomial.eval x P, (RingHom.congr_fun hq P).symm⟩
    have hle := ringKrullDim_le_of_surjective _ hsurj
    rw [hdim, ringKrullDim_eq_zero_of_field] at hle
    exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) hle
  obtain ⟨i, hi⟩ := hcut
  let D : GeoJets := MvPolynomial.X i - MvPolynomial.C (x i)
  refine ⟨x, D, hon, ⟨?_, ?_, ?_⟩, hi, by simp [D]⟩
  · exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  · apply MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
    apply Submodule.sub_mem
    · exact MvPolynomial.X_mem_restrictWeightedDegree _ _ _ (Nat.le_of_lt_succ i.isLt)
    · exact MvPolynomial.C_mem_restrictWeightedDegree _ _ _
  · apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
    simp only [MvPolynomial.degreeOf_X, MvPolynomial.degreeOf_C, max_zero]
    split <;> decide

end
end K1_13_6_1_5
end PackSource_K1_13_6_1_5Aux1

section PackSource_K1_13_6_1_5Split
set_option autoImplicit true
namespace K1_13_6_1_5
noncomputable section

open Polynomial K1 K1_13 K1_13_6 K1_13_6_1 K1_13_7 K1_13_7_1

/-- The common Taylor denominator and numerators at the original recovery length. -/
def c1 : Prop :=
  ∀ (g : Row 4) (p : Shape), InBox (shape g) p → Chamber p → 0 < p.t →
    ∃ T : TaylorChart, T.Fits (chart taylorLength p) ∧
      ∀ S : Geom[X], atJet g S = 0 → RegularAt g S → T.Recovers S

/-- A proper supported cut on an integral curve pays six units per distinct
point in the generic section of the sixfold box. -/
def c2 : Prop :=
  ∀ (C : Ideal GeoJets) (p : Shape), C.IsPrime → ringKrullDim (GeoJets ⧸ C) = 1 →
    InBox ⟨1, 3, 1⟩ p →
    ∀ (D : GeoJets), GeoFits D p → D ∉ C →
      ∀ points : Finset GeoPoint,
        (∀ x ∈ points, C ≤ RingHom.ker (MvPolynomial.eval x) ∧ MvPolynomial.eval x D = 0) →
        6 * points.card ≤ sectionDegree C (p.scale 6)

private theorem count_marks (h2 : c2) {f C s p D} {Γ : Finset K}
    (hc : CurveOnFactor f C) (hp : InBox ⟨1, 3, 1⟩ p)
    (hD : GeoFits D p) (hproper : D ∉ C) (hinj : Set.InjOn s (Γ : Set K))
    {L : Finset K} (hL : L ⊆ Γ)
    (hmarks : ∀ γ ∈ L, C ≤ markIdeal (extend (s γ)) ∧ evalGeneric (extend (s γ)) D = 0) :
    6 * L.card ≤ sectionDegree C (p.scale 6) := by
  classical
  let point := fun γ => markPoint (extend (s γ))
  have hinjL : Set.InjOn point (L : Set K) := by
    intro γ hγ η hη he
    exact hinj (hL hγ) (hL hη)
      (Polynomial.map_injective embed embed.injective (markPoint_injective he))
  have hcount := h2 C p hc.prime hc.dim hp D hD hproper (L.image point) (by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    exact hmarks γ hγ)
  rwa [Finset.card_image_of_injOn hinjL] at hcount

private theorem chart_has_simplex (p : Shape) (hp : InBox ⟨1, 3, 1⟩ p) :
    InBox ⟨1, 3, 1⟩ (chart taylorLength p) := by
  obtain ⟨hb, hj, ht⟩ := hp
  change 1 ≤ p.b at hb
  change 3 ≤ p.j at hj
  change 1 ≤ p.t at ht
  unfold chart
  simp only [InBox]
  exact ⟨(Nat.le_add_right _ _).trans (le_max_left _ _),
    Nat.le_add_left _ _, le_min (by omega) (by omega)⟩

theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1.c5 := by
  classical
  intro Γ s f C r hf hc hr hsep hinj hdeg
  let p := anchorBox f
  let g := (separant^[r]) f
  have hp := shape_chamber f
  have ht : 0 < p.t := hf.2.1
  have hunit : InBox ⟨1, 3, 1⟩ p := by
    change 1 ≤ p.b ∧ 3 ≤ p.j ∧ 1 ≤ p.t
    change Chamber p at hp
    have hbj := hp.1
    have hjt := hp.2
    omega
  have hgbox : InBox (shape g) p :=
    let hb := derivative_in_box f r
    ⟨hb.1.trans (le_max_left _ _), hb.2.1, hb.2.2⟩
  obtain ⟨T, hfit, hrecover⟩ := h1 g p hgbox hp ht
  let A := Γ.filter fun γ => C ≤ markIdeal (extend (s γ)) ∧ RegularAt g (extend (s γ))
  let B := Γ.filter fun γ => C ≤ markIdeal (extend (s γ)) ∧ ¬ RegularAt g (extend (s γ))
  let d := sectionDegree C ((chart taylorLength p).scale 6) / 6
  refine ⟨A, B, d, Finset.filter_subset _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro x a hmiss
    let D := T.pullback (valueForm x a)
    have on {γ} (hγ : γ ∈ A) :
        C ≤ markIdeal (extend (s γ)) ∧
          (evalGeneric (extend (s γ)) D = 0 ↔ (s γ).eval x = a) := by
      obtain ⟨hΓ, hpoint, hreg⟩ := Finset.mem_filter.mp hγ
      have hvan : atJet g (extend (s γ)) = 0 :=
        mem_markIdeal.mp (hpoint (hr.2.1 r le_rfl))
      exact ⟨hpoint, value_cut_eval T (hdeg γ hΓ) (hrecover _ hvan hreg) x a⟩
    have hproper : D ∉ C := by
      obtain ⟨γ, hγ, hmiss⟩ := hmiss
      exact fun hmem => hmiss ((on hγ).2.mp ((on hγ).1 hmem))
    let L := A.filter fun γ => (s γ).eval x = a
    have hL : L ⊆ Γ := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hcount := count_marks h2 hc (chart_has_simplex p hunit) (T.pullback_fits hfit _)
      hproper hinj hL (by
        intro γ hγ
        change γ ∈ A.filter (fun η => (s η).eval x = a) at hγ
        obtain ⟨hA, hv⟩ := Finset.mem_filter.mp hγ
        exact ⟨(on hA).1, (on hA).2.mpr hv⟩)
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 6)).mpr (by simpa [Nat.mul_comm] using hcount)
  · intro γ hγ hpoint
    by_cases hreg : RegularAt g (extend (s γ))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hpoint, hreg⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, hpoint, hreg⟩)
  · simpa only [d, Nat.mul_comm] using
      Nat.div_mul_le_self (sectionDegree C ((chart taylorLength p).scale 6)) 6
  · apply count_marks h2 hc hunit (toGeneric_fits hsep) hr.2.2 hinj (Finset.filter_subset _ _)
    intro γ hγ
    obtain ⟨_, hpoint, hsing⟩ := Finset.mem_filter.mp hγ
    exact ⟨hpoint, mem_markIdeal.mpr (not_ne_iff.mp hsing)⟩
  · obtain ⟨x, P, hx, hP, hproper, hvan⟩ := coordinate_cut hc.prime hc.dim
    have hfitP : GeoFits P p :=
      ⟨hP.1.trans hunit.1, hP.2.1.trans hunit.2.1, hP.2.2.trans hunit.2.2⟩
    simpa using h2 C p hc.prime hc.dim hunit P hfitP hproper {x} (by
      intro y hy
      rw [Finset.mem_singleton.mp hy]
      exact ⟨hx, hvan⟩)

end
end K1_13_6_1_5
end PackSource_K1_13_6_1_5Split

section PackSource_K1_13_6_1_5_2Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_5_2

open K1_13 K1_13_6 K1_13_6_1

/-- The scheme-theoretic affine fibre of a prescribed section. -/
abbrev CutQuotient (C : Ideal GeoJets) (E : GeoJets) :=
  GeoJets ⧸ (C ⊔ Ideal.span {E})

/-- The affine section quotient used in the definition of sectionDegree. -/
abbrev GenericQuotient (C : Ideal GeoJets) (a : Shape) :=
  SectionJets a ⧸
    (C.map (MvPolynomial.map (algebraMap GeoField (SectionField a))) ⊔
      Ideal.span {genericSection a})

/-- A specialization of the coefficients of the full box section. -/
noncomputable def boxSection (a : Shape) (c : SectionIndex a → GeoField) : GeoJets :=
  ∑ m ∈ boxMonomials a, MvPolynomial.C (c m) * ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val

end K1_13_6_1_5_2
end PackSource_K1_13_6_1_5_2Defs

section PackSource_K1_13_6_1_5_2Aux
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_5_2

open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1 MvPolynomial

theorem fits_pow {D : GeoJets} {p : Shape} (hD : GeoFits D p) (n : ℕ) :
    GeoFits (D ^ n) (p.scale n) :=
  ⟨(totalDegree_pow D n).trans (Nat.mul_le_mul_left n hD.1),
    (weightedTotalDegree_pow_le _ D n).trans (Nat.mul_le_mul_left n hD.2.1),
    (degreeOf_pow_le _ D n).trans (Nat.mul_le_mul_left n hD.2.2)⟩

private noncomputable def exponent (a : Shape) : SectionIndex a ↪ (Fin 4 →₀ ℕ) where
  toFun m := Finsupp.equivFunOnFinite.symm fun i => (m i).val
  inj' := by
    intro x y h
    funext i
    apply Fin.ext
    exact DFunLike.congr_fun h i

theorem exists_boxSection {E : GeoJets} {a : Shape} (hE : GeoFits E a) :
    ∃ c : SectionIndex a → GeoField, boxSection a c = E := by
  classical
  refine ⟨fun m => E.coeff (exponent a m), ?_⟩
  have hexp (m : SectionIndex a) (i : Fin 4) : exponent a m i = (m i).val := rfl
  have hsupport : E.support ⊆ (boxMonomials a).map (exponent a) := by
    intro s hs
    have hb : (∑ i : Fin 4, s i) ≤ a.b := by
      simpa [Finsupp.sum_fintype] using (le_totalDegree hs).trans hE.1
    have hj : (∑ i : Fin 4, i.val * s i) ≤ a.j := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, nsmul_eq_mul, Nat.mul_comm] using
        (le_weightedTotalDegree Fin.val hs).trans hE.2.1
    have ht : s 3 ≤ a.t := (monomial_le_degreeOf 3 hs).trans hE.2.2
    let m : SectionIndex a := fun i =>
      ⟨s i, Nat.lt_succ_of_le ((Finset.single_le_sum
        (f := fun j : Fin 4 => s j) (fun j _ => Nat.zero_le (s j)) (Finset.mem_univ i)).trans hb)⟩
    refine Finset.mem_map.mpr ⟨m, ?_, Finsupp.ext fun _ => rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ m, hb, hj, ht⟩
  have hsum := Finset.sum_subset (f := fun s => monomial s (E.coeff s)) hsupport (by
    intro s _ hs
    rw [notMem_support_iff.mp hs, map_zero])
  rw [Finset.sum_map] at hsum
  calc
    boxSection a (fun m => E.coeff (exponent a m)) =
        ∑ m ∈ boxMonomials a, monomial (exponent a m) (E.coeff (exponent a m)) := by
      unfold boxSection
      apply Finset.sum_congr rfl
      intro m _
      rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      simp only [hexp]
    _ = E := hsum.symm.trans E.as_sum.symm

theorem cut_finite {C : Ideal GeoJets} [C.IsPrime]
    (hdim : ringKrullDim (GeoJets ⧸ C) = 1) {E : GeoJets} (hE : E ∉ C) :
    Module.Finite GeoField (CutQuotient C E) := by
  have hlt : C < C ⊔ Ideal.span {E} := by
    apply lt_of_le_of_ne le_sup_left
    intro h
    exact hE (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self E) :
      E ∈ C)
  have hd := Ideal.ringKrullDim_quotient_succ_le_of_lt hlt
  rw [hdim] at hd
  apply (Module.finite_iff_krullDimLE_zero GeoField _).mpr
  apply Ring.krullDimLE_iff.mpr
  exact ENat.WithBot.add_le_add_one_right_iff.mp (by simpa using hd)

theorem pow_not_mem {C : Ideal GeoJets} [C.IsPrime] {D : GeoJets} (hD : D ∉ C) (n : ℕ) :
    D ^ n ∉ C := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
  exact pow_ne_zero n (mt Ideal.Quotient.eq_zero_iff_mem.mp hD)

private theorem power_colon {C : Ideal GeoJets} [C.IsPrime] {D : GeoJets} (hD : D ∉ C)
    (n : ℕ) : (C ⊔ Ideal.span {D ^ (n + 1)}).colon {D} = C ⊔ Ideal.span {D ^ n} := by
  ext x
  let q := Ideal.Quotient.mk C
  have hqD : q D ≠ 0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hD
  rw [Submodule.mem_colon_singleton, smul_eq_mul]
  constructor
  · intro hx
    obtain ⟨c, hc, y, hy, hsum⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hy
    have heq : q D * q x = q D * (q (D ^ n) * q r) := by
      have h := congrArg q hsum
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hc, zero_add, pow_succ,
        map_mul, map_mul, map_mul] at h
      linear_combination -h
    have hdiff : x - D ^ n * r ∈ C := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, map_mul, mul_left_cancel₀ hqD heq, sub_self]
    apply Submodule.mem_sup.mpr
    refine ⟨x - D ^ n * r, hdiff, D ^ n * r, Ideal.mem_span_singleton.mpr ⟨r, rfl⟩, ?_⟩
    exact sub_add_cancel _ _
  · intro hx
    obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hy
    rw [add_mul]
    apply Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right D C hc))
    apply Ideal.mem_sup_right
    exact Ideal.mem_span_singleton.mpr ⟨r, by rw [pow_succ]; ac_rfl⟩

private theorem sup_pow_succ {C : Ideal GeoJets} (D : GeoJets) (n : ℕ) :
    (C ⊔ Ideal.span {D ^ (n + 1)}) ⊔ Ideal.span {D} = C ⊔ Ideal.span {D} := by
  have hpow : (Ideal.span {D ^ (n + 1)} : Ideal GeoJets) ≤ Ideal.span {D} :=
    (Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_span_singleton.mpr ⟨D ^ n, by rw [pow_succ, mul_comm]⟩)
  rw [sup_assoc, sup_eq_right.mpr hpow]

set_option maxHeartbeats 800000 in
theorem finrank_power {C : Ideal GeoJets} [C.IsPrime] {D : GeoJets}
    (hdim : ringKrullDim (GeoJets ⧸ C) = 1) (hD : D ∉ C) (n : ℕ) :
    Module.finrank GeoField (CutQuotient C (D ^ n)) =
      n * Module.finrank GeoField (CutQuotient C D) := by
  induction n with
  | zero =>
    let : Subsingleton (CutQuotient C (D ^ 0)) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.span_singleton_one, sup_top_eq])
    simpa only [Nat.zero_mul] using
      (Module.finrank_zero_of_subsingleton : Module.finrank GeoField (CutQuotient C (D ^ 0)) = 0)
  | succ n ih =>
    let I : Ideal GeoJets := C ⊔ Ideal.span {D ^ (n + 1)}
    let J := I ⊔ Ideal.span {D}
    let : Module.Finite GeoField (GeoJets ⧸ I) := cut_finite hdim (pow_not_mem hD _)
    let q := (Submodule.factor (le_sup_left : I ≤ J)).restrictScalars GeoField
    let m := (K1_13_6_3_6.quotientMul I D).restrictScalars GeoField
    have hex : Function.Exact m q := K1_13_6_3_6.quotientMul_exact I D
    have he := (LinearMap.exact_iff.mp hex).symm
    have hr := q.finrank_range_add_finrank_ker
    have hq : Function.Surjective q := Submodule.factor_surjective (le_sup_left : I ≤ J)
    have hm : Function.Injective m := K1_13_6_3_6.quotientMul_injective I D
    rw [LinearMap.range_eq_top.mpr hq, finrank_top, ← he,
      ← (LinearEquiv.ofInjective m hm).finrank_eq] at hr
    change Module.finrank GeoField (GeoJets ⧸ ((C ⊔ Ideal.span {D ^ (n + 1)}) ⊔ Ideal.span {D})) +
      Module.finrank GeoField (GeoJets ⧸ (C ⊔ Ideal.span {D ^ (n + 1)}).colon {D}) =
      Module.finrank GeoField (CutQuotient C (D ^ (n + 1))) at hr
    rw [sup_pow_succ, power_colon hD] at hr
    change Module.finrank GeoField (CutQuotient C D) +
      Module.finrank GeoField (CutQuotient C (D ^ n)) = _ at hr
    rw [ih, add_comm, ← Nat.succ_mul] at hr
    exact hr.symm

theorem card_le_finrank {C : Ideal GeoJets} {D : GeoJets}
    [Module.Finite GeoField (CutQuotient C D)] (points : Finset GeoPoint)
    (hp : ∀ x ∈ points, C ≤ RingHom.ker (MvPolynomial.eval x) ∧ MvPolynomial.eval x D = 0) :
    points.card ≤ Module.finrank GeoField (CutQuotient C D) := by
  let I : Ideal GeoJets := C ⊔ Ideal.span {D}
  have hz : (points : Set GeoPoint) ⊆ zeroLocus GeoField I := by
    intro x hx
    have hx' := hp x hx
    have hI : I ≤ RingHom.ker (MvPolynomial.eval x) :=
      sup_le hx'.1 ((Ideal.span_singleton_le_iff_mem _).mpr hx'.2)
    intro E hE
    change MvPolynomial.eval x E = 0
    exact hI hE
  have hf : (zeroLocus GeoField I).Finite := finite_zeroLocus_of_finite_quotient I
  have hcard := Set.ncard_le_ncard hz hf
  rw [Set.ncard_coe_finset] at hcard
  exact hcard.trans (ncard_zeroLocus_le_finrank_quotient I)

end K1_13_6_1_5_2
end PackSource_K1_13_6_1_5_2Aux

section PackSource_K1_13_6_1_5_2Split
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_5_2

open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1

/-- Generic sections of integral affine curves have finite coordinate algebra. -/
def c1 : Prop :=
  ∀ (C : Ideal GeoJets) (a : Shape), C.IsPrime → ringKrullDim (GeoJets ⧸ C) = 1 →
    Module.Finite (SectionField a) (GenericQuotient C a)

/-- A proper coefficient specialization cannot increase the affine section length. -/
def c2 : Prop :=
  ∀ (C : Ideal GeoJets) (a : Shape), C.IsPrime → ringKrullDim (GeoJets ⧸ C) = 1 →
    Module.Finite (SectionField a) (GenericQuotient C a) →
    ∀ c : SectionIndex a → GeoField, boxSection a c ∉ C →
      Module.Finite GeoField (CutQuotient C (boxSection a c)) →
      Module.finrank GeoField (CutQuotient C (boxSection a c)) ≤ sectionDegree C a

theorem of_children (h₁ : c1) (h₂ : c2) : K1_13_6_1_5.c2 := by
  intro C p hC hdim _ D hD hproper points hpoints
  let : C.IsPrime := hC
  let : Module.Finite GeoField (CutQuotient C D) := cut_finite hdim hproper
  obtain ⟨c, hc⟩ := exists_boxSection (fits_pow hD 6)
  have hne : boxSection (p.scale 6) c ∉ C := hc ▸ pow_not_mem hproper 6
  have hlength := h₂ C (p.scale 6) hC hdim (h₁ C (p.scale 6) hC hdim) c hne
    (cut_finite hdim hne)
  rw [hc, finrank_power hdim hproper] at hlength
  exact (Nat.mul_le_mul_left 6 (card_le_finrank points hpoints)).trans hlength

end K1_13_6_1_5_2
end PackSource_K1_13_6_1_5_2Split

section PackSource_K1_13_6_1_5_2_2Aux
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_5_2_2

open MvPolynomial

/-- Independent residues force all scalar coefficients of a polynomial relation to vanish
when its right-hand side is a multiple of a section with regular constant term. -/
theorem coefficients_eq_zero
    {k A D σ ι : Type*} [Field k] [CommRing A] [IsDomain A] [CommRing D]
    [Algebra k A] [Algebra k D] [Fintype ι]
    (q : A →ₐ[k] D) (v : ι → A) (hv : LinearIndependent k (q ∘ v))
    (r : ι → MvPolynomial σ k) (H Q : MvPolynomial σ A)
    (hne : constantCoeff H ≠ 0) (hq : q (constantCoeff H) = 0)
    (he : (∑ i, C (v i) * MvPolynomial.map (algebraMap k A) (r i)) = H * Q) :
    ∀ i, r i = 0 := by
  classical
  have h (n : ℕ) : ∀ m : σ →₀ ℕ, m.degree = n → Q.coeff m = 0 ∧ ∀ i, (r i).coeff m = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m hm
      have hprod : (H * Q).coeff m = constantCoeff H * Q.coeff m := by
        rw [coeff_mul, Finset.sum_eq_single (0, m)]
        · rfl
        · intro p hp hne'
          have hadd := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          have hp₁ : p.1 ≠ 0 := by
            intro hz
            apply hne'
            exact Prod.ext hz (by simpa [hz] using hadd)
          have hdeg₁ : 0 < p.1.degree :=
            Nat.pos_of_ne_zero (fun hd => hp₁ ((Finsupp.degree_eq_zero_iff _).mp hd))
          have hdegs : p.1.degree + p.2.degree = n := by
            rw [← map_add, hadd, hm]
          rw [(ih p.2.degree (by omega) p.2 rfl).1, mul_zero]
        · exact fun hmiss => (hmiss (Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add m))).elim
      have hc := congrArg (fun P : MvPolynomial σ A => P.coeff m) he
      simp only [coeff_sum, coeff_C_mul, coeff_map, hprod] at hc
      have hrel : ∑ i, (r i).coeff m • (q ∘ v) i = 0 := by
        simpa only [map_sum, map_mul, AlgHom.commutes, hq, zero_mul, Function.comp_apply,
          Algebra.smul_def, mul_comm] using congrArg q hc
      have hzero := Fintype.linearIndependent_iff.mp hv _ hrel
      simp only [hzero, map_zero, mul_zero, Finset.sum_const_zero] at hc
      exact ⟨(mul_eq_zero.mp hc.symm).resolve_left hne, hzero⟩
  intro i
  ext m
  exact (h m.degree m rfl).2 i

end K1_13_6_1_5_2_2
end PackSource_K1_13_6_1_5_2_2Aux

section PackSource_K1_13_6_1_5_2_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_5_2_2

noncomputable section

open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_5_2 MvPolynomial
open scoped nonZeroDivisors

attribute [local instance] MvPolynomial.algebraMvPolynomial

private def translate {σ k : Type*} [CommRing k] (c : σ → k) :
    MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval (fun i => MvPolynomial.X i + C (c i))

private theorem translate_injective {σ k : Type*} [CommRing k] (c : σ → k) :
    Function.Injective (translate c) := by
  have h : (translate (fun i => -c i)).comp (translate c) = AlgHom.id k _ := by
    ext i : 1
    simp [translate, MvPolynomial.algebraMap_eq, add_assoc]
  have hinv : Function.LeftInverse (translate (fun i => -c i)) (translate c) :=
    fun p => AlgHom.congr_fun h p
  exact hinv.injective

private theorem lift_independence
    (C₀ : Ideal GeoJets) [C₀.IsPrime] (a : Shape) (c : SectionIndex a → GeoField)
    (hproper : boxSection a c ∉ C₀)
    {ι : Type} [Fintype ι] (v : ι → GeoJets)
    (hv : LinearIndependent GeoField
      (fun i => Ideal.Quotient.mk (C₀ ⊔ Ideal.span {boxSection a c}) (v i))) :
    LinearIndependent (SectionField a) (fun i =>
      (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap GeoField (SectionField a)) (v i))
        : GenericQuotient C₀ a)) := by
  classical
  let k := GeoField
  let R := MvPolynomial (SectionIndex a) k
  let F := SectionField a
  let B := MvPolynomial (Fin 4) R
  let L := SectionJets a
  let j : GeoJets →+* B := MvPolynomial.map (algebraMap k R)
  let H₀ : B := ∑ m ∈ boxMonomials a,
    C (MvPolynomial.X m) * ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val
  let I := C₀.map j ⊔ Ideal.span {H₀}
  let J : Ideal L := C₀.map (MvPolynomial.map (algebraMap k F)) ⊔ Ideal.span {genericSection a}
  let M : Submonoid B := (nonZeroDivisors R).map MvPolynomial.C
  have : IsLocalization M L := MvPolynomial.isLocalization (nonZeroDivisors R) F
  have hC (z : R) : algebraMap B L (C z) = C (algebraMap R F z) := by
    rw [MvPolynomial.algebraMap_def, map_C]
  have hX (i : Fin 4) : algebraMap B L (MvPolynomial.X i) = MvPolynomial.X i := by
    rw [MvPolynomial.algebraMap_def, map_X]
  have hj (p : GeoJets) : algebraMap B L (j p) =
      MvPolynomial.map (algebraMap k F) p := by
    rw [MvPolynomial.algebraMap_def]
    change MvPolynomial.map (algebraMap R F) (MvPolynomial.map (algebraMap k R) p) = _
    rw [MvPolynomial.map_map]
    rfl
  have hH : algebraMap B L H₀ = genericSection a := by
    simp only [H₀, genericSection, map_sum, map_mul, map_prod, map_pow, hC, hX]
    rfl
  have hJ : I.map (algebraMap B L) = J := by
    simp only [I, J, Ideal.map_sup, Ideal.map_map, Ideal.map_span, Set.image_singleton, hH]
    rw [show (algebraMap B L).comp j = MvPolynomial.map (algebraMap k F) from RingHom.ext hj]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  change ∑ i, g i • Ideal.Quotient.mk J (MvPolynomial.map (algebraMap k F) (v i)) = 0 at hg
  -- Clear the scalar denominators, then clear the denominator in the localized ideal.
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) g
  choose r hr using hd
  have hr' (i : ι) : algebraMap R F (r i) = algebraMap R F (d : R) * g i := by
    simpa only [Algebra.smul_def] using hr i
  have hsum : (∑ i, C (g i) * MvPolynomial.map (algebraMap k F) (v i)) ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hscalar (x : SectionField a) :
        algebraMap (SectionField a) (L ⧸ J) x = Ideal.Quotient.mk J (C x) := rfl
    simpa only [map_sum, map_mul, Algebra.smul_def, hscalar] using hg
  have hclear : algebraMap B L (∑ i, C (r i) * j (v i)) ∈ I.map (algebraMap B L) := by
    rw [hJ]
    convert J.mul_mem_left (C (algebraMap R F (d : R))) hsum using 1
    simp only [map_sum, map_mul, hC, hj, hr', Finset.mul_sum, mul_assoc]
  obtain ⟨s, hs, hmem⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M L I _).mp hclear
  obtain ⟨d', hd', rfl⟩ := Submonoid.mem_map.mp hs
  let A := GeoJets ⧸ C₀
  let q₀ := Ideal.Quotient.mk C₀
  let t := translate c
  let f₀ : R →+* MvPolynomial (SectionIndex a) A :=
    (MvPolynomial.map (algebraMap k A)).comp t.toRingHom
  let fX : Fin 4 → MvPolynomial (SectionIndex a) A :=
    fun i => C (q₀ (MvPolynomial.X i))
  let f : B →+* MvPolynomial (SectionIndex a) A :=
    eval₂Hom f₀ fX
  have hfC (p : R) : f (C p) = MvPolynomial.map (algebraMap k A) (t p) :=
    eval₂Hom_C f₀ fX p
  have hfX (i : Fin 4) : f (MvPolynomial.X i) = C (q₀ (MvPolynomial.X i)) :=
    eval₂Hom_X' f₀ fX i
  have hfj (p : GeoJets) : f (j p) = C (q₀ p) := by
    have he : f.comp j = MvPolynomial.C.comp q₀ := by
      apply MvPolynomial.ringHom_ext
      · intro z
        change f (MvPolynomial.map (algebraMap k R) (C z)) = C (q₀ (C z))
        rw [map_C, hfC, t.commutes]
        change MvPolynomial.map (algebraMap k A) (C z) = _
        rw [map_C]
        rfl
      · intro i
        change f (MvPolynomial.map (algebraMap k R) (MvPolynomial.X i)) = C (q₀ (MvPolynomial.X i))
        rw [map_X, hfX]
    exact DFunLike.congr_fun he p
  have hcut : constantCoeff (f H₀) = q₀ (boxSection a c) := by
    have htX (m : SectionIndex a) : t (MvPolynomial.X m) = MvPolynomial.X m + C (c m) :=
      aeval_X _ _
    simp only [H₀, boxSection, map_sum, map_mul, map_prod, map_pow,
      hfC, hfX, htX, map_add, map_X, map_C,
      constantCoeff_X, constantCoeff_C, zero_add, q₀]
    rfl
  have hI : I ≤ (Ideal.span {f H₀}).comap f := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro p hp
      change f (j p) ∈ (Ideal.span {f H₀} : Ideal _)
      rw [hfj, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
      exact Ideal.zero_mem _
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      exact Ideal.mem_span_singleton_self _
  have hmultiple : f (C d' * ∑ i, C (r i) * j (v i)) ∈ (Ideal.span {f H₀} : Ideal _) :=
    hI hmem
  obtain ⟨Q, hQ⟩ := Ideal.mem_span_singleton.mp hmultiple
  let q : A →ₐ[k] CutQuotient C₀ (boxSection a c) :=
    Ideal.Quotient.factorₐ k (le_sup_left : C₀ ≤ C₀ ⊔ Ideal.span {boxSection a c})
  have he : (∑ i, C (q₀ (v i)) * MvPolynomial.map (algebraMap k A) (t (d' * r i))) =
      f H₀ * Q := by
    calc
      _ = f (C d' * ∑ i, C (r i) * j (v i)) := by
        simp only [map_mul, map_sum, hfC, hfj, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ac_rfl)
      _ = _ := hQ
  have hE : q (constantCoeff (f H₀)) = 0 := by
    rw [hcut]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hz := coefficients_eq_zero q (fun i => q₀ (v i)) hv
    (fun i => t (d' * r i)) (f H₀) Q (by rw [hcut]; exact mt Ideal.Quotient.eq_zero_iff_mem.mp hproper)
    hE he
  have hd'₀ : d' ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd'
  have hd₀ : algebraMap R F (d : R) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective R F).ne (mem_nonZeroDivisors_iff_ne_zero.mp d.property)
  intro i
  have hdi : d' * r i = 0 := translate_injective c ((hz i).trans (map_zero t).symm)
  have hri := (mul_eq_zero.mp hdi).resolve_left hd'₀
  exact (mul_eq_zero.mp ((hr' i).symm.trans (by rw [hri, map_zero]))).resolve_left hd₀

/-- Every proper box specialization has length at most the generic affine section. -/
theorem proof : K1_13_6_1_5_2.c2 := by
  classical
  intro C₀ a hprime _ hgeneric c hproper hfinite
  let : C₀.IsPrime := hprime
  let : Module.Finite (SectionField a) (GenericQuotient C₀ a) := hgeneric
  let : Module.Finite GeoField (CutQuotient C₀ (boxSection a c)) := hfinite
  let b := Module.finBasis GeoField (CutQuotient C₀ (boxSection a c))
  choose v hv using fun i => Ideal.Quotient.mk_surjective (b i)
  have hli := lift_independence C₀ a c hproper v
    (show LinearIndependent GeoField
      (fun i => Ideal.Quotient.mk (C₀ ⊔ Ideal.span {boxSection a c}) (v i)) by
      simpa only [hv] using b.linearIndependent)
  change _ ≤ Module.finrank (SectionField a) (GenericQuotient C₀ a)
  simpa only [Fintype.card_fin] using hli.fintype_card_le_finrank

end

end K1_13_6_1_5_2_2
end PackSource_K1_13_6_1_5_2_2Proof

section PackSource_K1_13_6_1_5_1Proof
set_option autoImplicit true
namespace K1_13_6_1_5_1

noncomputable section

open Polynomial MvPolynomial K1_13 K1_13_6 K1_13_6_2_1 K1_13_7_1

local notation "W" => MvPolynomial.weightedTotalDegree

-- Keep the clearing length symbolic while proving the support and evaluation identities.
private def denominator (L : ℕ) (g : Row 4) : Row 4 :=
  separant g ^ (2 * L)

private def numerator (L : ℕ) (g : Row 4) (i : TaylorIndex) : Row 4 :=
  if hi : i.val < 4 then MvPolynomial.X ⟨i.val, hi⟩ * denominator L g
  else
    MvPolynomial.C (Polynomial.C (↑i.val.factorial : Geom)⁻¹) *
      (separant g ^ (2 * (L - i.val)) * jetNumerator g i.val)

private def recoveryChart (L : ℕ) (g : Row 4) : TaylorChart where
  denom := toGeneric (denominator L g)
  numerator i := toGeneric (numerator L g i)
  initial i := by
    unfold numerator toGeneric
    have hi : (i.castLE (by decide : 4 ≤ taylorLength)).val < 4 := i.isLt
    rw [dite_eq_left hi, map_mul, MvPolynomial.map_X]
    rfl

private theorem numerator_bound {L : ℕ} (hL : taylorLength ≤ L) (w : Fin 4 → ℕ)
    (Δ d₀ : ℕ) (hshift : ∀ i : Fin 3, w i.succ ≤ w i.castSucc + Δ) (hw : ∀ i, w i ≤ d₀)
    {g : Row 4} {B : ℕ} (hB : w 3 ≤ B) (hg : W w g ≤ B) (i : TaylorIndex) :
    W w (numerator L g i) ≤ d₀ + 2 * L * (B - w 3) + L * Δ := by
  have hi : i.val ≤ L := i.isLt.le.trans hL
  unfold numerator
  split_ifs
  · exact (weightedTotalDegree_mul_le _ _ _).trans
      ((Nat.add_le_add ((weight_X_le w _).trans (hw _)) (separant_pow_bound w hg _)).trans
        (Nat.le_add_right _ _))
  · apply (weight_const_mul_le _ _ _).trans
    apply (weightedTotalDegree_mul_le _ _ _).trans
    calc
      _ ≤ 2 * (L - i.val) * (B - w 3) + (w 0 + i.val * (2 * (B - w 3) + Δ)) :=
        Nat.add_le_add (separant_pow_bound w hg _) (jet_bound w Δ hshift hB hg i.val)
      _ = w 0 + 2 * (i.val + (L - i.val)) * (B - w 3) + i.val * Δ := by ring
      _ ≤ _ := by
        rw [Nat.add_sub_of_le hi]
        exact Nat.add_le_add (Nat.add_le_add_right (hw 0) _) (Nat.mul_le_mul_right Δ hi)

private theorem chart_fits {L : ℕ} (hL : taylorLength ≤ L) {g : Row 4} {p : Shape}
    (hg : InBox (shape g) p) (hp : Chamber p) (ht : 0 < p.t) :
    (recoveryChart L g).Fits (chart L p) := by
  constructor
  · apply three_weights hg hp ht
    intro w Δ d₀ B _ _ _ hB
    exact (separant_pow_bound w hB (2 * L)).trans (by omega)
  · intro i
    exact three_weights hg hp ht (fun w Δ d₀ _ hs hw hwB hB =>
      numerator_bound hL w Δ d₀ hs hw hwB hB i)

private theorem ordinary_eq_hasse (S : Geom[X]) (n : ℕ) :
    derivative^[n] S = Polynomial.C (n.factorial : Geom) * hasseDeriv n S := by
  ext m
  rw [coeff_iterate_derivative, Polynomial.coeff_C_mul, hasseDeriv_coeff,
    Nat.descFactorial_eq_factorial_mul_choose]
  simp only [nsmul_eq_mul, Nat.cast_mul, mul_assoc]

private theorem chart_recovers {L : ℕ} (hL : taylorLength ≤ L) {g : Row 4} {S : Geom[X]}
    (hg : atJet g S = 0) (hr : K1_13_7.RegularAt g S) : (recoveryChart L g).Recovers S := by
  have hden : atJet (denominator L g) S = atJet (separant g) S ^ (2 * L) :=
    map_pow (MvPolynomial.eval (jet S : Fin 4 → Geom[X])) _ _
  constructor
  · change evalGeneric S (toGeneric (denominator L g)) ≠ 0
    rw [evalGeneric_toGeneric, map_ne_zero_iff _ genericCoeffs_injective, hden]
    exact pow_ne_zero _ hr
  · intro i
    change evalGeneric S (toGeneric (numerator L g i)) =
      evalGeneric S (toGeneric (denominator L g)) * genericCoeffs (hasseDeriv i.val S)
    rw [evalGeneric_toGeneric, evalGeneric_toGeneric, ← map_mul]
    apply congrArg genericCoeffs
    unfold numerator
    split_ifs with hinit
    · unfold atJet
      rw [map_mul, MvPolynomial.eval_X, mul_comm]
      rfl
    · let E := MvPolynomial.eval (jet S : Fin 4 → Geom[X])
      change E (_ * (_ ^ _ * _)) = _
      rw [map_mul, map_mul, map_pow, MvPolynomial.eval_C]
      change _ * (atJet (separant g) S ^ (2 * (L - i.val)) *
        atJet (jetNumerator g i.val) S) = _
      rw [eval_jetNumerator _ _ hg, ordinary_eq_hasse]
      have hinv : Polynomial.C (↑i.val.factorial : Geom)⁻¹ *
          Polynomial.C (↑i.val.factorial : Geom) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ (factorial_cast_ne_zero
          (i.isLt.trans (by decide : taylorLength < K1.p))), map_one]
      have hpow : 2 * (L - i.val) + 2 * i.val = 2 * L := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (i.isLt.le.trans hL)]
      calc
        _ = (Polynomial.C (↑i.val.factorial : Geom)⁻¹ * Polynomial.C (↑i.val.factorial : Geom)) *
            ((atJet (separant g) S ^ (2 * (L - i.val)) * atJet (separant g) S ^ (2 * i.val)) *
              hasseDeriv i.val S) := by ring
        _ = _ := by rw [hinv, one_mul, ← pow_add, hpow, hden]

/-- Taylor recovery on the regular four-jet chart at the original length. -/
theorem proof : K1_13_6_1_5.c1 := by
  intro g p hbox hp ht
  exact ⟨recoveryChart taylorLength g, chart_fits le_rfl hbox hp ht,
    fun _ hg hr => chart_recovers le_rfl hg hr⟩

end
end K1_13_6_1_5_1
end PackSource_K1_13_6_1_5_1Proof

section PackSource_K1_13_6_1_4_2_2Defs
set_option autoImplicit true
namespace K1_13_6_1_4_2_2

noncomputable section

open K1_13 K1_13_6 K1_13_6_1_4_2 MvPolynomial

/-- The sixfold lattice system is applied to the combination of the three
shapes with the indicated multidegree. -/
def combinedShape (a b h : Shape) (t : Fin 3 → ℕ) : Shape :=
  ((a.scale (t 0)).plus (b.scale (t 1))).plus (h.scale (t 2))

/-- The dimension of the monomial span after restriction to the surface. -/
def boxHilbert (surface : Ideal GeoJets) (p : Shape) : ℕ :=
  Module.finrank GeoField
    ((restrictSupport GeoField (latticeIndices p)).map
      (Ideal.Quotient.mkₐ GeoField surface).toLinearMap)

/-- The common three-graded Hilbert function. -/
def multiHilbert (surface : Ideal GeoJets) (a b h : Shape) (t : Fin 3 → ℕ) : ℕ :=
  boxHilbert surface (combinedShape a b h t)

/-- Variables of the common monomial presentation, retaining their blocks. -/
abbrev SectionVariable (a b h : Shape) :=
  Σ l : Fin 3, latticeIndices (![a, b, h] l)

/-- The multidegree of a monomial in variables with unit-vector degrees. -/
def blockDegree {σ : Type} (block : σ → Fin 3) (e : σ →₀ ℕ) : Fin 3 → ℕ :=
  fun l => e.sum fun v n => if block v = l then n else 0

/-- Count the monomials of an exact multidegree outside the upward cones
generated by the forbidden exponents. -/
def standardCount {σ : Type} (block : σ → Fin 3) (forbidden : Finset (σ →₀ ℕ))
    (t : Fin 3 → ℕ) : ℕ :=
  ({e | blockDegree block e = t ∧ ∀ f ∈ forbidden, ¬ f ≤ e} : Set (σ →₀ ℕ)).ncard

end

end K1_13_6_1_4_2_2
end PackSource_K1_13_6_1_4_2_2Defs

section PackSource_K1_13_6_1_4_2_2Aux2
set_option autoImplicit true
namespace K1_13_6_1_4_2_2

noncomputable section

open MvPolynomial
open scoped BigOperators

/-- Restrict a multivariate polynomial to a ray with common offset `pad`. -/
def rayPolynomial (P : MvPolynomial (Fin 3) ℚ) (t : Fin 3 → ℕ) (pad : ℕ) : Polynomial ℚ :=
  P.eval₂ Polynomial.C fun l => Polynomial.C (pad : ℚ) + Polynomial.C (t l : ℚ) * Polynomial.X

theorem eval_rayPolynomial (P : MvPolynomial (Fin 3) ℚ) (t : Fin 3 → ℕ) (pad n : ℕ) :
    (rayPolynomial P t pad).eval (n : ℚ) =
      MvPolynomial.eval (fun l => ((n * t l + pad : ℕ) : ℚ)) P := by
  let f := Polynomial.evalRingHom (n : ℚ)
  have hf : f.comp Polynomial.C = RingHom.id ℚ := by ext r; simp [f]
  change f (rayPolynomial P t pad) = _
  rw [rayPolynomial, MvPolynomial.eval₂_comp_left, hf, MvPolynomial.eval₂_id]
  apply congrArg (fun x => MvPolynomial.eval x P)
  funext l
  simp [f, Function.comp_apply, Nat.cast_add, Nat.cast_mul, add_comm, mul_comm]

private theorem product_degree_and_coeff {α : Type} (s : Finset α)
    (q : α → Polynomial ℚ) (d : α → ℕ) (hq : ∀ i ∈ s, (q i).natDegree ≤ d i) :
    (∏ i ∈ s, q i).natDegree ≤ ∑ i ∈ s, d i ∧
      (∏ i ∈ s, q i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (q i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hi' := hq i (Finset.mem_insert_self i s)
    obtain ⟨hd, hc⟩ := ih fun j hj => hq j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      Polynomial.coeff_mul_add_eq_of_natDegree_le hi' hd, hc]
    exact ⟨Polynomial.natDegree_mul_le.trans (Nat.add_le_add hi' hd), rfl⟩

private theorem monomial_ray (e : Fin 3 →₀ ℕ) (r : ℚ) (t : Fin 3 → ℕ) (pad : ℕ) :
    (rayPolynomial (monomial e r) t pad).natDegree ≤ e.degree ∧
      (rayPolynomial (monomial e r) t pad).coeff e.degree =
        MvPolynomial.eval (fun i => (t i : ℚ)) (monomial e r) := by
  let f (i : Fin 3) := Polynomial.C (pad : ℚ) + Polynomial.C (t i : ℚ) * Polynomial.X
  have hf (i : Fin 3) : (f i).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  have hc (i : Fin 3) : (f i).coeff 1 = (t i : ℚ) := by
    simp [f]
  have hp (i : Fin 3) : ((f i) ^ e i).natDegree ≤ e i := by
    simpa using Polynomial.natDegree_pow_le_of_le (e i) (hf i)
  have hpc (i : Fin 3) : ((f i) ^ e i).coeff (e i) = (t i : ℚ) ^ e i := by
    simpa [hc] using
      (Polynomial.coeff_pow_of_natDegree_le (m := e i) (hf i))
  obtain ⟨hd, hcoeff⟩ := product_degree_and_coeff e.support (fun i => (f i) ^ e i) e
    (fun i _ => hp i)
  rw [rayPolynomial, MvPolynomial.eval₂_monomial, MvPolynomial.eval_monomial]
  change (Polynomial.C r * ∏ i ∈ e.support, (f i) ^ e i).natDegree ≤ _ ∧
    (Polynomial.C r * ∏ i ∈ e.support, (f i) ^ e i).coeff
      (∑ i ∈ e.support, e i) = r * ∏ i ∈ e.support, (t i : ℚ) ^ e i
  exact ⟨(Polynomial.natDegree_C_mul_le _ _).trans hd, by
    rw [Polynomial.coeff_C_mul, hcoeff]
    simp only [hpc]⟩

private theorem ray_as_sum (P : MvPolynomial (Fin 3) ℚ) (t : Fin 3 → ℕ) (pad : ℕ) :
    rayPolynomial P t pad = ∑ e ∈ P.support, rayPolynomial (monomial e (P.coeff e)) t pad := by
  unfold rayPolynomial
  simp only [← MvPolynomial.coe_eval₂Hom]
  conv_lhs => rw [P.as_sum]
  rw [map_sum]

theorem degree_ray_le (P : MvPolynomial (Fin 3) ℚ) (t : Fin 3 → ℕ) (pad : ℕ) :
    (rayPolynomial P t pad).natDegree ≤ P.totalDegree := by
  rw [ray_as_sum]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun e he =>
    (monomial_ray e (P.coeff e) t pad).1.trans (le_totalDegree he)

theorem coeff_ray (P : MvPolynomial (Fin 3) ℚ) (t : Fin 3 → ℕ) (pad : ℕ) {d : ℕ}
    (hd : P.totalDegree ≤ d) :
    (rayPolynomial P t pad).coeff d =
      MvPolynomial.eval (fun i => (t i : ℚ)) (homogeneousComponent d P) := by
  classical
  rw [ray_as_sum, Polynomial.finsetSum_coeff, homogeneousComponent_apply, map_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun e he => ?_
  obtain ⟨hdeg, hcoeff⟩ := monomial_ray e (P.coeff e) t pad
  by_cases hed : e.degree = d
  · simpa [hed] using hcoeff
  · simp only [hed, ↓reduceIte]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (hdeg.trans_lt (lt_of_le_of_ne ((le_totalDegree he).trans hd) hed))

private theorem eq_zero_of_eval_pos_nat (P : MvPolynomial (Fin 3) ℚ)
    (hp : ∀ t : Fin 3 → ℕ, (∀ i, 0 < t i) →
      MvPolynomial.eval (fun i => (t i : ℚ)) P = 0) : P = 0 := by
  let f : ℕ ↪ ℚ := ⟨fun n => ((n + 1 : ℕ) : ℚ), by
    intro a b hab
    exact Nat.add_right_cancel (Nat.cast_injective (R := ℚ) hab)⟩
  let s := (Finset.range (P.totalDegree + 1)).map f
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P (fun _ => s)
  · intro i
    simpa [s] using Nat.lt_succ_of_le (degreeOf_le_totalDegree P i)
  · intro x hx
    have hx' (i : Fin 3) : ∃ n : ℕ, n ∈ Finset.range (P.totalDegree + 1) ∧ f n = x i :=
      Finset.mem_map.mp (hx i)
    choose t _ ht using hx'
    have hcast : (fun i => (((t i + 1 : ℕ) : ℚ))) = x := funext ht
    rw [← hcast]
    exact hp (fun i => t i + 1) (fun _ => Nat.succ_pos _)

theorem degree_le_of_positive_rays (P : MvPolynomial (Fin 3) ℚ) (d : ℕ)
    (h : ∀ t : Fin 3 → ℕ, (∀ i, 0 < t i) → (rayPolynomial P t 0).natDegree ≤ d) :
    P.totalDegree ≤ d := by
  by_contra! hlt
  have hzero : homogeneousComponent P.totalDegree P = 0 := by
    apply eq_zero_of_eval_pos_nat
    intro t ht
    rw [← coeff_ray P t 0 le_rfl]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((h t ht).trans_lt hlt)
  have hsmall : P.totalDegree ≤ P.totalDegree - 1 := by
    apply Finset.sup_le
    intro e he
    change e.degree ≤ P.totalDegree - 1
    have hed : e.degree ≤ P.totalDegree := le_totalDegree he
    suffices e.degree ≠ P.totalDegree by omega
    intro heq
    have hz := congrArg (fun Q : MvPolynomial (Fin 3) ℚ => Q.coeff e) hzero
    exact (mem_support_iff.mp he) (by simpa [coeff_homogeneousComponent, heq] using hz)
  omega

/-- The exponent with the listed coordinates, in order. -/
def exponent (i j k : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![i, j, k]

private theorem exponent_degree (i j k : ℕ) : (exponent i j k).degree = i + j + k := by
  simp [exponent, Finsupp.degree_eq_sum, Fin.sum_univ_three]

private theorem exponent_eq_iff {i j k u v w : ℕ} :
    exponent i j k = exponent u v w ↔ i = u ∧ j = v ∧ k = w := by
  constructor
  · intro h
    exact ⟨congrArg (fun e : Fin 3 →₀ ℕ => e 0) h,
      congrArg (fun e : Fin 3 →₀ ℕ => e 1) h, congrArg (fun e : Fin 3 →₀ ℕ => e 2) h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private theorem exponent_cases {e : Fin 3 →₀ ℕ} (he : e.degree = 2) :
    e = exponent 2 0 0 ∨ e = exponent 0 2 0 ∨ e = exponent 0 0 2 ∨
      e = exponent 1 1 0 ∨ e = exponent 1 0 1 ∨ e = exponent 0 1 1 := by
  have heq {i j k : ℕ} (h : e 0 = i ∧ e 1 = j ∧ e 2 = k) : e = exponent i j k := by
    ext l
    fin_cases l
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  have hs : e 0 + e 1 + e 2 = 2 := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_three] using he
  have hc :
      (e 0 = 2 ∧ e 1 = 0 ∧ e 2 = 0) ∨ (e 0 = 0 ∧ e 1 = 2 ∧ e 2 = 0) ∨
      (e 0 = 0 ∧ e 1 = 0 ∧ e 2 = 2) ∨ (e 0 = 1 ∧ e 1 = 1 ∧ e 2 = 0) ∨
      (e 0 = 1 ∧ e 1 = 0 ∧ e 2 = 1) ∨ (e 0 = 0 ∧ e 1 = 1 ∧ e 2 = 1) := by omega
  rcases hc with hc | hc | hc | hc | hc | hc
  · exact Or.inl (heq hc)
  · exact Or.inr (Or.inl (heq hc))
  · exact Or.inr (Or.inr (Or.inl (heq hc)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (heq hc))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (heq hc)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (heq hc)))))

theorem eval_homogeneous_two (P : MvPolynomial (Fin 3) ℚ) (x : Fin 3 → ℚ) :
    MvPolynomial.eval x (homogeneousComponent 2 P) =
      P.coeff (exponent 2 0 0) * (x 0)^2 + P.coeff (exponent 0 2 0) * (x 1)^2 +
      P.coeff (exponent 0 0 2) * (x 2)^2 +
      P.coeff (exponent 1 1 0) * (x 0) * (x 1) +
      P.coeff (exponent 1 0 1) * (x 0) * (x 2) +
      P.coeff (exponent 0 1 1) * (x 1) * (x 2) := by
  classical
  let m (i j k : ℕ) := monomial (exponent i j k) (P.coeff (exponent i j k))
  have hform : homogeneousComponent 2 P =
      m 2 0 0 + m 0 2 0 + m 0 0 2 + m 1 1 0 + m 1 0 1 + m 0 1 1 := by
    ext e
    simp only [coeff_homogeneousComponent, m, AddMonoidAlgebra.coeff_add]
    by_cases he : e.degree = 2
    · rcases exponent_cases he with he | he | he | he | he | he <;>
        rw [he] <;> norm_num [exponent_degree, exponent_eq_iff]
    · have hne (i j k : ℕ) (hd : i + j + k = 2) : exponent i j k ≠ e := by
        intro h
        exact he (by rw [← h, exponent_degree, hd])
      simp [he, hne 2 0 0 rfl, hne 0 2 0 rfl, hne 0 0 2 rfl,
        hne 1 1 0 rfl, hne 1 0 1 rfl, hne 0 1 1 rfl]
  have heval (i j k : ℕ) :
      MvPolynomial.eval x (m i j k) =
        P.coeff (exponent i j k) * (x 0 ^ i * x 1 ^ j * x 2 ^ k) := by
    change MvPolynomial.eval x (monomial (exponent i j k) (P.coeff (exponent i j k))) = _
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp [Fin.prod_univ_three, exponent, mul_assoc]
  simp [hform, heval, mul_assoc]

end

end K1_13_6_1_4_2_2
end PackSource_K1_13_6_1_4_2_2Aux2

section PackSource_K1_13_6_1_4_2_2Aux1
set_option autoImplicit true
namespace K1_13_6_1_4_2_2

noncomputable section

open K1_13 K1_13_6 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_7_1 MvPolynomial

/-- Componentwise cap comparison. -/
def CapsLE (p q : Shape) : Prop :=
  p.b ≤ q.b ∧ p.j ≤ q.j ∧ p.t ≤ q.t

private theorem lattice_mono {p q : Shape} (hpq : CapsLE p q) :
    latticeIndices p ⊆ latticeIndices q := by
  intro e he
  obtain ⟨hb, hj, ht⟩ := hpq
  exact ⟨he.1.trans (Nat.mul_le_mul_left 6 hb),
    he.2.1.trans (Nat.mul_le_mul_left 6 hj), he.2.2.trans (Nat.mul_le_mul_left 6 ht)⟩

theorem boxHilbert_mono (surface : Ideal GeoJets) {p q : Shape} (hpq : CapsLE p q) :
    boxHilbert surface p ≤ boxHilbert surface q := by
  let := restrictSupport_finite (R := GeoField) (Set.toFinite (latticeIndices q))
  exact Submodule.finrank_mono (Submodule.map_mono (restrictSupport_mono GeoField (lattice_mono hpq)))

theorem combined_chamber {a b h : Shape} (ha : Chamber a) (hb : Chamber b) (hh : Chamber h)
    (t : Fin 3 → ℕ) : Chamber (combinedShape a b h t) :=
  chamber_plus (chamber_plus (chamber_scale ha _) (chamber_scale hb _)) (chamber_scale hh _)

theorem combined_full {a b h : Shape} (ha : FullChamber a) (hb : FullChamber b) (hh : FullChamber h)
    {t : Fin 3 → ℕ} (ht : 0 < t 0 + t 1 + t 2) : FullChamber (combinedShape a b h t) := by
  refine ⟨combined_chamber ha.1 hb.1 hh.1 t, ?_⟩
  change 0 < t 0 * a.t + t 1 * b.t + t 2 * h.t
  by_cases h0 : 0 < t 0
  · have := Nat.mul_pos h0 ha.2
    omega
  by_cases h1 : 0 < t 1
  · have := Nat.mul_pos h1 hb.2
    omega
  have := Nat.mul_pos (show 0 < t 2 by omega) hh.2
  omega

theorem combined_pad (a b h : Shape) (t : Fin 3 → ℕ) (n pad : ℕ) :
    combinedShape a b h (fun l => n * t l + pad) =
      ((combinedShape a b h t).scale n).plus ((combinedShape a b h (fun _ => 1)).scale pad) := by
  cases a
  cases b
  cases h
  simp only [combinedShape, Shape.scale, Shape.plus, Nat.one_mul]
  congr 1 <;> ring

theorem boxHilbert_pad (surface : Ideal GeoJets) {p q : Shape}
    (hp : FullChamber p) (hq : Chamber q) (n pad : ℕ) :
    boxHilbert surface (p.scale n) ≤ boxHilbert surface ((p.scale n).plus (q.scale pad)) ∧
      boxHilbert surface ((p.scale n).plus (q.scale pad)) ≤
        boxHilbert surface (p.scale (n + pad * q.b)) := by
  have ht : 0 < p.t := hp.2
  have hj : 0 < p.j := by have := hp.1.2; omega
  have hb : 0 < p.b := hj.trans_le hp.1.1
  have hqt : q.t ≤ q.b := by have := hq.1; have := hq.2; omega
  constructor
  · apply boxHilbert_mono
    exact ⟨Nat.le_add_right .., Nat.le_add_right .., Nat.le_add_right ..⟩
  · apply boxHilbert_mono
    dsimp [CapsLE, Shape.scale, Shape.plus]
    simp only [Nat.add_mul]
    exact ⟨Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hb) _,
      Nat.add_le_add_left ((Nat.mul_le_mul_left _ hq.1).trans (Nat.le_mul_of_pos_right _ hj)) _,
      Nat.add_le_add_left ((Nat.mul_le_mul_left _ hqt).trans (Nat.le_mul_of_pos_right _ ht)) _⟩

def boxIdeal (surface : Ideal GeoJets) (p : Shape) : Ideal (MvPolynomial (latticeIndices p) GeoField) :=
  surface.comap (monomialMap GeoField (latticeIndices p)).toRingHom

theorem boxHilbert_scale (surface : Ideal GeoJets) {p : Shape} (hp : Chamber p) (n : ℕ) :
    boxHilbert surface (p.scale n) = affineHilbertFunction (boxIdeal surface p) n := by
  let φ := monomialMap GeoField (latticeIndices p)
  let I := boxIdeal surface p
  let g : (MvPolynomial (latticeIndices p) GeoField ⧸ I) →ₐ[GeoField] (GeoJets ⧸ surface) :=
    Ideal.quotientMapₐ surface φ le_rfl
  have hg : Function.Injective g := Ideal.quotientMap_injective
  have hcomp : g.toLinearMap.comp (Ideal.Quotient.mkₐ GeoField I).toLinearMap =
      (Ideal.Quotient.mkₐ GeoField surface).toLinearMap.comp φ.toLinearMap := by
    ext x
    rfl
  unfold boxHilbert
  rw [← monomialMap_filtration hp, ← Submodule.map_comp, ← hcomp, Submodule.map_comp]
  exact (Submodule.equivMapOfInjective _ hg (quotientDegreeLE I n)).finrank_eq.symm

theorem boxHilbert_degree (surface : Ideal GeoJets) {p : Shape}
    (hdim : ringKrullDim (GeoJets ⧸ surface) = 2) (hp : FullChamber p) :
    (affineHilbertPolynomial (boxIdeal surface p)).natDegree ≤ 2 := by
  let φ := monomialMap GeoField (latticeIndices p)
  have hφ : Function.Surjective φ := monomialMap_surjective (latticeIndices_single hp)
  exact (natDegree_affineHilbertPolynomial_comap_of_surjective φ hφ surface).trans_le
    (K1_13_6_2_4_2.hilbert_degree_le (d := 2) hdim.le)

end

end K1_13_6_1_4_2_2
end PackSource_K1_13_6_1_4_2_2Aux1

section PackSource_K1_13_6_1_4_2_2Split
set_option autoImplicit true
namespace K1_13_6_1_4_2_2

noncomputable section

open Filter K1_13 K1_13_6 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_7_1 MvPolynomial

/-- The exact multigraded dimensions count standard monomials of the common
monomial presentation, with one finite collection of forbidden exponents. -/
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) (a b h : Shape),
    Chamber a → Chamber b → Chamber h →
    ∃ forbidden : Finset (SectionVariable a b h →₀ ℕ),
      ∀ t : Fin 3 → ℕ,
        multiHilbert surface a b h t = standardCount (fun v => v.1) forbidden t

/-- An exact-degree count outside finitely many monomial cones is eventually
a polynomial on a coordinatewise tail of the multidegrees. -/
def c2 : Prop :=
  ∀ {σ : Type} [Finite σ] (block : σ → Fin 3), Function.Surjective block →
    ∀ forbidden : Finset (σ →₀ ℕ),
      ∃ (P : MvPolynomial (Fin 3) ℚ) (N : ℕ),
        ∀ t : Fin 3 → ℕ, (∀ l, N ≤ t l) →
          MvPolynomial.eval (fun l => (t l : ℚ)) P = (standardCount block forbidden t : ℚ)

private theorem combined_scale (a b h : Shape) (t : Fin 3 → ℕ) (n : ℕ) :
    combinedShape a b h (fun l => n * t l) = (combinedShape a b h t).scale n := by
  simpa [Shape.scale, Shape.plus] using combined_pad a b h t n 0

private theorem polynomial_degree (surface : Ideal GeoJets) {a b h : Shape}
    (hdim : ringKrullDim (GeoJets ⧸ surface) = 2)
    (ha : FullChamber a) (hb : FullChamber b) (hh : FullChamber h)
    (P : MvPolynomial (Fin 3) ℚ) (N : ℕ)
    (hP : ∀ t : Fin 3 → ℕ, (∀ l, N ≤ t l) →
      MvPolynomial.eval (fun l => (t l : ℚ)) P = (multiHilbert surface a b h t : ℚ)) :
    P.totalDegree ≤ 2 := by
  apply degree_le_of_positive_rays
  intro t ht
  let p := combinedShape a b h t
  have hp : FullChamber p := combined_full ha hb hh (by have := ht 0; omega)
  have hpol : rayPolynomial P t 0 = affineHilbertPolynomial (boxIdeal surface p) := by
    apply Polynomial.eq_of_eventually_atTop_eval_natCast_eq
    filter_upwards [eventually_ge_atTop N, eventually_eval_affineHilbertPolynomial (boxIdeal surface p)]
      with n hn hH
    have htail (l : Fin 3) : N ≤ n * t l + 0 :=
      hn.trans (Nat.le_mul_of_pos_right n (ht l))
    rw [eval_rayPolynomial, hP _ htail, hH, multiHilbert]
    simp only [Nat.add_zero, combined_scale]
    rw [boxHilbert_scale surface hp.1]
  rw [hpol]
  exact boxHilbert_degree surface hdim hp

private theorem diagonal_coeff (surface : Ideal GeoJets) {a b h : Shape}
    (hdim : ringKrullDim (GeoJets ⧸ surface) = 2)
    (ha : FullChamber a) (hb : FullChamber b) (hh : FullChamber h)
    (P : MvPolynomial (Fin 3) ℚ) (N : ℕ) (hdeg : P.totalDegree ≤ 2)
    (hP : ∀ t : Fin 3 → ℕ, (∀ l, N ≤ t l) →
      MvPolynomial.eval (fun l => (t l : ℚ)) P = (multiHilbert surface a b h t : ℚ))
    (t : Fin 3 → ℕ) (ht : 0 < t 0 + t 1 + t 2) :
    (affineHilbertPolynomial (boxIdeal surface (combinedShape a b h t))).coeff 2 =
      (rayPolynomial P t N).coeff 2 := by
  let p := combinedShape a b h t
  let q := combinedShape a b h (fun _ => 1)
  let S := affineHilbertPolynomial (boxIdeal surface p)
  let R := rayPolynomial P t N
  let d := N * q.b
  have hp : FullChamber p := combined_full ha hb hh ht
  have hq : Chamber q := combined_chamber ha.1 hb.1 hh.1 _
  have hSdeg := boxHilbert_degree surface hdim hp
  have hRdeg : R.natDegree ≤ 2 := (degree_ray_le P t N).trans hdeg
  obtain ⟨M, hM⟩ := exists_eval_affineHilbertPolynomial (boxIdeal surface p)
  have hS (n : ℕ) (hn : M ≤ n) :
      S.eval (n : ℚ) = (boxHilbert surface (p.scale n) : ℚ) := by
    exact (hM n hn).trans (congrArg Nat.cast (boxHilbert_scale surface hp.1 n).symm)
  have hR (n : ℕ) :
      R.eval (n : ℚ) = (boxHilbert surface ((p.scale n).plus (q.scale N)) : ℚ) := by
    rw [show R = rayPolynomial P t N from rfl, eval_rayPolynomial,
      hP _ (fun l => Nat.le_add_left N (n * t l)), multiHilbert, combined_pad]
  have hbounds : ∀ᶠ n : ℕ in atTop,
      S.eval (n : ℚ) ≤ R.eval (n : ℚ) ∧
        R.eval (n : ℚ) ≤ (Polynomial.taylor (d : ℚ) S).eval (n : ℚ) := by
    filter_upwards [eventually_ge_atTop M] with n hn
    have hs : (Polynomial.taylor (d : ℚ) S).eval (n : ℚ) = S.eval ((n + d : ℕ) : ℚ) := by
      rw [Polynomial.taylor_apply, Polynomial.eval_comp]
      simp [Nat.cast_add]
    rw [hs, hS n hn, hR n, hS (n + d) (hn.trans (Nat.le_add_right n d))]
    obtain ⟨hlo, hhi⟩ := boxHilbert_pad surface hp hq n N
    exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  have hlo := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hSdeg hRdeg
    (hbounds.mono fun _ hn => hn.1)
  have hshift : (Polynomial.taylor (d : ℚ) S).natDegree ≤ 2 := by
    simpa only [Polynomial.natDegree_taylor] using hSdeg
  have hhi := Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hRdeg hshift
    (hbounds.mono fun _ hn => hn.2)
  rw [Polynomial.coeff_taylor_of_natDegree_le _ hSdeg] at hhi
  exact le_antisymm hlo hhi

theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1_4_2.c2 := by
  intro surface a b h _ hdim ha hb hh
  obtain ⟨forbidden, hcount⟩ := h1 surface a b h ha.1 hb.1 hh.1
  let block : SectionVariable a b h → Fin 3 := fun v => v.1
  have hblock : Function.Surjective block := by
    intro l
    exact ⟨⟨l, ⟨0, latticeIndices_zero _⟩⟩, rfl⟩
  obtain ⟨P, N, hP⟩ := h2 block hblock forbidden
  have hval (t : Fin 3 → ℕ) (ht : ∀ l, N ≤ t l) :
      MvPolynomial.eval (fun l => (t l : ℚ)) P = (multiHilbert surface a b h t : ℚ) := by
    rw [hcount]
    exact hP t ht
  have hdeg := polynomial_degree surface hdim ha hb hh P N hval
  refine ⟨P.coeff (exponent 2 0 0), P.coeff (exponent 0 2 0), P.coeff (exponent 0 0 2),
    P.coeff (exponent 1 1 0), P.coeff (exponent 1 0 1), P.coeff (exponent 0 1 1), ?_⟩
  intro i j k hijk
  let t : Fin 3 → ℕ := ![i, j, k]
  change (affineHilbertPolynomial (boxIdeal surface (combinedShape a b h t))).coeff 2 = _
  rw [diagonal_coeff surface hdim ha hb hh P N hdeg hval t hijk, coeff_ray P t N hdeg,
    eval_homogeneous_two]
  rfl

end

end K1_13_6_1_4_2_2
end PackSource_K1_13_6_1_4_2_2Split

section PackSource_K1_13_6_1_4_2_2_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_4_2_2_1

noncomputable section

open K1_13 K1_13_6 K1_13_6_1_4_2 K1_13_6_1_4_2_2 K1_13_6_2_3_2 MvPolynomial
open K1_13_7_1 (Chamber)
open scoped Pointwise

attribute [local instance] MvPolynomial.weightedGradedAlgebra

private theorem weight_eq_blockDegree {σ : Type} (block : σ → Fin 3) (e : σ →₀ ℕ) :
    Finsupp.weight (step ∘ block) e = blockDegree block e := by
  funext i
  simp only [Finsupp.weight_apply, blockDegree, Finsupp.sum, Finset.sum_apply, step, Function.comp_apply,
    Pi.smul_apply, Pi.single_apply]
  apply Finset.sum_congr rfl
  intro v _
  split <;> simp_all [eq_comm]

private theorem combined_add (a b h : Shape) (s t : Fin 3 → ℕ) :
    combinedShape a b h (s + t) = (combinedShape a b h s).plus (combinedShape a b h t) := by
  simp only [combinedShape, Shape.scale, Shape.plus, Pi.add_apply]
  congr 1 <;> ring

private theorem combined_slot (a b h : Shape) (i : Fin 3) (n : ℕ) :
    combinedShape a b h (n • step i) = (![a, b, h] i).scale n := by
  fin_cases i <;> simp [combinedShape, Shape.scale, Shape.plus, step, Pi.smul_apply]

private def exponentsMap (a b h : Shape) : (SectionVariable a b h →₀ ℕ) →+ (Fin 4 →₀ ℕ) :=
  Finsupp.weight fun v => v.2.val

private theorem exponent_mem {a b h : Shape} (ha : Chamber a) (hb : Chamber b)
    (hh : Chamber h) (e : SectionVariable a b h →₀ ℕ) :
    exponentsMap a b h e ∈
      latticeIndices (combinedShape a b h (Finsupp.weight (step ∘ fun v => v.1) e)) := by
  induction e using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using latticeIndices_zero (combinedShape a b h 0)
  | add e f he hf =>
      rw [map_add, map_add, combined_add,
        latticeIndices_plus (combined_chamber ha hb hh _) (combined_chamber ha hb hh _)]
      exact Set.add_mem_add he hf
  | single v n =>
      rw [Finsupp.weight_single, Function.comp_apply, combined_slot]
      have hch (i : Fin 3) : Chamber (![a, b, h] i) := by
        fin_cases i
        exacts [ha, hb, hh]
      rw [latticeIndices_scale (hch v.1), exponentsMap, Finsupp.weight_single]
      induction n with
      | zero => simp
      | succ n ih =>
          rw [succ_nsmul, succ_nsmul]
          exact Set.add_mem_add ih v.2.property

private theorem exponent_lift_slot {a b h : Shape} (i : Fin 3) (n : ℕ)
    {m : Fin 4 →₀ ℕ} (hm : m ∈ n • latticeIndices (![a, b, h] i)) :
    ∃ e : SectionVariable a b h →₀ ℕ,
      Finsupp.weight (step ∘ fun v => v.1) e = n • step i ∧ exponentsMap a b h e = m := by
  induction n generalizing m with
  | zero =>
      rw [zero_smul, Set.mem_zero] at hm
      subst m
      exact ⟨0, by simp, map_zero _⟩
  | succ n ih =>
      rw [succ_nsmul] at hm
      obtain ⟨u, hu, v, hv, rfl⟩ := hm
      obtain ⟨e, he, hexp⟩ := ih hu
      let w : SectionVariable a b h := ⟨i, ⟨v, hv⟩⟩
      refine ⟨e + Finsupp.single w 1, ?_, ?_⟩
      · rw [map_add, Finsupp.weight_single, one_smul, he, succ_nsmul]
        rfl
      · rw [map_add, hexp, exponentsMap, Finsupp.weight_single, one_smul]

private theorem exponent_lift {a b h : Shape} (ha : Chamber a) (hb : Chamber b)
    (hh : Chamber h) (t : Fin 3 → ℕ) {m : Fin 4 →₀ ℕ}
    (hm : m ∈ latticeIndices (combinedShape a b h t)) :
    ∃ e : SectionVariable a b h →₀ ℕ,
      Finsupp.weight (step ∘ fun v => v.1) e = t ∧ exponentsMap a b h e = m := by
  rw [combinedShape, latticeIndices_plus (chamber_plus (chamber_scale ha _) (chamber_scale hb _))
    (chamber_scale hh _), latticeIndices_plus (chamber_scale ha _) (chamber_scale hb _),
    latticeIndices_scale ha, latticeIndices_scale hb, latticeIndices_scale hh] at hm
  obtain ⟨_, ⟨u, hu, v, hv, rfl⟩, w, hw, rfl⟩ := hm
  obtain ⟨e₀, h₀, h₀'⟩ := exponent_lift_slot (a := a) (b := b) (h := h) 0 (t 0) hu
  obtain ⟨e₁, h₁, h₁'⟩ := exponent_lift_slot (a := a) (b := b) (h := h) 1 (t 1) hv
  obtain ⟨e₂, h₂, h₂'⟩ := exponent_lift_slot (a := a) (b := b) (h := h) 2 (t 2) hw
  refine ⟨e₀ + e₁ + e₂, ?_, by rw [map_add, map_add, h₀', h₁', h₂']⟩
  rw [map_add, map_add, h₀, h₁, h₂]
  funext i
  fin_cases i <;> simp [step]

private def sectionMap (a b h : Shape) :
    MvPolynomial (SectionVariable a b h) GeoField →ₐ[GeoField] GeoJets :=
  aeval fun v => monomial v.2.val 1

private theorem sectionMap_monomial (a b h : Shape) (e : SectionVariable a b h →₀ ℕ) :
    sectionMap a b h (monomial e 1) = monomial (exponentsMap a b h e) 1 := by
  rw [sectionMap, aeval_monomial, Finsupp.prod, exponentsMap, Finsupp.weight_apply, Finsupp.sum]
  simp only [monomial_pow, one_pow, ← monomial_sum_one, algebraMap_eq, C_mul_monomial, mul_one]

private theorem section_image {a b h : Shape} (ha : Chamber a) (hb : Chamber b)
    (hh : Chamber h) (t : Fin 3 → ℕ) :
    (weightedHomogeneousSubmodule GeoField (step ∘ fun v : SectionVariable a b h => v.1) t).map
      (sectionMap a b h).toLinearMap =
      restrictSupport GeoField (latticeIndices (combinedShape a b h t)) := by
  have hS : weightedHomogeneousSubmodule GeoField (step ∘ fun v : SectionVariable a b h => v.1) t =
      restrictSupport GeoField {e | Finsupp.weight (step ∘ fun v => v.1) e = t} :=
    weightedHomogeneousSubmodule_eq_finsupp_supported _ _ _
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, hS, restrictSupport_eq_span, Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    change sectionMap a b h (monomial e 1) ∈
      restrictSupport GeoField (latticeIndices (combinedShape a b h t))
    rw [sectionMap_monomial, monomial_mem_restrictSupport]
    exact Or.inl ((show Finsupp.weight (step ∘ fun v => v.1) e = t from he) ▸
      exponent_mem ha hb hh e)
  · rw [restrictSupport_eq_span, Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨e, he, rfl⟩ := exponent_lift ha hb hh t hm
    exact ⟨monomial e 1, isWeightedHomogeneous_monomial _ _ _ he, sectionMap_monomial a b h e⟩

private def degreeLexOrder (σ : Type) [Finite σ] : MonomialOrder σ := by
  let _ := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  exact MonomialOrder.degLex

/-- The homogeneous core imposes exactly the surface relations in each
degree. This keeps different degrees separate even if their affine images coincide. -/
theorem proof : K1_13_6_1_4_2_2.c1 := by
  classical
  intro surface a b h ha hb hh
  let σ := SectionVariable a b h
  let block : σ → Fin 3 := Sigma.fst
  let S := weightedHomogeneousSubmodule GeoField (step ∘ block)
  let φ := sectionMap a b h
  let C := surface.comap φ
  let J := (C.homogeneousCore S).toIdeal
  have hhom : J.IsHomogeneous S := (C.homogeneousCore S).isHomogeneous
  have hgraded : Graded block J :=
    fun _ hp t => weightedHomogeneousComponent_mem_of_mem _ _ hhom hp t
  let order := degreeLexOrder σ
  obtain ⟨forbidden, hf⟩ := order.exists_finset_standardExponents_iff J
  refine ⟨forbidden, fun t => ?_⟩
  let W := (S t).map (Ideal.Quotient.mkₐ GeoField J).toLinearMap
  let f := Ideal.quotientMapₐ surface φ (Ideal.toIdeal_homogeneousCore_le S C)
  have hinj : Function.Injective (f.toLinearMap.domRestrict W) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨x, hx⟩ hx0
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    change Ideal.Quotient.mk surface (φ p) = 0 at hx0
    have hpsurface : φ p ∈ surface := Ideal.Quotient.eq_zero_iff_mem.mp hx0
    have hpJ : p ∈ J := Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨t, hp⟩
      (show p ∈ C from hpsurface)
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr hpJ)
  have himage : W.map f.toLinearMap =
      (restrictSupport GeoField (latticeIndices (combinedShape a b h t))).map
        (Ideal.Quotient.mkₐ GeoField surface).toLinearMap := by
    rw [← section_image ha hb hh]
    simp only [W, ← Submodule.map_comp, ← AlgHom.comp_toLinearMap, f]
    rfl
  have hrank : Module.finrank GeoField W = multiHilbert surface a b h t := by
    change _ = boxHilbert surface (combinedShape a b h t)
    rw [boxHilbert, ← himage, ← LinearMap.range_domRestrict W f.toLinearMap]
    exact (LinearEquiv.ofInjective _ hinj).finrank_eq
  have hs :
      ({e | e ∈ order.standardExponents J ∧ Finsupp.weight (step ∘ block) e = t} :
        Set (σ →₀ ℕ)) =
      {e | blockDegree block e = t ∧ ∀ u ∈ forbidden, ¬ u ≤ e} := by
    ext e
    simp only [Set.mem_ofPred_eq, hf, weight_eq_blockDegree, and_comm]
  have hcount : hilbert block J t = (standardCount block forbidden t : ℚ) := by
    simpa only [hs, standardCount] using standard_rank block order J hgraded t
  change (Module.finrank GeoField W : ℚ) = _ at hcount
  rw [hrank] at hcount
  exact_mod_cast hcount

end

end K1_13_6_1_4_2_2_1
end PackSource_K1_13_6_1_4_2_2_1Proof

section PackSource_K1_13_6_1_4_2_2_2Proof
set_option autoImplicit true
namespace K1_13_6_1_4_2_2_2

noncomputable section

open Finset K1_13_6_1_4_2_2
open scoped BigOperators

private abbrev Block {σ : Type} (block : σ → Fin 3) (l : Fin 3) :=
  {v : σ // block v = l}

private abbrev Exact {σ : Type} (block : σ → Fin 3) (t : Fin 3 → ℕ) :=
  {e : σ →₀ ℕ // blockDegree block e = t}

section Count

variable {σ : Type} [Fintype σ] (block : σ → Fin 3)
  [∀ l, Fintype (Block block l)]

private theorem degree_eq_sum (e : σ →₀ ℕ) (l : Fin 3) :
    blockDegree block e l = ∑ v : Block block l, e v := by
  change e.sum (fun v n => if block v = l then n else 0) = _
  rw [Finsupp.sum_fintype _ _ (fun v => by simp), ← sum_filter]
  exact sum_subtype _ (by simp) _

private theorem degree_add (e f : σ →₀ ℕ) (l : Fin 3) :
    blockDegree block (e + f) l = blockDegree block e l + blockDegree block f l := by
  simp only [degree_eq_sum, Finsupp.add_apply, sum_add_distrib]

private theorem degree_mono {e f : σ →₀ ℕ} (hef : e ≤ f) (l : Fin 3) :
    blockDegree block e l ≤ blockDegree block f l := by
  simp only [degree_eq_sum]
  exact sum_le_sum fun v _ => Finsupp.le_def.mp hef v

/-- An exact multidegree specifies an independent antidiagonal in each block. -/
private def exactEquiv [DecidableEq σ] (t : Fin 3 → ℕ) :
    Exact block t ≃ ∀ l : Fin 3, (univ : Finset (Block block l)).finsuppAntidiag (t l) where
  toFun e l := ⟨Finsupp.equivFunOnFinite.symm (fun v => e.1 (v : σ)), by
    rw [mem_finsuppAntidiag]
    exact ⟨(degree_eq_sum block e.1 l).symm.trans (congrFun e.2 l), subset_univ _⟩⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun v => (f (block v)).1 ⟨v, rfl⟩), by
    funext l
    rw [degree_eq_sum]
    calc
      _ = ∑ v : Block block l, (f l).1 v := by
        apply sum_congr rfl
        rintro ⟨v, hv⟩ -
        subst l
        rfl
      _ = t l := (mem_finsuppAntidiag.mp (f l).2).1⟩
  left_inv e := by
    apply Subtype.ext
    ext v
    rfl
  right_inv f := by
    funext l
    apply Subtype.ext
    ext v
    obtain ⟨v, hv⟩ := v
    subst l
    rfl

private theorem exact_card [DecidableEq σ] (hblock : Function.Surjective block) (t : Fin 3 → ℕ) :
    Nat.card (Exact block t) =
      ∏ l : Fin 3, (t l + (Fintype.card (Block block l) - 1)).choose
        (Fintype.card (Block block l) - 1) := by
  rw [Nat.card_congr (exactEquiv block t), Nat.card_eq_fintype_card, Fintype.card_pi]
  refine prod_congr rfl fun l _ => ?_
  rw [Fintype.card_coe, card_finsuppAntidiag_nat_eq_choose, card_univ]
  obtain ⟨v, hv⟩ := hblock l
  have hpos : 0 < Fintype.card (Block block l) :=
    Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
  have hadd : Fintype.card (Block block l) + t l - 1 =
      t l + (Fintype.card (Block block l) - 1) := by omega
  exact (Nat.choose_symm_of_eq_add hadd).trans (by rw [hadd])

/-- Removing the cone vertex subtracts its degree in each block. -/
private def coneEquiv (s : σ →₀ ℕ) (t : Fin 3 → ℕ)
    (hs : ∀ l, blockDegree block s l ≤ t l) :
    {e : σ →₀ ℕ // blockDegree block e = t ∧ s ≤ e} ≃
      Exact block (fun l => t l - blockDegree block s l) where
  toFun e := ⟨e.1 - s, by
    funext l
    have hadd := congrArg (fun f => blockDegree block f l) (tsub_add_cancel_of_le e.2.2)
    rw [degree_add, congrFun e.2.1 l] at hadd
    change blockDegree block (e.1 - s) l = t l - blockDegree block s l
    omega⟩
  invFun u := ⟨u.1 + s, ⟨by
    funext l
    rw [degree_add, congrFun u.2 l]
    exact Nat.sub_add_cancel (hs l), le_add_self⟩⟩
  left_inv e := Subtype.ext (tsub_add_cancel_of_le e.2.2)
  right_inv u := Subtype.ext (add_tsub_cancel_right u.1 s)

end Count

/-- A filter on the finite exact-degree type computes the corresponding set cardinality. -/
private theorem exact_filter_card {σ : Type} (block : σ → Fin 3) (t : Fin 3 → ℕ)
    [Fintype (Exact block t)] (p : (σ →₀ ℕ) → Prop) [DecidablePred p] :
    #(univ.filter fun e : Exact block t => p e.1) =
      ({e | blockDegree block e = t ∧ p e} : Set (σ →₀ ℕ)).ncard := by
  rw [← Nat.card_coe_set_eq]
  calc
    _ = Nat.card ↥(univ.filter fun e : Exact block t => p e.1) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = _ := Nat.card_congr
      { toFun := fun e => ⟨e.1.1, e.1.2, (mem_filter.mp e.2).2⟩
        invFun := fun e => ⟨⟨e.1, e.2.1⟩, mem_filter.mpr ⟨mem_univ _, e.2.2⟩⟩
        left_inv := fun e => Subtype.ext rfl
        right_inv := fun e => Subtype.ext rfl }

private theorem eval_blockPoly (t : Fin 3 → ℕ) (l : Fin 3) (d k : ℕ)
    (hk : k ≤ t l) :
    MvPolynomial.eval (fun l => (t l : ℚ))
        (Polynomial.aeval (MvPolynomial.X l) (Polynomial.preHilbertPoly ℚ d k)) =
      ((t l - k + d).choose d : ℚ) := by
  change MvPolynomial.aeval (fun i => (t i : ℚ))
    (Polynomial.aeval (MvPolynomial.X l) (Polynomial.preHilbertPoly ℚ d k)) = _
  rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
  change (Polynomial.preHilbertPoly ℚ d k).eval (t l : ℚ) = _
  rw [Polynomial.preHilbertPoly_eq_choose_add_sub ℚ d (hk.trans (Nat.le_add_right _ _)),
    Nat.sub_add_comm hk]

/-- The signed sum over forbidden subsets gives a counting polynomial on the common tail. -/
theorem proof : K1_13_6_1_4_2_2.c2 := by
  classical
  intro σ hσ block hblock forbidden
  let : Fintype σ := Fintype.ofFinite σ
  let (l : Fin 3) : Fintype (Block block l) := Fintype.ofFinite _
  let d (l : Fin 3) := Fintype.card (Block block l) - 1
  let N := univ.sup (blockDegree block (forbidden.sup id))
  let P : MvPolynomial (Fin 3) ℚ :=
    ∑ U ∈ forbidden.powerset,
      MvPolynomial.C ((-1 : ℚ) ^ #U) *
        ∏ l : Fin 3, Polynomial.aeval (MvPolynomial.X l)
          (Polynomial.preHilbertPoly ℚ (d l) (blockDegree block (U.sup id) l))
  refine ⟨P, N, ?_⟩
  intro t ht
  let : Fintype (Exact block t) := Fintype.ofEquiv _ (exactEquiv block t).symm
  let cone (s : σ →₀ ℕ) : Finset (Exact block t) := univ.filter fun e => s ≤ e.1
  have hinter (U : Finset (σ →₀ ℕ)) : U.inf cone = cone (U.sup id) := by
    ext e
    simp only [Finset.mem_inf, cone, mem_filter, mem_univ, true_and, Finset.sup_le_iff, id]
  have havoid : (forbidden.inf fun s => (cone s)ᶜ) =
      univ.filter (fun e : Exact block t => ∀ s ∈ forbidden, ¬ s ≤ e.1) := by
    ext e
    simp only [Finset.mem_inf, mem_compl, cone, mem_filter, mem_univ, true_and]
  have hcard : (#(forbidden.inf fun s => (cone s)ᶜ) : ℚ) =
      (standardCount block forbidden t : ℚ) := by
    rw [havoid]
    exact congrArg (fun n : ℕ => (n : ℚ))
      (exact_filter_card block t (fun e => ∀ s ∈ forbidden, ¬ s ≤ e))
  have hie := congrArg (Int.cast : ℤ → ℚ)
    (inclusion_exclusion_card_inf_compl forbidden cone)
  push_cast at hie
  simp only [P, map_sum, map_mul, MvPolynomial.eval_C, map_prod]
  rw [← hcard, hie]
  refine sum_congr rfl fun U hU => ?_
  have hshift (l : Fin 3) : blockDegree block (U.sup id) l ≤ t l := by
    exact (degree_mono block (sup_mono (mem_powerset.mp hU)) l).trans
      ((le_sup (f := blockDegree block (forbidden.sup id)) (mem_univ l)).trans (ht l))
  congr 1
  rw [hinter, show #(cone (U.sup id)) =
      Nat.card {e : σ →₀ ℕ // blockDegree block e = t ∧ U.sup id ≤ e} from
        exact_filter_card block t _,
    Nat.card_congr (coneEquiv block (U.sup id) t hshift), exact_card block hblock _]
  push_cast
  exact prod_congr rfl fun l _ => eval_blockPoly t l _ _ (hshift l)

end

end K1_13_6_1_4_2_2_2
end PackSource_K1_13_6_1_4_2_2_2Proof

section PackSource_K1_13_6_1_2Local
set_option autoImplicit true
namespace K1_13_6_1_2

noncomputable section

open K1_13 K1_13_6

/-- A geometric minimal prime of a proper two-equation intersection has height two. -/
theorem pair_height {f Q : GeoJets} {p : Ideal GeoJets}
    (hf : f ≠ 0) (hrel : IsRelPrime f Q) (hp : (Ideal.span {f, Q}).IsMinimalPrime p) :
    p.height = 2 := by
  let _ : p.IsPrime := hp.isPrime
  have hcount : ({f, Q} : Set GeoJets).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by simp)
  have hupper : p.height ≤ 2 :=
    (Ideal.height_le_ncard_of_mem_minimalPrimes_span (by simp) hp).trans (by exact_mod_cast hcount)
  have hfmem : f ∈ p := hp.le (Ideal.subset_span (by simp))
  have hQmem : Q ∈ p := hp.le (Ideal.subset_span (by simp))
  have hpbot : p ≠ ⊥ := fun h => hf (Ideal.mem_bot.mp (h ▸ hfmem))
  have hone : 1 ≤ p.height := by
    have h := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hpbot)
    simpa [Ideal.height_bot] using h
  have hnot : p.height ≠ 1 := by
    intro h
    obtain ⟨z, hz⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one h).principal
    change p = Ideal.span {z} at hz
    have hzf : z ∣ f := Ideal.mem_span_singleton.mp (hz ▸ hfmem)
    have hzQ : z ∣ Q := Ideal.mem_span_singleton.mp (hz ▸ hQmem)
    exact hp.isPrime.ne_top (hz.trans (Ideal.span_singleton_eq_top.mpr (hrel hzf hzQ)))
  exact le_antisymm hupper ((ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr
    (lt_of_le_of_ne hone (Ne.symm hnot)))

/-- In a local ring of dimension at least two, the quotient by an anchor
and a cutter has length at least the maximal-ideal order of the cutter. -/
private theorem length_ge_order {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x y : R} {n : ℕ} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hh : 1 < (IsLocalRing.maximalIdeal R).height)
    (hy : y ∈ IsLocalRing.maximalIdeal R ^ n) :
    (n : ℕ∞) ≤ Module.length R (R ⧸ Ideal.span {x, y}) := by
  let m := IsLocalRing.maximalIdeal R
  let A : Ideal R := Ideal.span {x}
  have hno (i : ℕ) : ¬ m ^ i ≤ A := by
    intro h
    have hmin : m ∈ A.minimalPrimes := by
      refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem m).mpr hx⟩, ?_⟩
      intro P hP _
      exact fun z hz => hP.1.mem_of_pow_mem i (hP.2 (h (Ideal.pow_mem_pow hz i)))
    let _ : A.IsPrincipal := ⟨⟨x, rfl⟩⟩
    exact (not_le_of_gt hh)
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing A hmin)
  let I (i : ℕ) : Ideal R := A ⊔ m ^ i
  have hstep (i : ℕ) : I (i + 1) < I i := by
    refine lt_of_le_of_ne (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ i)) _) ?_
    intro he
    apply hno i
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := m) (IsNoetherian.noetherian _)
    · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · change m ^ i ≤ A ⊔ m • m ^ i
      rw [smul_eq_mul, ← pow_succ']
      change m ^ i ≤ I (i + 1)
      rw [he]
      exact le_sup_right
  have hcoheight (i : ℕ) : (i : ℕ∞) ≤ Order.coheight (I i : Submodule R R) := by
    induction i with
    | zero => simp
    | succ i ih =>
        rw [Nat.cast_succ]
        exact (add_le_add_left ih 1).trans
          (Order.coheight_add_one_le (show (I (i + 1) : Submodule R R) < I i from hstep i))
  rw [Module.length_quotient]
  apply (hcoheight n).trans
  apply Order.coheight_anti
  apply Ideal.span_le.mpr
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨Ideal.mem_sup_left (Ideal.mem_span_singleton_self x), Ideal.mem_sup_right hy⟩

/-- The local colength is positive because the localized intersection lies in the maximal ideal. -/
theorem cycleLength_pos {J p : Ideal GeoJets} (hp : p.IsPrime) (hle : J ≤ p) :
    0 < cycleLength J p hp := by
  let _ : p.IsPrime := hp
  let L := Localization.AtPrime p
  let A := J.map (algebraMap GeoJets L)
  have hA : A ≠ ⊤ := by
    apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal L).ne_top
    change J.map (algebraMap GeoJets L) ≤ IsLocalRing.maximalIdeal L
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p L]
    exact Ideal.map_mono hle
  change 0 < Module.length L (L ⧸ A)
  exact Module.length_pos_iff.mpr (Ideal.Quotient.nontrivial_iff.mpr hA)

/-- Compare ambient order of the cutter and local cycle length on a height-two prime. -/
theorem cycleLength_ge_order {f Q : Row 4} {p : Ideal GeoJets} [p.IsPrime] {n : ℕ}
    (hheight : p.height = 2)
    (hfp : toGeneric f ∈ p) (hQ : VanishesTo p (toGeneric Q) n) :
    (n : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) p ‹p.IsPrime› := by
  let L := Localization.AtPrime p
  let φ := algebraMap GeoJets L
  have hheight' : (IsLocalRing.maximalIdeal L).height = 2 := by
    apply WithBot.coe_injective
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
      IsLocalization.AtPrime.ringKrullDim_eq_height p L, hheight]
  have hf : φ (toGeneric f) ∈ IsLocalRing.maximalIdeal L :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L p _).mpr hfp
  have hmap : (intersectionIdeal f Q).map φ =
      Ideal.span {φ (toGeneric f), φ (toGeneric Q)} := by
    rw [intersectionIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  change (n : ℕ∞) ≤ Module.length L (L ⧸ (intersectionIdeal f Q).map φ)
  rw [hmap]
  exact length_ge_order hf (hheight' ▸ (by decide : (1 : ℕ∞) < 2)) hQ

end
end K1_13_6_1_2
end PackSource_K1_13_6_1_2Local

section PackSource_K1_13_6_1_4_3_2Aux2
set_option autoImplicit true
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 160000

namespace K1_13_6_1_4_3_2

noncomputable section

open K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_3
open MvPolynomial
open scoped BigOperators nonZeroDivisors

attribute [local instance] MvPolynomial.algebraMvPolynomial

private theorem quotient_isLocalization {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (M : Submonoid A) [IsLocalization M B] (I : Ideal A)
    (J' : Ideal B) (hJ : I.map (algebraMap A B) = J') :
    let f := Ideal.quotientMap J' (algebraMap A B) (Ideal.map_le_iff_le_comap.mp hJ.le)
    letI := f.toAlgebra
    IsLocalization (M.map (Ideal.Quotient.mk I)) (B ⧸ J') := by
  subst J'
  dsimp only
  let J := I.map (algebraMap A B)
  let f : A ⧸ I →+* B ⧸ J :=
    Ideal.quotientMap J (algebraMap A B) Ideal.le_comap_map
  let _ := f.toAlgebra
  change IsLocalization (M.map (Ideal.Quotient.mk I)) (B ⧸ J)
  have hm (m : M) : Ideal.Quotient.mk I m ∈ M.map (Ideal.Quotient.mk I) :=
    Submonoid.mem_map_of_mem _ m.property
  refine (isLocalization_iff (M.map (Ideal.Quotient.mk I)) (B ⧸ J)).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    exact (IsLocalization.map_units B ⟨m, hm⟩).map (Ideal.Quotient.mk J)
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨r, m⟩, e⟩ := IsLocalization.surj M z
    exact ⟨⟨Ideal.Quotient.mk I r, ⟨Ideal.Quotient.mk I m, hm m⟩⟩,
      by
        change Ideal.Quotient.mk J z * Ideal.Quotient.mk J (algebraMap A B m) =
          Ideal.Quotient.mk J (algebraMap A B r)
        simpa only [map_mul] using congrArg (Ideal.Quotient.mk J) e⟩
  · intro x y e
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk J (algebraMap A B x) =
      Ideal.Quotient.mk J (algebraMap A B y) at e
    have he : algebraMap A B (x - y) ∈ J := by
      rw [map_sub, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      exact e
    obtain ⟨m, hmM, hmem⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M B I _).mp he
    refine ⟨⟨Ideal.Quotient.mk I m, hm ⟨m, hmM⟩⟩, ?_⟩
    rw [← map_mul, ← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← mul_sub]
    exact hmem

private def eliminate {R σ : Type*} [CommRing R] [DecidableEq σ]
    (p q : σ) (hpq : p ≠ q) (u v : MvPolynomial {i // i ≠ p ∧ i ≠ q} R) :
    let ι := rename (R := R) (Subtype.val : {i // i ≠ p ∧ i ≠ q} → σ)
    (MvPolynomial σ R ⧸ Ideal.span {MvPolynomial.X p + ι u, MvPolynomial.X q + ι v}) ≃ₐ[R]
      MvPolynomial {i // i ≠ p ∧ i ≠ q} R := by
  let Free := {i // i ≠ p ∧ i ≠ q}
  let ι := rename (R := R) (Subtype.val : Free → σ)
  let I : Ideal (MvPolynomial σ R) := Ideal.span {MvPolynomial.X p + ι u, MvPolynomial.X q + ι v}
  let value (i : σ) : MvPolynomial Free R :=
    if h : i ≠ p ∧ i ≠ q then MvPolynomial.X ⟨i, h⟩ else if i = p then -u else -v
  let f : MvPolynomial σ R →ₐ[R] MvPolynomial Free R := aeval value
  have hι : f.comp ι = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    change f (ι (MvPolynomial.X i)) = MvPolynomial.X i
    simp [f, ι, value, i.property]
  have hfr (w : MvPolynomial Free R) : f (ι w) = w := AlgHom.congr_fun hι w
  have hfp : f (MvPolynomial.X p) = -u := by simp [f, value]
  have hfq : f (MvPolynomial.X q) = -v := by simp [f, value, hpq.symm]
  have hI : ∀ x ∈ I, f x = 0 := by
    have H : I ≤ RingHom.ker f.toRingHom := by
      simp [I, Ideal.span_le, Set.insert_subset_iff, hfp, hfq, hfr]
    exact fun _ hx => H hx
  let g := Ideal.Quotient.liftₐ I f hI
  let j := Ideal.Quotient.mkₐ R I
  change (MvPolynomial σ R ⧸ I) ≃ₐ[R] MvPolynomial Free R
  refine AlgEquiv.ofAlgHom g (j.comp ι) ?_ ?_
  · rw [← AlgHom.comp_assoc, show g.comp j = f from Ideal.Quotient.liftₐ_comp I f hI]
    exact hι
  · apply Ideal.Quotient.algHom_ext R
    simp only [AlgHom.comp_assoc, AlgHom.id_comp]
    ext i
    change j (ι (f (MvPolynomial.X i))) = j (MvPolynomial.X i)
    by_cases hi : i ≠ p ∧ i ≠ q
    · simp [f, value, hi, ι]
    · by_cases hip : i = p
      · subst i
        rw [hfp, map_neg, map_neg]
        have hz : j (MvPolynomial.X p + ι u) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
        exact (eq_neg_of_add_eq_zero_left (by simpa only [map_add] using hz)).symm
      · have hiq : i = q := by
          by_contra hn
          exact hi ⟨hip, hn⟩
        subst i
        rw [hfq, map_neg, map_neg]
        have hz : j (MvPolynomial.X q + ι v) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
        exact (eq_neg_of_add_eq_zero_left (by simpa only [map_add] using hz)).symm

abbrev sectionIdeal (a h : Shape) : Ideal (SliceJets a h) :=
  Ideal.span {firstSection a h, secondSection a h}

def UniversalSlice (a h : Shape) : Type := SliceJets a h ⧸ sectionIdeal a h

instance (a h : Shape) : CommRing (UniversalSlice a h) :=
  inferInstanceAs (CommRing (SliceJets a h ⧸ sectionIdeal a h))

instance (a h : Shape) : Algebra (PairSectionField a h) (UniversalSlice a h) :=
  inferInstanceAs (Algebra (PairSectionField a h) (SliceJets a h ⧸ sectionIdeal a h))

instance (a h : Shape) : Algebra GeoJets (UniversalSlice a h) :=
  inferInstanceAs (Algebra GeoJets (SliceJets a h ⧸ sectionIdeal a h))

/-- Quotienting the universal slice by an extended ideal gives the given section algebra. -/
def sliceEquiv (J : Ideal GeoJets) (a h : Shape) :
    (UniversalSlice a h ⧸ J.map (algebraMap GeoJets (UniversalSlice a h))) ≃ₐ[PairSectionField a h]
      SliceAlgebra J a h := by
  let F := PairSectionField a h
  let L := J.map (extendCoeffs a h)
  let proj : SliceJets a h →+* UniversalSlice a h := Ideal.Quotient.mk (sectionIdeal a h)
  have hmap : J.map (algebraMap GeoJets (UniversalSlice a h)) = L.map proj := by
    rw [Ideal.map_map]
    rfl
  have e : (UniversalSlice a h ⧸ L.map proj) ≃ₐ[F] (SliceJets a h ⧸ (sectionIdeal a h ⊔ L)) :=
    DoubleQuot.quotQuotEquivQuotSupₐ F (sectionIdeal a h) L
  exact (Ideal.quotientEquivAlgOfEq F hmap).trans
    (e.trans (Ideal.quotientEquivAlgOfEq F (sup_comm _ _)))

private def zeroIndex (b : Shape) : SectionIndex b := fun _ => 0

private abbrev CoeffRing (a h : Shape) := MvPolynomial (PairSectionIndex a h) GeoField
private abbrev IncidenceJets (a h : Shape) := MvPolynomial (Fin 4) (CoeffRing a h)

private def integralSection {σ : Type*} (p : Shape) (ι : SectionIndex p → σ) :
    MvPolynomial (Fin 4) (MvPolynomial σ GeoField) :=
  ∑ m ∈ boxMonomials p, C (MvPolynomial.X (ι m)) * ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val

private abbrev incidenceIdeal (a h : Shape) : Ideal (IncidenceJets a h) :=
  Ideal.span {integralSection a Sum.inl, integralSection h Sum.inr}

private theorem coeffElimination (a h : Shape) :
    Module.Flat GeoJets (IncidenceJets a h ⧸ incidenceIdeal a h) := by
  classical
  let σ := PairSectionIndex a h
  let p : σ := Sum.inl (zeroIndex a)
  let q : σ := Sum.inr (zeroIndex h)
  have hpq : p ≠ q := Sum.inl_ne_inr
  let Free := {i : σ // i ≠ p ∧ i ≠ q}
  let ι := rename (R := GeoJets) (Subtype.val : Free → σ)
  let e : IncidenceJets a h ≃ₐ[GeoJets] MvPolynomial σ GeoJets :=
    AlgEquiv.ofRingEquiv (f := (commAlgEquiv GeoField (Fin 4) σ).toRingEquiv) (by
      intro r
      have he : (commAlgEquiv GeoField (Fin 4) σ).toRingHom.comp
          (MvPolynomial.map (C : GeoField →+* CoeffRing a h)) = C := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp
        · intro i
          simp
      exact DFunLike.congr_fun he r)
  have decompose (b : Shape) (i : SectionIndex b → σ)
      (hi : ∀ m, m ≠ zeroIndex b → i m ≠ p ∧ i m ≠ q) :
      ∃ u : MvPolynomial Free GeoJets, e (integralSection b i) = MvPolynomial.X (i (zeroIndex b)) + ι u := by
    let value : σ → MvPolynomial Free GeoJets :=
      fun j => if hj : j ≠ p ∧ j ≠ q then MvPolynomial.X ⟨j, hj⟩ else 0
    let rem : MvPolynomial σ GeoJets :=
      ∑ m ∈ (boxMonomials b).erase (zeroIndex b), MvPolynomial.X (i m) * C (∏ j : Fin 4, MvPolynomial.X j ^ (m j).val)
    refine ⟨aeval value rem, ?_⟩
    have he (m : SectionIndex b) :
        e (C (MvPolynomial.X (i m)) * ∏ j : Fin 4, MvPolynomial.X j ^ (m j).val) =
          MvPolynomial.X (i m) * C (∏ j : Fin 4, MvPolynomial.X j ^ (m j).val) := by
      change commAlgEquiv GeoField (Fin 4) σ
        (C (MvPolynomial.X (i m)) * ∏ j : Fin 4, MvPolynomial.X j ^ (m j).val) = _
      simp
    have hz : zeroIndex b ∈ boxMonomials b := by
      simp [boxMonomials, zeroIndex]
    simp only [integralSection, map_sum, he]
    rw [← Finset.sum_erase_add _ _ hz, add_comm]
    have hrem : ι (aeval value rem) = rem := by
      simp only [rem, map_sum, map_mul, aeval_X, aeval_C, algebraMap_eq]
      exact Finset.sum_congr rfl fun m hm => by
        simp [ι, value, hi m (Finset.mem_erase.mp hm).1]
    rw [hrem]
    simp [zeroIndex, rem]
  obtain ⟨u, hu⟩ := decompose a Sum.inl fun m hm =>
    ⟨fun he => hm (Sum.inl.inj he), Sum.inl_ne_inr⟩
  obtain ⟨v, hv⟩ := decompose h Sum.inr fun m hm =>
    ⟨Sum.inr_ne_inl, fun he => hm (Sum.inr.inj he)⟩
  have hI : Ideal.span {MvPolynomial.X p + ι u, MvPolynomial.X q + ι v} = (incidenceIdeal a h).map e.toRingHom := by
    simp [incidenceIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hu, hv, p, q]
  exact Module.Flat.of_linearEquiv
    (((Ideal.quotientEquivAlg _ _ e hI).trans (eliminate p q hpq u v)).toLinearEquiv)

/-- The generic equations make a flat extension of the original four-jet ring.
The incidence ring is polynomial after elimination, and the field of
section coefficients is obtained by inverting the nonzero coefficients. -/
theorem universalSlice_flat (a h : Shape) : Module.Flat GeoJets (UniversalSlice a h) := by
  let A := IncidenceJets a h
  let B := SliceJets a h
  let I := incidenceIdeal a h
  let M : Submonoid A := (nonZeroDivisors (CoeffRing a h)).map C
  have hloc : IsLocalization M B :=
    MvPolynomial.isLocalization _ (PairSectionField a h)
  have hsec (p : Shape) (i : SectionIndex p → PairSectionIndex a h) :
      algebraMap A B (integralSection p i) = sectionWith p i := by
    change MvPolynomial.map (algebraMap (CoeffRing a h) (PairSectionField a h))
      (integralSection p i) = _
    simp only [integralSection, sectionWith, map_sum, map_mul, map_prod, map_pow,
      MvPolynomial.map_C, MvPolynomial.map_X]
  have hI : I.map (algebraMap A B) = sectionIdeal a h := by
    simp only [I, incidenceIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hsec] <;> rfl
  let f : (A ⧸ I) →+* UniversalSlice a h :=
    Ideal.quotientMap (sectionIdeal a h) (algebraMap A B) (Ideal.map_le_iff_le_comap.mp hI.le)
  let _ := @RingHom.toAlgebra (A ⧸ I) (UniversalSlice a h) _ _ f
  let mkI : A →+* (A ⧸ I) := Ideal.Quotient.mk I
  let M' : Submonoid (A ⧸ I) := M.map mkI
  have hlocal : IsLocalization (R := A ⧸ I) M' (UniversalSlice a h) := by
    have hl := quotient_isLocalization M I (sectionIdeal a h) hI
    dsimp only at hl
    exact hl
  have hflat := coeffElimination a h
  have hflat' : Module.Flat (A ⧸ I) (UniversalSlice a h) :=
    IsLocalization.flat (R := A ⧸ I) _ M'
  have htower : IsScalarTower GeoJets (A ⧸ I) (UniversalSlice a h) := by
    refine IsScalarTower.of_algebraMap_eq (R := GeoJets) (S := A ⧸ I)
      (A := UniversalSlice a h) fun r => ?_
    change Ideal.Quotient.mk (sectionIdeal a h) (extendCoeffs a h r) =
      f (Ideal.Quotient.mk I (MvPolynomial.map C r))
    have he : extendCoeffs a h r = algebraMap A B (MvPolynomial.map C r) := by
      change MvPolynomial.map (algebraMap GeoField (PairSectionField a h)) r =
        MvPolynomial.map (algebraMap (CoeffRing a h) (PairSectionField a h)) (MvPolynomial.map C r)
      rw [IsScalarTower.algebraMap_eq GeoField (CoeffRing a h) (PairSectionField a h),
        MvPolynomial.map_map, MvPolynomial.algebraMap_eq]
    exact congrArg (Ideal.Quotient.mk (sectionIdeal a h)) he
  exact Module.Flat.trans GeoJets (A ⧸ I) (UniversalSlice a h)

end

end K1_13_6_1_4_3_2
end PackSource_K1_13_6_1_4_3_2Aux2

section PackSource_K1_13_6_1_4_2_1_2_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_4_2_1_2_1

noncomputable section

open K1_13 K1_13_7_1 K1_13_6_1_4_2 K1_13_6_1_4_2_1_2 MvPolynomial
open scoped Pointwise

variable {k : Type*} [Field k]

private abbrev degreeShape (a h : Shape) (d : ℕ × ℕ) : Shape :=
  (a.scale d.1).plus (h.scale d.2)

private theorem degreeShape_add (a h : Shape) (d e : ℕ × ℕ) :
    degreeShape a h (d + e) = (degreeShape a h d).plus (degreeShape a h e) := by
  cases a
  cases h
  simp [degreeShape, Shape.scale, Shape.plus, Nat.add_mul, add_assoc, add_left_comm]

private theorem splitExponent {a h : Shape} (ha : Chamber a) (hh : Chamber h)
    (d e : ℕ × ℕ) {m : Fin 4 →₀ ℕ}
    (hm : m ∈ latticeIndices (degreeShape a h (d + e))) :
    ∃ u ∈ latticeIndices (degreeShape a h d),
      ∃ v ∈ latticeIndices (degreeShape a h e), u + v = m := by
  rw [degreeShape_add, latticeIndices_plus
    (chamber_plus (chamber_scale ha d.1) (chamber_scale hh d.2))
    (chamber_plus (chamber_scale ha e.1) (chamber_scale hh e.2))] at hm
  exact hm

private theorem exponent_eq_zero {a h : Shape} {m : Fin 4 →₀ ℕ}
    (hm : m ∈ latticeIndices (degreeShape a h 0)) : m = 0 := by
  have hzero : degreeShape a h 0 = ⟨0, 0, 0⟩ := by
    simp [degreeShape, Shape.scale, Shape.plus]
  rw [hzero] at hm
  have he : (fun i => m i) ∈ exponents ⟨0, 0, 0⟩ := hm
  rw [exponents_zero, Set.mem_singleton_iff] at he
  ext i
  exact congrFun he i

private abbrev liftedMonomial (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (d : ℕ × ℕ) (m : Fin 4 →₀ ℕ) (hm : m ∈ latticeIndices (degreeShape a h d)) :
    rees I a h :=
  homogeneous d (Ideal.Quotient.mk I (monomial m 1)) (monomial_mem_box hm 1)

private theorem liftedMonomial_zero (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (hm : (0 : Fin 4 →₀ ℕ) ∈ latticeIndices (degreeShape a h 0)) :
    liftedMonomial I a h 0 0 hm = 1 := by
  apply (show Function.Injective (rees I a h).val from Subtype.val_injective)
  rw [show (rees I a h).val 1 = AddMonoidAlgebra.single 0 1 from rfl]
  simp only [liftedMonomial, val_homogeneous, monomial_zero', map_one]

private theorem liftedMonomial_add (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (d e : ℕ × ℕ) {u v : Fin 4 →₀ ℕ}
    (hu : u ∈ latticeIndices (degreeShape a h d))
    (hv : v ∈ latticeIndices (degreeShape a h e))
    (huv : u + v ∈ latticeIndices (degreeShape a h (d + e))) :
    liftedMonomial I a h (d + e) (u + v) huv =
      liftedMonomial I a h d u hu * liftedMonomial I a h e v hv := by
  apply (show Function.Injective (rees I a h).val from Subtype.val_injective)
  simp only [map_mul, liftedMonomial, val_homogeneous, AddMonoidAlgebra.single_mul_single]
  rw [← map_mul, monomial_mul_monomial, mul_one]

/-- To prove submodule membership for a homogeneous piece, it suffices to check its monomials. -/
private theorem homogeneous_mem (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (d : ℕ × ℕ) (S : Submodule k (rees I a h))
    (hmon : ∀ m hm, liftedMonomial I a h d m hm ∈ S)
    (x : Affine I) (hx : x ∈ box I a h d) :
    homogeneous d x hx ∈ S := by
  obtain ⟨p, hp, rfl⟩ := hx
  let f : MvPolynomial (Fin 4) k →ₗ[k] AddMonoidAlgebra (Affine I) (ℕ × ℕ) :=
    (AddMonoidAlgebra.lsingle d).comp (Ideal.Quotient.mkₐ k I).toLinearMap
  let v := (rees I a h).val.toLinearMap
  have hle : restrictSupport k (latticeIndices (degreeShape a h d)) ≤ (S.map v).comap f := by
    rw [restrictSupport_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨liftedMonomial I a h d m hm, hmon m hm, rfl⟩
  obtain ⟨r, hr, heq⟩ := hle hp
  have heq' : r = homogeneous d (Ideal.Quotient.mk I p) ⟨p, hp, rfl⟩ :=
    Subtype.val_injective heq
  exact heq' ▸ hr

private def coordinateEval (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape) :
    MvPolynomial (latticeIndices a ⊕ latticeIndices h) k →ₐ[k] rees I a h :=
  aeval (Sum.elim (leftGen I a h) (rightGen I a h))

private theorem leftGen_mem_range (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (m : latticeIndices a) : leftGen I a h m ∈ (coordinateEval I a h).range :=
  ⟨MvPolynomial.X (.inl m), by simp [coordinateEval]⟩

private theorem rightGen_mem_range (I : Ideal (MvPolynomial (Fin 4) k)) (a h : Shape)
    (m : latticeIndices h) : rightGen I a h m ∈ (coordinateEval I a h).range :=
  ⟨MvPolynomial.X (.inr m), by simp [coordinateEval]⟩

private theorem liftedMonomial_mem_range (I : Ideal (MvPolynomial (Fin 4) k))
    (a h : Shape) (ha : Chamber a) (hh : Chamber h) (i j : ℕ) (m : Fin 4 →₀ ℕ)
    (hm : m ∈ latticeIndices (degreeShape a h (i, j))) :
    liftedMonomial I a h (i, j) m hm ∈ (coordinateEval I a h).range := by
  induction i generalizing m with
  | zero =>
    induction j generalizing m with
    | zero =>
      obtain rfl := exponent_eq_zero hm
      exact (liftedMonomial_zero I a h hm).symm ▸ (coordinateEval I a h).range.one_mem
    | succ j ih =>
      obtain ⟨u, hu, v, hv, rfl⟩ := splitExponent ha hh (0, j) (0, 1) hm
      have hv' : v ∈ latticeIndices h := by simpa only [degreeShape, right_axis] using hv
      exact (liftedMonomial_add I a h (0, j) (0, 1) hu hv hm).symm ▸
        (coordinateEval I a h).range.mul_mem (ih u hu) (rightGen_mem_range I a h ⟨v, hv'⟩)
  | succ i ih =>
    obtain ⟨u, hu, v, hv, rfl⟩ := splitExponent ha hh (i, j) (1, 0) hm
    have hv' : v ∈ latticeIndices a := by simpa only [degreeShape, left_axis] using hv
    exact (liftedMonomial_add I a h (i, j) (1, 0) hu hv hm).symm ▸
      (coordinateEval I a h).range.mul_mem (ih u hu) (leftGen_mem_range I a h ⟨v, hv'⟩)

private theorem rees_noetherian (I : Ideal (MvPolynomial (Fin 4) k))
    (a h : Shape) (ha : Chamber a) (hh : Chamber h) : IsNoetherianRing (rees I a h) := by
  classical
  apply isNoetherianRing_of_surjective _ _ (coordinateEval I a h).toRingHom
  intro p
  change p ∈ (coordinateEval I a h).range
  have hp : p = ∑ d ∈ p.val.coeff.support, homogeneous d (p.val.coeff d) (p.property d) := by
    apply (show Function.Injective (rees I a h).val from Subtype.val_injective)
    simp only [map_sum, val_homogeneous]
    exact (AddMonoidAlgebra.sum_coeff_single p.val).symm
  rw [hp]
  apply (coordinateEval I a h).range.sum_mem
  intro d _
  exact homogeneous_mem I a h d (coordinateEval I a h).range.toSubmodule
    (liftedMonomial_mem_range I a h ha hh d.1 d.2) _ _

private theorem liftedMonomial_mem_irrelevant (I : Ideal (MvPolynomial (Fin 4) k))
    (a h : Shape) (ha : Chamber a) (hh : Chamber h) (m : Fin 4 →₀ ℕ)
    (hm : m ∈ latticeIndices (degreeShape a h (1, 1))) :
    liftedMonomial I a h (1, 1) m hm ∈ irrelevant I a h := by
  obtain ⟨u, hu, v, hv, rfl⟩ := splitExponent ha hh (1, 0) (0, 1) hm
  have hu' : u ∈ latticeIndices a := by simpa only [degreeShape, left_axis] using hu
  have hv' : v ∈ latticeIndices h := by simpa only [degreeShape, right_axis] using hv
  exact (liftedMonomial_add I a h (1, 0) (0, 1) hu hv hm).symm ▸
    Ideal.subset_span (s := Set.range (pairGen I a h)) ⟨(⟨u, hu'⟩, ⟨v, hv'⟩), rfl⟩

private theorem liftedMonomial_mem_pow (I : Ideal (MvPolynomial (Fin 4) k))
    (a h : Shape) (ha : Chamber a) (hh : Chamber h) (i j : ℕ) (m : Fin 4 →₀ ℕ)
    (hm : m ∈ latticeIndices (degreeShape a h (i, j))) (n : ℕ) (hi : n ≤ i) (hj : n ≤ j) :
    liftedMonomial I a h (i, j) m hm ∈ irrelevant I a h ^ n := by
  induction n generalizing i j m with
  | zero => rw [Submodule.pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ n ih =>
    cases i with
    | zero => omega
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        obtain ⟨u, hu, v, hv, rfl⟩ := splitExponent ha hh (i, j) (1, 1) hm
        rw [Submodule.pow_succ]
        exact (liftedMonomial_add I a h (i, j) (1, 1) hu hv hm).symm ▸
          Ideal.mul_mem_mul (ih i j u hu (by omega) (by omega))
            (liftedMonomial_mem_irrelevant I a h ha hh v hv)

/-- The Rees algebra is Noetherian, and each bidegree lies in the indicated chart ideal powers. -/
theorem proof : K1_13_6_1_4_2_1_2.c1 := by
  intro k _ I a h ha hh
  refine ⟨rees_noetherian I a h ha hh, ?_⟩
  intro i j x hx n hi hj
  exact homogeneous_mem I a h (i, j) ((irrelevant I a h ^ n).restrictScalars k)
    (fun m hm => liftedMonomial_mem_pow I a h ha hh i j m hm n hi hj) x hx

end
end K1_13_6_1_4_2_1_2_1
end PackSource_K1_13_6_1_4_2_1_2_1Proof

section PackSource_K1_13_6_1_4_3_3_2Aux1
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_6_1_4_3_3_2

noncomputable section

open K1_13 K1_13_6_1_4_3_3 MvPolynomial
open scoped TensorProduct

section Coefficients

variable {k : Type} [Field k] (P : Fin 4 → Shape) (f : Fin 4 → Jets k)

private abbrev CoeffIndex := Σ i : Fin 4, lattice (P i)

private def center (a : CoeffIndex P) : k :=
  (f a.1).coeff a.2.1

private def coeffLine (a : CoeffIndex P) : Polynomial (CoefficientField k P) :=
  Polynomial.C (algebraMap k (CoefficientField k P) (center P f a)) +
    Polynomial.X * Polynomial.C
      (algebraMap (CoefficientRing k P) (CoefficientField k P) (MvPolynomial.X a))

/-- Follow the line from the actual coefficients in independent coefficient directions. -/
def deformation (i : Fin 4) : K1_13_5_4_2_4_1.Total (CoefficientField k P) := by
  classical
  letI := (lattice_finite (P i)).fintype
  exact ∑ e : lattice (P i), monomial e.val (coeffLine P f ⟨i, e⟩)

private def coeffLineHom : CoefficientRing k P →+* Polynomial (CoefficientField k P) :=
  eval₂Hom (Polynomial.C.comp (algebraMap k (CoefficientField k P))) (coeffLine P f)

private theorem coeffLineHom_injective : Function.Injective (coeffLineHom P f) := by
  let shift : CoefficientRing k P →ₐ[k] CoefficientRing k P :=
    aeval fun a => C (center P f a) + MvPolynomial.X a
  let unshift : CoefficientRing k P →ₐ[k] CoefficientRing k P :=
    aeval fun a => MvPolynomial.X a - C (center P f a)
  have hshift : unshift.comp shift = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro a
    simp [shift, unshift, algebraMap_eq]
  have hleft : Function.LeftInverse unshift shift := fun p => AlgHom.congr_fun hshift p
  have heval : (Polynomial.evalRingHom 1).comp (coeffLineHom P f) =
      (algebraMap (CoefficientRing k P) (CoefficientField k P)).comp shift.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change Polynomial.eval 1 (coeffLineHom P f (C c)) =
        algebraMap (CoefficientRing k P) (CoefficientField k P) (shift (C c))
      rw [coeffLineHom, eval₂Hom_C, RingHom.comp_apply, Polynomial.eval_C, algHom_C]
      exact IsScalarTower.algebraMap_apply k (CoefficientRing k P) (CoefficientField k P) c
    · intro a
      change Polynomial.eval 1 (coeffLineHom P f (MvPolynomial.X a)) =
        algebraMap (CoefficientRing k P) (CoefficientField k P)
          (aeval (fun b => C (center P f b) + MvPolynomial.X b) (MvPolynomial.X a))
      rw [coeffLineHom, MvPolynomial.eval₂Hom_X', aeval_X]
      simp only [coeffLine, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, one_mul, map_add]
      rw [IsScalarTower.algebraMap_apply k (CoefficientRing k P) (CoefficientField k P)]
      rfl
  intro p q hpq
  apply hleft.injective
  apply IsFractionRing.injective (CoefficientRing k P) (CoefficientField k P)
  exact (RingHom.congr_fun heval p).symm.trans
    ((congrArg (Polynomial.evalRingHom 1) hpq).trans (RingHom.congr_fun heval q))

open K1_13_5_4_2_4_1 in
private def genericCoeffMap : CoefficientField k P →+* ParameterField (CoefficientField k P) :=
  IsFractionRing.lift (g := (algebraMap (Polynomial (CoefficientField k P))
      (ParameterField (CoefficientField k P))).comp (coeffLineHom P f))
    ((IsFractionRing.injective (Polynomial (CoefficientField k P)) (ParameterField (CoefficientField k P))).comp
      (coeffLineHom_injective P f))

open K1_13_5_4_2_4_1 in
private theorem genericCoeffMap_coeff (a : CoeffIndex P) :
    genericCoeffMap P f (algebraMap (CoefficientRing k P) (CoefficientField k P) (MvPolynomial.X a)) =
      algebraMap (Polynomial (CoefficientField k P)) (ParameterField (CoefficientField k P))
        (coeffLine P f a) := by
  rw [genericCoeffMap, IsFractionRing.lift_algebraMap]
  simp [coeffLineHom]

open K1_13_5_4_2_4_1 in
theorem deformation_reduce
    (hs : ∀ i, (↑(f i).support : Set Exponent) ⊆ lattice (P i)) (i : Fin 4) :
    reduce (deformation P f i) =
      MvPolynomial.map (algebraMap k (CoefficientField k P)) (f i) := by
  classical
  let := (lattice_finite (P i)).fintype
  ext e
  simp only [deformation, reduce, map_sum, map_monomial, coeff_map, coeff_sum, coeff_monomial,
    coeffLine, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, zero_mul, add_zero, center]
  by_cases he : e ∈ lattice (P i)
  · rw [Finset.sum_eq_single (⟨e, he⟩ : lattice (P i))]
    · simp
    · intro a _ ha
      have hne : a.val ≠ e := fun h => ha (Subtype.ext h)
      simp [hne]
    · simp
  · have hcoeff : (f i).coeff e = 0 :=
      notMem_support_iff.mp fun h => he (hs i h)
    rw [hcoeff, map_zero]
    apply Finset.sum_eq_zero
    intro a _
    have hne : a.val ≠ e := fun h => he (h ▸ a.prop)
    simp [hne]

open K1_13_5_4_2_4_1 in
theorem finite_rank_map_ideal {L : Type} [Field L] [Algebra k L]
    (I : Ideal (Jets k)) [Module.Finite k (Jets k ⧸ I)] :
    Module.Finite L (Jets L ⧸ I.map (MvPolynomial.map (algebraMap k L))) ∧
    Module.finrank L (Jets L ⧸ I.map (MvPolynomial.map (algebraMap k L))) =
      Module.finrank k (Jets k ⧸ I) := by
  let e := (baseQuotient (L := L) I).toLinearEquiv
  exact ⟨Module.Finite.equiv e, e.finrank_eq.symm.trans Module.finrank_baseChange⟩

open K1_13_5_4_2_4_1 in
theorem deformation_generic (hf : Module.Finite (CoefficientField k P) (GenericAlgebra k P)) :
    Module.Finite (ParameterField (CoefficientField k P)) (GenericFiber (deformation P f)) ∧
    Module.finrank (ParameterField (CoefficientField k P)) (GenericFiber (deformation P f)) =
      Module.finrank (CoefficientField k P) (GenericAlgebra k P) := by
  let : Algebra (CoefficientField k P) (ParameterField (CoefficientField k P)) :=
    (genericCoeffMap P f).toAlgebra
  have hrow (i : Fin 4) :
      MvPolynomial.map (algebraMap (CoefficientField k P) (ParameterField (CoefficientField k P)))
          (genericEquation k P i) = toGeneric (deformation P f i) := by
    change MvPolynomial.map (genericCoeffMap P f) (genericEquation k P i) = _
    simp [genericEquation, toGeneric, deformation, genericCoeffMap_coeff]
  have hid :
      (CutIdeal (genericEquation k P)).map
          (MvPolynomial.map (algebraMap (CoefficientField k P) (ParameterField (CoefficientField k P)))) =
        (equationsIdeal (deformation P f)).map toGeneric := by
    simp only [CutIdeal, equationsIdeal, Ideal.map_span, ← Set.range_comp', hrow]
  have := hf
  have hbase := finite_rank_map_ideal (L := ParameterField (CoefficientField k P))
    (CutIdeal (genericEquation k P))
  rw [hid] at hbase
  exact hbase

end Coefficients

end

end K1_13_6_1_4_3_3_2
end PackSource_K1_13_6_1_4_3_3_2Aux1

section PackSource_K1_13_6_1_2Hasse
set_option autoImplicit true
namespace K1_13_6_1_2

noncomputable section

open Polynomial K1_13 K1_13_6
open scoped BigOperators

/-- Expand a polynomial at the original variables with new indeterminates
for their increments. -/
def taylorHom {n : ℕ} {A : Type*} [CommSemiring A] :
    MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) (MvPolynomial (Fin n) A) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    (fun i => MvPolynomial.C (MvPolynomial.X i) + MvPolynomial.X i)

private theorem pow_taylor {n : ℕ} {A : Type*} [CommSemiring A] (i : Fin n) (k : ℕ)
    (f : A) :
    (MvPolynomial.C f + MvPolynomial.X i) ^ k =
      ∑ j ∈ Finset.range (k + 1), MvPolynomial.monomial (Finsupp.single i j)
        (f ^ (k - j) * (k.choose j : A)) := by
  rw [add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro j _
  rw [MvPolynomial.X_pow_eq_monomial, ← map_pow, ← MvPolynomial.C_eq_coe_nat,
    mul_assoc, ← map_mul, mul_comm, MvPolynomial.C_mul_monomial, mul_one]

private theorem taylor_monomial_coeff {n : ℕ} {A : Type*} [CommSemiring A]
    (m a : Fin n →₀ ℕ) (c : A) :
    (taylorHom (MvPolynomial.monomial m c)).coeff a =
      MvPolynomial.monomial (m - a) (c * ∏ i : Fin n, ((m i).choose (a i) : A)) := by
  classical
  unfold taylorHom
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_pow, RingHom.comp_apply,
    MvPolynomial.coeff_C_mul]
  simp_rw [pow_taylor]
  rw [Finset.prod_univ_sum]
  simp_rw [← MvPolynomial.monomial_sum_prod]
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  have hindex (b : Fin n → ℕ) :
      (∑ i : Fin n, Finsupp.single i (b i)) =
        Finsupp.equivFunOnFinite.symm b := by
    simpa using (Finsupp.univ_sum_single (Finsupp.equivFunOnFinite.symm b))
  simp_rw [hindex]
  by_cases ha : ∀ i, a i ≤ m i
  · have hmem : (a : Fin n → ℕ) ∈ Fintype.piFinset (fun i => Finset.range (m i + 1)) :=
      Fintype.mem_piFinset.mpr fun i => Finset.mem_range_succ_iff.mpr (ha i)
    rw [Finset.sum_eq_single_of_mem (a : Fin n → ℕ) hmem]
    · have hea : Finsupp.equivFunOnFinite.symm (a : Fin n → ℕ) = a :=
        Finsupp.equivFunOnFinite.symm_apply_apply a
      simp only [hea, ↓reduceIte]
      rw [MvPolynomial.monomial_eq, Finsupp.prod_pow, map_mul, map_prod,
        Finset.prod_mul_distrib]
      simp only [Finsupp.tsub_apply, map_natCast]
      ac_rfl
    · intro b _ hb
      have hba : Finsupp.equivFunOnFinite.symm b ≠ a := by
        intro h
        exact hb (by simpa using congrArg (fun x : Fin n →₀ ℕ => (x : Fin n → ℕ)) h)
      simp [hba]
  · push Not at ha
    obtain ⟨i, hi⟩ := ha
    have hzero : (∏ k : Fin n, ((m k).choose (a k) : A)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.choose_eq_zero_of_lt hi])
    rw [hzero, mul_zero, map_zero]
    suffices (∑ b ∈ Fintype.piFinset (fun i => Finset.range (m i + 1)),
        if Finsupp.equivFunOnFinite.symm b = a then
          ∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) A) ^ (m i - b i) *
            ((m i).choose (b i) : MvPolynomial (Fin n) A) else 0) = 0 by
      rw [this, mul_zero]
    apply Finset.sum_eq_zero
    intro b hb
    have hn : Finsupp.equivFunOnFinite.symm b ≠ a := by
      intro h
      have hbi := Fintype.mem_piFinset.mp hb i
      have he : b i = a i := by
        simpa using congrArg (fun x : Fin n →₀ ℕ => x i) h
      exact (not_lt_of_ge (Finset.mem_range_succ_iff.mp (he ▸ hbi))) hi
    simp [hn]

theorem taylor_coeff {n : ℕ} {A : Type*} [CommSemiring A] (F : MvPolynomial (Fin n) A)
    (a : Fin n →₀ ℕ) : (taylorHom F).coeff a = hassePartial a F := by
  unfold hassePartial
  conv_lhs => rw [MvPolynomial.as_sum F, map_sum, MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl fun m _ => taylor_monomial_coeff m a (F.coeff m)

/-- Coefficient maps commute with the jet Hasse partials. -/
theorem map_hassePartial {n : ℕ} {A B : Type*} [CommSemiring A] [CommSemiring B]
    (φ : A →+* B) (a : Fin n →₀ ℕ) (P : MvPolynomial (Fin n) A) :
    MvPolynomial.map φ (hassePartial a P) = hassePartial a (MvPolynomial.map φ P) := by
  have h : (MvPolynomial.map (MvPolynomial.map φ)).comp (taylorHom (n := n)) =
      (taylorHom (A := B)).comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp [taylorHom]
  have hc := congrArg (fun F : MvPolynomial (Fin n) (MvPolynomial (Fin n) B) => F.coeff a)
    (RingHom.congr_fun h P)
  simpa only [RingHom.comp_apply, MvPolynomial.coeff_map, taylor_coeff] using hc

/-- Evaluating a Hasse partial at the original jet gives the corresponding
coefficient of the expansion around that jet. -/
theorem atJet_hassePartial {n : ℕ} (a : Fin n →₀ ℕ) (P : Row n) (S : Geom[X]) :
    atJet (hassePartial a P) S = (shiftJet P S).coeff a := by
  let e : Row n →+* Geom[X] := MvPolynomial.eval (jet S)
  let shift : Row n →+* Row n :=
    MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i))
  have h : (MvPolynomial.map e).comp taylorHom = shift := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [e, shift, taylorHom]
    · intro i
      simp [e, shift, taylorHom, add_comm]
  change e (hassePartial a P) = (shift P).coeff a
  have hc := congrArg (fun F : Row n => F.coeff a) (RingHom.congr_fun h P)
  simpa only [RingHom.comp_apply, MvPolynomial.coeff_map, taylor_coeff] using hc

private theorem source_support {a : Fin 4 →₀ ℕ} {P : Row 4} {m : Fin 4 →₀ ℕ}
    (hm : m ∈ (hassePartial a P).support) : ∃ v ∈ P.support, m = v - a := by
  classical
  by_contra! h
  apply (MvPolynomial.mem_support_iff.mp hm)
  unfold hassePartial
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro v hv
  simp [MvPolynomial.coeff_monomial, Ne.symm (h v hv)]

private theorem weight_le (w : Fin 4 → ℕ) (v a : Fin 4 →₀ ℕ) :
    (v - a).sum (fun i k => w i * k) ≤ v.sum (fun i k => w i * k) := by
  simp only [Finsupp.sum_fintype _ _ (fun _ => Nat.mul_zero _)]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.sub_le _ _)

/-- Hasse partials keep all three box bounds, since each exponent can only decrease. -/
theorem hasse_inBox (a : Fin 4 →₀ ℕ) {P : Row 4} {B : Shape}
    (hP : InBox (shape P) B) : InBox (shape (hassePartial a P)) B := by
  refine ⟨?_, ?_, ?_⟩
  · change (hassePartial a P).totalDegree ≤ B.b
    apply Finset.sup_le
    intro m hm
    obtain ⟨v, hv, rfl⟩ := source_support hm
    exact (by simpa only [one_mul] using weight_le (fun _ => 1) v a :
      (v - a).sum (fun _ k => k) ≤ v.sum (fun _ k => k)).trans
      ((MvPolynomial.le_totalDegree hv).trans hP.1)
  · change indexDegree (hassePartial a P) ≤ B.j
    apply Finset.sup_le
    intro m hm
    obtain ⟨v, hv, rfl⟩ := source_support hm
    exact (weight_le Fin.val v a).trans ((Finset.le_sup (f := fun m =>
      m.sum (fun i k => i.val * k)) hv).trans hP.2.1)
  · change (hassePartial a P).degreeOf 3 ≤ B.t
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    obtain ⟨v, hv, rfl⟩ := source_support hm
    exact (Nat.sub_le _ _).trans ((MvPolynomial.le_degreeOf_of_mem_support 3 hv).trans hP.2.2)

theorem hasse_atJet_eq_zero {n : ℕ} {a : Fin n →₀ ℕ} {P : Row n} {S : Geom[X]} {l : ℕ}
    (ha : multiOrder a < l) (h : OrderAt P S l) : atJet (hassePartial a P) S = 0 := by
  rw [atJet_hassePartial]
  by_contra hn
  exact (not_le_of_gt ha) (h a (MvPolynomial.mem_support_iff.mpr hn))

end
end K1_13_6_1_2
end PackSource_K1_13_6_1_2Hasse

section PackSource_K1_13_6_1_2Split
set_option autoImplicit true
namespace K1_13_6_1_2

noncomputable section

open K1_13 K1_13_6

/-- The ordinary affine Bézout bound for a local weight of a proper geometric pair. -/
def c1 : Prop :=
  ∀ (F G : GeoJets) (p : Ideal GeoJets) (hp : (Ideal.span {F, G}).IsMinimalPrime p),
    F ≠ 0 → IsRelPrime F G →
    cycleLength (Ideal.span {F, G}) p hp.isPrime ≤ (↑(F.totalDegree * G.totalDegree) : ℕ∞)

/-- The generic Hasse criterion for powers of the local maximal ideal at a geometric prime. -/
def c2 : Prop :=
  ∀ (F : GeoJets) (p : Ideal GeoJets) [p.IsPrime] (d : ℕ),
    p.height = 2 →
    (∀ a : Fin 4 →₀ ℕ, multiOrder a < d → hassePartial a F ∈ p) →
    VanishesTo p F d

theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_1.c2 := by
  intro f Q l surface hZ hf hproper hbox
  let _ : surface.IsPrime := hZ.isPrime
  have hf0 : toGeneric f ≠ 0 := fun h =>
    hf.1.ne_zero (K1_13_7_1.toGeneric_injective (h.trans (map_zero _).symm))
  have hrel := K1_13_7_1.proper_generic f Q hf.1 hproper
  have hheight : surface.height = 2 := pair_height hf0 hrel hZ
  have hdeg (P : Row 4) : (toGeneric P).totalDegree ≤ (shape P).b :=
    Finset.sup_mono (MvPolynomial.support_map_subset _ _)
  have hup : cycleLength (intersectionIdeal f Q) surface hZ.isPrime ≤
      (↑((shape f).b * cutterBox.b) : ℕ∞) :=
    (h1 _ _ _ hZ hf0 hrel).trans
      (by exact_mod_cast Nat.mul_le_mul (hdeg f) ((hdeg Q).trans hbox.1))
  have hnotop : cycleLength (intersectionIdeal f Q) surface hZ.isPrime ≠ ⊤ :=
    ne_of_lt (hup.trans_lt (ENat.natCast_lt_top _))
  let v := (cycleLength (intersectionIdeal f Q) surface hZ.isPrime).toNat
  have hv : cycleLength (intersectionIdeal f Q) surface hZ.isPrime = (v : ℕ∞) :=
    (ENat.natCast_toNat hnotop).symm
  have hpos := cycleLength_pos hZ.isPrime hZ.le
  rw [hv] at hpos hup
  refine ⟨v, by exact_mod_cast hpos, by exact_mod_cast hup, hv, ?_⟩
  intro hl
  have hcut : ∃ a : Fin 4 →₀ ℕ, multiOrder a < v + 1 ∧
      toGeneric (hassePartial a Q) ∉ surface := by
    by_contra! hn
    have horder : VanishesTo surface (toGeneric Q) (v + 1) := by
      apply h2 _ surface (v + 1) hheight
      intro a ha
      change hassePartial a (MvPolynomial.map genericCoeffs Q) ∈ surface
      rw [← map_hassePartial genericCoeffs a Q]
      exact hn a ha
    have hfp : toGeneric f ∈ surface := hZ.le (Ideal.subset_span (by simp))
    have hge := cycleLength_ge_order hheight hfp horder
    rw [hv] at hge
    exact (by omega : ¬ v + 1 ≤ v) (by exact_mod_cast hge)
  obtain ⟨a, ha, hproper'⟩ := hcut
  exact ⟨hassePartial a Q, hproper', hasse_inBox a hbox,
    fun S hS => hasse_atJet_eq_zero (by omega) hS⟩

end
end K1_13_6_1_2
end PackSource_K1_13_6_1_2Split

section PackSource_K1_13_6_1_2_2Proof
set_option autoImplicit true
namespace K1_13_6_1_2_2

noncomputable section

open K1_13_6 K1_13_6_1_2
open MvPolynomial
open scoped BigOperators

/-- A product of increments of total order at least `d` vanishes in a ring
where the `d`-th power of their common ideal is zero. -/
private theorem increment_prod_eq_zero {n : ℕ} {B : Type*} [CommRing B]
    {J : Ideal B} {d : ℕ} (hJ : J ^ d = ⊥) {t : Fin n → B} (ht : ∀ i, t i ∈ J)
    (a : Fin n →₀ ℕ) (ha : d ≤ multiOrder a) : (a.prod fun i k => t i ^ k) = 0 := by
  classical
  apply Ideal.mem_bot.mp
  rw [← hJ]
  apply Ideal.pow_le_pow_right ha
  have hp := Ideal.prod_mem_prod (s := a.support)
    (I := fun i => J ^ a i) (x := fun i => t i ^ a i)
    (fun i _ => Ideal.pow_mem_pow (ht i) (a i))
  rw [Finset.prod_pow_eq_pow_sum] at hp
  exact hp

/-- Evaluate the Taylor expansion at a lift of the coordinate residues.
Coefficients of low order vanish at the residue and terms of high order
vanish in the nilpotent kernel. -/
private theorem eval_eq_zero_of_hasse {K B C : Type*} [CommRing K] [CommRing B] [CommRing C]
    [Algebra K B] [Algebra K C] [Algebra.FormallySmooth K C] {n : ℕ}
    (φ : MvPolynomial (Fin n) K →ₐ[K] B) (ρ : B →ₐ[K] C) (hρ : Function.Surjective ρ)
    (F : MvPolynomial (Fin n) K) (d : ℕ) (hJ : RingHom.ker ρ.toRingHom ^ d = ⊥)
    (h : ∀ a : Fin n →₀ ℕ, multiOrder a < d → ρ (φ (hassePartial a F)) = 0) :
    φ F = 0 := by
  classical
  let J := RingHom.ker ρ.toRingHom
  have hnil : IsNilpotent J := ⟨d, hJ⟩
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id K C) ρ hρ hnil
  have hs (x : C) : ρ (s x) = x :=
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id K C) ρ hρ hnil x
  let r := ρ.comp φ
  let t (i : Fin n) : B := φ (MvPolynomial.X i) - s (r (MvPolynomial.X i))
  have ht (i : Fin n) : t i ∈ J := by
    change ρ (φ (MvPolynomial.X i) - s (r (MvPolynomial.X i))) = 0
    rw [map_sub, hs]
    exact sub_self _
  let ev : MvPolynomial (Fin n) (MvPolynomial (Fin n) K) →+* B :=
    eval₂Hom (s.toRingHom.comp r.toRingHom) t
  have heval : ev.comp taylorHom = φ.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [ev, RingHom.comp_apply, taylorHom, eval₂Hom_C]
      change s (r (MvPolynomial.C c)) = φ (MvPolynomial.C c)
      rw [← MvPolynomial.algebraMap_eq, r.commutes, s.commutes, φ.commutes]
    · intro i
      simp [ev, taylorHom, t]
  have hzero : ev (taylorHom F) = 0 := by
    conv_lhs => rw [MvPolynomial.as_sum (taylorHom F), map_sum]
    apply Finset.sum_eq_zero
    intro a _
    have he : ev (monomial a ((taylorHom F).coeff a)) =
        s (r ((taylorHom F).coeff a)) * (a.prod fun i k => t i ^ k) :=
      eval₂Hom_monomial _ _ _ _
    rw [he]
    by_cases ha : multiOrder a < d
    · have hr : r (hassePartial a F) = 0 := h a ha
      rw [taylor_coeff, hr, map_zero, zero_mul]
    · rw [increment_prod_eq_zero hJ ht a (le_of_not_gt ha), mul_zero]
  exact (RingHom.congr_fun heval F).symm.trans hzero

/-- The quotient by the chosen maximal-ideal power admits the lifted residue
coordinates used in the Taylor calculation. -/
private theorem local_mem_pow_of_hasse {K A : Type*} [CommRing K] [CommRing A]
    [Algebra K A] [IsLocalRing A] [Algebra.FormallySmooth K (IsLocalRing.ResidueField A)]
    {n : ℕ} (loc : MvPolynomial (Fin n) K →ₐ[K] A) (F : MvPolynomial (Fin n) K) (d : ℕ)
    (h : ∀ a : Fin n →₀ ℕ, multiOrder a < d → loc (hassePartial a F) ∈ IsLocalRing.maximalIdeal A) :
    loc F ∈ IsLocalRing.maximalIdeal A ^ d := by
  by_cases hd : d = 0
  · simp [hd, Ideal.one_eq_top]
  let m := IsLocalRing.maximalIdeal A
  have hm : m ^ d ≤ m := Ideal.pow_le_self hd
  let ρ : (A ⧸ m ^ d) →ₐ[K] IsLocalRing.ResidueField A := Ideal.Quotient.factorₐ K hm
  have hρ : Function.Surjective ρ := Ideal.Quotient.factor_surjective hm
  have hJ : RingHom.ker ρ.toRingHom ^ d = ⊥ := by
    change (RingHom.ker (Ideal.Quotient.factor hm)) ^ d = ⊥
    rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, Ideal.map_quotient_self]
  let φ := (Ideal.Quotient.mkₐ K (m ^ d)).comp loc
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  refine eval_eq_zero_of_hasse φ ρ hρ F d hJ fun a ha => ?_
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (h a ha)

/-- At every prime of a polynomial ring over a perfect field, the low Hasse
partials detect membership in the corresponding localized ideal power. -/
theorem vanishesTo_of_hasse {K : Type*} [Field K] [PerfectField K] {n : ℕ}
    (F : MvPolynomial (Fin n) K) (p : Ideal (MvPolynomial (Fin n) K)) [p.IsPrime]
    (d : ℕ) (h : ∀ a : Fin n →₀ ℕ, multiOrder a < d → hassePartial a F ∈ p) :
    VanishesTo p F d := by
  let L := Localization.AtPrime p
  have : Algebra.EssFiniteType (MvPolynomial (Fin n) K) L :=
    .of_isLocalization L p.primeCompl
  have : Algebra.EssFiniteType K L := .comp K (MvPolynomial (Fin n) K) L
  have : Algebra.EssFiniteType K (IsLocalRing.ResidueField L) := by
    change Algebra.EssFiniteType K (L ⧸ IsLocalRing.maximalIdeal L)
    infer_instance
  let loc : MvPolynomial (Fin n) K →ₐ[K] L := IsScalarTower.toAlgHom K _ L
  refine local_mem_pow_of_hasse loc F d fun a ha => ?_
  change algebraMap (MvPolynomial (Fin n) K) L (hassePartial a F) ∈ IsLocalRing.maximalIdeal L
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p)]
  exact Ideal.mem_map_of_mem _ (h a ha)

theorem proof : K1_13_6_1_2.c2 := by
  intro F p hp d _ h
  exact vanishesTo_of_hasse F p d h

end
end K1_13_6_1_2_2
end PackSource_K1_13_6_1_2_2Proof

section PackSource_K1_13_2_3_4DataC
set_option autoImplicit true
namespace K1_13_2_3_4

-- Keep the kernel reductions sequential to bound peak memory.
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

open K1_13_2

/-- The count at index `n - 1`, with index `-1` represented by zero. -/
private def c4cDen (n : ℕ) : ℕ :=
  if n == 0 then 0 else
    let u := n - 1
    u * (u * (2 * u + 21) + 66) / 72 + 1

private theorem c4cTwiceHalf (n : ℤ) : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
  have h : (2 : ℤ) ∣ n * (n - 1) := by
    rcases Int.emod_two_eq_zero_or_one n with hn | hn
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ n) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ n - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]

private theorem c4cDenPoly (u : ℤ) (hu : 0 ≤ u) :
    u * (u * (2 * u + 21) + 66) / 72 + 1 = denominator u := by
  rw [denominator, ite_eq_right (by omega)]
  let q := u / 6
  let r := u % 6
  let p := u * (u * (2 * u + 21) + 66)
  let v := 1 + r * (r + 1) / 2 + q * (22 + 7 * r + r * (r - 1) / 2) +
    (57 + 6 * r) * (q * (q - 1) / 2) + 6 * q * (q - 1) * (q - 2)
  change p / 72 + 1 = v
  suffices p + 47 ≤ 72 * v ∧ 72 * v ≤ p + 72 by omega
  have he : u = 6 * q + r := by dsimp [q, r]; omega
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by
    dsimp [r]
    omega
  have hq := c4cTwiceHalf q
  unfold p v
  rw [he]
  rcases hr with h | h | h | h | h | h <;> rw [h] <;> norm_num <;>
    constructor <;> nlinarith only [hq]

private theorem c4cDenEq (n : ℕ) :
    (c4cDen n : ℤ) = denominator ((n : ℤ) - 1) := by
  cases n with
  | zero => decide
  | succ n =>
    rw [c4cDen, ite_eq_right (by simp), Nat.succ_sub_one]
    push_cast
    rw [show (n : ℤ) + 1 - 1 = n by omega]
    exact c4cDenPoly n (by omega)

private theorem c4cDenSub (n k : ℕ) :
    (c4cDen (n - k) : ℤ) = denominator ((n : ℤ) - 1 - k) := by
  rw [c4cDenEq]
  by_cases h : k ≤ n
  · rw [Int.ofNat_sub h]
    congr 1
    omega
  · have hz : n - k = 0 := by omega
    simp [hz, denominator, show (n : ℤ) - 1 - k < 0 by omega]


private theorem c4cDenNeg (u : ℤ) (h : u < 0) : denominator u = 0 := by
  simp [denominator, h]

private theorem c4cCumNeg (d u : ℤ) (h : u < 0) : cumulative d u = 0 := by
  simp [cumulative, h]

private theorem c4cCumSmall (d u : ℤ) (h : u < d + 1) :
    cumulative d u = denominator u := by
  by_cases hu : u < 0
  · rw [c4cCumNeg _ _ hu, c4cDenNeg _ hu]
  have hd : ¬ d < 0 := by omega
  simp (disch := omega) [cumulative, hu, hd, c4cDenNeg]


/- In these grades the cap is inactive. The cumulative counts at the lower
   bound cancel in the target, and the shifted order falls below zero. -/
private def c4cChart (s q k : ℤ) : Flag :=
  ⟨1650 - 3*k, s - 1350 - q - 2*k, 1650 - 3*k, 550 - k, 1650 - q - 3*k⟩

private theorem c4cCap (d u c : ℤ) (hc : 0 ≤ c) (hu : u ≤ d) (hd : d ≤ 3*c) :
    cappedCount d u c = denominator u := by
  rw [cappedCount, ite_eq_right (by omega), c4cCumNeg (d - c - 1) (u - 3*(c + 1)) (by omega),
    sub_zero, c4cCumSmall d u (by omega)]

private theorem c4cCounts (s q k : ℤ) (hs₀ : 1866 ≤ s) (hs₁ : s ≤ 1942)
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 70) (hk₀ : 0 ≤ k) (hk₁ : k ≤ 300) :
    oldCount (c4cChart s q k) =
      denominator (1650 - 3*k) - denominator (s - 1350 - q - 2*k - 1) ∧
    kernelLower (c4cChart s q k) =
      denominator (1650 - 3*k) - denominator (s - 1350 - q - 2*k - 1) -
        denominator (1650 - q - 3*k - 1) := by
  let d := 1650 - 3*k
  let l := s - 1350 - q - 2*k
  let o := 1650 - q - 3*k
  let c := 550 - k
  let r := min d ((o - 1 - l + d) / 4) + 1
  have hr : r = (4649 - s) / 4 - k + 1 := by dsimp [r, d, o, l]; omega
  have hc : 0 ≤ c := by dsimp [c]; omega
  have hd : 0 ≤ d := by dsimp [d]; omega
  have hcap : d ≤ 3*c := by dsimp [d, c]; omega
  have hl : l - 1 ≤ d := by dsimp [d, l]; omega
  have hold : oldCount (c4cChart s q k) = denominator d - denominator (l - 1) := by
    change cappedCount d d c - cappedCount d (min d (l - 1)) c = _
    rw [min_eq_right hl, c4cCap _ _ _ hc (le_refl _) hcap, c4cCap _ _ _ hc hl hcap]
  refine ⟨hold, ?_⟩
  have ht : targetCount (c4cChart s q k) = denominator (o - 1) := by
    change (if o - 1 - l + d < 0 then 0 else cumulative d (o - 1) -
      cumulative (d - r) (o - 1 - 3*r) - cumulative d (l - 1) +
      cumulative (d - r) (l - 1)) = _
    rw [ite_eq_right (by dsimp [o, l, d]; omega),
      c4cCumNeg (d - r) (o - 1 - 3*r) (by rw [hr]; dsimp [o]; omega),
      c4cCumSmall d (o - 1) (by dsimp [o, d]; omega), c4cCumSmall d (l - 1) (by omega),
      c4cCumSmall (d - r) (l - 1) (by rw [hr]; dsimp [d, l]; omega), sub_zero, sub_add_cancel]
  change (if d < 0 || d < 0 || c < 0 then 0 else
    oldCount (c4cChart s q k) - targetCount (c4cChart s q k)) = _
  simp only [not_lt.mpr hd, not_lt.mpr hc, decide_false, Bool.false_or,
    Bool.false_eq_true, ite_false, hold, ht]
  rfl


private def c4cOld (s q k : ℕ) : ℕ :=
  c4cDen (1651 - 3*k) - c4cDen (s - (1350 + q + 2*k))

private def c4cPositive (s q k : ℕ) : ℕ :=
  c4cOld s q k - c4cDen (1650 - (q + 3*k))

private theorem c4cNatCounts (s q k : ℕ) (hs₀ : 1866 ≤ s) (hs₁ : s ≤ 1942)
    (hq : q ≤ 70) (hk : k ≤ 300) :
    (oldCount (c4cChart s q k)).toNat = c4cOld s q k ∧
    (kernelLower (c4cChart s q k)).toNat = c4cPositive s q k := by
  obtain ⟨ho, hp⟩ := c4cCounts s q k (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have hu : (c4cDen (1651 - 3*k) : ℤ) = denominator (1650 - 3*(k : ℤ)) := by
    rw [c4cDenSub]
    push_cast
    congr 1
  have hl : (c4cDen (s - (1350 + q + 2*k)) : ℤ) =
      denominator ((s : ℤ) - 1350 - q - 2*k - 1) := by
    rw [c4cDenSub]
    push_cast
    congr 1
    omega
  have ht : (c4cDen (1650 - (q + 3*k)) : ℤ) =
      denominator (1650 - (q : ℤ) - 3*k - 1) := by
    rw [c4cDenSub]
    push_cast
    congr 1
    omega
  rw [ho, hp, ← hu, ← hl, ← ht]
  unfold c4cPositive c4cOld
  omega

private theorem c4cSaving (a b c : ℤ) :
    (a - max 0 b).toNat - (a - max (max 0 b) c).toNat =
      min a.toNat c.toNat - b.toNat := by
  omega

private def c4cEntry (s q k : ℕ) : ℕ :=
  if k = 0 then 0 else if k ≤ 300 then
    min (c4cOld s q 0) (c4cPositive s q k) - c4cPositive s q 0
  else entry s q k

private theorem c4cEntryEq (s q k : ℕ) (hs₀ : 1866 ≤ s) (hs₁ : s ≤ 1942)
    (hq : q ≤ 70) : entry s q k = c4cEntry s q k := by
  let j := 3000 + q - s
  have hj : 993 ≤ j ∧ j ≤ 1581 := by dsimp [j]; omega
  by_cases hz : k = 0
  · simp [entry, cubicSavings, c4cEntry, hz]
  by_cases hk : k ≤ 300
  · have hw : windowFlag s j = c4cChart s q 0 := by
      unfold windowFlag c4cChart
      dsimp [j]
      congr 1 <;> omega
    have hr : cubicFlag (c4cChart s q 0) k = c4cChart s q k := by
      unfold cubicFlag c4cChart
      congr 1 <;> (try dsimp) <;> omega
    have h₀ := c4cNatCounts s q 0 hs₀ hs₁ hq (by decide)
    simp only [Nat.cast_zero] at h₀
    have h₁ := c4cNatCounts s q k hs₀ hs₁ hq hk
    change (if 993 ≤ j ∧ j ≤ 1581 then cubicSavings s j k else 0) = _
    rw [ite_eq_left hj, cubicSavings, ite_eq_right hz, c4cEntry, ite_eq_right hz, ite_eq_left hk]
    try dsimp only
    rw [hw, hr, c4cSaving, h₀.1, h₀.2, h₁.2]
  · simp only [c4cEntry, ite_eq_right hz, ite_eq_right hk]

private def c4cRow (s q code : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => c4cEntry s q (code % 512) + c4cRow s (q + 1) (code / 512) n

private theorem c4cRowEq (s q code n : ℕ) (hs₀ : 1866 ≤ s) (hs₁ : s ≤ 1942)
    (hq : q + n ≤ 71) : rowSum s q code n = c4cRow s q code n := by
  induction n generalizing q code with
  | zero => rfl
  | succ n ih =>
    rw [rowSum, c4cRow, c4cEntryEq _ _ _ hs₀ hs₁ (by omega),
      ih (q + 1) (code / 512) (by omega)]

private theorem c4cCheck {s code v : ℕ} (hs₀ : 1866 ≤ s) (hs₁ : s ≤ 1942)
    (hv : c4cRow s 0 code 71 = v) :
    [code].length = 1 ∧ rowsSum s [code] = v := by
  refine ⟨rfl, ?_⟩
  change rowSum s 0 code 71 + 0 = v
  rw [Nat.add_zero, c4cRowEq s 0 code 71 hs₀ hs₁ (by decide), hv]

/- The certificate encodes a row per grade. The base-512 digit of index
`q` is the cubic exponent on the diagonal `s + j = 3000 + q`. Each row is checked separately,
then the original block equalities follow from `rowsSum_append`. -/
private def rowsC1_row000 : List ℕ := [486700987698019908738002333011314256167925776103521575471461463512992763269698674608787884952500587372795800271133475072]

private theorem rowsC1_row000_checked :
    rowsC1_row000.length = 1 ∧ rowsSum 1866 rowsC1_row000 = 28404388 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC1_row001 : List ℕ := [648091605080800247133284792989942535928933486380203272005056907293069326017587720285046525223738631842424260239403647232]

private theorem rowsC1_row001_checked :
    rowsC1_row001.length = 1 ∧ rowsSum 1867 rowsC1_row001 = 28636056 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC1_row002 : List ℕ := [83441793537301272264976902685413991826338845460250135311755590776354155097794370026413849169328174622044296583811713597696]

private theorem rowsC1_row002_checked :
    rowsC1_row002.length = 1 ∧ rowsSum 1868 rowsC1_row002 = 28875231 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC1_row003 : List ℕ := [83603184771540509259889136275730033479590438416947941647856138218834081763567804739294290677220621830544762788960798900480]

private theorem rowsC1_row003_checked :
    rowsC1_row003.length = 1 ∧ rowsSum 1869 rowsC1_row003 = 29121059 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC1_row004 : List ℕ := [166235496703229960492770918302628172183885386840357447928387073019290629844570528286803350979548363830681117138479776661760]

private theorem rowsC1_row004_checked :
    rowsC1_row004.length = 1 ∧ rowsSum 1870 rowsC1_row004 = 29305336 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC1_row005 : List ℕ := [249029515082803303097608698603336600461387433318275390013423035356723912473261856689862106451522480835066633511792478912768]

private theorem rowsC1_row005_checked :
    rowsC1_row005.length = 1 ∧ rowsSum 1871 rowsC1_row005 = 29479343 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC1_row006 : List ℕ := [249190905701386193273857194501792640549895064275949125842619232570080931492139715505198035543668909748162893681686021800192]

private theorem rowsC1_row006_checked :
    rowsC1_row006.length = 1 ∧ rowsSum 1872 rowsC1_row006 = 29714183 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC1_row007 : List ℕ := [331822901801369726532241540604509980519121493915545371081063232193764544850718193199546275262277948193074074922167268671744]

private theorem rowsC1_row007_checked :
    rowsC1_row007.length = 1 ∧ rowsSum 1873 rowsC1_row007 = 29944623 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC1_row008 : List ℕ := [42722036900480870967881320679983583256540855964759901647021304377648233714239854869612513187671618318256375314456803165733120]

private theorem rowsC1_row008_checked :
    rowsC1_row008.length = 1 ∧ rowsSum 1874 rowsC1_row008 = 30174338 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC1_row009 : List ℕ := [42804830603028740741063202777162180613359514509441712241760496910837472203417625958420891390551787196557303255423104277676288]

private theorem rowsC1_row009_checked :
    rowsC1_row009.length = 1 ∧ rowsSum 1875 rowsC1_row009 = 30418119 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC1 : List ℕ :=
  rowsC1_row000 ++ rowsC1_row001 ++ rowsC1_row002 ++ rowsC1_row003
    ++ rowsC1_row004 ++ rowsC1_row005 ++ rowsC1_row006 ++ rowsC1_row007
    ++ rowsC1_row008 ++ rowsC1_row009

private theorem rowsC1_checked :
    rowsC1.length = 10 ∧ rowsSum 1866 rowsC1 = 294072676 := by
  constructor <;> simp only [rowsC1, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC1_row000_checked.1, rowsC1_row000_checked.2, rowsC1_row001_checked.1, rowsC1_row001_checked.2,
    rowsC1_row002_checked.1, rowsC1_row002_checked.2, rowsC1_row003_checked.1, rowsC1_row003_checked.2,
    rowsC1_row004_checked.1, rowsC1_row004_checked.2, rowsC1_row005_checked.1, rowsC1_row005_checked.2,
    rowsC1_row006_checked.1, rowsC1_row006_checked.2, rowsC1_row007_checked.1, rowsC1_row007_checked.2,
    rowsC1_row008_checked.1, rowsC1_row008_checked.2, rowsC1_row009_checked.1, rowsC1_row009_checked.2]

private def rowsC2_row000 : List ℕ := [85112574312053737423747168418143685051826489599255202254738071729787012354063633043713044788640495422023001380767370112532736]

private theorem rowsC2_row000_checked :
    rowsC2_row000.length = 1 ∧ rowsSum 1876 rowsC2_row000 = 30664326 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC2_row001 : List ℕ := [127420479726296510111106664271404112685949329866476943353937954597342940983348927918866496906216089937617509908528056580047104]

private theorem rowsC2_row001_checked :
    rowsC2_row001.length = 1 ∧ rowsSum 1877 rowsC2_row001 = 30888547 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC2_row002 : List ℕ := [127585743719109730956214848588906235433355482949250318549479201218679003945296301096888477292353273687338711969867593108553984]

private theorem rowsC2_row002_checked :
    rowsC2_row002.length = 1 ∧ rowsSum 1878 rowsC2_row002 = 31120790 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC2_row003 : List ℕ := [169893325721685641289137463299015308880866658026109471646162628173645714857076655069092458898571192212105590670353179854635264]

private theorem rowsC2_row003_checked :
    rowsC2_row003.length = 1 ∧ rowsSum 1879 rowsC2_row003 = 31376287 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC2_row004 : List ℕ := [21873682893046205935555236188151594627348918250162794463146530749510633555260969561973527488798637669942304100511753130637132032]

private theorem rowsC2_row004_checked :
    rowsC2_row004.length = 1 ∧ rowsSum 1880 rowsC2_row004 = 31616683 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC2_row005 : List ℕ := [21916073268750715259424359821907036213299465486670641177111105040154354762975052544623297650987576688004699279624197768457879808]

private theorem rowsC2_row005_checked :
    rowsC2_row005.length = 1 ∧ rowsSum 1881 rowsC2_row005 = 31804404 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC2_row006 : List ℕ := [43577638047456297511387394396391267676139141235937950795833851248080111697091934774176925421342535435763703807481960608389267712]

private theorem rowsC2_row006_checked :
    rowsC2_row006.length = 1 ∧ rowsSum 1882 rowsC2_row006 = 32048882 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC2_row007 : List ℕ := [65239285619863813176886612106958905695206055916507357912134082886272027825921244719074297768264824173363825824391455754174988544]

private theorem rowsC2_row007_checked :
    rowsC2_row007.length = 1 ∧ rowsSum 1883 rowsC2_row007 = 32294911 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC2_row008 : List ℕ := [65323900784184182249582002477519992281137401327867497942107767342519987770883640968421502378892522807243855078179288020932493568]

private theorem rowsC2_row008_checked :
    rowsC2_row008.length = 1 ∧ rowsSum 1884 rowsC2_row008 = 32492899 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC2_row009 : List ℕ := [86985382769503048340038381209095771397408856380927974638406947720679344310215964756739998918479314410862465037088918939923251456]

private theorem rowsC2_row009_checked :
    rowsC2_row009.length = 1 ∧ rowsSum 1885 rowsC2_row009 = 32746505 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC2 : List ℕ :=
  rowsC2_row000 ++ rowsC2_row001 ++ rowsC2_row002 ++ rowsC2_row003
    ++ rowsC2_row004 ++ rowsC2_row005 ++ rowsC2_row006 ++ rowsC2_row007
    ++ rowsC2_row008 ++ rowsC2_row009

private theorem rowsC2_checked :
    rowsC2.length = 10 ∧ rowsSum 1876 rowsC2 = 317054234 := by
  constructor <;> simp only [rowsC2, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC2_row000_checked.1, rowsC2_row000_checked.2, rowsC2_row001_checked.1, rowsC2_row001_checked.2,
    rowsC2_row002_checked.1, rowsC2_row002_checked.2, rowsC2_row003_checked.1, rowsC2_row003_checked.2,
    rowsC2_row004_checked.1, rowsC2_row004_checked.2, rowsC2_row005_checked.1, rowsC2_row005_checked.2,
    rowsC2_row006_checked.1, rowsC2_row006_checked.2, rowsC2_row007_checked.1, rowsC2_row007_checked.2,
    rowsC2_row008_checked.1, rowsC2_row008_checked.2, rowsC2_row009_checked.1, rowsC2_row009_checked.2]

private def rowsC3_row000 : List ℕ := [11199325641239657434194465647140974248795254646697399145088766828204577558947571800556805036895597764053576645052045930034830115072]

private theorem rowsC3_row000_checked :
    rowsC3_row000.length = 1 ∧ rowsSum 1886 rowsC3_row000 = 32973215 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC3_row001 : List ℕ := [11221029513600366212822923686233594532188862112074591733080482314151513477008085812079534013112759619565945686122244443168808501504]

private theorem rowsC3_row001_checked :
    rowsC3_row001.length = 1 ∧ rowsSum 1887 rowsC3_row001 = 33225916 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC3_row002 : List ℕ := [22311750680297624325830345930952329050183239815469391025932610552978475676930620021118232557137339618104366505260811145967315321088]

private theorem rowsC3_row002_checked :
    rowsC3_row002.length = 1 ∧ rowsSum 1888 rowsC3_row002 = 33489779 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC3_row003 : List ℕ := [33402514237370272346565945398762959715945500629251767251012650383640758722295239068576966969914619151847765218171713324587826675968]

private theorem rowsC3_row003_checked :
    rowsC3_row003.length = 1 ∧ rowsSum 1889 rowsC3_row003 = 33755809 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC3_row004 : List ℕ := [33445837201502300696127289907243690347061883698023357406838157752022026536834332545792005905105372350490172108633675199354109034752]

private theorem rowsC3_row004_checked :
    rowsC3_row004.length = 1 ∧ rowsSum 1890 rowsC3_row004 = 33963460 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC3_row005 : List ℕ := [44536515977985560750099642005062570861688097781371425247041095201827896217636266059124622808494639641631187945075424715938052833536]

private theorem rowsC3_row005_checked :
    rowsC3_row005.length = 1 ∧ rowsSum 1891 rowsC3_row005 = 34212972 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC3_row006 : List ℕ := [5734054728314059043838044684188764835056172867160258415238485883620148010263593292342740824875548024605183670121701995662551453663488]

private theorem rowsC3_row006_checked :
    rowsC3_row006.length = 1 ∧ rowsSum 1892 rowsC3_row006 = 34469951 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC3_row007 : List ℕ := [5745167110963387500965336927351600400480697146752693925526446161235733324710479233346612395562038387864738076049983184177100220399872]

private theorem rowsC3_row007_checked :
    rowsC3_row007.length = 1 ∧ rowsSum 1893 rowsC3_row007 = 34710054 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC3_row008 : List ℕ := [11423616348312383654825132419562426857675777857090011989962747254280294169327890041222523329807572002693432685223221719445091735699712]

private theorem rowsC3_row008_checked :
    rowsC3_row008.length = 1 ∧ rowsSum 1894 rowsC3_row008 = 34951171 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC3 : List ℕ :=
  rowsC3_row000 ++ rowsC3_row001 ++ rowsC3_row002 ++ rowsC3_row003
    ++ rowsC3_row004 ++ rowsC3_row005 ++ rowsC3_row006 ++ rowsC3_row007
    ++ rowsC3_row008

private theorem rowsC3_checked :
    rowsC3.length = 9 ∧ rowsSum 1886 rowsC3 = 305752327 := by
  constructor <;> simp only [rowsC3, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC3_row000_checked.1, rowsC3_row000_checked.2, rowsC3_row001_checked.1, rowsC3_row001_checked.2,
    rowsC3_row002_checked.1, rowsC3_row002_checked.2, rowsC3_row003_checked.1, rowsC3_row003_checked.2,
    rowsC3_row004_checked.1, rowsC3_row004_checked.2, rowsC3_row005_checked.1, rowsC3_row005_checked.2,
    rowsC3_row006_checked.1, rowsC3_row006_checked.2, rowsC3_row007_checked.1, rowsC3_row007_checked.2,
    rowsC3_row008_checked.1, rowsC3_row008_checked.2]

private def rowsC4_row000 : List ℕ := [17113177968310062700880077700903190211372043806379127781016890515579845308542989442495610640451402338249366542402070576595256073126144]

private theorem rowsC4_row000_checked :
    rowsC4_row000.length = 1 ∧ rowsSum 1895 rowsC4_row000 = 35215060 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC4_row001 : List ℕ := [17124268647169177956417172432508769457695684198758461950490375985479566535686908132000265712870285979553306765854674966102357441642752]

private theorem rowsC4_row001_checked :
    rowsC4_row001.length = 1 ∧ rowsSum 1896 rowsC4_row001 = 35482889 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC4_row002 : List ℕ := [22802696180728607104051016706592036281184306064062139372283599688604323750254337732263284964774666244478917703104367988406887041335552]

private theorem rowsC4_row002_checked :
    rowsC4_row002.length = 1 ∧ rowsSum 1897 rowsC4_row002 = 35752024 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC4_row003 : List ℕ := [2935836020896798230445078878304647578050754709721956913622086955444937451793275389152304794783368590598859969509436911869773564744958208]

private theorem rowsC4_row003_checked :
    rowsC4_row003.length = 1 ∧ rowsSum 1898 rowsC4_row003 = 35999170 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC4_row004 : List ℕ := [5848880457995681801300930357924250688965734131698409385388889179448783062789147276984760217976989563300480254816638661958324470774104320]

private theorem rowsC4_row004_checked :
    rowsC4_row004.length = 1 ∧ rowsSum 1899 rowsC4_row004 = 36195310 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC4_row005 : List ℕ := [5848891570335940431270467798815962551129998262320827144777305072596684364128695188488730223259245920872975652047786049970562713386090752]

private theorem rowsC4_row005_checked :
    rowsC4_row005.length = 1 ∧ rowsSum 1900 rowsC4_row005 = 36479131 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC4_row006 : List ℕ := [8761947119774752102850599782862433388222486298495807053135753971338214900849994640222957321111166835227083789511645840174850337839120640]

private theorem rowsC4_row006_checked :
    rowsC4_row006.length = 1 ∧ rowsSum 1901 rowsC4_row006 = 36712301 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC4_row007 : List ℕ := [11674980444533046675882887516996508099754755752513604759777033301260488233338126401736168069042278212223323726239646855265623438608433408]

private theorem rowsC4_row007_checked :
    rowsC4_row007.length = 1 ∧ rowsSum 1902 rowsC4_row007 = 36993294 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC4_row008 : List ℕ := [11674980444533046837274120553775122575966364704290556364525581518998302338027876378652941602522964518182239569371360151400631669528592640]

private theorem rowsC4_row008_checked :
    rowsC4_row008.length = 1 ∧ rowsSum 1903 rowsC4_row008 = 37262321 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC4 : List ℕ :=
  rowsC4_row000 ++ rowsC4_row001 ++ rowsC4_row002 ++ rowsC4_row003
    ++ rowsC4_row004 ++ rowsC4_row005 ++ rowsC4_row006 ++ rowsC4_row007
    ++ rowsC4_row008

private theorem rowsC4_checked :
    rowsC4.length = 9 ∧ rowsSum 1895 rowsC4 = 326091500 := by
  constructor <;> simp only [rowsC4, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC4_row000_checked.1, rowsC4_row000_checked.2, rowsC4_row001_checked.1, rowsC4_row001_checked.2,
    rowsC4_row002_checked.1, rowsC4_row002_checked.2, rowsC4_row003_checked.1, rowsC4_row003_checked.2,
    rowsC4_row004_checked.1, rowsC4_row004_checked.2, rowsC4_row005_checked.1, rowsC4_row005_checked.2,
    rowsC4_row006_checked.1, rowsC4_row006_checked.2, rowsC4_row007_checked.1, rowsC4_row007_checked.2,
    rowsC4_row008_checked.1, rowsC4_row008_checked.2]

private def rowsC5_row000 : List ℕ := [1503153721126863483744722490269213556652529746596596498274969374609996760807435423641082273627030247390734965028560164204237734837330510080]

private theorem rowsC5_row000_checked :
    rowsC5_row000.length = 1 ∧ rowsSum 1904 rowsC5_row000 = 37531039 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC5_row001 : List ℕ := [2994626794493789082266076343257216352610471829043472842159271117328114168146390983721479646257784254199666011843930639201908232043578392832]

private theorem rowsC5_row001_checked :
    rowsC5_row001.length = 1 ∧ rowsSum 1905 rowsC5_row001 = 37771999 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC5_row002 : List ℕ := [2994632484012001500810479512993768239181327063415645403955749518151192483505410018607933556560585581959508893795736256064666091853355024640]

private theorem rowsC5_row002_checked :
    rowsC5_row002.length = 1 ∧ rowsSum 1906 rowsC5_row002 = 38045448 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC5_row003 : List ℕ := [4486116925324673076659191872775994738936214752509052062295065395396812313487855603601506841874349543101791906556161728028249078665413001472]

private theorem rowsC5_row003_checked :
    rowsC5_row003.length = 1 ∧ rowsSum 1907 rowsC5_row003 = 38327971 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC5_row004 : List ℕ := [5977589987600919898052038408702212147074434945285945129724728168055667131095923441323493433476637890905442606433889302066010180628250755328]

private theorem rowsC5_row004_checked :
    rowsC5_row004.length = 1 ∧ rowsSum 1908 rowsC5_row004 = 38527726 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC5_row005 : List ℕ := [768123232154591210845332110903505100786301390105769369142190734154732708282417904563019444633046508775697294913421087543461886292592928358656]

private theorem rowsC5_row005_checked :
    rowsC5_row005.length = 1 ∧ rowsSum 1909 rowsC5_row005 = 38819639 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC5_row006 : List ℕ := [769614705216954103677297915017837340988177272319774232827353967336728426260317372521740807367909467778957039073596018793288157908395618337024]

private theorem rowsC5_row006_checked :
    rowsC5_row006.length = 1 ∧ rowsSum 1910 rowsC5_row006 = 39111484 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC5_row007 : List ℕ := [1533248918780820052427813085398354330909831389032724631685494796143759804369925531370585023154141568239655382268093903904845234545501875077376]

private theorem rowsC5_row007_checked :
    rowsC5_row007.length = 1 ∧ rowsSum 1911 rowsC5_row007 = 39380995 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC5_row008 : List ℕ := [2295403288702020102911220925861558341848090463837506916049053138604486820943374278590568593564958765429318280453093093667696315350134793830656]

private theorem rowsC5_row008_checked :
    rowsC5_row008.length = 1 ∧ rowsSum 1912 rowsC5_row008 = 39661353 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC5 : List ℕ :=
  rowsC5_row000 ++ rowsC5_row001 ++ rowsC5_row002 ++ rowsC5_row003
    ++ rowsC5_row004 ++ rowsC5_row005 ++ rowsC5_row006 ++ rowsC5_row007
    ++ rowsC5_row008

private theorem rowsC5_checked :
    rowsC5.length = 9 ∧ rowsSum 1904 rowsC5 = 347177654 := by
  constructor <;> simp only [rowsC5, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC5_row000_checked.1, rowsC5_row000_checked.2, rowsC5_row001_checked.1, rowsC5_row001_checked.2,
    rowsC5_row002_checked.1, rowsC5_row002_checked.2, rowsC5_row003_checked.1, rowsC5_row003_checked.2,
    rowsC5_row004_checked.1, rowsC5_row004_checked.2, rowsC5_row005_checked.1, rowsC5_row005_checked.2,
    rowsC5_row006_checked.1, rowsC5_row006_checked.2, rowsC5_row007_checked.1, rowsC5_row007_checked.2,
    rowsC5_row008_checked.1, rowsC5_row008_checked.2]

private def rowsC6_row000 : List ℕ := [2296891865766232615249506238861309297161347489190849419706733021085131284683925105207390260761302986658449773584997700765402358384187832140033]

private theorem rowsC6_row000_checked :
    rowsC6_row000.length = 1 ∧ rowsSum 1913 rowsC6_row000 = 39942270 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC6_row001 : List ℕ := [3060526073651670987802643665255532619302110657810611331684499503716888996415191958601504637791558823912844158055255758909697237416206705754370]

private theorem rowsC6_row001_checked :
    rowsC6_row001.length = 1 ∧ rowsSum 1914 rowsC6_row001 = 40226680 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC6_row002 : List ℕ := [393279094863161790631586524042032925259322884068967662749103159153523828558920425621496393516894957710439822323965533752132087448998329767297282]

private theorem rowsC6_row002_checked :
    rowsC6_row002.length = 1 ∧ rowsSum 1915 rowsC6_row002 = 40455650 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC6_row003 : List ℕ := [394804877620602388556068742447607922380579304685713915179255196269454551984435109263357909895056037639893886231265338470492772412270583098769667]

private theorem rowsC6_row003_checked :
    rowsC6_row003.length = 1 ∧ rowsSum 1916 rowsC6_row003 = 40745788 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC6_row004 : List ℕ := [785024934981487224245952144739115972059120027408085902401554278130240421951059717648286124795832189740365177691794013150431010472494734040498435]

private theorem rowsC6_row004_checked :
    rowsC6_row004.length = 1 ∧ rowsSum 1917 rowsC6_row004 = 40973542 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC6_row005 : List ℕ := [1175246483815434292690545114041117871026222317484803541017115206965482778311852966113942388894415878576233821370222557926616827217561542289654020]

private theorem rowsC6_row005_checked :
    rowsC6_row005.length = 1 ∧ rowsSum 1918 rowsC6_row005 = 41234803 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC6_row006 : List ℕ := [1176770780914478089298611842058170332389224318309138968112225030658977852275214315496531658820253612301097454675202122045140632281653564280013060]

private theorem rowsC6_row006_checked :
    rowsC6_row006.length = 1 ∧ rowsSum 1919 rowsC6_row006 = 41539927 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC6_row007 : List ℕ := [1566989349709655567416435541929698791539041470416874434919628397276614159683950006355296037982257082012679088848270738593656523128239066141819140]

private theorem rowsC6_row007_checked :
    rowsC6_row007.length = 1 ∧ rowsSum 1920 rowsC6_row007 = 41847978 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC6 : List ℕ :=
  rowsC6_row000 ++ rowsC6_row001 ++ rowsC6_row002 ++ rowsC6_row003
    ++ rowsC6_row004 ++ rowsC6_row005 ++ rowsC6_row006 ++ rowsC6_row007

private theorem rowsC6_checked :
    rowsC6.length = 8 ∧ rowsSum 1913 rowsC6 = 326966638 := by
  constructor <;> simp only [rowsC6, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC6_row000_checked.1, rowsC6_row000_checked.2, rowsC6_row001_checked.1, rowsC6_row001_checked.2,
    rowsC6_row002_checked.1, rowsC6_row002_checked.2, rowsC6_row003_checked.1, rowsC6_row003_checked.2,
    rowsC6_row004_checked.1, rowsC6_row004_checked.2, rowsC6_row005_checked.1, rowsC6_row005_checked.2,
    rowsC6_row006_checked.1, rowsC6_row006_checked.2, rowsC6_row007_checked.1, rowsC6_row007_checked.2]

private def rowsC7_row000 : List ℕ := [201749115138728335832294999963245003520991891411144297201537512051164914405775900644933478869872740846375172492559953510821470217422059008593887494]

private theorem rowsC7_row000_checked :
    rowsC7_row000.length = 1 ∧ rowsSum 1921 rowsC7_row000 = 42158211 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC7_row001 : List ℕ := [401932004564879280646311846402135195058318903267058243669513978147110482697218332782992030421125830113088367525004459440053494121796388299919720710]

private theorem rowsC7_row001_checked :
    rowsC7_row001.length = 1 ∧ rowsSum 1922 rowsC7_row001 = 42435804 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC7_row002 : List ℕ := [401932766710521458813927498106427376491815651652737369350181724846542538022593110394862318789546605127623249823695590646505557998070272788317470982]

private theorem rowsC7_row002_checked :
    rowsC7_row002.length = 1 ∧ rowsSum 1923 rowsC7_row002 = 42727099 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC7_row003 : List ℕ := [602116421259423271601287621732806812862910974032567547769875155497367072216855524919511244998733568773781583720242137951232306137915648490179002630]

private theorem rowsC7_row003_checked :
    rowsC7_row003.length = 1 ∧ rowsSum 1924 rowsC7_row003 = 42983291 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC7_row004 : List ℕ := [802298547048436284529353793422548429661526045725572433963777436783353632679920646021731862666522699204895733870232481123250710205230724812453839112]

private theorem rowsC7_row004_checked :
    rowsC7_row004.length = 1 ∧ rowsSum 1925 rowsC7_row004 = 43217928 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC7_row005 : List ℕ := [103095755043805777088429393023330479288038053171699214382031704992407910420809636639408325015173626422077682241223829331086600844875519140491924996360]

private theorem rowsC7_row005_checked :
    rowsC7_row005.length = 1 ∧ rowsSum 1926 rowsC7_row005 = 43524631 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC7_row006 : List ℕ := [103295937169597697445163962680835165948536066977273713288581063564816389347224613600908249728092908987335268744661605713476456245821079493169081614600]

private theorem rowsC7_row006_checked :
    rowsC7_row006.length = 1 ∧ rowsSum 1927 rowsC7_row006 = 43833918 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC7_row007 : List ℕ := [205789186337218191690911707665475222445769611386354555887426488986990500321780175877399888351235395235907669469938271979072966077091183042641466097928]

private theorem rowsC7_row007_checked :
    rowsC7_row007.length = 1 ∧ rowsSum 1928 rowsC7_row007 = 44105101 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC7 : List ℕ :=
  rowsC7_row000 ++ rowsC7_row001 ++ rowsC7_row002 ++ rowsC7_row003
    ++ rowsC7_row004 ++ rowsC7_row005 ++ rowsC7_row006 ++ rowsC7_row007

private theorem rowsC7_checked :
    rowsC7.length = 8 ∧ rowsSum 1921 rowsC7 = 344985983 := by
  constructor <;> simp only [rowsC7, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC7_row000_checked.1, rowsC7_row000_checked.2, rowsC7_row001_checked.1, rowsC7_row001_checked.2,
    rowsC7_row002_checked.1, rowsC7_row002_checked.2, rowsC7_row003_checked.1, rowsC7_row003_checked.2,
    rowsC7_row004_checked.1, rowsC7_row004_checked.2, rowsC7_row005_checked.1, rowsC7_row005_checked.2,
    rowsC7_row006_checked.1, rowsC7_row006_checked.2, rowsC7_row007_checked.1, rowsC7_row007_checked.2]

private def rowsC8_row000 : List ℕ := [308083033814687062517633348582057020240800519151331463223885632389770653492309047689323157540401351460498487047639279592996185125270901621756054864136]

private theorem rowsC8_row000_checked :
    rowsC8_row000.length = 1 ∧ rowsSum 1929 rowsC8_row000 = 44390104 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC8_row001 : List ℕ := [308283607684824720738286795886625920602402667829710008028005692023869245726661356772758138523920578074474543563007614814203497942920955951590980845832]

private theorem rowsC8_row001_checked :
    rowsC8_row001.length = 1 ∧ rowsSum 1930 rowsC8_row001 = 44705169 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC8_row002 : List ℕ := [410776856090287943386386545144189811145255968697849343696141675019562217413928455489723015187281214530831417552839810649780264506607683854875928690956]

private theorem rowsC8_row002_checked :
    rowsC8_row002.length = 1 ∧ rowsSum 1931 rowsC8_row002 = 45006648 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC8_row003 : List ℕ := [52887320038925312302713761405971067868982253287830925580334163377681394778347632484992191228488134371584417958797395989367569859495370177324184363991308]

private theorem rowsC8_row003_checked :
    rowsC8_row003.length = 1 ∧ rowsSum 1932 rowsC8_row003 = 45312877 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC8_row004 : List ℕ := [105364063403893568497901354754202087659403515844712216473305663656921582175453208848779901779304215714601945823704423813548478340530650458262445213483276]

private theorem rowsC8_row004_checked :
    rowsC8_row004.length = 1 ∧ rowsSum 1933 rowsC8_row004 = 45547060 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC8_row005 : List ℕ := [105364263196562934391963312881183735984543977936594804871067309868862270237893190374087948558013391768761030128917572377322425586501667984782021846237452]

private theorem rowsC8_row005_checked :
    rowsC8_row005.length = 1 ∧ rowsSum 1934 rowsC8_row005 = 45856919 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC8_row006 : List ℕ := [157841206354193116531649884466125601382702057589333792239845917581585634155788195149653673517664221001247171983912726017809303548271892409700592298099468]

private theorem rowsC8_row006_checked :
    rowsC8_row006.length = 1 ∧ rowsSum 1935 rowsC8_row006 = 46164340 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC8_row007 : List ℕ := [210317750317465281371651786821219920257403208729439406516742929061011227401216940761089025546994968632510341009796085447322077286755874754681591983899404]

private theorem rowsC8_row007_checked :
    rowsC8_row007.length = 1 ∧ rowsSum 1936 rowsC8_row007 = 46453223 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC8 : List ℕ :=
  rowsC8_row000 ++ rowsC8_row001 ++ rowsC8_row002 ++ rowsC8_row003
    ++ rowsC8_row004 ++ rowsC8_row005 ++ rowsC8_row006 ++ rowsC8_row007

private theorem rowsC8_checked :
    rowsC8.length = 8 ∧ rowsSum 1929 rowsC8 = 363436340 := by
  constructor <;> simp only [rowsC8, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC8_row000_checked.1, rowsC8_row000_checked.2, rowsC8_row001_checked.1, rowsC8_row001_checked.2,
    rowsC8_row002_checked.1, rowsC8_row002_checked.2, rowsC8_row003_checked.1, rowsC8_row003_checked.2,
    rowsC8_row004_checked.1, rowsC8_row004_checked.2, rowsC8_row005_checked.1, rowsC8_row005_checked.2,
    rowsC8_row006_checked.1, rowsC8_row006_checked.2, rowsC8_row007_checked.1, rowsC8_row007_checked.2]

private def rowsC9_row000 : List ℕ := [27025933610203421626161879907525517438265102697158085619419547425053543915463025322814486780109694824959885075232915217893418407537951205113696524106335500]

private theorem rowsC9_row000_checked :
    rowsC9_row000.length = 1 ∧ rowsSum 1937 rowsC9_row000 = 46752489 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC9_row001 : List ℕ := [27078410153387018799065050742326077259153600425675987146749187067450502911893329290688943780331585023196967017666947276614202567807846655613326183842841872]

private theorem rowsC9_row001_checked :
    rowsC9_row001.length = 1 ∧ rowsSum 1938 rowsC9_row001 = 47081445 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC9_row002 : List ℕ := [53946400463183725642622347560256596097536041132263247739580186628950019611659944020585805710710024495142497380421103359841873026679677021471257219341354768]

private theorem rowsC9_row002_checked :
    rowsC9_row002.length = 1 ∧ rowsSum 1939 rowsC9_row002 = 47411477 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC9_row003 : List ℕ := [80762118816317325316622476357402899630823050467264894266257222689858061714544055363787156205361487551948297422643209574745798145794357064726365953375471888]

private theorem rowsC9_row003_checked :
    rowsC9_row003.length = 1 ∧ rowsSum 1940 rowsC9_row003 = 47702936 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC9_row004 : List ℕ := [80814698052930690104651746463500753482859358001991250741412365361932177665417750537379149768359472128556000740273737569011244457204974773170609987067709712]

private theorem rowsC9_row004_checked :
    rowsC9_row004.length = 1 ∧ rowsSum 1941 rowsC9_row004 = 47947008 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC9_row005 : List ℕ := [107682688162932442631075236062744851792033465285005024049075128564591746055849560951177136676970531726970545484243177347692341866680556780618260244896811280]

private theorem rowsC9_row005_checked :
    rowsC9_row005.length = 1 ∧ rowsSum 1942 rowsC9_row005 = 48258651 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)

private def rowsC9 : List ℕ :=
  rowsC9_row000 ++ rowsC9_row001 ++ rowsC9_row002 ++ rowsC9_row003
    ++ rowsC9_row004 ++ rowsC9_row005

private theorem rowsC9_checked :
    rowsC9.length = 6 ∧ rowsSum 1937 rowsC9 = 285154006 := by
  constructor <;> simp only [rowsC9, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC9_row000_checked.1, rowsC9_row000_checked.2, rowsC9_row001_checked.1, rowsC9_row001_checked.2,
    rowsC9_row002_checked.1, rowsC9_row002_checked.2, rowsC9_row003_checked.1, rowsC9_row003_checked.2,
    rowsC9_row004_checked.1, rowsC9_row004_checked.2, rowsC9_row005_checked.1, rowsC9_row005_checked.2]

def rowsC : List ℕ := rowsC1 ++ rowsC2 ++ rowsC3 ++ rowsC4 ++ rowsC5 ++ rowsC6 ++ rowsC7 ++ rowsC8 ++ rowsC9

theorem rowsC_length : rowsC.length = 77 := by
  simp only [rowsC, List.length_append, Nat.reduceAdd,
    rowsC1_checked.1, rowsC2_checked.1, rowsC3_checked.1, rowsC4_checked.1,
    rowsC5_checked.1, rowsC6_checked.1, rowsC7_checked.1, rowsC8_checked.1,
    rowsC9_checked.1]

theorem rowsC_sum : rowsSum 1866 rowsC = 2910691358 := by
  simp only [rowsC, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsC1_checked.1, rowsC2_checked.1, rowsC3_checked.1, rowsC4_checked.1,
    rowsC5_checked.1, rowsC6_checked.1, rowsC7_checked.1, rowsC8_checked.1,
    rowsC1_checked.2, rowsC2_checked.2, rowsC3_checked.2, rowsC4_checked.2,
    rowsC5_checked.2, rowsC6_checked.2, rowsC7_checked.2, rowsC8_checked.2,
    rowsC9_checked.2]

end K1_13_2_3_4
end PackSource_K1_13_2_3_4DataC

section PackSource_K1_13_1_1Blocks
set_option autoImplicit true
namespace K1_13_1_1

open K1_13 K1_13_1 MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

private abbrev Local := LocalPolynomial Geom 3
private abbrev T : Local := MvPolynomial.X (localT 3)

private def liftVar (j : Fin 4) : LocalVariable 3 := ![localE 3, localY 0, localY 1, localY 2] j

private def liftPower (j : Fin 4) : ℕ := if j = 0 then 1 else j.val

private def liftImage (j : Fin 4) : Local := T ^ liftPower j * MvPolynomial.X (liftVar j)

private def liftJets : Form →ₐ[Geom] Local := bind₁ liftImage

private theorem liftJets_X (j : Fin 4) : liftJets (MvPolynomial.X j) = liftImage j := bind₁_X_right _ _

private theorem lift_value :
    liftJets valueForm = unscaledLocalSubstitution 3 0 0 (MvPolynomial.X (some 0)) := by
  rw [unscaledLocalSubstitution_Y_zero]
  simp only [valueForm, map_add, map_sub, liftJets_X, localCorrection, Fin.sum_univ_three]
  simp [liftImage, liftPower, liftVar]
  ring

private theorem lift_order (j : Fin 4) :
    liftImage j ∈ restrictWeightedOrder (localContactWeight 3) (1 + targetOrder j) := by
  have h : liftPower j * 1 + localContactWeight 3 (liftVar j) = 1 + targetOrder j := by
    fin_cases j <;> decide
  rw [← h]
  exact mul_mem_restrictWeightedOrder
    (pow_mem_restrictWeightedOrder (X_mem_restrictWeightedOrder _ _ (localContactWeight_T 3).ge)
      (liftPower j))
    (X_mem_restrictWeightedOrder _ _ le_rfl)

private theorem value_hom :
    valueForm.IsWeightedHomogeneous (fun _ => (1 : ℕ)) 1 := by
  let h := isWeightedHomogeneous_X Geom (fun _ : Fin 4 => (1 : ℕ))
  exact (((h 0).add (h 1)).sub (h 2)).add (h 3)

private theorem lift_value_order :
    liftJets valueForm ∈ restrictWeightedOrder (localContactWeight 3) 1 := by
  have h (j : Fin 4) :
      liftImage j ∈ restrictWeightedOrder (localContactWeight 3) 1 :=
    restrictWeightedOrder_anti _ (Nat.le_add_right 1 (targetOrder j)) (lift_order j)
  simpa only [valueForm, map_add, map_sub, liftJets_X] using
    (add_mem (sub_mem (add_mem (h 0) (h 1)) (h 2)) (h 3))

private def postprocess (s : ℕ) (g : ℤ) : Form →ₗ[Geom] Local :=
  (projectLowContact 138).comp
    ((LinearMap.mulLeft Geom (T ^ (g + 48).toNat *
      (liftJets valueForm) ^ (s - residualDegree s))).comp liftJets.toLinearMap)

private theorem postprocess_truncate (s : ℕ) (g : ℤ) (hg : -48 ≤ g) {P : Form}
    (hP : P.IsWeightedHomogeneous (fun _ => (1 : ℕ)) (residualDegree s)) :
    postprocess s g (weightedTruncation targetOrder (orderCutoff s g).toNat P) =
      postprocess s g P := by
  let d := residualDegree s
  let cutoff := (orderCutoff s g).toNat
  let H := filterSupport (fun e : Fin 4 →₀ ℕ => ¬ e.weight targetOrder < cutoff) P
  have hsplit : weightedTruncation targetOrder cutoff P + H = P :=
    filterSupport_add_filterSupport_not _ _
  have hH : H ∈ restrictWeightedOrder (fun j => 1 + targetOrder j) (d + cutoff) := by
    refine mem_restrictWeightedOrder.mpr fun e he => ?_
    have hc := mem_support_iff.mp he
    change (filterSupport _ P).coeff e ≠ 0 at hc
    rw [coeff_filterSupport] at hc
    by_cases hl : e.weight targetOrder < cutoff
    · simp [hl] at hc
    · have hd := hP (d := e) (by simpa [hl] using hc)
      rw [← Finsupp.degree_eq_weight_one] at hd
      have hw : e.weight (fun j => 1 + targetOrder j) = e.degree + e.weight targetOrder := by
        rw [Finsupp.degree_eq_sum, Finsupp.weight_eq_sum, Finsupp.weight_eq_sum,
          ← Finset.sum_add_distrib]
        simp [Nat.mul_add]
      rw [hw, hd]
      exact Nat.add_le_add_left (Nat.le_of_not_lt hl) d
  have ht : (T ^ (g + 48).toNat) ∈
      restrictWeightedOrder (localContactWeight 3) ((g + 48).toNat * 1) :=
    pow_mem_restrictWeightedOrder (X_mem_restrictWeightedOrder _ _ (localContactWeight_T 3).ge) _
  have hf := pow_mem_restrictWeightedOrder lift_value_order (s - d)
  have hh := mul_mem_restrictWeightedOrder (mul_mem_restrictWeightedOrder ht hf)
    (bind₁_mem_restrictWeightedOrder lift_order hH)
  have hc : 138 ≤ ((g + 48).toNat * 1 + (s-d) * 1) + (d + cutoff) := by
    have hd : d ≤ s := min_le_left _ _
    dsimp [cutoff, orderCutoff]
    omega
  have hz : postprocess s g H = 0 :=
    (weightedTruncation_eq_zero_iff _ _ _).mpr (restrictWeightedOrder_anti _ hc hh)
  calc
    postprocess s g (weightedTruncation targetOrder cutoff P) =
        postprocess s g (weightedTruncation targetOrder cutoff P + H) := by rw [map_add, hz, add_zero]
    _ = postprocess s g P := by rw [hsplit]

private theorem project_monomial (cut : ℕ) (e : LocalVariable 3 →₀ ℕ) (a : Geom) :
    projectLowContact cut (monomial e a) =
      if localContactOrder 3 e < cut then monomial e a else 0 := by
  classical
  by_cases hc : localContactOrder 3 e < cut
  · rw [ite_eq_left hc]
    ext v
    by_cases h : e = v
    · subst v
      simp [coeff_projectLowContact, hc]
    · simp [coeff_projectLowContact, coeff_monomial, h]
  · rw [ite_eq_right hc]
    ext v
    by_cases h : e = v
    · subst v
      simp [coeff_projectLowContact, hc]
    · simp [coeff_projectLowContact, coeff_monomial, h]

private theorem shift_projection (P : Local) :
    T ^ 48 * projectLowContact 90 P = projectLowContact 138 (T ^ 48 * P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial e a =>
      have hmul : T ^ 48 * monomial e a = monomial (Finsupp.single (localT 3) 48 + e) a := by
        rw [MvPolynomial.X_pow_eq_monomial, monomial_mul_monomial, one_mul]
      rw [project_monomial, hmul, project_monomial]
      have ho : localContactOrder 3 (Finsupp.single (localT 3) 48 + e) =
          48 + localContactOrder 3 e := by
        simp [localContactOrder, Finsupp.weight_single]
      have hlt : localContactOrder 3 (Finsupp.single (localT 3) 48 + e) < 138 ↔
          localContactOrder 3 e < 90 := by rw [ho]; omega
      by_cases he : localContactOrder 3 e < 90
      · simp [he, hlt.mpr he, hmul]
      · have hnot : ¬ localContactOrder 3 (Finsupp.single (localT 3) 48 + e) < 138 :=
          fun h => he (hlt.mp h)
        simp [he, hnot]
  | add P Q hP hQ => simp only [map_add, mul_add, hP, hQ]

private theorem jet_index_formula (m : Fin 4 →₀ ℕ) :
    m.weight jetIndex = m 1 + 2 * m 2 + 3 * m 3 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_four, jetIndex, Nat.mul_comm]

private def trimmed (u : JetVariable 3 →₀ ℕ) : Fin 4 →₀ ℕ :=
  u.some - Finsupp.single 0 (u.some.degree - residualDegree u.some.degree)

private theorem trimmed_other (u : JetVariable 3 →₀ ℕ) (j : Fin 4) (h : j ≠ 0) :
    trimmed u j = u (some j) := by
  simp [trimmed, Ne.symm h]

private theorem trimmed_id (u : JetVariable 3 →₀ ℕ) :
    (trimmed u).weight jetIndex = u.some.weight jetIndex := by
  rw [jet_index_formula, jet_index_formula]
  rw [trimmed_other u 1 (by decide), trimmed_other u 2 (by decide), trimmed_other u 3 (by decide)]
  simp

private theorem trimmed_value_and_degree (u : JetVariable 3 →₀ ℕ) (hu : AnchorEligible u) :
    trimmed u 0 + (u.some.degree - residualDegree u.some.degree) = u (some 0) ∧
      (trimmed u).degree = residualDegree u.some.degree := by
  have htotal : u.some.degree = u (some 0) + u (some 1) + u (some 2) + u (some 3) := by
    simp [Finsupp.degree_eq_sum, Fin.sum_univ_four]
  have hcap := hu.2.2.2.1
  have htrim : trimmed u 0 =
      u (some 0) - (u.some.degree - residualDegree u.some.degree) := by
    simp [trimmed]
  have hnew : (trimmed u).degree =
      trimmed u 0 + u (some 1) + u (some 2) + u (some 3) := by
    simp [Finsupp.degree_eq_sum, Fin.sum_univ_four, trimmed_other u 1 (by decide),
      trimmed_other u 2 (by decide), trimmed_other u 3 (by decide)]
  simp only [residualDegree] at *
  omega

private theorem trimmed_mem_band (u : JetVariable 3 →₀ ℕ) (hu : AnchorEligible u) :
    BandExponent (residualDegree u.some.degree) (-((u none : ℤ) - u.some.weight jetIndex))
      48 10 (trimmed u) := by
  refine ⟨(trimmed_value_and_degree u hu).2, ?_, ?_, ?_⟩
  · rw [trimmed_id]
    omega
  · rw [trimmed_id]
    exact_mod_cast hu.2.1
  · rw [trimmed_other u 3 (by decide)]
    exact hu.2.2.1

private theorem backShift_hom (u : JetVariable 3 →₀ ℕ) (hu : AnchorEligible u) (a : Geom) :
    (backShift (monomial (trimmed u) a)).IsWeightedHomogeneous
      (fun _ => (1 : ℕ)) (residualDegree u.some.degree) := by
  have h := isWeightedHomogeneous_monomial (fun _ : Fin 4 => (1 : ℕ)) (trimmed u) a
    (m := residualDegree u.some.degree)
    (by rw [← Finsupp.degree_eq_weight_one, (trimmed_value_and_degree u hu).2])
  apply h.bind₁
  intro j
  split_ifs
  · exact value_hom
  · exact isWeightedHomogeneous_X _ _ _

private theorem source_monomial_expr (u : JetVariable 3 →₀ ℕ) (a : Geom) :
    monomial u a = MvPolynomial.C a * MvPolynomial.X none ^ u none *
      MvPolynomial.X (some 0) ^ u (some 0) * MvPolynomial.X (some 1) ^ u (some 1) *
      MvPolynomial.X (some 2) ^ u (some 2) * MvPolynomial.X (some 3) ^ u (some 3) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_option]
  change _ * (_ * ∏ i : Fin 4, MvPolynomial.X (some i) ^ u (some i)) = _
  rw [Fin.prod_univ_four]
  ring

private theorem form_monomial_expr (m : Fin 4 →₀ ℕ) (a : Geom) :
    monomial m a = MvPolynomial.C a * MvPolynomial.X 0 ^ m 0 * MvPolynomial.X 1 ^ m 1 *
      MvPolynomial.X 2 ^ m 2 * MvPolynomial.X 3 ^ m 3 := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_four]
  ring

private theorem shifted_substitution (u : JetVariable 3 →₀ ℕ) (hu : AnchorEligible u) (a : Geom) :
    T ^ 48 * unscaledLocalSubstitution 3 0 0 (monomial u a) =
      T ^ (((u none : ℤ) - u.some.weight jetIndex) + 48).toNat *
        (liftJets valueForm) ^ (u.some.degree - residualDegree u.some.degree) *
        liftJets (backShift (monomial (trimmed u) a)) := by
  have hi := hu.2.1
  change u.some.weight jetIndex ≤ 48 at hi
  let r := (((u none : ℤ) - u.some.weight jetIndex) + 48).toNat
  have ht : r + u.some.weight jetIndex = u none + 48 := by dsimp [r]; omega
  rw [jet_index_formula] at ht
  simp only [Finsupp.some_apply] at ht
  have hv := (trimmed_value_and_degree u hu).1
  have h1 : unscaledLocalSubstitution (R := Geom) 3 0 0 (MvPolynomial.X (some 1)) =
      MvPolynomial.X (localY (0 : Fin 3)) := unscaledLocalSubstitution_Y_succ 3 0 0 0
  have h2 : unscaledLocalSubstitution (R := Geom) 3 0 0 (MvPolynomial.X (some 2)) =
      MvPolynomial.X (localY (1 : Fin 3)) := unscaledLocalSubstitution_Y_succ 3 0 0 1
  have h3 : unscaledLocalSubstitution (R := Geom) 3 0 0 (MvPolynomial.X (some 3)) =
      MvPolynomial.X (localY (2 : Fin 3)) := unscaledLocalSubstitution_Y_succ 3 0 0 2
  have b0 : backShift (MvPolynomial.X 0) = valueForm := by simp [backShift]
  have b (j : Fin 4) (hj : j ≠ 0) : backShift (MvPolynomial.X j) = MvPolynomial.X j := by
    simp [backShift, hj]
  rw [source_monomial_expr, form_monomial_expr]
  simp only [map_mul, map_pow, algHom_C, algebraMap_eq, unscaledLocalSubstitution_X, map_zero,
    zero_add, ← lift_value, h1, h2, h3, b0, b 1 (by decide), b 2 (by decide), b 3 (by decide),
    trimmed_other u 1 (by decide), trimmed_other u 2 (by decide), trimmed_other u 3 (by decide),
    liftJets_X]
  have hpow : T ^ r * T ^ u (some 1) * (T ^ 2) ^ u (some 2) * (T ^ 3) ^ u (some 3) =
      T ^ (u none + 48) := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  calc
    _ = T ^ (u none + 48) * MvPolynomial.C a * liftJets valueForm ^ u (some 0) *
        MvPolynomial.X (localY (0 : Fin 3)) ^ u (some 1) *
        MvPolynomial.X (localY (1 : Fin 3)) ^ u (some 2) *
        MvPolynomial.X (localY (2 : Fin 3)) ^ u (some 3) := by rw [pow_add]; ring
    _ = _ := by
      rw [← hpow, ← hv, pow_add]
      simp [liftImage, liftPower, liftVar, mul_pow]
      ring

private theorem shifted_constraint_monomial (u : JetVariable 3 →₀ ℕ) (hu : AnchorEligible u)
    (a : Geom) :
    let s := u.some.degree
    let g := (u none : ℤ) - u.some.weight jetIndex
    T ^ 48 * localConstraintAt 90 0 0 (monomial u a) =
      postprocess s g (blockMap s g ⟨monomial (trimmed u) a,
        (monomial_mem_restrictSupport (R := Geom)).mpr (Or.inl (trimmed_mem_band u hu))⟩) := by
  dsimp only [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [shift_projection, shifted_substitution u hu]
  have hi := hu.2.1
  change u.some.weight jetIndex ≤ 48 at hi
  let s := u.some.degree
  let g : ℤ := (u none : ℤ) - u.some.weight jetIndex
  let P := backShift (monomial (trimmed u) a)
  change postprocess s g P = postprocess s g
    (weightedTruncation targetOrder (orderCutoff s g).toNat P)
  exact (postprocess_truncate s g (by dsimp [g]; omega) (backShift_hom u hu a)).symm

theorem blockMap_eq_zero (s : ℕ) (g : ℤ) (h : 90 - (s : ℤ) ≤ g) :
    blockMap s g = 0 := by
  apply LinearMap.ext
  intro q
  change weightedTruncation targetOrder (orderCutoff s g).toNat (backShift q) = 0
  have hcut : (orderCutoff s g).toNat = 0 := by unfold orderCutoff; omega
  rw [hcut, weightedTruncation_eq_zero_iff, restrictWeightedOrder_zero]
  trivial

private abbrev Block := Fin 121 × Fin 138

private abbrev Image (b : Block) := LinearMap.range (blockMap b.1 (offset b.2))

private def merge {ι : Type} [Fintype ι] {V : ι → Submodule Geom Form}
    (post : ι → Form →ₗ[Geom] Local) : (∀ i, V i) →ₗ[Geom] Local :=
  ∑ i, (post i).comp ((V i).subtype.comp (LinearMap.proj i))

private theorem merge_single {ι : Type} [Fintype ι] [DecidableEq ι]
    {V : ι → Submodule Geom Form} (post : ι → Form →ₗ[Geom] Local) (i : ι) (v : V i) :
    merge post (Pi.single i v) = post i v := by
  rw [merge, LinearMap.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have hj' : (Pi.single i v : (k : ι) → V k) j = 0 :=
      Pi.single_eq_of_ne (M := fun k => ↥(V k)) hj v
    simp [hj']
  · simp

private def assemble : (∀ b : Block, Image b) →ₗ[Geom] Local :=
  merge (fun b => postprocess b.1 (offset b.2))

private theorem postprocess_mem_assemble (b : Block) (s : ℕ) (g : ℤ)
    (hs : (b.1 : ℕ) = s) (hg : offset b.2 = g)
    (q : bandSpace (residualDegree s) (-g) 48 10) :
    postprocess s g (blockMap s g q) ∈ LinearMap.range assemble := by
  subst s
  subst g
  let v : Image b := ⟨blockMap b.1 (offset b.2) q, LinearMap.mem_range_self _ q⟩
  exact ⟨Pi.single b v, merge_single (fun j : Block => postprocess j.1 (offset j.2)) b v⟩

private theorem shifted_monomial_mem_assemble (u : JetVariable 3 →₀ ℕ)
    (hu : AnchorEligible u) (a : Geom) :
    T ^ 48 * localConstraintAt 90 0 0 (monomial u a) ∈ LinearMap.range assemble := by
  classical
  let s := u.some.degree
  let g : ℤ := (u none : ℤ) - u.some.weight jetIndex
  let q : bandSpace (residualDegree s) (-g) 48 10 :=
    ⟨monomial (trimmed u) a, (monomial_mem_restrictSupport (R := Geom)).mpr (Or.inl (trimmed_mem_band u hu))⟩
  have hmono : T ^ 48 * localConstraintAt 90 0 0 (monomial u a) =
      postprocess s g (blockMap s g q) := shifted_constraint_monomial u hu a
  rw [hmono]
  by_cases hg : g < 90
  · have hJ := hu.2.1
    change u.some.weight jetIndex ≤ 48 at hJ
    have hs : s < 121 := by exact Nat.lt_succ_of_le hu.1
    have hr : (g + 48).toNat < 138 := by dsimp [g] at *; omega
    let b : Block := (⟨s, hs⟩, ⟨(g + 48).toNat, hr⟩)
    have ho : offset b.2 = g := by dsimp [b, offset, g]; omega
    exact postprocess_mem_assemble b s g rfl ho q
  · rw [blockMap_eq_zero s g (by omega), LinearMap.zero_apply, map_zero]
    exact Submodule.zero_mem _

/-- Translating to the origin leaves a contact image bounded by the sum of residual block ranks. -/
theorem rank_origin_le_blocks :
    Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) ≤
      ∑ s : Fin 121, ∑ r : Fin 138,
        Module.finrank Geom (LinearMap.range (blockMap s (offset r))) := by
  classical
  let shift := LinearMap.mulLeft Geom (T ^ 48)
  have hshift : Function.Injective shift :=
    fun _ _ h => mul_left_cancel₀ (pow_ne_zero _ (MvPolynomial.X_ne_zero _)) h
  let shifted := shift.comp (anchorLocal 0 0)
  have hdim : Module.finrank Geom (LinearMap.range shifted) =
      Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) := by
    rw [LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective shift hshift _).finrank_eq.symm
  have hsub : LinearMap.range shifted ≤ LinearMap.range assemble := by
    rintro _ ⟨Q, rfl⟩
    change shift (localConstraintAt 90 0 0 (Q : DifferentialPolynomial Geom 3)) ∈ _
    rw [(Q : DifferentialPolynomial Geom 3).as_sum, map_sum, map_sum]
    exact Submodule.sum_mem _ fun u hu => shifted_monomial_mem_assemble u (Q.property hu) _
  have (b : Block) : Module.Finite Geom (Image b) := by
    have : Module.Finite Geom (bandSpace (residualDegree b.1) (-offset b.2) 48 10) :=
      restrictSupport_finite ((Finsupp.finite_of_degree_le _).subset fun _ he =>
        Nat.le_of_eq he.1)
    infer_instance
  calc
    _ = Module.finrank Geom (LinearMap.range shifted) := hdim.symm
    _ ≤ Module.finrank Geom (LinearMap.range assemble) := Submodule.finrank_mono hsub
    _ ≤ Module.finrank Geom (∀ b : Block, Image b) := LinearMap.finrank_range_le assemble
    _ = _ := by rw [Module.finrank_pi_fintype, Fintype.sum_prod_type]

end

end K1_13_1_1
end PackSource_K1_13_1_1Blocks

section PackSource_K1_13_7_4_2Aux1
set_option autoImplicit true
namespace K1_13_7_4_2

noncomputable section

open scoped BigOperators Pointwise

section PowerScaling

variable {R ι : Type*} [CommRing R]

/-- Colength of an ideal in its ambient ring. -/
abbrev colength (I : Ideal R) : ℕ∞ := Module.length R (R ⧸ I)

private theorem mem_sup_span_singleton {I : Ideal R} {x y : R} :
    y ∈ I ⊔ Ideal.span {x} ↔ ∃ z, y - x * z ∈ I := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hb
    exact ⟨z, by simpa using ha⟩
  · rintro ⟨z, hz⟩
    exact ⟨y - x * z, hz, x * z, Ideal.mem_span_singleton.mpr ⟨z, rfl⟩,
      sub_add_cancel _ _⟩

/-- Filter by consecutive powers of a nonzerodivisor modulo the other cuts. -/
private theorem span_power_colength (I : Ideal R) (x : R)
    (hreg : ∀ y, x * y ∈ I → y ∈ I) (k : ℕ) :
    colength (I ⊔ Ideal.span {x ^ k}) = (k : ℕ∞) * colength (I ⊔ Ideal.span {x}) := by
  let P : ℕ → Ideal R := fun t => I ⊔ Ideal.span {x ^ t}
  have hmem (t : ℕ) (y : R) : y ∈ P t ↔ ∃ z, y - x ^ t * z ∈ I :=
    mem_sup_span_singleton
  have hstep (t : ℕ) (y : R) : x * y ∈ P (t + 1) ↔ y ∈ P t := by
    rw [hmem, hmem]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, hreg _ ?_⟩
      simpa only [pow_succ', mul_sub, mul_assoc] using hz
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      simpa only [pow_succ', mul_sub, mul_assoc] using I.mul_mem_left x hz
  have hP1 : P 1 = I ⊔ Ideal.span {x} := by simp [P]
  rw [← hP1]
  change colength (P k) = (k : ℕ∞) * colength (P 1)
  induction k with
  | zero =>
    have htop : P 0 = ⊤ := by simp [P]
    rw [htop]
    simp [Module.length_eq_zero]
  | succ k ih =>
    have hmap : (P k : Submodule R R) ≤
        Submodule.comap (LinearMap.mulLeft R x) (P (k + 1)) :=
      fun y hy => (hstep k y).2 hy
    have hle : P (k + 1) ≤ P 1 := by
      have hp : Ideal.span {x ^ (k + 1)} ≤ Ideal.span {x ^ 1} := by
        apply (Ideal.span_singleton_le_iff_mem _).mpr
        exact Ideal.mem_span_singleton.mpr ⟨x ^ k, by simp [pow_succ']⟩
      exact sup_le_sup_left hp _
    let f : (R ⧸ P k) →ₗ[R] (R ⧸ P (k + 1)) :=
      (P k).mapQ (P (k + 1)) (LinearMap.mulLeft R x) hmap
    let g : (R ⧸ P (k + 1)) →ₗ[R] (R ⧸ P 1) := Submodule.factor hle
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      obtain ⟨r, rfl⟩ := (P k).mkQ_surjective y
      rw [show f ((P k).mkQ r) = (P (k + 1)).mkQ (x * r) from rfl,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using (hstep k r).mp hy
    have hex : Function.Exact f g := by
      intro y
      obtain ⟨r, rfl⟩ := (P (k + 1)).mkQ_surjective y
      change (P 1).mkQ r = 0 ↔ ∃ t, f t = (P (k + 1)).mkQ r
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmem]
      constructor
      · rintro ⟨z, hz⟩
        refine ⟨(P k).mkQ z, ?_⟩
        change Ideal.Quotient.mk (P (k + 1)) (x * z) =
          Ideal.Quotient.mk (P (k + 1)) r
        have hz' : r - x * z ∈ I := by simpa only [pow_one] using hz
        exact (Ideal.Quotient.eq.mpr (Submodule.mem_sup_left hz')).symm
      · rintro ⟨t, ht⟩
        obtain ⟨z, rfl⟩ := (P k).mkQ_surjective t
        change Ideal.Quotient.mk (P (k + 1)) (x * z) =
          Ideal.Quotient.mk (P (k + 1)) r at ht
        have hr : r - x * z ∈ P 1 := hle (Ideal.Quotient.eq.mp ht.symm)
        obtain ⟨w, hw⟩ := (hmem 1 _).mp hr
        exact ⟨z + w, by simpa only [pow_one, mul_add, sub_sub] using hw⟩
    calc
      colength (P (k + 1)) = colength (P k) + colength (P 1) :=
        Module.length_eq_add_of_exact f g hf (Submodule.factor_surjective hle) hex
      _ = _ := by rw [ih, Nat.cast_succ, add_mul, one_mul]

private theorem span_range_eq_remaining_sup (f : ι → R) (i : ι) :
    Ideal.span (Set.range f) = remainingIdeal f i ⊔ Ideal.span {f i} := by
  classical
  rw [remainingIdeal, ← Ideal.span_union]
  congr 1
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    by_cases h : j = i
    · exact Or.inr (by simp [h])
    · exact Or.inl ⟨j, h, rfl⟩
  · rintro (⟨j, _, rfl⟩ | h)
    · exact ⟨j, rfl⟩
    · exact ⟨i, h.symm⟩

/-- Replacing the entries of the tuple by positive powers multiplies its
colength by the product of the exponents. -/
theorem power_colength {n : ℕ} (f : Fin n → R) (b : Fin n → ℕ) (hb : ∀ i, 0 < b i)
    (hreg : ∀ (e : Fin n → ℕ), (∀ j, 0 < e j) → ∀ i y,
      f i * y ∈ remainingIdeal (fun j => f j ^ e j) i →
      y ∈ remainingIdeal (fun j => f j ^ e j) i) :
    colength (Ideal.span (Set.range fun i => f i ^ b i)) =
      (↑(∏ i, b i) : ℕ∞) * colength (Ideal.span (Set.range f)) := by
  classical
  let e (s : Finset (Fin n)) (j : Fin n) : ℕ := if j ∈ s then b j else 1
  let F (s : Finset (Fin n)) (j : Fin n) : R := f j ^ e s j
  have he (s : Finset (Fin n)) : ∀ j, 0 < e s j := by
    intro j
    by_cases hj : j ∈ s <;> simp [e, hj, hb j]
  have hs (s : Finset (Fin n)) :
      colength (Ideal.span (Set.range (F s))) =
        (↑(∏ i ∈ s, b i) : ℕ∞) * colength (Ideal.span (Set.range f)) := by
    induction s using Finset.induction_on with
    | empty => simp [F, e]
    | @insert i s hi ih =>
      have hsame : remainingIdeal (F (insert i s)) i = remainingIdeal (F s) i := by
        unfold remainingIdeal
        congr 1
        exact Set.image_congr fun j hj => by
          have hji : j ≠ i := hj
          simp [F, e, hji]
      have hnew : F (insert i s) i = f i ^ b i := by simp [F, e]
      have hold : F s i = f i := by simp [F, e, hi]
      rw [span_range_eq_remaining_sup _ i, hsame, hnew,
        span_power_colength _ _ (hreg (e s) (he s) i) (b i),
        ← hold, ← span_range_eq_remaining_sup, ih, Finset.prod_insert hi, Nat.cast_mul, mul_assoc]
  simpa [F, e] using hs Finset.univ

/-- Positive powers preserve the radical of a tuple ideal. -/
theorem radical_span_powers (f : ι → R) (e : ι → ℕ) (he : ∀ i, 0 < e i) :
    (Ideal.span (Set.range fun i => f i ^ e i)).radical =
      (Ideal.span (Set.range f)).radical := by
  apply le_antisymm
  · apply Ideal.radical_mono
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hi : f i ∈ Ideal.span (Set.range f) := Ideal.subset_span (Set.mem_range_self i)
    exact Ideal.pow_mem_of_mem _ hi _ (he i)
  · apply (Ideal.radical_le_radical_iff).mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨e i, Ideal.subset_span ⟨i, rfl⟩⟩

end PowerScaling

section PowerLayers

variable {R : Type*} [CommRing R]

theorem colength_le_of_le {I J : Ideal R} (h : I ≤ J) : colength J ≤ colength I :=
  Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)

private def monomial {ι : Type*} (f : ι → R) {k : ℕ} (m : Sym ι k) : R :=
  (m.val.map f).prod

private theorem span_monomial {ι : Type*} (f : ι → R) (k : ℕ) :
    Ideal.span (Set.range (monomial f (k := k))) = Ideal.span (Set.range f) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top]
    apply (Ideal.eq_top_iff_one _).mpr
    exact Ideal.subset_span ⟨Sym.nil, rfl⟩
  | succ k ih =>
    rw [pow_succ', ← ih, Ideal.span_mul_span]
    congr 1
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      obtain ⟨i, m, rfl⟩ := m.exists_eq_cons_of_succ
      exact ⟨f i, ⟨i, rfl⟩, monomial f m, ⟨m, rfl⟩, by simp [monomial, Sym.coe_cons]⟩
    · rintro ⟨_, ⟨i, rfl⟩, _, ⟨m, rfl⟩, rfl⟩
      exact ⟨Sym.cons i m, by simp [monomial, Sym.coe_cons]⟩

private theorem colength_pow_succ {n : ℕ} (f : Fin n → R) (k : ℕ) :
    colength (Ideal.span (Set.range f) ^ (k + 1)) ≤
      colength (Ideal.span (Set.range f) ^ k) +
        (n.multichoose k : ℕ∞) * colength (Ideal.span (Set.range f)) := by
  classical
  let I := Ideal.span (Set.range f)
  let A : Submodule R R := I ^ (k + 1)
  let B : Submodule R R := I ^ k
  have hAB : A ≤ B := Ideal.pow_le_pow_right (Nat.le_succ k)
  let g : (R ⧸ A) →ₗ[R] (R ⧸ B) := Submodule.factor hAB
  let N := LinearMap.ker g
  let m := monomial f (k := k)
  have hspan : Ideal.span (Set.range m) = I ^ k := span_monomial f k
  have hm (u : Sym (Fin n) k) : m u ∈ I ^ k := hspan ▸ Ideal.subset_span ⟨u, rfl⟩
  let v (u : Sym (Fin n) k) : N :=
    ⟨A.mkQ (m u), by
      change B.mkQ (m u) = 0
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hm u⟩
  let L (u : Sym (Fin n) k) : R ⧸ I →ₗ[R] N :=
    (I : Submodule R R).liftQ (LinearMap.id.smulRight (v u)) (by
      intro r hr
      change r • v u = 0
      apply Subtype.ext
      change A.mkQ (r * m u) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      change r * m u ∈ I ^ (k + 1)
      rw [pow_succ']
      exact Ideal.mul_mem_mul hr (hm u))
  let e : (Sym (Fin n) k →₀ R ⧸ I) →ₗ[R] N := Finsupp.lsum R L
  have hsurj : Function.Surjective e := by
    have hgen : (I ^ k : Submodule R R) ≤
        (LinearMap.range (N.subtype.comp e)).comap A.mkQ := by
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨u, rfl⟩
      refine ⟨Finsupp.single u ((I : Submodule R R).mkQ 1), ?_⟩
      simp only [LinearMap.comp_apply, e, Finsupp.lsum_single, L, Submodule.liftQ_apply,
        Submodule.mkQ_apply, LinearMap.smulRight_apply, LinearMap.id_apply, one_smul]
      rfl
    intro z
    obtain ⟨r, hr⟩ := A.mkQ_surjective (z : R ⧸ A)
    have hzr : B.mkQ r = 0 := by
      have hz : g z = 0 := z.property
      simpa only [← hr, g, Submodule.factor_mk] using hz
    have hmem : r ∈ (I ^ k : Submodule R R) := by
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hzr
    obtain ⟨w, hw⟩ := hgen hmem
    exact ⟨w, Subtype.ext (hw.trans hr)⟩
  have hlen := Module.length_le_of_surjective e hsurj
  rw [Module.length_finsupp, ENat.card_eq_coe_fintype_card, Sym.card_sym_eq_multichoose,
    Fintype.card_fin] at hlen
  change Module.length R (R ⧸ A) ≤ Module.length R (R ⧸ B) + _
  rw [Module.length_eq_add_of_exact N.subtype g N.subtype_injective
    (Submodule.factor_surjective hAB) (LinearMap.exact_subtype_ker_map g), add_comm]
  exact add_le_add_right hlen _

/-- A power of an ideal generated by `n` elements has at most one copy of
the original quotient per monomial of degree below that power. -/
theorem colength_pow_le {n : ℕ} (f : Fin n → R) {t : ℕ} (ht : 0 < t) :
    colength (Ideal.span (Set.range f) ^ t) ≤
      ((t + n - 1).choose n : ℕ∞) * colength (Ideal.span (Set.range f)) := by
  let I := Ideal.span (Set.range f)
  have h (k : ℕ) : colength (I ^ k) ≤
      (∑ j ∈ Finset.range k, (n.multichoose j : ℕ∞)) * colength I := by
    induction k with
    | zero => simp [Module.length_eq_zero]
    | succ k ih =>
      rw [Finset.sum_range_succ, add_mul]
      exact (colength_pow_succ f k).trans (add_le_add ih le_rfl)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  simpa only [← Nat.cast_sum, Nat.sum_range_multichoose,
    show k + 1 + n - 1 = k + n by omega] using h (k + 1)

end PowerLayers

section GrowthComparison

private theorem ascFactorial_le {n : ℕ} (hn : n = 2 ∨ n = 3) {t : ℕ} (ht : 0 < t) :
    t.ascFactorial n ≤ t ^ n + 5 * t ^ (n - 1) := by
  rcases hn with rfl | rfl
  · calc
      t.ascFactorial 2 = t ^ 2 + t := by
        simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
        ring
      _ ≤ t ^ 2 + 5 * t ^ (2 - 1) := by simp only [Nat.reduceSub, pow_one]; omega
  · have h : 2 * t ≤ 2 * t ^ 2 := by
      apply Nat.mul_le_mul_left
      simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left t ht
    calc
      t.ascFactorial 3 = t ^ 3 + (3 * t ^ 2 + 2 * t) := by
        simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
        ring
      _ ≤ t ^ 3 + (3 * t ^ 2 + 2 * t ^ 2) := Nat.add_le_add_left (Nat.add_le_add_left h _) _
      _ = t ^ 3 + 5 * t ^ (3 - 1) := by ring

/-- Recover the leading-term comparison using one sufficiently large integer. -/
private theorem power_le_of_growth {n : ℕ} (hn : n = 2 ∨ n = 3) (M C : ℕ)
    (h : ∀ t : ℕ, 0 < t →
      (M * t + n - 1).choose n ≤ (t + n - 1).choose n * C) :
    M ^ n ≤ C := by
  by_contra! hc
  let t := 5 * C + 1
  have ht : 0 < t := Nat.succ_pos _
  have hnpos : 0 < n := by omega
  have hpow : 0 < t ^ (n - 1) := Nat.pow_pos ht
  have hnat : (M * t).ascFactorial n ≤ C * t.ascFactorial n := by
    simp only [Nat.ascFactorial_eq_factorial_mul_choose']
    exact (Nat.mul_le_mul_left _ (h t ht)).trans_eq (by ac_rfl)
  have hsmall : C * t.ascFactorial n < (C + 1) * t ^ n := calc
    C * t.ascFactorial n ≤ C * (t ^ n + 5 * t ^ (n - 1)) :=
      Nat.mul_le_mul_left _ (ascFactorial_le hn ht)
    _ = C * t ^ n + (5 * C) * t ^ (n - 1) := by ring
    _ < C * t ^ n + t * t ^ (n - 1) :=
      Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hpow) _
    _ = (C + 1) * t ^ n := by
      have he : n - 1 + 1 = n := by omega
      rw [← pow_succ', he, add_mul, one_mul]
  have hlarge : (C + 1) * t ^ n ≤ (M * t).ascFactorial n := calc
    (C + 1) * t ^ n ≤ M ^ n * t ^ n := Nat.mul_le_mul_right _ hc
    _ = (M * t) ^ n := (mul_pow _ _ _).symm
    _ ≤ (M * t).ascFactorial n := Nat.pow_succ_le_ascFactorial _ _
  exact (not_lt_of_ge (hlarge.trans hnat)) hsmall

/-- A containment in a maximal-ideal power and the corresponding Hilbert
function bound force a lower bound for the colength of the contained ideal. -/
theorem colength_ge_of_growth {R : Type*} [CommRing R] {n M : ℕ}
    (hn : n = 2 ∨ n = 3) (m : Ideal R) (f : Fin n → R)
    (hcontain : Ideal.span (Set.range f) ≤ m ^ M)
    (hgrow : ∀ t : ℕ, 0 < t → ((t + n - 1).choose n : ℕ∞) ≤ colength (m ^ t)) :
    (↑(M ^ n) : ℕ∞) ≤ colength (Ideal.span (Set.range f)) := by
  let I := Ideal.span (Set.range f)
  change (↑(M ^ n) : ℕ∞) ≤ colength I
  by_cases htop : colength I = ⊤
  · simp [htop]
  let C := (colength I).toNat
  have hC : (C : ℕ∞) = colength I := ENat.natCast_toNat htop
  rw [← hC, ENat.natCast_le_natCast]
  by_cases hM : M = 0
  · have hn0 : n ≠ 0 := by omega
    simp [hM, zero_pow hn0]
  have hMpos := Nat.pos_of_ne_zero hM
  apply power_le_of_growth hn M C
  intro t ht
  have hp : I ^ t ≤ m ^ (M * t) :=
    (Ideal.pow_right_mono hcontain t).trans_eq (pow_mul m M t).symm
  have h := (hgrow (M * t) (Nat.mul_pos hMpos ht)).trans
    ((colength_le_of_le hp).trans (colength_pow_le f ht))
  change (↑((M * t + n - 1).choose n) : ℕ∞) ≤
    ↑((t + n - 1).choose n) * colength I at h
  rw [← hC, ← ENat.natCast_mul] at h
  exact ENat.natCast_le_natCast.mp h

end GrowthComparison

end
end K1_13_7_4_2
end PackSource_K1_13_7_4_2Aux1

section PackSource_K1_13_2_3_4DataB
set_option autoImplicit true
namespace K1_13_2_3_4

-- Keep the kernel reductions sequential to bound peak memory.
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

open K1_13_2

private theorem bDenNeg {u : ℤ} (hu : u < 0) : denominator u = 0 := by
  simp [denominator, hu]

private theorem bCumNeg {d u : ℤ} (hu : u < 0) : cumulative d u = 0 := by
  simp [cumulative, hu]

private theorem bCumLow {d u : ℤ} (hd : 0 ≤ d) (hu : u ≤ d) :
    cumulative d u = denominator u := by
  by_cases hn : u < 0
  · rw [bCumNeg hn, bDenNeg hn]
  simp (disch := omega) [cumulative, hn, bDenNeg]
  omega

private theorem bCapLow {d u c : ℤ} (hd : 0 ≤ d) (hc : 0 ≤ c)
    (hu : u ≤ d) (ht : u < 3 * (c + 1)) :
    cappedCount d u c = denominator u := by
  simp (disch := omega) [cappedCount, bCumLow, bCumNeg]
  omega

-- At these grades the degree and upper bound coincide and equal three times the cap.
private def bFlag (s q k : ℤ) : Flag :=
  ⟨1650 - 3 * k, s - 1350 - q - 2 * k, 1650 - 3 * k, 550 - k, 1650 - q - 3 * k⟩

private theorem bOld (s q k : ℤ) (hs : 1758 ≤ s) (hs' : s ≤ 1865)
    (hq : 0 ≤ q) (hq' : q ≤ 70) (hk : 0 ≤ k) (hk' : k ≤ 256) :
    oldCount (bFlag s q k) = denominator (1650 - 3 * k) - denominator (s - 1350 - q - 2 * k - 1) := by
  simp (disch := omega) [oldCount, bFlag, bCapLow]

-- The two lower-cutoff terms in targetCount cancel and the shifted upper term vanishes.
private theorem bTarget (s q k : ℤ) (hs : 1758 ≤ s) (hs' : s ≤ 1865)
    (hq : 0 ≤ q) (hq' : q ≤ 70) (hk : 0 ≤ k) (hk' : k ≤ 256) :
    targetCount (bFlag s q k) = denominator (1650 - q - 3 * k - 1) := by
  simp (disch := omega) [targetCount, bFlag, bCumNeg, bCumLow]
  omega

private theorem bKernel (s q k : ℤ) (hs : 1758 ≤ s) (hs' : s ≤ 1865)
    (hq : 0 ≤ q) (hq' : q ≤ 70) (hk : 0 ≤ k) (hk' : k ≤ 256) :
    kernelLower (bFlag s q k) =
      denominator (1650 - 3 * k) - denominator (s - 1350 - q - 2 * k - 1) - denominator (1650 - q - 3 * k - 1) := by
  have h := bOld s q k hs hs' hq hq' hk hk'
  have t := bTarget s q k hs hs' hq hq' hk hk'
  unfold kernelLower
  rw [ite_eq_right, h, t]
  simp [bFlag]
  omega

-- A single rounded cubic gives D(index - 1) for positive indices.
-- At index zero it also gives the zero required for every negative argument.
private def bDen (i : ℕ) : ℕ := (((2 * i + 15) * i + 30) * i + 25) / 72

private theorem bTwiceHalf (x : ℤ) : 2 * (x * (x - 1) / 2) = x * (x - 1) := by
  have h : (2 : ℤ) ∣ x * (x - 1) := by
    rcases Int.emod_two_eq_zero_or_one x with hx | hx
    · exact dvd_mul_of_dvd_left (by omega : (2 : ℤ) ∣ x) _
    · exact dvd_mul_of_dvd_right (by omega : (2 : ℤ) ∣ x - 1) _
  rw [mul_comm, Int.ediv_mul_cancel h]

private theorem bTwiceDen (u : ℤ) (hu : 0 ≤ u) :
    let a := u / 6
    let b := u % 6
    2 * denominator u = ((12 * a + 21 + 6 * b) * a + 11 + (7 + b) * b) * a + b * (b + 1) + 2 := by
  let a := u / 6
  let b := u % 6
  simp only [denominator, ite_eq_right (not_lt.mpr hu)]
  change 2 * (1 + b * (b + 1) / 2 + a * (22 + 7 * b + b * (b - 1) / 2) +
    (57 + 6 * b) * (a * (a - 1) / 2) + 6 * a * (a - 1) * (a - 2)) =
      ((12 * a + 21 + 6 * b) * a + 11 + (7 + b) * b) * a + b * (b + 1) + 2
  have h := bTwiceHalf (b + 1)
  rw [show (b + 1) * (b + 1 - 1) = b * (b + 1) by ring] at h
  linear_combination h + a * bTwiceHalf b + (57 + 6 * b) * bTwiceHalf a

-- In each of the six residue classes the extra numerator lies in [0, 72).
private theorem bRound (a b v : ℤ) (hb : 0 ≤ b) (hb' : b ≤ 5)
    (hv : 2 * v = ((12 * a + 21 + 6 * b) * a + 11 + (7 + b) * b) * a + b * (b + 1) + 2) :
    v = (((2 * (6 * a + b + 1) + 15) * (6 * a + b + 1) + 30) * (6 * a + b + 1) + 25) / 72 := by
  let r := ((2 * b + 21) * b + 66) * b + 72 - 36 * (b * (b + 1) + 2)
  have he : ((2 * (6 * a + b + 1) + 15) * (6 * a + b + 1) + 30) * (6 * a + b + 1) + 25 =
      72 * v + r := by
    dsimp only [r]
    linear_combination -36 * hv
  have hr : 0 ≤ r ∧ r < 72 := by
    dsimp only [r]
    interval_cases b <;> decide
  omega

private theorem bDenNat (u : ℕ) : denominator u = (bDen (u + 1) : ℤ) := by
  simp only [bDen, Int.natCast_ediv, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  have h := bRound ((u : ℤ) / 6) ((u : ℤ) % 6) (denominator u)
    (by omega) (by omega) (bTwiceDen (u : ℤ) (by omega))
  rwa [show 6 * ((u : ℤ) / 6) + (u : ℤ) % 6 = u by omega] at h

private theorem bDenInt (u : ℤ) : denominator u = (bDen (u + 1).toNat : ℤ) := by
  by_cases h : u < 0
  · rw [bDenNeg h, show (u + 1).toNat = 0 by omega]
    rfl
  have hh := bDenNat u.toNat
  rwa [show (u.toNat : ℤ) = u by omega, show u.toNat + 1 = (u + 1).toNat by omega] at hh

private def bSavings (s q k : ℕ) : ℕ :=
  let old := bDen 1651 - bDen (s - (1350 + q))
  let lower := old - bDen (1650 - q)
  let after := bDen (1651 - 3 * k) - bDen (s - (1350 + q + 2 * k)) - bDen (1650 - q - 3 * k)
  (old - lower) - (old - max lower after)

private theorem bClip (a b t c d v : ℕ) :
    let old := (a : ℤ) - b
    let lower := max 0 (old - t)
    (old - lower).toNat - (old - max lower ((c : ℤ) - d - v)).toNat =
      let old' := a - b
      let lower' := old' - t
      (old' - lower') - (old' - max lower' (c - d - v)) := by
  dsimp only
  have subNat (x y : ℤ) (hy : 0 ≤ y) : (x - y).toNat = x.toNat - y.toNat := by omega
  have maxNat (x y : ℤ) : (max x y).toNat = max x.toNat y.toNat := by omega
  simp (disch := omega) only [subNat, maxNat, Int.toNat_natCast, Int.toNat_zero, Nat.zero_max]

private theorem bSavings_eq {s q k : ℕ} (hs : 1758 ≤ s) (hs' : s ≤ 1865)
    (hq : q ≤ 70) (hk : k ≤ 256) (hk0 : k ≠ 0) : entry s q k = bSavings s q k := by
  have hj : 993 ≤ 3000 + q - s ∧ 3000 + q - s ≤ 1581 := by omega
  have hw : windowFlag s (3000 + q - s) = bFlag s q 0 := by
    simp only [windowFlag, bFlag]
    congr 1 <;> omega
  have hc : cubicFlag (bFlag s q 0) k = bFlag s q k := by
    simp [bFlag, cubicFlag]
  simp only [entry, ite_eq_left hj, cubicSavings, ite_eq_right hk0, hw, hc]
  have ho := bOld s q 0 (by omega) (by omega) (by omega) (by omega) (by decide) (by decide)
  have hbase := bKernel s q 0 (by omega) (by omega) (by omega) (by omega) (by decide) (by decide)
  have hres := bKernel s q k (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [ho, hbase, hres]
  simp (disch := omega) only [bDenInt]
  have h1 : ((1650 : ℤ) - 3 * 0 + 1).toNat = 1651 := by decide
  have h2 : ((s : ℤ) - 1350 - q - 2 * 0 - 1 + 1).toNat = s - (1350 + q) := by omega
  have h3 : ((1650 : ℤ) - q - 3 * 0 - 1 + 1).toNat = 1650 - q := by omega
  have h4 : ((1650 : ℤ) - 3 * k + 1).toNat = 1651 - 3 * k := by omega
  have h5 : ((s : ℤ) - 1350 - q - 2 * k - 1 + 1).toNat = s - (1350 + q + 2 * k) := by omega
  have h6 : ((1650 : ℤ) - q - 3 * k - 1 + 1).toNat = 1650 - q - 3 * k := by omega
  simp only [h1, h2, h3, h4, h5, h6]
  apply bClip

private theorem bZeroRow (s q n : ℕ) : rowSum s q 0 n = 0 := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    have hz : entry s q 0 = 0 := by simp [entry, cubicSavings]
    simp [rowSum, hz, ih]

-- A zero suffix contributes nothing. The original entry covers digits outside
-- the range in which bSavings_eq specializes the flag arithmetic.
private def bRow (s q code : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if code = 0 then 0 else
      let k := code % 512
      (if k = 0 then 0 else if k ≤ 256 then bSavings s q k else entry s q k) +
        bRow s (q + 1) (code / 512) n

private theorem bRow_eq (s q code n : ℕ) (hs : 1758 ≤ s) (hs' : s ≤ 1865)
    (hq : q + n ≤ 71) : rowSum s q code n = bRow s q code n := by
  induction n generalizing q code with
  | zero => rfl
  | succ n ih =>
    by_cases hz : code = 0
    · subst code
      rw [bZeroRow]
      simp [bRow]
    rw [rowSum, bRow, ite_eq_right hz, ih _ _ (by omega)]
    by_cases hk0 : code % 512 = 0
    · simp [hk0, entry, cubicSavings]
    by_cases hk : code % 512 ≤ 256
    · simp only [ite_eq_right hk0, ite_eq_left hk, bSavings_eq (q := q) hs hs' (by omega) hk hk0]
    · simp only [ite_eq_right hk0, ite_eq_right hk]

private def bRows (s : ℕ) : List ℕ → ℕ
  | [] => 0
  | c :: cs => bRow s 0 c 71 + bRows (s + 1) cs

private theorem bRows_eq (s : ℕ) (cs : List ℕ) (lo : 1758 ≤ s)
    (hi : s + cs.length ≤ 1866) : rowsSum s cs = bRows s cs := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.length_cons] at hi
    rw [rowsSum, bRows, bRow_eq _ _ _ _ lo (by omega) (by decide), ih _ (by omega) (by omega)]



/-- The certificate encodes a row per grade. The base-512 digit of index
`q` is the cubic exponent on the diagonal `s + j = 3000 + q`. -/
private def rowsB1_chunk000 : List ℕ := [
  21824427147138291642878122648045419253929843162672815214528917204165034344640,
  29061460331456146707176124106804482419221782748606954946746290570995414696128,
  29075595161894267116114070081990462490711275639870992910060818919953405149376,
  36312628346212122583715858033406414330796557175693122701881081764822850306240]

private theorem rowsB1_chunk000_checked :
    rowsB1_chunk000.length = 4 ∧ rowsSum 1758 rowsB1_chunk000 = 43976193 := by
  constructor
  · rfl
  · rw [bRows_eq 1758 rowsB1_chunk000 (by decide) (by decide)]
    decide +kernel

private def rowsB1_chunk004 : List ℕ := [
  3748910679562072355837687470924870409099226220020367269744761244920480595542208,
  7454285804763146957277268114628668959258638917664323498119047782533602614542528,
  7461522810556264105121684255162748015755069417296050784500836123113453774799040,
  11174106671727714621291663473068551652486774022254066399141142682808166062850240]

private theorem rowsB1_chunk004_checked :
    rowsB1_chunk004.length = 4 ∧ rowsSum 1762 rowsB1_chunk004 = 45785842 := by
  constructor
  · rfl
  · rw [bRows_eq 1762 rowsB1_chunk004 (by decide) (by decide)]
    decide +kernel

private def rowsB1_chunk008 : List ℕ := [
  11174106699334805320751864284734507066738731691740806103338908981842037891498176,
  14879467689705547114074175542637126923946218675373618628940015600633980314026176,
  18592065713260501244079312065643980414342504881773849259675295923396667009761472,
  1919442267935780624939729310884786857764392004487801219973056894966739662469693632]

private theorem rowsB1_chunk008_checked :
    rowsB1_chunk008.length = 4 ∧ rowsSum 1766 rowsB1_chunk008 = 47566533 := by
  constructor
  · rfl
  · rw [bRows_eq 1766 rowsB1_chunk008 (by decide) (by decide)]
    decide +kernel

private def rowsB1_chunk012 : List ℕ := [
  1919456741946935710713323931486659735447285483398511244703942611008441462129000640,
  3816594332038731242125961274689878507140247540142801790488625170638209007457763520,
  5717437269068995767642089357025669666289968118890903436548795668654309397231665344]

private theorem rowsB1_chunk012_checked :
    rowsB1_chunk012.length = 3 ∧ rowsSum 1770 rowsB1_chunk012 = 37033122 := by
  constructor
  · rfl
  · rw [bRows_eq 1770 rowsB1_chunk012 (by decide) (by decide)]
    decide +kernel

private def rowsB1 : List ℕ := rowsB1_chunk000 ++ rowsB1_chunk004 ++ rowsB1_chunk008 ++ rowsB1_chunk012

private theorem rowsB1_checked :
    rowsB1.length = 15 ∧ rowsSum 1758 rowsB1 = 174361690 := by
  constructor
  · simp only [rowsB1, List.length_append, Nat.reduceAdd, rowsB1_chunk000_checked.1,
      rowsB1_chunk004_checked.1, rowsB1_chunk008_checked.1, rowsB1_chunk012_checked.1]
  · simp only [rowsB1, rowsSum_append, List.length_append, Nat.reduceAdd,
      rowsB1_chunk000_checked.1, rowsB1_chunk004_checked.1, rowsB1_chunk008_checked.1,
      rowsB1_chunk000_checked.2, rowsB1_chunk004_checked.2, rowsB1_chunk008_checked.2,
      rowsB1_chunk012_checked.2]

private def rowsB2_chunk000 : List ℕ := [
  5721142630059420324221740636157067774628768923627620760876922444823069485040763072,
  7618287457129186202512643575012137787995310653773894581055011374302956925774561472,
  7621992818119610758886606784484371451726644837517376455298176772472233411532128448,
  980853583758053912096699561189369171293346782025537970179170670527737996391676477632]

private theorem rowsB2_chunk000_checked :
    rowsB2_chunk000.length = 4 ∧ rowsSum 1773 rowsB2_chunk000 = 51174475 := by
  constructor
  · rfl
  · rw [bRows_eq 1773 rowsB2_chunk000 (by decide) (by decide)]
    decide +kernel

private def rowsB2_chunk004 : List ℕ := [
  982761851876831083885221852921169784537592011733818214080643289935370973585472585920,
  1954096298003830395863179880969595617864738779386507846515379746583928821682767233216,
  1955993435650461297572607420458350406303565438873448965545355830033757799979440767168,
  2929225019353390021578569537815525211822642449320110290753989112306035895066274398400]

private theorem rowsB2_chunk004_checked :
    rowsB2_chunk004.length = 4 ∧ rowsSum 1777 rowsB2_chunk004 = 53211888 := by
  constructor
  · rfl
  · rw [bRows_eq 1777 rowsB2_chunk004 (by decide) (by decide)]
    decide +kernel

private def rowsB2_chunk008 : List ℕ := [
  3900559472703287741461262159124178153908296448441828453497431089689676794457382551744,
  3902460315640207524232293297424596884289860480837383881900444707170151789860485169344,
  502197034884123602993510175328160118015074447678322192920914394609513205188832197181632,
  503170273885757276090069882554146274391939806676290312334291743379614665646368614351040]

private theorem rowsB2_chunk008_checked :
    rowsB2_chunk008.length = 4 ∧ rowsSum 1781 rowsB2_chunk008 = 55266253 := by
  constructor
  · rfl
  · rw [bRows_eq 1781 rowsB2_chunk008 (by decide) (by decide)]
    decide +kernel

private def rowsB2_chunk012 : List ℕ := [
  1000497304570724157104615836842459769777857254255739031052415096590601952332545263763648,
  1001468639024074027217407830009844715800067458465418086527458277378811894955100042526912]

private theorem rowsB2_chunk012_checked :
    rowsB2_chunk012.length = 2 ∧ rowsSum 1785 rowsB2_chunk012 = 28420456 := by
  constructor
  · rfl
  · rw [bRows_eq 1785 rowsB2_chunk012 (by decide) (by decide)]
    decide +kernel

private def rowsB2 : List ℕ := rowsB2_chunk000 ++ rowsB2_chunk004 ++ rowsB2_chunk008 ++ rowsB2_chunk012

private theorem rowsB2_checked :
    rowsB2.length = 14 ∧ rowsSum 1773 rowsB2 = 188073072 := by
  constructor
  · simp only [rowsB2, List.length_append, Nat.reduceAdd, rowsB2_chunk000_checked.1,
      rowsB2_chunk004_checked.1, rowsB2_chunk008_checked.1, rowsB2_chunk012_checked.1]
  · simp only [rowsB2, rowsSum_append, List.length_append, Nat.reduceAdd,
      rowsB2_chunk000_checked.1, rowsB2_chunk004_checked.1, rowsB2_chunk008_checked.1,
      rowsB2_chunk000_checked.2, rowsB2_chunk004_checked.2, rowsB2_chunk008_checked.2,
      rowsB2_chunk012_checked.2]

private def rowsB3_chunk000 : List ℕ := [
  1499763209908935691048016978374908007575356763167775251437931100702035226228287483248832,
  1997086450024083323628166225471579214801002109676049576822898637212135137662444037570752,
  1998059681607786252352171776212009356597005581071004408438545572930689541538161048518848,
  257124881860671284732677209768016411145291114831044391308378714741060930172193911093690561]

private theorem rowsB3_chunk000_checked :
    rowsB3_chunk000.length = 4 ∧ rowsSum 1787 rowsB3_chunk000 = 58605477 := by
  constructor
  · rfl
  · rw [bRows_eq 1787 rowsB3_chunk000 (by decide) (by decide)]
    decide +kernel

private def rowsB3_chunk004 : List ℕ := [
  257623180229507711223339261640246521308235272152773333429566260944263033682013855294783681,
  512254619940210768437563308462931390510457932562936720853545219067731028403356446880792770,
  512751943180325901935312808965040494486629691367941723735429325421450915429743595031199938,
  767878763473375073816584692927952899878582662741900928570064688785122354371535554333475011]

private theorem rowsB3_chunk004_checked :
    rowsB3_chunk004.length = 4 ∧ rowsSum 1791 rowsB3_chunk004 = 60830669 := by
  constructor
  · rfl
  · rw [bRows_eq 1791 rowsB3_chunk004 (by decide) (by decide)]
    decide +kernel

private def rowsB3_chunk008 : List ℕ := [
  1022508262412323424664328949798912188392358894218118388661437246176893073227601358627111107,
  1023006556983186561204311949420548790577666811836428090363652963496235793224933087209685188,
  131647938541329251670266195941287761024958437022289233003033357241469455837256544243880657092,
  131903068275610810556285513413985628420873481746527902108275419451930222475782859576188174534]

private theorem rowsB3_chunk008_checked :
    rowsB3_chunk008.length = 4 ∧ rowsSum 1795 rowsB3_chunk008 = 63192444 := by
  constructor
  · rfl
  · rw [bRows_eq 1795 rowsB3_chunk008 (by decide) (by decide)]
    decide +kernel

private def rowsB3_chunk012 : List ℕ := [
  262274365409387884477820114114764928831977200309447997614763356902805841865374023831154426054,
  262528994908326861790880158189891831229868237703699818536774217721123818811522160955479916742]

private theorem rowsB3_chunk012_checked :
    rowsB3_chunk012.length = 2 ∧ rowsSum 1799 rowsB3_chunk012 = 32409390 := by
  constructor
  · rfl
  · rw [bRows_eq 1799 rowsB3_chunk012 (by decide) (by decide)]
    decide +kernel

private def rowsB3 : List ℕ := rowsB3_chunk000 ++ rowsB3_chunk004 ++ rowsB3_chunk008 ++ rowsB3_chunk012

private theorem rowsB3_checked :
    rowsB3.length = 14 ∧ rowsSum 1787 rowsB3 = 215037980 := by
  constructor
  · simp only [rowsB3, List.length_append, Nat.reduceAdd, rowsB3_chunk000_checked.1,
      rowsB3_chunk004_checked.1, rowsB3_chunk008_checked.1, rowsB3_chunk012_checked.1]
  · simp only [rowsB3, rowsSum_append, List.length_append, Nat.reduceAdd,
      rowsB3_chunk000_checked.1, rowsB3_chunk004_checked.1, rowsB3_chunk008_checked.1,
      rowsB3_chunk000_checked.2, rowsB3_chunk004_checked.2, rowsB3_chunk008_checked.2,
      rowsB3_chunk012_checked.2]

private def rowsB4_chunk000 : List ℕ := [
  393153926898368037779956586260884810099629461466337530894068449703337103790479912149209678022,
  523524230355109593428136422297043040455355258298810726050894624286238085270850616115530399944,
  523779357175391519336607717997597312966345423910928523258048709878366167435799158900706607304,
  67403744533160573149815081095419755717829335161821473582592952719408791139519767887881957376200]

private theorem rowsB4_chunk000_checked :
    rowsB4_chunk000.length = 4 ∧ rowsSum 1801 rowsB4_chunk000 = 66698494 := by
  constructor
  · rfl
  · rw [bRows_eq 1801 rowsB4_chunk000 (by decide) (by decide)]
    decide +kernel

private def rowsB4_chunk004 : List ℕ := [
  67534370957112735004818182867855329459818665467524367851583201845534692509983537509866666033352,
  134284475089606596852643898426759232185045281576300356148425231210264482724176761656935073284296,
  201164440265591793311775069311023121171027053934403601362494993146329176530353119470450762678472,
  201294810571964435343337772165466064973999768161101407725246533797628533519914280496752620568780]

private theorem rowsB4_chunk004_checked :
    rowsB4_chunk004.length = 4 ∧ rowsSum 1805 rowsB4_chunk004 = 69282112 := by
  constructor
  · rfl
  · rw [bRows_eq 1805 rowsB4_chunk004 (by decide) (by decide)]
    decide +kernel

private def rowsB4_chunk008 : List ℕ := [
  268044405941816111835205848216086036713138827257909359916615046791159001649524467563885980909772,
  268175030873800457893077876484401107874737700002417187832002709029989846091415634678252031803596,
  34577467050480238934590926732728424482281439612892865746451262414272060043450779469199432608743628,
  68753390504776281640787256927054762517070429065106299246104782079995351432998244765056107955716300]

private theorem rowsB4_chunk008_checked :
    rowsB4_chunk008.length = 4 ∧ rowsSum 1809 rowsB4_chunk008 = 71729271 := by
  constructor
  · rfl
  · rw [bRows_eq 1809 rowsB4_chunk008 (by decide) (by decide)]
    decide +kernel

private def rowsB4_chunk012 : List ℕ := [
  68753651245878577588553675994500726878743184155093160934935405530764948874570955137958838169338060]

private theorem rowsB4_chunk012_checked :
    rowsB4_chunk012.length = 1 ∧ rowsSum 1813 rowsB4_chunk012 = 18309315 := by
  constructor
  · rfl
  · rw [bRows_eq 1813 rowsB4_chunk012 (by decide) (by decide)]
    decide +kernel

private def rowsB4 : List ℕ := rowsB4_chunk000 ++ rowsB4_chunk004 ++ rowsB4_chunk008 ++ rowsB4_chunk012

private theorem rowsB4_checked :
    rowsB4.length = 13 ∧ rowsSum 1801 rowsB4 = 226019192 := by
  constructor
  · simp only [rowsB4, List.length_append, Nat.reduceAdd, rowsB4_chunk000_checked.1,
      rowsB4_chunk004_checked.1, rowsB4_chunk008_checked.1, rowsB4_chunk012_checked.1]
  · simp only [rowsB4, rowsSum_append, List.length_append, Nat.reduceAdd,
      rowsB4_chunk000_checked.1, rowsB4_chunk004_checked.1, rowsB4_chunk008_checked.1,
      rowsB4_chunk000_checked.2, rowsB4_chunk004_checked.2, rowsB4_chunk008_checked.2,
      rowsB4_chunk012_checked.2]

private def rowsB5_chunk000 : List ℕ := [
  102996193415982998175614361476035042996816956930845070340167375286250461921569518819625724473869004,
  103062943012845790895788939348718625266687881250593435103223641673107586543131997946138430992909004,
  137238735842209849259625394286636050796725344997094359056362043669466859839572085844683170984854736,
  17669487206646215790739594036999697123890862852629209689225024489854023833254021835771025808943056080]

private theorem rowsB5_chunk000_checked :
    rowsB5_chunk000.length = 4 ∧ rowsSum 1814 rowsB5_chunk000 = 74964634 := by
  constructor
  · rfl
  · rw [bRows_eq 1814 rowsB5_chunk000 (by decide) (by decide)]
    decide +kernel

private def rowsB5_chunk004 : List ℕ := [
  17703663129845882334510554487129238509754266224092229570651202315631877380341678546493527941619746512,
  35201869437635201256963225235508674005746820615856007757212583879336492906155061595475767620750378704,
  35236045230464566286657802456455478010362991304615665819534584338182542517640056348498247281432168656,
  52768226821558029625335735832964466302384138196438057612730930092605686523768292782658714256330033360]

private theorem rowsB5_chunk004_checked :
    rowsB5_chunk004.length = 4 ∧ rowsSum 1818 rowsB5_chunk004 = 77713468 := by
  constructor
  · rfl
  · rw [bRows_eq 1818 rowsB5_chunk004 (by decide) (by decide)]
    decide +kernel

private def rowsB5_chunk008 : List ℕ := [
  70266232620841140333623954763484907059163055970211390320486844595951626679794191994211269088118933712,
  70266299500806315349368276719157937461893121307642181786543625702435796506700285774048610153276738768,
  9046777449802862484858672146943844927431916092451970281474066644838226083831965840326309796612214459600,
  9064309698273666489830722217757468829827811458468891966367327421915808671333158629641839358255938243792]

private theorem rowsB5_chunk008_checked :
    rowsB5_chunk008.length = 4 ∧ rowsSum 1822 rowsB5_chunk008 = 80477410 := by
  constructor
  · rfl
  · rw [bRows_eq 1822 rowsB5_chunk008 (by decide) (by decide)]
    decide +kernel

private def rowsB5 : List ℕ := rowsB5_chunk000 ++ rowsB5_chunk004 ++ rowsB5_chunk008

private theorem rowsB5_checked :
    rowsB5.length = 12 ∧ rowsSum 1814 rowsB5 = 233155512 := by
  constructor
  · simp only [rowsB5, List.length_append, Nat.reduceAdd, rowsB5_chunk000_checked.1,
      rowsB5_chunk004_checked.1, rowsB5_chunk008_checked.1]
  · simp only [rowsB5, rowsSum_append, List.length_append, Nat.reduceAdd,
      rowsB5_chunk000_checked.1, rowsB5_chunk004_checked.1, rowsB5_chunk000_checked.2,
      rowsB5_chunk004_checked.2, rowsB5_chunk008_checked.2]

private def rowsB6_chunk000 : List ℕ := [
  18023357152199593346050548787326776862054543923453407724783007652068824559638846440196412352445183790288,
  26999834126709074780998563979978981853792227848832153888434931629463635376324425396733083234857482555608,
  27017332132637711168171896746477806746820678756576285497706818225872463819850773098879933713146250891480,
  35976311101870663850815464838890082423802483254462715118331619903847053927472950529657262401977961255128]

private theorem rowsB6_chunk000_checked :
    rowsB6_chunk000.length = 4 ∧ rowsSum 1826 rowsB6_chunk000 = 83124628 := by
  constructor
  · rfl
  · rw [bRows_eq 1826 rowsB6_chunk000 (by decide) (by decide)]
    decide +kernel

private def rowsB6_chunk004 : List ℕ := [
  44952822318922314396501306820299582063898683846960496654799960803359437837417297034260975518041493311704,
  4640909033334526403962398348432366808275426124905681898577956059640330324970815393861996041907884632674520,
  9227923865847845415484094202736692519890637112346625446197353177416633443820321164723489194628102941153496,
  9227958861926191793177880979111281483818784310991063534840668156237239405479586490056222635177014743898328]

private theorem rowsB6_chunk004_checked :
    rowsB6_chunk004.length = 4 ∧ rowsSum 1830 rowsB6_chunk004 = 86155640 := by
  constructor
  · rfl
  · rw [bRows_eq 1830 rowsB6_chunk004 (by decide) (by decide)]
    decide +kernel

private def rowsB6_chunk008 : List ℕ := [
  13832874051843757504713494526871512486254107240591001389018284861486255686039061278405234729822600980437208,
  18419871284157649521313089921509975291391893764175779327696083431598312769422862811130246735752870366910680,
  18419871284157779891617517997511722200986871426284910140579943383523469711413467754421711917623999057205504,
  2371558427801121452860489265881330413392344544518439068556320985315208364980815691570692945606271479824881920]

private theorem rowsB6_chunk008_checked :
    rowsB6_chunk008.length = 4 ∧ rowsSum 1834 rowsB6_chunk008 = 89076513 := by
  constructor
  · rfl
  · rw [bRows_eq 1834 rowsB6_chunk008 (by decide) (by decide)]
    decide +kernel

private def rowsB6 : List ℕ := rowsB6_chunk000 ++ rowsB6_chunk004 ++ rowsB6_chunk008

private theorem rowsB6_checked :
    rowsB6.length = 12 ∧ rowsSum 1826 rowsB6 = 258356781 := by
  constructor
  · simp only [rowsB6, List.length_append, Nat.reduceAdd, rowsB6_chunk000_checked.1,
      rowsB6_chunk004_checked.1, rowsB6_chunk008_checked.1]
  · simp only [rowsB6, rowsSum_append, List.length_append, Nat.reduceAdd,
      rowsB6_chunk000_checked.1, rowsB6_chunk004_checked.1, rowsB6_chunk000_checked.2,
      rowsB6_chunk004_checked.2, rowsB6_chunk008_checked.2]

private def rowsB7_chunk000 : List ℕ := [
  2376154401544252028309685579146511896555101584536301239155143703978420834645809726974939491931156888268151040,
  4724714937272034405531843176746540638918701312992318111663706018497357628115258659170279616842581242272651520,
  7077844517312023569019777299881211974116899127860526691272910232153144806962384155860942558304445804563243264,
  7082431514578179634988043759076534740260815741016235983535062447304363272570710540772076868537945547051475200]

private theorem rowsB7_chunk000_checked :
    rowsB7_chunk000.length = 4 ∧ rowsSum 1838 rowsB7_chunk000 = 91876466 := by
  constructor
  · rfl
  · rw [bRows_eq 1838 rowsB7_chunk000 (by decide) (by decide)]
    decide +kernel

private def rowsB7_chunk004 : List ℕ := [
  9430974097488716554912302039813107349192595687364664714500805382858959117888711468918899198555912694769754368,
  1214237915034174183864315874634195641075230102299611648612808501939743564114422723793797722204848680208090898688,
  1216586457616948083842054857256470583528684407140852704306056965896935960961398148088949237242598248829731578112,
  2419044855970859651174227711576196401917300413376599468734205483066339991670494146457796907278498258001596621056]

private theorem rowsB7_chunk004_checked :
    rowsB7_chunk004.length = 4 ∧ rowsSum 1842 rowsB7_chunk004 = 95136682 := by
  constructor
  · rfl
  · rw [bRows_eq 1842 rowsB7_chunk004 (by decide) (by decide)]
    decide +kernel

private def rowsB7_chunk008 : List ℕ := [
  3623856392863756067337871348042138719987041190764860322291800456202723246640742905302537734200725933784393949440,
  3626204935446529900566019436721861146068365279068192151254512716551472438269913489633519315263787554558649147648,
  4828658737844230852791671960317086644407572680810213091852441327334411803614584996185136012282693880377868656896]

private theorem rowsB7_chunk008_checked :
    rowsB7_chunk008.length = 3 ∧ rowsSum 1846 rowsB7_chunk008 = 73419578 := by
  constructor
  · rfl
  · rw [bRows_eq 1846 rowsB7_chunk008 (by decide) (by decide)]
    decide +kernel

private def rowsB7 : List ℕ := rowsB7_chunk000 ++ rowsB7_chunk004 ++ rowsB7_chunk008

private theorem rowsB7_checked :
    rowsB7.length = 11 ∧ rowsSum 1838 rowsB7 = 260432726 := by
  constructor
  · simp only [rowsB7, List.length_append, Nat.reduceAdd, rowsB7_chunk000_checked.1,
      rowsB7_chunk004_checked.1, rowsB7_chunk008_checked.1]
  · simp only [rowsB7, rowsSum_append, List.length_append, Nat.reduceAdd,
      rowsB7_chunk000_checked.1, rowsB7_chunk004_checked.1, rowsB7_chunk000_checked.2,
      rowsB7_chunk004_checked.2, rowsB7_chunk008_checked.2]

private def rowsB8_chunk000 : List ℕ := [
  4828658737914257051908182637939712904655474816186644321637029936411169451397895025531836375349337276035637551360,
  622892266299877384751209141878264308788534161842442223863560085970527523921276357233239304669778287177054835286272,
  1238550966257080141401074218024525253534532376945304657436764797900009075571227116623186417565711894942809060389120,
  1238555672516240153027946413731489717664046136209266450738956383752184385432438491191271953234508229094512163664128]

private theorem rowsB8_chunk000_checked :
    rowsB8_chunk000.length = 4 ∧ rowsSum 1849 rowsB8_chunk000 = 100580370 := by
  constructor
  · rfl
  · rw [bRows_eq 1849 rowsB8_chunk000 (by decide) (by decide)]
    decide +kernel

private def rowsB8_chunk004 : List ℕ := [
  1855414473146243106476990130197575024633365089455928911676196715218275493879236957962952489292650655738699074089216,
  2472273273776246059926165744744099294380107889344717132214623778119517904161027892944471631609605931647135546192128,
  2472273273812082112504180911051267438425772321023090434317505898684600408226827346860520466585698470178233265533184,
  318305183998718557254927220640106582134025105802452877786881433733593206035776695535906514413258292153749855391559936]

private theorem rowsB8_chunk004_checked :
    rowsB8_chunk004.length = 4 ∧ rowsSum 1853 rowsB8_chunk004 = 103896094 := by
  constructor
  · rfl
  · rw [bRows_eq 1853 rowsB8_chunk004 (by decide) (by decide)]
    decide +kernel

private def rowsB8_chunk008 : List ℕ := [
  634136889916693072188923949301788159960460066396342713290665891380403462359007932363355335582918568822719651704320256,
  634140504328314958350241814235649235669470664446291164543810922205318054712730671449744451333277285930153026324115712,
  949972210250876470516218946661158397435174940012581187930215331780631193214647235237544209308023329003852156022927616]

private theorem rowsB8_chunk008_checked :
    rowsB8_chunk008.length = 3 ∧ rowsSum 1857 rowsB8_chunk008 = 80211996 := by
  constructor
  · rfl
  · rw [bRows_eq 1857 rowsB8_chunk008 (by decide) (by decide)]
    decide +kernel

private def rowsB8 : List ℕ := rowsB8_chunk000 ++ rowsB8_chunk004 ++ rowsB8_chunk008

private theorem rowsB8_checked :
    rowsB8.length = 11 ∧ rowsSum 1849 rowsB8 = 284688460 := by
  constructor
  · simp only [rowsB8, List.length_append, Nat.reduceAdd, rowsB8_chunk000_checked.1,
      rowsB8_chunk004_checked.1, rowsB8_chunk008_checked.1]
  · simp only [rowsB8, rowsSum_append, List.length_append, Nat.reduceAdd,
      rowsB8_chunk000_checked.1, rowsB8_chunk004_checked.1, rowsB8_chunk000_checked.2,
      rowsB8_chunk004_checked.2, rowsB8_chunk008_checked.2]

private def rowsB9_chunk000 : List ℕ := [
  950587866597695134253977556257595685018062141155854423885979957077841411188021688404296320022330583065980744371384576,
  1265803916173438052674220054365360418642686507108378862995309162979897596450316423447405538883203452374106409170743552,
  162972254207343901314522603468544327672504287430081089360618270942393796415603058519301013300530501064941289092562399488,
  163287470256915057148220969288535718963061492085019597000226879631130979259422772432279280096006714859675262660588450048]

private theorem rowsB9_chunk000_checked :
    rowsB9_chunk000.length = 4 ∧ rowsSum 1860 rowsB9_chunk000 = 109742129 := by
  constructor
  · rfl
  · rw [bRows_eq 1860 rowsB9_chunk000 (by decide) (by decide)]
    decide +kernel

private def rowsB9_chunk004 : List ℕ := [
  324678704498496016587443199809821146119887555959215295867379149599344819876394483689142502176295233384451705052116156672,
  486385771648448752904303967191322857106693009810942777241014939597172706255615282641903912681420489317776635564816204032]

private theorem rowsB9_chunk004_checked :
    rowsB9_chunk004.length = 2 ∧ rowsSum 1864 rowsB9_chunk004 = 56116171 := by
  constructor
  · rfl
  · rw [bRows_eq 1864 rowsB9_chunk004 (by decide) (by decide)]
    decide +kernel

private def rowsB9 : List ℕ := rowsB9_chunk000 ++ rowsB9_chunk004

private theorem rowsB9_checked :
    rowsB9.length = 6 ∧ rowsSum 1860 rowsB9 = 165858300 := by
  constructor
  · simp only [rowsB9, List.length_append, Nat.reduceAdd, rowsB9_chunk000_checked.1,
      rowsB9_chunk004_checked.1]
  · simp only [rowsB9, rowsSum_append, Nat.reduceAdd, rowsB9_chunk000_checked.1,
      rowsB9_chunk000_checked.2, rowsB9_chunk004_checked.2]

def rowsB : List ℕ := rowsB1 ++ rowsB2 ++ rowsB3 ++ rowsB4 ++ rowsB5 ++ rowsB6 ++ rowsB7 ++ rowsB8 ++ rowsB9

theorem rowsB_length : rowsB.length = 108 := by
  simp only [rowsB, List.length_append, Nat.reduceAdd,
    rowsB1_checked.1, rowsB2_checked.1, rowsB3_checked.1, rowsB4_checked.1,
    rowsB5_checked.1, rowsB6_checked.1, rowsB7_checked.1, rowsB8_checked.1,
    rowsB9_checked.1]

theorem rowsB_sum : rowsSum 1758 rowsB = 2005983713 := by
  simp only [rowsB, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsB1_checked.1, rowsB2_checked.1, rowsB3_checked.1, rowsB4_checked.1,
    rowsB5_checked.1, rowsB6_checked.1, rowsB7_checked.1, rowsB8_checked.1,
    rowsB1_checked.2, rowsB2_checked.2, rowsB3_checked.2, rowsB4_checked.2,
    rowsB5_checked.2, rowsB6_checked.2, rowsB7_checked.2, rowsB8_checked.2,
    rowsB9_checked.2]

end K1_13_2_3_4
end PackSource_K1_13_2_3_4DataB

section PackSource_K1_13_2_3_4DataD
set_option autoImplicit true
namespace K1_13_2_3_4

-- Keep the kernel reductions sequential to bound peak memory.
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

open K1_13_2

-- Each row has grade 1943–2007 and 71 base-512 digits. In this range the
-- original counting formula reduces to three denominator evaluations per flag.
private theorem ddDenNeg {v : ℤ} (hv : v < 0) : denominator v = 0 := by
  simp [denominator, hv]

private theorem ddCumNeg {d v : ℤ} (hv : v < 0) : cumulative d v = 0 := by
  simp [cumulative, hv]

-- Below the degree, the shifted terms in inclusion-exclusion all vanish.
private theorem ddCum {d v : ℤ} (hd : 0 ≤ d) (hv : v ≤ d) :
    cumulative d v = denominator v := by
  by_cases h : v < 0
  · rw [ddCumNeg h, ddDenNeg h]
  simp only [cumulative, show ¬ d < 0 by omega, h, decide_false, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte, min_eq_left (show v ≤ 3 * d by omega)]
  simp only [ddDenNeg (show v - d - 1 < 0 by omega),
    ddDenNeg (show v - d - 2 < 0 by omega), ddDenNeg (show v - d - 3 < 0 by omega),
    ddDenNeg (show v - 2 * d - 3 < 0 by omega),
    ddDenNeg (show v - 2 * d - 4 < 0 by omega),
    ddDenNeg (show v - 2 * d - 5 < 0 by omega),
    ddDenNeg (show v - 3 * d - 6 < 0 by omega), sub_zero, add_zero]

private theorem ddCumBelow {d v : ℤ} (hv : v ≤ d) : cumulative d v = denominator v := by
  by_cases hd : 0 ≤ d
  · exact ddCum hd hv
  · rw [ddCumNeg (by omega), ddDenNeg (by omega)]

private theorem ddCap {d v c : ℤ} (hd : 0 ≤ d) (hc : 0 ≤ c) (hv : v ≤ d)
    (hcap : v < 3 * (c + 1)) : cappedCount d v c = denominator v := by
  simp [cappedCount, show ¬ c < 0 by omega, ddCum hd hv,
    ddCumNeg (show v - 3 * (c + 1) < 0 by omega)]

-- In this block the window and its cubic residual have the same explicit flag shape.
private def ddFlag (s q k : ℤ) : Flag :=
  ⟨1650 - 3 * k, s - 1350 - q - 2 * k, 1650 - 3 * k, 550 - k, 1650 - q - 3 * k⟩

private def ddOld (s q k : ℤ) : ℤ :=
  denominator (1650 - 3 * k) - denominator (s - 1350 - q - 2 * k - 1)

private def ddTarget (q k : ℤ) : ℤ := denominator (1650 - q - 3 * k - 1)

private theorem ddOldEq {s q k : ℤ} (hs : s ≤ 2007) (hq : 0 ≤ q)
    (hk : 0 ≤ k) (hk' : k < 512) : oldCount (ddFlag s q k) = ddOld s q k := by
  dsimp only [oldCount, ddFlag, ddOld]
  rw [min_eq_right (by omega), ddCap (by omega) (by omega) (by omega) (by omega),
    ddCap (by omega) (by omega) (by omega) (by omega)]

-- Of the four cumulative counts in the target, one vanishes and two cancel.
private theorem ddTargetEq {s q k : ℤ} (hs : 1943 ≤ s) (hs' : s ≤ 2007)
    (hq : 0 ≤ q) (hq' : q ≤ 70) (hk : 0 ≤ k) (hk' : k < 512) :
    targetCount (ddFlag s q k) = ddTarget q k := by
  dsimp only [targetCount, ddFlag, ddTarget]
  rw [ite_eq_right (by omega)]
  let removed := min (1650 - 3 * k)
    ((1650 - q - 3 * k - 1 - (s - 1350 - q - 2 * k) + (1650 - 3 * k)) / 4) + 1
  have hv : 1650 - q - 3 * k - 1 - 3 * removed < 0 := by
    dsimp [removed]
    omega
  rw [ddCumNeg hv, ddCumBelow (by omega), ddCumBelow (by omega), ddCumBelow (by omega)]
  omega

private theorem ddKernelEq {s q k : ℤ} (hs : 1943 ≤ s) (hs' : s ≤ 2007)
    (hq : 0 ≤ q) (hq' : q ≤ 70) (hk : 0 ≤ k) (hk' : k < 512) :
    kernelLower (ddFlag s q k) = ddOld s q k - ddTarget q k := by
  simp only [kernelLower, ddFlag, show ¬ (1650 : ℤ) - 3 * k < 0 by omega,
    show ¬ (550 : ℤ) - k < 0 by omega, decide_false, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte]
  rw [← ddOldEq hs' hq hk hk', ← ddTargetEq hs hs' hq hq' hk hk']
  rfl

private theorem ddWindow {s q : ℕ} (hs : 1943 ≤ s) (hs' : s ≤ 2007) :
    windowFlag s (3000 + q - s) = ddFlag s q 0 := by
  simp only [windowFlag, ddFlag, mul_zero, sub_zero]
  congr 1 <;> omega

private theorem ddCubic (s q : ℤ) (k : ℕ) : cubicFlag (ddFlag s q 0) k = ddFlag s q k := by
  simp [ddFlag, cubicFlag]

private def ddSaving (s q k : ℕ) : ℕ :=
  let old := ddOld s q 0
  let lower := max 0 (old - ddTarget q 0)
  (old - lower).toNat -
    (old - max lower (ddOld s q k - ddTarget q k)).toNat

private theorem ddSavingEq {s q k : ℕ} (hs : 1943 ≤ s) (hs' : s ≤ 2007)
    (hq' : q ≤ 70) (hk' : k < 512) :
    entry s q k = ddSaving s q k := by
  have hj : 993 ≤ 3000 + q - s ∧ 3000 + q - s ≤ 1581 := by omega
  by_cases hk : k = 0
  · subst k
    simp [entry, cubicSavings, ddSaving]
  simp only [entry, hj, and_self, ↓reduceIte, cubicSavings, hk, ddWindow hs hs', ddCubic, ddSaving]
  rw [ddKernelEq (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    ddKernelEq (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    ddOldEq (by omega) (by omega) (by omega) (by omega)]

-- On nonnegative inputs the six residues share one rounded cubic.
private def ddDenNat (u : ℕ) : ℕ := (((2 * u + 21) * u + 66) * u + 72) / 72

-- The product of consecutive integers is even.
private theorem ddEvenPair (x : ℤ) : 2 * (x * (x - 1) / 2) = x * (x - 1) := by
  have hm : x * (x - 1) % 2 = 0 := by
    rw [Int.mul_emod, Int.sub_emod]
    rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega) with h | h <;> norm_num [h]
  omega

private theorem ddDenPoly (x r : ℤ) :
    1 + r * (r + 1) / 2 + x * (22 + 7 * r + r * (r - 1) / 2) + (57 + 6 * r) * (x * (x - 1) / 2) +
      6 * x * (x - 1) * (x - 2) =
    (((12 * x + 21 + 6 * r) * x + 11 + 7 * r + r * r) * x + 2 + r + r * r) / 2 := by
  have hp : 2 * (r * (r + 1) / 2) = r * (r + 1) := by
    simpa only [add_sub_cancel_right, mul_comm (r + 1) r] using ddEvenPair (r + 1)
  have he : 2 * (1 + r * (r + 1) / 2 + x * (22 + 7 * r + r * (r - 1) / 2) + (57 + 6 * r) * (x * (x - 1) / 2) +
      6 * x * (x - 1) * (x - 2)) = (((12 * x + 21 + 6 * r) * x + 11 + 7 * r + r * r) * x + 2 + r + r * r) := by
    linear_combination hp + x * ddEvenPair r + (57 + 6 * r) * ddEvenPair x
  omega

private theorem ddRoundCubic (x r : ℤ) (hr : 0 ≤ r) (hr' : r < 6) :
    (((12 * x + 21 + 6 * r) * x + 11 + 7 * r + r * r) * x + 2 + r + r * r) / 2 =
      (((2 * (6 * x + r) + 21) * (6 * x + r) + 66) * (6 * x + r) + 72) / 72 := by
  have hc : 0 ≤ 2 * r ^ 3 - 15 * r ^ 2 + 30 * r ∧ 2 * r ^ 3 - 15 * r ^ 2 + 30 * r < 36 := by
    interval_cases r <;> decide
  have he : ((2 * (6 * x + r) + 21) * (6 * x + r) + 66) * (6 * x + r) + 72 =
      36 * (((12 * x + 21 + 6 * r) * x + 11 + 7 * r + r * r) * x + 2 + r + r * r) + (2 * r ^ 3 - 15 * r ^ 2 + 30 * r) := by ring
  rw [he]
  omega

private theorem ddDenCorrect (i : ℕ) : denominator (i : ℤ) = ddDenNat i := by
  simp only [denominator, ddDenNat, show ¬ (i : ℤ) < 0 by omega, ↓reduceIte,
    Int.natCast_ediv, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_add]
  rw [ddDenPoly, ddRoundCubic _ _ (by omega) (by omega),
    show 6 * ((i : ℤ) / 6) + (i : ℤ) % 6 = i by omega]

-- Shifting the cubic's argument by one lets index zero represent every negative input.
private def ddBefore (u : ℕ) : ℕ := (((2 * u + 15) * u + 30) * u + 25) / 72

private theorem ddBeforeSucc (u : ℕ) : ddBefore (u + 1) = ddDenNat u := by
  unfold ddBefore ddDenNat
  congr 1
  ring

private theorem ddBeforeEq (a b : ℕ) :
    denominator ((a : ℤ) - b - 1) = (ddBefore (a - b) : ℤ) := by
  by_cases h : a ≤ b
  · simp only [Nat.sub_eq_zero_of_le h, ddDenNeg (show (a : ℤ) - b - 1 < 0 by omega),
      show ddBefore 0 = 0 from rfl, Nat.cast_zero]
  · have he : (a : ℤ) - b - 1 = ((a - b - 1 : ℕ) : ℤ) := by omega
    rw [he, ddDenCorrect, ← ddBeforeSucc, show a - b - 1 + 1 = a - b by omega]

private def ddNatSaving (s q k : ℕ) : ℕ :=
  let old := ddDenNat 1650 - ddBefore (s - (1350 + q))
  let lower := old - ddDenNat (1649 - q)
  let other := ddDenNat (1650 - 3 * k) - ddBefore (s - (1350 + q + 2 * k)) - ddDenNat (1649 - q - 3 * k)
  (old - lower) - (old - max lower other)

private theorem ddNatSavingEq {s q k : ℕ} (hq : q ≤ 70) (hk : k < 512) :
    ddSaving s q k = ddNatSaving s q k := by
  have h₁ : ∀ c : ℕ, c < 512 → ddOld s q c =
      (ddDenNat (1650 - 3 * c) : ℤ) - ddBefore (s - (1350 + q + 2 * c)) := by
    intro c hc
    unfold ddOld
    rw [show (1650 : ℤ) - 3 * c = ((1650 - 3 * c : ℕ) : ℤ) by omega, ddDenCorrect,
      show (s : ℤ) - 1350 - q - 2 * c = (s : ℤ) - ((1350 + q + 2 * c : ℕ) : ℤ) by omega,
      ddBeforeEq]
  have h₂ : ∀ c : ℕ, c < 512 → ddTarget q c = ddDenNat (1649 - q - 3 * c) := by
    intro c hc
    unfold ddTarget
    rw [show (1650 : ℤ) - q - 3 * c - 1 = ((1649 - q - 3 * c : ℕ) : ℤ) by omega, ddDenCorrect]
  have hb := h₁ 0 (by omega)
  have ht := h₂ 0 (by omega)
  simp only [Nat.cast_zero, Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at hb ht
  simp only [ddSaving, ddNatSaving, hb, ht, h₁ k hk, h₂ k hk]
  omega

-- The loop index is also the digit position, so every digit is read from the original code.
private def ddPrefix (s code : ℕ) : ℕ → ℕ
  | 0 => 0
  | q + 1 => ddNatSaving s q ((code >>> (9 * q)) % 512) + ddPrefix s code q

private theorem ddPrefixEq {s : ℕ} (hs : 1943 ≤ s) (hs' : s ≤ 2007)
    (code q n : ℕ) (hq : q + n ≤ 71) :
    rowSum s q (code / 512 ^ q) n + ddPrefix s code q = ddPrefix s code (q + n) := by
  induction n generalizing q with
  | zero => simp [rowSum]
  | succ n ih =>
    have hk := Nat.mod_lt (code / 512 ^ q) (by decide : 0 < 512)
    rw [rowSum, ddSavingEq hs hs' (by omega) hk, ddNatSavingEq (by omega) hk,
      Nat.div_div_eq_div_mul, ← pow_succ]
    have hi := ih (q + 1) (by omega)
    have hd : code >>> (9 * q) = code / 512 ^ q := by
      simp only [Nat.shiftRight_eq_div_pow, pow_mul, show (2 : ℕ) ^ 9 = 512 from rfl]
    rw [ddPrefix, hd] at hi
    rw [show q + (n + 1) = q + 1 + n by omega]
    omega

private theorem ddSingle {s code total : ℕ}
    (h : 1943 ≤ s ∧ s ≤ 2007 ∧ ddPrefix s code 71 = total) :
    [code].length = 1 ∧ rowsSum s [code] = total := by
  have he := ddPrefixEq h.1 h.2.1 code 0 71 (by decide)
  simp only [pow_zero, Nat.div_one, Nat.zero_add, show ddPrefix s code 0 = 0 from rfl,
    Nat.add_zero] at he
  exact ⟨rfl, (Nat.add_zero _).trans (he.trans h.2.2)⟩

/-- The certificate encodes a row per grade. The base-512 digit of index
`q` is the cubic exponent on the diagonal `s + j = 3000 + q`. -/
private def rowsD1_row1943 : List ℕ := [
  13864093624284037068282596270006879532491706471140757910254512911202485400233707987156570188148018810688872097509204115825535162545345774354316592558081445136]

private theorem rowsD1_row1943_checked :
    rowsD1_row1943.length = 1 ∧ rowsSum 1943 rowsD1_row1943 = 48532032 := ddSingle (by decide +kernel)

private def rowsD1_row1944 : List ℕ := [
  27620556934655258249284261306657683242909305166466150149715382457616063125920147933412859734562508328036660817286330949496276427298330581538437635519228808464]

private theorem rowsD1_row1944_checked :
    rowsD1_row1944.length = 1 ∧ rowsSum 1944 rowsD1_row1944 = 48859683 := ddSingle (by decide +kernel)

private def rowsD1_row1945 : List ℕ := [
  27620609411399793867292562184067883996491407402618833004846356914175796182317166414696647246991462294508982359165799216790900125522881244407044596119992667408]

private theorem rowsD1_row1945_checked :
    rowsD1_row1945.length = 1 ∧ rowsSum 1945 rowsD1_row1945 = 49189053 := ddSingle (by decide +kernel)

private def rowsD1_row1946 : List ℕ := [
  41377125198313808432849696367056994786409231503426265681163480684846457311728099638291142721842253554416380087758987681091492957186408887579561308432631991568]

private theorem rowsD1_row1946_checked :
    rowsD1_row1946.length = 1 ∧ rowsSum 1946 rowsD1_row1946 = 49521319 := ddSingle (by decide +kernel)

private def rowsD1_row1947 : List ℕ := [
  55133536339221617957744643837471583910017820628947315985147505106567550230052305662576064101688348140059138261664945789385470058548144968536910620641363890448]

private theorem rowsD1_row1947_checked :
    rowsD1_row1947.length = 1 ∧ rowsSum 1947 rowsD1_row1947 = 49852962 := ddSingle (by decide +kernel)

private def rowsD1_row1948 : List ℕ := [
  7084686340313165758768579846478369201028985078867898863551194462596509942057389425721727204262326333839011870935128154773544554869614804802370500308350676373776]

private theorem rowsD1_row1948_checked :
    rowsD1_row1948.length = 1 ∧ rowsSum 1948 rowsD1_row1948 = 50188791 := ddSingle (by decide +kernel)

private def rowsD1_row1949 : List ℕ := [
  7098442751249286864154888438293518732328008671955709234837066057658559968447718636518117512365556791048700185070737370818595377906211989731891373592692297699600]

private theorem rowsD1_row1949_checked :
    rowsD1_row1949.length = 1 ∧ rowsSum 1949 rowsD1_row1949 = 50412605 := ddSingle (by decide +kernel)

private def rowsD1_row1950 : List ℕ := [
  14141725202918541117600692603231002658501977731271213254467834682646706154190920579547314922226654467612668217459592558282095785964849767496708411932202984673560]

private theorem rowsD1_row1950_checked :
    rowsD1_row1950.length = 1 ∧ rowsSum 1950 rowsD1_row1950 = 50748619 := ddSingle (by decide +kernel)

private def rowsD1 : List ℕ :=
    rowsD1_row1943 ++ rowsD1_row1944 ++ rowsD1_row1945 ++
    rowsD1_row1946 ++ rowsD1_row1947 ++ rowsD1_row1948 ++
    rowsD1_row1949 ++ rowsD1_row1950

private theorem rowsD1_checked :
    rowsD1.length = 8 ∧ rowsSum 1943 rowsD1 = 397305064 := by
  constructor <;> simp only [rowsD1, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD1_row1943_checked.1, rowsD1_row1943_checked.2,
    rowsD1_row1944_checked.1, rowsD1_row1944_checked.2,
    rowsD1_row1945_checked.1, rowsD1_row1945_checked.2,
    rowsD1_row1946_checked.1, rowsD1_row1946_checked.2,
    rowsD1_row1947_checked.1, rowsD1_row1947_checked.2,
    rowsD1_row1948_checked.1, rowsD1_row1948_checked.2,
    rowsD1_row1949_checked.1, rowsD1_row1949_checked.2,
    rowsD1_row1950_checked.1, rowsD1_row1950_checked.2]

private def rowsD2_row1951 : List ℕ := [
  21171304822610438811243843732524961606573655579502707760177018110525706994669731512421611706633865873731227601463484487172054983992388501147617538497437742797080]

private theorem rowsD2_row1951_checked :
    rowsD2_row1951.length = 1 ∧ rowsSum 1951 rowsD2_row1951 = 51076092 := ddSingle (by decide +kernel)

private def rowsD2_row1952 : List ℕ := [
  21185088206387462826792338813793163807150561874193563566072621148777932407631587273782775701449095587428263047259074113219607687774321168937003825546165800538392]

private theorem rowsD2_row1952_checked :
    rowsD2_row1952.length = 1 ∧ rowsSum 1952 rowsD2_row1952 = 51364774 := ddSingle (by decide +kernel)

private def rowsD2_row1953 : List ℕ := [
  28228370605681468784583826434284479884628777886166814002970290447683979575181400452410412172535136762748541672908948639143727059825419259860041756738098154576152]

private theorem rowsD2_row1953_checked :
    rowsD2_row1953.length = 1 ∧ rowsSum 1953 rowsD2_row1953 = 51696017 := ddSingle (by decide +kernel)

private def rowsD2_row1954 : List ℕ := [
  3634388959044314612837654347815184399242806247446577053333792309049460519650347237140464823146113150554437541423361648193376770887088935471404938351957583896123672]

private theorem rowsD2_row1954_checked :
    rowsD2_row1954.length = 1 ∧ rowsSum 1954 rowsD2_row1954 = 52031837 := ddSingle (by decide +kernel)

private def rowsD2_row1955 : List ℕ := [
  7240563303893883878385566106554814333376515317867593411297581015131165279257174006289627702919757342971642015404431175760335308646197820731366006635508979320101144]

private theorem rowsD2_row1955_checked :
    rowsD2_row1955.length = 1 ∧ rowsSum 1955 rowsD2_row1955 = 52377791 := ddSingle (by decide +kernel)

private def rowsD2_row1956 : List ℕ := [
  7240577033541987563547541415365581588011388377441073533853613950906885977779050892735975731339940945317649664363426803301604113778017265694283164934750853210708248]

private theorem rowsD2_row1956_checked :
    rowsD2_row1956.length = 1 ∧ rowsSum 1956 rowsD2_row1956 = 52601764 := ddSingle (by decide +kernel)

private def rowsD2_row1957 : List ℕ := [
  10846765107986774997820950804445788841288461583234174990722919480648322695190173452325899402560266691168453095218930416619695035693943122321554732454529862378330392]

private theorem rowsD2_row1957_checked :
    rowsD2_row1957.length = 1 ∧ rowsSum 1957 rowsD2_row1957 = 52957221 := ddSingle (by decide +kernel)

private def rowsD2 : List ℕ :=
    rowsD2_row1951 ++ rowsD2_row1952 ++ rowsD2_row1953 ++
    rowsD2_row1954 ++ rowsD2_row1955 ++ rowsD2_row1956 ++
    rowsD2_row1957

private theorem rowsD2_checked :
    rowsD2.length = 7 ∧ rowsSum 1951 rowsD2 = 364105496 := by
  constructor <;> simp only [rowsD2, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD2_row1951_checked.1, rowsD2_row1951_checked.2,
    rowsD2_row1952_checked.1, rowsD2_row1952_checked.2,
    rowsD2_row1953_checked.1, rowsD2_row1953_checked.2,
    rowsD2_row1954_checked.1, rowsD2_row1954_checked.2,
    rowsD2_row1955_checked.1, rowsD2_row1955_checked.2,
    rowsD2_row1956_checked.1, rowsD2_row1956_checked.2,
    rowsD2_row1957_checked.1, rowsD2_row1957_checked.2]

private def rowsD3_row1958 : List ℕ := [
  14452925750108911817915011914130150870846229585320678242373611079434119753778953632523597616968152015712205054848146862235451684946873903867982715038745246443903256]

private theorem rowsD3_row1958_checked :
    rowsD3_row1958.length = 1 ∧ rowsSum 1958 rowsD3_row1958 = 53310127 := ddSingle (by decide +kernel)

private def rowsD3_row1959 : List ℕ := [
  1857208015995054524666629833129583448843912939210648245069593533000169616621658114486926644493375506681245786674439298139796608499662897120633717331254440837485041944]

private theorem rowsD3_row1959_checked :
    rowsD3_row1959.length = 1 ∧ rowsSum 1959 rowsD3_row1959 = 53653364 := ddSingle (by decide +kernel)

private def rowsD3_row1960 : List ℕ := [
  1864413307619127612823267505574164960054489262995798974926031767752553615776720820327994386785230082785110340727433125579580057728830005937032153361580608996578566424]

private theorem rowsD3_row1960_checked :
    rowsD3_row1960.length = 1 ∧ rowsSum 1960 rowsD3_row1960 = 53987134 := ddSingle (by decide +kernel)

private def rowsD3_row1961 : List ℕ := [
  3707168411593878042732315961781387949819663673741710871647550850297526977692453621507126379104450461681730419437233611972420363313353573886364138525932174859847737624]

private theorem rowsD3_row1961_checked :
    rowsD3_row1961.length = 1 ∧ rowsSum 1961 rowsD3_row1961 = 54330098 := ddSingle (by decide +kernel)

private def rowsD3_row1962 : List ℕ := [
  5549930545147986191995924839237182966566139937962246193918638341429808840032200812135889764701081263277429574324082851509617331665558816272681602815201794918715105560]

private theorem rowsD3_row1962_checked :
    rowsD3_row1962.length = 1 ∧ rowsSum 1962 rowsD3_row1962 = 54579573 := ddSingle (by decide +kernel)

private def rowsD3_row1963 : List ℕ := [
  5557142893810869612372899296809143918548772649643239060771021802883331649631522259537887029075312416769665773863424797749069077541607691033836547033810555472285671704]

private theorem rowsD3_row1963_checked :
    rowsD3_row1963.length = 1 ∧ rowsSum 1963 rowsD3_row1963 = 54934116 := ddSingle (by decide +kernel)

private def rowsD3_row1964 : List ℕ := [
  950890504189441101013454587843856293413015752677656770323542315147577035350764898793363807222195053740650965677527151218257105648256850184093901552493336432264534434072]

private theorem rowsD3_row1964_checked :
    rowsD3_row1964.length = 1 ∧ rowsSum 1964 rowsD3_row1964 = 55210710 := ddSingle (by decide +kernel)

private def rowsD3 : List ℕ :=
    rowsD3_row1958 ++ rowsD3_row1959 ++ rowsD3_row1960 ++
    rowsD3_row1961 ++ rowsD3_row1962 ++ rowsD3_row1963 ++
    rowsD3_row1964

private theorem rowsD3_checked :
    rowsD3.length = 7 ∧ rowsSum 1958 rowsD3 = 380005122 := by
  constructor <;> simp only [rowsD3, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD3_row1958_checked.1, rowsD3_row1958_checked.2,
    rowsD3_row1959_checked.1, rowsD3_row1959_checked.2,
    rowsD3_row1960_checked.1, rowsD3_row1960_checked.2,
    rowsD3_row1961_checked.1, rowsD3_row1961_checked.2,
    rowsD3_row1962_checked.1, rowsD3_row1962_checked.2,
    rowsD3_row1963_checked.1, rowsD3_row1963_checked.2,
    rowsD3_row1964_checked.1, rowsD3_row1964_checked.2]

private def rowsD4_row1965 : List ℕ := [
  952733259279712809867714061353663693476505375515162090674338176953396485504725853443609074217103765586588962206695205224734173551960536385690537860364144987667051979040]

private theorem rowsD4_row1965_checked :
    rowsD4_row1965.length = 1 ∧ rowsSum 1965 rowsD4_row1965 = 55576301 := ddSingle (by decide +kernel)

private def rowsD4_row1966 : List ℕ := [
  1898070226735958295415505841436705248586471873934115888334565764157399487028809361622163433475531601791399095307321745465843650383828231938456260615571226584670047183136]

private theorem rowsD4_row1966_checked :
    rowsD4_row1966.length = 1 ∧ rowsSum 1966 rowsD4_row1966 = 55938580 := ddSingle (by decide +kernel)

private def rowsD4_row1967 : List ℕ := [
  2841564432086216125918995342036662242536887699920022887552573350607940724047652891695340435961346473236734614407487625730567363014597636716210390418829547288376216002848]

private theorem rowsD4_row1967_checked :
    rowsD4_row1967.length = 1 ∧ rowsSum 1967 rowsD4_row1967 = 56277297 := ddSingle (by decide +kernel)

private def rowsD4_row1968 : List ℕ := [
  2843414392481814740349036547110600665930457726067817610852982291159820495378582067337745301059515992650577904558312391754429813063911933976480531803044410023760265093408]

private theorem rowsD4_row1968_checked :
    rowsD4_row1968.length = 1 ∧ rowsSum 1968 rowsD4_row1968 = 56624711 := ddSingle (by decide +kernel)

private def rowsD4_row1969 : List ℕ := [
  3788747767836550579595512883217734269864932650861337358292160589334015652749755110876741817017399495088437317454114712726998541484252150729875098784271861362972210372896]

private theorem rowsD4_row1969_checked :
    rowsD4_row1969.length = 1 ∧ rowsSum 1969 rowsD4_row1969 = 56945987 := ddSingle (by decide +kernel)

private def rowsD4_row1970 : List ℕ := [
  487799428751212958652269399621168590836467943841540283660154953302583197503141158557258936492184444767405047317491245673873952149026108763060158149465022154699995054481696]

private theorem rowsD4_row1970_checked :
    rowsD4_row1970.length = 1 ∧ rowsSum 1970 rowsD4_row1970 = 57303937 := ddSingle (by decide +kernel)

private def rowsD4_row1971 : List ℕ := [
  971811952489679611618181884567162281127488112358426685408430822829541382865612211996194484493202126488238406619946730840880451177479141320117804065581118163024215152931104]

private theorem rowsD4_row1971_checked :
    rowsD4_row1971.length = 1 ∧ rowsSum 1971 rowsD4_row1971 = 57581502 := ddSingle (by decide +kernel)

private def rowsD4 : List ℕ :=
    rowsD4_row1965 ++ rowsD4_row1966 ++ rowsD4_row1967 ++
    rowsD4_row1968 ++ rowsD4_row1969 ++ rowsD4_row1970 ++
    rowsD4_row1971

private theorem rowsD4_checked :
    rowsD4.length = 7 ∧ rowsSum 1965 rowsD4 = 396248315 := by
  constructor <;> simp only [rowsD4, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD4_row1965_checked.1, rowsD4_row1965_checked.2,
    rowsD4_row1966_checked.1, rowsD4_row1966_checked.2,
    rowsD4_row1967_checked.1, rowsD4_row1967_checked.2,
    rowsD4_row1968_checked.1, rowsD4_row1968_checked.2,
    rowsD4_row1969_checked.1, rowsD4_row1969_checked.2,
    rowsD4_row1970_checked.1, rowsD4_row1970_checked.2,
    rowsD4_row1971_checked.1, rowsD4_row1971_checked.2]

private def rowsD5_row1972 : List ℕ := [
  971811956095895118437993979833361629135785260743830956484522314839614825056059174962598819697246883637962016220893470567047833586992145667947185583678861218391512795197728]

private theorem rowsD5_row1972_checked :
    rowsD5_row1972.length = 1 ∧ rowsSum 1972 rowsD5_row1972 = 57898819 := ddSingle (by decide +kernel)

private def rowsD5_row1973 : List ℕ := [
  1455828168943659594254732767200141716735634142824451436806247481837439500433866003382770119623845065284719568678270292565797769554051014700079156142161148905228799015268640]

private theorem rowsD5_row1973_checked :
    rowsD5_row1973.length = 1 ∧ rowsSum 1973 rowsD5_row1973 = 58241930 := ddSingle (by decide +kernel)

private def rowsD5_row1974 : List ℕ := [
  1939838857132313896752800299629234641421415373639074053176337235593556446054132680580624180279227472807477611871462286484783263768350057130658623980797362585281403624239392]

private theorem rowsD5_row1974_checked :
    rowsD5_row1974.length = 1 ∧ rowsSum 1974 rowsD5_row1974 = 58621160 := ddSingle (by decide +kernel)

private def rowsD5_row1975 : List ℕ := [
  249270240330243877536875013220088005646868503961519020798214720700560247806769070670748620131500420985758737258350749679070516880318246699480312330650522218712188624573706528]

private theorem rowsD5_row1975_checked :
    rowsD5_row1975.length = 1 ∧ rowsSum 1975 rowsD5_row1975 = 58973106 := ddSingle (by decide +kernel)

private def rowsD5_row1976 : List ℕ := [
  497567719674708931595705151154038944982244519403188591751694743251359672462981656965416399003828888010073543727060781473263505864254015573531706108795607610411210825262051616]

private theorem rowsD5_row1976_checked :
    rowsD5_row1976.length = 1 ∧ rowsSum 1976 rowsD5_row1976 = 59337501 := ddSingle (by decide +kernel)

private def rowsD5_row1977 : List ℕ := [
  497567721517499169604618258274976226551125120307160503456563218747901288270157957762732161641661651274660541205674531545493051377878463209919048811086105061471142828241465728]

private theorem rowsD5_row1977_checked :
    rowsD5_row1977.length = 1 ∧ rowsSum 1977 rowsD5_row1977 = 59662769 := ddSingle (by decide +kernel)

private def rowsD5_row1978 : List ℕ := [
  744899068327564130357802353342055359655768058579200937500684518456242632594788065406492365477232830730632814839387712783550574994119703862826700554645563515944308715995410816]

private theorem rowsD5_row1978_checked :
    rowsD5_row1978.length = 1 ∧ rowsSum 1978 rowsD5_row1978 = 59950487 := ddSingle (by decide +kernel)

private def rowsD5 : List ℕ :=
    rowsD5_row1972 ++ rowsD5_row1973 ++ rowsD5_row1974 ++
    rowsD5_row1975 ++ rowsD5_row1976 ++ rowsD5_row1977 ++
    rowsD5_row1978

private theorem rowsD5_checked :
    rowsD5.length = 7 ∧ rowsSum 1972 rowsD5 = 412685772 := by
  constructor <;> simp only [rowsD5, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD5_row1972_checked.1, rowsD5_row1972_checked.2,
    rowsD5_row1973_checked.1, rowsD5_row1973_checked.2,
    rowsD5_row1974_checked.1, rowsD5_row1974_checked.2,
    rowsD5_row1975_checked.1, rowsD5_row1975_checked.2,
    rowsD5_row1976_checked.1, rowsD5_row1976_checked.2,
    rowsD5_row1977_checked.1, rowsD5_row1977_checked.2,
    rowsD5_row1978_checked.1, rowsD5_row1978_checked.2]

private def rowsD6_row1979 : List ℕ := [
  993197494851744715137433753410168134919198963945718388217264354248601759870055250768809124027316541557819740881819180001306010955511005444498020439609635993080134185171169664]

private theorem rowsD6_row1979_checked :
    rowsD6_row1979.length = 1 ∧ rowsSum 1979 rowsD6_row1979 = 60292859 := ddSingle (by decide +kernel)

private def rowsD6_row1980 : List ℕ := [
  127626363049081266167844372211578810460390525242810642890991295465380366272607673645365238356575021977058452233542391179195298899227231320089233818213698137804732036398790619520]

private theorem rowsD6_row1980_checked :
    rowsD6_row1980.length = 1 ∧ rowsSum 1980 rowsD6_row1980 = 60662595 := ddSingle (by decide +kernel)

private def rowsD6_row1981 : List ℕ := [
  127873693450557969832940509494291619076235052670375074307294356817337609302494932030872446346336564714505625204267126875751114629955142321911550216454361070621248196620341883264]

private theorem rowsD6_row1981_checked :
    rowsD6_row1981.length = 1 ∧ rowsSum 1981 rowsD6_row1981 = 61019904 := ddSingle (by decide +kernel)

private def rowsD6_row1982 : List ℕ := [
  254754673416945178313422010008362834270928207616140250703320218352026450581314581858460168878540859838046387023642543705002730784070919498913127049698147651033298026416153178496]

private theorem rowsD6_row1982_checked :
    rowsD6_row1982.length = 1 ∧ rowsSum 1982 rowsD6_row1982 = 61356710 := ddSingle (by decide +kernel)

private def rowsD6_row1983 : List ℕ := [
  381388322040222228537809466850743698131563249681615478207902574858463143639938961726283045629378134438682120655834173089196317019466013688357308307250492872934604477710892937600]

private theorem rowsD6_row1983_checked :
    rowsD6_row1983.length = 1 ∧ rowsSum 1983 rowsD6_row1983 = 61740488 := ddSingle (by decide +kernel)

private def rowsD6_row1984 : List ℕ := [
  381636621408390668177328236088677350252337567240250991647156316255268174708127520947279734184239525748306614575695903839138170217584721620888461026414534329585774590455175065984]

private theorem rowsD6_row1984_checked :
    rowsD6_row1984.length = 1 ∧ rowsSum 1984 rowsD6_row1984 = 62116571 := ddSingle (by decide +kernel)

private def rowsD6_row1985 : List ℕ := [
  65344697881129608270906765767536258955604447038545271079756287845703347706781317366436005577205295534774574447018997194838720640966161093445842768284745812247542950639992632914304]

private theorem rowsD6_row1985_checked :
    rowsD6_row1985.length = 1 ∧ rowsSum 1985 rowsD6_row1985 = 62380616 := ddSingle (by decide +kernel)

private def rowsD6 : List ℕ :=
    rowsD6_row1979 ++ rowsD6_row1980 ++ rowsD6_row1981 ++
    rowsD6_row1982 ++ rowsD6_row1983 ++ rowsD6_row1984 ++
    rowsD6_row1985

private theorem rowsD6_checked :
    rowsD6.length = 7 ∧ rowsSum 1979 rowsD6 = 429569743 := by
  constructor <;> simp only [rowsD6, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD6_row1979_checked.1, rowsD6_row1979_checked.2,
    rowsD6_row1980_checked.1, rowsD6_row1980_checked.2,
    rowsD6_row1981_checked.1, rowsD6_row1981_checked.2,
    rowsD6_row1982_checked.1, rowsD6_row1982_checked.2,
    rowsD6_row1983_checked.1, rowsD6_row1983_checked.2,
    rowsD6_row1984_checked.1, rowsD6_row1984_checked.2,
    rowsD6_row1985_checked.1, rowsD6_row1985_checked.2]

private def rowsD7_row1986 : List ℕ := [
  65471331046685680554465540756328809513590684353228262650163200028047228980312215031091247077341446576078449576661821515120699660775185400359364706776282044863070226087395845095808]

private theorem rowsD7_row1986_checked :
    rowsD7_row1986.length = 1 ∧ rowsSum 1986 rowsD7_row1986 = 62750730 := ddSingle (by decide +kernel)

private def rowsD7_row1987 : List ℕ := [
  130434392789475931296472069124281770756496673509964779267839442077392986499349438794171213002951902314233009603227169149121085788062923642552487208913791077959032592265055020663168]

private theorem rowsD7_row1987_checked :
    rowsD7_row1987.length = 1 ∧ rowsSum 1987 rowsD7_row1987 = 63106578 := ddSingle (by decide +kernel)

private def rowsD7_row1988 : List ℕ := [
  195270820884593781004328894223607029095218917418716644186221762683015887877254041013360797263388452745949688236588750993635966364460765802433702297964132310179525913720979860898176]

private theorem rowsD7_row1988_checked :
    rowsD7_row1988.length = 1 ∧ rowsSum 1988 rowsD7_row1988 = 63484853 := ddSingle (by decide +kernel)

private def rowsD7_row1989 : List ℕ := [
  195397949194018147147141049626198836249845585134661460063830877806411996809476696418571024240756228788435543180102710513244526332640686320136230840364784621205476439872480779321728]

private theorem rowsD7_row1989_checked :
    rowsD7_row1989.length = 1 ∧ rowsSum 1989 rowsD7_row1989 = 63874545 := ddSingle (by decide +kernel)

private def rowsD7_row1990 : List ℕ := [
  260360764090415766604987433853955115560258493204586401159504434942564960192929280275616735982503227318604919610421211945615449825817500319893338861578659414852921084215238427033984]

private theorem rowsD7_row1990_checked :
    rowsD7_row1990.length = 1 ∧ rowsSum 1990 rowsD7_row1990 = 64269789 := ddSingle (by decide +kernel)

private def rowsD7_row1991 : List ℕ := [
  33521321495903068443886356867240350470958430388852870476883558414360181235562137518680924989662399443345211021468102988041960769327694430097306835477521439838330179286374247536148864]

private theorem rowsD7_row1991_checked :
    rowsD7_row1991.length = 1 ∧ rowsSum 1991 rowsD7_row1991 = 64582414 := ddSingle (by decide +kernel)

private def rowsD7_row1992 : List ℕ := [
  66782408860880331860082959945791685219033859734742210226083290890622642350945500834650465254625556134031425286734038116788674132011529888920560073437816687190731904306209593013453184]

private theorem rowsD7_row1992_checked :
    rowsD7_row1992.length = 1 ∧ rowsSum 1992 rowsD7_row1992 = 64894000 := ddSingle (by decide +kernel)

private def rowsD7 : List ℕ :=
    rowsD7_row1986 ++ rowsD7_row1987 ++ rowsD7_row1988 ++
    rowsD7_row1989 ++ rowsD7_row1990 ++ rowsD7_row1991 ++
    rowsD7_row1992

private theorem rowsD7_checked :
    rowsD7.length = 7 ∧ rowsSum 1986 rowsD7 = 446962909 := by
  constructor <;> simp only [rowsD7, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD7_row1986_checked.1, rowsD7_row1986_checked.2,
    rowsD7_row1987_checked.1, rowsD7_row1987_checked.2,
    rowsD7_row1988_checked.1, rowsD7_row1988_checked.2,
    rowsD7_row1989_checked.1, rowsD7_row1989_checked.2,
    rowsD7_row1990_checked.1, rowsD7_row1990_checked.2,
    rowsD7_row1991_checked.1, rowsD7_row1991_checked.2,
    rowsD7_row1992_checked.1, rowsD7_row1992_checked.2]

private def rowsD8_row1993 : List ℕ := [
  99978660292912015874216380112891478635526558589443987738062960444733790887270644660310027919792930297602044152792276816072302821066730721481349188627762164883383193106560714748871040]

private theorem rowsD8_row1993_checked :
    rowsD8_row1993.length = 1 ∧ rowsSum 1993 rowsD8_row1993 = 65248059 := ddSingle (by decide +kernel)

private def rowsD8_row1994 : List ℕ := [
  100043749987337291324939693266075575534354872006549024738030756644105872793728417687523475030748898245545564916377175195060837374190994399379184758107633119047810998560303845130518912]

private theorem rowsD8_row1994_checked :
    rowsD8_row1994.length = 1 ∧ rowsSum 1994 rowsD8_row1994 = 65628090 := ddSingle (by decide +kernel)

private def rowsD8_row1995 : List ℕ := [
  133304711214292872501753566133225019166852348520748237393666270690593259618761443512187848250947771173490482571724977231745470420148452671836809806409071740825739216671290423588831616]

private theorem rowsD8_row1995_checked :
    rowsD8_row1995.length = 1 ∧ rowsSum 1995 rowsD8_row1995 = 66018413 := ddSingle (by decide +kernel)

private def rowsD8_row1996 : List ℕ := [
  17162916605902371043269814715812534514251634805496566572440838823692880811062285811476876895673468276616708797614147084785901005771791120708963538568701923763824269515634870483914211712]

private theorem rowsD8_row1996_checked :
    rowsD8_row1996.length = 1 ∧ rowsSum 1996 rowsD8_row1996 = 66385371 := ddSingle (by decide +kernel)

private def rowsD8_row1997 : List ℕ := [
  34192593336770729910519713372447645619801219125615612706148694890426369547669789406656672655750875014945995796414949136880479847022123083065484156076999184850126569962273095109488820608]

private theorem rowsD8_row1997_checked :
    rowsD8_row1997.length = 1 ∧ rowsSum 1997 rowsD8_row1997 = 66779004 := ddSingle (by decide +kernel)

private def rowsD8_row1998 : List ℕ := [
  34192593463404378533782374088515720513191063980593299741491320276373909757653907121778140396623349108201351521804080593868068435109949365481209457472815951867074892916019056193747173760]

private theorem rowsD8_row1998_checked :
    rowsD8_row1998.length = 1 ∧ rowsSum 1998 rowsD8_row1998 = 67102115 := ddSingle (by decide +kernel)

private def rowsD8_row1999 : List ℕ := [
  51222399993516693158369122952230694673589694467350181954119497855362344739567991983043350149295343129524158808422623494344802620910041738125130121048524251992551375795988656568955715968]

private theorem rowsD8_row1999_checked :
    rowsD8_row1999.length = 1 ∧ rowsSum 1999 rowsD8_row1999 = 67423880 := ddSingle (by decide +kernel)

private def rowsD8 : List ℕ :=
    rowsD8_row1993 ++ rowsD8_row1994 ++ rowsD8_row1995 ++
    rowsD8_row1996 ++ rowsD8_row1997 ++ rowsD8_row1998 ++
    rowsD8_row1999

private theorem rowsD8_checked :
    rowsD8.length = 7 ∧ rowsSum 1993 rowsD8 = 464584932 := by
  constructor <;> simp only [rowsD8, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD8_row1993_checked.1, rowsD8_row1993_checked.2,
    rowsD8_row1994_checked.1, rowsD8_row1994_checked.2,
    rowsD8_row1995_checked.1, rowsD8_row1995_checked.2,
    rowsD8_row1996_checked.1, rowsD8_row1996_checked.2,
    rowsD8_row1997_checked.1, rowsD8_row1997_checked.2,
    rowsD8_row1998_checked.1, rowsD8_row1998_checked.2,
    rowsD8_row1999_checked.1, rowsD8_row1999_checked.2]

private def rowsD9_row2000 : List ℕ := [
  68252012141717950720897818830658405839684054299668113578853073197836985803850139753289600899811039786941435318520137453095328191127673936841431325055906506125866494987575424325743952256]

private theorem rowsD9_row2000_checked :
    rowsD9_row2000.length = 1 ∧ rowsSum 2000 rowsD9_row2000 = 67821210 := ddSingle (by decide +kernel)

private def rowsD9_row2001 : List ℕ := [
  8787413302221766643752672029961957168673523916727452520302349504153213336227914331550195945558590962593142296449909324008635940956442317845939864767084173581578083059774666305480316567936]

private theorem rowsD9_row2001_checked :
    rowsD9_row2001.length = 1 ∧ rowsSum 2001 rowsD9_row2001 = 68213984 := ddSingle (by decide +kernel)

private def rowsD9_row2002 : List ℕ := [
  17506607788426613714186093232634088949390735496032260869029438474930497713713442697768355235332325197751464845907930633484088552879516878816734374979051303207783346499736162458553716720000]

private theorem rowsD9_row2002_checked :
    rowsD9_row2002.length = 1 ∧ rowsSum 2002 rowsD9_row2002 = 68573887 := ddSingle (by decide +kernel)

private def rowsD9_row2003 : List ℕ := [
  17506607853263041809296575533320048902753824758063769467643555981503441795303144099531744145379164369538684322925746817823419051597990971327652488137365039988417831417398847614279923941760]

private theorem rowsD9_row2003_checked :
    rowsD9_row2003.length = 1 ∧ rowsSum 2003 rowsD9_row2003 = 68976045 := ddSingle (by decide +kernel)

private def rowsD9_row2004 : List ℕ := [
  26225868796680546897084990951542115672877923567283293160464820186839587153689507623824116527269623007156183070782985406641046635276794573357472914412218011698642754736259678680165896044928]

private theorem rowsD9_row2004_checked :
    rowsD9_row2004.length = 1 ∧ rowsSum 2004 rowsD9_row2004 = 69370983 := ddSingle (by decide +kernel)

private def rowsD9_row2005 : List ℕ := [
  34945030216559590769099683227237998181970747105147141315854080168324733235646469381607087020907409557883641949817045199184045696688174744079985590360959527281204929233191246453757012230528]

private theorem rowsD9_row2005_checked :
    rowsD9_row2005.length = 1 ∧ rowsSum 2005 rowsD9_row2005 = 69671945 := ddSingle (by decide +kernel)

private def rowsD9 : List ℕ :=
    rowsD9_row2000 ++ rowsD9_row2001 ++ rowsD9_row2002 ++
    rowsD9_row2003 ++ rowsD9_row2004 ++ rowsD9_row2005

private theorem rowsD9_checked :
    rowsD9.length = 6 ∧ rowsSum 2000 rowsD9 = 412628054 := by
  constructor <;> simp only [rowsD9, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD9_row2000_checked.1, rowsD9_row2000_checked.2,
    rowsD9_row2001_checked.1, rowsD9_row2001_checked.2,
    rowsD9_row2002_checked.1, rowsD9_row2002_checked.2,
    rowsD9_row2003_checked.1, rowsD9_row2003_checked.2,
    rowsD9_row2004_checked.1, rowsD9_row2004_checked.2,
    rowsD9_row2005_checked.1, rowsD9_row2005_checked.2]

private def rowsD10_row2006 : List ℕ := [
  4490453445863234608973368833032118886390518806160544833149567944124925784926724610107739451093950210527961325889012099834338299642698330070813997669933445144796493485039621197460515835756928]

private theorem rowsD10_row2006_checked :
    rowsD10_row2006.length = 1 ∧ rowsSum 2006 rowsD10_row2006 = 70092207 := ddSingle (by decide +kernel)

private def rowsD10_row2007 : List ℕ := [
  8963383187674426221663279735108653542088056573967752442169490794067726491314564710967675078527696850015658871279471470997794382639203360582432446198098645026684367911848715505858547783188864]

private theorem rowsD10_row2007_checked :
    rowsD10_row2007.length = 1 ∧ rowsSum 2007 rowsD10_row2007 = 70478169 := ddSingle (by decide +kernel)

private def rowsD10 : List ℕ :=
    rowsD10_row2006 ++ rowsD10_row2007

private theorem rowsD10_checked :
    rowsD10.length = 2 ∧ rowsSum 2006 rowsD10 = 140570376 := by
  constructor <;> simp only [rowsD10, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD10_row2006_checked.1, rowsD10_row2006_checked.2,
    rowsD10_row2007_checked.1, rowsD10_row2007_checked.2]

def rowsD : List ℕ := rowsD1 ++ rowsD2 ++ rowsD3 ++ rowsD4 ++ rowsD5 ++ rowsD6 ++ rowsD7 ++ rowsD8 ++ rowsD9 ++ rowsD10

theorem rowsD_length : rowsD.length = 65 := by
  simp only [rowsD, List.length_append, Nat.reduceAdd,
    rowsD1_checked.1, rowsD2_checked.1, rowsD3_checked.1, rowsD4_checked.1,
    rowsD5_checked.1, rowsD6_checked.1, rowsD7_checked.1, rowsD8_checked.1,
    rowsD9_checked.1, rowsD10_checked.1]

theorem rowsD_sum : rowsSum 1943 rowsD = 3844665783 := by
  simp only [rowsD, rowsSum_append, List.length_append, Nat.reduceAdd,
    rowsD1_checked.1, rowsD2_checked.1, rowsD3_checked.1, rowsD4_checked.1,
    rowsD5_checked.1, rowsD6_checked.1, rowsD7_checked.1, rowsD8_checked.1,
    rowsD9_checked.1, rowsD1_checked.2, rowsD2_checked.2, rowsD3_checked.2,
    rowsD4_checked.2, rowsD5_checked.2, rowsD6_checked.2, rowsD7_checked.2,
    rowsD8_checked.2, rowsD9_checked.2, rowsD10_checked.2]

end K1_13_2_3_4
end PackSource_K1_13_2_3_4DataD

section PackSource_K1_14_4Defs
set_option autoImplicit true
namespace K1_14_4

open K1_14 Finset

/-- At grade j, eligible Y indices are the total indices from j up to the
smaller of the bank's total cap and the bound from its cutoff. -/
def gradeWidth (k B W j : ℕ) : ℕ :=
  min (B + 1) ((W + j) / k + 1) - j

def gradeCapacity (w : ℤ) (W j : ℕ) : ℕ :=
  let b := band w
  gradeWidth (131071 - w.toNat) b.jetBound W j *
    slots b.subbankSeeds (forcedPower w W j * (b.seedBound + 1))

def cutoffCapacity (w : ℤ) (W : ℕ) : ℕ :=
  ∑ j ∈ range ((band w).vBound + 1), gradeCapacity w W j

end K1_14_4
end PackSource_K1_14_4Defs
