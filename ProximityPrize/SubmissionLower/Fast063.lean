import ProximityPrize.SubmissionLower.Fast059
import ProximityPrize.SubmissionLower.Fast060
set_option Elab.async false
set_option autoImplicit true
section
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
end
section
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
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_3
noncomputable section
open K1_13 K1_13_6_1_4_3_3 MvPolynomial
abbrev Degree := Fin 4 → ℕ
abbrev GenericJets (k : Type) [Field k] (P : Fin 4 → Shape) :=
  Jets (CoefficientField k P)
def auxiliary : Shape := ⟨6, 6, 2⟩
def shapeAt (P : Fin 4 → Shape) (b : ℕ) (d : Degree) : Shape :=
  (((((auxiliary.scale b).plus ((P 0).scale (d 0))).plus
    ((P 1).scale (d 1))).plus ((P 2).scale (d 2))).plus ((P 3).scale (d 3)))
def shift (d : Degree) (i : Fin 4) (n : ℕ) : Degree := d + Pi.single i n
def piece (k : Type) [Field k] (P : Fin 4 → Shape) (b : ℕ) (d : Degree) :
    Submodule (CoefficientField k P) (GenericJets k P) :=
  restrictSupport (CoefficientField k P) (lattice (shapeAt P b d))
def prefixIdeal (k : Type) [Field k] (P : Fin 4 → Shape) (r : ℕ) :
    Ideal (GenericJets k P) :=
  Ideal.span (genericEquation k P '' {i : Fin 4 | i.val < r})
end
end K1_13_6_1_4_3_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_3_3_3
noncomputable section
open K1_13 K1_13_7_1 K1_13_7_1_1 K1_13_6_1_4_3_3 MvPolynomial
open scoped Pointwise
private theorem auxiliary_admissible : Chamber auxiliary ∧ Even auxiliary.j ∧ Even auxiliary.t :=
  ⟨⟨by decide, by decide⟩, ⟨3, rfl⟩, ⟨1, rfl⟩⟩
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
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_1_4_3_3_3
noncomputable section
open K1_13 K1_13_6_1_4_3_3 MvPolynomial
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
end
section
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
end
section
namespace K1_13_6_1_3
noncomputable section
open Polynomial K1_13 K1_13_6
abbrev RationalJets := MvPolynomial (Fin 4) GenericField
def toRational : Row 4 →+* RationalJets :=
  MvPolynomial.map (algebraMap Geom[X] GenericField)
abbrev contractedPrime (surface : Ideal GeoJets) : Ideal RationalJets :=
  surface.comap (MvPolynomial.map (algebraMap GenericField GeoField))
def contractedLength (g P : Row 4) (surface : Ideal GeoJets) (hp : surface.IsPrime) : ℕ∞ := by
  letI := hp
  let L := Localization.AtPrime (contractedPrime surface)
  let J : Ideal L := (Ideal.span {toRational g, toRational P}).map (algebraMap RationalJets L)
  exact Order.coheight J
def NormalForm (g P : Row 4) (surface : Ideal GeoJets) (v : ℕ) : Prop :=
  ∃ t d u B : Row 4,
    toGeneric t ∈ surface ∧ toGeneric d ∉ surface ∧ toGeneric u ∉ surface ∧
    d * P = B * g + u * t ^ v ∧
    ∀ a : Row 4, toGeneric a ∈ surface →
      ∃ e C W : Row 4, toGeneric e ∉ surface ∧ e * a = C * g + W * t
end
end K1_13_6_1_3
end
section
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
end
end K1_13_6_1_3
end
section
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
end
section
namespace K1_13_6_1_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_1
def c1 : Prop :=
  ∀ f P Q surface, IsRelPrime (toGeneric f) (toGeneric P) →
    (intersectionIdeal f Q).IsMinimalPrime surface → toGeneric P ∈ surface →
    ∃ (hZ : (intersectionIdeal f P).IsMinimalPrime surface) (w : ℕ),
      0 < w ∧ w ≤ (shape f).b * (shape P).b ∧
        cycleLength (intersectionIdeal f P) surface hZ.isPrime = (w : ℕ∞)
def c2 : Prop :=
  ∀ g P surface (hZ : (intersectionIdeal g P).IsMinimalPrime surface) (v : ℕ),
    IsRelPrime (toGeneric g) (toGeneric P) → toGeneric (separant g) ∉ surface →
    0 < v → contractedLength g P surface hZ.isPrime = (v : ℕ∞) →
    NormalForm g P surface v
def c3 : Prop :=
  ∀ g P surface (hZ : (intersectionIdeal g P).IsMinimalPrime surface) (v : ℕ),
    cycleLength (intersectionIdeal g P) surface hZ.isPrime = (v : ℕ∞) →
    v < K1.p → contractedLength g P surface hZ.isPrime = (v : ℕ∞)
end
end K1_13_6_1_3
end
section
set_option autoImplicit false
namespace K1_13_6_1_3_3
noncomputable section
open IsLocalRing
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
theorem localLength_le_map {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (Q : Ideal S) [Q.IsPrime] (J : Ideal R) :
    localLength (Q.comap (algebraMap R S)) J ≤ localLength Q (J.map (algebraMap R S)) := by
  rw [localLength_map]
  exact ENat.self_le_mul_right _ (localLength_pos Q (Ideal.map_le_iff_le_comap.mpr le_rfl)).ne'
end
end K1_13_6_1_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_1_3_3
noncomputable section
open IsLocalRing Algebra
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
section FiniteScalarExtension
variable {k l σ : Type*} [Field k] [Field l] [Algebra k l] [FiniteDimensional k l]
variable (Q : Ideal (MvPolynomial σ l)) [Q.IsPrime]
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
theorem purely_inseparable_fibre [FiniteDimensional k l] (p : ℕ) [ExpChar k p] (hp : p.Prime)
    (h : localLength Q (q.map (algebraMap (MvPolynomial σ k) _)) < (p : ℕ∞)) :
    localLength Q (q.map (algebraMap (MvPolynomial σ k) _)) = 1 := by
  rw [purely_inseparable_fibre_length q Q] at h ⊢
  exact tensor_selfLength_eq_one p hp h
end PolynomialFibre
end
end K1_13_6_1_3_3
end
section
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
end
section
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
end
section
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
end
section
namespace K1_13_6_1_5
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
open scoped BigOperators
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
end
section
namespace K1_13_6_1_5
noncomputable section
open Polynomial K1 K1_13 K1_13_6 K1_13_6_1 K1_13_7 K1_13_7_1
def c2 : Prop :=
  ∀ (C : Ideal GeoJets) (p : Shape), C.IsPrime → ringKrullDim (GeoJets ⧸ C) = 1 →
    InBox ⟨1, 3, 1⟩ p →
    ∀ (D : GeoJets), GeoFits D p → D ∉ C →
      ∀ points : Finset GeoPoint,
        (∀ x ∈ points, C ≤ RingHom.ker (MvPolynomial.eval x) ∧ MvPolynomial.eval x D = 0) →
        6 * points.card ≤ sectionDegree C (p.scale 6)
end
end K1_13_6_1_5
end
section
set_option autoImplicit false
namespace K1_13_6_1_5_2
open K1_13 K1_13_6 K1_13_6_1
abbrev CutQuotient (C : Ideal GeoJets) (E : GeoJets) :=
  GeoJets ⧸ (C ⊔ Ideal.span {E})
abbrev GenericQuotient (C : Ideal GeoJets) (a : Shape) :=
  SectionJets a ⧸
    (C.map (MvPolynomial.map (algebraMap GeoField (SectionField a))) ⊔
      Ideal.span {genericSection a})
noncomputable def boxSection (a : Shape) (c : SectionIndex a → GeoField) : GeoJets :=
  ∑ m ∈ boxMonomials a, MvPolynomial.C (c m) * ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val
end K1_13_6_1_5_2
end
section
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
end
section
set_option autoImplicit false
namespace K1_13_6_1_5_2
open K1_13 K1_13_6 K1_13_6_1 K1_13_7_1
def c1 : Prop :=
  ∀ (C : Ideal GeoJets) (a : Shape), C.IsPrime → ringKrullDim (GeoJets ⧸ C) = 1 →
    Module.Finite (SectionField a) (GenericQuotient C a)
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
end
section
set_option autoImplicit false
namespace K1_13_6_1_5_2_2
open MvPolynomial
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
end
section
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
end
section
namespace K1_13_6_1_4_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1_4_2 MvPolynomial
def combinedShape (a b h : Shape) (t : Fin 3 → ℕ) : Shape :=
  ((a.scale (t 0)).plus (b.scale (t 1))).plus (h.scale (t 2))
def boxHilbert (surface : Ideal GeoJets) (p : Shape) : ℕ :=
  Module.finrank GeoField
    ((restrictSupport GeoField (latticeIndices p)).map
      (Ideal.Quotient.mkₐ GeoField surface).toLinearMap)
def multiHilbert (surface : Ideal GeoJets) (a b h : Shape) (t : Fin 3 → ℕ) : ℕ :=
  boxHilbert surface (combinedShape a b h t)
abbrev SectionVariable (a b h : Shape) :=
  Σ l : Fin 3, latticeIndices (![a, b, h] l)
def blockDegree {σ : Type} (block : σ → Fin 3) (e : σ →₀ ℕ) : Fin 3 → ℕ :=
  fun l => e.sum fun v n => if block v = l then n else 0
def standardCount {σ : Type} (block : σ → Fin 3) (forbidden : Finset (σ →₀ ℕ))
    (t : Fin 3 → ℕ) : ℕ :=
  ({e | blockDegree block e = t ∧ ∀ f ∈ forbidden, ¬ f ≤ e} : Set (σ →₀ ℕ)).ncard
end
end K1_13_6_1_4_2_2
end
section
namespace K1_13_6_1_4_2_2
noncomputable section
open MvPolynomial
open scoped BigOperators
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
end
section
namespace K1_13_6_1_4_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_7_1 MvPolynomial
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
end
section
namespace K1_13_6_1_4_2_2
noncomputable section
open Filter K1_13 K1_13_6 K1_13_6_1_4 K1_13_6_1_4_2 K1_13_7_1 MvPolynomial
def c1 : Prop :=
  ∀ (surface : Ideal GeoJets) (a b h : Shape),
    Chamber a → Chamber b → Chamber h →
    ∃ forbidden : Finset (SectionVariable a b h →₀ ℕ),
      ∀ t : Fin 3 → ℕ,
        multiHilbert surface a b h t = standardCount (fun v => v.1) forbidden t
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
end
section
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
end
section
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
end
section
namespace K1_13_6_1_2
noncomputable section
open K1_13 K1_13_6
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
end
section
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
end
section
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
theorem proof : K1_13_6_1_4_2_1_2.c1 := by
  intro k _ I a h ha hh
  refine ⟨rees_noetherian I a h ha hh, ?_⟩
  intro i j x hx n hi hj
  exact homogeneous_mem I a h (i, j) ((irrelevant I a h ^ n).restrictScalars k)
    (fun m hm => liftedMonomial_mem_pow I a h ha hh i j m hm n hi hj) x hx
end
end K1_13_6_1_4_2_1_2_1
end
section
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
end
section
namespace K1_13_6_1_2
noncomputable section
open Polynomial K1_13 K1_13_6
open scoped BigOperators
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
theorem map_hassePartial {n : ℕ} {A B : Type*} [CommSemiring A] [CommSemiring B]
    (φ : A →+* B) (a : Fin n →₀ ℕ) (P : MvPolynomial (Fin n) A) :
    MvPolynomial.map φ (hassePartial a P) = hassePartial a (MvPolynomial.map φ P) := by
  have h : (MvPolynomial.map (MvPolynomial.map φ)).comp (taylorHom (n := n)) =
      (taylorHom (A := B)).comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp [taylorHom]
  have hc := congrArg (fun F : MvPolynomial (Fin n) (MvPolynomial (Fin n) B) => F.coeff a)
    (RingHom.congr_fun h P)
  simpa only [RingHom.comp_apply, MvPolynomial.coeff_map, taylor_coeff] using hc
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
end
section
namespace K1_13_6_1_2
noncomputable section
open K1_13 K1_13_6
def c1 : Prop :=
  ∀ (F G : GeoJets) (p : Ideal GeoJets) (hp : (Ideal.span {F, G}).IsMinimalPrime p),
    F ≠ 0 → IsRelPrime F G →
    cycleLength (Ideal.span {F, G}) p hp.isPrime ≤ (↑(F.totalDegree * G.totalDegree) : ℕ∞)
def c2 : Prop :=
  ∀ (F : GeoJets) (p : Ideal GeoJets) [p.IsPrime] (d : ℕ),
    p.height = 2 →
    (∀ a : Fin 4 →₀ ℕ, multiOrder a < d → hassePartial a F ∈ p) →
    VanishesTo p F d
end
end K1_13_6_1_2
end
section
namespace K1_13_6_1_2_2
noncomputable section
open K1_13_6 K1_13_6_1_2
open MvPolynomial
open scoped BigOperators
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
end
section
namespace K1_13_2_3_4
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0
open K1_13_2
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
private def rowsC1_row000 : List ℕ := [0x30403020130c06c4023140c0603420100804424130c06030180c86836201008040a1918904c26180c06030180c2643420100]
private theorem rowsC1_row000_checked :
    rowsC1_row000.length = 1 ∧ rowsSum 1866 rowsC1_row000 = 28404388 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row001 : List ℕ := [0x40403020140c0704024180c0603420100824624140c06030180c86836201008040a1918904c28180c06030180c2663420100]
private theorem rowsC1_row001_checked :
    rowsC1_row001.length = 1 ∧ rowsSum 1867 rowsC1_row001 = 28636056 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row002 : List ℕ := [0x2050483020180c0804024180c0623420100844626140c06030184cc683820100804122118904c28180c06030180c3663420100]
private theorem rowsC1_row002_checked :
    rowsC1_row002.length = 1 ∧ rowsSum 1868 rowsC1_row002 = 28875231 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row003 : List ℕ := [0x2060483422180c8804226180c0623620100844626140c06030184cc6c38201008041a2118904c28180c06030180c4663420100]
private theorem rowsC1_row003_checked :
    rowsC1_row003.length = 1 ∧ rowsSum 1869 rowsC1_row003 = 29121059 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row004 : List ℕ := [0x4060503824180d0804426180c0643620100864826180c06030188cc6c40201008041a2118904c28180c06030180c4663620100]
private theorem rowsC1_row004_checked :
    rowsC1_row004.length = 1 ∧ rowsSum 1870 rowsC1_row004 = 29305336 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row005 : List ℕ := [0x6070604024180d0804426180c0663620100864826180c06030188cc6c4020100804222120904c30180c06030180c4663620100]
private theorem rowsC1_row005_checked :
    rowsC1_row005.length = 1 ∧ rowsSum 1871 rowsC1_row005 = 29479343 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row006 : List ℕ := [0x6080604026180d8804628180c0663820100884826180c0603018cd06c4020100804222120904c30180c06030180c6663620100]
private theorem rowsC1_row006_checked :
    rowsC1_row006.length = 1 ∧ rowsSum 1872 rowsC1_row006 = 29714183 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row007 : List ℕ := [0x8080604028180e0804828180c0684020100884826180c06030190d06c4020100804223120984c30180c06030180c6663620100]
private theorem rowsC1_row007_checked :
    rowsC1_row007.length = 1 ∧ rowsSum 1873 rowsC1_row007 = 29944623 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row008 : List ℕ := [0x40a08060403018100804830180c06840201048c4826180c06030190d06c4020100814323120984c30180c06030180c6683620100]
private theorem rowsC1_row008_checked :
    rowsC1_row008.length = 1 ∧ rowsSum 1874 rowsC1_row008 = 30174338 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC1_row009 : List ℕ := [0x40c09068443019100844830180c46c40201088c4c28180c06030190d06c4020100814323120984c30180c06030180c6683620100]
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
private def rowsC2_row000 : List ℕ := [0x80c0a070483019100844c30180c86c40201088c4c28180c06030998d0704020100824323120984c30180c06030180c8683620100]
private theorem rowsC2_row000_checked :
    rowsC2_row000.length = 1 ∧ rowsSum 1876 rowsC2_row000 = 30664326 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row001 : List ℕ := [0xc0c0c08048301a100884c30180c86c402010c904c30180c06030998d8704020100824423120985030180c06030182c8683620100]
private theorem rowsC2_row001_checked :
    rowsC2_row001.length = 1 ∧ rowsSum 1877 rowsC2_row001 = 30888547 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row002 : List ℕ := [0xc100c0804c301b1008c4c30180cc704020110904c30180c06031198d8804020100834423120985030180c06030182c8683620100]
private theorem rowsC2_row002_checked :
    rowsC2_row002.length = 1 ∧ rowsSum 1878 rowsC2_row002 = 31120790 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row003 : List ℕ := [0x10100c0804c301b1008c5030180d0704020110904c30180c060319a0d8804020100834423120985030180c06030184c8683620100]
private theorem rowsC2_row003_checked :
    rowsC2_row003.length = 1 ∧ rowsSum 1879 rowsC2_row003 = 31376287 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row004 : List ℕ := [0x814100c080603020100906030180d0804020910904c30180c060319a0d8804020100844424120985030180c06030184c8683620100]
private theorem rowsC2_row004_checked :
    rowsC2_row004.length = 1 ∧ rowsSum 1880 rowsC2_row004 = 31616683 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row005 : List ℕ := [0x818120d088603220108906030188d0804020918904c30180c060321a0d8804020100844424120986030180c06030186cc683620100]
private theorem rowsC2_row005_checked :
    rowsC2_row005.length = 1 ∧ rowsSum 1881 rowsC2_row005 = 31804404 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row006 : List ℕ := [0x1018140e088603220108986030188d8804021118985030180c060321a0d8804020100864624130986030180c06030188cc683620100]
private theorem rowsC2_row006_checked :
    rowsC2_row006.length = 1 ∧ rowsSum 1882 rowsC2_row006 = 32048882 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row007 : List ℕ := [0x18181810090603420110986030190d8804021118985030180c061331a0e0804020102864624130986030180c06030188cc683620100]
private theorem rowsC2_row007_checked :
    rowsC2_row007.length = 1 ∧ rowsSum 1883 rowsC2_row007 = 32294911 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row008 : List ℕ := [0x18201810098603620118986030198d8804021920986030180c061331b0e0804020104864624130986030180c06030188cc684020100]
private theorem rowsC2_row008_checked :
    rowsC2_row008.length = 1 ∧ rowsSum 1884 rowsC2_row008 = 32492899 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC2_row009 : List ℕ := [0x20201810098603620118a06030198e0804022120986030180c062331b0e0804020104884624130986030180c0603018ccc6c4020100]
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
private def rowsC3_row000 : List ℕ := [0x10282018100c0603820120a060301a100804022120986030180c062331b100804020106884624130a06030180c0603018ccc6c4020100]
private theorem rowsC3_row000_checked :
    rowsC3_row000.length = 1 ∧ rowsSum 1886 rowsC3_row000 = 32973215 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3_row001 : List ℕ := [0x1030241a110c0644020120c060301a100804122120986030180c063341b100804020106884624130a06030180c0603018ccc6c4020100]
private theorem rowsC3_row001_checked :
    rowsC3_row001.length = 1 ∧ rowsSum 1887 rowsC3_row001 = 33225916 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3_row002 : List ℕ := [0x2030281c110c0644021130c060311b100804123120986030180c064341b100804020108884624130a06030180c0603018cd06c4020100]
private theorem rowsC3_row002_checked :
    rowsC3_row002.length = 1 ∧ rowsSum 1888 rowsC3_row002 = 33489779 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3_row003 : List ℕ := [0x30303020120c0684022130c060321b100804223130a06030180c064341b100804020108884824130a06030180c06030590d06c4020100]
private theorem rowsC3_row003_checked :
    rowsC3_row003.length = 1 ∧ rowsSum 1889 rowsC3_row003 = 33755809 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3_row004 : List ℕ := [0x30403020130c0684022130c060321b100804323130a06030180c064341b10080402010c884824130c06030180c06030590d06c4020100]
private theorem rowsC3_row004_checked :
    rowsC3_row004.length = 1 ∧ rowsSum 1890 rowsC3_row004 = 33963460 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3_row005 : List ℕ := [0x40403020130c06c4023130c060331b100804324130c06030180c266341c10080402050c8c4826130c06030180c06030990d06c4020100]
private theorem rowsC3_row005_checked :
    rowsC3_row005.length = 1 ∧ rowsSum 1891 rowsC3_row005 = 34212972 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3_row006 : List ℕ := [0x2050403020140c0704024140c060341c100804424130c06030180c466361c10080402050c8c4826130c06030180c06030990d06c4020100]
private theorem rowsC3_row006_checked :
    rowsC3_row006.length = 1 ∧ rowsSum 1892 rowsC3_row006 = 34469951 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3_row007 : List ℕ := [0x2060483422180c8804024180c0603420100804424130c06030180c466361c10080402090c8c4826130c06030180c06030d90d06c4020100]
private theorem rowsC3_row007_checked :
    rowsC3_row007.length = 1 ∧ rowsSum 1893 rowsC3_row007 = 34710054 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC3_row008 : List ℕ := [0x4060503822180c8804224180c0623420100824624130c06030180c6683620100804020d108c4826130c06030180c06031198d06c4020100]
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
private def rowsC4_row000 : List ℕ := [0x6070604024180d0804426180c0623620100844624140c06030180c6683620100804020d108c4826140c06030180c06031198d06c4020100]
private theorem rowsC4_row000_checked :
    rowsC4_row000.length = 1 ∧ rowsSum 1895 rowsC4_row000 = 35215060 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4_row001 : List ℕ := [0x6080604026180d0804426180c0643620100844626140c06030180c86836201008040211108c4826140c06030180c06031198d06c4020100]
private theorem rowsC4_row001_checked :
    rowsC4_row001.length = 1 ∧ rowsSum 1896 rowsC4_row001 = 35482889 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4_row002 : List ℕ := [0x8080604026180d8804626180c0663620100864826140c06030180c8683620100804021110904826140c06030180c06031998d06c4020100]
private theorem rowsC4_row002_checked :
    rowsC4_row002.length = 1 ∧ rowsSum 1897 rowsC4_row002 = 35752024 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4_row003 : List ℕ := [0x40a080604028180e0804828180c0663820100884826180c06030184cc683820100804021910904826140c06030180c06031998d06c4020100]
private theorem rowsC4_row003_checked :
    rowsC4_row003.length = 1 ∧ rowsSum 1898 rowsC4_row003 = 35999170 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4_row004 : List ℕ := [0x80c09068443018100804830180c0684020100884826180c06030188cc6c38201008040a1918904c26180c06030180c06031998d86c4020100]
private theorem rowsC4_row004_checked :
    rowsC4_row004.length = 1 ∧ rowsSum 1899 rowsC4_row004 = 36195310 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4_row005 : List ℕ := [0x80c0a070443019100844830180c4684020104884826180c06030188cc6c3820100804121918904c26180c06030180c060b1998d8704020100]
private theorem rowsC4_row005_checked :
    rowsC4_row005.length = 1 ∧ rowsSum 1900 rowsC4_row005 = 36479131 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4_row006 : List ℕ := [0xc0e0c08048301a100884c30180c46c40201048c4826180c0603018cd06c4020100804121918904c26180c06030180c060b21a0d8804020100]
private theorem rowsC4_row006_checked :
    rowsC4_row006.length = 1 ∧ rowsSum 1901 rowsC4_row006 = 36712301 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4_row007 : List ℕ := [0x10100c0804c301a100884c30180c86c40201088c4c28180c0603018cd06c40201008041a2118904c26180c06030180c061321a0d8804020100]
private theorem rowsC4_row007_checked :
    rowsC4_row007.length = 1 ∧ rowsSum 1902 rowsC4_row007 = 36993294 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC4_row008 : List ℕ := [0x10100c0804c301b1008c4c30180cc6c402010c8c4c28180c06030190d06c40201008041a2118904c26180c06030180c061321a0d8804020100]
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
private def rowsC5_row000 : List ℕ := [0x814120c08060301c1008c5030180cc70402010c904c28180c06030190d06c4020100804222118904c28180c06030180c061b21a0d8804020100]
private theorem rowsC5_row000_checked :
    rowsC5_row000.length = 1 ∧ rowsSum 1904 rowsC5_row000 = 37531039 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5_row001 : List ℕ := [0x1018120d088603020100906030180d0704020110904c30180c06030998d06c4020100804222118904c28180c06030180c061b21a0d8804020100]
private theorem rowsC5_row001_checked :
    rowsC5_row001.length = 1 ∧ rowsSum 1905 rowsC5_row001 = 37771999 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5_row002 : List ℕ := [0x1018140e088603220108906030180d0804020110904c30180c06031198d8704020100814322120904c28180c06030180c062331a0d8804020100]
private theorem rowsC5_row002_checked :
    rowsC5_row002.length = 1 ∧ rowsSum 1906 rowsC5_row002 = 38045448 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5_row003 : List ℕ := [0x181c1810090603420108986030188d8804020918904c30180c06031198d8704020100814323120984c28180c06030180c062331a0d8804020100]
private theorem rowsC5_row003_checked :
    rowsC5_row003.length = 1 ∧ rowsSum 1907 rowsC5_row003 = 38327971 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5_row004 : List ℕ := [0x20201810098603420110986030190d8804021118904c30180c060319a0d8804020100824323120984c30180c06030180c063331a0d8804020100]
private theorem rowsC5_row004_checked :
    rowsC5_row004.length = 1 ∧ rowsSum 1908 rowsC5_row004 = 38527726 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5_row005 : List ℕ := [0x1020201810098603620118986030190d8804021118985030180c060319a0d8804020100824323120984c30180c06030180c063331a0d8804020100]
private theorem rowsC5_row005_checked :
    rowsC5_row005.length = 1 ∧ rowsSum 1909 rowsC5_row005 = 38819639 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5_row006 : List ℕ := [0x10282418100c0603820118a06030198d8804021918985030180c060321a0d8804020100834423120984c30180c06030180c063331a0d8804020100]
private theorem rowsC5_row006_checked :
    rowsC5_row006.length = 1 ∧ rowsSum 1910 rowsC5_row006 = 39111484 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5_row007 : List ℕ := [0x2030241a110c0644020120a060301a0e0804022120986030180c060321a0d8804020100844423120984c30180c06030180c163331a0d8804020100]
private theorem rowsC5_row007_checked :
    rowsC5_row007.length = 1 ∧ rowsSum 1911 rowsC5_row007 = 39380995 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC5_row008 : List ℕ := [0x3030301c120c0644021120c060301a100804022120986030180c061331a0d8804020100844423120984c30180c06030180c164331b0d8804020100]
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
private def rowsC6_row000 : List ℕ := [0x30383020120c0684021130c060311a100804122120986030180c062331b0e0804020100844424120985030180c06030180c264341b0d8804020101]
private theorem rowsC6_row000_checked :
    rowsC6_row000.length = 1 ∧ rowsSum 1913 rowsC6_row000 = 39942270 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC6_row001 : List ℕ := [0x40403020130c0684022130c060321b100804123120986030180c062331b0e0804020102864424120985030180c06030180c264341b0e0804020102]
private theorem rowsC6_row001_checked :
    rowsC6_row001.length = 1 ∧ rowsSum 1914 rowsC6_row001 = 40226680 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC6_row002 : List ℕ := [0x2040403020140c06c4023130c060321b100804223130a06030180c063341b100804020102864624120985030180c06030180c364341b100804020102]
private theorem rowsC6_row002_checked :
    rowsC6_row002.length = 1 ∧ rowsSum 1915 rowsC6_row002 = 40455650 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC6_row003 : List ℕ := [0x2060483420180c0704023140c060331b100804323130a06030180c063341b100804020104864624130985030180c06030180c464341b100804020103]
private theorem rowsC6_row003_checked :
    rowsC6_row003.length = 1 ∧ rowsSum 1916 rowsC6_row003 = 40745788 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC6_row004 : List ℕ := [0x4060503422180c8804024140c060341c100804324130a06030180c064341b100804020106884624130986030180c06030180c466341b100804020103]
private theorem rowsC6_row004_checked :
    rowsC6_row004.length = 1 ∧ rowsSum 1917 rowsC6_row004 = 40973542 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC6_row005 : List ℕ := [0x6060603824180c8804224180c0603420100804424130c06030180c264341b100804020106884624130986030180c06030180c466341b100804020104]
private theorem rowsC6_row005_checked :
    rowsC6_row005.length = 1 ∧ rowsSum 1918 rowsC6_row005 = 41234803 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC6_row006 : List ℕ := [0x6080604024180d0804226180c0623420100824424130c06030180c266341b100804020108884624130986030180c06030180c666341b100804020104]
private theorem rowsC6_row006_checked :
    rowsC6_row006.length = 1 ∧ rowsSum 1919 rowsC6_row006 = 41539927 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC6_row007 : List ℕ := [0x8080604026180d8804426180c0643620100824624130c06030180c466361c100804020108884624130986030180c06030180c666341b100804020104]
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
private def rowsC7_row000 : List ℕ := [0x40a080604028180d8804626180c0643620100844624130c06030180c466361c10080402050c884824130a06030180c06030182c666341b100804020106]
private theorem rowsC7_row000_checked :
    rowsC7_row000.length = 1 ∧ rowsSum 1921 rowsC7_row000 = 42158211 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC7_row001 : List ℕ := [0x80c090684430180e0804628180c0663620100864626140c06030180c668362010080402050c8c4824130a06030180c06030182c666341b100804020106]
private theorem rowsC7_row001_checked :
    rowsC7_row001.length = 1 ∧ rowsSum 1922 rowsC7_row001 = 42435804 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC7_row002 : List ℕ := [0x80c0a068443019100804828180c0663820100864826140c06030180c868362010080402090c8c4826130a06030180c06030184c866341b100804020106]
private theorem rowsC7_row002_checked :
    rowsC7_row002.length = 1 ∧ rowsSum 1923 rowsC7_row002 = 42727099 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC7_row003 : List ℕ := [0xc0e0c080483019100844830180c0684020100884826180c06030180c868362010080402090c8c4826130a06030180c06030184c868361b100804020106]
private theorem rowsC7_row003_checked :
    rowsC7_row003.length = 1 ∧ rowsSum 1924 rowsC7_row003 = 42983291 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC7_row004 : List ℕ := [0x10100c08048301a100884c30180c4684020100884826180c06030184c8683620100804020d108c4826130c06030180c06030186c868361b100804020108]
private theorem rowsC7_row004_checked :
    rowsC7_row004.length = 1 ∧ rowsSum 1925 rowsC7_row004 = 43217928 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC7_row005 : List ℕ := [0x810100c0804c301b100884c30180c86c40201048c4826180c06030184cc6836201008040211108c4826130c06030180c06030186c868361c100804020108]
private theorem rowsC7_row005_checked :
    rowsC7_row005.length = 1 ∧ rowsSum 1926 rowsC7_row005 = 43524631 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC7_row006 : List ℕ := [0x814120c08050301b1008c4c30180c86c40201088c4826180c06030188cc6c38201008040211108c4826130c06030180c06030188c868361c100804020108]
private theorem rowsC7_row006_checked :
    rowsC7_row006.length = 1 ∧ rowsSum 1927 rowsC7_row006 = 43833918 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC7_row007 : List ℕ := [0x1018120d08860301c100905030180cc6c40201088c4c28180c0603018ccc6c38201008040211108c4826130c06030180c06030188cc683620100804020108]
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
private def rowsC8_row000 : List ℕ := [0x1818140e088603220100906030180cc70402010c8c4c28180c0603018cd06c40201008040a1910904826140c06030180c0603018ccc683620100804020108]
private theorem rowsC8_row000_checked :
    rowsC8_row000.length = 1 ∧ rowsSum 1929 rowsC8_row000 = 44390104 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC8_row001 : List ℕ := [0x181c1810090603420108906030180d0804020110904c28180c06030190d06c4020100804121918904826140c06030180c0603018ccc683620100804020108]
private theorem rowsC8_row001_checked :
    rowsC8_row001.length = 1 ∧ rowsSum 1930 rowsC8_row001 = 44705169 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC8_row002 : List ℕ := [0x20201810098603420110986030188d0804020110904c30180c06030190d06c4020100804121918904c26140c06030180c0603058ccc68362010080402010c]
private theorem rowsC8_row002_checked :
    rowsC8_row002.length = 1 ∧ rowsSum 1931 rowsC8_row002 = 45006648 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC8_row003 : List ℕ := [0x1028201810098603620110986030190d8804020910904c30180c06030998d06c40201008041a2118904c26140c06030180c0603058ccc68362010080402010c]
private theorem rowsC8_row003_checked :
    rowsC8_row003.length = 1 ∧ rowsSum 1932 rowsC8_row003 = 45312877 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC8_row004 : List ℕ := [0x2030241a100c0603620118986030190d8804021118904c30180c06031198d07040201008041a2118904c26180c06030180c06030990cc68362010080402010c]
private theorem rowsC8_row004_checked :
    rowsC8_row004.length = 1 ∧ rowsSum 1933 rowsC8_row004 = 45547060 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC8_row005 : List ℕ := [0x2030281a110c0604020120a06030198d8804021118985030180c06031198d8704020100804222118904c26180c06030180c06030d90cc68362010080402010c]
private theorem rowsC8_row005_checked :
    rowsC8_row005.length = 1 ∧ rowsSum 1934 rowsC8_row005 = 45856919 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC8_row006 : List ℕ := [0x3038301c120c0644021120c06030198e0804021918985030180c06031998d8704020100804222118904c26180c06030180c06030d90d06c362010080402030c]
private theorem rowsC8_row006_checked :
    rowsC8_row006.length = 1 ∧ rowsSum 1935 rowsC8_row006 = 46164340 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC8_row007 : List ℕ := [0x40403020120c0684021120c060301a100804022120985030180c060319a0d8804020100814322120904c26180c06030180c06031190d06c362010080402030c]
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
private def rowsC9_row000 : List ℕ := [0x2040403020130c0684022130c060311a100804022120986030180c060321a0d8804020100824323120904c28180c06030180c06031190d06c362010080402050c]
private theorem rowsC9_row000_checked :
    rowsC9_row000.length = 1 ∧ rowsSum 1937 rowsC9_row000 = 46752489 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC9_row001 : List ℕ := [0x2050483020140c06c4022130c060321b100804122120986030180c061321a0d8804020100824323120904c28180c06030180c06031198d06c3820100804020510]
private theorem rowsC9_row001_checked :
    rowsC9_row001.length = 1 ∧ rowsSum 1938 rowsC9_row001 = 47081445 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC9_row002 : List ℕ := [0x4060483422180c0704023130c060321b100804223120986030180c061331a0d8804020100834423120984c28180c06030180c06031998d06c3820100804020710]
private theorem rowsC9_row002_checked :
    rowsC9_row002.length = 1 ∧ rowsSum 1939 rowsC9_row002 = 47411477 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC9_row003 : List ℕ := [0x6060503822180c8804024140c060331b100804223130986030180c062331b0e0804020100834423120984c28180c06030180c060b1998d06c4020100804020910]
private theorem rowsC9_row003_checked :
    rowsC9_row003.length = 1 ∧ rowsSum 1940 rowsC9_row003 = 47702936 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC9_row004 : List ℕ := [0x6070604024180c8804224180c060341c100804323130a06030180c063331b0e0804020100844423120984c30180c06030180c060b1998d06c4020100804020910]
private theorem rowsC9_row004_checked :
    rowsC9_row004.length = 1 ∧ rowsSum 1941 rowsC9_row004 = 47947008 := by
  exact c4cCheck (by decide) (by decide) (by decide +kernel)
private def rowsC9_row005 : List ℕ := [0x8080604026180d0804226180c0603420100804424130a06030180c063341b0e0804020100844423120984c30180c06030180c06132198d06c4020100804020910]
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
end
section
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
end
section
namespace K1_14_5
open K1_14 Finset
open scoped BigOperators
private theorem sum_arithmetic (n : ℕ) (a d : ℤ) :
    (∑ t ∈ range n, (a - 2*d*(t : ℤ))) = (n : ℤ)*(a - d*((n : ℤ)-1)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, Nat.cast_succ]; ring
private theorem shape_sum_flip {M : Type} [AddCommMonoid M]
    (s : Shape) (f : ℕ → ℕ → M) :
    (∑ q ∈ range (s.B+1), ∑ j ∈ range (min q s.J+1), f q j) =
      ∑ j ∈ range (s.J+1), ∑ q ∈ Ico j (s.B+1), f q j := by
  calc
    _ = ∑ q ∈ range (s.B+1), ∑ j ∈ range (s.J+1),
        if j ≤ q then f q j else 0 := by
      apply sum_congr rfl
      intro q _
      rw [← sum_filter]
      congr 1
      ext j
      simp only [mem_range, mem_filter, Nat.lt_succ_iff, le_min_iff]
      tauto
    _ = ∑ j ∈ range (s.J+1), ∑ q ∈ range (s.B+1),
        if j ≤ q then f q j else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro j _
      rw [← sum_filter]
      congr 1
      ext q
      simp only [mem_filter, mem_range, mem_Ico]
      tauto
private def nodeRow (k d : ℕ) : ℕ :=
  let n := min k ((d+1)/2)
  n*(d+1-n)
private theorem nodeRow_eq_sum (k d : ℕ) :
    (∑ i ∈ range k, (d-2*i)) = nodeRow k d := by
  let n := min k ((d+1)/2)
  have hnk : n ≤ k := Nat.min_le_left _ _
  have hnd : n ≤ (d+1)/2 := Nat.min_le_right _ _
  have hreduce : (∑ i ∈ range k, (d-2*i)) = ∑ i ∈ range n, (d-2*i) := by
    symm
    apply sum_subset (range_mono hnk)
    intro i hi hni
    simp only [mem_range, not_lt] at hi hni
    have hi' : (d+1)/2 ≤ i := by unfold n at hni; omega
    omega
  have hcast : ((∑ i ∈ range n, (d-2*i) : ℕ) : ℤ) =
      ∑ i ∈ range n, ((d : ℤ)-2*(i : ℤ)) := by
    rw [Nat.cast_sum]
    apply sum_congr rfl
    intro i hi
    have hit := mem_range.mp hi
    rw [Nat.cast_sub (by omega : 2*i ≤ d)]
    push_cast
    rfl
  have hclosed := sum_arithmetic n (d : ℤ) 1
  simp only [mul_one, one_mul] at hclosed
  have hn : n ≤ d+1 := by omega
  apply Int.ofNat_inj.mp
  rw [hreduce, hcast, hclosed]
  change _ = (↑(n*(d+1-n)) : ℤ)
  push_cast [Nat.cast_sub hn]
  ring
def nodeCost (s : Shape) : ℕ :=
  triangle s.U * 262144 *
    ∑ q ∈ range (s.B+1), nodeRow (min q s.J+1) (s.m+min q s.J-q)
def poleSlope (s : Shape) : ℕ :=
  2*(s.U+1) * ∑ q ∈ range (s.B+1), (min q s.J+1)*((s.B+s.J-q)*(s.B-q))
private theorem debit_eq (s : Shape) (h : ℕ) :
    sourceDebit h s = nodeCost s + h * poleSlope s := by
  have hnode : shapeSum s (fun q i => s.m+min q s.J-(q+2*i)) =
      ∑ q ∈ range (s.B+1), nodeRow (min q s.J+1) (s.m+min q s.J-q) := by
    unfold shapeSum
    apply sum_congr rfl
    intro q _
    simpa only [Nat.sub_sub] using nodeRow_eq_sum (min q s.J+1) (s.m+min q s.J-q)
  have hpole : shapeSum s (fun q _ => (s.B+s.J-q)*(s.B-q)) =
      ∑ q ∈ range (s.B+1), (min q s.J+1)*((s.B+s.J-q)*(s.B-q)) := by
    unfold shapeSum
    simp only [sum_const, card_range, Nat.nsmul_eq_mul]
  unfold sourceDebit nodeCost poleSlope
  rw [hnode, hpole]
  ring
end K1_14_5
end
section
namespace K1_13_7_4_2
noncomputable section
open scoped BigOperators Pointwise
section PowerScaling
variable {R ι : Type*} [CommRing R]
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
end
section
namespace K1_13_2_3_4
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
private def bFlag (s q k : ℤ) : Flag :=
  ⟨1650 - 3 * k, s - 1350 - q - 2 * k, 1650 - 3 * k, 550 - k, 1650 - q - 3 * k⟩
private theorem bOld (s q k : ℤ) (hs : 1758 ≤ s) (hs' : s ≤ 1865)
    (hq : 0 ≤ q) (hq' : q ≤ 70) (hk : 0 ≤ k) (hk' : k ≤ 256) :
    oldCount (bFlag s q k) = denominator (1650 - 3 * k) - denominator (s - 1350 - q - 2 * k - 1) := by
  simp (disch := omega) [oldCount, bFlag, bCapLow]
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
private def rowsB1_chunk000 : List ℕ := [
  0x30403022180d0804830180c8704021120986030180c86c4020100864826180c0,
  0x40403422180d8804830180cc804021920986030180c86c4020100884826180c0,
  0x40483424180d8804830180d0804021920986030180cc6c4020100884826180c0,
  0x50483824180e0844c30180d0804022120a06030180cc6c4020102884826180c0]
private theorem rowsB1_chunk000_checked :
    rowsB1_chunk000.length = 4 ∧ rowsSum 1758 rowsB1_chunk000 = 43976193 := by
  constructor
  · rfl
  · rw [bRows_eq 1758 rowsB1_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB1_chunk004 : List ℕ := [
  0x206050402618100844c30180d0804022120a06030180cc6c4020102884826180c0,
  0x406060402818100884c30180d8804022130c06030184d06c4020104884826180c0,
  0x407060403019100885030188d8804023130c06030184d06c40201048c4826180c0,
  0x6080604030191008c5030188d8804123130c06030188d07040201068c4828180c0]
private theorem rowsB1_chunk004_checked :
    rowsB1_chunk004.length = 4 ∧ rowsSum 1762 rowsB1_chunk004 = 45785842 := by
  constructor
  · rfl
  · rw [bRows_eq 1762 rowsB1_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB1_chunk008 : List ℕ := [
  0x60806044301a1008c6030190e0804123130c0603018cd07040201088c4830180c0,
  0x80806844301b100906030198e0804224130c0603018cd08040201088c4c30180c0,
  0xa0907048301b10090603019900804224130c06030190d08040201088c4c30180c0,
  0x40c0a0804c301c1089860301a100804324130c06030190d880402010c8c4c30180c0]
private theorem rowsB1_chunk008_checked :
    rowsB1_chunk008.length = 4 ∧ rowsSum 1766 rowsB1_chunk008 = 47566533 := by
  constructor
  · rfl
  · rw [bRows_eq 1766 rowsB1_chunk008 (by decide) (by decide)]
    decide +kernel
private def rowsB1_chunk012 : List ℕ := [
  0x40c0c0804c30201089860301a100804424140c06030190d880402010c8c4c30180c0,
  0x80c0c0805030201109860301b100804424140c06030198d880402010c8c4c30180c0,
  0xc0e0c080603220110a060311b100804426140c06030198d880402010c904c30180c0]
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
  0xc100c088603420118a060311b100804626180c06030998d8804020110904c30180c0,
  0x10100d088603420120c060321b100824626180c060309a0d8804020510904c30180c0,
  0x10120d090603620120c060321c100824626180c060311a0d8804020510904c30180c0,
  0x814120e090603620120c0603320100844826180c060311a0e0804020910904c30180c0]
private theorem rowsB2_chunk000_checked :
    rowsB2_chunk000.length = 4 ∧ rowsSum 1773 rowsB2_chunk000 = 51174475 := by
  constructor
  · rfl
  · rw [bRows_eq 1773 rowsB2_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB2_chunk004 : List ℕ := [
  0x8181810098604021130c0603420100864826180c060319a0e0804020910904c30180c0,
  0x101818100a0604021130c0603420100864826180c060321a0e0804020d18904c30180c0,
  0x101c18100c0644022130c0603420100884828180c060321b100804021118904c30180c0,
  0x182018100c0644022140c0623620100884828180c060321b100804021118904c30180c0]
private theorem rowsB2_chunk004_checked :
    rowsB2_chunk004.length = 4 ∧ rowsSum 1777 rowsB2_chunk004 = 53211888 := by
  constructor
  · rfl
  · rw [bRows_eq 1777 rowsB2_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB2_chunk008 : List ℕ := [
  0x202018110c0684023140c0623620100884c28180c060331b100804021118904c30180c0,
  0x20241a110c0684024180c06436201008c4c30180c060331b100804021918985030180c0,
  0x1028241c120c06c4024180c06438201048c4c30180c061331b100804021918985030180c0,
  0x10302820130c0704024180c06638201088c4c30180c061331b100804021918986030180c0]
private theorem rowsB2_chunk008_checked :
    rowsB2_chunk008.length = 4 ∧ rowsSum 1781 rowsB2_chunk008 = 55266253 := by
  constructor
  · rfl
  · rw [bRows_eq 1781 rowsB2_chunk008 (by decide) (by decide)]
    decide +kernel
private def rowsB2_chunk012 : List ℕ := [
  0x20303020130c0804226180c0684020108904c30180c062341b100804021920986030180c0,
  0x20383020140c0804226180c068402010c904c30180c062341b1008040a2120986030180c0]
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
  0x30403020180c8804426180c068402010c904c30180c063341c1008040a2120986030180c0,
  0x40403022180d0804628180c46c4020110905030180c064341c100804122120986030180c0,
  0x40483422180d0804628180c46c4020110905030180c0643420100804122120986030180c0,
  0x2050483824180d8804830180c86c4020118985030180c06436201008041a2120986030180c1]
private theorem rowsB3_chunk000_checked :
    rowsB3_chunk000.length = 4 ∧ rowsSum 1787 rowsB3_chunk000 = 58605477 := by
  constructor
  · rfl
  · rw [bRows_eq 1787 rowsB3_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB3_chunk004 : List ℕ := [
  0x2060504026180d8804830180c8704020918986030180c06636201008041a3120986030180c1,
  0x406060402618100844c30180cc704020918986030180c0663620100804223120986030180c2,
  0x407060402818100844c30180d0804021118986030180c2663620100804223120986030180c2,
  0x608060403019100884c30180d0804021920986030180c4683620100804323120986030180c3]
private theorem rowsB3_chunk004_checked :
    rowsB3_chunk004.length = 4 ∧ rowsSum 1791 rowsB3_chunk004 = 60830669 := by
  constructor
  · rfl
  · rw [bRows_eq 1791 rowsB3_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB3_chunk008 : List ℕ := [
  0x808060443019100884c30180d0804021920986030180c4683620100804323120986030180c3,
  0x80906844301a1008c5030188d8804022120986030180c6683620100804323130986030180c4,
  0x40a0906848301b100906030188d8804022120a06030180c6683820100804323130a06030180c4,
  0x40c0a08048301b100906030190d8804022120a06030180c8683820100814424130a06030180c6]
private theorem rowsB3_chunk008_checked :
    rowsB3_chunk008.length = 4 ∧ rowsSum 1795 rowsB3_chunk008 = 63192444 := by
  constructor
  · rfl
  · rw [bRows_eq 1795 rowsB3_chunk008 (by decide) (by decide)]
    decide +kernel
private def rowsB3_chunk012 : List ℕ := [
  0x80c0c0804c301c100906030190e0804123130a06030180c8683820100824424130c06030180c6,
  0x80e0c080503020108986030198e0804123130c06030180c86c4020100824424130c06030180c6]
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
  0xc100c0806032201089860301a100804223130c06030180cc6c4020100834424130c06030180c6,
  0x10100c0886032201109860301a100804224130c06030184cc6c4020100834424130c06030180c8,
  0x10120d088603420118a060301a100804324130c06030184cc6c4020100844624130c06030180c8,
  0x814120d090603420118a060311b100804424130c06030188d06c4020100844624130c06030180c8]
private theorem rowsB4_chunk000_checked :
    rowsB4_chunk000.length = 4 ∧ rowsSum 1801 rowsB4_chunk000 = 66698494 := by
  constructor
  · rfl
  · rw [bRows_eq 1801 rowsB4_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB4_chunk004 : List ℕ := [
  0x8181410090603620120c060311b100804424140c06030188d06c4020100844624130c06030180c8,
  0x10181810098603820120c060321b100804424140c0603018cd06c4020100864624130c06030180c8,
  0x181c18100a0604021130c060331c100824626140c06030190d0704020100864624130c06030180c8,
  0x182018100c0644021130c060331c100824626180c06030190d0704020100864624130c06030180cc]
private theorem rowsB4_chunk004_checked :
    rowsB4_chunk004.length = 4 ∧ rowsSum 1805 rowsB4_chunk004 = 69282112 := by
  constructor
  · rfl
  · rw [bRows_eq 1805 rowsB4_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB4_chunk008 : List ℕ := [
  0x202018110c0644022130c0603420100844626180c06030190d8804020102884626130c06030180cc,
  0x20241a110c0684022130c0603420100844826180c06030198d8804020104884826130c06030180cc,
  0x1030241c120c0684023140c0623620100864826180c06030998d8804020104884826140c06030180cc,
  0x20302820120c06c4024180c0623620100884826180c06030998d8804020106884826140c06030180cc]
private theorem rowsB4_chunk008_checked :
    rowsB4_chunk008.length = 4 ∧ rowsSum 1809 rowsB4_chunk008 = 71729271 := by
  constructor
  · rfl
  · rw [bRows_eq 1809 rowsB4_chunk008 (by decide) (by decide)]
    decide +kernel
private def rowsB4_chunk012 : List ℕ := [
  0x20303020130c0704024180c0643620100884826180c060311a0d8804020106884826180c06030180cc]
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
  0x30383020140c0804224180c0643620100884828180c060311a0d8804020108884826180c06030182cc,
  0x30403020180c8804226180c06638201048c4c28180c060319a0d88040201088c4826180c06030182cc,
  0x40403022180c8804426180c06840201048c4c28180c060321a0e08040201088c4826180c06030184d0,
  0x2050483422180d0804426180c06840201088c4c30180c060321a0e080402010c8c4826180c06030184d0]
private theorem rowsB5_chunk000_checked :
    rowsB5_chunk000.length = 4 ∧ rowsSum 1814 rowsB5_chunk000 = 74964634 := by
  constructor
  · rfl
  · rw [bRows_eq 1814 rowsB5_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB5_chunk004 : List ℕ := [
  0x2060483824180d0804628180c068402010c904c30180c060321b0e080402010c8c4826180c06030186d0,
  0x4060604024180d8804830180c46c402010c904c30180c060331b10080402050c8c4826180c06030186d0,
  0x4070604026180e0804830180c46c4020110904c30180c061331b1008040205108c4826180c06030188d0,
  0x608060402818100804830180c86c4020110904c30180c061331b1008040209108c4c26180c06030188d0]
private theorem rowsB5_chunk004_checked :
    rowsB5_chunk004.length = 4 ∧ rowsSum 1818 rowsB5_chunk004 = 77713468 := by
  constructor
  · rfl
  · rw [bRows_eq 1818 rowsB5_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB5_chunk008 : List ℕ := [
  0x808060403019100844c30180cc704020110905030180c062341b100804020910904c26180c06030188d0,
  0x808068443019100884c30180cc704020918985030180c063341b100804020d10904c28180c0603018cd0,
  0x40a0906844301a100884c30180d0804020918985030180c063341b100804021110904c28180c0603018cd0,
  0x40c0a07048301a1008c5030180d0804021118986030180c064341c100804021118904c28180c0603018cd0]
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
  0x80c0c0804c301b100905030188d8804021920986030180c064341c100804021118904c30180c0603018cd0,
  0xc0e0c0804c301c100906030188d8804021920986030180c064361c100804021918904c30180c06030190d8,
  0xc100c080503020100906030190d8804022120986030180c0663620100804021918904c30180c06030190d8,
  0x10100c080603220108986030190d8804022120986030180c26636201008040a1918904c30180c06030190d8]
private theorem rowsB6_chunk000_checked :
    rowsB6_chunk000.length = 4 ∧ rowsSum 1826 rowsB6_chunk000 = 83124628 := by
  constructor
  · rfl
  · rw [bRows_eq 1826 rowsB6_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB6_chunk004 : List ℕ := [
  0x14120d088603220110986030198e0804123120a06030180c46636201008040a1918904c30180c06030190d8,
  0x818120d0906034201109860301a100804123130a06030180c4683620100804122118904c30180c06030190d8,
  0x10181410090603420118a060301a100804223130a06030180c6683620100804122120984c30180c06030198d8,
  0x10181810098603620120a060311a100804223130c06030180c66836201008041a2120984c30180c06030598d8]
private theorem rowsB6_chunk004_checked :
    rowsB6_chunk004.length = 4 ∧ rowsSum 1830 rowsB6_chunk004 = 86155640 := by
  constructor
  · rfl
  · rw [bRows_eq 1830 rowsB6_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB6_chunk008 : List ℕ := [
  0x18201810098603820120c060311b100804324130c06030180c8683820100804222120984c30180c06030598d8,
  0x202018100c0604021120c060321b100804424130c06030180c8683820100804222120985030180c06030998d8,
  0x202018100c0644021130c060321b100804424130c06030180cc6c3820100804223120985030180c0603099900,
  0x1028241a110c0644022130c060331c100804424130c06030184cc6c4020100804323120985030180c06030d9900]
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
  0x1030281c120c0684022130c0603420100824624140c06030184cc6c4020100804323120986030180c06030d9900,
  0x20303020120c06c4023140c0603420100824626140c06030188cc6c4020100814323120986030180c0603119900,
  0x30383020130c06c4024140c0603420100844626180c0603018cd06c4020100814423120986030180c060311a100,
  0x30403020140c0704024180c0623620100864826180c0603018cd06c4020100824423120986030180c060311a100]
private theorem rowsB7_chunk000_checked :
    rowsB7_chunk000.length = 4 ∧ rowsSum 1838 rowsB7_chunk000 = 91876466 := by
  constructor
  · rfl
  · rw [bRows_eq 1838 rowsB7_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB7_chunk004 : List ℕ := [
  0x40403020180c0804224180c0643620100864826180c06030190d06c4020100834423120986030180c060319a100,
  0x2050483422180c8804226180c0643620100884826180c06030190d0704020100834424130986030180c060319a100,
  0x2060483422180d0804426180c0663820100884826180c06030198d0704020100844424130986030180c060319a100,
  0x4060503824180d0804626180c06838201048c4828180c06030998d8704020100844424130986030180c060321a100]
private theorem rowsB7_chunk004_checked :
    rowsB7_chunk004.length = 4 ∧ rowsSum 1842 rowsB7_chunk004 = 95136682 := by
  constructor
  · rfl
  · rw [bRows_eq 1842 rowsB7_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB7_chunk008 : List ℕ := [
  0x6070604026180d8804628180c06840201048c4c28180c06030998d8804020100844624130986030180c060321a100,
  0x6080604026180d8804830180c06840201088c4c28180c06031198d8804020100864624130a06030180c060321a100,
  0x808060402818100804830180c46c40201088c4c30180c060319a0d8804020102864624130a06030180c060321a100]
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
  0x808060403019100844c30180c86c402010c904c30180c060319a0d8804020102864624130a06030180c060321a100,
  0x40c09068443019100844c30180c86c4020110904c30180c060321a0d8804020104884624130c06030180c060b21a100,
  0x80c0a07048301a100884c30180cc704020110904c30180c060321a0e0804020104884624130c06030180c061331b100,
  0x80c0c08048301a1008c4c30180d0704020110904c30180c060321a0e0804020106884624130c06030180c061331b100]
private theorem rowsB8_chunk000_checked :
    rowsB8_chunk000.length = 4 ∧ rowsSum 1849 rowsB8_chunk000 = 100580370 := by
  constructor
  · rfl
  · rw [bRows_eq 1849 rowsB8_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB8_chunk004 : List ℕ := [
  0xc0e0c0804c301b1008c5030180d0804020918905030180c061331b0e0804020108884826130c06030180c061b31b100,
  0x10100c08050301c100906030188d0804021118985030180c061331b100804020108884826130c06030180c061b31b100,
  0x10100c080603020100906030188d8804021118985030180c062331b1008040201088c4826130c06030180c062331b100,
  0x814120d088603220108986030190d8804021920986030180c063341b10080402010c8c4826130c06030180c062331b100]
private theorem rowsB8_chunk004_checked :
    rowsB8_chunk004.length = 4 ∧ rowsSum 1853 rowsB8_chunk004 = 103896094 := by
  constructor
  · rfl
  · rw [bRows_eq 1853 rowsB8_chunk004 (by decide) (by decide)]
    decide +kernel
private def rowsB8_chunk008 : List ℕ := [
  0x1018120d088603420110986030190d8804022120986030180c063341b10080402050c8c4826140c06030180c062331b100,
  0x10181810090603420110986030198e0804022120986030180c064341b10080402050c8c4826140c06030180c063341b100,
  0x181c1810098603620118a060301a0e0804022120986030180c064341b1008040209108c4826140c06030180c063341b100]
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
  0x18201810098603620120a060301a100804123120a06030180c064341c1008040209108c4826140c06030180c063341b100,
  0x202018100a0604020120c060311a100804223130a06030180c266361c100804020d108c4826180c06030180c064341b100,
  0x1028241a110c0644021120c060311b100804223130a06030180c2663620100804021110904826180c06030180c064341b100,
  0x1030241a110c0644021130c060321b100804324130c06030180c4663620100804021110904c26180c06030180c064341b100]
private theorem rowsB9_chunk000_checked :
    rowsB9_chunk000.length = 4 ∧ rowsSum 1860 rowsB9_chunk000 = 109742129 := by
  constructor
  · rfl
  · rw [bRows_eq 1860 rowsB9_chunk000 (by decide) (by decide)]
    decide +kernel
private def rowsB9_chunk004 : List ℕ := [
  0x2030281c120c0684022130c060331b100804324130c06030180c6683620100804021110904c26180c06030180c1643420100,
  0x30383020130c06c4023130c060331c100804424130c06030180c6683620100804021918904c26180c06030180c1643420100]
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
end
section
namespace K1_13_2_3_4
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0
open K1_13_2
private theorem ddDenNeg {v : ℤ} (hv : v < 0) : denominator v = 0 := by
  simp [denominator, hv]
private theorem ddCumNeg {d v : ℤ} (hv : v < 0) : cumulative d v = 0 := by
  simp [cumulative, hv]
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
private def ddDenNat (u : ℕ) : ℕ := (((2 * u + 21) * u + 66) * u + 72) / 72
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
private def rowsD1_row1943 : List ℕ := [
  0x40a080604026180d8804426180c0623420100804424130c06030180c064341b100804020102864423120984c30180c06030180c06132198d06c4020100804020d10]
private theorem rowsD1_row1943_checked :
    rowsD1_row1943.length = 1 ∧ rowsSum 1943 rowsD1_row1943 = 48532032 := ddSingle (by decide +kernel)
private def rowsD1_row1944 : List ℕ := [
  0x80c090604028180d8804626180c0643620100824424130c06030180c064341b100804020102864624120984c30180c06030180c061b2198d06c4020100804020d10]
private theorem rowsD1_row1944_checked :
    rowsD1_row1944.length = 1 ∧ rowsSum 1944 rowsD1_row1944 = 48859683 := ddSingle (by decide +kernel)
private def rowsD1_row1945 : List ℕ := [
  0x80c0a0684430180e0804628180c0643620100844624130c06030180c266341b100804020104864624120985030180c06030180c062321a0d86c4020100804020d10]
private theorem rowsD1_row1945_checked :
    rowsD1_row1945.length = 1 ∧ rowsSum 1945 rowsD1_row1945 = 49189053 := ddSingle (by decide +kernel)
private def rowsD1_row1946 : List ℕ := [
  0xc0e0c070443019100804828180c0663620100844624130c06030180c466341b100804020106884624130985030180c06030180c062321a0d86c4020100804020d10]
private theorem rowsD1_row1946_checked :
    rowsD1_row1946.length = 1 ∧ rowsSum 1946 rowsD1_row1946 = 49521319 := ddSingle (by decide +kernel)
private def rowsD1_row1947 : List ℕ := [
  0x10100c080483019100844830180c0683820100864626140c06030180c466361c100804020106884624130985030180c06030180c062331a0d86c4020100804021110]
private theorem rowsD1_row1947_checked :
    rowsD1_row1947.length = 1 ∧ rowsSum 1947 rowsD1_row1947 = 49852962 := ddSingle (by decide +kernel)
private def rowsD1_row1948 : List ℕ := [
  0x810100c0804c301a100884c30180c0684020100884826140c06030180c666361c100804020108884624130985030180c06030180c063331a0d86c4020100804021110]
private theorem rowsD1_row1948_checked :
    rowsD1_row1948.length = 1 ∧ rowsSum 1948 rowsD1_row1948 = 50188791 := ddSingle (by decide +kernel)
private def rowsD1_row1949 : List ℕ := [
  0x814120c0804c301b100884c30180c4684020100884826180c06030180c8683620100804020108884624130986030180c06030180c163331a0d8704020100804021110]
private theorem rowsD1_row1949_checked :
    rowsD1_row1949.length = 1 ∧ rowsSum 1949 rowsD1_row1949 = 50412605 := ddSingle (by decide +kernel)
private def rowsD1_row1950 : List ℕ := [
  0x1018120d08060301b1008c4c30180c86c4020104884826180c06030180c868362010080402050c884624130986030180c06030180c163331a0d8704020100804021118]
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
  0x1818140d088603020100905030180c86c40201088c4826180c06030184c868362010080402090c8c4824130986030180c06030180c264331a0d8704020100804021118]
private theorem rowsD2_row1951_checked :
    rowsD2_row1951.length = 1 ∧ rowsSum 1951 rowsD2_row1951 = 51076092 := ddSingle (by decide +kernel)
private def rowsD2_row1952 : List ℕ := [
  0x181c1810090603220100905030180cc6c40201088c4826180c06030184cc68362010080402090c8c4824130a06030180c06030180c264331a0d8804020100804061118]
private theorem rowsD2_row1952_checked :
    rowsD2_row1952.length = 1 ∧ rowsSum 1952 rowsD2_row1952 = 51364774 := ddSingle (by decide +kernel)
private def rowsD2_row1953 : List ℕ := [
  0x20201810090603420108906030180d070402010c8c4c28180c06030188cc6c3820100804020d108c4826130a06030180c06030180c364331a0d8804020100804061918]
private theorem rowsD2_row1953_checked :
    rowsD2_row1953.length = 1 ∧ rowsSum 1953 rowsD2_row1953 = 51696017 := ddSingle (by decide +kernel)
private def rowsD2_row1954 : List ℕ := [
  0x1028201810098603420110986030188d0804020110904c28180c0603018ccc6c3820100804020d108c4826130a06030180c06030180c464341a0d88040201008040a1918]
private theorem rowsD2_row1954_checked :
    rowsD2_row1954.length = 1 ∧ rowsSum 1954 rowsD2_row1954 = 52031837 := ddSingle (by decide +kernel)
private def rowsD2_row1955 : List ℕ := [
  0x2030241a100a0603620110986030188d8804020110904c28180c0603018cd06c38201008040211108c4826130a06030180c06030180c464341b0d88040201008040a1918]
private theorem rowsD2_row1955_checked :
    rowsD2_row1955.length = 1 ∧ rowsSum 1955 rowsD2_row1955 = 52377791 := ddSingle (by decide +kernel)
private def rowsD2_row1956 : List ℕ := [
  0x2030281a110c0603820118986030190d8804020910904c30180c06030190d06c40201008040211108c4826130c06030180c06030180c464341b0d88040201008040e1918]
private theorem rowsD2_row1956_checked :
    rowsD2_row1956.length = 1 ∧ rowsSum 1956 rowsD2_row1956 = 52601764 := ddSingle (by decide +kernel)
private def rowsD2_row1957 : List ℕ := [
  0x3038301c110c0644020120a06030198d8804021118904c30180c06030990d06c40201008040a19108c4826130c06030180c06030180c666341b0d88040201008040e1918]
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
  0x40403020120c0644021120c06030198e0804021118904c30180c06030998d06c4020100804121918904826130c06030180c06030182c666341b0d8804020100804121918]
private theorem rowsD3_row1958_checked :
    rowsD3_row1958.length = 1 ∧ rowsSum 1958 rowsD3_row1958 = 53310127 := ddSingle (by decide +kernel)
private def rowsD3_row1959 : List ℕ := [
  0x2040403020130c0684021130c060301a0e0804021918985030180c06031198d06c4020100804121918904826140c06030180c06030182c666341b0e0804020100804121918]
private theorem rowsD3_row1959_checked :
    rowsD3_row1959.length = 1 ∧ rowsSum 1959 rowsD3_row1959 = 53653364 := ddSingle (by decide +kernel)
private def rowsD3_row1960 : List ℕ := [
  0x2060483020130c06c4022130c060311a100804022120985030180c06031998d87040201008041a2118904826140c06030180c06030184c866341b0e08040201008041a2118]
private theorem rowsD3_row1960_checked :
    rowsD3_row1960.length = 1 ∧ rowsSum 1960 rowsD3_row1960 = 53987134 := ddSingle (by decide +kernel)
private def rowsD3_row1961 : List ℕ := [
  0x4060483420180c06c4023130c060311b100804022120985030180c060319a0d8704020100804222118904c26140c06030180c06030186c866341b0e08040201008041a2118]
private theorem rowsD3_row1961_checked :
    rowsD3_row1961.length = 1 ∧ rowsSum 1961 rowsD3_row1961 = 54330098 := ddSingle (by decide +kernel)
private def rowsD3_row1962 : List ℕ := [
  0x6060503822180c0804023140c060321b100804122120986030180c060321a0d8804020100804222118904c26140c06030180c06030186c866341b1008040201008041a2118]
private theorem rowsD3_row1962_checked :
    rowsD3_row1962.length = 1 ∧ rowsSum 1962 rowsD3_row1962 = 54579573 := ddSingle (by decide +kernel)
private def rowsD3_row1963 : List ℕ := [
  0x6080604024180c8804024140c060331b100804223120986030180c061321a0d8804020100814222118904c26140c06030180c06030188c866341b1008040201008041a2118]
private theorem rowsD3_row1963_checked :
    rowsD3_row1963.length = 1 ∧ rowsSum 1963 rowsD3_row1963 = 54934116 := ddSingle (by decide +kernel)
private def rowsD3_row1964 : List ℕ := [
  0x408080604024180d0804224180c060331c100804223130986030180c061331a0d8804020100814322118904c26180c06030180c06030188c868341b100804020100804222118]
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
  0x40a080604026180d0804426180c060341c100804323130a06030180c062331a0d8804020100824323120904c26180c06030180c06030188cc68361b100804020100804222120]
private theorem rowsD4_row1965_checked :
    rowsD4_row1965.length = 1 ∧ rowsSum 1965 rowsD4_row1965 = 55576301 := ddSingle (by decide +kernel)
private def rowsD4_row1966 : List ℕ := [
  0x80c090684028180d8804426180c0623420100804424130a06030180c062331b0e0804020100834323120904c26180c06030180c0603058ccc68361b100804020100804222120]
private theorem rowsD4_row1966_checked :
    rowsD4_row1966.length = 1 ∧ rowsSum 1966 rowsD4_row1966 = 55938580 := ddSingle (by decide +kernel)
private def rowsD4_row1967 : List ℕ := [
  0xc0c0a0684430180e0804626180c0643620100824424130c06030180c063331b0e0804020100834423120904c28180c06030180c0603058ccc68361b10080402010080c222120]
private theorem rowsD4_row1967_checked :
    rowsD4_row1967.length = 1 ∧ rowsSum 1967 rowsD4_row1967 = 56277297 := ddSingle (by decide +kernel)
private def rowsD4_row1968 : List ℕ := [
  0xc0e0c070483019100804828180c0643620100824624130c06030180c064341b0e0804020100844423120984c28180c06030180c0603098ccc68361b10080402010080c222120]
private theorem rowsD4_row1968_checked :
    rowsD4_row1968.length = 1 ∧ rowsSum 1968 rowsD4_row1968 = 56624711 := ddSingle (by decide +kernel)
private def rowsD4_row1969 : List ℕ := [
  0x10100c080483019100844830180c0663620100844624130c06030180c064341b100804020100844423120984c28180c06030180c06030990cc68361c100804020100814222120]
private theorem rowsD4_row1969_checked :
    rowsD4_row1969.length = 1 ∧ rowsSum 1969 rowsD4_row1969 = 56945987 := ddSingle (by decide +kernel)
private def rowsD4_row1970 : List ℕ := [
  0x814100c0804c301a100844c30180c0683820100864626130c06030180c264341b100804020102864423120984c28180c06030180c06030d90cc68361c100804020100814322120]
private theorem rowsD4_row1970_checked :
    rowsD4_row1970.length = 1 ∧ rowsSum 1970 rowsD4_row1970 = 57303937 := ddSingle (by decide +kernel)
private def rowsD4_row1971 : List ℕ := [
  0x1018120c08050301b100884c30180c4684020100864626140c06030180c466341b100804020104864423120984c30180c06030180c06031190cc68361c10080402010081c323120]
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
  0x1018120d08860301b1008c4c30180c46c4020100884826140c06030180c466361c100804020104864624120984c30180c06030180c06031190d0683620100804020100824323120]
private theorem rowsD5_row1972_checked :
    rowsD5_row1972.length = 1 ∧ rowsSum 1972 rowsD5_row1972 = 57898819 := ddSingle (by decide +kernel)
private def rowsD5_row1973 : List ℕ := [
  0x181c180e0886032201008c4c30180c86c4020104884826180c06030180c666361c100804020106864624120984c30180c06030180c06031190d0683620100804020100824323120]
private theorem rowsD5_row1973_checked :
    rowsD5_row1973.length = 1 ∧ rowsSum 1973 rowsD5_row1973 = 58241930 := ddSingle (by decide +kernel)
private def rowsD5_row1974 : List ℕ := [
  0x20201810090603220100905030180cc6c40201048c4826180c06030180c868361c100804020106884624130985030180c06030180c060b1998d06c3620100804020100824323120]
private theorem rowsD5_row1974_checked :
    rowsD5_row1974.length = 1 ∧ rowsSum 1974 rowsD5_row1974 = 58621160 := ddSingle (by decide +kernel)
private def rowsD5_row1975 : List ℕ := [
  0x1020201810098603420108906030180cc6c40201088c4826180c06030180c8683620100804020108884624130985030180c06030180c060b1998d06c3620100804020100834323120]
private theorem rowsD5_row1975_checked :
    rowsD5_row1975.length = 1 ∧ rowsSum 1975 rowsD5_row1975 = 58973106 := ddSingle (by decide +kernel)
private def rowsD5_row1976 : List ℕ := [
  0x2030241810098603620110986030180d070402010c8c4c28180c06030184c8683620100804020508884624130985030180c06030180c06131998d06c3620100804020100834323120]
private theorem rowsD5_row1976_checked :
    rowsD5_row1976.length = 1 ∧ rowsSum 1976 rowsD5_row1976 = 59337501 := ddSingle (by decide +kernel)
private def rowsD5_row1977 : List ℕ := [
  0x2030241a100c0603620110986030188d080402010c904c28180c06030188cc68362010080402050c884624130985030180c06030180c06132198d06c3620100804020100834423180]
private theorem rowsD5_row1977_checked :
    rowsD5_row1977.length = 1 ∧ rowsSum 1977 rowsD5_row1977 = 59662769 := ddSingle (by decide +kernel)
private def rowsD5_row1978 : List ℕ := [
  0x3030281c110c0603820118986030190d8804020110904c28180c06030188cc6c382010080402090c8c4824130986030180c06030180c061b2198d06c3620100804020100834423180]
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
  0x40403020120c0644020120a06030190d8804020910904c30180c0603018ccc6c3820100804020d0c8c4824130986030180c06030180c06232198d06c3820100804020100844423180]
private theorem rowsD6_row1979_checked :
    rowsD6_row1979.length = 1 ∧ rowsSum 1979 rowsD6_row1979 = 60292859 := ddSingle (by decide +kernel)
private def rowsD6_row1980 : List ℕ := [
  0x2040403020120c0684021120c06030198d8804021118904c30180c06030190d06c3820100804020d108c4824130986030180c06030180c06232198d06c3820100804020101844423180]
private theorem rowsD6_row1980_checked :
    rowsD6_row1980.length = 1 ∧ rowsSum 1980 rowsD6_row1980 = 60662595 := ddSingle (by decide +kernel)
private def rowsD6_row1981 : List ℕ := [
  0x2050403020130c0684021130c060301a0e0804021118904c30180c06030190d06c40201008040211108c4826130a06030180c06030180c062321a0d06c3820100804020101844423180]
private theorem rowsD6_row1981_checked :
    rowsD6_row1981.length = 1 ∧ rowsSum 1981 rowsD6_row1981 = 61019904 := ddSingle (by decide +kernel)
private def rowsD6_row1982 : List ℕ := [
  0x4060483420140c06c4022130c060311a0e0804021918985030180c06030990d06c40201008040211108c4826130a06030180c06030180c163331a0d06c4020100804020102844423180]
private theorem rowsD6_row1982_checked :
    rowsD6_row1982.length = 1 ∧ rowsSum 1982 rowsD6_row1982 = 61356710 := ddSingle (by decide +kernel)
private def rowsD6_row1983 : List ℕ := [
  0x6060503422180c0704023130c060311a100804022120985030180c06031198d06c40201008040a19108c4826130a06030180c06030180c163331a0d86c4020100804020102844423180]
private theorem rowsD6_row1983_checked :
    rowsD6_row1983.length = 1 ∧ rowsSum 1983 rowsD6_row1983 = 61740488 := ddSingle (by decide +kernel)
private def rowsD6_row1984 : List ℕ := [
  0x6070604024180c8804023140c060321b100804122120985030180c06031198d86c40201008041219108c4826130a06030180c06030180c263331a0d86c4020100804020103864423180]
private theorem rowsD6_row1984_checked :
    rowsD6_row1984.length = 1 ∧ rowsSum 1984 rowsD6_row1984 = 62116571 := ddSingle (by decide +kernel)
private def rowsD6_row1985 : List ℕ := [
  0x408080604024180c8804224140c060331b100804122120986030180c06031998d8704020100804121918904826130c06030180c06030180c264331a0d86c4020100804020104864423180]
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
  0x40a080604026180d0804224180c060331b100804223120986030180c060321a0d87040201008041a1918904826130c06030180c06030180c364331a0d86c4020100804020104864424180]
private theorem rowsD7_row1986_checked :
    rowsD7_row1986.length = 1 ∧ rowsSum 1986 rowsD7_row1986 = 62750730 := ddSingle (by decide +kernel)
private def rowsD7_row1987 : List ℕ := [
  0x80c090684028180d8804426180c060341c100804323120986030180c060321a0d8804020100804222118904826140c06030180c06030180c464331a0d8704020100804020104864424180]
private theorem rowsD7_row1987_checked :
    rowsD7_row1987.length = 1 ∧ rowsSum 1987 rowsD7_row1987 = 63106578 := ddSingle (by decide +kernel)
private def rowsD7_row1988 : List ℕ := [
  0xc0c0a0684430180d8804626180c0623420100804323130a06030180c061321a0d8804020100804222118904c26140c06030180c06030180c464331a0d8704020100804020106864624180]
private theorem rowsD7_row1988_checked :
    rowsD7_row1988.length = 1 ∧ rowsSum 1988 rowsD7_row1988 = 63484853 := ddSingle (by decide +kernel)
private def rowsD7_row1989 : List ℕ := [
  0xc0e0c070443018100804626180c0643620100804424130a06030180c062331a0d8804020100814222118904c26140c06030180c06030180c464341a0d8704020100804020106864624180]
private theorem rowsD7_row1989_checked :
    rowsD7_row1989.length = 1 ∧ rowsSum 1989 rowsD7_row1989 = 63874545 := ddSingle (by decide +kernel)
private def rowsD7_row1990 : List ℕ := [
  0x10100c080483019100804828180c0643620100824424130a06030180c062331b0d8804020100814322118904c26140c06030180c06030182c666341a0d8704020100804020106864624180]
private theorem rowsD7_row1990_checked :
    rowsD7_row1990.length = 1 ∧ rowsSum 1990 rowsD7_row1990 = 64269789 := ddSingle (by decide +kernel)
private def rowsD7_row1991 : List ℕ := [
  0x814100c0804c301a100844830180c0663620100844624130c06030180c063331b0e0804020100824323120904c26140c06030180c06030182c666341b0d8804020100804020106884624180]
private theorem rowsD7_row1991_checked :
    rowsD7_row1991.length = 1 ∧ rowsSum 1991 rowsD7_row1991 = 64582414 := ddSingle (by decide +kernel)
private def rowsD7_row1992 : List ℕ := [
  0x1018120c0804c301b100884c30180c0683820100844624130c06030180c064341b0e0804020100834323120904c26180c06030180c06030184c666341b0d8804020100804020308884624180]
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
  0x1818140d08860301b100884c30180c4683820100864626130c06030180c264341b100804020100834423120904c26180c06030180c06030186c866341b0d8804020100804020308884624180]
private theorem rowsD8_row1993_checked :
    rowsD8_row1993.length = 1 ∧ rowsSum 1993 rowsD8_row1993 = 65248059 := ddSingle (by decide +kernel)
private def rowsD8_row1994 : List ℕ := [
  0x181c180e08860301c1008c4c30180c4684020100884826140c06030180c266341b100804020100844423120984c28180c06030180c06030186c866341b0d8804020100804020508884624180]
private theorem rowsD8_row1994_checked :
    rowsD8_row1994.length = 1 ∧ rowsSum 1994 rowsD8_row1994 = 65628090 := ddSingle (by decide +kernel)
private def rowsD8_row1995 : List ℕ := [
  0x20201810090603220100905030180c86c4020104884826140c06030180c466341b100804020102844423120984c28180c06030180c06030188c866341b0d8804020100804020508884624180]
private theorem rowsD8_row1995_checked :
    rowsD8_row1995.length = 1 ∧ rowsSum 1995 rowsD8_row1995 = 66018413 := ddSingle (by decide +kernel)
private def rowsD8_row1996 : List ℕ := [
  0x1028201810098603420108905030180cc6c4020104884826180c06030180c666361b100804020102864423120984c28180c06030180c06030188c866341b0e0804020100804020708884624180]
private theorem rowsD8_row1996_checked :
    rowsD8_row1996.length = 1 ∧ rowsSum 1996 rowsD8_row1996 = 66385371 := ddSingle (by decide +kernel)
private def rowsD8_row1997 : List ℕ := [
  0x2030241810098603420108986030180cc6c40201088c4826180c06030180c666361c100804020104864423120984c28180c06030180c06030188c868341b0e080402010080402090c884624180]
private theorem rowsD8_row1997_checked :
    rowsD8_row1997.length = 1 ∧ rowsSum 1997 rowsD8_row1997 = 66779004 := ddSingle (by decide +kernel)
private def rowsD8_row1998 : List ℕ := [
  0x2030241a100a0603620110986030180d07040201088c4826180c06030180c868361c100804020106864624120984c30180c06030180c0603058ccc68341b0e080402010080402090c884624180]
private theorem rowsD8_row1998_checked :
    rowsD8_row1998.length = 1 ∧ rowsSum 1998 rowsD8_row1998 = 67102115 := ddSingle (by decide +kernel)
private def rowsD8_row1999 : List ℕ := [
  0x3038301c110c0603820118986030188d080402010c8c4c28180c06030184c8683620100804020106884624120984c30180c06030180c0603098ccc68361b10080402010080402090c884624180]
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
  0x40403020120c0644020118a06030190d8804020110904c28180c06030184cc683620100804020108884624120984c30180c06030180c0603098ccc68361b100804020100804020d0c884624180]
private theorem rowsD9_row2000_checked :
    rowsD9_row2000.length = 1 ∧ rowsSum 2000 rowsD9_row2000 = 67821210 := ddSingle (by decide +kernel)
private def rowsD9_row2001 : List ℕ := [
  0x2050403020120c0684021120a06030190d8804020910904c28180c06030188cc683620100804020508884624130985030180c06030180c06030d90cc68361b100804020100804020d0c884624180]
private theorem rowsD9_row2001_checked :
    rowsD9_row2001.length = 1 ∧ rowsSum 2001 rowsD9_row2001 = 68213984 := ddSingle (by decide +kernel)
private def rowsD9_row2002 : List ℕ := [
  0x4060483020130c0684021120c06030198d8804021118904c30180c0603018ccc6c382010080402050c884624130985030180c06030180c06030d90cc68361b100804020100804020d0c8c4624180]
private theorem rowsD9_row2002_checked :
    rowsD9_row2002.length = 1 ∧ rowsSum 2002 rowsD9_row2002 = 68573887 := ddSingle (by decide +kernel)
private def rowsD9_row2003 : List ℕ := [
  0x4060483420140c06c4022130c060301a0e0804021118904c30180c0603018cd06c382010080402090c884624130985030180c06030180c06031190cc68361b100804020100804060d0c8c4824180]
private theorem rowsD9_row2003_checked :
    rowsD9_row2003.length = 1 ∧ rowsSum 2003 rowsD9_row2003 = 68976045 := ddSingle (by decide +kernel)
private def rowsD9_row2004 : List ℕ := [
  0x6070603822180c0704023130c060311a100804021918984c30180c06030190d06c3820100804020d0c8c4824130985030180c06030180c06031190cc68361b1008040201008040611108c4824180]
private theorem rowsD9_row2004_checked :
    rowsD9_row2004.length = 1 ∧ rowsSum 2004 rowsD9_row2004 = 69370983 := ddSingle (by decide +kernel)
private def rowsD9_row2005 : List ℕ := [
  0x8080604024180c8804023130c060321b100804022120985030180c06030990d06c4020100804020d108c4824130986030180c06030180c060b1990d068361c1008040201008040a11108c4824180]
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
  0x408080604024180c8804024140c060321b100804122120985030180c06031198d06c40201008040211108c4824130986030180c06030180c060b1998d068361c1008040201008040a11108c4824180]
private theorem rowsD10_row2006_checked :
    rowsD10_row2006.length = 1 ∧ rowsSum 2006 rowsD10_row2006 = 70092207 := ddSingle (by decide +kernel)
private def rowsD10_row2007 : List ℕ := [
  0x80c090604026180d0804224180c060331b100804122120986030180c06031198d06c40201008040a11108c4826130a06030180c06030180c06131998d06c361c1008040201008040e11108c4824180]
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
end
section
namespace K1_14_4
open K1_14 Finset
def gradeWidth (k B W j : ℕ) : ℕ :=
  min (B + 1) ((W + j) / k + 1) - j
def gradeCapacity (w : ℤ) (W j : ℕ) : ℕ :=
  let b := band w
  gradeWidth (131071 - w.toNat) b.jetBound W j *
    slots b.subbankSeeds (forcedPower w W j * (b.seedBound + 1))
end K1_14_4
end
