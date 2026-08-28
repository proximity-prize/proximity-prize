import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.NormalizedPlaceEquivalence
import ProximityPrize.SubmissionLower.CoordinatePoleMass

/-!
# The unique pole in the small purely inseparable projection

For a purely inseparable rational-function projection, every normalized
place at which the projected coordinate has a pole lies over the same
infinity valuation.  Purely inseparable valuation uniqueness then makes
that pole unique.
-/

namespace ProximityPrize.SubmissionLower.SmallPurelyInseparablePole

open scoped Classical BigOperators WithZero

noncomputable section

open CoordinatePlaceClassification

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

abbrev Place := NormalizedValuation K L

/-- Two common normalized places at which the same purely inseparable
coordinate has a pole must coincide. -/
theorem place_eq_of_coordinate_poles
    (p : ℕ) [ExpChar K p] (hp : p.Prime)
    (c : RatFunc K →ₐ[K] L)
    (hpure : letI : Algebra (RatFunc K) L := c.toRingHom.toAlgebra
      IsPurelyInseparable (RatFunc K) L)
    (v w : Place K L)
    (hv : 1 < v.val (c RatFunc.X))
    (hw : 1 < w.val (c RatFunc.X)) : v = w := by
  letI : Algebra (RatFunc K) L := c.toRingHom.toAlgebra
  letI : IsPurelyInseparable (RatFunc K) L := hpure
  let v₀ : Valuation (RatFunc K) ℤᵐ⁰ := v.val.comap c.toRingHom
  let w₀ : Valuation (RatFunc K) ℤᵐ⁰ := w.val.comap c.toRingHom
  letI : v₀.IsTrivialOn K := by
    refine ⟨fun a ha ↦ ?_⟩
    change v.val (c (algebraMap K (RatFunc K) a)) = 1
    rw [c.commutes]
    exact v.property.2.eq_one a ha
  letI : w₀.IsTrivialOn K := by
    refine ⟨fun a ha ↦ ?_⟩
    change w.val (c (algebraMap K (RatFunc K) a)) = 1
    rw [c.commutes]
    exact w.property.2.eq_one a ha
  have hv₀ : 1 < v₀ RatFunc.X := hv
  have hw₀ : 1 < w₀ RatFunc.X := hw
  have hbase : v₀.IsEquiv w₀ :=
    PurelyInseparableValuation.RatFunc.isEquiv_of_one_lt_X v₀ w₀ hv₀ hw₀
  have hplaces : v.val.IsEquiv w.val :=
    PurelyInseparableValuation.isEquiv_of_isPurelyInseparable
      p hp v.val w.val hbase
  exact NormalizedPlaceEquivalence.eq_of_isEquiv K L v w hplaces

/-- A finite set of poles of a purely inseparable coordinate contains at
most one normalized place. -/
theorem card_pole_places_le_one
    (p : ℕ) [ExpChar K p] (hp : p.Prime)
    (c : RatFunc K →ₐ[K] L)
    (hpure : letI : Algebra (RatFunc K) L := c.toRingHom.toAlgebra
      IsPurelyInseparable (RatFunc K) L)
    (W : Finset (Place K L))
    (hW : ∀ v ∈ W, 1 < v.val (c RatFunc.X)) : W.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro v hv w hw
  exact place_eq_of_coordinate_poles K L p hp c hpure v w
    (hW v hv) (hW w hw)

/-- The unique pole order is at most the degree-`p` extension degree.
Choose an upstairs element of normalized value `exp 1`.  Its purely
inseparable minimal polynomial has degree `p^n ≤ p`; comparing values
in its equation shows that the coordinate pole order divides `p^n`. -/
theorem poleOrder_le_prime
    (p : ℕ) [ExpChar K p] (hp : p.Prime)
    (c : RatFunc K →ₐ[K] L)
    (hfinite : letI : Algebra (RatFunc K) L := c.toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L)
    (hpure : letI : Algebra (RatFunc K) L := c.toRingHom.toAlgebra
      IsPurelyInseparable (RatFunc K) L)
    (hdegree : letI : Algebra (RatFunc K) L := c.toRingHom.toAlgebra
      Module.finrank (RatFunc K) L = p)
    (v : Place K L) (hv : 1 < v.val (c RatFunc.X)) :
    CoordinatePoleMass.poleOrder K L v (c RatFunc.X) ≤ (p : ℤ) := by
  letI : Algebra (RatFunc K) L := c.toRingHom.toAlgebra
  letI : FiniteDimensional (RatFunc K) L := hfinite
  letI : IsPurelyInseparable (RatFunc K) L := hpure
  let v₀ : Valuation (RatFunc K) ℤᵐ⁰ := v.val.comap c.toRingHom
  letI : v₀.IsTrivialOn K := by
    refine ⟨fun a ha ↦ ?_⟩
    change v.val (c (algebraMap K (RatFunc K) a)) = 1
    rw [c.commutes]
    exact v.property.2.eq_one a ha
  have hv₀ : 1 < v₀ RatFunc.X := hv
  obtain ⟨u, hu⟩ := v.property.1 (WithZero.exp (1 : ℤ))
  have hu0 : u ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hu
    exact WithZero.exp_ne_zero hu.symm
  obtain ⟨n, a, hmin⟩ :=
    IsPurelyInseparable.minpoly_eq_X_pow_sub_C (RatFunc K) p u
  let N : ℕ := p ^ n
  have hNpos : 0 < N := pow_pos hp.pos n
  have hrel : u ^ N = c a := by
    have hzero := minpoly.aeval (RatFunc K) u
    rw [hmin] at hzero
    change u ^ (p ^ n) = c a
    rw [Polynomial.aeval_sub, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, sub_eq_zero] at hzero
    exact hzero
  have ha0 : a ≠ 0 := by
    intro hzero
    have : u ^ N = 0 := by simpa [hzero] using hrel
    exact (pow_ne_zero N hu0) this
  have hNdegree : N = (minpoly (RatFunc K) u).natDegree := by
    rw [hmin, Polynomial.natDegree_sub_C, Polynomial.natDegree_X_pow]
  have hNle : N ≤ p := by
    calc
      N = (minpoly (RatFunc K) u).natDegree := hNdegree
      _ ≤ Module.finrank (RatFunc K) L := minpoly.natDegree_le u
      _ = p := hdegree
  have hbase :=
    PurelyInseparableValuation.RatFunc.value_eq_X_zpow_intDegree_of_one_lt_X
      (v := v₀) hv₀ ha0
  have hvalue : v.val (c RatFunc.X) ^ a.intDegree = v.val u ^ N := by
    calc
      v.val (c RatFunc.X) ^ a.intDegree = v₀ a := hbase.symm
      _ = v.val (c a) := rfl
      _ = v.val (u ^ N) := by rw [hrel]
      _ = v.val u ^ N := v.val.map_pow u N
  have hlog := congrArg WithZero.log hvalue
  rw [WithZero.log_zpow, WithZero.log_pow, hu, WithZero.log_exp] at hlog
  simp only [zsmul_eq_mul, nsmul_eq_mul, mul_one] at hlog
  have hlog' : a.intDegree * (v.val (c RatFunc.X)).log = (N : ℤ) := by
    simpa using hlog
  have hepos : 0 < (v.val (c RatFunc.X)).log := by
    have hne : v.val (c RatFunc.X) ≠ 0 := ne_of_gt (zero_lt_one.trans hv)
    rw [← WithZero.exp_log hne, ← WithZero.exp_zero,
      WithZero.exp_lt_exp] at hv
    exact hv
  have haDegreePos : 0 < a.intDegree := by
    by_contra hnot
    have hnonpos : a.intDegree ≤ 0 := le_of_not_gt hnot
    have hmul : a.intDegree * (v.val (c RatFunc.X)).log ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos hepos.le
    have hNposInt : (0 : ℤ) < N := by exact_mod_cast hNpos
    rw [hlog'] at hmul
    omega
  have hlogle : (v.val (c RatFunc.X)).log ≤ (N : ℤ) := by
    nlinarith [hlog']
  unfold CoordinatePoleMass.poleOrder ContactLocalPoleBound.poleOrder
  rw [max_eq_right hepos.le]
  exact hlogle.trans (by exact_mod_cast hNle)

/-- The full finite pole mass of the degree-`p` purely inseparable
coordinate is at most `p`: all non-poles contribute zero, and the pole
set is a singleton whose order is bounded above. -/
theorem finite_sum_pole_le_prime
    (p : ℕ) [ExpChar K p] (hp : p.Prime)
    (c : RatFunc K →ₐ[K] L)
    (hfinite : letI : Algebra (RatFunc K) L := c.toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L)
    (hpure : letI : Algebra (RatFunc K) L := c.toRingHom.toAlgebra
      IsPurelyInseparable (RatFunc K) L)
    (hdegree : letI : Algebra (RatFunc K) L := c.toRingHom.toAlgebra
      Module.finrank (RatFunc K) L = p)
    (W : Finset (Place K L)) :
    (∑ v ∈ W, CoordinatePoleMass.poleOrder K L v (c RatFunc.X)) ≤ (p : ℤ) := by
  let poles := W.filter (fun v ↦ 1 < v.val (c RatFunc.X))
  have htrim :
      (∑ v ∈ W, CoordinatePoleMass.poleOrder K L v (c RatFunc.X)) =
        ∑ v ∈ poles, CoordinatePoleMass.poleOrder K L v (c RatFunc.X) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v hvW hvnot
    apply CoordinatePoleMass.poleOrder_eq_zero_of_le_one
    exact le_of_not_gt fun hgt ↦
      hvnot (Finset.mem_filter.mpr ⟨hvW, hgt⟩)
  have hpoles : poles.card ≤ 1 := by
    apply card_pole_places_le_one K L p hp c hpure poles
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  by_cases hnonempty : poles.Nonempty
  · obtain ⟨v, hv⟩ := hnonempty
    have hpoles_eq : poles = {v} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨hv, fun w hw ↦ ?_⟩
      exact (Finset.card_le_one.mp hpoles) w hw v hv
    rw [htrim, hpoles_eq]
    simp only [Finset.sum_singleton]
    exact poleOrder_le_prime K L p hp c hfinite hpure hdegree v
      (Finset.mem_filter.mp hv).2
  · have hpoles_eq : poles = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    rw [htrim, hpoles_eq]
    simp

end

end ProximityPrize.SubmissionLower.SmallPurelyInseparablePole

#print axioms ProximityPrize.SubmissionLower.SmallPurelyInseparablePole.place_eq_of_coordinate_poles
#print axioms ProximityPrize.SubmissionLower.SmallPurelyInseparablePole.card_pole_places_le_one
#print axioms ProximityPrize.SubmissionLower.SmallPurelyInseparablePole.poleOrder_le_prime
#print axioms ProximityPrize.SubmissionLower.SmallPurelyInseparablePole.finite_sum_pole_le_prime
