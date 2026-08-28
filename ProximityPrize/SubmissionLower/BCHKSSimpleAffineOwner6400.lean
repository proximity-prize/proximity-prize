import ProximityPrize.SubmissionLower.BCHKSBareUniversalSelectedPairCore
import ProximityPrize.SubmissionLower.BCHKSIdentitySparseRows6400

/-!
# The simple affine-owner branch at score 64.00

The factor-specific seed fibre first supplies one coordinate with a huge
agreement fibre.  Its direct affine obstruction is therefore identically
zero.  If the resulting affine root is simple, the retained fibre forces the
same linear graph to divide every universal coordinate obstruction needed by
the bare universal alignment core.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators
open UniversalNumerator

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

private theorem eval_affine_specialization_commute_6400
    {F : Type} [Field F] (A : F[X][X]) (a b z : F) :
    (A.eval (Polynomial.C a + Polynomial.X * Polynomial.C b)).eval z =
      (A.map (Polynomial.evalRingHom z)).eval (a + z * b) := by
  rw [mul_comm Polynomial.X (Polynomial.C b), mul_comm z b]
  induction A using Polynomial.induction_on' with
  | add A B hA hB =>
      simpa using congrArg₂ (· + ·) hA hB
  | monomial n c =>
      simp [Polynomial.map_monomial, Polynomial.eval_monomial]

/-- Score-64 simple-owner closure, with the unique remaining ramified branch
returned explicitly. -/
theorem simple_affine_owner_alignment_or_repeated_6400
    {I F : Type} [Fintype I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F]
    (omega : I ↪ F) (hn : Fintype.card I = 262144)
    (R : F[X][X][Y]) (D : ℕ)
    (hRpos : 0 < R.natDegree) (hRdeg : R.natDegree ≤ D)
    (hYZ : YZCap R D)
    (T : Finset F) (P : F → F[X]) (Arow : F → Finset I)
    (U₀ U₁ : I → F)
    (hPdeg : ∀ z ∈ T, (P z).natDegree ≤ 131071)
    (hExact : ∀ z ∈ T, (triSpecializeZ R z).eval (P z) = 0)
    (hrow : ∀ z ∈ T, 185364 ≤ (Arow z).card)
    (hagree : ∀ z ∈ T, ∀ i ∈ Arow z,
      (P z).eval (omega i) = U₀ i + z * U₁ i)
    (hT : 144802557 * D < T.card)
    (hkF : 131071 < Fintype.card F) :
    (∃ Good : Finset F, ∃ p₀ p₁ : F[X],
      Good ⊆ T ∧ 76780 < Good.card ∧
      p₀.natDegree ≤ 131071 ∧ p₁.natDegree ≤ 131071 ∧
      ∀ z ∈ Good, P z = p₀ + Polynomial.C z * p₁) ∨
    ∃ i₀ : I,
      102390000 * D < (T.filter fun z ↦ i₀ ∈ Arow z).card ∧
      directAffineObstruction R (omega i₀) (U₀ i₀) (U₁ i₀) = 0 ∧
      (triSpecializeX R (omega i₀)).derivative.eval
        (Polynomial.C (U₀ i₀) +
          Polynomial.X * Polynomial.C (U₁ i₀)) = 0 := by
  classical
  have hDpos : 0 < D := hRpos.trans_le hRdeg
  let Base : Finset I := Finset.univ.filter fun i : I ↦
    102390000 * D < (T.filter fun z ↦ i ∈ Arow z).card
  have hBaseCard : 1 ≤ Base.card := by
    have hcount := score6400_exists_base_fiber_numeric T.card D hDpos hT
    simpa [Base] using many_large_fibers T Arow 262144 76780 0
      (102390000 * D) hn
      (fun z hz ↦ by simpa using hrow z hz) hcount
  have hBaseNonempty : Base.Nonempty := Finset.card_pos.mp (by omega)
  let i₀ : I := Classical.choose hBaseNonempty
  have hi₀ : i₀ ∈ Base := Classical.choose_spec hBaseNonempty
  let x₀ : F := omega i₀
  let a : F := U₀ i₀
  let b : F := U₁ i₀
  let T₀ : Finset F := T.filter fun z ↦ i₀ ∈ Arow z
  have hT₀large : 102390000 * D < T₀.card := by
    simpa [Base, T₀] using (Finset.mem_filter.mp hi₀).2
  let G : F[X] := directAffineObstruction R x₀ a b
  have hGdegree : G.natDegree ≤ D :=
    directAffineObstruction_natDegree_le R x₀ a b D hYZ
  have hGroot : ∀ z ∈ T₀, G.eval z = 0 := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    apply directAffineObstruction_root_of_agreement R (P z) x₀ a b z
    · simpa only [← triEval_eq_eval_triSpecializeZ] using hExact z hz'.1
    · simpa [x₀, a, b] using hagree z hz'.1 i₀ hz'.2
  have hGzero : G = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' G T₀ hGroot
    exact hGdegree.trans_lt (by
      have : D ≤ 102390000 * D := by nlinarith
      exact this.trans_lt hT₀large)
  let slope : F[X] := (triSpecializeX R x₀).derivative.eval
    (Polynomial.C a + Polynomial.X * Polynomial.C b)
  by_cases hslopeZero : slope = 0
  · right
    refine ⟨i₀, ?_, ?_, ?_⟩
    · simpa [T₀] using hT₀large
    · simpa [G, x₀, a, b] using hGzero
    · simpa [slope, x₀, a, b] using hslopeZero
  left
  let T₁ : Finset F := T₀.filter fun z ↦ slope.eval z ≠ 0
  let Bad : Finset F := T₀.filter fun z ↦ slope.eval z = 0
  have hBadCard : Bad.card ≤ D := by
    have hsub : Bad ⊆ slope.roots.toFinset := by
      intro z hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hslopeZero]
      exact (Finset.mem_filter.mp hz).2
    calc
      Bad.card ≤ slope.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ slope.roots.card := Multiset.toFinset_card_le _
      _ ≤ slope.natDegree := Polynomial.card_roots' _
      _ ≤ D := by
        simpa [slope] using affineSlope_natDegree_le_of_yzCap R x₀ a b D hYZ
  have hpartition : T₁.card + Bad.card = T₀.card := by
    simpa only [T₁, Bad, not_ne_iff] using
      (Finset.card_filter_add_card_filter_not
        (s := T₀) (p := fun z ↦ slope.eval z ≠ 0))
  have hT₁large : 102389999 * D < T₁.card := by
    nlinarith
  have hT₁T : T₁ ⊆ T := by
    exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  let Bobs : ℕ := 262141 * R.natDegree + 262141 * D
  let Coord : Finset I := Finset.univ.filter fun i : I ↦
    Bobs < (T₁.filter fun z ↦ i ∈ Arow z).card
  have hCoordCard : 131072 ≤ Coord.card := by
    have hcount := score6400_simple_owner_incidence_numeric
      T₁.card R.natDegree D hRdeg hDpos hT₁large
    simpa [Coord, Bobs] using many_large_fibers T₁ Arow
      262144 76780 131071 Bobs hn
      (fun z hz ↦ by simpa using hrow z (hT₁T hz)) hcount
  let Afield : Finset F := Coord.image omega
  have hAfieldCard : 131072 ≤ Afield.card := by
    have hc : Afield.card = Coord.card :=
      Finset.card_image_iff.mpr fun i _ j _ hij ↦ omega.injective hij
    rw [hc]
    exact hCoordCard
  let idx : Afield → I := fun x ↦
    Classical.choose (Finset.mem_image.mp x.property)
  have hidx (x : Afield) : idx x ∈ Coord ∧ omega (idx x) = (x : F) :=
    Classical.choose_spec (Finset.mem_image.mp x.property)
  let U₀f : F → F := fun x ↦
    if hxA : x ∈ Afield then U₀ (idx ⟨x, hxA⟩) else 0
  let U₁f : F → F := fun x ↦
    if hxA : x ∈ Afield then U₁ (idx ⟨x, hxA⟩) else 0
  have hdiv : ∀ x ∈ Afield,
      (Polynomial.X - Polynomial.C
        (Polynomial.C a + Polynomial.X * Polynomial.C b)) ∣
        concreteUniversalAffineObstruction x₀ R 262141 131071
          (x - x₀) (U₀f x) (U₁f x) := by
    intro x hxA
    let xx : Afield := ⟨x, hxA⟩
    let i : I := idx xx
    let S : Finset F := T₁.filter fun z ↦ i ∈ Arow z
    have hlarge : 262141 * R.natDegree + 262141 * D < S.card := by
      simpa [S, i, Bobs] using (Finset.mem_filter.mp (hidx xx).1).2
    apply affine_graph_dvd_concreteUniversalAffineObstruction_of_many_roots
      x₀ a b (x - x₀) (U₀f x) (U₁f x) R
      262141 131071 R.natDegree D
      (by norm_num [FiniteHenselWeight.denominatorExponent])
      (by norm_num) hRpos hDpos hRpos le_rfl hYZ S _ hlarge
    intro z hz
    have hzS := Finset.mem_filter.mp hz
    have hzT₁ : z ∈ T₁ := hzS.1
    have hzT₀ : z ∈ T₀ := (Finset.mem_filter.mp hzT₁).1
    have hzT : z ∈ T := hT₁T hzT₁
    have hbase : (P z).eval x₀ = a + z * b := by
      have hzbase := (Finset.mem_filter.mp hzT₀).2
      simpa [x₀, a, b] using hagree z hzT i₀ hzbase
    have hslope : FiniteHensel.ySlope
        (triSpecializeZ R z) x₀ ((P z).eval x₀) ≠ 0 := by
      have hclean := (Finset.mem_filter.mp hzT₁).2
      have hslopeEval : slope.eval z =
          FiniteHensel.ySlope (triSpecializeZ R z) x₀ (a + z * b) := by
        calc
          slope.eval z =
              ((universalSlope x₀ R).eval
                (Polynomial.C a + Polynomial.X * Polynomial.C b)).eval z := by
            simp [slope, universalSlope, triSpecializeX,
              Polynomial.derivative_map]
          _ = ((universalSlope x₀ R).map
                (Polynomial.evalRingHom z)).eval (a + z * b) :=
            eval_affine_specialization_commute_6400
              (universalSlope x₀ R) a b z
          _ = _ := by
            simpa [evalZY] using universalSlope_eval x₀ z (a + z * b) R
      rw [hbase]
      rw [← hslopeEval]
      exact hclean
    have haffine : (P z).eval (x₀ + (x - x₀)) =
        U₀f x + z * U₁f x := by
      have hag := hagree z hzT i hzS.2
      have hix : omega i = x := hidx xx |>.2
      simpa [U₀f, U₁f, hxA, xx, i, hix] using hag
    have hzroot := biEval_concreteUniversalAffineObstruction_eq_zero
      x₀ z ((P z).eval x₀) R (P z) 262141 131071
      (x - x₀) (U₀f x) (U₁f x)
      (by norm_num [FiniteHenselWeight.denominatorExponent]) hRpos rfl
      (hPdeg z hzT) (hExact z hzT) hslope (by simpa using haffine)
    rw [hbase] at hzroot
    exact hzroot
  let P₁ : T₁ → F[X] := fun z ↦ P z
  have hT₁nonempty : T₁.Nonempty := Finset.card_pos.mp (by
    have : 0 < 102389999 * D := Nat.mul_pos (by norm_num) hDpos
    omega)
  obtain ⟨p₀, p₁, hp₀, hp₁, hpencil⟩ :=
    affine_graph_divisor_universal_alignment_core
      x₀ a b R hRpos (by simpa [G, directAffineObstruction,
        fixedAffineOwnerObstruction, x₀, a, b] using hGzero)
      131071 131071 le_rfl T₁ hT₁nonempty P₁
      (fun z ↦ hPdeg z (hT₁T z.property))
      (fun z ↦ hExact z (hT₁T z.property))
      (fun z ↦ by
        have hzT₀ := (Finset.mem_filter.mp z.property).1
        have hzbase := (Finset.mem_filter.mp hzT₀).2
        simpa [P₁, x₀, a, b] using
          hagree (z : F) (hT₁T z.property) i₀ hzbase)
      (fun z ↦ by
        have hclean := (Finset.mem_filter.mp z.property).2
        have hslopeEval : slope.eval (z : F) =
            FiniteHensel.ySlope (triSpecializeZ R (z : F)) x₀
              (a + (z : F) * b) := by
          calc
            slope.eval (z : F) =
                ((universalSlope x₀ R).eval
                  (Polynomial.C a + Polynomial.X * Polynomial.C b)).eval
                    (z : F) := by
              simp [slope, universalSlope, triSpecializeX,
                Polynomial.derivative_map]
            _ = ((universalSlope x₀ R).map
                  (Polynomial.evalRingHom (z : F))).eval
                    (a + (z : F) * b) :=
              eval_affine_specialization_commute_6400
                (universalSlope x₀ R) a b (z : F)
            _ = _ := by
              simpa [evalZY] using universalSlope_eval x₀ (z : F)
                (a + (z : F) * b) R
        have hzT₀ := (Finset.mem_filter.mp z.property).1
        have hzbase := (Finset.mem_filter.mp hzT₀).2
        have hbase : (P₁ z).eval x₀ = a + (z : F) * b := by
          simpa [P₁, x₀, a, b] using
            hagree (z : F) (hT₁T z.property) i₀ hzbase
        rw [hbase, ← hslopeEval]
        exact hclean)
      hkF Afield hAfieldCard U₀f U₁f hdiv
  refine ⟨T₁, p₀, p₁, hT₁T, ?_, hp₀, hp₁, ?_⟩
  · omega
  · intro z hz
    exact hpencil ⟨z, hz⟩

end ProximityPrize.SubmissionLower
