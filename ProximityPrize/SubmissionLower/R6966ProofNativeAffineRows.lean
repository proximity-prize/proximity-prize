import ProximityPrize.SubmissionLower.R6966ProofAffineMarkRows
import ProximityPrize.SubmissionLower.R6966ProofNativeGraphExceptional
import ProximityPrize.SubmissionLower.R6960RescueGeometryBills

set_option Elab.async false

namespace Research6966.NativeAffineRows
open Polynomial Finset
open K1 (K I p)
open K1_14 (L FX Seeds Equation atX jetAt graphEval liftPoly seedEmbedding)
open K1_14_3 (SeedField Surface ProjectedProduct)
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open scoped Polynomial Differential Classical
attribute [local instance] GenericPhysicalCentre.physical
noncomputable section
set_option maxHeartbeats 950000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 18

abbrev leading {G : Pade.Row SeedField} (N : Native G) := (den N).coeff 0
abbrev linear {G : Pade.Row SeedField} (N : Native G) := (rhs N).coeff 1
abbrev constant {G : Pade.Row SeedField} (N : Native G) := (rhs N).coeff 0

theorem den_eq {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive)
    (affine : G.graphDegree = 1) : den N = C (leading N) := by
  have cap := (NativeGraphMarks.equation_degrees N gp).1
  change (den N).natDegree ≤ G.graphDegree-1 at cap
  exact eq_C_of_natDegree_eq_zero (by omega)

theorem rhs_eq {G : Pade.Row SeedField} (N : Native G) (gp : G.primitive)
    (affine : G.graphDegree = 1) : rhs N = C (linear N)*Polynomial.X+C (constant N) := by
  apply Polynomial.eq_X_add_C_of_natDegree_le_one
  have cap := (NativeGraphMarks.equation_degrees N gp).2
  rwa [affine] at cap

def seedPoint (z : K) : Fin 2 → FX := ![seedEmbedding z, seedEmbedding z^p]

private theorem constant_power {R : Type*} [Field R] [Differential R]
    (x : R) (fixed : Differential.deriv x = 0) (n : ℕ) :
    Differential.deriv (x^n) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Derivation.leibniz, fixed, ih, smul_zero, smul_zero, add_zero]

private theorem constant_pair {R : Type*} [Field R] [Differential R] (x : R) (n : ℕ)
    (hx : Differential.deriv x = 0) (i : Fin 2) :
    Differential.deriv ((![x,x^n] : Fin 2 → R) i) = 0 := by
  fin_cases i
  · exact hx
  · exact constant_power _ hx _

private theorem fixed (z : K) (j : Fin 2) : Differential.deriv (seedPoint z j) = 0 := by
  apply constant_pair (seedEmbedding z) p _ j
  change Differential.deriv (algebraMap L[X] FX (C (algebraMap K L z))) = 0
  rw [GenericPhysicalCentre.physical_poly, derivative_C, map_zero]

theorem label_inj {u deleted maxHeight} (M : P1.ModelAt maxHeight u deleted) :
    Function.Injective M.label := by
  intro x y same
  exact sub_left_injective (b := M.shift) same

def val {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ : Finset K}
    (F : P1.FamilyAt a M Γ) (z : K) (Q : Equation) : FX :=
  Q.eval₂ (graphEval (M.label z)) (atX (F.scalar z))

def bad {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ : Finset K}
    (F : P1.FamilyAt a M Γ) (T : Finset K) {G : Pade.Row SeedField} (N : Native G) : Finset K :=
  T.filter (fun z => val F z (den N) = 0)

def good {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ : Finset K}
    (F : P1.FamilyAt a M Γ) (T : Finset K) {G : Pade.Row SeedField} (N : Native G) : Finset K :=
  T \ bad F T N

theorem good_subset {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) {G : Pade.Row SeedField} (N : Native G) : good F T N ⊆ T :=
  sdiff_subset

theorem sizes {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) {G : Pade.Row SeedField} (N : Native G) :
    (good F T N).card+(bad F T N).card = T.card :=
  card_sdiff_add_card_eq_card (filter_subset _ _)

def Owned {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ : Finset K}
    (F : P1.FamilyAt a M Γ) (T : Finset K) (parents : Finset Surface) {G : Pade.Row SeedField}
    (N : Native G) : Prop :=
  ∀ z ∈ T, ∃ q ∈ parents, N.poly ∈ q.asIdeal ∧
    ∀ P ∈ q.asIdeal, jetAt P (M.label z) (F.scalar z) = 0

private theorem law {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) {parents : Finset Surface} {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (owners : Owned F T parents N) (z : K) (mem : z ∈ T) :
    val F z (den N)*atX (F.scalar z).derivative = val F z (rhs N) := by
  obtain ⟨q, _, own, mark⟩ := owners z mem
  exact NativeGraphMarks.mark_law N gp own mark

theorem fee {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) {parents : Finset Surface} {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (affine : G.graphDegree = 1) (width : Fin 2 → ℕ)
    (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z ≤ width z)
    (small : width 0 < p) (owners : Owned F T parents N) :
    (bad F T N).card ≤ width 0+p*width 1 := by
  have count := NativeGraphExceptional.singular_count N gp width axes (by simpa [affine] using small)
    (bad F T N) M.label (label_inj M).injOn (fun z => atX (F.scalar z))
    (fun z mem => (mem_filter.mp mem).2) (by
      intro z mem
      obtain ⟨ht, hz⟩ := mem_filter.mp mem
      have eq := law F N gp owners z ht
      change val F z (den N) = 0 at hz
      rw [hz, zero_mul] at eq
      exact eq.symm)
  simpa only [affine, show 2*1-1=1 by decide, one_mul] using count

def point {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ : Finset K}
    (F : P1.FamilyAt a M Γ) (z : K) : Fin 3 → FX :=
  Fin.cons (atX (F.scalar z)) (seedPoint (M.label z))

private abbrev scalar := algebraMap L FX

def equation {u deleted maxHeight} (M : P1.ModelAt maxHeight u deleted)
    {G : Pade.Row SeedField} (N : Native G) (d : ℕ) (i : I) : Equation :=
  AffineMarkRows.row (leading N) (linear N) (constant N) d
    (algebraMap L[X] FX Polynomial.X) (scalar (algebraMap K L (K1.node i)))
    (scalar (algebraMap K L (M.word i)))

def rows {u deleted maxHeight} (M : P1.ModelAt maxHeight u deleted)
    {G : Pade.Row SeedField} (N : Native G) (d : ℕ) (i : I) : MvPolynomial (Fin 3) FX :=
  OdeSurfaceBridge.coordinates (equation M N d i)

theorem seed_cap {G : Pade.Row SeedField} (N : Native G) (width : Fin 2 → ℕ)
    (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z ≤ width z) (z : Fin 2) :
    (leading N) ∈ MvPolynomial.restrictWeightAtMost (Pi.single z 1) (width z) ∧
    (linear N) ∈ MvPolynomial.restrictWeightAtMost (Pi.single z 1) (width z) ∧
    (constant N) ∈ MvPolynomial.restrictWeightAtMost (Pi.single z 1) (width z) := by
  simp only [MvPolynomial.mem_restrictWeightAtMost, Finsupp.weight_single_one_apply,
    ← MvPolynomial.degreeOf_le_iff]
  exact ⟨axes 1 0 z, by simpa [linear, rhs, coeff_neg] using axes 0 1 z,
    by simpa [constant, rhs, coeff_neg] using axes 0 0 z⟩


theorem nodal_count_hypotheses {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) (sub : T ⊆ Γ) {parents : Finset Surface} {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (affine : G.graphDegree = 1)
    (d : ℕ) (physical : (131071 : ℤ)+M.overhead ≤ d) (dp : d < p)
    (owners : Owned F T parents N) :
    (∀ z : ↥(good F T N), a ≤ (WordSurfaceMarks.hits (point F z.val) (rows M N d)).card) ∧
    (∀ (x y : ↥(good F T N)), x ≠ y →
      ((WordSurfaceMarks.hits (point F x.val) (rows M N d)) ∩
        (WordSurfaceMarks.hits (point F y.val) (rows M N d))).card ≤ d) := by
  classical
  let S := good F T N
  let words (z : ↥S) := liftPoly (F.scalar z.val)
  let nodes (i : I) : FX := scalar (algebraMap K L (K1.node i))
  let recv (i : I) : FX := scalar (algebraMap K L (M.word i))
  have marks (z : ↥S) := F.mark z.val (sub (good_subset F N z.property))
  have degree (z : ↥S) : (words z).natDegree ≤ d := by
    change ((F.scalar z.val).map (algebraMap K L)).natDegree ≤ d
    rw [natDegree_map_eq_of_injective (algebraMap K L).injective]
    rcases (marks z).scalar_degree with zero | bound
    · simp [zero]
    · change ((F.scalar z.val).natDegree : ℤ) ≤ 131071+M.overhead at bound
      omega
  have unique : Function.Injective words := fun x z eq => Subtype.ext (F.distinct
    (sub (good_subset F N x.property)) (sub (good_subset F N z.property))
    ((map_injective _ (algebraMap K L).injective) eq))
  have detect (z : ↥S) (i : I) :
      MvPolynomial.eval (point F z.val) (rows M N d i) = 0 ↔ ((words z).map scalar).eval (nodes i) = recv i := by
    rw [show MvPolynomial.eval (point F z.val) (rows M N d i) =
      NonlinearMarkRows.evaluate (seedPoint (M.label z.val)) (atX (F.scalar z.val)) (equation M N d i)
        from OdeSurfaceBridge.read ..]
    have den0 := den_eq N gp affine
    have rhs1 := rhs_eq N gp affine
    have nz : val F z.val (den N) ≠ 0 := fun zero =>
      (mem_sdiff.mp z.property).2 (mem_filter.mpr ⟨good_subset F N z.property, zero⟩)
    have eq := law F N gp owners z.val (good_subset F N z.property)
    unfold val at nz eq
    rw [den0, eval₂_C] at nz eq
    rw [rhs1, eval₂_add, eval₂_mul, eval₂_C, eval₂_C, eval₂_X] at eq
    change MvPolynomial.eval (seedPoint (M.label z.val)) (leading N) ≠ 0 at nz
    have law' : MvPolynomial.eval (seedPoint (M.label z.val)) (leading N)*
        algebraMap L[X] FX (words z).derivative =
      MvPolynomial.eval (seedPoint (M.label z.val)) (linear N)*atX (F.scalar z.val)+
        MvPolynomial.eval (seedPoint (M.label z.val)) (constant N) := by
      simpa only [words, liftPoly, derivative_map, atX, graphEval, seedPoint] using eq
    exact AffineMarkRows.detects _ (fixed (M.label z.val)) _ _ _ (words z) d (degree z)
      (fun j hj => K1_14_2_4_2.factorial_ne_zero (hj.trans_lt dp)) _ _ law' nz
  refine ⟨?_, WordSurfacePrice.word_overlap (fun z : ↥S => point F z.val) (rows M N d) nodes
    (scalar.injective.comp ((algebraMap K L).injective.comp ProximityPrize.Benchmark.IRSProfile.domain.injective))
    recv (fun z => (words z).map scalar) ((map_injective _ scalar.injective).comp unique) d
    (fun z => natDegree_map_le.trans (degree z)) detect⟩
  intro z
  exact (marks z).bad.agreement.trans (card_le_card (fun i hi => WordSurfaceMarks.hit.mpr
    ((detect z i).mpr ((Polynomial.eval_map_apply scalar _).trans
      (congrArg scalar ((Polynomial.eval_map_apply (algebraMap K L) _).trans
        (congrArg (algebraMap K L) ((marks z).scalar_hits i hi))))))))

end
end Research6966.NativeAffineRows
