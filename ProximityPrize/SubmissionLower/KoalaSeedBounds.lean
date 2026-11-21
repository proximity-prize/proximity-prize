import ProximityPrize.SubmissionLower.KoalaCompressedEquation
import ProximityPrize.SubmissionLower.KoalaJetTaylor

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

namespace SplitCut.Compression
noncomputable section

open Polynomial
open K1_14 (FX L Seeds Equation)
open HighCore82219Upper (SeedConstants liftSeeds center)

def axisSpace (F : Type*) [Field F] (i : Fin 2) (d : ℕ) : Submodule F (SeedPoly F) :=
  MvPolynomial.restrictSupport F {m | m i ≤ d}

theorem axis_mem {F : Type*} [Field F] {i : Fin 2} {d : ℕ} {g : SeedPoly F} :
    g ∈ axisSpace F i d ↔ g.degreeOf i ≤ d := by
  exact (MvPolynomial.degreeOf_le_iff (f := g) (n := i)).symm

variable {F R : Type*} [Field F] [CommRing R] [Algebra F R]

def coeffSpace (M : Submodule F R) : Submodule F R[X] where
  carrier := {P | ∀ j, P.coeff j ∈ M}
  zero_mem' := fun j => by rw [coeff_zero]; exact M.zero_mem
  add_mem' h₁ h₂ := fun j => by rw [coeff_add]; exact M.add_mem (h₁ j) (h₂ j)
  smul_mem' a _ hp := fun j => by rw [coeff_smul]; exact M.smul_mem a (hp j)

theorem eval_mem (M : Submodule F R) {P : R[X]} (h : P ∈ coeffSpace M) (x : F) :
    P.eval (algebraMap F R x) ∈ M := by
  rw [eval_eq_sum_range]
  apply M.sum_mem
  intro j _
  rw [← map_pow, mul_comm, ← Algebra.smul_def]
  exact M.smul_mem _ (h j)

theorem taylor_mem (M : Submodule F R) {P : R[X]} (h : P ∈ coeffSpace M) (x : F) :
    taylor (algebraMap F R x) P ∈ coeffSpace M := by
  intro j
  rw [taylor_coeff]
  apply eval_mem M (x := x)
  intro k
  rw [hasseDeriv_coeff, ← map_natCast (algebraMap F R), ← Algebra.smul_def]
  exact M.smul_mem _ (h _)

/-- Translating both polynomial coordinates over the constant field does not
    spend any degree on either seed axis. -/
theorem translated_seed_bound (G : FreshEquation F) (x w : F) (i : Fin 2) (d : ℕ)
    (h : ∀ m n, ((G.coeff m).coeff n).degreeOf i ≤ d) (m n : ℕ) :
    (((StableNode.translate (MvPolynomial.C x) (MvPolynomial.C w) G).coeff m).coeff n).degreeOf i ≤ d := by
  let M : Submodule F (SeedPoly F) := axisSpace F i d
  let N : Submodule F (Polynomial (SeedPoly F)) := coeffSpace M
  have hs : G.map (taylorAlgHom (MvPolynomial.C w : SeedPoly F)).toRingHom ∈ coeffSpace N := by
    intro j
    rw [coeff_map]
    change taylor (algebraMap F (SeedPoly F) w) (G.coeff j) ∈ coeffSpace M
    exact taylor_mem M (fun k => axis_mem.mpr (h j k)) w
  have ht := taylor_mem N hs x
  apply axis_mem.mp
  exact ht m n

def centerEquation (G : FreshEquation L) : Equation :=
  G.eval₂ (mapRingHom liftSeeds) (Polynomial.C (MvPolynomial.C center))

theorem center_axis_bound (G : FreshEquation L) (i : Fin 2) (v : ℕ)
    (h : ∀ m n, ((G.coeff m).coeff n).degreeOf i ≤ v) (n : ℕ) :
    ((centerEquation G).coeff n).degreeOf i ≤ v := by
  let M := axisSpace FX i v
  let N := coeffSpace M
  let P := G.map (mapRingHom liftSeeds)
  have hP : P ∈ coeffSpace N := by
    intro j k
    apply axis_mem.mpr
    simp only [P, coeff_map, coe_mapRingHom, liftSeeds]
    rw [MvPolynomial.degreeOf_eq_sup]
    exact (Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans
      (by simpa only [MvPolynomial.degreeOf_eq_sup] using h j k)
  have he : centerEquation G = P.eval (algebraMap FX Equation center) := by
    rw [centerEquation, eval_map]
    rfl
  rw [he]
  exact axis_mem.mp (eval_mem N hP center n)

theorem center_y_bound (G : FreshEquation L) (e : ℕ) (h : ∀ i, (G.coeff i).natDegree ≤ e) :
    (centerEquation G).natDegree ≤ e := by
  rw [centerEquation, eval₂_eq_sum_range]
  apply natDegree_sum_le_of_forall_le
  intro i _
  refine natDegree_mul_le.trans (Nat.add_le_add ?_ ?_ |>.trans_eq (Nat.add_zero _))
  · exact natDegree_map_le.trans (h i)
  · exact (natDegree_pow_le_of_le _ (natDegree_C _).le).trans_eq (Nat.mul_zero _)

theorem center_eval {E : Type} [CommRing E] (ι : Seeds →+* E) (y : E) (G : FreshEquation L) :
    (centerEquation G).eval₂ ι y =
      (G.map (mapRingHom (ι.comp liftSeeds))).eval₂ (evalRingHom y) (ι (MvPolynomial.C center)) := by
  change eval₂RingHom ι y (G.eval₂ (mapRingHom liftSeeds) (C (MvPolynomial.C center))) = _
  rw [hom_eval₂, eval₂_map, coe_eval₂RingHom, eval₂_C]
  congr 1
  apply RingHom.ext
  intro P
  change (P.map liftSeeds).eval₂ ι y = (P.map (ι.comp liftSeeds)).eval y
  rw [eval₂_map, eval_map]

end
end SplitCut.Compression

#print axioms SplitCut.Compression.translated_seed_bound
#print axioms SplitCut.Compression.center_axis_bound
