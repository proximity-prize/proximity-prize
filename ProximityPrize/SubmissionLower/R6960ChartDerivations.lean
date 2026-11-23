import ProximityPrize.SubmissionLower.R6960PlaneConstants
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Etale.Field

noncomputable section
set_option Elab.async false
namespace Lower6960.ChartDerivations
open Polynomial Algebra TrivSqZeroExt
open scoped Polynomial

section Smooth
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
private abbrev Dual (B : Type*) := TrivSqZeroExt B B

private def twist (d : Derivation ℤ A A) : A→+* Dual B where
  toFun x:=⟨algebraMap A B x,algebraMap A B (d x)⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by
    ext
    · exact map_add (algebraMap A B) _ _
    · change algebraMap A B (d (x+y))=algebraMap A B (d x)+algebraMap A B (d y)
      rw [map_add,map_add]
  map_mul' x y := by
    ext
    · exact map_mul (algebraMap A B) _ _
    · change algebraMap A B (d (x*y))=algebraMap A B x*algebraMap A B (d y)+algebraMap A B (d x)*algebraMap A B y
      simp [d.leibniz,smul_eq_mul,mul_comm]

/-- The square-zero lifting property extends the base derivation. This
one construction applies to both the base localization and the separable
root extension. -/
theorem extend [Algebra.FormallySmooth A B] (d : Derivation ℤ A A) :
    ∃ D : Derivation ℤ B B,∀ x,D (algebraMap A B x)=algebraMap A B (d x) := by
  classical
  let S:=Dual B
  let π : S→+*B := (fstHom ℤ B B).toRingHom
  have onto : Function.Surjective π := fun b=>⟨⟨b,0⟩,rfl⟩
  let I:=RingHom.ker π
  have nil : I^2=⊥ := by
    rw [pow_two,eq_bot_iff]
    apply Ideal.mul_le.mpr
    intro a ha b hb
    have az : a.fst=0 := RingHom.mem_ker.mp ha
    have bz : b.fst=0 := RingHom.mem_ker.mp hb
    change a*b=0
    apply TrivSqZeroExt.ext
    · change a.fst*b.fst=0
      rw [az,zero_mul]
    · change a.fst*b.snd+a.snd*b.fst=0
      simp [az,bz]
  let : Algebra A S := (twist (B:=B) d).toAlgebra
  let eq := RingHom.quotientKerEquivOfSurjective onto
  let inv : B →ₐ[A] S ⧸ I := { eq.symm.toRingHom with
    commutes' := by
      intro r
      change eq.symm (π (twist d r))=Ideal.Quotient.mk I (twist d r)
      exact RingHom.quotientKerEquivOfSurjective_symm_apply onto _ }
  obtain ⟨g,hg⟩ := Algebra.FormallySmooth.exists_lift I ⟨2,nil⟩ inv
  have fstId (b : B) : (g b).fst=b := by
    have same:=congrArg eq (DFunLike.congr_fun hg b)
    change eq (Ideal.Quotient.mk I (g b))=eq (eq.symm b) at same
    exact (RingHom.quotientKerEquivOfSurjective_apply_mk onto (g b)).symm.trans
      (same.trans (eq.apply_symm_apply b))
  let sndAdd : B→+B := {
    toFun:=fun x=>(g x).snd
    map_zero':=by simp
    map_add':=fun x y=>by rw [map_add]; rfl }
  let D : Derivation ℤ B B := {
    sndAdd.toIntLinearMap with
    map_one_eq_zero':=by change (g 1).snd=0; simp
    leibniz':=by
      intro x y
      change (g (x*y)).snd=x*(g y).snd+y*(g x).snd
      rw [map_mul,snd_mul,fstId,fstId]
      simp [smul_eq_mul,mul_comm] }
  refine ⟨D,?_⟩
  intro x
  exact congrArg TrivSqZeroExt.snd (g.commutes x)

end Smooth

#print axioms extend

section Coordinates
open PlaneConstants (Plane)
variable {k : Type} [Field k]

private def dx : Derivation ℤ (Plane k) (Plane k) :=
  (Polynomial.derivative' : Derivation k[X] (Plane k) (Plane k)).restrictScalars ℤ

private def dz : Derivation ℤ (Plane k) (Plane k) :=
  letI : Differential k[X] := ⟨(Polynomial.derivative' : Derivation k k[X] k[X]).restrictScalars ℤ⟩
  Differential.mapCoeffs

private theorem dz_apply (q : Plane k) : dz q=Bivariate.swap (Bivariate.swap q).derivative := by
  ext i j
  change (q.coeff i).derivative.coeff j=_
  rw [CurvatureSquares.coeff_swap,coeff_derivative,coeff_derivative,
    show ((j:k[X])+1)=C ((j:k)+1) by simp,coeff_mul_C,CurvatureSquares.coeff_swap]

/-- Both compatible partials exist on any terminal-degree root field, and
their common constants admit p-th roots in that field. -/
theorem coordinates (F E : Type*) [Field F] [Field E] [Algebra (Plane k) F]
    [IsFractionRing (Plane k) F] [Algebra F E] [FiniteDimensional F E]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP F p] [CharP E p]
    (small : Module.finrank F E<p) :
    ∃ (Dx Dz : Derivation ℤ E E),
      (∀ q,Dx (algebraMap F E (algebraMap (Plane k) F q))=
        algebraMap F E (algebraMap (Plane k) F q.derivative)) ∧
      (∀ q,Dz (algebraMap F E (algebraMap (Plane k) F q))=
        algebraMap F E (algebraMap (Plane k) F (Bivariate.swap (Bivariate.swap q).derivative))) ∧
      ∀ u : E,Dx u=0 → Dz u=0 → ∃ y:E,y^p=u := by
  have : Algebra.FormallyEtale (Plane k) F :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (Plane k))
  have : Algebra.IsSeparable F E := by
    constructor
    intro x
    have hx : IsIntegral F x:=Algebra.IsIntegral.isIntegral x
    exact (separable_iff_derivative_ne_zero (minpoly.irreducible hx)).mpr
      (CurvatureSquares.derivative_ne_zero_of_natDegree_pos_lt_char p _ (minpoly.natDegree_pos hx)
        ((minpoly.natDegree_le x).trans_lt small))
  have : Algebra.FormallyEtale F E := Algebra.FormallyEtale.of_isSeparable F E
  obtain ⟨x,hx⟩ := extend (B:=F) (dx (k:=k))
  obtain ⟨z,hz⟩ := extend (B:=F) (dz (k:=k))
  obtain ⟨X',ex⟩ := extend (B:=E) x
  obtain ⟨Z',ez⟩ := extend (B:=E) z
  have vertical (q : Plane k) : z (algebraMap (Plane k) F q)=_ :=
    (hz q).trans (congrArg (algebraMap (Plane k) F) (dz_apply q))
  exact ⟨X',Z',fun q=>(ex _).trans (congrArg _ (hx q)),fun q=>(ez _).trans (congrArg _ (vertical q)),
    fun u hu hv=>PlaneConstants.root_field_constant p x z X' Z' hx vertical ex ez small u hu hv⟩
end Coordinates

#print axioms coordinates
end Lower6960.ChartDerivations
