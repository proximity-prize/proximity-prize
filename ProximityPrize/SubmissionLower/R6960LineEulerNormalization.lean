import ProximityPrize.SubmissionLower.R6960LineEuler
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Module

set_option Elab.async false
set_option maxHeartbeats 5200000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.LineEuler
noncomputable section
open Polynomial LaurentPolynomial Module
open scoped Polynomial BigOperators Matrix

variable {k : Type*} [Field k]

/-- The two affine polynomial rings embedded in the same Laurent torus. -/
def chartEmbedding (infinity : Bool) : (Polynomial k) →ₐ[k] Laurent k :=
  if infinity then infinityEmbedding else Polynomial.toLaurentAlg

theorem chartLocalization (s : Bool) :
    let : Algebra (Polynomial k) (Laurent k) := (chartEmbedding (k:=k) s).toRingHom.toAlgebra
    IsLocalization.Away (Polynomial.X : (Polynomial k)) (Laurent k) := by
  let : Algebra (Polynomial k) (Laurent k) := (chartEmbedding (k:=k) s).toRingHom.toAlgebra
  have inj : Function.Injective (chartEmbedding (k:=k) s) := by
    cases s
    · exact Polynomial.toLaurent_injective
    · exact infinityEmbedding_injective
  apply IsLocalization.Away.mk (Polynomial.X : (Polynomial k))
  · change IsUnit (chartEmbedding s (Polynomial.X : (Polynomial k)))
    have eq : chartEmbedding s (Polynomial.X : (Polynomial k))=T (if s then -1 else 1) := by
      cases s <;> simp [chartEmbedding,Polynomial.toLaurent_X]
    rw [eq]
    exact isUnit_T _
  · intro z
    cases s with
    | false =>
      obtain ⟨n,p,hp⟩ := LaurentPolynomial.exists_T_pow z
      refine ⟨n,p,?_⟩
      change z*(chartEmbedding false (Polynomial.X : (Polynomial k)))^n=chartEmbedding false p
      rw [←map_pow]
      change z*(Polynomial.X^n : (Polynomial k)).toLaurent=p.toLaurent
      simpa only [Polynomial.toLaurent_X_pow] using hp.symm
    | true =>
      obtain ⟨n,p,hp⟩ := LaurentPolynomial.exists_T_pow (invert z)
      refine ⟨n,p,?_⟩
      change z*(chartEmbedding true (Polynomial.X : (Polynomial k)))^n=chartEmbedding true p
      rw [←map_pow]
      change z*invert (Polynomial.X^n : (Polynomial k)).toLaurent=invert p.toLaurent
      have e := congrArg (invert (R:=k)) hp
      rw [map_mul,involutive_invert z,invert_T] at e
      simpa only [Polynomial.toLaurent_X_pow,invert_T] using e.symm
  · intro x y eq
    exact ⟨0,by rw [inj eq]⟩

variable {E : Type*} [Field E] [Algebra (Laurent k) E]

/-- The original affine order, using the selected base embedding. -/
abbrev chartOrder (s : Bool) :=
  @integralClosure (Polynomial k) E _ _ ((algebraMap (Laurent k) E).comp (chartEmbedding s).toRingHom).toAlgebra

/-- Both affine orders localize to this very same subring of the root field. -/
abbrev torusOrder := integralClosure (Laurent k) E

def chartOrderMap (s : Bool) : chartOrder (k:=k) (E:=E) s →+* torusOrder (k:=k) (E:=E) := by
  let : Algebra (Polynomial k) (Laurent k) := (chartEmbedding (k:=k) s).toRingHom.toAlgebra
  let : Algebra (Polynomial k) E := ((algebraMap (Laurent k) E).comp (chartEmbedding s).toRingHom).toAlgebra
  let : IsScalarTower (Polynomial k) (Laurent k) E :=
    IsScalarTower.of_algebraMap_eq (R:=(Polynomial k)) (S:=Laurent k) (A:=E) fun _=>rfl
  exact Subring.inclusion (show (chartOrder (k:=k) (E:=E) s).toSubring≤(torusOrder (k:=k) (E:=E)).toSubring
    from fun _ hi=>IsIntegral.tower_top (show IsIntegral (Polynomial k) _ from hi))

@[simp] theorem chartOrderMap_val (s : Bool) (x : chartOrder (k:=k) (E:=E) s) :
    (chartOrderMap s x:E)=(x:E) := rfl

variable {ι : Type*}

private def localBasisData (s : Bool) (b : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) s)) :
    {B : Basis ι (Laurent k) (torusOrder (k:=k) (E:=E)) //
      (∀ i,B i=chartOrderMap s (b i)) ∧
      ∀ x i,B.repr (chartOrderMap s x) i=chartEmbedding s (b.repr x i)} := by
  let : Algebra (Polynomial k) (Laurent k) := (chartEmbedding (k:=k) s).toRingHom.toAlgebra
  let : Algebra (Polynomial k) E := ((algebraMap (Laurent k) E).comp (chartEmbedding s).toRingHom).toAlgebra
  let : IsScalarTower (Polynomial k) (Laurent k) E :=
    IsScalarTower.of_algebraMap_eq (R:=(Polynomial k)) (S:=Laurent k) (A:=E) fun _=>rfl
  let A := chartOrder (k:=k) (E:=E) s
  let S := torusOrder (k:=k) (E:=E)
  let : Algebra (Polynomial k) S := ((algebraMap (Laurent k) S).comp (chartEmbedding s).toRingHom).toAlgebra
  let : Algebra A S := (chartOrderMap (k:=k) (E:=E) s).toAlgebra
  let : IsScalarTower (Polynomial k) (Laurent k) S :=
    IsScalarTower.of_algebraMap_eq (R:=(Polynomial k)) (S:=Laurent k) (A:=S) fun _=>rfl
  let : IsScalarTower A S E := IsScalarTower.of_algebraMap_eq (R:=A) (S:=S) (A:=E) fun _=>rfl
  let : IsScalarTower (Polynomial k) A S :=
    IsScalarTower.of_algebraMap_eq (R:=(Polynomial k)) (S:=A) (A:=S) fun _=>rfl
  let : IsScalarTower (Polynomial k) S E :=
    IsScalarTower.of_algebraMap_eq (R:=(Polynomial k)) (S:=S) (A:=E) fun _=>rfl
  let : IsLocalization.Away (Polynomial.X : (Polynomial k)) (Laurent k) := chartLocalization (k:=k) s
  have ux : IsUnit (algebraMap (Polynomial k) E (Polynomial.X : (Polynomial k))) := by
    change IsUnit (algebraMap (Laurent k) E (chartEmbedding s (Polynomial.X : (Polynomial k))))
    have mapX : chartEmbedding s (Polynomial.X : (Polynomial k))=T (if s then -1 else 1) := by
      cases s <;> simp [chartEmbedding,Polynomial.toLaurent_X]
    rw [mapX]
    exact (isUnit_T _).map _
  let : IsLocalization.Away (algebraMap (Polynomial k) E (Polynomial.X : (Polynomial k))) E :=
    IsLocalization.away_of_isUnit_of_bijective E ux Function.bijective_id
  let : IsLocalization.Away (algebraMap (Polynomial k) A (Polynomial.X : (Polynomial k))) S :=
    IsLocalization.Away.integralClosure (S:=E) (Rf:=Laurent k) (Sf:=E) (Polynomial.X : (Polynomial k))
  let powers := Submonoid.powers (Polynomial.X : (Polynomial k))
  refine ⟨b.localizationLocalization (Laurent k) powers S,?_,?_⟩
  · intro i
    exact b.localizationLocalization_apply (Laurent k) powers S i
  · intro x i
    exact b.localizationLocalization_repr_algebraMap (Laurent k) powers S x i

/-- Localizing an actual normalization basis along its base coordinate
preserves its index set and vectors in the common torus order. -/
def localBasis (s : Bool) (b : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) s)) :
    Basis ι (Laurent k) (torusOrder (k:=k) (E:=E)) := (localBasisData s b).1

@[simp] theorem localBasis_apply (s : Bool) (b : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) s)) (i : ι) :
    localBasis s b i=chartOrderMap s (b i) := (localBasisData s b).2.1 i

@[simp] theorem localBasis_repr (s : Bool) (b : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) s))
    (x : chartOrder (k:=k) (E:=E) s) (i : ι) :
    (localBasis s b).repr (chartOrderMap s x) i=chartEmbedding s (b.repr x i) := (localBasisData s b).2.2 x i

variable [Fintype ι] [DecidableEq ι]

/-- The change of coordinates from the reciprocal basis to the finite
basis on the common torus. -/
def normalizedTransition (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) true)) : Matrix ι ι (Laurent k) :=
  LinearMap.toMatrix' (((localBasis true bi).equivFun.symm.trans (localBasis false bf).equivFun).toLinearMap)

theorem normalizedTransition_unit (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) true)) : IsUnit (normalizedTransition bf bi) := by
  let e := (localBasis true bi).equivFun.symm.trans (localBasis false bf).equivFun
  apply isUnit_iff_exists_inv.mpr
  refine ⟨LinearMap.toMatrix' e.symm.toLinearMap,?_⟩
  apply Matrix.toLin'.injective
  rw [normalizedTransition,Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_toMatrix',Matrix.toLin'_one]
  exact e.comp_symm

theorem normalizedTransition_mulVec (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) true)) (v : ι→Laurent k) :
    normalizedTransition bf bi *ᵥ v=(localBasis false bf).equivFun ((localBasis true bi).equivFun.symm v) := by
  rw [←Matrix.toLin'_apply,normalizedTransition,Matrix.toLin'_toMatrix']
  rfl

/-- The columns of chart elements in their original polynomial basis. -/
def chartMatrix {s : Bool} (b : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) s))
    (u : ι→chartOrder (k:=k) (E:=E) s) : Matrix ι ι (Polynomial k) := fun i j=>b.repr (u j) i

/-- Matching normalized chart elements give literal matching Laurent
matrix columns, with the specified pole clearing in each column. -/
theorem normalized_join (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) true))
    (x : ι→chartOrder (k:=k) (E:=E) false) (y : ι→chartOrder (k:=k) (E:=E) true) (width : ι→ℕ)
    (agree : ∀ j,(x j:E)=algebraMap (Laurent k) E (T (width j:ℤ))*(y j:E)) :
    (chartMatrix bf x).map (Polynomial.toLaurent (R:=k)) = normalizedTransition bf bi *
      (chartMatrix bi y).map (infinityEmbedding (k:=k)) * Matrix.diagonal (fun j=>T (width j:ℤ)) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_diagonal]
  change chartEmbedding false (bf.repr (x j) i) =
    ((normalizedTransition bf bi) *ᵥ (fun u=>chartEmbedding true (bi.repr (y j) u))) i * T (width j:ℤ)
  have coord : (fun u=>chartEmbedding true (bi.repr (y j) u)) =
      (localBasis true bi).equivFun (chartOrderMap true (y j)) := by
    funext u
    rw [Basis.equivFun_apply,localBasis_repr]
  rw [coord,normalizedTransition_mulVec,LinearEquiv.symm_apply_apply]
  have tor : chartOrderMap false (x j)=T (R:=k) (width j:ℤ) • chartOrderMap true (y j) := by
    apply Subtype.ext
    rw [chartOrderMap_val,Subalgebra.coe_smul,chartOrderMap_val,Algebra.smul_def]
    exact agree j
  calc
    _ = (localBasis false bf).equivFun (chartOrderMap false (x j)) i := by
      rw [Basis.equivFun_apply,localBasis_repr]
    _ = _ := by
      rw [tor,(localBasis false bf).equivFun.map_smul]
      change T (width j:ℤ)*(localBasis false bf).equivFun (chartOrderMap true (y j)) i=_
      exact mul_comm _ _

/-- The Euler formula for the finite-free normalization of a line,
computed using the actual pair of affine PID bases. -/
theorem normalized_euler (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) true)) :
    FiniteDimensional k (H0 (normalizedTransition bf bi)) ∧
    FiniteDimensional k (H1 (normalizedTransition bf bi)) ∧
    ∃ d : ℤ,(normalizedTransition bf bi).det.degree=(d:WithBot ℤ) ∧
      (finrank k (H0 (normalizedTransition bf bi)):ℤ)-(finrank k (H1 (normalizedTransition bf bi)):ℤ)=
        (Fintype.card ι:ℤ)+d :=
  euler_index _ (normalizedTransition_unit bf bi)

#print axioms localBasis
#print axioms normalized_euler
end
end Lower6960.LineEuler
