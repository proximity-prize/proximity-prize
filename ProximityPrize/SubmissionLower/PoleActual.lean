import ProximityPrize.SubmissionLower.SourceColumn
import ProximityPrize.SubmissionLower.PoleImage
import ProximityPrize.SubmissionLower.ProjectivePole
import ProximityPrize.SubmissionLower.PoleSourceSpan

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 24
set_option maxHeartbeats 1400000

namespace PoleActual

open K1_14 (Shape)
open K1_14_1 (jetConstant otherBlock)
open K1_14_1_7
open K1_14_1_7_2 (centered zeroSubst substitute_base substitute_ordinate substitute_velocity)
open PoleSourceSpan PoleImage
open Polynomial
open scoped BigOperators Polynomial

noncomputable section

abbrev Target (F : Type) [Field F] := JetPolys (SeedFrac F)

abbrev abscissa (F : Type) [Field F] : Target F :=
  jetConstant (Polynomial.X (R := SeedFrac F))

abbrev ordinate (F : Type) [Field F] : Target F :=
  Polynomial.C (Polynomial.X (R := (SeedFrac F)[X]))

abbrev velocity (F : Type) [Field F] : Target F := Polynomial.X

def ringMap {F : Type} [Field F] (α : F) (z : SeedFrac F) :
    TrueSource F →+* Target F :=
  zeroSubst.comp (centered α z)

theorem ringMap_base {F : Type} [Field F] (α : F) (z : SeedFrac F) (p : (Seed F)[X]) :
    ringMap α z (jetConstant p) =
      jetConstant (Polynomial.taylor (algebraMap F (SeedFrac F) α)
        (p.map (algebraMap (Seed F) (SeedFrac F)))) := by
  simp [ringMap, centered, zeroSubst]

theorem ringMap_seed {F : Type} [Field F] (α : F) (z : SeedFrac F) (p : Seed F) :
    ringMap α z (sourceSeed p) =
      algebraMap (SeedFrac F) (Target F) (algebraMap (Seed F) (SeedFrac F) p) := by
  change ringMap α z (jetConstant (C p)) = _
  rw [ringMap_base, Polynomial.map_C, Polynomial.taylor_C]
  rfl

theorem ringMap_X {F : Type} [Field F] (α : F) (z : SeedFrac F) :
    ringMap α z (sourceX α) = abscissa F := by
  change ringMap α z (jetConstant (Polynomial.X - C (algebraMap F (Seed F) α))) = _
  rw [ringMap_base, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  simp [Polynomial.taylor_X, IsScalarTower.algebraMap_apply F (Seed F) (SeedFrac F)]

theorem ringMap_Y {F : Type} [Field F] (α : F) (z : SeedFrac F) :
    ringMap α z sourceY = algebraMap (SeedFrac F) (Target F) z + abscissa F * ordinate F := by
  simp only [ringMap, RingHom.comp_apply, centered, substitute_ordinate, zeroSubst, map_add,
    substitute_base]
  exact add_comm _ _

theorem ringMap_V {F : Type} [Field F] (α : F) (z : SeedFrac F) :
    ringMap α z sourceV = ordinate F + abscissa F * velocity F := by
  simp only [ringMap, RingHom.comp_apply, centered, substitute_velocity, zeroSubst]
  exact add_comm _ _

def algMap {F : Type} [Field F] (α : F) (z : SeedFrac F) :
    TrueSource F →ₐ[F] Target F where
  toRingHom := ringMap α z
  commutes' f := by
    change ringMap α z (sourceSeed (algebraMap F (Seed F) f)) = _
    rw [ringMap_seed]
    simp only [← IsScalarTower.algebraMap_apply]

def localMap {F : Type} [Field F] (s : Shape) (α : F) (z : SeedFrac F) :
    TrueSource F →ₗ[F] (Target F) ⧸ CutIdeal (abscissa F) (s.B+s.J) :=
  ((Ideal.Quotient.mkₐ F (CutIdeal (abscissa F) (s.B+s.J))).comp (algMap α z)).toLinearMap

/-- The zero class of the local map is the simple-pole divisibility test. -/
theorem localMap_zero_iff {F : Type} [Field F] (s : Shape) (α : F) (z : SeedFrac F)
    (P : TrueSource F) :
    localMap s α z P = 0 ↔
      (jetConstant ((Polynomial.X (R := SeedFrac F))^(s.B+s.J)) : Target F) ∣
        zeroSubst (centered α z P) := by
  change Ideal.Quotient.mk (CutIdeal (abscissa F) (s.B+s.J))
    (zeroSubst (centered α z P)) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, map_pow]


def seedValue {F : Type} [Field F] (side : Fin 2) : Target F :=
  algebraMap (SeedFrac F) (Target F)
    (algebraMap (Seed F) (SeedFrac F) (MvPolynomial.X side))

def chartEval {F : Type} [Field F] (z : SeedFrac F) :
    MvPolynomial (Fin 4) F →ₐ[F] Target F :=
  MvPolynomial.aeval ![abscissa F, ordinate F, velocity F, algebraMap (SeedFrac F) (Target F) z]

def sliceWeight {F : Type} [Field F] (side : Fin 2) (b c : F) (U : ℕ)
    (u : Fin (U+1)) : Target F :=
  seedValue (otherBlock side)^u.val *
    (algebraMap F (Target F) b + algebraMap F (Target F) c * seedValue side)^(U-u.val)

private theorem residue_eq {F : Type} [Field F] (side : Fin 2) (a b c : F) (hb : b ≠ 0) :
    algebraMap F (Target F) a * seedValue side =
      (algebraMap F (Target F) b + algebraMap F (Target F) c * seedValue side) *
        algebraMap (SeedFrac F) (Target F) (residue side a b c) := by
  let z := algebraMap (Seed F) (SeedFrac F) (MvPolynomial.X side)
  let d := algebraMap F (SeedFrac F) b + algebraMap F (SeedFrac F) c * z
  have hd : d ≠ 0 := (ProjectivePole.evaluate_column side a b c hb 0 0 le_rfl).1
  have h : algebraMap F (SeedFrac F) a * z = d * residue side a b c := by
    change _ = d * ((algebraMap F (SeedFrac F) a * z) / d)
    field_simp
  have hm := congrArg (algebraMap (SeedFrac F) (Target F)) h
  dsimp [d,z,seedValue] at hm ⊢
  simpa only [map_mul,map_add, ← IsScalarTower.algebraMap_apply] using hm

theorem localMap_mem_normalized_range {F : Type} [Field F] (s : Shape) (α : F)
    (side : Fin 2) (a b c : F) (ha : a ≠ 0) (hb : b ≠ 0)
    {P : TrueSource F} (hP : Shaped s P) :
    localMap s α (residue side a b c) P ∈
      (postcompose s.U s.B s.J (abscissa F) (chartEval (residue side a b c))
        (sliceWeight side b c s.U)).range := by
  let z := residue side a b c
  let f := localMap s α z
  let S := (postcompose s.U s.B s.J (abscissa F) (chartEval z)
    (sliceWeight side b c s.U)).range
  change P ∈ S.comap f
  apply (Submodule.span_le.mpr ?_) (shaped_mem_span α side hP)
  rintro _ ⟨t,i,u,q,j,hq,hj,hi,rfl⟩
  let v : Fin (s.U+1) := ⟨u, by omega⟩
  have hx := SourceColumn.original_column s.U s.B s.J a b c ha hb
    (seedValue side) (algebraMap (SeedFrac F) (Target F) z) (seedValue (otherBlock side))
    (abscissa F) (ordinate F) (velocity F) (residue_eq side a b c hb)
    v t q j i hq (hj.trans (min_le_right _ _)) (hj.trans (min_le_left _ _)) (by dsimp [v]; omega)
  change f (centeredMonomial α side t i u q j) ∈ S
  change Ideal.Quotient.mk (CutIdeal (abscissa F) (s.B+s.J))
    (ringMap α z (centeredMonomial α side t i u q j)) ∈ S
  rw [centeredMonomial]
  simp only [map_mul, map_pow, ringMap_X, ringMap_seed, ringMap_Y, ringMap_V]
  change Ideal.Quotient.mk (CutIdeal (abscissa F) (s.B+s.J))
    (abscissa F ^ t * seedValue side ^ i * seedValue (otherBlock side) ^ u *
      (algebraMap (SeedFrac F) (Target F) z + abscissa F * ordinate F) ^ (q-j) *
      (ordinate F + abscissa F * velocity F) ^ j) ∈ S
  convert hx using 2
  · rfl
  · have hv : v.val = u := rfl
    rw [hv]
    ring

/-- The actual local normalized image of any shaped family has rank at most
the sum of the passive, grade and offset block bounds. -/
theorem local_image_span_rank_le {F : Type} [Field F] {ι : Type*} (s : Shape) (α : F)
    (side : Fin 2) (a b c : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (P : ι → TrueSource F) (hP : ∀ i, Shaped s (P i)) :
    Module.finrank F (Submodule.span F (Set.range (localMap s α (residue side a b c) ∘ P))) ≤
      ∑ u : Fin (s.U+1), ∑ n : Fin (s.B+(s.U-u.val)+1), ∑ h : Fin (s.B+2*s.J),
        PoleFamily.blockBound ⟨u,n,h⟩ := by
  let z := residue side a b c
  let g := postcompose s.U s.B s.J (abscissa F) (chartEval z) (sliceWeight side b c s.U)
  have hincl : Submodule.span F (Set.range (localMap s α z ∘ P)) ≤ g.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact localMap_mem_normalized_range s α side a b c ha hb (hP i)
  exact (Submodule.finrank_mono hincl).trans
    (postcompose_rank_le_sum s.U s.B s.J (abscissa F) (chartEval z) (sliceWeight side b c s.U)
      (by simp [chartEval]))

end
end PoleActual
