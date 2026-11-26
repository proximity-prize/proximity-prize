import ProximityPrize.SubmissionBinaryLower.B6402ExceptionalSupport
import ProximityPrize.SubmissionBinaryLower.B6402PrimarySystem

namespace ProximityPrize.SubmissionBinaryLower.B6402ExceptionalInterpolation
open Polynomial P64Found B6401ContactKerD B6401QuotInterp B6402SeedCoordinates B6402QuotientSpace
open B6402PrimarySystem B6402ExceptionalSystem B6402ExceptionalSupport B6402ExceptionalFibres
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
variable {K : Type*} [Field K]
noncomputable local instance : CommRing (Polynomial K) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing (Polynomial (Polynomial K)) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing (Fibre K) := AddMonoidAlgebra.commRing
noncomputable local instance : CommRing ((Fibre K)[X]) := AddMonoidAlgebra.commRing

abbrev ACols (K : Type*) (s J T H d b : ℕ) := B6402ExceptionalSystem.Aux K b (auxBox s J T H d)
abbrev Eqs (K : Type*) (s J T H b : ℕ) := B6402ExceptionalSystem.Aux K b (testBox s J T H)

noncomputable def localSource {w W s q T : ℕ} (x : K) (y : K[X]) :
    Global K w W s q T →ₗ[K] (Fibre K)[X] where
  toFun u := localized x y (decode (width q T) u)
  map_add' u v := by simp only [localized,decode_add,locC,map_add,add_mul,Finset.sum_add_distrib]
  map_smul' c u := by
    simp only [localized,decode_smul,locC,map_mul,mul_assoc,←Finset.mul_sum]
    rw [Algebra.smul_def]; rfl

variable {U : Type*} [AddCommGroup U] [Module K U]
variable {s J T H d b : ℕ}

noncomputable def quotient (i : ℕ) : (U × ACols K s J T H d b) →ₗ[K] Fibre K :=
  if hi : i<b then
    (comb3 (auxBox s J T H d i)).comp ((LinearMap.proj (⟨i,hi⟩ : Fin b)).comp (LinearMap.snd K _ _))
  else 0

noncomputable def tests (F : (Fibre K)[X]) (a L : Fibre K) (g : U →ₗ[K] (Fibre K)[X]) :
    (U × ACols K s J T H d b) →ₗ[K] Eqs K s J T H b :=
  equations F a L (g.comp (LinearMap.fst K _ _)) quotient b (testBox s J T H)

theorem quotient_bounds (u : U × ACols K s J T H d b) (i : ℕ) (hi : i<b) :
    Bounds (quotient i u) (s+3*i) (J+5*i-d) (T+i*H-H) := by
  apply (in_box _ _ _ _).mp
  rw [quotient,dite_eq_left hi]
  change comb3 (auxBox s J T H d i) (u.2 ⟨i,hi⟩) ∈ supp (auxBox s J T H d i)
  exact comb3_mem_supp _ _

theorem detects (F : (Fibre K)[X]) (a L : Fibre K) (g : U →ₗ[K] (Fibre K)[X])
    (v : U × ACols K s J T H d b) (hH : H≤T) (hd : d≤J)
    (hF : ∀ j, Bounds (F.coeff (j+1)) (3*(j+1)) 5 H)
    (ha : Bounds a 0 5 0) (hL : Bounds L 0 d H)
    (hG : ∀ j, Bounds ((g v.1).coeff j) (s+3*j) J T)
    (zero : tests F a L g v=0) : remainderConditions F a L b (g v.1) :=
  by
    let gg := g.comp (LinearMap.fst K U (ACols K s J T H d b))
    let qq := quotient (K:=K) (U:=U) (s:=s) (J:=J) (T:=T) (H:=H) (d:=d) (b:=b)
    have cov := covered F a L gg qq v s J T H d b hH hd hF ha hL hG (quotient_bounds v)
    exact kernel_remainder F a L gg qq b (testBox s J T H) v cov zero

theorem unique_aux (F : (Fibre K)[X]) (a L : Fibre K) (g : U →ₗ[K] (Fibre K)[X])
    (v : U × ACols K s J T H d b) (hH : H≤T) (hd : d≤J) (hLne : L≠0)
    (hF : ∀ j, Bounds (F.coeff (j+1)) (3*(j+1)) 5 H)
    (ha : Bounds a 0 5 0) (hL : Bounds L 0 d H)
    (hG : ∀ j, Bounds ((g v.1).coeff j) (s+3*j) J T)
    (zero : tests F a L g v=0) (hg : g v.1=0) : v.2=0 := by
  funext i c
  let gg := g.comp (LinearMap.fst K U (ACols K s J T H d b))
  let qq := quotient (K:=K) (U:=U) (s:=s) (J:=J) (T:=T) (H:=H) (d:=d) (b:=b)
  have cov := covered F a L gg qq v s J T H d b hH hd hF ha hL hG (quotient_bounds v)
  have hz := zero_quotients F a L hLne gg qq b (testBox s J T H) v cov zero hg i.val i.isLt
  have hq : comb3 (auxBox s J T H d i) (v.2 i)=0 := by
    simpa only [qq,quotient,dite_eq_left i.isLt,LinearMap.comp_apply,LinearMap.proj_apply,LinearMap.snd_apply] using hz
  have eq := congrArg (extr3 (auxBox s J T H d i)) hq
  rw [extr3_comb3,map_zero] at eq
  exact congrFun eq c

#print axioms localSource
#print axioms detects
#print axioms unique_aux
end ProximityPrize.SubmissionBinaryLower.B6402ExceptionalInterpolation
