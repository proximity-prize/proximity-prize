import ProximityPrize.SubmissionBinaryLower.B6402SeedCoordinates
import ProximityPrize.SubmissionBinaryLower.B6402QuotientDimension

/-! A kernel vector outside the seed-bounded multiple space gives a
proper slope resultant over the generic seed field. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402QuotientSpace

open Polynomial B6401ContactKerD B6401QuotInterp B6401ResLineOrd
open B6402MixedDegree B6402Cofactor B6402SeedCoordinates B6402QuotientDimension
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
variable {K : Type*} [Field K]

abbrev Slots (wY W s q T : ℕ) := Indices (width (wY:=wY) (W:=W) (s:=s) q T)
local notation "CP" => ContactPoly (Polynomial K)

noncomputable def read (wY W s q T : ℕ) (p : CP) (j : Slots wY W s q T) : K :=
  (coord p j.1).coeff j.2.val

theorem read_source {wY W s q T : ℕ} (hw : 0<wY) (u : Slots wY W s q T → K) :
    read wY W s q T (source q T u) = u := by
  funext j
  unfold read source
  rw [coord_sum hw]
  exact decode_coeff _ _ _ _

private theorem read_add (wY W s q T : ℕ) (p g : CP) :
    read wY W s q T (p+g) = read wY W s q T p + read wY W s q T g := by
  funext j
  simp [read,coord]

private theorem read_smul (wY W s q T : ℕ) (a : K) (p : CP) :
    read wY W s q T (cC (C a)*p) = a • read wY W s q T p := by
  funext j
  simp [read,coord,cC,coeff_C_mul]

noncomputable def multiples (f : CP) (wY W s q T : ℕ) :
    (Slots wY (W-wdeg wY f) (s-f.natDegree) q (T-mixed q f) → K) →ₗ[K] (Slots wY W s q T → K) where
  toFun u := read wY W s q T (f * source q (T-mixed q f) u)
  map_add' u v := by rw [source_add,mul_add,read_add]
  map_smul' a u := by
    rw [source_smul,mul_left_comm f _ _,read_smul]; rfl

theorem proper_resultant [CharP K 2] (f : CP) (wY W s q T : ℕ) (hw : 0<wY)
    (hirr : Irreducible f) (hR : 0<f.natDegree) (dF : contactDeriv f=0)
    (hirrK : Irreducible (liftCRat f))
    (u : Slots wY W s q T → K) (outside : u ∉ LinearMap.range (multiples f wY W s q T)) :
    resultant f (source q T u) f.natDegree s ≠ 0 := by
  classical
  let G := source q T u
  obtain ⟨gD,gs,gW,gT⟩ := source_bounds hw u
  have eg : read wY W s q T G = u := read_source hw u
  have gne : G ≠ 0 := by
    intro h
    have hu : u=0 := by rw [←eg,h]; funext j; simp [read,coord]
    exact outside (hu ▸ Submodule.zero_mem _)
  apply resultant_ne_zero_of_not_dvd f G f.natDegree s hirrK rfl hR gs gne
  rintro ⟨c,h⟩
  obtain ⟨p,hp,pD,ps,pW,pT⟩ := bounded_cofactor hirr hR gne dF gD q T wY W s gs gW gT ⟨c,h⟩
  obtain ⟨v,hv⟩ := source_spans hw p pD ps pW pT
  apply outside
  refine ⟨v,?_⟩
  change read wY W s q T (f*source q (T-mixed q f) v)=u
  rw [hv,←hp,eg]

#print axioms proper_resultant
end ProximityPrize.SubmissionBinaryLower.B6402QuotientSpace
