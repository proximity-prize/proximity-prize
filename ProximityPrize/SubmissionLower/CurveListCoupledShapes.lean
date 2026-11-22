import ProximityPrize.SubmissionLower.CurveListCoupledCap

set_option Elab.async false
set_option autoImplicit false

namespace CurveListCoupledCap
noncomputable section
open K1_13 (Shape)
open K1_13_5_4_2_4 (Exponent exponentVector latticeBody)
open scoped BigOperators Pointwise
open private K1_13_5_4_2_5.sumShape from ProximityPrize.SubmissionLower.Fast048

abbrev shapeBody (s : Shape) (h : ℕ) : Set Space := body s.b s.j s.t h
abbrev shapeSupport (s : Shape) (h : ℕ) : Finset Exponent := exponents s.b s.j s.t h

def ShapeOK (s : Shape) (h : ℕ) : Prop := 2*h ≤ s.t ∧ 2*s.t ≤ s.j ∧ s.j ≤ s.b

theorem shape_chamber {s : Shape} {h : ℕ} (hs : ShapeOK s h) : Chamber s.b s.j s.t h := by
  obtain ⟨hc,hj,hb⟩ := hs
  exact ⟨by positivity,by exact_mod_cast hc,by exact_mod_cast hj,by exact_mod_cast hb⟩

theorem lattice_shapeBody {s : Shape} {h : ℕ} (hs : ShapeOK s h) :
    latticeBody (shapeSupport s h) = shapeBody s h :=
  lattice_exponents _ _ _ _ hs.1 hs.2.1 hs.2.2

theorem shape_polytope {s : Shape} {h : ℕ} (hs : ShapeOK s h) :
    ∃ v : Finset Space, shapeBody s h = convexHull ℝ (v : Set Space) := by
  classical
  refine ⟨(shapeSupport s h).image exponentVector, ?_⟩
  rw [← lattice_shapeBody hs, latticeBody, Finset.coe_image]

theorem zero_mem_shapeBody (s : Shape) (h : ℕ) : 0 ∈ shapeBody s h := by
  change (∀ i : Fin 4, (0 : ℝ) ≤ 0) ∧ 0+0+0+0 ≤ (s.b : ℝ) ∧
    0+2*0+3*0 ≤ (s.j : ℝ) ∧ 0+2*0 ≤ (s.t : ℝ) ∧ 0 ≤ (h : ℝ)
  simp

theorem shape_zero : shapeBody ⟨0,0,0⟩ 0 = 0 := by
  ext x
  rw [show (0 : Set Space) = {0} from rfl, Set.mem_singleton_iff]
  simp only [shapeBody,Nat.cast_zero]
  constructor
  · rintro ⟨hn,hb,_,_,_⟩
    have hsum : (∑ j : Fin 4, x j) ≤ 0 := by simpa only [Fin.sum_univ_four] using hb
    funext i
    exact le_antisymm ((Finset.single_le_sum (f := x) (fun j _ => hn j) (Finset.mem_univ i)).trans hsum) (hn i)
  · rintro rfl
    simpa only [shapeBody,Nat.cast_zero] using zero_mem_shapeBody ⟨0,0,0⟩ 0

theorem sum_shapeOK {ι : Type} (S : Finset ι) (p : ι → Shape) (h : ι → ℕ)
    (hp : ∀ i, ShapeOK (p i) (h i)) : ShapeOK (K1_13_5_4_2_5.sumShape S p) (∑ i ∈ S, h i) := by
  obtain hsum := fun (f g : ι → ℕ) (H : ∀ i, f i ≤ g i) =>
    Finset.sum_le_sum (s := S) (fun i _ => H i)
  refine ⟨?_,?_,hsum _ _ (fun i => (hp i).2.2)⟩
  · change 2 * (∑ i ∈ S, h i) ≤ ∑ i ∈ S, (p i).t
    rw [Finset.mul_sum]
    exact hsum _ _ (fun i => (hp i).1)
  · change 2 * (∑ i ∈ S, (p i).t) ≤ ∑ i ∈ S, (p i).j
    rw [Finset.mul_sum]
    exact hsum _ _ (fun i => (hp i).2.1)

theorem sum_shapeBody {ι : Type} (S : Finset ι) (p : ι → Shape) (h : ι → ℕ)
    (hp : ∀ i, ShapeOK (p i) (h i)) :
    (∑ i ∈ S, shapeBody (p i) (h i)) = shapeBody (K1_13_5_4_2_5.sumShape S p) (∑ i ∈ S, h i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [K1_13_5_4_2_5.sumShape,Finset.sum_empty,shape_zero]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi,ih]
    change body _ _ _ _ + body _ _ _ _ = body _ _ _ _
    rw [← body_add (shape_chamber (hp i)) (shape_chamber (sum_shapeOK S p h hp))]
    simp only [K1_13_5_4_2_5.sumShape, Finset.sum_insert hi, Nat.cast_add]

end
end CurveListCoupledCap
