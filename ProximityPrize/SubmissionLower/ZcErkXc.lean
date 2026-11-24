import ProximityPrize.SubmissionLower.Zmk5EEe
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qrsE1ie
noncomputable section
open Polynomial Finset
open P5 (K I p)




open quN7Z4a (Sheet physicalWeight compressionWidth)

open gT (kM)
open Cu (sQ oO)


open scoped Classical
def c1 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)]
    (J:Ideal kM) (T:Finset K) (z :K→K) (s :K→K[X])
    (D H :ℕ) (S:Sheet C₀ J 2 H T z s),
    0<D→ compressionWidth D 2≤physicalWeight D S.root.equation →
    Set.InjOn z (T:Set K)→(∀ γ∈T,(s γ).natDegree≤D) →
    T.card≤5*H
def c2 :Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)]
    (J:Ideal kM) (T:Finset K) (z :K→K) (s :K→K[X])
    (H :ℕ) (S:Sheet C₀ J 2 H T z s),
    (discriminant S.root.equation).natDegree<p → ¬geomSquare S.root.equation →
    Set.InjOn z (T:Set K)→T.card≤11*H
def c3:Prop :=
  ∀ (C₀:sQ) [Fact (Irreducible C₀)]
    (J:Ideal kM) (T:Finset K) (z :K→K) (s :K→K[X]) (w:I→K)
    (H :ℕ) (S:Sheet C₀ J 2 H T z s),
    geomSquare S.root.equation→Set.InjOn z (T:Set K) →
    Nonempty (CoverIncidence T s w H)
private theorem disc_degree {C₀:sQ} (D:ℕ)
  (f : ((oO C₀)[X])[X]) :
  (discriminant f).natDegree≤2*physicalWeight D f := by
 have hc (i:ℕ) : (f.coeff i).natDegree≤physicalWeight D f := by
  by_cases h:f.coeff i=0
  · simp [h]
  exact (Nat.le_add_right _ _).trans
    (Finset.le_sup (f := fun j=>(f.coeff j).natDegree+j*D) (mem_support_iff.mpr h))
 have hm: (f.coeff 2*f.coeff 0).natDegree≤2*physicalWeight D f := by
  exact natDegree_mul_le.trans (by simpa only [two_mul] using Nat.add_le_add (hc 2) (hc 0))
 unfold discriminant
 exact (natDegree_sub_le _ _).trans (max_le (natDegree_pow_le_of_le 2 (hc 1))
  ((natDegree_C_mul_le _ _).trans hm))
end
end qrsE1ie
