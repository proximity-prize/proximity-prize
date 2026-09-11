import ProximityPrize.SubmissionLower.Part.G026


section Compact_SecondJetGlobalIndex
/-! Finite coefficient indices for the weighted global second-jet space. -/
namespace ProximityPrize.SubmissionLower.SecondJetGlobalIndex
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

def budget (D w h r : ℕ) := D-(w-2)*h-(w-1)*r
def yCount (D w h r : ℕ) := (budget D w h r-1)/w+1
abbrev Index (D w L B s : ℕ) :=
  Σ h : Fin (s+1), Σ r : Fin (B-h.val+1), Σ y : Fin (yCount D w h.val r.val),
    Fin (budget D w h.val r.val-w*y.val) × Fin (L+1-h.val-r.val-y.val)

def exponent {D w L B s : ℕ} (i : Index D w L B s) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    ![i.2.2.2.1.val,i.1.val,i.2.2.1.val,i.2.1.val,i.2.2.2.2.val]

theorem exponent_injective (D w L B s : ℕ) :
    Function.Injective (exponent (D := D) (w := w) (L := L) (B := B) (s := s)) := by
  rintro ⟨h,r,y,x,z⟩ ⟨h',r',y',x',z'⟩ he
  have hv : ∀ k : Fin 5, ![x.val,h.val,y.val,r.val,z.val] k =
      ![x'.val,h'.val,y'.val,r'.val,z'.val] k := by
    intro k
    simpa [exponent] using congrArg (fun d : Fin 5 →₀ ℕ => d k) he
  have hh : h = h' := Fin.ext (hv 1)
  subst h'
  have hr : r = r' := Fin.ext (hv 3)
  subst r'
  have hy : y = y' := Fin.ext (hv 2)
  subst y'
  have hx : x = x' := Fin.ext (hv 0)
  have hz : z = z' := Fin.ext (hv 4)
  subst x'
  subst z'
  rfl

theorem exponent_bounds (D w L B s : ℕ) (hsB : s ≤ B) (i : Index D w L B s) :
    exponent i 1+exponent i 3 ≤ B ∧ exponent i 1 ≤ s ∧
      exponent i 1+exponent i 2+exponent i 3+exponent i 4 ≤ L ∧
      exponent i 0+w*exponent i 2+(w-1)*exponent i 3+(w-2)*exponent i 1 < D := by
  rcases i with ⟨h,r,y,x,z⟩
  have hh := h.isLt
  have hr := r.isLt
  have hx := x.isLt
  have hz := z.isLt
  simp only [budget] at hx
  simp [exponent]
  omega

theorem card_index (D w L B s : ℕ) :
    Fintype.card (Index D w L B s) =
      ∑ h : Fin (s+1), ∑ r : Fin (B-h.val+1), ∑ y : Fin (yCount D w h.val r.val),
        (budget D w h.val r.val-w*y.val)*(L+1-h.val-r.val-y.val) := by
  simp [Index]

variable {K N : Type*} [Field K] [Fintype N]
theorem exists_weighted_global_contact (D w L B s m : ℕ) (hsB : s ≤ B) (hLm : m+B+s ≤ L)
    (x u0 u1 : N → K)
    (hcard : Fintype.card N*SecondJetFacetCounts.rankBound m L B s < Fintype.card (Index D w L B s)) :
    ∃ P : SecondJetSupport.Poly (K := K), P ≠ 0 ∧
      (∀ d ∈ P.support, d 1+d 3 ≤ B ∧ d 1 ≤ s ∧ d 1+d 2+d 3+d 4 ≤ L ∧
        d 0+w*d 2+(w-1)*d 3+(w-2)*d 1 < D) ∧
      ∀ n, Polynomial.X^m ∣ SecondJetLocal.contact (K := K)
        (SecondJetSupport.flatEquiv (K := K)
          (SecondJetGlobalSupport.localize (x n) (u0 n) (u1 n) P)) := by
  obtain ⟨P,hP,hPex,hcontact⟩ := SecondJetGlobalMap.exists_global_contact
    exponent (exponent_injective D w L B s) m L B s hsB hLm
    (fun i => (exponent_bounds D w L B s hsB i).1)
    (fun i => (exponent_bounds D w L B s hsB i).2.1)
    (fun i => (exponent_bounds D w L B s hsB i).2.2.1) x u0 u1 hcard
  refine ⟨P,hP,?_,hcontact⟩
  intro d hd
  obtain ⟨i,rfl⟩ := hPex d hd
  exact exponent_bounds D w L B s hsB i

end
end ProximityPrize.SubmissionLower.SecondJetGlobalIndex

end Compact_SecondJetGlobalIndex
