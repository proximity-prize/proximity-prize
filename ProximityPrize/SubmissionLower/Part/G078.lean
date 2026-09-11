import ProximityPrize.SubmissionLower.Part.G077


section Compact_SecondJetRelaxedGlobalIndex
/-! A finite global monomial family with separate weight budgets by S degree. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalIndex
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

def budget (D : ℕ → ℕ) (w h r : ℕ) := D h-(w-2)*h-(w-1)*r
def yCount (D : ℕ → ℕ) (w U h r : ℕ) :=
  min ((budget D w h r-1)/w+1) (U+1-h-r)
abbrev Index (D : ℕ → ℕ) (w L B s U : ℕ) :=
  Σ h : Fin (s+1), Σ r : Fin (B-2*h.val+1), Σ y : Fin (yCount D w U h.val r.val),
    Fin (budget D w h.val r.val-w*y.val) × Fin (L+1-h.val-r.val-y.val)

def exponent {D : ℕ → ℕ} {w L B s U : ℕ} (i : Index D w L B s U) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    ![i.2.2.2.1.val,i.1.val,i.2.2.1.val,i.2.1.val,i.2.2.2.2.val]

theorem exponent_injective (D : ℕ → ℕ) (w L B s U : ℕ) :
    Function.Injective (exponent (D := D) (w := w) (L := L) (B := B) (s := s) (U := U)) := by
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

theorem exponent_bounds (D : ℕ → ℕ) (w L B s U : ℕ) (hsB : 2*s ≤ B)
    (i : Index D w L B s U) :
    2*exponent i 1+exponent i 3 ≤ B ∧ exponent i 1 ≤ s ∧
      exponent i 1+exponent i 2+exponent i 3 ≤ U ∧
      exponent i 1+exponent i 2+exponent i 3+exponent i 4 ≤ L ∧
      exponent i 0+w*exponent i 2+(w-1)*exponent i 3+(w-2)*exponent i 1 < D (exponent i 1) := by
  rcases i with ⟨h,r,y,x,z⟩
  have hh := h.isLt
  have hr := r.isLt
  have hy := y.isLt
  have hx := x.isLt
  have hz := z.isLt
  simp only [budget] at hx
  simp only [yCount] at hy
  simp [exponent]
  omega

theorem card_index (D : ℕ → ℕ) (w L B s U : ℕ) :
    Fintype.card (Index D w L B s U) =
      ∑ h : Fin (s+1), ∑ r : Fin (B-2*h.val+1), ∑ y : Fin (yCount D w U h.val r.val),
        (budget D w h.val r.val-w*y.val)*(L+1-h.val-r.val-y.val) := by
  simp [Index]

variable {K N : Type*} [Field K] [Fintype N]
theorem exists_weighted_global_contact (D : ℕ → ℕ) (w L B s U m : ℕ)
    (hsB : 2*s ≤ B) (hw : 2 ≤ w) (x u0 u1 : N → K)
    (hcard : Fintype.card N*SecondJetRelaxedGlobalMap.rankBound m L B s U
      (fun h => (D h+B-1)/w) < Fintype.card (Index D w L B s U)) :
    ∃ P : SecondJetSupport.Poly (K := K), P ≠ 0 ∧
      (∀ d ∈ P.support, 2*d 1+d 3 ≤ B ∧ d 1 ≤ s ∧ d 1+d 2+d 3 ≤ U ∧
        d 1+d 2+d 3+d 4 ≤ L ∧ d 0+w*d 2+(w-1)*d 3+(w-2)*d 1 < D (d 1)) ∧
      ∀ n, Polynomial.X^m ∣ SecondJetLocal.contact (K := K)
        (SecondJetSupport.flatEquiv (K := K)
          (SecondJetGlobalSupport.localize (x n) (u0 n) (u1 n) P)) := by
  obtain ⟨P,hP,hPex,hcontact⟩ := SecondJetRelaxedGlobalMap.exists_global_contact
    exponent (exponent_injective D w L B s U) m L B s U w D hw
    (fun i => (exponent_bounds D w L B s U hsB i).1)
    (fun i => (exponent_bounds D w L B s U hsB i).2.1)
    (fun i => (exponent_bounds D w L B s U hsB i).2.2.1)
    (fun i => (exponent_bounds D w L B s U hsB i).2.2.2.1)
    (fun i => (exponent_bounds D w L B s U hsB i).2.2.2.2) x u0 u1 hcard
  refine ⟨P,hP,?_,hcontact⟩
  intro d hd
  obtain ⟨i,rfl⟩ := hPex d hd
  exact exponent_bounds D w L B s U hsB i

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedGlobalIndex

end Compact_SecondJetRelaxedGlobalIndex
