import ProximityPrize.SubmissionBinaryLower.B6402FilteredJets
import ProximityPrize.SubmissionBinaryLower.B6402MixedDegree

/-! Seed-degree bounds in the local quotient equations at q=1 and q=2.
The input weight includes the ordinate and the slope. -/

namespace ProximityPrize.SubmissionBinaryLower.B6402ProductJets
open Polynomial B6401ContactKerD B6401QuotInterp B6402FilteredJets
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

/-- The zero coefficient consumes no seed variables, whatever its row weight. -/
def Fits (p : K[X]) (out cap : ℕ) : Prop := p ≠ 0 → p.natDegree+out≤cap

private theorem fits_add {p r : K[X]} {out cap : ℕ} (hp : Fits p out cap)
    (hr : Fits r out cap) : Fits (p+r) out cap := by
  intro hn
  by_cases h : p=0
  · subst p; simpa using hr (by simpa using hn)
  by_cases h' : r=0
  · subst r; simpa using hp h
  have a:=hp h; have b:=hr h'; have := natDegree_add_le p r; omega

private theorem fits_sum {ι : Type*} (s : Finset ι) (f : ι → K[X]) {o c : ℕ}
    (h : ∀ i∈s, Fits (f i) o c) : Fits (∑ i ∈ s,f i) o c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Fits]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact fits_add (h a (Finset.mem_insert_self _ _))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

private theorem fits_comp {p r : K[X]} {h k o c : ℕ} (hp : Fits p h k)
    (hr : Fits r o (h+c)) : Fits (p*r) o (k+c) := by
  intro hn
  have a:=hp (left_ne_zero_of_mul hn); have b:=hr (right_ne_zero_of_mul hn)
  have := natDegree_mul_le (p:=p) (q:=r); omega

private theorem fits_shift {p r : K[X]} {o c a : ℕ} (hp : p.natDegree≤a)
    (hr : Fits r o c) : Fits (p*r) o (a+c) := by
  apply fits_comp (h:=0) (k:=a)
  · simpa [Fits] using (fun _ : p ≠ 0 => hp)
  · simpa using hr

private theorem fits_mono {p : K[X]} {o c d : ℕ} (h : Fits p o c) (hcd : c≤d) :
    Fits p o d := fun hn => (h hn).trans hcd

private theorem reduced (m s q j a b dy : ℕ) (idx : LocalBasisIdx m s) :
    Fits ((reduceMonomialCoords m s q j a b idx : ℕ) : K[X])
      (dy*localWeight idx.1) (dy*(q+j+2*b)) := by
  intro hn
  have hr : reduceMonomialCoords m s q j a b idx≠0 := by intro h; simp [h] at hn
  simp [reduction_preserves_weight m s q j a b idx hr]

private theorem tail (m s q j a b dy r : ℕ) (idx : LocalBasisIdx m s)
    (x : K) (y : K[X]) (hy : y.natDegree ≤ dy) (hr : r<2) :
    Fits (if r=0 then ((reduceMonomialCoords m s q j a b idx : ℕ) : K[X])
          else y*((reduceMonomialCoords m s q j a b idx : ℕ) : K[X]) +
            C x*((reduceMonomialCoords m s q (j+1) a b idx : ℕ) : K[X]) +
            ((reduceMonomialCoords m s (q+1) j a b idx : ℕ) : K[X]))
      (dy*localWeight idx.1) (dy*(q+j+2*b+r)) := by
  rcases (show r=0 ∨ r=1 by omega) with rfl|rfl
  · simpa using reduced m s q j a b dy idx
  · simp only [one_ne_zero,↓reduceIte]
    apply fits_add
    · apply fits_add
      · convert fits_shift hy (reduced m s q j a b dy idx) using 1; ring
      · have h:=fits_shift (p:=C x) (a:=0) (by simp) (reduced m s q (j+1) a b dy idx)
        convert h using 1; ring
    · convert reduced (K:=K) m s (q+1) j a b dy idx using 1; ring

/-- One shifted global basis element times a local multiplier basis element.
The two indicated grades bound its nonzero output coefficient. -/
private theorem entry (m s dy k r b a u j v c : ℕ) (idx : LocalBasisIdx m s)
    (x : K) (y : K[X]) (hy : y.natDegree≤dy) (hr : r<2) :
    Fits (∑ i ∈ Finset.range (a+1), ∑ h ∈ Finset.range (b+1),
      (Nat.choose a i : K[X]) * (C x ^ 2) ^ (a-i) *
        ((Nat.choose b h : K[X]) * (y^2)^(b-h)) *
        (if r=0 then ((reduceMonomialCoords m s u (k+j) (i+v) (h+c) idx : ℕ) : K[X])
         else y*((reduceMonomialCoords m s u (k+j) (i+v) (h+c) idx : ℕ) : K[X]) +
           C x*((reduceMonomialCoords m s u (k+1+j) (i+v) (h+c) idx : ℕ) : K[X]) +
           ((reduceMonomialCoords m s (u+1) (k+j) (i+v) (h+c) idx : ℕ) : K[X])))
       (dy*localWeight idx.1) (dy*(2*b+r+k)+dy*(u+j+2*c)) := by
  apply fits_sum; intro i _
  apply fits_sum; intro h hh
  have hb : h≤b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
  have hx : ((Nat.choose a i : K[X])*(C x^2)^(a-i)).natDegree=0 := by
    rw [show ((Nat.choose a i : K[X])*(C x^2)^(a-i))=C ((Nat.choose a i : K)*(x^2)^(a-i)) by simp,natDegree_C]
  have hyy : ((Nat.choose b h : K[X])*(y^2)^(b-h)).natDegree ≤ 2*(b-h)*dy := by
    refine natDegree_mul_le.trans ?_
    simp only [natDegree_natCast,zero_add]
    refine natDegree_pow_le.trans ?_
    have hh' : (y^2).natDegree≤2*dy :=
      natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hy)
    calc (b-h)*(y^2).natDegree ≤ (b-h)*(2*dy) := Nat.mul_le_mul_left _ hh'
      _ = _ := by ring
  have hxy : (((Nat.choose a i : K[X])*(C x^2)^(a-i))*
      ((Nat.choose b h : K[X])*(y^2)^(b-h))).natDegree ≤ 2*(b-h)*dy :=
    natDegree_mul_le.trans (by omega)
  rw [show k+1+j=k+j+1 by omega]
  apply fits_mono (fits_shift hxy (tail m s u (k+j) (i+v) (h+c) dy r idx x y hy hr))
  have hb' : b-h+h=b := Nat.sub_add_cancel hb
  nlinarith only [congrArg (fun t : ℕ => 2*t*dy) hb']

theorem product_local_degree [CharP K 2] {wY W d m s dy H : ℕ}
    (hw : 0<wY) (x : K) (y : K[X]) (hy : y.natDegree≤dy)
    (f : KerDIdx wY W d → K[X])
    (hf : B6402MixedDegree.mixed dy (∑ e : KerDIdx wY W d, cC (f e)*kerDBasisPoly e.1)≤H)
    (β : ℕ × ℕ × ℕ × ℕ) (idx : LocalBasisIdx m s) :
    Fits (prodLocalNF (C x) y f β idx) (dy*localWeight idx.1) (H+dy*localWeight β) := by
  rcases β with ⟨u,j,v,c⟩
  unfold prodLocalNF
  apply fits_sum; intro e _
  rcases e with ⟨⟨k,r,b,a⟩,he⟩
  have hr := ((mem_kerDIdxFinset_iff wY W d hw k r b a).mp he).1
  apply fits_comp (h:=dy*(2*b+r+k)) (k:=H)
  · exact B6402MixedDegree.coordinate_bound hw f hf _
  · exact entry m s dy k r b a u j v c idx x y hy hr

theorem global_local_degree {wY W s m dy : ℕ} (hw : 0<wY) (x : K) (y : K[X])
    (hy : y.natDegree≤dy) (e : KerDIdx wY W s) (idx : LocalBasisIdx m s) :
    Fits (kerDLocalNF m s (C x) y e.1 idx) (dy*localWeight idx.1)
      (dy*(2*e.1.2.2.1+e.1.2.1+e.1.1)) := by
  rcases e with ⟨⟨k,r,b,a⟩,he⟩
  have hr := ((mem_kerDIdxFinset_iff wY W s hw k r b a).mp he).1
  simpa only [kerDLocalNF, zero_add,add_zero,mul_zero] using
    entry m s dy k r b a 0 0 0 0 idx x y hy hr

theorem primary_row_degree [CharP K 2] {wY W WF d m s k dy H T : ℕ}
    (hw : 0<wY) (x : K) (y : K[X]) (hy : y.natDegree≤dy) (ht : H≤T)
    (f : KerDIdx wY WF d → K[X]) (g : KerDIdx wY W s → K[X])
    (v : LocalBasisIdx (m-k) (s-d) → K[X])
    (hf : B6402MixedDegree.mixed dy (∑ e : KerDIdx wY WF d, cC (f e)*kerDBasisPoly e.1)≤H)
    (hg : ∀ e : KerDIdx wY W s, Fits (g e) (dy*(2*e.1.2.2.1+e.1.2.1+e.1.1)) T)
    (hv : ∀ i, Fits (v i) (dy*localWeight i.1) (T-H)) (idx : LocalBasisIdx m s) :
    Fits ((∑ e : KerDIdx wY W s, g e*kerDLocalNF m s (C x) y e.1 idx) -
          (∑ i : LocalBasisIdx (m-k) (s-d), v i*prodLocalNF (C x) y f i.1 idx))
      (dy*localWeight idx.1) T := by
  classical
  have a : Fits (∑ e : KerDIdx wY W s, g e*kerDLocalNF m s (C x) y e.1 idx) (dy*localWeight idx.1) T := by
    apply fits_sum; intro e _
    exact (by simpa using fits_comp (c:=0) (hg e) (by simpa using global_local_degree hw x y hy e idx))
  have b : Fits (∑ i : LocalBasisIdx (m-k) (s-d), v i*prodLocalNF (C x) y f i.1 idx) (dy*localWeight idx.1) T := by
    apply fits_sum; intro i _
    have hp := product_local_degree hw x y hy f hf i.1 idx
    have hc := fits_comp (c:=H) (hv i) (by simpa only [Nat.add_comm H] using hp)
    simpa only [Nat.sub_add_cancel ht] using hc
  have bn : Fits (-(∑ i : LocalBasisIdx (m-k) (s-d), v i*prodLocalNF (C x) y f i.1 idx)) (dy*localWeight idx.1) T := by
    simpa [Fits] using b
  simpa only [sub_eq_add_neg] using fits_add a bn

#print axioms primary_row_degree
#print axioms product_local_degree
end ProximityPrize.SubmissionBinaryLower.B6402ProductJets
