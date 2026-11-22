import ProximityPrize.SubmissionLower.Low49ActiveLattice
import ProximityPrize.SubmissionLower.Low48BentCyclePrice

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace Low49ActiveCount
open Low48BentLattice (Cap latticePoints coords)
open Low49ActiveLattice (Fits Active points)
open K1_13_6_2_4 (Exponent)
open Finset
open scoped BigOperators
noncomputable section

def missing (a : Cap) (c : ℕ) : Set Exponent := latticePoints a \ points a c

private def clipAt (c h : ℕ) : ℕ := 2*c-2*h
private def indexAt (a : Cap) (h : ℕ) : ℕ := 2*a.1.j-4*h
private def degreeAt (a : Cap) (h : ℕ) : ℕ := 2*a.1.b-h

private def Slices (a : Cap) (c : ℕ) :=
  Σ h : Fin (2*a.2+1), Σ r : Fin (clipAt c h.val), Σ z : Fin (r.val/2+1),
    Fin (r.val-2*z.val+1) × Fin (clipAt c h.val-r.val)

private theorem slices_ext {a : Cap} {c : ℕ} {s t : Slices a c}
    (hh : s.1.val=t.1.val) (hr : s.2.1.val=t.2.1.val)
    (hz : s.2.2.1.val=t.2.2.1.val) (hy : s.2.2.2.1.val=t.2.2.2.1.val)
    (hu : s.2.2.2.2.val=t.2.2.2.2.val) : s=t := by
  rcases s with ⟨⟨h,h₀⟩,⟨r,r₀⟩,⟨z,z₀⟩,⟨y,y₀⟩,⟨u,u₀⟩⟩
  rcases t with ⟨⟨h',h₀'⟩,⟨r',r₀'⟩,⟨z',z₀'⟩,⟨y',y₀'⟩,⟨u',u₀'⟩⟩
  change h=h' at hh
  change r=r' at hr
  change z=z' at hz
  change y=y' at hy
  change u=u' at hu
  subst h' r' z' y' u'
  rfl

private theorem at_bounds {a : Cap} {c h : ℕ} (ha : Fits a c) (hh : h ≤ 2*a.2) :
    2*h ≤ 2*c ∧ 4*h ≤ 2*a.1.j ∧ h ≤ 2*a.1.b ∧
    2*clipAt c h ≤ indexAt a h ∧ clipAt c h ≤ 2*(2*a.1.t-2*h) ∧
    indexAt a h+clipAt c h ≤ degreeAt a h := by
  obtain ⟨hb,hj,hc,ht,hh',_⟩ := ha
  unfold clipAt indexAt degreeAt
  omega

private def slicesEquiv (a : Cap) (c : ℕ) (ha : Fits a c) : missing a c ≃ Slices a c where
  toFun e := by
    have hh := ((coords a e.val).mp e.property.1).2.2.2
    let h : Fin (2*a.2+1) := ⟨e.val 4, Nat.lt_succ_of_le hh⟩
    have hc := at_bounds ha hh
    have he := (coords a e.val).mp e.property.1
    have hcut : 2*a.1.b+2*a.1.j < e.val 0+2*Active e.val+3*e.val 4+2*c := by
      apply Nat.lt_of_not_ge
      exact fun hv => e.property.2 ⟨e.property.1,hv⟩
    let r := indexAt a h.val-Active e.val
    have hr : r < clipAt c h.val ∧ e.val 2+2*e.val 3 ≤ r := by
      dsimp [r,h,clipAt,indexAt,Active] at *
      omega
    let r₀ : Fin (clipAt c h.val) := ⟨r,hr.1⟩
    let z : Fin (r₀.val/2+1) := ⟨e.val 3,by dsimp [r₀]; omega⟩
    let y : Fin (r₀.val-2*z.val+1) := ⟨e.val 2,by dsimp [r₀,z]; omega⟩
    let u := e.val 0 - (degreeAt a h.val - Active e.val + 1 - (clipAt c h.val-r))
    have hu : u < clipAt c h.val-r := by
      dsimp [r,h,u,degreeAt,indexAt,clipAt,Active] at *
      omega
    exact ⟨h,r₀,z,y,⟨u,hu⟩⟩
  invFun s := by
    rcases s with ⟨h,r,z,y,u⟩
    have hh := h.isLt
    have hr := r.isLt
    have hz := z.isLt
    have hy := y.isLt
    have hu := u.isLt
    have hc := at_bounds ha (Nat.le_of_lt_succ hh)
    let act := indexAt a h-r.val
    let x := act - y.val - z.val
    let m0 := degreeAt a h-act+1-(clipAt c h-r.val)+u.val
    let m : Exponent := Finsupp.equivFunOnFinite.symm ![m0,x,y.val,z.val,h.val]
    have hi : m ∈ latticePoints a := by
      apply (coords a m).mpr
      change m0+x+y.val+z.val+h.val ≤ 2*a.1.b ∧
        x+2*y.val+3*z.val+4*h.val ≤ 2*a.1.j ∧ z.val+2*h.val ≤ 2*a.1.t ∧ h.val ≤ 2*a.2
      dsimp [m0,x,act,degreeAt,clipAt,indexAt] at *
      omega
    refine ⟨m,hi,?_⟩
    intro hm
    have hd := hm.2
    change m0+2*(x+y.val+z.val)+3*h.val+2*c ≤ 2*a.1.b+2*a.1.j at hd
    dsimp [m0,x,act,degreeAt,clipAt,indexAt] at *
    omega
  left_inv e := by
    apply Subtype.ext
    ext i
    have hh := ((coords a e.val).mp e.property.1).2.2.2
    have hc := at_bounds ha hh
    have he := (coords a e.val).mp e.property.1
    have hcut : 2*a.1.b+2*a.1.j < e.val 0+2*Active e.val+3*e.val 4+2*c := by
      apply Nat.lt_of_not_ge
      exact fun hv => e.property.2 ⟨e.property.1,hv⟩
    fin_cases i
    · change degreeAt a (e.val 4) - (indexAt a (e.val 4) - (indexAt a (e.val 4) - Active e.val)) + 1 -
        (clipAt c (e.val 4) - (indexAt a (e.val 4)-Active e.val)) +
        (e.val 0 - (degreeAt a (e.val 4)-Active e.val+1 -
          (clipAt c (e.val 4)-(indexAt a (e.val 4)-Active e.val)))) = e.val 0
      dsimp [degreeAt,indexAt,clipAt,Active] at *
      omega
    · change indexAt a (e.val 4)-(indexAt a (e.val 4)-Active e.val)-e.val 2-e.val 3 = e.val 1
      dsimp [indexAt,Active] at *
      omega
    · rfl
    · rfl
    · rfl
  right_inv s := by
    rcases s with ⟨⟨h,hh⟩,⟨r,hr⟩,⟨z,hz⟩,⟨y,hy⟩,⟨u,hu⟩⟩
    change r < clipAt c h at hr
    change z < r/2+1 at hz
    change y < r-2*z+1 at hy
    change u < clipAt c h-r at hu
    have hc := at_bounds ha (show h ≤ 2*a.2 by omega)
    have hact : indexAt a h-r-y-z+y+z = indexAt a h-r := by
      have hci := hc.2.2.2.1
      omega
    have hr' : indexAt a h-(indexAt a h-r-y-z+y+z)=r := by
      rw [hact]
      have hci := hc.2.2.2.1
      omega
    apply slices_ext
    · rfl
    · exact hr'
    · rfl
    · rfl
    · change degreeAt a h-(indexAt a h-r)+1-(clipAt c h-r)+u -
        (degreeAt a h-(indexAt a h-r-y-z+y+z)+1 -
          (clipAt c h-(indexAt a h-(indexAt a h-r-y-z+y+z)))) = u
      rw [hr',hact]
      omega


open private sum_affine sum_pair from ProximityPrize.SubmissionLower.Fast054

private theorem middle_sum (r : ℕ) :
    (∑ z ∈ range (r/2+1), ((r-2*z+1 : ℕ) : ℚ)) =
      ((r/2 : ℕ)+1 : ℚ) * (((r+1 : ℕ) - (r/2 : ℕ) : ℕ) : ℚ) := by
  have h (z : ℕ) (hz : z ∈ range (r/2+1)) :
      ((r-2*z+1 : ℕ) : ℚ) = (r+1 : ℚ)+(-2)*(z : ℚ) := by
    have h2 : 2*z ≤ r := by have := mem_range.mp hz; omega
    push_cast [Nat.cast_sub h2]
    ring
  rw [sum_congr rfl h, sum_affine]
  push_cast [Nat.cast_sub (show r/2 ≤ r+1 by omega)]
  ring

private theorem card_sum (a : Cap) (c : ℕ) (ha : Fits a c) :
    ((missing a c).ncard : ℚ) = ∑ h ∈ range (2*a.2+1), ∑ r ∈ range (clipAt c h),
      ((clipAt c h-r : ℕ) : ℚ) *
        ((r/2 : ℕ)+1 : ℚ) * (((r+1 : ℕ) - (r/2 : ℕ) : ℕ) : ℚ) := by
  classical
  let : Fintype (Slices a c) := by unfold Slices; infer_instance
  rw [← Nat.card_coe_set_eq, Nat.card_congr (slicesEquiv a c ha), Nat.card_eq_fintype_card]
  unfold Slices
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_sum, Nat.cast_mul]
  rw [Fin.sum_univ_eq_sum_range (fun h =>
    ∑ r : Fin (clipAt c h), ∑ z : Fin (r.val/2+1),
      ((r.val-2*z.val+1 : ℕ) : ℚ) * ((clipAt c h-r.val : ℕ) : ℚ))]
  apply sum_congr rfl
  intro h _
  rw [Fin.sum_univ_eq_sum_range (fun r => ∑ z : Fin (r/2+1),
    ((r-2*z.val+1 : ℕ) : ℚ) * ((clipAt c h-r : ℕ) : ℚ))]
  apply sum_congr rfl
  intro r _
  rw [Fin.sum_univ_eq_sum_range (fun z =>
    ((r-2*z+1 : ℕ) : ℚ) * ((clipAt c h-r : ℕ) : ℚ)), ← Finset.sum_mul, middle_sum]
  ring

def sliceLoss (q : ℚ) : ℚ := q*(q+1)^2*(q+2)/3

private def pairedLoss (q i : ℚ) : ℚ :=
    (2*q-2*i)*(i+1)^2 + (2*q-2*i-1)*(i+1)*(i+2)

private theorem sum_paired_loss (q : ℚ) (n : ℕ) :
    ∑ i ∈ range n, pairedLoss q i =
      pairedLoss q 0 * n + (pairedLoss q 1-pairedLoss q 0)*((n : ℚ)*(n-1)/2) +
      (pairedLoss q 2-2*pairedLoss q 1+pairedLoss q 0)*((n : ℚ)*(n-1)*(n-2)/6) +
      (pairedLoss q 3-3*pairedLoss q 2+3*pairedLoss q 1-pairedLoss q 0)*((n : ℚ)*(n-1)*(n-2)*(n-3)/24) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    unfold pairedLoss
    ring

private theorem sum_strip (q : ℕ) :
    (∑ r ∈ range (2*q), ((2*q-r : ℕ) : ℚ) *
      ((r/2 : ℕ)+1 : ℚ) * (((r+1 : ℕ) - (r/2 : ℕ) : ℕ) : ℚ)) = sliceLoss q := by
  rw [sum_pair]
  calc
    _ = ∑ i ∈ range q, pairedLoss q i := by
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      have h0 : (2*i)/2=i := by omega
      have h1 : (2*i+1)/2=i := by omega
      rw [h0,h1]
      push_cast [Nat.cast_sub (show 2*i ≤ 2*q by omega), Nat.cast_sub (show 2*i+1 ≤ 2*q by omega),
        Nat.cast_sub (show i ≤ 2*i+1 by omega), Nat.cast_sub (show i ≤ 2*i+1+1 by omega)]
      unfold pairedLoss
      ring
    _ = _ := by rw [sum_paired_loss]; unfold pairedLoss sliceLoss; ring

theorem loss_count (a : Cap) (c : ℕ) (ha : Fits a c) :
    ((missing a c).ncard : ℚ) =
      ∑ h ∈ range (2*a.2+1), sliceLoss ((c : ℚ) - (h : ℚ)) := by
  rw [card_sum a c ha]
  apply sum_congr rfl
  intro h hh
  have hch : h ≤ c := by
    have := ha.2.2.2.2.1
    have := mem_range.mp hh
    omega
  unfold clipAt
  rw [show 2*c-2*h=2*(c-h) by omega, sum_strip]
  push_cast [Nat.cast_sub hch]
  rfl

theorem clipped_count (a : Cap) (c : ℕ) (ha : Fits a c) :
    ((points a c).ncard : ℚ) = ((latticePoints a).ncard : ℚ) -
      ∑ h ∈ range (2*a.2+1), sliceLoss ((c : ℚ) - (h : ℚ)) := by
  rw [← loss_count a c ha]
  have hn := Set.ncard_sdiff_add_ncard_of_subset
    (s:=points a c) (t:=latticePoints a) (fun _ hm => hm.1) (Low48BentLattice.finite a)
  change (missing a c).ncard + (points a c).ncard = (latticePoints a).ncard at hn
  exact (eq_sub_of_add_eq' (by exact_mod_cast hn))


end
end Low49ActiveCount
