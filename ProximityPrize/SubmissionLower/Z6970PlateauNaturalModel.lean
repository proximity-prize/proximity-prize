import ProximityPrize.SubmissionLower.Z6970PlateauNatural
import ProximityPrize.SubmissionLower.Z6970PlateauEnvelopeSound

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace ExpandedPlateauNatural6970
open KoalaPiecewiseTriangle (Line)

def toLine (l : Ray) : Line := ⟨(l.base:ℤ)-10000, l.slope⟩

def rays (f c r : ℕ) : Ray × List Ray :=
  let w := 1679-2*c-3*f
  let u := 500-f
  let base := 11321+2*r+c+f-w
  (⟨base-r-min c u,3⟩, [⟨base-(w+c)/2,6⟩, ⟨base-(2*w+u-r)/3,7⟩,
      ⟨base+r-w,8⟩, ⟨base+r-w-u,9⟩, ⟨base+2*r-2*w,12⟩])

theorem mapped_rays (f c r : ℕ) (hf : f ≤ 500) (hr : r ≤ 2)
    (h : ExpandedPlateauSum6970.spanLength c f r ≠ 0) :
    (toLine (rays f c r).1, (rays f c r).2.map toLine) =
      ExpandedPlateauSum6970.lines (c:ℤ) (f:ℤ) (r:ℤ) := by
  have hc : r+2*c+3*f ≤ 1679 := by unfold ExpandedPlateauSum6970.spanLength at h; omega
  simp only [rays, toLine, ExpandedPlateauSum6970.lines, List.map_cons, List.map_nil,
    Prod.mk.injEq, List.cons.injEq, Line.mk.injEq, Nat.cast_ofNat, and_true]
  repeat' constructor
  all_goals omega

theorem natural_integral
    (hb : ∀ (a b : ℕ) (k : Ray), 0 < k.slope → (bill a b k : ℤ) = ExpandedPlateauEnvelope6970.billFast a b (toLine k))
    (hs : ∀ (h : ℕ) (l : Ray) (ks : List Ray), (∀ k ∈ ks, l.slope < k.slope) → stop h l ks = (ExpandedPlateauEnvelope6970.switchAt (h:ℤ) (toLine l) (ks.map toLine)).toNat)
    (lo hi : ℕ) (l : Ray) (ls : List Ray) (pos : ∀ k ∈ l :: ls, 0 < k.slope)
    (ord : (l::ls).Pairwise (fun a b => a.slope < b.slope)) :
    (integrate lo hi l ls : ℤ) = ExpandedPlateauEnvelope6970.integrate lo hi (toLine l) (ls.map toLine) := by
  induction ls generalizing lo hi l with
  | nil => exact hb lo hi l (pos l (by simp))
  | cons k ks ih =>
    by_cases empty : hi ≤ lo
    · have h : (hi:ℤ) ≤ lo := by exact_mod_cast empty
      simp [integrate, ExpandedPlateauEnvelope6970.integrate, empty, h]
    · have h : ¬(hi:ℤ) ≤ lo := by exact_mod_cast empty
      have left := pos l (by simp)
      have right : ∀ j ∈ k::ks, 0 < j.slope := fun j hj => pos j (List.mem_cons_of_mem _ hj)
      obtain ⟨higher,sorted⟩ := List.pairwise_cons.mp ord
      let t := ExpandedPlateauEnvelope6970.switchAt (hi:ℤ) (toLine l) ((k::ks).map toLine)
      have ht : stop hi l (k::ks) = t.toNat := hs hi l (k::ks) higher
      have hm : ((max lo t.toNat : ℕ) : ℤ) = max (lo:ℤ) t := by omega
      simp only [integrate, if_neg empty, Nat.cast_add, List.map_cons, ExpandedPlateauEnvelope6970.integrate, if_neg h]
      rw [ht, hb lo t.toNat l left, ih (max lo t.toNat) hi k right sorted, hm]
      suffices same : ExpandedPlateauEnvelope6970.billFast (lo:ℤ) (t.toNat:ℤ) (toLine l) = ExpandedPlateauEnvelope6970.billFast (lo:ℤ) t (toLine l) from
        congrArg (fun z : ℤ => z + ExpandedPlateauEnvelope6970.integrate (max (lo:ℤ) t) hi (toLine k) (ks.map toLine)) same
      by_cases ht0 : 0 ≤ t
      · rw [Int.toNat_of_nonneg ht0]
      · have ht1 : t ≤ lo := by omega
        have ht2 : ((t.toNat:ℕ):ℤ) ≤ lo := by omega
        simp [ExpandedPlateauEnvelope6970.billFast,ht1,ht2]

end ExpandedPlateauNatural6970
