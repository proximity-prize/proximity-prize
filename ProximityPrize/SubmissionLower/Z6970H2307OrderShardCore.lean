import ProximityPrize.SubmissionLower.Z6970H2307OrderMemo

set_option autoImplicit false
set_option Elab.async false

namespace Height2307Orders
open K1_13 (Shape)

abbrev PrefixEntry := Nat × Nat × Nat

def prefixFind (w L : Nat) : List PrefixEntry → Option Nat
  | [] => none
  | (width,len,v) :: rest => if w=width ∧ L=len then some v else prefixFind w L rest

def prefixGood (r : Shape) (map : List PrefixEntry) : Bool :=
  map.all fun (w,L,v) => decide (beforeSlice w r 0 L=v)

theorem prefixFind_sound (r : Shape) (map : List PrefixEntry) (h : prefixGood r map=true)
    {w L v : Nat} (hf : prefixFind w L map=some v) :
    beforeSlice w r 0 L=v := by
  induction map with
  | nil => simp [prefixFind] at hf
  | cons e rest ih =>
    obtain ⟨width,len,val⟩ := e
    simp only [prefixGood,List.all_cons,Bool.and_eq_true] at h
    obtain ⟨first,next⟩ := h
    by_cases hp : w=width ∧ L=len
    · have hv : val=v := by simpa [prefixFind,hp] using hf
      rw [hp.1,hp.2,← hv]
      exact of_decide_eq_true first
    · exact ih next (by simpa only [prefixFind,if_neg hp] using hf)

def checkRow (r : Shape) (map : List PrefixEntry) (p : Threshold) : Bool :=
  match prefixFind p.stride (p.m-1) map with
  | none => false
  | some v => decide (0<p.m ∧ 0<p.j ∧ 0<p.stride ∧
      v+afterSlice p.stride r ⟨p.b,p.j,0⟩ (p.m-1)<21230822871131)

theorem checkedShard (r : Shape) (map : List PrefixEntry) (ps : List Threshold)
    (hm : prefixGood r map=true) (hc : ps.all (checkRow r map)=true) :
    ps.all (checked r)=true := by
  apply List.all_eq_true.mpr
  intro p hp
  have ck := List.all_eq_true.mp hc p hp
  cases he : prefixFind p.stride (p.m-1) map with
  | none => simp [checkRow,he] at ck
  | some v =>
    exact checked_of_prefix r p v (prefixFind_sound r map hm he)
      (of_decide_eq_true (by simpa only [checkRow,he] using ck))

end Height2307Orders
