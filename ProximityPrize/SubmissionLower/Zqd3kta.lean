import ProximityPrize.SubmissionLower.ZhZv6fd
set_option Elab.async false
set_option autoImplicit true
namespace P6_6_8
open Finset
open aR (Shape)
open P6_6
open wV (aWp)
open scoped BigOperators
open private clip eL3 from ProximityPrize.SubmissionLower.E6
open private cuts from ProximityPrize.SubmissionLower.ZhZv6fd
private def bands (lo:ℕ) :List (ℕ×ℕ)→List (ℕ×ℕ×ℕ)
  | []=>[]
  | (hi,cap) :: rest=>(lo,hi,cap) :: bands hi rest
private abbrev bgn:=bands 0 cuts
private def ow (start stop:ℕ) :List (ℕ×ℕ×ℕ)→Prop
  | []=>start=stop
  | (lo,hi,cap) :: rest=>start=lo∧lo≤hi ∧
      (∀ r used :ℕ,lo≤ r+used→ r+used<hi →
        min r (Dj (r+used))=min r cap)∧ow hi stop rest
private theorem eO4 :ow 0 4026 bgn:= by
  simp only [bgn,cuts,bands,ow,true_and,and_true]
  refine ⟨by decide,?_,by decide,?_,by decide,?_,by decide,?_,by decide,?_,
    by decide,?_,by decide,?_,by decide,?_,by decide,?_,by decide,?_,
    by decide,?_,by decide,?_,by decide,?_,by decide,?_,by decide,?_,
    by decide,?_,by decide,?_⟩
  all_goals
    intro r used hlo hhi
    simp (disch:=omega) only [Dj,ite_eq_left,ite_eq_right] <;> omega
private theorem integrate (used j t stop start:ℕ) (bs :List (ℕ×ℕ×ℕ)) (h:ow start stop bs) :
    start≤ stop∧(bs.map (aWp used 4026 j t)).sum =
      ∑ r∈Ico (clip used 4026 start) (clip used 4026 stop),
        V7 (min r (Dj (r+used))) j t:= by
  induction bs generalizing start with
  | nil =>
    change start=stop at h
    subst start
    simp
  | cons kA rest ih =>
    rcases kA with ⟨lo,hi,cap⟩
    obtain ⟨hstart,hle,hcap,htail⟩:=h
    subst start
    obtain ⟨hstop,hsum⟩:=ih hi htail
    refine ⟨hle.trans hstop,?_⟩
    rw [List.map_cons,List.sum_cons,hsum,eL3 _ _ _ _ _ _ _ hle]
    have hl: (∑ r∈Ico (clip used 4026 lo) (clip used 4026 hi),V7 (min r cap) j t) =
        ∑ r∈Ico (clip used 4026 lo) (clip used 4026 hi),V7 (min r (Dj (r+used))) j t:= by
      refine sum_congr rfl fun r hr => ?_
      have hs :=mem_Ico.mp hr
      simp only [clip] at hs
      rw [hcap r used (by omega) (by omega)]
    rw [hl]
    exact sum_Ico_consecutive _
      (Nat.sub_le_sub_right (min_le_min_left 4026 hle) used)
      (Nat.sub_le_sub_right (min_le_min_left 4026 hstop) used)
def pS (x :Shape) :ℕ :=
  if x.b≤4025∧x.j≤1710∧x.t≤570 then
    (bgn.map (aWp x.b 4026 (1710 - x.j) (570 - x.t))).sum
  else 0
theorem aUJ (x :Shape) :pS x=Gq x := by
  by_cases h:x.b≤4025∧x.j≤1710∧x.t≤570
  · simp only [pS,Gq,ite_eq_left h]
    rw [(integrate x.b (1710 - x.j) (570 - x.t) 4026 0 bgn eO4).2,
      show clip x.b 4026 0=0 by simp [clip],Nat.Ico_zero_eq_range]
    have hb:=h.1
    rw [show clip x.b 4026 4026=4025 - x.b+1 by simp only [clip,min_self]; omega]
  · simp only [pS,Gq,ite_eq_right h]
theorem empty_stock :Gq oL=0x686af4cc85 :=
  (aUJ oL).symm.trans rfl
end P6_6_8
