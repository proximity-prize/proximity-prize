import ProximityPrize.SubmissionLower.Z07A6ec
import ProximityPrize.SubmissionLower.ZhDU57c
import ProximityPrize.SubmissionLower.Zq1cNdd
set_option Elab.async false
set_option autoImplicit true
namespace P5_7_4
open P5_7 (FarBand Ls jJ Bank Jr terminal cV)
open cu (Shape)
open agU (ad1)
open czX (a8x dei)
def c1 :Prop :=LocalPole
def c2 :Prop := ∀ (b:FarBand) (t:Bank),Jr b t→PoleDebit t
private def CoreOK (s :Shape) (n:ℕ) :Prop :=
 s.J≤ s.B∧s.B<K1.p∧ad1 s≤n
private theorem core_ok (s :Shape) (n:ℕ)
  (h:2*s.J≤ s.m∧s.m+s.J≤ s.B+1∧s.J≤ s.B∧s.B<K1.p ∧
    262144*a8x (s.m-2*s.J) s.J≤6*n) :CoreOK s n:= by
 obtain ⟨hm,hB,hj,hp,h⟩:=h
 have he :=dei s hm hB
 exact ⟨hj,hp,by omega⟩
local notation "core!" => core_ok _ _ (by decide)
private def StageOK (s :Ls) :Prop :=
 CoreOK s.free.shape s.free.ad1∧s.free.shape.B≤ s.free.shape.U ∧
  CoreOK s.moving.shape s.moving.ad1∧s.moving.shape.B≤ s.moving.shape.U
private theorem stage_cons {s :Ls} {ss :List Ls} (h:StageOK s)
  (ht : ∀ x∈ss,StageOK x) : ∀ x∈s :: ss,StageOK x :=
 List.forall_mem_cons.mpr ⟨h,ht⟩
private theorem stage_ok (b:FarBand) : ∀ s∈b.row.stages,StageOK s := by
 cases b <;> simp only [FarBand.row]
 all_goals repeat' first
  | exact (fun _ h=>(List.not_mem_nil h).elim)
  | refine stage_cons ⟨core!,by decide,core!,by decide⟩ ?_
private theorem width_cons {B:ℕ} {g:jJ} {gs :List jJ} (h:B≤g.slots)
  (ht : ∀ x∈gs,B≤x.slots) : ∀ x∈g :: gs,B≤x.slots :=
 List.forall_mem_cons.mpr ⟨h,ht⟩
private theorem grade_widths (b:FarBand) :
  ∀ g∈b.row.gw,(terminal b).shape.B≤g.slots := by
 cases b <;> simp only [FarBand.row]
 all_goals repeat' first
  | exact (fun _ h=>(List.not_mem_nil h).elim)
  | refine width_cons (by decide) ?_
private theorem terminal_core (b:FarBand) :CoreOK (terminal b).shape (terminal b).ad1 := by
 cases b <;> exact core!
private theorem bank_ok (b:FarBand) (t:Bank) (ht:Jr b t) :
   t.shape.J≤t.shape.B∧t.shape.B≤t.shape.U∧t.shape.B<K1.p ∧
    ad1 t.shape≤t.ad1 := by
 rcases ht with rfl | ⟨s,hs,rfl | rfl⟩ | ⟨i,rfl⟩
 · obtain ⟨hj,hp,hn⟩:=terminal_core b
   exact ⟨hj,by cases b <;> decide,hp,hn⟩
 · obtain ⟨⟨hj,hp,hn⟩,hu,_,_⟩:=stage_ok b s hs
   exact ⟨hj,hu,hp,hn⟩
 · obtain ⟨_,_,⟨hj,hp,hn⟩,hu⟩:=stage_ok b s hs
   exact ⟨hj,hu,hp,hn⟩
 · obtain ⟨hj,hp,hn⟩:=terminal_core b
   exact ⟨hj,grade_widths b (cV b i) (List.get_mem _ _),hp,hn⟩
end P5_7_4
