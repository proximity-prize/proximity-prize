import ProximityPrize.SubmissionLower.ZEQaUSb
set_option Elab.async false
section
set_option autoImplicit true
namespace qMNIwTb
noncomputable section
open P5 (I p)
open P5_7_2 (Aux fO NodeUnits anM jX stages)
open cu (L)
open DP (jF zG aq7 complete bga azS)
open P5_7_4 (poleRank)
def c1 :Prop :=
  ∀ (b:fO) (h:ℕ),(jX b).lo≤h→h≤(jX b).hi→b.val<12 →
    ∀ (move :Bool) (a :Aux),Filed b move a → ¬ CJ b move a →
      ∀ (D:jF h),NodeUnits D → ∀ (Crt:zG D) (word:I→L),
        let W:=anM h a.dI a.shape
        Module.finrank L (aq7 h word a.shape W) ≤
          2*h*poleRank a.shape+Module.finrank L (complete Crt word a.shape W)
def c2 :Prop :=
  ∀ (b:fO) (h:ℕ),(jX b).lo≤h→h≤(jX b).hi→b.val<12 →
    ∀ (move :Bool) (a :Aux),Filed b move a → ¬ CJ b move a →
      aL4 h a∧bga a.shape+2*h*poleRank a.shape <
        azS h a.shape+O3 h a (fullCap a.shape) move
def c3:Prop :=
  ∀ (b:fO) (h:ℕ),(jX b).lo≤h→h≤(jX b).hi→12≤b.val →
    ∀ (move :Bool) (a :Aux),Filed b move a→a.shape.B<p∧aL4 h a ∧
      bga a.shape+2*h*((a.shape.U+1)*agU.ajD a.shape.B a.shape.J) <
        O3 h a (fullCap a.shape) move
private theorem height_guard (b:fO) :0<(jX b).lo∧(jX b).hi≤131070:= by
 fin_cases b <;> decide
private theorem free_char (b:fO) : ∀ s∈stages b,s.free.U<p:= by
 fin_cases b <;> simp only [stages,List.map_cons,List.map_nil,List.forall_mem_cons]
 all_goals repeat' first | exact (fun _ h=>(List.not_mem_nil h).elim) | refine ⟨by decide,?_⟩
end
end qMNIwTb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace qcT6PRb
open P5 (I)
open P5_7_2 (Aux)

open cu (L FX Jet)
open DP Polynomial
open private gPw from ProximityPrize.SubmissionLower.Z


noncomputable section
private instance finite_complete {h:ℕ} {D:jF h} (Crt:zG D)
  (word:I→L) (a :Aux) (W:ℕ) :Module.Finite L (completeAt Crt word a W) := by
 let _:=gPw Crt word a.shape W
 exact Module.Finite.of_injective (Submodule.inclusion inf_le_left)
  (Submodule.inclusion_injective (inf_le_left:completeAt Crt word a W≤_))
private instance finite_layers {h:ℕ} {D:jF h} (Crt:zG D)
  (word:I→L) (a :Aux) (W:ℕ) :Module.Finite FX (ack Crt word a W) := by
 change Module.Finite FX
  (Submodule.span FX ((completeAt Crt word a W).map U4.toLinearMap:Set Jet))
 exact Module.Finite.of_fg ((Module.Finite.iff_fg.mp inferInstance).span (A:=FX))
end
end qcT6PRb
end
