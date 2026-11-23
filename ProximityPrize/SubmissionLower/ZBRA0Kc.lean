import ProximityPrize.SubmissionLower.ZUJ1rYc
import ProximityPrize.SubmissionLower.Z2fdgla
import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.ZYswgKc
set_option Elab.async false
set_option autoImplicit true
namespace P4_6_5_1
noncomputable section
open P4 (I K)


open aR (af extend)
open oR (Rr)
open we (zq D7)
open Polynomial
open scoped BigOperators
private def bcJ {n:ℕ} (f :Fin n→af 3)
    (Γ:Finset K) (s :K→K[X]) (a :aap n) :Finset K:= by
  classical
  exact Γ.filter fun γ=>zq (extend (s γ))∈D7 (f a.1) a.2
private theorem bI4 {n:ℕ} {f :Fin n→af 3} {Γ:Finset K}
    {s :K→K[X]} {a :aap n} {γ:K} : γ∈bcJ f Γ s a ↔
    γ∈Γ∧zq (extend (s γ))∈D7 (f a.1) a.2 := by
  classical
  exact Finset.mem_filter
private def cLF (w:I→K) (Γ:Finset K) (s :K→K[X]) :Rr w Γ s where
  n:=0
  part:=Fin.elim0
  cap:=Fin.elim0
  sub i:=Fin.elim0 i
  localCapacity i:=Fin.elim0 i
end
end P4_6_5_1
