import ProximityPrize.SubmissionLower.AZ
set_option Elab.async false
set_option autoImplicit true
namespace cj
open vF
open scoped BigOperators
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private theorem bGN (w s :ℕ) (v :Fin w→Ground) :
    ∃ c:Fin w→Ground,∀ j:Fin w,
      (∑ i:Fin w,c i*((s+j.val).choose i.val :Ground))=v j:= by
  induction w with
  | zero=>exact ⟨Fin.elim0,fun j=>j.elim0⟩
  | succ w ih =>
    obtain ⟨a,ha⟩:=ih (fun j=>v j.succ - v j.castSucc)
    let c:Fin (w+1)→Ground :=
      Fin.cases (v 0 - ∑ i:Fin w,a i*(s.choose (i.val+1) :Ground)) a
    refine ⟨c,?_⟩
    let ev (j:Fin (w+1)) :=
      ∑ i:Fin (w+1),c i*((s+j.val).choose i.val :Ground)
    change ∀ j,ev j=v j
    have step (j:Fin w) :ev j.succ-ev j.castSucc=v j.succ - v j.castSucc:= by
      rw [← ha j]
      dsimp only [ev]
      rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
      simp only [Fin.val_zero,Nat.choose_zero_right,Nat.cast_one,mul_one,
        add_sub_add_left_eq_sub,← Finset.sum_sub_distrib,Fin.val_succ,Fin.val_castSucc,
        ← Nat.add_assoc,Nat.choose_succ_succ,Nat.cast_add,mul_add,c,Fin.cases_succ]
      apply Finset.sum_congr rfl
      intro i _
      abel
    intro j
    induction j using Fin.induction with
    | zero =>
      dsimp only [ev]
      rw [Fin.sum_univ_succ]
      simp [c]
    | succ j hj =>
      have h:=step j
      rw [hj] at h
      exact sub_left_injective h
private theorem bm8 (n r k :ℕ) :
    n.choose r*(n - r).choose k=n.choose k*(n - k).choose r := by
  have hr :=Nat.choose_mul (n:=n) (k :=k+r) (s :=r) (by omega)
  have hk :=Nat.choose_mul (n:=n) (k :=k+r) (s :=k) (by omega)
  rw [show k+r - r=k by omega] at hr
  rw [show k+r - k=r by omega] at hk
  rw [← hr,← hk,Nat.choose_symm_of_eq_add (n:=k+r) (a :=r) (b:=k) (by omega)]
end cj
