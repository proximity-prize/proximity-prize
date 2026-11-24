import ProximityPrize.SubmissionLower.AZ
import ProximityPrize.SubmissionLower.AS
set_option Elab.async false
set_option autoImplicit true
section
namespace cz5
open fP (Ew)
open scoped BigOperators
noncomputable section
abbrev Ground :=ZMod P1.p
abbrev Exponent:=Fin 4 →₀ ℕ
abbrev gU (cut:ℕ) :=
 {m:Exponent // Ew 50 (cut:ℤ) 50 15 m}
instance cGU (cut:ℕ) :Finite (gU cut) :=
 ((Finsupp.finite_of_degree_le _).subset fun _ (h:Ew _ _ _ _ _) =>
   Nat.le_of_eq h.1).to_subtype
instance cGV (cut:ℕ) :Fintype (gU cut) :=
 Fintype.ofFinite _
end
end cz5
end
section
namespace dn0
open cz5

open scoped BigOperators
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private def exponent (b c f :ℕ) :Exponent :=
 Finsupp.equivFunOnFinite.symm ![50-(b+c+f),b,c,f]
@[simp] private theorem ayO (b c f :ℕ) (j:Fin 4) :
   exponent b c f j = ![50-(b+c+f),b,c,f] j:= by
  simp [exponent]
private theorem R0 {ι:Type*} [Fintype ι] [DecidableEq ι]
   (S:Submodule Ground (ι→Ground)) (v :ι→Ground)
   (h : ∀ m,v m≠0→Pi.single m (1 :Ground)∈S) :v∈S:= by
 have hsum: (∑ m,v m•Pi.single m (1 :Ground))=v := by
   funext n
   simp [Finset.sum_apply,Pi.single_apply,smul_eq_mul,mul_ite]
 rw [← hsum]
 apply S.sum_mem
 intro m _
 by_cases hm:v m=0
 · simp [hm]
 · exact S.smul_mem _ (h m hm)
end
end dn0
end
section
namespace dn1
open scoped BigOperators
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private theorem bm8 (n r k :ℕ) :
  n.choose r*(n - r).choose k=n.choose k*(n - k).choose r := by
 have hr :=Nat.choose_mul (n:=n) (k :=k+r) (s :=r) (by omega)
 have hk :=Nat.choose_mul (n:=n) (k :=k+r) (s :=k) (by omega)
 rw [show k+r - r=k by omega] at hr
 rw [show k+r - k=r by omega] at hk
 rw [← hr,← hk,Nat.choose_symm_of_eq_add (n:=k+r) (a :=r) (b:=k) (by omega)]
end dn1
end
