import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.HK
section ProximityFlatProofPort
variable {α N:Type*}
namespace Finsupp
variable [Zero N] {r:α → α → Prop} {s:N → N → Prop}
theorem Lex.acc (hbot:∀ ⦃n⦄,¬s n 0) (hs:WellFounded s) (x:α →₀ N)
   (h:∀ a∈x.support,Acc (rᶜ ⊓ (·≠·)) a):
   Acc (Finsupp.Lex r s) x:=by
 letI:DecidableEq α:=Classical.decEq α
 rw [lex_eq_invImage_dfinsupp_lex]
 classical
   refine InvImage.accessible toDFinsupp (DFinsupp.Lex.acc (fun _ => hbot) (fun _ => hs) _ ?_)
   simpa only [toDFinsupp_support] using h
theorem Lex.wellFounded (hbot:∀ ⦃n⦄,¬s n 0) (hs:WellFounded s)
   (hr:WellFounded <| rᶜ ⊓ (·≠·)):WellFounded (Finsupp.Lex r s):=
 ⟨fun x => Lex.acc hbot hs x fun a _ => hr.apply a⟩
theorem Lex.wellFounded' (hbot:∀ ⦃n⦄,¬s n 0) (hs:WellFounded s)
   [Std.Trichotomous r] (hr:WellFounded (Function.swap r)):WellFounded (Finsupp.Lex r s):=
 (lex_eq_invImage_dfinsupp_lex r s).symm ▸
   InvImage.wf _ (DFinsupp.Lex.wellFounded' (fun _ => hbot) (fun _ => hs) hr)
instance Lex.wellFoundedLT {α N} [LT α] [@Std.Trichotomous α (· < ·)] [hα:WellFoundedGT α]
   [AddMonoid N] [PartialOrder N] [IsBotZeroClass N]
   [hN:WellFoundedLT N]:WellFoundedLT (Lex (α →₀ N)):=
 ⟨Lex.wellFounded' (fun _ => not_lt_zero) hN.wf hα.wf⟩
instance Colex.wellFoundedLT {α N} [LT α] [@Std.Trichotomous α (· < ·)] [WellFoundedLT α]
   [AddMonoid N] [PartialOrder N] [IsBotZeroClass N]
   [WellFoundedLT N]:WellFoundedLT (Colex (α →₀ N)):=
 Lex.wellFoundedLT (α:=αᵒᵈ)
variable (r)
theorem Lex.wellFounded_of_finite [IsStrictTotalOrder α r] [Finite α]
   (hs:WellFounded s):WellFounded (Finsupp.Lex r s):=
 InvImage.wf (@equivFunOnFinite α N _ _) (Pi.Lex.wellFounded r fun _ => hs)
theorem Lex.wellFoundedLT_of_finite [LinearOrder α] [Finite α] [LT N]
   [hwf:WellFoundedLT N]:WellFoundedLT (Lex (α →₀ N)):=
 ⟨Finsupp.Lex.wellFounded_of_finite (· < ·) hwf.1⟩
theorem Colex.wellFoundedLT_of_finite [LinearOrder α] [Finite α] [LT N]
   [WellFoundedLT N]:WellFoundedLT (Colex (α →₀ N)):=
 Lex.wellFoundedLT_of_finite (α:=αᵒᵈ)
protected theorem wellFoundedLT [Preorder N] [WellFoundedLT N] (hbot:∀ n:N,¬n < 0):
   WellFoundedLT (α →₀ N):=
 ⟨InvImage.wf toDFinsupp (DFinsupp.wellFoundedLT fun _ a => hbot a).wf⟩
instance wellFoundedLT' {N}
   [AddMonoid N] [PartialOrder N] [IsBotZeroClass N] [WellFoundedLT N]:
   WellFoundedLT (α →₀ N):=
 Finsupp.wellFoundedLT fun _ => not_lt_zero
instance wellFoundedLT_of_finite [Finite α] [Preorder N] [WellFoundedLT N]:
   WellFoundedLT (α →₀ N):=
 ⟨InvImage.wf equivFunOnFinite Function.wellFoundedLT.wf⟩
end Finsupp
