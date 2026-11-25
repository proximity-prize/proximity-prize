import ProximityPrize.SubmissionLower.DdAE
import Mathlib.Algebra.AffineMonoid.UniqueSums
import ProximityPrize.SubmissionLower.DdCP
set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open _root_ renaming Code.closeCodewordsRel→ oq,Finset→mD,Finset.card_image_of_injective→ oj,Finset.range→lJ,Fintype.card→n5,IsCoprime→lV,Nat.add→cy,Nat.div→nI,Nat.land→nX,Nat.mul→lI,Nat.shiftRight→nq,Nat.sub→c9
set_option autoImplicit true
section
namespace acY.Compact
set_option maxHeartbeats 2000000
open xE
private def ahf (s :Nat) (f :Nat→Nat) :Nat→Nat
 | 0=>0
 | n+1=>Nat.add (ahf s f n) (f (Nat.add s n))
end acY.Compact
end
section
namespace ju
end ju
end
section
namespace ju
def total {α:Type*} [AddMonoid α] (f :ℕ→α) :ℕ→α
 | 0=>0
 | n+1=>total f n+f n
end ju
end
section
namespace ju
open scoped BigOperators

theorem abt {α:Type*} [AddCommMonoid α] (f :ℕ→α) (n:ℕ) :
   total f n = ∑ i∈lJ n,f i:= by
 induction n with
 | zero=>simp [total]
 | succ n ih=>rw [total,Finset.sum_range_succ,ih]
end ju
end
section
namespace i4
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem ProximityPrize.Benchmark
open yP.a92
open scoped NNReal
end
end i4
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace DdP1
noncomputable section
open Polynomial Matrix CoreDefinitions Code gR ProximityPrize.Benchmark
open scoped BigOperators NNReal
structure a08 where
 dw:ℕ
 numerator :ℕ
 denominator :ℕ
 aou:ℕ
 mcaBound:ℕ
 listBound:ℕ
end
end DdP1
end
section
namespace bzq
open xE Finset
open scoped BigOperators
end bzq
end
