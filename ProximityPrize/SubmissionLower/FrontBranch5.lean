import ProximityPrize.SubmissionLower.FrontBranch3
set_option autoImplicit true
section
namespace P1_5
noncomputable section
open Polynomial P1
structure Direction (u : Words) (deleted : Finset I) where
  den : K[X]
  U : K[X]
  V : K[X]
  A : Fin 2 → K[X]
  out : Fin 2 → Fin 2 → K[X]
  den_nodes : ∀ i, den.eval (node i) ≠ 0
  U_ne : U ≠ 0
  V_ne : V ≠ 0
  U_dvd : U ∣ den
  coprime : IsCoprime U V
  phase : U * den.map twist = V * den
  degrees_eq : V.natDegree = U.natDegree
  primitive : IsCoprime (A 0) (A 1)
  height : U.natDegree + amplitudeDegree (A 0) (A 1) + deleted.card ≤ heightCap
  out_degree : ∀ i j, (out i j).degree <
    (k + U.natDegree + amplitudeDegree (A 0) (A 1) : ℕ)
  nodes : ∀ x ∉ deleted, ∀ i j, (out i j).eval (node x) =
    U.eval (node x) * ((A i).map twist).eval (node x) * u j x -
    V.eval (node x) * (A j).eval (node x) * twist (u i x)
variable {u : Words} {deleted : Finset I}
def Direction.s (F : Direction u deleted) := amplitudeDegree (F.A 0) (F.A 1)
def Direction.amp (F : Direction u deleted) (γ : K) := F.A 0 + C γ * F.A 1
structure Regular (F : Direction u deleted) (γ : K) : Prop where
  amp_ne : F.amp γ ≠ 0
  degree_eq : (F.amp γ).natDegree = F.s
  adjacent : IsCoprime (F.amp γ) ((F.amp γ).map twist)
  content_unit : IsCoprime (F.amp γ) F.U
  node_unit : ∀ i ∉ deleted, (F.amp γ).eval (node i) ≠ 0
structure CrossLift (F : Direction u deleted) where
  G : K[X]
  L : K[X]
  monic : G.Monic
  left : G ∣ F.U
  right : G.map twist ∣ F.V
  degree_lt : L.degree < (k + F.s + G.natDegree : ℕ)
  nodes : ∀ i ∉ deleted, L.eval (node i) = G.eval (node i) *
    ((F.A 0).eval (node i) * u 1 i - (F.A 1).eval (node i) * u 0 i)
structure Offset (F : Direction u deleted) {η : K} (anchor : BadMark u η) where
  pencil : K[X]
  pencil_degree : pencil.degree < k
  E : K[X]
  Q : K[X]
  E_monic : E.Monic
  left : E ∣ F.U
  right : E.map twist ∣ F.V
  proper : Q.degree < E.degree
  reduced : IsCoprime Q E
  raw : I → K
  raw_fixed : ∀ i ∉ deleted, twist (raw i) = raw i
  first : ∀ i ∉ deleted, u 0 i + η * u 1 i - anchor.decoder.eval (node i) =
    (F.amp η).eval (node i) * raw i / F.den.eval (node i)
  second : ∀ i ∉ deleted, u 1 i - pencil.eval (node i) =
    Q.eval (node i) / E.eval (node i) + (F.A 1).eval (node i) * raw i / F.den.eval (node i)
end
end P1_5
end
section
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
namespace P1_5
noncomputable section
open Polynomial P1
open ProximityPrize.Benchmark
open scoped BigOperators
variable {u : Words} {deleted : Finset I}
end
end P1_5
end
section
set_option maxRecDepth 8000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace P1_5
noncomputable section
open Polynomial P1
open K1_12 (eq_on_puncture natDegree_lt_of_degree_lt_pos eval_unit_of_dvd)
open private cancel_pair from ProximityPrize.SubmissionLower.Fast068
theorem eval_twist (P : K[X]) (i : I) :
    (P.map twist).eval (node i) = twist (P.eval (node i)) :=
  K1_12.eval_twist P i
end
end P1_5
end
section
set_option maxRecDepth 8000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace P1_5_2
noncomputable section
open Polynomial P1 FrobeniusLocator ProximityPrize.Benchmark
open P1_5 (Direction Regular Offset eval_twist)
open K1_12 (eval_unit_of_dvd invariant_multiple)
open private coprime_factor_of_label from ProximityPrize.SubmissionLower.Fast068
variable {u : Words} {deleted : Finset I} {F : Direction u deleted} {η γ : K}
  {anchor : BadMark u η}
end
end P1_5_2
end
