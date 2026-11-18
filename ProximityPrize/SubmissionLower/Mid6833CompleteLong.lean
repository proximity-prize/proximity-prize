/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Retuned from the frozen 68.32 submission of Bome2017, building on Lucieno
(PR 618) and BitWonka (PRs 581 and 582). KoalaBear 69.69 long branch, November 18. -/
/- Adapted from Lucieno, Proximity Prize PR 618, commit dbaea1b59ca9d7311bc98b5fb6d18eb9e1b7603a. Changes for 81,66 errors, right cap 159 and sharper persistent-curve charge. Research pilot. -/
import ProximityPrize.SubmissionLower.Mid6833Primitive
import ProximityPrize.SubmissionLower.Mid6833SepAssembly
import ProximityPrize.SubmissionLower.Koala6831BenchmarkResidual

namespace ProximityPrize.SubmissionLower.Koala6831BenchmarkResidual
open Koala6831BenchmarkField (prime)
set_option autoImplicit false
set_option maxRecDepth 12000
open Koala6831BenchmarkPrimitive Koala6831BenchmarkRetention Koala6831Comparison Koala6831Ordinary
open Koala6831Separation (NormalForm)
open scoped Classical

variable {K I : Type} [Field K] [Fintype I] [CharP K 2130706433]

theorem separated_retained_6969
    {x : I ↪ K} {σ : K →+* K} {received : Received K I}
    {retained : Finset K} {selected : SelectionMap K}
    {q : SymbolicRow (SeedRing K)}
    (hfixed : ∀ i, σ (x i) = x i) (hpow : ∀ g : K, σ g = g ^ prime)
    (hcard : Fintype.card I = 262144)
    (hprim : IsPrimitiveRow q) (hf : q.first ≠ 0) (hs : q.second ≠ 0)
    (hlong : 12137 ≤ primitiveExcess 131071 q) (hsmall : primitiveExcess 131071 q ≤ 33735)
    (N : NormalForm q 131071 (primitiveExcess 131071 q))
    (hgoodSeed : ∀ g ∈ retained, primitiveSelected σ prime q selected g = 0 ∧
      Disjoint (agreementSet x received selected g) (badNodes x σ received q))
    (hdegree : ∀ g ∈ retained, (selected g).natDegree ≤ 131071)
    (hagree : ∀ g ∈ retained, 179740 ≤ (agreementSet x received selected g).card)
    (hpencil : ∀ P₀ P₁ : Polynomial K, P₀.natDegree ≤ 131071 → P₁.natDegree ≤ 131071 →
      (RCN050.pencilSeeds retained selected P₀ P₁).card ≤ 82405) :
    retained.card ≤ 215658647347788502 := by
  let bad := badNodes x σ received q
  let Good := {i : I // i ∉ bad}
  let goodX : Good ↪ K := (Function.Embedding.subtype (· ∉ bad)).trans x
  let agree (g : ↥retained) : Finset Good :=
    (agreementSet x received selected g.1).subtype (· ∉ bad)
  have hgoodCard : Fintype.card Good ≤ 262144 := by
    rw [← hcard]
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hgood (i : Good) :
      q.atNode (MvPolynomial.C (goodX i))
        (MvPolynomial.C (received 0 i.1) + MvPolynomial.X 0 * MvPolynomial.C (received 1 i.1))
        (MvPolynomial.C (σ (received 0 i.1)) + MvPolynomial.X 1 * MvPolynomial.C (σ (received 1 i.1))) = 0 :=
    good_node_identity (x := x) (σ := σ) (received := received) (q := q) i.2
  have hsize (g : ↥retained) : 179740 ≤ (agree g).card := by
    have havoid := Finset.disjoint_left.mp (hgoodSeed g.1 g.2).2
    have heq : (agreementSet x received selected g.1).filter (· ∉ bad) =
        agreementSet x received selected g.1 :=
      Finset.filter_true_of_mem (fun i hi hb => havoid hi hb)
    change 179740 ≤ ((agreementSet x received selected g.1).subtype (· ∉ bad)).card
    rw [Finset.card_subtype, heq]
    exact hagree g.1 g.2
  have h₀ (g : ↥retained) (i : Good) (hi : i ∈ agree g) :
      (selected g.1).eval (goodX i) = received 0 i.1 + g.1 * received 1 i.1 :=
    eval_eq_of_mem_agreementSet (Finset.mem_subtype.mp hi)
  have h₁ (g : ↥retained) (i : Good) (hi : i ∈ agree g) :
      ((selected g.1).map σ).eval (goodX i) = σ (received 0 i.1) + g.1 ^ prime * σ (received 1 i.1) := by
    have heval : ((selected g.1).map σ).eval (σ (x i.1)) = σ ((selected g.1).eval (x i.1)) :=
      Polynomial.eval_map_apply σ (x i.1)
    rw [hfixed i.1] at heval
    have hfit : (selected g.1).eval (x i.1) = received 0 i.1 + g.1 * received 1 i.1 := h₀ g i hi
    change ((selected g.1).map σ).eval (x i.1) = _
    rw [heval, hfit, map_add, map_mul, hpow g.1]
  obtain ⟨G, hne, hsupport, hvanish⟩ := Koala6831Separated.sep6969_carrier_of_primitive
    goodX (fun i => received 0 i.1) (fun i => received 1 i.1)
    (fun i => σ (received 0 i.1)) (fun i => σ (received 1 i.1)) hgoodCard
    q hprim hf hs hlong hsmall N hgood σ prime selected Subtype.val agree
    (fun g => hdegree g.1 g.2) hsize h₀ h₁ (fun g => (hgoodSeed g.1 g.2).1)
  apply SepCount6969.count_82404_long_factors x hcard (inferInstance : Fact (Nat.Prime 2130706433)).out G hne ?_ retained selected
    (received 0) (received 1) (fun g hg => hvanish ⟨g,hg⟩) hdegree hagree hpencil
  intro d hd
  obtain ⟨h₀,h₁,h₂,h₃,_⟩ := hsupport d hd
  exact ⟨h₀,h₁,h₂,by omega⟩
#print axioms separated_retained_6969
end ProximityPrize.SubmissionLower.Koala6831BenchmarkResidual

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
