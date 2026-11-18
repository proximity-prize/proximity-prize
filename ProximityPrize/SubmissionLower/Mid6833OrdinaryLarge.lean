/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Retuned from Lucieno's comparison construction and the promoted Bome2017 68.32
release, including the collaborator credits retained in that release. The ordinary argument itself
is reused; the radius, selected-seed budget, profile choices and excess splits differ. -/
import ProximityPrize.SubmissionLower.Mid6833GateLarge
import ProximityPrize.SubmissionLower.Koala6831OrdinaryTestAdapter
namespace ProximityPrize.SubmissionLower.K6969OrdinaryLarge
open Koala6831Ordinary Koala6831Comparison Koala6831Quotient Koala6831OrdinaryIncidence
open Koala6831BenchmarkPrimitive (Received agreementSet eval_eq_of_mem_agreementSet)
open Koala6831Intrinsic (implicitRegularity graphSpecialize)
open ProximityPrize.Benchmark
open RCN136 RCN137
open scoped Classical BigOperators Polynomial
open MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65000
set_option maxHeartbeats 6000000
variable {K : Type*} [Field K]
abbrev profile := _root_.Frontier6969.LargeTable.profiles
abbrev minExcess (c : ℕ) := if c≤2 then 16223 else 12168
abbrev shape (i : Fin 11) : ℕ × ℕ := ((profile i).2.1,(profile i).2.2+(i.val+1)*(profile i).2.1)
private theorem admissible (idx : Fin 11) :
    2 ≤ (profile idx).1 ∧ 1 ≤ (profile idx).2.1 ∧
      idx.val + 2 ≤ (profile idx).2.2 ∧
      131071 + 33735 < (profile idx).1 * 179740 := by
  fin_cases idx <;> decide +kernel

theorem interpolate {I : Type*} [Fintype I]
    (x u₀ v₀ u₁ v₁ : I → K) (q : Poly K) (q_ne : q ≠ 0)
    (idx : Fin 11) (δ : ℕ) (large : _root_.Frontier6969.LargeTable.cutoff idx ≤ δ) (small : δ ≤ 33735)
    (node_count : Fintype.card I ≤ 262144)
    (q_code : weightDegree (codeWeights 131071) q = 131071 + δ)
    (q_value : weightDegree valueWeights q = 1)
    (q_total : weightDegree totalWeights q = idx.val + 2)
    (q_order : ∀ i, (weightLift germWeights (centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) q)).natTrailingDegree = 1) :
    let (m, y, L) := profile idx
    ∃ Q : Poly K, Q ∈ ordinaryBox K (m * 179740) 131071 y L ∧ ¬ q ∣ Q ∧
      ∀ i, ∃ B : Poly K, ∀ d ∈
        (centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) Q -
          centerAtNode (x i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) q * B).support,
        m ≤ d 0 + d 1 + d 2 := by
  have gate := _root_.Frontier6969.LargeTable.dimension idx δ large
  have admissible := admissible idx
  cases profile : profile idx with
  | mk m caps =>
      obtain ⟨y, L⟩ := caps
      simp only [profile] at gate admissible ⊢
      obtain ⟨m_pos, value_le, total_le, code_upper⟩ := admissible
      exact exists_ordinary_interpolant x u₀ v₀ u₁ v₁ q q_ne (m * 179740) 131071 y L m δ (idx.val + 2)
        (by omega) value_le total_le m_pos q_code q_value q_total q_order
        ((Nat.add_le_add_left (Nat.mul_le_mul_right _ node_count) _).trans_lt gate)

theorem carrier {I Γ : Type*} [Fintype I]
    (nodes : I ↪ K) (u₀ v₀ u₁ v₁ : I → K) (node_count : Fintype.card I ≤ 262144)
    (β a b : Carrier K) (b_ne : b ≠ 0)
    (idx : Fin 11) (δ : ℕ) (large : _root_.Frontier6969.LargeTable.cutoff idx ≤ δ) (small : δ ≤ 33735)
    (β_value : weightDegree valueWeights (retainCarrier β) = 0)
    (a_value : weightDegree valueWeights (retainCarrier a) = 0)
    (b_value : weightDegree valueWeights (retainCarrier b) = 0)
    (β_total : weightDegree totalWeights (retainCarrier β) ≤ idx.val + 2)
    (a_total : weightDegree totalWeights (retainCarrier a) ≤ idx.val + 1)
    (b_total : weightDegree totalWeights (retainCarrier b) ≤ idx.val + 1)
    (q_prime : Prime (comparisonRow β a b))
    (q_code : weightDegree (codeWeights 131071) (comparisonRow β a b) = 131071 + δ)
    (q_value : weightDegree valueWeights (comparisonRow β a b) = 1)
    (q_total : weightDegree totalWeights (comparisonRow β a b) = idx.val + 2)
    (q_order : ∀ i, (weightLift germWeights
      (centerAtNode (nodes i) (u₀ i) (v₀ i) (u₁ i) (v₁ i) (comparisonRow β a b))).natTrailingDegree = 1)
    (P₀ P₁ : Γ → Polynomial K) (g₀ g₁ : Γ → K) (agreement : Γ → Finset I)
    (degree₀ : ∀ g, (P₀ g).natDegree ≤ 131071) (degree₁ : ∀ g, (P₁ g).natDegree ≤ 131071)
    (number_agreeing : ∀ g, 179740 ≤ (agreement g).card)
    (agree₀ : ∀ g i, i ∈ agreement g → (P₀ g).eval (nodes i) = u₀ i + g₀ g * v₀ i)
    (agree₁ : ∀ g i, i ∈ agreement g → (P₁ g).eval (nodes i) = u₁ i + g₁ g * v₁ i)
    (q_zero : ∀ g, specialize (P₀ g) (P₁ g) (g₀ g) (g₁ g) (comparisonRow β a b) = 0) :
    let (_, y, L) := profile idx
    ∃ G : Carrier K, G ≠ 0 ∧
      (∀ d ∈ G.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ L + (idx.val + 1) * y) ∧
      ∀ g, MvPolynomial.aeval ![Polynomial.X, P₀ g, Polynomial.C (g₀ g), Polynomial.C (g₁ g)] G = 0 := by
  have interpolant := interpolate (fun i => nodes i) u₀ v₀ u₁ v₁
    (comparisonRow β a b) q_prime.ne_zero idx δ large small node_count q_code q_value q_total q_order
  cases profile : profile idx with
  | mk m data =>
      obtain ⟨y, L⟩ := data
      simp only [profile] at interpolant ⊢
      obtain ⟨Q, Q_box, proper, contacts⟩ := interpolant
      have support := (MvPolynomial.mem_restrictSupport_iff K).mp Q_box
      have Q_cap : ∀ d ∈ Q.support, d 1 + d 2 ≤ y ∧ d 1 + d 2 + d 3 + d 4 ≤ L :=
        fun d hd => (support hd).2
      have Q_y : ∀ d ∈ Q.support, d 2 ≤ y := by
        intro d hd
        have bound := (Q_cap d hd).1
        omega
      have positive : 0 < m * 179740 := by
        have Q_ne : Q ≠ 0 := fun hz => proper (by rw [hz]; exact dvd_zero _)
        obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr Q_ne
        exact Nat.zero_lt_of_lt (support hd).1
      refine ⟨carrierFromInterpolant β a b y Q,
        carrier_nonzero β a b y Q b_ne b_value q_prime q_value proper Q_y, ?_, ?_⟩
      · intro d hd
        exact carrier_support_caps β a b y L (idx.val + 2) Q (by omega)
          β_value a_value b_value β_total a_total b_total Q_cap d hd
      · intro g
        apply carrier_vanishes β a b y Q Q_y (P₀ g) (P₁ g) (g₀ g) (g₁ g) (q_zero g)
        apply specialization_zero_of_relative_contacts nodes (agreement g) u₀ v₀ u₁ v₁
          (P₀ g) (P₁ g) (g₀ g) (g₁ g) m 131071 (m * 179740) Q (comparisonRow β a b)
          (degree₀ g) (degree₁ g) positive (Nat.mul_le_mul_left m (number_agreeing g))
          (fun d hd => (support hd).1) (q_zero g) (agree₀ g) (agree₁ g) (fun i _ => contacts i)

theorem primitive_carrier {I Γ : Type*} [Fintype I]
    (nodes : I ↪ K) (u₀ v₀ u₁ v₁ : I → K) (node_count : Fintype.card I ≤ 262144)
    (q : SymbolicRow (SeedRing K)) (hprim : IsPrimitiveRow q)
    (hf : q.first ≠ 0) (hs : q.second ≠ 0)
    (hlarge : minExcess (weightDegree totalWeights (primitiveRowLift q)) ≤ primitiveExcess 131071 q) (hsmall : primitiveExcess 131071 q ≤ 33735)
    (hc₂ : 2 ≤ weightDegree totalWeights (primitiveRowLift q))
    (hc₁₀ : weightDegree totalWeights (primitiveRowLift q) ≤ 12)
    (hgood : ∀ i, q.atNode (MvPolynomial.C (nodes i))
      (MvPolynomial.C (u₀ i) + MvPolynomial.X 0 * MvPolynomial.C (v₀ i))
      (MvPolynomial.C (u₁ i) + MvPolynomial.X 1 * MvPolynomial.C (v₁ i)) = 0)
    (σ : K →+* K) (p : ℕ) (P : K → Polynomial K) (seed : Γ → K)
    (agreement : Γ → Finset I) (hdegree : ∀ g, (P (seed g)).natDegree ≤ 131071)
    (hsize : ∀ g, 179740 ≤ (agreement g).card)
    (h₀ : ∀ g i, i ∈ agreement g → (P (seed g)).eval (nodes i) = u₀ i + seed g * v₀ i)
    (h₁ : ∀ g i, i ∈ agreement g →
      ((P (seed g)).map σ).eval (nodes i) = u₁ i + (seed g) ^ p * v₁ i)
    (hzero : ∀ g, primitiveSelected σ p q P (seed g) = 0) :
    ∃ idx : Fin 11, idx.val + 2 = weightDegree totalWeights (primitiveRowLift q) ∧
      let (_, y, L) := profile idx
      ∃ G : Carrier K, G ≠ 0 ∧
        (∀ d ∈ G.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ L + (idx.val + 1) * y) ∧
        ∀ g, MvPolynomial.aeval
          ![Polynomial.X, P (seed g), Polynomial.C (seed g), Polynomial.C ((seed g) ^ p)] G = 0 := by
  let c := weightDegree totalWeights (primitiveRowLift q)
  have hc : 2 ≤ c ∧ c ≤ 12 := ⟨hc₂, hc₁₀⟩
  let idx : Fin 11 := ⟨c - 2, by omega⟩
  have hidx : idx.val + 2 = c := by dsimp [idx]; omega
  have hcap : c - 1 ≤ idx.val + 1 := by omega
  obtain ⟨hβ, ha, hb⟩ := primitiveRowLift_total_weight_caps q hf hs
  refine ⟨idx, hidx, ?_⟩
  apply carrier nodes u₀ v₀ u₁ v₁ node_count
    (carrierOfSeedCoefficients q.beta) (carrierOfSeedCoefficients q.first)
    (carrierOfSeedCoefficients q.second) (carrierOfSeedCoefficients_ne_zero hs)
    idx (primitiveExcess 131071 q) (by change minExcess c ≤ _ at hlarge; rw [←hidx] at hlarge; simpa [Frontier6969.LargeTable.cutoff,minExcess] using hlarge) hsmall
    (liftedCoefficient_value_weight q.beta) (liftedCoefficient_value_weight q.first)
    (liftedCoefficient_value_weight q.second) (hβ.trans_eq hidx.symm) (ha.trans hcap) (hb.trans hcap)
    (primitiveRowLift_prime q hprim (Or.inl hf))
    (primitiveRowLift_code_weight_of_two_sided q 131071 hf hs)
    (primitiveRowLift_value_weight_of_two_sided q hf hs) hidx.symm
    (fun i ↦ primitiveRowLift_germ_order_one q hprim (nodes i)
      (u₀ i) (v₀ i) (u₁ i) (v₁ i) (hgood i))
    (fun g ↦ P (seed g)) (fun g ↦ (P (seed g)).map σ) seed (fun g ↦ (seed g) ^ p) agreement
    hdegree (fun g ↦ Polynomial.natDegree_map_le.trans (hdegree g)) hsize h₀ h₁
  intro g
  exact (primitiveRowLift_specializes_eq σ p q P (seed g)).trans (hzero g)

variable {K E Ω I : Type} [Field K] [Field E] [Field Ω] [Fintype I]
structure Support (x : I ↪ K) (U : Received K I) (S : Finset K) (P : K → Polynomial K) : Prop where
  degree_le : ∀ g∈S, (P g).natDegree≤131071
  agreement : ∀ g∈S, 179740≤(agreementSet x U P g).card
  pencil : ∀ p₀ p₁ : Polynomial K, p₀.natDegree≤131071 → p₁.natDegree≤131071 →
    (RCN050.pencilSeeds S P p₀ p₁).card≤82405
private theorem ordinary_profiles_match (i : Fin 11) :
    ((profile i).2.1, (profile i).2.2 + (i.val + 1) * (profile i).2.1) =
      shape i := by
  fin_cases i <;> decide +kernel

private theorem ordinary_profile_caps (i : Fin 11) :
    (shape i).1 ≤ 19 ∧ (shape i).2 ≤ 185 ∧
      (shape i).1 ≤ (shape i).2 := by
  fin_cases i <;> decide +kernel

theorem retained_price [IsAlgClosed Ω] [CharP E 2130706433] [CharP Ω 2130706433]
    (φ : Polynomial K →+* E) (hφ : Function.Injective φ) (ψ : E →+* Ω)
    (x : I ↪ K) (σ : K →+* K) (hfixed : ∀ i, σ (x i) = x i)
    (hpow : ∀ g : K, σ g = g ^ 2130706433) (hcard : Fintype.card I = 262144)
    (U : Received K I) (retained : Finset K) (P : K → Polynomial K)
    (selection : Support x U retained P) (q : SymbolicRow (SeedRing K))
    (hf : q.first ≠ 0) (hs : q.second ≠ 0) (hprim : IsPrimitiveRow q)
    (hδ : minExcess (weightDegree totalWeights (primitiveRowLift q)) ≤ primitiveExcess 131071 q) (hδ' : primitiveExcess 131071 q ≤ 33735)
    (hc₂ : 2 ≤ weightDegree totalWeights (primitiveRowLift q))
    (hc₁₀ : weightDegree totalWeights (primitiveRowLift q) ≤ 12)
    (hkeep : ∀ g ∈ retained, primitiveSelected σ 2130706433 q P g = 0 ∧
      Disjoint (agreementSet x U P g)
        (primitiveBadNodes x (conjugateWord σ (U 0)) (conjugateWord σ (U 1)) q))
    (tests : ∀ (F : Carrier K), F ≠ 0 → ∀ (idx : Fin 11),
      (∀ d ∈ F.support, d 1 ≤ (shape idx).1 ∧ d 1 + d 2 + d 3 ≤ (shape idx).2) →
      HasOrdinaryAgreementTests φ ψ F x (U 0) (U 1) P retained Finset.univ 131071
        (shape idx).1 (shape idx).2) :
    ∃ idx : Fin 11, idx.val + 2 = weightDegree totalWeights (primitiveRowLift q) ∧ retained.card ≤ ordinaryPrice 2130706433 262144 131071 179740 82404
      (shape idx).1 (shape idx).2 := by
  classical
  let agree := agreementSet x U P
  let u := conjugateWord σ (U 0)
  let v := conjugateWord σ (U 1)
  let bad := primitiveBadNodes x u v q
  let Good := { i : I // i ∉ bad }
  let goodX : Good ↪ K := (Function.Embedding.subtype (· ∉ bad)).trans x
  let agreement (g : ↥retained) := (agree g.1).subtype (· ∉ bad)
  have good_count : Fintype.card Good ≤ 262144 := by
    rw [← hcard]
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have good_node (i : Good) :
      q.atNode (MvPolynomial.C (goodX i))
        (MvPolynomial.C (U 0 i.1) + MvPolynomial.X 0 * MvPolynomial.C (U 1 i.1))
        (MvPolynomial.C (σ (U 0 i.1)) + MvPolynomial.X 1 * MvPolynomial.C (σ (U 1 i.1))) = 0 := by
    by_contra hn
    apply i.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change q.atNode (MvPolynomial.C (x i.1)) (affineSeedWord u v 0 i.1)
      (affineSeedWord u v 1 i.1) ≠ 0
    have heq : q.atNode (MvPolynomial.C (x i.1))
        (MvPolynomial.C (U 0 i.1) + MvPolynomial.X 0 * MvPolynomial.C (U 1 i.1))
        (MvPolynomial.C (σ (U 0 i.1)) + MvPolynomial.X 1 * MvPolynomial.C (σ (U 1 i.1))) ≠ 0 := hn
    simpa only [affineSeedWord, u, v, conjugateWord, zero_ne_one, one_ne_zero,
      ite_true, ite_false] using heq
  have agreeing_count (g : ↥retained) : 179740 ≤ (agreement g).card := by
    have havoid := Finset.disjoint_left.mp (hkeep g.1 g.2).2
    have eq : (agree g.1).filter (· ∉ bad) = agree g.1 :=
      Finset.filter_true_of_mem (fun i hi hb => havoid hi hb)
    change 179740 ≤ ((agree g.1).subtype (· ∉ bad)).card
    rw [Finset.card_subtype, eq]
    exact selection.agreement g.1 g.2
  have natDegree (g : ↥retained) : (P g.1).natDegree ≤ 131071 := selection.degree_le g.1 g.2
  have agrees₀ (g : ↥retained) (i : Good) (hi : i ∈ agreement g) :
      (P g.1).eval (goodX i) = U 0 i.1 + g.1 * U 1 i.1 :=
    eval_eq_of_mem_agreementSet (Finset.mem_subtype.mp hi)
  have agrees₁ (g : ↥retained) (i : Good) (hi : i ∈ agreement g) :
      ((P g.1).map σ).eval (goodX i) = σ (U 0 i.1) + g.1 ^ 2130706433 * σ (U 1 i.1) := by
    have h : ((P g.1).map σ).eval (σ (x i.1)) = σ ((P g.1).eval (x i.1)) :=
      Polynomial.eval_map_apply σ (x i.1)
    rw [hfixed i.1] at h
    have h_agree := agrees₀ g i hi
    change (P g.1).eval (x i.1) = _ at h_agree
    change ((P g.1).map σ).eval (x i.1) = _
    rw [h, h_agree, map_add, map_mul, hpow g.1]
  obtain ⟨idx, idxeq, hF⟩ := primitive_carrier goodX
    (fun i => U 0 i.1) (fun i => U 1 i.1) (fun i => σ (U 0 i.1)) (fun i => σ (U 1 i.1))
    good_count q hprim hf hs hδ hδ' hc₂ hc₁₀ good_node σ 2130706433 P Subtype.val agreement
    natDegree agreeing_count agrees₀ agrees₁ (fun g => (hkeep g.1 g.2).1)
  dsimp at hF
  obtain ⟨F, hF, support, zero⟩ := hF
  have hshape := ordinary_profiles_match idx
  have hy' := congrArg Prod.fst hshape
  have ht' := congrArg Prod.snd hshape
  have support' : ∀ d ∈ F.support, d 1 ≤ (shape idx).1 ∧
      d 1 + d 2 + d 3 ≤ (shape idx).2 := by
    simpa only [← hy', ← ht'] using support
  obtain ⟨hy, ht, hyt⟩ := ordinary_profile_caps idx
  have price := ordinary_carrier_seed_count φ hφ ψ F hF (shape idx).1 (shape idx).2
    hy ht hyt support' x (U 0) (U 1) P retained Finset.univ 131071 179740 82404 (by decide) (by decide)
    (by rw [Finset.card_univ, hcard]; decide)
    selection.degree_le (fun g hg => zero ⟨g, hg⟩) selection.agreement
    selection.pencil (tests F hF idx support')
  rw [Finset.card_univ, hcard] at price
  exact ⟨idx, idxeq, price⟩

private theorem ordinarySurface_rename (φ : Polynomial K →+* E) (F : Carrier K) :
    ordinarySurface φ F = MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) (surfaceMap φ F) := rfl

theorem ordinarySurface_comp (φ : Polynomial K →+* E) (ψ : E →+* Ω) (F : Carrier K) :
    ordinarySurface (ψ.comp φ) F = MvPolynomial.map ψ (ordinarySurface φ F) := by
  rw [ordinarySurface_rename, ordinarySurface_rename, MvPolynomial.map_rename]
  change MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) (MvPolynomial.map (ψ.comp φ) (collectX K F)) =
    MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) (MvPolynomial.map ψ (MvPolynomial.map φ (collectX K F)))
  rw [MvPolynomial.map_map]

theorem ordinarySurface_implicitRegularity (φ : Polynomial K →+* E) (F : Carrier K) :
    ordinarySurface φ (implicitRegularity F) = MvPolynomial.pderiv (1 : Fin 3) (ordinarySurface φ F) := by
  rw [ordinarySurface_rename, ordinarySurface_rename, implicitRegularity]
  have hswap : Equiv.swap (0 : Fin 3) 1 0 = 1 := by decide
  have h := MvPolynomial.pderiv_rename (Equiv.swap (0 : Fin 3) 1).injective 0 (surfaceMap φ F)
  rw [hswap, RCN267.surfaceMap_pderiv] at h
  exact h.symm

theorem exists_cleared_ordinary_factor (ψ : RatFunc K →+* Ω) (F : Carrier K) (hF : F ≠ 0)
    (y t : ℕ) (hcap : ∀ d ∈ F.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ t)
    (H : MvPolynomial (Fin 3) (RatFunc K))
    (hH : H ∈ normalizedFactorSet (ordinarySurface (algebraMap (Polynomial K) (RatFunc K)) F)) :
    ∃ (L : Carrier K) (c : Ω), c ≠ 0 ∧
      ordinarySurface (ψ.comp (algebraMap (Polynomial K) (RatFunc K))) L = MvPolynomial.C c * MvPolynomial.map ψ H ∧
      ordinarySurface (ψ.comp (algebraMap (Polynomial K) (RatFunc K))) (implicitRegularity L) =
        MvPolynomial.C c * MvPolynomial.pderiv (1 : Fin 3) (MvPolynomial.map ψ H) ∧
      ∀ d ∈ L.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ t := by
  let φ := algebraMap (Polynomial K) (RatFunc K)
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  obtain ⟨L, D, hD, hclear, hlift⟩ := exists_integral_carrier_lift H
  let c := ψ (φ D)
  have hc : c ≠ 0 := (map_ne_zero ψ).mpr (fun hz => hD (hφ (hz.trans (map_zero φ).symm)))
  have hclearΩ : ordinarySurface (ψ.comp φ) L = MvPolynomial.C c * MvPolynomial.map ψ H := by
    rw [ordinarySurface_comp, hclear, map_mul, MvPolynomial.map_C]
  refine ⟨L, c, hc, hclearΩ, ?_, ?_⟩
  · rw [ordinarySurface_implicitRegularity, hclearΩ, MvPolynomial.pderiv_mul]
    simp
  · let Q := ordinarySurface φ F
    have hQ : Q ≠ 0 := fun hz => hF (ordinarySurface_injective φ hφ (by simpa only [map_zero] using hz))
    obtain ⟨hy, ht⟩ := ordinarySurface_degree_caps φ F y t hcap
    obtain ⟨sumY, sumT⟩ := factor_degree_budgets Q hQ
    have hd : H.degreeOf 1 ≤ y :=
      ((Finset.single_le_sum (fun J _ => Nat.zero_le (J.degreeOf (1 : Fin 3))) hH).trans sumY).trans hy
    have hdt : H.totalDegree ≤ t :=
      ((Finset.single_le_sum (fun J _ => Nat.zero_le J.totalDegree) hH).trans sumT).trans ht
    exact fun d hdL => ⟨((hlift d hdL).1).trans hd, ((hlift d hdL).2).trans hdt⟩

private theorem eval_ordinary_mapped (φ : Polynomial K →+* E) (ψ : E →+* Ω)
    (P : K → Polynomial K) (p : ℕ) (g : K) (H : MvPolynomial (Fin 3) E) :
    MvPolynomial.aeval (ordinaryPoint (ψ.comp φ) P p g) (MvPolynomial.map ψ H) =
      ψ (MvPolynomial.eval (ordinaryPoint φ P p g) H) := by
  have hp : ordinaryPoint (ψ.comp φ) P p g = ψ ∘ ordinaryPoint φ P p g := by
    funext i
    fin_cases i <;> rfl
  rw [MvPolynomial.aeval_eq_eval, hp, MvPolynomial.eval_map, MvPolynomial.eval₂_comp]

private theorem hasOrdinaryAgreementTests [CharP Ω 2130706433]
    (ψ : RatFunc K →+* Ω) (F : Carrier K) (hF : F ≠ 0) (y t : ℕ)
    (hy : 1 ≤ y) (hyt : y ≤ t)
    (hcap : ∀ d ∈ F.support, d 1 ≤ y ∧ d 1 + d 2 + d 3 ≤ t)
    (x : I ↪ K) (u₀ u₁ : I → K) (P : K → Polynomial K)
    (seeds : Finset K) (nodes : Finset I) (w : ℕ) (hw : w < 2130706433)
    (hdegree : ∀ g ∈ seeds, (P g).natDegree ≤ w) :
    HasOrdinaryAgreementTests (algebraMap (Polynomial K) (RatFunc K)) ψ F x u₀ u₁ P seeds nodes w y t := by
  let φ := algebraMap (Polynomial K) (RatFunc K)
  let ι := ψ.comp φ
  have hinj : Function.Injective ι := ψ.injective.comp (IsFractionRing.injective _ _)
  intro H hH
  obtain ⟨L, c, hc, hsurf, hsep, hL⟩ := exists_cleared_ordinary_factor ψ F hF y t hcap H hH
  obtain ⟨test, hfull⟩ := exists_ordinary_agreement_tests ι hinj L nodes x u₀ u₁ w y t hy hyt hL
  let adapted : ShortenedAgreementTests nodes
      (MvPolynomial.C c * MvPolynomial.pderiv (1 : Fin 3) (MvPolynomial.map ψ H)) w y t := {
    full := test.full
    short := test.short
    correct C isprime reg count i hi := by
      have sep : ordinarySurface ι (implicitRegularity L) =
          MvPolynomial.C c * MvPolynomial.pderiv (1 : Fin 3) (MvPolynomial.map ψ H) := hsep
      have hreg : ordinarySurface ι (implicitRegularity L) ∉ C := sep.symm ▸ reg
      simpa only [sep] using test.correct C isprime hreg count i hi }
  refine ⟨c, hc, adapted, ?_⟩
  intro g hg hroot hregular i hi
  let v := ordinaryPoint ι P 2130706433 g
  have point_eq : (fun j => ψ (ordinaryPoint φ P 2130706433 g j)) = v := by
    funext j
    fin_cases j <;> rfl
  have vanish : MvPolynomial.aeval v (ordinarySurface ι L) = 0 := by
    rw [hsurf, map_mul, eval_ordinary_mapped, hroot, map_zero, mul_zero]
  have graph_zero : graphSpecialize (P g) g (g ^ 2130706433) L = 0 := by
    change MvPolynomial.eval v (ordinarySurface ι L) = 0 at vanish
    rw [eval_ordinarySurface] at vanish
    exact hinj (vanish.trans (map_zero ι).symm)
  have regular : MvPolynomial.aeval v (ordinarySurface ι (implicitRegularity L)) ≠ 0 := by
    rw [hsep, map_mul, MvPolynomial.pderiv_map, eval_ordinary_mapped, MvPolynomial.aeval_C]
    exact mul_ne_zero hc ((map_ne_zero ψ).mpr hregular)
  change MvPolynomial.aeval (fun j => ψ (ordinaryPoint φ P 2130706433 g j)) (test.full i) = 0 ↔ _
  rw [point_eq, hfull]
  exact fullOrdinaryTest_graph_iff ι L P 2130706433 w hw g (x i) (u₀ i) (u₁ i)
    (hdegree g hg) graph_zero regular


theorem seed_count [CharP K 2130706433]
    (x : I ↪ K) (σ : K →+* K) (hfixed : ∀ i, σ (x i) = x i)
    (hpow : ∀ g : K, σ g = g ^ 2130706433) (hcard : Fintype.card I = 262144)
    (U : Received K I) (seeds : Finset K) (P : K → Polynomial K) (q : SymbolicRow (SeedRing K))
    (data : Support x U seeds P)
    (hf : q.first≠0) (hs : q.second≠0) (hprim : IsPrimitiveRow q)
    (hδ' : primitiveExcess 131071 q ≤ 33735)
    (hkeep : ∀ g∈seeds, primitiveSelected σ 2130706433 q P g = 0 ∧
      Disjoint (agreementSet x U P g)
        (primitiveBadNodes x (conjugateWord σ (U 0)) (conjugateWord σ (U 1)) q))
    (hδ : minExcess (weightDegree totalWeights (primitiveRowLift q)) ≤ primitiveExcess 131071 q)
    (hc₂ : 2 ≤ weightDegree totalWeights (primitiveRowLift q))
    (hc₁₀ : weightDegree totalWeights (primitiveRowLift q) ≤ 12) :
    seeds.card + (33735-primitiveExcess 131071 q+1)*6*(2130706433+1) ≤ 103791747798885716 := by
  let E := RatFunc K
  let Ω := AlgebraicClosure E
  let φ := algebraMap (Polynomial K) E
  let ψ := algebraMap E Ω
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  let eChar : CharP E 2130706433 :=
    charP_of_injective_ringHom (f := φ.comp Polynomial.C) (hφ.comp Polynomial.C_injective) _
  let oChar : CharP Ω 2130706433 := charP_of_injective_ringHom (f := ψ) ψ.injective _
  have tests (F : Carrier K) (hF : F ≠ 0) (idx : Fin 11)
      (hcap : ∀ d ∈ F.support, d 1 ≤ (shape idx).1 ∧ d 1 + d 2 + d 3 ≤ (shape idx).2) :
      HasOrdinaryAgreementTests φ ψ F x (U 0) (U 1) P seeds Finset.univ 131071
        (shape idx).1 (shape idx).2 := by
    have hy : 1 ≤ (shape idx).1 := by fin_cases idx <;> decide +kernel
    have hyt : (shape idx).1 ≤ (shape idx).2 := by fin_cases idx <;> decide +kernel
    exact hasOrdinaryAgreementTests ψ F hF _ _ hy hyt hcap x (U 0) (U 1) P seeds
      Finset.univ 131071 (by decide) data.degree_le
  obtain ⟨idx, heq, pr⟩ := retained_price φ hφ ψ x σ hfixed hpow hcard U seeds P
    data q hf hs hprim hδ hδ' hc₂ hc₁₀ hkeep tests
  have hcut : _root_.Frontier6969.LargeTable.cutoff idx ≤ primitiveExcess 131071 q := by
    simpa [minExcess, Frontier6969.LargeTable.cutoff,←heq] using hδ
  have bound := _root_.Frontier6969.LargeTable.price idx _ hcut
  cases he : profile idx with
  | mk m caps =>
    obtain ⟨y,L⟩ := caps
    simp only [he] at pr
    change (let (_,y,L) := profile idx; ordinaryPrice 2130706433 262144 131071 179740 82404 y (L + (idx.val+1)*y) + 10*2130706433*(262144+1)+(33735-primitiveExcess 131071 q+1)*6*(2130706433+1) ≤ 103791747798885716) at bound
    simp only [he] at bound
    omega

#print axioms seed_count
end
end ProximityPrize.SubmissionLower.K6969OrdinaryLarge
