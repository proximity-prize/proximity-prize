import ProximityPrize.SubmissionLower.Koala6844VirtualHighKernel
import ProximityPrize.SubmissionLower.Koala6844VirtualHighSplitIdeals
import ProximityPrize.SubmissionLower.Koala6844VirtualHighRank
import ProximityPrize.SubmissionLower.Koala6844VirtualHighGermDegrees


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Polynomial
open scoped BigOperators Classical

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]

def virtualSeedDirection (second : Bool) : Fin 3 :=
  if second then 2 else 1

def virtualLocalContact (d : Polynomial K) (A : Fin 2 → Polynomial K) (B : Polynomial K)
    (second : Bool) (M : ℕ) (a : K) : LocalContact K :=
  ⟨a, d.rootMultiplicity a, M, virtualEquation A B (virtualSeedDirection second)⟩

def ordinaryRankSix (m b : ℕ) : ℤ := 3 * m * (m+1) * (b+1) * (b+1)

def virtualRankSix (M y b : ℕ) : ℤ :=
  (b+1) * M * (M+1) * (3*(y+b+1)-2*((M : ℤ)-1))

def sourceRankBudgetSix (n d0 d1 m M y b : ℕ) : ℤ :=
  n * ordinaryRankSix m b + ((d0 : ℤ) + d1) * virtualRankSix M y b

private theorem ordinaryLocal_rank (m y b : ℕ) (hy : m ≤ y) (a u : K) :
    6 * (Module.finrank K ((⟨a, 1, m, ordinaryEquation u⟩ : LocalContact K).target y b b) : ℤ)
      ≤ ordinaryRankSix m b := by
  have h := ordinary_quotient_rank_two_le m y b b hy a u
  have h' :
      (2 : ℤ) * Module.finrank K ((⟨a, 1, m, ordinaryEquation u⟩ : LocalContact K).target y b b)
      ≤ (m : ℤ)*(m+1)*(b+1)*(b+1) := by
    exact_mod_cast h
  unfold ordinaryRankSix
  nlinarith only [h']

set_option maxHeartbeats 800000 in
private theorem virtualLocal_rank
    (d : Polynomial K) (A : Fin 2 → Polynomial K) (B : Polynomial K) (second : Bool)
    (M y b : ℕ) (hy : M ≤ y) (hb : M ≤ b) (hd : d ≠ 0) (hc : IsCoprime (A 0) d)
    (a : K) (ha : a ∈ d.roots.toFinset) :
    6 * (Module.finrank K ((virtualLocalContact d A B second M a).target y b b) : ℤ)
      ≤ d.rootMultiplicity a * virtualRankSix M y b := by
  have rootMem := Multiset.mem_toFinset.mp ha
  have hroot := (Polynomial.mem_roots hd).mp rootMem
  have hl := (Polynomial.rootMultiplicity_pos hd).mpr hroot
  let A' (i : Fin 2) := Polynomial.taylor a (A i)
  let B' := Polynomial.taylor a B
  let z := virtualSeedDirection second
  have hz : z ≠ 0 := by cases second <;> decide
  have hA : (A' 0).coeff 0 ≠ 0 := by
    have hr : d.eval₂ (RingHom.id K) a = 0 := by
      simpa only [Polynomial.eval₂_id] using (show d.eval a = 0 from hroot)
    have h := eval₂_ne_zero_of_coprime_root (A 0) d hc (RingHom.id K) a hr
    simpa [A', Polynomial.taylor_coeff_zero, Polynomial.eval₂_id] using h
  have hq := virtualEquation_coeff_zero_ne A' B' z hz hA
  have hdeg (n : ℕ) (i : Fin 3) :
      ((virtualEquation A' B' z).coeff n).degreeOf i ≤ singleSeedWidth second i := by
    have h := degreeOf_virtualEquation_coeff_le A' B' z hz n i
    cases second <;> fin_cases i <;> simpa [z, virtualSeedDirection, singleSeedWidth] using h
  have h := sharp_virtual_quotient_rank (d.rootMultiplicity a) hl M y b hy hb second
    (virtualEquation A' B' z) hq hdeg
  unfold virtualRankSix
  change 6 * (Module.finrank K
    (RectangleJet (K := K) (d.rootMultiplicity a * M) (sourceRectangle y b b) ⧸
      virtualContactSpace (K := K) (d.rootMultiplicity a * M) (d.rootMultiplicity a) M
        (Polynomial.taylor (MvPolynomial.C a) (virtualEquation A B z)) (sourceRectangle y b b)) : ℤ) ≤ _
  rw [taylor_virtualEquation]
  change 6 * (Module.finrank K
    (RectangleJet (K := K) (d.rootMultiplicity a * M) (sourceRectangle y b b) ⧸
      virtualContactSpace (K := K) (d.rootMultiplicity a * M) (d.rootMultiplicity a) M
        (virtualEquation A' B' z) (sourceRectangle y b b)) : ℤ) ≤ _ at h
  simpa only [mul_assoc] using h

private theorem sum_rootMultiplicity (d : Polynomial K) (hs : d.Splits) :
    (∑ a : ↥d.roots.toFinset, (d.rootMultiplicity (a : K) : ℤ)) = d.natDegree := by
  have h : (∑ a ∈ d.roots.toFinset, d.rootMultiplicity a) = d.natDegree := by
    simp_rw [← Polynomial.count_roots]
    rw [Multiset.toFinset_sum_count_eq, hs.natDegree_eq_card_roots]
  rw [Finset.univ_eq_attach]
  calc
    _ = ∑ a ∈ d.roots.toFinset, (d.rootMultiplicity a : ℤ) :=
      Finset.sum_attach _ (fun a : K => (d.rootMultiplicity a : ℤ))
    _ = _ := by exact_mod_cast h

theorem exists_centered_sourceSpace_of_split
    {I : Type} (nodes : Finset I) (x u : I → K)
    (d0 d1 : Polynomial K) (A0 A1 : Fin 2 → Polynomial K) (B0 B1 : Polynomial K)
    (hs0 : d0.Splits) (hs1 : d1.Splits) (hd0 : d0 ≠ 0) (hd1 : d1 ≠ 0)
    (hc0 : IsCoprime (A0 0) d0) (hc1 : IsCoprime (A1 0) d1)
    (D w y b m M : ℕ) (hm : m ≤ y) (hMy : M ≤ y) (hMb : M ≤ b) :
    ∃ S : Submodule K (globalBox K D w y b b),
      6 * (Module.finrank K (globalBox K D w y b b) : ℤ) -
        sourceRankBudgetSix nodes.card d0.natDegree d1.natDegree m M y b ≤
        6 * (Module.finrank K S : ℤ) ∧
      ∀ F ∈ S,
      (∀ i ∈ nodes, MvPolynomial.finSuccEquiv K 3 F.val ∈ ordinaryIdeal (x i) (u i) ^ m) ∧
      MvPolynomial.finSuccEquiv K 3 F.val ∈ divisorIdeal d0 (virtualEquation A0 B0 1) ^ M ∧
      MvPolynomial.finSuccEquiv K 3 F.val ∈ divisorIdeal d1 (virtualEquation A1 B1 2) ^ M := by
  classical
  let J := ↥nodes ⊕ (↥d0.roots.toFinset ⊕ ↥d1.roots.toFinset)
  let contact : J → LocalContact K
    | .inl i => ⟨x i, 1, m, ordinaryEquation (u i)⟩
    | .inr (.inl a) => virtualLocalContact d0 A0 B0 false M a
    | .inr (.inr a) => virtualLocalContact d1 A1 B1 true M a
  let cap : J → ℤ
    | .inl _ => ordinaryRankSix m b
    | .inr (.inl a) => d0.rootMultiplicity (a : K) * virtualRankSix M y b
    | .inr (.inr a) => d1.rootMultiplicity (a : K) * virtualRankSix M y b
  have hcap (j : J) : 6 * (Module.finrank K ((contact j).target y b b) : ℤ) ≤ cap j := by
    rcases j with i | (a | a)
    · exact ordinaryLocal_rank m y b hm (x i) (u i)
    · exact virtualLocal_rank d0 A0 B0 false M y b hMy hMb hd0 hc0 a a.property
    · exact virtualLocal_rank d1 A1 B1 true M y b hMy hMb hd1 hc1 a a.property
  have capSum : (∑ j : J, cap j) =
      sourceRankBudgetSix nodes.card d0.natDegree d1.natDegree m M y b := by
    simp only [J, Fintype.sum_sum_type, cap, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, nsmul_eq_mul, ← Finset.sum_mul, sum_rootMultiplicity _ hs0,
      sum_rootMultiplicity _ hs1, sourceRankBudgetSix]
    ring
  have hsum : 6 * (∑ j : J, (Module.finrank K ((contact j).target y b b) : ℤ)) ≤
      sourceRankBudgetSix nodes.card d0.natDegree d1.natDegree m M y b := by
    rw [Finset.mul_sum, ← capSum]
    exact Finset.sum_le_sum (fun j _ => hcap j)
  let S := (allSourceContacts contact D w y b b).ker
  have hs : (Module.finrank K (globalBox K D w y b b) : ℤ) ≤ Module.finrank K S +
      ∑ j : J, (Module.finrank K ((contact j).target y b b) : ℤ) := by
    exact_mod_cast finrank_contactKernel_add_budget contact D w y b b
  refine ⟨S, by omega, ?_⟩
  intro F hF
  have hContact := mem_ideal_of_mem_contactKernel contact D w y b b F hF
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have h := hContact (.inl ⟨i,hi⟩)
    simpa [contact, ordinaryIdeal, ordinaryEquation, liftPolynomial, coordinatePolynomial] using h
  · apply mem_divisorIdeal_pow_of_split_local d0 _ _ hs0 hd0 M
    intro a ha
    exact hContact (.inr (.inl ⟨a,ha⟩))
  · apply mem_divisorIdeal_pow_of_split_local d1 _ _ hs1 hd1 M
    intro a ha
    exact hContact (.inr (.inr ⟨a,ha⟩))

theorem exists_centered_source_of_split_gate
    {I : Type} (nodes : Finset I) (x u : I → K)
    (d0 d1 : Polynomial K) (A0 A1 : Fin 2 → Polynomial K) (B0 B1 : Polynomial K)
    (hs0 : d0.Splits) (hs1 : d1.Splits) (hd0 : d0 ≠ 0) (hd1 : d1 ≠ 0)
    (hc0 : IsCoprime (A0 0) d0) (hc1 : IsCoprime (A1 0) d1)
    (D w y b m M : ℕ) (hm : m ≤ y) (hMy : M ≤ y) (hMb : M ≤ b)
    (gate : sourceRankBudgetSix nodes.card d0.natDegree d1.natDegree m M y b <
      6 * Module.finrank K (globalBox K D w y b b)) :
    ∃ F : globalBox K D w y b b, F ≠ 0 ∧
      (∀ i ∈ nodes, MvPolynomial.finSuccEquiv K 3 F.val ∈ ordinaryIdeal (x i) (u i) ^ m) ∧
      MvPolynomial.finSuccEquiv K 3 F.val ∈ divisorIdeal d0 (virtualEquation A0 B0 1) ^ M ∧
      MvPolynomial.finSuccEquiv K 3 F.val ∈ divisorIdeal d1 (virtualEquation A1 B1 2) ^ M := by
  obtain ⟨S, hS, hcontact⟩ := exists_centered_sourceSpace_of_split
    nodes x u d0 d1 A0 A1 B0 B1 hs0 hs1 hd0 hd1 hc0 hc1 D w y b m M hm hMy hMb
  have hpos : 0 < Module.finrank K S := by
    exact_mod_cast (show (0 : ℤ) < Module.finrank K S by omega)
  obtain ⟨F, hF⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := S)).mp hpos
  refine ⟨F.val, ?_, hcontact F.val F.property⟩
  intro h
  exact hF (Subtype.ext h)

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh
