import ProximityPrize.SubmissionLower.Koala6844VirtualShortLocalMembership


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open scoped BigOperators
open SecondJetBasis SecondJetSupport SecondJetLocal SecondJetGlobalSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000

variable {K : Type*} [Field K]

private abbrev P5 := Poly (K := K)

structure NodePoleData (m : ℕ) (A B : P5 (K := K)) where
  lead : P5 (K := K)
  base : P5 (K := K)
  shift : P5 (K := K)
  numerator : P5 (K := K)
  seed_relation : lead*MvPolynomial.X 4 = A-base
  auxiliary_relation : lead*B = MvPolynomial.X 0*numerator + A*shift
  den_support : FitsLocal ⟨0,0,0,0,1,1⟩ A
  numerator_support : FitsLocal ⟨1,0,0,1,1,0⟩ numerator
  lead_support : FitsLocal ⟨0,0,0,0,0,0⟩ lead
  base_support : FitsLocal ⟨0,0,0,0,0,0⟩ base
  shift_support : FitsLocal ⟨0,0,0,0,0,0⟩ shift
  lead_unit : IsCoprime (flatContact lead) (Polynomial.X^m)

private theorem local_monomial_eq (e : Fin 5 →₀ ℕ) (c : K) :
    MvPolynomial.monomial e c =
      noSeedMonomial (e 0) (e 1) (e 2) (e 3) c * MvPolynomial.X 4^(e 4) := by
  rw [noSeedMonomial, MvPolynomial.X, MvPolynomial.monomial_pow, one_pow,
    MvPolynomial.monomial_mul_monomial, mul_one]
  apply congrArg (fun e : Fin 5 →₀ ℕ => MvPolynomial.monomial e c)
  ext i
  fin_cases i <;> simp [Finsupp.add_apply]

private theorem scaledArray_mem
    (D : ℕ → ℕ) (w wQ L B s U q m : ℕ)
    (hsB : 2*s ≤ B) (hUL : U ≤ L) (hqU : q ≤ U)
    (caps : ℕ → ℕ) (hcap : ∀ h ≤ s, U ≤ caps h)
    (den num : P5 (K := K)) (x u0 u1 : K)
    (data : NodePoleData m (localize x u0 u1 den) (localize x u0 u1 num))
    (c : NormalizedIndex D w wQ L B s U q → K) :
    ((scaleContact m (flatContact (data.lead^(L+q)))).comp
      (normalizedContactMap D w wQ L B s U q m den num x u0 u1)) c ∈
        Finset.univ.sup (localPoleSpace m L B s U q caps (localize x u0 u1 den) data.numerator) := by
  classical
  let P := reconstructNormalized (K := K) D w wQ L B s U q c
  let F := localize x u0 u1 (clearAux den num q P)
  let A := localize x u0 u1 den
  let N := localize x u0 u1 num
  let V := (Finset.univ.sup (localPoleSpace m L B s U q caps A data.numerator) :
    Submodule K (Target (K := K)))
  change scaleContact m (flatContact (data.lead^(L+q)))
    (flatContact F %ₘ Polynomial.X^m) ∈ V
  have hz := scaleContact_eq_of_shorter_remainder m 0
    (flatContact (data.lead^(L+q))) (flatContact F) (by simp)
  rw [Nat.sub_zero] at hz
  rw [hz]
  have hmul : scaleContact m (flatContact (data.lead^(L+q))) (flatContact F) =
      localRemainder m (data.lead^(L+q)*F) := by simp [scaleContact,localRemainder]
  rw [hmul]
  have hF := clearAux_map (localize x u0 u1).toRingHom den num q P
  change F = clearAux A N q (P.map (localize x u0 u1).toRingHom) at hF
  rw [hF]
  unfold clearAux
  rw [Finset.mul_sum, map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [Polynomial.coeff_map]
  change localRemainder m (data.lead^(L+q)*
    (A^(q-j)*(localize x u0 u1 (P.coeff j)*N^j))) ∈ V
  rw [MvPolynomial.as_sum (P.coeff j), map_sum]
  rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, map_sum]
  apply Submodule.sum_mem
  intro e he
  let M := localize x u0 u1 (MvPolynomial.monomial e (AddMonoidAlgebra.coeff (P.coeff j) e))
  change localRemainder m (data.lead^(L+q)*(A^(q-j)*(M*N^j))) ∈ V
  rw [MvPolynomial.as_sum M]
  rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, map_sum]
  apply Submodule.sum_mem
  intro d hd
  have he' := reconstructed_normalized_bounds D w wQ L B s U q hsB hUL hqU c j e he
  have hL := SecondJetGlobalSupport.localize_monomial x u0 u1 e
    (AddMonoidAlgebra.coeff (P.coeff j) e) d hd
  have hB := SecondJetRelaxedGlobalSupport.localize_support x u0 u1 e d
    (AddMonoidAlgebra.coeff (P.coeff j) e) hd
  rw [local_monomial_eq]
  rw [← mul_assoc (data.lead^(L+q)), ← mul_assoc _ _ (N^j)]
  exact localized_monomial_mem_pole_spaces m L B s U q caps hcap
    (d 0) (d 1) (d 2) (d 3) (d 4) j (AddMonoidAlgebra.coeff M d)
    data.lead data.base A N data.shift data.numerator data.seed_relation data.auxiliary_relation
    data.numerator_support data.den_support data.lead_support data.base_support data.shift_support
    hL.1 (hB.2.1.trans he'.2.1) (hB.1 ▸ he'.2.2.1) (by omega)
    (hL.2.2.2.trans he'.2.2.2.2.1) (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

def seedlessRankBudget (m B s U : ℕ) : ℕ :=
  Fintype.card (SeedlessIndex m B s U) -
    ∑ r : Fin m, ∑ h : Fin (s+1), Fintype.card (SeedlessKernelBlock m B s U r.val h.val)

theorem normalized_local_rank_bound
    (D : ℕ → ℕ) (w wQ L B s U q m : ℕ) (hsB : 2*s ≤ B) (hUL : U ≤ L) (hqU : q ≤ U)
    (caps : ℕ → ℕ) (hcap : ∀ h ≤ s, U ≤ caps h)
    (den num : P5 (K := K)) (x u0 u1 : K)
    (data : NodePoleData m (localize x u0 u1 den) (localize x u0 u1 num)) :
    Module.finrank K (normalizedContactMap D w wQ L B s U q m den num x u0 u1).range ≤
      SecondJetRelaxedGlobalMap.rankBound m L B s U caps +
        ∑ j : Fin q, seedlessRankBudget (m-(j.val+1)) B s (U-(j.val+1)) := by
  classical
  let f := normalizedContactMap D w wQ L B s U q m den num x u0 u1
  let A := localize x u0 u1 den
  let C := data.numerator
  let W := flatContact (data.lead^(L+q))
  let fs := (scaleContact m W).comp f
  have hW : IsCoprime W (Polynomial.X^m) := by
    simp only [W, map_pow]
    exact data.lead_unit.pow_left
  have htrunc (c : NormalizedIndex D w wQ L B s U q → K) :
      f c %ₘ Polynomial.X^m = f c :=
    (Polynomial.modByMonic_eq_self_iff (Polynomial.monic_X_pow m)).mpr
      (Polynomial.degree_modByMonic_lt _ (Polynomial.monic_X_pow m))
  have hinj := rank_le_scaledContact_rank m W f hW htrunc
  let R (j : Fin (q+1)) : Submodule K (Target (K := K)) :=
    if j.val=0 then (SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps).range else
      (seedlessContactMap (K := K) (m-j.val) B s (U-j.val)).range
  let S (j : Fin (q+1)) := scaleContact m
    (flatContact (A^(q-j.val)*((MvPolynomial.X 0)*C)^j.val))
  let b (j : Fin (q+1)) : ℕ :=
    if j.val=0 then SecondJetRelaxedGlobalMap.rankBound m L B s U caps else
      seedlessRankBudget (m-j.val) B s (U-j.val)
  have hR (j : Fin (q+1)) : FiniteDimensional K (R j) := by
    by_cases hj : j.val=0
    · have hEq : R j = (SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps).range := ite_eq_left hj
      rw [hEq]
      infer_instance
    · have hEq : R j = (seedlessContactMap (K := K) (m-j.val) B s (U-j.val)).range := ite_eq_right hj
      rw [hEq]
      infer_instance
  have hb (j : Fin (q+1)) : Module.finrank K (R j) ≤ b j := by
    by_cases hj : j.val=0
    · have hEq : R j = (SecondJetRelaxedRank.restrictedMap (K := K) m L B s U caps).range := ite_eq_left hj
      rw [hEq]
      exact SecondJetRelaxedGlobalMap.local_rank_le_count (K := K) m L B s U caps |>.trans_eq
        (show SecondJetRelaxedGlobalMap.rankBound m L B s U caps = b j from (ite_eq_left hj).symm)
    · have hEq : R j = (seedlessContactMap (K := K) (m-j.val) B s (U-j.val)).range := ite_eq_right hj
      rw [hEq, show b j = seedlessRankBudget (m-j.val) B s (U-j.val) from ite_eq_right hj]
      unfold seedlessRankBudget
      have hh := seedless_local_rank_bound (K := K) (m-j.val) B s (U-j.val)
      omega
  have hm := rank_le_sum_of_pole_spans fs R hR S
    (fun i => scaledArray_mem D w wQ L B s U q m hsB hUL hqU caps hcap
      den num x u0 u1 data (Pi.single i 1)) b hb
  refine hinj.trans (hm.trans_eq ?_)
  rw [Fin.sum_univ_succ]
  simp [b]

end
end ProximityPrize.SubmissionLower.Koala6844VirtualShort
