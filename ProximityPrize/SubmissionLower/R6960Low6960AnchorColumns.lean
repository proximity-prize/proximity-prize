import ProximityPrize.SubmissionLower.R6960Low6960AnchorLocal
import ProximityPrize.SubmissionLower.Low50Euler2367JetDegree

set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

open K1 K1_13 K1_13_1_1 PolynomialDifferential ReedSolomon.HiddenDerivative
open MvPolynomial
open scoped BigOperators Polynomial

namespace Low6960AnchorColumns
noncomputable section

abbrev Ex := JetVariable 3 →₀ ℕ
abbrev DP := DifferentialPolynomial Geom 3

def jidx (u : Ex) : ℕ := u.some.weight Fin.val
def jdeg (u : Ex) : ℕ := u.some.degree
def jdiff (u : Ex) : ℕ := u (some 1) + u (some 2) + u (some 3)

@[simp] theorem jidx_add (u v : Ex) : jidx (u + v) = jidx u + jidx v := by
  simp [jidx, Finsupp.some_add]
@[simp] theorem jdeg_add (u v : Ex) : jdeg (u + v) = jdeg u + jdeg v := by
  simp [jdeg, Finsupp.some_add]
@[simp] theorem jdiff_add (u v : Ex) : jdiff (u + v) = jdiff u + jdiff v := by
  unfold jdiff
  simp only [Finsupp.add_apply]
  omega

def top (u : Ex) : Ex := u + Finsupp.single none (jidx u)

@[simp] theorem top_add (u v : Ex) : top (u + v) = top u + top v := by
  rw [top, jidx_add, Finsupp.single_add]
  unfold top
  abel

def Related (u v : Ex) : Prop :=
  jdeg v = jdeg u ∧ jidx v ≤ jidx u ∧ jdiff v ≤ jdiff u ∧
    v (some 3) ≤ u (some 3) ∧ v none = u none + jidx v

theorem Related.add {u v a b : Ex} (h : Related u a) (k : Related v b) :
    Related (u+v) (a+b) := by
  obtain ⟨hd,hi,hf,ht,hx⟩ := h
  obtain ⟨kd,ki,kf,kt,kx⟩ := k
  unfold Related
  simp only [jdeg_add, jidx_add, jdiff_add, Finsupp.add_apply]
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem top_related (u : Ex) : Related u (top u) := by
  unfold top Related jdeg jidx jdiff
  simp [Finsupp.some_add, Finsupp.some_single_none]

def Bounded (u : Ex) (P : DP) : Prop :=
  ∀ v ∈ P.support, Related u v ∧ jidx v < jidx u

def HasTop (u : Ex) (a : Geom) (P : DP) : Prop :=
  ∃ L, P = monomial (top u) a + L ∧ Bounded u L

private theorem bounded_add {u : Ex} {P Q : DP} (h : Bounded u P) (k : Bounded u Q) :
    Bounded u (P+Q) := by
  intro v hv
  exact (Finset.mem_union.mp (support_add hv)).elim (h v) (k v)

private theorem monomial_related {u : Ex} {a : Geom} {v : Ex}
    (h : v ∈ (monomial (top u) a).support) : Related u v := by
  have hv := Finset.mem_singleton.mp (support_monomial_subset h)
  simpa only [hv] using top_related u

private theorem top_idx (u : Ex) : jidx (top u) = jidx u := by
  unfold jidx top
  simp [Finsupp.some_add, Finsupp.some_single_none]

private theorem bounded_mul_left {u v : Ex} {P Q : DP} (h : Bounded u P)
    (k : ∀ a ∈ Q.support, Related v a) : Bounded (u+v) (P*Q) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hz)
  obtain ⟨hr, hi⟩ := h a ha
  have hk := k b hb
  exact ⟨hr.add hk, by simpa using Nat.add_lt_add_of_lt_of_le hi hk.2.1⟩

private theorem bounded_mul_right {u v : Ex} {P Q : DP} (h : ∀ a ∈ P.support, Related u a)
    (k : Bounded v Q) : Bounded (u+v) (P*Q) := by
  rw [add_comm, mul_comm]
  exact bounded_mul_left k h

theorem HasTop.mul {u v : Ex} {a b : Geom} {P Q : DP} (h : HasTop u a P)
    (k : HasTop v b Q) : HasTop (u+v) (a*b) (P*Q) := by
  obtain ⟨L, rfl, hL⟩ := h
  obtain ⟨M, rfl, hM⟩ := k
  refine ⟨monomial (top u) a * M + L * monomial (top v) b + L*M, ?_, ?_⟩
  · rw [top_add, ← monomial_mul_monomial]
    ring
  · refine bounded_add (bounded_add ?_ ?_) ?_
    · exact bounded_mul_right (fun b hb => monomial_related hb) hM
    · exact bounded_mul_left hL (fun b hb => monomial_related hb)
    · exact bounded_mul_left hL (fun b hb => (hM b hb).1)

theorem HasTop.support {u : Ex} {a : Geom} {P : DP} (h : HasTop u a P) :
    ∀ v ∈ P.support, Related u v := by
  obtain ⟨L,rfl,hL⟩ := h
  intro v hv
  exact (Finset.mem_union.mp (support_add hv)).elim (fun h => monomial_related h) (fun h => (hL v h).1)

theorem HasTop.lower {u : Ex} {a : Geom} {P : DP} (h : HasTop u a P) :
    ∀ v ∈ P.support, v = top u ∨ jidx v < jidx u := by
  obtain ⟨L,rfl,hL⟩ := h
  intro v hv
  exact (Finset.mem_union.mp (support_add hv)).elim
    (fun h => Or.inl (Finset.mem_singleton.mp (support_monomial_subset h))) (fun h => Or.inr (hL v h).2)

theorem HasTop.coeff {u : Ex} {a : Geom} {P : DP} (h : HasTop u a P) :
    P.coeff (top u) = a := by
  obtain ⟨L,rfl,hL⟩ := h
  have hzero : L.coeff (top u) = 0 := by
    apply notMem_support_iff.mp
    intro hz
    have hh := (hL _ hz).2
    rw [top_idx] at hh
    exact (lt_irrefl _) hh
  simp [hzero]

theorem HasTop.pow {u : Ex} {a : Geom} {P : DP} (h : HasTop u a P) (n : ℕ) :
    HasTop (n • u) (a^n) (P^n) := by
  induction n with
  | zero =>
    refine ⟨0, ?_, by simp [Bounded]⟩
    simp [top,jidx,monomial_zero']
  | succ n ih =>
    rw [pow_succ, pow_succ, succ_nsmul]
    exact ih.mul h

private def eulTerm (i k : ℕ) (hk : k < 4) : DP :=
  monomial (Finsupp.single none k + Finsupp.single (some ⟨k,hk⟩) 1)
    ((-1 : Geom)^k * (133449-k).choose (i-k))

def eul (i : Fin 4) : DP :=
  ∑ k : Fin (i.val+1), eulTerm i.val k.val (by omega)

private theorem eulTerm_related (i k : Fin 4) (h : k ≤ i) :
    Related (Finsupp.single (some i) 1)
      (Finsupp.single none k.val + Finsupp.single (some k) 1) := by
  have hval : k.val ≤ i.val := h
  simp only [Related, jdeg, jidx, jdiff, Finsupp.some_add, Finsupp.some_single_none,
    zero_add, Finsupp.some_single_some, Finsupp.degree_single, Finsupp.weight_single,
    nsmul_eq_mul, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_apply, Option.some.injEq]
  fin_cases k <;> fin_cases i <;> (first | contradiction | decide)


theorem eul_top (i : Fin 4) : HasTop (Finsupp.single (some i) 1) ((-1 : Geom)^i.val) (eul i) := by
  rw [eul, Fin.sum_univ_castSucc]
  let L := ∑ k : Fin i.val, eulTerm i.val k.val (by omega)
  have he : eulTerm i.val i.val i.isLt =
      monomial (top (Finsupp.single (some i) 1)) ((-1 : Geom)^i.val) := by
    simp [eulTerm,top,jidx,Finsupp.some_single_some, Finsupp.weight_single,add_comm]
  refine ⟨L, ?_, ?_⟩
  · rw [add_comm]
    congr 1
  · intro v hv
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp (support_sum hv)
    have hv' := Finset.mem_singleton.mp (support_monomial_subset hk)
    subst v
    refine ⟨eulTerm_related i ⟨k,by omega⟩ (by exact k.isLt.le), ?_⟩
    simp [jidx,Finsupp.some_add,Finsupp.some_single_none,Finsupp.some_single_some,Finsupp.weight_single, k.isLt]


def ColumnEligible (u : Ex) : Prop :=
  jdeg u ≤ 141 ∧ jidx u ≤ 59 ∧ u (some 3) ≤ 14 ∧
    jdeg u ≤ Final50AnchorSpace.gradeLimit (jdiff u) ∧
    u none + 133449*jdeg u < 105*179808 + 2*jidx u

private def orth (u : Ex) : DP :=
  eul 0 ^ u (some 0) * eul 1 ^ u (some 1) *
    eul 2 ^ u (some 2) * eul 3 ^ u (some 3)

private def jetOnly (u : Ex) : Ex := u.some.optionElim 0

private theorem normalized_jet (u : Ex) :
    u (some 0) • Finsupp.single (some (0 : Fin 4)) 1 +
      u (some 1) • Finsupp.single (some (1 : Fin 4)) 1 +
      u (some 2) • Finsupp.single (some (2 : Fin 4)) 1 +
      u (some 3) • Finsupp.single (some (3 : Fin 4)) 1 = jetOnly u := by
  ext k
  cases k with
  | none => simp [jetOnly]
  | some k => fin_cases k <;> simp [jetOnly]

private def sign (u : Ex) : Geom :=
  ((-1 : Geom)^0) ^ u (some 0) * ((-1 : Geom)^1) ^ u (some 1) *
    ((-1 : Geom)^2) ^ u (some 2) * ((-1 : Geom)^3) ^ u (some 3)

private theorem sign_ne_zero (u : Ex) : sign u ≠ 0 := by simp [sign]

private theorem orth_top (u : Ex) : HasTop (jetOnly u) (sign u) (orth u) := by
  rw [← normalized_jet]
  exact ((((eul_top 0).pow _).mul ((eul_top 1).pow _)).mul ((eul_top 2).pow _)).mul ((eul_top 3).pow _)

private theorem single_top (x : ℕ) : HasTop (Finsupp.single none x) 1
    (monomial (Finsupp.single none x) 1) := by
  refine ⟨0, ?_, by simp [Bounded]⟩
  simp [top,jidx,Finsupp.some_single_none]

private def adjusted (u : Ex) : Ex :=
  Finsupp.single none (u none - jidx u) + jetOnly u

private theorem adjusted_idx (u : Ex) : jidx (adjusted u) = jidx u := by
  rw [adjusted,jidx,Finsupp.some_add,Finsupp.some_single_none,zero_add,jetOnly,Finsupp.some_optionElim]
  rfl

private theorem adjusted_top (u : Ex) (h : jidx u ≤ u none) : top (adjusted u) = u := by
  rw [top,adjusted_idx]
  ext k
  cases k with
  | none => simp [adjusted,jetOnly,Nat.sub_add_cancel h]
  | some k => simp [adjusted,jetOnly]

def column (u : Ex) : DP :=
  if u none < jidx u then monomial u 1 else
    monomial (Finsupp.single none (u none - jidx u)) 1 * orth u

private theorem column_hasTop (u : Ex) (h : ¬ u none < jidx u) :
    HasTop (adjusted u) (sign u) (column u) := by
  simpa only [column, ite_eq_right h, one_mul, adjusted] using (single_top _).mul (orth_top u)

theorem column_coeff (u : Ex) : (column u).coeff u ≠ 0 := by
  by_cases h : u none < jidx u
  · simp [column,h]
  · have he := (column_hasTop u h).coeff
    rw [adjusted_top u (Nat.le_of_not_gt h)] at he
    rw [he]
    exact sign_ne_zero u

theorem column_lower (u v : Ex) (h : v ≠ u) (hle : jidx u ≤ jidx v) :
    (column u).coeff v = 0 := by
  apply notMem_support_iff.mp
  intro hv
  by_cases hcut : u none < jidx u
  · rw [column,ite_eq_left hcut] at hv
    exact h (Finset.mem_singleton.mp (support_monomial_subset hv))
  · obtain he | hl := (column_hasTop u hcut).lower v hv
    · exact h (he.trans (adjusted_top u (Nat.le_of_not_gt hcut)))
    · rw [adjusted_idx] at hl
      omega

private theorem jet_weight (m : Fin 4 →₀ ℕ) (w : Fin 4 → ℕ) :
    m.weight w = m 0 * w 0 + m 1 * w 1 + m 2 * w 2 + m 3 * w 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_succ, smul_eq_mul, add_assoc]

private theorem weight_formula (u : Ex) :
    u.weight (differentialWeight 133449) + jidx u = u none + 133449*jdeg u := by
  have he : differentialWeight (d := 3) 133449 = fun i =>
      i.elim 1 (fun k => 133449 - k.val) := by
    funext i
    cases i <;> rfl
  conv_lhs => enter [1]; rw [← Finsupp.optionElim_some u,he,Finsupp.weight_optionElim,one_mul]
  unfold jidx jdeg
  rw [Finsupp.degree_eq_weight_one, jet_weight, jet_weight, jet_weight]
  change u none + (u.some 0*133449 + u.some 1*133448 + u.some 2*133447 + u.some 3*133446) +
      (u.some 0*0 + u.some 1*1 + u.some 2*2 + u.some 3*3) =
    u none + 133449 * (u.some 0*1 + u.some 1*1 + u.some 2*1 + u.some 3*1)
  omega

private theorem adjusted_shape (u : Ex) :
    jdeg (adjusted u) = jdeg u ∧ jdiff (adjusted u) = jdiff u ∧
      adjusted u (some 3) = u (some 3) ∧ adjusted u none = u none - jidx u := by
  have he : (adjusted u).some = u.some := by
    rw [adjusted,Finsupp.some_add,Finsupp.some_single_none,zero_add,jetOnly,Finsupp.some_optionElim]
  change (adjusted u).some.degree = u.some.degree ∧ _ ∧ _ ∧ _
  rw [he]
  simp [adjusted,jetOnly,jdiff]

theorem column_wide {u : Ex} (h : ColumnEligible u) :
    column u ∈ Low6960AnchorLocal.wideSpace := by
  apply (MvPolynomial.mem_restrictSupport_iff Geom).mpr
  intro v hv
  obtain ⟨hd,hi,ht,hf,hw⟩ := h
  have hvw := weight_formula v
  by_cases hcut : u none < jidx u
  · rw [column,ite_eq_left hcut] at hv
    have he := Finset.mem_singleton.mp (support_monomial_subset hv)
    subst v
    refine ⟨hd,hi,ht,hf,?_⟩
    omega
  · obtain ⟨hvd,hvi,hvf,hvt,hvx⟩ := (column_hasTop u hcut).support v hv
    obtain ⟨had,haf,hat,hax⟩ := adjusted_shape u
    rw [had] at hvd
    rw [adjusted_idx] at hvi
    rw [haf] at hvf
    rw [hat] at hvt
    rw [hax] at hvx
    refine ⟨hvd.le.trans hd,hvi.trans hi,hvt.trans ht,?_ ,?_⟩
    · exact hvd.le.trans (hf.trans (Final50AnchorSpace.gradeLimit_antitone hvf))
    · omega



private theorem spec_eul (S : (Polynomial Geom)) (i : Fin 4) :
    differentialSpecializationHom S (eul i) = EulerJetDegree.euler 133449 i.val S := by
  rw [eul, map_sum, EulerJetDegree.euler, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold eulTerm
  rw [monomial_add_single, pow_one, ← MvPolynomial.C_mul_X_pow_eq_monomial,
    map_mul, map_mul, map_pow]
  simp [differentialSpecializationHom, mul_assoc]

private theorem natDegree_prod_bound (S : (Polynomial Geom)) (u : Ex) (hS : S.natDegree ≤ 133449) :
    (differentialSpecializationHom S (orth u)).natDegree ≤ 133449*jdeg u - jidx u := by
  rw [orth,map_mul,map_mul,map_mul,map_pow,map_pow,map_pow,map_pow,spec_eul,spec_eul,spec_eul,spec_eul]
  have hh (i : Fin 4) := (Polynomial.natDegree_pow_le
    (p := EulerJetDegree.euler 133449 i.val S) (n := u (some i))).trans
      (Nat.mul_le_mul_left _ (EulerJetDegree.natDegree_euler_le_sub (i := i.val) hS))
  have ha := Polynomial.natDegree_mul_le.trans (Nat.add_le_add
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add
      (Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hh 0) (hh 1))) (hh 2))) (hh 3))
  refine ha.trans ?_
  rw [jdeg, Finsupp.degree_eq_weight_one, jidx, jet_weight, jet_weight]
  change (u (some 0)*133449 + u (some 1)*133448 + u (some 2)*133447 + u (some 3)*133446) ≤
    133449 * (u (some 0)*1+u (some 1)*1+u (some 2)*1+u (some 3)*1) -
    (u (some 0)*0+u (some 1)*1+u (some 2)*2+u (some 3)*3)
  omega

theorem column_eval_degree (S : (Polynomial Geom)) {u : Ex} (h : ColumnEligible u)
    (hs : S.natDegree ≤ 133449) :
    (differentialSpecialization (column u) S).natDegree ≤ 105 * 179808 - 1 := by
  obtain ⟨hd,hi,_,_,hw⟩ := h
  by_cases hcut : u none < jidx u
  · rw [column,ite_eq_left hcut]
    apply (natDegree_differentialSpecialization_le _ _ hs).trans
    rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
    intro v hv
    have he := Finset.mem_singleton.mp (support_monomial_subset hv)
    subst v
    have hf := weight_formula u
    omega
  · change (differentialSpecializationHom S (column u)).natDegree ≤ _
    rw [column,ite_eq_right hcut,map_mul,← MvPolynomial.X_pow_eq_monomial,map_pow]
    have hx : differentialSpecializationHom S (MvPolynomial.X none : DP) = Polynomial.X := by
      simp [differentialSpecializationHom]
    rw [hx]
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_X_pow]
    · have hrel := natDegree_prod_bound S u hs
      have hz : jidx u ≤ 133449*jdeg u := by
        have hh := weight_formula u
        have hwnd : u none ≤ u.weight (differentialWeight 133449) := by
          have he : differentialWeight (d := 3) 133449 = fun i =>
              i.elim 1 (fun k => 133449 - k.val) := by
            funext i
            cases i <;> rfl
          rw [← Finsupp.optionElim_some u,he,Finsupp.weight_optionElim,one_mul]
          simp
        omega
      omega

end
end Low6960AnchorColumns
