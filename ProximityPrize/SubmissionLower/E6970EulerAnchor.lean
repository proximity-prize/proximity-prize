import ProximityPrize.SubmissionLower.Z6969Pack0832
import ProximityPrize.SubmissionLower.E6970FinalRank
section Z6969Source2264
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

namespace LowAnchor6970Local
noncomputable section
open K1 K1_13 K1_13_1_1 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open E6970FinalAnchorSpace (gradeLimit gradeLimit_antitone cap_of_grade cap_active AnchorEligible anchorLocal anchorSpace)
open scoped BigOperators
open K1_13_1 (atJet_unflatten)
open K1_13_1_1 (exponent_le_of_mem_translation_monomial)

def WideEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 143 ∧ u.some.weight (fun i => i.val) ≤ 60 ∧ u (some 3) ≤ 16 ∧
    u.some.degree ≤ gradeLimit (u (some 1) + u (some 2) + u (some 3)) ∧
    u.weight (differentialWeight 133378) ≤ 107 * 179730 - 1 + 60

def wideSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | WideEligible u}

def wideLocal (x y : Geom) : wideSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 107 x y).domRestrict _

section
open MvPolynomial

private def truncateX : DifferentialPolynomial Geom 3 →ₗ[Geom] DifferentialPolynomial Geom 3 :=
  filterSupport (fun u => u none < 107)
private theorem origin_monomial_zero (u : JetVariable 3 →₀ ℕ) (a : Geom)
    (hu : 107 ≤ u none) :
    localConstraintAt 107 0 0 (monomial u a) = 0 := by
  have hm : (MvPolynomial.X none ^ u none * monomial (u.erase none) a :
      DifferentialPolynomial Geom 3) = monomial u a := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, one_mul, Finsupp.single_add_erase]
  rw [← hm]
  apply (satisfiesLocalConstraints_iff_coeff_eq_zero 107 0 0 _).mpr
  intro e he
  rw [map_mul, map_pow, unscaledLocalSubstitution, bind₁_X_right]
  simp only [unscaledLocalImage, MvPolynomial.C_0, zero_add, MvPolynomial.X_pow_eq_monomial]
  rw [coeff_monomial_mul', ite_eq_right]
  rw [Finsupp.single_le_iff]
  rw [localContactOrder_eq] at he
  change u none ≤ e (localT 3) → False
  omega
private theorem origin_truncateX (Q : DifferentialPolynomial Geom 3) :
    localConstraintAt 107 0 0 (truncateX Q) = localConstraintAt 107 0 0 Q := by
  rw [Q.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hfilter : truncateX (monomial u (Q.coeff u)) =
      if u none < 107 then monomial u (Q.coeff u) else 0 := by
    ext v
    rw [truncateX, coeff_filterSupport]
    by_cases h : u = v
    · subst v
      by_cases hx : u none < 107 <;> simp [hx]
    · by_cases hx : u none < 107 <;> simp [hx, MvPolynomial.coeff_monomial, h]
  rw [hfilter]
  split
  · rfl
  · rw [map_zero, origin_monomial_zero _ _ (by omega)]

private theorem centered {u v : JetVariable 3 →₀ ℕ}
    (h : v ≤ u) (hu : WideEligible u) (hx : v none < 107) :
    AnchorEligible v := by
  have hd : v.some.degree ≤ u.some.degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum fun j _ => h (some j)
  have hi : v.some.weight (fun i => i.val) ≤ u.some.weight (fun i => i.val) := by
    rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum]
    exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right j.val (h (some j))
  obtain ⟨hdeg,hidx,ht,htail,_⟩ := hu
  have hsum := add_le_add (add_le_add (h (some 1)) (h (some 2))) (h (some 3))
  refine ⟨hd.trans hdeg,hi.trans hidx,(h _).trans ht,hd.trans (htail.trans (gradeLimit_antitone hsum)),?_⟩
  have hw := Finsupp.weight_le_weight
    (w := fun j : Fin 4 => 133378 - j.val) (w' := fun _ => 133378)
    (fun j => Nat.sub_le _ _) v.some
  have he : v.some.weight (fun _ => 133378) = 133378 * v.some.degree := by
    simp only [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, smul_eq_mul,
      Finset.mul_sum, Nat.mul_comm]
  rw [he] at hw
  have hweight : differentialWeight (d := 3) 133378 =
      fun j => j.elim 1 (fun i => 133378 - i.val) := by
    funext j
    cases j <;> rfl
  rw [← Finsupp.optionElim_some v, hweight, Finsupp.weight_optionElim, one_mul]
  calc
    _ ≤ 106 + 133378 * 143 :=
      Nat.add_le_add (Nat.le_of_lt_succ hx)
        (hw.trans (Nat.mul_le_mul_left _ (hd.trans hdeg)))
    _ ≤ _ := by decide
private theorem centered_in_space (x y : Geom) (Q : wideSpace) :
    truncateX (globalPointTranslation x y (Q : DifferentialPolynomial Geom 3)) ∈
      anchorSpace := by
  classical
  rw [(Q : DifferentialPolynomial Geom 3).as_sum, map_sum, map_sum]
  refine Submodule.sum_mem _ fun u hu => ?_
  apply (mem_restrictSupport_iff Geom).mpr
  intro v hv
  have hn := mem_support_iff.mp hv
  rw [truncateX, coeff_filterSupport] at hn
  split at hn
  · exact centered
      (exponent_le_of_mem_translation_monomial x y u v _ (mem_support_iff.mpr hn))
      (Q.property hu) (by assumption)
  · exact (hn rfl).elim
theorem rank_at_point_le_origin (x y : Geom) :
    Module.finrank Geom (LinearMap.range (wideLocal x y)) ≤
      Module.finrank Geom (LinearMap.range (anchorLocal 0 0)) := by
  have hpositive (j : JetVariable 3) : differentialWeight 133378 j ≠ 0 := by
    cases j with
    | none => decide
    | some j =>
      have hj := j.isLt
      change 133378 - j.val ≠ 0
      omega
  have : Module.Finite Geom anchorSpace :=
    restrictSupport_finite <|
      (Finsupp.finite_of_nat_weight_le _ hpositive _).subset fun _ hu => hu.2.2.2.2
  let f : wideSpace →ₗ[Geom] DifferentialPolynomial Geom 3 :=
    (truncateX.comp (globalPointTranslation x y).toLinearMap).domRestrict wideSpace
  let tr : wideSpace →ₗ[Geom] anchorSpace := f.codRestrict _ fun Q =>
    centered_in_space x y Q
  have he : wideLocal x y = (anchorLocal 0 0).comp tr := by
    apply LinearMap.ext
    intro Q
    change localConstraintAt 107 x y (Q : DifferentialPolynomial Geom 3) =
      localConstraintAt 107 0 0 (truncateX (globalPointTranslation x y Q))
    rw [origin_truncateX,localConstraintAt_eq_zero_globalPointTranslation]
  rw [he]
  exact LinearMap.finrank_range_comp_le_left _ _

end

theorem per_position (x y : Geom) :
    Module.finrank Geom (LinearMap.range (wideLocal x y)) ≤ 24736787 :=
  (rank_at_point_le_origin x y).trans E6970FinalRank.origin_rank

theorem finiteWide : Module.Finite Geom wideSpace := by
  have hpositive (j : JetVariable 3) : differentialWeight 133378 j ≠ 0 := by
    cases j with
    | none => decide
    | some j =>
      have hj := j.isLt
      change 133378 - j.val ≠ 0
      omega
  exact MvPolynomial.restrictSupport_finite <|
    (Finsupp.finite_of_nat_weight_le _ hpositive _).subset fun _ hu => hu.2.2.2.2

theorem shape_bound (Q : wideSpace) :
    InBox (shape (MvPolynomial.optionEquivRight Geom (Fin 4) Q)) ⟨143, 60, 16⟩ := by
  classical
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  have hQ := (MvPolynomial.mem_restrictSupport_iff Geom).mp Q.property
  have hm (m : Fin 4 →₀ ℕ) (h : m ∈ P.support) : ∃ i, WideEligible (m.optionElim i) := by
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp h)
    refine ⟨i, hQ ?_⟩
    exact MvPolynomial.mem_support_iff.mpr (by
      rwa [← MvPolynomial.optionEquivRight_coeff_coeff, ← Polynomial.mem_support_iff])
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.some_optionElim, Finsupp.degree_apply, Finsupp.sum] using hi.1
  · apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.some_optionElim, Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hi.2.1
  · change P.degreeOf 3 ≤ 16
    rw [MvPolynomial.degreeOf_eq_sup]
    apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.optionElim_apply_some] using hi.2.2.1

theorem active_bound (Q : wideSpace) :
    A6966LowBase.ActiveFits (MvPolynomial.optionEquivRight Geom (Fin 4) Q) 179 := by
  classical
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  intro m hm
  obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp hm)
  have hQ := (MvPolynomial.mem_restrictSupport_iff Geom).mp Q.property
  have h : WideEligible (m.optionElim i) := hQ (MvPolynomial.mem_support_iff.mpr (by
    rwa [← MvPolynomial.optionEquivRight_coeff_coeff, ← Polynomial.mem_support_iff]))
  have hd := h.1
  have hl := h.2.2.2.1
  have hw := h.2.1
  simp only [Finsupp.optionElim_apply_some] at hl
  rw [Finsupp.some_optionElim] at hd hw
  have hdeg : m.degree = m 0 + m 1 + m 2 + m 3 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_four]
  have hweight : m.weight (fun i : Fin 4 => i.val) = m 1 + 2 * m 2 + 3 * m 3 := by
    rw [Finsupp.weight_eq_sum, Fin.sum_univ_four]
    simp [Nat.mul_comm, Nat.add_assoc]
  change m.weight (fun i : Fin 4 => i.val) ≤ 60 at hw
  rw [hweight] at hw
  have hc := cap_of_grade (s := m.degree) (t := m 1 + m 2 + m 3)
    (by omega) (by omega) (by simpa [Finsupp.some_optionElim] using hl)
  have hb := cap_active _ hd
  omega

theorem rawWeight (Q : wideSpace) :
    differentialWeightedDegree 133378 (Q : DifferentialPolynomial Geom 3) ≤
      107 * 179730 - 1 + 60 := by
  rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  exact fun m hm => (Q.property hm).2.2.2.2


end
end LowAnchor6970Local
end Z6969Source2264

-- Source: ProximityPrize.SubmissionLower.LowAnchor6970Columns
section Z6969Source2265
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

open K1 K1_13 K1_13_1_1 PolynomialDifferential ReedSolomon.HiddenDerivative
open MvPolynomial
open scoped BigOperators Polynomial

namespace LowAnchor6970Columns
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
    ((-1 : Geom)^k * (133378-k).choose (i-k))

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
  jdeg u ≤ 143 ∧ jidx u ≤ 60 ∧ u (some 3) ≤ 16 ∧
    jdeg u ≤ E6970FinalAnchorSpace.gradeLimit (jdiff u) ∧
    u none + 133378*jdeg u < 107*179730 + 2*jidx u

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
    u.weight (differentialWeight 133378) + jidx u = u none + 133378*jdeg u := by
  have he : differentialWeight (d := 3) 133378 = fun i =>
      i.elim 1 (fun k => 133378 - k.val) := by
    funext i
    cases i <;> rfl
  conv_lhs => enter [1]; rw [← Finsupp.optionElim_some u,he,Finsupp.weight_optionElim,one_mul]
  unfold jidx jdeg
  rw [Finsupp.degree_eq_weight_one, jet_weight, jet_weight, jet_weight]
  change u none + (u.some 0*133378 + u.some 1*133377 + u.some 2*133376 + u.some 3*133375) +
      (u.some 0*0 + u.some 1*1 + u.some 2*2 + u.some 3*3) =
    u none + 133378 * (u.some 0*1 + u.some 1*1 + u.some 2*1 + u.some 3*1)
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
    column u ∈ LowAnchor6970Local.wideSpace := by
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
    · exact hvd.le.trans (hf.trans (E6970FinalAnchorSpace.gradeLimit_antitone hvf))
    · omega



private theorem spec_eul (S : (Polynomial Geom)) (i : Fin 4) :
    differentialSpecializationHom S (eul i) = EulerJetDegree.euler 133378 i.val S := by
  rw [eul, map_sum, EulerJetDegree.euler, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold eulTerm
  rw [monomial_add_single, pow_one, ← MvPolynomial.C_mul_X_pow_eq_monomial,
    map_mul, map_mul, map_pow]
  simp [differentialSpecializationHom, mul_assoc]

private theorem natDegree_prod_bound (S : (Polynomial Geom)) (u : Ex) (hS : S.natDegree ≤ 133378) :
    (differentialSpecializationHom S (orth u)).natDegree ≤ 133378*jdeg u - jidx u := by
  rw [orth,map_mul,map_mul,map_mul,map_pow,map_pow,map_pow,map_pow,spec_eul,spec_eul,spec_eul,spec_eul]
  have hh (i : Fin 4) := (Polynomial.natDegree_pow_le
    (p := EulerJetDegree.euler 133378 i.val S) (n := u (some i))).trans
      (Nat.mul_le_mul_left _ (EulerJetDegree.natDegree_euler_le_sub (i := i.val) hS))
  have ha := Polynomial.natDegree_mul_le.trans (Nat.add_le_add
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add
      (Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hh 0) (hh 1))) (hh 2))) (hh 3))
  refine ha.trans ?_
  rw [jdeg, Finsupp.degree_eq_weight_one, jidx, jet_weight, jet_weight]
  change (u (some 0)*133378 + u (some 1)*133377 + u (some 2)*133376 + u (some 3)*133375) ≤
    133378 * (u (some 0)*1+u (some 1)*1+u (some 2)*1+u (some 3)*1) -
    (u (some 0)*0+u (some 1)*1+u (some 2)*2+u (some 3)*3)
  omega

theorem column_eval_degree (S : (Polynomial Geom)) {u : Ex} (h : ColumnEligible u)
    (hs : S.natDegree ≤ 133378) :
    (differentialSpecialization (column u) S).natDegree ≤ 107 * 179730 - 1 := by
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
      have hz : jidx u ≤ 133378*jdeg u := by
        have hh := weight_formula u
        have hwnd : u none ≤ u.weight (differentialWeight 133378) := by
          have he : differentialWeight (d := 3) 133378 = fun i =>
              i.elim 1 (fun k => 133378 - k.val) := by
            funext i
            cases i <;> rfl
          rw [← Finsupp.optionElim_some u,he,Finsupp.weight_optionElim,one_mul]
          simp
        omega
      omega

end
end LowAnchor6970Columns
end Z6969Source2265

-- Source: ProximityPrize.SubmissionLower.LowAnchor6970Dimension
section Z6969Source2266
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

namespace LowAnchor6970Dimension
open E6970FinalAnchorSpace LowAnchor6970Columns
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

/- Count the abscissa powers using the monomial parametrization in P0_9_1. -/
private abbrev Exponent := JetVariable 3 →₀ ℕ
private def indexWeight (a b c : ℕ) : ℕ := a + 2 * b + 3 * c
private def gradeCeiling (a b c : ℕ) : ℕ :=
  min 143 (gradeLimit (a + b + c))
private def gradeSlots (a b c : ℕ) : ℕ :=
  gradeCeiling a b c + 1 - (a + b + c)
private def firstWidth (a b c : ℕ) : ℕ :=
  107 * 179730 - 133378 * gradeCeiling a b c + 2 * indexWeight a b c
private def abscissaWidth (a b c j : ℕ) : ℕ := firstWidth a b c + 133378 * j
private noncomputable def exponent (x v a b c : ℕ) : Exponent :=
  (Finsupp.equivFunOnFinite.symm ![v, a, b, c]).optionElim x
@[simp] private theorem exponent_none (x v a b c : ℕ) : exponent x v a b c none = x := by
  simp [exponent]
@[simp] private theorem exponent_some (x v a b c : ℕ) (i : Fin 4) :
    exponent x v a b c (some i) = ![v, a, b, c] i := by
  simp [exponent]
private theorem exponent_coordinates (u : Exponent) :
    exponent (u none) (u (some 0)) (u (some 1)) (u (some 2)) (u (some 3)) = u := by
  ext i
  cases i with
  | none => simp
  | some i => fin_cases i <;> simp
private theorem jet_weight (m : Fin 4 →₀ ℕ) (w : Fin 4 → ℕ) :
    m.weight w = m 0 * w 0 + m 1 * w 1 + m 2 * w 2 + m 3 * w 3 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_succ, smul_eq_mul, add_assoc]
private theorem eligible_exponent (x v a b c : ℕ) :
    ColumnEligible (exponent x v a b c) ↔
      c ≤ 16 ∧ indexWeight a b c ≤ 60 ∧ v + (a + b + c) ≤ gradeCeiling a b c ∧
        x + 133378 * (v + (a + b + c)) < 107 * 179730 + 2 * indexWeight a b c := by
  unfold ColumnEligible jdeg jidx jdiff gradeCeiling indexWeight
  rw [Finsupp.degree_eq_weight_one, jet_weight, jet_weight]
  simp only [mul_one, Finsupp.some_apply, exponent_some, Matrix.cons_val_zero, le_min_iff]
  simp only [exponent_none, Matrix.cons_val_one]
  have ht : ![v,a,b,c] (2 : Fin 4) = b := rfl
  have hf : ![v,a,b,c] (3 : Fin 4) = c := rfl
  rw [ht,hf,show ![a,b,c] (0 : Fin 3) = a by rfl]
  change (v + a + b + c ≤ 143 ∧ v * 0 + a * 1 + b * 2 + c * 3 ≤ 60 ∧
    c ≤ 16 ∧ v + a + b + c ≤ gradeLimit (a + b + c) ∧
    x + 133378 * (v + a + b + c) < 107 * 179730 + 2 * (v * 0 + a * 1 + b * 2 + c * 3)) ↔ _
  omega
private theorem width_iff (a b c j x : ℕ) (hj : j ≤ gradeCeiling a b c) :
    x < abscissaWidth a b c j ↔
      x + 133378 * (gradeCeiling a b c - j) < 107 * 179730 + 2 * indexWeight a b c := by
  have hgrade : gradeCeiling a b c ≤ 143 := min_le_left _ _
  unfold abscissaWidth firstWidth
  omega
private abbrev Slot :=
  Σ c : Fin 17, Σ b : Fin ((60 - 3 * c.val) / 2 + 1),
    Σ a : Fin (60 - 3 * c.val - 2 * b.val + 1),
      Σ j : Fin (gradeSlots a.val b.val c.val),
        Fin (abscissaWidth a.val b.val c.val j.val)
private abbrev Eligible := {u : Exponent // ColumnEligible u}
private theorem slot_bounds (c b a j x : ℕ) :
    (c < 17 ∧ b < (60 - 3 * c) / 2 + 1 ∧ a < 60 - 3 * c - 2 * b + 1 ∧
      j < gradeSlots a b c ∧ x < abscissaWidth a b c j) ↔
    (c ≤ 16 ∧ indexWeight a b c ≤ 60 ∧ j + (a + b + c) ≤ gradeCeiling a b c ∧
      x < abscissaWidth a b c j) := by
  unfold indexWeight gradeSlots
  omega
private noncomputable def slotExponent (q : Slot) : Eligible := by
  rcases q with ⟨c, b, a, j, x⟩
  refine ⟨exponent x (gradeCeiling a b c - j - (a.val + b.val + c.val)) a b c, ?_⟩
  obtain ⟨hc, hi, hj, hx⟩ := (slot_bounds c b a j x).mp
    ⟨c.isLt, b.isLt, a.isLt, j.isLt, x.isLt⟩
  have hg : gradeCeiling a b c - j - (a.val + b.val + c.val) + (a.val + b.val + c.val) =
      gradeCeiling a b c - j := by omega
  rw [eligible_exponent, hg]
  exact ⟨hc, hi, by omega, (width_iff a b c j x (by omega)).mp hx⟩
private theorem slotExponent_injective : Function.Injective slotExponent := by
  rintro ⟨⟨c, hc⟩, ⟨b, hb⟩, ⟨a, ha⟩, ⟨j, hj⟩, ⟨x, hx⟩⟩
    ⟨⟨c', hc'⟩, ⟨b', hb'⟩, ⟨a', ha'⟩, ⟨j', hj'⟩, ⟨x', hx'⟩⟩ h
  have ec : c = c' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 3)) h
  have eb : b = b' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 2)) h
  have ea : a = a' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 1)) h
  have ex : x = x' := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val none) h
  subst c'
  subst b'
  subst a'
  subst x'
  have ev : gradeCeiling a b c - j - (a + b + c) =
      gradeCeiling a b c - j' - (a + b + c) := by
    simpa [slotExponent] using congrArg (fun u : Eligible => u.val (some 0)) h
  have ej : j = j' := by
    change j < gradeSlots a b c at hj
    change j' < gradeSlots a b c at hj'
    unfold gradeSlots at hj hj'
    omega
  subst j'
  rfl
private theorem slotExponent_surjective : Function.Surjective slotExponent := by
  intro u
  let x := u.val none
  let v := u.val (some 0)
  let a := u.val (some 1)
  let b := u.val (some 2)
  let c := u.val (some 3)
  have he : exponent x v a b c = u.val := exponent_coordinates u.val
  obtain ⟨hc, hi, hg, hx⟩ := (eligible_exponent x v a b c).mp (he.symm ▸ u.property)
  let j := gradeCeiling a b c - (v + (a + b + c))
  have hj : j ≤ gradeCeiling a b c := Nat.sub_le _ _
  have hj' : gradeCeiling a b c - j = v + (a + b + c) := by
    dsimp [j]
    omega
  obtain ⟨hc', hb', ha', hj'', hx'⟩ := (slot_bounds c b a j x).mpr
    ⟨hc, hi, by dsimp [j]; omega, (width_iff a b c j x hj).mpr (hj'.symm ▸ hx)⟩
  refine ⟨⟨⟨c, hc'⟩, ⟨b, hb'⟩, ⟨a, ha'⟩, ⟨j, hj''⟩, ⟨x, hx'⟩⟩, Subtype.ext ?_⟩
  change exponent x (gradeCeiling a b c - j - (a + b + c)) a b c = u.val
  have hv : gradeCeiling a b c - j - (a + b + c) = v := by omega
  rwa [hv]
private def sumRange (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumRange f n + f n
private theorem sumRange_eq (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange, Finset.sum_range_succ, ih]
private theorem sumRange_eq_fin (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ i : Fin n, f i := by
  rw [Fin.sum_univ_eq_sum_range, sumRange_eq]
private def tripleCount (a b c : ℕ) : ℕ :=
  let n := gradeSlots a b c
  n * firstWidth a b c + 133378 * (n * (n - 1) / 2)
private theorem sum_abscissaWidth (a b c : ℕ) :
    (∑ j : Fin (gradeSlots a b c), abscissaWidth a b c j) = tripleCount a b c := by
  rw [Fin.sum_univ_eq_sum_range (abscissaWidth a b c)]
  simp [abscissaWidth, tripleCount, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, Finset.sum_range_id]
private def rowCount (b c : ℕ) : ℕ :=
  sumRange (fun a => tripleCount a b c) (60 - 3 * c - 2 * b + 1)
private def sliceCount (c : ℕ) : ℕ :=
  sumRange (fun b => rowCount b c) ((60 - 3 * c) / 2 + 1)
private theorem slot_card : Fintype.card Slot = sumRange sliceCount 17 := by
  simp only [Slot, sliceCount, rowCount, Fintype.card_sigma, Fintype.card_fin, sumRange_eq_fin,
    sum_abscissaWidth]
private def totals : List ℕ := [850756238102, 776429219730, 705307064644, 636594763614, 571282407124, 508559756144, 449432664652, 393075530440, 340510104358, 290895287642, 245268861392, 202774096910, 164464938924, 129468895424, 98856242320, 71739993024, 49210355782]

private theorem slice_value (i : Fin 17) : sliceCount i = totals[i.val]! := by
  fin_cases i <;> decide +kernel

private theorem totalCount : sumRange sliceCount 17 = 6484626420226 := by
  rw [sumRange_eq_fin]
  calc
    _ = ∑ c : Fin 17, totals[c.val]! := Finset.sum_congr rfl fun c _ => slice_value c
    _ = _ := by rw [← sumRange_eq_fin]; decide +kernel


theorem eligible_card : Nonempty (Eligible ≃ Fin 6484626420226) := by
  let e : Slot ≃ Eligible :=
    Equiv.ofBijective slotExponent ⟨slotExponent_injective, slotExponent_surjective⟩
  exact ⟨e.symm.trans ((Fintype.equivFin Slot).trans (finCongr (slot_card.trans totalCount)))⟩

end LowAnchor6970Dimension
end Z6969Source2266

-- Source: ProximityPrize.SubmissionLower.LowAnchor6970
section Z6969Source2267
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 300000
set_option linter.style.haveILetI false
set_option maxRecDepth 10000

namespace LowAnchor6970
noncomputable section
open K1 K1_13 K1_13_1_1 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open LowAnchor6970Columns LowAnchor6970Local
open scoped BigOperators
open K1_13_1 (atJet_unflatten)

private abbrev Slot := {u : Ex // ColumnEligible u}

private theorem independent_dp : LinearIndependent Geom (fun u : Slot => column u.val) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c he i hi
  by_contra hn
  let F := s.filter (fun i => c i ≠ 0)
  have hF : F.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hn⟩⟩
  obtain ⟨j, hj, hm⟩ := F.exists_max_image (fun u => jidx u.val) hF
  have hj' := Finset.mem_filter.mp hj
  have hcoeff := congrArg (fun p : DP => p.coeff j.val) he
  change (∑ i ∈ s, c i • column i.val).coeff j.val = (0 : DP).coeff j.val at hcoeff
  rw [MvPolynomial.coeff_sum, AddMonoidAlgebra.coeff_zero,
    Finset.sum_eq_single_of_mem j hj'.1] at hcoeff
  · rw [MvPolynomial.coeff_smul, smul_eq_mul] at hcoeff
    exact (mul_ne_zero hj'.2 (column_coeff j.val)) hcoeff
  · intro k hk hkj
    rw [MvPolynomial.coeff_smul]
    by_cases hc : c k = 0
    · simp [hc]
    · have hne : j.val ≠ k.val := fun h => hkj (Subtype.ext h.symm)
      have hi := hm k (Finset.mem_filter.mpr ⟨hk,hc⟩)
      simp [column_lower k.val j.val hne hi]

private def source : Submodule Geom DP := Submodule.span Geom
    (Set.range fun u : Slot => column u.val)

private theorem source_le_wide : source ≤ wideSpace := by
  apply Submodule.span_le.mpr
  rintro _ ⟨u,rfl⟩
  exact column_wide u.property

private theorem dim_source : Module.finrank Geom source = 6484626420226 := by
  classical
  obtain ⟨e⟩ := LowAnchor6970Dimension.eligible_card
  letI : Fintype Slot := Fintype.ofEquiv _ e.symm
  rw [source,finrank_span_eq_card independent_dp,Fintype.card_congr e,Fintype.card_fin]

private theorem source_eval (Q : source) (S : (Polynomial Geom)) (hs : S.natDegree ≤ 133378) :
    (differentialSpecialization (Q.val : DP) S).natDegree ≤ 107*179730-1 := by
  change (differentialSpecializationHom S Q.val).natDegree ≤ _
  let f := (differentialSpecializationHom (d := 3) S).toLinearMap
  change (f Q.val).natDegree ≤ _
  have hq : Q.val ∈ Submodule.span Geom (Set.range fun u : Slot => column u.val) := Q.property
  refine Submodule.span_induction (p := fun p _ => (f p).natDegree ≤ 107 * 179730 - 1) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨u,rfl⟩
    exact column_eval_degree S u.property hs
  · rw [map_zero]
    simp
  · intro a b _ _ ha hb
    rw [map_add]
    exact (Polynomial.natDegree_add_le (f a) (f b)).trans (max_le ha hb)
  · intro a p _ hp
    rw [map_smul]
    exact (Polynomial.natDegree_smul_le _ _).trans hp

private def row (w : I → K) (i : I) : source →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 107 (embed (node i)) (embed (w i))).domRestrict _

private theorem row_rank (w : I → K) (i : I) :
    Module.finrank Geom (LinearMap.range (row w i)) ≤ 24736787 := by
  letI : Module.Finite Geom wideSpace := finiteWide
  let L := wideLocal (embed (node i)) (embed (w i))
  have hle : LinearMap.range (row w i) ≤ LinearMap.range L := by
    rintro _ ⟨Q,rfl⟩
    exact ⟨⟨Q.val,source_le_wide Q.property⟩,rfl⟩
  have hfin : Module.finrank Geom (LinearMap.range (row w i)) ≤
      Module.finrank Geom (LinearMap.range L) := Submodule.finrank_mono hle
  exact hfin.trans (per_position (embed (node i)) (embed (w i)))

private theorem exists_local (w : I → K) :
    ∃ Q : source, Q ≠ 0 ∧ ∀ i, row w i Q = 0 := by
  have hr : (∑ i, Module.finrank Geom (LinearMap.range (row w i))) ≤ 262144 * 24736787 := calc
    _ ≤ ∑ _ : I, (24736787 : ℕ) := Finset.sum_le_sum fun i _ => row_rank w i
    _ = _ := by simp
  have hroom : 262144 * 24736787 < Module.finrank Geom source := by
    rw [dim_source]
    decide
  exact LinearMap.exists_ne_zero_of_sum_finrank_range_lt (row w) (hr.trans_lt hroom)

/-- The Euler anchor at the actual low endpoint, using the published local-rank witnesses. -/
theorem exists_anchor (w : I → K) :
    ∃ P : Row 4, P ≠ 0 ∧ InBox (shape P) ⟨143,60,16⟩ ∧ A6966LowBase.ActiveFits P 179 ∧
      differentialWeightedDegree 133378 ((MvPolynomial.optionEquivRight Geom (Fin 4)).symm P) ≤
        107 * 179730 - 1 + 60 ∧
      ∀ (S : (Polynomial K)) (T : Finset I), S.natDegree ≤ 133378 → 179730 ≤ T.card →
        (∀ i ∈ T, S.eval (node i) = w i) → atJet P (extend S) = 0 := by
  classical
  obtain ⟨Q,hQ,hloc⟩ := exists_local w
  let V : wideSpace := ⟨Q.val, source_le_wide Q.property⟩
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q.val
  have hP : P ≠ 0 := by
    intro h
    exact hQ (Subtype.ext ((MvPolynomial.optionEquivRight Geom (Fin 4)).injective
      (h.trans (map_zero _).symm)))
  refine ⟨P,hP,shape_bound V,active_bound V,?_,?_⟩
  · simpa only [P,AlgEquiv.symm_apply_apply] using rawWeight V
  · intro S T hd hT hits
    rw [atJet_unflatten]
    have hS : (extend S).natDegree ≤ 133378 := Polynomial.natDegree_map_le.trans hd
    have hdeg := (source_eval Q (extend S) hS).trans_lt (by decide : 107*179730-1 < 107*179730)
    have heval (i : I) (hi : i ∈ T) : (extend S).eval (embed (node i)) = embed (w i) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom, hits i hi]
    exact eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
      (fun i => embed (node i)) T 107 179730
      ((RingHom.injective embed).comp node.injective).injOn hT
      (fun i hi => X_sub_C_pow_dvd_differentialSpecialization_of_contact
        Q.val (extend S) (embed (node i)) (embed (w i)) (heval i hi) (hloc i)) hdeg

/-- The actual low-band model and marks supply the same single anchor. -/
theorem anchor_of_family {cap u del Γ} (M : P1.ModelAt cap u del) (F : P1.FamilyAt 179730 M Γ)
    (hi : M.overhead ≤ 2307) :
    ∃ P : Row 4, P ≠ 0 ∧ InBox (shape P) ⟨143,60,16⟩ ∧ A6966LowBase.ActiveFits P 179 ∧
      differentialWeightedDegree 133378 ((MvPolynomial.optionEquivRight Geom (Fin 4)).symm P) ≤
        107*179730-1+60 ∧ ∀ γ∈Γ,atJet P (extend (F.scalar γ))=0 := by
  obtain ⟨P,nz,box,active,weight,zero⟩ := exists_anchor M.word
  refine ⟨P,nz,box,active,weight,?_⟩
  intro γ hγ
  let mark := F.mark γ hγ
  have degree : (F.scalar γ).natDegree ≤ 133378 := by
    rcases mark.scalar_degree with z | h
    · simp [z]
    · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at h
      omega
  exact zero _ mark.bad.support degree mark.bad.agreement mark.scalar_hits

end
end LowAnchor6970
end Z6969Source2267
