import ProximityPrize.SubmissionLower.AnchorBlock82190
import ProximityPrize.SubmissionLower.AnchorSpace82190
import ProximityPrize.SubmissionLower.Fast070

set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Pascal82190
open K1_13 K1_13_1_1 MvPolynomial
open scoped BigOperators
noncomputable section

def degree (s : ℕ) : ℕ := min s (AnchorSpace82190.cap s)
theorem degree_le (s : ℕ) : degree s ≤ 48 := by
  apply (min_le_right s _).trans
  unfold AnchorSpace82190.cap
  split_ifs <;> decide

abbrev block (s : ℕ) (g : ℤ) := AnchorBlock82190.blockAt (degree s) s g

def lineCharge (d : ℕ) (lo order : ℤ) (b c : ℕ) : ℕ :=
  let fmin := max 0 ((lo - b - 2 * (min c 24 : ℕ) + 2) / 3)
  let rowMin := max fmin (3 * (d : ℤ) - 3 * b - 2 * c - order + 1)
  min (intervalSize fmin (min d 12)) (intervalSize rowMin ((d : ℤ) - b - c))
def pairCharge (d : ℕ) (lo : ℤ) (b : ℕ) : ℕ :=
  sumRange (min d 12 + 1) fun f =>
    intervalSize (max 0 ((lo - b - 3 * f + 1) / 2))
      (min ((d : ℤ) - f) ((48 - 3 * f) / 2))
def pascalCharge (s : ℕ) (g : ℤ) : ℕ :=
  let d := degree s
  let lo := -g
  let order := orderCutoff s g
  min (bandCount d lo (activeIndex g) 12)
    (sumRange (d+1) fun b => min (pairCharge d lo b) (sumRange (d-b+1) (lineCharge d lo order b)))

open private coefficient_of_filter support_projectJet rank_le_projected_sum
  from ProximityPrize.SubmissionLower.Fast054
theorem rank_block_le_active (s : ℕ) (g : ℤ) (hg : g < 90 - (s : ℤ)) :
    Module.finrank Geom (LinearMap.range (block s g)) ≤
      bandCount (degree s) (-g) (activeIndex g) 12 := by
  let d := degree s
  let B := bandSpace d (-g) 48 12
  let A := bandSpace d (-g) (activeIndex g) 12
  let cut := (90 - g).toNat
  let retain := fun e : Fin 4 →₀ ℕ => e.weight jetIndex < cut
  let project : B →ₗ[Geom] A := ((filterSupport retain).domRestrict B).codRestrict A (by
    intro Q
    apply (mem_restrictSupport_iff Geom).mpr
    intro e he
    have ⟨hret, hQ⟩ := coefficient_of_filter he
    obtain ⟨hdeg, hlo, hhi, htop⟩ := Q.property hQ
    refine ⟨hdeg, hlo, ?_, htop⟩
    dsimp [activeIndex]
    change e.weight jetIndex < cut at hret
    dsimp [cut] at hret
    omega)
  let trunc := weightedTruncation (R := Geom) targetOrder (orderCutoff s g).toNat
  let restricted := (trunc.comp backShift.toLinearMap).domRestrict A
  have fac : block s g = restricted.comp project := by
    apply LinearMap.ext
    intro Q
    let P := filterSupport retain (Q : Form)
    let H := filterSupport (fun e => ¬retain e) (Q : Form)
    change trunc (backShift (Q : Form)) = trunc (backShift P)
    have hsplit : P + H = (Q : Form) := filterSupport_add_filterSupport_not _ _
    have hH : H.IsWeightedHomogeneous (fun _ => (1 : ℕ)) d := by
      intro e he
      have hmem : e ∈ H.support := MvPolynomial.mem_support_iff.mpr he
      obtain ⟨_, hq⟩ := coefficient_of_filter hmem
      rw [← Finsupp.degree_eq_weight_one]
      exact (Q.property hq).1
    have hI : H ∈ restrictWeightedOrder jetIndex cut := by
      refine mem_restrictWeightedOrder.mpr fun e he => ?_
      exact Nat.le_of_not_lt (coefficient_of_filter he).1
    have hh := backShift_homogeneous hH
    have hj := backShift_index_order hI
    have hkill : trunc (backShift H) = 0 := by
      apply (weightedTruncation_eq_zero_iff _ _ _).mpr
      refine mem_restrictWeightedOrder.mpr fun e he => ?_
      have hdeg := hh (MvPolynomial.mem_support_iff.mp he)
      rw [← Finsupp.degree_eq_weight_one, degree_formula] at hdeg
      have heI := mem_restrictWeightedOrder.mp hj e he
      rw [jetIndex_formula] at heI
      rw [targetOrder_formula]
      have hd : d ≤ s := min_le_left _ _
      dsimp [cut, orderCutoff] at *
      omega
    rw [← hsplit, map_add, map_add, hkill, add_zero]
  have : Module.Finite Geom A := bandSpace_finite _ _ _ _
  calc
    _ = Module.finrank Geom (LinearMap.range (restricted.comp project)) := by rw [fac]
    _ ≤ Module.finrank Geom (LinearMap.range restricted) :=
      LinearMap.finrank_range_comp_le_left restricted project
    _ ≤ Module.finrank Geom A := LinearMap.finrank_range_le restricted
    _ = _ := finrank_bandSpace _ _ _ _
private theorem degree_of_mem_blockMap {s : ℕ} {g : ℤ}
    (Q : bandSpace (degree s) (-g) 48 12) {e : Fin 4 →₀ ℕ}
    (he : e ∈ (block s g Q).support) : e.degree = degree s := by
  have hQ : (Q : Form).IsWeightedHomogeneous (fun _ => (1 : ℕ)) (degree s) := by
    intro e he
    rw [← Finsupp.degree_eq_weight_one]
    exact (Q.property (MvPolynomial.mem_support_iff.mpr he)).1
  have h := (backShift_homogeneous hQ).weightedTruncation targetOrder (orderCutoff s g).toNat
  have hc := h (MvPolynomial.mem_support_iff.mp he)
  rwa [← Finsupp.degree_eq_weight_one] at hc
theorem rank_block_le_pascal (s : ℕ) (g : ℤ) (hg : g < 90 - (s : ℤ))
    (hline : ∀ (b c : ℕ), b + c ≤ degree s →
      Module.finrank Geom (LinearMap.range
        ((projectJet 2 c).comp ((projectJet 1 b).comp (block s g)))) ≤
        lineCharge (degree s) (-g) (orderCutoff s g) b c)
    (hpair : ∀ b ≤ degree s,
      Module.finrank Geom (LinearMap.range ((projectJet 1 b).comp (block s g))) ≤
        pairCharge (degree s) (-g) b) :
    Module.finrank Geom (LinearMap.range (block s g)) ≤ pascalCharge s g := by
  let d := degree s
  refine le_min (rank_block_le_active s g hg) ?_
  have h : Module.finrank Geom (LinearMap.range (block s g)) ≤
      ∑ b : Fin (d + 1),
        Module.finrank Geom (LinearMap.range ((projectJet 1 b).comp (block s g))) :=
    rank_le_projected_sum 1 (d + 1) (block s g) (fun Q e he => by
      have := degree_of_mem_blockMap Q he
      exact Nat.lt_succ_of_le ((Finsupp.le_degree 1 e).trans_eq this))
  refine h.trans ?_
  rw [sumRange_eq_fin]
  refine Finset.sum_le_sum fun b _ => le_min (hpair b (Nat.le_of_lt_succ b.isLt)) ?_
  have hs :=
    rank_le_projected_sum 2 (d - b.val + 1) ((projectJet 1 b).comp (block s g))
      (fun Q e he => by
        have ⟨hb, he'⟩ := support_projectJet he
        have hd := degree_of_mem_blockMap Q he'
        rw [degree_formula] at hd
        omega)
  refine hs.trans ?_
  rw [sumRange_eq_fin]
  exact Finset.sum_le_sum fun c _ => hline b c (by have := b.isLt; have := c.isLt; omega)
def c2 : Prop :=
  PascalEntries →
    ∀ (s : ℕ) (g : ℤ), s ≤ 120 → -48 ≤ g → g < 90 - (s : ℤ) →
      ∀ (b c : ℕ), b + c ≤ degree s →
        Module.finrank Geom (LinearMap.range
          ((projectJet 2 c).comp ((projectJet 1 b).comp (block s g)))) ≤
          lineCharge (degree s) (-g) (orderCutoff s g) b c
def c3 : Prop :=
  PascalEntries →
    ∀ (s : ℕ) (g : ℤ), s ≤ 120 → -48 ≤ g → g < 90 - (s : ℤ) →
      ∀ b ≤ degree s,
        Module.finrank Geom (LinearMap.range ((projectJet 1 b).comp (block s g))) ≤
          pairCharge (degree s) (-g) b
namespace Lines
private abbrev Exponent := Fin 4 →₀ ℕ
private abbrev Column (s : ℕ) (g : ℤ) :=
  {m : Exponent // BandExponent (degree s) (-g) 48 12 m}
private abbrev oldBasis (s : ℕ) (g : ℤ) :
    Module.Basis (Column s g) Geom (bandSpace (degree s) (-g) 48 12) :=
  basisRestrictSupport Geom {m | BandExponent (degree s) (-g) 48 12 m}
private abbrev lineMap (s : ℕ) (g : ℤ) (b c : ℕ) :=
  (projectJet 2 c).comp ((projectJet 1 b).comp (block s g))
private def colMin (g : ℤ) (b c : ℕ) : ℤ :=
  max 0 ((-g - b - 2 * (min c 24 : ℕ) + 2) / 3)
private def colMax (s : ℕ) : ℤ := min (degree s) 12
private def rowMin (s : ℕ) (g : ℤ) (b c : ℕ) : ℤ :=
  max (colMin g b c) (3 * (degree s : ℤ) - 3 * b - 2 * c - orderCutoff s g + 1)
private def rowMax (s b c : ℕ) : ℤ :=
  (degree s : ℤ) - b - c
private def lineRows (s : ℕ) (g : ℤ) (b c : ℕ) : Set Exponent :=
  {e | e.degree = degree s ∧ e 1 = b ∧ e 2 = c ∧
    (e.weight targetOrder : ℤ) < orderCutoff s g ∧ colMin g b c ≤ (e 3 : ℤ)}
private theorem lineRows_finite (s : ℕ) (g : ℤ) (b c : ℕ) :
    (lineRows s g b c).Finite :=
  (Finsupp.finite_of_degree_le (degree s)).subset fun _ he => Nat.le_of_eq he.1
variable {s : ℕ} {g : ℤ} {b c : ℕ}
private theorem column_coeff (m : Column s g) (e : Exponent) :
    (lineMap s g b c (oldBasis s g m)).coeff e =
      if e 2 = c then
        if e 1 = b then
          if e.weight targetOrder < (orderCutoff s g).toNat then
            (backShift (monomial m.val 1)).coeff e
          else 0
        else 0
      else 0 := by
  change (filterSupport (fun x => x 2 = c) (filterSupport (fun x => x 1 = b)
    (weightedTruncation targetOrder (orderCutoff s g).toNat
      (backShift ↑(oldBasis s g m))))).coeff e = _
  have hmono : (oldBasis s g m : Form) = monomial m.val 1 :=
    coe_basisRestrictSupport_apply (R := Geom) _ m
  rw [coeff_filterSupport, coeff_filterSupport, coeff_weightedTruncation, hmono]
private theorem column_data (m : Column s g) (e : Exponent)
    (hne : (lineMap s g b c (oldBasis s g m)).coeff e ≠ 0) :
    e.degree = degree s ∧ e 1 = b ∧ e 2 = c ∧
      (e.weight targetOrder : ℤ) < orderCutoff s g := by
  rw [column_coeff] at hne
  split_ifs at hne with hc hb ho
  · have hm : m.val.weight (fun _ => (1 : ℕ)) = degree s := by
      rw [← Finsupp.degree_eq_weight_one]
      exact m.property.1
    have hhom := backShift_homogeneous (isWeightedHomogeneous_monomial _ _ (1 : Geom) hm)
    have hd := hhom hne
    rw [← Finsupp.degree_eq_weight_one] at hd
    exact ⟨hd, hb, hc, by omega⟩
  all_goals contradiction
private theorem pascal_coeff (hPascal : PascalEntries) (m : Column s g) (e : Exponent)
    (hd : e.degree = degree s) (hb : e 1 = b) (hc : e 2 = c)
    (ho : (e.weight targetOrder : ℤ) < orderCutoff s g) :
    (lineMap s g b c (oldBasis s g m)).coeff e =
      pascalRowScale e * pascalColScale m.val * ((e 1).choose (m.val 1) : Geom) *
        ((e 2).choose (m.val 2) : Geom) * ((e 3).choose (m.val 3) : Geom) := by
  have hw : e.weight targetOrder < (orderCutoff s g).toNat := by omega
  rw [column_coeff, ite_eq_left hc, ite_eq_left hb, ite_eq_left hw]
  exact hPascal m.val e (m.property.1.trans hd.symm)
    (m.property.1.le.trans (degree_le _))
private theorem col_lower_and_row (hPascal : PascalEntries) (m : Column s g) (e : Exponent)
    (hne : (lineMap s g b c (oldBasis s g m)).coeff e ≠ 0) :
    colMin g b c ≤ (m.val 3 : ℤ) ∧ e ∈ lineRows s g b c := by
  obtain ⟨hd, hb, hc, ho⟩ := column_data m e hne
  rw [pascal_coeff hPascal m e hd hb hc ho] at hne
  have h₁ : m.val 1 ≤ b := by
    by_contra! h
    simp [hb, Nat.choose_eq_zero_of_lt h] at hne
  have h₂ : m.val 2 ≤ c := by
    by_contra! h
    simp [hc, Nat.choose_eq_zero_of_lt h] at hne
  have h₃ : m.val 3 ≤ e 3 := by
    by_contra! h
    simp [Nat.choose_eq_zero_of_lt h] at hne
  have hlow := m.property.2.1
  have hhigh := m.property.2.2.1
  rw [jetIndex_formula] at hlow hhigh
  have hcap : m.val 2 ≤ min c 24 := by omega
  have hf : colMin g b c ≤ (m.val 3 : ℤ) := by
    unfold colMin
    omega
  exact ⟨hf, hd, hb, hc, ho, by omega⟩
open private intervalIndex intervalIndex_recover from ProximityPrize.SubmissionLower.Fast070
private theorem row_bounds (e : lineRows s g b c) :
    rowMin s g b c ≤ (e.val 3 : ℤ) ∧ (e.val 3 : ℤ) ≤ rowMax s b c := by
  obtain ⟨hd, hb, hc, ho, htop⟩ := e.property
  rw [degree_formula] at hd
  rw [targetOrder_formula] at ho
  refine ⟨max_le htop ?_, ?_⟩
  · omega
  · unfold rowMax
    omega
private def rowIndex (e : lineRows s g b c) :
    Fin (intervalSize (rowMin s g b c) (rowMax s b c)) :=
  intervalIndex _ _ (e.val 3) (row_bounds e).1 (row_bounds e).2
private theorem rowIndex_injective :
    Function.Injective (rowIndex (s := s) (g := g) (b := b) (c := c)) := by
  intro e e' heq
  have hf : e.val 3 = e'.val 3 := by
    have hval := congrArg (fun i : Fin (intervalSize (rowMin s g b c) (rowMax s b c)) =>
      (rowMin s g b c + (i.val : ℤ)).toNat) heq
    simpa only [rowIndex, intervalIndex_recover] using hval
  obtain ⟨hd, hb, hc, _, _⟩ := e.property
  obtain ⟨hd', hb', hc', _, _⟩ := e'.property
  rw [degree_formula] at hd hd'
  apply Subtype.ext
  ext i
  fin_cases i
  · change e.val 0 = e'.val 0
    omega
  · exact hb.trans hb'.symm
  · exact hc.trans hc'.symm
  · exact hf
open private range_le_of_basis from ProximityPrize.SubmissionLower.Fast070
private theorem rank_le_rows (hPascal : PascalEntries) (s : ℕ) (g : ℤ) (b c : ℕ) :
    Module.finrank Geom (LinearMap.range (lineMap s g b c)) ≤
      intervalSize (rowMin s g b c) (rowMax s b c) := by
  let : Fintype (lineRows s g b c) := (lineRows_finite s g b c).fintype
  let S := restrictSupport Geom (lineRows s g b c)
  let : Module.Finite Geom S := restrictSupport_finite (lineRows_finite s g b c)
  have hsub : LinearMap.range (lineMap s g b c) ≤ S := by
    apply range_le_of_basis (oldBasis s g)
    intro m
    apply (mem_restrictSupport_iff Geom).mpr
    intro e he
    exact (col_lower_and_row hPascal m e (mem_support_iff.mp he)).2
  calc
    _ ≤ Module.finrank Geom S := Submodule.finrank_mono hsub
    _ = Fintype.card (lineRows s g b c) :=
      Module.finrank_eq_card_basis (basisRestrictSupport Geom (lineRows s g b c))
    _ ≤ _ := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective _ (rowIndex_injective (s := s) (g := g) (b := b) (c := c))
private def lineVector (s : ℕ) (g : ℤ) (b c : ℕ) [Fintype (lineRows s g b c)] (f : ℕ) :
    Form :=
  ∑ r : lineRows s g b c, monomial r.val (pascalRowScale r.val * ((r.val 3).choose f : Geom))
open scoped Classical in
private theorem coeff_lineVector [Fintype (lineRows s g b c)] (f : ℕ) (e : Exponent) :
    (lineVector s g b c f).coeff e =
      if e ∈ lineRows s g b c then pascalRowScale e * ((e 3).choose f : Geom) else 0 := by
  classical
  simp only [lineVector, coeff_sum, coeff_monomial]
  by_cases he : e ∈ lineRows s g b c
  · let r : lineRows s g b c := ⟨e, he⟩
    rw [ite_eq_left he, Finset.sum_eq_single r]
    · simp [r]
    · intro r' _ hne
      have h : r'.val ≠ e := fun eq => hne (Subtype.ext eq)
      simp [h]
    · simp
  · rw [ite_eq_right he]
    apply Finset.sum_eq_zero
    intro r _
    have h : r.val ≠ e := fun eq => he (eq ▸ r.property)
    simp [h]
private theorem column_eq_smul [Fintype (lineRows s g b c)] (hPascal : PascalEntries)
    (m : Column s g) :
    lineMap s g b c (oldBasis s g m) =
      (pascalColScale m.val * (b.choose (m.val 1) : Geom) * (c.choose (m.val 2) : Geom)) •
        lineVector s g b c (m.val 3) := by
  classical
  ext e
  rw [coeff_smul, coeff_lineVector]
  by_cases he : e ∈ lineRows s g b c
  · rw [ite_eq_left he]
    obtain ⟨hd, hb, hc, ho, _⟩ := he
    rw [pascal_coeff hPascal m e hd hb hc ho, hb, hc]
    rw [smul_eq_mul]
    ac_rfl
  · rw [ite_eq_right he, smul_zero]
    by_contra hne
    exact he (col_lower_and_row hPascal m e hne).2
private theorem rank_le_columns (hPascal : PascalEntries) (s : ℕ) (g : ℤ) (b c : ℕ) :
    Module.finrank Geom (LinearMap.range (lineMap s g b c)) ≤
      intervalSize (colMin g b c) (colMax s) := by
  let : Fintype (lineRows s g b c) := (lineRows_finite s g b c).fintype
  let v : Fin (intervalSize (colMin g b c) (colMax s)) → Form := fun i =>
    lineVector s g b c ((colMin g b c + (i.val : ℤ)).toNat)
  let S := Submodule.span Geom (Set.range v)
  let : Module.Finite Geom S := Module.Finite.span_of_finite Geom (Set.finite_range v)
  have hsub : LinearMap.range (lineMap s g b c) ≤ S := by
    apply range_le_of_basis (oldBasis s g)
    intro m
    by_cases hlo : colMin g b c ≤ (m.val 3 : ℤ)
    · have hdeg := (Finsupp.le_degree 3 m.val).trans_eq m.property.1
      have htop := m.property.2.2.2
      have hhi : (m.val 3 : ℤ) ≤ colMax s := by unfold colMax; omega
      let i := intervalIndex (colMin g b c) (colMax s) (m.val 3) hlo hhi
      rw [column_eq_smul hPascal]
      apply S.smul_mem
      apply Submodule.subset_span
      exact ⟨i, congrArg (lineVector s g b c) (intervalIndex_recover _ _ _ hlo hhi)⟩
    · have hz : lineMap s g b c (oldBasis s g m) = 0 := by
        ext e
        simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
        by_contra hne
        exact hlo (col_lower_and_row hPascal m e hne).1
      rw [hz]
      exact S.zero_mem
  refine (Submodule.finrank_mono hsub).trans ?_
  simpa only [S, Set.finrank, Fintype.card_fin] using finrank_range_le_card (R := Geom) v
theorem lines : Pascal82190.c2 := by
  intro hPascal s g _ _ _ b c _
  exact le_min (rank_le_columns hPascal s g b c) (rank_le_rows hPascal s g b c)
end Lines
namespace Pairs
private def pairLower (lo : ℤ) (b f : ℕ) : ℤ :=
  max 0 ((lo - b - 3 * f + 1) / 2)
private def pairUpper (d f : ℕ) : ℤ :=
  min ((d : ℤ) - f) ((48 - 3 * f) / 2)
private abbrev PairSlots (d : ℕ) (lo : ℤ) (b : ℕ) :=
  Σ f : Fin (min d 12 + 1), Fin (intervalSize (pairLower lo b f) (pairUpper d f))
private def pairSecond {d : ℕ} {lo : ℤ} {b : ℕ} (p : PairSlots d lo b) : ℕ :=
  (pairLower lo b p.1).toNat + p.2.val
private theorem card_pairSlots (d : ℕ) (lo : ℤ) (b : ℕ) :
    Fintype.card (PairSlots d lo b) = pairCharge d lo b := by
  calc
    _ = ∑ f : Fin (min d 12 + 1), Fintype.card
        (Fin (intervalSize (pairLower lo b f) (pairUpper d f))) := Fintype.card_sigma
    _ = _ := by
      rw [pairCharge, sumRange_eq_fin]
      exact Finset.sum_congr rfl fun f _ => Fintype.card_fin _
private theorem exists_pairSlot {d : ℕ} {lo : ℤ} {b : ℕ} {m : Fin 4 →₀ ℕ}
    (hm : BandExponent d lo 48 12 m) (hb : m 1 ≤ b) :
    ∃ p : PairSlots d lo b, pairSecond p = m 2 ∧ p.1.val = m 3 := by
  obtain ⟨hdeg, hlo, hhi, htop⟩ := hm
  rw [degree_formula] at hdeg
  rw [jetIndex_formula] at hlo hhi
  have hf : m 3 < min d 12 + 1 := by omega
  let lower := pairLower lo b (m 3)
  let upper := pairUpper d (m 3)
  have hnonneg : 0 ≤ lower := le_max_left _ _
  have hlower : lower ≤ (m 2 : ℤ) := by
    dsimp only [lower, pairLower]
    omega
  have hupper : (m 2 : ℤ) ≤ upper := by
    dsimp only [upper, pairUpper]
    omega
  let offset := m 2 - lower.toNat
  have hfit : offset < intervalSize lower upper := by
    dsimp only [offset, intervalSize]
    omega
  refine ⟨⟨⟨m 3, hf⟩, ⟨offset, hfit⟩⟩, ?_, rfl⟩
  change lower.toNat + offset = m 2
  dsimp only [offset]
  omega
open private sliceColumn project_monomial from ProximityPrize.SubmissionLower.Fast070
theorem pairs : Pascal82190.c3 := by
  classical
  intro hPascal s g _ _ _ b _
  let d := degree s
  let cutoff := (orderCutoff s g).toNat
  let B := bandSpace d (-g) 48 12
  let φ : B →ₗ[Geom] Form := (projectJet 1 b).comp (block s g)
  let basis : Module.Basis {m | BandExponent d (-g) 48 12 m} Geom B :=
    basisRestrictSupport Geom _
  let column (p : PairSlots d (-g) b) := sliceColumn d b cutoff (pairSecond p) p.1.val
  have hd : d ≤ 48  := degree_le _
  have hspan : LinearMap.range φ ≤ Submodule.span Geom (Set.range column) := by
    have htop : (⊤ : Submodule Geom B) = Submodule.span Geom (Set.range basis) :=
      basis.span_eq.symm
    rw [← Submodule.map_top, htop, Submodule.map_span_le]
    rintro _ ⟨m, rfl⟩
    change projectJet 1 b (weightedTruncation targetOrder cutoff
      (backShift (↑(basis m) : Form))) ∈ _
    rw [show (↑(basis m) : Form) = monomial m.val 1 from coe_basisRestrictSupport_apply _ _,
      project_monomial hPascal hd b cutoff m.val m.property.1]
    by_cases hb : m.val 1 ≤ b
    · obtain ⟨p, hp₂, hp₃⟩ := exists_pairSlot m.property hb
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨p, by simp only [column, hp₂, hp₃]⟩
    · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hb)]
  have : Module.Finite Geom (Submodule.span Geom (Set.range column)) :=
    Module.Finite.span_of_finite _ (Set.finite_range column)
  exact (Submodule.finrank_mono hspan).trans
    ((finrank_range_le_card (R := Geom) column).trans_eq (card_pairSlots d (-g) b))
end Pairs
theorem rank_le (s : ℕ) (g : ℤ) (hs : s ≤ 120) (hlo : -48 ≤ g) (hg : g < 90 - (s : ℤ)) :
    Module.finrank Geom (LinearMap.range (block s g)) ≤ pascalCharge s g :=
  rank_block_le_pascal s g hg (Lines.lines K1_13_1_1_1.proof s g hs hlo hg)
    (Pairs.pairs K1_13_1_1_1.proof s g hs hlo hg)

#print axioms rank_le
end
end Pascal82190
