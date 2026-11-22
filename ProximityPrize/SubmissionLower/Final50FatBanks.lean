import ProximityPrize.SubmissionLower.Final50FatDefs

set_option Elab.async true
section
namespace Final50FatBanks
open K1_13_4_2 (Bank)
def cut : Bank → ℕ
  | .first => Final50Fat.firstCut
  | .second => Final50Fat.secondCut
def targetRank : Bank → ℕ
  | .first => 1
  | .second => Final50Fat.bankRank
theorem cut_large (b : Bank) : 131071 * b.box.b ≤ cut b + 1 := by
  cases b <;> decide
def rawBase (b : Bank) : ℕ := cut b + 1 - 131071 * b.box.b
def width (b : Bank) (h q k l : ℕ) : ℕ :=
  rawBase b + 131071 * (b.box.b - q) + (l + 2 * k) + (2300 + (b.box.b - q)) * h
end Final50FatBanks
end
section
namespace Final50FatBanks
open K1_13 (Geom)
open K1_13_4 K1_13_4_2
open K1_13_4_2_1 (jetSum)
open Function
open scoped BigOperators Polynomial
noncomputable section
open private Column colExp colX column column_li coordinate coordinate_column column_bounds
  space space_bounds from ProximityPrize.SubmissionLower.PortLow4
private abbrev NewColumn (b : Bank) (h : ℕ) :=
  Σ q : Fin (b.box.b + 1), Σ k : Fin (min q.val 1150 + 1),
    Σ l : Fin (min (q.val - k.val) (2300 - 2 * k.val) + 1),
      Fin (width b h q.val k.val l.val) × Fin 70001
private def offset (b : Bank) : ℕ := P0_9_4_1.cut b - cut b
private theorem cut_shift (b : Bank) : cut b + offset b = P0_9_4_1.cut b := by
  have h : cut b ≤ P0_9_4_1.cut b := by cases b <;> decide
  unfold offset
  omega
private theorem width_shift (b : Bank) (h q k l : ℕ) :
    width b h q k l + offset b = P0_9_4_1.width b h q k l := by
  have hc := cut_shift b
  have hl := cut_large b
  unfold width P0_9_4_1.width rawBase P0_9_4_1.rawBase
  omega
private def inOld (b : Bank) (h d : ℕ) (hd : d ≤ offset b) : NewColumn b h ↪ Column b h :=
  (Embedding.refl _).sigmaMap fun q =>
    (Embedding.refl _).sigmaMap fun k =>
      (Embedding.refl _).sigmaMap fun l =>
        ((Fin.addNatEmb d).trans (Fin.castLEEmb
          ((Nat.add_le_add_left hd _).trans_eq (width_shift b h q.val k.val l.val)))).prodMap
          (Embedding.refl _)
private abbrev base (b : Bank) (h : ℕ) := inOld b h 0 (Nat.zero_le _)
private def newSpace (b : Bank) (h : ℕ) : Submodule Geom PhysicalRow :=
  Submodule.span Geom (Set.range (column ∘ base b h))
private theorem occurs {b : Bank} {h : ℕ} {F : PhysicalRow}
    (hF : F ∈ newSpace b h) {e : SeedVar →₀ ℕ} {x : ℕ} (hne : (F.coeff e).coeff x ≠ 0) :
    ∃ c : NewColumn b h, colExp (base b h c) = e ∧ colX (base b h c) = x := by
  classical
  by_contra! hn
  have hle : newSpace b h ≤ LinearMap.ker (coordinate e x) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    change coordinate e x (column (base b h c)) = 0
    rw [coordinate_column, ite_eq_right]
    exact fun hc => (hn c hc.1 hc.2).elim
  exact hne (LinearMap.mem_ker.mp (hle hF))
private theorem fits (b : Bank) (h : ℕ) (F : PhysicalRow) (hF : F ∈ newSpace b h) :
    Caps b.box F ∧ TrueCut h (cut b + (b.box.b + b.box.j) * h) F := by
  have hle : newSpace b h ≤ space b h := Submodule.span_mono (by
    rintro _ ⟨c, rfl⟩
    exact ⟨base b h c, rfl⟩)
  refine ⟨(space_bounds b h F (hle hF)).1, ?_⟩
  intro e he
  obtain ⟨c, hc, hx⟩ := occurs hF (by
    rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
    exact MvPolynomial.mem_support_iff.mp he)
  rcases c with ⟨q,k,l,x,u⟩
  let shifted := inOld b h (offset b) le_rfl ⟨q,k,l,x,u⟩
  have hw := (column_bounds shifted).2.2.2.2
  have he' : colExp shifted = e := hc
  have hx' : colX shifted = (F.coeff e).natDegree + offset b :=
    congrArg (· + offset b) hx
  rw [he', hx'] at hw
  have hs := cut_shift b
  omega
theorem ambient (b : Bank) (h : ℕ) :
    ∃ V : Submodule Geom PhysicalRow, Module.Finite Geom V ∧
      (∀ F ∈ V, Caps b.box F ∧ TrueCut h (cut b + (b.box.b + b.box.j) * h) F) ∧
      Module.finrank Geom V = 70001 * jetSum b.box.b (width b h) := by
  refine ⟨newSpace b h, Module.Finite.span_of_finite _ (Set.finite_range _), fits b h, ?_⟩
  rw [newSpace, finrank_span_eq_card ((column_li b h).comp _ (base b h).injective)]
  simp only [NewColumn, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Nat.mul_comm _ 70001]
  unfold jetSum
  simp only [Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Fin.sum_univ_eq_sum_range]
end
end Final50FatBanks
end
section
namespace Final50FatBanks
open K1_13_4_2 (Bank poleDebit)
open K1_13_4_2_1 (jetSum)
open Finset
open scoped BigOperators
open private moment moment_eq slice antidifference credit extra pole_eq bank_moments
  from ProximityPrize.SubmissionLower.Fast074
private def rawVolume (b : Bank) : ℕ := moment b.box.b (rawBase b) 1 131071 0
private theorem volume_eq (b : Bank) (h : ℕ) :
    jetSum b.box.b (width b h) = rawVolume b + credit b.box.b * h := by
  simp only [width, rawVolume, moment, credit, jetSum, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun q _ => sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  ring
private theorem first_raw : rawVolume .first = 2808773216714362860 := by
  change moment 6789 3790812 1 131071 0 = _
  refine moment_eq 6789 3790812 1 131071 0 _ (by decide) ?_
  change antidifference (slice 6789 3790812 1 131071 0) 1151 = _
  have h0 : slice 6789 3790812 1 131071 0 0 = 707283588927417840 := by decide
  have h1 : slice 6789 3790812 1 131071 0 1 = 706652195589370800 := by decide
  have h2 : slice 6789 3790812 1 131071 0 2 = 706020845639253984 := by decide
  have h3 : slice 6789 3790812 1 131071 0 3 = 705389539039319520 := by decide
  have h4 : slice 6789 3790812 1 131071 0 4 = 704758275751819536 := by decide
  unfold antidifference
  rw [h0, h1, h2, h3, h4]
  decide
private theorem second_raw : rawVolume .second = 2829926035494441570 := by
  change moment 6820 2533860 1 131071 0 = _
  refine moment_eq 6820 2533860 1 131071 0 _ (by decide) ?_
  change antidifference (slice 6820 2533860 1 131071 0) 1151 = _
  have h0 : slice 6820 2533860 1 131071 0 0 = 712574084912676480 := by decide
  have h1 : slice 6820 2533860 1 131071 0 1 = 711938093152918896 := by decide
  have h2 : slice 6820 2533860 1 131071 0 2 = 711302144781073680 := by decide
  have h3 : slice 6820 2533860 1 131071 0 3 = 710666239759392960 := by decide
  have h4 : slice 6820 2533860 1 131071 0 4 = 710030378050128864 := by decide
  unfold antidifference
  rw [h0, h1, h2, h3, h4]
  decide
private theorem endpoint (b : Bank) :
    targetRank b + 262144 * (70001 * b.nodeRank) + 2413 * extra b.box.b ≤
      70001 * rawVolume b := by
  obtain ⟨_, _, hfirst, hsecond⟩ := bank_moments
  cases b
  · have he : extra Bank.first.box.b = 0x1cc973f372d9cdc := hfirst
    have ha : (1 : ℕ) + 262144 * (70001 * 0x9bab8f5dfb7) + 2413 * 0x1cc973f372d9cdc ≤
        70001 * 2808773216714362860 := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      targetRank Bank.first + 262144 * (70001 * Bank.first.nodeRank) + 2413 * x ≤ 70001 * y)
      he first_raw).mpr ha
  · have he : extra Bank.second.box.b = 0x1d32fca954a0ef7 := hsecond
    have ha : (1472355152501952209006 : ℕ) + 262144 * (70001 * 0x9bac59312df) +
        2413 * 0x1d32fca954a0ef7 ≤ 70001 * 2829926035494441570 := by decide
    exact (congrArg₂ (fun x y : ℕ =>
      targetRank Bank.second + 262144 * (70001 * Bank.second.nodeRank) + 2413 * x ≤ 70001 * y)
      he second_raw).mpr ha
theorem budget (b : Bank) (h : ℕ) (hh : h ≤ 2413) :
    targetRank b + 262144 * (70001 * b.nodeRank) + h * poleDebit b.box ≤
      70001 * jetSum b.box.b (width b h) := by
  have he := endpoint b
  have hm := Nat.mul_le_mul_right (extra b.box.b) hh
  rw [pole_eq, volume_eq, Nat.mul_add, Nat.mul_add]
  have hc : h * (70001 * credit b.box.b) = 70001 * (credit b.box.b * h) := by ring
  omega
end Final50FatBanks
end
section
namespace Final50FatBanks
noncomputable section
open K1 K1_13 K1_13_4 K1_13_4_2
open scoped Polynomial BigOperators
open private codim_inf_le codim_finset_inf_le separable_rank dimension_of_debits
  from ProximityPrize.SubmissionLower.Fast050
private theorem contact_bound : K1_13_4_2.c2 :=
  K1_13_4_2_2.of_children K1_13_4_2_2_1.proof K1_13_4_2_2_2.proof K1_13_4_2_2_3.proof
    K1_13_4_2_2_4.proof K1_13_4_2_2_5.proof K1_13_4_2_2_6.proof
private theorem simple_pole_bound : K1_13_4_2.c3 :=
  K1_13_4_2_3.of_children K1_13_4_2_3_1.proof K1_13_4_2_3_2.proof
private theorem deformation_bound : K1_13_4_2.c4 :=
  K1_13_4_2_4.of_children K1_13_4_2_4_1.proof K1_13_4_2_4_2.proof
private theorem rank_of_bounds (b : Bank) (w : I → K) {Γ s}
    (P : PoleData Γ s) (L : ResidueChart P) (hh : P.H.natDegree ≤ 2413) :
    HasRank w P L b.box (cut b) (targetRank b) := by
  classical
  obtain ⟨V, hV, hbox, hdimV⟩ := ambient b P.H.natDegree
  have hsize := (budget b P.H.natDegree hh).trans_eq hdimV.symm
  let : Module.Finite Geom V := hV
  have hcap : ∀ F ∈ V, Caps b.box F := fun F hF => (hbox F hF).1
  let A : I → Submodule Geom PhysicalRow := fun i => contactAt (embed (node i)) (embed (w i))
  let U : Submodule Geom PhysicalRow := ⨅ i, A i
  let W : Submodule Geom PhysicalRow := poleCondition P L b.box (liftX P.H)
  have hU : codimIn V U ≤ 262144 * (70001 * b.nodeRank) := by
    have hA (i : I) (_ : i ∈ Finset.univ) : codimIn V (A i) ≤ 70001 * b.nodeRank :=
      contact_bound b (embed (node i)) (embed (w i)) V hV hcap
    have h := codim_finset_inf_le V (Finset.univ : Finset I) A (70001 * b.nodeRank) hA
    have hc : (Finset.univ : Finset I).card = 262144 := Fintype.card_fin (2 ^ 18)
    rw [hc, Finset.inf_univ_eq_iInf] at h
    exact h
  have hW : codimIn V W ≤ P.H.natDegree * poleDebit b.box := by
    apply deformation_bound Γ s P L b.box V _ hV
    intro P' L' _ hdeg hsep
    rw [← hdeg]
    exact separable_rank simple_pole_bound P' L' b.box V hcap hsep
  have hdebit := (codim_inf_le V U W).trans (Nat.add_le_add hU hW)
  let S : Submodule Geom PhysicalRow := V ⊓ (U ⊓ W)
  have hdim : targetRank b ≤ Module.finrank Geom S := dimension_of_debits hsize hdebit
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := Geom) (M := ↥S) hdim
  let e : Fin (targetRank b) → PhysicalRow := fun i => (f i).val
  refine ⟨e, hf.map_injOn S.subtype Subtype.val_injective.injOn, ?_⟩
  intro i
  have hm := Submodule.mem_inf.mp (f i).property
  have hUW : e i ∈ U ⊓ W := hm.2
  have hb := hbox (e i) hm.1
  refine ⟨hb.1, hb.2, ?_, (mem_poleCondition P L b.box _ _).mp (Submodule.mem_inf.mp hUW).2⟩
  intro j
  have hmem : e i ∈ A j := (Submodule.mem_iInf A).mp (Submodule.mem_inf.mp hUW).1 j
  exact (mem_contactAt (embed (node j)) (embed (w j)) (e i)).mp hmem
theorem proof : Final50Fat.c1 := by
  intro w Γ s P L hh
  refine ⟨?_, rank_of_bounds .second w P L hh⟩
  obtain ⟨e, he, hsource⟩ := rank_of_bounds .first w P L hh
  let i : Fin (targetRank Bank.first) := ⟨0, by decide⟩
  exact ⟨e i, he.ne_zero i, hsource i⟩
end
end Final50FatBanks
end

#print axioms Final50FatBanks.proof
