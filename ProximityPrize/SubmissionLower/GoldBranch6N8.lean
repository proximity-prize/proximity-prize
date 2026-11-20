import ProximityPrize.SubmissionLower.GoldBranch6
import ProximityPrize.SubmissionLower.UpperBranch3
set_option Elab.async false
set_option autoImplicit true
section
namespace P3_6_1
noncomputable section
open K1_13 (Geom)
open P3_6 (physicalDegree anchorCutoff)
open PolynomialDifferential ReedSolomon.HiddenDerivative
def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 120 ∧
    u.some.weight (fun i => i.val) ≤ 48 ∧
    u (some 3) ≤ 10 ∧
    u (some 1) + u (some 2) + u (some 3) ≤ 48 - (u.some.degree - 113 + 1) / 2 ∧
    u.weight (differentialWeight physicalDegree) ≤ anchorCutoff
def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}
def anchorLocal (center received : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 90 center received).domRestrict anchorSpace
end
end P3_6_1
end
section
namespace P3_6_1
noncomputable section
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open scoped BigOperators
open private exponent_le_of_mem_translation_monomial eligible_of_le from ProximityPrize.SubmissionLower.Fast064
open private truncateX origin_truncateX old_rank from ProximityPrize.SubmissionLower.PortLowBase
private theorem centered_old_eligible {u v : JetVariable 3 →₀ ℕ}
    (h : v ≤ u) (hu : AnchorEligible u) (hx : v none < 90) :
    K1_13_1.AnchorEligible v := by
  obtain ⟨hd, hi, hf, ht, _⟩ := hu
  have hw := Finsupp.weight_le_weight
    (w := fun j : Fin 4 => 133671 - j.val) (w' := fun _ => 133671)
    (fun j => Nat.sub_le _ _) u.some
  have he : u.some.weight (fun _ => 133671) = 133671 * u.some.degree := by
    simp only [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, smul_eq_mul,
      Finset.mul_sum, Nat.mul_comm]
  rw [he] at hw
  apply eligible_of_le (u := u.some.optionElim 89)
  · intro j
    cases j with
    | none => simpa using Nat.le_of_lt_succ hx
    | some j => simpa using h (some j)
  · refine ⟨by simpa using hd, by simpa using hi, by simpa using hf, by simpa using ht, ?_⟩
    have hweight : differentialWeight (d := 3) 133671 =
        fun j => j.elim 1 (fun i => 133671 - i.val) := by
      funext j
      cases j <;> rfl
    rw [hweight, Finsupp.weight_optionElim, one_mul]
    exact (Nat.add_le_add_left (hw.trans (Nat.mul_le_mul_left _ hd)) _).trans (by decide)
private theorem centered_in_old_space (x y : Geom) (Q : anchorSpace) :
    truncateX (globalPointTranslation x y (Q : DifferentialPolynomial Geom 3)) ∈
      K1_13_1.anchorSpace := by
  classical
  rw [(Q : DifferentialPolynomial Geom 3).as_sum, map_sum, map_sum]
  refine Submodule.sum_mem _ fun u hu => ?_
  apply (mem_restrictSupport_iff Geom).mpr
  intro v hv
  have hn := mem_support_iff.mp hv
  rw [truncateX, coeff_filterSupport] at hn
  split at hn
  · exact centered_old_eligible
      (exponent_le_of_mem_translation_monomial x y u v _ (mem_support_iff.mpr hn))
      (Q.property hu) (by assumption)
  · exact (hn rfl).elim
theorem rank_local (x y : Geom) :
    Module.finrank Geom (LinearMap.range (anchorLocal x y)) ≤ 9199626 := by
  have hpositive (j : JetVariable 3) : differentialWeight 133671 j ≠ 0 := by
    cases j with
    | none => decide
    | some j =>
      have hj := j.isLt
      change 133671 - j.val ≠ 0
      omega
  have : Module.Finite Geom K1_13_1.anchorSpace :=
    restrictSupport_finite <|
      (Finsupp.finite_of_nat_weight_le _ hpositive _).subset fun _ hu => hu.2.2.2.2
  let f : anchorSpace →ₗ[Geom] DifferentialPolynomial Geom 3 :=
    (truncateX.comp (globalPointTranslation x y).toLinearMap).domRestrict anchorSpace
  let tr : anchorSpace →ₗ[Geom] K1_13_1.anchorSpace :=
    f.codRestrict K1_13_1.anchorSpace (centered_in_old_space x y)
  have h : anchorLocal x y = (K1_13_1.anchorLocal 0 0).comp tr := by
    apply LinearMap.ext
    intro Q
    change localConstraintAt 90 x y (Q : DifferentialPolynomial Geom 3) =
      localConstraintAt 90 0 0 (truncateX (globalPointTranslation x y Q))
    rw [origin_truncateX, localConstraintAt_eq_zero_globalPointTranslation]
  rw [h]
  exact (LinearMap.finrank_range_comp_le_left (K1_13_1.anchorLocal 0 0) tr).trans (old_rank 0 0)
end
end P3_6_1
end
section
set_option autoImplicit false
set_option maxRecDepth 2000
namespace P3_6_1
open K1_13 (Geom)
open PolynomialDifferential (JetVariable differentialWeight)
open scoped BigOperators
open private P0_9_1.Exponent P0_9_1.exponent exponent_some exponent_none P0_9_1.exponent_coordinates jet_weight
  indexWeight gradeCeiling gradeSlots sumRange sumRange_eq_fin from ProximityPrize.SubmissionLower.PortLowBase
private def firstWidth (a b c : ℕ) : ℕ :=
  90 * 179983 - 133344 * gradeCeiling a b c + indexWeight a b c
private def abscissaWidth (a b c j : ℕ) : ℕ := firstWidth a b c + 133344 * j
private theorem true_weight (x v a b c : ℕ) :
    (P0_9_1.exponent x v a b c).weight (differentialWeight 133344) =
      x + (v * 133344 + a * 133343 + b * 133342 + c * 133341) := by
  have hw : differentialWeight (d := 3) 133344 = fun i =>
      i.elim 1 (fun k => 133344 - k.val) := by
    funext i
    cases i <;> rfl
  rw [hw, P0_9_1.exponent, Finsupp.weight_optionElim, jet_weight]
  simp
private theorem eligible_exponent (x v a b c : ℕ) :
    AnchorEligible (P0_9_1.exponent x v a b c) ↔
      c ≤ 10 ∧ indexWeight a b c ≤ 48 ∧ v + (a + b + c) ≤ gradeCeiling a b c ∧
        x + 133344 * (v + (a + b + c)) < 90 * 179983 + indexWeight a b c := by
  unfold AnchorEligible gradeCeiling indexWeight
  rw [show P3_6.physicalDegree = 133344 from rfl,
    Finsupp.degree_eq_weight_one, jet_weight, jet_weight, true_weight]
  simp only [mul_one, Finsupp.some_apply, exponent_some, Matrix.cons_val_zero, le_min_iff]
  change (v + a + b + c ≤ 120 ∧ v * 0 + a * 1 + b * 2 + c * 3 ≤ 48 ∧
    c ≤ 10 ∧ a + b + c ≤ 48 - (v + a + b + c - 113 + 1) / 2 ∧
    x + (v * 133344 + a * 133343 + b * 133342 + c * 133341) ≤ 90 * 179983 - 1) ↔ _
  by_cases h : a + b + c = 0 <;> omega
private theorem width_iff (a b c j x : ℕ) (hj : j ≤ gradeCeiling a b c) :
    x < abscissaWidth a b c j ↔
      x + 133344 * (gradeCeiling a b c - j) < 90 * 179983 + indexWeight a b c := by
  have hgrade : gradeCeiling a b c ≤ 120 := min_le_left _ _
  unfold abscissaWidth firstWidth
  omega
private abbrev Slot :=
  Σ c : Fin 11, Σ b : Fin ((48 - 3 * c.val) / 2 + 1),
    Σ a : Fin (48 - 3 * c.val - 2 * b.val + 1),
      Σ j : Fin (gradeSlots a.val b.val c.val),
        Fin (abscissaWidth a.val b.val c.val j.val)
private abbrev Eligible := {u : P0_9_1.Exponent // AnchorEligible u}
private theorem slot_bounds (c b a j x : ℕ) :
    (c < 11 ∧ b < (48 - 3 * c) / 2 + 1 ∧ a < 48 - 3 * c - 2 * b + 1 ∧
      j < gradeSlots a b c ∧ x < abscissaWidth a b c j) ↔
    (c ≤ 10 ∧ indexWeight a b c ≤ 48 ∧ j + (a + b + c) ≤ gradeCeiling a b c ∧
      x < abscissaWidth a b c j) := by
  unfold indexWeight gradeSlots
  omega
private noncomputable def slotExponent (q : Slot) : Eligible := by
  rcases q with ⟨c, b, a, j, x⟩
  refine ⟨P0_9_1.exponent x (gradeCeiling a b c - j - (a.val + b.val + c.val)) a b c, ?_⟩
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
    simpa [slotExponent, exponent_some] using congrArg (fun u : Eligible => u.val (some 3)) h
  have eb : b = b' := by
    simpa [slotExponent, exponent_some] using congrArg (fun u : Eligible => u.val (some 2)) h
  have ea : a = a' := by
    simpa [slotExponent, exponent_some] using congrArg (fun u : Eligible => u.val (some 1)) h
  have ex : x = x' := by
    simpa [slotExponent, exponent_none] using congrArg (fun u : Eligible => u.val none) h
  subst c'
  subst b'
  subst a'
  subst x'
  have ev : gradeCeiling a b c - j - (a + b + c) =
      gradeCeiling a b c - j' - (a + b + c) := by
    simpa [slotExponent, exponent_some] using congrArg (fun u : Eligible => u.val (some 0)) h
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
  have he : P0_9_1.exponent x v a b c = u.val := P0_9_1.exponent_coordinates u.val
  obtain ⟨hc, hi, hg, hx⟩ := (eligible_exponent x v a b c).mp (he.symm ▸ u.property)
  let j := gradeCeiling a b c - (v + (a + b + c))
  have hj : j ≤ gradeCeiling a b c := Nat.sub_le _ _
  have hj' : gradeCeiling a b c - j = v + (a + b + c) := by
    dsimp [j]
    omega
  obtain ⟨hc', hb', ha', hj'', hx'⟩ := (slot_bounds c b a j x).mpr
    ⟨hc, hi, by dsimp [j]; omega, (width_iff a b c j x hj).mpr (hj'.symm ▸ hx)⟩
  refine ⟨⟨⟨c, hc'⟩, ⟨b, hb'⟩, ⟨a, ha'⟩, ⟨j, hj''⟩, ⟨x, hx'⟩⟩, Subtype.ext ?_⟩
  change P0_9_1.exponent x (gradeCeiling a b c - j - (a + b + c)) a b c = u.val
  have hv : gradeCeiling a b c - j - (a + b + c) = v := by omega
  rwa [hv]
private def tripleCount (a b c : ℕ) : ℕ :=
  let n := gradeSlots a b c
  n * firstWidth a b c + 133344 * (n * (n - 1) / 2)
private theorem sum_abscissaWidth (a b c : ℕ) :
    (∑ j : Fin (gradeSlots a b c), abscissaWidth a b c j) = tripleCount a b c := by
  rw [Fin.sum_univ_eq_sum_range (abscissaWidth a b c)]
  simp [abscissaWidth, tripleCount, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, Finset.sum_range_id]
private def rowCount (b c : ℕ) : ℕ :=
  sumRange (fun a => tripleCount a b c) (48 - 3 * c - 2 * b + 1)
private def sliceCount (c : ℕ) : ℕ :=
  sumRange (fun b => rowCount b c) ((48 - 3 * c) / 2 + 1)
private theorem slot_card : Fintype.card Slot = sumRange sliceCount 11 := by
  simp only [Slot, sliceCount, rowCount, Fintype.card_sigma, Fintype.card_fin, sumRange_eq_fin,
    sum_abscissaWidth]
private def rowTable : ℕ → List ℕ
  | 0 => [0x773a0a164,0x72301ec08,0x6d2a66f63,0x682923d37,0x632c96746,0x5e350f8e9,0x59427e2da, 0x5454a135d,
      0x4f6b378b6,0x4a8600129,0x45a4b9afa, 0x40c72346d, 0x3becfbbc6,0x371601f49,0x3241f4d3a, 0x2d70933dd,
      0x28a19c176,0x23d4ce449,0x1f09e8a9a, 0x1a40aa2ad, 0x1578d1ac6,0x10b21e129,0xbec4e41a, 0x727211dd,
      0x262558b6]
  | 1 => [0x70ccf091b, 0x6bbc5b574,0x66b09c6e4,0x61aa048c4,0x5ca882bce, 0x57abd5e46,0x52b3bce70,0x4dbff6a90,
      0x48d0420ea, 0x43e45dfc2,0x3efc0955c, 0x3a1702ffc, 0x353509de6,0x3055dcd5e, 0x2b793aca8,0x269ee2a08,
      0x21c6933c2,0x1cf00b81a, 0x181b0a554,0x13474e9b4,0xe749737e, 0x9a2a30f6,0x4d131060]
  | 2 => [0x6a43d3f98,0x652e0a8d8,0x601d77c1e, 0x5b11da7ae, 0x560af19cc, 0x51087c0bc, 0x4c0a38ac2,0x470fe6622,
      0x421944120,0x3d2610a00,0x38360af06,0x3348f1e76,0x2e5e84694,0x2976815a4,0x2490a79ea, 0x1facb61aa,
      0x1aca6bb28,0x15e9874a8,0x1109c7c6e, 0xc2aec0be, 0x74cb2fdc, 0x26edb80c]
  | 3 => [0x63a17dca8,0x5e86cf873,0x5970f63a8,0x545fb0c8b, 0x4f52be160,0x4a49dd06b, 0x4544cc7f0,0x40434b633,
      0x3b4518978,0x3649f3003,0x315199818,0x2c5bcaffb, 0x2768465f0,0x2276ca83b, 0x1d8716520,0x1898e8ae3,
      0x13ac007c8,0xec01ca13,0x9d4fc008,0x4ea5d7eb]
  | 4 => [0x5ce5eb4e2,0x57c5b56db, 0x52a9f2da2,0x4d926277b, 0x487ec32aa, 0x436ed3d73,0x3e625361a, 0x395900ae3,
      0x34529aa12,0x2f4ee01eb, 0x2a4d900b2,0x254e694ab, 0x20512ac1a, 0x1b5593543,0x165b61e6a, 0x1162555d3,
      0xc6a2c9c2,0x772a687b, 0x27b82042]
  | 5 => [0x560ff7866,0x50e997430,0x4bc748a2c, 0x46a8ca89e, 0x418ddbdca, 0x3c763b7f4,0x3761a8560,0x324fe1452,
      0x2d40a530e, 0x2833b2fd8,0x2328c98f4,0x1e1fa7ca6,0x19180c932,0x1411b6cdc, 0xf0c655e8,0xa07d729a,
      0x503cb136]
  | 6 => [0x4f1e7d754,0x49f150092,0x44c7d2966,0x3fa1c4014,0x3a7ee32e0,0x355eef00e, 0x3041a65e2,0x2b26c82a0,
      0x260e1348c, 0x20f7469ea, 0x1be2210fe, 0x16ce6180c, 0x11bbc6d58,0xcaa0ff26,0x798fbbba, 0x28849158]
  | 7 => [0x4810581cc, 0x42dbbac21,0x3daa6bb70,0x387c29dfd, 0x3350b420c, 0x2e27c95e1,0x2901287c0,0x23dc905ed,
      0x1eb9bfeac, 0x199876041,0x1478718f0,0xf59716fd, 0xa3b348ac, 0x51d79c41]
  | 8 => [0x40e4627ee, 0x3ba7b26fd, 0x366def06a, 0x3136d7279,0x2c0229b6e, 0x26cfa598d, 0x219f09b1a, 0x1c7014e59,
      0x17428618e, 0x12161c2fd, 0xcea960ea, 0x7bfb2999,0x29530b4e]
  | 9 => [0x3999779da, 0x345412146,0x2f1137874,0x29d0a6da8,0x24921ef26,0x1f555eb32,0x1a1a25010,0x14e030c04,
      0xfa740d52,0xa6f1423e, 0x5376990c]
  | 10 => [0x322e727b0,0x2cdfb4b1c, 0x2793203ae, 0x224873faa, 0x1cff6ed54,0x17b7cfaf0,0x1271556c2,0xd2bbef0e,
      0x7e6cb218,0x2a238e24]
  | _ => []
private theorem row0 (b : Fin 25) : rowCount b 0 = (rowTable 0)[b.val]! := by fin_cases b <;> decide
private theorem row1 (b : Fin 23) : rowCount b 1 = (rowTable 1)[b.val]! := by fin_cases b <;> decide
private theorem row2 (b : Fin 22) : rowCount b 2 = (rowTable 2)[b.val]! := by fin_cases b <;> decide
private theorem row3 (b : Fin 20) : rowCount b 3 = (rowTable 3)[b.val]! := by fin_cases b <;> decide
private theorem row4 (b : Fin 19) : rowCount b 4 = (rowTable 4)[b.val]! := by fin_cases b <;> decide
private theorem row5 (b : Fin 17) : rowCount b 5 = (rowTable 5)[b.val]! := by fin_cases b <;> decide
private theorem row6 (b : Fin 16) : rowCount b 6 = (rowTable 6)[b.val]! := by fin_cases b <;> decide
private theorem row7 (b : Fin 14) : rowCount b 7 = (rowTable 7)[b.val]! := by fin_cases b <;> decide
private theorem row8 (b : Fin 13) : rowCount b 8 = (rowTable 8)[b.val]! := by fin_cases b <;> decide
private theorem row9 (b : Fin 11) : rowCount b 9 = (rowTable 9)[b.val]! := by fin_cases b <;> decide
private theorem row10 (b : Fin 10) : rowCount b 10 = (rowTable 10)[b.val]! := by fin_cases b <;> decide
private theorem rowTable_correct (c : Fin 11) :
    ∀ b : Fin ((48 - 3 * c.val) / 2 + 1), rowCount b c = (rowTable c)[b.val]! := by
  fin_cases c
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
private def sliceTotals : List ℕ :=
  [0x5e22ac537a, 0x53e180c8fb, 0x4a343a7cf4,0x40f849dec6,0x3858b1fb67,0x3031dd7716,
    0x28afc9cde0,0x21ae5a60bb, 0x1b5a9e4a98,0x158fefa044,0x107c712474]
private theorem sliceCount_eq (c : Fin 11) : sliceCount c = sliceTotals[c.val]! := by
  unfold sliceCount
  rw [sumRange_eq_fin]
  calc
    _ = ∑ b : Fin ((48 - 3 * c.val) / 2 + 1), (rowTable c)[b.val]! :=
      Finset.sum_congr rfl fun b _ => rowTable_correct c b
    _ = _ := by
      rw [← sumRange_eq_fin]
      fin_cases c <;> decide
private theorem totalCount : sumRange sliceCount 11 = 0x23180642897 := by
  rw [sumRange_eq_fin]
  calc
    _ = ∑ c : Fin 11, sliceTotals[c.val]! :=
      Finset.sum_congr rfl fun c _ => sliceCount_eq c
    _ = _ := by rw [← sumRange_eq_fin]; decide
theorem anchor_finrank : Module.finrank Geom anchorSpace = 0x23180642897 := by
  let e : Slot ≃ Eligible :=
    Equiv.ofBijective slotExponent ⟨slotExponent_injective, slotExponent_surjective⟩
  let b := MvPolynomial.basisRestrictSupport Geom {u : P0_9_1.Exponent | AnchorEligible u}
  exact (Module.finrank_eq_card_basis (b.reindex e.symm)).trans (slot_card.trans totalCount)
end P3_6_1
end
section
namespace P3_6_1
noncomputable section
open PolynomialDifferential ReedSolomon.HiddenDerivative
open P3 (K I node agreement)
open P3_6 (Messages TrueWeightLE physicalDegree anchorCutoff LowerRow SmallFactor Cover)
open K1_13 (Geom embed extend Row shape InBox atJet indexDegree jet OnFactor)
open K1_13_1 (anchorLead anchorLead_ne anchorLead_mul indexDegree_eq eval_anchorLead
  atJet_eq_anchorLead_of_top_zero)
open scoped BigOperators Polynomial
open private coeff_flatten atJet_unflatten anchorLead_term fits_of_prod from ProximityPrize.SubmissionLower.Fast040
private theorem trueWeight_iff {n D : ℕ} (P : Row n) :
    TrueWeightLE P D ↔
      ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).weightedTotalDegree
        (fun v => v.elim 1 (fun i => physicalDegree - i.val)) ≤ D := by
  classical
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  constructor
  · intro h u hu
    have hc : (P.coeff u.some).coeff (u none) ≠ 0 := by
      rw [← coeff_flatten, Finsupp.optionElim_some]
      exact MvPolynomial.mem_support_iff.mp hu
    have hm : u.some ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr (fun hz => hc (by simp [hz]))
    have hi := Polynomial.le_natDegree_of_ne_zero hc
    rw [← Finsupp.optionElim_some u, Finsupp.weight_optionElim, one_mul]
    apply (Nat.add_le_add_right hi _).trans
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using h _ hm
  · intro h m hm
    let d := (P.coeff m).natDegree
    have hc : (P.coeff m).coeff d ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)
    have hu : m.optionElim d ∈ ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).support :=
      MvPolynomial.mem_support_iff.mpr (by rwa [coeff_flatten])
    have hb := h _ hu
    rw [Finsupp.weight_optionElim, one_mul] at hb
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hb
private theorem differentialWeight_eq : differentialWeight (d := 3) physicalDegree =
    fun v => v.elim 1 (fun i => physicalDegree - i.val) := by
  funext v
  cases v <;> rfl
private theorem anchor_bounds (Q : anchorSpace) :
    InBox (shape (MvPolynomial.optionEquivRight Geom (Fin 4) Q)) ⟨120, 48, 10⟩ ∧
      TrueWeightLE (MvPolynomial.optionEquivRight Geom (Fin 4) Q) anchorCutoff := by
  classical
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  have hQ := (MvPolynomial.mem_restrictSupport_iff Geom).mp Q.property
  have hm (m : Fin 4 →₀ ℕ) (h : m ∈ P.support) : ∃ i, AnchorEligible (m.optionElim i) := by
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp h)
    refine ⟨i, hQ ?_⟩
    exact MvPolynomial.mem_support_iff.mpr (by
      rwa [← MvPolynomial.optionEquivRight_coeff_coeff, ← Polynomial.mem_support_iff])
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.some_optionElim, Finsupp.degree_apply, Finsupp.sum] using hi.1
  · apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.some_optionElim, Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hi.2.1
  · change P.degreeOf 3 ≤ 10
    rw [MvPolynomial.degreeOf_eq_sup]
    apply Finset.sup_le
    intro m h
    obtain ⟨i, hi⟩ := hm m h
    simpa only [Finsupp.optionElim_apply_some] using hi.2.2.1
  · apply (trueWeight_iff P).mpr
    rw [AlgEquiv.symm_apply_apply, ← differentialWeight_eq,
      MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
    exact fun m h => (hQ h).2.2.2.2
private theorem exists_anchor (w : I → K) :
    ∃ Q : Row 4, Q ≠ 0 ∧ InBox (shape Q) ⟨120, 48, 10⟩ ∧
      TrueWeightLE Q anchorCutoff ∧
      ∀ Γ s, Messages w Γ s → ∀ γ ∈ Γ, atJet Q (extend (s γ)) = 0 := by
  let localRows (i : I) := anchorLocal (embed (node i)) (embed (w i))
  have hr : (∑ i, Module.finrank Geom (LinearMap.range (localRows i))) ≤
      0x23180280000 := by
    calc
      _ ≤ ∑ _ : I, (9199626 : ℕ) := Finset.sum_le_sum fun i _ => rank_local _ _
      _ = _ := by simp
  have hDim : 0x23180280000 < Module.finrank Geom anchorSpace := by
    rw [anchor_finrank]
    decide
  obtain ⟨Q, hQ, hlocal⟩ :=
    LinearMap.exists_ne_zero_of_sum_finrank_range_lt localRows (hr.trans_lt hDim)
  let P : Row 4 := MvPolynomial.optionEquivRight Geom (Fin 4) Q
  have hP : P ≠ 0 := by
    intro h
    exact hQ (Subtype.ext ((MvPolynomial.optionEquivRight Geom (Fin 4)).injective
      (h.trans (map_zero _).symm)))
  obtain ⟨hbox, hweight⟩ := anchor_bounds Q
  refine ⟨P, hP, hbox, hweight, ?_⟩
  intro Γ s hm γ hγ
  obtain ⟨T, hT, hhit⟩ := hm.hits γ hγ
  have hdeg : differentialWeightedDegree physicalDegree (Q : DifferentialPolynomial Geom 3) <
      90 * agreement := by
    have h := (trueWeight_iff P).mp hweight
    rw [AlgEquiv.symm_apply_apply] at h
    rw [differentialWeightedDegree, differentialWeight_eq]
    exact lt_of_le_of_lt h (by decide : anchorCutoff < 90 * agreement)
  have hS : (extend (s γ)).natDegree ≤ physicalDegree :=
    Polynomial.natDegree_map_le.trans (hm.degree γ hγ)
  rw [atJet_unflatten]
  refine differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    (fun i => embed (node i)) (fun i => embed (w i)) T hdeg
    (fun i _ => hlocal i) _ hS
    ((RingHom.injective embed).comp node.injective).injOn hT ?_
  intro i hi
  rw [Polynomial.eval_map, Polynomial.eval₂_hom, hhit i hi]
section FactorCover
open MvPolynomial UniqueFactorizationMonoid
private theorem lower_of_anchor (P : Row 4) (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨120, 48, 10⟩) (hw : TrueWeightLE P anchorCutoff) :
    LowerRow (anchorLead P) := by
  refine ⟨anchorLead_ne hP, ?_, ?_, ?_⟩
  · rw [← weightedTotalDegree_one, weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    obtain ⟨u, hu, _, h⟩ := anchorLead_term P m hm
    have hab := (le_weightedTotalDegree (1 : Fin 4 → ℕ) hu)
    rw [weightedTotalDegree_one] at hab
    exact (h (1 : Fin 4 → ℕ)).trans (hab.trans hbox.1)
  · rw [indexDegree_eq, weightedTotalDegree, Finset.sup_le_iff]
    intro m hm
    obtain ⟨u, hu, _, h⟩ := anchorLead_term P m hm
    have hab := le_weightedTotalDegree (fun i => i.val) hu
    rw [← indexDegree_eq] at hab
    exact (h (fun i => i.val)).trans (hab.trans hbox.2.1)
  · intro m hm
    obtain ⟨u, hu, hc, h⟩ := anchorLead_term P m hm
    have hle := h (fun i => physicalDegree - i.val)
    rw [← hc]
    apply (Nat.add_le_add_left _ _).trans (hw u hu)
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm, Fin.val_castSucc] using hle
private theorem factor_small {P f : Row 4} (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨120, 48, 10⟩) (hw : TrueWeightLE P anchorCutoff)
    (hf : Irreducible f) (ht : 0 < (shape f).t) (hd : f ∣ P) : SmallFactor f := by
  refine ⟨hf, ht, ⟨?_, ?_, ?_⟩, ?_⟩
  · have h := weightedTotalDegree_le_of_dvd (1 : Fin 4 → ℕ) hd hP
    rw [weightedTotalDegree_one, weightedTotalDegree_one] at h
    exact h.trans hbox.1
  · have h := weightedTotalDegree_le_of_dvd (fun i => i.val) hd hP
    rw [← indexDegree_eq, ← indexDegree_eq] at h
    exact h.trans hbox.2.1
  · have h := weightedTotalDegree_le_of_dvd (Pi.single (3 : Fin 4) 1) hd hP
    simp only [weightedTotalDegree_piSingle] at h
    exact h.trans hbox.2.2
  · let e := MvPolynomial.optionEquivRight Geom (Fin 4)
    have hd' : e.symm f ∣ e.symm P := _root_.map_dvd e.symm hd
    have hP' : e.symm P ≠ 0 := fun h => hP (e.symm.injective (h.trans (map_zero _).symm))
    exact (trueWeight_iff f).mpr
      ((weightedTotalDegree_le_of_dvd _ hd' hP').trans ((trueWeight_iff P).mp hw))
private theorem cover_of_anchor {Γ : Finset K} {s : K → K[X]} (P : Row 4)
    (hP : P ≠ 0) (hbox : InBox (shape P) ⟨120, 48, 10⟩)
    (hw : TrueWeightLE P anchorCutoff)
    (hz : ∀ γ ∈ Γ, atJet P (extend (s γ)) = 0) :
    ∃ (n : ℕ) (g : Row 3) (f : Fin n → Row 4), Cover Γ s g f := by
  classical
  let _ : StrongNormalizationMonoid (Row 4) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := normalizedFactors P
  let T := A.toFinset.filter fun q => 0 < (shape q).t
  let n := Fintype.card ↥T
  let e : Fin n ≃ ↥T := (Fintype.equivFin ↥T).symm
  let f : Fin n → Row 4 := fun i => (e i).val
  have hT : ∀ q ∈ T, q ∈ A ∧ 0 < (shape q).t := by
    intro q hq
    simpa [T] using hq
  have hfi (i : Fin n) : f i ∈ A ∧ 0 < (shape (f i)).t := hT _ (e i).property
  have hd : (∏ i, f i) ∣ P := by
    have heq : (∏ i, f i) = ∏ q ∈ T, q := by
      rw [show (∏ i, f i) = ∏ q : ↥T, q.val from e.prod_comp Subtype.val]
      exact Finset.prod_coe_sort T id
    rw [heq]
    exact ((Finset.prod_dvd_prod_of_subset T A.toFinset id (Finset.filter_subset _ _)).trans
      (Multiset.toFinset_prod_dvd_prod A)).trans (prod_normalizedFactors hP).dvd
  refine ⟨n, anchorLead P, f, ⟨lower_of_anchor P hP hbox hw, ?_, ?_,
    fits_of_prod P hP hbox f (fun i => (hfi i).2) hd, ?_⟩⟩
  · intro i
    exact factor_small hP hbox hw (irreducible_of_normalized_factor _ (hfi i).1)
      (hfi i).2 (dvd_of_mem_normalizedFactors (hfi i).1)
  · intro i j hij hassoc
    apply hij
    apply e.injective
    exact Subtype.ext (mem_normalizedFactors_eq_of_associated (hfi i).1 (hfi j).1 hassoc)
  · intro γ hγ
    let S := extend (s γ)
    by_cases hg : atJet (anchorLead P) S = 0
    · exact Or.inl hg
    right
    have hSA : eval (jet S) A.prod = 0 := by
      have hdiv := _root_.map_dvd (eval (jet S)) (prod_normalizedFactors hP).symm.dvd
      change atJet P S ∣ eval (jet S) A.prod at hdiv
      rw [hz γ hγ, zero_dvd_iff] at hdiv
      exact hdiv
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hSA
    obtain ⟨q, hq, hqS⟩ := hSA
    have hqlead : atJet (anchorLead q) S ≠ 0 := by
      intro hzero
      obtain ⟨R, hR⟩ := dvd_of_mem_normalizedFactors hq
      apply hg
      rw [hR, anchorLead_mul, atJet, map_mul]
      exact mul_eq_zero_of_left hzero _
    have hqt : 0 < (shape q).t := by
      by_contra! h
      apply hqlead
      rw [← atJet_eq_anchorLead_of_top_zero q S (Nat.eq_zero_of_le_zero h)]
      exact hqS
    have hqT : q ∈ T := Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hq, hqt⟩
    let j := e.symm ⟨q, hqT⟩
    have hj : f j = q := congrArg Subtype.val (e.apply_symm_apply ⟨q, hqT⟩)
    exact ⟨j, by rw [hj, OnFactor, ← eval_anchorLead]; exact ⟨hqS, hqlead⟩⟩
end FactorCover
theorem proof : P3_6.c1 := by
  intro w Γ s hm
  obtain ⟨P, hP, hb, hw, hz⟩ := exists_anchor w
  exact cover_of_anchor P hP hb hw (hz Γ s hm)
end
end P3_6_1
end
section
namespace P3_6_2
noncomputable section
open K1_13 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open K1_13_2 (SourcePolynomial SourceExponent Local topWeight toRow)
open P3 (I K node)
open MvPolynomial (mem_support_iff)
open private weight_eq_sum pointContact from ProximityPrize.SubmissionLower.PortLowBase
def SourceEligible (e : SourceExponent) : Prop :=
  e.weight jetDegreeWeight ≤ 4012 ∧
  e.weight jetDerivativeWeight ≤ 1650 ∧
  e.weight topWeight ≤ 550 ∧
  e.weight (differentialWeight 133344) ≤ 3000 * 179983 - 1
def sourceExponents : Set SourceExponent := { e | SourceEligible e }
theorem sourceExponents_finite : sourceExponents.Finite := by
  refine (Finsupp.finite_of_nat_weight_le (differentialWeight (d := 3) 133344)
    ?_ (3000 * 179983 - 1)).subset (fun e he => he.2.2.2)
  intro v
  cases v with
  | none => decide
  | some j =>
    exact (differentialWeight_some_pos_of_order_lt_degree (by decide : 3 < 133344) j).ne'
def sourceColumns : Finset SourceExponent := sourceExponents_finite.toFinset
def SourceSpace : Submodule Geom SourcePolynomial :=
  MvPolynomial.restrictSupport Geom sourceExponents
instance : Module.Finite Geom SourceSpace :=
  MvPolynomial.restrictSupport_finite sourceExponents_finite
theorem row_bounds (Q : SourceSpace) :
    InBox (shape (toRow Q.1)) ⟨4012, 1650, 550⟩ ∧
    P3_6.TrueWeightLE (toRow Q.1) (3000 * 179983 - 1) := by
  classical
  have h (m : Fin 4 →₀ ℕ) (hm : m ∈ (toRow Q.1).support) :
      m.sum (fun _ a => a) ≤ 4012 ∧
      m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
      ((toRow Q.1).coeff m).natDegree + m.sum (fun i a => (133344 - i.val) * a) ≤
        3000 * 179983 - 1 := by
    let n := ((toRow Q.1).coeff m).natDegree
    have hc : (Q.1).coeff (m.optionElim n) ≠ 0 := by
      rw [← MvPolynomial.optionEquivRight_coeff_coeff]
      change ((toRow Q.1).coeff m).coeff n ≠ 0
      rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
      exact mem_support_iff.mp hm
    have supportBound : ∀ e ∈ Q.1.support, SourceEligible e := Q.2
    obtain ⟨hb, hj, ht, hw⟩ := supportBound _ (mem_support_iff.mpr hc)
    have jb : jetDegreeWeight (d := 3) = (fun v => v.elim 0 (fun _ => 1)) := by
      funext v; cases v <;> rfl
    have ji : jetDerivativeWeight (d := 3) = (fun v => v.elim 0 (fun i => i.val)) := by
      funext v; cases v <;> rfl
    have jw : differentialWeight (d := 3) 133344 =
        (fun v => v.elim 1 (fun i => 133344 - i.val)) := by
      funext v; cases v <;> rfl
    rw [jb] at hb
    rw [ji] at hj
    rw [jw] at hw
    change (m.optionElim n).weight (fun v => v.elim 0 (Pi.single (3 : Fin 4) (1 : ℕ))) ≤ 550 at ht
    simp only [Finsupp.weight_optionElim, zero_mul, zero_add, one_mul] at hb hj ht hw
    rw [Finsupp.weight_single_one_apply] at ht
    rw [weight_eq_sum m (fun _ => 1)] at hb
    rw [weight_eq_sum m (fun i => i.val)] at hj
    rw [weight_eq_sum m (fun i => 133344 - i.val)] at hw
    exact ⟨by simpa only [one_mul] using hb, hj, ht, hw⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact Finset.sup_le fun m hm => (h m hm).1
  · exact Finset.sup_le fun m hm => (h m hm).2.1
  · exact MvPolynomial.degreeOf_le_iff.mpr fun m hm => (h m hm).2.2.1
  · exact fun m hm => (h m hm).2.2.2
theorem translate_mem_source (x y : Geom) (Q : SourceSpace) :
    globalPointTranslation x y Q.1 ∈ SourceSpace := by
  have preserve (wt : JetVariable 3 → ℕ) (B : ℕ)
      (h : ∀ e ∈ Q.1.support, e.weight wt ≤ B) :
      ∀ e ∈ (globalPointTranslation x y Q.1).support, e.weight wt ≤ B :=
    MvPolynomial.mem_restrictWeightAtMost.mp
      (globalPointTranslation_mem_restrictWeightAtMost (Nat.zero_le _) (Nat.zero_le _)
        x y (MvPolynomial.mem_restrictWeightAtMost.mpr h))
  have h : ∀ e ∈ Q.1.support, SourceEligible e :=
    Q.2
  exact fun e he =>
    ⟨preserve jetDegreeWeight 4012 (fun t ht => (h t ht).1) e he,
      preserve jetDerivativeWeight 1650 (fun t ht => (h t ht).2.1) e he,
      preserve topWeight 550 (fun t ht => (h t ht).2.2.1) e he,
      preserve (differentialWeight 133344) (3000 * 179983 - 1)
        (fun t ht => (h t ht).2.2.2) e he⟩
def nodeMap (x y : Geom) : SourceSpace →ₗ[Geom] Local :=
  (localConstraintAt 3000 x y).domRestrict SourceSpace
def wordMap (w : I → K) : SourceSpace →ₗ[Geom] (I → Local) :=
  LinearMap.pi fun i => nodeMap (embed (node i)) (embed (w i))
theorem contact_of_word_kernel (w : I → K) (Q : SourceSpace) (hQ : wordMap w Q = 0) :
    Contact w (toRow Q.1) := by
  intro i S hS
  rw [K1_13_2.atJet_toRow]
  have hi : SatisfiesLocalConstraints (d := 3) 3000 (embed (node i)) (embed (w i)) Q.1 := by
    exact congrFun hQ i
  have hd := pointContact (embed (node i)) (embed (w i)) Q.1 S hS hi
  with_reducible exact hd
theorem finrank_source : Module.finrank Geom SourceSpace = sourceColumns.card := by
  have h : (↑sourceColumns : Set SourceExponent) = sourceExponents :=
    Set.Finite.coe_toFinset sourceExponents_finite
  rw [SourceSpace, ← h]
  exact MvPolynomial.finrank_restrictSupport_finset (K := Geom) sourceColumns
end
end P3_6_2
end
section
namespace P3_6_2
noncomputable section
open K1_13_2 (SourceExponent topWeight)
open PolynomialDifferential ReedSolomon.HiddenDerivative Finset
open scoped BigOperators
open private Column P0_9_2.exponent coordinates coordinates_exponent P0_9_2.exponent_coordinates scaled_sum
  from ProximityPrize.SubmissionLower.PortLowBase
private def width (a b c f : ℕ) : ℕ :=
  0x202ef7c8 + b + 2 * c + 3 * f - 133344 * (a + b + c + f)
private def tuples : Finset Column :=
  (range 551).sigma fun f =>
    (range ((1650 - 3 * f) / 2 + 1)).sigma fun c =>
      (range (1651 - 2 * c - 3 * f)).sigma fun b =>
        (range (4013 - b - c - f)).sigma fun a => range (width a b c f)
private theorem mem_columns (t : Column) :
    P0_9_2.exponent t ∈ sourceColumns ↔ t ∈ tuples := by
  rcases t with ⟨f, c, b, a, x⟩
  change P0_9_2.exponent ⟨f, c, b, a, x⟩ ∈ sourceExponents_finite.toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  change SourceEligible (P0_9_2.exponent ⟨f, c, b, a, x⟩) ↔ _
  simp only [tuples, mem_sigma, mem_range, SourceEligible, Finsupp.weight_eq_sum,
    Fintype.sum_option, Fin.sum_univ_succ, Fin.sum_univ_zero, smul_eq_mul,
    jetDegreeWeight_none, jetDegreeWeight_some, jetDerivativeWeight, differentialWeight,
    topWeight, Option.elim_none, Option.elim_some, P0_9_2.exponent, Finsupp.coe_equivFunOnFinite_symm]
  simp [width]
  omega
private theorem card_columns : sourceColumns.card = tuples.card := by
  let e : Column ≃ SourceExponent :=
    ⟨P0_9_2.exponent, coordinates, coordinates_exponent, P0_9_2.exponent_coordinates⟩
  exact (Finset.card_equiv e (fun t => (mem_columns t).symm)).symm
private def widthInt (a b c f : ℤ) : ℤ :=
  0x202ef7c8 + b + 2 * c + 3 * f - 133344 * (a + b + c + f)
private theorem cast_width (a b c f : ℕ) (h : a + b + c + f ≤ 4012) :
    (width a b c f : ℤ) = widthInt a b c f := by
  have hpos : 133344 * (a + b + c + f) ≤ 0x202ef7c8 + b + 2 * c + 3 * f := by omega
  simp [width, widthInt, Nat.cast_sub hpos]
private def prefixA (b c f n : ℤ) : ℤ :=
  n * (2 * widthInt 0 b c f - 133344 * (n - 1))
private def doubleA (b c f : ℤ) : ℤ :=
  prefixA b c f (4013 - b - c - f)
private def prefixB (c f n : ℤ) : ℤ :=
  let p := 4013 - c - f
  let q := 2 * widthInt 0 0 c f - 133344 * (p - 1)
  let r := 2 - 133344
  6 * n * p * q + 3 * n * (n - 1) * (p * r - q) - n * (n - 1) * (2 * n - 1) * r
private def twelveB (c f : ℤ) : ℤ :=
  prefixB c f (1651 - 2 * c - 3 * f)
private def prefixC (f n : ℤ) : ℤ :=
  let v₀ := twelveB 0 f
  let v₁ := twelveB 1 f
  let v₂ := twelveB 2 f
  let v₃ := twelveB 3 f
  24 * n * v₀ + 12 * n * (n - 1) * (v₁ - v₀) +
    4 * n * (n - 1) * (n - 2) * (v₂ - 2 * v₁ + v₀) +
    n * (n - 1) * (n - 2) * (n - 3) * (v₃ - 3 * v₂ + 3 * v₁ - v₀)
private def countA (b c f : ℕ) : ℤ :=
  ∑ a ∈ range (4013 - b - c - f), (width a b c f : ℤ)
private def countB (c f : ℕ) : ℤ :=
  ∑ b ∈ range (1651 - 2 * c - 3 * f), countA b c f
private def countC (f : ℕ) : ℤ :=
  ∑ c ∈ range ((1650 - 3 * f) / 2 + 1), countB c f
private theorem card_tuples_int : (tuples.card : ℤ) = ∑ f ∈ range 551, countC f := by
  simp only [tuples, card_sigma, card_range, Nat.cast_sum, countC, countB, countA]
private theorem countA_closed (b c f : ℕ) (h : b + 2 * c + 3 * f ≤ 1650) :
    2 * countA b c f = doubleA b c f := by
  have hsum : countA b c f =
      ∑ a ∈ range (4013 - b - c - f), widthInt a b c f := by
    apply sum_congr rfl
    intro a ha
    rw [mem_range] at ha
    exact cast_width a b c f (by omega)
  rw [hsum, scaled_sum 2 (fun a => widthInt a b c f) (prefixA b c f)
    (by simp [prefixA]) (by intro t; unfold prefixA widthInt; ring)]
  have hn : ((4013 - b - c - f : ℕ) : ℤ) = 4013 - b - c - f := by omega
  rw [hn, doubleA]
private theorem countB_closed (c f : ℕ) (h : 2 * c + 3 * f ≤ 1650) :
    12 * countB c f = twelveB c f := by
  calc
    12 * countB c f =
        ∑ b ∈ range (1651 - 2 * c - 3 * f), 6 * (2 * countA b c f) := by
      simp only [countB, ← mul_assoc, ← mul_sum, show (6 : ℤ) * 2 = 12 by decide]
    _ = 6 * ∑ b ∈ range (1651 - 2 * c - 3 * f), doubleA b c f := by
      rw [mul_sum]
      apply sum_congr rfl
      intro b hb
      rw [mem_range] at hb
      rw [countA_closed b c f (by omega)]
    _ = twelveB c f := by
      rw [scaled_sum 6 (fun b => doubleA b c f) (prefixB c f)
        (by simp [prefixB])
        (by intro t; unfold prefixB doubleA prefixA widthInt; ring)]
      have hn : ((1651 - 2 * c - 3 * f : ℕ) : ℤ) = 1651 - 2 * c - 3 * f := by omega
      rw [hn, twelveB]
private def closedC (f : ℕ) : ℤ :=
  prefixC f ((1650 - 3 * f) / 2 + 1 : ℕ)
private theorem countC_closed (f : ℕ) (hf : f < 551) :
    288 * countC f = closedC f := by
  calc
    288 * countC f =
        ∑ c ∈ range ((1650 - 3 * f) / 2 + 1), 24 * (12 * countB c f) := by
      simp only [countC, ← mul_assoc, ← mul_sum, show (24 : ℤ) * 12 = 288 by decide]
    _ = 24 * ∑ c ∈ range ((1650 - 3 * f) / 2 + 1), twelveB c f := by
      rw [mul_sum]
      apply sum_congr rfl
      intro c hc
      rw [mem_range] at hc
      rw [countB_closed c f (by omega)]
    _ = closedC f := by
      rw [scaled_sum 24 (fun c => twelveB c f) (prefixC f)
        (by simp [prefixC])
        (by intro t; unfold prefixC twelveB prefixB widthInt; ring)]
      rfl
private def pairPrefix (q : ℤ) : ℤ :=
  q * (0x6fcab31170103ec7200 + (q - 1) * (-0x603e4eec09cb79c80 +
    (q - 2) * (0x17649b0ab8dc580 + (q - 3) * (0x28375fe41100 +
      (q - 4) * 0x4d4108300))))
private theorem pair_step (q : ℕ) (hq : q < 275) :
    pairPrefix (q + 1) = pairPrefix q + 120 * (closedC (2 * q) + closedC (2 * q + 1)) := by
  have he : (((1650 - 3 * (2 * q)) / 2 + 1 : ℕ) : ℤ) = 826 - 3 * q := by omega
  have ho : (((1650 - 3 * (2 * q + 1)) / 2 + 1 : ℕ) : ℤ) = 824 - 3 * q := by omega
  simp only [closedC, he, ho, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  unfold pairPrefix prefixC twelveB prefixB widthInt
  ring
private theorem pairs_sum (n : ℕ) (hn : n ≤ 275) :
    120 * (∑ f ∈ range (2 * n), closedC f) = pairPrefix n := by
  induction n with
  | zero => simp [pairPrefix]
  | succ n ih =>
    have hindex : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := Nat.cast_succ n
    rw [hindex, sum_range_succ, sum_range_succ, add_assoc,
      mul_add, ih (by omega), hcast, pair_step n (by omega)]
theorem sourceColumns_card : sourceColumns.card = 0x4f46b23213028fc0a := by
  have h : 288 * (tuples.card : ℤ) = ∑ f ∈ range 551, closedC f := by
    rw [card_tuples_int, mul_sum]
    exact sum_congr rfl fun f hf => countC_closed f (mem_range.mp hf)
  have hprefix : pairPrefix 275 = 0x29ce47f223e735d1a0c00 := by rfl
  have hlast : closedC 550 = 0xd5e204cc64c0 := by rfl
  have hsum : 120 * (∑ f ∈ range 550, closedC f) = pairPrefix 275 :=
    pairs_sum 275 (by decide)
  rw [show 551 = 2 * 275 + 1 by decide, sum_range_succ,
    show 2 * 275 = 550 by decide, hlast] at h
  rw [hprefix] at hsum
  rw [card_columns]
  omega
end
end P3_6_2
end
section
namespace P3_6_2
noncomputable section
open K1_13 PolynomialDifferential ReedSolomon.HiddenDerivative
open K1_13_2 (SourceExponent Local toRow)
open P3 (I K node)
open scoped BigOperators
open private high_monomial_vanishes origin_rank map_independent_family from ProximityPrize.SubmissionLower.PortLowBase
private theorem old_eligible (e : SourceExponent) (he : SourceEligible e)
    (hx : e none < 3000) : K1_13_2.SourceEligible e := by
  have hw := weight_le_add_mul_totalJetDegree 133671 e
  change e.weight (differentialWeight 133671) ≤ e none + 133671 * e.weight jetDegreeWeight at hw
  refine ⟨he.1, he.2.1, he.2.2.1, ?_⟩
  have hb := he.1
  omega
private theorem node_range_le (x y : Geom) :
    LinearMap.range (nodeMap x y) ≤ LinearMap.range (K1_13_2.nodeMap 0 0) := by
  rintro _ ⟨Q, rfl⟩
  let R := globalPointTranslation x y Q.1
  have hR : R ∈ SourceSpace := translate_mem_source x y Q
  change localConstraintAt 3000 x y Q.1 ∈ _
  rw [localConstraintAt_eq_zero_globalPointTranslation]
  change localConstraintAt 3000 0 0 R ∈ _
  rw [congrArg (localConstraintAt 3000 0 0) R.as_sum, map_sum]
  refine Submodule.sum_mem _ fun e he => ?_
  by_cases hx : e none < 3000
  · have hOld : e ∈ K1_13_2.sourceExponents := old_eligible e (hR he) hx
    have hMono : MvPolynomial.monomial e (R.coeff e) ∈ K1_13_2.SourceSpace :=
      (MvPolynomial.monomial_mem_restrictSupport Geom).mpr (Or.inl hOld)
    exact ⟨⟨_, hMono⟩, rfl⟩
  · rw [high_monomial_vanishes _ _ (Nat.le_of_not_gt hx)]
    exact Submodule.zero_mem _
theorem word_rank_le (w : I → K) {b : ℕ}
    (h : Module.finrank Geom (LinearMap.range (K1_13_2.nodeMap 0 0)) ≤ b) :
    Module.finrank Geom (LinearMap.range (wordMap w)) ≤ 262144 * b := by
  let nmap (i : I) := nodeMap (embed (node i)) (embed (w i))
  let B (i : I) := LinearMap.range (nmap i)
  let f : SourceSpace →ₗ[Geom] (∀ i, B i) := LinearMap.pi fun i => (nmap i).rangeRestrict
  let g : (∀ i, B i) →ₗ[Geom] (I → Local) :=
    LinearMap.pi fun i => (B i).subtype.comp (LinearMap.proj i)
  have hw : wordMap w = g.comp f := rfl
  rw [hw]
  calc
    Module.finrank Geom (LinearMap.range (g.comp f)) ≤
        Module.finrank Geom (LinearMap.range g) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range f g)
    _ ≤ Module.finrank Geom (∀ i, B i) := g.finrank_range_le
    _ = ∑ i, Module.finrank Geom (B i) := Module.finrank_pi_fintype Geom
    _ ≤ ∑ _ : I, b := Finset.sum_le_sum fun i _ =>
      (Submodule.finrank_mono (node_range_le (embed (node i)) (embed (w i)))).trans h
    _ = 262144 * b := by simp [I, FrobeniusLocator.Native.I, ProximityPrize.Benchmark.IRSProfile.Index]
private theorem surplus {r k n : ℕ}
    (hr : r ≤ 262144 * 0x138fb014d2be6) (hn : n = 0x4f46b23213028fc0a)
    (he : r + k = n) : P3_6.sourceRank ≤ k := by
  change 0x107f1dec8090fc0a ≤ k
  omega
private theorem family_of_kernel (w : I → K) {n : ℕ}
    (hker : n ≤ Module.finrank Geom (LinearMap.ker (wordMap w))) :
    ∃ e : Fin n → Row 4, LinearIndependent Geom e ∧
      ∀ i, InBox (shape (e i)) P3_6.primaryBox ∧
        P3_6.TrueWeightLE (e i) P3_6.primaryCutoff ∧ Contact w (e i) := by
  let liftRow : LinearMap.ker (wordMap w) →ₗ[Geom] Row 4 :=
    toRow.toLinearMap.comp (SourceSpace.subtype.comp (LinearMap.ker (wordMap w)).subtype)
  have hinj : Function.Injective liftRow := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact toRow.injective hab
  let admissible (P : Row 4) := InBox (shape P) P3_6.primaryBox ∧
    P3_6.TrueWeightLE P P3_6.primaryCutoff ∧ Contact w P
  have hrows (Q : LinearMap.ker (wordMap w)) : admissible (liftRow Q) := by
    obtain ⟨hbox, hwt⟩ := row_bounds Q.1
    have hk : wordMap w Q.1 = 0 := (LinearMap.mem_ker (f := wordMap w)).mp Q.2
    have hcont := contact_of_word_kernel w Q.1 hk
    have happly : liftRow Q = toRow Q.1.1 := rfl
    rw [happly]
    exact ⟨hbox, hwt, hcont⟩
  have h := map_independent_family (V := LinearMap.ker (wordMap w)) (W := Row 4)
    (n := n) liftRow hinj admissible hrows hker
  simpa only [admissible] using h
theorem proof : P3_6.c2 := by
  intro w
  have hSource : Module.finrank Geom SourceSpace = 0x4f46b23213028fc0a := by
    rw [finrank_source, sourceColumns_card]
  exact family_of_kernel w
    (surplus (word_rank_le w origin_rank) hSource (wordMap w).finrank_range_add_finrank_ker)
end
end P3_6_2
end
section
namespace P3_6_3
noncomputable section
open P3 (I K)
open P3_6 (TrueWeightLE primaryBox primaryCutoff layerWidth)
open K1_13 (Row InBox shape Contact)
def requiredOrder (T : ℕ) : ℕ :=
  (primaryCutoff - T) / layerWidth + 1
def BankRow (w : I → K) (T : ℕ) (P : Row 4) : Prop :=
  InBox (shape P) primaryBox ∧ TrueWeightLE P T ∧ Contact w P
end
end P3_6_3
end
section
namespace P3_6_3
noncomputable section
open Polynomial
open P3 (I K node agreement)
open P3_6 (Messages SmallFactor ProperCut TrueWeightLE physicalDegree primaryBox
  PrimaryRank primaryCutoff layerWidth layerNeed sourceRank)
open K1_13 (Geom embed extend Row shape InBox OrderAt indexDegree remaining)
open K1_13_3 (symbolAt symbolIndex cofactor_rank)
open scoped BigOperators
open private exists_fresh specialization_bounds sum_by_layer from ProximityPrize.SubmissionLower.PortLowBase
def c1 : Prop :=
  ∀ (w : I → K) (T : ℕ) (P : Row 4), T ≤ primaryCutoff → BankRow w T P →
    ∀ S : Geom[X], S.natDegree ≤ physicalDegree →
      (∃ H : Finset I, agreement ≤ H.card ∧
        ∀ i ∈ H, S.eval (embed (node i)) = embed (w i)) →
      OrderAt P S (requiredOrder T)
def c2 : Prop :=
  ∀ (f P : Row 4) (Γ : Finset K) (s : K → K[X]) (d a : ℕ),
    SmallFactor f →
    InBox (shape P) primaryBox → TrueWeightLE P primaryCutoff →
    (∀ γ ∈ Γ, OrderAt P (extend (s γ)) d) →
    a < d → f ^ a ∣ P → (¬ f ^ (a + 1) ∣ P) →
    ProperCut f Γ s (d - a)
def c3 : Prop :=
  ∀ (w : I → K) (x : Geom), PrimaryRank w →
    (∀ i : I, x ≠ embed (node i)) →
    ∃ r : ℕ → ℕ, sourceRank ≤ ∑ T ∈ Finset.range (primaryCutoff + 1), r T ∧
      ∀ T ≤ primaryCutoff, ∃ e : Fin (r T) → Row 4,
        (∀ i, BankRow w T (e i)) ∧
        LinearIndependent Geom (fun i => symbolAt x (e i))
private theorem exists_availability (hc : c1) (hd : c2)
    {w : I → K} {Γ : Finset K} {s : K → K[X]} (hm : Messages w Γ s)
    {f : Row 4} (hf : SmallFactor f) :
    ∃ l : ℕ, (∀ T ≤ primaryCutoff, ∀ P, BankRow w T P → f ^ (requiredOrder T - l) ∣ P) ∧
      (0 < l → ProperCut f Γ s l) := by
  classical
  let admissible (l : ℕ) : Prop :=
    ∀ T ≤ primaryCutoff, ∀ P, BankRow w T P → f ^ (requiredOrder T - l) ∣ P
  have hex : ∃ l, admissible l := by
    refine ⟨primaryCutoff / layerWidth + 1, fun T _ P _ => ?_⟩
    have hle : requiredOrder T ≤ primaryCutoff / layerWidth + 1 :=
      Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le _ _)) _
    rw [Nat.sub_eq_zero_of_le hle, pow_zero]
    exact one_dvd P
  let l := Nat.find hex
  have hl : admissible l := Nat.find_spec hex
  refine ⟨l, hl, fun hpos => ?_⟩
  have hbad : ¬ admissible (l - 1) := Nat.find_min hex (by omega)
  dsimp only [admissible] at hbad
  push Not at hbad
  obtain ⟨T, hT, P, hP, hnext⟩ := hbad
  have hle : l ≤ requiredOrder T := by
    by_contra! hlt
    have heq : requiredOrder T - (l - 1) = 0 := by omega
    exact hnext (by rw [heq, pow_zero]; exact one_dvd P)
  have hstep : requiredOrder T - (l - 1) = (requiredOrder T - l) + 1 := by omega
  have horder : ∀ γ ∈ Γ, OrderAt P (extend (s γ)) (requiredOrder T) := by
    intro γ hγ
    apply hc w T P hT hP
    · simpa only [extend, natDegree_map_eq_of_injective (RingHom.injective embed)] using
        hm.degree γ hγ
    · obtain ⟨H, hcard, hH⟩ := hm.hits γ hγ
      refine ⟨H, hcard, fun i hi => ?_⟩
      rw [extend, eval_map, eval₂_at_apply, hH i hi]
  have hweight : TrueWeightLE P primaryCutoff := fun m hm => (hP.2.1 m hm).trans hT
  have hcut := hd f P Γ s (requiredOrder T) (requiredOrder T - l) hf hP.1
    hweight horder (by omega) (hl T hT P hP) (by rwa [hstep] at hnext)
  have heq : requiredOrder T - (requiredOrder T - l) = l := by omega
  rwa [heq] at hcut
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : P3_6.c3 := by
  classical
  intro w Γ s hm hr n g f hf
  choose l hl hcut using fun i => exists_availability h1 h2 hm (hf.factors i)
  obtain ⟨x, hx, hsup⟩ := exists_fresh f
  obtain ⟨r, hrank, hfamilies⟩ := h3 w x hr hx
  have hnz : ∀ i, symbolAt x (f i) ≠ 0 := by
    intro i hz
    have hzero := hsup i
    rw [hz, MvPolynomial.support_zero, eq_comm, MvPolynomial.support_eq_empty] at hzero
    exact (hf.factors i).1.ne_zero hzero
  let cost (k : ℕ) :=
    remaining (∑ i, (k + 1 - l i) * (shape (f i)).b)
      (∑ i, (k + 1 - l i) * (shape (f i)).j)
  have hcost : ∀ T ≤ primaryCutoff, r T ≤ cost ((primaryCutoff - T) / layerWidth) := by
    intro T hT
    obtain ⟨e, he, hei⟩ := hfamilies T hT
    let a (i : Fin n) := requiredOrder T - l i
    have hdiv (i : Fin (r T)) : (∏ j, f j ^ a j) ∣ e i := by
      apply Fintype.prod_dvd_of_isRelPrime
      · intro j k hjk
        have hj := (hf.factors j).1
        have hk := (hf.factors k).1
        exact (hj.isRelPrime_iff_not_dvd.mpr
          (fun h => hf.different j k hjk (hj.associated_of_dvd hk h))).pow
      · intro j
        exact hl j T hT (e i) (he i)
    have hbound := cofactor_rank n (fun i => symbolAt x (f i)) a hnz (r T)
      (fun i => symbolAt x (e i)) hei (fun i => by
        obtain ⟨hb, hj⟩ := specialization_bounds x (e i) (he i).1
        exact ⟨hb, hj, by simpa only [map_prod, map_pow] using map_dvd (symbolAt x) (hdiv i)⟩)
    have hb (i : Fin n) : (symbolAt x (f i)).totalDegree = (shape (f i)).b := by
      change (symbolAt x (f i)).totalDegree = (f i).totalDegree
      unfold MvPolynomial.totalDegree
      rw [hsup]
    have hj (i : Fin n) : symbolIndex (symbolAt x (f i)) = (shape (f i)).j := by
      change symbolIndex (symbolAt x (f i)) = indexDegree (f i)
      unfold symbolIndex indexDegree
      rw [hsup]
    simpa only [cost, a, requiredOrder, hb, hj] using hbound
  have hsum : sourceRank ≤ layerWidth * ∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k :=
    hrank.trans ((Finset.sum_le_sum fun T hT =>
      hcost T (Nat.le_of_lt_succ (Finset.mem_range.mp hT))).trans (sum_by_layer primaryCutoff layerWidth (by decide) cost))
  refine ⟨l, ?_, hcut⟩
  change layerNeed ≤ ∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k
  have hceil : layerWidth * (layerNeed - 1) < sourceRank := by
    change 0x107f1dec80909796 < 0x107f1dec8090fc0a
    decide
  by_contra! hsmall
  have hpred : (∑ k ∈ Finset.range (1 + primaryCutoff / layerWidth), cost k) ≤
      layerNeed - 1 := by omega
  exact (not_le_of_gt hceil) (hsum.trans (Nat.mul_le_mul_left layerWidth hpred))
end
end P3_6_3
end
section
set_option maxRecDepth 12000
namespace P3_6_3_1
noncomputable section
open Polynomial FrobeniusLocator ProximityPrize.Benchmark
open P3 (I K node agreement)
open P3_6 (TrueWeightLE physicalDegree primaryCutoff layerWidth)
open P3_6_3 (BankRow requiredOrder)
open K1_13 (Geom embed Row jet)
open K1_13_3_1 (line)
open scoped BigOperators
open private eval_line line_contacts_zero from ProximityPrize.SubmissionLower.Fast074
open private order_of_locator_lines from ProximityPrize.SubmissionLower.Fast074
private def Bounded (Q : Polynomial Geom[X]) (b : ℕ) : Prop :=
  ∀ j, (Q.coeff j).natDegree ≤ b + layerWidth * j
private theorem bounded_mul {F G : Polynomial Geom[X]} {a b : ℕ}
    (hF : Bounded F a) (hG : Bounded G b) : Bounded (F * G) (a + b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum, Nat.mul_add]
  omega
private theorem bounded_C (f : Geom[X]) {a : ℕ} (hf : f.natDegree ≤ a) :
    Bounded (Polynomial.C f) a := by
  intro j
  by_cases h : j = 0
  · simpa [h] using hf
  · simp [Polynomial.coeff_C, h]
private theorem bounded_prod {ι : Type*} (A : Finset ι)
    (f : ι → Polynomial Geom[X]) (b : ι → ℕ) (hf : ∀ i ∈ A, Bounded (f i) (b i)) :
    Bounded (∏ i ∈ A, f i) (∑ i ∈ A, b i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using bounded_C (1 : Geom[X]) (a := 0) (by simp)
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact bounded_mul (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
private theorem bounded_pow {f : Polynomial Geom[X]} {b : ℕ} (hf : Bounded f b) (n : ℕ) :
    Bounded (f ^ n) (b * n) := by
  induction n with
  | zero => simpa using bounded_C (1 : Geom[X]) (a := 0) (by simp)
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact bounded_mul ih hf
private theorem line_degree (P : Row 4) (S U : Geom[X]) (T : ℕ)
    (hP : TrueWeightLE P T) (hS : S.natDegree ≤ physicalDegree)
    (hU : U.natDegree ≤ agreement + 3) (j : ℕ) :
    ((line P S U).coeff j).natDegree ≤ T + layerWidth * j := by
  let b (i : Fin 4) : ℕ := physicalDegree - i.val
  let F (i : Fin 4) : Polynomial Geom[X] :=
    Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin 4) : Bounded (F i) (b i) := by
    intro k
    have hs : (jet S i).natDegree ≤ b i :=
      (natDegree_hasseDeriv_le S i.val).trans (Nat.sub_le_sub_right hS _)
    have hu : (jet U i).natDegree ≤ b i + layerWidth := by
      refine (natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi : i.val ≤ physicalDegree := (Nat.le_of_lt_succ i.isLt).trans (by decide)
      have hwidth : agreement + 3 = layerWidth + physicalDegree := by decide
      change agreement + 3 - i.val ≤ (physicalDegree - i.val) + layerWidth
      rw [hwidth, Nat.add_sub_assoc hi, Nat.add_comm layerWidth]
    change ((Polynomial.C (jet S i) + Polynomial.C (jet U i) *
      Polynomial.X).coeff k).natDegree ≤ b i + layerWidth * k
    rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
    by_cases h0 : k = 0
    · simpa [h0] using hs
    · by_cases h1 : k = 1
      · simpa [h1] using hu
      · simp [h0, h1]
  unfold line
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  have hterm := bounded_mul (bounded_C (P.coeff m) le_rfl)
    (bounded_prod m.support (fun i => F i ^ m i) (fun i => b i * m i)
      (fun i _ => bounded_pow (hF i) (m i))) j
  exact hterm.trans (Nat.add_le_add_right (hP m hm) _)
private theorem line_coeff_zero (w : I → K) (T : ℕ) (P : Row 4) (S : Geom[X])
    (hP : BankRow w T P) (hS : S.natDegree ≤ physicalDegree)
    (A : Finset I) (hA : A.card = agreement)
    (hhit : ∀ i ∈ A, S.eval (embed (node i)) = embed (w i))
    (V : Geom[X]) (hV : V.natDegree ≤ 3) (j : ℕ)
    (hj : T + layerWidth * j ≤ primaryCutoff) :
    (line P S (locator (fun i => embed (node i)) A * V)).coeff j = 0 := by
  classical
  let x (i : I) : Geom := embed (node i)
  let L := locator x A
  let U := L * V
  have hU : U.natDegree ≤ agreement + 3 := by
    exact natDegree_mul_le.trans (by rw [locator_natDegree, hA]; exact Nat.add_le_add_left hV _)
  let Q := line P S U
  have hcontact (i : I) (hi : i ∈ A) (c : Geom) :
      (Polynomial.X - C (x i)) ^ 3000 ∣ Q.eval (C c) := by
    rw [show Q = line P S U from rfl, eval_line]
    apply hP.2.2
    have hL : L.eval (x i) = 0 := locator_eval_zero x A i hi
    have hU0 : U.eval (x i) = 0 := by simp [U, hL]
    simpa [x, eval_smul, hU0] using hhit i hi
  have hx : Function.Injective x :=
    (RingHom.injective embed).comp IRSProfile.domain.injective
  have hb := (line_degree P S U T hP.2.1 hS hU j).trans hj
  have hdegree : (Q.coeff j).natDegree < 3000 * A.card := by
    rw [hA]
    exact hb.trans_lt (Nat.sub_lt (Nat.mul_pos (by decide) (by decide)) (by decide))
  exact line_contacts_zero Q A x hx 3000 hcontact j hdegree
theorem proof : P3_6_3.c1 := by
  intro w T P hT hP S hS hits
  obtain ⟨H, hH, hhits⟩ := hits
  obtain ⟨A, hAH, hA⟩ := Finset.exists_subset_card_eq hH
  let x (i : I) := embed (node i)
  apply order_of_locator_lines P S (locator x A) (locator_monic x A).ne_zero
  intro V hV j hj
  apply line_coeff_zero w T P S hP hS A hA (fun i hi => hhits i (hAH hi)) V hV j
  have hj' : j ≤ (primaryCutoff - T) / layerWidth := Nat.lt_succ_iff.mp hj
  have hq := Nat.div_mul_le_self (primaryCutoff - T) layerWidth
  rw [Nat.mul_comm _ layerWidth] at hq
  calc
    T + layerWidth * j ≤ T + layerWidth * ((primaryCutoff - T) / layerWidth) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left layerWidth hj') T
    _ ≤ T + (primaryCutoff - T) := Nat.add_le_add_left hq T
    _ = primaryCutoff := Nat.add_sub_of_le hT
end
end P3_6_3_1
end
section
namespace P3_6_3_2
noncomputable section
open Polynomial
open P3_6 (SmallFactor TrueWeightLE physicalDegree primaryBox primaryCutoff)
open K1_13 (Geom embed extend Row Shape shape InBox indexDegree)
open private translateTop topHasse topHasse_coeff source_support sum_add_top total_add_top
  apply_add_top erase_top_add topHasse_order topHasse_zero exact_hasse_not_dvd from ProximityPrize.SubmissionLower.PortLowBase
private theorem topHasse_bounds (box : Shape) (T a : ℕ) (P : Row 4)
    (hb : InBox (shape P) box) (hw : TrueWeightLE P T) :
    InBox (shape (topHasse a P)) box ∧ TrueWeightLE (topHasse a P) T := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change (topHasse a P).totalDegree ≤ box.b
    apply Finset.sup_le
    intro m hm
    have hp := (MvPolynomial.le_totalDegree (source_support hm)).trans hb.1
    rw [total_add_top] at hp
    exact (Nat.le_add_right _ _).trans hp
  · change indexDegree (topHasse a P) ≤ box.j
    apply Finset.sup_le
    intro m hm
    have hp := (Finset.le_sup (f := fun u : Fin 4 →₀ ℕ => u.sum (fun i k => i.val * k))
      (source_support hm)).trans hb.2.1
    rw [sum_add_top Fin.val] at hp
    exact (Nat.le_add_right _ _).trans hp
  · change (topHasse a P).degreeOf 3 ≤ box.t
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have hp := (MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)).trans hb.2.2
    rw [apply_add_top] at hp
    exact (Nat.le_add_right _ _).trans hp
  · intro m hm
    have hp := hw _ (source_support hm)
    rw [sum_add_top (fun i => physicalDegree - i.val)] at hp
    rw [topHasse_coeff]
    have hc := Polynomial.natDegree_mul_le
      (p := (↑((m 3 + a).choose a) : Geom[X])) (q := P.coeff (m + Finsupp.single 3 a))
    rw [Polynomial.natDegree_natCast, zero_add] at hc
    exact (Nat.add_le_add_right hc _).trans ((Nat.add_le_add_left (Nat.le_add_right _ _) _).trans hp)
private theorem topHasse_one_not_dvd (f : Row 4) (hf : Irreducible f)
    (hpos : 0 < f.degreeOf 3) (hsmall : f.degreeOf 3 < K1.p) : ¬ f ∣ topHasse 1 f := by
  classical
  have hdeg : (topHasse 1 f).degreeOf 3 ≤ f.degreeOf 3 - 1 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    have h := MvPolynomial.le_degreeOf_of_mem_support 3 (source_support hm)
    rw [apply_add_top] at h
    omega
  have hnz : topHasse 1 f ≠ 0 := by
    have hsup : 0 < f.support.sup (fun m => m (3 : Fin 4)) := by
      rwa [← MvPolynomial.degreeOf_eq_sup]
    obtain ⟨u, hu, htop⟩ := (Finset.le_sup_iff hsup).mp (le_refl _)
    rw [← MvPolynomial.degreeOf_eq_sup] at htop
    have hupos : 0 < u 3 := hpos.trans_le htop
    have hult : u 3 < K1.p := (MvPolynomial.le_degreeOf_of_mem_support 3 hu).trans_lt hsmall
    let m := u.erase 3 + Finsupp.single 3 (u 3 - 1)
    have hsum : m + Finsupp.single 3 1 = u := by
      dsimp [m]
      rw [add_assoc, ← Finsupp.single_add, Nat.sub_add_cancel hupos, erase_top_add]
    have hm : m 3 + 1 = u 3 := by
      rw [← apply_add_top, hsum]
    have hc : (↑(u 3) : Geom[X]) ≠ 0 := by
      have : CharP Geom K1.p :=
        charP_of_injective_ringHom (RingHom.injective embed) K1.p
      intro hz
      have hz' : (↑(u 3) : Geom) = 0 := by
        simpa only [map_natCast, map_zero] using congrArg (Polynomial.evalRingHom (0 : Geom)) hz
      exact (not_le_of_gt hult)
        (Nat.le_of_dvd hupos ((CharP.cast_eq_zero_iff Geom K1.p _).mp hz'))
    have hcoeff : (topHasse 1 f).coeff m ≠ 0 := by
      rw [topHasse_coeff, hm, hsum, Nat.choose_one_right]
      exact mul_ne_zero hc (MvPolynomial.mem_support_iff.mp hu)
    intro hz
    exact hcoeff (by rw [hz]; rfl)
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro h
    exact hnz (by rw [hg, h, mul_zero])
  have h := MvPolynomial.degreeOf_mul_eq (n := (3 : Fin 4)) hf.ne_zero hg0
  rw [hg, h] at hdeg
  omega
theorem proof : P3_6_3.c2 := by
  intro f P Γ s d a hf hb hw hord _ hdiv hexact
  obtain ⟨hbox, hweight⟩ := topHasse_bounds primaryBox primaryCutoff a P hb hw
  have hp : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hf.1
  have hsmall : f.degreeOf 3 < K1.p :=
    (show f.degreeOf 3 ≤ 10 from hf.2.2.1.2.2).trans_lt (by decide)
  have hproper : ¬ f ∣ topHasse a P :=
    exact_hasse_not_dvd translateTop topHasse_zero f P a hp
      (topHasse_one_not_dvd f hf.1 hf.2.1 hsmall) hdiv hexact
  exact ⟨topHasse a P, hproper, hbox, hweight, fun γ hγ =>
    topHasse_order a d P (extend (s γ)) (hord γ hγ)⟩
end
end P3_6_3_2
end
section
namespace P3_6_3_3
noncomputable section
open Polynomial
open P3 (I K node)
open P3_6 (TrueWeightLE physicalDegree primaryCutoff)
open P3_6_3 (BankRow)
open K1_13 (Geom embed Row InBox shape indexDegree Contact atJet)
open K1_13_3 (Symbol symbolAt)
open private jetEval jetEval_apply dvd_smul_poly coefficientArray symbolLinear linearFactor
  linearFactor_ne linearFactor_degree divide_specialization support_linear_mul from ProximityPrize.SubmissionLower.PortLowBase
open scoped BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
private abbrev Exponent := Fin 4 →₀ ℕ
private def jetWeight (m : Exponent) : ℕ :=
  m.sum (fun i a => (physicalDegree - i.val) * a)
private theorem bankRow_iff {w : I → K} {T : ℕ} {P : Row 4} :
    BankRow w T P ↔
      (∀ m ∈ P.support, m.sum (fun _ a => a) ≤ 4012 ∧
        m.sum (fun i a => i.val * a) ≤ 1650 ∧ m 3 ≤ 550 ∧
        (P.coeff m).natDegree + jetWeight m ≤ T) ∧ Contact w P := by
  simp only [BankRow, InBox, shape, indexDegree, MvPolynomial.totalDegree,
    MvPolynomial.degreeOf_le_iff, Finset.sup_le_iff, TrueWeightLE]
  constructor
  · rintro ⟨⟨hb, hj, ht⟩, hT, hc⟩
    exact ⟨fun m hm => ⟨hb m hm, hj m hm, ht m hm, hT m hm⟩, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨fun m hm => (h m hm).1, fun m hm => (h m hm).2.1, fun m hm => (h m hm).2.2.1⟩,
      fun m hm => (h m hm).2.2.2, hc⟩
private def bank (w : I → K) (T : ℕ) : Submodule Geom (Row 4) where
  carrier := {P | BankRow w T P}
  zero_mem' := by
    apply bankRow_iff.mpr
    simp [Contact, atJet]
  add_mem' {P Q} hP hQ := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    obtain ⟨hQ, hq⟩ := bankRow_iff.mp hQ
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      have hor := Finset.mem_union.mp (MvPolynomial.support_add hm)
      have bounds :
          m.sum (fun _ a => a) ≤ 4012 ∧ m.sum (fun i a => i.val * a) ≤ 1650 ∧
            m 3 ≤ 550 ∧ jetWeight m ≤ T := by
        rcases hor with h | h
        · obtain ⟨hb, hj, ht, hw⟩ := hP m h
          exact ⟨hb, hj, ht, by omega⟩
        · obtain ⟨hb, hj, ht, hw⟩ := hQ m h
          exact ⟨hb, hj, ht, by omega⟩
      obtain ⟨hb, hj, ht, hw⟩ := bounds
      refine ⟨hb, hj, ht, ?_⟩
      have hsum : ((P + Q).coeff m).natDegree ≤
          max (P.coeff m).natDegree (Q.coeff m).natDegree := by
        change ((P.coeff m) + (Q.coeff m)).natDegree ≤ _
        exact natDegree_add_le _ _
      have hdegree (R : Row 4) (hR : m ∈ R.support → (R.coeff m).natDegree + jetWeight m ≤ T) :
          (R.coeff m).natDegree ≤ T - jetWeight m := by
        by_cases h : m ∈ R.support
        · have := hR h
          omega
        · have hz : R.coeff m = 0 := by
            by_contra hnz
            exact h (MvPolynomial.mem_support_iff.mpr hnz)
          rw [hz, natDegree_zero]
          exact Nat.zero_le _
      have hp' := hdegree P (fun h => (hP m h).2.2.2)
      have hq' := hdegree Q (fun h => (hQ m h).2.2.2)
      have := hsum.trans (max_le hp' hq')
      omega
    · intro i S hS
      rw [← jetEval_apply, map_add, jetEval_apply, jetEval_apply]
      exact dvd_add (hp i S hS) (hq i S hS)
  smul_mem' c P hP := by
    obtain ⟨hP, hp⟩ := bankRow_iff.mp hP
    apply bankRow_iff.mpr
    constructor
    · intro m hm
      obtain ⟨hb, hj, ht, hw⟩ := hP m (MvPolynomial.support_smul hm)
      refine ⟨hb, hj, ht, ?_⟩
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i S hS
      have h : jetEval S (c • P) = c • jetEval S P := (jetEval S).map_smul c P
      rw [jetEval_apply, jetEval_apply] at h
      rw [h]
      exact dvd_smul_poly _ _ c (hp i S hS)
private instance finiteBank (w : I → K) (T : ℕ) : Module.Finite Geom (bank w T) := by
  classical
  let f : bank w T →ₗ[Geom] (((Fin 4 → Fin 4013) × Fin (T + 1)) → Geom) :=
    (coefficientArray T).comp (bank w T).subtype
  have hzero (Q : bank w T) (hQ : f Q = 0) : Q = 0 := by
    obtain ⟨P, hP⟩ := Q
    change BankRow w T P at hP
    apply Subtype.ext
    change P = 0
    apply MvPolynomial.ext
    intro m
    change _ = 0
    by_contra hnz
    have hm := MvPolynomial.mem_support_iff.mpr hnz
    have hT : (P.coeff m).natDegree ≤ T := (Nat.le_add_right _ _).trans (hP.2.1 m hm)
    let u : Fin 4 → Fin 4013 := fun i => ⟨m i, Nat.lt_succ_of_le <|
      (MvPolynomial.le_degreeOf_of_mem_support i hm).trans <|
        (P.degreeOf_le_totalDegree i).trans hP.1.1⟩
    apply hnz
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < T + 1
    · have hval := congrFun hQ (u, ⟨k, hk⟩)
      change (P.coeff (Finsupp.equivFunOnFinite.symm (fun i => (u i).val))).coeff k = 0 at hval
      have heq : Finsupp.equivFunOnFinite.symm (fun i => (u i).val) = m :=
        Finsupp.equivFunOnFinite.symm_apply_apply m
      rwa [heq] at hval
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  apply Module.Finite.of_injective f
  intro P Q h
  apply sub_eq_zero.mp
  have hz := f.map_sub P Q
  rw [h, sub_self] at hz
  exact hzero (P - Q) hz
private def bankEval (w : I → K) (x : Geom) (T : ℕ) : bank w T →ₗ[Geom] Symbol :=
  (symbolLinear x).comp (bank w T).subtype
private theorem mul_cutoff_iff (w : I → K) (x : Geom) (hx : ∀ i : I, x ≠ embed (node i))
    (T : ℕ) (P : Row 4) :
    BankRow w (T + 1) (MvPolynomial.C (linearFactor x) * P) ↔ BankRow w T P := by
  rw [bankRow_iff, bankRow_iff, support_linear_mul]
  apply and_congr
  · refine forall_congr' fun m => forall_congr' fun hm => ?_
    rw [MvPolynomial.coeff_C_mul, natDegree_mul (linearFactor_ne x)
      (MvPolynomial.mem_support_iff.mp hm), linearFactor_degree]
    omega
  · simp only [Contact, atJet, map_mul, MvPolynomial.eval_C]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro S
    apply forall_congr'
    intro hS
    generalize (3000 : ℕ) = m
    have hc : IsCoprime (linearFactor (embed (node i))) (linearFactor x) :=
      isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (hx i).symm).isUnit
    have hd : IsCoprime (linearFactor (embed (node i)) ^ m) (linearFactor x) := hc.pow_left
    exact hd.dvd_mul_left_iff
private theorem zero_cutoff_kernel (w : I → K) (x : Geom) :
    LinearMap.ker (bankEval w x 0) = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro P hP
  change symbolAt x P.val = 0 at hP
  obtain ⟨Q, hQ⟩ := divide_specialization P.val x hP
  have hp : TrueWeightLE P.val 0 := P.property.2.1
  apply Subtype.ext
  change P.val = 0
  rw [← hQ]
  suffices Q = 0 by simp [this]
  apply MvPolynomial.ext
  intro m
  change _ = 0
  by_contra hnz
  have hm : m ∈ P.val.support := by
    rw [← hQ, support_linear_mul]
    exact MvPolynomial.mem_support_iff.mpr hnz
  have h := hp m hm
  rw [← hQ, MvPolynomial.coeff_C_mul, natDegree_mul (linearFactor_ne x) hnz,
    linearFactor_degree] at h
  omega
private theorem kernel_finrank (w : I → K) (x : Geom) (hx : ∀ i : I, x ≠ embed (node i))
    (T : ℕ) : Module.finrank Geom (LinearMap.ker (bankEval w x (T + 1))) =
      Module.finrank Geom (bank w T) := by
  let L : bank w T →ₗ[Geom] (LinearMap.ker (bankEval w x (T + 1))) :=
    LinearMap.codRestrict _ (LinearMap.codRestrict (bank w (T + 1))
      ((LinearMap.mulLeft Geom (MvPolynomial.C (linearFactor x))).comp (bank w T).subtype)
      (fun P => (mul_cutoff_iff w x hx T P.val).mpr P.property)) (fun P => by
        rw [LinearMap.mem_ker]
        change symbolAt x (MvPolynomial.C (linearFactor x) * P.val) = 0
        simp [symbolAt, linearFactor])
  have hL : Function.Bijective L := by
    have hnz : (MvPolynomial.C (linearFactor x) : Row 4) ≠ 0 := by
      simpa only [ne_eq, MvPolynomial.C_eq_zero] using linearFactor_ne x
    constructor
    · intro P Q h
      apply Subtype.ext
      have heq := congrArg (fun V : LinearMap.ker (bankEval w x (T + 1)) => V.val.val) h
      change MvPolynomial.C (linearFactor x) * P.val = MvPolynomial.C (linearFactor x) * Q.val at heq
      exact mul_left_cancel₀ hnz heq
    · intro P
      have h : symbolAt x P.val.val = 0 := LinearMap.mem_ker.mp P.property
      obtain ⟨Q, hQ⟩ := divide_specialization P.val.val x h
      have hmem : BankRow w (T + 1) (MvPolynomial.C (linearFactor x) * Q) := by
        rw [hQ]
        exact P.val.property
      refine ⟨⟨Q, (mul_cutoff_iff w x hx T Q).mp hmem⟩, Subtype.ext (Subtype.ext hQ)⟩
  exact (LinearEquiv.ofBijective L hL).finrank_eq.symm
theorem proof : P3_6_3.c3 := by
  classical
  intro w x hr hx
  let r (T : ℕ) := Module.finrank Geom (LinearMap.range (bankEval w x T))
  refine ⟨r, ?_, fun T _ => ?_⟩
  · have heq (T : ℕ) : Module.finrank Geom (bank w T) =
        ∑ V ∈ Finset.range (T + 1), r V := by
      induction T with
      | zero =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank w 0) (V₂ := Symbol) (bankEval w x 0)
        rw [zero_cutoff_kernel, finrank_bot, Nat.add_zero] at h
        simpa only [Nat.zero_add, Finset.sum_range_one] using h.symm
      | succ T ih =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := Geom) (V := bank w (T + 1)) (V₂ := Symbol) (bankEval w x (T + 1))
        rw [kernel_finrank w x hx, ih, Nat.add_comm] at h
        rw [Finset.sum_range_succ]
        exact h.symm
    obtain ⟨e, he, hmem⟩ := hr
    have hi : LinearIndependent Geom (fun i => (⟨e i, hmem i⟩ : bank w primaryCutoff)) :=
      LinearIndependent.of_comp (bank w primaryCutoff).subtype he
    rw [← heq]
    simpa only [Fintype.card_fin] using hi.fintype_card_le_finrank
  · let b := Module.finBasis Geom (LinearMap.range (bankEval w x T))
    choose e he using fun i : Fin (r T) => LinearMap.mem_range.mp (b i).property
    refine ⟨fun i => (e i).val, fun i => (e i).property, ?_⟩
    have h : LinearIndependent Geom (fun i => (b i).val) :=
      b.linearIndependent.map' (LinearMap.range (bankEval w x T)).subtype
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have heq : (fun i => symbolAt x (e i).val) = fun i => (b i).val := funext he
    rwa [heq]
end
end P3_6_3_3
end
section
namespace P3_6_8
open K1_13 (Shape)
open K1_13_8_2 (Threshold orderFor)
abbrev oneReserve : ℕ := 0x572a200a42ce14
abbrev twoReserve : ℕ := 0xf915c8e214a19b
abbrev twoOrder : ℕ := 72
def emptyThresholds : List Threshold :=
  [⟨107, 46, 56⟩, ⟨14, 41, 53⟩, ⟨61, 31, 52⟩, ⟨8, 13, 32⟩,
    ⟨9, 7, 9⟩, ⟨22, 4, 8⟩, ⟨3, 7, 4⟩, ⟨4, 10, 22⟩,
    ⟨10, 28, 48⟩]
def emptyOrder (a : Shape) : ℕ := orderFor a.b a.j emptyThresholds
def RetainedBox (a : Shape) : Prop :=
  a.b ≤ 20 ∧ a.j ≤ 6 ∧
    (4 ≤ a.j → a.b ≤ 17) ∧ (5 ≤ a.j → a.b ≤ 14) ∧ (6 ≤ a.j → a.b ≤ 7)
end P3_6_8
end
section
namespace P3_6_8
open K1_13 (Shape Fits InBox FatEligible remaining)
open K1_13_8 (Valid zeroShape fullCap zeroMass availableMass layerTerm layerCount)
open K1_13_8_2 (orderFor)
open P0_9_8 (oneStart twoStart oneOrder indexBudget symbol_count availableMass_anti_prefix
  orderFor_select orderFor_mono oneOrder_pos oneOrder_mono)
open P3_6 (factorCap)
open scoped BigOperators
def c1 : Prop :=
  zeroMass 21 3 < P3_6.layerNeed ∧ zeroMass 18 4 < P3_6.layerNeed ∧
    zeroMass 15 5 < P3_6.layerNeed ∧ zeroMass 8 6 < P3_6.layerNeed ∧
    zeroMass 3 7 < P3_6.layerNeed
def c2 : Prop :=
  ∀ a, Valid a → RetainedBox a →
    (a.t = 1 → P3_6.fatPrice a ≤ oneReserve) ∧
    (a.t = 2 → P3_6.fatPrice a ≤ twoReserve) ∧
    (a.t = 1 → a.j = 3 → a.b ≤ 6 → 2 * P3_6.fatPrice a ≤ twoReserve)
def c3 : Prop :=
  ∀ s ∈ emptyThresholds,
    availableMass zeroShape ⟨s.b, s.j, 0⟩ (s.l - 1) < P3_6.layerNeed
def c4 : Prop :=
  ∀ a, Valid a → InBox (zeroShape.plus a) fullCap →
    P3_6.physicalPrice a (emptyOrder a) ≤ indexBudget zeroShape factorCap a.j
def c5 : Prop :=
  ∀ j : ℕ, 4 ≤ j → j ≤ 45 →
    availableMass oneStart ⟨0, j, 0⟩ (oneOrder ⟨0, j, 0⟩ - 1) < P3_6.layerNeed
def c6 : Prop :=
  ∀ a, Valid a → InBox (oneStart.plus a) fullCap →
    P3_6.physicalPrice a (oneOrder a) ≤ indexBudget oneStart (factorCap - oneReserve) a.j
def c7 : Prop :=
  availableMass twoStart ⟨0, 3, 0⟩ (twoOrder - 1) < P3_6.layerNeed
def c8 : Prop :=
  ∀ a, Valid a → InBox (twoStart.plus a) fullCap →
    P3_6.physicalPrice a twoOrder ≤ indexBudget twoStart (factorCap - twoReserve) a.j
private def Bellman (r : Shape) (cap : ℕ) : Prop :=
  ∃ (B order : Shape → ℕ), B zeroShape ≤ cap ∧
    (∀ x, Valid x → InBox (r.plus x) fullCap →
      0 < order x ∧
        (order x = 1 ∨ availableMass r x (order x - 1) < P3_6.layerNeed)) ∧
    (∀ (y a : Shape), (y = zeroShape ∨ Valid y) → Valid a →
      InBox (r.plus (y.plus a)) fullCap →
      P3_6.physicalPrice a (order (y.plus a)) + B (y.plus a) ≤ B y)
private theorem physicalPrice_anti (a : Shape) {l u : ℕ} (hl : 0 < l) (h : l ≤ u) :
    P3_6.physicalPrice a u ≤ P3_6.physicalPrice a l := by
  unfold P3_6.physicalPrice
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (K1_13_8.ceilDiv_anti _ hl h) _) _
private theorem bellman_of_budget (r : Shape) (cap : ℕ) (order : Shape → ℕ)
    (hpos : ∀ x, 0 < order x)
    (hmono : ∀ {a x}, a.b ≤ x.b → a.j ≤ x.j → order a ≤ order x)
    (horders : ∀ x, Valid x → InBox (r.plus x) fullCap →
      order x = 1 ∨ availableMass r x (order x - 1) < P3_6.layerNeed)
    (hprice : ∀ a, Valid a → InBox (r.plus a) fullCap →
      P3_6.physicalPrice a (order a) ≤ indexBudget r cap a.j) :
    Bellman r cap := by
  let B := fun y : Shape => indexBudget r cap (48 - r.j - y.j)
  refine ⟨B, order, ?_, fun x hx hb => ⟨hpos x, horders x hx hb⟩, ?_⟩
  · change cap * (48 - r.j - 0) / (48 - r.j) ≤ cap
    rw [Nat.sub_zero]
    exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm])
  · intro y a _ ha hbox
    let x := y.plus a
    have hb : InBox (r.plus a) fullCap :=
      ⟨(Nat.add_le_add_left (Nat.le_add_left a.b y.b) _).trans hbox.1,
        (Nat.add_le_add_left (Nat.le_add_left a.j y.j) _).trans hbox.2.1,
        (Nat.add_le_add_left (Nat.le_add_left a.t y.t) _).trans hbox.2.2⟩
    have hl := hmono (a := a) (x := x) (Nat.le_add_left _ _) (Nat.le_add_left _ _)
    have hfee := (physicalPrice_anti a (hpos a) hl).trans (hprice a ha hb)
    have hidx : r.j + (y.j + a.j) ≤ 48 := hbox.2.1
    have hbalance : a.j + (48 - r.j - x.j) = 48 - r.j - y.j := by
      change a.j + (48 - r.j - (y.j + a.j)) = 48 - r.j - y.j
      omega
    apply (Nat.add_le_add_right hfee (B x)).trans
    have hdiv : cap * a.j / (48 - r.j) + cap * (48 - r.j - x.j) / (48 - r.j) ≤
        (cap * a.j + cap * (48 - r.j - x.j)) / (48 - r.j) :=
      Nat.div_add_div_le_add_div
    rw [← Nat.mul_add, hbalance] at hdiv
    exact hdiv
private theorem empty_bellman (horder : c3) (hprice : c4) : Bellman zeroShape factorCap := by
  apply bellman_of_budget zeroShape factorCap emptyOrder
    (fun x => (orderFor_select x.b x.j emptyThresholds).1)
    (fun hb hj => orderFor_mono hb hj emptyThresholds) _ hprice
  intro x _ _
  rcases (orderFor_select x.b x.j emptyThresholds).2 with he | ⟨s, hs, hb, hj, he⟩
  · exact Or.inl he
  · have hj0 : 0 < s.j := by
      simp [emptyThresholds] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    right
    change emptyOrder x = s.l at he
    rw [he]
    exact (availableMass_anti_prefix (y := ⟨s.b, s.j, 0⟩)
      (Or.inl rfl) (by simpa [zeroShape] using hj0) hb hj).trans_lt (horder s hs)
private theorem one_bellman (horder : c5) (hprice : c6) :
    Bellman oneStart (factorCap - oneReserve) := by
  apply bellman_of_budget oneStart (factorCap - oneReserve) oneOrder oneOrder_pos
    (fun _ hj => oneOrder_mono hj) _ hprice
  intro x _ hx
  have hj : 3 + x.j ≤ 48 := hx.2.1
  by_cases hsmall : x.j ≤ 3
  · exact Or.inl (ite_eq_left hsmall)
  · have h := horder x.j (by omega) (by omega)
    exact Or.inr <| (availableMass_anti_prefix (x := x) (y := ⟨0, x.j, 0⟩)
      (Or.inr (by decide)) (by change 0 < 3 + x.j; omega)
      (Nat.zero_le x.b) le_rfl).trans_lt h
private theorem two_bellman (horder : c7) (hprice : c8) :
    Bellman twoStart (factorCap - twoReserve) := by
  apply bellman_of_budget twoStart (factorCap - twoReserve) (fun _ => twoOrder)
    (fun _ => by decide) (fun _ _ => le_rfl) _ hprice
  intro x hx _
  have hj : 3 ≤ x.j := (Nat.mul_le_mul_left 3 hx.1).trans hx.2.1
  exact Or.inr <| (availableMass_anti_prefix (y := ⟨0, 3, 0⟩)
    (Or.inr (by decide)) (by decide) (Nat.zero_le _) hj).trans_lt horder
private def shapeSum {ι : Type*} (a : ι → Shape) (s : Finset ι) : Shape :=
  ⟨∑ i ∈ s, (a i).b, ∑ i ∈ s, (a i).j, ∑ i ∈ s, (a i).t⟩
private theorem shapeSum_empty {ι : Type*} (a : ι → Shape) :
    shapeSum a ∅ = zeroShape := by simp [shapeSum, zeroShape]
private theorem shapeSum_insert {ι : Type*} [DecidableEq ι] (a : ι → Shape)
    {i : ι} {s : Finset ι} (hi : i ∉ s) :
    shapeSum a (insert i s) = (shapeSum a s).plus (a i) := by
  simp [shapeSum, Shape.plus, Finset.sum_insert hi, Nat.add_comm]
private theorem shapeSum_union {ι : Type*} [DecidableEq ι] (a : ι → Shape)
    {s t : Finset ι} (h : Disjoint s t) :
    shapeSum a (s ∪ t) = (shapeSum a s).plus (shapeSum a t) := by
  simp [shapeSum, Shape.plus, Finset.sum_union h]
private theorem shapeSum_mono {ι : Type*} (a : ι → Shape) {s t : Finset ι}
    (h : s ⊆ t) : InBox (shapeSum a s) (shapeSum a t) :=
  ⟨Finset.sum_le_sum_of_subset h, Finset.sum_le_sum_of_subset h, Finset.sum_le_sum_of_subset h⟩
private theorem inBox_trans {a b c : Shape} (hab : InBox a b) (hbc : InBox b c) :
    InBox a c :=
  ⟨hab.1.trans hbc.1, hab.2.1.trans hbc.2.1, hab.2.2.trans hbc.2.2⟩
private theorem inBox_shapeSum {ι : Type*} (a : ι → Shape) {i : ι} {s : Finset ι}
    (hi : i ∈ s) : InBox (a i) (shapeSum a s) :=
  ⟨Finset.single_le_sum (f := fun i => (a i).b) (fun _ _ => Nat.zero_le _) hi,
    Finset.single_le_sum (f := fun i => (a i).j) (fun _ _ => Nat.zero_le _) hi,
    Finset.single_le_sum (f := fun i => (a i).t) (fun _ _ => Nat.zero_le _) hi⟩
private theorem shapeSum_valid_or_empty {ι : Type*} {a : ι → Shape}
    (ha : ∀ i, Valid (a i)) (s : Finset ι) :
    s = ∅ ∨ Valid (shapeSum a s) := by
  by_cases he : s.Nonempty
  · obtain ⟨i, hi⟩ := he
    refine Or.inr ⟨(ha i).1.trans (inBox_shapeSum a hi).2.2, ?_, ?_⟩
    · change 3 * (∑ i ∈ s, (a i).t) ≤ ∑ i ∈ s, (a i).j
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (ha i).2.1
    · change (∑ i ∈ s, (a i).j) ≤ 3 * ∑ i ∈ s, (a i).b
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (ha i).2.2
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp he)
private theorem spend_le {ι : Type*} [DecidableEq ι] [Fintype ι] {l : ι → ℕ}
    (f : ι → ℕ) {z s : Finset ι} {q d L : ℕ}
    (hz : ∀ i ∈ z, l i = 0) (hs : ∀ i ∈ s, l i ≤ L) (hdisj : Disjoint z s)
    (hq : q ≤ ∑ i ∈ z, f i) :
    d * q + (d - L) * (∑ i ∈ s, f i) ≤ ∑ i, (d - l i) * f i := by
  calc
    _ ≤ d * (∑ i ∈ z, f i) + (d - L) * (∑ i ∈ s, f i) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hq) _
    _ = (∑ i ∈ z, d * f i) + ∑ i ∈ s, (d - L) * f i := by
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ (∑ i ∈ z, (d - l i) * f i) + ∑ i ∈ s, (d - l i) * f i := by
      apply Nat.add_le_add
      · exact Finset.sum_le_sum fun i hi => by rw [hz i hi, Nat.sub_zero]
      · exact Finset.sum_le_sum fun i hi =>
          Nat.mul_le_mul_right _ (Nat.sub_le_sub_left (hs i hi) _)
    _ = ∑ i ∈ z ∪ s, (d - l i) * f i := (Finset.sum_union hdisj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
private theorem mass_le {n : ℕ} {a : Fin n → Shape} {l : Fin n → ℕ}
    (hlayers : P3_6.LayerBudget a l) {z s : Finset (Fin n)} {q : Shape} {L : ℕ}
    (hz : ∀ i ∈ z, l i = 0) (hs : ∀ i ∈ s, l i ≤ L)
    (hdisj : Disjoint z s) (hq : InBox q (shapeSum a z)) :
    P3_6.layerNeed ≤ ∑ k ∈ Finset.range layerCount, layerTerm q (shapeSum a s) L k := by
  have hcount : 1 + P3_6.primaryCutoff / P3_6.layerWidth ≤ layerCount := by decide
  refine hlayers.trans ((Finset.sum_le_sum fun k _ => K1_13_8.remaining_anti ?_ ?_).trans
    (Finset.sum_le_sum_of_subset (Finset.range_mono hcount)))
  · exact spend_le (fun i => (a i).b) hz hs hdisj hq.1
  · exact spend_le (fun i => (a i).j) hz hs hdisj hq.2.1
private theorem retained_bound (hexcl : c1) {r : Shape} (hr : Valid r)
    (hmass : P3_6.layerNeed ≤ ∑ k ∈ Finset.range layerCount,
      remaining ((k + 1) * r.b) ((k + 1) * r.j)) : RetainedBox r := by
  have reject {b j : ℕ} (hb : b ≤ r.b) (hj : j ≤ r.j) (hjpos : 0 < j)
      (hsmall : zeroMass b j < P3_6.layerNeed) : False := by
    have hle : P3_6.layerNeed ≤ zeroMass b j := hmass.trans <|
      (Finset.sum_le_sum fun k _ => K1_13_8.remaining_anti
        (Nat.mul_le_mul_left _ hb) (Nat.mul_le_mul_left _ hj)).trans
        (K1_13_8.zeroMass_upper symbol_count hjpos)
    exact (not_lt_of_ge hle) hsmall
  obtain ⟨ht, hjt, hjb⟩ := hr
  obtain ⟨h21, h18, h15, h8, hj7⟩ := hexcl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_contra! h; exact reject (by omega) (by omega) (by decide) h21
  · by_contra! h; exact reject (by omega) (by omega) (by decide) hj7
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) h18
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) h15
  · intro hj; by_contra! h; exact reject (by omega) hj (by decide) h8
private theorem retainedBox_down {a r : Shape} (h : InBox a r) (hr : RetainedBox r) :
    RetainedBox a := by
  rcases h with ⟨hb, hj, _⟩
  rcases hr with ⟨hrb, hrj, h4, h5, h6⟩
  exact ⟨hb.trans hrb, hj.trans hrj, fun k => hb.trans (h4 (k.trans hj)),
    fun k => hb.trans (h5 (k.trans hj)), fun k => hb.trans (h6 (k.trans hj))⟩
private theorem retained_cost {ι : Type*} [DecidableEq ι] {a : ι → Shape} {cost : ι → ℕ}
    {z : Finset ι} (hretained : c2) (ha : ∀ i, Valid (a i)) (hbox : RetainedBox (shapeSum a z))
    (ht : (shapeSum a z).t = 1 ∨ (shapeSum a z).t = 2)
    (hfat : ∀ i, FatEligible (a i) → cost i ≤ P3_6.fatPrice (a i)) :
    (∑ i ∈ z, cost i) ≤ if (shapeSum a z).t = 1 then oneReserve else twoReserve := by
  let r := shapeSum a z
  change r.t = 1 ∨ r.t = 2 at ht
  change RetainedBox r at hbox
  change (∑ i ∈ z, cost i) ≤ if r.t = 1 then oneReserve else twoReserve
  have admitted {i} (hi : i ∈ z) := retainedBox_down (inBox_shapeSum a hi) hbox
  have paid {i} (hi : i ∈ z) : cost i ≤ P3_6.fatPrice (a i) :=
    hfat i ⟨(admitted hi).1.trans (by decide), (admitted hi).2.1.trans (by decide)⟩
  rcases ht with ht | ht
  · rw [ite_eq_left ht]
    calc
      _ ≤ ∑ i ∈ z, oneReserve * (a i).t := by
        apply Finset.sum_le_sum
        intro i hi
        have hti : (a i).t ≤ r.t := (inBox_shapeSum a hi).2.2
        have hai : (a i).t = 1 := by have := (ha i).1; omega
        simpa only [hai, Nat.mul_one] using (paid hi).trans ((hretained _ (ha i) (admitted hi)).1 hai)
      _ = oneReserve := by
        rw [← Finset.mul_sum]
        change oneReserve * r.t = oneReserve
        rw [ht, Nat.mul_one]
  · rw [ite_eq_right (by omega : r.t ≠ 1)]
    have htwo : 2 * (∑ i ∈ z, cost i) ≤ twoReserve * r.t := by
      change 2 * (∑ i ∈ z, cost i) ≤ twoReserve * ∑ i ∈ z, (a i).t
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hti : (a i).t ≤ r.t := (inBox_shapeSum a hi).2.2
      obtain ⟨_, hsingle, hpair⟩ := hretained _ (ha i) (admitted hi)
      by_cases hai : (a i).t = 2
      · rw [hai, Nat.mul_comm twoReserve 2]
        exact Nat.mul_le_mul_left _ ((paid hi).trans (hsingle hai))
      · have htone : (a i).t = 1 := by have := (ha i).1; omega
        let s := z.erase i
        have hsadd : (shapeSum a s).plus (a i) = r :=
          (shapeSum_insert a (Finset.notMem_erase i z)).symm.trans
            (congrArg (shapeSum a) (Finset.insert_erase hi))
        have hsTop : (shapeSum a s).t + (a i).t = r.t := congrArg Shape.t hsadd
        have hsvalid : Valid (shapeSum a s) := by
          rcases shapeSum_valid_or_empty ha s with he | hv
          · rw [he, shapeSum_empty] at hsTop
            change 0 + (a i).t = r.t at hsTop
            omega
          · exact hv
        have hsIndex : (shapeSum a s).j + (a i).j = r.j := congrArg Shape.j hsadd
        have hsDegree : (shapeSum a s).b + (a i).b = r.b := congrArg Shape.b hsadd
        have hiIndexBudget := (ha i).2.1
        have hsIndexBudget := hsvalid.2.1
        have hrIndexBudget : r.j ≤ 6 := hbox.2.1
        have hjr : r.j = 6 := by omega
        have hbr : r.b ≤ 7 := hbox.2.2.2.2 (by omega)
        have hj : (a i).j = 3 := by omega
        have hb : (a i).b ≤ 6 := by
          have := hsvalid.2.2
          omega
        rw [htone, Nat.mul_one]
        exact (Nat.mul_le_mul_left _ (paid hi)).trans (hpair htone hj hb)
    rw [ht, Nat.mul_comm twoReserve 2] at htwo
    omega
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5)
    (h6 : c6) (h7 : c7) (h8 : c8) : P3_6.c8 := by
  intro n a l cost hfits hlayers hphys hfat
  let z := Finset.univ.filter (fun i => l i = 0)
  let pos := Finset.univ.filter (fun i => ¬ l i = 0)
  let r := shapeSum a z
  have ha (i : Fin n) : Valid (a i) := hfits.1 i
  have hz (i : Fin n) (hi : i ∈ z) : l i = 0 := (Finset.mem_filter.mp hi).2
  have hpos (i : Fin n) (hi : i ∈ pos) : 0 < l i :=
    Nat.pos_of_ne_zero (Finset.mem_filter.mp hi).2
  have hdisj {s : Finset (Fin n)} (hs : s ⊆ pos) : Disjoint z s :=
    Finset.disjoint_left.mpr fun i hi his => (Nat.ne_of_gt (hpos i (hs his))) (hz i hi)
  have account : ∃ (q : Shape) (cap : ℕ), InBox q r ∧ (q = zeroShape ∨ 0 < q.j) ∧
      Bellman q cap ∧ (∑ i ∈ z, cost i) + cap ≤ factorCap := by
    rcases shapeSum_valid_or_empty ha z with hempty | hr
    · have hr0 : r = zeroShape := by simp [r, hempty, shapeSum_empty]
      refine ⟨zeroShape, factorCap, ?_, Or.inl rfl, empty_bellman h3 h4, ?_⟩
      · rw [hr0]
        exact ⟨le_rfl, le_rfl, le_rfl⟩
      · simp [hempty]
    · have hmass := mass_le hlayers (s := ∅) (q := r) (L := 0) hz (by simp) (by simp)
        (show InBox r r from ⟨le_rfl, le_rfl, le_rfl⟩)
      have hret : RetainedBox r := retained_bound h1 hr
        (by simpa only [layerTerm, shapeSum_empty, zeroShape, Nat.mul_zero, Nat.add_zero]
          using hmass)
      have htr : 1 ≤ r.t := hr.1
      have hjr : 3 * r.t ≤ r.j := hr.2.1
      have hbr : r.j ≤ 3 * r.b := hr.2.2
      have hrj : r.j ≤ 6 := hret.2.1
      have ht : r.t = 1 ∨ r.t = 2 := by omega
      have hcost := retained_cost h2 ha hret ht hfat
      rcases ht with ht | ht
      · refine ⟨oneStart, factorCap - oneReserve, ?_, Or.inr (by decide), one_bellman h5 h6, ?_⟩
        · change 1 ≤ r.b ∧ 3 ≤ r.j ∧ 1 ≤ r.t
          omega
        · rw [ite_eq_left ht] at hcost
          exact (Nat.add_le_add_right hcost _).trans (by decide)
      · refine ⟨twoStart, factorCap - twoReserve, ?_, Or.inr (by decide), two_bellman h7 h8, ?_⟩
        · change 2 ≤ r.b ∧ 6 ≤ r.j ∧ 2 ≤ r.t
          omega
        · rw [ite_eq_right (by omega : r.t ≠ 1)] at hcost
          exact (Nat.add_le_add_right hcost _).trans (by decide)
  obtain ⟨q, cap, hqr, hq, ⟨B, order, hB0, horder, hB⟩, haccount⟩ := account
  have hall : InBox (shapeSum a Finset.univ) fullCap := hfits.2
  have hcap {s : Finset (Fin n)} (hs : s ⊆ pos) : InBox (q.plus (shapeSum a s)) fullCap := by
    have hb := shapeSum_mono a (Finset.subset_univ (z ∪ s))
    rw [shapeSum_union a (hdisj hs)] at hb
    have hle : InBox (q.plus (shapeSum a s)) (r.plus (shapeSum a s)) :=
      ⟨Nat.add_le_add_right hqr.1 _, Nat.add_le_add_right hqr.2.1 _,
        Nat.add_le_add_right hqr.2.2 _⟩
    exact inBox_trans hle (inBox_trans hb hall)
  have positive_bound (s : Finset (Fin n)) : s ⊆ pos →
      (∑ i ∈ s, cost i) + B (shapeSum a s) ≤ B zeroShape := by
    refine Finset.strongInductionOn s fun s ih hs => ?_
    by_cases he : s.Nonempty
    · obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image s l he
      let t := s.erase i
      have hti : i ∉ t := Finset.notMem_erase i s
      have hin : insert i t = s := Finset.insert_erase hi
      have hts : t ⊆ s := Finset.erase_subset i s
      have hprev := ih t (Finset.erase_ssubset hi) (hts.trans hs)
      have hvalid : shapeSum a t = zeroShape ∨ Valid (shapeSum a t) := by
        rcases shapeSum_valid_or_empty ha t with ht | ht
        · exact Or.inl (ht ▸ shapeSum_empty a)
        · exact Or.inr ht
      have hsvalid : Valid (shapeSum a s) := by
        rcases shapeSum_valid_or_empty ha s with hempty | hv
        · exact (he.ne_empty hempty).elim
        · exact hv
      have hL : 0 < l i := hpos i (hs hi)
      have hj : 0 < q.j + (shapeSum a s).j := by
        obtain ⟨ht, hidx, _⟩ := hsvalid
        omega
      have hmass : P3_6.layerNeed ≤ availableMass q (shapeSum a s) (l i) :=
        (mass_le hlayers hz hmax (hdisj hs) hqr).trans (K1_13_8.layerSum_le_available symbol_count hq hj)
      have hc := hcap hs
      obtain ⟨horderPos, horderTest⟩ := horder _ hsvalid hc
      have hord : order (shapeSum a s) ≤ l i := by
        rcases horderTest with heq | htest
        · omega
        · by_contra! h
          have hmono : availableMass q (shapeSum a s) (l i) ≤
              availableMass q (shapeSum a s) (order (shapeSum a s) - 1) :=
            K1_13_8.availableMass_mono symbol_count hq hj (by omega)
          exact (not_lt_of_ge (hmass.trans hmono)) htest
      have hstep : P3_6.physicalPrice (a i) (l i) + B (shapeSum a s) ≤ B (shapeSum a t) := by
        have hshape : shapeSum a s = (shapeSum a t).plus (a i) :=
          hin ▸ shapeSum_insert a hti
        refine (Nat.add_le_add_right (physicalPrice_anti _ horderPos hord) _).trans ?_
        rw [hshape] at hc ⊢
        exact hB _ _ hvalid (ha i) hc
      have hfee := hphys i hL
      rw [← hin, Finset.sum_insert hti, hin]
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp he, shapeSum_empty]
  have hpaid := positive_bound pos (Finset.Subset.rfl)
  have hpartition : (∑ i ∈ z, cost i) + (∑ i ∈ pos, cost i) = ∑ i, cost i :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  change (∑ i, cost i) ≤ factorCap
  omega
end P3_6_8
end
section
namespace P3_6_8_1
open K1_13_8 (fastRemaining zeroMass)
open scoped BigOperators
private def sumBelow (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumBelow f n + f n
private theorem sumBelow_eq (f : ℕ → ℕ) (n : ℕ) :
    sumBelow f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => rw [sumBelow, Finset.sum_range_succ, ih]
private theorem sumBelow_add (f : ℕ → ℕ) (m n : ℕ) :
    sumBelow f (m + n) = sumBelow f m + sumBelow (fun k => f (m + k)) n := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih =>
    change sumBelow f (m + n) + f (m + n) =
      sumBelow f m + (sumBelow (fun k => f (m + k)) n + f (m + n))
    rw [ih, Nat.add_assoc]
private def term (b j k : ℕ) : ℕ :=
  fastRemaining ((k + 1) * b) ((k + 1) * j)
private theorem mass_eq {b j m : ℕ} (hm : m ≤ 1650 / j)
    (hb : 4012 < (m + 1) * b ∨ m = 1650 / j) :
    zeroMass b j = sumBelow (term b j) m := by
  unfold zeroMass
  rw [sumBelow_eq]
  rcases hb with hb | h
  · apply K1_13_8.sum_range_truncate _ hm
    intro k hk
    have h := hb.trans_le (Nat.mul_le_mul_right b (Nat.succ_le_succ hk))
    simp [term, fastRemaining, Nat.not_le_of_gt h]
  · rw [h] <;> rfl
private theorem extend {f : ℕ → ℕ} {m n N x y total : ℕ}
    (hleft : sumBelow f m = x)
    (hright : sumBelow (fun k => f (m + k)) n = y)
    (hlen : m + n = N) (hvalue : x + y = total) :
    sumBelow f N = total := by
  rw [← hlen, sumBelow_add, hleft, hright, hvalue]
local notation "row!" h "," len "," nxt "," v "," z =>
  extend (n := len) (N := nxt) (y := v) (total := z) h rfl rfl rfl
private theorem exclude3 : zeroMass 21 3 < P3_6.layerNeed := by
  rw [mass_eq (b := 21) (j := 3) (m := 191) (by decide) (Or.inl (by decide))]
  have r0 : sumBelow (term 21 3) 0 = 0 := rfl
  have r1 := row! r0,12,12,0x4240a7b23ab, 0x4240a7b23ab
  have r2 := row! r1,12,24,0x394ee7b654b, 0x7b8f8f688f6
  have r3 := row! r2,12,36,0x312b2543543,0xacbab4abe39
  have r4 := row! r3,12,48,0x29c9a1fea93,0xd68456aa8cc
  have r5 := row! r4,12,60,0x231ef361b3b, 0xf9a34a0c407
  have r6 := row! r5,12,72,0x1d2002b9c3b, 0x116c34cc6042
  have r7 := row! r6,12,84,0x17c20d28193,0x12e8559ee1d5
  have r8 := row! r7,12,96,0x12faa3a1e43,0x1417ffd90018
  have r9 := row! r8,12,108,0xebfaaf044b, 0x1503fa880463
  have r10 := row! r9,12,120,0xb075bb04ab, 0x15b47043090e
  have r11 := row! r10,12,132,0x7c8425336f, 0x1630f4683c7d
  have r12 := row! r11,12,144,0x4f9ee0d079,0x168093490cf6
  have r13 := row! r12,12,156,0x2a1d1f2461,0x16aab0683157
  have r14 := row! r13,12,168,0xedb076feb, 0x16b98b6fa142
  have r15 := row! r14,12,180,0x233086028,0x16bbbe78016a
  have r16 := row! r15,11,191,0xd3d8050,0x16bbcbb581ba
  rw [r16]
  decide
private theorem exclude4 : zeroMass 18 4 < P3_6.layerNeed := by
  rw [mass_eq (b := 18) (j := 4) (m := 222) (by decide) (Or.inl (by decide))]
  have r0 : sumBelow (term 18 4) 0 = 0 := rfl
  have r1 := row! r0,12,12,0x41f1b7b52c4,0x41f1b7b52c4
  have r2 := row! r1,12,24,0x389290559a4,0x7a84480ac68
  have r3 := row! r2,12,36,0x3030c559d84,0xaab50d649ec
  have r4 := row! r3,12,48,0x28ba70fbe64,0xd36f7e60850
  have r5 := row! r4,12,60,0x221e5125c44,0xf58dcf86494
  have r6 := row! r5,12,72,0x1c4bc771724,0x111d996f7bb8
  have r7 := row! r6,12,84,0x1732d928f04,0x1290c7020abc
  have r8 := row! r7,12,96,0x12c42f463e4,0x13bd09f66ea0
  have r9 := row! r8,12,108,0xef116735c4,0x14ac1b5da464
  have r10 := row! r9,12,120,0xbab7f0a4a4,0x1566d34e4908
  have r11 := row! r10,12,132,0x8e5fd15084,0x15f5331f998c
  have r12 := row! r11,12,144,0x693c84d964,0x165e6fa472f0
  have r13 := row! r12,12,156,0x4a8bc1df44,0x16a8fb665234
  have r14 := row! r13,12,168,0x31957a0224,0x16da90e05458
  have r15 := row! r14,12,180,0x1dae12c8d0,0x16f83ef31d28
  have r16 := row! r15,12,192,0xe72af99a0,0x1706b1a2b6c8
  have r17 := row! r16,12,204,0x4656f6302,0x170b171219ca
  have r18 := row! r17,12,216,0x70e4e5ee, 0x170b87f6ffb8
  have r19 := row! r18,6,222,10163916,0x170b88921684
  rw [r19]
  decide
private theorem exclude5 : zeroMass 15 5 < P3_6.layerNeed := by
  rw [mass_eq (b := 15) (j := 5) (m := 267) (by decide) (Or.inl (by decide))]
  have r0 : sumBelow (term 15 5) 0 = 0 := rfl
  have r1 := row! r0,12,12,0x41a1290dc6f, 0x41a1290dc6f
  have r2 := row! r1,12,24,0x37cbcd64947,0x796cf6725b6
  have r3 := row! r2,12,36,0x2f1b31cbc0f, 0xa888283e1c5
  have r4 := row! r3,12,48,0x2777cf5a107,0xcffff7982cc
  have r5 := row! r4,12,60,0x20cb1a7636f, 0xf0cb120e63b
  have r6 := row! r5,12,72,0x1aff82d6d87,0x10bca94e53c2
  have r7 := row! r6,12,84,0x1600738288f, 0x121cb0867c51
  have r8 := row! r7,12,96,0x11ba52cfcc7,0x133855b37918
  have r9 := row! r8,12,108,0xe1a826516f, 0x1419fdd9ca87
  have r10 := row! r9,12,120,0xb0f5f38cc7,0x14caf3cd574e
  have r11 := row! r10,12,132,0x888419140f, 0x155377e66b5d
  have r12 := row! r11,12,144,0x6757d04b87,0x15bacfb6b6e4
  have r13 := row! r12,12,156,0x4c8607966f, 0x160755be4d53
  have r14 := row! r13,12,168,0x3733625707,0x163e8920a45a
  have r15 := row! r14,12,180,0x269438ee8f, 0x16651d5992e9
  have r16 := row! r15,12,192,0x19ec98bd47,0x167f09f25030
  have r17 := row! r16,12,204,0x109044226f, 0x168f9a36729f
  have r18 := row! r17,12,216,0x9e2b27c47,0x16997ce8eee6
  have r19 := row! r18,12,228,0x55710280f, 0x169ed3f916f5
  have r20 := row! r19,12,240,0x2703f8215,0x16a14438990a
  have r21 := row! r20,12,252,0xc3c2a559,0x16a207fb3e63
  have r22 := row! r21,12,264,0x127d6185,0x16a21a789fe8
  have r23 := row! r22,3,267,116550,0x16a21a7a672e
  rw [r23]
  decide
private theorem exclude6 : zeroMass 8 6 < P3_6.layerNeed := by
  rw [mass_eq (b := 8) (j := 6) (m := 275) (by decide) (Or.inr rfl)]
  have r0 : sumBelow (term 8 6) 0 = 0 := rfl
  have r1 := row! r0,12,12,0x41d431ea47d, 0x41d431ea47d
  have r2 := row! r1,12,24,0x384a33ebf39,0x7a1e65d63b6
  have r3 := row! r2,12,36,0x2fccf1b3315,0xa9eb57896cb
  have r4 := row! r3,12,48,0x2848b90f311,0xd23410989dc
  have r5 := row! r4,12,60,0x21aa8b3622d, 0xf3de9bcec09
  have r6 := row! r5,12,72,0x1be01cc5369,0x10fbeb893f72
  have r7 := row! r6,12,84,0x16d7d5c09c5,0x126968e54937
  have r8 := row! r7,12,96,0x1280d193841,0x139175fe8178
  have r9 := row! r8,12,108,0xecadf101dd, 0x147e23ef8355
  have r10 := row! r9,12,120,0xba6806f999,0x15388bf67cee
  have r11 := row! r10,12,132,0x904eb52275,0x15c8daab9f63
  have r12 := row! r11,12,144,0x6d808bef71,0x16365b378ed4
  have r13 := row! r12,12,156,0x512752438d, 0x16878289d261
  have r14 := row! r13,12,168,0x3a780571c9,0x16c1fa8f442a
  have r15 := row! r14,12,180,0x28b2d93d25,0x16eaad68814f
  have r16 := row! r15,12,192,0x1b2337d8a1,0x1705d0a059f0
  have r17 := row! r16,12,204,0x111fc1e73d, 0x1716f062412d
  have r18 := row! r17,12,216,0xa0a4e7bf9,0x1720fab0bd26
  have r19 := row! r18,12,228,0x54feb19d5,0x17264a9bd6fb
  have r20 := row! r19,12,240,0x268dbb3d1,0x1728b3778acc
  have r21 := row! r20,12,252,0xd89aaced, 0x17298c1237b9
  have r22 := row! r21,12,264,0x2dd8d829,0x1729b9eb0fe2
  have r23 := row! r22,11,275,41777285,0x1729bc688867
  rw [r23]
  decide
private theorem exclude7 : zeroMass 3 7 < P3_6.layerNeed := by
  rw [mass_eq (b := 3) (j := 7) (m := 235) (by decide) (Or.inr rfl)]
  have r0 : sumBelow (term 3 7) 0 = 0 := rfl
  have r1 := row! r0,12,12,0x41c00f6df00,0x41c00f6df00
  have r2 := row! r1,12,24,0x3805af47a6c, 0x79c5beb596c
  have r3 := row! r2,12,36,0x2f4ce582c30,0xa912a43859c
  have r4 := row! r3,12,48,0x2787e05314c, 0xd09a848b6e8
  have r5 := row! r4,12,60,0x20a8c29e5c0,0xf1434729ca8
  have r6 := row! r5,12,72,0x1aa1a3fc48c, 0x10be4eb26134
  have r7 := row! r6,12,84,0x156490b67b0,0x121497bdc8e4
  have r8 := row! r7,12,96,0x10e389c882c, 0x1322d05a5110
  have r9 := row! r8,12,108,0xd1084dfe00,0x13f3d8a84f10
  have r10 := row! r9,12,120,0x9dd6c5c02c, 0x1491af6e0f3c
  have r11 := row! r10,12,132,0x73c1f4e4b0,0x15057162f3ec
  have r12 := row! r11,12,144,0x51e717a08c, 0x1557587a9478
  have r13 := row! r12,12,156,0x3762b547c0,0x158ebb2fdc38
  have r14 := row! r13,12,168,0x2350a04d4c, 0x15b20bd02984
  have r15 := row! r14,12,180,0x14cbf64330,0x15c6d7c66cb4
  have r16 := row! r15,12,192,0xaef1fda6c, 0x15d1c6e64720
  have r17 := row! r16,12,204,0x4d3d0e300,0x15d69ab72a20
  have r18 := row! r17,12,216,0x193084bec, 0x15d82dbf760c
  have r19 := row! r18,12,228,0x45102330,0x15d872cf993c
  have r20 := row! r19,7,235,27570140,0x15d874744918
  rw [r20]
  decide
theorem proof : P3_6_8.c1 :=
  ⟨exclude3, exclude4, exclude5, exclude6, exclude7⟩
end P3_6_8_1
end
section
namespace P3_6_8_2
open K1_13 (Shape chart ceilDiv mixed32)
open K1_13_8 (Valid)
open K1_13_8_4 (TotalLE IndexFits mixed_mono_total)
open P3_6 (fatPrice linearChart taylorLength physicalDegree incidenceGap
  resultantBox commonBox fatOrder divisorOrder isolatedOrder)
open P3_6_8 (RetainedBox oneReserve twoReserve)
private def fatChart (x : Shape) : Shape :=
  if x.t = 1 then linearChart x.chamber else chart (taylorLength + 4) x.chamber
private abbrev divisorBox : Shape :=
  ⟨commonBox.b + resultantBox.b / divisorOrder, commonBox.j + resultantBox.j / divisorOrder, 0⟩
private theorem shape_eq {x y : Shape}
    (hb : x.b = y.b) (hj : x.j = y.j) (ht : x.t = y.t) : x = y := by
  cases x
  cases y
  simp_all
local notation "shape!" => shape_eq (by decide) (by decide) (by decide)
private theorem divisorBox_eq : divisorBox = ⟨22994,7683,0⟩ := shape!
private def divisorCut (h : Shape) : Shape :=
  ⟨max (max h.b divisorBox.b) (max h.j (divisorBox.j + 1)),
    max h.j (divisorBox.j + 1), max 1 h.t⟩
private def divisorFee (p h : Shape) (md mp : ℕ) : ℕ :=
  ceilDiv (P3.t * md) (32 * incidenceGap) + ceilDiv mp 32 +
    20 * p.b * h.b ^ 2 + 5 * physicalDegree * p.b * h.b + 1
private def singularFee (x : Shape) (ms : ℕ) : ℕ :=
  if 1 < x.t then ceilDiv (4 * x.t * ms) 32 + x.t * x.b ^ 2 + 1 else 0
private def curveFee (mc mq : ℕ) : ℕ :=
  let length := (fatOrder - isolatedOrder + 1) * (fatOrder - divisorOrder + 2 - isolatedOrder)
  ceilDiv (P3.t * mc + incidenceGap * mq) (32 * incidenceGap * length)
private def isolatedFee : ℕ :=
  ceilDiv (3 * resultantBox.j ^ 2 * (2 * resultantBox.b - resultantBox.j))
    (4 * fatOrder * (fatOrder - divisorOrder + 1) * isolatedOrder)
private theorem fatPrice_expand (x : Shape) :
    fatPrice x =
      divisorFee x.chamber (fatChart x)
        (mixed32 x.chamber divisorBox (divisorCut (fatChart x)) (fatChart x))
        (mixed32 x.chamber divisorBox (divisorCut (fatChart x)) x.chamber) +
      singularFee x (mixed32 x.chamber x.chamber (fatChart x) (fatChart x)) +
      curveFee (mixed32 x.chamber resultantBox resultantBox (fatChart x))
        (mixed32 x.chamber resultantBox resultantBox x.chamber) + isolatedFee := rfl
private theorem chamber_widen {x y : Shape} (h : TotalLE x y) :
    TotalLE x.chamber y.chamber :=
  ⟨max_le_max h.1 h.2.1.le, h.2⟩
private theorem chart_widen (L : ℕ) {x y : Shape} (h : TotalLE x y) :
    TotalLE (chart L x) (chart L y) := by
  refine ⟨?_, by simp only [chart, h.2.1], by simp only [chart, h.2.1, h.2.2]⟩
  dsimp only [chart]
  rw [h.2.1]
  exact max_le_max
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right h.1 _)) _) le_rfl
private theorem fatChart_widen {x y : Shape} (h : TotalLE x y) :
    TotalLE (fatChart x) (fatChart y) := by
  have hp := chamber_widen h
  unfold fatChart
  rw [← h.2.2]
  split
  · refine ⟨?_, by simp only [linearChart, hp.2.1], by simp only [linearChart, hp.2.1]⟩
    dsimp only [linearChart]
    rw [hp.2.1]
    exact max_le_max
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hp.1 _)) _) le_rfl
  · exact chart_widen _ hp
private theorem cut_widen {h H : Shape} (hh : TotalLE h H) :
    TotalLE (divisorCut h) (divisorCut H) := by
  refine ⟨?_, by simp only [divisorCut, hh.2.1], by simp only [divisorCut, hh.2.2]⟩
  dsimp only [divisorCut]
  rw [hh.2.1]
  exact max_le_max (max_le_max hh.1 le_rfl) le_rfl
private theorem capped_index (b j t : ℕ) : IndexFits ⟨b, j, min t (j / 3)⟩ := by
  change 3 * min t (j / 3) ≤ j
  exact (Nat.mul_le_mul_left 3 (min_le_right _ _)).trans (by omega)
private theorem fatChart_index (x : Shape) : IndexFits (fatChart x) := by
  unfold fatChart
  split <;> exact capped_index _ _ _
private theorem cut_index {h : Shape} (hh : IndexFits h) : IndexFits (divisorCut h) := by
  change 3 * h.t ≤ h.j at hh
  change 3 * max 1 h.t ≤ max h.j (divisorBox.j + 1)
  rcases le_total 1 h.t with ht | ht
  · rw [max_eq_right ht]
    exact hh.trans (le_max_left _ _)
  · rw [max_eq_left ht]
    exact (show 3 * 1 ≤ divisorBox.j + 1 from by decide).trans (le_max_right _ _)
private theorem ceil_mono {a b l : ℕ} (h : a ≤ b) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h _) _)
private theorem fatPrice_widen {x y : Shape} (h : TotalLE x y) (hv : IndexFits x) :
    fatPrice x ≤ fatPrice y := by
  have hp := chamber_widen h
  have hh := fatChart_widen h
  have hc := cut_widen hh
  have hp' : IndexFits x.chamber := hv
  have hh' := fatChart_index x
  have hc' := cut_index hh'
  have hbig : IndexFits divisorBox := Nat.zero_le _
  have hq : IndexFits resultantBox := Nat.zero_le _
  rw [fatPrice_expand x, fatPrice_expand y]
  refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_) le_rfl
  · have hd := mixed_mono_total hp (TotalLE.refl divisorBox) hc hh hp' hbig hc' hh'
    have hm := mixed_mono_total hp (TotalLE.refl divisorBox) hc hp hp' hbig hc' hp'
    dsimp only [divisorFee]
    refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_) ?_) le_rfl
    · exact ceil_mono (Nat.mul_le_mul_left _ hd)
    · exact ceil_mono hm
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hp.1)
        (by simpa only [pow_two] using Nat.mul_le_mul hh.1 hh.1)
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hp.1) hh.1
  · have hs := mixed_mono_total hp hp hh hh hp' hp' hh' hh'
    dsimp only [singularFee]
    rw [← h.2.2]
    split
    · exact Nat.add_le_add (Nat.add_le_add (ceil_mono (Nat.mul_le_mul_left _ hs))
        (Nat.mul_le_mul_left _ (by simpa only [pow_two] using Nat.mul_le_mul h.1 h.1))) le_rfl
    · exact le_rfl
  · have hc := mixed_mono_total hp (TotalLE.refl resultantBox) (TotalLE.refl resultantBox)
      hh hp' hq hq hh'
    have hm := mixed_mono_total hp (TotalLE.refl resultantBox) (TotalLE.refl resultantBox)
      hp hp' hq hq hp'
    exact ceil_mono (Nat.add_le_add (Nat.mul_le_mul_left _ hc) (Nat.mul_le_mul_left _ hm))
private def fromSlack (p : Shape) : Shape :=
  ⟨p.b + p.j + 3 * p.t, p.j + 3 * p.t, p.t⟩
private def degreeCoeff (p q r : Shape) : ℕ :=
  16 * (p.j * q.j * r.t + p.j * q.t * r.j + p.t * q.j * r.j) +
  48 * (p.j * q.t * r.t + p.t * q.j * r.t + p.t * q.t * r.j) + 144 * p.t * q.t * r.t
private def degreePart (p q r s : Shape) : ℕ :=
  p.b * degreeCoeff q r s + q.b * degreeCoeff p r s +
  r.b * degreeCoeff p q s + s.b * degreeCoeff p q r
private def indexPart (p q r s : Shape) : ℕ :=
  24 * (p.j * q.j * r.j * s.t + p.j * q.j * r.t * s.j +
    p.j * q.t * r.j * s.j + p.t * q.j * r.j * s.j) +
  104 * (p.j * q.j * r.t * s.t + (p.j * q.t + p.t * q.j) * (r.j * s.t + r.t * s.j) +
    p.t * q.t * r.j * s.j) +
  312 * ((p.j * q.t + p.t * q.j) * r.t * s.t + p.t * q.t * (r.j * s.t + r.t * s.j)) +
  936 * p.t * q.t * r.t * s.t
set_option maxHeartbeats 2000000 in
private theorem mixed_from_parts (p q r s : Shape) (d i : ℕ)
    (hd : degreePart p q r s = d) (hi : indexPart p q r s = i) :
    mixed32 (fromSlack p) (fromSlack q) (fromSlack r) (fromSlack s) = d + i := by
  have h :
      K1_13.difference (K1_13.difference (K1_13.difference
        (K1_13.difference K1_13.volume32 (fromSlack p)) (fromSlack q)) (fromSlack r))
        (fromSlack s) ⟨0,0,0⟩ = (↑(degreePart p q r s + indexPart p q r s) : ℤ) := by
    simp only [K1_13.difference, K1_13.volume32, Shape.plus, fromSlack,
      degreePart, degreeCoeff, indexPart, Nat.cast_add, Nat.cast_mul, Nat.cast_zero, Nat.cast_ofNat]
    ring
  unfold mixed32
  rw [h, Int.toNat_natCast, hd, hi]
private abbrev divisorSlack : Shape := ⟨15311,7683,0⟩
private abbrev resultantSlack : Shape := ⟨0x2596a670,0x13315480,0⟩
private theorem isolated_value : isolatedFee = 0x4a9107dde10a := by decide
private theorem singular_from_mix {x h : Shape} {m fee : ℕ}
    (hx : x.chamber = x) (hh : fatChart x = h)
    (hm : mixed32 x x h h = m) (hfee : singularFee x m = fee) :
    singularFee x (mixed32 x.chamber x.chamber (fatChart x) (fatChart x)) = fee := by
  rwa [hx, hh, hm]
private theorem fee_of_parts {x h : Shape} {md mp mc mq divs singular curves cap : ℕ}
    (hx : x.chamber = x) (hh : fatChart x = h) (hc : divisorCut h = h)
    (hd : mixed32 x ⟨22994,7683,0⟩ h h = md)
    (hp : mixed32 x ⟨22994,7683,0⟩ h x = mp)
    (hcurve : mixed32 x resultantBox resultantBox h = mc)
    (hpoint : mixed32 x resultantBox resultantBox x = mq)
    (hdivs : divisorFee x h md mp = divs)
    (hsingular : singularFee x (mixed32 x.chamber x.chamber (fatChart x) (fatChart x)) = singular)
    (hcurves : curveFee mc mq = curves) (hcap : divs + singular + curves + 0x4a9107dde10a ≤ cap) :
    fatPrice x ≤ cap := by
  rw [fatPrice_expand, hsingular, hx, hh, hc, divisorBox_eq, hd, hp,
    hcurve, hpoint, hdivs, hcurves, isolated_value]
  exact hcap
local notation "mix!" p "," q "," r "," s "," d "," i =>
  mixed_from_parts p q r s d i (by decide) (by decide)
local notation "row!" p "," w "," limit "," sf "," sg "," dv "," cv ","
    dd "," di "," pd "," pi "," cd "," ci "," qd "," qi =>
  fee_of_parts (x := fromSlack p) (h := fromSlack w) (cap := limit)
    (divs := dv) (singular := sf) (curves := cv) rfl shape! shape!
    (mix! p, divisorSlack, w, w, dd, di) (mix! p, divisorSlack, w, p, pd, pi)
    (mix! p, resultantSlack, resultantSlack, w, cd, ci)
    (mix! p, resultantSlack, resultantSlack, p, qd, qi)
    (by decide) sg (by decide) (by decide)
private theorem r1 : fatPrice ⟨20,3,1⟩ ≤ oneReserve :=
  row! ⟨17,0,1⟩,⟨2400208,1,44449⟩, (oneReserve),0, rfl,
    0x1cd53f90fdc3d6,0x1c521449306a5,
    0x1530af4976536f0,0x10d368af8c3e60,0x166ac9ee3c0,0x18ced595e0,
    0x50c1e82ebe2c1f3600000,0x657f04d8a73218600000,0x41d4c539e69050000,0x95a5650f7cba0000
private theorem r2 : fatPrice ⟨17,4,1⟩ ≤ oneReserve :=
  row! ⟨13,1,1⟩,⟨1866828,2,88897⟩, (oneReserve),0, rfl,
    0x3665f9ec47e38d, 0x2498f9c691df1,
    0x31cf650e3719210,0x59bc4de5b33c00,0x264e63ef4e0,0x56823921f0,
    0x60f1476c4d604599e0000,0xf9d56b320fde44ec0000,0x41979737d4ee30000,0xdab6a76567860000
private theorem r3 : fatPrice ⟨14,5,1⟩ ≤ oneReserve :=
  row! ⟨9,2,1⟩,⟨1333448,0,133346⟩, (oneReserve),0, rfl,
    0x54032d330fd2e5,0x2dc61cf551a25,
    0x4c258db893d5a80,0xfc6132218e8c60,0x320ca405520,0xc48d64e650,
    0x70f7408ea430888fe0000,0x1bd041945c1cd944c0000,0x415a6935c34c10000,0x11fc7e9bb52520000
private theorem r4 : fatPrice ⟨7,6,1⟩ ≤ oneReserve :=
  row! ⟨1,3,1⟩,⟨266688,133345,133346⟩, (oneReserve),0, rfl,
    0x43917917da01f7,0x28db2839c59b8,
    0x2dfff23faa451f0,0x1e55814af3d3fc8,0x1d06355b6d0,0x14df29ac8e8,
    0x590ec9a35647e6cdb0000,0x2498bfeb8356a46fe0000,0x359a5ad00a87f0000,0x164d92c113d1e0000
private theorem r5 : fatPrice ⟨7,6,2⟩ ≤ twoReserve :=
  row! ⟨1,0,2⟩,⟨666743,2,311148⟩, (twoReserve),0x956f762bad03, (singular_from_mix rfl shape!
      (mix! ⟨1,0,2⟩,⟨1,0,2⟩,⟨666743,2,311148⟩,⟨666743,2,311148⟩,0x10c13c9f69800,0x149aa0eb81a80)
      (by decide)),
    0xf268a7e8373393,0x5cd207bd3dffb,
    0xaaabd813a065d00,0x670f71e9fd68c40,0x3cec3f2b3c0,0x2b6a1441540,
    0xc4a9bef18782d775c0000,0x58cf6c2f8cbaa9e880000,0x49639e7b549040000,0x25695943df2e80000
private theorem r6 : fatPrice ⟨6,3,1⟩ ≤ twoReserve / 2 :=
  row! ⟨3,0,1⟩,⟨533378,1,44449⟩, (twoReserve / 2),0, rfl,
    0x5d328074de088,0xa8d12b09a931,
    0x555dbc14083cd0,0x10d368af8c3e60,0x5b83f18ae0,0x18ced595e0,
    0x1a1b47d791364b7f00000,0x657f04d8a73218600000,0x198ab3dd1d9950000,0x95a5650f7cba0000
theorem proof : P3_6_8.c2 := by
  intro ⟨b, j, t⟩ ha hb
  have hjt : 3 * t ≤ j := ha.2.1
  have hj6 : j ≤ 6 := hb.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro ht
    change t = 1 at ht
    subst t
    have hj : j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
    rcases hj with rfl | rfl | rfl | rfl
    · exact (fatPrice_widen (y := ⟨20,3,1⟩) ⟨hb.1, rfl, rfl⟩ hjt).trans r1
    · exact (fatPrice_widen (y := ⟨17,4,1⟩) ⟨hb.2.2.1 le_rfl, rfl, rfl⟩ hjt).trans r2
    · exact (fatPrice_widen (y := ⟨14,5,1⟩) ⟨hb.2.2.2.1 le_rfl, rfl, rfl⟩ hjt).trans r3
    · exact (fatPrice_widen (y := ⟨7,6,1⟩) ⟨hb.2.2.2.2 le_rfl, rfl, rfl⟩ hjt).trans r4
  · intro ht
    change t = 2 at ht
    subst t
    have hj : j = 6 := by omega
    subst j
    exact (fatPrice_widen (y := ⟨7,6,2⟩) ⟨hb.2.2.2.2 le_rfl, rfl, rfl⟩ hjt).trans r5
  · intro ht hj hb6
    change t = 1 at ht
    change j = 3 at hj
    subst t
    subst j
    have hfee := (fatPrice_widen (y := ⟨6,3,1⟩) ⟨hb6, rfl, rfl⟩ hjt).trans r6
    exact (Nat.mul_le_mul_left 2 hfee).trans (by decide)
end P3_6_8_2
end
section
namespace P3_6_8_3
open K1_13_8 (zeroShape availableMass zeroMass fastRemaining)
open K1_13_8_2 (Threshold)
open scoped BigOperators
private def sumBelow (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumBelow f n + f n
private theorem sumBelow_eq (f : ℕ → ℕ) (n : ℕ) :
    sumBelow f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => rw [sumBelow, Finset.sum_range_succ, ih]
private theorem sumBelow_add (f : ℕ → ℕ) (m n : ℕ) :
    sumBelow f (m + n) = sumBelow f m + sumBelow (fun k => f (m + k)) n := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih =>
    change sumBelow f (m + n) + f (m + n) =
      sumBelow f m + (sumBelow (fun k => f (m + k)) n + f (m + n))
    rw [ih, Nat.add_assoc]
private def tailTerm (b j k : ℕ) : ℕ :=
  fastRemaining ((k + 1) * b) ((k + 1) * j)
private theorem extend {f : ℕ → ℕ} {m n N x total : ℕ}
    (hleft : sumBelow f m = x)
    (hright : sumBelow (fun k => f (m + k)) n = total - x)
    (hlen : m + n = N) (hle : x ≤ total) :
    sumBelow f N = total := by
  rw [← hlen, sumBelow_add, hleft, hright, Nat.add_sub_of_le hle]
private theorem zeroMass_eq (b j : ℕ) :
    zeroMass b j = sumBelow (tailTerm b j) (1650 / j) :=
  (sumBelow_eq _ _).symm
local notation "block!" h "," len "," k "," t =>
  extend h (n := len) (N := k) (total := t) rfl rfl (by decide)
private theorem r1 : zeroMass 107 46 = 0x286a49ace04 := by
  rw [zeroMass_eq]
  have h : sumBelow (tailTerm 107 46) 0 = 0 := rfl
  have h := block! h, 8,8,0x1cf5a8d1c59
  have h := block! h, 8,16,0x264d9a2d3f4
  have h := block! h, 8,24,0x284142fca90
  have h := block! h, 8,32,0x286a26ff521
  exact block! h, 3,35,0x286a49ace04
private theorem r2 : zeroMass 14 41 = 0x39c61c47c4b := by
  rw [zeroMass_eq]
  have h : sumBelow (tailTerm 14 41) 0 = 0 := rfl
  have h := block! h, 8,8,0x21fefc6cbea
  have h := block! h, 8,16,0x323cf7fd6b5
  have h := block! h, 8,24,0x384b7872f96
  have h := block! h, 8,32,0x39af6306b28
  exact block! h, 8,40,0x39c61c47c4b
private theorem r3 : zeroMass 61 31 = 0x4040a84f1a4 := by
  rw [zeroMass_eq]
  have h : sumBelow (tailTerm 61 31) 0 = 0 := rfl
  have h := block! h, 8,8,0x22945e24fa2
  have h := block! h, 8,16,0x346505c0ff6
  have h := block! h, 8,24,0x3c6c6fe4cb4
  have h := block! h, 8,32,0x3f610fa8906
  have h := block! h, 8,40,0x4026c33a08a
  have h := block! h, 8,48,0x404044e96f8
  exact block! h, 5,53,0x4040a84f1a4
private theorem r4 : zeroMass 8 13 = 0xb740cb8402f := by
  rw [zeroMass_eq]
  have h : sumBelow (tailTerm 8 13) 0 = 0 := rfl
  have h := block! h, 8,8,0x2aa8fc26d41
  have h := block! h, 8,16,0x4d567d5d214
  have h := block! h, 8,24,0x691e22d19d0
  have h := block! h, 8,32,0x7effc005539
  have h := block! h, 8,40,0x8fe5ba3f5dc
  have h := block! h, 8,48,0x9ca565fef10
  have h := block! h, 8,56,0xa5ff646e461
  have h := block! h, 8,64,0xaca000d6494
  have h := block! h, 8,72,0xb11f8e10b00
  have h := block! h, 8,80,0xb402c3fadf9
  have h := block! h, 8,88,0xb5bb1ce997c
  have h := block! h, 8,96,0xb6a7331b0e0
  have h := block! h, 8,104,0xb7131e29d41
  have h := block! h, 8,112,0xb738d0807d4
  have h := block! h, 8,120,0xb74074cbbf0
  exact block! h, 6,126,0xb740cb8402f
private theorem r5 : zeroMass 9 7 = 0x13ef0ca5101c := by
  rw [zeroMass_eq]
  have h : sumBelow (tailTerm 9 7) 0 = 0 := rfl
  have h := block! h, 8,8,0x2c993b24c2a
  have h := block! h, 8,16,0x54292edfe26
  have h := block! h, 8,24,0x771d27d3a98
  have h := block! h, 8,32,0x95dc5c41bb2
  have h := block! h, 8,40,0xb0c8156ec3e
  have h := block! h, 8,48,0xc83bd9048e0
  have h := block! h, 8,56,0xdc8d9274eaa
  have h := block! h, 8,64,0xee0dbc5d586
  have h := block! h, 8,72,0xfd0789e9218
  have h := block! h, 8,80,0x109c11034452
  have h := block! h, 8,88,0x1147b6faf13e
  have h := block! h, 8,96,0x11d72fd80580
  have h := block! h, 8,104,0x124df6ce83ea
  have h := block! h, 8,112,0x12af3f8a3ea6
  have h := block! h, 8,120,0x12fdf8c4fa58
  have h := block! h, 8,128,0x133ccedc9cb2
  have h := block! h, 8,136,0x136e2e6964fe
  have h := block! h, 8,144,0x139446d40fe0
  have h := block! h, 8,152,0x13b10cec05ea
  have h := block! h, 8,160,0x13c63d7d9386
  have h := block! h, 8,168,0x13d55fe80d58
  have h := block! h, 8,176,0x13dfc8b3fed2
  have h := block! h, 8,184,0x13e69c29617e
  have h := block! h, 8,192,0x13ead0e5c200
  have h := block! h, 8,200,0x13ed32726eaa
  have h := block! h, 8,208,0x13ee63daae26
  have h := block! h, 8,216,0x13eee241e518
  have h := block! h, 8,224,0x13ef0779c4b2
  have h := block! h, 8,232,0x13ef0c9880be
  exact block! h, 3,235,0x13ef0ca5101c
private theorem r6 : zeroMass 22 4 = 0x143e8e62c9dd := by
  rw [zeroMass_eq]
  have h : sumBelow (tailTerm 22 4) 0 = 0 := rfl
  have h := block! h, 8,8,0x2ccd7433584
  have h := block! h, 8,16,0x54e026962aa
  have h := block! h, 8,24,0x78928ada068
  have h := block! h, 8,32,0x983ab2675dc
  have h := block! h, 8,40,0xb42a6741c82
  have h := block! h, 8,48,0xccaf46ead50
  have h := block! h, 8,56,0xe212dd45ab4
  have h := block! h, 8,64,0xf49abf7b2da
  have h := block! h, 8,72,0x10488a6dceb8
  have h := block! h, 8,80,0x1121a8bc8c0c
  have h := block! h, 8,88,0x11d8ac08cdb2
  have h := block! h, 8,96,0x127100c4aca0
  have h := block! h, 8,104,0x12eddc5db1e4
  have h := block! h, 8,112,0x13523eeb150a
  have h := block! h, 8,120,0x13a0f4dbef08
  have h := block! h, 8,128,0x13dc98a5743c
  have h := block! h, 8,136,0x1407948d21b0
  have h := block! h, 8,144,0x14242eba3f02
  have h := block! h, 8,152,0x1434c84c5e6a
  have h := block! h, 8,160,0x143c41fed04e
  have h := block! h, 8,168,0x143e50948e68
  have h := block! h, 8,176,0x143e8d84d8ac
  have h := block! h, 8,184,0x143e8e62c9dd
  have h := block! h, 8,192,0x143e8e62c9dd
  have h := block! h, 8,200,0x143e8e62c9dd
  have h := block! h, 8,208,0x143e8e62c9dd
  have h := block! h, 8,216,0x143e8e62c9dd
  have h := block! h, 8,224,0x143e8e62c9dd
  have h := block! h, 8,232,0x143e8e62c9dd
  have h := block! h, 8,240,0x143e8e62c9dd
  have h := block! h, 8,248,0x143e8e62c9dd
  have h := block! h, 8,256,0x143e8e62c9dd
  have h := block! h, 8,264,0x143e8e62c9dd
  have h := block! h, 8,272,0x143e8e62c9dd
  have h := block! h, 8,280,0x143e8e62c9dd
  have h := block! h, 8,288,0x143e8e62c9dd
  have h := block! h, 8,296,0x143e8e62c9dd
  have h := block! h, 8,304,0x143e8e62c9dd
  have h := block! h, 8,312,0x143e8e62c9dd
  have h := block! h, 8,320,0x143e8e62c9dd
  have h := block! h, 8,328,0x143e8e62c9dd
  have h := block! h, 8,336,0x143e8e62c9dd
  have h := block! h, 8,344,0x143e8e62c9dd
  have h := block! h, 8,352,0x143e8e62c9dd
  have h := block! h, 8,360,0x143e8e62c9dd
  have h := block! h, 8,368,0x143e8e62c9dd
  have h := block! h, 8,376,0x143e8e62c9dd
  have h := block! h, 8,384,0x143e8e62c9dd
  have h := block! h, 8,392,0x143e8e62c9dd
  have h := block! h, 8,400,0x143e8e62c9dd
  have h := block! h, 8,408,0x143e8e62c9dd
  exact block! h, 4,412,0x143e8e62c9dd
private theorem r7 : zeroMass 3 7 = 0x15d874744918 := by
  rw [zeroMass_eq]
  have h : sumBelow (tailTerm 3 7) 0 = 0 := rfl
  have h := block! h, 8,8,0x2cf73313ec4
  have h := block! h, 8,16,0x557453747ba
  have h := block! h, 8,24,0x79c5beb596c
  have h := block! h, 8,32,0x9a371914fb0
  have h := block! h, 8,40,0xb7114bfdf56
  have h := block! h, 8,48,0xd09a848b6e8
  have h := block! h, 8,56,0xe716320acec
  have h := block! h, 8,64,0xfac5047fb82
  have h := block! h, 8,72,0x10be4eb26134
  have h := block! h, 8,80,0x11ab112f4f38
  have h := block! h, 8,88,0x12761e5224fe
  have h := block! h, 8,96,0x1322d05a5110
  have h := block! h, 8,104,0x13b4551b7f54
  have h := block! h, 8,112,0x142dade5d48a
  have h := block! h, 8,120,0x1491af6e0f3c
  have h := block! h, 8,128,0x14e301b5b600
  have h := block! h, 8,136,0x15241ff352e6
  have h := block! h, 8,144,0x1557587a9478
  have h := block! h, 8,152,0x157ecca47bfc
  have h := block! h, 8,160,0x159c70b798d2
  have h := block! h, 8,168,0x15b20bd02984
  have h := block! h, 8,176,0x15c137c84a08
  have h := block! h, 8,184,0x15cb61202f0e
  have h := block! h, 8,192,0x15d1c6e64720
  have h := block! h, 8,200,0x15d57a9f68e4
  have h := block! h, 8,208,0x15d7602f0e5a
  have h := block! h, 8,216,0x15d82dbf760c
  have h := block! h, 8,224,0x15d86ba9d150
  have h := block! h, 8,232,0x15d8745e7f76
  exact block! h, 3,235,0x15d874744918
private theorem r8 : zeroMass 4 10 = 0xf47ed882a04 := by
  rw [zeroMass_eq]
  have h : sumBelow (tailTerm 4 10) 0 = 0 := rfl
  have h := block! h, 8,8,0x2be35e679da
  have h := block! h, 8,16,0x519ac1fe3a6
  have h := block! h, 8,24,0x71c06c2b6ae
  have h := block! h, 8,32,0x8ce6f972988
  have h := block! h, 8,40,0xa399554cbc4
  have h := block! h, 8,48,0xb65aae006ac
  have h := block! h, 8,56,0xc5a6687ab86
  have h := block! h, 8,64,0xd1f01428f32
  have h := block! h, 8,72,0xdba35ed0afa
  have h := block! h, 8,80,0xe3240868ad4
  have h := block! h, 8,88,0xe8cdd6f28f0
  have h := block! h, 8,96,0xecf48a52e98
  have h := block! h, 8,104,0xefe3d02a272
  have h := block! h, 8,112,0xf1df37ae3fe
  have h := block! h, 8,120,0xf3222582c86
  have h := block! h, 8,128,0xf3dfc791d60
  have h := block! h, 8,136,0xf44308e5b5c
  have h := block! h, 8,144,0xf46e8580fc4
  have h := block! h, 8,152,0xf47c7e3769e
  have h := block! h, 8,160,0xf47ecc87a0a
  exact block! h, 5,165,0xf47ed882a04
private theorem r9 : zeroMass 10 28 = 0x55cf969adb0 := by
  rw [zeroMass_eq]
  have h : sumBelow (tailTerm 10 28) 0 = 0 := rfl
  have h := block! h, 8,8,0x25dedfd1408
  have h := block! h, 8,16,0x3d9cf5e83b2
  have h := block! h, 8,24,0x4b3c4320f48
  have h := block! h, 8,32,0x521a8eae460
  have h := block! h, 8,40,0x54ec565398a
  have h := block! h, 8,48,0x55b7be9cf10
  have h := block! h, 8,56,0x55cf8317d38
  exact block! h, 2,58,0x55cf969adb0
private theorem startCount : fastRemaining 0 0 = 0x5f37df242c := rfl
private theorem threshold_lt (s : Threshold) {tail mass : ℕ}
    (htail : zeroMass s.b s.j = tail)
    (hmass : (s.l - 1) * 0x5f37df242c + tail = mass)
    (hlt : mass < P3_6.layerNeed) :
    availableMass zeroShape ⟨s.b, s.j, 0⟩ (s.l - 1) < P3_6.layerNeed := by
  simp only [availableMass, zeroShape, Nat.zero_add, Nat.mul_zero, ite_true]
  change (s.l - 1) * fastRemaining 0 0 + zeroMass s.b s.j < P3_6.layerNeed
  rw [startCount, htail, hmass]
  exact hlt
theorem proof : P3_6_8.c3 := by
  intro s hs
  simp [P3_6_8.emptyThresholds] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact threshold_lt ⟨107,46,56⟩ r1 (mass := 0x16fba58b9378) rfl (by decide)
  · exact threshold_lt ⟨14,41,53⟩ r2 (mass := 0x16f3bb17d53b) rfl (by decide)
  · exact threshold_lt ⟨61,31,52⟩ r3 (mass := 0x16fc2bf92668) rfl (by decide)
  · exact threshold_lt ⟨8,13,32⟩ r4 (mass := 0x16fbd0bda183) rfl (by decide)
  · exact threshold_lt ⟨9,7,9⟩ r5 (mass := 0x16e8cb9e317c) rfl (by decide)
  · exact threshold_lt ⟨22,4,8⟩ r6 (mass := 0x16d9157cc711) rfl (by decide)
  · exact threshold_lt ⟨3,7,4⟩ r7 (mass := 0x16f61c11b59c) rfl (by decide)
  · exact threshold_lt ⟨4,10,22⟩ r8 (mass := 0x171782d621a0) rfl (by decide)
  · exact threshold_lt ⟨10,28,48⟩ r9 (mass := 0x16d83b6151c4) rfl (by decide)
end P3_6_8_3
end
section
namespace P3_6_8_4
open K1_13
open K1_13_8_2 (Chamber mixed_mono)
open private P0_9_8_3.box_refl P0_9_8_3.normalize_mono P0_9_8_3.normalize_chamber P0_9_8_3.plus_mono P0_9_8_3.plus_chamber
  P0_9_8_3.scale_mono P0_9_8_3.scale_chamber P0_9_8_3.chart_chamber P0_9_8_3.lifted_chamber P0_9_8_3.chart_mono P0_9_8_3.lifted_mono
  P0_9_8_3.graphShape P0_9_8_3.graph_chamber P0_9_8_3.graph_mono P0_9_8_3.ceil_mono from ProximityPrize.SubmissionLower.PortLow8
private theorem surface_mono {p p' q : Shape} (hp : InBox p p') (hp' : Chamber p') (hq : Chamber q) :
    P3_6.surfaceNumerator32 p q ≤ P3_6.surfaceNumerator32 p' q := by
  let L := P3_6.taylorLength
  have hchart : mixed32 p q (chart (L+1) p) (chart (L+2) p) ≤
      mixed32 p' q (chart (L+1) p') (chart (L+2) p') :=
    mixed_mono hp (P0_9_8_3.box_refl q) (P0_9_8_3.chart_mono _ hp) (P0_9_8_3.chart_mono _ hp) hp' hq
      (P0_9_8_3.chart_chamber _ _) hq (P0_9_8_3.chart_chamber _ _) (P0_9_8_3.chart_chamber _ _)
  have hlift : mixed32 p q (liftedChart (L+1) p) (liftedChart (L+2) p) ≤
      mixed32 p' q (liftedChart (L+1) p') (liftedChart (L+2) p') :=
    mixed_mono hp (P0_9_8_3.box_refl q) (P0_9_8_3.lifted_mono _ hp) (P0_9_8_3.lifted_mono _ hp) hp' hq
      (P0_9_8_3.lifted_chamber _ _) hq (P0_9_8_3.lifted_chamber _ _) (P0_9_8_3.lifted_chamber _ _)
  have hgraph (M : ℕ) :
      mixed32 p q (P0_9_8_3.graphShape p) (liftedChart M p) ≤ mixed32 p' q (P0_9_8_3.graphShape p') (liftedChart M p') :=
    mixed_mono hp (P0_9_8_3.box_refl q) (P0_9_8_3.graph_mono hp) (P0_9_8_3.lifted_mono _ hp) hp' hq
      (P0_9_8_3.graph_chamber _) hq (P0_9_8_3.graph_chamber _) (P0_9_8_3.lifted_chamber _ _)
  exact min_le_min hchart (Nat.add_le_add (Nat.add_le_add hlift (Nat.mul_le_mul_left _ (hgraph _)))
    (Nat.mul_le_mul_left _ (hgraph _)))
theorem physical_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l : ℕ) : P3_6.physicalPrice x l ≤ P3_6.physicalPrice y l := by
  let p := x.chamber
  let p' := y.chamber
  let q : Shape := P3_6.primaryBox
  let L := P3_6.taylorLength
  let A := q.plus (p.scale 4)
  let A' := q.plus (p'.scale 4)
  have hp := P0_9_8_3.normalize_mono h
  have hpc : Chamber p := P0_9_8_3.normalize_chamber x hx
  have hp'c : Chamber p' := P0_9_8_3.normalize_chamber y hy
  have hqc : Chamber q := ⟨by decide, by decide⟩
  have ha : InBox A A' := P0_9_8_3.plus_mono (P0_9_8_3.box_refl q) (P0_9_8_3.scale_mono hp 4)
  have hac : Chamber A := P0_9_8_3.plus_chamber hqc (P0_9_8_3.scale_chamber hpc 4)
  have ha'c : Chamber A' := P0_9_8_3.plus_chamber hqc (P0_9_8_3.scale_chamber hp'c 4)
  have hs := surface_mono hp hp'c hqc
  have hb := (P0_9_8_3.chart_mono (L+1) hp).1
  have hmain : (P3.t + 2*P3_6.incidenceGap) * x.b * q.b * (chart (L+1) p).b ≤
      (P3.t + 2*P3_6.incidenceGap) * y.b * q.b * (chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (P0_9_8_3.box_refl q) ha (P0_9_8_3.chart_mono L hp) hp'c hqc ha'c hqc hac (P0_9_8_3.chart_chamber L p)
  have hpoint := mixed_mono hp (P0_9_8_3.box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (P0_9_8_3.chart_mono L hp) hp'c hp'c hp'c hpc hpc (P0_9_8_3.chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left P3.t hc) (Nat.mul_le_mul_left (2*P3_6.incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*P3_6.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (P0_9_8_3.ceil_mono (Nat.add_le_add (P0_9_8_3.ceil_mono hs _) (P0_9_8_3.ceil_mono hmain _)) l) hraw)
    (P0_9_8_3.ceil_mono hgeom _)
end P3_6_8_4
end
section
namespace P3_6_8_4
open K1_13 (Shape chart mixed32 ceilDiv)
open K1_13_8 (zeroShape)
open P0_9_8 (indexBudget)
open P3_6_8 (emptyOrder)
open P3_6 (physicalPrice physicalDegree incidenceGap primaryBox surfaceNumerator32 taylorLength factorCap)
def peak (b j : ℕ) : Shape := ⟨b, j, min 10 (j / 3)⟩
private def mainFee (x : Shape) : ℕ :=
  ceilDiv (surfaceNumerator32 x.chamber primaryBox) 32 +
    ceilDiv ((P3.t + 2 * incidenceGap) * x.b * primaryBox.b *
      (chart (taylorLength + 1) x.chamber).b) incidenceGap
private def auxFee (x : Shape) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let z := q.plus (p.scale 4)
  let curves := mixed32 p q z h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q z p + 2 * x.t * mixed32 p p p p
  2 * physicalDegree * x.b * q.b +
    ceilDiv (P3.t * curves + 2 * incidenceGap * points) (32 * incidenceGap)
private theorem price_eq (x : Shape) (l : ℕ) :
    physicalPrice x l = ceilDiv (mainFee x) l + auxFee x := by
  simp only [physicalPrice, mainFee, auxFee, Nat.add_assoc]
private abbrev RowBound (b j : ℕ) : Prop :=
  physicalPrice (peak b j) (emptyOrder (peak b j)) ≤ indexBudget zeroShape factorCap j
private theorem row (b j l main aux : ℕ)
    (horder : emptyOrder (peak b j) = l) (hmain : mainFee (peak b j) = main)
    (haux : auxFee (peak b j) = aux)
    (hle : ceilDiv main l + aux ≤ indexBudget zeroShape factorCap j) :
    RowBound b j := by
  change physicalPrice (peak b j) (emptyOrder (peak b j)) ≤ indexBudget zeroShape factorCap j
  rwa [price_eq, horder, hmain, haux]
local notation "row!" b "," j "," l "," m "," a => row b j l m a rfl rfl rfl (by decide)
theorem prices7 (j : ℕ) (hlo : 13 ≤ j) (hhi : j ≤ 21) :
    RowBound 7 j := by
  interval_cases j
  · exact row! 7,13,22,0x167e30676ac0ad2,0x8c0cd3ecd8c5
  · exact row! 7,14,22,0x1c62c8dac39df7c, 0xa511d6c0c92e
  · exact row! 7,15,22,0x23399feb7e233b2,0xc032fd693b1e
  · exact row! 7,16,22,0x2b14b5ff843c538,0xdd69ea63da64
  · exact row! 7,17,22,0x34060b7e7818d29,0xfcbbfdc2d7d6
  · exact row! 7,18,22,0x3e1fa0cc8b63683,0x11e3692729ab0
  · exact row! 7,19,22,0x4973764fa807f07,0x141cc33604a1f
  · exact row! 7,20,22,0x56138c6f7035fd1,0x167859177a4aa
  · exact row! 7,21,22,0x6411e39015983de, 0x18f76b948eeb3
theorem prices8 (j : ℕ) (hlo : 7 ≤ j) (hhi : j ≤ 9) :
    RowBound 8 j := by
  interval_cases j
  · exact row! 8,7,4,0x2fcb8420578586,0x2373f47abaa6
  · exact row! 8,8,4,0x4563e58d502008,0x2de17a49034a
  · exact row! 8,9,4,0x6b45a1439d00f0,0x3ca02bb59a50
theorem prices21 (j : ℕ) (hlo : 4 ≤ j) (hhi : j ≤ 6) :
    RowBound 21 j := by
  interval_cases j
  · exact row! 21,4,1,0x14574c7cf1d075,0x1970671cd35d
  · exact row! 21,5,1,0x2ce0e9fe9d92dd, 0x256d3c7ae5fd
  · exact row! 21,6,1,0x4f4eef1c0f6cef, 0x32aa0cf53e9e
theorem prices60 (j : ℕ) (hlo : 31 ≤ j) (hhi : j ≤ 40) :
    RowBound 60 j := by
  interval_cases j
  · exact row! 60,31,48,0x24d61ffe7482eba8,0x510ae523cc1bf
  · exact row! 60,32,48,0x276d204b66c8b2de, 0x551e77b253f31
  · exact row! 60,33,48,0x2a1c4836f7b25396,0x5948b2d4bafff
  · exact row! 60,34,48,0x2ce303b0d5eb4198,0x5d897efe82a7f
  · exact row! 60,35,48,0x2fc0daa6d3cbf32b, 0x61e0c4a32c503
  · exact row! 60,36,48,0x32b55506c3acec1c, 0x664e6c36395df
  · exact row! 60,37,48,0x35bffabe77e6b038,0x6ad25e2b2b366
  · exact row! 60,38,48,0x38e053bbc2d1c34c, 0x6f6c82f5833ec
  · exact row! 60,39,48,0x3c15e7ec76c6a925,0x741cc308c2dc5
  · exact row! 60,40,48,0x3f603f3e661de590,0x78e306d86b743
theorem prices106 (j : ℕ) (hlo : 46 ≤ j) (hhi : j ≤ 48) :
    RowBound 106 j := by
  interval_cases j
  · exact row! 106,46,53,0x8e70d0201815b916,0xd2f197554757e
  · exact row! 106,47,53,0x94d299eb692308e5,0xd9e2b6cb4d538
  · exact row! 106,48,53,0x9b53c874006703ca, 0xe0ebefc39ca88
theorem prices120 (j : ℕ) (hlo : 3 ≤ j) (hhi : j ≤ 48) :
    RowBound 120 j := by
  interval_cases j
  · exact row! 120,3,1,0x1b20d628741f37,0x5285c9c9b463
  · exact row! 120,4,8,0x7692590285deb1,0x846913de6aae
  · exact row! 120,5,8,0x1040f3e72c1b64d, 0xb7d023a935e7
  · exact row! 120,6,8,0x1c4b7526dcf18a3,0xecc151bce793
  · exact row! 120,7,9,0x2b7ea7aaa3d5d2b, 0x12336830a0a69
  · exact row! 120,8,9,0x3dde88ffda7e8ed, 0x15b319f633438
  · exact row! 120,9,9,0x51b16318bf6c252,0x194c08b6159af
  · exact row! 120,10,22,0x66c82f6471851bf, 0x1cfd0c1f858db
  · exact row! 120,11,22,0x7e510be401cd107,0x20c6993233bd6
  · exact row! 120,12,22,0x984ef6b5ecff2c1,0x24aa7ce0e6628
  · exact row! 120,13,32,0xb4c4edfa6817c4a, 0x28a5e8ed2c9ad
  · exact row! 120,14,32,0xd3b5efd36056e57,0x2cba118ce0296
  · exact row! 120,15,32,0xf524fa5f5277b7f, 0x30ea4eb1f4727
  · exact row! 120,16,32,0x119150bbe737691f, 0x3530ff56b570e
  · exact row! 120,17,32,0x13f892212b0937ec, 0x3990a6b956ca2
  · exact row! 120,18,32,0x168843b7a8689a7d, 0x3e0ee879c8ada
  · exact row! 120,19,32,0x1940956162a5562f, 0x42a1da8e5f705
  · exact row! 120,20,32,0x1c21b70078936bb7,0x474e041a201cd
  · exact row! 120,21,32,0x1f2bd876d1fe8dac, 0x4c1c375e588c5
  · exact row! 120,22,32,0x225f29a67236816b, 0x50fc85d6210be
  · exact row! 120,23,32,0x25bbda71780f47a9,0x55f6525bc62e1
  · exact row! 120,24,32,0x29421ab9cb5492fd, 0x5b16a0f59d70c
  · exact row! 120,25,32,0x2cf21a616f5628c4,0x6045821a3f1d8
  · exact row! 120,26,32,0x30cc094a82e809b3,0x658e2d0f6bee9
  · exact row! 120,27,32,0x34d01756edd5e861,0x6b02f8e02bfc8
  · exact row! 120,28,48,0x38fe7468b36f8a2b, 0x7081bb8be43b7
  · exact row! 120,29,48,0x3d575061f288efc6,0x761a984564889
  · exact row! 120,30,48,0x41dadb2492edcbc9,0x7be67663cb655
  · exact row! 120,31,52,0x4689449297ede391,0x81b67f3bb80d0
  · exact row! 120,32,52,0x4b62bc8e205d37d3,0x87a0f627cab45
  · exact row! 120,33,52,0x50671eff699bcd8f, 0x8da5c39b84c09
  · exact row! 120,34,52,0x5595d7d62255188d, 0x93c4d00a6796f
  · exact row! 120,35,52,0x5aee6f001ce18f14,0x99fe03e7f49cb
  · exact row! 120,36,52,0x60706c6b2b99b4f1,0xa05147a7ad36f
  · exact row! 120,37,52,0x661b580520d60df1,0xa6be83bd12cb0
  · exact row! 120,38,52,0x6beeb9bbceef1de1,0xad45a09ba6be2
  · exact row! 120,39,52,0x71ea197d083d688e, 0xb3e686b6ea757
  · exact row! 120,40,52,0x780cff369f1971c5,0xbaa11e825f564
  · exact row! 120,41,53,0x7e56f2d665dbbd53,0xc175507186c5b
  · exact row! 120,42,53,0x84c77c4a2edccf05,0xc86304f7e2291
  · exact row! 120,43,53,0x8b5e237fcc752aa8,0xcf6a2488f2e5a
  · exact row! 120,44,53,0x921a706510fd5409,0xd68a97983a607
  · exact row! 120,45,53,0x98fbeae7cecdcef5,0xddc4469939fee
  · exact row! 120,46,56,0xa0021af5d83f1f39,0xe51719ff73262
  · exact row! 120,47,56,0xa72c887cffa9c8a2,0xec82fa3e673b6
  · exact row! 120,48,56,0xae7abb6b17664efd, 0xf407cfc997a3e
end P3_6_8_4
end
section
namespace P3_6_8_4
open K1_13 (Shape InBox)
open K1_13_8 (Valid fullCap zeroShape)
open K1_13_8_2 (Threshold orderFor)
open P3_6 (physicalPrice factorCap)
open P3_6_8 (emptyOrder emptyThresholds)
open P0_9_8 (indexBudget)
private def endpoint (b j : ℕ) : Prop :=
  b = 120 ∨ emptyOrder (peak b j) ≠ emptyOrder (peak (b + 1) j)
private theorem orderFor_stays (b j : ℕ) (ss : List Threshold)
    (h : ∀ s ∈ ss, s.j ≤ j → s.b ≠ b + 1) :
    orderFor b j ss = orderFor (b + 1) j ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    have he : (s.b ≤ b ∧ s.j ≤ j) ↔ (s.b ≤ b + 1 ∧ s.j ≤ j) := by
      constructor
      · exact fun ⟨hb, hj⟩ => ⟨hb.trans (Nat.le_succ _), hj⟩
      · intro ⟨hb, hj⟩
        exact ⟨by have hn := h s List.mem_cons_self hj; omega, hj⟩
    simp only [orderFor, he, ih (fun s hs => h s (List.mem_cons_of_mem _ hs))]
private theorem active_threshold {b j : ℕ}
    (h : emptyOrder (peak b j) ≠ emptyOrder (peak (b + 1) j)) :
    ∃ s ∈ emptyThresholds, s.b = b + 1 ∧ s.j ≤ j := by
  by_contra hn
  apply h
  exact orderFor_stays b j emptyThresholds (fun s hs hj hb => hn ⟨s, hs, hb, hj⟩)
private theorem endpoint_bound {b j : ℕ} (hj : 3 ≤ j) (hmax : j ≤ 48)
    (hshape : j ≤ 3 * b) (he : endpoint b j) :
    physicalPrice (peak b j) (emptyOrder (peak b j)) ≤ indexBudget zeroShape factorCap j := by
  rcases he with rfl | hchange
  · exact prices120 j hj hmax
  obtain ⟨s, hs, hb, hjs⟩ := active_threshold hchange
  simp [emptyThresholds] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change 107 = b + 1 at hb
    have hb' : b = 106 := by omega
    subst b
    exact prices106 j hjs hmax
  · change 14 = b + 1 at hb
    change 41 ≤ j at hjs
    omega
  · change 61 = b + 1 at hb
    have hb' : b = 60 := by omega
    subst b
    change 31 ≤ j at hjs
    by_cases h41 : 41 ≤ j
    · have h4 : 4 ≤ j := by omega
      have h7 : 7 ≤ j := by omega
      have h10 : 10 ≤ j := by omega
      have h13 : 13 ≤ j := by omega
      have h28 : 28 ≤ j := by omega
      simp [emptyOrder, peak, emptyThresholds, orderFor, h4, h7, h10, h13, h28, h41, hjs] at hchange
    · exact prices60 j hjs (by omega)
  · change 8 = b + 1 at hb
    have hb' : b = 7 := by omega
    subst b
    exact prices7 j hjs hshape
  · change 9 = b + 1 at hb
    have hb' : b = 8 := by omega
    subst b
    change 7 ≤ j at hjs
    by_cases h10 : 10 ≤ j
    · by_cases h13 : 13 ≤ j <;>
        simp [emptyOrder, peak, emptyThresholds, orderFor, h13, h10, hjs] at hchange
    · exact prices8 j hjs (by omega)
  · change 22 = b + 1 at hb
    have hb' : b = 21 := by omega
    subst b
    change 4 ≤ j at hjs
    by_cases h7 : 7 ≤ j
    · by_cases h10 : 10 ≤ j <;> by_cases h13 : 13 ≤ j <;>
        by_cases h28 : 28 ≤ j <;> by_cases h41 : 41 ≤ j <;>
        simp [emptyOrder, peak, emptyThresholds, orderFor, h13, h10, h28, h41, h7, hjs] at hchange
    · exact prices21 j hjs (by omega)
  · change 3 = b + 1 at hb
    change 7 ≤ j at hjs
    omega
  · change 4 = b + 1 at hb
    change 10 ≤ j at hjs
    omega
  · change 10 = b + 1 at hb
    change 28 ≤ j at hjs
    omega
private theorem peak_fits_index (b j : ℕ) : 3 * (peak b j).t ≤ j := by
  have h := min_le_right 10 (j / 3)
  change 3 * min 10 (j / 3) ≤ j
  omega
private theorem peak_bound (b j : ℕ) (hb : b ≤ 120) (hshape : j ≤ 3 * b)
    (hend : ∀ k ≤ 120, j ≤ 3 * k → endpoint k j →
      physicalPrice (peak k j) (emptyOrder (peak k j)) ≤ indexBudget zeroShape factorCap j) :
    physicalPrice (peak b j) (emptyOrder (peak b j)) ≤ indexBudget zeroShape factorCap j := by
  induction hb using Nat.decreasingInduction with
  | self => exact hend _ le_rfl hshape (Or.inl rfl)
  | of_succ b hb ih =>
    by_cases he : endpoint b j
    · exact hend b (by omega) hshape he
    · have horder : emptyOrder (peak b j) = emptyOrder (peak (b + 1) j) := by
        by_contra h
        exact he (Or.inr h)
      have hmono : InBox (peak b j) (peak (b + 1) j) :=
        ⟨Nat.le_succ b, le_rfl, le_rfl⟩
      rw [horder]
      exact (physical_mono hmono (peak_fits_index b j) (peak_fits_index (b + 1) j) _).trans
        (ih (by omega))
theorem proof : P3_6_8.c4 := by
  intro a ha hbox
  have hz : zeroShape.plus a = a := by
    cases a
    simp [zeroShape, Shape.plus]
  rw [hz] at hbox
  have hj : 3 ≤ a.j := (Nat.mul_le_mul_left 3 ha.1).trans ha.2.1
  have hmax : a.j ≤ 48 := hbox.2.1
  have ht : a.t ≤ (peak a.b a.j).t :=
    le_min hbox.2.2 ((Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr
      (by simpa [Nat.mul_comm] using ha.2.1))
  have hmono : InBox a (peak a.b a.j) := ⟨le_rfl, le_rfl, ht⟩
  have horder : emptyOrder a = emptyOrder (peak a.b a.j) := rfl
  rw [horder]
  exact (physical_mono hmono ha.2.1 (peak_fits_index a.b a.j) _).trans <|
    peak_bound _ _ hbox.1 ha.2.2 fun _ _ hvalid he =>
      endpoint_bound hj hmax hvalid he
end P3_6_8_4
end
section
namespace P3_6_8_5
open K1_13 (Shape)
open K1_13_8 (availableMass availableMass_eq_sum availableMass_mono fastRemaining
  remaining_anti)
open P0_9_8 (availableMass_anti_prefix oneOrder oneStart symbol_count)
open scoped BigOperators
private def capacity (j L k : ℕ) : ℕ :=
  fastRemaining (k + 1) ((k + 1) * 3 + (k + 1 - L) * j)
private theorem capacity_anti (j L : ℕ) : Antitone (capacity j L) := by
  intro a b hab
  simp only [capacity, ← symbol_count]
  exact remaining_anti (by omega) <|
    Nat.add_le_add (Nat.mul_le_mul_right 3 (by omega))
      (Nat.mul_le_mul_right j (by omega))
private def layerMass (j L s n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, capacity j L (s + k)
private theorem mass_eq (j L : ℕ) :
    availableMass oneStart ⟨0, j, 0⟩ L = layerMass j L 0 (L + 1650 / (3 + j)) := by
  have h := availableMass_eq_sum symbol_count (r := oneStart)
    (y := ⟨0, j, 0⟩) (L := L) (N := L + 1650 / (3 + j))
    (Or.inr (by decide)) (by change 0 < 3 + j; omega) le_rfl
  rw [← h]
  change (∑ k ∈ Finset.range _, K1_13.remaining
    ((k + 1) * 1 + (k + 1 - L) * 0) ((k + 1) * 3 + (k + 1 - L) * j)) = _
  simp only [layerMass, capacity, symbol_count, Nat.zero_add, Nat.mul_one, Nat.mul_zero,
    Nat.add_zero]
private theorem add_block (width count rest : ℕ) {j L s n cap : ℕ}
    (hw : width ≤ n) (hcount : capacity j L s ≤ count)
    (hrest : layerMass j L (s + width) (n - width) ≤ rest)
    (htotal : width * count + rest ≤ cap) : layerMass j L s n ≤ cap := by
  have hsplit : layerMass j L s n =
      layerMass j L s width + layerMass j L (s + width) (n - width) := by
    conv_lhs => rw [layerMass, ← Nat.add_sub_of_le hw, Finset.sum_range_add]
    simp only [layerMass, Nat.add_assoc]
  have hblock : layerMass j L s width ≤ width * count := by
    calc
      _ ≤ ∑ _k ∈ Finset.range width, count :=
        Finset.sum_le_sum fun k _ =>
          ((capacity_anti j L) (Nat.le_add_right s k)).trans hcount
      _ = _ := by simp
  rw [hsplit]
  exact (Nat.add_le_add hblock hrest).trans htotal
private theorem bounded_block (width rest : ℕ) {j L s n cap : ℕ}
    (hw : width ≤ n) (hr : rest ≤ cap)
    (hcount : capacity j L s ≤ (cap - rest) / width)
    (hrest : layerMass j L (s + width) (n - width) ≤ rest) :
    layerMass j L s n ≤ cap := by
  refine add_block width _ rest hw hcount hrest ?_
  calc
    width * ((cap - rest) / width) + rest ≤ (cap - rest) + rest := by
      rw [Nat.mul_comm width]
      exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
    _ = cap := Nat.sub_add_cancel hr
private theorem empty_block (j L s : ℕ) : layerMass j L s 0 ≤ 0 := by
  simp [layerMass]
local notation "row!" w "," r => bounded_block w r (by decide) (by decide) (by decide) ?_
private theorem r1 : layerMass 4 3 131 107 ≤ 0x108b57f4432 := by
  refine row! 2,0xf606e0869a
  refine row! 2,0xe45c710082
  refine row! 2,0xd3accaa896
  refine row! 2,0xc3eeaf70e4
  refine row! 2,0xb51909a270
  refine row! 2,0xa722ebffe0
  refine row! 2,0x9a03920494
  refine row! 2,0x8db260404a
  refine row! 2,0x8226e479ba
  refine row! 2,0x7758d5edae
  refine row! 3,0x6833b5893a
  refine row! 3,0x5a90380841
  refine row! 3,0x4e5458c4bb
  refine row! 3,0x4366eb3169
  refine row! 3,0x39af9c8f3f
  refine row! 3,0x3116f5f6b9
  refine row! 3,0x29865e0d18
  refine row! 3,0x22e81b0de4
  refine row! 3,0x1d27547ffc
  refine row! 4,0x1688557f08
  refine row! 4,0x112847da88
  refine row! 4,0xcdcd76ce4
  refine row! 5,0x8a701b358
  refine row! 5,0x5a3fa7dc8
  refine row! 6,0x329f54bd0
  refine row! 7,0x175dba83a
  refine row! 9,0x7121c420
  refine row! 16,0
  exact empty_block 4 3 238
private theorem r2 : layerMass 4 3 80 158 ≤ 0x4b9de13c07c := by
  refine row! 1,0x49c76301a94
  refine row! 1,0x47f988a2f55
  refine row! 1,0x463437dfd60
  refine row! 1,0x44775699a1c
  refine row! 1,0x42c2cad40ee
  refine row! 2,0x3f6a2a9330e
  refine row! 2,0x3c31ded5812
  refine row! 2,0x39191bf3ad8
  refine row! 2,0x361f186d1f4
  refine row! 2,0x33430cea2dc
  refine row! 2,0x30843440100
  refine row! 2,0x2de1cb768ee
  refine row! 2,0x2b5b11ca36e
  refine row! 2,0x28ef48b049a
  refine row! 2,0x269db3dc712
  refine row! 2,0x24659942f08
  refine row! 2,0x2246411c958
  refine row! 2,0x203ef5ec6cc
  refine row! 2,0x1e4f0481f18
  refine row! 2,0x1c75bbfcff2
  refine row! 2,0x1ab26dd3866
  refine row! 2,0x19046dd3bc2
  refine row! 2,0x176b12280ae
  refine row! 2,0x15e5b35cc90
  refine row! 2,0x1473ac62668
  refine row! 2,0x13145a915e8
  refine row! 2,0x11c71dafee8
  refine row! 2,0x108b57f4432
  exact r1
private theorem r3 : layerMass 4 3 52 186 ≤ 0x8e77971e912 := by
  refine row! 1,0x8b83867f45a
  refine row! 1,0x889b2bfaccc
  refine row! 1,0x85be69d8630
  refine row! 1,0x82ed227c624
  refine row! 1,0x8027386a0d8
  refine row! 1,0x7d6c8e42e0f
  refine row! 1,0x7abd06c6a44
  refine row! 1,0x781884d3974
  refine row! 1,0x757eeb6761a
  refine row! 1,0x72f01d9d850
  refine row! 1,0x706bfeb12a2
  refine row! 1,0x6df271fc700
  refine row! 1,0x6b835af87ea
  refine row! 1,0x691e9d3db33
  refine row! 1,0x66c41c8490c
  refine row! 1,0x6473bca430e
  refine row! 1,0x622d6194124
  refine row! 1,0x5ff0ef6b66e
  refine row! 1,0x5dbe4a61274
  refine row! 1,0x5b9556cc3e2
  refine row! 1,0x5975f9247a2
  refine row! 1,0x57601600fcf
  refine row! 1,0x5553921a0b6
  refine row! 1,0x535052485aa
  refine row! 1,0x51563b8523e
  refine row! 1,0x4f6532ea4fa
  refine row! 1,0x4d7d1db3684
  refine row! 1,0x4b9de13c07c
  exact r2
private theorem r4 : layerMass 4 3 24 214 ≤ 0xf5a1af5d002 := by
  refine row! 1,0xf134c1db31a
  refine row! 1,0xecd6f87d343
  refine row! 1,0xe888327160e
  refine row! 1,0xe4484f0098a
  refine row! 1,0xe0172d8e546
  refine row! 1,0xdbf4ad98d3e
  refine row! 1,0xd7e0aeba08c
  refine row! 1,0xd3db10a60fc
  refine row! 1,0xcfe3b32cf6c
  refine row! 1,0xcbfa763a109
  refine row! 1,0xc81f39d4058
  refine row! 1,0xc451de1d01c
  refine row! 1,0xc0924353a16
  refine row! 1,0xbce049d1682
  refine row! 1,0xb93bd20c88e
  refine row! 1,0xb5a4bc97388
  refine row! 1,0xb21aea1fbee
  refine row! 1,0xae9e3b70a4d
  refine row! 1,0xab2e9171a10
  refine row! 1,0xa7cbcd260e6
  refine row! 1,0xa475cfaeb50
  refine row! 1,0xa12c7a491c0
  refine row! 1,0x9defae4f9b0
  refine row! 1,0x9abf4d3987a
  refine row! 1,0x979b389c236
  refine row! 1,0x94835229109
  refine row! 1,0x91777bb01ca
  refine row! 1,0x8e77971e912
  exact r3
private theorem r5 : layerMass 4 3 0 238 ≤ 0x172d41020ede := by
  refine row! 1,0x16ce8ac83f02
  refine row! 2,0x161220b8c382
  refine row! 1,0x15b58d688852
  refine row! 1,0x155a18e0fd02
  refine row! 1,0x14ffc0f3d090
  refine row! 1,0x14a683743d98
  refine row! 1,0x144e5e36f244
  refine row! 1,0x13f74f122c50
  refine row! 1,0x13a153ddae83
  refine row! 1,0x134c6a72c19c
  refine row! 1,0x12f890ac3754
  refine row! 1,0x12a5c46678e2
  refine row! 1,0x1254037f6ed4
  refine row! 1,0x12034bd69d2a
  refine row! 1,0x11b39b4d18c0
  refine row! 1,0x1164efc58842
  refine row! 1,0x111747242727
  refine row! 1,0x10ca9f4ed444
  refine row! 1,0x107ef62cf98e
  refine row! 1,0x103449a7a84c
  refine row! 1,0xfea97a98e72
  refine row! 1,0xfa1de1ef79c
  refine row! 1,0xf5a1af5d002
  exact r4
private theorem check4 : availableMass oneStart ⟨0, 4, 0⟩ 3 < P3_6.layerNeed := by
  rw [mass_eq]
  exact r5.trans_lt (by decide)
private theorem r6 : layerMass 5 12 21 197 ≤ 0xfc94d38bb8a := by
  refine row! 4,0xe942a718b8a
  refine row! 4,0xd70fdd6605a
  refine row! 4,0xc5f1c16851a
  refine row! 4,0xb5ddc3e2e9a
  refine row! 4,0xa6c97c47dba
  refine row! 4,0x98aaa99b82a
  refine row! 4,0x8b77335b82a
  refine row! 4,0x7f252a5ee9a
  refine row! 4,0x73aac9b9bba
  refine row! 4,0x68fe77a3f3a
  refine row! 5,0x5c9cda070aa
  refine row! 5,0x515e3a54de4
  refine row! 5,0x4730f60b80e
  refine row! 5,0x3e03dd7638d
  refine row! 5,0x35c6365f96d
  refine row! 5,0x2e67becc424
  refine row! 6,0x2688dfdf440
  refine row! 6,0x1fbc82874c8
  refine row! 6,0x19e9474f49c
  refine row! 7,0x1423cf0ed1c
  refine row! 7,0xf6e392c1eb
  refine row! 8,0xb1b64dee2b
  refine row! 8,0x7d0bb84b1b
  refine row! 9,0x51357d5515
  refine row! 10,0x2ff1ccfc83
  refine row! 13,0x15832e1f1a
  refine row! 17,0x5ece882a2
  refine row! 30,0
  exact empty_block 5 12 218
private theorem r7 : layerMass 5 12 0 218 ≤ 0x17266bd8f19a := by
  refine row! 6,0x14ee267e1272
  refine row! 7,0x126c2e0827fa
  refine row! 4,0x111113cb1f7a
  refine row! 4,0xfc94d38bb8a
  exact r6
private theorem check5 : availableMass oneStart ⟨0, 5, 0⟩ 12 < P3_6.layerNeed := by
  rw [mass_eq]
  exact r7.trans_lt (by decide)
private theorem r8 : layerMass 11 42 0 159 ≤ 0x172a52eb7916 := by
  refine row! 8,0x1434a11cfa36
  refine row! 9,0x11041e413266
  refine row! 9,0xdfacb5677f2
  refine row! 9,0xb1768fe7f6d
  refine row! 9,0x858bc8dc6ef
  refine row! 4,0x741d8df043f
  refine row! 4,0x647afd7fbfb
  refine row! 5,0x5307ffdfa15
  refine row! 5,0x43febbe0985
  refine row! 5,0x372699342ae
  refine row! 5,0x2c49058aa3b
  refine row! 6,0x2160149902d
  refine row! 6,0x18b5d85e2e5
  refine row! 7,0x10d900ae028
  refine row! 8,0xa5aef8b590
  refine row! 9,0x5936f4df95
  refine row! 10,0x290cde946f
  refine row! 14,0xab5e592c1
  refine row! 27,0
  exact empty_block 11 42 159
private theorem check11 : availableMass oneStart ⟨0, 11, 0⟩ 42 < P3_6.layerNeed := by
  rw [mass_eq]
  exact r8.trans_lt (by decide)
private theorem r9 : layerMass 31 64 0 112 ≤ 0x172d4213e81f := by
  refine row! 5,0x1553b2f2d8d3
  refine row! 5,0x1386ab457b78
  refine row! 5,0x11c5f3377813
  refine row! 5,0x1011536609ef
  refine row! 5,0xe6894e09061
  refine row! 5,0xccb8128a2c3
  refine row! 5,0xb39e232a151
  refine row! 5,0x9b38265c90b
  refine row! 6,0x7ec4ea7c3cb
  refine row! 6,0x634acf44ce7
  refine row! 6,0x48c432d9903
  refine row! 6,0x2f2b8272a05
  refine row! 2,0x276bb23a419
  refine row! 2,0x20aaed34595
  refine row! 2,0x1ad3ce44333
  refine row! 2,0x15d19390293
  refine row! 2,0x11902a2af4b
  refine row! 2,0xdfc39bebe9
  refine row! 2,0xb033034b8d
  refine row! 2,0x8934d5e6f9
  refine row! 3,0x59fdf4219a
  refine row! 3,0x38e8f1b5e4
  refine row! 4,0x1b8f82d9f0
  refine row! 4,0xc4cc04b68
  refine row! 6,0x27f973ea8
  refine row! 12,0
  exact empty_block 31 64 112
private theorem check31 : availableMass oneStart ⟨0, 31, 0⟩ 64 < P3_6.layerNeed := by
  rw [mass_eq]
  exact r9.trans_lt (by decide)
private theorem check_interval {j lo L : ℕ} (hj : lo ≤ j)
    (hL : oneOrder ⟨0, j, 0⟩ - 1 ≤ L)
    (hcheck : availableMass oneStart ⟨0, lo, 0⟩ L < P3_6.layerNeed) :
    availableMass oneStart ⟨0, j, 0⟩ (oneOrder ⟨0, j, 0⟩ - 1) < P3_6.layerNeed := by
  have hstart : oneStart = K1_13_8.zeroShape ∨ 0 < oneStart.j := Or.inr (by decide)
  have hindex : 0 < oneStart.j + (⟨0, lo, 0⟩ : Shape).j := by
    change 0 < 3 + lo
    omega
  calc
    availableMass oneStart ⟨0, j, 0⟩ (oneOrder ⟨0, j, 0⟩ - 1) ≤
        availableMass oneStart ⟨0, lo, 0⟩ (oneOrder ⟨0, j, 0⟩ - 1) :=
      availableMass_anti_prefix hstart hindex (Nat.zero_le 0) hj
    _ ≤ availableMass oneStart ⟨0, lo, 0⟩ L :=
      availableMass_mono symbol_count hstart hindex hL
    _ < P3_6.layerNeed := hcheck
theorem proof : P3_6_8.c5 := by
  intro j hj4 hj45
  have horder : oneOrder ⟨0, j, 0⟩ - 1 = (3 * j - 4) / 2 - 1 := by
    have hj : ¬ j ≤ 3 := by omega
    simp only [oneOrder, ite_eq_right hj]
  by_cases hj4' : j ≤ 4
  · exact check_interval hj4 (by rw [horder]; omega) check4
  by_cases hj10 : j ≤ 10
  · exact check_interval (by omega) (by rw [horder]; omega) check5
  by_cases hj30 : j ≤ 30
  · exact check_interval (by omega) (by rw [horder]; omega) check11
  exact check_interval (by omega) (by rw [horder]; omega) check31
end P3_6_8_5
end
section
namespace P3_6_8_6
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
open P0_9_8 (oneStart oneOrder indexBudget)
open P0_9_8_5 (ceil_mono)
open P3_6 (physicalPrice physicalDegree incidenceGap primaryBox taylorLength surfaceNumerator32)
open P3_6_8 (oneReserve)
open private P0_9_8_5.box_refl P0_9_8_5.normalize_mono P0_9_8_5.normalize_chamber P0_9_8_5.plus_mono P0_9_8_5.plus_chamber P0_9_8_5.scale_mono
  P0_9_8_5.scale_chamber P0_9_8_5.chart_chamber P0_9_8_5.lifted_chamber P0_9_8_5.chart_mono P0_9_8_5.lifted_mono P0_9_8_5.graphShape P0_9_8_5.graph_chamber
  P0_9_8_5.graph_mono from ProximityPrize.SubmissionLower.PortLow8
private theorem surface_mono {p p' q : Shape} (hp : InBox p p') (hp' : Chamber p') (hq : Chamber q) :
    surfaceNumerator32 p q ≤ surfaceNumerator32 p' q := by
  let L := taylorLength
  have hchart : mixed32 p q (chart (L+1) p) (chart (L+2) p) ≤
      mixed32 p' q (chart (L+1) p') (chart (L+2) p') :=
    mixed_mono hp (P0_9_8_5.box_refl q) (P0_9_8_5.chart_mono _ hp) (P0_9_8_5.chart_mono _ hp) hp' hq
      (P0_9_8_5.chart_chamber _ _) hq (P0_9_8_5.chart_chamber _ _) (P0_9_8_5.chart_chamber _ _)
  have hlift : mixed32 p q (liftedChart (L+1) p) (liftedChart (L+2) p) ≤
      mixed32 p' q (liftedChart (L+1) p') (liftedChart (L+2) p') :=
    mixed_mono hp (P0_9_8_5.box_refl q) (P0_9_8_5.lifted_mono _ hp) (P0_9_8_5.lifted_mono _ hp) hp' hq
      (P0_9_8_5.lifted_chamber _ _) hq (P0_9_8_5.lifted_chamber _ _) (P0_9_8_5.lifted_chamber _ _)
  have hgraph (M : ℕ) :
      mixed32 p q (P0_9_8_5.graphShape p) (liftedChart M p) ≤ mixed32 p' q (P0_9_8_5.graphShape p') (liftedChart M p') :=
    mixed_mono hp (P0_9_8_5.box_refl q) (P0_9_8_5.graph_mono hp) (P0_9_8_5.lifted_mono _ hp) hp' hq
      (P0_9_8_5.graph_chamber _) hq (P0_9_8_5.graph_chamber _) (P0_9_8_5.lifted_chamber _ _)
  exact min_le_min hchart (Nat.add_le_add (Nat.add_le_add hlift (Nat.mul_le_mul_left _ (hgraph _)))
    (Nat.mul_le_mul_left _ (hgraph _)))
private theorem physical_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l : ℕ) : physicalPrice x l ≤ physicalPrice y l := by
  let p := x.chamber
  let p' := y.chamber
  let q := primaryBox
  let L := taylorLength
  let A := q.plus (p.scale 4)
  let A' := q.plus (p'.scale 4)
  have hp := P0_9_8_5.normalize_mono h
  have hpc : Chamber p := P0_9_8_5.normalize_chamber x hx
  have hp'c : Chamber p' := P0_9_8_5.normalize_chamber y hy
  have hqc : Chamber q := by dsimp [Chamber, q]; omega
  have ha : InBox A A' := P0_9_8_5.plus_mono (P0_9_8_5.box_refl q) (P0_9_8_5.scale_mono hp 4)
  have hac : Chamber A := P0_9_8_5.plus_chamber hqc (P0_9_8_5.scale_chamber hpc 4)
  have ha'c : Chamber A' := P0_9_8_5.plus_chamber hqc (P0_9_8_5.scale_chamber hp'c 4)
  have hs := surface_mono hp hp'c hqc
  have hb := (P0_9_8_5.chart_mono (L+1) hp).1
  have hmain : (P3.t + 2*incidenceGap) * x.b * q.b * (chart (L+1) p).b ≤
      (P3.t + 2*incidenceGap) * y.b * q.b * (chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (P0_9_8_5.box_refl q) ha (P0_9_8_5.chart_mono L hp) hp'c hqc ha'c hqc hac (P0_9_8_5.chart_chamber L p)
  have hpoint := mixed_mono hp (P0_9_8_5.box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (P0_9_8_5.chart_mono L hp) hp'c hp'c hp'c hpc hpc (P0_9_8_5.chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left P3.t hc) (Nat.mul_le_mul_left (2*incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (ceil_mono (Nat.add_le_add (ceil_mono hs _) (ceil_mono hmain _)) l) hraw)
    (ceil_mono hgeom _)
private def peak (j : ℕ) : Shape := ⟨119, j, min 9 (j / 3)⟩
private def budget (j : ℕ) : ℕ := indexBudget oneStart (P3_6.factorCap - oneReserve) j
private abbrev PeakBound (j : ℕ) : Prop :=
  physicalPrice (peak j) (oneOrder (peak j)) ≤ budget j
private def mainFee (x : Shape) : ℕ :=
  ceilDiv (surfaceNumerator32 x.chamber primaryBox) 32 +
    ceilDiv ((P3.t + 2 * incidenceGap) * x.b * primaryBox.b *
      (chart (taylorLength + 1) x.chamber).b) incidenceGap
private def auxFee (x : Shape) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let z := q.plus (p.scale 4)
  let curves := mixed32 p q z h + 2 * x.t * mixed32 p p p h
  let points := mixed32 p q z p + 2 * x.t * mixed32 p p p p
  2 * physicalDegree * x.b * q.b +
    ceilDiv (P3.t * curves + 2 * incidenceGap * points) (32 * incidenceGap)
private theorem price_eq (x : Shape) (l : ℕ) :
    physicalPrice x l = ceilDiv (mainFee x) l + auxFee x := by
  simp only [physicalPrice, mainFee, auxFee, Nat.add_assoc]
private theorem row (j l main aux fee allowance : ℕ)
    (horder : oneOrder (peak j) = l) (hmain : mainFee (peak j) = main)
    (haux : auxFee (peak j) = aux) (hfee : ceilDiv main l + aux = fee)
    (hbudget : budget j = allowance) (hle : fee ≤ allowance) : PeakBound j := by
  change physicalPrice (peak j) (oneOrder (peak j)) ≤ budget j
  rw [price_eq, horder, hmain, haux, hfee, hbudget]
  exact hle
local notation "paid[" j "," l "," main "," aux "," fee "," cap "]" =>
  row j l main aux fee cap rfl rfl rfl rfl rfl (by decide)
section
set_option maxRecDepth 4096
private theorem r3 : PeakBound 3 := paid[3,1,0x1ae6262a3cb05a, 0x51d65f62f40e, 0x1b37fc899fa468,0x306168c3143949]
private theorem r4 : PeakBound 4 := paid[4,4,0x7593fa7616cb48,0x835476f8e7dc, 0x1de853147e9aae, 0x4081e1041af70c]
private theorem r5 : PeakBound 5 := paid[5,5,0x101e275272538a8,0xb6559adc75be, 0x344a06a2b0b446,0x50a2594521b4cf]
private theorem r6 : PeakBound 6 := paid[6,7,0x1c0f162320f6b12,0xeae01d537417,0x410d5bdb55a7f5,0x60c2d186287292]
private theorem r7 : PeakBound 7 := paid[7,8,0x2b220a74d64b9fe, 0x120edeae8c2d7,0x576502d4955a17,0x70e349c72f3055]
private theorem r8 : PeakBound 8 := paid[8,10,0x3d5b01d4ec08a74,0x15880e832f85a, 0x6383b709ac9fcc, 0x8103c20835ee18]
private theorem r9 : PeakBound 9 := paid[9,11,0x5104baca853b90c, 0x191a6e2bb88cc, 0x7769fc66660dfc, 0x91243a493cabdb]
private theorem r10 : PeakBound 10 := paid[10,13,0x65ef55b3a48c5d8,0x1cc4d7873bb8b, 0x7f41a341dbcac3,0xa144b28a43699e]
private theorem r11 : PeakBound 11 := paid[11,14,0x7d47000ebb11a5d, 0x2087bea21f295,0x91350e441c4fe5,0xb1652acb4a2761]
private theorem r12 : PeakBound 12 := paid[12,16,0x970eb7fa4586932,0x2464ece3dc4e5,0x995506c8834b79,0xc185a30c50e524]
private theorem r13 : PeakBound 13 := paid[13,17,0xb3497b9678e77b4,0x285999f020827,0xab433b1d91f114,0xd1a61b4d57a2e7]
private theorem r14 : PeakBound 14 := paid[14,19,0xd1fa49054274698,0x2c66f75c06809,0xb39933b01350ce, 0xe1c6938e5e60aa]
private theorem r15 : PeakBound 15 := paid[15,20,0xf3241e651ee8875,0x30905604ec6cf, 0xc58c50e46780d5,0xf1e70bcf651e6e]
private theorem r16 : PeakBound 16 := paid[16,22,0x116c9f9d643402a8,0x34d021372925e, 0xce0e71f517d84f, 0x1020784106bdc31]
private theorem r17 : PeakBound 17 := paid[17,23,0x13ceed97a9cbb5e6,0x3928d6940b7a3,0xe00c2fd4cf23b9,0x11227fc517299f4]
private theorem r18 : PeakBound 18 := paid[18,25,0x16595bb70a8154c6,0x3da00d4deadfb, 0xe8b4b63bb0a722,0x1224874927957b7]
private theorem r19 : PeakBound 19 := paid[19,26,0x190c19dd89a4a4a5,0x422bf19c46cb7,0xfac1479f0fae20,0x13268ecd380157a]
private theorem r20 : PeakBound 20 := paid[20,28,0x1be757ed4609a638,0x46d10059a10f6,0x1038ba1a388200b, 0x14289651486d33d]
private theorem r21 : PeakBound 21 := paid[21,29,0x1eeb45c8277c0c16,0x4b97f7d029029,0x115aa3fc4fe0356,0x152a9dd558d9100]
private theorem r22 : PeakBound 22 := paid[22,31,0x22181350314b9b9c, 0x50710dec047dd, 0x11e941374fc86b1,0x162ca5596944ec3]
private theorem r23 : PeakBound 23 := paid[23,32,0x256df067824c557f, 0x556394831e98a, 0x130c5bc84444c36,0x172eacdd79b0c86]
private theorem r24 : PeakBound 24 := paid[24,34,0x28ed0cf00249ec56,0x5a7c7189deebe, 0x139cdce27be3976,0x1830b4618a1ca49]
private theorem r25 : PeakBound 25 := paid[25,35,0x2c9598cbb494257e, 0x5fa3ed1a1e7ed, 0x14c148dc829cbbe, 0x1932bbe59a8880c]
private theorem r26 : PeakBound 26 := paid[26,37,0x3067c3dcb7ff01ac, 0x64e5244857228,0x15537f07301f5aa, 0x1a34c369aaf45cf]
private theorem r27 : PeakBound 27 := paid[27,38,0x3463be04f4563377,0x6a524300c2c0c, 0x16795ee6c5f485a, 0x1b36caedbb60392]
private theorem r28 : PeakBound 28 := paid[28,40,0x3889b7266ce9803c, 0x6fc96fdc199c3,0x170d45e5a143cf8,0x1c38d271cbcc155]
private theorem r29 : PeakBound 29 := paid[29,41,0x3cd9df23408ce8b0,0x755aa7dd30c2a, 0x18348606caac6ea, 0x1d3ad9f5dc37f18]
private theorem r30 : PeakBound 30 := paid[30,43,0x415411e3aca071d3,0x7b05d4a7fc8f8,0x18c9eeb84185a80,0x1e3ce179eca3cdc]
private theorem r31 : PeakBound 31 := paid[31,44,0x45f7bb575fcf8f6d, 0x80cadfe0715e2,0x19f2264577a5925,0x1f3ee8fdfd0fa9f]
private theorem r32 : PeakBound 32 := paid[32,46,0x4ac4636c2c72b7c5,0x86a9b32a8389c, 0x1a8830749e25dff, 0x2040f0820d7b862]
private theorem r33 : PeakBound 33 := paid[33,47,0x4fb9920fe4e26ea8,0x8ca2382a276dc, 0x1bb09294b96f10c, 0x2142f8061de7625]
private theorem r34 : PeakBound 34 := paid[34,49,0x54d6cf305b7737e3,0x92b4588351656,0x1c468f826cf07ce, 0x2244ff8a2e533e8]
private theorem r35 : PeakBound 35 := paid[35,50,0x5a1ba2bb62899743,0x98dffdd9f5cc0,0x1d6e84b4b1cfe7f, 0x2347070e3ebf1ab]
private theorem r36 : PeakBound 36 := paid[36,52,0x5f87949ecc721095,0x9f2511d208fce, 0x1e03f0565fb5ee5,0x24490e924f2af6e]
private theorem r37 : PeakBound 37 := paid[37,53,0x651a2cc86b8927a6,0xa5837e0f7f536,0x1f2b001b2b217c6,0x254b16165f96d31]
private theorem r38 : PeakBound 38 := paid[38,55,0x6ad2f32612276043,0xabfb2c364d2ad, 0x1fbf751b5c2a13a, 0x264d1d9a7002af4]
private theorem r39 : PeakBound 39 := paid[39,56,0x70b16fa592a53e39,0xb28c05ea66de8,0x20e53e3538df397,0x274f251e806e8b7]
private theorem r40 : PeakBound 40 := paid[40,58,0x76b52a34bf5b4555,0xb935f4cfc0c9b, 0x21786dbcbdeb9f1,0x28512ca290da67a]
private theorem r41 : PeakBound 41 := paid[41,59,0x7cddaac16aa1f964,0xbff8e28a4f47c, 0x229ca0aedb4b7a1,0x29533426a14643d]
private theorem r42 : PeakBound 42 := paid[42,61,0x832a793966d1de33,0xc6d4b8be06b40,0x232e4ca63985184,0x2a553baab1b2200]
private theorem r43 : PeakBound 43 := paid[43,62,0x899b1d8a8643778f, 0xcdc9610edb69c, 0x2450a7b65acbcab, 0x2b57432ec21dfc3]
private theorem r44 : PeakBound 44 := paid[44,64,0x902f1fa29b4f4945,0xd4d6c520c1c45,0x24e09eadc79596b, 0x2c594ab2d289d86]
private theorem r45 : PeakBound 45 := paid[45,65,0x96e6076f784dd722,0xdbfcce97ae1ef, 0x2600eaf1e87e53f, 0x2d5b5236e2f5b4a]
private theorem prices_at_cap (j : Fin 43) : PeakBound (j.val + 3) := by
  fin_cases j
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10
  · exact r11
  · exact r12
  · exact r13
  · exact r14
  · exact r15
  · exact r16
  · exact r17
  · exact r18
  · exact r19
  · exact r20
  · exact r21
  · exact r22
  · exact r23
  · exact r24
  · exact r25
  · exact r26
  · exact r27
  · exact r28
  · exact r29
  · exact r30
  · exact r31
  · exact r32
  · exact r33
  · exact r34
  · exact r35
  · exact r36
  · exact r37
  · exact r38
  · exact r39
  · exact r40
  · exact r41
  · exact r42
  · exact r43
  · exact r44
  · exact r45
end
theorem proof : P3_6_8.c6 := by
  intro a ha hbox
  have hb : 1 + a.b ≤ 120 := hbox.1
  have hj : 3 + a.j ≤ 48 := hbox.2.1
  have ht : 1 + a.t ≤ 10 := hbox.2.2
  have haPos : 1 ≤ a.t := ha.1
  have haIndex : 3 * a.t ≤ a.j := ha.2.1
  have hpeak : InBox a (peak a.j) :=
    ⟨by change a.b ≤ 119; omega, le_rfl,
      le_min (by omega : a.t ≤ 9) (by omega : a.t ≤ a.j / 3)⟩
  have hpeakIndex : 3 * (peak a.j).t ≤ (peak a.j).j := by
    change 3 * min 9 (a.j / 3) ≤ a.j
    have := min_le_right 9 (a.j / 3)
    omega
  let j : Fin 43 := ⟨a.j - 3, by omega⟩
  have hj_eq : j.val + 3 = a.j := by dsimp [j]; omega
  have hprice := prices_at_cap j
  rw [hj_eq] at hprice
  exact (physical_mono hpeak haIndex hpeakIndex (oneOrder a)).trans hprice
end P3_6_8_6
end
section
namespace P3_6_8_7
open K1_13_8 (availableMass fastRemaining fastRemaining_zero sum_range_truncate)
open P0_9_8 (twoStart)
open P3_6_8 (twoOrder)
open scoped BigOperators
private def retainedTerm (k : ℕ) : ℕ :=
  fastRemaining ((k + 1) * 2) ((k + 1) * 6)
private def tailTerm (k : ℕ) : ℕ :=
  fastRemaining (142 + (k + 1) * 2) (426 + (k + 1) * 9)
private abbrev sumTerms (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, f k
private theorem sumStep {f : ℕ → ℕ} {n total : ℕ}
    (hsum : sumTerms f n = total) (row : ℕ) (hrow : f n = row) :
    sumTerms f (n + 1) = total + row := by
  unfold sumTerms at hsum ⊢
  rw [Finset.sum_range_succ, hsum, hrow]
private theorem tail_zero {k : ℕ} (hk : 136 ≤ k) : tailTerm k = 0 := by
  unfold tailTerm
  exact fastRemaining_zero (by omega)
private theorem mass_eq :
    availableMass twoStart ⟨0, 3, 0⟩ (twoOrder - 1) =
      sumTerms retainedTerm 71 + sumTerms tailTerm 136 := by
  have htrim : sumTerms tailTerm 183 = sumTerms tailTerm 136 :=
    sum_range_truncate (f := tailTerm) (fun _ hk => tail_zero hk) (by decide)
  rw [← htrim]
  simp only [availableMass, twoOrder, sumTerms, retainedTerm, tailTerm,
    show ¬ (6 : ℕ) = 0 by decide, ite_false,
    show (72 - 1 : ℕ) = 71 by decide,
    show min 71 (1650 / 6) = (71 : ℕ) by decide,
    show (6 + 3 : ℕ) = 9 by decide, show (1650 / 9 : ℕ) = 183 by decide,
    show (71 * 2 : ℕ) = 142 by decide, show (71 * 6 : ℕ) = 426 by decide,
    Nat.add_zero]
local notation:65 h:65 " ▷ " v:66 => sumStep h v (by decide)
private theorem r0 : sumTerms retainedTerm 0 = 0 := Finset.sum_range_zero _
private theorem t0 : sumTerms tailTerm 0 = 0 := Finset.sum_range_zero _
private theorem r8 : sumTerms retainedTerm 8 = 0x2d5eefda29e :=
  r0 ▷ 0x5e3507bdc0 ▷ 0x5d33fc9a1e ▷ 0x5c34bc45df ▷ 0x5b37454d30
    ▷ 0x5a3b963bd2 ▷ 0x5941ad9d1a ▷ 0x584989fbf1 ▷ 0x575329e2d4
private theorem r16 : sumTerms retainedTerm 16 = 0x56eb48e2dcc :=
  r8 ▷ 0x565e8bdbd4 ▷ 0x556bae7096 ▷ 0x547a902a53 ▷ 0x538b2f91d8
    ▷ 0x529d8b2f86 ▷ 0x51b1a18b52 ▷ 0x50c7712cc5 ▷ 0x4fdef89afc
private theorem r24 : sumTerms retainedTerm 24 = 0x7cdc79f5e8a :=
  r16 ▷ 0x4ef8365ca8 ▷ 0x4e1328f80e ▷ 0x4d2fcef307 ▷ 0x4c4e26d300
    ▷ 0x4b6e2f1cfa ▷ 0x4a8fe6558a ▷ 0x49b34b00d9 ▷ 0x48d85ba2a4
private theorem r32 : sumTerms retainedTerm 32 = 0x9f6878341d8 :=
  r24 ▷ 0x47ff16be3c ▷ 0x47277ad686 ▷ 0x4651866dfb ▷ 0x457d3806a8
    ▷ 0x44aa8e222e ▷ 0x43d98741c2 ▷ 0x430a21e62d ▷ 0x423c5c8fcc
private theorem r40 : sumTerms retainedTerm 40 = 0xbec3bba34b6 :=
  r32 ▷ 0x417035be90 ▷ 0x40a5abf1fe ▷ 0x3fdcbda92f ▷ 0x3f156962d0
    ▷ 0x3e4fad9d22 ▷ 0x3d8b88d5fa ▷ 0x3cc8f98ac1 ▷ 0x3c07fe3874
private theorem r48 : sumTerms retainedTerm 48 = 0xdb213bce424 :=
  r40 ▷ 0x3b48955ba4 ▷ 0x3a8abd7076 ▷ 0x39ce74f2a3 ▷ 0x3913ba5d78
    ▷ 0x385a8c2bd6 ▷ 0x37a2e8d832 ▷ 0x36eccedc95 ▷ 0x36383cb29c
private theorem r56 : sumTerms retainedTerm 56 = 0xf4b26c64d22 :=
  r48 ▷ 0x358530d378 ▷ 0x34d3a9b7ee ▷ 0x3423a5d857 ▷ 0x337523aca0
    ▷ 0x32c821ac4a ▷ 0x321c9e4e6a ▷ 0x31729809a9 ▷ 0x30ca0d5444
private theorem r64 : sumTerms retainedTerm 64 = 0x10ba739dbcb0 :=
  r56 ▷ 0x3022fca40c ▷ 0x2f7d646e66 ▷ 0x2ed943284b ▷ 0x2e36974648
    ▷ 0x2d955f3c7e ▷ 0x2cf5997ea2 ▷ 0x2c57447ffd ▷ 0x2bba5eb36c
private theorem r71 : sumTerms retainedTerm 71 = 0x11dbda4829ba :=
  r64 ▷ 0x2b1ee68b60 ▷ 0x2a84da79de ▷ 0x29ec38f07f ▷ 0x2955006070
    ▷ 0x28bf2f3a72 ▷ 0x282ac3eeda ▷ 0x2797bced91
private theorem t8 : sumTerms tailTerm 8 = 0x11f7a8f6fe4 :=
  t0 ▷ 0x26c0c9dae6 ▷ 0x25eccde84c ▷ 0x251bc48318 ▷ 0x244da92156
    ▷ 0x2382772847 ▷ 0x22ba2a05e8 ▷ 0x21f4bd1766 ▷ 0x21322bc2af
private theorem t16 : sumTerms tailTerm 16 = 0x20f00689db8 :=
  t8 ▷ 0x2072715cdc ▷ 0x1fb58943cc ▷ 0x1efb6ec484 ▷ 0x1e441d34d4
    ▷ 0x1d8f8fd9ad ▷ 0x1cddc200d0 ▷ 0x1c2eaee71a ▷ 0x1b8251d23d
private theorem t24 : sumTerms tailTerm 24 = 0x2d41503d43c :=
  t16 ▷ 0x1ad8a5f702 ▷ 0x1a31a6930c ▷ 0x198d4ed310 ▷ 0x18eb99eca2
    ▷ 0x184c830463 ▷ 0x17b00547d8 ▷ 0x17161bd38e ▷ 0x167ec1ccfb
private theorem t32 : sumTerms tailTerm 32 = 0x373ef4c6e30 :=
  t24 ▷ 0x15e9f24898 ▷ 0x1557a863cc ▷ 0x14c7df2afc ▷ 0x143a91b380
    ▷ 0x13afbb01a9 ▷ 0x13275622c0 ▷ 0x12a15e1302 ▷ 0x121dcdd7a9
private theorem t40 : sumTerms tailTerm 40 = 0x3f3779c7654 :=
  t32 ▷ 0x119ca064de ▷ 0x111dd0b7cc ▷ 0x10a159bc88 ▷ 0x102736682e
    ▷ 0xfaf619ebf ▷ 0xf39d64d48 ▷ 0xec68f4fb6 ▷ 0xe55878b07
private theorem t48 : sumTerms tailTerm 48 = 0x45745b84768 :=
  t40 ▷ 0xde6b9d314 ▷ 0xd7a2104cc ▷ 0xd0fb7ebf4 ▷ 0xca7795d6c
    ▷ 0xc41601ce5 ▷ 0xbdd66f730 ▷ 0xb7b88a7ea ▷ 0xb1bbff3d5
private theorem t56 : sumTerms tailTerm 56 = 0x4a39eca2c2c :=
  t48 ▷ 0xabe078e7a ▷ 0xa625a348c ▷ 0xa08b29180 ▷ 0x9b10b59fa
    ▷ 0x95b5f315b ▷ 0x907a8c438 ▷ 0x8b5e2adde ▷ 0x8660792d3
private theorem t64 : sumTerms tailTerm 64 = 0x4dc735dff60 :=
  t56 ▷ 0x818120650 ▷ 0x7cbfca4cc ▷ 0x781c1f96c ▷ 0x7395c9898
    ▷ 0x6f2c70561 ▷ 0x6adfbcc20 ▷ 0x66af567d2 ▷ 0x629ae5cc1
private theorem t72 : sumTerms tailTerm 72 = 0x5055d5ccbc4 :=
  t64 ▷ 0x5ea211dd6 ▷ 0x5ac48274c ▷ 0x5701de3f8 ▷ 0x5359cc806
    ▷ 0x4fcbf3637 ▷ 0x4c57f9aa8 ▷ 0x48fd85006 ▷ 0x45bc3ba5f
private theorem t80 : sumTerms tailTerm 80 = 0x5219e086c18 :=
  t72 ▷ 0x4293c2c4c ▷ 0x3f83c01cc ▷ 0x3c8bd8564 ▷ 0x39abb0b04
    ▷ 0x36e2ed51d ▷ 0x343132f90 ▷ 0x3196254ba ▷ 0x2f116886d
private theorem t88 : sumTerms tailTerm 88 = 0x5341bf72b1c :=
  t80 ▷ 0x2ca29fcf2 ▷ 0x2a496ee0c ▷ 0x2805785f0 ▷ 0x25d65f852
    ▷ 0x23bbc6753 ▷ 0x21b54fe98 ▷ 0x1fc29d82e ▷ 0x1de3517ab
private theorem t96 : sumTerms tailTerm 96 = 0x53f610f6390 :=
  t88 ▷ 0x1c170cf08 ▷ 0x1a5d719cc ▷ 0x18b6201dc ▷ 0x1720b9ab0
    ▷ 0x159cde619 ▷ 0x142a2ef80 ▷ 0x12c84b0a2 ▷ 0x1176d2cd9
private theorem t104 : sumTerms tailTerm 104 = 0x54598832034 :=
  t96 ▷ 0x1035655ce ▷ 0xf03a26cc ▷ 0xde128968 ▷ 0xccd970de
    ▷ 0xbc88beaf ▷ 0xad1a5e08 ▷ 0x9e882856 ▷ 0x90cc00b7
private theorem t112 : sumTerms tailTerm 112 = 0x5488ccbbbc8 :=
  t104 ▷ 0x83dfb884 ▷ 0x77bd2acc ▷ 0x6c5e20d4 ▷ 0x61bc6d9c
    ▷ 0x57d1d255 ▷ 0x4e9819f0 ▷ 0x4608fd8a ▷ 0x3e1e4005
private theorem t120 : sumTerms tailTerm 120 = 0x549a5a5810c :=
  t112 ▷ 0x36d1926a ▷ 0x301caf8c ▷ 0x29f94060 ▷ 0x2460f7aa
    ▷ 0x1f4d764b ▷ 0x1ab866f8 ▷ 0x169b627e ▷ 0x12f00b83
private theorem t128 : sumTerms tailTerm 128 = 0x549e60b4ac0 :=
  t120 ▷ 0xfaff2c0 ▷ 0xcd4b2cc ▷ 0xa57d44c ▷ 0x832e9c8
    ▷ 0x65f73d1 ▷ 81198304 ▷ 59964786 ▷ 42792945
private theorem t136 : sumTerms tailTerm 136 = 0x549ea3223a4 :=
  t128 ▷ 29252806 ▷ 18916940 ▷ 11353304 ▷ 6132406
    ▷ 2820135 ▷ 984936 ▷ 190630 ▷ 3599
theorem proof : P3_6_8.c7 := by
  unfold P3_6_8.c7
  rw [mass_eq, r71, t136]
  change 0x11dbda4829ba + 0x549ea3223a4 < 0x172dd72ade84
  decide
end P3_6_8_7
end
section
namespace P3_6_8_8
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
private theorem box_refl (x : Shape) : InBox x x := ⟨le_rfl, le_rfl, le_rfl⟩
private theorem normalize_mono {x y : Shape} (h : InBox x y) :
    InBox x.chamber y.chamber := ⟨max_le_max h.1 h.2.1, h.2.1, h.2.2⟩
private theorem normalize_chamber (x : Shape) (h : 3 * x.t ≤ x.j) :
    Chamber x.chamber := ⟨le_max_right _ _, h⟩
private theorem plus_mono {x y u v : Shape} (h : InBox x y) (h' : InBox u v) :
    InBox (x.plus u) (y.plus v) :=
  ⟨Nat.add_le_add h.1 h'.1, Nat.add_le_add h.2.1 h'.2.1, Nat.add_le_add h.2.2 h'.2.2⟩
private theorem plus_chamber {x y : Shape} (hx : Chamber x) (hy : Chamber y) :
    Chamber (x.plus y) := by
  exact ⟨Nat.add_le_add hx.1 hy.1, by simp only [Shape.plus, Nat.mul_add]; exact Nat.add_le_add hx.2 hy.2⟩
private theorem scale_mono {x y : Shape} (h : InBox x y) (k : ℕ) :
    InBox (x.scale k) (y.scale k) :=
  ⟨Nat.mul_le_mul_left k h.1, Nat.mul_le_mul_left k h.2.1, Nat.mul_le_mul_left k h.2.2⟩
private theorem scale_chamber {x : Shape} (hx : Chamber x) (k : ℕ) :
    Chamber (x.scale k) :=
  ⟨Nat.mul_le_mul_left k hx.1, by simpa [Shape.scale, Nat.mul_left_comm 3 k] using Nat.mul_le_mul_left k hx.2⟩
private theorem min_fits_index (a i : ℕ) : 3 * min a (i / 3) ≤ i := by
  have h := min_le_right a (i / 3)
  omega
private theorem chart_chamber (L : ℕ) (x : Shape) : Chamber (chart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
private theorem lifted_chamber (L : ℕ) (x : Shape) : Chamber (liftedChart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
private theorem chart_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
    InBox (chart L x) (chart L y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [chart] <;> gcongr
private theorem lifted_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
    InBox (liftedChart L x) (liftedChart L y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [liftedChart] <;> gcongr
private def graphShape (p : Shape) : Shape :=
  ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
private theorem graph_chamber (x : Shape) : Chamber (graphShape x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
private theorem graph_mono {x y : Shape} (h : InBox x y) :
    InBox (graphShape x) (graphShape y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [graphShape] <;> gcongr
private theorem surface_mono {p p' q : Shape} (hp : InBox p p') (hp' : Chamber p') (hq : Chamber q) :
    P3_6.surfaceNumerator32 p q ≤ P3_6.surfaceNumerator32 p' q := by
  let L := P3_6.taylorLength
  have hchart : mixed32 p q (chart (L+1) p) (chart (L+2) p) ≤
      mixed32 p' q (chart (L+1) p') (chart (L+2) p') :=
    mixed_mono hp (box_refl q) (chart_mono _ hp) (chart_mono _ hp) hp' hq
      (chart_chamber _ _) hq (chart_chamber _ _) (chart_chamber _ _)
  have hlift : mixed32 p q (liftedChart (L+1) p) (liftedChart (L+2) p) ≤
      mixed32 p' q (liftedChart (L+1) p') (liftedChart (L+2) p') :=
    mixed_mono hp (box_refl q) (lifted_mono _ hp) (lifted_mono _ hp) hp' hq
      (lifted_chamber _ _) hq (lifted_chamber _ _) (lifted_chamber _ _)
  have hgraph (M : ℕ) :
      mixed32 p q (graphShape p) (liftedChart M p) ≤ mixed32 p' q (graphShape p') (liftedChart M p') :=
    mixed_mono hp (box_refl q) (graph_mono hp) (lifted_mono _ hp) hp' hq
      (graph_chamber _) hq (graph_chamber _) (lifted_chamber _ _)
  exact min_le_min hchart (Nat.add_le_add (Nat.add_le_add hlift (Nat.mul_le_mul_left _ (hgraph _)))
    (Nat.mul_le_mul_left _ (hgraph _)))
theorem ceil_mono {a b : ℕ} (h : a ≤ b) (l : ℕ) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h l) 1)
theorem physical_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l : ℕ) : P3_6.physicalPrice x l ≤ P3_6.physicalPrice y l := by
  let p := x.chamber
  let p' := y.chamber
  let q : Shape := P3_6.primaryBox
  let L := P3_6.taylorLength
  let A := q.plus (p.scale 4)
  let A' := q.plus (p'.scale 4)
  have hp := normalize_mono h
  have hpc : Chamber p := normalize_chamber x hx
  have hp'c : Chamber p' := normalize_chamber y hy
  have hqc : Chamber q := ⟨by decide, le_rfl⟩
  have ha : InBox A A' := plus_mono (box_refl q) (scale_mono hp 4)
  have hac : Chamber A := plus_chamber hqc (scale_chamber hpc 4)
  have ha'c : Chamber A' := plus_chamber hqc (scale_chamber hp'c 4)
  have hs := surface_mono hp hp'c hqc
  have hb := (chart_mono (L+1) hp).1
  have hmain : (P3.t + 2*P3_6.incidenceGap) * x.b * q.b * (chart (L+1) p).b ≤
      (P3.t + 2*P3_6.incidenceGap) * y.b * q.b * (chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left P3.t hc) (Nat.mul_le_mul_left (2*P3_6.incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*P3_6.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (ceil_mono (Nat.add_le_add (ceil_mono hs _) (ceil_mono hmain _)) l) hraw)
    (ceil_mono hgeom _)
end P3_6_8_8
end
section
namespace P3_6_8_8
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8 (Valid fullCap)
open P0_9_8 (twoStart indexBudget)
open P3_6_8 (twoOrder twoReserve)
open P3_6 (physicalPrice factorCap)
private def budget (j : ℕ) : ℕ := indexBudget twoStart (factorCap - twoReserve) j
private def peak (j : ℕ) : Shape := ⟨118, j, min 8 (j / 3)⟩
private def priceFromParts (f m₀ m₁ m₂ c₀ c₁ p₀ p₁ : ℕ) : ℕ :=
  ceilDiv (ceilDiv (m₀ + 133346 * m₁ + 133347 * m₂) 32 +
    ceilDiv ((82161 + 2 * 46639) * 118 * 4012 * 31202965) 46639) 72 +
  2 * 133344 * 118 * 4012 +
  ceilDiv (82161 * (c₀ + 2 * f * c₁) + 93278 * (p₀ + 2 * f * p₁)) 1492448
private theorem row_le (lo j f m₀ m₁ m₂ c₀ c₁ p₀ p₁ price allowance : ℕ) :
    let a : Shape := ⟨118, j, f⟩
    let p := a.chamber
    let q := P3_6.primaryBox
    let L := P3_6.taylorLength
    let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
    let e₁ := liftedChart (L + 1) p
    let e₂ := liftedChart (L + 2) p
    let h := chart L p
    let z := q.plus (p.scale 4)
    mixed32 p q e₁ e₂ = m₀ → mixed32 p q g e₂ = m₁ → mixed32 p q g e₁ = m₂ →
    mixed32 p q z h = c₀ → mixed32 p p p h = c₁ →
    mixed32 p q z p = p₀ → mixed32 p p p p = p₁ →
    (chart (L + 1) p).b = 31202965 →
    priceFromParts f m₀ m₁ m₂ c₀ c₁ p₀ p₁ = price → budget lo = allowance →
    price ≤ allowance → P3_6.physicalPrice a twoOrder ≤ budget lo := by
  intro a p q L g e₁ e₂ h z hm₀ hm₁ hm₂ hc₀ hc₁ hp₀ hp₁ hb hprice hbudget hle
  have hsurface : P3_6.surfaceNumerator32 p q ≤ m₀ + 133346 * m₁ + 133347 * m₂ := by
    unfold P3_6.surfaceNumerator32
    change min _ (mixed32 p q e₁ e₂ + 133346 * mixed32 p q g e₂ +
      133347 * mixed32 p q g e₁) ≤ _
    rw [hm₀, hm₁, hm₂]
    exact min_le_right _ _
  have hpaid : P3_6.physicalPrice a twoOrder ≤ priceFromParts f m₀ m₁ m₂ c₀ c₁ p₀ p₁ := by
    unfold P3_6.physicalPrice priceFromParts
    change ceilDiv (ceilDiv (P3_6.surfaceNumerator32 p q) 32 +
          ceilDiv ((82161 + 2 * 46639) * 118 * 4012 * (chart (L + 1) p).b) 46639) 72 +
        2 * 133344 * 118 * 4012 +
        ceilDiv (82161 * (mixed32 p q z h + 2 * f * mixed32 p p p h) +
          93278 * (mixed32 p q z p + 2 * f * mixed32 p p p p)) 1492448 ≤ _
    rw [hb, hc₀, hc₁, hp₀, hp₁]
    exact Nat.add_le_add_right (Nat.add_le_add_right
      (ceil_mono (Nat.add_le_add_right (ceil_mono hsurface _) _) _) _) _
  rw [← hprice] at hle
  rw [hbudget]
  exact hpaid.trans hle
section
set_option maxRecDepth 4096
local notation "row!" lo "," hi "," f "," m₀ "," m₁ "," m₂ "," c₀ "," c₁ "," p₀ "," p₁
    "," price "," allowance =>
  row_le lo hi f m₀ m₁ m₂ c₀ c₁ p₀ p₁ price allowance
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
private theorem r1 : physicalPrice (peak 12) twoOrder ≤ budget 3 :=
  row! 3,12,4,0x5827371961a83d00,0x33f5170f5980,0x33f4fd860900,0x28f9abd3a12300,0xd95c902400,0xb79ae6600,4147200,0x238c49aa1dc3b3,0x28453f9d06ae44
private theorem r2 : physicalPrice (peak 25) twoOrder ≤ budget 13 :=
  row! 13,25,8,0x1bce0934ba20a3a00,0xee6c12a0b280,0xee6b9d71a8e0,0x6b5b98938936c0,0x7f883faea00,0x1c3cd12e60,35511552,0xa32ce9d66cbb71,0xae8168fdc79dd4
private theorem r3 : physicalPrice (peak 36) twoOrder ≤ budget 26 :=
  row! 26,36,8,0x3c6b1e1e205221300,0x1f91a55735280,0x1f9195d32d800,0xb1e658655e0300,0x165c5c33d000,0x2df4ac8e00,97173504,0x159ab5090561ed2,0x15d02d1fb8f3ba9
private theorem r4 : physicalPrice (peak 42) twoOrder ≤ budget 37 :=
  row! 37,42,8,0x531dadf8e733b5200,0x2b1779e56d740,0x2b1764b797800,0xddd1e27484f800,0x213d2f2c7c00,0x38f540da80,0x88c6800,0x1d7d6416e72f84b, 0x1f0ab65e5fd0ffb
end
private theorem peak_fit (j : ℕ) : 3 * (peak j).t ≤ j := by
  change 3 * min 8 (j / 3) ≤ j
  have h := min_le_right 8 (j / 3)
  omega
private theorem interval_le {lo hi j : ℕ} (hlo : lo ≤ j) (hhi : j ≤ hi)
    (hrow : physicalPrice (peak hi) twoOrder ≤ budget lo) :
    physicalPrice (peak j) twoOrder ≤ budget j := by
  have hpeak : InBox (peak j) (peak hi) :=
    ⟨le_rfl, hhi, min_le_min le_rfl (Nat.div_le_div_right hhi)⟩
  exact (physical_mono hpeak (peak_fit j) (peak_fit hi) twoOrder).trans
    (hrow.trans (Nat.div_le_div_right (Nat.mul_le_mul_left _ hlo)))
private theorem peak_bound {j : ℕ} (hlo : 3 ≤ j) (hhi : j ≤ 42) :
    physicalPrice (peak j) twoOrder ≤ budget j := by
  by_cases h12 : j ≤ 12
  · exact interval_le hlo h12 r1
  by_cases h25 : j ≤ 25
  · exact interval_le (by omega) h25 r2
  by_cases h36 : j ≤ 36
  · exact interval_le (by omega) h36 r3
  · exact interval_le (by omega) hhi r4
theorem proof : P3_6_8.c8 := by
  intro a ha hbox
  change 2 + a.b ≤ 120 ∧ 6 + a.j ≤ 48 ∧ 2 + a.t ≤ 10 at hbox
  obtain ⟨hb, hj, ht⟩ := hbox
  have hlo : 3 ≤ a.j := (Nat.mul_le_mul_left 3 ha.1).trans ha.2.1
  have hfit : 3 * a.t ≤ a.j := ha.2.1
  have hpeak : InBox a (peak a.j) :=
    ⟨by change a.b ≤ 118; omega, le_rfl, by change a.t ≤ min 8 (a.j / 3); omega⟩
  exact (physical_mono hpeak hfit (peak_fit a.j) twoOrder).trans (peak_bound hlo (by omega))
end P3_6_8_8
end
