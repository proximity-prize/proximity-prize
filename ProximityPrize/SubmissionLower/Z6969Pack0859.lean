import ProximityPrize.SubmissionLower.Gate6966Tail
import ProximityPrize.SubmissionLower.Z6969Pack0853
import ProximityPrize.SubmissionLower.Z6969Pack0851
import ProximityPrize.SubmissionLower.Z6969Pack0836
import ProximityPrize.SubmissionLower.Z6969Pack0854
import ProximityPrize.SubmissionLower.R6960Low6960WeightedCut
import ProximityPrize.SubmissionLower.Shared50OrderDivision
import ProximityPrize.SubmissionLower.Z6969Pack0840

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969GateTail
section Z6969Source2426
set_option autoImplicit true
namespace Low6969GateFreeCard
export Gate6966FreeCard (mn mx mn_eq mx_eq)
end Low6969GateFreeCard

namespace Low6969GateCell
export Gate6966Cell (Gt hB hJ hT TT Cone TT_symm TT_mono_left TT_mono hB_mono hJ_mono hT_mono
  hull_cone Pr VD mkPr lhsV LS lhsV_eq LS_mono cell Valid cell_sound core levelOK level_sound
  hullP hull_le quad tail_ok)
end Low6969GateCell

namespace Low6969GateCell.Gt
export Gate6966Cell.Gt (Ok xh wx0 wx1 wx2 sep tsep)
end Low6969GateCell.Gt
end Z6969Source2426

-- Source: ProximityPrize.SubmissionLower.Low6969GateAssm
section Z6969Source2427
set_option autoImplicit true
set_option Elab.async false

-- merged module Low6969GateCount2
section Merged_Low6969GateCount2

set_option autoImplicit false
set_option Elab.async false

namespace Low6969GateCount2

open P3 (K)
open K1_13 (Row shape)
open K1_13_6 (GeoJets)
open Low6969Prices (Messages SmallFactor ActiveFits ProperCut)
open Low6969GeometryCut (CutInput)
open Low6969SharedTally (Data)
open Low6969SharedTallyNew (tally)
open Low6969SharedPersistent (Persistent)
open scoped Polynomial BigOperators

theorem count₂ {w : P3.I → K} {Γ : Finset K} {s : K → (Polynomial K)}
    (hm : Messages w Γ s) (f : Row 4) (hf : SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (l : ℕ) (hl : 0 < l) (hproper : ProperCut f Γ s l)
    (A : ℕ)
    (hmarks : ∀ (Q : Row 4) (input : CutInput Γ s f Q l)
      (data : Data Γ s f Q l {P | Persistent Γ s P}), tally data data.branches ≤ A) :
    Γ.card ≤ A + Low6969SharedPrice.additiveBase (shape f) l + Low6969SharedPrice.nonsharedFee (shape f) l := by
  classical
  obtain ⟨Q, hQprop, hbox, hweight, hQ, hcontact⟩ := hproper
  have input : CutInput Γ s f Q l :=
    ⟨hm.distinct, hm.degree, hf, hon, hl, hQprop, hbox, hweight, hcontact⟩
  let data : Data Γ s f Q l {P | Persistent Γ s P} := Low6969SharedTally.build _
  obtain ⟨a, c, d, hCard, ha, hc, hd⟩ := Low6969SharedCount.cover_counts hm input data
  have hG := hmarks Q input data
  have hbase := Low6969SharedTallyOld.additive_le hl ha hc hd
  omega

end Low6969GateCount2

end Merged_Low6969GateCount2

-- merged module Low6969GateFinal
section Merged_Low6969GateFinal

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace Low6969GateFinal

open P3 (K)
open K1_13 (Row Shape shape InBox)
open K1_13_6 (GeoJets toGeneric)
open K1_13_6_1_2 (VanishesTo)
open Low6969SharedPrice (coord)
open Low6969GeometryCut (CutInput)
open Low6969GeometryCut_2 (Branch)
open Low6969SharedTally (Data)
open Low6969SharedTallyNew (tally)
open Low6969SharedPersistent (Persistent)
open Low6969SharedRational (FractionJet toGeometric)
open Low6969SharedShapeRank (ambient contactSpace)
open scoped Polynomial BigOperators

instance infiniteGenericField : Infinite K1_13_6.GenericField :=
  Infinite.of_injective (algebraMap (Polynomial K1_13.Geom) K1_13_6.GenericField)
    (IsFractionRing.injective (Polynomial K1_13.Geom) K1_13_6.GenericField)

def levelCount : ℕ := 1 + Low6969Prices.primaryCutoff / Low6969Prices.layerWidth

def boxOf (Yb : Fin 3 → ℕ) : Shape := ⟨max (Yb 0) (Yb 1), Yb 1, min (Yb 2) (Yb 1 / 3)⟩

theorem boxOf_chamber (Yb : Fin 3 → ℕ) : Low48BentLattice.Chamber (boxOf Yb, 0) := by
  refine ⟨le_max_right _ _, ?_, Nat.zero_le _⟩
  change 3 * min (Yb 2) (Yb 1 / 3) ≤ Yb 1
  have := Nat.min_le_right (Yb 2) (Yb 1 / 3)
  omega

theorem inBox_boxOf {G : Row 4} {Yb : Fin 3 → ℕ} (h : ∀ i, coord (shape G) i ≤ Yb i) :
    InBox (shape G) (boxOf Yb) := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hc := (K1_13_7_1.shape_chamber G).2
  change 3 * (shape G).t ≤ (shape G).j at hc
  refine ⟨?_, ?_, ?_⟩
  · change (shape G).b ≤ max (Yb 0) (Yb 1)
    exact le_trans (by simpa [coord] using h0) (le_max_left _ _)
  · simpa [coord, boxOf] using h1
  · change (shape G).t ≤ min (Yb 2) (Yb 1 / 3)
    refine le_min (by simpa [coord] using h2) ?_
    have h1' : (shape G).j ≤ Yb 1 := by simpa [coord] using h1
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)

noncomputable def Tt (p q₁ q₂ : Shape) : ℚ := (Low6969Gate.tiltedPair p q₁ q₂ : ℚ) / 1920

noncomputable def rhs (f : Row 4) (qs : Shape) (r a : ℕ) (cc v : ℚ) (B η : Fin 3 → ℕ) : ℚ :=
  let p := (shape f).chamber
  let Yb : Fin 3 → ℕ := fun i => B i - (a * coord (shape f) i + η i)
  (1 - cc) * Tt p (boxOf Yb) (boxOf Yb) + Tt p (boxOf η) (boxOf Yb) +
    ((r - a : ℕ) : ℚ) * Tt p (shape f).chamber (boxOf η) +
    cc * ((r - a : ℕ) : ℚ) * Tt p (shape f).chamber (boxOf Yb) +
    v * ((r - a : ℕ) : ℚ) ^ 2 * Tt p (shape f).chamber qs

def GoodAt (A : ℕ) (f : Row 4) (qs : Shape) (r a : ℕ) (cc v : ℚ) (B η : Fin 3 → ℕ) : Prop :=
  a < r ∧ Low6969GateTwoCut.ClassCert r a cc v ∧ rhs f qs r a cc v B η ≤ (A : ℚ) * ((r - a : ℕ) : ℚ) ^ 2

theorem exact_order_fun (S : Finset (Ideal GeoJets)) (hS : ∀ P ∈ S, P.IsPrime) {g : GeoJets} (hg : g ≠ 0) :
    ∃ e : Ideal GeoJets → ℕ, ∀ (P : Ideal GeoJets) (hP : P ∈ S),
      @VanishesTo _ _ P (hS P hP) g (e P) ∧ ¬ @VanishesTo _ _ P (hS P hP) g (e P + 1) := by
  classical
  have hex : ∀ P : Ideal GeoJets, ∃ n : ℕ, ∀ hP : P ∈ S,
      @VanishesTo _ _ P (hS P hP) g n ∧ ¬ @VanishesTo _ _ P (hS P hP) g (n + 1) := by
    intro P
    by_cases hP : P ∈ S
    · haveI := hS P hP
      obtain ⟨n, hn⟩ := Low6969GateOrder.exists_exact_order P hg
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose e he using hex
  exact ⟨e, fun P hP => he P hP⟩

variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}

theorem level_dichotomy (hf : Low6969Prices.SmallFactor f)
    (D : Data Γ s f Q l {P | Persistent Γ s P}) (input : CutInput Γ s f Q l)
    (htilt : Low6969Prices.tiltedFits (shape f))
    (qs : Shape) (hbs : InBox (shape (K1_13_6.separant f)) qs) (hcs : Low48BentLattice.Chamber (qs, 0))
    (hnd : ¬ f ∣ K1_13_6.separant f) (A r : ℕ) (B : Fin 3 → ℕ) (cert : ℕ → ℚ × ℚ)
    (hc0 : ∀ a, 0 ≤ (cert a).1) (hc1 : ∀ a, (cert a).1 ≤ 1) (hv0 : ∀ a, 0 ≤ (cert a).2)
    (U : Submodule K1_13_6.GenericField ↥ambient)
    (hU : U ≤ contactSpace (D.branches.image Branch.surface) r ⊓ Low6969GateBox.boxSpace (B 0) (B 1) (B 2))
    (hne : U ≠ ⊥) :
    ∃ (a : ℕ) (η : Fin 3 → ℕ),
      Module.finrank K1_13_6.GenericField U ≤
        Low6969GateShape.free (fun k => B k - (a * coord (shape f) k + η k)) ∧
      (∀ k, a * coord (shape f) k + η k ≤ B k) ∧ (η 2 ≤ η 0 ∧ 3 * η 2 ≤ η 1 ∧ η 1 ≤ 2 * η 0 + η 2) ∧
      (GoodAt A f qs r a (cert a).1 (cert a).2 B η → tally D D.branches ≤ A) := by
  classical
  set S := D.branches.image Branch.surface with hSdef
  have hS : ∀ P ∈ S, P.IsPrime := by
    intro P hP
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hP
    exact b.base.isPrime
  let U' : Submodule K1_13_6.GenericField FractionJet := U.map ambient.subtype
  have hU'ne : U' ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro u hu
    have : ambient.subtype u ∈ U' := ⟨u, hu, rfl⟩
    rw [h] at this
    have h0 : (u : FractionJet) = 0 := by simpa using this
    exact (Submodule.mem_bot _).mpr (Subtype.ext h0)
  have hfirr := hf.1
  have hdeg : 0 < f.totalDegree :=
    Nat.lt_of_lt_of_le hf.2.1 (MvPolynomial.degreeOf_le_totalDegree f 3)
  have hcont : ∀ Q' ∈ U', ∀ (P : Ideal GeoJets) (hP : P ∈ S),
      @VanishesTo _ _ P (hS P hP) (toGeometric Q') r := by
    rintro _ ⟨u, hu, rfl⟩ P hP
    haveI := hS P hP
    have hc : u ∈ contactSpace S r := (hU hu).1
    exact K1_13_6_1_2_2.vanishesTo_of_hasse _ P r (fun a ha => hc P hP a ha)
  have hB : ∀ Q' ∈ U', ∀ k, Low6969GateShape.shp k Q' ≤ B k := by
    rintro _ ⟨u, hu, rfl⟩ k
    have := Low6969GateHb.shp_le_of_mem_boxSpace (B 0) (B 1) (B 2) u (hU hu).2 k
    have hk : (![B 0, B 1, B 2] : Fin 3 → ℕ) k = B k := by fin_cases k <;> rfl
    simpa [hk] using this
  obtain ⟨a, H, K1, K2, hH0, hK10, hfH, hfG, hHG, hGG, hQ1, hQ2, hs1, hs2, hdim, hfit, hval⟩ :=
    Low6969GateRows.rows_from_subspace f hfirr hdeg U' hU'ne r S hS hcont B hB
  refine ⟨a, fun k => coord (shape H) k, ?_, hfit, hval, ?_⟩
  · have hfr : Module.finrank K1_13_6.GenericField U' = Module.finrank K1_13_6.GenericField U :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective ambient.subtype ambient.injective_subtype U)).symm
    rw [← hfr]
    exact hdim
  · intro hgood
    obtain ⟨hlt, hcertA, hrhs⟩ := hgood
    have hf0 : f ≠ 0 := hfirr.ne_zero
    have hf0' := K1_13_6_3_6.toGeneric_ne_zero hf0
    have hH0' := K1_13_6_3_6.toGeneric_ne_zero hH0
    have hK10' := K1_13_6_3_6.toGeneric_ne_zero hK10
    have hsf0 : K1_13_6.separant f ≠ 0 := fun h => hnd (by rw [h]; exact dvd_zero _)
    have hsf0' := K1_13_6_3_6.toGeneric_ne_zero hsf0
    have hfs := K1_13_7_1.proper_generic f (K1_13_6.separant f) hfirr hnd
    obtain ⟨e, he⟩ := exact_order_fun S hS hf0'
    obtain ⟨m, hm'⟩ := exact_order_fun S hS hH0'
    have hmemS : ∀ b ∈ D.branches, b.surface ∈ S := fun b hb => Finset.mem_image_of_mem _ hb
    have hch : ∀ G : Row 4, Low48BentLattice.Chamber ((shape G).chamber, 0) := fun G =>
      ⟨(K1_13_7_1.shape_chamber G).1, (K1_13_7_1.shape_chamber G).2, Nat.zero_le _⟩
    have hbox : ∀ G : Row 4, InBox (shape G) (shape G).chamber := fun G =>
      ⟨le_max_left _ _, le_rfl, le_rfl⟩
    have hmain := Low6969GateTwoCut.two_cut_count_tilted D input D.branches (subset_refl _) H K1 K2
      (K1_13_6.separant f) htilt (shape f).chamber (boxOf fun k => coord (shape H) k)
      (boxOf fun k => B k - (a * coord (shape f) k + coord (shape H) k))
      (boxOf fun k => B k - (a * coord (shape f) k + coord (shape H) k)) qs
      (hbox f) (inBox_boxOf (fun k => le_rfl)) (inBox_boxOf hs1) (inBox_boxOf hs2) hbs
      (hch f) (boxOf_chamber _) (boxOf_chamber _) (boxOf_chamber _) hcs r a (cert a).1 (cert a).2
      (hc0 a) (hc1 a) (hv0 a) hcertA e m hf0 hH0 hK10 hf0' hH0' hK10' hsf0 hsf0' hfH hfG hHG hGG hfs
      (fun b hb => he b.surface (hmemS b hb)) (fun b hb => hm' b.surface (hmemS b hb)) rfl
      (fun b hb => hQ1 b.surface (hmemS b hb)) (fun b hb => hQ2 b.surface (hmemS b hb)) hlt.le
    have hρ : (0 : ℚ) < ((r - a : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hlt
    have hN := Low6969GateTwoCut.mark_bound_of_good hρ hmain (by exact hrhs)
    have : ((tally D D.branches : ℕ) : ℚ) ≤ (A : ℚ) := by
      simpa [tally] using hN
    exact_mod_cast this

theorem two_cut_price_tilted {w : P3.I → K} (hm : Low6969Prices.Messages w Γ s) (hf : Low6969Prices.SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (hl : 0 < l)
    (hproper : Low6969Prices.ProperCut f Γ s l) (htilt : Low6969Prices.tiltedFits (shape f))
    (qs : Shape) (hbs : InBox (shape (K1_13_6.separant f)) qs) (hcs : Low48BentLattice.Chamber (qs, 0))
    (hnd : ¬ f ∣ K1_13_6.separant f) (A : ℕ) (B : ℕ → Fin 3 → ℕ) (W : ℕ → ℕ)
    (cert : ℕ → ℕ → ℚ × ℚ) (hc0 : ∀ r a, 0 ≤ (cert r a).1) (hc1 : ∀ r a, (cert r a).1 ≤ 1)
    (hv0 : ∀ r a, 0 ≤ (cert r a).2)
    (hW : ∀ i, i < levelCount → ∀ (a : ℕ) (η : Fin 3 → ℕ),
      (∀ k, a * coord (shape f) k + η k ≤ B i k) → (η 2 ≤ η 0 ∧ 3 * η 2 ≤ η 1 ∧ η 1 ≤ 2 * η 0 + η 2) →
      ¬ GoodAt A f qs (i + 1) a (cert (i + 1) a).1 (cert (i + 1) a).2 (B i) η →
        Low6969GateShape.free (fun k => B i k - (a * coord (shape f) k + η k)) ≤ W i)
    (hsum : ∑ i ∈ Finset.range levelCount,
      (Low6969Prices.symbolCount - Low6969GateBox.ambCount (B i 0) (B i 1) (B i 2) + W i) < Low6969Prices.layerNeed) :
    Γ.card ≤ A + Low6969SharedPrice.additiveBase (shape f) l + Low6969SharedPrice.nonsharedFee (shape f) l := by
  classical
  unfold levelCount at hW hsum
  refine Low6969GateCount2.count₂ hm f hf hon l hl hproper A ?_
  intro Q' input' data'
  set S := data'.branches.image Branch.surface with hSdef
  have hpers : ∀ P ∈ S, Persistent Γ s P := by
    intro P hP
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
    exact data'.allowed b hb
  have hneed := Low6969SharedShapeRank.bank_layers hm S hpers
  refine @Low6969GateGate.gate₂_of_need K1_13_6.GenericField (↥ambient) ℕ inferInstance inferInstance inferInstance
    inferInstance (ℕ × (Fin 3 → ℕ)) (tally data' data'.branches ≤ A)
    (Finset.range (1 + Low6969Prices.primaryCutoff / Low6969Prices.layerWidth))
    (fun i => contactSpace S (i + 1)) (fun i => Low6969GateBox.boxSpace (B i 0) (B i 1) (B i 2)) W
    (fun i g => (∀ k, g.1 * coord (shape f) k + g.2 k ≤ B i k) →
      (g.2 2 ≤ g.2 0 ∧ 3 * g.2 2 ≤ g.2 1 ∧ g.2 1 ≤ 2 * g.2 0 + g.2 2) →
      GoodAt A f qs (i + 1) g.1 (cert (i + 1) g.1).1 (cert (i + 1) g.1).2 (B i) g.2)
    (fun i g => Low6969GateShape.free (fun k => B i k - (g.1 * coord (shape f) k + g.2 k)))
    Low6969Prices.layerNeed ?_ ?_ hneed ?_
  · intro i _ U hU hne
    obtain ⟨a, η, hd, hfit, hval, hg⟩ := level_dichotomy hf data' input' htilt qs hbs hcs hnd A (i + 1) (B i)
      (cert (i + 1)) (hc0 (i + 1)) (hc1 (i + 1)) (hv0 (i + 1)) U hU hne
    exact ⟨(a, η), hd, fun hgood => hg (hgood hfit hval)⟩
  · intro i hi g hg
    by_contra hn
    exact hg (fun h1 h2 => by_contra fun h3 => hn (hW i (Finset.mem_range.mp hi) g.1 g.2 h1 h2 h3))
  · calc _ = ∑ i ∈ Finset.range levelCount,
          (Low6969Prices.symbolCount - Low6969GateBox.ambCount (B i 0) (B i 1) (B i 2) + W i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Low6969SharedShapeRank.ambient_dim, Low6969GateBox.boxSpace_dim]
      _ < _ := hsum

end Low6969GateFinal

end Merged_Low6969GateFinal

-- merged module Low6969GateAssm
section Merged_Low6969GateAssm

set_option autoImplicit false

namespace Low6969GateCell
open Low6969GateCertCF (cvOf cvOf_le)

abbrev Lv := List (ℕ × ℕ × ℕ × ℕ)

def dflt : ℕ × ℕ × ℕ × ℕ := (4012, 1650, 550, 0)
def Bof (lv : Lv) (i : ℕ) : Fin 3 → ℕ := ![(lv.getD i dflt).1, (lv.getD i dflt).2.1, (lv.getD i dflt).2.2.1]
def Wof (lv : Lv) (i : ℕ) : ℕ := (lv.getD i dflt).2.2.2

def okAt (G : Gt) (r0 : ℕ) (ws : List ℕ) (lv : Lv) (i : ℕ) : Bool :=
  levelOK G (i + 1) (lv.getD i dflt).2.2.2 (lv.getD i dflt).1 (lv.getD i dflt).2.1 (lv.getD i dflt).2.2.1 80
    (fun a => some (cvOf r0 ws (i + 1) a))

def allOK (G : Gt) (r0 : ℕ) (ws : List ℕ) (lv : Lv) (lo n : ℕ) : Bool :=
  (List.range n).all fun d => okAt G r0 ws lv (lo + d)












theorem allOK_get (G : Gt) (r0 : ℕ) (ws : List ℕ) (lv : Lv) (n : ℕ)
    (h : allOK G r0 ws lv 0 n = true) (i : ℕ) (hi : i < n) : okAt G r0 ws lv i = true := by
  unfold allOK at h
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simpa using this

theorem lookup_none (r0 : ℕ) (ws : List ℕ) (r a : ℕ) (h : r0 + ws.length ≤ r) :
    Low6969GateClassTable.lookup r0 ws r a = none := by
  unfold Low6969GateClassTable.lookup
  rw [if_neg]
  intro hc; omega

theorem cvOf_tail (r0 : ℕ) (ws : List ℕ) (r a amax : ℕ) (hr : r0 + ws.length ≤ r) (ha : a ≤ amax) (hlt : a < r) :
    (cvOf r0 ws r a).2 * ((r - a) * (r - a)) ≤ Low6969GateCell.VD * (amax * amax) + (r - a) * (r - a) := by
  unfold cvOf
  by_cases h0 : a = 0
  · subst h0; simp [Low6969GateCell.VD]
  · have hb : Nat.beq a 0 = false := by
      rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨n, hn⟩
      rw [hn]; rfl
    simp only [hb, Bool.cond_false, lookup_none r0 ws r a hr]
    have hp : 0 < (r - a) * (r - a) := Nat.mul_pos (Nat.sub_pos_of_lt hlt) (Nat.sub_pos_of_lt hlt)
    have h1 := Nat.div_mul_le_self (Low6969GateCell.VD * a * a + (r - a) * (r - a) - 1) ((r - a) * (r - a))
    have h2 : a * a ≤ amax * amax := Nat.mul_le_mul ha ha
    have h3 : Low6969GateCell.VD * a * a ≤ Low6969GateCell.VD * (amax * amax) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ h2
    simp only [Low6969GateCell.VD] at h1 h3 ⊢
    omega



































/-! PERF (69.62): the `Low6969GateAmb.compute` lower bound evaluated in Nat. `cumulative` over ℤ is
slow in the kernel (Int.div/mod, 8 `denominator` calls per count); `denN`/`dg` are the same
quantities with guarded Nat subtraction. -/
def denN (u : ℕ) : ℕ :=
  1 + (u % 6) * (u % 6 + 1) / 2 + (u / 6) * (22 + 7 * (u % 6) + (u % 6) * (u % 6 - 1) / 2) +
    (57 + 6 * (u % 6)) * ((u / 6) * (u / 6 - 1) / 2) + 6 * (u / 6) * (u / 6 - 1) * (u / 6 - 2)

def dg (v c : ℕ) : ℕ := bif Nat.ble c v then denN (v - c) else 0

def cumPV (V d : ℕ) : ℕ := dg V 0 + dg V (2 * d + 3) + dg V (2 * d + 4) + dg V (2 * d + 5)

def cumQV (V d : ℕ) : ℕ := dg V (d + 1) + dg V (d + 2) + dg V (d + 3) + dg V (3 * d + 6)

def cumP (d u : ℕ) : ℕ := cumPV (min u (3 * d)) d

def cumQ (d u : ℕ) : ℕ := cumQV (min u (3 * d)) d

def cappedN (d u c : ℕ) : ℤ :=
  ((cumP d u : ℤ) - cumQ d u) -
    (bif Nat.ble (c + 1) d && Nat.ble (3 * (c + 1)) u then
      (cumP (d - c - 1) (u - 3 * (c + 1)) : ℤ) - cumQ (d - c - 1) (u - 3 * (c + 1)) else 0)

theorem denN_eq (n : ℕ) : K1_13_2.denominator (n : ℤ) = (denN n : ℤ) := by
  unfold K1_13_2.denominator denN
  rw [if_neg (by omega)]
  have hq : ((n : ℤ) / 6) = ((n / 6 : ℕ) : ℤ) := by omega
  have hr : ((n : ℤ) % 6) = ((n % 6 : ℕ) : ℤ) := by omega
  simp only [hq, hr]
  have hr6 : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize n % 6 = r at *
  generalize n / 6 = q at *
  rcases q with _ | _ | q <;> interval_cases r <;> push_cast <;> simp <;> ring_nf <;> simp

theorem den_eq (v c : ℕ) : K1_13_2.denominator ((v : ℤ) - (c : ℤ)) = (dg v c : ℤ) := by
  unfold dg
  by_cases h : c ≤ v
  · have : Nat.ble c v = true := Nat.ble_eq_true_of_le h
    rw [this, show (v : ℤ) - c = ((v - c : ℕ) : ℤ) by omega]
    exact denN_eq _
  · have : Nat.ble c v = false := by
      cases e : Nat.ble c v
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true e) h
    rw [this]
    unfold K1_13_2.denominator
    rw [if_pos (by omega)]
    rfl

theorem cum_eq (d u : ℕ) : K1_13_2.cumulative (d : ℤ) (u : ℤ) = (cumP d u : ℤ) - cumQ d u := by
  unfold K1_13_2.cumulative
  have h0 : (decide ((d : ℤ) < 0) || decide ((u : ℤ) < 0)) = false := by simp
  rw [h0]
  simp only [Bool.false_eq_true, if_false]
  have hv : min (u : ℤ) (3 * (d : ℤ)) = ((min u (3 * d) : ℕ) : ℤ) := by push_cast; rfl
  rw [hv]
  unfold cumP cumQ cumPV cumQV
  generalize min u (3 * d) = V
  have e0 := den_eq V 0
  have e1 := den_eq V (d + 1)
  have e2 := den_eq V (d + 2)
  have e3 := den_eq V (d + 3)
  have e4 := den_eq V (2 * d + 3)
  have e5 := den_eq V (2 * d + 4)
  have e6 := den_eq V (2 * d + 5)
  have e7 := den_eq V (3 * d + 6)
  push_cast at e0 e1 e2 e3 e4 e5 e6 e7
  rw [sub_zero] at e0
  have r1 : (V : ℤ) - d - 1 = V - (d + 1) := by ring
  have r2 : (V : ℤ) - d - 2 = V - (d + 2) := by ring
  have r3 : (V : ℤ) - d - 3 = V - (d + 3) := by ring
  have r4 : (V : ℤ) - 2 * d - 3 = V - (2 * d + 3) := by ring
  have r5 : (V : ℤ) - 2 * d - 4 = V - (2 * d + 4) := by ring
  have r6 : (V : ℤ) - 2 * d - 5 = V - (2 * d + 5) := by ring
  have r7 : (V : ℤ) - 3 * d - 6 = V - (3 * d + 6) := by ring
  rw [r1, r2, r3, r4, r5, r6, r7, e0, e1, e2, e3, e4, e5, e6, e7]
  push_cast
  ring


theorem capped_eq (d u c : ℕ) : K1_13_2.cappedCount (d : ℤ) (u : ℤ) (c : ℤ) = cappedN d u c := by
  unfold K1_13_2.cappedCount cappedN
  rw [if_neg (by omega), cum_eq]
  by_cases h : c + 1 ≤ d ∧ 3 * (c + 1) ≤ u
  · have e1 : (d : ℤ) - c - 1 = ((d - c - 1 : ℕ) : ℤ) := by omega
    have e2 : (u : ℤ) - 3 * ((c : ℤ) + 1) = ((u - 3 * (c + 1) : ℕ) : ℤ) := by omega
    rw [e1, e2, cum_eq]
    have : (Nat.ble (c + 1) d && Nat.ble (3 * (c + 1)) u) = true := by
      simp [Nat.ble_eq, h.1, h.2]
    rw [this]; rfl
  · have : (Nat.ble (c + 1) d && Nat.ble (3 * (c + 1)) u) = false := by
      by_cases h1 : c + 1 ≤ d
      · have h2 : ¬ 3 * (c + 1) ≤ u := fun x => h ⟨h1, x⟩
        have e : Nat.ble (3 * (c + 1)) u = false :=
          Bool.eq_false_iff.mpr (fun e => h2 (Nat.le_of_ble_eq_true e))
        simp [e]
      · have e : Nat.ble (c + 1) d = false :=
          Bool.eq_false_iff.mpr (fun e => h1 (Nat.le_of_ble_eq_true e))
        simp [e]
    rw [this]
    have h2 : K1_13_2.cumulative ((d : ℤ) - c - 1) ((u : ℤ) - 3 * ((c : ℤ) + 1)) = 0 := by
      unfold K1_13_2.cumulative
      rw [if_pos]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
    rw [h2]; rfl

def sumUpTo (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumUpTo f n + f n

theorem sumUpTo_eq (f : ℕ → ℤ) (n : ℕ) : sumUpTo f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp [sumUpTo]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; rfl

def blockN (b j t k : ℕ) : ℤ :=
  ((Low6969GateAmb.stop b k - Low6969GateAmb.start k : ℕ) : ℤ) * cappedN (Low6969GateAmb.padGrade b k) (Low6969GateAmb.index j) t

def computeN (b j t : ℕ) : ℤ := sumUpTo (blockN b j t) (Low6969GateAmb.chunks b)

theorem computeN_eq (b j t : ℕ) : computeN b j t = Low6969GateAmb.compute b j t := by
  unfold computeN Low6969GateAmb.compute
  rw [sumUpTo_eq]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold blockN Low6969GateAmb.block
  rw [capped_eq]


def ambLB (b j t : ℕ) : ℤ :=
  bif Nat.ble 4012 b && Nat.ble 1650 j && Nat.ble 550 t then (Low6969Prices.symbolCount : ℤ) else computeN b j t

theorem ambLB_le (b j t : ℕ) : ambLB b j t ≤ (Low6969GateBox.ambCount b j t : ℤ) := by
  unfold ambLB
  cases h : (Nat.ble 4012 b && Nat.ble 1650 j && Nat.ble 550 t)
  · simp only [Bool.cond_false, computeN_eq]
    exact Low6969GateAmb.amb_ge b j t
  · have h' : 4012 ≤ b ∧ 1650 ≤ j ∧ 550 ≤ t := by simpa [Nat.ble_eq, and_assoc] using h
    simp only [Bool.cond_true]
    rw [Low6969GateAmb.amb_full b j t h'.1 h'.2.1 h'.2.2]

def lsum (lv : Lv) (i : ℕ) : ℤ :=
  (Low6969Prices.symbolCount : ℤ) - ambLB (lv.getD i dflt).1 (lv.getD i dflt).2.1 (lv.getD i dflt).2.2.1 +
    ((lv.getD i dflt).2.2.2 : ℤ)















end Low6969GateCell

end Merged_Low6969GateAssm
end Z6969Source2427

-- Source: ProximityPrize.SubmissionLower.Low6969GateBilinear
section Z6969Source2428
set_option autoImplicit true
set_option Elab.async false

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

namespace Low6969GateBilinear

open Low6969Prices K1_13

def Nt (B1 J2 t k h1 h2 x1 x2 x3 y1 y2 y3 : ℤ) : ℤ :=
  (-960*(2*J2*h1*h2 - 2*J2*h1*k*t + J2*h1*k - 2*J2*h1*t - J2*h1 - 2*J2*h2*k*t + J2*h2*k - 2*J2*h2 - 2*J2*k^2*t - 2*J2*k*t - 4*J2*k - 2*J2 - 2*h1*h2*t + 3*h1*k*t^2 - 2*h1*k*t + 3*h1*t^2 + 3*h2*k*t^2 - 2*h2*k*t + 2*h2*t + 3*k^2*t^2 + 3*k*t^2 + 4*k*t + 2*t - 4)) * x1 * y2
  + (960*(J2^2*h1*k + J2^2*h1 + J2^2*h2*k + J2^2*k^2 + J2^2*k + 2*J2*h1*h2 - 6*J2*h1*k*t + 2*J2*h1*k - 6*J2*h1*t - 6*J2*h2*k*t + 2*J2*h2*k - 2*J2*h2 - 6*J2*k^2*t - 6*J2*k*t - 4*J2*k - 2*J2 - 6*h1*h2*t + 4*h1*h2 + 9*h1*k*t^2 - 6*h1*k*t + 9*h1*t^2 - 4*h1 + 9*h2*k*t^2 - 6*h2*k*t + 6*h2*t - 4*h2 + 9*k^2*t^2 + 9*k*t^2 + 12*k*t + 6*t + 4)) * x1 * y3
  + (-960*(2*J2*h1*h2 - 2*J2*h1*k*t + J2*h1*k - 2*J2*h1*t - J2*h1 - 2*J2*h2*k*t + J2*h2*k - 2*J2*h2 - 2*J2*k^2*t - 2*J2*k*t - 4*J2*k - 2*J2 - 2*h1*h2*t + 3*h1*k*t^2 - 2*h1*k*t + 3*h1*t^2 + 3*h2*k*t^2 - 2*h2*k*t + 2*h2*t + 3*k^2*t^2 + 3*k*t^2 + 4*k*t + 2*t - 4)) * x2 * y1
  + (480*(-4*B1*h1*h2 + 4*B1*h1*k*t - 2*B1*h1*k + 4*B1*h1*t + 2*B1*h1 + 4*B1*h2*k*t - 2*B1*h2*k + 4*B1*h2 + 4*B1*k^2*t + 4*B1*k*t + 8*B1*k + 4*B1 + 6*J2*h1*h2 - 6*J2*h1*k*t + 3*J2*h1*k - 6*J2*h1*t - 3*J2*h1 - 6*J2*h2*k*t + 3*J2*h2*k - 6*J2*h2 - 6*J2*k^2*t - 6*J2*k*t - 12*J2*k - 6*J2 - 4*h1*h2*t - 2*h1*h2 + 7*h1*k*t^2 - 4*h1*k*t + 7*h1*t^2 + 2*h1 + 7*h2*k*t^2 - 4*h2*k*t + 4*h2*t + 2*h2 + 7*k^2*t^2 + 7*k*t^2 + 8*k*t + 4*t - 12)) * x2 * y2
  + (-480*(-4*B1*J2*h1*k - 4*B1*J2*h1 - 4*B1*J2*h2*k - 4*B1*J2*k^2 - 4*B1*J2*k - 4*B1*h1*h2 + 12*B1*h1*k*t - 4*B1*h1*k + 12*B1*h1*t + 12*B1*h2*k*t - 4*B1*h2*k + 4*B1*h2 + 12*B1*k^2*t + 12*B1*k*t + 8*B1*k + 4*B1 + 3*J2^2*h1*k + 3*J2^2*h1 + 3*J2^2*h2*k + 3*J2^2*k^2 + 3*J2^2*k + 4*J2*h1*h2 - 14*J2*h1*k*t + 4*J2*h1*k - 14*J2*h1*t - 14*J2*h2*k*t + 4*J2*h2*k - 4*J2*h2 - 14*J2*k^2*t - 14*J2*k*t - 8*J2*k - 4*J2 - 8*h1*h2*t + 4*h1*h2 + 15*h1*k*t^2 - 8*h1*k*t + 15*h1*t^2 - 4*h1 + 15*h2*k*t^2 - 8*h2*k*t + 8*h2*t - 4*h2 + 15*k^2*t^2 + 15*k*t^2 + 16*k*t + 8*t + 4)) * x2 * y3
  + (960*(J2^2*h1*k + J2^2*h1 + J2^2*h2*k + J2^2*k^2 + J2^2*k + 2*J2*h1*h2 - 6*J2*h1*k*t + 2*J2*h1*k - 6*J2*h1*t - 6*J2*h2*k*t + 2*J2*h2*k - 2*J2*h2 - 6*J2*k^2*t - 6*J2*k*t - 4*J2*k - 2*J2 - 6*h1*h2*t + 4*h1*h2 + 9*h1*k*t^2 - 6*h1*k*t + 9*h1*t^2 - 4*h1 + 9*h2*k*t^2 - 6*h2*k*t + 6*h2*t - 4*h2 + 9*k^2*t^2 + 9*k*t^2 + 12*k*t + 6*t + 4)) * x3 * y1
  + (-480*(-4*B1*J2*h1*k - 4*B1*J2*h1 - 4*B1*J2*h2*k - 4*B1*J2*k^2 - 4*B1*J2*k - 4*B1*h1*h2 + 12*B1*h1*k*t - 4*B1*h1*k + 12*B1*h1*t + 12*B1*h2*k*t - 4*B1*h2*k + 4*B1*h2 + 12*B1*k^2*t + 12*B1*k*t + 8*B1*k + 4*B1 + 3*J2^2*h1*k + 3*J2^2*h1 + 3*J2^2*h2*k + 3*J2^2*k^2 + 3*J2^2*k + 4*J2*h1*h2 - 14*J2*h1*k*t + 4*J2*h1*k - 14*J2*h1*t - 14*J2*h2*k*t + 4*J2*h2*k - 4*J2*h2 - 14*J2*k^2*t - 14*J2*k*t - 8*J2*k - 4*J2 - 8*h1*h2*t + 4*h1*h2 + 15*h1*k*t^2 - 8*h1*k*t + 15*h1*t^2 - 4*h1 + 15*h2*k*t^2 - 8*h2*k*t + 8*h2*t - 4*h2 + 15*k^2*t^2 + 15*k*t^2 + 16*k*t + 8*t + 4)) * x3 * y2
  + (480*(-12*B1*J2*h1*k - 12*B1*J2*h1 - 12*B1*J2*h2*k - 12*B1*J2*k^2 - 12*B1*J2*k - 12*B1*h1*h2 + 36*B1*h1*k*t - 12*B1*h1*k + 36*B1*h1*t + 36*B1*h2*k*t - 12*B1*h2*k + 12*B1*h2 + 36*B1*k^2*t + 36*B1*k*t + 24*B1*k + 12*B1 + 7*J2^2*h1*k + 7*J2^2*h1 + 7*J2^2*h2*k + 7*J2^2*k^2 + 7*J2^2*k + 8*J2*h1*h2 - 30*J2*h1*k*t + 8*J2*h1*k - 30*J2*h1*t - 30*J2*h2*k*t + 8*J2*h2*k - 8*J2*h2 - 30*J2*k^2*t - 30*J2*k*t - 16*J2*k - 8*J2 - 12*h1*h2*t + 4*h1*h2 + 27*h1*k*t^2 - 12*h1*k*t + 27*h1*t^2 - 4*h1 + 27*h2*k*t^2 - 12*h2*k*t + 12*h2*t - 4*h2 + 27*k^2*t^2 + 27*k*t^2 + 24*k*t + 12*t + 4)) * x3 * y3

theorem sub5 (c0 c1 c2 c3 c4 : BentCap) : [c0,c1,c2,c3,c4].sublists = [[], [c0], [c1], [c0, c1], [c2], [c0, c2], [c1, c2], [c0, c1, c2], [c3], [c0, c3], [c1, c3], [c0, c1, c3], [c2, c3], [c0, c2, c3], [c1, c2, c3], [c0, c1, c2, c3], [c4], [c0, c4], [c1, c4], [c0, c1, c4], [c2, c4], [c0, c2, c4], [c1, c2, c4], [c0, c1, c2, c4], [c3, c4], [c0, c3, c4], [c1, c3, c4], [c0, c1, c3, c4], [c2, c3, c4], [c0, c2, c3, c4], [c1, c2, c3, c4], [c0, c1, c2, c3, c4]] := by rfl

def mixZ (caps : List BentCap) : ℤ :=
  caps.sublists.foldl (fun acc boxes =>
    let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
    acc + (-1 : ℤ) ^ (5 - boxes.length) * bentIntegral s.1.b s.1.j s.1.t s.2) 0

theorem ambientMix_eq (caps : List BentCap) : ambientMix caps = (mixZ caps).toNat := rfl

theorem mixZ_tilted (B1 J2 t k h1 h2 x1 x2 x3 y1 y2 y3 : ℕ) :
    mixZ [(⟨x1,x2,x3⟩, 0), (⟨y1,y2,y3⟩, 0), (⟨B1+1, J2+3, t+1⟩, 1),
      (⟨1 + k*B1, 4 + k*J2, 2 + k*t⟩, h1), (⟨1 + (k+1)*B1, 4 + (k+1)*J2, 2 + (k+1)*t⟩, h2)] =
      Nt B1 J2 t k h1 h2 x1 x2 x3 y1 y2 y3 := by
  unfold mixZ
  rw [sub5]
  simp only [List.foldl_cons, List.foldl_nil, addBent, Shape.plus, List.length_cons, List.length_nil]
  unfold bentIntegral Nt
  push_cast
  ring

theorem tiltedPair_formula (p q1 q2 : Shape) (hb : p.j + 1 ≤ p.b) (hj : 2 ≤ p.j) (k h1 h2 : ℕ)
    (hk : Low6969Prices.taylorLength - 4 = k) (hh1 : (bentLift k p).2 = h1) (hh2 : (bentLift (k + 1) p).2 = h2) :
    Low6969Gate.tiltedPair p q1 q2 =
      (Nt ((p.b - 1 : ℕ) : ℤ) ((p.j - 2 : ℕ) : ℤ) p.t k h1 h2 q1.b q1.j q1.t q2.b q2.j q2.t).toNat := by
  obtain ⟨b, j, t⟩ := p
  obtain ⟨x1, x2, x3⟩ := q1
  obtain ⟨y1, y2, y3⟩ := q2
  simp only at hb hj hh1 hh2 ⊢
  obtain ⟨B1, rfl⟩ : ∃ B1, b = B1 + 1 := ⟨b - 1, by omega⟩
  obtain ⟨J2, rfl⟩ : ∃ J2, j = J2 + 2 := ⟨j - 2, by omega⟩
  have hk1 : Low6969Prices.taylorLength - 3 = k + 1 := by
    have : 4 ≤ Low6969Prices.taylorLength := by decide
    omega
  unfold Low6969Gate.tiltedPair
  rw [hk, hk1, ambientMix_eq]
  have hg : bentGraph ⟨B1 + 1, J2 + 2, t⟩ = (⟨B1 + 1, J2 + 3, t + 1⟩, 1) := by
    simp [bentGraph]
    omega
  have hl1 : bentLift k ⟨B1 + 1, J2 + 2, t⟩ = (⟨1 + k * B1, 4 + k * J2, 2 + k * t⟩, h1) := by
    rw [← hh1]; simp [bentLift]
  have hl2 : bentLift (k + 1) ⟨B1 + 1, J2 + 2, t⟩ =
      (⟨1 + (k + 1) * B1, 4 + (k + 1) * J2, 2 + (k + 1) * t⟩, h2) := by
    rw [← hh2]; simp [bentLift]
  rw [hg, hl1, hl2, mixZ_tilted]
  simp

end Low6969GateBilinear
end Z6969Source2428

-- Source: ProximityPrize.SubmissionLower.Low6969WeightedCut
section Z6969Source2429
set_option autoImplicit true
set_option Elab.async false



-- merged module Low6969WeightedCut
section Merged_Low6969WeightedCut

set_option Elab.async false
set_option maxHeartbeats 1500000

namespace Low6969WeightedCut
noncomputable section

open K1_13 (Row Shape shape InBox)
open K1_13_6 (GeoJets toGeneric separant)
open K1_13_6_1_2 (VanishesTo)
open Low6969SharedPrice (Rate Surface surface surfaceScale weights coord)
open KoalaFarBridge (separant_box separant_proper)
open Low6969SharedChooseCut (weighted_pow weight_coord)
open Low6969SharedCount (shape_valid)
open scoped ENat






























open Low6969WeightedRate (boxFee sepBox charge)












































































































end
end Low6969WeightedCut

end Merged_Low6969WeightedCut
end Z6969Source2429

-- Source: ProximityPrize.SubmissionLower.Low6969GateThetaOrd
section Z6969Source2430
set_option autoImplicit true
set_option Elab.async false

-- merged module Low6969GateGateT
section Merged_Low6969GateGateT

-- merged module Low6969GateTheta
section Merged_Low6969GateTheta

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option Elab.async false

namespace Low6969GateBilinear

open Low6969Prices K1_13

structure TP where
  B1 : ℤ
  J2 : ℤ
  t : ℤ
  k : ℤ
  h1 : ℤ
  h2 : ℤ

def TP.eval (P : TP) (x1 x2 x3 y1 y2 y3 : ℤ) : ℤ :=
  Nt P.B1 P.J2 P.t P.k P.h1 P.h2 x1 x2 x3 y1 y2 y3

def TP.cone (P : TP) (c1 c2 c3 d1 d2 d3 : ℤ) : ℤ :=
  P.eval (c1 + c2 + 3*c3) (c2 + 3*c3) c3 (d1 + d2 + 3*d3) (d2 + 3*d3) d3

def TP.ray (P : TP) (i k : Fin 3) : ℤ :=
  P.cone (if i = 0 then 1 else 0) (if i = 1 then 1 else 0) (if i = 2 then 1 else 0)
    (if k = 0 then 1 else 0) (if k = 1 then 1 else 0) (if k = 2 then 1 else 0)

theorem cone_expand (P : TP) (c1 c2 c3 d1 d2 d3 : ℤ) :
    P.cone c1 c2 c3 d1 d2 d3 =
      c1*d1 * P.ray 0 0 + c1*d2 * P.ray 0 1 + c1*d3 * P.ray 0 2 +
      c2*d1 * P.ray 1 0 + c2*d2 * P.ray 1 1 + c2*d3 * P.ray 1 2 +
      c3*d1 * P.ray 2 0 + c3*d2 * P.ray 2 1 + c3*d3 * P.ray 2 2 := by
  simp only [TP.ray, TP.cone, TP.eval, Nt]
  simp
  ring

theorem theta_cone (Px Ph : TP) (num den : ℤ)
    (h : ∀ i k : Fin 3, den * Px.ray i k ≤ num * Ph.ray i k)
    (c1 c2 c3 d1 d2 d3 : ℤ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3) :
    den * Px.cone c1 c2 c3 d1 d2 d3 ≤ num * Ph.cone c1 c2 c3 d1 d2 d3 := by
  rw [cone_expand, cone_expand]
  have key : ∀ (a b : ℤ) (i k : Fin 3), 0 ≤ a → 0 ≤ b →
      den * ((a*b) * Px.ray i k) ≤ num * ((a*b) * Ph.ray i k) := by
    intro a b i k ha hb
    have := mul_le_mul_of_nonneg_left (h i k) (mul_nonneg ha hb)
    linarith
  have := key c1 d1 0 0 hc1 hd1
  have := key c1 d2 0 1 hc1 hd2
  have := key c1 d3 0 2 hc1 hd3
  have := key c2 d1 1 0 hc2 hd1
  have := key c2 d2 1 1 hc2 hd2
  have := key c2 d3 1 2 hc2 hd3
  have := key c3 d1 2 0 hc3 hd1
  have := key c3 d2 2 1 hc3 hd2
  have := key c3 d3 2 2 hc3 hd3
  linarith

def tpOf (p : Shape) (k h1 h2 : ℕ) : TP :=
  ⟨((p.b - 1 : ℕ) : ℤ), ((p.j - 2 : ℕ) : ℤ), p.t, k, h1, h2⟩

theorem tiltedPair_cone (p q1 q2 : Shape) (hb : p.j + 1 ≤ p.b) (hj : 2 ≤ p.j) (k h1 h2 : ℕ)
    (hk : Low6969Prices.taylorLength - 4 = k) (hh1 : (bentLift k p).2 = h1)
    (hh2 : (bentLift (k + 1) p).2 = h2)
    (h1c : q1.j ≤ q1.b) (h1t : 3 * q1.t ≤ q1.j) (h2c : q2.j ≤ q2.b) (h2t : 3 * q2.t ≤ q2.j) :
    Low6969Gate.tiltedPair p q1 q2 =
      ((tpOf p k h1 h2).cone ((q1.b - q1.j : ℕ) : ℤ) ((q1.j - 3 * q1.t : ℕ) : ℤ) q1.t
        ((q2.b - q2.j : ℕ) : ℤ) ((q2.j - 3 * q2.t : ℕ) : ℤ) q2.t).toNat := by
  rw [tiltedPair_formula p q1 q2 hb hj k h1 h2 hk hh1 hh2]
  congr 1
  simp only [TP.cone, TP.eval, tpOf]
  congr 1 <;> push_cast [Nat.cast_sub h1c, Nat.cast_sub h1t, Nat.cast_sub h2c, Nat.cast_sub h2t] <;> ring_nf

































example : ∀ i k : Fin 3, (10000 : ℤ) * (TP.mk 119 48 12 133505 133506 133507).ray i k ≤
    7614 * (TP.mk 136 55 14 133505 133506 133507).ray i k := by
  decide +kernel

end Low6969GateBilinear

end Merged_Low6969GateTheta

-- merged module Low6969GateGlueT
section Merged_Low6969GateGlueT

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Low6969GateCell
open Low6969GateFreeCard (mx mn mx_eq mn_eq)
open K1_13 (Row Shape shape InBox)
open Low6969GateBilinear (tpOf TP)
open Low6969SharedPrice (coord)

def Gt.mat (G : Gt) (i k : Fin 3) : ℤ :=
  ![![(G.m00 : ℤ), G.m01, G.m02], ![(G.m01 : ℤ), G.m11, G.m12], ![(G.m02 : ℤ), G.m12, G.m22]] i k




















open K1_13 (Shape)
open Low6969GateBilinear (TP tpOf)

/-- A gate matrix can be certified on a different upper chart. The priced
factor only needs its own chart formula and the nine cross-chart inequalities. -/
theorem tilted_le_saved_matrix (G : Gt) (px q1 q2 : Shape) (num den : ℕ) (hd : 0<den)
    (hbx : px.j+1≤px.b) (hjx : 2≤px.j) (k hx1 hx2 : ℕ)
    (hk : Low6969Prices.taylorLength-4=k)
    (hh1 : (Low6969Prices.bentLift k px).2=hx1)
    (hh2 : (Low6969Prices.bentLift (k+1) px).2=hx2)
    (upper : TP) (matrix : ∀ i j,upper.ray i j=Gt.mat G i j)
    (rays : ∀ i j,(den:ℤ)*(tpOf px k hx1 hx2).ray i j≤num*upper.ray i j)
    (c1 : q1.j≤q1.b ∧ 3*q1.t≤q1.j) (c2 : q2.j≤q2.b ∧ 3*q2.t≤q2.j) :
    (Low6969Gate.tiltedPair px q1 q2:ℚ)≤(num:ℚ)/den*(TT G q1.b q1.j q1.t q2.b q2.j q2.t:ℚ) := by
  let a : ℤ := (q1.b-q1.j:ℕ)
  let b : ℤ := (q1.j-3*q1.t:ℕ)
  let d : ℤ := (q2.b-q2.j:ℕ)
  let e : ℤ := (q2.j-3*q2.t:ℕ)
  have price : upper.cone a b q1.t d e q2.t=(TT G q1.b q1.j q1.t q2.b q2.j q2.t:ℤ) := by
    rw [Low6969GateBilinear.cone_expand]
    simp only [matrix,Gt.mat,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.isValue]
    unfold TT a b d e
    push_cast
    ring
  have compare:=Low6969GateBilinear.theta_cone _ upper num den rays a b q1.t d e q2.t
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [price] at compare
  rw [Low6969GateBilinear.tiltedPair_cone px q1 q2 hbx hjx k hx1 hx2 hk hh1 hh2 c1.1 c1.2 c2.1 c2.2]
  let x:ℤ:=(tpOf px k hx1 hx2).cone a b q1.t d e q2.t
  let y:=TT G q1.b q1.j q1.t q2.b q2.j q2.t
  change (x.toNat:ℚ)≤(num:ℚ)/den*y
  change (den:ℤ)*x≤num*(y:ℤ) at compare
  rw [div_mul_eq_mul_div,le_div_iff₀ (by exact_mod_cast hd : (0:ℚ)<den)]
  by_cases hx : 0≤x
  · have xi : (x.toNat:ℤ)=x:=Int.toNat_of_nonneg hx
    have cost : (x.toNat:ℤ)*den≤num*(y:ℤ) := by simpa only [xi,mul_comm x] using compare
    exact_mod_cast cost
  · simpa only [Int.toNat_eq_zero.mpr (by omega : x≤0),Nat.cast_zero,zero_mul] using
      (mul_nonneg (Nat.cast_nonneg num : (0:ℚ)≤num) (Nat.cast_nonneg y))


theorem Tt_le (G : Gt) (ph px q1 q2 : Shape) (num den : ℕ) (hden : 0 < den)
    (hbh : ph.j + 1 ≤ ph.b) (hjh : 2 ≤ ph.j) (hbx : px.j + 1 ≤ px.b) (hjx : 2 ≤ px.j) (k h1 h2 hx1 hx2 : ℕ)
    (hk : Low6969Prices.taylorLength - 4 = k) (hh1 : (Low6969Prices.bentLift 133446 ph).2 = h1)
    (hh2 : (Low6969Prices.bentLift 133447 ph).2 = h2) (hx1' : (Low6969Prices.bentLift k px).2 = hx1)
    (hx2' : (Low6969Prices.bentLift (k + 1) px).2 = hx2)
    (hM : ∀ i k', (tpOf ph 133446 h1 h2).ray i k' = Gt.mat G i k')
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (tpOf px k hx1 hx2).ray i k' ≤ num * (tpOf ph 133446 h1 h2).ray i k')
    (c1 : q1.j ≤ q1.b ∧ 3 * q1.t ≤ q1.j) (c2 : q2.j ≤ q2.b ∧ 3 * q2.t ≤ q2.j) :
    (Low6969Gate.tiltedPair px q1 q2 : ℚ) ≤ (num : ℚ) / den * (TT G q1.b q1.j q1.t q2.b q2.j q2.t : ℚ) := by
  exact tilted_le_saved_matrix G px q1 q2 num den hden hbx hjx k hx1 hx2 hk hx1' hx2'
    (tpOf ph 133446 h1 h2) hM hθ c1 c2

theorem alg (tp1 tp2 tp3 tp4 tp5 T1 T2 Txe TXe Txq TXq Txs ts N cc ρ v AA AX : ℚ)
    (hc0 : 0 ≤ cc) (hc1 : cc ≤ 1) (hρ : 0 ≤ ρ) (hv : 0 ≤ v) (hN : 0 ≤ N)
    (t1 : tp1 ≤ N * T1) (t2 : tp2 ≤ N * T2) (t3 : tp3 ≤ N * Txe) (t4 : tp4 ≤ N * Txq) (t5 : tp5 ≤ N * Txs)
    (m3 : Txe ≤ TXe) (m4 : Txq ≤ TXq) (m5 : Txs ≤ ts)
    (core : (1 - cc) * T1 + T2 + ρ * TXe + cc * ρ * TXq + v * ρ ^ 2 * ts ≤ 1920 * AA * ρ ^ 2)
    (hA : N * AA ≤ AX) :
    (1 - cc) * (tp1 / 1920) + tp2 / 1920 + ρ * (tp3 / 1920) + cc * ρ * (tp4 / 1920) + v * ρ ^ 2 * (tp5 / 1920) ≤ AX * ρ ^ 2 := by
  have u1 := mul_le_mul_of_nonneg_left t1 (sub_nonneg.mpr hc1)
  have u3 := mul_le_mul_of_nonneg_left t3 hρ
  have u4 := mul_le_mul_of_nonneg_left t4 (mul_nonneg hc0 hρ)
  have u5 := mul_le_mul_of_nonneg_left t5 (mul_nonneg hv (sq_nonneg ρ))
  have w3 := mul_le_mul_of_nonneg_left m3 (mul_nonneg hN hρ)
  have w4 := mul_le_mul_of_nonneg_left m4 (mul_nonneg hN (mul_nonneg hc0 hρ))
  have w5 := mul_le_mul_of_nonneg_left m5 (mul_nonneg hN (mul_nonneg hv (sq_nonneg ρ)))
  have hc := mul_le_mul_of_nonneg_left core hN
  have hA' := mul_le_mul_of_nonneg_right hA (sq_nonneg ρ)
  nlinarith [u1, u3, u4, u5, w3, w4, w5, hc, hA', t2]

theorem rhs_le_tilted (f : Row 4) (G : Gt) (hG : G.Ok) (hlift : G.lift = false) (hsc : G.sc = 1920)
    (hxt : 3 * G.xt ≤ G.xj) (hbh : G.xj + 1 ≤ G.xb) (hjh : 2 ≤ G.xj)
    (hlo : G.lb ≤ (shape f).b ∧ G.lj ≤ (shape f).j ∧ G.lt ≤ (shape f).t)
    (hhi : (shape f).b ≤ G.xb ∧ (shape f).j ≤ G.xj ∧ (shape f).t ≤ G.xt)
    (htf : 3 * (shape f).t + 3 ≤ (shape f).j ∧ (shape f).j + 1 ≤ (shape f).b)
    (k h1 h2 hx1 hx2 : ℕ) (hk : Low6969Prices.taylorLength - 4 = k)
    (hh1 : (Low6969Prices.bentLift 133446 ⟨G.xb, G.xj, G.xt⟩).2 = h1)
    (hh2 : (Low6969Prices.bentLift 133447 ⟨G.xb, G.xj, G.xt⟩).2 = h2)
    (hx1' : (Low6969Prices.bentLift k (shape f)).2 = hx1) (hx2' : (Low6969Prices.bentLift (k + 1) (shape f)).2 = hx2)
    (hM : ∀ i k', (tpOf ⟨G.xb, G.xj, G.xt⟩ 133446 h1 h2).ray i k' = Gt.mat G i k')
    (num den Ax : ℕ) (hden : 0 < den)
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (tpOf (shape f) k hx1 hx2).ray i k' ≤ num * (tpOf ⟨G.xb, G.xj, G.xt⟩ 133446 h1 h2).ray i k')
    (hA : num * G.A ≤ den * Ax)
    (qs : Shape) (hqs : qs = ⟨G.sep.1, G.sep.2.1, G.sep.2.2⟩)
    (r a cn vn W : ℕ) (B η : Fin 3 → ℕ) (hρ : a < r) (hcn : cn ≤ 2 * (r - a))
    (hI : lhsV (mkPr G r a cn vn W (B 0) (B 1) (B 2)) (B 0 - a * G.lb - η 0) (B 1 - a * G.lj - η 1)
      (B 2 - a * G.lt - η 2) (η 0) (η 1) (η 2) ≤ (mkPr G r a cn vn W (B 0) (B 1) (B 2)).rhs) :
    Low6969GateFinal.rhs f qs r a ((cn : ℚ) / (2 * ((r - a : ℕ) : ℚ))) ((vn : ℚ) / 10000000) B η ≤
      (Ax : ℚ) * ((r - a : ℕ) : ℚ) ^ 2 := by
  have hpx : (shape f).chamber = shape f := by
    have : max (shape f).b (shape f).j = (shape f).b := max_eq_left (by omega)
    cases hsh : shape f with
    | mk b j t => simp only [hsh] at this htf ⊢; simp only [K1_13.Shape.chamber, this]
  set Yb : Fin 3 → ℕ := fun i => B i - (a * coord (shape f) i + η i) with hYb
  have hy0 : Yb 0 ≤ B 0 - a * G.lb - η 0 := by
    show B 0 - (a * (shape f).b + η 0) ≤ _
    have := Nat.mul_le_mul_left a hlo.1; omega
  have hy1 : Yb 1 ≤ B 1 - a * G.lj - η 1 := by
    show B 1 - (a * (shape f).j + η 1) ≤ _
    have := Nat.mul_le_mul_left a hlo.2.1; omega
  have hy2 : Yb 2 ≤ B 2 - a * G.lt - η 2 := by
    show B 2 - (a * (shape f).t + η 2) ≤ _
    have := Nat.mul_le_mul_left a hlo.2.2; omega
  have core := core G hG hxt r a cn vn W (B 0) (B 1) (B 2) hρ hcn hy0 hy1 hy2 hI
  rw [hlift] at core
  simp only [hB, hJ, hT, Bool.cond_false, mx_eq, mn_eq] at core
  unfold Low6969GateFinal.rhs Low6969GateFinal.Tt
  simp only [hpx]
  have hq : Low6969GateFinal.boxOf Yb = ⟨max (Yb 0) (Yb 1), Yb 1, min (Yb 2) (Yb 1 / 3)⟩ := rfl
  have he : Low6969GateFinal.boxOf η = ⟨max (η 0) (η 1), η 1, min (η 2) (η 1 / 3)⟩ := rfl
  have cq := Low6969GateFinal.boxOf_chamber Yb
  have ce := Low6969GateFinal.boxOf_chamber η
  have cqs : qs.j ≤ qs.b ∧ 3 * qs.t ≤ qs.j := by
    subst hqs
    simp only [Gt.sep, hlift, hB, hJ, hT, Bool.cond_false, mx_eq, mn_eq]
    refine ⟨le_max_right _ _, ?_⟩
    have := Nat.min_le_right (G.xt - 1) ((G.xj - 3) / 3)
    omega
  have hρpos : (0 : ℚ) ≤ ((r - a : ℕ) : ℚ) := Nat.cast_nonneg _
  have hcc0 : (0 : ℚ) ≤ (cn : ℚ) / (2 * ((r - a : ℕ) : ℚ)) := by positivity
  have hcc1 : (cn : ℚ) / (2 * ((r - a : ℕ) : ℚ)) ≤ 1 := by
    have hpos : (0 : ℚ) < 2 * ((r - a : ℕ) : ℚ) := by
      have : (0 : ℚ) < ((r - a : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hρ
      linarith
    rw [div_le_one hpos]; exact_mod_cast hcn
  have hv0 : (0 : ℚ) ≤ (vn : ℚ) / 10000000 := by positivity
  have T := fun (q1 q2 : Shape) (c1 : q1.j ≤ q1.b ∧ 3 * q1.t ≤ q1.j) (c2 : q2.j ≤ q2.b ∧ 3 * q2.t ≤ q2.j) =>
    Tt_le G ⟨G.xb, G.xj, G.xt⟩ (shape f) q1 q2 num den hden hbh hjh (by omega) (by omega) k h1 h2 hx1 hx2 hk hh1 hh2
      hx1' hx2' hM hθ c1 c2
  have cx : (shape f).j ≤ (shape f).b ∧ 3 * (shape f).t ≤ (shape f).j := ⟨by omega, by omega⟩
  have cX : Cone (mx G.xb G.xj) G.xj G.xt := ⟨by rw [mx_eq]; exact le_max_right _ _, hxt⟩
  have cxC : Cone (shape f).b (shape f).j (shape f).t := cx
  have mxle : (shape f).b ≤ mx G.xb G.xj := by rw [mx_eq]; exact hhi.1.trans (le_max_left _ _)
  have t1 := T _ _ ⟨cq.1, cq.2.1⟩ ⟨cq.1, cq.2.1⟩
  have t2 := T _ _ ⟨ce.1, ce.2.1⟩ ⟨cq.1, cq.2.1⟩
  have t3 := T _ _ cx ⟨ce.1, ce.2.1⟩
  have t4 := T _ _ cx ⟨cq.1, cq.2.1⟩
  have t5 := T _ _ cx cqs
  have m3 : TT G (shape f).b (shape f).j (shape f).t (Low6969GateFinal.boxOf η).b (Low6969GateFinal.boxOf η).j (Low6969GateFinal.boxOf η).t ≤
      TT G (mx G.xb G.xj) G.xj G.xt (Low6969GateFinal.boxOf η).b (Low6969GateFinal.boxOf η).j (Low6969GateFinal.boxOf η).t :=
    TT_mono_left G hG cxC cX ⟨ce.1, ce.2.1⟩ mxle hhi.2.1 hhi.2.2
  have m4 : TT G (shape f).b (shape f).j (shape f).t (Low6969GateFinal.boxOf Yb).b (Low6969GateFinal.boxOf Yb).j (Low6969GateFinal.boxOf Yb).t ≤
      TT G (mx G.xb G.xj) G.xj G.xt (Low6969GateFinal.boxOf Yb).b (Low6969GateFinal.boxOf Yb).j (Low6969GateFinal.boxOf Yb).t :=
    TT_mono_left G hG cxC cX ⟨cq.1, cq.2.1⟩ mxle hhi.2.1 hhi.2.2
  have m5 : TT G (shape f).b (shape f).j (shape f).t qs.b qs.j qs.t ≤ G.tsep := by
    subst hqs
    exact TT_mono_left G hG cxC cX cqs mxle hhi.2.1 hhi.2.2
  have hN : (0 : ℚ) ≤ (num : ℚ) / den := by positivity
  simp only [Low6969GateFinal.boxOf] at t1 t2 t3 t4 t5 m3 m4 ⊢
  have hA' : (num : ℚ) / den * G.A ≤ Ax := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by exact_mod_cast hden)]
    exact_mod_cast (by linarith [hA] : num * G.A ≤ Ax * den)
  rw [hsc] at core
  push_cast at core
  simp only [hYb] at t1 t2 t4 m4 core
  simp only [mx_eq] at m3 m4
  exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcc0 hcc1 hρpos hv0 hN t1 t2 t3 t4 t5
    (Nat.cast_le.mpr m3) (Nat.cast_le.mpr m4) (Nat.cast_le.mpr m5) core hA'

end Low6969GateCell

end Merged_Low6969GateGlueT

-- merged module Low6969GateGateT
section Merged_Low6969GateGateT

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace Low6969GateCell
open P3 (K)
open K1_13 (Row Shape shape InBox)
open Low6969GateBilinear (tpOf)
open Low6969GateFreeCard (mx)
open Low6969SharedPrice (coord)
open Low6969GateCertCF (cvOf cvOf_le certF certF_bounds certF_class)
open scoped Polynomial BigOperators

theorem sum_tail (lv : Lv) (n : ℕ) (hn : n = lv.length) (L : ℕ) (hL : n ≤ L) (F : ℕ → ℕ)
    (hF : ∀ i, n ≤ i → F i = 0) : ∑ i ∈ Finset.range L, F i = ∑ i ∈ Finset.range n, F i := by
  symm
  apply Finset.sum_subset (Finset.range_mono hL)
  intro i _ hi
  exact hF i (by simpa using hi)

theorem hI_of_free (G : Gt) (hG : G.Ok) (hx : 3 * G.xt ≤ G.xj) (hpos : 0 < G.lb ∧ 0 < G.lj ∧ 0 < G.lt)
    (r0 : ℕ) (ws : List ℕ) (lv : Lv) (n : ℕ) (hn : n = lv.length) (hr0 : r0 + ws.length ≤ n + 1)
    (hall : allOK G r0 ws lv 0 n = true)
    (ρ0 amax : ℕ) (hρ0 : 0 < ρ0) (hru : ρ0 + amax ≤ n + 1)
    (hamax : ∀ a, a * G.lb ≤ 4012 → a * G.lj ≤ 1650 → a * G.lt ≤ 550 → a ≤ amax)
    (hS0 : G.tsep ≤ G.sc * G.A * VD)
    (hS1 : 2 * VD * TT G (mx G.xb G.xj) G.xj G.xt 4012 1650 550 ≤ (G.sc * G.A * VD - G.tsep) * ρ0)
    (hS2 : 2 * VD * TT G (mx G.xb G.xj) G.xj G.xt 4012 1650 550 * ρ0 +
        VD * (2 * TT G 4012 1650 550 4012 1650 550 + amax * amax * G.tsep) ≤ (G.sc * G.A * VD - G.tsep) * (ρ0 * ρ0))
    (i : ℕ) (x : Fin 3 → ℕ) (hxl : G.lb ≤ x 0 ∧ G.lj ≤ x 1 ∧ G.lt ≤ x 2) (a : ℕ) (η : Fin 3 → ℕ)
    (hfit : ∀ k, a * x k + η k ≤ Bof lv i k) (hv : η 2 ≤ η 0 ∧ 3 * η 2 ≤ η 1 ∧ η 1 ≤ 2 * η 0 + η 2)
    (hfree : Wof lv i < Low6969GateShape.free (fun k => Bof lv i k - (a * x k + η k))) :
    a < i + 1 ∧ lhsV (mkPr G (i + 1) a (cvOf r0 ws (i + 1) a).1 (cvOf r0 ws (i + 1) a).2 (Wof lv i)
        (Bof lv i 0) (Bof lv i 1) (Bof lv i 2)) (Bof lv i 0 - a * G.lb - η 0) (Bof lv i 1 - a * G.lj - η 1)
        (Bof lv i 2 - a * G.lt - η 2) (η 0) (η 1) (η 2) ≤
      (mkPr G (i + 1) a (cvOf r0 ws (i + 1) a).1 (cvOf r0 ws (i + 1) a).2 (Wof lv i)
        (Bof lv i 0) (Bof lv i 1) (Bof lv i 2)).rhs := by
  by_cases hi : i < n
  · have hok := allOK_get G r0 ws lv n hall i hi
    unfold okAt at hok
    have hB0 : Bof lv i 0 = (lv.getD i dflt).1 := rfl
    have hB1 : Bof lv i 1 = (lv.getD i dflt).2.1 := rfl
    have hB2 : Bof lv i 2 = (lv.getD i dflt).2.2.1 := rfl
    have hfree' : (lv.getD i dflt).2.2.2 < Low6969GateShape.free
        (fun k => ![(lv.getD i dflt).1, (lv.getD i dflt).2.1, (lv.getD i dflt).2.2.1] k - (a * x k + η k)) := hfree
    have hfit' : ∀ k, a * x k + η k ≤ ![(lv.getD i dflt).1, (lv.getD i dflt).2.1, (lv.getD i dflt).2.2.1] k := hfit
    obtain ⟨hlt, c, hc, hle⟩ := level_sound G hG hx hpos (i + 1) _ _ _ _ 80 (fun a => some (cvOf r0 ws (i + 1) a))
      (fun a c hc => by simp only [Option.some.injEq] at hc; subst hc; exact cvOf_le r0 ws (i + 1) a) hok x hxl a η
      hfit' hv hfree'
    simp only [Option.some.injEq] at hc
    subst hc
    exact ⟨hlt, by simpa [Wof, hB0, hB1, hB2] using hle⟩
  · have hge : n ≤ i := by omega
    have hd : lv.getD i dflt = dflt := by
      rw [List.getD_eq_default]; omega
    have hB0 : Bof lv i 0 = 4012 := by unfold Bof; simp only [hd]; rfl
    have hB1 : Bof lv i 1 = 1650 := by unfold Bof; simp only [hd]; rfl
    have hB2 : Bof lv i 2 = 550 := by unfold Bof; simp only [hd]; rfl
    have hW0 : Wof lv i = 0 := by unfold Wof; simp only [hd]; rfl
    have f0 := hfit 0
    have f1 := hfit 1
    have f2 := hfit 2
    rw [hB0] at f0
    rw [hB1] at f1
    rw [hB2] at f2
    have l0 := Nat.mul_le_mul_left a hxl.1
    have l1 := Nat.mul_le_mul_left a hxl.2.1
    have l2 := Nat.mul_le_mul_left a hxl.2.2
    have ha : a ≤ amax := hamax a (by nlinarith) (by nlinarith) (by nlinarith)
    have hlt : a < i + 1 := by omega
    refine ⟨hlt, ?_⟩
    rw [hB0, hB1, hB2, hW0]
    have hρ : ρ0 ≤ i + 1 - a := by omega
    have key := tail_ok G hG hx (i + 1 - a) (cvOf r0 ws (i + 1) a).1 (cvOf r0 ws (i + 1) a).2 a amax ρ0 hρ hρ0
      (by have := cvOf_le r0 ws (i + 1) a; omega)
      (cvOf_tail r0 ws (i + 1) a amax (by omega) ha hlt) ha hS0 hS1 hS2
      (yb := 4012 - a * G.lb - η 0) (yj := 1650 - a * G.lj - η 1) (yt := 550 - a * G.lt - η 2)
      (hb := η 0) (hj := η 1) (ht := η 2) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [lhsV_eq]
    exact key

theorem hsum_of (lv : Lv) (n : ℕ) (hn : n = lv.length) (hL : n ≤ Low6969GateFinal.levelCount)
    (hs : (∑ i ∈ Finset.range n, lsum lv i) < Low6969Prices.layerNeed) :
    ∑ i ∈ Finset.range Low6969GateFinal.levelCount,
      (Low6969Prices.symbolCount - Low6969GateBox.ambCount (Bof lv i 0) (Bof lv i 1) (Bof lv i 2) + Wof lv i) <
      Low6969Prices.layerNeed := by
  rw [sum_tail lv n hn _ hL]
  · have : ((∑ i ∈ Finset.range n, (Low6969Prices.symbolCount - Low6969GateBox.ambCount (Bof lv i 0) (Bof lv i 1)
        (Bof lv i 2) + Wof lv i) : ℕ) : ℤ) ≤ ∑ i ∈ Finset.range n, ((Low6969Prices.symbolCount : ℤ) -
        ambLB (lv.getD i dflt).1 (lv.getD i dflt).2.1 (lv.getD i dflt).2.2.1 + (Wof lv i : ℤ)) := by
      push_cast
      apply Finset.sum_le_sum
      intro i _
      have h1 := ambLB_le (lv.getD i dflt).1 (lv.getD i dflt).2.1 (lv.getD i dflt).2.2.1
      have h2 := Low6969GateAmb.amb_le (Bof lv i 0) (Bof lv i 1) (Bof lv i 2)
      have e : Low6969GateBox.ambCount (Bof lv i 0) (Bof lv i 1) (Bof lv i 2) =
          Low6969GateBox.ambCount (lv.getD i dflt).1 (lv.getD i dflt).2.1 (lv.getD i dflt).2.2.1 := rfl
      rw [e] at h2 ⊢
      push_cast [Nat.cast_sub h2]
      linarith
    have h3 := lt_of_le_of_lt this hs
    exact_mod_cast h3
  · intro i hi
    have hd : lv.getD i dflt = dflt := by rw [List.getD_eq_default]; omega
    have hB0 : Bof lv i 0 = 4012 := by unfold Bof; simp only [hd]; rfl
    have hB1 : Bof lv i 1 = 1650 := by unfold Bof; simp only [hd]; rfl
    have hB2 : Bof lv i 2 = 550 := by unfold Bof; simp only [hd]; rfl
    have hW0 : Wof lv i = 0 := by unfold Wof; simp only [hd]; rfl
    rw [hB0, hB1, hB2, hW0, Low6969GateAmb.amb_full 4012 1650 550 le_rfl le_rfl le_rfl]
    simp

theorem price_T {w : P3.I → K} {Γ : Finset K} {s : K → (Polynomial K)} {f : Row 4} {l : ℕ}
    (hm : Low6969Prices.Messages w Γ s) (hf : Low6969Prices.SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (hl : 0 < l)
    (hproper : Low6969Prices.ProperCut f Γ s l) (hchar : f.degreeOf 3 < K1.p)
    (htf : 3 * (shape f).t + 3 ≤ (shape f).j ∧ (shape f).j + 1 ≤ (shape f).b)
    (G : Gt) (hG : G.Ok) (hlift : G.lift = false) (hsc : G.sc = 1920)
    (hxt : 3 * G.xt ≤ G.xj) (hbh : G.xj + 1 ≤ G.xb) (hjh : 2 ≤ G.xj)
    (hpos : 0 < G.lb ∧ 0 < G.lj ∧ 0 < G.lt)
    (hlo : G.lb ≤ (shape f).b ∧ G.lj ≤ (shape f).j ∧ G.lt ≤ (shape f).t)
    (hhi : (shape f).b ≤ G.xb ∧ (shape f).j ≤ G.xj ∧ (shape f).t ≤ G.xt)
    (k h1 h2 hx1 hx2 : ℕ) (hk : Low6969Prices.taylorLength - 4 = k)
    (hh1 : (Low6969Prices.bentLift 133446 ⟨G.xb, G.xj, G.xt⟩).2 = h1)
    (hh2 : (Low6969Prices.bentLift 133447 ⟨G.xb, G.xj, G.xt⟩).2 = h2)
    (hx1' : (Low6969Prices.bentLift k (shape f)).2 = hx1) (hx2' : (Low6969Prices.bentLift (k + 1) (shape f)).2 = hx2)
    (hM : ∀ i k', (tpOf ⟨G.xb, G.xj, G.xt⟩ 133446 h1 h2).ray i k' = Gt.mat G i k')
    (num den Ax : ℕ) (hden : 0 < den)
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (tpOf (shape f) k hx1 hx2).ray i k' ≤ num * (tpOf ⟨G.xb, G.xj, G.xt⟩ 133446 h1 h2).ray i k')
    (hA : num * G.A ≤ den * Ax)
    (r0 : ℕ) (ws : List ℕ) (ht : Low6969GateClassTable.tableOK r0 ws = true) (lv : Lv) (n : ℕ) (hn : n = lv.length)
    (hr0 : r0 + ws.length ≤ n + 1) (hL : n ≤ Low6969GateFinal.levelCount)
    (hall : allOK G r0 ws lv 0 n = true)
    (ρ0 amax : ℕ) (hρ0 : 0 < ρ0) (hru : ρ0 + amax ≤ n + 1)
    (hamax : ∀ a, a * G.lb ≤ 4012 → a * G.lj ≤ 1650 → a * G.lt ≤ 550 → a ≤ amax)
    (hS0 : G.tsep ≤ G.sc * G.A * VD)
    (hS1 : 2 * VD * TT G (mx G.xb G.xj) G.xj G.xt 4012 1650 550 ≤ (G.sc * G.A * VD - G.tsep) * ρ0)
    (hS2 : 2 * VD * TT G (mx G.xb G.xj) G.xj G.xt 4012 1650 550 * ρ0 +
        VD * (2 * TT G 4012 1650 550 4012 1650 550 + amax * amax * G.tsep) ≤ (G.sc * G.A * VD - G.tsep) * (ρ0 * ρ0))
    (hs : (∑ i ∈ Finset.range n, lsum lv i) < Low6969Prices.layerNeed) :
    Γ.card ≤ Ax + Low6969SharedPrice.additiveBase (shape f) l + Low6969SharedPrice.nonsharedFee (shape f) l := by
  have hf0 : f ≠ 0 := hf.1.ne_zero
  have htpos : 0 < f.degreeOf 3 := by
    have : (shape f).t = f.degreeOf 3 := rfl
    omega
  have hnd : ¬ f ∣ K1_13_6.separant f := KoalaFarBridge.separant_proper hf0 htpos hchar
  have sb := KoalaFarBridge.separant_box f
  set qs : Shape := ⟨G.sep.1, G.sep.2.1, G.sep.2.2⟩ with hqs
  have hsep : G.sep = (mx (G.xb - 1) (G.xj - 3), G.xj - 3, Low6969GateFreeCard.mn (G.xt - 1) ((G.xj - 3) / 3)) := by
    simp only [Gt.sep, hlift, hB, hJ, hT, Bool.cond_false]
  have hbs : InBox (shape (K1_13_6.separant f)) qs := by
    refine ⟨?_, ?_, ?_⟩
    · have := sb.1
      simp only [hqs, hsep, Low6969GateFreeCard.mx_eq]
      exact this.trans ((Nat.sub_le_sub_right hhi.1 1).trans (le_max_left _ _))
    · have := sb.2.1
      simp only [hqs, hsep]
      exact this.trans (Nat.sub_le_sub_right hhi.2.1 3)
    · have := sb.2.2
      simp only [hqs, hsep, Low6969GateFreeCard.mn_eq]
      refine this.trans (le_min (Nat.sub_le_sub_right hhi.2.2 1) ?_)
      refine (Nat.le_div_iff_mul_le (by norm_num)).mpr ?_
      have h5 := htf.1; have h6 := hhi.2.1; show ((shape f).t - 1) * 3 ≤ G.xj - 3; omega
  have hcs : Low48BentLattice.Chamber (qs, 0) := by
    refine ⟨?_, ?_, Nat.zero_le _⟩
    · simp only [hqs, hsep, Low6969GateFreeCard.mx_eq]; exact le_max_right _ _
    · simp only [hqs, hsep, Low6969GateFreeCard.mn_eq]
      have := Nat.min_le_right (G.xt - 1) ((G.xj - 3) / 3)
      omega
  have hxl : G.lb ≤ coord (shape f) 0 ∧ G.lj ≤ coord (shape f) 1 ∧ G.lt ≤ coord (shape f) 2 := hlo
  have hsum := hsum_of lv n hn hL hs
  refine Low6969GateFinal.two_cut_price_tilted hm hf hon hl hproper (by exact ⟨htf.1, htf.2⟩) qs hbs hcs hnd Ax (Bof lv) (Wof lv)
    (certF r0 ws) (fun r a => (certF_bounds r0 ws r a).1) (fun r a => (certF_bounds r0 ws r a).2.1)
    (fun r a => (certF_bounds r0 ws r a).2.2) ?_ hsum
  intro i _ a η hfit hv hng
  by_contra hfree
  push_neg at hfree
  obtain ⟨hlt, hI⟩ := hI_of_free G hG hxt hpos r0 ws lv n hn hr0 hall ρ0 amax hρ0 hru hamax hS0 hS1 hS2 i
    (fun k => coord (shape f) k) hxl a η hfit hv hfree
  have hc : (cvOf r0 ws (i + 1) a).1 ≤ 2 * (i + 1 - a) := cvOf_le r0 ws (i + 1) a
  have hr := rhs_le_tilted f G hG hlift hsc hxt hbh hjh hlo hhi htf k h1 h2 hx1 hx2 hk hh1 hh2 hx1' hx2' hM num den Ax hden
    hθ hA qs hqs (i + 1) a _ _ (Wof lv i) (Bof lv i) η hlt hc hI
  exact hng ⟨hlt, certF_class ht hlt, hr⟩

end Low6969GateCell

end Merged_Low6969GateGateT

end Merged_Low6969GateGateT

-- merged module Low6969GateThetaOrd
section Merged_Low6969GateThetaOrd

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option Elab.async false

namespace Low6969GateBilinear

open K1_13

def No (z1 z2 z3 w1 w2 w3 x1 x2 x3 y1 y2 y3 : ℤ) : ℤ :=
  (0) * x1 * y1
  + (16*(w2*z3 + w3*z2 - 3*w3*z3)) * x1 * y2
  + (16*(w2 - 3*w3)*(z2 - 3*z3)) * x1 * y3
  + (16*(w2*z3 + w3*z2 - 3*w3*z3)) * x2 * y1
  + (8*(2*w1*z3 - 3*w2*z3 + 2*w3*z1 - 3*w3*z2 + 7*w3*z3)) * x2 * y2
  + (8*(2*w1*z2 - 6*w1*z3 + 2*w2*z1 - 3*w2*z2 + 7*w2*z3 - 6*w3*z1 + 7*w3*z2 - 15*w3*z3)) * x2 * y3
  + (16*(w2 - 3*w3)*(z2 - 3*z3)) * x3 * y1
  + (8*(2*w1*z2 - 6*w1*z3 + 2*w2*z1 - 3*w2*z2 + 7*w2*z3 - 6*w3*z1 + 7*w3*z2 - 15*w3*z3)) * x3 * y2
  + (-8*(6*w1*z2 - 18*w1*z3 + 6*w2*z1 - 7*w2*z2 + 15*w2*z3 - 18*w3*z1 + 15*w3*z2 - 27*w3*z3)) * x3 * y3

theorem mixed32_formula (x y z w : Shape) :
    mixed32 x y z w = (No z.b z.j z.t w.b w.j w.t x.b x.j x.t y.b y.j y.t).toNat := by
  obtain ⟨x1, x2, x3⟩ := x
  obtain ⟨y1, y2, y3⟩ := y
  obtain ⟨z1, z2, z3⟩ := z
  obtain ⟨w1, w2, w3⟩ := w
  unfold mixed32
  congr 1
  simp only [difference, volume32, Shape.plus, No]
  push_cast
  ring

structure OP where
  z1 : ℤ
  z2 : ℤ
  z3 : ℤ
  w1 : ℤ
  w2 : ℤ
  w3 : ℤ

def OP.cone (P : OP) (c1 c2 c3 d1 d2 d3 : ℤ) : ℤ :=
  No P.z1 P.z2 P.z3 P.w1 P.w2 P.w3 (c1 + c2 + 3*c3) (c2 + 3*c3) c3 (d1 + d2 + 3*d3) (d2 + 3*d3) d3

def OP.ray (P : OP) (i k : Fin 3) : ℤ :=
  P.cone (if i = 0 then 1 else 0) (if i = 1 then 1 else 0) (if i = 2 then 1 else 0)
    (if k = 0 then 1 else 0) (if k = 1 then 1 else 0) (if k = 2 then 1 else 0)

theorem ocone_expand (P : OP) (c1 c2 c3 d1 d2 d3 : ℤ) :
    P.cone c1 c2 c3 d1 d2 d3 =
      c1*d1 * P.ray 0 0 + c1*d2 * P.ray 0 1 + c1*d3 * P.ray 0 2 +
      c2*d1 * P.ray 1 0 + c2*d2 * P.ray 1 1 + c2*d3 * P.ray 1 2 +
      c3*d1 * P.ray 2 0 + c3*d2 * P.ray 2 1 + c3*d3 * P.ray 2 2 := by
  simp only [OP.ray, OP.cone, No]
  simp
  ring

theorem otheta_cone (Px Ph : OP) (num den : ℤ)
    (h : ∀ i k : Fin 3, den * Px.ray i k ≤ num * Ph.ray i k)
    (c1 c2 c3 d1 d2 d3 : ℤ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3) :
    den * Px.cone c1 c2 c3 d1 d2 d3 ≤ num * Ph.cone c1 c2 c3 d1 d2 d3 := by
  rw [ocone_expand, ocone_expand]
  have key : ∀ (a b : ℤ) (i k : Fin 3), 0 ≤ a → 0 ≤ b →
      den * ((a*b) * Px.ray i k) ≤ num * ((a*b) * Ph.ray i k) := by
    intro a b i k ha hb
    have := mul_le_mul_of_nonneg_left (h i k) (mul_nonneg ha hb)
    linarith
  have := key c1 d1 0 0 hc1 hd1
  have := key c1 d2 0 1 hc1 hd2
  have := key c1 d3 0 2 hc1 hd3
  have := key c2 d1 1 0 hc2 hd1
  have := key c2 d2 1 1 hc2 hd2
  have := key c2 d3 1 2 hc2 hd3
  have := key c3 d1 2 0 hc3 hd1
  have := key c3 d2 2 1 hc3 hd2
  have := key c3 d3 2 2 hc3 hd3
  linarith

def opOf (z w : Shape) : OP := ⟨z.b, z.j, z.t, w.b, w.j, w.t⟩

theorem mixed32_cone (z w q1 q2 : Shape)
    (h1c : q1.j ≤ q1.b) (h1t : 3 * q1.t ≤ q1.j) (h2c : q2.j ≤ q2.b) (h2t : 3 * q2.t ≤ q2.j) :
    mixed32 q1 q2 z w =
      ((opOf z w).cone ((q1.b - q1.j : ℕ) : ℤ) ((q1.j - 3 * q1.t : ℕ) : ℤ) q1.t
        ((q2.b - q2.j : ℕ) : ℤ) ((q2.j - 3 * q2.t : ℕ) : ℤ) q2.t).toNat := by
  rw [mixed32_formula]
  congr 1
  simp only [OP.cone, opOf]
  congr 1 <;> push_cast [Nat.cast_sub h1c, Nat.cast_sub h1t, Nat.cast_sub h2c, Nat.cast_sub h2t] <;> ring_nf

theorem mixed32_theta (zx wx zh wh q1 q2 : Shape) (num den : ℕ)
    (h : ∀ i k : Fin 3, (den : ℤ) * (opOf zx wx).ray i k ≤ num * (opOf zh wh).ray i k)
    (h1c : q1.j ≤ q1.b) (h1t : 3 * q1.t ≤ q1.j) (h2c : q2.j ≤ q2.b) (h2t : 3 * q2.t ≤ q2.j) :
    den * mixed32 q1 q2 zx wx ≤ num * mixed32 q1 q2 zh wh := by
  rw [mixed32_cone zx wx q1 q2 h1c h1t h2c h2t, mixed32_cone zh wh q1 q2 h1c h1t h2c h2t]
  have := otheta_cone _ _ (num : ℤ) (den : ℤ) h
    ((q1.b - q1.j : ℕ) : ℤ) ((q1.j - 3 * q1.t : ℕ) : ℤ) q1.t
    ((q2.b - q2.j : ℕ) : ℤ) ((q2.j - 3 * q2.t : ℕ) : ℤ) q2.t
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  generalize (opOf zx wx).cone ((q1.b - q1.j : ℕ) : ℤ) ((q1.j - 3 * q1.t : ℕ) : ℤ) q1.t
        ((q2.b - q2.j : ℕ) : ℤ) ((q2.j - 3 * q2.t : ℕ) : ℤ) q2.t = A at this ⊢
  generalize (opOf zh wh).cone ((q1.b - q1.j : ℕ) : ℤ) ((q1.j - 3 * q1.t : ℕ) : ℤ) q1.t
        ((q2.b - q2.j : ℕ) : ℤ) ((q2.j - 3 * q2.t : ℕ) : ℤ) q2.t = B at this ⊢
  have hn : (0:ℤ) ≤ num := by positivity
  have hd : (0:ℤ) ≤ den := by positivity
  have eA : (A.toNat : ℤ) = max A 0 := Int.toNat_eq_max A
  have eB : (B.toNat : ℤ) = max B 0 := Int.toNat_eq_max B
  have : ((den * A.toNat : ℕ) : ℤ) ≤ ((num * B.toNat : ℕ) : ℤ) := by
    push_cast
    rw [eA, eB]
    rcases le_total 0 A with hA | hA <;> rcases le_total 0 B with hB | hB
    · rw [max_eq_left hA, max_eq_left hB]; exact this
    · rw [max_eq_left hA, max_eq_right hB]; nlinarith
    · rw [max_eq_right hA, max_eq_left hB]; nlinarith
    · rw [max_eq_right hA, max_eq_right hB]; simp
  exact_mod_cast this

end Low6969GateBilinear

end Merged_Low6969GateThetaOrd
end Z6969Source2430
