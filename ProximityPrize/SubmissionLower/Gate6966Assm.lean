import ProximityPrize.SubmissionLower.Low6966WeightedTally
import ProximityPrize.SubmissionLower.Low6966SurfaceLinearFour
import ProximityPrize.SubmissionLower.Gate6966Rows
import ProximityPrize.SubmissionLower.Gate6966CertCF
import ProximityPrize.SubmissionLower.Gate6966Gate
import ProximityPrize.SubmissionLower.Gate6966Amb
import ProximityPrize.SubmissionLower.Gate6966Hb
import ProximityPrize.SubmissionLower.Gate6966Tail

set_option Elab.async false

-- merged module Gate6966Count2
section Merged_Gate6966Count2

set_option autoImplicit false
set_option Elab.async false

namespace Gate6966Count2

open P3 (K)
open K1_13 (Row shape)
open K1_13_6 (GeoJets)
open Low6966Prices (Messages SmallFactor ActiveFits ProperCut)
open Low6966GeometryCut (CutInput)
open Low6966SharedTally (Data)
open Low6966SharedTallyNew (tally)
open Low6966SharedPersistent (Persistent)
open scoped Polynomial BigOperators

theorem count₂ {w : P3.I → K} {Γ : Finset K} {s : K → (Polynomial K)}
    (hm : Messages w Γ s) (f : Row 4) (hf : SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (l : ℕ) (hl : 0 < l) (hproper : ProperCut f Γ s l)
    (A : ℕ)
    (hmarks : ∀ (Q : Row 4) (input : CutInput Γ s f Q l)
      (data : Data Γ s f Q l {P | Persistent Γ s P}), tally data data.branches ≤ A) :
    Γ.card ≤ A + Low6966SharedPrice.additiveBase (shape f) l + Low6966SharedPrice.nonsharedFee (shape f) l := by
  classical
  obtain ⟨Q, hQprop, hbox, hweight, hQ, hcontact⟩ := hproper
  have input : CutInput Γ s f Q l :=
    ⟨hm.distinct, hm.degree, hf, hon, hl, hQprop, hbox, hweight, hcontact⟩
  let data : Data Γ s f Q l {P | Persistent Γ s P} := Low6966SharedTally.build _
  obtain ⟨a, c, d, hCard, ha, hc, hd⟩ := Low6966SharedCount.cover_counts hm input data
  have hG := hmarks Q input data
  have hbase := Low6966SharedTallyOld.additive_le hl ha hc hd
  omega

end Gate6966Count2

end Merged_Gate6966Count2

-- merged module Gate6966Final
section Merged_Gate6966Final

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace Gate6966Final

open P3 (K)
open K1_13 (Row Shape shape InBox)
open K1_13_6 (GeoJets toGeneric)
open K1_13_6_1_2 (VanishesTo)
open Low6966SharedPrice (coord)
open Low6966GeometryCut (CutInput)
open Low6966GeometryCut_2 (Branch)
open Low6966SharedTally (Data)
open Low6966SharedTallyNew (tally)
open Low6966SharedPersistent (Persistent)
open Low6966SharedRational (FractionJet toGeometric)
open Low6966SharedShapeRank (ambient contactSpace)
open scoped Polynomial BigOperators

instance infiniteGenericField : Infinite K1_13_6.GenericField :=
  Infinite.of_injective (algebraMap (Polynomial K1_13.Geom) K1_13_6.GenericField)
    (IsFractionRing.injective (Polynomial K1_13.Geom) K1_13_6.GenericField)

def levelCount : ℕ := 1 + Low6966Prices.primaryCutoff / Low6966Prices.layerWidth

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

noncomputable def Tt (p q₁ q₂ : Shape) : ℚ := (Gate6966.tiltedPair p q₁ q₂ : ℚ) / 1920

noncomputable def rhs (f : Row 4) (qs : Shape) (r a : ℕ) (cc v : ℚ) (B η : Fin 3 → ℕ) : ℚ :=
  let p := (shape f).chamber
  let Yb : Fin 3 → ℕ := fun i => B i - (a * coord (shape f) i + η i)
  (1 - cc) * Tt p (boxOf Yb) (boxOf Yb) + Tt p (boxOf η) (boxOf Yb) +
    ((r - a : ℕ) : ℚ) * Tt p (shape f).chamber (boxOf η) +
    cc * ((r - a : ℕ) : ℚ) * Tt p (shape f).chamber (boxOf Yb) +
    v * ((r - a : ℕ) : ℚ) ^ 2 * Tt p (shape f).chamber qs

def GoodAt (A : ℕ) (f : Row 4) (qs : Shape) (r a : ℕ) (cc v : ℚ) (B η : Fin 3 → ℕ) : Prop :=
  a < r ∧ Gate6966TwoCut.ClassCert r a cc v ∧ rhs f qs r a cc v B η ≤ (A : ℚ) * ((r - a : ℕ) : ℚ) ^ 2

theorem exact_order_fun (S : Finset (Ideal GeoJets)) (hS : ∀ P ∈ S, P.IsPrime) {g : GeoJets} (hg : g ≠ 0) :
    ∃ e : Ideal GeoJets → ℕ, ∀ (P : Ideal GeoJets) (hP : P ∈ S),
      @VanishesTo _ _ P (hS P hP) g (e P) ∧ ¬ @VanishesTo _ _ P (hS P hP) g (e P + 1) := by
  classical
  have hex : ∀ P : Ideal GeoJets, ∃ n : ℕ, ∀ hP : P ∈ S,
      @VanishesTo _ _ P (hS P hP) g n ∧ ¬ @VanishesTo _ _ P (hS P hP) g (n + 1) := by
    intro P
    by_cases hP : P ∈ S
    · haveI := hS P hP
      obtain ⟨n, hn⟩ := Gate6966Order.exists_exact_order P hg
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose e he using hex
  exact ⟨e, fun P hP => he P hP⟩

variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}

theorem level_dichotomy (hf : Low6966Prices.SmallFactor f)
    (D : Data Γ s f Q l {P | Persistent Γ s P}) (input : CutInput Γ s f Q l)
    (htilt : Low6966Prices.tiltedFits (shape f))
    (qs : Shape) (hbs : InBox (shape (K1_13_6.separant f)) qs) (hcs : Low48BentLattice.Chamber (qs, 0))
    (hnd : ¬ f ∣ K1_13_6.separant f) (A r : ℕ) (B : Fin 3 → ℕ) (cert : ℕ → ℚ × ℚ)
    (hc0 : ∀ a, 0 ≤ (cert a).1) (hc1 : ∀ a, (cert a).1 ≤ 1) (hv0 : ∀ a, 0 ≤ (cert a).2)
    (U : Submodule K1_13_6.GenericField ↥ambient)
    (hU : U ≤ contactSpace (D.branches.image Branch.surface) r ⊓ Gate6966Box.boxSpace (B 0) (B 1) (B 2))
    (hne : U ≠ ⊥) :
    ∃ (a : ℕ) (η : Fin 3 → ℕ),
      Module.finrank K1_13_6.GenericField U ≤
        Gate6966Shape.free (fun k => B k - (a * coord (shape f) k + η k)) ∧
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
  have hB : ∀ Q' ∈ U', ∀ k, Gate6966Shape.shp k Q' ≤ B k := by
    rintro _ ⟨u, hu, rfl⟩ k
    have := Gate6966Hb.shp_le_of_mem_boxSpace (B 0) (B 1) (B 2) u (hU hu).2 k
    have hk : (![B 0, B 1, B 2] : Fin 3 → ℕ) k = B k := by fin_cases k <;> rfl
    simpa [hk] using this
  obtain ⟨a, H, K1, K2, hH0, hK10, hfH, hfG, hHG, hGG, hQ1, hQ2, hs1, hs2, hdim, hfit, hval⟩ :=
    Gate6966Rows.rows_from_subspace f hfirr hdeg U' hU'ne r S hS hcont B hB
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
    have hmain := Gate6966TwoCut.two_cut_count_tilted D input D.branches (subset_refl _) H K1 K2
      (K1_13_6.separant f) htilt (shape f).chamber (boxOf fun k => coord (shape H) k)
      (boxOf fun k => B k - (a * coord (shape f) k + coord (shape H) k))
      (boxOf fun k => B k - (a * coord (shape f) k + coord (shape H) k)) qs
      (hbox f) (inBox_boxOf (fun k => le_rfl)) (inBox_boxOf hs1) (inBox_boxOf hs2) hbs
      (hch f) (boxOf_chamber _) (boxOf_chamber _) (boxOf_chamber _) hcs r a (cert a).1 (cert a).2
      (hc0 a) (hc1 a) (hv0 a) hcertA e m hf0 hH0 hK10 hf0' hH0' hK10' hsf0 hsf0' hfH hfG hHG hGG hfs
      (fun b hb => he b.surface (hmemS b hb)) (fun b hb => hm' b.surface (hmemS b hb)) rfl
      (fun b hb => hQ1 b.surface (hmemS b hb)) (fun b hb => hQ2 b.surface (hmemS b hb)) hlt.le
    have hρ : (0 : ℚ) < ((r - a : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hlt
    have hN := Gate6966TwoCut.mark_bound_of_good hρ hmain (by exact hrhs)
    have : ((tally D D.branches : ℕ) : ℚ) ≤ (A : ℚ) := by
      simpa [tally] using hN
    exact_mod_cast this

theorem two_cut_price_tilted {w : P3.I → K} (hm : Low6966Prices.Messages w Γ s) (hf : Low6966Prices.SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (hl : 0 < l)
    (hproper : Low6966Prices.ProperCut f Γ s l) (htilt : Low6966Prices.tiltedFits (shape f))
    (qs : Shape) (hbs : InBox (shape (K1_13_6.separant f)) qs) (hcs : Low48BentLattice.Chamber (qs, 0))
    (hnd : ¬ f ∣ K1_13_6.separant f) (A : ℕ) (B : ℕ → Fin 3 → ℕ) (W : ℕ → ℕ)
    (cert : ℕ → ℕ → ℚ × ℚ) (hc0 : ∀ r a, 0 ≤ (cert r a).1) (hc1 : ∀ r a, (cert r a).1 ≤ 1)
    (hv0 : ∀ r a, 0 ≤ (cert r a).2)
    (hW : ∀ i, i < levelCount → ∀ (a : ℕ) (η : Fin 3 → ℕ),
      (∀ k, a * coord (shape f) k + η k ≤ B i k) → (η 2 ≤ η 0 ∧ 3 * η 2 ≤ η 1 ∧ η 1 ≤ 2 * η 0 + η 2) →
      ¬ GoodAt A f qs (i + 1) a (cert (i + 1) a).1 (cert (i + 1) a).2 (B i) η →
        Gate6966Shape.free (fun k => B i k - (a * coord (shape f) k + η k)) ≤ W i)
    (hsum : ∑ i ∈ Finset.range levelCount,
      (Low6966Prices.symbolCount - Gate6966Box.ambCount (B i 0) (B i 1) (B i 2) + W i) < Low6966Prices.layerNeed) :
    Γ.card ≤ A + Low6966SharedPrice.additiveBase (shape f) l + Low6966SharedPrice.nonsharedFee (shape f) l := by
  classical
  unfold levelCount at hW hsum
  refine Gate6966Count2.count₂ hm f hf hon l hl hproper A ?_
  intro Q' input' data'
  set S := data'.branches.image Branch.surface with hSdef
  have hpers : ∀ P ∈ S, Persistent Γ s P := by
    intro P hP
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
    exact data'.allowed b hb
  have hneed := Low6966SharedShapeRank.bank_layers hm S hpers
  refine @Gate6966Gate.gate₂_of_need K1_13_6.GenericField (↥ambient) ℕ inferInstance inferInstance inferInstance
    inferInstance (ℕ × (Fin 3 → ℕ)) (tally data' data'.branches ≤ A)
    (Finset.range (1 + Low6966Prices.primaryCutoff / Low6966Prices.layerWidth))
    (fun i => contactSpace S (i + 1)) (fun i => Gate6966Box.boxSpace (B i 0) (B i 1) (B i 2)) W
    (fun i g => (∀ k, g.1 * coord (shape f) k + g.2 k ≤ B i k) →
      (g.2 2 ≤ g.2 0 ∧ 3 * g.2 2 ≤ g.2 1 ∧ g.2 1 ≤ 2 * g.2 0 + g.2 2) →
      GoodAt A f qs (i + 1) g.1 (cert (i + 1) g.1).1 (cert (i + 1) g.1).2 (B i) g.2)
    (fun i g => Gate6966Shape.free (fun k => B i k - (g.1 * coord (shape f) k + g.2 k)))
    Low6966Prices.layerNeed ?_ ?_ hneed ?_
  · intro i _ U hU hne
    obtain ⟨a, η, hd, hfit, hval, hg⟩ := level_dichotomy hf data' input' htilt qs hbs hcs hnd A (i + 1) (B i)
      (cert (i + 1)) (hc0 (i + 1)) (hc1 (i + 1)) (hv0 (i + 1)) U hU hne
    exact ⟨(a, η), hd, fun hgood => hg (hgood hfit hval)⟩
  · intro i hi g hg
    by_contra hn
    exact hg (fun h1 h2 => by_contra fun h3 => hn (hW i (Finset.mem_range.mp hi) g.1 g.2 h1 h2 h3))
  · calc _ = ∑ i ∈ Finset.range levelCount,
          (Low6966Prices.symbolCount - Gate6966Box.ambCount (B i 0) (B i 1) (B i 2) + W i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Low6966SharedShapeRank.ambient_dim, Gate6966Box.boxSpace_dim]
      _ < _ := hsum

end Gate6966Final

end Merged_Gate6966Final

-- merged module Gate6966Assm
section Merged_Gate6966Assm

set_option autoImplicit false

namespace Gate6966Cell
open Gate6966CertCF (cvOf cvOf_le)

abbrev Lv := List (ℕ × ℕ × ℕ × ℕ)

def dflt : ℕ × ℕ × ℕ × ℕ := (4012, 1650, 550, 0)
def Bof (lv : Lv) (i : ℕ) : Fin 3 → ℕ := ![(lv.getD i dflt).1, (lv.getD i dflt).2.1, (lv.getD i dflt).2.2.1]
def Wof (lv : Lv) (i : ℕ) : ℕ := (lv.getD i dflt).2.2.2

def okAt (G : Gt) (r0 : ℕ) (ws : List ℕ) (lv : Lv) (i : ℕ) : Bool :=
  levelOK G (i + 1) (lv.getD i dflt).2.2.2 (lv.getD i dflt).1 (lv.getD i dflt).2.1 (lv.getD i dflt).2.2.1 80
    (fun a => some (cvOf r0 ws (i + 1) a))

def allOK (G : Gt) (r0 : ℕ) (ws : List ℕ) (lv : Lv) (lo n : ℕ) : Bool :=
  (List.range n).all fun d => okAt G r0 ws lv (lo + d)

theorem allOK_add (G : Gt) (r0 : ℕ) (ws : List ℕ) (lv : Lv) (lo n m : ℕ)
    (h1 : allOK G r0 ws lv lo n = true) (h2 : allOK G r0 ws lv (lo + n) m = true) :
    allOK G r0 ws lv lo (n + m) = true := by
  unfold allOK at *
  rw [List.range_add]
  simp only [List.all_append, Bool.and_eq_true, List.all_map] at *
  refine ⟨h1, ?_⟩
  simpa [Function.comp_def, Nat.add_assoc] using h2

theorem allOK_nil (G : Gt) (r0 : ℕ) (ws : List ℕ) (lv : Lv) (lo : ℕ) : allOK G r0 ws lv lo 0 = true := rfl

theorem allOK_get (G : Gt) (r0 : ℕ) (ws : List ℕ) (lv : Lv) (n : ℕ)
    (h : allOK G r0 ws lv 0 n = true) (i : ℕ) (hi : i < n) : okAt G r0 ws lv i = true := by
  unfold allOK at h
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simpa using this

theorem lookup_none (r0 : ℕ) (ws : List ℕ) (r a : ℕ) (h : r0 + ws.length ≤ r) :
    Gate6966ClassTable.lookup r0 ws r a = none := by
  unfold Gate6966ClassTable.lookup
  rw [if_neg]
  intro hc; omega

theorem cvOf_tail (r0 : ℕ) (ws : List ℕ) (r a amax : ℕ) (hr : r0 + ws.length ≤ r) (ha : a ≤ amax) (hlt : a < r) :
    (cvOf r0 ws r a).2 * ((r - a) * (r - a)) ≤ Gate6966Cell.VD * (amax * amax) + (r - a) * (r - a) := by
  unfold cvOf
  by_cases h0 : a = 0
  · subst h0; simp [Gate6966Cell.VD]
  · have hb : Nat.beq a 0 = false := by
      rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨n, hn⟩
      rw [hn]; rfl
    simp only [hb, Bool.cond_false, lookup_none r0 ws r a hr]
    have hp : 0 < (r - a) * (r - a) := Nat.mul_pos (Nat.sub_pos_of_lt hlt) (Nat.sub_pos_of_lt hlt)
    have h1 := Nat.div_mul_le_self (Gate6966Cell.VD * a * a + (r - a) * (r - a) - 1) ((r - a) * (r - a))
    have h2 : a * a ≤ amax * amax := Nat.mul_le_mul ha ha
    have h3 : Gate6966Cell.VD * a * a ≤ Gate6966Cell.VD * (amax * amax) := by
      rw [mul_assoc]; exact Nat.mul_le_mul_left _ h2
    simp only [Gate6966Cell.VD] at h1 h3 ⊢
    omega

def tabAll (r0 : ℕ) (ws : List ℕ) (lo n : ℕ) : Bool :=
  (List.range n).all fun d => Gate6966ClassTable.levelOK (r0 + (lo + d)) (ws.getD (lo + d) 0)

theorem tabAll_add (r0 : ℕ) (ws : List ℕ) (lo n m : ℕ) (h1 : tabAll r0 ws lo n = true)
    (h2 : tabAll r0 ws (lo + n) m = true) : tabAll r0 ws lo (n + m) = true := by
  unfold tabAll at *
  rw [List.range_add]
  simp only [List.all_append, Bool.and_eq_true, List.all_map] at *
  refine ⟨h1, ?_⟩
  simpa [Function.comp_def, Nat.add_assoc] using h2

theorem tabAll_nil (r0 : ℕ) (ws : List ℕ) (lo : ℕ) : tabAll r0 ws lo 0 = true := rfl

theorem tableOK_of_all (ws : List ℕ) : ∀ (r0 lo : ℕ),
    tabAll r0 ws 0 ws.length = true → Gate6966ClassTable.tableOK r0 ws = true := by
  have key : ∀ (ws : List ℕ) (r0 : ℕ), (∀ j, j < ws.length → Gate6966ClassTable.levelOK (r0 + j) (ws.getD j 0) = true) →
      Gate6966ClassTable.tableOK r0 ws = true := by
    intro ws
    induction ws with
    | nil => intro r0 _; rfl
    | cons w ws ih =>
      intro r0 h
      have h0 : Gate6966ClassTable.levelOK r0 w = true := by simpa using h 0 (by simp)
      refine Gate6966ClassTable.tableOK_cons h0 (ih (r0 + 1) fun j hj => ?_)
      have := h (j + 1) (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this
  intro r0 _ h
  apply key
  intro j hj
  unfold tabAll at h
  have := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  simpa using this


/-! PERF (69.62): the `Gate6966Amb.compute` lower bound evaluated in Nat. `cumulative` over ℤ is
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
  ((Gate6966Amb.stop b k - Gate6966Amb.start k : ℕ) : ℤ) * cappedN (Gate6966Amb.padGrade b k) (Gate6966Amb.index j) t

def computeN (b j t : ℕ) : ℤ := sumUpTo (blockN b j t) (Gate6966Amb.chunks b)

theorem computeN_eq (b j t : ℕ) : computeN b j t = Gate6966Amb.compute b j t := by
  unfold computeN Gate6966Amb.compute
  rw [sumUpTo_eq]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold blockN Gate6966Amb.block
  rw [capped_eq]


def ambLB (b j t : ℕ) : ℤ :=
  bif Nat.ble 4012 b && Nat.ble 1650 j && Nat.ble 550 t then (Low6966Prices.symbolCount : ℤ) else computeN b j t

theorem ambLB_le (b j t : ℕ) : ambLB b j t ≤ (Gate6966Box.ambCount b j t : ℤ) := by
  unfold ambLB
  cases h : (Nat.ble 4012 b && Nat.ble 1650 j && Nat.ble 550 t)
  · simp only [Bool.cond_false, computeN_eq]
    exact Gate6966Amb.amb_ge b j t
  · have h' : 4012 ≤ b ∧ 1650 ≤ j ∧ 550 ≤ t := by simpa [Nat.ble_eq, and_assoc] using h
    simp only [Bool.cond_true]
    rw [Gate6966Amb.amb_full b j t h'.1 h'.2.1 h'.2.2]

def lsum (lv : Lv) (i : ℕ) : ℤ :=
  (Low6966Prices.symbolCount : ℤ) - ambLB (lv.getD i dflt).1 (lv.getD i dflt).2.1 (lv.getD i dflt).2.2.1 +
    ((lv.getD i dflt).2.2.2 : ℤ)

def psum (lv : Lv) (lo : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => psum lv lo n + lsum lv (lo + n)

theorem psum_add (lv : Lv) (lo n m : ℕ) : psum lv lo (n + m) = psum lv lo n + psum lv (lo + n) m := by
  induction m with
  | zero => simp [psum]
  | succ m ih => rw [← Nat.add_assoc, psum, ih, psum, add_assoc, Nat.add_assoc]

theorem psum_eq (lv : Lv) (n : ℕ) : psum lv 0 n = ∑ i ∈ Finset.range n, lsum lv i := by
  induction n with
  | zero => simp [psum]
  | succ n ih => rw [psum, ih, Finset.sum_range_succ]; simp

end Gate6966Cell

end Merged_Gate6966Assm
