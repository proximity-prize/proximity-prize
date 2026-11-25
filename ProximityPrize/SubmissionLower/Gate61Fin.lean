import ProximityPrize.SubmissionLower.Gate61Assm
import ProximityPrize.SubmissionLower.Gate61GateT
import ProximityPrize.SubmissionLower.Gate61ThetaOrd
import ProximityPrize.SubmissionLower.Gate61DatET
import ProximityPrize.SubmissionLower.Gate61DatO1
import ProximityPrize.SubmissionLower.Gate61DatO2
import ProximityPrize.SubmissionLower.Gate61SumET
import ProximityPrize.SubmissionLower.Gate61SumO1
import ProximityPrize.SubmissionLower.Gate61SumO2
import ProximityPrize.SubmissionLower.R6960Low6960Gates

-- merged module Gate61FinalOrd
section Merged_Gate61FinalOrd

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace Gate61FinalOrd

open P3 (K)
open K1_13 (Row Shape shape InBox mixed32)
open K1_13_6 (GeoJets toGeneric)
open K1_13_6_1_2 (VanishesTo)
open Low6960SharedPrice (coord)
open Low6960GeometryCut (CutInput)
open Low6960GeometryCut_2 (Branch)
open Low6960SharedTally (Data)
open Low6960SharedTallyNew (tally)
open Low6960SharedPersistent (Persistent)
open Low6960SharedRational (FractionJet toGeometric)
open Low6960SharedShapeRank (ambient contactSpace)
open Gate61Final (levelCount exact_order_fun)
open scoped Polynomial BigOperators

def boxOfL (Yb : Fin 3 → ℕ) : Shape :=
  ⟨max (max (Yb 0) (Yb 1)) (max (Yb 1) 3), max (Yb 1) 3, max (min (Yb 2) (Yb 1 / 3)) 1⟩

theorem boxOfL_chamber (Yb : Fin 3 → ℕ) : K1_13_6_2_3.ChamberBox (boxOfL Yb) := by
  refine ⟨?_, ?_, ?_⟩
  · exact le_max_right _ _
  · change 3 * max (min (Yb 2) (Yb 1 / 3)) 1 ≤ max (Yb 1) 3
    have := Nat.min_le_right (Yb 2) (Yb 1 / 3)
    rcases le_total (min (Yb 2) (Yb 1 / 3)) 1 with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  · exact lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)

theorem inBox_boxOfL {G : Row 4} {Yb : Fin 3 → ℕ} (h : ∀ i, coord (shape G) i ≤ Yb i) :
    InBox (shape G) (boxOfL Yb) := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hc := (K1_13_7_1.shape_chamber G).2
  change 3 * (shape G).t ≤ (shape G).j at hc
  refine ⟨?_, ?_, ?_⟩
  · change (shape G).b ≤ max (max (Yb 0) (Yb 1)) (max (Yb 1) 3)
    exact le_trans (by simpa [coord] using h0) (le_trans (le_max_left _ _) (le_max_left _ _))
  · change (shape G).j ≤ max (Yb 1) 3
    exact le_trans (by simpa [coord] using h1) (le_max_left _ _)
  · change (shape G).t ≤ max (min (Yb 2) (Yb 1 / 3)) 1
    refine le_trans ?_ (le_max_left _ _)
    refine le_min (by simpa [coord] using h2) ?_
    have h1' : (shape G).j ≤ Yb 1 := by simpa [coord] using h1
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)

noncomputable def Tm (f : Row 4) (q₁ q₂ : Shape) : ℚ :=
  (mixed32 q₁ q₂ (K1_13.chart (Low6960Prices.taylorLength + 1) (shape f).chamber)
    (K1_13.chart (Low6960Prices.taylorLength + 2) (shape f).chamber) : ℚ) / 32

noncomputable def rhs (f : Row 4) (qs : Shape) (r a : ℕ) (cc v : ℚ) (B η : Fin 3 → ℕ) : ℚ :=
  let Yb : Fin 3 → ℕ := fun i => B i - (a * coord (shape f) i + η i)
  (1 - cc) * Tm f (boxOfL Yb) (boxOfL Yb) + Tm f (boxOfL η) (boxOfL Yb) +
    ((r - a : ℕ) : ℚ) * Tm f (shape f).chamber (boxOfL η) +
    cc * ((r - a : ℕ) : ℚ) * Tm f (shape f).chamber (boxOfL Yb) +
    v * ((r - a : ℕ) : ℚ) ^ 2 * Tm f (shape f).chamber qs

def GoodAt (A : ℕ) (f : Row 4) (qs : Shape) (r a : ℕ) (cc v : ℚ) (B η : Fin 3 → ℕ) : Prop :=
  a < r ∧ Gate61TwoCut.ClassCert r a cc v ∧ rhs f qs r a cc v B η ≤ (A : ℚ) * ((r - a : ℕ) : ℚ) ^ 2

variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}

theorem level_dichotomy_ord (hf : Low6960Prices.SmallFactor f)
    (D : Data Γ s f Q l {P | Persistent Γ s P}) (input : CutInput Γ s f Q l)
    (qs : Shape) (hbs : InBox (shape (K1_13_6.separant f)) qs) (hcs : K1_13_6_2_3.ChamberBox qs)
    (hnd : ¬ f ∣ K1_13_6.separant f) (A r : ℕ) (B : Fin 3 → ℕ) (cert : ℕ → ℚ × ℚ)
    (hc0 : ∀ a, 0 ≤ (cert a).1) (hc1 : ∀ a, (cert a).1 ≤ 1) (hv0 : ∀ a, 0 ≤ (cert a).2)
    (U : Submodule K1_13_6.GenericField ↥ambient)
    (hU : U ≤ contactSpace (D.branches.image Branch.surface) r ⊓ Gate61Box.boxSpace (B 0) (B 1) (B 2))
    (hne : U ≠ ⊥) :
    ∃ (a : ℕ) (η : Fin 3 → ℕ),
      Module.finrank K1_13_6.GenericField U ≤
        Gate61Shape.free (fun k => B k - (a * coord (shape f) k + η k)) ∧
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
  have hB : ∀ Q' ∈ U', ∀ k, Gate61Shape.shp k Q' ≤ B k := by
    rintro _ ⟨u, hu, rfl⟩ k
    have := Gate61Hb.shp_le_of_mem_boxSpace (B 0) (B 1) (B 2) u (hU hu).2 k
    have hk : (![B 0, B 1, B 2] : Fin 3 → ℕ) k = B k := by fin_cases k <;> rfl
    simpa [hk] using this
  obtain ⟨a, H, K1, K2, hH0, hK10, hfH, hfG, hHG, hGG, hQ1, hQ2, hs1, hs2, hdim, hfit, hval⟩ :=
    Gate61Rows.rows_from_subspace f hfirr hdeg U' hU'ne r S hS hcont B hB
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
    have hcf : K1_13_6_2_3.ChamberBox (shape f).chamber :=
      ⟨(K1_13_7_1.shape_chamber f).1, (K1_13_7_1.shape_chamber f).2, hf.2.1⟩
    have hbox : ∀ G : Row 4, InBox (shape G) (shape G).chamber := fun G =>
      ⟨le_max_left _ _, le_rfl, le_rfl⟩
    have hmain := Gate61TwoCut.two_cut_count_ordinary D input D.branches (subset_refl _) H K1 K2
      (K1_13_6.separant f) (shape f).chamber (boxOfL fun k => coord (shape H) k)
      (boxOfL fun k => B k - (a * coord (shape f) k + coord (shape H) k))
      (boxOfL fun k => B k - (a * coord (shape f) k + coord (shape H) k)) qs
      (hbox f) (inBox_boxOfL (fun k => le_rfl)) (inBox_boxOfL hs1) (inBox_boxOfL hs2) hbs
      hcf (boxOfL_chamber _) (boxOfL_chamber _) (boxOfL_chamber _) hcs r a (cert a).1 (cert a).2
      (hc0 a) (hc1 a) (hv0 a) hcertA e m hf0 hH0 hK10 hf0' hH0' hK10' hsf0 hsf0' hfH hfG hHG hGG hfs
      (fun b hb => he b.surface (hmemS b hb)) (fun b hb => hm' b.surface (hmemS b hb)) rfl
      (fun b hb => hQ1 b.surface (hmemS b hb)) (fun b hb => hQ2 b.surface (hmemS b hb)) hlt.le
    have hρ : (0 : ℚ) < ((r - a : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hlt
    have hN := Gate61TwoCut.mark_bound_of_good hρ hmain (by exact hrhs)
    have : ((tally D D.branches : ℕ) : ℚ) ≤ (A : ℚ) := by
      simpa [tally] using hN
    exact_mod_cast this

theorem two_cut_price_ordinary {w : P3.I → K} (hm : Low6960Prices.Messages w Γ s) (hf : Low6960Prices.SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (hl : 0 < l)
    (hproper : Low6960Prices.ProperCut f Γ s l)
    (qs : Shape) (hbs : InBox (shape (K1_13_6.separant f)) qs) (hcs : K1_13_6_2_3.ChamberBox qs)
    (hnd : ¬ f ∣ K1_13_6.separant f) (A : ℕ) (B : ℕ → Fin 3 → ℕ) (W : ℕ → ℕ)
    (cert : ℕ → ℕ → ℚ × ℚ) (hc0 : ∀ r a, 0 ≤ (cert r a).1) (hc1 : ∀ r a, (cert r a).1 ≤ 1)
    (hv0 : ∀ r a, 0 ≤ (cert r a).2)
    (hW : ∀ i, i < levelCount → ∀ (a : ℕ) (η : Fin 3 → ℕ),
      (∀ k, a * coord (shape f) k + η k ≤ B i k) → (η 2 ≤ η 0 ∧ 3 * η 2 ≤ η 1 ∧ η 1 ≤ 2 * η 0 + η 2) →
      ¬ GoodAt A f qs (i + 1) a (cert (i + 1) a).1 (cert (i + 1) a).2 (B i) η →
        Gate61Shape.free (fun k => B i k - (a * coord (shape f) k + η k)) ≤ W i)
    (hsum : ∑ i ∈ Finset.range levelCount,
      (Low6960Prices.symbolCount - Gate61Box.ambCount (B i 0) (B i 1) (B i 2) + W i) < Low6960Prices.layerNeed) :
    Γ.card ≤ A + Low6960SharedPrice.additiveBase (shape f) l + Low6960SharedPrice.nonsharedFee (shape f) l := by
  classical
  unfold levelCount at hW hsum
  refine Gate61Count2.count₂ hm f hf hon l hl hproper A ?_
  intro Q' input' data'
  set S := data'.branches.image Branch.surface with hSdef
  have hpers : ∀ P ∈ S, Persistent Γ s P := by
    intro P hP
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
    exact data'.allowed b hb
  have hneed := Low6960SharedShapeRank.bank_layers hm S hpers
  refine @Gate61Gate.gate₂_of_need K1_13_6.GenericField (↥ambient) ℕ inferInstance inferInstance inferInstance
    inferInstance (ℕ × (Fin 3 → ℕ)) (tally data' data'.branches ≤ A)
    (Finset.range (1 + Low6960Prices.primaryCutoff / Low6960Prices.layerWidth))
    (fun i => contactSpace S (i + 1)) (fun i => Gate61Box.boxSpace (B i 0) (B i 1) (B i 2)) W
    (fun i g => (∀ k, g.1 * coord (shape f) k + g.2 k ≤ B i k) →
      (g.2 2 ≤ g.2 0 ∧ 3 * g.2 2 ≤ g.2 1 ∧ g.2 1 ≤ 2 * g.2 0 + g.2 2) →
      GoodAt A f qs (i + 1) g.1 (cert (i + 1) g.1).1 (cert (i + 1) g.1).2 (B i) g.2)
    (fun i g => Gate61Shape.free (fun k => B i k - (g.1 * coord (shape f) k + g.2 k)))
    Low6960Prices.layerNeed ?_ ?_ hneed ?_
  · intro i _ U hU hne
    obtain ⟨a, η, hd, hfit, hval, hg⟩ := level_dichotomy_ord hf data' input' qs hbs hcs hnd A (i + 1) (B i)
      (cert (i + 1)) (hc0 (i + 1)) (hc1 (i + 1)) (hv0 (i + 1)) U hU hne
    exact ⟨(a, η), hd, fun hgood => hg (hgood hfit hval)⟩
  · intro i hi g hg
    by_contra hn
    exact hg (fun h1 h2 => by_contra fun h3 => hn (hW i (Finset.mem_range.mp hi) g.1 g.2 h1 h2 h3))
  · calc _ = ∑ i ∈ Finset.range levelCount,
          (Low6960Prices.symbolCount - Gate61Box.ambCount (B i 0) (B i 1) (B i 2) + W i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Low6960SharedShapeRank.ambient_dim, Gate61Box.boxSpace_dim]
      _ < _ := hsum

end Gate61FinalOrd

end Merged_Gate61FinalOrd

-- merged module Gate61GlueO
section Merged_Gate61GlueO

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Gate61Cell
open Gate61FreeCard (mx mn mx_eq mn_eq)
open K1_13 (Row Shape shape InBox mixed32)
open Gate61Bilinear (opOf OP)
open Low6960SharedPrice (coord)

theorem Tm_le (G : Gt) (zx wx zh wh q1 q2 : Shape) (num den : ℕ) (hden : 0 < den)
    (hM : ∀ i k', (opOf zh wh).ray i k' = G.mat i k')
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (opOf zx wx).ray i k' ≤ num * (opOf zh wh).ray i k')
    (c1 : q1.j ≤ q1.b ∧ 3 * q1.t ≤ q1.j) (c2 : q2.j ≤ q2.b ∧ 3 * q2.t ≤ q2.j) :
    (mixed32 q1 q2 zx wx : ℚ) ≤ (num : ℚ) / den * (TT G q1.b q1.j q1.t q2.b q2.j q2.t : ℚ) := by
  have h := Gate61Bilinear.mixed32_theta zx wx zh wh q1 q2 num den hθ c1.1 c1.2 c2.1 c2.2
  have e : mixed32 q1 q2 zh wh = TT G q1.b q1.j q1.t q2.b q2.j q2.t := by
    rw [Gate61Bilinear.mixed32_cone zh wh q1 q2 c1.1 c1.2 c2.1 c2.2, Gate61Bilinear.ocone_expand]
    simp only [hM, Gt.mat]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    symm
    rw [← Int.toNat_natCast (TT G q1.b q1.j q1.t q2.b q2.j q2.t)]
    congr 1
    unfold TT
    push_cast [Nat.cast_sub c1.1, Nat.cast_sub c2.1]
    ring
  rw [e] at h
  have hq : (den : ℚ) * (mixed32 q1 q2 zx wx : ℚ) ≤ num * (TT G q1.b q1.j q1.t q2.b q2.j q2.t : ℚ) := by
    exact_mod_cast h
  have hd : (0 : ℚ) < den := by exact_mod_cast hden
  rw [div_mul_eq_mul_div, le_div_iff₀ hd]
  linarith

theorem alg32 (tp1 tp2 tp3 tp4 tp5 T1 T2 Txe TXe Txq TXq Txs ts N cc ρ v AA AX : ℚ)
    (hc0 : 0 ≤ cc) (hc1 : cc ≤ 1) (hρ : 0 ≤ ρ) (hv : 0 ≤ v) (hN : 0 ≤ N)
    (t1 : tp1 ≤ N * T1) (t2 : tp2 ≤ N * T2) (t3 : tp3 ≤ N * Txe) (t4 : tp4 ≤ N * Txq) (t5 : tp5 ≤ N * Txs)
    (m3 : Txe ≤ TXe) (m4 : Txq ≤ TXq) (m5 : Txs ≤ ts)
    (core : (1 - cc) * T1 + T2 + ρ * TXe + cc * ρ * TXq + v * ρ ^ 2 * ts ≤ 32 * AA * ρ ^ 2)
    (hA : N * AA ≤ AX) :
    (1 - cc) * (tp1 / 32) + tp2 / 32 + ρ * (tp3 / 32) + cc * ρ * (tp4 / 32) + v * ρ ^ 2 * (tp5 / 32) ≤ AX * ρ ^ 2 := by
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

theorem rhs_le_ord (f : Row 4) (G : Gt) (hG : G.Ok) (hlift : G.lift = true) (hsc : G.sc = 32)
    (hxt : 3 * G.xt ≤ G.xj)
    (hlo : G.lb ≤ (shape f).b ∧ G.lj ≤ (shape f).j ∧ G.lt ≤ (shape f).t)
    (hhi : (shape f).b ≤ G.xb ∧ (shape f).j ≤ G.xj ∧ (shape f).t ≤ G.xt)
    (hcx : 3 * (shape f).t ≤ (shape f).j)
    (zh wh : Shape) (hM : ∀ i k', (opOf zh wh).ray i k' = G.mat i k')
    (num den Ax : ℕ) (hden : 0 < den)
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (opOf (K1_13.chart (Low6960Prices.taylorLength + 1) (shape f).chamber)
        (K1_13.chart (Low6960Prices.taylorLength + 2) (shape f).chamber)).ray i k' ≤ num * (opOf zh wh).ray i k')
    (hA : num * G.A ≤ den * Ax)
    (qs : Shape) (hqs : qs = ⟨G.sep.1, G.sep.2.1, G.sep.2.2⟩)
    (r a cn vn W : ℕ) (B η : Fin 3 → ℕ) (hρ : a < r) (hcn : cn ≤ 2 * (r - a))
    (hI : lhsV (mkPr G r a cn vn W (B 0) (B 1) (B 2)) (B 0 - a * G.lb - η 0) (B 1 - a * G.lj - η 1)
      (B 2 - a * G.lt - η 2) (η 0) (η 1) (η 2) ≤ (mkPr G r a cn vn W (B 0) (B 1) (B 2)).rhs) :
    Gate61FinalOrd.rhs f qs r a ((cn : ℚ) / (2 * ((r - a : ℕ) : ℚ))) ((vn : ℚ) / 10000000) B η ≤
      (Ax : ℚ) * ((r - a : ℕ) : ℚ) ^ 2 := by
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
  simp only [hB, hJ, hT, Bool.cond_true, mx_eq, mn_eq] at core
  unfold Gate61FinalOrd.rhs Gate61FinalOrd.Tm
  have cq := Gate61FinalOrd.boxOfL_chamber Yb
  have ce := Gate61FinalOrd.boxOfL_chamber η
  have cqs : qs.j ≤ qs.b ∧ 3 * qs.t ≤ qs.j := by
    subst hqs
    simp only [Gt.sep, hlift, hB, hJ, hT, Bool.cond_true, mx_eq, mn_eq]
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
    Tm_le G _ _ zh wh q1 q2 num den hden hM hθ c1 c2
  have cx : ((shape f).chamber).j ≤ ((shape f).chamber).b ∧ 3 * ((shape f).chamber).t ≤ ((shape f).chamber).j :=
    ⟨le_max_right _ _, hcx⟩
  have cX : Cone (mx G.xb G.xj) G.xj G.xt := ⟨by rw [mx_eq]; exact le_max_right _ _, hxt⟩
  have cxC : Cone ((shape f).chamber).b ((shape f).chamber).j ((shape f).chamber).t := cx
  have mxle : ((shape f).chamber).b ≤ mx G.xb G.xj := by
    rw [mx_eq]; exact max_le_max hhi.1 hhi.2.1
  have t1 := T _ _ ⟨cq.1, cq.2.1⟩ ⟨cq.1, cq.2.1⟩
  have t2 := T _ _ ⟨ce.1, ce.2.1⟩ ⟨cq.1, cq.2.1⟩
  have t3 := T _ _ cx ⟨ce.1, ce.2.1⟩
  have t4 := T _ _ cx ⟨cq.1, cq.2.1⟩
  have t5 := T _ _ cx cqs
  have m3 := TT_mono_left G hG cxC cX ⟨ce.1, ce.2.1⟩ mxle hhi.2.1 hhi.2.2
  have m4 := TT_mono_left G hG cxC cX ⟨cq.1, cq.2.1⟩ mxle hhi.2.1 hhi.2.2
  have m5 : TT G ((shape f).chamber).b ((shape f).chamber).j ((shape f).chamber).t qs.b qs.j qs.t ≤ G.tsep := by
    subst hqs
    exact TT_mono_left G hG cxC cX cqs mxle hhi.2.1 hhi.2.2
  have hN : (0 : ℚ) ≤ (num : ℚ) / den := by positivity
  have hA' : (num : ℚ) / den * G.A ≤ Ax := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by exact_mod_cast hden)]
    exact_mod_cast (by linarith [hA] : num * G.A ≤ Ax * den)
  rw [hsc] at core
  push_cast at core
  simp only [Gate61FinalOrd.boxOfL] at t1 t2 t3 t4 t5 m3 m4 ⊢
  simp only [hYb] at t1 t2 t4 m4 core
  simp only [mx_eq] at m3 m4
  exact alg32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcc0 hcc1 hρpos hv0 hN t1 t2 t3 t4 t5
    (Nat.cast_le.mpr m3) (Nat.cast_le.mpr m4) (Nat.cast_le.mpr m5) core hA'

end Gate61Cell

end Merged_Gate61GlueO

-- merged module Gate61GateO
section Merged_Gate61GateO

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace Gate61Cell
open P3 (K)
open K1_13 (Row Shape shape InBox)
open Gate61Bilinear (opOf)
open Low6960SharedPrice (coord)
open Gate61FreeCard (mx)
open Gate61CertCF (cvOf cvOf_le certF certF_bounds certF_class)
open scoped Polynomial BigOperators

theorem price_O {w : P3.I → K} {Γ : Finset K} {s : K → (Polynomial K)} {f : Row 4} {l : ℕ}
    (hm : Low6960Prices.Messages w Γ s) (hf : Low6960Prices.SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (hl : 0 < l)
    (hproper : Low6960Prices.ProperCut f Γ s l) (hchar : f.degreeOf 3 < K1.p)
    (hcx : 3 * (shape f).t ≤ (shape f).j)
    (G : Gt) (hG : G.Ok) (hlift : G.lift = true) (hsc : G.sc = 32)
    (hxt : 3 * G.xt ≤ G.xj) (hpos : 0 < G.lb ∧ 0 < G.lj ∧ 0 < G.lt) (hxj : 3 ≤ G.xj)
    (hlo : G.lb ≤ (shape f).b ∧ G.lj ≤ (shape f).j ∧ G.lt ≤ (shape f).t)
    (hhi : (shape f).b ≤ G.xb ∧ (shape f).j ≤ G.xj ∧ (shape f).t ≤ G.xt)
    (zh wh : Shape) (hM : ∀ i k', (opOf zh wh).ray i k' = G.mat i k')
    (num den Ax : ℕ) (hden : 0 < den)
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (opOf (K1_13.chart (Low6960Prices.taylorLength + 1) (shape f).chamber)
        (K1_13.chart (Low6960Prices.taylorLength + 2) (shape f).chamber)).ray i k' ≤ num * (opOf zh wh).ray i k')
    (hA : num * G.A ≤ den * Ax)
    (r0 : ℕ) (ws : List ℕ) (ht : Gate61ClassTable.tableOK r0 ws = true) (lv : Lv) (n : ℕ) (hn : n = lv.length)
    (hr0 : r0 + ws.length ≤ n + 1) (hL : n ≤ Gate61Final.levelCount)
    (hall : allOK G r0 ws lv 0 n = true)
    (ρ0 amax : ℕ) (hρ0 : 0 < ρ0) (hru : ρ0 + amax ≤ n + 1)
    (hamax : ∀ a, a * G.lb ≤ 4012 → a * G.lj ≤ 1650 → a * G.lt ≤ 550 → a ≤ amax)
    (hS0 : G.tsep ≤ G.sc * G.A * VD)
    (hS1 : 2 * VD * TT G (mx G.xb G.xj) G.xj G.xt 4012 1650 550 ≤ (G.sc * G.A * VD - G.tsep) * ρ0)
    (hS2 : 2 * VD * TT G (mx G.xb G.xj) G.xj G.xt 4012 1650 550 * ρ0 +
        VD * (2 * TT G 4012 1650 550 4012 1650 550 + amax * amax * G.tsep) ≤ (G.sc * G.A * VD - G.tsep) * (ρ0 * ρ0))
    (hs : (∑ i ∈ Finset.range n, lsum lv i) < Low6960Prices.layerNeed) :
    Γ.card ≤ Ax + Low6960SharedPrice.additiveBase (shape f) l + Low6960SharedPrice.nonsharedFee (shape f) l := by
  have hf0 : f ≠ 0 := hf.1.ne_zero
  have htpos : 0 < f.degreeOf 3 := by
    have : (shape f).t = f.degreeOf 3 := rfl
    omega
  have hnd : ¬ f ∣ K1_13_6.separant f := KoalaFarBridge.separant_proper hf0 htpos hchar
  have sb := KoalaFarBridge.separant_box f
  set qs : Shape := ⟨G.sep.1, G.sep.2.1, G.sep.2.2⟩ with hqs
  have hsep : G.sep = (mx (mx (G.xb - 1) (G.xj - 3)) (mx (G.xj - 3) 3), mx (G.xj - 3) 3,
      mx (Gate61FreeCard.mn (G.xt - 1) ((G.xj - 3) / 3)) 1) := by
    simp only [Gt.sep, hlift, hB, hJ, hT, Bool.cond_true]
  have hbs : InBox (shape (K1_13_6.separant f)) qs := by
    refine ⟨?_, ?_, ?_⟩
    · have := sb.1
      simp only [hqs, hsep, Gate61FreeCard.mx_eq]
      exact this.trans ((Nat.sub_le_sub_right hhi.1 1).trans ((le_max_left _ _).trans (le_max_left _ _)))
    · have := sb.2.1
      simp only [hqs, hsep, Gate61FreeCard.mx_eq]
      exact this.trans ((Nat.sub_le_sub_right hhi.2.1 3).trans (le_max_left _ _))
    · have := sb.2.2
      simp only [hqs, hsep, Gate61FreeCard.mn_eq, Gate61FreeCard.mx_eq]
      refine this.trans (le_trans ?_ (le_max_left _ _))
      refine le_min (Nat.sub_le_sub_right hhi.2.2 1) ?_
      refine (Nat.le_div_iff_mul_le (by norm_num)).mpr ?_
      show ((shape f).t - 1) * 3 ≤ G.xj - 3
      omega
  have hcs : K1_13_6_2_3.ChamberBox qs := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [hqs, hsep, Gate61FreeCard.mx_eq]
      exact le_max_right _ _
    · simp only [hqs, hsep, Gate61FreeCard.mn_eq, Gate61FreeCard.mx_eq]
      have := Nat.min_le_right (G.xt - 1) ((G.xj - 3) / 3)
      rcases le_total (min (G.xt - 1) ((G.xj - 3) / 3)) 1 with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; omega
    · simp only [hqs, hsep, Gate61FreeCard.mx_eq]
      exact lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hxl : G.lb ≤ coord (shape f) 0 ∧ G.lj ≤ coord (shape f) 1 ∧ G.lt ≤ coord (shape f) 2 := hlo
  have hsum := hsum_of lv n hn hL hs
  refine Gate61FinalOrd.two_cut_price_ordinary hm hf hon hl hproper qs hbs hcs hnd Ax (Bof lv) (Wof lv)
    (certF r0 ws) (fun r a => (certF_bounds r0 ws r a).1) (fun r a => (certF_bounds r0 ws r a).2.1)
    (fun r a => (certF_bounds r0 ws r a).2.2) ?_ hsum
  intro i _ a η hfit hv hng
  by_contra hfree
  push_neg at hfree
  obtain ⟨hlt, hI⟩ := hI_of_free G hG hxt hpos r0 ws lv n hn hr0 hall ρ0 amax hρ0 hru hamax hS0 hS1 hS2 i
    (fun k => coord (shape f) k) hxl a η hfit hv hfree
  have hc : (cvOf r0 ws (i + 1) a).1 ≤ 2 * (i + 1 - a) := cvOf_le r0 ws (i + 1) a
  have hr := rhs_le_ord f G hG hlift hsc hxt hlo hhi hcx zh wh hM num den Ax hden hθ hA qs hqs (i + 1) a _ _
    (Wof lv i) (Bof lv i) η hlt hc hI
  exact hng ⟨hlt, certF_class ht hlt, hr⟩

end Gate61Cell

end Merged_Gate61GateO

-- merged module Gate61Fin
section Merged_Gate61Fin

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
set_option Elab.async false

namespace Gate61Fin
open Gate61Cell
open K1_13 (Shape shape)
open Gate61Bilinear (tpOf opOf)

def DEN : ℕ := 10000000
def tlRef : ℕ := 133430
def kT : ℕ := Low6960Prices.taylorLength - 4
def kTRef : ℕ := tlRef - 4
def rayT (p : Shape) : Fin 3 → Fin 3 → ℤ :=
  (tpOf p kT (Low6960Prices.bentLift kT p).2 (Low6960Prices.bentLift (kT + 1) p).2).ray
def rayTRef (p : Shape) : Fin 3 → Fin 3 → ℤ :=
  (tpOf p kTRef (Low6960Prices.bentLift kTRef p).2 (Low6960Prices.bentLift (kTRef + 1) p).2).ray
def rayO (p : Shape) : Fin 3 → Fin 3 → ℤ :=
  (opOf (K1_13.chart (Low6960Prices.taylorLength + 1) p.chamber)
    (K1_13.chart (Low6960Prices.taylorLength + 2) p.chamber)).ray
def rayORef (p : Shape) : Fin 3 → Fin 3 → ℤ :=
  (opOf (K1_13.chart (tlRef + 1) p.chamber)
    (K1_13.chart (tlRef + 2) p.chamber)).ray

def cd (x y : ℤ) : ℕ := if y ≤ 0 then 0 else (((DEN : ℤ) * x).toNat + y.toNat - 1) / y.toNat

def thNum (rx rh : Fin 3 → Fin 3 → ℤ) : ℕ :=
  ((List.finRange 3).flatMap fun i => (List.finRange 3).map fun k => cd (rx i k) (rh i k)).foldl max 0

def thOK (rx rh : Fin 3 → Fin 3 → ℤ) : Bool :=
  decide (∀ i k : Fin 3, (DEN : ℤ) * rx i k ≤ (thNum rx rh : ℤ) * rh i k)

theorem thOK_spec {rx rh : Fin 3 → Fin 3 → ℤ} (h : thOK rx rh = true) :
    ∀ i k : Fin 3, (DEN : ℤ) * rx i k ≤ (thNum rx rh : ℤ) * rh i k := of_decide_eq_true h

def hiS (G : Gt) : Shape := ⟨G.xb, G.xj, G.xt⟩
def inR (G : Gt) (x : Shape) : Bool :=
  Nat.ble G.lb x.b && Nat.ble G.lj x.j && Nat.ble G.lt x.t && Nat.ble x.b G.xb && Nat.ble x.j G.xj && Nat.ble x.t G.xt
def tfB (x : Shape) : Bool := Nat.ble (3 * x.t + 3) x.j && Nat.ble (x.j + 1) x.b

def cls (x : Shape) : ℕ :=
  if inR Gate61DatET.G x = true ∧ tfB x = true then 1
  else if inR Gate61DatO1.G x = true ∧ tfB x = false then 2
  else if inR Gate61DatO2.G x = true ∧ tfB x = false then 3 else 0

def numT (G : Gt) (x : Shape) : ℕ := thNum (rayT x) (rayTRef (hiS G))
def numO (G : Gt) (x : Shape) : ℕ := thNum (rayO x) (rayORef (hiS G))
def Ax (num A : ℕ) : ℕ := (num * A + DEN - 1) / DEN

def Gfun (x : Shape) : ℕ :=
  if cls x = 1 then Ax (numT Gate61DatET.G x) Gate61DatET.G.A
  else if cls x = 2 then Ax (numO Gate61DatO1.G x) Gate61DatO1.G.A
  else if cls x = 3 then Ax (numO Gate61DatO2.G x) Gate61DatO2.G.A else 0

def shapeOK (x : Shape) : Bool :=
  if cls x = 1 then thOK (rayT x) (rayTRef (hiS Gate61DatET.G))
  else if cls x = 2 then thOK (rayO x) (rayORef (hiS Gate61DatO1.G))
  else if cls x = 3 then thOK (rayO x) (rayORef (hiS Gate61DatO2.G)) else false

def allShapes : Bool :=
  (List.range 6).all fun id => (List.range 15).all fun t =>
    (Low6960Gate.gateList id t).all fun p => shapeOK ⟨p.1, p.2, t⟩

theorem gl_nil (id t : ℕ) (h : 15 ≤ t) : Low6960Gate.gateList id t = [] := by
  unfold Low6960Gate.gateList
  split <;> first | rfl | (rename_i h2; omega)

theorem amax_le (lb lj lt amax : ℕ) (hb : 0 < lb) (hj : 0 < lj) (ht : 0 < lt)
    (h : amax = min (4012 / lb) (min (1650 / lj) (550 / lt))) :
    ∀ a, a * lb ≤ 4012 → a * lj ≤ 1650 → a * lt ≤ 550 → a ≤ amax := by
  intro a h1 h2 h3
  subst h
  exact le_min ((Nat.le_div_iff_mul_le hb).mpr h1) (le_min ((Nat.le_div_iff_mul_le hj).mpr h2)
    ((Nat.le_div_iff_mul_le ht).mpr h3))

theorem ceil_le (N D : ℕ) (hD : 0 < D) : N ≤ D * ((N + D - 1) / D) := by
  have := Gate61CertCF.ceil_mul N D hD
  rw [Nat.mul_comm]; exact this

theorem cls_cases {x : Shape} {c : ℕ} (h : cls x = c) (hc : c ≠ 0) :
    (c = 1 ∧ inR Gate61DatET.G x = true ∧ tfB x = true) ∨ (c = 2 ∧ inR Gate61DatO1.G x = true ∧ tfB x = false) ∨
    (c = 3 ∧ inR Gate61DatO2.G x = true ∧ tfB x = false) := by
  unfold cls at h
  split_ifs at h with c1 c2 c3
  · subst h; exact Or.inl ⟨rfl, c1⟩
  · subst h; exact Or.inr (Or.inl ⟨rfl, c2⟩)
  · subst h; exact Or.inr (Or.inr ⟨rfl, c3⟩)
  · exact absurd h.symm hc

theorem inR_props {G : Gt} {x : Shape} (h : inR G x = true) :
    G.lb ≤ x.b ∧ G.lj ≤ x.j ∧ G.lt ≤ x.t ∧ x.b ≤ G.xb ∧ x.j ≤ G.xj ∧ x.t ≤ G.xt := by
  simp only [inR, Bool.and_eq_true, Nat.ble_eq] at h
  tauto

theorem tfB_true {x : Shape} (h : tfB x = true) : 3 * x.t + 3 ≤ x.j ∧ x.j + 1 ≤ x.b := by
  simpa [tfB, Nat.ble_eq] using h

theorem tfB_false {x : Shape} (h : tfB x = false) : ¬ (3 * x.t + 3 ≤ x.j ∧ x.j + 1 ≤ x.b) := by
  intro hh
  have e1 := Nat.ble_eq_true_of_le hh.1
  have e2 := Nat.ble_eq_true_of_le hh.2
  simp [tfB, e1, e2] at h

theorem shapeOK_cases {x : Shape} (h : shapeOK x = true) :
    (cls x = 1 ∧ thOK (rayT x) (rayTRef (hiS Gate61DatET.G)) = true) ∨
    (cls x = 2 ∧ thOK (rayO x) (rayORef (hiS Gate61DatO1.G)) = true) ∨
    (cls x = 3 ∧ thOK (rayO x) (rayORef (hiS Gate61DatO2.G)) = true) := by
  unfold shapeOK at h
  split_ifs at h with c1 c2 c3
  · exact Or.inl ⟨c1, h⟩
  · exact Or.inr (Or.inl ⟨c2, h⟩)
  · exact Or.inr (Or.inr ⟨c3, h⟩)

open P3 (K) in
open scoped Polynomial in
theorem gated_price {w : P3.I → K} {Γ : Finset K} {s : K → (Polynomial K)} {f : K1_13.Row 4} {l : ℕ}
    (hm : Low6960Prices.Messages w Γ s) (hf : Low6960Prices.SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (hl : 0 < l)
    (hproper : Low6960Prices.ProperCut f Γ s l) (hchar : f.degreeOf 3 < K1.p)
    (hx : shapeOK (shape f) = true) :
    Γ.card ≤ Gfun (shape f) + Low6960SharedPrice.additiveBase (shape f) l +
      Low6960SharedPrice.nonsharedFee (shape f) l := by
  rcases shapeOK_cases hx with ⟨hc, hth⟩ | ⟨hc, hth⟩ | ⟨hc, hth⟩
  · obtain (⟨_, hin, htf⟩ | ⟨h2, _⟩ | ⟨h3, _⟩) := cls_cases hc (by norm_num)
    · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
      have hθ := thOK_spec hth
      have key := price_T hm hf hon hl hproper hchar (tfB_true htf) Gate61DatET.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl (by decide)
        (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩ kT kTRef
        (Low6960Prices.bentLift kTRef (hiS Gate61DatET.G)).2 (Low6960Prices.bentLift (kTRef + 1) (hiS Gate61DatET.G)).2
        (Low6960Prices.bentLift kT (shape f)).2 (Low6960Prices.bentLift (kT + 1) (shape f)).2 rfl rfl rfl rfl rfl
        (by decide +kernel) (numT Gate61DatET.G (shape f)) DEN (Ax (numT Gate61DatET.G (shape f)) Gate61DatET.G.A)
        (by decide) hθ (ceil_le _ _ (by decide)) 1 Gate61DatET.ws Gate61DatET.tabOK Gate61DatET.lv Gate61DatET.n rfl
        (by decide +kernel) (by decide +kernel) Gate61DatET.allOKn Gate61DatET.rho0 Gate61DatET.amax (by decide)
        (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) Gate61DatET.sumLt
      simp only [Gfun, hc, if_true]
      exact key
    · omega
    · omega
  · obtain (⟨h1, _⟩ | ⟨_, hin, htf⟩ | ⟨h3, _⟩) := cls_cases hc (by norm_num)
    · omega
    · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
      have hθ := thOK_spec hth
      have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
      have key := price_O hm hf hon hl hproper hchar hcx Gate61DatO1.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl
        (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩
        (K1_13.chart (tlRef + 1) (hiS Gate61DatO1.G).chamber)
        (K1_13.chart (tlRef + 2) (hiS Gate61DatO1.G).chamber)
        (by decide +kernel) (numO Gate61DatO1.G (shape f)) DEN (Ax (numO Gate61DatO1.G (shape f)) Gate61DatO1.G.A)
        (by decide) hθ (ceil_le _ _ (by decide)) 1 Gate61DatO1.ws Gate61DatO1.tabOK Gate61DatO1.lv Gate61DatO1.n rfl
        (by decide +kernel) (by decide +kernel) Gate61DatO1.allOKn Gate61DatO1.rho0 Gate61DatO1.amax (by decide)
        (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) Gate61DatO1.sumLt
      simp only [Gfun, hc]
      simpa using key
    · omega
  · obtain (⟨h1, _⟩ | ⟨h2, _⟩ | ⟨_, hin, htf⟩) := cls_cases hc (by norm_num)
    · omega
    · omega
    · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
      have hθ := thOK_spec hth
      have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
      have key := price_O hm hf hon hl hproper hchar hcx Gate61DatO2.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl
        (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩
        (K1_13.chart (tlRef + 1) (hiS Gate61DatO2.G).chamber)
        (K1_13.chart (tlRef + 2) (hiS Gate61DatO2.G).chamber)
        (by decide +kernel) (numO Gate61DatO2.G (shape f)) DEN (Ax (numO Gate61DatO2.G (shape f)) Gate61DatO2.G.A)
        (by decide) hθ (ceil_le _ _ (by decide)) 1 Gate61DatO2.ws Gate61DatO2.tabOK Gate61DatO2.lv Gate61DatO2.n rfl
        (by decide +kernel) (by decide +kernel) Gate61DatO2.allOKn Gate61DatO2.rho0 Gate61DatO2.amax (by decide)
        (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) Gate61DatO2.sumLt
      simp only [Gfun, hc]
      simpa using key

def one (id t : ℕ) : Bool := (Low6960Gate.gateList id t).all fun p => shapeOK ⟨p.1, p.2, t⟩

def gtOne (id t : ℕ) : Bool := (Low6960Gate.gateList id t).all fun p =>
  let x : Shape := ⟨p.1, p.2, t⟩
  let k : Low6960Allocation.Band := ⟨id % 19, Nat.mod_lt _ (by decide)⟩
  let l := Low6960Allocation.order (Low6960Allocation.bandOrders k) x
  Nat.blt 0 l && Nat.ble (Low6960Gate.gatePrice Gfun x l)
    (Low6960Allocation.allowance k ((Low6960Allocation.start k).t + t) p.1 p.2 t)

end Gate61Fin

end Merged_Gate61Fin
