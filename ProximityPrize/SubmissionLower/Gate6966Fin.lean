import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Gate6966Assm
import ProximityPrize.SubmissionLower.Gate6966ThetaOrd
import ProximityPrize.SubmissionLower.Low6966AllocTotal
import ProximityPrize.SubmissionLower.Witness6966SumETm
set_option Elab.async false













set_option Elab.async false

-- merged module Gate6966FinalOrd
section Merged_Gate6966FinalOrd

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace Gate6966FinalOrd

open P3 (K)
open K1_13 (Row Shape shape InBox mixed32)
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
open Gate6966Final (levelCount exact_order_fun)
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
  (mixed32 q₁ q₂ (K1_13.chart (Low6966Prices.taylorLength + 1) (shape f).chamber)
    (K1_13.chart (Low6966Prices.taylorLength + 2) (shape f).chamber) : ℚ) / 32

noncomputable def rhs (f : Row 4) (qs : Shape) (r a : ℕ) (cc v : ℚ) (B η : Fin 3 → ℕ) : ℚ :=
  let Yb : Fin 3 → ℕ := fun i => B i - (a * coord (shape f) i + η i)
  (1 - cc) * Tm f (boxOfL Yb) (boxOfL Yb) + Tm f (boxOfL η) (boxOfL Yb) +
    ((r - a : ℕ) : ℚ) * Tm f (shape f).chamber (boxOfL η) +
    cc * ((r - a : ℕ) : ℚ) * Tm f (shape f).chamber (boxOfL Yb) +
    v * ((r - a : ℕ) : ℚ) ^ 2 * Tm f (shape f).chamber qs

def GoodAt (A : ℕ) (f : Row 4) (qs : Shape) (r a : ℕ) (cc v : ℚ) (B η : Fin 3 → ℕ) : Prop :=
  a < r ∧ Gate6966TwoCut.ClassCert r a cc v ∧ rhs f qs r a cc v B η ≤ (A : ℚ) * ((r - a : ℕ) : ℚ) ^ 2

variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}

theorem level_dichotomy_ord (hf : Low6966Prices.SmallFactor f)
    (D : Data Γ s f Q l {P | Persistent Γ s P}) (input : CutInput Γ s f Q l)
    (qs : Shape) (hbs : InBox (shape (K1_13_6.separant f)) qs) (hcs : K1_13_6_2_3.ChamberBox qs)
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
    have hcf : K1_13_6_2_3.ChamberBox (shape f).chamber :=
      ⟨(K1_13_7_1.shape_chamber f).1, (K1_13_7_1.shape_chamber f).2, hf.2.1⟩
    have hbox : ∀ G : Row 4, InBox (shape G) (shape G).chamber := fun G =>
      ⟨le_max_left _ _, le_rfl, le_rfl⟩
    have hmain := Gate6966TwoCut.two_cut_count_ordinary D input D.branches (subset_refl _) H K1 K2
      (K1_13_6.separant f) (shape f).chamber (boxOfL fun k => coord (shape H) k)
      (boxOfL fun k => B k - (a * coord (shape f) k + coord (shape H) k))
      (boxOfL fun k => B k - (a * coord (shape f) k + coord (shape H) k)) qs
      (hbox f) (inBox_boxOfL (fun k => le_rfl)) (inBox_boxOfL hs1) (inBox_boxOfL hs2) hbs
      hcf (boxOfL_chamber _) (boxOfL_chamber _) (boxOfL_chamber _) hcs r a (cert a).1 (cert a).2
      (hc0 a) (hc1 a) (hv0 a) hcertA e m hf0 hH0 hK10 hf0' hH0' hK10' hsf0 hsf0' hfH hfG hHG hGG hfs
      (fun b hb => he b.surface (hmemS b hb)) (fun b hb => hm' b.surface (hmemS b hb)) rfl
      (fun b hb => hQ1 b.surface (hmemS b hb)) (fun b hb => hQ2 b.surface (hmemS b hb)) hlt.le
    have hρ : (0 : ℚ) < ((r - a : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hlt
    have hN := Gate6966TwoCut.mark_bound_of_good hρ hmain (by exact hrhs)
    have : ((tally D D.branches : ℕ) : ℚ) ≤ (A : ℚ) := by
      simpa [tally] using hN
    exact_mod_cast this

theorem two_cut_price_ordinary {w : P3.I → K} (hm : Low6966Prices.Messages w Γ s) (hf : Low6966Prices.SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (hl : 0 < l)
    (hproper : Low6966Prices.ProperCut f Γ s l)
    (qs : Shape) (hbs : InBox (shape (K1_13_6.separant f)) qs) (hcs : K1_13_6_2_3.ChamberBox qs)
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
    obtain ⟨a, η, hd, hfit, hval, hg⟩ := level_dichotomy_ord hf data' input' qs hbs hcs hnd A (i + 1) (B i)
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

end Gate6966FinalOrd

end Merged_Gate6966FinalOrd

-- merged module Gate6966GlueO
section Merged_Gate6966GlueO

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Gate6966Cell
open Gate6966FreeCard (mx mn mx_eq mn_eq)
open K1_13 (Row Shape shape InBox mixed32)
open Gate6966Bilinear (opOf OP)
open Low6966SharedPrice (coord)

theorem Tm_le (G : Gt) (zx wx zh wh q1 q2 : Shape) (num den : ℕ) (hden : 0 < den)
    (hM : ∀ i k', (opOf zh wh).ray i k' = G.mat i k')
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (opOf zx wx).ray i k' ≤ num * (opOf zh wh).ray i k')
    (c1 : q1.j ≤ q1.b ∧ 3 * q1.t ≤ q1.j) (c2 : q2.j ≤ q2.b ∧ 3 * q2.t ≤ q2.j) :
    (mixed32 q1 q2 zx wx : ℚ) ≤ (num : ℚ) / den * (TT G q1.b q1.j q1.t q2.b q2.j q2.t : ℚ) := by
  have h := Gate6966Bilinear.mixed32_theta zx wx zh wh q1 q2 num den hθ c1.1 c1.2 c2.1 c2.2
  have e : mixed32 q1 q2 zh wh = TT G q1.b q1.j q1.t q2.b q2.j q2.t := by
    rw [Gate6966Bilinear.mixed32_cone zh wh q1 q2 c1.1 c1.2 c2.1 c2.2, Gate6966Bilinear.ocone_expand]
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
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (opOf (K1_13.chart (Low6966Prices.taylorLength + 1) (shape f).chamber)
        (K1_13.chart (Low6966Prices.taylorLength + 2) (shape f).chamber)).ray i k' ≤ num * (opOf zh wh).ray i k')
    (hA : num * G.A ≤ den * Ax)
    (qs : Shape) (hqs : qs = ⟨G.sep.1, G.sep.2.1, G.sep.2.2⟩)
    (r a cn vn W : ℕ) (B η : Fin 3 → ℕ) (hρ : a < r) (hcn : cn ≤ 2 * (r - a))
    (hI : lhsV (mkPr G r a cn vn W (B 0) (B 1) (B 2)) (B 0 - a * G.lb - η 0) (B 1 - a * G.lj - η 1)
      (B 2 - a * G.lt - η 2) (η 0) (η 1) (η 2) ≤ (mkPr G r a cn vn W (B 0) (B 1) (B 2)).rhs) :
    Gate6966FinalOrd.rhs f qs r a ((cn : ℚ) / (2 * ((r - a : ℕ) : ℚ))) ((vn : ℚ) / 10000000) B η ≤
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
  unfold Gate6966FinalOrd.rhs Gate6966FinalOrd.Tm
  have cq := Gate6966FinalOrd.boxOfL_chamber Yb
  have ce := Gate6966FinalOrd.boxOfL_chamber η
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
  simp only [Gate6966FinalOrd.boxOfL] at t1 t2 t3 t4 t5 m3 m4 ⊢
  simp only [hYb] at t1 t2 t4 m4 core
  simp only [mx_eq] at m3 m4
  exact alg32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcc0 hcc1 hρpos hv0 hN t1 t2 t3 t4 t5
    (Nat.cast_le.mpr m3) (Nat.cast_le.mpr m4) (Nat.cast_le.mpr m5) core hA'

end Gate6966Cell

end Merged_Gate6966GlueO

-- merged module Gate6966GateO
section Merged_Gate6966GateO

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace Gate6966Cell
open P3 (K)
open K1_13 (Row Shape shape InBox)
open Gate6966Bilinear (opOf)
open Low6966SharedPrice (coord)
open Gate6966FreeCard (mx)
open Gate6966CertCF (cvOf cvOf_le certF certF_bounds certF_class)
open scoped Polynomial BigOperators

theorem price_O {w : P3.I → K} {Γ : Finset K} {s : K → (Polynomial K)} {f : Row 4} {l : ℕ}
    (hm : Low6966Prices.Messages w Γ s) (hf : Low6966Prices.SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (hl : 0 < l)
    (hproper : Low6966Prices.ProperCut f Γ s l) (hchar : f.degreeOf 3 < K1.p)
    (hcx : 3 * (shape f).t ≤ (shape f).j)
    (G : Gt) (hG : G.Ok) (hlift : G.lift = true) (hsc : G.sc = 32)
    (hxt : 3 * G.xt ≤ G.xj) (hpos : 0 < G.lb ∧ 0 < G.lj ∧ 0 < G.lt) (hxj : 3 ≤ G.xj)
    (hlo : G.lb ≤ (shape f).b ∧ G.lj ≤ (shape f).j ∧ G.lt ≤ (shape f).t)
    (hhi : (shape f).b ≤ G.xb ∧ (shape f).j ≤ G.xj ∧ (shape f).t ≤ G.xt)
    (zh wh : Shape) (hM : ∀ i k', (opOf zh wh).ray i k' = G.mat i k')
    (num den Ax : ℕ) (hden : 0 < den)
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (opOf (K1_13.chart (Low6966Prices.taylorLength + 1) (shape f).chamber)
        (K1_13.chart (Low6966Prices.taylorLength + 2) (shape f).chamber)).ray i k' ≤ num * (opOf zh wh).ray i k')
    (hA : num * G.A ≤ den * Ax)
    (r0 : ℕ) (ws : List ℕ) (ht : Gate6966ClassTable.tableOK r0 ws = true) (lv : Lv) (n : ℕ) (hn : n = lv.length)
    (hr0 : r0 + ws.length ≤ n + 1) (hL : n ≤ Gate6966Final.levelCount)
    (hall : allOK G r0 ws lv 0 n = true)
    (ρ0 amax : ℕ) (hρ0 : 0 < ρ0) (hru : ρ0 + amax ≤ n + 1)
    (hamax : ∀ a, a * G.lb ≤ 4012 → a * G.lj ≤ 1650 → a * G.lt ≤ 550 → a ≤ amax)
    (hS0 : G.tsep ≤ G.sc * G.A * VD)
    (hS1 : 2 * VD * TT G (mx G.xb G.xj) G.xj G.xt 4012 1650 550 ≤ (G.sc * G.A * VD - G.tsep) * ρ0)
    (hS2 : 2 * VD * TT G (mx G.xb G.xj) G.xj G.xt 4012 1650 550 * ρ0 +
        VD * (2 * TT G 4012 1650 550 4012 1650 550 + amax * amax * G.tsep) ≤ (G.sc * G.A * VD - G.tsep) * (ρ0 * ρ0))
    (hs : (∑ i ∈ Finset.range n, lsum lv i) < Low6966Prices.layerNeed) :
    Γ.card ≤ Ax + Low6966SharedPrice.additiveBase (shape f) l + Low6966SharedPrice.nonsharedFee (shape f) l := by
  have hf0 : f ≠ 0 := hf.1.ne_zero
  have htpos : 0 < f.degreeOf 3 := by
    have : (shape f).t = f.degreeOf 3 := rfl
    omega
  have hnd : ¬ f ∣ K1_13_6.separant f := KoalaFarBridge.separant_proper hf0 htpos hchar
  have sb := KoalaFarBridge.separant_box f
  set qs : Shape := ⟨G.sep.1, G.sep.2.1, G.sep.2.2⟩ with hqs
  have hsep : G.sep = (mx (mx (G.xb - 1) (G.xj - 3)) (mx (G.xj - 3) 3), mx (G.xj - 3) 3,
      mx (Gate6966FreeCard.mn (G.xt - 1) ((G.xj - 3) / 3)) 1) := by
    simp only [Gt.sep, hlift, hB, hJ, hT, Bool.cond_true]
  have hbs : InBox (shape (K1_13_6.separant f)) qs := by
    refine ⟨?_, ?_, ?_⟩
    · have := sb.1
      simp only [hqs, hsep, Gate6966FreeCard.mx_eq]
      exact this.trans ((Nat.sub_le_sub_right hhi.1 1).trans ((le_max_left _ _).trans (le_max_left _ _)))
    · have := sb.2.1
      simp only [hqs, hsep, Gate6966FreeCard.mx_eq]
      exact this.trans ((Nat.sub_le_sub_right hhi.2.1 3).trans (le_max_left _ _))
    · have := sb.2.2
      simp only [hqs, hsep, Gate6966FreeCard.mn_eq, Gate6966FreeCard.mx_eq]
      refine this.trans (le_trans ?_ (le_max_left _ _))
      refine le_min (Nat.sub_le_sub_right hhi.2.2 1) ?_
      refine (Nat.le_div_iff_mul_le (by norm_num)).mpr ?_
      show ((shape f).t - 1) * 3 ≤ G.xj - 3
      omega
  have hcs : K1_13_6_2_3.ChamberBox qs := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [hqs, hsep, Gate6966FreeCard.mx_eq]
      exact le_max_right _ _
    · simp only [hqs, hsep, Gate6966FreeCard.mn_eq, Gate6966FreeCard.mx_eq]
      have := Nat.min_le_right (G.xt - 1) ((G.xj - 3) / 3)
      rcases le_total (min (G.xt - 1) ((G.xj - 3) / 3)) 1 with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; omega
    · simp only [hqs, hsep, Gate6966FreeCard.mx_eq]
      exact lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hxl : G.lb ≤ coord (shape f) 0 ∧ G.lj ≤ coord (shape f) 1 ∧ G.lt ≤ coord (shape f) 2 := hlo
  have hsum := hsum_of lv n hn hL hs
  refine Gate6966FinalOrd.two_cut_price_ordinary hm hf hon hl hproper qs hbs hcs hnd Ax (Bof lv) (Wof lv)
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

end Gate6966Cell

end Merged_Gate6966GateO

-- merged module Gate6966Fin
section Merged_Gate6966Fin

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
set_option Elab.async false

namespace Gate6966Fin
open Gate6966Cell
open K1_13 (Shape shape)
open Gate6966Bilinear (tpOf opOf)

def DEN : ℕ := 10000000
def kT : ℕ := Low6966Prices.taylorLength - 4
def rayT (p : Shape) : Fin 3 → Fin 3 → ℤ :=
  (tpOf p kT (Low6966Prices.bentLift kT p).2 (Low6966Prices.bentLift (kT + 1) p).2).ray
def rayO (p : Shape) : Fin 3 → Fin 3 → ℤ :=
  (opOf (K1_13.chart (Low6966Prices.taylorLength + 1) p.chamber)
    (K1_13.chart (Low6966Prices.taylorLength + 2) p.chamber)).ray

def savedT (p : Shape) : Fin 3 → Fin 3 → ℤ :=
  (tpOf p 133446 (Low6966Prices.bentLift 133446 p).2 (Low6966Prices.bentLift 133447 p).2).ray
def savedO (p : Shape) : Fin 3 → Fin 3 → ℤ :=
  (opOf (K1_13.chart 133451 p.chamber) (K1_13.chart 133452 p.chamber)).ray

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

def numT (G : Gt) (x : Shape) : ℕ := thNum (rayT x) (savedT (hiS G))
def numO (G : Gt) (x : Shape) : ℕ := thNum (rayO x) (savedO (hiS G))
def Ax (num A : ℕ) : ℕ := (num * A + DEN - 1) / DEN

def valid (x : Shape) : Bool := Nat.ble x.j (2 * x.b + x.t)

def Gk : ℕ → Gt
  | 1 => Witness6966DatETr5.G
  | 2 => Witness6966DatETr3x.G
  | 3 => Witness6966DatS48x.G
  | 4 => Witness6966DatETm.G
  | 5 => Witness6966DatO1j54.G
  | 6 => Witness6966DatO1j55.G
  | 7 => Witness6966DatO2b.G
  | 8 => Witness6966DatS1.G
  | 9 => Witness6966DatO2a.G
  | _ => Witness6966DatETr5.G
def isT : ℕ → Bool
  | 1 => true
  | 2 => true
  | 3 => true
  | 4 => true
  | 5 => false
  | 6 => false
  | 7 => false
  | 8 => false
  | 9 => false
  | _ => false

def okK (k : ℕ) (x : Shape) : Bool := valid x && inR (Gk k) x && (if isT k then tfB x else !tfB x)

private def choices : ℕ → ℕ → List (ℕ × ℕ)
  | 39,13 => [(142,9)]
  | 40,13 => [(141,8), (142,9)]
  | 41,13 => [(125,9), (141,8), (142,9)]
  | 42,14 => [(125,9), (141,8), (142,9)]
  | 43,9 => [(142,4)]
  | 43,10 => [(142,4)]
  | 43,11 => [(142,4)]
  | 43,12 => [(142,4)]
  | 43,13 => [(142,4)]
  | 43,14 => [(116,7), (125,9), (141,8), (142,9)]
  | 44,7 => [(142,4)]
  | 44,8 => [(142,4)]
  | 44,9 => [(142,4)]
  | 44,10 => [(142,4)]
  | 44,11 => [(142,4)]
  | 44,12 => [(142,4)]
  | 44,13 => [(142,4)]
  | 44,14 => [(116,7), (125,9), (141,8), (142,9)]
  | 45,5 => [(142,4)]
  | 45,6 => [(142,4)]
  | 45,7 => [(142,4)]
  | 45,8 => [(142,4)]
  | 45,9 => [(142,4)]
  | 45,10 => [(142,4)]
  | 45,11 => [(142,4)]
  | 45,12 => [(142,4)]
  | 45,13 => [(142,4)]
  | 45,14 => [(137,4), (142,3)]
  | 45,15 => [(142,9)]
  | 46,2 => [(142,4)]
  | 46,4 => [(142,4)]
  | 46,5 => [(142,4)]
  | 46,6 => [(142,4)]
  | 46,7 => [(142,4)]
  | 46,8 => [(142,4)]
  | 46,9 => [(142,4)]
  | 46,10 => [(142,4)]
  | 46,11 => [(142,4)]
  | 46,12 => [(142,4)]
  | 46,13 => [(142,4)]
  | 46,14 => [(137,4), (142,3)]
  | 46,15 => [(142,9)]
  | 47,2 => [(142,4)]
  | 47,3 => [(142,4)]
  | 47,4 => [(142,4)]
  | 47,5 => [(142,4)]
  | 47,6 => [(142,4)]
  | 47,7 => [(142,4)]
  | 47,8 => [(142,4)]
  | 47,9 => [(142,4)]
  | 47,10 => [(142,4)]
  | 47,11 => [(142,4)]
  | 47,12 => [(142,4)]
  | 47,13 => [(142,4)]
  | 47,14 => [(137,4), (142,3)]
  | 47,15 => [(142,9)]
  | 48,2 => [(142,4)]
  | 48,3 => [(142,4)]
  | 48,4 => [(142,4)]
  | 48,5 => [(142,4)]
  | 48,6 => [(142,4)]
  | 48,7 => [(142,4)]
  | 48,8 => [(142,4)]
  | 48,9 => [(142,4)]
  | 48,10 => [(142,4)]
  | 48,11 => [(142,4)]
  | 48,12 => [(142,4)]
  | 48,13 => [(142,4)]
  | 48,14 => [(137,4), (142,3)]
  | 48,15 => [(142,4)]
  | 49,2 => [(142,4)]
  | 49,3 => [(142,4)]
  | 49,4 => [(142,4)]
  | 49,5 => [(142,4)]
  | 49,6 => [(142,4)]
  | 49,7 => [(142,4)]
  | 49,8 => [(142,4)]
  | 49,9 => [(142,4)]
  | 49,10 => [(142,4)]
  | 49,11 => [(142,4)]
  | 49,12 => [(142,4)]
  | 49,13 => [(142,4)]
  | 49,14 => [(142,4)]
  | 49,15 => [(142,4)]
  | 50,2 => [(142,4)]
  | 50,3 => [(142,4)]
  | 50,4 => [(142,4)]
  | 50,5 => [(142,4)]
  | 50,6 => [(142,4)]
  | 50,7 => [(142,4)]
  | 50,8 => [(142,4)]
  | 50,9 => [(142,4)]
  | 50,10 => [(142,4)]
  | 50,11 => [(142,4)]
  | 50,12 => [(142,4)]
  | 50,13 => [(142,4)]
  | 50,14 => [(142,4)]
  | 50,15 => [(142,4)]
  | 51,2 => [(142,1)]
  | 51,3 => [(142,1)]
  | 51,4 => [(142,1)]
  | 51,5 => [(142,1)]
  | 51,6 => [(142,1)]
  | 51,7 => [(142,1)]
  | 51,8 => [(97,4), (142,1)]
  | 51,9 => [(97,4), (142,1)]
  | 51,10 => [(97,4), (119,1), (142,4)]
  | 51,11 => [(142,4)]
  | 51,12 => [(142,4)]
  | 51,13 => [(20,5), (142,4)]
  | 51,14 => [(19,5), (142,4)]
  | 51,15 => [(142,4)]
  | 52,2 => [(142,1)]
  | 52,3 => [(142,1)]
  | 52,4 => [(142,1)]
  | 52,5 => [(142,1)]
  | 52,6 => [(142,1)]
  | 52,7 => [(142,1)]
  | 52,8 => [(97,4), (142,1)]
  | 52,9 => [(97,4), (142,1)]
  | 52,10 => [(97,4), (124,1), (142,4)]
  | 52,11 => [(22,5), (142,4)]
  | 52,12 => [(23,5), (142,4)]
  | 52,13 => [(23,5), (142,4)]
  | 52,14 => [(23,5), (142,4)]
  | 52,15 => [(142,4)]
  | 53,2 => [(142,1)]
  | 53,3 => [(142,1)]
  | 53,4 => [(142,1)]
  | 53,5 => [(105,2), (142,1)]
  | 53,6 => [(105,2), (142,1)]
  | 53,7 => [(105,2), (142,1)]
  | 53,8 => [(105,2), (142,1)]
  | 53,9 => [(105,2), (142,1)]
  | 53,10 => [(22,5), (110,2), (142,1)]
  | 53,11 => [(23,5), (110,2), (142,4)]
  | 53,12 => [(25,5), (110,2), (142,4)]
  | 53,13 => [(25,5), (110,2), (142,4)]
  | 53,14 => [(25,5), (110,2), (142,4)]
  | 53,15 => [(142,4)]
  | 54,2 => [(107,2), (142,1)]
  | 54,3 => [(142,1)]
  | 54,4 => [(107,2), (142,1)]
  | 54,5 => [(107,2), (142,1)]
  | 54,6 => [(107,2), (142,1)]
  | 54,7 => [(107,2), (142,1)]
  | 54,8 => [(107,2), (142,1)]
  | 54,9 => [(107,2), (142,1)]
  | 54,10 => [(25,5), (110,2), (142,1)]
  | 54,11 => [(27,5), (110,2), (142,4)]
  | 54,12 => [(28,5), (110,2), (142,4)]
  | 54,13 => [(29,5), (110,2), (142,4)]
  | 54,14 => [(29,5), (110,2), (142,4)]
  | 54,15 => [(142,4)]
  | 55,2 => [(110,2), (142,1)]
  | 55,3 => [(110,2), (142,1)]
  | 55,4 => [(110,2), (142,1)]
  | 55,5 => [(110,2), (142,1)]
  | 55,6 => [(110,2), (142,1)]
  | 55,7 => [(110,2), (142,1)]
  | 55,8 => [(110,2), (142,1)]
  | 55,9 => [(28,6), (110,2), (142,1)]
  | 55,10 => [(30,6), (110,2), (142,1)]
  | 55,11 => [(32,6), (110,2), (142,4)]
  | 55,12 => [(35,6), (110,2), (142,4)]
  | 55,13 => [(37,6), (110,2), (142,4)]
  | 55,14 => [(38,6), (110,2), (142,4)]
  | 55,15 => [(142,4)]
  | 56,2 => [(142,1)]
  | 56,3 => [(142,1)]
  | 56,4 => [(142,1)]
  | 56,5 => [(142,1)]
  | 56,6 => [(142,1)]
  | 56,7 => [(142,1)]
  | 56,8 => [(142,1)]
  | 56,9 => [(142,1)]
  | 56,10 => [(142,1)]
  | 56,11 => [(142,4)]
  | 56,12 => [(142,4)]
  | 56,13 => [(142,4)]
  | 56,14 => [(142,4)]
  | 56,15 => [(142,4)]
  | 57,2 => [(142,1)]
  | 57,3 => [(142,1)]
  | 57,4 => [(142,1)]
  | 57,5 => [(142,1)]
  | 57,6 => [(142,1)]
  | 57,7 => [(142,1)]
  | 57,8 => [(142,1)]
  | 57,9 => [(142,1)]
  | 57,10 => [(97,4), (142,1)]
  | 57,11 => [(142,4)]
  | 57,12 => [(142,4)]
  | 57,13 => [(142,4)]
  | 57,14 => [(142,4)]
  | 57,15 => [(142,4)]
  | 58,2 => [(142,1)]
  | 58,3 => [(142,1)]
  | 58,4 => [(142,1)]
  | 58,5 => [(142,1)]
  | 58,6 => [(142,1)]
  | 58,7 => [(142,1)]
  | 58,8 => [(97,4), (142,1)]
  | 58,9 => [(97,4), (142,1)]
  | 58,10 => [(97,4), (142,1)]
  | 58,11 => [(142,4)]
  | 58,12 => [(142,4)]
  | 58,13 => [(142,4)]
  | 58,14 => [(142,4)]
  | 58,15 => [(142,4)]
  | _,_ => []
private def pick (b : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (hi,k)::rest => if b≤hi then k else pick b rest
def cls (x : Shape) : ℕ :=
  let k := pick x.b (choices x.j x.t)
  if 1≤k ∧ k≤9 ∧ okK k x then k else 0

def numK (k : ℕ) (x : Shape) : ℕ := if isT k then numT (Gk k) x else numO (Gk k) x
def thK (k : ℕ) (x : Shape) : Bool :=
  if isT k then thOK (rayT x) (savedT (hiS (Gk k))) else thOK (rayO x) (savedO (hiS (Gk k)))
def Gfun (x : Shape) : ℕ := if cls x = 0 then 0 else Ax (numK (cls x) x) (Gk (cls x)).A
def shapeOK (x : Shape) : Bool := if cls x = 0 then false else thK (cls x) x

theorem gl_nil (id t : ℕ) (h : 16 ≤ t) : Low6966Gate.gateList id t = [] := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm]
  rcases Nat.lt_or_ge id 30 with hi | hi
  · interval_cases id <;> rfl
  · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [Nat.add_comm]
    rfl

theorem amax_le (lb lj lt amax : ℕ) (hb : 0 < lb) (hj : 0 < lj) (ht : 0 < lt)
    (h : amax = min (4012 / lb) (min (1650 / lj) (550 / lt))) :
    ∀ a, a * lb ≤ 4012 → a * lj ≤ 1650 → a * lt ≤ 550 → a ≤ amax := by
  intro a h1 h2 h3
  subst h
  exact le_min ((Nat.le_div_iff_mul_le hb).mpr h1) (le_min ((Nat.le_div_iff_mul_le hj).mpr h2)
    ((Nat.le_div_iff_mul_le ht).mpr h3))

theorem ceil_le (N D : ℕ) (hD : 0 < D) : N ≤ D * ((N + D - 1) / D) := by
  have := Gate6966CertCF.ceil_mul N D hD
  rw [Nat.mul_comm]; exact this

theorem cls_cases {x : Shape} {c : ℕ} (h : cls x = c) (hc : c ≠ 0) :
    1 ≤ c ∧ c ≤ 9 ∧ okK c x = true := by
  simp only [cls] at h
  split at h
  · rename_i ok; subst c; exact ok
  · omega

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
    cls x ≠ 0 ∧ thK (cls x) x = true := by
  unfold shapeOK at h
  split_ifs at h with c0
  exact ⟨c0, h⟩

theorem okK_props {k : ℕ} {x : Shape} (h : okK k x = true) :
    valid x = true ∧ inR (Gk k) x = true ∧ (if isT k then tfB x else !tfB x) = true := by
  unfold okK at h
  simpa [Bool.and_eq_true, and_assoc] using h

open P3 (K) in
open scoped Polynomial in
theorem gated_price {w : P3.I → K} {Γ : Finset K} {s : K → (Polynomial K)} {f : K1_13.Row 4} {l : ℕ}
    (hm : Low6966Prices.Messages w Γ s) (hf : Low6966Prices.SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (hl : 0 < l)
    (hproper : Low6966Prices.ProperCut f Γ s l) (hchar : f.degreeOf 3 < K1.p)
    (hx : shapeOK (shape f) = true) :
    Γ.card ≤ Gfun (shape f) + Low6966SharedPrice.additiveBase (shape f) l +
      Low6966SharedPrice.nonsharedFee (shape f) l := by
  obtain ⟨hc, hth⟩ := shapeOK_cases hx
  obtain ⟨c1, c2, hok⟩ := cls_cases (rfl : cls (shape f) = cls (shape f)) hc
  obtain ⟨_, hin, htf⟩ := okK_props hok
  generalize hcc : cls (shape f) = c at *
  interval_cases c
  · -- gate 1 = ETr5
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have htf' : tfB (shape f) = true := by simpa [isT] using htf
    have key := price_T hm hf hon hl hproper hchar (tfB_true htf') Witness6966DatETr5.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl (by decide)
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩ kT
          (Low6966Prices.bentLift 133446 (hiS Witness6966DatETr5.G)).2 (Low6966Prices.bentLift 133447 (hiS Witness6966DatETr5.G)).2
          (Low6966Prices.bentLift kT (shape f)).2 (Low6966Prices.bentLift (kT + 1) (shape f)).2 rfl rfl rfl rfl rfl
          (by decide +kernel) (numT Witness6966DatETr5.G (shape f)) DEN (Ax (numT Witness6966DatETr5.G (shape f)) Witness6966DatETr5.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Witness6966DatETr5.ws Witness6966DatETr5.tabOK Witness6966DatETr5.lv Witness6966DatETr5.n rfl
          (by decide +kernel) (by decide +kernel) Witness6966DatETr5.allOKn Witness6966DatETr5.rho0 Witness6966DatETr5.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Witness6966DatETr5.sumLt
    simp only [Gfun, hcc, show numK 1 (shape f) = numT Witness6966DatETr5.G (shape f) from rfl]
    have e1 : (Gk 1).A = Witness6966DatETr5.G.A := rfl
    simpa [e1] using key
  · -- gate 2 = ETr3x
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have htf' : tfB (shape f) = true := by simpa [isT] using htf
    have key := price_T hm hf hon hl hproper hchar (tfB_true htf') Witness6966DatETr3x.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl (by decide)
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩ kT
          (Low6966Prices.bentLift 133446 (hiS Witness6966DatETr3x.G)).2 (Low6966Prices.bentLift 133447 (hiS Witness6966DatETr3x.G)).2
          (Low6966Prices.bentLift kT (shape f)).2 (Low6966Prices.bentLift (kT + 1) (shape f)).2 rfl rfl rfl rfl rfl
          (by decide +kernel) (numT Witness6966DatETr3x.G (shape f)) DEN (Ax (numT Witness6966DatETr3x.G (shape f)) Witness6966DatETr3x.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Witness6966DatETr3x.ws Witness6966DatETr3x.tabOK Witness6966DatETr3x.lv Witness6966DatETr3x.n rfl
          (by decide +kernel) (by decide +kernel) Witness6966DatETr3x.allOKn Witness6966DatETr3x.rho0 Witness6966DatETr3x.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Witness6966DatETr3x.sumLt
    simp only [Gfun, hcc, show numK 2 (shape f) = numT Witness6966DatETr3x.G (shape f) from rfl]
    have e1 : (Gk 2).A = Witness6966DatETr3x.G.A := rfl
    simpa [e1] using key
  · -- gate 3 = S48x
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have htf' : tfB (shape f) = true := by simpa [isT] using htf
    have key := price_T hm hf hon hl hproper hchar (tfB_true htf') Witness6966DatS48x.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl (by decide)
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩ kT
          (Low6966Prices.bentLift 133446 (hiS Witness6966DatS48x.G)).2 (Low6966Prices.bentLift 133447 (hiS Witness6966DatS48x.G)).2
          (Low6966Prices.bentLift kT (shape f)).2 (Low6966Prices.bentLift (kT + 1) (shape f)).2 rfl rfl rfl rfl rfl
          (by decide +kernel) (numT Witness6966DatS48x.G (shape f)) DEN (Ax (numT Witness6966DatS48x.G (shape f)) Witness6966DatS48x.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Witness6966DatS48x.ws Witness6966DatS48x.tabOK Witness6966DatS48x.lv Witness6966DatS48x.n rfl
          (by decide +kernel) (by decide +kernel) Witness6966DatS48x.allOKn Witness6966DatS48x.rho0 Witness6966DatS48x.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Witness6966DatS48x.sumLt
    simp only [Gfun, hcc, show numK 3 (shape f) = numT Witness6966DatS48x.G (shape f) from rfl]
    have e1 : (Gk 3).A = Witness6966DatS48x.G.A := rfl
    simpa [e1] using key
  · -- gate 4 = ETm
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have htf' : tfB (shape f) = true := by simpa [isT] using htf
    have key := price_T hm hf hon hl hproper hchar (tfB_true htf') Witness6966DatETm.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl (by decide)
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩ kT
          (Low6966Prices.bentLift 133446 (hiS Witness6966DatETm.G)).2 (Low6966Prices.bentLift 133447 (hiS Witness6966DatETm.G)).2
          (Low6966Prices.bentLift kT (shape f)).2 (Low6966Prices.bentLift (kT + 1) (shape f)).2 rfl rfl rfl rfl rfl
          (by decide +kernel) (numT Witness6966DatETm.G (shape f)) DEN (Ax (numT Witness6966DatETm.G (shape f)) Witness6966DatETm.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Witness6966DatETm.ws Witness6966DatETm.tabOK Witness6966DatETm.lv Witness6966DatETm.n rfl
          (by decide +kernel) (by decide +kernel) Witness6966DatETm.allOKn Witness6966DatETm.rho0 Witness6966DatETm.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Witness6966DatETm.sumLt
    simp only [Gfun, hcc, show numK 4 (shape f) = numT Witness6966DatETm.G (shape f) from rfl]
    have e1 : (Gk 4).A = Witness6966DatETm.G.A := rfl
    simpa [e1] using key
  · -- gate 5 = O1j54
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
    have key := price_O hm hf hon hl hproper hchar hcx Witness6966DatO1j54.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩
          (K1_13.chart 133451 (hiS Witness6966DatO1j54.G).chamber)
          (K1_13.chart 133452 (hiS Witness6966DatO1j54.G).chamber)
          (by decide +kernel) (numO Witness6966DatO1j54.G (shape f)) DEN (Ax (numO Witness6966DatO1j54.G (shape f)) Witness6966DatO1j54.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Witness6966DatO1j54.ws Witness6966DatO1j54.tabOK Witness6966DatO1j54.lv Witness6966DatO1j54.n rfl
          (by decide +kernel) (by decide +kernel) Witness6966DatO1j54.allOKn Witness6966DatO1j54.rho0 Witness6966DatO1j54.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Witness6966DatO1j54.sumLt
    simp only [Gfun, hcc, show numK 5 (shape f) = numO Witness6966DatO1j54.G (shape f) from rfl]
    have e1 : (Gk 5).A = Witness6966DatO1j54.G.A := rfl
    simpa [e1] using key
  · -- gate 6 = O1j55
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
    have key := price_O hm hf hon hl hproper hchar hcx Witness6966DatO1j55.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩
          (K1_13.chart 133451 (hiS Witness6966DatO1j55.G).chamber)
          (K1_13.chart 133452 (hiS Witness6966DatO1j55.G).chamber)
          (by decide +kernel) (numO Witness6966DatO1j55.G (shape f)) DEN (Ax (numO Witness6966DatO1j55.G (shape f)) Witness6966DatO1j55.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Witness6966DatO1j55.ws Witness6966DatO1j55.tabOK Witness6966DatO1j55.lv Witness6966DatO1j55.n rfl
          (by decide +kernel) (by decide +kernel) Witness6966DatO1j55.allOKn Witness6966DatO1j55.rho0 Witness6966DatO1j55.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Witness6966DatO1j55.sumLt
    simp only [Gfun, hcc, show numK 6 (shape f) = numO Witness6966DatO1j55.G (shape f) from rfl]
    have e1 : (Gk 6).A = Witness6966DatO1j55.G.A := rfl
    simpa [e1] using key
  · -- gate 7 = O2b
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
    have key := price_O hm hf hon hl hproper hchar hcx Witness6966DatO2b.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩
          (K1_13.chart 133451 (hiS Witness6966DatO2b.G).chamber)
          (K1_13.chart 133452 (hiS Witness6966DatO2b.G).chamber)
          (by decide +kernel) (numO Witness6966DatO2b.G (shape f)) DEN (Ax (numO Witness6966DatO2b.G (shape f)) Witness6966DatO2b.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Witness6966DatO2b.ws Witness6966DatO2b.tabOK Witness6966DatO2b.lv Witness6966DatO2b.n rfl
          (by decide +kernel) (by decide +kernel) Witness6966DatO2b.allOKn Witness6966DatO2b.rho0 Witness6966DatO2b.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Witness6966DatO2b.sumLt
    simp only [Gfun, hcc, show numK 7 (shape f) = numO Witness6966DatO2b.G (shape f) from rfl]
    have e1 : (Gk 7).A = Witness6966DatO2b.G.A := rfl
    simpa [e1] using key
  · -- gate 8 = S1
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
    have key := price_O hm hf hon hl hproper hchar hcx Witness6966DatS1.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩
          (K1_13.chart 133451 (hiS Witness6966DatS1.G).chamber)
          (K1_13.chart 133452 (hiS Witness6966DatS1.G).chamber)
          (by decide +kernel) (numO Witness6966DatS1.G (shape f)) DEN (Ax (numO Witness6966DatS1.G (shape f)) Witness6966DatS1.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Witness6966DatS1.ws Witness6966DatS1.tabOK Witness6966DatS1.lv Witness6966DatS1.n rfl
          (by decide +kernel) (by decide +kernel) Witness6966DatS1.allOKn Witness6966DatS1.rho0 Witness6966DatS1.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Witness6966DatS1.sumLt
    simp only [Gfun, hcc, show numK 8 (shape f) = numO Witness6966DatS1.G (shape f) from rfl]
    have e1 : (Gk 8).A = Witness6966DatS1.G.A := rfl
    simpa [e1] using key
  · -- gate 9 = O2a
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
    have key := price_O hm hf hon hl hproper hchar hcx Witness6966DatO2a.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩
          (K1_13.chart 133451 (hiS Witness6966DatO2a.G).chamber)
          (K1_13.chart 133452 (hiS Witness6966DatO2a.G).chamber)
          (by decide +kernel) (numO Witness6966DatO2a.G (shape f)) DEN (Ax (numO Witness6966DatO2a.G (shape f)) Witness6966DatO2a.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Witness6966DatO2a.ws Witness6966DatO2a.tabOK Witness6966DatO2a.lv Witness6966DatO2a.n rfl
          (by decide +kernel) (by decide +kernel) Witness6966DatO2a.allOKn Witness6966DatO2a.rho0 Witness6966DatO2a.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Witness6966DatO2a.sumLt
    simp only [Gfun, hcc, show numK 9 (shape f) = numO Witness6966DatO2a.G (shape f) from rfl]
    have e1 : (Gk 9).A = Witness6966DatO2a.G.A := rfl
    simpa [e1] using key

def one (id t : ℕ) : Bool := (Low6966Gate.gateList id t).all fun p => !(valid ⟨p.1, p.2, t⟩) || shapeOK ⟨p.1, p.2, t⟩

end Gate6966Fin

end Merged_Gate6966Fin
