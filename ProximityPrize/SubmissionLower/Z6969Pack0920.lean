import ProximityPrize.SubmissionLower.Z6969Pack0891
import ProximityPrize.SubmissionLower.Witness6966SumO2a
import ProximityPrize.SubmissionLower.Z6969Pack0859
import ProximityPrize.SubmissionLower.Z6969Pack0840
import ProximityPrize.SubmissionLower.Z6969Pack0894
import ProximityPrize.SubmissionLower.Z6969Pack0897
import ProximityPrize.SubmissionLower.Z6969Pack0900
import ProximityPrize.SubmissionLower.Z6969Pack0903
import ProximityPrize.SubmissionLower.Z6969Pack0906
import ProximityPrize.SubmissionLower.Z6969Pack0909
import ProximityPrize.SubmissionLower.Z6969Pack0912
import ProximityPrize.SubmissionLower.Z6969Pack0915
import ProximityPrize.SubmissionLower.Z6969Pack0850
import ProximityPrize.SubmissionLower.Z6969Pack0853

set_option Elab.async false

-- merged module Z6969Pack0918
section Merged_Z6969Pack0918

-- Source: ProximityPrize.SubmissionLower.Low6969WitnessSumO2a
section Z6969Source2489
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000

namespace Low6969WitnessDatO2a

open Low6969GateCell
open scoped BigOperators

def G : Gt := transport Witness6966DatO2a.G
abbrev ws := Witness6966DatO2a.ws
abbrev lv := Witness6966DatO2a.lv
abbrev n := Witness6966DatO2a.n
abbrev rho0 := Witness6966DatO2a.rho0
abbrev amax := Witness6966DatO2a.amax

theorem tabOK : Low6969GateClassTable.tableOK 1 ws = true :=
  (tableOK_transport 1 ws).trans Witness6966DatO2a.tabOK

theorem allOKn : allOK G 1 ws lv 0 n = true :=
  (allOK_transport Witness6966DatO2a.G 1 ws lv 0 n).trans Witness6966DatO2a.allOKn

theorem sumLt : (∑ i ∈ Finset.range n, lsum lv i) < Low6969Prices.layerNeed := by
  simp only [lsum_transport]
  exact Witness6966DatO2a.sumLt.trans_le (by decide)

end Low6969WitnessDatO2a
end Z6969Source2489

-- Source: ProximityPrize.SubmissionLower.Low6969GateFin
section Z6969Source2490
set_option autoImplicit true
set_option Elab.async false

-- merged module Low6969GateFinalOrd
section Merged_Low6969GateFinalOrd

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace Low6969GateFinalOrd

open P3 (K)
open K1_13 (Row Shape shape InBox mixed32)
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
open Low6969GateFinal (levelCount exact_order_fun)
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
  (mixed32 q₁ q₂ (K1_13.chart (Low6969Prices.taylorLength + 1) (shape f).chamber)
    (K1_13.chart (Low6969Prices.taylorLength + 2) (shape f).chamber) : ℚ) / 32

noncomputable def rhs (f : Row 4) (qs : Shape) (r a : ℕ) (cc v : ℚ) (B η : Fin 3 → ℕ) : ℚ :=
  let Yb : Fin 3 → ℕ := fun i => B i - (a * coord (shape f) i + η i)
  (1 - cc) * Tm f (boxOfL Yb) (boxOfL Yb) + Tm f (boxOfL η) (boxOfL Yb) +
    ((r - a : ℕ) : ℚ) * Tm f (shape f).chamber (boxOfL η) +
    cc * ((r - a : ℕ) : ℚ) * Tm f (shape f).chamber (boxOfL Yb) +
    v * ((r - a : ℕ) : ℚ) ^ 2 * Tm f (shape f).chamber qs

def GoodAt (A : ℕ) (f : Row 4) (qs : Shape) (r a : ℕ) (cc v : ℚ) (B η : Fin 3 → ℕ) : Prop :=
  a < r ∧ Low6969GateTwoCut.ClassCert r a cc v ∧ rhs f qs r a cc v B η ≤ (A : ℚ) * ((r - a : ℕ) : ℚ) ^ 2

variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}

theorem level_dichotomy_ord (hf : Low6969Prices.SmallFactor f)
    (D : Data Γ s f Q l {P | Persistent Γ s P}) (input : CutInput Γ s f Q l)
    (qs : Shape) (hbs : InBox (shape (K1_13_6.separant f)) qs) (hcs : K1_13_6_2_3.ChamberBox qs)
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
    have hcf : K1_13_6_2_3.ChamberBox (shape f).chamber :=
      ⟨(K1_13_7_1.shape_chamber f).1, (K1_13_7_1.shape_chamber f).2, hf.2.1⟩
    have hbox : ∀ G : Row 4, InBox (shape G) (shape G).chamber := fun G =>
      ⟨le_max_left _ _, le_rfl, le_rfl⟩
    have hmain := Low6969GateTwoCut.two_cut_count_ordinary D input D.branches (subset_refl _) H K1 K2
      (K1_13_6.separant f) (shape f).chamber (boxOfL fun k => coord (shape H) k)
      (boxOfL fun k => B k - (a * coord (shape f) k + coord (shape H) k))
      (boxOfL fun k => B k - (a * coord (shape f) k + coord (shape H) k)) qs
      (hbox f) (inBox_boxOfL (fun k => le_rfl)) (inBox_boxOfL hs1) (inBox_boxOfL hs2) hbs
      hcf (boxOfL_chamber _) (boxOfL_chamber _) (boxOfL_chamber _) hcs r a (cert a).1 (cert a).2
      (hc0 a) (hc1 a) (hv0 a) hcertA e m hf0 hH0 hK10 hf0' hH0' hK10' hsf0 hsf0' hfH hfG hHG hGG hfs
      (fun b hb => he b.surface (hmemS b hb)) (fun b hb => hm' b.surface (hmemS b hb)) rfl
      (fun b hb => hQ1 b.surface (hmemS b hb)) (fun b hb => hQ2 b.surface (hmemS b hb)) hlt.le
    have hρ : (0 : ℚ) < ((r - a : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hlt
    have hN := Low6969GateTwoCut.mark_bound_of_good hρ hmain (by exact hrhs)
    have : ((tally D D.branches : ℕ) : ℚ) ≤ (A : ℚ) := by
      simpa [tally] using hN
    exact_mod_cast this

theorem two_cut_price_ordinary {w : P3.I → K} (hm : Low6969Prices.Messages w Γ s) (hf : Low6969Prices.SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (hl : 0 < l)
    (hproper : Low6969Prices.ProperCut f Γ s l)
    (qs : Shape) (hbs : InBox (shape (K1_13_6.separant f)) qs) (hcs : K1_13_6_2_3.ChamberBox qs)
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
    obtain ⟨a, η, hd, hfit, hval, hg⟩ := level_dichotomy_ord hf data' input' qs hbs hcs hnd A (i + 1) (B i)
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

end Low6969GateFinalOrd

end Merged_Low6969GateFinalOrd

-- merged module Low6969GateGlueO
section Merged_Low6969GateGlueO

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Low6969GateCell
open Low6969GateFreeCard (mx mn mx_eq mn_eq)
open K1_13 (Row Shape shape InBox mixed32)
open Low6969GateBilinear (opOf OP)
open Low6969SharedPrice (coord)

theorem Tm_le (G : Gt) (zx wx zh wh q1 q2 : Shape) (num den : ℕ) (hden : 0 < den)
    (hM : ∀ i k', (opOf zh wh).ray i k' = Gt.mat G i k')
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (opOf zx wx).ray i k' ≤ num * (opOf zh wh).ray i k')
    (c1 : q1.j ≤ q1.b ∧ 3 * q1.t ≤ q1.j) (c2 : q2.j ≤ q2.b ∧ 3 * q2.t ≤ q2.j) :
    (mixed32 q1 q2 zx wx : ℚ) ≤ (num : ℚ) / den * (TT G q1.b q1.j q1.t q2.b q2.j q2.t : ℚ) := by
  have h := Low6969GateBilinear.mixed32_theta zx wx zh wh q1 q2 num den hθ c1.1 c1.2 c2.1 c2.2
  have e : mixed32 q1 q2 zh wh = TT G q1.b q1.j q1.t q2.b q2.j q2.t := by
    rw [Low6969GateBilinear.mixed32_cone zh wh q1 q2 c1.1 c1.2 c2.1 c2.2, Low6969GateBilinear.ocone_expand]
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
    (zh wh : Shape) (hM : ∀ i k', (opOf zh wh).ray i k' = Gt.mat G i k')
    (num den Ax : ℕ) (hden : 0 < den)
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (opOf (K1_13.chart (Low6969Prices.taylorLength + 1) (shape f).chamber)
        (K1_13.chart (Low6969Prices.taylorLength + 2) (shape f).chamber)).ray i k' ≤ num * (opOf zh wh).ray i k')
    (hA : num * G.A ≤ den * Ax)
    (qs : Shape) (hqs : qs = ⟨G.sep.1, G.sep.2.1, G.sep.2.2⟩)
    (r a cn vn W : ℕ) (B η : Fin 3 → ℕ) (hρ : a < r) (hcn : cn ≤ 2 * (r - a))
    (hI : lhsV (mkPr G r a cn vn W (B 0) (B 1) (B 2)) (B 0 - a * G.lb - η 0) (B 1 - a * G.lj - η 1)
      (B 2 - a * G.lt - η 2) (η 0) (η 1) (η 2) ≤ (mkPr G r a cn vn W (B 0) (B 1) (B 2)).rhs) :
    Low6969GateFinalOrd.rhs f qs r a ((cn : ℚ) / (2 * ((r - a : ℕ) : ℚ))) ((vn : ℚ) / 10000000) B η ≤
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
  unfold Low6969GateFinalOrd.rhs Low6969GateFinalOrd.Tm
  have cq := Low6969GateFinalOrd.boxOfL_chamber Yb
  have ce := Low6969GateFinalOrd.boxOfL_chamber η
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
  simp only [Low6969GateFinalOrd.boxOfL] at t1 t2 t3 t4 t5 m3 m4 ⊢
  simp only [hYb] at t1 t2 t4 m4 core
  simp only [mx_eq] at m3 m4
  exact alg32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcc0 hcc1 hρpos hv0 hN t1 t2 t3 t4 t5
    (Nat.cast_le.mpr m3) (Nat.cast_le.mpr m4) (Nat.cast_le.mpr m5) core hA'

end Low6969GateCell

end Merged_Low6969GateGlueO

-- merged module Low6969GateGateO
section Merged_Low6969GateGateO

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace Low6969GateCell
open P3 (K)
open K1_13 (Row Shape shape InBox)
open Low6969GateBilinear (opOf)
open Low6969SharedPrice (coord)
open Low6969GateFreeCard (mx)
open Low6969GateCertCF (cvOf cvOf_le certF certF_bounds certF_class)
open scoped Polynomial BigOperators

theorem price_O {w : P3.I → K} {Γ : Finset K} {s : K → (Polynomial K)} {f : Row 4} {l : ℕ}
    (hm : Low6969Prices.Messages w Γ s) (hf : Low6969Prices.SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (hl : 0 < l)
    (hproper : Low6969Prices.ProperCut f Γ s l) (hchar : f.degreeOf 3 < K1.p)
    (hcx : 3 * (shape f).t ≤ (shape f).j)
    (G : Gt) (hG : G.Ok) (hlift : G.lift = true) (hsc : G.sc = 32)
    (hxt : 3 * G.xt ≤ G.xj) (hpos : 0 < G.lb ∧ 0 < G.lj ∧ 0 < G.lt) (hxj : 3 ≤ G.xj)
    (hlo : G.lb ≤ (shape f).b ∧ G.lj ≤ (shape f).j ∧ G.lt ≤ (shape f).t)
    (hhi : (shape f).b ≤ G.xb ∧ (shape f).j ≤ G.xj ∧ (shape f).t ≤ G.xt)
    (zh wh : Shape) (hM : ∀ i k', (opOf zh wh).ray i k' = Gt.mat G i k')
    (num den Ax : ℕ) (hden : 0 < den)
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (opOf (K1_13.chart (Low6969Prices.taylorLength + 1) (shape f).chamber)
        (K1_13.chart (Low6969Prices.taylorLength + 2) (shape f).chamber)).ray i k' ≤ num * (opOf zh wh).ray i k')
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
  have hsep : G.sep = (mx (mx (G.xb - 1) (G.xj - 3)) (mx (G.xj - 3) 3), mx (G.xj - 3) 3,
      mx (Low6969GateFreeCard.mn (G.xt - 1) ((G.xj - 3) / 3)) 1) := by
    simp only [Gt.sep, hlift, hB, hJ, hT, Bool.cond_true]
  have hbs : InBox (shape (K1_13_6.separant f)) qs := by
    refine ⟨?_, ?_, ?_⟩
    · have := sb.1
      simp only [hqs, hsep, Low6969GateFreeCard.mx_eq]
      exact this.trans ((Nat.sub_le_sub_right hhi.1 1).trans ((le_max_left _ _).trans (le_max_left _ _)))
    · have := sb.2.1
      simp only [hqs, hsep, Low6969GateFreeCard.mx_eq]
      exact this.trans ((Nat.sub_le_sub_right hhi.2.1 3).trans (le_max_left _ _))
    · have := sb.2.2
      simp only [hqs, hsep, Low6969GateFreeCard.mn_eq, Low6969GateFreeCard.mx_eq]
      refine this.trans (le_trans ?_ (le_max_left _ _))
      refine le_min (Nat.sub_le_sub_right hhi.2.2 1) ?_
      refine (Nat.le_div_iff_mul_le (by norm_num)).mpr ?_
      show ((shape f).t - 1) * 3 ≤ G.xj - 3
      omega
  have hcs : K1_13_6_2_3.ChamberBox qs := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [hqs, hsep, Low6969GateFreeCard.mx_eq]
      exact le_max_right _ _
    · simp only [hqs, hsep, Low6969GateFreeCard.mn_eq, Low6969GateFreeCard.mx_eq]
      have := Nat.min_le_right (G.xt - 1) ((G.xj - 3) / 3)
      rcases le_total (min (G.xt - 1) ((G.xj - 3) / 3)) 1 with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; omega
    · simp only [hqs, hsep, Low6969GateFreeCard.mx_eq]
      exact lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hxl : G.lb ≤ coord (shape f) 0 ∧ G.lj ≤ coord (shape f) 1 ∧ G.lt ≤ coord (shape f) 2 := hlo
  have hsum := hsum_of lv n hn hL hs
  refine Low6969GateFinalOrd.two_cut_price_ordinary hm hf hon hl hproper qs hbs hcs hnd Ax (Bof lv) (Wof lv)
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

end Low6969GateCell

end Merged_Low6969GateGateO

-- merged module Low6969GateFin
section Merged_Low6969GateFin

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
set_option Elab.async false

namespace Low6969GateFin
open Low6969GateCell
open K1_13 (Shape shape)
open Low6969GateBilinear (tpOf opOf)

def DEN : ℕ := 10000000
def kT : ℕ := Low6969Prices.taylorLength - 4
def rayT (p : Shape) : Fin 3 → Fin 3 → ℤ :=
  (tpOf p kT (Low6969Prices.bentLift kT p).2 (Low6969Prices.bentLift (kT + 1) p).2).ray
def rayO (p : Shape) : Fin 3 → Fin 3 → ℤ :=
  (opOf (K1_13.chart (Low6969Prices.taylorLength + 1) p.chamber)
    (K1_13.chart (Low6969Prices.taylorLength + 2) p.chamber)).ray

def savedT (p : Shape) : Fin 3 → Fin 3 → ℤ :=
  (tpOf p 133446 (Low6969Prices.bentLift 133446 p).2 (Low6969Prices.bentLift 133447 p).2).ray
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
  | 1 => Low6969WitnessDatETr5.G
  | 2 => Low6969WitnessDatETr3x.G
  | 3 => Low6969WitnessDatS48x.G
  | 4 => Low6969WitnessDatETm.G
  | 5 => Low6969WitnessDatO1j54.G
  | 6 => Low6969WitnessDatO1j55.G
  | 7 => Low6969WitnessDatO2b.G
  | 8 => Low6969WitnessDatS1.G
  | 9 => Low6969WitnessDatO2a.G
  | _ => Low6969WitnessDatETr5.G
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
  | 39, 13 => [(142, 9)]
  | 40, 13 => [(141, 8), (142, 9)]
  | 41, 13 => [(125, 9), (141, 8), (142, 9)]
  | 42, 14 => [(125, 9), (141, 8), (142, 9)]
  | 43, 9 => [(142, 4)]
  | 43, 10 => [(142, 4)]
  | 43, 11 => [(142, 4)]
  | 43, 12 => [(142, 4)]
  | 43, 13 => [(142, 4)]
  | 43, 14 => [(116, 7), (125, 9), (141, 8), (142, 9)]
  | 44, 7 => [(142, 4)]
  | 44, 8 => [(142, 4)]
  | 44, 9 => [(142, 4)]
  | 44, 10 => [(142, 4)]
  | 44, 11 => [(142, 4)]
  | 44, 12 => [(142, 4)]
  | 44, 13 => [(142, 4)]
  | 44, 14 => [(116, 7), (125, 9), (141, 8), (142, 9)]
  | 45, 5 => [(142, 4)]
  | 45, 6 => [(142, 4)]
  | 45, 7 => [(142, 4)]
  | 45, 8 => [(142, 4)]
  | 45, 9 => [(142, 4)]
  | 45, 10 => [(142, 4)]
  | 45, 11 => [(142, 4)]
  | 45, 12 => [(142, 4)]
  | 45, 13 => [(142, 4)]
  | 45, 14 => [(137, 4), (142, 3)]
  | 45, 15 => [(142, 9)]
  | 46, 2 => [(142, 4)]
  | 46, 4 => [(142, 4)]
  | 46, 5 => [(142, 4)]
  | 46, 6 => [(142, 4)]
  | 46, 7 => [(142, 4)]
  | 46, 8 => [(142, 4)]
  | 46, 9 => [(142, 4)]
  | 46, 10 => [(142, 4)]
  | 46, 11 => [(142, 4)]
  | 46, 12 => [(142, 4)]
  | 46, 13 => [(142, 4)]
  | 46, 14 => [(137, 4), (142, 3)]
  | 46, 15 => [(142, 9)]
  | 47, 2 => [(142, 4)]
  | 47, 3 => [(142, 4)]
  | 47, 4 => [(142, 4)]
  | 47, 5 => [(142, 4)]
  | 47, 6 => [(142, 4)]
  | 47, 7 => [(142, 4)]
  | 47, 8 => [(142, 4)]
  | 47, 9 => [(142, 4)]
  | 47, 10 => [(142, 4)]
  | 47, 11 => [(142, 4)]
  | 47, 12 => [(142, 4)]
  | 47, 13 => [(142, 4)]
  | 47, 14 => [(137, 4), (142, 3)]
  | 47, 15 => [(142, 9)]
  | 48, 2 => [(142, 4)]
  | 48, 3 => [(142, 4)]
  | 48, 4 => [(142, 4)]
  | 48, 5 => [(142, 4)]
  | 48, 6 => [(142, 4)]
  | 48, 7 => [(142, 4)]
  | 48, 8 => [(142, 4)]
  | 48, 9 => [(142, 4)]
  | 48, 10 => [(142, 4)]
  | 48, 11 => [(142, 4)]
  | 48, 12 => [(142, 4)]
  | 48, 13 => [(142, 4)]
  | 48, 14 => [(137, 4), (142, 3)]
  | 48, 15 => [(142, 4)]
  | 49, 2 => [(142, 4)]
  | 49, 3 => [(142, 4)]
  | 49, 4 => [(142, 4)]
  | 49, 5 => [(142, 4)]
  | 49, 6 => [(142, 4)]
  | 49, 7 => [(142, 4)]
  | 49, 8 => [(142, 4)]
  | 49, 9 => [(142, 4)]
  | 49, 10 => [(142, 4)]
  | 49, 11 => [(142, 4)]
  | 49, 12 => [(142, 4)]
  | 49, 13 => [(142, 4)]
  | 49, 14 => [(142, 4)]
  | 49, 15 => [(142, 4)]
  | 50, 2 => [(142, 4)]
  | 50, 3 => [(142, 4)]
  | 50, 4 => [(142, 4)]
  | 50, 5 => [(142, 4)]
  | 50, 6 => [(142, 4)]
  | 50, 7 => [(142, 4)]
  | 50, 8 => [(142, 4)]
  | 50, 9 => [(142, 4)]
  | 50, 10 => [(142, 4)]
  | 50, 11 => [(142, 4)]
  | 50, 12 => [(142, 4)]
  | 50, 13 => [(142, 4)]
  | 50, 14 => [(142, 4)]
  | 50, 15 => [(142, 4)]
  | 51, 2 => [(142, 1)]
  | 51, 3 => [(142, 1)]
  | 51, 4 => [(142, 1)]
  | 51, 5 => [(142, 1)]
  | 51, 6 => [(142, 1)]
  | 51, 7 => [(142, 1)]
  | 51, 8 => [(97, 4), (142, 1)]
  | 51, 9 => [(97, 4), (142, 1)]
  | 51, 10 => [(97, 4), (119, 1), (142, 4)]
  | 51, 11 => [(142, 4)]
  | 51, 12 => [(142, 4)]
  | 51, 13 => [(20, 5), (142, 4)]
  | 51, 14 => [(19, 5), (142, 4)]
  | 51, 15 => [(142, 4)]
  | 52, 2 => [(142, 1)]
  | 52, 3 => [(142, 1)]
  | 52, 4 => [(142, 1)]
  | 52, 5 => [(142, 1)]
  | 52, 6 => [(142, 1)]
  | 52, 7 => [(142, 1)]
  | 52, 8 => [(97, 4), (142, 1)]
  | 52, 9 => [(97, 4), (142, 1)]
  | 52, 10 => [(97, 4), (124, 1), (142, 4)]
  | 52, 11 => [(21, 5), (142, 4)]
  | 52, 12 => [(23, 5), (142, 4)]
  | 52, 13 => [(23, 5), (142, 4)]
  | 52, 14 => [(23, 5), (142, 4)]
  | 52, 15 => [(142, 4)]
  | 53, 2 => [(142, 1)]
  | 53, 3 => [(142, 1)]
  | 53, 4 => [(142, 1)]
  | 53, 5 => [(105, 2), (142, 1)]
  | 53, 6 => [(105, 2), (142, 1)]
  | 53, 7 => [(105, 2), (142, 1)]
  | 53, 8 => [(105, 2), (142, 1)]
  | 53, 9 => [(105, 2), (142, 1)]
  | 53, 10 => [(110, 2), (142, 1)]
  | 53, 11 => [(23, 5), (110, 2), (142, 4)]
  | 53, 12 => [(24, 5), (110, 2), (142, 4)]
  | 53, 13 => [(25, 5), (110, 2), (142, 4)]
  | 53, 14 => [(25, 5), (110, 2), (142, 4)]
  | 53, 15 => [(142, 4)]
  | 54, 2 => [(107, 2), (142, 1)]
  | 54, 3 => [(142, 1)]
  | 54, 4 => [(107, 2), (142, 1)]
  | 54, 5 => [(107, 2), (142, 1)]
  | 54, 6 => [(107, 2), (142, 1)]
  | 54, 7 => [(107, 2), (142, 1)]
  | 54, 8 => [(107, 2), (142, 1)]
  | 54, 9 => [(107, 2), (142, 1)]
  | 54, 10 => [(25, 5), (110, 2), (142, 1)]
  | 54, 11 => [(26, 5), (110, 2), (142, 4)]
  | 54, 12 => [(28, 5), (110, 2), (142, 4)]
  | 54, 13 => [(29, 5), (110, 2), (142, 4)]
  | 54, 14 => [(29, 5), (110, 2), (142, 4)]
  | 54, 15 => [(142, 4)]
  | 55, 2 => [(110, 2), (142, 1)]
  | 55, 3 => [(110, 2), (142, 1)]
  | 55, 4 => [(110, 2), (142, 1)]
  | 55, 5 => [(110, 2), (142, 1)]
  | 55, 6 => [(110, 2), (142, 1)]
  | 55, 7 => [(110, 2), (142, 1)]
  | 55, 8 => [(110, 2), (142, 1)]
  | 55, 9 => [(28, 6), (110, 2), (142, 1)]
  | 55, 10 => [(30, 6), (110, 2), (142, 1)]
  | 55, 11 => [(32, 6), (110, 2), (142, 4)]
  | 55, 12 => [(35, 6), (110, 2), (142, 4)]
  | 55, 13 => [(37, 6), (110, 2), (142, 4)]
  | 55, 14 => [(38, 6), (110, 2), (142, 4)]
  | 55, 15 => [(142, 4)]
  | 56, 2 => [(142, 1)]
  | 56, 3 => [(142, 1)]
  | 56, 4 => [(142, 1)]
  | 56, 5 => [(142, 1)]
  | 56, 6 => [(142, 1)]
  | 56, 7 => [(142, 1)]
  | 56, 8 => [(142, 1)]
  | 56, 9 => [(142, 1)]
  | 56, 10 => [(142, 1)]
  | 56, 11 => [(142, 4)]
  | 56, 12 => [(142, 4)]
  | 56, 13 => [(142, 4)]
  | 56, 14 => [(142, 4)]
  | 56, 15 => [(142, 4)]
  | 57, 2 => [(142, 1)]
  | 57, 3 => [(142, 1)]
  | 57, 4 => [(142, 1)]
  | 57, 5 => [(142, 1)]
  | 57, 6 => [(142, 1)]
  | 57, 7 => [(142, 1)]
  | 57, 8 => [(142, 1)]
  | 57, 9 => [(142, 1)]
  | 57, 10 => [(97, 4), (142, 1)]
  | 57, 11 => [(142, 4)]
  | 57, 12 => [(142, 4)]
  | 57, 13 => [(142, 4)]
  | 57, 14 => [(142, 4)]
  | 57, 15 => [(142, 4)]
  | 58, 2 => [(142, 1)]
  | 58, 3 => [(142, 1)]
  | 58, 4 => [(142, 1)]
  | 58, 5 => [(142, 1)]
  | 58, 6 => [(142, 1)]
  | 58, 7 => [(142, 1)]
  | 58, 8 => [(97, 4), (142, 1)]
  | 58, 9 => [(97, 4), (142, 1)]
  | 58, 10 => [(97, 4), (142, 1)]
  | 58, 11 => [(142, 4)]
  | 58, 12 => [(142, 4)]
  | 58, 13 => [(142, 4)]
  | 58, 14 => [(142, 4)]
  | 58, 15 => [(142, 4)]
  | _, _ => []

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

theorem gl_nil (id t : ℕ) (h : 16 ≤ t) : Low6969Gate.gateList id t = [] := by
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
  have := Low6969GateCertCF.ceil_mul N D hD
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
    (hm : Low6969Prices.Messages w Γ s) (hf : Low6969Prices.SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (hl : 0 < l)
    (hproper : Low6969Prices.ProperCut f Γ s l) (hchar : f.degreeOf 3 < K1.p)
    (hx : shapeOK (shape f) = true) :
    Γ.card ≤ Gfun (shape f) + Low6969SharedPrice.additiveBase (shape f) l +
      Low6969SharedPrice.nonsharedFee (shape f) l := by
  obtain ⟨hc, hth⟩ := shapeOK_cases hx
  obtain ⟨c1, c2, hok⟩ := cls_cases (rfl : cls (shape f) = cls (shape f)) hc
  obtain ⟨_, hin, htf⟩ := okK_props hok
  generalize hcc : cls (shape f) = c at *
  interval_cases c
  · -- gate 1 = ETr5
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have htf' : tfB (shape f) = true := by simpa [isT] using htf
    have key := price_T hm hf hon hl hproper hchar (tfB_true htf') Low6969WitnessDatETr5.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl (by decide)
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩ kT
          (Low6969Prices.bentLift 133446 (hiS Low6969WitnessDatETr5.G)).2 (Low6969Prices.bentLift 133447 (hiS Low6969WitnessDatETr5.G)).2
          (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT + 1) (shape f)).2 rfl rfl rfl rfl rfl
          (by decide +kernel) (numT Low6969WitnessDatETr5.G (shape f)) DEN (Ax (numT Low6969WitnessDatETr5.G (shape f)) Low6969WitnessDatETr5.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Low6969WitnessDatETr5.ws Low6969WitnessDatETr5.tabOK Low6969WitnessDatETr5.lv Low6969WitnessDatETr5.n rfl
          (by decide +kernel) (by decide +kernel) Low6969WitnessDatETr5.allOKn Low6969WitnessDatETr5.rho0 Low6969WitnessDatETr5.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Low6969WitnessDatETr5.sumLt
    simp only [Gfun, hcc, show numK 1 (shape f) = numT Low6969WitnessDatETr5.G (shape f) from rfl]
    have e1 : (Gk 1).A = Low6969WitnessDatETr5.G.A := rfl
    simpa [e1] using key
  · -- gate 2 = ETr3x
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have htf' : tfB (shape f) = true := by simpa [isT] using htf
    have key := price_T hm hf hon hl hproper hchar (tfB_true htf') Low6969WitnessDatETr3x.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl (by decide)
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩ kT
          (Low6969Prices.bentLift 133446 (hiS Low6969WitnessDatETr3x.G)).2 (Low6969Prices.bentLift 133447 (hiS Low6969WitnessDatETr3x.G)).2
          (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT + 1) (shape f)).2 rfl rfl rfl rfl rfl
          (by decide +kernel) (numT Low6969WitnessDatETr3x.G (shape f)) DEN (Ax (numT Low6969WitnessDatETr3x.G (shape f)) Low6969WitnessDatETr3x.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Low6969WitnessDatETr3x.ws Low6969WitnessDatETr3x.tabOK Low6969WitnessDatETr3x.lv Low6969WitnessDatETr3x.n rfl
          (by decide +kernel) (by decide +kernel) Low6969WitnessDatETr3x.allOKn Low6969WitnessDatETr3x.rho0 Low6969WitnessDatETr3x.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Low6969WitnessDatETr3x.sumLt
    simp only [Gfun, hcc, show numK 2 (shape f) = numT Low6969WitnessDatETr3x.G (shape f) from rfl]
    have e1 : (Gk 2).A = Low6969WitnessDatETr3x.G.A := rfl
    simpa [e1] using key
  · -- gate 3 = S48x
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have htf' : tfB (shape f) = true := by simpa [isT] using htf
    have key := price_T hm hf hon hl hproper hchar (tfB_true htf') Low6969WitnessDatS48x.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl (by decide)
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩ kT
          (Low6969Prices.bentLift 133446 (hiS Low6969WitnessDatS48x.G)).2 (Low6969Prices.bentLift 133447 (hiS Low6969WitnessDatS48x.G)).2
          (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT + 1) (shape f)).2 rfl rfl rfl rfl rfl
          (by decide +kernel) (numT Low6969WitnessDatS48x.G (shape f)) DEN (Ax (numT Low6969WitnessDatS48x.G (shape f)) Low6969WitnessDatS48x.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Low6969WitnessDatS48x.ws Low6969WitnessDatS48x.tabOK Low6969WitnessDatS48x.lv Low6969WitnessDatS48x.n rfl
          (by decide +kernel) (by decide +kernel) Low6969WitnessDatS48x.allOKn Low6969WitnessDatS48x.rho0 Low6969WitnessDatS48x.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Low6969WitnessDatS48x.sumLt
    simp only [Gfun, hcc, show numK 3 (shape f) = numT Low6969WitnessDatS48x.G (shape f) from rfl]
    have e1 : (Gk 3).A = Low6969WitnessDatS48x.G.A := rfl
    simpa [e1] using key
  · -- gate 4 = ETm
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have htf' : tfB (shape f) = true := by simpa [isT] using htf
    have key := price_T hm hf hon hl hproper hchar (tfB_true htf') Low6969WitnessDatETm.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl (by decide)
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩ kT
          (Low6969Prices.bentLift 133446 (hiS Low6969WitnessDatETm.G)).2 (Low6969Prices.bentLift 133447 (hiS Low6969WitnessDatETm.G)).2
          (Low6969Prices.bentLift kT (shape f)).2 (Low6969Prices.bentLift (kT + 1) (shape f)).2 rfl rfl rfl rfl rfl
          (by decide +kernel) (numT Low6969WitnessDatETm.G (shape f)) DEN (Ax (numT Low6969WitnessDatETm.G (shape f)) Low6969WitnessDatETm.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Low6969WitnessDatETm.ws Low6969WitnessDatETm.tabOK Low6969WitnessDatETm.lv Low6969WitnessDatETm.n rfl
          (by decide +kernel) (by decide +kernel) Low6969WitnessDatETm.allOKn Low6969WitnessDatETm.rho0 Low6969WitnessDatETm.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Low6969WitnessDatETm.sumLt
    simp only [Gfun, hcc, show numK 4 (shape f) = numT Low6969WitnessDatETm.G (shape f) from rfl]
    have e1 : (Gk 4).A = Low6969WitnessDatETm.G.A := rfl
    simpa [e1] using key
  · -- gate 5 = O1j54
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
    have key := price_O hm hf hon hl hproper hchar hcx Low6969WitnessDatO1j54.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩
          (K1_13.chart 133451 (hiS Low6969WitnessDatO1j54.G).chamber)
          (K1_13.chart 133452 (hiS Low6969WitnessDatO1j54.G).chamber)
          (by decide +kernel) (numO Low6969WitnessDatO1j54.G (shape f)) DEN (Ax (numO Low6969WitnessDatO1j54.G (shape f)) Low6969WitnessDatO1j54.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Low6969WitnessDatO1j54.ws Low6969WitnessDatO1j54.tabOK Low6969WitnessDatO1j54.lv Low6969WitnessDatO1j54.n rfl
          (by decide +kernel) (by decide +kernel) Low6969WitnessDatO1j54.allOKn Low6969WitnessDatO1j54.rho0 Low6969WitnessDatO1j54.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Low6969WitnessDatO1j54.sumLt
    simp only [Gfun, hcc, show numK 5 (shape f) = numO Low6969WitnessDatO1j54.G (shape f) from rfl]
    have e1 : (Gk 5).A = Low6969WitnessDatO1j54.G.A := rfl
    simpa [e1] using key
  · -- gate 6 = O1j55
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
    have key := price_O hm hf hon hl hproper hchar hcx Low6969WitnessDatO1j55.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩
          (K1_13.chart 133451 (hiS Low6969WitnessDatO1j55.G).chamber)
          (K1_13.chart 133452 (hiS Low6969WitnessDatO1j55.G).chamber)
          (by decide +kernel) (numO Low6969WitnessDatO1j55.G (shape f)) DEN (Ax (numO Low6969WitnessDatO1j55.G (shape f)) Low6969WitnessDatO1j55.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Low6969WitnessDatO1j55.ws Low6969WitnessDatO1j55.tabOK Low6969WitnessDatO1j55.lv Low6969WitnessDatO1j55.n rfl
          (by decide +kernel) (by decide +kernel) Low6969WitnessDatO1j55.allOKn Low6969WitnessDatO1j55.rho0 Low6969WitnessDatO1j55.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Low6969WitnessDatO1j55.sumLt
    simp only [Gfun, hcc, show numK 6 (shape f) = numO Low6969WitnessDatO1j55.G (shape f) from rfl]
    have e1 : (Gk 6).A = Low6969WitnessDatO1j55.G.A := rfl
    simpa [e1] using key
  · -- gate 7 = O2b
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
    have key := price_O hm hf hon hl hproper hchar hcx Low6969WitnessDatO2b.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩
          (K1_13.chart 133451 (hiS Low6969WitnessDatO2b.G).chamber)
          (K1_13.chart 133452 (hiS Low6969WitnessDatO2b.G).chamber)
          (by decide +kernel) (numO Low6969WitnessDatO2b.G (shape f)) DEN (Ax (numO Low6969WitnessDatO2b.G (shape f)) Low6969WitnessDatO2b.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Low6969WitnessDatO2b.ws Low6969WitnessDatO2b.tabOK Low6969WitnessDatO2b.lv Low6969WitnessDatO2b.n rfl
          (by decide +kernel) (by decide +kernel) Low6969WitnessDatO2b.allOKn Low6969WitnessDatO2b.rho0 Low6969WitnessDatO2b.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Low6969WitnessDatO2b.sumLt
    simp only [Gfun, hcc, show numK 7 (shape f) = numO Low6969WitnessDatO2b.G (shape f) from rfl]
    have e1 : (Gk 7).A = Low6969WitnessDatO2b.G.A := rfl
    simpa [e1] using key
  · -- gate 8 = S1
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
    have key := price_O hm hf hon hl hproper hchar hcx Low6969WitnessDatS1.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩
          (K1_13.chart 133451 (hiS Low6969WitnessDatS1.G).chamber)
          (K1_13.chart 133452 (hiS Low6969WitnessDatS1.G).chamber)
          (by decide +kernel) (numO Low6969WitnessDatS1.G (shape f)) DEN (Ax (numO Low6969WitnessDatS1.G (shape f)) Low6969WitnessDatS1.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Low6969WitnessDatS1.ws Low6969WitnessDatS1.tabOK Low6969WitnessDatS1.lv Low6969WitnessDatS1.n rfl
          (by decide +kernel) (by decide +kernel) Low6969WitnessDatS1.allOKn Low6969WitnessDatS1.rho0 Low6969WitnessDatS1.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Low6969WitnessDatS1.sumLt
    simp only [Gfun, hcc, show numK 8 (shape f) = numO Low6969WitnessDatS1.G (shape f) from rfl]
    have e1 : (Gk 8).A = Low6969WitnessDatS1.G.A := rfl
    simpa [e1] using key
  · -- gate 9 = O2a
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := inR_props hin
    have hθ := thOK_spec (by simpa [thK, isT] using hth)
    have hcx : 3 * (shape f).t ≤ (shape f).j := (K1_13_7_1.shape_chamber f).2
    have key := price_O hm hf hon hl hproper hchar hcx Low6969WitnessDatO2a.G (by simp only [Gt.Ok]; decide +kernel) rfl rfl
          (by decide) (by decide) (by decide) ⟨a1, a2, a3⟩ ⟨a4, a5, a6⟩
          (K1_13.chart 133451 (hiS Low6969WitnessDatO2a.G).chamber)
          (K1_13.chart 133452 (hiS Low6969WitnessDatO2a.G).chamber)
          (by decide +kernel) (numO Low6969WitnessDatO2a.G (shape f)) DEN (Ax (numO Low6969WitnessDatO2a.G (shape f)) Low6969WitnessDatO2a.G.A)
          (by decide) hθ (ceil_le _ _ (by decide)) 1 Low6969WitnessDatO2a.ws Low6969WitnessDatO2a.tabOK Low6969WitnessDatO2a.lv Low6969WitnessDatO2a.n rfl
          (by decide +kernel) (by decide +kernel) Low6969WitnessDatO2a.allOKn Low6969WitnessDatO2a.rho0 Low6969WitnessDatO2a.amax (by decide)
          (by decide) (amax_le _ _ _ _ (by decide) (by decide) (by decide) (by decide))
          (by decide +kernel) (by decide +kernel) (by decide +kernel) Low6969WitnessDatO2a.sumLt
    simp only [Gfun, hcc, show numK 9 (shape f) = numO Low6969WitnessDatO2a.G (shape f) from rfl]
    have e1 : (Gk 9).A = Low6969WitnessDatO2a.G.A := rfl
    simpa [e1] using key

def one (id t : ℕ) : Bool := (Low6969Gate.gateList id t).all fun p => !(valid ⟨p.1, p.2, t⟩) || shapeOK ⟨p.1, p.2, t⟩

end Low6969GateFin

end Merged_Low6969GateFin
end Z6969Source2490

-- Source: ProximityPrize.SubmissionLower.Low6969GateChecks
section Z6969Source2491
set_option autoImplicit true
set_option Elab.async false

-- merged module G6966CheckOrders
section Merged_G6966CheckOrders
namespace Low6969GateFin
open K1_13 (Shape)
def gtOne (id t : ℕ) : Bool := (Low6969Gate.gateList id t).all fun p =>
  let x : Shape := ⟨p.1, p.2, t⟩
  let k : Low6969Allocation.Band := ⟨id % 40, Nat.mod_lt _ (by decide)⟩
  let l := Low6969Allocation.order (Low6969Allocation.bandOrders k) x
  Nat.blt 0 l && Nat.ble (Low6969Gate.gatePrice Gfun x l)
    (Low6969Allocation.allowance k ((Low6969Allocation.start k).t + t) p.1 p.2 t)


end Low6969GateFin

end Merged_G6966CheckOrders

-- merged module Low6969WitnessChunk
section Merged_Low6969WitnessChunk
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Low6969GateFin
open K1_13 (Shape shape)
open Low6969SharedPrice (additiveBase nonsharedFee)

/-- the `i`-th chunk of 32 shapes of a gate list, checked as a gate row -/
def chunkOf (l : List (ℕ × ℕ)) (i : ℕ) : List (ℕ × ℕ) := (l.drop (32 * i)).take 32

theorem all_of_chunks (f : ℕ × ℕ → Bool) (l : List (ℕ × ℕ)) (N : ℕ) (hN : l.length ≤ 32 * N)
    (h : ∀ i, i < N → (chunkOf l i).all f = true) : l.all f = true := by
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨k, hk, hkp⟩ := List.getElem_of_mem hp
  have hi : k / 32 < N := by omega
  have := List.all_eq_true.mp (h (k / 32) hi) p ?_
  · exact this
  · unfold chunkOf
    rw [← hkp]
    have hmem : l[k] ∈ (l.drop (32 * (k / 32))).take 32 := by
      rw [List.mem_iff_getElem]
      refine ⟨k - 32 * (k / 32), ?_, ?_⟩
      · simp [List.length_take, List.length_drop]; omega
      · simp [List.getElem_take, List.getElem_drop]; congr 1; omega
    exact hmem

def oneF (_id t : ℕ) (p : ℕ × ℕ) : Bool := !(valid ⟨p.1, p.2, t⟩) || shapeOK ⟨p.1, p.2, t⟩

def gtF (id t : ℕ) (p : ℕ × ℕ) : Bool :=
  let x : Shape := ⟨p.1, p.2, t⟩
  let k : Low6969Allocation.Band := ⟨id % 40, Nat.mod_lt _ (by decide)⟩
  let l := Low6969Allocation.order (Low6969Allocation.bandOrders k) x
  Nat.blt 0 l && Nat.ble (Low6969Gate.gatePrice Gfun x l)
    (Low6969Allocation.allowance k ((Low6969Allocation.start k).t + t) p.1 p.2 t)

theorem one_of_chunks (id t N : ℕ) (hN : (Low6969Gate.gateList id t).length ≤ 32 * N)
    (h : ∀ i, i < N → (chunkOf (Low6969Gate.gateList id t) i).all (oneF id t) = true) : one id t = true :=
  all_of_chunks (oneF id t) _ N hN h

theorem gtOne_of_chunks (id t N : ℕ) (hN : (Low6969Gate.gateList id t).length ≤ 32 * N)
    (h : ∀ i, i < N → (chunkOf (Low6969Gate.gateList id t) i).all (gtF id t) = true) : gtOne id t = true :=
  all_of_chunks (gtF id t) _ N hN h
def hiTab : ℕ → List (List ℤ)
  | 1 => [[0, 39251835991215360, 155160962561491200], [39251835991215360, 149980979443347840, 795447676052641920], [155160962561491200, 795447676052641920, 2461153937333616000]]
  | 2 => [[0, 43765106196728640, 138697765881171840], [43765106196728640, 161606057188517280, 598684265902436160], [138697765881171840, 598684265902436160, 1810857692289280320]]
  | 3 => [[0, 34191490393196160, 103873744650748800], [34191490393196160, 200584350102899520, 666511629364518720], [103873744650748800, 666511629364518720, 2002133435035876800]]
  | 4 => [[0, 49252838423501760, 155160962561491200], [49252838423501760, 221141973957193440, 815449680917214720], [155160962561491200, 815449680917214720, 2461153937333616000]]
  | 5 => [[0, 961702793864192, 3023023622878464], [961702793864192, 1904171333531440, 6634038567368208], [3023023622878464, 6634038567368208, 20177946184676400]]
  | 6 => [[0, 992477277733344, 3141562368284064], [992477277733344, 1950333059335168, 6876815022280704], [3141562368284064, 6876815022280704, 20958706137010176]]
  | 7 => [[0, 653957955172672, 1963013660900544], [653957955172672, 3658316914073104, 11205759307181232], [1963013660900544, 11205759307181232, 33619557512308752]]
  | 8 => [[0, 653957955172672, 1963013660900544], [653957955172672, 4427679010801904, 13570835366494032], [1963013660900544, 13570835366494032, 40714785690247152]]
  | 9 => [[0, 751980383692768, 2257080946460832], [751980383692768, 4796972736093216, 14678716542367968], [2257080946460832, 14678716542367968, 44038429217868960]]
  | _ => []

def rayK (c : ℕ) (x : Shape) : Fin 3 → Fin 3 → ℤ := if isT c then rayT x else rayO x

/-- the gate's top ray as literals (checked equal to `savedK c (hiS (Gk c))` for 1 <= c <= 9) -/
def savedK (c : ℕ) (x : Shape) := if isT c then savedT x else savedO x

def hiL (c : ℕ) : Fin 3 → Fin 3 → ℤ := fun i k =>
  if c = 0 ∨ 10 ≤ c then savedK c (hiS (Gk c)) i k else ((hiTab c).getD i.1 []).getD k.1 0

theorem hiTab_ok : ∀ c, c < 10 → 1 ≤ c → ∀ i k : Fin 3,
    ((hiTab c).getD i.1 []).getD k.1 0 = savedK c (hiS (Gk c)) i k := by decide +kernel

theorem hiL_eq (c : ℕ) : hiL c = savedK c (hiS (Gk c)) := by
  funext i k
  unfold hiL
  by_cases h : c = 0 ∨ 10 ≤ c
  · simp only [h, ite_true]
  · rw [if_neg h]
    exact hiTab_ok c (by omega) (by omega) i k

theorem numK_eq (c : ℕ) (x : Shape) : numK c x = thNum (rayK c x) (hiL c) := by
  rw [hiL_eq]
  unfold numK rayK savedK
  by_cases h : isT c = true
  · simp only [h, ite_true]; rfl
  · simp only [h, ite_false]; rfl

/-- shape check from the shared numerator -/
def sN (c : ℕ) (x : Shape) (n : ℕ) : Bool :=
  if c = 0 then false else decide (∀ i k : Fin 3, (DEN : ℤ) * rayK c x i k ≤ (n : ℤ) * hiL c i k)

theorem thK_eq (c : ℕ) (x : Shape) : thK c x =
    (if isT c = true then thOK (rayT x) (savedT (hiS (Gk c))) else thOK (rayO x) (savedO (hiS (Gk c)))) := rfl
theorem thOK_eq (rx rh : Fin 3 → Fin 3 → ℤ) : thOK rx rh =
    decide (∀ i k : Fin 3, (DEN : ℤ) * rx i k ≤ (thNum rx rh : ℤ) * rh i k) := rfl
theorem shapeOK_c (c : ℕ) (x : Shape) :
    (if c = 0 then false else thK c x) = sN c x (thNum (rayK c x) (hiL c)) := by
  unfold sN
  by_cases h : c = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    rw [thK_eq, hiL_eq]
    by_cases h2 : isT c = true
    · rw [if_pos h2, thOK_eq]
      simp only [rayK, savedK, h2, ite_true]
    · rw [if_neg h2, thOK_eq]
      simp only [rayK, savedK, h2, Bool.false_eq_true, ite_false]

theorem shapeOK_eq (x : Shape) : shapeOK x = sN (cls x) x (thNum (rayK (cls x) x) (hiL (cls x))) :=
  shapeOK_c (cls x) x

def gtG (id t : ℕ) (p : ℕ × ℕ) (G : ℕ) : Bool :=
  let x : Shape := ⟨p.1, p.2, t⟩
  let k : Low6969Allocation.Band := ⟨id % 40, Nat.mod_lt _ (by decide)⟩
  let l := Low6969Allocation.order (Low6969Allocation.bandOrders k) x
  Nat.blt 0 l && Nat.ble (additiveBase x l + nonsharedFee x l + G)
    (Low6969Allocation.allowance k ((Low6969Allocation.start k).t + t) p.1 p.2 t)

/-- fused shape + price check: the ray numerator is computed once -/
def fF (id t : ℕ) (p : ℕ × ℕ) : Bool :=
  let x : Shape := ⟨p.1, p.2, t⟩
  let c := cls x
  let n := thNum (rayK c x) (hiL c)
  (!(valid x) || sN c x n) && gtG id t p (if c = 0 then 0 else Ax n (Gk c).A)

theorem gtF_eq (id t : ℕ) (p : ℕ × ℕ) :
    gtF id t p = gtG id t p (Gfun ⟨p.1, p.2, t⟩) := rfl

theorem Gfun_eq (x : Shape) : Gfun x = (if cls x = 0 then 0 else Ax (thNum (rayK (cls x) x) (hiL (cls x))) (Gk (cls x)).A) := by
  unfold Gfun
  generalize cls x = c
  by_cases h : c = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, numK_eq]

theorem fF_eq (id t : ℕ) (p : ℕ × ℕ) : fF id t p = (oneF id t p && gtF id t p) := by
  rw [gtF_eq, Gfun_eq]
  unfold oneF
  rw [shapeOK_eq]
  rfl


section FastGateRays
set_option linter.unusedVariables false
open Low6969GateBilinear (TP OP Nt No tpOf opOf)
open K1_13_8_2 (Threshold orderFor)
def tC12 (B1 J2 t k h1 h2 : ℤ) : ℤ := (-960*(2*J2*h1*h2 - 2*J2*h1*k*t + J2*h1*k - 2*J2*h1*t - J2*h1 - 2*J2*h2*k*t + J2*h2*k - 2*J2*h2 - 2*J2*k^2*t - 2*J2*k*t - 4*J2*k - 2*J2 - 2*h1*h2*t + 3*h1*k*t^2 - 2*h1*k*t + 3*h1*t^2 + 3*h2*k*t^2 - 2*h2*k*t + 2*h2*t + 3*k^2*t^2 + 3*k*t^2 + 4*k*t + 2*t - 4))
def tC13 (B1 J2 t k h1 h2 : ℤ) : ℤ := (960*(J2^2*h1*k + J2^2*h1 + J2^2*h2*k + J2^2*k^2 + J2^2*k + 2*J2*h1*h2 - 6*J2*h1*k*t + 2*J2*h1*k - 6*J2*h1*t - 6*J2*h2*k*t + 2*J2*h2*k - 2*J2*h2 - 6*J2*k^2*t - 6*J2*k*t - 4*J2*k - 2*J2 - 6*h1*h2*t + 4*h1*h2 + 9*h1*k*t^2 - 6*h1*k*t + 9*h1*t^2 - 4*h1 + 9*h2*k*t^2 - 6*h2*k*t + 6*h2*t - 4*h2 + 9*k^2*t^2 + 9*k*t^2 + 12*k*t + 6*t + 4))
def tC21 (B1 J2 t k h1 h2 : ℤ) : ℤ := (-960*(2*J2*h1*h2 - 2*J2*h1*k*t + J2*h1*k - 2*J2*h1*t - J2*h1 - 2*J2*h2*k*t + J2*h2*k - 2*J2*h2 - 2*J2*k^2*t - 2*J2*k*t - 4*J2*k - 2*J2 - 2*h1*h2*t + 3*h1*k*t^2 - 2*h1*k*t + 3*h1*t^2 + 3*h2*k*t^2 - 2*h2*k*t + 2*h2*t + 3*k^2*t^2 + 3*k*t^2 + 4*k*t + 2*t - 4))
def tC22 (B1 J2 t k h1 h2 : ℤ) : ℤ := (480*(-4*B1*h1*h2 + 4*B1*h1*k*t - 2*B1*h1*k + 4*B1*h1*t + 2*B1*h1 + 4*B1*h2*k*t - 2*B1*h2*k + 4*B1*h2 + 4*B1*k^2*t + 4*B1*k*t + 8*B1*k + 4*B1 + 6*J2*h1*h2 - 6*J2*h1*k*t + 3*J2*h1*k - 6*J2*h1*t - 3*J2*h1 - 6*J2*h2*k*t + 3*J2*h2*k - 6*J2*h2 - 6*J2*k^2*t - 6*J2*k*t - 12*J2*k - 6*J2 - 4*h1*h2*t - 2*h1*h2 + 7*h1*k*t^2 - 4*h1*k*t + 7*h1*t^2 + 2*h1 + 7*h2*k*t^2 - 4*h2*k*t + 4*h2*t + 2*h2 + 7*k^2*t^2 + 7*k*t^2 + 8*k*t + 4*t - 12))
def tC23 (B1 J2 t k h1 h2 : ℤ) : ℤ := (-480*(-4*B1*J2*h1*k - 4*B1*J2*h1 - 4*B1*J2*h2*k - 4*B1*J2*k^2 - 4*B1*J2*k - 4*B1*h1*h2 + 12*B1*h1*k*t - 4*B1*h1*k + 12*B1*h1*t + 12*B1*h2*k*t - 4*B1*h2*k + 4*B1*h2 + 12*B1*k^2*t + 12*B1*k*t + 8*B1*k + 4*B1 + 3*J2^2*h1*k + 3*J2^2*h1 + 3*J2^2*h2*k + 3*J2^2*k^2 + 3*J2^2*k + 4*J2*h1*h2 - 14*J2*h1*k*t + 4*J2*h1*k - 14*J2*h1*t - 14*J2*h2*k*t + 4*J2*h2*k - 4*J2*h2 - 14*J2*k^2*t - 14*J2*k*t - 8*J2*k - 4*J2 - 8*h1*h2*t + 4*h1*h2 + 15*h1*k*t^2 - 8*h1*k*t + 15*h1*t^2 - 4*h1 + 15*h2*k*t^2 - 8*h2*k*t + 8*h2*t - 4*h2 + 15*k^2*t^2 + 15*k*t^2 + 16*k*t + 8*t + 4))
def tC31 (B1 J2 t k h1 h2 : ℤ) : ℤ := (960*(J2^2*h1*k + J2^2*h1 + J2^2*h2*k + J2^2*k^2 + J2^2*k + 2*J2*h1*h2 - 6*J2*h1*k*t + 2*J2*h1*k - 6*J2*h1*t - 6*J2*h2*k*t + 2*J2*h2*k - 2*J2*h2 - 6*J2*k^2*t - 6*J2*k*t - 4*J2*k - 2*J2 - 6*h1*h2*t + 4*h1*h2 + 9*h1*k*t^2 - 6*h1*k*t + 9*h1*t^2 - 4*h1 + 9*h2*k*t^2 - 6*h2*k*t + 6*h2*t - 4*h2 + 9*k^2*t^2 + 9*k*t^2 + 12*k*t + 6*t + 4))
def tC32 (B1 J2 t k h1 h2 : ℤ) : ℤ := (-480*(-4*B1*J2*h1*k - 4*B1*J2*h1 - 4*B1*J2*h2*k - 4*B1*J2*k^2 - 4*B1*J2*k - 4*B1*h1*h2 + 12*B1*h1*k*t - 4*B1*h1*k + 12*B1*h1*t + 12*B1*h2*k*t - 4*B1*h2*k + 4*B1*h2 + 12*B1*k^2*t + 12*B1*k*t + 8*B1*k + 4*B1 + 3*J2^2*h1*k + 3*J2^2*h1 + 3*J2^2*h2*k + 3*J2^2*k^2 + 3*J2^2*k + 4*J2*h1*h2 - 14*J2*h1*k*t + 4*J2*h1*k - 14*J2*h1*t - 14*J2*h2*k*t + 4*J2*h2*k - 4*J2*h2 - 14*J2*k^2*t - 14*J2*k*t - 8*J2*k - 4*J2 - 8*h1*h2*t + 4*h1*h2 + 15*h1*k*t^2 - 8*h1*k*t + 15*h1*t^2 - 4*h1 + 15*h2*k*t^2 - 8*h2*k*t + 8*h2*t - 4*h2 + 15*k^2*t^2 + 15*k*t^2 + 16*k*t + 8*t + 4))
def tC33 (B1 J2 t k h1 h2 : ℤ) : ℤ := (480*(-12*B1*J2*h1*k - 12*B1*J2*h1 - 12*B1*J2*h2*k - 12*B1*J2*k^2 - 12*B1*J2*k - 12*B1*h1*h2 + 36*B1*h1*k*t - 12*B1*h1*k + 36*B1*h1*t + 36*B1*h2*k*t - 12*B1*h2*k + 12*B1*h2 + 36*B1*k^2*t + 36*B1*k*t + 24*B1*k + 12*B1 + 7*J2^2*h1*k + 7*J2^2*h1 + 7*J2^2*h2*k + 7*J2^2*k^2 + 7*J2^2*k + 8*J2*h1*h2 - 30*J2*h1*k*t + 8*J2*h1*k - 30*J2*h1*t - 30*J2*h2*k*t + 8*J2*h2*k - 8*J2*h2 - 30*J2*k^2*t - 30*J2*k*t - 16*J2*k - 8*J2 - 12*h1*h2*t + 4*h1*h2 + 27*h1*k*t^2 - 12*h1*k*t + 27*h1*t^2 - 4*h1 + 27*h2*k*t^2 - 12*h2*k*t + 12*h2*t - 4*h2 + 27*k^2*t^2 + 27*k*t^2 + 24*k*t + 12*t + 4))
def tC12N (B1 J2 t k h1 h2 : ℕ) : ℤ := (((Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 k) (Nat.add (Nat.mul 1920 h1) (Nat.add (Nat.mul 1920 h2) 1920))) k) (Nat.mul 1920 h1)) t) (Nat.add (Nat.mul 3840 k) (Nat.add (Nat.mul 960 h1) (Nat.add (Nat.mul 1920 h2) 1920)))) J2) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 h1) (Nat.mul 1920 h2)) k) (Nat.mul (Nat.mul 1920 h2) h1)) t) 3840)) : ℕ) : ℤ) - (((Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 2880 k) (Nat.add (Nat.mul 2880 h1) (Nat.add (Nat.mul 2880 h2) 2880))) k) (Nat.mul 2880 h1)) t) (Nat.add (Nat.mul 3840 k) (Nat.add (Nat.mul 1920 h2) 1920))) t) (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 960 h1) (Nat.mul 960 h2)) k) (Nat.mul (Nat.mul 1920 h2) h1)) J2)) : ℕ) : ℤ)
theorem tC12N_eq (B1 J2 t k h1 h2 : ℕ) : tC12N B1 J2 t k h1 h2 = tC12 B1 J2 t k h1 h2 := by
  unfold tC12N tC12
  simp only [Nat.add_eq, Nat.mul_eq]
  push_cast
  ring
def tC13N (B1 J2 t k h1 h2 : ℕ) : ℤ := (((Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.mul 960 J2) J2) (Nat.mul (Nat.mul 8640 t) t)) k) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 960 h1) (Nat.add (Nat.mul 960 h2) 960)) J2) (Nat.add (Nat.mul 1920 h1) (Nat.mul 1920 h2))) J2) (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 8640 h1) (Nat.add (Nat.mul 8640 h2) 8640)) t) 11520) t))) k) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 960 J2) (Nat.mul 1920 h2)) J2) (Nat.add (Nat.mul (Nat.mul 8640 t) t) (Nat.mul 3840 h2))) h1) (Nat.add (Nat.mul (Nat.add (Nat.mul 5760 h2) 5760) t) 3840))) : ℕ) : ℤ) - (((Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 5760 k) (Nat.add (Nat.mul 5760 h1) (Nat.add (Nat.mul 5760 h2) 5760))) k) (Nat.mul 5760 h1)) t) (Nat.add (Nat.mul 3840 k) (Nat.add (Nat.mul 1920 h2) 1920))) J2) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 5760 h1) (Nat.mul 5760 h2)) k) (Nat.mul (Nat.mul 5760 h2) h1)) t) (Nat.add (Nat.mul 3840 h1) (Nat.mul 3840 h2)))) : ℕ) : ℤ)
theorem tC13N_eq (B1 J2 t k h1 h2 : ℕ) : tC13N B1 J2 t k h1 h2 = tC13 B1 J2 t k h1 h2 := by
  unfold tC13N tC13
  simp only [Nat.add_eq, Nat.mul_eq]
  push_cast
  ring
def tC21N (B1 J2 t k h1 h2 : ℕ) : ℤ := (((Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 k) (Nat.add (Nat.mul 1920 h1) (Nat.add (Nat.mul 1920 h2) 1920))) k) (Nat.mul 1920 h1)) t) (Nat.add (Nat.mul 3840 k) (Nat.add (Nat.mul 960 h1) (Nat.add (Nat.mul 1920 h2) 1920)))) J2) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 h1) (Nat.mul 1920 h2)) k) (Nat.mul (Nat.mul 1920 h2) h1)) t) 3840)) : ℕ) : ℤ) - (((Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 2880 k) (Nat.add (Nat.mul 2880 h1) (Nat.add (Nat.mul 2880 h2) 2880))) k) (Nat.mul 2880 h1)) t) (Nat.add (Nat.mul 3840 k) (Nat.add (Nat.mul 1920 h2) 1920))) t) (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 960 h1) (Nat.mul 960 h2)) k) (Nat.mul (Nat.mul 1920 h2) h1)) J2)) : ℕ) : ℤ)
theorem tC21N_eq (B1 J2 t k h1 h2 : ℕ) : tC21N B1 J2 t k h1 h2 = tC21 B1 J2 t k h1 h2 := by
  unfold tC21N tC21
  simp only [Nat.add_eq, Nat.mul_eq]
  push_cast
  ring
def tC22N (B1 J2 t k h1 h2 : ℕ) : ℤ := (((Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 3360 k) (Nat.add (Nat.mul 3360 h1) (Nat.add (Nat.mul 3360 h2) 3360))) k) (Nat.mul 3360 h1)) t) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 k) (Nat.add (Nat.mul 1920 h1) (Nat.add (Nat.mul 1920 h2) 1920))) k) (Nat.mul 1920 h1)) B1) (Nat.add (Nat.mul 3840 k) (Nat.add (Nat.mul 1920 h2) 1920)))) t) (Nat.add (Nat.mul (Nat.add (Nat.mul 3840 k) (Nat.add (Nat.mul 960 h1) (Nat.add (Nat.mul 1920 h2) 1920))) B1) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1440 h1) (Nat.mul 1440 h2)) k) (Nat.mul (Nat.mul 2880 h2) h1)) J2) (Nat.add (Nat.mul 960 h1) (Nat.mul 960 h2))))) : ℕ) : ℤ) - (((Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 2880 k) (Nat.add (Nat.mul 2880 h1) (Nat.add (Nat.mul 2880 h2) 2880))) k) (Nat.mul 2880 h1)) t) (Nat.add (Nat.mul 5760 k) (Nat.add (Nat.mul 1440 h1) (Nat.add (Nat.mul 2880 h2) 2880)))) J2) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 B1) (Nat.add (Nat.mul 1920 t) 960)) h2) (Nat.mul (Nat.add (Nat.mul 960 B1) (Nat.mul 1920 t)) k)) h1) (Nat.add (Nat.mul (Nat.mul (Nat.add (Nat.mul 960 B1) (Nat.mul 1920 t)) h2) k) 5760))) : ℕ) : ℤ)
theorem tC22N_eq (B1 J2 t k h1 h2 : ℕ) : tC22N B1 J2 t k h1 h2 = tC22 B1 J2 t k h1 h2 := by
  unfold tC22N tC22
  simp only [Nat.add_eq, Nat.mul_eq]
  push_cast
  ring
def tC23N (B1 J2 t k h1 h2 : ℕ) : ℤ := (((Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 B1) (Nat.mul 6720 t)) k) (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 h1) (Nat.add (Nat.mul 1920 h2) 1920)) B1) (Nat.add (Nat.mul (Nat.add (Nat.mul 6720 h1) (Nat.add (Nat.mul 6720 h2) 6720)) t) 3840))) k) (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 B1) (Nat.mul 6720 t)) h1) (Nat.add (Nat.mul 1920 h2) 1920))) J2) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 k) (Nat.mul 1920 h2)) B1) (Nat.add (Nat.mul (Nat.add (Nat.mul 3840 k) (Nat.mul 3840 h2)) t) 1920)) h1) (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 B1) (Nat.mul 3840 t)) k) 1920) h2))) : ℕ) : ℤ) - (((Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 7200 t) (Nat.mul 5760 B1)) t) (Nat.mul (Nat.mul 1440 J2) J2)) k) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 7200 h1) (Nat.add (Nat.mul 7200 h2) 7200)) t) (Nat.add (Nat.mul (Nat.add (Nat.mul 5760 h1) (Nat.add (Nat.mul 5760 h2) 5760)) B1) 7680)) t) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1440 h1) (Nat.add (Nat.mul 1440 h2) 1440)) J2) (Nat.add (Nat.mul 1920 h1) (Nat.mul 1920 h2))) J2) (Nat.mul 3840 B1)))) k) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1440 J2) (Nat.mul 1920 h2)) J2) (Nat.add (Nat.mul (Nat.add (Nat.mul 7200 t) (Nat.mul 5760 B1)) t) (Nat.mul 1920 h2))) h1) (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 h2) 1920) B1) (Nat.add (Nat.mul (Nat.add (Nat.mul 3840 h2) 3840) t) 1920)))) : ℕ) : ℤ)
theorem tC23N_eq (B1 J2 t k h1 h2 : ℕ) : tC23N B1 J2 t k h1 h2 = tC23 B1 J2 t k h1 h2 := by
  unfold tC23N tC23
  simp only [Nat.add_eq, Nat.mul_eq]
  push_cast
  ring
def tC31N (B1 J2 t k h1 h2 : ℕ) : ℤ := (((Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.mul 960 J2) J2) (Nat.mul (Nat.mul 8640 t) t)) k) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 960 h1) (Nat.add (Nat.mul 960 h2) 960)) J2) (Nat.add (Nat.mul 1920 h1) (Nat.mul 1920 h2))) J2) (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 8640 h1) (Nat.add (Nat.mul 8640 h2) 8640)) t) 11520) t))) k) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 960 J2) (Nat.mul 1920 h2)) J2) (Nat.add (Nat.mul (Nat.mul 8640 t) t) (Nat.mul 3840 h2))) h1) (Nat.add (Nat.mul (Nat.add (Nat.mul 5760 h2) 5760) t) 3840))) : ℕ) : ℤ) - (((Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 5760 k) (Nat.add (Nat.mul 5760 h1) (Nat.add (Nat.mul 5760 h2) 5760))) k) (Nat.mul 5760 h1)) t) (Nat.add (Nat.mul 3840 k) (Nat.add (Nat.mul 1920 h2) 1920))) J2) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 5760 h1) (Nat.mul 5760 h2)) k) (Nat.mul (Nat.mul 5760 h2) h1)) t) (Nat.add (Nat.mul 3840 h1) (Nat.mul 3840 h2)))) : ℕ) : ℤ)
theorem tC31N_eq (B1 J2 t k h1 h2 : ℕ) : tC31N B1 J2 t k h1 h2 = tC31 B1 J2 t k h1 h2 := by
  unfold tC31N tC31
  simp only [Nat.add_eq, Nat.mul_eq]
  push_cast
  ring
def tC32N (B1 J2 t k h1 h2 : ℕ) : ℤ := (((Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 B1) (Nat.mul 6720 t)) k) (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 h1) (Nat.add (Nat.mul 1920 h2) 1920)) B1) (Nat.add (Nat.mul (Nat.add (Nat.mul 6720 h1) (Nat.add (Nat.mul 6720 h2) 6720)) t) 3840))) k) (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 B1) (Nat.mul 6720 t)) h1) (Nat.add (Nat.mul 1920 h2) 1920))) J2) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 k) (Nat.mul 1920 h2)) B1) (Nat.add (Nat.mul (Nat.add (Nat.mul 3840 k) (Nat.mul 3840 h2)) t) 1920)) h1) (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 B1) (Nat.mul 3840 t)) k) 1920) h2))) : ℕ) : ℤ) - (((Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 7200 t) (Nat.mul 5760 B1)) t) (Nat.mul (Nat.mul 1440 J2) J2)) k) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 7200 h1) (Nat.add (Nat.mul 7200 h2) 7200)) t) (Nat.add (Nat.mul (Nat.add (Nat.mul 5760 h1) (Nat.add (Nat.mul 5760 h2) 5760)) B1) 7680)) t) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1440 h1) (Nat.add (Nat.mul 1440 h2) 1440)) J2) (Nat.add (Nat.mul 1920 h1) (Nat.mul 1920 h2))) J2) (Nat.mul 3840 B1)))) k) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 1440 J2) (Nat.mul 1920 h2)) J2) (Nat.add (Nat.mul (Nat.add (Nat.mul 7200 t) (Nat.mul 5760 B1)) t) (Nat.mul 1920 h2))) h1) (Nat.add (Nat.mul (Nat.add (Nat.mul 1920 h2) 1920) B1) (Nat.add (Nat.mul (Nat.add (Nat.mul 3840 h2) 3840) t) 1920)))) : ℕ) : ℤ)
theorem tC32N_eq (B1 J2 t k h1 h2 : ℕ) : tC32N B1 J2 t k h1 h2 = tC32 B1 J2 t k h1 h2 := by
  unfold tC32N tC32
  simp only [Nat.add_eq, Nat.mul_eq]
  push_cast
  ring
def tC33N (B1 J2 t k h1 h2 : ℕ) : ℤ := (((Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 12960 t) (Nat.mul 17280 B1)) t) (Nat.mul (Nat.mul 3360 J2) J2)) k) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 12960 h1) (Nat.add (Nat.mul 12960 h2) 12960)) t) (Nat.add (Nat.mul (Nat.add (Nat.mul 17280 h1) (Nat.add (Nat.mul 17280 h2) 17280)) B1) 11520)) t) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 3360 h1) (Nat.add (Nat.mul 3360 h2) 3360)) J2) (Nat.add (Nat.mul 3840 h1) (Nat.mul 3840 h2))) J2) (Nat.mul 11520 B1)))) k) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 3360 J2) (Nat.mul 3840 h2)) J2) (Nat.add (Nat.mul (Nat.add (Nat.mul 12960 t) (Nat.mul 17280 B1)) t) (Nat.mul 1920 h2))) h1) (Nat.add (Nat.mul (Nat.add (Nat.mul 5760 h2) 5760) B1) (Nat.add (Nat.mul (Nat.add (Nat.mul 5760 h2) 5760) t) 1920)))) : ℕ) : ℤ) - (((Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 5760 B1) (Nat.mul 14400 t)) k) (Nat.add (Nat.mul (Nat.add (Nat.mul 5760 h1) (Nat.add (Nat.mul 5760 h2) 5760)) B1) (Nat.add (Nat.mul (Nat.add (Nat.mul 14400 h1) (Nat.add (Nat.mul 14400 h2) 14400)) t) 7680))) k) (Nat.add (Nat.mul (Nat.add (Nat.mul 5760 B1) (Nat.mul 14400 t)) h1) (Nat.add (Nat.mul 3840 h2) 3840))) J2) (Nat.add (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 5760 k) (Nat.mul 5760 h2)) B1) (Nat.add (Nat.mul (Nat.add (Nat.mul 5760 k) (Nat.mul 5760 h2)) t) 1920)) h1) (Nat.mul (Nat.add (Nat.mul (Nat.add (Nat.mul 5760 B1) (Nat.mul 5760 t)) k) 1920) h2))) : ℕ) : ℤ)
theorem tC33N_eq (B1 J2 t k h1 h2 : ℕ) : tC33N B1 J2 t k h1 h2 = tC33 B1 J2 t k h1 h2 := by
  unfold tC33N tC33
  simp only [Nat.add_eq, Nat.mul_eq]
  push_cast
  ring
theorem tsplit (B1 J2 t k h1 h2 x1 x2 x3 y1 y2 y3 : ℤ) :
    Low6969GateBilinear.Nt B1 J2 t k h1 h2 x1 x2 x3 y1 y2 y3 =
    tC12 B1 J2 t k h1 h2 * x1 * y2 +
    tC13 B1 J2 t k h1 h2 * x1 * y3 +
    tC21 B1 J2 t k h1 h2 * x2 * y1 +
    tC22 B1 J2 t k h1 h2 * x2 * y2 +
    tC23 B1 J2 t k h1 h2 * x2 * y3 +
    tC31 B1 J2 t k h1 h2 * x3 * y1 +
    tC32 B1 J2 t k h1 h2 * x3 * y2 +
    tC33 B1 J2 t k h1 h2 * x3 * y3 := rfl
def tRayF (P : Low6969GateBilinear.TP) (i k : Fin 3) : ℤ :=
  let c12 := tC12 P.B1 P.J2 P.t P.k P.h1 P.h2
  let c13 := tC13 P.B1 P.J2 P.t P.k P.h1 P.h2
  let c21 := tC21 P.B1 P.J2 P.t P.k P.h1 P.h2
  let c22 := tC22 P.B1 P.J2 P.t P.k P.h1 P.h2
  let c23 := tC23 P.B1 P.J2 P.t P.k P.h1 P.h2
  let c31 := tC31 P.B1 P.J2 P.t P.k P.h1 P.h2
  let c32 := tC32 P.B1 P.J2 P.t P.k P.h1 P.h2
  let c33 := tC33 P.B1 P.J2 P.t P.k P.h1 P.h2
  match i.val, k.val with
    | 0, 0 => 0
    | 0, 1 => c12
    | 0, 2 => 3 * c12 + c13
    | 1, 0 => c21
    | 1, 1 => c12 + c21 + c22
    | 1, 2 => 3 * c12 + c13 + 3 * c21 + 3 * c22 + c23
    | 2, 0 => 3 * c21 + c31
    | 2, 1 => 3 * c12 + 3 * c21 + 3 * c22 + c31 + c32
    | 2, 2 => 9 * c12 + 3 * c13 + 9 * c21 + 9 * c22 + 3 * c23 + 3 * c31 + 3 * c32 + c33
    | _, _ => 0

def tRayFN (B1 J2 t k h1 h2 : ℕ) (i kk : Fin 3) : ℤ :=
  let c12 := tC12N B1 J2 t k h1 h2
  let c13 := tC13N B1 J2 t k h1 h2
  let c21 := tC21N B1 J2 t k h1 h2
  let c22 := tC22N B1 J2 t k h1 h2
  let c23 := tC23N B1 J2 t k h1 h2
  let c31 := tC31N B1 J2 t k h1 h2
  let c32 := tC32N B1 J2 t k h1 h2
  let c33 := tC33N B1 J2 t k h1 h2
  match i.val, kk.val with
    | 0, 0 => 0
    | 0, 1 => c12
    | 0, 2 => 3 * c12 + c13
    | 1, 0 => c21
    | 1, 1 => c12 + c21 + c22
    | 1, 2 => 3 * c12 + c13 + 3 * c21 + 3 * c22 + c23
    | 2, 0 => 3 * c21 + c31
    | 2, 1 => 3 * c12 + 3 * c21 + 3 * c22 + c31 + c32
    | 2, 2 => 9 * c12 + 3 * c13 + 9 * c21 + 9 * c22 + 3 * c23 + 3 * c31 + 3 * c32 + c33
    | _, _ => 0

theorem tRayFN_eq (B1 J2 t k h1 h2 : ℕ) :
    tRayFN B1 J2 t k h1 h2 = tRayF ⟨(B1 : ℤ), (J2 : ℤ), (t : ℤ), (k : ℤ), (h1 : ℤ), (h2 : ℤ)⟩ := by
  funext i kk
  simp only [tRayFN, tRayF, tC12N_eq, tC13N_eq, tC21N_eq, tC22N_eq, tC23N_eq, tC31N_eq, tC32N_eq, tC33N_eq]

def oC11 (z1 z2 z3 w1 w2 w3 : ℤ) : ℤ := (0)
def oC12 (z1 z2 z3 w1 w2 w3 : ℤ) : ℤ := (16*(w2*z3 + w3*z2 - 3*w3*z3))
def oC13 (z1 z2 z3 w1 w2 w3 : ℤ) : ℤ := (16*(w2 - 3*w3)*(z2 - 3*z3))
def oC21 (z1 z2 z3 w1 w2 w3 : ℤ) : ℤ := (16*(w2*z3 + w3*z2 - 3*w3*z3))
def oC22 (z1 z2 z3 w1 w2 w3 : ℤ) : ℤ := (8*(2*w1*z3 - 3*w2*z3 + 2*w3*z1 - 3*w3*z2 + 7*w3*z3))
def oC23 (z1 z2 z3 w1 w2 w3 : ℤ) : ℤ := (8*(2*w1*z2 - 6*w1*z3 + 2*w2*z1 - 3*w2*z2 + 7*w2*z3 - 6*w3*z1 + 7*w3*z2 - 15*w3*z3))
def oC31 (z1 z2 z3 w1 w2 w3 : ℤ) : ℤ := (16*(w2 - 3*w3)*(z2 - 3*z3))
def oC32 (z1 z2 z3 w1 w2 w3 : ℤ) : ℤ := (8*(2*w1*z2 - 6*w1*z3 + 2*w2*z1 - 3*w2*z2 + 7*w2*z3 - 6*w3*z1 + 7*w3*z2 - 15*w3*z3))
def oC33 (z1 z2 z3 w1 w2 w3 : ℤ) : ℤ := (-8*(6*w1*z2 - 18*w1*z3 + 6*w2*z1 - 7*w2*z2 + 15*w2*z3 - 18*w3*z1 + 15*w3*z2 - 27*w3*z3))
theorem osplit (z1 z2 z3 w1 w2 w3 x1 x2 x3 y1 y2 y3 : ℤ) :
    Low6969GateBilinear.No z1 z2 z3 w1 w2 w3 x1 x2 x3 y1 y2 y3 =
    oC11 z1 z2 z3 w1 w2 w3 * x1 * y1 +
    oC12 z1 z2 z3 w1 w2 w3 * x1 * y2 +
    oC13 z1 z2 z3 w1 w2 w3 * x1 * y3 +
    oC21 z1 z2 z3 w1 w2 w3 * x2 * y1 +
    oC22 z1 z2 z3 w1 w2 w3 * x2 * y2 +
    oC23 z1 z2 z3 w1 w2 w3 * x2 * y3 +
    oC31 z1 z2 z3 w1 w2 w3 * x3 * y1 +
    oC32 z1 z2 z3 w1 w2 w3 * x3 * y2 +
    oC33 z1 z2 z3 w1 w2 w3 * x3 * y3 := rfl
def oRayF (P : Low6969GateBilinear.OP) (i k : Fin 3) : ℤ :=
  let c11 := oC11 P.z1 P.z2 P.z3 P.w1 P.w2 P.w3
  let c12 := oC12 P.z1 P.z2 P.z3 P.w1 P.w2 P.w3
  let c13 := oC13 P.z1 P.z2 P.z3 P.w1 P.w2 P.w3
  let c21 := oC21 P.z1 P.z2 P.z3 P.w1 P.w2 P.w3
  let c22 := oC22 P.z1 P.z2 P.z3 P.w1 P.w2 P.w3
  let c23 := oC23 P.z1 P.z2 P.z3 P.w1 P.w2 P.w3
  let c31 := oC31 P.z1 P.z2 P.z3 P.w1 P.w2 P.w3
  let c32 := oC32 P.z1 P.z2 P.z3 P.w1 P.w2 P.w3
  let c33 := oC33 P.z1 P.z2 P.z3 P.w1 P.w2 P.w3
  match i.val, k.val with
    | 0, 0 => c11
    | 0, 1 => c11 + c12
    | 0, 2 => 3 * c11 + 3 * c12 + c13
    | 1, 0 => c11 + c21
    | 1, 1 => c11 + c12 + c21 + c22
    | 1, 2 => 3 * c11 + 3 * c12 + c13 + 3 * c21 + 3 * c22 + c23
    | 2, 0 => 3 * c11 + 3 * c21 + c31
    | 2, 1 => 3 * c11 + 3 * c12 + 3 * c21 + 3 * c22 + c31 + c32
    | 2, 2 => 9 * c11 + 9 * c12 + 3 * c13 + 9 * c21 + 9 * c22 + 3 * c23 + 3 * c31 + 3 * c32 + c33
    | _, _ => 0

theorem tRayF_eq (P : TP) : tRayF P = P.ray := by
  funext i k
  fin_cases i <;> fin_cases k <;>
    simp [tRayF, TP.ray, TP.cone, TP.eval, tsplit] <;> ring
theorem oRayF_eq (P : OP) : oRayF P = P.ray := by
  funext i k
  fin_cases i <;> fin_cases k <;>
    simp [oRayF, OP.ray, OP.cone, osplit] <;> ring

theorem addF_eq (x : Shape) (l : ℕ) : Low6969FastPrice.additiveBaseF x l = Low6969SharedPrice.additiveBase x l := by
  simp only [Low6969FastPrice.additiveBaseF, Low6969SharedPrice.additiveBase, Low6969FastPrice.mixF_eq]

def orderB (b j : ℕ) : List Threshold → ℕ → ℕ
  | [], acc => acc
  | s :: rest, acc => orderB b j rest (bif Nat.ble s.b b && Nat.ble s.j j then (bif Nat.ble acc s.l then s.l else acc) else acc)

theorem orderB_aux (b j : ℕ) (l : List Threshold) : ∀ acc, 1 ≤ acc → orderB b j l acc = max acc (orderFor b j l) := by
  induction l with
  | nil => intro acc h; simp only [orderB, orderFor]; omega
  | cons s rest ih =>
    intro acc hacc
    simp only [orderB, orderFor]
    by_cases h : s.b ≤ b ∧ s.j ≤ j
    · have e : (Nat.ble s.b b && Nat.ble s.j j) = true := by
        simp only [Bool.and_eq_true, Nat.ble_eq]; exact h
      rw [e]
      simp only [Bool.cond_true, h, and_self, if_true]
      by_cases h2 : acc ≤ s.l
      · have e2 : Nat.ble acc s.l = true := Nat.ble_eq_true_of_le h2
        rw [e2]; simp only [Bool.cond_true]
        rw [ih _ (by omega)]
        omega
      · have e2 : Nat.ble acc s.l = false := by
          cases hh : Nat.ble acc s.l
          · rfl
          · exact absurd (Nat.le_of_ble_eq_true hh) h2
        rw [e2]; simp only [Bool.cond_false]
        rw [ih _ (by omega)]
        omega
    · have e : (Nat.ble s.b b && Nat.ble s.j j) = false := by
        cases hh : (Nat.ble s.b b && Nat.ble s.j j)
        · rfl
        · exfalso; apply h; simp only [Bool.and_eq_true, Nat.ble_eq] at hh; exact hh
      rw [e]
      simp only [Bool.cond_false, h, if_false]
      rw [ih _ hacc]
      omega

theorem one_le_orderFor (b j : ℕ) (l : List Threshold) : 1 ≤ orderFor b j l := by
  induction l with
  | nil => simp [orderFor]
  | cons s rest ih => simp only [orderFor]; exact le_trans ih (le_max_right _ _)

theorem orderB_eq {k : Low6969Allocation.Band} (cells : List (Low6969Allocation.MassCell k)) (x : Shape) :
    orderB x.b x.j (cells.map Subtype.val) 1 = Low6969Allocation.order cells x := by
  rw [orderB_aux _ _ _ 1 le_rfl]
  have := one_le_orderFor x.b x.j (cells.map Subtype.val)
  unfold Low6969Allocation.order
  omega

def gtGF (id t : ℕ) (p : ℕ × ℕ) (G : ℕ) : Bool :=
  let x : Shape := ⟨p.1, p.2, t⟩
  let k : Low6969Allocation.Band := ⟨id % 40, Nat.mod_lt _ (by decide)⟩
  let l := orderB x.b x.j ((Low6969Allocation.bandOrders k).map Subtype.val) 1
  Nat.blt 0 l && Nat.ble (Low6969FastPrice.additiveBaseF x l + Low6969SharedPrice.nonsharedFee x l + G)
    (Low6969Allocation.allowance k ((Low6969Allocation.start k).t + t) p.1 p.2 t)

theorem gtGF_eq (id t : ℕ) (p : ℕ × ℕ) (G : ℕ) : gtGF id t p G = gtG id t p G := by
  have h := orderB_eq (Low6969Allocation.bandOrders ⟨id % 40, Nat.mod_lt _ (by decide)⟩) ⟨p.1, p.2, t⟩
  dsimp only at h
  unfold gtGF gtG
  simp only [h, addF_eq]

def rayTF (x : Shape) : Fin 3 → Fin 3 → ℤ :=
  tRayFN (x.b - 1) (x.j - 2) x.t kT (Low6969Prices.bentLift kT x).2 (Low6969Prices.bentLift (kT + 1) x).2

theorem rayTF_eq' (x : Shape) :
    rayTF x = tRayF (tpOf x kT (Low6969Prices.bentLift kT x).2 (Low6969Prices.bentLift (kT + 1) x).2) := by
  unfold rayTF
  rw [tRayFN_eq]
  rfl
def rayOF (x : Shape) : Fin 3 → Fin 3 → ℤ :=
  oRayF (opOf (K1_13.chart (Low6969Prices.taylorLength + 1) x.chamber)
    (K1_13.chart (Low6969Prices.taylorLength + 2) x.chamber))
def rayKF (c : ℕ) (x : Shape) : Fin 3 → Fin 3 → ℤ := if isT c then rayTF x else rayOF x

theorem rayKF_eq (c : ℕ) (x : Shape) : rayKF c x = rayK c x := by
  unfold rayKF rayK rayOF rayT rayO
  rw [rayTF_eq', tRayF_eq, oRayF_eq]

def thNumF (r h : Fin 3 → Fin 3 → ℤ) : ℕ :=
  max (max (max (max (max (max (max (max (max 0 (cd (r 0 0) (h 0 0))) (cd (r 0 1) (h 0 1))) (cd (r 0 2) (h 0 2)))
    (cd (r 1 0) (h 1 0))) (cd (r 1 1) (h 1 1))) (cd (r 1 2) (h 1 2))) (cd (r 2 0) (h 2 0))) (cd (r 2 1) (h 2 1))) (cd (r 2 2) (h 2 2))

theorem thNumF_eq (r h : Fin 3 → Fin 3 → ℤ) : thNumF r h = thNum r h := by
  rfl

def sNF (c n : ℕ) (r : Fin 3 → Fin 3 → ℤ) : Bool :=
  if c = 0 then false else
    decide ((DEN : ℤ) * r 0 0 ≤ (n : ℤ) * hiL c 0 0) && decide ((DEN : ℤ) * r 0 1 ≤ (n : ℤ) * hiL c 0 1) &&
    decide ((DEN : ℤ) * r 0 2 ≤ (n : ℤ) * hiL c 0 2) && decide ((DEN : ℤ) * r 1 0 ≤ (n : ℤ) * hiL c 1 0) &&
    decide ((DEN : ℤ) * r 1 1 ≤ (n : ℤ) * hiL c 1 1) && decide ((DEN : ℤ) * r 1 2 ≤ (n : ℤ) * hiL c 1 2) &&
    decide ((DEN : ℤ) * r 2 0 ≤ (n : ℤ) * hiL c 2 0) && decide ((DEN : ℤ) * r 2 1 ≤ (n : ℤ) * hiL c 2 1) &&
    decide ((DEN : ℤ) * r 2 2 ≤ (n : ℤ) * hiL c 2 2)

theorem sNF_eq (c : ℕ) (x : Shape) (n : ℕ) : sNF c n (rayK c x) = sN c x n := by
  unfold sNF sN
  by_cases h : c = 0
  · simp [h]
  · simp only [h, if_false]
    rw [Bool.eq_iff_iff]
    simp [Fin.forall_fin_succ, and_assoc]

def fFF (id t : ℕ) (p : ℕ × ℕ) : Bool :=
  let x : Shape := ⟨p.1, p.2, t⟩
  let c := cls x
  let r := rayKF c x
  let n := thNumF r (hiL c)
  (!(valid x) || sNF c n r) && gtGF id t p (if c = 0 then 0 else Ax n (Gk c).A)

theorem fFF_eq (id t : ℕ) (p : ℕ × ℕ) : fFF id t p = fF id t p := by
  unfold fFF fF
  simp only [rayKF_eq, thNumF_eq, sNF_eq, gtGF_eq]

end FastGateRays

theorem both_of_chunks (id t N : ℕ) (hN : (Low6969Gate.gateList id t).length ≤ 32 * N)
    (h : ∀ i, i < N → (chunkOf (Low6969Gate.gateList id t) i).all (fFF id t) = true) :
    one id t = true ∧ gtOne id t = true := by
  have h1 : ∀ i, i < N → (chunkOf (Low6969Gate.gateList id t) i).all (oneF id t) = true := by
    intro i hi
    have := h i hi
    simp only [fFF_eq, fF_eq, List.all_eq_true, Bool.and_eq_true] at this ⊢
    exact fun p hp => (this p hp).1
  have h2 : ∀ i, i < N → (chunkOf (Low6969Gate.gateList id t) i).all (gtF id t) = true := by
    intro i hi
    have := h i hi
    simp only [fFF_eq, fF_eq, List.all_eq_true, Bool.and_eq_true] at this ⊢
    exact fun p hp => (this p hp).2
  exact ⟨one_of_chunks id t N hN h1, gtOne_of_chunks id t N hN h2⟩

end Low6969GateFin

end Merged_Low6969WitnessChunk
end Z6969Source2491

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck0Top2
section Z6969Source2492
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_0_2_0 : (chunkOf (Low6969Gate.gateList 0 2) 0).all (fFF 0 2) = true := by decide +kernel
private theorem f_0_2_1 : (chunkOf (Low6969Gate.gateList 0 2) 1).all (fFF 0 2) = true := by decide +kernel
private theorem f_0_2_2 : (chunkOf (Low6969Gate.gateList 0 2) 2).all (fFF 0 2) = true := by decide +kernel
private theorem f_0_2_3 : (chunkOf (Low6969Gate.gateList 0 2) 3).all (fFF 0 2) = true := by decide +kernel
private theorem f_0_2_4 : (chunkOf (Low6969Gate.gateList 0 2) 4).all (fFF 0 2) = true := by decide +kernel
private theorem f_0_2_5 : (chunkOf (Low6969Gate.gateList 0 2) 5).all (fFF 0 2) = true := by decide +kernel
private theorem f_0_2_6 : (chunkOf (Low6969Gate.gateList 0 2) 6).all (fFF 0 2) = true := by decide +kernel
private theorem f_0_2_7 : (chunkOf (Low6969Gate.gateList 0 2) 7).all (fFF 0 2) = true := by decide +kernel
private theorem f_0_2_8 : (chunkOf (Low6969Gate.gateList 0 2) 8).all (fFF 0 2) = true := by decide +kernel
private theorem f_0_2_9 : (chunkOf (Low6969Gate.gateList 0 2) 9).all (fFF 0 2) = true := by decide +kernel
private theorem f_0_2_10 : (chunkOf (Low6969Gate.gateList 0 2) 10).all (fFF 0 2) = true := by decide +kernel
theorem fb_0_2 : one 0 2 = true ∧ gtOne 0 2 = true :=
  both_of_chunks 0 2 11 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_2_0
    · exact f_0_2_1
    · exact f_0_2_2
    · exact f_0_2_3
    · exact f_0_2_4
    · exact f_0_2_5
    · exact f_0_2_6
    · exact f_0_2_7
    · exact f_0_2_8
    · exact f_0_2_9
    · exact f_0_2_10
  )
end Low6969GateFin
end Z6969Source2492

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck0Top3
section Z6969Source2493
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_0_3_0 : (chunkOf (Low6969Gate.gateList 0 3) 0).all (fFF 0 3) = true := by decide +kernel
private theorem f_0_3_1 : (chunkOf (Low6969Gate.gateList 0 3) 1).all (fFF 0 3) = true := by decide +kernel
private theorem f_0_3_2 : (chunkOf (Low6969Gate.gateList 0 3) 2).all (fFF 0 3) = true := by decide +kernel
private theorem f_0_3_3 : (chunkOf (Low6969Gate.gateList 0 3) 3).all (fFF 0 3) = true := by decide +kernel
private theorem f_0_3_4 : (chunkOf (Low6969Gate.gateList 0 3) 4).all (fFF 0 3) = true := by decide +kernel
private theorem f_0_3_5 : (chunkOf (Low6969Gate.gateList 0 3) 5).all (fFF 0 3) = true := by decide +kernel
private theorem f_0_3_6 : (chunkOf (Low6969Gate.gateList 0 3) 6).all (fFF 0 3) = true := by decide +kernel
private theorem f_0_3_7 : (chunkOf (Low6969Gate.gateList 0 3) 7).all (fFF 0 3) = true := by decide +kernel
private theorem f_0_3_8 : (chunkOf (Low6969Gate.gateList 0 3) 8).all (fFF 0 3) = true := by decide +kernel
theorem fb_0_3 : one 0 3 = true ∧ gtOne 0 3 = true :=
  both_of_chunks 0 3 9 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_3_0
    · exact f_0_3_1
    · exact f_0_3_2
    · exact f_0_3_3
    · exact f_0_3_4
    · exact f_0_3_5
    · exact f_0_3_6
    · exact f_0_3_7
    · exact f_0_3_8
  )
end Low6969GateFin
end Z6969Source2493

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck0Top4
section Z6969Source2494
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_0_4_0 : (chunkOf (Low6969Gate.gateList 0 4) 0).all (fFF 0 4) = true := by decide +kernel
private theorem f_0_4_1 : (chunkOf (Low6969Gate.gateList 0 4) 1).all (fFF 0 4) = true := by decide +kernel
private theorem f_0_4_2 : (chunkOf (Low6969Gate.gateList 0 4) 2).all (fFF 0 4) = true := by decide +kernel
private theorem f_0_4_3 : (chunkOf (Low6969Gate.gateList 0 4) 3).all (fFF 0 4) = true := by decide +kernel
private theorem f_0_4_4 : (chunkOf (Low6969Gate.gateList 0 4) 4).all (fFF 0 4) = true := by decide +kernel
private theorem f_0_4_5 : (chunkOf (Low6969Gate.gateList 0 4) 5).all (fFF 0 4) = true := by decide +kernel
private theorem f_0_4_6 : (chunkOf (Low6969Gate.gateList 0 4) 6).all (fFF 0 4) = true := by decide +kernel
private theorem f_0_4_7 : (chunkOf (Low6969Gate.gateList 0 4) 7).all (fFF 0 4) = true := by decide +kernel
private theorem f_0_4_8 : (chunkOf (Low6969Gate.gateList 0 4) 8).all (fFF 0 4) = true := by decide +kernel
private theorem f_0_4_9 : (chunkOf (Low6969Gate.gateList 0 4) 9).all (fFF 0 4) = true := by decide +kernel
private theorem f_0_4_10 : (chunkOf (Low6969Gate.gateList 0 4) 10).all (fFF 0 4) = true := by decide +kernel
theorem fb_0_4 : one 0 4 = true ∧ gtOne 0 4 = true :=
  both_of_chunks 0 4 11 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_4_0
    · exact f_0_4_1
    · exact f_0_4_2
    · exact f_0_4_3
    · exact f_0_4_4
    · exact f_0_4_5
    · exact f_0_4_6
    · exact f_0_4_7
    · exact f_0_4_8
    · exact f_0_4_9
    · exact f_0_4_10
  )
end Low6969GateFin
end Z6969Source2494

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck0Top5
section Z6969Source2495
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_0_5_0 : (chunkOf (Low6969Gate.gateList 0 5) 0).all (fFF 0 5) = true := by decide +kernel
private theorem f_0_5_1 : (chunkOf (Low6969Gate.gateList 0 5) 1).all (fFF 0 5) = true := by decide +kernel
private theorem f_0_5_2 : (chunkOf (Low6969Gate.gateList 0 5) 2).all (fFF 0 5) = true := by decide +kernel
private theorem f_0_5_3 : (chunkOf (Low6969Gate.gateList 0 5) 3).all (fFF 0 5) = true := by decide +kernel
private theorem f_0_5_4 : (chunkOf (Low6969Gate.gateList 0 5) 4).all (fFF 0 5) = true := by decide +kernel
private theorem f_0_5_5 : (chunkOf (Low6969Gate.gateList 0 5) 5).all (fFF 0 5) = true := by decide +kernel
private theorem f_0_5_6 : (chunkOf (Low6969Gate.gateList 0 5) 6).all (fFF 0 5) = true := by decide +kernel
private theorem f_0_5_7 : (chunkOf (Low6969Gate.gateList 0 5) 7).all (fFF 0 5) = true := by decide +kernel
private theorem f_0_5_8 : (chunkOf (Low6969Gate.gateList 0 5) 8).all (fFF 0 5) = true := by decide +kernel
private theorem f_0_5_9 : (chunkOf (Low6969Gate.gateList 0 5) 9).all (fFF 0 5) = true := by decide +kernel
private theorem f_0_5_10 : (chunkOf (Low6969Gate.gateList 0 5) 10).all (fFF 0 5) = true := by decide +kernel
private theorem f_0_5_11 : (chunkOf (Low6969Gate.gateList 0 5) 11).all (fFF 0 5) = true := by decide +kernel
private theorem f_0_5_12 : (chunkOf (Low6969Gate.gateList 0 5) 12).all (fFF 0 5) = true := by decide +kernel
theorem fb_0_5 : one 0 5 = true ∧ gtOne 0 5 = true :=
  both_of_chunks 0 5 13 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_5_0
    · exact f_0_5_1
    · exact f_0_5_2
    · exact f_0_5_3
    · exact f_0_5_4
    · exact f_0_5_5
    · exact f_0_5_6
    · exact f_0_5_7
    · exact f_0_5_8
    · exact f_0_5_9
    · exact f_0_5_10
    · exact f_0_5_11
    · exact f_0_5_12
  )
end Low6969GateFin
end Z6969Source2495

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck0Top6
section Z6969Source2496
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_0_6_0 : (chunkOf (Low6969Gate.gateList 0 6) 0).all (fFF 0 6) = true := by decide +kernel
private theorem f_0_6_1 : (chunkOf (Low6969Gate.gateList 0 6) 1).all (fFF 0 6) = true := by decide +kernel
private theorem f_0_6_2 : (chunkOf (Low6969Gate.gateList 0 6) 2).all (fFF 0 6) = true := by decide +kernel
private theorem f_0_6_3 : (chunkOf (Low6969Gate.gateList 0 6) 3).all (fFF 0 6) = true := by decide +kernel
private theorem f_0_6_4 : (chunkOf (Low6969Gate.gateList 0 6) 4).all (fFF 0 6) = true := by decide +kernel
private theorem f_0_6_5 : (chunkOf (Low6969Gate.gateList 0 6) 5).all (fFF 0 6) = true := by decide +kernel
private theorem f_0_6_6 : (chunkOf (Low6969Gate.gateList 0 6) 6).all (fFF 0 6) = true := by decide +kernel
private theorem f_0_6_7 : (chunkOf (Low6969Gate.gateList 0 6) 7).all (fFF 0 6) = true := by decide +kernel
private theorem f_0_6_8 : (chunkOf (Low6969Gate.gateList 0 6) 8).all (fFF 0 6) = true := by decide +kernel
private theorem f_0_6_9 : (chunkOf (Low6969Gate.gateList 0 6) 9).all (fFF 0 6) = true := by decide +kernel
private theorem f_0_6_10 : (chunkOf (Low6969Gate.gateList 0 6) 10).all (fFF 0 6) = true := by decide +kernel
private theorem f_0_6_11 : (chunkOf (Low6969Gate.gateList 0 6) 11).all (fFF 0 6) = true := by decide +kernel
private theorem f_0_6_12 : (chunkOf (Low6969Gate.gateList 0 6) 12).all (fFF 0 6) = true := by decide +kernel
private theorem f_0_6_13 : (chunkOf (Low6969Gate.gateList 0 6) 13).all (fFF 0 6) = true := by decide +kernel
private theorem f_0_6_14 : (chunkOf (Low6969Gate.gateList 0 6) 14).all (fFF 0 6) = true := by decide +kernel
theorem fb_0_6 : one 0 6 = true ∧ gtOne 0 6 = true :=
  both_of_chunks 0 6 15 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_6_0
    · exact f_0_6_1
    · exact f_0_6_2
    · exact f_0_6_3
    · exact f_0_6_4
    · exact f_0_6_5
    · exact f_0_6_6
    · exact f_0_6_7
    · exact f_0_6_8
    · exact f_0_6_9
    · exact f_0_6_10
    · exact f_0_6_11
    · exact f_0_6_12
    · exact f_0_6_13
    · exact f_0_6_14
  )
end Low6969GateFin
end Z6969Source2496

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck0Top7
section Z6969Source2497
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_0_7_0 : (chunkOf (Low6969Gate.gateList 0 7) 0).all (fFF 0 7) = true := by decide +kernel
private theorem f_0_7_1 : (chunkOf (Low6969Gate.gateList 0 7) 1).all (fFF 0 7) = true := by decide +kernel
private theorem f_0_7_2 : (chunkOf (Low6969Gate.gateList 0 7) 2).all (fFF 0 7) = true := by decide +kernel
private theorem f_0_7_3 : (chunkOf (Low6969Gate.gateList 0 7) 3).all (fFF 0 7) = true := by decide +kernel
private theorem f_0_7_4 : (chunkOf (Low6969Gate.gateList 0 7) 4).all (fFF 0 7) = true := by decide +kernel
private theorem f_0_7_5 : (chunkOf (Low6969Gate.gateList 0 7) 5).all (fFF 0 7) = true := by decide +kernel
private theorem f_0_7_6 : (chunkOf (Low6969Gate.gateList 0 7) 6).all (fFF 0 7) = true := by decide +kernel
private theorem f_0_7_7 : (chunkOf (Low6969Gate.gateList 0 7) 7).all (fFF 0 7) = true := by decide +kernel
private theorem f_0_7_8 : (chunkOf (Low6969Gate.gateList 0 7) 8).all (fFF 0 7) = true := by decide +kernel
private theorem f_0_7_9 : (chunkOf (Low6969Gate.gateList 0 7) 9).all (fFF 0 7) = true := by decide +kernel
private theorem f_0_7_10 : (chunkOf (Low6969Gate.gateList 0 7) 10).all (fFF 0 7) = true := by decide +kernel
private theorem f_0_7_11 : (chunkOf (Low6969Gate.gateList 0 7) 11).all (fFF 0 7) = true := by decide +kernel
private theorem f_0_7_12 : (chunkOf (Low6969Gate.gateList 0 7) 12).all (fFF 0 7) = true := by decide +kernel
private theorem f_0_7_13 : (chunkOf (Low6969Gate.gateList 0 7) 13).all (fFF 0 7) = true := by decide +kernel
private theorem f_0_7_14 : (chunkOf (Low6969Gate.gateList 0 7) 14).all (fFF 0 7) = true := by decide +kernel
private theorem f_0_7_15 : (chunkOf (Low6969Gate.gateList 0 7) 15).all (fFF 0 7) = true := by decide +kernel
private theorem f_0_7_16 : (chunkOf (Low6969Gate.gateList 0 7) 16).all (fFF 0 7) = true := by decide +kernel
theorem fb_0_7 : one 0 7 = true ∧ gtOne 0 7 = true :=
  both_of_chunks 0 7 17 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_7_0
    · exact f_0_7_1
    · exact f_0_7_2
    · exact f_0_7_3
    · exact f_0_7_4
    · exact f_0_7_5
    · exact f_0_7_6
    · exact f_0_7_7
    · exact f_0_7_8
    · exact f_0_7_9
    · exact f_0_7_10
    · exact f_0_7_11
    · exact f_0_7_12
    · exact f_0_7_13
    · exact f_0_7_14
    · exact f_0_7_15
    · exact f_0_7_16
  )
end Low6969GateFin
end Z6969Source2497

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck0Top8
section Z6969Source2498
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_0_8_0 : (chunkOf (Low6969Gate.gateList 0 8) 0).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_1 : (chunkOf (Low6969Gate.gateList 0 8) 1).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_2 : (chunkOf (Low6969Gate.gateList 0 8) 2).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_3 : (chunkOf (Low6969Gate.gateList 0 8) 3).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_4 : (chunkOf (Low6969Gate.gateList 0 8) 4).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_5 : (chunkOf (Low6969Gate.gateList 0 8) 5).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_6 : (chunkOf (Low6969Gate.gateList 0 8) 6).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_7 : (chunkOf (Low6969Gate.gateList 0 8) 7).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_8 : (chunkOf (Low6969Gate.gateList 0 8) 8).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_9 : (chunkOf (Low6969Gate.gateList 0 8) 9).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_10 : (chunkOf (Low6969Gate.gateList 0 8) 10).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_11 : (chunkOf (Low6969Gate.gateList 0 8) 11).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_12 : (chunkOf (Low6969Gate.gateList 0 8) 12).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_13 : (chunkOf (Low6969Gate.gateList 0 8) 13).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_14 : (chunkOf (Low6969Gate.gateList 0 8) 14).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_15 : (chunkOf (Low6969Gate.gateList 0 8) 15).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_16 : (chunkOf (Low6969Gate.gateList 0 8) 16).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_17 : (chunkOf (Low6969Gate.gateList 0 8) 17).all (fFF 0 8) = true := by decide +kernel
private theorem f_0_8_18 : (chunkOf (Low6969Gate.gateList 0 8) 18).all (fFF 0 8) = true := by decide +kernel
theorem fb_0_8 : one 0 8 = true ∧ gtOne 0 8 = true :=
  both_of_chunks 0 8 19 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_8_0
    · exact f_0_8_1
    · exact f_0_8_2
    · exact f_0_8_3
    · exact f_0_8_4
    · exact f_0_8_5
    · exact f_0_8_6
    · exact f_0_8_7
    · exact f_0_8_8
    · exact f_0_8_9
    · exact f_0_8_10
    · exact f_0_8_11
    · exact f_0_8_12
    · exact f_0_8_13
    · exact f_0_8_14
    · exact f_0_8_15
    · exact f_0_8_16
    · exact f_0_8_17
    · exact f_0_8_18
  )
end Low6969GateFin
end Z6969Source2498

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck0Top9
section Z6969Source2499
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_0_9_0 : (chunkOf (Low6969Gate.gateList 0 9) 0).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_1 : (chunkOf (Low6969Gate.gateList 0 9) 1).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_2 : (chunkOf (Low6969Gate.gateList 0 9) 2).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_3 : (chunkOf (Low6969Gate.gateList 0 9) 3).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_4 : (chunkOf (Low6969Gate.gateList 0 9) 4).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_5 : (chunkOf (Low6969Gate.gateList 0 9) 5).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_6 : (chunkOf (Low6969Gate.gateList 0 9) 6).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_7 : (chunkOf (Low6969Gate.gateList 0 9) 7).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_8 : (chunkOf (Low6969Gate.gateList 0 9) 8).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_9 : (chunkOf (Low6969Gate.gateList 0 9) 9).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_10 : (chunkOf (Low6969Gate.gateList 0 9) 10).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_11 : (chunkOf (Low6969Gate.gateList 0 9) 11).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_12 : (chunkOf (Low6969Gate.gateList 0 9) 12).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_13 : (chunkOf (Low6969Gate.gateList 0 9) 13).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_14 : (chunkOf (Low6969Gate.gateList 0 9) 14).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_15 : (chunkOf (Low6969Gate.gateList 0 9) 15).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_16 : (chunkOf (Low6969Gate.gateList 0 9) 16).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_17 : (chunkOf (Low6969Gate.gateList 0 9) 17).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_18 : (chunkOf (Low6969Gate.gateList 0 9) 18).all (fFF 0 9) = true := by decide +kernel
private theorem f_0_9_19 : (chunkOf (Low6969Gate.gateList 0 9) 19).all (fFF 0 9) = true := by decide +kernel
theorem fb_0_9 : one 0 9 = true ∧ gtOne 0 9 = true :=
  both_of_chunks 0 9 20 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_9_0
    · exact f_0_9_1
    · exact f_0_9_2
    · exact f_0_9_3
    · exact f_0_9_4
    · exact f_0_9_5
    · exact f_0_9_6
    · exact f_0_9_7
    · exact f_0_9_8
    · exact f_0_9_9
    · exact f_0_9_10
    · exact f_0_9_11
    · exact f_0_9_12
    · exact f_0_9_13
    · exact f_0_9_14
    · exact f_0_9_15
    · exact f_0_9_16
    · exact f_0_9_17
    · exact f_0_9_18
    · exact f_0_9_19
  )
end Low6969GateFin
end Z6969Source2499

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck0Top10
section Z6969Source2500
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_0_10_0 : (chunkOf (Low6969Gate.gateList 0 10) 0).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_1 : (chunkOf (Low6969Gate.gateList 0 10) 1).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_2 : (chunkOf (Low6969Gate.gateList 0 10) 2).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_3 : (chunkOf (Low6969Gate.gateList 0 10) 3).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_4 : (chunkOf (Low6969Gate.gateList 0 10) 4).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_5 : (chunkOf (Low6969Gate.gateList 0 10) 5).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_6 : (chunkOf (Low6969Gate.gateList 0 10) 6).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_7 : (chunkOf (Low6969Gate.gateList 0 10) 7).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_8 : (chunkOf (Low6969Gate.gateList 0 10) 8).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_9 : (chunkOf (Low6969Gate.gateList 0 10) 9).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_10 : (chunkOf (Low6969Gate.gateList 0 10) 10).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_11 : (chunkOf (Low6969Gate.gateList 0 10) 11).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_12 : (chunkOf (Low6969Gate.gateList 0 10) 12).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_13 : (chunkOf (Low6969Gate.gateList 0 10) 13).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_14 : (chunkOf (Low6969Gate.gateList 0 10) 14).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_15 : (chunkOf (Low6969Gate.gateList 0 10) 15).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_16 : (chunkOf (Low6969Gate.gateList 0 10) 16).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_17 : (chunkOf (Low6969Gate.gateList 0 10) 17).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_18 : (chunkOf (Low6969Gate.gateList 0 10) 18).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_19 : (chunkOf (Low6969Gate.gateList 0 10) 19).all (fFF 0 10) = true := by decide +kernel
private theorem f_0_10_20 : (chunkOf (Low6969Gate.gateList 0 10) 20).all (fFF 0 10) = true := by decide +kernel
theorem fb_0_10 : one 0 10 = true ∧ gtOne 0 10 = true :=
  both_of_chunks 0 10 21 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_10_0
    · exact f_0_10_1
    · exact f_0_10_2
    · exact f_0_10_3
    · exact f_0_10_4
    · exact f_0_10_5
    · exact f_0_10_6
    · exact f_0_10_7
    · exact f_0_10_8
    · exact f_0_10_9
    · exact f_0_10_10
    · exact f_0_10_11
    · exact f_0_10_12
    · exact f_0_10_13
    · exact f_0_10_14
    · exact f_0_10_15
    · exact f_0_10_16
    · exact f_0_10_17
    · exact f_0_10_18
    · exact f_0_10_19
    · exact f_0_10_20
  )
end Low6969GateFin
end Z6969Source2500

end Merged_Z6969Pack0918

-- merged module Z6969Pack0919
section Merged_Z6969Pack0919

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck0Top11
section Z6969Source2501
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_0_11_0 : (chunkOf (Low6969Gate.gateList 0 11) 0).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_1 : (chunkOf (Low6969Gate.gateList 0 11) 1).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_2 : (chunkOf (Low6969Gate.gateList 0 11) 2).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_3 : (chunkOf (Low6969Gate.gateList 0 11) 3).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_4 : (chunkOf (Low6969Gate.gateList 0 11) 4).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_5 : (chunkOf (Low6969Gate.gateList 0 11) 5).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_6 : (chunkOf (Low6969Gate.gateList 0 11) 6).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_7 : (chunkOf (Low6969Gate.gateList 0 11) 7).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_8 : (chunkOf (Low6969Gate.gateList 0 11) 8).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_9 : (chunkOf (Low6969Gate.gateList 0 11) 9).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_10 : (chunkOf (Low6969Gate.gateList 0 11) 10).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_11 : (chunkOf (Low6969Gate.gateList 0 11) 11).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_12 : (chunkOf (Low6969Gate.gateList 0 11) 12).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_13 : (chunkOf (Low6969Gate.gateList 0 11) 13).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_14 : (chunkOf (Low6969Gate.gateList 0 11) 14).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_15 : (chunkOf (Low6969Gate.gateList 0 11) 15).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_16 : (chunkOf (Low6969Gate.gateList 0 11) 16).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_17 : (chunkOf (Low6969Gate.gateList 0 11) 17).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_18 : (chunkOf (Low6969Gate.gateList 0 11) 18).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_19 : (chunkOf (Low6969Gate.gateList 0 11) 19).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_20 : (chunkOf (Low6969Gate.gateList 0 11) 20).all (fFF 0 11) = true := by decide +kernel
private theorem f_0_11_21 : (chunkOf (Low6969Gate.gateList 0 11) 21).all (fFF 0 11) = true := by decide +kernel
theorem fb_0_11 : one 0 11 = true ∧ gtOne 0 11 = true :=
  both_of_chunks 0 11 22 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_11_0
    · exact f_0_11_1
    · exact f_0_11_2
    · exact f_0_11_3
    · exact f_0_11_4
    · exact f_0_11_5
    · exact f_0_11_6
    · exact f_0_11_7
    · exact f_0_11_8
    · exact f_0_11_9
    · exact f_0_11_10
    · exact f_0_11_11
    · exact f_0_11_12
    · exact f_0_11_13
    · exact f_0_11_14
    · exact f_0_11_15
    · exact f_0_11_16
    · exact f_0_11_17
    · exact f_0_11_18
    · exact f_0_11_19
    · exact f_0_11_20
    · exact f_0_11_21
  )
end Low6969GateFin
end Z6969Source2501

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck0Top12
section Z6969Source2502
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_0_12_0 : (chunkOf (Low6969Gate.gateList 0 12) 0).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_1 : (chunkOf (Low6969Gate.gateList 0 12) 1).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_2 : (chunkOf (Low6969Gate.gateList 0 12) 2).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_3 : (chunkOf (Low6969Gate.gateList 0 12) 3).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_4 : (chunkOf (Low6969Gate.gateList 0 12) 4).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_5 : (chunkOf (Low6969Gate.gateList 0 12) 5).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_6 : (chunkOf (Low6969Gate.gateList 0 12) 6).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_7 : (chunkOf (Low6969Gate.gateList 0 12) 7).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_8 : (chunkOf (Low6969Gate.gateList 0 12) 8).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_9 : (chunkOf (Low6969Gate.gateList 0 12) 9).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_10 : (chunkOf (Low6969Gate.gateList 0 12) 10).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_11 : (chunkOf (Low6969Gate.gateList 0 12) 11).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_12 : (chunkOf (Low6969Gate.gateList 0 12) 12).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_13 : (chunkOf (Low6969Gate.gateList 0 12) 13).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_14 : (chunkOf (Low6969Gate.gateList 0 12) 14).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_15 : (chunkOf (Low6969Gate.gateList 0 12) 15).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_16 : (chunkOf (Low6969Gate.gateList 0 12) 16).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_17 : (chunkOf (Low6969Gate.gateList 0 12) 17).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_18 : (chunkOf (Low6969Gate.gateList 0 12) 18).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_19 : (chunkOf (Low6969Gate.gateList 0 12) 19).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_20 : (chunkOf (Low6969Gate.gateList 0 12) 20).all (fFF 0 12) = true := by decide +kernel
private theorem f_0_12_21 : (chunkOf (Low6969Gate.gateList 0 12) 21).all (fFF 0 12) = true := by decide +kernel
theorem fb_0_12 : one 0 12 = true ∧ gtOne 0 12 = true :=
  both_of_chunks 0 12 22 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_12_0
    · exact f_0_12_1
    · exact f_0_12_2
    · exact f_0_12_3
    · exact f_0_12_4
    · exact f_0_12_5
    · exact f_0_12_6
    · exact f_0_12_7
    · exact f_0_12_8
    · exact f_0_12_9
    · exact f_0_12_10
    · exact f_0_12_11
    · exact f_0_12_12
    · exact f_0_12_13
    · exact f_0_12_14
    · exact f_0_12_15
    · exact f_0_12_16
    · exact f_0_12_17
    · exact f_0_12_18
    · exact f_0_12_19
    · exact f_0_12_20
    · exact f_0_12_21
  )
end Low6969GateFin
end Z6969Source2502

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck0Top13
section Z6969Source2503
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_0_13_0 : (chunkOf (Low6969Gate.gateList 0 13) 0).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_1 : (chunkOf (Low6969Gate.gateList 0 13) 1).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_2 : (chunkOf (Low6969Gate.gateList 0 13) 2).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_3 : (chunkOf (Low6969Gate.gateList 0 13) 3).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_4 : (chunkOf (Low6969Gate.gateList 0 13) 4).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_5 : (chunkOf (Low6969Gate.gateList 0 13) 5).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_6 : (chunkOf (Low6969Gate.gateList 0 13) 6).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_7 : (chunkOf (Low6969Gate.gateList 0 13) 7).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_8 : (chunkOf (Low6969Gate.gateList 0 13) 8).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_9 : (chunkOf (Low6969Gate.gateList 0 13) 9).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_10 : (chunkOf (Low6969Gate.gateList 0 13) 10).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_11 : (chunkOf (Low6969Gate.gateList 0 13) 11).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_12 : (chunkOf (Low6969Gate.gateList 0 13) 12).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_13 : (chunkOf (Low6969Gate.gateList 0 13) 13).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_14 : (chunkOf (Low6969Gate.gateList 0 13) 14).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_15 : (chunkOf (Low6969Gate.gateList 0 13) 15).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_16 : (chunkOf (Low6969Gate.gateList 0 13) 16).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_17 : (chunkOf (Low6969Gate.gateList 0 13) 17).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_18 : (chunkOf (Low6969Gate.gateList 0 13) 18).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_19 : (chunkOf (Low6969Gate.gateList 0 13) 19).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_20 : (chunkOf (Low6969Gate.gateList 0 13) 20).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_21 : (chunkOf (Low6969Gate.gateList 0 13) 21).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_22 : (chunkOf (Low6969Gate.gateList 0 13) 22).all (fFF 0 13) = true := by decide +kernel
private theorem f_0_13_23 : (chunkOf (Low6969Gate.gateList 0 13) 23).all (fFF 0 13) = true := by decide +kernel
theorem fb_0_13 : one 0 13 = true ∧ gtOne 0 13 = true :=
  both_of_chunks 0 13 24 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_13_0
    · exact f_0_13_1
    · exact f_0_13_2
    · exact f_0_13_3
    · exact f_0_13_4
    · exact f_0_13_5
    · exact f_0_13_6
    · exact f_0_13_7
    · exact f_0_13_8
    · exact f_0_13_9
    · exact f_0_13_10
    · exact f_0_13_11
    · exact f_0_13_12
    · exact f_0_13_13
    · exact f_0_13_14
    · exact f_0_13_15
    · exact f_0_13_16
    · exact f_0_13_17
    · exact f_0_13_18
    · exact f_0_13_19
    · exact f_0_13_20
    · exact f_0_13_21
    · exact f_0_13_22
    · exact f_0_13_23
  )
end Low6969GateFin
end Z6969Source2503

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck0Top14
section Z6969Source2504
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_0_14_0 : (chunkOf (Low6969Gate.gateList 0 14) 0).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_1 : (chunkOf (Low6969Gate.gateList 0 14) 1).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_2 : (chunkOf (Low6969Gate.gateList 0 14) 2).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_3 : (chunkOf (Low6969Gate.gateList 0 14) 3).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_4 : (chunkOf (Low6969Gate.gateList 0 14) 4).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_5 : (chunkOf (Low6969Gate.gateList 0 14) 5).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_6 : (chunkOf (Low6969Gate.gateList 0 14) 6).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_7 : (chunkOf (Low6969Gate.gateList 0 14) 7).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_8 : (chunkOf (Low6969Gate.gateList 0 14) 8).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_9 : (chunkOf (Low6969Gate.gateList 0 14) 9).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_10 : (chunkOf (Low6969Gate.gateList 0 14) 10).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_11 : (chunkOf (Low6969Gate.gateList 0 14) 11).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_12 : (chunkOf (Low6969Gate.gateList 0 14) 12).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_13 : (chunkOf (Low6969Gate.gateList 0 14) 13).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_14 : (chunkOf (Low6969Gate.gateList 0 14) 14).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_15 : (chunkOf (Low6969Gate.gateList 0 14) 15).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_16 : (chunkOf (Low6969Gate.gateList 0 14) 16).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_17 : (chunkOf (Low6969Gate.gateList 0 14) 17).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_18 : (chunkOf (Low6969Gate.gateList 0 14) 18).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_19 : (chunkOf (Low6969Gate.gateList 0 14) 19).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_20 : (chunkOf (Low6969Gate.gateList 0 14) 20).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_21 : (chunkOf (Low6969Gate.gateList 0 14) 21).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_22 : (chunkOf (Low6969Gate.gateList 0 14) 22).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_23 : (chunkOf (Low6969Gate.gateList 0 14) 23).all (fFF 0 14) = true := by decide +kernel
private theorem f_0_14_24 : (chunkOf (Low6969Gate.gateList 0 14) 24).all (fFF 0 14) = true := by decide +kernel
theorem fb_0_14 : one 0 14 = true ∧ gtOne 0 14 = true :=
  both_of_chunks 0 14 25 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_14_0
    · exact f_0_14_1
    · exact f_0_14_2
    · exact f_0_14_3
    · exact f_0_14_4
    · exact f_0_14_5
    · exact f_0_14_6
    · exact f_0_14_7
    · exact f_0_14_8
    · exact f_0_14_9
    · exact f_0_14_10
    · exact f_0_14_11
    · exact f_0_14_12
    · exact f_0_14_13
    · exact f_0_14_14
    · exact f_0_14_15
    · exact f_0_14_16
    · exact f_0_14_17
    · exact f_0_14_18
    · exact f_0_14_19
    · exact f_0_14_20
    · exact f_0_14_21
    · exact f_0_14_22
    · exact f_0_14_23
    · exact f_0_14_24
  )
end Low6969GateFin
end Z6969Source2504

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck0Top15
section Z6969Source2505
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_0_15_0 : (chunkOf (Low6969Gate.gateList 0 15) 0).all (fFF 0 15) = true := by decide +kernel
private theorem f_0_15_1 : (chunkOf (Low6969Gate.gateList 0 15) 1).all (fFF 0 15) = true := by decide +kernel
private theorem f_0_15_2 : (chunkOf (Low6969Gate.gateList 0 15) 2).all (fFF 0 15) = true := by decide +kernel
private theorem f_0_15_3 : (chunkOf (Low6969Gate.gateList 0 15) 3).all (fFF 0 15) = true := by decide +kernel
private theorem f_0_15_4 : (chunkOf (Low6969Gate.gateList 0 15) 4).all (fFF 0 15) = true := by decide +kernel
private theorem f_0_15_5 : (chunkOf (Low6969Gate.gateList 0 15) 5).all (fFF 0 15) = true := by decide +kernel
private theorem f_0_15_6 : (chunkOf (Low6969Gate.gateList 0 15) 6).all (fFF 0 15) = true := by decide +kernel
private theorem f_0_15_7 : (chunkOf (Low6969Gate.gateList 0 15) 7).all (fFF 0 15) = true := by decide +kernel
private theorem f_0_15_8 : (chunkOf (Low6969Gate.gateList 0 15) 8).all (fFF 0 15) = true := by decide +kernel
private theorem f_0_15_9 : (chunkOf (Low6969Gate.gateList 0 15) 9).all (fFF 0 15) = true := by decide +kernel
private theorem f_0_15_10 : (chunkOf (Low6969Gate.gateList 0 15) 10).all (fFF 0 15) = true := by decide +kernel
private theorem f_0_15_11 : (chunkOf (Low6969Gate.gateList 0 15) 11).all (fFF 0 15) = true := by decide +kernel
private theorem f_0_15_12 : (chunkOf (Low6969Gate.gateList 0 15) 12).all (fFF 0 15) = true := by decide +kernel
theorem fb_0_15 : one 0 15 = true ∧ gtOne 0 15 = true :=
  both_of_chunks 0 15 13 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_0_15_0
    · exact f_0_15_1
    · exact f_0_15_2
    · exact f_0_15_3
    · exact f_0_15_4
    · exact f_0_15_5
    · exact f_0_15_6
    · exact f_0_15_7
    · exact f_0_15_8
    · exact f_0_15_9
    · exact f_0_15_10
    · exact f_0_15_11
    · exact f_0_15_12
  )
end Low6969GateFin
end Z6969Source2505

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck1
section Z6969Source2506
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_1_2_0 : (chunkOf (Low6969Gate.gateList 1 2) 0).all (fFF 1 2) = true := by decide +kernel
theorem fb_1_2 : one 1 2 = true ∧ gtOne 1 2 = true :=
  both_of_chunks 1 2 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_2_0
  )
private theorem f_1_3_0 : (chunkOf (Low6969Gate.gateList 1 3) 0).all (fFF 1 3) = true := by decide +kernel
private theorem f_1_3_1 : (chunkOf (Low6969Gate.gateList 1 3) 1).all (fFF 1 3) = true := by decide +kernel
theorem fb_1_3 : one 1 3 = true ∧ gtOne 1 3 = true :=
  both_of_chunks 1 3 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_3_0
    · exact f_1_3_1
  )
private theorem f_1_4_0 : (chunkOf (Low6969Gate.gateList 1 4) 0).all (fFF 1 4) = true := by decide +kernel
private theorem f_1_4_1 : (chunkOf (Low6969Gate.gateList 1 4) 1).all (fFF 1 4) = true := by decide +kernel
theorem fb_1_4 : one 1 4 = true ∧ gtOne 1 4 = true :=
  both_of_chunks 1 4 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_4_0
    · exact f_1_4_1
  )
private theorem f_1_5_0 : (chunkOf (Low6969Gate.gateList 1 5) 0).all (fFF 1 5) = true := by decide +kernel
private theorem f_1_5_1 : (chunkOf (Low6969Gate.gateList 1 5) 1).all (fFF 1 5) = true := by decide +kernel
private theorem f_1_5_2 : (chunkOf (Low6969Gate.gateList 1 5) 2).all (fFF 1 5) = true := by decide +kernel
theorem fb_1_5 : one 1 5 = true ∧ gtOne 1 5 = true :=
  both_of_chunks 1 5 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_5_0
    · exact f_1_5_1
    · exact f_1_5_2
  )
private theorem f_1_6_0 : (chunkOf (Low6969Gate.gateList 1 6) 0).all (fFF 1 6) = true := by decide +kernel
private theorem f_1_6_1 : (chunkOf (Low6969Gate.gateList 1 6) 1).all (fFF 1 6) = true := by decide +kernel
private theorem f_1_6_2 : (chunkOf (Low6969Gate.gateList 1 6) 2).all (fFF 1 6) = true := by decide +kernel
theorem fb_1_6 : one 1 6 = true ∧ gtOne 1 6 = true :=
  both_of_chunks 1 6 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_6_0
    · exact f_1_6_1
    · exact f_1_6_2
  )
private theorem f_1_7_0 : (chunkOf (Low6969Gate.gateList 1 7) 0).all (fFF 1 7) = true := by decide +kernel
private theorem f_1_7_1 : (chunkOf (Low6969Gate.gateList 1 7) 1).all (fFF 1 7) = true := by decide +kernel
private theorem f_1_7_2 : (chunkOf (Low6969Gate.gateList 1 7) 2).all (fFF 1 7) = true := by decide +kernel
private theorem f_1_7_3 : (chunkOf (Low6969Gate.gateList 1 7) 3).all (fFF 1 7) = true := by decide +kernel
theorem fb_1_7 : one 1 7 = true ∧ gtOne 1 7 = true :=
  both_of_chunks 1 7 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_7_0
    · exact f_1_7_1
    · exact f_1_7_2
    · exact f_1_7_3
  )
private theorem f_1_8_0 : (chunkOf (Low6969Gate.gateList 1 8) 0).all (fFF 1 8) = true := by decide +kernel
private theorem f_1_8_1 : (chunkOf (Low6969Gate.gateList 1 8) 1).all (fFF 1 8) = true := by decide +kernel
private theorem f_1_8_2 : (chunkOf (Low6969Gate.gateList 1 8) 2).all (fFF 1 8) = true := by decide +kernel
private theorem f_1_8_3 : (chunkOf (Low6969Gate.gateList 1 8) 3).all (fFF 1 8) = true := by decide +kernel
theorem fb_1_8 : one 1 8 = true ∧ gtOne 1 8 = true :=
  both_of_chunks 1 8 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_8_0
    · exact f_1_8_1
    · exact f_1_8_2
    · exact f_1_8_3
  )
private theorem f_1_9_0 : (chunkOf (Low6969Gate.gateList 1 9) 0).all (fFF 1 9) = true := by decide +kernel
private theorem f_1_9_1 : (chunkOf (Low6969Gate.gateList 1 9) 1).all (fFF 1 9) = true := by decide +kernel
private theorem f_1_9_2 : (chunkOf (Low6969Gate.gateList 1 9) 2).all (fFF 1 9) = true := by decide +kernel
private theorem f_1_9_3 : (chunkOf (Low6969Gate.gateList 1 9) 3).all (fFF 1 9) = true := by decide +kernel
theorem fb_1_9 : one 1 9 = true ∧ gtOne 1 9 = true :=
  both_of_chunks 1 9 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_9_0
    · exact f_1_9_1
    · exact f_1_9_2
    · exact f_1_9_3
  )
private theorem f_1_10_0 : (chunkOf (Low6969Gate.gateList 1 10) 0).all (fFF 1 10) = true := by decide +kernel
private theorem f_1_10_1 : (chunkOf (Low6969Gate.gateList 1 10) 1).all (fFF 1 10) = true := by decide +kernel
private theorem f_1_10_2 : (chunkOf (Low6969Gate.gateList 1 10) 2).all (fFF 1 10) = true := by decide +kernel
private theorem f_1_10_3 : (chunkOf (Low6969Gate.gateList 1 10) 3).all (fFF 1 10) = true := by decide +kernel
private theorem f_1_10_4 : (chunkOf (Low6969Gate.gateList 1 10) 4).all (fFF 1 10) = true := by decide +kernel
theorem fb_1_10 : one 1 10 = true ∧ gtOne 1 10 = true :=
  both_of_chunks 1 10 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_10_0
    · exact f_1_10_1
    · exact f_1_10_2
    · exact f_1_10_3
    · exact f_1_10_4
  )
private theorem f_1_11_0 : (chunkOf (Low6969Gate.gateList 1 11) 0).all (fFF 1 11) = true := by decide +kernel
private theorem f_1_11_1 : (chunkOf (Low6969Gate.gateList 1 11) 1).all (fFF 1 11) = true := by decide +kernel
private theorem f_1_11_2 : (chunkOf (Low6969Gate.gateList 1 11) 2).all (fFF 1 11) = true := by decide +kernel
private theorem f_1_11_3 : (chunkOf (Low6969Gate.gateList 1 11) 3).all (fFF 1 11) = true := by decide +kernel
private theorem f_1_11_4 : (chunkOf (Low6969Gate.gateList 1 11) 4).all (fFF 1 11) = true := by decide +kernel
theorem fb_1_11 : one 1 11 = true ∧ gtOne 1 11 = true :=
  both_of_chunks 1 11 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_11_0
    · exact f_1_11_1
    · exact f_1_11_2
    · exact f_1_11_3
    · exact f_1_11_4
  )
private theorem f_1_12_0 : (chunkOf (Low6969Gate.gateList 1 12) 0).all (fFF 1 12) = true := by decide +kernel
private theorem f_1_12_1 : (chunkOf (Low6969Gate.gateList 1 12) 1).all (fFF 1 12) = true := by decide +kernel
private theorem f_1_12_2 : (chunkOf (Low6969Gate.gateList 1 12) 2).all (fFF 1 12) = true := by decide +kernel
private theorem f_1_12_3 : (chunkOf (Low6969Gate.gateList 1 12) 3).all (fFF 1 12) = true := by decide +kernel
private theorem f_1_12_4 : (chunkOf (Low6969Gate.gateList 1 12) 4).all (fFF 1 12) = true := by decide +kernel
theorem fb_1_12 : one 1 12 = true ∧ gtOne 1 12 = true :=
  both_of_chunks 1 12 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_12_0
    · exact f_1_12_1
    · exact f_1_12_2
    · exact f_1_12_3
    · exact f_1_12_4
  )
private theorem f_1_13_0 : (chunkOf (Low6969Gate.gateList 1 13) 0).all (fFF 1 13) = true := by decide +kernel
private theorem f_1_13_1 : (chunkOf (Low6969Gate.gateList 1 13) 1).all (fFF 1 13) = true := by decide +kernel
private theorem f_1_13_2 : (chunkOf (Low6969Gate.gateList 1 13) 2).all (fFF 1 13) = true := by decide +kernel
private theorem f_1_13_3 : (chunkOf (Low6969Gate.gateList 1 13) 3).all (fFF 1 13) = true := by decide +kernel
private theorem f_1_13_4 : (chunkOf (Low6969Gate.gateList 1 13) 4).all (fFF 1 13) = true := by decide +kernel
theorem fb_1_13 : one 1 13 = true ∧ gtOne 1 13 = true :=
  both_of_chunks 1 13 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_13_0
    · exact f_1_13_1
    · exact f_1_13_2
    · exact f_1_13_3
    · exact f_1_13_4
  )
private theorem f_1_14_0 : (chunkOf (Low6969Gate.gateList 1 14) 0).all (fFF 1 14) = true := by decide +kernel
private theorem f_1_14_1 : (chunkOf (Low6969Gate.gateList 1 14) 1).all (fFF 1 14) = true := by decide +kernel
private theorem f_1_14_2 : (chunkOf (Low6969Gate.gateList 1 14) 2).all (fFF 1 14) = true := by decide +kernel
private theorem f_1_14_3 : (chunkOf (Low6969Gate.gateList 1 14) 3).all (fFF 1 14) = true := by decide +kernel
private theorem f_1_14_4 : (chunkOf (Low6969Gate.gateList 1 14) 4).all (fFF 1 14) = true := by decide +kernel
theorem fb_1_14 : one 1 14 = true ∧ gtOne 1 14 = true :=
  both_of_chunks 1 14 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_1_14_0
    · exact f_1_14_1
    · exact f_1_14_2
    · exact f_1_14_3
    · exact f_1_14_4
  )
end Low6969GateFin
end Z6969Source2506

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck2
section Z6969Source2507
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_2_2_0 : (chunkOf (Low6969Gate.gateList 2 2) 0).all (fFF 2 2) = true := by decide +kernel
theorem fb_2_2 : one 2 2 = true ∧ gtOne 2 2 = true :=
  both_of_chunks 2 2 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_2_0
  )
private theorem f_2_3_0 : (chunkOf (Low6969Gate.gateList 2 3) 0).all (fFF 2 3) = true := by decide +kernel
theorem fb_2_3 : one 2 3 = true ∧ gtOne 2 3 = true :=
  both_of_chunks 2 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_3_0
  )
private theorem f_2_4_0 : (chunkOf (Low6969Gate.gateList 2 4) 0).all (fFF 2 4) = true := by decide +kernel
private theorem f_2_4_1 : (chunkOf (Low6969Gate.gateList 2 4) 1).all (fFF 2 4) = true := by decide +kernel
theorem fb_2_4 : one 2 4 = true ∧ gtOne 2 4 = true :=
  both_of_chunks 2 4 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_4_0
    · exact f_2_4_1
  )
private theorem f_2_5_0 : (chunkOf (Low6969Gate.gateList 2 5) 0).all (fFF 2 5) = true := by decide +kernel
private theorem f_2_5_1 : (chunkOf (Low6969Gate.gateList 2 5) 1).all (fFF 2 5) = true := by decide +kernel
private theorem f_2_5_2 : (chunkOf (Low6969Gate.gateList 2 5) 2).all (fFF 2 5) = true := by decide +kernel
theorem fb_2_5 : one 2 5 = true ∧ gtOne 2 5 = true :=
  both_of_chunks 2 5 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_5_0
    · exact f_2_5_1
    · exact f_2_5_2
  )
private theorem f_2_6_0 : (chunkOf (Low6969Gate.gateList 2 6) 0).all (fFF 2 6) = true := by decide +kernel
private theorem f_2_6_1 : (chunkOf (Low6969Gate.gateList 2 6) 1).all (fFF 2 6) = true := by decide +kernel
private theorem f_2_6_2 : (chunkOf (Low6969Gate.gateList 2 6) 2).all (fFF 2 6) = true := by decide +kernel
theorem fb_2_6 : one 2 6 = true ∧ gtOne 2 6 = true :=
  both_of_chunks 2 6 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_6_0
    · exact f_2_6_1
    · exact f_2_6_2
  )
private theorem f_2_7_0 : (chunkOf (Low6969Gate.gateList 2 7) 0).all (fFF 2 7) = true := by decide +kernel
private theorem f_2_7_1 : (chunkOf (Low6969Gate.gateList 2 7) 1).all (fFF 2 7) = true := by decide +kernel
private theorem f_2_7_2 : (chunkOf (Low6969Gate.gateList 2 7) 2).all (fFF 2 7) = true := by decide +kernel
private theorem f_2_7_3 : (chunkOf (Low6969Gate.gateList 2 7) 3).all (fFF 2 7) = true := by decide +kernel
theorem fb_2_7 : one 2 7 = true ∧ gtOne 2 7 = true :=
  both_of_chunks 2 7 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_7_0
    · exact f_2_7_1
    · exact f_2_7_2
    · exact f_2_7_3
  )
private theorem f_2_8_0 : (chunkOf (Low6969Gate.gateList 2 8) 0).all (fFF 2 8) = true := by decide +kernel
private theorem f_2_8_1 : (chunkOf (Low6969Gate.gateList 2 8) 1).all (fFF 2 8) = true := by decide +kernel
private theorem f_2_8_2 : (chunkOf (Low6969Gate.gateList 2 8) 2).all (fFF 2 8) = true := by decide +kernel
private theorem f_2_8_3 : (chunkOf (Low6969Gate.gateList 2 8) 3).all (fFF 2 8) = true := by decide +kernel
theorem fb_2_8 : one 2 8 = true ∧ gtOne 2 8 = true :=
  both_of_chunks 2 8 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_8_0
    · exact f_2_8_1
    · exact f_2_8_2
    · exact f_2_8_3
  )
private theorem f_2_9_0 : (chunkOf (Low6969Gate.gateList 2 9) 0).all (fFF 2 9) = true := by decide +kernel
private theorem f_2_9_1 : (chunkOf (Low6969Gate.gateList 2 9) 1).all (fFF 2 9) = true := by decide +kernel
private theorem f_2_9_2 : (chunkOf (Low6969Gate.gateList 2 9) 2).all (fFF 2 9) = true := by decide +kernel
private theorem f_2_9_3 : (chunkOf (Low6969Gate.gateList 2 9) 3).all (fFF 2 9) = true := by decide +kernel
private theorem f_2_9_4 : (chunkOf (Low6969Gate.gateList 2 9) 4).all (fFF 2 9) = true := by decide +kernel
theorem fb_2_9 : one 2 9 = true ∧ gtOne 2 9 = true :=
  both_of_chunks 2 9 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_9_0
    · exact f_2_9_1
    · exact f_2_9_2
    · exact f_2_9_3
    · exact f_2_9_4
  )
private theorem f_2_10_0 : (chunkOf (Low6969Gate.gateList 2 10) 0).all (fFF 2 10) = true := by decide +kernel
private theorem f_2_10_1 : (chunkOf (Low6969Gate.gateList 2 10) 1).all (fFF 2 10) = true := by decide +kernel
private theorem f_2_10_2 : (chunkOf (Low6969Gate.gateList 2 10) 2).all (fFF 2 10) = true := by decide +kernel
private theorem f_2_10_3 : (chunkOf (Low6969Gate.gateList 2 10) 3).all (fFF 2 10) = true := by decide +kernel
private theorem f_2_10_4 : (chunkOf (Low6969Gate.gateList 2 10) 4).all (fFF 2 10) = true := by decide +kernel
theorem fb_2_10 : one 2 10 = true ∧ gtOne 2 10 = true :=
  both_of_chunks 2 10 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_10_0
    · exact f_2_10_1
    · exact f_2_10_2
    · exact f_2_10_3
    · exact f_2_10_4
  )
private theorem f_2_11_0 : (chunkOf (Low6969Gate.gateList 2 11) 0).all (fFF 2 11) = true := by decide +kernel
private theorem f_2_11_1 : (chunkOf (Low6969Gate.gateList 2 11) 1).all (fFF 2 11) = true := by decide +kernel
private theorem f_2_11_2 : (chunkOf (Low6969Gate.gateList 2 11) 2).all (fFF 2 11) = true := by decide +kernel
private theorem f_2_11_3 : (chunkOf (Low6969Gate.gateList 2 11) 3).all (fFF 2 11) = true := by decide +kernel
private theorem f_2_11_4 : (chunkOf (Low6969Gate.gateList 2 11) 4).all (fFF 2 11) = true := by decide +kernel
theorem fb_2_11 : one 2 11 = true ∧ gtOne 2 11 = true :=
  both_of_chunks 2 11 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_11_0
    · exact f_2_11_1
    · exact f_2_11_2
    · exact f_2_11_3
    · exact f_2_11_4
  )
private theorem f_2_12_0 : (chunkOf (Low6969Gate.gateList 2 12) 0).all (fFF 2 12) = true := by decide +kernel
private theorem f_2_12_1 : (chunkOf (Low6969Gate.gateList 2 12) 1).all (fFF 2 12) = true := by decide +kernel
private theorem f_2_12_2 : (chunkOf (Low6969Gate.gateList 2 12) 2).all (fFF 2 12) = true := by decide +kernel
private theorem f_2_12_3 : (chunkOf (Low6969Gate.gateList 2 12) 3).all (fFF 2 12) = true := by decide +kernel
private theorem f_2_12_4 : (chunkOf (Low6969Gate.gateList 2 12) 4).all (fFF 2 12) = true := by decide +kernel
theorem fb_2_12 : one 2 12 = true ∧ gtOne 2 12 = true :=
  both_of_chunks 2 12 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_12_0
    · exact f_2_12_1
    · exact f_2_12_2
    · exact f_2_12_3
    · exact f_2_12_4
  )
private theorem f_2_13_0 : (chunkOf (Low6969Gate.gateList 2 13) 0).all (fFF 2 13) = true := by decide +kernel
private theorem f_2_13_1 : (chunkOf (Low6969Gate.gateList 2 13) 1).all (fFF 2 13) = true := by decide +kernel
private theorem f_2_13_2 : (chunkOf (Low6969Gate.gateList 2 13) 2).all (fFF 2 13) = true := by decide +kernel
private theorem f_2_13_3 : (chunkOf (Low6969Gate.gateList 2 13) 3).all (fFF 2 13) = true := by decide +kernel
private theorem f_2_13_4 : (chunkOf (Low6969Gate.gateList 2 13) 4).all (fFF 2 13) = true := by decide +kernel
theorem fb_2_13 : one 2 13 = true ∧ gtOne 2 13 = true :=
  both_of_chunks 2 13 5 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_13_0
    · exact f_2_13_1
    · exact f_2_13_2
    · exact f_2_13_3
    · exact f_2_13_4
  )
private theorem f_2_14_0 : (chunkOf (Low6969Gate.gateList 2 14) 0).all (fFF 2 14) = true := by decide +kernel
private theorem f_2_14_1 : (chunkOf (Low6969Gate.gateList 2 14) 1).all (fFF 2 14) = true := by decide +kernel
private theorem f_2_14_2 : (chunkOf (Low6969Gate.gateList 2 14) 2).all (fFF 2 14) = true := by decide +kernel
private theorem f_2_14_3 : (chunkOf (Low6969Gate.gateList 2 14) 3).all (fFF 2 14) = true := by decide +kernel
private theorem f_2_14_4 : (chunkOf (Low6969Gate.gateList 2 14) 4).all (fFF 2 14) = true := by decide +kernel
private theorem f_2_14_5 : (chunkOf (Low6969Gate.gateList 2 14) 5).all (fFF 2 14) = true := by decide +kernel
theorem fb_2_14 : one 2 14 = true ∧ gtOne 2 14 = true :=
  both_of_chunks 2 14 6 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_2_14_0
    · exact f_2_14_1
    · exact f_2_14_2
    · exact f_2_14_3
    · exact f_2_14_4
    · exact f_2_14_5
  )
end Low6969GateFin
end Z6969Source2507

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck3
section Z6969Source2508
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_3_2_0 : (chunkOf (Low6969Gate.gateList 3 2) 0).all (fFF 3 2) = true := by decide +kernel
theorem fb_3_2 : one 3 2 = true ∧ gtOne 3 2 = true :=
  both_of_chunks 3 2 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_2_0
  )
private theorem f_3_3_0 : (chunkOf (Low6969Gate.gateList 3 3) 0).all (fFF 3 3) = true := by decide +kernel
theorem fb_3_3 : one 3 3 = true ∧ gtOne 3 3 = true :=
  both_of_chunks 3 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_3_0
  )
private theorem f_3_4_0 : (chunkOf (Low6969Gate.gateList 3 4) 0).all (fFF 3 4) = true := by decide +kernel
private theorem f_3_4_1 : (chunkOf (Low6969Gate.gateList 3 4) 1).all (fFF 3 4) = true := by decide +kernel
theorem fb_3_4 : one 3 4 = true ∧ gtOne 3 4 = true :=
  both_of_chunks 3 4 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_4_0
    · exact f_3_4_1
  )
private theorem f_3_5_0 : (chunkOf (Low6969Gate.gateList 3 5) 0).all (fFF 3 5) = true := by decide +kernel
private theorem f_3_5_1 : (chunkOf (Low6969Gate.gateList 3 5) 1).all (fFF 3 5) = true := by decide +kernel
theorem fb_3_5 : one 3 5 = true ∧ gtOne 3 5 = true :=
  both_of_chunks 3 5 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_5_0
    · exact f_3_5_1
  )
private theorem f_3_6_0 : (chunkOf (Low6969Gate.gateList 3 6) 0).all (fFF 3 6) = true := by decide +kernel
private theorem f_3_6_1 : (chunkOf (Low6969Gate.gateList 3 6) 1).all (fFF 3 6) = true := by decide +kernel
private theorem f_3_6_2 : (chunkOf (Low6969Gate.gateList 3 6) 2).all (fFF 3 6) = true := by decide +kernel
theorem fb_3_6 : one 3 6 = true ∧ gtOne 3 6 = true :=
  both_of_chunks 3 6 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_6_0
    · exact f_3_6_1
    · exact f_3_6_2
  )
private theorem f_3_7_0 : (chunkOf (Low6969Gate.gateList 3 7) 0).all (fFF 3 7) = true := by decide +kernel
private theorem f_3_7_1 : (chunkOf (Low6969Gate.gateList 3 7) 1).all (fFF 3 7) = true := by decide +kernel
private theorem f_3_7_2 : (chunkOf (Low6969Gate.gateList 3 7) 2).all (fFF 3 7) = true := by decide +kernel
theorem fb_3_7 : one 3 7 = true ∧ gtOne 3 7 = true :=
  both_of_chunks 3 7 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_7_0
    · exact f_3_7_1
    · exact f_3_7_2
  )
private theorem f_3_8_0 : (chunkOf (Low6969Gate.gateList 3 8) 0).all (fFF 3 8) = true := by decide +kernel
private theorem f_3_8_1 : (chunkOf (Low6969Gate.gateList 3 8) 1).all (fFF 3 8) = true := by decide +kernel
private theorem f_3_8_2 : (chunkOf (Low6969Gate.gateList 3 8) 2).all (fFF 3 8) = true := by decide +kernel
theorem fb_3_8 : one 3 8 = true ∧ gtOne 3 8 = true :=
  both_of_chunks 3 8 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_8_0
    · exact f_3_8_1
    · exact f_3_8_2
  )
private theorem f_3_9_0 : (chunkOf (Low6969Gate.gateList 3 9) 0).all (fFF 3 9) = true := by decide +kernel
private theorem f_3_9_1 : (chunkOf (Low6969Gate.gateList 3 9) 1).all (fFF 3 9) = true := by decide +kernel
private theorem f_3_9_2 : (chunkOf (Low6969Gate.gateList 3 9) 2).all (fFF 3 9) = true := by decide +kernel
theorem fb_3_9 : one 3 9 = true ∧ gtOne 3 9 = true :=
  both_of_chunks 3 9 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_9_0
    · exact f_3_9_1
    · exact f_3_9_2
  )
private theorem f_3_10_0 : (chunkOf (Low6969Gate.gateList 3 10) 0).all (fFF 3 10) = true := by decide +kernel
private theorem f_3_10_1 : (chunkOf (Low6969Gate.gateList 3 10) 1).all (fFF 3 10) = true := by decide +kernel
private theorem f_3_10_2 : (chunkOf (Low6969Gate.gateList 3 10) 2).all (fFF 3 10) = true := by decide +kernel
private theorem f_3_10_3 : (chunkOf (Low6969Gate.gateList 3 10) 3).all (fFF 3 10) = true := by decide +kernel
theorem fb_3_10 : one 3 10 = true ∧ gtOne 3 10 = true :=
  both_of_chunks 3 10 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_10_0
    · exact f_3_10_1
    · exact f_3_10_2
    · exact f_3_10_3
  )
private theorem f_3_11_0 : (chunkOf (Low6969Gate.gateList 3 11) 0).all (fFF 3 11) = true := by decide +kernel
private theorem f_3_11_1 : (chunkOf (Low6969Gate.gateList 3 11) 1).all (fFF 3 11) = true := by decide +kernel
private theorem f_3_11_2 : (chunkOf (Low6969Gate.gateList 3 11) 2).all (fFF 3 11) = true := by decide +kernel
private theorem f_3_11_3 : (chunkOf (Low6969Gate.gateList 3 11) 3).all (fFF 3 11) = true := by decide +kernel
theorem fb_3_11 : one 3 11 = true ∧ gtOne 3 11 = true :=
  both_of_chunks 3 11 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_11_0
    · exact f_3_11_1
    · exact f_3_11_2
    · exact f_3_11_3
  )
private theorem f_3_12_0 : (chunkOf (Low6969Gate.gateList 3 12) 0).all (fFF 3 12) = true := by decide +kernel
private theorem f_3_12_1 : (chunkOf (Low6969Gate.gateList 3 12) 1).all (fFF 3 12) = true := by decide +kernel
private theorem f_3_12_2 : (chunkOf (Low6969Gate.gateList 3 12) 2).all (fFF 3 12) = true := by decide +kernel
private theorem f_3_12_3 : (chunkOf (Low6969Gate.gateList 3 12) 3).all (fFF 3 12) = true := by decide +kernel
theorem fb_3_12 : one 3 12 = true ∧ gtOne 3 12 = true :=
  both_of_chunks 3 12 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_12_0
    · exact f_3_12_1
    · exact f_3_12_2
    · exact f_3_12_3
  )
private theorem f_3_13_0 : (chunkOf (Low6969Gate.gateList 3 13) 0).all (fFF 3 13) = true := by decide +kernel
private theorem f_3_13_1 : (chunkOf (Low6969Gate.gateList 3 13) 1).all (fFF 3 13) = true := by decide +kernel
private theorem f_3_13_2 : (chunkOf (Low6969Gate.gateList 3 13) 2).all (fFF 3 13) = true := by decide +kernel
private theorem f_3_13_3 : (chunkOf (Low6969Gate.gateList 3 13) 3).all (fFF 3 13) = true := by decide +kernel
theorem fb_3_13 : one 3 13 = true ∧ gtOne 3 13 = true :=
  both_of_chunks 3 13 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_13_0
    · exact f_3_13_1
    · exact f_3_13_2
    · exact f_3_13_3
  )
private theorem f_3_14_0 : (chunkOf (Low6969Gate.gateList 3 14) 0).all (fFF 3 14) = true := by decide +kernel
private theorem f_3_14_1 : (chunkOf (Low6969Gate.gateList 3 14) 1).all (fFF 3 14) = true := by decide +kernel
private theorem f_3_14_2 : (chunkOf (Low6969Gate.gateList 3 14) 2).all (fFF 3 14) = true := by decide +kernel
private theorem f_3_14_3 : (chunkOf (Low6969Gate.gateList 3 14) 3).all (fFF 3 14) = true := by decide +kernel
theorem fb_3_14 : one 3 14 = true ∧ gtOne 3 14 = true :=
  both_of_chunks 3 14 4 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_3_14_0
    · exact f_3_14_1
    · exact f_3_14_2
    · exact f_3_14_3
  )
end Low6969GateFin
end Z6969Source2508

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck4
section Z6969Source2509
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_4_3_0 : (chunkOf (Low6969Gate.gateList 4 3) 0).all (fFF 4 3) = true := by decide +kernel
theorem fb_4_3 : one 4 3 = true ∧ gtOne 4 3 = true :=
  both_of_chunks 4 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_3_0
  )
private theorem f_4_4_0 : (chunkOf (Low6969Gate.gateList 4 4) 0).all (fFF 4 4) = true := by decide +kernel
theorem fb_4_4 : one 4 4 = true ∧ gtOne 4 4 = true :=
  both_of_chunks 4 4 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_4_0
  )
private theorem f_4_5_0 : (chunkOf (Low6969Gate.gateList 4 5) 0).all (fFF 4 5) = true := by decide +kernel
theorem fb_4_5 : one 4 5 = true ∧ gtOne 4 5 = true :=
  both_of_chunks 4 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_5_0
  )
private theorem f_4_6_0 : (chunkOf (Low6969Gate.gateList 4 6) 0).all (fFF 4 6) = true := by decide +kernel
private theorem f_4_6_1 : (chunkOf (Low6969Gate.gateList 4 6) 1).all (fFF 4 6) = true := by decide +kernel
theorem fb_4_6 : one 4 6 = true ∧ gtOne 4 6 = true :=
  both_of_chunks 4 6 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_6_0
    · exact f_4_6_1
  )
private theorem f_4_7_0 : (chunkOf (Low6969Gate.gateList 4 7) 0).all (fFF 4 7) = true := by decide +kernel
private theorem f_4_7_1 : (chunkOf (Low6969Gate.gateList 4 7) 1).all (fFF 4 7) = true := by decide +kernel
theorem fb_4_7 : one 4 7 = true ∧ gtOne 4 7 = true :=
  both_of_chunks 4 7 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_7_0
    · exact f_4_7_1
  )
private theorem f_4_8_0 : (chunkOf (Low6969Gate.gateList 4 8) 0).all (fFF 4 8) = true := by decide +kernel
private theorem f_4_8_1 : (chunkOf (Low6969Gate.gateList 4 8) 1).all (fFF 4 8) = true := by decide +kernel
theorem fb_4_8 : one 4 8 = true ∧ gtOne 4 8 = true :=
  both_of_chunks 4 8 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_8_0
    · exact f_4_8_1
  )
private theorem f_4_9_0 : (chunkOf (Low6969Gate.gateList 4 9) 0).all (fFF 4 9) = true := by decide +kernel
private theorem f_4_9_1 : (chunkOf (Low6969Gate.gateList 4 9) 1).all (fFF 4 9) = true := by decide +kernel
private theorem f_4_9_2 : (chunkOf (Low6969Gate.gateList 4 9) 2).all (fFF 4 9) = true := by decide +kernel
theorem fb_4_9 : one 4 9 = true ∧ gtOne 4 9 = true :=
  both_of_chunks 4 9 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_9_0
    · exact f_4_9_1
    · exact f_4_9_2
  )
private theorem f_4_10_0 : (chunkOf (Low6969Gate.gateList 4 10) 0).all (fFF 4 10) = true := by decide +kernel
private theorem f_4_10_1 : (chunkOf (Low6969Gate.gateList 4 10) 1).all (fFF 4 10) = true := by decide +kernel
private theorem f_4_10_2 : (chunkOf (Low6969Gate.gateList 4 10) 2).all (fFF 4 10) = true := by decide +kernel
theorem fb_4_10 : one 4 10 = true ∧ gtOne 4 10 = true :=
  both_of_chunks 4 10 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_10_0
    · exact f_4_10_1
    · exact f_4_10_2
  )
private theorem f_4_11_0 : (chunkOf (Low6969Gate.gateList 4 11) 0).all (fFF 4 11) = true := by decide +kernel
private theorem f_4_11_1 : (chunkOf (Low6969Gate.gateList 4 11) 1).all (fFF 4 11) = true := by decide +kernel
private theorem f_4_11_2 : (chunkOf (Low6969Gate.gateList 4 11) 2).all (fFF 4 11) = true := by decide +kernel
theorem fb_4_11 : one 4 11 = true ∧ gtOne 4 11 = true :=
  both_of_chunks 4 11 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_11_0
    · exact f_4_11_1
    · exact f_4_11_2
  )
private theorem f_4_12_0 : (chunkOf (Low6969Gate.gateList 4 12) 0).all (fFF 4 12) = true := by decide +kernel
private theorem f_4_12_1 : (chunkOf (Low6969Gate.gateList 4 12) 1).all (fFF 4 12) = true := by decide +kernel
private theorem f_4_12_2 : (chunkOf (Low6969Gate.gateList 4 12) 2).all (fFF 4 12) = true := by decide +kernel
theorem fb_4_12 : one 4 12 = true ∧ gtOne 4 12 = true :=
  both_of_chunks 4 12 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_12_0
    · exact f_4_12_1
    · exact f_4_12_2
  )
private theorem f_4_13_0 : (chunkOf (Low6969Gate.gateList 4 13) 0).all (fFF 4 13) = true := by decide +kernel
private theorem f_4_13_1 : (chunkOf (Low6969Gate.gateList 4 13) 1).all (fFF 4 13) = true := by decide +kernel
private theorem f_4_13_2 : (chunkOf (Low6969Gate.gateList 4 13) 2).all (fFF 4 13) = true := by decide +kernel
theorem fb_4_13 : one 4 13 = true ∧ gtOne 4 13 = true :=
  both_of_chunks 4 13 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_13_0
    · exact f_4_13_1
    · exact f_4_13_2
  )
private theorem f_4_14_0 : (chunkOf (Low6969Gate.gateList 4 14) 0).all (fFF 4 14) = true := by decide +kernel
private theorem f_4_14_1 : (chunkOf (Low6969Gate.gateList 4 14) 1).all (fFF 4 14) = true := by decide +kernel
private theorem f_4_14_2 : (chunkOf (Low6969Gate.gateList 4 14) 2).all (fFF 4 14) = true := by decide +kernel
theorem fb_4_14 : one 4 14 = true ∧ gtOne 4 14 = true :=
  both_of_chunks 4 14 3 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_4_14_0
    · exact f_4_14_1
    · exact f_4_14_2
  )
end Low6969GateFin
end Z6969Source2509

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck5
section Z6969Source2510
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_5_3_0 : (chunkOf (Low6969Gate.gateList 5 3) 0).all (fFF 5 3) = true := by decide +kernel
theorem fb_5_3 : one 5 3 = true ∧ gtOne 5 3 = true :=
  both_of_chunks 5 3 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_3_0
  )
private theorem f_5_4_0 : (chunkOf (Low6969Gate.gateList 5 4) 0).all (fFF 5 4) = true := by decide +kernel
theorem fb_5_4 : one 5 4 = true ∧ gtOne 5 4 = true :=
  both_of_chunks 5 4 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_4_0
  )
private theorem f_5_5_0 : (chunkOf (Low6969Gate.gateList 5 5) 0).all (fFF 5 5) = true := by decide +kernel
theorem fb_5_5 : one 5 5 = true ∧ gtOne 5 5 = true :=
  both_of_chunks 5 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_5_0
  )
private theorem f_5_6_0 : (chunkOf (Low6969Gate.gateList 5 6) 0).all (fFF 5 6) = true := by decide +kernel
theorem fb_5_6 : one 5 6 = true ∧ gtOne 5 6 = true :=
  both_of_chunks 5 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_6_0
  )
private theorem f_5_7_0 : (chunkOf (Low6969Gate.gateList 5 7) 0).all (fFF 5 7) = true := by decide +kernel
private theorem f_5_7_1 : (chunkOf (Low6969Gate.gateList 5 7) 1).all (fFF 5 7) = true := by decide +kernel
theorem fb_5_7 : one 5 7 = true ∧ gtOne 5 7 = true :=
  both_of_chunks 5 7 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_7_0
    · exact f_5_7_1
  )
private theorem f_5_8_0 : (chunkOf (Low6969Gate.gateList 5 8) 0).all (fFF 5 8) = true := by decide +kernel
private theorem f_5_8_1 : (chunkOf (Low6969Gate.gateList 5 8) 1).all (fFF 5 8) = true := by decide +kernel
theorem fb_5_8 : one 5 8 = true ∧ gtOne 5 8 = true :=
  both_of_chunks 5 8 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_8_0
    · exact f_5_8_1
  )
private theorem f_5_9_0 : (chunkOf (Low6969Gate.gateList 5 9) 0).all (fFF 5 9) = true := by decide +kernel
private theorem f_5_9_1 : (chunkOf (Low6969Gate.gateList 5 9) 1).all (fFF 5 9) = true := by decide +kernel
theorem fb_5_9 : one 5 9 = true ∧ gtOne 5 9 = true :=
  both_of_chunks 5 9 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_9_0
    · exact f_5_9_1
  )
private theorem f_5_10_0 : (chunkOf (Low6969Gate.gateList 5 10) 0).all (fFF 5 10) = true := by decide +kernel
private theorem f_5_10_1 : (chunkOf (Low6969Gate.gateList 5 10) 1).all (fFF 5 10) = true := by decide +kernel
theorem fb_5_10 : one 5 10 = true ∧ gtOne 5 10 = true :=
  both_of_chunks 5 10 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_10_0
    · exact f_5_10_1
  )
private theorem f_5_11_0 : (chunkOf (Low6969Gate.gateList 5 11) 0).all (fFF 5 11) = true := by decide +kernel
private theorem f_5_11_1 : (chunkOf (Low6969Gate.gateList 5 11) 1).all (fFF 5 11) = true := by decide +kernel
theorem fb_5_11 : one 5 11 = true ∧ gtOne 5 11 = true :=
  both_of_chunks 5 11 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_11_0
    · exact f_5_11_1
  )
private theorem f_5_12_0 : (chunkOf (Low6969Gate.gateList 5 12) 0).all (fFF 5 12) = true := by decide +kernel
private theorem f_5_12_1 : (chunkOf (Low6969Gate.gateList 5 12) 1).all (fFF 5 12) = true := by decide +kernel
theorem fb_5_12 : one 5 12 = true ∧ gtOne 5 12 = true :=
  both_of_chunks 5 12 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_12_0
    · exact f_5_12_1
  )
private theorem f_5_13_0 : (chunkOf (Low6969Gate.gateList 5 13) 0).all (fFF 5 13) = true := by decide +kernel
private theorem f_5_13_1 : (chunkOf (Low6969Gate.gateList 5 13) 1).all (fFF 5 13) = true := by decide +kernel
theorem fb_5_13 : one 5 13 = true ∧ gtOne 5 13 = true :=
  both_of_chunks 5 13 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_13_0
    · exact f_5_13_1
  )
private theorem f_5_14_0 : (chunkOf (Low6969Gate.gateList 5 14) 0).all (fFF 5 14) = true := by decide +kernel
private theorem f_5_14_1 : (chunkOf (Low6969Gate.gateList 5 14) 1).all (fFF 5 14) = true := by decide +kernel
theorem fb_5_14 : one 5 14 = true ∧ gtOne 5 14 = true :=
  both_of_chunks 5 14 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_5_14_0
    · exact f_5_14_1
  )
end Low6969GateFin
end Z6969Source2510

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck6
section Z6969Source2511
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_6_4_0 : (chunkOf (Low6969Gate.gateList 6 4) 0).all (fFF 6 4) = true := by decide +kernel
theorem fb_6_4 : one 6 4 = true ∧ gtOne 6 4 = true :=
  both_of_chunks 6 4 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_4_0
  )
private theorem f_6_5_0 : (chunkOf (Low6969Gate.gateList 6 5) 0).all (fFF 6 5) = true := by decide +kernel
theorem fb_6_5 : one 6 5 = true ∧ gtOne 6 5 = true :=
  both_of_chunks 6 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_5_0
  )
private theorem f_6_6_0 : (chunkOf (Low6969Gate.gateList 6 6) 0).all (fFF 6 6) = true := by decide +kernel
theorem fb_6_6 : one 6 6 = true ∧ gtOne 6 6 = true :=
  both_of_chunks 6 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_6_0
  )
private theorem f_6_7_0 : (chunkOf (Low6969Gate.gateList 6 7) 0).all (fFF 6 7) = true := by decide +kernel
theorem fb_6_7 : one 6 7 = true ∧ gtOne 6 7 = true :=
  both_of_chunks 6 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_7_0
  )
private theorem f_6_8_0 : (chunkOf (Low6969Gate.gateList 6 8) 0).all (fFF 6 8) = true := by decide +kernel
theorem fb_6_8 : one 6 8 = true ∧ gtOne 6 8 = true :=
  both_of_chunks 6 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_8_0
  )
private theorem f_6_9_0 : (chunkOf (Low6969Gate.gateList 6 9) 0).all (fFF 6 9) = true := by decide +kernel
private theorem f_6_9_1 : (chunkOf (Low6969Gate.gateList 6 9) 1).all (fFF 6 9) = true := by decide +kernel
theorem fb_6_9 : one 6 9 = true ∧ gtOne 6 9 = true :=
  both_of_chunks 6 9 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_9_0
    · exact f_6_9_1
  )
private theorem f_6_10_0 : (chunkOf (Low6969Gate.gateList 6 10) 0).all (fFF 6 10) = true := by decide +kernel
private theorem f_6_10_1 : (chunkOf (Low6969Gate.gateList 6 10) 1).all (fFF 6 10) = true := by decide +kernel
theorem fb_6_10 : one 6 10 = true ∧ gtOne 6 10 = true :=
  both_of_chunks 6 10 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_10_0
    · exact f_6_10_1
  )
private theorem f_6_11_0 : (chunkOf (Low6969Gate.gateList 6 11) 0).all (fFF 6 11) = true := by decide +kernel
private theorem f_6_11_1 : (chunkOf (Low6969Gate.gateList 6 11) 1).all (fFF 6 11) = true := by decide +kernel
theorem fb_6_11 : one 6 11 = true ∧ gtOne 6 11 = true :=
  both_of_chunks 6 11 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_11_0
    · exact f_6_11_1
  )
private theorem f_6_12_0 : (chunkOf (Low6969Gate.gateList 6 12) 0).all (fFF 6 12) = true := by decide +kernel
private theorem f_6_12_1 : (chunkOf (Low6969Gate.gateList 6 12) 1).all (fFF 6 12) = true := by decide +kernel
theorem fb_6_12 : one 6 12 = true ∧ gtOne 6 12 = true :=
  both_of_chunks 6 12 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_12_0
    · exact f_6_12_1
  )
private theorem f_6_13_0 : (chunkOf (Low6969Gate.gateList 6 13) 0).all (fFF 6 13) = true := by decide +kernel
private theorem f_6_13_1 : (chunkOf (Low6969Gate.gateList 6 13) 1).all (fFF 6 13) = true := by decide +kernel
theorem fb_6_13 : one 6 13 = true ∧ gtOne 6 13 = true :=
  both_of_chunks 6 13 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_13_0
    · exact f_6_13_1
  )
private theorem f_6_14_0 : (chunkOf (Low6969Gate.gateList 6 14) 0).all (fFF 6 14) = true := by decide +kernel
private theorem f_6_14_1 : (chunkOf (Low6969Gate.gateList 6 14) 1).all (fFF 6 14) = true := by decide +kernel
theorem fb_6_14 : one 6 14 = true ∧ gtOne 6 14 = true :=
  both_of_chunks 6 14 2 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_6_14_0
    · exact f_6_14_1
  )
end Low6969GateFin
end Z6969Source2511

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck7
section Z6969Source2512
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_7_5_0 : (chunkOf (Low6969Gate.gateList 7 5) 0).all (fFF 7 5) = true := by decide +kernel
theorem fb_7_5 : one 7 5 = true ∧ gtOne 7 5 = true :=
  both_of_chunks 7 5 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_5_0
  )
private theorem f_7_6_0 : (chunkOf (Low6969Gate.gateList 7 6) 0).all (fFF 7 6) = true := by decide +kernel
theorem fb_7_6 : one 7 6 = true ∧ gtOne 7 6 = true :=
  both_of_chunks 7 6 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_6_0
  )
private theorem f_7_7_0 : (chunkOf (Low6969Gate.gateList 7 7) 0).all (fFF 7 7) = true := by decide +kernel
theorem fb_7_7 : one 7 7 = true ∧ gtOne 7 7 = true :=
  both_of_chunks 7 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_7_0
  )
private theorem f_7_8_0 : (chunkOf (Low6969Gate.gateList 7 8) 0).all (fFF 7 8) = true := by decide +kernel
theorem fb_7_8 : one 7 8 = true ∧ gtOne 7 8 = true :=
  both_of_chunks 7 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_8_0
  )
private theorem f_7_9_0 : (chunkOf (Low6969Gate.gateList 7 9) 0).all (fFF 7 9) = true := by decide +kernel
theorem fb_7_9 : one 7 9 = true ∧ gtOne 7 9 = true :=
  both_of_chunks 7 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_9_0
  )
private theorem f_7_10_0 : (chunkOf (Low6969Gate.gateList 7 10) 0).all (fFF 7 10) = true := by decide +kernel
theorem fb_7_10 : one 7 10 = true ∧ gtOne 7 10 = true :=
  both_of_chunks 7 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_10_0
  )
private theorem f_7_11_0 : (chunkOf (Low6969Gate.gateList 7 11) 0).all (fFF 7 11) = true := by decide +kernel
theorem fb_7_11 : one 7 11 = true ∧ gtOne 7 11 = true :=
  both_of_chunks 7 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_11_0
  )
private theorem f_7_12_0 : (chunkOf (Low6969Gate.gateList 7 12) 0).all (fFF 7 12) = true := by decide +kernel
theorem fb_7_12 : one 7 12 = true ∧ gtOne 7 12 = true :=
  both_of_chunks 7 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_12_0
  )
private theorem f_7_13_0 : (chunkOf (Low6969Gate.gateList 7 13) 0).all (fFF 7 13) = true := by decide +kernel
theorem fb_7_13 : one 7 13 = true ∧ gtOne 7 13 = true :=
  both_of_chunks 7 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_13_0
  )
private theorem f_7_14_0 : (chunkOf (Low6969Gate.gateList 7 14) 0).all (fFF 7 14) = true := by decide +kernel
theorem fb_7_14 : one 7 14 = true ∧ gtOne 7 14 = true :=
  both_of_chunks 7 14 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_7_14_0
  )
end Low6969GateFin
end Z6969Source2512

end Merged_Z6969Pack0919

-- merged module Z6969Pack0920
section Merged_Z6969Pack0920

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck8
section Z6969Source2513
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_8_7_0 : (chunkOf (Low6969Gate.gateList 8 7) 0).all (fFF 8 7) = true := by decide +kernel
theorem fb_8_7 : one 8 7 = true ∧ gtOne 8 7 = true :=
  both_of_chunks 8 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_7_0
  )
private theorem f_8_8_0 : (chunkOf (Low6969Gate.gateList 8 8) 0).all (fFF 8 8) = true := by decide +kernel
theorem fb_8_8 : one 8 8 = true ∧ gtOne 8 8 = true :=
  both_of_chunks 8 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_8_0
  )
private theorem f_8_9_0 : (chunkOf (Low6969Gate.gateList 8 9) 0).all (fFF 8 9) = true := by decide +kernel
theorem fb_8_9 : one 8 9 = true ∧ gtOne 8 9 = true :=
  both_of_chunks 8 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_9_0
  )
private theorem f_8_10_0 : (chunkOf (Low6969Gate.gateList 8 10) 0).all (fFF 8 10) = true := by decide +kernel
theorem fb_8_10 : one 8 10 = true ∧ gtOne 8 10 = true :=
  both_of_chunks 8 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_10_0
  )
private theorem f_8_11_0 : (chunkOf (Low6969Gate.gateList 8 11) 0).all (fFF 8 11) = true := by decide +kernel
theorem fb_8_11 : one 8 11 = true ∧ gtOne 8 11 = true :=
  both_of_chunks 8 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_11_0
  )
private theorem f_8_12_0 : (chunkOf (Low6969Gate.gateList 8 12) 0).all (fFF 8 12) = true := by decide +kernel
theorem fb_8_12 : one 8 12 = true ∧ gtOne 8 12 = true :=
  both_of_chunks 8 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_12_0
  )
private theorem f_8_13_0 : (chunkOf (Low6969Gate.gateList 8 13) 0).all (fFF 8 13) = true := by decide +kernel
theorem fb_8_13 : one 8 13 = true ∧ gtOne 8 13 = true :=
  both_of_chunks 8 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_13_0
  )
private theorem f_8_14_0 : (chunkOf (Low6969Gate.gateList 8 14) 0).all (fFF 8 14) = true := by decide +kernel
theorem fb_8_14 : one 8 14 = true ∧ gtOne 8 14 = true :=
  both_of_chunks 8 14 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_8_14_0
  )
end Low6969GateFin
end Z6969Source2513

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck9
section Z6969Source2514
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_9_10_0 : (chunkOf (Low6969Gate.gateList 9 10) 0).all (fFF 9 10) = true := by decide +kernel
theorem fb_9_10 : one 9 10 = true ∧ gtOne 9 10 = true :=
  both_of_chunks 9 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_10_0
  )
private theorem f_9_11_0 : (chunkOf (Low6969Gate.gateList 9 11) 0).all (fFF 9 11) = true := by decide +kernel
theorem fb_9_11 : one 9 11 = true ∧ gtOne 9 11 = true :=
  both_of_chunks 9 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_11_0
  )
private theorem f_9_12_0 : (chunkOf (Low6969Gate.gateList 9 12) 0).all (fFF 9 12) = true := by decide +kernel
theorem fb_9_12 : one 9 12 = true ∧ gtOne 9 12 = true :=
  both_of_chunks 9 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_12_0
  )
private theorem f_9_13_0 : (chunkOf (Low6969Gate.gateList 9 13) 0).all (fFF 9 13) = true := by decide +kernel
theorem fb_9_13 : one 9 13 = true ∧ gtOne 9 13 = true :=
  both_of_chunks 9 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_13_0
  )
private theorem f_9_14_0 : (chunkOf (Low6969Gate.gateList 9 14) 0).all (fFF 9 14) = true := by decide +kernel
theorem fb_9_14 : one 9 14 = true ∧ gtOne 9 14 = true :=
  both_of_chunks 9 14 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_9_14_0
  )
end Low6969GateFin
end Z6969Source2514

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck10
section Z6969Source2515
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_10_7_0 : (chunkOf (Low6969Gate.gateList 10 7) 0).all (fFF 10 7) = true := by decide +kernel
theorem fb_10_7 : one 10 7 = true ∧ gtOne 10 7 = true :=
  both_of_chunks 10 7 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_7_0
  )
private theorem f_10_8_0 : (chunkOf (Low6969Gate.gateList 10 8) 0).all (fFF 10 8) = true := by decide +kernel
theorem fb_10_8 : one 10 8 = true ∧ gtOne 10 8 = true :=
  both_of_chunks 10 8 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_8_0
  )
private theorem f_10_9_0 : (chunkOf (Low6969Gate.gateList 10 9) 0).all (fFF 10 9) = true := by decide +kernel
theorem fb_10_9 : one 10 9 = true ∧ gtOne 10 9 = true :=
  both_of_chunks 10 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_9_0
  )
private theorem f_10_10_0 : (chunkOf (Low6969Gate.gateList 10 10) 0).all (fFF 10 10) = true := by decide +kernel
theorem fb_10_10 : one 10 10 = true ∧ gtOne 10 10 = true :=
  both_of_chunks 10 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_10_0
  )
private theorem f_10_11_0 : (chunkOf (Low6969Gate.gateList 10 11) 0).all (fFF 10 11) = true := by decide +kernel
theorem fb_10_11 : one 10 11 = true ∧ gtOne 10 11 = true :=
  both_of_chunks 10 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_11_0
  )
private theorem f_10_12_0 : (chunkOf (Low6969Gate.gateList 10 12) 0).all (fFF 10 12) = true := by decide +kernel
theorem fb_10_12 : one 10 12 = true ∧ gtOne 10 12 = true :=
  both_of_chunks 10 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_12_0
  )
private theorem f_10_13_0 : (chunkOf (Low6969Gate.gateList 10 13) 0).all (fFF 10 13) = true := by decide +kernel
theorem fb_10_13 : one 10 13 = true ∧ gtOne 10 13 = true :=
  both_of_chunks 10 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_13_0
  )
private theorem f_10_14_0 : (chunkOf (Low6969Gate.gateList 10 14) 0).all (fFF 10 14) = true := by decide +kernel
theorem fb_10_14 : one 10 14 = true ∧ gtOne 10 14 = true :=
  both_of_chunks 10 14 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_10_14_0
  )
end Low6969GateFin
end Z6969Source2515

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck11
section Z6969Source2516
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_11_9_0 : (chunkOf (Low6969Gate.gateList 11 9) 0).all (fFF 11 9) = true := by decide +kernel
theorem fb_11_9 : one 11 9 = true ∧ gtOne 11 9 = true :=
  both_of_chunks 11 9 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_9_0
  )
private theorem f_11_10_0 : (chunkOf (Low6969Gate.gateList 11 10) 0).all (fFF 11 10) = true := by decide +kernel
theorem fb_11_10 : one 11 10 = true ∧ gtOne 11 10 = true :=
  both_of_chunks 11 10 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_10_0
  )
private theorem f_11_11_0 : (chunkOf (Low6969Gate.gateList 11 11) 0).all (fFF 11 11) = true := by decide +kernel
theorem fb_11_11 : one 11 11 = true ∧ gtOne 11 11 = true :=
  both_of_chunks 11 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_11_0
  )
private theorem f_11_12_0 : (chunkOf (Low6969Gate.gateList 11 12) 0).all (fFF 11 12) = true := by decide +kernel
theorem fb_11_12 : one 11 12 = true ∧ gtOne 11 12 = true :=
  both_of_chunks 11 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_12_0
  )
private theorem f_11_13_0 : (chunkOf (Low6969Gate.gateList 11 13) 0).all (fFF 11 13) = true := by decide +kernel
theorem fb_11_13 : one 11 13 = true ∧ gtOne 11 13 = true :=
  both_of_chunks 11 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_13_0
  )
private theorem f_11_14_0 : (chunkOf (Low6969Gate.gateList 11 14) 0).all (fFF 11 14) = true := by decide +kernel
theorem fb_11_14 : one 11 14 = true ∧ gtOne 11 14 = true :=
  both_of_chunks 11 14 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_11_14_0
  )
end Low6969GateFin
end Z6969Source2516

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck12
section Z6969Source2517
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_12_13_0 : (chunkOf (Low6969Gate.gateList 12 13) 0).all (fFF 12 13) = true := by decide +kernel
theorem fb_12_13 : one 12 13 = true ∧ gtOne 12 13 = true :=
  both_of_chunks 12 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_12_13_0
  )
end Low6969GateFin
end Z6969Source2517

-- Source: ProximityPrize.SubmissionLower.Low6969GateCheck13
section Z6969Source2518
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
private theorem f_13_11_0 : (chunkOf (Low6969Gate.gateList 13 11) 0).all (fFF 13 11) = true := by decide +kernel
theorem fb_13_11 : one 13 11 = true ∧ gtOne 13 11 = true :=
  both_of_chunks 13 11 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_13_11_0
  )
private theorem f_13_12_0 : (chunkOf (Low6969Gate.gateList 13 12) 0).all (fFF 13 12) = true := by decide +kernel
theorem fb_13_12 : one 13 12 = true ∧ gtOne 13 12 = true :=
  both_of_chunks 13 12 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_13_12_0
  )
private theorem f_13_13_0 : (chunkOf (Low6969Gate.gateList 13 13) 0).all (fFF 13 13) = true := by decide +kernel
theorem fb_13_13 : one 13 13 = true ∧ gtOne 13 13 = true :=
  both_of_chunks 13 13 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_13_13_0
  )
private theorem f_13_14_0 : (chunkOf (Low6969Gate.gateList 13 14) 0).all (fFF 13 14) = true := by decide +kernel
theorem fb_13_14 : one 13 14 = true ∧ gtOne 13 14 = true :=
  both_of_chunks 13 14 1 (by decide +kernel) (fun i hi => by
    interval_cases i
    · exact f_13_14_0
  )
end Low6969GateFin
end Z6969Source2518

-- Source: ProximityPrize.SubmissionLower.Low6969GateTable
section Z6969Source2519
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Low6969GateFin
open K1_13 (Shape shape)
open Low6969Allocation

theorem allOne (id : ℕ) (hi : id < 14) (t : ℕ) (ht : t < 16) : one id t = true := by
  interval_cases id
  · interval_cases t
    · rfl
    · rfl
    · exact fb_0_2.1
    · exact fb_0_3.1
    · exact fb_0_4.1
    · exact fb_0_5.1
    · exact fb_0_6.1
    · exact fb_0_7.1
    · exact fb_0_8.1
    · exact fb_0_9.1
    · exact fb_0_10.1
    · exact fb_0_11.1
    · exact fb_0_12.1
    · exact fb_0_13.1
    · exact fb_0_14.1
    · exact fb_0_15.1
  · interval_cases t
    · rfl
    · rfl
    · exact fb_1_2.1
    · exact fb_1_3.1
    · exact fb_1_4.1
    · exact fb_1_5.1
    · exact fb_1_6.1
    · exact fb_1_7.1
    · exact fb_1_8.1
    · exact fb_1_9.1
    · exact fb_1_10.1
    · exact fb_1_11.1
    · exact fb_1_12.1
    · exact fb_1_13.1
    · exact fb_1_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · exact fb_2_2.1
    · exact fb_2_3.1
    · exact fb_2_4.1
    · exact fb_2_5.1
    · exact fb_2_6.1
    · exact fb_2_7.1
    · exact fb_2_8.1
    · exact fb_2_9.1
    · exact fb_2_10.1
    · exact fb_2_11.1
    · exact fb_2_12.1
    · exact fb_2_13.1
    · exact fb_2_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · exact fb_3_2.1
    · exact fb_3_3.1
    · exact fb_3_4.1
    · exact fb_3_5.1
    · exact fb_3_6.1
    · exact fb_3_7.1
    · exact fb_3_8.1
    · exact fb_3_9.1
    · exact fb_3_10.1
    · exact fb_3_11.1
    · exact fb_3_12.1
    · exact fb_3_13.1
    · exact fb_3_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · exact fb_4_3.1
    · exact fb_4_4.1
    · exact fb_4_5.1
    · exact fb_4_6.1
    · exact fb_4_7.1
    · exact fb_4_8.1
    · exact fb_4_9.1
    · exact fb_4_10.1
    · exact fb_4_11.1
    · exact fb_4_12.1
    · exact fb_4_13.1
    · exact fb_4_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · exact fb_5_3.1
    · exact fb_5_4.1
    · exact fb_5_5.1
    · exact fb_5_6.1
    · exact fb_5_7.1
    · exact fb_5_8.1
    · exact fb_5_9.1
    · exact fb_5_10.1
    · exact fb_5_11.1
    · exact fb_5_12.1
    · exact fb_5_13.1
    · exact fb_5_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_6_4.1
    · exact fb_6_5.1
    · exact fb_6_6.1
    · exact fb_6_7.1
    · exact fb_6_8.1
    · exact fb_6_9.1
    · exact fb_6_10.1
    · exact fb_6_11.1
    · exact fb_6_12.1
    · exact fb_6_13.1
    · exact fb_6_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_7_5.1
    · exact fb_7_6.1
    · exact fb_7_7.1
    · exact fb_7_8.1
    · exact fb_7_9.1
    · exact fb_7_10.1
    · exact fb_7_11.1
    · exact fb_7_12.1
    · exact fb_7_13.1
    · exact fb_7_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_8_7.1
    · exact fb_8_8.1
    · exact fb_8_9.1
    · exact fb_8_10.1
    · exact fb_8_11.1
    · exact fb_8_12.1
    · exact fb_8_13.1
    · exact fb_8_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_9_10.1
    · exact fb_9_11.1
    · exact fb_9_12.1
    · exact fb_9_13.1
    · exact fb_9_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_10_7.1
    · exact fb_10_8.1
    · exact fb_10_9.1
    · exact fb_10_10.1
    · exact fb_10_11.1
    · exact fb_10_12.1
    · exact fb_10_13.1
    · exact fb_10_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_11_9.1
    · exact fb_11_10.1
    · exact fb_11_11.1
    · exact fb_11_12.1
    · exact fb_11_13.1
    · exact fb_11_14.1
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_12_13.1
    · rfl
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_13_11.1
    · exact fb_13_12.1
    · exact fb_13_13.1
    · exact fb_13_14.1
    · rfl

theorem allGt (id : ℕ) (hi : id < 14) (t : ℕ) (ht : t < 16) : gtOne id t = true := by
  interval_cases id
  · interval_cases t
    · rfl
    · rfl
    · exact fb_0_2.2
    · exact fb_0_3.2
    · exact fb_0_4.2
    · exact fb_0_5.2
    · exact fb_0_6.2
    · exact fb_0_7.2
    · exact fb_0_8.2
    · exact fb_0_9.2
    · exact fb_0_10.2
    · exact fb_0_11.2
    · exact fb_0_12.2
    · exact fb_0_13.2
    · exact fb_0_14.2
    · exact fb_0_15.2
  · interval_cases t
    · rfl
    · rfl
    · exact fb_1_2.2
    · exact fb_1_3.2
    · exact fb_1_4.2
    · exact fb_1_5.2
    · exact fb_1_6.2
    · exact fb_1_7.2
    · exact fb_1_8.2
    · exact fb_1_9.2
    · exact fb_1_10.2
    · exact fb_1_11.2
    · exact fb_1_12.2
    · exact fb_1_13.2
    · exact fb_1_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · exact fb_2_2.2
    · exact fb_2_3.2
    · exact fb_2_4.2
    · exact fb_2_5.2
    · exact fb_2_6.2
    · exact fb_2_7.2
    · exact fb_2_8.2
    · exact fb_2_9.2
    · exact fb_2_10.2
    · exact fb_2_11.2
    · exact fb_2_12.2
    · exact fb_2_13.2
    · exact fb_2_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · exact fb_3_2.2
    · exact fb_3_3.2
    · exact fb_3_4.2
    · exact fb_3_5.2
    · exact fb_3_6.2
    · exact fb_3_7.2
    · exact fb_3_8.2
    · exact fb_3_9.2
    · exact fb_3_10.2
    · exact fb_3_11.2
    · exact fb_3_12.2
    · exact fb_3_13.2
    · exact fb_3_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · exact fb_4_3.2
    · exact fb_4_4.2
    · exact fb_4_5.2
    · exact fb_4_6.2
    · exact fb_4_7.2
    · exact fb_4_8.2
    · exact fb_4_9.2
    · exact fb_4_10.2
    · exact fb_4_11.2
    · exact fb_4_12.2
    · exact fb_4_13.2
    · exact fb_4_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · exact fb_5_3.2
    · exact fb_5_4.2
    · exact fb_5_5.2
    · exact fb_5_6.2
    · exact fb_5_7.2
    · exact fb_5_8.2
    · exact fb_5_9.2
    · exact fb_5_10.2
    · exact fb_5_11.2
    · exact fb_5_12.2
    · exact fb_5_13.2
    · exact fb_5_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_6_4.2
    · exact fb_6_5.2
    · exact fb_6_6.2
    · exact fb_6_7.2
    · exact fb_6_8.2
    · exact fb_6_9.2
    · exact fb_6_10.2
    · exact fb_6_11.2
    · exact fb_6_12.2
    · exact fb_6_13.2
    · exact fb_6_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_7_5.2
    · exact fb_7_6.2
    · exact fb_7_7.2
    · exact fb_7_8.2
    · exact fb_7_9.2
    · exact fb_7_10.2
    · exact fb_7_11.2
    · exact fb_7_12.2
    · exact fb_7_13.2
    · exact fb_7_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_8_7.2
    · exact fb_8_8.2
    · exact fb_8_9.2
    · exact fb_8_10.2
    · exact fb_8_11.2
    · exact fb_8_12.2
    · exact fb_8_13.2
    · exact fb_8_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_9_10.2
    · exact fb_9_11.2
    · exact fb_9_12.2
    · exact fb_9_13.2
    · exact fb_9_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_10_7.2
    · exact fb_10_8.2
    · exact fb_10_9.2
    · exact fb_10_10.2
    · exact fb_10_11.2
    · exact fb_10_12.2
    · exact fb_10_13.2
    · exact fb_10_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_11_9.2
    · exact fb_11_10.2
    · exact fb_11_11.2
    · exact fb_11_12.2
    · exact fb_11_13.2
    · exact fb_11_14.2
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_12_13.2
    · rfl
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact fb_13_11.2
    · exact fb_13_12.2
    · exact fb_13_13.2
    · exact fb_13_14.2
    · rfl

theorem gated_ok {id : ℕ} {x : Shape} (h : Low6969Gate.Gated id x) (hv : valid x = true) : shapeOK x = true := by
  obtain ⟨hid, hm⟩ := h
  have ht : x.t < 16 := by
    by_contra hc
    rw [gl_nil id x.t (by omega)] at hm
    simp at hm
  have := allOne id hid x.t ht
  have := List.all_eq_true.mp this (x.b, x.j) hm
  simpa [hv] using this

theorem gateTable : GateTable bandOrders Gfun := by
  intro k x _ _ hg
  obtain ⟨hid, hm⟩ := hg
  have ht : x.t < 16 := by
    by_contra hc
    rw [gl_nil k.val x.t (by omega)] at hm
    simp at hm
  have h := List.all_eq_true.mp (allGt k.val hid x.t ht) (x.b, x.j) hm
  have hk : (⟨k.val % 40, Nat.mod_lt _ (by decide)⟩ : Band) = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  rw [hk] at h
  exact ⟨_, h.1, le_rfl, h.2⟩

theorem index_le (P : K1_13.Row 4) : K1_13.indexDegree P ≤ 2 * P.totalDegree + P.degreeOf 3 := by
  unfold K1_13.indexDegree
  apply Finset.sup_le
  intro m hm
  have h1 : (m.sum fun _ e => e) ≤ P.totalDegree := MvPolynomial.le_totalDegree hm
  have h2 : m 3 ≤ P.degreeOf 3 := MvPolynomial.monomial_le_degreeOf 3 hm
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
  rw [Finsupp.sum_fintype _ _ (fun _ => Nat.mul_zero _)]
  simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue] at h1 ⊢
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [h3]
  omega

theorem gateBank : Low6969RetainedCut.GateBank Gfun := by
  intro w Γ s n D hm f hf hdiff z hz i hi l active hl0 hl hact hchar Δ hΔ hon hoff id hbox hgated
  obtain ⟨Q, h1, h2, h3, h4, h5⟩ := D.proper_cut (hf i) hchar hl0 hl
  have hv : valid (shape (f i)) = true := by
    have := index_le (f i)
    simp only [valid, shape, Nat.ble_eq]
    exact this
  have := gated_price (Low6969Prices.Messages.mono hm hΔ) (hf i) hon hl0
    ⟨Q, h1, h2, h3, h4, fun γ hγ => h5 γ (hΔ hγ)⟩ hchar (gated_ok hgated hv)
  unfold Low6969Gate.gatePrice
  omega

theorem gates : Low6969Allocation.Gates := ⟨Gfun, gateBank, gateTable⟩

end Low6969GateFin
end Z6969Source2519

-- Source: ProximityPrize.SubmissionLower.Low6969Endpoint
section Z6969Source2520
set_option autoImplicit true
set_option Elab.async false

theorem LowProfile6969.low_6969 : Front6969.c6 :=
  LowProfile6969.low_of_gates Low6969GateFin.gates

end Z6969Source2520

end Merged_Z6969Pack0920
