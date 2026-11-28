import ProximityPrize.SubmissionLower.Z6969Pack0859

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 50000

namespace Low6969GateCount2
noncomputable section

open P3 (K)
open K1_13 (Row shape)
open K1_13_6 (GeoJets)
open Low6969Prices (Messages SmallFactor ActiveFits ProperCut)
open Low6969GeometryCut (CutInput)
open Low6969SharedTally (Data)
open Low6969SharedTallyNew (tally)
open Low6969SharedPersistent (Persistent)
open scoped Polynomial BigOperators

theorem count₂_precise {w : P3.I → K} {Γ : Finset K} {s : K → (Polynomial K)}
    (hm : Messages w Γ s) (f : Row 4) (hf : SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (l : ℕ) (hl : 0 < l) (hproper : ProperCut f Γ s l)
    (A : ℕ)
    (hmarks : ∀ (Q : Row 4) (input : CutInput Γ s f Q l)
      (data : Data Γ s f Q l {P | Persistent Γ s P}), tally data data.branches ≤ A) :
    Γ.card ≤ A + Low6969SharedPrice.additiveBase (shape f) l + Low6969SharedThirdCut.preciseFee (shape f) l := by
  classical
  obtain ⟨Q, hQprop, hbox, hweight, hQ, hcontact⟩ := hproper
  have input : CutInput Γ s f Q l :=
    ⟨hm.distinct, hm.degree, hf, hon, hl, hQprop, hbox, hweight, hcontact⟩
  let data : Data Γ s f Q l {P | Persistent Γ s P} := Low6969SharedTally.build _
  obtain ⟨a, c, d, hCard, ha, hc, hd⟩ := Low6969SharedCount.cover_counts_precise hm input data
  have hG := hmarks Q input data
  have hbase := Low6969SharedTallyOld.additive_le hl ha hc hd
  omega

end
end Low6969GateCount2

namespace Low6969GateFinal
noncomputable section

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
variable {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}

theorem two_cut_price_tilted_precise {w : P3.I → K} (hm : Low6969Prices.Messages w Γ s) (hceil : ExpandedOrderH2307.layerWidth * (Low6969Prices.layerNeed-1) < ExpandedOrderH2307.sourceRank) (hf : Low6969Prices.SmallFactor f)
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
    Γ.card ≤ A + Low6969SharedPrice.additiveBase (shape f) l + Low6969SharedThirdCut.preciseFee (shape f) l := by
  classical
  unfold levelCount at hW hsum
  refine Low6969GateCount2.count₂_precise hm f hf hon l hl hproper A ?_
  intro Q' input' data'
  set S := data'.branches.image Branch.surface with hSdef
  have hpers : ∀ P ∈ S, Persistent Γ s P := by
    intro P hP
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
    exact data'.allowed b hb
  have hneed := Low6969SharedShapeRank.bank_layers hm hceil S hpers
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

end
end Low6969GateFinal

namespace Low6969GateCell
noncomputable section

open Low6969GateFreeCard (mx mn mx_eq mn_eq)
open K1_13 (Row Shape shape InBox)
open Low6969GateBilinear (tpOf TP)
open Low6969SharedPrice (coord)
open K1_13 (Shape)
open Low6969GateBilinear (TP tpOf)
open P3 (K)
open K1_13 (Row Shape shape InBox)
open Low6969GateBilinear (tpOf)
open Low6969GateFreeCard (mx)
open Low6969SharedPrice (coord)
open Low6969GateCertCF (cvOf cvOf_le certF certF_bounds certF_class)
open scoped Polynomial BigOperators

theorem rhs_le_tilted_exact (f : Row 4) (G : Gt) (hG : G.Ok) (hlift : G.lift = false) (hsc : G.sc = 1920)
    (hxt : 3 * G.xt ≤ G.xj) (hbh : G.xj + 1 ≤ G.xb) (hjh : 2 ≤ G.xj)
    (hlo : G.lb ≤ (shape f).b ∧ G.lj ≤ (shape f).j ∧ G.lt ≤ (shape f).t)
    (hhi : (shape f).b ≤ G.xb ∧ (shape f).j ≤ G.xj ∧ (shape f).t ≤ G.xt)
    (htf : 3 * (shape f).t + 3 ≤ (shape f).j ∧ (shape f).j + 1 ≤ (shape f).b)
    (k k0 h1 h2 hx1 hx2 : ℕ) (hk : Low6969Prices.taylorLength - 4 = k)
    (hh1 : (Low6969Prices.bentLift k0 ⟨G.xb, G.xj, G.xt⟩).2 = h1)
    (hh2 : (Low6969Prices.bentLift (k0+1) ⟨G.xb, G.xj, G.xt⟩).2 = h2)
    (hx1' : (Low6969Prices.bentLift k (shape f)).2 = hx1) (hx2' : (Low6969Prices.bentLift (k + 1) (shape f)).2 = hx2)
    (hM : ∀ i k', (tpOf ⟨G.xb, G.xj, G.xt⟩ k0 h1 h2).ray i k' = Gt.mat G i k')
    (num den Ax : ℕ) (hden : 0 < den)
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (tpOf (shape f) k hx1 hx2).ray i k' ≤ num * (tpOf ⟨G.xb, G.xj, G.xt⟩ k0 h1 h2).ray i k')
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
    tilted_le_saved_matrix G (shape f) q1 q2 num den hden (by omega) (by omega)
      k hx1 hx2 hk hx1' hx2' (tpOf ⟨G.xb, G.xj, G.xt⟩ k0 h1 h2) hM hθ c1 c2
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

theorem price_T_precise {w : P3.I → K} {Γ : Finset K} {s : K → (Polynomial K)} {f : Row 4} {l : ℕ}
    (hm : Low6969Prices.Messages w Γ s) (hceil : ExpandedOrderH2307.layerWidth * (Low6969Prices.layerNeed-1) < ExpandedOrderH2307.sourceRank) (hf : Low6969Prices.SmallFactor f)
    (hon : ∀ γ ∈ Γ, K1_13.OnFactor f (K1_13.extend (s γ))) (hl : 0 < l)
    (hproper : Low6969Prices.ProperCut f Γ s l) (hchar : f.degreeOf 3 < K1.p)
    (htf : 3 * (shape f).t + 3 ≤ (shape f).j ∧ (shape f).j + 1 ≤ (shape f).b)
    (G : Gt) (hG : G.Ok) (hlift : G.lift = false) (hsc : G.sc = 1920)
    (hxt : 3 * G.xt ≤ G.xj) (hbh : G.xj + 1 ≤ G.xb) (hjh : 2 ≤ G.xj)
    (hpos : 0 < G.lb ∧ 0 < G.lj ∧ 0 < G.lt)
    (hlo : G.lb ≤ (shape f).b ∧ G.lj ≤ (shape f).j ∧ G.lt ≤ (shape f).t)
    (hhi : (shape f).b ≤ G.xb ∧ (shape f).j ≤ G.xj ∧ (shape f).t ≤ G.xt)
    (k k0 h1 h2 hx1 hx2 : ℕ) (hk : Low6969Prices.taylorLength - 4 = k)
    (hh1 : (Low6969Prices.bentLift k0 ⟨G.xb, G.xj, G.xt⟩).2 = h1)
    (hh2 : (Low6969Prices.bentLift (k0+1) ⟨G.xb, G.xj, G.xt⟩).2 = h2)
    (hx1' : (Low6969Prices.bentLift k (shape f)).2 = hx1) (hx2' : (Low6969Prices.bentLift (k + 1) (shape f)).2 = hx2)
    (hM : ∀ i k', (tpOf ⟨G.xb, G.xj, G.xt⟩ k0 h1 h2).ray i k' = Gt.mat G i k')
    (num den Ax : ℕ) (hden : 0 < den)
    (hθ : ∀ i k' : Fin 3, (den : ℤ) * (tpOf (shape f) k hx1 hx2).ray i k' ≤ num * (tpOf ⟨G.xb, G.xj, G.xt⟩ k0 h1 h2).ray i k')
    (hA : num * G.A ≤ den * Ax)
    (r0 : ℕ) (ws : List ℕ) (ht : Low6969GateClassTable.tableOK r0 ws = true) (lv : Lv) (n : ℕ) (hn : n = lv.length)
    (hr0 : r0 + ws.length ≤ n + 1) (hL : n ≤ Low6969GateFinal.levelCount)
    (hall : allOK G r0 ws lv 0 n = true)
    (ρ0 amax : ℕ) (hρ0 : 0 < ρ0) (hru : ρ0 + amax ≤ n + 1)
    (hamax : ∀ a, a * G.lb ≤ 4024 → a * G.lj ≤ 1679 → a * G.lt ≤ 500 → a ≤ amax)
    (hS0 : G.tsep ≤ G.sc * G.A * VD)
    (hS1 : 2 * VD * TT G (mx G.xb G.xj) G.xj G.xt 4024 1679 500 ≤ (G.sc * G.A * VD - G.tsep) * ρ0)
    (hS2 : 2 * VD * TT G (mx G.xb G.xj) G.xj G.xt 4024 1679 500 * ρ0 +
        VD * (2 * TT G 4024 1679 500 4024 1679 500 + amax * amax * G.tsep) ≤ (G.sc * G.A * VD - G.tsep) * (ρ0 * ρ0))
    (hsum : ∑ i ∈ Finset.range Low6969GateFinal.levelCount,
      (Low6969Prices.symbolCount - Low6969GateBox.ambCount (Bof lv i 0) (Bof lv i 1) (Bof lv i 2) + Wof lv i) <
      Low6969Prices.layerNeed) :
    Γ.card ≤ Ax + Low6969SharedPrice.additiveBase (shape f) l + Low6969SharedThirdCut.preciseFee (shape f) l := by
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
  refine Low6969GateFinal.two_cut_price_tilted_precise hm hceil hf hon hl hproper (by exact ⟨htf.1, htf.2⟩) qs hbs hcs hnd Ax (Bof lv) (Wof lv)
    (certF r0 ws) (fun r a => (certF_bounds r0 ws r a).1) (fun r a => (certF_bounds r0 ws r a).2.1)
    (fun r a => (certF_bounds r0 ws r a).2.2) ?_ hsum
  intro i _ a η hfit hv hng
  by_contra hfree
  push_neg at hfree
  obtain ⟨hlt, hI⟩ := hI_of_free G hG hxt hpos r0 ws lv n hn hr0 hall ρ0 amax hρ0 hru hamax hS0 hS1 hS2 i
    (fun k => coord (shape f) k) hxl a η hfit hv hfree
  have hc : (cvOf r0 ws (i + 1) a).1 ≤ 2 * (i + 1 - a) := cvOf_le r0 ws (i + 1) a
  have hr := rhs_le_tilted_exact f G hG hlift hsc hxt hbh hjh hlo hhi htf k k0 h1 h2 hx1 hx2 hk hh1 hh2 hx1' hx2' hM num den Ax hden
    hθ hA qs hqs (i + 1) a _ _ (Wof lv i) (Bof lv i) η hlt hc hI
  exact hng ⟨hlt, certF_class ht hlt, hr⟩

end
end Low6969GateCell

