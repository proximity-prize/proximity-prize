import ProximityPrize.SubmissionLower.KoalaH2430Adapter
import ProximityPrize.SubmissionLower.H2429ReducibleCharge

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace H2429TerminalCount
noncomputable section
open Polynomial Finset HighCore82258
open FrontCore82258 (effectiveHeight)
open K1_14 (Equation SeedBound atMark graphEval)
open K1_14_4 (seedDegree seedDegree_le_iff)
open KoalaRect (axisDegree axisDegree_le_iff seedBound_of_axis)
open KoalaTwoSectionPrice (singleCut properCharge charge)
open HighCore82258Upper (Input)

abbrev rootFee := H2429ReducibleCharge.partCharge

theorem rootFee_ge (e a b : ℕ) : e ≤ rootFee e a b := by
  unfold rootFee H2429ReducibleCharge.partCharge charge
  split <;> omega

/-- Count the marked roots of any reduced terminal equation with bounded seed axes. -/
theorem roots {u del Γ} (M : AnchorModel u del) (F : AnchoredFamily M Γ)
    (hw : effectiveHeight M = 2429) (hshift : M.shift ∉ Γ) {f : Equation}
    (hf : Reduced f) (he : f.natDegree ≤ 22) {T : Finset K}
    (hT : T ⊆ Γ) (hz : ∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0)
    {a b : ℕ} (ha : axisDegree f 0 ≤ a) (hb : axisDegree f 1 ≤ b)
    (hwidth : a+b ≤ 476) (hsmall : ¬ singleCut f.natDegree → a+b ≤ 448) :
    T.card ≤ rootFee f.natDegree a b := by
  classical
  let e := f.natDegree
  let v := a+b
  have he₀ : 0 < e := hf.1
  have hseed : SeedBound f v := seedBound_of_axis (Nat.add_le_add ha hb)
  by_cases hd : seedDegree f = 0
  · have hzero : SeedBound f 0 := (seedDegree_le_iff f 0).mp hd.le
    exact (FrontCore82258.fixed_count M F T hT hf.1 hzero hz).trans (rootFee_ge _ _ _)
  obtain ⟨H,hH⟩ := FrontCore82258.adjacent_chart M F
  have hsep : singularDegree e v < K1.p := by
    change (2*e-1)*v < 2130706433
    have h₁ : 2*e-1 ≤ 43 := by omega
    exact (Nat.mul_le_mul h₁ hwidth).trans_lt (by decide)
  by_cases htwo : e ≤ 2
  · have hc := KoalaH2430.small_ordinate_near (by decide : 2429 ≤ 2429)
      (by decide : 2429 ≤ 2430) M F hw hH hf hseed hsep hT hz
    unfold rootFee H2429ReducibleCharge.partCharge
    rw [if_pos htwo]
    exact hc.trans (Nat.le_add_right _ _)
  have haxes (i : ℕ) : (f.coeff i).degreeOf 0 ≤ a ∧ (f.coeff i).degreeOf 1 ≤ b :=
    ⟨(axisDegree_le_iff f 0 _).mp ha i,(axisDegree_le_iff f 1 _).mp hb i⟩
  have hflat : e * degreeAt 2429 + v < K1.p := by
    exact (Nat.add_le_add (Nat.mul_le_mul_right (degreeAt 2429) he) hwidth).trans_lt (by decide)
  let bad := T.filter fun γ => graphEval (M.label γ) (f.resultant f.derivative) = 0
  let R := T \ bad
  have hsub : bad ⊆ T := filter_subset _ _
  have hbad := FrontCore82258.resultant_count M hf hseed hsep bad (fun _ hγ => (mem_filter.mp hγ).2)
  have hreg : ∀ γ ∈ R, regularRoot f (M.label γ) (F.scalar γ) := by
    intro γ hγ
    obtain ⟨ht,hn⟩ := mem_sdiff.mp hγ
    exact P1_7.regular_of_resultant hf.1 (hz γ ht) (fun hm => hn (mem_filter.mpr ⟨ht,hm⟩))
  have hw' : (effectiveHeight M).toNat = 2429 := by simp [hw]
  let J : Input := {
    words:=u,deleted:=del,model:=M,labels:=Γ,family:=F,shift_out:=hshift,
    block:=H,chart:=hH,marks:=R,marks_sub:=sdiff_subset.trans hT,
    f:=f,regular:=hreg,reduced:=hf,sheets:=by omega,seed_pos:=Nat.pos_of_ne_zero hd,
    v:=v,seed_bound:=hseed,lo:=2429,hi:=2429,lower:=hw'.ge,upper:=hw'.le,
    positive:=by rw [hw']; decide,quotient_pos:=by rw [hw']; decide,
    agreement_gap:=by decide,factorial_guard:=by decide,separant_guard:=hsep,flat_guard:=hflat }
  have hn := KoalaH2430.regular_count_near J (by change 2429 ≤ 2429; decide)
    (by change 2429 ≤ 2695; decide) haxes rfl hsmall
  change R.card ≤ properCharge agreement 2429 2429 e a b + flatFee 2429 v + e at hn
  have hpart := card_sdiff_add_card_eq_card hsub
  change R.card+bad.card=T.card at hpart
  change bad.card ≤ singularFee e v at hbad
  unfold rootFee H2429ReducibleCharge.partCharge
  rw [if_neg htwo]
  unfold charge
  change T.card ≤ properCharge agreement 2429 2429 e a b + flatFee 2429 v + singularFee e v + e
  omega


private theorem reduced_factor {f g : Equation} (hf : Reduced f) (hg : g ∣ f)
    (hunit : ¬ IsUnit g) : Reduced g := by
  have hp := isPrimitive_of_dvd hf.2.1 hg
  have hpos : 0 < g.natDegree := by
    by_contra! hz
    have hc := eq_C_of_natDegree_le_zero hz
    have hdiv : C (g.coeff 0) ∣ g := ⟨1,by simpa only [mul_one] using hc⟩
    have hu : IsUnit (C (g.coeff 0)) := isUnit_C.mpr (hp _ hdiv)
    rw [← hc] at hu
    exact hunit hu
  exact ⟨hpos,hp,hf.2.2.of_dvd (Polynomial.map_dvd _ hg)⟩

/-- Pay the two factors with the actual axis sums from the original equation. -/
theorem reducible_roots {u del Γ} (M : AnchorModel u del) (F : AnchoredFamily M Γ)
    (hw : effectiveHeight M = 2429) (hshift : M.shift ∉ Γ) {f : Equation}
    (hf : Reduced f) (hn : ¬ Irreducible f) {T : Finset K}
    (hT : T ⊆ Γ) (hz : ∀ γ ∈ T, atMark f (M.label γ) (F.scalar γ) = 0)
    (hard : f.natDegree = 16 ∨ f.natDegree = 17)
    (axes16 : f.natDegree = 16 → axisDegree f 0+axisDegree f 1 ≤ 386)
    (axes17 : f.natDegree = 17 → axisDegree f 0+axisDegree f 1 ≤ 375) :
    T.card ≤ if f.natDegree = 16 then 160676000000000000 else 161350000000000000 := by
  classical
  have hs : ∃ g h : Equation, f = g*h ∧ ¬ IsUnit g ∧ ¬ IsUnit h := by
    by_contra! h
    apply hn
    refine ⟨Polynomial.not_isUnit_of_natDegree_pos _ hf.1,fun g k he => ?_⟩
    by_cases hg : IsUnit g
    · exact Or.inl hg
    · exact Or.inr (h g k he hg)
  obtain ⟨g,h,he,hg,hh⟩ := hs
  have hg' : Reduced g := reduced_factor hf ⟨h,he⟩ hg
  have hh' : Reduced h := reduced_factor hf ⟨g,he.trans (mul_comm g h)⟩ hh
  have hd : f.natDegree = g.natDegree+h.natDegree := by
    rw [he,natDegree_mul hg'.2.1.ne_zero hh'.2.1.ne_zero]
  have haxis (k : Fin 2) : axisDegree f k = axisDegree g k + axisDegree h k := by
    rw [he,KoalaRect.axisDegree_mul hg'.2.1.ne_zero hh'.2.1.ne_zero]
  have hsum : axisDegree g 0+axisDegree g 1+axisDegree h 0+axisDegree h 1 =
      axisDegree f 0+axisDegree f 1 := by rw [haxis 0,haxis 1]; omega
  have ht : f.natDegree ≤ 17 := by rcases hard with h | h <;> omega
  have hs : axisDegree f 0+axisDegree f 1 ≤ 386 := by
    rcases hard with h | h
    · exact axes16 h
    · exact (axes17 h).trans (by decide)
  let U := T.filter fun γ => atMark g (M.label γ) (F.scalar γ) = 0
  let V := T.filter fun γ => atMark h (M.label γ) (F.scalar γ) = 0
  have hcover : T ⊆ U ∪ V := by
    intro γ hγ
    have hzero := hz γ hγ
    rw [he, K1_14.atMark, Polynomial.eval₂_mul] at hzero
    rcases mul_eq_zero.mp hzero with hzero | hzero
    · exact mem_union_left _ (mem_filter.mpr ⟨hγ,hzero⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hγ,hzero⟩)
  have hp := (card_le_card hcover).trans (card_union_le U V)
  have h₁ := roots M F hw hshift hg' (show g.natDegree≤22 by omega)
    ((filter_subset _ _ : U ⊆ T).trans hT) (fun _ hγ => (mem_filter.mp hγ).2)
    le_rfl le_rfl (show axisDegree g 0+axisDegree g 1≤476 by omega) (fun _ => by omega)
  have h₂ := roots M F hw hshift hh' (show h.natDegree≤22 by omega)
    ((filter_subset _ _ : V ⊆ T).trans hT) (fun _ hγ => (mem_filter.mp hγ).2)
    le_rfl le_rfl (show axisDegree h 0+axisDegree h 1≤476 by omega) (fun _ => by omega)
  refine (hp.trans (Nat.add_le_add h₁ h₂)).trans ?_
  rcases hard with hw | hw
  · rw [if_pos hw]
    exact H2429ReducibleCharge.split_grade16 hg'.1 hh'.1 (hd.symm.trans hw) (by have := axes16 hw; omega)
  · rw [if_neg (by omega)]
    exact H2429ReducibleCharge.split_grade17 hg'.1 hh'.1 (hd.symm.trans hw) (by have := axes17 hw; omega)

end
end H2429TerminalCount
