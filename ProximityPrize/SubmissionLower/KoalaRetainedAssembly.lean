import ProximityPrize.SubmissionLower.Shared50BentCaps
import ProximityPrize.SubmissionLower.Shared50Tally
import ProximityPrize.SubmissionLower.KoalaRetainedWitness

-- merged module KoalaRetainedGeometry
section Merged_KoalaRetainedGeometry
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000

namespace KoalaRetainedCut
noncomputable section

open P3 (K I)
open K1_13 (Row Shape InBox shape mixed32 chart)
open Final50Price (Messages tiltedFits tiltedSurface taylorLength)
open Final50GeometryCut (CutInput MixedBound)
open private chargedPrice assemble_charge continued_bound from ProximityPrize.SubmissionLower.Final50GeometryCut
open private Final50ActiveCycle.mixed from ProximityPrize.SubmissionLower.Final50ActiveCycleMixed
open scoped Polynomial BigOperators

/-- The accepted physical charge with an arbitrary mixed surface budget. -/
def cutPrice (x : Shape) (l scale surface : ℕ) := chargedPrice x l scale surface

def fourSurface (p q : Shape) :=
  mixed32 p q (chart (taylorLength+1) p) (chart (taylorLength+2) p)

variable {w : I → K} {Γ : Finset K} {s : K → K[X]} {f Q : Row 4} {l : ℕ}

theorem smaller_tilted (hm : Messages w Γ s) (input : CutInput Γ s f Q l)
    (q : Shape) (hQ : InBox (shape Q) q) (hq : Low48BentLattice.Chamber (q,0))
    (hguard : tiltedFits (shape f)) :
    Γ.card ≤ cutPrice (shape f) l (60*32) (tiltedSurface (shape f).chamber q) := by
  let p := (shape f).chamber
  have hp := K1_13_7_1.shape_chamber f
  have ht : 1 ≤ p.t := input.small.2.1
  have hCh := Shared50BentCaps.caps_chamber (p := p) hp.1 ht hguard.1 hq
  apply assemble_charge Final50GeometryCut_1.proof continued_bound hm input (by decide : 0 < 60*32)
  apply Final50ActiveCycle.mixed (R := Low48BentCycle.rawFamily (Shared50BentCaps.caps p q))
    (B := Low48BentCycle.capFamily (Shared50BentCaps.caps p q)) input Shared50BentCaps.ordinary_doubled
  · exact Low48BentCycle.old_section ⟨le_max_left _ _,le_rfl,le_rfl⟩
  · exact Low48BentCycle.old_section hQ
  · exact Shared50BentCaps.chart q ht
  · exact Shared50BentCaps.ordinary_budget hCh

theorem smaller_four (hm : Messages w Γ s) (input : CutInput Γ s f Q l)
    (q : Shape) (hQ : InBox (shape Q) q) (hq : K1_13_6_2_3.ChamberBox q) :
    Γ.card ≤ cutPrice (shape f) l 32 (fourSurface (shape f).chamber q) := by
  classical
  let D : Shared50Tally.Data Γ s f Q l Set.univ := Shared50Tally.build Set.univ
  have h := Shared50CycleFour.bound_with_cut K1_13_6_2_3_1.proof
    (K1_13_6_2_3_2.of_children
      K1_13_6_2_3_2_1.proof K1_13_6_2_3_2_2.proof K1_13_6_2_3_2_3.proof
      K1_13_6_2_3_2_4.proof K1_13_6_2_3_2_5.proof K1_13_6_2_3_2_6.proof)
    (K1_13_6_2_3_3.of_children K1_13_6_2_3_3_1.proof
      (K1_13_6_2_3_3_2.of_children K1_13_6_2_3_3_2_1.proof K1_13_6_2_3_3_2_2.proof))
    f Q Q l input.small input.proper q hq hQ (fun _ => l)
    D.branches D.points (D.four input) (fun b _ => ⟨b.base,b.high⟩)
  have hh := (le_div_iff₀ (by norm_num : (0:ℚ)<32)).mp h
  have hn : 32*l*(∑ b∈D.branches, b.weight*(D.points b).card) ≤ fourSurface (shape f).chamber q := by
    apply (Nat.cast_le (α := ℚ)).mp
    simp only [fourSurface,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat]
    simpa only [Nat.cast_mul,← Finset.mul_sum,mul_comm (32:ℚ),mul_assoc,mul_left_comm] using hh
  apply assemble_charge Final50GeometryCut_1.proof continued_bound hm input (by decide : 0 < 32)
  obtain ⟨C,B,hcurve,hpos,hcover,hcost⟩ := D.pieces input
  refine ⟨C,B,hcurve,hpos,?_,(Nat.mul_le_mul_left (32*l) hcost).trans hn⟩
  intro γ hγ hmixed
  obtain ⟨b,hb⟩ := Final50GeometryCut_2.branch_of_mixed hmixed
  exact hcover γ hγ ⟨b,Set.mem_univ _,hb⟩

#print axioms smaller_tilted
#print axioms smaller_four

end
end KoalaRetainedCut
end Merged_KoalaRetainedGeometry

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
namespace KoalaRetainedCut
noncomputable section

open P3 (I K)
open K1_13 (Geom Row Shape shape InBox OrderAt atJet extend)
open Final50Price (primaryBox primaryCutoff TrueWeightLE ActiveFits SmallFactor Messages
  tiltedFits tiltedSurface physicalPrice ProperCut)
open scoped Polynomial BigOperators

def chamberHull (x : Shape) : Shape := ⟨max x.b x.j,x.j,min x.t (x.j/3)⟩

theorem hull_includes {Q : Row 4} {x : Shape} (hb : InBox (shape Q) x) :
    InBox (shape Q) (chamberHull x) := by
  have h := (K1_13_7_1.shape_chamber Q).2
  change 3*(shape Q).t ≤ (shape Q).j at h
  exact ⟨hb.1.trans (le_max_left _ _),hb.2.1, le_min hb.2.2 (by have := hb.2.1; omega)⟩

theorem hull_valid (x : Shape) : Low48BentLattice.Chamber (chamberHull x,0) := by
  refine ⟨le_max_right _ _,?_,Nat.zero_le _⟩
  change 3*min x.t (x.j/3) ≤ x.j
  have := min_le_right x.t (x.j/3)
  omega

def contractedPrice (x h : Shape) (l active : ℕ) : ℕ :=
  let q := chamberHull (residualBox h l)
  let old := physicalPrice x l active
  let four := if 0 < q.t then min old (cutPrice x l 32 (fourSurface x.chamber q)) else old
  if tiltedFits x then min four (cutPrice x l (60*32) (tiltedSurface x.chamber q)) else four

/-- Physical count for the actual extremal bank witness and the selected (off-retained) marks. -/
theorem price_of_witness_floor {w : I → K} {Γ : Finset K} {s : K → K[X]} {P H f : Row 4}
    {k a l active : ℕ} (hm : Messages w Γ s) (hsmall : SmallFactor f)
    (hactive : ActiveFits f active) (hchar : f.degreeOf 3 < K1.p)
    (hon : ∀ γ∈Γ, K1_13.OnFactor f (extend (s γ)))
    (hoff : ∀ γ∈Γ, atJet H (extend (s γ)) ≠ 0)
    (hP : P ≠ 0) (hH : H ≠ 0) (hc : IsRelPrime f H) (hpos : 0 < l) (hl : l ≤ k-a)
    (hbox : InBox (shape P) primaryBox) (hweight : TrueWeightLE P primaryCutoff)
    (htaper : ActiveFits P 5164) (hord : ∀ γ∈Γ, OrderAt P (extend (s γ)) k)
    (divH : H^k ∣ P) (divF : f^a ∣ P) (exactF : ¬ f^(a+1) ∣ P) :
    ∀ h : Shape, InBox h (shape H) → Γ.card ≤ contractedPrice (shape f) h l active := by
  intro h hfloor
  obtain ⟨Q,hproper,hboxQ,hweightQ,hactiveQ,horderQ⟩ :=
    exists_divided_cut hP hH hsmall.1 hsmall.2.1 hchar hc hl hbox hweight htaper divH divF exactF
  have hQP : InBox (shape Q) primaryBox :=
    ⟨hboxQ.1.trans (Nat.sub_le _ _), hboxQ.2.1.trans (Nat.sub_le _ _),
      hboxQ.2.2.trans (Nat.sub_le _ _)⟩
  have horder (γ) (hγ : γ∈Γ) := horderQ _ (hoff γ hγ) (hord γ hγ)
  have hfloorQ : InBox (shape Q) (residualBox h l) :=
    ⟨hboxQ.1.trans (Nat.sub_le_sub_left (Nat.mul_le_mul_left l hfloor.1) _),
      hboxQ.2.1.trans (Nat.sub_le_sub_left (Nat.mul_le_mul_left l hfloor.2.1) _),
      hboxQ.2.2.trans (Nat.sub_le_sub_left (Nat.mul_le_mul_left l hfloor.2.2) _)⟩
  let q := chamberHull (residualBox h l)
  have hQ : InBox (shape Q) q := hull_includes hfloorQ
  have hch := hull_valid (residualBox h l)
  have input : Final50GeometryCut.CutInput Γ s f Q l :=
    ⟨hm.distinct,hm.degree,hsmall,hon,hpos,hproper,hQP,hweightQ,horder⟩
  have hold := Final50ActiveCycle.proof w Γ s hm f hsmall active hactive hon l hpos
    ⟨Q,hproper,hQP,hweightQ,hactiveQ,horder⟩
  have hfour : Γ.card ≤ (if 0 < q.t then min (physicalPrice (shape f) l active)
      (cutPrice (shape f) l 32 (fourSurface (shape f).chamber q)) else physicalPrice (shape f) l active) := by
    split
    next ht => exact le_min hold (smaller_four hm input q hQ ⟨hch.1,hch.2.1,ht⟩)
    next => exact hold
  unfold contractedPrice
  split
  next hg => exact le_min hfour (smaller_tilted hm input q hQ hch hg)
  next => exact hfour

/-- Physical count for the actual extremal bank witness and the selected (off-retained) marks. -/
theorem price_of_witness {w : I → K} {Γ : Finset K} {s : K → K[X]} {P H f : Row 4}
    {k a l active : ℕ} (hm : Messages w Γ s) (hsmall : SmallFactor f)
    (hactive : ActiveFits f active) (hchar : f.degreeOf 3 < K1.p)
    (hon : ∀ γ∈Γ, K1_13.OnFactor f (extend (s γ)))
    (hoff : ∀ γ∈Γ, atJet H (extend (s γ)) ≠ 0)
    (hP : P ≠ 0) (hH : H ≠ 0) (hc : IsRelPrime f H) (hpos : 0 < l) (hl : l ≤ k-a)
    (hbox : InBox (shape P) primaryBox) (hweight : TrueWeightLE P primaryCutoff)
    (htaper : ActiveFits P 5164) (hord : ∀ γ∈Γ, OrderAt P (extend (s γ)) k)
    (divH : H^k ∣ P) (divF : f^a ∣ P) (exactF : ¬ f^(a+1) ∣ P) :
    Γ.card ≤ contractedPrice (shape f) (shape H) l active :=
  price_of_witness_floor hm hsmall hactive hchar hon hoff hP hH hc hpos hl hbox hweight
    htaper hord divH divF exactF (shape H) ⟨le_rfl,le_rfl,le_rfl⟩

#print axioms price_of_witness_floor
#print axioms price_of_witness

end
end KoalaRetainedCut