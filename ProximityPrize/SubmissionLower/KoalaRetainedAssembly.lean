import ProximityPrize.SubmissionLower.KoalaRetainedWitness
import ProximityPrize.SubmissionLower.KoalaRetainedGeometry

set_option autoImplicit false
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
