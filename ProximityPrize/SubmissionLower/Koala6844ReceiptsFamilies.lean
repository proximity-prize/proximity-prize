import Mathlib.Algebra.BigOperators.Group.List.Basic
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPhysicalPair

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false

structure CountedFactor where
  flag : Flag
  count : Nat
  slope_pos : 0 < flag.r
  ordered : flag.ordered

def factorFlags (family : List CountedFactor) : Flag :=
  ⟨(family.map (fun a => a.flag.r)).sum, (family.map (fun a => a.flag.y)).sum,
    (family.map (fun a => a.flag.t)).sum⟩

def factorCounts (family : List CountedFactor) : Nat :=
  (family.map CountedFactor.count).sum

def Flag.add (f g : Flag) : Flag := ⟨f.r+g.r,f.y+g.y,f.t+g.t⟩

theorem factorFlags_append (a b : List CountedFactor) :
    factorFlags (a++b) = (factorFlags a).add (factorFlags b) := by
  simp only [factorFlags, List.map_append, List.sum_append, Flag.add]

theorem factorFlags_ordered (family : List CountedFactor) : (factorFlags family).ordered := by
  induction family with
  | nil => exact ⟨Nat.le_refl 0,Nat.le_refl 0⟩
  | cons a tail ih =>
    exact ⟨Nat.add_le_add a.ordered.1 ih.1, Nat.add_le_add a.ordered.2 ih.2⟩

theorem factorFlags_pos {family : List CountedFactor} (h : family ≠ []) :
    0 < (factorFlags family).r := by
  cases family with
  | nil => exact False.elim (h rfl)
  | cons a tail =>
    change 0 < a.flag.r+(factorFlags tail).r
    have hp := a.slope_pos
    omega

def FamilySubset (g family : List CountedFactor) : Prop := ∀ a ∈ g, a ∈ family

def ShortPricingScope (scope : Flag) (L r y : Nat) : Prop :=
  1 ≤ r ∧ r ≤ y ∧ y ≤ L ∧ r ≤ scope.r ∧ y ≤ scope.y

theorem single_factor_le_sum (group : List CountedFactor) (a : CountedFactor) (ha : a ∈ group) :
    a.flag.cumulativeLE (factorFlags group) := by
  induction group with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons b tail ih =>
    change a.flag.cumulativeLE (b.flag.add (factorFlags tail))
    rcases List.mem_cons.mp ha with hr | ht
    · subst b
      exact ⟨Nat.le_add_right _ _,Nat.le_add_right _ _,Nat.le_add_right _ _⟩
    · obtain ⟨hr,hy,ht⟩ := ih ht
      exact ⟨Nat.le_trans hr (Nat.le_add_left _ _),
        Nat.le_trans hy (Nat.le_add_left _ _),Nat.le_trans ht (Nat.le_add_left _ _)⟩

/-- Individual short factors may share a cap even when their aggregate degrees exceed it. -/
def PointwiseShortPricing (family : List CountedFactor) (scope : Flag) (L : Nat) : Prop :=
  ∀ (group : List CountedFactor), FamilySubset group family →
    (∀ a ∈ group, a.flag.t ≤ L) →
    ∀ r y, (∀ a ∈ group, a.flag.r ≤ r ∧ a.flag.y ≤ y) → ShortPricingScope scope L r y →
      let rate := shortRates ⟨r,y,L⟩
      rate.denominator * factorCounts group ≤ dot (factorFlags group).increments rate.numerator

/-- Choose a short factor of greatest middle degree as the first part of a partition. -/
private theorem largest_middle {l : List CountedFactor} (nonempty : l ≠ []) :
    ∃ a rest, l.Perm (a :: rest) ∧ ∀ b ∈ rest, b.flag.y ≤ a.flag.y := by
  induction l with
  | nil => exact False.elim (nonempty rfl)
  | cons b l ih =>
    by_cases h : l = []
    · subst l
      exact ⟨b,[],List.Perm.refl _,by simp⟩
    obtain ⟨a,rest,hp,below⟩ := ih h
    by_cases hab : a.flag.y ≤ b.flag.y
    · refine ⟨b,l,List.Perm.refl _,?_⟩
      intro z hz
      rcases List.mem_cons.mp (hp.mem_iff.mp hz) with eqn | mem
      · exact eqn ▸ hab
      · exact Nat.le_trans (below z mem) hab
    · refine ⟨a,b::rest,(hp.cons b).trans (by apply List.Perm.swap),?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with eqn | mem
      · exact eqn ▸ Nat.le_of_not_ge hab
      · exact below z mem

private theorem factorFlags_perm {l l' : List CountedFactor} (h : l.Perm l') :
    factorFlags l = factorFlags l' := by
  unfold factorFlags
  rw [(h.map (fun a => a.flag.r)).sum_eq, (h.map (fun a => a.flag.y)).sum_eq,
    (h.map (fun a => a.flag.t)).sum_eq]

def ShortFamilyPricing (family : List CountedFactor) (scope : Flag) (L : Nat) : Prop :=
  ∀ (group : List CountedFactor), FamilySubset group family →
    (∀ a ∈ group, a.flag.t ≤ L) →
    ∀ r y, (factorFlags group).r ≤ r → (factorFlags group).y ≤ y → ShortPricingScope scope L r y →
      let rate := shortRates ⟨r,y,L⟩
      rate.denominator * factorCounts group ≤ dot (factorFlags group).increments rate.numerator

def LongFamilyPricing (family : List CountedFactor) (src : Sources) : Prop :=
  ∀ (group : List CountedFactor), FamilySubset group family →
    (∀ a ∈ group, src.totalCap < a.flag.t) →
    ∀ scope : Flag, (factorFlags group).cumulativeLE scope →
      ∀ rate, longRates scope src = some rate →
        rate.denominator * factorCounts group ≤ dot (factorFlags group).increments rate.numerator

private theorem sum_filter_partition {α : Type} (p : α → Bool) (w : α → Nat) (l : List α) :
    ((l.filter p).map w).sum + ((l.filter (fun x => !p x)).map w).sum = (l.map w).sum := by
  induction l with
  | nil => rfl
  | cons a tail ih =>
    cases h : p a <;> simp [h, List.sum_cons] at ih ⊢ <;> omega

private theorem flag_filter_partition (p : CountedFactor → Bool) (l : List CountedFactor) :
    (factorFlags (l.filter p)).add (factorFlags (l.filter (fun x => !p x))) = factorFlags l := by
  unfold factorFlags Flag.add
  simp only
  rw [sum_filter_partition p (fun a => a.flag.r) l,
    sum_filter_partition p (fun a => a.flag.y) l,
    sum_filter_partition p (fun a => a.flag.t) l]

def remainderCap (scope left : Flag) : Flag :=
  ⟨otherSlope scope left.r left.y,otherMiddle scope left.y,scope.t-left.t⟩

private structure PairCaps (scope left right : Flag) : Prop where
  left_pos : 1 ≤ left.r
  left_slope_lt : left.r < scope.r
  left_middle_lt : left.y < scope.y
  right_padded : right.cumulativeLE (remainderCap scope left)
  padding_ordered : (remainderCap scope left).ordered

private theorem pair_caps (scope p q : Flag)
    (hq : q.ordered) (hp0 : 0 < p.r) (hq0 : 0 < q.r)
    (hscope : (p.add q).cumulativeLE scope)
    (hfit : p.t+otherMiddle scope p.y ≤ scope.t) :
    PairCaps scope p q := by
  rcases hscope with ⟨hr,hy,ht⟩
  simp only [Flag.add] at hr hy ht
  have hq1 := hq.1
  have hq2 := hq.2
  have hqmid : q.y ≤ otherMiddle scope p.y := by unfold otherMiddle; omega
  have hqsl : q.r ≤ scope.r-p.r := by omega
  have hqtot : q.t ≤ scope.t-p.t := by omega
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · exact ⟨Nat.le_min.mpr ⟨Nat.le_trans hq1 hqmid,hqsl⟩,hqmid,hqtot⟩
  · exact ⟨Nat.min_le_left _ _, by
      change otherMiddle scope p.y ≤ scope.t-p.t
      omega⟩

private theorem all_long_le_terminal (f : Flag) (src : Sources) (p : Nat)
    (hprice : terminalPrice f src = some p) (hfo : f.ordered)
    {family group : List CountedFactor} (hsub : FamilySubset group family)
    (hlong : ∀ a ∈ group, src.totalCap < a.flag.t)
    (hfit : (factorFlags group).cumulativeLE f)
    (incidence : LongFamilyPricing family src) :
    factorCounts group ≤ p := by
  obtain ⟨rate, hrate, hbase, _⟩ := terminalPrice_base_facts f src p hprice
  have hvalid := longRates_valid hrate
  have hraw := incidence group hsub hlong f hfit rate hrate
  have hpad := dot_cumulative_mono (factorFlags_ordered group) hfo hfit hvalid.2
  exact Nat.le_trans (count_le_rateBill _ _ _ hvalid.1 (Nat.le_trans hraw hpad)) hbase

private theorem singleton_short_le_terminal (f : Flag) (src : Sources) (p : Nat)
    (hprice : terminalPrice f src = some p) (hfo : f.ordered) (hyL : f.y ≤ src.totalCap)
    {family : List CountedFactor} {a : CountedFactor} (hsub : a ∈ family)
    (hshort : a.flag.t ≤ src.totalCap) (hfit : a.flag.cumulativeLE f)
    (incidence : ShortFamilyPricing family f src.totalCap) :
    a.count ≤ p := by
  obtain ⟨_, _, _, hbase⟩ := terminalPrice_base_facts f src p hprice
  let scope : Flag := ⟨f.r,f.y,src.totalCap⟩
  have hraw := incidence [a] (fun b hb => by
    have he : b=a := by simpa using hb
    subst b
    exact hsub) (fun b hb => by
    have he : b=a := by simpa using hb
    subst b

    exact hshort) f.r f.y hfit.1 hfit.2.1
    ⟨Nat.le_trans a.slope_pos hfit.1,hfo.1,hyL,Nat.le_refl _,Nat.le_refl _⟩
  have hvalid := shortRates_valid scope
  have hpad := dot_cumulative_mono a.ordered (show scope.ordered from ⟨hfo.1,hyL⟩)
    (show a.flag.cumulativeLE scope from ⟨hfit.1,hfit.2.1,hshort⟩) hvalid.2
  exact Nat.le_trans (count_le_rateBill _ _ _ hvalid.1 (Nat.le_trans hraw hpad)) hbase

private theorem two_short_groups_le_terminal (f : Flag) (src : Sources) (p : Nat)
    (hprice : terminalPrice f src = some p) (hyL : f.y ≤ src.totalCap) (hLt : src.totalCap+f.y ≤ f.t)
    {family left right : List CountedFactor}
    (hnL : left ≠ []) (hnR : right ≠ [])
    (hsubL : FamilySubset left family) (hsubR : FamilySubset right family)
    (hshortL : ∀ a ∈ left, a.flag.t ≤ src.totalCap)
    (hshortR : ∀ a ∈ right, a.flag.t ≤ src.totalCap)
    (htL : (factorFlags left).t ≤ src.totalCap)
    (hfit : ((factorFlags left).add (factorFlags right)).cumulativeLE f)
    (incidence : ShortFamilyPricing family f src.totalCap)
    (individual : PointwiseShortPricing family f src.totalCap)
    (largest : ∀ a ∈ right, a.flag.y ≤ (factorFlags left).y) :
    factorCounts left+factorCounts right ≤ p := by
  let v := factorFlags left
  let u := factorFlags right
  let cap := remainderCap f v
  have ordL := factorFlags_ordered left
  have ordR := factorFlags_ordered right
  change v.t ≤ src.totalCap at htL
  have hsum : v.t+otherMiddle f v.y ≤ f.t := by unfold otherMiddle; omega
  have h := pair_caps f v u ordR (factorFlags_pos hnL) (factorFlags_pos hnR) hfit hsum
  have hvY : v.y ≤ f.y := by
    have hsumY : v.y+u.y ≤ f.y := hfit.2.1
    omega
  have hr : cap.r ≤ f.r := Nat.le_trans (Nat.min_le_right _ _) (Nat.sub_le _ _)
  have hy : cap.y ≤ f.y := Nat.sub_le _ _
  have hleft := incidence left hsubL hshortL v.r v.y (Nat.le_refl _) (Nat.le_refl _)
    ⟨h.left_pos,ordL.1,Nat.le_trans hvY hyL,Nat.le_of_lt h.left_slope_lt,hvY⟩
  let rsmall := min cap.r v.y
  let ysmall := min cap.y v.y
  have hposy : 1 ≤ v.y := Nat.le_trans h.left_pos ordL.1
  have hscope : ShortPricingScope f src.totalCap rsmall ysmall := by
    refine ⟨Nat.le_min.mpr ⟨Nat.le_trans (factorFlags_pos hnR) h.right_padded.1,hposy⟩,
      (by have horder : cap.r ≤ cap.y := h.padding_ordered.1; dsimp [rsmall,ysmall]; omega),?_,?_,?_⟩
    · exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_trans hy hyL)
    · exact Nat.le_trans (Nat.min_le_left _ _) hr
    · exact Nat.le_trans (Nat.min_le_left _ _) hy
  have hright := individual right hsubR hshortR rsmall ysmall (by
    intro a ha
    have hu := single_factor_le_sum right a ha
    have hm := largest a ha
    exact ⟨Nat.le_min.mpr ⟨Nat.le_trans hu.1 h.right_padded.1,Nat.le_trans a.ordered.1 hm⟩,
      Nat.le_min.mpr ⟨Nat.le_trans hu.2.1 h.right_padded.2.1,hm⟩⟩) hscope
  have hpad := dot_cumulative_mono ordR h.padding_ordered h.right_padded
    (shortRates_valid ⟨rsmall,ysmall,src.totalCap⟩).2
  exact twoShortPair_le_terminal f src p v.r v.y v.t (factorCounts left) (factorCounts right)
    hprice h.left_pos h.left_slope_lt ordL.1 h.left_middle_lt ordL.2 htL hsum hleft
    (Nat.le_trans hright hpad)

private theorem mixed_groups_le_terminal (f : Flag) (src : Sources) (p : Nat)
    (hprice : terminalPrice f src = some p) (hyL : f.y ≤ src.totalCap)
    {family left right : List CountedFactor}
    (hnL : left ≠ []) (hnR : right ≠ [])
    (hsubL : FamilySubset left family) (hsubR : FamilySubset right family)
    (hshortL : ∀ a ∈ left, a.flag.t ≤ src.totalCap)
    (hlongR : ∀ a ∈ right, src.totalCap < a.flag.t)
    (hfit : ((factorFlags left).add (factorFlags right)).cumulativeLE f)
    (shortIncidence : ShortFamilyPricing family f src.totalCap)
    (longIncidence : LongFamilyPricing family src) :
    factorCounts left+factorCounts right ≤ p := by
  let v := factorFlags left
  let u := factorFlags right
  let cap := remainderCap f v
  have ordL := factorFlags_ordered left
  have ordR := factorFlags_ordered right
  have hu : src.totalCap < u.t := by
    dsimp only [u]
    cases right with
    | nil => exact False.elim (hnR rfl)
    | cons a tail =>
      have hh := hlongR a (List.mem_cons_self)
      change src.totalCap < a.flag.t+(factorFlags tail).t
      omega
  have hfitT := hfit.2.2
  change v.t+u.t ≤ f.t at hfitT
  have hlarge : v.t+(src.totalCap+1) ≤ f.t := by omega
  have hsum : v.t+otherMiddle f v.y ≤ f.t := by unfold otherMiddle; omega
  have h := pair_caps f v u ordR (factorFlags_pos hnL) (factorFlags_pos hnR) hfit hsum
  have hvY := Nat.le_of_lt h.left_middle_lt
  have hleft := shortIncidence left hsubL hshortL v.r v.y (Nat.le_refl _) (Nat.le_refl _)
    ⟨h.left_pos,ordL.1,Nat.le_trans hvY hyL,Nat.le_of_lt h.left_slope_lt,hvY⟩
  refine mixedPair_le_terminal f src p v.r v.y v.t (factorCounts left) (factorCounts right)
    hprice h.left_pos h.left_slope_lt ordL.1 h.left_middle_lt ordL.2 hlarge hsum hleft ?_
  intro rate hrate
  have hscope : u.cumulativeLE ⟨cap.r,cap.y,f.t⟩ :=
    ⟨h.right_padded.1,h.right_padded.2.1,Nat.le_trans h.right_padded.2.2 (Nat.sub_le _ _)⟩
  have hright := longIncidence right hsubR hlongR ⟨cap.r,cap.y,f.t⟩ hscope rate hrate
  exact Nat.le_trans hright (dot_cumulative_mono ordR h.padding_ordered
    h.right_padded (longRates_valid hrate).2)

theorem factorFamilies_le_terminal (f : Flag) (src : Sources) (p : Nat)
    (family : List CountedFactor)
    (hprice : terminalPrice f src = some p)
    (hfo : f.ordered) (hyL : f.y ≤ src.totalCap) (hLt : src.totalCap+f.y ≤ f.t)
    (hfit : (factorFlags family).cumulativeLE f)
    (shortIncidence : ShortFamilyPricing family f src.totalCap)
    (longIncidence : LongFamilyPricing family src)
    (individual : PointwiseShortPricing family f src.totalCap) :
    factorCounts family ≤ p := by
  let test (a : CountedFactor) : Bool := decide (a.flag.t ≤ src.totalCap)
  let ss := family.filter test
  let ls := family.filter (fun a => !test a)
  have hsubS : FamilySubset ss family := fun a ha => (List.mem_filter.mp ha).1
  have hsubL : FamilySubset ls family := fun a ha => (List.mem_filter.mp ha).1
  have hallS : ∀ a ∈ ss, a.flag.t ≤ src.totalCap := fun a ha =>
    of_decide_eq_true (List.mem_filter.mp ha).2
  have hallL : ∀ a ∈ ls, src.totalCap < a.flag.t := by
    intro a ha
    have hyes := (List.mem_filter.mp ha).2
    have hno : ¬ a.flag.t ≤ src.totalCap := by simpa [test] using hyes
    omega
  have hflags : (factorFlags ss).add (factorFlags ls) = factorFlags family :=
    flag_filter_partition test family
  have hsum : factorCounts ss+factorCounts ls = factorCounts family :=
    sum_filter_partition test CountedFactor.count family
  rw [← hsum]
  by_cases hs : ss = []
  · have hls : (factorFlags ls).cumulativeLE f := by
      simpa [hs, factorFlags, Flag.add] using (hflags ▸ hfit : ((factorFlags ss).add (factorFlags ls)).cumulativeLE f)
    simpa [hs, factorCounts] using all_long_le_terminal f src p hprice hfo hsubL hallL hls longIncidence
  · by_cases hl : ls = []
    · have hf : (factorFlags ss).cumulativeLE f := by
        simpa [hl, factorFlags, Flag.add] using (hflags ▸ hfit : ((factorFlags ss).add (factorFlags ls)).cumulativeLE f)
      obtain ⟨a,t,hperm,largest⟩ := largest_middle hs
      have sortedFit : (factorFlags (a::t)).cumulativeLE f := (factorFlags_perm hperm) ▸ hf
      have sortedCounts : factorCounts ss = factorCounts (a::t) :=
        (hperm.map CountedFactor.count).sum_eq
      have ha : a ∈ ss := hperm.mem_iff.mpr List.mem_cons_self
      rw [sortedCounts]
      cases t with
      | nil =>
        have haFit : a.flag.cumulativeLE f := by simpa [factorFlags] using sortedFit
        have haPrice := singleton_short_le_terminal f src p hprice hfo hyL (hsubS a ha)
          (hallS a ha) haFit shortIncidence
        simpa [hl, factorCounts] using haPrice
      | cons b rest =>
        let others := b::rest
        have hmem (d : CountedFactor) (hd : d ∈ others) : d ∈ ss :=
          hperm.mem_iff.mpr (List.mem_cons_of_mem _ hd)
        have hfitPair : ((factorFlags [a]).add (factorFlags others)).cumulativeLE f := by
          rw [← factorFlags_append]
          exact sortedFit
        have hf1 : FamilySubset [a] family := by
          intro d hd
          have eqn : d=a := by simpa using hd
          subst d
          exact hsubS a ha
        have hS1 : ∀ d ∈ [a], d.flag.t ≤ src.totalCap := by
          intro d hd
          have eqn : d=a := by simpa using hd
          subst d
          exact hallS a ha
        have hpaid := two_short_groups_le_terminal f src p hprice hyL hLt
          (left := [a]) (right := others) (by simp) (by simp [others])
          hf1 (fun d hd => hsubS d (hmem d hd)) hS1 (fun d hd => hallS d (hmem d hd))
          (by simpa [factorFlags] using hallS a ha) hfitPair shortIncidence individual
          (by simpa [factorFlags,others] using largest)
        simpa [hl, others, factorCounts] using hpaid
    · exact mixed_groups_le_terminal f src p hprice hyL hs hl hsubS hsubL hallS hallL
        (hflags ▸ hfit) shortIncidence longIncidence

end ProximityPrize.SubmissionLower.Koala6844Receipts
