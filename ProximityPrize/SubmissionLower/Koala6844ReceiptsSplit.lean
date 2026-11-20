import ProximityPrize.SubmissionLower.Koala6844ReceiptsGroupBound

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false

private theorem foldSome {α : Type} (step : Nat → α → Option Nat)
    (mono : ∀ b x c, step b x = some c → b ≤ c)
    (entries : List α) {base ans : Nat} (h : entries.foldlM step base = some ans) :
    base ≤ ans ∧ ∀ x ∈ entries, ∃ b c, step b x = some c ∧ c ≤ ans := by
  induction entries generalizing base with
  | nil =>
    change some base = some ans at h
    exact ⟨Nat.le_of_eq (Option.some.inj h), fun x hx => False.elim (List.not_mem_nil hx)⟩
  | cons entry rest ih =>
    rw [List.foldlM_cons] at h
    cases hs : step base entry with
    | none => simp [hs] at h
    | some next =>
      have hr : rest.foldlM step next = some ans := by simpa [hs] using h
      obtain ⟨hrest, witness⟩ := ih hr
      refine ⟨Nat.le_trans (mono base entry next hs) hrest, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · subst x
        exact ⟨base, next, hs, hrest⟩
      · exact witness x hx

def otherMiddle (f : Flag) (y : Nat) : Nat := f.y-y
def otherSlope (f : Flag) (r y : Nat) : Nat := min (otherMiddle f y) (f.r-r)
def twoShortCap (f : Flag) (L y : Nat) : Nat := min L (f.t - otherMiddle f y)
def mixedCap (f : Flag) (L y : Nat) : Nat := f.t - max (L+1) (otherMiddle f y)

def twoShortEndpoints (f : Flag) (L r y : Nat) : Nat :=
  let l := shortRates ⟨r,y,L⟩
  let g := shortRates ⟨otherSlope f r y,otherMiddle f y,L⟩
  max (shortSplitCharge f l g r y (otherSlope f r y) (otherMiddle f y) y)
    (shortSplitCharge f l g r y (otherSlope f r y) (otherMiddle f y) (twoShortCap f L y))

def mixedEndpoints (f : Flag) (L r y : Nat) (g : Rates) : Nat :=
  let l := shortRates ⟨r,y,L⟩
  max (shortSplitCharge f l g r y (otherSlope f r y) (otherMiddle f y) y)
    (shortSplitCharge f l g r y (otherSlope f r y) (otherMiddle f y) (mixedCap f L y))

def firstSplitMaximum (f : Flag) (L r y best : Nat) : Nat :=
  if y ≤ twoShortCap f L y then max best (twoShortEndpoints f L r y) else best

theorem splitCharge_facts (f : Flag) (src : Sources) (L r y base ans : Nat)
    (h : splitCharge f src L r y base = some ans) :
    base ≤ ans ∧
    (y ≤ twoShortCap f L y → twoShortEndpoints f L r y ≤ ans) ∧
    (y ≤ mixedCap f L y → ∃ rate,
      longRates ⟨otherSlope f r y, otherMiddle f y, f.t⟩ src = some rate ∧
      mixedEndpoints f L r y rate ≤ ans) := by
  have hbase : base ≤ firstSplitMaximum f L r y base := by
    unfold firstSplitMaximum
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_refl _
  have hshort (hcap : y ≤ twoShortCap f L y) :
      twoShortEndpoints f L r y ≤ firstSplitMaximum f L r y base := by
    rw [firstSplitMaximum, if_pos hcap]
    exact Nat.le_max_right _ _
  change
    (if y ≤ mixedCap f L y then
      (longRates ⟨otherSlope f r y,otherMiddle f y,f.t⟩ src).bind
        (fun rate => some (max (firstSplitMaximum f L r y base) (mixedEndpoints f L r y rate)))
     else some (firstSplitMaximum f L r y base)) = some ans at h
  by_cases hm : y ≤ mixedCap f L y
  · rw [if_pos hm] at h
    cases hrate : longRates ⟨otherSlope f r y,otherMiddle f y,f.t⟩ src with
    | none => simp [hrate, Option.bind] at h
    | some rate =>
      have han : max (firstSplitMaximum f L r y base) (mixedEndpoints f L r y rate) = ans := by
        simpa [hrate, Option.bind] using h
      refine ⟨?_, ?_, fun _ => ⟨rate, rfl, ?_⟩⟩
      · rw [← han]
        exact Nat.le_trans hbase (Nat.le_max_left _ _)
      · intro hc
        rw [← han]
        exact Nat.le_trans (hshort hc) (Nat.le_max_left _ _)
      · rw [← han]
        exact Nat.le_max_right _ _
  · rw [if_neg hm] at h
    have han := Option.some.inj h
    refine ⟨?_, ?_, fun hc => False.elim (hm hc)⟩
    · rw [← han]
      exact hbase
    · intro hc
      rw [← han]
      exact hshort hc

private def splitRange (f : Flag) (src : Sources) (L base i : Nat) : Option Nat :=
  (List.range (f.y-(i+1))).foldlM
    (fun acc dy => splitCharge f src L (i+1) ((i+1)+dy) acc) base

private def basePrice (f : Flag) (L : Nat) (x : Rates) : Nat :=
  max (x.bill f) ((shortRates ⟨f.r,f.y,L⟩).bill ⟨f.r,f.y,L⟩)

private theorem priceFold (f : Flag) (src : Sources) (ans : Nat)
    (h : terminalPrice f src = some ans) :
    ∃ x, longRates f src = some x ∧
      (List.range (f.r-1)).foldlM (splitRange f src src.totalCap)
        (basePrice f src.totalCap x) = some ans := by
  unfold terminalPrice at h
  dsimp only at h
  split at h
  · cases h
  · cases hrate : longRates f src with
    | none => simp [hrate] at h
    | some x =>
      refine ⟨x, rfl, ?_⟩
      change (List.range (f.r-1)).foldlM
        (fun best i => (List.range (f.y-(i+1))).foldlM
          (fun acc dy => splitCharge f src src.totalCap (i+1) ((i+1)+dy) acc) best)
        (basePrice f src.totalCap x) = some ans
      simpa [basePrice, hrate] using h

private theorem splitCharge_mono (f : Flag) (src : Sources) (L r y base ans : Nat)
    (h : splitCharge f src L r y base = some ans) : base ≤ ans :=
  (splitCharge_facts f src L r y base ans h).1

private theorem splitRange_mono (f : Flag) (src : Sources) (L base i ans : Nat)
    (h : splitRange f src L base i = some ans) : base ≤ ans := by
  unfold splitRange at h
  exact (foldSome _ (fun b dy c => splitCharge_mono f src L (i+1) ((i+1)+dy) b c)
    _ h).1

theorem terminalPrice_base_facts (f : Flag) (src : Sources) (ans : Nat)
    (h : terminalPrice f src = some ans) :
    ∃ x, longRates f src = some x ∧ x.bill f ≤ ans ∧
      (shortRates ⟨f.r,f.y,src.totalCap⟩).bill ⟨f.r,f.y,src.totalCap⟩ ≤ ans := by
  obtain ⟨x, hx, hfold⟩ := priceFold f src ans h
  have hb := (foldSome _ (splitRange_mono f src src.totalCap) _ hfold).1
  exact ⟨x, hx, Nat.le_trans (Nat.le_max_left _ _) hb, Nat.le_trans (Nat.le_max_right _ _) hb⟩

theorem terminalPrice_split_facts (f : Flag) (src : Sources) (ans r y : Nat)
    (h : terminalPrice f src = some ans) (hr : 1 ≤ r) (hr' : r < f.r)
    (hy : r ≤ y) (hy' : y < f.y) :
    (y ≤ twoShortCap f src.totalCap y → twoShortEndpoints f src.totalCap r y ≤ ans) ∧
    (y ≤ mixedCap f src.totalCap y →
      ∃ rate, longRates ⟨otherSlope f r y, otherMiddle f y, f.t⟩ src = some rate ∧
        mixedEndpoints f src.totalCap r y rate ≤ ans) := by
  obtain ⟨x, _, hfold⟩ := priceFold f src ans h
  have hi : r-1 ∈ List.range (f.r-1) := List.mem_range.mpr (by omega)
  obtain ⟨b, c, hs, hc⟩ := (foldSome _ (splitRange_mono f src src.totalCap) _ hfold).2 _ hi
  unfold splitRange at hs
  rw [show r-1+1 = r by omega] at hs
  have hj : y-r ∈ List.range (f.y-r) := List.mem_range.mpr (by omega)
  obtain ⟨a, q, hq, hqc⟩ := (foldSome _
    (fun b dy c => splitCharge_mono f src src.totalCap r (r+dy) b c) _ hs).2 _ hj
  rw [show r+(y-r) = y by omega] at hq
  have hf := (splitCharge_facts f src src.totalCap r y a q hq).2
  have bounds := Nat.le_trans hqc hc
  refine ⟨fun hh => Nat.le_trans (hf.1 hh) bounds, ?_⟩
  intro hh
  obtain ⟨rate, heq, hle⟩ := hf.2 hh
  exact ⟨rate, heq, Nat.le_trans hle bounds⟩

end ProximityPrize.SubmissionLower.Koala6844Receipts
