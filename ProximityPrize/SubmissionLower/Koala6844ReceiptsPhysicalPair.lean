import ProximityPrize.SubmissionLower.Koala6844ReceiptsSplit

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false

def Flag.cumulativeLE (f g : Flag) : Prop :=
  f.r ≤ g.r ∧ f.y ≤ g.y ∧ f.t ≤ g.t

def Flag.ordered (f : Flag) : Prop :=
  f.r ≤ f.y ∧ f.y ≤ f.t

def FlagIncrements.monotoneRates (d : FlagIncrements) : Prop :=
  d.total ≤ d.middle ∧ d.middle ≤ d.slope

theorem mixedRates_monotone (f g : FlagIncrements) :
    (FlagIncrements.map (fun i => mixedRate i f g)).monotoneRates := by
  simp [FlagIncrements.map, FlagIncrements.monotoneRates, mixedRate] <;> omega

theorem rawGeometryRates_monotone {f : Flag} {d : FlagIncrements}
    (h : rawGeometryRates f = some d) : d.monotoneRates := by
  unfold rawGeometryRates at h
  dsimp only at h
  split at h
  · cases h
    have first := mixedRates_monotone (earlyCut (padFlag f)) (normalCut (padFlag f))
    have second := mixedRates_monotone
      ⟨(padFlag f).t-(padFlag f).y,(padFlag f).y-(padFlag f).r,(padFlag f).r+1⟩
      (rawMovingCut (padFlag f))
    constructor
    · exact Nat.add_le_add first.1 (Nat.mul_le_mul_left _ second.1)
    · exact Nat.add_le_add first.2 (Nat.mul_le_mul_left _ second.2)
  · cases h

theorem shortRates_valid (f : Flag) :
    0 < (shortRates f).denominator ∧ (shortRates f).numerator.monotoneRates := by
  unfold shortRates
  cases h : rawGeometryRates f with

  | some d =>
    change 0 < 1 ∧ d.monotoneRates
    exact ⟨by decide, rawGeometryRates_monotone h⟩
  | none =>
    change 0 < geometryScale*geometryScale ∧ _
    exact ⟨by decide, mixedRates_monotone _ _⟩

theorem longRates_valid {f : Flag} {src : Sources} {d : Rates}
    (h : longRates f src = some d) : 0 < d.denominator ∧ d.numerator.monotoneRates := by
  unfold longRates at h
  dsimp only at h
  split at h
  · cases h
  · cases hz : graphCharge f (padFlag f 2) src.z 0 with
    | none => simp [hz] at h
    | some z =>
      simp [hz] at h
      cases hyz : graphCharge f (padFlag f 2) src.yz 1 with
      | none => simp [hyz] at h
      | some yz =>
        simp [hyz] at h
        cases hall : graphCharge f (padFlag f 2) src.all 2 with
        | none => simp [hall] at h
        | some all =>
          simp [hall] at h
          obtain ⟨hm, rfl⟩ := h
          refine ⟨?_, hm⟩
          change 0 < graphScale
          decide

theorem dot_cumulative_eq (f : Flag) (d : FlagIncrements)
    (hf : f.ordered) (hd : d.monotoneRates) :
    dot f.increments d =
      f.t*d.total + f.y*(d.middle-d.total) + f.r*(d.slope-d.middle) := by
  let v := d.middle-d.total
  let u := d.slope-d.middle
  have hy : d.middle = d.total+v := by
    dsimp only [v]
    have h := hd.1
    omega
  have hr : d.slope = d.total+v+u := by
    have h := hd.2
    dsimp only [u]
    omega
  change (f.t-f.y)*d.total+(f.y-f.r)*d.middle+f.r*d.slope =
    f.t*d.total+f.y*v+f.r*u
  rw [hr, hy]
  calc
    _ = ((f.t-f.y)+(f.y-f.r)+f.r)*d.total + ((f.y-f.r)+f.r)*v + f.r*u := by
      simp only [Nat.mul_add, Nat.add_mul]
      ac_rfl
    _ = _ := by
      have hf₁ := hf.1
      have hf₂ := hf.2
      rw [show f.t-f.y+(f.y-f.r)+f.r=f.t by omega, show f.y-f.r+f.r=f.y by omega]

theorem dot_cumulative_mono {f g : Flag} {d : FlagIncrements}
    (hf : f.ordered) (hg : g.ordered) (hfg : f.cumulativeLE g)
    (hd : d.monotoneRates) : dot f.increments d ≤ dot g.increments d := by
  rw [dot_cumulative_eq f d hf hd, dot_cumulative_eq g d hg hd]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_right _ hfg.2.2) (Nat.mul_le_mul_right _ hfg.2.1))
    (Nat.mul_le_mul_right _ hfg.1)

theorem twoShortPair_le_terminal (f : Flag) (src : Sources) (ans r y t c c' : Nat)
    (hprice : terminalPrice f src = some ans) (hr : 1 ≤ r) (hr' : r < f.r)
    (hy : r ≤ y) (hy' : y < f.y) (hty : y ≤ t) (htL : t ≤ src.totalCap)
    (hfit : t + otherMiddle f y ≤ f.t)
    (hleft :
      let rate := shortRates ⟨r,y,src.totalCap⟩
      rate.denominator*c ≤ dot (Flag.mk r y t).increments rate.numerator)
    (hright :
      let rate := shortRates ⟨min (otherSlope f r y) y,min (otherMiddle f y) y,src.totalCap⟩
      rate.denominator*c' ≤
        dot (Flag.mk (otherSlope f r y) (otherMiddle f y) (f.t-t)).increments rate.numerator) :
    c+c' ≤ ans := by
  let L := src.totalCap
  have hcap : t ≤ twoShortCap f L y := by unfold twoShortCap; omega
  have hfits : twoShortCap f L y + otherMiddle f y ≤ f.t := by unfold twoShortCap; omega
  have hcost := counts_le_endpoint_bills f (shortRates ⟨r,y,L⟩)
    (shortRates ⟨min (otherSlope f r y) y,min (otherMiddle f y) y,L⟩) r y (otherSlope f r y)
    (otherMiddle f y) y t (twoShortCap f L y) c c' (Nat.le_refl y) hty hcap hfits
    (shortRates_valid _).1 (shortRates_valid _).1 hleft hright
  exact Nat.le_trans hcost
    ((terminalPrice_split_facts f src ans r y hprice hr hr' hy hy').1 (Nat.le_trans hty hcap))

theorem mixedPair_le_terminal (f : Flag) (src : Sources) (ans r y t c c' : Nat)
    (hprice : terminalPrice f src = some ans) (hr : 1 ≤ r) (hr' : r < f.r)
    (hy : r ≤ y) (hy' : y < f.y) (hty : y ≤ t)
    (htL : t + (src.totalCap+1) ≤ f.t) (hfit : t + otherMiddle f y ≤ f.t)
    (hleft :
      let rate := shortRates ⟨r,y,src.totalCap⟩
      rate.denominator*c ≤ dot (Flag.mk r y t).increments rate.numerator)
    (hright : ∀ rate,
      longRates ⟨otherSlope f r y,otherMiddle f y,f.t⟩ src = some rate →
      rate.denominator*c' ≤
        dot (Flag.mk (otherSlope f r y) (otherMiddle f y) (f.t-t)).increments rate.numerator) :
    c+c' ≤ ans := by
  let L := src.totalCap
  have hcap : t ≤ mixedCap f L y := by
    unfold mixedCap
    dsimp only [L]
    omega
  have hfits : mixedCap f L y + otherMiddle f y ≤ f.t := by unfold mixedCap; omega
  obtain ⟨rate, hrate, hcost⟩ :=
    (terminalPrice_split_facts f src ans r y hprice hr hr' hy hy').2 (Nat.le_trans hty hcap)
  have hsum := counts_le_endpoint_bills f (shortRates ⟨r,y,L⟩) rate r y (otherSlope f r y)
    (otherMiddle f y) y t (mixedCap f L y) c c' (Nat.le_refl y) hty hcap hfits
    (shortRates_valid _).1 (longRates_valid hrate).1 hleft (hright rate hrate)
  exact Nat.le_trans hsum hcost

end ProximityPrize.SubmissionLower.Koala6844Receipts
