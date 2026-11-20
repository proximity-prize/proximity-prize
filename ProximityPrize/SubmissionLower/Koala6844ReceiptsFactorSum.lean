import ProximityPrize.SubmissionLower.Koala6844ReceiptsFamilies

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option autoImplicit false

private theorem dot_add (f g : Flag) (rate : FlagIncrements)
    (hf : f.ordered) (hg : g.ordered) :
    dot (f.add g).increments rate = dot f.increments rate + dot g.increments rate := by
  have hf1 := hf.1
  have hf2 := hf.2
  have hg1 := hg.1
  have hg2 := hg.2
  have h₀ : f.t + g.t - (f.y + g.y) = (f.t - f.y) + (g.t - g.y) := by omega
  have h₁ : f.y + g.y - (f.r + g.r) = (f.y - f.r) + (g.y - g.r) := by omega
  simp only [Flag.add, Flag.increments, dot, h₀, h₁, Nat.add_mul]
  ac_rfl

theorem factor_sum_priced (group : List CountedFactor) (rate : Rates)
    (h : ∀ a ∈ group, rate.denominator * a.count ≤ dot a.flag.increments rate.numerator) :
    rate.denominator * factorCounts group ≤ dot (factorFlags group).increments rate.numerator := by
  induction group with
  | nil => simp [factorCounts,factorFlags,dot,Flag.increments]
  | cons a tail ih =>
    have ha := h a List.mem_cons_self
    have htail := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    change rate.denominator * (a.count + factorCounts tail) ≤
      dot (a.flag.add (factorFlags tail)).increments rate.numerator
    rw [Nat.mul_add, dot_add _ _ _ a.ordered (factorFlags_ordered tail)]
    exact Nat.add_le_add ha htail

def ShortFactorPricing (family : List CountedFactor) (scope : Flag) (L : Nat) : Prop :=
  ∀ a ∈ family, a.flag.t ≤ L → ∀ r y, a.flag.r ≤ r → a.flag.y ≤ y → ShortPricingScope scope L r y →
    let rate := shortRates ⟨r,y,L⟩
    rate.denominator * a.count ≤ dot a.flag.increments rate.numerator

def LongFactorPricing (family : List CountedFactor) (src : Sources) : Prop :=
  ∀ a ∈ family, src.totalCap < a.flag.t →
    ∀ scope : Flag, a.flag.cumulativeLE scope →
      ∀ rate, longRates scope src = some rate →
        rate.denominator * a.count ≤ dot a.flag.increments rate.numerator

theorem shortFamilyPricing_of_factor {family : List CountedFactor} {scope : Flag} {L : Nat}
    (h : ShortFactorPricing family scope L) : ShortFamilyPricing family scope L := by
  intro group sub hshort r y hr hy hscope
  apply factor_sum_priced
  intro a ha
  have hle := single_factor_le_sum group a ha
  exact h a (sub a ha) (hshort a ha) r y (Nat.le_trans hle.1 hr) (Nat.le_trans hle.2.1 hy) hscope

theorem longFamilyPricing_of_factor {family : List CountedFactor} {src : Sources}
    (h : LongFactorPricing family src) : LongFamilyPricing family src := by
  intro group sub hlong scope hscope rate hrate
  apply factor_sum_priced
  intro a ha
  obtain ⟨hr,hy,ht⟩ := single_factor_le_sum group a ha
  exact h a (sub a ha) (hlong a ha) scope
    ⟨Nat.le_trans hr hscope.1,Nat.le_trans hy hscope.2.1,Nat.le_trans ht hscope.2.2⟩ rate hrate

theorem pointwiseShortPricing_of_factor {family : List CountedFactor} {scope : Flag} {L : Nat}
    (h : ShortFactorPricing family scope L) : PointwiseShortPricing family scope L := by
  intro group sub short r y limits hscope
  apply factor_sum_priced
  intro a ha
  exact h a (sub a ha) (short a ha) r y (limits a ha).1 (limits a ha).2 hscope

theorem factorCounts_le_terminal
    (f : Flag) (src : Sources) (p : Nat) (family : List CountedFactor)
    (hprice : terminalPrice f src = some p)
    (hfo : f.ordered) (hyL : f.y ≤ src.totalCap) (hLt : src.totalCap+f.y ≤ f.t)
    (hfit : (factorFlags family).cumulativeLE f)
    (shortIncidence : ShortFactorPricing family f src.totalCap)
    (longIncidence : LongFactorPricing family src) :
    factorCounts family ≤ p :=
  factorFamilies_le_terminal f src p family hprice hfo hyL hLt hfit
    (shortFamilyPricing_of_factor shortIncidence) (longFamilyPricing_of_factor longIncidence)
    (pointwiseShortPricing_of_factor shortIncidence)

end ProximityPrize.SubmissionLower.Koala6844Receipts
