import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f
import ProximityPrize.SubmissionLower.Bundle6970_40f9df008f04cc7f

set_option Elab.async false
set_option autoImplicit false
namespace Height2307Companion
open K1_13 (Shape)
open scoped BigOperators

theorem sealed_rules (k : ℕ) (ord : ℕ → ℕ → ℕ) (price : Shape → ℕ)
    (ho : Supports anchors k ord) (hc : Corners ord price) {r : Rule} (hr : r ∈ rules)
    (same : k=r.band) : Within r price := by
  simp only [rules,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28
  · subst r
    subst k
    exact group0 ord price ho hc
  · subst r
    subst k
    exact group1 ord price ho hc
  · subst r
    subst k
    exact group2 ord price ho hc
  · subst r
    subst k
    exact group3 ord price ho hc
  · subst r
    subst k
    exact group4 ord price ho hc
  · subst r
    subst k
    exact group5 ord price ho hc
  · subst r
    subst k
    exact group6 ord price ho hc
  · subst r
    subst k
    exact group7 ord price ho hc
  · subst r
    subst k
    exact group8 ord price ho hc
  · subst r
    subst k
    exact group9 ord price ho hc
  · subst r
    subst k
    exact group10 ord price ho hc
  · subst r
    subst k
    exact group11 ord price ho hc
  · subst r
    subst k
    exact group12 ord price ho hc
  · subst r
    subst k
    exact group13 ord price ho hc
  · subst r
    subst k
    exact group14 ord price ho hc
  · subst r
    subst k
    exact group15 ord price ho hc
  · subst r
    subst k
    exact group16 ord price ho hc
  · subst r
    subst k
    exact group17 ord price ho hc
  · subst r
    subst k
    exact group18 ord price ho hc
  · subst r
    subst k
    exact group19 ord price ho hc
  · subst r
    subst k
    exact group20 ord price ho hc
  · subst r
    subst k
    exact group21 ord price ho hc
  · subst r
    subst k
    exact group22 ord price ho hc
  · subst r
    subst k
    exact group23 ord price ho hc
  · subst r
    subst k
    exact group24 ord price ho hc
  · subst r
    subst k
    exact group25 ord price ho hc
  · subst r
    subst k
    exact group26 ord price ho hc
  · subst r
    subst k
    exact group27 ord price ho hc
  · subst r
    subst k
    exact group28 ord price ho hc

theorem with_ordinary_prices {ι : Type*} {s : Finset ι} {a : ι → Shape} {cost : ι → ℕ}
    {k debt : ℕ} {r : Shape} (ord : ℕ → ℕ → ℕ) (price : Shape → ℕ)
    (ho : Supports anchors k ord) (hc : Corners ord price)
    (hbook : book k r = some debt) (ha : ∀ i ∈ s, legal (a i))
    (hb : (∑ i ∈ s, (a i).b) ≤ r.b) (hj : (∑ i ∈ s, (a i).j) ≤ r.j)
    (ht : (∑ i ∈ s, (a i).t) ≤ r.t) (fee : ∀ i ∈ s, cost i ≤ price (a i)) :
    (∑ i ∈ s, cost i) ≤ debt := by
  apply fromRules_sound hbook ha hb hj ht
  intro plan mem same i hi hcap
  exact (fee i hi).trans ((sealed_rules k ord price ho hc mem same) (a i) (ha i hi) hcap)
end Height2307Companion
