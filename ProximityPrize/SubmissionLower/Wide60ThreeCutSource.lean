/- Full-support adaptation of PR656 (8d1d82a4df2fd3cd347a881c91088431dded323d)
   and the PR658 coupled-chart and sequential-cut proof (fbfa288e5fe2252d30dde0b0b8a065e0df712acb). -/
import ProximityPrize.SubmissionLower.PortFoundation

set_option Elab.async false

namespace Wide60ThreeCutSource
open CJ0 Finset
open scoped BigOperators

def support:Source:=⟨57,78,23,11,fullBox 78 23 11⟩

theorem shapeOK : ShapeOK support := by
  have hmem:=mem_fullBox (B:=78) (J:=23) (C:=11) (by decide) (by decide)
  refine ⟨by decide,by decide,by decide,by decide,by decide,?_,?_⟩
  · intro j hj
    exact (hmem j).mp hj
  · intro j hj _
    have h:=(hmem j).mp hj
    apply (hmem _).mpr
    exact ⟨by simpa [Jet.q,Jet.a,Jet.b,Jet.c] using
      (show j.a-1+j.b+j.c≤78 by unfold Jet.q at h; omega),h.2⟩

theorem facet (j : Jet) (hj : j ∈ support.E) : j.b+3*j.c ≤ 34 := by
  obtain ⟨_,hv,hc⟩:=(mem_fullBox (B:=78) (J:=23) (C:=11) (by decide) (by decide) j).mp hj
  unfold Jet.v at hv
  omega

private def width (c b:ℕ):=78-(b+c)+1
private def bRange (c:ℕ):=range (23-2*c+1)
private def countRow (c:ℕ) := ∑ b ∈ bRange c,width c b
private def totalRow (c : ℕ) := ∑ b ∈ bRange c,
  (width c b*(width c b-1)/2+width c b*(b+c))
private def indexRow (c:ℕ) := ∑ b ∈ bRange c,width c b*(b+2*c)

private theorem ragged : support.E =
    (range 12).sigma (fun c => (bRange c).sigma (fun b => range (width c b))):=by
  rfl

theorem moments : support.E.card = 10530 ∧ (∑ j ∈ support.E, j.q) = 469196 ∧
    (∑ j ∈ support.E,j.v)=155662:=by
  have h₁ : ∑ c ∈ range 12,countRow c=10530:=by decide +kernel
  have h₂ : ∑ c ∈ range 12,totalRow c=469196:=by decide +kernel
  have h₃ : ∑ c ∈ range 12,indexRow c=155662:=by decide +kernel
  refine ⟨?_,?_,?_⟩
  · simpa only [ragged,card_sigma,card_range,countRow] using h₁
  · rw [ragged, sum_sigma]
    refine Eq.trans (sum_congr rfl (fun c _ => ?_)) h₂
    simp only [sum_sigma,totalRow,Jet.q,Jet.a,Jet.b,Jet.c]
    apply sum_congr rfl
    intro b _
    simp only [Nat.add_assoc, sum_add_distrib, sum_range_id, sum_const, card_range,
      smul_eq_mul,Nat.mul_add]
  · simpa only [ragged, sum_sigma, indexRow, Jet.v, Jet.b, Jet.c, sum_const, card_range,
      smul_eq_mul] using h₃


def supportLow:Source:=⟨57,78,23,10,fullBox 78 23 10⟩

theorem shapeOKLow : ShapeOK supportLow := by
  have hmem:=mem_fullBox (B:=78) (J:=23) (C:=10) (by decide) (by decide)
  refine ⟨by decide,by decide,by decide,by decide,by decide,?_,?_⟩
  · intro j hj
    exact (hmem j).mp hj
  · intro j hj _
    have h:=(hmem j).mp hj
    apply (hmem _).mpr
    exact ⟨by simpa [Jet.q,Jet.a,Jet.b,Jet.c] using
      (show j.a-1+j.b+j.c≤78 by unfold Jet.q at h; omega),h.2⟩

theorem facetLow (j : Jet) (hj : j ∈ supportLow.E) : j.b+3*j.c ≤ 33 := by
  obtain ⟨_,hv,hc⟩:=(mem_fullBox (B:=78) (J:=23) (C:=10) (by decide) (by decide) j).mp hj
  unfold Jet.v at hv
  omega

private def widthLow (c b:ℕ):=78-(b+c)+1
private def countRowLow (c:ℕ) := ∑ b ∈ bRange c,widthLow c b
private def totalRowLow (c : ℕ) := ∑ b ∈ bRange c,
  (widthLow c b*(widthLow c b-1)/2+widthLow c b*(b+c))
private def indexRowLow (c:ℕ) := ∑ b ∈ bRange c,widthLow c b*(b+2*c)

private theorem raggedLow : supportLow.E =
    (range 11).sigma (fun c => (bRange c).sigma (fun b => range (widthLow c b))):=by
  rfl

theorem momentsLow : supportLow.E.card = 10395 ∧ (∑ j ∈ supportLow.E, j.q) = 463155 ∧
    (∑ j ∈ supportLow.E,j.v)=152625:=by
  have h₁ : ∑ c ∈ range 11,countRowLow c=10395:=by decide +kernel
  have h₂ : ∑ c ∈ range 11,totalRowLow c=463155:=by decide +kernel
  have h₃ : ∑ c ∈ range 11,indexRowLow c=152625:=by decide +kernel
  refine ⟨?_,?_,?_⟩
  · simpa only [raggedLow,card_sigma,card_range,countRowLow] using h₁
  · rw [raggedLow, sum_sigma]
    refine Eq.trans (sum_congr rfl (fun c _ => ?_)) h₂
    simp only [sum_sigma,totalRowLow,Jet.q,Jet.a,Jet.b,Jet.c]
    apply sum_congr rfl
    intro b _
    simp only [Nat.add_assoc, sum_add_distrib, sum_range_id, sum_const, card_range,
      smul_eq_mul,Nat.mul_add]
  · simpa only [raggedLow, sum_sigma, indexRowLow, Jet.v, Jet.b, Jet.c, sum_const, card_range,
      smul_eq_mul] using h₃

end Wide60ThreeCutSource
