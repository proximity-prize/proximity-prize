import ProximityPrize.SubmissionLower.Z6970CompanionCount
set_option autoImplicit false
set_option Elab.async false

namespace Height2307Companion
open K1_13 (Shape InBox)
open Finset
open scoped BigOperators

structure Rule where
  band : ℕ
  cap : Shape
  byDegree : Bool
  rate : ℕ

def normBox (r : Shape) : Shape :=
  let t := number r.b r.j r.t
  ⟨r.b,min r.j (2*r.b+t),t⟩

theorem fit_norm {x r : Shape} (hx : legal x) (hr : InBox x r) : InBox x (normBox r) := by
  obtain ⟨h0,hj,hb,hi⟩ := hx
  obtain ⟨hB,hJ,hT⟩ := hr
  have h : x.t ≤ number r.b r.j r.t := le_min (hb.trans hB) (le_min (by omega) hT)
  exact ⟨hB,le_min hJ (by omega),h⟩

def applies (k : ℕ) (rest : Shape) (r : Rule) : Bool :=
  let n := normBox rest
  decide (k=r.band ∧ n.b≤r.cap.b ∧ n.j≤r.cap.j ∧ n.t≤r.cap.t)

def select (k : ℕ) (rest : Shape) : List Rule → Option ℕ
  | [] => none
  | h :: tail =>
    let next := select k rest tail
    if applies k rest h then
      let d := bill h.byDegree h.rate rest.b rest.j rest.t
      some (match next with | none => d | some v => min d v)
    else next

theorem select_spec {n k : ℕ} {rest : Shape} {rules : List Rule}
    (h : ∀ r ∈ rules, applies k rest r = true → n ≤ bill r.byDegree r.rate rest.b rest.j rest.t)
    {debt : ℕ} (hd : select k rest rules = some debt) : n ≤ debt := by
  induction rules generalizing debt with
  | nil => simp [select] at hd
  | cons a rs ih =>
    have tail {v : ℕ} (he : select k rest rs = some v) : n ≤ v :=
      ih (fun r hr => h r (List.mem_cons_of_mem a hr)) he
    by_cases yes : applies k rest a = true
    · have ha := h a (List.mem_cons_self ..) yes
      cases he : select k rest rs with
      | none => simp [select,yes,he] at hd; omega
      | some v =>
        have hv := tail he
        simp [select,yes,he] at hd
        omega
    · simp [select,yes] at hd
      exact tail hd

def fromRules (k : ℕ) (r : Shape) (rules : List Rule) : Option ℕ :=
  if number r.b r.j r.t=0 then some 0 else select k r rules

theorem fromRules_sound {ι : Type*} {s : Finset ι} {a : ι → Shape} {cost : ι → ℕ}
    {k debt : ℕ} {r : Shape} {rules : List Rule}
    (hbook : fromRules k r rules = some debt)
    (ha : ∀ i ∈ s, legal (a i))
    (hb : (∑ i ∈ s, (a i).b) ≤ r.b)
    (hj : (∑ i ∈ s, (a i).j) ≤ r.j)
    (ht : (∑ i ∈ s, (a i).t) ≤ r.t)
    (prices : ∀ t ∈ rules, k=t.band → ∀ i ∈ s, InBox (a i) t.cap →
        cost i ≤ charge t.byDegree t.rate (a i)) : (∑ i ∈ s, cost i) ≤ debt := by
  classical
  have fits (i) (hi : i ∈ s) : InBox (a i) (normBox r) := fit_norm (ha i hi) (member_fits hb hj ht hi)
  by_cases hz : number r.b r.j r.t = 0
  · have he : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hpos := (ha i hi).1
      have ht0 := (fits i hi).2.2
      change (a i).t ≤ number r.b r.j r.t at ht0
      omega
    simp [he]
  · apply select_spec (rules := rules) (k := k) (rest := r) _ (by simpa [fromRules,hz] using hbook)
    intro t mem hy
    have ok : k=t.band ∧ (normBox r).b≤t.cap.b ∧ (normBox r).j≤t.cap.j ∧ (normBox r).t≤t.cap.t := of_decide_eq_true hy
    apply sum_le_bill ha hb hj ht
    intro i hi
    have f := fits i hi
    exact prices t mem ok.1 i hi ⟨f.1.trans ok.2.1,f.2.1.trans ok.2.2.1,f.2.2.trans ok.2.2.2⟩
end Height2307Companion
