import ProximityPrize.SubmissionLower.Z29Fskc
import ProximityPrize.SubmissionLower.ZMwIPwd
set_option Elab.async false
section
set_option autoImplicit true
namespace q8kPhwd
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
local notation "asr" h "," mm "," qq "," nn "," aa "," dd "," bb "," cc =>
  checked (lo:=2964) (m:=mm) (mid :=qq) (n:=nn) (a :=aa) (b:=bb) (c:=cc)
    h rfl (numeric qq nn dd bb rfl rfl) rfl
private theorem r0:bvj 2964 8=(0x6dc21a66fd0:ℕ) :=numeric 2964 8 0x25a6fd8625 0x6dc21a66fd0 rfl rfl
private theorem r1 :bvj 2964 16=(0xd9e7d0177a0:ℕ) :=asr r0,8,2972,8,0x6dc21a66fd0,0x2559f8cbc5,0x6c25b5b07d0,0xd9e7d0177a0
private theorem r2 :bvj 2964 24=(0x14474938fa88:ℕ) :=asr r1,16,2980,8,0xd9e7d0177a0,0x250b6b6d0d,0x6a8cc3782e8,0x14474938fa88
theorem total2 :bvj 2964 32=(0x1ad6be780590:ℕ) :=asr r2,24, 2988,8,0x14474938fa88,0x24bb6cf512,0x68f753f0b08,0x1ad6be780590
end q8kPhwd
end
section
set_option autoImplicit true
namespace qkrKkqa
noncomputable section
open Finset
open scoped BigOperators Classical
open q6nKpZc
open q7F2qKe (origins lossTail partMass stopCount stops)
open cu (Jet)
open gT (Ambient)
open pI (mass)
open TD (J2 bfw)
variable {b u del M Γ F} {x : @Input b u del M Γ F} (C:aAT F b x)
def combine (S:ℕ→Jet→Finset (Ideal Ambient)) :Finset (Ideal Ambient) :=
  (origins b).biUnion fun o=>(C.factors o).biUnion (S o)
theorem dNW {S I} :
    I∈combine C S ↔ ∃ o∈origins b,∃ f∈C.factors o,I∈S o f := by
  simp only [combine,mem_biUnion]
private theorem mass_biUnion {α:Type*} (s :Finset α) (S:α→Finset (Ideal Ambient))
    (h: (↑s :Set α).PairwiseDisjoint S) (k :Fin 4) :
    J2 (s.biUnion S) k = ∑ i∈s,J2 (S i) k := by
  simp only [J2,mass,sum_biUnion h,Nat.cast_sum]
theorem mass_combine {S:ℕ→Jet→Finset (Ideal Ambient)}
    (h : ∀ o∈origins b,∀ f∈C.factors o,S o f⊆C.parents o f) (k :Fin 4) :
    J2 (combine C S) k = ∑ o∈origins b,∑ f∈C.factors o,J2 (S o f) k := by
  unfold combine
  rw [mass_biUnion]
  · apply sum_congr rfl
    intro o ho
    apply mass_biUnion
    intro f hf g hg hne
    apply disjoint_left.mpr
    intro I hI hJ
    exact hne (C.parent_unique o ho f hf o ho g hg I (h o ho f hf hI) (h o ho g hg hJ)).2
  · intro o ho v hv hne
    apply disjoint_left.mpr
    intro I hI hJ
    obtain ⟨f,hf,hI⟩:=mem_biUnion.mp hI
    obtain ⟨g,hg,hJ⟩:=mem_biUnion.mp hJ
    exact hne (C.parent_unique o ho f hf v hv g hg I (h o ho f hf hI) (h v hv g hg hJ)).1
theorem sum_stopped_le (o:ℕ) (f :Jet) (J:Finset ℕ) {i:ℕ}
    (h : ∀ j∈J,i≤j) (k :Fin 4) :
    (∑ j∈J,J2 (stopped C o f j) k)≤J2 (QV C o f i) k := by
  have dis : (↑J:Set ℕ).PairwiseDisjoint (stopped C o f) := by
    intro s hs t ht hne
    apply disjoint_left.mpr
    intro I hI hJ
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (stopped_mem hI).2.1 ((stopped_mem hJ).2.2 s hlt)
    · exact (stopped_mem hJ).2.1 ((stopped_mem hI).2.2 t hgt)
  rw [← mass_biUnion J _ dis]
  apply bfw
  intro I hI
  obtain ⟨j,hj,hm⟩:=mem_biUnion.mp hI
  exact live_anti (h j hj) (mem_filter.mp hm).1
theorem lossTail_le (o i:ℕ) (k :Fin 4) :
    lossTail b C.factors (stopped C) o i k≤partMass C.factors (QV C) o i k := by
  unfold lossTail partMass
  rw [sum_comm]
  exact sum_le_sum fun f _=>sum_stopped_le C o f _ (fun _ hj=>(mem_filter.mp hj).2) k
theorem live_zero (o:ℕ) (f :Jet) :QV C o f 0=C.parents o f := by
  simp [QV]
theorem exhaust {o f I} (h:I∈C.parents o f) :
    I∈QV C o f (stopCount b) ∨ ∃ j∈stops b,I∈stopped C o f j:= by
  by_cases hp : ∀ j<stopCount b,Pass x j I
  · exact Or.inl (mem_filter.mpr ⟨h,hp⟩)
  · push Not at hp
    obtain ⟨j,hj,hfail⟩:=hp
    let p:= fun t=>t<stopCount b ∧ ¬ Pass x t I
    have hex : ∃ t,p t:=⟨j,hj,hfail⟩
    have hm:=Nat.find_spec hex
    refine Or.inr ⟨Nat.find hex,mem_range.mpr hm.1,mem_filter.mpr ⟨?_,hm.2⟩⟩
    refine mem_filter.mpr ⟨h,fun i hi => ?_⟩
    by_contra hn
    exact Nat.find_min hex hi ⟨hi.trans hm.1,hn⟩
end
end qkrKkqa
end
