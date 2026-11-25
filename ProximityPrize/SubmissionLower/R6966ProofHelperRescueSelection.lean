import ProximityPrize.SubmissionLower.R6966ProofHelperRescueSource

set_option Elab.async false

namespace Research6966.HelperRescueSelection
open Finset Polynomial HelperRescueSource
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (jetDegree seedDegree rowCaps_iff seedDegree_le)
open Lower6960.Rescue6966Source (jetCap seedCap)
open scoped Polynomial
set_option maxHeartbeats 1200000
set_option maxRecDepth 5000

def bandIndex (u : ℕ) : ℕ :=
  if u ≤ 1 then 0 else if u ≤ 3 then 1 else if u ≤ 8 then 2
  else if u ≤ 15 then 3 else if u ≤ 25 then 4 else if u ≤ 40 then 5
  else if u ≤ 50 then 6 else if u ≤ 70 then 7 else 8

private theorem index_le (u : ℕ) : bandIndex u ≤ 8 := by
  unfold bandIndex
  repeat' split
  all_goals decide

def bandUpper (i : ℕ) : ℕ :=
  match i with
  | 0 => 1
  | 1 => 3
  | 2 => 8
  | 3 => 15
  | 4 => 25
  | 5 => 40
  | 6 => 50
  | 7 => 70
  | _ => 92

theorem profile (r : Fin 54) :
    jetCap r = r.val/9+2 ∧ seedCap r = bandUpper (r.val%9) := by
  fin_cases r <;> decide +kernel

def select (a u : ℕ) (ap : 2 ≤ a) (aq : a ≤ 7) : Fin 54 :=
  ⟨9*(a-2)+bandIndex u, by have := index_le u; omega⟩

private theorem selected_band {u : ℕ} (up : 0 < u) (uq : u ≤ 92) :
    lowerFromUpper (bandUpper (bandIndex u)) ≤ u ∧
      u ≤ bandUpper (bandIndex u) ∧
      (QuadraticBudget.band (bandUpper (bandIndex u))).2 = (QuadraticBudget.band u).2 := by
  interval_cases u <;> decide

theorem select_bounds {a u : ℕ} (ap : 2 ≤ a) (aq : a ≤ 7) (up : 0 < u) (uq : u ≤ 92) :
    let r := select a u ap aq
    jetCap r = a ∧ sourceLower r ≤ u ∧ u ≤ seedCap r ∧
      sourceWeight r = (if a = 2 then (QuadraticBudget.band u).2 else a*(131071-lastHeight)-1) := by
  let r := select a u ap aq
  obtain ⟨degree, upper⟩ := profile r
  have idx := index_le u
  have div : r.val/9+2=a := by change (9*(a-2)+bandIndex u)/9+2=a; omega
  have mod : r.val%9=bandIndex u := by change (9*(a-2)+bandIndex u)%9=bandIndex u; omega
  rw [div] at degree
  rw [mod] at upper
  obtain ⟨low,high,weight⟩ := selected_band up uq
  refine ⟨degree, ?_, ?_, ?_⟩
  · rwa [sourceLower, upper]
  · rwa [upper]
  · rw [sourceWeight,degree,upper,weight]

/-- Select the rescue from the actual degree and seed degree of the
common factor. The quadratic branch uses its own band-specific weight
cutoff, and all higher degrees use the physical lower bound. -/
theorem prepare_selected (checked : ∀ r i, Checked (request r i))
    {u deleted} {M : Lower6960.Rescue6966.Model u deleted} {Γ} (F : Lower6960.Rescue6966.Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : firstHeight ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ lastHeight)
    (noPole : ∀ j i,(D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (irr : Irreducible G) (slope : G.natDegree = 1)
    (ap : 2 ≤ jetDegree G) (aq : jetDegree G ≤ 7) (up : 0 < seedDegree G) (uq : seedDegree G ≤ 92)
    (quadratic : jetDegree G = 2 → (QuadraticBudget.band (seedDegree G)).2 ≤
      RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) :
    ∃ R : Lower6960.Rescue6966.Run F Crt G, R.rect = select (jetDegree G) (seedDegree G) ap aq := by
  let r := select (jetDegree G) (seedDegree G) ap aq
  obtain ⟨degree,low,high,weight⟩ := select_bounds ap aq up uq
  change jetCap r=jetDegree G at degree
  have seeded : UsesSeed G := by
    unfold UsesSeed
    by_contra! no
    exact (Nat.not_le_of_lt up) ((seedDegree_le G 0).mpr no)
  have caps : K1_14_2_2.RowCaps G (Lower6960.Rescue6966.primeShape r) :=
    (rowCaps_iff ..).mpr ⟨degree.ge,slope.le,high⟩
  have big : sourceWeight r ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw := by
    by_cases isQuad : jetDegree G = 2
    · exact (weight.trans (ite_eq_left isQuad)).le.trans (quadratic isQuad)
    · have hd : 3 ≤ jetCap r := by omega
      exact high_degree_weight r hi hd phys irr.ne_zero slope degree.le
  have positiveSlope : 0 < G.natDegree := by rw [slope]; exact Nat.zero_lt_one
  exact prepare r (checked r) F Crt lo hi noPole residues phys irr positiveSlope
    seeded caps degree.le low big

#print axioms select_bounds
#print axioms prepare_selected
end Research6966.HelperRescueSelection
