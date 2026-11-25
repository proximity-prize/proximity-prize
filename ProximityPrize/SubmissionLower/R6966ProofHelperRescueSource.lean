import ProximityPrize.SubmissionLower.R6966ProofHelperWindowIntervals
import ProximityPrize.SubmissionLower.R6966ProofHelperWeightCap
import ProximityPrize.SubmissionLower.R6966ProofQuadraticBudget
import ProximityPrize.SubmissionLower.High6966RescueGeometry

set_option Elab.async false

namespace Research6966.HelperRescueSource
open Finset Polynomial
open K1_14 (Shape Jet L shapeSum triangle)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open HelperAvoidance (debitAt triSlots)
open HelperWindowIntervals (cutoff bound slotLimit triangle_tail)
open HelperWindowPrefix (volume)
open Lower6960.Rescue6966Source (bank reserve jetCap seedCap)
open scoped Polynomial
set_option maxRecDepth 5000
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

abbrev agreement : ℕ := 179769
abbrev firstHeight : ℕ := 2330
abbrev lastHeight : ℕ := 2499

structure Request where
  bank : P1_7.Bank
  reserve : ℕ
  degree : ℕ
  lower : ℕ
  weight : ℕ

def lowerFromUpper (u : ℕ) : ℕ :=
  if u ≤ 1 then 1 else if u ≤ 3 then 2 else if u ≤ 8 then 4
  else if u ≤ 15 then 9 else if u ≤ 25 then 16 else if u ≤ 40 then 26
  else if u ≤ 50 then 41 else if u ≤ 70 then 51 else 71

def sourceLower (r : Fin 54) : ℕ := lowerFromUpper (seedCap r)

def sourceWeight (r : Fin 54) : ℕ :=
  if jetCap r = 2 then (QuadraticBudget.band (seedCap r)).2
  else jetCap r*(131071-lastHeight)-1

def request (r : Fin 54) (i : Fin 17) : Request :=
  ⟨bank r i,reserve r i,jetCap r,sourceLower r,sourceWeight r⟩

def Request.top (q : Request) (h : ℕ) : ℕ := cutoff q.bank.shape agreement h q.reserve

def Positive (q : Request) (lo hi : ℕ) : Prop :=
  let S := q.bank.shape
  let width := triangle S.U
  width*q.bank.nodeRows+hi*(2*(S.U+1))*q.bank.poleMoment+
      bound S agreement q.reserve lo hi q.degree 1 q.weight (slotLimit S S.U q.lower)
        (triSlots S.U q.lower) <
    width*volume (q.top hi) S.B S.J (131071-lo)

instance (q : Request) (lo hi : ℕ) : Decidable (Positive q lo hi) := by
  unfold Positive
  infer_instance

def Cover (q : Request) (lo : ℕ) : List ℕ → Prop
  | [] => lo = lastHeight+1
  | hi::next => lo ≤ hi ∧ hi ≤ lastHeight ∧ Positive q lo hi ∧ Cover q (hi+1) next

private theorem cover_height {q : Request} {ends : List ℕ} {lo h : ℕ}
    (c : Cover q lo ends) (hl : lo ≤ h) (hh : h ≤ lastHeight) :
    ∃ bot top, bot ≤ h ∧ h ≤ top ∧ top ≤ lastHeight ∧ Positive q bot top := by
  induction ends generalizing lo with
  | nil =>
    change lo=lastHeight+1 at c
    omega
  | cons top ends ih =>
    obtain ⟨_,htop,cert,more⟩ := c
    by_cases hb : h ≤ top
    · exact ⟨lo,top,hl,hb,htop,cert⟩
    · exact ih more (by omega)

structure Checked (q : Request) : Prop where
  nodes : P1_7_1.nodeRows q.bank.shape = q.bank.nodeRows
  pole : P1_7_1.groupedPoleMoment q.bank.shape.B q.bank.shape.J ≤ q.bank.poleMoment
  narrow : q.bank.shape.J < 131071-lastHeight
  room : q.bank.shape.B*(131071-firstHeight)+2*firstHeight*q.reserve < q.bank.shape.m*agreement
  reserve_fit : 2*q.reserve ≤ q.bank.shape.B
  intervals : ∃ ends : List ℕ, Cover q firstHeight ends

theorem node_check (b : P1_7.Bank) (hm : 2*b.shape.J ≤ b.shape.m)
    (hB : b.shape.m+b.shape.J ≤ b.shape.B+1)
    (check : 262144*P1_7_1_2.sixPerNode (b.shape.m-2*b.shape.J) b.shape.J = 6*b.nodeRows) :
    P1_7_1.nodeRows b.shape = b.nodeRows := by
  have exactRows := P1_7_1_2.six_nodeRows b.shape hm hB
  rw [check] at exactRows
  omega

theorem Checked.width {q : Request} (cert : Checked q) {h : ℕ}
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) :
    q.bank.shape.B*(131071-h) < q.top h := by
  have lo' : 2330 ≤ h := lo
  have hi' : h ≤ 2499 := hi
  have delta : 131071-firstHeight = (131071-h)+(h-firstHeight) := by
    change 128741=(131071-h)+(h-2330)
    omega
  have res : 2*h*q.reserve = 2*firstHeight*q.reserve+(h-firstHeight)*(2*q.reserve) := by
    conv_lhs => rw [show h = firstHeight+(h-firstHeight) by omega]
    ring
  have more := Nat.mul_le_mul_left (h-firstHeight) cert.reserve_fit
  have atStart := cert.room
  rw [delta,Nat.mul_add] at atStart
  rw [Nat.mul_comm (h-firstHeight) q.bank.shape.B] at more
  change q.bank.shape.B*(131071-h) < q.bank.shape.m*agreement-2*h*q.reserve
  rw [res]
  omega

theorem Checked.debit_positive {q : Request} (cert : Checked q) {h : ℕ}
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) :
    P1_7.debit h q.bank+
        (∑ W ∈ range (q.top h), debitAt q.bank.shape h (q.top h) W q.degree 1 q.weight
          (triSlots q.bank.shape.U q.lower)) <
      triangle q.bank.shape.U*shapeSum q.bank.shape (fun t j => q.top h+j-t*(131071-h)) := by
  obtain ⟨ends,c⟩ := cert.intervals
  obtain ⟨bot,top,hb,ht,htop,num⟩ := cover_height c lo hi
  have narrow := cert.narrow.trans_le (Nat.sub_le_sub_left htop 131071)
  have hp : 0 < h := (show 0 < firstHeight by decide).trans_le lo
  let S := q.bank.shape
  have result := HelperWindowIntervals.positive S agreement q.reserve bot top h q.degree 1 q.weight
    (slotLimit S S.U q.lower) (triangle S.U) (2*(S.U+1)) q.bank.nodeRows q.bank.poleMoment
    (triSlots S.U q.lower) hp hb ht narrow (triangle_tail S q.degree S.U q.lower) num
  simpa only [P1_7.debit,Request.top,S,Nat.mul_left_comm h 2,Nat.mul_assoc] using result

theorem avoiding_rows (r : Fin 54) (checked : ∀ i, Checked (request r i))
    {h : ℕ} (lo : firstHeight ≤ h) (hi : h ≤ lastHeight)
    {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L) {G : Jet}
    (phys : HelperPhysicalModel.Model Crt G) (irr : Irreducible G) (slope : 0 < G.natDegree)
    (seeded : UsesSeed G) (degree : jetCap r ≤ jetDegree G) (seed : sourceLower r ≤ seedDegree G)
    (weight : sourceWeight r ≤ RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw) :
    ∀ i, ∃ Q ∈ evaluated Crt word (bank r i).shape (Lower6960.Rescue6966Source.cutoff h r i), ¬G∣Q := by
  intro i
  let q := request r i
  have cert : Checked q := checked i
  obtain ⟨_,_,charB,charU,_⟩ := Lower6960.Rescue6966Source.shape_guards r i
  have hp : 0<h := (show 0 < firstHeight by decide).trans_le lo
  have hl : h≤131070 := hi.trans (by decide)
  have wide := cert.width lo hi
  have pos : 0 < q.top h := (Nat.zero_le _).trans_lt wide
  exact HelperAvoidance.triangle_avoiding hp hl Crt word q.bank phys irr slope seeded charU
    degree slope weight seed charB pos wide.le cert.nodes cert.pole (cert.debit_positive lo hi)

/-- The ordinary physical weight lower bound supplies every degree-three
through degree-seven rescue cutoff from the actual common factor. -/
theorem high_degree_weight (r : Fin 54) {h : ℕ} (hi : h ≤ lastHeight) (hd : 3 ≤ jetCap r)
    {D : PoleData h} {Crt : CRTLift D} {G : Jet} (phys : HelperPhysicalModel.Model Crt G)
    (nz : G ≠ 0) (slope : G.natDegree = 1) (degree : jetCap r ≤ jetDegree G) :
    sourceWeight r ≤ RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw := by
  have present := HelperWeightCap.weight_lower phys nz (131071-h) (by have h' : h ≤ 2499 := hi; omega)
  rw [slope] at present
  have fit := Nat.mul_le_mul (Nat.sub_le_sub_left hi 131071) degree
  rw [sourceWeight,ite_eq_right (by omega),Nat.mul_comm (jetCap r)]
  omega

/-- Every certified source row is passed to the actual 17-stage rescue of
the marked P1 family. -/
theorem prepare (r : Fin 54) (checked : ∀ i, Checked (request r i))
    {u deleted} {M : Lower6960.Rescue6966.Model u deleted} {Γ} (F : Lower6960.Rescue6966.Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : firstHeight ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ lastHeight)
    (noPole : ∀ j i,(D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (irr : Irreducible G) (slope : 0 < G.natDegree)
    (seeded : UsesSeed G) (caps : RowCaps G (Lower6960.Rescue6966.primeShape r))
    (degree : jetCap r ≤ jetDegree G) (seed : sourceLower r ≤ seedDegree G)
    (weight : sourceWeight r ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ R : Lower6960.Rescue6966.Run F Crt G, R.rect = r :=
  Lower6960.Rescue6966.prepare_from_rows F Crt hi noPole residues r irr caps
    (avoiding_rows r checked lo hi Crt (Lower6960.Rescue6966.word M) phys irr slope seeded degree seed weight)

#print axioms avoiding_rows
#print axioms high_degree_weight
#print axioms prepare
end Research6966.HelperRescueSource
