import ProximityPrize.SubmissionLower.ZucFfdd
set_option Elab.async false
set_option autoImplicit true
set_option Elab.async false
namespace qQ76XXb
noncomputable section
open Polynomial Finset
open P6 (K I node)
open P6_6 (Messages)
open dN (aB7 DA)
private theorem pieces_capacity {Γ:Finset K} (C:DA Γ) (k :ℕ)
    (h : ∀ i,(C.dO i).card≤k*C.degree i) :C.union.card≤k*C.total:= by
  classical
  calc
    _ ≤ ∑ i,(C.dO i).card:=card_biUnion_le
    _ ≤ ∑ i,k*C.degree i:=sum_le_sum fun i _=>h i
    _ = _:= by rw [DA.total,mul_sum]
private theorem cbH {w Γ s} (C:DA Γ) (h:Messages w Γ s)
    (hc:C.qv s) (hd : ∀ i,0<C.degree i) :C.union.card≤2*C.total:= by
  apply pieces_capacity
  intro i
  have hbound:=P6_6_5.bv5 (h.mono (C.subset i)) (C.degree i)
    (fun j=>hc i (node j) (w j))
  have hpos :=hd i
  omega
private theorem a8X {w Γ s d} (h:Messages w Γ s)
    (hs :aB7 Γ s d) (hd:0<d) :Γ.card≤4*d:= by
  classical
  have hsection (i:I) (hi : ∃ γ∈Γ,(s γ).eval (node i)≠w i) :
      (Γ.filter fun γ=>(s γ).eval (node i)=w i).card≤2*d:= by
    obtain ⟨C,hC,hc,hpos,hdeg⟩:=hs (node i) (w i) hi
    exact (card_le_card hC).trans
      ((cbH C (h.mono (filter_subset _ _)) hc hpos).trans
        (Nat.mul_le_mul_left 2 hdeg))
  have :=P6_6_5.bv5 h (2*d) hsection
  omega
theorem bgc {w Γ s} (C:DA Γ) (h:Messages w Γ s)
    (hc:C.uG s) (hd : ∀ i,0<C.degree i) :C.union.card≤4*C.total :=
  pieces_capacity C 4 (fun i=>a8X (h.mono (C.subset i)) (hc i) (hd i))
end
end qQ76XXb
