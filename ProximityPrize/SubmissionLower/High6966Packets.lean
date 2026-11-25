import ProximityPrize.SubmissionLower.R6966ProofNearBook
import ProximityPrize.SubmissionLower.High6966Main20142Charge
import ProximityPrize.SubmissionLower.High6966Main15000Charge
import ProximityPrize.SubmissionLower.High6966Main13200Charge

set_option Elab.async false

namespace Research6966.NearPacket
open Finset
open K1 (K)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open K1_14_2_2 (mass mass_mono)
open Lower6960.Rescue6966 (Model Family OnSurface)
open NearBook (Packet Paid)
open scoped Classical
noncomputable section
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false

theorem main20142 {u del} {M:Model u del} {Γ} {F:Family M Γ} {D:PoleData M.overhead.toNat}
    {Crt:CRTLift D} (R:Lower6960.High6966Main20142.Rows F Crt) (hi:M.overhead.toNat≤2499)
    (nop:∀ j i,(D.block j).eval (nodeL i)≠0)
    (res:∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ b:Packet M Crt,Paid b 240122305198674767 1828374077815 7736 220 ∧
      ∀ γ∈R.marks,γ∈b.paid ∨ ∃ q∈b.parents,OnSurface F q γ := by
  obtain ⟨ini,C,S,geom,orig,cover⟩:=R.main_prefix hi nop res
  let b:Packet M Crt:=⟨C.paid,S,ini.final,fun J h=>(ini.kept_geom (mem_filter.mp h).1).1,geom,orig⟩
  have cap (k:Fin 4) : mass ini.final k≤⌊Lower6960.High6966Main20142.history 16 k⌋₊ := by
    have s:=mass_mono (show ini.final⊆ini.kept 16 from filter_subset _ _) k
    exact Nat.le_floor (((Nat.cast_le (α:=ℚ)).mpr s).trans (ini.cap_kept (i:=16) (by decide) k))
  refine ⟨b,⟨(C.paid_count hi).trans Lower6960.High6966Main20142.main_fee_bound,?_,?_⟩,cover⟩
  · exact (cap 1).trans (by decide +kernel : ⌊Lower6960.High6966Main20142.history 16 1⌋₊≤7736)
  · exact (cap 0).trans (by decide +kernel : ⌊Lower6960.High6966Main20142.history 16 0⌋₊≤220)
#print axioms main20142

theorem main15000 {u del} {M:Model u del} {Γ} {F:Family M Γ} {D:PoleData M.overhead.toNat}
    {Crt:CRTLift D} (R:Lower6960.High6966Main15000.Rows F Crt) (hi:M.overhead.toNat≤2499)
    (nop:∀ j i,(D.block j).eval (nodeL i)≠0)
    (res:∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ b:Packet M Crt,Paid b 185233047747540462 1838347228855 6160 220 ∧
      ∀ γ∈R.marks,γ∈b.paid ∨ ∃ q∈b.parents,OnSurface F q γ := by
  obtain ⟨ini,C,S,geom,orig,cover⟩:=R.main_prefix hi nop res
  let b:Packet M Crt:=⟨C.paid,S,ini.final,fun J h=>(ini.kept_geom (mem_filter.mp h).1).1,geom,orig⟩
  have cap (k:Fin 4) : mass ini.final k≤⌊Lower6960.High6966Main15000.history 16 k⌋₊ := by
    have s:=mass_mono (show ini.final⊆ini.kept 16 from filter_subset _ _) k
    exact Nat.le_floor (((Nat.cast_le (α:=ℚ)).mpr s).trans (ini.cap_kept (i:=16) (by decide) k))
  refine ⟨b,⟨(C.paid_count hi).trans Lower6960.High6966Main15000.main_fee_bound,?_,?_⟩,cover⟩
  · exact (cap 1).trans (by decide +kernel : ⌊Lower6960.High6966Main15000.history 16 1⌋₊≤6160)
  · exact (cap 0).trans (by decide +kernel : ⌊Lower6960.High6966Main15000.history 16 0⌋₊≤220)
#print axioms main15000

theorem main13200 {u del} {M:Model u del} {Γ} {F:Family M Γ} {D:PoleData M.overhead.toNat}
    {Crt:CRTLift D} (R:Lower6960.High6966Main13200.Rows F Crt) (hi:M.overhead.toNat≤2499)
    (nop:∀ j i,(D.block j).eval (nodeL i)≠0)
    (res:∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ b:Packet M Crt,Paid b 167997887646643864 1849635312035 5608 220 ∧
      ∀ γ∈R.marks,γ∈b.paid ∨ ∃ q∈b.parents,OnSurface F q γ := by
  obtain ⟨ini,C,S,geom,orig,cover⟩:=R.main_prefix hi nop res
  let b:Packet M Crt:=⟨C.paid,S,ini.final,fun J h=>(ini.kept_geom (mem_filter.mp h).1).1,geom,orig⟩
  have cap (k:Fin 4) : mass ini.final k≤⌊Lower6960.High6966Main13200.history 16 k⌋₊ := by
    have s:=mass_mono (show ini.final⊆ini.kept 16 from filter_subset _ _) k
    exact Nat.le_floor (((Nat.cast_le (α:=ℚ)).mpr s).trans (ini.cap_kept (i:=16) (by decide) k))
  refine ⟨b,⟨(C.paid_count hi).trans Lower6960.High6966Main13200.main_fee_bound,?_,?_⟩,cover⟩
  · exact (cap 1).trans (by decide +kernel : ⌊Lower6960.High6966Main13200.history 16 1⌋₊≤5608)
  · exact (cap 0).trans (by decide +kernel : ⌊Lower6960.High6966Main13200.history 16 0⌋₊≤220)
#print axioms main13200

theorem rescue {u del} {M:Model u del} {Γ} {F:Family M Γ} {D:PoleData M.overhead.toNat}
    {Crt:CRTLift D} {G:Jet} (R:Lower6960.Rescue6966.Run F Crt G) (hi:M.overhead.toNat≤2499)
    (nop:∀ j i,(D.block j).eval (nodeL i)≠0)
    (res:∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ b:Packet M Crt,Paid b (Lower6960.Rescue6966.paidCap R.rect) (Lower6960.Rescue6966.retainedCredit R.rect)
      ((Lower6960.Rescue6966Source.data R.rect).bound 1) ((Lower6960.Rescue6966Source.data R.rect).bound 0) ∧
      ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → γ∈b.paid ∨ ∃ q∈b.parents,OnSurface F q γ := by
  obtain ⟨C,S,geom,orig,cover⟩:=R.paid_packet nop res
  let b:Packet M Crt:=⟨C.paid,S,R.final,fun J h=>(R.parent_geom (mem_filter.mp h).1).1,geom,orig⟩
  exact ⟨b,⟨(C.paid_count hi).trans (Lower6960.Rescue6966.rescue_fee_bound R.rect),
    R.terminal_cap 1,R.terminal_cap 0⟩,cover⟩
#print axioms rescue
end
end Research6966.NearPacket
