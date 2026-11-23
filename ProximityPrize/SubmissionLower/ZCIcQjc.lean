import ProximityPrize.SubmissionLower.ZXrG2Fd
import ProximityPrize.SubmissionLower.Z2dBXLe
import ProximityPrize.SubmissionLower.ZU4mhUb
set_option Elab.async false
open _root_ renaming Finset.card_le_card → z1q, Finset.card_union_le → z2s, Finset.filter_subset → zT0, Finset.mem_union_left → zDk, Finset.mem_union_right → zMj, Nat.add_le_add_right → zlr, Nat.mul_le_mul_left → zBI
set_option autoImplicit true
namespace P6_6_5
noncomputable section
open P6 (K)
open P6_6 (Messages m6 mW)
open aR (af ao embed extend cK ceilDiv)
open oR (qg Rr)
open scoped Polynomial
def c1 :Prop :=
  ∀ w Γ s,Messages w Γ s → ∀ v,v≤ m6.t →
    ∀ n (f :Fin n→af 3),Zl v f →
    (∀ γ∈Γ,∃ i,qg 2 (f i) (extend (s γ)) ∧ ¬ Fb (f i)) →
    Nonempty (a0Z v w Γ s)
def c2 :Prop :=
  ∀ w Γ s,Messages w Γ s → ∀ v,v≤ m6.t →
    ∀ n (f :Fin n→af 3),Zl v f →
    (∀ γ∈Γ,∃ i,qg 2 (f i) (extend (s γ))∧Fb (f i)) →
    ∃ C:Rr w Γ s,Γ⊆C.CF∧C.n≤(mW v).b ∧
      C.BJ≤P6_6.gZ*(mW v).b
private theorem fX6 {w Γ s} (h:Messages w Γ s) (u:ao[X][X]) (hu:u≠0)
    (hr : ∀ γ∈Γ,u.eval (extend (s γ))=0) :
    Γ.card≤u.natDegree := by
  classical
  let a :K→ao[X] := fun γ=>extend (s γ)
  have hinj:Set.InjOn a (Γ:Set K) :=
    fun _ hx _ hy heq=>h.distinct hx hy (Polynomial.map_injective embed embed.injective heq)
  have hb: (Γ.image a).card≤u.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro b hb
    change b∈Γ.image a at hb
    obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hb
    exact (Polynomial.mem_roots hu).mpr (hr γ hγ)
  rw [Finset.card_image_of_injOn hinj] at hb
  exact hb
private theorem ebC {w Γ s v} (h:Messages w Γ s) (hv :v≤ m6.t)
    (q:af 2) (hq:a93 v q) (hr : ∀ γ∈Γ,cK q (extend (s γ))=0) :
    46402*Γ.card≤82317*bGL v+46402*O1 v^2 := by
  classical
  obtain ⟨n,f,u,hf,hu,hd,hc⟩:=ebE v hv q hq
  let iy :=Γ.filter fun γ=>u.eval (extend (s γ))=0
  let regular :=Γ.filter fun γ => ∃ i,qg 1 (f i) (extend (s γ))
  have hr₀:iy.card≤O1 v*(O1 v - 1) :=
    (fX6 (h.mono (zT0 _ _)) u hu
      (fun _ hγ=>(Finset.mem_filter.mp hγ).2)).trans hd
  obtain ⟨C,hC,hn,hcap⟩ :=
    ebI (h.mono (Δ:=regular) (zT0 _ _)) hv f hf
      (fun _ hγ=>(Finset.mem_filter.mp hγ).2)
  have hr₁:46402*regular.card≤82317*C.BJ+46402*C.n :=
    (zBI _ (z1q hC)).trans
      (bJG C (h.mono (zT0 _ _)))
  have Eh:Γ⊆iy∪regular := by
    intro γ hγ
    rcases hc _ (hr γ hγ) with ho | hreg
    · exact zDk _ (Finset.mem_filter.mpr ⟨hγ,ho⟩)
    · exact zMj _ (Finset.mem_filter.mpr ⟨hγ,hreg⟩)
  have htotal:=(z1q Eh).trans (z2s _ _)
  have hH :1≤O1 v :=(by decide :1≤2).trans (cSk hv)
  have hsquare :O1 v*(O1 v - 1)+O1 v=O1 v^2 := by
    rw [pow_two,← Nat.mul_succ]
    change O1 v*(O1 v - 1+1)= _
    rw [Nat.sub_add_cancel hH]
  omega
private theorem ePy {w Γ s v} (C:a0Z v w Γ s) (h:Messages w Γ s) :
    46402*Γ.card≤46402*R4 v+(82317+2*46402)*acg v := by
  classical
  have hm:=bJG C.multiple h
  have hi:=bJG C.invariant h
  have hc:=(z1q C.cover).trans
    ((z2s _ _).trans
      (zlr (z2s _ _) _))
  have hmix :=C.kK
  have hf :=C.fresh
  have hn:=C.components
  omega
private theorem charge {l m d r b h:ℕ}
    (hl:46402*l≤46402*m+(82317+2*46402)*d+82317*r+46402*(b+h)) :
    l≤ m+ceilDiv ((82317+2*46402)*d+82317*r) 46402+b+h:= by
  unfold ceilDiv
  omega
theorem of_children (h1 :c1) (h2 :c2) :P6_6.c5:= by
  classical
  intro w Γ s h v hv g hg hr
  obtain ⟨n,f,q,hf,hq,hc⟩:=bFR v g hg
  let first:=Γ.filter fun γ=>cK q (extend (s γ))=0
  let proper :=Γ.filter fun γ => ∃ i,qg 2 (f i) (extend (s γ)) ∧ ¬ Fb (f i)
  let acA:=Γ.filter fun γ => ∃ i,qg 2 (f i) (extend (s γ))∧Fb (f i)
  have hfirst:=ebC (h.mono (Δ:=first) (zT0 _ _)) hv q hq
    (fun _ hγ=>(Finset.mem_filter.mp hγ).2)
  have hpmsg :=h.mono (Δ:=proper) (zT0 _ _)
  obtain ⟨P⟩:=h1 w proper s hpmsg v hv n f hf (fun _ hγ=>(Finset.mem_filter.mp hγ).2)
  have hproper :=ePy P hpmsg
  have hwmsg :=h.mono (Δ:=acA) (zT0 _ _)
  obtain ⟨W,hW,hn,hcap⟩:=h2 w acA s hwmsg v hv n f hf (fun _ hγ=>(Finset.mem_filter.mp hγ).2)
  have hwhole :46402*acA.card≤82317*W.BJ+46402*W.n :=
    (zBI _ (z1q hW)).trans (bJG W hwmsg)
  have Eh:Γ⊆first∪proper∪acA:= by
    intro γ hγ
    rcases hc _ (hr γ hγ) with hlow | ⟨i,hreg⟩
    · exact zDk _ (zDk _ (Finset.mem_filter.mpr ⟨hγ,hlow⟩))
    by_cases hw:Fb (f i)
    · exact zMj _ (Finset.mem_filter.mpr ⟨hγ,i,hreg,hw⟩)
    · exact zDk _ (zMj _
        (Finset.mem_filter.mpr ⟨hγ,i,hreg,hw⟩))
  have htotal:=(z1q Eh).trans
    ((z2s _ _).trans
      (zlr (z2s _ _) _))
  have hsum:46402*Γ.card≤46402*R4 v +
      (82317+2*46402)*acg v +
      82317*(133425*(mW v).b+bGL v) +
      46402*((mW v).b+O1 v^2) := by
    change W.BJ≤133425*(mW v).b at hcap
    omega
  have hfee :=charge hsum
  unfold acg at hfee
  rw [← Nat.mul_assoc] at hfee
  exact hfee
end
end P6_6_5
