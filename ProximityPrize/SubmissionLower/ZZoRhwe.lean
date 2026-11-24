import ProximityPrize.SubmissionLower.ZrstUma
set_option Elab.async false
set_option autoImplicit true
namespace qJofIZa
open qHde8fc qKVdmob
open fP (cF)
open private adz from ProximityPrize.SubmissionLower.ZrstUma
set_option Elab.async false
private abbrev Term:=ℕ×Triple
def unpack :ℕ→ℕ→List Term
  | 0,_=>[]
  | n+1,z =>
    (z % 0x80000000,(z >>> 31) % 64,(z >>> 37) % 64,(z >>> 43) % 32) ::
      unpack n (z >>> 48)
private instance (r c f u j k :ℕ) :Decidable (iG r c f u j k) := by
  unfold iG
  infer_instance
private def choose (n k :ℕ) :ℕ :=
  if k≤n then n.descFactorial (min k (n - k))/(min k (n - k)).factorial else 0
private theorem choose_eq (n k :ℕ) :choose n k=n.choose k := by
  by_cases hk :k≤n
  · rw [choose,ite_eq_left hk,← Nat.choose_eq_descFactorial_div_factorial]
    by_cases h:k≤n - k
    · rw [min_eq_left h]
    · rw [min_eq_right (by omega :n - k≤k),Nat.choose_symm hk]
  · rw [choose,ite_eq_right hk,Nat.choose_eq_zero_of_lt (by omega)]
private def entry (v :Triple) (i j k :ℕ) :ℕ :=
  choose v.1 i*choose v.2.1 j*choose v.2.2 k
private def dot (i j k :ℕ) :List Term→ℕ
  | []=>0
  | (z,v) :: ts=>z*entry v i j k+dot i j k ts
private noncomputable def synth (e :aY) (cut:ℕ) :List Term→ gP e cut→Ground
  | []=>0
  | (z,v) :: ts=>(z :Ground)•cZ e cut v+synth e cut ts
private theorem jP (e :aY) (cut:ℕ) (v :Triple) (m:gP e cut) :
    (entry v (m.val.val 1) (m.val.val 2) (m.val.val 3) :Ground)=cZ e cut v m:= by
  simp only [entry,choose_eq,Nat.cast_mul,cZ,cE,yv]
private theorem kG (e :aY) (cut:ℕ) (ts :List Term) (m:gP e cut) :
    (dot (m.val.val 1) (m.val.val 2) (m.val.val 3) ts :Ground)=synth e cut ts m:= by
  induction ts with
  | nil=>simp [dot,synth]
  | cons t ts ih =>
    obtain ⟨z,v⟩:=t
    rw [dot,Nat.cast_add,Nat.cast_mul,jP,ih]
    rfl
private theorem m4 (e :aY) (cut:ℕ) (ts :List Term)
    (h : ∀ t∈ts,t.2.1+t.2.2.1+t.2.2.2≤56 ∧
      iG (cP (aD e.val)) (e.val 2) (e.val 3) (cP t.2) t.2.2.1 t.2.2.2) :
    synth e cut ts∈Submodule.span Ground (Set.range fun v :iw e =>
      cZ e cut (aD v.val.val)) := by
  induction ts with
  | nil=>exact Submodule.zero_mem _
  | cons t ts ih =>
    obtain ⟨z,b,c,f⟩:=t
    obtain ⟨hd,hb⟩:=h _ List.mem_cons_self
    change b+c+f≤56 at hd
    let v :aY:=⟨Finsupp.equivFunOnFinite.symm ![56-(b+c+f),b,c,f],by
      rw [cF]
      change 56-(b+c+f)+b+c+f=56
      omega⟩
    have hv :aD v.val=(b,c,f) :=rfl
    have he :dZ v<dZ e := by
      apply adz
      rw [hv]
      exact hb
    have hm:cZ e cut (b,c,f) ∈
        Submodule.span Ground (Set.range fun v :iw e =>
          cZ e cut (aD v.val.val)) :=
      Submodule.subset_span ⟨⟨v,he⟩,congrArg (cZ e cut) hv⟩
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hm)
      (ih fun u hu=>h u (List.mem_cons_of_mem _ hu))
private abbrev low (r cut k :ℕ) :ℕ:=r-(56+3*(56 - cut)+2*k)
def slice (r cut k :ℕ) (v :Triple) (ts :List Term) :Bool :=
  (List.range ((56-3*k)/2+1-low r cut k)).all fun d =>
    let j:=low r cut k+d
    let b:=2*j+3*k
    decide (Lr r cut v.2.1 v.2.2 j k) ||
      (List.range (57 - max cut b)).all fun l =>
        let i:=cut - b+l
        dot i j k ts % P1.p == entry v i j k % P1.p
private theorem slice_sound {r cut i j k :ℕ} {v :Triple} {ts :List Term}
    (hlo:cut≤ i+2*j+3*k) (hhi:i+2*j+3*k≤56)
    (hs : ¬ Lr r cut v.2.1 v.2.2 j k) (h:slice r cut k v ts=true) :
    dot i j k ts % P1.p=entry v i j k % P1.p:= by
  have hj:low r cut k≤j:= by
    unfold low
    unfold Lr iG at hs
    omega
  have hjd:j-low r cut k<(56-3*k)/2+1-low r cut k := by omega
  dsimp only [slice] at h
  have hjc:=List.all_eq_true.mp h _ (List.mem_range.mpr hjd)
  rw [Nat.add_sub_of_le hj] at hjc
  rw [decide_eq_false hs,Bool.false_or] at hjc
  have hid :i-(cut - (2*j+3*k))<57 - max cut (2*j+3*k) := by omega
  have hc:=List.all_eq_true.mp hjc _ (List.mem_range.mpr hid)
  rw [Nat.add_sub_of_le (by omega :cut - (2*j+3*k)≤ i)] at hc
  exact beq_iff_eq.mp hc
end qJofIZa
