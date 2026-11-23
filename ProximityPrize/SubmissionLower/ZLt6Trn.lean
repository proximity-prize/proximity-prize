import ProximityPrize.SubmissionLower.ZYvV56c
set_option Elab.async false
namespace qL60b
open qDoysbd
open private prep value lineTest start extent EvalTerm EvalTerm.s EvalTerm.u EvalTerm.k EvalTerm.z from ProximityPrize.SubmissionLower.ZN1KL1c
open private aaJ bG5 fastFact from ProximityPrize.SubmissionLower.ZLkly3d
def dS (s u:ℕ) :ℕ:=(s+P1.p-u%P1.p)%P1.p
def aJR (s u n:ℕ) :ℕ×ℕ:=
  Nat.rec (motive:=fun _=>ℕ×ℕ) (1,dS s u) (fun n r=>(r.2,(dS s u*r.2+(n+P1.p-(s+u)%P1.p)*(n+1)%P1.p*r.1)%P1.p)) n
def bGR (s u k:ℕ) :ℕ:=
  if s+u-k≤k then (if u%2=0 then 1 else P1.p-1)*(fastFact k/fastFact (s+u-k)%P1.p)%P1.p*(aJR s u (s+u-k)).1%P1.p
  else (aJR s u k).1
def valueR (f:ℕ) (vs:List EvalTerm) :ℕ:=
  List.rec (motive:=fun _=>ℕ) 0 (fun v _ r=>if f+EvalTerm.k v≤EvalTerm.s v+EvalTerm.u v then (EvalTerm.z v%P1.p*bGR (EvalTerm.s v-f) (EvalTerm.u v) (EvalTerm.k v)+r)%P1.p else r) vs
def lineTestR (q a f t u:ℕ) (bs :List Block) :Bool :=
  let lo:=start q a f t u
  let vs:=prep t u bs
  (List.range (min ((56-t-3*u)/2+1) (extent vs)-lo)).all (fun j=>valueR (lo+j) vs == 0)
private theorem hp :P1.p=2130706433:=rfl
private theorem aaJ_succ (s u n:ℕ) :aaJ s u (n+1)=((aaJ s u n).2,((s :ℤ) - u)*(aaJ s u n).2+((n:ℤ)-(s+u:ℕ))*(n+1)*(aaJ s u n).1):=rfl
private theorem aJR_succ (s u n:ℕ) :aJR s u (n+1)=((aJR s u n).2,(dS s u*(aJR s u n).2+(n+P1.p-(s+u)%P1.p)*(n+1)%P1.p*(aJR s u n).1)%P1.p):=rfl
private theorem cS (s u:ℕ) :((dS s u:ℕ):ZMod P1.p)=((((s:ℤ)-u:ℤ)):ZMod P1.p) := by
  have h:u%P1.p≤s+P1.p:=(Nat.mod_lt _ (by rw [hp]; omega)).le.trans (Nat.le_add_left _ _)
  rw [dS,ZMod.natCast_mod,Nat.cast_sub h,Nat.cast_add,ZMod.natCast_self,ZMod.natCast_mod]
  push_cast; ring
private theorem cN (s u n:ℕ) :(((n+P1.p-(s+u)%P1.p:ℕ)):ZMod P1.p)=((((n:ℤ)-(s+u:ℕ):ℤ)):ZMod P1.p) := by
  have h:(s+u)%P1.p≤n+P1.p:=(Nat.mod_lt _ (by rw [hp]; omega)).le.trans (Nat.le_add_left _ _)
  rw [Nat.cast_sub h,Nat.cast_add,ZMod.natCast_self,ZMod.natCast_mod]
  push_cast; ring
private theorem aJ_mod (s u:ℕ) :∀ n,(((aaJ s u n).1:ℤ):ZMod P1.p)=((aJR s u n).1:ZMod P1.p) ∧
    (((aaJ s u n).2:ℤ):ZMod P1.p)=((aJR s u n).2:ZMod P1.p)
  | 0=>⟨by simp [aaJ,aJR],by rw [show aJR s u 0=(1,dS s u) from rfl,cS]; rfl⟩
  | n+1=> by
    obtain ⟨h1,h2⟩:=aJ_mod s u n
    rw [aaJ_succ,aJR_succ]
    refine ⟨h2,?_⟩
    simp only [ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul]
    rw [cS,cN,← h1,← h2]
    push_cast; ring
private theorem bG_mod (s u k:ℕ) :(((bG5 s u k):ℤ):ZMod P1.p)=((bGR s u k:ℕ):ZMod P1.p) := by
  unfold bG5 bGR
  dsimp only
  split_ifs with h hu
  · simp only [ZMod.natCast_mod,Nat.cast_mul,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast]
    rw [(aJ_mod s u _).1,(Nat.even_iff.mpr hu).neg_one_pow]; push_cast; ring
  · have ho:Odd u:=Nat.odd_iff.mpr (by omega)
    have h1:1≤P1.p:= by rw [hp]; omega
    simp only [ZMod.natCast_mod,Nat.cast_mul,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast,Nat.cast_sub h1,ZMod.natCast_self]
    rw [(aJ_mod s u _).1,ho.neg_one_pow]; push_cast; ring
  · exact (aJ_mod s u k).1
private theorem valueR_cons (f:ℕ) (v:EvalTerm) (vs:List EvalTerm) :valueR f (v::vs)=
    if f+EvalTerm.k v≤EvalTerm.s v+EvalTerm.u v then (EvalTerm.z v%P1.p*bGR (EvalTerm.s v-f) (EvalTerm.u v) (EvalTerm.k v)+valueR f vs)%P1.p else valueR f vs:=rfl
private theorem value_mod (f:ℕ) :∀ vs:List EvalTerm,((value f vs:ℤ):ZMod P1.p)=((valueR f vs:ℕ):ZMod P1.p)
  | []=> by simp [value,valueR]
  | v::vs=> by
    have ih:=value_mod f vs
    rw [valueR_cons]
    unfold value
    dsimp only
    split_ifs
    · simp only [ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,Int.cast_add,Int.cast_mul,Int.cast_natCast]
      rw [bG_mod,ih]
    · exact ih
private theorem valueR_lt (f:ℕ) :∀ vs:List EvalTerm,valueR f vs<P1.p
  | []=>(by rw [hp]; decide :0<P1.p)
  | v::vs=> by
    rw [valueR_cons]
    split_ifs
    · exact Nat.mod_lt _ (by rw [hp]; omega)
    · exact valueR_lt f vs
private theorem value_emod (f:ℕ) (vs:List EvalTerm) :value f vs % (P1.p:ℤ)=(valueR f vs:ℤ) := by
  have h:=(ZMod.intCast_eq_intCast_iff' (value f vs) (valueR f vs:ℤ) P1.p).mp (by rw [Int.cast_natCast]; exact value_mod f vs)
  rw [h]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast valueR_lt f vs)
private theorem lineTest_eq (q a f t u:ℕ) (bs:List Block) :lineTest q a f t u bs=lineTestR q a f t u bs := by
  unfold lineTest lineTestR
  dsimp only
  congr 1
  funext j
  rw [value_emod]
  cases valueR (start q a f t u+j) (prep t u bs) <;> rfl
theorem aT_of {q a f n code t u:ℕ} (h:lineTestR q a f t u (unpack q n code)=true) :aT q a f n code t u := by
  unfold aT; rw [lineTest_eq]; exact h
theorem lK_of {q a f n code t:ℕ}
    (h:(List.range (min 16 ((56-t)/3)+1)).all (lineTestR q a f t · (unpack q n code))=true) :lK q a f n code t := by
  unfold lK
  have e:(lineTest q a f t · (unpack q n code))=(lineTestR q a f t · (unpack q n code)):=funext fun u=>lineTest_eq q a f t u _
  rw [e]; exact h
theorem Head_of {q a f n code:ℕ} (h:valueR f (prep q a (unpack q n code))=1) :Head q a f n code := by
  unfold Head; rw [value_emod,h]; rfl
def segR (q a f n code t lo len:ℕ) :Bool:=
  (List.range' lo len).all (fun u=>!decide (u≤min 16 ((56-t)/3)) || lineTestR q a f t u (unpack q n code))
private theorem segR_mem {q a f n code t lo len u:ℕ} (h:segR q a f n code t lo len=true) (h1:lo≤u) (h2:u<lo+len)
    (hu:u≤min 16 ((56-t)/3)) :lineTestR q a f t u (unpack q n code)=true := by
  have:=List.all_eq_true.mp h u (List.mem_range'_1.mpr ⟨h1,h2⟩)
  simpa [hu] using this
theorem lK_of4 {q a f n code t:ℕ} (h0:segR q a f n code t 0 4=true) (h1:segR q a f n code t 4 4=true)
    (h2:segR q a f n code t 8 4=true) (h3:segR q a f n code t 12 5=true) :lK q a f n code t := by
  apply lK_of
  refine List.all_eq_true.mpr fun u hu=>?_
  have hu':u≤min 16 ((56-t)/3):=Nat.le_of_lt_succ (List.mem_range.mp hu)
  have h16:u<17:= by omega
  by_cases ha:u<4
  · exact segR_mem h0 (Nat.zero_le _) (by omega) hu'
  by_cases hb:u<8
  · exact segR_mem h1 (by omega) (by omega) hu'
  by_cases hc:u<12
  · exact segR_mem h2 (by omega) (by omega) hu'
  · exact segR_mem h3 (by omega) (by omega) hu'
end qL60b
