import ProximityPrize.SubmissionLower.ZV7VOqb
set_option Elab.async false
namespace qL60i
open qEofLDb (Term Io apA)
open private negOne sumN coeffTop from ProximityPrize.SubmissionLower.ZV7VOqb
def negR (n:ℕ) :ℕ:=if n%2=0 then 1 else P1.p-1
def sumNR (g:ℕ→ℕ) :ℕ→ℕ
  | 0=>0
  | n+1=>(sumNR g n+g n)%P1.p
def coeffTopR (s u k:ℕ) :ℕ:=
  let j:=s+u-k
  negR u*sumNR (fun i=>s.fast_choose i%P1.p*negR (j-i)%P1.p*(u.fast_choose (j-i)%P1.p)%P1.p) (j+1)%P1.p
def lit1 (n:ℕ) (f:ℕ→ℕ) :ℕ:=Nat.casesOn (motive:=fun _=>ℕ) n (f 0) (fun m=>f (m+1))
def coeffTopRc (s u k:ℕ) :ℕ:=lit1 s fun s=>lit1 u fun u=>lit1 k fun k=>coeffTopR s u k
def apAR (t a f:ℕ) (b:Term) :ℕ:=
  if b.n≤t+a∧b.i≤t then
    let s:=b.c-(a+f)
    let u:=t+a-b.n
    if b.k≤s+u then
      (b.q%(P1.p:ℤ)).toNat*(t.fast_choose b.i%P1.p)%P1.p*((t+a-b.i).fast_choose (b.n-b.i)%P1.p)%P1.p*coeffTopRc s u b.k%P1.p
    else 0
  else 0
def IoR (t a f:ℕ) :List Term→ℕ
  | []=>0
  | b::bs=>(apAR t a f b+IoR t a f bs)%P1.p
private theorem hp :P1.p=2130706433:=rfl
private instance :NeZero P1.p:=⟨by rw [hp]; omega⟩
private theorem negR_cast (n:ℕ) :((negR n:ℕ):ZMod P1.p)=((negOne n:ℤ):ZMod P1.p) := by
  unfold negR negOne
  split_ifs
  · simp
  · rw [Nat.cast_sub (by rw [hp]; omega :1≤P1.p),ZMod.natCast_self]; simp
private theorem sumNR_cast (g:ℕ→ℕ) (G:ℕ→ℤ) (h:∀ i,((g i:ℕ):ZMod P1.p)=((G i:ℤ):ZMod P1.p)) :
    ∀ n,((sumNR g n:ℕ):ZMod P1.p)=((sumN G n:ℤ):ZMod P1.p)
  | 0=> by simp [sumNR,sumN]
  | n+1=> by
    have e1:sumNR g (n+1)=(sumNR g n+g n)%P1.p:=rfl
    have e2:sumN G (n+1)=sumN G n+G n:=rfl
    rw [e1,e2,ZMod.natCast_mod,Nat.cast_add,Int.cast_add,sumNR_cast g G h n,h]
private theorem coeffTop_cast (s u k:ℕ) :((coeffTopR s u k:ℕ):ZMod P1.p)=((coeffTop s u k:ℤ):ZMod P1.p) := by
  unfold coeffTopR coeffTop
  dsimp only
  rw [ZMod.natCast_mod,Nat.cast_mul,Int.cast_mul,negR_cast,sumNR_cast _
    (fun i=>(s.fast_choose i:ℤ)*negOne (s+u-k-i)*(u.fast_choose (s+u-k-i):ℤ)) (fun i=> by
      simp only [ZMod.natCast_mod,Nat.cast_mul,Int.cast_mul,Int.cast_natCast,negR_cast])]
private theorem lit1_eq (n:ℕ) (f:ℕ→ℕ) :lit1 n f=f n:= by cases n <;> rfl
private theorem coeffTopRc_eq (s u k:ℕ) :coeffTopRc s u k=coeffTopR s u k:= by simp only [coeffTopRc,lit1_eq]
private theorem apA_cast (t a f:ℕ) (b:Term) :((apAR t a f b:ℕ):ZMod P1.p)=((apA t a f b:ℤ):ZMod P1.p) := by
  unfold apAR apA
  dsimp only
  simp only [coeffTopRc_eq]
  split_ifs
  · have hq:(((b.q%(P1.p:ℤ)).toNat:ℕ):ℤ)=b.q%(P1.p:ℤ):=Int.toNat_of_nonneg (Int.emod_nonneg _ (by rw [hp]; omega))
    have hq':(((b.q%(P1.p:ℤ)).toNat:ℕ):ZMod P1.p)=((b.q:ℤ):ZMod P1.p) := by
      rw [← Int.cast_natCast,hq,ZMod.intCast_mod]
    simp only [ZMod.natCast_mod,Nat.cast_mul,Int.cast_mul,Int.cast_natCast,coeffTop_cast,hq']
  · simp
  · simp
private theorem Io_cast (t a f:ℕ) :∀ bs:List Term,((IoR t a f bs:ℕ):ZMod P1.p)=((Io t a f bs:ℤ):ZMod P1.p)
  | []=> by simp [IoR,Io]
  | b::bs=> by
    have e1:IoR t a f (b::bs)=(apAR t a f b+IoR t a f bs)%P1.p:=rfl
    have e2:Io t a f (b::bs)=apA t a f b+Io t a f bs:=rfl
    rw [e1,e2,ZMod.natCast_mod,Nat.cast_add,Int.cast_add,apA_cast,Io_cast t a f bs]
private theorem IoR_lt (t a f:ℕ) :∀ bs:List Term,IoR t a f bs<P1.p
  | []=>(by show 0<P1.p; rw [hp]; omega)
  | _::_=>Nat.mod_lt _ (by rw [hp]; omega)
theorem Io_emod (t a f:ℕ) (bs:List Term) :Io t a f bs%(P1.p:ℤ)=(IoR t a f bs:ℤ) := by
  have h:=(ZMod.intCast_eq_intCast_iff' (Io t a f bs) (IoR t a f bs:ℤ) P1.p).mp
    (by rw [Int.cast_natCast]; exact (Io_cast t a f bs).symm)
  rw [h]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast IoR_lt t a f bs)
end qL60i
