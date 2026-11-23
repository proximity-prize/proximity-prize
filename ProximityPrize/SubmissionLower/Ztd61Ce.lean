import ProximityPrize.SubmissionLower.ZYvV56c
import ProximityPrize.SubmissionLower.ZZoRhwe
import ProximityPrize.SubmissionLower.Z9vlvqb
import ProximityPrize.SubmissionLower.Zbi9s5b
import ProximityPrize.SubmissionLower.ZyTlNte
import ProximityPrize.SubmissionLower.ZCIcQjc
import ProximityPrize.SubmissionLower.ZbvbtFa
import ProximityPrize.SubmissionLower.ZJObpKc
import ProximityPrize.SubmissionLower.Zqmzf9b
set_option Elab.async false
open _root_ renaming Finset.filter_subset → zT0, Finset.single_le_sum → zfK, Finset.sum_add_distrib → zfW, Finset.sum_le_sum → zQk, Finset.sum_le_sum_of_subset → zZL, MvPolynomial.eval → zY9, Nat.add_le_add_left → z3b, Nat.add_sub_of_le → zp3, Nat.le_add_right → z8K, Nat.mul_comm → z5A, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.sub_le → z7J, Nat.zero_le → zD0, Polynomial.C → z1z, Polynomial.leadingCoeff → z4w
set_option maxHeartbeats 2000000
section
set_option autoImplicit true
set_option Elab.async false
namespace qYiv0Ea
open qHde8fc
open fP (cF)
noncomputable section
private def ic (b c f k :ℕ) (m:gU 0) :Ground :=
  (b.choose (m.val 1) :Ground)*(c.choose (m.val 2) :Ground) *
    (if k≤ m.val 3 then (f.choose (m.val 3 - k) :Ground) else 0)
private theorem dd4 (b c f :ℕ) :
    ic b c f 0=cE 0 (b,c,f) := by
  funext m
  simp [ic,cE,yv]
private theorem dd2 (b c f k :ℕ) :
    ic b c f (k+1)=ic b c (f+1) k - ic b c f k := by
  funext m
  change _=ic b c (f+1) k m - ic b c f k m
  unfold ic
  rw [← mul_sub]
  congr 1
  by_cases h:k< m.val 3
  · have h₁:k+1≤ m.val 3:= by omega
    have h₂:k≤ m.val 3:= by omega
    have h₃:m.val 3 - k=(m.val 3-(k+1))+1 := by omega
    rw [ite_eq_left h₁,ite_eq_left h₂,ite_eq_left h₂,h₃,Nat.choose_succ_succ',Nat.cast_add,
      add_sub_cancel_right]
  · by_cases he :k=m.val 3
    · simp [he]
    · have h₁ : ¬ k+1≤ m.val 3:= by omega
      have h₂ : ¬ k≤ m.val 3:= by omega
      rw [ite_eq_right h₁,ite_eq_right h₂,ite_eq_right h₂,sub_zero]
private theorem gqA (S:Submodule Ground (gU 0→Ground))
    (b c:ℕ) : ∀ (k f :ℕ),
    (∀ i:ℕ,i≤k→ic b c (f+i) 0∈S) →
    ic b c f k∈S:= by
  intro k
  induction k with
  | zero =>
    intro f h
    simpa only [Nat.add_zero] using h 0 le_rfl
  | succ k ih =>
    intro f h
    rw [dd2]
    apply S.sub_mem
    · apply ih
      intro i hi
      rw [show f+1+i=f+(i+1) by omega]
      exact h (i+1) (by omega)
    · exact ih f (fun i hi=>h i (by omega))
private theorem fZr (S:Submodule Ground (gU 0→Ground))
    (b c:ℕ) : ∀ (k f :ℕ),ic b c f k∈S →
    (∀ i:ℕ,0< i→i≤k→ic b c (f+i) 0∈S) →
    ic b c f 0∈S:= by
  intro k
  induction k with
  | zero=>exact fun _ h _=>h
  | succ k ih =>
    intro f h ht
    rw [dd2] at h
    have hnext:ic b c (f+1) k∈S:= by
      apply gqA
      intro i hi
      rw [show f+1+i=f+(i+1) by omega]
      exact ht (i+1) (by omega) (by omega)
    apply ih f
    · simpa only [sub_sub_cancel] using S.sub_mem hnext h
    · exact fun i hp hi=>ht i hp (by omega)
private def b7f (e :aY) (i:ℕ) (hi:i≤e.val 0) :aY :=
  ⟨Finsupp.equivFunOnFinite.symm ![e.val 0 - i,e.val 1,e.val 2,e.val 3+i],by
    have hd:=e.property
    rw [cF] at hd ⊢
    simp
    omega⟩
private theorem b7g (e :aY) (i:ℕ) (hi:i≤e.val 0) (j:Fin 4) :
    (b7f e i hi).val j = ![e.val 0 - i,e.val 1,e.val 2,e.val 3+i] j:= by
  simp [b7f]
private theorem gM0 (e :aY) (ha :17≤e.val 0) :bk1 e := by
  refine ⟨0,Or.inl (zD0 _),?_⟩
  let S:=Submodule.span Ground
    (Set.range fun v :iw e=>cE 0 (aD v.val.val))
  change cE 0 (e.val 1,e.val 2,e.val 3)∈S
  rw [← dd4]
  apply fZr S _ _ 17
  · have hz :ic (e.val 1) (e.val 2) (e.val 3) 17=0:= by
      funext m
      have hm:=m.property.2.2.2
      simp [ic,show ¬ 17≤ m.val 3 by omega]
    rw [hz]
    exact S.zero_mem
  · intro i hp hi
    let v :=b7f e i (hi.trans ha)
    have hv1 :v.val 1=e.val 1 := by simp [v,b7g]
    have hv2 :v.val 2=e.val 2 := by simp [v,b7g]
    have hv3:v.val 3=e.val 3+i:= by simp [v,b7g]
    have hd:=e.property
    rw [cF] at hd
    have hv :dZ v<dZ e := by
      simp only [dZ,aD,cP,hv1,hv2,hv3]
      omega
    rw [dd4]
    exact Submodule.subset_span ⟨⟨v,hv⟩,by simp [aD,hv1,hv2,hv3]⟩
theorem okL {w f a :ℕ} (h:17≤a) :Ok w f a := fun e _ _ ha=>gM0 e (by omega)
end
end qYiv0Ea
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qYiv0Ea
open qHde8fc qDoysbd
open qhonTAe (Ae abJ)
open GN (ord)
open fP (cF)
open private aV aaH W6 start value prep lineTest extent gK3 from ProximityPrize.SubmissionLower.ZN1KL1c
def unpack5 (q:ℕ) :ℕ→ℕ→List Block
  | 0,_=>[]
  | groups+1,code =>
    let n:=code % 32
    let len:=(code >>> 15) % 16+1
    let zs :=code >>> 19
    ⟨n,(56 - n)/2+q-(n+(code >>> 5) % 32),(code >>> 10) % 32,len,zs % 2^(31*len)⟩ ::
      unpack5 q groups (zs >>> (31*len))
def FitsB (cut:ℕ) (bs :List Block) :Prop :=
  bs.all (fun b=>decide (b.i+b.len≤b.n+1∧2*b.n+(b.i+b.len-1)+b.k<cut))=true
def HeadB (q a f :ℕ) (bs :List Block) :Prop :=value f (prep q a bs) % (P1.p:ℤ)=1
def PlaneB (q a f t:ℕ) (bs :List Block) :Prop :=
  (List.range (min 16 ((56-t)/3)+1)).all (lineTest q a f t · bs)=true
private theorem line_soundB {q a f t u k :ℕ} {bs :List Block}
    (h:lineTest q a f t u bs=true) (hk :start q a f t u≤k)
    (hdom:3*u+2*k+t≤56) :value k (prep t u bs) % (P1.p:ℤ)=0:= by
  by_cases he :extent (prep t u bs)≤k
  · rw [gK3 he,Int.zero_emod]
  · unfold lineTest at h
    have hi:k-start q a f t u <
        min ((56-t-3*u)/2+1) (extent (prep t u bs))-start q a f t u:= by omega
    have hm:=beq_iff_eq.mp (List.all_eq_true.mp h _ (List.mem_range.mpr hi))
    rwa [zp3 hk] at hm
theorem coreB {w f a cut:ℕ} (bs :List Block) (hpos :0<cut) (hw:w≤112)
    (hf :FitsB cut bs) (hh:HeadB (112-w) a f bs) (hl : ∀ t≤112-w,PlaneB (112-w) a f t bs)
    (e :aY) (he :cP (aD e.val)=w) (hef :e.val 3=f) (hea :e.val 0=a) :
    cE cut (aD e.val)∈qokB5pc.jZ e cut:= by
  let q:=112-w
  have hwt:w=56+ord e.val :=he.symm.trans (qhonTAe.nG e)
  have hq:56-ord e.val=q:= by dsimp only [q]; omega
  refine Ae e cut hpos (aV bs) (aaH bs ?_) ⟨?_,?_⟩
  · exact fun v hv=>of_decide_eq_true (List.all_eq_true.mp hf v hv)
  · rw [W6 e (by omega),hq,hea,hef]
    intro hz
    have hm:=Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
    change value f (prep q a bs) % (P1.p:ℤ)=1 at hh
    omega
  · intro v hLive hkey
    obtain ⟨hv,hva⟩:=(abJ _).mp hLive
    let t:=56-ord v.val
    let u:=v.val 0
    let k :=v.val 3
    have hc:=qhonTAe.nG v
    change cP (aD v.val)=56+ord v.val at hc
    unfold dZ at hkey
    rw [he,hc,hef] at hkey
    have hd:=v.property
    have hd' := e.property
    rw [cF] at hd hd'
    have ho' : w-56≤ord v.val := by omega
    have ht:t≤q:= by dsimp only [t,q]; omega
    have hnum :3*u+2*k≤56-t:= by
      have h0:ord v.val=3*u+v.val 2+2*k :=rfl
      dsimp only [t]
      omega
    have hk :start q a f t u≤k := by
      unfold start
      split
      · exact zD0 _
      · rename_i h
        have hsame :ord v.val=ord e.val := by dsimp only [t,q] at h; omega
        have h0:ord v.val=3*u+v.val 2+2*k :=rfl
        have h1 :ord e.val=3*a+e.val 2+2*f := by rw [← hea,← hef]; rfl
        dsimp only [u,k] at *
        split <;> omega
    have hu:u∈List.range (min 16 ((56-t)/3)+1) :=List.mem_range.mpr (by
      change u≤16 at hva
      omega)
    have hline :lineTest q a f t u bs=true :=List.all_eq_true.mp (hl t ht:PlaneB _ _ _ _ _) u hu
    have hm:=line_soundB hline hk (by omega)
    rw [W6 v hv]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.dvd_of_emod_eq_zero hm)
theorem okW {w f a n code :ℕ} (hA:AddrOK w f a=true)
    (hf :FitsB (cutOf w f a) (unpack5 (112-w) n code)) (hh:HeadB (112-w) a f (unpack5 (112-w) n code))
    (hl : ∀ t≤112-w,PlaneB (112-w) a f t (unpack5 (112-w) n code)) :Ok w f a :=
  ok_of_span hA fun e he hef hea=>coreB _ (addr_pos hA).1 (addr_pos hA).2 hf hh hl e he hef hea
end qYiv0Ea
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qYiv0Ea
open qHde8fc qKVdmob
open qJofIZa (unpack slice)

open private dot entry synth m4 kG jP slice_sound from ProximityPrize.SubmissionLower.ZZoRhwe
open private i7 from ProximityPrize.SubmissionLower.ZrstUma
private instance (r c f u j k :ℕ) :Decidable (iG r c f u j k) := by
  unfold iG
  infer_instance
def validP (r c f :ℕ) (t:ℕ×Triple) :Bool :=
  decide (t.2.1+t.2.2.1+t.2.2.2≤56∧iG r c f (cP t.2) t.2.2.1 t.2.2.2)
theorem coreP {r a f cut n z :ℕ}
    (hl: (unpack n z).all (validP r (ee r a f).2.1 f)=true)
    (hfit : ∀ k≤16,slice r cut k (ee r a f) (unpack n z)=true)
    (e :aY) (hr :cP (aD e.val)=r) (ha :e.val 0=a) (hf :e.val 3=f) :
    fG e cut:= by
  have hv :=bnW e
  rw [hr,ha,hf] at hv
  have hj:e.val 2=(ee r a f).2.1 :=(congrArg (fun v :Triple=>v.2.1) hv).symm
  let ts :=unpack n z
  have hok (t:ℕ×Triple) (ht:t∈ts) :
      t.2.1+t.2.2.1+t.2.2.2≤56∧iG r (ee r a f).2.1 f (cP t.2) t.2.2.1 t.2.2.2 :=
    of_decide_eq_true (List.all_eq_true.mp hl t ht)
  have heq :synth e cut ts=cZ e cut (aD e.val) := by
    funext m
    obtain ⟨hlo,hhi⟩:=i7 m.val
    have hk :m.val.val 3≤16:=m.val.property.2.2.2
    let i:=m.val.val 1
    let j:=m.val.val 2
    let k :=m.val.val 3
    have hres : ¬ Lr r cut (ee r a f).2.1 f j k := by
      simpa only [b8,hr,hj,hf] using m.property
    have hm:dot i j k ts % P1.p=entry (ee r a f) i j k % P1.p :=
      slice_sound hlo hhi hres (hfit k hk)
    have hm' := congrArg (fun u:ℕ=>(u:Ground)) hm
    simpa only [ZMod.natCast_mod,i,j,k,kG,jP,hv] using hm'
  unfold fG
  rw [← heq]
  exact m4 e cut ts fun t ht=>⟨(hok t ht).1,by
    simpa only [hr,hj,hf] using (hok t ht).2⟩
theorem okP {w f a n z :ℕ} (hA:AddrOK w f a=true)
    (hl: (unpack n z).all (validP w (ee w a f).2.1 f)=true)
    (hfit : ∀ k≤16,slice w (cutOf w f a) k (ee w a f) (unpack n z)=true) :Ok w f a :=
  ok_of_span hA fun e he hef hea =>
    qKVdmob.amN e (by have :=(addr_pos hA).2; omega) _ (coreP hl hfit e he hea hef)
end qYiv0Ea
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qcZ3orc
open P6_6 P6_6_8 q2w4Sxc
local notation "a!" l "," u "," f =>
  C8 (lo:=l) (hi:=u) (k :=1) (bw:=f) (Or.inr rfl) (by decide) (by decide) (by decide) rfl (by decide)
local notation "r!" l "," u "," kv "," f "," w "," h =>
  C8 (lo:=l) (hi:=u) (k :=kv) (bw:=f)
    (Or.inl (order (r :=l) (k :=kv) (ws :=w) h rfl (by decide)))
    (by decide) (by decide) (by decide) rfl (by decide)
private theorem r1 :C ⟨1,3,1⟩ ⟨45,5,1⟩ :=
  a! ⟨1,3,1⟩,⟨45,5,1⟩,0x2005650aa1b93a
private theorem r2 :C ⟨3,6,1⟩ ⟨23,9,1⟩ :=
  a! ⟨3,6,1⟩,⟨23,9,1⟩,0x479758e462cff7
private theorem r3:C ⟨2,6,2⟩ ⟨9,9,3⟩ :=
  a! ⟨2,6,2⟩,⟨9,9,3⟩,0x6deb1f15107826
private theorem r4 :C ⟨10,6,2⟩ ⟨23,7,2⟩ :=
  a! ⟨10,6,2⟩,⟨23,7,2⟩,0x8bb507e7b43573
private theorem r5:C ⟨10,8,2⟩ ⟨13,8,2⟩ :=
  a! ⟨10,8,2⟩,⟨13,8,2⟩,0x72044c522cd362
private theorem r6:C ⟨14,8,2⟩ ⟨23,8,2⟩ :=
  a! ⟨14,8,2⟩,⟨23,8,2⟩,0xc79eb7a584c1b0
private theorem r7:C ⟨10,9,2⟩ ⟨23,9,3⟩ :=
  r! ⟨10,9,2⟩,⟨23,9,3⟩,2,0x8808b6708c72d9,[([11,12],0x88378ceb6bf),([13,14],0x658c17db9d6),([16,19],0x45341d540c3),([23,30],0x22a6b6b4f99),([53],0x575bdf76d2)],⟨rfl,rfl,rfl,rfl,rfl,trivial⟩
private theorem r8:C ⟨24,6,1⟩ ⟨45,9,1⟩ :=
  a! ⟨24,6,1⟩,⟨45,9,1⟩,0x8d6f039b03e003
private theorem r9:C ⟨24,6,2⟩ ⟨45,9,3⟩ :=
  r! ⟨24,6,2⟩,⟨45,9,3⟩,3,0xafd73233183f2b,[([11,10],0x7eaf1041865),([11,12],0x5ec59037ef3),([13,15],0x460b463d607),([17,20],0x2bdf8772bae),([24,36],0x1017a9fe8e8)],⟨rfl,rfl,rfl,rfl,rfl,trivial⟩
private theorem dz :C ⟨5,10,1⟩ ⟨45,11,1⟩ :=
  r! ⟨5,10,1⟩,⟨45,11,1⟩,2,0x6f85129d0885e0,[([14,15],0xa767bc4b96b),([17,20],0x733216bf730),([23,31],0x395f84eb373),([52],0x915ba6283c)],⟨rfl,rfl,rfl,rfl,trivial⟩
private theorem dD:C ⟨4,10,2⟩ ⟨45,11,3⟩ :=
  r! ⟨4,10,2⟩,⟨45,11,3⟩,5,0xace4c18a2af50a,[([13,10],0x8ba11ba8a53),([11,12],0x5d9da4f1ff4),([13,14],0x40b99d835b9),([16,19],0x25d33e61b85),([25,42],0xdbbb68433e)],⟨rfl,rfl,rfl,rfl,rfl,trivial⟩
private theorem dK:C ⟨6,12,1⟩ ⟨45,16,1⟩ :=
  r! ⟨6,12,1⟩,⟨45,16,1⟩,2,0xf542a9f8759a27,[([22,27],0xfab4b99cb60),([35,59],0x5bb31c19616)],⟨rfl,rfl,trivial⟩
private theorem e8:C ⟨4,12,2⟩ ⟨45,16,5⟩ :=
  r! ⟨4,12,2⟩,⟨45,16,5⟩,9,0xe82b1b55c8e7fd,[([21,16],0xd69a7a06959),([18,21],0x64a4aed0d61),([27,47],0x24bdc055a5b)],⟨rfl,rfl,rfl,trivial⟩
private theorem gD:C ⟨46,3,1⟩ ⟨133,16,1⟩ :=
  r! ⟨46,3,1⟩,⟨133,16,1⟩,7,0xda0634009fb132,[([30,29],0x13035510a67a),([34],0x2a0a504ff1a)],⟨rfl,rfl,trivial⟩
private theorem gx :C ⟨46,6,2⟩ ⟨133,16,5⟩ :=
  r! ⟨46,6,2⟩,⟨133,16,5⟩,22,0x1137a680cae6b4b,[([27,7],0xd6ae3bacbf7),([8,8],0x41a44f7e088),([9,10],0x2d9060cd2ed),([10,12],0x154942f8990),([17],0x2e87ec5f42)],⟨rfl,rfl,rfl,rfl,rfl,trivial⟩
theorem A:C ⟨1,3,1⟩ ⟨133,16,12⟩ :=
  Certificate.trim (.splitB 45
    (.rK 11
      (Certificate.trim (.rK 5
        (Certificate.trim (r1))
        (Certificate.trim (.rK 9
          (.splitB 23
            (.splitT 1
              (Certificate.trim (r2))
              (.splitB 9
                (r3)
                (.rK 8
                  (Certificate.trim (.rK 7
                    (r4)
                    (.splitB 13
                      (r5)
                      (r6))))
                  (r7))))
            (.splitT 1
              (r8)
              (r9)))
          (Certificate.trim (.splitT 1
            (Certificate.trim (dz))
            (dD)))))))
      (Certificate.trim (.splitT 1
        (Certificate.trim (dK))
        (e8))))
    (.splitT 1
      (gD)
      (Certificate.trim (gx))))
end qcZ3orc
end
section
set_option autoImplicit true
namespace qcZ3orc
open q2w4Sxc
theorem proof :q2w4Sxc.c1 :=
  root (.rK 38 (Certificate.trim (Certificate.rK 16 A B)) D)
end qcZ3orc
end
section
set_option autoImplicit true
namespace qJrCx9a
open aR (Shape)
open P6_6 P6_6_8
theorem proof :q2w4Sxc.c6:= by
  rintro ⟨b,j,t⟩ hv hj
  change j=7 at hj
  subst j
  rcases hv with hz | ⟨hv,hb⟩
  · have h:=congrArg Shape.j hz
    change 7=0 at h
    omega
  obtain ⟨h1,h3,h7⟩:=hv
  change 1≤t at h1
  change 3*t≤7 at h3
  change 7≤3*b at h7
  change b≤10 at hb
  have h₂:t≤2 := by omega
  have h₃:3≤b:= by omega
  interval_cases b <;> interval_cases t
  · exact s31
  · exact s32
  · exact s41
  · exact s42
  · exact s51
  · exact s52
  · exact s61
  · exact s62
  · exact s71
  · exact s72
  · exact s81
  · exact s82
  · exact s91
  · exact s92
  · exact s101
  · exact s102
end qJrCx9a
end
section
set_option autoImplicit true
set_option maxRecDepth 12000
namespace q4DKPnb
noncomputable section
open P6_6 P6_6_7 q6t08kb
open aR (af shape cK jet extend qE)
open Ex (X7 YN aQU C6 bUq)
open oR (qg)
open aeA (view biB elimination d0Z d02
  cLz cLA)
open ana (bZ3 aVQ)
open aF0 (BJ YM)
open MvPolynomial UniqueFactorizationMonoid
open scoped BigOperators Polynomial
open private b7n from ProximityPrize.SubmissionLower.B7
open private beA from ProximityPrize.SubmissionLower.A3
open private QI from ProximityPrize.SubmissionLower.AH
open private bpk from ProximityPrize.SubmissionLower.CD
open private fX6 from ProximityPrize.SubmissionLower.ZCIcQjc
open private orderAt_ord from ProximityPrize.SubmissionLower.ZfVU1Oc
private theorem lower_irreducible {R:af 4} (h:Irreducible R) (ht: (shape R).t=0) :
    Irreducible (X7 R) := by
  have he :YN R=z1z (X7 R) := by
    have hd:=(aQU R).trans ht
    simpa only [ X7,z4w,hd] using
      Polynomial.eq_C_of_natDegree_eq_zero hd
  have hi:Irreducible (z1z (X7 R)) :=he ▸ h.map YN
  refine ⟨fun hu=>hi.not_isUnit (Polynomial.isUnit_C.mpr hu),?_⟩
  intro a b hab
  exact (hi.isUnit_or_isUnit
    (show z1z (X7 R)=z1z a*z1z b by
      rw [← map_mul,← hab])).imp Polynomial.isUnit_C.mp Polynomial.isUnit_C.mp
private theorem elimination_cap (g:af 3) (w:Fin 3→ℕ) {B T:ℕ}
    (hb:g.weightedTotalDegree w≤B) (ht: (view g).natDegree≤T)
    (hw:w 2*T≤B) :
    (elimination g).weightedTotalDegree (fun i=>w i.castSucc) ≤
      max B ((2*T - 1)*B - w 2*T^2) := by
  let c:=(view g).natDegree
  by_cases hc:c=0
  · exact (cLA w g hc).trans (hb.trans (le_max_left _ _))
  have hpos :=Nat.pos_of_ne_zero hc
  have hh:=(cLz w g hpos).trans (zBI (2*c - 1) hb)
  have hrate :w 2*(T+c)≤2*B:= calc
    _≤w 2*(T+T) :=zBI _ (z3b ht _)
    _=2*(w 2*T) := by ring
    _≤_:=zBI 2 hw
  have hid :w 2*c^2+w 2*((T - c)*(T+c))=w 2*T^2 := calc
    _=w 2*(c+(T - c))^2 := by
      conv_lhs=>rw [show T+c=(c+(T - c))+c by rw [zp3 ht]]
      ring
    _ = _:= by rw [zp3 ht]
  exact (Nat.le_sub_of_add_le (by
    simpa only [Nat.add_assoc,hid] using beA hpos ht hrate hh)).trans (le_max_right _ _)
private theorem project {C:Context} {R:af 4} {l ell:ℕ} (h:HigherIndex C R l ell) :
    let a :=lowerBody (shape R)
    ∃ q:af 2,q≠0∧q.totalDegree≤projectionTotal a ∧
      qE q≤projectionIndex a ∧
      ∀ γ∈singular C R,cK q (extend (C.s γ))=0:= by
  classical
  dsimp only
  let a :=lowerBody (shape R)
  let g:=X7 R
  have hb:g.totalDegree≤a.b:= by
    have hh:=b7n R (1 :Fin 4→ℕ)
    change g.weightedTotalDegree 1+1*(shape R).t≤R.weightedTotalDegree 1 at hh
    rw [weightedTotalDegree_one,weightedTotalDegree_one,one_mul] at hh
    exact ((z8K _ _).trans hh).trans (le_max_left _ _)
  have hj:qE g≤a.j:= by
    have hh:=b7n R (fun i=>i.val)
    change g.weightedTotalDegree (fun i=>i.val)+3*(shape R).t≤_ at hh
    rw [← C6,← C6] at hh
    exact (z8K _ _).trans hh
  have ht: (view g).natDegree≤a.t:= by
    have hh:=biB (fun i=>i.val) g (view g).natDegree le_rfl
    rw [← C6] at hh
    change _+2*(view g).natDegree≤qE g at hh
    change qE g≤(shape R).j at hj
    change (view g).natDegree≤(shape R).j/2
    omega
  have hJ: (shape R).j≤1710 :=h.2.1.2.2.1.2.1.trans (z7J _ _)
  have hchar : (view g).natDegree<K1.p:= by
    change (view g).natDegree≤(shape R).j/2 at ht
    change (view g).natDegree<0x7f000001
    omega
  refine ⟨elimination g,d02 (lower_irreducible h.1.1 h.2.2.1) hchar,?_,?_,?_⟩
  · have htb:a.t≤a.b:=(Nat.div_le_self _ _).trans
      ((z8K _ 3).trans (le_max_right _ _))
    have hw: (1 :Fin 3→ℕ) 2*a.t≤a.b:= by simpa only [Pi.one_apply,one_mul]
    have hh:=elimination_cap g (1 :Fin 3→ℕ) (by rwa [weightedTotalDegree_one]) ht hw
    have hconst: (fun i:Fin 2=>(1 :Fin 3→ℕ) i.castSucc)=1 :=rfl
    rw [hconst,weightedTotalDegree_one,Pi.one_apply,one_mul] at hh
    exact hh
  · rw [C6]
    exact elimination_cap g (fun i:Fin 3=>i.val) (C6 g ▸ hj) ht (by
      change 2*((shape R).j/2)≤(shape R).j
      omega)
  · intro γ hγ
    obtain ⟨hr,hp⟩:=Finset.mem_filter.mp hγ
    have hz :cK R (extend (C.s γ))=0 :=
      BO.bfW (Finset.mem_filter.mp hr).2 (orderAt_ord C R γ)
    rw [bUq R _ h.2.2.1] at hz
    exact (d0Z g _ hz).resolve_right fun ⟨_,hs⟩=>hs.2 hp
private def cap (B J:ℕ) (f :af 2) :ℕ :=
  cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) (BJ gZ B)
    (YM gZ B J)
private theorem ceY {w Γ s B J} (h:Messages w Γ s) (hJ:0<J)
    (f :af 2) (hf :Irreducible f) (hp:0<f.degreeOf 1)
    (hb:f.totalDegree≤B) (hj:f.degreeOf 1≤J)
    (hr : ∀ γ∈Γ,qg 1 f (extend (s γ))) :
    46402*Γ.card≤82317*cap B J f+46402 := by
  obtain ⟨T⟩:=czH.proof f gZ B J (by decide) (by decide) hJ hb hj
  have ha :0<BJ gZ B:= by simp [BJ]
  have hv :0<YM gZ B J :=
    lt_min ha ((by decide :0<gZ).trans_le (Nat.le_add_left _ _))
  apply P6_6_5.bv5 h
  intro i hi
  exact cz7.a8m h.distinct f hf hp hr ha hv i hi
    (T.cut (P6.node i) (w i)) (aVQ _ (T.ags _ _) (T.top_bound _ _))
    (fun γ hγ=>T.agrees _ (h.degree γ hγ) (hr γ hγ) _ _)
private theorem ebC {w Γ s B J} (h:Messages w Γ s) (hB:2≤B) (hchar :B<K1.p)
    (hJ:0<J) (q:af 2) (hq:q≠0) (hb:q.totalDegree≤B) (hj:qE q≤J)
    (hr : ∀ γ∈Γ,cK q (extend (s γ))=0) :
    46402*Γ.card≤82317*firstMixed B J+46402*B^2 := by
  classical
  let _:StrongNormalizationMonoid (af 2) :=UniqueFactorizationMonoid.strongNormalizationMonoid
  let M:=normalizedFactors q
  let A:=M.toFinset
  let T:=A.filter fun f=>0<f.degreeOf 1
  have hsub:T⊆A:=zT0 _ _
  have hdiv : (∏ f∈A,f)∣q :=
    (Multiset.toFinset_prod_dvd_prod M).trans (prod_normalizedFactors hq).dvd
  have ht : ∑ f∈A,f.totalDegree≤B:= by
    have hh:=sum_weightedTotalDegree_le_of_prod_dvd (1 :Fin 2→ℕ) A id hq hdiv
    simp only [id_eq,weightedTotalDegree_one] at hh
    exact hh.trans hb
  have hi : ∑ f∈A,f.degreeOf 1≤J:= by
    apply (zQk fun f _=>bZ3 f).trans
    have hh:=sum_weightedTotalDegree_le_of_prod_dvd (fun i:Fin 2=>i.val) A id hq hdiv
    simpa only [id_eq,← C6] using hh.trans (C6 q ▸ hj)
  have hf (f :af 2) (hf :f∈A) :Irreducible f :=
    irreducible_of_normalized_factor f (Multiset.mem_toFinset.mp hf)
  have hg (f :af 2) (hm:f∈A) :=
    bpk hB hchar f (hf f hm)
      ((zfK (fun x _=>zD0 x.totalDegree) hm).trans ht)
  let u := ∏ f∈A,QI f
  let iy :=Γ.filter fun γ=>u.eval (extend (s γ))=0
  let part (f :af 2) :=Γ.filter fun γ=>qg 1 f (extend (s γ))
  have ho:iy.card≤B*(B - 1) := calc
    _≤u.natDegree :=fX6 (h.mono (zT0 _ _)) u
      (Finset.prod_ne_zero_iff.mpr fun f hm=>(hg f hm).1)
      (fun _ hγ=>(Finset.mem_filter.mp hγ).2)
    _ ≤ ∑ f∈A,(QI f).natDegree :=Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ f∈A,f.totalDegree*(B - 1) :=zQk fun f hm=>(hg f hm).2.1
    _≤B*(B - 1) := by rw [← Finset.sum_mul]; exact ztf _ ht
  have hcover :Γ⊆iy∪T.biUnion part:= by
    intro γ hγ
    have hv :=map_dvd (zY9 (jet (extend (s γ)))) (prod_normalizedFactors hq).symm.dvd
    change cK q (extend (s γ))∣zY9 (jet (extend (s γ))) M.prod at hv
    rw [hr γ hγ,zero_dvd_iff,map_multiset_prod,Multiset.prod_eq_zero_iff,Multiset.mem_map] at hv
    obtain ⟨f,hm,hz⟩:=hv
    have hmA:f∈A:=Multiset.mem_toFinset.mpr hm
    rcases (hg f hmA).2.2 _ hz with hu | ⟨hp,hreg⟩
    · apply Finset.mem_union_left _
      exact Finset.mem_filter.mpr ⟨hγ,show Polynomial.evalRingHom _ u=0 by
        rw [show u = ∏ f∈A,QI f from rfl,map_prod]
        exact Finset.prod_eq_zero hmA hu⟩
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨f,Finset.mem_filter.mpr ⟨hmA,hp⟩,Finset.mem_filter.mpr ⟨hγ,hreg⟩⟩)
  have hp (f :af 2) (hm:f∈T) :0<f.degreeOf 1 :=(Finset.mem_filter.mp hm).2
  have hcount:46402*(T.biUnion part).card≤82317*(∑ f∈T,cap B J f)+46402*T.card:= calc
    _≤46402*(∑ f∈T,(part f).card) :=zBI _ Finset.card_biUnion_le
    _ = ∑ f∈T,46402*(part f).card:=Finset.mul_sum _ _ _
    _ ≤ ∑ f∈T,(82317*cap B J f+46402) := by
      refine zQk fun f hm=>ceY (h.mono (zT0 _ _)) hJ f
        (hf f (hsub hm)) (hp f hm) ?_ ?_ (fun _ hγ=>(Finset.mem_filter.mp hγ).2)
      · exact (zfK (fun x _=>zD0 x.totalDegree) (hsub hm)).trans ht
      · exact (zfK (fun x _=>zD0 (x.degreeOf 1)) (hsub hm)).trans hi
    _ = _:= by simp [zfW,Finset.mul_sum,z5A]
  have ht' : ∑ f∈T,f.totalDegree≤B :=
    (zZL hsub).trans ht
  have hn:T.card≤B:= calc
    _ = ∑ _∈T,1 :=Finset.card_eq_sum_ones _
    _ ≤ ∑ f∈T,f.totalDegree :=zQk fun f hm =>
      (hp f hm).trans_le (f.degreeOf_le_totalDegree 1)
    _≤_:=ht'
  have hmix : (∑ f∈T,cap B J f)≤firstMixed B J:= by
    simp only [cap,cappedDegreeMixedVolume,zfW,← Finset.sum_mul,firstMixed]
    exact Nat.add_le_add (ztf _ ht')
      (ztf _ ((zZL hsub).trans hi))
  have hcard:=(Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hsq:B*(B - 1)+B=B^2 := by
    rw [pow_two,← Nat.mul_succ,Nat.succ_eq_add_one,Nat.sub_add_cancel (by omega :1≤B)]
  omega
theorem proof :q6t08kb.c1 := by
  classical
  intro C R l ell h
  let a :=lowerBody (shape R)
  let B:=projectionTotal a
  let J:=projectionIndex a
  obtain ⟨q,hq,hb,hj,hr⟩:=project h
  have hbox :=h.2.1.2.2.1
  have hb' : (shape R).b≤4025:=hbox.1.trans (z7J _ _)
  have hj' : (shape R).j≤1710 :=hbox.2.1.trans (z7J _ _)
  have ha :a.b≤4025:=max_le hb' (by change (shape R).j+3≤4025; omega)
  have ht:2*a.t - 1≤1709:= by change 2*((shape R).j/2) - 1≤1709; omega
  have hchar :B<K1.p:= by
    have hh:=Nat.mul_le_mul ht ha
    change max a.b ((2*a.t - 1)*a.b-a.t^2)<0x7f000001
    omega
  have hab:2≤a.b:=(by decide :2≤3).trans
    ((Nat.le_add_left _ _).trans (le_max_right _ _))
  have hB:2≤B:=hab.trans (le_max_left _ _)
  have hJ:0<J:=(lt_of_lt_of_le (by decide :0<2) h.2.2.2).trans_le (le_max_left _ _)
  have hmsg :=C.messages.mono (Δ:=singular C R) <|
    (zT0 _ _).trans (zT0 _ _)
  simpa only [d1C,ee8,B,J,a] using ebC hmsg hB hchar hJ q hq hb hj hr
end
end q4DKPnb
end
section
set_option autoImplicit true
namespace qgLc7la
noncomputable section
open aR (af ao Shape cK qE)
open oR (qg)
open we (eT DO ag9 graph zq)
open yz (aCt F3)
open P6_6 (gZ bf LN Wk)
open P6_6_5 (Fb tC)
open qSCPCwb (Dm Vk Uj afs)
open MvPolynomial
open scoped Polynomial
structure FactorBox (a :Shape) (f :af 3) :Prop where
  irreducible :Irreducible f
  proper : ¬ Fb f
  gap:a.j+3≤a.b
  index_pos :2≤a.j
  top_eq :a.t=a.j/2
  total_max :a.b≤Wk.b
  index_max :a.j≤Wk.j
  total:f.totalDegree≤a.b
  index :qE f≤a.j
  top:f.degreeOf 2≤a.t
abbrev RY (a :Shape) :=LN (bf+2) a
abbrev Wa (a :Shape) :=aCt (RY a) bf
def i9 (a :Shape) (f :af 3) (P:Ideal (eT 3)) :=
  (F3 f P).comap (monomialMap we.cH (Wa a))
def pN (a :Shape) (f :af 3) (P:Ideal (eT 3)) :ℚ :=
  affineDegree (i9 a f P)
structure Gf (a :Shape) (f :af 3) where
  cut:eT 4
  next:eT 4
  numerator :Fin aR.bf→eT 4
  graph_box :DO (graph f) (tC a) 1
  cut_box :DO cut (LN (bf+1) a) (bf - 1)
  next_box :DO next (RY a) bf
  coefficient_box : ∀ i,DO (numerator i) (LN bf a) (bf - 2)
  cut_represents :ag9 f (Dm f) cut
  next_represents :ag9 f (Vk f) next
  actual : ∀ S:ao[X],S.natDegree≤gZ→qg 2 f S →
    cK (Dm f) S=0∧cK (Vk f) S=0 ∧
      Uj f numerator (zq S)=afs S
end
end qgLc7la
end
section
set_option autoImplicit true
namespace qgLc7la
noncomputable section
open aR (af Shape shape)
open Ex (X7 C6 YN aQU)

open we (eT DO ag9)
open P6_6 (tB aWx Wk gZ bf LN)
open q6t08kb (HigherIndex lowerBody)
open qSCPCwb (Dm Vk)
open qeu0RUc (yD avw cfr)
open MvPolynomial
open scoped Polynomial
open private b7n from ProximityPrize.SubmissionLower.B7
open private cBi from ProximityPrize.SubmissionLower.BF
open private cut next support from ProximityPrize.SubmissionLower.CD
open private actual a6m from ProximityPrize.SubmissionLower.Zqmzf9b
open private aEA from ProximityPrize.SubmissionLower.A3
open private gre from ProximityPrize.SubmissionLower.ZZMyKHc
open private bHC from ProximityPrize.SubmissionLower.BG
private theorem anchor_irreducible {R:af 4} (hR:Irreducible R) (ht: (shape R).t=0) :
    Irreducible (X7 R) := by
  have hi:=hR.map YN
  have hd:=(aQU R).trans ht
  have he :YN R=z1z (X7 R) := by
    simpa only [ X7,z4w,hd] using
      Polynomial.eq_C_of_natDegree_le_zero hd.le
  rw [he] at hi
  refine ⟨fun h=>hi.not_isUnit (Polynomial.isUnit_C.mpr h),?_⟩
  intro x y h
  exact (hi.isUnit_or_isUnit (by rw [h,Polynomial.C_mul])).imp
    Polynomial.isUnit_C.mp Polynomial.isUnit_C.mp
theorem factorBox {C R l ell} (h:HigherIndex C R l ell) (hw : ¬ q6t08kb.acA R) :
    FactorBox (lowerBody (shape R)) (X7 R) := by
  let a :=lowerBody (shape R)
  let f :=X7 R
  have hb:=b7n R (1 :Fin 4→ℕ)
  change f.weightedTotalDegree 1+1*(shape R).t≤R.weightedTotalDegree 1 at hb
  rw [weightedTotalDegree_one,weightedTotalDegree_one,h.2.2.1,mul_zero,add_zero] at hb
  have hj:=b7n R (fun i=>i.val)
  change f.weightedTotalDegree (fun i=>i.val)+3*(shape R).t ≤
    R.weightedTotalDegree (fun i=>i.val) at hj
  rw [← C6,← C6,h.2.2.1,mul_zero,add_zero] at hj
  have hbox :=h.2.1.2.2.1
  have hjmax :a.j≤Wk.j:=hbox.2.1.trans (z7J _ _)
  have hbmax :a.b≤Wk.b:=max_le (hbox.1.trans (z7J _ _)) (by
    change a.j≤1710 at hjmax
    change a.j+3≤4025
    omega)
  refine ⟨anchor_irreducible h.1.1 h.2.2.1,hw,le_max_right _ _,h.2.2.2,rfl,
    hbmax,hjmax,hb.trans (le_max_left _ _),hj,?_⟩
  rw [degreeOf_le_iff]
  intro m hm
  have hi:=le_weightedTotalDegree (fun i:Fin 3=>i.val) hm
  rw [← C6] at hi
  have h2 :=Finsupp.apply_smul_le_weight (fun i:Fin 3=>i.val) m (2 :Fin 3)
  have hmul :2*m 2≤ m.weight (fun i=>i.val) := by
    simpa only [smul_eq_mul,z5A,show (2 :Fin 3).val = 2 by rfl] using h2
  exact (Nat.le_div_iff_mul_le (by decide :0<2)).mpr
    (by rw [Nat.mul_comm]; exact hmul.trans (hi.trans hj))
theorem anchor_weight {R:af 4} (h:tB R aWx) :
    tB (X7 R) aWx := by
  intro m hm
  obtain ⟨u,hu,hc,hle⟩:=cBi R m hm
  rw [← hc]
  apply (z3b _ _).trans (h u hu)
  simpa only [Finsupp.weight_apply,smul_eq_mul,z5A,Fin.val_castSucc] using
    hle (fun i=>gZ - i.val)
theorem qP {a f} (h:FactorBox a f) :Nonempty (Gf a f) := by
  obtain ⟨hg,he,hn,hc⟩:=support bf (by decide) f a h.total h.index h.top
  have hpad (j:Fin aR.bf) :
      DO (a6m f j) (LN bf a) (bf - 2) := by
    unfold a6m
    split_ifs with hi
    · exact hc ⟨j.val,hi⟩
    · simp [DO]
  have hrep:ag9 f (Dm f) (cut bf f) :=
    aEA f (bf-3)
  have hrep' : ag9 f (Vk f) (next bf f) :=
    aEA f (bf - 2)
  exact ⟨⟨cut bf f,next bf f,a6m f,hg,he,hn,hpad,
    hrep,hrep',actual hrep hrep'⟩⟩
theorem aIn (a :Shape) (i:Fin 4) :
    Finsupp.single i 1∈Wa a := by
  let r :=bf+2 - 4
  have ht:1≤ min (1+r*(a.t+2)) ((2+r*(a.j+2))/2) :=
    le_min (z8K _ _) (by omega)
  exact gre (RY a) bf (z8K 1 _) (z8K 2 _)
    ht (by decide) i
theorem gnI {a f} (hf :Irreducible f) {P:Ideal (eT 3)}
    (hP:P∈yD f) :
    (i9 a f P).IsPrime∧(affineHilbertPolynomial (i9 a f P)).natDegree=1 := by
  have hm:=Ideal.mem_retainedMinimalPrimes.mp (avw.mp hP).2
  let:=hm.1.isPrime
  obtain ⟨hp,hd⟩:=bHC f P hm.2
  refine ⟨hp.comap _,?_⟩
  unfold i9
  rw [natDegree_affineHilbertPolynomial_comap_of_surjective _
    (monomialMap_surjective (aIn a)),hd,cfr hf hP]
end
end qgLc7la
end
