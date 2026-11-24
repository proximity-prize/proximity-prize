import ProximityPrize.SubmissionLower.A1
import ProximityPrize.SubmissionLower.A2
import ProximityPrize.SubmissionLower.O
set_option Elab.async false
set_option maxHeartbeats 800000
set_option autoImplicit true
section
namespace aZw
noncomputable section
open Polynomial
open P0 (DY)
open cu (fO)

open scoped BigOperators
def kA (w:ℤ) :fO :=
 if w≤3554 then ⟨3554,6,188,1024,1422,290,28962⟩
 else if w≤8249 then ⟨8249,4,96,582,809,165,11805⟩
 else if w≤23999 then ⟨23999,4,46,582,809,165,8216⟩
 else ⟨DY,4,35,582,809,165,7295⟩
def dI (i:Fin 2) :ℕ := ![0,5] i
end
end aZw
end
section
namespace aZw
noncomputable section
open Polynomial Finset ProximityPrize.Benchmark

private theorem azg (errors m x gap cap:ℕ)
    (hm:0< m) (hg:0<gap) (hx :gap≤x) (he :0<errors)
    (hsecond: (m*x)^2≤(x+errors)*(m*(x+(m-1)*(x-gap))))
    (hfirst:m*x≤(x+errors)*cap) :
    gap*m≤errors*cap+gap:= by
  have hcancel:m*x^2≤(x+errors)*(x+(m-1)*(x-gap)) := by
    apply Nat.le_of_mul_le_mul_left _ hm
    calc
      _=(m*x)^2 := by ring
      _≤_:=hsecond
      _ = _:= by ring
  have hM: ((m - 1 :ℕ) :ℤ)=(m:ℤ)-1 :=Int.ofNat_sub (by omega)
  have hX: ((x - gap:ℕ) :ℤ)=(x :ℤ)-gap:=Int.ofNat_sub hx
  have hcancelZ:=Int.ofNat_le.mpr hcancel
  push_cast [hM,hX] at hcancelZ
  have hfirstZ:=Int.ofNat_le.mpr hfirst
  push_cast at hfirstZ
  have secondZ: ((m:ℤ)*errors-((m:ℤ)-1)*gap)*x ≥
      ((m:ℤ)-1)*errors*gap:= by
    nlinarith only [hcancelZ]
  have firstZ: ((m:ℤ)-(cap:ℤ))*x≤(cap:ℤ)*errors := by
    nlinarith only [hfirstZ]
  by_contra! h
  have hbadZ: (errors :ℤ)*cap+gap<(gap:ℤ)*m:= by exact_mod_cast h
  have hbad: (cap:ℤ)*errors<((m:ℤ)-1)*gap:= by nlinarith only [hbadZ]
  have hxpos :0<(x :ℤ) := by omega
  have cmp: (m:ℤ)*errors-((m:ℤ)-1)*gap<((m:ℤ)-(cap:ℤ))*errors := by
    linarith only [hbad]
  have left:=mul_lt_mul_of_pos_right cmp hxpos
  have right:=mul_le_mul_of_nonneg_right firstZ (Int.natCast_nonneg errors)
  have impossible :=secondZ.trans_lt (left.trans_le (show
      ((m:ℤ)-(cap:ℤ))*errors*x≤(cap:ℤ)*errors*errors from by
        convert right using 1
        ring))
  have bigger :=mul_lt_mul_of_pos_right hbad (Int.ofNat_lt.mpr he)
  nlinarith only [impossible,bigger]
end
end aZw
end
section
set_option backward.isDefEq.respectTransparency false
namespace atp
noncomputable section



open DP Polynomial
open scoped Polynomial
open private bVD from ProximityPrize.SubmissionLower.Z
theorem dRH {h:ℕ} (D:jF h) :Nonempty (zG D) := by
 choose d N hN using bVD D
 exact ⟨⟨d,N,fun i=>(hN i).1,fun i=>(hN i).2.1,fun i=>(hN i).2.2.1,
  fun i=>(hN i).2.2.2.1,fun i=>(hN i).2.2.2.2⟩⟩
end
end atp
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace atp
noncomputable section
open K1 (I K node)
open cu (L Shape Jet j9 rD ku)
open DP cyT Polynomial
open bax (deX cHz dfg cHy)
open scoped Polynomial BigOperators
open private cSb aAC dib from ProximityPrize.SubmissionLower.Z
private theorem gNp {h A:ℕ} {D:jF h}
  (hnode : ∀ i k,(D.block i).eval (ad0 k)≠0)
  {s :Shape} {W:ℕ} {Q:L[X]}
  (hdeg:Q.natDegree≤W+(s.B+s.J)*(2*h))
  (hpole :Iy D^(s.B+s.J)∣Q)
  (lg:Finset I) (hcard:A≤lg.card)
  (hcontact : ∀ k∈lg,(Polynomial.X-C (ad0 k))^s.m∣Q)
  (hW:W<s.m*A) :Q=0:= by
 by_contra hne
 obtain ⟨T,hT⟩:=hpole
 have hTne :T≠0:= by intro he; simp [hT,he] at hne
 have hmonic: (Iy D).Monic:=(D.monic 0).mul (D.monic 1)
 have hDdeg: (Iy D).natDegree=2*h:= by
  rw [Iy,natDegree_mul (D.monic 0).ne_zero (D.monic 1).ne_zero,D.degree,D.degree]
  omega
 have hTdeg:T.natDegree≤W:= by
  rw [hT,natDegree_mul (pow_ne_zero _ hmonic.ne_zero) hTne,natDegree_pow,hDdeg] at hdeg
  omega
 have hroot (k :I) :IsCoprime (Polynomial.X-C (ad0 k)) (Iy D) := by
  refine (irreducible_X_sub_C _).coprime_iff_not_dvd.mpr ?_
  rw [dvd_iff_isRoot]
  simpa [IsRoot,Iy] using mul_ne_zero (hnode 0 k) (hnode 1 k)
 have hcontacts (k :I) (hk :k∈lg) : (Polynomial.X-C (ad0 k))^s.m∣T :=
  ((hroot k).pow.dvd_of_dvd_mul_left (hT ▸ hcontact k hk))
 have hinj:Function.Injective ad0:=(algebraMap K L).injective.comp node.injective
 have hh:=wT.aHG lg ad0 hinj s.m T hcontacts
  (hTdeg.trans_lt (hW.trans_le (Nat.mul_le_mul_left _ hcard)))
 exact hTne hh
theorem dPr {h A:ℕ} {D:jF h} (Crt:zG D) (word:I→L)
  (hnode : ∀ i k,(D.block i).eval (ad0 k)≠0)
  (z :K) (S:K[X]) (hres :aKF D z S)
  (hdeg: (j9 S).natDegree≤131071+h)
  (lg:Finset I) (hcard:A≤lg.card)
  (hhits : ∀ k∈lg,(j9 S).eval (ad0 k)=word k)
  (s :Shape) (W:ℕ) (hW:W<s.m*A) (P:Jet)
  (hP:P∈VY Crt word s W) :rD P z S=0:= by
 apply deX z S _ hP
 intro Q hQ
 obtain ⟨⟨ha,hc⟩,hp⟩:=hQ
 exact gNp hnode (cHz ha _ _ hdeg)
  (dfg Crt hres hp) lg hcard
  (fun k hk=>cHy hc _ _ k (hhits k hk)) hW
theorem bT9 {h:ℕ} (hhi:h≤131071) (s :Shape) (W:ℕ)
    (hw:c69 h s W) :
    ceG h s W+azS h s≤Module.finrank L (Aw h s W) := by
  rw [cSb]
  have hsum:ku s (aAC h s W) =
      ku s (fun q j=>W+1+j - q*(131071 - h)) +
        2*h*ku s (fun q _=>s.B+s.J - q) := by
    unfold ku
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro j hj
    exact dib hhi hw (by simpa using hq) (by simpa using hj)
  simp only [hsum,ceG,azS,Nat.mul_add,Nat.mul_assoc,Nat.le_refl]
end
end atp
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace atp
noncomputable section
open K1 (I)
open cu (L Shape Jet)
open DP Polynomial
open bjE (Bounded b3N bgu c55 bgw bgz
 dfH dfI)
open scoped Polynomial BigOperators
open private bVR a1T ahl afg aTi
 bVU cDr aMs bY9 blq from ProximityPrize.SubmissionLower.Z
open private ceD dfe dff aJB ady
 from ProximityPrize.SubmissionLower.Z
private theorem edA {h} (hpos :0<h) (hh:h≤131070) {D:jF h} (Crt:zG D)
    {s W P} (hp:P∈Aw h s W) :
    Bounded (131071-h) (131071-h-1) (W+(s.B+s.J)*(2*h)) (forward Crt P) := by
  let u:=131071-h
  let v :=u-1
  have huv :v+1=u:= by dsimp [u,v]; omega
  have hd:131071+h=2*h+u:= by dsimp [u]; omega
  have hy :Bounded u v (2*h+u) (bgw D Crt) :=
    a1T (afg (aTi (bgu D).le) (bVU u v))
      (aTi ((bY9 D Crt).trans (by omega)))
  have hv :Bounded u v (2*h+v) (bgz D Crt) := by
    have hh' : (IE D).derivative.natDegree≤2*h-1 :=
      (natDegree_derivative_le _).trans (by rw [bgu])
    refine a1T (a1T
      (afg (aTi (bgu D).le) (cDr u v)) ?_) ?_
    · exact bVR (afg (aTi hh') (bVU u v)) (by omega)
    · exact aTi (((natDegree_derivative_le _).trans
        (Nat.sub_le_sub_right (bY9 D Crt) 1)).trans (by omega))
  change Bounded u v _ (forward Crt P)
  rw [b3N,P.as_sum_support_C_mul_X_pow,map_sum]
  apply ahl
  intro j hj
  rw [map_mul,map_pow,(P.coeff j).as_sum_support_C_mul_X_pow]
  simp only [dfH,dfI]
  simp only [map_sum,map_mul,map_pow,Finset.sum_mul]
  simp only [coe_eval₂RingHom,eval₂_C,eval₂_X,RingHom.comp_apply]
  apply ahl
  intro i hi
  have hdeg:=blq hp (mem_support_iff.mp hi)
  have hw: ((P.coeff j).coeff i).natDegree+(2*h+u)*i+(2*h+v)*j ≤
      W+(s.B+s.J)*(2*h) := by
    have hjmul :j*(2*h+u)=(2*h+v)*j+j:= by
      rw [show 2*h+u=(2*h+v)+1 by omega,Nat.mul_add,Nat.mul_one,Nat.mul_comm j (2*h+v)]
    rw [hd,Nat.add_mul,hjmul,Nat.mul_comm i (2*h+u)] at hdeg
    omega
  apply bVR (afg (afg ?_ (aMs hy i)) (aMs hv j)) hw
  exact aTi natDegree_map_le
private theorem fTT {h} (hpos :0<h) (hh:h≤131070) {D:jF h} (Crt:zG D)
  (word:I→L) {s W P} (hP:P∈VY Crt word s W) (j i:ℕ)
  (hw:W<(131071-h)*i+(131071-h-1)*j) :ceD Crt j i P=0:= by
 have hsub:VY Crt word s W≤LinearMap.ker (ceD Crt j i) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨A,hA,rfl⟩
  apply LinearMap.mem_ker.mpr
  rcases hA.2 with ⟨Q,hQ⟩
  have hz :=c55 s W (edA hpos hh Crt hA.1.1) hQ j i hw
  change ((aJB Crt (U4 A)).coeff j).coeff i=0
  rw [dfe,hQ]
  simp only [map_mul,ady,coe_mapRingHom,Polynomial.map_C,pW,
    RingHom.comp_apply,coeff_C_mul,coeff_map,hz,map_zero,mul_zero]
 exact LinearMap.mem_ker.mp (hsub hP)
theorem eu5 {h:ℕ} (hl:0<h) (hh:h≤131070)
    {D:jF h} (Crt:zG D) (word:I→L) (s :Shape) (W:ℕ)
    (P:Jet) (hP:P∈VY Crt word s W) (hn:P≠0) :
    (P.leadingCoeff.natDegree+P.natDegree)*(131071-h)≤W+P.natDegree := by
  let j:=P.natDegree
  let i:=P.leadingCoeff.natDegree
  change (i+j)*(131071-h)≤W+j
  have huv :131071-h=(131071-h-1)+1 := by omega
  have he : (i+j)*(131071-h)=(131071-h)*i+(131071-h-1)*j+j:= by
    have hj:j*(131071-h)=(131071-h-1)*j+j:= by
      calc
        j*(131071-h)=j*((131071-h-1)+1) :=congrArg (j*·) huv
        _=(131071-h-1)*j+j:= by ring
    rw [Nat.add_mul,hj,Nat.mul_comm i]
    omega
  rw [he]
  by_contra! hw
  have hz :=fTT hl hh Crt word hP j i (by omega)
  obtain ⟨hj,hi,hn'⟩:=dff Crt hn
  change ((aJB Crt P).coeff j).coeff i=0 at hz
  have hj' : (aJB Crt P).natDegree=j:=hj
  have hi' : (aJB Crt P).leadingCoeff.natDegree=i:=hi
  rw [← hj',coeff_natDegree,← hi',coeff_natDegree] at hz
  exact (leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn')) hz
end
end atp
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace atp
noncomputable section
open K1 (I)
open cu (L FX Shape Jet ku triangle A5)
open DP axj Polynomial
open scoped Polynomial BigOperators
open private X3.mk avt generators bRG.nodeMap cYx from ProximityPrize.SubmissionLower.Z
open private aUq cNg cEw from ProximityPrize.SubmissionLower.Z
theorem Yw (h:ℕ) (word:I→L) (s :Shape) (W:ℕ) :
    Module.finrank L (Aw h s W) ≤
      bga s+Module.finrank L (aq7 h word s W) := by
  classical
  by_cases hzero :Module.finrank L (Aw h s W)=0
  · simp [hzero]
  have :Module.Finite L (Aw h s W) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hzero)
  have :Module.Finite L (avt s) :=
    Module.Finite.span_of_finite L (Set.finite_range (generators s))
  let f :Aw h s W →ₗ[L] (I→avt s) :=
    LinearMap.pi (bRG.nodeMap h word s W)
  let g:LinearMap.ker f →ₗ[L] aq7 h word s W :=
    LinearMap.codRestrict (aq7 h word s W)
      ((Aw h s W).subtype.comp (LinearMap.ker f).subtype) (by
        intro P
        refine ⟨P.val.property,?_⟩
        intro i a b j e hab
        have hz :=LinearMap.mem_ker.mp P.property
        exact congrArg (fun z :I→avt s=>(z i).val (X3.mk j b a e hab)) hz)
  have hg:Function.Injective g:= by
    intro P Q hPQ
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun R:aq7 h word s W=>R.val) hPQ
  have hle :aq7 h word s W≤Aw h s W:=inf_le_left
  have :Module.Finite L (aq7 h word s W) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hker :=LinearMap.finrank_le_finrank_of_injective hg
  have hnull:=f.finrank_range_add_finrank_ker
  have htarget :Module.finrank L (I→avt s)≤bga s := by
    rw [Module.finrank_pi_fintype]
    calc
      (∑ _:I,Module.finrank L (avt s)) ≤
          ∑ _:I,(ku s (fun q k=>s.m+min q s.J-(q+2*k)))*triangle s.U :=
        Finset.sum_le_sum (fun _ _=>cYx s)
      _=bga s := by
        rw [Finset.sum_const,Finset.card_univ,ProximityPrize.Benchmark.IRSProfile.card_index,
          smul_eq_mul,bga]
        ac_rfl
  have hrange :=(LinearMap.range f).finrank_le.trans htarget
  omega
theorem d3s {h:ℕ} {D:jF h} (Crt:zG D) (word:I→L)
    {s :Shape} {W:ℕ} {P:Jet} (hP:P∈VY Crt word s W) (i:Fin 2) (r :ℕ) :
    A5 i r P∈VY Crt word s (W+2*h*r) := by
  let target :=VY Crt word s (W+2*h*r)
  have hsub:VY Crt word s W≤target.comap (aUq i r) :=
    Submodule.span_le.mpr (by
      rintro _ ⟨Q,hQ,rfl⟩
      change aUq i r (U4 Q)∈target
      have hmem:BA D i r Q∈complete Crt word s (W+2*h*r) :=
        ⟨⟨ds6 D hQ.1.1 i r,cyS.proof h D word s Q hQ.1.2 i r⟩,
          bay.proof h D Crt s Q hQ.2 i r⟩
      have he :U4 (BA D i r Q)∈target :=
        Submodule.subset_span ⟨BA D i r Q,hmem,rfl⟩
      rw [cEw] at he
      have hn:algebraMap L[X] FX (D.block i^(2*r))≠0:= by
        rw [← map_zero (algebraMap L[X] FX)]
        exact (IsFractionRing.injective L[X] FX).ne (pow_ne_zero (2*r) (D.monic i).ne_zero)
      exact (target.smul_mem_iff hn).mp he)
  rw [← cNg]
  exact hsub hP
end
end atp
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace dnG
noncomputable section
open cu DP Ge aY9 Polynomial
open scoped BigOperators Polynomial
open private bqB cTI from ProximityPrize.SubmissionLower.Z
private theorem c7U {h:ℕ} (hh:0<h) (hp:h<K1.p)
   (D:jF h) (Crt:zG D) :Nonempty (cAi D Crt) := by
 let B : ∀ i,bQl D Crt i:=a1P hh D Crt
 let den:=(B 0).den*(B 1).den
 let num :=C (B 1).den*(B 0).num+C (B 0).den*(B 1).num
 have hden:Uw den≠0:= by
   dsimp only [den]
   rw [map_mul]
   exact mul_ne_zero (B 0).specialDen (B 1).specialDen
 have hmonic: (bfF D).Monic :=
   (aVZ hh D 0).monic.mul (aVZ hh D 1).monic
 refine ⟨⟨bfF D,num,den,hmonic,?_,hden,?_,bqB hden,?_⟩⟩
 · rw [bfF,Polynomial.map_mul,b9t,b9t,Iy]
 · dsimp only [num,den]
   rw [cXv _ _ _ _ _ (B 0).specialDen (B 1).specialDen,
     (B 0).specialLift,(B 1).specialLift,OY,Fin.sum_univ_two]
 · apply gq6 hh hp D _
   intro i α hr hb
   dsimp only [num,den]
   rw [cXv _ _ _ _ _ (bqB (B 0).specialDen) (bqB (B 1).specialDen)]
   simpa only [Fin.sum_univ_two] using cTI B i α hr hb
end
end dnG
end
section
namespace bjU
open cu (Shape slots)

open Finset
open scoped BigOperators
def cut (s :Shape) (v lo t:ℕ) :ℕ :=
  min (s.B+1)
    ((s.m*P0.dw+(t - min t (s.U/v)) - 2*lo*t - 1)/(131071-lo)+1)
def weight (s :Shape) (v r :ℕ) :ℕ :=
 slots s.U (r*v) - slots s.U ((r+1)*v)
end bjU
end
section
namespace bjU
open cu (Shape slots)

open Finset
open scoped BigOperators
private def cAt (s :Shape) (v lo t:ℕ) :Prop :=
 let k :=cut s v lo t
 min t s.J≤k∧(k-1)*(131071-lo)+2*lo*t<s.m*P0.dw+(t - min t (s.U/v))
private instance (s :Shape) (v lo t:ℕ) :Decidable (cAt s v lo t) := by
 unfold cAt
 infer_instance
private def bsK (s :Shape) (v i:ℕ) :ℕ×ℕ×ℕ :=
 let R:=s.U/v
 let n:=min R i
 let a :=weight s v 0
 let b:=v*v
 let s₁:=n*(n-1)/2
 let s₂:=n*(n-1)*(2*n-1)/6
 let last :=if R< i then slots s.U (R*v) else 0
 ⟨a*n - b*s₁+last,a*s₁ - b*s₂+last*R,a*s₂ - b*s₁*s₁+last*R*R⟩
private def czP (s :Shape) (v r :ℕ) :Prop :=
 let w:=weight s v r
 let p:=bsK s v r
 let q:=bsK s v (r+1)
 q.1=p.1+w∧q.2.1=p.2.1+w*r∧q.2.2=p.2.2+w*r*r
private instance (s :Shape) (v r :ℕ) :Decidable (czP s v r) := by
 unfold czP
 infer_instance
structure af where
 ok :Bool
 base :ℤ
 slope :ℤ
def af.add (x y :af) :af :=⟨x.ok && y.ok,x.base+y.base,x.slope+y.slope⟩
def scan (f :ℕ→af) (a :ℕ) :ℕ→af
 | 0=>⟨true,0,0⟩
 | n+1=>(scan f a n).add (f (a+n))
private theorem dcl (f :ℕ→af) (a n m:ℕ) :
   scan f a (n+m)=(scan f a n).add (scan f (a+n) m) := by
 induction m with
 | zero=>cases scan f a n; simp [scan,af.add]
 | succ m ih =>
   change (scan f a (n+m)).add (f (a+(n+m))) =
    (scan f a n).add ((scan f (a+n) m).add (f ((a+n)+m)))
   rw [ih]
   simp only [af.add,Bool.and_assoc,add_assoc]
private theorem coM (f :ℕ→af) (a n:ℕ) (slope :Bool) :
   (if slope then (scan f a n).slope else (scan f a n).base) =
     ∑ i∈range n,if slope then (f (a+i)).slope else (f (a+i)).base := by
 cases slope <;> induction n with
 | zero=>simp [scan]
 | succ n ih=>simp_all only [scan,af.add,Bool.false_eq_true,ite_false,ite_true,
     sum_range_succ]
end bjU
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace dnk
noncomputable section
open cu gT atd
open XY (ag6)
private theorem c5I {P Q:Jet} (h:ag6 P Q)
   (I:Ideal Jet) [I.IsPrime] (hP:P∈I) (hQ:Q∈I) :2≤I.height:= by
 have hne :I ≠ ⊥ := fun e=>h.left_ne (by simpa [e] using hP)
 obtain ⟨D,hD,hp⟩:=Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹I.IsPrime› hne
 let J:Ideal Jet:=Ideal.span {D}
 have :J.IsPrime :=(Ideal.span_singleton_prime hp.ne_zero).mpr hp
 have hJ₀:J ≠ ⊥ := fun e=>hp.ne_zero (Ideal.span_singleton_eq_bot.mp e)
 have hJ₁:1≤J.height :=
   Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hJ₀)
 have hJI:J<I:= by
   refine lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem I).mpr hD) ?_
   intro e
   exact h.no_common D hp.irreducible
     (Ideal.mem_span_singleton.mp (e ▸ hP:P∈J))
     (Ideal.mem_span_singleton.mp (e ▸ hQ:Q∈J))
 calc
   2=1+1 := by decide
   _≤J.height+1 :=add_le_add hJ₁ le_rfl
   _≤I.height:=Ideal.height_add_one_le_of_lt_of_isPrime hJI
end
end dnk
end
