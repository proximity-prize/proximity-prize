import ProximityPrize.SubmissionLower.DT
import ProximityPrize.SubmissionLower.Zeg869c
import ProximityPrize.SubmissionLower.ZikYn6c
set_option Elab.async false
section
set_option autoImplicit true
namespace qa84RQb
noncomputable section
open Finset PolynomialDifferential ReedSolomon.HiddenDerivative
open xE (UT topWeight)
open P6_6 (gZ aWx)
open P6_6_2 (columns bFE FF)
open Rw (qB)
open private exponent equiv from ProximityPrize.SubmissionLower.DT
open private plateau gradeCap_eq from ProximityPrize.SubmissionLower.Zeg869c
def width (q j:ℕ) :ℕ:=0x2027d3a8+j - 133425*q
def tuples (B:ℕ) :Finset qB :=
  (range 571).sigma fun f =>
    (range ((1710-3*f)/2+1)).sigma fun c =>
      (range (1711 - 2*c-3*f)).sigma fun b =>
        (range (B+1 - b - c - f)).sigma fun a =>
          range (width (a+b+c+f) (b+2*c+3*f))
def arF:qB→Prop
  | ⟨f,c,b,a,_⟩=>b+c+f≤plateau (a+b+c+f)
instance (t:qB) :Decidable (arF t) := by
  rcases t with ⟨f,c,b,a,x⟩
  unfold arF
  infer_instance
def bad (B:ℕ) :Finset qB:=(tuples B).filter fun t => ¬ arF t
theorem bfA (B f c b a x :ℕ) :
    (⟨f,c,b,a,x⟩:qB)∈tuples B ↔
      f≤570∧b+2*c+3*f≤1710∧a+b+c+f≤B ∧
        x<width (a+b+c+f) (b+2*c+3*f) := by
  simp only [tuples,mem_sigma,mem_range]
  omega
private theorem aVS (t:qB) :
    exponent t∈columns↔t∈(tuples 4025).filter arF:= by
  rcases t with ⟨f,c,b,a,x⟩
  change exponent ⟨f,c,b,a,x⟩∈bFE.toFinset↔_
  rw [Set.Finite.mem_toFinset,mem_filter,bfA]
  change FF (exponent ⟨f,c,b,a,x⟩)↔_
  have hgrade : (exponent ⟨f,c,b,a,x⟩).some.degree=a+b+c+f := by
    simp [Finsupp.degree_eq_sum,Fin.sum_univ_four,exponent]
  rw [FF,hgrade,gradeCap_eq]
  simp only [Finsupp.weight_eq_sum,Fintype.sum_option,Fin.sum_univ_succ,Fin.sum_univ_zero,
    smul_eq_mul,jetDegreeWeight_none,jetDegreeWeight_some,jetDerivativeWeight,
    differentialWeight,topWeight,Option.elim_none,Option.elim_some,exponent,
    Finsupp.coe_equivFunOnFinite_symm,show gZ=133425 by rfl,arF,le_min_iff]
  simp [width,show aWx=0x2027d3a7 by rfl]
  omega
private theorem card_of_columns {u:Finset UT} {v :Finset qB}
    (h : ∀ t,exponent t∈u↔t∈v.filter arF) :
    u.card+(v.filter fun t => ¬ arF t).card=v.card:= by
  have hc: (v.filter arF).card=u.card:=card_equiv equiv fun t=>(h t).symm
  rw [← hc]
  exact card_filter_add_card_filter_not arF
theorem bWu:columns.card+(bad 4025).card=(tuples 4025).card :=
  card_of_columns aVS
end
end qa84RQb
end
section
set_option autoImplicit true
namespace qa84RQb
open Finset
open Rw (amJ bKe)
open scoped BigOperators
private def acQ (W a b c f :ℤ) :ℤ :=
  W+b+2*c+3*f - 133425*(a+b+c+f)
private theorem bWy (B a b c f :ℕ) (hW:133425*B≤0x2027d3a8)
    (h:a+b+c+f≤B) : (width (a+b+c+f) (b+2*c+3*f) :ℤ)=acQ 0x2027d3a8 a b c f := by
  have hpos :133425*(a+b+c+f)≤0x2027d3a8+(b+2*c+3*f) := by omega
  simp only [width,acQ,Nat.cast_sub hpos,Nat.cast_ofNat,Nat.cast_add,Nat.cast_mul]
  ring
private def aEf (W b c f n:ℤ) :ℤ :=
  n*(2*acQ W 0 b c f - 133425*(n - 1))
private def aC1 (W B b c f :ℤ) :ℤ :=
  aEf W b c f (B+1 - b - c - f)
private def avU (W B c f n:ℤ) :ℤ :=
  let p:=B+1 - c - f
  let q:=2*acQ W 0 0 c f - 133425*(p - 1)
  let r :=2 - 133425
  6*n*p*q+3*n*(n - 1)*(p*r - q) - n*(n - 1)*(2*n - 1)*r
private def aae (W B J c f :ℤ) :ℤ :=
  avU W B c f (J+1 - 2*c-3*f)
private def aoQ (W B J f n:ℤ) :ℤ :=
  let v₀:=aae W B J 0 f
  let v₁:=aae W B J 1 f
  let v₂:=aae W B J 2 f
  let v₃:=aae W B J 3 f
  24*n*v₀+12*n*(n - 1)*(v₁ - v₀) +
    4*n*(n - 1)*(n - 2)*(v₂ - 2*v₁+v₀) +
    n*(n - 1)*(n - 2)*(n-3)*(v₃-3*v₂+3*v₁ - v₀)
private def aCN (B b c f :ℕ) :ℤ :=
  ∑ a∈range (B+1 - b - c - f),(width (a+b+c+f) (b+2*c+3*f) :ℤ)
private def auI (B J c f :ℕ) :ℤ :=
  ∑ b∈range (J+1 - 2*c-3*f),aCN B b c f
private def aCO (B J f :ℕ) :ℤ :=
  ∑ c∈range ((J-3*f)/2+1),auI B J c f
private theorem bWv (B:ℕ) :
    ((tuples B).card:ℤ) = ∑ f∈range 571,aCO B 1710 f := by
  simp only [tuples,card_sigma,card_range,Nat.cast_sum,aCO,auI,aCN]
private theorem bYS (B b c f :ℕ) (hW:133425*B≤0x2027d3a8)
    (h:b+c+f≤B) :2*aCN B b c f=aC1 0x2027d3a8 B b c f := by
  have hsum:aCN B b c f = ∑ a∈range (B+1 - b - c - f),acQ 0x2027d3a8 a b c f := by
    apply sum_congr rfl
    intro a ha
    rw [mem_range] at ha
    exact bWy B a b c f hW (by omega)
  rw [hsum,amJ 2 (fun a=>acQ 0x2027d3a8 a b c f) (aEf 0x2027d3a8 b c f)
    (by simp [aEf]) (by intro t; unfold aEf acQ; ring)]
  have hn: ((B+1 - b - c - f :ℕ) :ℤ)=(B:ℤ)+1 - b - c - f := by omega
  rw [hn,aC1]
private theorem bYT (B J c f :ℕ) (hW:133425*B≤0x2027d3a8)
    (hJB:J≤B) (h:2*c+3*f≤J) :
    12*auI B J c f=aae 0x2027d3a8 B J c f := by
  calc
    12*auI B J c f =
        ∑ b∈range (J+1 - 2*c-3*f),6*(2*aCN B b c f) := by
      simp only [auI,← mul_assoc,← mul_sum,show (6:ℤ)*2=12 by decide]
    _=6 * ∑ b∈range (J+1 - 2*c-3*f),aC1 0x2027d3a8 B b c f := by
      rw [mul_sum]
      apply sum_congr rfl
      intro b hb
      rw [mem_range] at hb
      rw [bYS B b c f hW (by omega)]
    _=aae 0x2027d3a8 B J c f := by
      rw [amJ 6 (fun b=>aC1 0x2027d3a8 B b c f) (avU 0x2027d3a8 B c f)
        (by simp [avU]) (by intro t; unfold avU aC1 aEf acQ; ring)]
      have hn: ((J+1 - 2*c-3*f :ℕ) :ℤ)=(J:ℤ)+1 - 2*c-3*f := by omega
      rw [hn,aae]
private def ajj (B J f :ℕ) :ℤ :=
  aoQ 0x2027d3a8 B J f ((J-3*f)/2+1 :ℕ)
private theorem bYU (B J f :ℕ) (hW:133425*B≤0x2027d3a8)
    (hJB:J≤B) (hf :3*f≤J) :288*aCO B J f=ajj B J f := by
  calc
    288*aCO B J f =
        ∑ c∈range ((J-3*f)/2+1),24*(12*auI B J c f) := by
      simp only [aCO,← mul_assoc,← mul_sum,show (24 :ℤ)*12=288 by decide]
    _=24 * ∑ c∈range ((J-3*f)/2+1),aae 0x2027d3a8 B J c f := by
      rw [mul_sum]
      apply sum_congr rfl
      intro c hc
      rw [mem_range] at hc
      rw [bYT B J c f hW hJB (by omega)]
    _=ajj B J f := by
      rw [amJ 24 (fun c=>aae 0x2027d3a8 B J c f) (aoQ 0x2027d3a8 B J f)
        (by simp [aoQ]) (by intro t; unfold aoQ aae avU acQ; ring)]
      rfl
private theorem ctT (B:ℕ) (hW:133425*B≤0x2027d3a8) (hJB:1710≤B) :
    288*((tuples B).card:ℤ) = ∑ f∈range 571,ajj B 1710 f := by
  rw [bWv,mul_sum]
  apply sum_congr rfl
  intro f hf
  rw [mem_range] at hf
  exact bYU B 1710 f hW hJB (by omega)
private def pair (B q:ℤ) :ℤ :=
  aoQ 0x2027d3a8 B 1710 (2*q) (856-3*q) +
    aoQ 0x2027d3a8 B 1710 (2*q+1) (854-3*q)
private def ajf (B n:ℤ) :ℤ :=
  let a :=pair B 0
  let b:=pair B 1
  let c:=pair B 2
  let d:=pair B 3
  let e :=pair B 4
  n*(120*a+(n - 1)*(60*(b-a)+(n - 2)*(20*(c - 2*b+a) +
    (n-3)*(5*(d-3*c+3*b-a)+(n-4)*(e-4*d+6*c-4*b+a)))))
private theorem ccx (B q:ℕ) (hq:q<285) :
    ajf B (q+1)=ajf B q+120*(ajj B 1710 (2*q)+ajj B 1710 (2*q+1)) := by
  have he : (((1710-3*(2*q))/2+1 :ℕ) :ℤ)=856-3*q:= by omega
  have ho: (((1710-3*(2*q+1))/2+1 :ℕ) :ℤ)=854-3*q:= by omega
  simp only [ajj,he,ho,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  change ajf B (q+1)=ajf B q+120*pair B q
  unfold ajf pair aoQ aae avU acQ
  ring
private theorem a1x (B:ℕ) (hW:133425*B≤0x2027d3a8) (hB:1710≤B) :
    34560*((tuples B).card:ℤ)=ajf B 285+120*ajj B 1710 570:= by
  have h:=ctT B hW hB
  have hs :=bKe (ajj B 1710) (ajf B) 285
    (by simp [ajf]) (ccx B) 285 (by decide)
  rw [show 571=2*285+1 by decide,sum_range_succ] at h
  rw [show (34560:ℤ)=120*288 by decide,mul_assoc,h,mul_add,hs]
  simp only [Nat.cast_ofNat,show (2 :ℕ)*285=570 by decide]
theorem base_volume :34560*((tuples 4025).card:ℤ)=0x2da4cf9294e7eae571d00 :=
  (a1x 4025 (by decide) (by decide)).trans rfl
end qa84RQb
end
section
set_option autoImplicit true
namespace qa84RQb
open Finset
open Rw (qB bKe amJ)
open private plateau plateau_spec from ProximityPrize.SubmissionLower.Zeg869c
open scoped BigOperators
private abbrev aSu:=Σ _:ℕ,Σ _:ℕ,Σ _:ℕ,ℕ
private def pieces (q j n:ℕ) :Finset aSu :=
  (range n).sigma fun r =>
    (range (r/2+1)).sigma fun f =>
      (range (r - 2*f+1)).sigma fun _=>range (width q (j+r))
private theorem mem_pieces (q j n r f c x :ℕ) :
    (⟨r,f,c,x⟩:aSu)∈pieces q j n↔r<n∧2*f+c≤ r∧x<width q (j+r) := by
  simp only [pieces,mem_sigma,mem_range]
  omega
private def aVI (q L:ℕ) :=pieces q (L+1) (1710 - L)
private def arL (B:ℕ) :Finset qB:=(range (B+1)).sigma fun q=>aVI q (plateau q)
private def extra :=pieces 4025 1703 8
private theorem c0a (B q r f c x :ℕ) :
    (⟨q,r,f,c,x⟩:qB)∈arL B ↔
      q≤B∧plateau q+r<1710∧2*f+c≤ r∧x<width q (plateau q+1+r) := by
  simp only [arL,aVI,mem_sigma,mem_range,mem_pieces]
  omega
private def bOY:qB→qB
  | ⟨f,c,b,a,x⟩ =>
    let q:=a+b+c+f
    ⟨q,b+2*c+3*f - plateau q - 1,f,c,x⟩
private def bJN :qB→qB
  | ⟨q,r,f,c,x⟩ =>
    let b:=plateau q+1+r - 2*c-3*f
    ⟨f,c,b,q-(b+c+f),x⟩
private def admissible :qB→Prop
  | ⟨q,r,f,c,_⟩=>2*c+3*f≤plateau q+1+r
set_option linter.constructorNameAsVariable false in
private theorem gBT (B:ℕ) (t:qB) (ht:t∈bad B) :
    bOY t∈arL B∧admissible (bOY t)∧bJN (bOY t)=t:= by
  rcases t with ⟨f,c,b,a,x⟩
  rw [bad,mem_filter,bfA] at ht
  obtain ⟨⟨_,hj,hq,hx⟩,hp⟩:=ht
  let q:=a+b+c+f
  let j:=b+2*c+3*f
  let r :=j - plateau q - 1
  change ¬ b+c+f≤plateau q at hp
  change j≤1710 at hj
  change x<width q j at hx
  have hr :plateau q+1+r=j:= by dsimp [r,j]; omega
  have hrc :2*f+c≤ r := by dsimp [j] at hr; omega
  refine ⟨(c0a B q r f c x).mpr ⟨hq,by omega,hrc,by rwa [hr]⟩,?_,?_⟩
  · change 2*c+3*f≤plateau q+1+r
    rw [hr]
    dsimp [j]
    omega
  · change (⟨f,c,_,_,x⟩:qB)=⟨f,c,b,a,x⟩
    have hb:plateau q+1+r - 2*c-3*f=b:= by rw [hr]; dsimp [j]; omega
    have ha :q-(b+c+f)=a := by dsimp [q]; omega
    rw [hb,ha]
private def extraToLoss :aSu→qB
  | ⟨s,k,f,x⟩=>⟨4025,852+s,f,852+s - k - 2*f,x⟩
private def extraOfLoss :qB→aSu
  | ⟨_,r,f,c,x⟩=>⟨r-852,r-(c+2*f),f,x⟩
private theorem extra_spec (B:ℕ) (hB:4025≤B) (t:aSu) (ht:t∈extra) :
    extraToLoss t∈arL B ∧ ¬ admissible (extraToLoss t)∧extraOfLoss (extraToLoss t)=t:= by
  rcases t with ⟨s,k,f,x⟩
  obtain ⟨hs,hk,hx⟩:=(mem_pieces 4025 1703 8 s k f x).mp ht
  let r :=852+s
  let c:=r - k - 2*f
  have hc:c+k+2*f=r := by dsimp [c,r]; omega
  have hL:plateau 4025=850:=rfl
  have hj:plateau 4025+1+r=1703+s := by rw [hL]; dsimp [r]; omega
  refine ⟨(c0a B 4025 r f c x).mpr ⟨hB,?_,by omega,by rwa [hj]⟩,?_,?_⟩
  · rw [hL]
    dsimp [r]
    omega
  · change ¬ 2*c+3*f≤plateau 4025+1+r
    rw [hj]
    dsimp [r] at hc
    omega
  · change (⟨r-852,r-(c+2*f),f,x⟩:aSu)=⟨s,k,f,x⟩
    rw [show r-852=s by dsimp [r]; omega,show r-(c+2*f)=k by omega]
private theorem card_le_with_disjoint_images {s t:Finset qB} {u:Finset aSu}
    (hs : ∀ x∈s,bOY x∈t∧admissible (bOY x)∧bJN (bOY x)=x)
    (hu : ∀ x∈u,extraToLoss x∈t ∧ ¬ admissible (extraToLoss x) ∧
      extraOfLoss (extraToLoss x)=x) :s.card+u.card≤t.card:= by
  have he :u.image extraToLoss⊆t:= by
    intro y hy
    obtain ⟨x,hx,rfl⟩:=mem_image.mp hy
    exact (hu x hx).1
  have hi: (u.image extraToLoss).card=u.card :=
    card_image_of_injOn fun x hx y hy h=> by
      simpa only [(hu x hx).2.2,(hu y hy).2.2] using congrArg extraOfLoss h
  have hb:s.card≤(t \ u.image extraToLoss).card:= by
    apply card_le_card_of_injOn bOY
    · intro x hx
      obtain ⟨hm,ha,_⟩:=hs x hx
      refine mem_sdiff.mpr ⟨hm,fun he => ?_⟩
      obtain ⟨y,hy,h⟩:=mem_image.mp he
      exact (hu y hy).2.1 (by rwa [h])
    · intro x hx y hy h
      simpa only [(hs x hx).2.2,(hs y hy).2.2] using congrArg bJN h
  rw [← hi,← card_sdiff_add_card_eq_card he]
  exact Nat.add_le_add_right hb _
private def count (r :ℕ) :ℕ := ∑ f∈range (r/2+1),(r - 2*f+1)
private theorem bYW (r :ℕ) :
    (count r :ℤ)=(((r/2 :ℕ) :ℤ)+1)*((r :ℤ)-(r/2 :ℕ)+1) := by
  rw [count,Nat.cast_sum]
  have h:=amJ 1 (fun f=>(r :ℤ) - 2*f+1)
    (fun n=>n*(r+2 - n)) (by ring) (by intro n; ring) (r/2+1)
  rw [one_mul,Nat.cast_add,Nat.cast_one] at h
  convert h using 1
  · apply sum_congr rfl
    intro f hf
    rw [mem_range] at hf
    omega
  · ring
private def crT (q j r :ℕ) :ℤ :=
  (((r/2 :ℕ) :ℤ)+1)*((r :ℤ)-(r/2 :ℕ)+1) *
    (0x2027d3a8+(j:ℤ)+r - 133425*q)
private theorem pieces_sum (q j n:ℕ) (hq:q≤4025) :
    ((pieces q j n).card:ℤ) = ∑ r∈range n,crT q j r := by
  simp only [pieces,card_sigma,card_range,Nat.cast_sum]
  apply sum_congr rfl
  intro r _
  have hw:133425*q≤0x2027d3a8+(j+r) := by omega
  have hc: (width q (j+r) :ℤ)=0x2027d3a8+(j:ℤ)+r - 133425*q:= by
    simp only [width,Nat.cast_sub hw,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    ring
  calc
    _=(count r :ℤ)*(width q (j+r) :ℤ) := by
      simp only [sum_const,nsmul_eq_mul,card_range,← sum_mul,count,Nat.cast_sum]
    _ = _:= by rw [bYW,hc,crT]
private def aWk (C n:ℤ) :ℤ :=
  n*(120*(3*C+2)+(n-1) *
    (60*(7*C+24)+(n-2)*(20*(4*C+46)+(n-3)*120)))
private theorem pieces_closed (q j n:ℕ) (hq:q≤4025) :
    120*((pieces q j (2*n)).card:ℤ)=aWk (0x2027d3a8+j - 133425*q) n:= by
  rw [pieces_sum q j _ hq]
  apply bKe (N :=n) _ _ (by simp [aWk]) _ n le_rfl
  intro k _
  have he : (2*k)/2=k := by omega
  have ho: (2*k+1)/2=k := by omega
  simp only [crT,he,ho,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  unfold aWk
  ring
private def bqE (lo L n len:ℤ) :ℤ :=
  let C:=0x2027d3a8+L+1 - 133425*lo
  len*(2*aWk C n+(len - 1) *
    (aWk (C - 133425) n-aWk C n))
private theorem bVH (lo L n len:ℕ) (hhi:lo+len≤4026)
    (hn:1710 - L=2*n) (hcap : ∀ k<len,plateau (lo+k)=L) :
    240*(∑ k∈range len,((aVI (lo+k) (plateau (lo+k))).card:ℤ)) =
      bqE lo L n len:= by
  let g:= fun k :ℤ=>aWk (0x2027d3a8+L+1 - 133425*((lo:ℤ)+k)) n
  have h:=amJ 2 g (bqE lo L n)
    (by simp [bqE]) (by intro t; unfold bqE g aWk; ring) len
  rw [mul_sum] at h ⊢
  convert h using 1
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  rw [hcap k hk,aVI,hn,show (240:ℤ)=2*120 by decide,mul_assoc,
    pieces_closed (lo+k) (L+1) n (by omega),Nat.cast_add,Nat.cast_add,Nat.cast_one]
  simp only [g,add_assoc]
private def aOA (n:ℕ) :ℤ :=
  ∑ q∈range n,((aVI q (plateau q)).card:ℤ)
private theorem advance {lo hi L n:ℕ} {old added:ℤ}
    (hle :lo≤hi) (hhi:hi≤4026) (ha :plateau lo=L) (hb:plateau (hi - 1)=L)
    (hn:1710 - L=2*n) (hv :bqE lo L n (hi-lo:ℕ)=added)
    (hprev :240*aOA lo=old) :240*aOA hi=old+added:= by
  have h:=bVH lo L n (hi-lo) (by omega) hn fun k hk=> by
    apply le_antisymm
    · simpa only [ha] using plateau_spec.1 (show lo≤lo+k by omega)
    · simpa only [hb] using plateau_spec.1 (show lo+k≤hi - 1 by omega)
  rw [hv] at h
  conv_lhs=>rw [aOA,show hi=lo+(hi-lo) by omega,sum_range_add]
  rw [mul_add,← aOA,hprev,h]
private theorem start:240*aOA 3307=0:= by
  have hzero :aOA 3307=0:= by
    apply sum_eq_zero
    intro q hq
    rw [mem_range] at hq
    simp [plateau,hq,aVI,pieces]
  rw [hzero,mul_zero]
local notation "auk" a "," b "," l "," i "," v =>
  advance (lo:=a) (hi:=b) (L:=l) (n:=i) (added:=v)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl
private theorem losses_count (B:ℕ) : ((arL B).card:ℤ)=aOA (B+1) := by
  simp only [arL,card_sigma,Nat.cast_sum,aOA]
private theorem loss_total:240*aOA 4026=0x1393169bb9551eb60 :=
  start
    |> (auk 3307,3335,1700,5,0x49ae7e870f20)
    |> (auk 3335, 3407,1650,30,0x6ac7ff07449c40)
    |> (auk 3407,3470,1600,55,0x1f51b7d4b2968c0)
    |> (auk 3470,3537,1550,80,0x5a5a1e7314e2e00)
    |> (auk 3537,3585,1500,105,0x81eac341f57e380)
    |> (auk 3585, 3630,1450,130,0xd00a7feb3794480)
    |> (auk 3630,3678,1400,155,0x14f1ee988417a900)
    |> (auk 3678,3733,1350,180,0x208e2b795368b7c0)
    |> (auk 3733, 3781,1300,205,0x2387375d88579c80)
    |> (auk 3781,3830,1250,230,0x2a82914610fa5020)
    |> (auk 3830,3878,1200,255,0x2d28d72b12d4c000)
    |> (auk 3878,3927,1150,280,0x2d676afe4488bfc0)
    |> (auk 3927,3975,1100,305,0x25bc3f6bc274bb80)
    |> (auk 3975,4020,1050,330,0x165a62c621d36b60)
    |> (auk 4020,4025,1000,355,0x16c554c5ac68d60)
    |> (auk 4025,4026,850,430,0x6f2a19b8feffe0)
private theorem extra_total:120*(extra.card:ℤ)=0x4c93403a0 :=
  (pieces_closed 4025 1703 4 (by decide)).trans rfl
private theorem loss_arith {b e t:ℕ} (h:b+e≤t) (he :120*(e :ℤ)=0x4c93403a0)
    (ht:240*(t:ℤ)=0x1393169bb9551eb60) :
    b≤0x14e1292e0031b9e := by omega
theorem loss_upper : (bad 4025).card≤0x14e1292e0031b9e :=
  loss_arith
    (card_le_with_disjoint_images (gBT 4025) (extra_spec 4025 le_rfl))
    extra_total ((congrArg (fun n=>240*n) (losses_count 4025)).trans loss_total)
end qa84RQb
end
section
set_option autoImplicit true
namespace qa84RQb
private theorem finish {s b t:ℕ} (h:s+b=t) (hb:b≤0x14e1292e0031b9e)
    (ht:34560*(t:ℤ)=0x2da4cf9294e7eae571d00) :
    0x5678fbe532882ec9d≤ s := by omega
theorem proof :P6_6_2.c1 :=finish bWu loss_upper base_volume
end qa84RQb
end
