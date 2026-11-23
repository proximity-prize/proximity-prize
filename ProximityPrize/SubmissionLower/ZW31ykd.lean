import ProximityPrize.SubmissionLower.ZCUPQZb
import ProximityPrize.SubmissionLower.Z1iXjHc
set_option Elab.async false
open _root_ renaming DFunLike.congr_fun→lJ,Finset.sum_eq_zero→lI,Function.Injective→mD,Int.toNat_of_nonneg→lV,P5_8_2.offset→c9,ite_eq_left→nq,ite_eq_right→lz,max_eq_left→nI,qxVnKgd.region→aU,qxVnKgd.score→cy
section
set_option autoImplicit true
namespace qHvCGFa
open i4 P5_8_2 Finset MvPolynomial
noncomputable section
local notation "V" => (MvPolynomial.X (R:=F) :Fin 3→lK)
private theorem monomial_ex (a b c:ℕ) (z :F) :
  monomial (ex a b c) z=C z*(V 0^a*V 1^b*V 2^c) := by
 rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype _ _ (fun _=>pow_zero _),Fin.prod_univ_three]
 simp only [ex_zero,ex_one,ex_two,mul_assoc]
private theorem target_expansion (a b c:ℕ) (z :F) :
    target (monomial (ex a b c) z) =
      ∑ h∈range (a+1),∑ j∈range (a-h+1),
        monomial (ex (b+j) (c+(a-h-j)) h)
          (z*((-1 :F)^(a-h-j)*(a.choose h:F)*((a-h).choose j:F))) := by
  classical
  rw [monomial_ex]
  simp only [target,map_mul,map_pow,aeval_C,algebraMap_eq,aeval_X]
  change C z*((V 2+V 0-V 1)^a*V 0^b*V 1^c)= _
  have hsum: (V 2+V 0-V 1 :lK)=V 2+(V 0 + -V 1) := by ring
  rw [hsum,add_pow (V 2 :lK) (V 0 + -V 1)]
  simp only [mul_sum,sum_mul]
  refine sum_congr rfl fun h _ => ?_
  rw [add_pow (V 0:lK) (-V 1)]
  simp only [mul_sum,sum_mul]
  refine sum_congr rfl fun j _ => ?_
  rw [monomial_ex,neg_pow]
  simp only [map_mul,map_pow,map_neg,map_one,map_natCast]
  ring
theorem target_entry (row col:Jet) (z :F) :
    (target (monomial (Ac col) z)).coeff (rowExp row)=z*alu row col:= by
  classical
  let P:Prop :=col.b≤ row.b∧col.c≤ row.c ∧
    row.a+(row.b-col.b)+(row.c-col.c)=col.a
  have hexp (h j:ℕ) (hh:h≤ col.a) (hj:j≤ col.a-h) :
      ex (col.b+j) (col.c+(col.a-h-j)) h=rowExp row ↔
        P∧h=row.a∧j=row.b-col.b:= by
    have hcoords :ex (col.b+j) (col.c+(col.a-h-j)) h=rowExp row ↔
        col.b+j=row.b∧col.c+(col.a-h-j)=row.c∧h=row.a := by
      constructor
      · intro he
        exact ⟨lJ he 0,lJ he 1,lJ he 2⟩
      · rintro ⟨h₀,h₁,h₂⟩
        rw [h₀,h₁,h₂,rowExp]
    rw [hcoords]
    dsimp only [P]
    omega
  rw [Ac,target_expansion]
  simp_rw [coeff_sum,coeff_monomial]
  by_cases hp:P
  · obtain ⟨hb,hc,ha⟩:=hp
    have hh:row.a≤ col.a := by omega
    have hj:row.b-col.b≤ col.a-row.a := by omega
    rw [sum_eq_single_of_mem row.a (mem_range.mpr (by omega))]
    · rw [sum_eq_single_of_mem (row.b-col.b) (mem_range.mpr (by omega))]
      · rw [nq  ((hexp _ _ hh hj).2 ⟨⟨hb,hc,ha⟩,rfl,rfl⟩),alu,
          nq  ⟨hb,hc,ha⟩,show col.a-row.a-(row.b-col.b)=row.c-col.c by omega]
      · intro j hmem hne
        exact lz  (fun he=>hne ((hexp _ _ hh (Nat.lt_succ_iff.mp (mem_range.mp hmem))).1 he).2.2)
    · intro h hmem hne
      apply lI
      intro j hjmem
      exact lz (fun he=>hne ((hexp _ _ (Nat.lt_succ_iff.mp (mem_range.mp hmem))
        (Nat.lt_succ_iff.mp (mem_range.mp hjmem))).1 he).2.1)
  · rw [alu,lz hp,mul_zero]
    apply lI
    intro h hh
    apply lI
    intro j hj
    exact lz (fun he=>hp ((hexp _ _ (Nat.lt_succ_iff.mp (mem_range.mp hh))
      (Nat.lt_succ_iff.mp (mem_range.mp hj))).1 he).1)
end
end qHvCGFa
end
section
set_option autoImplicit true
namespace qHvCGFa
open i4 P5_8_2 Finset MvPolynomial
noncomputable section
local instance :Fact (Nat.Prime i4.p) :=⟨KoalaBear.is_prime⟩
private abbrev EL (s :Source) (q u:ℕ) := ↥(aTf s q (c9 u))
private abbrev dG (s :Source) (q u:ℕ) := ↥(aCq s.m q (c9 u))
private abbrev Forms (q u:ℕ) := ↥(planeSpace (deg q) (initialFlags q u))
private def vector (s :Source) (q u:ℕ) :Forms q u →ₗ[F] (EL s q u→F) :=
 LinearMap.pi fun j=>(lcoeff F (Ac j.val)).comp
  ((source q).comp (planeSpace (deg q) (initialFlags q u)).subtype)
variable {s :Source} {B J C q u:ℕ} (hE :s.E=aH1 B J C)
 (hB:J≤B) (hJC:2*C≤J) (hJ:1959≤J) (hC:979≤C) (hq:q≤B)
include hE hB hJC hJ hC hq in
private theorem Uj (f :Forms q u) :
   source q f.val = ∑ j:EL s q u,monomial (Ac j.val) (vector s q u f j) := by
 classical
 let p:=source q f.val
 apply MvPolynomial.ext
 intro e
 change p.coeff e=(∑ j:EL s q u,monomial (Ac j.val) (p.coeff (Ac j.val))).coeff e
 simp_rw [coeff_sum,coeff_monomial]
 by_cases he :e∈p.support
 · let j:EL s q u:=⟨bYa e,apx s hE hB hJC hJ hC hq f he⟩
   have hj:Ac j.val=e :=ex_eta e
   rw [sum_eq_single j]
   · simp [hj]
   · intro k _ hkj
     exact lz (fun hk=>hkj (Subtype.ext (colExp_injective (hk.trans hj.symm))))
   · simp
 · have hz :=MvPolynomial.notMem_support_iff.mp he
   rw [hz]
   symm
   apply lI
   intro j _
   split
   · rename_i hj
     rwa [hj]
   · rfl
include hE hB hJC hJ hC hq in
private theorem vector_injective :
  mD (vector s q u) := by
 intro f g h
 apply Subtype.ext
 apply source_injective q
 rw [Uj hE hB hJC hJ hC hq f,Uj hE hB hJC hJ hC hq g,h]
private theorem bvo (r :dG s q u) :
  c9 u+(q:ℤ)+((rowExp r.val) 1 :ℤ)+2*((rowExp r.val) 2 :ℕ)<(s.m:ℤ) := by
 obtain ⟨hm,_,hr⟩:=mem_filter.mp r.property
 have hq:r.val.q=q:= by
  rcases r with ⟨⟨c,b,a⟩,_⟩
  simp only [mem_sigma,mem_range,mem_singleton] at hm
  simp only [Jet.q,Jet.a,Jet.b,Jet.c]
  omega
 change c9 u+(r.val.v :ℤ)+3*(r.val.a :ℤ)<(s.m:ℤ) at hr
 simp only [rowExp,ex_one,ex_two]
 simp only [Jet.q] at hq
 simp only [Jet.v,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hr
 omega
include hE hB hJC hJ hC hq in
private theorem in_kernel (hm:s.m=4600) (f :Forms q u) :
   vector s q u f∈(GU s q (c9 u)).mulVecLin.ker := by
 classical
 apply LinearMap.mem_ker.mpr
 funext r
 have hz : (target (source q f.val)).coeff (rowExp r.val)=0 :=
   MvPolynomial.notMem_support_iff.mp (fun hs=> by
     have ho:=target_order f hs
     have hr :=bvo r
     omega)
 rw [Uj hE hB hJC hJ hC hq f,map_sum] at hz
 simp_rw [coeff_sum,target_entry] at hz
 change (∑ j:EL s q u,alu r.val j.val*vector s q u f j)=0
 simpa only [mul_comm (alu r.val _)] using hz
include hE hB hJC hJ hC hq in
private theorem bound (hm:s.m=4600) :
   (GU s q (c9 u)).rank+Module.finrank F (Forms q u) ≤
     (aTf s q (c9 u)).card:= by
 classical
 let M:=GU s q (c9 u)
 let inject :=(vector s q u).codRestrict M.mulVecLin.ker (in_kernel hE hB hJC hJ hC hq hm)
 have hi:mD inject :=
   fun _ _ h=>vector_injective hE hB hJC hJ hC hq (congrArg Subtype.val h)
 have hle :=LinearMap.finrank_le_finrank_of_injective hi
 have hdim:=M.mulVecLin.finrank_range_add_finrank_ker
 rw [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] at hdim
 exact (Nat.add_le_add_left hle M.rank).trans_eq hdim
theorem proof :P5_8_2.c1 := by
 intro q hq u _
 exact bound (s :=P5_8.bo8) (B:=6251) (J:=1959) (C:=979) (q:=q) (u:=u)
  rfl (by decide) (by decide) le_rfl le_rfl (Nat.lt_succ_iff.mp hq) rfl
end
end qHvCGFa
end
section
set_option autoImplicit true
namespace qxVnKgd
open P5_8_2 Finset
set_option maxRecDepth 1024
abbrev Block :=Σ _:ℕ,ℕ
private def qO (i:Fin 7) (x :Cell) :ℤ×ℤ :=
 let p:=x.1
 let o:=x.2
 match i.val with
 | 0=>(p,o)
 | 1=>(p,2*p-o)
 | 2 | 5=>(4600+o-p,p)
 | 3 | 4=>(4600+p-o,o)
 | _=>(4600+2*o-p,p-o)
private def tag (q o:ℤ) :ℕ :=
 let p:=q+o-4600
 if q<1959 then (if o≤q then 0 else 1)
 else if p≤0 then 2
 else if 2*p+o≤3919 then (if p+2*o≤3919 then 3 else 5)
 else (if p+2*o≤3919 then 4 else 6)
private def inverse (i:Fin 7) (q o:ℤ) :Cell :=
 let p:=q+o-4600
 match i.val with
 | 0=>⟨q,o⟩
 | 1=>⟨q,2*q-o⟩
 | 2 | 5=>⟨o,p⟩
 | 3 | 4=>⟨p,o⟩
 | _=>⟨p+o,p⟩
private theorem DN (i:Fin 7) (x :Cell) (hx :x∈aU i) :
  let q:=(qO i x).1
  let o:=(qO i x).2
  0≤q∧q≤6251∧1≤o∧o≤6559-q ∧
    tag q o=i.val∧inverse i q o=x := by
 obtain ⟨p,o⟩:=x
 fin_cases i <;>
  simp only [aU,mem_sigma,mem_Icc] at hx <;>
  simp [qO,tag,inverse,Sigma.mk.injEq] <;>
  (obtain ⟨⟨_,_⟩,_,_⟩:=hx
   repeat' first | split | constructor
   all_goals omega)
private def blockOf (q o:ℤ) :Block :=⟨q.toNat,(6559-q-o).toNat⟩
private theorem blockOf_coords {q o:ℤ} (hq:0≤q) (hu:o≤6559-q) :
  ((blockOf q o).1 :ℤ)=q∧P (blockOf q o).2=q+o-4600 ∧
    O (blockOf q o).1 (blockOf q o).2=o:= by
 simp only [blockOf,P,O,lV hq,
  lV (by omega :0≤6559-q-o),true_and]
 constructor <;> omega
private def value (b:Block) :ℤ:=m5 b.1 b.2 (pick b.1 b.2)
private theorem lowAt {q o:ℤ} (hq:0≤q) (hq' : q<1959)
  (ho:o≤6559-q) (hp:q+o≤4600) (he :max 0 (o-q)≤q) :
  let e :=max 0 (o-q)
  low q (q-e) (o-2*e)≤value (blockOf q o) := by
 obtain ⟨hq₁,hp₁,ho₁⟩:=blockOf_coords hq ho
 have hsmall: (blockOf q o).1<1959:= by omega
 have hh: ((o-q).toNat :ℤ)=max 0 (o-q) := by omega
 have h:=low_le (u:=(blockOf q o).2) (e :=((o-q).toNat :ℤ))
  hsmall (by omega) (by omega) (by omega)
 simp only [Int.toNat_natCast] at h
 rw [hq₁,ho₁,hh] at h
 simpa only [value,pick,nq hsmall,ho₁,hq₁] using h
private theorem highAt {p o:ℤ} (hq:1959≤4600+p-o) (hp:p≤1959)
  (hn:A p o+A o p≤979) :
  high p o (A p o) (A o p)≤value (blockOf (4600+p-o) o) := by
 obtain ⟨hq₁,hp₁,ho₁⟩:=blockOf_coords (by omega :0≤4600+p-o)
  (by omega :o≤6559-(4600+p-o))
 have hp₂:P (blockOf (4600+p-o) o).2=p:= by omega
 have hlarge :1959≤(blockOf (4600+p-o) o).1 := by omega
 have h:=high_le (u:=(blockOf (4600+p-o) o).2) hlarge
  (le_max_left _ _:0≤A p o) (le_max_left _ _:0≤A o p) hn
 rw [hp₂,ho₁] at h
 simpa only [value,pick,lz (not_lt_of_ge hlarge),ho₁,hp₂,A] using h
private theorem score_le (i:Fin 7) (x :Cell) (hx :x∈aU i) :
   cy i x≤value (blockOf (qO i x).1 (qO i x).2) := by
 obtain ⟨p,o⟩:=x
 fin_cases i <;> simp only [aU,mem_sigma,mem_Icc] at hx <;>
   (obtain ⟨⟨hp₁,hp₂⟩,ho₁,ho₂⟩:=hx) <;> dsimp [cy ,qO]
 · have h:=lowAt (q:=p) (o:=o) (by omega) (by omega) (by omega) (by omega) (by omega)
   simpa only [nI  (by omega :o-p≤0),sub_zero,mul_zero] using h
 · have h:=lowAt (q:=p) (o:=2*p-o) (by omega) (by omega) (by omega) (by omega) (by omega)
   rw [max_eq_right (by omega :0≤2*p-o-p)] at h
   dsimp only at h
   rwa [show p-(2*p-o-p)=o by ring,show 2*p-o-2*(2*p-o-p)=o by ring] at h
 · have h₁:A o p=0:=max_eq_left (by omega)
   have h₂:A p o=0:=nI  (by omega)
   have h:=highAt (p:=o) (o:=p) (by omega) (by omega) (by omega)
   simpa [h₁,h₂,high,H_nonpos ho₂] using h
 · have h₁:A p o=0:=max_eq_left (by omega)
   have h₂:A o p=0:=nI  (by omega)
   have h:=highAt (p:=p) (o:=o) (by omega) (by omega) (by omega)
   simpa only [h₁,h₂] using h
 · have h₁:A p o=2*p+o-3919:=max_eq_right (by omega)
   have h₂:A o p=0:=nI  (by omega)
   have h:=highAt (p:=p) (o:=o) (by omega) (by omega) (by omega)
   simpa only [h₁,h₂] using h
 · have h₁:A p o=2*p+o-3919:=max_eq_right (by omega)
   have h₂:A o p=0:=nI  (by omega)
   have h:=highAt (p:=o) (o:=p) (by omega) (by omega) (by omega)
   change high p o (2*p+o-3919) 0≤value (blockOf (4600+o-p) p)
   rwa [high_swap o p,h₁,h₂] at h
 · have h₁:A o (p-o)=2*o+(p-o)-3919:=max_eq_right (by omega)
   have h₂:A (p-o) o=2*(p-o)+o-3919:=max_eq_right (by omega)
   have h:=highAt (p:=o) (o:=p-o) (by omega) (by omega) (by omega)
   rw [h₁,h₂,high_both hp₂,show 4600+o-(p-o)=4600+2*o-p by ring] at h
   exact h
private def embed (i:Fin 7) (x :Cell) :Block :=
 blockOf (qO i x).1 (qO i x).2
private theorem embed_inj (i j:Fin 7) (x y :Cell) (hi:x∈aU i) (hj:y∈aU j)
  (h:embed i x=embed j y) : (⟨i,x⟩:Σ _:Fin 7,Cell)=⟨j,y⟩:= by
 obtain ⟨hi₁,_,_,hi₄,hi₅,hi₆⟩:=DN i x hi
 obtain ⟨hj₁,_,_,hj₄,hj₅,hj₆⟩:=DN j y hj
 have hx :=blockOf_coords hi₁ hi₄
 have hy :=blockOf_coords hj₁ hj₄
 change blockOf (qO i x).1 (qO i x).2=blockOf (qO j y).1 (qO j y).2 at h
 have hq:=hx.1.symm.trans ((congrArg (fun b:Block=>(b.1 :ℤ)) h).trans hy.1)
 have ho:=hx.2.2.symm.trans ((congrArg (fun b:Block=>O b.1 b.2) h).trans hy.2.2)
 rw [hq,ho,hj₅] at hi₅
 have hij:i=j:=Fin.ext hi₅.symm
 subst j
 rw [hq,ho,hj₆] at hi₆
 subst y
 rfl
private theorem join {ι α β:Type} [DecidableEq β] (s :Finset ι)
   (Ax :ι→Finset α) (t:Finset β) (e :ι→α→β) (f :ι→α→ℤ) (g:β→ℤ)
   (hi : ∀ i j x y,x∈Ax i→y∈Ax j→e i x=e j y →
     (⟨i,x⟩:Σ _:ι,α)=⟨j,y⟩)
   (hm : ∀ i x,x∈Ax i→e i x∈t)
   (hf : ∀ i x,x∈Ax i→f i x≤g (e i x)) (hg : ∀ b,0≤g b) :
   (∑ i∈s,∑ x∈Ax i,f i x) ≤ ∑ b∈t,g b:= by
 rw [sum_sigma']
 let loc: (Σ _:ι,α)→β:= fun x=>e x.1 x.2
 apply sum_le_sum_of_injOn (g:=g) loc
 · rintro ⟨i,x⟩ hx ⟨j,y⟩ hy h
   exact hi i j x y (mem_sigma.mp hx).2 (mem_sigma.mp hy).2 h
 · intro b hb
   obtain ⟨⟨i,x⟩,hx,rfl⟩:=mem_image.mp hb
   exact hm i x (mem_sigma.mp hx).2
 · rintro ⟨i,x⟩ hx
   exact hf i x (mem_sigma.mp hx).2
 · intro b _ _
   exact hg b
private theorem embed_bounds (i:Fin 7) (x :Cell) (hx :x∈aU i) :
  (embed i x).1<6252∧(embed i x).2<6559-(embed i x).1 := by
 simp only [embed,blockOf]
 obtain ⟨hq₁,hq₂,ho₁,ho₂,_,_⟩:=DN i x hx
 constructor <;> omega
private theorem region_le_of_bounds (Q U:ℕ)
    (hm : ∀ i x,x∈aU i→(embed i x).1<Q∧(embed i x).2<U-(embed i x).1) :
    (∑ i:Fin 7,∑ x∈aU i,cy i x) ≤
        (↑(∑ q∈range Q,∑ u∈range (U-q),m5 q u (pick q u)) :ℤ) := by
  let t:Finset Block :=(range Q).sigma (fun q=>range (U-q))
  have hmem (i) (x) (hx :x∈aU i) :embed i x∈t:= by
    simpa only [t,mem_sigma,mem_range] using hm i x hx
  have hb:=join (ι:=Fin 7) (α:=Cell) (β:=Block)
    univ aU t embed cy value embed_inj hmem score_le
    (fun _=>Int.natCast_nonneg _)
  simpa only [t,sum_sigma,value,Nat.cast_sum] using hb
theorem region_le :
    (∑ i:Fin 7,∑ x∈aU i,cy i x) ≤
        (↑(∑ q∈range 6252,∑ u∈range (6559-q),m5 q u (pick q u)) :ℤ) :=
  region_le_of_bounds 6252 6559 embed_bounds
end qxVnKgd
end
section
set_option autoImplicit true
namespace qxVnKgd
open Finset P5_8_2
def c1 :Prop :=0xe8816aca9c ≤ ∑ x∈aU 0,cy 0 x
def c2 :Prop :=0x11eecc1e06 ≤ ∑ x∈aU 1,cy 1 x
def c3:Prop :=0x147a546f66d ≤ ∑ x∈aU 3,cy 3 x
def c4 :Prop :=0x532827c33 ≤ ∑ x∈aU 4,cy 4 x
def c5:Prop :=0x54dcf32e1 ≤ ∑ x∈aU 5,cy 5 x
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) :P5_8_2.c4 := by
 refine ⟨pick,?_⟩
 have h:=region_le
 simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at h
 change (∑ x∈aU 0,cy 0 x)+((∑ x∈aU 1,cy 1 x) +
   ((∑ x∈aU 2,cy 2 x)+((∑ x∈aU 3,cy 3 x) +
     ((∑ x∈aU 4,cy 4 x)+((∑ x∈aU 5,cy 5 x) + ∑ x∈aU 6,cy 6 x)))))≤_ at h
 rw [total_left,total_both] at h
 simp only [c1,c2,c3,c4,c5] at h1 h2 h3 h4 h5
 exact Int.ofNat_le.mp (show (0x47a97605ca1 :ℤ)≤_ by omega)
end qxVnKgd
end
