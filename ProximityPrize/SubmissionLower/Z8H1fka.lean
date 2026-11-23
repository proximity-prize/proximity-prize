import ProximityPrize.SubmissionLower.ZENrqsd
set_option Elab.async false
open _root_ renaming Finset.mem_filter→n5,Finset.sum_congr→lJ,Finset.sum_eq_zero→ oq,Finset.sum_fin_eq_sum_range→ oz,Fintype.card_sigma→ oy,MvPolynomial.X→lI,MvPolynomial.monomial→cy,Nat.add_sub_of_le→ oK,Nat.cast_add→nI,Nat.cast_mul→nq,Nat.cast_ofNat→ oj,Or.inr→lz,P5_8_1.contactChange→c9,ite_eq_left→ oY,ite_eq_right→nX,ju.total→aU,min_eq_left→lV,min_eq_right→mD,min_le_left→ ov,not_false_eq_true→ ox,not_true_eq_false→ oD
section
set_option autoImplicit true
namespace P5_8_1
open scoped BigOperators
open i4 (Jet aCq aTf GU)
open ju (abt)
local instance :Fact (Nat.Prime i4.p) :=⟨KoalaBear.is_prime⟩
private abbrev xN (q u:ℕ) :=
 {r :aCq 61 q ((u:ℤ)-25) // 0≤(u:ℤ)-25+(r.val.v :ℤ)}
private theorem active_of_nonzero (q u:ℕ) (r :aCq 61 q ((u:ℤ)-25))
   (s :aTf source q ((u:ℤ)-25))
   (hn:GU source q ((u:ℤ)-25) r s≠0) :
   0≤(u:ℤ)-25+(r.val.v :ℤ) := by
 have hs :=(Finset.mem_filter.mp s.property).2.2
 change i4.alu r.val s.val≠0 at hn
 unfold i4.alu at hn
 split at hn
 · rename_i h
   have hb:=h.1
   have hc:=h.2.1
   simp only [Jet.v,nI,nq,oj] at *
   omega
 · exact (hn rfl).elim
private theorem bLI (q u c d h:ℕ)
  (hr : (⟨c,d,h⟩:Jet)∈aCq 61 q ((u:ℤ)-25))
  (ha :0≤(u:ℤ)-25+(Jet.v ⟨c,d,h⟩:ℤ)) :
  h<q+1∧aAa q u h≤d∧d<bvg q u h∧q-(h+d)=c:= by
 simp only [aCq,n5 ,Finset.mem_sigma,Finset.mem_range,
  Finset.mem_singleton,Jet.v,Jet.b,Jet.c,Jet.a,nI,nq,
  oj] at hr ha
 unfold aAa bvg
 omega
private theorem cGN (q u c b a :ℕ)
  (hs : (⟨c,b,a⟩:Jet)∈aTf source q ((u:ℤ)-25)) :
  b< min q 25+1∧ayp u b≤ c∧c<bnz q b∧q-(b+c)=a := by
 change (⟨c,b,a⟩:Jet)∈((i4.aH1 83 25 11).filter _).filter _ at hs
 rw [n5 ,n5 ,i4.b8U (by decide) (by decide)] at hs
 simp only [Jet.q,Jet.v,Jet.a,Jet.b,Jet.c,nI,nq,
  oj] at hs
 unfold ayp bnz
 omega
private def aJo (q u:ℕ) :
   xN q u→af q u
 | ⟨⟨⟨c,d,h⟩,hr⟩,ha⟩ =>
   let H :=bLI q u c d h hr ha
   ⟨⟨h,H.1⟩,⟨d-aAa q u h,by
     change d-aAa q u h<bvg q u h-aAa q u h
     obtain ⟨_,hlo,hhi,_⟩:=H
     omega⟩⟩
private def bX9 (q u:ℕ) :
   ↥(aTf source q ((u:ℤ)-25))→qB q u
 | ⟨⟨c,b,a⟩,hs⟩ =>
   let H :=cGN q u c b a hs
   ⟨⟨b,H.1⟩,⟨c-ayp u b,by
     change c-ayp u b<bnz q b-ayp u b
     obtain ⟨_,hlo,hhi,_⟩:=H
     omega⟩⟩
private theorem fY7 (q u:ℕ) (r :xN q u) :
  rowJet q u (aJo q u r)=r.val.val := by
 rcases r with ⟨⟨⟨c,d,h⟩,hr⟩,ha⟩
 obtain ⟨_,hlo,_,hc⟩:=bLI q u c d h hr ha
 change (⟨q-(h+(aAa q u h+(d-aAa q u h))),aAa q u h+(d-aAa q u h),h⟩:Jet)= _
 rw [oK hlo,hc]
private theorem dNi (q u:ℕ) (s : ↥(aTf source q ((u:ℤ)-25))) :
  bYa q u (bX9 q u s)=s.val := by
 rcases s with ⟨⟨c,b,a⟩,hs⟩
 obtain ⟨_,hlo,_,ha⟩:=cGN q u c b a hs
 change (⟨ayp u b+(c-ayp u b),b,q-(b+(ayp u b+(c-ayp u b)))⟩:Jet)= _
 rw [oK hlo,ha]
theorem cDg (q u:ℕ) :
   (GU source q ((u:ℤ)-25)).rank≤(Bs q u).rank := by
 let M:=GU source q ((u:ℤ)-25)
 have hs : (M.submatrix (Subtype.val :xN q u→_) id).rank=M.rank := by
   apply Matrix.rank_submatrix_eq_of_ne_zero_mem_range
   intro r s hn
   exact ⟨⟨r,active_of_nonzero q u r s hn⟩,rfl⟩
 have he :M.submatrix (Subtype.val :xN q u→_) id =
     (Bs q u).submatrix (aJo q u) (bX9 q u) := by
   ext r s
   exact congrArg₂ i4.alu (fY7 q u r).symm (dNi q u s).symm
 change M.rank≤_
 rw [← hs,he]
 exact Matrix.rank_submatrix_le _ _ _
theorem cEk (q u:ℕ) :Fintype.card (af q u)=rows q u:= by
 simp only [af,oy ,Fintype.card_fin,rows,abt,
  oz]
 exact lJ rfl fun i hi=> by simp [Finset.mem_range.mp hi]
theorem cEe (q u:ℕ) :Fintype.card (qB q u)=cols q u:= by
 simp only [qB,oy ,Fintype.card_fin,cols,abt,
  oz]
 exact lJ rfl fun i hi=> by simp [Finset.mem_range.mp hi]
theorem fTg (q u:ℕ) : (Bs q u).rank≤b9S q u:= by
 exact le_min ((Bs q u).rank_le_card_height.trans_eq (cEk q u))
  ((Bs q u).rank_le_card_width.trans_eq (cEe q u))
end P5_8_1
end
section
set_option autoImplicit true
namespace P5_8_1
open ju (total)
private def tri (n:ℕ) :=n*(n-1)/2
private theorem tri_succ (n:ℕ) :tri (n+1)=n+tri n:= by
 simp only [tri,← Nat.choose_two_right,Nat.choose_succ_succ' n 1,Nat.choose_one_right]
private def down (s a n:ℕ) :=
 let d:=min n ((a+s-1)/s)
 d*a - s*tri d
private theorem down_eq (s a n:ℕ) (hs :s=1∨s=2∨s=3) :
    aU (fun h=>a-s*h) n=down s a n:= by
  let t:=(a+s-1)/s
  have hp (i:ℕ) (hi:i<t) :s*i≤a := by
    dsimp [t] at hi
    rcases hs with rfl|rfl|rfl <;> omega
  have hz (i:ℕ) (hi:t≤ i) :a≤ s*i:= by
    dsimp [t] at hi
    rcases hs with rfl|rfl|rfl <;> omega
  have h (n:ℕ) :aU (fun h=>a-s*h) n+s*tri (min n t)=min n t*a := by
    induction n with
    | zero=>simp [total,tri]
    | succ n ih =>
      by_cases hn:n<t
      · have hmul :=hp n hn
        simp only [lV hn.le] at ih
        rw [min_eq_left (by omega :n+1≤t),total,tri_succ,Nat.mul_add,
          Nat.add_mul,one_mul]
        omega
      · simp only [min_eq_right (by omega :t≤n)] at ih
        rw [min_eq_right (by omega :t≤n+1),total,Nat.sub_eq_zero_of_le (hz n (by omega)),
          add_zero]
        exact ih
  change _=min n t*a - s*tri (min n t)
  have hn:=h n
  omega
private theorem bh5 (f g:ℕ→ℕ) (n:ℕ) :
   aU (fun i=>f i+g i) n=aU f n+total g n:= by
 induction n with
 | zero=>rfl
 | succ n ih=>simp only [total,ih]; omega
private theorem total_prefix (f :ℕ→ℕ) (n r :ℕ) :
    aU (fun i=>if i< r then f i else 0) n=aU f (min n r) := by
  induction n with
  | zero=>rfl
  | succ n ih =>
    by_cases h:n< r
    · simp only [aU,ih,oY h,lV h.le,lV (by omega :n+1≤ r)]
    · simp only [total,ih,ite_eq_right h,add_zero,min_eq_right (by omega :r≤n),
        mD  (by omega :r≤n+1)]
private theorem vo (f :ℕ→ℕ) (n l r :ℕ) (hl:l≤n) (hr :r≤n) :
    aU (fun i=>if l≤ i∧i< r then f i else 0) n=aU f r - aU f l:= by
  have he (i:ℕ) :
      (if l≤ i∧i< r then f i else 0)+(if i<l then f i else 0) =
        if i< max l r then f i else 0:= by
    by_cases h₁:i<l <;> by_cases h₂:i< r <;> simp [h₁,h₂,lt_max_iff]
  have h:=congrArg (fun f=>aU f n) (funext he)
  rw [bh5,total_prefix,total_prefix,mD hl,mD (max_le hl hr)] at h
  have hm:Monotone (aU f) :=
    monotone_nat_of_le_succ fun n=> by rw [aU]; omega
  rw [hm.map_max] at h
  omega
private theorem row_pieces (a n j k l:ℕ) (hj:j<n)
    (hk :j<k↔n-j≤a-25-2*j) (hl:j<l↔a+j≤86) :
    min (n-j) (a-25-2*j)-(a+j-86) =
      (if j< min k l then n-j else 0) +
      (if l≤j∧j<k then 86+n-a-2*j else 0) +
      (if k≤j∧j<l then a-25-2*j else 0) +
      (if max k l≤j∧j<n then 61-3*j else 0) := by
  have hK' : k≤j ↔ ¬ j<k := by omega
  have hL' : l≤j ↔ ¬ j<l:= by omega
  simp only [lt_min_iff,max_le_iff,hK',hL']
  by_cases hK:j<k
  · rw [lV (hk.mp hK)]
    by_cases hL:j<l <;>
      simp only [hK,hL,hj,and_true,and_false,oD,
        ox ,ite_true,ite_false,zero_add,add_zero] <;> omega
  · have hmin:a-25-2*j≤n-j:= by
      have hh:=(not_congr hk).mp hK
      omega
    rw [mD hmin]
    by_cases hL:j<l <;>
      simp only [hK,hL,hj,and_true,and_false,oD,
        ox ,ite_true,ite_false,zero_add,add_zero] <;> omega
def c5X (q u:ℕ) :=
 let a :=u+2*q+1
 let n:=q+1
 let k :=min n (a+1-(25+n))
 let l:=min n (87-a)
 down 1 n (min k l) +
 (down 2 (86+n-a) k - down 2 (86+n-a) l) +
 (down 2 (a-25) l - down 2 (a-25) k) +
 (down 3 61 n - down 3 61 (max k l))
theorem eQo (q u:ℕ) :rows q u=c5X q u:= by
  let a :=u+2*q+1
  let n:=q+1
  let k :=min n (a+1-(25+n))
  let l:=min n (87-a)
  have hk :k≤n:=ov _ _
  have hl:l≤n:=ov _ _
  let f₁:= fun h:ℕ=>if h< min k l then n-h else 0
  let f₂:= fun h:ℕ=>if l≤h∧h<k then 86+n-a-2*h else 0
  let f₃:= fun h:ℕ=>if k≤h∧h<l then a-25-2*h else 0
  let f₄:= fun h:ℕ=>if max k l≤h∧h<n then 61-3*h else 0
  have he (j:ℕ) (hj:j≤n) :
      aU (a8b q u) j=aU (fun h=>f₁ h+f₂ h+f₃ h+f₄ h) j:= by
    induction j with
    | zero=>rfl
    | succ j ih =>
      have PN :a8b q u j=f₁ j+f₂ j+f₃ j+f₄ j:= by
        have hj' : j<n:= by omega
        have hkJ:j<k↔n-j≤a-25-2*j:= by dsimp [k]; omega
        have hlJ:j<l↔a+j≤86:= by dsimp [l]; omega
        have h₀:u+2*(q-j)+1-25=a-25-2*j:= by dsimp [a,n] at *; omega
        have h₁:u+2*q+j+1-86=a+j-86:= by dsimp [a]; omega
        unfold a8b bvg aAa
        rw [h₀,h₁]
        exact row_pieces a n j k l hj' hkJ hlJ
      exact congrArg₂ Nat.add (ih ((Nat.le_succ j).trans hj)) PN
  change aU (a8b q u) n= _
  rw [he n le_rfl]
  simp only [bh5]
  dsimp only [f₁,f₂,f₃,f₄]
  rw [total_prefix,mD ((ov k l).trans hk),vo _ _ _ _ hl hk,
    vo _ _ _ _ hk hl,vo _ _ _ _ (max_le hk hl) le_rfl]
  change _=down 1 n (min k l)+(down 2 (86+n-a) k - down 2 (86+n-a) l) +
    (down 2 (a-25) l - down 2 (a-25) k)+(down 3 61 n - down 3 61 (max k l))
  rw [down_eq 2 _ _ (lz (Or.inl rfl)),down_eq 2 _ _ (lz (Or.inl rfl)),
    down_eq 2 _ _ (lz (Or.inl rfl)),down_eq 2 _ _ (lz (Or.inl rfl)),
    down_eq 3 _ _ (lz (lz rfl)),down_eq 3 _ _ (lz (lz rfl)),
    ← down_eq 1 n (min k l) (Or.inl rfl)]
  simp only [Nat.one_mul]
end P5_8_1
end
section
set_option autoImplicit true
namespace q1EkR5c
open i4 (Jet alu)
open P5_8_1 MvPolynomial
open scoped BigOperators
noncomputable section
abbrev Exp:=Fin 3 →₀ ℕ
def exponent (a b c:ℕ) :Exp :=
 Finsupp.single 0 a+Finsupp.single 1 b+Finsupp.single 2 c
@[simp] theorem exponent_zero (a b c:ℕ) :exponent a b c 0=a := by simp [exponent]
@[simp] theorem bpQ (a b c:ℕ) :exponent a b c 1=b:= by simp [exponent]
@[simp] theorem d5n (a b c:ℕ) :exponent a b c 2=c:= by simp [exponent]
private theorem exponent_eq (a b c x y z :ℕ) :
   exponent a b c=exponent x y z↔a=x∧b=y∧c=z := by
 constructor
 · intro h
   exact ⟨by simpa using DFunLike.congr_fun h 0,by simpa using DFunLike.congr_fun h 1,
    by simpa using DFunLike.congr_fun h 2⟩
 · rintro ⟨rfl,rfl,rfl⟩
   rfl
private theorem expand (a b c:ℕ) :
    c9 (cy (exponent a b c) 1) =
      ∑ h∈Finset.range (a+1),∑ j∈Finset.range (a-h+1),
        cy (exponent h (b+j) (c+(a-h-j)))
          ((-1 :F)^(a-h-j)*(a.choose h:F)*((a-h).choose j:F)) := by
  classical
  let E :lK:=lI 0
  let V:lK:=lI 1
  let W:lK:=lI 2
  have hx :cy (exponent a b c) (1 :F)=E^a*(V^b*W^c) := by
    simp only [E,V,W,X_pow_eq_monomial,monomial_mul_monomial,one_mul,exponent,add_assoc]
  have hE :c9 E=E+(V + -W) := by
    simp [E,V,W,c9,sub_eq_add_neg]
    ac_rfl
  have hV:c9 V=V:= by simp [V,c9]
  have hW:c9 W=W:= by simp [W,c9]
  rw [hx,map_mul,map_mul,map_pow,map_pow,map_pow,hE,hV,hW,
    add_pow E (V + -W),Finset.sum_mul]
  refine lJ rfl fun h _ => ?_
  rw [add_pow V (-W)]
  simp only [Finset.mul_sum,Finset.sum_mul]
  refine lJ rfl fun j _ => ?_
  have hneg : -W=cy (Finsupp.single 2 1) (-1 :F) := by
    simp only [W,lI,map_neg]
  have hcast (n:ℕ) : (n:lK)=cy 0 (n:F) := by
    rw [monomial_zero',map_natCast]
  rw [hneg]
  simp only [E,V,W,X_pow_eq_monomial,monomial_pow,hcast,
    monomial_mul_monomial,one_mul,mul_one]
  apply congrArg₂ (fun e v=>(cy e v :lK))
  · ext i
    fin_cases i <;> simp [exponent,Nat.add_comm]
  · ring
theorem contact_coeff (r s :Jet) (v :F) :
    (c9 (cy (exponent s.a s.b s.c) v)).coeff (exponent r.a r.b r.c) =
      alu r s*v := by
  have hm: (cy (exponent s.a s.b s.c) v :lK)=v•cy (exponent s.a s.b s.c) 1 := by
    simp [smul_monomial]
  rw [hm,show c9 (v•cy (exponent s.a s.b s.c) 1) =
    v•c9 (cy (exponent s.a s.b s.c) 1) from contactChange.toLinearMap.map_smul _ _,
    coeff_smul,smul_eq_mul,mul_comm v]
  congr 1
  classical
  let P:=s.b≤ r.b∧s.c≤ r.c∧r.a+(r.b-s.b)+(r.c-s.c)=s.a
  have hex (h j:ℕ) (hh:h≤ s.a) (hj:j≤ s.a-h) :
      exponent h (s.b+j) (s.c+(s.a-h-j))=exponent r.a r.b r.c ↔
        P∧h=r.a∧j=r.b-s.b:= by
    rw [exponent_eq]
    dsimp [P]
    omega
  rw [expand]
  simp_rw [coeff_sum,coeff_monomial]
  by_cases hp:P
  · obtain ⟨hb,hc,ha⟩:=hp
    have hh:r.a≤ s.a := by omega
    have hj:r.b-s.b≤ s.a-r.a := by omega
    rw [Finset.sum_eq_single_of_mem r.a (Finset.mem_range.mpr (by omega))]
    · rw [Finset.sum_eq_single_of_mem (r.b-s.b) (Finset.mem_range.mpr (by omega))]
      · rw [oY  ((hex _ _ hh hj).2 ⟨⟨hb,hc,ha⟩,rfl,rfl⟩),alu,
          oY  ⟨hb,hc,ha⟩,show s.a-r.a-(r.b-s.b)=r.c-s.c by omega]
      · intro j hj' hne
        exact nX  fun he=>hne ((hex _ _ hh (by simpa using hj')).1 he).2.2
    · intro h hh' hne
      exact oq fun j hj' => nX fun he =>
        hne ((hex _ _ (by simpa using hh') (by simpa using hj')).1 he).2.1
  · rw [alu,nX hp]
    exact oq fun h hh=>oq fun j hj=>nX fun he =>
      hp ((hex _ _ (by simpa using hh) (by simpa using hj)).1 he).1
end
end q1EkR5c
end
