import ProximityPrize.SubmissionLower.ZLcmX9d
import ProximityPrize.SubmissionLower.ZkYlUGe
import Mathlib.Data.Nat.Basic
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.ZskDvCd
set_option Elab.async false
open _root_ renaming Fin.forall_fin_succ → z60, Fin.forall_fin_two → zzH, Fin.sum_univ_eq_sum_range → zdx, Finset.le_sup → zZi, Finset.sup_le → zf9, Finsupp.degree_single → zlu, Int.toNat_of_nonneg → zi4, Matrix.range_cons → zuW, Matrix.range_empty → zn6, MvPolynomial.support_add → zut, Nat.find → zqr, Polynomial.C → z1z, Set.singleton_union → z1f, Submodule.mem_bot → zLn, Submodule.mem_top → z8t, Submodule.subset_span → zBO
section
set_option autoImplicit true
namespace qcIhqIe
open P6_6_2 qwbsesc Finset
open xE (gd oldCount denominator)
open GI (anX)
open aAZ (bD6 Jc)
open private term clipped_sum from ProximityPrize.SubmissionLower.ZeuEwuc
open private df6 from ProximityPrize.SubmissionLower.Z0rImdc
open scoped BigOperators
private theorem cum_neg (d u:ℤ) (hu:u<0) :gd d u=0:= by
  simp [gd,hu]
private def extra (q r :ℕ) :ℤ :=
  if 3000≤q+r∧r<1710 then
    denominator (1709-(r :ℤ)) - denominator (1709-(r :ℤ)-3*((q:ℤ)+r-2999))
  else 0
def premium (t:ℕ) :ℤ :=
  ∑ j∈range t,(denominator ((t:ℤ)-1-j) - denominator ((t:ℤ)-4*(j+1)))
private theorem lattice_eq (q r :ℕ) (hq:1291≤q) (hq' : q<1710)
    (hr :r<1710) (hc:3000≤q+r) :
    latticeAllowance ⟨q,1710-(r :ℤ),1710,570,4710-(q:ℤ) - r⟩ =
      extra q r := by
  let o:ℤ:=4710-(q:ℤ) - r
  let u:ℤ:=1709-(r :ℤ)
  have ho:1292≤o∧o≤1710 := by dsimp [o]; omega
  have hup:0≤u∧u≤418:= by dsimp [u]; omega
  let x :ℤ:=max 0 ((q:ℤ)-(o+2)/3+1)
  let y :ℤ:=2*max 0 (855 - max 0 ((o-(q:ℤ)+1)/2)+1)
  let z :ℤ:=3*(1710-o+1)
  have hx :u<x :=(show u<(q:ℤ)-(o+2)/3+1 by omega).trans_le (le_max_right _ _)
  have hy0:max 0 ((o-(q:ℤ)+1)/2)≤210 :=max_le (by decide) (by omega)
  have hy1 :855 - max 0 ((o-(q:ℤ)+1)/2)+1 ≤
      max 0 (855 - max 0 ((o-(q:ℤ)+1)/2)+1) :=le_max_right _ _
  have hy :u<y := by dsimp [y]; omega
  have hz :0≤z := by dsimp [z]; omega
  unfold latticeAllowance extra
  dsimp only
  rw [ite_eq_left ⟨hc,hr⟩,min_eq_left (by omega : (q:ℤ)≤1710),
    show (1710 :ℤ)/2=855 by decide,min_eq_right (by omega : (855:ℤ)≤q),
    min_eq_left (by omega : (570:ℤ)≤q),
    min_eq_right (show (1710 :ℤ) - o≤570 by omega),
    max_eq_right (show 0≤(1710 :ℤ) - o+1 by omega),
    show (1710 :ℤ) - r - 1=u by dsimp [u]; ring]
  change denominator u - denominator (u-x) - denominator (u-y) - denominator (u-z) +
    denominator (u-x-y)+denominator (u-x-z)+denominator (u-y-z) -
    denominator (u-x-y-z)= _
  rw [Jc _ (by omega :u-x<0),
    Jc _ (by omega :u-y<0),Jc _ (by omega :u-x-y<0),
    Jc _ (by omega :u-x-z<0),Jc _ (by omega :u-y-z<0),
    Jc _ (by omega :u-x-y-z<0)]
  simp only [sub_zero,add_zero]
  rw [show u-z=1709-(r :ℤ)-3*((q:ℤ)+r-2999) by unfold u z o; ring]
private theorem bBL (q:ℕ) (r :Offset) (hq:1291≤q) (hq' : q<1710)
    (p:Fin 11→ℕ) :xR q r p≤(term q r.val+extra q r.val).toNat := by
  have hd:iO q=q:= by
    unfold iO P6_6.Dj
    rw [ite_eq_left (by omega),min_eq_left (by omega :q≤1710),min_self]
  by_cases hr :1710≤(4709:ℤ) - q - r.val
  · refine (block_le_old q r p).trans ?_
    rw [b3v,hd,oldCount,term,min_eq_left hr,extra,ite_eq_right (by omega)]
    dsimp only
    rw [show (1710 :ℤ) - r.val - 1=1709 - r.val by ring,min_eq_right (by omega),
      bCi _ _ (by decide),bCi _ _ (by omega),add_zero]
  · refine (min_le_right _ _).trans ?_
    rw [b3v,hd]
    have hcut: (4710 :ℤ) - q - r.val - 1=4709 - q - r.val := by ring
    by_cases hp:1710≤ r.val
    · unfold oppositeBound
      dsimp only
      by_cases ho: (4710 :ℤ) - q - r.val≤0
      · rw [ite_eq_left ho]
        exact Nat.zero_le _
      · rw [ite_eq_right ho,ite_eq_left (by omega : (1710 :ℤ) - r.val≤0),hcut,
          bCi _ _ (min_le_left _ _),term,
          cum_neg _ (1709-(r.val :ℤ)) (by omega),extra,ite_eq_right (by omega),sub_zero,add_zero]
    · have he :=lattice_eq q r.val hq hq' (by omega) (by omega)
      unfold oppositeBound
      dsimp only
      rw [ite_eq_right (by omega : ¬ (4710 :ℤ) - q - r.val≤0),
        ite_eq_right (by omega : ¬ (1710 :ℤ) - r.val≤0),he,hcut,oldCount]
      dsimp only
      rw [show (1710 :ℤ) - r.val - 1=1709 - r.val by ring,
        min_eq_right (show (1709:ℤ) - r.val≤1710 by omega),
        bCi _ _ (by decide),bCi _ _ (by omega),
        bCi _ _ (min_le_left _ _),term]
      apply Int.toNat_le_toNat
      have hm:=min_le_left (extra q r.val)
        (gd q 1710 - gd q (min 1710 (4709-(q:ℤ) - r.val)))
      omega
private theorem sum_term (q:ℕ) (hq:q<1710) :
    (∑ r :Offset,term q r.val)=(3000-(q:ℤ))*gd q 1710 := by
  simp only [term,sum_sub_distrib]
  change ((∑ r :Fin 4710,gd q (min 1710 (4709-(q:ℤ) - r.val))) -
    ∑ r :Fin 4710,gd q (1709-(r.val :ℤ)))= _
  rw [zdx (fun r :ℕ=>gd q (min 1710 (4709-(q:ℤ) - r))),
    zdx (fun r :ℕ=>gd q (1709-(r :ℤ))),
    show (4709:ℤ)-(q:ℤ)=((4709 - q:ℕ) :ℤ) by omega,
    clipped_sum q (4709-q) 4710 (by omega) (by omega)]
  have h:=df6 q 1709 4710 (by decide)
  norm_num only [Nat.cast_ofNat] at h
  rw [h,add_sub_cancel_left,
    show ((4709 - q+1 - 1710 :ℕ) :ℤ)=3000-(q:ℤ) by omega]
private theorem sum_extra (q:ℕ) (hq:1291≤q) (hq' : q<1710) :
    (∑ r :Offset,extra q r.val)=premium (q-1290) := by
  have e :4710=(3000 - q)+(q - 1290)+3000:= by omega
  change (∑ r :Fin 4710,extra q r.val)= _
  rw [zdx (extra q),e,sum_range_add,sum_range_add]
  have e0 (i:ℕ) (hi:i∈range (3000-q)) :extra q i=0:= by
    have :=mem_range.mp hi
    unfold extra
    rw [ite_eq_right (by omega)]
  have e1 (i:ℕ) (hi:i∈range 3000) :extra q (3000-q+(q-1290)+i)=0:= by
    unfold extra
    rw [ite_eq_right (by omega)]
  rw [sum_eq_zero e0,sum_eq_zero e1,zero_add,add_zero,premium]
  apply sum_congr rfl
  intro j hj
  have :=mem_range.mp hj
  unfold extra
  rw [ite_eq_left (by omega),
    show (1709:ℤ)-((3000-q+j:ℕ) :ℤ)=((q-1290:ℕ) :ℤ)-1-j by omega,
    show ((q-1290:ℕ) :ℤ)-1-j-3*((q:ℤ)+((3000-q+j:ℕ) :ℤ)-2999) =
      ((q-1290:ℕ) :ℤ)-4*((j:ℤ)+1) by omega]
theorem aH4 (q:ℕ) (hq:1291≤q) (hq' : q<1710) (p:Offset→Fin 11→ℕ) :
    (al2 q p:ℤ)≤(3000-(q:ℤ))*gd q 1710+premium (q-1290) := by
  rw [← sum_term q hq',← sum_extra q hq hq',← sum_add_distrib,al2,Nat.cast_sum]
  apply sum_le_sum
  intro r _
  have ht:0≤term q r.val :=
    sub_nonneg.mpr (anX q (le_min (by omega) (by omega)))
  have he :0≤extra q r.val := by
    unfold extra
    split
    · rename_i h
      exact sub_nonneg.mpr (bD6 _ _ (by omega) (by omega))
    · exact le_rfl
  have hb:=Int.ofNat_le.mpr (bBL q r hq hq' (p r))
  rwa [zi4 (add_nonneg ht he)] at hb
end qcIhqIe
end
section
set_option autoImplicit true
namespace qKSECDd
open xE (Flag gd U1 denominator oldCount AO m5 BH)
open akL (KP aDd)
open GI (anX)
open aAZ (anW aej bwI Jc)
open P6_6_2 (Offset pT xR oppositeBound latticeAllowance iO)
open qwbsesc (b3v pairPowers residual_pair block_le_old block_le_residual)
open private aOG from ProximityPrize.SubmissionLower.AR
local notation "D" => denominator
def Ej (t:ℕ) :Fin 11→ℕ:=pairPowers 10 10 t 0
def jO (m:ℤ) :ℤ:=(m+1713)/4
private theorem diag (d u:ℤ) (hd:2≤d) (hu:u≤d) :
    gd d u=D u :=
  (anW _ _ hd (by omega)).trans (bwI _ _ hu)
private theorem den_mono {u v :ℤ} (huv :u≤v) (hv :v≤1710) :D u≤D v := by
  rw [← diag 1710 u (by decide) (huv.trans hv),← diag 1710 v (by decide) hv]
  exact anX 1710 huv
private theorem col (d u c:ℤ) (hd:2≤d) (hu:u≤d) (hc:0≤ c)
    (hcap:d<3*(c+1)) :U1 d u c=D u:= by
  unfold U1
  rw [ite_eq_right (by omega),diag d u hd hu]
  have hz :u-3*(c+1)<0:= by omega
  simp only [gd,hz,decide_true,Bool.or_true,ite_true,sub_zero]
private theorem old_diag (d j c o:ℤ) (hd:2≤d) (hj:j≤d) (hc:0≤ c)
    (hcap:d<3*(c+1)) :oldCount ⟨d,j+1,d,c,o⟩=D d - D j:= by
  simp only [oldCount,add_sub_cancel_right,min_eq_right hj]
  rw [col _ _ _ hd le_rfl hc hcap,col _ _ _ hd hj hc hcap]
private theorem degree_eq (h:ℕ) (hh:h<400) :iO (2150+h)=1710 := by
  unfold iO P6_6.Dj
  rw [ite_eq_left (by omega),min_eq_right (by omega),min_eq_right (by omega)]
theorem flag_at (h:ℕ) (hh:h<400) (r :Offset) :
    pT (2150+h) r=⟨1710,1710-(r.val :ℤ),1710,570,(850-(h:ℤ))+(1710-r.val)⟩:= by
  rw [b3v,degree_eq h hh]
  push_cast
  congr 1 <;> ring
theorem old_le (h j:ℕ) (hh:h<400) (r :Offset)
    (hr : (r.val :ℤ)=1709-(j:ℤ)) (p:Fin 11→ℕ) :
    (xR (2150+h) r p:ℤ)≤D 1710 - D j:= by
  have hj: (j:ℤ)≤1710 := by omega
  have hb:=Int.ofNat_le.mpr (block_le_old (2150+h) r p)
  rw [flag_at h hh,hr,show (1710 :ℤ)-(1709-(j:ℤ))=j+1 by ring,
    old_diag _ _ _ _ (by decide) hj (by decide) (by decide),
    Int.toNat_of_nonneg (sub_nonneg.mpr (den_mono hj le_rfl))] at hb
  exact hb
theorem pos_le (h i:ℕ) (hh:h<400) (r :Offset)
    (hr : (r.val :ℤ)=1710+(i:ℤ)) (p:Fin 11→ℕ) :
    (xR (2150+h) r p:ℤ)≤D (849-(h:ℤ)-i) := by
  refine (Int.ofNat_le.mpr (min_le_right _ _)).trans ?_
  rw [flag_at h hh,hr]
  have hl: (1710 :ℤ)-(1710+(i:ℤ))≤0:= by omega
  have he : (850-(h:ℤ))+(1710-(1710+(i:ℤ)))=850-(h:ℤ)-i:= by ring
  simp only [oppositeBound,he,hl,ite_true]
  by_cases ho: (850:ℤ)-h-i≤0
  · simp [ho,Jc _ (by omega : (849:ℤ)-h-i<0)]
  · have harg : (850:ℤ)-h-i-1=849-h-i:= by ring
    rw [ite_eq_right ho,harg,min_eq_right (by omega),
      col _ _ _ (by decide) (by omega) (by decide) (by decide)]
    have hnon :=den_mono (show (-1 :ℤ)≤849-h-i by omega) (by omega)
    rw [Jc _ (by decide)] at hnon
    exact (Int.toNat_of_nonneg hnon).le
private theorem allowance_eq (m j:ℤ) (hm:451≤ m) (ho:m+j<1710) (hj:j<1141) :
    latticeAllowance ⟨1710,j+1,1710,570,m+j+1⟩=D j - D (4*j+3*m-5130) := by
  let x :=1711-(m+j+3)/3
  let z :=3*(min 570 (1709-m-j)+1)
  have hx :1141≤x := by dsimp [x]; omega
  have hz :0≤z := by dsimp [z]; omega
  have he : (1710 :ℤ)-(m+j+1)=1709-m-j:= by ring
  have hy :max 0 ((m+j+1-1710+1)/2)=0:= by omega
  simp only [latticeAllowance,min_self,min_eq_left (by decide : (570:ℤ)≤1710),
    min_eq_right (by decide : (1710 :ℤ)/2≤1710),hy,sub_zero,he,add_sub_cancel_right]
  have hx' : max 0 (1710-(m+j+1+2)/3+1)=x := by dsimp [x]; omega
  rw [hx',max_eq_right (by omega :0≤ min 570 (1709-m-j)+1)]
  change D j - D (j-x) - D (j-1712) - D (j-z) +
    D (j-x-1712)+D (j-x-z)+D (j-1712-z) - D (j-x-1712-z)= _
  simp (disch:=omega) only [Jc,sub_zero,add_zero]
  by_cases hz' : (570:ℤ)≤1709-m-j
  · have hv :z=1713:= by simp [z,min_eq_left hz']
    simp (disch:=omega) only [hv,Jc,sub_zero]
  · have hv :j-z=4*j+3*m-5130:= by
      dsimp [z]
      rw [min_eq_right (by omega)]
      ring
    rw [hv]
theorem opp_le (h j:ℕ) (hh:h<400) (hmj: (850:ℤ)-h+j<1710) (hj:j<1141)
    (r :Offset) (hr : (r.val :ℤ)=1709-(j:ℤ)) (p:Fin 11→ℕ) :
    (xR (2150+h) r p:ℤ)≤D (850-(h:ℤ)+j) - D (4*(j:ℤ)+3*(850-(h:ℤ))-5130) := by
  let m:ℤ:=850-h
  change _≤D (m+j) - D (4*(j:ℤ)+3*m-5130)
  have hf :pT (2150+h) r=⟨1710,(j:ℤ)+1,1710,570,m+j+1⟩:= by
    rw [flag_at h hh,hr]
    dsimp [m]
    congr 1 <;> ring
  refine (Int.ofNat_le.mpr (min_le_right _ _)).trans ?_
  rw [hf]
  have hn:0≤D (m+j) - D (4*(j:ℤ)+3*m-5130) :=
    sub_nonneg.mpr (den_mono (by omega) (by omega))
  have hm:451≤ m:= by dsimp [m]; omega
  have ho:m+(j:ℤ)<1710 :=hmj
  have hop:oppositeBound ⟨1710,(j:ℤ)+1,1710,570,m+j+1⟩ ≤
      (D (m+j) - D (4*(j:ℤ)+3*m-5130)).toNat := by
    unfold oppositeBound
    dsimp only
    rw [ite_eq_right (by omega),ite_eq_right (by omega),add_sub_cancel_right,
      min_eq_right (show m+j≤1710 by omega),
      col 1710 (m+j) 570 (by decide) (by omega) (by decide) (by decide),
      col 1710 1710 570 (by decide) (by decide) (by decide) (by decide),
      old_diag _ _ _ _ (by decide) (by omega) (by decide) (by decide),
      allowance_eq _ _ hm ho (by omega)]
    apply Int.toNat_le_toNat
    have hb:=min_le_left (D j - D (4*(j:ℤ)+3*m-5130)) (D 1710 - D (m+j))
    omega
  exact (zi4 hn) ▸ Int.ofNat_le.mpr hop
private theorem brp (F:Flag) (p:Fin 11→ℕ) :
    m5 (BH F p)≤oldCount F:= by
  have hc:=bjv.proof aw7.proof
  have ht:=aYY.proof aw7.proof
  have hk :=aOG (BH F p) (hc _) (ht _)
  obtain ⟨f,hf⟩:=bjw.proof F p
  have hi:=LinearMap.finrank_le_finrank_of_injective (f :=f) hf
  have hn:=(KP F).finrank_range_add_finrank_ker
  rw [aDd] at hn
  have ho:=hc F
  omega
def kernelValue (m t j:ℤ) :ℤ :=
  let a :=jO m
  D (1710-3*t) - D (m+j-3*t)+D (m+j-3*a) - D (j-2*t) +
    D (j+a-1711)+D (j+a-1712)+D (j+a-1713)
private theorem aOk (m t j:ℤ) (hm:451≤ m) (hm' : m≤850)
    (hj:j<1190) (ho:m+j<1710) (ht:0≤t) (ht' : t≤512) :
    m5 ⟨1710-3*t,j+1-2*t,1710-3*t,570-t,m+j+1-3*t⟩=kernelValue m t j:= by
  let a :=jO m
  let d:=1710-3*t
  let o:=m+j-3*t
  let l:=j-2*t
  have ha :541≤a∧a≤640:= by dsimp [a,jO]; omega
  have hbal:o+1-1-(l+1)+d=m+1709-4*t:= by dsimp [o,l,d]; ring
  have hdiv : (m+1709-4*t)/4=a-1-t:= by dsimp [a,jO]; omega
  have hsize :2≤d-(a-t) := by dsimp [d]; omega
  have hlower :l≤2*(d-(a-t))+2 := by dsimp [l,d]; omega
  have hold:oldCount ⟨d,l+1,d,570-t,o+1⟩=D d - D l :=
    old_diag _ _ _ _ (by dsimp [d]; omega) (by dsimp [l,d]; omega) (by omega) (by dsimp [d]; omega)
  rw [show j+1-2*t=l+1 by dsimp [l]; ring,show m+j+1-3*t=o+1 by dsimp [o]; ring]
  change m5 ⟨d,l+1,d,570-t,o+1⟩= _
  simp only [m5,show ¬ d<0 by omega,show ¬ 570-t<0 by omega,
    decide_false,Bool.false_or,Bool.false_eq_true,ite_false,hold]
  unfold AO
  dsimp only
  rw [hbal,ite_eq_right (by omega),hdiv,min_eq_right (by omega),
    show a-1-t+1=a-t by ring,add_sub_cancel_right,add_sub_cancel_right,
    diag _ o (by omega) (by dsimp [o,d]; omega),
    diag _ (o-3*(a-t)) hsize (by dsimp [o,d]; omega),
    diag _ l (by omega) (by dsimp [l,d]; omega),
    anW _ l hsize hlower]
  unfold aej kernelValue
  change _=D d - D o+D (m+j-3*a) - D l+D (j+a-1711)+D (j+a-1712)+D (j+a-1713)
  have e1 :o-3*(a-t)=m+j-3*a := by dsimp [o]; ring
  have e2 (k :ℤ) :l-(d-(a-t))-k=j+a-1710-k := by dsimp [l,d]; ring
  rw [e1,e2 1,e2 2,e2 3,
    show j+a-1710-1=j+a-1711 by ring,
    show j+a-1710-2=j+a-1712 by ring,
    show j+a-1710-3=j+a-1713 by ring]
  ring
theorem prod_le (h j t:ℕ) (hh:h<400) (hmj: (850:ℤ)-h+j<1710) (hj:j<1190)
    (ht:t≤512) (r :Offset) (hr : (r.val :ℤ)=1709-(j:ℤ)) :
    (xR (2150+h) r (Ej t) :ℤ)≤D 1710 - D j - kernelValue (850-(h:ℤ)) t j:= by
  let m:ℤ:=850-h
  let F:=pT (2150+h) r
  have hf :F=⟨1710,(j:ℤ)+1,1710,570,m+j+1⟩:= by
    rw [show F=pT (2150+h) r from rfl,flag_at h hh,hr]
    dsimp [m]
    congr 1 <;> ring
  have hc:oldCount F=D 1710 - D j:= by
    rw [hf,old_diag _ _ _ _ (by decide) (by omega) (by decide) (by decide)]
  have hg:m5 (BH F (Ej t))=kernelValue m t j:= by
    rw [hf,Ej,residual_pair]
    have Kr :xE.Jd 10=⟨3,2,3,1,3⟩:=rfl
    simp only [Kr,Nat.cast_zero,zero_mul,add_zero,mul_one]
    rw [show (t:ℤ)*3=3*t by ring,show (t:ℤ)*2=2*t by ring]
    have hm:451≤ m:= by dsimp [m]; omega
    have hu:m≤850:= by dsimp [m]; omega
    exact aOk m t j hm hu (by omega) hmj (by omega) (by omega)
  have hn:=sub_nonneg.mpr (brp F (Ej t))
  have hb:=block_le_residual (2150+h) r (Ej t)
  exact (by rw [← hc,← hg,← zi4 hn]; exact Int.ofNat_le.mpr hb)
end qKSECDd
end
section
set_option autoImplicit true
namespace qwzqCne
open qK9H6va (offset)
open qxuyiwe (profileCutoff)
def c1 :Prop :=aGq 54 82
def c2 :Prop :=aGq 83 89
def c3:Prop :=aGq 90 95
def c4 :Prop :=aGq 96 99
def c5:Prop :=aGq 100 103
def c6:Prop :=aGq 104 106
def c7:Prop :=aGq 107 108
def c8:Prop :=aGq 109 110
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4)
    (h5:c5) (h6:c6) (h7:c7) (h8:c8) :qxuyiwe.c4 := by
  have head:aGq 54 (tailCost - 1) := by
    intro e hlo hhi
    let w:=cP (aD e.val)
    change 54≤w at hlo
    change w≤110 at hhi
    by_cases hw:w≤82
    · exact h1 e hlo hw
    by_cases h89:w≤89
    · exact h2 e (by omega) h89
    by_cases h95:w≤95
    · exact h3 e (by omega) h95
    by_cases h99:w≤99
    · exact h4 e (by omega) h99
    by_cases h103:w≤103
    · exact h5 e (by omega) h103
    by_cases h106:w≤106
    · exact h6 e (by omega) h106
    by_cases h108:w≤108
    · exact h7 e (by omega) h108
    · exact h8 e (by omega) hhi
  refine ⟨ix,fun q hd r => ?_⟩
  exact (fTj head tailWitness q (offset r) hd).trans
    (card_le_eligible (offset r) (profileCutoff q 54 (offset r)))
end qwzqCne
end
section
set_option autoImplicit true
namespace q1US8Va
private def counts :Nat→Nat
  | 0=>0x1077
  | 1=>0xb8
  | 2=>0xb8
  | 3=>0xf8
  | 4=>0xc1076
  | 5=>0x40b7
  | 6=>0x40b7
  | 7=>0x50f7
  | 8=>0x50c1075
  | 9=>0x1840b6
  | 10=>0x1840b6
  | 11=>0x1c50f6
  | 12=>0x1c50c1074
  | 13=>0x81840b5
  | 14=>0x81840b5
  | 15=>0x91c50f5
  | 16=>0x91c50c1073
  | 17=>0x2881840b4
  | 18=>0x2881840b4
  | 19=>0x2c91c50f4
  | 20=>0x2c91c50c1072
  | 21=>0xc2881840b3
  | 22=>0xc2881840b3
  | 23=>0xd2c91c50f3
  | 24=>0xd2c91c50c1071
  | 25=>0x38c2881840b2
  | 26=>0x38c2881840b2
  | 27=>0x3cd2c91c50f2
  | 28=>0x34d2c91c50c1070
  | 29=>0xc40c2881840b1
  | 30=>0xa3cc2881840b1
  | 31=>0x93902c91c50f1
  | 32=>0x73112c91c50c106f
  | 33=>0x14b40f2881840b0
  | 34=>0xca3922881840b0
  | 35=>0x483523891c50f0
  | 36=>0x63104891c50c106e
  | 37=>0x8b3d43481840af
  | 38=>0xa3924481840af
  | 39=>0x335154c1c50ef
  | 40=>0x3905101c50c106d
  | 41=>0x441354b1840ae
  | 42=>0x45258f1840ae
  | 43=>0x1535542850ee
  | 44=>0x145573850c106c
  | 45=>0x1565d32440ad
  | 46=>0x166173440ad
  | 47=>0x565a4880ed
  | 48=>0x5db58c0c106b
  | 49=>0x571c4470ac
  | 50=>0x5de58b0ac
  | 51=>0x15e7511ac
  | 52=>0x1785628106a
  | 53=>0x15f75116b
  | 54=>0x178d62ab
  | 55=>0x15f75112a
  | 56=>0x5e358a069
  | 57=>0x15f751169
  | 58=>0x5e158a068
  | 59=>0x579d406067
  | 60=>0x5de58c0a7
  | 61=>0x571c4470a6
  | 62=>0x176d6303065
  | 63=>0x159652203064
  | 64=>0x166183440a4
  | 65=>0x1565d32440a3
  | 66=>0x5145ce143062
  | 67=>0x54d650a143061
  | 68=>0x45258f1840a1
  | 69=>0x43d354b1840a0
  | 70=>0xe45440714305f
  | 71=>0xcd45530714305e
  | 72=>0x939244818409e
  | 73=>0x8c3d434818409d
  | 74=>0x18c41224714305c
  | 75=>0x20d48e24714305b
  | 76=>0xca39228818409b
  | 77=>0x14b40f28818409a
  | 78=>0x1cc44b247143059
  | 79=>0x24e40b247143058
  | 80=>0xa3cc288184098
  | 81=>0xc40c288184097
  | 82=>0xd34b247143056
  | 83=>0xf34b247143055
  | 84=>0x38c288184095
  | 85=>0x38c288184094
  | 86=>0x34b247143053
  | 87=>0x34b247143052
  | 88=>0xc288184092
  | 89=>0xc288184091
  | 90=>0xb247143050
  | 91=>0xb24714304f
  | 92=>0x28818408f
  | 93=>0x28818408e
  | 94=>0x24714304d
  | 95=>0x24714304c
  | 96=>0x818408c
  | 97=>0x818408b
  | 98=>0x714304a
  | _=>0
def groupCount (g i:Nat) :Nat :=
  let z :=counts g
  let lo:=z % 64
  if i<lo then 0 else (z >>> (6*(i-lo+1))) % 64
end q1US8Va
end
section
set_option autoImplicit true
namespace q1US8Va
open qK9H6va (offset Gy)
def KC (r cap:ℕ) :Prop :=
  (Gy 55 (offset r)).rank≤ cap
abbrev Pivot:=Σ k :Fin 99,Σ i:Fin 57,Fin (groupCount k.val i.val)
abbrev Selected (lo w:ℕ) :=
  {p:Pivot // lo≤p.2.1.val∧p.1.val+p.2.1.val<w}
noncomputable instance (lo w:ℕ) :Fintype (Selected lo w) :=Fintype.ofFinite _
end q1US8Va
end
section
set_option autoImplicit true
set_option Elab.async false
namespace P6_6_6
noncomputable section
open aR wH K1_13_7_6 MvPolynomial
open bAo (aye bmH bWj)
open P6_6 (aPr mu tau nu)
open private cVG cDl from ProximityPrize.SubmissionLower.E5
theorem epf (P Q R:af 3)
    (hP:Gh P IG.b IG.j)
    (hQ:Gh Q IG.b IG.j)
    (hR:Gh R IG.b IG.j)
    (points :Finset Sz) (hpoints : ∀ y∈points,bzn P Q R y) :
    points.card≤brg:= by
  classical
  let φ:=monomialMap cH (cap aPr (2*0x57bcf00))
  have hmap :Function.Surjective φ :=
    aye (by decide :1≤aPr) (by decide :1≤0x57bcf00)
  let f :=fW P
  let g:=fW Q
  let h:=fW R
  let D:=aGW φ
  have hcuts : ∀ t:Lower,t∈({f,g,h} : Set Lower) →
      ∃ L:MvPolynomial (cap aPr (2*0x57bcf00)) cH,φ L=t∧L.totalDegree≤1 := by
    intro t ht
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact bmH (b:=aPr) (j:=0x57bcf00) P hP
    · exact bmH (b:=aPr) (j:=0x57bcf00) Q hQ
    · exact bmH (b:=aPr) (j:=0x57bcf00) R hR
  have hpay : ∀ t:Lower,t∈({f,g,h} : Set Lower) →
      ∀ p:PrimeSpectrum Lower,t∉p.asIdeal →
        ∀ qs :Finset (PrimeSpectrum Lower),
          (∀ q∈qs,q.asIdeal∈(ke p t).minimalPrimes) →
          (∀ q∈qs,localColength q (ke p t) < ⊤) →
          a3c D p t qs≤D p:= by
    intro t ht p hp qs hmin hfin
    obtain ⟨L,rfl,hL⟩:=hcuts t ht
    exact ML.proof φ hmap p L hL hp qs hmin hfin
  have hpoints_cost:=cVG f g h D
    (fun q=>affineDegree_nonneg (q.asIdeal.comap φ))
    (fun y q hy=>(dHY φ hmap y q hy).ge)
    hpay points Ny hpoints
  have hbound:=hpoints_cost.trans (bWj (by decide)
    (by decide :2*0x57bcf00≤aPr))
  have hprice :=cDl points.card aPr 0x57bcf00 Ny
    (by decide) (by decide) hbound
  unfold brg
  have hden:4*mu*(mu - tau+1)*nu=4*Ny := by
    calc
      _=4*(mu*(mu - tau+1)*nu) := by ac_rfl
      _ = _:=congrArg (fun n:ℕ=>4*n) a6E
  rw [hden]
  exact hprice
end
end P6_6_6
end
section
set_option autoImplicit true
set_option Elab.async false
namespace P6_6_6
noncomputable section
open aR jA MvPolynomial UniqueFactorizationMonoid
open P6_6 (aPr aWz mu tau)
private abbrev Exponent:=Fin 3 →₀ ℕ
open private avc apx dhV cNr bFB b6f from ProximityPrize.SubmissionLower.E5
private theorem b2c {P f :Lower} (hf :Prime f)
    (hlow:axh.bRT P tau) :
    ∃ a<tau,f^a∣P ∧ ¬ f^(a+1)∣P:= by
  classical
  have hex : ∃ n:ℕ,¬ f^n∣P:=⟨tau,hlow f hf⟩
  have hpos :0<zqr hex := by
    by_contra! h
    have hz :zqr hex=0:= by omega
    exact Nat.find_spec hex (by simp [hz])
  have hle :=Nat.find_min' hex (hlow f hf)
  let a :=zqr hex - 1
  have ha :a+1=zqr hex :=Nat.sub_add_cancel hpos
  refine ⟨a,by omega,not_not.mp (Nat.find_min hex (by omega :a<zqr hex)),?_⟩
  rw [ha]
  exact Nat.find_spec hex
private def admissible (P:Lower) :Submodule iP Lower where
  carrier := {Q |
    (∀ m∈Q.support,m.degree≤aPr ∧
      Finsupp.weight (R:=ℕ) (Fin.val :Fin 3→ℕ) m≤aWz) ∧
    ∀ y,Qu P y mu→Qu Q y Fw}
  zero_mem' := by
    simp [Qu]
  add_mem' := by
    intro Q R hQ hR
    change (_∧_) at hQ hR ⊢
    refine ⟨fun m hm => ?_,fun y hy m hm => ?_⟩
    · exact (Finset.mem_union.mp (support_add hm)).elim (hQ.1 m) (hR.1 m)
    · rw [map_add] at hm
      exact (Finset.mem_union.mp (support_add hm)).elim (hQ.2 y hy m) (hR.2 y hy m)
  smul_mem' := by
    intro c Q hQ
    change (_∧_) at hQ ⊢
    rw [Algebra.smul_def]
    change (_ ∧ ∀ y,Qu P y mu→Qu (C c*Q) y Fw)
    refine ⟨fun m hm=>hQ.1 m (support_C_mul_le Q c hm),fun y hy m hm => ?_⟩
    rw [map_mul,show translate y (C c)=C c by simp [jA.translate]] at hm
    exact hQ.2 y hy m (support_C_mul_le (translate y Q) c hm)
private theorem epl {P:Lower} (hb:P.totalDegree≤aPr)
    (hj:H9 P≤aWz) (i:Fin 3) {a :ℕ} (ha :a<tau) :
    avc i a P∈admissible P:= by
  refine ⟨fun m hm => ?_,fun y hy m hm => ?_⟩
  · have hs :=apx i a P hm
    have htotal:=(le_totalDegree hs).trans hb
    change (m+Finsupp.single i a).degree≤_ at htotal
    rw [map_add,zlu] at htotal
    have hindex :=(zZi (f := fun x :Exponent=>x.sum (fun j e=>j.val*e)) hs).trans hj
    rw [← b6f,map_add] at hindex
    exact ⟨(Nat.le_add_right _ _).trans htotal,(Nat.le_add_right _ _).trans hindex⟩
  · rw [dhV] at hm
    have hord:=hy _ (apx i a (translate y P) hm)
    change mu≤(m+Finsupp.single i a).degree at hord
    change mu - tau+1≤ m.degree
    rw [map_add,zlu] at hord
    have ht:tau≤ mu:= by decide
    omega
theorem ePB (P:Lower) (hP:P≠0) (hb:P.totalDegree≤aPr)
    (hj:H9 P≤aWz) (hlow:axh.bRT P tau) :
    ∃ Q:Lower,Q≠0∧Q.totalDegree≤aPr∧H9 Q≤aWz ∧
      IsRelPrime P Q ∧ ∀ y,Qu P y mu→Qu Q y Fw:= by
  classical
  let partials :Set Lower := {Q | ∃ (i:Fin 3) (a :ℕ),a<tau∧Q=avc i a P}
  let N :=Submodule.span iP partials
  have hN :N≤admissible P:=Submodule.span_le.mpr (by
    rintro _ ⟨i,a,ha,rfl⟩
    exact epl hb hj i ha)
  have hPN :P∈N :=zBO ⟨0,0,by decide,rfl⟩
  let _:StrongNormalizationMonoid Lower :=UniqueFactorizationMonoid.strongNormalizationMonoid
  let _:Infinite iP:=Infinite.of_injective DI DI.injective
  let factors :=(normalizedFactors P).toFinset
  let forbidden:Option ↥factors→Submodule iP N
    | none => ⊥
    | some f=>((Ideal.span {f.val}).restrictScalars iP).comap N.subtype
  have hproper (k :Option ↥factors) :forbidden k ≠ ⊤ := by
    cases k with
    | none =>
      intro he
      have hm: (⟨P,hPN⟩:N)∈forbidden none :=he ▸ z8t
      exact hP (congrArg Subtype.val ((zLn iP).mp hm))
    | some f =>
      have hm:f.val∈normalizedFactors P:=Multiset.mem_toFinset.mp f.property
      have hf :=prime_of_normalized_factor f.val hm
      have hfp:=dvd_of_mem_normalizedFactors hm
      obtain ⟨i,hi⟩:=bFB hf
        (((totalDegree_le_of_dvd_of_isDomain hfp hP).trans hb).trans_lt (by decide))
      obtain ⟨a,ha,hdiv,hnext⟩:=b2c hf hlow
      obtain ⟨U,hU⟩:=hdiv
      have hnd : ¬ f.val∣U:= by
        rintro ⟨V,hv⟩
        exact hnext ⟨V,by rw [hU,hv,pow_succ,mul_assoc]⟩
      have hc : ¬ f.val∣avc i a P:= by
        rw [hU]
        exact cNr i hf hi a (ha.trans (by decide)) hnd
      let G:N :=⟨avc i a P,zBO ⟨i,a,ha,rfl⟩⟩
      intro he
      have hg:G∈forbidden (some f) :=he ▸ z8t
      exact hc (Ideal.mem_span_singleton.mp hg)
  obtain ⟨Q,hQ⟩:=Submodule.exists_forall_notMem_of_forall_ne_top
    (ι:=Option ↥factors) (K:=iP) (M:=N) forbidden hproper
  have hgood:=hN Q.property
  refine ⟨Q.val,?_,?_,?_,?_,hgood.2⟩
  · exact fun hz=>hQ none ((zLn iP).mpr (Subtype.ext hz))
  · exact zf9 (fun m hm=>(hgood.1 m hm).1)
  · exact zf9 (fun m hm=>(b6f m) ▸ (hgood.1 m hm).2)
  · apply (isRelPrime_iff_no_prime_factors hP).mpr
    intro d hdP hdQ hd
    obtain ⟨f,hf,hassoc⟩:=exists_mem_normalizedFactors_of_dvd hP hd.irreducible hdP
    exact hQ (some ⟨f,Multiset.mem_toFinset.mpr hf⟩)
      (Ideal.mem_span_singleton.mpr (hassoc.dvd_iff_dvd_left.mp hdQ))
end
end P6_6_6
end
section
set_option autoImplicit true
set_option Elab.async false
namespace P6_6_6
noncomputable section
open Polynomial aR wH K1_13_7_4
open P6_6 (aPr aWz mu nu)
open scoped BigOperators
open private bsc bOE b5O from ProximityPrize.SubmissionLower.E5
private def c8q (P Q:af 3) :Submodule ao (af 3) where
  carrier := {R | Gh R aPr aWz ∧
    ∀ S:ao[X],wU P S mu→wU Q S Fw→wU R S nu}
  zero_mem' := by
    constructor
    · simp [Gh,qE]
    · intro S _ _
      change ∀ m∈(IM S 0).support,_
      simp
  add_mem' := by
    intro R T hR hT
    change Gh R _ _∧_ at hR
    change Gh T _ _∧_ at hT
    obtain ⟨⟨hRb,hRj⟩,hr⟩:=hR
    obtain ⟨⟨hTb,hTj⟩,ht⟩:=hT
    change Gh (R+T) _ _∧_
    refine ⟨⟨(MvPolynomial.totalDegree_add R T).trans (max_le hRb hTb),?_⟩,?_⟩
    · apply zf9
      intro m hm
      rcases Finset.mem_union.mp (zut hm) with hm | hm
      · exact (zZi hm).trans hRj
      · exact (zZi hm).trans hTj
    · intro S hp hq m hm
      change m∈(IM S (R+T)).support at hm
      rw [map_add] at hm
      rcases Finset.mem_union.mp (zut hm) with hm | hm
      · exact hr S hp hq m hm
      · exact ht S hp hq m hm
  smul_mem' := by
    intro a R hR
    change Gh R _ _∧_ at hR
    obtain ⟨⟨hRb,hRj⟩,hr⟩:=hR
    change Gh (a•R) _ _∧_
    have hs :a•R=MvPolynomial.C (z1z a)*R:= by
      rw [Algebra.smul_def,IsScalarTower.algebraMap_eq ao ao[X] (af 3)]
      rfl
    rw [hs]
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact (Finset.sup_mono (bOE R (z1z a))).trans hRb
    · exact (Finset.sup_mono (bOE R (z1z a))).trans hRj
    · intro S hp hq m hm
      change m∈(IM S (MvPolynomial.C (z1z a)*R)).support at hm
      rw [map_mul,IM,MvPolynomial.eval₂Hom_C] at hm
      exact hr S hp hq m (bOE _ _ hm)
private theorem dwM {P Q:af 3}
    (hpq:bbj P Q) (hp:Gh P aPr aWz)
    (hq:Gh Q aPr aWz) :
    ∃ R∈c8q P Q,∀ (q:PrimeSpectrum Lower),
      q.asIdeal∈(Ib P Q).minimalPrimes →
      localColength q (Ib P Q)<(↑ahv :ℕ∞)→fW R∉q.asIdeal:= by
  classical
  let partials (F:af 3) (d:ℕ) :Set (af 3) :=
    {D | ∃ a,EY a<d∧D =BV a F}
  let V:=Submodule.span ao (partials P 33667∪partials Q 6045)
  have hadm:V≤ c8q P Q:= by
    apply Submodule.span_le.mpr
    rintro D (⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩)
    · refine ⟨b5O a hp,?_⟩
      intro S hPS _ m hm
      exact (by omega :863≤34529-EY a).trans (cUA P S a _ hPS m hm)
    · refine ⟨b5O a hq,?_⟩
      intro S _ hQS m hm
      exact (by omega :863≤6907-EY a).trans (cUA Q S a _ hQS m hm)
  let bad := {p:Ideal Lower | p∈(Ib P Q).minimalPrimes ∧
    ∃ q:PrimeSpectrum Lower,q.asIdeal=p∧localColength q (Ib P Q)<(↑ahv :ℕ∞)}
  have hf :bad.Finite :=
    (Ib P Q).finite_minimalPrimes_of_isNoetherianRing.subset fun _ h=>h.1
  have hw : ∀ p∈bad,∃ R∈V,fW R∉p:= by
    intro p hp'
    obtain ⟨hmin,q,rfl,hsmall⟩:=hp'
    have hheight:q.asIdeal.height=2 :=aD7 hpq hmin
    by_contra! h
    have hP:afc q (fW P) 33667:= by
      exact bRE.proof q P 33667 hheight fun a ha=>h _ (zBO (Or.inl ⟨a,ha,rfl⟩))
    have hQ:afc q (fW Q) 6045:= by
      exact bRE.proof q Q 6045 hheight fun a ha=>h _ (zBO (Or.inr ⟨a,ha,rfl⟩))
    have hrange :Ideal.span (Set.range ![fW P,fW Q])=Ib P Q:= by
      simp only [Ib,zuW,zn6,Set.union_empty,
        z1f]
    have hlarge :=bsc 2 (Or.inl rfl) q ![fW P,fW Q] ![33667,6045]
      hheight (hrange ▸ hmin)
      (by simp [zzH]) (by simpa [zzH] using And.intro hP hQ)
    have hn:33667*6045=ahv := by decide
    have hnum : (∏ i:Fin 2,(![33667,6045] :Fin 2→ℕ) i)=ahv := by
      rw [Fin.prod_univ_two]
      exact hn
    rw [hnum,hrange] at hlarge
    exact (not_le_of_gt hsmall) hlarge
  obtain ⟨R,hR,havoid⟩:=d3Y V bad hf hw
  exact ⟨R,hadm hR,fun q hmin hlow=>havoid q.asIdeal ⟨hmin,q,rfl,hlow⟩⟩
theorem fWI (P Q:af 3) (hpq:bbj P Q)
    (hP:Gh P IG.b IG.j) (hQ:Gh Q IG.b IG.j) :
    ∃ R:af 3,Gh R IG.b IG.j ∧
      ∀ S:ao[X],wU P S mu→wU Q S Fw →
        bac P Q (Ud S)∨bzn P Q R (Ud S) := by
  obtain ⟨R,hR,havoid⟩:=dwM hpq hP hQ
  refine ⟨R,hR.1,?_⟩
  intro S hPS hQS
  by_cases hhigh:bac P Q (Ud S)
  · exact Or.inl hhigh
  right
  let q:=pointPrime (Ud S)
  have hRub:=hR.2 S hPS hQS
  have hp:=cb5 hPS
  have hq:=cb5 hQS
  have hr :=cb5 hRub
  have hle :asD P Q R≤q.asIdeal:=bPj.mpr
    ⟨cvd (by decide) hp,cvd (by decide) hq,
      cvd (by decide) hr⟩
  have height_three_of_le (p:PrimeSpectrum Lower)
      (hpI:asD P Q R≤p.asIdeal) (hpq' : p.asIdeal≤q.asIdeal) :
      p.asIdeal.height=3:= by
    obtain ⟨I,hI,hIp⟩:=Ideal.exists_minimalPrimes_le
      (cbc.mpr ⟨(bPj.mp hpI).1,(bPj.mp hpI).2.1⟩)
    let t:PrimeSpectrum Lower :=⟨I,hI.isPrime⟩
    have :I.IsPrime :=hI.isPrime
    have ht:t.asIdeal.height=2 :=aD7 hpq hI
    have hlow:localColength t (Ib P Q)<(↑ahv :ℕ∞) := by
      apply lt_of_not_ge
      intro h
      exact hhigh ⟨t,hI,ht,hIp.trans hpq',h,br7 hI⟩
    have hlt:t.asIdeal<p.asIdeal:= by
      apply lt_of_le_of_ne hIp
      intro heq
      apply havoid t hI hlow
      change fW R∈I
      rw [heq]
      exact (bPj.mp hpI).2.2
    have hh:=Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [ht] at hh
    exact le_antisymm (emB p) hh
  have hheight:=height_three_of_le q hle le_rfl
  have hmin:q.asIdeal∈(asD P Q R).minimalPrimes := by
    refine ⟨⟨q.isPrime,hle⟩,?_⟩
    intro I hI hIq
    let p:PrimeSpectrum Lower :=⟨I,hI.1⟩
    have :I.IsPrime :=hI.1
    have hph:=height_three_of_le p hI.2 hIq
    have heq :I=q.asIdeal:=Ideal.eq_of_le_of_height_le I hIq (by
      change q.asIdeal.height≤p.asIdeal.height
      rw [hheight,hph])
    exact heq.ge
  refine ⟨q,rfl,hmin,?_,br7 hmin⟩
  have hrange :Ideal.span (Set.range ![fW P,fW Q,fW R]) =
      asD P Q R:= by
    simp only [asD,zuW,zn6,Set.union_empty,
      z1f]
  have hlen:=bsc 3 (Or.inr rfl) q ![fW P,fW Q,fW R]
    ![mu,Fw,nu] hheight (hrange ▸ hmin) (by simp [z60])
    (by simpa [z60] using And.intro hp (And.intro hq hr))
  have hnum : (∏ i:Fin 3,(![mu,Fw,nu] :Fin 3→ℕ) i)=Ny := by
    rw [Fin.prod_univ_three]
    exact a6E
  rwa [hrange,hnum] at hlen
end
end P6_6_6
end
