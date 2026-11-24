import ProximityPrize.SubmissionLower.Zqby9gc
set_option Elab.async false
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qqW9Gbd
noncomputable section
open Polynomial
open cu (L ku)
open DP (Fg awN c69)
open P6_7_1 (Rectangle)
open scoped BigOperators
open private aAC cZb dib dc4 asU ahS cFV dPL from ProximityPrize.SubmissionLower.Z
open private cF0 from ProximityPrize.SubmissionLower.Z
private abbrev Positions (h:ℕ) (s :Rectangle) (W:ℕ) :=
  Σ q:Fin (s.B+1),Σ j:Fin (min q.val s.J+1),
    Fin (aAC h s.box W q.val j.val)×(Fin (s.z+1)×Fin (s.t+1))
private def rU {h s W} (k :Positions h s W) :asU :=
  (k.2.1.val,k.1.val-k.2.1.val,k.2.2.1.val,
    Finsupp.equivFunOnFinite.symm ![k.2.2.2.1.val,k.2.2.2.2.val])
private theorem card_positions (h:ℕ) (s :Rectangle) (W:ℕ) :
    Fintype.card (Positions h s W)=stock s*ku s.box (aAC h s.box W) := by
  simp only [Positions,stock,ku,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,
    ← Fin.sum_univ_eq_sum_range,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl
private theorem eligible {h s W} (k :Positions h s W) :
    let (j,i,a,e) :=rU k
    awN h s.box W j i a e∧e 0≤ s.z∧e 1≤ s.t:= by
  obtain ⟨q,j,a,z,t⟩:=k
  have hq:=q.isLt
  have hj:=j.isLt
  have hjq:=min_le_left q.val s.J
  have hjJ:=min_le_right q.val s.J
  have hgrade :q.val-j.val+j.val=q.val := by omega
  have hz :=z.isLt
  have ht:=t.isLt
  have hw:=(cZb h s.box W _ _ _).mp a.isLt
  let e :Fin 2 →₀ ℕ:=Finsupp.equivFunOnFinite.symm ![z.val,t.val]
  change awN h s.box W j.val (q.val-j.val) a.val e∧z.val≤ s.z∧t.val≤ s.t
  refine ⟨⟨?_,?_,?_,?_⟩,by omega,by omega⟩
  · change q.val-j.val+j.val≤ s.B
    omega
  · change j.val≤ s.J
    omega
  · rw [dc4]
    change z.val+t.val≤ s.z+s.t
    omega
  · rw [hgrade]
    exact hw
private theorem exponents_inj (h s W) :Function.Injective (rU (h:=h) (s :=s) (W:=W)) := by
  rintro ⟨q,j,a,z,t⟩ ⟨q',j',a',z',t'⟩ he
  have hj:j.val=j'.val :=congrArg (fun x :asU=>x.1) he
  have hi:q.val-j.val=q'.val-j'.val :=congrArg (fun x :asU=>x.2.1) he
  have hjq:=j.isLt.trans_le (Nat.succ_le_succ (min_le_left q.val s.J))
  have hjq' := j'.isLt.trans_le (Nat.succ_le_succ (min_le_left q'.val s.J))
  have hq:q=q' := Fin.ext (by omega)
  subst q'
  have hJ:j=j' := Fin.ext hj
  subst j'
  have hA:a=a' := Fin.ext (congrArg (fun x :asU=>x.2.2.1) he)
  have hZ:z=z' := Fin.ext (congrArg (fun x :asU=>x.2.2.2 0) he)
  have hT:t=t' := Fin.ext (congrArg (fun x :asU=>x.2.2.2 1) he)
  subst a'
  subst z'
  subst t'
  rfl
private def monomialRow {h s W} (k :Positions h s W) :rectAmbient h s W:= by
  classical
  refine ⟨ahS (rU k),?_,?_⟩
  · intro j i a e hb
    rw [cFV (rU k) (j,i,a,e),ite_eq_right]
    intro he
    have hh:=(eligible k).1
    change awN h s.box W (rU k).1 (rU k).2.1
      (rU k).2.2.1 (rU k).2.2.2 at hh
    rw [he] at hh
    exact hb hh
  · intro j i a e hb
    rw [cFV (rU k) (j,i,a,e),ite_eq_right]
    intro he
    have hh:=(eligible k).2
    change (rU k).2.2.2 0≤ s.z∧(rU k).2.2.2 1≤ s.t at hh
    rw [he] at hh
    exact hb.elim (fun hn=>(not_lt_of_ge hh.1) hn) (fun hn=>(not_lt_of_ge hh.2) hn)
private theorem ds9 (h:ℕ) (s :Rectangle) (W:ℕ) :
    stock s*ku s.box (aAC h s.box W)≤Module.finrank L (rectAmbient h s W) := by
  classical
  let read:rectAmbient h s W →ₗ[L] (Positions h s W→L) :=
    LinearMap.pi fun k=>(cF0 (rU k).1 (rU k).2.1 (rU k).2.2.1
      (rU k).2.2.2).comp (rectAmbient h s W).subtype
  have hf :read ∘ (monomialRow (h:=h) (s :=s) (W:=W))=Pi.basisFun L (Positions h s W) := by
    funext k j
    rw [Pi.basisFun_apply]
    change Fg (ahS (rU k)) (rU j).1 (rU j).2.1
      (rU j).2.2.1 (rU j).2.2.2= _
    rw [cFV]
    by_cases he :k=j
    · subst j
      simp
    · have hn:rU k≠rU j:= fun hh=>he (exponents_inj h s W hh)
      simp [hn,Ne.symm he]
  have hi:LinearIndependent L (monomialRow (h:=h) (s :=s) (W:=W)) := by
    apply LinearIndependent.of_comp read
    rw [hf]
    exact (Pi.basisFun L (Positions h s W)).linearIndependent
  have hle :rectAmbient h s W≤DP.Aw h s.box W:=inf_le_left
  let e :=dPL h s.box W
  let _:Module.Finite L (rectAmbient h s W) :=
    Module.Finite.of_injective (e.toLinearMap.comp (Submodule.inclusion hle))
      (e.injective.comp (Submodule.inclusion_injective hle))
  rw [← card_positions]
  exact hi.fintype_card_le_finrank
theorem bT9 {h:ℕ} (hhi:h≤131071) (s :Rectangle) (W:ℕ)
    (hw:c69 h s.box W) :
    stock s*ku s.box (fun q j=>W+1+j-q*(131071-h))+iL h s ≤
      Module.finrank L (rectAmbient h s W) := by
  refine le_trans ?_ (ds9 h s W)
  unfold iL ku
  simp only [Nat.mul_assoc,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro j hj
  rw [dib hhi hw (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq))
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)),Nat.mul_add]
  simp only [Rectangle.box,Nat.mul_assoc,Nat.mul_add,le_refl]
end
end qqW9Gbd
end
section
set_option autoImplicit true
namespace qbbqILc
noncomputable section
open cu (ku)
open DP (CI pW)
open Ge (Gm Exponent aQu adk kq EM residue forward)
open P6_7_1 (Rectangle)
open Polynomial
def cap (s :Rectangle) (a :Fin 2) :ℕ:=if a=0 then s.z else s.t
def Boxed {F:Type} [Field F] (s :Rectangle) (P:Gm F) :Prop :=
  ∀ j i d (e :Exponent),s.z<e 0∨s.t<e 1→aQu P j i d e=0
def eta (s :Rectangle) (q j:ℕ) :=s.B+s.J-q-min q s.J+2*j
def bbE (s :Rectangle) (u:ℕ) :=
  ku s.box fun q j=>eta s q j*(s.B-q+(u-(q-j)+1))
def localRows (s :Rectangle) (a :Fin 2) :=
  (cap s (CI a)+1)*bbE s (cap s a)
def LocalPole :Prop :=
  ∀ (F:Type) [Field F] [CharP F K1.p] (s :Rectangle),
    s.J≤ s.B→s.B<K1.p→s.B≤ s.z→s.B≤ s.t →
    ∀ (α:F) (side :Fin 2) (a b c:F),b≠0 →
    ∃ tests :Gm F →ₗ[F] (Fin (localRows s side)→F),
      ∀ P,adk s.box P→Boxed s P→tests P=0 →
        (pW ((Polynomial.X - C (algebraMap F (kq F) α))^(s.B+s.J)) :
          EM (kq F))∣forward (Polynomial.X - C α) (C (residue side a b c)) P
end
end qbbqILc
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qUlPTla
open Finset
open private sum_arithmetic from ProximityPrize.SubmissionLower.ZnaMqIa
open private ddK from ProximityPrize.SubmissionLower.H
open private sum_affine_product from ProximityPrize.SubmissionLower.Z7V3Ypa
private def headFast (h:ℤ) (l a :ℕ) :ℤ :=
  let n:ℤ:=((min 442 (2079-l) :ℕ) :ℤ)
  let x :=2079-(l:ℤ)
  let z :=2*(0x1013e9d4-2*h*a)-(131071-h)*(2078+(l:ℤ))
  let w:=2-4*h-(131071-h)
  n*(6*x*z+3*(n-1)*(x*w-z)-(n-1)*(2*n-1)*w)
private theorem head_fast_eq (h:ℤ) (l a :ℕ) :
    headFast h l a=12*(∑ q∈range 2079,∑ j∈range (min q 441+1),
      if j+l≤q then width h q j a else 0) := by
  change _=12*(∑ q∈range ((⟨0,2078,441,0⟩:cu.Shape).B+1),
    ∑ j∈range (min q (⟨0,2078,441,0⟩:cu.Shape).J+1),
      if j+l≤q then width h q j a else 0)
  rw [ddK (⟨0,2078,441,0⟩:cu.Shape)]
  change _=12*(∑ j∈range 442,∑ q∈Ico j 2079,
    if j+l≤q then width h q j a else 0)
  have cut (j:ℕ) :
      (∑ q∈Ico j 2079,if j+l≤q then width h q j a else 0) =
        ∑ q∈Ico (j+l) 2079,width h q j a := by
    rw [← sum_filter]
    congr 1
    ext q
    simp only [mem_filter,mem_Ico]
    omega
  simp_rw [cut]
  let n:=min 442 (2079-l)
  have keep :
      (∑ j∈range 442,∑ q∈Ico (j+l) 2079,width h q j a) =
        ∑ j∈range n,∑ q∈Ico (j+l) 2079,aso h q j a := by
    rw [← sum_subset (range_mono (min_le_left _ _) :range n⊆range 442)
      (f := fun j => ∑ q∈Ico (j+l) 2079,width h q j a)]
    · exact sum_congr rfl fun j _=>sum_congr rfl fun q hq=> by
        simp only [width,ite_eq_left (Or.inl (mem_Ico.mp hq).2)]
    · intro j hj hn
      have hz :2079≤j+l:= by
        simp only [mem_range,n,lt_min_iff] at hj hn
        omega
      rw [Ico_eq_empty_of_le hz,sum_empty]
  rw [keep,show (12 :ℤ)=6*2 by decide,mul_assoc,mul_sum]
  have col (j:ℕ) (hj:j<n) :
      2*(∑ q∈Ico (j+l) 2079,aso h q j a) =
        (2079-(l:ℤ)-j)*(2*(0x1013e9d4-2*h*a)-(131071-h)*(2078+(l:ℤ))+
          (2-4*h-(131071-h))*j) := by
    have hn:j+l≤2079:= by have :=(lt_min_iff.mp hj).2; omega
    rw [sum_Ico_eq_sum_range,mul_sum]
    have f (i:ℕ) :2*aso h (j+l+i) j a =
        2*aso h (j+l) j a - 2*(131071-h)*(i:ℤ) := by
      unfold aso
      push_cast
      ring
    simp_rw [f]
    rw [sum_arithmetic,Nat.cast_sub hn]
    simp only [aso,Nat.cast_add,Nat.cast_ofNat]
    ring
  rw [show (∑ j∈range n,2*(∑ q∈Ico (j+l) 2079,aso h q j a)) =
      ∑ j∈range n,((2079-(l:ℤ))+(-1 :ℤ)*j)*
        (2*(0x1013e9d4-2*h*a)-(131071-h)*(2078+(l:ℤ))+(2-4*h-(131071-h))*j) by
      refine sum_congr rfl fun j hj => ?_
      rw [col j (mem_range.mp hj)]
      ring,sum_affine_product]
  unfold headFast
  ring
private def tailFast (h:ℤ) (l a q:ℕ) :ℤ :=
  let n:ℤ:=((min 442 (min (q+1-l) (tailEnd q a)) :ℕ) :ℤ)
  6*n*(2*(0x1013e9d4-2*h*a-(131071-h)*q)+(1-2*h)*(n-1))
private theorem tail_fast_eq (h:ℤ) (l a q:ℕ) (hq:2079≤q) :
    tailFast h l a q=12*(∑ j∈range (min q 441+1),
      if j+l≤q then width h q j a else 0) := by
  let n:=min 442 (min (q+1-l) (tailEnd q a))
  have m:min q 441=441 :=min_eq_right (by omega)
  rw [m]
  have keep :
      (∑ j∈range 442,if j+l≤q then width h q j a else 0) =
        ∑ j∈range n,aso h q j a := by
    have step (j:ℕ) :
        (if j+l≤q then width h q j a else 0) =
          if j< min (q+1-l) (tailEnd q a) then aso h q j a else 0:= by
      simp only [width,not_lt_of_ge hq,false_or,lt_min_iff]
      by_cases hj:j+l≤q <;> by_cases hk :j<tailEnd q a
      all_goals have hiff :j<q+1-l↔j+l≤q:= by omega
      all_goals simp [hj,hk,hiff]
    simp_rw [step,← sum_filter]
    congr 1
    ext j
    simp [n,lt_min_iff,and_left_comm]
  rw [keep,show (12 :ℤ)=6*2 by decide,mul_assoc,mul_sum]
  have f (j:ℕ) :2*aso h q j a =
      2*(0x1013e9d4-2*h*a-(131071-h)*q)-2*(2*h-1)*(j:ℤ) := by
    unfold aso
    ring
  simp_rw [f]
  rw [sum_arithmetic]
  unfold tailFast
  ring
private def tally (f :ℕ→ℤ) :ℕ→ℤ
  | 0=>0
  | n+1=>tally f n+f n
private theorem tally_eq (f :ℕ→ℤ) (n:ℕ) :tally f n = ∑ i∈range n,f i:= by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [tally,sum_range_succ,ih]
private def fastAt (h:ℤ) (l a :ℕ) :ℤ :=
  if l≤2093 then headFast h l a+tally (fun q=>tailFast h l a (2079+q)) 15 else 0
private theorem fastAt_eq (h:ℤ) (l a :ℕ) :
    fastAt h l a=12*(∑ q∈range 2094,∑ j∈range (min q 441+1),
      if j+l≤q then width h q j a else 0) := by
  by_cases hl:l≤2093
  · rw [fastAt,ite_eq_left hl,tally_eq,head_fast_eq,
      ← sum_range_add_sum_Ico _ (by decide :2079≤2094),mul_add,sum_Ico_eq_sum_range]
    congr 1
    rw [mul_sum]
    exact sum_congr rfl fun q _=>tail_fast_eq h l a _ (Nat.le_add_right _ _)
  · rw [fastAt,ite_eq_right hl]
    symm
    apply mul_eq_zero_of_right
    apply sum_eq_zero
    intro q hq
    apply sum_eq_zero
    intro j _
    have not_le : ¬ j+l≤q:= by have :=mem_range.mp hq; omega
    rw [ite_eq_right not_le]
def a3T (h:ℤ) (U E v d:ℕ) :ℤ :=
  tally (fun a=>if stock U v (a+d)=0 then 0 else
    (stock U v (a+d) :ℤ)*fastAt h (E*(a+d)) a) 30
theorem cRJ (h:ℤ) (U E v d:ℕ) :a3T h U E v d = 12*phase h U E v d:= by
  unfold a3T phase
  rw [tally_eq,mul_sum]
  apply sum_congr rfl
  intro a _
  by_cases ha :stock U v (a+d)=0
  · simp [ha]
  · rw [ite_eq_right ha,fastAt_eq]
    ring
end qUlPTla
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qUlPTla
open Finset P6_7_1
open P1_7_6_7 (aT stripe stripe_eq)
private def poleTerm (q j:ℕ) :ℤ :=
  ((2534-q-min q 441+2*j:ℕ) :ℤ)*(2093-2*(q:ℤ)+j)
private theorem c4C (U:ℕ) :aWs (aV U)=0x784472a140:= by
  change (∑ q∈range 2094,∑ j∈range (min q 441+1),poleTerm q j).toNat= _
  have dO (l r :ℕ) (x w:aT) (hlr :l≤ r) (hr :r≤2094)
      (hx : ∀ q∈Ico l r,x.eval q=2534-(q:ℤ)-min q 441)
      (hw : ∀ q∈Ico l r,w.eval q = ↑(min q 441+1 :ℕ)) :
      stripe ⟨1,0,0⟩ x ⟨2093,-2⟩ 2 1 ⟨0,0⟩ w l r =
        360*(∑ q∈Ico l r,∑ j∈range (min q 441+1),poleTerm q j) := by
    rw [stripe_eq _ _ _ _ _ _ _ hlr (by simp [aT.eval])
      (fun q hq=> by
        rw [hw q hq]
        simpa only [aT.eval,zero_mul,add_zero] using Int.natCast_nonneg (min q 441+1))]
    congr 1
    apply sum_congr rfl
    intro q hq
    have hz : (aT.eval ⟨0,0⟩ q).toNat=0:= by simp [aT.eval]
    rw [hw q hq,hx q hq,hz]
    simp only [Y2.PG.eval,zero_mul,add_zero,one_mul,
      Int.toNat_natCast,aT.eval,Nat.Ico_zero_eq_range]
    apply sum_congr rfl
    intro j _
    have hq' := (mem_Ico.mp hq).2.trans_le hr
    have hm:q+min q 441≤2534 := by have :=min_le_right q 441; omega
    simp only [poleTerm,Nat.sub_sub,Nat.cast_add,Nat.cast_sub hm]
    push_cast
    ring
  have h₀:=dO 0 441 ⟨2534,-2⟩ ⟨1,1⟩ (by decide) (by decide)
    (fun q hq=> by
      rw [min_eq_left (mem_Ico.mp hq).2.le]
      simp only [aT.eval]; ring)
    (fun q hq=> by
      rw [min_eq_left (mem_Ico.mp hq).2.le]
      simp [aT.eval,add_comm])
  have h₁:=dO 441 2094 ⟨2093,-1⟩ ⟨442,0⟩ (by decide) le_rfl
    (fun q hq=> by rw [min_eq_right (mem_Ico.mp hq).1]; simp only [aT.eval]; ring)
    (fun q hq=> by rw [min_eq_right (mem_Ico.mp hq).1]; simp [aT.eval])
  have hov : (∑ q∈range 2094,∑ j∈range (min q 441+1),poleTerm q j) =
      (0x784472a140:ℤ) := by
    rw [← sum_range_add_sum_Ico _ (by decide :441≤2094)]
    rw [Nat.Ico_zero_eq_range] at h₀
    have c:stripe ⟨1,0,0⟩ ⟨2534,-2⟩ ⟨2093,-2⟩ 2 1 ⟨0,0⟩ ⟨1,1⟩ 0 441 +
        stripe ⟨1,0,0⟩ ⟨2093,-1⟩ ⟨2093,-2⟩ 2 1 ⟨0,0⟩ ⟨442,0⟩ 441 2094 =
        360*(0x784472a140:ℤ) :=rfl
    omega
  rw [hov]
  rfl
private theorem from_six (n c:ℕ) (h:6*n=c) (hc:c=6*0x5a9dffd40000) :
    n=0x5a9dffd40000 :=
  Nat.eq_of_mul_eq_mul_left (by decide :0<6) (h.trans hc)
private theorem node_eq (U:ℕ) :agU.ad1 (aV U).box=0x5a9dffd40000:= by
  let s :=(aV U).box
  let c:=262144*czX.a8x (s.m-2*s.J) s.J
  refine from_six (agU.ad1 s) c (czX.dei s
    (by decide :2*441≤1500) (by decide :1500+441≤2093+1)) ?_
  have h₁:s.J=441 :=rfl
  have h₀:s.m-2*s.J=618:= by
    have hm:s.m=1500:=rfl
    omega
  change 262144*czX.a8x (s.m-2*s.J) s.J= _
  rw [h₀,h₁] <;> rfl
def cost (h:ℤ) (U:ℕ) :ℤ:=((U:ℤ)+1)*60837*0x5a9dffd40000+h*0x784472a140*((U:ℤ)+60838)
private theorem Fi (h U:ℕ) : (rectDebit h (aV U) :ℤ)=cost h U:= by
  have hn:rectDebit h (aV U) =
      (U+1)*60837*agU.ad1 (aV U).box+h*aWs (aV U)*(U+60836+2) := by
    unfold rectDebit agU.ad1
    change (U+1)*60837*262144*_+_=(U+1)*60837*(262144*_)+_
    rw [Nat.mul_assoc ((U+1)*60837) 262144]
    rfl
  rw [hn,node_eq,c4C]
  simp only [cost,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
  ring
theorem reflected_debit (h U:ℕ) :
    rectDebit h {terminal with t:=U} = rectDebit h (aV U) := by
  simp only [rectDebit,aWs,aV,cu.ku,Rectangle.box]
  ring
def margin (h:ℤ) (U E v :ℕ) :ℤ :=
  60837*(a3T h U E v 0-a3T h U E v 1)-12*cost h U
theorem of_row {h U E v :ℕ} (hl:packetLo≤h) (hu:h≤packetHi)
    (he :0<E) (hc:2093/E<30∨U+1≤30*v)
    (h₀:0< margin 2350 U E v) (h₁:0< margin 2369 U E v) :
    rectDebit h (aV U)< rectGain h (aV U) 0 E v := by
  have interp:19*margin h U E v =
      (2369-(h:ℤ))*margin 2350 U E v+((h:ℤ)-2350)*margin 2369 U E v := by
    simp only [margin,cRJ]
    have e₀:=phase_interp (h:ℤ) U E v 0
    have e₁:=phase_interp (h:ℤ) U E v 1
    unfold cost
    linear_combination 730044*e₀ - 730044*e₁
  have l: (2350:ℤ)≤h:= by exact_mod_cast hl
  have r : (h:ℤ)≤2369:= by exact_mod_cast hu
  have pos :0<19*margin h U E v := by
    rw [interp]
    by_cases hh: (h:ℤ)<2369
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hh) h₀)
        (mul_nonneg (sub_nonneg.mpr l) h₁.le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr r) h₀.le)
        (mul_pos (by omega) h₁)
  have hb:=phase_bound h U E v (hu.trans (by decide :packetHi≤131071)) he hc
  apply Int.ofNat_lt.mp
  rw [gain_eq,Fi]
  simp only [margin,cRJ] at pos
  linarith only [pos,hb]
end qUlPTla
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qUlPTla
open P6_7_1
def check (E U v :ℕ) :Bool :=
  decide (0<E) && decide (2093/E<30∨U+1≤30*v) &&
    decide (0< margin 2350 U E v) && decide (0< margin 2369 U E v)
def checked :ℕ→List (ℕ×ℕ)→Prop
  | _,[]=>True
  | i,p :: ps=>check i (min terminal.z p.2) (min terminal.z p.1+1)=true ∧
      checked (i+1) ps
theorem checked_get {ps :List (ℕ×ℕ)} {n:ℕ} (hc:checked n ps)
    (i:Fin ps.length) :
    check (n+i.val) (min terminal.z (ps.get i).2) (min terminal.z (ps.get i).1+1)=true := by
  induction ps generalizing n with
  | nil=>exact Fin.elim0 i
  | cons p ps ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change check (n+0) (min terminal.z p.2) (min terminal.z p.1+1)=true
      rw [Nat.add_zero]
      exact hc.1
    · change check (n+(j.val+1)) (min terminal.z (ps.get j).2)
        (min terminal.z (ps.get j).1+1)=true
      rw [← Nat.add_assoc,Nat.add_right_comm n j.val 1]
      exact ih hc.2 j
theorem checked_append {n:ℕ} {xs ys :List (ℕ×ℕ)} (hx :checked n xs)
    (hy :checked (n+xs.length) ys) :checked n (xs++ys) := by
  induction xs generalizing n with
  | nil=>simpa only [List.length_nil,Nat.add_zero,List.nil_append] using hy
  | cons x xs ih =>
    refine ⟨hx.1,ih hx.2 ?_⟩
    rw [show n+1+xs.length=n+(x::xs).length by simp only [List.length_cons]; omega]
    exact hy
def segment (start:ℕ) :=(gw.drop start).take 25
theorem solve {h E U v :ℕ} (hl:packetLo≤h) (hu:h≤packetHi)
    (hc:check E U v=true) :rectDebit h (aV U)< rectGain h (aV U) 0 E v := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  exact of_row hl hu hc.1.1.1 hc.1.1.2 hc.1.2 hc.2
end qUlPTla
end
