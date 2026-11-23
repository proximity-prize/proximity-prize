import ProximityPrize.SubmissionLower.ZlfuKwd
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qMNQHHc
open P5_7 (midAgreement)
open qlc9qed
open aR (ao)
open jA Polynomial
open scoped BigOperators
open private exponent exponent_none exponent_zero bpQ d5n coordinate from ProximityPrize.SubmissionLower.B9
open private sum_coeffs from ProximityPrize.SubmissionLower.ZTFKldb
noncomputable section
private def start (b:Bank) :ℕ:=b.m*midAgreement - 131071*b.box.b
private theorem start_eq (b:Bank) :start b+131071*b.box.b=b.cut+1 := by
  cases b <;> decide
private theorem box_bounds (b:Bank) :
    2*b.box.t≤b.box.j∧b.box.j≤b.box.b∧b.U≤70000:= by
  cases b <;> decide
private def width (b:Bank) (h k j d:ℕ) :ℕ :=
  start b+131071*d+j+2*k+(b.box.j+d)*h
private abbrev Lh (b:Bank) (h:ℕ) :=
  Σ k :Fin (b.box.t+1),Σ j:Fin (b.box.j-2*k.val+1),
    Σ d:Fin (b.box.b-k.val-j.val+1),Fin (width b h k j d)×Fin (b.U+1)
private def Ac {b h} (c:Lh b h) :mA →₀ ℕ :=
  exponent c.2.2.2.2.val (b.box.b-c.1.val-c.2.1.val-c.2.2.1.val)
    c.2.1.val c.1.val
private def auD {b h} (c:Lh b h) :ℕ:=c.2.2.2.1.val
private def column {b h} (c:Lh b h) :jK :=
  MvPolynomial.monomial (Ac c) (Polynomial.monomial (auD c) 1)
private theorem bYf (b:Bank) (h:ℕ) :
    Function.Injective (fun c:Lh b h=>(Ac c,auD c)) := by
  rintro ⟨k,j,d,x,u⟩ ⟨k',j',d',x',u'⟩ he
  have hk :=congrArg (fun p: (mA →₀ ℕ)×ℕ=>p.1 (some 2)) he
  have hj:=congrArg (fun p: (mA →₀ ℕ)×ℕ=>p.1 (some 1)) he
  have hd:=congrArg (fun p: (mA →₀ ℕ)×ℕ=>p.1 (some 0)) he
  have hu:=congrArg (fun p: (mA →₀ ℕ)×ℕ=>p.1 none) he
  have hx :=congrArg Prod.snd he
  simp only [Ac,auD,d5n,bpQ,exponent_zero,exponent_none] at *
  have hkk :k=k' := Fin.ext hk
  subst k'
  have hjj:j=j' := Fin.ext hj
  subst j'
  have hd₀:=d.isLt
  have hd₁:=d'.isLt
  have hdd:d=d' := Fin.ext (by omega)
  subst d'
  have hxx :x=x' := Fin.ext hx
  have huu:u=u' := Fin.ext hu
  subst x'
  subst u'
  rfl
private theorem bDn {b h} (c:Lh b h) (e :mA →₀ ℕ) (x :ℕ) :
    coordinate e x (column c)=if Ac c=e∧auD c=x then 1 else 0:= by
  classical
  change ((column c).coeff e).coeff x= _
  by_cases he :Ac c=e <;> simp [column,he,Polynomial.coeff_monomial]
private theorem cGZ (b:Bank) (h:ℕ) :
    LinearIndependent ao (column (b:=b) (h:=h)) := by
  classical
  let L:jK →ₗ[ao] (Lh b h→ao) :=
    LinearMap.pi (fun c:Lh b h=>coordinate (Ac c) (auD c))
  apply LinearIndependent.of_comp L
  have he :L ∘ column=(Pi.basisFun ao (Lh b h) :Lh b h→Lh b h→ao) := by
    funext c d
    rw [Function.comp_apply,Pi.basisFun_apply,Pi.single_apply]
    change coordinate (Ac d) (auD d) (column c)= _
    simp only [bDn,← Prod.mk.injEq,(bYf b h).eq_iff,eq_comm]
  rw [he]
  exact (Pi.basisFun ao (Lh b h)).linearIndependent
private theorem b6S (a :mA →₀ ℕ) (w:Fin 3→ℕ) :
    Finsupp.weight (fun i:mA=>i.elim 0 w) a =
      w 0*a (some 0)+w 1*a (some 1)+w 2*a (some 2) := by
  simp only [Finsupp.weight_apply,smul_eq_mul]
  rw [← sum_coeffs a w]
  congr 1
  funext i n
  cases i <;> simp [Nat.mul_comm]
private theorem column_mem {b h} (c:Lh b h) :column c∈Aw b h b.cut:= by
  classical
  have hs (a :mA →₀ ℕ) (ha :a∈(column c).support) :a=Ac c :=
    Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha)
  obtain ⟨k,j,d,x,u⟩:=c
  obtain ⟨hTJ,hJB,hU⟩:=box_bounds b
  have hk :=k.isLt
  have hj:=j.isLt
  have hd:=d.isLt
  have hu:=u.isLt
  let i:=b.box.b - k.val - j.val - d.val
  have hgrade :i+j.val+k.val+d.val=b.box.b:= by dsimp [i]; omega
  have hindex :j.val+2*k.val≤b.box.j:= by omega
  have hw :
      (131071+h)*i+(131071+h-1)*j.val+(131071+h-2)*k.val +
        (j.val+2*k.val)+131071*d.val+d.val*h =
      131071*b.box.b+b.box.b*h:= by
    have h1 :131071+h-1+1=131071+h:= by omega
    have h2 :131071+h-2+2=131071+h:= by omega
    calc
      _=(131071+h)*i+(131071+h-1+1)*j.val+(131071+h-2+2)*k.val +
          (131071+h)*d.val := by ring
      _ = _:= by rw [h1,h2,← Nat.mul_add,← Nat.mul_add,← Nat.mul_add,hgrade,
        Nat.add_mul,Nat.mul_comm h]
  refine mem_ambient.mpr ⟨⟨?_,?_,?_,?_⟩,?_,?_⟩
  · apply Finset.sup_le
    intro a ha
    rw [hs a ha,b6S]
    simp only [Ac,exponent_zero,bpQ,d5n,one_mul]
    change i+j.val+k.val≤b.box.b
    omega
  · apply Finset.sup_le
    intro a ha
    rw [hs a ha,b6S]
    simpa only [Ac,exponent_zero,bpQ,d5n,Fin.val_zero,
      Fin.val_one,Fin.val_two,zero_mul,one_mul,zero_add] using hindex
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro a ha
    rw [hs a ha,Ac,d5n]
    omega
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro a ha
    rw [hs a ha,Ac,exponent_none]
    omega
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro a ha
    rw [hs a ha,Ac,exponent_none]
    omega
  · intro a ha
    rw [hs a ha,sum_coeffs,column,MvPolynomial.coeff_monomial,ite_eq_left rfl,
      Polynomial.natDegree_monomial_eq _ one_ne_zero]
    change x.val+((131071+h)*i+(131071+h-1)*j.val+(131071+h-2)*k.val)≤_
    have hx :x.val<start b+131071*d.val+j.val+2*k.val +
        (b.box.j*h+d.val*h) := by
      simpa only [width,Nat.add_mul] using x.isLt
    rw [Nat.add_mul b.box.b b.box.j h]
    have hstart:=start_eq b
    omega
private theorem finite_ambient (b:Bank) (h:ℕ) :Module.Finite ao (Aw b h b.cut) := by
  classical
  let V:=Aw b h b.cut
  let T:=b.cut+(b.box.b+b.box.j)*h
  let N :=max b.box.b b.U + 1
  let E :=mA→Fin N
  let f :V →ₗ[ao] ((E×Fin (T+1))→ao) :=LinearMap.pi fun p =>
    (coordinate (Finsupp.equivFunOnFinite.symm (fun i=>(p.1 i).val)) p.2).comp V.subtype
  have hzero (Q:V) (hz :f Q=0) :Q=0:= by
    obtain ⟨F,hF⟩:= Q
    obtain ⟨hcap,hU,hcut⟩:=mem_ambient.mp hF
    apply Subtype.ext
    change F=0
    apply MvPolynomial.ext
    intro a
    change F.coeff a=0
    by_contra hne
    have ha :=MvPolynomial.mem_support_iff.mpr hne
    have hd: (F.coeff a).natDegree≤T:=(Nat.le_add_right ..).trans (hcut a ha)
    have ht:=(MvPolynomial.le_weightedTotalDegree (fun i:mA=>i.elim 0 (fun _=>1))
      ha).trans hcap.1
    rw [b6S] at ht
    simp only [one_mul] at ht
    have he (i:mA) :a i<N := by
      dsimp [N]
      cases i with
      | none=>have :=(MvPolynomial.le_degreeOf_of_mem_support none ha).trans hU; omega
      | some i =>
        fin_cases i
        · change a (some 0)<_; omega
        · change a (some 1)<_; omega
        · change a (some 2)<_; omega
    let e :E := fun i=>⟨a i,he i⟩
    apply hne
    ext n
    rw [Polynomial.coeff_zero]
    by_cases hn:n<T+1
    · have hv :=congrFun hz (e,⟨n,hn⟩)
      change (F.coeff (Finsupp.equivFunOnFinite.symm (fun i=>(e i).val))).coeff n=0 at hv
      have heq :Finsupp.equivFunOnFinite.symm (fun i=>(e i).val)=a :=
        Finsupp.equivFunOnFinite.symm_apply_apply a
      rwa [heq] at hv
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  apply Module.Finite.of_injective f
  intro Q R he
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub,he,sub_self]
open Finset
private theorem bw6 (a s :ℤ) (n:ℕ) :
    2*(∑ i∈range n,(a+s*(i:ℤ)))=n*(2*a+s*((n:ℤ)-1)) := by
  induction n with
  | zero=>simp
  | succ n ih=>rw [sum_range_succ,mul_add,ih,Nat.cast_succ]; ring
private def integral24 (f :ℤ→ℤ) (n:ℤ) :ℤ :=
  24*n*f 0+12*n*(n-1)*(f 1-f 0)+4*n*(n-1)*(n-2)*(f 2-2*f 1+f 0) +
    n*(n-1)*(n-2)*(n-3)*(f 3-3*f 2+3*f 1-f 0)
private theorem sum_poly (f :ℤ→ℤ)
    (hf : ∀ i:ℤ,6*f i=6*f 0+6*i*(f 1-f 0) +
      3*i*(i-1)*(f 2-2*f 1+f 0)+i*(i-1)*(i-2)*(f 3-3*f 2+3*f 1-f 0))
    (n:ℕ) :24*(∑ i∈range n,f i)=integral24 f n:= by
  induction n with
  | zero=>simp [integral24]
  | succ n ih =>
    rw [sum_range_succ,mul_add,ih,Nat.cast_succ]
    unfold integral24
    linear_combination 4*hf (n:ℤ)
private def row (B a s k j:ℤ) :ℤ :=
  (B+1-k-j)*(2*(a+j+2*k)+s*(B-k-j))
private def slice (B J a s k :ℤ) :ℤ :=
  integral24 (row B a s k) (J+1-2*k)
private theorem width_count (b:Bank) (h:ℕ) :
    (∑ k∈range (b.box.t+1),∑ j∈range (b.box.j-2*k+1),
      ∑ d∈range (b.box.b-k-j+1),width b h k j d) =
      b.az0+b.basePole*h:= by
  let B:=b.box.b
  let J:=b.box.j
  let a :ℤ:=(start b:ℤ)+J*(h:ℤ)
  let s :ℤ:=131071+(h:ℤ)
  have hr (k :ℕ) (hk :k∈range (b.box.t+1)) :
      48*(∑ j∈range (J-2*k+1),∑ d∈range (B-k-j+1),
        (width b h k j d:ℤ))=slice B J a s k := by
    have hk' := mem_range.mp hk
    obtain ⟨hTJ,hJB,_⟩:=box_bounds b
    change 2*b.box.t≤J at hTJ
    change J≤B at hJB
    have hkJ:2*k≤J:= by omega
    rw [show (48:ℤ)=24*2 by decide,mul_assoc,mul_sum]
    have hj (j:ℕ) (hj:j∈range (J-2*k+1)) :
        2*(∑ d∈range (B-k-j+1),(width b h k j d:ℤ))=row B a s k j:= by
      have hj' := mem_range.mp hj
      have hkB:k≤B:= by omega
      have hjB:j≤B-k := by omega
      have hw (d:ℕ) : (width b h k j d:ℤ)=a+j+2*k+s*d:= by
        simp only [width,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
        dsimp [a,s,J]
        ring
      simp only [hw]
      rw [bw6,row,Nat.cast_add,Nat.cast_one,Nat.cast_sub hjB,Nat.cast_sub hkB]
      ring
    rw [sum_congr rfl hj,sum_poly (row B a s k) (by intro i; unfold row; ring),slice]
    rw [Nat.cast_add,Nat.cast_one,Nat.cast_sub hkJ,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have hsum :
      1152*(∑ k∈range (b.box.t+1),∑ j∈range (J-2*k+1),
        ∑ d∈range (B-k-j+1),(width b h k j d:ℤ)) =
      integral24 (slice B J a s) (b.box.t+1 :ℕ) := by
    rw [show (1152:ℤ)=24*48 by decide,mul_assoc,mul_sum,sum_congr rfl hr]
    exact sum_poly (slice B J a s) (by intro i; unfold slice integral24 row; ring) _
  have hc:integral24 (slice B J a s) (b.box.t+1 :ℕ) =
      1152*((b.az0:ℤ)+b.basePole*(h:ℤ)) := by
    cases b <;>
      simp only [a,s,B,J,start,Bank.m,Bank.box,Bank.az0,Bank.basePole,
        Nat.cast_sub (show 131071*87≤64*midAgreement by decide),
        Nat.cast_sub (show 131071*164≤120*midAgreement by decide),Nat.cast_add,
        Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] <;>
      unfold integral24 slice integral24 row <;> ring
  rw [hc] at hsum
  exact_mod_cast (show (∑ k∈range (b.box.t+1),∑ j∈range (J-2*k+1),
    ∑ d∈range (B-k-j+1),(width b h k j d:ℤ)) =
      (b.az0:ℤ)+b.basePole*(h:ℤ) by omega)
private theorem column_card (b:Bank) (h:ℕ) :
    Fintype.card (Lh b h)=b.ambientCount h:= by
  simp only [Lh,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,
    Nat.mul_comm _ (b.U+1),← Finset.mul_sum]
  unfold Bank.ambientCount
  congr 1
  calc
    _ = ∑ k∈range (b.box.t+1),∑ j∈range (b.box.j-2*k+1),
        ∑ d∈range (b.box.b-k-j+1),width b h k j d:= by
      rw [← Fin.sum_univ_eq_sum_range]
      refine sum_congr rfl fun k _ => ?_
      rw [← Fin.sum_univ_eq_sum_range]
      refine sum_congr rfl fun j _ => ?_
      rw [← Fin.sum_univ_eq_sum_range]
    _ = _:=width_count b h
end
end qMNQHHc
