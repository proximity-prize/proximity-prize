import ProximityPrize.SubmissionLower.S
set_option Elab.async false
set_option autoImplicit true
section
namespace aw8
open K1 aR jA NR
open scoped BigOperators Polynomial
noncomputable section
set_option backward.isDefEq.respectTransparency false
private abbrev Lh (b:Bank) (h:ℕ) :=
 Σ q:Fin (b.box.b+1),Σ k :Fin (min q.val 1150+1),
   Σ l:Fin (min (q.val - k.val) (2300 - 2*k.val)+1),
     Fin (width b h q.val k.val l.val)×Fin 70001
private def exponent (u i l k :ℕ) :mA →₀ ℕ :=
 Finsupp.equivFunOnFinite.symm (fun j=>j.elim u (![i,l,k] ·))
@[simp] private theorem exponent_none (u i l k :ℕ) :exponent u i l k none=u:= by
  simp [exponent]
@[simp] private theorem exponent_zero (u i l k :ℕ) :exponent u i l k (some 0)=i:= by
  simp [exponent]
@[simp] private theorem bpQ (u i l k :ℕ) :exponent u i l k (some 1)=l:= by
  simp [exponent]
@[simp] private theorem d5n (u i l k :ℕ) :exponent u i l k (some 2)=k := by
  simp [exponent]
private def Ac {b:Bank} {h:ℕ} (c:Lh b h) :mA →₀ ℕ :=
 exponent c.2.2.2.2.val (c.1.val - c.2.1.val - c.2.2.1.val) c.2.2.1.val c.2.1.val
private def auD {b:Bank} {h:ℕ} (c:Lh b h) :ℕ:=c.2.2.2.1.val
private theorem bYf (b:Bank) (h:ℕ) :
  Function.Injective (fun c:Lh b h=>(Ac c,auD c)) := by
 rintro ⟨q,k,l,x,u⟩ ⟨q',k',l',x',u'⟩ he
 have he₀:=congrArg (fun p: (mA →₀ ℕ)×ℕ=>p.1 (some 0)) he
 have he₁:=congrArg (fun p: (mA →₀ ℕ)×ℕ=>p.1 (some 1)) he
 have he₂:=congrArg (fun p: (mA →₀ ℕ)×ℕ=>p.1 (some 2)) he
 have heu:=congrArg (fun p: (mA →₀ ℕ)×ℕ=>p.1 none) he
 have hex :=congrArg Prod.snd he
 simp only [Ac,auD,exponent_zero,bpQ,d5n,exponent_none] at *
 have hk :=k.isLt
 have hl:=l.isLt
 have hk' := k'.isLt
 have hl' := l'.isLt
 simp only [Nat.lt_succ_iff,le_min_iff] at hk hl hk' hl'
 have hq:q=q' := Fin.ext (by omega)
 subst q'
 have hkk :k=k' := Fin.ext he₂
 subst k'
 have hll:l=l' := Fin.ext he₁
 subst l'
 have hxx :x=x' := Fin.ext hex
 have huu:u=u' := Fin.ext heu
 subst x'
 subst u'
 rfl
private def coordinate (e :mA →₀ ℕ) (x :ℕ) :jK →ₗ[ao] ao :=
 (Polynomial.lcoeff ao x).comp ((MvPolynomial.lcoeff ao[X] e).restrictScalars ao)
private def column {b:Bank} {h:ℕ} (c:Lh b h) :jK :=
 MvPolynomial.monomial (Ac c) (Polynomial.monomial (auD c) 1)
private theorem bDn {b:Bank} {h:ℕ} (c:Lh b h)
  (e :mA →₀ ℕ) (x :ℕ) :
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
private def space (b:Bank) (h:ℕ) :Submodule ao jK :=
 Submodule.span ao (Set.range (column (b:=b) (h:=h)))
private theorem eFJ {b:Bank} {h:ℕ} {F:jK}
  (hF:F∈space b h) {e :mA →₀ ℕ} {x :ℕ} (hne : (F.coeff e).coeff x≠0) :
  ∃ c:Lh b h,Ac c=e∧auD c=x := by
 classical
 by_contra! hn
 have hle :space b h≤LinearMap.ker (coordinate e x) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨c,rfl⟩
  change coordinate e x (column c)=0
  rw [bDn,ite_eq_right]
  exact fun hc=>(hn c hc.1 hc.2).elim
 exact hne (LinearMap.mem_ker.mp (hle hF))
private theorem i7 {b:Bank} {h:ℕ} (c:Lh b h) :
    let e :=Ac c
    Finsupp.weight (fun i:mA=>i.elim 0 (fun _=>1)) e≤b.box.b ∧
    Finsupp.weight (fun i:mA=>i.elim 0 Fin.val) e≤b.box.j ∧
    e (some 2)≤b.box.t∧e none≤70000 ∧
    auD c+e.sum (fun i n=>i.elim 0 (fun j=>(131071+h - j.val)*n)) ≤
      b.cut+(b.box.b+b.box.j)*h:= by
  rcases c with ⟨q,k,l,x,u⟩
  have hq:=q.isLt
  have hk :=k.isLt
  have hl:=l.isLt
  have hx :=x.isLt
  have hu:=u.isLt
  simp only [Nat.lt_succ_iff,le_min_iff] at hq hk hl
  have hs :q.val - k.val-l.val+l.val+k.val=q.val := by omega
  have hi:l.val+2*k.val≤2300:= by omega
  have hraw:aEw b+131071*b.box.b=b.cut+1 := by
    unfold aEw
    have :=bZs b
    omega
  have hcredit : (2300+(b.box.b - q.val))*h+h*q.val=(b.box.b+2300)*h:= by
    rw [mul_comm h q.val,← Nat.add_mul]
    congr 1
    omega
  have hweight :
      (131071+h - 0)*(q.val - k.val-l.val) +
        (131071+h - 1)*l.val+(131071+h - 2)*k.val+(l.val+2*k.val) =
      131071*q.val+h*q.val := by
    have h₁:131071+h - 1+1=131071+h:= by omega
    have h₂:131071+h - 2+2=131071+h:= by omega
    calc
      _=(131071+h)*(q.val - k.val-l.val) +
          (131071+h - 1+1)*l.val+(131071+h - 2+2)*k.val := by
        simp only [Nat.sub_zero]
        ring
      _ = _:= by rw [h₁,h₂,← Nat.mul_add,← Nat.mul_add,hs,Nat.add_mul]
  have hsum :
      (exponent u.val (q.val - k.val-l.val) l.val k.val).sum
        (fun i n=>i.elim 0 (fun j=>(131071+h - j.val)*n)) =
      (131071+h - 0)*(q.val - k.val-l.val) +
        (131071+h - 1)*l.val+(131071+h - 2)*k.val := by
    rw [Finsupp.sum_fintype _ _ (fun i=> by cases i <;> simp),
      Fintype.sum_option,Fin.sum_univ_three]
    simp
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [Finsupp.weight_apply,Finsupp.sum_fintype,Fintype.sum_option,Fin.sum_univ_succ,
      Ac,smul_eq_mul,← Nat.add_assoc,hs] using hq
  · simpa [Finsupp.weight_apply,Finsupp.sum_fintype,Fintype.sum_option,Fin.sum_univ_succ,
      Ac,smul_eq_mul,Nat.mul_comm] using hi
  · simpa [Ac] using hk.2
  · simpa [Ac] using Nat.le_of_lt_succ hu
  · change x.val+(exponent u.val (q.val - k.val-l.val) l.val k.val).sum
      (fun i n=>i.elim 0 (fun j=>(131071+h - j.val)*n)) ≤
        b.cut+(b.box.b+b.box.j)*h
    rw [hsum,a1U]
    change x.val<width b h q.val k.val l.val at hx
    unfold width at hx
    omega
private theorem deR (b:Bank) (h:ℕ) (F:jK) (hF:F∈space b h) :
   Jn b.box F∧ahb h (b.cut+(b.box.b+b.box.j)*h) F:= by
 have he (e :mA →₀ ℕ) (hm:e∈F.support) :
    ∃ c:Lh b h,Ac c=e∧auD c=(F.coeff e).natDegree := by
   exact eFJ hF (by
    rw [Polynomial.coeff_natDegree,Polynomial.leadingCoeff_ne_zero]
    exact MvPolynomial.mem_support_iff.mp hm)
 refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
 · apply Finset.sup_le
   intro e hm
   obtain ⟨c,rfl,_⟩:=he e hm
   exact (i7 c).1
 · apply Finset.sup_le
   intro e hm
   obtain ⟨c,rfl,_⟩:=he e hm
   exact (i7 c).2.1
 · apply MvPolynomial.degreeOf_le_iff.mpr
   intro e hm
   obtain ⟨c,rfl,_⟩:=he e hm
   exact (i7 c).2.2.1
 · apply MvPolynomial.degreeOf_le_iff.mpr
   intro e hm
   obtain ⟨c,rfl,_⟩:=he e hm
   exact (i7 c).2.2.2.1
 · intro e hm
   obtain ⟨c,rfl,hx⟩:=he e hm
   rw [← hx]
   exact (i7 c).2.2.2.2
end
end aw8
end
