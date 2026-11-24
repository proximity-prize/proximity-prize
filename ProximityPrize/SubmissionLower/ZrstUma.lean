import ProximityPrize.SubmissionLower.DR
import ProximityPrize.SubmissionLower.ZS1sWBc
set_option Elab.async false
set_option autoImplicit true
namespace qKVdmob
open qHde8fc
open fP (Ew cF xH)
open scoped BigOperators
open private R0 from ProximityPrize.SubmissionLower.DR
noncomputable section
private def exp (a b c f :ℕ) :Exponent:=Finsupp.equivFunOnFinite.symm ![a,b,c,f]
private theorem adz {e v :aY}
    (h:iG (cP (aD e.val)) (e.val 2) (e.val 3)
      (cP (aD v.val)) (v.val 2) (v.val 3)) :
    dZ v<dZ e := by
  have hv :=v.property
  have he :=e.property
  rw [cF] at hv he
  unfold iG at h
  unfold dZ
  omega
private theorem i7 {cut:ℕ} (m:gU cut) :
    cut≤ m.val 1+2*m.val 2 + 3*m.val 3 ∧
      m.val 1+2*m.val 2 + 3*m.val 3≤56:= by
  obtain ⟨_,hl,hu,_⟩:=m.property
  rw [xH] at hl hu
  exact ⟨by exact_mod_cast hl,by exact_mod_cast hu⟩
private theorem a2O {cut:ℕ} {m n:gU cut}
    (hb:m.val 1=n.val 1) (hc:m.val 2=n.val 2) (hf :m.val 3=n.val 3) :
    m=n:= by
  have hm:=m.property.1
  have hn:=n.property.1
  rw [cF] at hm hn
  apply Subtype.ext
  apply Finsupp.ext
  intro j
  fin_cases j
  · change m.val 0=n.val 0
    omega
  · exact hb
  · exact hc
  · exact hf
private theorem iN {cut b c f :ℕ} (m:gU cut)
    (h:c< m.val 2∨f< m.val 3) :cE cut (b,c,f) m=0:= by
  rcases h with h | h
  · simp [cE,yv,Nat.choose_eq_zero_of_lt h]
  · simp [cE,yv,Nat.choose_eq_zero_of_lt h]
private def width (cut j k :ℕ) :ℕ:=57 - max cut (2*j+3*k)
private def BS (cut j k :ℕ) (htop:k≤16)
    (i:Fin (width cut j k)) :gU cut:= by
  let b:=56-(2*j+3*k) - i.val
  have hpos :=i.isLt
  unfold width at hpos
  refine ⟨exp (56-(b+j+k)) b j k,?_⟩
  simp only [Ew,cF,xH]
  change 56-(b+j+k)+b+j+k=56 ∧
    (cut:ℤ)≤(b+2*j+3*k :ℕ) ∧
    ((b+2*j+3*k :ℕ) :ℤ)≤56∧k≤16
  constructor
  · dsimp only [b]
    omega
  · refine ⟨?_,?_,htop⟩ <;> dsimp only [b] <;> omega
private theorem SP (cut j k :ℕ) (htop:k≤16)
    (i:Fin (width cut j k)) :
    (BS cut j k htop i).val 1=56-(2*j+3*k) - i.val :=rfl
private theorem Ir (cut j k :ℕ) (htop:k≤16)
    (i:Fin (width cut j k)) :
    (BS cut j k htop i).val 2=j:=rfl
private theorem GX (cut j k :ℕ) (htop:k≤16)
    (i:Fin (width cut j k)) :
    (BS cut j k htop i).val 3=k :=rfl
private theorem auE {cut j k :ℕ} (htop:k≤16)
    (m:gU cut) (h₂:m.val 2=j) (h₃:m.val 3=k) :
    ∃ i,BS cut j k htop i=m:= by
  obtain ⟨hlo,hhi⟩:=i7 m
  rw [h₂,h₃] at hlo hhi
  let i:Fin (width cut j k) :=⟨56-(m.val 1+2*j+3*k),by
    unfold width
    omega⟩
  refine ⟨i,a2O ?_ h₂.symm h₃.symm⟩
  rw [SP]
  dsimp only [i]
  omega
private def R7 (e :aY) (hr :cP (aD e.val)≤112)
    (j k i:ℕ) (h:iG (cP (aD e.val)) (e.val 2) (e.val 3)
      (56+3*i+j+2*k) j k) :iw e := by
  let u:aY:=⟨exp i (56 - j - k - i) j k,by
    rw [cF]
    change i+(56 - j - k - i)+j+k=56
    unfold iG at h
    omega⟩
  refine ⟨u,adz ?_⟩
  rw [nG u]
  exact h
private abbrev jZ (e :aY) (cut:ℕ) :=
  Submodule.span Ground (Set.range fun v :iw e=>cE cut (aD v.val.val))
private theorem singleton_mem (e :aY) (hr :cP (aD e.val)≤112)
    (cut:ℕ) (m:gU cut) (hm:b8 e cut (m.val 2) (m.val 3)) :
    Pi.single m (1 :Ground)∈jZ e cut:= by
  classical
  let S:=jZ e cut
  let key (m:gU cut) :=m.val 2+m.val 3
  have hsingle (n:ℕ) : ∀ m:gU cut,key m=n →
      b8 e cut (m.val 2) (m.val 3)→Pi.single m (1 :Ground)∈S:= by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m hm hcovered
      let j:=m.val 2
      let k :=m.val 3
      obtain ⟨_,hhi⟩:=i7 m
      have htop:=m.property.2.2.2
      have hjk :2*j+3*k≤56:= by dsimp only [j,k]; omega
      have hi_cost (i:Fin (width cut j k)) :
          iG (cP (aD e.val)) (e.val 2) (e.val 3)
            (56+3*i.val+j+2*k) j k := by
        have hi:=i.isLt
        unfold width at hi
        change Lr _ cut _ _ j k at hcovered
        unfold Lr iG at hcovered
        unfold iG
        omega
      let atCol:=BS cut j k htop
      let v (i:Fin (width cut j k)) :iw e :=R7 e hr j k i.val (hi_cost i)
      have hv (i:Fin (width cut j k)) :
          aD (v i).val.val=(56 - j - k - i.val,j,k) :=rfl
      let target (i:Fin (width cut j k)) :Ground :=
        Pi.single (M:= fun _:gU cut=>Ground) m 1 (atCol i)
      obtain ⟨coef,hcoef⟩:=SX (56 - j - k) (56-(2*j+3*k))
        (width cut j k) (by omega) (by omega) (by unfold width; omega) target
      let g:gU cut→Ground :=
        ∑ i:Fin (width cut j k),coef i•cE cut (aD (v i).val.val)
      have hg:g∈S:= by
        apply Submodule.sum_mem
        intro i _
        exact S.smul_mem _ (Submodule.subset_span ⟨v i,rfl⟩)
      have hbox (z :gU cut) (hz :j<z.val 2∨k<z.val 3) :g z=0:= by
        simp only [g,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hv]
        apply Finset.sum_eq_zero
        intro i _
        rw [iN z hz,mul_zero]
      have hfit (z :gU cut) (h₂:z.val 2=j) (h₃:z.val 3=k) :
          g z=Pi.single (M:= fun _:gU cut=>Ground) m 1 z := by
        obtain ⟨i,hi⟩:=auE htop z h₂ h₃
        subst z
        change g (atCol i)=target i
        rw [← hcoef i]
        simp only [g,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hv,
          cE,yv,atCol,SP,Ir,GX,
          Nat.choose_self,Nat.cast_one,mul_one]
      have hrest:g-Pi.single m (1 :Ground)∈S:= by
        apply R0
        intro z hz
        have hsmall:z.val 2≤j∧z.val 3≤k := by
          by_contra! ho
          have hne :z≠m:= by
            rintro rfl
            dsimp [j,k] at ho
            omega
          have hor :j<z.val 2∨k<z.val 3:= by omega
          exact hz (by rw [Pi.sub_apply,hbox z hor,Pi.single_eq_of_ne hne,sub_zero])
        have hlt:key z<n:= by
          by_contra! hle
          dsimp only [key] at hle hm
          have hmatch :z.val 2=j∧z.val 3=k := by dsimp only [j,k] at hsmall ⊢; omega
          exact hz (by rw [Pi.sub_apply,hfit z hmatch.1 hmatch.2,sub_self])
        have hzcovered:b8 e cut (z.val 2) (z.val 3) := by
          unfold b8 Lr iG at *
          change z.val 2≤ m.val 2∧z.val 3≤ m.val 3 at hsmall
          omega
        exact ih _ hlt z rfl hzcovered
      simpa only [sub_sub_cancel] using S.sub_mem hg hrest
  exact hsingle _ m rfl hm
theorem amN (e :aY) (hr :cP (aD e.val)≤112)
    (cut:ℕ) (h:fG e cut) :
    cE cut (aD e.val) ∈
      Submodule.span Ground (Set.range fun v :iw e =>
        cE cut (aD v.val.val)) := by
  classical
  let S:=jZ e cut
  let L: (gU cut→Ground) →ₗ[Ground] (gP e cut→Ground) :=
    LinearMap.pi fun m=>LinearMap.proj m.val
  have hspan:Submodule.span Ground (Set.range fun v :iw e =>
      cZ e cut (aD v.val.val))≤S.map L:= by
    apply Submodule.span_le.mpr
    rintro _ ⟨v,rfl⟩
    exact ⟨_,Submodule.subset_span (Set.mem_range_self v),rfl⟩
  obtain ⟨w,hw,hm⟩:=hspan h
  have hrest:cE cut (aD e.val) - w∈S:= by
    apply R0
    intro m hn
    apply singleton_mem e hr
    by_contra hcovered
    have hm' := congrFun hm (⟨m,hcovered⟩:gP e cut)
    change w m=cE cut (aD e.val) m at hm'
    exact hn (by rw [Pi.sub_apply,hm',sub_self])
  simpa only [sub_add_cancel] using S.add_mem hrest hw
end
end qKVdmob
