import ProximityPrize.SubmissionLower.B0
import ProximityPrize.SubmissionLower.ZkYlUGe
import ProximityPrize.SubmissionLower.Z3vxfLe
import ProximityPrize.SubmissionLower.Z3gZttb
set_option Elab.async false
section
set_option autoImplicit true
namespace qzVXMPd
open qwzqCne MvPolynomial
open GN (Interpolant ord weights b9)
open fP (m9 oG)
noncomputable section
abbrev cost (e :aY) :ℕ:=cP (aD e.val)
theorem nG (e :aY) :cost e=54+ord e.val := by
  rw [cost,Sj,oG,ord]
abbrev jZ (e :aY) (cut:ℕ) :Submodule Ground (gU cut→Ground) :=
  Submodule.span Ground (Set.range fun v :iw e=>cE cut (aD v.val.val))
def Md (m:Exponent) :Prop :=m.weight m9≤56∧m 0≤16
abbrev Bounded (d:ℕ) :=restrictWeightedDegree (R:=Ground) weights d
def Ak (e :aY) (P:Interpolant) :Prop :=
  b9 e.val P≠0 ∧
    ∀ v :aY,Md v.val→dZ e<dZ v→b9 v.val P=0
def cutBudget (e :aY) :ℕ:=3*(56 - ord e.val)+2*e.val 0+e.val 2/2
theorem abJ (m:Exponent) :Md m↔ord m≤56∧m 0≤16:= by
  rw [Md,oG,ord]
end
end qzVXMPd
end
section
set_option autoImplicit true
namespace qzVXMPd
open qwzqCne MvPolynomial
open axE (Form raw basis adB a1y a1z blP aTx ao9)
open fP (lP m9 oG cF)
open scoped BigOperators
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private def project (cut:ℕ) :Form →ₗ[Ground] (gU cut→Ground) :=
  LinearMap.pi fun col=>lcoeff Ground col.val
private theorem ad7 (cut:ℕ) (v :aY) :
    project cut (bind₁ raw (monomial v.val 1))=cE cut (aD v.val) := by
  funext m
  exact ao9 v.val m.val (v.property.trans m.property.1.symm)
private theorem bt7 {cut:ℕ} {F:Form} (hc:0<cut)
    (h:F∈restrictWeightedDegree lP (cut - 1)) :
    project cut F=0:= by
  funext m
  apply coeff_eq_zero_of_mem_restrictWeightedDegree h
  have hl:=m.property.2.1
  omega
private theorem ccT {cut:ℕ} {v :Exponent} (h : ¬ Md v) :
    project cut (bind₁ basis (monomial v 1))=0:= by
  funext m
  apply notMem_support_iff.mp
  intro hm
  obtain ⟨hw,ha⟩:=blP v m.val hm
  have hi:=m.property.2.2.1
  have ht:=m.property.2.2.2
  exact h ⟨by omega,ha.trans ht⟩
private theorem b65 {v e :aY}
    (h:v.val.weight m9<e.val.weight m9) :dZ v<dZ e := by
  have hd:=v.property
  rw [cF] at hd
  rw [oG,oG] at h
  unfold dZ
  rw [Sj,Sj,oG,oG]
  omega
private theorem amf (m:Exponent) (z :Ground) :
    (monomial m z :Form)=z•monomial m 1 := by
  rw [smul_monomial,smul_eq_mul,mul_one]
private theorem relation (e :aY) (cut:ℕ) :
    ∃ z :Ground,z≠0 ∧
      ∃ q∈jZ e cut,
        project cut (bind₁ basis (monomial e.val 1)) =
          z•cE cut (aD e.val)+q:= by
  obtain ⟨z,hz,F,hF,he⟩:=aTx e.val
  refine ⟨z,hz,project cut (bind₁ raw F),?_,?_⟩
  · rw [F.as_sum,map_sum,map_sum]
    apply Submodule.sum_mem
    intro m hm
    obtain ⟨hd,hw⟩:=hF m hm
    let v :aY:=⟨m,hd.trans e.property⟩
    have hlt:dZ v<dZ e :=b65 hw
    rw [amf,map_smul,map_smul,show m=v.val from rfl,ad7]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (⟨v,hlt⟩:iw e)))
  · rw [a1y,he,map_add,map_add,amf,map_smul,map_smul,ad7]
private theorem d0u {e v :aY} (h:dZ v<dZ e) (cut:ℕ) :
    jZ v cut≤jZ e cut:= by
  apply Submodule.span_le.mpr
  rintro _ ⟨w,rfl⟩
  exact Submodule.subset_span (Set.mem_range_self (⟨w.val,w.property.trans h⟩:iw e))
private theorem ccS (e :aY) (cut:ℕ) (v :iw e) :
    project cut (bind₁ basis (monomial v.val.val 1))∈jZ e cut:= by
  obtain ⟨z,_,q,hq,h⟩:=relation v.val cut
  rw [h]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self v)))
    (d0u v.property cut hq)
private theorem b2n (F:Form) (h:F.IsHomogeneous 54) :
    (adB F).IsHomogeneous 54 := by
  apply IsWeightedHomogeneous.bind₁ (w:=(1 :Fin 4→ℕ)) _ h
  intro i
  have hx :=isHomogeneous_X (σ:=Fin 4) Ground
  fin_cases i
  · exact (((hx 1).sub (hx 2)).sub (hx 3)).sub (hx 0)
  · exact ((hx 2).add (hx 3)).add (hx 0)
  · exact (hx 3).add (hx 0)
  · exact hx 0
theorem gtu (e :aY) (cut:ℕ) (F:Form) (hc:0<cut)
    (hhom:F.IsHomogeneous 54) (hlow:F∈restrictWeightedDegree lP (cut - 1))
    (hlead: (adB F).coeff e.val≠0 ∧
      ∀ v :aY,Md v.val→dZ e<dZ v→(adB F).coeff v.val=0) :
    cE cut (aD e.val)∈jZ e cut:= by
  classical
  let t:=(adB F).coeff e.val
  let G:=adB F - monomial e.val t
  have hg:G.IsHomogeneous 54 :=
    (b2n F hhom).sub (isHomogeneous_monomial t e.property)
  have hG:project cut (bind₁ basis G)∈jZ e cut:= by
    rw [G.as_sum,map_sum,map_sum]
    apply Submodule.sum_mem
    intro m hm
    by_cases hlive :Md m
    · have hd:m.degree=54 := by
        rw [Finsupp.degree_eq_weight_one]
        exact hg (mem_support_iff.mp hm)
      let v :aY:=⟨m,hd⟩
      have hlt:dZ v<dZ e := by
        apply lt_of_not_ge
        intro h
        apply (mem_support_iff.mp hm)
        change G.coeff v.val=0
        dsimp only [G]
        rw [MvPolynomial.coeff_sub,coeff_monomial]
        by_cases hv :e.val=v.val
        · rw [ite_eq_left hv,← hv,sub_self]
        · have hkey :dZ e<dZ v := by
            have he :=e.property
            rw [cF] at he hd
            have hdif :e.val 1≠v.val 1∨e.val 2≠v.val 2∨e.val 3≠v.val 3:= by
              by_contra! hsame
              apply hv
              ext i
              fin_cases i
              · change e.val 0=v.val 0
                change v.val 0+v.val 1+v.val 2+v.val 3=54 at hd
                omega
              · exact hsame.1
              · exact hsame.2.1
              · exact hsame.2.2
            unfold dZ at h ⊢
            change v.val 0+v.val 1+v.val 2+v.val 3=54 at hd
            omega
          rw [ite_eq_right hv,hlead.2 v hlive hkey,sub_zero]
      rw [amf,map_smul,map_smul]
      exact Submodule.smul_mem _ _ (ccS e cut ⟨v,hlt⟩)
    · rw [amf,map_smul,map_smul,ccT hlive,smul_zero]
      exact Submodule.zero_mem _
  have hB:t•project cut (bind₁ basis (monomial e.val 1))∈jZ e cut:= by
    dsimp only [G] at hG
    rw [map_sub,a1z,map_sub,bt7 hc hlow,zero_sub,
      amf,map_smul,map_smul] at hG
    exact (jZ e cut).neg_mem_iff.mp hG
  have hB' := (jZ e cut).smul_mem t⁻¹ hB
  rw [smul_smul,inv_mul_cancel₀ hlead.1,one_smul] at hB'
  obtain ⟨z,hz,q,hq,he⟩:=relation e cut
  rw [he] at hB'
  have hv :=Submodule.sub_mem (jZ e cut) hB' hq
  rw [add_sub_cancel_right] at hv
  have hv' := Submodule.smul_mem (jZ e cut) z⁻¹ hv
  rw [smul_smul,inv_mul_cancel₀ hz,one_smul] at hv'
  exact hv'
end
end qzVXMPd
end
section
set_option autoImplicit true
namespace qzVXMPd
open qwzqCne MvPolynomial
open GN (Form Interpolant weights b9 wc)
open fP (lP)
open qhonTAe (factorial_ne_zero)
open private biP a7a cDc cKq bnm dmk dmj c5Q from ProximityPrize.SubmissionLower.B0
open private aNF bg1 from ProximityPrize.SubmissionLower.B0
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private theorem ePF (j:Fin 3) {Q:Form} (hQ:Q.IsHomogeneous 54) :
    (a7a j Q).IsHomogeneous 53:= by
  have hd (i:Fin 4) : (pderiv i Q).IsHomogeneous 53:=hQ.pderiv
  fin_cases j
  · exact hd 0
  · exact (hd 0).sub (hd 1)
  · exact ((hd 0).sub (hd 1)).sub (hd 2)
private theorem dMi (v :aY) :
    (bind₁ wc ((MvPolynomial.X 0:Form)^54)).coeff v.val=(v.val.multinomial:Ground) := by
  rw [map_pow,bind₁_X_right]
  have hv :wc 0=(∑ j:Fin 4,MvPolynomial.X j) := by simp [wc,Fin.sum_univ_four,add_assoc]
  rw [hv,coeff_sum_X_pow_of_fintype]
  rw [ite_eq_left (show v.val.sum (fun _ m=>m)=54 from v.property)]
private def Lift (d:ℕ) (P:Interpolant) :Prop :=
  ∃ Q:Form,Q.IsHomogeneous 54∧Q∈restrictWeightedDegree lP d ∧
    ∀ v :aY,(bind₁ wc Q).coeff v.val =
      b9 v.val P*(v.val.multinomial:Ground)
private theorem bIr (a :Ground) :Lift 0 (C a) := by
  refine ⟨C a*(MvPolynomial.X 0:Form)^54,(isHomogeneous_X_pow _ _).C_mul _,?_,?_⟩
  · simpa only [zero_add] using mul_mem_restrictWeightedDegree
      (C_mem_restrictWeightedDegree lP 0 a)
      (X_pow_mem_restrictWeightedDegree_zero (R:=Ground) (i:=0) rfl 54)
  · intro v
    rw [map_mul,bind₁_C_right,coeff_C_mul,dMi,b9,aeval_C]
    simp
private theorem ewe {d:ℕ} {P:Interpolant} (h:Lift d P) (j:Fin 3) :
    Lift (d+weights j) (P*MvPolynomial.X j) := by
  obtain ⟨Q,hQ,hd,hc⟩:=h
  refine ⟨biP j*a7a j Q,(dmk j).mul (ePF j hQ),
    ?_,?_⟩
  · rw [add_comm]
    exact mul_mem_restrictWeightedDegree (dmj j) (c5Q j hd)
  · intro v
    rw [map_mul,cDc,← cKq,bnm,hc,map_mul]
    rw [show b9 v.val (MvPolynomial.X j)=(v.val j.succ:Ground) by simp [b9]]
    ring
private theorem bfc (m:Fin 3 →₀ ℕ) (a :Ground) :
    Lift (m.weight weights) (monomial m a) := by
  induction m using Finsupp.induction₂ with
  | zero=>simpa only [map_zero,← C_apply] using bIr a
  | add_single j n m _ hnz ih =>
    clear hnz
    rw [map_add,Finsupp.weight_single,smul_eq_mul,monomial_add_single]
    induction n with
    | zero=>simpa only [zero_mul,add_zero,pow_zero,mul_one] using ih
    | succ n hn =>
      rw [Nat.succ_mul,← add_assoc,pow_succ,← mul_assoc]
      exact ewe hn j
private theorem ajL (cut:ℕ) (P:Interpolant)
    (hP:P∈restrictWeightedDegree weights (cut - 1)) :
    ∃ Q:Form,Q.IsHomogeneous 54∧Q∈restrictWeightedDegree lP (cut - 1) ∧
      ∀ v :aY,(bind₁ wc Q).coeff v.val =
        b9 v.val P*(v.val.multinomial:Ground) := by
  classical
  have h:= fun m:Fin 3 →₀ ℕ=>bfc m (P.coeff m)
  unfold Lift at h
  choose Q hQ hd hc using h
  refine ⟨∑ m∈P.support,Q m,IsHomogeneous.sum _ _ _ (fun m _=>hQ m),?_,?_⟩
  · apply Submodule.sum_mem
    intro m hm
    exact restrictWeightedDegree_mono _ (mem_restrictWeightedDegree.mp hP m hm) (hd m)
  · intro v
    calc
      _ = ∑ m∈P.support,(b9 v.val (monomial m (P.coeff m))) *
          (v.val.multinomial:Ground) := by
        simp only [map_sum,coeff_sum,hc]
      _ = _:= by rw [← Finset.sum_mul,← map_sum,← P.as_sum]
private theorem aoy (v :aY) : (v.val.multinomial:Ground)≠0:= by
  have h:=congrArg (fun n:ℕ=>(n:Ground)) (Nat.multinomial_spec Finset.univ v.val)
  rw [Nat.cast_mul,← Finsupp.multinomial_eq_of_support_subset
    (Finset.subset_univ v.val.support),← Finsupp.degree_eq_sum,v.property] at h
  intro hz
  simp only [hz,mul_zero] at h
  exact factorial_ne_zero (by decide :54≤56) h.symm
theorem Ae (e :aY) (cut:ℕ) (hc:0<cut) (P:Interpolant)
    (hP:P∈restrictWeightedDegree weights (cut - 1)) (hsep:Ak e P) :
    cE cut (aD e.val)∈jZ e cut:= by
  obtain ⟨Q,hhom,hlow,hcoeff⟩:=ajL cut P hP
  apply gtu e cut Q hc hhom hlow
  constructor
  · rw [aNF,hcoeff]
    exact mul_ne_zero (bg1 _) (mul_ne_zero hsep.1 (aoy e))
  · intro v hlive hv
    rw [aNF,hcoeff,hsep.2 v hlive hv,zero_mul,mul_zero]
end
end qzVXMPd
end
section
set_option autoImplicit true
namespace qeUg7Fa
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 0
local notation "r!" z "," p=>asA (v :=z) (by rfl) p
private theorem r1 :total 2690 12=0x204645333ea0 :=
  r! 0x2b62e859e40,r! 0x2b5268b6900,r! 0x2b41e84a150,r! 0x2b316eff260,
  r! 0x2b20f5c2860,r! 0x2b108214fa0,r! 0x2b000fc3ec0,r! 0x2aefa3e3400,
  r! 0x2adf36da900,r! 0x2aced155880,r! 0x2abe6b51180,r! 0x2aae0bda5f0,
  rfl
private theorem r2 :total 2702 12=0x1fb2fa21b340 :=
  r! 0x2a9dac807a0,r! 0x2a8d537e190,r! 0x2a7cfacd6c0,r! 0x2a6ca978d40,
  r! 0x2a5c562ff00,r! 0x2a4c0b37b60,r! 0x2a3bbf78b60,r! 0x2a2b7a1a160,
  r! 0x2a1b34a7d80,r! 0x2a0af616850,r! 0x29fab7509d0,r! 0x29ea80ccf50,
  rfl
private theorem r3:total 2714 11=0x1c8e84059290 :=
  r! 0x29da471b030,r! 0x29ca16c4580,r! 0x29b9e4e8040,r! 0x29a9ba0f060,
  r! 0x29998ee0b80,r! 0x29896a7f3f0,r! 0x297945ad400,r! 0x296929c4670,
  r! 0x295909f0020,r! 0x2948f46a200,r! 0x2938dc57040,rfl
theorem apj:total 2690 35=0x5c87c35a8470 :=
  (total_append r1 (total_append r2 r3))
end qeUg7Fa
end
