import ProximityPrize.SubmissionLower.B0
import ProximityPrize.SubmissionLower.Z3wMysc
import ProximityPrize.SubmissionLower.Z3vxfLe
import ProximityPrize.SubmissionLower.ZELw4Ka
import ProximityPrize.SubmissionLower.ZGAUtmc
import ProximityPrize.SubmissionLower.Z3gZttb
set_option Elab.async false
open _root_ renaming MvPolynomial.X → z9v, Nat.cast_mul → z2R, Set.mem_range_self → zWL, Submodule.smul_mem → zc2, Submodule.subset_span → zBO, Submodule.sum_mem → zo3
section
set_option autoImplicit true
namespace qrcA6ce
open qoWrama
open qHde8fc (Ground Exponent aD)
open GN (Interpolant ord weights b9)
open fP (oG)
open MvPolynomial
noncomputable section
abbrev cost (e :aY) :ℕ:=cP (aD e.val)
theorem nG (e :aY) :cost e=52+ord e.val := by
  rw [cost,Sj,oG,ord]
abbrev jZ (e :aY) (cut:ℕ) :Submodule Ground (gU cut→Ground) :=
  Submodule.span Ground (Set.range fun v :iw e=>cE cut (aD v.val.val))
def Md (m:Exponent) :Prop :=ord m≤56∧m 0≤16
abbrev Bounded (d:ℕ) :=restrictWeightedDegree (R:=Ground) weights d
def Ak (e :aY) (P:Interpolant) :Prop :=
  b9 e.val P≠0 ∧
    ∀ v :aY,Md v.val→dZ e<dZ v→b9 v.val P=0
def cutBudget (e :aY) :ℕ:=3*(56 - ord e.val)+2*e.val 0+e.val 2/2
end
end qrcA6ce
end
section
set_option autoImplicit true
namespace qrcA6ce
open qoWrama MvPolynomial
open qHde8fc (Ground Exponent aD)
open GN (ord)
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
  rw [oG,← ord] at hw
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
    apply zo3
    intro m hm
    obtain ⟨hd,hw⟩:=hF m hm
    let v :aY:=⟨m,hd.trans e.property⟩
    have hlt:dZ v<dZ e :=b65 hw
    rw [amf,map_smul,map_smul,show m=v.val from rfl,ad7]
    exact zc2 _ _ (zBO (zWL (⟨v,hlt⟩:iw e)))
  · rw [a1y,he,map_add,map_add,amf,map_smul,map_smul,ad7]
theorem span_of_inactive (e :aY) (cut:ℕ) (h : ¬ Md e.val) :
    cE cut (aD e.val)∈jZ e cut:= by
  obtain ⟨z,hz,q,hq,he⟩:=relation e cut
  rw [ccT h,eq_comm,add_eq_zero_iff_eq_neg] at he
  have hp:z•cE cut (aD e.val)∈jZ e cut :=
    he.symm ▸ (jZ e cut).neg_mem hq
  have hs :=(jZ e cut).smul_mem z⁻¹ hp
  simpa only [smul_smul,inv_mul_cancel₀ hz,one_smul] using hs
private theorem d0u {e v :aY} (h:dZ v<dZ e) (cut:ℕ) :
    jZ v cut≤jZ e cut:= by
  apply Submodule.span_le.mpr
  rintro _ ⟨w,rfl⟩
  exact zBO (zWL (⟨w.val,w.property.trans h⟩:iw e))
private theorem ccS (e :aY) (cut:ℕ) (v :iw e) :
    project cut (bind₁ basis (monomial v.val.val 1))∈jZ e cut:= by
  obtain ⟨z,_,q,hq,h⟩:=relation v.val cut
  rw [h]
  exact Submodule.add_mem _ (zc2 _ _ (zBO (zWL v)))
    (d0u v.property cut hq)
private theorem b2n (F:Form) (h:F.IsHomogeneous 52) :
    (adB F).IsHomogeneous 52 := by
  apply IsWeightedHomogeneous.bind₁ (w:=(1 :Fin 4→ℕ)) _ h
  intro i
  have hx :=isHomogeneous_X (σ:=Fin 4) Ground
  fin_cases i
  · exact (((hx 1).sub (hx 2)).sub (hx 3)).sub (hx 0)
  · exact ((hx 2).add (hx 3)).add (hx 0)
  · exact (hx 3).add (hx 0)
  · exact hx 0
theorem gtu (e :aY) (cut:ℕ) (F:Form) (hc:0<cut)
    (hhom:F.IsHomogeneous 52) (hlow:F∈restrictWeightedDegree lP (cut - 1))
    (hlead: (adB F).coeff e.val≠0 ∧
      ∀ v :aY,Md v.val→dZ e<dZ v→(adB F).coeff v.val=0) :
    cE cut (aD e.val)∈jZ e cut:= by
  classical
  let t:=(adB F).coeff e.val
  let G:=adB F - monomial e.val t
  have hg:G.IsHomogeneous 52 :=
    (b2n F hhom).sub (isHomogeneous_monomial t e.property)
  have hG:project cut (bind₁ basis G)∈jZ e cut:= by
    rw [G.as_sum,map_sum,map_sum]
    apply zo3
    intro m hm
    by_cases hlive :Md m
    · have hd:m.degree=52 := by
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
                change v.val 0+v.val 1+v.val 2+v.val 3=52 at hd
                omega
              · exact hsame.1
              · exact hsame.2.1
              · exact hsame.2.2
            unfold dZ at h ⊢
            change v.val 0+v.val 1+v.val 2+v.val 3=52 at hd
            omega
          rw [ite_eq_right hv,hlead.2 v hlive hkey,sub_zero]
      rw [amf,map_smul,map_smul]
      exact zc2 _ _ (ccS e cut ⟨v,hlt⟩)
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
  have hv' := zc2 (jZ e cut) z⁻¹ hv
  rw [smul_smul,inv_mul_cancel₀ hz,one_smul] at hv'
  exact hv'
end
end qrcA6ce
end
section
set_option autoImplicit true
namespace qrcA6ce
open qoWrama MvPolynomial
open qHde8fc (Ground aD)
open GN (Form Interpolant weights b9 wc)
open fP (lP)
open private biP a7a cDc cKq bnm dmk dmj c5Q from ProximityPrize.SubmissionLower.B0
open private aNF bg1 from ProximityPrize.SubmissionLower.B0
noncomputable section
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private theorem ePF {n:ℕ} (j:Fin 3)
    {Q:Form} (hQ:Q.IsHomogeneous n) :
    (a7a j Q).IsHomogeneous (n - 1) := by
  have hd (i:Fin 4) : (pderiv i Q).IsHomogeneous (n - 1) :=hQ.pderiv
  fin_cases j
  · exact hd 0
  · exact (hd 0).sub (hd 1)
  · exact ((hd 0).sub (hd 1)).sub (hd 2)
private theorem dMi {n:ℕ} (v : {e :Fin 4 →₀ ℕ // e.degree=n}) :
    (bind₁ wc ((z9v 0:Form)^n)).coeff v.val=(v.val.multinomial:Ground) := by
  rw [map_pow,bind₁_X_right]
  have hv :wc 0=(∑ j:Fin 4,z9v j) := by simp [wc,Fin.sum_univ_four,add_assoc]
  rw [hv,coeff_sum_X_pow_of_fintype]
  rw [ite_eq_left (show v.val.sum (fun _ m=>m)=n from v.property)]
private def Lift (n d:ℕ) (P:Interpolant) :Prop :=
  ∃ Q:Form,Q.IsHomogeneous n∧Q∈restrictWeightedDegree lP d ∧
    ∀ v : {e :Fin 4 →₀ ℕ // e.degree=n},(bind₁ wc Q).coeff v.val =
      b9 v.val P*(v.val.multinomial:Ground)
private theorem bIr (n:ℕ) (a :Ground) :Lift n 0 (C a) := by
  refine ⟨C a*(z9v 0:Form)^n,(isHomogeneous_X_pow _ _).C_mul _,?_,?_⟩
  · simpa only [zero_add] using mul_mem_restrictWeightedDegree
      (C_mem_restrictWeightedDegree lP 0 a)
      (X_pow_mem_restrictWeightedDegree_zero (R:=Ground) (i:=0) rfl n)
  · intro v
    rw [map_mul,bind₁_C_right,coeff_C_mul,dMi,b9,aeval_C]
    simp
private theorem ewe {n d:ℕ} (hn:0<n)
    {P:Interpolant} (h:Lift n d P) (j:Fin 3) :
    Lift n (d+weights j) (P*z9v j) := by
  obtain ⟨Q,hQ,hd,hc⟩:=h
  refine ⟨biP j*a7a j Q,?_,?_,?_⟩
  · simpa only [Nat.add_comm 1,Nat.sub_add_cancel hn] using
      (dmk j).mul (ePF j hQ)
  · rw [add_comm]
    exact mul_mem_restrictWeightedDegree (dmj j) (c5Q j hd)
  · intro v
    rw [map_mul,cDc,← cKq,bnm,hc,map_mul]
    rw [show b9 v.val (z9v j)=(v.val j.succ:Ground) by simp [b9]]
    ring
private theorem bfc {n:ℕ} (hn:0<n) (m:Fin 3 →₀ ℕ) (a :Ground) :
    Lift n (m.weight weights) (monomial m a) := by
  induction m using Finsupp.induction₂ with
  | zero=>simpa only [map_zero,← C_apply] using bIr n a
  | add_single j n m _ hnz ih =>
    clear hnz
    rw [map_add,Finsupp.weight_single,smul_eq_mul,monomial_add_single]
    induction n with
    | zero=>simpa only [zero_mul,add_zero,pow_zero,mul_one] using ih
    | succ jn hprev =>
      rw [Nat.succ_mul,← add_assoc,pow_succ,← mul_assoc]
      exact ewe hn hprev j
theorem ajL {n:ℕ} (hn:0<n) (cut:ℕ) (P:Interpolant)
    (hP:P∈restrictWeightedDegree weights (cut - 1)) :
    ∃ Q:Form,Q.IsHomogeneous n∧Q∈restrictWeightedDegree lP (cut - 1) ∧
      ∀ v : {e :Fin 4 →₀ ℕ // e.degree=n},(bind₁ wc Q).coeff v.val =
        b9 v.val P*(v.val.multinomial:Ground) := by
  classical
  have h:= fun m:Fin 3 →₀ ℕ=>bfc hn m (P.coeff m)
  unfold Lift at h
  choose Q hQ hd hc using h
  refine ⟨∑ m∈P.support,Q m,IsHomogeneous.sum _ _ _ (fun m _=>hQ m),?_,?_⟩
  · apply zo3
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
  rw [z2R,← Finsupp.multinomial_eq_of_support_subset
    (Finset.subset_univ v.val.support),← Finsupp.degree_eq_sum,v.property] at h
  intro hz
  simp only [hz,mul_zero] at h
  exact qhonTAe.factorial_ne_zero (show 52≤56 by decide) h.symm
theorem Ae (e :aY) (cut:ℕ) (hc:0<cut) (P:Interpolant)
    (hP:P∈restrictWeightedDegree weights (cut - 1)) (hsep:Ak e P) :
    cE cut (aD e.val)∈jZ e cut:= by
  obtain ⟨Q,hhom,hlow,hcoeff⟩:=ajL (show 0<52 by decide) cut P hP
  apply gtu e cut Q hc hhom hlow
  constructor
  · rw [aNF,hcoeff]
    exact mul_ne_zero (bg1 _) (mul_ne_zero hsep.1 (aoy e))
  · intro v hlive hv
    rw [aNF,hcoeff,hsep.2 v hlive hv,zero_mul,mul_zero]
end
end qrcA6ce
end
section
set_option autoImplicit true
namespace qKVdmob
open qHde8fc (Ground)
open scoped BigOperators
open private bGN bm8 from ProximityPrize.SubmissionLower.ZELw4Ka
local instance :Fact (Nat.Prime P1.p) :=⟨KoalaBear.is_prime⟩
private theorem factorial_ne_zero {m:ℕ} (hm:m≤56) :
    (m.factorial:Ground)≠0:= by
  induction m with
  | zero=>simp
  | succ m ih =>
    rw [Nat.factorial_succ,z2R]
    refine mul_ne_zero ?_ (ih (by omega))
    intro h
    have hp:=(CharP.cast_eq_zero_iff Ground P1.p (m+1)).mp h
    have hle :=Nat.le_of_dvd (Nat.succ_pos m) hp
    change 0x7f000001≤ m+1 at hle
    omega
private theorem choose_ne_zero {n k :ℕ} (hn:n≤56) (hk :k≤n) :
    (n.choose k :Ground)≠0:= by
  intro h
  have he :=congrArg (fun m:ℕ=>(m:Ground)) (Nat.choose_mul_factorial_mul_factorial hk)
  simp only [z2R,h,zero_mul] at he
  exact factorial_ne_zero hn he.symm
theorem SX (n U w:ℕ) (hn:n≤56) (hU:U≤n) (hw:w≤U + 1)
    (v :Fin w→Ground) :
    ∃ c:Fin w→Ground,∀ j:Fin w,
      (∑ i:Fin w,c i*((n - i.val).choose (U - j.val) :Ground))=v j:= by
  let δ (j:Fin w) :Ground :=(n.choose (U - j.val) :Ground)
  obtain ⟨a,ha⟩:=bGN w (n-U) (fun j=>v j/δ j)
  refine ⟨fun i=>a i*(n.choose i.val :Ground),?_⟩
  intro j
  have hz :δ j≠0:=choose_ne_zero hn (by omega)
  calc
    _ = ∑ i:Fin w,(a i*((n-U + j.val).choose i.val :Ground))*δ j:= by
      apply Finset.sum_congr rfl
      intro i _
      have h:=congrArg (fun m:ℕ=>(m:Ground)) (bm8 n i.val (U - j.val))
      have he :n-(U - j.val)=n-U + j.val := by omega
      simp only [z2R,he] at h
      dsimp only [δ]
      rw [mul_assoc,h]
      ac_rfl
    _=v j:= by rw [← Finset.sum_mul,ha,div_mul_cancel₀ _ hz]
end qKVdmob
end
section
set_option autoImplicit true
namespace qeUg7Fa
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 0
local notation "r!" z "," p=>asA (v :=z) (by rfl) p
private theorem r1 :total 2830 12=0x19e66ac9cc50 :=
  r! 0x22d9250b730,r! 0x22ca7aa7c00,r! 0x22bbc37b7f0,r! 0x22ad1da92d0,
  r! 0x229e6d4faf0,r! 0x228fd2b2b00,r! 0x2281248c5a0,r! 0x227290557f0,
  r! 0x2263e9209a0,r! 0x22555b5c580,r! 0x2246be98220,r! 0x223833cb9a0,
  rfl
private theorem r2 :total 2842 12=0x1963719d9980 :=
  r! 0x22299dd50e0,r! 0x221b1c65530,r! 0x220ca043f60,r! 0x21fe1194ac0,
  r! 0x21ef99eb810,r! 0x21e1120b9a0,r! 0x21d2a48fb30,r! 0x21c41fead90,
  r! 0x21b5bb7cea0,r! 0x21a73e09260,r! 0x2198dd343a0,r! 0x218a669aa40,
  rfl
private theorem r3:total 2854 11=0x16d3f5240740 :=
  r! 0x217c10105d0,r! 0x216d9ef4380,r! 0x215f4c827d0,r! 0x2150e257e40,
  r! 0x21429653130,r! 0x213435fc630,r! 0x2125f07cc10,r! 0x21179422a40,
  r! 0x210958e4f50,r! 0x20faffad700,r! 0x20eccae03e0,rfl
theorem rows9:total 2830 35=0x4a1dd18b6d10 :=
  (total_append r1 (total_append r2 r3))
end qeUg7Fa
end
