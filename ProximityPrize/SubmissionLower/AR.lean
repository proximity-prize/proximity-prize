import ProximityPrize.SubmissionLower.B7
set_option Elab.async false
open _root_ renaming AddCommGroup→ oK,Fin.prod_univ_four→pQ,Fin.sum_univ_four→ oy,Finsupp.weight_eq_sum→n5,Fintype.sum_option→pL,Int.natCast_nonneg→p5,LinearMap.ker→mD,LinearMap.range→cy,Module.Finite→pz,Module.finrank→aU,MvPolynomial.X_mem_restrictWeightedOrder→ oZ,MvPolynomial.bind₁→lz,MvPolynomial.bind₁_mem_restrictWeightedOrder→p7,MvPolynomial.monomial→lJ,MvPolynomial.mul_mem_restrictWeightedOrder→nq,MvPolynomial.restrictSupport→pC,MvPolynomial.restrictSupport_finite→pU,MvPolynomial.restrictWeightedOrder→lI,MvPolynomial.weightedTruncation→ ox,MvPolynomial.weightedTruncation_eq_zero_iff→ oD,Nat.mul_comm→ oY,ReedSolomon.HiddenDerivative.jetDerivativeWeight→ oj,ReedSolomon.HiddenDerivative.localContactWeight→c9,ReedSolomon.HiddenDerivative.unscaledLocalImage→ ov,Submodule→ oz,Submodule.add_mem→p6,Submodule.finrank_mono→ oq,ite_eq_left→pG,smul_eq_mul→nI,xE.oldCount→lV
set_option autoImplicit true
section
namespace y9
noncomputable section
open aR (ao)
open xE (M7 UT topWeight)
open gW (Bank gZ Ao Dj)
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
def ali (b:Bank) (e :UT) :Prop :=
 e.weight jetDegreeWeight≤b.box.b ∧
 e.weight oj≤b.box.j ∧
 e.weight topWeight≤b.box.t ∧
 e.weight (differentialWeight gZ)≤Ao ∧
 e (some 1)+e (some 2)+e (some 3)≤Dj e.some.degree
def aE1 (b:Bank) :Set UT := { e | ali b e }
theorem aQv (b:Bank) : (aE1 b).Finite := by
 refine (Finsupp.finite_of_nat_weight_le (differentialWeight (d:=3) gZ)
   ?_ Ao).subset (fun _ he=>he.2.2.2.1)
 intro v
 cases v with
 | none=>decide
 | some j =>
   exact (differentialWeight_some_pos_of_order_lt_degree (by decide :3<gZ) j).ne'
def W2 (b:Bank) :oz ao M7 :=
 pC ao (aE1 b)
instance (b:Bank) :pz ao (W2 b) :=
 pU (aQv b)
abbrev QA:=Fin 4650
abbrev sP (b:Bank) :=Fin (b.box.b+1)×QA
def aQj (r :QA) :ℤ:=(r.val :ℤ) - 1650
abbrev offset {b:Bank} (i:sP b) :ℤ:=aQj i.2
def iO (q:ℕ) :ℕ:=min q (Dj q)
def TO (b:Bank) (i:sP b) :Set UT :=
  { e | ali b e∧e none<b.m ∧
    e.weight jetDegreeWeight=i.1.val∧(e none :ℤ)-e.weight oj=offset i }
def aFx (b:Bank) (i:sP b) :oz ao M7 :=
 pC ao (TO b i)
instance (b:Bank) (i:sP b) :pz ao (aFx b i) :=
 pU ((aQv b).subset (fun _ h=>h.1))
end
end y9
end
section
namespace y9
noncomputable section
open aR Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open xE (M7)





private theorem weight_eq_sum (m:Fin 4 →₀ ℕ) (weight:Fin 4→ℕ) :
  m.weight weight=m.sum (fun i a=>weight i*a) := by
 simp only [Finsupp.weight_apply,nI,oY]
private theorem aqS (t:ℕ) {lo hi:ℕ} (hle :lo≤hi) {f :ℕ→ℕ}
   (hf :Antitone f ∧ ∀ q,f q≤lo) :
   Antitone (fun q=>if q<t then hi else f q) ∧ ∀ q,(if q<t then hi else f q)≤hi:= by
 have hbound (q:ℕ) : (if q<t then hi else f q)≤hi:= by
   split
   · exact le_rfl
   · exact (hf.2 q).trans hle
 refine ⟨?_,hbound⟩
 intro q r hqr
 change (if r<t then hi else f r)≤(if q<t then hi else f q)
 by_cases hq:q<t
 · rw [pG hq]
   exact hbound r
 · rw [ite_eq_right hq,ite_eq_right (show ¬ r<t by omega)]
   exact hf.1 hqr
private theorem eMe {m:ℕ} (x y :ao) (Q:M7) (S:ao[X])
  (hS:S.eval x=y) (hQ:SatisfiesLocalConstraints m x y Q) :
  (Polynomial.X-Polynomial.C x)^m∣differentialSpecialization Q S:= by
 exact X_sub_C_pow_dvd_differentialSpecialization_of_contact Q S x y hS hQ
end
end y9
end
section
namespace y9
noncomputable section
open aR (ao)
open xE (M7 UT Local)
open akL (Jp BU oH La)
open gW (Bank)
open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
private def jO {b:Bank} (i:sP b) :ℕ:=i.1.val - iO i.1.val
private def Ra {b:Bank} (i:sP b) (e :UT) :Jp :=
 Finsupp.equivFunOnFinite.symm
  ![e (some 0) - jO i,e (some 1),e (some 2),e (some 3)]
private theorem bhx (e :UT) :
  e.weight jetDegreeWeight=e (some 0)+e (some 1)+e (some 2)+e (some 3) := by
 simp [n5 ,pL,oy]
private theorem bhy (e :UT) :
  e.weight oj=e (some 1)+2*e (some 2)+3*e (some 3) := by
 simp [n5 ,pL,oy ,oj,
  nI,oY]
local notation "T" => (MvPolynomial.X (localT 3) :Local)
local notation "E" => (MvPolynomial.X (localE 3) :Local)
private def Ce (j:Fin 3) :Local:=MvPolynomial.X (localY j)
private def asF:Local:=ov 3 0 0 (some 0)
private def NH :Fin 4→Local :=
 ![T*E,T*Ce 0,T^2*Ce 1,T^3*Ce 2]
private def aWg:M7 →ₐ[ao] Local:=unscaledLocalSubstitution 3 0 0
private theorem dck :lz NH (La 0)=asF:= by
 simp [La,NH,asF,ov,localCorrection,Fin.sum_univ_three,Ce]
 ring
private theorem coL (j:Fin 3) :
  lz NH (La j.succ)=T^j.succ.val*Ce j:= by
 fin_cases j <;> simp [La,NH]
private theorem blU {σ τ:Type*} [Fintype σ]
  (f :σ→MvPolynomial τ ao) (e :σ →₀ ℕ) :
  lz f (lJ e 1) = ∏ j,f j^e j:= by
 rw [bind₁_monomial,C_1,one_mul]
 exact Finsupp.prod_fintype e (fun j n=>f j^n) (fun _=>pow_zero _)
private theorem eH8 (e :UT) :
   aWg (lJ e 1)=T^e none *
     (asF^e (some 0)*(Ce 0)^e (some 1)*(Ce 1)^e (some 2)*(Ce 2)^e (some 3)) := by
 rw [aWg,unscaledLocalSubstitution,blU,Fintype.prod_option,pQ]
 change (C (0:ao)+T)^e none *
   (asF^e (some 0)*(Ce 0)^e (some 1)*(Ce 1)^e (some 2)*(Ce 2)^e (some 3))= _
 simp
private def aid (j:Fin 4) :ℕ:=oH j+BU j
private theorem cwS (e :Jp) :
  e.weight aid=e.weight oH+e.weight BU:= by
 simp [n5 ,aid,nI,Nat.mul_add,Finset.sum_add_distrib]
private theorem aQH (n:ℕ) :
  T^n∈lI (c9 3) n:= by
 simpa using pow_mem_restrictWeightedOrder
  (oZ (R:=ao) (c9 3) (localT 3) (m:=1) le_rfl) n
private theorem bv2 (j:Fin 4) :
   NH j∈lI (c9 3) (aid j) := by
 have hY (k :Fin 3) :Ce k∈lI (c9 3) 0:= by simp
 have hE :E∈lI (c9 3) 3 :=
   oZ _ _ le_rfl
 fin_cases j
 · simpa [NH,aid,oH,BU] using
    nq (aQH 1) hE
 · simpa [NH,aid,oH,BU] using
    nq (aQH 1) (hY 0)
 · simpa [NH,aid,oH,BU] using
    nq (aQH 2) (hY 1)
 · simpa [NH,aid,oH,BU] using
    nq (aQH 3) (hY 2)
private theorem cva :
  asF∈lI (c9 3) 1 := by
 have h (j:Fin 4) :NH j∈lI (c9 3) 1 :=
  restrictWeightedOrder_anti _ (Nat.succ_le_succ (Nat.zero_le _)) (bv2 j)
 rw [← dck]
 simp only [La,ite_true,map_add,map_sub,bind₁_X_right]
 exact p6 _ (Submodule.sub_mem _ (p6 _ (h 0) (h 1)) (h 2)) (h 3)
private theorem caB {n m:ℕ} {p:Local}
  (h:T^n*p∈lI (c9 3) (m+n)) :
  p∈lI (c9 3) m:= by
 rw [MvPolynomial.X_pow_eq_monomial] at h
 intro e he
 have hh:=mem_restrictWeightedOrder.mp h (Finsupp.single (localT 3) n+e) (by
  rw [MvPolynomial.mem_support_iff,coeff_monomial_mul,one_mul]
  exact MvPolynomial.mem_support_iff.mp he)
 change m≤e.weight (c9 3)
 simp only [map_add,Finsupp.weight_single,localContactWeight_T,nI,mul_one] at hh
 omega
end
end y9
end
section
namespace y9
noncomputable section
open aR (ao)
open xE (Flag AO m5)
open akL (KP b3u aWa aAu
 aDd b3d alM MI oH)

open MvPolynomial
private theorem cet (F:Flag) :
  aU ao (cy (KP F))≤(aAu F).card:= by
 rw [← b3d]
 apply oq
 rintro _ ⟨p,rfl⟩
 exact b3u F p
private theorem fTs (F:Flag) (h:F.order≤0) :
  aU ao (cy (KP F))=0:= by
 have hz :KP F=0:= by
  ext p:1
  change ox oH F.order.toNat (alM (p:MI))=0
  apply (oD _ _ _).mpr
  simp [Int.toNat_of_nonpos h]
 simp [hz]
private theorem aOG (F:Flag)
   (hcols : ((aWa F).card:ℤ)=lV F)
   (hrows : ((aAu F).card:ℤ)=AO F) :
   m5 F≤(aU ao (mD (KP F)) :ℤ) := by
 have hr :=cet F
 have hn:=(KP F).finrank_range_add_finrank_ker
 rw [aDd] at hn
 unfold m5
 split
 · exact p5 _
 · omega
end
end y9
end
section
namespace y9
noncomputable section
open aR PolynomialDifferential ReedSolomon.HiddenDerivative
open xE (UT)


open scoped BigOperators
private theorem b5V {m:ℕ} (e :UT) (c:ao) (he :m≤e none) :
    localConstraintAt m 0 0 (lJ e c)=0:= by
  change ox (c9 3) m
    (lz (ov 3 0 0) (lJ e c))=0
  apply (oD _ _ _).mpr
  refine p7
    (w:= fun v :JetVariable 3=>v.elim 1 (fun _=>0)) ?_ ?_
  · intro v
    cases v with
    | none =>
      simpa only [ov,map_zero,zero_add,Option.elim_none] using
        (oZ (R:=ao)
          (c9 3) (localT 3) (m:=1) (by rfl))
    | some j=>simp
  · exact (MvPolynomial.monomial_mem_restrictWeightedOrder _ _ _ _).mpr
      (Or.inl (by simpa only [Finsupp.weight_elim_one_zero] using he))
private theorem b3b {ι V:Type*} [oK V] [Module ao V]
   (p:ι→ oz ao V) [∀ i,pz ao (p i)] (s :Finset ι) :
   aU ao (s.sup p:oz ao V) ≤ ∑ i∈s,aU ao (p i) := by
 classical
 induction s using Finset.induction_on with
 | empty=>simp
 | insert i s hi ih =>
   rw [Finset.sup_insert,Finset.sum_insert hi]
   exact (Submodule.finrank_add_le_finrank_add_finrank (p i) (s.sup p)).trans
     (Nat.add_le_add_left ih _)
private theorem cZu {V W:Type*} [oK V] [Module ao V]
  [oK W] [Module ao W] {n:ℕ} (f :V →ₗ[ao] W)
  (hf :Function.Injective f) (P:W→Prop) (hP : ∀ x,P (f x))
  (hn:n≤aU ao V) :
  ∃ e :Fin n→W,LinearIndependent ao e ∧ ∀ i,P (e i) := by
 obtain ⟨e,he⟩:=exists_linearIndependent_of_le_finrank hn
 exact ⟨f ∘ e,he.map' f (LinearMap.ker_eq_bot_of_injective hf),fun i=>hP (e i)⟩
private theorem dgs {r d k bound x5:ℕ}
 (hr :r≤262144*bound) (hd:262144*bound + x5≤d)
 (h:r+k=d) :x5≤k := by omega
end
end y9
end
