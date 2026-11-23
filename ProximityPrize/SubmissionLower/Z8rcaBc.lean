import ProximityPrize.SubmissionLower.ZbnhR9d
import ProximityPrize.SubmissionLower.ZIo6oRc
import ProximityPrize.SubmissionLower.ZVZMqYa
import ProximityPrize.SubmissionLower.ZbsVARc
import ProximityPrize.SubmissionLower.P5_7_1_7_5Split
set_option Elab.async false
section
set_option autoImplicit true
namespace qHuUuEa
noncomputable section
open P6 (K p)
open P6_7_1 (Input)
open cu (L)
open gT (kM bbt aSf)
open YY (U7)
structure DescendedMarks (x :Input) (T:Finset K) (J:Ideal kM)
    (Q:MvPolynomial (Fin 2) L) (e H :ℕ) :Prop where
  subset :T⊆x.Γ
  curve :bbt J e H
  irreducible :Irreducible Q
  projection :J.comap gT.pZ=Ideal.span {MvPolynomial.map U7 Q}
  plane_pos :0<Q.totalDegree
  seed_lt:Q.totalDegree*e<p
  marks : ∀ γ∈T,aSf J (x.M.label γ) (x.F.scalar γ)
end
end qHuUuEa
end
section
set_option autoImplicit true
namespace qgscZIa
noncomputable section
open q3rjQGe (AxisSection)
open gT (Ambient Pp)
open OH (Q6)
abbrev fixedAxis (a :Fin 2) :Fin 4 :=if a=0 then 1 else 0
abbrev freeAxis (a :Fin 2) :Fin 4 :=Fin.castLE (by decide :2≤4) a
abbrev axisIdeal (q:Ideal Ambient) (a :Fin 2) :=
  q.map Q6 ⊔ Ideal.span {Pp (fixedAxis a)}
def axisCoord (q:Ideal Ambient) (a :Fin 2) (i:Fin 4) :AxisSection q a :=
  Ideal.Quotient.mk (axisIdeal q a) (MvPolynomial.X i)
def axisRestrict (q:Ideal Ambient) (a :Fin 2) :Ambient →+* AxisSection q a :=
  (Ideal.Quotient.mk (axisIdeal q a)).comp Q6
end
end qgscZIa
end
section
set_option autoImplicit true
set_option Elab.async false
namespace qUlPTla
open P6_7_1
private theorem grade_checks :checked 1 gw:= by
  have h:checked 1 (segment 0 ++ (segment 25 ++ (segment 50 ++ segment 75))) :=
    checked_append Wp (checked_append Z3 (checked_append aib akh))
  exact h
theorem proof :P6_7_1.c7:= by
  intro h hl hu t
  cases t with
  | none =>
    change rectDebit h {terminal with t:=terminal.z} <
      rectGain h {terminal with t:=terminal.z} 1 (gw.length+1) 0
    rw [reflected_debit,reflected_gain]
    exact solve hl hu ordinary_check
  | some p =>
    obtain ⟨i,a⟩:=p
    have hc:check (i.val+1) (subWidth i) (seedCap i+1)=true := by
      rw [Nat.add_comm]
      exact checked_get grade_checks i
    have hs :=solve hl hu hc
    fin_cases a
    · exact hs
    · change rectDebit h {terminal with t:=subWidth i} <
        rectGain h {terminal with t:=subWidth i} 1 (i.val+1) (seedCap i+1)
      rw [reflected_debit,reflected_gain]
      exact hs
end qUlPTla
end
section
set_option autoImplicit true
namespace qCpNcsc
theorem proof :qy95ATd.c3:=qHDgEWd.proof
end qCpNcsc
end
section
set_option autoImplicit true
namespace qAxVxdc
theorem proof :qy95ATd.c4 :=qwDXpPd.proof
end qAxVxdc
end
section
set_option autoImplicit true
namespace qH2fULd
noncomputable section
open Finset Polynomial
open P6 (K)
open P6_7_3 (Input)
open qy95ATd (WordChart left polar site)
open qQ9yWTb (Curve)
open qb0hmCe (CurveModel SiteTarget coeffHeight cLN specialize zD)
open P5_7_7 (phys)
open cu (L)
open E7 (CurvePlace)
open scoped Classical WithZero
structure Sheet {x :Input} {U:Finset K} (J:WordChart x U) {q:Curve}
    (C:CurveModel q) where
  f :C.E[X][X]
  irreducible :Irreducible f
  positive :0<f.natDegree
  normalized: (f.coeff f.natDegree).leadingCoeff=1
  marks :Finset K
  Bp:marks⊆U
  atPlace : ∀ γ∈marks,C.E →ₐ[L] LaurentSeries L
  place :K→CurvePlace L C.E
  distinct :Set.InjOn place (marks :Set K)
  value : ∀ γ (hγ:γ∈marks) c,
    (place γ).value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (atPlace γ hγ c)
  arc : ∀ γ (hγ:γ∈marks),∃ a :Fin 2→PowerSeries L,
    (∀ i,atPlace γ hγ (C.seed i)=(a i:LaurentSeries L)) ∧
    (∀ i,PowerSeries.constantCoeff (a i)=site x γ i) ∧
    (∃ i,PowerSeries.coeff 1 (a i)≠0)
  integral : ∀ γ (_:γ∈marks) i j,
    (place γ).value ((f.coeff i).coeff j)≤1
  root : ∀ γ (hγ:γ∈marks),specialize (cLN (atPlace γ hγ) 0 f) (J.P γ) (J.Q γ)=0
  separable : ∀ γ (hγ:γ∈marks),
    ((cLN (atPlace γ hγ) 0 f).map phys).Separable
  simple : ∀ γ (hγ:γ∈marks),
    specialize (cLN (atPlace γ hγ) 0 f).derivative (J.P γ) (J.Q γ)≠0
  num :K→ L[X]
  den:K→ L[X]
  den_ne : ∀ γ∈marks,den γ≠0
  reduced : ∀ γ∈marks,IsCoprime (num γ) (den γ)
  formula : ∀ γ (hγ:γ∈marks),
    phys (num γ)/phys (den γ)=zD (atPlace γ hγ) f (J.P γ) (J.Q γ)
abbrev Sheet.d {x :Input} {U:Finset K} {J:WordChart x U} {q:Curve} {C:CurveModel q}
    (S:Sheet J C) :=S.f.natDegree
abbrev Sheet.h {x :Input} {U:Finset K} {J:WordChart x U} {q:Curve} {C:CurveModel q}
    (S:Sheet J C) :=coeffHeight S.f
structure Prepared {x :Input} {U:Finset K} (J:WordChart x U) (q:Curve)
    (T:Finset K) (e W H :ℕ) where
  curve :CurveModel q
  n:ℕ
  part:Fin n→Sheet J curve
  inside : ∀ j,(part j).marks⊆T
  zJ: (T \ univ.biUnion (fun j=>(part j).marks)).card≤(7+2*e)*H*q.totalDegree
  degree : ∑ j,(part j).d≤e
  height : ∑ j,(part j).h≤H*q.totalDegree
  weight : ∀ j i,((part j).f.coeff i).natDegree +
    (part j).d*left J+i*(J.u₁-J.u₀)≤W∨(part j).f.coeff i=0
def poleOrderAt {x :Input} {U:Finset K} {J:WordChart x U} {q:Curve}
    {C:CurveModel q} (S:Sheet J C) (γ:K) :ℕ :=
  max (S.den γ).natDegree ((S.num γ).natDegree-P5_7_7.relativeDegree J γ)
def poleRate (e W:ℕ) :ℕ:=polar e W+(2*e-1)
def targetMatch (R:SiteTarget) {x :Input} {U:Finset K} (J:WordChart x U) (γ:K) :Prop :=
  let z :=site x γ R.coord
  let P:=R.a+R.b*z
  let Q:=R.c+R.d*z
  (P≠0∨Q≠0)∧(J.P γ).eval R.center*Q=(J.Q γ).eval R.center*P
def Sheet.direction {x :Input} {U:Finset K} {J:WordChart x U} {q:Curve} {C:CurveModel q}
    (S:Sheet J C) (γ:K) (i:Fin 2) :L :=
  if h:γ∈S.marks then (S.atPlace γ h (C.seed i)).coeff 1 else 0
def exception (R:SiteTarget) {x :Input} {U:Finset K} {J:WordChart x U}
    {q:Curve} {C:CurveModel q} (S:Sheet J C) (γ:K) :Prop :=
  targetMatch R J γ ∧ ¬ ((S.num γ).eval R.center=0↔R.det=0∨S.direction γ R.coord=0)
structure Starts {x :Input} {U:Finset K} (J:WordChart x U) where
  center :Fin 2→L
  distinct :center 0≠center 1
  a :Fin 2→L
  b:Fin 2→L
  c:Fin 2→L
  d:Fin 2→L
  invertible : ∀ i,a i*d i-b i*c i≠0
  target : ∀ γ∈U,∀ i,
    (J.P γ).eval (center i)*(c i+d i*site x γ i) =
      (J.Q γ).eval (center i)*(a i+b i*site x γ i)
end
end qH2fULd
end
section
set_option autoImplicit true
namespace qVkUX6a
noncomputable section
open Finset MvPolynomial
open cu (L)
open qQ9yWTb (Curve Usable)
open qe6nVeb (immersedAt)
open scoped Classical
open private count_factors filter_count usable_eval usable_mul from ProximityPrize.SubmissionLower.P5_7_1_7_5Split
open private bad_count from ProximityPrize.SubmissionLower.ZTV7u3a
private theorem usable_iff (q:Curve) (z :Fin 2→L) :
    Usable q z↔immersedAt q z := by
  have hc: (PowerSeries.C:L →+* PowerSeries L)=algebraMap L (PowerSeries L) :=
    RingHom.ext fun _=>PowerSeries.C_eq_algebraMap
  simp only [Usable,immersedAt,hc]
  exact exists_congr fun _=>and_congr_right fun _=>and_comm
theorem proof :qy95ATd.c6:= by
  intro T s hinj b hb cap
  let d := ⌊2*b⌋₊
  have hdb: (d:ℚ)≤2*b:=Nat.floor_le (by positivity)
  rcases qSQfSDc.proof T s hinj d with ⟨f,hf,hd,hz⟩ | ⟨U,hU,hcard,f,hf,hd,hs⟩
  · have hp (q:Curve) (hq:Irreducible q) (U:Finset P5.K) (hU:U⊆T)
        (hu : ∀ γ∈U,eval (s γ) q=0) :
        (U.card:ℚ)≤b*q.totalDegree+(1/3:ℚ)*(q.totalDegree :ℚ)^2 := by
      let V:=U.filter fun γ => ¬ Usable q (s γ)
      have hbad:=bad_count qYzLClc.proof qGzrWfb.proof
        (hinj.mono (show (U:Set P5.K)⊆T from hU)) hq hu
      rw [show (U.filter fun γ => ¬ immersedAt q (s γ))=V from
        filter_congr fun γ _=>not_congr (usable_iff q (s γ)).symm] at hbad
      have hbad' : 3*(V.card:ℚ)≤(q.totalDegree :ℚ)^2 := by
        rw [pow_two]
        exact_mod_cast hbad.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      have hgood:=filter_count hU (cap q hq)
      have hpart: (U.card:ℚ)=((U.filter fun γ=>Usable q (s γ)).card:ℚ)+V.card:= by
        exact_mod_cast (card_filter_add_card_filter_not
          (s :=U) (p:= fun γ=>Usable q (s γ))).symm
      linarith only [hbad',hgood,hpart]
    have H :=count_factors (fun q z=>eval z q=0) (fun _ _ h=>h)
      (fun _ _ _ h=>mul_eq_zero.mp (by simpa only [map_mul] using h))
      (by norm_num : (0:ℚ)≤1/3) hp f hf T Subset.rfl hz
    have hdeg: (f.totalDegree :ℚ)≤2*b:=(by exact_mod_cast hd: (f.totalDegree :ℚ)≤d).trans hdb
    have hlin:=mul_le_mul_of_nonneg_left hdeg hb
    have hsq:=pow_le_pow_left₀ (Nat.cast_nonneg f.totalDegree : (0:ℚ)≤_) hdeg 2
    linarith only [H,hlin,hsq]
  · have hp (q:Curve) (hq:Irreducible q) (V:Finset P5.K) (hV:V⊆T)
        (hv : ∀ γ∈V,Usable q (s γ)) :
        (V.card:ℚ)≤b*q.totalDegree+0*(q.totalDegree :ℚ)^2 := by
      have he :V.filter (fun γ=>Usable q (s γ))=V:=filter_true_of_mem hv
      simpa only [he,zero_mul,add_zero] using filter_count hV (cap q hq)
    have H :=count_factors Usable (fun _ _=>usable_eval) (fun _ _ _=>usable_mul)
      (le_refl (0:ℚ)) hp f hf U hU
      (fun γ hγ=>(usable_iff f (s γ)).mpr (qYzLClc.proof.1 f _ (hs γ hγ)))
    have hdeg: (f.totalDegree :ℚ)≤(d:ℚ)+1 := by exact_mod_cast hd
    have hmul :=mul_le_mul_of_nonneg_left hdeg hb
    have hb' : 2*b<(d:ℚ)+2 :=(Nat.lt_floor_add_one _).trans (by linarith)
    have hlt:=mul_lt_mul_of_pos_left hb' (by positivity :0<(d:ℚ)+1)
    have hcard' : ((d:ℚ)+1)*((d:ℚ)+2)≤2*(U.card:ℚ) := by exact_mod_cast hcard
    exfalso
    simp only [zero_mul,add_zero] at H
    linarith only [H,hmul,hlt,hcard']
end
end qVkUX6a
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qCReOzb
noncomputable section
open Finset
open scoped Classical
open P6_7_4 (wordLift)
open q6nKpZc (Input)
open P5_7_2 (introduction stages O2 anM)
open q7F2qKe (nV originBudget originCutter chosen_mem)
open qzVScmb (Origin last intro_guard)
open cu (Jet A5)
open DP (d3r d3q)


open akZ (aRJ ajz cN5 bLw)
open private avoid_divisors from ProximityPrize.SubmissionLower.Zr07w3a
private def eG {b:P5_7_2.fO} (i:Fin (last b)) :=(introduction b)[i.val]
theorem first_origins {b u del M Γ F} (x : @Input b u del M Γ F) (h:nV b 0∈stages b)
    {D:Finset Jet} (hD:aRJ (anchor x h) D)
    (hcap : ∀ j,ajz D j≤originBudget b 0 j) :Nonempty (Origins x D) := by
  let R (i:Fin (last b)) :=x.donors.initial (eG i) (List.getElem_mem i.isLt)
  let pass (f :Jet) (i:Fin (last b)) := ∀ j a,a≤(eG i).dI→f∣A5 j a (R i).jet
  let fail (f :Jet) (n:ℕ) :=n=last b ∨ ∃ hi:n<last b,¬ pass f ⟨n,hi⟩
  have ex (f :Jet) : ∃ n,fail f n:=⟨last b,Or.inl rfl⟩
  let o (f :Jet) :Origin b:=⟨Nat.find (ex f),Nat.lt_succ_of_le
    (Nat.find_min' (ex f) (Or.inl rfl))⟩
  have before (f :Jet) (i:Fin (last b)) (hi:i.val<(o f).val) :pass f i:= by
    by_contra hn
    exact Nat.find_min (ex f) hi (Or.inr ⟨i.isLt,hn⟩)
  have missing (f :Jet) (i:Fin (last b)) (he :i.val=(o f).val) : ¬ pass f i:= by
    rcases Nat.find_spec (ex f) with hn | ⟨hi,hn⟩
    · exact ((he.trans hn).not_lt i.isLt).elim
    · exact (Fin.ext he :i=⟨_,hi⟩).symm ▸ hn
  have ic (i:Fin (last b)) (j:Fin 2) {a :ℕ} (ha :a≤(eG i).dI) :
      A5 j a (R i).jet∈x.banks (eG i).shape (O2 (eG i).shape) := by
    have hr :=(R i).cfw
    have hm:=Nat.mul_le_mul_left (2*M.iF.toNat) ha
    have hW:anM M.iF.toNat (eG i).dI (eG i).shape +
        2*M.iF.toNat*a≤O2 (eG i).shape := by
      unfold anM O2 at *
      omega
    exact d3q x.crt (wordLift M) rfl rfl rfl le_rfl hW
      (atp.d3s x.crt (wordLift M) (chosen_mem (R i)) j a)
  have an1 (i:Fin (last b)) :
      ∃ q∈x.banks (eG i).shape (O2 (eG i).shape),
        ∀ f∈D.filter (fun f=>(o f).val=i.val),¬ f∣q:= by
    apply avoid_divisors
    intro f hf
    have hn:=missing f i (mem_filter.mp hf).2.symm
    dsimp only [pass] at hn
    push Not at hn
    obtain ⟨j,a,ha,hf⟩:=hn
    exact ⟨_,ic i j ha,hf⟩
  choose cut hmem hproper using an1
  let C (i:ℕ) :Jet:=if hi:i<last b then cut ⟨i,hi⟩ else 0
  refine ⟨⟨o,C,?_,?_,?_⟩⟩
  · suffices hh : ∀ n≤last b,∀ T⊆D,(∀ f∈T,n≤(o f).val) →
        ∀ j,ajz T j≤originBudget b n j by
      exact fun n hn j=>hh n hn _ (filter_subset _ _) (fun f hf=>(mem_filter.mp hf).2) j
    intro n
    induction n with
    | zero=>exact fun _ _ hs _ j=>(cN5 hs j).trans (hcap j)
    | succ n ih =>
      intro hn T hT hall j
      let i:Fin (last b) :=⟨n,Nat.lt_of_succ_le hn⟩
      have hc:=ih (Nat.le_of_succ_le hn) T hT (fun f hf=>(Nat.le_succ n).trans (hall f hf)) j
      have hs :=d3r x.crt (wordLift M) (chosen_mem (R i))
      have hr :=bLw (hD.mono hT) (R i).nonzero hs
        (intro_guard (List.getElem_mem i.isLt)).2 (eG i).dI
        (fun f hf=>before f i (hall f hf)) j
      unfold originBudget
      rw [List.take_succ_eq_append_getElem i.isLt,List.foldl_append]
      exact le_min hc hr
  · intro f hf he
    let i:Fin (last b) :=⟨(o f).val,he⟩
    have hC:C (o f)=cut i:=dite_eq_left he
    have hs :originCutter b (o f)=(eG i).shape := by
      rw [originCutter,List.getElem?_eq_getElem he]
      rfl
    rw [hC,hs]
    exact ⟨d3r x.crt (wordLift M) (hmem i),hproper i f (mem_filter.mpr ⟨hf,rfl⟩)⟩
  · intro i hi γ hγ
    change Mark F (if hm:i<last b then cut ⟨i,hm⟩ else 0) γ
    rw [dite_eq_left hi]
    unfold Mark
    have hr :=(R ⟨i,hi⟩).cfw
    exact aS3 x (by unfold O2; omega) (hmem ⟨i,hi⟩) γ hγ
end
end qCReOzb
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
namespace qCReOzb
noncomputable section
open Polynomial Finset
open scoped Classical BigOperators
open P6 (K jG)
open q6nKpZc (Input TopPair FixedTariff aAT I0)
open qzVScmb (last Guards guards gX)
open private aby tail_partition from ProximityPrize.SubmissionLower.ZODErLe
open P5_7_2 (A fO stages)
open q7F2qKe (origins isLast originBudget fibreShape nV earlyFee eHB akj)
open cu (Jet)
open gT (Ambient)
open pI (oU aaS a5I d2l)
open TD (J2)
open akZ (aRJ cVg yE ajz cN5)
def c1 :Prop :=
  ∀ (b:fO),2≤b.val → ∀ u del (M:jG u del) Γ (F:P1.bje A M Γ)
    (x :Input b M F) (h:nV b 0∈stages b) (D:Finset Jet),
    aRJ (anchor x h) D →
    (∀ f∈D,f.natDegree=0)→(∀ j,ajz D j≤originBudget b (last b) j) →
    ∃ gH :Finset K,gH.card≤eHB b ∧ ∀ f∈D,∀ γ∈Γ,Mark F f γ→γ∈gH
def c2 :Prop :=
  ∀ (b:fO),2≤b.val → ∀ u del (M:jG u del) Γ (F:P1.bje A M Γ)
    (x :Input b M F) (h:nV b 0∈stages b) (D:Finset Jet),
    TopPair M F b→aRJ (anchor x h) D →
    (∀ f∈D,0<f.natDegree)→(∀ j,ajz D j≤originBudget b (last b) j) →
    ∃ gH :Finset K,gH.card≤akj ∧ ∀ f∈D,Nonempty (LastCut F b gH f)
private theorem marked_fixed {b u del M Γ F} {x : @Input b u del M Γ F} {G:Guards b}
    (B:BankBook x G) {q:Ideal Ambient} {γ:K} (hγ:γ∈Γ) (hm:I0 F q γ)
    (hn : ¬ ∀ s (hs :s∈stages b),¬ aaS (B.fixed s hs).free.equation q ∧
      ¬ aaS (B.fixed s hs).moving.equation q) :γ∈B.gH := by
  push Not at hn
  obtain ⟨s,hs,hn⟩:=hn
  by_cases hf :aaS (B.fixed s hs).free.equation q
  · exact B.b3r s hs γ hγ (Or.inl (by
      simpa only [d2l] using RingHom.mem_ker.mp (hm hf)))
  · exact B.b3r s hs γ hγ (Or.inr (by
      simpa only [d2l] using RingHom.mem_ker.mp (hm (hn hf))))
private theorem build (ordinary_count:c1) (last_cuts :c2)
    {b u del M Γ F} (hb:2≤b.val) (x : @Input b u del M Γ F) (top:TopPair M F b)
    (uq:FixedTariff F b) (G:Guards b) :Nonempty (aAT F b x) := by
  obtain ⟨B⟩:=bank_book x G uq
  obtain ⟨D,hD,hcap,hroot⟩:=cVg B.anchor_strip
  have hstart : ∀ j,ajz D j≤originBudget b 0 j:=hcap
  obtain ⟨C⟩:=first_origins x G.anchor_mem hD hstart
  let O:=D.filter fun f=>(C.origin f).val=last b∧f.natDegree=0
  let V:=D.filter fun f=>(C.origin f).val=last b∧0<f.natDegree
  let T:=D \ O
  have hT:T⊆D:=sdiff_subset
  have tail_last (E :Finset Jet) (hE :E⊆D)
      (he : ∀ f∈E,(C.origin f).val=last b) (j:Fin 3) :
      ajz E j≤originBudget b (last b) j :=
    (cN5 (fun f hf=>mem_filter.mpr ⟨hE hf,(he f hf).ge⟩) j).trans (C.tail _ le_rfl j)
  have ho:=tail_last O (filter_subset _ _) (fun _ hf=>(mem_filter.mp hf).2.1)
  have hv :=tail_last V (filter_subset _ _) (fun _ hf=>(mem_filter.mp hf).2.1)
  obtain ⟨iy,hordinary,ordinary_cov⟩:=ordinary_count b hb u del M Γ F x G.anchor_mem O
    (hD.mono (filter_subset _ _)) (fun _ hf=>(mem_filter.mp hf).2.2) ho
  obtain ⟨singular,hsingular,cuts⟩:=last_cuts b hb u del M Γ F x G.anchor_mem V top
    (hD.mono (filter_subset _ _)) (fun _ hf=>(mem_filter.mp hf).2.2) hv
  let be1 (f :Jet) (hf :f∈V) :=Classical.choice (cuts f hf)
  let factors (o:ℕ) :=T.filter fun f=>(C.origin f).val=o
  let res (_:ℕ) (f :Jet) :=if hf :f∈V then (be1 f hf).line else false
  let lines (_:ℕ) (f :Jet) :=if hf :f∈V then
    if (be1 f hf).line then Γ.filter (LineRoot F (be1 f hf).row) else ∅ else ∅
  let cut (o:ℕ) (f :Jet) :=
    if o<last b then C.cut o else if hf :f∈V then (be1 f hf).cut else 0
  have cqz {o f} (hf :f∈factors o) :f∈T∧(C.origin f).val=o:=mem_filter.mp hf
  have late_eq {o f} (hf :f∈factors o) (hl : ¬ o<last b) :o=last b:= by
    have hs :=(C.origin f).isLt
    rw [(cqz hf).2] at hs
    change o<last b+1 at hs
    omega
  have late_mem {o f} (hf :f∈factors o) (hl:o=last b) :f∈V:= by
    obtain ⟨hf,he⟩:=cqz hf
    obtain ⟨hd,hn⟩:=mem_sdiff.mp hf
    refine mem_filter.mpr ⟨hd,he.trans hl,Nat.pos_of_ne_zero ?_⟩
    intro hz
    exact hn (mem_filter.mpr ⟨hd,he.trans hl,hz⟩)
  have individual {f :Jet} (hf :f∈V) (j:Fin 3) :
      yE f j≤originBudget b (last b) j :=
    (single_le_sum (fun _ _=>Nat.zero_le _) hf).trans (hv j)
  have firstIrred (o) (_:o∈origins b) f (hf :f∈factors o) :=
    hD.factors f (hT (cqz hf).1)
  have proper (o) (_:o∈origins b) f (hf :f∈factors o) :
      oU (cut o f) (fibreShape b o (res o f)) ∧ ¬ f∣cut o f := by
    by_cases h:o<last b
    · have he :=(cqz hf).2
      have hn:f∉V:= fun hv=>h.ne (he.symm.trans (mem_filter.mp hv).2.1)
      have hp:=C.proper f (hT (cqz hf).1) (he.symm ▸ h)
      simpa only [cut,ite_eq_left h,res,dite_eq_right hn,fibreShape,Bool.false_eq_true,
        ite_false,he] using hp
    · have he :=late_eq hf h
      have hm:=late_mem hf he
      have hp:=aby (individual hm) (be1 f hm).line (be1 f hm).caps
      have hc:cut o f=(be1 f hm).cut:= by simp only [cut,ite_eq_right h,dite_eq_left hm]
      have hr :res o f=(be1 f hm).line :=dite_eq_left hm
      rw [hc,hr,he]
      exact ⟨hp,(be1 f hm).proper⟩
  have rescue (o) (_:o∈origins b) f (hf :f∈factors o) (hr :res o f=true) :
      isLast b o ∧ ∀ j,0<yE f j:= by
    by_cases hv :f∈V
    · have he :o=last b:=(cqz hf).2.symm.trans (mem_filter.mp hv).2.1
      have hl: (be1 f hv).line=true := by simpa only [res,dite_eq_left hv] using hr
      have hJ:0<yE f 1 :=(mem_filter.mp hv).2.2
      have hirr :=(hD.factors f (hT (cqz hf).1)).1
      exact ⟨he,fun j=> by
        fin_cases j
        · exact hJ.trans_le (akZ.caQ hirr.ne_zero)
        · exact hJ
        · exact (be1 f hv).line_pos hl⟩
    · simp [res,hv] at hr
  have tail:=tail_partition hT C.origin C.tail
  obtain ⟨P⟩:=geometric_cover F G factors cut res
    (fun o ho f hf=>(firstIrred o ho f hf).1) proper
    (fun o ho f hf hr=>(rescue o ho f hf hr).1) tail
  let good (q:Ideal Ambient) := ∀ s (hs :s∈stages b),¬ aaS (B.fixed s hs).free.equation q ∧
    ¬ aaS (B.fixed s hs).moving.equation q
  let parents (o:ℕ) (f :Jet) :=(P.Bp o f).filter good
  have hsub o f :parents o f⊆P.Bp o f :=filter_subset _ _
  let zo:=B.gH∪iy∪singular∪P.gH
  refine ⟨{
    factors :=factors,parents :=parents,cut:=cut,rescue :=res,line :=lines,zo:=zo
    fixed:=B.fixed
    firstFactor := fun o ho f hf=>⟨(firstIrred o ho f hf).1,(firstIrred o ho f hf).2.2.1,
      G.anchor_mem,(firstIrred o ho f hf).2.1⟩
    tail:=tail
    rescue_last :=rescue
    line_price := ?_
    proper :=proper
    nonlast_common := ?_
    DN := ?_
    parent_unique := fun o ho f hf i hi g hg q hq hq' =>
      P.unique o ho f hf i hi g hg q (hsub o f hq) (hsub i g hq')
    factor_cap := ?_
    mass_cap := ?_
    early_price := ?_
    Eh := ?_ }⟩
  · intro o ho f hf
    by_cases h:f∈V
    · cases hl: (be1 f h).line
      · simp [lines,res,h,hl]
      · simpa only [lines,res,dite_eq_left h,hl,ite_true] using
          line_count x.vo (mem_filter.mp h).2.2 ((be1 f h).line_pos hl)
            ((be1 f h).line_caps hl)
    · simp [lines,res,h]
  · intro o ho hl f hf g hg
    have hh:o<last b:=lt_of_le_of_ne (Nat.le_of_lt_succ (mem_range.mp ho)) hl
    simp only [cut,ite_eq_left hh]
  · intro o ho f hf q hq
    obtain ⟨ha,hh,hf,hcut⟩:=P.geom o ho f hf q (hsub o f hq)
    exact ⟨ha,hh,hf,hcut,(mem_filter.mp hq).2⟩
  · intro o ho f hf k
    unfold J2
    exact_mod_cast (a5I (hsub o f) k).trans (P.local_mass o ho f hf k)
  · intro k
    have h:=(sum_le_sum fun o (_:o∈origins b) =>
      sum_le_sum fun f (_:f∈factors o)=>a5I (hsub o f) k).trans (P.total_mass k)
    unfold J2
    exact_mod_cast h
  · have hb:=gX (gX (gX B.bound hordinary) hsingular) P.paid_bound
    dsimp only [zo]
    unfold earlyFee
    omega
  · intro γ hγ
    have use (o) (ho:o∈origins b) (f) (hf :f∈factors o) (hz :Mark F f γ)
        (hc:Mark F (cut o f) γ) :
        γ∈zo ∨ ∃ i∈origins b,∃ g∈factors i,
          γ∈lines i g ∨ ∃ q∈parents i g,I0 F q γ:= by
      rcases P.Eh o ho f hf γ hγ hz hc with hp | ⟨i,hi,g,hg,q,hq,hm⟩
      · exact Or.inl (mem_union_right _ hp)
      · by_cases h:good q
        · exact Or.inr ⟨i,hi,g,hg,Or.inr ⟨q,mem_filter.mpr ⟨hq,h⟩,hm⟩⟩
        · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _
            (marked_fixed B hγ hm h))))
    let R:=(x.donors.staged _ G.anchor_mem).free
    have hz :Mark F (anchor x G.anchor_mem) γ :=
      aS3 x (by have hr :=R.cfw; unfold P5_7_2.anM P5_7_2.O2; omega)
        (q7F2qKe.chosen_mem R) γ hγ
    rcases B.anchor_strip.Eh _ _ hz with h | h | h
    · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (B.content_paid γ hγ h))))
    · exact Or.inl (mem_union_left _ (mem_union_left _
        (mem_union_left _ (B.b3r _ G.anchor_mem γ hγ (Or.inl h)))))
    obtain ⟨f,hf,hz⟩:=hroot _ _ h
    by_cases ho:f∈O
    · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ (ordinary_cov f ho γ hγ hz))))
    let o:=(C.origin f).val
    have horg:o∈origins b:=mem_range.mpr (C.origin f).isLt
    have hm:f∈factors o:=mem_filter.mpr ⟨mem_sdiff.mpr ⟨hf,ho⟩,rfl⟩
    by_cases hl:o<last b
    · exact use o horg f hm hz (by simpa only [cut,ite_eq_left hl] using C.zero o hl γ hγ)
    have hf :=late_mem hm (late_eq hm hl)
    rcases (be1 f hf).Eh γ hγ hz with h | h | ⟨he,hr⟩
    · exact Or.inl (mem_union_left _ (mem_union_right _ h))
    · exact use o horg f hm hz (by simpa only [cut,ite_eq_right hl,dite_eq_left hf] using h)
    · exact Or.inr ⟨o,horg,f,hm,Or.inl (by
        simpa only [lines,dite_eq_left hf,he,ite_true] using mem_filter.mpr ⟨hγ,hr⟩)⟩
theorem of_children (h1 :c1) (h2 :c2) :q6nKpZc.c2 := by
  intro b hb u del M Γ F x top uq
  exact build h1 h2 hb x top uq (guards b)
end
end qCReOzb
end
section
set_option autoImplicit true
namespace qVrMoId
theorem proof :qDDNOOe.c1 := fun b hb o ho j hj hl =>
  qVu1nGe.proof b (by omega) o ho j hj hl
end qVrMoId
end
section
set_option autoImplicit true
namespace qY77wKd
theorem proof :qDDNOOe.c2 := fun b hb o ho j hj hl =>
  qVu1nGe.proof b (by omega) o ho j hj hl
end qY77wKd
end
section
set_option autoImplicit true
namespace qS2g9bc
theorem proof :qDDNOOe.c3:= fun b hb o ho j hj hl =>
  qVu1nGe.proof b (by omega) o ho j hj hl
end qS2g9bc
end
section
set_option autoImplicit true
namespace qUIDgfe
theorem proof :qDDNOOe.c4 := fun b hb o ho j hj hl =>
  qVu1nGe.proof b (by omega) o ho j hj hl
end qUIDgfe
end
section
set_option autoImplicit true
namespace qb5SUPb
theorem proof :qDDNOOe.c5:= fun b hb o ho j hj hl =>
  qVu1nGe.proof b (by omega) o ho j hj hl
end qb5SUPb
end
