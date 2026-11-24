import ProximityPrize.SubmissionLower.AD
set_option Elab.async false
set_option maxRecDepth 12000
open _root_ renaming Algebra.algebraMap→c9,Fin.last→lI,Finset→cy,Finset.range→lz,IsCoprime→lJ,MvPolynomial→aU,MvPolynomial.eval→mD,Polynomial.Bivariate.swap→ oj,Polynomial.C→nq,PolynomialDifferential.DifferentialPolynomial→lV,ProximityPrize.Benchmark.IRSProfile.domain→nI,ReedSolomon.closePolynomialSet→nX,add_sub_cancel_right→n5
set_option autoImplicit true
section
namespace bar
noncomputable section
open MvPolynomial
open scoped MonomialOrder BigOperators
variable {k σ:Type*} [Field k] [Finite σ]
theorem d38 (I:Ideal (aU σ k)) (g:aU σ k) :
    ∃ C:ℕ,∀ f∈I ⊔ Ideal.span {g},∃ q:aU σ k,
      f - q*g∈I∧q.totalDegree≤f.totalDegree+C:= by
  classical
  let:=Fintype.ofFinite σ
  let:LinearOrder σ:=LinearOrder.lift' _ (Fintype.equivFin σ).injective
  let:WellFoundedGT σ:=Finite.to_wellFoundedGT
  let m:MonomialOrder σ:=MonomialOrder.degLex
  let J:=I ⊔ Ideal.span {g}
  obtain ⟨E,hE⟩:=m.exists_finset_standardExponents_iff J
  have hex (e :E) : ∃ b∈J,b≠0∧m.degree b≤(e :σ →₀ ℕ) := by
    by_contra! h
    have hs : (e :σ →₀ ℕ)∈m.standardExponents J:= fun b hb hn=>h b hb hn
    exact (hE _).mp hs _ e.property le_rfl
  choose b hb hn he using hex
  let B:Set (aU σ k) :=Set.range b
  let:Fintype B:=(Set.finite_range b).fintype
  have hB (x :B) : (x :aU σ k)∈J∧(x :aU σ k)≠0:= by
    obtain ⟨e,h⟩:=x.property
    rw [← h]
    exact ⟨hb e,hn e⟩
  have hrep (x :B) : ∃ q:aU σ k,(x :aU σ k) - q*g∈I:= by
    obtain ⟨i,hi,j,hj,hij⟩:=Submodule.mem_sup.mp (hB x).1
    obtain ⟨q,rfl⟩:=Ideal.mem_span_singleton.mp hj
    refine ⟨q,?_⟩
    rw [← hij,mul_comm g q,n5]
    exact hi
  choose a ha using hrep
  refine ⟨Finset.univ.sup fun x :B=>(a x).totalDegree,?_⟩
  intro f hf
  obtain ⟨c,r,hfr,hc,hr⟩ :=
    m.div_set (B:=B) (fun x hx=>m.isUnit_leadingCoeff.mpr (hB ⟨x,hx⟩).2) f
  rw [Finsupp.linearCombination_apply,Finsupp.sum] at hfr
  have hsum : ∑ x∈c.support,c x•(x :aU σ k)∈J :=
    J.sum_mem fun x _=>J.smul_mem (c x) (hB x).1
  have hrJ:r∈J:= by
    convert J.sub_mem hf hsum using 1
    rw [hfr,add_comm,n5]
  have hr0:r=0:= by
    by_contra hr0
    have hstd:m.degree r∈m.standardExponents J:= by
      apply (hE _).mpr
      intro e heE hle
      exact hr _ (m.degree_mem_support hr0) (b ⟨e,heE⟩) ⟨⟨e,heE⟩,rfl⟩
        ((he ⟨e,heE⟩).trans hle)
    exact hstd r hrJ hr0 le_rfl
  refine ⟨∑ x∈c.support,c x*a x,?_,?_⟩
  · rw [Finset.sum_mul,hfr,hr0,add_zero,← Finset.sum_sub_distrib]
    exact I.sum_mem fun x _=> by
      simpa only [smul_eq_mul,mul_sub,mul_assoc] using I.mul_mem_left (c x) (ha x)
  · apply totalDegree_finsetSum_le
    intro x _
    have hcx : (c x).totalDegree≤f.totalDegree := by
      by_cases hx :c x=0
      · simp [hx]
      have hx' := m.totalDegree_le_of_degree_le
        (fun _ _ h=>degree_le_degree_of_degLex_le h) (hc x)
      rw [totalDegree_mul_of_isDomain (hB x).2 hx] at hx'
      omega
    exact (totalDegree_mul _ _).trans
      (Nat.add_le_add hcx (Finset.le_sup (f := fun y :B=>(a y).totalDegree) (Finset.mem_univ x)))
end
end bar
end
section
namespace i4
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators
abbrev K:=gR.Native.K
abbrev Node :=gR.Native.I
abbrev node :=nI
abbrev p:ℕ:=2130706433
abbrev n:ℕ:=262144
abbrev k :ℕ:=131072
abbrev N :ℕ:=131071
abbrev Jet:=Sigma fun _:ℕ=>Sigma fun _:ℕ=>ℕ
def Jet.a (j:Jet) :ℕ:=j.2.2
def Jet.b (j:Jet) :ℕ:=j.2.1
def Jet.c (j:Jet) :ℕ:=j.1
def Jet.q (j:Jet) :ℕ:=j.a+j.b+j.c
def Jet.v (j:Jet) :ℕ:=j.b+2*j.c
structure Source where
 m:ℕ
 B:ℕ
 J:ℕ
 C:ℕ
 E :cy Jet
def aH1 (B J C:ℕ) :cy Jet :=
  (lz (C+1)).sigma fun c =>
    (lz (J - 2*c+1)).sigma fun b=>lz (B-(b+c)+1)
structure Rz (s :Source) :Prop where
 multiplicity :0<s.m
 top_pos :0<s.C
 index_top:2*s.C≤ s.J
 aQV:s.J≤ s.B
 characteristic:max N (s.B*(s.B-1))<p
 support : ∀ j∈s.E,j.q≤ s.B∧j.v≤ s.J∧j.c≤ s.C
 lower : ∀ j∈s.E,0<j.a→(⟨j.c,j.b,j.a-1⟩:Jet)∈s.E
def errors (A:ℕ) :=n - A
def gap (A:ℕ) :=A-N
structure aRk (A:ℕ) :Prop where
 gt_degree :N<A
 lt_length:A<n
 one_le_beta :gap A≤errors A
 beta_lt_two:errors A<2*gap A
def width (A:ℕ) (s :Source) (j:Jet) :=s.m*A-N*j.q+j.v
abbrev apU (A:ℕ) (s :Source) :=(j:s.E)×Fin (width A s j.val)
def column (A:ℕ) (s :Source) (i:apU A s) :SourceColumn 2 :=
 ⟨i.2.val,i.1.val.a,![i.1.val.b,i.1.val.c]⟩
def aWf (A:ℕ) (s :Source) :ℕ :=
 (localConstraintMatrix s.m (fun _:Unit=>(0:ZMod p)) (fun _=>0) (column A s)).rank
def Vv (A:ℕ) (s :Source) (w:Node→K) :ℕ :=
 (localConstraintMatrix s.m (fun i=>node i) w (column A s)).rank
def aCq (m q:ℕ) (g:ℤ) :cy Jet :=
  ((lz (q+1)).sigma fun c =>
    (lz (q-c+1)).sigma fun b => {q-(b+c)}).filter fun j:Jet =>
      0≤g+(j.v :ℤ)+3*(j.a :ℤ)∧g+(j.v :ℤ)+3*(j.a :ℤ)<(m:ℤ)
def aTf (s :Source) (q:ℕ) (g:ℤ) :cy Jet :=
 s.E.filter fun j=>j.q=q∧0≤g+(j.v :ℤ)
def alu (row col:Jet) :ZMod p :=
 if col.b≤ row.b∧col.c≤ row.c∧row.a+(row.b-col.b)+(row.c-col.c)=col.a
 then (-1)^(row.c-col.c)*(col.a.choose row.a :ℕ)*((col.a-row.a).choose (row.b-col.b) :ℕ)
 else 0
def GU (s :Source) (q:ℕ) (g:ℤ) :
    Matrix (aCq s.m q g) (aTf s q g) (ZMod p) :=
  fun r c=>alu r.val c.val
def aWw (s :Source) (cut:ℕ) :ℕ :=
  ∑ q∈lz cut,∑ u∈lz (s.m+s.J-q),
    (GU s q ((u:ℤ) - s.J)).rank
def axY (s :Source) (cut:ℕ) :Prop :=
 ∀ j∈s.E,cut≤j.q→s.m≤j.a
def t:ℕ:=max (2*k-7) (k-2)
def t₁:ℕ:=2*k-5
def a₀ (s :Source) :=1+t*(s.B-1)
def D (s :Source) :=t*(s.J-2)+k-1
def e (s :Source) :=min (t*(s.C-1)+k-2) (D s/2)
def R₂ (s :Source) :=
  (s.C*D s+e s*s.J - 2*s.C*e s)*(2*a₀ s - D s) +
    e s*(D s-e s)*(2*s.B-s.J)
def H (s :Source) :=max s.B ((2*s.C-1)*s.B - s.C^2)
def I₁ (s :Source) :=max s.J ((2*s.C-1)*s.J - 2*s.C^2)
def a₁ (s :Source) :=1+t₁*(H s-1)
def d₁ (s :Source) :=min (a₁ s) (t₁*(I₁ s-1)+k-1)
def R₁ (s :Source) :=H s*d₁ s+I₁ s*a₁ s - I₁ s*d₁ s
def bCu (A:ℕ) (s :Source) :=
 errors A*(2*R₂ s+R₁ s)+gap A*(s.B+H s^2)
def L (A:ℕ) (s :Source) :=(bCu A s+(gap A-1))/gap A
abbrev close (A:ℕ) (w:Node→K) :=nX node w k A
def axW (A cap:ℕ) :Prop :=
 ∀ w:Node→K,(close A w).Finite∧(close A w).ncard≤ cap
def indexWeight {r :ℕ} : JetVariable r→ℕ:= fun j=>j.elim 0 Fin.val
def ato (s :Source) (Q:lV K 2) :Prop :=
  Q≠0∧jetTotalDegree Q≤ s.B∧Q.weightedTotalDegree indexWeight≤ s.J ∧
    jetDegree Q (lI 2)≤ s.C
def bRZ (s :Source) (Q:lV K 1) :Prop :=
 Q≠0∧jetTotalDegree Q≤H s∧jetDegree Q (lI 1)≤I₁ s
def ae8 {r :ℕ} (Q:lV K r) (f :K[X]) :Prop :=
  ∃ G:lV K r,Irreducible G∧G∣Q ∧
    differentialSpecialization G f=0∧differentialSpecialization (separant G (lI r)) f≠0
abbrev FX:=FractionRing K[X]
abbrev nU:=AlgebraicClosure FX
abbrev jo:=aU (Fin k) nU
abbrev BL (r :ℕ) :=aU (Fin (r+1)) nU
def embed:K →+* nU :=
 (c9 FX nU).comp ((c9 K[X] FX).comp nq)
def center :nU:=c9 FX nU (c9 K[X] FX Polynomial.X)
def Gp (f :K[X]) (i:Fin k) :nU:=embed (f.coeff i.val)
def awb (y :Fin k→nU) (j:ℕ) :nU :=
 ∑ i:Fin k,(i.val.choose j:nU)*center^(i.val-j)*y i
structure Chart (r :ℕ) where
 equation :BL r
 denominator :BL r
 numerator :Fin k→BL r
def Chart.aa0 {r} (T:Chart r) :Set (Fin (r+1)→nU) :=
 {u | mD u T.equation=0∧mD u T.denominator≠0}
def Chart.output {r} (T:Chart r) (u:Fin (r+1)→nU) (i:Fin k) :nU :=
 mD u (T.numerator i)/mD u T.denominator
def Chart.aN8 {r} (T:Chart r) :=T.output '' T.aa0
def Chart.ideal {r} (T:Chart r) :Ideal jo:=MvPolynomial.vanishingIdeal nU T.aN8
structure aAQ {r} (T:Chart r) :Prop where
 irreducible :Irreducible T.equation
 nonvanishing : ¬ T.equation∣T.denominator
 recover : ∀ u∈T.aa0,∀ j:Fin (r+1),awb (T.output u) j.val=u j
structure Family (r :ℕ) where
 count:ℕ
 bY:Fin count→Chart r
def bHP (s :Source) (P:BL 2) :Prop :=
 P.totalDegree≤a₀ s∧P.weightedTotalDegree Fin.val≤D s∧P.degreeOf (lI 2)≤e s
def aOa (s :Source) (P:BL 1) :Prop :=
 P.totalDegree≤a₁ s∧P.degreeOf (lI 1)≤d₁ s
structure bQQ (s :Source) (F:Family 2) :Prop where
 count:F.count≤ s.B
 bct : ∀ i,aAQ (F.bY i)
 total: (∑ i,(F.bY i).equation.totalDegree)≤ s.B
 index : (∑ i,(F.bY i).equation.weightedTotalDegree Fin.val)≤ s.J
 top: (∑ i,(F.bY i).equation.degreeOf (lI 2))≤ s.C
 bands : ∀ i,bHP s (F.bY i).denominator ∧ ∀ j,bHP s ((F.bY i).numerator j)
structure cxu (s :Source) (F:Family 1) :Prop where
 count:F.count≤H s
 bct : ∀ i,aAQ (F.bY i)
 total: (∑ i,(F.bY i).equation.totalDegree)≤H s
 index : (∑ i,(F.bY i).equation.degreeOf (lI 1))≤I₁ s
 bands : ∀ i,aOa s (F.bY i).denominator ∧ ∀ j,aOa s ((F.bY i).numerator j)
def cxn {r} (F:Family r) (Q:lV K r) :Prop :=
 ∀ f :K[X],f.degree<k→ae8 Q f → ∃ i,Gp f∈(F.bY i).aN8
structure bQ7 {r} (F:Family r) (budget:ℕ) :Prop where
 prime : ∀ i,(F.bY i).ideal.IsPrime
 dimension : ∀ i,(MvPolynomial.affineHilbertPolynomial (F.bY i).ideal).natDegree=r
 total: (∑ i,MvPolynomial.affineDegree (F.bY i).ideal)≤(budget:ℚ)
end
end i4
end
section
namespace i4
noncomputable section
open Finset
open scoped BigOperators
theorem b8U {B J C:ℕ} (hBJ:J≤B) (hJC:2*C≤J) (j:Jet) :
  j∈aH1 B J C↔j.q≤B∧j.v≤J∧j.c≤C:= by
 rcases j with ⟨c,b,a⟩
 simp only [aH1,mem_sigma,mem_range,Jet.q,Jet.v,Jet.c,Jet.b,Jet.a]
 omega
end
end i4
end
section
set_option backward.isDefEq.respectTransparency false
namespace P0
noncomputable section
open Polynomial Matrix CoreDefinitions Code
open gR
open ProximityPrize.Benchmark
open scoped BigOperators NNReal
abbrev K:=Native.K
abbrev I:=Native.I
abbrev e9:=Fin 2→ I→K
abbrev node :=nI
abbrev p:=Native.p
abbrev blockLength:ℕ:=262144
abbrev k :ℕ:=131072
abbrev dw:ℕ:=180217
abbrev t:ℕ:=blockLength - dw
abbrev L:ℕ:=dw - k
abbrev b39:ℕ:=16
abbrev DY:ℕ:=t+1 - L-(b39+1)
abbrev ajO:ℤ:=2480
abbrev LM:ℕ:=31973440934878498
def blf :Prop :=
  ∀ word:I→K,
    let S:=nX node word (k+1) dw
    S.Finite∧S.ncard≤LM
abbrev kB:=Bx.lN K
abbrev nC:=Polynomial K[X]
structure B5 (u:e9) (γ:K) where
 support :cy I
 decoder :K[X]
 dw:P0.dw≤ support.card
 degree :decoder.degree<k
 lg : ∀ i∈support,decoder.eval (node i)=u 0 i+γ*u 1 i
 nonjoint : ¬ (NM node (u 0) k support∧NM node (u 1) k support)
def iy (u:e9) := QO node (u 0) (u 1) L t
def So (u:e9) :=AI p node (u 0) (u 1) L t
def aDf (u:e9) :=Bx.adJ (iy u)
def Vv (u:e9) :=Bx.adJ (So u)
def R5 (u:e9) :=Bx.ay6 (So u)
def aB8 (u:e9) :Prop :=
 Principal.bTJ node (u 0) (u 1) k p
def aKm (u:e9) :Prop :=
  ∃ (a :ℕ) (g:kB[X]),g≠0∧g.natDegree≤a∧a≤t ∧
    ∀ P:kB[X],P.natDegree≤t →
      (((So u).map (c9 K[X] kB)).mulVec (fun i=>P.coeff i.val)=0 ↔
        ∃ Q:kB[X],Q.natDegree≤t - a∧P=g*Q)
def ayo {F ι:Type} [Field F] [Fintype ι] [DecidableEq ι]
    (p:ℕ) (x u v :ι→F) (l t:ℕ) :Matrix (Fin 4×Fin l) (Fin (t+1)) F :=
  fun i j =>
    if i.1=0 then oX x u (i.2.val+j.val) else
    if i.1=1 then oX x v (i.2.val+j.val) else
    if i.1=2 then oX x u (i.2.val+j.val)^p else
      oX x v (i.2.val+j.val)^p
abbrev bcD (u:e9) :=ayo p node (u 0) (u 1) L t
def aYx (u:e9) :Prop :=
 Vv u=(bcD u).rank
def abC (u:e9) :Prop :=
  b39<R5 u∧aDf u=L ∧ ¬ aB8 u ∧
    ¬ aKm u ∧ ¬ aYx u
structure qo (u:e9) where
 a :ℕ
 b:ℕ
 c:ℕ
 ab:a≤b
 active :b≤t
 inactive :t<c
 top:c≤k
 degreeSum:a+b+c=2*k+2
 nullitySum:R5 u+a+b=2*(t+1)
 level :kL.aKl
   (fun s j=>c9 K[X] kB (Principal.P8 p node (u 0) (u 1) s j))
   k a b c
def qo.height {u:e9} (T:qo u) :=(k+1) - T.c
abbrev Relation {u:e9} (T:qo u) :=
 kL.axT p node (u 0) (u 1) k T.height
def sZ (U:nC) :kB[X] :=
 U.map (c9 K[X] kB)
def aiE {F:Type} [Field F] (G U V:F[X]) :Prop :=
 G≠0∧G∣U∧G∣V ∧ ∀ H :F[X],H∣U→H∣V→H∣G
def vn (P:nC) (γ:K) :K[X] :=P.map (evalRingHom γ)
def seed :nC:=nq (R:=K[X]) (Polynomial.X (R:=K))
def jH (P:K[X]) :nC:=P.map nq
def twist:K →+* K:=frobenius K p
def uO (a₀ a₁:K[X]) :ℕ:=max a₀.natDegree a₁.natDegree
def Ox (a :K[X]) :K[X] :=
 ∏ j:Fin 6,a.map (iterateFrobenius K p j.val)
def Xb (U V:nC) :ℕ :=
  Module.finrank kB (Submodule.span kB (Set.range fun j:Fin 4 =>
    sZ (oj
     (if j=0 then U else if j=1 then seed*U else if j=2 then V else seed^p*V))))
def _root_.aSg.ajp (q:ℕ) (U V:nC) :ℕ :=
  Module.finrank kB (Submodule.span kB (Set.range fun j:Fin 4 =>
    sZ (oj
     (if j=0 then U else if j=1 then seed*U else if j=2 then V else seed^q*V))))
def JO (a :K[X]) (β:Fin 2→K[X]) :nC :=
 jH a*(jH ((β 0).map twist)+seed^p*jH ((β 1).map twist))
def _root_.aSg.NJ (q:ℕ) (a :K[X]) (β:Fin 2→K[X]) :nC :=
 jH a*(jH ((β 0).map twist)+seed^q*jH ((β 1).map twist))
def J9 (b:K[X]) (α:Fin 2→K[X]) :nC :=
 -(jH b*(jH (α 0)+seed*jH (α 1)))
def Z4 (U V U' V' : nC) :Prop :=U*V' = V*U'
def ake (u:e9) (deleted:cy I) (U V output :nC) :Prop :=
  ∀ i∉deleted,
    U.eval (C (node i))*(C (u 0 i)+Polynomial.X (R:=K)*C (u 1 i)) +
    V.eval (C (node i))*(C (u 0 i^p)+Polynomial.X (R:=K)^p*C (u 1 i^p)) =
      output.eval (C (node i))
def _root_.aSg.ad9 (q:ℕ) (u:e9) (deleted:cy I) (U V output :nC) :Prop :=
  ∀ i∉deleted,
    U.eval (C (node i))*(C (u 0 i)+Polynomial.X (R:=K)*C (u 1 i)) +
    V.eval (C (node i))*(C (u 0 i^q)+Polynomial.X (R:=K)^q*C (u 1 i^q)) =
      output.eval (C (node i))
structure jG (u:e9) (deleted:cy I) where
 shift:K
 pencil₀:K[X]
 pencil₁:K[X]
 pencil₀_degree :pencil₀.degree<k
 pencil₁_degree :pencil₁.degree<k
 E :K[X]
 factor :K[X]
 Q:K[X]
 A₀:K[X]
 A₁:K[X]
 word:I→K
 word_fixed : ∀ i,twist (word i)=word i
 word_deleted : ∀ i∈deleted,word i=0
 E_monic:E.Monic
 aFF : ∀ i,E.eval (node i)≠0
 factor_nodes : ∀ i∉deleted,factor.eval (node i)≠0
 coprime_factor :lJ E factor
 offset_proper :Q.degree<E.degree
 offset_reduced:lJ Q E
 adjacent_coprime :lJ E (E.map twist)
 amplitudes_primitive :lJ A₀ A₁
 first_amplitude_unit :lJ A₀ E
 aVi:E.natDegree+uO A₀ A₁≤DY
 first_word : ∀ i∉deleted,
   E.eval (node i)*(u 0 i+shift*u 1 i - pencil₀.eval (node i)) =
     factor.eval (node i)*A₀.eval (node i)*word i
 second_word : ∀ i∉deleted,
   E.eval (node i)*(u 1 i - pencil₁.eval (node i)) =
     Q.eval (node i)+factor.eval (node i)*A₁.eval (node i)*word i
def jG.iF {u deleted} (M:jG u deleted) :ℤ :=
 (M.E.natDegree :ℤ)-M.factor.natDegree - uO M.A₀ M.A₁
def jG.label {u deleted} (M:jG u deleted) (γ:K) :K :=
 γ-M.shift
def jG.wK {u deleted} (M:jG u deleted) (γ:K) :K[X] :=
 M.A₀+Polynomial.C (M.label γ)*M.A₁
def jG.decoder {u deleted} (M:jG u deleted) {γ:K}
    (B:B5 u γ) :K[X] :=
  B.decoder-M.pencil₀-Polynomial.C (M.label γ)*M.pencil₁
end
end P0
end
section
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
namespace P0
noncomputable section
open Polynomial Code LinearCode CoreDefinitions ToyProblem
open gR ProximityPrize.Benchmark
open yP.baR yP.a92
open scoped NNReal
private theorem ard {a i j x y u v z w e s :ℕ}
  (hi:a^i≤x*2^u) (hj:a^j≤y*2^v)
  (hc:x*y≤z*2^w) (he :i+j=e) (hs :u+v+w=s) :
  a^e≤z*2^s := by
 subst e
 subst s
 calc
  a^(i+j)=a^i*a^j:=pow_add ..
  _≤(x*2^u)*(y*2^v) :=Nat.mul_le_mul hi hj
  _=(x*y)*2^(u+v) := by rw [pow_add]; ac_rfl
  _≤(z*2^w)*2^(u+v) :=Nat.mul_le_mul_right _ hc
  _=z*(2^(u+v)*2^w) := by ac_rfl
  _=z*2^(u+v+w) :=congrArg (z * ·) (pow_add (2 :ℕ) (u+v) w).symm
end
end P0
end
