import ProximityPrize.SubmissionLower.Z6969Pack0528
import ProximityPrize.SubmissionLower.Z6969Pack0427
import ProximityPrize.SubmissionLower.Z6969Pack0520

set_option Elab.async false

-- Source: Research6969.NativeSurfaceCount
section Z6969Source0550
set_option autoImplicit true
namespace Research6969.NativeSurfaceCount
noncomputable section
open K1 (K I node p)
open K1_14 (FX L Jet Equation atX liftPoly seedEmbedding graphEval jetAt)
open K1_14_3 (Surface ProjectedProduct SeedField)
open Research6966
open Research6966.PadeNativeQuotient (Native)
open Research6966.NativeGraphExceptional (den rhs)
open Research6966.NonlinearMarkRows (evaluate)
open Research6966.NonlinearMarkDegrees (cap)
open Research6969.MarkedAdaptive (Coordinates price)
open Finset Polynomial
open scoped Classical BigOperators Differential
attribute [local instance] GenericPhysicalCentre.physical GenericPhysicalCentre.seeds
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000

def label (t:K) : Fin 2→FX := ![seedEmbedding t,seedEmbedding t^p]
private theorem fixed_power {E:Type*} [Field E] [Differential E] (x:E)
    (constant:Differential.deriv x=0) (n:ℕ) : Differential.deriv (x^n)=0 := by
  induction n with
  | zero=>simp
  | succ n ih=>rw [pow_succ,Derivation.leibniz,constant,ih,smul_zero,smul_zero,add_zero]
private theorem fixed_pair (v:FX) (n:ℕ) (hv:Differential.deriv v=0) (j:Fin 2) :
    Differential.deriv ((![v,v^n]:Fin 2→FX) j)=0 := by
  fin_cases j
  · exact hv
  · exact fixed_power v hv n
theorem label_fixed (t:K) (j:Fin 2) : Differential.deriv (label t j)=0 := by
  apply fixed_pair _ p _ j
  change Differential.deriv (algebraMap (Polynomial L) FX (C (algebraMap K L t)))=0
  rw [GenericPhysicalCentre.physical_poly,derivative_C,map_zero]

private theorem total_cap {u:ℕ} {Q:Equation} (caps:∀ i,(Q.coeff i).totalDegree≤u) :
    cap (fun _=>1) u Q := by
  intro i
  apply MvPolynomial.mem_restrictWeightAtMost.mpr
  intro m hm
  have d: m.degree≤u := (MvPolynomial.le_totalDegree hm).trans (caps i)
  simpa [Finsupp.weight_apply,Finsupp.degree_apply,Finsupp.sum] using d

/-- Price regular words on any nonzero ordinate equation over the native seeds. -/
theorem regular_equation {a₀ : P1.Words} {deleted : Finset I} {maxHeight agreement d U V:ℕ}
    {M:P1.ModelAt maxHeight a₀ deleted} {Γ T:Finset K} (F:P1.FamilyAt agreement M Γ)
    (sub:T⊆Γ) {H:Equation} (hn:H≠0)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (nonlinear:2≤G.graphDegree) (up:0<U)
    (hU:∀ j i,((N.poly.coeff j).coeff i).totalDegree≤U)
    (hV:∀ i,(H.coeff i).totalDegree≤V)
    (physical:(131071:ℤ)+M.overhead≤d) (dp:0<d) (gap:d<agreement)
    (possible:agreement≤Fintype.card I) (tame:d<p)
    (ode:∀ z∈T,evaluate (label (M.label z)) (atX (F.scalar z)) (den N)*atX (F.scalar z).derivative=
      evaluate (label (M.label z)) (atX (F.scalar z)) (rhs N))
    (on:∀ z∈T,evaluate (label (M.label z)) (atX (F.scalar z)) H=0)
    (regular:∀ z∈T,evaluate (label (M.label z)) (atX (F.scalar z)) (den N)≠0) :
    (T.card:ℚ) ≤ ((H.natDegree*U^2+2*V*(G.graphDegree-1)*U:ℕ):ℚ)*price (Fintype.card I) d agreement^2 := by
  classical
  let r:=G.graphDegree-1
  have rp:1≤r:=by dsimp [r];omega
  have li : Function.Injective M.label := fun x y same=>sub_left_injective (b:=M.shift) same
  let encode (z:K):Coordinates r U:=MvPolynomial.monomialPoint
    (MvPolynomial.bidegreeExponents (Fin 2) r U) (OdeEmbedding.point (label (M.label z)) (atX (F.scalar z)))
  have inject : Function.Injective encode := by
    intro z y same
    have eq:=MvPolynomial.monomialPoint_injective (fun i=>MvPolynomial.single_mem_bidegreeExponents rp up i)
      (show encode z=encode y from same)
    exact li (seedEmbedding.injective (congrFun eq (some 0)))
  let W:=T.image encode
  let back:=Function.invFun encode
  have inverse (z:K):back (encode z)=z:=Function.leftInverse_invFun inject z
  have membership {x} (hx:x∈W) : back x∈T ∧ encode (back x)=x := by
    obtain ⟨z,hz,rfl⟩:=mem_image.mp hx
    rw [inverse]
    exact ⟨hz,rfl⟩
  have fam {x} (hx:x∈W):back x∈Γ:=sub ((membership hx).1)
  obtain ⟨dy,ny⟩:=NativeGraphMarks.equation_degrees N gp
  have hdeg {x} (hx:x∈W) : (F.scalar (back x)).natDegree≤d := by
    rcases (F.mark _ (fam hx)).scalar_degree with zero|bnd
    · simp [zero]
    · change ((F.scalar (back x)).natDegree:ℤ)≤131071+M.overhead at bnd
      omega
  have counted:=NonlinearSurface.count rp up dp gap possible tame (den N) (rhs N) H dy
    (ny.trans (by dsimp [r];omega)) (total_cap (hU 1)) (total_cap (fun i=>by
      simpa [rhs,coeff_neg] using hU 0 i)) hn le_rfl (total_cap hV)
    W (fun x=>F.scalar (back x)) (fun x=>label (M.label (back x))) M.word
    (fun _ hx=>(membership hx).2.symm) (by
      intro x hx y hy eq
      have same:=F.distinct (fam hx) (fam hy) eq
      exact (membership hx).2.symm.trans ((congrArg encode same).trans (membership hy).2))
    (fun _ hx=>hdeg hx) (fun _ _=>label_fixed _)
    (fun _ hx=>ode _ ((membership hx).1)) (fun _ hx=>regular _ (membership hx).1)
    (fun _ hx=>on _ ((membership hx).1)) (by
      intro x hx
      let mark:=F.mark _ (fam hx)
      refine mark.bad.agreement.trans (card_le_card ?_)
      intro i hi
      exact mem_filter.mpr ⟨mem_univ _,mark.scalar_hits i hi⟩)
  rwa [show W.card=T.card from card_image_of_injective _ inject] at counted

theorem price_equation {a₀ : P1.Words} {deleted : Finset I} {maxHeight agreement d U V:ℕ}
    {M:P1.ModelAt maxHeight a₀ deleted} {Γ T:Finset K} (F:P1.FamilyAt agreement M Γ)
    (sub:T⊆Γ) {H:Equation} (hn:H≠0)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (nonlinear:2≤G.graphDegree) (up:0<U)
    (hU:∀ j i,((N.poly.coeff j).coeff i).totalDegree≤U)
    (hV:∀ i,(H.coeff i).totalDegree≤V) (small:(2*G.graphDegree-1)*U<p)
    (physical:(131071:ℤ)+M.overhead≤d) (dp:0<d) (gap:d<agreement)
    (possible:agreement≤Fintype.card I) (tame:d<p)
    (ode:∀ z∈T,evaluate (label (M.label z)) (atX (F.scalar z)) (den N)*atX (F.scalar z).derivative=
      evaluate (label (M.label z)) (atX (F.scalar z)) (rhs N))
    (on:∀ z∈T,evaluate (label (M.label z)) (atX (F.scalar z)) H=0) :
    (T.card:ℚ) ≤ ((2*G.graphDegree-1)*((p+1)*U):ℕ)+
      ((H.natDegree*U^2+2*V*(G.graphDegree-1)*U:ℕ):ℚ)*price (Fintype.card I) d agreement^2 := by
  classical
  let ev (z:K):=evaluate (label (M.label z)) (atX (F.scalar z))
  let bad:=T.filter (fun z=>ev z (den N)=0)
  let good:=T\bad
  have goodsub:good⊆T:=sdiff_subset
  have ordinary z (hz:z∈good) : ev z (den N)≠0 :=
    fun zero=>(mem_sdiff.mp hz).2 (mem_filter.mpr ⟨goodsub hz,zero⟩)
  have li : Function.Injective M.label := fun x y same=>sub_left_injective (b:=M.shift) same
  have badcap:=NativeGraphExceptional.singular_count N gp (fun _=>U)
    (fun j i z=>(MvPolynomial.degreeOf_le_totalDegree ..).trans (hU j i)) small bad _ li.injOn
    (fun z=>atX (F.scalar z)) (fun z h=>(mem_filter.mp h).2) (by
      intro z hz
      have eq:=ode z (mem_filter.mp hz).1
      rw [(mem_filter.mp hz).2,zero_mul] at eq
      exact eq.symm)
  have counted:=regular_equation F (goodsub.trans sub) hn N gp nonlinear up hU hV physical dp gap possible tame
    (fun z hz=>ode z (goodsub hz)) (fun z hz=>on z (goodsub hz)) ordinary
  have total:good.card+bad.card=T.card:=card_sdiff_add_card_eq_card (filter_subset _ _)
  rw [←total,Nat.cast_add,add_comm (good.card:ℚ)]
  have singular : bad.card≤(2*G.graphDegree-1)*((p+1)*U) := by
    simpa only [Nat.add_mul,Nat.one_mul,Nat.add_comm U] using badcap
  exact add_le_add (by exact_mod_cast singular) counted

theorem price_owned {a₀ : P1.Words} {deleted : Finset I} {maxHeight agreement d U V:ℕ}
    {M:P1.ModelAt maxHeight a₀ deleted} {Γ T:Finset K} (F:P1.FamilyAt agreement M Γ)
    (sub:T⊆Γ) {S:Finset Surface} {H:Equation} (project:ProjectedProduct S H)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (nonlinear:2≤G.graphDegree) (up:0<U)
    (hU:∀ j i,((N.poly.coeff j).coeff i).totalDegree≤U)
    (hV:∀ i,(H.coeff i).totalDegree≤V) (small:(2*G.graphDegree-1)*U<p)
    (physical:(131071:ℤ)+M.overhead≤d) (dp:0<d) (gap:d<agreement)
    (possible:agreement≤Fintype.card I) (tame:d<p)
    (owned:∀ z∈T,∃ Q∈S,N.poly∈Q.asIdeal ∧ ∀ P∈Q.asIdeal,jetAt P (M.label z) (F.scalar z)=0) :
    (T.card:ℚ) ≤ ((2*G.graphDegree-1)*((p+1)*U):ℕ)+
      ((H.natDegree*U^2+2*V*(G.graphDegree-1)*U:ℕ):ℚ)*price (Fintype.card I) d agreement^2 := by
  apply price_equation F sub project.primitive.ne_zero N gp nonlinear up hU hV small physical dp gap possible tame
  · intro z hz
    obtain ⟨Q,_,owner,mark⟩:=owned z hz
    exact NativeGraphMarks.mark_law N gp owner mark
  · intro z hz
    obtain ⟨Q,hQ,_,mark⟩:=owned z hz
    have h:=mark (C H) (project.vanishes Q hQ)
    simpa [K1_14.jetAt,evaluate,label,graphEval] using h



/-- Convert the geometric bound to the two integer coefficients charged
by the retained-word ledgers. Each ceiling is rounded upwards once. -/
theorem round_price {marks bad g v r u n a d:ℕ}
    (count : (marks:ℚ) ≤ bad + ((g*u^2+2*v*r*u:ℕ):ℚ)*price n d a^2) :
    let seed:ℕ:=⌈price n d a*u⌉₊+4
    let ordinate:ℕ:=⌈price n d a*r+((n-d:ℕ):ℚ)/(a-d:ℕ)⌉₊+4
    marks≤bad+g*seed^2+2*v*seed*ordinate := by
  let R:=price n d a
  let seed:ℕ:=⌈R*u⌉₊+4
  let ordinate:ℕ:=⌈R*r+((n-d:ℕ):ℚ)/(a-d:ℕ)⌉₊+4
  have positive : 0≤R := by dsimp [R,MarkedAdaptive.price];positivity
  have hs : R*u≤(seed:ℚ) := (Nat.le_ceil _).trans (by dsimp [seed];push_cast;linarith)
  have ho : R*r≤(ordinate:ℚ) := by
    have mu : (0:ℚ)≤((n-d:ℕ):ℚ)/(a-d:ℕ) := by positivity
    calc R*r ≤ R*r+((n-d:ℕ):ℚ)/(a-d:ℕ) := le_add_of_nonneg_right mu
      _ ≤ (⌈R*r+((n-d:ℕ):ℚ)/(a-d:ℕ)⌉₊:ℚ) := Nat.le_ceil _
      _ ≤ _ := by dsimp [ordinate];push_cast;linarith
  have mult : R*u*(R*r) ≤ (seed:ℚ)*ordinate :=
    mul_le_mul hs ho (by positivity) (by positivity)
  have sq : (R*u)^2 ≤ (seed:ℚ)^2 := by
    rw [pow_two,pow_two];exact mul_le_mul hs hs (by positivity) (by positivity)
  have total : (marks:ℚ) ≤ (bad:ℚ)+g*(seed:ℚ)^2+2*v*seed*ordinate := calc
    _ ≤ (bad:ℚ)+((g*u^2+2*v*r*u:ℕ):ℚ)*R^2 := count
    _ = bad+g*(R*u)^2+(2*v:ℚ)*(R*u*(R*r)) := by push_cast;ring
    _ ≤ bad+g*(seed:ℚ)^2+(2*v:ℚ)*((seed:ℚ)*ordinate) :=
      add_le_add (add_le_add (le_refl (bad:ℚ)) (mul_le_mul_of_nonneg_left sq (Nat.cast_nonneg g)))
        (mul_le_mul_of_nonneg_left mult (by positivity))
    _ = _ := by ring
  exact_mod_cast total

end
end Research6969.NativeSurfaceCount
end Z6969Source0550

-- Source: Research6969.JointRouted
section Z6969Source0551
set_option autoImplicit true
namespace Research6969.JointRouted
noncomputable section
open K1 (K I p)
open K1_14 (FX Seeds Jet Equation graphEval jetAt atX)
open K1_14_3 (Surface ProjectedProduct SeedField)
open Research6966
open Research6966.PadeNativeQuotient (Native)
open Research6966.NativeGraphExceptional (den rhs)
open Research6966.NonlinearMarkRows (evaluate)
open NativeSurfaceCount (label regular_equation round_price)
open Finset Polynomial
open scoped Classical Differential
set_option maxRecDepth 7000
set_option maxHeartbeats 1100000

abbrev seedWeight (d U:ℕ):ℕ:=⌈MarkedAdaptive.price (Fintype.card I) d 179740*U⌉₊+4
abbrev ordWeight (d r:ℕ):ℕ:=⌈MarkedAdaptive.price (Fintype.card I) d 179740*r+
  ((Fintype.card I-d:ℕ):ℚ)/(179740-d:ℕ)⌉₊+4

theorem natCeil_div (a b : ℕ) (hb : 0 < b) : ⌈(a : ℚ) / (b : ℚ)⌉₊ = (a + b - 1) / b := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ hbq]
    have h1 : (a + b - 1) / b * b + (a + b - 1) % b = a + b - 1 := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    have h2 : (a + b - 1) % b < b := Nat.mod_lt _ hb
    have : a ≤ (a + b - 1) / b * b := by
      generalize (a + b - 1) / b * b = m at h1 ⊢
      generalize (a + b - 1) % b = r at h1 h2
      omega
    exact_mod_cast this
  · have hc : (a : ℚ) / b ≤ (⌈(a : ℚ) / b⌉₊ : ℚ) := Nat.le_ceil _
    rw [div_le_iff₀ hbq] at hc
    have hc' : a ≤ ⌈(a : ℚ) / b⌉₊ * b := by exact_mod_cast hc
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul hb, Nat.succ_mul]
    omega

theorem seedWeight_eq (d U : ℕ) :
    seedWeight d U = (2 * 262144 * d * U + 179740 - 1) / 179740 + 4 := by
  unfold seedWeight
  rw [show Fintype.card K1.I = 262144 from Fintype.card_fin (2^18)]
  unfold Research6969.MarkedAdaptive.price
  have : (2 * ((262144 : ℕ) : ℚ) * d / (179740 : ℕ) * U) = ((2 * 262144 * d * U : ℕ) : ℚ) / ((179740 : ℕ) : ℚ) := by
    push_cast; ring
  rw [this, natCeil_div _ _ (by norm_num)]


/-- At a regular rescue mark the exclusive polynomial and the graph law
hold on the same word. Either counting theorem applies to this same set. -/
theorem invoice_optional {u del} {M:P1.ModelAt 33735 u del} {Γ S:Finset K}
    (F:P1.FamilyAt 179740 M Γ) (sub:S⊆Γ) (hi:M.overhead.toNat≤2534)
    {A B:Finset Surface} {f g h:Equation} (main:JointProjection.Product A f)
    (rescue:JointProjection.Product B g) (union:JointProjection.Product (A∪B) h)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (nonlinear:2≤G.graphDegree)
    {degree U:ℕ} (pos:0<U) (dp:0<degree) (phys:131071+M.overhead≤(degree:ℤ))
    (gap:degree<179740) (tame:degree<p)
    (width:∀ j i,((N.poly.coeff j).coeff i).totalDegree≤U)
    (grade:h.natDegree<64)
    (smallF:(2*h.natDegree-1)*K1_14_4.seedDegree f<p)
    (smallG:(2*h.natDegree-1)*K1_14_4.seedDegree g<p)
    (owners:∀z∈S,∃Q∈A∪B,∀P∈Q.asIdeal,jetAt P (M.label z) (F.scalar z)=0)
    (law:∀ z∈S,jetAt (C f) (M.label z) (F.scalar z)≠0 →
      evaluate (label (M.label z)) (atX (F.scalar z)) (den N)*atX (F.scalar z).derivative=
      evaluate (label (M.label z)) (atX (F.scalar z)) (rhs N))
    (regular:∀ z∈S,jetAt (C f) (M.label z) (F.scalar z)≠0 →
      evaluate (label (M.label z)) (atX (F.scalar z)) (den N)≠0) :
    ∃ j w:ℕ,f.natDegree+j=h.natDegree ∧ j≤g.natDegree ∧ w≤K1_14_4.seedDegree g ∧
      S.card≤JointMarked.price f.natDegree (K1_14_4.seedDegree f)+
        min (JointMarked.price j w) (j*seedWeight degree U^2+
          2*w*seedWeight degree U*ordWeight degree (G.graphDegree-1)) := by
  classical
  obtain ⟨e,eq,dvd,enz,sum,sep⟩:=JointProjection.exclusive main rescue union
  obtain ⟨prim,seed⟩:=JointProjection.remainder rescue dvd
  let ev (z:K):Equation→+*FX:=eval₂RingHom (graphEval (M.label z)) (atX (F.scalar z))
  let P:=S.filter fun z=>ev z f=0
  let E:=S\P
  have psub:P⊆S:=filter_subset _ _
  have esub:E⊆S:=sdiff_subset
  have actual (z) (hz:z∈S):ev z h=0:=by
    obtain ⟨Q,hQ,hit⟩:=owners z hz
    simpa [ev,jetAt] using hit (C h) (union.vanishes hQ)
  have read (z) (q:Equation):ev z q=(q.map (graphEval (M.label z))).eval (atX (F.scalar z)):=by
    simp [ev,Polynomial.eval_map]
  have absent z (hz:z∈E):ev z f≠0:=fun zero=>(mem_sdiff.mp hz).2 (mem_filter.mpr ⟨esub hz,zero⟩)
  have outside z (hz:z∈E):jetAt (C f) (M.label z) (F.scalar z)≠0:=by simpa [jetAt,ev] using absent z hz
  have cell z (hz:z∈E):ev z e=0:=by
    have atZ:=actual z (esub hz)
    rw [eq,map_mul] at atZ
    exact (mul_eq_zero.mp atZ).resolve_left (absent z hz)
  have lp:f.natDegree≤h.natDegree:=by omega
  have le':e.natDegree≤h.natDegree:=by omega
  have priceP:=JointMarked.owned_count F (psub.trans sub) hi f main.primitive main.separable (lp.trans_lt grade) le_rfl
    ((Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 lp) 1)).trans_lt smallF) (by
      intro z hz;rw [←read];exact (mem_filter.mp hz).2)
  have priceE:=JointMarked.owned_count F (esub.trans sub) hi e prim sep (le'.trans_lt grade) le_rfl
    ((Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 le') 1) seed).trans_lt smallG)
    (fun z hz=>(read z e).symm.trans (cell z hz))
  have fit:179740≤Fintype.card I:=by rw [show Fintype.card I=262144 from Fintype.card_fin (2^18)]; decide
  have charged:=regular_equation F (esub.trans sub) enz N gp nonlinear pos width
    ((K1_14_4.seedDegree_le_iff ..).mp le_rfl) phys dp gap fit tame
    (fun z hz=>law z (esub hz) (outside z hz)) (fun z hz=>cell z hz)
    (fun z hz=>regular z (esub hz) (outside z hz))
  have q:=round_price (bad:=0) (g:=e.natDegree) (v:=K1_14_4.seedDegree e) (r:=G.graphDegree-1) (u:=U)
    (n:=Fintype.card I) (a:=179740) (d:=degree) (by simpa using charged)
  simp only [Nat.zero_add] at q
  have priceBoth:=le_min priceE q
  refine ⟨_,_,sum,natDegree_le_of_dvd dvd rescue.primitive.ne_zero,seed,?_⟩
  have part:E.card+P.card=S.card:=card_sdiff_add_card_eq_card psub
  rw [←part,Nat.add_comm E.card]
  exact Nat.add_le_add priceP priceBoth

theorem invoice {u del} {M:P1.ModelAt 33735 u del} {Γ S:Finset K}
    (F:P1.FamilyAt 179740 M Γ) (sub:S⊆Γ) (hi:M.overhead.toNat≤2534)
    {A B:Finset Surface} {f g h:Equation} (main:ProjectedProduct A f)
    (rescue:ProjectedProduct B g) (union:ProjectedProduct (A∪B) h)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (nonlinear:2≤G.graphDegree)
    {degree U:ℕ} (pos:0<U) (dp:0<degree) (phys:131071+M.overhead≤(degree:ℤ))
    (gap:degree<179740) (tame:degree<p)
    (width:∀ j i,((N.poly.coeff j).coeff i).totalDegree≤U)
    (grade:h.natDegree<64)
    (smallF:(2*h.natDegree-1)*K1_14_4.seedDegree f<p)
    (smallG:(2*h.natDegree-1)*K1_14_4.seedDegree g<p)
    (owners:∀z∈S,∃Q∈A∪B,∀P∈Q.asIdeal,jetAt P (M.label z) (F.scalar z)=0)
    (law:∀ z∈S,jetAt (C f) (M.label z) (F.scalar z)≠0 →
      evaluate (label (M.label z)) (atX (F.scalar z)) (den N)*atX (F.scalar z).derivative=
      evaluate (label (M.label z)) (atX (F.scalar z)) (rhs N))
    (regular:∀ z∈S,jetAt (C f) (M.label z) (F.scalar z)≠0 →
      evaluate (label (M.label z)) (atX (F.scalar z)) (den N)≠0) :
    ∃ j w:ℕ,f.natDegree+j=h.natDegree ∧ w≤K1_14_4.seedDegree g ∧
      S.card≤JointMarked.price f.natDegree (K1_14_4.seedDegree f)+
        min (JointMarked.price j w) (j*seedWeight degree U^2+
          2*w*seedWeight degree U*ordWeight degree (G.graphDegree-1)) :=
  by
    obtain ⟨j,w,sum,_,wid,fee⟩:=invoice_optional F sub hi (Or.inl main) (Or.inl rescue) (Or.inl union)
      N gp nonlinear pos dp phys gap tame width grade smallF smallG owners law regular
    exact ⟨j,w,sum,wid,fee⟩

end
end Research6969.JointRouted
end Z6969Source0551

-- Source: Research6969.JointLedger
section Z6969Source0552
set_option autoImplicit true
namespace Research6969.JointLedger
noncomputable section
open K1 (p I)
open JointMarked (price)
open JointRouted (seedWeight ordWeight)

structure Book where
  fee : ℕ
  seedMass : ℕ
  ordinateCredit : ℕ
  seedCredit : ℕ

def coefficient (e:ℕ):ℕ:=(Near6969FactorPrice.rate (max 3 e)+2*e-1)*p
def markedDebit (b:Book) (e:ℕ) : ℕ :=
  if e=0 then 0 else (coefficient e-b.seedCredit)*b.seedMass+(max 3 e-1)*e
def graphDebit (b:Book) (e x y:ℕ) : ℕ :=
  e*x^2+(2*x*y-b.seedCredit)*b.seedMass

private theorem with_credit (rate credit v cap:ℕ) (room:v≤cap):
    rate*v≤credit*v+(rate-credit)*cap := by
  have h:rate≤credit+(rate-credit):=by omega
  exact (Nat.mul_le_mul_right v h).trans (by rw [Nat.add_mul]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ room) _)

theorem marked_le (b:Book) (e v:ℕ) (room:v≤b.seedMass):
    price e v≤b.seedCredit*v+markedDebit b e := by
  by_cases zero:e=0
  · simp [zero,price,markedDebit]
  · simp only [price,markedDebit,ite_eq_right zero]
    rw [←Nat.mul_assoc]
    exact (Nat.add_le_add_right (with_credit (coefficient e) b.seedCredit v b.seedMass room) _).trans_eq (Nat.add_assoc ..)

theorem graph_le (b:Book) (e v x y:ℕ) (room:v≤b.seedMass) :
    e*x^2+2*v*x*y≤b.seedCredit*v+graphDebit b e x y := by
  have pay:=with_credit (2*x*y) b.seedCredit v b.seedMass room
  rw [show 2*v*x*y=(2*x*y)*v by ring]
  unfold graphDebit
  omega

def Pass (main rescue:Book) (x y limit i j:ℕ):Prop :=
  main.fee+rescue.fee+markedDebit main i+min (markedDebit rescue j) (graphDebit rescue j x y)
    ≤limit+main.ordinateCredit*i+rescue.ordinateCredit*j

instance (main rescue:Book) (x y limit i j:ℕ) : Decidable (Pass main rescue x y limit i j) := by
  unfold Pass
  infer_instance

/-- The same two credits are consumed by both sides of the minimum on
the exclusive rescue equation. Each surviving degree enters its own bill once. -/
theorem consume (main rescue:Book) {total paid surviving i j v w x y limit:ℕ}
    (cover:total≤surviving+paid)
    (paidPrefix:paid+main.ordinateCredit*i+main.seedCredit*v+rescue.ordinateCredit*j+rescue.seedCredit*w≤main.fee+rescue.fee)
    (routed:surviving≤price i v+min (price j w) (j*x^2+2*w*x*y))
    (mainCap:v≤main.seedMass) (rescueCap:w≤rescue.seedMass) (done:Pass main rescue x y limit i j) :
    total≤limit := by
  have mp:=marked_le main i v mainCap
  have ep:=marked_le rescue j w rescueCap
  have gp:=graph_le rescue j w x y rescueCap
  have mn:=min_le_min ep gp
  rw [Nat.add_min_add_left] at mn
  unfold Pass at done
  omega

end
end Research6969.JointLedger
end Z6969Source0552

-- Source: Research6969.GradeTable
section Z6969Source0553
set_option autoImplicit true
namespace Research6969.GradeTable
open JointLedger

def first (test:ℕ→Bool):ℕ→Bool
  | 0=>true
  | n+1=>test n && first test n

theorem entry {f:ℕ→Bool} {n:ℕ} (ok:first f n=true) {i:ℕ} (hi:i<n):f i=true:=by
  induction n with
  | zero=>omega
  | succ n ih=>
    have hs:=Bool.and_eq_true_iff.mp ok
    by_cases same:i=n
    · simpa [same] using hs.1
    · exact ih hs.2 (by omega)

def check (m r:Book) (x y limit n:ℕ):Bool :=
  first (fun i=>first (fun j=>decide (Pass m r x y limit i j)) (n+1-i)) (n+1)

theorem checked {m r:Book} {x y limit n:ℕ} (ok:check m r x y limit n=true) :
    ∀ i j:Fin (n+1),i.val+j.val≤n→Pass m r x y limit i.val j.val:=by
  intro i j sum
  let f:=fun i=>first (fun j=>decide (Pass m r x y limit i j)) (n+1-i)
  have row:=entry (show first f (n+1)=true from ok) i.isLt
  exact of_decide_eq_true (entry row (show j.val<n+1-i.val by omega))

end Research6969.GradeTable
end Z6969Source0553

-- Source: Research6969.JointSmallCertificates
section Z6969Source0554
set_option autoImplicit true
namespace Research6969.SmallCertificates
open JointLedger
open JointRouted (seedWeight ordWeight)
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

abbrev primary1 : Book := ⟨205764847783078227,5503,126979896095280,1816676828996⟩
abbrev rescue1 : Book := ⟨34848927525703159,24839,206646633540,208389551481⟩
theorem seed_price1 : seedWeight 133460 1=389297 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill1 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary1 rescue1 389297 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary2 : Book := ⟨203623142476321729,5458,126881882836380,1816710589896⟩
abbrev rescue2 : Book := ⟨33036341832539669,21876,413291143800,215369846589⟩
theorem seed_price2 : seedWeight 133460 2=778590 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill2 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary2 rescue2 778590 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary3 : Book := ⟨202026846775169117,5429,126684668343420,1816777241024⟩
abbrev rescue3 : Book := ⟨31074122775277824,20959,619935654060,216390639020⟩
theorem seed_price3 : seedWeight 133460 3=1167883 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill3 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary3 rescue3 1167883 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary4 : Book := ⟨200489216485889094,5388,126469137375540,1816850271928⟩
abbrev rescue4 : Book := ⟨29197303702490968,20046,826579633500,217412440380⟩
theorem seed_price4 : seedWeight 133460 4=1557175 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill4 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary4 rescue4 1557175 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary5 : Book := ⟨199154573704011765,5350,126245256078240,1816926490928⟩
abbrev rescue5 : Book := ⟨27501369032801000,17929,1033224143760,218435218305⟩
theorem seed_price5 : seedWeight 133460 5=1946468 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill5 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary5 rescue5 1946468 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary6 : Book := ⟨197571264505672176,5312,126021374780940,1817002709928⟩
abbrev rescue6 : Book := ⟨25703534277495936,17082,1239868654020,219459008444⟩
theorem seed_price6 : seedWeight 133460 6=2335761 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill6 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary6 rescue6 2335761 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary7 : Book := ⟨196390635614266072,5274,125801717218380,1817077186896⟩
abbrev rescue7 : Book := ⟨26075806386532736,16728,1446513164280,220786655515⟩
theorem seed_price7 : seedWeight 133460 7=2725054 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill7 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary7 rescue7 2725054 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary8 : Book := ⟨195177924874418294,5237,125582060186640,1817151668048⟩
abbrev rescue8 : Book := ⟨22557237352261468,16463,1653157143720,221547035032⟩
theorem seed_price8 : seedWeight 133460 8=3114346 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill8 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary8 rescue8 3114346 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary9 : Book := ⟨193312820225067037,5200,125364515287680,1817225811096⟩
abbrev rescue9 : Book := ⟨22431832087008914,16521,1859801653980,223132847495⟩
theorem seed_price9 : seedWeight 133460 9=3503639 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill9 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary9 rescue9 3503639 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary10 : Book := ⟨191972345836058179,5164,125149081990680,1817299081036⟩
abbrev rescue10 : Book := ⟨19757791676453168,14832,2066446164240,225057901428⟩
theorem seed_price10 : seedWeight 133460 10=3892932 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill10 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary10 rescue10 3892932 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary11 : Book := ⟨191189708424265424,5128,124935761357280,1817371486236⟩
abbrev rescue11 : Book := ⟨19509119143794733,13578,2273090674500,228059351000⟩
theorem seed_price11 : seedWeight 133460 11=4282225 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill11 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary11 rescue11 4282225 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary12 : Book := ⟨189899439526341313,5092,124722440193060,1817443887252⟩
abbrev rescue12 : Book := ⟨17507280825119066,12216,2479734653940,230005811000⟩
theorem seed_price12 : seedWeight 133460 12=4671517 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill12 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary12 rescue12 4671517 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary13 : Book := ⟨188682103096635776,5056,124511231692440,1817515423528⟩
abbrev rescue13 : Book := ⟨15286339105750627,12070,2686379164200,230580796490⟩
theorem seed_price13 : seedWeight 133460 13=5060810 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill13 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary13 rescue13 5060810 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary14 : Book := ⟨186679027578918589,5028,124287098786460,1817591782592⟩
abbrev rescue14 : Book := ⟨14867945835023022,10854,2893023674460,233898741000⟩
theorem seed_price14 : seedWeight 133460 14=5450103 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill14 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary14 rescue14 5450103 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary15 : Book := ⟨186320372405965399,4992,124198287823080,1817621639236⟩
abbrev rescue15 : Book := ⟨13112079970355718,9781,3099668184720,235845206000⟩
theorem seed_price15 : seedWeight 133460 15=5839396 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill15 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary15 rescue15 5839396 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary16 : Book := ⟨185228290944896622,4956,124136252482140,1817642785728⟩
abbrev rescue16 : Book := ⟨11568344374968281,8833,3306312164160,237791666000⟩
theorem seed_price16 : seedWeight 133460 16=6228688 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill16 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary16 rescue16 6228688 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary17 : Book := ⟨182978269490810060,4921,124074217672020,1817663936404⟩
abbrev rescue17 : Book := ⟨10976346647019908,7996,3512956674420,239738131000⟩
theorem seed_price17 : seedWeight 133460 17=6617981 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill17 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary17 rescue17 6617981 389300 274784969259510674 i.val j.val := by decide +kernel

abbrev primary18 : Book := ⟨182711329596118984,4886,124013461076460,1817684545752⟩
abbrev rescue18 : Book := ⟨9262048418821099,7257,3719601184680,241684596000⟩
theorem seed_price18 : seedWeight 133460 18=7007274 := by
  rw [Research6969.JointRouted.seedWeight_eq]
theorem bill18 : ∀ i j:Fin 22,i.val+j.val≤21 → Pass primary18 rescue18 7007274 389300 274784969259510674 i.val j.val := by decide +kernel

theorem ordinate_price : ordWeight 133460 1=389300 := by
  unfold ordWeight MarkedAdaptive.price
  rw [show Fintype.card K1.I=262144 from Fintype.card_fin (2^18)]
  decide +kernel
end Research6969.SmallCertificates
end Z6969Source0554

-- Source: Research6969.ExtendedJointBills
section Z6969Source0555
set_option autoImplicit true
namespace Research6969.ExtendedJointBills
open JointLedger
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem bill1:∀ i j:Fin 22,i.val+j.val≤21→Pass SmallCertificates.primary1 SmallCertificates.rescue1 389297 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=21) (by decide +kernel)

theorem bill2:∀ i j:Fin 23,i.val+j.val≤22→Pass SmallCertificates.primary2 SmallCertificates.rescue2 778590 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=22) (by decide +kernel)

theorem bill3:∀ i j:Fin 24,i.val+j.val≤23→Pass SmallCertificates.primary3 SmallCertificates.rescue3 1167883 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=23) (by decide +kernel)

theorem bill4:∀ i j:Fin 24,i.val+j.val≤23→Pass SmallCertificates.primary4 SmallCertificates.rescue4 1557175 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=23) (by decide +kernel)

theorem bill5:∀ i j:Fin 25,i.val+j.val≤24→Pass SmallCertificates.primary5 SmallCertificates.rescue5 1946468 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=24) (by decide +kernel)

theorem bill6:∀ i j:Fin 26,i.val+j.val≤25→Pass SmallCertificates.primary6 SmallCertificates.rescue6 2335761 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=25) (by decide +kernel)

theorem bill7:∀ i j:Fin 26,i.val+j.val≤25→Pass SmallCertificates.primary7 SmallCertificates.rescue7 2725054 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=25) (by decide +kernel)

theorem bill8:∀ i j:Fin 27,i.val+j.val≤26→Pass SmallCertificates.primary8 SmallCertificates.rescue8 3114346 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=26) (by decide +kernel)

theorem bill9:∀ i j:Fin 28,i.val+j.val≤27→Pass SmallCertificates.primary9 SmallCertificates.rescue9 3503639 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=27) (by decide +kernel)

theorem bill10:∀ i j:Fin 28,i.val+j.val≤27→Pass SmallCertificates.primary10 SmallCertificates.rescue10 3892932 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=27) (by decide +kernel)

theorem bill11:∀ i j:Fin 29,i.val+j.val≤28→Pass SmallCertificates.primary11 SmallCertificates.rescue11 4282225 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=28) (by decide +kernel)

theorem bill12:∀ i j:Fin 29,i.val+j.val≤28→Pass SmallCertificates.primary12 SmallCertificates.rescue12 4671517 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=28) (by decide +kernel)

theorem bill13:∀ i j:Fin 30,i.val+j.val≤29→Pass SmallCertificates.primary13 SmallCertificates.rescue13 5060810 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=29) (by decide +kernel)

theorem bill14:∀ i j:Fin 31,i.val+j.val≤30→Pass SmallCertificates.primary14 SmallCertificates.rescue14 5450103 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=30) (by decide +kernel)

theorem bill15:∀ i j:Fin 31,i.val+j.val≤30→Pass SmallCertificates.primary15 SmallCertificates.rescue15 5839396 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=30) (by decide +kernel)

theorem bill16:∀ i j:Fin 32,i.val+j.val≤31→Pass SmallCertificates.primary16 SmallCertificates.rescue16 6228688 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=31) (by decide +kernel)

theorem bill17:∀ i j:Fin 32,i.val+j.val≤31→Pass SmallCertificates.primary17 SmallCertificates.rescue17 6617981 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=31) (by decide +kernel)

theorem bill18:∀ i j:Fin 33,i.val+j.val≤32→Pass SmallCertificates.primary18 SmallCertificates.rescue18 7007274 389300 274784969259510674 i.val j.val:=by
  exact GradeTable.checked (n:=32) (by decide +kernel)

end Research6969.ExtendedJointBills
end Z6969Source0555
