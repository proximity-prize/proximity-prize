import ProximityPrize.SubmissionLower.HighCore82258Pairs
import ProximityPrize.SubmissionLower.UpperBranch4

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
namespace Lower6960.PowerLayers
open K1_14 (Shape Jet Equation Seeds FX triangle)
open K1_14_3 (RowCaps)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (jetDegree seedDegree jetDegree_le seedDegree_le jetDegree_mul seedDegree_mul)
open P1_7_4_1 (factorDegree factorDegree_pow factorDegree_add)
open Polynomial Finset
open scoped BigOperators Classical
open K1_14_2_1_2 (seed_finrank)

/-- All rows at a lower cutoff contain the same power if the buffered rows
have a common seeded divisor. The divisor may be different for each bank. -/
theorem forced_power {h N W U : ℕ} (hh : 0<h) (hw : W<N) {G P R : Jet}
    (irr : Irreducible G) (slope : 0<G.natDegree) (seeded : UsesSeed G)
    (np : P≠0) (div : G∣P) (small : U<K1.p)
    (caps : ∀ j i, ((P.coeff j).coeff i).totalDegree≤U)
    (shifts : ∀ (i : Fin 2) a, W+2*h*a≤N-1 → G∣K1_14.seedHasse i a R) :
    G^(1+(N-1-W)/(2*h))∣R := by
  apply K1_14_2_1_1.proof G P R U _ irr slope seeded np div small caps
  intro i a ha
  apply shifts i a
  have le : a≤(N-1-W)/(2*h) := by omega
  have := (Nat.le_div_iff_mul_le (by omega : 0<2*h)).mp le
  rw [Nat.mul_comm a] at this
  omega

/-- Positions in the quotient by an actual fixed polynomial. The final
inequality measures the leading term after multiplication, as in the source. -/
def positions (s : Shape) (h W : ℕ) (F : Jet) : Finset (ℕ×ℕ) :=
  ((range (s.B+1)).product (range (s.J+1))).filter fun a =>
    a.1+a.2+jetDegree F≤s.B ∧ a.2+F.natDegree≤s.J ∧
    (a.1+a.2+F.leadingCoeff.natDegree+F.natDegree)*(131071-h) ≤ W+(a.2+F.natDegree)

/-- Compare the whole row space with the smaller seed box of its quotient.
No condition that the leading coefficient consume seed degree is needed. -/
theorem quotient_rank (s : Shape) (h W : ℕ) (V : Submodule FX Jet) (F : Jet)
    (nf : F≠0) (dvd : ∀ R∈V,F∣R) (caps : ∀ R∈V,RowCaps R s)
    (lead : ∀ R∈V,R≠0 →
      (R.leadingCoeff.natDegree+R.natDegree)*(131071-h)≤W+R.natDegree) :
    Module.finrank FX V≤(positions s h W F).card*triangle (s.U-seedDegree F) := by
  classical
  let U := V.comap (Algebra.lmul FX Jet F)
  let mulF : U →ₗ[FX] V := (((Algebra.lmul FX Jet F).comp U.subtype).codRestrict V
    (fun Q=>Q.property))
  have eqv : Function.Bijective mulF := by
    constructor
    · intro x y he
      exact Subtype.ext (mul_left_cancel₀ nf (congrArg Subtype.val he))
    · intro x
      obtain ⟨y,hy⟩:=dvd x x.property
      exact ⟨⟨y,by change F*y∈V; rw [←hy]; exact x.property⟩, Subtype.ext hy.symm⟩
  have cdeg (Q : U) : seedDegree (Q : Jet)≤s.U-seedDegree F := by
    by_cases zero : (Q : Jet)=0
    · simp [zero,seedDegree]
    have hp : seedDegree (F*(Q : Jet))≤s.U := by
      apply (seedDegree_le ..).2
      intro j i
      by_cases z : (((F*(Q : Jet)).coeff j).coeff i)=0
      · simp [z]
      exact (caps _ Q.property j i z).2.2
    rw [seedDegree_mul nf zero] at hp
    omega
  let T := MvPolynomial.restrictTotalDegree (Fin 2) FX (s.U-seedDegree F)
  let S := positions s h W F
  let coord (a : S) : U →ₗ[FX] Seeds :=
    (((lcoeff Seeds a.val.1).restrictScalars FX).comp
      ((lcoeff Equation a.val.2).restrictScalars FX)).comp U.subtype
  let proj : U →ₗ[FX] (S→T) := LinearMap.pi fun a => (coord a).codRestrict T (fun Q =>
    (MvPolynomial.mem_restrictTotalDegree ..).2 ((seedDegree_le ..).1 (cdeg Q) a.val.2 a.val.1))
  have hz : ∀ Q : U, proj Q=0 → Q=0 := by
    intro Q z
    apply Subtype.ext
    by_contra bad
    have nq : (Q : Jet)≠0 := bad
    let j := (Q : Jet).natDegree
    let i := (Q : Jet).leadingCoeff.natDegree
    have coeff : (((Q : Jet).coeff j).coeff i)≠0 := by
      dsimp only [i,j]
      rw [coeff_natDegree,coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nq)
    have jq := (jetDegree_le (Q : Jet) _).1 le_rfl j i coeff
    have total : jetDegree (F*(Q : Jet))≤s.B := (jetDegree_le ..).2 (fun v y ne=>(caps _ Q.property v y ne).1)
    rw [jetDegree_mul nf nq] at total
    have nd : (F*(Q : Jet)).natDegree≤s.J := by
      let R := F*(Q : Jet)
      have hn : R≠0 := mul_ne_zero nf nq
      apply (caps R Q.property R.natDegree R.leadingCoeff.natDegree ?_).2.1
      rw [coeff_natDegree,coeff_natDegree]; exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hn)
    have l := lead (F*(Q:Jet)) Q.property (mul_ne_zero nf nq)
    rw [natDegree_mul nf nq] at nd l
    rw [leadingCoeff_mul,natDegree_mul (leadingCoeff_ne_zero.mpr nf) (leadingCoeff_ne_zero.mpr nq)] at l
    have mem : (i,j)∈S := by
      apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by dsimp [j]; omega)⟩,?_,?_,?_⟩
      · omega
      · dsimp [j]; omega
      · dsimp [i,j]; linarith
    have witness := congrArg (fun f : S→T => ((f ⟨(i,j),mem⟩ : T) : Seeds)) z
    exact coeff witness
  have inj : Function.Injective proj := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub,hxy]
    ext a
    exact sub_self _
  let eq := LinearEquiv.ofBijective mulF eqv
  rw [←eq.finrank_eq]
  calc _ ≤ Module.finrank FX (S→T) := LinearMap.finrank_le_finrank_of_injective inj
       _ = _ := by
          let : Module.Free FX T := Module.Free.of_basis (MvPolynomial.basisRestrictSupport FX _)
          rw [Module.finrank_pi_fintype FX (M:=fun _ : S=>T)]
          simp [T,S,seed_finrank]

/-- The executable histogram uses these original slope and total indices
after forgetting the nonnegative ordinate power in the divisor's leading term. -/
def eligiblePositions (s : Shape) (h W slope trim : ℕ) : Finset (ℕ×ℕ) :=
  ((range (s.B+1)).product (range (s.J+1))).filter fun a =>
    a.2≤a.1 ∧ slope≤a.2 ∧ a.1+trim≤s.B ∧ a.1*(131071-h)≤W+a.2

theorem layer_rank (s : Shape) (h W k slope extra u : ℕ) (V : Submodule FX Jet)
    (G : Jet) (g : G≠0) (sg : slope≤G.natDegree) (ug : u≤seedDegree G)
    (bg : G.natDegree+extra≤jetDegree G)
    (dvd : ∀ R∈V,G^k∣R) (caps : ∀ R∈V,RowCaps R s)
    (lead : ∀ R∈V,R≠0 →
      (R.leadingCoeff.natDegree+R.natDegree)*(131071-h)≤W+R.natDegree) :
    Module.finrank FX V ≤ (eligiblePositions s h W (k*slope) (k*extra)).card *
      (if k*u≤s.U then triangle (s.U-k*u) else 0) := by
  classical
  let F:=G^k
  have nf : F≠0 := pow_ne_zero k g
  have ds : F.natDegree=k*G.natDegree := natDegree_pow G k
  have du : seedDegree F=k*seedDegree G := factorDegree_pow g k 2
  have db : jetDegree F=k*jetDegree G := factorDegree_pow g k 0
  have sfit : k*slope≤F.natDegree := ds ▸ Nat.mul_le_mul_left _ sg
  have bfit : F.natDegree+k*extra≤jetDegree F := by
    rw [ds,db,←Nat.mul_add]; exact Nat.mul_le_mul_left _ bg
  have ufit : k*u≤seedDegree F := du ▸ Nat.mul_le_mul_left _ ug
  by_cases zero : s.U<k*u
  · rw [ite_eq_right (Nat.not_le.mpr zero),Nat.mul_zero]
    have sub : V=⊥ := by
      apply bot_unique
      intro R hr
      change R=0
      by_contra nr
      obtain ⟨Q,hq⟩:=dvd R hr
      have qn : Q≠0 := right_ne_zero_of_mul (hq ▸ nr)
      have cap : seedDegree R≤s.U := (seedDegree_le ..).2 (by
        intro j i
        by_cases hz : ((R.coeff j).coeff i)=0
        · simp [hz]
        exact (caps R hr j i hz).2.2)
      change R=F*Q at hq
      rw [hq,seedDegree_mul nf qn] at cap
      omega
    rw [sub,finrank_bot]
  · rw [ite_eq_left (Nat.le_of_not_gt zero)]
    have rank:=quotient_rank s h W V F nf dvd caps lead
    have card : (positions s h W F).card ≤ (eligiblePositions s h W (k*slope) (k*extra)).card := by
      apply card_le_card_of_injOn (fun a:ℕ×ℕ=>(a.1+a.2+F.natDegree,a.2+F.natDegree))
      · intro a ha
        obtain ⟨_,ht,hj,hw⟩:=mem_filter.mp ha
        apply mem_filter.mpr
        dsimp only
        refine ⟨mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩,
          by omega, by omega, by omega, ?_⟩
        exact (Nat.mul_le_mul_right _ (by omega)).trans hw
      · rintro ⟨i,j⟩ _ ⟨i',j'⟩ _ he
        simp only [Prod.mk.injEq,Nat.add_left_inj] at he
        obtain ⟨ha,rfl⟩:=he
        simp_all
    have tri : triangle (s.U-seedDegree F)≤triangle (s.U-k*u) := by
      unfold triangle
      apply Nat.div_le_div_right
      have := Nat.sub_le_sub_left ufit s.U
      exact Nat.mul_le_mul (by omega) (by omega)
    exact rank.trans (Nat.mul_le_mul card tri)

/-- A source with more dimensions than this explicit power-layer bound
has a row at the buffered cutoff avoiding the specified moving prime. -/
def layerCost (s : Shape) (h N W slope extra u : ℕ) : ℕ :=
  let k:=1+(N-1-W)/(2*h)
  (eligiblePositions s h W (k*slope) (k*extra)).card *
    (if k*u≤s.U then triangle (s.U-k*u) else 0)

theorem no_common_power (s : Shape) (h N slope extra u : ℕ)
    (rows : ℕ→Submodule FX Jet) (G : Jet) (nz : G≠0)
    (sg : slope≤G.natDegree) (ug : u≤seedDegree G) (bg : G.natDegree+extra≤jetDegree G)
    (caps : ∀ W<N, ∀ R∈rows W, RowCaps R s)
    (lead : ∀ W<N, ∀ R∈rows W, R≠0 →
      (R.leadingCoeff.natDegree+R.natDegree)*(131071-h)≤W+R.natDegree)
    (supply : (∑ W∈range N,layerCost s h N W slope extra u) <
      ∑ W∈range N,Module.finrank FX (rows W)) :
    ¬ (∀ W<N, ∀ R∈rows W,G^(1+(N-1-W)/(2*h))∣R) := by
  intro power
  apply (Nat.not_lt_of_ge (Finset.sum_le_sum (s:=range N) (fun W mem =>
    layer_rank s h W _ slope extra u (rows W) G nz sg ug bg (power W (mem_range.mp mem))
      (caps W (mem_range.mp mem)) (lead W (mem_range.mp mem))))) supply

theorem avoiding_row (s : Shape) (h N slope extra u : ℕ) (hh : 0<h)
    (rows : ℕ→Submodule FX Jet) (G P : Jet) (irr : Irreducible G)
    (gs : 0<G.natDegree) (seeded : UsesSeed G) (np : P≠0) (gp : G∣P)
    (small : s.U<K1.p) (pc : ∀ j i,((P.coeff j).coeff i).totalDegree≤s.U)
    (sg : slope≤G.natDegree) (ug : u≤seedDegree G) (bg : G.natDegree+extra≤jetDegree G)
    (caps : ∀ W<N, ∀ R∈rows W, RowCaps R s)
    (lead : ∀ W<N, ∀ R∈rows W, R≠0 →
      (R.leadingCoeff.natDegree+R.natDegree)*(131071-h)≤W+R.natDegree)
    (shift : ∀ W<N,∀ R∈rows W,∀ i a, W+2*h*a≤N-1 → K1_14.seedHasse i a R∈rows (N-1))
    (supply : (∑ W∈range N,layerCost s h N W slope extra u) <
      ∑ W∈range N,Module.finrank FX (rows W)) :
    ∃ Q∈rows (N-1), ¬ G∣Q := by
  by_contra! shared
  apply no_common_power s h N slope extra u rows G irr.ne_zero sg ug bg caps lead supply
  intro W hw R hr
  exact forced_power hh hw irr gs seeded np gp small pc
    (fun i a hsp => shared _ (shift W hw R hr i a hsp))

/-- A nonnegative combination of clipped affine widths, less an affine
debit, has nondecreasing integer first differences. -/
def net {ι : Type*} (T : Finset ι) (weight : ι→ℕ) (a b : ι→ℤ)
    (c d : ℤ) (x : ℕ) : ℤ :=
  (∑ i∈T, (weight i : ℤ)*max 0 (a i+b i*(x:ℤ)))-(c+d*(x:ℤ))

private theorem clip_second (x y : ℤ) :
    2*max 0 (x+y) ≤ max 0 x + max 0 (x+2*y) := by
  by_cases h : 0≤x+y
  · rw [max_eq_right h]
    have h1 := le_max_right 0 x
    have h2 := le_max_right 0 (x+2*y)
    omega
  · rw [max_eq_left (by omega : x+y≤0)]
    have h1 := le_max_left 0 x
    have h2 := le_max_left 0 (x+2*y)
    omega

theorem net_convex {ι : Type*} (T : Finset ι) (weight : ι→ℕ) (a b : ι→ℤ)
    (c d : ℤ) (x : ℕ) :
    2*net T weight a b c d (x+1) ≤ net T weight a b c d x + net T weight a b c d (x+2) := by
  classical
  have each (i) : 2*((weight i:ℤ)*max 0 (a i+b i*((x:ℤ)+1))) ≤
      (weight i:ℤ)*max 0 (a i+b i*(x:ℤ)) + (weight i:ℤ)*max 0 (a i+b i*((x:ℤ)+2)) := by
    have z:=mul_le_mul_of_nonneg_left (clip_second (a i+b i*(x:ℤ)) (b i)) (Int.natCast_nonneg (weight i))
    rw [show a i+b i*((x:ℤ)+1)=a i+b i*(x:ℤ)+b i by ring,
      show a i+b i*((x:ℤ)+2)=a i+b i*(x:ℤ)+2*b i by ring]
    linarith only [z]
  have total:=sum_le_sum (s:=T) (fun i _=>each i)
  rw [←Finset.mul_sum, Finset.sum_add_distrib] at total
  unfold net
  push_cast
  linarith only [total]

theorem from_two_heights (f : ℕ→ℤ) (lo : ℕ) (positive : 0<f lo)
    (next : f lo≤f (lo+1)) (convex : ∀ x,2*f (x+1)≤f x+f (x+2)) :
    ∀ y,lo≤y → 0<f y := by
  intro y hy
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hy
  have both : ∀ n, 0<f (lo+n) ∧ f (lo+n)≤f (lo+n+1) := by
    intro t
    induction t with
    | zero => exact ⟨positive,next⟩
    | succ t ih =>
      have := convex (lo+t)
      exact ⟨lt_of_lt_of_le ih.1 ih.2,by
        change f (lo+t+1)≤f (lo+t+2)
        omega⟩
  exact (both n).1

/-- Sum the clipped width of one coordinate using its rank-loss increments.
This exchanges the cutoff sum for the short Hasse-layer sum in the replay. -/
theorem sum_layer_gains (N width shift layers : ℕ) (delta : ℕ→ℕ) :
    (∑ W∈range N, ∑ i∈range layers,
      if width≤W ∧ W+shift*i<N then delta i else 0) =
      ∑ i∈range layers, (N-width-shift*i)*delta i := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have support : (range N).filter (fun W=>width≤W ∧ W+shift*i<N) = Ico width (N-shift*i) := by
    ext W
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  rw [←Finset.sum_filter,support,Finset.sum_const,Nat.card_Ico,nsmul_eq_mul]
  change (N-shift*i-width)*delta i=(N-width-shift*i)*delta i
  rw [Nat.sub_sub,Nat.sub_sub,Nat.add_comm (shift*i) width]

#print axioms sum_layer_gains
#print axioms net_convex
#print axioms from_two_heights
#print axioms avoiding_row
#print axioms layer_rank
#print axioms forced_power
#print axioms quotient_rank
end Lower6960.PowerLayers
