import ProximityPrize.SubmissionLower.R6966ProofPadeJetOrder
import ProximityPrize.SubmissionLower.R6966ProofPadeCoverage
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Equiv

set_option Elab.async false

namespace Research6966.Pade
open Polynomial Finset
open scoped Polynomial
noncomputable section
variable {K:Type*} [Field K]

def jetVars : K[X][X] ≃ₐ[K] MvPolynomial (Fin 2) K :=
  (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm).trans
    (MvPolynomial.finSuccEquiv K 1).symm

private theorem coeff_vars (P:K[X][X]) (d:Fin 2 →₀ ℕ) :
    (jetVars P).coeff d=(P.coeff (d 0)).coeff (d 1) := by
  let Q:=P.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm.toRingHom
  change ((MvPolynomial.finSuccEquiv K 1).symm Q).coeff d=_
  rw [←Finsupp.cons_tail d,←MvPolynomial.finSuccEquiv_coeff_coeff,AlgEquiv.apply_symm_apply]
  simp only [Q,Polynomial.coeff_map]
  change ((MvPolynomial.uniqueAlgEquiv K (Fin 1)).symm (P.coeff (d 0))).coeff d.tail=_
  rw [MvPolynomial.coeff_uniqueAlgEquiv_symm];rfl

def totalJet (P:K[X][X]) := (jetVars P).totalDegree

theorem totalJet_mul {P Q:K[X][X]} (p:P≠0) (q:Q≠0) : totalJet (P*Q)=totalJet P+totalJet Q := by
  unfold totalJet
  rw [map_mul,MvPolynomial.totalDegree_mul_of_isDomain ((map_ne_zero_iff _ jetVars.injective).mpr p)
    ((map_ne_zero_iff _ jetVars.injective).mpr q)]

theorem totalJet_le (P:K[X][X]) (b:ℕ) :
    totalJet P≤b ↔ ∀ j i,(P.coeff j).coeff i≠0 → i+j≤b := by
  classical
  have add (d:Fin 2→₀ℕ) : d.sum (fun _ n=>n)=d 1+d 0 := by
    rw [Finsupp.sum_fintype _ _ (fun _=>rfl),Fin.sum_univ_two,Nat.add_comm]
  constructor
  · intro bound j i nz
    let d:Fin 2→₀ℕ := Finsupp.equivFunOnFinite.symm ![j,i]
    have mem : d∈(jetVars P).support := MvPolynomial.mem_support_iff.mpr (by rw [coeff_vars];exact nz)
    have h: d.sum (fun _ n=>n)≤b := (MvPolynomial.le_totalDegree mem).trans bound
    rw [add] at h;exact h
  · intro bound
    apply Finset.sup_le
    intro d hd
    apply (add d).le.trans
    exact bound _ _ (coeff_vars P d ▸ MvPolynomial.mem_support_iff.mp hd)

def Row.polynomial (G:Row K) : K[X][X] := C G.a*X-C G.b

theorem Row.slope_degree {G:Row K} (p:G.primitive) : G.polynomial.natDegree=1 := by
  unfold Row.polynomial
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply (natDegree_sub_le ..).trans;apply max_le
    · rw [natDegree_mul (C_ne_zero.mpr p.1) X_ne_zero,natDegree_C,natDegree_X]
    · simp
  · simpa [coeff_sub,coeff_C_mul] using p.1

theorem Row.polynomial_ne {G:Row K} (p:G.primitive) : G.polynomial ≠ 0 := by
  intro z
  have h:=G.slope_degree p
  simp [z] at h

theorem Row.polynomial_primitive {G:Row K} (p:G.primitive) : G.polynomial.IsPrimitive := by
  apply isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro d hd
  have div := (C_dvd_iff_dvd_coeff d _).mp hd
  have da : d∣G.a := by simpa [Row.polynomial,coeff_sub,coeff_C_mul] using div 1
  have db : d∣G.b := by simpa [Row.polynomial,coeff_sub,coeff_C_mul] using div 0
  obtain ⟨u,v,eq⟩:=p.2
  apply isUnit_iff_dvd_one.mpr
  rw [←eq]
  exact dvd_add (dvd_mul_of_dvd_right da _) (dvd_mul_of_dvd_right db _)

theorem Row.total_polynomial {G:Row K} (p:G.primitive) : totalJet G.polynomial=G.graphDegree := by
  apply le_antisymm
  · apply (totalJet_le ..).mpr
    intro j i nz
    rcases j with _|j
    · have non : G.b.coeff i≠0 := by simpa [Row.polynomial,coeff_sub,coeff_C_mul] using nz
      exact (le_natDegree_of_ne_zero non).trans (le_max_right ..)
    rcases j with _|j
    · have non : G.a.coeff i≠0 := by simpa [Row.polynomial,coeff_sub,coeff_C_mul] using nz
      exact (Nat.add_le_add_right (le_natDegree_of_ne_zero non) 1).trans (le_max_left ..)
    · have := coeff_eq_zero_of_natDegree_lt (show G.polynomial.natDegree<j+2 by rw [G.slope_degree p];omega)
      simp [this] at nz
  · apply max_le
    · have h := (totalJet_le G.polynomial _).mp le_rfl 1 G.a.natDegree
      apply h
      simp [Row.polynomial,leadingCoeff_ne_zero.mpr p.1]
    · by_cases zero:G.b=0
      · simp [zero]
      have h := (totalJet_le G.polynomial _).mp le_rfl 0 G.b.natDegree
      apply (by simpa using h : ((G.polynomial.coeff 0).coeff G.b.natDegree≠0) → G.b.natDegree≤_)
      simp [Row.polynomial,leadingCoeff_ne_zero.mpr zero]

private theorem roots_degree (ys:Finset K) : (∏ y∈ys,(X-C y : K[X])).natDegree=ys.card := by
  rw [natDegree_prod ys (fun y=>X-C y) (fun y _=>X_sub_C_ne_zero y)]
  simp

/-- A nonmultiplicative row has enough room for every vanishing order on
the graph in a single univariate restriction. -/
theorem bezout_sheet_order {G:Row K} (gp:G.primitive) (ys:Finset K) (v:K→K)
    (graph:∀ y∈ys,G.err v y=0) (Q:K[X][X]) (b j k:ℕ) (bt:totalJet Q≤b) (sj:Q.natDegree≤j)
    (order:∀ y∈ys,Q∈(TerminalProjection.fibrePoint y (v y))^k)
    (avoids:¬G.polynomial∣Q) : ys.card*k≤b+(G.graphDegree-1)*min b j := by
  have non : Q≠0 := fun z=>avoids (z ▸ dvd_zero _)
  have degree:Q.natDegree≤b := by
    have q:Q.coeff Q.natDegree≠0:=by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr non
    have h := (totalJet_le Q b).mp bt Q.natDegree (Q.coeff Q.natDegree).natDegree
      (by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr q)
    omega
  have cap := le_min degree sj
  have regular (y) (hy:y∈ys) : G.a.eval y≠0 := by
    intro zero
    have bzero:G.b.eval y=0 := by simpa [Row.err,zero] using graph y hy
    obtain ⟨u,w,bz⟩:=gp.2
    have H:=congrArg (eval y) bz
    simp [zero,bzero] at H
  have dv := TerminalProjection.all_sheets G.a G.b Q ys v (min b j) k cap (fun y hy=>
    ⟨regular y hy,sub_eq_zero.mp (graph y hy),order y hy⟩)
  have nz:=TerminalProjection.nonzero_of_avoids G.a G.b Q _ cap gp.1 (G.polynomial_primitive gp) avoids
  have lower:=natDegree_le_of_dvd dv nz
  rw [natDegree_pow,roots_degree,Nat.mul_comm] at lower
  apply lower.trans
  refine TerminalProjection.ordinate_width G.a G.b Q _ G.graphDegree b cap
    (by unfold Row.graphDegree;omega) (by unfold Row.graphDegree;omega) (le_max_right ..) ?_
  intro i hi
  have le:Q.coeff i≠0:=mem_support_iff.mp hi
  exact (totalJet_le Q b).mp bt i _ (by rw [coeff_natDegree];exact leadingCoeff_ne_zero.mpr le)

/-- Successive forcing for exactly the row, degree and order budget
used by the physical terminal cut. -/
theorem forced_power {G:Row K} (gp:G.primitive) (ys:Finset K) (v:K→K)
    (graph:∀y∈ys,G.err v y=0) (Q:K[X][X]) (b j k t:ℕ) (bt:totalJet Q≤b) (sj:Q.natDegree≤j)
    (ord:∀y∈ys,Q∈(TerminalProjection.fibrePoint y (v y))^k) (tk:t≤k)
    (forces:∀ i<t,i*G.graphDegree≤b → i≤j →
        b-i*G.graphDegree+(G.graphDegree-1)*min (b-i*G.graphDegree) (j-i)
        < ys.card*(k-i)) : G.polynomial^t ∣ Q := by
  classical
  by_cases z:Q=0
  · simp [z]
  have gn:=G.polynomial_ne gp
  have powers (i:ℕ) : i≤t → ∃ R:K[X][X],Q=G.polynomial^i*R ∧
      ∀y∈ys,R∈(TerminalProjection.fibrePoint y (v y))^(k-i) := by
    induction i with
    | zero => intro _;exact ⟨Q,by simp,by simpa using ord⟩
    | succ i ih =>
      intro next
      obtain ⟨R,eq,contact⟩:=ih (by omega)
      have rn:R≠0:= right_ne_zero_of_mul (eq ▸ z)
      have powdeg (n:ℕ) : totalJet (G.polynomial^n)=n*G.graphDegree := by
        induction n with
        | zero => simp [totalJet,jetVars]
        | succ n h =>
          rw [pow_succ,totalJet_mul (pow_ne_zero _ gn) gn,h,G.total_polynomial gp,Nat.succ_mul]
      have total:=bt
      have slope:=sj
      rw [eq,totalJet_mul (pow_ne_zero _ gn) rn,powdeg] at total
      rw [eq,natDegree_mul (pow_ne_zero _ gn) rn,natDegree_pow,G.slope_degree gp,mul_one] at slope
      have bd:totalJet R≤b-i*G.graphDegree := by omega
      have jd:R.natDegree≤j-i := by omega
      have div : G.polynomial∣ R := by
        by_contra no
        exact (Nat.not_le_of_lt (forces i (by omega) (by omega) (by omega)))
          (bezout_sheet_order gp ys v graph R _ _ _ bd jd contact no)
      obtain ⟨T,hT⟩:=div
      refine ⟨T,by rw [eq,hT,pow_succ,mul_assoc],?_⟩
      intro y hy
      have hit:=sub_eq_zero.mp (graph y hy)
      have reg : G.a.eval y≠0 := by
        intro hz
        change G.a.eval y*v y=G.b.eval y at hit
        obtain ⟨l,w,one⟩:=gp.2
        have test:=congrArg (eval y) one
        simp [←hit,hz] at test
      apply PadeJetOrder.strip G.a G.b T y (v y) (k-(i+1)) reg hit
      rw [show k-(i+1)+1=k-i by omega]
      exact hT ▸ contact y hy
  obtain ⟨R,eq,_⟩:=powers t le_rfl
  exact ⟨R,eq⟩

#print axioms bezout_sheet_order
#print axioms forced_power

/-- Number charged by the physical quotient receipt, using a rounded-up
division only when a positive number of graph factors is forced. -/
def layers (a n b j k:ℕ) : ℕ :=
  let width:=b+(a-1)*min b j
  if width<n*k then min k (1+(n*k-width-1)/(n-(2*a-1))) else 0

theorem layers_force {a n b j k i:ℕ} (ap:0<a) (many:2*a-1<n)
    (active:i<layers a n b j k) (ib:i*a≤b) (ij:i≤j) :
    b-i*a+(a-1)*min (b-i*a) (j-i)<n*(k-i) := by
  let width:=b+(a-1)*min b j
  by_cases excess:width<n*k
  · change i<(if width<n*k then min k (1+(n*k-width-1)/(n-(2*a-1))) else 0) at active
    rw [ite_eq_left excess,lt_min_iff] at active
    have ik:=active.1.le
    have div:i≤(n*k-width-1)/(n-(2*a-1)):=by omega
    have spend: i*(n-(2*a-1))≤n*k-width-1 :=
      (Nat.le_div_iff_mul_le (by omega)).mp div
    have split:i*(n-(2*a-1))+i*(2*a-1)=i*n:=by
      rw [←Nat.mul_add,Nat.sub_add_cancel (by omega)]
    have full:n*(k-i)+i*n=n*k:=by
      rw [Nat.mul_comm i n,←Nat.mul_add,Nat.sub_add_cancel ik]
    have ia : i ≤ i*a := by simpa only [mul_one] using Nat.mul_le_mul_left i (show 1≤a from ap)
    have drop:min (b-i*a) (j-i)+i≤min b j := by
      have l:=min_le_left (b-i*a) (j-i)
      have r:=min_le_right (b-i*a) (j-i)
      omega
    have cols:=Nat.mul_le_mul_left (a-1) drop
    rw [Nat.mul_add] at cols
    have reduced:b-i*a+(a-1)*min (b-i*a) (j-i)+i*(2*a-1)≤width := by
      dsimp only [width]
      rw [show 2*a-1=a+(a-1) by omega,Nat.mul_add,Nat.mul_comm i (a-1)]
      omega
    omega
  · simp [layers,show ¬b+(a-1)*min b j<n*k from excess] at active

theorem forced_layers {G:Row K} (gp:G.primitive) (ys:Finset K) (v:K→K)
    (graph:∀y∈ys,G.err v y=0) (Q:K[X][X]) (b j k:ℕ) (bt:totalJet Q≤b) (sj:Q.natDegree≤j)
    (ord:∀y∈ys,Q∈(TerminalProjection.fibrePoint y (v y))^k)
    (many:2*G.graphDegree-1<ys.card) :
    G.polynomial^(layers G.graphDegree ys.card b j k) ∣ Q := by
  apply forced_power gp ys v graph Q b j k _ bt sj ord
  · dsimp only [layers]
    split
    · exact min_le_left ..
    · exact Nat.zero_le _
  · intro i hi ib ij
    exact layers_force (by unfold Row.graphDegree;omega) many hi ib ij

#print axioms forced_layers
end
end Research6966.Pade
