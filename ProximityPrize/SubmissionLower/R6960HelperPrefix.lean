import ProximityPrize.SubmissionLower.R6960PowerLayers
import ProximityPrize.SubmissionLower.HighCore82258PrefixProcess
import ProximityPrize.SubmissionLower.KoalaRectBridgeCore

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1500000
namespace Lower6960.HelperPrefix
open Polynomial Finset
open K1_14 (Jet Shape Banks FX Seeds Equation)
open K1_14_2 (toJet Ambient)
open K1_14_2_2 (Active dual orderOn mass sectionDegree)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (Surface Parent ProjectedProduct)
open scoped Classical
open P1_7_4_2 (sections)

theorem product_power {R G H : Jet} {k : ℕ} (cop : IsRelPrime G H)
    (left : G^k∣R) (right : H^k∣R) : (G*H)^k∣R := by
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid (D:=Seeds)
  let : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D:=Equation)
  rw [mul_pow]
  exact (cop.pow_left.pow_right).mul_dvd left right

/-- Vanishing of a translated row to order s gives order sk for its kth
power. This also applies at a seed prime after passing to the residue field. -/
theorem powered_contact {R : Type*} [CommRing R] (I : Ideal R)
    {a : R} {s k n : ℕ} (h : a∈I^s) (fit : n≤s*k) : a^k∈I^n := by
  have p:=Ideal.pow_mem_pow h k
  rw [←pow_mul] at p
  exact Ideal.pow_le_pow_right fit p

/-- Strip a factor that is nonzero at the mark. Use the translated generic
seed direction and the univariate order at the origin. -/
theorem strip_contact {K : Type*} [Field K] (g a : (Polynomial K)) {n k : ℕ}
    (unit : g.eval 0≠0) (van : (Polynomial.X : (Polynomial K))^n∣g^k*a) :
    (Polynomial.X : (Polynomial K))^n∣a := by
  have nd : ¬ (Polynomial.X : (Polynomial K))∣g := fun h => unit ((coeff_zero_eq_eval_zero g).symm.trans (Polynomial.X_dvd_iff.mp h))
  have cop : IsCoprime (Polynomial.X : (Polynomial K)) g := Polynomial.irreducible_X.coprime_iff_not_dvd.mpr nd
  exact (cop.pow (m:=n) (n:=k)).dvd_of_dvd_mul_left van

/-- The rescue history uses a proper pair and every retained prime is dual.
This is the multiplicity-squared intersection before cancelling the free
factor's power from the numerical pair cap. -/
theorem proper_power_mass (G Q : Jet) (s t : Shape) (S : Finset (Ideal Ambient))
    (k : ℕ) (pos : 0<k) (index : Fin 4) (ng : G≠0) (nq : Q≠0)
    (cop : IsRelPrime (toJet G) (toJet Q))
    (js : s.J≤s.B) (jt : t.J≤t.B)
    (capsG : K1_14_2_2.RowCaps (G^k) s) (capsQ : K1_14_2_2.RowCaps Q t)
    (on : ∀ I∈S, Active I ∧ dual I ∧ toJet G∈I ∧ orderOn I Q k) :
    (k*k)*mass S index≤pairCap s t index := by
  let : UniqueFactorizationMonoid Ambient := MvPolynomial.uniqueFactorizationMonoid (Fin 4)
  have hcop : IsRelPrime (toJet (G^k)) (toJet Q) := by rw [map_pow]; exact cop.pow_left
  apply sections (G^k) Q s t S index (k*k) (pow_ne_zero k ng) nq hcop js jt capsG capsQ (Nat.mul_pos pos pos)
  intro I hI
  obtain ⟨act,hd,hg,hq⟩ := on I hI
  have ho : orderOn I (G^k) k := by
    let _ := act.prime
    refine ⟨1,Ideal.one_notMem I,?_⟩
    rw [one_mul,map_pow]
    exact Ideal.mem_sup_left (Ideal.pow_mem_pow hg k)
  have len:=K1_14_2_2_4_4.proof (G^k) Q I act k pos ho hq
  rw [ite_eq_left hd,pow_two] at len
  exact ⟨act,fun _=>len⟩

/-- Both prefixes use one projected product once their retained parents
pass the same terminal bank. The prefixes can have different stage lists. -/
theorem union_terminal (rows : Banks) (s : Shape) (left right : Finset Surface)
    (existsParent : (left∪right).Nonempty)
    (gl : ∀ q∈left,Parent q) (gr : ∀ q∈right,Parent q)
    (pl : ∀ q∈left,HighCore82258.BankPass rows s q)
    (pr : ∀ q∈right,HighCore82258.BankPass rows s q) :
    ∃ f, ProjectedProduct (left∪right) f ∧
      ∀ q∈left∪right, HighCore82258.BankPass rows s q := by
  classical
  obtain ⟨f,prod⟩:=K1_14_3_7.proof (left∪right) existsParent (by
    intro q mem; exact (mem_union.mp mem).elim (gl q) (gr q))
  exact ⟨f,prod,fun q mem=>(mem_union.mp mem).elim (pl q) (pr q)⟩

open K1_14_2_2_3
open K1_14_2_2_3 (shiftedWord specialize_shiftedWord)

/-- The prefix only needs order on the dual parents. A passing family of
seed tests gives that order even for a powered or stripped synthetic row. -/
theorem dual_order_of_tests {I : Ideal Ambient} (act : Active I) (dualI : dual I)
    (R : Jet) (r : ℕ) (small : r<K1.p)
    (tests : ∀ t : List (Fin 2), t.length≤r → toJet (shiftedWord R t)∈I) :
    orderOn I R (r+1) := by
  let a := algebraMap K1_14.Seeds K1_14_2.SeedField
  have hc : fibreContact (I.map (specializeJets a)) (specializeJets a (toJet R)) r := by
    intro t ht
    rw [←specialize_shiftedWord]
    exact Ideal.mem_map_of_mem _ (tests _ ht)
  rw [←mapGenericJets_eq] at hc
  exact clear_dual dualI (K1_14_2_2_3_1.proof I act.prime act.jet_finite dualI act.jet_lt _ r small hc)

/-- Two relatively prime seeded moving factors cannot be unavoidable in
the same buffered bank once the two-slope test passes. -/
theorem not_two_common (s : Shape) (h N : ℕ) (hh : 0<h)
    (rows : ℕ→Submodule FX Jet) (G H P : Jet) (g : Irreducible G) (h' : Irreducible H)
    (cop : IsRelPrime G H) (gs : 0<G.natDegree) (hs : 0<H.natDegree)
    (gu : K1_14_2.UsesSeed G) (hu : K1_14_2.UsesSeed H)
    (np : P≠0) (inside : P∈rows (N-1)) (small : s.U<K1.p)
    (pc : ∀ j i,((P.coeff j).coeff i).totalDegree≤s.U)
    (caps : ∀ W<N, ∀ R∈rows W,K1_14_3.RowCaps R s)
    (lead : ∀ W<N, ∀ R∈rows W,R≠0 →
      (R.leadingCoeff.natDegree+R.natDegree)*(131071-h)≤W+R.natDegree)
    (shift : ∀ W<N,∀ R∈rows W,∀ i a,W+2*h*a≤N-1 → K1_14.seedHasse i a R∈rows (N-1))
    (supply : (∑ W∈range N, Lower6960.PowerLayers.layerCost s h N W 2 0 1) <
      ∑ W∈range N,Module.finrank FX (rows W))
    (allG : ∀ Q∈rows (N-1),G∣Q) (allH : ∀ Q∈rows (N-1),H∣Q) : False := by
  let F:=G*H
  have fn : F≠0 := mul_ne_zero g.ne_zero h'.ne_zero
  have ds : 2≤F.natDegree := by dsimp only [F];rw [natDegree_mul g.ne_zero h'.ne_zero];omega
  have du : 1≤K1_14_2_2_2_1.seedDegree F := by
    obtain ⟨j,i,pos⟩:=gu
    have ge := (K1_14_2_2_2_1.seedDegree_le G _).1 le_rfl j i
    dsimp only [F]
    rw [K1_14_2_2_2_1.seedDegree_mul g.ne_zero h'.ne_zero]
    omega
  have dg : F.natDegree+0≤K1_14_2_2_2_1.jetDegree F := by
    have co : (F.coeff F.natDegree).coeff F.leadingCoeff.natDegree ≠ 0 := by
      rw [coeff_natDegree,coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr fn)
    have := (K1_14_2_2_2_1.jetDegree_le F _).1 le_rfl _ _ co
    omega
  apply Lower6960.PowerLayers.no_common_power s h N 2 0 1 rows F fn ds du dg caps lead supply
  intro W hw R hr
  apply product_power cop
  · exact Lower6960.PowerLayers.forced_power hh hw g gs gu np (allG P inside) small pc
      (fun i a ha=>allG _ (shift W hw R hr i a ha))
  · exact Lower6960.PowerLayers.forced_power hh hw h' hs hu np (allH P inside) small pc
      (fun i a ha=>allH _ (shift W hw R hr i a ha))

open K1_14_3R (fixed_of_no_seed)

/-- Choose one helper for the entire finite prefix after stripping its unique
exception. Its powers preserve the same factor avoidance. -/
theorem one_helper {ι : Type*} [Fintype ι] (P : ι→Jet) (ks : ι→ℕ)
    (V : Submodule FX Jet) (nonempty : ∃ H∈V,H≠0)
    (proper : ∀ i,P i≠0)
    (avoid : ∀ i G,Irreducible G → G∣P i → 0<G.natDegree → K1_14_2.UsesSeed G →
      ∃ H∈V, ¬ G∣H) :
    ∃ H∈V,H≠0 ∧ ∀ i,K1_14_3.NoMovingCommon (P i) (H^(ks i)) := by
  classical
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid (D:=Seeds)
  let : UniqueFactorizationMonoid Jet := Polynomial.uniqueFactorizationMonoid (D:=Equation)
  have prod : (∏ i,P i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>proper i)
  obtain ⟨H,inside,nh,all⟩:=K1_14_2_1.exists_layered (∏ i,P i) prod V nonempty (by
    intro G irr divides degree seeded
    obtain ⟨i,_,di⟩:=irr.prime.exists_mem_finset_dvd divides
    exact avoid i G irr di degree seeded)
  refine ⟨H,inside,nh,?_⟩
  intro i G irr left right degree
  apply fixed_of_no_seed
  intro seeded
  exact all G irr (left.trans (Finset.dvd_prod_of_mem P (Finset.mem_univ i))) degree seeded
    (irr.prime.dvd_of_dvd_pow right)

open P0_10R_1 (section_bound component_height)
open P1_7_4_1 (irreducible_cut)

/-- The exceptional branch starts with just the known prime and its
avoiding row. All its parent components really contain that prime. -/
theorem exceptional_initial (G Q : Jet) (s t : Shape) (irr : Irreducible G)
    (nd : ¬G∣Q) (js : s.J≤s.B) (jt : t.J≤t.B)
    (cg : K1_14_2_2.RowCaps G s) (cq : K1_14_2_2.RowCaps Q t) :
    ∃ S : Finset (Ideal Ambient), P1_7_4_1.SectionGeometry S ∧
      K1_14_2_2.Fits S (K1_14_2_2_2.residualBudget s t) ∧
      (∀ I∈S,toJet G∈I) ∧
      ∀ z R,K1_14.jetAt G z R=0 → K1_14.jetAt Q z R=0 →
        ∃ I∈S,K1_14_2.OnJet I z R := by
  have proper:=irreducible_cut irr nd
  obtain ⟨S,hs,cover⟩:=K1_14_2_2_2_3.proof _ _ proper
  obtain ⟨finite,fit⟩:=section_bound _ _ proper s t js jt cg cq S hs
  refine ⟨S,?_,fit,fun I hi=>(hs I hi).2.2.1,cover⟩
  intro I hi
  obtain ⟨prime,dim,row,cut⟩:=hs I hi
  exact ⟨prime,dim,component_height proper prime dim row cut,finite I hi⟩

def timesShape (k : ℕ) (s : Shape) : Shape := ⟨k*s.m,k*s.B,k*s.J,k*s.U⟩

theorem scaled_pair (k : ℕ) (s t : Shape) (i : Fin 4) :
    pairCap (timesShape k s) t i=k*pairCap s t i := by
  fin_cases i <;> simp [timesShape,pairCap,Nat.mul_sub,Nat.mul_add,
    Nat.mul_left_comm,Nat.mul_comm]

theorem exceptional_history (G Q : Jet) (s t : Shape) (S : Finset (Ideal Ambient))
    (k : ℕ) (hk : 0<k) (i : Fin 4) (ng : G≠0) (nq : Q≠0)
    (cop : IsRelPrime (toJet G) (toJet Q))
    (hs : s.J≤s.B) (ht : t.J≤t.B)
    (hc : K1_14_2_2.RowCaps (G^k) (timesShape k s)) (hq : K1_14_2_2.RowCaps Q t)
    (on : ∀ I∈S,Active I ∧ dual I ∧ toJet G∈I ∧ orderOn I Q k) :
    k*mass S i≤pairCap s t i := by
  have bound:=proper_power_mass G Q (timesShape k s) t S k hk i ng nq cop
    (Nat.mul_le_mul_left _ hs) ht hc hq on
  rw [scaled_pair,Nat.mul_assoc] at bound
  exact Nat.le_of_mul_le_mul_left bound hk

theorem high_ledger :
    116851670497542517 + 118687375614631597 + 27283109943102372 +
    143456202788540 + 48 + 3730105881391565 = 266695718139456639 := by decide +kernel

#print axioms exceptional_initial
#print axioms exceptional_history
#print axioms high_ledger
#print axioms one_helper
#print axioms not_two_common
#print axioms dual_order_of_tests
#print axioms product_power
#print axioms powered_contact
#print axioms strip_contact
#print axioms proper_power_mass
#print axioms union_terminal
end Lower6960.HelperPrefix
