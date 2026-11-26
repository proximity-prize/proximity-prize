import ProximityPrize.SubmissionLower.R6966ProofWordSurfaceMarks
import Mathlib.Algebra.Polynomial.Roots

set_option Elab.async false

namespace Research6966.WordSurfacePrice
open Finset Module MvPolynomial WordSurfaceJets WordSurfaceInterpolation WordSurfaceCount WordSurfaceMarks
variable {K ι I :Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype ι]
noncomputable section
set_option maxHeartbeats 800000

private theorem box_loss (x y z a b c:ℕ) (ha:a≤x) (hb:b≤y) (hc:c≤z) :
    x*y*z ≤ (x-a)*(y-b)*(z-c) + (a*y*z+b*x*z+c*x*y) := by
  obtain ⟨x,rfl⟩:=Nat.exists_eq_add_of_le ha
  obtain ⟨y,rfl⟩:=Nat.exists_eq_add_of_le hb
  obtain ⟨z,rfl⟩:=Nat.exists_eq_add_of_le hc
  simp only [Nat.add_sub_cancel_left]
  nlinarith only [Nat.zero_le (a*b*c),Nat.zero_le (a*b*z),Nat.zero_le (a*c*y),Nat.zero_le (b*c*x)]

private theorem two_choose (k:ℕ) : k^2≤2*(k+1).choose 2 := by
  have eq:=Nat.choose_succ_right_eq (k+1) 1
  rw [Nat.choose_one_right,Nat.add_sub_cancel] at eq
  nlinarith

def side (n a d height:ℕ) : ℕ := (n-a)*height+(a-d)

def mixed (v h:Fin 3→ℕ) : ℕ:=v 0*h 1*h 2+v 1*h 0*h 2+v 2*h 0*h 1

/-- A word family on one trivariate equation costs its mixed tridegree
times the square of the agreement ratio. The argument counts words
even if the parameter-map fibre has positive dimension or the surface
is singular at a marked lift. -/
theorem count (points:ι→Fin 3→K) (rows:I→Pol (Fin 3) K) (H:Pol (Fin 3) K) (hn:H≠0)
    (onSurface:∀ x,eval (points x) H=0) (v height:Fin 3→ℕ) (vp:∀ i,H.degreeOf i≤v i)
    (rp:∀ j i,(rows j).degreeOf i≤height i)
    (A d:ℕ) (gap:d<A) (enough:∀ z,A≤(hits (points z) rows).card)
    (shared:∀ x y,x≠y → ((hits (points x) rows)∩(hits (points y) rows)).card≤d) :
    Fintype.card ι*(A-d)^2 ≤ 2*mixed v (fun i=>side (Fintype.card I) A d (height i)) := by
  classical
  let n:=Fintype.card I
  let delta:=A-d
  let t:=2+(∑i,v i)
  let k:=t*delta
  let beta (i:Fin 3):=(n-A)*height i+delta
  let cap (i:Fin 3):=t*(n-A)*height i+(k-1)
  let small (i:Fin 3):=cap i-v i
  have dt:0<delta:=by dsimp [delta];omega
  have tp:2≤t:=by dsimp [t];omega
  have tk:t≤k:=by simpa only [mul_one] using Nat.mul_le_mul_left t (show 1≤delta from dt)
  have k2:2≤k:=tp.trans tk
  have full (i:Fin 3):cap i+1=t*beta i := by
    dsimp only [cap,beta]
    rw [Nat.add_assoc,Nat.sub_add_cancel (by omega)]
    dsimp [k];ring
  have vi (i:Fin 3):v i≤cap i := by
    have vv:v i≤∑j,v j:=Finset.single_le_sum (fun j _=>Nat.zero_le (v j)) (Finset.mem_univ i)
    dsimp only [cap];dsimp only [t] at tk;omega
  have sm (i:Fin 3):small i+1=t*beta i-v i := by
    dsimp only [small];rw [←full];have:=vi i;omega
  obtain ⟨seps,degree,own,other⟩:=separators points rows height rp A d t enough shared
  have onto:=interpolate points k (by omega) (fun j=>t*(n-A)*height j) seps degree own other
  have jets:=trivariate_budget points (k-2) cap small H hn (fun i=>by
    dsimp only [small];have:=vi i;have:=vp i;omega) onSurface (by
      rw [show k-2+2=k by omega];exact onto)
  rw [show k-2+3=k+1 by omega] at jets
  simp only [sm,full,Fin.prod_univ_three] at jets
  have fits (i:Fin 3):v i≤t*beta i:=by rw [←full];exact (vi i).trans (Nat.le_succ _)
  have loss:=box_loss (t*beta 0) (t*beta 1) (t*beta 2) (v 0) (v 1) (v 2) (fits 0) (fits 1) (fits 2)
  let weight:=v 0*beta 1*beta 2+v 1*beta 0*beta 2+v 2*beta 0*beta 1
  have lead:Fintype.card ι*(k+1).choose 2≤t^2*weight := by
    dsimp only [weight]
    nlinarith only [jets,loss]
  have chooseBound:=Nat.mul_le_mul_left (Fintype.card ι) (two_choose k)
  have cancel:Fintype.card ι*delta^2≤2*weight := by
    have scaled:t^2*(Fintype.card ι*delta^2)≤t^2*(2*weight) := by
      dsimp only [k] at chooseBound
      nlinarith only [chooseBound,lead]
    exact Nat.le_of_mul_le_mul_left scaled (by positivity)
  exact cancel


theorem word_overlap {σ:Type*} [Fintype σ] [DecidableEq σ] (points:ι→σ→K) (rows:I→Pol σ K)
    (nodes:I→K) (distinct:Function.Injective nodes) (received:I→K)
    (words:ι→Polynomial K) (unique:Function.Injective words) (d:ℕ) (degree:∀ z,(words z).natDegree≤d)
    (detect:∀ z i,eval (points z) (rows i)=0 ↔ (words z).eval (nodes i)=received i) :
    ∀ x y,x≠y → ((hits (points x) rows)∩(hits (points y) rows)).card≤d := by
  classical
  intro x y ne
  let T:=hits (points x) rows ∩ hits (points y) rows
  have nz:words x-words y≠0:=sub_ne_zero.mpr (fun e=>ne (unique e))
  have sub:T.image nodes ⊆ (words x-words y).roots.toFinset := by
    rintro z hz
    obtain ⟨i,hi,rfl⟩:=mem_image.mp hz
    obtain ⟨hx,hy⟩:=mem_inter.mp hi
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots nz).mpr
    change (words x-words y).eval (nodes i)=0
    rw [Polynomial.eval_sub,(detect x i).mp (hit.mp hx),(detect y i).mp (hit.mp hy),sub_self]
  change T.card≤d
  rw [←card_image_of_injective T distinct]
  exact (card_le_card sub).trans ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans
    ((Polynomial.natDegree_sub_le ..).trans (max_le (degree x) (degree y)))))


/-- Distinct polynomial words supply the pairwise constraint themselves.
The row equations only need to detect agreement on the chosen lifts. -/
theorem count_words (points:ι→Fin 3→K) (rows:I→Pol (Fin 3) K) (H:Pol (Fin 3) K) (hn:H≠0)
    (onSurface:∀ x,eval (points x) H=0) (v height:Fin 3→ℕ) (vp:∀ i,H.degreeOf i≤v i)
    (rp:∀ j i,(rows j).degreeOf i≤height i)
    (nodes:I→K) (distinct:Function.Injective nodes) (received:I→K)
    (words:ι→Polynomial K) (unique:Function.Injective words) (A d:ℕ) (gap:d<A)
    (degree:∀ z,(words z).natDegree≤d)
    (detect:∀ z i,eval (points z) (rows i)=0 ↔ (words z).eval (nodes i)=received i)
    (enough:∀ z,A≤(hits (points z) rows).card) :
    Fintype.card ι*(A-d)^2 ≤ 2*mixed v (fun i=>side (Fintype.card I) A d (height i)) := by
  classical
  apply count points rows H hn onSurface v height vp rp A d gap enough
  exact word_overlap points rows nodes distinct received words unique d degree detect

end
end Research6966.WordSurfacePrice
