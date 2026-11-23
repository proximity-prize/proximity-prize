import ProximityPrize.SubmissionLower.ZSyXMse
import ProximityPrize.SubmissionLower.ZyCQ7Ke
import ProximityPrize.SubmissionLower.Zd8LTIa
set_option Elab.async false
open _root_ renaming Algebra → zZE, Field → zrb, Function.Injective → zq4, MvPolynomial → z3y, MvPolynomial.X → z9v, Polynomial.X → z7y, RingHom.id → zz4
section
set_option autoImplicit true
namespace qoRVxvd
open aR (ao)
open MvPolynomial
noncomputable section
abbrev Poly := z3y (Fin 3) ao
abbrev Exp := Fin 3 →₀ ℕ
def masks (q d : ℕ) : Set Exp :=
  {e | e 0 + e 1 + e 2 = q ∧ d ≤ e 1 + e 2 ∧ e 1 + 2*e 2 ≤ 27 ∧ e 2 ≤ 12}
abbrev Source (q d : ℕ) := restrictSupport ao (masks q d)
def gw (q d : ℕ) := min (q+1) (28-d)
def lo (q d n : ℕ) := n - (q-d)
def stop (n : ℕ) := min 12 (min n (27-n)) + 1
def width (q d n : ℕ) := stop n - lo q d n
def rows (n h : ℕ) := min 12 (min n (h-1-n)) + 1
def Bp (q d h n : ℕ) := if n < h then min (width q d n) (rows n h) else 0
abbrev jJ (q d : ℕ) := Fin (gw q d)
abbrev Index (q d h : ℕ) := Σ n : jJ q d, Fin (width q d n - Bp q d h n)
def α (q c : ℕ) := c - (27-q)
def r₁ (q n i h : ℕ) := min (h-n) (27-q-i)
def a₀ (q n i h : ℕ) := α q (i + r₁ q n i h)
local notation "A" => (MvPolynomial.X 0 : Poly)
local notation "V" => (MvPolynomial.X 1 : Poly)
local notation "W" => (MvPolynomial.X 2 : Poly)
def witness (q n i h : ℕ) : Poly :=
  let r := h - n
  let s := r₁ q n i h
  let a := a₀ q n i h
  V^(q-n-a-(r-s)) * (A-V)^(n-i-r) * W^i * A^a *
    (A-V+W)^s * (V*(A-V)+A*W)^(r-s)
abbrev Target := z3y (Fin 2) ao
def bY : Poly →ₐ[ao] Target :=
  aeval ![1, 1 + z9v 1, z9v 1 + z9v 0]
def wt : Fin 2 → ℕ := ![2, 1]
end
end qoRVxvd
end
section
set_option autoImplicit true
namespace qoRVxvd
open aR (ao)
open qmb8rCe (box cap sumN_eq)
open MvPolynomial
open scoped BigOperators
noncomputable section
private def exp (a b c : ℕ) : Exp := Finsupp.equivFunOnFinite.symm ![a,b,c]
private theorem exp_apply (a b c : ℕ) :
    (exp a b c) 0 = a ∧ (exp a b c) 1 = b ∧ (exp a b c) 2 = c := by
  simp [exp]
private abbrev sourceIndex (q d : ℕ) := Σ n : jJ q d, Fin (width q d n)
private def encode {q d : ℕ} (hq : q ≤ 27) (hd : d ≤ q) (e : masks q d) :
    sourceIndex q d := by
  have hg := e.property.1
  have hl := e.property.2.1
  have hw := e.property.2.2.1
  have ht := e.property.2.2.2
  let c := e.val 2
  let a := e.val 0
  let n := a + c - α q c
  have hc : α q c ≤ a := by dsimp [α, a, c]; omega
  have he : n < gw q d := by dsimp [n, α, a, c, gw]; omega
  have hcl : lo q d n ≤ c := by dsimp [lo, n, α, a, c]; omega
  have hcu : c < stop n := by dsimp [stop, n, α, a, c]; omega
  refine ⟨⟨n, he⟩, ⟨c-lo q d n, ?_⟩⟩
  change c-lo q d n < width q d n
  unfold width
  omega
private def decode {q d : ℕ} (hq : q ≤ 27) (hd : d ≤ q) (j : sourceIndex q d) :
    masks q d := by
  let n := j.1.val
  let c := lo q d n + j.2.val
  let a := n-c+α q c
  have hn : n < gw q d := j.1.isLt
  have hi : j.2.val < width q d n := j.2.isLt
  have hcu : c < stop n := by dsimp [c, width] at *; omega
  have hcn : c ≤ n := by unfold stop at hcu; omega
  have hq' : a+c ≤ q := by dsimp [a, α, gw, stop] at *; omega
  refine ⟨exp a (q-a-c) c, ?_⟩
  change _ + _ + _ = q ∧ _ ≤ _ + _ ∧ _ + 2*_ ≤ 27 ∧ _ ≤ 12
  have he := exp_apply a (q-a-c) c
  rw [he.1, he.2.1, he.2.2]
  dsimp [a, α, gw, stop, c, lo] at *
  omega
private def maskEquiv {q d : ℕ} (hq : q ≤ 27) (hd : d ≤ q) :
    masks q d ≃ sourceIndex q d where
  toFun := encode hq hd
  invFun := decode hq hd
  left_inv e := by
    obtain ⟨hg, hl, hw, ht⟩ := e.property
    have hc : α q (e.val 2) ≤ e.val 0 := by unfold α; omega
    have hi : lo q d (e.val 0 + e.val 2 - α q (e.val 2)) ≤ e.val 2 := by unfold lo; omega
    have he : lo q d (e.val 0 + e.val 2 - α q (e.val 2)) +
        (e.val 2 - lo q d (e.val 0 + e.val 2 - α q (e.val 2))) = e.val 2 := by omega
    apply Subtype.ext
    ext j
    fin_cases j <;> simp [decode, encode, exp, he] <;> omega
  right_inv j := by
    obtain ⟨n,i⟩ := j
    have hn := n.isLt
    have hi := i.isLt
    have hcu : lo q d n + i.val < stop n := by unfold width at hi; omega
    have hcn : lo q d n + i.val ≤ n := by unfold stop at hcu; omega
    let p := encode hq hd (decode hq hd ⟨n,i⟩)
    have he : p.1 = n := by
      apply Fin.ext
      simp [p, encode, decode, exp]
      omega
    refine Sigma.ext he ((Fin.heq_ext_iff (congrArg (fun j : jJ q d => width q d j) he)).2 ?_)
    have he' := congrArg (fun j : jJ q d => lo q d j) he
    change lo q d p.1 = lo q d n at he'
    change p.2.val = i.val
    have hp₂ : p.2.val = lo q d n + i.val - lo q d p.1 := by simp [p, encode, decode, exp]
    rw [hp₂, he', Nat.add_sub_cancel_left]
theorem finiteSource {q d : ℕ} (hq : q ≤ 27) (hd : d ≤ q) :
    Module.Finite ao (Source q d) := by
  let := Fintype.ofEquiv (sourceIndex q d) (maskEquiv hq hd).symm
  exact Module.Finite.of_basis (basisRestrictSupport ao (masks q d))
theorem stock {q d : ℕ} (hq : q ≤ 27) (hd : d ≤ q) :
    Module.finrank ao (Source q d) = ∑ n : jJ q d, width q d n := by
  let := Fintype.ofEquiv (sourceIndex q d) (maskEquiv hq hd).symm
  rw [Module.finrank_eq_card_basis (basisRestrictSupport ao (masks q d)),
    Fintype.card_congr (maskEquiv hq hd)]
  simp [sourceIndex]
theorem count (q d h : ℕ) :
    Fintype.card (Index q d h) + (∑ n : jJ q d, Bp q d h n) =
      ∑ n : jJ q d, width q d n := by
  rw [Fintype.card_sigma, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [Fintype.card_fin, Nat.sub_add_cancel]
  unfold Bp
  split
  · exact min_le_left _ _
  · exact Nat.zero_le _
theorem kept_eq (q d h : ℕ) : (∑ n : jJ q d, Bp q d h n) = cap box q d h := by
  rw [Fin.sum_univ_eq_sum_range, cap, sumN_eq]
  have hm : min (q + 1) (min (box.j + 1 - d) h) = min (gw q d) h := by
    change min (q+1) (min (28-d) h) = min (min (q+1) (28-d)) h
    exact (min_assoc ..).symm
  rw [hm]
  have hr : Finset.range (min (gw q d) h) = (Finset.range (gw q d)).filter (· < h) := by
    ext n
    simp [lt_min_iff]
  rw [hr, Finset.sum_filter]
  rfl
theorem witness_bounds {q d h : ℕ} (hq : q ≤ 27) (hd : d ≤ q) (j : Index q d h) :
    let n := j.1.val
    let i := lo q d n + j.2.val
    i + (h-n) < stop n ∧ n + a₀ q n i h + (h-n-r₁ q n i h) ≤ q ∧
      n + a₀ q n i h ≤ q-d+i := by
  dsimp only
  let n := j.1.val
  let i := lo q d n + j.2.val
  have hn : n < gw q d := j.1.isLt
  have hi : j.2.val < width q d n - Bp q d h n := j.2.isLt
  have hstop : i + (h-n) < stop n := by
    by_cases hh : n < h
    · have hr : rows n h < width q d n := by
        simp only [Bp, ite_eq_left hh] at hi
        omega
      have he : rows n h = h-n := by
        unfold rows width stop at *
        omega
      have hi' : j.2.val < width q d n - min (width q d n) (rows n h) := by
        simpa only [Bp, ite_eq_left hh] using hi
      have hij : j.2.val + rows n h < width q d n := by omega
      unfold width at hij
      dsimp [i]
      omega
    · simp only [Bp, ite_eq_right hh, Nat.sub_zero, width] at hi
      dsimp [i]
      omega
  have hnq : n ≤ q := by unfold gw at hn; omega
  have hnd : n ≤ 27-d := by unfold gw at hn; omega
  refine ⟨hstop, ?_, ?_⟩
  · change n + a₀ q n i h + (h-n-r₁ q n i h) ≤ q
    unfold a₀ α r₁
    unfold stop at hstop
    omega
  · change n + a₀ q n i h ≤ q-d+i
    have hil : n - (q-d) ≤ i := by simp [i, lo]
    unfold a₀ α r₁
    omega
end
end qoRVxvd
end
section
section
namespace q8Z6NHc
noncomputable section
open Polynomial
open cu (L)
open qZu9hjc (atPair gauge jacobian)
open scoped Classical
abbrev Slot (d s a :ℕ) := {ij:Fin (d+1)×Fin (a+1) // ij.2.val+ij.1.val*s≤a}
abbrev Index (d s a :ℕ) :=Slot d s a ⊕ Slot d s (a+s+1)
abbrev jo (d s a :ℕ) :=z3y (Index d s a) L
abbrev Generic (d s a :ℕ) :=AlgebraicClosure (FractionRing (jo d s a))
def form {F:Type} [zrb F] {d s a :ℕ} (u:Slot d s a→F) :F[X][X] :=
 ∑ i,monomial i.val.1.val (monomial i.val.2.val (u i))
def genericF (d s a :ℕ) : (Generic d s a)[X][X] :=
 form fun i=>algebraMap (jo d s a) (Generic d s a) (z9v (Sum.inl i))
def genericG (d s a :ℕ) : (Generic d s a)[X][X] :=
 form fun i=>algebraMap (jo d s a) (Generic d s a) (z9v (Sum.inr i))
structure UniversalValue (d s a :ℕ) (b c:L) where
 size :ℕ
 pt:Fin size→Generic d s a×Generic d s a
 distinct :zq4 pt
 f_zero : ∀ i,atPair (zz4 _) (pt i).1 (pt i).2 (genericF d s a)=0
 g_zero : ∀ i,atPair (zz4 _) (pt i).1 (pt i).2 (genericG d s a)=0
 all_roots : ∀ x y,atPair (zz4 _) x y (genericF d s a)=0 →
   atPair (zz4 _) x y (genericG d s a)=0 → ∃ i,pt i=(x,y)
 simple : ∀ i,jacobian (zz4 _) (pt i).1 (pt i).2 (genericF d s a) (genericG d s a)≠0
 gauge_ne : ∀ i,gauge b c (pt i).2≠0
 R: (jo d s a)[X]
 primitive :R.IsPrimitive
 scalar :Generic d s a
 scalar_ne :scalar≠0
 product :R.map (algebraMap (jo d s a) (Generic d s a))=C scalar *
   ∏ i,((z7y: (Generic d s a)[X]) - C
     (atPair (zz4 _) (pt i).1 (pt i).2 (genericF d s a).derivative /
     gauge b c (pt i).2^(d-2)))
def actualCoeffs {E :Type} [zrb E] {d s a :ℕ} (f g:E[X][X]) :Index d s a→E
 | .inl i=>(f.coeff i.val.1).coeff i.val.2
 | .inr i=>(g.coeff i.val.1).coeff i.val.2
def perturb {E :Type} [zrb E] [zZE L E] {d s a :ℕ}
    (α:Index d s a→E) (δ:Index d s a→L) (r :jo d s a) :E[X] :=
  r.eval₂ (C.comp (algebraMap L E))
    (fun i=>C (α i)+C (algebraMap L E (δ i))*(z7y:E[X]))
def extract {E :Type} [zrb E] [zZE L E] {d s a :ℕ}
    (α:Index d s a→E) (δ:Index d s a→L) (R: (jo d s a)[X]) (n:ℕ) :E[X] :=
  R.sum fun i r=>monomial i ((perturb α δ r).coeff n)
def kK (s a d b e :ℤ) :ℤ:=d*b+e*a-d*e*s
def rawDegree (d a s :ℤ) :ℤ :=
 kK s a d (a+s+1) d+kK s a d (a-s) (d-1)+kK s (a+s+1) d (a-s) (d-1)
def boundary (d a s :ℤ) :ℤ:=2*(a-d*s)+s+1
end
end q8Z6NHc
end
section
namespace q14iMuc
noncomputable section
open Polynomial qps5rle
open P5 (K p)
open cu (L)
open scoped WithZero
theorem discr_map {R F:Type*} [CommRing R] [IsDomain R] [CommRing F] [IsDomain F]
   (φ:R →+* F) (hφ:zq4 φ) (f :R[X]) (hd:0<f.natDegree) :
   (f.map φ).discr=φ f.discr := by
 have hdeg:=natDegree_map_eq_of_injective hφ f
 have hpos :0<(f.map φ).natDegree :=hdeg.symm ▸ hd
 have h:=congrArg φ (resultant_deriv (natDegree_pos_iff_degree_pos.mp hd))
 rw [← resultant_map_map,← derivative_map,map_mul,map_mul,map_pow,map_neg,map_one,
   ← leadingCoeff_map_of_injective hφ,← hdeg,resultant_deriv
     (natDegree_pos_iff_degree_pos.mp hpos)] at h
 exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
   (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hpos))) h
theorem discr_scale {R:Type*} [CommRing R] [IsDomain R]
   (c:R) (hc:c≠0) (f :R[X]) (hd:0<f.natDegree) :
   (C c*f).discr=c^(2*f.natDegree-2)*f.discr := by
 have hdeg:=natDegree_C_mul hc (p:=f)
 have hpos :0<(C c*f).natDegree :=hdeg.symm ▸ hd
 have h:=resultant_deriv (natDegree_pos_iff_degree_pos.mp hpos)
 rw [hdeg,derivative_C_mul,resultant_C_mul_left,resultant_C_mul_right,
   resultant_deriv (natDegree_pos_iff_degree_pos.mp hd),leadingCoeff_mul,leadingCoeff_C] at h
 have hexp:f.natDegree-1+f.natDegree=(2*f.natDegree-2)+1 := by omega
 apply mul_left_cancel₀ (a :=(-1 :R)^(f.natDegree*(f.natDegree-1)/2) *
   (c*f.leadingCoeff)) (mul_ne_zero (pow_ne_zero _ (by simp))
     (mul_ne_zero hc (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hd))))
 rw [← h,← mul_assoc (c^(f.natDegree-1)),← pow_add,hexp,pow_succ]
 ring
theorem discr_ne {E :Type} [zrb E] [zZE L E] (f :E[X][X])
  (hi:Irreducible f) (hd:0<f.natDegree) (hp:f.natDegree<p) :f.discr≠0:= by
 let F:=FractionRing E[X]
 let φ:=algebraMap E[X] F
 have hφ:zq4 φ:=IsFractionRing.injective E[X] F
 let g:=f.map φ
 have hdeg:g.natDegree=f.natDegree :=natDegree_map_eq_of_injective hφ f
 have hg:0<g.natDegree :=hdeg.symm ▸ hd
 have hpg:g.natDegree<p:=hdeg.symm ▸ hp
 have hir :Irreducible g :=
  ((hi.isPrimitive hd.ne').irreducible_iff_irreducible_map_fraction_map (K:=F)).mp hi
 let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let _:CharP E p:=charP_of_injective_ringHom (algebraMap L E).injective p
 let _:CharP E[X] p:=charP_of_injective_ringHom (C_injective (R:=E)) p
 let _:CharP F p:=charP_of_injective_ringHom hφ p
 have hn: (g.natDegree :F)≠0:= fun hz =>
  hpg.not_ge (Nat.le_of_dvd hg ((CharP.cast_eq_zero_iff F p _).mp hz))
 have hh:g.derivative.coeff (g.natDegree-1)≠0:= by
  have he :g.natDegree-1+1=g.natDegree := by omega
  have ha :=congrArg (fun n:ℕ=>(n:F)) he
  simp only [Nat.cast_add,Nat.cast_one] at ha
  rw [coeff_derivative,he,ha,coeff_natDegree]
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hir.ne_zero) hn
 have hder :g.derivative≠0:= fun hz=>hh (by rw [hz,coeff_zero])
 have hdd:g.derivative.natDegree=g.natDegree-1 :=
  le_antisymm (natDegree_derivative_le _) (le_natDegree_of_ne_zero hh)
 have hc:=(separable_iff_derivative_ne_zero hir).mpr hder
 have hr :=resultant_ne_zero g g.derivative hc
 rw [hdd,resultant_deriv (natDegree_pos_iff_degree_pos.mp hg)] at hr
 intro hz
 apply hr
 have hm:g.discr=0:= by rw [discr_map φ hφ f hd,hz,map_zero]
 rw [hm,mul_zero]
private theorem trailing_map {E F:Type*} [zrb E] [zrb F] (φ:E →+* F)
   (hφ:zq4 φ) (g:E[X]) : (g.map φ).trailingCoeff=φ g.trailingCoeff := by
 by_cases hg:g=0
 · simp [hg]
 have hgm:g.map φ≠0:=(Polynomial.map_ne_zero_iff hφ).mpr hg
 have hdeg: (g.map φ).natTrailingDegree=g.natTrailingDegree := by
   rw [natTrailingDegree_eq_support_min' hgm,natTrailingDegree_eq_support_min' hg]
   simp only [support_map_of_injective _ hφ]
 rw [trailingCoeff,trailingCoeff,hdeg,coeff_map]
theorem initialAt_map {E :Type} [zrb E] [zZE L E] (φ:E →ₐ[L] SeedSeries)
  (x :L) (g:E[X]) :initialAt x (g.map φ.toRingHom)=φ (initialAt x g) := by
 unfold initialAt
 have hc:φ.toRingHom (algebraMap L E x)=algebraMap L SeedSeries x :=φ.commutes x
 rw [← hc,← map_taylor g _ φ.toRingHom,trailing_map φ.toRingHom φ.injective]
 rfl
private theorem initialAt_mul {E :Type} [zrb E] [zZE L E]
  (x :L) (f g:E[X]) :initialAt x (f*g)=initialAt x f*initialAt x g:= by
 simp only [initialAt,taylor_mul,trailingCoeff_mul]
private theorem initialAt_parameter_pow {E :Type} [zrb E] [zZE L E]
   (x :L) (n:ℕ) :initialAt x ((physicalParameter x :E[X])^n)=1 := by
 have ht: (physicalParameter x :E[X]).taylor (algebraMap L E x)=Polynomial.X:= by
   rw [show (physicalParameter x :E[X])=z7y - C (algebraMap L E x) from rfl,
     map_sub,taylor_X,taylor_C,add_sub_cancel_right]
 rw [initialAt,taylor_pow,ht,trailingCoeff,natTrailingDegree_X_pow]
 simp
private theorem initialAt_C {E :Type} [zrb E] [zZE L E]
   (x :L) (c:E) :initialAt x (C c)=c:= by
 by_cases hc:c=0
 · simp [hc,initialAt]
 rw [initialAt,taylor_C,trailingCoeff_eq_coeff_zero (by simpa using hc),coeff_C_zero]
theorem initialAt_identity {E :Type} [zrb E] [zZE L E]
  (x :L) (a b n:ℕ) (u:E) (f g:E[X])
  (h: (physicalParameter x)^a*g=(physicalParameter x)^b*C (u^n)*f) :
  initialAt x g=u^n*initialAt x f := by
 simpa only [initialAt_mul,initialAt_parameter_pow,initialAt_C,one_mul] using
  congrArg (initialAt x) h
theorem site_det {E :Type} [zrb E] [zZE L E]
   (R:qE3Ebna.SiteTarget) (z :E) (V:Fin 2→L) (M:Matrix (Fin 2) (Fin 2) L) :
   (siteMatrix R z V M).det =
     physicalParameter R.center*C (targetDet R z V*algebraMap L E M.det) := by
 unfold siteMatrix
 rw [Matrix.det_mul]
 have hm: (M.map (C.comp (algebraMap L E))).det=C (algebraMap L E M.det) :=
   ((C.comp (algebraMap L E)).map_det M).symm
 rw [hm,C_mul,← mul_assoc]
 congr 1
 rw [Matrix.det_fin_two_of,targetDet,map_sub,map_mul,map_mul,mul_sub]
 ring
theorem constant_val_le (x :L) :vSeed (algebraMap L SeedSeries x)≤1 := by
 rw [LaurentSeries.algebraMap_apply,← WithZero.exp_zero]
 apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero L (D:=0)).mpr
 intro n hn
 simp [HahnSeries.C_apply,HahnSeries.coeff_single_of_ne (ne_of_lt hn)]
private theorem small_coeff_zero {z :SeedSeries} (h:vSeed z<1) :z.coeff 0=0:= by
 by_cases hz :z=0
 · simp [hz]
 have hv :vSeed z≠0:=vSeed.ne_zero_iff.mpr hz
 have hh:WithZero.log (vSeed z)<0 :=
   (WithZero.log_lt_iff_lt_exp hv).mpr (by simpa only [WithZero.exp_zero] using h)
 exact (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero L hv).mp le_rfl 0 (by omega)
theorem coeff_nonzero_val_le {z :SeedSeries} (h:z.coeff 0≠0) :1≤vSeed z :=
 le_of_not_gt fun hz=>h (small_coeff_zero hz)
theorem constant_val_eq (x :L) (hx :x≠0) :vSeed (algebraMap L SeedSeries x)=1 :=
 le_antisymm (constant_val_le x) (coeff_nonzero_val_le (by
  simpa [LaurentSeries.algebraMap_apply,HahnSeries.C_apply] using hx))
theorem coeff_nonzero_of_val_eq {z :SeedSeries} (h:vSeed z=1) :z.coeff 0≠0:= by
  intro hz
  have hb:vSeed z≤WithZero.exp (-1 :ℤ) := by
    apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero L).mpr
    intro n hn
    by_cases hnz :n=0
    · simpa only [hnz] using hz
    · apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero L (D:=0)).mp
        (by simp only [neg_zero,WithZero.exp_zero,h,le_refl])
      omega
  exact ((WithZero.exp_lt_one_iff.mpr (show (-1 :ℤ)<0 by omega)).not_ge) (h ▸ hb)
end
end q14iMuc
end
section
set_option backward.isDefEq.respectTransparency false
namespace qymFiQe
noncomputable section
open Polynomial qps5rle
open P5 (p)
open cu (L)
open scoped BigOperators
abbrev F:=PhysicalSeries
abbrev Roots :=AlgebraicClosure F
abbrev Simple (w:Roots) :=IntermediateField.adjoin F ({w} : Set Roots)
abbrev IntegerRing:=vPhysical.valuationSubring
abbrev point (w:Roots) :Simple w:=⟨w,IntermediateField.mem_adjoin_simple_self F w⟩
def seed :F:=algebraMap SeedSeries F (HahnSeries.single 1 1)
def coefficientwise (D:Derivation ℤ F F) :Prop :=
 ∀ (a :F) (i:ℤ),(D a).coeff i=LaurentSeries.derivative L (a.coeff i)
def constants {A:Type} [zrb A] [zZE ℤ A] (D:Derivation ℤ A A) :Subfield A where
  carrier := {a | D a=0}
  zero_mem' := D.map_zero
  one_mem' := D.map_one_eq_zero
  add_mem' := fun {a b} ha hb=> by
    change D a=0 at ha
    change D b=0 at hb
    change D (a+b)=0
    simp [ha,hb]
  neg_mem' := fun {a} ha=> by
    change D a=0 at ha
    change D (-a)=0
    simp [ha]
  mul_mem' := fun {a b} ha hb=> by
    change D a=0 at ha
    change D b=0 at hb
    change D (a*b)=0
    simp [D.leibniz,ha,hb]
  inv_mem' := fun {a} ha=> by
    change D a=0 at ha
    change D a⁻¹=0
    simp [D.leibniz_inv,ha]
def smallConstants (D:Derivation ℤ F F) (w:Roots) :Subfield (Simple w) :=
  (constants D).map (algebraMap F (Simple w)) ⊔
    Subfield.closure (Set.range (fun a :Simple w=>a^p))
def btY (D:Derivation ℤ F F) (w:Roots) (c:Fin p→smallConstants D w) :Simple w :=
 ∑ i,(c i:Simple w)*algebraMap F (Simple w) seed^(i:ℕ)
end
end qymFiQe
end
end
