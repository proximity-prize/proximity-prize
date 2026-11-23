import ProximityPrize.SubmissionLower.ZskDvCd
set_option Elab.async false
set_option autoImplicit true
namespace qK9H6va
noncomputable section
open aR (ao)
open fP (Form Ew GS m9 Jx)
open MvPolynomial
open scoped BigOperators
def iO (q:ℕ) :ℕ:=min q (P6_6_1.asu q)
theorem gAv (q:ℕ) :P6_6_1.asu q≤56:= by
  unfold P6_6_1.asu
  split <;> (try split) <;> omega
def offset (r :ℕ) :ℤ:=(r :ℤ) - 56
def Vm (q:ℕ) (g:ℤ) :ℤ:=99-(q:ℤ) - g
def auo (q:ℕ) (g:ℤ) :GS (iO q) (-g) 56 16 →ₗ[ao] Form :=
  ((weightedTruncation m9 (Vm q g).toNat).comp
    Jx.toLinearMap).domRestrict _
def b5w (q:ℕ) :ℕ :=
  ∑ r :Fin 155,Module.finrank ao (LinearMap.range (auo q (offset r)))
abbrev Lh (d:ℕ) (lo:ℤ) :=
  {m:Fin 4 →₀ ℕ // Ew d lo 56 16 m}
abbrev af (d cutoff :ℕ) :=
  {m:Fin 4 →₀ ℕ // m.degree=d∧m.weight m9<cutoff}
instance columnFinite (d:ℕ) (lo:ℤ) :Finite (Lh d lo) :=
  ((Finsupp.finite_of_degree_le _).subset fun _ (h:Ew _ _ _ _ _) =>
    Nat.le_of_eq h.1).to_subtype
instance rowFinite (d cutoff :ℕ) :Finite (af d cutoff) :=
  ((Finsupp.finite_of_degree_le _).subset fun _ (h:_∧_) =>
    Nat.le_of_eq h.1).to_subtype
instance columnFintype (d:ℕ) (lo:ℤ) :Fintype (Lh d lo) :=Fintype.ofFinite _
instance rowFintype (d cutoff :ℕ) :Fintype (af d cutoff) :=Fintype.ofFinite _
abbrev XN (q:ℕ) (g:ℤ) :=Lh (iO q) (-g)
abbrev ait (q:ℕ) (g:ℤ) :=af (iO q) (Vm q g).toNat
def prefixMatrix (d:ℕ) (lo:ℤ) (cutoff :ℕ) :Matrix (af d cutoff) (Lh d lo) (ZMod P1.p) :=
  fun e m=>((e.val 1).choose (m.val 1) :ZMod P1.p) *
    ((e.val 2).choose (m.val 2) :ZMod P1.p)*((e.val 3).choose (m.val 3) :ZMod P1.p)
def Gy (q:ℕ) (g:ℤ) :Matrix (ait q g) (XN q g) (ZMod P1.p) :=
  prefixMatrix (iO q) (-g) (Vm q g).toNat
def Oi (q:ℕ) :ℕ :=
  ∑ r :Fin 155,(Gy q (offset r)).rank
private def r0:List ℕ :=
  [99,392,970,1920,3325, 5264,7812,11040,15015,
    19800,25454,32032,39585,48160,57800,68544,80427]
private def r1 :List ℕ :=
  [93398,107406,122400,138329,154908,171787,188632,205125,220964,
    235936,249768,262274, 273280,282900,291176,298217,304062]
private def r2 :List ℕ :=
  [308815, 312512,315252,317068,318054,318240,317715, 316506,314697,
    312312,309431,306075, 302319,298181, 293732,288987,284012]
private def r3:List ℕ :=
  [278819,273470,267974, 262388,256718,251017,245288,239579,233890,
    228226,222587,216978,211399,205856,200349,194884,189461]
private def r4 :List ℕ :=
  [184087,178762,173493,168280,163131,158044,153027,148077,143202,
    138399,133673,129022,124450,119955,115541,111206,106953]
private def r5:List ℕ :=
  [102782,98694,94690,90770,86937,83188,79527,75952,72465,
    69065,65753,62529,59394,56346,53388,50517,47736]
private def r6:List ℕ :=
  [45042,42437,39920,37491,35149,32895, 30727,28647,26651,
    24742,22884, 21143,19387,17812,16135,14724,13116]
private def r7:List ℕ :=
  [11869,10332,9249,7799,6880,5544,4788,3602,3006,
    2017,1577,601,432,0,0]
def aPJ:List ℕ :=
  r0 ++ r1 ++ r2 ++ r3 ++ r4 ++ r5 ++ r6 ++ r7
def Ni (q:ℕ) :ℕ:=aPJ[q]!
def RankBand (lo hi:ℕ) :Prop :=
  ∀ q,47≤q→q≤131→lo≤ iO q→iO q≤hi →
    Oi q≤Ni q
end
end qK9H6va
