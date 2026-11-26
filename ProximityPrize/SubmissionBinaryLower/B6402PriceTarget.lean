import ProximityPrize.SubmissionBinaryLower.B6402EndpointBudget
import ProximityPrize.SubmissionBinaryLower.B6402PriceCells

/-! Interpret the numerical target of a dual certificate as the actual
graded budget, in the coordinates returned by the native profile theorem. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402PriceTarget
open B6402LinearCertificate B6402PriceRows B6402EndpointBudget
set_option autoImplicit false
set_option maxHeartbeats 1500000

structure Values where
  f0 : ℚ
  f1 : ℚ
  f2 : ℚ
  f3 : ℚ
  excess : ℚ
  c : ℚ
  v : ℚ
  bound : ℚ
  deriving DecidableEq,Repr

def values (p : Plan) (h : ℚ) : Values :=
  let t := (p.cap:ℚ)-p.s*h
  let m2 := (p.m:ℚ)*p.m
  ⟨cost p t h 0/m2,cost p t h 1/m2,(cost p t h 2+regCost p t h)/m2,
   cost p t h 3/m2,B6402EndpointBudget.excess p t/m2,-(slope p*(t+1)),
   (badCost p t h-regCost p t h)/m2,rhs p h⟩

def Values.row (a : Values) (n : ℕ) : Row :=
   ⟨[(0,a.f0),(1,a.f1),(2,a.f2),(3,a.f3),(4,a.excess),(n-1,a.c),(n,a.v)],a.bound⟩

theorem objective {n : ℕ} (hn : 5≤n) (p : Plan) (h : ℚ) (x : Fin n → ℚ) (v : ℚ) :
    B6402LinearCertificate.lhs ((values p h).row n) (extend x v)=
      B6402EndpointBudget.lhs p h (x ⟨0,by omega⟩) (x ⟨1,by omega⟩) (x ⟨2,by omega⟩) (x ⟨3,by omega⟩)
        (x ⟨4,by omega⟩) (x ⟨n-1,by omega⟩) v := by
  rw [row_lhs]
  have h0 : 0<n := by omega
  have h1 : 1<n := by omega
  have h2 : 2<n := by omega
  have h3 : 3<n := by omega
  have h4 : 4<n := by omega
  have he : n-1<n := by omega
  have outer : ∀ k<n,k<n+1 := by omega
  simp only [Values.row,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    dite_eq_left (outer _ h0),dite_eq_left (outer _ h1),dite_eq_left (outer _ h2),
    dite_eq_left (outer _ h3),dite_eq_left (outer _ h4),dite_eq_left (outer _ he),dite_eq_left (Nat.lt_succ_self n),
    extend,dite_eq_left h0,dite_eq_left h1,dite_eq_left h2,dite_eq_left h3,dite_eq_left h4,
    dite_eq_left he,dite_eq_right (lt_irrefl n)]
  unfold B6402EndpointBudget.lhs values; ring

def represents (n : ℕ) (r : Row) (a : Values) : Bool :=
  decide (r.bound=a.bound ∧ ∀ i : Fin (n+1), coeff r i.val=coeff (a.row n) i.val)

theorem from_literal {n : ℕ} (hn : 5≤n) (p : Plan) (h : ℚ) (a : Values) (r : Row)
    (computed : values p h=a) (checked : represents n r a=true)
    (x : Fin n → ℚ) (v : ℚ) (cut : B6402LinearCertificate.lhs r (extend x v)<r.bound) :
      B6402EndpointBudget.lhs p h (x ⟨0,by omega⟩) (x ⟨1,by omega⟩) (x ⟨2,by omega⟩) (x ⟨3,by omega⟩)
        (x ⟨4,by omega⟩) (x ⟨n-1,by omega⟩) v < rhs p h := by
  subst a; simp only [represents,decide_eq_true_eq] at checked
  have eq : B6402LinearCertificate.lhs r (extend x v)=
      B6402LinearCertificate.lhs ((values p h).row n) (extend x v) := by
    unfold B6402LinearCertificate.lhs dot
    apply Finset.sum_congr rfl; intro j _
    exact congrArg (fun c : ℚ => c*extend x v j) (checked.2 j)
  rw [eq,objective hn,checked.1] at cut
  exact cut

#print axioms from_literal
end ProximityPrize.SubmissionBinaryLower.B6402PriceTarget
