import ProximityPrize.SubmissionLower.ContactSparsePoleSupport

namespace ProximityPrize.SubmissionLower.ContactFlagBezout

open scoped BigOperators
open ProximityPrize.SubmissionLower.ContactSparsePoleSupport

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

structure FlagDegree where
  zOnly : ℕ
  yz : ℕ
  all : ℕ
  deriving DecidableEq, Repr

instance : Add FlagDegree := ⟨fun p q ↦
  ⟨p.zOnly + q.zOnly, p.yz + q.yz, p.all + q.all⟩⟩

instance : SMul ℕ FlagDegree := ⟨fun n p ↦
  ⟨n * p.zOnly, n * p.yz, n * p.all⟩⟩

@[simp] theorem add_zOnly (p q : FlagDegree) :
    (p + q).zOnly = p.zOnly + q.zOnly := rfl

@[simp] theorem add_yz (p q : FlagDegree) :
    (p + q).yz = p.yz + q.yz := rfl

@[simp] theorem add_all (p q : FlagDegree) :
    (p + q).all = p.all + q.all := rfl

@[simp] theorem nsmul_zOnly (n : ℕ) (p : FlagDegree) :
    (n • p).zOnly = n * p.zOnly := rfl

@[simp] theorem nsmul_yz (n : ℕ) (p : FlagDegree) :
    (n • p).yz = n * p.yz := rfl

@[simp] theorem nsmul_all (n : ℕ) (p : FlagDegree) :
    (n • p).all = n * p.all := rfl

def InFlag (p : FlagDegree) (d : Fin 3 →₀ ℕ) : Prop :=
  d 1 ≤ p.all ∧
    d 0 + d 1 ≤ p.yz + p.all ∧
    d 0 + d 1 + d 2 ≤ p.zOnly + p.yz + p.all

theorem inFlag_zero (p : FlagDegree) : InFlag p 0 := by
  simp [InFlag]

theorem inFlag_add {p q : FlagDegree} {d e : Fin 3 →₀ ℕ}
    (hd : InFlag p d) (he : InFlag q e) : InFlag (p + q) (d + e) := by
  rcases hd with ⟨hdS, hdYS, hdTot⟩
  rcases he with ⟨heS, heYS, heTot⟩
  simp only [InFlag, Finsupp.add_apply, add_zOnly, add_yz, add_all]
  omega

noncomputable def exponentOfTriple (t : ℕ × ℕ × ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 t.1 + Finsupp.single 1 t.2.1 +
    Finsupp.single 2 t.2.2

noncomputable def flagSupport (p : FlagDegree) : Finset (Fin 3 →₀ ℕ) :=
  by
    classical
    exact (((((Finset.range (p.zOnly + p.yz + p.all + 1)).product
        (Finset.range (p.all + 1))).product
        (Finset.range (p.zOnly + p.yz + p.all + 1))).image
          (fun t ↦ exponentOfTriple (t.1.1, t.1.2, t.2))).filter (InFlag p))

theorem mem_flagSupport_iff (p : FlagDegree) (d : Fin 3 →₀ ℕ) :
    d ∈ flagSupport p ↔ InFlag p d := by
  classical
  constructor
  · intro hd
    unfold flagSupport at hd
    exact (Finset.mem_filter.mp hd).2
  · intro hd
    unfold flagSupport
    rw [Finset.mem_filter]
    refine ⟨?_, hd⟩
    apply Finset.mem_image.mpr
    rcases hd with ⟨hS, hYS, htotal⟩
    refine ⟨((d 0, d 1), d 2), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by simp; omega),
          Finset.mem_range.mpr (by simp; omega)⟩,
        Finset.mem_range.mpr (by simp; omega)⟩
    · ext i
      fin_cases i <;> simp [exponentOfTriple]

theorem zero_mem_flagSupport (p : FlagDegree) :
    (0 : Fin 3 →₀ ℕ) ∈ flagSupport p := by
  rw [mem_flagSupport_iff]
  exact inFlag_zero p

theorem flagSupport_downwardClosed (p : FlagDegree) :
    ExponentSetDownwardClosed (flagSupport p) := by
  intro d hd e he
  rw [mem_flagSupport_iff] at hd ⊢
  rcases hd with ⟨hdS, hdYS, hdtotal⟩
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  exact ⟨h1.trans hdS, by omega, by omega⟩

def PolynomialInFlag {K : Type*} [Field K]
    (p : FlagDegree) (A : MvPolynomial (Fin 3) K) : Prop :=
  ∀ d ∈ A.support, InFlag p d

theorem support_subset_flagSupport_iff {K : Type*} [Field K]
    (p : FlagDegree) (A : MvPolynomial (Fin 3) K) :
    A.support ⊆ flagSupport p ↔ PolynomialInFlag p A := by
  simp only [PolynomialInFlag, Finset.subset_iff, mem_flagSupport_iff]

def flagSWeights : Fin 3 → ℕ := ![0, 1, 0]
def flagYSWeights : Fin 3 → ℕ := ![1, 1, 0]
def flagTotalWeights : Fin 3 → ℕ := ![1, 1, 1]

theorem flag_weight_fin3 (weights : Fin 3 → ℕ) (d : Fin 3 →₀ ℕ) :
    Finsupp.weight weights d =
      d 0 * weights 0 + d 1 * weights 1 + d 2 * weights 2 := by
  have hd : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) +
      Finsupp.single 2 (d 2) := by
    ext i
    fin_cases i <;> simp
  rw [hd, map_add, map_add]
  simp [Finsupp.weight_single, Nat.mul_comm]

def flagMixed (p q r : FlagDegree) : ℕ :=
  p.all * q.all * r.all +
  (p.zOnly * q.all * r.all + q.zOnly * p.all * r.all +
    r.zOnly * p.all * q.all) +
  (p.yz * q.all * r.all + q.yz * p.all * r.all +
    r.yz * p.all * q.all) +
  (p.all * q.yz * r.yz + q.all * p.yz * r.yz +
    r.all * p.yz * q.yz) +
  (p.zOnly * q.yz * r.all + p.zOnly * r.yz * q.all +
    q.zOnly * p.yz * r.all + q.zOnly * r.yz * p.all +
    r.zOnly * p.yz * q.all + r.zOnly * q.yz * p.all)

def unitZFlag : FlagDegree := ⟨1, 0, 0⟩
def unitYZFlag : FlagDegree := ⟨0, 1, 0⟩
def unitAllFlag : FlagDegree := ⟨0, 0, 1⟩

end ProximityPrize.SubmissionLower.ContactFlagBezout
