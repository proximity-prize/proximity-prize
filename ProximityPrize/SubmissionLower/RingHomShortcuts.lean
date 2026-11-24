import Mathlib.Algebra.Ring.Equiv
set_option Elab.async false

/-! On Lean 4.36 Mathlib the generic search for `AddMonoidHomClass` / `MonoidHomClass` on ring
homs between quotient and polynomial rings exceeds the synthesis budget; these shortcuts resolve
it directly. -/

@[instance high] abbrev ringHomAddMonoidHomClassShortcut {α β : Type*} [NonAssocSemiring α]
    [NonAssocSemiring β] : AddMonoidHomClass (α →+* β) α β := RingHomClass.toAddMonoidHomClass

@[instance high] abbrev ringHomMonoidHomClassShortcut {α β : Type*} [NonAssocSemiring α]
    [NonAssocSemiring β] : MonoidHomClass (α →+* β) α β := RingHomClass.toMonoidHomClass

@[instance high] abbrev ringEquivAddMonoidHomClassShortcut {α β : Type*} [NonAssocSemiring α]
    [NonAssocSemiring β] : AddMonoidHomClass (α ≃+* β) α β := RingHomClass.toAddMonoidHomClass

@[instance high] abbrev ringEquivMonoidHomClassShortcut {α β : Type*} [NonAssocSemiring α]
    [NonAssocSemiring β] : MonoidHomClass (α ≃+* β) α β := RingHomClass.toMonoidHomClass
