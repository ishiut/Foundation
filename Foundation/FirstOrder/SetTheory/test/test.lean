import Foundation.FirstOrder.SetTheory.Basic
import Foundation.FirstOrder.Basic.Semantics.Semantics
import Foundation.FirstOrder.Basic.Syntax.Formula
import Foundation.Vorspiel.ExistsUnique
import Foundation.FirstOrder.SetTheory.Z
import Foundation.FirstOrder.SetTheory.Ordinal

namespace LO.FirstOrder.SetTheory
namespace Semiformula

section external

open Classical

variable {V : Type*} [SetStructure V] [hV_Nonempty: Nonempty V] [hV_ZFC : V ⊧ₘ* 𝗭𝗙𝗖]

section local_attribute

-- This does not work without [V ⊧ₘ* 𝗭].
example [V ⊧ₘ* 𝗭] : IsEmpty (∅ : V) := by exact IsEmpty.empty

lemma hV_ZF : V ⊧ₘ* 𝗭𝗙 := by
  unfold ZermeloFraenkelChoice at hV_ZFC
  exact ModelsTheory.of_add_left V 𝗭𝗙 𝗔𝗖

lemma hV_Z : V ⊧ₘ* 𝗭 := by
  apply ModelsTheory.of_ss hV_ZF z_subset_zf

-- By doing this, hV_Z and hV_ZF can be used without explicitly passing them.
attribute [local instance] hV_Z
attribute [local instance] hV_ZF

-- Now, it works without [V ⊧ₘ* 𝗭].
example : IsEmpty (∅ : V) := by exact IsEmpty.empty

section emptyset

example : ∀ x : V, (∀ y : V, y ∉ x) ↔ x = (∅ : V):= by
  intro x
  constructor
  case mp =>
    intro h
    ext z
    constructor
    case a.mp =>
      intro hz
      absurd hz
      apply h
    case a.mpr =>
      intro hz
      simp only [not_mem_empty] at hz
  case mpr =>
    intro hx
    rw [hx]
    simp only [not_mem_empty, not_false_eq_true, implies_true]

example : ∀ x : V, (∀ y : V, y ∉ x) ↔ x = (∅ : V):= by
  apply isEmpty_iff_eq_empty

end emptyset

section singleton

example (x : V) : ∃ y : V, ∀ z : V, (z ∈ y ↔ z = x) := by
  use doubleton x x
  intro z
  constructor
  case h.mp =>
    intro h
    apply mem_doubleton_iff.mp at h
    cases h <;> assumption
  case h.mpr =>
    intro h
    rw [mem_doubleton_iff]
    left; exact h

example (x : V): ∀ z : V, (z ∈ singleton x ↔ z = x) := by
  apply mem_singleton_iff

example (x : V): ∀ z : V, (z ∈ ({x} : V) ↔ z = x) := by
  intro z
  constructor
  case mp =>
    intro hz
    apply mem_singleton_iff.mp at hz
    exact hz
  case mpr =>
    intro hz
    apply mem_singleton_iff.mpr
    exact hz

example : V ⊧ₘ (“∀ x, ∃ y, ∀ z, (z ∈ y ↔ z = x)” : Sentence ℒₛₑₜ) := by
  rw [models_iff]
  simp only [Nat.reduceAdd, Fin.isValue, Semiformula.eval_all, Nat.succ_eq_add_one,
    Semiformula.eval_ex, LogicalConnective.HomClass.map_iff, Semiformula.eval_operator_two,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one, Structure.Mem.mem,
    Matrix.cons_app_two, Fin.Fin1.eq_one, Matrix.cons_val_fin_one, Structure.Eq.eq,
    LogicalConnective.Prop.iff_eq]
  intro x
  use doubleton x x
  intro z
  rw [mem_doubleton_iff]
  simp only [or_self]

end singleton

section union

example : ∀ a b c : V, ∃ x : V, ∀ y : V, y ∈ x ↔ y = a ∨ y = b ∨ y = c := by
  intro a b c
  use sUnion (doubleton (doubleton a b) (singleton c))
  intro y
  constructor
  case h.mp =>
    intro hy
    apply mem_sUnion_iff.mp at hy
    obtain ⟨x, hx1, hx2⟩ := hy
    apply mem_doubleton_iff.mp at hx1
    obtain hab | hc := hx1
    case inl =>
      rw [hab] at hx2
      apply mem_doubleton_iff.mp at hx2
      obtain hya | hyb := hx2
      case inl =>
        left; exact hya
      case inr =>
        right; left; exact hyb
    case inr =>
      rw [hc] at hx2
      apply mem_singleton_iff.mp at hx2
      right; right; exact hx2
  case h.mpr =>
    intro h
    rw [mem_sUnion_iff]
    obtain hya | hyb | hyc := h
    case inl =>
      use doubleton a b
      simp only [mem_doubleton_iff, true_or, true_and]
      left; exact hya
    case inr.inl =>
      use doubleton a b
      simp only [mem_doubleton_iff, true_or, true_and]
      right; exact hyb
    case inr.inr =>
      use singleton c
      simp only [mem_doubleton_iff, or_true, true_and]
      apply mem_singleton_iff.mpr hyc

-- Rewrite by using union of two sets.
example : ∀ a b c : V, ∃ x : V, ∀ y : V, y ∈ x ↔ y = a ∨ y = b ∨ y = c := by
  intro a b c
  use (doubleton a b) ∪ (singleton c)
  intro y
  constructor
  case h.mp =>
    intro h
    simp only [mem_union_iff, mem_doubleton_iff] at h
    obtain (ha | hb) | hc := h
    case inl.inl =>
      left; exact ha
    case inl.inr =>
      right; left; exact hb
    case inr =>
      apply mem_singleton_iff.mp at hc
      right; right; exact hc
  case h.mpr =>
    intro h
    simp only [mem_union_iff, mem_doubleton_iff]
    obtain ha | hb | hc := h
    case inl =>
      left; left; exact ha
    case inr.inl =>
      left; right; exact hb
    case inr.inr =>
      right
      apply mem_singleton_iff.mpr hc

example : ∀ a b c : V, ∃ x : V, ∀ y : V, y ∈ x ↔ y = a ∨ y = b ∨ y = c := by
  intro a b c
  use {a, b, c}
  intro y
  simp only [mem_insert, mem_singleton_iff]

end union

section power

#check power

example : power (∅ : V) = {∅} := by simp only [power_empty]

lemma subset_of_singleton_empty: ∀ x : V, x ⊆ {∅} → x = ∅ ∨ x = {∅} := by
  intro x hx
  by_cases h : ∅ ∈ x
  case pos =>
    right
    ext y
    simp only [mem_singleton_iff]
    constructor
    case h.a.mp =>
      intro hyx
      apply hx at hyx
      simp only [mem_singleton_iff] at hyx
      exact hyx
    case h.a.mpr =>
      intro hy
      simpa only [hy]
  case neg =>
    left
    ext y
    constructor
    case h.a.mp =>
      intro hyx
      absurd hyx
      apply hx at hyx
      simp only [mem_singleton_iff] at hyx
      simpa only [hyx]
    case h.a.mpr =>
      intro hy
      simp only [not_mem_empty] at hy

lemma power_singleton_empty : power ({∅} : V) = {∅, {∅}} := by
  ext y
  simp only [mem_power_iff, mem_insert, mem_singleton_iff]
  constructor
  case a.mp =>
    intro hy
    apply subset_of_singleton_empty
    exact hy
  case a.mpr =>
    intro hy
    obtain hy1 | hy2 := hy
    case inl =>
      simp only [hy1, empty_subset]
    case inr =>
      simp only [hy2, _root_.subset_refl]

end power

section omega

#check (ω : V)

example : (∅ : V) ∈ (ω : V) := by exact empty_mem_ω

example : ∀ x : V, (x ∈ (ω : V) → x ∪ {x} ∈ (ω : V)) := by
  intro x hx
  have h_succ : x ∪ {x} = succ x := by
    unfold succ
    rw [insert_def]
    rw [union_comm]
  rw [h_succ]
  exact ω_succ_closed hx

example : ({∅} : V) ∈ (ω : V) := by
  have h : ({∅} : V) = succ ∅ := by
    unfold succ
    rw [insert_def]
    simp only [union_empty]
  rw [h]
  apply ω_succ_closed
  exact empty_mem_ω

end omega

section kpair

example (x1 y1 x2 y2 : V) : x1 = x2 ∧ y1 =y2 ↔ ⟨x1, y1⟩ₖ =⟨x2, y2⟩ₖ := by
  exact Iff.symm kpair_iff

example (x1 y1 z1 x2 y2 z2 : V) : x1 = x2 ∧ y1 = y2 ∧ z1 = z2 ↔
    ⟨x1, y1, z1⟩ₖ =⟨x2, y2, z2⟩ₖ := by
  constructor
  case mp =>
    intro h
    rw [h.left, h.right.left, h.right.right]
  case mpr =>
    intro h
    simp only [kpair_iff] at h
    exact h

end kpair

section separation

#check separation_exists_eval
#check (“x.&1 = x” : Semiformula ℒₛₑₜ V 1)

variable (a : V)

#check separation_exists_eval a (“x.&1 = x” : Semiformula ℒₛₑₜ V 1)

example : ∃ x : V, (∅ ∉ x) ∧ ∀ y : V, y ∈ x → succ y ∈ x := by
  use {y ∈ ω ; y ≠ ∅}
  simp only [ne_eq, ne_empty_iff_isNonempty, mem_sep_iff, empty_mem_ω, true_and,
    not_isNonempty_iff_isEmpty, isEmpty_iff_eq_empty, and_imp]
  intro y hyω hy_nonempty
  constructor
  case h.left =>
    exact ω_succ_closed hyω
  case h.right =>
    apply isNonempty_def.mpr
    use y
    simp only [mem_succ_self]

def P := (fun (x : V) => x = ∅)
#check P
#check (ℒₛₑₜ-predicate P)
#check (ℒₛₑₜ-predicate (fun (x : V) => x = ∅))
#check fun (n : V) => {y ∈ ω ; y ≠ n}
#check fun (n : V) => (sep ω (fun y => y ≠ n) (by definability))


lemma neq_empty_definable: (ℒₛₑₜ-predicate (fun (x : V) => x ≠ ∅)) := by
  apply Language.Definable.imp
  case hR =>
    exact Language.DefinableFunction.const ∅
  case hS =>
    exact Language.Definable.const False

#check separation_exists

example : ∃ x : V, (∅ ∉ x) ∧ ∀ y : V, y ∈ x → succ y ∈ x := by
  -- obtain ⟨x, hx⟩ := separation_exists (ω : V) (fun (x : V) => x ≠ ∅) neq_empty_definable
  obtain ⟨x, hx⟩ := separation_exists (ω : V) (fun (x : V) => x ≠ ∅) (by definability)
  use x
  constructor
  case h.left =>
    intro h
    apply (hx ∅).mp at h
    absurd h.right
    rfl
  case h.right =>
    intro y hy
    apply (hx (succ y)).mpr
    constructor
    case left =>
      apply ω_succ_closed
      apply (hx y).mp at hy
      apply hy.left
    case right =>
      intro h
      have h1 : y ∈ (∅ : V) := by
        rw [← h]
        simp only [mem_succ_self]
      exact absurd h1 not_mem_empty

end separation

section ordinals

example : IsOrdinal (ω : V) := by
  exact IsOrdinal.ω

example : IsOrdinal (succ (ω : V)) := by
  exact IsOrdinal.succ

#check (0 : V)
#check (1 : V)

example (α : V) (h₁ : IsOrdinal α) (h₂ : α ≠ (0 : V)) : 0 ∈ α := by
  simp only [zero_def]
  have h₃ : 0 ⊆ α := by
    exact empty_subset α
  apply IsOrdinal.subset_iff.mp at h₃
  obtain h₃l | h₃r := h₃
  case inl =>
    rw [h₃l] at h₂
    contradiction
  case inr =>
    exact h₃r

variable (α : Ordinal V)
#check α
#check α.val
#check (10000 : V)

noncomputable def zero : Ordinal V := ⟨∅, IsOrdinal.empty⟩
#check zero
#check zero.val

lemma zero_val : zero.val = (∅ : V) := by
  exact subset_empty_iff_eq_empty.mp fun z a ↦ a

example (α β : Ordinal V) (h : α.val =β.val) : α = β := by
  exact Ordinal.ext h

example (α β : Ordinal V) : α < β ∨ α = β ∨ β < α := by
  exact lt_trichotomy α β

example (α : Ordinal V) (hα : α ≠ zero) : zero < α := by
  have h₁ : zero ≤ α := by
    apply Ordinal.le_def.mpr
    rw [zero_val]
    apply empty_subset
  exact Std.lt_of_le_of_ne h₁ (id (Ne.symm hα))

noncomputable def nat_ordinal : ℕ → Ordinal V
  | 0 => zero
  | n + 1 => Ordinal.succ (nat_ordinal n)

#check nat_ordinal 0

lemma nat_zero : nat_ordinal 0 = (zero : Ordinal V) := by
  exact Ordinal.ext rfl

lemma nat_one : (nat_ordinal 1).val = ({∅} : V) := by
  simp only [nat_ordinal, Ordinal.succ_val]
  rw [zero_val]
  unfold succ
  exact insert_empty_eq ∅

lemma nat_two : (nat_ordinal 2).val = ({∅, {∅}} : V) := by
  unfold nat_ordinal
  simp only [Ordinal.succ_val]
  rw [nat_one]
  unfold succ
  ext x
  simp only [mem_insert, mem_singleton_iff]
  grind

#check IsOrdinal.zero

instance : IsOrdinal (0 : V) := by
  exact IsOrdinal.zero





end ordinals


end local_attribute

end external

end Semiformula
end SetTheory
end FirstOrder
end LO
