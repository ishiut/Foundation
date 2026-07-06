import Foundation.FirstOrder.SetTheory.Basic
import Foundation.FirstOrder.Basic.Semantics.Semantics
import Foundation.FirstOrder.Basic.Syntax.Formula
import Foundation.Vorspiel.ExistsUnique
import Foundation.FirstOrder.SetTheory.Z

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

end local_attribute

end external

end Semiformula
end SetTheory
end FirstOrder
end LO
