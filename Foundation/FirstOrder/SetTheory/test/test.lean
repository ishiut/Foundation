module

public import Foundation.FirstOrder.SetTheory.Basic
public import Foundation.FirstOrder.Basic.Semantics.Semantics
public import Foundation.FirstOrder.Basic.Syntax.Formula

namespace LO.FirstOrder.SetTheory
namespace Semiformula

variable {V : Type*} [SetStructure V] [hV_Nonempty: Nonempty V] [hV_ZFC : V ⊧ₘ* 𝗭𝗙𝗖]
variable (a : V)

-- scoped instance : HasSubset V := ⟨fun x y ↦ ∀ z ∈ x, z ∈ y⟩

#check V
#check IsEmpty
#check IsEmpty a
#check ToString
#check “∃ e, !isEmpty e → e ∈ e”

def random : Sentence ℒₛₑₜ := “∀ x, !isEmpty x”

def empty : Sentence ℒₛₑₜ := “∃ e, ∀ y, y ∉ e”

def infinity : Sentence ℒₛₑₜ := “∃ I, (∀ e, !isEmpty e → e ∈ I) ∧ (∀ x ∈ I, ∀ x', !isSucc x' x → x' ∈ I)”

#check ZermeloFraenkel.axiom_of_empty_set
#check empty

#check Semiformula.EvalAux
#check Semiformula.eval_ex
#check Models
#check Models V empty
#check models_iff_models
#check Semiformula.Evalbm
#check ModelsTheory.add_iff
#check ZermeloFraenkel
#check ModelsTheory
#check modelsTheory_iff
#check “∃ x, x = x”
#check empty

lemma V_models_empty : V ⊧ₘ empty := by
  -- You can split V ⊧ₘ* 𝗭𝗙𝗖 into V ⊧ₘ* 𝗭𝗙 ∧ V ⊧ₘ* 𝗔𝗖
  simp only [ModelsTheory.add_iff] at hV_ZFC
  obtain ⟨hV_ZF, hV_AC⟩ := hV_ZFC
  -- By this, we can interpret ⊧ₘ* by using ⊧ₘ
  apply modelsTheory_iff.mp at hV_ZF
  -- Use ZermeloFraenkel.axiom_of_empty_set, the instance of Axiom.empty
  apply hV_ZF ZermeloFraenkel.axiom_of_empty_set

example : V ⊧ₘ (“∃ x, x = x” : Sentence ℒₛₑₜ) := by
  -- models_iff translates ⊧ₘ by using evaluation ⊧/!
  rw [models_iff]
  -- These simps can be done by simp?
  simp only [Semiformula.eval_ex]
  simp only [Semiformula.eval_operator_two]
  simp only [Structure.Eq.eq]
  simp only [exists_const]
  -- simp only [Nat.reduceAdd, Fin.Fin1.eq_one, Fin.isValue, Semiformula.eval_ex,
  --   Nat.succ_eq_add_one, Semiformula.eval_operator_two, Semiterm.val_bvar,
  --   Matrix.cons_val_fin_one, Structure.Eq.eq, exists_const]

#check Semiformula.eval_ex

example : V ⊧ₘ (“∃ x, ∀ y, y ∉ x” : Sentence ℒₛₑₜ) := by
  rw [models_iff]
  simp only [Semiformula.eval_ex]
  have h1 : V ⊧ₘ empty := V_models_empty
  rw [models_iff] at h1
  unfold empty at h1
  -- From V ⊧/![] (“∃⁰...”), you can have ∃ x statement.
  rw [Semiformula.eval_ex] at h1
  obtain ⟨e, he⟩ := h1
  use e
  -- simp only [Nat.reduceAdd, Fin.isValue, Semiformula.eval_ex, Nat.succ_eq_add_one,
  --   Semiformula.eval_all, LogicalConnective.HomClass.map_neg, Semiformula.eval_operator_two,
  --   Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.Fin1.eq_one,
  --   Matrix.cons_val_fin_one, Structure.Mem.mem, LogicalConnective.Prop.neg_eq]

-- This is a template to set up the constant of the object that is proven to exist.
lemma V_empty_lemma : ∃ x : V, ∀ y, y ∉ x := by
  have h1 : V ⊧ₘ empty := V_models_empty
  rw [models_iff] at h1
  unfold empty at h1
  rw [Semiformula.eval_ex] at h1
  obtain ⟨e, he⟩ := h1
  use e
  exact he

-- It must be noncomputable.
noncomputable def V_empty : V := Classical.choose V_empty_lemma
variable (v1 : V)

#check V_empty

lemma V_empty_spec: ∀ y : V, y ∉ (V_empty : V) := Classical.choose_spec V_empty_lemma

-- To apply the property of the constant (in this case V_empty), we can use V_empty_lemma
-- obtained as above.
example : V ⊧/![V_empty, v1] (“∀ y, y ∉ #1” : Semiformula ℒₛₑₜ Empty 2) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Semiformula.eval_all,
    LogicalConnective.HomClass.map_neg, Semiformula.eval_operator_two, Semiterm.val_bvar,
    Matrix.cons_val_zero, Matrix.cons_val_one, Structure.Mem.mem, LogicalConnective.Prop.neg_eq]
  intro y
  apply V_empty_spec


#check ZermeloFraenkel Axiom.pairing
#check Axiom.pairing


lemma V_pairing_lemma : ∀ x y : V, ∃ z : V, ∀ w, w ∈ z ↔ w = x ∨ w = y := by
  have h1 : V ⊧ₘ Axiom.pairing := by
      simp only [ModelsTheory.add_iff] at hV_ZFC
      obtain ⟨hV_ZF, hV_AC⟩ := hV_ZFC
      apply modelsTheory_iff.mp at hV_ZF
      apply hV_ZF ZermeloFraenkel.axiom_of_pairing
  rw [models_iff] at h1
  unfold Axiom.pairing at h1
  simp only [Nat.reduceAdd, Fin.isValue, Semiformula.eval_all, Nat.succ_eq_add_one,
    Semiformula.eval_ex, LogicalConnective.HomClass.map_iff, Semiformula.eval_operator_two,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one, Structure.Mem.mem,
    LogicalConnective.HomClass.map_or, Matrix.cons_app_three, Matrix.cons_app_two, Fin.Fin1.eq_one,
    Matrix.cons_val_fin_one, Structure.Eq.eq, LogicalConnective.Prop.or_eq,
    LogicalConnective.Prop.iff_eq] at h1
  apply h1

noncomputable def V_pairing (x y : V) : V := Classical.choose (V_pairing_lemma x y)
#check fun (x y : V) => V_pairing x y

lemma V_pairing_spec (x y : V): ∀ z : V, z ∈ V_pairing x y ↔ z = x ∨ z = y := Classical.choose_spec (V_pairing_lemma x y)

#check V_pairing_spec

-- -- Old definition used in the following parts.
-- lemma V_pairing : ∀ x y : V, ∃ z : V, ∀ w, w ∈ z ↔ w = x ∨ w = y := by
--   have h1 : V ⊧ₘ Axiom.pairing := by
--       simp only [ModelsTheory.add_iff] at hV_ZFC
--       obtain ⟨hV_ZF, hV_AC⟩ := hV_ZFC
--       apply modelsTheory_iff.mp at hV_ZF
--       apply hV_ZF ZermeloFraenkel.axiom_of_pairing
--   rw [models_iff] at h1
--   unfold Axiom.pairing at h1
--   simp only [Nat.reduceAdd, Fin.isValue, Semiformula.eval_all, Nat.succ_eq_add_one,
--     Semiformula.eval_ex, LogicalConnective.HomClass.map_iff, Semiformula.eval_operator_two,
--     Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one, Structure.Mem.mem,
--     LogicalConnective.HomClass.map_or, Matrix.cons_app_three, Matrix.cons_app_two, Fin.Fin1.eq_one,
--     Matrix.cons_val_fin_one, Structure.Eq.eq, LogicalConnective.Prop.or_eq,
--     LogicalConnective.Prop.iff_eq] at h1
--   apply h1


lemma V_singleton : ∀ x : V, ∃ y : V, ∀ z, (z ∈ y ↔ z = x) := by
  intro x
  obtain ⟨y, hy⟩ := V_pairing x x
  use y
  intro z
  constructor
  case h.mp =>
    intro hzy
    apply or_self_iff.mp
    apply (hy z).mp hzy
  case h.mpr =>
    intro hzx
    apply (hy z).mpr
    left
    exact hzx

-- def union : Sentence ℒₛₑₜ := “∀ x, ∃ y, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w”
lemma V_union : ∀ x : V, ∃ y : V, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w := by
  have h1 : V ⊧ₘ Axiom.union := by
    simp only [ModelsTheory.add_iff] at hV_ZFC
    obtain ⟨hV_ZF, hV_AC⟩ := hV_ZFC
    apply modelsTheory_iff.mp at hV_ZF
    apply hV_ZF ZermeloFraenkel.axiom_of_union
  rw [models_iff] at h1
  unfold Axiom.union at h1
  simp only [Nat.reduceAdd, Fin.isValue, Semiformula.eval_all, Nat.succ_eq_add_one,
    Semiformula.eval_ex, LogicalConnective.HomClass.map_iff, Semiformula.eval_operator_two,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one, Structure.Mem.mem,
    Semiformula.eval_bexsMem, Matrix.cons_app_two, Fin.Fin1.eq_one, Matrix.cons_val_fin_one,
    LogicalConnective.Prop.iff_eq] at h1
  apply h1

-- As an example of the axiom of union,
lemma V_tripleton : ∀ a b c : V, ∃ x : V, ∀ y : V, y ∈ x ↔ y = a ∨ y = b ∨ y = c := by
  intro a b c
  obtain ⟨pair_ab, hab⟩ := V_pairing a b
  obtain ⟨singleton_c, hc⟩ := V_singleton c
  obtain ⟨pair_ab_c, h_ab_c⟩ := V_pairing pair_ab singleton_c
  obtain ⟨x, hx⟩ := V_union pair_ab_c
  use x
  intro y
  constructor
  case h.mp =>
    intro hyx
    obtain ⟨w, hw⟩ := (hx y).mp hyx
    obtain hw1 := (h_ab_c w).mp hw.left
    obtain case_ab | case_c := hw1
    case inl =>
      obtain hyw := hw.right
      rw [case_ab] at hyw
      obtain hya | hyb := (hab y).mp hyw
      case inl => left; exact hya
      case inr => right; left; exact hyb
    case inr =>
      right; right
      obtain hyw := hw.right
      rw [case_c] at hyw
      obtain hyc := (hc y).mp hyw
      exact hyc
  case h.mpr =>
    intro hyabc
    obtain hya | hyb | hyc := hyabc
    case inl =>
      rw [hya]
      apply (hx a).mpr
      use pair_ab
      constructor
      case h.left =>
        apply (h_ab_c pair_ab).mpr
        left; rfl
      case h.right =>
        apply (hab a).mpr
        left; rfl
    case inr.inl =>
      rw [hyb]
      apply (hx b).mpr
      use pair_ab
      constructor
      case h.left =>
        apply (h_ab_c pair_ab).mpr
        left; rfl
      case h.right =>
        apply (hab b).mpr
        right; rfl
    case inr.inr =>
      rw [hyc]
      apply (hx c).mpr
      use singleton_c
      constructor
      case h.left =>
        rw [h_ab_c]
        right; rfl
      case h.right =>
        rw [hc]

-- lemma subset_def {a b : V} : a ⊆ b ↔ ∀ x ∈ a, x ∈ b := by rfl
-- def power : Sentence ℒₛₑₜ := “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ⊆ x”
lemma V_power : ∀ x : V, ∃ y : V, ∀ z, z ∈ y ↔ z ⊆ x := by
  intro x
  have h1 : V ⊧ₘ Axiom.power := by
    simp only [ModelsTheory.add_iff] at hV_ZFC
    obtain ⟨hV_ZF, hV_AC⟩ := hV_ZFC
    apply modelsTheory_iff.mp at hV_ZF
    apply hV_ZF ZermeloFraenkel.axiom_of_power_set
  rw [models_iff] at h1
  unfold Axiom.power at h1
  simp only [Nat.reduceAdd, Fin.isValue, Semiformula.eval_all, Nat.succ_eq_add_one,
    Semiformula.eval_ex, LogicalConnective.HomClass.map_iff, Semiformula.eval_operator_two,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one, Structure.Mem.mem,
    Semiformula.eval_substs, Defined.eval_iff, Fin.Fin1.eq_one, Matrix.cons_val_fin_one,
    Matrix.cons_app_two, LogicalConnective.Prop.iff_eq] at h1
  obtain ⟨y, hy⟩ := h1 x
  use y

#check fun (x y : V) => x ∪ y

-- def infinity : Sentence ℒₛₑₜ := “∃ I, (∀ e, !isEmpty e → e ∈ I) ∧ (∀ x ∈ I, ∀ x', !isSucc x' x → x' ∈ I)”
lemma V_infinity : ∃ I, V_empty ∈ I ∧ (∀ x ∈ I, ∀ y, )


end Semiformula
end SetTheory
end FirstOrder
end LO
