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

namespace LO
namespace FirstOrder
namespace Semiformula
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
    -- rw [models_iff]
    -- unfold Semiformula.Evalbm
    -- unfold ZermeloFraenkelChoice at hV_ZFC
    simp only [ModelsTheory.add_iff] at hV_ZFC
    obtain ⟨hV_ZF, hV_AC⟩ := hV_ZFC
    apply modelsTheory_iff.mp at hV_ZF
    apply hV_ZF ZermeloFraenkel.axiom_of_empty_set

example : V ⊧ₘ (“∃ x, x = x” : Sentence ℒₛₑₜ) := by
    rw [models_iff]
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
    rw [Semiformula.eval_ex] at h1
    obtain ⟨e, he⟩ := h1
    use e
    -- simp only [Nat.reduceAdd, Fin.isValue, Semiformula.eval_ex, Nat.succ_eq_add_one,
    --   Semiformula.eval_all, LogicalConnective.HomClass.map_neg, Semiformula.eval_operator_two,
    --   Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.Fin1.eq_one,
    --   Matrix.cons_val_fin_one, Structure.Mem.mem, LogicalConnective.Prop.neg_eq]

lemma V_empty_lemma : ∃ x : V, ∀ y, y ∉ x := by
    have h1 : V ⊧ₘ empty := V_models_empty
    rw [models_iff] at h1
    unfold empty at h1
    rw [Semiformula.eval_ex] at h1
    obtain ⟨e, he⟩ := h1
    use e
    exact he

noncomputable def V_empty : V := Classical.choose V_empty_lemma

#check V_empty

#check ZermeloFraenkel Axiom.pairing
#check Axiom.pairing

lemma V_singleton : ∀ x : V, ∃ y : V, ∀ z, (z ∈ y ↔ z = x) := by
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
      LogicalConnective.HomClass.map_or, Matrix.cons_app_three, Matrix.cons_app_two,
      Fin.Fin1.eq_one, Matrix.cons_val_fin_one, Structure.Eq.eq, LogicalConnective.Prop.or_eq,
      LogicalConnective.Prop.iff_eq] at h1
    intro x
    obtain ⟨y, hy⟩ := h1 x x
    use y
    intro z
    constructor
    case h.mp =>
        intro hzy
        apply (or_self (z=x)).mp
        apply (hy z).mp hzy
    case h.mpr =>
        intro hzx
        apply (hy z).mpr
        left
        apply hzx

end Semiformula
end FirstOrder
end LO
end Semiformula
end SetTheory
end FirstOrder
end LO
