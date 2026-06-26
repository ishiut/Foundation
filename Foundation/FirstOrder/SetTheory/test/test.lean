module

public import Foundation.FirstOrder.SetTheory.Basic
public import Foundation.FirstOrder.Basic.Semantics.Semantics
public import Foundation.FirstOrder.Basic.Syntax.Formula

namespace LO.FirstOrder.SetTheory
namespace Semiformula

variable {V : Type*} [SetStructure V] [Nonempty V] [V ⊧ₘ* 𝗭𝗙𝗖]
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

example : V ⊧ₘ empty := by
    unfold empty
    unfold Models
    unfold Semantics.Models
    apply Semiformula.eval_rel₂



lemma subset_def {a b : V} : a ⊆ b ↔ ∀ x ∈ a, x ∈ b := by rfl

end Semiformula
end LO.FirstOrder.SetTheory
