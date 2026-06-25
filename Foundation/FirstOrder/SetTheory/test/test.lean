module

public import Foundation.FirstOrder.SetTheory.Basic
public import Foundation.FirstOrder.Basic.Semantics.Semantics
public import Foundation.FirstOrder.Basic.Syntax.Formula

namespace LO.FirstOrder.SetTheory
namespace Semiformula

variable {V : Type*} [SetStructure V]
variable (a : V)

-- scoped instance : HasSubset V := ⟨fun x y ↦ ∀ z ∈ x, z ∈ y⟩

#check V
#check IsEmpty
#check IsEmpty a
#check “∃ e, ∀ y, y ∉ e”

def empty : Sentence ℒₛₑₜ := “∃ e, ∀ y, y ∉ e”

def infinity : Sentence ℒₛₑₜ := “∃ I, (∀ e, !isEmpty e → e ∈ I) ∧ (∀ x ∈ I, ∀ x', !isSucc x' x → x' ∈ I)”


lemma subset_def {a b : V} : a ⊆ b ↔ ∀ x ∈ a, x ∈ b := by rfl

end Semiformula
end LO.FirstOrder.SetTheory
