module

public import Foundation.FirstOrder.SetTheory.Basic.Axioms

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V]

scoped instance : HasSubset V := ⟨fun x y ↦ ∀ z ∈ x, z ∈ y⟩

#check V
#check ∀ (a b : V), a ⊆ b

lemma subset_def {a b : V} : a ⊆ b ↔ ∀ x ∈ a, x ∈ b := by rfl

end LO.FirstOrder.SetTheory
