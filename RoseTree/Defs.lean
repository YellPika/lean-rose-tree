import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

universe u
variable {A B C : Type*}

/-- The type of node-labelled, finitely branching trees. -/
structure Rose (A : Type u) : Type u where
  /-- The label of the root node. -/
  label : A

  /-- The list of child trees. -/
  children : List (Rose A)

namespace Rose

/-- The fold operation over trees. -/
@[simp]
def fold (f : A → List B → B) : Rose A → B
  | ⟨x, xs⟩ => f x (xs.map (fold f))

/-- Grafts a tree to every sub-node in a `Rose` tree. -/
@[simp]
def bind (f : A → Rose B) : Rose A → Rose B := fun
  | ⟨x, xs⟩ => ⟨(f x).label, (f x).children ++ List.map (bind f) xs⟩

instance : Monad Rose where
  pure x := ⟨x, []⟩
  bind := flip bind

end Rose
