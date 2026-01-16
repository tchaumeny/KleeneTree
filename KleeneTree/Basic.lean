import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Set.Finite.Lemmas

/-!
## Main Definitions

* `Node`: A node in the complete binary tree. It is encoded as a `List Bool`,
          to be read from right to left (this choice makes it easier for inductive constructions).
* `BinaryTree`: The structure representing a (binary) tree, using the suffix relationship
                to represent the asendency relationship.
* `Path`: An (infinite) path through the complete binary tree, encoded as a function `ℕ → Bool`.
          To retrieve the `n`-th `Node` of a  path `p`, we just call `p.get_node n`.
-/

open List

abbrev Node := List Bool

structure BinaryTree where
  nodes : Set Node
  root_mem : nil ∈ nodes
  suffix_closed :
    ∀ {p q : Node}, q ∈ nodes → IsSuffix p q → p ∈ nodes

abbrev Path := ℕ → Bool

namespace Path

def get_node (p : Path) : ℕ → Node
| 0 => nil
| n + 1 => p n :: p.get_node n

lemma get_node_length {p : Path} : (p.get_node n).length = n := by
  induction n with
  | zero => simp only [get_node, length_nil]
  | succ n ih => simp only [get_node, length_cons, ih]

lemma get_node_suffix {p : Path} (n m : ℕ) : ∃ t, p.get_node (n + m) = t ++ p.get_node n := by
  induction m with
  | zero => simp
  | succ m ih =>
    let ⟨t, ht⟩ := ih
    rw [← Nat.add_assoc]
    nth_rewrite 1 [get_node]
    rw [ht]
    use p (n + m) :: t
    rw [cons_append]

end Path
