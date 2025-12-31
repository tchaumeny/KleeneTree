# Kleene tree: an infinite tree with no computable path

This project formalizes the Kleene tree in [Lean](https://lean-lang.org/), following (not strictly) a paper by Andrej Bauer (see *references*).

The Kleene tree is a (binary) tree which is computable, infinite and does not have a computable (infinite) path.

Kleene tree is a recurring construction in computability theory and reverse mathematics, as it shows the non-computable aspect of the (weak) Kőnig's lemma (see e.g. Stillwell's book).

### Main results

##### Kleene tree is computable

We can algorithmically decide membership of a `Node` in the tree.

```lean
theorem kleene_tree_computable : ComputablePred kleeneTree.nodes
```

##### Kleene tree is infinite

```lean
theorem kleene_tree_infinite : kleeneTree.nodes.Infinite
```

##### Kleene tree does not have a computable path

Any path (e.g., as given by weak Kőnig's lemma) must be non-computable.

```lean
theorem kleene_tree_no_computable_path {p : Path} :
  (∀ n : ℕ, p.get_node n ∈ kleeneTree.nodes) → ¬ Computable p
```

### References

* [Andrej Bauer, *Kőnig's Lemma and Kleene Tree*](https://math.andrej.com/wp-content/uploads/2006/05/kleene-tree.pdf)
* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*](https://arxiv.org/abs/1810.08380)
* [John Stillwell, *Reverse Mathematics: Proofs from the Inside Out*](https://press.princeton.edu/books/paperback/9780691196411/reverse-mathematics)
