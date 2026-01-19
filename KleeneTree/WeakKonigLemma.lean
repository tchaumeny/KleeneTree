import KleeneTree.Basic

/-!
## Main Results

* `weak_konig_lemma`: A formalization of weak Kőnig's lemma using the `BinaryTree` structure
-/

open List

lemma suffix_subsets {tree : BinaryTree} (hp : p ∈ tree.nodes) :
    { q ∈ tree.nodes | IsSuffix p q }
    = { p } ∪ { q ∈ tree.nodes | ∃ b : Bool, IsSuffix (b :: p) q } :=
  calc
    _ = { q ∈ tree.nodes | p = q ∨ ∃ b : Bool, IsSuffix (b :: p) q } := by
      rw [Set.sep_ext_iff]
      intro q hq
      constructor
      · intro hpq
        unfold IsSuffix at hpq
        let ⟨t, ht⟩ := hpq
        by_cases H : t = []
        · grind
        · right
          unfold IsSuffix
          use t.getLast H, t.dropLast
          rwa [List.append_cons, dropLast_concat_getLast H]
      · intro hpq
        obtain _ | ⟨b, hb⟩ := hpq
        · grind
        · unfold IsSuffix at hb ⊢
          use hb.choose ++ [b]
          simp [hb.choose_spec]
    _ = _ := by rw [Set.sep_or]; grind

open Classical in
noncomputable def wkl_nodes {tree : BinaryTree} (hinf : tree.nodes.Infinite) :
  ℕ → { p ∈ tree.nodes | { q ∈ tree.nodes | IsSuffix p q }.Infinite }
| 0 => ⟨nil, by simp [hinf, tree.root_mem]⟩
| n + 1 => by
  let previous := wkl_nodes hinf n
  let hinf' := previous.property.right
  rw [suffix_subsets previous.property.left, Set.infinite_union] at hinf'
  have H : ∃ b : Bool, { q ∈ tree.nodes | IsSuffix (b :: wkl_nodes hinf n) q }.Infinite := by
    obtain absurd | h := hinf'
    · exfalso
      exact absurd <| Set.finite_singleton _
    · have h' : ({q ∈ tree.nodes | IsSuffix (false :: previous) q }
                  ∪ { q ∈ tree.nodes | IsSuffix (true :: previous) q}).Infinite := by
        conv_rhs at h => right; simp
        rw [Set.sep_or] at h
        exact h
      obtain hf | ht := Set.infinite_union.1 h'
      · use false
      · use true
  let b := H.choose
  let spec := H.choose_spec
  have hmem : b :: previous ∈ tree.nodes := by
    let spec' := spec.nonempty.choose_spec
    exact tree.suffix_closed spec'.left spec'.right
  exact ⟨b :: previous, ⟨hmem, spec⟩⟩

lemma wkl_nodes_len {tree : BinaryTree} (hinf : tree.nodes.Infinite) :
  (wkl_nodes hinf n).val.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [wkl_nodes, ih]

noncomputable def wkl_path {tree : BinaryTree} (hinf : tree.nodes.Infinite) : Path :=
  fun n ↦ (wkl_nodes _ (n + 1)).val.head (ne_nil_of_length_eq_add_one <| wkl_nodes_len hinf)

lemma wkl_path_node_eq {tree : BinaryTree} (hinf : tree.nodes.Infinite) :
    (wkl_path hinf).get_node n = wkl_nodes hinf n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Path.get_node, ih, wkl_path, wkl_nodes]

theorem weak_konig_lemma {tree : BinaryTree} (hinf : tree.nodes.Infinite) :
    ∃ p : Path, ∀ n : ℕ, p.get_node n ∈ tree.nodes := by
  use wkl_path hinf
  simp [wkl_path_node_eq]
  grind
