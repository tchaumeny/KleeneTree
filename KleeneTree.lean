import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Kleene tree: an infinite tree with no computable path

This file defines the Kleene tree, a (binary) tree which is computable,
infinite and does not have a computable path, following (not strictly) a
paper of Andrej Bauer (see references).

## Main Definitions

* `Node`: A node in the complete binary tree. It is encoded as a `List Bool`,
          to be read from right to left (this choice makes it easier for inductive constructions).
* `BinaryTree`: The structure representing a (binary) tree, using the suffix relationship
                to represent the asendency relationship.
* `Path`: An (infinite) path through the complete binary tree, encoded as a function `ℕ → Bool`.
          To retrieve the `n`-th `Node` of a  path `p`, we just call `p.get_node n`.
* `kleeneTree`: A particular instance of `BinaryTree`, which is the main construction here.

## Main Results

* `separation_problem`: An impossibility result (similar to the Halting problem),
                        used to construct Kleene tree.
* `kleene_tree_computable`: Kleene tree is computable, meaning that we can algorithmically decide
                            membership of a `Node`.
* `kleene_tree_infinite`: Kleene tree is infinite, which we prove by constructing a particular
                          injection from `ℕ → Node`.
* `kleene_tree_no_computable_path`: Kleene tree does not have a computable `Path`: any path
                                    (e.g., as given by weak Kőnig's lemma) must be non-computable.

## References

* [Andrej Bauer, *Kőnig's Lemma and Kleene Tree*](https://math.andrej.com/wp-content/uploads/2006/05/kleene-tree.pdf)
-/

open List

abbrev Node := List Bool

structure BinaryTree where
  nodes : Set Node
  root_mem : nil ∈ nodes
  suffix_closed :
    ∀ {p q : Node}, q ∈ nodes → IsSuffix p q → p ∈ nodes
  root : nodes := ⟨nil, root_mem⟩

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

open Nat.Partrec

def bounded_separator : ℕ → Node → Bool := fun k node =>
  List.recOn
    node
    true
    fun head tail itail =>
      (Option.casesOn
        (Code.evaln k (Code.ofNatCode tail.length) 0)
        true
        fun v => head = decide (v = 0))
      && itail

lemma bounded_separator_primrec₂ : Primrec₂ bounded_separator :=
  Primrec.list_rec
    Primrec.snd
    (Primrec.const true)
    (Primrec.and.comp₂
      (Primrec.option_casesOn
        (Code.primrec_evaln.comp <|
          Primrec.pair
            (Primrec.pair
              (Primrec.fst.comp Primrec.fst)
              ((Primrec.ofNat Code).comp <| Primrec.list_length.comp <|
                Primrec.fst.comp <| Primrec.snd.comp Primrec.snd)
            )
            (Primrec.const 0)
          )
        (Primrec.const true)
        (Primrec.beq.comp
          (Primrec.fst.comp <| Primrec.snd.comp Primrec.fst)
          (Primrec.eq.decide.comp Primrec.snd (Primrec.const 0))).to₂
      ).to₂
      (Primrec.snd.comp₂ <| Primrec.snd.comp₂ Primrec.snd.to₂)
    )

lemma bounded_separator_mono {k₁ k₂ : ℕ} (node : Node) :
  k₁ ≤ k₂ → bounded_separator k₂ node → bounded_separator k₁ node
:= by induction node with
  | nil => simp [bounded_separator]
  | cons head tail itail =>
    intro hk₁₂ hk₂
    simp only [bounded_separator, Bool.and_eq_true] at itail hk₂ ⊢
    constructor
    · rcases Option.eq_none_or_eq_some (Code.evaln k₁ (Code.ofNatCode tail.length) 0)
      with hnone | ⟨x, hx⟩
      · simp only [hnone]
      · simp only [Eq.trans hx (Option.mem_def.1 (Code.evaln_mono hk₁₂ hx)).symm, hk₂.left]
    · exact itail hk₁₂ hk₂.right

lemma bounded_separator_suffix {node : Node} (t : List Bool) :
  bounded_separator k (t ++ node) → bounded_separator k node
:= by induction t with
  | nil => simp
  | cons head tail itail =>
    intro h
    simp only [bounded_separator, cons_append, length_append, Bool.and_eq_true] at h ⊢ itail
    exact itail h.right

lemma bounded_separator_stable (p : Path) (h : m ≤ n) :
  bounded_separator k (p.get_node n) → bounded_separator k (p.get_node m) := by
  intro hn
  let ⟨t, ht⟩ := Path.get_node_suffix (p := p) m (n - m)
  rw [Nat.add_sub_of_le h] at ht
  rw [congrArg (bounded_separator k) ht] at hn
  exact bounded_separator_suffix t hn

def kleeneTree : BinaryTree where
  nodes := { node | bounded_separator node.length node }
  root_mem := by simp [bounded_separator]
  suffix_closed := by
    intro p q hq hpq
    unfold IsSuffix at hpq
    let ⟨t, ht⟩ := hpq
    simp only [Set.mem_setOf_eq, ← ht] at hq
    exact bounded_separator_mono (k₁ := p.length) (k₂ := (t ++ p).length) p (by simp)
          <| bounded_separator_suffix t hq

lemma ofNatCode_encode {c : Code} : Code.ofNatCode c.encodeCode = c :=
  by simp [← Code.ofNatCode_eq, ← Code.encodeCode_eq, Denumerable.ofNat_encode]

lemma primrec_encodeCode : Primrec Code.encodeCode := by
  rw [← Code.encodeCode_eq]
  exact Primrec.encode_iff.2 Primrec.id

open Classical in
theorem separation_problem :
    ¬∃ sep : Code → Bool, Computable sep ∧
      ∀ c : Code, ((c.eval 0).map (fun v => sep c = (v = 0))).getOrElse true := by
  rintro ⟨sep, ⟨hcomp, hsep⟩⟩
  let ⟨c, e⟩ :=
    Code.fixed_point
      (Computable.cond
        hcomp
        (Computable.const (Code.const 1))
        (Computable.const (Code.const 0))
      )
  by_cases H : sep c
  all_goals
    simp only [H, cond] at e
    have hceval := (congrArg (fun f => f 0) e).symm
    simp [Code.eval_const] at hceval
    let hsepc := hsep c
    rw [hceval] at hsepc
    simp only [Part.map_some, one_ne_zero, decide_false, Part.getOrElse_some] at hsepc
    grind only

theorem kleene_tree_computable : ComputablePred kleeneTree.nodes := by
  simp [kleeneTree]
  have hp : Primrec (fun node => decide (bounded_separator node.length node)) := by
    simp only [Bool.decide_eq_true]
    exact bounded_separator_primrec₂.comp Primrec.list_length Primrec.id
  exact (Primrec.primrecPred hp).computablePred

def bounded_node_builder (k : ℕ) : ℕ → Node
| 0 => nil
| n + 1 =>
    (Option.casesOn
      (Code.evaln k (Code.ofNatCode n) 0)
      true
      fun v => decide (v = 0)) :: bounded_node_builder k n

lemma node_builder_length (n : ℕ) : (bounded_node_builder k n).length = n := by
  induction n with
  | zero => trivial
  | succ n ih => simp [bounded_node_builder, ih]

lemma node_builder_separator (n : ℕ) : bounded_separator k (bounded_node_builder k n) := by
  induction n with
  | zero => simp [bounded_separator, bounded_node_builder]
  | succ n ih =>
    unfold bounded_node_builder bounded_separator
    dsimp [List.recOn]
    unfold bounded_separator at ih
    simp only [Bool.and_eq_true]
    constructor
    · simp only [node_builder_length]
      rcases Option.eq_none_or_eq_some (Code.evaln k (Code.ofNatCode n) 0) with hnone | ⟨x, hx⟩
      · simp only [hnone, true_eq_decide_iff]
      · simp only [hx, decide_eq_decide, Bool.decide_iff_dist, BEq.rfl]
    · exact ih

theorem kleene_tree_infinite : kleeneTree.nodes.Infinite := by
  have hmem : ∀ n, bounded_node_builder n n ∈ kleeneTree.nodes := by
    intro n
    unfold kleeneTree
    simp only [Set.mem_setOf_eq, node_builder_length, node_builder_separator]
  have hinj : Function.Injective fun n => bounded_node_builder n n := by
    unfold Function.Injective
    intro a₁ a₂ heq
    dsimp at heq
    grind only [!node_builder_length]
  exact Set.infinite_of_injective_forall_mem hinj hmem

open Classical in
theorem kleene_tree_no_computable_path {p : Path} :
  (∀ n : ℕ, p.get_node n ∈ kleeneTree.nodes) → ¬ Computable p := by
  intro hpath hpcomp
  unfold kleeneTree at hpath
  simp only [Set.mem_setOf_eq] at hpath
  let sep := fun c : Code => p c.encodeCode
  have hsep : ∀ c : Code, ((c.eval 0).map (fun v => sep c = (v = 0))).getOrElse true := by
    intro c
    rcases Part.eq_none_or_eq_some (c.eval 0) with hnone | ⟨x, hx⟩
    · simp only [hnone, Part.map_none, Part.getOrElse_none]
    · have hxmem : x ∈ c.eval 0 := by simp only [hx, Part.mem_some_iff]
      let ⟨k, hk⟩ := Code.evaln_complete.1 hxmem
      simp only [decide]
      unfold sep
      let hmaxkcsucc := hpath <| max k c.encodeCode.succ
      rw [Path.get_node_length] at hmaxkcsucc
      let hcsucc := bounded_separator_stable p le_sup_right hmaxkcsucc
      simp only [bounded_separator, Nat.succ_eq_add_one, Path.get_node, Path.get_node_length,
        ofNatCode_encode, Bool.and_eq_true] at hcsucc
      let hcsuccl := hcsucc.left
      rw [Code.evaln_mono (k₁ := k) (k₂ := max k c.encodeCode.succ) le_sup_left hk] at hcsuccl
      simpa [hx] using hcsuccl
  exact separation_problem ⟨sep, And.intro (hpcomp.comp primrec_encodeCode.to_comp) hsep⟩
