/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import OneFactor.Plantholt67
public import Overfull.Theorem12
public import Overfull.ChenCao

/-!
# Overfull criteria: the glue

Restatements of `OneFactor.overfull_criterion67` (PALOMAR-2026-11-04-000016) and of
`Overfull.overfull_of_critical`, `Overfull.overfull_of_critical_cc`,
`Overfull.overfull_of_critical_ccjs` (PALOMAR-2026-11-04-000009), and the elementary step
"an overfull graph has odd order at least 3 and is a `Δ`-overfull subgraph of itself".
-/

@[expose] public section

namespace OverfullCriteria

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- An overfull graph has odd order. -/
theorem odd_card_of_overfull (h : G.maxDegree * (Fintype.card V / 2) < #G.edgeFinset) :
    Odd (Fintype.card V) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hle : ∑ v, G.degree v ≤ ∑ _v : V, G.maxDegree :=
    sum_le_sum fun v _ => G.degree_le_maxDegree v
  rw [sum_const, card_univ, smul_eq_mul] at hle
  obtain ⟨k, hk⟩ := hodd
  rw [hk, show k + k = 2 * k by ring, Nat.mul_div_cancel_left k (by norm_num)] at h
  rw [hk] at hle
  nlinarith

/-- An overfull graph has at least two vertices. -/
theorem two_le_card_of_overfull (h : G.maxDegree * (Fintype.card V / 2) < #G.edgeFinset) :
    2 ≤ Fintype.card V := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < #G.edgeFinset)
  induction e using Sym2.ind with
  | h a b =>
    rw [mem_edgeFinset, mem_edgeSet] at he
    have hab : a ≠ b := G.ne_of_adj he
    have : ({a, b} : Finset V).card = 2 := card_pair hab
    rw [← this]
    exact card_le_univ _

/-- An overfull graph is a `Δ`-overfull subgraph of itself. -/
theorem exists_overfull_subgraph_of_overfull
    (h : G.maxDegree * (Fintype.card V / 2) < #G.edgeFinset) :
    ∃ H : G.Subgraph, Odd H.verts.ncard ∧ 3 ≤ H.verts.ncard ∧
      G.maxDegree * (H.verts.ncard - 1) < 2 * H.edgeSet.ncard := by
  have hodd := odd_card_of_overfull G h
  have h2 := two_le_card_of_overfull G h
  have hv : (⊤ : G.Subgraph).verts.ncard = Fintype.card V := by
    rw [Subgraph.verts_top, Set.ncard_univ, Nat.card_eq_fintype_card]
  have he : (⊤ : G.Subgraph).edgeSet.ncard = #G.edgeFinset := by
    rw [Subgraph.edgeSet_top, ← coe_edgeFinset, Set.ncard_coe_finset]
  refine ⟨⊤, ?_, ?_, ?_⟩
  · rw [hv]; exact hodd
  · rw [hv]; obtain ⟨k, hk⟩ := hodd; omega
  · rw [hv, he]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, show (2 * k + 1) / 2 = k by omega] at h
    rw [hk, show 2 * k + 1 - 1 = 2 * k by omega]
    nlinarith

end OverfullCriteria
