module

public import OverfullWork.DenseClosure

@[expose] public section


/-! Adapted from jtraverso/menger-hamiltonian, MengerHamilton/Hamiltonian.lean.
Original retrieved snapshot SHA-256:
e501790716a0dfb7c0a69a3ccba278e5e4c0ea7ead0933ce763486f84a4dc67b.
Immutable upstream Git blob: 58eed24251623163e13396baa6fc9022bf4a7487.
Ore and Dirac only.
Copyright (c) 2026 Juan Pablo Traverso Gianini, Apache 2.0. -/

namespace OverfullWork.DenseHamilton
open SimpleGraph
variable {V : Type*}

/-- **Bondy–Chvátal (1976).** Adding an edge between two non-adjacent vertices whose degrees sum
to at least `n` does not change whether the graph is Hamiltonian. -/
theorem isHamiltonian_sup_edge_iff [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v : V} (huv : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hdeg : Fintype.card V ≤ G.degree u + G.degree v) :
    (G ⊔ edge u v).IsHamiltonian ↔ G.IsHamiltonian := by
  exact ⟨isHamiltonian_of_sup_edge G huv hnadj hdeg, fun h => h.mono le_sup_left⟩

/-- **Ore's theorem (1960).** A graph on `n ≥ 3` vertices in which any two distinct non-adjacent
vertices have degree sum at least `n` is Hamiltonian. -/
theorem ore [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hdeg : ∀ u v, u ≠ v → ¬ G.Adj u v → Fintype.card V ≤ G.degree u + G.degree v) :
    G.IsHamiltonian := by
  suffices key : ∀ N (H : SimpleGraph V) [DecidableRel H.Adj],
      (Finset.univ.filter (fun p : V × V => p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2)).card = N →
      (∀ u v, u ≠ v → ¬ H.Adj u v → Fintype.card V ≤ H.degree u + H.degree v) →
      H.IsHamiltonian from key _ G rfl hdeg
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro H _ hN hH
  by_cases hall : ∀ u v, u ≠ v → H.Adj u v
  · exact isHamiltonian_of_forall_adj hn hall
  push Not at hall
  obtain ⟨u, v, huv, hnadj⟩ := hall
  classical
  have hle : H ≤ H ⊔ edge u v := le_sup_left
  rw [← isHamiltonian_sup_edge_iff H huv hnadj (hH u v huv hnadj)]
  refine ih _ ?_ (H ⊔ edge u v) rfl ?_
  · rw [← hN]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(u, v), ?_, ?_⟩
      · simp [huv, hnadj]
      · simp [huv, edge_adj]
    · intro p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 (hle h)⟩
  · intro a b hab hnab
    have := hH a b hab (fun h => hnab (hle h))
    exact this.trans (add_le_add (degree_le_of_le hle) (degree_le_of_le hle))

/-- **Dirac's theorem (1952).** A graph on `n ≥ 3` vertices with minimum degree at least `n / 2`
is Hamiltonian. -/
theorem dirac [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hdeg : Fintype.card V ≤ 2 * G.minDegree) : G.IsHamiltonian := by
  refine ore G hn fun u v _ _ => hdeg.trans ?_
  have := G.minDegree_le_degree u
  have := G.minDegree_le_degree v
  omega


end OverfullWork.DenseHamilton

