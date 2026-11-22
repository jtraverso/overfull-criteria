module

public import OverfullWork.MultigraphExtension

@[expose] public section


/-!
# Edge identifiers for a bipartite multiplicity multigraph

Each edge copy is an ordered left endpoint, right endpoint, and an index
below the corresponding multiplicity. The counting bridge preserves
parallel copies and incidence degrees.
-/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsBipartiteOn (M : MultiGraph V) (L : Finset V) : Prop :=
  ∀ u v, (u ∈ L ↔ v ∈ L) → M.mult s(u,v) = 0

namespace BipartiteCopies

abbrev Left (L : Finset V) := {v : V // v ∈ L}
abbrev Right (L : Finset V) := {v : V // v ∉ L}

abbrev Copies (M : MultiGraph V) (L : Finset V) :=
  Σ a : Left L, Σ b : Right L, Fin (M.mult s(a.1,b.1))

def left {M : MultiGraph V} {L : Finset V} (e : Copies M L) : Left L := e.1
def right {M : MultiGraph V} {L : Finset V} (e : Copies M L) : Right L := e.2.1
def edge {M : MultiGraph V} {L : Finset V} (e : Copies M L) : Sym2 V := s(e.1.1,e.2.1.1)

omit [Fintype V] [DecidableEq V] in
theorem pair_eq_iff (M : MultiGraph V) (L : Finset V) (e : Copies M L)
    (a : Left L) (b : Right L) :
    edge e = s(a.1,b.1) ↔ left e = a ∧ right e = b := by
  rw [edge, Sym2.eq_iff]
  constructor
  · rintro (h | h)
    · exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩
    · exact False.elim (b.2 (h.1 ▸ e.1.2))
  · rintro ⟨ha, hb⟩
    exact Or.inl ⟨congrArg Subtype.val ha, congrArg Subtype.val hb⟩

theorem pair_card (M : MultiGraph V) (L : Finset V) (a : Left L) (b : Right L) :
    (univ.filter (fun e : Copies M L => edge e = s(a.1,b.1))).card = M.mult s(a.1,b.1) := by
  simp_rw [pair_eq_iff]
  rw [card_eq_sum_ones, sum_filter, Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  simp only [left, right]
  rw [sum_eq_single a]
  · rw [sum_eq_single b]
    · simp
    · intro b' hb' hne
      simp [hne]
    · simp
  · intro a' ha' hne
    simp [hne]
  · simp

theorem edge_fibre_card (M : MultiGraph V) (L : Finset V) (hB : M.IsBipartiteOn L)
    (p : Sym2 V) : (univ.filter (fun e : Copies M L => edge e = p)).card = M.mult p := by
  induction p using Sym2.inductionOn with
  | hf u v =>
    by_cases hu : u ∈ L <;> by_cases hv : v ∈ L
    · have hz := hB u v (by simp [hu, hv])
      rw [hz, card_eq_zero]
      apply filter_eq_empty_iff.mpr
      intro e he hp
      rcases Sym2.eq_iff.mp hp with h | h
      · exact e.2.1.2 (h.2.symm ▸ hv)
      · exact e.2.1.2 (h.2.symm ▸ hu)
    · exact pair_card M L ⟨u,hu⟩ ⟨v,hv⟩
    · rw [Sym2.eq_swap]
      exact pair_card M L ⟨v,hv⟩ ⟨u,hu⟩
    · have hz := hB u v (by simp [hu, hv])
      rw [hz, card_eq_zero]
      apply filter_eq_empty_iff.mpr
      intro e he hp
      rcases Sym2.eq_iff.mp hp with h | h
      · exact hu (h.1 ▸ e.1.2)
      · exact hv (h.1 ▸ e.1.2)

theorem left_fibre_card (M : MultiGraph V) (L : Finset V) (a : Left L) :
    (univ.filter (fun e : Copies M L => left e = a)).card =
      ∑ b : Right L, M.mult s(a.1,b.1) := by
  rw [card_eq_sum_ones, sum_filter, Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  simp only [left]
  rw [sum_eq_single a]
  · simp
  · intro a' ha' hne
    simp [hne]
  · simp

theorem right_fibre_card (M : MultiGraph V) (L : Finset V) (b : Right L) :
    (univ.filter (fun e : Copies M L => right e = b)).card =
      ∑ a : Left L, M.mult s(a.1,b.1) := by
  rw [card_eq_sum_ones, sum_filter, Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  simp only [right]
  apply sum_congr rfl
  intro a ha
  rw [sum_eq_single b]
  · simp
  · intro b' hb' hne
    simp [hne]
  · simp

theorem left_fibre_le_degree (M : MultiGraph V) (L : Finset V) (a : Left L) :
    (univ.filter (fun e : Copies M L => left e = a)).card ≤ M.degree a.1 := by
  rw [left_fibre_card, degree_eq_sum_mult,
    ← Finset.sum_subtype Lᶜ (fun _ => mem_compl) (fun v => M.mult s(a.1,v))]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)

theorem right_fibre_le_degree (M : MultiGraph V) (L : Finset V) (b : Right L) :
    (univ.filter (fun e : Copies M L => right e = b)).card ≤ M.degree b.1 := by
  rw [right_fibre_card, degree_eq_sum_mult,
    ← Finset.sum_subtype L (fun _ => Iff.rfl) (fun v => M.mult s(v,b.1))]
  calc
    _ ≤ ∑ v : V, M.mult s(v,b.1) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = _ := by simp only [Sym2.eq_swap]

omit [Fintype V] [DecidableEq V] in
theorem same_side_of_incident (M : MultiGraph V) (L : Finset V)
    {e f : Copies M L} {v : V} (he : v ∈ edge e) (hf : v ∈ edge f) :
    left e = left f ∨ right e = right f := by
  rcases Sym2.mem_iff.mp he with he | he <;> rcases Sym2.mem_iff.mp hf with hf | hf
  · exact Or.inl (Subtype.ext (he.symm.trans hf))
  · exact False.elim (f.2.1.2 (hf ▸ (he.symm ▸ e.1.2)))
  · exact False.elim (e.2.1.2 (he ▸ (hf.symm ▸ f.1.2)))
  · exact Or.inr (Subtype.ext (he.symm.trans hf))

#print axioms edge_fibre_card
#print axioms left_fibre_le_degree

end BipartiteCopies
end SimpleGraph.MultiGraph
