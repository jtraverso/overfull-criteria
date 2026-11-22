module

public import OverfullWork.Multigraph

@[expose] public section


/-!
# Explicit one-point multigraph extension of saturated graphs

Every original edge has multiplicity one. The edge from the new point
to v has multiplicity Delta-degree(v). Saturation makes its degree Delta.
The degree-gap-two hypothesis is needed only for the multiplicity bound.
No density hypothesis or factorization theorem is assumed here.
-/

namespace SimpleGraph.MultiGraph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem degree_eq_sum_mult (M : MultiGraph V) (v : V) :
    M.degree v = ∑ w : V, M.mult s(v,w) := by
  have hfin : univ.filter (fun e : Sym2 V => v ∈ e) =
      univ.image (fun w : V => s(v,w)) := by
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_image]
    exact Sym2.mem_iff_exists.trans (by simp only [eq_comm])
  have hinj : Function.Injective (fun w : V => s(v,w)) := by
    intro a b h
    rcases Sym2.eq_iff.mp h with h | h
    · exact h.2
    · exact h.2.trans h.1
  rw [degree, hfin, Finset.sum_image (fun a _ b _ h => hinj h)]

end SimpleGraph.MultiGraph

namespace OverfullWork.MultigraphExtension

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def pairMultiplicity : Option V → Option V → ℕ
  | none, none => 0
  | none, some v => G.maxDegree - G.degree v
  | some v, none => G.maxDegree - G.degree v
  | some u, some v => if G.Adj u v then 1 else 0

omit [DecidableEq V] in
theorem pairMultiplicity_symm (u v : Option V) :
    pairMultiplicity G u v = pairMultiplicity G v u := by
  cases u <;> cases v <;> simp [pairMultiplicity, G.adj_comm]

omit [DecidableEq V] in
theorem pairMultiplicity_self (u : Option V) : pairMultiplicity G u u = 0 := by
  cases u <;> simp [pairMultiplicity]

def pointExtension : MultiGraph (Option V) where
  mult := Sym2.lift ⟨pairMultiplicity G, pairMultiplicity_symm G⟩
  loopless := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have h := Sym2.mk_isDiag_iff.mp he
      subst v
      exact pairMultiplicity_self G u

omit [DecidableEq V] in
@[simp] theorem mult_mk (u v : Option V) :
    (pointExtension G).mult s(u,v) = pairMultiplicity G u v := rfl

omit [DecidableEq V] in
theorem preserves_original (u v : V) :
    (pointExtension G).mult s(some u, some v) = if G.Adj u v then 1 else 0 := rfl

omit [DecidableEq V] in
theorem contains_original (u v : V) (huv : G.Adj u v) :
    1 ≤ (pointExtension G).mult s(some u, some v) := by
  rw [preserves_original, if_pos huv]

theorem degree_none :
    (pointExtension G).degree none = ∑ v : V, (G.maxDegree - G.degree v) := by
  rw [MultiGraph.degree_eq_sum_mult]
  simp [pairMultiplicity]

theorem degree_some (v : V) : (pointExtension G).degree (some v) = G.maxDegree := by
  have hsum : (∑ w : V, if G.Adj v w then 1 else 0) = G.degree v := by
    have hfin : univ.filter (G.Adj v) = G.neighborFinset v := by
      ext w
      simp
    simpa using congrArg Finset.card hfin
  rw [MultiGraph.degree_eq_sum_mult]
  simp only [mult_mk, Fintype.sum_option, pairMultiplicity]
  rw [hsum]
  have h := G.degree_le_maxDegree v
  omega

omit [DecidableEq V] in
theorem total_deficit_identity :
    (∑ v : V, G.degree v) + (∑ v : V, (G.maxDegree - G.degree v)) =
      Fintype.card V * G.maxDegree := by
  rw [← sum_add_distrib]
  have hsum : ∀ v : V, G.degree v + (G.maxDegree - G.degree v) = G.maxDegree :=
    fun v => Nat.add_sub_of_le (G.degree_le_maxDegree v)
  simp_rw [hsum]
  simp

theorem regular_of_saturated (hn : 1 ≤ Fintype.card V)
    (hsat : 2 * G.edgeFinset.card = G.maxDegree * (Fintype.card V - 1)) :
    (pointExtension G).IsRegularOfDegree G.maxDegree := by
  have htotal := total_deficit_identity G
  rw [G.sum_degrees_eq_twice_card_edges, hsat] at htotal
  have hsplit : G.maxDegree * (Fintype.card V - 1) + G.maxDegree =
      Fintype.card V * G.maxDegree := by
    calc
      _ = G.maxDegree * (Fintype.card V - 1 + 1) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hn, Nat.mul_comm]
  intro v
  cases v with
  | none => rw [degree_none]; omega
  | some v => exact degree_some G v

omit [DecidableEq V] in
theorem multiplicity_le_two (hgap : G.maxDegree - G.minDegree ≤ 2)
    (e : Sym2 (Option V)) : (pointExtension G).mult e ≤ 2 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [mult_mk]
    cases u with
    | none =>
      cases v with
      | none => simp [pairMultiplicity]
      | some v =>
        have h := G.minDegree_le_degree v
        dsimp only [pairMultiplicity]
        omega
    | some u =>
      cases v with
      | none =>
        have h := G.minDegree_le_degree u
        dsimp only [pairMultiplicity]
        omega
      | some v => simp [pairMultiplicity]; split_ifs <;> omega

theorem exists_multigraphExtension (hn : 1 ≤ Fintype.card V)
    (hgap : G.maxDegree - G.minDegree ≤ 2)
    (hsat : 2 * G.edgeFinset.card = G.maxDegree * (Fintype.card V - 1)) :
    MultiGraph.HasMultigraphExtension G := by
  exact ⟨pointExtension G, regular_of_saturated G hn hsat,
    multiplicity_le_two G hgap, contains_original G⟩

theorem regular_iff_saturated (hn : 1 ≤ Fintype.card V) :
    (pointExtension G).IsRegularOfDegree G.maxDegree ↔
      2 * G.edgeFinset.card = G.maxDegree * (Fintype.card V - 1) := by
  refine ⟨fun hreg => ?_, regular_of_saturated G hn⟩
  have hnone := hreg none
  rw [degree_none] at hnone
  have htotal := total_deficit_identity G
  rw [G.sum_degrees_eq_twice_card_edges, hnone] at htotal
  have hsplit : G.maxDegree * (Fintype.card V - 1) + G.maxDegree =
      Fintype.card V * G.maxDegree := by
    calc
      _ = G.maxDegree * (Fintype.card V - 1 + 1) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hn, Nat.mul_comm]
  omega

theorem edge_count_extension : (pointExtension G).edgeCount =
    G.edgeFinset.card + ∑ v : V, (G.maxDegree - G.degree v) := by
  have hsum := (pointExtension G).sum_degrees_eq_twice_edgeCount
  rw [Fintype.sum_option, degree_none] at hsum
  simp_rw [degree_some] at hsum
  simp only [sum_const, card_univ, smul_eq_mul] at hsum
  have htotal := total_deficit_identity G
  rw [G.sum_degrees_eq_twice_card_edges] at htotal
  omega

omit [DecidableEq V] in
theorem even_order (hn : Odd (Fintype.card V)) : Even (Fintype.card (Option V)) := by
  obtain ⟨m, hm⟩ := hn
  simp only [Fintype.card_option]
  exact ⟨m + 1, by omega⟩

#print axioms regular_of_saturated
#print axioms multiplicity_le_two
#print axioms exists_multigraphExtension

end OverfullWork.MultigraphExtension
