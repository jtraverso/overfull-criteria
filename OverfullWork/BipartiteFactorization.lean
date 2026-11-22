module

public import OverfullWork.BipartiteCopies
public import GalvinMultigraph.Local.Konig

@[expose] public section


/-!
# Kőnig colouring and factorization in the multiplicity model

The endpoint implementation is reused from the author's galvin-dinitz
project. This bridge counts copies explicitly and transports its result
to SimpleGraph.MultiGraph.EdgeColoring.
-/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical
open BipartiteCopies

set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def colouringFromCopies (M : MultiGraph V) (L : Finset V) {D : ℕ}
    (c : Copies M L → Fin D) (p : Sym2 V) (i : Fin D) : ℕ :=
  ((univ.filter (fun e : Copies M L => c e = i)).filter (fun e => BipartiteCopies.edge e = p)).card

theorem colouringFromCopies_sum (M : MultiGraph V) (L : Finset V)
    (hB : M.IsBipartiteOn L) {D : ℕ} (c : Copies M L → Fin D) (p : Sym2 V) :
    (∑ i : Fin D, colouringFromCopies M L c p i) = M.mult p := by
  have hf : ∀ i : Fin D, colouringFromCopies M L c p i =
      ((univ.filter (fun e : Copies M L => BipartiteCopies.edge e = p)).filter (fun e => c e = i)).card := by
    intro i
    unfold colouringFromCopies
    apply congrArg Finset.card
    ext e
    simp [and_comm]
  simp_rw [hf]
  rw [sum_card_fiberwise_eq_card_filter]
  simp only [mem_univ, filter_true]
  exact edge_fibre_card M L hB p

theorem colouringFromCopies_proper (M : MultiGraph V) (L : Finset V)
    {D : ℕ} (c : Copies M L → Fin D)
    (hc : ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → c e ≠ c f)
    (v : V) (i : Fin D) :
    (∑ p ∈ univ.filter (fun p : Sym2 V => v ∈ p), colouringFromCopies M L c p i) ≤ 1 := by
  unfold colouringFromCopies
  rw [sum_card_fiberwise_eq_card_filter]
  apply card_le_one.mpr
  intro e he f hf
  simp only [mem_filter, mem_univ, true_and] at he hf
  by_contra hne
  have hve : v ∈ BipartiteCopies.edge e := he.2
  have hvf : v ∈ BipartiteCopies.edge f := hf.2
  exact hc e f hne (same_side_of_incident M L hve hvf) (he.1.trans hf.1.symm)

/-- Kőnig's theorem for the project's weighted loopless multigraph model. -/
theorem exists_edgeColoring_of_bipartite (M : MultiGraph V) (L : Finset V) (D : ℕ)
    (hB : M.IsBipartiteOn L) (hdeg : ∀ v, M.degree v ≤ D) : Nonempty (M.EdgeColoring D) := by
  classical
  have hL : ∀ a : Left L, GalvinMultigraph.Local.degLOn
      (left : Copies M L → Left L) univ a ≤ D := by
    intro a
    exact (left_fibre_le_degree M L a).trans (hdeg a.1)
  have hR : ∀ b : Right L, GalvinMultigraph.Local.degROn
      (right : Copies M L → Right L) univ b ≤ D := by
    intro b
    exact (right_fibre_le_degree M L b).trans (hdeg b.1)
  obtain ⟨phi, hlt, hproper⟩ := GalvinMultigraph.Local.konig_multigraph
    (left : Copies M L → Left L) (right : Copies M L → Right L) univ D hL hR
  let c : Copies M L → Fin D := fun e => ⟨phi e, hlt e (mem_univ e)⟩
  have hc : ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → c e ≠ c f := by
    intro e f hne hadj heq
    exact hproper e (mem_univ e) f (mem_univ f) hne hadj (congrArg Fin.val heq)
  exact ⟨{
    col := colouringFromCopies M L c
    sum_col := colouringFromCopies_sum M L hB c
    proper := colouringFromCopies_proper M L c hc }⟩

def EdgeColoring.IsFactorization {M : MultiGraph V} {D : ℕ} (C : M.EdgeColoring D) : Prop :=
  ∀ (v : V) (i : Fin D), ∑ e ∈ univ.filter (fun e : Sym2 V => v ∈ e), C.col e i = 1

theorem EdgeColoring.isFactorization_of_regular {M : MultiGraph V} {D : ℕ}
    (C : M.EdgeColoring D) (hreg : M.IsRegularOfDegree D) : C.IsFactorization := by
  intro v i
  have hs : (∑ j : Fin D, ∑ e ∈ univ.filter (fun e : Sym2 V => v ∈ e), C.col e j) = D := by
    rw [sum_comm]
    simp_rw [C.sum_col]
    exact hreg v
  have hr : (∑ j ∈ (univ : Finset (Fin D)).erase i,
      ∑ e ∈ univ.filter (fun e : Sym2 V => v ∈ e), C.col e j) ≤ D - 1 := by
    calc
      _ ≤ ∑ _j ∈ (univ : Finset (Fin D)).erase i, 1 := sum_le_sum (fun j _ => C.proper v j)
      _ = _ := by simp
  rw [← sum_erase_add _ _ (mem_univ i)] at hs
  have hi := C.proper v i
  have hD : 0 < D := by have h := i.isLt; omega
  omega

/-- A regular bipartite multigraph decomposes into D perfect matchings,
with all parallel copies included. This conclusion has no factorization premise. -/
theorem exists_factorization_of_bipartite (M : MultiGraph V) (L : Finset V) (D : ℕ)
    (hB : M.IsBipartiteOn L) (hreg : M.IsRegularOfDegree D) :
    ∃ C : M.EdgeColoring D, C.IsFactorization := by
  obtain ⟨C⟩ := exists_edgeColoring_of_bipartite M L D hB (fun v => (hreg v).le)
  exact ⟨C, C.isFactorization_of_regular hreg⟩

#print axioms exists_edgeColoring_of_bipartite
#print axioms exists_factorization_of_bipartite

end SimpleGraph.MultiGraph
