module

public import OverfullWork.BipartiteFactorization
public import ShannonColouring.Defs

@[expose] public section


/-! # Exact edge-copy bridge for arbitrary loopless multiplicity multigraphs -/

namespace SimpleGraph.MultiGraph.GeneralCopies

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Copies (M : MultiGraph V) := Σ e : Sym2 V, Fin (M.mult e)

omit [Fintype V] [DecidableEq V] in
theorem exists_endpoints (e : Sym2 V) : ∃ p : V × V, s(p.1,p.2) = e := by
  induction e using Sym2.inductionOn with
  | hf u v => exact ⟨(u,v),rfl⟩

noncomputable def endpoints (e : Sym2 V) : V × V := Classical.choose (exists_endpoints e)

omit [Fintype V] [DecidableEq V] in
theorem endpoints_eq (e : Sym2 V) : s((endpoints e).1,(endpoints e).2) = e :=
  Classical.choose_spec (exists_endpoints e)

noncomputable def ends (M : MultiGraph V) (c : Copies M) : V × V := endpoints c.1

omit [Fintype V] [DecidableEq V] in
theorem incident_iff (M : MultiGraph V) (c : Copies M) (v : V) :
    ShannonColouring.Incident (ends M) c v ↔ v ∈ c.1 := by
  rw [← endpoints_eq c.1]
  simp only [ShannonColouring.Incident, ends, Sym2.mem_iff, eq_comm]

omit [Fintype V] [DecidableEq V] in
theorem loopless (M : MultiGraph V) (c : Copies M) : (ends M c).1 ≠ (ends M c).2 := by
  intro h
  have hd : c.1.IsDiag := by rw [← endpoints_eq c.1]; simpa [ends] using h
  have h0 := M.loopless c.1 hd
  have hlt := c.2.isLt
  omega

theorem edge_fibre_card (M : MultiGraph V) (p : Sym2 V) :
    (univ.filter (fun c : Copies M => c.1 = p)).card = M.mult p := by
  rw [card_eq_sum_ones, sum_filter, Fintype.sum_sigma]
  rw [sum_eq_single p]
  · simp
  · intro q _ hq
    simp [hq]
  · simp

theorem degree_eq (M : MultiGraph V) (v : V) :
    ShannonColouring.degree (ends M) v = M.degree v := by
  unfold ShannonColouring.degree
  have hi : ∀ c : Copies M, ((ends M c).1 = v ∨ (ends M c).2 = v) ↔ v ∈ c.1 :=
    fun c => incident_iff M c v
  simp_rw [hi]
  rw [card_eq_sum_ones, sum_filter, Fintype.sum_sigma, M.degree_eq_sum_ite]
  apply sum_congr rfl
  intro p _
  by_cases h : v ∈ p <;> simp [h]

noncomputable def colouredCopies (M : MultiGraph V) {k : ℕ}
    (c : Copies M → Fin k) (p : Sym2 V) (i : Fin k) : ℕ :=
  ((univ.filter (fun e => c e = i)).filter (fun e => e.1 = p)).card

theorem colouredCopies_sum (M : MultiGraph V) {k : ℕ} (c : Copies M → Fin k) (p : Sym2 V) :
    (∑ i, colouredCopies M c p i) = M.mult p := by
  have hf : ∀ i, colouredCopies M c p i =
      ((univ.filter (fun e : Copies M => e.1 = p)).filter (fun e => c e = i)).card := by
    intro i
    unfold colouredCopies
    congr 1
    ext e
    simp [and_comm]
  simp_rw [hf]
  rw [sum_card_fiberwise_eq_card_filter]
  simp only [mem_univ, filter_true]
  exact edge_fibre_card M p

theorem colouredCopies_proper (M : MultiGraph V) {k : ℕ} (c : Copies M → Fin k)
    (hc : ShannonColouring.IsProperEdgeColouring (ends M) c) (v : V) (i : Fin k) :
    (∑ p ∈ univ.filter (fun p : Sym2 V => v ∈ p), colouredCopies M c p i) ≤ 1 := by
  unfold colouredCopies
  rw [sum_card_fiberwise_eq_card_filter]
  apply card_le_one.mpr
  intro e he f hf
  simp only [mem_filter,mem_univ,true_and] at he hf
  by_contra hne
  exact hc e f hne ⟨v,(incident_iff M e v).mpr he.2,
    (incident_iff M f v).mpr hf.2⟩ (he.1.trans hf.1.symm)

noncomputable def edgeColoring (M : MultiGraph V) {k : ℕ} (c : Copies M → Fin k)
    (hc : ShannonColouring.IsProperEdgeColouring (ends M) c) : M.EdgeColoring k where
  col := colouredCopies M c
  sum_col := colouredCopies_sum M c
  proper := colouredCopies_proper M c hc

end SimpleGraph.MultiGraph.GeneralCopies
