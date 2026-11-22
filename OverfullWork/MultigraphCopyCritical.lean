module

public import OverfullWork.ActiveSaturatedCentreColouring

@[expose] public section


/-! # Minimal uncolourable copy subgraphs and a genuine bounded-row root

Minimality is by the actual number of edge copies with a fixed palette.
Every one-copy deletion has a coloring. The active saturated-centre
construction forces a nonisolated ordinary root with bounded row.
This does not assert the missing multigraph multifan extension.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

def eraseOne (M : MultiGraph V) (e : Sym2 V) : MultiGraph V where
  mult t := if t=e then M.mult t-1 else M.mult t
  loopless t ht := by rw [M.loopless t ht];simp

theorem eraseOne_le (M : MultiGraph V) (e t : Sym2 V) :
    (M.eraseOne e).mult t ≤ M.mult t := by
  dsimp only [eraseOne]
  split_ifs <;> omega

theorem eraseOne_count (M : MultiGraph V) (e : Sym2 V) (he : 0 < M.mult e) :
    (M.eraseOne e).edgeCount+1 = M.edgeCount := by
  have hm := sum_erase_add univ M.mult (mem_univ e)
  have hn := sum_erase_add univ (M.eraseOne e).mult (mem_univ e)
  have hs : (∑ t ∈ univ.erase e, (M.eraseOne e).mult t) = ∑ t ∈ univ.erase e, M.mult t := by
    apply sum_congr rfl
    intro t ht
    exact if_neg (mem_erase.mp ht).1
  rw [hs] at hn
  have hself : (M.eraseOne e).mult e = M.mult e-1 := if_pos rfl
  rw [hself] at hn
  change (∑ t ∈ univ.erase e, M.mult t)+(M.mult e-1) = (M.eraseOne e).edgeCount at hn
  change (∑ t ∈ univ.erase e, M.mult t)+M.mult e = M.edgeCount at hm
  omega

theorem degree_le_of_mult_le (M N : MultiGraph V) (h : ∀ e, N.mult e ≤ M.mult e) (v : V) :
    N.degree v ≤ M.degree v := by
  exact sum_le_sum (fun e _ => h e)

structure IsCopyCritical (M : MultiGraph V) (k : ℕ) : Prop where
  uncolourable : ¬Nonempty (M.EdgeColoring k)
  deletion_colourable : ∀ e, 0 < M.mult e → Nonempty ((M.eraseOne e).EdgeColoring k)

theorem exists_copy_critical (M : MultiGraph V) (k : ℕ) (hNo : ¬Nonempty (M.EdgeColoring k)) :
    ∃ N : MultiGraph V, (∀ e, N.mult e ≤ M.mult e) ∧ N.IsCopyCritical k := by
  let P : ℕ → Prop := fun t => ∃ N : MultiGraph V,
    (∀ e, N.mult e ≤ M.mult e) ∧ N.edgeCount=t ∧ ¬Nonempty (N.EdgeColoring k)
  have hExists : ∃ t, P t := ⟨M.edgeCount,M,fun _ => le_rfl,rfl,hNo⟩
  obtain ⟨N,hNM,hsize,hNNo⟩ := Nat.find_spec hExists
  refine ⟨N,hNM,hNNo,?_⟩
  intro e he
  by_contra hNoDelete
  have hCount := N.eraseOne_count e he
  have hlt : (N.eraseOne e).edgeCount < Nat.find hExists := by omega
  exact Nat.find_min hExists hlt ⟨N.eraseOne e,fun t => (N.eraseOne_le e t).trans (hNM t),rfl,hNoDelete⟩

theorem exists_bounded_row_critical_witness (M : MultiGraph V) (a : V) (d μ : ℕ)
    (hdeg : ∀ v, M.degree v ≤ d)
    (hoff : ∀ u v, u ≠ a → v ≠ a → M.mult s(u,v) ≤ μ)
    (hNo : ¬Nonempty (M.EdgeColoring (d+μ))) :
    ∃ N : MultiGraph V, (∀ e, N.mult e ≤ M.mult e) ∧ N.IsCopyCritical (d+μ) ∧
      (∀ v, N.degree v ≤ d) ∧ ∃ u v,
        u ≠ a ∧ u ≠ v ∧ 0 < N.mult s(u,v) ∧ N.mult s(a,u) < μ ∧
        (∀ w, N.mult s(u,w) ≤ μ) ∧ Nonempty ((N.eraseOne s(u,v)).EdgeColoring (d+μ)) := by
  obtain ⟨N,hNM,hcrit⟩ := M.exists_copy_critical (d+μ) hNo
  have hNdeg : ∀ v, N.degree v ≤ d := fun v => (M.degree_le_of_mult_le N hNM v).trans (hdeg v)
  obtain ⟨u,hua,hpos,hsmall,hrow⟩ := N.exists_bounded_row_of_not_colourable a d μ
    (fun v w hv hw => (hNM _).trans (hoff v w hv hw)) (hNdeg a) hcrit.uncolourable
  have hex : ∃ v, 0 < N.mult s(u,v) := by
    by_contra! h
    have hz : N.degree u = 0 := by rw [degree_eq_sum_mult];exact sum_eq_zero (fun v _ => Nat.eq_zero_of_le_zero (h v))
    omega
  obtain ⟨v,huv⟩ := hex
  have hne : u ≠ v := by
    intro he
    subst v
    have hz := N.loopless s(u,u) (by simp)
    omega
  exact ⟨N,hNM,hcrit,hNdeg,u,v,hua,hne,huv,hsmall,hrow,hcrit.deletion_colourable _ huv⟩

end SimpleGraph.MultiGraph
