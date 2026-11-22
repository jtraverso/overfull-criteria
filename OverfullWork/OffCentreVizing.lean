module

public import OverfullWork.CopyMultifanCounting
public import OverfullWork.DeletedCopyKempeState

@[expose] public section


/-! # CMS Lemma 3.10: Vizing with multiplicity away from one centre

All branches are proved. The minimal uncolorable subgraph supplies a
bounded row; its actual one-copy-deleted state is extended by a maximal
labelled-copy multifan, contradicting criticality.
-/
namespace SimpleGraph.MultiGraph
open Finset ShannonColouring
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 12000000

theorem exists_edgeColoring_off_centre_bound (M : MultiGraph V) (a : V) (d μ : ℕ)
    (hdeg : ∀ v, M.degree v ≤ d)
    (hoff : ∀ u v, u ≠ a → v ≠ a → M.mult s(u,v) ≤ μ) :
    Nonempty (M.EdgeColoring (d+μ)) := by
  by_contra hNo
  obtain ⟨N,hNM,hcrit,hNdeg,u,v,hua,huv,hpos,hsmall,hrow,_⟩ :=
    M.exists_bounded_row_critical_witness a d μ hdeg hoff hNo
  have hμ : 0 < μ := by omega
  obtain ⟨c,hc,_,_⟩ := hcrit.exists_deleted_kempe_state d μ hNdeg hμ u v hpos
  have hdegs : ∀ z, ShannonColouring.degree (N.freshEnds u v) z ≤ d := by
    intro z
    rw [N.freshEnds_degree u v hpos z]
    exact hNdeg z
  have hRows : ∀ z, (univ.filter (fun h =>
      OverfullWork.CopyMultifan.Joins (N.freshEnds u v) h u z)).card ≤ μ := by
    intro z
    have hh : (univ.filter (fun h : N.FreshCopies u v =>
        OverfullWork.CopyMultifan.Joins (N.freshEnds u v) h u z)).card = N.mult s(u,z) := by
      calc
        _ = (univ.filter (fun h : N.FreshCopies u v =>
          s((N.freshEnds u v h).1,(N.freshEnds u v h).2)=s(u,z))).card := by
          congr 1
          ext h
          simp only [mem_filter,mem_univ,true_and]
          exact Iff.rfl
        _ = _ := N.freshEnds_fibre u v hpos s(u,z)
    exact hh.le.trans (hrow z)
  obtain ⟨c',hc'⟩ := OverfullWork.CopyMultifan.bounded_row_extension
    (N.freshEnds_loopless u v huv) hdegs hRows (notMem_erase none univ)
    (by exact Or.inl rfl : Incident (N.freshEnds u v) none u) c hc
  have hs : insert (none : N.FreshCopies u v) (univ.erase none) = univ := insert_erase (mem_univ _)
  rw [hs] at hc'
  exact hcrit.not_fresh_colourable u v hpos ⟨c',fun i j hij hInc =>
    hc' i (mem_univ _) j (mem_univ _) hij hInc⟩

end SimpleGraph.MultiGraph
