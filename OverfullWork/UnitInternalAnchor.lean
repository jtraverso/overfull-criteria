module

public import OverfullWork.ResidueOccupiedVertexBudget

@[expose] public section


/-! Elementary finite obstructions for the Stage I first anchor in CMS Step 4. -/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

theorem single_edge_positive_pair (M : MultiGraph V) (hOne : M.edgeCount=1)
    (b w : V) (hbw : b ≠ w) (hb : 0 < M.degree b) (hw : 0 < M.degree w) :
    0 < M.mult s(b,w) := by
  rw [degree_eq_sum_mult] at hb hw
  obtain ⟨x,_,hx⟩ := sum_pos_iff.mp hb
  obtain ⟨y,_,hy⟩ := sum_pos_iff.mp hw
  have hUnique : s(b,x)=s(w,y) := by
    by_contra hNe
    have hSum := sum_le_sum_of_subset_of_nonneg
      (show ({s(b,x),s(w,y)} : Finset (Sym2 V)) ⊆ univ from subset_univ _)
      (f := M.mult) (fun _ _ _ => Nat.zero_le _)
    rw [sum_insert (by simpa using hNe),sum_singleton] at hSum
    change M.mult s(b,x)+M.mult s(w,y) ≤ M.edgeCount at hSum
    omega
  rcases Sym2.eq_iff.mp hUnique with hh|hh
  · exact (hbw hh.1).elim
  · simpa only [hh.2] using hx

namespace EdgeColoring

theorem internal_restrict_compl_degree {M : MultiGraph V} {A : Finset V} {k : ℕ}
    (C : (M.internalPart A).EdgeColoring k) (i : Fin k) (v : V) (hv : v ∈ Aᶜ) :
    ((C.colourGraph i).restrict Aᶜ).degree v=(C.colourGraph i).degree v := by
  rw [degree_restrict,if_pos hv,degree_eq_sum_mult]
  apply sum_subset (subset_univ _)
  intro u _ hu
  have hLe := C.col_le_mult s(v,u) i
  rw [internalPart_mult,if_neg (by
    intro hh
    exact (mem_compl.mp hv) (hh.mpr (by simpa using hu)))] at hLe
  exact Nat.eq_zero_of_le_zero hLe

theorem unit_internal_pair_has_missing {M : MultiGraph V} {A : Finset V} {k : ℕ}
    (C : (M.internalPart A).EdgeColoring k) (i : Fin k) (b w : V)
    (hb : b ∈ Aᶜ) (hw : w ∈ Aᶜ) (hbw : b ≠ w)
    (hOne : (C.colourGraph i).edgesWithin Aᶜ=1)
    (hZero : M.mult s(b,w)=0) :
    b ∈ C.missingSet Aᶜ i ∨ w ∈ C.missingSet Aᶜ i := by
  by_contra! hMissing
  have hbPos : 0 < (C.colourGraph i).degree b := by
    have hh : ¬(C.colourGraph i).degree b=0 := by
      intro hz;exact hMissing.1 (mem_filter.mpr ⟨hb,hz⟩)
    omega
  have hwPos : 0 < (C.colourGraph i).degree w := by
    have hh : ¬(C.colourGraph i).degree w=0 := by
      intro hz;exact hMissing.2 (mem_filter.mpr ⟨hw,hz⟩)
    omega
  have hPair := single_edge_positive_pair ((C.colourGraph i).restrict Aᶜ) hOne b w hbw
    (by rwa [C.internal_restrict_compl_degree i b hb])
    (by rwa [C.internal_restrict_compl_degree i w hw])
  change 0 < (if s(b,w).toFinset ⊆ Aᶜ then C.col s(b,w) i else 0) at hPair
  have hLe := C.col_le_mult s(b,w) i
  have hLeM := internalPart_le M A s(b,w)
  rw [hZero] at hLeM
  split_ifs at hPair <;> omega

end EdgeColoring
end SimpleGraph.MultiGraph
