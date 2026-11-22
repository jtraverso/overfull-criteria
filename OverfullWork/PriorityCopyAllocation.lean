module

public import OverfullWork.InternalEdges

@[expose] public section


/-! # Allocate actual copies with a prescribed priority class

Fill the priority class up to its total capacity before using any copy
outside it. Both finite allocations are constructed from the existing
bounded-allocation theorem, including zero capacities and empty classes.
-/
namespace OverfullWork.PriorityCopyAllocation
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

theorem exists_allocation (c : V → ℕ) (H : Finset V) (q : ℕ)
    (hq : q ≤ ∑ v, c v) :
    ∃ f : V → ℕ, (∀ v, f v ≤ c v) ∧ (∑ v, f v) = q ∧
      (∑ v ∈ H, f v) = min q (∑ v ∈ H, c v) := by
  let cH : V → ℕ := fun v => if v ∈ H then c v else 0
  let cR : V → ℕ := fun v => if v ∈ H then 0 else c v
  let qH := min q (∑ v ∈ H, c v)
  have hsumH : (∑ v, cH v) = ∑ v ∈ H, c v := by simp [cH, sum_filter]
  have hsumR : (∑ v, cR v) = ∑ v ∈ Hᶜ, c v := by
    calc
      _ = ∑ v, if v ∈ Hᶜ then c v else 0 := sum_congr rfl (fun v _ => by
        by_cases hv : v ∈ H <;> simp [cR,hv])
      _ = _ := by
        have hh := sum_filter (s := (univ : Finset V)) (p := fun v => v ∈ Hᶜ) (f := c)
        simpa only [filter_mem_eq_inter,univ_inter] using hh.symm
  have hsplit := sum_add_sum_compl H c
  obtain ⟨fH,hfH,hsH⟩ := MultiGraph.bounded_allocation cH qH (by rw [hsumH];exact min_le_right _ _)
  obtain ⟨fR,hfR,hsR⟩ := MultiGraph.bounded_allocation cR (q-qH) (by
    rw [hsumR]
    dsimp only [qH]
    omega)
  have hfH0 : ∀ v ∉ H, fH v = 0 := by
    intro v hv
    have hh := hfH v
    simp only [cH,if_neg hv] at hh
    omega
  have hfR0 : ∀ v ∈ H, fR v = 0 := by
    intro v hv
    have hh := hfR v
    simp only [cR,if_pos hv] at hh
    omega
  refine ⟨fun v => fH v+fR v,?_,?_,?_⟩
  · intro v
    change fH v+fR v ≤ c v
    by_cases hv : v ∈ H
    · have hh := hfH v
      simp only [cH,if_pos hv] at hh
      rw [hfR0 v hv,add_zero]
      exact hh
    · have hh := hfR v
      simp only [cR,if_neg hv] at hh
      rw [hfH0 v hv,zero_add]
      exact hh
  · rw [sum_add_distrib,hsH,hsR]
    exact Nat.add_sub_of_le (min_le_left _ _)
  · rw [sum_add_distrib]
    have hRzero : (∑ v ∈ H, fR v) = 0 := sum_eq_zero hfR0
    have hHsum : (∑ v ∈ H, fH v) = qH := by
      have hz : (∑ v ∈ Hᶜ, fH v) = 0 := sum_eq_zero (fun v hv => hfH0 v (mem_compl.mp hv))
      have hh := sum_add_sum_compl H fH
      omega
    rw [hHsum,hRzero,add_zero]

theorem all_capacity_when_short (c f : V → ℕ) (H : Finset V) (q : ℕ)
    (hf : ∀ v, f v ≤ c v) (hpriority : (∑ v ∈ H, f v) = min q (∑ v ∈ H, c v))
    (hshort : (∑ v ∈ H, c v) ≤ q) : ∀ v ∈ H, f v = c v := by
  rw [min_eq_right hshort] at hpriority
  exact (sum_eq_sum_iff_of_le (fun v _ => hf v)).mp hpriority

end OverfullWork.PriorityCopyAllocation
