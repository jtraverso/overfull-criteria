module

public import OverfullWork.CMSOperation41RoundLimits

@[expose] public section


/-! Degree estimates used in Claim 4.1(4) and Claim 4.2(3).
Once a vertex leaves the exceptional set while still active, its
degree follows the target except for subsequent preprocessing losses.
The special-spoke charge is shared across each pair of vertices. -/
namespace OverfullWork.CMSTrimmingRound

open Finset
open scoped Classical

variable {V : Type*} [DecidableEq V]

theorem retired_degree_bound_from_trimming_history
    (D r a : ℕ) (U active : ℕ → Finset V) (degree loss : ℕ → V → ℕ)
    (hFirst : ∀ v ∈ active 0,v ∉ U 0 → D ≤ degree 0 v+a)
    (hActive : ∀ i < r,active (i+1) ⊆ active i)
    (hRetire : ∀ i < r,∀ v ∈ active (i+1),v ∈ U i → v ∉ U (i+1) →
      D-2*(i+1) ≤ degree (i+1) v+a)
    (hStep : ∀ i < r,∀ v ∈ active (i+1),v ∉ U i →
      degree i v ≤ degree (i+1) v+(2+loss i v))
    (hRoom : 2*r ≤ D) :
    ∀ j ≤ r,∀ v ∈ active j,v ∉ U j →
      D-2*j ≤ degree j v+a+(∑ i ∈ range j,loss i v) := by
  intro j hj
  induction j with
  | zero =>
    intro v hv hU
    simpa using hFirst v hv hU
  | succ j ih =>
    intro v hv hU'
    have hj' : j < r := by omega
    have hv' := hActive j hj' hv
    by_cases hU : v ∈ U j
    · have h := hRetire j hj' v hv hU hU'
      omega
    · have hOld := ih hj'.le v hv' hU
      have hNew := hStep j hj' v hv hU
      rw [sum_range_succ]
      omega

def specialUseCount (special : ℕ → Option V) (j : ℕ) (v : V) : ℕ :=
  ((range j).filter (fun i => special i = some v)).card

theorem two_special_use_counts_le_rounds (special : ℕ → Option V) (j : ℕ) {u v : V}
    (hne : u ≠ v) :
    specialUseCount special j u+specialUseCount special j v ≤ j := by
  let A := (range j).filter (fun i => special i = some u)
  let B := (range j).filter (fun i => special i = some v)
  have hDis : Disjoint A B := by
    apply disjoint_left.mpr
    intro i hi hi'
    exact hne (Option.some.inj ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hi').2))
  have hSub : A∪B ⊆ range j := union_subset (filter_subset _ _) (filter_subset _ _)
  have h := card_le_card hSub
  rw [card_range,card_union_of_disjoint hDis] at h
  exact h

theorem weak_degree_sum_from_special_charges
    (D d j c : ℕ) (initial final : V → ℕ) (special : ℕ → Option V)
    {u v : V} (hne : u ≠ v)
    (hTarget : d+2*j = D) (hWeak : D+2 ≤ initial u+initial v)
    (hU : initial u ≤ final u+c+2*specialUseCount special j u)
    (hV : initial v ≤ final v+c+2*specialUseCount special j v) :
    d+2 ≤ final u+final v+2*c := by
  have hPair := two_special_use_counts_le_rounds special j hne
  omega

end OverfullWork.CMSTrimmingRound
