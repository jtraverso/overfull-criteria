module

public import OverfullWork.MaximumCoreDegree

@[expose] public section


/-! # Critical deficit moments controlled by the local maximum-core profile

The estimates sum over the cut between maximum-degree and nonmaximum
vertices. They do not replace the distribution by its worst degree gap.
-/
namespace OverfullWork.Gate8J2C
open SimpleGraph Finset
open scoped Classical
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A maximum vertex splits its degree between maximum and nonmaximum
neighbours. -/
theorem nonmaximum_neighbours_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : V) (hb : G.degree b=G.maxDegree) :
    ((G.neighborFinset b).filter fun x => G.degree x≠G.maxDegree).card=
      G.maxDegree-maximumNeighbours G b := by
  have h:=card_filter_add_card_filter_not (s:=G.neighborFinset b)
    (fun x => G.degree x=G.maxDegree)
  rw [card_neighborFinset_eq_degree,hb] at h
  change maximumNeighbours G b+
    ((G.neighborFinset b).filter fun x => G.degree x≠G.maxDegree).card=G.maxDegree at h
  omega

/-- Express a sum over maximum-degree neighbours using the core vertex set. -/
theorem sum_over_maximum_neighbours (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) (f : V → ℕ) :
    (∑ b∈univ.filter (fun b => G.degree b=G.maxDegree),
      if G.Adj x b then f b else 0)=
      ∑ b∈(G.neighborFinset x).filter (fun b => G.degree b=G.maxDegree),f b := by
  rw [←sum_filter]
  congr 1
  ext b
  simp only [mem_filter,mem_univ,true_and,mem_neighborFinset]
  tauto

/-- Every edge forces the corresponding deficit power into the local
maximum-neighbour power at its opposite endpoint. -/
theorem critical_deficit_power_row (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (p : ℕ) (x : V) :
    maximumNeighbours G x*(G.maxDegree-G.degree x+1)^p≤
      ∑ b∈univ.filter (fun b => G.degree b=G.maxDegree),
        if G.Adj x b then (maximumNeighbours G b)^p else 0 := by
  rw [sum_over_maximum_neighbours]
  calc
    _ = ∑ _b∈(G.neighborFinset x).filter (fun b => G.degree b=G.maxDegree),
        (G.maxDegree-G.degree x+1)^p := by
      simp only [sum_const,nsmul_eq_mul,Nat.cast_id,maximumNeighbours]
    _ ≤ _ := by
      apply sum_le_sum
      intro b hb
      have hbx:=((mem_neighborFinset G x b).mp (mem_filter.mp hb).1).symm
      exact Nat.pow_le_pow_left (deficit_le_maximumNeighbours G hcrit hbx) p

/-- Deficit moments outside the maximum-degree core are bounded by the
local power profile of that core. This is valid for every natural p. -/
theorem critical_deficit_power_le_core_profile (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ v,0<G.degree v) (p : ℕ) :
    2*(∑ x∈univ.filter (fun x => G.degree x≠G.maxDegree),
      (G.maxDegree-G.degree x+1)^p)≤
      ∑ b∈univ.filter (fun b => G.degree b=G.maxDegree),
        (maximumNeighbours G b)^p*(G.maxDegree-maximumNeighbours G b) := by
  let L:=univ.filter fun x => G.degree x≠G.maxDegree
  let K:=univ.filter fun b => G.degree b=G.maxDegree
  have hrow : ∀ x∈L,2*(G.maxDegree-G.degree x+1)^p≤
      ∑ b∈K,if G.Adj x b then (maximumNeighbours G b)^p else 0 := by
    intro x _
    exact (Nat.mul_le_mul_right _ (critical_maximumNeighbours_ge_two G hcrit hactive x)).trans
      (critical_deficit_power_row G hcrit p x)
  calc
    _ = ∑ x∈L,2*(G.maxDegree-G.degree x+1)^p := by rw [mul_sum]
    _ ≤ ∑ x∈L,∑ b∈K,if G.Adj x b then (maximumNeighbours G b)^p else 0 :=
      sum_le_sum hrow
    _ = ∑ b∈K,∑ x∈L,if G.Adj x b then (maximumNeighbours G b)^p else 0 := by
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro b hb
      have hbD:=(mem_filter.mp hb).2
      rw [←sum_filter,sum_const,nsmul_eq_mul,Nat.cast_id]
      have hcard : (L.filter fun x => G.Adj x b).card=
          ((G.neighborFinset b).filter fun x => G.degree x≠G.maxDegree).card := by
        congr 1
        ext x
        simp only [L,mem_filter,mem_univ,true_and,mem_neighborFinset]
        exact ⟨fun h => ⟨h.2.symm,h.1⟩,fun h => ⟨h.2,h.1.symm⟩⟩
      rw [hcard,nonmaximum_neighbours_card G b hbD,Nat.mul_comm]

/-- The square-moment specialization needed by variance estimates. -/
theorem critical_deficit_square_le_core_profile (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ v,0<G.degree v) :
    2*(∑ x∈univ.filter (fun x => G.degree x≠G.maxDegree),
      (G.maxDegree-G.degree x+1)^2)≤
      ∑ b∈univ.filter (fun b => G.degree b=G.maxDegree),
        (maximumNeighbours G b)^2*(G.maxDegree-maximumNeighbours G b) :=
  critical_deficit_power_le_core_profile G hcrit hactive 2

/-- A power-tail bound for the exceptional low-degree stratum. The
threshold r>0 ensures that no maximum-degree vertex lies in the stratum. -/
theorem critical_deficit_tail_le_core_profile (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcrit : Overfull.IsDeltaCritical G) (hactive : ∀ v,0<G.degree v)
    (p r : ℕ) (hr : 0<r) :
    2*(r+1)^p*(univ.filter fun x => G.degree x+r≤G.maxDegree).card≤
      ∑ b∈univ.filter (fun b => G.degree b=G.maxDegree),
        (maximumNeighbours G b)^p*(G.maxDegree-maximumNeighbours G b) := by
  let T:=univ.filter fun x => G.degree x+r≤G.maxDegree
  let L:=univ.filter fun x => G.degree x≠G.maxDegree
  have hsub : T⊆L := by
    intro x hx
    have hh:=(mem_filter.mp hx).2
    apply mem_filter.mpr
    exact ⟨mem_univ x,by omega⟩
  have hpoint : ∀ x∈T,(r+1)^p≤(G.maxDegree-G.degree x+1)^p := by
    intro x hx
    have hh:=(mem_filter.mp hx).2
    exact Nat.pow_le_pow_left (by omega) p
  have hs : (∑ x∈T,(G.maxDegree-G.degree x+1)^p)≤
      ∑ x∈L,(G.maxDegree-G.degree x+1)^p :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  calc
    _ = 2*(∑ _x∈T,(r+1)^p) := by
      simp only [sum_const,nsmul_eq_mul,Nat.cast_id]
      ring
    _ ≤ 2*(∑ x∈T,(G.maxDegree-G.degree x+1)^p):=Nat.mul_le_mul_left 2 (sum_le_sum hpoint)
    _ ≤ 2*(∑ x∈L,(G.maxDegree-G.degree x+1)^p):=Nat.mul_le_mul_left 2 hs
    _ ≤ _:=critical_deficit_power_le_core_profile G hcrit hactive p

end OverfullWork.Gate8J2C
