module

public import OverfullWork.DirectedReserveUsage
public import OverfullWork.RobustReservePartition

@[expose] public section


/-! Assign the parts of the sampled reserve cyclically to the layouts,
and delete exactly the layout vertices in the assigned part. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedReserveUsage UniformSubsetSampling
open scoped Classical
variable {V J : Type*} [Fintype V] [Fintype J]

private theorem ceiling_mul_ge (n k : ℕ) (hk : 0 < k) : n ≤ (n+k-1)/k*k := by
  have hm := Nat.mod_lt (n+k-1) hk
  have he := Nat.mod_add_div (n+k-1) k
  rw [Nat.mul_comm] at he
  omega

/-- Cyclic assignment of the rounds to the partition blocks gives the
ceiling bound used in (7.2). The bound persists after trimming each block. -/
theorem exists_balanced_block_schedule {k : ℕ} (hk : 0 < k)
    (rank : V → Fin k) (boundary : J → Finset V) :
    ∃ slot : J → Fin k,
      let A := fun i => slice rank (slot i) \ boundary i
      (∀ i, Disjoint (boundary i) (A i)) ∧
      (∀ v, visits A v ≤ (Fintype.card J+k-1)/k) ∧
      (∀ i, (slice rank (slot i) \ A i).card ≤ (boundary i).card) := by
  let e := Fintype.equivFin J
  let slot (i : J) : Fin k := ⟨(e i).val%k,Nat.mod_lt _ hk⟩
  let A := fun i => slice rank (slot i) \ boundary i
  refine ⟨slot,?_,?_,?_⟩
  · intro i
    exact disjoint_left.mpr fun v hv hA => (mem_sdiff.mp hA).2 hv
  · intro v
    let cap := (Fintype.card J+k-1)/k
    let F := (univ : Finset J).filter fun i => v ∈ A i
    change F.card ≤ cap
    rw [← card_range cap]
    apply card_le_card_of_injOn (fun i : J => (e i).val/k)
    · intro i _
      have he := (e i).isLt
      have hh := ceiling_mul_ge (Fintype.card J) k hk
      exact mem_range.mpr ((Nat.div_lt_iff_lt_mul hk).mpr (he.trans_le hh))
    · intro i hi j hj hquot
      change (e i).val/k = (e j).val/k at hquot
      have hI : rank v = slot i := (mem_slice _ _ _).mp (mem_sdiff.mp (mem_filter.mp hi).2).1
      have hJ : rank v = slot j := (mem_slice _ _ _).mp (mem_sdiff.mp (mem_filter.mp hj).2).1
      have hMod : (e i).val%k = (e j).val%k := congrArg Fin.val (hI.symm.trans hJ)
      apply e.injective
      apply Fin.ext
      calc
        (e i).val = (e i).val%k+k*((e i).val/k) := (Nat.mod_add_div _ _).symm
        _ = (e j).val%k+k*((e j).val/k) := by rw [hMod,hquot]
        _ = (e j).val := Nat.mod_add_div _ _
  · intro i
    apply card_le_card
    intro v hv
    by_contra hb
    exact (mem_sdiff.mp hv).2 (mem_sdiff.mpr ⟨(mem_sdiff.mp hv).1,hb⟩)

/-- Divide a finite layout index into disjoint groups with the balanced
ceiling bound, for either scale in the batch induction. -/
theorem exists_balanced_layout_groups {k : ℕ} (hk : 0 < k) :
    ∃ groups : Fin k → Finset J,
      (∀ i, (groups i).card ≤ (Fintype.card J+k-1)/k) ∧
      Pairwise (fun i j => Disjoint (groups i) (groups j)) ∧
      (univ : Finset (Fin k)).biUnion groups = (univ : Finset J) := by
  obtain ⟨slot,_,hVisits,_⟩ := exists_balanced_block_schedule (V := Fin k) (J := J) hk
    id (fun _ => ∅)
  let group : Fin k → Finset J := fun i => univ.filter (fun j => slot j = i)
  refine ⟨group,?_,?_,?_⟩
  · intro i
    convert hVisits i using 1
    unfold visits
    congr 1
    ext j
    simp [group, mem_slice, eq_comm]
  · intro i j hij
    exact disjoint_left.mpr fun x hx hy =>
      hij (((mem_filter.mp hx).2).symm.trans (mem_filter.mp hy).2)
  · ext i
    exact ⟨fun _ => mem_univ _,fun _ => mem_biUnion.mpr
      ⟨slot i,mem_univ _,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩⟩

end OverfullWork.DirectedSpanningConfiguration
