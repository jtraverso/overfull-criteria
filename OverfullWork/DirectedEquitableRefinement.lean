module

public import OverfullWork.FiniteUniformChunks
public import OverfullWork.DirectedCommonEnergyMonotonicity

@[expose] public section


/-! Equalize a common directed partition by refining it. The short
remainders remain whole parts so that every old part is partitioned
exactly and its energy contribution can still be counted. -/
namespace OverfullWork.DirectedPairEnergy

open Finset Finpartition DirectedClusterQuotient
open scoped Classical
variable {V : Type*} [Fintype V]

set_option maxHeartbeats 750000 in
/-- Divide a cell into equal parts and at most one smaller part,
bounding both the number of parts and the leftover mass. -/
theorem exists_uniform_chunk_finpartition (A : Finset V) (m : ℕ) (hm : 0 < m) :
    ∃ Q : Finpartition A, Q.parts.card ≤ A.card/m+1 ∧
      (∀ U ∈ Q.parts, U.card ≤ m) ∧
      (∑ U ∈ Q.parts, if U.card = m then (0:ℝ) else (U.card:ℝ)) ≤ (m:ℝ)-1 := by
  obtain ⟨C,hC,hSize,hApart,hR⟩ := exists_uniform_chunks A m hm
  let B := (univ : Finset (Fin (A.card/m))).image C
  let rem := A \ univ.biUnion C
  let parts := insert rem B
  have hDis : (↑parts : Set (Finset V)).PairwiseDisjoint id := by
    intro U hU W hW hNe
    change U ∈ insert rem B at hU
    change W ∈ insert rem B at hW
    rcases mem_insert.mp hU with rfl | hU
    · have hW' := (mem_insert.mp hW).resolve_left (fun h => hNe h.symm)
      obtain ⟨j,_,rfl⟩ := mem_image.mp hW'
      exact disjoint_left.mpr (fun x hx hj => (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨j,mem_univ _,hj⟩))
    · rcases mem_insert.mp hW with rfl | hW
      · obtain ⟨i,_,rfl⟩ := mem_image.mp hU
        exact disjoint_left.mpr (fun x hi hx => (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨i,mem_univ _,hi⟩))
      · obtain ⟨i,_,rfl⟩ := mem_image.mp hU
        obtain ⟨j,_,rfl⟩ := mem_image.mp hW
        exact hApart i j (fun h => hNe (congrArg C h))
  have hUnion : parts.sup id = A := by
    rw [sup_eq_biUnion]
    ext x
    simp only [mem_biUnion,id_eq]
    constructor
    · rintro ⟨U,hU,hx⟩
      rcases mem_insert.mp hU with rfl | hU
      · exact (mem_sdiff.mp hx).1
      · obtain ⟨i,_,rfl⟩ := mem_image.mp hU
        exact hC i hx
    · intro hx
      by_cases h : x ∈ univ.biUnion C
      · obtain ⟨i,_,hi⟩ := mem_biUnion.mp h
        exact ⟨C i,mem_insert_of_mem (mem_image.mpr ⟨i,mem_univ _,rfl⟩),hi⟩
      · exact ⟨rem,mem_insert_self _ _,mem_sdiff.mpr ⟨hx,h⟩⟩
  let Q := (Finpartition.ofPairwiseDisjoint parts hDis).copy hUnion
  have hCount : Q.parts.card ≤ A.card/m+1 := calc
    _ ≤ parts.card := card_erase_le
    _ ≤ B.card+1 := card_insert_le _ _
    _ ≤ _ := Nat.add_le_add_right (card_image_le.trans (by simp)) _
  have hMember (U : Finset V) (hU : U ∈ Q.parts) : U = rem ∨ U ∈ B :=
    mem_insert.mp (mem_of_mem_erase hU)
  have hSmall : rem.card < m := hR
  have hRemR : (rem.card:ℝ) ≤ (m:ℝ)-1 := by
    have h : ((rem.card:ℕ):ℝ)+1 ≤ m := by exact_mod_cast hSmall
    linarith only [h]
  refine ⟨Q,hCount,?_,?_⟩
  · intro U hU
    rcases hMember U hU with rfl | hU
    · exact hSmall.le
    · obtain ⟨i,_,rfl⟩ := mem_image.mp hU
      exact (hSize i).le
  · calc
      _ ≤ ∑ U ∈ Q.parts, if U = rem then (rem.card:ℝ) else 0 := by
        apply sum_le_sum
        intro U hU
        rcases hMember U hU with rfl | hU
        · simp [hSmall.ne]
        · obtain ⟨i,_,rfl⟩ := mem_image.mp hU
          simp only [hSize,if_true]
          split_ifs <;> positivity
      _ ≤ (rem.card:ℝ) := by
        by_cases h : rem ∈ Q.parts <;> simp [h]
      _ ≤ _ := hRemR

set_option maxHeartbeats 800000 in
/-- Rechunk an entire partition without lowering its directed
energy. Only the bounded sum of short remainders is exceptional. -/
theorem exists_equitable_refinement_at_size (D : Digraph V)
    (P : Finpartition (univ : Finset V)) (m : ℕ) (hm : 0 < m) :
    ∃ Q : Finpartition (univ : Finset V),
      Q ≤ P ∧ partitionEnergy D P ≤ partitionEnergy D Q ∧
      Q.parts.card ≤ Fintype.card V/m+P.parts.card ∧ (∀ U ∈ Q.parts, U.card ≤ m) ∧
      (∑ U ∈ Q.parts, if U.card = m then (0:ℝ) else (U.card:ℝ)) ≤ (P.parts.card:ℝ)*((m:ℝ)-1) := by
  choose Q hQ hSize hMass using fun U : P.parts => exists_uniform_chunk_finpartition U.val m hm
  let bind (U : Finset V) (hU : U ∈ P.parts) : Finpartition U := Q ⟨U,hU⟩
  refine ⟨P.bind bind,?_,partitionEnergy_bind_mono D P bind,?_,?_,?_⟩
  · intro U hU
    obtain ⟨A,hA,hUA⟩ := mem_bind.mp hU
    exact ⟨A,hA,(bind A hA).le hUA⟩
  · rw [card_bind,Finset.attach_eq_univ]
    have hSum : (∑ U : P.parts, (U.val.card/m)) ≤ Fintype.card V/m := by
      apply (Nat.le_div_iff_mul_le hm).mpr
      rw [Finset.sum_mul]
      calc
        _ ≤ ∑ U : P.parts, U.val.card := sum_le_sum (fun U _ => Nat.div_mul_le_self _ _)
        _ = _ := by rw [Finset.sum_coe_sort,P.sum_card_parts,card_univ]
    calc
      _ ≤ ∑ U : P.parts, (U.val.card/m+1) := sum_le_sum (fun U _ => hQ U)
      _ ≤ _ := by
        simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one]
        exact Nat.add_le_add_right hSum _
  · intro U hU
    obtain ⟨A,hA,hUA⟩ := mem_bind.mp hU
    exact hSize ⟨A,hA⟩ U hUA
  · rw [sum_parts_bind]
    exact (sum_le_sum (fun U _ => hMass U)).trans (by
      simp only [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,le_refl])

end OverfullWork.DirectedPairEnergy
