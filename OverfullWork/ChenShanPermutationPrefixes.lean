module

public import OverfullWork.ChenShanConditionalPermutation

@[expose] public section

namespace OverfullWork.ChenShan

open Finset UniformSubsetSampling
open scoped Classical

variable (V : Type*) [Fintype V]

/-- Initial segments of a fixed enumeration. Applying one permutation
to all these sets gives nested prefixes of a uniform ordering. -/
noncomputable def initialSegment (k : ℕ) : Finset V :=
  (univ : Finset (Fin (min k (Fintype.card V)))).map
    ((Fin.castLEEmb (min_le_right k (Fintype.card V))).trans
      (Fintype.equivFin V).symm.toEmbedding)

theorem mem_initialSegment (k : ℕ) (v : V) :
    v ∈ initialSegment V k ↔ ((Fintype.equivFin V) v).val < k := by
  unfold initialSegment
  constructor
  · intro hv
    obtain ⟨i,_,rfl⟩ := mem_map.mp hv
    rw [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.apply_symm_apply]
    exact i.isLt.trans_le (min_le_left _ _)
  · intro hv
    let e := Fintype.equivFin V
    have hi : (e v).val < min k (Fintype.card V) := lt_min hv (e v).isLt
    exact mem_map.mpr ⟨⟨(e v).val,hi⟩,mem_univ _,by
      change e.symm ⟨(e v).val,_⟩ = v
      rw [show (⟨(e v).val,(e v).isLt⟩ : Fin (Fintype.card V)) = e v from Fin.eta _ _,
        e.symm_apply_apply]⟩

theorem card_initialSegment (k : ℕ) (hk : k ≤ Fintype.card V) :
    (initialSegment V k).card = k := by
  simp only [initialSegment,card_map,card_univ,Fintype.card_fin,min_eq_left hk]

theorem initialSegment_mono : Monotone (initialSegment V) := by
  intro k l hk v hv
  exact (mem_initialSegment V l v).mpr ((mem_initialSegment V k v).mp hv |>.trans_le hk)

theorem initialSegment_full :
    initialSegment V (Fintype.card V) = univ := by
  apply eq_univ_of_forall
  intro v
  exact (mem_initialSegment V _ v).mpr (Fintype.equivFin V v).isLt

variable {V}

theorem card_permutation_prefix (k : ℕ) (hk : k ≤ Fintype.card V) (π : Equiv.Perm V) :
    (permutationImage (initialSegment V k) π).card = k := by
  rw [permutationImage,card_map,card_initialSegment _ _ hk]

theorem permutation_prefix_mono (π : Equiv.Perm V) :
    Monotone fun k => permutationImage (initialSegment V k) π :=
  fun _ _ h => map_subset_map.mpr (initialSegment_mono V h)

theorem permutation_prefix_full (π : Equiv.Perm V) :
    permutationImage (initialSegment V (Fintype.card V)) π = univ := by
  rw [initialSegment_full]
  apply eq_univ_of_forall
  intro v
  exact mem_map.mpr ⟨π.symm v,mem_univ _,π.apply_symm_apply v⟩

end OverfullWork.ChenShan
