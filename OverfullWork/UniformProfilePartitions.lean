module

public import OverfullWork.UniformPartitionSampling

@[expose] public section


/-! Exact-size random partitions with simultaneous profile guarantees.
Counting the union of bad block events needs only the single-block
marginals, even though the blocks themselves are dependent. -/
namespace OverfullWork.UniformSubsetSampling

open Finset
open scoped Classical
universe u v w
variable {V : Type u} [Fintype V] {I : Type v} [Fintype I]

noncomputable def slice (rank : V → I) (i : I) : Finset V :=
  univ.filter fun x => rank x = i

omit [Fintype I] in
@[simp] theorem mem_slice (rank : V → I) (i : I) (x : V) :
    x ∈ slice rank i ↔ rank x = i := by simp [slice]

/-- Prescribed sizes and fixed-size marginal bounds construct an actual
partition with the required properties in every block. -/
theorem exists_partition_avoiding (size : I → ℕ)
    (hSize : (∑ i,size i) = Fintype.card V) (bad : I → Finset V → Prop)
    (hBad : (∑ i,probability (size i) (bad i)) < 1) :
    ∃ rank : V → I, ∀ i, (slice rank i).card = size i ∧ ¬bad i (slice rank i) := by
  classical
  have hCard : Fintype.card V = Fintype.card (Σ i, Fin (size i)) := by
    simp only [Fintype.card_sigma, Fintype.card_fin, hSize]
  let e := Fintype.equivOfCardEq hCard
  let rank₀ : V → I := fun x => (e x).1
  have hSlice : ∀ i, (slice rank₀ i).card = size i := by
    intro i
    have he : (univ : Finset (Fin (size i))).map
        (⟨fun j => e.symm ⟨i,j⟩, fun j k he =>
          eq_of_heq (Sigma.mk.inj (e.symm.injective he)).2⟩ : Fin (size i) ↪ V) =
        slice rank₀ i := by
      ext x
      simp only [slice,mem_map,mem_univ,true_and,mem_filter]
      constructor
      · rintro ⟨j,rfl⟩
        change (e (e.symm ⟨i,j⟩)).1 = i
        rw [e.apply_symm_apply]
      · intro hx
        rcases h : e x with ⟨j,f⟩
        have hj : j = i := by
          change (e x).1 = i at hx
          rwa [h] at hx
        subst j
        refine ⟨f, ?_⟩
        change e.symm ⟨i,f⟩ = x
        rw [← h,e.symm_apply_apply]
    rw [← he, card_map, card_univ, Fintype.card_fin]
  obtain ⟨π,hπ⟩ := exists_permutation_avoiding (slice rank₀) bad (by simpa only [hSlice] using hBad)
  refine ⟨rank₀ ∘ π.symm, fun i => ?_⟩
  have he : slice (rank₀ ∘ π.symm) i = (slice rank₀ i).map π.toEmbedding := by
    ext x
    rw [mem_map_equiv]
    simp only [slice,mem_filter,mem_univ,true_and,Function.comp_apply]
  rw [he,card_map,hSlice]
  exact ⟨rfl,hπ i⟩

/-- A fixed order threshold guarantees simultaneous additive profile
control in every prescribed block of a partition. -/
theorem exists_partition_profile_threshold (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I] {J : Type w} [Fintype J]
      (profiles : J → Finset V) (size : I → ℕ), N ≤ Fintype.card V →
      (∑ i,size i) = Fintype.card V → (Fintype.card J:ℝ) ≤ C*(Fintype.card V:ℝ) →
      Fintype.card I < Fintype.card V^2 →
      ∃ rank : V → I, ∀ i, (slice rank i).card = size i ∧
        ∀ j, |((slice rank i ∩ profiles j).card:ℝ)-
          ((size i:ℝ)/(Fintype.card V:ℝ))*(profiles j).card| < ε*(Fintype.card V:ℝ) := by
  obtain ⟨N,hN⟩ := exists_uniform_profile_threshold.{u,w} C ε hC hε
  refine ⟨max N 2, ?_⟩
  intro V _ I _ J _ profiles size hn hSize hProfiles hI
  let bad (i : I) (X : Finset V) : Prop := ∃ j,
    ε*(Fintype.card V:ℝ) ≤ |((X ∩ profiles j).card:ℝ)-
      ((size i:ℝ)/(Fintype.card V:ℝ))*(profiles j).card|
  have hEach : ∀ i, probability (size i) (bad i) ≤ 1/(Fintype.card V:ℝ)^2 := by
    intro i
    have hi : size i ≤ Fintype.card V := by
      rw [← hSize]
      exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    exact hN profiles (size i) (by omega) hi hProfiles
  have hlt : (∑ i, probability (size i) (bad i)) < 1 := by
    have hi : (Fintype.card I:ℝ) < (Fintype.card V:ℝ)^2 := by exact_mod_cast hI
    have hn₀ : (0:ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
    calc
      _ ≤ ∑ _i : I, 1/(Fintype.card V:ℝ)^2 :=
        sum_le_sum (fun i _ => hEach i)
      _ = (Fintype.card I:ℝ)/(Fintype.card V:ℝ)^2 := by simp [div_eq_mul_inv]
      _ < _ := (div_lt_one (pow_pos hn₀ _)).mpr hi
  obtain ⟨rank,hRank⟩ := exists_partition_avoiding size hSize bad hlt
  refine ⟨rank, fun i => ⟨(hRank i).1, fun j => ?_⟩⟩
  exact not_le.mp (fun h => (hRank i).2 ⟨j,h⟩)

end OverfullWork.UniformSubsetSampling
