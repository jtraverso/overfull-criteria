module

public import OverfullWork.UniformSamplingBudget
public import Mathlib.GroupTheory.Perm.Fin

@[expose] public section


/-! A common random permutation of a prescribed partition has the
uniform fixed-size sample as each marginal. This is the finite
sampling step used in GGKLO Lemma 4.17 and Lemma 7.3(i). -/
namespace OverfullWork.UniformSubsetSampling

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

private theorem exists_permutation_map (X Y : Finset V) (h : X.card = Y.card) :
    ∃ π : Equiv.Perm V, X.map π.toEmbedding = Y := by
  classical
  let c (S : Finset V) : ((S : Set V)ᶜ : Set V) ≃ ↥(Sᶜ : Finset V) :=
    ⟨fun v => ⟨v.val, mem_compl.mpr v.prop⟩, fun v => ⟨v.val, mem_compl.mp v.prop⟩,
      fun _ => rfl, fun _ => rfl⟩
  have hc : (Xᶜ : Finset V).card = (Yᶜ : Finset V).card := by simp only [card_compl, h]
  let a : (X : Set V) ≃ (Y : Set V) := Finset.equivOfCardEq h
  let b := (c X).trans ((Finset.equivOfCardEq hc).trans (c Y).symm)
  let g := (Equiv.Set.compl (s := (X : Set V)) (t := (Y : Set V)) a).symm b
  refine ⟨g.val, eq_of_subset_of_card_le ?_ (by rw [card_map, h])⟩
  intro v hv
  obtain ⟨x,hx,rfl⟩ := mem_map.mp hv
  have he := g.prop ⟨x,hx⟩
  change g.val x = (a ⟨x,hx⟩).val at he
  exact he.symm ▸ (a ⟨x,hx⟩).prop

noncomputable def permutationImage (S : Finset V) (π : Equiv.Perm V) :=
  S.map π.toEmbedding

omit [Fintype V] in
private theorem permutationImage_trans (S : Finset V) (π γ : Equiv.Perm V) :
    permutationImage S (π.trans γ) = (permutationImage S π).map γ.toEmbedding := by
  exact (Finset.map_map π.toEmbedding γ.toEmbedding S).symm

private theorem permutation_fiber_card (S X Y : Finset V) (h : X.card = Y.card) :
    ((univ : Finset (Equiv.Perm V)).filter (fun π => permutationImage S π = X)).card =
      ((univ : Finset (Equiv.Perm V)).filter (fun π => permutationImage S π = Y)).card := by
  classical
  obtain ⟨γ,hγ⟩ := exists_permutation_map X Y h
  have hγ' : Y.map γ.symm.toEmbedding = X := by
    rw [← hγ, map_map]
    have he : γ.toEmbedding.trans γ.symm.toEmbedding = Function.Embedding.refl V := by
      ext x
      exact γ.symm_apply_apply x
    rw [he, map_refl]
  apply card_bij (fun π _ => π.trans γ)
  · intro π hπ
    exact mem_filter.mpr ⟨mem_univ _, by rw [permutationImage_trans, (mem_filter.mp hπ).2, hγ]⟩
  · intro π _ σ _ hEq
    apply Equiv.ext
    intro v
    exact γ.injective (congrArg (fun f : Equiv.Perm V => f v) hEq)
  · intro π hπ
    refine ⟨π.trans γ.symm, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
    · rw [permutationImage_trans, (mem_filter.mp hπ).2, hγ']
    · apply Equiv.ext
      intro v
      exact γ.apply_symm_apply (π v)

private theorem permutation_preimage_card (S : Finset V) (T : Finset (Finset V))
    (hT : T ⊆ (univ : Finset V).powersetCard S.card) :
    ((univ : Finset (Equiv.Perm V)).filter (fun π => permutationImage S π ∈ T)).card =
      T.card*((univ : Finset (Equiv.Perm V)).filter (fun π => permutationImage S π = S)).card := by
  rw [← sum_card_fiberwise_eq_card_filter]
  apply sum_const_nat
  intro X hX
  exact permutation_fiber_card S X S (mem_powersetCard.mp (hT hX)).2

/-- The fraction of permutations producing a bad image of one block
equals the fixed-size sampling probability. -/
theorem permutation_probability (S : Finset V) (bad : Finset V → Prop) :
    (((univ : Finset (Equiv.Perm V)).filter (fun π => bad (permutationImage S π))).card:ℝ) =
      probability S.card bad*(Fintype.card (Equiv.Perm V):ℝ) := by
  classical
  let T := (univ : Finset V).powersetCard S.card
  let k := ((univ : Finset (Equiv.Perm V)).filter (fun π => permutationImage S π = S)).card
  have hMem : ∀ π, permutationImage S π ∈ T := fun π => mem_powersetCard.mpr ⟨subset_univ _, card_map _⟩
  have hTotal := permutation_preimage_card S T (Subset.refl _)
  have hAll : (univ.filter fun π => permutationImage S π ∈ T) = univ :=
    eq_univ_of_forall (fun π => mem_filter.mpr ⟨mem_univ _,hMem π⟩)
  rw [hAll, card_univ] at hTotal
  have hBad := permutation_preimage_card S (T.filter bad) (filter_subset _ _)
  have hFilter : (univ.filter fun π => permutationImage S π ∈ T.filter bad) =
      univ.filter fun π => bad (permutationImage S π) := by
    ext π
    rw [mem_filter, mem_filter, mem_filter]
    simp only [mem_univ, true_and, hMem]
  rw [hFilter] at hBad
  have hT : T.card = (Fintype.card V).choose S.card := by simp [T, card_powersetCard]
  have hPos : (0:ℝ) < (Fintype.card V).choose S.card := by
    exact_mod_cast Nat.choose_pos (card_le_univ S)
  rw [probability, ← hT, hBad, hTotal]
  push_cast
  rw [← mul_assoc, div_mul_cancel₀ _ (by rw [hT]; exact hPos.ne' : (T.card:ℝ) ≠ 0)]

/-- One permutation avoids all blockwise bad events whenever their
fixed-size probabilities sum to less than one. -/
theorem exists_permutation_avoiding {I : Type*} [Fintype I] (blocks : I → Finset V)
    (bad : I → Finset V → Prop) (h : (∑ i, probability (blocks i).card (bad i)) < 1) :
    ∃ π : Equiv.Perm V, ∀ i, ¬bad i ((blocks i).map π.toEmbedding) := by
  classical
  let E := fun i => (univ : Finset (Equiv.Perm V)).filter (fun π => bad i (permutationImage (blocks i) π))
  let F := (univ : Finset I).biUnion E
  have hBound : (F.card:ℝ) ≤ (∑ i, probability (blocks i).card (bad i))*
      (Fintype.card (Equiv.Perm V):ℝ) := by
    rw [sum_mul]
    simp_rw [← permutation_probability]
    exact_mod_cast (card_biUnion_le (s := (univ : Finset I)) (t := E))
  have hPos : (0:ℝ) < Fintype.card (Equiv.Perm V) := by positivity
  have hStrict : (F.card:ℝ) < Fintype.card (Equiv.Perm V) := by
    simpa only [one_mul] using hBound.trans_lt (mul_lt_mul_of_pos_right h hPos)
  have hlt : F.card < Fintype.card (Equiv.Perm V) := by exact_mod_cast hStrict
  have hPos' : 0 < ((univ : Finset (Equiv.Perm V)) \ F).card := by rw [card_univ_sdiff]; omega
  obtain ⟨π,hπ⟩ := card_pos.mp hPos'
  refine ⟨π, fun i hBad => (mem_sdiff.mp hπ).2 ?_⟩
  exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_univ _,hBad⟩⟩

end OverfullWork.UniformSubsetSampling
