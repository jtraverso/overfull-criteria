module

public import Overfull.Fork

@[expose] public section


/-! # Distinct anchors and distinct leaves from bounded local capacity

The witnesses are constructed by selecting one anchor for each leaf,
counting the resulting fibres, and choosing distinct anchor preimages.
No matching, expansion, or recolouring outcome is assumed.
-/
namespace OverfullWork.CaoChenForkSelection
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 1000000

/-- More than k*r covered leaves, with capacity at most r per anchor,
produce k+1 edges having both distinct anchors and distinct leaves. -/
theorem exists_distinct_anchors_and_leaves (A T : Finset V) (R : V → V → Prop)
    (r k : ℕ) (hcover : ∀ t ∈ T, ∃ a ∈ A, R a t)
    (hcapacity : ∀ a ∈ A, (T.filter (R a)).card ≤ r) (hcount : k * r < T.card) :
    ∃ z t : Fin (k + 1) → V, Function.Injective z ∧ Function.Injective t ∧
      ∀ i, z i ∈ A ∧ t i ∈ T ∧ R (z i) (t i) := by
  classical
  let f : V → V := fun t => if ht : t ∈ T then Classical.choose (hcover t ht) else t
  have hf : ∀ t ∈ T, f t ∈ A ∧ R (f t) t := by
    intro t ht
    dsimp only [f]
    rw [dif_pos ht]
    exact Classical.choose_spec (hcover t ht)
  let Z := T.image f
  have hZA : Z ⊆ A := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hz
    exact (hf t ht).1
  have hZcard : k + 1 ≤ Z.card := by
    by_contra hn
    have hsmall : Z.card ≤ k := by omega
    have hsub : T ⊆ Z.biUnion (fun a => T.filter (R a)) := by
      intro t ht
      exact mem_biUnion.mpr ⟨f t, mem_image.mpr ⟨t, ht, rfl⟩,
        mem_filter.mpr ⟨ht, (hf t ht).2⟩⟩
    have hbound : T.card ≤ Z.card * r := by
      calc
        T.card ≤ (Z.biUnion (fun a => T.filter (R a))).card := card_le_card hsub
        _ ≤ ∑ a ∈ Z, (T.filter (R a)).card := card_biUnion_le
        _ ≤ ∑ _a ∈ Z, r := sum_le_sum (fun a ha => hcapacity a (hZA ha))
        _ = Z.card * r := by simp
    have hmul := Nat.mul_le_mul_right r hsmall
    omega

  let e : Fin (k + 1) ↪ Z := (Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin (k + 1)) ≤ Fintype.card Z by simpa using hZcard)).some
  have hpre : ∀ z : Z, ∃ t ∈ T, f t = z.val := fun z => mem_image.mp z.property
  choose pre hpreT hpreEq using hpre
  have hinj : Function.Injective (fun i : Fin (k + 1) => (e i).val) := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  refine ⟨fun i => (e i).val, fun i => pre (e i), hinj, ?_, ?_⟩
  · intro i j hij
    apply hinj
    change (e i).val = (e j).val
    change pre (e i) = pre (e j) at hij
    rw [← hpreEq (e i), ← hpreEq (e j)]
    exact congrArg f hij
  · intro i
    have hh := hf (pre (e i)) (hpreT (e i))
    rw [hpreEq (e i)] at hh
    exact ⟨hh.1, hpreT (e i), hh.2⟩

/-- The numerical selection step required in Cao--Chen Claim 5.3.
The unresolved recolouring step must supply the many good leaves. -/
theorem exists_d_add_two_anchors_and_leaves (A T : Finset V) (R : V → V → Prop)
    (d : ℕ) (hcover : ∀ t ∈ T, ∃ a ∈ A, R a t)
    (hcapacity : ∀ a ∈ A, (T.filter (R a)).card ≤ d - 1)
    (hcount : (d + 1) * (d - 1) < T.card) :
    ∃ z t : Fin (d + 2) → V, Function.Injective z ∧ Function.Injective t ∧
      ∀ i, z i ∈ A ∧ t i ∈ T ∧ R (z i) (t i) :=
  exists_distinct_anchors_and_leaves A T R (d - 1) (d + 1) hcover hcapacity hcount

end OverfullWork.CaoChenForkSelection
