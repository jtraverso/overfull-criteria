module

public import OverfullWork.ChenShanReserveAllTests
import OverfullWork.DenseHall
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset IndependentBernoulliSampling
open scoped Classical

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

def tripartiteAdjacent (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (x y : TripartiteVertex A B W) : Prop :=
  tripartiteArc F P Q x y ∨ tripartiteArc F P Q y x

noncomputable def crossingCommonCandidates
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (x y : TripartiteVertex A B W) : Finset (TripartiteVertex A B W) :=
  (S.vertices (i+1)).filter (fun z => tripartiteAdjacent F P Q x z ∧ tripartiteAdjacent F P Q y z)

theorem crossing_common_candidates_slots
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (x y : TripartiteVertex A B W) (hxy : x ≠ y)
    (hx : x ∈ S.vertices i \ S.vertices (i+1)) (hy : y ∈ S.vertices i \ S.vertices (i+1)) :
    let Z := crossingCommonCandidates S i F P Q x y
    ∃ f : (↥Z × Bool) ↪ CyclicEdgeSlot (V := CrossingPart S i) crossingNext,
      ∀ e : ↥Z × Bool,
        let out := if e.2 then y else x
        let arc := crossingArcSlotEmbedding S i (f e)
        ((arc.1 = out ∧ arc.2 = e.1.1) ∨ (arc.1 = e.1.1 ∧ arc.2 = out)) ∧
          tripartiteArc F P Q arc.1 arc.2 := by
  dsimp only
  let Z := crossingCommonCandidates S i F P Q x y
  let orient (z : ↥Z) (b : Bool) :=
    decide (tripartiteArc F P Q (if b then y else x) z.1)
  have hArc (e : ↥Z × Bool) :
      let out := if e.2 then y else x
      if orient e.1 e.2 then tripartiteArc F P Q out e.1.1 else tripartiteArc F P Q e.1.1 out := by
    rcases e with ⟨z,b⟩
    have hz := (mem_filter.mp z.2).2
    cases b
    · by_cases h : tripartiteArc F P Q x z.1
      · simp [orient,h]
      · have h' := hz.1.resolve_left h
        simpa [orient,h] using h'
    · by_cases h : tripartiteArc F P Q y z.1
      · simp [orient,h]
      · have h' := hz.2.resolve_left h
        simpa [orient,h] using h'
  obtain ⟨f,hf⟩ := exists_common_neighbor_crossing_slots S i F P Q Z x y hxy hx hy
    (filter_subset _ _) orient hArc
  refine ⟨f,fun e => ?_⟩
  dsimp only at *
  have h := hArc e
  rw [hf]
  cases hb : orient e.1 e.2
  · simp only [hb,Bool.false_eq_true,ite_false] at h ⊢
    exact ⟨Or.inr ⟨trivial,trivial⟩,h⟩
  · simp only [hb,ite_true] at h ⊢
    exact ⟨Or.inl ⟨trivial,trivial⟩,h⟩

/-- There are at most 16n² ordered pairs of outer vertices to test. -/
theorem crossing_outer_pair_test_budget
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) (hi : i ≤ l)
    (hm : 0 < m) (hk : (k:ℝ) ≤ (3/2)*(m:ℝ))
    (hn : 1 ≤ nestedCoreSize ρ m i) :
    let X := S.vertices i \ S.vertices (i+1)
    (Fintype.card (↥X × ↥X) : ℝ) ≤ 16*(nestedCoreSize ρ m i : ℝ)^2 := by
  dsimp only
  have hX : (S.vertices i \ S.vertices (i+1)).card ≤ 4*nestedCoreSize ρ m i :=
    (card_le_card sdiff_subset).trans (S.vertices_card_le hm hk i hi hn)
  rw [Fintype.card_prod,Fintype.card_coe,Nat.cast_mul]
  have hr : ((S.vertices i \ S.vertices (i+1)).card : ℝ) ≤ 4*nestedCoreSize ρ m i := by
    exact_mod_cast hX
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) _) hr 2
  nlinarith only [hsq]


/-- Neighborhoods restricted to an inner part or to its protected
subset can be indexed by actual edges of the same reserve. -/
theorem exists_slots_for_outer_neighborhood
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (x : TripartiteVertex A B W) (hx : x ∈ S.vertices i \ S.vertices (i+1))
    (Z : Finset (TripartiteVertex A B W)) (hZ : Z ⊆ S.vertices (i+1)) :
    let N := Z.filter (tripartiteAdjacent F P Q x)
    ∃ f : ↥N ↪ CyclicEdgeSlot (V := CrossingPart S i) crossingNext,
      ∀ z : N, let arc := crossingArcSlotEmbedding S i (f z)
        ((arc.1=x ∧ arc.2=z.1) ∨ (arc.1=z.1 ∧ arc.2=x)) ∧ tripartiteArc F P Q arc.1 arc.2 := by
  dsimp only
  let N := Z.filter (tripartiteAdjacent F P Q x)
  let f : ↥N ↪ (TripartiteVertex A B W × TripartiteVertex A B W) :=
    ⟨fun z => if tripartiteArc F P Q x z.1 then (x,z.1) else (z.1,x),by
      intro z w he
      have hz : z.1 ≠ x := fun h => (mem_sdiff.mp hx).2 (h ▸ hZ (mem_filter.mp z.2).1)
      have hw : w.1 ≠ x := fun h => (mem_sdiff.mp hx).2 (h ▸ hZ (mem_filter.mp w.2).1)
      by_cases hf : tripartiteArc F P Q x z.1 <;> by_cases hg : tripartiteArc F P Q x w.1 <;>
        simp only [hf,hg,ite_true,ite_false,Prod.mk.injEq,Subtype.ext_iff] at he ⊢ <;> grind⟩
  have hDef (z : N) : f z = if tripartiteArc F P Q x z.1 then (x,z.1) else (z.1,x) := rfl
  have hPairs (z : N) : ((f z).1=x ∧ (f z).2=z.1) ∨ ((f z).1=z.1 ∧ (f z).2=x) := by
    by_cases h : tripartiteArc F P Q x z.1 <;> simp [hDef,h]
  have hArc (z : N) : tripartiteArc F P Q (f z).1 (f z).2 := by
    have hz := (mem_filter.mp z.2).2
    by_cases h : tripartiteArc F P Q x z.1
    · simp [hDef,h]
    · simpa [hDef,h] using hz.resolve_left h
  have hRange (z : N) : f z ∈ Set.range (crossingArcSlotEmbedding S i) := by
    have hi := hZ (mem_filter.mp z.2).1
    have hc : CrossesNestedPrefix S i (f z).1 (f z).2 := by
      rcases hPairs z with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · rw [ha,hb]
        exact Or.inr ⟨hx,hi⟩
      · rw [ha,hb]
        exact Or.inl ⟨hi,hx⟩
    exact crossing_arc_mem_slot_range S i F P Q (hArc z) hc
  obtain ⟨g,hg⟩ := exists_lift_to_crossing_arc_slots S i f hRange
  refine ⟨g,fun z => ?_⟩
  rw [hg]
  exact ⟨hPairs z,hArc z⟩


/-- The neighborhood and its good subset are measured on reserve arcs
via the same injective index. This transfers the deterministic margin
of (R4) into the two means in the common sample. -/
theorem mapped_reserve_neighborhood_mean {X I : Type*} [Fintype X] [Fintype I]
    (p : I → ℝ) (U : Finset X) (f : ↥U ↪ I) (Good : X → Prop)
    {μ η₀ : ℝ} (hU : U.Nonempty)
    (hμ : 0 < μ) (hη₀ : 0 < η₀) (hη₀small : η₀ ≤ 1/40)
    (hp : ∀ z : U, |p (f z)-μ| ≤ μ*η₀/100)
    (hGood : (1/2+20*η₀)*(U.card : ℝ) ≤ (U.filter Good).card) :
    (1/2+19*η₀)*mean p ((univ : Finset ↥U).map f) <
      mean p ((univ.filter (fun z : U => Good z.1)).map f) := by
  let S := (univ : Finset ↥U).map f
  let T := (univ.filter (fun z : U => Good z.1)).map f
  have hS : S.card = U.card := by simp [S]
  have hT : T.card = (U.filter Good).card := by
    unfold T
    rw [card_map,DenseHall.subtype_filter_card]
  have hS₀ : S.Nonempty := card_pos.mp (by rw [hS]; exact hU.card_pos)
  have hSub : T ⊆ S := map_subset_map.mpr (filter_subset _ _)
  apply reserve_neighborhood_mean_ratio p S T hS₀ hSub hμ hη₀ hη₀small
  · intro e he
    obtain ⟨z,_,rfl⟩ := mem_map.mp he
    exact hp z
  · rw [hS,hT]
    exact hGood

end OverfullWork.ChenShan
