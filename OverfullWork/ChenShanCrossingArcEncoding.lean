module

public import OverfullWork.ChenShanCrossingSampling
public import OverfullWork.ChenShanReserveCommonPairs
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

universe u

variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

/-- Distinct classes of the same tripartite part are separated by the
inner-prefix membership test. The other tripartite parts are disjoint
by the sum tags. -/
def crossingVertexEmbedding (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) :
    (Σ j, CrossingPart S i j) ↪ TripartiteVertex A B W where
  toFun v := crossingVertex S i v.1 v.2
  inj' := by
    rintro ⟨j,a⟩ ⟨t,b⟩ h
    revert a b h
    fin_cases j <;> fin_cases t <;> intro a b h <;>
      simp only [crossingVertex,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq] at h
    all_goals first
      | exact congrArg (Sigma.mk _) (Subtype.ext h)
      | exact False.elim ((mem_sdiff.mp b.2).2 (h ▸ a.2))
      | exact False.elim ((mem_sdiff.mp a.2).2 (h.symm ▸ b.2))

/-- Each slot in the cyclic product sample records a unique ordered arc
on the original tripartite vertices. -/
def crossingArcSlotEmbedding (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) :
    CyclicEdgeSlot (V := CrossingPart S i) crossingNext ↪
      (TripartiteVertex A B W × TripartiteVertex A B W) where
  toFun e := (crossingVertex S i e.1 e.2.1, crossingVertex S i (crossingNext e.1) e.2.2)
  inj' := by
    rintro ⟨j,a,b⟩ ⟨t,c,d⟩ h
    let f := crossingVertexEmbedding S i
    have h₁ : (⟨j,a⟩ : Σ j, CrossingPart S i j) = ⟨t,c⟩ :=
      f.injective (congrArg Prod.fst h)
    have h₂ : (⟨crossingNext j,b⟩ : Σ j, CrossingPart S i j) = ⟨crossingNext t,d⟩ :=
      f.injective (congrArg Prod.snd h)
    have hIndex := congrArg Sigma.fst h₁
    dsimp only at hIndex
    subst t
    have hA := eq_of_heq (Sigma.mk.inj_iff.mp h₁).2
    have hB := eq_of_heq (Sigma.mk.inj_iff.mp h₂).2
    rw [hA,hB]

/-- Any family of ambient arcs lying in the crossing slots can be
sampled using coordinates of the same Bernoulli test space. -/
theorem exists_lift_to_crossing_arc_slots
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    {X : Type*} (f : X ↪ (TripartiteVertex A B W × TripartiteVertex A B W))
    (h : ∀ x, f x ∈ Set.range (crossingArcSlotEmbedding S i)) :
    ∃ g : X ↪ CyclicEdgeSlot (V := CrossingPart S i) crossingNext,
      ∀ x, crossingArcSlotEmbedding S i (g x) = f x := by
  let e := crossingArcSlotEmbedding S i
  let q := Equiv.ofInjective e e.injective
  let g (x : X) := q.symm ⟨f x,h x⟩
  have hg (x : X) : e (g x) = f x :=
    congrArg Subtype.val (q.apply_symm_apply ⟨f x,h x⟩)
  exact ⟨⟨g,fun x y he => f.injective ((hg x).symm.trans ((congrArg e he).trans (hg y)))⟩,hg⟩


theorem mem_vertices_left (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (a : A) : Sum.inl a ∈ S.vertices i ↔ a ∈ S.left i := by
  simp [NestedTripartitePrefixes.vertices,mem_map]

theorem mem_vertices_right (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (b : B) : Sum.inr (Sum.inl b) ∈ S.vertices i ↔ b ∈ S.right i := by
  simp [NestedTripartitePrefixes.vertices,mem_map]

theorem mem_vertices_color (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (w : W) : Sum.inr (Sum.inr w) ∈ S.vertices i ↔ w ∈ S.colors i := by
  simp [NestedTripartitePrefixes.vertices,mem_map]

/-- Both endpoints lie in the current level, with exactly one in the
next level. -/
def CrossesNestedPrefix (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) (v w : TripartiteVertex A B W) : Prop :=
  (v ∈ S.vertices (i+1) ∧ w ∈ S.vertices i \ S.vertices (i+1)) ∨
  (v ∈ S.vertices i \ S.vertices (i+1) ∧ w ∈ S.vertices (i+1))

/-- Every actual tripartite arc across the cut is present in the
cyclic product sample space. -/
theorem crossing_arc_mem_slot_range
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    {v w : TripartiteVertex A B W}
    (hArc : tripartiteArc F P Q v w) (hCut : CrossesNestedPrefix S i v w) :
    (v,w) ∈ Set.range (crossingArcSlotEmbedding S i) := by
  rcases v with a | (b | z) <;> rcases w with a' | (b' | z') <;>
    simp only [tripartiteArc] at hArc
  all_goals
    simp only [CrossesNestedPrefix,mem_sdiff,mem_vertices_left,mem_vertices_right,
      mem_vertices_color] at hCut
  · rcases hCut with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact ⟨⟨0,⟨a,ha⟩,⟨b',mem_sdiff.mpr hb⟩⟩,rfl⟩
    · exact ⟨⟨3,⟨a,mem_sdiff.mpr ha⟩,⟨b',hb⟩⟩,rfl⟩
  · rcases hCut with ⟨hb,hz⟩ | ⟨hb,hz⟩
    · exact ⟨⟨4,⟨b,hb⟩,⟨z',mem_sdiff.mpr hz⟩⟩,rfl⟩
    · exact ⟨⟨1,⟨b,mem_sdiff.mpr hb⟩,⟨z',hz⟩⟩,rfl⟩
  · rcases hCut with ⟨hz,ha⟩ | ⟨hz,ha⟩
    · exact ⟨⟨2,⟨z,hz⟩,⟨a',mem_sdiff.mpr ha⟩⟩,rfl⟩
    · exact ⟨⟨5,⟨z,mem_sdiff.mpr hz⟩,⟨a',ha⟩⟩,rfl⟩

theorem crossing_slot_crosses
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (e : CyclicEdgeSlot (V := CrossingPart S i) crossingNext) :
    let a := crossingArcSlotEmbedding S i e
    CrossesNestedPrefix S i a.1 a.2 := by
  rcases e with ⟨j,a,b⟩
  revert a b
  fin_cases j <;> intro a b <;> dsimp only
  · exact Or.inl ⟨(mem_vertices_left S _ _).mpr a.2,
      mem_sdiff.mpr ⟨(mem_vertices_right S _ _).mpr (mem_sdiff.mp b.2).1,
        fun h => (mem_sdiff.mp b.2).2 ((mem_vertices_right S _ _).mp h)⟩⟩
  · exact Or.inr ⟨mem_sdiff.mpr ⟨(mem_vertices_right S _ _).mpr (mem_sdiff.mp a.2).1,
        fun h => (mem_sdiff.mp a.2).2 ((mem_vertices_right S _ _).mp h)⟩,
      (mem_vertices_color S _ _).mpr b.2⟩
  · exact Or.inl ⟨(mem_vertices_color S _ _).mpr a.2,
      mem_sdiff.mpr ⟨(mem_vertices_left S _ _).mpr (mem_sdiff.mp b.2).1,
        fun h => (mem_sdiff.mp b.2).2 ((mem_vertices_left S _ _).mp h)⟩⟩
  · exact Or.inr ⟨mem_sdiff.mpr ⟨(mem_vertices_left S _ _).mpr (mem_sdiff.mp a.2).1,
        fun h => (mem_sdiff.mp a.2).2 ((mem_vertices_left S _ _).mp h)⟩,
      (mem_vertices_right S _ _).mpr b.2⟩
  · exact Or.inl ⟨(mem_vertices_right S _ _).mpr a.2,
      mem_sdiff.mpr ⟨(mem_vertices_color S _ _).mpr (mem_sdiff.mp b.2).1,
        fun h => (mem_sdiff.mp b.2).2 ((mem_vertices_color S _ _).mp h)⟩⟩
  · exact Or.inr ⟨mem_sdiff.mpr ⟨(mem_vertices_color S _ _).mpr (mem_sdiff.mp a.2).1,
        fun h => (mem_sdiff.mp a.2).2 ((mem_vertices_color S _ _).mp h)⟩,
      (mem_vertices_left S _ _).mpr b.2⟩


/-- Common-neighbor tests on inner vertices lift to disjoint pairs of
slots in the original sampling space. -/
theorem exists_common_neighbor_crossing_slots
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (Z : Finset (TripartiteVertex A B W)) (u v : TripartiteVertex A B W)
    (huv : u ≠ v) (hu : u ∈ S.vertices i \ S.vertices (i+1))
    (hv : v ∈ S.vertices i \ S.vertices (i+1)) (hZ : Z ⊆ S.vertices (i+1))
    (orient : ↥Z → Bool → Bool)
    (hArc : ∀ e : ↥Z × Bool,
      let out := if e.2 then v else u
      if orient e.1 e.2 then tripartiteArc F P Q out e.1.1 else tripartiteArc F P Q e.1.1 out) :
    ∃ g : (↥Z × Bool) ↪ CyclicEdgeSlot (V := CrossingPart S i) crossingNext,
      ∀ e : ↥Z × Bool, let out := if e.2 then v else u
        crossingArcSlotEmbedding S i (g e) =
          if orient e.1 e.2 then (out,e.1.1) else (e.1.1,out) := by
  let f := reserveCommonArcPairsWithOrientation Z u v huv
    (fun h => (mem_sdiff.mp hu).2 (hZ h)) (fun h => (mem_sdiff.mp hv).2 (hZ h)) orient
  have hf (e : ↥Z × Bool) : f e ∈ Set.range (crossingArcSlotEmbedding S i) := by
    rcases e with ⟨z,b⟩
    let out := if b then v else u
    have ho : out ∈ S.vertices i \ S.vertices (i+1) := by cases b <;> assumption
    have hz := hZ z.2
    have he := hArc (z,b)
    change (if orient z b then tripartiteArc F P Q out z.1 else tripartiteArc F P Q z.1 out) at he
    change (if orient z b then (out,z.1) else (z.1,out)) ∈ _
    by_cases hb : orient z b = true
    · simp only [hb,ite_true] at he ⊢
      exact crossing_arc_mem_slot_range S i F P Q he (Or.inr ⟨ho,hz⟩)
    · have hb' : orient z b = false := by cases h : orient z b <;> simp_all
      simp only [hb',Bool.false_eq_true,ite_false] at he ⊢
      exact crossing_arc_mem_slot_range S i F P Q he (Or.inl ⟨hz,ho⟩)
  exact exists_lift_to_crossing_arc_slots S i f hf

end OverfullWork.ChenShan
