module

public import OverfullWork.ChenShanCoverDownMatchingInput
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {V : Type*}

noncomputable def directedMatchingArcs {F G : Finset V} (f : ↥F ≃ ↥G) : Finset (V × V) :=
  univ.image (fun a : ↥F => (a.val,(f a).val))

@[simp] theorem mem_directedMatchingArcs {F G : Finset V} (f : ↥F ≃ ↥G) (e : V × V) :
    e ∈ directedMatchingArcs f ↔ ∃ a : ↥F, (a.val,(f a).val) = e := by
  simp only [directedMatchingArcs,mem_image,mem_univ,true_and]

noncomputable def matchingStarTriangles {F G : Finset V} (u : V) (f : ↥F ≃ ↥G) :
    Finset (Finset (V × V)) :=
  univ.image (fun a : ↥F => exteriorTriangle (u,a.val) (f a).val)

private theorem matching_star_triangles_disjoint {F G : Finset V} (u : V) (f : ↥F ≃ ↥G)
    (hF : u ∉ F) (hG : u ∉ G) (a b : ↥F) (hne : a ≠ b) :
    Disjoint (exteriorTriangle (u,a.val) (f a).val)
      (exteriorTriangle (u,b.val) (f b).val) := by
  have ha : a.val ≠ u := fun h => hF (h ▸ a.property)
  have hb : b.val ≠ u := fun h => hF (h ▸ b.property)
  have hc : (f a).val ≠ u := fun h => hG (h ▸ (f a).property)
  have hd : (f b).val ≠ u := fun h => hG (h ▸ (f b).property)
  have h₁ : a.val ≠ b.val := fun h => hne (Subtype.ext h)
  have h₂ : (f a).val ≠ (f b).val := fun h => hne (f.injective (Subtype.ext h))
  apply disjoint_left.mpr
  intro e he he'
  simp only [exteriorTriangle,exteriorReserveArcs,mem_insert,mem_singleton] at he he'
  rcases he with rfl | rfl | rfl <;>
    simp_all [Prod.mk.injEq,Ne.symm hb,Ne.symm hd]

/-- One perfect matching gives an exact triangle decomposition of its
oriented matching edges and the entire crossing star at the exterior vertex. -/
theorem matching_star_covers_exactly [Fintype V]
    (R : Finset (V × V)) (u : V) {F G : Finset V} (f : ↥F ≃ ↥G)
    (hF : F = arcOutNeighbors R u) (hG : G = arcInNeighbors R u)
    (huF : u ∉ F) (huG : u ∉ G) (hDisj : Disjoint F G) :
    let T := matchingStarTriangles u f
    let M := directedMatchingArcs f
    (↑T : Set (Finset (V × V))).PairwiseDisjoint id ∧
    ArcBalanced (coveredEdges T) ∧
    coveredEdges T = (R.filter (touches u)) ∪ M := by
  let T := matchingStarTriangles u f
  let M := directedMatchingArcs f
  have hPair : (↑T : Set (Finset (V × V))).PairwiseDisjoint id := by
    intro A hA B hB hne
    obtain ⟨a,_,rfl⟩ := mem_image.mp hA
    obtain ⟨b,_,rfl⟩ := mem_image.mp hB
    exact matching_star_triangles_disjoint u f huF huG a b (fun h => hne (h ▸ rfl))
  have hBal : ArcBalanced (coveredEdges T) := by
    apply arcBalanced_coveredEdges _ hPair
    intro A hA
    obtain ⟨a,_,rfl⟩ := mem_image.mp hA
    apply exteriorTriangle_balanced
    · intro h
      change u = a.val at h
      exact huF (by rw [h]; exact a.property)
    · intro h
      change u = (f a).val at h
      exact huG (by rw [h]; exact (f a).property)
    · intro h
      change a.val = (f a).val at h
      exact disjoint_left.mp hDisj a.property (by rw [h]; exact (f a).property)
  have hOut (a : V) (ha : a ∈ F) : (u,a) ∈ R := by
    rwa [hF,mem_arcOutNeighbors] at ha
  have hIn (b : V) (hb : b ∈ G) : (b,u) ∈ R := by
    rwa [hG,mem_arcInNeighbors] at hb
  refine ⟨hPair,hBal,?_⟩
  ext e
  constructor
  · intro he
    obtain ⟨S,hS,he⟩ := mem_coveredEdges.mp he
    obtain ⟨a,_,rfl⟩ := mem_image.mp hS
    have hFa := hOut a.val a.property
    have hGa := hIn (f a).val (f a).property
    simp only [exteriorTriangle,exteriorReserveArcs,mem_insert,mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact mem_union_left _ (mem_filter.mpr ⟨hFa,Or.inl rfl⟩)
    · exact mem_union_right _ ((mem_directedMatchingArcs f _).mpr ⟨a,rfl⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hGa,Or.inr rfl⟩)
  · intro he
    have hMem (a : ↥F) : exteriorTriangle (u,a.val) (f a).val ∈ T :=
      mem_image.mpr ⟨a,mem_univ _,rfl⟩
    rcases mem_union.mp he with he | he
    · obtain ⟨he,ht⟩ := mem_filter.mp he
      rcases ht with hf | hg
      · have ha : e.2 ∈ F := by
          rw [hF,mem_arcOutNeighbors,← hf,Prod.eta]
          exact he
        let a : ↥F := ⟨e.2,ha⟩
        have heq : e = (u,a.val) := Prod.ext hf rfl
        exact mem_coveredEdges.mpr ⟨_,hMem a,mem_insert.mpr (Or.inl heq)⟩
      · have hb : e.1 ∈ G := by
          rw [hG,mem_arcInNeighbors,← hg,Prod.eta]
          exact he
        let b : ↥G := ⟨e.1,hb⟩
        let a := f.symm b
        have hEq : f a = b := f.apply_symm_apply b
        have heq : e = ((f a).val,u) := Prod.ext (congrArg Subtype.val hEq).symm hg
        exact mem_coveredEdges.mpr ⟨_,hMem a,mem_insert.mpr
          (Or.inr (mem_insert.mpr (Or.inr (mem_singleton.mpr heq))))⟩
    · obtain ⟨a,ha⟩ := (mem_directedMatchingArcs f e).mp he
      exact mem_coveredEdges.mpr ⟨_,hMem a,mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inl ha.symm)))⟩

/-- A matching contributes at most one incident arc at each vertex,
and contributes zero away from its two shores. -/
theorem directedMatchingArcs_degree {F G : Finset V} (f : ↥F ≃ ↥G)
    (hDisj : Disjoint F G) (v : V) :
    incidentDegree (directedMatchingArcs f) v ≤ if v ∈ F ∪ G then 1 else 0 := by
  unfold incidentDegree
  by_cases hv : v ∈ F ∪ G
  · rw [ite_eq_left hv]
    apply card_le_one.mpr
    intro e he e' he'
    obtain ⟨ha,ha'⟩ := mem_filter.mp he
    obtain ⟨hb,hb'⟩ := mem_filter.mp he'
    obtain ⟨a,rfl⟩ := (mem_directedMatchingArcs f e).mp ha
    obtain ⟨b,rfl⟩ := (mem_directedMatchingArcs f e').mp hb
    simp only at ha' hb'
    rcases ha' with h | h <;> rcases hb' with h' | h'
    · have heq : a = b := Subtype.ext (h.trans h'.symm)
      rw [heq]
    · exact False.elim (disjoint_left.mp hDisj (h ▸ a.property) (h' ▸ (f b).property))
    · exact False.elim (disjoint_left.mp hDisj (h' ▸ b.property) (h ▸ (f a).property))
    · have heq : a = b := f.injective (Subtype.ext (h.trans h'.symm))
      rw [heq]
  · rw [ite_eq_right hv,Nat.le_zero,card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨ha,ha'⟩ := mem_filter.mp he
    obtain ⟨a,rfl⟩ := (mem_directedMatchingArcs f e).mp ha
    rcases ha' with h | h
    · exact hv (mem_union_left _ (h ▸ a.property))
    · exact hv (mem_union_right _ (h ▸ (f a).property))

/-- Glue the matching triangles at all exterior vertices. Their edges
are exactly the updated crossing reserve and the interior matching
arcs, and their removal preserves the remaining graph's balance. -/
theorem matching_stars_cover_round [Fintype V]
    (X : Finset V) (GU R : Finset (V × V)) (F G : ↥X → Finset V)
    (f : ∀ x : ↥X, ↥(F x) ≃ ↥(G x))
    (hF : ∀ x : ↥X, F x = arcOutNeighbors R x.val)
    (hG : ∀ x : ↥X, G x = arcInNeighbors R x.val)
    (hNoF : ∀ x : ↥X, x.val ∉ F x) (hNoG : ∀ x : ↥X, x.val ∉ G x)
    (hDisj : ∀ x : ↥X, Disjoint (F x) (G x))
    (hR : ∀ e ∈ R, (e.1 ∈ X ∨ e.2 ∈ X) ∧ ¬(e.1 ∈ X ∧ e.2 ∈ X))
    (hRGU : Disjoint R GU) (hBal : ArcBalanced (GU ∪ R))
    (hInside : ∀ x : ↥X, directedMatchingArcs (f x) ⊆ GU)
    (hMatch : ∀ x y : ↥X, x ≠ y →
      Disjoint (directedMatchingArcs (f x)) (directedMatchingArcs (f y)))
    (K : Finset V) (hProtect : ∀ x : ↥X, Disjoint (directedMatchingArcs (f x)) (K ×ˢ K))
    (bound : ℝ) (hLoad : ∀ v, ((univ.filter (fun x : ↥X => v ∈ F x ∪ G x)).card : ℝ) ≤ bound) :
    let T := (univ : Finset ↥X).biUnion (fun x => matchingStarTriangles x.val (f x))
    let M := (univ : Finset ↥X).biUnion (fun x => directedMatchingArcs (f x))
    (↑T : Set (Finset (V × V))).PairwiseDisjoint id ∧
    coveredEdges T = R ∪ M ∧ M ⊆ GU ∧ Disjoint M (K ×ˢ K) ∧
    (∀ v, (incidentDegree M v : ℝ) ≤ bound) ∧ ArcBalanced (GU \ M) := by
  intro T M
  let stars (x : ↥X) := matchingStarTriangles x.val (f x)
  let matchedArcs (x : ↥X) := directedMatchingArcs (f x)
  have hLocal (x : ↥X) :=
    matching_star_covers_exactly R x.val (f x) (hF x) (hG x) (hNoF x) (hNoG x) (hDisj x)
  have hSeparated (x y : ↥X) (hne : x ≠ y) :
      Disjoint (coveredEdges (stars x)) (coveredEdges (stars y)) := by
    apply disjoint_left.mpr
    intro e hx hy
    rw [(hLocal x).2.2] at hx
    rw [(hLocal y).2.2] at hy
    rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
    · obtain ⟨hr,hx'⟩ := mem_filter.mp hx
      have hy' := (mem_filter.mp hy).2
      rcases hx' with h | h <;> rcases hy' with h' | h'
      · exact hne (Subtype.ext (h.symm.trans h'))
      · exact (hR e hr).2 ⟨h.symm ▸ x.property,h'.symm ▸ y.property⟩
      · exact (hR e hr).2 ⟨h'.symm ▸ y.property,h.symm ▸ x.property⟩
      · exact hne (Subtype.ext (h.symm.trans h'))
    · exact disjoint_left.mp hRGU (mem_filter.mp hx).1 (hInside y hy)
    · exact disjoint_left.mp hRGU (mem_filter.mp hy).1 (hInside x hx)
    · exact disjoint_left.mp (hMatch x y hne) hx hy
  have hPair : (↑T : Set (Finset (V × V))).PairwiseDisjoint id := by
    intro P hP Q hQ hne
    obtain ⟨u,_,hu⟩ := mem_biUnion.mp hP
    obtain ⟨v,_,hv⟩ := mem_biUnion.mp hQ
    by_cases heq : u = v
    · subst v
      exact (hLocal u).1 hu hv hne
    · apply disjoint_left.mpr
      intro e he he'
      exact disjoint_left.mp (hSeparated u v heq)
        (mem_coveredEdges.mpr ⟨P,hu,he⟩) (mem_coveredEdges.mpr ⟨Q,hv,he'⟩)
  have hCov : coveredEdges T = R ∪ M := by
    ext e
    have hMem : e ∈ coveredEdges T ↔ ∃ x : ↥X, e ∈ coveredEdges (stars x) := by
      constructor
      · intro he
        obtain ⟨P,hP,h⟩ := mem_coveredEdges.mp he
        obtain ⟨x,_,hx⟩ := mem_biUnion.mp hP
        exact ⟨x,mem_coveredEdges.mpr ⟨P,hx,h⟩⟩
      · rintro ⟨x,hx⟩
        obtain ⟨P,hP,h⟩ := mem_coveredEdges.mp hx
        exact mem_coveredEdges.mpr ⟨P,mem_biUnion.mpr ⟨x,mem_univ _,hP⟩,h⟩
    rw [hMem]
    constructor
    · rintro ⟨x,hx⟩
      rw [(hLocal x).2.2] at hx
      exact (mem_union.mp hx).elim (fun h => mem_union_left _ (mem_filter.mp h).1)
        (fun h => mem_union_right _ (mem_biUnion.mpr ⟨x,mem_univ _,h⟩))
    · intro he
      rcases mem_union.mp he with he | he
      · rcases (hR e he).1 with h | h
        · refine ⟨⟨e.1,h⟩,?_⟩
          rw [(hLocal ⟨e.1,h⟩).2.2]
          exact mem_union_left _ (mem_filter.mpr ⟨he,Or.inl rfl⟩)
        · refine ⟨⟨e.2,h⟩,?_⟩
          rw [(hLocal ⟨e.2,h⟩).2.2]
          exact mem_union_left _ (mem_filter.mpr ⟨he,Or.inr rfl⟩)
      · obtain ⟨x,_,hx⟩ := mem_biUnion.mp he
        refine ⟨x,?_⟩
        rw [(hLocal x).2.2]
        exact mem_union_right _ hx
  have hM : M ⊆ GU := by
    intro e he
    obtain ⟨x,_,hx⟩ := mem_biUnion.mp he
    exact hInside x hx
  have hPr : Disjoint M (K ×ˢ K) := by
    apply disjoint_left.mpr
    intro e he hk
    obtain ⟨x,_,hx⟩ := mem_biUnion.mp he
    exact disjoint_left.mp (hProtect x) hx hk
  have hBound (v : V) : (incidentDegree M v : ℝ) ≤ bound := by
    have hFiltered : M.filter (touches v) =
        (univ : Finset ↥X).biUnion (fun x => (matchedArcs x).filter (touches v)) := by
      ext e
      simp only [M,mem_biUnion,mem_filter,mem_univ,true_and]
      constructor
      · rintro ⟨⟨x,hx⟩,he⟩
        exact ⟨x,hx,he⟩
      · rintro ⟨x,hx,he⟩
        exact ⟨⟨x,hx⟩,he⟩
    have h : (M.filter (touches v)).card ≤
        (univ.filter (fun x : ↥X => v ∈ F x ∪ G x)).card := by
      rw [hFiltered,card_filter]
      apply card_biUnion_le.trans
      apply sum_le_sum
      intro x _
      have h := directedMatchingArcs_degree (f x) (hDisj x) v
      unfold incidentDegree at h
      convert h using 1
      congr 2
    unfold incidentDegree
    have h' : ((M.filter (touches v)).card : ℝ) ≤
        ((univ.filter (fun x : ↥X => v ∈ F x ∪ G x)).card : ℝ) := by exact_mod_cast h
    have hh := h'.trans (hLoad v)
    convert hh using 1
    congr 2
    ext e
    simp only [mem_filter,touches]
  have hPacked : ArcBalanced (coveredEdges T) := by
    apply arcBalanced_coveredEdges _ hPair
    intro P hP
    obtain ⟨x,_,hx⟩ := mem_biUnion.mp hP
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    apply exteriorTriangle_balanced
    · intro he
      change x.val = a.val at he
      exact hNoF x (by rw [he]; exact a.property)
    · intro he
      change x.val = (f x a).val at he
      exact hNoG x (by rw [he]; exact (f x a).property)
    · intro he
      change a.val = (f x a).val at he
      exact disjoint_left.mp (hDisj x) a.property (by rw [he]; exact (f x a).property)
  have hDiff : (GU ∪ R) \ coveredEdges T = GU \ M := by
    rw [hCov]
    ext e
    have h₁ : e ∈ GU → e ∉ R := fun hg hr => disjoint_left.mp hRGU hr hg
    simp only [mem_sdiff,mem_union]
    tauto
  have hSub : coveredEdges T ⊆ GU ∪ R := by
    rw [hCov]
    exact union_subset (fun e he => mem_union_right _ he)
      (fun e he => mem_union_left _ (hM he))
  refine ⟨hPair,hCov,hM,hPr,hBound,?_⟩
  rw [← hDiff]
  exact arcBalanced_sdiff hSub hBal hPacked

end OverfullWork.ChenShan
