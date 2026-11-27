module

public import OverfullWork.ChenShanCoverDownMatchingTriangles
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

universe u
variable {V : Type u}

private noncomputable def innerShore (U F : Finset V) : Finset ↥U :=
  F.subtype (· ∈ U)

private noncomputable def innerShoreEquiv (U F : Finset V) (hF : F ⊆ U) :
    ↥(innerShore U F) ≃ ↥F where
  toFun a := ⟨a.val.val,mem_subtype.mp a.property⟩
  invFun a := ⟨⟨a.val,hF a.property⟩,mem_subtype.mpr a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem innerShore_filter_card (U F : Finset V) (hF : F ⊆ U) (P : V → Prop) :
    ((innerShore U F).filter (fun a => P a.val)).card = (F.filter P).card := by
  have hEq : (innerShore U F).filter (fun a => P a.val) = innerShore U (F.filter P) := by
    ext a
    simp only [innerShore,mem_filter,mem_subtype]
  rw [hEq,← card_map (Function.Embedding.subtype (· ∈ U))]
  exact congrArg card (subtype_map_of_mem (fun a ha => hF (mem_filter.mp ha).1))

/-- Match on the finite interior support, then return the matchings to
the ambient graph. Only the order of the interior enters Lemma 4.14. -/
theorem exists_cover_down_matchings_on_interior
    (b : ℕ) (hb : 0 < b) (density η : ℝ) (hdensity : 0 < density) (hDensityOne : density ≤ 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ (V J : Type u) [Fintype J] (U : Finset V) (E : V → V → Prop) (F G : J → Finset V),
    U.card ≤ 3*n → Fintype.card J ≤ 3*b*n →
    (∀ j, F j ⊆ U ∧ G j ⊆ U) →
    (∀ j, (F j).card = (G j).card) → (∀ j, Disjoint (F j) (G j)) →
    (∀ j, 81*b*density^(3/2:ℝ)*n ≤ η*(F j).card) →
    (∀ j, ∀ x ∈ F j, (1/2+η)*((G j).card : ℝ) ≤ ((G j).filter (E x)).card) →
    (∀ j, ∀ y ∈ G j, (1/2+η)*((F j).card : ℝ) ≤ ((F j).filter (fun x => E x y)).card) →
    (∀ i j, i ≠ j → (((F i ∪ G i) ∩ (F j ∪ G j)).card : ℝ) ≤ 6*density^2*n) →
    (∀ v, ((univ.filter (fun j => v ∈ F j ∪ G j)).card : ℝ) ≤ 2*b*density*n) →
    ∃ f : ∀ j, ↥(F j) ≃ ↥(G j),
      (∀ j, ∀ x : ↥(F j), E x.val (f j x).val) ∧
      ∀ i j, i ≠ j → Disjoint (directedMatchingArcs (f i)) (directedMatchingArcs (f j)) := by
  obtain ⟨n₀,hPack⟩ := exists_cover_down_shore_matchings.{u} b hb density η hdensity hDensityOne
  refine ⟨n₀,?_⟩
  intro n hn V J _ U E F G hU hJ hSub hSize hDisj hMargin hLeft hRight hOverlap hLoad
  let F' (j : J) := innerShore U (F j)
  let G' (j : J) := innerShore U (G j)
  let E' (a b : ↥U) := E a.val b.val
  let up : ↥U ↪ V := Function.Embedding.subtype _
  have hMapF j : (F' j).map up = F j := subtype_map_of_mem (hSub j).1
  have hMapG j : (G' j).map up = G j := subtype_map_of_mem (hSub j).2
  have hCardF j : (F' j).card = (F j).card := by rw [← hMapF j, card_map]
  have hCardG j : (G' j).card = (G j).card := by rw [← hMapG j, card_map]
  have hDisj' j : Disjoint (F' j) (G' j) := by
    apply disjoint_left.mpr
    intro a ha hb
    exact disjoint_left.mp (hDisj j) (mem_subtype.mp ha) (mem_subtype.mp hb)
  have hOverlap' i j (hne : i ≠ j) :
      ((((F' i ∪ G' i) ∩ (F' j ∪ G' j))).card : ℝ) ≤ 6*density^2*n := by
    have heq : ((((F' i ∪ G' i) ∩ (F' j ∪ G' j))).map up) =
        (F i ∪ G i) ∩ (F j ∪ G j) := by
      rw [Finset.map_inter,Finset.map_union,Finset.map_union,hMapF,hMapF,hMapG,hMapG]
    have h := hOverlap i j hne
    rw [← heq,card_map] at h
    exact h
  have hLoad' (v : ↥U) : ((univ.filter (fun j => v ∈ F' j ∪ G' j)).card : ℝ) ≤ 2*b*density*n := by
    have heq : univ.filter (fun j => v ∈ F' j ∪ G' j) =
        univ.filter (fun j => v.val ∈ F j ∪ G j) := by
      ext j
      simp only [F',G',innerShore,mem_filter,mem_union,mem_subtype]
    rw [heq]
    exact hLoad v.val
  obtain ⟨M,hM,hPair⟩ := hPack n hn ↥U J E' F' G'
    (by simpa only [Fintype.card_coe] using hU) hJ
    (fun j => (hCardF j).trans ((hSize j).trans (hCardG j).symm)) hDisj'
    (by intro j; rw [hCardF]; exact hMargin j)
    (by
      intro j x hx
      have hh := innerShore_filter_card U (G j) (hSub j).2 (E x.val)
      rw [hCardG,hh]
      exact hLeft j x.val (mem_subtype.mp hx))
    (by
      intro j y hy
      have hh := innerShore_filter_card U (F j) (hSub j).1 (fun x => E x y.val)
      rw [hCardF,hh]
      exact hRight j y.val (mem_subtype.mp hy))
    (by
      intro i j hne
      have h := hOverlap' i j hne
      convert h using 1
      congr 2
      ext a
      simp only [mem_inter,mem_union])
    (by
      intro v
      have h := hLoad' v
      convert h using 1 <;> congr 2 <;> ext j <;> simp only [mem_filter,mem_union])
  choose f hf hEdge using hM
  let eF (j : J) := innerShoreEquiv U (F j) (hSub j).1
  let eG (j : J) := innerShoreEquiv U (G j) (hSub j).2
  let g (j : J) := ((eF j).symm.trans (f j)).trans (eG j)
  refine ⟨g,?_,?_⟩
  · intro j a
    exact hEdge j ((eF j).symm a)
  · intro i j hij
    have hSubMatch (j : J) : directedMatchingArcs (g j) ⊆ (M j).map (up.prodMap up) := by
      intro e he
      obtain ⟨a,rfl⟩ := (mem_directedMatchingArcs (g j) e).mp he
      let a' := (eF j).symm a
      let b' := f j a'
      have hMem : (a'.val,b'.val) ∈ M j := by
        rw [hf j]
        exact (mem_matchingArcs (f j) _ _).mpr ⟨a',Or.inl ⟨rfl,rfl⟩⟩
      exact mem_map.mpr ⟨_,hMem,rfl⟩
    exact ((disjoint_map (up.prodMap up)).mpr (hPair i j hij)).mono (hSubMatch i) (hSubMatch j)

/-- Finish the matching phase of a round. The matchings use only
unprotected interior arcs, and the resulting triangles leave a locally
balanced interior with the stated degree budget and protected edges. -/
theorem exists_cover_down_round_end
    (b : ℕ) (hb : 0 < b) (density η : ℝ) (hdensity : 0 < density) (hOne : density ≤ 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ (V : Type u) [Fintype V] (U X K : Finset V) (GU R : Finset (V × V)) (bound : ℝ),
    let F := fun x : ↥X => arcOutNeighbors R x.val
    let G := fun x : ↥X => arcInNeighbors R x.val
    let H := GU \ (K ×ˢ K)
    U.card ≤ 3*n → X.card ≤ 3*b*n → K ⊆ U → Disjoint X U →
    GU ⊆ U ×ˢ U →
    (∀ e ∈ R, (e.1 ∈ X ∧ e.2 ∈ U) ∨ (e.1 ∈ U ∧ e.2 ∈ X)) →
    (∀ a c, (a,c) ∈ R → (c,a) ∉ R) →
    ArcBalanced (GU ∪ R) →
    (∀ j, 81*b*density^(3/2:ℝ)*n ≤ η*(F j).card) →
    (∀ j, ∀ x ∈ F j, (1/2+η)*((G j).card : ℝ) ≤
      ((G j).filter (fun y => (x,y) ∈ H)).card) →
    (∀ j, ∀ y ∈ G j, (1/2+η)*((F j).card : ℝ) ≤
      ((F j).filter (fun x => (x,y) ∈ H)).card) →
    (∀ i j, i ≠ j → (((F i ∪ G i) ∩ (F j ∪ G j)).card : ℝ) ≤ 6*density^2*n) →
    (∀ v, ((univ.filter (fun j : ↥X => v ∈ F j ∪ G j)).card : ℝ) ≤ bound) →
    bound ≤ 2*b*density*n →
    ∃ T : Finset (Finset (V × V)), ∃ M : Finset (V × V),
      (↑T : Set (Finset (V × V))).PairwiseDisjoint id ∧
      coveredEdges T = R ∪ M ∧ M ⊆ H ∧
      (∀ v, (incidentDegree M v : ℝ) ≤ bound) ∧
      ArcBalanced (GU \ M) ∧
      (GU \ M) ∩ (K ×ˢ K) = GU ∩ (K ×ˢ K) := by
  obtain ⟨n₀,hPack⟩ := exists_cover_down_matchings_on_interior.{u} b hb density η hdensity hOne
  refine ⟨n₀,?_⟩
  intro n hn V _ U X K GU R bound F G H hU hX hK hXU hGU hCross hAsymm hBal
    hMargin hLeft hRight hOverlap hLoad hB
  have hout (x : ↥X) : x.val ∉ U := fun h => disjoint_left.mp hXU x.property h
  have hSub (x : ↥X) : F x ⊆ U ∧ G x ⊆ U := by
    constructor
    · intro y hy
      exact ((hCross (x.val,y) (mem_arcOutNeighbors.mp hy)).resolve_right
        (fun h => hout x h.1)).2
    · intro y hy
      exact ((hCross (y,x.val) (mem_arcInNeighbors.mp hy)).resolve_left
        (fun h => hout x h.2)).1
  have hDisj (x : ↥X) : Disjoint (F x) (G x) := by
    apply disjoint_left.mpr
    intro y hy hy'
    exact hAsymm _ _ (mem_arcOutNeighbors.mp hy) (mem_arcInNeighbors.mp hy')
  have hCount (x : ↥X) : (F x).card = (G x).card :=
    cover_down_exterior_out_in_card U GU R hGU hBal x.val (hout x)
  have hXR (e) (he : e ∈ R) : (e.1 ∈ X ∨ e.2 ∈ X) ∧ ¬(e.1 ∈ X ∧ e.2 ∈ X) := by
    rcases hCross e he with h | h
    · exact ⟨Or.inl h.1,fun h' => disjoint_left.mp hXU h'.2 h.2⟩
    · exact ⟨Or.inr h.2,fun h' => disjoint_left.mp hXU h'.1 h.1⟩
  have hRDisj : Disjoint R GU := by
    apply disjoint_left.mpr
    intro e hr hg
    obtain ⟨h₁,h₂⟩ := mem_product.mp (hGU hg)
    exact (hXR e hr).1.elim (fun h => disjoint_left.mp hXU h h₁)
      (fun h => disjoint_left.mp hXU h h₂)
  obtain ⟨f,hf,hPair⟩ := hPack n hn V ↥X U (fun a c => (a,c) ∈ H) F G hU
    (by simpa only [Fintype.card_coe] using hX) hSub hCount hDisj hMargin
    (by intro j x hx; convert hLeft j x hx using 1; congr 4)
    (by intro j y hy; convert hRight j y hy using 1; congr 4)
    hOverlap (fun v => (hLoad v).trans hB)
  have hInside (x : ↥X) : directedMatchingArcs (f x) ⊆ H := by
    intro e he
    obtain ⟨a,rfl⟩ := (mem_directedMatchingArcs (f x) e).mp he
    exact hf x a
  have hProtect (x : ↥X) : Disjoint (directedMatchingArcs (f x)) (K ×ˢ K) := by
    apply disjoint_left.mpr
    intro e he hk
    exact (mem_sdiff.mp (hInside x he)).2 hk
  let T := (univ : Finset ↥X).biUnion (fun x => matchingStarTriangles x.val (f x))
  let M := (univ : Finset ↥X).biUnion (fun x => directedMatchingArcs (f x))
  have hM : M ⊆ H := by
    intro e he
    obtain ⟨x,_,hx⟩ := mem_biUnion.mp he
    exact hInside x hx
  have ⟨hT,hCov,_,hPr,hBudget,hNext⟩ := matching_stars_cover_round X GU R F G f
    (fun _ => rfl) (fun _ => rfl)
    (fun x hx => hout x ((hSub x).1 hx)) (fun x hx => hout x ((hSub x).2 hx))
    hDisj hXR hRDisj hBal (fun x => (hInside x).trans sdiff_subset) hPair K hProtect bound hLoad
  refine ⟨T,M,hT,hCov,hM,hBudget,hNext,?_⟩
  ext e
  have he : e ∈ K ×ˢ K → e ∉ M := fun hk hm => disjoint_left.mp hPr hm hk
  simp only [mem_inter,mem_sdiff]
  tauto

end OverfullWork.ChenShan
