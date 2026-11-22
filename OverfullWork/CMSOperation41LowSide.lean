module

public import OverfullWork.LowSkeletonPreparation
public import OverfullWork.CleanedSourceVAL

@[expose] public section


/-! In CMS Operation 4.1, an independent cleaned low set supplies the
two prescribed matchings and all representatives of its skeleton. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph PrunedCore RobustExpansion LowVertexMatchingAbsorption
open LowSkeletonPreparation PaperLowSkeleton
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem independent_cut_strict_comparison (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (hInd : G.IsIndepSet (W : Set V))
    (hCompare : ∀ w ∈ W,∀ v,G.Adj w v → neighboursIn G W v < G.degree w)
    (hPos : ∀ w ∈ W,0 < G.degree w) :
    (∀ a : W,0 < (univ.filter fun b : ↥(Wᶜ : Finset V) => G.Adj a.val b.val).card) ∧
    ∀ (a : W) (b : ↥(Wᶜ : Finset V)),G.Adj a.val b.val →
      (univ.filter fun a' : W => G.Adj a'.val b.val).card <
      (univ.filter fun b' : ↥(Wᶜ : Finset V) => G.Adj a.val b'.val).card := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun u v => Classical.propDecidable (G.Adj u v))
  have hRow (a : W) :
      (univ.filter fun b : ↥(Wᶜ : Finset V) => G.Adj a.val b.val).card = G.degree a.val := by
    rw [DenseHall.subtype_filter_card,←card_neighborFinset_eq_degree]
    congr 1
    ext b
    simp only [mem_filter,mem_compl,mem_neighborFinset]
    constructor
    · exact And.right
    · intro hab
      exact ⟨fun hb => hInd a.property hb hab.ne hab,hab⟩
  have hCol (b : ↥(Wᶜ : Finset V)) :
      (univ.filter fun a : W => G.Adj a.val b.val).card = neighboursIn G W b.val := by
    have hCast := DenseHall.subtype_filter_card W (fun a => G.Adj a b.val)
    calc
      _ = (W.filter fun a => G.Adj a b.val).card := by convert hCast using 1
      _ = _ := by
        rw [neighboursIn_eq_filter_card]
        congr 1
        ext a
        simp only [mem_filter,G.adj_comm]
  constructor
  · intro a
    rw [hRow]
    exact hPos a.val a.property
  · intro a b h
    rw [hRow,hCol]
    exact hCompare a.val a.property b.val h

theorem two_matchings_of_strict_independent_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (hInd : G.IsIndepSet (W : Set V))
    (hStrict : ∀ w ∈ W,∀ v,G.Adj w v → neighboursIn G W v < G.degree w)
    (hPos : ∀ w ∈ W,0 < G.degree w) :
    ∃ M₁ M₂ : SimpleGraph V,M₁ ≤ G ∧ M₂ ≤ G ∧
      OneFactor.IsMatchingGraph M₁ ∧ OneFactor.IsMatchingGraph M₂ ∧ Disjoint M₁ M₂ ∧
      (∀ w ∈ W,∃! v,M₁.Adj w v) ∧ (∀ w ∈ W,∃! v,M₂.Adj w v) ∧
      (∀ u v,M₁.Adj u v → (u ∈ W ∧ v ∉ W) ∨ (v ∈ W ∧ u ∉ W)) ∧
      (∀ u v,M₂.Adj u v → (u ∈ W ∧ v ∉ W) ∨ (v ∈ W ∧ u ∉ W)) := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun u v => Classical.propDecidable (G.Adj u v))
  have h := independent_cut_strict_comparison G W hInd hStrict hPos
  exact exists_two_matchings_of_strict_comparison G W h.1 h.2

theorem two_matchings_of_clean_independent_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (hInd : G.IsIndepSet (W : Set V)) (hClean : CleanedSourceVAL.IsReady G W)
    (hPos : ∀ w ∈ W,0 < G.degree w) :
    ∃ M₁ M₂ : SimpleGraph V,M₁ ≤ G ∧ M₂ ≤ G ∧
      OneFactor.IsMatchingGraph M₁ ∧ OneFactor.IsMatchingGraph M₂ ∧ Disjoint M₁ M₂ ∧
      (∀ w ∈ W,∃! v,M₁.Adj w v) ∧ (∀ w ∈ W,∃! v,M₂.Adj w v) ∧
      (∀ u v,M₁.Adj u v → (u ∈ W ∧ v ∉ W) ∨ (v ∈ W ∧ u ∉ W)) ∧
      (∀ u v,M₂.Adj u v → (u ∈ W ∧ v ∉ W) ∨ (v ∈ W ∧ u ∉ W)) :=
  two_matchings_of_strict_independent_cut G W hInd
    (MaximumNeighbourCleanup.hall_of_final_inequality G W hClean.1 hClean.2) hPos

theorem exists_low_skeleton_and_representatives_of_clean_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (W U : Finset V) (hInd : G.IsIndepSet (W : Set V)) (hClean : CleanedSourceVAL.IsReady G W)
    (hPos : ∀ w ∈ W,0 < G.degree w) (hSize : 2 ≤ W.card)
    (hDegree : ∀ u ∈ U,u ∉ W → U.card+4*(W.card+1) ≤ G.degree u) :
    ∃ H : SimpleGraph V, IsSkeleton G H W ∧
      Nonempty (LowSkeletonProjection.Projection G (outerLeaves H W) U (nonisolatedVertices H)) := by
  obtain ⟨M₁,M₂,h₁,h₂,hm₁,hm₂,hDis,hC₁,hC₂,hX₁,hX₂⟩ :=
    two_matchings_of_clean_independent_cut G W hInd hClean hPos
  obtain ⟨H,hH⟩ := exists_skeleton_of_two_matchings G M₁ M₂ W h₁ h₂ hm₁ hm₂ hDis
    hC₁ hC₂ hX₁ hX₂ hSize
  let A := outerLeaves H W
  let Z := nonisolatedVertices H
  have hAZ : A ⊆ Z := by
    intro v hv
    have hOne := (mem_filter.mp hv).2
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have hZ : Z.card ≤ 2*(W.card+1) :=
    (nonisolatedVertices_card_le_twice_edges H).trans (Nat.mul_le_mul_left 2 hH.edge_bound)
  refine ⟨H,hH,LowSkeletonProjection.exists_projection G A U Z ?_⟩
  intro u hu
  obtain ⟨huA,huU⟩ := mem_inter.mp hu
  have huW : u ∉ W := mem_compl.mp (mem_filter.mp huA).1
  have hA := card_le_card hAZ
  have hLower := hDegree u huU huW
  omega

theorem exists_paired_skeleton_representatives {G H : SimpleGraph V} [DecidableRel H.Adj]
    {W U Z : Finset V} (hs : IsSkeleton G H W)
    (P : LowSkeletonProjection.Projection G (outerLeaves H W) U Z) :
    ∃ f : ℕ, 0 < f ∧ 2*f = (outerLeaves H W).card ∧
      ∃ e : (Fin f × Bool) ↪ ↥(Uᶜ : Finset V),
        ∀ v, v ∈ Set.range e ↔ ∃ a : outerLeaves H W,P.representative a = v := by
  obtain ⟨f,hf⟩ := hs.outer_even
  have hCard : Fintype.card (Fin f × Bool) = Fintype.card ↥(outerLeaves H W) := by
    rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_coe,hf]
    omega
  let coordinates := Fintype.equivOfCardEq hCard
  let e : (Fin f × Bool) ↪ ↥(Uᶜ : Finset V) :=
    coordinates.toEmbedding.trans ⟨P.representative,P.injective⟩
  have hf₂ := hs.outer_two_le
  refine ⟨f,by omega,by omega,e,?_⟩
  intro v
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨coordinates i,rfl⟩
  · rintro ⟨a,rfl⟩
    refine ⟨coordinates.symm a,?_⟩
    change P.representative (coordinates (coordinates.symm a)) = P.representative a
    rw [Equiv.apply_symm_apply]


end OverfullWork.CMSTrimmingRound
