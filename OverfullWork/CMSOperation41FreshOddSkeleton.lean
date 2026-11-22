module

public import OverfullWork.CMSOperation41LowSide
public import OverfullWork.OddLowSkeletonWitness

@[expose] public section


/-! In odd Case S2.1 the edge from the second matching can be chosen
with its outer endpoint uncovered by the first matching. This keeps
every outer attachment a leaf and retains the actual two matchings. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph PrunedCore LowVertexMatchingAbsorption LowVertexMatchingFlexibility PaperLowSkeleton
open scoped Classical

theorem exists_two_injections_with_fresh_edge {A B : Type*} [Fintype A] [Fintype B]
    (r : A → B → Prop) [DecidableRel r] (a₀ : A) (b₀ : B) (hab : r a₀ b₀)
    (hPos : ∀ a,0 < (univ.filter (r a)).card)
    (hDegree : ∀ a b,r a b → (univ.filter (fun a => r a b)).card < (univ.filter (r a)).card) :
    ∃ f g : A → B,Function.Injective f ∧ Function.Injective g ∧
      (∀ a,r a (f a)) ∧ (∀ a,r a (g a)) ∧ (∀ a,f a ≠ g a) ∧
      (∀ a,f a ≠ b₀) ∧ ∃ a,g a = b₀ := by
  classical
  obtain ⟨f,hf,hfr,hAvoid⟩ := exists_injection_avoiding_vertex_of_strict_degree_comparison
    r hPos hDegree b₀
  obtain ⟨g,hg,hgr,hfg⟩ := exists_second_injection_of_strict_degree_comparison
    r hPos hDegree f hfr
  by_cases hRange : ∃ a,g a = b₀
  · exact ⟨f,g,hf,hg,hfr,hgr,hfg,hAvoid,hRange⟩
  · let g' (a : A) := if a = a₀ then b₀ else g a
    have hInj : Function.Injective g' := by
      intro a b h
      change (if a = a₀ then b₀ else g a) = (if b = a₀ then b₀ else g b) at h
      by_cases ha : a = a₀ <;> by_cases hb : b = a₀
      · exact ha.trans hb.symm
      · rw [if_pos ha,if_neg hb] at h
        exact (hRange ⟨b,h.symm⟩).elim
      · rw [if_neg ha,if_pos hb] at h
        exact (hRange ⟨a,h⟩).elim
      · rw [if_neg ha,if_neg hb] at h
        exact hg h
    refine ⟨f,g',hf,hInj,hfr,?_,?_,hAvoid,⟨a₀,by simp [g']⟩⟩
    · intro a
      by_cases h : a = a₀
      · subst a
        simpa [g'] using hab
      · simpa [g',h] using hgr a
    · intro a
      by_cases h : a = a₀
      · simpa [g',h] using hAvoid a
      · simpa [g',h] using hfg a

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 2000000 in
theorem exists_odd_skeleton_of_clean_independent_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (hInd : G.IsIndepSet (W : Set V))
    (hCompare : ∀ w ∈ W,∀ v,G.Adj w v → neighboursIn G W v < G.degree w)
    (hPos : ∀ w ∈ W,0 < G.degree w) (hThree : 3 ≤ W.card) (hOdd : Odd W.card) :
    ∃ (M₁ M₂ : SimpleGraph V) (w a b : V),M₁ ≤ G ∧ M₂ ≤ G ∧
      OneFactor.IsMatchingGraph M₁ ∧ OneFactor.IsMatchingGraph M₂ ∧ Disjoint M₁ M₂ ∧
      (∀ v ∈ W,∃! u,M₁.Adj v u) ∧ (∀ v ∈ W,∃! u,M₂.Adj v u) ∧
      w ∈ W ∧ M₁.Adj w a ∧ M₂.Adj w b ∧ M₁.degree b = 0 ∧
      IsSkeleton G (M₁ ⊔ edge w b) W ∧
      (∀ v,v ∉ W → (M₁ ⊔ edge w b).degree v ≤ 1) ∧
      (outerLeaves (M₁ ⊔ edge w b) W).card = W.card+1 ∧
      a ∈ outerLeaves (M₁ ⊔ edge w b) W ∧ b ∈ outerLeaves (M₁ ⊔ edge w b) W ∧ a ≠ b := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableRel G.Adj)
    (fun u v => Classical.propDecidable (G.Adj u v))
  obtain ⟨w₀,hw₀⟩ := card_pos.mp (show 0 < W.card by omega)
  obtain ⟨v₀,hv₀⟩ := (G.degree_pos_iff_exists_adj w₀).mp (hPos w₀ hw₀)
  have hvOut : v₀ ∉ W := fun h => hInd hw₀ h hv₀.ne hv₀
  let w' : W := ⟨w₀,hw₀⟩
  let b' : ↥(Wᶜ : Finset V) := ⟨v₀,mem_compl.mpr hvOut⟩
  let r (a : W) (b : ↥(Wᶜ : Finset V)) := G.Adj a.val b.val
  have hR := independent_cut_strict_comparison G W hInd hCompare hPos
  obtain ⟨f,g,hf,hg,hfr,hgr,hfg,hAvoid,w,hw⟩ :=
    exists_two_injections_with_fresh_edge r w' b' hv₀ hR.1 hR.2
  let M₁ := selectionGraph W f
  let M₂ := selectionGraph W g
  let a := (f w).val
  let b := b'.val
  have hbOut : b ∉ W := hvOut
  have hM₁ : M₁ ≤ G := selectionGraph_le W f hfr
  have hM₂ : M₂ ≤ G := selectionGraph_le W g hgr
  obtain ⟨hm₁,hCover₁⟩ := selectionGraph_isMatching W f hf
  obtain ⟨hm₂,hCover₂⟩ := selectionGraph_isMatching W g hg
  have hCross (u v : V) (h : M₁.Adj u v) : (u ∈ W ∧ v ∉ W) ∨ (v ∈ W ∧ u ∉ W) :=
    selectionGraph_crosses_cut W f h
  have hwa : M₁.Adj w.val a := Or.inl ⟨w,rfl,rfl⟩
  have hwb : M₂.Adj w.val b := Or.inl ⟨w,rfl,congrArg Subtype.val hw.symm⟩
  have hFresh : M₁.degree b = 0 := by
    apply Nat.eq_zero_of_not_pos
    rintro h
    obtain ⟨v,hv⟩ := (M₁.degree_pos_iff_exists_adj b).mp h
    rcases hv with ⟨u,hu,_⟩|⟨u,_,hu⟩
    · exact hbOut (hu.symm ▸ u.property)
    · exact hAvoid u (Subtype.ext hu.symm)
  have hNe : a ≠ b := fun h => hAvoid w (Subtype.ext h)
  have hAOut : a ∉ W := mem_compl.mp (f w).property
  have hbNot : ¬M₁.Adj w.val b := by
    intro h
    have hh := (M₁.degree_pos_iff_exists_adj b).mpr ⟨w.val,h.symm⟩
    omega
  have hDegreeA : M₁.degree a = 1 :=
    degree_eq_one_iff_existsUnique_adj.mpr ⟨w.val,hwa.symm,fun u hu => hm₁ a u w.val hu hwa.symm⟩
  obtain ⟨hS,hOuter,hCard⟩ := OddLowSkeletonWitness.odd_skeleton_of_fresh_matching G M₁ W
    hM₁ hm₁ hCover₁ hCross w.property (hM₂ hwb) hbOut hFresh hThree hOdd
  refine ⟨M₁,M₂,w.val,a,b,hM₁,hM₂,hm₁,hm₂,selectionGraph_disjoint W f g hfg,
    hCover₁,hCover₂,w.property,hwa,hwb,hFresh,hS,hOuter,hCard,?_,?_,hNe⟩
  · apply mem_filter.mpr
    refine ⟨mem_compl.mpr hAOut,?_⟩
    rw [matching_sup_edge_degree M₁ (hM₂ hwb).ne hbNot,hDegreeA,
      if_neg (not_or.mpr ⟨hwa.ne.symm,hNe⟩)]
  · apply mem_filter.mpr
    refine ⟨mem_compl.mpr hbOut,?_⟩
    rw [matching_sup_edge_degree M₁ (hM₂ hwb).ne hbNot,hFresh,if_pos (Or.inr rfl)]

end OverfullWork.CMSTrimmingRound
