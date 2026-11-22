module

public import OverfullWork.CMSOperation42RobustMatching
public import OverfullWork.DirectedInducedPerturbation
public import OverfullWork.ClassTwoMatchingRound
public import OverfullWork.CleanedSourceVAL

@[expose] public section


/-! A matching-removal round of CMS Operation 4.2 with the perfect
matching supplied by robust expansion of the surviving ordinary core. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph RobustExpansion InducedDigraphSampling
open scoped Classical
universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem induced_graph_robust_of_small_complement (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (ν τ : ℝ) (hν : 0 ≤ ν) (hν₁ : ν ≤ 1) (hτ : 0 ≤ τ) (hτHalf : τ ≤ 1/2)
    (hRob : IsRealRobust G ν τ)
    (hLost : 8*(Sᶜ.card:ℝ) ≤ ν*(Fintype.card V:ℝ))
    (hLostτ : 4*(Sᶜ.card:ℝ) ≤ τ*(Fintype.card V:ℝ)) :
    IsRealRobust (G.induce (S : Set V)) (ν/2) (2*τ) := by
  classical
  cases (Subsingleton.elim (inferInstance : DecidableEq V)
    (fun a b => Classical.propDecidable (a = b)))
  let D := RobustSpanningLinkage.symmetric G
  have hD : DirectedRobustExpansion.IsRealRobust D ν τ := RobustSpanningLinkage.symmetric_robust G ν τ hRob
  have hAll : DirectedRobustExpansion.IsRealRobust (induced D univ) ν τ := by
    apply (induced_real_robust_iff D univ ν τ).mpr
    intro X _ hlo hhi
    have h := hD X (by simpa only [card_univ] using hlo) (by simpa only [card_univ] using hhi)
    simp only [card_univ]
    refine h.trans ?_
    exact_mod_cast (card_le_card (show DirectedRobustExpansion.realNeighbourhood D ν X ⊆
      univ.filter (fun v => ν*(Fintype.card V:ℝ) ≤ (DirectedRobustExpansion.inNeighbours D X v:ℝ)) from
        fun v hv => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩))
  have hLost' : ((univ : Finset V) \ S).card ≤ Sᶜ.card := by rw [←compl_eq_univ_sdiff]
  have hAdded : (S \ (univ : Finset V)).card ≤ Sᶜ.card := by
    have hE : S \ (univ : Finset V) = ∅ := by ext v; simp
    rw [hE,card_empty]
    exact Nat.zero_le _
  have hPart := induced_robust_after_small_vertex_changes D univ S ν τ Sᶜ.card hν hν₁ hτ hτHalf hAll
    hLost' hAdded (by simpa only [card_univ] using hLost) (by simpa only [card_univ] using hLostτ)
  intro X hlo hhi
  let H := G.induce (S : Set V)
  have hGrowth := hPart X hlo hhi
  have hSub : DirectedRobustExpansion.realNeighbourhood (induced D S) (ν/2) X ⊆
      RobustExpansion.realNeighbourhood H (ν/2) X := by
    intro v hv
    have hCount : DirectedRobustExpansion.inNeighbours (induced D S) X v ≤ PrunedCore.neighboursIn H X v := by
      rw [RobustExpansion.neighboursIn_eq_filter_card]
      apply card_le_card
      intro w hw
      obtain ⟨hwX,hwAdj⟩ := mem_filter.mp hw
      exact mem_filter.mpr ⟨hwX,(show G.Adj w.val v.val from hwAdj).symm⟩
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2.trans (by exact_mod_cast hCount)⟩
  exact hGrowth.trans (by exact_mod_cast card_le_card hSub)

theorem degree_le_induced_add_complement (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : S) : G.degree v.val ≤ (G.induce (S : Set V)).degree v+Sᶜ.card := by
  let e : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have hN : ((G.induce (S : Set V)).neighborFinset v).map e = G.neighborFinset v.val ∩ S := by
    ext w
    constructor
    · intro hw
      obtain ⟨x,hx,rfl⟩ := mem_map.mp hw
      exact mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr
        ((mem_neighborFinset (G.induce (S : Set V)) v x).mp hx),x.property⟩
    · intro hw
      obtain ⟨hv,hS⟩ := mem_inter.mp hw
      exact mem_map.mpr ⟨⟨w,hS⟩,(mem_neighborFinset (G.induce (S : Set V)) v _).mpr
        ((mem_neighborFinset G v.val w).mp hv),rfl⟩
  have hEq := congrArg Finset.card hN
  rw [card_map,card_neighborFinset_eq_degree] at hEq
  have hh := card_sdiff_add_card_inter (G.neighborFinset v.val) S
  have h : (G.neighborFinset v.val \ S).card ≤ Sᶜ.card := by
    apply card_le_card
    intro x hx
    exact mem_compl.mpr (mem_sdiff.mp hx).2
  rw [card_neighborFinset_eq_degree] at hh
  simp only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] at hEq hh ⊢
  omega

set_option maxHeartbeats 1600000 in
theorem cms_operation_4_2_next_matching (ν τ α : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : 512*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (x : V),
      let Y := Xᶜ
      let n := Fintype.card V
      N+3 ≤ X.card → Odd X.card → x ∈ X → G.degree x < G.maxDegree →
      G.IsIndepSet (Y : Set V) → CleanedSourceVAL.IsReady G Y →
      ¬G.EdgeColorable G.maxDegree → IsRealRobust G ν τ →
      8*((Y.card+3:ℕ):ℝ) ≤ ν*(n:ℝ) → 4*((Y.card+3:ℕ):ℝ) ≤ τ*(n:ℝ) →
      (∀ v ∈ X, v ≠ x → α*(n:ℝ)+(Y.card+3:ℕ) ≤ (G.degree v:ℝ)) →
      2 ≤ (Y.filter fun v => 0 < G.degree v).card →
      ∃ y z, PaperTopDegreeMatching.IsTopPair G Y y z ∧
        Nonempty (ClassTwoMatchingRound.CoreRound G X x y z) := by
  have hτ : 0 < τ := hν.trans_le hντ
  have hαPos : 0 < α := by linarith only [hτα,hτ]
  have hν₁ : ν ≤ 1 := by linarith only [hντ,hτα,hα,hτ]
  have hτHalf : τ ≤ 1/2 := by linarith only [hτα,hα]
  obtain ⟨N,hN⟩ := exists_matching_on_even_robust_core.{u} (ν/2) (2*τ) α (by positivity)
    (by linarith only [hντ,hτ]) (by linarith only [hτα]) hα
  refine ⟨max N 1,?_⟩
  intro V _ _ G _ X x Y n hSize hOdd hx hxD hInd hClean hUncol hRob hSmall hSmallτ hHigh hActive
  have hY2 : 2 ≤ Y.card := hActive.trans (card_le_card (filter_subset _ _))
  obtain ⟨y,z,hTop⟩ := PaperTopDegreeMatching.exists_top_pair G Y hY2
  have hPos := ClassTwoHallMatching.top_pair_positive G Y hTop hActive
  have hHall := MaximumNeighbourCleanup.hall_of_final_inequality G Y hClean.1 hClean.2
  refine ⟨y,z,hTop,?_⟩
  apply ClassTwoMatchingRound.exists_round_of_core_matchings G hUncol X hOdd hInd hHall hClean.1
    x hx hxD _ y z hTop.left_mem hTop.right_mem hTop.ne hPos.1 hPos.2
  intro a b ha hb hax hbx hab S hCard hEven
  have hSBound : max N 1 ≤ S.card := by omega
  have hSSize : N ≤ S.card := (le_max_left _ _).trans hSBound
  have hComp : Sᶜ.card = Y.card+3 := by
    have h₁ := card_add_card_compl S
    have h₂ := card_add_card_compl X
    change X.card+Y.card = _ at h₂
    omega
  apply hN G S hSSize hEven
  · apply induced_graph_robust_of_small_complement G S ν τ hν.le hν₁ hτ.le hτHalf hRob
    · rwa [hComp]
    · rwa [hComp]
  · have hSSub : S ⊆ X := (erase_subset _ _).trans ((erase_subset _ _).trans (erase_subset _ _))
    have hNonemp : Nonempty S := by
      obtain ⟨v,hv⟩ := card_pos.mp ((le_max_right N 1).trans hSBound)
      exact ⟨⟨v,hv⟩⟩
    letI : Nonempty S := hNonemp
    have hDeg (v : S) : α*(S.card:ℝ) ≤ ((G.induce (S : Set V)).degree v:ℝ) := by
      have hvx : v.val ≠ x := (mem_erase.mp (mem_erase.mp (mem_erase.mp v.property).2).2).1
      have hh := hHigh v.val (hSSub v.property) hvx
      have h := degree_le_induced_add_complement G S v
      rw [hComp] at h
      have hR : (G.degree v.val:ℝ) ≤ ((G.induce (S : Set V)).degree v:ℝ)+(Y.card+3:ℕ) := by
        exact_mod_cast h
      have hs : (S.card:ℝ) ≤ n := by exact_mod_cast card_le_univ S
      have hN := mul_le_mul_of_nonneg_left hs hαPos.le
      linarith only [hh,hR,hN]
    obtain ⟨v,hv⟩ := (G.induce (S : Set V)).exists_minimal_degree_vertex
    simpa only [hv] using hDeg v

theorem cms_operation_4_2_clean_round (ν τ α : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : 512*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (x : V),
      let Y := Xᶜ
      let n := Fintype.card V
      N+3 ≤ X.card → Odd X.card → x ∈ X → G.degree x < G.maxDegree →
      G.IsIndepSet (Y : Set V) → CleanedSourceVAL.IsReady G Y →
      ¬G.EdgeColorable G.maxDegree → IsRealRobust G ν τ →
      8*((Y.card+3:ℕ):ℝ) ≤ ν*(n:ℝ) → 4*((Y.card+3:ℕ):ℝ) ≤ τ*(n:ℝ) →
      (∀ v ∈ X, v ≠ x → α*(n:ℝ)+(Y.card+3:ℕ) ≤ (G.degree v:ℝ)) →
      2 ≤ (Y.filter fun v => 0 < G.degree v).card →
      (∀ u ∈ Y, ∀ v ∈ Y, u ≠ v → G.degree u+G.degree v < G.maxDegree+2) →
      4 ≤ G.maxDegree → ∃ s : ClassTwoCleanupRound.CleanRound G X, s.anchor = x := by
  obtain ⟨N,hN⟩ := cms_operation_4_2_next_matching.{u} ν τ α hν hντ hτα hα
  refine ⟨N,?_⟩
  intro V _ _ G _ X x Y n hSize hOdd hx hxD hInd hClean hUncol hRob hSmall hSmallτ hHigh hActive hPairs hD
  obtain ⟨y,z,hTop,⟨r⟩⟩ :=
    hN G X x hSize hOdd hx hxD hInd hClean hUncol hRob hSmall hSmallτ hHigh hActive
  obtain ⟨s,hx',_⟩ :=
    ClassTwoCleanupRound.exists_cleanup_for_round G X hInd hClean.1 hPairs hD hx hxD hTop r
  exact ⟨s,hx'⟩

end OverfullWork.CMSMatchingRemoval
