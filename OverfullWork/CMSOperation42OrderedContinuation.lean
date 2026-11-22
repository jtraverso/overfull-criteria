module

public import OverfullWork.CMSOperation42OrderedRounds

@[expose] public section


/-! The round constructor preserves the degree order, the strong
outside pair bound, and the full maximum-neighbour inequality. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph RobustExpansion OddCutDeficit
open NormalizedAlmostStoppingRun CleanedSourceVAL
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

structure OrderedFixedCoreState (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (L : ℕ) : Prop where
  uncolourable : ¬G.EdgeColorable G.maxDegree
  no_overfull : ¬G.HasOverfullSubgraph
  ready : IsReady G Xᶜ
  ordered : ∀ y ∈ Xᶜ,∀ x ∈ X,G.degree y ≤ G.degree x
  pairs : ∀ y ∈ Xᶜ,∀ z ∈ Xᶜ,y ≠ z → G.degree y+G.degree z+L ≤ G.maxDegree

def IsMatchingRemovalStop (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) : Prop :=
  (Xᶜ.filter (fun y => 0 < G.degree y)).card ≤ 1 ∨
    ∃ x ∈ X,(∀ v ∈ X,G.degree x ≤ G.degree v) ∧
      ((∑ y ∈ Xᶜ,G.degree y) ≤ G.degree x ∨
        ∃ v ∈ X,v ≠ x ∧ G.degree v+G.degree x ≤ G.maxDegree)

theorem two_le_maximum_core_excess (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hOdd : Odd X.card) (hCore : ∀ v ∈ X,G.degree v=G.maxDegree)
    (hLarge : G.maxDegree < ∑ y ∈ Xᶜ,G.degree y) :
    G.maxDegree+2 ≤ ∑ y ∈ Xᶜ,G.degree y := by
  by_contra! hShort
  have hSum : (∑ y ∈ Xᶜ,G.degree y) = G.maxDegree+1 := by omega
  have hX : (∑ x ∈ X,G.degree x) = G.maxDegree*X.card := by
    rw [sum_congr rfl (fun x hx => hCore x hx)]
    simp [Nat.mul_comm]
  have hBoth := sum_add_sum_compl X (fun v => G.degree v)
  rw [hX,hSum,G.sum_degrees_eq_twice_card_edges] at hBoth
  obtain ⟨k,hk⟩ := hOdd
  have hEq : G.maxDegree*X.card+(G.maxDegree+1) = 2*(G.maxDegree*(k+1))+1 := by
    rw [hk]
    ring
  omega

theorem clean_ordinary_preserves_ordered_state {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K L : ℕ} (c : Certificate G B K) (a : OrderedFixedCoreState G c.set L)
    (s : ClassTwoCleanupRound.CleanRound G c.set)
    (hLarge : G.degree s.anchor < ∑ y ∈ c.setᶜ,G.degree y)
    (hNo : ¬s.graph.HasOverfullSubgraph) (hL : c.setᶜ.card ≤ L)
    (hRoom : 2*B+2 ≤ G.maxDegree) (hGap : B+2*L+2 ≤ G.maxDegree) :
    OrderedFixedCoreState s.graph c.set L := by
  have hPair (y : V) (hy : y ∈ c.setᶜ) (z : V) (hz : z ∈ c.setᶜ) (hyz : y ≠ z) :
      G.degree y+G.degree z+c.setᶜ.card ≤ G.maxDegree := by
    have h := a.pairs y hy z hz hyz
    omega
  refine ⟨s.uncolourable,hNo,⟨s.complement_nonmaximum,s.maximum_neighbour_inequality⟩,
    ordinary_round_cut_order c s a.ready hLarge hRoom hPair,?_⟩
  let U : Finset V := {s.left,s.right}
  have hU : U ⊆ c.setᶜ := insert_subset s.top.left_mem (singleton_subset_iff.mpr s.top.right_mem)
  have hCard : 2 ≤ U.card := by rw [card_pair s.top.ne]
  have hCost : (∑ y ∈ c.setᶜ,G.degree y) ≤ G.maxDegree+B := by
    have h := c.budget
    omega
  have hStep : s.graph.maxDegree+1 = G.maxDegree := by
    have h := s.maximum
    omega
  apply separated_cut_pairs_after_top_match_and_cleanup G s.graph c.setᶜ U B L
    (s.le_residue.trans sdiff_le) hStep hCost hGap a.pairs hU hCard
  · intro u hu
    have hSum : (G \ s.round.matching).degree u+s.round.matching.degree u = G.degree u := by
      simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
        MaximumMatching.degree_sdiff_add_of_le G s.round.matching s.round.le_original u
    have hSelected : u = s.left ∨ u = s.right := by simpa only [U,mem_insert,mem_singleton] using hu
    rw [s.round.complementary_degrees u (hU hu),if_pos hSelected] at hSum
    have hLe : s.graph.degree u ≤ (G \ s.round.matching).degree u :=
      degree_le_of_le s.le_residue (v := u)
    omega
  · intro u hu v hv hvU
    have hNot : v ≠ s.left := by intro h; exact hvU (by simp [U,h])
    rcases (show u = s.left ∨ u = s.right by simpa only [U,mem_insert,mem_singleton] using hu) with h | h
    · exact h ▸ s.top.maximum v hv
    · exact h ▸ s.top.second v hv hNot

theorem clean_maximum_preserves_ordered_state {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K L : ℕ} (c : Certificate G B K) (a : OrderedFixedCoreState G c.set L)
    {U : Finset V} (s : MaximumCoreCleanRound G c.set U)
    (hCore : ∀ v ∈ c.set,G.degree v = G.maxDegree)
    (hU : U ⊆ c.setᶜ) (hThree : U.card = 3)
    (hTop : ∀ u ∈ U,∀ v ∈ c.setᶜ,v ∉ U → G.degree v ≤ G.degree u)
    (hL : c.setᶜ.card ≤ L) (hGap : B+2*L+2 ≤ G.maxDegree) :
    OrderedFixedCoreState s.graph c.set L := by
  have hPair (y : V) (hy : y ∈ c.setᶜ) (z : V) (hz : z ∈ c.setᶜ) (hyz : y ≠ z) :
      G.degree y+G.degree z+c.setᶜ.card ≤ G.maxDegree := by
    have h := a.pairs y hy z hz hyz
    omega
  refine ⟨s.uncolourable,s.no_overfull,s.ready,
    maximum_round_cut_order c s a.ready hCore hPair,?_⟩
  have hCost : (∑ y ∈ c.setᶜ,G.degree y) ≤ G.maxDegree+B := by
    have h := c.budget
    omega
  have hStep : s.graph.maxDegree+1 = G.maxDegree := by
    have h := s.maximum
    omega
  apply separated_cut_pairs_after_top_match_and_cleanup G s.graph c.setᶜ U B L
    (s.le_residue.trans sdiff_le) hStep hCost hGap a.pairs hU (by omega) _ hTop
  intro u hu
  have hSum : (G \ s.round.matching).degree u+s.round.matching.degree u = G.degree u := by
    simpa only [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G s.round.matching s.round.le_original u
  rw [s.round.complementary_degrees u (hU hu),if_pos hu] at hSum
  have hLe : s.graph.degree u ≤ (G \ s.round.matching).degree u :=
    degree_le_of_le s.le_residue (v := u)
  omega

set_option maxHeartbeats 3500000 in
theorem cms_operation_4_2_continue_ordered (ν τ α : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : 512*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ,∀ {W : Type u} [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj] {B K L : ℕ} (c : Certificate G B K),
      let X := c.set
      let Y := Xᶜ
      let n := Fintype.card W
      let r := ⌈ν*(n:ℝ)⌉₊
      let t := ⌈τ*(n:ℝ)⌉₊
      N+3 ≤ X.card → Y.card ≤ L →
      OrderedFixedCoreState G X L → ¬IsMatchingRemovalStop G X → IsRealRobust G ν τ →
      8*((Y.card+3:ℕ):ℝ) ≤ ν*(n:ℝ) → 4*((Y.card+3:ℕ):ℝ) ≤ τ*(n:ℝ) →
      α*(n:ℝ)+(B+Y.card+3:ℕ) ≤ (G.maxDegree:ℝ) →
      4*(B+K+2)+1 ≤ G.maxDegree → B+2*L+2 ≤ G.maxDegree →
      G.maxDegree ≤ (r-1)*(r-1) → 2*B+2*t+1 ≤ G.maxDegree →
      ∀ x ∈ X,(∀ v ∈ X,G.degree x ≤ G.degree v) →
      ∃ H : SimpleGraph W,SafeFixedCoreStep X G H ∧ OrderedFixedCoreState H X L ∧
        ∀ v ∈ X,((∑ w ∈ Y,H.degree w)-H.degree v)+1 ≤ (∑ w ∈ Y,G.degree w)-G.degree x := by
  obtain ⟨N₁,hOrd⟩ := cms_operation_4_2_safe_round.{u} ν τ α hν hντ hτα hα
  obtain ⟨N₂,hMax⟩ := cms_operation_4_2_maximum_core_safe_round.{u} ν τ α hν hντ hτα hα
  refine ⟨max N₁ N₂,?_⟩
  intro W _ _ G _ B K L c X Y n r t hSize hL a hStop hRob hSmall hSmallτ hDens hRoom hGap
    hRate hPair x hx hMin
  have hLarge : G.degree x < ∑ w ∈ Y,G.degree w := by
    apply Nat.lt_of_not_ge
    intro h
    exact hStop (Or.inr ⟨x,hx,hMin,Or.inl h⟩)
  have hNonstop (v : W) (hv : v ∈ X) (hne : v ≠ x) : G.maxDegree < G.degree x+G.degree v := by
    apply Nat.lt_of_not_ge
    intro h
    exact hStop (Or.inr ⟨x,hx,hMin,Or.inr ⟨v,hv,hne,by omega⟩⟩)
  have hSize₁ : N₁+3 ≤ X.card := (Nat.add_le_add_right (le_max_left _ _) _).trans hSize
  have hSize₂ : N₂+3 ≤ X.card := (Nat.add_le_add_right (le_max_right _ _) _).trans hSize
  by_cases hxD : G.degree x < G.maxDegree
  · obtain ⟨s,hS,hNo⟩ := hOrd G c x hSize₁ hx hxD hLarge hNonstop a.ready
      a.uncolourable a.no_overfull hRob hSmall hSmallτ hDens (by omega) hRate hPair
    have hxLarge : G.degree s.anchor < ∑ w ∈ Y,G.degree w := by
      simpa only [hS,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using hLarge
    have hxMin (v : W) (hv : v ∈ X) : G.degree s.anchor ≤ G.degree v := by
      simpa only [hS,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using hMin v hv
    refine ⟨s.graph,SafeFixedCoreStep.ordinary s hNo,
      clean_ordinary_preserves_ordered_state c a s hxLarge hNo hL (by omega) hGap,?_⟩
    intro v hv
    simpa only [hS,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      s.excess_decreases hxMin hxLarge v hv
  · have hCore (v : W) (hv : v ∈ X) : G.degree v = G.maxDegree := by
      have hLower := hMin v hv
      have hUpper := G.degree_le_maxDegree v
      omega
    rw [hCore x hx] at hLarge
    have hDens' : α*(n:ℝ)+(Y.card+3:ℕ) ≤ (G.maxDegree:ℝ) := by
      have h : (Y.card+3:ℕ) ≤ B+Y.card+3 := by omega
      have hCast : ((Y.card+3:ℕ):ℝ) ≤ ((B+Y.card+3:ℕ):ℝ) := by exact_mod_cast h
      exact (add_le_add_right hCast _).trans hDens
    have hPairMax : 2*t+1 ≤ G.maxDegree := by omega
    obtain ⟨U,hU,hThree,hTop,q,hNo⟩ := hMax G c hSize₂ hCore hLarge a.ready
      a.uncolourable hRob hSmall hSmallτ hDens' hRoom hPairMax hRate
    obtain ⟨s,_⟩ := exists_cleanup_of_maximum_core_round G c a.ready U hU hThree hTop q hRoom hNo
    have hLarge' := two_le_maximum_core_excess G X c.odd hCore hLarge
    refine ⟨s.graph,SafeFixedCoreStep.maximum s,
      clean_maximum_preserves_ordered_state c a s hCore hU hThree hTop hL hGap,?_⟩
    intro v hv
    have hDec := s.excess_decreases hCore hLarge' v hv
    rw [hCore x hx]
    exact (Nat.le_add_right _ 1).trans hDec

end OverfullWork.CMSMatchingRemoval
