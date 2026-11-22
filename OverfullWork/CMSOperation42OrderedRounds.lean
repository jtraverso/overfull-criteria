module

public import OverfullWork.CMSOperation42CutOrder
public import OverfullWork.CMSOperation42SafeRun

@[expose] public section


/-! Degree-order preservation in the matching residue. The matched
outside vertices pay for their own loss. If an outside vertex is
unmatched, its degree is at most half the maximum by comparison
with one of the chosen highest-degree vertices. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph OddCutDeficit
open NormalizedAlmostStoppingRun CleanedSourceVAL
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem residue_order_of_top_matching (G R : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel R.Adj] (X : Finset V)
    (hR : R ≤ G) (hLoss : ∀ v,G.degree v ≤ R.degree v+1)
    (hOrder : ∀ y ∈ Xᶜ,∀ x ∈ X,G.degree y ≤ G.degree x)
    (hPair : ∀ y ∈ Xᶜ,∀ z ∈ Xᶜ,y ≠ z → G.degree y+G.degree z ≤ G.maxDegree)
    (hCore : ∀ x ∈ X,R.degree x = G.degree x ∨ G.maxDegree+2 ≤ 2*G.degree x)
    (hOutside : ∀ y ∈ Xᶜ,R.degree y+1 ≤ G.degree y ∨
      ∃ z ∈ Xᶜ,y ≠ z ∧ G.degree y ≤ G.degree z) :
    ∀ y ∈ Xᶜ,∀ x ∈ X,R.degree y ≤ R.degree x := by
  intro y hy x hx
  have hyLe : R.degree y ≤ G.degree y := R.degree_le_of_le hR (v := y)
  have hO := hOrder y hy x hx
  have hxLoss := hLoss x
  rcases hCore x hx with he | hHigh
  · omega
  rcases hOutside y hy with hY | ⟨z,hz,hyz,hY⟩
  · omega
  · have hYZ := hPair y hy z hz hyz
    omega

theorem ordinary_round_cut_order {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K)
    (s : ClassTwoCleanupRound.CleanRound G c.set) (hReady : IsReady G c.setᶜ)
    (hLarge : G.degree s.anchor < ∑ y ∈ c.setᶜ,G.degree y)
    (hRoom : 2*B+2 ≤ G.maxDegree)
    (hPair : ∀ y ∈ c.setᶜ,∀ z ∈ c.setᶜ,y ≠ z →
      G.degree y+G.degree z+c.setᶜ.card ≤ G.maxDegree) :
    ∀ y ∈ c.setᶜ,∀ x ∈ c.set,s.graph.degree y ≤ s.graph.degree x := by
  let R := sdiff G s.round.matching
  have hD (v : V) : R.degree v+s.round.matching.degree v = G.degree v := by
    simpa only [R,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G s.round.matching s.round.le_original v
  have hLoss (v : V) : G.degree v ≤ R.degree v+1 := by
    have h := hD v
    have hOne := s.round.degree_le_one v
    omega
  have hR : R ≤ G := sdiff_le
  have hROrder : ∀ y ∈ c.setᶜ,∀ x ∈ c.set,R.degree y ≤ R.degree x := by
    apply residue_order_of_top_matching G R c.set hR hLoss c.ordered
    · intro y hy z hz hyz
      have h := hPair y hy z hz hyz
      omega
    · intro x hx
      by_cases hEq : x = s.anchor
      · subst x
        exact Or.inl (s.round.anchor_degree_eq s.anchor_mem)
      · right
        have h := LargeCentreCriticalGeometry.other_degree_lower G c s.anchor_mem hLarge hx hEq
        omega
    · intro y hy
      by_cases hSel : y = s.left ∨ y = s.right
      · left
        have h := hD y
        rw [s.round.complementary_degrees y hy,if_pos hSel] at h
        omega
      · exact Or.inr ⟨s.left,s.top.left_mem,fun h => hSel (Or.inl h),s.top.maximum y hy⟩
  exact cut_order_after_cleanup G R s.graph c.set hR s.le_residue s.core hLoss hPair
    (weak_VAL G c.setᶜ hReady) hROrder

theorem maximum_round_cut_order {G : SimpleGraph V} [DecidableRel G.Adj]
    {B K : ℕ} (c : Certificate G B K) {U : Finset V}
    (s : MaximumCoreCleanRound G c.set U) (hReady : IsReady G c.setᶜ)
    (hCore : ∀ v ∈ c.set,G.degree v = G.maxDegree)
    (hPair : ∀ y ∈ c.setᶜ,∀ z ∈ c.setᶜ,y ≠ z →
      G.degree y+G.degree z+c.setᶜ.card ≤ G.maxDegree) :
    ∀ y ∈ c.setᶜ,∀ x ∈ c.set,s.graph.degree y ≤ s.graph.degree x := by
  let R := sdiff G s.round.matching
  have hD (v : V) : R.degree v+s.round.matching.degree v = G.degree v := by
    simpa only [R,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      MaximumMatching.degree_sdiff_add_of_le G s.round.matching s.round.le_original v
  have hLoss (v : V) : G.degree v ≤ R.degree v+1 := by
    have h := hD v
    have hOne := s.round.degree_le_one v
    omega
  have hR : R ≤ G := sdiff_le
  have hROrder (y : V) (hy : y ∈ c.setᶜ) (x : V) (hx : x ∈ c.set) :
      R.degree y ≤ R.degree x := by
    have hyG := hReady.1 y hy
    have hyR := hD y
    have hxR := hD x
    rw [s.round.core_degrees x hx,hCore x hx] at hxR
    omega
  exact cut_order_after_cleanup G R s.graph c.set hR s.le_residue s.core hLoss hPair
    (weak_VAL G c.setᶜ hReady) hROrder

theorem separated_cut_pairs_after_top_match_and_cleanup (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (Y U : Finset V) (B L : ℕ)
    (hLe : H ≤ G) (hD : H.maxDegree+1 = G.maxDegree)
    (hCost : (∑ y ∈ Y,G.degree y) ≤ G.maxDegree+B)
    (hRoom : B+2*L+2 ≤ G.maxDegree)
    (hPair : ∀ y ∈ Y,∀ z ∈ Y,y ≠ z → G.degree y+G.degree z+L ≤ G.maxDegree)
    (hU : U ⊆ Y) (hTwo : 2 ≤ U.card)
    (hLoss : ∀ u ∈ U,H.degree u+1 ≤ G.degree u)
    (hTop : ∀ u ∈ U,∀ v ∈ Y,v ∉ U → G.degree v ≤ G.degree u) :
    ∀ y ∈ Y,∀ z ∈ Y,y ≠ z → H.degree y+H.degree z+L ≤ H.maxDegree := by
  intro y hy z hz hyz
  have hyLe : H.degree y ≤ G.degree y := H.degree_le_of_le hLe (v := y)
  have hzLe : H.degree z ≤ G.degree z := H.degree_le_of_le hLe (v := z)
  have hold := hPair y hy z hz hyz
  by_cases hyU : y ∈ U
  · have h := hLoss y hyU
    omega
  by_cases hzU : z ∈ U
  · have h := hLoss z hzU
    omega
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp hTwo
  have hNew : ({y,z} : Finset V) ⊆ (Y.erase a).erase b := by
    intro v hv
    rcases mem_insert.mp hv with hv|hv
    · have hya : y ≠ a := fun h => hyU (h ▸ ha)
      have hyb : y ≠ b := fun h => hyU (h ▸ hb)
      simp [hv,hya,hyb,hy]
    · rw [mem_singleton.mp hv]
      have hza : z ≠ a := fun h => hzU (h ▸ ha)
      have hzb : z ≠ b := fun h => hzU (h ▸ hb)
      simp [hza,hzb,hz]
  have hSum := sum_le_sum_of_subset_of_nonneg hNew
    (f := fun u => G.degree u) (fun _ _ _ => Nat.zero_le _)
  rw [sum_pair hyz] at hSum
  have hBA : b ∈ Y.erase a := mem_erase.mpr ⟨hab.symm,hU hb⟩
  have hAll := sum_erase_add (s := Y) (f := fun u => G.degree u) (hU ha)
  have hAll' := sum_erase_add (s := Y.erase a) (f := fun u => G.degree u) hBA
  have hty := hTop a ha y hy hyU
  have htz := hTop b hb z hz hzU
  omega

end OverfullWork.CMSMatchingRemoval
