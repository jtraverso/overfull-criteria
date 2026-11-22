module

public import OverfullWork.ClassTwoRoundBudget

@[expose] public section


/-! The separation of pairs in (4.2) controls the degree order through
Algorithm 2. A deletion to a different outside vertex forces a margin
by weak VAL. A deletion to the vertex being compared occurs at both
ends and leaves the comparison intact. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph RobustExpansion
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cut_order_after_cleanup_of_edge_sum (G R H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel R.Adj] [DecidableRel H.Adj]
    (X : Finset V) (threshold : ℕ) (hRG : R ≤ G) (hHR : H ≤ R)
    (hCore : H.induce (X : Set V) = R.induce (X : Set V))
    (hLoss : ∀ v,G.degree v ≤ R.degree v+1)
    (hPair : ∀ y ∈ Xᶜ,∀ z ∈ Xᶜ,y ≠ z → G.degree y+G.degree z+Xᶜ.card+1 ≤ threshold)
    (hVAL : ∀ y ∈ Xᶜ,∀ x,G.Adj y x → threshold ≤ G.degree y+G.degree x)
    (hOrder : ∀ y ∈ Xᶜ,∀ x ∈ X,R.degree y ≤ R.degree x) :
    ∀ y ∈ Xᶜ,∀ x ∈ X,H.degree y ≤ H.degree x := by
  intro y hy x hx
  let F := sdiff R H
  have hX (z : V) (h : F.Adj x z) : z ∈ Xᶜ := by
    apply mem_compl.mpr
    intro hz
    have he := congrArg (fun (J : SimpleGraph X) => J.Adj ⟨x,hx⟩ ⟨z,hz⟩) hCore
    exact h.2 (he.mpr h.1)
  have hCard (v : V) : H.degree v+F.degree v=R.degree v := by
    have h := MaximumMatching.degree_sdiff_add_of_le R H hHR v
    simpa only [F,Nat.add_comm,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using h
  by_cases hOther : ∃ z ∈ Xᶜ,z ≠ y ∧ F.Adj x z
  · obtain ⟨z,hz,hzy,hAdj⟩ := hOther
    have hLossX : F.degree x ≤ Xᶜ.card := by
      rw [←card_neighborFinset_eq_degree]
      exact card_le_card (fun z hz => hX z ((mem_neighborFinset _ _ _).mp hz))
    have hLe : H.degree y ≤ G.degree y := H.degree_le_of_le (hHR.trans hRG) (v := y)
    have hS := hVAL z hz x (hRG hAdj.1).symm
    have hP := hPair y hy z hz hzy.symm
    have hxLoss := hLoss x
    have hxCard := hCard x
    omega
  · have hxOnly : F.neighborFinset x ⊆ {y} := by
      intro z hz
      have hAdj := (mem_neighborFinset _ _ _).mp hz
      exact mem_singleton.mpr (by by_contra hzy; exact hOther ⟨z,hX z hAdj,hzy,hAdj⟩)
    have hxLe : F.degree x ≤ 1 := by
      rw [←card_neighborFinset_eq_degree,←card_singleton y]
      exact card_le_card hxOnly
    have hF : F.degree x ≤ F.degree y := by
      by_cases hZero : F.degree x = 0
      · simp [hZero]
      · obtain ⟨z,hAdj⟩ := (F.degree_pos_iff_exists_adj x).mp (by omega)
        have hyz : z = y := mem_singleton.mp (hxOnly ((mem_neighborFinset _ _ _).mpr hAdj))
        have hyPos := (F.degree_pos_iff_exists_adj y).mpr ⟨x,hyz ▸ hAdj.symm⟩
        omega
    have hOrd := hOrder y hy x hx
    have hxCard := hCard x
    have hyCard := hCard y
    omega

theorem cut_order_after_cleanup (G R H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel R.Adj] [DecidableRel H.Adj]
    (X : Finset V) (hRG : R ≤ G) (hHR : H ≤ R)
    (hCore : H.induce (X : Set V) = R.induce (X : Set V))
    (hLoss : ∀ v,G.degree v ≤ R.degree v+1)
    (hPair : ∀ y ∈ Xᶜ,∀ z ∈ Xᶜ,y ≠ z → G.degree y+G.degree z+Xᶜ.card ≤ G.maxDegree)
    (hVAL : ∀ y ∈ Xᶜ,∀ x,G.Adj y x → G.maxDegree+2 ≤ G.degree y+G.degree x)
    (hOrder : ∀ y ∈ Xᶜ,∀ x ∈ X,R.degree y ≤ R.degree x) :
    ∀ y ∈ Xᶜ,∀ x ∈ X,H.degree y ≤ H.degree x := by
  apply cut_order_after_cleanup_of_edge_sum G R H X (G.maxDegree+2) hRG hHR hCore hLoss _ hVAL hOrder
  intro y hy z hz hyz
  have h := hPair y hy z hz hyz
  omega

theorem separated_cut_pairs_after_matching (G R : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel R.Adj] (Y : Finset V) (B L : ℕ)
    (hLe : R ≤ G) (hD : R.maxDegree+1 = G.maxDegree)
    (hCost : (∑ y ∈ Y,G.degree y) ≤ G.maxDegree+B)
    (hRoom : B+2*L+2 ≤ G.maxDegree)
    (hPair : ∀ y ∈ Y,∀ z ∈ Y,y ≠ z → G.degree y+G.degree z+L ≤ G.maxDegree)
    {a b : V} (ha : a ∈ Y) (hb : b ∈ Y) (hab : a ≠ b)
    (haLoss : R.degree a+1 ≤ G.degree a) (hbLoss : R.degree b+1 ≤ G.degree b)
    (hTop : ∀ y ∈ Y,y ≠ a → y ≠ b → G.degree y ≤ G.degree a ∧ G.degree y ≤ G.degree b) :
    ∀ y ∈ Y,∀ z ∈ Y,y ≠ z → R.degree y+R.degree z+L ≤ R.maxDegree := by
  intro y hy z hz hyz
  have hyLe : R.degree y ≤ G.degree y := R.degree_le_of_le hLe (v := y)
  have hzLe : R.degree z ≤ G.degree z := R.degree_le_of_le hLe (v := z)
  have hold := hPair y hy z hz hyz
  by_cases hChosen : y = a ∨ y = b ∨ z = a ∨ z = b
  · rcases hChosen with rfl|rfl|rfl|rfl <;> omega
  push Not at hChosen
  have hNew : ({y,z} : Finset V) ⊆ (Y.erase a).erase b := by
    intro v hv
    rcases mem_insert.mp hv with rfl|hv
    · simp [hChosen.1,hChosen.2.1,hy]
    · rw [mem_singleton.mp hv]
      simp [hChosen.2.2.1,hChosen.2.2.2,hz]
  have hSum := sum_le_sum_of_subset_of_nonneg hNew
    (f := fun u => G.degree u) (fun _ _ _ => Nat.zero_le _)
  rw [sum_pair hyz] at hSum
  have hBA : b ∈ Y.erase a := mem_erase.mpr ⟨hab.symm,hb⟩
  have hAll := sum_erase_add (s := Y) (f := fun u => G.degree u) ha
  have hAll' := sum_erase_add (s := Y.erase a) (f := fun u => G.degree u) hBA
  have hty := hTop y hy hChosen.1 hChosen.2.1
  have htz := hTop z hz hChosen.2.2.1 hChosen.2.2.2
  omega

end OverfullWork.CMSMatchingRemoval
