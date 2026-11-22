module

public import OverfullWork.CMSSecondLowTerminalColouring
public import OverfullWork.CMSCleanupRobustness

@[expose] public section


/-! Apply Algorithm 2 to the enlarged exceptional set of Subcase 2.4.
The ordinary deficit pays for the partition even if the original
minimum outside vertex stops being the largest exceptional weight. -/
namespace OverfullWork.NormalizedClassTwoStep

open Finset SimpleGraph TwoIndependentIdentifications OddCutDeficit RobustExpansion
open FixedCoreBudgetTransport
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
universe u

set_option maxHeartbeats 1400000 in
theorem cms_no_second_low_terminal_after_cleanup (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ σ : ℝ,0 < σ ∧ ∀ ν : ℝ,0 < ν → ν ≤ σ →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 ≤ η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] {B K : ℕ} {s : State V B K}
          (p : SecondLowData s),
          let m := Fintype.card (Vertices p.exceptional)
          let d := s.graph.maxDegree
          N ≤ m → α*(m:ℝ) ≤ (d:ℝ) → B ≤ η*(m:ℝ) →
          (K+1:ℕ) ≤ 2*η^2*(m:ℝ) → B < d →
          ((max B (K+1):ℕ):ℝ) ≤ ν*(Fintype.card V:ℝ) →
          IsRealRobust s.graph (2*ν) σ → False := by
  obtain ⟨σ,hσ,hUse⟩ := cms_colourable_of_two_centre_stop.{u} α hα hα₁
  refine ⟨σ,hσ,?_⟩
  intro ν hν hνσ
  obtain ⟨η₀,hη₀,hUse⟩ := hUse ν hν hνσ
  let ηMax := min η₀ (1/2)
  refine ⟨ηMax,by dsimp only [ηMax]; positivity,?_⟩
  intro η hη hηMax
  obtain ⟨N,hN⟩ := hUse η hη (hηMax.trans (min_le_left _ _))
  refine ⟨N,?_⟩
  intro V _ _ B K s p m d hSize hDensity hB hK hBd hLoss hRob
  let G := s.graph
  let Z := p.exceptional
  have hDegZ (z : V) (hz : z ∈ Z) : G.degree z ≤ G.degree p.anchor := p.degree_bounds.2.1 z hz
  have hxB : G.degree p.anchor < B := p.degree_bounds.1
  have hNonmax (z : V) (hz : z ∈ Z) : G.degree z < G.maxDegree :=
    (hDegZ z hz).trans_lt (hxB.trans hBd)
  obtain ⟨H,_,hLe,hMax,hNC,hNo,hCore,hNonmaxH,hRich⟩ :=
    MaximumNeighbourCleanup.exists_cleanup_no_overfull G s.uncolourable Z hNonmax s.no_overfull
  have hZInd := independent_of_le G H Z p.independent hLe
  have hSet : (↑(Zᶜ) : Set V) = (Z : Set V)ᶜ := by ext v; simp
  have hCore' : H.induce (↑(Zᶜ) : Set V) = G.induce (↑(Zᶜ) : Set V) := by
    rwa [hSet]
  have hBudget := budget_eq_of_fixed_core G H Zᶜ hCore' hMax
    (by simpa only [compl_compl] using p.independent)
    (by simpa only [compl_compl] using hZInd)
  simp only [compl_compl] at hBudget
  let F := deficitMass H H.maxDegree Zᶜ
  have hBoundF : F ≤ 3*B := by
    have hOld := p.ordinary_deficit_bounds.2
    have hOutside := p.degree_bounds.2.2.2
    change deficitMass G G.maxDegree Zᶜ ≤ B at hOld
    change (∑ z ∈ Z,G.degree z) ≤ 2*B at hOutside
    change F+(∑ z ∈ Z,H.degree z) = _ at hBudget
    omega
  have hFAnchor : G.degree p.anchor ≤ F := by
    have hOld := p.ordinary_deficit_bounds.1
    have hMono : deficitMass G G.maxDegree Zᶜ ≤ F := by
      unfold F deficitMass
      rw [hMax]
      apply sum_le_sum
      intro v _
      have h : H.degree v ≤ G.degree v := H.degree_le_of_le hLe (v := v)
      omega
    exact hOld.trans hMono
  have hDegree (z : V) (hz : z ∈ Z) : H.degree z ≤ G.degree p.anchor :=
    (show H.degree z ≤ G.degree z from H.degree_le_of_le hLe (v := z)).trans (hDegZ z hz)
  obtain ⟨A,hA,hOrder,hBalance⟩ := BoundedWeightBipartition.exists_balanced Z
    (fun z => H.degree z) (G.degree p.anchor) hDegree
  let M := graph H Z A hA hZInd
  have hZCard : 2 ≤ Z.card := by
    have hAct := ClassTwoGlobalNoOverfull.two_active_of_large_centre G s.cut p.anchor p.anchor_mem p.large
    have hComp := hAct.trans (card_le_card (filter_subset _ _))
    have hYX : p.anchor ∉ s.cut.setᶜ := notMem_compl.mpr p.anchor_mem
    change 2 ≤ (insert p.anchor s.cut.setᶜ).card
    rw [card_insert_of_notMem hYX]
    omega
  have hZSmall : (Z.card:ℝ) ≤ 2*η^2*(m:ℝ) :=
    (by exact_mod_cast p.card_bound : (Z.card:ℝ) ≤ (K+1:ℕ)).trans hK
  have hFL : (∑ x : Outside Z,(H.maxDegree-H.degree x.val)) = F := by
    unfold F deficitMass
    exact sum_subtype Zᶜ (fun v => mem_compl) (fun v => H.maxDegree-H.degree v) |>.symm
  have hFReal : (F:ℝ) ≤ 3*η*(m:ℝ) := by
    have h : (F:ℝ) ≤ 3*(B:ℝ) := by exact_mod_cast hBoundF
    linarith only [h,hB]
  have hHigh (x : Outside Z) : (H.maxDegree:ℝ)-5*η*(m:ℝ) ≤ H.degree x.val := by
    have hSingle : H.maxDegree-H.degree x.val ≤ F :=
      single_le_sum (f := fun v => H.maxDegree-H.degree v) (fun _ _ => Nat.zero_le _) (mem_compl.mpr x.property)
    have hD := H.degree_le_maxDegree x.val
    have hR : (H.maxDegree:ℝ) ≤ (H.degree x.val:ℝ)+(F:ℝ) := by
      exact_mod_cast (show H.maxDegree ≤ H.degree x.val+F by omega)
    have hηm := mul_nonneg hη (Nat.cast_nonneg (α := ℝ) m)
    linarith only [hR,hFReal,hηm]
  have hLeft : M.degree (Sum.inl false) = ∑ z ∈ A,H.degree z := by
    rw [show M = graph H Z A hA hZInd from rfl,degree_inl]
    rfl
  have hRight : M.degree (Sum.inl true) = ∑ z ∈ Z \ A,H.degree z := by
    rw [show M = graph H Z A hA hZInd from rfl,degree_inl]
    rfl
  have hBoth : M.degree (Sum.inl false)+M.degree (Sum.inl true) ≤ 2*B := by
    have hS := p.degree_bounds.2.2.2
    change (∑ z ∈ Z,G.degree z) ≤ 2*B at hS
    have hLeSum := sum_le_sum (s := Z) (fun z _ =>
      (show H.degree z ≤ G.degree z from H.degree_le_of_le hLe (v := z)))
    have hSum := sum_sdiff hA (f := fun z => H.degree z)
    rw [hLeft,hRight]
    omega
  have hLow (k : Bool) : (M.degree (Sum.inl k):ℝ) ≤ 10*η*(m:ℝ) := by
    have hC : M.degree (Sum.inl k) ≤ 2*B := by cases k <;> omega
    have h : (M.degree (Sum.inl k):ℝ) ≤ 2*(B:ℝ) := by exact_mod_cast hC
    have hηm := mul_nonneg hη (Nat.cast_nonneg (α := ℝ) m)
    linarith only [h,hB,hηm]
  have hOrderM : M.degree (Sum.inl false) ≤ M.degree (Sum.inl true) := by
    rwa [hLeft,hRight]
  have hBalanceM : M.degree (Sum.inl true) ≤ M.degree (Sum.inl false)+
      ∑ x : Outside Z,(H.maxDegree-H.degree x.val) := by
    rw [hFL,hLeft,hRight]
    omega
  have hLossDeg (v : V) : G.degree v ≤ H.degree v+max B (K+1) := by
    by_cases hv : v ∈ Z
    · have hD := hDegZ v hv
      have hM := le_max_left B (K+1)
      omega
    · have h := degree_le_degree_add_complement G H Zᶜ hCore' v (mem_compl.mpr hv)
      rw [compl_compl] at h
      have hM := le_max_right B (K+1)
      have hCard : Z.card ≤ K+1 := p.card_bound
      omega
  have hMargin : ((max B (K+1):ℕ):ℝ) ≤ (2*ν-ν)*(Fintype.card V:ℝ) := by
    linarith only [hLoss]
  have hRobH := real_robust_of_subgraph_degree_loss G H hLe (max B (K+1)) (2*ν) ν σ σ
    (by linarith only [hν]) le_rfl hMargin hLossDeg hRob
  have hDefReal : ((∑ x : Outside Z,(H.maxDegree-H.degree x.val)):ℕ) ≤ 6*η*(m:ℝ) := by
    rw [hFL]
    linarith only [hFReal,mul_nonneg hη (Nat.cast_nonneg (α := ℝ) m)]
  have hDens : α*(m:ℝ) ≤ (H.maxDegree:ℝ) := by rwa [hMax]
  exact hNC (hN H Z A hA hZInd hSize hDens (even_card_vertices Z p.even_complement) hZCard hZSmall
    hLow hOrderM hBalanceM hDefReal hHigh (CleanedSourceVAL.weak_VAL H Z ⟨hNonmaxH,hRich⟩) hNo hRobH)

end OverfullWork.NormalizedClassTwoStep
