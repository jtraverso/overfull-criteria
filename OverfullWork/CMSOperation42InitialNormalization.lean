module

public import OverfullWork.CMSOperation42CompleteRun
public import OverfullWork.CMSOperation42SeparatedStart
public import OverfullWork.DegreeOrderedIndependentCut

@[expose] public section


/-! From the odd witness at the end of Operation 4.1 to the fixed
core used by Operation 4.2. Ordering is performed on the graph before
Algorithm 2. With an extra complementary-size margin in the pair
threshold, the fixed-cut cleanup preserves that order and the
entire induced core. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph RobustExpansion OddCutDeficit
open NormalizedAlmostStoppingRun CleanedSourceVAL
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ordered_separated_odd_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hOdd : Odd X.card) (B L : ℕ)
    (hPairs : ∀ y ∈ Xᶜ,∀ z ∈ Xᶜ,y ≠ z → G.degree y+G.degree z+L < G.maxDegree)
    (hBudget : ClassTwoMatchingRun.budget G X ≤ G.maxDegree+B) :
    ∃ Z : Finset V,Odd Z.card ∧ Zᶜ.card = Xᶜ.card ∧
      (∀ y ∈ Zᶜ,∀ x ∈ Z,G.degree y ≤ G.degree x) ∧
      (∀ y ∈ Zᶜ,∀ z ∈ Zᶜ,y ≠ z → G.degree y+G.degree z+L < G.maxDegree) ∧
      ClassTwoMatchingRun.budget G Z ≤ G.maxDegree+B := by
  have hStandard (u : V) (hu : u ∈ Xᶜ) (v : V) (hv : v ∈ Xᶜ) (hne : u ≠ v) :
      G.degree u+G.degree v < G.maxDegree-L := by
    have h := hPairs u hu v hv hne
    omega
  obtain ⟨Y,hCard,hPair,hSum,hOrder⟩ := DegreeOrderedIndependentCut.exists_ordered_subset
    (fun v => G.degree v) (G.maxDegree-L) Xᶜ hStandard
  let Z := Yᶜ
  have hY : Zᶜ = Y := compl_compl Y
  have hZ : Z.card = X.card := by
    have h₁ := card_add_card_compl X
    have h₂ := card_add_card_compl Z
    rw [hY,hCard] at h₂
    omega
  have hNew := DegreeOrderedIndependentCut.budget_add_total_degree G Z
  have hOld := DegreeOrderedIndependentCut.budget_add_total_degree G X
  rw [hZ,hY] at hNew
  refine ⟨Z,by rwa [hZ],(congrArg Finset.card hY).trans hCard,?_,?_,?_⟩
  · intro y hy x hx
    rw [hY] at hy
    exact hOrder y hy x (mem_compl.mp hx)
  · intro y hy z hz hyz
    rw [hY] at hy hz
    have h := hPair y hy z hz hyz
    omega
  · unfold ClassTwoMatchingRun.budget at hBudget ⊢
    rw [hY]
    omega

set_option maxHeartbeats 4200000 in
theorem exists_matching_removal_start_of_near_tight_odd_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (hOdd : Odd X.card) (b A K : ℕ) (hSmall : Xᶜ.card ≤ K)
    (hNC : ¬G.EdgeColorable G.maxDegree) (hNo : ¬G.HasOverfullSubgraph)
    (hVAL : ∀ u v,G.Adj u v → G.maxDegree ≤ G.degree u+G.degree v+A)
    (hBudget : ClassTwoMatchingRun.budget G X ≤ G.maxDegree+b)
    (hRoom : b+2*(A+K)+1 ≤ G.maxDegree) :
    (∀ v,G.degree v=G.maxDegree) ∨
      ∃ (H : SimpleGraph V) (Z : Finset V),
        MaximumNeighbourCleanup.DeletionRun Zᶜ G H ∧ H ≤ G ∧ H.maxDegree = G.maxDegree ∧
        H.induce (Z : Set V) = G.induce (Z : Set V) ∧
        Odd Z.card ∧ Zᶜ.card ≤ K ∧ H.IsIndepSet (↑(Zᶜ) : Set V) ∧
        ClassTwoMatchingRun.budget H Z ≤ H.maxDegree+(b+2*(A+K)) ∧
        OrderedFixedCoreState H Z (A+K) := by
  let L := A+K
  have hVAL₁ (u v : V) (h : G.Adj u v) : G.maxDegree ≤ G.degree u+G.degree v+L := by
    have hh := hVAL u v h
    dsimp only [L]
    omega
  obtain ⟨S,_,hOddS,hSmallS,_,hBudgetS,hPairsS⟩ :=
    separate_initial_odd_cut G X hOdd b L hBudget hRoom hVAL₁
  obtain ⟨Z,hOddZ,hSizeZ,hOrd,hPairs,hBudgetZ⟩ :=
    ordered_separated_odd_cut G S hOddS (b+2*L) L hPairsS hBudgetS
  have hK : Zᶜ.card ≤ K := hSizeZ.le.trans (hSmallS.trans hSmall)
  by_cases hReg : ∀ v,G.degree v = G.maxDegree
  · exact Or.inl hReg
  right
  have hNonmax (y : V) (hy : y ∈ Zᶜ) : G.degree y < G.maxDegree := by
    by_contra! hn
    apply hReg
    intro v
    have hv := G.degree_le_maxDegree v
    by_cases hvZ : v ∈ Z
    · have h := hOrd y hy v hvZ
      omega
    · have hvY : v ∈ Zᶜ := mem_compl.mpr hvZ
      by_cases he : v = y
      · subst v
        omega
      · have h := hPairs y hy v hvY (fun h => he h.symm)
        omega
  have hInd : G.IsIndepSet (↑(Zᶜ) : Set V) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro u hu v hv huv hAdj
    have h := hPairs u hu v hv huv
    have hh := hVAL₁ u v hAdj
    omega
  obtain ⟨H,hRun,hLe,hMax,hNC',hNo',hCore,hW,hReady⟩ :=
    MaximumNeighbourCleanup.exists_cleanup_no_overfull G hNC Zᶜ hNonmax hNo
  have hS : (↑(Zᶜ) : Set V)ᶜ = (Z : Set V) := by ext v; simp
  rw [hS] at hCore
  have hIndH := FixedCoreBudgetTransport.independent_of_le G H Zᶜ hInd hLe
  have hEq := FixedCoreBudgetTransport.budget_eq_of_fixed_core G H Z hCore hMax hInd hIndH
  have hNewBudget : ClassTwoMatchingRun.budget H Z ≤ H.maxDegree+(b+2*L) := by
    unfold ClassTwoMatchingRun.budget
    rwa [hEq,hMax]
  refine ⟨H,Z,hRun,hLe,hMax,hCore,hOddZ,hK,hIndH,hNewBudget,
    ⟨hNC',hNo',⟨hW,hReady⟩,?_,?_⟩⟩
  · apply cut_order_after_cleanup_of_edge_sum G G H Z (G.maxDegree-A) le_rfl hLe hCore
      (fun _ => by omega) _ _ hOrd
    · intro y hy z hz hyz
      have h := hPairs y hy z hz hyz
      dsimp only [L] at h
      omega
    · intro y _ x hAdj
      have h := hVAL y x hAdj
      omega
  · intro y hy z hz hyz
    have h₁ : H.degree y ≤ G.degree y := H.degree_le_of_le hLe (v := y)
    have h₂ : H.degree z ≤ G.degree z := H.degree_le_of_le hLe (v := z)
    have h := hPairs y hy z hz hyz
    omega

end OverfullWork.CMSMatchingRemoval
