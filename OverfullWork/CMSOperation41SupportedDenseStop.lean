module

public import OverfullWork.CMSNoAlmostDenseStop
public import OverfullWork.CMSOperation42Round
public import OverfullWork.CMSOddDeficitStop

@[expose] public section


/-! Case 1 uses the actual non-isolated support of the last graph.
Pass the trimmed degrees, the local low-degree condition and the
robustness margin to the appropriate simple stopping profile. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph RobustExpansion
open scoped Classical
universe u

set_option maxHeartbeats 3200000 in
theorem cms_colourable_of_supported_dense_trimming_stop (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ σ : ℝ,0 < σ ∧ ∀ ν : ℝ,0 < ν → ν ≤ σ →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (X B : Finset V),
          let n := Fintype.card V
          let d := G.maxDegree
          N ≤ X.card → α*(n:ℝ) ≤ (d:ℝ) →
          G.support ⊆ (X : Set V) → (∀ v ∈ X,0 < G.degree v) → B ⊆ X →
          (∀ v ∈ X,v ∉ B → (d:ℝ)-6*η*(n:ℝ) ≤ (G.degree v:ℝ)) →
          (∀ a b,G.degree a ≤ 2 → G.Adj a b → d+2 ≤ G.degree a+G.degree b) →
          (B.card ≤ 1 ∨ (Even X.card ∧ B.card ≤ 2)) →
          ¬G.HasOverfullSubgraph → IsRealRobust G (2*ν) σ →
          8*(Xᶜ.card:ℝ) ≤ (2*ν)*(n:ℝ) → 4*(Xᶜ.card:ℝ) ≤ σ*(n:ℝ) → G.EdgeColorable d := by
  obtain ⟨τ,hτ,hUse⟩ := cms_colourable_of_cleaned_dense_stop.{u} α hα hα₁
  let σ := min (τ/2) (1/2)
  have hσ₁ : σ ≤ τ/2 := min_le_left _ _
  have hσ₂ : σ ≤ 1/2 := min_le_right _ _
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  refine ⟨σ,hσ,?_⟩
  intro ν hν hνσ
  obtain ⟨η₀,hη₀,hUse⟩ := hUse ν hν (by linarith only [hνσ,hσ₁,hτ])
  refine ⟨η₀/2,by positivity,?_⟩
  intro η hη hηMax
  obtain ⟨N₀,hUse⟩ := hUse (2*η) (by positivity) (by linarith only [hηMax])
  let N := max N₀ 1
  refine ⟨N,?_⟩
  intro V _ _ G _ X B n d hSize hDensity hSupport hPositive hSub hOrd hWeak hProfiles hNo hRob hSmall hSmallτ
  let H := G.induce (X : Set V)
  have hNX : 1 ≤ X.card := (le_max_right _ _).trans hSize
  have hX : X.Nonempty := card_pos.mp hNX
  obtain ⟨a₀,ha₀⟩ := hX
  have hPosD : 0 < d := (hPositive a₀ ha₀).trans_le (G.degree_le_maxDegree _)
  have hD : H.maxDegree = d := maxDegree_induce_of_positive_support_subset G X hSupport hPosD
  have hDeg (v : X) : H.degree v = G.degree v.val := by
    simpa only [H,←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using
      G.degree_induce_of_support_subset hSupport v
  have hN : Fintype.card (↥(X : Set V)) = X.card := Fintype.card_coe X
  have hParts : X.card+Xᶜ.card = n := card_add_card_compl X
  have hHalf : (n:ℝ) ≤ 2*(X.card:ℝ) := by
    have hp : (X.card:ℝ)+(Xᶜ.card:ℝ) = n := by exact_mod_cast hParts
    have ht := mul_le_mul_of_nonneg_right (show 2*ν ≤ 1 by linarith only [hνσ,hσ₂])
      (Nat.cast_nonneg (α := ℝ) n)
    linarith only [hp,ht,hSmall,Nat.cast_nonneg (α := ℝ) Xᶜ.card]
  have hDensH : α*(Fintype.card (↥(X : Set V)):ℝ) ≤ (H.maxDegree:ℝ) := by
    rw [hN,hD]
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_univ X) hα.le).trans hDensity
  have hHigh (v : X) (hv : v.val ∉ B) :
      (H.maxDegree:ℝ)-6*(2*η)*(Fintype.card (↥(X : Set V)):ℝ) ≤ (H.degree v:ℝ) := by
    have hGrow := mul_le_mul_of_nonneg_left hHalf (show 0 ≤ 6*η by positivity)
    have hDegV := hOrd v.val v.property hv
    rw [hN,hD,hDeg]
    linarith only [hGrow,hDegV]
  have hNoH := Critical.no_overfull_of_copy (Copy.induce G (X : Set V)) hD hNo
  have hRaw := CMSMatchingRemoval.induced_graph_robust_of_small_complement G X (2*ν) σ
    (by positivity) (by linarith only [hνσ,hσ₂]) hσ.le hσ₂ hRob hSmall hSmallτ
  have hRH : IsRealRobust H ν τ := by
    rw [show 2*ν/2 = ν by ring] at hRaw
    exact real_robust_of_subgraph_degree_loss H H le_rfl 0 ν ν (2*σ) τ le_rfl
      (by linarith only [hσ₁]) (by simp) (fun _ => by simp) hRaw
  apply colourable_of_induced_support_subset G X hSupport d
  rw [←hD]
  have hWeakH (u v : X) (hu : H.degree u ≤ 2) (huv : H.Adj u v) :
      H.maxDegree+2 ≤ H.degree u+H.degree v := by
    rw [hD,hDeg,hDeg]
    exact hWeak u.val v.val (by rwa [hDeg] at hu) huv
  apply hUse H (by rw [hN]; exact (le_max_left _ _).trans hSize) hDensH
    (fun v => (hDeg v).symm ▸ hPositive v.val v.property) hWeakH _ hNoH hRH
  rcases hProfiles with hOne | ⟨hEven,hTwo⟩
  · left
    by_cases hB : B.Nonempty
    · obtain ⟨z,hz⟩ := hB
      let z' : X := ⟨z,hSub hz⟩
      refine ⟨z',fun v hv => hHigh v (fun h => hv (Subtype.ext ?_))⟩
      exact card_le_one.mp hOne v.val h z hz
    · exact ⟨⟨a₀,ha₀⟩,fun v _ => hHigh v (fun hv => hB ⟨v.val,hv⟩)⟩
  · right
    refine ⟨by rwa [hN],?_⟩
    by_cases hB : B.Nonempty
    · obtain ⟨x,hx⟩ := hB
      let x' : X := ⟨x,hSub hx⟩
      have hTail : (B.erase x).card ≤ 1 := by
        have h := card_erase_add_one hx
        omega
      by_cases hTailPos : (B.erase x).Nonempty
      · obtain ⟨y,hy⟩ := hTailPos
        let y' : X := ⟨y,hSub (mem_of_mem_erase hy)⟩
        refine ⟨x',y',?_⟩
        intro v hvx hvy
        apply hHigh v
        intro hv
        have hv' : v.val ∈ B.erase x := mem_erase.mpr ⟨fun h => hvx (Subtype.ext h),hv⟩
        exact hvy (Subtype.ext (card_le_one.mp hTail v.val hv' y hy))
      · refine ⟨x',x',?_⟩
        intro v hv _
        exact hHigh v (fun he => hTailPos ⟨v.val,mem_erase.mpr ⟨fun h => hv (Subtype.ext h),he⟩⟩)
    · exact ⟨⟨a₀,ha₀⟩,⟨a₀,ha₀⟩,fun v _ _ => hHigh v (fun hv => hB ⟨v.val,hv⟩)⟩

end OverfullWork.CanonicalRegularization
