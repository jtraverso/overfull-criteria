module

public import OverfullWork.CMSOperation41SupportedDenseStop
public import OverfullWork.FixedCoreBudgetTransport
public import OverfullWork.MaximumNeighbourCleanup

@[expose] public section


/-! The final application of Algorithm 2 supplies (4.1). Its edge
losses outside the chosen vertices cost at most their number. The
ordinary graph is unchanged, which protects robust expansion. -/
namespace OverfullWork.RobustExpansion

open Finset SimpleGraph PrunedCore
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 2000000 in
theorem real_robust_of_unchanged_outside_set (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (W : Finset V) (ν τ : ℝ)
    (hOutside : ∀ a b,a ∉ W → b ∉ W → G.Adj a b → H.Adj a b)
    (hLoss : (W.card:ℝ) ≤ (ν/2)*(Fintype.card V:ℝ))
    (hRob : IsRealRobust G ν τ) : IsRealRobust H (ν/2) τ := by
  intro S hLower hUpper
  have hNeighbours (a : V) (ha : a ∉ W) :
      neighboursIn G S a ≤ neighboursIn H S a+W.card := by
    rw [neighboursIn_eq_filter_card,neighboursIn_eq_filter_card]
    have hSub : (S.filter (G.Adj a)) \ W ⊆ S.filter (H.Adj a) := by
      intro b hb
      obtain ⟨hIn,hOut⟩ := mem_sdiff.mp hb
      obtain ⟨hSet,hOld⟩ := mem_filter.mp hIn
      exact mem_filter.mpr ⟨hSet,hOutside a b ha hOut hOld⟩
    have h := card_le_card_sdiff_add_card (s := S.filter (G.Adj a)) (t := W)
    exact h.trans (Nat.add_le_add_right (card_le_card hSub) _)
  have hSub : realNeighbourhood G ν S \ W ⊆ realNeighbourhood H (ν/2) S := by
    intro a ha
    obtain ⟨hOld,hW⟩ := mem_sdiff.mp ha
    have hVal := (mem_filter.mp hOld).2
    have hh : (neighboursIn G S a:ℝ) ≤ (neighboursIn H S a:ℝ)+W.card := by exact_mod_cast hNeighbours a hW
    exact mem_filter.mpr ⟨mem_univ _,by linarith only [hVal,hh,hLoss]⟩
  have hCard : ((realNeighbourhood G ν S).card:ℝ) ≤ ((realNeighbourhood H (ν/2) S).card:ℝ)+W.card := by
    have h := card_le_card_sdiff_add_card (s := realNeighbourhood G ν S) (t := W)
    exact_mod_cast h.trans (Nat.add_le_add_right (card_le_card hSub) _)
  have hGrow := hRob S hLower hUpper
  linarith only [hGrow,hCard,hLoss]

end OverfullWork.RobustExpansion

namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph RobustExpansion MaximumNeighbourCleanup
open scoped Classical
universe u

set_option maxHeartbeats 4400000 in
/-- Exclude the dense stopping graph of Case 1 by running Algorithm 2
on its last low set and then using the cleaned graph on its actual
support. The output handles both parities when at most one exception
survives, and the even-order case with two surviving exceptions. -/
theorem cms_no_dense_trimming_stop_before_final_cleanup (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ σ : ℝ,0 < σ ∧ ∀ ν : ℝ,0 < ν → ν ≤ σ →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (A W : Finset V),
          let n := Fintype.card V
          let d := G.maxDegree
          N+W.card ≤ A.card → α*(n:ℝ) ≤ (d:ℝ) →
          G.support ⊆ (A : Set V) → W ⊆ A → (∀ w ∈ W,G.degree w < d) →
          (W.card ≤ 1 ∨ (Even A.card ∧ W.card ≤ 2)) →
          (∀ v ∈ A,v ∉ W → (d:ℝ)-6*η*(n:ℝ) ≤ (G.degree v:ℝ)) →
          ¬G.EdgeColorable d → ¬G.HasOverfullSubgraph → IsRealRobust G (4*ν) σ →
          8*((Aᶜ.card+W.card:ℕ):ℝ) ≤ (2*ν)*(n:ℝ) →
          4*((Aᶜ.card+W.card:ℕ):ℝ) ≤ σ*(n:ℝ) → False := by
  obtain ⟨σ,hσ,hUse⟩ := cms_colourable_of_supported_dense_trimming_stop.{u} α hα hα₁
  refine ⟨σ,hσ,?_⟩
  intro ν hν hνσ
  obtain ⟨η₀,hη₀,hUse⟩ := hUse ν hν hνσ
  let ηMax := min (η₀/2) (α/24)
  refine ⟨ηMax,by dsimp only [ηMax]; positivity,?_⟩
  intro η hη hηMax
  obtain ⟨N₀,hUse⟩ := hUse (2*η) (by positivity)
    (by have h := hηMax.trans (min_le_left _ _); linarith)
  let N := max N₀ (max ⌈8/α⌉₊ ⌈1/η⌉₊)
  refine ⟨N,?_⟩
  intro V _ _ G _ A W n d hn hDens hSupport hWA hW hProfiles hOrd hNC hNo hRob hSmall hSmallτ
  have hCardW : W.card ≤ 2 := hProfiles.elim (fun h => h.trans (by decide)) And.right
  have hLarge (z : ℝ) (hz : ⌈z⌉₊ ≤ N) : z ≤ (n:ℝ) := by
    have hN : N ≤ n := (Nat.le_add_right _ _).trans (hn.trans (card_le_univ A))
    exact (Nat.le_ceil z).trans (by exact_mod_cast hz.trans hN)
  have hαn : 8 ≤ α*(n:ℝ) := by
    have h := hLarge (8/α) ((le_max_left _ _).trans (le_max_right _ _))
    simpa only [mul_comm α] using (div_le_iff₀ hα).mp h
  have hηn : 1 ≤ η*(n:ℝ) := by
    have h := hLarge (1/η) ((le_max_right _ _).trans (le_max_right _ _))
    simpa only [mul_comm η] using (div_le_iff₀ hη).mp h
  have hSmallη := mul_le_mul_of_nonneg_right (hηMax.trans (min_le_right _ _))
    (Nat.cast_nonneg (α := ℝ) n)
  obtain ⟨H,p,hHG,hMax,hUncolourable,hNoH,hCore,hWH,hFinal⟩ :=
    exists_cleanup_no_overfull G hNC W hW hNo
  let X := univ.filter (fun v => 0 < H.degree v)
  let B := W ∩ X
  have hX (v : V) : v ∈ X ↔ 0 < H.degree v := by simp [X]
  have hSupportH : H.support ⊆ (X : Set V) := fun v hv => (hX v).mpr ((H.degree_pos_iff_mem_support v).mpr hv)
  have hXA : X ⊆ A := by
    intro v hv
    obtain ⟨x,hx⟩ := (H.degree_pos_iff_exists_adj v).mp ((hX v).mp hv)
    exact hSupport (G.mem_support.mpr ⟨x,hHG hx⟩)
  have hOutside : H.induce (↑(Wᶜ : Finset V) : Set V) = G.induce (↑(Wᶜ : Finset V) : Set V) := by
    rw [show (↑(Wᶜ : Finset V) : Set V) = (W : Set V)ᶜ by ext v; simp]
    exact hCore
  have hLoss (v : V) (hv : v ∉ W) : G.degree v ≤ H.degree v+W.card := by
    have h := FixedCoreBudgetTransport.degree_le_degree_add_complement G H Wᶜ hOutside v (mem_compl.mpr hv)
    simpa only [compl_compl] using h
  have hGood (v : V) (hv : v ∈ A) (hvW : v ∉ W) : 3 ≤ H.degree v := by
    have hh : (G.degree v:ℝ) ≤ (H.degree v:ℝ)+W.card := by exact_mod_cast hLoss v hvW
    have hw : (W.card:ℝ) ≤ 2 := by exact_mod_cast hCardW
    exact_mod_cast (show (3:ℝ) ≤ (H.degree v:ℝ) by
      linarith only [hOrd v hv hvW,hh,hw,hDens,hαn,hSmallη])
  have hAX : A \ W ⊆ X := fun v hv => (hX v).mpr (by
    have h := hGood v (mem_sdiff.mp hv).1 (mem_sdiff.mp hv).2
    omega)
  have hComps : Xᶜ.card ≤ Aᶜ.card+W.card := by
    have hSub : Xᶜ ⊆ Aᶜ ∪ W := by
      intro v hv
      by_cases ha : v ∈ A
      · have hw : v ∈ W := by
          by_contra h
          exact mem_compl.mp hv (hAX (mem_sdiff.mpr ⟨ha,h⟩))
        exact mem_union_right _ hw
      · exact mem_union_left _ (mem_compl.mpr ha)
    exact (card_le_card hSub).trans (card_union_le _ _)
  have hSizeX : N₀ ≤ X.card := by
    have h₁ := card_le_card_sdiff_add_card (s := A) (t := W)
    have h₂ := card_le_card hAX
    have h₃ : N₀ ≤ N := le_max_left _ _
    omega
  have hDensH : α*(n:ℝ) ≤ (H.maxDegree:ℝ) := by rwa [hMax]
  have hOrdH (v : V) (hv : v ∈ X) (hnB : v ∉ B) :
      (H.maxDegree:ℝ)-6*(2*η)*(n:ℝ) ≤ (H.degree v:ℝ) := by
    have hnW : v ∉ W := fun hw => hnB (mem_inter.mpr ⟨hw,hv⟩)
    have hh : (G.degree v:ℝ) ≤ (H.degree v:ℝ)+W.card := by exact_mod_cast hLoss v hnW
    have hw : (W.card:ℝ) ≤ 2 := by exact_mod_cast hCardW
    rw [hMax]
    linarith only [hh,hw,hηn,hOrd v (hXA hv) hnW]
  have hWeakH (u v : V) (hu : H.degree u ≤ 2) (huv : H.Adj u v) :
      H.maxDegree+2 ≤ H.degree u+H.degree v := by
    have huX := (hX u).mpr ((H.degree_pos_iff_exists_adj u).mpr ⟨v,huv⟩)
    have huW : u ∈ W := by
      by_contra h
      have hge := hGood u (hXA huX) h
      omega
    exact degree_sum_of_final_inequality H W hWH hFinal u huW v huv
  have hBSub : B ⊆ W := inter_subset_left
  have hProfileH : B.card ≤ 1 ∨ (Even X.card ∧ B.card ≤ 2) := by
    by_cases hOne : B.card ≤ 1
    · exact Or.inl hOne
    right
    have hSizeB := card_le_card hBSub
    have hEq : B = W := eq_of_subset_of_card_le hBSub (by omega)
    have hEvenA : Even A.card := hProfiles.elim (fun h => by omega) And.left
    have hEqX : X = A := by
      apply le_antisymm hXA
      intro v hv
      by_cases hvW : v ∈ W
      · exact (mem_inter.mp (hEq.symm ▸ hvW : v ∈ B)).2
      · exact hAX (mem_sdiff.mpr ⟨hv,hvW⟩)
    exact ⟨hEqX.symm ▸ hEvenA,hSizeB.trans hCardW⟩
  have hOutsideEdges (a b : V) (ha : a ∉ W) (hb : b ∉ W) : G.Adj a b → H.Adj a b := by
    let a' : ↥((W : Set V)ᶜ) := ⟨a,ha⟩
    let b' : ↥((W : Set V)ᶜ) := ⟨b,hb⟩
    exact (Iff.of_eq (congrArg (fun J : SimpleGraph ↥((W : Set V)ᶜ) => J.Adj a' b') hCore)).mpr
  have hWloss : (W.card:ℝ) ≤ (4*ν/2)*(n:ℝ) := by
    push_cast at hSmall
    have hNonneg : 0 ≤ (Aᶜ.card:ℝ) := Nat.cast_nonneg _
    linarith only [hSmall,hNonneg,Nat.cast_nonneg (α := ℝ) W.card]
  have hRobH := real_robust_of_unchanged_outside_set G H W (4*ν) σ hOutsideEdges hWloss hRob
  rw [show 4*ν/2 = 2*ν by ring] at hRobH
  have hCompsR : (Xᶜ.card:ℝ) ≤ ((Aᶜ.card+W.card:ℕ):ℝ) := by exact_mod_cast hComps
  exact hUncolourable (hUse H X B hSizeX hDensH hSupportH (fun v => (hX v).mp)
    inter_subset_right hOrdH hWeakH hProfileH hNoH hRobH
    ((mul_le_mul_of_nonneg_left hCompsR (by norm_num)).trans hSmall)
    ((mul_le_mul_of_nonneg_left hCompsR (by norm_num)).trans hSmallτ))

end OverfullWork.CanonicalRegularization
