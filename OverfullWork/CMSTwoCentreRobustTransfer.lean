module

public import OverfullWork.CMSTwoCentreBaseImage
public import OverfullWork.RealRobustExpansion

@[expose] public section


/-! The two-group quotient retains all edges between ordinary vertices.
The loss in the robust neighbourhood is bounded by the deleted vertices
and the two exceptional labels. -/
namespace OverfullWork.TwoIndependentIdentifications

open Finset SimpleGraph PrunedCore RobustExpansion TwoCentreOrdinaryCore
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1800000 in
theorem real_robust_two_identifications (G : SimpleGraph V) [DecidableRel G.Adj]
    (Z A : Finset V) (hA : A ⊆ Z) (hInd : G.IsIndepSet (Z : Set V))
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ) (hτHalf : τ ≤ 1/2) :
    let n := Fintype.card V
    let m := Fintype.card (Vertices Z)
    2 ≤ Z.card →
    τ*(n:ℝ)+2 ≤ (2*τ)*(m:ℝ) →
    (Z.card:ℝ)+2 ≤ (ν/2)*(n:ℝ) →
    IsRealRobust G ν τ →
    IsRealRobust (graph G Z A hA hInd).supportGraph (ν/2) (2*τ) := by
  intro n m hZ hLength hLoss hRob
  let M := graph G Z A hA hInd
  have hm : m ≤ n := by
    dsimp only [m]
    rw [card_vertices]
    have hC := card_add_card_compl Z
    omega
  have hmR : (m:ℝ) ≤ n := by exact_mod_cast hm
  intro S hSLo hSHi
  let T : Finset V := (ordinaryVertices S).image Subtype.val
  have hT : T.card = (ordinaryVertices S).card := card_image_of_injective _ Subtype.val_injective
  have hSSize : T.card ≤ S.card ∧ S.card ≤ T.card+2 := by
    have hh := card_split S
    rw [←hT] at hh
    split_ifs at hh with h₁ h₂ <;> omega
  have hSSizeR : (T.card:ℝ) ≤ S.card ∧ (S.card:ℝ) ≤ T.card+2 := by
    exact ⟨by exact_mod_cast hSSize.1, by exact_mod_cast hSSize.2⟩
  have hTLo : τ*(n:ℝ) ≤ (T.card:ℝ) := by
    change (2*τ)*(m:ℝ) ≤ S.card at hSLo
    linarith only [hLength,hSSizeR.2,hSLo]
  have hTHi : (T.card:ℝ) ≤ (1-τ)*(n:ℝ) := by
    change (S.card:ℝ) ≤ (1-2*τ)*(m:ℝ) at hSHi
    have hScale := mul_le_mul_of_nonneg_left hmR (by linarith only [hτHalf] : 0 ≤ 1-2*τ)
    have hPlus := mul_nonneg hτ (Nat.cast_nonneg (α := ℝ) n)
    linarith only [hSSizeR.1,hSHi,hScale,hPlus]
  let R := realNeighbourhood G ν T
  have hExpand : (T.card:ℝ)+ν*(n:ℝ) ≤ R.card := hRob T hTLo hTHi
  let F : Finset (Outside Z) := univ.filter (fun x => x.val ∈ R)
  have hRImage : F.image Subtype.val = R \ Z := by
    ext v
    simp only [F,mem_image,mem_filter,mem_univ,true_and,mem_sdiff]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨hx,x.property⟩
    · rintro ⟨hv,hvZ⟩
      exact ⟨⟨v,hvZ⟩,hv,rfl⟩
  have hFB : R.card ≤ F.card+Z.card := by
    have hSplit := card_sdiff_add_card_inter R Z
    rw [←hRImage,card_image_of_injective _ Subtype.val_injective] at hSplit
    have hCap : (R∩Z).card ≤ Z.card := card_le_card inter_subset_right
    omega
  have hNbr (x : Outside Z) :
      neighboursIn G T x.val ≤ neighboursIn M.supportGraph S (Sum.inr x) := by
    let P := (ordinaryVertices S).filter (fun z => G.Adj x.val z.val)
    have hEq : P.image Subtype.val = T.filter (G.Adj x.val) := by
      ext v
      simp only [P,T,mem_image,mem_filter]
      constructor
      · rintro ⟨z,⟨hz,hxz⟩,rfl⟩
        exact ⟨⟨z,hz,rfl⟩,hxz⟩
      · rintro ⟨⟨z,hz,rfl⟩,hxz⟩
        exact ⟨z,⟨hz,hxz⟩,rfl⟩
    have hSub : P.image (Sum.inr : Outside Z → Vertices Z) ⊆
        S.filter (M.supportGraph.Adj (Sum.inr x)) := by
      intro w hw
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hw
      obtain ⟨hyS,hxy⟩ := mem_filter.mp hy
      refine mem_filter.mpr ⟨(mem_filter.mp hyS).2,?_⟩
      change 0 < (graph G Z A hA hInd).mult s(Sum.inr x,Sum.inr y)
      rw [mult_inr_inr,if_pos hxy]
      decide
    rw [neighboursIn_eq_filter_card,neighboursIn_eq_filter_card,←hEq,
      card_image_of_injective _ Subtype.val_injective]
    have h := card_le_card hSub
    rw [card_image_of_injective _ (fun _ _ h => Sum.inr.inj h)] at h
    exact h
  have hFSub : F.image (Sum.inr : Outside Z → Vertices Z) ⊆ realNeighbourhood M.supportGraph (ν/2) S := by
    intro w hw
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hw
    have hxR : x.val ∈ R := (mem_filter.mp hx).2
    have hNeigh := (mem_filter.mp hxR).2
    change ν*(n:ℝ) ≤ (neighboursIn G T x.val:ℝ) at hNeigh
    have hScale : (ν/2)*(m:ℝ) ≤ ν*(n:ℝ) := by
      have h := mul_le_mul_of_nonneg_left hmR (by positivity : 0 ≤ ν/2)
      linarith only [h,mul_nonneg hν (Nat.cast_nonneg (α := ℝ) n)]
    have hNbrR : (neighboursIn G T x.val:ℝ) ≤ neighboursIn M.supportGraph S (Sum.inr x) := by
      exact_mod_cast hNbr x
    exact mem_filter.mpr ⟨mem_univ _,hScale.trans (hNeigh.trans hNbrR)⟩
  have hCount := card_le_card hFSub
  rw [card_image_of_injective _ (fun _ _ h => Sum.inr.inj h)] at hCount
  have hCountR : (F.card:ℝ) ≤ (realNeighbourhood M.supportGraph (ν/2) S).card := by exact_mod_cast hCount
  have hFBR : (R.card:ℝ) ≤ F.card+Z.card := by exact_mod_cast hFB
  have hM := mul_le_mul_of_nonneg_left hmR (by positivity : 0 ≤ ν/2)
  change (S.card:ℝ)+(ν/2)*(m:ℝ) ≤ (realNeighbourhood M.supportGraph (ν/2) S).card
  linarith only [hExpand,hCountR,hFBR,hSSizeR.2,hLoss,hM]

end OverfullWork.TwoIndependentIdentifications
