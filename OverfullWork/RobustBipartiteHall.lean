module

public import OverfullWork.RobustExpansionDeletion
public import OverfullWork.BipartiteRobustMargin
public import OverfullWork.ExceptionalHall

@[expose] public section


/-! # Hall after bounded vertex and edge deletions in a robust bipartite graph

Small sets use minimum degree; middle sets use the original robust
expansion; large sets use minimum degree on the other side. This is the
matching argument in CMS Case 2 Step 4 after covering the anchors.
-/
namespace OverfullWork.RobustBipartiteHall
open SimpleGraph Finset PrunedCore RobustExpansion BipartiteRobustMargin
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

theorem hall_after_deletions (G F : SimpleGraph V) (A U B : Finset V) (r cutoff : ℕ)
    (hRobust : IsBipartiteRobustAt G A r cutoff) (hU : U ⊆ A) (hB : B ⊆ Aᶜ)
    (hEqual : U.card=B.card) (hVertexLoss : (Aᶜ\B).card ≤ r)
    (hEdgeLoss : ∀ v ∈ B, F.degree v < r)
    (hMinLeft : ∀ x ∈ U, cutoff ≤ neighboursIn (G\F) B x)
    (hMinRight : ∀ y ∈ B, cutoff ≤ neighboursIn (G\F) U y) :
    ∀ X : Finset V, X ⊆ U → X.card ≤ (B.filter (fun y => ∃ x ∈ X, (G\F).Adj x y)).card := by
  intro X hX
  let N := B.filter (fun y => ∃ x ∈ X, (G\F).Adj x y)
  change X.card ≤ N.card
  by_cases hSmall : X.card < cutoff
  · rcases X.eq_empty_or_nonempty with hEmpty|⟨x,hx⟩
    · simp only [hEmpty,card_empty,Nat.zero_le]
    · have hCount := hMinLeft x (hX hx)
      have hSub : B.filter (fun y => (G\F).Adj x y) ⊆ N := by
        intro y hy
        exact mem_filter.mpr ⟨(mem_filter.mp hy).1,x,hx,(mem_filter.mp hy).2⟩
      rw [neighboursIn_eq_filter_card] at hCount
      have hh := card_le_card hSub
      omega
  by_cases hWindow : X.card+cutoff ≤ A.card
  · let R := neighbours G Aᶜ r X
    have hGrow := hRobust.1 X (hX.trans hU) (by omega) hWindow
    have hSurvive : R ∩ B ⊆ N := by
      intro y hy
      obtain ⟨hyR,hyB⟩ := mem_inter.mp hy
      have hMany := (mem_filter.mp hyR).2
      have hLoss := neighboursIn_le_sdiff_add_degree G F X y
      have hFew := hEdgeLoss y hyB
      have hPos : 0 < neighboursIn (G\F) X y := by omega
      rw [neighboursIn_eq_filter_card] at hPos
      obtain ⟨x,hx⟩ := card_pos.mp hPos
      exact mem_filter.mpr ⟨hyB,x,(mem_filter.mp hx).1,((mem_filter.mp hx).2).symm⟩
    have hRemoved : R\B ⊆ Aᶜ\B := by
      intro y hy
      exact mem_sdiff.mpr ⟨(mem_filter.mp (mem_sdiff.mp hy).1).1,(mem_sdiff.mp hy).2⟩
    have hRemovedCard := (card_le_card hRemoved).trans hVertexLoss
    have hKept := card_le_card hSurvive
    have hSplit := card_sdiff_add_card_inter R B
    change X.card+r ≤ R.card at hGrow
    omega
  · by_contra hBad
    have hNsub : N ⊆ B := filter_subset _ _
    have hXcard : X.card ≤ U.card := card_le_card hX
    have hNcard : N.card < B.card := by omega
    have hRemaining : (B\N).Nonempty := by
      apply card_pos.mp
      have hh := card_sdiff_add_card_eq_card hNsub
      omega
    obtain ⟨y,hy⟩ := hRemaining
    obtain ⟨hyB,hyN⟩ := mem_sdiff.mp hy
    have hSub : U.filter (fun x => (G\F).Adj y x) ⊆ U\X := by
      intro x hx
      refine mem_sdiff.mpr ⟨(mem_filter.mp hx).1,?_⟩
      intro hxX
      exact hyN (mem_filter.mpr ⟨hyB,x,hxX,((mem_filter.mp hx).2).symm⟩)
    have hMin := hMinRight y hyB
    rw [neighboursIn_eq_filter_card] at hMin
    have hBound := hMin.trans (card_le_card hSub)
    have hSplit := card_sdiff_add_card_eq_card hX
    have hUcard := card_le_card hU
    omega

theorem exists_matching_after_deletions (G F : SimpleGraph V) (A U B : Finset V) (r cutoff : ℕ)
    (hRobust : IsBipartiteRobustAt G A r cutoff) (hU : U ⊆ A) (hB : B ⊆ Aᶜ)
    (hEqual : U.card=B.card) (hVertexLoss : (Aᶜ\B).card ≤ r)
    (hEdgeLoss : ∀ v ∈ B, F.degree v < r)
    (hMinLeft : ∀ x ∈ U, cutoff ≤ neighboursIn (G\F) B x)
    (hMinRight : ∀ y ∈ B, cutoff ≤ neighboursIn (G\F) U y) :
    ∃ f : ↥U ≃ ↥B, ∀ x : ↥U, (G\F).Adj x (f x) := by
  have hHall := hall_after_deletions G F A U B r cutoff hRobust hU hB hEqual hVertexLoss
    hEdgeLoss hMinLeft hMinRight
  let rel : ↥U → ↥B → Prop := fun x y => (G\F).Adj x y
  have hFiniteHall : ∀ S : Finset ↥U, S.card ≤ (univ.filter (fun y => ∃ x ∈ S, rel x y)).card := by
    intro S
    let X := S.image (fun x : ↥U => x.val)
    have hX : X ⊆ U := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
      exact y.property
    have hCard : X.card=S.card := card_image_of_injective _ Subtype.val_injective
    have hCount := hHall X hX
    have hEq : (univ.filter (fun y : ↥B => ∃ x ∈ S, rel x y)).card=
        (B.filter (fun y => ∃ x ∈ X, (G\F).Adj x y)).card := by
      apply card_bij (fun y _ => y.val)
      · intro y hy
        obtain ⟨x,hx,hxy⟩ := (mem_filter.mp hy).2
        exact mem_filter.mpr ⟨y.property,x.val,mem_image.mpr ⟨x,hx,rfl⟩,hxy⟩
      · intro y hy z hz he
        exact Subtype.ext he
      · intro y hy
        obtain ⟨hyB,x,hx,hxy⟩ := mem_filter.mp hy
        obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
        exact ⟨⟨y,hyB⟩,mem_filter.mpr ⟨mem_univ _,z,hz,hxy⟩,rfl⟩
    rw [hEq]
    omega
  obtain ⟨f,hf,hRel⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective rel).mp hFiniteHall
  have hCards : Fintype.card ↥U=Fintype.card ↥B := by simpa only [Fintype.card_coe] using hEqual
  have hBij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hCards⟩
  exact ⟨Equiv.ofBijective f hBij,hRel⟩

end OverfullWork.RobustBipartiteHall
