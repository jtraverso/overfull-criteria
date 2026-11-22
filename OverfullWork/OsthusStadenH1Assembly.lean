module

public import OverfullWork.OsthusStadenH1Profile

@[expose] public section


/-! Build the thin reserves and establish (H1), starting with the
regular copies and the explicit reduced-degree estimates (6). -/
namespace OverfullWork.DirectedRegularPairs

open Finset DirectedRobustExpansion
open scoped Classical
universe u v w z

/-- Preserve the typical incidences of retained vertices in the main copies. -/
theorem exists_thin_reserves_with_h1_partition_and_good_main (β γ ε δ η ξ : ℝ)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hγ : 0 < γ) (hSum : 5*γ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ) (hδη : δ ≤ η/4)
    (hη : 0 < η) (hη1 : η ≤ 1) (hThin : 2*η ≤ γ*β)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {W : Type v} [Fintype W]
      {I : Type w} [Fintype I] {U : Type z} [Fintype U]
      (source target : I → U) (a : U → W ↪ V) (D : I → Digraph W)
      (t m : ℕ) (αnorm α e d : ℝ),
      t+m = Fintype.card W → N ≤ m →
      4*ε*(Fintype.card W:ℝ) ≤ ξ*(t:ℝ) →
      2*ε ≤ δ → (Fintype.card W:ℝ)*ε ≤ m →
      (Fintype.card W:ℝ)*ε ≤ (m:ℝ)*δ →
      2*ε*(Fintype.card W:ℝ)+(t:ℝ) ≤ δ*(m:ℝ) →
      (∀ i, IsCentredRegular (D i) ε β) →
      (∀ u v x y, a u x = a v y → u = v) →
      (∀ i j, i ≠ j → Disjoint (liftDirectedPair (a (source i)) (a (target i)) (D i))
        (liftDirectedPair (a (source j)) (a (target j)) (D j))) →
      (∀ s u, let J := incidentCopySet source target s u
        (α-4*d)*(Fintype.card U:ℝ) ≤ β*(J.card:ℝ) ∧
          β*(J.card:ℝ) ≤ (α+2*e)*(Fintype.card U:ℝ)) →
      α*(Fintype.card U:ℝ) ≤ αnorm → 8*αnorm ≤ 9*α*(Fintype.card U:ℝ) →
      3*α*(Fintype.card U:ℝ)/4 ≤ (1-ξ)*((α-4*d)*(Fintype.card U:ℝ)) →
      6*((α+2*e)*(Fintype.card U:ℝ)) ≤ 7*α*(Fintype.card U:ℝ) →
      4*ξ*((α+2*e)*(Fintype.card U:ℝ)) ≤ γ*β*(α*(Fintype.card U:ℝ)) →
      αnorm*(m:ℝ) = α*(Fintype.card V:ℝ) →
      ∃ kept : U → Fin m ↪ W, ∃ F : Fin 5 → I → Digraph (Fin m), ∃ R : I → Digraph (Fin m),
        let b := fun u => (kept u).trans (a u)
        let H := fun j => directedPairUnion (b ∘ source) (b ∘ target) (F j)
        (∀ j i, IsCentredRegular (F j i) η (γ*β)) ∧
        (∀ i, IsCentredRegular (R i) η ((1-5*γ)*β)) ∧
        (∀ j l, j ≠ l → Disjoint (H j) (H l)) ∧
        (∀ j, Disjoint (H j) (directedPairUnion (b ∘ source) (b ∘ target) R)) ∧
        (∀ j x y, (H j).Adj x y → (directedPairUnion (a ∘ source) (a ∘ target) D).Adj x y) ∧
        (∀ i x y, (D i).Adj (kept (source i) x) (kept (target i) y) ↔
          (R i).Adj x y ∨ ∃ j,(F j i).Adj x y) ∧
        (∀ j s u x, γ*α*(Fintype.card V:ℝ)/3 ≤ (pairSemidegree s (H j) (b u x):ℝ) ∧
          (pairSemidegree s (H j) (b u x):ℝ) ≤ 2*γ*α*(Fintype.card V:ℝ)) ∧
        ∀ s u x, ((atypicalIncidentCopies source target R η ((1-5*γ)*β) s u x).card:ℝ) ≤
          ξ*((incidentCopySet source target s u).card:ℝ) := by
  obtain ⟨N,hN⟩ := exists_five_regular_arc_reserves.{0} γ δ η hγ hSum hδ hδη hη hη1
  refine ⟨max N 1,?_⟩
  intro V _ W _ I _ U _ source target a D t m αnorm α e d hM hm hDel hReg hLarge hScale hDeg hD
    hSeparate hOldDis hCounts hA hALarge hLow hHigh hBad hNorm
  have hm_pos : 0 < m := (le_max_right N 1).trans hm
  have hn : 0 < Fintype.card W := by omega
  obtain ⟨K,hK,hGood⟩ := exists_retained_good_copy_profiles (copyEndpoint source target)
    D β ε ξ t hD hε hε1 hξ hn hDel
  have hCard (u : U) : Fintype.card (K u) = m := by rw [Fintype.card_coe,hK]; omega
  let kept (u : U) : Fin m ↪ W :=
    (Fintype.equivFinOfCardEq (hCard u)).symm.toEmbedding.trans (Function.Embedding.subtype _)
  have hMem (u : U) (x : Fin m) : kept u x ∈ K u :=
    ((Fintype.equivFinOfCardEq (hCard u)).symm x).property
  let b (u : U) := (kept u).trans (a u)
  let P (i : I) := pullDirectedPair (kept (source i)) (kept (target i)) (D i)
  have hP (i : I) : IsCentredRegular (P i) δ β :=
    centred_regular_pull_of_trim _ _ _ _ _ _ (hD i) hReg
      (by simpa only [Fintype.card_fin] using hLarge) (by simpa only [Fintype.card_fin] using hScale)
  have hLift (i : I) : liftDirectedPair (b (source i)) (b (target i)) (P i) ≤
      liftDirectedPair (a (source i)) (a (target i)) (D i) := by
    rintro v w ⟨x,y,hx,hy,h⟩
    exact ⟨kept (source i) x,kept (target i) y,hx,hy,h⟩
  have hDis (i j : I) (hij : i ≠ j) :
      Disjoint (liftDirectedPair (b (source i)) (b (target i)) (P i))
        (liftDirectedPair (b (source j)) (b (target j)) (P j)) :=
    (hOldDis i j hij).mono (hLift i) (hLift j)
  choose parts R hParts hR hPartDis hRDis hCover hPoint using fun i =>
    hN (P i) β (by simpa only [Fintype.card_fin] using ((le_max_left N 1).trans hm)) (hP i)
  let F (j : Fin 5) (i : I) := parts i j
  have hF (j : Fin 5) (i : I) : F j i ≤ P i := fun x y h => (hCover i x y).mpr (Or.inr ⟨j,h⟩)
  have hRP (i : I) : R i ≤ P i := fun x y h => (hCover i x y).mpr (Or.inl h)
  have hTypicalPull (s : Bool) (u : U) (x : Fin m) (i : I)
      (hu : copyEndpoint source target s i = u)
      (ht : |(pairSemidegree s (D i) (kept u x):ℝ)-β*(Fintype.card W:ℝ)| ≤ 2*ε*(Fintype.card W:ℝ)) :
      |(pairSemidegree s (P i) x:ℝ)-β*(Fintype.card (Fin m):ℝ)| ≤ δ*(Fintype.card (Fin m):ℝ) := by
    rw [←hu] at ht
    exact typical_semidegree_pull_of_trim _ _ _ s x β (2*ε) δ hβ.le hβ1
      (by simp only [Fintype.card_fin]; omega) (by cases s <;> exact ht)
      (by simp only [Fintype.card_fin,show Fintype.card W-m = t by omega]; exact hDeg)
  refine ⟨kept,F,R,fun j i => hParts i j,hR,?_,?_,?_,hCover,?_,?_⟩
  · intro j l hjl
    exact disjoint_directedPairUnions (b ∘ source) (b ∘ target) P _ _ (hF j) (hF l)
      (fun i => hPartDis i j l hjl) hDis
  · intro j
    exact disjoint_directedPairUnions (b ∘ source) (b ∘ target) P _ _ (hF j) hRP
      (fun i => hRDis i j) hDis
  · rintro j v w ⟨i,h⟩
    exact ⟨i,hLift i (liftDirectedPair_mono _ _ (hF j i) h)⟩
  · intro j
    let typical (s : Bool) (u : U) (x : Fin m) :=
      (incidentCopySet source target s u).filter (fun i =>
        |(pairSemidegree s (D i) (kept u x):ℝ)-β*(Fintype.card W:ℝ)| ≤ 2*ε*(Fintype.card W:ℝ))
    have hBudget s u x :
        let J := incidentCopySet source target s u
        let Q := typical s u x
        Q ⊆ J ∧ 2*αnorm ≤ 3*β*(Q.card:ℝ) ∧ 6*β*(J.card:ℝ) ≤ 7*αnorm ∧
          4*((J \ Q).card:ℝ) ≤ γ*αnorm := by
      let J := incidentCopySet source target s u
      let Q := typical s u x
      have hSub : Q ⊆ J := filter_subset _ _
      have hCompl : J \ Q = J.filter (fun i =>
        2*ε*(Fintype.card W:ℝ) < |(pairSemidegree s (D i) (kept u x):ℝ)-β*(Fintype.card W:ℝ)|) := by
        ext i
        simp only [Q,typical,J,mem_sdiff,mem_filter]
        by_cases hi : i ∈ incidentCopySet source target s u <;> simp [hi,not_le]
      have hFlags : ((J \ Q).card:ℝ) ≤ ξ*(J.card:ℝ) := by
        rw [hCompl]
        exact hGood s u (kept u x) (hMem u x)
      have hSize : ((J \ Q).card:ℝ) = (J.card:ℝ)-(Q.card:ℝ) := by
        rw [card_sdiff_of_subset hSub,Nat.cast_sub (card_le_card hSub)]
      have h := h1_budget_from_reduced_counts hβ hξ.le hξ1 hγ.le (hCounts s u).1 (hCounts s u).2
        (hSize ▸ hFlags) hA hALarge hLow hHigh hBad
      refine ⟨hSub,h.1,h.2.1,?_⟩
      rw [hSize]
      exact h.2.2
    have hTypical s u x i (hi : i ∈ typical s u x) :
        γ*β*(Fintype.card (Fin m):ℝ)/2 ≤ (pairSemidegree s (F j i) x:ℝ) ∧
        (pairSemidegree s (F j i) x:ℝ) ≤ 3*γ*β*(Fintype.card (Fin m):ℝ)/2 := by
      have hOld := hTypicalPull s u x i (mem_filter.mp (mem_filter.mp hi).1).2 (mem_filter.mp hi).2
      have hr : |(pairSemidegree s (F j i) x:ℝ)-γ*β*(Fintype.card (Fin m):ℝ)| ≤
          η*(Fintype.card (Fin m):ℝ) := by
        cases s
        · exact ((hPoint i x).1 hOld).1 j
        · exact ((hPoint i x).2 hOld).1 j
      have hScale := mul_le_mul_of_nonneg_right hThin (Nat.cast_nonneg (Fintype.card (Fin m)) : (0:ℝ) ≤ _)
      exact ⟨by linarith only [(abs_le.mp hr).1,hScale],by linarith only [(abs_le.mp hr).2,hScale]⟩
    have h := h1_profile_of_reserve_copies source target b (F j) β γ αnorm hβ.le hγ.le typical
      (fun u v x y he => hSeparate u v (kept u x) (kept v y) he)
      (fun i l hil => (hDis i l hil).mono (liftDirectedPair_mono _ _ (hF j i))
        (liftDirectedPair_mono _ _ (hF j l))) hBudget hTypical
    intro s u x
    have h' := h s u x
    simp only [Fintype.card_fin] at h'
    simpa only [mul_assoc, hNorm] using h'
  · intro s u x
    have hSub : atypicalIncidentCopies source target R η ((1-5*γ)*β) s u x ⊆
        atypicalIncidentCopies source target D ε β s u (kept u x) := by
      intro i hi
      obtain ⟨hInc,hBad⟩ := mem_filter.mp hi
      refine mem_filter.mpr ⟨hInc,?_⟩
      apply lt_of_not_ge
      intro hOld
      have hPull := hTypicalPull s u x i (mem_filter.mp hInc).2 hOld
      have hMain : |(pairSemidegree s (R i) x:ℝ)-((1-5*γ)*β)*(Fintype.card (Fin m):ℝ)| ≤
          η*(Fintype.card (Fin m):ℝ) := by
        cases s
        · exact ((hPoint i x).1 hPull).2
        · exact ((hPoint i x).2 hPull).2
      have hTwice : η*(Fintype.card (Fin m):ℝ) ≤ 2*η*(Fintype.card (Fin m):ℝ) := by
        have hNonneg : 0 ≤ η*(Fintype.card (Fin m):ℝ) := by positivity
        linarith only [hNonneg]
      exact (not_lt_of_ge (hMain.trans hTwice)) hBad
    exact (show ((atypicalIncidentCopies source target R η ((1-5*γ)*β) s u x).card:ℝ) ≤
        ((atypicalIncidentCopies source target D ε β s u (kept u x)).card:ℝ) by
      exact_mod_cast card_le_card hSub).trans (hGood s u (kept u x) (hMem u x))


theorem exists_thin_reserves_with_h1_and_partition (β γ ε δ η ξ : ℝ)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hγ : 0 < γ) (hSum : 5*γ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ) (hδη : δ ≤ η/4)
    (hη : 0 < η) (hη1 : η ≤ 1) (hThin : 2*η ≤ γ*β)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {W : Type v} [Fintype W]
      {I : Type w} [Fintype I] {U : Type z} [Fintype U]
      (source target : I → U) (a : U → W ↪ V) (D : I → Digraph W)
      (t m : ℕ) (αnorm α e d : ℝ),
      t+m = Fintype.card W → N ≤ m →
      4*ε*(Fintype.card W:ℝ) ≤ ξ*(t:ℝ) →
      2*ε ≤ δ → (Fintype.card W:ℝ)*ε ≤ m →
      (Fintype.card W:ℝ)*ε ≤ (m:ℝ)*δ →
      2*ε*(Fintype.card W:ℝ)+(t:ℝ) ≤ δ*(m:ℝ) →
      (∀ i, IsCentredRegular (D i) ε β) →
      (∀ u v x y, a u x = a v y → u = v) →
      (∀ i j, i ≠ j → Disjoint (liftDirectedPair (a (source i)) (a (target i)) (D i))
        (liftDirectedPair (a (source j)) (a (target j)) (D j))) →
      (∀ s u, let J := incidentCopySet source target s u
        (α-4*d)*(Fintype.card U:ℝ) ≤ β*(J.card:ℝ) ∧
          β*(J.card:ℝ) ≤ (α+2*e)*(Fintype.card U:ℝ)) →
      α*(Fintype.card U:ℝ) ≤ αnorm → 8*αnorm ≤ 9*α*(Fintype.card U:ℝ) →
      3*α*(Fintype.card U:ℝ)/4 ≤ (1-ξ)*((α-4*d)*(Fintype.card U:ℝ)) →
      6*((α+2*e)*(Fintype.card U:ℝ)) ≤ 7*α*(Fintype.card U:ℝ) →
      4*ξ*((α+2*e)*(Fintype.card U:ℝ)) ≤ γ*β*(α*(Fintype.card U:ℝ)) →
      αnorm*(m:ℝ) = α*(Fintype.card V:ℝ) →
      ∃ kept : U → Fin m ↪ W, ∃ F : Fin 5 → I → Digraph (Fin m), ∃ R : I → Digraph (Fin m),
        let b := fun u => (kept u).trans (a u)
        let H := fun j => directedPairUnion (b ∘ source) (b ∘ target) (F j)
        (∀ j i, IsCentredRegular (F j i) η (γ*β)) ∧
        (∀ i, IsCentredRegular (R i) η ((1-5*γ)*β)) ∧
        (∀ j l, j ≠ l → Disjoint (H j) (H l)) ∧
        (∀ j, Disjoint (H j) (directedPairUnion (b ∘ source) (b ∘ target) R)) ∧
        (∀ j x y, (H j).Adj x y → (directedPairUnion (a ∘ source) (a ∘ target) D).Adj x y) ∧
        (∀ i x y, (D i).Adj (kept (source i) x) (kept (target i) y) ↔
          (R i).Adj x y ∨ ∃ j,(F j i).Adj x y) ∧
        ∀ j s u x, γ*α*(Fintype.card V:ℝ)/3 ≤ (pairSemidegree s (H j) (b u x):ℝ) ∧
          (pairSemidegree s (H j) (b u x):ℝ) ≤ 2*γ*α*(Fintype.card V:ℝ) := by
  obtain ⟨N,hN⟩ := exists_thin_reserves_with_h1_partition_and_good_main.{u,v,w,z}
    β γ ε δ η ξ hβ hβ1 hγ hSum hε hε1 hδ hδη hη hη1 hThin hξ hξ1
  refine ⟨N,?_⟩
  intro V _ W _ I _ U _ source target a D t m αnorm α e d hM hm hDel hReg hLarge hScale hDeg hD
    hSeparate hOldDis hCounts hA hALarge hLow hHigh hBad hNorm
  obtain ⟨kept,F,R,hF,hR,hDis,hRDis,hSub,hCover,hProfiles,_⟩ :=
    hN source target a D t m αnorm α e d hM hm hDel hReg hLarge hScale hDeg hD
      hSeparate hOldDis hCounts hA hALarge hLow hHigh hBad hNorm
  exact ⟨kept,F,R,hF,hR,hDis,hRDis,hSub,hCover,hProfiles⟩

theorem exists_thin_reserves_with_h1 (β γ ε δ η α e d ξ : ℝ)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hγ : 0 < γ) (hSum : 5*γ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ) (hδη : δ ≤ η/4)
    (hη : 0 < η) (hη1 : η ≤ 1) (hThin : 2*η ≤ γ*β)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {W : Type v} [Fintype W]
      {I : Type w} [Fintype I] {U : Type z} [Fintype U]
      (source target : I → U) (a : U → W ↪ V) (D : I → Digraph W)
      (t m : ℕ) (αnorm : ℝ),
      t+m = Fintype.card W → N ≤ m →
      4*ε*(Fintype.card W:ℝ) ≤ ξ*(t:ℝ) →
      2*ε ≤ δ → (Fintype.card W:ℝ)*ε ≤ m →
      (Fintype.card W:ℝ)*ε ≤ (m:ℝ)*δ →
      2*ε*(Fintype.card W:ℝ)+(t:ℝ) ≤ δ*(m:ℝ) →
      (∀ i, IsCentredRegular (D i) ε β) →
      (∀ u v x y, a u x = a v y → u = v) →
      (∀ i j, i ≠ j → Disjoint (liftDirectedPair (a (source i)) (a (target i)) (D i))
        (liftDirectedPair (a (source j)) (a (target j)) (D j))) →
      (∀ s u, let J := incidentCopySet source target s u
        (α-4*d)*(Fintype.card U:ℝ) ≤ β*(J.card:ℝ) ∧
          β*(J.card:ℝ) ≤ (α+2*e)*(Fintype.card U:ℝ)) →
      α*(Fintype.card U:ℝ) ≤ αnorm → 8*αnorm ≤ 9*α*(Fintype.card U:ℝ) →
      3*α*(Fintype.card U:ℝ)/4 ≤ (1-ξ)*((α-4*d)*(Fintype.card U:ℝ)) →
      6*((α+2*e)*(Fintype.card U:ℝ)) ≤ 7*α*(Fintype.card U:ℝ) →
      4*ξ*((α+2*e)*(Fintype.card U:ℝ)) ≤ γ*β*(α*(Fintype.card U:ℝ)) →
      αnorm*(m:ℝ) = α*(Fintype.card V:ℝ) →
      ∃ kept : U → Fin m ↪ W, ∃ F : Fin 5 → I → Digraph (Fin m), ∃ R : I → Digraph (Fin m),
        let b := fun u => (kept u).trans (a u)
        let H := fun j => directedPairUnion (b ∘ source) (b ∘ target) (F j)
        (∀ j i, IsCentredRegular (F j i) η (γ*β)) ∧
        (∀ i, IsCentredRegular (R i) η ((1-5*γ)*β)) ∧
        (∀ j l, j ≠ l → Disjoint (H j) (H l)) ∧
        (∀ j, Disjoint (H j) (directedPairUnion (b ∘ source) (b ∘ target) R)) ∧
        (∀ j x y, (H j).Adj x y → (directedPairUnion (a ∘ source) (a ∘ target) D).Adj x y) ∧
        ∀ j s u x, γ*α*(Fintype.card V:ℝ)/3 ≤ (pairSemidegree s (H j) (b u x):ℝ) ∧
          (pairSemidegree s (H j) (b u x):ℝ) ≤ 2*γ*α*(Fintype.card V:ℝ) := by
  obtain ⟨N,hN⟩ := exists_thin_reserves_with_h1_and_partition.{u,v,w,z}
    β γ ε δ η ξ hβ hβ1 hγ hSum hε hε1 hδ hδη hη hη1 hThin hξ hξ1
  refine ⟨N,?_⟩
  intro V _ W _ I _ U _ source target a D t m αnorm hM hm hDel hReg hLarge hScale hDeg hD
    hSeparate hOldDis hCounts hA hALarge hLow hHigh hBad hNorm
  obtain ⟨kept,F,R,hF,hR,hDis,hRDis,hSub,_,hProfiles⟩ :=
    hN source target a D t m αnorm α e d hM hm hDel hReg hLarge hScale hDeg hD
      hSeparate hOldDis hCounts hA hALarge hLow hHigh hBad hNorm
  exact ⟨kept,F,R,hF,hR,hDis,hRDis,hSub,hProfiles⟩

end OverfullWork.DirectedRegularPairs
