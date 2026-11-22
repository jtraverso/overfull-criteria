module

public import OverfullWork.KuhnOsthusParityExtendedBlock
public import OverfullWork.KuhnOsthusParityBlockIteration

@[expose] public section


/-! Iterate the physical parity extension starting from the seven
projected exceptional covers and their original arcs for each block. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u v
variable {V : Type u} {Z : Type v}

/-- The seven canonical exceptional intervals and their actual
two-arc expansions in the original graph. -/
structure ParityExceptionalPacket (D : Digraph (V ⊕ Z)) (A : ℕ → Finset V) (q : ℕ) where
  projectedHost : Digraph V
  middle : CycleAbsorberExceptionalCovers projectedHost A q
  first : IntervalPathCover projectedHost (clusterIntervalVertices A 0 (2*q)) (A 0) (A (2*q))
  sixth : IntervalPathCover projectedHost (clusterIntervalVertices A (10*q) (12*q)) (A (10*q)) (A (12*q))
  seventh : IntervalPathCover projectedHost (clusterIntervalVertices A (12*q) (14*q)) (A (12*q)) (A (14*q))
  paths₁ : ProjectedExceptionalArcs D first.digraph (id : Z → Z)
  paths₂ : ProjectedExceptionalArcs D middle.second.digraph (id : Z → Z)
  paths₃ : ProjectedExceptionalArcs D middle.third.digraph (id : Z → Z)
  paths₄ : ProjectedExceptionalArcs D middle.fourth.digraph (id : Z → Z)
  paths₅ : ProjectedExceptionalArcs D middle.fifth.digraph (id : Z → Z)
  paths₆ : ProjectedExceptionalArcs D sixth.digraph (id : Z → Z)
  paths₇ : ProjectedExceptionalArcs D seventh.digraph (id : Z → Z)

noncomputable def ParityExceptionalPacket.original {D : Digraph (V ⊕ Z)} {A : ℕ → Finset V} {q : ℕ}
    (P : ParityExceptionalPacket D A q) : Digraph (V ⊕ Z) :=
  (((P.paths₃.original ⊔ P.paths₅.original) ⊔ P.paths₄.original) ⊔ P.paths₂.original) ⊔
    (P.paths₆.original ⊔ P.paths₇.original ⊔ P.paths₁.original)

/-- Exceptional systems in the order of the seven output cycles. -/
noncomputable def ParityExceptionalPacket.absorptionOrder {D : Digraph (V ⊕ Z)} {A : ℕ → Finset V}
    {q : ℕ} (P : ParityExceptionalPacket D A q) : Fin 7 → Digraph (V ⊕ Z) :=
  ![P.paths₃.original,P.paths₅.original,P.paths₄.original,P.paths₂.original,
    P.paths₆.original,P.paths₇.original,P.paths₁.original]

/-- Lifting ordinary arcs into the original vertex set preserves inclusion. -/
theorem liftOrdinaryCycleArcs_mono (Z : Type v) {G H : Digraph V} (h : G ≤ H) :
    liftOrdinaryCycleArcs Z G ≤ liftOrdinaryCycleArcs Z H := by
  rintro (x | z) (y | w) he
  · exact h he
  · exact he
  · exact he
  · exact he

/-- A family of original parity blocks from prepared exceptional
packets and explicit routing margins. The iteration supplies the
ordinary residual for the whole physical construction in each round. -/
theorem kuhn_osthus_lemma_10_5_with_original_absorption (q : ℕ) (hq : 15 ≤ q)
    (ε₀ ε ε' θ δ₁ δ₂ δ₃ d a : ℝ)
    (hε₀ : 0 < ε₀) (hε₀₁ : ε₀ ≤ 1) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hε' : 0 < ε') (hε'₁ : ε' ≤ 1) (ha : 0 ≤ a)
    (hClean : 2*(ε₀+a) ≤ ε) (hCycle : 2*(ε+a) ≤ ε')
    (hθ : 4*ε ≤ θ) (hGapθ : 2*θ < d) (hGap' : 2*ε' < d) (hd : d ≤ 1)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃)
    (hδ₁₁ : δ₁ ≤ 1) (hδ₂₁ : δ₂ ≤ 1) (hδ₃₁ : δ₃ ≤ 1)
    (hGap₁ : 2*δ₁ < d) (hGap₂ : 2*δ₂ < d) (hGap₃ : 2*δ₃ < d)
    (hTol₁ : 2*(ε₀+a) ≤ δ₁) (hTol₂ : 2*(δ₁+a) ≤ δ₂) (hTol₃ : 2*(δ₂+a) ≤ δ₃) :
    ∃ N : ℕ, ∀ {V : Type u} {Z : Type v} [Fintype V] (D : Digraph (V ⊕ Z))
      (R : Digraph V) {n m : ℕ} (X : Fin (14*q) → Finset V)
      (hHost : liftOrdinaryCycleArcs Z R ≤ D) (hm : 0 < m) (hNm : N ≤ 2*m)
      (hCover : ∀ x, ∃ i, x ∈ X i) (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
      (hSize : ∀ i, (X i).card = 2*m)
      (εBase : ℝ) (hTol : 2*(εBase+a) ≤ ε₀)
      (hPairs : ∀ i, IsLowerSuperregularPair R εBase d (X i) (X (finRotate (14*q) i)))
      (hLoss : ((n*6:ℕ):ℝ) ≤ a*(((2*m:ℕ):ℝ)*ε₀))
      (hLossε : 1 ≤ a*(((2*m:ℕ):ℝ)*ε))
      (hLossε' : 3 ≤ a*(((2*m:ℕ):ℝ)*ε'))
      (hLoss₁ : 3 ≤ a*(((2*m:ℕ):ℝ)*δ₁))
      (hLoss₂ : 1 ≤ a*(((2*m:ℕ):ℝ)*δ₂)) (hLoss₃ : 1 ≤ a*(((2*m:ℕ):ℝ)*δ₃))
      (s r : ℕ) (hs : 0 < s) (hr : 0 < r)
      (hCutθ : (m:ℝ)*θ ≤ (s:ℝ))
      (hRouteθ : 28*((s:ℝ)+1) < (d-2*θ)^14*((d-θ)*(m:ℝ)))
      (hCut : ∀ ξ ∈ ({ε,ε',δ₁,δ₂,δ₃}:Finset ℝ), ((2*m:ℕ):ℝ)*ξ ≤ (r:ℝ))
      (hRoute : ∀ ξ ∈ ({ε,ε',δ₁,δ₂,δ₃}:Finset ℝ),
        28*((r:ℝ)+1) < (d-2*ξ)^14*((d-ξ)*((2*m:ℕ):ℝ))),
      let hk : 0 < 14*q := by omega
      let A := cyclicCluster X hk
      let B := cyclicCluster (rotateClusterArray X hk (7*q)) hk
      ∀ (E : Fin n → ParityExceptionalPacket D A q)
        (eTop : Fin (2*m) ≃ A 0) (_eLow : Fin (2*m) ≃ B 0),
        Pairwise (fun i j => Disjoint (E i).original (E j).original) →
        (∀ i, Disjoint (liftOrdinaryCycleArcs Z R) (E i).original) →
        ∃ P : Fin n → Digraph (V ⊕ Z),
          (∀ i, (E i).original ≤ P i ∧ P i ≤ D ∧
            ∃ M : Fin 6 → Equiv.Perm V, ordinaryCycleHost (P i) ≤ matchingUnion M ∧
              (∀ T₀ T₁ : Equiv.Perm V,
                Nonempty (ParityRepairConfiguration ![T₀,T₁,M 1,M 2,M 3,M 4,M 5])) ∧
              AbsorbsWindingFactor X (P i) (E i).absorptionOrder) ∧
          Pairwise (fun i j => Disjoint (P i) (P j)) := by
  obtain ⟨N,hN⟩ := kuhn_osthus_lemma_10_3_from_exceptional_covers.{u} q hq
    ε₀ ε ε' θ d a hε₀.le hε hε₁ hε' hε'₁ ha hClean hCycle hθ hGapθ hGap' hd
  refine ⟨N,?_⟩
  intro V Z _ D R n m X hHost hm hNm hCover hDis hSize εBase hTol hPairs
    hLoss hLossε hLossε' hLoss₁ hLoss₂ hLoss₃ s r hs hr hCutθ hRouteθ hCut hRoute
    hk A B E eTop eLow hApart hReserved
  let valid (i : Fin n) (P : Digraph (V ⊕ Z)) : Prop :=
    P ≤ D ∧ ∃ M : Fin 6 → Equiv.Perm V, ordinaryCycleHost P ≤ matchingUnion M ∧
      (∀ T₀ T₁ : Equiv.Perm V,
        Nonempty (ParityRepairConfiguration ![T₀,T₁,M 1,M 2,M 3,M 4,M 5])) ∧
      AbsorbsWindingFactor X P (E i).absorptionOrder
  have hLocal (i : Fin n) (T : Digraph V) (hT : T ≤ R)
      (hPairsT : ∀ j, IsLowerSuperregularPair T ε₀ d (X j) (X (finRotate (14*q) j))) :
      ∃ (P : Digraph (V ⊕ Z)) (M : Fin 6 → Equiv.Perm V),
        valid i P ∧ (E i).original ≤ P ∧
        P ≤ liftOrdinaryCycleArcs Z T ⊔ (E i).original ∧ ordinaryCycleHost P ≤ matchingUnion M := by
    let C := E i
    let S := liftOrdinaryCycleArcs Z T
    have hS : S ≤ D := (liftOrdinaryCycleArcs_mono Z hT).trans hHost
    obtain ⟨K⟩ := hN (G := T) X hm hNm hCover hDis hSize hPairsT hLossε hLossε'
      s hs hCutθ hRouteθ r hr (hCut ε (by simp)) (hCut ε' (by simp))
      (hRoute ε (by simp)) (hRoute ε' (by simp)) C.middle eTop eLow
    have hOriginal := K.restore_original_factors X hk hDis D (fun h => hS h)
      C.paths₂ C.paths₃ C.paths₄ C.paths₅
    have reserve {Q : Digraph (V ⊕ Z)} (hQ : Q ≤ C.original) : Disjoint S Q :=
      (hReserved i).mono (liftOrdinaryCycleArcs_mono Z hT) hQ
    have hRes₆ : Disjoint S C.paths₆.original := reserve
      (le_sup_left.trans (le_sup_left.trans le_sup_right))
    have hRes₇ : Disjoint S C.paths₇.original := reserve
      (le_sup_right.trans (le_sup_left.trans le_sup_right))
    have hRes₁ : Disjoint S C.paths₁.original := reserve (le_sup_right.trans le_sup_right)
    obtain ⟨B₁,B₂,B₃,M,hD,_,_,_,_,h6,h7,h1,hSupport,hBound,hConfig,hAbsorb⟩ :=
      NormalizedCycleAbsorber.exists_original_parity_extension_with_absorption (r := r) X hq hm hS hCover hDis hSize
        ε₀ δ₁ δ₂ δ₃ d a hδ₁ hδ₂ hδ₃ hδ₁₁ hδ₂₁ hδ₃₁ ha hGap₁ hGap₂ hGap₃ hd
        hTol₁ hLoss₁ hTol₂ hLoss₂ hTol₃ hLoss₃ hPairsT hr
        (hCut δ₁ (by simp)) (hCut δ₂ (by simp)) (hCut δ₃ (by simp))
        (hRoute δ₁ (by simp)) (hRoute δ₂ (by simp)) (hRoute δ₃ (by simp))
        K hOriginal C.sixth C.seventh C.first C.paths₆ C.paths₇ C.paths₁ hRes₆ hRes₇ hRes₁
    let F := liftOrdinaryCycleArcs Z K.mainOrdinary ⊔ (C.paths₃.original ⊔ C.paths₅.original)
    let U := liftOrdinaryCycleArcs Z K.upper.ordinary ⊔ C.paths₄.original
    let W := liftOrdinaryCycleArcs Z K.lower.ordinary ⊔ C.paths₂.original
    let L := F ⊔ U ⊔ W
    let P := L ⊔ B₁ ⊔ B₂ ⊔ B₃
    have hF : K.mainOrdinary ≤ T :=
      (sup_le (sup_le K.top.paths.unionPaths_le K.topTail.unionPaths_le)
        (sup_le K.low.paths.unionPaths_le K.lowTail.unionPaths_le)).trans (fun _ _ h => h.1)
    have hU : K.upper.ordinary ≤ T := K.upper.ordinary_le.trans (fun _ _ h => h.1.1)
    have hW : K.lower.ordinary ≤ T := K.lower_le.trans (fun _ _ h => h.1)
    have hL : L ≤ S ⊔ C.original := by
      intro x y h
      rcases h with ((h | h) | (h | h)) | (h | h)
      · exact .inl (liftOrdinaryCycleArcs_mono Z hF h)
      · exact .inr (.inl (.inl (.inl h)))
      · exact .inl (liftOrdinaryCycleArcs_mono Z hU h)
      · exact .inr (.inl (.inl (.inr h)))
      · exact .inl (liftOrdinaryCycleArcs_mono Z hW h)
      · exact .inr (.inl (.inr h))
    have hKeep : C.original ≤ P := by
      intro x y h
      rcases h with (((h | h) | h) | h) | ((h | h) | h)
      · exact .inl (.inl (.inl (.inl (.inl (.inr (.inl h))))))
      · exact .inl (.inl (.inl (.inl (.inl (.inr (.inr h))))))
      · exact .inl (.inl (.inl (.inl (.inr (.inr h)))))
      · exact .inl (.inl (.inl (.inr (.inr h))))
      · exact .inl (.inl (.inr (h6 h)))
      · exact .inl (.inr (h7 h))
      · exact .inr (h1 h)
    have hBound' : P ≤ S ⊔ C.original := by
      have he : P = L ⊔ (B₁ ⊔ B₂ ⊔ B₃) := by dsimp only [P]; ac_rfl
      rw [he]
      apply sup_le hL
      exact hSupport.trans (sup_le_sup
        (liftOrdinaryCycleArcs_mono Z (fun _ _ h => h.1)) le_sup_right)
    exact ⟨P,M,⟨hD,M,hBound,hConfig,hAbsorb⟩,hKeep,hBound',hBound⟩
  obtain ⟨P,hP,hDisP⟩ := exists_iterated_parity_blocks_of_cluster_pairs R X
    (fun i => (E i).original) valid hApart hReserved hm hSize εBase ε₀ d a hε₀ hε₀₁ ha
    (by linarith) hTol hLoss hPairs hLocal
  exact ⟨P,fun i => ⟨(hP i).2.1,(hP i).1.1,(hP i).1.2⟩,hDisP⟩

/-- The projected-packet construction with the original six-factor
budget and parity configuration. -/
theorem kuhn_osthus_lemma_10_5_from_projected_packets (q : ℕ) (hq : 15 ≤ q)
    (ε₀ ε ε' θ δ₁ δ₂ δ₃ d a : ℝ)
    (hε₀ : 0 < ε₀) (hε₀₁ : ε₀ ≤ 1) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hε' : 0 < ε') (hε'₁ : ε' ≤ 1) (ha : 0 ≤ a)
    (hClean : 2*(ε₀+a) ≤ ε) (hCycle : 2*(ε+a) ≤ ε')
    (hθ : 4*ε ≤ θ) (hGapθ : 2*θ < d) (hGap' : 2*ε' < d) (hd : d ≤ 1)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃)
    (hδ₁₁ : δ₁ ≤ 1) (hδ₂₁ : δ₂ ≤ 1) (hδ₃₁ : δ₃ ≤ 1)
    (hGap₁ : 2*δ₁ < d) (hGap₂ : 2*δ₂ < d) (hGap₃ : 2*δ₃ < d)
    (hTol₁ : 2*(ε₀+a) ≤ δ₁) (hTol₂ : 2*(δ₁+a) ≤ δ₂) (hTol₃ : 2*(δ₂+a) ≤ δ₃) :
    ∃ N : ℕ, ∀ {V : Type u} {Z : Type v} [Fintype V] (D : Digraph (V ⊕ Z))
      (R : Digraph V) {n m : ℕ} (X : Fin (14*q) → Finset V)
      (hHost : liftOrdinaryCycleArcs Z R ≤ D) (hm : 0 < m) (hNm : N ≤ 2*m)
      (hCover : ∀ x, ∃ i, x ∈ X i) (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
      (hSize : ∀ i, (X i).card = 2*m)
      (εBase : ℝ) (hTol : 2*(εBase+a) ≤ ε₀)
      (hPairs : ∀ i, IsLowerSuperregularPair R εBase d (X i) (X (finRotate (14*q) i)))
      (hLoss : ((n*6:ℕ):ℝ) ≤ a*(((2*m:ℕ):ℝ)*ε₀))
      (hLossε : 1 ≤ a*(((2*m:ℕ):ℝ)*ε))
      (hLossε' : 3 ≤ a*(((2*m:ℕ):ℝ)*ε'))
      (hLoss₁ : 3 ≤ a*(((2*m:ℕ):ℝ)*δ₁))
      (hLoss₂ : 1 ≤ a*(((2*m:ℕ):ℝ)*δ₂)) (hLoss₃ : 1 ≤ a*(((2*m:ℕ):ℝ)*δ₃))
      (s r : ℕ) (hs : 0 < s) (hr : 0 < r)
      (hCutθ : (m:ℝ)*θ ≤ (s:ℝ))
      (hRouteθ : 28*((s:ℝ)+1) < (d-2*θ)^14*((d-θ)*(m:ℝ)))
      (hCut : ∀ ξ ∈ ({ε,ε',δ₁,δ₂,δ₃}:Finset ℝ), ((2*m:ℕ):ℝ)*ξ ≤ (r:ℝ))
      (hRoute : ∀ ξ ∈ ({ε,ε',δ₁,δ₂,δ₃}:Finset ℝ),
        28*((r:ℝ)+1) < (d-2*ξ)^14*((d-ξ)*((2*m:ℕ):ℝ))),
      let hk : 0 < 14*q := by omega
      let A := cyclicCluster X hk
      let B := cyclicCluster (rotateClusterArray X hk (7*q)) hk
      ∀ (E : Fin n → ParityExceptionalPacket D A q)
        (eTop : Fin (2*m) ≃ A 0) (_eLow : Fin (2*m) ≃ B 0),
        Pairwise (fun i j => Disjoint (E i).original (E j).original) →
        (∀ i, Disjoint (liftOrdinaryCycleArcs Z R) (E i).original) →
        ∃ P : Fin n → Digraph (V ⊕ Z),
          (∀ i, (E i).original ≤ P i ∧ P i ≤ D ∧
            ∃ M : Fin 6 → Equiv.Perm V, ordinaryCycleHost (P i) ≤ matchingUnion M ∧
              ∀ T₀ T₁ : Equiv.Perm V,
                Nonempty (ParityRepairConfiguration ![T₀,T₁,M 1,M 2,M 3,M 4,M 5])) ∧
          Pairwise (fun i j => Disjoint (P i) (P j)) := by
  obtain ⟨N,hN⟩ := kuhn_osthus_lemma_10_5_with_original_absorption.{u,v}
    q hq ε₀ ε ε' θ δ₁ δ₂ δ₃ d a hε₀ hε₀₁ hε hε₁ hε' hε'₁ ha
    hClean hCycle hθ hGapθ hGap' hd hδ₁ hδ₂ hδ₃ hδ₁₁ hδ₂₁ hδ₃₁
    hGap₁ hGap₂ hGap₃ hTol₁ hTol₂ hTol₃
  refine ⟨N,?_⟩
  intro V Z _ D R n m X hHost hm hNm hCover hDis hSize εBase hTol hPairs
    hLoss hLossε hLossε' hLoss₁ hLoss₂ hLoss₃ s r hs hr hCutθ hRouteθ hCut hRoute
    hk A B E eTop eLow hApart hReserved
  obtain ⟨P,hP,hDisP⟩ := hN D R X hHost hm hNm hCover hDis hSize εBase hTol hPairs
    hLoss hLossε hLossε' hLoss₁ hLoss₂ hLoss₃ s r hs hr hCutθ hRouteθ hCut hRoute E eTop eLow hApart hReserved
  refine ⟨P,fun i => ?_,hDisP⟩
  obtain ⟨hE,hD,M,hBound,hConfig,_⟩ := hP i
  exact ⟨hE,hD,M,hBound,hConfig⟩

end OverfullWork.DirectedRobustExpansion
