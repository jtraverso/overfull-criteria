module

public import OverfullWork.KuhnOsthusParityRoutingScales
public import OverfullWork.KuhnOsthusParityWindingFactors

@[expose] public section


/-! Construct the parity reserve on the original graph after deleting
the earlier reserves. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs InducedDigraphSampling
open scoped Classical
universe u

set_option maxHeartbeats 850000 in
/-- The seven-interval factors in the physical complement supply
the packets of Lemma 10.5. The ordinary parity reserve is then
built in the complement of those very same original arcs. -/
theorem kuhn_osthus_parity_reserve_from_original_factors (q : ℕ) (hq : 15 ≤ q)
    (ε₀ ε ε' θ δ₁ δ₂ δ₃ d a : ℝ)
    (hε₀ : 0 < ε₀) (hε₀₁ : ε₀ ≤ 1) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hε' : 0 < ε') (hε'₁ : ε' ≤ 1) (ha : 0 ≤ a)
    (hClean : 2*(ε₀+a) ≤ ε) (hCycle : 2*(ε+a) ≤ ε')
    (hθ : 4*ε ≤ θ) (hGapθ : 2*θ < d) (hGap' : 2*ε' < d) (hd : d ≤ 1)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃)
    (hδ₁₁ : δ₁ ≤ 1) (hδ₂₁ : δ₂ ≤ 1) (hδ₃₁ : δ₃ ≤ 1)
    (hGap₁ : 2*δ₁ < d) (hGap₂ : 2*δ₂ < d) (hGap₃ : 2*δ₃ < d)
    (hTol₁ : 2*(ε₀+a) ≤ δ₁) (hTol₂ : 2*(δ₁+a) ≤ δ₂) (hTol₃ : 2*(δ₂+a) ≤ δ₃)
    (hRouteMargin : 28*θ < (d-2*θ)^14*(d-θ))
    (hTolerance : ∀ ξ ∈ ({ε,ε',δ₁,δ₂,δ₃}:Finset ℝ), ξ ≤ θ) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {n m : ℕ}
      (G C : Digraph V) (Z : Finset V) (c : ↥Zᶜ → Fin (14*q))
      (_hC : C ≤ G) (_hm : 0 < m) (_hNm : N ≤ 2*m)
      (loss : ℕ) (εInitial εAfter εBase : ℝ)
      (_hBound : ∀ x ∉ Z, inDegree C x ≤ loss ∧ outDegree C x ≤ loss)
      (_hAfter : 0 < εAfter) (_hAfter₁ : εAfter ≤ 1)
      (_hBase : 0 < εBase) (_hBase₁ : εBase ≤ 1)
      (_hTolAfter : 2*(εInitial+a) ≤ εAfter) (_hTolBase : 2*(εAfter+a) ≤ εBase)
      (_hTol : 2*(εBase+a) ≤ ε₀)
      (_hPayAfter : (loss:ℝ) ≤ a*(((2*m:ℕ):ℝ)*εAfter))
      (_hPayBase : (n:ℝ) ≤ a*(((2*m:ℕ):ℝ)*εBase))
      (_hLoss : ((n*6:ℕ):ℝ) ≤ a*(((2*m:ℕ):ℝ)*ε₀))
      (_hLossε : 1 ≤ a*(((2*m:ℕ):ℝ)*ε))
      (_hLossε' : 3 ≤ a*(((2*m:ℕ):ℝ)*ε'))
      (_hLoss₁ : 3 ≤ a*(((2*m:ℕ):ℝ)*δ₁))
      (_hLoss₂ : 1 ≤ a*(((2*m:ℕ):ℝ)*δ₂)) (_hLoss₃ : 1 ≤ a*(((2*m:ℕ):ℝ)*δ₃)),
      let X (i : Fin (14*q)) := (univ : Finset ↥Zᶜ).filter (fun x => c x = i)
      let emb : ↥Zᶜ ↪ V := Function.Embedding.subtype _
      let idx : Fin (7*(2*q)) ≃ Fin (14*q) := finCongr (by omega)
      ∀ C₁ : Fin 1 × Fin (7*(2*q)) → Finset V,
      (∀ i, (univ : Finset (Fin 1)).biUnion (fun j => C₁ (j,i)) = (X (idx i)).map emb) →
      let U (j : Fin 1 × Fin 7) := (univ : Finset (Fin (2*q))).biUnion
        (fun i => C₁ (j.1,intervalPosition j.2 i))
      let S (j : Fin 1 × Fin 7) := C₁ (j.1,intervalPosition j.2 ⟨0,by omega⟩)
      let next := (Equiv.refl (Fin 1)).prodCongr (finRotate 7)
      let e := (exceptionalCoordinates Z).toEmbedding
      ∀ (F : Fin n → ∀ j, OriginalInterval (G \ C) Z (U j ∪ S (next j)) (S j) (S (next j))),
        (∀ i, (X i).card = 2*m) →
        (∀ i, IsLowerSuperregularPair (induced G Zᶜ) εInitial d (X i) (X (finRotate (14*q) i))) →
        Pairwise (fun i j => Disjoint (⨆ v, (F i v).digraph) (⨆ v, (F j v).digraph)) →
        ∃ (P : Fin n → Digraph (↥Zᶜ ⊕ ↥Z)) (L : Fin n → Fin 7 → Digraph (↥Zᶜ ⊕ ↥Z))
          (T : Digraph ↥Zᶜ),
          let E := pullDirectedPair e e (⨆ i, ⨆ j, (F i j).digraph)
          (∀ j, P j ≤ pullDirectedPair e e (G \ C) ∧ AbsorbsWindingFactor X (P j) (L j)) ∧
          Pairwise (fun j l => Disjoint (P j) (P l)) ∧
          (⨆ j, P j) = liftOrdinaryCycleArcs (↥Z) T ⊔ E ∧
          liftOrdinaryCycleArcs (↥Z) T ≤ pullDirectedPair e e (G \ C) \ E ∧
          (∀ x, inDegree T x = 5*n ∧ outDegree T x = 5*n) ∧
          ∀ v, let d := match v with | .inl _ => 6*n | .inr _ => 7*n
            inDegree (⨆ j, P j) v = d ∧ outDegree (⨆ j, P j) v = d := by
  obtain ⟨N,hN⟩ := kuhn_osthus_parity_reserve_after_chord_deletion.{u,u} q hq
    ε₀ ε ε' θ δ₁ δ₂ δ₃ d a hε₀ hε₀₁ hε hε₁ hε' hε'₁ ha hClean hCycle hθ hGapθ hGap' hd
    hδ₁ hδ₂ hδ₃ hδ₁₁ hδ₂₁ hδ₃₁ hGap₁ hGap₂ hGap₃ hTol₁ hTol₂ hTol₃
  obtain ⟨R,hR⟩ := exists_parity_routing_cutoffs d θ (by linarith only [hθ,hε]) hGapθ hRouteMargin
  refine ⟨max N (2*R),?_⟩
  intro V _ n m G C Z c hC hm hNm loss εInitial εAfter εBase hBound
    hAfter hAfter₁ hBase hBase₁ hTolAfter hTolBase hTol hPayAfter hPayBase hLoss hLossε hLossε'
    hLoss₁ hLoss₂ hLoss₃ X emb idx C₁ hCover₁ U S next e F hSize hPairs hF
  have hC₁ : C₁ = fun j => (X (idx j.2)).map emb := unrefined_winding_cells _ _ hCover₁
  subst C₁
  have hNm' : N ≤ 2*m := (le_max_left _ _).trans hNm
  have hRm : R ≤ m := by have h := (le_max_right N (2*R)).trans hNm; omega
  obtain ⟨s,r,hs,hr,hCutθ,hRouteθ,hCut⟩ := hR m hm hRm
  have hk : 0 < 14*q := by omega
  have hCover (x : ↥Zᶜ) : ∃ i, x ∈ X i := ⟨c x,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
  have hDis (i j : Fin (14*q)) (hij : i ≠ j) : Disjoint (X i) (X j) :=
    disjoint_left.mpr (fun x hi hj => hij (((mem_filter.mp hi).2).symm.trans (mem_filter.mp hj).2))
  let A := cyclicCluster X hk
  let B := cyclicCluster (rotateClusterArray X hk (7*q)) hk
  let G' := pullDirectedPair e e G
  let C' := pullDirectedPair e e C
  have : Nonempty ↥Zᶜ := ⟨(card_pos.mp (by rw [hSize (⟨0,hk⟩ : Fin (14*q))]; omega)).choose⟩
  obtain ⟨E,hE,hDisE,hDegreeE⟩ := parity_packets_of_original_winding_factors Z X
    (by omega : 0 < q) hCover hDis hSize F hF
  change (Fin n → ParityExceptionalPacket (G' \ C') A q) at E
  change (⨆ i, (E i).original) = pullDirectedPair e e (⨆ i, ⨆ j, (F i j).digraph) at hE
  change Pairwise (fun i j => Disjoint (E i).original (E j).original) at hDisE
  change ∀ v, let d := match v with | .inl _ => n | .inr _ => 7*n
    inDegree (⨆ j, (E j).original) v = d ∧ outDegree (⨆ j, (E j).original) v = d at hDegreeE
  have hLift : liftDirectedPair e e C' = C := by
    ext x y
    obtain ⟨u,rfl⟩ := (exceptionalCoordinates Z).surjective x
    obtain ⟨v,rfl⟩ := (exceptionalCoordinates Z).surjective y
    exact liftDirectedPair_adj e e C' u v
  have hBound' (x : ↥Zᶜ) : inDegree C' (.inl x) ≤ loss ∧ outDegree C' (.inl x) ≤ loss := by
    have hi := lift_pair_semidegree e e C' false (.inl x)
    have ho := lift_pair_semidegree e e C' true (.inl x)
    change inDegree (liftDirectedPair e e C') (e (.inl x)) = inDegree C' (.inl x) at hi
    change outDegree (liftDirectedPair e e C') (e (.inl x)) = outDegree C' (.inl x) at ho
    rw [hLift] at hi ho
    rw [←hi,←ho]
    exact hBound x.val (mem_compl.mp x.prop)
  let eA : Fin (2*m) ≃ A 0 := (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]; exact hSize _)).symm
  let eB : Fin (2*m) ≃ B 0 := (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]; exact hSize _)).symm
  obtain ⟨P,T,hP,hDisP,hSplit,hT,hRegT,hRegP⟩ := hN G' C' X (fun _ _ h => hC h) hm hNm' hCover
    hDis hSize loss εInitial εAfter εBase hBound' hAfter hAfter₁ hBase hBase₁ hTolAfter hTolBase hTol
    hPayAfter hPayBase hPairs hLoss hLossε hLossε' hLoss₁ hLoss₂ hLoss₃ s r hs hr hCutθ hRouteθ
    (fun ξ hξ => (hCut ξ (hTolerance ξ hξ)).1) (fun ξ hξ => (hCut ξ (hTolerance ξ hξ)).2)
    E eA eB hDisE (fun v => by cases v <;> exact hDegreeE _)
  rw [hE] at hSplit hT
  exact ⟨P,(fun j => (E j).absorptionOrder),T,(fun j => (hP j).2),hDisP,hSplit,hT,hRegT,
    fun v => by cases v <;> exact hRegP _⟩

end OverfullWork.DirectedRobustExpansion
