module

public import OverfullWork.KuhnOsthusCycleAbsorberPhysical

@[expose] public section


/-! End-to-end construction of the cycle absorber from the cyclic
cluster pairs and the four projected complete exceptional systems
with their original path arcs. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u v
variable {V : Type u} {Z : Type v}

def ordinaryCycleHost (D : Digraph (V ⊕ Z)) : Digraph V :=
  ⟨fun x y => D.Adj (.inl x) (.inl y)⟩

/-- Kühn–Osthus Lemma 10.3 in the cluster and exceptional-path
coordinates used by the routing lemmas. The output includes the
ordered switch certificates, the exact original arc sets and both
unused repair pairs in the original host. -/
theorem kuhn_osthus_lemma_10_3_from_projected_systems (q : ℕ) (hq : 15 ≤ q)
    (ε₀ ε η θ d a : ℝ) (hε₀ : 0 ≤ ε₀) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hη : 0 < η) (hη₁ : η ≤ 1) (ha : 0 ≤ a)
    (hTol₀ : 2*(ε₀+a) ≤ ε) (hTol : 2*(ε+a) ≤ η)
    (hθ : 4*ε ≤ θ) (hGapθ : 2*θ < d) (hGapη : 2*η < d) (hd : d ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} {Z : Type v} [Fintype V] (D : Digraph (V ⊕ Z))
      {H : Digraph V} {m : ℕ}
      (X : Fin (14*q) → Finset V) (hm : 0 < m) (hNm : N ≤ 2*m)
      (hCover : ∀ v, ∃ i, v ∈ X i)
      (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
      (hSize : ∀ i, (X i).card = 2*m)
      (hPairs : ∀ i, IsLowerSuperregularPair (ordinaryCycleHost D) ε₀ d (X i) (X (finRotate (14*q) i)))
      (hDelete : 1 ≤ a*(((2*m:ℕ):ℝ)*ε))
      (hBudget : 3 ≤ a*(((2*m:ℕ):ℝ)*η))
      (s : ℕ) (hs : 0 < s) (hCutθ : (m:ℝ)*θ ≤ (s:ℝ))
      (hRouteθ : 28*((s:ℝ)+1) < (d-2*θ)^14*((d-θ)*(m:ℝ)))
      (r : ℕ) (hr : 0 < r) (hCutε : ((2*m:ℕ):ℝ)*ε ≤ (r:ℝ))
      (hCutη : ((2*m:ℕ):ℝ)*η ≤ (r:ℝ))
      (hRouteε : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ)))
      (_hRouteη : 28*((r:ℝ)+1) < (d-2*η)^14*((d-η)*((2*m:ℕ):ℝ))),
      let hk : 0 < 14*q := by omega
      let A := cyclicCluster X hk
      let B := cyclicCluster (rotateClusterArray X hk (7*q)) hk
      ∀ (E : CycleAbsorberExceptionalCovers H A q)
        (P₂ : ProjectedExceptionalArcs D E.second.digraph (id : Z → Z))
        (P₃ : ProjectedExceptionalArcs D E.third.digraph (id : Z → Z))
        (P₄ : ProjectedExceptionalArcs D E.fourth.digraph (id : Z → Z))
        (P₅ : ProjectedExceptionalArcs D E.fifth.digraph (id : Z → Z))
        (eTop : Fin (2*m) ≃ A 0) (eLow : Fin (2*m) ≃ B 0),
        ∃ C : NormalizedCycleAbsorber (G := ordinaryCycleHost D \ E.arcs) E eTop eLow,
          CycleAbsorberOriginalConclusion C D P₂ P₃ P₄ P₅ := by
  obtain ⟨N,hN⟩ := kuhn_osthus_lemma_10_3_from_exceptional_covers.{u} q hq
    ε₀ ε η θ d a hε₀ hε hε₁ hη hη₁ ha hTol₀ hTol hθ hGapθ hGapη hd
  refine ⟨N,?_⟩
  intro V Z _ D H m X hm hNm hCover hDis hSize hPairs hDelete hBudget s hs hCutθ hRouteθ
    r hr hCutε hCutη hRouteε hRouteη hk A B E P₂ P₃ P₄ P₅ eTop eLow
  obtain ⟨C⟩ := hN X hm hNm hCover hDis hSize hPairs hDelete hBudget s hs hCutθ hRouteθ
    r hr hCutε hCutη hRouteε hRouteη E eTop eLow
  exact ⟨C,C.restore_original_factors X hk hDis D (fun h => h) P₂ P₃ P₄ P₅⟩

/-- The deletion at the start of the parity reserve construction of
Lemma 10.5. On ordinary successor pairs, removing the original cycle
absorber costs at most three matchings. The host being trimmed can
already exclude original arcs reserved earlier. -/
theorem CycleAbsorberOriginalConclusion.residual_pair [Fintype V] {G H : Digraph V}
    {A B : ℕ → Finset V} {m q : ℕ} {E : CycleAbsorberExceptionalCovers H A q}
    {eTop : Fin (2*m) ≃ A 0} {eLow : Fin (2*m) ≃ B 0}
    {N : NormalizedCycleAbsorber (G := G \ E.arcs) E eTop eLow}
    {D : Digraph (V ⊕ Z)}
    {P₂ : ProjectedExceptionalArcs D E.second.digraph (id : Z → Z)}
    {P₃ : ProjectedExceptionalArcs D E.third.digraph (id : Z → Z)}
    {P₄ : ProjectedExceptionalArcs D E.fourth.digraph (id : Z → Z)}
    {P₅ : ProjectedExceptionalArcs D E.fifth.digraph (id : Z → Z)}
    (h : CycleAbsorberOriginalConclusion N D P₂ P₃ P₄ P₅)
    (R : Digraph (V ⊕ Z)) (U W : Finset V) (hm : 0 < m)
    (hU : U.card = 2*m) (hW : W.card = 2*m) (ε η d a : ℝ)
    (hη : 0 < η) (hη₁ : η ≤ 1) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hTol : 2*(ε+a) ≤ η) (hBudget : 3 ≤ a*(((2*m:ℕ):ℝ)*η))
    (hPair : IsLowerSuperregularPair (ordinaryCycleHost R) ε d U W) :
    let F := liftOrdinaryCycleArcs Z N.mainOrdinary ⊔ (P₃.original ⊔ P₅.original)
    let S := liftOrdinaryCycleArcs Z N.upper.ordinary ⊔ P₄.original
    let S' := liftOrdinaryCycleArcs Z N.lower.ordinary ⊔ P₂.original
    IsLowerSuperregularPair (ordinaryCycleHost (R \ (F ⊔ S ⊔ S'))) η d U W := by
  intro F S S'
  obtain ⟨_,_,_,_,_,_,hProject,_,_⟩ := h
  let M : Fin 3 → Equiv.Perm V := ![N.mainPermutation,N.upper.permutation,N.lower.permutation]
  have hBound : ordinaryCycleHost (F ⊔ S ⊔ S') ≤ matchingUnion M := by
    intro x y he
    rcases hProject x y he with (hf | hu) | hw
    · exact ⟨0,(N.exact_main _ _).mp hf⟩
    · exact ⟨1,(N.upper.exact_factor _ _).mp hu⟩
    · rw [← N.second_arcs] at hw
      exact ⟨2,(N.lower.exact_factor _ _).mp hw⟩
  change IsLowerSuperregularPair (ordinaryCycleHost R \ ordinaryCycleHost (F ⊔ S ⊔ S')) η d U W
  exact residual_pairs_after_matchings M hBound U W hm hU hW ε η d a hη hη₁ ha hd hTol
    (by simpa only [Nat.cast_ofNat] using hBudget) hPair

end OverfullWork.DirectedRobustExpansion
