module

public import OverfullWork.KuhnOsthusExceptionalFactorSequence
public import OverfullWork.KuhnOsthusParityFromOriginalFactors

@[expose] public section


/-! Apply Lemma 10.5 to the third call to Lemma 7.6. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs InducedDigraphSampling
open scoped Classical
universe u

set_option maxHeartbeats 850000 in
/-- With one style, the cover property identifies the style cells
with the parity clusters. Apply Lemma 10.5 without choosing new
exceptional arcs after preprocessing and chords have been removed. -/
theorem kuhn_osthus_parity_reserve_from_wound_pack (q : ℕ) (hq : 15 ≤ q)
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
      (Y : Fin (7*(2*q)) → Finset V) (loss : ℕ) (εInitial εAfter εBase σ : ℝ),
      let X (i : Fin (14*q)) := (univ : Finset ↥Zᶜ).filter (fun x => c x = i)
      let emb : ↥Zᶜ ↪ V := Function.Embedding.subtype _
      let idx : Fin (7*(2*q)) ≃ Fin (14*q) := finCongr (by omega)
      let e := (exceptionalCoordinates Z).toEmbedding
      C ≤ G → 0 < m → N ≤ 2*m →
      (∀ x ∉ Z, inDegree C x ≤ loss ∧ outDegree C x ≤ loss) →
      0 < εAfter → εAfter ≤ 1 → 0 < εBase → εBase ≤ 1 →
      2*(εInitial+a) ≤ εAfter → 2*(εAfter+a) ≤ εBase → 2*(εBase+a) ≤ ε₀ →
      (loss:ℝ) ≤ a*(((2*m:ℕ):ℝ)*εAfter) → (n:ℝ) ≤ a*(((2*m:ℕ):ℝ)*εBase) →
      ((n*6:ℕ):ℝ) ≤ a*(((2*m:ℕ):ℝ)*ε₀) →
      1 ≤ a*(((2*m:ℕ):ℝ)*ε) → 3 ≤ a*(((2*m:ℕ):ℝ)*ε') →
      3 ≤ a*(((2*m:ℕ):ℝ)*δ₁) → 1 ≤ a*(((2*m:ℕ):ℝ)*δ₂) →
      1 ≤ a*(((2*m:ℕ):ℝ)*δ₃) →
      (∀ i, Y i = (X (idx i)).map emb) →
      (∀ i, (X i).card = 2*m) →
      (∀ i, IsLowerSuperregularPair (induced G Zᶜ) εInitial d (X i) (X (finRotate (14*q) i))) →
      ∀ E : WoundFactorPacking (G \ C) Z Y (by omega) 1 (2*m) n σ,
        ∃ (P : Fin n → Digraph (↥Zᶜ ⊕ ↥Z)) (L : Fin n → Fin 7 → Digraph (↥Zᶜ ⊕ ↥Z))
          (T : Digraph ↥Zᶜ),
          let F := pullDirectedPair e e (⨆ i, ⨆ j, (E.factors i j).digraph)
          let PC := liftDirectedPair e e (⨆ i, P i)
          PC ≤ G \ C ∧ (⨆ i, ⨆ j, (E.factors i j).digraph) ≤ PC ∧
          (∀ x, let d := if x ∈ Z then 7*n else 6*n
            inDegree PC x = d ∧ outDegree PC x = d) ∧
          (∀ j, P j ≤ pullDirectedPair e e (G \ C) ∧ AbsorbsWindingFactor X (P j) (L j)) ∧
          Pairwise (fun j l => Disjoint (P j) (P l)) ∧
          (⨆ j, P j) = liftOrdinaryCycleArcs (↥Z) T ⊔ F ∧
          liftOrdinaryCycleArcs (↥Z) T ≤ pullDirectedPair e e (G \ C) \ F ∧
          (∀ x, inDegree T x = 5*n ∧ outDegree T x = 5*n) ∧
          ∀ v, let d := match v with | .inl _ => 6*n | .inr _ => 7*n
            inDegree (⨆ j, P j) v = d ∧ outDegree (⨆ j, P j) v = d := by
  obtain ⟨N,hN⟩ := kuhn_osthus_parity_reserve_from_original_factors.{u} q hq
    ε₀ ε ε' θ δ₁ δ₂ δ₃ d a hε₀ hε₀₁ hε hε₁ hε' hε'₁ ha hClean hCycle hθ hGapθ hGap' hd
    hδ₁ hδ₂ hδ₃ hδ₁₁ hδ₂₁ hδ₃₁ hGap₁ hGap₂ hGap₃ hTol₁ hTol₂ hTol₃ hRouteMargin hTolerance
  refine ⟨N,?_⟩
  intro V _ n m G C Z c Y loss εInitial εAfter εBase σ X emb idx e
    hC hm hNm hBound hAfter hAfter₁ hBase hBase₁ hTolAfter hTolBase hTol
    hPayAfter hPayBase hLoss hLossε hLossε' hLoss₁ hLoss₂ hLoss₃ hX hSize hPairs E
  obtain ⟨P,L,T,hP,hApart,hSplit,hT,hRegT,hRegP⟩ :=
    hN G C Z c hC hm hNm loss εInitial εAfter εBase hBound
      hAfter hAfter₁ hBase hBase₁ hTolAfter hTolBase hTol hPayAfter hPayBase
      hLoss hLossε hLossε' hLoss₁ hLoss₂ hLoss₃ E.cell (fun i => (E.cover i).trans (hX i))
      E.factors hSize hPairs E.apart
  refine ⟨P,L,T,?_,?_,?_,hP,hApart,hSplit,hT,hRegT,hRegP⟩
  · rintro x y ⟨u,v,rfl,rfl,h⟩
    obtain ⟨j,hj⟩ := Digraph.iSup_adj.mp h
    exact (hP j).1 hj
  · intro x y h
    obtain ⟨u,rfl⟩ := (exceptionalCoordinates Z).surjective x
    obtain ⟨v,rfl⟩ := (exceptionalCoordinates Z).surjective y
    refine ⟨u,v,rfl,rfl,?_⟩
    rw [hSplit]
    exact Or.inr h
  · intro x
    obtain ⟨v,rfl⟩ := (exceptionalCoordinates Z).surjective x
    have hi := lift_pair_semidegree e e (⨆ j, P j) false v
    have ho := lift_pair_semidegree e e (⨆ j, P j) true v
    change inDegree (liftDirectedPair e e (⨆ j, P j)) (e v) = _ ∧
      outDegree (liftDirectedPair e e (⨆ j, P j)) (e v) = _
    change inDegree (liftDirectedPair e e (⨆ j, P j)) (e v) = inDegree (⨆ j, P j) v at hi
    change outDegree (liftDirectedPair e e (⨆ j, P j)) (e v) = outDegree (⨆ j, P j) v at ho
    rw [hi,ho]
    cases v with
    | inl v =>
      change inDegree (⨆ j, P j) (.inl v) = (if v.val ∈ Z then 7*n else 6*n) ∧
        outDegree (⨆ j, P j) (.inl v) = (if v.val ∈ Z then 7*n else 6*n)
      rw [if_neg (mem_compl.mp v.prop)]
      exact hRegP (.inl v)
    | inr v =>
      change inDegree (⨆ j, P j) (.inr v) = (if v.val ∈ Z then 7*n else 6*n) ∧
        outDegree (⨆ j, P j) (.inr v) = (if v.val ∈ Z then 7*n else 6*n)
      rw [if_pos v.prop]
      exact hRegP (.inr v)

end OverfullWork.DirectedRobustExpansion
