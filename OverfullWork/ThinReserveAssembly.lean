module

public import OverfullWork.RegularPairArcPartition

@[expose] public section


/-! Realize the local thin parts of §5.2 as disjoint subdigraphs of
the host. Every local pair retains its exact arc identities. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset DirectedRegularPairs
open scoped Classical
universe u v w
variable {V : Type u} {W : Type v} {I : Type w}

def liftDirectedPair (a b : W ↪ V) (D : Digraph W) : Digraph V :=
  ⟨fun x y => ∃ s t, a s = x ∧ b t = y ∧ D.Adj s t⟩

theorem liftDirectedPair_adj (a b : W ↪ V) (D : Digraph W) (s t : W) :
    (liftDirectedPair a b D).Adj (a s) (b t) ↔ D.Adj s t := by
  constructor
  · rintro ⟨x,y,hx,hy,h⟩
    cases a.injective hx
    cases b.injective hy
    exact h
  · exact fun h => ⟨s,t,rfl,rfl,h⟩

theorem liftDirectedPair_mono (a b : W ↪ V) {D H : Digraph W} (h : H ≤ D) :
    liftDirectedPair a b H ≤ liftDirectedPair a b D := by
  rintro x y ⟨s,t,hs,ht,hst⟩
  exact ⟨s,t,hs,ht,h hst⟩

def directedPairUnion (a b : I → W ↪ V) (D : I → Digraph W) : Digraph V :=
  ⟨fun x y => ∃ i,(liftDirectedPair (a i) (b i) (D i)).Adj x y⟩

private theorem disjoint_liftDirectedPair (a b : W ↪ V) {D H : Digraph W} (h : Disjoint D H) :
    Disjoint (liftDirectedPair a b D) (liftDirectedPair a b H) := by
  rw [disjoint_iff_inf_le]
  rintro x y ⟨⟨s,t,hs,ht,hst⟩,⟨q,r,hq,hr,hqr⟩⟩
  have h₁ := a.injective (hq.trans hs.symm)
  have h₂ := b.injective (hr.trans ht.symm)
  subst q
  subst r
  exact (disjoint_iff_inf_le.mp h) ⟨hst,hqr⟩

theorem disjoint_directedPairUnions (a b : I → W ↪ V) (D F G : I → Digraph W)
    (hFD : ∀ i, F i ≤ D i) (hGD : ∀ i, G i ≤ D i) (hFG : ∀ i, Disjoint (F i) (G i))
    (hDis : ∀ i j, i ≠ j →
      Disjoint (liftDirectedPair (a i) (b i) (D i)) (liftDirectedPair (a j) (b j) (D j))) :
    Disjoint (directedPairUnion a b F) (directedPairUnion a b G) := by
  rw [disjoint_iff_inf_le]
  rintro x y ⟨⟨i,hi⟩,⟨j,hj⟩⟩
  by_cases h : i = j
  · subst j
    exact (disjoint_iff_inf_le.mp (disjoint_liftDirectedPair _ _ (hFG i))) ⟨hi,hj⟩
  · exact (disjoint_iff_inf_le.mp (hDis i j h))
      ⟨liftDirectedPair_mono _ _ (hFD i) hi,liftDirectedPair_mono _ _ (hGD j) hj⟩

theorem exists_thin_reserve_partition (γ ε δ : ℝ) (hγ : 0 < γ) (hSum : 5*γ ≤ 1)
    (hε : 0 ≤ ε) (hSmall : ε ≤ δ/4) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ N : ℕ, ∀ {W : Type v} [Fintype W] [DecidableEq W] {V : Type u} {I : Type w}
      (a b : I → W ↪ V) (D : I → Digraph W) (d : ℝ), N ≤ Fintype.card W →
      (∀ i, IsCentredRegular (D i) ε d) →
      (∀ i j, i ≠ j → Disjoint (liftDirectedPair (a i) (b i) (D i))
        (liftDirectedPair (a j) (b j) (D j))) →
      ∃ F : Fin 5 → I → Digraph W, ∃ R : I → Digraph W,
        (∀ j i, IsCentredRegular (F j i) δ (γ*d)) ∧
        (∀ i, IsCentredRegular (R i) δ ((1-5*γ)*d)) ∧
        (∀ j l, j ≠ l → Disjoint (directedPairUnion a b (F j)) (directedPairUnion a b (F l))) ∧
        (∀ j, Disjoint (directedPairUnion a b (F j)) (directedPairUnion a b R)) ∧
        (∀ x y, (directedPairUnion a b D).Adj x y ↔
          (directedPairUnion a b R).Adj x y ∨ ∃ j,(directedPairUnion a b (F j)).Adj x y) ∧
        (∀ i v,
          (|(inDegree (D i) v:ℝ)-d*(Fintype.card W:ℝ)| ≤ ε*(Fintype.card W:ℝ) →
            (∀ j, |(inDegree (F j i) v:ℝ)-(γ*d)*(Fintype.card W:ℝ)| ≤ δ*(Fintype.card W:ℝ))) ∧
          (|(outDegree (D i) v:ℝ)-d*(Fintype.card W:ℝ)| ≤ ε*(Fintype.card W:ℝ) →
            (∀ j, |(outDegree (F j i) v:ℝ)-(γ*d)*(Fintype.card W:ℝ)| ≤ δ*(Fintype.card W:ℝ)))) := by
  obtain ⟨N,hN⟩ := exists_five_regular_arc_reserves.{v} γ ε δ hγ hSum hε hSmall hδ hδ1
  refine ⟨N,?_⟩
  intro W _ _ V I a b D d hn hD hDis
  choose F R hF hR hFDis hFR hParts hDeg using fun i => hN (D i) d hn (hD i)
  have hFD (j : Fin 5) (i : I) : F i j ≤ D i := fun s t h => (hParts i s t).mpr (Or.inr ⟨j,h⟩)
  have hRD (i : I) : R i ≤ D i := fun s t h => (hParts i s t).mpr (Or.inl h)
  refine ⟨fun j i => F i j,R,fun j i => hF i j,hR,?_,?_,?_,?_⟩
  · intro j l hjl
    exact disjoint_directedPairUnions a b D _ _ (hFD j) (hFD l) (fun i => hFDis i j l hjl) hDis
  · intro j
    exact disjoint_directedPairUnions a b D _ _ (hFD j) hRD (fun i => hFR i j) hDis
  · intro x y
    constructor
    · rintro ⟨i,s,t,hs,ht,h⟩
      rcases (hParts i s t).mp h with h | ⟨j,h⟩
      · exact Or.inl ⟨i,s,t,hs,ht,h⟩
      · exact Or.inr ⟨j,i,s,t,hs,ht,h⟩
    · rintro (⟨i,s,t,hs,ht,h⟩ | ⟨j,i,s,t,hs,ht,h⟩)
      · exact ⟨i,s,t,hs,ht,hRD i h⟩
      · exact ⟨i,s,t,hs,ht,hFD j i h⟩
  · intro i v
    exact ⟨fun h => ((hDeg i v).1 h).1,fun h => ((hDeg i v).2 h).1⟩

end OverfullWork.DirectedRobustExpansion
