module

public import OverfullWork.KuhnOsthusExceptionalFactorSequence
public import OverfullWork.KuhnOsthusChordAfterPreprocessing

@[expose] public section


/-! Apply Lemma 9.4 to the second call to Lemma 7.6. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset InducedDigraphSampling
open scoped Classical
universe u

set_option maxHeartbeats 850000 in
/-- The second winding pack fixes the exceptional arcs of the chord
absorber in the complement of preprocessing. The cycle base and the
four quarters of the universal walk are realized in that same host. -/
theorem kuhn_osthus_chord_reserve_from_wound_pack
    (C εStart ε₀ εD εB ηB δB εW ηW dHost d₁ dW aD aW aPG : ℝ)
    (hC : 0 < C) (hε₀ : 0 < ε₀) (hε₀₁ : ε₀ ≤ 1)
    (hεD : 0 < εD) (hεD₁ : εD ≤ 1) (hSmall : εD ≤ εB/4)
    (hεB : 0 < εB) (hεB₁ : εB ≤ 1) (hηB : 0 < ηB) (hηB₁ : ηB ≤ 1)
    (hδB : 0 ≤ δB) (hTolB : 2*(εB+δB) ≤ ηB) (hBaseBudget : 8*εB ≤ δB*ηB)
    (hεW : 0 < εW) (hεW₁ : εW ≤ 1) (hηW : 0 < ηW) (hηW₁ : ηW ≤ 1)
    (haD : 0 ≤ aD) (haW : 0 ≤ aW) (haPG : 0 ≤ aPG)
    (hd₁ : 0 ≤ d₁) (hBaseCentre : d₁+5*εB ≤ dHost)
    (hFloorW : 2*εW ≤ dW) (hMatchW : 2*ηW ≤ dW)
    (hTolPG : 2*(εStart+aPG) ≤ ε₀) (hTolPGW : 2*(εStart+aPG) ≤ εW)
    (hTolD : 2*(ε₀+aD) ≤ εD) (hTolW : 2*(4*εW+aW) ≤ ηW) :
    ∃ N₁ N₂ : ℕ, ∀ {V : Type u} {J : Type*} [Fintype V] {f n p r₂ r₃ : ℕ}
      (G PG : Digraph V) (Z : Finset V) (c : ↥Zᶜ → Fin (f*(n+1)))
      (D : J → Finset ↥Zᶜ) (w : Equiv.Perm J) (parent : J → Fin (f*(n+1)))
      (X : Fin (f*(n+1)) → Finset V) (mB m mStyle lossPG : ℕ) (σ : ℝ),
      letI : DecidableEq ↥Zᶜ := Classical.decEq _
      let A (i : Fin (f*(n+1))) := (univ : Finset ↥Zᶜ).filter (fun v => c v = i)
      let s := finRotate (f*(n+1))
      2 ≤ f → PG ≤ G →
      (∀ v ∉ Z, inDegree PG v ≤ lossPG ∧ outDegree PG v ≤ lossPG) →
      (∀ i, (A i).map (Function.Embedding.subtype (· ∈ Zᶜ)) = X i) →
      (∀ v, ∃ j, v ∈ D j) → (∀ i j, i ≠ j → Disjoint (D i) (D j)) →
      (∀ j v, v ∈ D j → c v = parent j) →
      N₁ ≤ mB → 0 < mB → (∀ i, (A i).card = mB) →
      N₂ ≤ 4*m → 0 < m → (∀ i, (D i).card = 4*m) →
      2*(Fintype.card ↥Zᶜ:ℝ) ≤ C*(4*m:ℕ) →
      (∀ i, IsLowerSuperregularPair (induced G Zᶜ) εStart dHost (A i) (A (s i))) →
      (∀ i, IsLowerSuperregularPair (induced G Zᶜ) εStart dW (D i) (D (w i))) →
      (lossPG:ℝ) ≤ aPG*((mB:ℝ)*ε₀) → (lossPG:ℝ) ≤ aPG*(((4*m:ℕ):ℝ)*εW) →
      (r₃:ℝ) ≤ aD*((mB:ℝ)*εD) →
      (((⌊d₁*(mB:ℝ)⌋₊+r₃:ℕ):ℝ) ≤ aW*((m:ℝ)*ηW)) →
      (r₂:ℝ) < (dW-2*ηW)*((m:ℝ)*ηW) → (r₂:ℝ) ≤ (dW-3*ηW)*(m:ℝ) →
      ∀ E : WoundFactorPacking (G \ PG) Z X (Nat.succ_pos n) p mStyle r₃ σ,
        ∃ (B : Digraph ↥Zᶜ) (Q : J × Fin 4 → Finset ↥Zᶜ)
          (M : ∀ i, Fin r₂ → Q i ≃ Q ((w.prodCongr (Equiv.refl (Fin 4))) i)),
          let e : ↥Zᶜ ↪ V := Function.Embedding.subtype _
          let L := liftDirectedPair e e B
          let U := liftDirectedPair e e (successorCellMatchingUnion Q (w.prodCongr (Equiv.refl (Fin 4))) M)
          let F := ⨆ i, ⨆ j, (E.factors i j).digraph
          let CA := (U ⊔ F) ⊔ L
          CA ≤ G \ PG ∧ F ≤ CA ∧ Disjoint U F ∧ Disjoint (U ⊔ F) L ∧
          (∀ i, IsSuperregularPair (induced L Zᶜ) (ηB+εB) d₁ (A i) (A (s i))) ∧
          (∀ x y, L.Adj x y → ∃ u v : ↥Zᶜ, u.val = x ∧ v.val = y ∧ c v = s (c u)) ∧
          (∀ j, (univ : Finset (Fin 4)).biUnion (fun h => Q (j,h)) = D j) ∧
          (∀ v, ∃ j, v ∈ Q j) ∧ (∀ j v, v ∈ Q j → c v = parent j.1) ∧
          (∀ i, (Q i).card = m) ∧ (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) ∧
          (∀ i p z, p ≠ z → ∀ x, M i p x ≠ M i z x) ∧
          ∀ x, let d := if x ∈ Z then (p*f)*r₃ else ⌊d₁*(mB:ℝ)⌋₊+r₂+r₃
            inDegree CA x = d ∧ outDegree CA x = d := by
  obtain ⟨N₁,N₂,hN⟩ := kuhn_osthus_chord_reserve_after_preprocessing.{u}
    C εStart ε₀ εD εB ηB δB εW ηW dHost d₁ dW aD aW aPG
    hC hε₀ hε₀₁ hεD hεD₁ hSmall hεB hεB₁ hηB hηB₁ hδB hTolB hBaseBudget
    hεW hεW₁ hηW hηW₁ haD haW haPG hd₁ hBaseCentre hFloorW hMatchW hTolPG hTolPGW hTolD hTolW
  refine ⟨N₁,N₂,?_⟩
  intro V J _ f n p r₂ r₃ G PG Z c D w parent X mB m mStyle lossPG σ A s
    hf hPG hLossPG hMap hDCover hDDis hParent hNB hmB hASize hNW hm hDSize hProfile
    hAPairs hDPairs hPayPG hPayPGW hPayE hPayWalk hDemand hRoom E
  have hCellCover (x : V) (hx : x ∉ Z) : ∃ i, x ∈ E.cell i := by
    let v : ↥Zᶜ := ⟨x,mem_compl.mpr hx⟩
    let i := c v
    have hi : x ∈ X i := by
      rw [←hMap i]
      exact mem_map.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,rfl⟩,rfl⟩
    rw [←E.cover i] at hi
    obtain ⟨a,_,ha⟩ := mem_biUnion.mp hi
    exact ⟨(a,i),ha⟩
  obtain ⟨B,Q,M,hCA,hApart,hSup,hPairs,hNext,hQCover,hVCover,hQParent,hQSize,hQDis,hM,hDegree⟩ :=
    hN G PG Z c D w parent E.cell mB m mStyle lossPG E.factors
      hf hPG hLossPG (fun i => (E.size i).1) E.disjoint hCellCover E.apart hDCover hDDis
      hParent hNB hmB hASize hNW hm hDSize hProfile hAPairs hDPairs hPayPG hPayPGW hPayE hPayWalk hDemand hRoom
  exact ⟨B,Q,M,hCA,le_sup_right.trans le_sup_left,hApart,hSup,hPairs,hNext,
    hQCover,hVCover,hQParent,hQSize,hQDis,hM,hDegree⟩

end OverfullWork.DirectedRobustExpansion
