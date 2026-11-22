module

public import OverfullWork.KuhnOsthusChordReserveScales
public import OverfullWork.KuhnOsthusWindingExceptionalDegrees

@[expose] public section


/-! Realize the chord absorber in the actual complement of the
preprocessing graph, using the original factors of Lemma 7.6. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs InducedDigraphSampling
open scoped Classical
universe u

set_option maxHeartbeats 850000 in
/-- Lemma 9.4 on one physical partition. Its two matching budgets are
chosen integrally and the exceptional reserve is the union of the
given original factors. The two ordinary pair families survive the
preprocessing deletion by the local estimates of Lemma 9.2. -/
theorem kuhn_osthus_chord_reserve_after_preprocessing
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
      (X : Fin p × Fin (f*(n+1)) → Finset V) (mB m mStyle lossPG : ℕ),
      letI : DecidableEq ↥Zᶜ := Classical.decEq _
      let A (i : Fin (f*(n+1))) := (univ : Finset ↥Zᶜ).filter (fun v => c v = i)
      let s := finRotate (f*(n+1))
      let T (j : Fin p × Fin f) := univ.biUnion (fun i : Fin (n+1) => X (j.1,intervalPosition j.2 i))
      let S (j : Fin p × Fin f) := X (j.1,intervalPosition j.2 (0 : Fin (n+1)))
      let next := (Equiv.refl (Fin p)).prodCongr (finRotate f)
      ∀ (F : Fin r₃ → ∀ j, OriginalInterval (G \ PG) Z (T j ∪ S (next j)) (S j) (S (next j))),
      2 ≤ f → PG ≤ G →
      (∀ v ∉ Z, inDegree PG v ≤ lossPG ∧ outDegree PG v ≤ lossPG) →
      (∀ i, (X i).card = mStyle) → (∀ i j, i ≠ j → Disjoint (X i) (X j)) →
      (∀ x ∉ Z, ∃ i, x ∈ X i) →
      Pairwise (fun i j => Disjoint (⨆ z, (F i z).digraph) (⨆ z, (F j z).digraph)) →
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
      ∃ (B : Digraph ↥Zᶜ) (Q : J × Fin 4 → Finset ↥Zᶜ)
        (M : ∀ i, Fin r₂ → Q i ≃ Q ((w.prodCongr (Equiv.refl (Fin 4))) i)),
        let e : ↥Zᶜ ↪ V := Function.Embedding.subtype _
        let L := liftDirectedPair e e B
        let U := liftDirectedPair e e (successorCellMatchingUnion Q (w.prodCongr (Equiv.refl (Fin 4))) M)
        let E := ⨆ i, ⨆ j, (F i j).digraph
        let CA := (U ⊔ E) ⊔ L
        CA ≤ G \ PG ∧ Disjoint U E ∧ Disjoint (U ⊔ E) L ∧
        (∀ i, IsSuperregularPair (induced L Zᶜ) (ηB+εB) d₁ (A i) (A (s i))) ∧
        (∀ x y, L.Adj x y → ∃ u v : ↥Zᶜ, u.val = x ∧ v.val = y ∧ c v = s (c u)) ∧
        (∀ j, (univ : Finset (Fin 4)).biUnion (fun h => Q (j,h)) = D j) ∧
        (∀ v, ∃ j, v ∈ Q j) ∧ (∀ j v, v ∈ Q j → c v = parent j.1) ∧
        (∀ i, (Q i).card = m) ∧ (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) ∧
        (∀ i p z, p ≠ z → ∀ x, M i p x ≠ M i z x) ∧
        ∀ x, let d := if x ∈ Z then (p*f)*r₃ else ⌊d₁*(mB:ℝ)⌋₊+r₂+r₃
          inDegree CA x = d ∧ outDegree CA x = d := by
  let dB := d₁+5*εB
  have hdB : 0 < dB := by dsimp only [dB]; linarith only [hd₁,hεB]
  obtain ⟨N₁,N₂,hN⟩ := kuhn_osthus_lemma_9_4_of_normalized_pairs.{u}
    C ε₀ εD εB ηB δB εW ηW dB dW aD aW hC hεD hεD₁ hSmall hεB hεB₁ hηB hηB₁ hδB hTolB
    hεW hηW hηW₁ haD haW hdB hFloorW hTolD hTolW
  let N₁' := max N₁ ⌈1/εB⌉₊
  let N₂' := max N₂ (4*⌈1/ηW⌉₊)
  refine ⟨N₁',N₂',?_⟩
  intro V J _ f n p r₂ r₃ G PG Z c D w parent X mB m mStyle lossPG A s T S next F
    hf hPG hLossPG hXSize hXDis hXCover hF hDCover hDDis hParent hNB hmB hASize hNW hm hDSize hProfile
    hAPairs hDPairs hPayPG hPayPGW hPayE hPayWalk hDemand hRoom
  let : DecidableEq ↥Zᶜ := Classical.decEq _
  let R := induced G Zᶜ
  let P₀ := induced PG Zᶜ
  let E : Digraph V := ⨆ i, ⨆ j, (F i j).digraph
  let r₁ := ⌊d₁*(mB:ℝ)⌋₊
  have hE : E ≤ G \ PG := iSup_le (fun i => iSup_le (fun j => (F i j).le))
  have hDegree (x : V) : let d := if x ∈ Z then (p*f)*r₃ else r₃
      inDegree E x = d ∧ outDegree E x = d := by
    simpa only [Fintype.card_fin] using winding_exceptional_reserve_exact_semidegrees X
      (Nat.succ_pos n) hf mStyle hXSize hXDis hXCover F hF x
  have hOrdLoss (v : ↥Zᶜ) : inDegree P₀ v ≤ lossPG ∧ outDegree P₀ v ≤ lossPG := by
    have h := hLossPG v.val (mem_compl.mp v.prop)
    change inDegree (induced PG Zᶜ) v ≤ lossPG ∧ outDegree (induced PG Zᶜ) v ≤ lossPG
    rw [induced_inDegree,induced_outDegree]
    exact ⟨(card_le_card inter_subset_right).trans ((inProfile_card PG _).trans_le h.1),
      (card_le_card inter_subset_right).trans ((outProfile_card PG _).trans_le h.2)⟩
  have hA (i : Fin (f*(n+1))) : IsLowerSuperregularPair (induced (G \ PG) Zᶜ) ε₀ dB (A i) (A (s i)) := by
    have hPair : IsLowerSuperregularPair R εStart dB (A i) (A (s i)) := by
      obtain ⟨d,hLow,hHigh,hReg⟩ := hAPairs i
      exact ⟨d,hBaseCentre.trans hLow,hHigh,hReg⟩
    change IsLowerSuperregularPair (R \ P₀) ε₀ dB (A i) (A (s i))
    exact IsLowerSuperregularPair.after_bounded_arc_deletion (G := R) (L := P₀) (fun _ _ h => hPG h)
      lossPG hOrdLoss (A i) (A (s i)) (card_pos.mp (by rwa [hASize])) (card_pos.mp (by rwa [hASize]))
      mB (hASize _) (hASize _) εStart ε₀ dB aPG hε₀ hε₀₁ haPG hdB.le hTolPG hPayPG hPair
  have hD (i : J) : IsLowerSuperregularPair (induced (G \ PG) Zᶜ) εW dW (D i) (D (w i)) := by
    have hPos : 0 < 4*m := by omega
    change IsLowerSuperregularPair (R \ P₀) εW dW (D i) (D (w i))
    exact IsLowerSuperregularPair.after_bounded_arc_deletion (G := R) (L := P₀) (fun _ _ h => hPG h)
      lossPG hOrdLoss (D i) (D (w i)) (card_pos.mp (by rwa [hDSize])) (card_pos.mp (by rwa [hDSize]))
      (4*m) (hDSize _) (hDSize _) εStart εW dW aPG hεW hεW₁ haPG
      (by linarith only [hεW,hFloorW]) hTolPGW hPayPGW (hDPairs i)
  have hCutB : 1 ≤ εB*(mB:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hεB).mp ((Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈1/εB⌉₊ ≤ mB from (le_max_right _ _).trans hNB)))
  have hCutW : 1 ≤ (m:ℝ)*ηW := (div_le_iff₀ hηW).mp ((Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈1/ηW⌉₊ ≤ m from by have h := (le_max_right N₂ (4*⌈1/ηW⌉₊)).trans hNW; omega)))
  obtain ⟨_,hCut₁,hDemand₁,hRect₁,hLoss₁,hBudget₁⟩ :=
    chord_base_cycle_integer_budgets d₁ εB ηB δB mB hd₁ hεB hCutB hBaseBudget
  obtain ⟨hh₂,hCut₂,hDemand₂,hDegree₂⟩ := chord_walk_quarter_integer_budgets dW ηW m r₂
    hMatchW hCutW hDemand hRoom
  obtain ⟨B,Q,M,hBLe,hULe,hBPair,hBNext,hQCover,hQSize,hQDis,hM,hCA,hEB,hEU,hBU,hReg⟩ :=
    hN (G \ PG) E Z A s D w (p*f) r₁ r₂ r₃ mB m ⌈εB*(mB:ℝ)⌉₊ ⌈(m:ℝ)*ηW⌉₊ ⌈7*εB*(mB:ℝ)⌉₊
      hE hDegree (fun v => ⟨c v,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩) hDCover
      (fun i j hij => disjoint_left.mpr (fun v hi hj => hij (((mem_filter.mp hi).2).symm.trans (mem_filter.mp hj).2)))
      hDDis ((le_max_left _ _).trans hNB) hmB hASize (fun j => by rw [hDSize]; exact (le_max_left _ _).trans hNW)
      hm hDSize hProfile hA hD hPayE hCut₁ hDemand₁ hRect₁ hLoss₁ hBudget₁ hPayWalk hh₂ hCut₂ hDemand₂ hDegree₂
  let e : ↥Zᶜ ↪ V := Function.Embedding.subtype _
  let L := liftDirectedPair e e B
  let U := liftDirectedPair e e (successorCellMatchingUnion Q (w.prodCongr (Equiv.refl (Fin 4))) M)
  have hReorder : E ⊔ L ⊔ U = (U ⊔ E) ⊔ L := by ac_rfl
  rw [hReorder] at hCA hReg
  have hInd : induced L Zᶜ = B := by ext v w; exact liftDirectedPair_adj e e B v w
  refine ⟨B,Q,M,hCA,hEU.symm,disjoint_sup_left.mpr ⟨hBU.symm,hEB⟩,?_,?_,hQCover,
    ?_,?_,hQSize,hQDis,hM,hReg⟩
  · intro i
    rw [hInd]
    exact IsSuperregularPair.shift_density (hBPair i) (chord_base_cycle_floor_density_error d₁ εB mB hd₁ hmB hCutB)
  · rintro x y ⟨u,v,rfl,rfl,h⟩
    obtain ⟨i,hi,hj⟩ := hBNext u v h
    exact ⟨u,v,rfl,rfl,((mem_filter.mp hj).2).trans (congrArg s ((mem_filter.mp hi).2).symm)⟩
  · intro v
    obtain ⟨j,hj⟩ := hDCover v
    rw [←hQCover j] at hj
    obtain ⟨q,_,hq⟩ := mem_biUnion.mp hj
    exact ⟨(j,q),hq⟩
  · intro j v hv
    apply hParent j.1 v
    rw [←hQCover j.1]
    exact mem_biUnion.mpr ⟨j.2,mem_univ _,hv⟩

end OverfullWork.DirectedRobustExpansion
