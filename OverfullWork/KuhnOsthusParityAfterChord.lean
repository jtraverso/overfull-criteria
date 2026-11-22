module

public import OverfullWork.KuhnOsthusParityPacketProjection
public import OverfullWork.KuhnOsthusParityReserveSplit

@[expose] public section


/-! Use the same physical graph for the deletion of the earlier
reserves, the parity packets and the ordinary parity reserve. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u v

set_option maxHeartbeats 800000 in
/-- Lemma 10.5 in the complement of the earlier reserves, as used in
Lemma 11.2. The packets are prescribed in that complement. The
routing and the ordinary (5n)-regular part are constructed in the
further complement of those packets. -/
theorem kuhn_osthus_parity_reserve_after_chord_deletion (q : ℕ) (hq : 15 ≤ q)
    (ε₀ ε ε' θ δ₁ δ₂ δ₃ d a : ℝ)
    (hε₀ : 0 < ε₀) (hε₀₁ : ε₀ ≤ 1) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hε' : 0 < ε') (hε'₁ : ε' ≤ 1) (ha : 0 ≤ a)
    (hClean : 2*(ε₀+a) ≤ ε) (hCycle : 2*(ε+a) ≤ ε')
    (hθ : 4*ε ≤ θ) (hGapθ : 2*θ < d) (hGap' : 2*ε' < d) (hd : d ≤ 1)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃)
    (hδ₁₁ : δ₁ ≤ 1) (hδ₂₁ : δ₂ ≤ 1) (hδ₃₁ : δ₃ ≤ 1)
    (hGap₁ : 2*δ₁ < d) (hGap₂ : 2*δ₂ < d) (hGap₃ : 2*δ₃ < d)
    (hTol₁ : 2*(ε₀+a) ≤ δ₁) (hTol₂ : 2*(δ₁+a) ≤ δ₂) (hTol₃ : 2*(δ₂+a) ≤ δ₃) :
    ∃ N : ℕ, ∀ {V : Type u} {Z : Type v} [Fintype V] [Fintype Z]
      (G C : Digraph (V ⊕ Z)) {n m : ℕ} (X : Fin (14*q) → Finset V)
      (hC : C ≤ G) (hm : 0 < m) (hNm : N ≤ 2*m)
      (hCover : ∀ x, ∃ i, x ∈ X i) (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
      (hSize : ∀ i, (X i).card = 2*m)
      (loss : ℕ) (εInitial εAfter εBase : ℝ)
      (hBound : ∀ x : V, inDegree C (.inl x) ≤ loss ∧ outDegree C (.inl x) ≤ loss)
      (hAfter : 0 < εAfter) (hAfter₁ : εAfter ≤ 1)
      (hBase : 0 < εBase) (hBase₁ : εBase ≤ 1)
      (hTolAfter : 2*(εInitial+a) ≤ εAfter) (hTolBase : 2*(εAfter+a) ≤ εBase)
      (hTol : 2*(εBase+a) ≤ ε₀)
      (hPayAfter : (loss:ℝ) ≤ a*(((2*m:ℕ):ℝ)*εAfter))
      (hPayBase : (n:ℝ) ≤ a*(((2*m:ℕ):ℝ)*εBase))
      (hPairs : ∀ i, IsLowerSuperregularPair (ordinaryCycleHost G) εInitial d
        (X i) (X (finRotate (14*q) i)))
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
      let D := G \ C
      ∀ (E : Fin n → ParityExceptionalPacket D A q)
        (eTop : Fin (2*m) ≃ A 0) (_eLow : Fin (2*m) ≃ B 0),
        let E₀ := ⨆ j, (E j).original
        Pairwise (fun i j => Disjoint (E i).original (E j).original) →
        (∀ v, let d := match v with | .inl _ => n | .inr _ => 7*n
          inDegree E₀ v = d ∧ outDegree E₀ v = d) →
        ∃ (P : Fin n → Digraph (V ⊕ Z)) (T : Digraph V),
          (∀ j, (E j).original ≤ P j ∧ P j ≤ D ∧
            AbsorbsWindingFactor X (P j) (E j).absorptionOrder) ∧
          Pairwise (fun j l => Disjoint (P j) (P l)) ∧
          let P₀ := ⨆ j, P j
          P₀ = liftOrdinaryCycleArcs Z T ⊔ E₀ ∧
          liftOrdinaryCycleArcs Z T ≤ D \ E₀ ∧
          (∀ x, inDegree T x = 5*n ∧ outDegree T x = 5*n) ∧
          ∀ v, let d := match v with | .inl _ => 6*n | .inr _ => 7*n
            inDegree P₀ v = d ∧ outDegree P₀ v = d := by
  obtain ⟨N,hN⟩ := kuhn_osthus_lemma_10_5_with_original_absorption.{u,v} q hq
    ε₀ ε ε' θ δ₁ δ₂ δ₃ d a hε₀ hε₀₁ hε hε₁ hε' hε'₁ ha hClean hCycle hθ hGapθ hGap' hd
    hδ₁ hδ₂ hδ₃ hδ₁₁ hδ₂₁ hδ₃₁ hGap₁ hGap₂ hGap₃ hTol₁ hTol₂ hTol₃
  refine ⟨N,?_⟩
  intro V Z _ _ G C n m X hC hm hNm hCover hDis hSize loss εInitial εAfter εBase
    hBound hAfter hAfter₁ hBase hBase₁ hTolAfter hTolBase hTol hPayAfter hPayBase hPairs
    hLoss hLossε hLossε' hLoss₁ hLoss₂ hLoss₃ s r hs hr hCutθ hRouteθ hCut hRoute
    hk A B D E eTop eLow E₀ hPackets hDegE
  have hd₀ : 0 ≤ d := by linarith only [hε,hθ,hGapθ]
  have hX (i : Fin (14*q)) : (X i).Nonempty := card_pos.mp (by rw [hSize]; omega)
  have hPairsD (i : Fin (14*q)) :
      IsLowerSuperregularPair (ordinaryCycleHost D) εAfter d (X i) (X (finRotate (14*q) i)) :=
    IsLowerSuperregularPair.after_bounded_arc_deletion (G := ordinaryCycleHost G) (L := ordinaryCycleHost C)
      (fun _ _ h => hC h) loss
      (fun x => ⟨((ordinaryCycleHost_semidegrees_le C x).1).trans (hBound x).1,
        ((ordinaryCycleHost_semidegrees_le C x).2).trans (hBound x).2⟩)
      _ _ (hX i) (hX _) _ (hSize i) (hSize _) εInitial εAfter d a
      hAfter hAfter₁ ha hd₀ hTolAfter hPayAfter (hPairs i)
  have hLossE (x : V) : inDegree (ordinaryCycleHost E₀) x ≤ n ∧
      outDegree (ordinaryCycleHost E₀) x ≤ n := by
    obtain ⟨hi,ho⟩ := ordinaryCycleHost_semidegrees_le E₀ x
    exact ⟨hi.trans_eq (hDegE (.inl x)).1,ho.trans_eq (hDegE (.inl x)).2⟩
  let R := ordinaryCycleHost (D \ E₀)
  obtain ⟨hHost,hReserved,hPairsR⟩ := parity_routing_host_after_packet_deletion D A E X
    (by omega : 0 < 2*m) hSize εAfter εBase d a hBase hBase₁ ha hd₀ hTolBase hPayBase hPairsD hLossE
  obtain ⟨P,hP,hDisP⟩ := hN D R X hHost hm hNm hCover hDis hSize εBase hTol hPairsR
    hLoss hLossε hLossε' hLoss₁ hLoss₂ hLoss₃ s r hs hr hCutθ hRouteθ hCut hRoute E eTop eLow
    hPackets hReserved
  let P₀ := ⨆ j, P j
  have hP₀ : P₀ ≤ D := iSup_le (fun j => (hP j).2.1)
  have hE₀ : E₀ ≤ P₀ := iSup_le (fun j => (hP j).1.trans (le_iSup P j))
  have hAbsorb (j : Fin n) : AbsorbsWindingFactor X (P j) (E j).absorptionOrder :=
    (hP j).2.2.choose_spec.2.2
  have hM (j : Fin n) : ∃ M : Fin 6 → Equiv.Perm V,
      ordinaryCycleHost (P j) ≤ matchingUnion M :=
    ⟨(hP j).2.2.choose,(hP j).2.2.choose_spec.1⟩
  have hεLe : ε₀ ≤ ε := by linarith only [hClean,ha,hε₀]
  have hGap : 2*ε < d := by linarith only [hθ,hGapθ,hε]
  have hCut₀ : ((2*m:ℕ):ℝ)*ε₀ ≤ (r:ℝ) :=
    (mul_le_mul_of_nonneg_left hεLe (Nat.cast_nonneg _)).trans (hCut ε (by simp))
  have hDeg₀ : (r:ℝ) ≤ (d-ε₀)*((2*m:ℕ):ℝ) := by
    have hp : (d-2*ε)^14 ≤ 1 := pow_le_one₀ (by linarith only [hGap])
      (by linarith only [hd,hε])
    have hScale := mul_le_of_le_one_left
      (mul_nonneg (by linarith only [hGap,hε] : 0 ≤ d-ε)
        (Nat.cast_nonneg (2*m) : (0:ℝ) ≤ _)) hp
    have hRouteε := hRoute ε (by simp)
    have hPay := mul_le_mul_of_nonneg_right (sub_le_sub_left hεLe d)
      (Nat.cast_nonneg (2*m) : (0:ℝ) ≤ _)
    linarith only [hScale,hRouteε,hPay,show (0:ℝ) ≤ r from Nat.cast_nonneg _]
  have hDegP := parity_reserve_semidegrees_of_matching_budget X R P (fun j => (E j).absorptionOrder)
    r εBase ε₀ d a hCover hDis hm hSize hr hε₀ hε₀₁ ha (by linarith only [hGap,hεLe])
    hCut₀ hDeg₀ hTol hLoss hPairsR hM hAbsorb hDisP
  obtain ⟨hApart,hSplit,hDegT⟩ := parity_reserve_split_of_exact_semidegrees P₀ E₀ n hE₀ hDegP hDegE
  let T := ordinaryCycleHost (P₀ \ E₀)
  have hT : liftOrdinaryCycleArcs Z T ≤ D \ E₀ := by
    intro x y h
    have hp : P₀.Adj x y := by rw [hSplit]; exact .inl h
    exact ⟨hP₀ hp,fun he => disjoint_iff_inf_le.mp hApart ⟨h,he⟩⟩
  exact ⟨P,T,fun j => ⟨(hP j).1,(hP j).2.1,hAbsorb j⟩,hDisP,hSplit,hT,hDegT,hDegP⟩

end OverfullWork.DirectedRobustExpansion
