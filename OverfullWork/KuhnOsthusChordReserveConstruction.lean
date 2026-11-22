module

public import OverfullWork.KuhnOsthusChordAbsorberUnion
public import OverfullWork.KuhnOsthusCycleAbsorberReserveMiddle
public import OverfullWork.OsthusStadenH1Profile

@[expose] public section


/-! The successive physical deletions in Kühn–Osthus Lemma 9.4. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs InducedDigraphSampling
open scoped Classical
universe v

set_option maxHeartbeats 650000 in
/-- Remove the given original exceptional factors, construct the
base-cycle reserve, and then construct the universal-walk reserve
in the ordinary complement of both. -/
theorem kuhn_osthus_lemma_9_4_of_normalized_pairs
    (C ε₀ εD εB ηB δB εW ηW dB dW aD aW : ℝ)
    (hC : 0 < C) (hεD : 0 < εD) (hεD₁ : εD ≤ 1) (hSmall : εD ≤ εB/4)
    (hεB : 0 < εB) (hεB₁ : εB ≤ 1) (hηB : 0 < ηB) (hηB₁ : ηB ≤ 1)
    (hδB : 0 ≤ δB) (hTolB : 2*(εB+δB) ≤ ηB)
    (hεW : 0 < εW) (hηW : 0 < ηW) (hηW₁ : ηW ≤ 1)
    (haD : 0 ≤ aD) (haW : 0 ≤ aW) (hdB : 0 < dB) (hFloorW : 2*εW ≤ dW)
    (hTolD : 2*(ε₀+aD) ≤ εD) (hTolW : 2*(4*εW+aW) ≤ ηW) :
    ∃ N₁ N₂ : ℕ, ∀ {V : Type v} {I J : Type*} [Fintype V]
      (G E : Digraph V) (Z : Finset V) (A : I → Finset ↥Zᶜ) (s : Equiv.Perm I)
      (D : J → Finset ↥Zᶜ) (w : Equiv.Perm J) (q r₁ r₂ r₃ mB m h₁ h₂ loss : ℕ),
      letI : DecidableEq ↥Zᶜ := Classical.decEq _
      let R := induced G Zᶜ
      let e : ↥Zᶜ ↪ V := Function.Embedding.subtype (· ∈ Zᶜ)
      E ≤ G →
      (∀ x, let d := if x ∈ Z then q*r₃ else r₃
        inDegree E x = d ∧ outDegree E x = d) →
      (∀ x, ∃ i, x ∈ A i) → (∀ x, ∃ j, x ∈ D j) →
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) → (∀ i j, i ≠ j → Disjoint (D i) (D j)) →
      N₁ ≤ mB → 0 < mB → (∀ i, (A i).card = mB) →
      (∀ j, N₂ ≤ (D j).card) → 0 < m → (∀ j, (D j).card = 4*m) →
      2*(Fintype.card ↥Zᶜ:ℝ) ≤ C*(4*m:ℕ) →
      (∀ i, IsLowerSuperregularPair R ε₀ dB (A i) (A (s i))) →
      (∀ j, IsLowerSuperregularPair R εW dW (D j) (D (w j))) →
      (r₃:ℝ) ≤ aD*((mB:ℝ)*εD) →
      (mB:ℝ)*εB ≤ h₁ →
      (((r₁+2*h₁ : ℕ):ℝ) ≤ (dB-εB)*(mB:ℝ)) →
      (r₁:ℝ) ≤ (dB-2*εB)*(mB:ℝ) →
      (dB+εB)*(mB:ℝ) ≤ (r₁:ℝ)+loss →
      (loss:ℝ) ≤ δB*((mB:ℝ)*ηB) →
      ((r₁+r₃:ℕ):ℝ) ≤ aW*((m:ℝ)*ηW) →
      0 < h₂ → (m:ℝ)*ηW ≤ h₂ → (r₂:ℝ) < (dW-2*ηW)*h₂ →
      ((h₂+r₂:ℕ):ℝ) ≤ (dW-ηW)*(m:ℝ) →
      ∃ (B : Digraph ↥Zᶜ) (Q : J × Fin 4 → Finset ↥Zᶜ)
        (M : ∀ i, Fin r₂ → Q i ≃ Q ((w.prodCongr (Equiv.refl (Fin 4))) i)),
        let L := liftDirectedPair e e B
        let U := liftDirectedPair e e (successorCellMatchingUnion Q
          (w.prodCongr (Equiv.refl (Fin 4))) M)
        L ≤ G \ E ∧ U ≤ G \ (E ⊔ L) ∧
        (∀ i, IsSuperregularPair B ηB ((r₁:ℝ)/mB) (A i) (A (s i))) ∧
        (∀ x y, B.Adj x y → ∃ i, x ∈ A i ∧ y ∈ A (s i)) ∧
        (∀ j, (univ : Finset (Fin 4)).biUnion (fun h => Q (j,h)) = D j) ∧
        (∀ i, (Q i).card = m) ∧ (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) ∧
        (∀ i p z, p ≠ z → ∀ x, M i p x ≠ M i z x) ∧
        ((E ⊔ L ⊔ U) ≤ G ∧ Disjoint E L ∧ Disjoint E U ∧ Disjoint L U ∧
          ∀ x, let d := if x ∈ Z then q*r₃ else r₁+r₂+r₃
            inDegree (E ⊔ L ⊔ U) x = d ∧ outDegree (E ⊔ L ⊔ U) x = d) := by
  obtain ⟨N₁,hN₁⟩ := kuhn_osthus_lemma_9_3_cycle_component.{0}
    εD εB ηB δB hεD.le hSmall hεB hεB₁ hηB hηB₁ hδB hTolB
  obtain ⟨N₂,hN₂⟩ := kuhn_osthus_lemma_9_3_walk_component.{v}
    C εW ηW dW aW hC hεW hηW hηW₁ haW hFloorW hTolW
  refine ⟨N₁,N₂,?_⟩
  intro V I J _ G E Z A s D w q r₁ r₂ r₃ mB m h₁ h₂ loss R e
    hE hEDeg hACover hDCover hA hD hMinY hY hCard hMinD hm hDSize hProfile hAPairs hDPairs
    hEBudget hCut₁ hDemand₁ hRect₁ hLoss₁ hBudget₁ hBudget₂ hh₂ hCut₂ hDemand₂ hDegree₂
  let E₀ := induced E Zᶜ
  have hE₀ : E₀ ≤ R := fun _ _ h => hE h
  have hE₀Deg (x : ↥Zᶜ) : inDegree E₀ x ≤ r₃ ∧ outDegree E₀ x ≤ r₃ := by
    obtain ⟨hi,ho⟩ := hEDeg x.val
    have hx := mem_compl.mp x.prop
    simp only [if_neg hx] at hi ho
    change inDegree (induced E Zᶜ) x ≤ r₃ ∧ outDegree (induced E Zᶜ) x ≤ r₃
    constructor
    · rw [induced_inDegree,←hi,←inProfile_card]
      exact card_le_card inter_subset_right
    · rw [induced_outDegree,←ho,←outProfile_card]
      exact card_le_card inter_subset_right
  let eA (i : I) : Fin mB ≃ A i :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe,hCard i])).symm
  have hNonempty (i : I) : (A i).Nonempty := card_pos.mp (by rwa [hCard])
  have hAPairs' (i : I) : IsLowerSuperregularPair (R \ E₀) εD dB (A i) (A (s i)) :=
    IsLowerSuperregularPair.after_bounded_arc_deletion hE₀ r₃ hE₀Deg _ _ (hNonempty i)
      (hNonempty (s i)) _ (hCard i) (hCard (s i)) ε₀ εD dB aD hεD hεD₁ haD hdB.le
      hTolD hEBudget (hAPairs i)
  choose d hd hLower hCentred using hAPairs'
  have hMap (i : I) : (univ : Finset (Fin mB)).map (clusterEmbedding (eA i)) = A i := by
    ext x
    rw [mem_map]
    exact ⟨fun ⟨y,_,he⟩ => he ▸ (eA i y).prop,
      fun hx => ⟨(eA i).symm ⟨x,hx⟩,mem_univ _,congrArg Subtype.val ((eA i).apply_symm_apply _)⟩⟩
  have hAPairCoords (i : I) : IsCentredSuperregular
      (pullDirectedPair (clusterEmbedding (eA i)) (clusterEmbedding (eA (s i))) (R \ E₀)) εD (d i) := by
    apply (centred_superregular_iff_pair_univ _ _ _).mpr
    apply superregular_pullDirectedPair
    simpa only [hMap] using hCentred i
  have hBuild := hN₁ (R \ E₀) s A eA r₁ h₁ loss dB d
  simp only [Fintype.card_fin] at hBuild
  obtain ⟨B,hB,hBPair,hBDeg,hBNext⟩ := hBuild hMinY hdB hd
    hA hAPairCoords hCut₁ hDemand₁ hRect₁ hLoss₁ hBudget₁
  have hBLoss (x : ↥Zᶜ) : inDegree B x = r₁ ∧ outDegree B x = r₁ := by
    obtain ⟨i,hi⟩ := hACover x
    exact hBDeg i ⟨x,hi⟩
  have hEB : Disjoint E₀ B := disjoint_iff_inf_le.mpr (fun _ _ h => (hB h.2).2 h.1)
  have hLoss (x : ↥Zᶜ) : inDegree (E₀ ⊔ B) x ≤ r₁+r₃ ∧ outDegree (E₀ ⊔ B) x ≤ r₁+r₃ := by
    obtain ⟨ho,hi⟩ := degrees_sup_of_disjoint E₀ B (disjoint_iff_inf_le.mp hEB) x
    rw [hi,ho,(hBLoss x).1,(hBLoss x).2]
    exact ⟨by have := (hE₀Deg x).1; omega,by have := (hE₀Deg x).2; omega⟩
  obtain ⟨Q,hQCover,hQSize,hQDis,M,hU,hM,hUDeg,_⟩ :=
    hN₂ R (E₀ ⊔ B) (sup_le hE₀ (fun _ _ h => (hB h).1)) w D m (r₁+r₃) r₂ h₂
      hm hMinD hDSize hProfile hD hBudget₂ (fun _ x _ => hLoss x) hDPairs hh₂ hCut₂ hDemand₂ hDegree₂
  let F := successorCellMatchingUnion Q (w.prodCongr (Equiv.refl (Fin 4))) M
  let L := liftDirectedPair e e B
  let U := liftDirectedPair e e F
  have hLiftB : L ≤ G \ E := by
    rintro x y ⟨a,b,rfl,rfl,h⟩
    exact hB h
  have hLiftF : U ≤ G \ (E ⊔ L) := by
    rintro x y ⟨a,b,rfl,rfl,h⟩
    have h' := hU h
    exact ⟨h'.1,fun he => h'.2 (he.imp id ((liftDirectedPair_adj e e B a b).mp))⟩
  have hSupp (K : Digraph ↥Zᶜ) {x y : V} (h : (liftDirectedPair e e K).Adj x y) :
      x ∉ Z ∧ y ∉ Z := by
    obtain ⟨a,b,rfl,rfl,_⟩ := h
    exact ⟨mem_compl.mp a.prop,mem_compl.mp b.prop⟩
  have hFDeg (x : ↥Zᶜ) : inDegree F x = r₂ ∧ outDegree F x = r₂ := by
    letI : DecidableEq ↥Zᶜ := Classical.decEq _
    obtain ⟨j,hj⟩ := hDCover x
    rw [←hQCover j] at hj
    obtain ⟨b,_,hb⟩ := mem_biUnion.mp hj
    exact hUDeg (j,b) ⟨x,hb⟩
  have hLiftDeg (K : Digraph ↥Zᶜ) (r : ℕ)
      (hK : ∀ x, inDegree K x = r ∧ outDegree K x = r) (x : V) (hx : x ∉ Z) :
      inDegree (liftDirectedPair e e K) x = r ∧ outDegree (liftDirectedPair e e K) x = r := by
    let a : ↥Zᶜ := ⟨x,mem_compl.mpr hx⟩
    exact ⟨(lift_pair_semidegree e e K false a).trans (hK a).1,
      (lift_pair_semidegree e e K true a).trans (hK a).2⟩
  have hPhysicalPair (i : I) : IsSuperregularPair B ηB ((r₁:ℝ)/mB) (A i) (A (s i)) := by
    simpa only [hMap,Fintype.card_fin] using superregular_of_pullDirectedPair B (clusterEmbedding (eA i))
      (clusterEmbedding (eA (s i))) _ _ _ _ ((centred_superregular_iff_pair_univ _ _ _).mp (hBPair i))
  exact ⟨B,Q,M,hLiftB,hLiftF,hPhysicalPair,hBNext,hQCover,hQSize,hQDis,hM,
    chord_absorber_union_of_reserves G E L U Z q r₃ r₁ r₂ hE hLiftB hLiftF
      (fun _ _ => hSupp B) (fun _ _ => hSupp F) hEDeg (hLiftDeg B _ hBLoss) (hLiftDeg F _ hFDeg)⟩

end OverfullWork.DirectedRobustExpansion
