module

public import OverfullWork.KuhnOsthusWindingIntervalGeometry
public import OverfullWork.OsthusStadenNestedRefinement
public import OverfullWork.OsthusStadenSliceRegularity
public import OverfullWork.KuhnOsthusWalkCoordinates
public import OverfullWork.RealDirectedRobustHamilton

@[expose] public section


/-! Uniformly refine an ordered coarse cycle and retain the physical
profiles in the wound cycle of Kühn–Osthus, Theorem 1.2. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u

/-- Reindex a reduced graph by a bijection without changing its
robust expansion parameters or its physical semidegrees. -/
theorem robust_reduced_graph_reindex {V W : Type*} [Fintype V] [Fintype W]
    (D : Digraph V) (e : W ≃ V) (ν τ : ℝ) (hD : IsRealRobust D ν τ) :
    let R := fibrePullback D e e
    IsRealRobust R ν τ ∧ ∀ v, inDegree R v = inDegree D (e v) ∧ outDegree R v = outDegree D (e v) := by
  intro R
  have hOrder := Fintype.card_congr e
  have hN (S : Finset W) (v : W) :
      inNeighbours R S v = inNeighbours D (S.map e.toEmbedding) (e v) := by
    unfold inNeighbours
    rw [filter_map,card_map]
    rfl
  have hImage (S : Finset W) :
      (realNeighbourhood R ν S).map e.toEmbedding = realNeighbourhood D ν (S.map e.toEmbedding) := by
    unfold realNeighbourhood
    rw [←univ_map_equiv_to_embedding e,filter_map]
    congr 1
    ext v
    simp only [mem_filter,mem_univ,true_and,Function.comp_apply,Equiv.coe_toEmbedding,hN,hOrder]
  constructor
  · intro S hLo hHi
    have h := hD (S.map e.toEmbedding) (by rwa [card_map,←hOrder]) (by rwa [card_map,←hOrder])
    rwa [←hImage,card_map,card_map,←hOrder] at h
  · have hF (v : V) : fibreWeight e univ v = 1 := by
      have he : (univ : Finset W).filter (fun w => e w = v) = {e.symm v} := by
        ext w
        simp only [mem_filter,mem_univ,true_and,mem_singleton]
        exact e.eq_symm_apply.symm
      rw [fibreWeight,he,card_singleton]
    intro w
    simpa only [mul_one] using fibrePullback_semidegrees D e e 1 hF hF w

/-- Obtain the cyclic labels of the coarse reduced graph after its
robustness and minimum semidegrees have been verified. -/
theorem exists_kuhn_osthus_ordered_reduced_cycle (ν τ γ : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (D : Digraph V), N ≤ Fintype.card V →
      IsRealRobust D ν τ →
      (∀ v, γ*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ)) →
      (∀ v, γ*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) →
      ∃ e : Fin (Fintype.card V) ≃ V,
        let R := fibrePullback D e e
        (∀ j, R.Adj j (finRotate (Fintype.card V) j)) ∧
        IsRealRobust R ν τ ∧ ∀ j, inDegree R j = inDegree D (e j) ∧ outDegree R j = outDegree D (e j) := by
  obtain ⟨N,hN⟩ := DirectedAbsorbingLadder.exists_hamilton_threshold.{u} ν τ γ hν hντ hτγ hγ
  refine ⟨N,?_⟩
  intro V _ D hSize hRob hIn hOut
  obtain ⟨e,hC⟩ := exists_fin_cyclic_order (hN D hSize hRob hIn hOut)
  exact ⟨e,hC,robust_reduced_graph_reindex D e ν τ hRob⟩

/-- Preserve a fixed fraction of a large parent profile after
removing vertices from a uniformly refined cell. This is the
profile inequality of (CSys8) with an explicit deletion budget. -/
theorem UniformProfileCell.lower_after_trimming {V J : Type*} {profiles : J → Finset V}
    {P A B : Finset V} {ℓ : ℕ} {ε τ θ : ℝ}
    (hU : UniformProfileCell profiles P A ℓ ε) (hBA : B ⊆ A)
    (hℓ : 0 < ℓ) (hετ : ε ≤ τ) (hθ : θ ≤ 1-ε)
    (hLoss : ((A \ B).card:ℝ) ≤ (1-ε-θ)*(τ*(P.card:ℝ)/(ℓ:ℝ))) :
    ∀ j, τ*(P.card:ℝ) ≤ profileCount P (profiles j) →
      θ*(profileCount P (profiles j)/(ℓ:ℝ)) ≤ profileCount B (profiles j) := by
  intro j hj
  have hℓR : 0 < (ℓ:ℝ) := by exact_mod_cast hℓ
  have hOld := hU j ((mul_le_mul_of_nonneg_right hετ (Nat.cast_nonneg _)).trans hj)
  have hNew := exceptional_overlap_loss (profiles j) A B
  rw [inter_eq_right.mpr hBA] at hNew
  have hPay := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hj hℓR.le)
    (by linarith only [hθ] : 0 ≤ 1-ε-θ)
  linarith only [(abs_le.mp hOld).1,hNew,hPay,hLoss]

set_option maxHeartbeats 650000 in
/-- Refine the coarse cells uniformly in the two directed profiles.
The physical cells follow the same winding order as the adjacency
and degree data in the lifted reduced digraph. -/
theorem exists_kuhn_osthus_wound_refinement (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε)
    (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {k m : ℕ}
      (G : Digraph V) (R₀ : Digraph (Fin k)) (A : Fin k → Finset V)
      (hk : 0 < k) (η d ν τ : ℝ),
      let parent := windingParent (n := ℓ*k) k hk
      let R := fibrePullback R₀ parent parent
      N ≤ ℓ*m → (∀ i, (A i).card = ℓ*m) →
      2*(Fintype.card V:ℝ) ≤ C*((ℓ*m:ℕ):ℝ) →
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) →
      (ℓ:ℝ)*ε ≤ η → 2*ε ≤ η → η ≤ 1 →
      (∀ i j, R₀.Adj i j → IsUniform G ε (A i) (A j) ∧ d+ε ≤ density G (A i) (A j)) →
      (∀ i, R₀.Adj i (finRotate k i)) →
      0 < ν → ν ≤ τ → τ ≤ 1/4 → 2 ≤ τ*(k:ℝ) → IsRealRobust R₀ ν τ →
      ∃ X : Fin (ℓ*k) → Finset V,
        (∀ j, (X j).card = m ∧ X j ⊆ A (parent j)) ∧
        (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧
        (∀ i, (univ : Finset (Fin ℓ)).biUnion (fun a => X (intervalPosition a i)) = A i) ∧
        (∀ j, UniformProfileCell (inProfile G) (A (parent j)) (X j) ℓ ε ∧
          UniformProfileCell (outProfile G) (A (parent j)) (X j) ℓ ε) ∧
        (∀ i j, R.Adj i j → IsUniform G η (X i) (X j) ∧ d ≤ density G (X i) (X j)) ∧
        (∀ i, parent (finRotate (ℓ*k) i) = finRotate k (parent i) ∧ R.Adj i (finRotate (ℓ*k) i)) ∧
        IsRealRobust R (ν^2/2) (2*τ) ∧
        ∀ i, inDegree R i = inDegree R₀ (parent i)*ℓ ∧ outDegree R i = outDegree R₀ (parent i)*ℓ := by
  obtain ⟨N,hN⟩ := exists_ambient_uniform_refinement.{u,u} C ε hC hε ℓ hℓ
  refine ⟨N,?_⟩
  intro V _ k m G R₀ A hk η d ν τ parent R hNmin hCard hProfiles hDis hScale hTol hη₁
    hReg hCycle hν hντ hτ hOrder hRob
  let profiles : V ⊕ V → Finset V := Sum.elim (inProfile G) (outProfile G)
  have hRef (i : Fin k) : Nonempty (UniformRefinementOf (I := Fin ℓ) profiles (A i) m ε) :=
    hN profiles (A i) m (by rwa [hCard]) (hCard i)
      (by simpa only [Fintype.card_sum,Nat.cast_add,hCard,two_mul] using hProfiles)
  let F (i : Fin k) := Classical.choice (hRef i)
  let p : Fin (ℓ*k) ≃ Fin ℓ × Fin k := finProdFinEquiv.symm
  have hp (j : Fin (ℓ*k)) : (p j).2 = parent j := by rfl
  let X (j : Fin (ℓ*k)) := (F (parent j)).cells (p j).1
  have hY (j : Fin (ℓ*k)) : (X j).card = m := (F (parent j)).size _
  have hSub (j : Fin (ℓ*k)) : X j ⊆ A (parent j) := (F (parent j)).subset _
  have hApart (i j : Fin (ℓ*k)) (hij : i ≠ j) : Disjoint (X i) (X j) := by
    by_cases h : parent i = parent j
    · have ha : (p i).1 ≠ (p j).1 := fun h' => hij (p.injective (Prod.ext h'
        ((hp i).trans (h.trans (hp j).symm))))
      change Disjoint ((F (parent i)).cells (p i).1) ((F (parent j)).cells (p j).1)
      rw [←h]
      exact (F (parent i)).disjoint _ _ ha
    · exact (hDis _ _ h).mono (hSub i) (hSub j)
  have hCover (i : Fin k) : (univ : Finset (Fin ℓ)).biUnion (fun a => X (intervalPosition a i)) = A i := by
    have he (a : Fin ℓ) : p (intervalPosition a i) = (a,i) :=
      finProdFinEquiv.symm_apply_apply (a,i)
    have he' (a : Fin ℓ) : X (intervalPosition a i) = (F i).cells a := by
      change (F (parent (intervalPosition a i))).cells (p (intervalPosition a i)).1 = _
      rw [←hp,he]
    simp only [he']
    exact (F i).cover
  have hUniform (j : Fin (ℓ*k)) : UniformProfileCell (inProfile G) (A (parent j)) (X j) ℓ ε ∧
      UniformProfileCell (outProfile G) (A (parent j)) (X j) ℓ ε := by
    constructor
    · intro v hv
      simpa only [Fintype.card_fin,profiles,Sum.elim_inl,X] using (F (parent j)).uniform (p j).1 (.inl v)
        (by simpa only [profiles,Sum.elim_inl] using hv)
    · intro v hv
      simpa only [Fintype.card_fin,profiles,Sum.elim_inr,X] using (F (parent j)).uniform (p j).1 (.inr v)
        (by simpa only [profiles,Sum.elim_inr] using hv)
  have hScale' (i : Fin (ℓ*k)) : ((A (parent i)).card:ℝ)*ε ≤ ((X i).card:ℝ)*η := by
    rw [hCard,hY,Nat.cast_mul]
    calc
      _ = (m:ℝ)*((ℓ:ℝ)*ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hScale (Nat.cast_nonneg _)
  have hLarge (i : Fin (ℓ*k)) : ((A (parent i)).card:ℝ)*ε ≤ (X i).card :=
    (hScale' i).trans (mul_le_of_le_one_right (Nat.cast_nonneg _) hη₁)
  have hRegX (i j : Fin (ℓ*k)) (h : R.Adj i j) :
      IsUniform G η (X i) (X j) ∧ d ≤ density G (X i) (X j) := by
    obtain ⟨hU,hD⟩ := hReg (parent i) (parent j) h
    exact ⟨uniform_on_subcells G hU (hSub i) (hSub j) (hLarge i) (hLarge j) (hScale' i) (hScale' j) hTol,
      by have hh := density_on_subcells G hU hD (hSub i) (hSub j) (hLarge i) (hLarge j); linarith⟩
  have hNext (j : Fin (ℓ*k)) : parent (finRotate (ℓ*k) j) = finRotate k (parent j) := by
    apply Fin.ext
    rw [finRotate_val_modulo]
    change (finRotate (ℓ*k) j).val%k = (j.val%k+1)%k
    rw [finRotate_val_modulo,Nat.mod_mod_of_dvd _ (dvd_mul_left k ℓ),Nat.mod_add_mod]
  have hFib := windingParent_fibres ℓ k hk
  have hCycleX (j : Fin (ℓ*k)) : R.Adj j (finRotate (ℓ*k) j) := by
    change R₀.Adj (parent j) (parent (finRotate (ℓ*k) j))
    rw [hNext]
    exact hCycle (parent j)
  exact ⟨X,fun j => ⟨hY j,hSub j⟩,hApart,hCover,hUniform,hRegX,fun j => ⟨hNext j,hCycleX j⟩,
    fibrePullback_realRobust R₀ parent parent ℓ hFib hFib hℓ ν τ hν hντ hτ
      (by simpa only [Fintype.card_fin] using hOrder) hRob,
    fibrePullback_semidegrees R₀ parent parent ℓ hFib hFib⟩

end OverfullWork.DirectedRobustExpansion
