module

public import OverfullWork.KuhnOsthusExceptionalFreePairs
public import OverfullWork.KuhnOsthusOriginalInterval

@[expose] public section


/-! Construct one complete exceptional path system from the
exceptional endpoints and the regular pairs of a wrapped interval. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u

/-- Given the selected endpoints, route and realize the correcting
chords, trim the successor pairs, and complete the physical interval.
The free pairs have individual density parameters bounded below by d. -/
theorem exists_original_interval_of_scheduled_chords_lower
    (d δ ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 2*ε < d)
    (hCost : ν ≤ (d-2*ε)*τ) (hDegrees : γ ≤ d-2*ε) (hTol : 2*δ ≤ ε) :
    ∃ N : ℕ, ∀ {V : Type*} [Fintype V] {W : Type u} [Fintype W] {n : ℕ}
      (G : Digraph V) (H L : Digraph W) (R : Digraph (Fin (n+1)))
      (Z A S T : Finset V) (cluster : W → Fin (n+1)),
      let s := finRotate (n+1)
      let B := (univ : Finset W).filter (fun x => cluster x = 0)
      ∀ (coord : W ⊕ B ≃ A) (first : B ≃ S) (last : B ≃ T)
        (endpoint : Bool × Z → W)
        (m w e endpointCap routeCap routeBudget radius growth cutoff : ℕ),
        let loss := endpointCap+(routeCap+2)+2*endpointCap
        (∀ b : B, (coord (Sum.inl b.val)).val = (first b).val) →
        (∀ b : B, (coord (Sum.inr b)).val = (last b).val) →
        Disjoint A Z → Function.Injective endpoint →
        (∀ p, cluster (endpoint p) ≠ 0) →
        (∀ z, s.symm (cluster (endpoint (true,z))) ≠ 0) →
        (∀ z, s (cluster (endpoint (false,z))) ≠ 0) →
        (∀ z : Z, G.Adj (coord (Sum.inl (endpoint (false,z)))).val z ∧
          G.Adj z (coord (Sum.inl (endpoint (true,z)))).val) →
        (∀ x y, cluster x ≠ 0 → cluster y ≠ 0 → H.Adj x y →
          G.Adj (coord (Sum.inl x)).val (coord (Sum.inl y)).val) →
        (∀ x y, (splitIntervalDigraph L B).Adj x y → G.Adj (coord x).val (coord y).val) →
        (∀ i, (intervalCluster cluster i).card = m) →
        (∀ i, ((univ : Finset (Bool × Z)).filter (fun p => cluster (endpoint p) = i)).card ≤ endpointCap) →
        w+endpointCap ≤ m → 2*(routeCap+2+2*endpointCap)+e < w →
        (∀ i, ¬R.Adj i i) → IsRobustAt R radius cutoff → 0 < growth →
        2*(routeBudget+1)+growth ≤ radius →
        (∀ i, cutoff+2*(routeBudget+1) ≤ outDegree R i) →
        (∀ i, cutoff ≤ inDegree R i) →
        Z.card*(2*((n+1)/growth+3)) < routeCap*(routeBudget+1) →
        (∀ i j, R.Adj i j → ∀ X ⊆ intervalCluster cluster i, ∀ Y ⊆ intervalCluster cluster j,
          e < X.card → e < Y.card → 0 < incidences H X Y) →
        loss < m → N ≤ m-loss →
        ε*(m:ℝ)+1 ≤ (d-2*ε)*((m-loss:ℕ):ℝ) →
        (m:ℝ)*δ+loss ≤ ((m-loss:ℕ):ℝ)*ε →
        (∀ i, IsLowerSuperregularPair L δ d (intervalCluster cluster i) (intervalCluster cluster (s i))) →
        Nonempty (OriginalInterval G Z A S T) := by
  classical
  obtain ⟨N,hN⟩ := exists_original_interval_of_wrapped_lower_superregular_pairs.{u}
    d ε ν τ γ hν hWidth hε.le hτγ hγ hd hCost hDegrees
  refine ⟨N,?_⟩
  intro V _ W _ n G H L R Z A S T cluster s B coord first last endpoint
    m w e endpointCap routeCap routeBudget radius growth cutoff loss
    hFirst hLast hDis hInj hInside hStart hFinish hExc hChord hReserve hSize hCap hW hRoom
    hR hRobust hg hAvoid hOut hIn hMass hRect hm hNsize hHall hPay hPair
  obtain ⟨D,hPath,hKeep,hSupport,hBalance,hFree⟩ := exists_balanced_exceptional_matching R H s
    cluster endpoint {0} m w e endpointCap routeCap routeBudget radius growth cutoff
    hSize hInj (fun p => by simpa only [mem_singleton] using hInside p)
    (fun z => by simpa only [mem_singleton] using hStart z)
    (fun z => by simpa only [mem_singleton] using hFinish z) hR
    (by
      intro i
      convert hCap i using 2
      ext p
      simp only [mem_filter,mem_univ,true_and]) hW hRoom hRobust hg
    (by simpa only [card_singleton] using hAvoid) (fun i => by simpa only [card_singleton] using hOut i)
    hIn (by simpa only [Fintype.card_coe,Fintype.card_fin] using hMass) hRect
  let r := ⌈ε*(m:ℝ)⌉₊
  have hM : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨hOverlap,hMin,hr,hFreePairs⟩ := free_lower_successor_pairs_of_exceptional_budget
    D L cluster s m loss N r d δ ε hd hε hε1 hTol hm hNsize
    (Nat.ceil_pos.mpr (mul_pos hε hM)) (Nat.le_ceil _)
    ((Nat.ceil_lt_add_one (mul_nonneg hε.le hM.le)).le.trans hHall) hPay hSize hFree hPair
  let f (p : Bool × Z) := (coord (Sum.inl (endpoint p))).val
  have hf : Function.Injective f :=
    Subtype.coe_injective.comp (coord.injective.comp (Sum.inl_injective.comp hInj))
  have hEnd (p : Bool × Z) : f p ∈ A \ (S ∪ T) := by
    refine mem_sdiff.mpr ⟨(coord (Sum.inl (endpoint p))).prop,?_⟩
    intro hp
    rcases mem_union.mp hp with hp | hp
    · let b := first.symm ⟨f p,hp⟩
      have he : (coord (Sum.inl b.val)).val = f p :=
        (hFirst b).trans (congrArg Subtype.val (first.apply_symm_apply ⟨f p,hp⟩))
      have he' : b.val = endpoint p :=
        Sum.inl.inj (coord.injective (Subtype.ext he))
      exact hInside p (he' ▸ (mem_filter.mp b.prop).2)
    · let b := last.symm ⟨f p,hp⟩
      have he : (coord (Sum.inr b)).val = f p :=
        (hLast b).trans (congrArg Subtype.val (last.apply_symm_apply ⟨f p,hp⟩))
      exact Sum.inl_ne_inr (coord.injective (Subtype.ext he.symm))
  have hInsideD (x y : W) (h : D.Adj x y) : y ∉ B := fun hy =>
    (hSupport x y h).2.1 (mem_singleton.mpr (mem_filter.mp hy).2)
  have hArc (x y : W ⊕ B) (h : (splitIntervalDigraph (D ⊔ L) B).Adj x y) :
      G.Adj (coord x).val (coord y).val ∨ ∃ z : Z, f (false,z) = (coord x).val ∧
        f (true,z) = (coord y).val := by
    cases x with
    | inr b => exact h.elim
    | inl x =>
      cases y with
      | inl y =>
        have hy : y ∉ B ∧ (D ⊔ L).Adj x y := h
        rcases (Digraph.sup_adj _ _ _ _).mp hy.2 with hD | hL
        · obtain ⟨hx,hy',h⟩ := hSupport x y hD
          rcases h with ⟨z,ha,hb⟩ | hH
          · exact Or.inr ⟨z,congrArg (fun x : W => (coord (Sum.inl x)).val) ha,
              congrArg (fun x : W => (coord (Sum.inl x)).val) hb⟩
          · exact Or.inl (hChord x y (fun he => hx (mem_singleton.mpr he))
              (fun he => hy' (mem_singleton.mpr he)) hH)
        · exact Or.inl (hReserve _ _ ⟨hy.1,hL⟩)
      | inr y =>
        have hy : (D ⊔ L).Adj x y.val := h
        rcases (Digraph.sup_adj _ _ _ _).mp hy with hD | hL
        · exact (hInsideD x y hD y.prop).elim
        · exact Or.inl (hReserve _ _ hL)
  exact hN G D L Z A S T cluster (fun _ => r) coord first last f
    hFirst hLast hDis hEnd hf hExc hArc (fun z =>
      ⟨endpoint (false,z),endpoint (true,z),hKeep z,rfl,rfl⟩)
    hPath hInsideD hBalance hOverlap hMin hr hFreePairs

/-- Given the selected endpoints, route and realize the correcting
chords, trim the successor pairs, and complete the physical interval.
The Hall cutoff is rounded once at the original cluster size. -/
theorem exists_original_interval_of_scheduled_chords
    (d δ ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 2*ε < d) (hd1 : d ≤ 1)
    (hCost : ν ≤ (d-2*ε)*τ) (hDegrees : γ ≤ d-2*ε) (hTol : 2*δ ≤ ε) :
    ∃ N : ℕ, ∀ {V : Type*} [Fintype V] {W : Type u} [Fintype W] {n : ℕ}
      (G : Digraph V) (H L : Digraph W) (R : Digraph (Fin (n+1)))
      (Z A S T : Finset V) (cluster : W → Fin (n+1)),
      let s := finRotate (n+1)
      let B := (univ : Finset W).filter (fun x => cluster x = 0)
      ∀ (coord : W ⊕ B ≃ A) (first : B ≃ S) (last : B ≃ T)
        (endpoint : Bool × Z → W)
        (m w e endpointCap routeCap routeBudget radius growth cutoff : ℕ),
        let loss := endpointCap+(routeCap+2)+2*endpointCap
        (∀ b : B, (coord (Sum.inl b.val)).val = (first b).val) →
        (∀ b : B, (coord (Sum.inr b)).val = (last b).val) →
        Disjoint A Z → Function.Injective endpoint →
        (∀ p, cluster (endpoint p) ≠ 0) →
        (∀ z, s.symm (cluster (endpoint (true,z))) ≠ 0) →
        (∀ z, s (cluster (endpoint (false,z))) ≠ 0) →
        (∀ z : Z, G.Adj (coord (Sum.inl (endpoint (false,z)))).val z ∧
          G.Adj z (coord (Sum.inl (endpoint (true,z)))).val) →
        (∀ x y, cluster x ≠ 0 → cluster y ≠ 0 → H.Adj x y →
          G.Adj (coord (Sum.inl x)).val (coord (Sum.inl y)).val) →
        (∀ x y, (splitIntervalDigraph L B).Adj x y → G.Adj (coord x).val (coord y).val) →
        (∀ i, (intervalCluster cluster i).card = m) →
        (∀ i, ((univ : Finset (Bool × Z)).filter (fun p => cluster (endpoint p) = i)).card ≤ endpointCap) →
        w+endpointCap ≤ m → 2*(routeCap+2+2*endpointCap)+e < w →
        (∀ i, ¬R.Adj i i) → IsRobustAt R radius cutoff → 0 < growth →
        2*(routeBudget+1)+growth ≤ radius →
        (∀ i, cutoff+2*(routeBudget+1) ≤ outDegree R i) →
        (∀ i, cutoff ≤ inDegree R i) →
        Z.card*(2*((n+1)/growth+3)) < routeCap*(routeBudget+1) →
        (∀ i j, R.Adj i j → ∀ X ⊆ intervalCluster cluster i, ∀ Y ⊆ intervalCluster cluster j,
          e < X.card → e < Y.card → 0 < incidences H X Y) →
        loss < m → N ≤ m-loss →
        ε*(m:ℝ)+1 ≤ (d-2*ε)*((m-loss:ℕ):ℝ) →
        (m:ℝ)*δ+loss ≤ ((m-loss:ℕ):ℝ)*ε →
        (∀ i, IsSuperregularPair L δ d (intervalCluster cluster i) (intervalCluster cluster (s i))) →
        Nonempty (OriginalInterval G Z A S T) := by
  obtain ⟨N,hN⟩ := exists_original_interval_of_scheduled_chords_lower.{u}
    d δ ε ν τ γ hν hWidth hε hε1 hτγ hγ hd hCost hDegrees hTol
  refine ⟨N,?_⟩
  intro V _ W _ n G H L R Z A S T cluster s B coord first last endpoint
    m w e endpointCap routeCap routeBudget radius growth cutoff loss
    hFirst hLast hDis hInj hInside hStart hFinish hExc hChord hReserve hSize hCap hW hRoom
    hR hRobust hg hAvoid hOut hIn hMass hRect hm hNsize hHall hPay hPair
  exact hN G H L R Z A S T cluster coord first last endpoint
    m w e endpointCap routeCap routeBudget radius growth cutoff
    hFirst hLast hDis hInj hInside hStart hFinish hExc hChord hReserve hSize hCap hW hRoom
    hR hRobust hg hAvoid hOut hIn hMass hRect hm hNsize hHall hPay
    (fun i => ⟨d,le_rfl,hd1,hPair i⟩)

end OverfullWork.DirectedRobustExpansion
