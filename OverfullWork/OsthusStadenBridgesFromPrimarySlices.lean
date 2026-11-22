module

public import OverfullWork.OsthusStadenPhysicalBridgeAssembly
public import OverfullWork.KuhnOsthusWindingIntervalGeometry

@[expose] public section


/-! The end of §5.5, starting with the aligned physical primary slices. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical

/-- All arcs of a physical thin reserve remain in its original pure
host, including those in copies left out of the primary factors. -/
theorem primaryThinDigraphs_le {V I : Type*} [Fintype V] [Fintype I]
    {H : Digraph V} {f : V → Option I} {M : I → I → ℕ}
    {m₀ b : ℕ} {β γ η a exc : ℝ}
    (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exc) (q : Fin 5) :
    primaryThinDigraphs B q ≤ H := by
  rintro x y ⟨e,z,w,hx,hy,h⟩
  exact B.copy_le e ⟨B.kept e.1.1 z,B.kept e.1.2 w,hx,hy,
    (B.copy_partition e z w).mpr (Or.inr ⟨q,h⟩)⟩

/-- The cyclic order returned by the robust Hamilton theorem has one
cycle in the original primary labels. -/
theorem spanning_conjugate_finRotate {I : Type*} {n : ℕ} (e : Fin n ≃ I) :
    ∀ i k, (e.permCongr (finRotate n)).SameCycle i k := by
  intro i k
  have h : (finRotate n).SameCycle (e.symm i) (e.symm k) := by
    by_cases hn : 2 ≤ n
    · exact (isCycle_finRotate_of_le hn).sameCycle (finRotate_interval_ne_self hn _)
        (finRotate_interval_ne_self hn _)
    · have he : e.symm i = e.symm k := Fin.ext (by
        have hi := (e.symm i).isLt
        have hk := (e.symm k).isLt
        omega)
      rw [he]
  obtain ⟨l,hl⟩ := h.exists_nat_pow_eq
  refine ⟨(l:ℤ),?_⟩
  rw [zpow_natCast]
  have hp := conjugate_power e.symm (finRotate n) l i
  change e.symm (((e.permCongr (finRotate n))^l) i) = _ at hp
  exact e.symm.injective (hp.trans hl)

set_option maxHeartbeats 2300000 in
/-- From the primary slice data, install the physical bridge arcs of
§5.5 at the same time as the one-vertex trim in all layers. -/
theorem exists_osthus_staden_bridged_primary_slices_with_reserves
    {V I : Type*} [Fintype V] [Fintype I]
    {H G : Digraph V} {f : V → Option I} {m₀ b r s p m mBase : ℕ}
    [NeZero (2*s)] [NeZero p] {β γ η a exc : ℝ}
    (B : OsthusStadenPrimaryReserveData H f
      (reducedMultiplicity (quotient H f) (fun i j => density H (cluster f i) (cluster f j)) β)
      m₀ b β γ η a exc)
    (E : Fin r → I → Digraph V) (g : Fin r → V → Option I) (σ : Fin r → Equiv.Perm I)
    (τ ε δ d εBase εH0 dH0 : ℝ)
    (R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
      (cluster (g t) i) (2*s) p m τ τ τ)
    (base : ∀ i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
      (cluster B.partition i) (2*s) p mBase εBase εBase εBase)
    (A : UnwoundPrimarySlices G (primaryThinDigraphs B) E g σ τ ε d R)
    (D : PrimaryRedSelection (p := p) A.coordinates) (C : Equiv.Perm I)
    (κ loss : ℕ)
    (hs : 3 ≤ s) (hHost : H ≤ G)
    (hCSpan : ∀ i k, C.SameCycle i k)
    (hC : ∀ i, (quotient H f).Adj i (C i))
    (hσ : ∀ t i, (quotient H f).Adj i (σ t i))
    (hDen : ∀ i k, (quotient H f).Adj i k →
      dH0+β ≤ density H (cluster f i) (cluster f k))
    (hβ : 0 < β) (hγ : 0 ≤ γ) (hη : 0 < η) (hη₁ : η ≤ 1)
    (hdH0 : 0 ≤ dH0) (hεH0 : 0 ≤ εH0)
    (hErr : 4*η ≤ γ*β) (hBad : η ≤ εH0*β)
    (hParent : ∀ t i, cluster (g t) i ⊆ cluster B.partition i)
    (hLoss : ∀ t i, (((cluster B.partition i) \ cluster (g t) i).card:ℝ) ≤ γ*dH0*(B.size:ℝ)/4)
    (hNear : ∀ t u, ((primaryPCells (R t) u) \ primaryPCells base u).card ≤ loss)
    (hCapacity : Fintype.card (RefinedFactorIndex r (2*s) p)+loss ≤ m)
    (hBadSize : 4*εH0*(B.size:ℝ) ≤ 2*(m:ℝ))
    (hτ : 0 ≤ τ) (hτ₁ : τ ≤ 1/8) (hFloor : 8*τ ≤ γ*dH0/4)
    (hκ : (κ:ℝ) < (1-8*τ)*(γ*dH0/4)*(m:ℝ))
    (hd : 0 ≤ d) (hd₁ : d ≤ 1) (hδ : 2*ε ≤ δ) (hδ₁ : δ ≤ 1)
    (hRoom : ε*((2*m:ℕ):ℝ)+1 ≤ δ*((2*m-1:ℕ):ℝ)) :
    let layer₀ := unwoundSlice E A.label A.factor
    let cells := fun (j : RefinedFactorIndex r (2*s) p) u => primaryPCells (R j.1) u
    ∃ src dst : RefinedFactorIndex r (2*s) p → I → RefinedVertex I (2*s) p,
    ∃ erase : RefinedFactorIndex r (2*s) p → RefinedVertex I (2*s) p → V,
      let halfIn := fun (j : RefinedFactorIndex r (2*s) p) i =>
        primaryHalfCell (R j.1) ((A.factor j).symm (src j i)) (redPhase p j.1.val).2
      let halfOut := fun (j : RefinedFactorIndex r (2*s) p) i =>
        primaryHalfCell (R j.1) (dst j i) (redPhase p j.1.val).2
      (∀ j i, (src j i).1.1 = i ∧ (dst j i).1.1 = C i) ∧
      (∀ j i, D.selectedPCell false j ((A.factor j).symm (src j i)) ∧
        D.selectedPCell true j (dst j i)) ∧
      (∀ j i k, src j i ≠ dst j k) ∧
      Function.Injective (fun q : RefinedFactorIndex r (2*s) p × RefinedVertex I (2*s) p =>
        erase q.1 q.2) ∧
      (∀ j u, erase j u ∈ cells j u ∧ erase j u ∈ primaryPCells base u) ∧
      ∃ P : TrimmedPhysicalBridgeLayers G layer₀ A.factor C cells erase src dst halfIn halfOut κ (2*m) δ d,
        P.UsesBridgeReserves (primaryThinDigraphs B 1) (primaryThinDigraphs B 0) := by
  let layer₀ := unwoundSlice E A.label A.factor
  let cells (j : RefinedFactorIndex r (2*s) p) u := primaryPCells (R j.1) u
  let Q := quotient H f
  choose src dst hTags hEdges hRed hSrc hDst hSep using fun j =>
    D.exists_bridge_order j hs Q C hC (hσ j.1)
  let halfIn (j : RefinedFactorIndex r (2*s) p) (i : I) :=
    primaryHalfCell (R j.1) ((A.factor j).symm (src j i)) (redPhase p j.1.val).2
  let halfOut (j : RefinedFactorIndex r (2*s) p) (i : I) :=
    primaryHalfCell (R j.1) (dst j i) (redPhase p j.1.val).2
  let HIn := primaryThinDigraphs B (1 : Fin 5)
  let HOut := primaryThinDigraphs B (0 : Fin 5)
  let useful (j : RefinedFactorIndex r (2*s) p) (i : I) := (cells j (src j i)).filter (fun x =>
    (κ:ℝ) < profileCount (halfIn j i) (inProfile HIn x) ∧
    (κ:ℝ) < profileCount (halfOut j i) (outProfile HOut x))
  have hUseful (j : RefinedFactorIndex r (2*s) p) (i : I) : m ≤ (useful j i).card := by
    have h := useful_bridge_vertices_in_physical_cells B E (g j.1) τ (R j.1)
      ((A.factor j).symm (src j i)) (src j i) (dst j i) (redPhase p j.1.val).2 (redPhase p j.1.val).2
      1 0 (hEdges j i).2 (hEdges j i).1 εH0 dH0 κ hβ hγ hη hη₁ hdH0 hεH0 hErr hBad
      (hDen _ _ (hEdges j i).2) (hDen _ _ (hEdges j i).1)
      (hParent j.1) (hLoss j.1) hBadSize hτ hτ₁ hFloor hκ
    change (cells j (src j i)).card ≤ 2*(useful j i).card at h
    rw [A.size_cells] at h
    omega
  obtain ⟨baseLabel,hBaseLabel,_⟩ := exists_p_cell_labels B.partition base
  have hBaseDis (u v : RefinedVertex I (2*s) p) (h : u ≠ v) :
      Disjoint (primaryPCells base u) (primaryPCells base v) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact h (Option.some.inj (((hBaseLabel x u).mpr hx).symm.trans ((hBaseLabel x v).mpr hy)))
  have hDis (j : RefinedFactorIndex r (2*s) p) (u v : RefinedVertex I (2*s) p) (h : u ≠ v) :
      Disjoint (cells j u) (cells j v) :=
    disjoint_left.mpr fun x hx hy =>
      h (Option.some.inj (((A.label_cell j.1 x u).mpr hx).symm.trans ((A.label_cell j.1 x v).mpr hy)))
  obtain ⟨erase,hFresh,hErase,hPick⟩ := exists_globally_distinct_bridge_and_trim_vertices
    (primaryPCells base) cells src useful loss hBaseDis hSrc (fun j u => hNear j.1 u)
    (fun j u => hCapacity.trans (by rw [A.size_cells]; omega))
    (fun j i => ⟨filter_subset _ _,hCapacity.trans (hUseful j i)⟩)
  refine ⟨src,dst,erase,hTags,hRed,hSep,hFresh,hErase,?_⟩
  apply exists_trimmed_physical_bridge_layers_with_reserves G HIn HOut layer₀ A.factor
    (fun j => σ j.1) (fun u => u.1.1) C cells erase src dst halfIn halfOut κ (2*m) ε δ d
  · exact A.slice_le
  · exact (primaryThinDigraphs_le B _).trans hHost
  · exact (primaryThinDigraphs_le B _).trans hHost
  · exact B.thin_disjoint _ _ (by decide : (1:Fin 5) ≠ 0)
  · exact A.slice_disjoint
  · exact fun j => ⟨A.slice_thin_disjoint j _,A.slice_thin_disjoint j _⟩
  · exact hCSpan
  · rintro ⟨t,c,e⟩ x y
    exact A.cycles t c e x y
  · exact hTags
  · exact hSrc
  · exact hDst
  · exact hDis
  · exact fun j u => A.size_cells j.1 u
  · exact fun j u => (hErase j u).1
  · exact hFresh
  · exact fun j i => primaryHalfCell_subset (R j.1) _ _
  · exact fun j i => primaryHalfCell_subset (R j.1) _ _
  · exact fun j i => (mem_filter.mp (hPick j i)).2
  · exact A.superregular
  · exact hd
  · exact hd₁
  · exact hδ
  · exact hδ₁
  · exact hRoom

/-- The physical bridge construction with its original interface. -/
theorem exists_osthus_staden_bridged_primary_slices
    {V I : Type*} [Fintype V] [Fintype I]
    {H G : Digraph V} {f : V → Option I} {m₀ b r s p m mBase : ℕ}
    [NeZero (2*s)] [NeZero p] {β γ η a exc : ℝ}
    (B : OsthusStadenPrimaryReserveData H f
      (reducedMultiplicity (quotient H f) (fun i j => density H (cluster f i) (cluster f j)) β)
      m₀ b β γ η a exc)
    (E : Fin r → I → Digraph V) (g : Fin r → V → Option I) (σ : Fin r → Equiv.Perm I)
    (τ ε δ d εBase εH0 dH0 : ℝ)
    (R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
      (cluster (g t) i) (2*s) p m τ τ τ)
    (base : ∀ i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
      (cluster B.partition i) (2*s) p mBase εBase εBase εBase)
    (A : UnwoundPrimarySlices G (primaryThinDigraphs B) E g σ τ ε d R)
    (D : PrimaryRedSelection (p := p) A.coordinates) (C : Equiv.Perm I)
    (κ loss : ℕ)
    (hs : 3 ≤ s) (hHost : H ≤ G)
    (hCSpan : ∀ i k, C.SameCycle i k)
    (hC : ∀ i, (quotient H f).Adj i (C i))
    (hσ : ∀ t i, (quotient H f).Adj i (σ t i))
    (hDen : ∀ i k, (quotient H f).Adj i k →
      dH0+β ≤ density H (cluster f i) (cluster f k))
    (hβ : 0 < β) (hγ : 0 ≤ γ) (hη : 0 < η) (hη₁ : η ≤ 1)
    (hdH0 : 0 ≤ dH0) (hεH0 : 0 ≤ εH0)
    (hErr : 4*η ≤ γ*β) (hBad : η ≤ εH0*β)
    (hParent : ∀ t i, cluster (g t) i ⊆ cluster B.partition i)
    (hLoss : ∀ t i, (((cluster B.partition i) \ cluster (g t) i).card:ℝ) ≤ γ*dH0*(B.size:ℝ)/4)
    (hNear : ∀ t u, ((primaryPCells (R t) u) \ primaryPCells base u).card ≤ loss)
    (hCapacity : Fintype.card (RefinedFactorIndex r (2*s) p)+loss ≤ m)
    (hBadSize : 4*εH0*(B.size:ℝ) ≤ 2*(m:ℝ))
    (hτ : 0 ≤ τ) (hτ₁ : τ ≤ 1/8) (hFloor : 8*τ ≤ γ*dH0/4)
    (hκ : (κ:ℝ) < (1-8*τ)*(γ*dH0/4)*(m:ℝ))
    (hd : 0 ≤ d) (hd₁ : d ≤ 1) (hδ : 2*ε ≤ δ) (hδ₁ : δ ≤ 1)
    (hRoom : ε*((2*m:ℕ):ℝ)+1 ≤ δ*((2*m-1:ℕ):ℝ)) :
    let layer₀ := unwoundSlice E A.label A.factor
    let cells := fun (j : RefinedFactorIndex r (2*s) p) u => primaryPCells (R j.1) u
    ∃ src dst : RefinedFactorIndex r (2*s) p → I → RefinedVertex I (2*s) p,
    ∃ erase : RefinedFactorIndex r (2*s) p → RefinedVertex I (2*s) p → V,
      let halfIn := fun (j : RefinedFactorIndex r (2*s) p) i =>
        primaryHalfCell (R j.1) ((A.factor j).symm (src j i)) (redPhase p j.1.val).2
      let halfOut := fun (j : RefinedFactorIndex r (2*s) p) i =>
        primaryHalfCell (R j.1) (dst j i) (redPhase p j.1.val).2
      (∀ j i, (src j i).1.1 = i ∧ (dst j i).1.1 = C i) ∧
      (∀ j i, D.selectedPCell false j ((A.factor j).symm (src j i)) ∧
        D.selectedPCell true j (dst j i)) ∧
      (∀ j i k, src j i ≠ dst j k) ∧
      Function.Injective (fun q : RefinedFactorIndex r (2*s) p × RefinedVertex I (2*s) p =>
        erase q.1 q.2) ∧
      (∀ j u, erase j u ∈ cells j u ∧ erase j u ∈ primaryPCells base u) ∧
      Nonempty (TrimmedPhysicalBridgeLayers G layer₀ A.factor C cells erase src dst halfIn halfOut κ (2*m) δ d) := by
  obtain ⟨src,dst,erase,hTags,hRed,hSep,hFresh,hErase,P,_⟩ :=
    exists_osthus_staden_bridged_primary_slices_with_reserves B E g σ τ ε δ d εBase εH0 dH0
      R base A D C κ loss hs hHost hCSpan hC hσ hDen hβ hγ hη hη₁ hdH0 hεH0 hErr hBad
      hParent hLoss hNear hCapacity hBadSize hτ hτ₁ hFloor hκ hd hd₁ hδ hδ₁ hRoom
  exact ⟨src,dst,erase,hTags,hRed,hSep,hFresh,hErase,⟨P⟩⟩

end OverfullWork.DirectedRobustExpansion
