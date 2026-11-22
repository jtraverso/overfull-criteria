module

public import OverfullWork.OsthusStadenSharedBalancingReserve
public import OverfullWork.OsthusStadenBalancingHalfCells
public import OverfullWork.OsthusStadenPhysicalH2Pairs
public import OverfullWork.OsthusStadenBalancedPhysicalGraphs
public import OverfullWork.OsthusStadenShadowMatrixFromRedLayer

@[expose] public section


/-! Realize the shadow matrices with physical arcs of H2 in §5.9. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical

set_option maxHeartbeats 2750000 in
/-- All shadow matrices are realized together using the reserved
physical copies and the same adapted cells and bridge deletions as the
red layers. The output includes (B1) and the successor balance (41). -/
theorem exists_osthus_staden_balancing_on_physical_layers
    {V I : Type*} [Fintype V] [Fintype I]
    {r s p m mBase m₀ b : ℕ} [NeZero (2*s)] [NeZero p]
    {G H : Digraph V} {f : V → Option I} {M : I → I → ℕ} {β γ η a exc : ℝ}
    (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exc)
    {E : Fin r → I → Digraph V} {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I}
    {τ εBase ε δ d : ℝ}
    (base : ∀ i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
      (cluster B.partition i) (2*s) p mBase εBase εBase εBase)
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
      (cluster (g t) i) (2*s) p m τ τ τ}
    (A : UnwoundPrimarySlices G (primaryThinDigraphs B) E g σ τ ε d R)
    (D : PrimaryRedSelection (p := p) A.coordinates) (hp : 3 ≤ p)
    (Q : Digraph I) (hCopy : ∀ i k, Q.Adj i k → 0 < M i k) (hHost : H ≤ G)
    (erase : RefinedFactorIndex r (2*s) p → RefinedVertex I (2*s) p → V)
    (bound c cap loss halfLoss cutoff used : ℕ) (εH2 dH2 : ℝ)
    (hHalf : ∀ t u (q : Bool), (primaryHalfCell (R t) u q \ primaryHalfCell base u q).card ≤ halfLoss)
    (hLarge : (B.size:ℝ)*η ≤ ((2*mBase:ℕ):ℝ))
    (hScale : (B.size:ℝ)*η ≤ ((2*mBase:ℕ):ℝ)*εH2)
    (hTol : 2*η ≤ εH2) (hDensity : dH2 ≤ γ*β-2*η)
    (hCutoff : 0 < cutoff) (hCap : 0 < cap) (hDemand : bound ≤ cap*loss)
    (hKeep : cutoff+loss+halfLoss+1 ≤ m)
    (hFit : ((2*mBase:ℕ):ℝ)*εH2 ≤ (cutoff:ℝ))
    (hUsed : (Fintype.card (RefinedFactorIndex r (2*s) p)-1)*cap ≤ used)
    (hCoeff : 0 ≤ dH2-εH2) (hSlack : 0 ≤ (dH2-εH2)*(cutoff:ℝ)-(used:ℝ))
    (hNeed : (bound:ℝ) ≤ ((dH2-εH2)*(cutoff:ℝ)-(used:ℝ))*(cutoff:ℝ)) :
    letI : DecidableEq (RefinedVertex I (2*s) p) := Classical.decEq _
    let L := RefinedFactorIndex r (2*s) p
    let U := RefinedVertex I (2*s) p
    let cell := fun (j : L) (u : U) => (primaryPCells (R j.1) u).erase (erase j u)
    let ordinary := fun j => univ.biUnion (cell j)
    let eligible := fun (j : L) (u : U) =>
      balancingHalfCell base (R j.1) (erase j) u (redPhase p j.1.val).2
    let label := fun (j : L) => trimPCellLabel (A.label j.1) (erase j)
    let incoming := D.allPCells true
    let outgoing := D.allPCells false
    let send := fun (j : L) => shadowSend (A.factor j) (incoming j) (outgoing j)
    let receive := fun (j : L) => shadowReceive (A.factor j) (incoming j) (outgoing j)
    ∀ {F : L → Digraph V} {κ : ℕ} {redCap : ℝ}
      {center : L → I → V} {IStar OStar : L → I → Finset V},
      OsthusStadenRedLayerProperties G (primaryThinDigraphs B 4) (unwoundSlice E A.label A.factor)
        F A.factor ordinary cell D.vertices center IStar OStar κ redCap δ d →
      let sin := fun j u => cellExceptionalArcCount (F j) (ordinary j) (cell j u) false
      let sout := fun j u => cellExceptionalArcCount (F j) (ordinary j) (cell j u) true
      ∀ W : ∀ j, ↥(incoming j ∪ outgoing j) → ↥(incoming j ∪ outgoing j) → ℕ,
        (∀ j v w, W j v w ≤ if Q.Adj (send j v).1.1 (receive j w).1.1 then bound else 0) →
        (∀ j v, (∑ w,W j v w) = c+sin j v) →
        (∀ j w, (∑ v,W j v w) = c+sout j w) →
        ∃ P : L → Finset (V × V),
          (∀ j, digraphOfArcs (P j) ≤ primaryThinDigraphs B 4) ∧
          (∀ j k, j ≠ k → Disjoint (P j) (P k)) ∧
          (∀ j e, e ∈ P j → ∃ u v, e.1 ∈ eligible j u ∧ e.2 ∈ eligible j v ∧
            u ∈ Set.range (send j) ∧ v ∈ Set.range (receive j)) ∧
          (∀ j x, inDegree (digraphOfArcs (P j)) x ≤ Fintype.card U*cap ∧
            outDegree (digraphOfArcs (P j)) x ≤ Fintype.card U*cap) ∧
          (∀ j, Disjoint (Set.range (send j)) (Set.range (receive j))) ∧
          OsthusStadenBalancedLayerProperties G (fun j => F j ⊔ digraphOfArcs (P j))
            (fun j => trimLayerArcs (F j) (ordinary j))
            (fun j => physicalExceptionalArcs (F j) (ordinary j) ∪ P j)
            ordinary cell label A.factor κ (redCap+((Fintype.card U*cap:ℕ):ℝ)) δ d := by
  letI : DecidableEq (RefinedVertex I (2*s) p) := Classical.decEq _
  intro L U cell ordinary eligible label incoming outgoing send receive F κ redCap center IStar OStar hRed sin sout
    W hSupport hRow hCol
  let project (u : U) := u.1.1
  let Qp := fibrePullback Q project project
  let ABase := primaryPCells base
  have hBaseSize (u : U) : (ABase u).card = 2*mBase :=
    ((base u.1.1).second _).size _
  have hBaseCell (u : U) : ABase u ⊆ cluster B.partition (project u) := by
    exact (((base u.1.1).second _).subset _).trans ((base u.1.1).first.subset _)
  obtain ⟨baseLabel,hBaseLabel,_⟩ := exists_p_cell_labels B.partition base
  have hBaseDis (u v : U) (hne : u ≠ v) : Disjoint (ABase u) (ABase v) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hne (Option.some.inj (((hBaseLabel x u).mpr hx).symm.trans ((hBaseLabel x v).mpr hy)))
  obtain ⟨pair,hPair,hRegular⟩ := exists_primary_thin_pairs_on_base_cells B 4 Q project ABase εH2 dH2 hCopy
    hBaseCell (fun u => by rw [hBaseSize]; exact hLarge) (fun u => by rw [hBaseSize]; exact hScale) hTol hDensity
  have hDis (j : L) : Disjoint (incoming j) (outgoing j) := by
    apply disjoint_left.mpr
    intro u hu hv
    exact D.pCell_unique_direction j u ⟨(D.mem_allPCells_iff true j u).mp hu,(D.mem_allPCells_iff false j u).mp hv⟩
  have hSep (j : L) (u : U) (hu : u ∈ outgoing j) : A.factor j u ∉ incoming j := by
    intro hv
    have h := D.distance (by omega : 1 < p) ((D.mem_allPCells_iff false j _).mp hu) ((D.mem_allPCells_iff true j _).mp hv)
      (k := 1) (by decide) (by rw [pow_one])
    omega
  have hZero (q : Bool) (j : L) (u : U) (hu : u ∉ D.allPCells (!q) j) :
      cellExceptionalArcCount (F j) (ordinary j) (cell j u) q = 0 := by
    apply cell_exceptional_arc_count_of_no_red_endpoints (F j) (ordinary j) (cell j u) q
      (fun _ hx => mem_biUnion.mpr ⟨u,mem_univ _,hx⟩)
    apply disjoint_left.mpr
    intro x hx hred
    have hr := hRed.ordinaryRedEndpoints_subset j (!q) hred
    have hSelected := (D.mem_half_of_mem_vertices_and_pCell (!q) j u x hr (mem_erase.mp hx).2).1
    exact hu ((D.mem_allPCells_iff _ _ _).mpr hSelected)
  have hEligible (j : L) (u : U) : eligible j u ⊆ ABase u :=
    (balancingHalfCell_subsets base (R j.1) (erase j) u (redPhase p j.1.val).2).1
  have hLabel (j : L) (u : U) (x : V) (hx : x ∈ eligible j u) : label j x = some u :=
    (trimPCellLabel_eq_some (A.label j.1) (primaryPCells (R j.1)) (erase j) (A.label_cell j.1) x u).mpr
      ((balancingHalfCell_subsets base (R j.1) (erase j) u (redPhase p j.1.val).2).2 hx)
  have hSize (j : L) (u : U) : cutoff+loss ≤ (eligible j u).card := by
    have h := balancingHalfCell_size_lower base (R j.1) (erase j) u (redPhase p j.1.val).2 halfLoss
      (hHalf j.1 u _)
    change m ≤ (eligible j u).card+halfLoss+1 at h
    omega
  obtain ⟨P,hP,hPDis,hPEnd,hPCap,hBalance⟩ :=
    exists_balancing_arcs_from_shared_reserve_pairs A.factor incoming outgoing label sin sout Qp
    (primaryThinDigraphs B 4) pair ABase eligible W bound c cap loss cutoff used εH2 dH2
    hDis hSep (fun j u => hZero false j u) (fun j u => hZero true j u) hSupport hRow hCol
    hBaseDis hEligible hLabel hPair hRegular hCutoff hCap hDemand hSize
    (fun u => by rw [hBaseSize]; exact hFit) hUsed hCoeff hSlack hNeed
  have hRange (j : L) : Disjoint (Set.range (send j)) (Set.range (receive j)) := by
    have hSelected (u : ↥(incoming j ∪ outgoing j)) : ∃ q, D.selectedPCell q j u := by
      rcases mem_union.mp u.property with h | h
      · exact ⟨true,(D.mem_allPCells_iff true j _).mp h⟩
      · exact ⟨false,(D.mem_allPCells_iff false j _).mp h⟩
    apply shadow_ranges_disjoint (A.factor j) (incoming j) (outgoing j) p hp
    intro u v k hk h
    obtain ⟨q,hq⟩ := hSelected u
    obtain ⟨q',hq'⟩ := hSelected v
    exact D.distance (by omega : 1 < p) hq hq' hk h
  have hCellOrd (j : L) (u : U) : cell j u ⊆ ordinary j :=
    fun x hx => mem_biUnion.mpr ⟨u,mem_univ _,hx⟩
  have hOrd (j : L) (u : U) : eligible j u ⊆ ordinary j :=
    ((balancingHalfCell_subsets base (R j.1) (erase j) u (redPhase p j.1.val).2).2).trans (hCellOrd j u)
  refine ⟨P,hP,hPDis,hPEnd,hPCap,hRange,?_⟩
  exact balanced_physical_graphs_from_red_layers hRed label P (Fintype.card U*cap)
    (fun j u x => trimPCellLabel_eq_some (A.label j.1) (primaryPCells (R j.1)) (erase j) (A.label_cell j.1) x u)
    hCellOrd ((primaryThinDigraphs_le B _).trans hHost) hP hPDis
    (fun j e he => by
      obtain ⟨u,v,hu,hv,_,_⟩ := hPEnd j e he
      exact ⟨hOrd j u hu,hOrd j v hv⟩)
    hPCap hBalance

set_option maxHeartbeats 2200000 in
/-- On the same robust reduced support, find the shadow matrices and
realize them together in H2. The degree and capacity margins remain explicit. -/
theorem exists_osthus_staden_balanced_layers_from_robust_support
    {V I : Type*} [Fintype V] [Fintype I]
    {r s p m mBase m₀ b : ℕ} [NeZero (2*s)] [NeZero p]
    {G H : Digraph V} {f : V → Option I} {M : I → I → ℕ} {β γ η a exc : ℝ}
    (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exc)
    {E : Fin r → I → Digraph V} {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I}
    {τ εBase ε δ d : ℝ}
    (base : ∀ i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
      (cluster B.partition i) (2*s) p mBase εBase εBase εBase)
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
      (cluster (g t) i) (2*s) p m τ τ τ}
    (A : UnwoundPrimarySlices G (primaryThinDigraphs B) E g σ τ ε d R)
    (D : PrimaryRedSelection (p := p) A.coordinates) (hp : 3 ≤ p) (hs : 2 ≤ s)
    (Q : Digraph I) (hCopy : ∀ i k, Q.Adj i k → 0 < M i k) (hHost : H ≤ G)
    (ν t₀ α err : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ t₀) (hτ : t₀ ≤ 1/4) (hOrder : 2 ≤ t₀*(Fintype.card I:ℝ))
    (hRobust : IsRealRobust Q ν t₀)
    (hIn : ∀ i, α*(Fintype.card I:ℝ) ≤ (inDegree Q i:ℝ))
    (hOut : ∀ i, α*(Fintype.card I:ℝ) ≤ (outDegree Q i:ℝ))
    (hAlpha : 8*t₀ ≤ α) (hErr : 0 ≤ err) (hErrSmall : 16*err ≤ ν^2/2)
    (erase : RefinedFactorIndex r (2*s) p → RefinedVertex I (2*s) p → V)
    (hErase : ∀ j u, erase j u ∈ primaryPCells (R j.1) u)
    (bound c cap loss halfLoss cutoff used : ℕ) (εH2 dH2 : ℝ)
    (hHalf : ∀ t u (q : Bool), (primaryHalfCell (R t) u q \ primaryHalfCell base u q).card ≤ halfLoss)
    (hLarge : (B.size:ℝ)*η ≤ ((2*mBase:ℕ):ℝ))
    (hScale : (B.size:ℝ)*η ≤ ((2*mBase:ℕ):ℝ)*εH2)
    (hTol : 2*η ≤ εH2) (hDensity : dH2 ≤ γ*β-2*η)
    (hCutoff : 0 < cutoff) (hCap : 0 < cap) (hDemand : bound ≤ cap*loss)
    (hKeep : cutoff+loss+halfLoss+1 ≤ m)
    (hFit : ((2*mBase:ℕ):ℝ)*εH2 ≤ (cutoff:ℝ))
    (hUsed : (Fintype.card (RefinedFactorIndex r (2*s) p)-1)*cap ≤ used)
    (hCoeff : 0 ≤ dH2-εH2) (hSlack : 0 ≤ (dH2-εH2)*(cutoff:ℝ)-(used:ℝ))
    (hNeed : (bound:ℝ) ≤ ((dH2-εH2)*(cutoff:ℝ)-(used:ℝ))*(cutoff:ℝ)) :
    letI : DecidableEq (RefinedVertex I (2*s) p) := Classical.decEq _
    let L := RefinedFactorIndex r (2*s) p
    let U := RefinedVertex I (2*s) p
    let cell := fun (j : L) (u : U) => (primaryPCells (R j.1) u).erase (erase j u)
    let ordinary := fun j => univ.biUnion (cell j)
    let eligible := fun (j : L) (u : U) =>
      balancingHalfCell base (R j.1) (erase j) u (redPhase p j.1.val).2
    let label := fun (j : L) => trimPCellLabel (A.label j.1) (erase j)
    let incoming := D.allPCells true
    let outgoing := D.allPCells false
    let send := fun (j : L) => shadowSend (A.factor j) (incoming j) (outgoing j)
    let receive := fun (j : L) => shadowReceive (A.factor j) (incoming j) (outgoing j)
    ∀ {F : L → Digraph V} {κ : ℕ} {redCap : ℝ}
      {center : L → I → V} {IStar OStar : L → I → Finset V},
      OsthusStadenRedLayerProperties G (primaryThinDigraphs B 4) (unwoundSlice E A.label A.factor)
        F A.factor ordinary cell D.vertices center IStar OStar κ redCap δ d →
      ((2*m-1:ℕ):ℝ)*redCap ≤ err*(c:ℝ) →
      (∀ j, 8 ≤ α*(Fintype.card ↥(incoming j ∪ outgoing j):ℝ)) →
      (∀ j, 3*((c:ℝ)/(Fintype.card ↥(incoming j ∪ outgoing j):ℝ)) ≤ (bound:ℝ)*(ν^2/2)^2) →
        ∃ P : L → Finset (V × V),
          (∀ j, digraphOfArcs (P j) ≤ primaryThinDigraphs B 4) ∧
          (∀ j k, j ≠ k → Disjoint (P j) (P k)) ∧
          (∀ j e, e ∈ P j → ∃ u v, e.1 ∈ eligible j u ∧ e.2 ∈ eligible j v ∧
            u ∈ Set.range (send j) ∧ v ∈ Set.range (receive j)) ∧
          (∀ j x, inDegree (digraphOfArcs (P j)) x ≤ Fintype.card U*cap ∧
            outDegree (digraphOfArcs (P j)) x ≤ Fintype.card U*cap) ∧
          (∀ j, Disjoint (Set.range (send j)) (Set.range (receive j))) ∧
          OsthusStadenBalancedLayerProperties G (fun j => F j ⊔ digraphOfArcs (P j))
            (fun j => trimLayerArcs (F j) (ordinary j))
            (fun j => physicalExceptionalArcs (F j) (ordinary j) ∪ P j)
            ordinary cell label A.factor κ (redCap+((Fintype.card U*cap:ℕ):ℝ)) δ d := by
  letI : DecidableEq (RefinedVertex I (2*s) p) := Classical.decEq _
  intro L U cell ordinary eligible label incoming outgoing send receive F κ redCap center IStar OStar hRed
    hDemandRate hShadowOrder hShadowCap
  choose W hSupport hRow hCol using fun j =>
    exists_shadow_balancing_matrix_from_physical_red_layer D (by omega : 1 < p) hs j Q (F j)
      (erase j) (hErase j) κ bound c ν t₀ α err redCap hν hντ hτ hOrder hRobust hIn hOut
      hAlpha hErr hErrSmall hDemandRate (hRed.exceptional_independent j) (hRed.exceptional_degrees j)
      (hRed.ordinaryRedEndpoints_subset j) (hRed.exceptional_neighbours j) (hShadowOrder j) (hShadowCap j)
  exact exists_osthus_staden_balancing_on_physical_layers B base A D hp Q hCopy hHost erase
    bound c cap loss halfLoss cutoff used εH2 dH2 hHalf hLarge hScale hTol hDensity hCutoff hCap hDemand
    hKeep hFit hUsed hCoeff hSlack hNeed hRed W hSupport hRow hCol

end OverfullWork.DirectedRobustExpansion
