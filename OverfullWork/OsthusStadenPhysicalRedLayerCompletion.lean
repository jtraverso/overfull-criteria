module

public import OverfullWork.OsthusStadenSpecialExceptionLayerUnion
public import OverfullWork.OsthusStadenBridgesFromPrimarySlices

@[expose] public section


/-! Assemble the exact core, bridge, and special arcs in §5.7. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical

/-- The physical exceptional vertices chosen as bridge centres. -/
noncomputable def bridgeCenters {V U I L : Type*} [Fintype I]
    (erase : L → U → V) (src : L → I → U) (j : L) : Finset V :=
  univ.image (erase j ∘ src j)

section RedVertices

variable {V I : Type*} [Fintype V] [Fintype I] {r s p m : ℕ} [NeZero (2*s)] [NeZero p]
variable {G : Digraph V} {thin : Fin 5 → Digraph V} {E : Fin r → I → Digraph V}
variable {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I} {τ ε d : ℝ}
variable {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G thin E))
  (cluster (g t) i) (2*s) p m τ τ τ}
variable {A : UnwoundPrimarySlices G thin E g σ τ ε d R}

/-- A vertex in the selected physical half is red in that direction. -/
theorem PrimaryRedSelection.mem_vertices_of_mem_selected_half
    (D : PrimaryRedSelection (p := p) A.coordinates) (q : Bool)
    (j : RefinedFactorIndex r (2*s) p) (u : RefinedVertex I (2*s) p) (x : V)
    (hu : D.selectedPCell q j u)
    (hx : x ∈ primaryHalfCell (R j.1) u (redPhase p j.1.val).2) :
    x ∈ D.vertices q j := by
  obtain ⟨i,z,hz,rfl⟩ := hu
  exact mem_biUnion.mpr ⟨i,mem_univ _,mem_biUnion.mpr ⟨_,mem_map.mpr ⟨z,hz,rfl⟩,hx⟩⟩

end RedVertices

/-- All endpoints of the physical thin reserves belong to the retained
base primary cells. In particular, the core arcs cannot use these reserves. -/
theorem primaryThinDigraphs_avoids_core {V I : Type*} [Fintype V] [Fintype I]
    {H : Digraph V} {f : V → Option I} {M : I → I → ℕ} {m₀ b : ℕ} {β γ η a exc : ℝ}
    (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exc)
    (q : Fin 5) {x y : V} (h : (primaryThinDigraphs B q).Adj x y) :
    x ∉ exceptional B.partition ∧ y ∉ exceptional B.partition := by
  obtain ⟨e,z,w,hx,hy,_⟩ := h
  have hEnds (i : I) (u : Fin B.size) : ((B.kept i).trans (B.base i)) u ∉ exceptional B.partition := by
    have hu : ((B.kept i).trans (B.base i)) u ∈ cluster B.partition i := by
      rw [←B.retained_cells i]
      exact mem_map.mpr ⟨u,mem_univ _,rfl⟩
    intro h'
    exact Option.some_ne_none i (((mem_cluster _ _ _).mp hu).symm.trans ((mem_exceptional _ _).mp h'))
  exact ⟨hx ▸ hEnds e.1.1 z,hy ▸ hEnds e.1.2 w⟩

/-- The properties of the red layers used to start the shadow
balancing step. The original successor arcs and bridge endpoints are retained. -/
structure OsthusStadenRedLayerProperties {L U I V : Type*} [Fintype V]
    (G reserve : Digraph V) (initial F : L → Digraph V) (factor : L → Equiv.Perm U)
    (ordinary : L → Finset V) (cell : L → U → Finset V) (red : Bool → L → Finset V)
    (center : L → I → V) (incoming outgoing : L → I → Finset V)
    (κ : ℕ) (cap δ d : ℝ) : Prop where
  le : ∀ j, F j ≤ G
  disjoint_layers : ∀ j k, j ≠ k → Disjoint (F j) (F k)
  disjoint_reserve : ∀ j, Disjoint (F j) reserve
  exceptional_degrees : ∀ j x, x ∉ ordinary j → inDegree (F j) x = κ ∧ outDegree (F j) x = κ
  exceptional_independent : ∀ j x y, x ∉ ordinary j → y ∉ ordinary j → ¬ (F j).Adj x y
  arc_support : ∀ j x y, (F j).Adj x y →
    (x ∈ ordinary j ∧ y ∈ ordinary j) ∨
    (x ∉ ordinary j ∧ y ∈ ordinary j ∧ y ∈ red true j) ∨
    (y ∉ ordinary j ∧ x ∈ ordinary j ∧ x ∈ red false j)
  exceptional_neighbours : ∀ j x, x ∈ ordinary j → ∀ q : Bool,
    profileCount ((ordinary j)ᶜ) (if q then outProfile (F j) x else inProfile (F j) x) ≤ cap
  ordinary_adjacency : ∀ j x, x ∈ ordinary j → ∀ y, y ∈ ordinary j →
    ((F j).Adj x y ↔ (initial j).Adj x y)
  superregular : ∀ j u, IsSuperregularPair (F j) δ d (cell j u) (cell j (factor j u))
  bridge_adjacency : ∀ j i x, ((F j).Adj x (center j i) ↔ x ∈ incoming j i) ∧
    ((F j).Adj (center j i) x ↔ x ∈ outgoing j i)

set_option maxHeartbeats 3000000 in
/-- Assemble the three exceptional families using their original physical
arcs. The ordinary pairs stay superregular, the bridge incidences stay
exact, and the H2 reserve is still disjoint from every layer. -/
theorem complete_osthus_staden_red_layers
    {V I : Type*} [Fintype V] [Fintype I] {r s p m m₀ b : ℕ} [NeZero (2*s)] [NeZero p]
    {G H : Digraph V} {f : V → Option I} {M : I → I → ℕ} {β γ η a exc : ℝ}
    (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exc)
    {E : Fin r → I → Digraph V} {g : Fin r → V → Option I} {σ : Fin r → Equiv.Perm I}
    {τ ε δ d : ℝ}
    {R : ∀ t i, PrimaryNestedRefinement (arcProfiles (primarySliceGraphs G (primaryThinDigraphs B) E))
      (cluster (g t) i) (2*s) p m τ τ τ}
    (A : UnwoundPrimarySlices G (primaryThinDigraphs B) E g σ τ ε d R)
    (D : PrimaryRedSelection (p := p) A.coordinates) (C : Equiv.Perm I)
    (erase : RefinedFactorIndex r (2*s) p → RefinedVertex I (2*s) p → V)
    (src dst : RefinedFactorIndex r (2*s) p → I → RefinedVertex I (2*s) p)
    (κ : ℕ) (capCore capSpecial : ℝ)
    (hHost : H ≤ G) (hParent : ∀ t i, cluster (g t) i ⊆ cluster B.partition i)
    (hErase : ∀ j u, erase j u ∈ primaryPCells (R j.1) u)
    (hRedBridge : ∀ j i, D.selectedPCell false j ((A.factor j).symm (src j i)) ∧
      D.selectedPCell true j (dst j i))
    (core special : RefinedFactorIndex r (2*s) p → Digraph V) :
    let cell := fun (j : RefinedFactorIndex r (2*s) p) => primaryPCells (R j.1)
    let trim := fun j u => (cell j u).erase (erase j u)
    let ordinary := fun j => univ.biUnion (trim j)
    let Z := exceptional B.partition
    let bridge := bridgeCenters erase src
    let S := specialExceptions Z cell erase bridge
    let halfIn := fun (j : RefinedFactorIndex r (2*s) p) i =>
      primaryHalfCell (R j.1) ((A.factor j).symm (src j i)) (redPhase p j.1.val).2
    let halfOut := fun (j : RefinedFactorIndex r (2*s) p) i =>
      primaryHalfCell (R j.1) (dst j i) (redPhase p j.1.val).2
    ∀ (P : TrimmedPhysicalBridgeLayers G (unwoundSlice E A.label A.factor) A.factor C
        cell erase src dst halfIn halfOut κ (2*m) δ d),
      P.UsesBridgeReserves (primaryThinDigraphs B 1) (primaryThinDigraphs B 0) →
      (∀ j, core j ≤ G) →
      (∀ j, special j ≤ primaryThinDigraphs B 2 ⊔ primaryThinDigraphs B 3) →
      (∀ j k, j ≠ k → Disjoint (core j) (core k)) →
      (∀ j k, j ≠ k → Disjoint (special j) (special k)) →
      (∀ j x y, (core j).Adj x y →
        (x ∈ Z ∧ y ∈ ordinary j ∧ y ∈ D.vertices true j) ∨
        (y ∈ Z ∧ x ∈ ordinary j ∧ x ∈ D.vertices false j)) →
      (∀ j x y, (special j).Adj x y →
        (x ∈ S j ∧ y ∈ ordinary j ∧ y ∈ D.vertices true j) ∨
        (y ∈ S j ∧ x ∈ ordinary j ∧ x ∈ D.vertices false j)) →
      (∀ j x, x ∈ Z → inDegree (core j) x = κ ∧ outDegree (core j) x = κ) →
      (∀ j x, x ∈ S j → inDegree (special j) x = κ ∧ outDegree (special j) x = κ) →
      (∀ j x, x ∉ Z → (inDegree (core j) x:ℝ) ≤ capCore ∧ (outDegree (core j) x:ℝ) ≤ capCore) →
      (∀ j x, x ∉ S j → (inDegree (special j) x:ℝ) ≤ capSpecial ∧ (outDegree (special j) x:ℝ) ≤ capSpecial) →
      let F := fun j => (P.graph j ⊔ core j) ⊔ special j
      OsthusStadenRedLayerProperties G (primaryThinDigraphs B 4) (unwoundSlice E A.label A.factor)
        F A.factor ordinary trim D.vertices (fun j i => erase j (src j i))
        P.incoming P.outgoing κ (1+capCore+capSpecial) δ d := by
  intro cell trim ordinary Z bridge S halfIn halfOut P hRes hCoreG hSpecRes hCoreDis hSpecDis
    hCoreArc hSpecArc hCore hSpecExact hCoreCap hSpecCap F
  let L := RefinedFactorIndex r (2*s) p
  have hTrim (j : L) (u : RefinedVertex I (2*s) p) : trim j u ⊆ ordinary j :=
    fun x hx => mem_biUnion.mpr ⟨u,mem_univ _,hx⟩
  have hBase (j : L) (u : RefinedVertex I (2*s) p) {x : V} (hx : x ∈ cell j u) : x ∉ Z := by
    have hc := hParent j.1 u.1.1 ((((R j.1 u.1.1).second _).subset _).trans
      ((R j.1 u.1.1).first.subset _) hx)
    intro h
    exact Option.some_ne_none _ (((mem_cluster _ _ _).mp hc).symm.trans ((mem_exceptional _ _).mp h))
  have hOrdCore (j : L) : Disjoint Z (ordinary j) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨u,_,hu⟩ := mem_biUnion.mp hy
    exact hBase j u (mem_erase.mp hu).2 hx
  have hBridgeOut (j : L) : Disjoint (bridge j) (ordinary j) := by
    apply disjoint_left.mpr
    rintro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact P.bridge_exceptional j i
  have hBridgeCore (j : L) : Disjoint (bridge j) Z := by
    apply disjoint_left.mpr
    rintro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact hBase j (src j i) (hErase j (src j i))
  have hSOrd (j : L) : Disjoint (S j) (ordinary j) :=
    disjoint_left.mpr (fun _ hx => mem_compl.mp (mem_sdiff.mp hx).1)
  have hSZ (j : L) : Disjoint (S j) Z :=
    disjoint_left.mpr (fun _ hx hy => (mem_sdiff.mp hx).2 (mem_union_left _ hy))
  have hSBridge (j : L) : Disjoint (S j) (bridge j) :=
    disjoint_left.mpr (fun _ hx hy => (mem_sdiff.mp hx).2 (mem_union_right _ hy))
  have hBridgeArc (j : L) (x y : V) (h : (P.graph j).Adj x y) :
      (x ∈ ordinary j ∧ y ∈ ordinary j) ∨
      (x ∈ bridge j ∧ y ∈ ordinary j ∧ y ∈ D.vertices true j) ∨
      (y ∈ bridge j ∧ x ∈ ordinary j ∧ x ∈ D.vertices false j) := by
    rcases h with ⟨_,hx,hy⟩ | ⟨i,_,⟨hx,rfl⟩ | ⟨rfl,hy⟩⟩
    · exact Or.inl ⟨hx,hy⟩
    · obtain ⟨hne,hh⟩ := mem_erase.mp ((P.star_support j i).1 hx)
      exact Or.inr (Or.inr ⟨mem_image.mpr ⟨i,mem_univ _,rfl⟩,
        hTrim j _ (mem_erase.mpr ⟨hne,primaryHalfCell_subset _ _ _ hh⟩),
        D.mem_vertices_of_mem_selected_half false j _ x (hRedBridge j i).1 hh⟩)
    · obtain ⟨hne,hh⟩ := mem_erase.mp ((P.star_support j i).2 hy)
      exact Or.inr (Or.inl ⟨mem_image.mpr ⟨i,mem_univ _,rfl⟩,
        hTrim j _ (mem_erase.mpr ⟨hne,primaryHalfCell_subset _ _ _ hh⟩),
        D.mem_vertices_of_mem_selected_half true j _ y (hRedBridge j i).2 hh⟩)
  have hBridgeAvoid (j : L) (x y : V) (h : (P.graph j).Adj x y) : x ∉ Z ∧ y ∉ Z := by
    rcases hBridgeArc j x y h with h | h | h
    · exact ⟨disjoint_left.mp (hOrdCore j).symm h.1,disjoint_left.mp (hOrdCore j).symm h.2⟩
    · exact ⟨disjoint_left.mp (hBridgeCore j) h.1,disjoint_left.mp (hOrdCore j).symm h.2.1⟩
    · exact ⟨disjoint_left.mp (hOrdCore j).symm h.2.1,disjoint_left.mp (hBridgeCore j) h.1⟩
  have hOld := adjoin_exact_core_exception_arcs G Z ordinary P.graph core κ P.layer_le hCoreG
    P.layer_disjoint hCoreDis hOrdCore hBridgeAvoid
    (fun j x y h => (hCoreArc j x y h).imp (fun h => ⟨h.1,h.2.1⟩) (fun h => ⟨h.1,h.2.1⟩))
    P.exceptional_independent hCore
  obtain ⟨hOldG,hOldDis,hOldCore,hOldBridge,hOldOrd,hOldInd⟩ := hOld
  let old (j : L) := P.graph j ⊔ core j
  have hOldAvoid (j : L) (x y : V) (h : (old j).Adj x y) : x ∉ S j ∧ y ∉ S j := by
    rcases h with h | h
    · rcases hBridgeArc j x y h with h | h | h
      · exact ⟨disjoint_left.mp (hSOrd j).symm h.1,disjoint_left.mp (hSOrd j).symm h.2⟩
      · exact ⟨disjoint_left.mp (hSBridge j).symm h.1,disjoint_left.mp (hSOrd j).symm h.2.1⟩
      · exact ⟨disjoint_left.mp (hSOrd j).symm h.2.1,disjoint_left.mp (hSBridge j).symm h.1⟩
    · rcases hCoreArc j x y h with h | h
      · exact ⟨disjoint_left.mp (hSZ j).symm h.1,disjoint_left.mp (hSOrd j).symm h.2.1⟩
      · exact ⟨disjoint_left.mp (hSOrd j).symm h.2.1,disjoint_left.mp (hSZ j).symm h.1⟩
  have hOldExact (j : L) (x : V) (hx : x ∉ ordinary j) (hs : x ∉ S j) :
      inDegree (old j) x = κ ∧ outDegree (old j) x = κ := by
    by_cases hz : x ∈ Z
    · exact hOldCore j x hz
    · have hB : x ∈ bridge j := Classical.byContradiction fun h =>
        hs (mem_sdiff.mpr ⟨mem_compl.mpr hx,fun h' => (mem_union.mp h').elim hz h⟩)
      obtain ⟨i,_,rfl⟩ := mem_image.mp hB
      exact ⟨(hOldBridge j _ hz hx).1.trans (P.bridge_degrees j i).1,
        (hOldBridge j _ hz hx).2.trans (P.bridge_degrees j i).2⟩
  have hOldThin (q : Fin 5) (h1 : (1 : Fin 5) ≠ q) (h0 : (0 : Fin 5) ≠ q) (j : L) :
      Disjoint (old j) (primaryThinDigraphs B q) := by
    rw [disjoint_iff_inf_le]
    rintro x y ⟨hb | hc,hq⟩
    · rcases P.graph_le_reserves _ _ hRes j hb with hMain | hIn | hOut
      · exact disjoint_iff_inf_le.mp (A.slice_thin_disjoint j q) ⟨hMain,hq⟩
      · exact disjoint_iff_inf_le.mp (B.thin_disjoint 1 q h1) ⟨hIn,hq⟩
      · exact disjoint_iff_inf_le.mp (B.thin_disjoint 0 q h0) ⟨hOut,hq⟩
    · have hz := primaryThinDigraphs_avoids_core B q hq
      exact (hCoreArc j x y hc).elim (fun h => hz.1 h.1) (fun h => hz.2 h.1)
  have hMixed (j k : L) : Disjoint (old j) (special k) := by
    rw [disjoint_iff_inf_le]
    rintro x y ⟨h,h'⟩
    rcases hSpecRes k h' with h2 | h3
    · exact disjoint_iff_inf_le.mp (hOldThin 2 (by decide) (by decide) j) ⟨h,h2⟩
    · exact disjoint_iff_inf_le.mp (hOldThin 3 (by decide) (by decide) j) ⟨h,h3⟩
  have hSpecG (j : L) : special j ≤ G :=
    (hSpecRes j).trans ((sup_le (primaryThinDigraphs_le B 2) (primaryThinDigraphs_le B 3)).trans hHost)
  obtain ⟨hFG,hFDis,hFExact,hFOrd,hFInd⟩ :=
    adjoin_exact_special_exception_arcs G S ordinary old special κ hOldG hSpecG hOldDis hSpecDis
      hMixed hSOrd hOldAvoid
      (fun j x y h => (hSpecArc j x y h).imp (fun h => ⟨h.1,h.2.1⟩) (fun h => ⟨h.1,h.2.1⟩))
      hOldInd hOldExact hSpecExact
  refine ⟨hFG,hFDis,?_,hFExact,hFInd,?_,?_,?_,?_,?_⟩
  · intro j
    rw [disjoint_iff_inf_le]
    rintro x y ⟨h | h,hq⟩
    · exact disjoint_iff_inf_le.mp (hOldThin 4 (by decide) (by decide) j) ⟨h,hq⟩
    · rcases hSpecRes j h with h2 | h3
      · exact disjoint_iff_inf_le.mp (B.thin_disjoint 2 4 (by decide)) ⟨h2,hq⟩
      · exact disjoint_iff_inf_le.mp (B.thin_disjoint 3 4 (by decide)) ⟨h3,hq⟩
  · intro j x y h
    rcases h with (hb | hc) | hs
    · rcases hBridgeArc j x y hb with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨disjoint_left.mp (hBridgeOut j) h.1,h.2⟩)
      · exact Or.inr (Or.inr ⟨disjoint_left.mp (hBridgeOut j) h.1,h.2⟩)
    · exact (hCoreArc j x y hc).elim
        (fun h => Or.inr (Or.inl ⟨disjoint_left.mp (hOrdCore j) h.1,h.2⟩))
        (fun h => Or.inr (Or.inr ⟨disjoint_left.mp (hOrdCore j) h.1,h.2⟩))
    · exact (hSpecArc j x y hs).elim
        (fun h => Or.inr (Or.inl ⟨disjoint_left.mp (hSOrd j) h.1,h.2⟩))
        (fun h => Or.inr (Or.inr ⟨disjoint_left.mp (hSOrd j) h.1,h.2⟩))
  · intro j x hx q
    let Q := fun T => if q then outProfile T x else inProfile T x
    let X := (ordinary j)ᶜ
    have hOne : profileCount X (Q (P.graph j)) ≤ 1 := by
      have hCard : (X ∩ Q (P.graph j)).card ≤ 1 := by
        apply card_le_one.mpr
        intro y hy z hz
        obtain ⟨hyo,hy⟩ := mem_inter.mp hy
        obtain ⟨hzo,hz⟩ := mem_inter.mp hz
        have h := P.unique_exceptional_neighbour j x y z hx (mem_compl.mp hyo) (mem_compl.mp hzo)
        cases q
        · exact h.2 (mem_filter.mp hy).2 (mem_filter.mp hz).2
        · exact h.1 (mem_filter.mp hy).2 (mem_filter.mp hz).2
      unfold profileCount
      exact_mod_cast hCard
    have hBound (T : Digraph V) (cap : ℝ)
        (h : (inDegree T x:ℝ) ≤ cap ∧ (outDegree T x:ℝ) ≤ cap) : profileCount X (Q T) ≤ cap := by
      have hCard : profileCount X (Q T) ≤ ((Q T).card:ℝ) := by
        unfold profileCount
        exact_mod_cast card_le_card (inter_subset_right : X ∩ Q T ⊆ Q T)
      exact hCard.trans (by cases q <;> first | exact h.1 | exact h.2)
    have h1 := exceptional_profile_sup_le (old j) (special j) q X x
    have h2 := exceptional_profile_sup_le (P.graph j) (core j) q X x
    have ha := hBound (core j) capCore (hCoreCap j x (disjoint_left.mp (hOrdCore j).symm hx))
    have hb := hBound (special j) capSpecial (hSpecCap j x (disjoint_left.mp (hSOrd j).symm hx))
    exact h1.trans (add_le_add (h2.trans (add_le_add hOne ha)) hb)
  · intro j x hx y hy
    refine (hFOrd j x hx y hy).trans ((hOldOrd j x hx y hy).trans ?_)
    constructor
    · intro h
      rcases h with ⟨h,_,_⟩ | ⟨i,_,h | h⟩
      · exact h
      · have hv := P.bridge_exceptional j i
        have he : y = erase j (src j i) := h.2
        exact (hv (he ▸ hy)).elim
      · have hv := P.bridge_exceptional j i
        have he : x = erase j (src j i) := h.1
        exact (hv (he ▸ hx)).elim
    · intro h
      exact Or.inl ⟨h,hx,hy⟩
  · intro j u
    apply (P.superregular j u).congr_on
    intro x hx y hy
    exact ((hFOrd j x (hTrim _ _ hx) y (hTrim _ _ hy)).trans
      (hOldOrd j x (hTrim _ _ hx) y (hTrim _ _ hy))).symm
  · intro j i x
    let v := erase j (src j i)
    have hv : v ∈ bridge j := mem_image.mpr ⟨i,mem_univ _,rfl⟩
    have hvo := disjoint_left.mp (hBridgeOut j) hv
    have hvZ := disjoint_left.mp (hBridgeCore j) hv
    have hvS := disjoint_left.mp (hSBridge j).symm hv
    obtain ⟨hin,hout⟩ := P.bridge_adjacency j i x
    constructor
    · refine ⟨?_,fun h => Or.inl (Or.inl (hin.mpr h))⟩
      rintro ((hb | hc) | hs)
      · exact hin.mp hb
      · exact (hCoreArc j x v hc).elim (fun h => (hvo h.2.1).elim) (fun h => (hvZ h.1).elim)
      · exact (hSpecArc j x v hs).elim (fun h => (hvo h.2.1).elim) (fun h => (hvS h.1).elim)
    · refine ⟨?_,fun h => Or.inl (Or.inl (hout.mpr h))⟩
      rintro ((hb | hc) | hs)
      · exact hout.mp hb
      · exact (hCoreArc j v x hc).elim (fun h => (hvZ h.1).elim) (fun h => (hvo h.2.1).elim)
      · exact (hSpecArc j v x hs).elim (fun h => (hvS h.1).elim) (fun h => (hvo h.2.1).elim)

end OverfullWork.DirectedRobustExpansion
