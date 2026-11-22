module

public import OverfullWork.OsthusStadenSuperregularAfterBridgeTrim
public import OverfullWork.OsthusStadenGlobalBridgeTrimming
public import OverfullWork.OsthusStadenBridgeArcs

@[expose] public section


/-! Install the two bridge stars on each trimmed physical layer. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical

/-- Keep exactly the old arcs whose endpoints are both retained. -/
def trimLayerArcs {V : Type*} (D : Digraph V) (ordinary : Finset V) : Digraph V :=
  ⟨fun x y => D.Adj x y ∧ x ∈ ordinary ∧ y ∈ ordinary⟩

/-- The bridge stars are the only new arcs of the trimmed layer. -/
noncomputable def addTrimmedBridgeStars {V U I : Type*} [Fintype U] [Fintype I]
    (D : Digraph V) (cell : U → Finset V) (erase : U → V)
    (center : I → V) (incoming outgoing : I → Finset V) : Digraph V :=
  trimLayerArcs D (univ.biUnion (fun u => (cell u).erase (erase u))) ⊔
    indexedArcUnion univ (fun i => bridgeArcs (center i) (incoming i) (outgoing i))

/-- The bridge stars, the ordinary remnant, and the cycle routing on
the same original vertices. -/
structure TrimmedPhysicalBridgeLayers
    {L U I V : Type*} [Fintype U] [Fintype I] [Fintype V]
    (G : Digraph V) (initial : L → Digraph V) (F : L → Equiv.Perm U) (C : Equiv.Perm I)
    (cell : L → U → Finset V) (erase : L → U → V)
    (src dst : L → I → U) (halfIn halfOut : L → I → Finset V)
    (κ n : ℕ) (δ d : ℝ) where
  incoming : L → I → Finset V
  outgoing : L → I → Finset V
  star_support : ∀ j i, incoming j i ⊆ (halfIn j i).erase (erase j ((F j).symm (src j i))) ∧
    outgoing j i ⊆ (halfOut j i).erase (erase j (dst j i))
  star_size : ∀ j i, (incoming j i).card = κ ∧ (outgoing j i).card = κ
  bridge_adjacency : ∀ j i x,
    let H := addTrimmedBridgeStars (initial j) (cell j) (erase j)
      (erase j ∘ src j) (incoming j) (outgoing j)
    (H.Adj x (erase j (src j i)) ↔ x ∈ incoming j i) ∧
      (H.Adj (erase j (src j i)) x ↔ x ∈ outgoing j i)
  bridge_degrees : ∀ j i,
    let H := addTrimmedBridgeStars (initial j) (cell j) (erase j)
      (erase j ∘ src j) (incoming j) (outgoing j)
    inDegree H (erase j (src j i)) = κ ∧ outDegree H (erase j (src j i)) = κ
  primary_spanning : ∀ i k, C.SameCycle i k
  bridge_exceptional : ∀ j i,
    erase j (src j i) ∉ univ.biUnion (fun u => (cell j u).erase (erase j u))
  cover_cycles : ∀ j u, ∃ i, (F j).SameCycle u (src j i)
  route_cycles : ∀ j i, (F j).SameCycle ((F j).symm (src j i)) (src j i) ∧
    (F j).SameCycle (dst j i) (src j (C i))
  exceptional_independent : ∀ j x y,
    let ordinary := univ.biUnion (fun u => (cell j u).erase (erase j u))
    let H := addTrimmedBridgeStars (initial j) (cell j) (erase j)
      (erase j ∘ src j) (incoming j) (outgoing j)
    x ∉ ordinary → y ∉ ordinary → ¬H.Adj x y
  unique_exceptional_neighbour : ∀ j x y z,
    let ordinary := univ.biUnion (fun u => (cell j u).erase (erase j u))
    let H := addTrimmedBridgeStars (initial j) (cell j) (erase j)
      (erase j ∘ src j) (incoming j) (outgoing j)
    x ∈ ordinary → y ∉ ordinary → z ∉ ordinary →
    (H.Adj x y → H.Adj x z → y = z) ∧ (H.Adj y x → H.Adj z x → y = z)
  layer_le : ∀ j,
    addTrimmedBridgeStars (initial j) (cell j) (erase j)
      (erase j ∘ src j) (incoming j) (outgoing j) ≤ G
  layer_disjoint : ∀ j k, j ≠ k →
    Disjoint (addTrimmedBridgeStars (initial j) (cell j) (erase j)
      (erase j ∘ src j) (incoming j) (outgoing j))
      (addTrimmedBridgeStars (initial k) (cell k) (erase k)
        (erase k ∘ src k) (incoming k) (outgoing k))
  cell_size : ∀ j u, ((cell j u).erase (erase j u)).card = n-1
  exceptional_count : ∀ j,
    ((univ.biUnion (fun u => (cell j u).erase (erase j u)))ᶜ : Finset V).card =
      ((univ.biUnion (cell j))ᶜ : Finset V).card+Fintype.card U
  superregular : ∀ j u,
    IsSuperregularPair (addTrimmedBridgeStars (initial j) (cell j) (erase j)
      (erase j ∘ src j) (incoming j) (outgoing j)) δ d
        ((cell j u).erase (erase j u)) ((cell j (F j u)).erase (erase j (F j u)))

section Layer

variable {L U I V : Type*} [Fintype U] [Fintype I] [Fintype V]
variable {G : Digraph V} {initial : L → Digraph V} {F : L → Equiv.Perm U} {C : Equiv.Perm I}
variable {cell : L → U → Finset V} {erase : L → U → V}
variable {src dst : L → I → U} {halfIn halfOut : L → I → Finset V} {κ n : ℕ} {δ d : ℝ}

/-- The layer on the original vertex type, with its physical bridge stars. -/
noncomputable def TrimmedPhysicalBridgeLayers.graph
    (P : TrimmedPhysicalBridgeLayers G initial F C cell erase src dst halfIn halfOut κ n δ d)
    (j : L) : Digraph V :=
  addTrimmedBridgeStars (initial j) (cell j) (erase j) (erase j ∘ src j) (P.incoming j) (P.outgoing j)

/-- Keep the two reserve memberships chosen in the bridge construction. -/
def TrimmedPhysicalBridgeLayers.UsesBridgeReserves
    (P : TrimmedPhysicalBridgeLayers G initial F C cell erase src dst halfIn halfOut κ n δ d)
    (HIn HOut : Digraph V) : Prop :=
  (∀ j i x, x ∈ P.incoming j i → HIn.Adj x (erase j (src j i))) ∧
  ∀ j i y, y ∈ P.outgoing j i → HOut.Adj (erase j (src j i)) y

theorem TrimmedPhysicalBridgeLayers.graph_le_reserves
    (P : TrimmedPhysicalBridgeLayers G initial F C cell erase src dst halfIn halfOut κ n δ d)
    (HIn HOut : Digraph V) (h : P.UsesBridgeReserves HIn HOut) (j : L) :
    P.graph j ≤ initial j ⊔ (HIn ⊔ HOut) := by
  rintro x y (⟨hOld,_,_⟩ | ⟨i,_,⟨hx,rfl⟩ | ⟨rfl,hy⟩⟩)
  · exact Or.inl hOld
  · exact Or.inr (Or.inl (h.1 j i x hx))
  · exact Or.inr (Or.inr (h.2 j i y hy))

end Layer

set_option maxHeartbeats 1750000 in
/-- Add all bridge stars simultaneously. Each bridge has exact
semidegrees, the exceptional set is independent, and the ordinary
successor pairs stay superregular after one deletion per cell. -/
theorem exists_trimmed_physical_bridge_layers_with_reserves
    {L U I V : Type*} [Fintype L] [Fintype U] [Fintype I] [Fintype V]
    (G HIn HOut : Digraph V) (initial : L → Digraph V) (F : L → Equiv.Perm U)
    (σ : L → Equiv.Perm I) (project : U → I) (C : Equiv.Perm I)
    (cell : L → U → Finset V) (erase : L → U → V)
    (src dst : L → I → U) (halfIn halfOut : L → I → Finset V)
    (κ n : ℕ) (ε δ d : ℝ)
    (hG : ∀ j, initial j ≤ G) (hHIn : HIn ≤ G) (hHOut : HOut ≤ G)
    (hHDis : Disjoint HIn HOut)
    (hLayerDis : ∀ j k, j ≠ k → Disjoint (initial j) (initial k))
    (hReserve : ∀ j, Disjoint (initial j) HIn ∧ Disjoint (initial j) HOut)
    (hCSpan : ∀ i k, C.SameCycle i k)
    (hOrbit : ∀ j x y, (F j).SameCycle x y ↔ (σ j).SameCycle (project x) (project y))
    (hTags : ∀ j i, project (src j i) = i ∧ project (dst j i) = C i)
    (hSrc : ∀ j, Function.Injective (src j)) (hDst : ∀ j, Function.Injective (dst j))
    (hCellDis : ∀ j u v, u ≠ v → Disjoint (cell j u) (cell j v))
    (hCell : ∀ j u, (cell j u).card = n)
    (hErase : ∀ j u, erase j u ∈ cell j u)
    (hFresh : Function.Injective (fun q : L × U => erase q.1 q.2))
    (hHalfIn : ∀ j i, halfIn j i ⊆ cell j ((F j).symm (src j i)))
    (hHalfOut : ∀ j i, halfOut j i ⊆ cell j (dst j i))
    (hUseful : ∀ j i, let x := erase j (src j i)
      (κ:ℝ) < profileCount (halfIn j i) (inProfile HIn x) ∧
      (κ:ℝ) < profileCount (halfOut j i) (outProfile HOut x))
    (hSuper : ∀ j u, IsSuperregularPair (initial j) ε d (cell j u) (cell j (F j u)))
    (hd : 0 ≤ d) (hd₁ : d ≤ 1) (hδ : 2*ε ≤ δ) (hδ₁ : δ ≤ 1)
    (hRoom : ε*(n:ℝ)+1 ≤ δ*((n-1:ℕ):ℝ)) :
    ∃ P : TrimmedPhysicalBridgeLayers G initial F C cell erase src dst halfIn halfOut κ n δ d,
      P.UsesBridgeReserves HIn HOut := by
  let center (j : L) (i : I) := erase j (src j i)
  let trimmed (j : L) (u : U) := (cell j u).erase (erase j u)
  let ordinary (j : L) := univ.biUnion (trimmed j)
  have hInOrd (j : L) (u : U) : trimmed j u ⊆ ordinary j :=
    fun _ h => mem_biUnion.mpr ⟨u,mem_univ _,h⟩
  have hTrimDis (j : L) (u v : U) (h : u ≠ v) : Disjoint (trimmed j u) (trimmed j v) :=
    (hCellDis j u v h).mono (erase_subset _ _) (erase_subset _ _)
  have hOutside (j : L) (u : U) : erase j u ∉ ordinary j := by
    intro h
    obtain ⟨v,_,hv⟩ := mem_biUnion.mp h
    by_cases he : u = v
    · subst v
      exact (mem_erase.mp hv).1 rfl
    · exact disjoint_left.mp (hCellDis j u v he) (hErase j u) (mem_erase.mp hv).2
  have hCenters (j k : L) (i l : I) (h : center j i = center k l) : j = k := by
    have he : (j,src j i) = (k,src k l) := hFresh h
    exact congrArg Prod.fst he
  have hCenterInj (j : L) : Function.Injective (center j) := by
    intro i l h
    have he : (j,src j i) = (j,src j l) := hFresh h
    exact hSrc j (congrArg Prod.snd he)
  choose incoming outgoing hL hR hLC hRC hInArc hOutArc hStarLe using fun j i =>
    exists_bridge_arcs HIn HOut (center j i) (halfIn j i) (halfOut j i) κ
      (erase j ((F j).symm (src j i))) (erase j (dst j i)) (hUseful j i).1 (hUseful j i).2
  let star (j : L) (i : I) := bridgeArcs (center j i) (incoming j i) (outgoing j i)
  let layer (j : L) := addTrimmedBridgeStars (initial j) (cell j) (erase j)
    (center j) (incoming j) (outgoing j)
  have hInCell (j : L) (i : I) : incoming j i ⊆ trimmed j ((F j).symm (src j i)) := by
    intro x hx
    obtain ⟨hn,hh⟩ := mem_erase.mp (hL j i hx)
    exact mem_erase.mpr ⟨hn,hHalfIn j i hh⟩
  have hOutCell (j : L) (i : I) : outgoing j i ⊆ trimmed j (dst j i) := by
    intro x hx
    obtain ⟨hn,hh⟩ := mem_erase.mp (hR j i hx)
    exact mem_erase.mpr ⟨hn,hHalfOut j i hh⟩
  have hInRet (j : L) (i : I) : incoming j i ⊆ ordinary j := (hInCell j i).trans (hInOrd _ _)
  have hOutRet (j : L) (i : I) : outgoing j i ⊆ ordinary j := (hOutCell j i).trans (hInOrd _ _)
  have hAdj (j : L) (x y : V) : (layer j).Adj x y ↔
      ((initial j).Adj x y ∧ x ∈ ordinary j ∧ y ∈ ordinary j) ∨ ∃ i, (star j i).Adj x y := by
    simp only [layer,addTrimmedBridgeStars,Digraph.sup_adj,trimLayerArcs,indexedArcUnion,
      mem_univ,true_and,ordinary,trimmed,star]
  have hInExact (j : L) (i : I) (x : V) : (layer j).Adj x (center j i) ↔ x ∈ incoming j i := by
    rw [hAdj]
    constructor
    · rintro (⟨_,_,hy⟩ | ⟨k,⟨hx,he⟩ | ⟨_,hy⟩⟩)
      · exact (hOutside j (src j i) hy).elim
      · obtain rfl := hCenterInj j he
        exact hx
      · exact (hOutside j (src j i) (hOutRet j k hy)).elim
    · exact fun hx => Or.inr ⟨i,Or.inl ⟨hx,rfl⟩⟩
  have hOutExact (j : L) (i : I) (y : V) : (layer j).Adj (center j i) y ↔ y ∈ outgoing j i := by
    rw [hAdj]
    constructor
    · rintro (⟨_,hx,_⟩ | ⟨k,⟨hx,_⟩ | ⟨he,hy⟩⟩)
      · exact (hOutside j (src j i) hx).elim
      · exact (hOutside j (src j i) (hInRet j k hx)).elim
      · obtain rfl := hCenterInj j he
        exact hy
    · exact fun hy => Or.inr ⟨i,Or.inr ⟨rfl,hy⟩⟩
  have hExact (j : L) (i : I) : inDegree (layer j) (center j i) = κ ∧ outDegree (layer j) (center j i) = κ := by
    have hin : (univ.filter (fun x => (layer j).Adj x (center j i))).card = (incoming j i).card := by
      congr 1
      ext x
      simp only [mem_filter,mem_univ,true_and,hInExact]
    have hout : (univ.filter ((layer j).Adj (center j i))).card = (outgoing j i).card := by
      congr 1
      ext y
      simp only [mem_filter,mem_univ,true_and,hOutExact]
    exact ⟨hin.trans (hLC _ _),hout.trans (hRC _ _)⟩
  have hCard (j : L) (u : U) : (trimmed j u).card = n-1 :=
    (card_erase_of_mem (hErase j u)).trans (congrArg (·-1) (hCell j u))
  have hExceptional (j : L) :
      ((ordinary j)ᶜ : Finset V).card = ((univ.biUnion (cell j))ᶜ : Finset V).card+Fintype.card U := by
    have hKeep : (univ.biUnion (cell j)).card = (ordinary j).card+Fintype.card U := by
      dsimp only [ordinary]
      rw [card_biUnion (fun u _ v _ h => hCellDis j u v h),
        card_biUnion (fun u _ v _ h => hTrimDis j u v h),
        ←card_univ (α := U),card_eq_sum_ones,←sum_add_distrib]
      apply sum_congr rfl
      intro u _
      have hPos : 0 < n := by
        rw [←hCell j u]
        exact card_pos.mpr ⟨erase j u,hErase j u⟩
      rw [hCell,hCard]
      omega
    have hN := card_le_univ (univ.biUnion (cell j))
    rw [card_compl,card_compl]
    omega
  refine ⟨⟨incoming,outgoing,fun j i => ⟨hL j i,hR j i⟩,fun j i => ⟨hLC j i,hRC j i⟩,
    fun j i x => ⟨hInExact j i x,hOutExact j i x⟩,hExact,hCSpan,
    fun j i => hOutside j (src j i),?_,?_,?_,?_,?_,?_,hCard,hExceptional,?_⟩,⟨hInArc,hOutArc⟩⟩
  · intro j u
    refine ⟨project u,(hOrbit j _ _).mpr ?_⟩
    rw [(hTags j (project u)).1]
  · intro j i
    constructor
    · nth_rewrite 2 [←(F j).apply_symm_apply (src j i)]
      exact (Equiv.Perm.SameCycle.refl _ _).apply_right
    · apply (hOrbit j _ _).mpr
      rw [(hTags j i).2,(hTags j (C i)).1]
  · intro j x y
    change x ∉ ordinary j → y ∉ ordinary j → ¬ (layer j).Adj x y
    intro hx hy h
    rcases (hAdj j x y).mp h with ⟨_,hox,_⟩ | ⟨i,⟨hL,_⟩ | ⟨_,hR⟩⟩
    · exact hx hox
    · exact hx (hInRet j i hL)
    · exact hy (hOutRet j i hR)
  · intro j x y z
    change x ∈ ordinary j → y ∉ ordinary j → z ∉ ordinary j →
      ((layer j).Adj x y → (layer j).Adj x z → y = z) ∧
      ((layer j).Adj y x → (layer j).Adj z x → y = z)
    intro _ hy hz
    have hin (v : V) (hv : v ∉ ordinary j) (he : (layer j).Adj x v) :
        ∃ i, x ∈ incoming j i ∧ v = center j i := by
      rcases (hAdj _ _ _).mp he with ⟨_,_,h⟩ | ⟨i,hL | hR⟩
      · exact (hv h).elim
      · exact ⟨i,hL⟩
      · exact (hv (hOutRet _ _ hR.2)).elim
    have hout (v : V) (hv : v ∉ ordinary j) (he : (layer j).Adj v x) :
        ∃ i, v = center j i ∧ x ∈ outgoing j i := by
      rcases (hAdj _ _ _).mp he with ⟨_,h,_⟩ | ⟨i,hL | hR⟩
      · exact (hv h).elim
      · exact (hv (hInRet _ _ hL.1)).elim
      · exact ⟨i,hR⟩
    constructor
    · intro hxy hxz
      obtain ⟨i,hxi,hi⟩ := hin y hy hxy
      obtain ⟨k,hxk,hk⟩ := hin z hz hxz
      have he : (F j).symm (src j i) = (F j).symm (src j k) := by
        by_contra hn
        exact disjoint_left.mp (hTrimDis _ _ _ hn) (hInCell _ _ hxi) (hInCell _ _ hxk)
      obtain rfl := hSrc j ((F j).symm.injective he)
      exact hi.trans hk.symm
    · intro hyx hzx
      obtain ⟨i,hi,hxi⟩ := hout y hy hyx
      obtain ⟨k,hk,hxk⟩ := hout z hz hzx
      have he : dst j i = dst j k := by
        by_contra hn
        exact disjoint_left.mp (hTrimDis _ _ _ hn) (hOutCell _ _ hxi) (hOutCell _ _ hxk)
      obtain rfl := hDst j he
      exact hi.trans hk.symm
  · intro j x y h
    rcases (hAdj _ _ _).mp h with ⟨ha,_,_⟩ | ⟨i,hs⟩
    · exact hG j ha
    · exact sup_le hHIn hHOut (hStarLe j i hs)
  · intro j k hjk
    rw [disjoint_iff_inf_le]
    intro x y h
    rcases (hAdj _ _ _).mp h.1 with ⟨hj,_,_⟩ | ⟨i,hj⟩ <;>
      rcases (hAdj _ _ _).mp h.2 with ⟨hk,_,_⟩ | ⟨l,hk⟩
    · exact disjoint_iff_inf_le.mp (hLayerDis j k hjk) ⟨hj,hk⟩
    · rcases hStarLe k l hk with hin | hout
      · exact disjoint_iff_inf_le.mp (hReserve j).1 ⟨hj,hin⟩
      · exact disjoint_iff_inf_le.mp (hReserve j).2 ⟨hj,hout⟩
    · rcases hStarLe j i hj with hin | hout
      · exact disjoint_iff_inf_le.mp (hReserve k).1 ⟨hk,hin⟩
      · exact disjoint_iff_inf_le.mp (hReserve k).2 ⟨hk,hout⟩
    · exact disjoint_iff_inf_le.mp (disjoint_bridge_arcs HIn HOut _ _ _ _
        (fun he => hjk (hCenters j k i l he)) hHDis
        (hInArc j i) (hOutArc j i) (hInArc k l) (hOutArc k l)) ⟨hj,hk⟩
  · intro j u
    have hP := (hSuper j u).erase_one (hErase j u) (hErase j (F j u)) hd hd₁ hδ hδ₁
      (by simpa only [hCell,card_erase_of_mem (hErase j u)] using hRoom)
      (by simpa only [hCell,card_erase_of_mem (hErase j (F j u))] using hRoom)
    apply hP.congr_on
    intro x hx y hy
    change (initial j).Adj x y ↔ (layer j).Adj x y
    rw [hAdj]
    constructor
    · exact fun h => Or.inl ⟨h,hInOrd _ _ hx,hInOrd _ _ hy⟩
    · rintro (⟨h,_,_⟩ | ⟨i,⟨_,rfl⟩ | ⟨rfl,_⟩⟩)
      · exact h
      · exact (hOutside j (src j i) (hInOrd _ _ hy)).elim
      · exact (hOutside j (src j i) (hInOrd _ _ hx)).elim

/-- The bridge construction with its original interface. -/
theorem exists_trimmed_physical_bridge_layers
    {L U I V : Type*} [Fintype L] [Fintype U] [Fintype I] [Fintype V]
    (G HIn HOut : Digraph V) (initial : L → Digraph V) (F : L → Equiv.Perm U)
    (σ : L → Equiv.Perm I) (project : U → I) (C : Equiv.Perm I)
    (cell : L → U → Finset V) (erase : L → U → V)
    (src dst : L → I → U) (halfIn halfOut : L → I → Finset V)
    (κ n : ℕ) (ε δ d : ℝ)
    (hG : ∀ j, initial j ≤ G) (hHIn : HIn ≤ G) (hHOut : HOut ≤ G)
    (hHDis : Disjoint HIn HOut)
    (hLayerDis : ∀ j k, j ≠ k → Disjoint (initial j) (initial k))
    (hReserve : ∀ j, Disjoint (initial j) HIn ∧ Disjoint (initial j) HOut)
    (hCSpan : ∀ i k, C.SameCycle i k)
    (hOrbit : ∀ j x y, (F j).SameCycle x y ↔ (σ j).SameCycle (project x) (project y))
    (hTags : ∀ j i, project (src j i) = i ∧ project (dst j i) = C i)
    (hSrc : ∀ j, Function.Injective (src j)) (hDst : ∀ j, Function.Injective (dst j))
    (hCellDis : ∀ j u v, u ≠ v → Disjoint (cell j u) (cell j v))
    (hCell : ∀ j u, (cell j u).card = n)
    (hErase : ∀ j u, erase j u ∈ cell j u)
    (hFresh : Function.Injective (fun q : L × U => erase q.1 q.2))
    (hHalfIn : ∀ j i, halfIn j i ⊆ cell j ((F j).symm (src j i)))
    (hHalfOut : ∀ j i, halfOut j i ⊆ cell j (dst j i))
    (hUseful : ∀ j i, let x := erase j (src j i)
      (κ:ℝ) < profileCount (halfIn j i) (inProfile HIn x) ∧
      (κ:ℝ) < profileCount (halfOut j i) (outProfile HOut x))
    (hSuper : ∀ j u, IsSuperregularPair (initial j) ε d (cell j u) (cell j (F j u)))
    (hd : 0 ≤ d) (hd₁ : d ≤ 1) (hδ : 2*ε ≤ δ) (hδ₁ : δ ≤ 1)
    (hRoom : ε*(n:ℝ)+1 ≤ δ*((n-1:ℕ):ℝ)) :
    Nonempty (TrimmedPhysicalBridgeLayers G initial F C cell erase src dst halfIn halfOut κ n δ d) := by
  obtain ⟨P,_⟩ := exists_trimmed_physical_bridge_layers_with_reserves G HIn HOut initial F σ project C
    cell erase src dst halfIn halfOut κ n ε δ d hG hHIn hHOut hHDis hLayerDis hReserve hCSpan hOrbit hTags
    hSrc hDst hCellDis hCell hErase hFresh hHalfIn hHalfOut hUseful hSuper hd hd₁ hδ hδ₁ hRoom
  exact ⟨P⟩

end OverfullWork.DirectedRobustExpansion
