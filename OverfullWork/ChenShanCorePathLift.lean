module

public import OverfullWork.ChenShanPathWitnesses
public import OverfullWork.ChenShanReserveTutte
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph
open scoped Classical

variable {V I : Type*}

/-- A quotient edge records an edge between distinct assigned core labels. -/
def coreQuotient (G : SimpleGraph V) (label : V → I) : SimpleGraph I where
  Adj i j := i ≠ j ∧ ∃ v w, G.Adj v w ∧ label v = i ∧ label w = j
  symm := by
    constructor
    rintro i j ⟨hne,v,w,hvw,hi,hj⟩
    exact ⟨hne.symm,w,v,hvw.symm,hj,hi⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem coreQuotient_reachable {G : SimpleGraph V} (label : V → I)
    {v w : V} (h : G.Reachable v w) : (coreQuotient G label).Reachable (label v) (label w) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons u v _ huv _ ih =>
    by_cases hEq : label u = label v
    · simpa only [hEq] using ih
    · have hAdj : (coreQuotient G label).Adj (label u) (label v) :=
        ⟨hEq,u,v,huv,rfl,rfl⟩
      exact hAdj.reachable.trans ih

private theorem walk_length_le_one_of_eq_or_adj {G : SimpleGraph V} {u v : V}
    (h : u = v ∨ G.Adj u v) : ∃ p : G.Walk u v, p.length ≤ 1 := by
  rcases h with rfl | h
  · exact ⟨.nil,by simp⟩
  · exact ⟨.cons h .nil,by simp⟩

private theorem lift_coreQuotient_edge {G : SimpleGraph V} (label : V → I) (core : V → Prop)
    (hAttach : ∀ v, ∃ w, core w ∧ label w = label v ∧ (v = w ∨ G.Adj v w))
    {i j : I} (h : (coreQuotient G label).Adj i j) :
    ∃ u v, core u ∧ core v ∧ label u = i ∧ label v = j ∧
      ∃ p : G.Walk u v, p.length ≤ 3 := by
  obtain ⟨_,x,y,hxy,hx,hy⟩ := h
  obtain ⟨u,hu,huLabel,huAdj⟩ := hAttach x
  obtain ⟨v,hv,hvLabel,hvAdj⟩ := hAttach y
  obtain ⟨p,hp⟩ := walk_length_le_one_of_eq_or_adj (huAdj.imp Eq.symm Adj.symm)
  obtain ⟨q,hq⟩ := walk_length_le_one_of_eq_or_adj hvAdj
  refine ⟨u,v,hu,hv,huLabel.trans hx,hvLabel.trans hy,p.append (.cons hxy q),?_⟩
  rw [Walk.length_append,Walk.length_cons]
  omega

private theorem lift_coreQuotient_walk {G : SimpleGraph V} (label : V → I) (core : V → Prop)
    (hAttach : ∀ v, ∃ w, core w ∧ label w = label v ∧ (v = w ∨ G.Adj v w))
    (hClique : ∀ u v, core u → core v → label u = label v → u = v ∨ G.Adj u v)
    {i j : I} (p : (coreQuotient G label).Walk i j) (hLen : 0 < p.length) :
    ∃ u v, core u ∧ core v ∧ label u = i ∧ label v = j ∧
      ∃ q : G.Walk u v, q.length+1 ≤ 4*p.length := by
  induction p with
  | nil => exact (Nat.lt_irrefl _ hLen).elim
  | @cons i j k h p ih =>
    obtain ⟨u,v,hu,hv,hui,hvj,q,hq⟩ := lift_coreQuotient_edge label core hAttach h
    by_cases hNil : p.length = 0
    · have hjk := Walk.eq_of_length_eq_zero hNil (p := p)
      refine ⟨u,v,hu,hv,hui,hvj.trans hjk,q,?_⟩
      rw [Walk.length_cons,hNil]
      omega
    · obtain ⟨u',v',hu',hv',hu'j,hv'k,q',hq'⟩ := ih (Nat.pos_of_ne_zero hNil)
      obtain ⟨d,hd⟩ := walk_length_le_one_of_eq_or_adj (hClique v u' hv hu' (hvj.trans hu'j.symm))
      refine ⟨u,v',hu,hv',hui,hv'k,(q.append d).append q',?_⟩
      rw [Walk.length_append,Walk.length_append,Walk.length_cons]
      omega

/-- With at most four cores, two distinct connected core labels are joined
by a path with at most twelve vertices. Every vertex is assigned to a core
containing it or adjacent to it. -/
theorem exists_short_path_between_core_labels [Fintype I] {G : SimpleGraph V}
    (label : V → I) (core : V → Prop) (hFour : Fintype.card I ≤ 4)
    (hAttach : ∀ v, ∃ w, core w ∧ label w = label v ∧ (v = w ∨ G.Adj v w))
    (hClique : ∀ u v, core u → core v → label u = label v → u = v ∨ G.Adj u v)
    {x y : V} (hNe : label x ≠ label y) (hReach : G.Reachable x y) :
    ∃ u v, core u ∧ core v ∧ label u = label x ∧ label v = label y ∧
      ∃ p : G.Walk u v, p.IsPath ∧ p.support.length ≤ 12 := by
  classical
  obtain ⟨p,hp⟩ := (coreQuotient_reachable label hReach).exists_isPath
  have hBound : p.length < 4 := hp.length_lt.trans_le hFour
  have hPos : 0 < p.length := Nat.pos_of_ne_zero (fun h => hNe (Walk.eq_of_length_eq_zero h))
  obtain ⟨u,v,hu,hv,hux,hvy,q,hq⟩ := lift_coreQuotient_walk label core hAttach hClique p hPos
  refine ⟨u,v,hu,hv,hux,hvy,q.bypass,q.bypass_isPath,?_⟩
  rw [Walk.length_support]
  have hle := q.length_bypass_le_length
  omega

/-- Choose an anchor for every vertex outside the disjoint core cliques. -/
theorem exists_short_path_between_core_cliques [Fintype I] {G : SimpleGraph V}
    (K : I → Set V) (hFour : Fintype.card I ≤ 4)
    (hDis : (Set.univ : Set I).PairwiseDisjoint K) (hCliques : ∀ i, G.IsClique (K i))
    (hCover : ∀ v, ∃ i w, w ∈ K i ∧ (v = w ∨ G.Adj v w))
    {i j : I} (hNe : i ≠ j) {x y : V}
    (hx : x ∈ K i) (hy : y ∈ K j) (hReach : G.Reachable x y) :
    ∃ u v, u ∈ K i ∧ v ∈ K j ∧ ∃ p : G.Walk u v, p.IsPath ∧ p.support.length ≤ 12 := by
  classical
  let core (v : V) := ∃ i, v ∈ K i
  let label (v : V) := if h : core v then h.choose else (hCover v).choose
  have hLabel {v : V} {i : I} (hi : v ∈ K i) : label v = i := by
    have hv : core v := ⟨i,hi⟩
    change (if h : core v then h.choose else (hCover v).choose) = i
    rw [dite_eq_left hv]
    by_contra hn
    exact Set.disjoint_left.mp (hDis (Set.mem_univ _) (Set.mem_univ _) hn) hv.choose_spec hi
  have hCore (v : V) (hv : core v) : v ∈ K (label v) := by
    obtain ⟨i,hi⟩ := hv
    rwa [hLabel hi]
  have hAttach (v : V) : ∃ w, core w ∧ label w = label v ∧ (v = w ∨ G.Adj v w) := by
    by_cases hv : core v
    · exact ⟨v,hv,rfl,Or.inl rfl⟩
    · obtain ⟨w,hw,he⟩ := (hCover v).choose_spec
      have hEq : (hCover v).choose = label v := by
        change _ = (if h : core v then h.choose else (hCover v).choose)
        rw [dite_eq_right hv]
      exact ⟨w,⟨_,hw⟩,(hLabel hw).trans hEq,he⟩
  have hCliq (u v : V) (hu : core u) (hv : core v) (he : label u = label v) :
      u = v ∨ G.Adj u v := by
    by_cases huv : u = v
    · exact Or.inl huv
    · exact Or.inr (hCliques (label v) (he ▸ hCore u hu) (hCore v hv) huv)
  have hxy : label x ≠ label y := by rw [hLabel hx,hLabel hy]; exact hNe
  obtain ⟨u,v,hu,hv,hui,hvj,p,hp,hpLen⟩ := exists_short_path_between_core_labels
    label core hFour hAttach hCliq hxy hReach
  have hui' : label u = i := hui.trans (hLabel hx)
  have hvj' : label v = j := hvj.trans (hLabel hy)
  exact ⟨u,v,hui' ▸ hCore u hu,hvj' ▸ hCore v hv,p,hp,hpLen⟩

/-- The vertex support of an actual path between two specified cores. -/
def CorePathWitness (G : SimpleGraph V) (K : I → Set V) (i j : I) (P : Finset V) : Prop :=
  ∃ u v, u ∈ K i ∧ v ∈ K j ∧
    ∃ p : G.Walk u v, p.IsPath ∧ p.support.length ≤ 12 ∧
      ∀ v', v' ∈ P ↔ v' ∈ p.support

private theorem cover_induced_core_cliques [Finite V] {G : SimpleGraph V}
    (K : I → Set V) (Y : Finset V)
    (hNeighbors : ∀ v, (∀ i, v ∉ K i) → Y.card < (G.neighborSet v ∩ ⋃ i, K i).ncard)
    (u : ↥((↑Y : Set V)ᶜ)) :
    ∃ i, ∃ w : ↥((↑Y : Set V)ᶜ), w.val ∈ K i ∧
      (u = w ∨ (G.induce (↑Y : Set V)ᶜ).Adj u w) := by
  by_cases hCore : ∃ i, u.val ∈ K i
  · obtain ⟨i,hi⟩ := hCore
    exact ⟨i,u,hi,Or.inl rfl⟩
  · have hMore := hNeighbors u.val (fun i hi => hCore ⟨i,hi⟩)
    have hNot : ¬ G.neighborSet u.val ∩ (⋃ i, K i) ⊆ (Y : Set V) := by
      intro h
      exact (not_le.mpr hMore) (by simpa using Set.ncard_le_ncard h)
    obtain ⟨w,hw,hwY⟩ := Set.not_subset.mp hNot
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hw.2
    exact ⟨i,⟨w,hwY⟩,hi,Or.inr hw.1⟩

/-- If the deleted set cannot exhaust the core neighbors of any exceptional
vertex, any connected pair of surviving distinct cores has a short witness
avoiding the deleted set. -/
theorem exists_short_core_path_witness_avoiding [Finite V] [Fintype I] {G : SimpleGraph V}
    (K : I → Set V) (hFour : Fintype.card I ≤ 4)
    (hDis : (Set.univ : Set I).PairwiseDisjoint K) (hCliques : ∀ i, G.IsClique (K i))
    (Y : Finset V)
    (hNeighbors : ∀ v, (∀ i, v ∉ K i) → Y.card < (G.neighborSet v ∩ ⋃ i, K i).ncard)
    {i j : I} (hNe : i ≠ j) {x y : ↥((↑Y : Set V)ᶜ)}
    (hx : x.val ∈ K i) (hy : y.val ∈ K j)
    (hReach : (G.induce (↑Y : Set V)ᶜ).Reachable x y) :
    ∃ P : Finset V, CorePathWitness G K i j P ∧ Disjoint P Y := by
  classical
  let S := (↑Y : Set V)ᶜ
  let H := G.induce S
  let K' (i : I) : Set S := Subtype.val ⁻¹' K i
  have hKD : (Set.univ : Set I).PairwiseDisjoint K' := by
    intro a ha b hb hab
    exact Set.disjoint_left.mpr (fun _ h₁ h₂ => Set.disjoint_left.mp (hDis ha hb hab) h₁ h₂)
  have hKC (i : I) : H.IsClique (K' i) :=
    fun _ hu _ hv hn => hCliques i hu hv (fun he => hn (Subtype.ext he))
  have hCover := cover_induced_core_cliques K Y hNeighbors
  obtain ⟨u,v,hu,hv,p,hp,hpLen⟩ := exists_short_path_between_core_cliques
    K' hFour hKD hKC hCover hNe hx hy hReach
  let f : H →g G := (Embedding.induce (G := G) S).toHom
  let q := p.map f
  refine ⟨q.support.toFinset,⟨u.val,v.val,hu,hv,q,?_,?_,fun _ => List.mem_toFinset⟩,?_⟩
  · exact hp.map Subtype.val_injective
  · change (p.map f).support.length ≤ 12
    rwa [Walk.support_map, List.length_map]
  · apply Finset.disjoint_left.mpr
    intro w hw hY
    have hm : w ∈ p.support.map f := by simpa [q,Walk.support_map] using hw
    obtain ⟨w',_,rfl⟩ := List.mem_map.mp hm
    exact w'.property hY

theorem CorePathWitness.card_le {G : SimpleGraph V} {K : I → Set V} {i j : I} {P : Finset V}
    (h : CorePathWitness G K i j P) : P.card ≤ 12 := by
  classical
  obtain ⟨u,v,hu,hv,p,hp,hLen,hP⟩ := h
  have hEq : P = p.support.toFinset := by ext; simpa using hP _
  rwa [hEq,List.toFinset_card_of_nodup hp.support_nodup]

theorem CorePathWitness.reverse {G : SimpleGraph V} {K : I → Set V} {i j : I} {P : Finset V}
    (h : CorePathWitness G K i j P) : CorePathWitness G K j i P := by
  obtain ⟨u,v,hu,hv,p,hp,hLen,hP⟩ := h
  exact ⟨v,u,hv,hu,p.reverse,hp.reverse,by simpa [Walk.support_reverse] using hLen,
    fun x => by simpa [Walk.support_reverse] using hP x⟩

theorem CorePathWitness.reachable_induce {G : SimpleGraph V} {K : I → Set V} {i j : I}
    {P Y : Finset V} (h : CorePathWitness G K i j P) (hDis : Disjoint P Y) :
    ∃ x y : ↥((↑Y : Set V)ᶜ), x.val ∈ K i ∧ y.val ∈ K j ∧
      (G.induce (↑Y : Set V)ᶜ).Reachable x y := by
  obtain ⟨x,y,hx,hy,p,_,_,hP⟩ := h
  have hp (v : V) (hv : v ∈ p.support) : v ∈ (↑Y : Set V)ᶜ :=
    fun hY => Finset.disjoint_left.mp hDis ((hP v).mpr hv) hY
  exact ⟨_,_,hx,hy,(p.induce (↑Y : Set V)ᶜ hp).reachable⟩

/-- The paper's fixed reserve of actual paths between core pairs. It
preserves their connectivity after any three deletions, and after
arbitrary further deletions disjoint from the reserve. -/
theorem exists_core_clique_path_reserve [Finite V] [Fintype I] {G : SimpleGraph V}
    (K : I → Set V) (hFour : Fintype.card I ≤ 4)
    (hDis : (Set.univ : Set I).PairwiseDisjoint K) (hCliques : ∀ i, G.IsClique (K i))
    (hNeighbors : ∀ v, (∀ i, v ∉ K i) → 3 < (G.neighborSet v ∩ ⋃ i, K i).ncard) :
    ∃ W : Finset V, W.card ≤ 135720 ∧
      ∀ Y D : Finset V, Y.card ≤ 3 → Disjoint W D → ∀ i j, i ≠ j →
      (∃ x y : ↥((↑Y : Set V)ᶜ), x.val ∈ K i ∧ y.val ∈ K j ∧
        (G.induce (↑Y : Set V)ᶜ).Reachable x y) →
      ∃ x y : ↥((↑(Y ∪ D) : Set V)ᶜ), x.val ∈ K i ∧ y.val ∈ K j ∧
        (G.induce (↑(Y ∪ D) : Set V)ᶜ).Reachable x y := by
  classical
  let rank : I ↪ Fin 4 := (Fintype.equivFin I).toEmbedding.trans (Fin.castLEEmb hFour)
  let T := (Finset.univ : Finset (I × I)).filter (fun q => rank q.1 < rank q.2)
  let B := (Finset.univ : Finset (Fin 4 × Fin 4)).filter (fun q => q.1 < q.2)
  let f (q : T) : B := ⟨(rank q.val.1,rank q.val.2),Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,(Finset.mem_filter.mp q.property).2⟩⟩
  have hInj : Function.Injective f := by
    intro a b h
    have h' := congrArg Subtype.val h
    apply Subtype.ext
    exact Prod.ext (rank.injective (congrArg Prod.fst h')) (rank.injective (congrArg Prod.snd h'))
  have hSize : T.card ≤ 6 := by
    have h := Fintype.card_le_of_injective f hInj
    simp only [Fintype.card_coe] at h
    exact h.trans (show B.card ≤ 6 by decide)
  let Good (q : I × I) := CorePathWitness G K q.1 q.2
  obtain ⟨W,hW,hReserve⟩ := exists_fault_tolerant_path_reserve T hSize Good
    (fun q P hp => CorePathWitness.card_le hp)
  refine ⟨W,hW,?_⟩
  intro Y D hY hWD i j hne ⟨x,y,hx,hy,hxy⟩
  have hSizeY (v : V) (hv : ∀ k, v ∉ K k) :
      Y.card < (G.neighborSet v ∩ ⋃ k, K k).ncard := hY.trans_lt (hNeighbors v hv)
  rcases lt_or_gt_of_ne (rank.injective.ne hne) with hij | hji
  · have hi : (i,j) ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩
    obtain ⟨P,_,hP,hAvoid⟩ := hReserve (i,j) hi Y D hY hWD
      (exists_short_core_path_witness_avoiding K hFour hDis hCliques Y hSizeY hne hx hy hxy)
    exact CorePathWitness.reachable_induce hP hAvoid
  · have hj : (j,i) ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hji⟩
    obtain ⟨P,_,hP,hAvoid⟩ := hReserve (j,i) hj Y D hY hWD
      (exists_short_core_path_witness_avoiding K hFour hDis hCliques Y hSizeY hne.symm hy hx hxy.symm)
    exact (CorePathWitness.reverse hP).reachable_induce hAvoid

/-- The fixed reserve preserves the component relation on every surviving
vertex when the total deletion leaves a vertex and the required
neighbors in the cores. -/
theorem exists_core_clique_reserve_preserving_components
    [Finite V] [Fintype I] {G : SimpleGraph V}
    (K : I → Set V) (hFour : Fintype.card I ≤ 4)
    (hDis : (Set.univ : Set I).PairwiseDisjoint K) (hCliques : ∀ i, G.IsClique (K i))
    (hNeighbors : ∀ v, (∀ i, v ∉ K i) → 3 < (G.neighborSet v ∩ ⋃ i, K i).ncard) :
    ∃ W : Finset V, W.card ≤ 135720 ∧
      ∀ Y D : Finset V, Y.card ≤ 3 → Disjoint W D →
      (∀ i, (Y ∪ D).card < (K i).ncard) →
      (∀ v, (∀ i, v ∉ K i) → (Y ∪ D).card < (G.neighborSet v ∩ ⋃ i, K i).ncard) →
      ∃ hIn : ((↑(Y ∪ D) : Set V)ᶜ) ⊆ (↑Y : Set V)ᶜ,
        ∀ x y : ↥((↑(Y ∪ D) : Set V)ᶜ),
          (G.induce (↑Y : Set V)ᶜ).Reachable (Set.inclusion hIn x) (Set.inclusion hIn y) ↔
            (G.induce (↑(Y ∪ D) : Set V)ᶜ).Reachable x y := by
  classical
  obtain ⟨W,hW,hKeep⟩ := exists_core_clique_path_reserve K hFour hDis hCliques hNeighbors
  refine ⟨W,hW,?_⟩
  intro Y D hY hWD hK hN
  let T : Set V := (↑(Y ∪ D) : Set V)ᶜ
  let S : Set V := (↑Y : Set V)ᶜ
  have hTS : T ⊆ S := fun _ ht hy => ht (Finset.mem_union_left _ hy)
  refine ⟨hTS,?_⟩
  intro x y
  refine ⟨?_,fun h => h.map (G.induceHomOfLE hTS).toHom⟩
  apply reachable_induce_of_core_witnesses hTS K hCliques _ _ x y
  · intro v
    obtain ⟨i,w,hw,h⟩ := cover_induced_core_cliques K (Y ∪ D) hN v
    rcases h with rfl | hadj
    · exact ⟨i,v,hw,Reachable.refl _⟩
    · exact ⟨i,w,hw,hadj.reachable⟩
  · intro i j h
    by_cases hij : i = j
    · subst j
      have hNot : ¬ K i ⊆ (↑(Y ∪ D) : Set V) := by
        intro hSub
        exact (not_le.mpr (hK i)) (by simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hSub)
      obtain ⟨w,hw,hW⟩ := Set.not_subset.mp hNot
      exact ⟨⟨w,hW⟩,⟨w,hW⟩,hw,hw,Reachable.refl _⟩
    · exact hKeep Y D hY hWD i j hij h

private theorem odd_components_le_reachable_clique_cover [Finite V] [Finite I]
    (G : SimpleGraph V) (K : I → Set V) (hClique : ∀ i, G.IsClique (K i))
    (hCover : ∀ v, ∃ i w, w ∈ K i ∧ G.Reachable v w) :
    G.oddComponents.ncard ≤ Nat.card I := by
  classical
  have hRep (c : G.oddComponents) : ∃ v, v ∈ c.val.supp := c.val.nonempty_supp
  choose v hv using hRep
  choose i w hw hReach using fun c => hCover (v c)
  have hMem (c : G.oddComponents) : w c ∈ c.val.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact (ConnectedComponent.sound (hReach c)).symm.trans ((ConnectedComponent.mem_supp_iff _ _).mp (hv c))
  have hInj : Function.Injective i := by
    intro c d hEq
    apply Subtype.ext
    apply ConnectedComponent.eq_of_common_vertex (hMem c)
    by_cases h : w c = w d
    · rw [h]
      exact hMem d
    · have ha := hClique (i d) (hEq ▸ hw c) (hw d) h
      exact d.val.mem_supp_of_adj_mem_supp (hMem d) ha.symm
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective i hInj

/-- For the middle range in the Tutte check, only deletions inside the
cores can exhaust a vertex's neighbors in the cores. -/
theorem odd_components_induce_le_core_count [Finite V] [Fintype I] {G : SimpleGraph V}
    (K : I → Set V) (hClique : ∀ i, G.IsClique (K i)) (Y : Set V)
    (hNeighbors : ∀ v, (∀ i, v ∉ K i) →
      (Y ∩ ⋃ i, K i).ncard < (G.neighborSet v ∩ ⋃ i, K i).ncard) :
    (G.induce Yᶜ).oddComponents.ncard ≤ Fintype.card I := by
  classical
  let S := Yᶜ
  let H := G.induce S
  let K' (i : I) : Set S := Subtype.val ⁻¹' K i
  have hK (i : I) : H.IsClique (K' i) :=
    fun _ hu _ hv hn => hClique i hu hv (fun he => hn (Subtype.ext he))
  rw [← Nat.card_eq_fintype_card]
  apply odd_components_le_reachable_clique_cover H K' hK
  intro v
  by_cases hCore : ∃ i, v.val ∈ K i
  · obtain ⟨i,hi⟩ := hCore
    exact ⟨i,v,hi,Reachable.refl _⟩
  · have hMore := hNeighbors v.val (fun i hi => hCore ⟨i,hi⟩)
    have hNot : ¬ G.neighborSet v.val ∩ (⋃ i, K i) ⊆ Y := by
      intro h
      exact (not_le.mpr hMore) (Set.ncard_le_ncard fun _ hw => ⟨h hw,hw.2⟩)
    obtain ⟨w,hw,hWY⟩ := Set.not_subset.mp hNot
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hw.2
    have hadj : H.Adj v ⟨w,hWY⟩ := hw.1
    exact ⟨i,⟨w,hWY⟩,hi,hadj.reachable⟩

/-- For the large range, use one clique per core and a singleton for each
exceptional vertex. Empty parts cause no problem after deletion. -/
theorem odd_components_induce_le_core_add_exceptional [Finite V] [Fintype I]
    {G : SimpleGraph V} (K : I → Set V) (X : Set V) (Y : Set V)
    (hClique : ∀ i, G.IsClique (K i)) (hCover : ∀ v, v ∉ X → ∃ i, v ∈ K i) :
    (G.induce Yᶜ).oddComponents.ncard ≤ Fintype.card I + X.ncard := by
  classical
  let S := Yᶜ
  let H := G.induce S
  let C : I ⊕ X → Set S := Sum.elim (fun i => Subtype.val ⁻¹' K i) (fun w => {v | v.val = w.val})
  have hC (j : I ⊕ X) : H.IsClique (C j) := by
    rcases j with i | w
    · exact fun _ hu _ hv hn => hClique i hu hv (fun he => hn (Subtype.ext he))
    · intro v hv v' hv' hne
      have hEq : v.val = v'.val := (show v.val = w.val from hv).trans (show v'.val = w.val from hv').symm
      exact (hne (Subtype.ext hEq)).elim
  have hCv (v : S) : ∃ j, v ∈ C j := by
    by_cases hv : v.val ∈ X
    · exact ⟨.inr ⟨v.val,hv⟩,rfl⟩
    · obtain ⟨i,hi⟩ := hCover v.val hv
      exact ⟨.inl i,hi⟩
  have hBound := odd_component_count_le_clique_cover H C hC hCv
  simpa only [Nat.card_sum,Nat.card_eq_fintype_card (α := I),Nat.card_coe_set_eq] using hBound

end OverfullWork.ChenShan
