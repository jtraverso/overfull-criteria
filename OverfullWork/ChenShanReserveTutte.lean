module

public import Mathlib.Combinatorics.SimpleGraph.Tutte
public import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph

variable {V U I : Type*}

/-- A matching removes an even number of vertices from each component. -/
theorem odd_support_sdiff_matching_iff [Fintype V]
    {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsMatching)
    (c : G.ConnectedComponent) : Odd (c.supp \ M.verts).ncard ↔ Odd c.supp.ncard := by
  classical
  have hEven : Even (M.verts ∩ c.supp).ncard := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    have he := (hM.induce_connectedComponent c).even_card
    simpa only [Subgraph.induce_verts,Set.toFinset_card] using he
  have hCard := Set.ncard_inter_add_ncard_sdiff_eq_ncard c.supp M.verts
  rw [Set.inter_comm] at hCard
  obtain ⟨q,hq⟩ := hEven
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x+q,by omega⟩
  · rintro ⟨x,hx⟩
    exact ⟨x-q,by omega⟩

/-- Match component labels across a deletion to transfer the odd-component bound. -/
theorem odd_components_le_of_matching_deletion [Fintype V] [Finite U]
    {G : SimpleGraph V} {R : SimpleGraph U} {M : G.Subgraph} (hM : M.IsMatching)
    (j : R.ConnectedComponent ↪ G.ConnectedComponent)
    (hSize : ∀ c, c.supp.ncard = ((j c).supp \ M.verts).ncard) :
    R.oddComponents.ncard ≤ G.oddComponents.ncard := by
  rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq]
  refine Nat.card_le_card_of_injective (fun c : R.oddComponents => (⟨j c.val,?_⟩ : G.oddComponents)) ?_
  · have h : Odd c.val.supp.ncard := c.property
    rw [hSize c.val] at h
    exact (odd_support_sdiff_matching_iff hM (j c.val)).mp h
  · intro c d h
    exact Subtype.ext (j.injective (congrArg Subtype.val h))

/-- If deleting the endpoints of a matching does not split any component,
the remaining graph has at most as many odd components as the original. -/
theorem odd_components_induce_le_of_matching [Fintype V]
    {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsMatching)
    (hReach : ∀ v w : ↥(M.vertsᶜ : Set V), G.Reachable v.val w.val →
      (G.induce M.vertsᶜ).Reachable v w) :
    (G.induce M.vertsᶜ).oddComponents.ncard ≤ G.oddComponents.ncard := by
  let R := G.induce M.vertsᶜ
  let φ : R →g G := ⟨Subtype.val,fun h => h⟩
  let j : R.ConnectedComponent ↪ G.ConnectedComponent :=
    ⟨ConnectedComponent.map φ, ConnectedComponent.ind₂ (fun v w h =>
      ConnectedComponent.sound (hReach v w (ConnectedComponent.exact h)))⟩
  apply odd_components_le_of_matching_deletion hM j
  intro c
  have hMem (v : ↥(M.vertsᶜ : Set V)) : v ∈ c.supp ↔ v.val ∈ (j c).supp := by
    simp only [ConnectedComponent.mem_supp_iff]
    change R.connectedComponentMk v = c ↔ j (R.connectedComponentMk v) = j c
    exact j.injective.eq_iff.symm
  let p : c.supp → ↥((j c).supp \ M.verts) :=
    fun v => ⟨v.val.val,(hMem v.val).mp v.property,v.val.property⟩
  have hp : Function.Bijective p := by
    constructor
    · intro v w h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : ↥((j c).supp \ M.verts) => x.val) h))
    · intro v
      exact ⟨⟨⟨v.val,v.property.2⟩,(hMem _).mpr v.property.1⟩,rfl⟩
  exact Nat.card_congr (Equiv.ofBijective p hp)

/-- A clique remains connected on its surviving vertices. -/
private theorem reachable_in_induced_clique {G : SimpleGraph V} {S K : Set V}
    (hK : G.IsClique K) (v w : S) (hv : v.val ∈ K) (hw : w.val ∈ K) :
    (G.induce S).Reachable v w := by
  by_cases h : v = w
  · subst w
    exact SimpleGraph.Reachable.refl _
  · have hne : v.val ≠ w.val := fun h' => h (Subtype.ext h')
    have hadj : (G.induce S).Adj v w := hK hv hw hne
    exact hadj.reachable

/-- If the surviving vertices can still reach a core and every connected
pair of cores has a surviving witness, the induced deletion splits no
component on the surviving vertices. -/
theorem reachable_induce_of_core_witnesses {G : SimpleGraph V} {S T : Set V}
    (hTS : T ⊆ S) (K : I → Set V) (hClique : ∀ i, G.IsClique (K i))
    (hAttach : ∀ v : T, ∃ (i : I) (x : T), x.val ∈ K i ∧ (G.induce T).Reachable v x)
    (hKeep : ∀ i j : I, (∃ x y : S, x.val ∈ K i ∧ y.val ∈ K j ∧
      (G.induce S).Reachable x y) → ∃ x y : T, x.val ∈ K i ∧ y.val ∈ K j ∧
      (G.induce T).Reachable x y)
    (v w : T) (hvw : (G.induce S).Reachable (Set.inclusion hTS v) (Set.inclusion hTS w)) :
    (G.induce T).Reachable v w := by
  obtain ⟨i,x,hxi,hvx⟩ := hAttach v
  obtain ⟨j,y,hyj,hwy⟩ := hAttach w
  let φ := (G.induceHomOfLE hTS).toHom
  have hxy : (G.induce S).Reachable (Set.inclusion hTS x) (Set.inclusion hTS y) :=
    ((hvx.map φ).symm.trans hvw).trans (hwy.map φ)
  obtain ⟨x',y',hx'i,hy'j,hxy'⟩ := hKeep i j
    ⟨Set.inclusion hTS x,Set.inclusion hTS y,hxi,hyj,hxy⟩
  have hx := reachable_in_induced_clique (hClique i) x x' hxi hx'i
  have hy := reachable_in_induced_clique (hClique j) y' y hy'j hyj
  exact hvx.trans (hx.trans (hxy'.trans (hy.trans hwy.symm)))

/-- A finite cover by cliques bounds the number of components by the number of cliques. -/
theorem component_count_le_clique_cover [Finite V] [Finite I] (G : SimpleGraph V)
    (K : I → Set V) (hClique : ∀ i, G.IsClique (K i)) (hCover : ∀ v, ∃ i, v ∈ K i) :
    Nat.card G.ConnectedComponent ≤ Nat.card I := by
  classical
  have hRep (c : G.ConnectedComponent) : ∃ v, v ∈ c.supp := c.nonempty_supp
  choose v hv using hRep
  choose i hi using fun c => hCover (v c)
  refine Nat.card_le_card_of_injective i ?_
  intro c d he
  apply ConnectedComponent.eq_of_common_vertex (hv c)
  by_cases h : v c = v d
  · rw [h]
    exact hv d
  · have hadj := hClique (i d) (he ▸ hi c) (hi d) h
    exact d.mem_supp_of_adj_mem_supp (hv d) hadj.symm

theorem odd_component_count_le_clique_cover [Finite V] [Finite I] (G : SimpleGraph V)
    (K : I → Set V) (hClique : ∀ i, G.IsClique (K i)) (hCover : ∀ v, ∃ i, v ∈ K i) :
    G.oddComponents.ncard ≤ Nat.card I := by
  rw [← Nat.card_coe_set_eq]
  have h := Nat.card_le_card_of_injective
    (Subtype.val : G.oddComponents → G.ConnectedComponent) Subtype.val_injective
  exact h.trans (component_count_le_clique_cover G K hClique hCover)

/-- The three cardinality ranges of the Tutte argument in Chen–Shan, Lemma 5.22. -/
theorem exists_perfect_matching_of_reserve_tutte_bounds [Finite V] (G : SimpleGraph V) (t : ℕ)
    (hSmall : ∀ Y : Set V, Y.ncard ≤ 3 →
      ((⊤ : G.Subgraph).deleteVerts Y).coe.oddComponents.ncard ≤ Y.ncard)
    (hMiddle : ∀ Y : Set V, 4 ≤ Y.ncard → Y.ncard < t+4 →
      ((⊤ : G.Subgraph).deleteVerts Y).coe.oddComponents.ncard ≤ 4)
    (hLarge : ∀ Y : Set V, t+4 ≤ Y.ncard →
      ((⊤ : G.Subgraph).deleteVerts Y).coe.oddComponents.ncard ≤ t+4) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  apply SimpleGraph.tutte.mpr
  intro Y
  rw [IsTutteViolator,not_lt]
  by_cases h : Y.ncard ≤ 3
  · exact hSmall Y h
  by_cases h' : Y.ncard < t+4
  · exact (hMiddle Y (by omega) h').trans (by omega)
  · exact (hLarge Y (by omega)).trans (by omega)

end OverfullWork.ChenShan
