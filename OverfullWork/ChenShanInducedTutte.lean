module

public import OverfullWork.ChenShanReserveTutte

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph
open scoped Classical

variable {V U : Type*}

theorem odd_component_count_eq_of_iso {G : SimpleGraph V} {H : SimpleGraph U}
    (φ : G ≃g H) : G.oddComponents.ncard = H.oddComponents.ncard := by
  let F := φ.connectedComponentEquiv
  have hMem (c : G.ConnectedComponent) (v : V) : v ∈ c.supp ↔ φ v ∈ (F c).supp :=
    ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp.symm
  have hSize (c : G.ConnectedComponent) : c.supp.ncard = (F c).supp.ncard := by
    let e : c.supp ≃ (F c).supp :=
      { toFun := fun v => ⟨φ v.val,(hMem c v.val).mp v.property⟩
        invFun := fun v => ⟨φ.symm v.val,(hMem c _).mpr (by simp [v.property])⟩
        left_inv := fun v => Subtype.ext (φ.symm_apply_apply v.val)
        right_inv := fun v => Subtype.ext (φ.apply_symm_apply v.val) }
    exact Nat.card_congr e
  have hOdd (c) : c ∈ G.oddComponents ↔ F c ∈ H.oddComponents := by
    change Odd c.supp.ncard ↔ Odd (F c).supp.ncard
    rw [hSize]
  exact Nat.card_congr
    { toFun := fun c => ⟨F c.val,(hOdd c.val).mp c.property⟩
      invFun := fun c => ⟨F.symm c.val,(hOdd _).mpr (by simp [c.property])⟩
      left_inv := fun c => Subtype.ext (F.symm_apply_apply c.val)
      right_inv := fun c => Subtype.ext (F.apply_symm_apply c.val) }

/-- Tutte's criterion in the induced-complement form used in the paper. -/
theorem tutte_induce_complement [Finite V] (G : SimpleGraph V) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ↔
      ∀ Y : Set V, (G.induce Yᶜ).oddComponents.ncard ≤ Y.ncard := by
  rw [SimpleGraph.tutte]
  apply forall_congr'
  intro Y
  rw [SimpleGraph.IsTutteViolator,not_lt]
  have h : (⊤ : G.Subgraph).deleteVerts Y = (⊤ : G.Subgraph).induce Yᶜ := by
    have hSet : Set.univ \ Y = Yᶜ := by ext; simp
    simp only [Subgraph.deleteVerts,Subgraph.verts_top,hSet]
  rw [h,← SimpleGraph.induce_eq_coe_induce_top]; rfl

/-- In the small range, removal of an intact matching preserves the
parity of every surviving component when the reserve prevents splitting. -/
theorem odd_components_after_induced_matching_deletion_le [Finite V] {G : SimpleGraph V}
    {N : G.Subgraph} (hN : N.IsMatching) (Y : Set V) (hDis : Disjoint N.verts Y)
    (hReach : ∀ x y : ↥((Y ∪ N.verts)ᶜ),
      (G.induce Yᶜ).Reachable ⟨x.val,fun hy => x.property (Or.inl hy)⟩
        ⟨y.val,fun hy => y.property (Or.inl hy)⟩ →
      (G.induce (Y ∪ N.verts)ᶜ).Reachable x y) :
    (G.induce (Y ∪ N.verts)ᶜ).oddComponents.ncard ≤ (G.induce Yᶜ).oddComponents.ncard := by
  let H := G.induce Yᶜ
  let φ : H →g G := (Embedding.induce (G := G) Yᶜ).toHom
  let M := N.comap φ
  have hM : M.IsMatching := by
    intro v hv
    obtain ⟨w,hw,hUnique⟩ := hN hv
    have hwY : w ∈ Yᶜ := fun hY => Set.disjoint_left.mp hDis hw.snd_mem hY
    refine ⟨⟨w,hwY⟩,⟨N.adj_sub hw,hw⟩,?_⟩
    intro w' hw'
    exact Subtype.ext (hUnique w'.val hw'.2)
  let R := G.induce (Y ∪ N.verts)ᶜ
  let e : R ≃g H.induce M.vertsᶜ :=
    { toFun := fun v => ⟨⟨v.val,fun hy => v.property (Or.inl hy)⟩,
            fun hn => v.property (Or.inr hn)⟩
      invFun := fun v => ⟨v.val.val,fun h => h.elim v.val.property v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  let _ := Fintype.ofFinite ↥(Yᶜ : Set V)
  rw [odd_component_count_eq_of_iso e]
  apply odd_components_induce_le_of_matching hM
  intro v w hvw
  have h := hReach (e.symm v) (e.symm w) hvw
  exact e.reachable_iff.mpr h

end OverfullWork.ChenShan
