module

public import OverfullWork.AlternatingLayerSystem

@[expose] public section


/-! # Connect the actual layers to one of the two path closures

Grow from the first endpoint. If its large layer has the wrong parity,
advance a subset of exactly cutoff vertices from the other seed once.
All meeting and predecessor choices follow from finite cardinalities.
-/
namespace OverfullWork.PairedRoutes
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 32000000

structure LayerConnection (τ : Equiv.Perm V) (F : SimpleGraph V) (U : Finset V) (a b : V) (ell : ℕ) where
  layers : ℕ → Finset V
  rounds : ℕ
  round_bound : rounds+2 ≤ ell
  safe : ∀ j, j ≤ rounds → layers j ⊆ U
  predecessors : ∀ j, j < rounds → ∀ z ∈ layers (j+1),
    4+2*rounds < ((layers j).filter (fun x => F.Adj (τ x) z)).card
  start : ∀ x ∈ layers 0, F.Adj a x
  target : V
  target_mem : target ∈ layers rounds
  finish : F.Adj (τ target) b ∨ ∃ T : Finset V, T ⊆ U ∧ (∀ y ∈ T, F.Adj y b) ∧
    2 < (T.filter (fun y => F.Adj (τ y) (τ target))).card

theorem relative_sides (A D B : Finset V) (hD : D=A ∨ D=Aᶜ) (hB : B=A ∨ B=Aᶜ) : D=B ∨ D=Bᶜ := by
  rcases hD with rfl|rfl <;> rcases hB with rfl|rfl <;> simp

theorem exists_layer_connection {τ : Equiv.Perm V} {F : SimpleGraph V} {U A : Finset V}
    {m cutoff g q : ℕ} (s : LayerSystem τ F U A m cutoff g q)
    (hg : 0 < g) (hWindow : 2*cutoff ≤ m) (ell : ℕ)
    (hRounds : m/g+3 ≤ ell) (hReserve : 4+2*ell < q)
    (a b : V) (Da Db Sa T : Finset V) (hDa : Da=A ∨ Da=Aᶜ) (hDb : Db=A ∨ Db=Aᶜ)
    (hSa : Sa ⊆ Da ∩ U) (hT : T ⊆ Db ∩ U) (hLow : cutoff ≤ Sa.card) (hOther : cutoff < T.card)
    (hStart : ∀ x ∈ Sa, F.Adj a x) (hLast : ∀ y ∈ T, F.Adj y b) :
    Nonempty (LayerConnection τ F U a b ell) := by
  obtain ⟨j,hj,hLarge⟩ := s.exists_large Da Sa hDa hSa hLow hg
  have hjBound : j+2 ≤ ell := by omega
  have hSafe : ∀ l, l ≤ j → s.layers Da Sa l ⊆ U := by
    intro l _
    exact (s.layers_subset Da Sa hDa hSa l).trans inter_subset_right
  have hPred : ∀ l, l < j → ∀ z ∈ s.layers Da Sa (l+1),
      4+2*j < ((s.layers Da Sa l).filter (fun x => F.Adj (τ x) z)).card := by
    intro l hl z hz
    have hh := s.layers_predecessors Da Sa hDa hSa l z hz
    omega
  have hSn := s.layers_subset Da Sa hDa hSa j
  have hSide := LayerSystem.side_choice Da hDa j
  have hChoice := relative_sides A (LayerSystem.side Da j) Db hSide hDb
  have hDbCard := s.side_card Db hDb
  rcases hChoice with hSame|hOpp
  · have hSnDb : s.layers Da Sa j ⊆ Db := by
      intro z hz
      have hh := (mem_inter.mp (hSn hz)).1
      rwa [hSame] at hh
    have hTImage : T.image τ ⊆ Db := by
      intro z hz
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
      exact s.mate_mem_side Db hDb y (mem_inter.mp (hT hy)).2 (mem_inter.mp (hT hy)).1
    have hMeet : Db.card < (s.layers Da Sa j).card+T.card := by omega
    obtain ⟨z,hz,hzT⟩ := exists_layered_meeting τ s.involutive Db (s.layers Da Sa j) T hSnDb hTImage hMeet
    exact ⟨{
      layers := s.layers Da Sa, rounds := j, round_bound := hjBound, safe := hSafe,
      predecessors := hPred, start := hStart, target := z, target_mem := hz,
      finish := Or.inl (hLast (τ z) hzT)
    }⟩
  · obtain ⟨Y,hYT,hYCard⟩ := exists_subset_card_eq (show cutoff ≤ T.card by omega)
    have hY : Y ⊆ Db ∩ U := hYT.trans hT
    let T₁ := s.advance Db Y
    have hT₁ : T₁ ⊆ Dbᶜ ∩ U := s.subset Db hDb Y hY
    have hGrow : cutoff+g ≤ T₁.card := by
      have hh := s.growth Db hDb Y hY (by omega) (by omega)
      rwa [hYCard] at hh
    have hDbCompl : Dbᶜ=A ∨ Dbᶜ=Aᶜ := by
      rcases hDb with hDb|hDb
      · exact Or.inr (by rw [hDb])
      · exact Or.inl (by rw [hDb,compl_compl])
    have hSnDb : s.layers Da Sa j ⊆ Dbᶜ := by
      intro z hz
      have hh := (mem_inter.mp (hSn hz)).1
      rwa [hOpp] at hh
    have hTImage : T₁.image τ ⊆ Dbᶜ := by
      intro z hz
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
      exact s.mate_mem_side Dbᶜ hDbCompl y (mem_inter.mp (hT₁ hy)).2 (mem_inter.mp (hT₁ hy)).1
    have hMeet : Dbᶜ.card < (s.layers Da Sa j).card+T₁.card := by
      have hh := s.side_card Dbᶜ hDbCompl
      omega
    obtain ⟨z,hz,hzT⟩ := exists_layered_meeting τ s.involutive Dbᶜ (s.layers Da Sa j) T₁ hSnDb hTImage hMeet
    have hTail : 2 < (T.filter (fun y => F.Adj (τ y) (τ z))).card := by
      have hh := s.predecessors Db hDb Y hY (τ z) hzT
      have hMono : (Y.filter (fun y => F.Adj (τ y) (τ z))).card ≤
          (T.filter (fun y => F.Adj (τ y) (τ z))).card := by
        apply card_le_card
        intro y hy
        exact mem_filter.mpr ⟨hYT (mem_filter.mp hy).1,(mem_filter.mp hy).2⟩
      omega
    exact ⟨{
      layers := s.layers Da Sa, rounds := j, round_bound := hjBound, safe := hSafe,
      predecessors := hPred, start := hStart, target := z, target_mem := hz,
      finish := Or.inr ⟨T,hT.trans inter_subset_right,hLast,hTail⟩
    }⟩

end OverfullWork.PairedRoutes
