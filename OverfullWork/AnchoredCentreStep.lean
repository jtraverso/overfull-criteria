module

public import OverfullWork.ProtectedCentreRun
public import OverfullWork.AvailableNeighbours

@[expose] public section


/-! # CMS second-anchor recoloring without disturbing the first center

Two available neighbors suffice: the selected matching color meets the
first center through at most one of them. The chosen exchange therefore
discards no copy at either center. The neighbor reserve is counted in
the simple support, independently of parallel multiplicities.
-/
namespace SimpleGraph.MultiGraph.PartialColouring
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}
set_option maxHeartbeats 16000000

def ordinaryFree (P : M.PartialColouring k) (A : Finset V) (a b : V) : Finset V :=
  P.available.neighboursInto (A.erase a) b

structure AnchoredStep (P Q : M.PartialColouring k) (A : Finset V) (a b : V) where
  step : CentreStep P Q b
  neighbour_mem : step.neighbour ∈ A.erase a
  anchor_free : step.removed.degree a=0

theorem exists_safe_ordinary_neighbour (P : M.PartialColouring k) (A : Finset V) (a b : V)
    (i : Fin k) (hRoom : 2 ≤ (P.ordinaryFree A a b).card) :
    ∃ u ∈ P.ordinaryFree A a b, P.colouring.col s(a,u) i=0 := by
  let S := P.ordinaryFree A a b
  let Bad := S.filter (fun u => 0 < P.colouring.col s(a,u) i)
  have hBad : Bad.card ≤ 1 := by
    have hh : Bad.card ≤ (P.colouring.colourGraph i).degree a := by
      rw [degree_eq_sum_mult]
      calc
        _ = ∑ u ∈ S, if 0 < P.colouring.col s(a,u) i then 1 else 0 := by
          simp only [Bad,card_eq_sum_ones,sum_filter]
        _ ≤ ∑ u ∈ S, (P.colouring.colourGraph i).mult s(a,u) := by
          apply sum_le_sum
          intro u _
          change (if 0 < P.colouring.col s(a,u) i then 1 else 0) ≤ P.colouring.col s(a,u) i
          split_ifs <;> omega
        _ ≤ ∑ u, (P.colouring.colourGraph i).mult s(a,u) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    exact hh.trans (P.colouring.colourGraph_degree_le_one i a)
  have hExists : (S\Bad).Nonempty := by
    apply card_pos.mp
    rw [card_sdiff_of_subset (filter_subset _ _)]
    change 0 < S.card-Bad.card
    change 2 ≤ S.card at hRoom
    omega
  obtain ⟨u,hu⟩ := hExists
  have hs := (mem_sdiff.mp hu).1
  have hz : ¬0 < P.colouring.col s(a,u) i := by
    intro h;exact (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨hs,h⟩)
  exact ⟨u,hs,by omega⟩

theorem exists_anchored_step (P : M.PartialColouring k) (A : Finset V) (a b : V)
    (hb : b ∉ A) (hRoom : 2 ≤ (P.ordinaryFree A a b).card)
    (hMissing : 0 < (P.colouring.missingPalette b).card) :
    ∃ Q, Nonempty (AnchoredStep P Q A a b) := by
  obtain ⟨i,hi⟩ := card_pos.mp hMissing
  have hib : (P.colouring.colourGraph i).degree b=0 := (mem_filter.mp hi).2
  obtain ⟨u,hu,hSafe⟩ := exists_safe_ordinary_neighbour P A a b i hRoom
  have huA : u ∈ A.erase a := (mem_filter.mp hu).1
  have hav : 0 < P.available.mult s(b,u) := (mem_filter.mp hu).2
  have hbu : b ≠ u := by intro he;exact hb (he ▸ (mem_erase.mp huA).2)
  have hau : a ≠ u := (mem_erase.mp huA).1.symm
  let L := P.colouring.colourGraph i
  let R := L.incidentOn {u}
  let E := unitEdge b u hbu
  have hR : ∀ e, R.mult e ≤ P.colouring.col e i := L.incidentOn_le {u}
  have hE : ∀ e, E.mult e ≤ P.available.mult e := unit_available_of_positive P b u hbu hav
  have hp : ∀ v, (L.subtractCopies R).degree v+E.degree v ≤ 1 :=
    matching_after_incidentOn_clear L {u} (P.colouring.colourGraph_degree_le_one i)
      b u hbu (Or.inl hib) (Or.inr (mem_singleton_self u))
  let Q := P.exchange i R E hR hE hp
  have hRb : R.degree b=0 := by
    have hh := L.degree_le_of_mult_le R hR b
    change R.degree b ≤ (P.colouring.colourGraph i).degree b at hh
    omega
  have hRa : R.degree a=0 := by
    apply incidentOn_degree_zero_away L {u} a (by simpa only [mem_singleton] using hau)
    intro v hv
    have hvu : v=u := mem_singleton.mp hv
    subst v
    exact hSafe
  have hCount : R.edgeCount ≤ 1 := by
    have hh := L.incidentOn_edgeCount_le {u}
    simp only [sum_singleton] at hh
    exact hh.trans (P.colouring.colourGraph_degree_le_one i u)
  have hGain : Q.graph.degree b=P.graph.degree b+1 := by
    have hh := P.exchange_degree_identity i R E hR hE hp b
    change Q.graph.degree b+R.degree b=P.graph.degree b+E.degree b at hh
    have he : E.degree b=1 := by simp [E,degree_unitEdge]
    omega
  exact ⟨Q,⟨{
    step := {
      color := i, neighbour := u, distinct := hbu, removed := R,
      removed_le := hR, available := hE, proper := hp, updated := rfl,
      erased_le_one := hCount, centre_free := hRb, centre_gain := hGain
    }
    neighbour_mem := huA
    anchor_free := hRa
  }⟩⟩

theorem AnchoredStep.bundle_balance {P Q : M.PartialColouring k} {A : Finset V} {a b : V}
    (h : AnchoredStep P Q A a b) (e : Sym2 V) :
    Q.graph.mult e+h.step.removed.mult e=P.graph.mult e+
      (unitEdge b h.step.neighbour h.step.distinct).mult e := by
  have hh := P.exchange_bundle_balance h.step.color h.step.removed
    (unitEdge b h.step.neighbour h.step.distinct)
    h.step.removed_le h.step.available h.step.proper e
  have heq := congrArg (fun X : M.PartialColouring k => X.graph.mult e) h.step.updated
  rw [←heq] at hh
  exact hh

theorem AnchoredStep.anchor_bundle {P Q : M.PartialColouring k} {A : Finset V} {a b : V}
    (h : AnchoredStep P Q A a b) (hab : a ≠ b) (v : V) :
    Q.graph.mult s(a,v)=P.graph.mult s(a,v) := by
  have hh := h.bundle_balance s(a,v)
  have hz := h.step.removed.mult_eq_zero_of_degree_zero a v h.anchor_free
  have hau : a ≠ h.step.neighbour := (mem_erase.mp h.neighbour_mem).1.symm
  have ha : a ∉ s(b,h.step.neighbour) := by simp only [Sym2.mem_iff];tauto
  have he : (unitEdge b h.step.neighbour h.step.distinct).mult s(a,v)=0 := by
    apply if_neg
    intro he
    exact ha (he ▸ (by simp : a ∈ s(a,v)))
  omega

theorem AnchoredStep.free_loss_le {P Q : M.PartialColouring k} {A : Finset V} {a b : V}
    (h : AnchoredStep P Q A a b) :
    (P.ordinaryFree A a b).card ≤ (Q.ordinaryFree A a b).card+1 := by
  have hs : P.ordinaryFree A a b ⊆ insert h.step.neighbour (Q.ordinaryFree A a b) := by
    intro v hv
    by_cases hvu : v=h.step.neighbour
    · exact mem_insert.mpr (Or.inl hvu)
    have he : s(b,v) ≠ s(b,h.step.neighbour) := by
      intro he
      rcases Sym2.eq_iff.mp he with hh|hh
      · exact hvu hh.2
      · exact hvu (hh.2.trans hh.1)
    have hbal := h.bundle_balance s(b,v)
    have hz : (unitEdge b h.step.neighbour h.step.distinct).mult s(b,v)=0 := if_neg he
    rw [hz] at hbal
    have hle : Q.graph.mult s(b,v) ≤ P.graph.mult s(b,v) := by omega
    have hmem := mem_filter.mp hv
    have hav : 0 < Q.available.mult s(b,v) := by
      change 0 < M.mult s(b,v)-Q.graph.mult s(b,v)
      have hOld : 0 < M.mult s(b,v)-P.graph.mult s(b,v) := hmem.2
      omega
    exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hmem.1,hav⟩))
  exact (card_le_card hs).trans (card_insert_le _ _)

theorem AnchoredStep.second_bundle {P Q : M.PartialColouring k} {A : Finset V} {a b : V}
    (h : AnchoredStep P Q A a b) (v : V) (hv : v ∉ A) :
    Q.graph.mult s(b,v)=P.graph.mult s(b,v) := by
  have hh := h.bundle_balance s(b,v)
  have hz := h.step.removed.mult_eq_zero_of_degree_zero b v h.step.centre_free
  have hvu : v ≠ h.step.neighbour := by
    intro he;exact hv (he ▸ (mem_erase.mp h.neighbour_mem).2)
  have he : s(b,v) ≠ s(b,h.step.neighbour) := by
    intro he
    rcases Sym2.eq_iff.mp he with he|he
    · exact hvu he.2
    · exact hvu (he.2.trans he.1)
  have hE : (unitEdge b h.step.neighbour h.step.distinct).mult s(b,v)=0 := if_neg he
  omega

theorem AnchoredStep.away_bundle_le {P Q : M.PartialColouring k} {A : Finset V} {a b : V}
    (h : AnchoredStep P Q A a b) (e : Sym2 V) (hb : b ∉ e) :
    Q.graph.mult e ≤ P.graph.mult e := by
  have hh := h.bundle_balance e
  rw [unitEdge_zero_of_not_mem _ _ _ _ hb] at hh
  omega

end SimpleGraph.MultiGraph.PartialColouring
