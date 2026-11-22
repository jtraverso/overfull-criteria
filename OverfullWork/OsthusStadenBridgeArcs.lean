module

public import OverfullWork.OsthusStadenBridgeCells

@[expose] public section


/-! Add the two disjoint reserve stars at each of the bridge vertices
in Osthus–Staden §5.5. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- A bridge receives arcs from its incoming half and sends arcs to its
outgoing half. -/
def bridgeArcs {V : Type*} (x : V) (incoming outgoing : Finset V) : Digraph V :=
  ⟨fun u v => (u ∈ incoming ∧ v = x) ∨ (u = x ∧ v ∈ outgoing)⟩

/-- A strict reserve margin allows one removal from each red half
before choosing the exact `κ` arcs in each direction. -/
theorem exists_bridge_arcs {V : Type*} [Fintype V]
    (HIn HOut : Digraph V) (x : V) (A B : Finset V) (κ : ℕ)
    (removeA removeB : V)
    (hIn : (κ : ℝ) < profileCount A (inProfile HIn x))
    (hOut : (κ : ℝ) < profileCount B (outProfile HOut x)) :
    ∃ incoming outgoing : Finset V,
      incoming ⊆ A.erase removeA ∧ outgoing ⊆ B.erase removeB ∧
      incoming.card = κ ∧ outgoing.card = κ ∧
      (∀ u ∈ incoming, HIn.Adj u x) ∧ (∀ v ∈ outgoing, HOut.Adj x v) ∧
      bridgeArcs x incoming outgoing ≤ HIn ⊔ HOut := by
  let Ain := A ∩ inProfile HIn x
  let Bout := B ∩ outProfile HOut x
  have hA : κ ≤ (Ain.erase removeA).card := by
    have h : κ < Ain.card := by
      change (κ : ℝ) < (Ain.card : ℝ) at hIn
      exact_mod_cast hIn
    have he := pred_card_le_card_erase (s := Ain) (a := removeA)
    omega
  have hB : κ ≤ (Bout.erase removeB).card := by
    have h : κ < Bout.card := by
      change (κ : ℝ) < (Bout.card : ℝ) at hOut
      exact_mod_cast hOut
    have he := pred_card_le_card_erase (s := Bout) (a := removeB)
    omega
  obtain ⟨incoming,hi,hiCard⟩ := exists_subset_card_eq hA
  obtain ⟨outgoing,ho,hoCard⟩ := exists_subset_card_eq hB
  have h_i (u : V) (hu : u ∈ incoming) : u ∈ A.erase removeA ∧ HIn.Adj u x := by
    have h := mem_erase.mp (hi hu)
    obtain ⟨hA,hH⟩ := mem_inter.mp h.2
    exact ⟨mem_erase.mpr ⟨h.1,hA⟩,(mem_filter.mp hH).2⟩
  have h_o (v : V) (hv : v ∈ outgoing) : v ∈ B.erase removeB ∧ HOut.Adj x v := by
    have h := mem_erase.mp (ho hv)
    obtain ⟨hB,hH⟩ := mem_inter.mp h.2
    exact ⟨mem_erase.mpr ⟨h.1,hB⟩,(mem_filter.mp hH).2⟩
  refine ⟨incoming,outgoing,fun _ hu => (h_i _ hu).1,fun _ hv => (h_o _ hv).1,hiCard,hoCard,
    fun u hu => (h_i u hu).2,fun v hv => (h_o v hv).2,?_⟩
  rintro u v (⟨hu,rfl⟩ | ⟨rfl,hv⟩)
  · exact Or.inl (h_i u hu).2
  · exact Or.inr (h_o v hv).2

/-- A common arc could only come from bridge stars of different
directions. Disjoint reserves exclude that case. -/
theorem disjoint_bridge_arcs {V : Type*} (HIn HOut : Digraph V) {x y : V}
    (A B C E : Finset V) (hxy : x ≠ y) (hDis : Disjoint HIn HOut)
    (hA : ∀ u ∈ A, HIn.Adj u x) (hB : ∀ v ∈ B, HOut.Adj x v)
    (hC : ∀ u ∈ C, HIn.Adj u y) (hE : ∀ v ∈ E, HOut.Adj y v) :
    Disjoint (bridgeArcs x A B) (bridgeArcs y C E) := by
  rw [disjoint_iff_inf_le]
  intro u v h
  rcases h with ⟨(⟨hAx,hvx⟩ | ⟨hux,hBx⟩),(⟨hCy,hvy⟩ | ⟨huy,hEy⟩)⟩
  · exact hxy (hvx.symm.trans hvy)
  · subst v
    subst u
    exact (disjoint_iff_inf_le.mp hDis) ⟨hA y hAx,hE x hEy⟩
  · subst u
    subst v
    exact (disjoint_iff_inf_le.mp hDis) ⟨hC x hCy,hB y hBx⟩
  · exact hxy (hux.symm.trans huy)

end OverfullWork.DirectedRobustExpansion
