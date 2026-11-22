module

public import OverfullWork.CentreSaturation
public import OverfullWork.PerturbationAccounting
public import OverfullWork.ResidueColouring

@[expose] public section


/-! # Color resources for CMS's protected Initial Stage

Restrict a color to copies incident with a selected vertex set. Count
the actual colors used on a protected set, so the triangle inequality
supplies an unused color in the current coloring, not an oracle.
-/
namespace SimpleGraph.MultiGraph
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 12000000

def incidentOn (M : MultiGraph V) (S : Finset V) : MultiGraph V where
  mult e := if ∃ v ∈ S, v ∈ e then M.mult e else 0
  loopless e he := by rw [M.loopless e he];simp

theorem incidentOn_le (M : MultiGraph V) (S : Finset V) (e : Sym2 V) :
    (M.incidentOn S).mult e ≤ M.mult e := by
  dsimp only [incidentOn]
  split_ifs <;> omega

theorem subtract_incidentOn_degree_zero (M : MultiGraph V) (S : Finset V) (v : V) (hv : v ∈ S) :
    (M.subtractCopies (M.incidentOn S)).degree v=0 := by
  apply sum_eq_zero
  intro e he
  change M.mult e-(if ∃ w ∈ S, w ∈ e then M.mult e else 0)=0
  rw [if_pos ⟨v,hv,(mem_filter.mp he).2⟩,Nat.sub_self]

theorem incidentOn_edgeCount_le (M : MultiGraph V) (S : Finset V) :
    (M.incidentOn S).edgeCount ≤ ∑ v ∈ S, M.degree v := by
  have hp : ∀ e : Sym2 V, (M.incidentOn S).mult e ≤ ∑ v ∈ S, if v ∈ e then M.mult e else 0 := by
    intro e
    by_cases he : ∃ v ∈ S, v ∈ e
    · obtain ⟨v,hv,hve⟩ := he
      change (if ∃ w ∈ S, w ∈ e then M.mult e else 0) ≤ _
      rw [if_pos ⟨v,hv,hve⟩]
      have hh := single_le_sum (f := fun w => if w ∈ e then M.mult e else 0)
        (fun _ _ => Nat.zero_le _) hv
      simpa only [if_pos hve] using hh
    · change (if ∃ w ∈ S, w ∈ e then M.mult e else 0) ≤ _
      rw [if_neg he];exact Nat.zero_le _
  calc
    _ ≤ ∑ e : Sym2 V, ∑ v ∈ S, if v ∈ e then M.mult e else 0 := sum_le_sum (fun e _ => hp e)
    _ = ∑ v ∈ S, ∑ e : Sym2 V, if v ∈ e then M.mult e else 0 := sum_comm
    _ = _ := sum_congr rfl (fun v _ => (M.degree_eq_sum_ite v).symm)

theorem incidentOn_degree_zero_away (M : MultiGraph V) (S : Finset V) (a : V) (ha : a ∉ S)
    (hz : ∀ v ∈ S, M.mult s(a,v)=0) : (M.incidentOn S).degree a=0 := by
  rw [degree_eq_sum_mult]
  apply sum_eq_zero
  intro v _
  change (if ∃ w ∈ S, w ∈ s(a,v) then M.mult s(a,v) else 0)=0
  split_ifs with h
  · obtain ⟨w,hw,hwe⟩ := h
    rcases Sym2.mem_iff.mp hwe with hwa|hwv
    · exact False.elim (ha (hwa ▸ hw))
    · exact hz v (hwv ▸ hw)
  · rfl

theorem triangle_zero_of_centre_and_pair (M : MultiGraph V) (a b w : V)
    (ha : M.degree a=0) (hbw : M.mult s(b,w)=0) (e : Sym2 V) (he : e.toFinset ⊆ ({a,b,w}:Finset V)) :
    M.mult e=0 := by
  induction e using Sym2.inductionOn with
  | hf x y =>
    have hx : x ∈ ({a,b,w}:Finset V) := he (by simp)
    have hy : y ∈ ({a,b,w}:Finset V) := he (by simp)
    simp only [mem_insert,mem_singleton] at hx hy
    rcases hx with hxa|hxb|hxw
    · subst x;exact M.mult_eq_zero_of_degree_zero a y ha
    · subst x
      rcases hy with hya|hyb|hyw
      · subst y;rw [Sym2.eq_swap];exact M.mult_eq_zero_of_degree_zero a b ha
      · subst y;exact M.loopless _ (by simp)
      · subst y;exact hbw
    · subst x
      rcases hy with hya|hyb|hyw
      · subst y;rw [Sym2.eq_swap];exact M.mult_eq_zero_of_degree_zero a w ha
      · subst y;rw [Sym2.eq_swap];exact hbw
      · subst y;exact M.loopless _ (by simp)

theorem unitEdge_zero_of_not_mem (a u : V) (hau : a ≠ u) (e : Sym2 V) (ha : a ∉ e) :
    (unitEdge a u hau).mult e=0 := by
  apply if_neg
  intro he
  exact ha (he ▸ (by simp : a ∈ s(a,u)))

namespace EdgeColoring
variable {M : MultiGraph V} {k : ℕ}

def usedOn (C : M.EdgeColoring k) (S : Finset V) : Finset (Fin k) :=
  univ.filter (fun i => 0 < (C.colourGraph i).edgesWithin S)

theorem usedOn_card_le (C : M.EdgeColoring k) (S : Finset V) : (C.usedOn S).card ≤ M.edgesWithin S := by
  rw [usedOn,card_eq_sum_ones,sum_filter,←C.sum_edgesWithin S]
  apply sum_le_sum
  intro i _
  split_ifs <;> omega

theorem unusedOn_copies_zero (C : M.EdgeColoring k) (S : Finset V) (i : Fin k)
    (hi : i ∉ C.usedOn S) (e : Sym2 V) (he : e.toFinset ⊆ S) : C.col e i=0 := by
  have hz : (C.colourGraph i).edgesWithin S=0 := by
    have hh : ¬0 < (C.colourGraph i).edgesWithin S := fun h => hi (mem_filter.mpr ⟨mem_univ _,h⟩)
    omega
  have hh := single_le_sum (s := (univ : Finset (Sym2 V)))
    (f := fun t => if t.toFinset ⊆ S then C.col t i else 0) (fun _ _ => Nat.zero_le _) (mem_univ e)
  rw [if_pos he] at hh
  change C.col e i ≤ (C.colourGraph i).edgesWithin S at hh
  omega

end EdgeColoring
namespace PartialColouring
variable {M : MultiGraph V} {k : ℕ}

theorem exchange_bundle_balance (P : M.PartialColouring k) (i : Fin k) (R A : MultiGraph V)
    (hR : ∀ e, R.mult e ≤ P.colouring.col e i) (hA : ∀ e, A.mult e ≤ P.available.mult e)
    (hp : ∀ v, ((P.colouring.colourGraph i).subtractCopies R).degree v+A.degree v ≤ 1) (e : Sym2 V) :
    (P.exchange i R A hR hA hp).graph.mult e+R.mult e=P.graph.mult e+A.mult e := by
  have hr := (hR e).trans (P.colouring.col_le_mult e i)
  change P.graph.mult e-R.mult e+A.mult e+R.mult e=P.graph.mult e+A.mult e
  omega

theorem exchange_mass_identity (P : M.PartialColouring k) (i : Fin k) (R A : MultiGraph V)
    (hR : ∀ e, R.mult e ≤ P.colouring.col e i) (hA : ∀ e, A.mult e ≤ P.available.mult e)
    (hp : ∀ v, ((P.colouring.colourGraph i).subtractCopies R).degree v+A.degree v ≤ 1) :
    (P.exchange i R A hR hA hp).colouring.colourMass i+R.edgeCount=P.colouring.colourMass i+A.edgeCount := by
  rw [EdgeColoring.colourMass,P.exchange_colour_selected i R A hR hA hp,edgeCount_addCopies]
  have hd : ((P.colouring.colourGraph i).subtractCopies R).edgeCount+R.edgeCount=
      (P.colouring.colourGraph i).edgeCount := by
    change (∑ e, (P.colouring.col e i-R.mult e))+(∑ e, R.mult e)=_
    rw [←sum_add_distrib]
    exact sum_congr rfl (fun e _ => Nat.sub_add_cancel (hR e))
  change _ = (P.colouring.colourGraph i).edgeCount+A.edgeCount
  omega

theorem matching_after_incidentOn_clear (L : MultiGraph V) (S : Finset V) (hL : ∀ v, L.degree v ≤ 1)
    (a u : V) (hau : a ≠ u) (ha : L.degree a=0 ∨ a ∈ S) (hu : L.degree u=0 ∨ u ∈ S) :
    ∀ v, (L.subtractCopies (L.incidentOn S)).degree v+(unitEdge a u hau).degree v ≤ 1 := by
  intro v
  have hs := degree_subtract_add L (L.incidentOn S) (L.incidentOn_le S) v
  have hv := hL v
  rw [degree_unitEdge]
  by_cases hva : v=a
  · subst v;rw [if_pos (Or.inl rfl)]
    rcases ha with ha|ha
    · omega
    · rw [subtract_incidentOn_degree_zero L S a ha]
  by_cases hvu : v=u
  · subst v;rw [if_pos (Or.inr rfl)]
    rcases hu with hu|hu
    · omega
    · rw [subtract_incidentOn_degree_zero L S u hu]
  · rw [if_neg (by simp [hva,hvu])];omega

theorem exists_unused_triangle_colour (P : M.PartialColouring k) (a b w : V)
    (hTri : P.graph.edgesWithin {a,b,w} ≤ P.graph.degree a)
    (hMissing : 0 < (P.colouring.missingPalette a).card) :
    ∃ α : Fin k, α ∉ P.colouring.usedOn {a,b,w} := by
  have hCount := P.colouring.usedOn_card_le {a,b,w}
  have hDegree := P.colouring.missingPalette_card_add_degree a
  have hCard : (P.colouring.usedOn {a,b,w}).card < k := by omega
  have hh : (univ\P.colouring.usedOn {a,b,w}).Nonempty := by
    apply card_pos.mp
    rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin]
    omega
  obtain ⟨α,hα⟩ := hh
  exact ⟨α,(mem_sdiff.mp hα).2⟩

end PartialColouring
end SimpleGraph.MultiGraph
