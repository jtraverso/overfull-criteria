module

public import OverfullWork.MultigraphCuts

@[expose] public section


/-!
# Exact preservation of overfull obstructions by the saturated point extension

The proof uses regularity and complement symmetry of odd cuts. Neither
a density hypothesis nor a degree-gap hypothesis is needed for preservation.
-/

namespace OverfullWork.MultigraphExtension

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def oldVertices (S : Finset (Option V)) : Finset V :=
  univ.filter (fun v => some v ∈ S)

theorem image_oldVertices_eq (S : Finset (Option V)) (hnone : none ∉ S) :
    (oldVertices S).image some = S := by
  ext w
  cases w <;> simp [oldVertices, hnone]

/-- For a regular even-order multigraph with a distinguished new point,
it suffices to check odd subsets of the original vertices. -/
theorem noOddOverfull_of_old_sets (M : MultiGraph (Option V)) {D : ℕ}
    (hreg : M.IsRegularOfDegree D) (heven : Even (Fintype.card (Option V)))
    (hbound : ∀ T : Finset V, Odd T.card →
      M.twiceInternal (T.image some) ≤ D * (T.card - 1)) : M.NoOddOverfull D := by
  have hold (S : Finset (Option V)) (hodd : Odd S.card) (hnone : none ∉ S) :
      M.twiceInternal S ≤ D * (S.card - 1) := by
    let T := oldVertices S
    have hi : T.image some = S := image_oldVertices_eq S hnone
    have hcard : T.card = S.card := by
      have h := congrArg Finset.card hi
      rwa [card_image_of_injective T (Option.some_injective V)] at h
    have hb := hbound T (by rwa [hcard])
    rwa [hi, hcard] at hb
  intro S hodd
  by_cases hnone : none ∈ S
  · have hodd' := MultiGraph.odd_card_compl heven hodd
    have hnone' : none ∉ Sᶜ := by simpa using hnone
    have hb := hold Sᶜ hodd' hnone'
    by_contra h
    have hc := (M.complementary_odd_overfull_iff hreg heven S hodd).mp (Nat.lt_of_not_ge h)
    omega
  · exact hold S hodd hnone

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem twiceInternal_image (T : Finset V) :
    (pointExtension G).twiceInternal (T.image some) = 2 * Plantholt.eIn G T := by
  rw [MultiGraph.twiceInternal, sum_image (fun a _ b _ h => Option.some.inj h)]
  simp_rw [sum_image (fun a _ b _ h => Option.some.inj h), preserves_original]
  rw [Plantholt.two_mul_eIn]
  apply sum_congr rfl
  intro u hu
  have hfin : T.filter (G.Adj u) = Plantholt.nbIn G T u := by
    ext v
    simp [Plantholt.nbIn, and_comm]
  calc
    _ = (T.filter (G.Adj u)).card := by simp
    _ = _ := congrArg Finset.card hfin

theorem eIn_eq_edge_filter (T : Finset V) :
    Plantholt.eIn G T = (G.edgeFinset.filter (fun e => e.toFinset ⊆ T)).card := by
  unfold Plantholt.eIn
  congr 1
  ext e
  induction e using Sym2.inductionOn with
  | hf u v =>
    simp [mem_edgeFinset, mem_edgeSet, Plantholt.inside_adj, Sym2.toFinset_mk_eq,
      insert_subset_iff, singleton_subset_iff]

theorem edgesWithin_image (T : Finset V) :
    (pointExtension G).edgesWithin (T.image some) = Plantholt.eIn G T := by
  have h := twiceInternal_image G T
  rw [MultiGraph.twiceInternal_eq] at h
  omega

theorem hasOverfull_of_simple (h : G.HasOverfullSubgraph) :
    (pointExtension G).HasOverfullSubset G.maxDegree := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.image some, ?_⟩
  rw [card_image_of_injective T (Option.some_injective V), edgesWithin_image, eIn_eq_edge_filter]
  exact hT

theorem odd_bound_image_of_no_overfull (hno : ¬ G.HasOverfullSubgraph)
    (T : Finset V) (hodd : Odd T.card) :
    (pointExtension G).twiceInternal (T.image some) ≤ G.maxDegree * (T.card - 1) := by
  have hb : Plantholt.eIn G T ≤ G.maxDegree * (T.card / 2) := by
    by_contra h
    apply hno
    refine ⟨T, ?_⟩
    rw [← eIn_eq_edge_filter]
    exact Nat.lt_of_not_ge h
  rw [twiceInternal_image]
  obtain ⟨m, hm⟩ := hodd
  have hh : T.card / 2 = m := by omega
  have hp : G.maxDegree * (T.card - 1) = 2 * (G.maxDegree * m) := by
    rw [hm]
    have hsub : 2 * m + 1 - 1 = 2 * m := by omega
    rw [hsub]
    ring
  rw [hh] at hb
  rw [hp]
  omega

theorem no_overfull_pointExtension_iff
    (hn : Odd (Fintype.card V))
    (hsat : 2 * G.edgeFinset.card = G.maxDegree * (Fintype.card V - 1)) :
    (¬ (pointExtension G).HasOverfullSubset G.maxDegree) ↔ ¬ G.HasOverfullSubgraph := by
  constructor
  · intro h hG
    exact h (hasOverfull_of_simple G hG)
  · intro hG
    have hnpos : 1 ≤ Fintype.card V := by obtain ⟨m, hm⟩ := hn; omega
    have hreg := regular_of_saturated G hnpos hsat
    apply ((pointExtension G).noOverfull_iff_odd_bounds G.maxDegree
      (fun v => (hreg v).le)).mpr
    exact noOddOverfull_of_old_sets (pointExtension G) hreg (even_order hn)
      (odd_bound_image_of_no_overfull G hG)

theorem has_overfull_pointExtension_iff
    (hn : Odd (Fintype.card V))
    (hsat : 2 * G.edgeFinset.card = G.maxDegree * (Fintype.card V - 1)) :
    (pointExtension G).HasOverfullSubset G.maxDegree ↔ G.HasOverfullSubgraph := by
  classical
  have h := not_congr (no_overfull_pointExtension_iff G hn hsat)
  simpa only [not_not] using h

/-- This upgrades the existence theorem by proving all odd-set bounds.
It still does not supply a factorization or a colouring of M. -/
theorem exists_noOverfull_extension
    (hn : Odd (Fintype.card V)) (hgap : G.maxDegree - G.minDegree ≤ 2)
    (hsat : 2 * G.edgeFinset.card = G.maxDegree * (Fintype.card V - 1))
    (hno : ¬ G.HasOverfullSubgraph) :
    ∃ M : MultiGraph (Option V), M.IsRegularOfDegree G.maxDegree ∧
      (∀ e, M.mult e ≤ 2) ∧
      (∀ u v, G.Adj u v → 1 ≤ M.mult s(some u, some v)) ∧
      ¬ M.HasOverfullSubset G.maxDegree := by
  have hnpos : 1 ≤ Fintype.card V := by obtain ⟨m, hm⟩ := hn; omega
  exact ⟨pointExtension G, regular_of_saturated G hnpos hsat,
    multiplicity_le_two G hgap, contains_original G,
    (no_overfull_pointExtension_iff G hn hsat).mpr hno⟩

#print axioms no_overfull_pointExtension_iff
#print axioms exists_noOverfull_extension

end OverfullWork.MultigraphExtension
