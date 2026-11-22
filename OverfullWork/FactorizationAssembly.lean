module

public import OverfullWork.BipartiteFactorization
public import OverfullWork.MultigraphColouring
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section


/-!
# Completing a coloured regular subgraph with a bipartite residual

The residual engine is unconditional Kőnig factorization. The remaining
structural obligation is to construct the coloured regular internal cover;
this file neither assumes nor proves that every dense graph has such a cover.
-/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def addCopies (M N : MultiGraph V) : MultiGraph V where
  mult e := M.mult e + N.mult e
  loopless e he := by rw [M.loopless e he, N.loopless e he]

def subtractCopies (M H : MultiGraph V) : MultiGraph V where
  mult e := M.mult e - H.mult e
  loopless e he := by rw [M.loopless e he, H.loopless e he]

omit [Fintype V] [DecidableEq V] in
theorem ext_mult {M N : MultiGraph V} (h : ∀ e, M.mult e = N.mult e) : M = N := by
  cases M
  cases N
  congr
  exact funext h

omit [Fintype V] [DecidableEq V] in
theorem add_subtract_of_le (M H : MultiGraph V) (hsub : ∀ e, H.mult e ≤ M.mult e) :
    H.addCopies (M.subtractCopies H) = M := by
  apply ext_mult
  intro e
  exact Nat.add_sub_of_le (hsub e)

theorem degree_subtract_add (M H : MultiGraph V) (hsub : ∀ e, H.mult e ≤ M.mult e) (v : V) :
    (M.subtractCopies H).degree v + H.degree v = M.degree v := by
  simp only [degree, subtractCopies]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro e he
  exact Nat.sub_add_cancel (hsub e)

theorem regular_subtract (M H : MultiGraph V) {D k : ℕ}
    (hsub : ∀ e, H.mult e ≤ M.mult e)
    (hM : M.IsRegularOfDegree D) (hH : H.IsRegularOfDegree k) :
    (M.subtractCopies H).IsRegularOfDegree (D - k) := by
  intro v
  have h := degree_subtract_add M H hsub v
  rw [hM v, hH v] at h
  omega

def EdgeColoring.addCopies {M N : MultiGraph V} {k l : ℕ}
    (C : M.EdgeColoring k) (F : N.EdgeColoring l) : (M.addCopies N).EdgeColoring (k + l) where
  col e := Fin.addCases (C.col e) (F.col e)
  sum_col e := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, C.sum_col, F.sum_col]
    rfl
  proper v i := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [Fin.addCases_left] using C.proper v j
    · intro j
      simpa only [Fin.addCases_right] using F.proper v j

/-- Assemble a coloured k-regular subgraph with a bipartite (D-k)-regular
residual. This is a proved reduction; existence of H remains explicit. -/
theorem exists_factorization_of_bipartite_residual
    (M H : MultiGraph V) (L : Finset V) (D k : ℕ) (hk : k ≤ D)
    (hsub : ∀ e, H.mult e ≤ M.mult e)
    (hM : M.IsRegularOfDegree D) (hH : H.IsRegularOfDegree k)
    (hcol : Nonempty (H.EdgeColoring k)) (hB : (M.subtractCopies H).IsBipartiteOn L) :
    ∃ C : M.EdgeColoring D, C.IsFactorization := by
  obtain ⟨C⟩ := hcol
  obtain ⟨F, hF⟩ := exists_factorization_of_bipartite (M.subtractCopies H) L (D - k)
    hB (regular_subtract M H hsub hM hH)
  have hsum : Nonempty ((H.addCopies (M.subtractCopies H)).EdgeColoring (k + (D - k))) :=
    ⟨C.addCopies F⟩
  rw [add_subtract_of_le M H hsub, Nat.add_sub_of_le hk] at hsum
  obtain ⟨T⟩ := hsum
  exact ⟨T, T.isFactorization_of_regular hM⟩

omit [Fintype V] [DecidableEq V] in
/-- If H includes every internal copy on both sides of L, its residual is
bipartite. Crossing copies may be used to complete H's colour classes. -/
theorem bipartite_residual_of_internal_cover (M H : MultiGraph V) (L : Finset V)
    (hcover : ∀ u v, (u ∈ L ↔ v ∈ L) → H.mult s(u,v) = M.mult s(u,v)) :
    (M.subtractCopies H).IsBipartiteOn L := by
  intro u v huv
  change M.mult s(u,v) - H.mult s(u,v) = 0
  rw [hcover u v huv, Nat.sub_self]

/-- A proper internal-cover criterion: k<D, so the premise does not simply
give a full colouring of M. The construction of such H is the remaining
partition-and-recolouring problem in the dense factorization argument. -/
theorem exists_factorization_of_internal_cover
    (M H : MultiGraph V) (L : Finset V) (D k : ℕ) (hk : k < D)
    (hsub : ∀ e, H.mult e ≤ M.mult e)
    (hM : M.IsRegularOfDegree D) (hH : H.IsRegularOfDegree k)
    (hcol : Nonempty (H.EdgeColoring k))
    (hcover : ∀ u v, (u ∈ L ↔ v ∈ L) → H.mult s(u,v) = M.mult s(u,v)) :
    ∃ C : M.EdgeColoring D, C.IsFactorization :=
  exists_factorization_of_bipartite_residual M H L D k hk.le hsub hM hH hcol
    (bipartite_residual_of_internal_cover M H L hcover)

#print axioms exists_factorization_of_bipartite_residual
#print axioms exists_factorization_of_internal_cover

end SimpleGraph.MultiGraph

namespace OverfullWork.MultigraphExtension

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Concrete reduction for the original graph: construct a proper coloured
regular internal cover in its point extension, then use the bipartite
residual engine. Existence of that cover is not claimed here. -/
theorem edgeColourable_of_internal_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : MultiGraph (Option V)) (L : Finset (Option V)) (k : ℕ)
    (hn : 1 ≤ Fintype.card V)
    (hsat : 2 * G.edgeFinset.card = G.maxDegree * (Fintype.card V - 1))
    (hk : k < G.maxDegree)
    (hsub : ∀ e, H.mult e ≤ (pointExtension G).mult e)
    (hH : H.IsRegularOfDegree k) (hcol : Nonempty (H.EdgeColoring k))
    (hcover : ∀ u v, (u ∈ L ↔ v ∈ L) → H.mult s(u,v) = (pointExtension G).mult s(u,v)) :
    G.EdgeColorable G.maxDegree := by
  obtain ⟨C, hC⟩ := MultiGraph.exists_factorization_of_internal_cover (pointExtension G) H L
    G.maxDegree k hk hsub (regular_of_saturated G hn hsat) hH hcol hcover
  exact edgeColourable_of_extension_colouring G C

#print axioms edgeColourable_of_internal_cover

end OverfullWork.MultigraphExtension
