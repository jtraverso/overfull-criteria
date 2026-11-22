module

public import OverfullWork.SubtypeColouringExtension
public import OverfullWork.HeavyPairResidualFactorization

@[expose] public section


/-! # Reassemble the peeled two-factors and the factorized ordinary residue

The central residual copies extend the ordinary factors with the same
palette. The removed layers then receive a disjoint palette. No final
colouring is assumed by the explicit factorization criterion below.
-/
namespace OverfullWork.HeavyPairPeeling
open SimpleGraph Finset HeavyPairBoundary CanonicalPairTriangle SubtypeColouringExtension Gate8J2I
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

def pairColouring (a b : V) (hab : a ≠ b) (r : ℕ) : (copiesOn a b hab r).EdgeColoring r where
  col t _ := (MultiGraph.unitEdge a b hab).mult t
  sum_col t := by
    change (∑ _i : Fin r, (MultiGraph.unitEdge a b hab).mult t) =
      r * (MultiGraph.unitEdge a b hab).mult t
    simp
  proper v i := by
    change (MultiGraph.unitEdge a b hab).degree v ≤ 1
    rw [MultiGraph.degree_unitEdge]
    split_ifs <;> omega

theorem Certificate.residual_split {M : MultiGraph V} {d q : ℕ} {a b : V}
    (c : Certificate M d q a b) (hab : a ≠ b) (hreg : M.IsRegularOfDegree d)
    (hq : q = d - M.mult s(a,b)) :
    (c.residual.restrict (outside a b)).addCopies (copiesOn a b hab (d-2*q)) = c.residual := by
  have hp := c.residual_pair hreg hq
  have hleft : ∀ w : V, w ≠ b → c.residual.mult s(a,w) = 0 := by
    intro w hwb
    by_cases hwa : w = a
    · subst w; exact c.residual.loopless _ (by simp)
    · exact c.residual_boundary_left ⟨w,(mem_outside a b w).mpr ⟨hwa,hwb⟩⟩
  have hright : ∀ w : V, w ≠ a → c.residual.mult s(b,w) = 0 := by
    intro w hwa
    by_cases hwb : w = b
    · subst w; exact c.residual.loopless _ (by simp)
    · exact c.residual_boundary_right ⟨w,(mem_outside a b w).mpr ⟨hwa,hwb⟩⟩
  apply MultiGraph.ext_mult
  intro t
  induction t using Sym2.inductionOn with
  | hf x y =>
    by_cases hxa : x = a
    · subst x
      by_cases hyb : y = b
      · subst y
        simp [MultiGraph.addCopies,MultiGraph.restrict,Sym2.toFinset_mk_eq,
          insert_subset_iff,singleton_subset_iff,hp,copiesOn,scaledCopies,MultiGraph.unitEdge]
      · have hz := hleft y hyb
        simp [MultiGraph.addCopies,MultiGraph.restrict,Sym2.toFinset_mk_eq,
          insert_subset_iff,singleton_subset_iff,hz,copiesOn,scaledCopies,
          MultiGraph.unitEdge,Sym2.eq_iff,hab,hyb]
    by_cases hxb : x = b
    · subst x
      by_cases hya : y = a
      · subst y
        rw [show s(b,a) = s(a,b) from Sym2.eq_swap]
        simp [MultiGraph.addCopies,MultiGraph.restrict,Sym2.toFinset_mk_eq,
          insert_subset_iff,singleton_subset_iff,hp,copiesOn,scaledCopies,MultiGraph.unitEdge]
      · have hz := hright y hya
        simp [MultiGraph.addCopies,MultiGraph.restrict,Sym2.toFinset_mk_eq,
          insert_subset_iff,singleton_subset_iff,hz,copiesOn,scaledCopies,
          MultiGraph.unitEdge,Sym2.eq_iff,hab.symm,hya]
    by_cases hya : y = a
    · subst y
      have hz : c.residual.mult s(x,a) = 0 := by
        rw [show s(x,a) = s(a,x) from Sym2.eq_swap]
        exact hleft x hxb
      simp [MultiGraph.addCopies,MultiGraph.restrict,Sym2.toFinset_mk_eq,
        insert_subset_iff,singleton_subset_iff,hz,copiesOn,scaledCopies,
        MultiGraph.unitEdge,Sym2.eq_iff,hxa,hxb]
    by_cases hyb : y = b
    · subst y
      have hz : c.residual.mult s(x,b) = 0 := by
        rw [show s(x,b) = s(b,x) from Sym2.eq_swap]
        exact hright x hxa
      simp [MultiGraph.addCopies,MultiGraph.restrict,Sym2.toFinset_mk_eq,
        insert_subset_iff,singleton_subset_iff,hz,copiesOn,scaledCopies,
        MultiGraph.unitEdge,Sym2.eq_iff,hxa,hxb]
    simp [MultiGraph.addCopies,MultiGraph.restrict,Sym2.toFinset_mk_eq,
      insert_subset_iff,singleton_subset_iff,copiesOn,scaledCopies,
      MultiGraph.unitEdge,Sym2.eq_iff,hxa,hxb,hya,hyb]

theorem Certificate.colouring_of_ordinary {M : MultiGraph V} {d q : ℕ} {a b : V}
    (c : Certificate M d q a b) (hab : a ≠ b) (hreg : M.IsRegularOfDegree d)
    (hq : q = d - M.mult s(a,b))
    (F : (ordinary c.residual a b).EdgeColoring (d-2*q)) :
    Nonempty (M.EdgeColoring d) := by
  let E := extend_colouring (outside a b) (ordinary c.residual a b) F
  let P := pairColouring a b hab (d-2*q)
  have hdisj : ∀ w, (extend (outside a b) (ordinary c.residual a b)).degree w = 0 ∨
      (copiesOn a b hab (d-2*q)).degree w = 0 := by
    intro w
    by_cases hw : w ∈ outside a b
    · right
      have hh := (mem_outside a b w).mp hw
      rw [degree_copiesOn, if_neg (by tauto)]
    · left
      exact extend_degree_outside _ _ w hw
  have C := E.addSamePalette P hdisj
  have hs : Nonempty (c.residual.EdgeColoring (d-2*q)) := by
    have hh : (extend (outside a b) (ordinary c.residual a b)).addCopies
        (copiesOn a b hab (d-2*q)) = c.residual := by
      rw [extend_ordinary]
      exact c.residual_split hab hreg hq
    exact ⟨by rwa [hh] at C⟩
  obtain ⟨R⟩ := hs
  obtain ⟨H⟩ := c.colourable
  have hGraph := MultiGraph.add_subtract_of_le M c.cover c.le_original
  change c.cover.addCopies c.residual = M at hGraph
  have hdegree := MultiGraph.degree_subtract_add M c.cover c.le_original a
  rw [hreg a,c.regular a] at hdegree
  have hcol := H.addCopies R
  have hpalette : 2*q + (d-2*q) = d := by omega
  exact ⟨by rwa [hGraph,hpalette] at hcol⟩

/-- Full colourability of the peeled multigraph under explicit numeric
reserves; the ordinary factorization is constructed by the linear engine. -/
theorem colourable_of_linear_reserve (D A : MultiGraph V) (d q B C m : ℕ) (a b : V)
    (c : Certificate (D.addCopies A) d q a b) (hab : a ≠ b) (hStar : D.IsStarAt a)
    (hreg : (D.addCopies A).IsRegularOfDegree d) (hq : q = d - (D.addCopies A).mult s(a,b))
    (hBudget : A.twiceInternal (univ.erase a) ≤ B)
    (hC : 4000 ≤ C) (hsize : linearHalfBound C (B+1) ≤ m)
    (hcard : Fintype.card ↥(outside a b) = 2*m)
    (hdense : (C+64)*m ≤ C*(d-2*q)) : Nonempty ((D.addCopies A).EdgeColoring d) := by
  obtain ⟨F,_⟩ := ordinary_factorization D A d q B C m a b c hab hStar hBudget hC hsize hcard hdense
  exact c.colouring_of_ordinary hab hreg hq F

end OverfullWork.HeavyPairPeeling
