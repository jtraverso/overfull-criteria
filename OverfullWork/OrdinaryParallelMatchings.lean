module

public import OverfullWork.ParallelBudget
public import OverfullWork.MultiplicityLayerColouring
public import OverfullWork.ShannonBridge
public import OverfullWork.EquitableRecolouring

@[expose] public section


/-! Separate and partition the extra copies of the ordinary multigraph
in CMS §5.2, Case 1. -/
namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The extra copies after retaining one copy of every supported pair. -/
noncomputable def parallelCopies (M : MultiGraph V) : MultiGraph V :=
  M.subtractCopies (ofSimpleGraph M.supportGraph)

@[simp]
theorem parallelCopies_mult (M : MultiGraph V) (e : Sym2 V) :
    M.parallelCopies.mult e = M.mult e-1 := by
  induction e using Sym2.inductionOn with
  | hf x y =>
    simp only [parallelCopies,subtractCopies,ofSimpleGraph,SimpleGraph.mem_edgeSet,supportGraph]
    split_ifs with h
    · rfl
    · omega

theorem degree_parallelCopies (M : MultiGraph V) (v : V) :
    M.parallelCopies.degree v = M.parallelExcess v := by
  rw [degree_eq_sum_mult,parallelExcess]
  simp only [parallelCopies_mult]

theorem simple_add_parallelCopies (M : MultiGraph V) :
    (ofSimpleGraph M.supportGraph).addCopies M.parallelCopies = M := by
  apply add_subtract_of_le
  intro e
  induction e using Sym2.inductionOn with
  | hf x y =>
    simp only [ofSimpleGraph,SimpleGraph.mem_edgeSet,supportGraph]
    split_ifs <;> omega

/-- Shannon and equitable recolouring partition the parallel copies
into bounded matchings. The same palette provides their exact copy sum.
The number of colours and the per-matching size are explicit. -/
theorem exists_parallel_copy_matchings (M : MultiGraph V) (b ℓ m : ℕ)
    (hDeg : ∀ v, M.parallelExcess v ≤ b)
    (hPalette : 3*b/2 ≤ ℓ) (hMass : M.parallelCopies.edgeCount ≤ ℓ*m) :
    ∃ C : M.parallelCopies.EdgeColoring ℓ,
      (∀ i, (C.colourGraph i).edgeCount ≤ m) ∧
      ∀ i v, (C.colourGraph i).degree v ≤ 1 := by
  obtain ⟨S⟩ := exists_edgeColoring_shannon M.parallelCopies b (fun v => by
    rw [degree_parallelCopies]
    exact hDeg v)
  obtain ⟨S'⟩ := S.enlarge hPalette
  obtain ⟨C,hC⟩ := S'.exists_equitable
  refine ⟨C,?_,C.colourGraph_degree_le_one⟩
  intro i
  by_contra h
  have hPer (j : Fin ℓ) : m ≤ C.colourMass j := by
    have hh := hC i j
    change ¬ C.colourMass i ≤ m at h
    omega
  have hSum := C.sum_colourMass
  have hi : i ∈ (univ : Finset (Fin ℓ)) := mem_univ _
  have hLt : (∑ _j : Fin ℓ, m) < ∑ j : Fin ℓ, C.colourMass j :=
    sum_lt_sum (fun j _ => hPer j) ⟨i,hi,Nat.lt_of_not_ge h⟩
  simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul,hSum] at hLt
  omega

end SimpleGraph.MultiGraph
