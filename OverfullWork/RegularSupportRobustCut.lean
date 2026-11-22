module

public import OverfullWork.HeavyNeighbourCutRepair
public import OverfullWork.CompletionBipartiteRobust

@[expose] public section


/-! # A fresh robust cut controls the completed simple support itself

Partition the actual support, rather than transporting discrepancy from
the ordered base. The existing incidence criterion proves robustness
of this same cut from its bounded exceptional support deficits.
-/
namespace OverfullWork.RegularSupportRobustCut
open SimpleGraph Finset PrunedCore RobustExpansion BipartiteRobustMargin
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 6000000

def anchorPair (a b : V) (hab : a ≠ b) : (Fin 1 × Bool) ↪ V where
  toFun z := if z.2 then a else b
  inj' := by
    intro x y h
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · cases hx : x.2 <;> cases hy : y.2 <;> simp_all [hab,hab.symm]

theorem support_contained (M : MultiGraph V) :
    ∀ e, (MultiGraph.ofSimpleGraph M.supportGraph).mult e ≤ M.mult e := by
  intro e
  induction e using Sym2.inductionOn with
  | hf u v =>
    change (if s(u,v) ∈ M.supportGraph.edgeSet then 1 else 0) ≤ M.mult s(u,v)
    simp only [mem_edgeSet, MultiGraph.supportGraph]
    split_ifs <;> omega

theorem exists_cut (M : MultiGraph V) (d m : ℕ) (a b : V) (hab : a ≠ b)
    (hm : 1 ≤ m) (hcard : Fintype.card V = 2*m) (hreg : M.IsRegularOfDegree d)
    (E : Finset V) (e s δ q r t : ℕ) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (hsize : 30*(m:ℝ)^4 < ξ^6) (hE : E.card ≤ e)
    (hDef : ∀ v, v ∉ E → d-M.supportGraph.degree v ≤ s)
    (hRoom : 2*(δ:ℝ)+ξ+3*(s:ℝ) ≤ d)
    (hδ : δ ≤ m) (hMargin : m+2*q ≤ 2*δ) (hr : 0 < r)
    (hrq : r ≤ q) (hrt : r+e ≤ t) (hScale : 4*r*m+2*m*e ≤ q*t) :
    ∃ A : Finset V, A.card = m ∧ Aᶜ.card = m ∧ a ∈ A ∧ b ∉ A ∧
      IsBipartiteRobustAt M.supportGraph A r t ∧
      ∀ v, |(neighboursIn M.supportGraph A v:ℝ)-(neighboursIn M.supportGraph Aᶜ v:ℝ)| < ξ := by
  have hMu : ∀ u v, ((MultiGraph.ofSimpleGraph M.supportGraph).mult s(u,v):ℝ) ≤ 1 := by
    intro u v
    simp only [MultiGraph.ofSimpleGraph]
    split_ifs <;> norm_num
  obtain ⟨A,hA,hAc,hSep,ha,hb,hDis⟩ :=
    (MultiGraph.ofSimpleGraph M.supportGraph).exists_balanced_degree_partition_center m hcard
      (show 1 ≤ m from hm) (anchorPair a b hab) 0 1 (by norm_num) hMu ξ hξ hsize
  have ha' : a ∈ A := ha
  have hb' : b ∉ A := hb
  have hWeighted : ∀ v, |(M.degreeInto A v:ℝ)-(M.degreeInto Aᶜ v:ℝ)| <
      ξ+((d-M.supportGraph.degree v:ℕ):ℝ) := by
    intro v
    have hh := MultiGraph.regular_discrepancy_from_simple M M.supportGraph d hreg
      (support_contained M) A v
    have hd := hDis v
    simp only [one_mul] at hd
    linarith
  refine ⟨A,hA,hAc,ha',hb',?_,?_⟩
  · exact CompletionBipartiteRobust.robust_of_completed_cut M.supportGraph M d hreg
      (support_contained M) A E m δ q r t e s ξ hA hAc hE hWeighted hDef hRoom
      hδ hMargin hr hrq hrt hScale
  · intro v
    have hd := hDis v
    simp only [one_mul, CompletionBipartiteRobust.simple_degreeInto_eq_neighbours] at hd
    exact hd

end OverfullWork.RegularSupportRobustCut
