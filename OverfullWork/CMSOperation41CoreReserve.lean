module

public import OverfullWork.CMSOperation41PrefixClassTwo
public import OverfullWork.CMSOperation42CoreRobustness

@[expose] public section


/-! Claim 4.2(1) for every physical prefix. The protected remainder
of the simultaneous core packing lies in each current ordinary core. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph RobustExpansion CMSMatchingRemoval
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem robust_physical_prefix_of_core_reserve (G S : SimpleGraph V)
    (U : Finset V) (L : ℕ → SimpleGraph V) (j : ℕ)
    (R : SimpleGraph (↥(Uᶜ : Finset V))) [DecidableRel R.Adj]
    (hCore : ∀ a b,a ∉ U → b ∉ U → (S.Adj a b ↔ G.Adj a b))
    (hLe : R ≤ G.induce (↑(Uᶜ) : Set V))
    (hAvoid : ∀ i < j,∀ u v,R.Adj u v → ¬(L i).Adj u.val v.val)
    (r t : ℕ) (hRob : IsRobustAt R r t) :
    IsRobustAt (sdiff S (usedTrimmingPrefix L j)) (r-U.card) (t+U.card) := by
  let A := Uᶜ
  let H := sdiff S (usedTrimmingPrefix L j)
  have hRLe : R ≤ H.induce (A : Set V) := by
    intro u v h
    change S.Adj u.val v.val ∧ ¬(usedTrimmingPrefix L j).Adj u.val v.val
    refine ⟨(hCore u.val v.val (mem_compl.mp u.property) (mem_compl.mp v.property)).mpr (hLe h),?_⟩
    intro hj
    obtain ⟨i,hi⟩ := iSup_adj.mp hj
    exact hAvoid i.val i.isLt u v h hi
  have hCurrent := isRobustAt_mono_graph R (H.induce (A : Set V)) hRLe r t hRob
  simpa only [A,compl_compl] using robust_of_ordinary_core H A r t hCurrent

end OverfullWork.CMSTrimmingRound
