module

public import OverfullWork.GeneralCopies
public import OverfullWork.FactorizationAssembly
public import LeanPool.Vizing.Main

@[expose] public section


namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem degree_ofSimpleGraph (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (ofSimpleGraph G).degree v=G.degree v := by
  rw [degree_eq_sum_mult]
  simp only [ofSimpleGraph,mem_edgeSet]
  rw [←G.card_neighborFinset_eq_degree]
  simp only [←card_filter]
  congr 1
  ext u
  simp

theorem ofSimpleGraph_colouring (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hcol : G.EdgeColorable k) : Nonempty ((ofSimpleGraph G).EdgeColoring k) := by
  obtain ⟨C⟩:=hcol
  let M := ofSimpleGraph G
  have hmem (e : GeneralCopies.Copies M) : e.1∈G.edgeSet := by
    have h:=e.2.isLt
    change e.2.val<(if e.1∈G.edgeSet then 1 else 0) at h
    by_contra hn
    rw [if_neg hn] at h
    omega
  let f : GeneralCopies.Copies M → G.edgeSet := fun e => ⟨e.1,hmem e⟩
  have hf : Function.Injective f := by
    intro e g h
    have he : e.1=g.1 := congrArg Subtype.val h
    cases e with
    | mk e i =>
      cases g with
      | mk g j =>
        dsimp only at he
        subst g
        have hi:=i.isLt
        have hj:=j.isLt
        have hm : M.mult e≤1 := by dsimp [M,ofSimpleGraph]; split_ifs <;> omega
        have hij : i=j := Fin.ext (by omega)
        subst j
        rfl
  let c : GeneralCopies.Copies M → Fin k := fun e => C (f e)
  have hc : ShannonColouring.IsProperEdgeColouring (GeneralCopies.ends M) c := by
    intro e g hne hinc
    apply C.valid
    rw [lineGraph_adj_iff_exists]
    obtain ⟨v,he,hg⟩:=hinc
    exact ⟨fun h => hne (hf h),v,(GeneralCopies.incident_iff M e v).mp he,
      (GeneralCopies.incident_iff M g v).mp hg⟩
  exact ⟨GeneralCopies.edgeColoring M c hc⟩

theorem ofSimpleGraph_vizing (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hdeg : ∀ v,G.degree v≤d) : Nonempty ((ofSimpleGraph G).EdgeColoring (d+1)) := by
  apply ofSimpleGraph_colouring
  apply (LeanPool.Vizing.lineGraph_colorable G).mono
  have hd : G.maxDegree≤d := G.maxDegree_le_of_forall_degree_le d hdeg
  omega

def supportGraph (M : MultiGraph V) : SimpleGraph V where
  Adj u v := 0<M.mult s(u,v)
  symm := ⟨by intro u v h; simpa only [Sym2.eq_swap] using h⟩
  loopless := ⟨by intro u h; have hz:=M.loopless s(u,u) (by simp); omega⟩

noncomputable instance (M : MultiGraph V) : DecidableRel M.supportGraph.Adj := Classical.decRel _

theorem of_supportGraph (M : MultiGraph V) (hmu : ∀ e,M.mult e≤1) :
    ofSimpleGraph M.supportGraph=M := by
  apply ext_mult
  intro e
  induction e using Sym2.inductionOn with
  | hf u v =>
    simp only [ofSimpleGraph,SimpleGraph.mem_edgeSet,supportGraph]
    have h:=hmu s(u,v)
    split_ifs <;> omega

theorem exists_edgeColoring_simple (M : MultiGraph V) (d : ℕ)
    (hmu : ∀ e,M.mult e≤1) (hdeg : ∀ v,M.degree v≤d) : Nonempty (M.EdgeColoring (d+1)) := by
  have hg : ∀ v,M.supportGraph.degree v≤d := by
    intro v
    rw [←degree_ofSimpleGraph,of_supportGraph M hmu]
    exact hdeg v
  have hc:=ofSimpleGraph_vizing M.supportGraph d hg
  rwa [of_supportGraph M hmu] at hc

end SimpleGraph.MultiGraph
