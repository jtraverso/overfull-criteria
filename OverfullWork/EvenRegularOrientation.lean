module

public import OverfullWork.DirectedRobustExpansion
public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section


/-! An even-regular graph has a balanced orientation. Match each edge
to one of the prescribed tail slots at its endpoints. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_balanced_even_regular_orientation (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hReg : ∀ v, G.degree v = 2*k) :
    ∃ D : Digraph V, IsOrientationOf D G ∧ ∀ v, outDegree D v = k ∧ inDegree D v = k := by
  classical
  let N := fun e : G.edgeSet => (univ : Finset (V × Fin k)).filter (fun x => x.1 ∈ e.val)
  have hHall (X : Finset G.edgeSet) : X.card ≤ (X.biUnion N).card := by
    let E := X.image Subtype.val
    let S := (univ : Finset V).filter (fun v => ∃ e ∈ E, v ∈ e)
    let H := SimpleGraph.fromEdgeSet (E : Set (Sym2 V))
    letI : DecidableRel H.Adj := Classical.decRel _
    have hHG : H ≤ G := by
      intro v w h
      obtain ⟨e,_,he⟩ := mem_image.mp ((fromEdgeSet_adj (E : Set (Sym2 V))).mp h).1
      have hm := e.prop
      rwa [he] at hm
    have hEdges (inst : Fintype H.edgeSet) : @SimpleGraph.edgeFinset V H inst = E := by
      letI := inst
      ext e
      rw [mem_edgeFinset,edgeSet_fromEdgeSet]
      constructor
      · exact fun h => h.1
      · intro he
        obtain ⟨f,_,rfl⟩ := mem_image.mp he
        exact ⟨he,G.not_isDiag_of_mem_edgeSet f.prop⟩
    have hD (v : V) : H.degree v ≤ if v ∈ S then 2*k else 0 := by
      by_cases hv : v ∈ S
      · rw [if_pos hv,←hReg v]
        exact degree_le_of_le hHG
      · rw [if_neg hv,(degree_eq_zero_iff_notMem_support H v).mpr]
        intro hs
        obtain ⟨w,hw⟩ := H.mem_support.mp hs
        exact hv (mem_filter.mpr ⟨mem_univ _,s(v,w),((fromEdgeSet_adj (E : Set (Sym2 V))).mp hw).1,Sym2.mem_mk_left _ _⟩)
    have hSum := sum_le_sum (s := (univ : Finset V)) (fun v _ => hD v)
    rw [H.sum_degrees_eq_twice_card_edges,hEdges,card_image_of_injective _ Subtype.val_injective,
      ←sum_filter] at hSum
    simp only [sum_const,smul_eq_mul,filter_mem_eq_inter,univ_inter] at hSum
    have hSub : S ×ˢ (univ : Finset (Fin k)) ⊆ X.biUnion N := by
      intro x hx
      obtain ⟨e,he,hx'⟩ := (mem_filter.mp (mem_product.mp hx).1).2
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      exact mem_biUnion.mpr ⟨f,hf,mem_filter.mpr ⟨mem_univ _,hx'⟩⟩
    have hc := card_le_card hSub
    rw [card_product,card_univ,Fintype.card_fin] at hc
    nlinarith only [hSum,hc]
  have hCard : Fintype.card G.edgeSet = Fintype.card (V × Fin k) := by
    have h := G.sum_degrees_eq_twice_card_edges
    simp only [hReg,sum_const,smul_eq_mul,card_univ] at h
    rw [G.card_edgeSet,Fintype.card_prod,Fintype.card_fin]
    nlinarith only [h]
  obtain ⟨f,hf,hfN⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hHall
  let F := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hCard⟩)
  have hF (e : G.edgeSet) : (F e).1 ∈ e.val := (mem_filter.mp (hfN e)).2
  let D : Digraph V := ⟨fun v w => ∃ e : G.edgeSet, e.val = s(v,w) ∧ (F e).1 = v⟩
  have hD : IsOrientationOf D G := by
    refine ⟨?_,?_,?_⟩
    · intro v w h
      obtain ⟨e,he,_⟩ := h
      have hm := e.prop
      rwa [he] at hm
    · intro v w h
      let e : G.edgeSet := ⟨s(v,w),h⟩
      have hm : (F e).1 ∈ s(v,w) := hF e
      rcases Sym2.mem_iff.mp hm with hv | hw
      · exact Or.inl ⟨e,rfl,hv⟩
      · exact Or.inr ⟨e,Sym2.eq_swap,hw⟩
    · intro v w h
      obtain ⟨⟨e,he,hve⟩,⟨f',hf',hwf⟩⟩ := h
      have hef : e = f' := Subtype.ext (he.trans (Sym2.eq_swap.trans hf'.symm))
      have hm := e.prop
      rw [he] at hm
      have hne : v ≠ w := (show G.Adj v w from hm).ne
      exact hne (hve.symm.trans ((congrArg (fun a => (F a).1) hef).trans hwf))
  refine ⟨D,hD,?_⟩
  intro v
  have hout : outDegree D v = k := by
    let e := fun i : Fin k => F.symm (v,i)
    have hv (i : Fin k) : (F (e i)).1 = v := congrArg Prod.fst (F.apply_symm_apply (v,i))
    have hm (i : Fin k) : v ∈ (e i).val := hv i ▸ hF (e i)
    choose w hw using fun i => Sym2.mem_iff_exists.mp (hm i)
    letI : DecidablePred (D.Adj v) := Classical.decPred _
    suffices hh : (univ : Finset (Fin k)).card =
        (@Finset.filter V (D.Adj v) (Classical.decPred _) univ).card by
      simpa only [outDegree,card_univ,Fintype.card_fin] using hh.symm
    apply card_bij (fun i _ => w i)
    · intro i _
      exact mem_filter.mpr ⟨mem_univ _,e i,hw i,hv i⟩
    · intro i _ j _ hij
      have he : e i = e j := Subtype.ext ((hw i).trans ((congrArg (fun z => s(v,z)) hij).trans (hw j).symm))
      exact congrArg Prod.snd (F.symm.injective he)
    · intro u hu
      obtain ⟨e',he',hv'⟩ := (mem_filter.mp hu).2
      let i := (F e').2
      have hFi : (v,i) = F e' := Prod.ext hv'.symm rfl
      have he : e i = e' := (congrArg F.symm hFi).trans (F.symm_apply_apply _)
      have hEnds : s(v,w i) = s(v,u) := (hw i).symm.trans ((congrArg Subtype.val he).trans he')
      exact ⟨i,mem_univ _,Sym2.congr_right.mp hEnds⟩
  have h := degree_partition D G hD v
  rw [hReg v,hout] at h
  exact ⟨hout,by omega⟩

end OverfullWork.DirectedRobustExpansion
