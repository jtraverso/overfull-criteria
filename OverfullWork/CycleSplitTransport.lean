module

public import OverfullWork.SimpleColouringBridge
public import OverfullWork.AlternatingCycleSplit
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section


/-! Transport of a split of a simple graph along an injective vertex map. -/
namespace OverfullWork.DeterministicSplit
open SimpleGraph Finset
open scoped Classical
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

noncomputable def mapSimpleLayer (M : MultiGraph W) (f : W ↪ V) : MultiGraph V :=
  MultiGraph.ofSimpleGraph (M.supportGraph.map f)

omit [DecidableEq W] in
theorem degree_map_graph (H : SimpleGraph W) (f : W ↪ V) (w : W) :
    (H.map f).degree (f w)=H.degree w := by
  classical
  have he : (H.map f).neighborFinset (f w)=(H.neighborFinset w).image f := by
    apply Finset.coe_injective
    simpa only [coe_neighborFinset,Finset.coe_image] using H.neighborSet_map f w
  rw [←card_neighborFinset_eq_degree,he,Finset.card_image_of_injective _ f.injective,
    card_neighborFinset_eq_degree]

omit [DecidableEq W] [Fintype V] in
theorem mapSimpleLayer_mult (M : MultiGraph W) (f : W ↪ V)
    (hM : ∀e,M.mult e≤1) (u v : W) :
    (mapSimpleLayer M f).mult s(f u,f v)=M.mult s(u,v) := by
  change (if s(f u,f v)∈(M.supportGraph.map f).edgeSet then 1 else 0)=_
  simp only [mem_edgeSet,map_adj_apply,MultiGraph.supportGraph]
  have hh:=hM s(u,v)
  split_ifs <;> omega

omit [DecidableEq W] [Fintype V] in
theorem mapSimpleLayer_mult_of_not_range (M : MultiGraph W) (f : W ↪ V)
    (u v : V) (hu : u∉Set.range f) :
    (mapSimpleLayer M f).mult s(u,v)=0 := by
  change (if s(u,v)∈(M.supportGraph.map f).edgeSet then 1 else 0)=0
  rw [if_neg]
  simp only [mem_edgeSet,map_adj]
  rintro ⟨a,b,hab,ha,hb⟩
  exact hu ⟨a,ha⟩

theorem mapSimpleLayer_degree (M : MultiGraph W) (f : W ↪ V)
    (hM : ∀e,M.mult e≤1) (w : W) :
    (mapSimpleLayer M f).degree (f w)=M.degree w := by
  rw [mapSimpleLayer,MultiGraph.degree_ofSimpleGraph,degree_map_graph,
    ←MultiGraph.degree_ofSimpleGraph,MultiGraph.of_supportGraph M hM]

theorem mapSimpleLayer_degree_of_not_range (M : MultiGraph W) (f : W ↪ V)
    (v : V) (hv : v∉Set.range f) : (mapSimpleLayer M f).degree v=0 := by
  rw [MultiGraph.degree_eq_sum_mult]
  apply Finset.sum_eq_zero
  intro w hw
  exact mapSimpleLayer_mult_of_not_range M f v w hv

theorem mapSimpleLayer_add (H : SimpleGraph W) (f : W ↪ V)
    (A B : MultiGraph W) (hab : A.addCopies B=MultiGraph.ofSimpleGraph H) :
    (mapSimpleLayer A f).addCopies (mapSimpleLayer B f)=
      MultiGraph.ofSimpleGraph (H.map f) := by
  classical
  have hcap (e) : A.mult e≤1 ∧ B.mult e≤1 := by
    have hh:=congrArg (fun M:MultiGraph W => M.mult e) hab
    change A.mult e+B.mult e=(if e∈H.edgeSet then 1 else 0) at hh
    split_ifs at hh <;> omega
  apply MultiGraph.ext_mult
  intro e
  induction e using Sym2.inductionOn with
  | hf u v =>
    by_cases hu : u∈Set.range f
    · obtain ⟨a,rfl⟩:=hu
      by_cases hv : v∈Set.range f
      · obtain ⟨b,rfl⟩:=hv
        change (mapSimpleLayer A f).mult s(f a,f b)+(mapSimpleLayer B f).mult s(f a,f b)=_
        rw [mapSimpleLayer_mult A f (fun e=>(hcap e).1),
          mapSimpleLayer_mult B f (fun e=>(hcap e).2)]
        have hh:=congrArg (fun M:MultiGraph W => M.mult s(a,b)) hab
        change A.mult s(a,b)+B.mult s(a,b)=(if s(a,b)∈H.edgeSet then 1 else 0) at hh
        simpa only [MultiGraph.ofSimpleGraph,mem_edgeSet,map_adj_apply] using hh
      · change (mapSimpleLayer A f).mult s(f a,v)+(mapSimpleLayer B f).mult s(f a,v)=_
        have ha : (mapSimpleLayer A f).mult s(f a,v)=0 := by
          rw [Sym2.eq_swap]
          exact mapSimpleLayer_mult_of_not_range A f v (f a) hv
        have hb : (mapSimpleLayer B f).mult s(f a,v)=0 := by
          rw [Sym2.eq_swap]
          exact mapSimpleLayer_mult_of_not_range B f v (f a) hv
        rw [ha,hb]
        change 0=(if s(f a,v)∈(H.map f).edgeSet then 1 else 0)
        rw [if_neg]
        simp only [mem_edgeSet,map_adj]
        rintro ⟨a',b',hadj,ha',hb'⟩
        exact hv ⟨b',hb'⟩
    · change (mapSimpleLayer A f).mult s(u,v)+(mapSimpleLayer B f).mult s(u,v)=_
      rw [mapSimpleLayer_mult_of_not_range A f u v hu,mapSimpleLayer_mult_of_not_range B f u v hu]
      change 0=(if s(u,v)∈(H.map f).edgeSet then 1 else 0)
      rw [if_neg]
      simp only [mem_edgeSet,map_adj]
      rintro ⟨a,b,hadj,ha,hb⟩
      exact hu ⟨a,ha⟩

/-- The unique possibly unbalanced vertex remains unique after an embedding. -/
theorem transport_simple_split (H : SimpleGraph W) (f : W ↪ V)
    (A B : MultiGraph W) (x : W)
    (hab : A.addCopies B=MultiGraph.ofSimpleGraph H)
    (hoff : ∀w,w≠x → A.degree w=B.degree w)
    (hrootA : A.degree x≤B.degree x+2) (hrootB : B.degree x≤A.degree x+2) :
    ∃P Q : MultiGraph V,
      P.addCopies Q=MultiGraph.ofSimpleGraph (H.map f) ∧
      (∀v,v≠f x → P.degree v=Q.degree v) ∧
      P.degree (f x)≤Q.degree (f x)+2 ∧ Q.degree (f x)≤P.degree (f x)+2 := by
  classical
  have hcap (e) : A.mult e≤1 ∧ B.mult e≤1 := by
    have hh:=congrArg (fun M:MultiGraph W => M.mult e) hab
    change A.mult e+B.mult e=(if e∈H.edgeSet then 1 else 0) at hh
    split_ifs at hh <;> omega
  have ha:=fun w => mapSimpleLayer_degree A f (fun e=>(hcap e).1) w
  have hb:=fun w => mapSimpleLayer_degree B f (fun e=>(hcap e).2) w
  refine ⟨mapSimpleLayer A f,mapSimpleLayer B f,mapSimpleLayer_add H f A B hab,?_,?_,?_⟩
  · intro v hv
    by_cases hin : v∈Set.range f
    · obtain ⟨w,rfl⟩:=hin
      rw [ha,hb]
      exact hoff w (fun he => hv (congrArg f he))
    · rw [mapSimpleLayer_degree_of_not_range A f v hin,
        mapSimpleLayer_degree_of_not_range B f v hin]
  · rwa [ha,hb]
  · rwa [ha,hb]

/-- A graph containing a cycle has a nonempty cycle piece with an alternating split.
Only one vertex of that piece can have unequal degrees in the two layers. -/
theorem exists_cycle_split_of_not_isAcyclic (G : SimpleGraph V) (hcyc : ¬G.IsAcyclic) :
    ∃ H : SimpleGraph V, H≤G ∧ H≠⊥ ∧
      ∃ x : V, ∃ A B : MultiGraph V,
        A.addCopies B=MultiGraph.ofSimpleGraph H ∧
        (∀v,v≠x → A.degree v=B.degree v) ∧
        A.degree x≤B.degree x+2 ∧ B.degree x≤A.degree x+2 := by
  classical
  have hex : ∃k,3≤k ∧ Nonempty (Copy (cycleGraph k) G) := by
    by_contra hn
    apply hcyc
    rw [isAcyclic_iff_free_cycleGraph]
    intro k hk hc
    exact hn ⟨k,hk,hc⟩
  obtain ⟨k,hk,⟨c⟩⟩:=hex
  obtain ⟨n,rfl⟩ : ∃n,k=n+3 := ⟨k-3,by omega⟩
  let f : Fin (n+3) ↪ V := ⟨c,c.injective⟩
  let H : SimpleGraph V := (cycleGraph (n+3)).map f
  have hle : H≤G := by
    intro u v huv
    obtain ⟨a,b,hab,ha,hb⟩:=(map_adj f _ u v).mp huv
    rw [←ha,←hb]
    exact c.toHom.map_adj hab
  have hne : H≠⊥ := by
    have hd : H.degree (f 0)=2 := by
      change ((cycleGraph (n+3)).map f).degree (f 0)=2
      calc
        _=(cycleGraph (n+3)).degree (0 : Fin (n+3)) := by
          convert degree_map_graph (cycleGraph (n+3)) f 0 using 1 <;>
            congr 1 <;> exact Subsingleton.elim _ _
        _=2 := cycleGraph_degree_three_le
    intro he
    simp [he] at hd
  obtain ⟨A,B,hab,hoff,ha,hb⟩:=cycleGraph_even_odd_split n
  obtain ⟨P,Q,hpq,hpqoff,hp,hq⟩:=transport_simple_split (cycleGraph (n+3)) f A B 0 (by convert hab using 1 <;> congr 1) hoff ha hb
  exact ⟨H,hle,hne,f 0,P,Q,(by convert hpq using 1 <;> congr 1),hpqoff,hp,hq⟩

end OverfullWork.DeterministicSplit
