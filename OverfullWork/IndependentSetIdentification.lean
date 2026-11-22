module

public import OverfullWork.PairIdentificationControl

@[expose] public section


/-! # Identifying an actual independent vertex set

All vertices in Y map to one new centre. Outside vertices are retained,
and every original edge remains a distinct labelled copy in the actual
fibre-count multigraph. Independence prevents loops. No absence of
overfull subsets or edge colouring of the target is assumed to exist.
-/
namespace OverfullWork.IndependentSetIdentification
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

abbrev Outside (Y : Finset V) := {v : V // v∉Y}
abbrev Vertices (Y : Finset V) := Option (Outside Y)

def vertexMap (Y : Finset V) (a : V) : Vertices Y :=
  if ha : a∈Y then none else some ⟨a,ha⟩

omit [Fintype V] in
@[simp] theorem map_eq_none (Y : Finset V) (a : V) :
    vertexMap Y a=none ↔ a∈Y := by
  by_cases ha : a∈Y <;> simp [vertexMap,ha]

omit [Fintype V] in
@[simp] theorem map_eq_some (Y : Finset V) (a : V) (x : Outside Y) :
    vertexMap Y a=some x ↔ a=x.val := by
  rcases x with ⟨x,hx⟩
  by_cases ha : a∈Y
  · have hax : a≠x := fun he=>hx (he ▸ ha)
    simp [vertexMap,ha,hax]
  · simp [vertexMap,ha]

omit [Fintype V] in
theorem map_loopless (G : SimpleGraph V) (Y : Finset V)
    (hind : G.IsIndepSet (Y:Set V)) :
    ∀a b,G.Adj a b → vertexMap Y a≠vertexMap Y b := by
  intro a b hab he
  by_cases ha : a∈Y
  · have hb : b∈Y := (map_eq_none Y b).mp (he.symm.trans ((map_eq_none Y a).mpr ha))
    exact hind ha hb hab.ne hab
  · by_cases hb : b∈Y
    · have haa : a∈Y := (map_eq_none Y a).mp (he.trans ((map_eq_none Y b).mpr hb))
      exact ha haa
    · have hab' : a=b := by simpa only [vertexMap,dif_neg ha,dif_neg hb,Option.some.injEq,Subtype.mk.injEq] using he
      exact hab.ne hab'

noncomputable def graph (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hind : G.IsIndepSet (Y:Set V)) : MultiGraph (Vertices Y) :=
  EdgeImage.graph G (vertexMap Y) (map_loopless G Y hind)

/-- The merged degree is the sum of the actual original degrees.
Independence ensures no original edge contributes twice. -/
theorem degree_none (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hind : G.IsIndepSet (Y:Set V)) :
    (graph G Y hind).degree none=∑y∈Y,G.degree y := by
  rw [graph,EdgeImage.degree_eq]
  have heq : (univ.filter fun e:G.edgeSet => (none : Vertices Y)∈Sym2.map (vertexMap Y) e.val)=
      Y.biUnion (fun y=>univ.filter fun e:G.edgeSet=>y∈e.val) := by
    ext e
    simp only [mem_filter,mem_univ,true_and,mem_biUnion,Sym2.mem_map,map_eq_none]
    exact ⟨fun ⟨y,hy,hyY⟩=>⟨y,hyY,hy⟩,fun ⟨y,hyY,hy⟩=>⟨y,hy,hyY⟩⟩
  have hdis : (↑Y:Set V).PairwiseDisjoint (fun y=>univ.filter fun e:G.edgeSet=>y∈e.val) := by
    intro y hy z hz hyz
    apply Finset.disjoint_left.mpr
    intro e hey hez
    have hay : e.val∈G.incidenceSet y:=⟨e.property,(mem_filter.mp hey).2⟩
    have haz : e.val∈G.incidenceSet z:=⟨e.property,(mem_filter.mp hez).2⟩
    exact hind hy hz hyz (G.adj_of_mem_incidenceSet hyz hay haz)
  rw [heq,card_biUnion hdis]
  apply sum_congr rfl
  intro y _
  exact PairIdentification.source_incidence_card G y

/-- Every outside degree remains unchanged, even when several edges now
have the same two image endpoints. -/
theorem degree_some (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hind : G.IsIndepSet (Y:Set V)) (x : Outside Y) :
    (graph G Y hind).degree (some x)=G.degree x.val := by
  rw [graph,EdgeImage.degree_eq,←PairIdentification.source_incidence_card G x.val]
  congr 1
  ext e
  simp only [mem_filter,mem_univ,true_and,Sym2.mem_map,map_eq_some]
  exact ⟨fun ⟨a,ha,he⟩=>he ▸ ha,fun h=>⟨x.val,h,rfl⟩⟩

/-- The only extra degree condition is the actual sum at the centre. -/
theorem degree_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hind : G.IsIndepSet (Y:Set V)) (D : ℕ)
    (hdegree : ∀v,G.degree v≤D) (hsum : (∑y∈Y,G.degree y)≤D) :
    ∀v,(graph G Y hind).degree v≤D := by
  intro v
  cases v with
  | none => rw [degree_none];exact hsum
  | some x => rw [degree_some];exact hdegree x.val

/-- An actual target colouring pulls back to all labelled original edges. -/
theorem colourable_of_identification (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hind : G.IsIndepSet (Y:Set V)) {D : ℕ}
    (C : (graph G Y hind).EdgeColoring D) : G.EdgeColorable D :=
  EdgeImage.colourable_of_image_colouring G (vertexMap Y) (map_loopless G Y hind) C

theorem card_vertices (Y : Finset V) : Fintype.card (Vertices Y)=Yᶜ.card+1 := by
  have e : Outside Y ≃ ↥(Yᶜ : Finset V) :=
    { toFun:=fun x=>⟨x.val,mem_compl.mpr x.property⟩
      invFun:=fun x=>⟨x.val,mem_compl.mp x.property⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  have hc : Fintype.card (Outside Y)=Yᶜ.card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  rw [Fintype.card_option,hc]

theorem even_card_vertices (Y : Finset V) (hodd : Odd Yᶜ.card) :
    Even (Fintype.card (Vertices Y)) := by
  rw [card_vertices]
  obtain ⟨k,hk⟩:=hodd
  exact ⟨k+1,by omega⟩

private theorem fibre_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (e : Sym2 (Vertices Y)) (A : Finset (Sym2 V))
    (hA : ∀a∈EdgeImage.fibre G (vertexMap Y) e,a.val∈A) :
    (EdgeImage.fibre G (vertexMap Y) e).card≤A.card := by
  have hsub : (EdgeImage.fibre G (vertexMap Y) e).image Subtype.val⊆A := by
    intro z hz
    obtain ⟨a,ha,rfl⟩:=mem_image.mp hz
    exact hA a ha
  have hh:=card_le_card hsub
  rwa [card_image_of_injective _ Subtype.val_injective] at hh

/-- No parallel copies are created between two outside vertices. -/
theorem isStarAt (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hind : G.IsIndepSet (Y:Set V)) :
    (graph G Y hind).IsStarAt none := by
  intro a b ha hb
  cases a with
  | none => exact (ha rfl).elim
  | some a =>
    cases b with
    | none => exact (hb rfl).elim
    | some b =>
      change (EdgeImage.fibre G (vertexMap Y) s(some a,some b)).card≤1
      have hh:=fibre_card_le G Y s(some a,some b) {s(a.val,b.val)} (by
        intro e he
        let p:=MultiGraph.GeneralCopies.endpoints e.val
        have hp : s(p.1,p.2)=e.val:=MultiGraph.GeneralCopies.endpoints_eq e.val
        have hm : s(vertexMap Y p.1,vertexMap Y p.2)=s(some a,some b) := by
          rw [←Sym2.map_mk,hp]
          exact (mem_filter.mp he).2
        rcases Sym2.eq_iff.mp hm with ⟨h1,h2⟩|⟨h1,h2⟩
        · have h1':=(map_eq_some Y p.1 a).mp h1
          have h2':=(map_eq_some Y p.2 b).mp h2
          exact mem_singleton.mpr (by rw [←hp,h1',h2'])
        · have h1':=(map_eq_some Y p.1 b).mp h1
          have h2':=(map_eq_some Y p.2 a).mp h2
          exact mem_singleton.mpr (by rw [←hp,h1',h2',Sym2.eq_swap]))
      simpa only [card_singleton] using hh

/-- At most one original edge per member of Y maps to a specified
centre-to-outside pair. -/
theorem centre_mult_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hind : G.IsIndepSet (Y:Set V)) (x : Outside Y) :
    (graph G Y hind).mult s(none,some x)≤Y.card := by
  change (EdgeImage.fibre G (vertexMap Y) s(none,some x)).card≤Y.card
  apply (fibre_card_le G Y _ (Y.image fun y=>s(y,x.val)) ?_).trans (card_image_le)
  intro e he
  let p:=MultiGraph.GeneralCopies.endpoints e.val
  have hp : s(p.1,p.2)=e.val:=MultiGraph.GeneralCopies.endpoints_eq e.val
  have hm : s(vertexMap Y p.1,vertexMap Y p.2)=s(none,some x) := by
    rw [←Sym2.map_mk,hp]
    exact (mem_filter.mp he).2
  rcases Sym2.eq_iff.mp hm with ⟨h1,h2⟩|⟨h1,h2⟩
  · have h1':=(map_eq_none Y p.1).mp h1
    have h2':=(map_eq_some Y p.2 x).mp h2
    exact mem_image.mpr ⟨p.1,h1',by rw [←hp,h2']⟩
  · have h1':=(map_eq_some Y p.1 x).mp h1
    have h2':=(map_eq_none Y p.2).mp h2
    exact mem_image.mpr ⟨p.2,h2',by rw [←hp,h1',Sym2.eq_swap]⟩

theorem centreControl (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (hind : G.IsIndepSet (Y:Set V)) :
    (graph G Y hind).CentreControl none Y.card := by
  left
  intro x
  cases x with
  | none => rw [(graph G Y hind).loopless _ (by simp)];omega
  | some x => exact centre_mult_le G Y hind x

end OverfullWork.IndependentSetIdentification
