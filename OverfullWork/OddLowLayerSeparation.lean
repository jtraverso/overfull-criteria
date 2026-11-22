module

public import OverfullWork.LowSkeletonLayerGluing
public import OverfullWork.PathGraphRealization

@[expose] public section


/-! # Separating the odd skeleton's extra edge by actual path indices

The label of a projected endpoint is its representative's core-path index.
Matching leaves inherit their unique partner's label. Every base-layer edge
preserves these constructed labels, so different anchor paths forbid a
connection before the final odd edge is inserted.
-/
namespace OverfullWork.OddLowLayerSeparation
open SimpleGraph Finset LowSkeletonProjection
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 4000000

omit [Fintype V] [DecidableEq V] in
theorem label_eq_of_reachable {L : Type*} (F : SimpleGraph V) (label : V → L)
    (hedge : ∀x y,F.Adj x y → label x=label y) {x y : V} (h : F.Reachable x y) :
    label x=label y := by
  obtain ⟨p⟩:=h
  induction p with
  | nil => rfl
  | cons h p ih => exact (hedge _ _ h).trans ih

noncomputable def projectLabel {L : Type*} {G : SimpleGraph V} {A U Z : Finset V}
    (P : Projection G A U Z) (label : V → L) (v : V) : L :=
  if hv : v∈A then label (P.representative ⟨v,hv⟩).val else label v

theorem projectLabel_eq_rep {L : Type*} {G : SimpleGraph V} {A U Z : Finset V}
    (P : Projection G A U Z) (label : V → L) (v : V) (hv : v∈A) :
    projectLabel P label v=label (P.representative ⟨v,hv⟩).val := by
  simp only [projectLabel,dif_pos hv]

theorem projectLabel_eq_core {L : Type*} {G : SimpleGraph V} {A U Z : Finset V}
    (P : Projection G A U Z) (label : V → L) (v : V) (hv : v∉U) :
    projectLabel P label v=label v := by
  by_cases ha : v∈A
  · rw [projectLabel_eq_rep P label v ha,P.fixed ⟨v,ha⟩ hv]
  · simp only [projectLabel,dif_neg ha]

theorem projectLabel_projection_edge {L : Type*} {G : SimpleGraph V} {A U Z : Finset V}
    (P : Projection G A U Z) (label : V → L) (x y : V) (hxy : P.matching.Adj x y) :
    projectLabel P label x=projectLabel P label y := by
  have hsource : ∀x y,P.matching.Adj x y → x∈A∩U → y∉A∪Z →
      projectLabel P label x=projectLabel P label y := by
    intro x y hxy hx hy
    have hxA:=(mem_inter.mp hx).1
    have hxU:=(mem_inter.mp hx).2
    have he : y=(P.representative ⟨x,hxA⟩).val :=
      P.isMatching x y _ hxy (P.selected ⟨x,hxA⟩ hxU)
    have hyA : y∉A := fun hyA => hy (mem_union_left _ hyA)
    rw [projectLabel_eq_rep P label x hxA]
    simp only [projectLabel,dif_neg hyA]
    exact congrArg label he.symm
  rcases P.endpoints x y hxy with hx|hy
  · exact hsource x y hxy hx.1 hx.2.2
  · exact (hsource y x hxy.symm hy.1 hy.2.2).symm

noncomputable def matchingLabel {L : Type*} (M : SimpleGraph V) (W : Finset V)
    (label : V → L) (fallback : L) (v : V) : L :=
  if v∈W then if h : ∃a,M.Adj v a then label h.choose else fallback else label v

theorem matchingLabel_outside {L : Type*} (M : SimpleGraph V) (W : Finset V)
    (label : V → L) (fallback : L) (v : V) (hv : v∉W) :
    matchingLabel M W label fallback v=label v := by
  simp only [matchingLabel,if_neg hv]

theorem matchingLabel_low_edge {L : Type*} (M : SimpleGraph V) (W : Finset V)
    (hm : OneFactor.IsMatchingGraph M) (label : V → L) (fallback : L)
    (v a : V) (hv : v∈W) (hva : M.Adj v a) :
    matchingLabel M W label fallback v=label a := by
  have hex : ∃b,M.Adj v b:=⟨a,hva⟩
  unfold matchingLabel
  rw [if_pos hv,dif_pos hex]
  exact congrArg label (hm v hex.choose a hex.choose_spec hva)

/-- No reachability condition is assumed: the invariant is built from
projection partners and matching uniqueness. -/
theorem not_reachable_of_projected_labels {L : Type*}
    (G M K : SimpleGraph V) (A W U Z : Finset V) (P : Projection G A U Z)
    (hWU : W⊆U) (hAW : Disjoint A W) (hm : OneFactor.IsMatchingGraph M)
    (hMcross : ∀x y,M.Adj x y → (x∈W ∧ y∉W) ∨ (y∈W ∧ x∉W))
    (hKcore : ∀x y,K.Adj x y → x∉U ∧ y∉U)
    (label : V → L) (fallback : L) (hKlabel : ∀x y,K.Adj x y → label x=label y)
    (w a b : V) (hw : w∈W) (hwa : M.Adj w a)
    (ha : a∈A) (hb : b∈A) (hbW : b∉W)
    (hsep : label (P.representative ⟨a,ha⟩).val≠label (P.representative ⟨b,hb⟩).val) :
    ¬((M⊔P.matching)⊔K).Reachable w b := by
  let beta:=projectLabel P label
  let finalLabel:=matchingLabel M W beta fallback
  have hM : ∀x y,M.Adj x y → finalLabel x=finalLabel y := by
    intro x y hxy
    rcases hMcross x y hxy with ⟨hx,hy⟩|⟨hy,hx⟩
    · exact (matchingLabel_low_edge M W hm beta fallback x y hx hxy).trans
        (matchingLabel_outside M W beta fallback y hy).symm
    · exact (matchingLabel_outside M W beta fallback x hx).trans
        (matchingLabel_low_edge M W hm beta fallback y x hy hxy.symm).symm
  have hN : ∀x y,P.matching.Adj x y → finalLabel x=finalLabel y := by
    intro x y hxy
    have hn : x∉W ∧ y∉W := by
      have hsource : ∀x∈A,x∉W := fun x hx hw => Finset.disjoint_left.mp hAW hx hw
      rcases P.endpoints x y hxy with hx|hy
      · exact ⟨hsource x (mem_inter.mp hx.1).1,fun hw => hx.2.1 (hWU hw)⟩
      · exact ⟨fun hw => hy.2.1 (hWU hw),hsource y (mem_inter.mp hy.1).1⟩
    change matchingLabel M W beta fallback x=matchingLabel M W beta fallback y
    rw [matchingLabel_outside M W beta fallback x hn.1,matchingLabel_outside M W beta fallback y hn.2]
    exact projectLabel_projection_edge P label x y hxy
  have hK : ∀x y,K.Adj x y → finalLabel x=finalLabel y := by
    intro x y hxy
    have hc:=hKcore x y hxy
    have hx : x∉W:=fun hx => hc.1 (hWU hx)
    have hy : y∉W:=fun hy => hc.2 (hWU hy)
    change matchingLabel M W beta fallback x=matchingLabel M W beta fallback y
    rw [matchingLabel_outside M W beta fallback x hx,matchingLabel_outside M W beta fallback y hy]
    change projectLabel P label x=projectLabel P label y
    rw [projectLabel_eq_core P label x hc.1,projectLabel_eq_core P label y hc.2]
    exact hKlabel x y hxy
  intro hreach
  have he:=label_eq_of_reachable ((M⊔P.matching)⊔K) finalLabel
    (fun x y h => h.elim (fun h => h.elim (hM x y) (hN x y)) (hK x y)) hreach
  change matchingLabel M W beta fallback w=matchingLabel M W beta fallback b at he
  rw [matchingLabel_low_edge M W hm beta fallback w a hw hwa,
    matchingLabel_outside M W beta fallback b hbW] at he
  change projectLabel P label a=projectLabel P label b at he
  rw [projectLabel_eq_rep P label a ha,projectLabel_eq_rep P label b hb] at he
  exact hsep he

section PathIndices
variable {I : Type*} [Fintype I] {G : SimpleGraph V} [DecidableRel G.Adj]
  {s t : I → V}

/-- The actual path containing a vertex, with `none` off the path family. -/
noncomputable def pathIndexLabel (T : ∀i,G.Walk (s i) (t i)) (v : V) : Option I :=
  if h : ∃i,v∈(T i).support then some h.choose else none

omit [Fintype V] [DecidableRel G.Adj] in
theorem pathIndexLabel_eq_some (T : ∀i,G.Walk (s i) (t i))
    (hdis : ∀i j,i≠j → ∀z,z∈(T i).support → z∉(T j).support)
    (i : I) (v : V) (hv : v∈(T i).support) : pathIndexLabel T v=some i := by
  have hex : ∃j,v∈(T j).support := ⟨i,hv⟩
  have he : hex.choose=i := by
    by_contra hn
    exact hdis hex.choose i hn v hex.choose_spec hv
  simp only [pathIndexLabel,dif_pos hex,he]

theorem pathIndexLabel_edge (T : ∀i,G.Walk (s i) (t i))
    (hdis : ∀i j,i≠j → ∀z,z∈(T i).support → z∉(T j).support)
    (x y : V) (hxy : (PathGraphRealization.pathUnion T).Adj x y) :
    pathIndexLabel T x=pathIndexLabel T y := by
  obtain ⟨i,hi⟩:=PathGraphRealization.pathUnion_adj_iff T |>.mp hxy
  rw [pathIndexLabel_eq_some T hdis i x (PathGraphRealization.mem_support_of_adj (T i) hi),
    pathIndexLabel_eq_some T hdis i y (PathGraphRealization.mem_support_of_adj (T i) hi.symm)]

/-- Distinct actual core paths separate the two odd-edge anchors. Neither
reachability nor an output forest is supplied as a hypothesis. -/
theorem not_reachable_of_separated_paths
    (M : SimpleGraph V) (A W U Z : Finset V) (P : Projection G A U Z)
    (hWU : W⊆U) (hAW : Disjoint A W) (hm : OneFactor.IsMatchingGraph M)
    (hMcross : ∀x y,M.Adj x y → (x∈W ∧ y∉W) ∨ (y∈W ∧ x∉W))
    (T : ∀i,G.Walk (s i) (t i))
    (hdis : ∀i j,i≠j → ∀z,z∈(T i).support → z∉(T j).support)
    (hcore : ∀i z,z∈(T i).support → z∉U)
    (w a b : V) (hw : w∈W) (hwa : M.Adj w a)
    (ha : a∈A) (hb : b∈A) (hbW : b∉W)
    (i j : I) (hij : i≠j)
    (hia : (P.representative ⟨a,ha⟩).val∈(T i).support)
    (hjb : (P.representative ⟨b,hb⟩).val∈(T j).support) :
    ¬((M⊔P.matching)⊔PathGraphRealization.pathUnion T).Reachable w b := by
  have hKcore : ∀x y,(PathGraphRealization.pathUnion T).Adj x y → x∉U ∧ y∉U := by
    intro x y h
    obtain ⟨k,hk⟩:=PathGraphRealization.pathUnion_adj_iff T |>.mp h
    exact ⟨hcore k x (PathGraphRealization.mem_support_of_adj (T k) hk),
      hcore k y (PathGraphRealization.mem_support_of_adj (T k) hk.symm)⟩
  apply not_reachable_of_projected_labels G M (PathGraphRealization.pathUnion T)
    A W U Z P hWU hAW hm hMcross hKcore (pathIndexLabel T) none
    (pathIndexLabel_edge T hdis) w a b hw hwa ha hb hbW
  rw [pathIndexLabel_eq_some T hdis i _ hia,pathIndexLabel_eq_some T hdis j _ hjb]
  exact fun he => hij (Option.some.inj he)

/-- Adding the odd skeleton edge to the matching/projection/path base
preserves acyclicity when its two projected anchors lie on different paths. -/
theorem odd_union_isAcyclic
    (M : SimpleGraph V) (A W U Z : Finset V) (P : Projection G A U Z)
    (hWU : W⊆U) (hAW : Disjoint A W) (hm : OneFactor.IsMatchingGraph M)
    (hMcross : ∀x y,M.Adj x y → (x∈W ∧ y∉W) ∨ (y∈W ∧ x∉W))
    (T : ∀i,G.Walk (s i) (t i)) (hp : ∀i,(T i).IsPath)
    (hdis : ∀i j,i≠j → ∀z,z∈(T i).support → z∉(T j).support)
    (hcore : ∀i z,z∈(T i).support → z∉U)
    (w a b : V) (hw : w∈W) (hwa : M.Adj w a)
    (ha : a∈A) (hb : b∈A) (hbW : b∉W)
    (i j : I) (hij : i≠j)
    (hia : (P.representative ⟨a,ha⟩).val∈(T i).support)
    (hjb : (P.representative ⟨b,hb⟩).val∈(T j).support) :
    (((M⊔P.matching)⊔PathGraphRealization.pathUnion T)⊔edge w b).IsAcyclic := by
  have hNcross : ∀x y,P.matching.Adj x y →
      (x∈U ∧ y∉U) ∨ (y∈U ∧ x∉U) := by
    intro x y h
    rcases P.endpoints x y h with h|h
    · exact Or.inl ⟨(mem_inter.mp h.1).2,h.2.1⟩
    · exact Or.inr ⟨(mem_inter.mp h.1).2,h.2.1⟩
  have hNzero : ∀w∈W,∀v,¬P.matching.Adj w v := by
    intro w hw v h
    rcases P.endpoints w v h with h|h
    · exact Finset.disjoint_left.mp hAW (mem_inter.mp h.1).1 hw
    · exact h.2.1 (hWU hw)
  have hKcore : ∀x y,(PathGraphRealization.pathUnion T).Adj x y → x∉U ∧ y∉U := by
    intro x y h
    obtain ⟨k,hk⟩:=PathGraphRealization.pathUnion_adj_iff T |>.mp h
    exact ⟨hcore k x (PathGraphRealization.mem_support_of_adj (T k) hk),
      hcore k y (PathGraphRealization.mem_support_of_adj (T k) hk.symm)⟩
  have hbase := LowSkeletonLayerGluing.acyclic_of_matching_attachments M P.matching
    (PathGraphRealization.pathUnion T) W U hWU hm P.isMatching hMcross hNcross
    hNzero hKcore (PathGraphRealization.pathUnion_isAcyclic T hp hdis)
  exact hbase.sup_edge_of_not_reachable
    (not_reachable_of_separated_paths M A W U Z P hWU hAW hm hMcross T hdis hcore
      w a b hw hwa ha hb hbW i j hij hia hjb)

end PathIndices
end OverfullWork.OddLowLayerSeparation
